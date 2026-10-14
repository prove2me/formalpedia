-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2239
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:05:47.082888+00:00
-- url     : https://prove2.me/submissions/598db8dc-e2e6-4919-baf2-202b47563495

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 402517985 ≤ n < 402697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 402519235 1250 402517985 402518003
    0xb0a050c0f0d0f02030a0e0d0218040c03020a0b1810110a03090608060d03120b04180f0b0912070b040c0b0d05061f17040c050307030b1b130b090d 64
    0x7a40c144540d40e03400c2c0c1e1845030001420300c102e4542450000081d108500844d440311030000d03403284103100da451050007060b640440076000b90911070b8030b52818076026034010011f404900b0b06600522910b41c025074818403c0c15002c00101125100d02c400c1642082c80460f4030050b0141c03c400d003240d000742d01191140981c0a141c141004054000c0d03081d07000c59456445460300c5613210305c1080a40014100c3c0603012403c03a50f400ca10441847c1d20a9400210080c00010980b05204000c40103448140d002c03101c1e2203009015900340100d000b0300640c041401c1c1e0062a6001001040d640b80c1c8c0192072008046a444e20041800c1280c50b002e80000f4041c40c80006458000241c2680f00ad000d081c0e403218040d040c21205034260643c00024841c0903d403030b40781c0c404840c24080026071403a100420607942c08000c0b40e4040383c6507030244856030045018010440c21400e09080b0205482d850480c0c00003c01402c003c605803250404540c4000c171011400f4050b1558419070214414a030040001003480c86 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 402520485 1250 402519235 402519253
    0xb0c0d0c020d0e0102010603080301180e031c11030103210203040306051302041d03191809060608010b0c0a0b060402190801150306140907020f010903020c130b0108010b0a050c 77
    0x141c0010018110354059a81107000c0d9420001682203c00c5c502011f00100c3e0200018000d4024500502000b0342c855400058030001525103241160089400707480038410a1120900c04420bd000b110000240304001a1565247d548d8464005400184445400c1002d50024000e18028400d035001584c00110901c4145001c2d6400700c1d22078042c0c0030882c81140f802458004000020740ca0448170350cc050025450300110200107d000301c0c054140c8020803400503c0c1c58030799080300000c027000f00103030030b00410700340d00700000504503c1d0160041c10f0705003400d0080307001d061000034114a8040c0c00c0480c0800603112500494084d00c1580e020101c010324076218940c826030301000f034034100c03034000d0450510803401800c00c506503580f912410200c03482e403800c4892240b60002a49811194a004580e00503c015409900b540c20a020030340160f00120b44a12150400c3c855100d031034010003608001c1c00050000180805c141030140c0b2482c044042540d0003c540142c01300c1d01490500b40071191b8041e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 402521735 1250 402520485 402520487
    0x3012c1501051c1d0105070c0803060d0c0308030405012915040902031302120a150b030715030209031c05030a0902040f0207080415050909011701091e0507080601080a0b0c0d0c 77
    0x440148040c0d100340c1520203d07500c00780c0610400b4059500388e5a0448000034a883e2080c60b500058201da9000540d103000d440011510205440118401c2c07010a40364507280c10042e003100d07a0200b040c100807a0300d90000120802e5000c0d0b003403c010f0100c800550214826075000c04034019900701618030707840001030145228984015903241c910813259500100549680943c60b809203000c0100702c0131034281120112541c50300b1140c0004400303800c54403100c0c4ea030440341141c0a890101d52021130750000d10126541410311403044050200404c0050700001407800070114407009000e0850903507074041b140110366880d00b000511518841040d07440d17840a080c02480390740300d03100e038900400300d0401d8050002d001f241a01d03170441c00240101d100c0c2e8a0701480650070b21035041c1a040c1c6550b101450400215080d024015040c1034400c0100344a0080ca055813410009030400e419a9101c840104001140050354041065020110f0403140d1a0744031032032254020104074103001c900f40140030180f2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 402522985 1250 402521735 402521741
    0xb0607080c07060f0507080c0a2102010506012c0a030c150206010f050303070b0703020c0327010c050d050d090503180112060303080705030c070f050303012c1501051c 73
    0x1501101050342c600c1eaa0320b00040d989000310b20000c80200d50288481e80206030080090040c405d407100546042c00856900c00c2015820201103502150644003401c0e0f031241d09104103075204c40207003010451130140d83c9089031062030440251000c040300c169041040d0715070040d008011607020320144501e588845001c50303100051b2007031200500c40c1303034000100801c0c503c864030308807003018019526040107030304c5009000d000104000c0c14550200b00d011201e01c010001800c01c2007082c02c1f0241c02d07030882180a0101a003d5031240e04100710380360706d0404154003003090140000d0702e003402a41c4d0401201c0c6080946610f0a02404070b004c08070780340640088403d01c0065a82c400d07a07601074001c0218890234101c030300d50701014001032203e400141c8045d000f43c00464001084c440c100341801502e60790100c4096894100b00c410b41c00100041007000100382023407041c0711a25181c1c6162081c126070110908000404281c440f00345c0c2000900c40fa4010801c840b10310a00340d994031a01e000352070a64010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 402524235 1250 402522985 402522997
    0x2b08030702010c0207050d170f030c03040c090509061f0e040503040806100303020a0305090f040f0609050a090215090117010609150903081614240603070f060f030b060708 75
    0x76500340801c000041d132011511a09032400142401615000c0340c0701c545141c012036013003200303209041207242191528078004d14030031550044c000d0b5991420f898500c1110300c0e96401b40ba5824240018000114170100c1c142e40e110f14480000821440204140c0300345484c1c65112020040c180810300c0103000022000f0025240c5c003404030b4400d40c0341d07250704400210305d03440080e0041c1c01c85401c03100024402c1004040703550008003c111340410381300c0060101c50000c0c2da0302045941e611030800c1000c81038002c2c658400e45060302004002c401d6004074010720902041481041c000040f0003d85a000320801c000c5100c00300591880c42d80c43e82d9000e44020b9050003860124621510001c02952058070716800760fa030320484031810840700807d5900c0075410601c0840c0c040d01c0040070080401420000f101510b40515140030210a4410a02c001c0e00005030405019070000e240601404070204c40403012100c80d0300c0c01607000d010b1b01004800070140180c00c00c0d800000055500c1c14001200b0160003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 402525485 1250 402524235 402524237
    0x13240204030203010e03040f0e130c08010e0c040b03031b03160b1f14040e070305030a0e1201060806010e0405010e01061403010507030b09061002010e10140705040803092b080307 78
    0xf11700d49101c4c445640b406680314111828000303003818841100401e00a581143c40c00c091b8540c04203603a9030f0122720504030303000101543e40d20203411010240400c138000c0074407401d0307604101500e000c8010a07160b10620304070000040000c4101150408104200e402001c2c00b920000352550440c42e02913b0392506607010316807100351a10301c400e11218030203e10100c5080e4000d94403c262a0010700c806402c07021240342842c00307600d00020110780c05000401d020180d80d56203017503980000c0c003000045204501214003681c505001409406800a080f5040d500c0300e151441440c1e607986081170151000422140e0954240b03074001842024451b28202e4040f0b0880003440aa55502e0044044401c01004140e21042880c04110181051108801041c01c030f0300c0007056295a0b403080610701b1021007170078076040b0b41e0303141849090103049100035088082d034580f0500e42407034010b4035a501c0c0920f41c8900c0c8102035192542801008100400d0840c0914021084181700241000c041603002110400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 402526735 1250 402525485 402525491
    0x10c290115050313230d0905010f090f03170f130512010507020c090c0c060c0304030207060903030909020306120a031106060f090109020a05091203131a031324020403020301 76
    0x1c0c001a0040040e80d104e0010524205500c8075103840e000c0c09662200701040940781d1140036100303149001d0020301080c40d45904d03014540d038a884c000600d0308210744461420490040741c103104a401e01800340c02100c1d04503442a000b10312840d040c1100b84611030b4410600c100028160480c00308038501d0f981100c004903640382c400c2c2c411690756420b03030f81c0854079400180c20009045d03682d490051407458100300c5d540340341400c00f040b000c802490700b802503669440358980403003000704051381040301e42d010f001c0a1401c500032034510b030740c00b4100b4101d42c081d0806107900480021002c2d1101110f00c2d503000c041204403070051569080103003050780d1070901500d59004410018425041c003a0803070169110241404599a203040c6030440250441c4a05000300a010070002c0095940c0050314882500b070000030b10f0b60b4180c408a40011340e80780c0da110750b00300b551129003a0050050344080d03a504c520302550f924100300f00707840c000b180c107914109448891000b030502000300e0170155015000707581c801d030700030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 402527985 1250 402526735 402526769
    0x903030d0e0d1d09041b170c0d0c0b03060d020402040b1e0a0210022512120c0804031b02151305030a4209052109010c2901 54
    0x8a503c0000d40c075401c0b44000700c07000d4035803003400d1588029074024021a4110141100d0701e0480300440e4103541311215462826001070203220342840950f44806040328164140000c80c3d691914141c118401c00600c440c003c8002141e54440111030b04003958001c0c4110354958444184210640000c007024024031510b9070303851000040d00d4125142907009800801880e040920000040e5102d800004407508203110980c14002c1240c21054001e4410b107028910a980304200034120305000520054190408401520380da4106007a5500700c1d0300b52800b000525451020a2507210010a0080d00400302c4e80e803030340b0390302490000f4020f040c221311010902595100c04140d5a950945009405440d1200c0740a146461285003400c0500c40d1842118500700d82400300d10381500c0e0f0728451131159441d500d41d80100301d005e00c481c06542d811513400b42180107402c8000f20315801001030542c141300090003507400f4041e03400741d90440e1803012500314928a03c2c2d1010041081c0707080c401c01d41003071061628 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 402529235 1250 402527985 402527987
    0x81906151e090909030302040302041802090c0a08130515070302040515070b0a051909030c02091315050702030c12070c05010f0e10090b0304060510060c15050a020903030d0e0d 77
    0x1918460300c07425920816401c1c00d001e0014002c01c22000304406141d400c01c070002c01600c90307010340340d00310310741c0c030a038944004107070040c400b0114000b01071640421081101480d510741001e100e6400c012001d60920140c1100c0c03514038a00702601181e441c01c205d141040100c200d501d41c005100340c64040e80c1404511880e0706040005000d4200004c0c0500201c00c000340b072100841d1301c8940e0002e110914460407481c0c0ba040c98080316000c40d8158001180510760100354200006a180c100043c18410b0140b00f031a5161030341c032040300c03900d00000756494101040e0054400c005403a1404220029900ba0b0a0100291604c3d580311032000c440800c860800014550300a103900d040c801043d071101c602c5801100c0401040e10800000141400302190000c030300f174980d10024605c1148650f02c00105070a110002c00d1103004a54400302c01c00162000382c50000e1102c20f03a15900c0c40c85260302045548484960802900aa924040e0140700c00f0a02c100000e426400020700e44d021036082c0c952210b92560 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 402530485 1250 402529235 402529277
    0x6090d120c02060115140f030106030b091e090f2d010b0303160f0b0a0f0b0303090f061e030f010e010503010908160314030a0b09010e060d0308190615 66
    0x42041c000d40c0020004120094080c451a005035020740317410301d141c0340526082c007820307000a120742019420110040c44210f070544120b40c0702030800c942e0340c195454403402041c0c03210709540c03010b4001e07130350034000c103000203030400c5811050900003080e107c15542c501113849209181d201e03941c10f5803103c0c00c3c904200b10418801c4035003180002c0d02852524000c0410400852a882011039988800c0c085d1440031580002610340501d98500300403442c0801c0d0082e0700103a40da40c275162482074200b0004002d480d501c010842c1481030b41554001c0e220045420301540b01c884400782c1030b0740e000001080002d503031301e1404124160740040f00d90303100312b0340c0710010705003201c40500c00100030100030050704560001c2c5080c2c544103207101e840c0c041880d601049d03102d1030b1600180c400b00340103034036000752403614500000b155005d0b005082c03101c0c2d00340c6800000600c100c2030031200070702880000c901181803050f5001c42011440701c803000520045513251080041010710406030000115010f004640c01d940080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 402531735 1250 402530485 402530501
    0x60d021c050103051c021c0302032a04170c03030703021f061a180409030207140904080909040510020a05030106030c05030603100c110f01022d0307031d06090d12 71
    0x10000b00540350000c41c0740300c001069007000d0010761084001140c80d00002e8003030701f4003c401c1c5540150722410640052503540840840120f461008401c02050310402c0e541960b045400300345140818111a429040c1451040d0365010340600000546005240d0001205941d0007005004c0c2000780000190b118102c070340e203019440c4110741000100d5000c0c0f0103032001c2c11410700c106a59113143c4941c000054201c4042490850240e0003240c13003013024078112444041d01200036140d200d81441c00740e89000c90303485070502c1c051091a1080100f018400e041003140c00121801100b1940da400040000d02940c00c00d104d80c80c00241400500303103145104006503409048050010010741c580440d107040944140c4a0101c00c00241c0445421100c074100321080842c04260001651004445042690f000340c9031250b0441c83c141c407640030b800ca070851085990020030b902d000641000c1403240e0f000050040e580a0206104200502c0790b04240401c820001c100c89842d42c0d185070352078098020a441c011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 402532985 1250 402531735 402531743
    0x6090c03130b0402010522030c1a07081e0406090f09292202120a05010303090626010305030d0501080f0a03031e020a02030a0210290f060d021c050103 66
    0x1c022810001582c1c0051181c11502c1410300c10700740300241c1204c1d0741c84240c00060090008003140c0400c14840f01181c058040c107441c850004044103007034501e004d42c0c0705282c00142400d0340014414002d084480240e000400d1310080e643d83c42d60389080c001e0002d00c46020768000030501c1c40001420032802e01c5007400c0076100400c009a00c4601070881604c41d401102c81a410006845820900310000d1b07060702c20464040d000180c480400c0789880e80e4002e8002c0120309120f18150051012070b410080b010b0441f110f41c41c01c89a030036200440065802c1c40c1c40e02c031003040440034002108024022000d0a801003501c032003001682c1c2d03286100c81d51805400d040d110990018462203006c02d00c43e07000740c500c0c1e1610001c0030010070100690a001c0303030b201109101c011303003001c50034040b4958140141051103c4051041c00408a15207030b10050f81d03c401c000300c6415841c8422034020b0f07126502e8151a0200042000303440d00d440c008114040e520828820b5141c0a801440503003440300c40c07086605890b04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 402534235 1250 402532985 402533011
    0x150d0e0607121a1210110c0634090504090606031103070e06131e1407050306030706030c0e0d050c030d0302070b040602030606131202010f0c110f1909020306090c03 72
    0x3c02c6090004407001c01c001d000c00350080100c504210851805400342055101480981e144a010f01207803d001c005401d11a0031125008000c0401200c2102c1f01e6090b00c0c44010f907a1000c10600e01521010241e0380003c0e04982000c1000e0144450380d0b100c1402c50b80034041c12a440c41100d4100f54886080d070140c1001441210b000c00d003541003d07030b190036001c42d900b4000101c16402644c1700940e034542180c458196500c0d503440251101c841d02d003d80e008021802e20605600300400020f4aa10040c0980410141d454230142c00705482010402d11181c406480d4071428416810714a4a81c854140c816000348242007010000511070320031650040d42045444002d40c4035990382074060b501c0580b0f540d0340000c06022000810708007002c02402020080841c8070031441c03910001d000400d2000310751003071189240118012849200ba002d0880e001201e500414622100c001b603841404d00020340680ea50f4208080740040c0b4640c02140038a004560f2a0036903500c00080880c103200480d500001688 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 402535485 1250 402534235 402534281
    0xf030216270f140f06030d09030b240d0311010507180302270109020304050c010807080406270b09070504020406020d03020d02160b0403120e0c150d0e060712 69
    0x2015442440c4a00d848031001ca000c400f45030318a0700c05a416a40c1072036200c06070003030258610f4100000c3e10b040702942007014032149180c41e0414500001030070715403103140d050408140700017250f520440c94180103048090500707860030001c000300030304100f038a045c1d8030308000308012a006051003400300c0c140000b000540e906503801d0203c0202440d1007048080c94548001c2005070010300703505d000c2c0803200307001603c900d024205145080080d80145060100c414180a030443d0b00c80703000d030303445500480d0220f000300b81c052000c12105a240c180300f4484850b40d2019041008000030349000703401440869441680314170400003248180d06c980e01c0964022162014464001e4020717082410071500010700b4404843d20300c00290740100d20880e040c0c2110303420401016008411a55860805102081000000140743d0b0b0f6500301e003103d95100d0254500b141c1e2403071420208440090107150014041d56007100ba04561342c010940f0014041014680d4600d581d011030300c00c0d2041c0400d1030400340801d41d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 402536735 1250 402535485 402535559
    0x806030606120d031a101d010e0d1101020f1209040e06010b042607120b071e0c240606020d02120f09031606120e01090b0402100c0f030216 61
    0xc521100ba0703100e4411401e901d0f44050381d401c00c1b8030f101340c8040c1c0c0b40c4000a8103d025400100c0744240d84150502c00c803030805030640c4c0c9841f6151001554000380c40c10350001401c0060740f0741902410050100d00c14114000741e11420718000e41010102070740c00380164a0f06900207501c403a4240514681488240400c02c040d181e0f900201540403c45015000d1858110706010305003041d80d04a500021050450402000203090800c1e81c400c1d030f07600c1c06111035014809400310103481040142d04020740880e0a205005c0d0001d040d0309074030228ac0790803072114003555044004c0c040c14401c00f00075006601d000d0740030a0010030780b18807901500c0c010310b2901c060944aa5070315007040041541620800c03c40d85d60800c28004000040d040a884682071050114074070020f56203035a95600f0964102090040050f08080703c0a8000707074103c40c07401310b0704124401100c0f101c503d030350081d064800c600300030b506040d00451100c070340380d1224410b120290345503004180e030b0400790a80c604044e0b06004d40301c55a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 402537985 1250 402536735 402536741
    0x60203041a090304142e030b041e060503030f03010911040306091a07020c061206010507200306070e091303090f14030c030a02090a020702030106030c060806030606120d03 75
    0x11621a01c200010071940c0d141a00359039600301c6400006a00c00a0184562107400000e0b003620641100c3d80039020340030403807001451340135940e20300e05000456030150f0700034003e030800c102c07481c0054001c02400d81c080028401c0c1e1107261000803031491402401290604020003100e0500d000b1404052840e40b03084040030040031151a01922104144008400224035019902c4000d02a032a0020341c1c00107070343c0820030034002034019410366004110f0916603460708070035240d6000049130341d80c4155480710010313150b52241038401440104010b100c4140008891045400b803003065080702c50361303590b110064545010518038583d008102d0300c002804007031501d50310180d681c824500300800c2540e03020b00c004142d50f030390131210140210400780160742c20b08000710450810100c00404e40c40b42130750085041444090543c0f0301d82c507000141d10041d13407425042a40111b600025400526130349920081c0001e000b0340d41c03d8820f020307200206401d81341030400d0318030034201d6402402907403c4039901070b401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 402539235 1250 402537985 402537991
    0xf0603010e06181602060106081006051b030a050301080106050105040f121103030309070e0c0301032315010b0901030509060606160f06060803030105120115150c020406140415030f060203 82
    0x40034040002c511840200782d0349031809008038004c0f468048622500281c14400f058001e107080010b240100b0101141c851900000c950290600d40e41d1120756400b8540080548034846941d0b00c00050081e03501540100114101c40080008004482e02c41004481c103210307034410003440b480000341c00d00c0340c00b0542004101c502d104523035940803c9207a0000c6800e64000704c030044901d8100850400a8045010101f41d01111048a040ca10b46c11552030b4280034400e5603a000d004600c80380d20051860302000442c4c00070f180c0140e10384080d03943d90b9015003258406903400d0300281c10900410b08200d00080e42da40a6000113140c18200220900151381c074102ca1201550f0005660f1401000700d542131081a010740b804030095a40c0358182000e005902150850b08070203680b6180f0788852840c40313000c0100548040407565003000600800403211800c4e4410301079030140c50510000b6580d0070121444c2d41070704040d07400b405811042d80710702da00c514043c44042c024520301c8861070f000464a90081d58 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 402540485 1250 402539235 402539239
    0xd140a02150603010f0906390f020f1606030c020a02090106211b0e180708040204060b13030512040b03040221070306091e0503091302090607030903110f0603010e06 72
    0x1707a880b582c18164058461028066aa4682e1016145015808545209050204100701031070300d610184403c100135468251907410883c10390004404103109200d09410300c0900741c01c039642d03603c031084081c491403124454071011034a030003034809110340085440c60a02c0d030000c1238586207030302e01700c4182d03150385c9280c1103020000c1400d2508c030560303001d40c8103c98260800700c18400410b181c04102424030f01e040e010b800d1248003a80412007030804800078003940301c4001d2526807840d07141c03440480e001d8111600184400030010030b002d0006100200c0400c2100e000c0c1044070000300c00e040451245100b58050260074040c1040044c0260030000941606450955845807031041c58410f0182132201c150002c0f5107032600c0d52582d82c20711841044c1c0d000b215000503a0034000c0b20295940c2d5542c0c0c8a03883c45a805296040600010b4000550641e070f00c01e100076101c669100c40724540202611482d0100721140c080c04613031181e40d4242017449007000351014241520303513400e00c000c054001c0d9004001d15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 402541735 1250 402540485 402540491
    0x7050d0e070f080606090606033108120f0a06061d03030705010227030d080a1a10050918102706030305071a0702100b210d140a0215060301 61
    0x1880102d040e102c03001000e001003d0201c2d410188100010040058481e5114800900c244406010214000440201040090800e000c248012070041140d01c0c140503159a85c0442d20f04040041d8204a6201d205041440345481c2c0c1c03035209020442e000350141e000040c0349512104883d00e0324550051740b844e4001c04890a1000544e140c81c20b9130700c038410760a2207100380c68450014280d00c90003400d030a04110090071404200c0e400003000b113400180924038603034840741c0c07200ca0b251045100100041018085442c072107c00c0d013016003668044000c0b03600410b1490400e401252842c40c0d083e001d003c840025280151400724100c40c81170004062000d15a21120f0b00302c114000b51252400562094070341544449040c14081e603e000d005442c0442e42180d0030400c100c0f15804104030303608030360301c250006400d9001d00c04500d91806100c9050320704410500b0f07194100d2400194118040d6241d901d59408018613540345445000765451403015900c500c500312225005c0b003017900d50018001d8000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 402542985 1250 402541735 402541739
    0x105040e0a02041a12010e06060405060d0b07080702240705030405120a080109060b09090c1b0a050102130f150f0e060313050d0f0518010e03100203060f0907050d0e07 73
    0x150440b130440030300b01e0130484880043c0e00c1a00300766101c01c80069818000f000030b44004550f564031984000c0c0241d102c1c41e66000090000d035100740c0d0340030980c0c0c0c100390660041c1c9008240079000c80000d480300000351140c1c0e0140640c5201a520b544503100840f20208003d4852801c00e03902070f0006401100d0a008184d1020700c3c0441c00c0c0d000d4900381d9115920282c3c0c0e0b501d40b061160445001b034202580e8540100182180e50b00c5403054942c00c40811840e00d075a0703001e10f03403070311b40b4401210141038602d00442c0c0102041c01070540103030400884e034501c03502c3e0050741c40c1001c0040103480e100302c2c8200b8291110000045005041d0404040740b40c1c182031205212040c0041e07110360080301c610801080c03840000050000c1040b400f10208294106402c1c107155042002d040e0b07004003889000d01606080d030040c03090740b050081086ca181e0250443c1c1c01070343c040e0350140c043d4000303d03001f40c02240c19010308055450012450b5005046548410340703070000041c4a6009000c03900040c80261055501c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 402544235 1250 402542985 402542989
    0x3040902160b070e0f1f0c0206091302031e06010c0b090c0907021e0f0c06070501090606180f090201200c060a091409040c06050a0210140a0e0f060105040e0a02 70
    0x34410900da135030300328142280c4800c102900d401241081d010f00180d01c40e91181d40e49010394015505410704010440d0b203010700c00074525109102c003041c0c22068141030320b13550b40096000f860203886020401e1112040204a03444441011104140001c540085000c080b42c03005c8000e503000840030007036440001404001c50110342042d903813540180e125580000d141c072100041e01d0040714090002d8003000d00d400140a82c3c1e029548005407080c0e00004d1503008104c8250701007505254084410f014940e07441c0c28a0b0054845100c4c2145023500384020341100b1082e41c03169811055050b11060720003800030348046124000071490424900c20804492103603500c540c0a071554140f01e9595002d0307241845441a85c8200c03c406071401613030f00c001440300244e18805d964083d65200c2c0303451515203083c0d0008902c0d0001503c2c0340303080079140810340780c65070311041e00061080140c4003007801080141101d007540d92460354801d6255030440d5006011620f01600190100089082101c182d51282d0f00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 402545485 1250 402544235 402544253
    0xf08070f060c110f0705030d051c06080a1202030403050d12020d060b091002071202041e05090102070c080a11210f0106080708070b070b18010c09051509030304090216 73
    0xc8107102250300380b001c90801010411001044c1c01441c405001c0305458280404e6441028140301001e102d4003080090102180201403803a001c20314009204071551140340644444d451581562840143c0b00d031014914000401c880440f544035008290030100c25000f11804914032500680660302080072143c02e8656001d4240585000344066540344902000c0011402409200d90103540090364100f1800b83e11813808946035806480c0400e03401a5840000b41c50b80001040070550f0f0f240100307204035804154050071009110b441c840c8085c4c0d496140c42551405003013801420001015003006090800f01c14186204400080b060300d03001351503071646c1c144030b048801007499030f5640004101c00341c820040e542c0103240c10b002400145040480050036445421005070038855500040303408a580148403420703810851008011a6030701100080c9588228071890b481855540c1620391442c65100c226190064010010740c542441e0840380b201940114940c040c8081c2404400302c04070311800703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 402546735 1250 402545485 402545501
    0x409030314100605040302040b1903080a030501091e0b040204081e1c0f08060a030f1b050604120f0812010b0d050c03040803040221010614090a090f08070f06 69
    0x30300d001c035220300c18507040000c1c0c4800524402410500c607804209058100c0112001d4a0b0140d0340070500390101d4000c62040c04264040700d5022102c0300000090141120240c00c0c0849076a0f010700c500e90740c031064001551900c0705e901e40d5801c2612100015660180e10001140e0742c00790025040994071410a410103a490780d145401000342103008030150f40a2203445c101800d207045c0142c44400302c03c0018940e403940c0d403480e014800000049126951102c04000c010344d8441e1801d1001d02c03081c03808a1201e00020351500c4900c00440001c240c900c0c05205850a4440c220f0140d42d124031142c4900707103101014001600c240504014081c4d400d110090400d0191100300809940c60160180d9003045402c010549814100c0034400d00c0300007911380301140d0300f141c0c04982005146061020784203400c0b00c0383c0303003501e095032074240c00140b9040700400341c04040000b210081915552041e028040c1e402d54400101001c90a0780302a00040b140c0c0c2c050103801d406000c01c04a4000190750f22001c8440c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 402547985 1250 402546735 402546737
    0x5100807020a05011e0608011407050f042126030c07060e03070c1a0a120b06090409030f0215040507060f1808060f1f1512061509150207051e040903 65
    0x6000c00801c669814010f080051981e46d00820914401d40c29270b403a070100203000714003081300c00609119a40f1514050318007512600041d01411a15040c0400c21906140011500224043c3c507824180d03810800c0104c03095080c0403058510380d07460401c42c40710341c89074000300c078015614940503200c0d04d02003010b00349140c460711090500a0800380b044a40511560244103500020088001c5495005d60031a14a031404400481e80d9001900080c400f401100907254010f46403605245c03d059101800303031078407007a40c2c09840c02c0c448070703424640d904401128040c0060b80555403c0040728402d40e07a2003010204c515120001101d104011210b003285c55018940720303031214050001100d441c000940e0081415008207144111000640980303c003581b08000c1c40020020400440e240111a0000b1701002c01038200030380c03074540310700c0420108072016230380000e00d5114000c5001d5558103601d440491003a0000c00c1414505010000c4010301060054508036008400348100c4c0c45900800e5152442 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 402549235 1250 402547985 402548021
    0x5010915150b04120c081009020a0b04050117100f060c1101080702100b060f1606060b1c09020117010e07030b061908041415010306050901050105100807020a0501 71
    0x540140401034442000740c105401c0c01e40c410030450101540216000c0700d4002c000122002c1480c18801550011a40004101d001c0c150050a410900e64840c001c5180f0803291003850984403001400680190700484e40820018184403160403c1c141d141540251404000700031a500c8540e1100c210345243e102d034000c250710000030400c000080c80060f220580a00c0c0114552034200c500a40d036018205203084607564500c10100691586004c6854a2400207141ea90b203030a107031418101041c2c203020644183e4988800031030881409003c9881509807442c400c020150780e805100000c0400400c101e041c4038401d44502c0c1825010315034940241095401c9618500d41224041c0070780c2d000d103c01e14810380703081140d22080340b142c03007042495448130f00e03122031250346524040c0a80e4041d80c01d00b250a120b840151100d80c2452031440b810f0324030a410502403621611149420388a0a00039181e002026001c0c94404070310507140c1590000480c41103078000c0c0d045807151400c40301d0440c078030442484 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 402550485 1250 402549235 402549263
    0x41a0a02010b0319121e0207050102060901060e01171504060204050405100f0b090a080f0a03090e040f060209032a03070b0705030405151b010c12090209071b050109 72
    0xa02071051044485042d0064000070860203685590340b20a48802024200400d580175400b81c894401511a942984052907804148450280d500d180b1441842e0040c8201c600046810b441030140030100d4200710074040050742007040e641711213440624062210b20924500100c030221031030301c9a019501600c7d005981d203042600f4003068400c002d2031185d0082000d0010040c40699011620407941407048407503c4d400c0000024200e14110b500484461003413002201c4c64103030108150503520b110303445039242155100b0346161985011100680001280d081c2030380402c85d65001051350071030040540d80981c030482c1c00919103141e0380005c101e06034441e40c1036a44500b4200180c4024080d0b5200084c04c011441e44c0341e50b640c0c482c0d405154058005c207125504088919410b0300d018141c145000c46d4448808810b0074001c1001003800c00000780d1320010020f50710114800e1042054029000d403045548840c8180c502a0f100c02c10686000300e42505000031800030700c103008039540302e2900305071042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 402551735 1250 402550485 402550487
    0x1905191206080f0c190506040b041511030f03130209130b060f0a1502030c031c15080c041505040c020303011e050a030b06030109122313030201030203060402041a0a 72
    0x401c5904140c1c07080d401141e0308188000d002951110440e41114404c1036181402d02d0240105001d0340440c1d001440440c000c1200080c2c0c1c0c01510940300c171425980d401e210051012114640703280b00c134025681040060350300d09003d01c4000c1d540600b080c0004560480c0c15400f05860000842c1e00c0007850954034251020080d4404031203402c114101c0b0404c0b050301c40720000130a02003443c0325044482e00034642c5000014000e005603000400c42e10140d0740c9885e107010030a050180325031100180350385400c4c00002130780c03180d501000a5401c0d0000405041c0c00342c005100c024502d4200b03160036480d0004000402d503689002d40c40707480c05184d02a41d1a07514010701105204280746140011948485040c0007035290310b00b501c0101c9070005050041e40e241c0b000403a004261703512028095003100303841000c041e900048407014080c0f01e0160318105502c0384110200d5800f6440c0d16101c2407940c0303001040550700c0303500a107420803801000189003036503d04c5500d01e80c411300b8008180303c2c0808a0170410b82 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 402552985 1250 402551735 402551741
    0x5030405090c130f1a0d18051b09012706080106060e040f0614210615010e0d030806010c05030c060a0c1704080406030207060906060b0d0c1419051912 66
    0x100300103a810580d00c0c1c20301208480408500600700100d080210386c400d00620f50707800000240a45502c02c017104070319401c0c5540c54030328848201001d4002a452504541009004141203e20401d5403c8880c2d082c83c0103c902d2503207044200b11030b25100e030004200c1210a05c00e400042138141ca50180121903113042c041614000140f100c429460301000300460000c417a503c001040d81220070304039041c85d0064000c00f041d5251f440401900c1120308000d481d5000811200041d0800d895024200d80c540703003006451280f60f14020001285100401c015501925000c2c0c0e15901c520203a81c200303940e00118900d062000c8035150f400e43c2d10381e12000a070641284108000d2094401f403101c45241c01d03140c2140360b11480c864103040590016000b01030001c03503400044e07140d900040a0080380da69108040c0542c00c00a1002d25003490b00c039035280d401c0c0c050004444488000c140013030503d283c4c0003040e90103455441001050143c200103840600c0d100210140b510441a11200801c610910b150422 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 402554235 1250 402552985 402552989
    0x1060e0d061a36040f030810090f1e0507090e06030f0619110708070f020411030928170d090506011205070e04050a060b040f02162a06050705030405090c13 68
    0x84000d0f41c244004039061840d1003d4044d0103041104143e16403640391081100680d0000d0a01803405010640c01151608140310070b04141c8041c240740c4940c03200d42e40440701e00b43d80c0040800d100c6881008405088543c0c1c40d0f105800605a5400031107a051082c1403e9040340d00750a0720b03030b02416003c01c04209200c1c0c032071100607154045060802c103598160703040c0701c0c0d810b014007590a041042d90855a50350850030400103170030380d603d443c2d0800b805600d0780e4401e400c13901803d488100a4080c0c4030080c11440075a400d40054203010808200d10341d0003c19803108441c2c020041e00c0d000c10b100498401c11155009000c80e200e0200c3c10070b0241000790600c42a6004074444a8401c002e00010407000546080c41d00e401050026480c0608000100288041840644003a0000c24075019540101c490720f91058082c01030441498101905a40102c040203108404503800500c1440000d00c5140902142441241282d20301902c50000a45050040310881001c060000c3d2140090011060382c0c80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 402555485 1250 402554235 402554329
    0x50c0912120f040f0b0702030a06180f061e1815020705030406020a0b010b040b030106030e07031e0204061e061107120b1f050105161502030c03010e01060e0d061a 71
    0x400c00700c80750f0001c1e40340d1025000c0502900d82f101c0c00c0c12141e00d51208042c4640f41e202c100e10b55890385600d048405448a03221103ca420106000d004403140103008640e81c2241e82104050304880c15a294903244013900c03d02071400ea424409100010410030007440074002940080c000d421107898070080c065030507040b8080c0300e0424001002280002000d42c1d056804900b0040703400f40780313096103e00d040d400d5400a0018240c078040d030a6420070303c034800031229000b81d90a01250f42c0f41e1041250078200c0c0040c03014102002281088201e10500a0890a152038816114450b0f41c07515151b541d551032210944001c000802030050340386d40080415548081c240060b4940c602d0400044c001e80502440c1c94180d0700e40030103100420001d401c18252800c8035030811901c07405c25284100840d0001d01803104000b10400010490f58040d0490f40c0d0300c1c0c3c0005200d0900d0030f040d0b5486001030040500c118032104582c1034143c2040d65090b5407161420002e05556064000741d00e51503480a00c42d8002c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 402556735 1250 402555485 402555487
    0x10b040e130804090513060603060618231b0a05091c0506010b0a110f030405010311071e06020d0507120605100e060f0f0c0a15050c0912120f040f0b 65
    0x800159094191422130704000c0002070700f9a10301034404c10840845900030051407400c1d00110070800954403c109484200c0d01c1c500f00e555000d84440c1c02c507040c0b1103442030b10382800300c1c59039808005c2100c1c0640c840524000141e01c400c0014000195030010304001d404101c000c22040340600f0044203540320300c5402c01c5404d00f184070540b9010340720b6030103005d0700805070303800544100c1c081e014504403c1400c1d00c0808407004d50002100160306c070f40040c001d090000f41001a0a00405021000d8454858100403840c80c1200c0d0400b00b00d943c2d444d900701c115034090b0244004820a091031142724851a000c5d00c0307251110100c401c1281c125021504540d03c198128406110a16448140000f540c103040d51040e645046201c50505c3c0b6003d101c0e04503521640c0000d81215246001c0b03840049244a040c16400b080101071210080d94411031341112100301c14025a03060340351482041c0d40c40521003060325000c02031009041c00035884541040d0345500005010030044c1d058a01d410001d00c43c1b84155 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 402557985 1250 402556735 402556771
    0x507091503111b0c13020310061815030903080f10031b050306040c1d1501210f0e100603080306101e08091515010c03050909010b040e 59
    0x1034500100600d0310204050b964050404903110340360460368180000024100502e807040500c41d0707908404001c1d24040c01c1e9900c480100d14015001303403809104030607141400d141c01c0900403580b90100c403818075988c642d4031900060321025a203003001125060b50b40414540f205050260039408003408074044400007408006050b42c601d000d4605603640050003aa050b04c00b0034107000c3e00031040d0030880d032501815041c0010480b03c2481c1d502100c003404010487c03884203801900307045c00304460081e5040c1409046c01c07560f44c86050f403030700e291003c0454501c01070702c420b02c078a040324050503881140c50307641e0a0038030740003c04000100c50700c42000420700c00e080c1503565203c0540000f41402e40540d5414180d001c02d2800b5441c460701a14131aa5035000b04105200c00403e00307001501c0e00c86031070040343c15101c4044400840c0c14803070441000e44200300f07840007004603000980300900b5001c001e0140600d00c01c9940d4001424001c003911200140ca450408440102819000e0035011216800c8012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 402559235 1250 402557985 402557999
    0x6051c030806010f0302040e0c07030813020d1101030905010e030c100509070905090703152c12130e18010c1706090403030908070c060206060a050a170708031309050709 74
    0x341c5074410820301e050341240c3ca1a0200b680a80a240c20a100940780300c4200155449410060600796021740c1c3e540c0c003951100c1382c2000b0064024107003e034101d6074481143c4042412103206085040701031400144103050342d21460300311000340c0d403a1411a00002001c0303014080c10454003405a01b145810005400c007001c000b07a90307040c144076a5400c9515980068901c10b0288091001140c00684550384c50308025204801004c1c2c000781c0c80010001e1021004004c13800c201054a00d108520050018116042c103006103600003180c040103480c058540440c40c1e401d100701d058007424000c0010b20401802e800c0c0c06003540c80c03880a03501001002581c1640d400c01844509400c01c00c00e030b801c2c3d0001d44403800d00710080c10a40720003601880340044c04034100201040c203102219110b07801e03134041d5101c06041004031105445840e510414541042c058000c410401000806c0e0002c1203403121580d40040f241103402640034590b003941c030807a0400074288039001c0c85a1106813032420102c00740c2070082c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402560485 1250 402559235 402559247
    0xf02210405090a02070b010902030a05100501020d110118031806021c12140c07020f0f030318040b0d0507030c05030105041a04060b04051f080607230f0d06051c03 71
    0x2160342e1040c5001004941100d03c2d60f07046528190b080008114070f503071102e0608000e5802520302c089858030300000a090030044210100980c0c00590151211200380c26048605910814048016550300c0b19600e441104031401250f0b0300c0d01c01d0302c1d0200ea4036805031200040b140349502240c150342217545c0d00c00030301e0001c00034581c0401c860b0802c0040d00707200000b207400a02c0418240c0d2a81c4483d0300600644c2c160b050090301116100725041350351960580140700b000c420100c0c440303400d9402805424030303040810162074034003c0c01500000b210460400066205a404242a101038000e003000f44140101d04110b14080c000030380080c4024141590351908181d2001260740184545c10046000c202d07a64000d805090700c01041442103007000007002c02e104651400d90440310780c80d2480001c0942000c100c26203e20401c0c0c9981405004000d400505803803031001f00038161400f04042030b0741506100103098403c1840b0000102c01c1d00b0101400321084002d002c504945080c0901c800000764020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 402561735 1250 402560485 402560489
    0x906080a05040201090b0f0d180501230105040f0209090a05070221030a05091e030c071a030f070504080f0a03080f040f030302090307051810050604080c0f06070f030f022104 76
    0x6c05075541e030b030450f180c486000c0d028808422840c02c0c108048a00000038120a10110340d004070020451517000712641d401401c00354190424004c1c01200410451805602500408101c10009458225450b00003040395004440303280ca22030740c03007050044490741008110101030343c0303070305507140c441034034003214460b000061009203155107c9002030703c82c10091001120401d10b500c10400c603d1042c8030040e48a81124801164a01c10b036240068182010540140b441640d011300620b55154449410407541008003000180441008001111401000105043c0440038050031180c8024a001010700703c01070410300241040005120202e11410365011501e94141801655220034402182c10320b08680c0c0415404817092800402ca2510480381c80d2065030300c18610707481903843c0e008200d10350045008407800780e40031011881550510118000c51068010482401c103c0c1581d940c80001c08075090840c0020302c141e4000c0c6102d50100f240002805408a2049507040d0000e11030050340034074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 402562985 1250 402561735 402561749
    0x16060605030706050304150b09100302010f02030909060402071a130b061e010f03180f06060b03011a0a02030d020c011b05271804350703031505040c0906080a0504020109 74
    0x4c40c817001c4413103a143c1d00c0042416409840307449d061501c001004403103130842c0f106a010030424842e07c1c0c410b61010040710962640144020200e40750301092000030742003048120780c05003180f1100282944402d203218410300224602520b134041902d0181880e0710040e00c0213016075a02d45640f41c00c95240711038200c0b034080c01e00e400c61054917088004c8000d059803420806202c18680500e00c14000c032582c1000002c0d00901050004c140d407000c1511140c4404d1107207680c180ba01c541d11480c83c400100007006400d0392441141c1c00c00700354051070800c03a4003456111005030340d2031207404940e2141c0c14043d01e51000d98101142405201c803240072002d07d4111140c1c07009c0c4000f005644040d41c5d0305d40100002020307400f85984505e41071400007110494010360b0f85a03081e02c1140c0b02a0200c0880c1c0d0040030801d101016804e0119580e0190041d20046540f14203c140174003020031a601e441c4580b4040c90020f9036480c4040d03180400c003402441c4050009124142003208010150f40c000001f00d04903128 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 402564235 1250 402562985 402563003
    0x503010306200c0124050a03020907050c19060b010c021c05030708070b060118060f0f02010e0f03030624040308250507052d040c0207050616060605030706050304 71
    0x3030450b400c5011214081090040002245500760401d0540c80308010386882e0028030404c908403500030041400d144145035014260720310600060504c84003154018a00c1d0134060b013043e40194440b03013005000f8520441c8411032903400d03414060540a010004002800c00100c0021541c021580901c201c0c511584904840c0b00e40d002002020021074540a03000b0010646907249843c1500380c92005494841c00211a08000d0b0001500b030b01c01401220929129810401c207440700035924100d142a0400c150355a80e441405c0c100d90900c2407901e81800d0070043c3d5601e203840d41c00c010018026007010881d1401c0e0181c41c0000c11b14500c111419a03400805468032401c0d26480f0035546102c2e040000706040a4a005200304080081d04000f50ba50840321000340c0030b001601031314580c8603192000d40e0459810b80e01e00c082e04160b4004501c0827000d105582e40c07141c517030020070a10360283d86800c02e9010801404410b0002a01c40c48001d484100d015090841c50706e00020032030302001d440501001c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 402565485 1250 402564235 402564251
    0xf0806150f070206070804030506070f020c041a0d052b1205090109140a060f110304060506130c1d0103060b07110a05100c030215160c02040f06150e03010204060503010306 75
    0xc040402d40301d1569001346060358843c180e10304003c26030410b22080710a4403c0c407010540c0ca50041441042407035582c3e0092078203000c0801004007419441c94500119038450108488070345038a45007004503070085004120080500100e80000c442200c2d082c581020103c3c1c82840455210044e9401d8101d92500418030352a0241d1840c010240d05030010420180e88a0b92400c01d6808508030140e03e0003035504103c43d104015044042e1401e50100f4066400100001000602958012078000001401700d215644c00075404104880c19045d40740c0120300b0300d040342080c00d02981c01001c15080c080c6000d010342c07840c103501022a4010004001c003001e0a00c014003449850740f4003080c0040c10010314080c040900300038080c0039520001010340c0140100741d00c0c800c44170310b0b120480f4001e42c0d0401c150b29201480c5c0e10b00315103045803a4000c0741d0150b00e61200026407031300e5000b050b000d0440901c010311070130011174015101c8010500c4003400b80c1d006200c2040555048003e032811260001c0c4041881302d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 402566735 1250 402565485 402565507
    0x705060c100507110c01030c14030405072c1012170903240609010305060a1a0904060b0a090603051009050313060906120e03040b0a0207080601080c010f080615 70
    0x71155000c40c000d201d14000c20845656440081c40b030701c4d41080800e642284811000440070b030350200d030015000c600320380c1503003d0100381a401507520078064015282910b440f10803515403501c840c1d8007000f03010800c0008145043d10b480e5042d07000440320000b820070b68076048040d031201c1049071000e809501401e0001441c16480300844111650007415186c0d42406620702c10070002401a0400100a02000040b22410860221416244c01c2070083c00c082d9100000d140c003404c5010100c8491100100c0113541a0700c611a00a0046100c0c0002044010f01c120601581010720b50024075200d0400700c00b000030030008654189180c04064002c903a070059428081e00d1032058075201340160715000c0e80003031090380c0614008250b4205590318603404221032031020580307906220b5003242e40c0040004002c500d04600c024403580d00c180c010707079001c0c55448101a003084c00c240d000780c52035048000034120175a40481c1c40d0010030114144802c02e401c004003c41c0b42c40d040c100c1003c40c0e0920020b9034100300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 402567985 1250 402566735 402566743
    0x41a120a0b070c060509210d0f090b090f0a080702090403171e0711030904051f17010c031a010f090b0d20040501121a060a080402030f0105010501020705060c 69
    0x20354001c035246000c0e0500600041c10040030010588405180c030000c60f800e40004109a80c0c641d4102c3c920021502c00480500d156510980607090090350390303004107118003007a00034585880c1c00b070801c450f907614010703000d94101080c0090b95160b6070803803030a6000140c565001c0d20381484c0c0594401c20159100d2600340e42c5a48400c4048000b40001c604210026003036445001d5644042015040c080c0c648120503140c0f49103004144691383c000f400521201e0500b54886a0701407402c0c0075060001e003064044060240c80b94000c200700340448004020500401d005142248405242c00c202d04a0440c440844030028060041c4c10010702d00280e044c0a442800003501401940e0b5903183d03540c95004200004040c940c1d00101500d80410106100040c00000e1b00d0440e034060b140c10310841200c050810040200020b071100755180c03070610070b11a40714130001d80882d142c0354940700000d08003401010700c0c18003c00000081d580c101070052109981c0422800c0440b1000d07250a41c40d61304052aa6040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 402569235 1250 402567985 402568003
    0x1060201230c2502010e060f0d05060d02040606050c160312030903120507031d0f07060c06110409090b06100914040207171b060106020706050c0c030604030518041a12 73
    0x4900c0707440404114201404988040e04c02d880d07888040180d8414000c0ca40904018014410b10a104500c00514941c000d55401400205803108828a41c0d0002c1e080b1002ca4020301c002502c0440c0801824400708090140c184180012150719440c560740d0000c01e0340c4080071041015201d0031180300f094080d80400700c490990032811300c040d1414201c0100142001c20902501c0c4042132103031002d00201044001000c03803214064070a081c18114143da28101c00a0100c0d503569803010103680040094015002134100c94001251203941c500b01440b4601029241710f102d886079070440640150081d842c101114142040380c07030303c2d00940d00014003e0003004c00c05001c441d204040c0d01c00c0490f4240040001142c1084500740c480462400c1c1a07035220300340038140150303200190a101c1305020341c4c00342101c0700071201211441a80039020900b400c909036021804a440810715140d0300781603400c503101c5140c09960420608038120020076002c07414503200f0340514400c032201c01300d042052200c100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 402570485 1250 402569235 402569257
    0x3030c2d030913181101261602070b04030b0106030501080d12050c1608070209090303040f0f23011d0c03072606090a020102060f06060a030c05041e080601060201230c 73
    0x135a07403503d810202094041c01d201140011590103445046001160642200044404401d4141d95424042e40c800c0d100e002c540005510541a0006202800034000c10203580b01d41e01ca550154503140014050b10810307000036040d508a986590090307a4001c0d2400d400d00c44182000c515900d500c1184111840b421112210901c2007203c40b0041c02211402084114800e0720302c4007290b40c41c8800c841d1240401d860080014655100300804566104190301c8418020140307040b6242e030681d00b6080a21192643c907145944a5240411a0100742c050340880d9100c83c004c1c0c086030310050000380d112070581c051400031200e09440000101c41c2502d0805403041c00f80b040740c072a4107024a01940d1080d40c00d100b00c1c0148a5400014000035213901c10702d000b184041c00c100e09140c186402034002d02514482042040380601c4002403104c5126904e400030400c2c100c5205009080020340c0d41080320580100040da03040c404d5407440075030500f005040002030004081c00d1506c40c01649115849240e001031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 402571735 1250 402570485 402570521
    0x30f080709090e010614190303120f060905061201020c0c06030c0f0301060228110108040f1e06050f010602120c030c0105040309080114070e06090109030203030c2d030913 75
    0x8600c0200540c4000b09541846c00020b284d40d4100302000f141e54013404102e4540a80324000f000002c4c0a403105084210340c9010110700b400392001104d08640f40c44d80445400398441c1c0500c001810070350703031110410004000a40c5042d09040c251a50f1700740b00542c0760701840d4004006811150301c002517603030043c1d62140041e60795175203400c02036480c00c06840300685114080c024501440818162079504c5600403100d541102c0b0f580015a03950744e008105513101d40304c0c1c00e42c6030700103403035900a030300d040304544c1200884140030b0a100044500003001c1e0720000344c03454018032109400250000d4445205410542c0e256000403c950941c041d4600640d1a513003448240810950407103210400c0c0c407084c034000c1003440c103a203162081790881914407401045c80b2804049441c1468401041803c0040c100f0640c2c140c1c0e6540480d2840d4843c4c400440540c001d00c0c0d010011510444910265600c86130740340c0060801000d03229183c0c800c84401d02c6c424110044a0f0500040f42d80050901c080d54841da0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 402572985 1250 402571735 402571751
    0x140102070305100c120621060219030c0225120213050a061706040c060305150604080105060a050d11061806130501030b0301021806070203010912020c0418030f08070909 74
    0x3034040d040004500380402d12200790075030151034512035071048a030f680510100b0b074074148061040501d892001904d88c030350204444602507000700f100c50403004081e41c0001c6c045404081c001c1c105031040403c10000003c000354862098480003100c4c040e208003420381c0102d2000d40c0b0004203034901010841041500b000108512203503035600c148100d0f0b00a491038048190350783d900c0f0741c40b894100d800800d1815200305c01e0003028070907407109601c801100c0d1840520303c0d141d400210b0942050380002841e1303469000b04000c909043d0712010040000340c4800307062440ca03544600528401050850207207401089012854440b241c5103140d2034000740400e5075130183d071403000c40b241010f4054503000c00d0821030407240078101442100c00c070007000c99004407141004802c00c102070344045400d0741d240d905c4044440100e560031010900c0e10365540c005004c031110106c244000d990000151041900382a03183d007022a0700511403080d003250524043c43c2542c1c48030000c0e140118940c2000031528070f01004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 402574235 1250 402572985 402573013
    0x61a12071b03080714120f040206210a0e01050c0a0503190501080307023f030c161502011406062a0312180304030209070509060f0909130c140102070305 67
    0x4404d00410b403035035503030810828040360340300f8078426020090684100c1e040003541003d14562080e8001c2d200a080d02c0c07805440c401100f005c1e4010010081c000842c010510846650500c82c01d805411441300034812480c20052103c0b2174060380c1182030074083c00000203008508805104000c0c0440c41004200c03550f19400c03500d54a810a44040b401003944003c0501041d800d2040c010035040d0f80f6126a00500380702d030744041140910032000e00319200074019611090750a00228020110030a02400c2951174000405142d11b52250b04d4425a45010709411030b1078808034105078001c10580708180e81d031000c0d040100c548071111220100d8078040001c204540c1c94040b0007411003c10346a001440c030344070b2058044180340c18854503401e40d4000c03c01000142890079245030321010504105040500d0744c0c000c81c20540c0102d42c91042040006416095490304452003900407503140c001c40038543c20fa035901c0008122034060844c080e10503480340c0d01160b10800890f80030f15844030036900d00d4401034178 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 402575485 1250 402574235 402574247
    0x60605040302030f010510060f02030c0706020d020d08010b090103020c101113050f030a02042309030912160e0a0f0207050102090906060708030106050d0f020a020d0201061a12071b03 80
    0x124800e0096000c150b100d01014081c02d0301400c81c00c007047c020146441c1d800d0301d01c005a4403042d020f40c00240214204250300380244d0008081ea078000d008250910b402c000c0c00c2080080002007030000050041c002179507142d050703130908002801e00580d9940c204201500d010310940c503900c13606003000106480c80e0041800b8280071200707080000d0000ea220010040e210030040b94032601a404841c10382c0140c901500304080b03c0035016020803603040c2e5000404202d81c0112103194042d400060104110b041400180801107503c0000c0c00213418803520100c070415040c411810414000e07008203040c0503140c4c1c0302d041e101d80880030456544c001c52501c2030103034100100302031207140c1c3c3d180007414030b0401c44212050709900c007410500c0c6a082c1141034505400621031a06215580c07021030317020003960310040211100b6038000380701040010302d000342514102e800140c07400744241c0c844110440c6043c1a42c480c0340d21508803118031ba4a20600b10b4003040407815080741481030318141000e05030003507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 402576735 1250 402575485 402575489
    0x110904150504030f090b07050c0d0c03050703030c0b0a2703050f040306151203050304080c152502030421050c1512063c040e070501030605030d0806060307050c0106060504 75
    0x1484140c401550740b0000440c0740590302028202c3e0700007001c0c406152038000f502204c0d860bc140c0808031550b40702d032519443c01040e80c00c00c41c0400c00c0209001c05101c240d081466202c40f10b1501400000d9035103030544c950041c0440840d072140a914140c004160041c02581c0c08000c13642c0c21192255070320300344103020303201a161b00d0410041c80d0300003084120342d1030b8901d210741e074041d11400e20b16213495485070300700e034040e6910840342d001d0003240d03046001e42c114005002e900c5044401c000b01d60329807032808104512100c128150f44c02088200140c4005440b00c0500b41072450f0346401800d81401d000341008141d40200790300c801d880d80305d0203601c507400028180103114900305012a507122400d001c200e24400003c0c42c100002e803603450b651740814034a925010503450300a01800170302d000204059840c0f001d03200d480360f00304130001c0c0301d29645886208024001280205000401c0e03110140803900c000c0c15450080d400000009e841ca4054030458035454042c0000f001585c2d580e500060068111b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 402577985 1250 402576735 402576737
    0x219090c051b0105040b27060103080702011101141620070312020d0e0603150904080a02010c050327120d02070c0b0c060105121e0a030807020a110904150504030f 71
    0x821504402c01205114280c0f0690f403080b110b440f65210204410f403201c2440402d000644010905040b5075541402194025441000304680b66251480050600503892009001d141c0c9459400300d00c07a8215801d10307410034a00238141a1440c8050012140000c092001c60b08250540803003410784c90300043e04030200c0340200c0b18000d2040c1c0741a0200e031511154494900010202030800005141c8080110380001c11006440102000c171800704804c45011a400d990040010442405031902070244806032004e80c42c080f407840c9000348100c4001c108000765038240ca010340b245050810000c2200c00400d113103076141540c4070f10201850304d020394405c4908645a407100400003c2c1c0340002c80c10748030740705481030240c0001c2e820241406a48030540c1c50140c0c45206100314560300c0b400d0580c600040400c0c0300b01402d40c6909a013005080b02c035000e0407550455008480c1c1c180483c00000180701d0340182240c414486031590300b0600b02e000340c03018038110001d1801c4240402c05070455181640c0c0015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 402579235 1250 402577985 402578017
    0xb0601030e03040b04090209060409090b0103110a060215100e0103050a26070b1009090c0801180f0b100905010605120115050f0f0415120b0901030c030219090c05 71
    0x1081d400c40e20790049103d001003030403041c0320a00648001c0e4000d400c02ca40c2c0a404a0b0074a9034410102c419a964840191200403d54005000340030800368016005071082e90520b880a10307060000352b0f5203a00e6825604601c00080c04035140c1c0207038660400092020fa0700303050304da503164142035440e044512800c40741c01500410b00304010f8803004408141300e5078201001c0c10003144d622495100c070401005507181c02200c50000c070705103e00d40701d0818454021048121041e0801d1a96030840d40901c0c0300c40203045580c100d5500250700c4900d0101940d501c03214603680c91f00c4812241c241f50941da00310038841e908040002c25100c0c0d209002e840800074070300704103040c0d0f642d62009804020084840c1e500081007080140002c540820003050820000c0e00094642941c41d0318007082c0e8020f40310400000b03400c54102c4540c9034054090750b030010404441c0740f03806515580d82c2001c109041d01c0004e0080410080d248510b20300748041c40000d2201c50400d0051440400d0014496444404001100f1007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 402580485 1250 402579235 402579251
    0x50601180b0907051614030a0f140405090402060c0309100e01180506180d080a02010e1b06030a0c0201020d0f1d0f03040b0912010e0a02120d0909020a0309050a0b060103 74
    0x207840d0b50020b00030181500d4861620700c98007140310001242c0d00d0144d6420010408001c04e0710b41c20401031800e41007960b244080101146002000304006600d1041034480500080c4115131b114042c00d90000d9046403081da407a000d0030221401c600501c00c8582d800000340c103240e020140c02284920780c0c0e40090303903119183c107088200150030100318008c4607001030040c082190340c0f049241d4034601942000305000d000d2551965041e1030303580242c0b415070041c0d4542c1e00c0c1d804503000410a40541c60f610002404011681e1800b18407140801031201c5641074480c00d003101c40c0d0f4001c0d411a0001040b090044c41003822030341140028021031400d000340300144202006142901240e410100d1400c8005186401d00d482800d0406820401917180d1046412080181303010b400d1060f90381c02c02c0010003508050406004016074400f100b2034401c0a82c006110313510500350310000301c40603950000390050f25100c207603c040300200701190008201d0700c241c0703a01200340702044000300d2264200740d8050107809 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 402581735 1250 402580485 402580489
    0x2070c0801050c1e03090606040b041e06150f0e010c03200f0f0a020102030d0b06120415060603020909271e01181212140a05070e060a0c030c0f050601180b 68
    0x44412030f9070003401c3d003181f404103002c0e00c0c180d0007038004007000800200380c1c05030300c141c0c0444050034029219883c80d5100b404122040744c86280c109926540c2c1031090482c14001d40160420354801840d50400029881e60402c05000d0f08044500350034031550346119000210102d551950001d44d40c21039441001500290050000390701e2150940c10b90156050002520200c006001c078503600a038821014401005004100000c040c821030047c1c20341d0103140c400740d078408211840da41110f01010700401c006541034403203010796038000101c0d0301d0b07079600025004174009580c0030454110000d4013415045201845050741c00c8100b1111490003041241e0880c08242001d02a610300244405403100caa1800320b1700840782240e2642500602084454240082c058030040449404003011358070001c1c4003400c0d03400045180014030641d556840d0a0850f5000382181e4005d01d8000c0c10891203982600400210807035040505502c18100c070074039611403501e0314a059402e2070580b806450705150b41c60714 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 402582985 1250 402581735 402581737
    0x6090221061e04050405030d0e07091a060301150e030f07060206010b070c05011b0b010e04120908061f0504020a09180605010e04020307030216080a021605030304060302070c0801050c1e 81
    0xc01c042c2190040900408000e00003d03040081040e41e02e400144170382c602e4440d8502032006485600300182941c81c0c2840780b18802c07110f141e6440f0080f003801104d21700441d166142220b06480201c1c0c400558046c40410481d220900300c2c20f030316003501944040c02c1c4541c40c0095240c041d5001ca800b551910ba8075001004090b014110b0041c0c441e1600d40002c004a500039080400380d0f04940070b01038481c00e01901c1c0c1c11101c46082e030100102c004254200010b010711600034900361260741ca80241450f19184900e80c0d2000040e0030000c1c0d0002c18021320b052000d03182072110003000d01810035500e8034141d407005010780f4450b129000e002030240c200b264505220344644015103405856081000c0c40c01c406200003500010306078014542c1c03c0001d02202401104070100d02072040006a6071101102ca000b0300b0b014200707102a005241081c004c2c400c03035601100341c40035038002d451f005031620703c2410149000400780e400750300b40c2d518000030300ca50a110301c0300030404644000144981151a1148180c403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 402584235 1250 402582985 402583009
    0x201030902271803030624041e0e0105030609070e070c1703070320070312020702040518011104120f080f0c100c0e100e0301060801140a0f05040302100e010609022106 73
    0x1b000e0814150003800c046c443d000200f0444100c20180e061a440f213100700310f040f03540359a0104980d088102000ac02503210101c40c0948429806040c040c205130000c95903841850248621204200d07001410092184011880b180e0f045041b03029520000303145015541e100343d594000003400c09a203e180194001c5030300224200002c100c42c500700107903e08030380d98050502c02031072140c0c00b0840d08000da0f8840c05694024250310040e405020030b450034050071199851240c48141c0010f00c0100102e00c0d00500d40740c401d5400c4661017480003620702c2c241c8054401d0810740c1c40c110501040c3e081c60803000041011041e81a41e03030030080001d076505d06440c080c403151b00440d0300000118202a0040c440c03045042200c0b00500003240b130729100d007105800e4848080035100c0c4040b10760104180001c0701e001d00440078035100c80800850030304d40c50003500c4402c86103080e11010345070340490003004400d600000041030814011074071044e50403030840380e505d00145604119006040850f050385442c2089100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 402585485 1250 402584235 402584239
    0x30c1005040b06180406050c071202030904050a270206070c030b09060109090804180905060109020a080606130e07050d11091e0307060c08040e04080702030709140402010309022718030306 82
    0xc4142e9171035880e80050b2500510713428004005000d01c1c4000396404603400130702031458004d0341d11440803031309004c101c40005001090481c14039080680303070741c2110144504140150000904400d4900124120384140b036001480190505400428800b40c8482c07203000b0341d03402017030310b844d6680c0b0b4241d1400d82c1c5403114041c040c1c2804020800401b1803603644801503600310380d00070990701d030162500c90801100f648406051500050400c90065204410381d601490854106090204202c0280368040d40360003640340302d0500a010030400e500400649402c40162007080c0700d00341403e1220842e64011103144c901490380d20b00741c0d16a07041d45103c50300700c081001d801000d10034500a4200c80000720075000b03030307a0000b08000c04070b4050702000c65544124083d1084955503081c80c414180340c240c0c59800b40309510700d8034055103503048280b405035400c00d0302441c001c42c40320054000110184101d102c40005001c41c00410441142003c02c00740c031030b003903860442e2010814040d580b43c49100484280b5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 402586735 1250 402585485 402585529
    0x903090b030603100914010504050303060a0518070804080f070804090f1406061c0e07050a060504060f0e1c03030c030506030f03030c180d06060801060506040501120e030c1005040b06 80
    0x14940030041d41c410051a40180b5100402e041460206c508642098806440907000002003004608141040c6801840c064928450f00c25100844120010000d0309400803c01d481010500340403900301981d4100694441195a0342d86030315047c81d45501c140300e00c41082d0b0902d040481012098030428040702903020301d04090340d0b2410108241a030050810b41070b420144556803204451602c40c03603441d282401b005160ba58204010040c0fa003c1c541d010000304a800c01c401c0c04200c1d807085050b91040c14500303041d88405440d40c002904001c0c86010403040e50440101e02c0e0a00d41d258012610041d00b60310300700b05a0315000203041d29400b0701100642c1c603600c10004104001c0c4a54000c018040684603a0a04116400d0000c4d0032192000e0003547c2c5541c0f20207091050740e100b031242400400c012074481c5c3c60036141200190207500c640b84405001c2e6624000040a91024001c44594000c4241602e200542243d516001824269420785004100d98005075a5040040c040343d19000c02138218 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 402587985 1250 402586735 402586753
    0x30303060405060102160f14030d140903010204030b090102031e01060917030904150306050108190305090409021309060509030307080f0711060a0608061f0501051602130903090b030603 81
    0x80006460003030f0a40d8114480e05080c0450710104040000107010482d02a020040c5080c1141d2141099018140d20980044250364a41d07504680c00c480041e4000c00b503a500c078010321b00064024000c079440035001542d00c0040002050041d4003d6202c1c2c0e090000b81020b80404810a40d0b01400902404c0701050020205100c41075a80d01c0403004403a14504407490310310110003080c261500b4a2069091a200040600c1082014010540506903001c020722086240c1c80f0702141c400d40c9244080c043c8140002c189a080d1a02e40240c2d40e0769030083d000c0c0081d641c0c19a0020300030800010240c901030b20b00340c04a0810100401106e00420700380d5034290351071f04d4600d01003800362000341c01d82c0c0a01110007042501e5000901c46640304010008000801514004c103450801e00000c1842c00c0c080c10400703030201616065560744080e07030020310f415503c40c56051802990301a0752100650b10400664440421800c540c000c1084903119a503a1071245503280c0c682c10290005841c20342d4580c02100c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 402589235 1250 402587985 402587989
    0x180705010807210e0307021c1109060d0b07081b030105090a051003290a1404031d0603010305010228080f27010c0e01210c020705030714150903030306 66
    0xb41019030300d498940e0f855290b55105603403c880c41c9400071a1a40c10102c0c40c042540740402c40c91100c1d00c02e40d112502040b032981e07201c14180c0800c880151140f5100c0c80850740c1a1907c0003903441695100c0081c407101e043c2420301810801d0200c1d540c0102c1c043c280d5001c8804440a41585d04a45000d0000d44842d20f80c020080083c02c0014401d1082c6588140c00002040c0000340300440050507a000c0c03c0c0b00030040c820009403550041c07011071001e0510441c407141d078203241c0c03500707920075058580800d1041040f0180503248034541541c0d98450740110001c810b124065009202040309210050700f0001540f5001e090343c00c01841c2940440c40010003d0455040988a141d200800c150101140080d07e04000c4901498900e1140b1503035540565000854010301101550320003402c00150085c40c880c07120800d0380c03082881c2c14603203445805e2684154020440752000d004000e0030340b0b02660b2518041c2580310b0a000040d4400c41020013101074682da0720b82150110360024000e10301d1541d4100c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 402590485 1250 402589235 402589247
    0xc010f0203090f01140301060c03080109050105010215060406090c05030115091a0904020708182407030e0307030206040608040516030c091e0e0309090f0702060714040b0a08180705010807 82
    0x20f449030500c40c1c440003217240d6010b440011406800691240080c00c0100d0030000c1400d14140c00180d4103c0c42c00b401403100d6178001843d0880e50071401c0752250301342c0e140004200500704543c0406502810850045c1105070024082e505031071110b90f254003100d69880c0e007102c0680c02d81c030450401c0c2007005c100210304240b0000500101d400600090301d428400d544250b440c0d4418481d042420490f80030b645241d01d0607820006501c90190842049040c1054226265109080000b01440b04a60b20301c0440c2e00c0901014008580003010984c545a6031725003d4a12102250200c0d940e000751480503100e0340c141c50680e41a03a8001e8404c140700707410040300b04020035060b00d800c0c880c0321044d00403a076070084a0244801e640c00f040007450321076542d601806540040600001c00804040c070801582c0c40d0b00040060340090280b4000148c0218061030b0405840341d500410704031b110004100101c690407009050007401c90002c0c000000f02c0f81c005c4079848080303070b01596000403070030004038800b544609 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 402591735 1250 402590485 402590509
    0x1e090613020708120402010e15090607020a0f08010b10020d020715020f010c1e050301140d03050c030a030204030c17120f4f090522050105090c010f020309 68
    0x80c00624081d03080d100c0c102142c1090b0101c20018210208000440d60302190701036050384150f40115403000941d6080f4110302070b00c209a4020000070507540259602c40c041741c402410301c400c0d00c5000d641c40d007d01c20301801300c04241c01d0080f049210611540e9100107039501594400c2d41c0540304440c10b00d00240092580c0360045000c500c40d0840b545442c030001e01c1680e10100c1c09031140c0741702c003140c4561200800382140314171092003c00c0c001040084644a01c1d4200030004440c5110b1140c00c614041e20b0303d0086021440c061700c4040740d0f2140c400d4040d8010810359001d100c2c4c200303400c1d5849007a08030000380800010200e410071818002104124005410174140c00413051b1b09011105910b80c44280c02c0c1e0509182c03144a554080f00303a0034010507034a020800f0f800c801c42c070b1820741180c1d0b005203544a2042d1201c03241d5440001c7d20350510311b010211003040c804a000010096801c015029103002e4411340c8903070151201c0101150b005918804206205170061810104c1c0c02c0d04101c100b01d520 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 402592985 1250 402591735 402591769
    0xf15061e0d1d1f0212070c0605010807050604150311070b010e010e04020102030703030e0f030a090f060806010519030b0409050607080a02251a041505060109180504110319021e0906 79
    0x34401c901ca52440f2150307044c815440395440c604447d0803070410700309891040c1e00c150055044014244840d0311898100d070b055802003e042d140840202d1030440c0201180c040c10080d410000c12850200401d4449090481c1c02c0e00403007240703603602e503902007070a414141c4000340540e00403c00301c40042c1c0a0780003021288601030549403001800800141103500c003048440c0080c94040301400400c01c1000f00e00c3c0035150b11f00d0a54190b2800100107030144c070030400e0300340306290f2211003402564442c0e00a1642da003c05002030100c41c815207000c0b90348000c00c0c1c4000010411060018060712407520070341d10452501c0c2e92800b003114400340070840c032420f01d08044c0d03514070550208140600b02c40402034040c0e88102d1901d00b021001890180c100d0b60081c140300c0c10007002c0e030780800407e03da0600392240d20a40c4400000c4a17110744c0741000c41b0141e504510b0350903016036003001284c0f0b00681d0b02080d00c50b0003514015940e200448044140c4048202810f9111501c84c022454600f0043c404585003c0c0d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 402594235 1250 402592985 402592987
    0x6051327051b0415030e0f1504051614040e0c0a0909230604021810090c050c0d05040801060e04021c0305070516051002060f15061e0d1d1f02 62
    0x340c0140880d643d0b1283e08072124035071030800d400e805681e1501c50b4048010203440901581b00311820804d4407039500c5c0c0c01050f22102500007042c1071103010b10814940e811a1418880301c641c1d190404a059006840024499850062000051500810141c2c2441c0004003c90304c09801d140440300244070741041654503034101e4582000344070200e0f405810003020b0000508581c603040c070410205003c025804e00000c520403090210751721144043d00e0680b99588404070700358840b400c086a01d4003403015001b0441c4070310040031100c59003100052040d12003100083c0300d01d5490b00c0945c2003600c1d058900940118043c0341e400360101e0791306030921281d0f20070b1502c00e10b0440706d030300c0749854907006080d8415080c0d6209400c004610b4041d039080d9050545002411040c60322541516800000034151200e00110352450380360359890307200707c80040c00042001250310b404003159504941065607841c48061420211031045440142d4581d95030f00c100d4000c00e0340303d1880c0c42044041486030100c0d000650 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 402595485 1250 402594235 402594271
    0x30206130e0c0403050c060c0d120e030a08090f031602060906120412080708070e0f010e040606030515031203070c0312090f02100e150304051005010605132705 70
    0x101107281c500410407890380b29181c6056050241c1400c02c0902c02600c107001c100242c200070000410158540303000750404124500089140d040600b8100c046c6142c9404001000ba20b4a600540c903d0f028180c1101181c20042010420a0b9648915459102c0700420121514010b00d007035001400d00c51000780c965414000310785103000c814601a182103c0ac1aa988400781d0199402200360390300894914000b0002c0c2054400540300b441c04058441c000c406100b0305014903401012800c007081d1014008010266956200a0041c10152048118172014800340c1c8000d1400103501c1c0c1d0207403651309030107156495501040d680d00c0c90070a812014440300ca907400010041a10444520078001c400e602d818008510400c05a4a501541c030410302200c068429082c0e12001007118403048012100b994944036030800b18908010300740040340c2d0a00300303000818440d40c06005080c80c0620005284540c41d02c5030103118000240c3c4400d01c464141403468030b4050a056000a0b412a851044464801c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 402596735 1250 402595485 402595499
    0x9010b041e05090f1621030504030204021303021e12030a2a0510050708070c080a030914030d06050907031e0218040e01020405120105061f02160806040210110703020613 74
    0x1da10482003032004102030804001c044920306651200f13501c1c82200c6e41003040c080e030f4050f003980a6804042d001c7c60740402e085280c2800001d440b0091900140034410008c40702c1c2c0f428034000c41400032a4000c0e0002d5002806541002090324100c01003603ea5001400a13005200c0d89100400e404003000032182d07002d003010130018480303002034a6210350301049610f8045405842c07640e001d40343c2c9040207004051440415070b0b02081d00e0004000345004194010281001c1c003c078040a20b0184003800300196114840e00142c1c00b170004c0301c00c2a1500c0e80c40b645c400d24141d08452000c0f030300d80d48081c0603d5620030f034200503600401070306115480351030b005000b0070003041c1200c202d041241c016a50004007805a80703400c0091880d804071280007409985070810100d141048849040707268214000c02d440c038194024001c400c4207201c1140d80ca8400d941e1030704626660141940c00f81d00a80c403019a0701c80f950301c07890300c092110301d06074020218545140c1c03e01185910107072410504002400000c074002d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 402597985 1250 402596735 402596743
    0x301111801270b04090e0c030d0e210c090c0c06060114040803030403030e0118030c081e030c03040303050f01140f061e030105040b060a0f080405100c030509010b041e05090f 76
    0x3d066009429a02c40c1d084c02d0480089417080100c0411543c091158824203560008204902c086140703400c103c080c0c2a000881c062603c80f00400c200070404015014070000002541220014201c801c0780c0701d500c0303501000c0018415403c50746181d0304076030f00040c1b013940204000003087d00b0700b40100f07103480d9884031102d0640e0030541e400c03000207803510618025601c09000307140184c0d150b507031106140141a6009001004691401401400045590b01403140007200b40341c2024000b0120640e40e241c4400c000c0e0260384115400c401007481c2030080358610803042c0c0041e050320804400f3f6000c2c003090004020003000003841503980003104000300011403c2c0392079044030884d800201203440794102410401690560820103000c0c06050048440540d4030641700114000315040c04901038803103090907810019010311b00c0000608090041e10025030551205101e440404001c014100b013000c208420b03a003403410b8240003981c1a4000740c0b810000d41d40101e030014905400c80e01c0c07141040280a0030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 402599235 1250 402597985 402597989
    0x20607082811060c0a02070315090f0f060614090a09111009081c0e06031009051003060b0a0311013e0d050408060115120f0209030111180127 62
    0x107402d40d007801c001003100700b003482d8002041d98401d50034201c01440081d650209844050100ca0a82c0742041c605000c6910a1281680211403120074400500301581c1c004000c04040314400e25108000031041000c0240b801451001401100030b40c840151480c05092020310582d180000e10312000410394580084000c80c50b0305803a03103140d1504d00f829042c01c020056881044c02421880c1103044141c0c0005503010940084030466165100d054003018050015081902c00b54600001c4c4240f00361105889011244240014080f81d1640404d004040e034040c4002858150381e48082035096000c0c054a4809480480ca201c3d21032050403c0fa07049441000e0b45a02c010315082c00c7c0011071142840750009a02940c00c0907071070300c0d14000d4840c0c2c3d591814822a84241b0304105003411051141600070031192801c4814400c4001828000c03000b54071404442d4400c0d803034041c50b00842d01d00c1406076642c0d0a1040c0324400c048108800654049648440003220340035002180c03088481a0800c04c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 402600485 1250 402599235 402599237
    0x11d010b0f03010905030d0c050c160510020c09040209130c1518030b010605031b0a031a010207081009022215060801150c15020a0e030709090206070828 67
    0x40040c00001407184a90441c4500341c0070b0703410f1980e00700100d14000103d414141d9000c80000c2d111300600004c44a50203080c02d500e2480c0211000c030180103241305401d0003a20310454800d450080c00b82416079032188070340e18503a08596200001800f51a01105040e0301040600140c60007003041d641380d050319a42c9400100c2a0901c0742084103200394400405217820601079020b00000c0d045880700000c1c1c0744148141800c00c0000400255000c540740c18100d2038980074884180ca80c5403400014000c1d001074500070010085400903950150b1000a80300c04840d07207440038181c0c80034070342503c2002e8004000140d8000e510840140745454508584446140d030038180000ca0143e80b281c0c402c0940e1980d480b0504000300403005010030241c40d100c0484c40c4a440c2004941d451207450404540c0c1d00f40c0600b41e070440c5c4041348082d6802e03000030350304e0b6410900f10306954400f601c65010760708661045030044d4200c0020301034100048c1c01032004010080d400c00d00805641040d8800741e030849031b5130200ca0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 402601735 1250 402600485 402600491
    0x903040b0a02300316020c0d0f1203051918020d0506010e0f062b0506010b04171b1002010b0907030b030d08060f240c06071106011a030405011d01 64
    0xc040c100031000c26154200600300c000d02c240380040d491041e01002e170401e00d014440680d20903285008020100503540e001d04010b596048908041100030081c050076101318a441c010100b020707109201b8944582c110304811041e0001d40d041c490300400c0320021444118481d03182410142c1c3c0c1e16403403154260f220308001e000d55810400166540c1801401ea400180681c805200e0315555034078100b010010b425101d0031001c88000304079802095030000c00741c01c5002c5c210021943c228810001c00985260002400100e44590074856031002600146e0100104114040086140c182082009020700d403001140900d05080000c4c2d42071810768440001c6599402201c00c1e40c1405d125102c0760304800d080c850280c3c9080008034040c9104070110901c0f45807410f01c40003042e01030500a500c00c41c0b90f07801254844035182c03900c1da60b844040d03c8490204295000300028540d000850034183d4802030180c0c40c0c40c5070000180d005030340010300116079554072100b0384400c49030b00030640040b00c10840008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 402602985 1250 402601735 402601753
    0xe030f01022206020c010e1903150c02070503070b070f150506100809120c01060e0c090102011d031909091a010806010c0f1b030203030d020304060b0a060c0b0903040b0a02 75
    0x102560700302e0034050074001020b01200b080071a4000c80c2e2200032040030300b800b010101c12000050301d00c030401840e8000501c498503001c402c3c480121b047ca0036041c0c010380c007041119803000b0b003681c1d100d8203846105e90541c811075050100040c2400600491403058045a1880003650b40f0b034000900180550556541c0c0d80741004000d00d81110380c04000da885043c40309040c20200070741c42e158540686205000314000894980b248025403107240204144040222541004104041e00e94098484580158203029110000070b070300c0102c0403071092184004510700652024120010380e0820124801c0c810002d40009143c2401e00540c0929a500521116100c90380d10024000000181c0190304015440090000084503d04d9034044503030004580445101d192504030b012003401d4100035054000410703200c0d620780d0290040c60003244035034401d07c50a009401032000154180c030410700007612624044011612411540c1d81000209060380d152076200d415041e910ba100306810300050344500300c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 402604235 1250 402602985 402603007
    0x110105122a030c0a30021c05091504080409060602061807051e0307030804030311120f070b0915100e090106050f0909030d050114030d0e06040909030e030f0102 70
    0x2400c1c1e0100d00c5481c1c00c41c1031140c501c0d2860b01451403110240101c0071402e841c500001400d4421050441162000d10b502140600d000303500810150060607151840b034101e82c0040c0d000b00c03445100c4c403100030014202c018000c41c1c00800c02400a80e00103c04100c0840d0402040c001c1d18081c04a58004100a0402c241c2500383d6440100d02e4030501c0e08021400e0040b81e841d1010340803680a44c0d18000c425410300030020707040c0320495000411201d4001f41c0042050340184903c0d540e002d03000f041d68030001442101148a01c501c203196103043d2010810000044c8409000c00e4021136150211010340c20b0400c043c50409009480c1da090103001d242041000080500500d90301822410003408841c2c6003002181100c20550405485400d84500060145104000f40e03024980450001d2286503500c100e1984c480702d880f159980240154075010b11064040c803020b26a02c480a0306217480e151400112030020301e11010110200007400071412287d580c02c00846071a400244001030b0b4900350761a0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 402605485 1250 402604235 402604291
    0xf2f0607030903021b060d0513140106080a020d061404080c070f0b040e18060103060b1c03091802090310020a0e032a06190314180a11010512 62
    0x24034000c040c200342600002950204a1a108040400500510410780b000140050280e4020315425074076020800464094850200d14154000e4080a903414a1180141c1c00d803866800b0300c144d59800f01140c8801401c010248040c01401800d0004e440e14030040401d84101c1d00752015503500d0004903a40401c0901404900000c0c0b5000c56000502403070110480d6480c002ca12616000410801c0001c081d10280407409000c44030300e0043e07031505e603128500a4020004070303d6080c05081c3d4881905005440c00d0b012400301c079095103d0342d490a2800300381c00b240a8180b00e02e001580d8080c0300e200120388041040c16136050000714090b0b260404c0540c000e10140c51500440e1299000ea075003074036442e6a228603082c032131a212440248a03410030002c0740c1140b00c0c000b481c98258803003004051141d98550301401e28050606034060480d01c0d00708591007030300d80400203c6815005842c00b40001040b034060000704e0441818210f0074050318090b013180080701200c2800341c1419110400309200da842c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 402606735 1250 402605485 402605491
    0x7050a0309021206370e0715090f092a12061202030111071e02010903080f0a0e060910110a02040203040b01090b03010c05030a0504020d14010209090a14070f2f06 71
    0x94444180244445c880f41d030700c0349805140465950740c035032507401d80e0b0f2401c0c003a1030007038000b150b40c94800c50345000b001005100c4a100d02e100b40030702400042a060304500070900c070701400340202c103083c03581d036501356035201c042e50703020024030000e030314004044200b03030091000928802101d000c08003154014142500c0c1c03040710818010a081100c040041c04030f1003041101100710004901041c01440140e6801c0c881d608003400301ca01c04118480503142800c0184104080340c1d81c1c50780303001180002e0000d03034000d4006035a4400f25175200c0711492481401980301048048080f160501d4a5401280890740269000d441c0e2030b03005001030140901c240034510485038240c008001044000800919501004d0400c013030711a00c03040483c3c19580c1c0c410001080d01d0304208602e4030401c4034010117000b0360001007940d003e00f84120000b0560300f8280700703000d038800e540440841c1c5c55481840403181c41b20910001018454500480d484c1ea42543d2100200491100045c01910004507245440d1075001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 402607985 1250 402606735 402606781
    0x1022b14070e0a080f071a0c072c0411040c090f06030c0809030f0f0f0c0f011d06130b0603030d23061c11010201090618030905010c030807050a0309021206 68
    0x5e10080201c5030b030000b0302104480b00400d240903a5a0001f0111903a81300341c1107504028403400402044044000c90601c043c2501481c054800c040d84c60340c0b81103545030440f0090701c2096070108003002424560044140e2001610700444090b0302d81c0807013010044560131000010740c0d41e071100a04580c200031440e400c000b0100041d0704115003a40000380d036115489503080d40e1b480c08035405070040c1d005070175520994106029503400300343ea800c60354001c050050400601060705541e41c41448000300e407a41c054400b140341e815101d00e1585070041e500c2400f51600e50544410080d4682c000300c9403141c0190190f110440360601234807400706486060300500b41d00d00c980000d140039480b50111881224a080d4811907a000c80800c0d100144d00601e8104000b80c01c150030444106825051503080c903100c0d6100780c540d0755245813984011a10500742240040100e80c081d40401c00075402100a8070320310510307140125425034542d002c40c2e41010400e0017881950301001c140803c0101c8846001000040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 402609235 1250 402607985 402607993
    0xf0309061b03050a090837031d030a020d03020d020601210609062912060c07030804020d0807050c01092705060d0c18050901022b14070e0a08 62
    0x902080035030280c04900740141031200000e1a408214003400000c03000302800019208100d110300105480100791108618110064500149080b819415038000d2550160340b1a58101c901c0c031500c482003004440d005600d480b46405d0200103030390700c1c40c4000015100354040c0088180e8440081d10f8074106802001244807400703941102100c0d030a604004840d00404040355404a40c05c14000030f143e04510301e12020b050f9021002d414040c12542c100300d403416100900704030402c0c1011600e481d410758800c01c03822070400442010a215942c181d801034001080521900c0070390751610310b9a440500d04480e6038201c000c40100350341c1c1122a41c001810301c000000410750120303002030b11181d0f5211840c85000c0e9520045082a12581c00e201f14107680051049a1582c8418071030600c0900d140b02456902c0c1003d0000e10702031410b000340d549621300601480992003110107040b1440303900001c1d400c0702580c0d238803a045040a0141015028001540714049004080402e02c00ca2010039044100a540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 402610485 1250 402609235 402609257
    0xf0a2a030803040b100e011415120609040302070510120c0f090b0c010b060403030e101106270706092903271c080112020306061003090f0f030906 64
    0x344034002c8030703882603002e030203e95a961450f18540b002c07803994021007090344800d070010405103640610302d0070b0003070115185030803d4400c40241e6401d02c40c18503a40c8403030102c1c2002c01c0070b5051619081e41c22500c240143c0740710988038404141d01010708210400042c0c0c12020303010071081e0520410b10800c220f481c000f110281007080140814944d03100300c40f0b5413500086c403006002c03029408040003460081a643e51280c2c1e81c01c0082c018100c01c201d5501c104203403424007000070b004030b105008412017034002e4106503980070001c04203200070007510b04a1021400750340340703036000a004c1c103005841e40b503d405001d83d00b80343e045c51400168074000d1002c41c1c8800500b0098990040c1a00d9006807502d5160401820314107496460f00f502d039001584911035510442d00801d0100304640480f01d481d642c0032181d03a641c6488010084188201a42540100b4049152410301d0702034540520380b10b04010a14084039a05c41c4003008103800c050341c1d5540b110490808050b408001c12000781072a24041072000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 402611735 1250 402610485 402610493
    0x9180b0609070e0603090111030c070311060103050d0503130f0615050d030e0910030503070b1f060c03030c051306091a03092e020a020610051005040e090f0a2a03 71
    0x1c22020300f20381c45081c010002494840094101a40d0800c42078001601c03070a0a04000c09035402801049021400d20200c0390301c011400503815049940113001000604807541041d18998000b910080041c40d40304421008901c83c0168030384400d22540c000610001e10404590025000e42c0006116039000000a80401c2c0e20191191b103210048903034900319200e110940284d01e40c00c1d44020b001d800b02060040601c4503584a59100d0000d001c061100c0f94a111518843c901050040b0004180402c503040f005c07038860340c030041c032503003c40c207125261400c00e0410040500c0d0603440030780044d030100403e00c418150140c0040c400c1c0196140c013815414011078540e15900d803040c1c0d2030344500054034031501c903207501035140704509140719085540348a1803100075100c1e1000c407401c0071442c1d80f2080000c0c032030615000038040c10b200c45d59683e05090519102050390540034149030418418a080d4003d08c0d4818041086407a11503a00c65440024006004030045007800701d0f15440d4281900800201d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 402612985 1250 402611735 402611747
    0x405031b0c0f1c0209130611030403050703050d0b03250527041707110111120d0c0e0a08030a0809120301060302070f0506091f0e030a030c0909180b060907 68
    0x2e208503400c0c0074944030110700e80c80d000c0c04000e000c0c2d8001401414040001303120303401340102501410043c422000c000300341850512003942d006001840070040100482c2c8202c02512070307a61180c5001c0b0309200d010f0006413034030f100c0003205681107400741403190344190400800001008140d46048106103000d00040040041030342d015107042404c030008042107040c17003000b040000580300e0a5120401030405100344580b00200c58040f8461700b00740785d054140064520300300b01d0801c00d0030385019003001c4803a001d464a00c0940e070a109003d1104030701c503514248a10044e0a98400458507103074581d000800c01c1d2406000c3c4440d60b0000300310002d010550004170390544003d424090303540c11f03091034202000e000390003000c0c1c110b002d0a0240142c10202180c0c0580e8004210002c060702042d0110b0042211142409200369600c10041c05440306c0c0281c00c1103e0203034040c1440754120742d03039982e00c8041c0c80c4031402e4181c0300c0410401c01d4040007030750300c245604901d013556100514588220b000d480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 402614235 1250 402612985 402613009
    0x15190b010c11041116110f010206060906040b01090905240d05190804080f01050f1608011503060b0a031e0903081f0504060e04021807050a030c170405031b0c 69
    0x76541341c02e094154600c00d481211148071404600b0200320400b400c04005540d02c40360041d1040b1380301e0038186095840003403844c5c060390000b000494140c8079401000001d1408040c002e040c0004450000b4401205100341c42c8181400c0004551118030038843c00c0d4a46402c8070014400e94400c2c0301c0101240000441d50038002910b52000c800300c006041c61750702805140c2c80071072103200d0220703410a000019044035024115101503011b491f100c01005200b00240d00345c407080020720003001000004498046010520304600300002c0c065110300c0031b0a034590003805003402080c1c03a4040d400ca070020310503040c092801c444004012401c40c56170010710000000d001c2103144490314034416907d4580075004c0340105401802004525907410301060000700803101030b84078442c81aa0343c4605a440e0102d684502d8a507982e0502d03010780c01d00150020024030b803d071020401c10041060720070750310041c054000d070b00036402140c460407407101c02c0750003140f44801c02c4126080707401d40c1251920f0f80780c80c40315 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 402615485 1250 402614235 402614239
    0x6070b15010203070f121803080c0c0103051302060d020c030309070305060601090f05090a0e0f0a0b01080705010806060315030d0504030212150a02160b0705070b070e060904020c15190b010c11 84
    0x748842501b1411210300036400b101b030040781c1d10184004200460310000700020790281040d504100d0340785006504070380044510200003114400c4920062074110020b20f10586842001428400c0c030707800351891600101d078401e03010380c032280041c41070003001c0040c00d910031401d20f0070202040c107207003201401c54514412280104400b42c0480c01c4019560070040b0051200000c0b62a454045100265034142a54081d590843c208001003040078020030700703500780d070810f0b1100541c58492100780015540b008101c2c0e42080007250000c04a0f503028040e03841c074251070703982d12904c0d90b00318010802d60444100d04010943c0c41040c0382c00d0364400200c85190301800d203020050b156003125128142082040c9001050f130340c140303030820030401c0c0c00c0000740503058007601d031241c0c0b55541c52034103030f171035a50708000c49501a506200c0301a4525142c3c00400c0801c0c1c8030f4041d614146011045488084070170b44d251321303c08080f10221543c18281c0c1c401c40010643c00d10700322005401585401890250311103800e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 402616735 1250 402615485 402615503
    0x40b063607020a0203010e06070f1b08210a020d0c08040f02011101020d050c0301091401030c031e0b090a060c0201091a1b031014010e06030f04050c06070b15010203070f 74
    0x1c0e868500030b20031594042c1e000341c000d001e40d5421207052601e645003103c00b0008104441c2034280c48621078143c682124080302c64504425800352282c50386504860402c2c0302d000c0d200d00c00f00615000500720103001e940d00020142c0c0303941e05001d0b03905c103076016007061303070304002d03202e400c20020480c02800320601c0c07502070800200100030303d1842400780c400c00036920b1076a403d10050185502a00c0000d50483e12582001c2081103416034220000003001e10000d40103030010313801800441c690b92030102e4441101031060100c445103660300390804404555091041e0400032082081c41900e001d034000103031030752008100344402030b81c0d0a618400300070f8100b8660210a80003c1050036828001c1c84103200c80201180c2340e2802890b000342c0c8203080d0040144501c4601c0c00d4039034550060030f01100d9110020955070031a0707505181c25014100040080d1014480c0c29800784250f11004000c001041c0100062140780ca022840313058004800c07440c0f50b0455100300951400306e129141c1e0345030501d52000c151 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 402617985 1250 402616735 402616741
    0x61804020405060f04060e040512070b18030d050c07030801050a080307030c02030f0f0703150203060609130f020307030b041b050a180317030921040b090109030605040b0636 76
    0x4c1140d5011101d03002ea001850070002191901240804600c140e202d00c0c202c1f0315140c8020b40080343c1e405000001060341040e42c020411500d081003d612840340f41204407818001260017130401c3c1e07141610000851175000030f6400515500203103290242805a84595040b0319241e40185c1c0d80c4103542c405010080301b044c408045641c00c2c01883c1020362000200c802420103141c5103521143d56100032a400520242e031440383c200c4500076a4440d12004107542d06010f404002d01c081c011003c0880d03640c15076911409040114184080c5024003031694002440c000c400003848200c603c501403039502440001c01400403581e00070f00301e4101588600d040e0700d002035020402004c004054100401aa44020f40c5465104140010b50f12505010048441d04600d5650b00d0303440a2070710074070020307041e0100006e00c04042118014541201c1c185010480c103903403034440ea0300312401038401f160441405424841d05241c46070045120511800f84603500b06d07088140c143c11040c0420940308848031200c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 402619235 1250 402617985 402617989
    0x6170106270e0a03030b0127060e03151008070b0903030a0c1502190f0e01020715020f0a06090605010f0b071b0b0a0906030608030a050304060515100908010506180402040506 76
    0x441c440d03840b500301ca1403001c01c0e240c00780250007142c0c010303070006005601d02e120203940441e50800c0200b0203040703100075078140b041c12581c4038800321285805221314040344450100c0070311028404c030700d0440700d00a02420103681500304101a48110b4004030117010f02c0803140d8012041301c0c9402c07d03504002040f440300707140000c0e4050030492255913a40c03000c1580c0703202c2c402da000303110b858030100d5540b440004424031044d540403940a030514010b07030203118103201841d2800301800d941c0c0102e0040b20880c2000728500303440c103403c0d100100c440c1e9444400e032004008081c064117014000d401000d541143c201000c40056008030303000540b00c0d080e010100300500003d01d1360100030341001903c0a5407203c2400d0050030b502410b114100000e4500203000a13828004001d0b114041160ba4a0a00c0c6845640310302d8081c00d4090180c0440140007464140c0c196200e180b0201d0344100c81d241e20711074a180c1100242191801400c2c07d0142c036401e206e04810940d83c12045a001e64126800240c903194440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 402620485 1250 402619235 402619241
    0x9060905060106020304030c050409030f030e0f120712210c0e06160b07030e03160501061d090106060201050402100315170307020a082d1203010303030617010627 71
    0x1800d00e008000c00480c01c07690200052042d40e0260004a02040c0d4800601c02100e519000103000161124803107103400340701340c00c075410250100c0304503003141e001c03000c0a504089156440504003040000d1042c00c2243c02244004042c40c24101004a03402082403030000d805140c1102c1e18055451211040345c5000f240c00302c1c0400c20141545131240c084032070010381e0b4420344600769039048003007001440c118030034090021180800b5000c0c50502000b01c20390f00500381601001c81c3c15540300c60021404445040002642d9090414000ba4509003510b8203421102c180c0c1149086906003020400503803078960724480a6295487c0000d0444d144c00c50300038100301c043d040342c410050f1341042c804000c00000301420b85176008991502c840c1d5079070302115540701489103030000c403101030003200840c0c28141101080c2c1c2c80501c1040c0d41c00c10003241d000d000e181d44240c03c102c0200b41d03100828480480344050500f804c800007030007000094140320b2480059011400d10060528040b1200c48104030260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 402621735 1250 402620485 402620501
    0x10608040c030506160210050624120f2409010509180a080c0d03090c030b100803030c040f32010c0218072d0e040b10080f01050d0c090906 61
    0xc1600c4c118141100c0ca0802d0664010340e41c8010310455004001214051058074001c1b900207108410294400810580a404041d000400d01320144907140c00c40c41c2032400035118450088142c03159261581e051500d4a80501c504a2030001a114640d0300b529a030318082e066810443c3c842c00e0540c2c07000d0100301e01191014024545000f110048800c00c17801e0b1000e440750040240944151010b178020840c00c58111440c05001d01c1c1138144200041551302e14116040083c8825241410391a009258616441a120b8408450340082d04000e010980406103000d0004100084082462182900305040c0314420710100c298031031090b51705580c019501035103400e9028080c0041010140d860000c0d2041c107c0d682c8020682d05200316124040a490304040f1000d902003250b501c598514041ba51711030145d4845802c6640c5116a072950f58807840150390000b0702d561210024541510030000810040e4000303801500a81c10000020740d82e0441c440c1590a041070010f10901503051280c0680002c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 402622985 1250 402621735 402621743
    0x40b06041107050a03030b1f021c180902090a030b010303080901141e09070515032707030602130b04080606030708030c0c0f03030d0207140f1c030c2f06060307030b010608040c03 78
    0x2502e62230045c0e00416003c41200c8010b04040007550f060b00207549034211600722200249640c0320502c01403405601410840b100500f2604103241c40c2d6860658980013a003003500400c600b0405c018150100740500c0c00a08041d5100042600301f44540880c4001a010440c1401032400005854000108405001001c0003008840015501c01c50741034154019102181e042e43c02c40e58404000c0381c2581a21080000c00004100181c03550b1a0007000350002d103c00c0300038011403400020300550b600007804c00703841e610001d444036003401400c0501c0c14038668003158143e0014443e24030361680c041200e502c20705c8155040002003400d2000241148aa000103050075880461b140341400350f01002c250142c0f045408070b4846943c048801c0b95124100b581603003c000106000256091090b000013605064a007802d98007810600b16050303581d80c0119116449420030703490303000410310401c03060341c01a41c1940a0898a819520340c0030745080d050080c0c0003400082408101040390f2004000d0066400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 402624235 1250 402622985 402623029
    0xc16050a12021302270a121709060406110c0d23030f0c0304052e0f200102180a030f0f21170115091802070605040b06041107050a03030b 60
    0x149007015810044e465817456410a01007548503402c0604104040c3d038142c0003581240441369444000e075110b00f40180002400c00d20181455843d03200103030020703040720303210140303101011420076142c034080641003482503000d610310384040348008503910054110800d0700c4200034080811a4550b115400c00384245c5980043c00c010a6600400600103a410880d5000c1d40518103000c80d01140354458078140e02c804482909403a0140070300420242c01d009030500d00c2c0300380310310000381d008007140380f42d0403031165000a003030480c0e215480c204107030800003140c0d29010f01d400c5444081024849520040c81004d40350f000c4818851081c1d2885500345089030003009042903400028050340d00c000400543c040007400114403454455075000207400c180e41e0316502585041d141c1242e40c0c1451000c003000590030000e240200d00c0070b01400b8070880c010400f080c9142080d40c184800c0790011045071030300c1e1030244004c0c000a18003103601101c40d501840d011884003060f41c001200c1d4842110344282d40d1318 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 402625485 1250 402624235 402624247
    0x10204050607110a0506030405030d0510030b04050d02160f03060f09020901030507090c05090102030a0e130e010b0916050403030503100f030317060a060e09100f08030c16050a12021302 81
    0x1030030f41c0008021034240c4080b001550f079102401040c0c041580c00400700e403c00e100c0c030001145a640a23503800b8040041524050380c1d00c0d212161511000c6d20142e441c0e80282d00140754458040100135030491001c2c9801d000a4501844030395000350710300008020700e880740d450b001d404a0071b07002448aa500186419025696494559a5409648a0612010f0030420b44c41e85050082c01600c0c02c2d80c4044e0091450001440022210440b0203102c8903800400d50880c0c035032a041c1881000030300c0313064400015107941048200100740000602c480a14200c0804050b40c40340e208090368220ba0340b50800f00e8494480c1c440f02ca0413089903411121840186c110004189030744070303903000381e00203460521000c41e88603942801541040c83c01101c0c0419143c441d0340806003048a112544000fa086a09801356280ea10f03607254034204c6e40c0110015031021406a4480000b0300076181040e000c46100c01c00c4514041c00b20b581c140705880380010341c40c0707010b9000080d51075040500340543d00d031030011035540c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 402626735 1250 402625485 402625493
    0x12061f081902030711070605030f01090209040603120c03080c13060f0c050d26060901050d0203030c070321030e07050d02040f0c08010f081914030d090c0e0c0306010c080903010204050607 82
    0x109841c541909184101b04000460602800440b2b0082240c07030069035a5a08284100029504c201d00c2503802558035000000030601c440c0b00280302c512640d50341600320300325040043c030814001c0d254283d034a204121460b080300035418020304a440504142e04128132040c010f079544540d80340c0c040c3c41802040f410302c2c896a400341510400c1380754a0107c40c0b032103002800300300b050482224200e41120101005128500d016504c80780198802400c0341d1a1205004c803a5003050380035401200d007018055030104c00d2942541130074036002410301d001c03c80c02d68002101543d540750360dc5154000e243c086503a80540d201c1e50054445407140c2401408403901101000300305050074814560b20903044c5c40049140000420681840741000c0d41801d00b211050320354a801c10071125000c0d400d880308004609a8005a00541d0802800b030441209024a0560040a101402007000c00a070100b0400c202c90741e0b0300818090503c6401500340740e01d40c48200003190081c031035034002c60350001e4041240e200300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 402627985 1250 402626735 402626747
    0x3091a040c09060602010b0a030b151804020f030f0c090601120c0905030d020d0207151b0c09050a0203010302030a0b070909060f1410050d0b0d020a090212061f0819020307 75
    0x22048420100303d0f10740e031000704900300c6400d039803480d82c40000b038501000030410a4441a810030001c5007041044002c040010b0f48105c610a01a680a4441400c20080d1302c0c103217103104010003043d0040c02e0518203000c80151100e080c0020b00e440303080f1682c0410304030307441141c0300d10076081004401c04c441202154040d043d40d0341c0d44100d83c400d110b00c44920789402d101117032611418a198008213034007404d02d007060103a41c803940c001104005060340c030390304803074000101b003400d0501400400c01203d003032040c00b1007503400040020210500400c010001a2000a03030391641c7da070040c61880c25502e90700c03000c60f8151a10741c40103074035038185a400b00f9041494111a412034030901340c0800c80640341c5060164030404c044003800460000d100152024416820a9066440040c91a019071840f9400038654085a41068442d140d01050344034111800a44450f08100101c4241d100f13000800304401d6021149049542000080404501c0d1400c20000e2204451541c2c20155241e1500c1c007402004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 402629235 1250 402627985 402627989
    0x204050a0e0f0706090e090a0206121b1e070311010c030e100501030b060d0501060b07120e0d0503040626090312100b07020d0321021309020405090703091a040c 70
    0x200d00488005502e120000100c03c42214020380300d0182040c9440c00c1c601c03103100010b051003a94000c040c10800183e031440e0040610500400001220f81041465540c7d28101180c081509090410510715402c0c0060707078002004902d98400c0f40c0c0c5074501d1500300c0c1c0c11044d801b08014198205032004181c241c1640007610106000c004440c03480301c240b0414000c0d201d0a200c041c0030303000308c0e2000c540c95007010071198030402d000b90300208100c0e94580140e00c042d480b2a001b5502c00c10117083c2400c05c554403816841481c2412140c0054a11068943c503032240b140e441603609004259803118030040c2d004006064400c83c41000c200c49180c09a030060710380d4011234418a2242c24240007074018002084000142c61940d43da182c2002c00d10303401d020030505039803003d9060007840159004100c2c003001100c4612604042e015031140c5a11200c10f10320700300c0303030802c0b9041d500600c0f040c001902c90512107a400322081c50045094012030820150486488855402004042041009010958110f441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 402630485 1250 402629235 402629261
    0x182a210102041508040c050f0a080615040c111f0603140c04141e06010507081305030c06120a090c0807150810181e06080a060b031504080a05070204050a 67
    0xc092510300841340d9601c00c490003002d0f503041c0481841030b81068810922882d9010707080003151030329091081c0c6041e2080720407112192407407030142d8503030030140155400007441d402c10f0b50701400d0040d00303540c58401c0c00d003121000030001e900e01a00047d407904407034011504100001100090401c816841e40c03241020680100d0070a81e100078420b40300c1803d2031160310300804100b0785284902e02c081c8144800381084d410400140b180d040461622030041100380700981a10700c5151401060606040d041601644200024080d01c08415400c20802fa80100d24000001d8603031400e19181c8012545c503048032006108500002c115400c04c8481511a0032003501d54290715034a020311510b45d605240211043d41e540d02ca40380f1540341e01d0346c01104160444407980c0240c1940c42245504071130b6903520441da2944074603140b00034071807180300c1c03507248200c107501a0058441140c1070703050341440600024404680011100c000600c5002a40e0b13113164000c005114504000c681140070b006c003000b05207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 402631735 1250 402630485 402630509
    0x90604140f0d0807030c06141501080a02030106020c010c0c0815100503030310030602090a091802042003060d060b0402030112050114060306060105070201030b030f06182a21010204 79
    0x380741c1c034280c2c0100c400103030321886041c5441c5032580e04640d0a21610004c440361a01c581740700120300d50080d01d19100c0e600860f01341c450f85516400050001901501c80b0261910400c01486065400324001c400c1c280700b8203055583c07035076928001c6031035611980f0a8140d03000301203541410040c6030101d0350140603118449145281c0f240201610b911040e624090440c60814041000910715000380c803d4801c01000c4251560340c0b000705d00700343c503407040f80b080d000390840103d20704505d040c1c407840c40d044010b4a4484001c03a920001610180310241c10148030b054030202a070100402ca07085101080000380040d1344030b5955020b10501d98a41e80c0c0110b4140d42230400c1c02003d810020041d030300c07508d0001c0007000d03a904c41400550341a071004006a0405494a06604d81d98504002d18a18212003500400305450145e0812110a2084a000801c1d8008041070b181a002c00548000042d0000540d240903000c8200002c41211020040d169141150f0302d40d00b11892040d4081c104455001d4141707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 402632985 1250 402631735 402631759
    0x2609010b10090501020709050411040603060209011202040323030f040608060f010f0f05090d06110a02011508060721090f060f1404080a030e0a060603031b020619020309060414 77
    0x2ea684a00c18000e060050388400300810501c42550403041e080b034003518054199001c200040341c10b0f102e1941003a1070103500012282a15640258100d204510200c1c0031800d150440d030711b00c000c0400c4415642507104000403c1c014406061040b01d1612441e0f07014a5500c603621103014082c0030048900500c0344549200604065000303100f10344140c41030340c0d80c040b40d21240c2681551203401200156070844500054000011654480c01c100c851400c0710061b221a12020000c0c255452002000100b0513045410000040000384007a04544c0d030f4200074680c0301e2070300c19441c80f010000000e8000b01d070424001c00140080107100c0781c0418000c18080c09180410b414200c06d40e0720700040048510220400034010541000150206075618500481c0840201403403e00e400b9200c40140d40040e582d000030410550045500b1501d40411902c85203500003940005440d030040d07000d0101c103459201d40300301c8068824002c80711090002002e0395103070303a00c440b405030f400c0e660721040c0c87c041c0c500400a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 402634235 1250 402632985 402632987
    0x714040303210219020312090109020307140310090f0b0916120804080706091d1303120b090108070602010b04181509023a122609010b10 60
    0x11141641d8064540e505414511004030000e420100d002050407582444454001d109045880280c12590360003076407076861038051540900c0000e010018181c0c50324407141c005071804203445d003c442c0f42e91800c0081e090107002190400c406001d031002201d2800c010310040205a103450741d1124043c0f80c0c0c5040c582c7e03030001299650390401400780700da40d624200401540000d9843c505c1000c0c840c002103404c1039035030032005d0f1038a015a045000410715001060128036a29000c040040e118202401e4040c00d003502801d14803c07110030f000d000c002e03110102d51040f0709a5000310103040703009485203400351b941c0c584054035840c44d8000d090055082c43c1ea28111442c05000700c402080c00d281c1881210200b50b610702c88074040e91010111110307114020380002d84d07201400180c0c60310705040e0102c0981d12028210800528020800e4040305000c080140801c080b0312540128218a0a1050400726001d499a070003058140340071040c900c50350200000c0c4141034010a080b54400e480c444032030194800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 402635485 1250 402634235 402634237
    0xc08090a0b13141516080106050703030e1905010b100804020f060c0f03041e050907141e0c010b0a240810170609070f050f0d030203210714 61
    0xa084007426202040452082c10303040c10095204a43c1c103c1d1501003503e106052140c5107031580180074280e0b0403c18021202100103150803414a4809010744c1000c0c005405030080d0480a010142e07500e0310845008001c100c1c0120700f001c4072030340c190410806d00d0018040d001d071304000c602030503039011351103012405031000b00e00030f50f40140350380d000407650002e116141c0c0214044c980f4520441c00c0d080081c00080c001800a0205080840306190385810141203155555000e03d008145000400c00b035150300030400c02000f09400c2c0020ba031074034011201841200450003000440b4400511200034800552100380108000d4801c03d075019075424513624a05c0414000e0451146090005c0900c2441116600d50184040304d18801880e2100307041d0000007082e82c283c2c4280e5100000b44181c4100402540004101c171880c030101307890400d00440c1c508000c10f50b40c10f00074000b43c10007604040c024000d41d0303c0800710303200850708a40f1a10301c0490040080e030300000810203a90744042c0741d40400e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 402636735 1250 402635485 402635503
    0x13060501050f030603011401060507020306070509103f050903120a0b03011e0f05010902161403160f0303050702010b09040209100905070201060501030501080c010c0219030c090c0809 80
    0x40c4859003000d0042c04220041c1d80300038022603041d5a0f441c0b012a0306c28040030038074040e180d2699041d0311920380c0d206052030010040c1180d0180300040c02900d1243d694080d08141c00b00e410f2518540304080403001400400701c400070407031b6203400b00c010116010411b041d1408010501001401103440d1030411540b01d10031030b03521490642540c8001109140baa8025070880440a000010a00c5e1013415494001442c0c50f0036800da180caa1802e84180c034901d00995014003021201103141ca4804942464880310109005010000b00c01c0c0b505024003050040d02c0f81230300e03d00b01070001039440380360500100901080c1103012070b20b401c010401c91072051007400364102c805460362450713458a400b0840c40c24030007440241500401e15001c0340b400341c070b03000701402034045800110b100c0303003800000f43c151441600080c08917405208001d40702e1703a01c5007420201a80591b5449050500741c10400d45440c0c0c035420181980360031010019107440c43c0da000e071901c00700607a0354407110b413503203c50191190002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 402637985 1250 402636735 402636737
    0x2030a030b09090a200409111e06160c050a0f0314010216020f040b040c0302210c03010e06010908160303032301030308151f09080f06010603152313060501 68
    0x30380f00040000c03600c0c42d0990317410b044244210610603061000509584010004507034082c0c030390f58155a5070506c06100404400600c01d8042c801066501041d05801400075440c120035800409800b070210f0700c255080549400b03880f80c030f04140c4500442d040c4440521040300c4940c0c0b0240000b4014406100747c424003845c410541d99444490713000c028002140751030040c1d10a80d50b0200c11101d98491041061209041e1000b6850b640c00f101e030044800720030000f0003060320748035041200b0028001e085a0550320681a01102c0f61211001240c222403590044a498410094000c0c04810522040c400f2a03100b6501402501c4501c0580c02e5030341004285406104001c000500009025108180d1f1040c5000c0000041c011400000340e0922407410b26103080c2c04103003c1c0c10300c1f0140e01520110241100760300a0071040c0c55180c0310b50340c03000f0510409080680d18021481402d4060f5041c100910b9250040006041444850300b43d614081c0022486000750905032603a000e850f0059500722441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 402639235 1250 402637985 402637993
    0x9060d06080c0a330908030a08150103090206070f06060f080303010f050f100e010509180603010e010e06160c0629040c02070b0702060403060e0706020c09060a051306080d02030a030b0909 82
    0x950b6500d204484e040712200b03010312601120104440401300090300f6000c03401d550380c5025080402e480d041c00306042040504050600c001d40e005601c80c0c404580d41154448843e503044070300c41c107000c0300800243c2c000c0304e0501e0f062500020754800006c092f6043c5ca480b1400140e4065440c02002000007044070303070b43d80000088600c11030309409640190420039040c10300030b241030fa42800241c44012a404003407030002c022000e0241c6410240300b180e14a007450b0008200d0039840b00d200e80d545d4000202007911200500003104100761103000c2d150206c0d9072007075003403000c0c80c0003c0040ba11191406030407001c4004010f004244d03440c06000ba00140302c035a8001e0302a05092007080c0f015039120705000d83c2c10020811000000a00038030509000b40f8408010f01121402d044000341403090b200d000307611407a040e10921042c1c1e0740e5000c014007215000c071601032007070381d2480500c00503004540c0820014000d10590401154021008140007440e03540c003000305d04448010800c2100c41a1150301c00c941c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 402640485 1250 402639235 402639299
    0x6010e1005010c060b031e0601050d0206041820030403030b101422060e011403010b0d02030a15090506030d0201051b0702030a15090213180809060d06080c0a 69
    0x4003c0041c4062103008070720109000803140042032400074040c64005581c1020300c000c036240101803040724050072040324989945441600040e6050186014481003500b4641c0c400c00e10800c50b91083c0d0039001220f441609410181c0c0101030142c0045401354046400c0100c0c005003032030582a902c0b405200340d141d0840703011040201c001241c1203490040c0792100d40c6034142c2194016599490001c0c0070343da883d4a920040040010304030360b450010341607483c000740010b003c0304411606451401c1c026010040e1a90b9440382c040300a80540055888081d084240208110501d1341145124590076401c856103124600301c00c03400ca80040b82c4030340880e030002008460301d42c0018014009580010100c80e8002c3e10354440c00300c0da000260030240320503600c80c0000d08500307100b0984070002115180800146d03d1026140780c480c034003003034024a07803c40010030144541da60000e4984451001c40d04010a0b5100c070b010701e03030342c141c00c0c0c1c1c22030b1140702c02d4000020105d02c83d1500710305a0081080a1038061 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 402641735 1250 402640485 402640487
    0x6040e01140703021308030c0a050c0a0635160f0f02062412030c010606030903020c0d0305042309060d12080c120a09020f0604050a18020c0604120206010e100501 71
    0x14200c1e00500c1d85c042c00c0e1840c00180540304101a04a44c0000c0c0d000d0b0000c8003007490071500e8040c0084c03025025001491042049540102c1008241500c802d581400d101300c2007103202c6020480b600c07010307801d80d9582c14028546001032031010030114a859403591002510001d582c4100f04600a40041e4048400a40c9160030001000c1b505001d400c00d100c8030407002400207030b41c0a00c48203c00740c40d5001040c09594a075090144074010013403820304000c09072817a00c00130b40311410408454002e8914854040805108004940c014003800d140d01d100e2142d84802c441000c3c0810501c580b09480401c0410100c0c60b000280b000c0307196120055040301e84040006440c1d0401c001c2c11a00244814419650b40e125181d59040c4145004100050b01961500c1007155110306000c1040c000c81040c4410b01580d140d5a0589041d00c0548030508500708142100740080d110381c01241d0f0701401900c0900040140100b100d40f031800507902501d6550780c903025190007110f022140c1c0390b01800401401c00582d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 402642985 1250 402641735 402641737
    0x506070f06140a1b120c111b01180815041104090b0105190b1c020c01060605030105090a0504020d11031626010501050a0519150806040e0114070302 65
    0x4544603100900c94100030307841d110110740c0c140507004103440d041010400d86640e58880c411048102c10a403004059608400030004040120b00e0002d49a03140070380c1e90254050503c24010420740004c845c2c541074040e035008048145101003a010542d001c025000f54041ca0b00701a050758a640d0051002a4204801c0900b014001d0300c2030391003014a40510070591a58013030201194011007464110b949804244240c1c000703170104803400348801c0107003031000000100403288a0200601094507810310030300354100034818044464038540c6403440c0090b860343c01c9805141203420440e1460050707566019100d00b59a401c45001354000c9180764128001400c0000c0709607101800b90403904039a0030b44075148041022904400440c00c140d4651a030b200c10003601c0c94010a1200d0001c1c080d9514220204148801c240501442018801070b018010307950403a40301c00404820700c01000501514001803c1c6000c01e4905600075420700c1e401c5001000c050280040003c50894001550703654580e0031802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 402644235 1250 402642985 402642997
    0xe0607030e0114030103050619020c1e0705210106120809100311031302031614091b03070509010905060f070f0c080f0312010602060108070306020c07091805010e12040506 75
    0x40c0092001480d000303183c250095406144548020612030518203002110910044440140d080c010888500300f004085400c61508401c0310201050b031000310402424a1196000141c1210358020403110103401e2250360810800400d008001c01902c500b88180d5081010b08003900200c010005040103041000180c03550080924000402d80d98548030306504c0d40c000d03541440108100b540d02d405614092020704c1414003040301002c8100d02d0844070b01410750b41d40e040d0368858248040050001e55a0414070300352485200c84680d42c0340340c03250b0b014007150402c05110703001400587c001b04d0103091940803910031010812525041805c590b545405103414400212036040d206040040c458600300105260144503c01441e15003000c00484d04d4005c00592182c021540081c00402ca55200840c820003900c3c1c001c00007617030345d40008044500e014001e030304c8501994940026140c00c1140102c03c01c0c0180c1c0f14500920003081c0c1103c1d004d55411444036007021644d01040704200503d00790004040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 402645485 1250 402644235 402644237
    0xd021f06050a0b0702010207060e0f0915060406020718060e0a02030a11030109020d1107120f050712050a02060702060f0105010e03070e101706010e0c0c0c120d0e010e0607030e01 78
    0x90080d0310750700400c860703191030f40c03020f010a0404140c1d0021981c042c41084041c003c1c6143c6800043c01c1c1030700060003102c440c0300641c061a003010105a5030342c2c62001000f070100d00500010340d03403075451400075503e00840c400c8940d100d00351100f41055044501403203089903900500050036441b00300410000f540041c24403640c0071341d03441016503205200c102841c02020480401600c0b21a58182c19050310507d101101a84008208100c00982d00c451407144a0b001031800342500030031440d003074948d0710441002624050350b40e4008016581e0183c02400d02034001d90030f0f40d241e80ca6018050380e0301d500690703152240d01c1004005104c1540320b80404200000001d0440300b01c1a5221307401c1c06035401c242d132100149010210107100c003004640e03004201e915060f009110a61600b41c140303800380c40c050101044080c0000b080300700240100001258030704010000c0300d5082441c0d901c26a104400d00781d4202145882c0500117940d03010f500481c2034400081c0c52949003c510b5901261101201e519043c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 402646735 1250 402645485 402645491
    0x302061315050715180218060102010c0912030507020d0f081e09030601030803060d060501121208070903300810050a0f090f152904050117041e06050402120d021f 71
    0x43d000d030ba07d40c0545010352110300000045414000002800e445210b036200c01401503500d001c02100403a4400400c0c100d401d4a804c81c0c82d8140b0b880055031160640768054240701410007a58184140f0b0002000c01a202403466002c442c5458803404045c050142d4244d4036070800001000441e4481300110703484440200340850340303880750351000116002a0041e001e40e20703103001810100129a03003e00f03410040350804c026140340400c80140000d0b8a40001800c00d050603001d514400c40b2201c481c0c2e502c9440d800144014003a031600107200c29000c1303a504107210724580700042c149c2451040701058a44111014000d507060100b0311000d8107e11105a000c86e60b03882402442c1c4001a01950250010f0300400000c4040d26102c0b45450142c100b0498040500300300401080e80c101e000281e103140640900861a80c460910b40313100c003610b1800c108684081d44119040000640c046071280e40708407a031090844418558a940380c0d0607085000244c3d0224601c00000c01c0d07481e1174910729900d901004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 402647985 1250 402646735 402646781
    0x11b0f20030a050106080f150a020703090f15080109111e090901060f0201050c311a0405150a0c0308180a14060604090206041802040302061315050715 66
    0x880d1902842c40d00c03d54643e50748100034002c8810502c4070a443c0480c03c0003d01c4002c120000d4003641d0b030006801c1c2484c0359400a06181058007030b20f6000003c2855100e40303014299982200c182c0c0e0303007050b0f120f00c001034086000480c1290103845051440201c0d0220740d428241c402c0010607141c10b500344582c0c50418244180ca80300c1d544c652400b4040c00b00340e9559185441d818070042e00356100640034a010705414460489003800a1540b000c2c0c030b0b0043c85c191420401040c2e01510384400907001090040310034501030040724080d200a108854059403840c0c0c42509028600f00c4901560301824000b45603c1d03110404640308280b82500446038170f0a40061404195001b454841104421a003801c00d000040c0300c0a10240520350340100d042d107040c00682074960001c0c1180c030550040c400f0318141c0402082811505505440203141e01401c3e441e514203042c5401484059284a05a14001c1c0c00c4903203a100c40c429001c0d101e005038054020750b00031042029260141c5005140d880c40391804540d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 402649235 1250 402647985 402647989
    0xf1e0e0307090902100f020a080304061e0203011404020f0922090506040b01120209040b090c060301080703020a1d06060714011803090f0e010e0604090818011b0f20 72
    0x1040c4000c189090b80014680d806105100e0118051106101400454a050341d20b0b1500422041d000c3c40c4d0096400c0e0b1f403645d071443d005c002800d40c0240403409880000100181d41640c0d80254141d511007244004426200401c03c02a4400c111172900000e800384078507000c40c01d00301d280399503113054004440807084c01d0b04400c00c1101c0c103010080e501680700c6400e02060100c2586040d02529008100d16003052868001c81d12210024000405076039542000420f0b0303100a100307041852100522117552542d58200d40d9a84901c0303400240d10079003036544001002c12072003401c5072121900090741d06040e52140104400c84e001200142c840944031440b5041207882071007940c43c03404a2106100c4e42442a08008102040d035400c2000010000e440c140006501c0880290459115000c80e600a03513542000c94098401c40314000c0c000400800c403000f000c102d040c44101411020faa0f8600c082004001d03001e606201190098a2041c010b508400400d44e143d410030580c190002c0030310380004110b40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 402650485 1250 402649235 402649243
    0x402250507120302060a06090e15190e0708061602100f09020604090e060105030f0a06050a231801050c04060f140f071707030509100e09040b0105040c0f1e0e03 70
    0x1003c07001604241c0c2004154032003840341c10058004484104800407164020340d0f5075031901400b00200384e0032040001e50304a00a5400c01081008a4090004480c9014030540d12502d50150741a54000d140025014843d19000d103c07002520394000c0150032010b40056009006001202c0c0f8a19222880303040541c840e600244000d20701c801c03001807014001041c2c0c0741401c006821061080e008241c0160028030300081002c2041d400c00400551600c030008030100600c1e40c0e500d085c1d48082d032400440c0b6402e0b841e9102c140705101203008915a41e5802007410300302d074011501501400d0f418802409202e200b0999800031107003a0404d01c08500d61040d1035002d940062096092402d00092400c003080450031816640c1425446281e0800c203030740d50098018060940308074080e4510209000c8510b101d144610301c8a040a0032030f10340746c100340c1030000380c80b03109000e100e00480c1130003175135040310744544429185424642da030042c138006022507000b40281038021010410500c1003441005075000c0c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 402651735 1250 402650485 402650519
    0xb1c0804151e02010509030f0d0603140109031701080a0b070e0a080c0f04051524030f0609090c130e0304080f06010e01170d20060405010902030c0402250507 69
    0x10325100b6401d4144800b588580d10038035a00d40031039040606001e001030000047d0350041c40c1d480c101070349803905040d594004208641c4040c0ca0040c04840000d8480d41c19402118040c0c000c1c0e07509421101030a03026944298284a405900c0c1d00412076040407588580610f03403c1041890240052104100014018040340c2c020b03e4054104802005e43c919224400c080200b070259402d202914041c5030360f0412462a04900c0d01540f82c1c214a2001985089009400700150140b03035503c90a0045410b0603c0700d00f2030344c05004014820105640400000f000c01d090b0000803c5200401c00c1d070021680070f072007600111226403005100c085888002800070210142480c0d000b019950301d800700c0c0c40800801a84200c29046841c05002d1400c030b40461025410125414421180764000e2080c400c90021000c4030f603510301900c401e0008004064021409050085040301c54004104c8200800c0707107c0c0c56050803682c5144230400e5164501ca60000480f24005c609669513143c1c1c540c80a4012074a10b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 402652985 1250 402651735 402651737
    0x1b210222090e0c09220506040b0a050112080316031b050711010302090a0605070507210605010e1501081e0130022808030c0304080c040b1c080415 64
    0x5030401d001c0d1403480d00c144004004884014041440f49a0128080810180040a00d400107250611242d00302c1c4d0203090406a1101c04c4860f24582801e26000c504010f0f248070b402c40d82031900001e68881c030400c01000c8160400401440e50f11001480010100c01d03032004400d260710384005802e20318444002508012258450300c3d5201e00030316000c00e491155082d80da0505106004103051500c038000741106465032802c10a542c1c824904100f468580076520403e407d424030310440d01e401412010001a180c80350b2000d0100da40c0300d441000c4111002c946030201c0c90390301083da00c6c4540c842c0d2121500400107510005c0e00c0004403030142e401c0390f026000b0510000d40c102000d100c440d0341040c44d4ac41246906c061001c000e2039903002540f40c0030a0300b1070340301807403c501080700e6804600b0b003684002c110301012a41d440c20706c4c058454480d0081d00c104401400b901101e80c01604082c003440c40c1d2008010b10f0002c4190390b012170f030685035891a50a8840b52028400481d01581e5982412011045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 402654235 1250 402652985 402653047
    0x5010509030c010f060e13061506050904050a09150903120c03020304020102060c090a03082208070812090609010f11030705011b17070f120203040606091b2102 70
    0x104002e01d6003951801118070601c1894902c2c10054822180c00d13183e008400c83e044917441c0701982c100341014180351012140f5818502000240741c9401100070b00001d041968140616912943e8036021901007440203494050b10f40140056110b43c0d6208000700c40c881e0401031564100003880b40f00301c0c0c03a0041641c0100e030340042440191760b0100407440d4013100904182d890507038004c3c042000d110315407000614551001c1400000d00011410f1504450217031416040301c50341d144141641d4030700520030402c240c0101821240d4030401c01040303880c145400388c107103451300f0100801140c05034811210903007000078075001c01380d005800b40300901800f800b81b070001c0350118113080c44030081e48180e0240d005004c032610140710810503d912560744286141882d4503420041d040995a09120343d0341038a1140c4000108810415607a02c102c0035180e48500400c54070100d0320058805c558034905000208058040070400d2440c030090041c40e6810590700581407040b4a4030b004504e0582d0940301c460190 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 402655485 1250 402654235 402654247
    0x506010f0f020a0c09021b06040812061f02070e0112051b030313030f1101030e0607030b031204030b09011a0d1104060b041202100207061706040624020111070b01060c0f0501050903 79
    0x1047d40105e4034603c4850b000c0c210038101b0b80d4440740c461261801c00840d0a0746140026815507605c05d0321842c5250104080c0900202c00c1c9000b03445800d01c0c02025200854180003059460240102c4814140c0c80700040c43c1c016070b000e40c4004440b02e04007859078180700401c01d101e03013a003000b2071340c2000b580f1504028081d0b500d0740c0340c20000b00c0194030100d07041500c0c000700241c0c00c43c40001d0700c2e80c21800740d09001848840b04e001083c00c0000000960700304100c001400820131580106861003000688006c11580d0000c80c45160200711154241c0c1d84280b40343d806001140c030440036072428500c01070000030b0250380c4410119071900070f90300c910140140c14246034194202292540301c110000e2002e0b0100718107000d00501151400c45c01c100080b43ca80d40000d10f0f9844c0c0741e00100c003415030340c0206480c9900307001e000e10703180d907580320340d40019400d0800c81d07226400002d0980e502903900c44103a4105070300b03141c800c541c210009581503842002065480d4003140c0c2c20b210b0703c1e004602c07200107160350304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 402656735 1250 402655485 402655507
    0x109060c08091c11010302030402090c0d0e03031e0f040305070305030a150306020a030b040509060a0b010512090c0a080601030314030c070c0b0d180b060108090f07080304050a090506010f0f020a0c0902 88
    0x313044021081c141401001000016904c0010150384200c0f0140403944070322100354004000d0004281210103440004180203030701d40e411a14012a8088200c1c10410ba45c840000340c0040350300b43c80040200e8428000400040e00520141d40e001c250b5000020b0b031084070a03100c40c0038004d5640291030300b40e40050081150355040c0184420418252330500003820203401141c1d840702e0041104460a9480b805400560321a01c1100c16620350040155041d091031142141c0b980c50040f4290f11840c1d000c0e40004041d840410801c0c101c0350582c5900510700800e02a03110244d00c01400300b2040c40041108600040d100d00506001d012020120740d00c030240c25003001d08035194807560041e07000143d003607080005d40c041c0c01154004001c1c6401e080ba910b03071743d440038a0080ba002c0e25886601801c1c001040c41c50001000c0c000300d5078100c0381c140481d9511400301c0201d4905540c003500180303580c100e8001490045014540e0350078584100d0344030101d551150201d4260341d8012001850700011980b01305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 402657985 1250 402656735 402656753
    0xf07031b06020d0605190303080c0706060f080c15160f02040903020f10060b03011211120a0b0f0403020a030c150216020307060203040b0301090b130501030f0c090b0109060c08091c 79
    0xd803000f07031000036100303925810355403030a9402d02c030040400c51001c000924400d042c002faa2a090703408a0184445500c940c210071026a144c000c9104904ca28440c120a0b80b81400a91161940b1000e01070314105a0120305c1800070500719060394402c91600d009170058449104140016010380d0145c41d1128000c8002820540b880d031248005904100c010300000340b152088a0454a0103405d038000e040d01e5241510054044650240c0d0091012004110701c40000c07810110141c030a6000300003560307079191418980c5100b610081c005902c082051380000f400744035528038090180d0301c0ba424000312042c81d107090368441c011060350595900c1d00c10046040800444002d040c10380061070515003404868030759400144104500141c54014401c025254505680d9805907800e200744a19038581c02e142d9000010120111400200d0716800a00103265129285204405944800c5e000f8503028040324010300c0c00405803021041080421901d0351054048124455001c19034104c900c050704045840c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 402659235 1250 402657985 402657989
    0x180f050108070501023a080906131a041403030a0c080606030c0901050a1202030403030b1311030106110c09040c03020102120a1b030c05011a0f0303040503030f07031b06020d06 77
    0x607644080301c1400f043e038020652040802c45c1c88000d49a1400001d888101100d41c695807810303005c1500018520541d008240300d00c00c903030007011a215030702c840700054900c60354000054040b01404000c80350300c4a00181030758015005d05030088420040041c545e041d0390060303807140c0031503548010307094000e5008204294000700481790241035140c507001000780c5200340483c1c0341c1000760000351994864020030b810b00061018140840d22441c2500d405001440c110350503130f00c01c2a401c00d00f1002280d15008030000c0d8807020707040c641940d2034000240c95582c2e13020420120f901800c0c04070201a05d400340a81e100310b002d0f420746041e4030f2840c00003a00b40081e52802c224800342c104419505981c20110700c86502c802c00705018401a1141022a903119030382e0001001c2c3d508003100303140c2039070348400c1510541c0710403100001c0300301119081591768455031091503003642060094500c0252408003610302d0a020b4200f40b1070044604080300c100d0808201e007114141d5011034800246171542c0300e0540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 402660485 1250 402659235 402659249
    0x340503010e0703020d0813030602091507050d0e060d0f0506150406140a03110a0c060f0b0d111215090d14160503041e080c01030c1704030306180f0501 66
    0x490307003002019482d1038540d180406800381c0380c042405401c003c0d000049942e07001c0c150070354001d010707128607041c0081e500c00c03c1550302c210310140c210000a08070500f110a410382c040001c00a48841800a031203203110b800003aa4803600034002d084041c115030241055140d6050b8002401e4a8460b08101d15000d0045103051404024001800b08a400c20040c01c481c1024111107a00c5542d0402e0440140080810780721401d84041041c40301c0541011003201002d12440062102d02c0030107140c041140c400810381a880f01000040340b0100705051003034811902d010704004c0d42d911554038410f181408900172950628200002c120030f40350184040c644206040c60800d82c0342c2e40ca0241c0d03182e01e000d50703c0c405080074491455041000070170800c40300100300c01015184400701132480050311200074401c45203603005640e6400442d620038440c0b1072401d46540c890f150f000342e081001003500d22000b40300300c0915540d01c1022500b00c0750500d84007008010010301160f100402e0b01290240e84044e8440300b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 402661735 1250 402660485 402660491
    0x303060812030606040e040203160305060f0c03071202090f09070207030b130c060806040b0a1d10151b05060c0306120c0f0d0f021203190c0c06030c0234050301 70
    0xd196840c03000301c0b0100c03a06c561041540703882c0da0000030f040c10403281e00c0ca151011090320000821401094080c03007505c49200d0504070b0340e02c444805c1218801142d50900040300b007440c0002c20101a8040e00c01da00d0003038245001540c10307030085580014140c40c02d81c0564810301007007040000411038643d01a050161b40b803000e48042d0350702c0020420700d00a460520004100055282d01c4682c480c280d0944000d01503a8059a01c00e4840301c000919091010001740f84d000140c0c0a2860440180440721442e5042c0f2070041464811643c03100001c4071881c42000c40d080c5400410380801203940120350310b8031202d590342005001c1019141d124200d074101600601e0f0100c1e215502d03800c1c2224100310946201589030604e1600c00c180202200001358030242c1d030307005045d404034008080c11205141d0101d211405008240c2521504108100100181c0d18201c003480094481e80026280d48080c0c0100c400b8101e01c160445051340010001c40300368086c5081508048070400c41e103400512043d0020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 402662985 1250 402661735 402661741
    0x303090509130503160f02090c0316020c03070605090307031a10140d020103050a0e01020c0303101d0103150f051302040b0f18150607060b03010b0907120b0301060b07030306081203 79
    0x180d102e000c5c52070803c010b19020b00720344007441118a148450a036004100c1d0485251070b5000d0300554105481d40b099084a40319080522070001a1440804600400810314646418001c84150703009100c195058042c1100010010744d40c0072100c0402003c40000c1000381c50080c0c0c10181e1440340394800031450f245040c0b5540151a508065040c04c1c1d020b18010415603544164a000740446030742c1c0340100e6200080780b40d05504040003440c043c0107501d00c107117051541c0c0c010b0480c140c1ea0840301c041c0c0708880c2d14010000500c4d4031002d081c605d2412400410420550f0b00801e00300c420445103003080054046644003140b410780f2418100e4903084802e41403202480c40030074000840440303941d103c140c01d80045810440030745054880701800800060381c45080f40b9000001e40504004203001c3c9d8240090a6203914200701050f11805140d518664110044155a00980814222190107560391100401e6582014000380044c501030b882c04100c0501d030107060b91400c526240c0070300b140c006c14414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 402664235 1250 402662985 402662993
    0x310612110327030706150e010807181409030705100213060c050114100f0602070b09130b06030106020a0b0a1122050604090905010f051017030f04030309050913 70
    0x140d03900a01c001c2c511502d403548050803501001c00041c80356450380710100e014800c0000a0300620703618080780b03c0307659a40d60303034600a0725617620a00603524141c10400c0203105012800c00b1800300345007a07070008200390000d044414507514003580c0001182c0c000160400034000b0410542c0000c00e0004400c52074028030b6004440144840d00402003000aa80d1a400070701c402500520501c0001d06940c645504000044000d02c24140c1f2840b03514602c92a03000072500c0c000704401088400405491b45088520000c01c101303102c90002841d2525502e8040e41501d8551502950203802e568000313140c045128201104507003001041e04e131140b03041c04081c2c00e5100704941510244001c691036039070100034550301c0380c2203001c468100075002400420300181d1801d40703030030030512240140000c000103107010804405490003220f43c040c00d81458031081084d04c9884019540d92420b04050300d0070000090450700326503200d6882540044c03c045070a11080c5081c2d071240d83c108125a005c5c0102c170a6581d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 402665485 1250 402664235 402664237
    0x1903080c0a030f0203151302180f061605030306030f0619020309030f0304050d0e062713090b060a150f050a050403020d050a03180509060631061211 65
    0x5001003816001c52810301003070081d0000207401d81580b000b903403640303850441c0c01c00300d4518500c83d9110340101412540d001742d49100b19408203d00c0c0c4404540c8130084014410f01c409030041e060340141041200ca120314014020303020586102d03001440d546c1c2084000c041c0b501006002c00c103c01d412102c00d001800c2000d41c507141905000140150322a5100104d80781907000d101403001c41c01d4000030404c401c1203c00710300c011540456803109001c0c486400c0a010745401001070340302c0c07980d0a42144500f046500b007000d1680200040110b40c2900034054044142c5114050480da0700701614280320581c903203008210044d000c0441209079000c44c403103004002506240d440303014040c2c0091170f81c1e8046d00c1403013220701031600940601d64030316940c03404664848101d01c050b000501e8003500b50b51100b4040100c40d044540c0200076106540f2440d00300f0400e544280e020452003140801072031001080c540050581500441c00d01103138918000010f842640300d9040480d0080c81e01107280c82d9445160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 402666735 1250 402665485 402665491
    0x22b0203091017010b09041407120915021c0605010507150c09030b0f0405010b0f0109090f0204030f0507091a18060a0302062b0b03120a141902190308 66
    0x10b070303a49601085001c05a8450449081c0ca5480340a000c0000c103910300080018580c210341924200000140000e008112105c155081e00006003861071541c890f11250f00328503402c0707000b56100181031174014001c4040303038042c8551018040079112002a2503005114003c0104000e080c13aa14110003170341e40c48040504640c4140b80e6645d22212908070031f106d41c4589018543c440c10400003420115244000072008546c1201d0b258240324441c0000d04010405002e60041030312a003100700c0c1811804005800a50701e80000c2c0d56003840b000010400384170741d50500500540142c07046c24144209182a10504640d5003c00043d2698000c41b5854a02c94807520342c0d03a20f0300405068032408002000442c00340d0001c0c1d0720500119002e01d5660b2160503500100c41c40c4003a004215404502040584c0e4486409950540208520305400a0319038002c00e01140185441c10a25610f1040d105030340c3c008109180310700e244140e1002086030100818601d0110469003550300c032503070b0f6070000c00c132420003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 402667985 1250 402666735 402666739
    0xf031a0303040e09010204050d0f1401110a21110406080a09030e0f181005100c0f080f0705030f21090c2403040525030510020304020f060a022b020309 66
    0x1180c00140074113020750564001d40001003050280c6040750034411400d6218490507641401900e90030950044140300b6072200040750f000060070407402d4601540c8118009000214032002c1090000e00264613200303c040041c1d280c4001c0f46c4070741c288070008191400092801e02828902588400480e4000d900d40118020403260003210304040c0300031078102c1c1c00c1c0c618600404404001802038200700f05282c0700540e00c05403040340503080e04440486d1000f4031603801601d90b00c1052002c80100d07001d4002040d03402500780c0003602d40001a51b50034a9944141030203000c0d40e002180c40c14537002081d110110303610800c0c40c05280782c2000715000e6194070784007020b540b00c0c440d00311500901c01071400b59180300e014050b140c1600ea103040e0a1203521004981841d4038031060408040c4048036103100004103894000c1d00030034014044d0303a100c0340203500241c403da0f440040800541801e41e142c8008280341d04e07543d4085c15008035045001c2103201815494907104109600c030803c0100c0d8004141c4c0c59401d0300b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 402669235 1250 402667985 402668009
    0xd020d09140409050604060524060304020d03030b030303041a0c04230a0f18060b031003060504030507080c1506030102090d0305090a090c02150f01060e10110105070f031a030304 78
    0x50032000400910f403d8100500500407071080009000103030f8403280c800d00c2c0f1501c080302d500f184030a0b00308010521140d060392229090000c2805410b142c007080030510721900300003840c1d60b80000001d103180c000311000c54080d403118056000001302c80b22095004414024003070b003040e06050a94080c2d848002c0f014602007000c0d03101c1401544c0d440d07020801071a41d00c0e5041c1c7d18640340c5110441c11140c4119060125040c500c0000e42006e42034220b0b84154183d210f00701c4894155070b2040f01a29000d8409d60402c442446642c012546020091000121800051044110b400081c00b80d0040040083d440380e44180098806621071030b6100c980306600d89409aa80d10144001030032440d241c0d0040c0480ea4a052820030f4815000159006072031213072603800401c4e036a480b28403803486a003409800d0005400c0c0074006440e080c2036400d1243d0029034185807980c10401da42d601e086031011100d070000519495000040703e501840780003849200c0d80080400903d020002c01e540303200d580b04a00512203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 402670485 1250 402669235 402669269
    0x8010b07031713020102070b040303080117070b0f120609192c1f0216020105070305072117010803040e092a040506030f06040201050d06080106030f050d020d09 70
    0x2200d880500540c0400003010b10207401c0c40070305140344003d1140201d005d0310502401003121800b000035a0b08691349655508807070b81c02c052980710120403100c0901b04900c1812404282c0c2200704018003440d484248a86465045804a20450590103405503025460440607c0710307c1048030200314080110880c0860b04c0315900d405d4127814600e29190a00c02550390101409422020404000b00342e0589207440400c81666103400491141c2089540044d403007210758030065000b14068111a0f020f82001c5040040a407108a134840074400b1700420100250040c5144a41186076081c213003a40d003038158a6581000d405682ea032140c1c0c080c01040c140c00d180003905495040040154450081170b0f040313115440d440c041c0d00d4100c60416068400c07801c28002405c5130600058078201d10b90500c000301100e80b03868005450650042e221000c046484d14404520b10200340110002180b0920300b0b03842908543c2070150501103040b403180e00319082844014181e43d800140481038550142d50312000c88 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 402671735 1250 402670485 402670487
    0x302120d0218040228210c110d020a060f0b040504050105090d020111180d08040b0301080706110c091f03140118170306030a14030a110c2206050406120c0f0608010b0703 74
    0x44042042072400c442c0c04076590401c6c20a40c1c00c82c8009000c1512210021120180080c0d11084602c00140040c0c2c01040c0302408a03c480d000b501c00c640c88080c00150a15a01001c03401b078640403901039425a440f01c09003d5a0746d010888889640d107075200070440001081c0da0811039101d200c01811301c807e0403680d810603e60703944601c00500f0b91f00041c041d9683d0750311003612495420911400225024510000800d180a801030f000078000c007002808018450400700f040e4420040c12207803c1d102e081c0f0090301443c0c103a100e4080914011030b03100003842d028054003030035500800d128030390320010249403e0008403c40c1e2520030115401c00d0840d107030f81d60f40c40424078219004902920301c09452a202980ca1400700040c644520103a942600e8043d04225045e40d515601101c150090b1f0401e41c500040301240b820760a400d403a40c0340110700035035100300040544016030801c140b00841e0700c0200c000c009001c11044000e210400030983c1c2a45004409020b40c0414407400588440020b1050101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 402672985 1250 402671735 402671747
    0x1e050712050f180406050d0c090b0303040b1207030e1905011808030601080702030c07030c061205070203041202030f010515090f04020a03031b0203010c080a060b030c03040305070302120d0218040228 87
    0x2d808060441c68118000d030906040c0c0c20a03070700c05c202d05548ad01c20400840d0401000f11010307610000707452840c158000400c200002c500078112010540e030b0b003201c4122007500740403244800c002820424200c0703505060403400c443c121107440403c991020350b400001520b000c20b81e940305809080c0316009645012041c0c0c114800d60f07440c0115809401d0300441041694807111060724142c2c6d0740e950b0b2521105082c00121800cd4981c2405030340203210800003115100200012244041c098603020f41103d44180e003510b80955007407040300c001c83c15544803410720b52074450f0302c400040d02c0300010382425004240540c031a8003029040100764501140703100d8001d5007042503d81c0c043c0c0204102c01120600401240b0305884d002112401c003400080c00d0301c0d0701070a80740504180c4c24440e00e1502c8503035042c0d5042c0d203c92012000d50048111640f020020304001e060030030351000703016030780358159032003010030040d0254502d208074030500c030201c0944050010300e20203800e07103854005415510002960340c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 402674235 1250 402672985 402672989
    0x8120c3007051e01090b04020411130b090f180c030c0c190209070203091503060102070803030a0606090f03050c280b071103010e100c1e050712050f180406 68
    0x826001451004010700001c0700d03c40403800c20404081102082056070aa821600000d00350f610074602080c09403600764488220020040700c4546000c1c0070a00c00e03070068083e54801000b83c000801c04440c541005841c50341192000c42d5442d0b100241c0071803180740390303901030900c102e1100f01200003204403410b002242c910005031811248403020f88044420303980d5a41508074029814000410f1903c0d0000060301c0c89610002c01c030400c1d20000c14900200380e000100f405046119481c00040c1c010703024030082d0300580244501181303442c1410405880348801d51300c400710a402c40801003001c42d90104040540307410880d5000c07554003d0303641030714002070501c0c05841c0004058000045000101d8020404248255a000c0744140712030101400c07942074030b000e1070047c0c12801104900c0ba40c00e6211044075120303030a041d0608040c11300d116402000307040c15500400c01c001030100500184e14400342c010b9840d464514613000c0c1c44402c00d641c600804031426030441c08440308a0f41760351a81c1003440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 402675485 1250 402674235 402674323
    0x901030215130902160501060915171014150102030f0f1e0a0e01030b190308031e01030305030106081014060f0409090b16080c090f010201140a0608120c 67
    0x1454004c005c0c40d00d04181049901211030750300c2c105001910071401e0094003140006c05420b02c0e0603520f05045401180c030701d6607501400e805021214940c500b01403240d01c40741e20f50b0b5104240ca5160a080124203e4030244d101419580207101005500400c6400c98101c071007009a4162200c030032b00c0b04d0504242e00350140b170000c8200450703403d0f03140c0e921510300145a10b01b45da00380845400c24050140c00d01c0c4810601420390404003047c000b01d010038000710f030840c52020560610b160403100b02e11070500c0a07002140014800801013001c03540c8506136540014581c40e01303410140c035060440d8210804002e83c98040e05000c64135020181d004000d0b0380080079172180910410019280003100460100c0d02e24480c08140c0c420918024815403100f882860040401851300c04140c00700800c40503290513060466480304aa488902c034003a142d54058840c040340400c0141c03d10503c01d0a1540d1403220320003030441440080e10840300024150176400d504010895603081518501058000441581d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 402676735 1250 402675485 402675487
    0x16030e03010f0c090b07080d1113121703091e0106030507080a0201021212070c020409290a0908070813080601030f051b0906040b0619031a0901030215130902 69
    0x105020200f50442031034014035940b600c08441d00c6a21040042c0076400010b0011324050242c4428810306902c0751828610b5080300c9418011581c18801210b00301d03030050340040da010b510517410014088514011516040c427001d00b1441c1c0a01c03144c0d03075840d4954210103205284840211401c0b820740c8040b01868001042c0c1d5400c41e00e6006280c2e4032116034104078018070541e840070488a00311030540d11090b5404c111080300d9120312000300c40c3d2410400d0700b030741d026554404042c0001c001c110002100d00221600d49800c41b00d69186111406000f444490964100508080000e400701c1c200e4040950201c651602c6001c2ca00a4030810b25142d00505954882c25001005001c5000441c06016204904885031300d0400c829800d0841c00c0d4110b040c2d04440068041a40b130314060f0044408100082d000030f060002c0d51721002c4211041c10100400710303580d100304030003105038644101c1c40c905055032200040d526590204818200b10122003096600108041d0030181641007400020100c1080035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 402677985 1250 402676735 402676751
    0x180605042406080d0203030f07110709180311070b040306050c0403390b0306220203100512010e0303070c0c0f0e07120905071820190e030316030e0301 66
    0x40001080c0740e01616403c3d00c03c3d165401c0c001440041100c1c45003000c0001d400705522001019203000c1400300443c040c03030159240202e0540300ca84920011171540b00391aa003440c1d01c900307024111005010884a240c1c01500c0180011100d40d021202180da0000700000c0c6543d1f4285000f000303024603000102424001440102400000e45c0914500444018000525031160410740080000780c822107002400500005a8919002014030070404442c40c0720203000c298070f01c00320100d90003121503c85403c0158028130450400481e003015142d800d03c020043c1840e004081607407030000910030810851b040320640300308403400c0e100100030300c06613000000341c0e6114500d0041480c41103420900007509100c1a80814500c4d018030525550081b003c4c11080b810012184020888040b060304001d403501340764a0002a10b00d4411030950b0070030740035611214403180030100c010350390403d20100078101c1c00c6c65020740d6001c0b042320300c103001c4181021800a42403400b6a19021440300f0980e05511745000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 402679235 1250 402677985 402678053
    0x30405462306031e090d1e0c051615050c06130c03060606020102031501020c010f050f091507031e051c060e13030f0f05040b13080307030e04050a18060504 68
    0x1052041c0501013119041c1c1d69549011380350386846d1490320400048803092066a40d1418000d002d4140340b8510b8660106040c030f40b40c4618003180c0300c48480305250b04c20001c2003003920b5150b1384000500949085890115900c41195030703068041c003450b08002e60340c00c0346402c1000242041d0300441c2d10090a009183d51910017a00035007049444182c444004034008043e588081001c07071481e81c058480514140d40b141040f44c45802402181203008402c22100410703540700d691210a00145a46e03103540d40341c80e440c000b45000c104002e10030300e10036802c40c09040c5941100554402003034004400d05410f2074030005c980540001d034002140c07545000240003405070412080d54003d4000d844601e1500703940c4070102d50502310380e4407200c001a418071080c09031030340c40300041c40d200c040c3d0402a808540c640340d4003415588404000c40c003044400e1080349141c141406159884410740e5400c00035508a201240040000c2090003090590f55800241c20815044407003480700403113009041e5441100b000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 402680485 1250 402679235 402679261
    0xf0105010e060609100305040503040503011e06090506030a031b021c020f0102070501140304050a0b0906010e0c1602093106061505090d030203040546230603 69
    0x80c0c0016115620700080060900303408941080c1000f0f00000040803452504030000e110240040300c160204110000342c41c1c0c3e0900822700003007240c2c90300d07030142e01d4604400350845040740c2c002d20390702c2d08080c1042003aa90200382d8a80b91501030600083d0451040c4030a0990021504001c0d8071042c1c240c0a000031001040320402901d109844074600035849400680c2c0e22940381c45040d00080380300c45c110b004484090003840d0098803d5003140d01c000410343c0c1e20458008200e841c000d0b6548100010071245007108806034120203a80f4002e4038101a40304020038034922200d01900460141c004540c1a003c00d15030480650034103049440c1100806002811340140c18105949003800e2010200303e074444214031042211490300c5644c50a2010814402000d40c01c0c6415400c0d80418440016140c4134180b040605902208500c0c0711a01d5164142010400c05030400c2c585c00d108003010440105100442d1007620800c0100c0005200101c03205494400014145500140003105101c00032807030f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 402681735 1250 402680485 402680489
    0x2240f070f170a1b03152603180108150a2601050a022d0403020d0807050a0302070501090e040510050a0204090e0a0203061305030306210f1f09110f03010603050f010501 74
    0x704e08110f100076000c00403415111400c2c030700b20842c4906a41005620510b0302e001030444401942051040405000c3c0f50954110000e004140d1030143c603600707100d40e030054034540e2019004465403500000403001c03a020741d00f5030044800036404600140e0401e03903801004c0c1d84030903186e002441545031000849019400145010032095004617050207210b5090f801281070200342d500c00350400d803031a000c02031650210319007511844000c00002e00441c406112000c03075203010350000c003d03da16150006001c041180c0c0461800300314001488001400403408041d0b82c8011200410143c0341d540314100240b00ea80c0c0401d866526020210300700d8400410340c1d4460600032410b43c1c00d690707624114241490506600109950410000281e15103007090403001c0820708140200310040f600e203481c514001c03500341e141d0410351003200301c2c1560008030a1071600c074108541d4144030030744255540d005511095041c40e0b00c500450341e20301641c2d480c01d50104c0c004681040c2203820790400c8041040c0209070038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 402682985 1250 402681735 402681761
    0x4050c0301110a0e060d0b030a060203090c09160f09080a06060f08210c210c10020a0c0311030708040e0109050603010c0509190801020a02240f070f170a 67
    0x45500202d112000c01e050b039140c0c2c4060b80b5041d004415001c00c1040c40d602c0000400e2242e543c0b40496411f54a007040340c0d204a61090600581e02d0030020010307403510070b43c40203142c41415440f08102d40c1c1c84620715442c40b1990346007454150b0710204541510b02640540100489101d1007031a4824045030350032081c11034102880d484031494a4104007500e40e500c60211410084188c10b0600d00d03400214010218a500601501d055003420b04180300c10340d0400300314803002c0b9000300e04130340c03101c0050007095415910401c00310716148410708054500f050450003c1c0c244400f8014200989038140308880059038440c403100e0b034031034681c030b036146918000b030061031021460700c40010702609051044080d080426103605040907000b1082100c0c900403050001c110888040d0300041c0090300340041c02c58802c26401a111800b1054103100004082a183c540d090541006010700c10350f070243d09a40200c014034024000d6440ac80d003e5401d900d201c0e000443c1200e083c41000140c94541d44000100914 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 402684235 1250 402682985 402682991
    0x718121e023c0d2301050705040611010b2b080a030203040507080a020310020a030e0106080d0f090b0a140714010501030c0e0405150a06050d060203060f060a0504030314040e04050c0301 81
    0xc0c0b2601030707070603088071000b450300301403030003005808a141c1010a020407150107a030815000c110022090030b60302c0549605011640200d01030022540100c401c018041c00d05000308200030300c400c00900c040c12910700045000c020008003510f0000d04011040c1e1254006c0c03403665a65403e008018000c0d441140c050703c3ca8041c010000c540c0303860104030101940d0700103008254102e8040c1c1000025403180381101e043c1669800c0f440c201e9942800350400911041c00940b03006441c285014082103100003580b0100018402c0510170b580d100700039030792121003500d024442d080c504403003400c0d540320b6410013a04103029040158002401500002d041c3d078850182d1010aa90f141c08090440d001950020000e8200361304003540340001502e0746500c60030196000c10010399072008181003405405c8203603900b0750004204031541c108ac20031854032880c01d48220307181c8030303060400902a0240f4003009040101c0c0a21801140f1034050659010f17042540090205052620b0b004e6500e089001c50103000303500b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 402685485 1250 402684235 402684319
    0x1c1401080601051f030b04060509250c02031f060302090c03061f020303040f0c18020d05060d0b0a1113060509040b0a0f171606080718121e02 62
    0x2c0c200d030044040c00c130301e0908613410718150006a01600300101c00b1508a541d851002405942d01c00b645401882c030b0760325400850544074985100703155640f01c424240702d203c49110b801600c00041c0c04200309030f006100321044034040e000b200a00000c0c1e0010f940160b20f8014040420703410070080d80940800c0b101000000d04a0403040156401100f404026070018000500422041100142c0440c49403405080d11303038550400c4500c4400301c16862421036808280b0b0030100c0454428190007030317011140c0e03041c00102d41c0e81c0c06000220003403100e895191620140b24240100000f5038903050304004110f0452520740e00700400075017186808922490406e10560418104416500b098030802400d880a4034208881402c1a9495140400c1540300d449542854202a000c000025201c660b1740c400c0242407114004000d071b411420323503461200314400100500525180781007251036004c074404200300e4406415042d0700c011071784042c2d00300c0c008050440404070a5990803075481c0c4076850040141c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 402686735 1250 402685485 402685489
    0x102190315050109030b340e09010e0403120b04020d02030906100f120203190507050315070914030309030a050d110a0b01050f0604090c080402010305071707051c140108060105 77
    0x300b84161800300d66040b42c18804505818507082c2d1200b903030b08104250351a000c801c110300c5402c4648010170203020368420b22007582e005250090440f0100c0e1100c130395505204030606005070103403008040c042007200b1040089070700c0d00402980c060042046480d00c098581183c0030354000c2341d441c2e600d0702500d400600c00000f09040203040d503a484c0e80c070107407040c10081003442d2401d101c00280c0c0e1510501c0164400040300c4003054240c42d1240000e0300405180c82c003414900320b45850343c02c001000e10b07010000f6031135000001c2e100b122640c500c241491900c141c08a07043d031007074001c526014014100d0b00c80500000150045030015255140141c0164817003000703440b03100c0d0080c000e01c1e602c00e00340100010300d0100400d0183c42e1000308400d00d0507542c0c6641104560f07240400b0008545040c082001359038052003007540c801c020781002e08501d20207076818200100010850020700c1000304103229214441c4100700c1140114ac01c00700002e1103520038108075050309125440d0f00d0320419001203039034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 402687985 1250 402686735 402686771
    0x60906070e03010c0f141b07030201030c0206220f0204050a0c09050d0503030a150b0a02010608100203130f03050f04121203150303080a021912050f090304060315050301021903 77
    0x40130b443d9034802c091548808221010104454000b080000034814081000c50402414200c006600d0060080700c1c95440007605070b0360882c41c031109540000c42000040c01e042813000300481d42c03001415158078282d01d0481501001031101035002490601000f8404010f6840352842c20381c5500c03825080c5a40301c0c1040000390a5110080075a0800e01c00324504401c11f4002c10500c0228610311551103448082c4120640c0181e9080d0300145c0d12403004102400c428032814880070030a00c4190301d1031816849502c0788003c01c41d80180b04030841d00fa6402418400c1d000c1c0d0701503a00c0400034039a91652000d1900c10009051400d0761465940010300750058060b104450a210700b000507141c1003451501c00303541ea10340c014006034117035400304400e0b00921000020600e42c108951275080030325461241407011114010002050610b00e40705114410b5000001d440031600b440c078000c00e164010386206108007101d98000da80540c008285c20528500c0c110162400481568040040301c1e60607900c4104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 402689235 1250 402687985 402688001
    0x30c05011a0d030e041803051918152c0916270e04060212160e06131203020a020909060105010e1509030a0309150302040b1603020a05060906070e0301 66
    0x840301400030781c1000240038140300e03000840010b00004040105040c07120565145910440009000040e101c0d5400ea0500191422803840d01d82104d900c00080c09007800001240505000040c8010b4201c050b5445000000341c54201c030029070551590f01e0049854901d001c0c043d01b4407554601c4001000d070b0648540c2cee030310b84103111350b03601c5103884003480e00d00c001d400e102d4940341422805042c0070480c3c42c048886240074501c00d803030050760b68241c1e103600496468060302c4543c607070400c00d03a451703401703a1720000102c0400d50444420380d482416010b4003501c210103030b00122616203103150a000781900031800340c1c034860003607441c0a85691025080c0707440c1d80090140034041908007035006864145071841c1500345140ea42000d1401d610480000e1602200c101c084000891000303041c841c420342e444000304000801e0a040d81098100328042d104d50089061800326113004240040500d442001031907407140d001340c04c1d80d9050034414003490304c2c0ea03412034212010503240b080685041c1070500c03550720 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 402690485 1250 402689235 402689239
    0x12010509060610091d060108060409030f03020904060806160e010206100311060c030d0e0f0304030c0e090106050607030c0209010e07020a350405180609011205030f0304030c05011a 79
    0x180d5a030300d000300140010b19207120740802130400000700c1c0d4a01c14412108402514480d4106246410307000100300d0301d4020000c500503400c001945001a412164145800f242403c0158480a5500125000b4009503000421604c550000d000000035203a000150300ba1290340c40c02c8050042400680e0748820680f1580100780c01214100046001083c2001200300010f003064038040001115a1030340e0045501900102d80c0c0e00d0781c4c503580c40800c203c0c0c81000003450000d981042e1540e29811940c4185100b058446070300d40340050b015510a6014401814004101545400043c24000c104e81c140c0c0e0400c80c02944440e0021031746a2b068207025209243d0356004040c030b4046a603541d1410000481d02c0d6043c0e030309080314042c0510012030010004500040c8540c0c03141e1404042100030290852100f40164001007030000d035440741804241920078840e80030500c41c4007403400038035511450a03604420840442408101a44402c0c10380501707018030004d120075908000e80310104104400515 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 402691735 1250 402690485 402690493
    0x70902030103050601120f082107020d051b0c04150f0b0322031812150614120307050105131a010506030a0903020f07030507080f03040b070303020d0207021e12010509 73
    0xb0030a1b003800400390440d4426900b108142ea0603544101403504a00001d0f24500902c41c1c000c5401007444408583c45400392000341160b00b442e1001900920891017080070303012200114112400e000c20901c160032001500402c444a031503040310854107800d0150320400a180a0000f4110180c5c02c140c0e0300035911090010b202c00d030016803200080d900b10000300c1c10700c50300700d0710056030318029824940148404044044082c0c401d10b0064000c018540072404851b2520b007080c051031000d079281e5507c1d0741042d20040480090740012615500980000800c2503080c0340400544883c8500340c600302d58440d48102c0c2c5500c01da5485c5031041403003401026080741003440001c0c480e40341707600001f00150080c01a03800b00c3d00765182c0c590408805800650781d0740e02c02c4004114041d010840000300c0340b40040038506090800d150082c2c1e910401401404258020170105a803030308582c11a09074583c020802812040451903441203800c0b401c0b41103100d06008000e407200b040c4103014451046004038090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 402692985 1250 402691735 402691739
    0x1060503091002040f0501051602040f06080c0102070806360d09141003050604020702090a140106080103050604151b20120316020c090c03060a0b0a0203030a1109060714070902030103050601 83
    0x45483e0b03000900b44614100020127008050b848500c40d485440010343d1002c40c40c1401c0010349490840b52100a074115880312404011980000c00c215030802400e07000d40307400e40181d4a4040040d40f0f403c1f401503090184201c002014440081c400310100e0094a8180340652b41c1d4184a5130910b1038445503030000000403074041940d120b648800d030302a000420041c244003968010581085044806400890350f1f8604074203a4028140c211b80100301d1840d00601c03547c1141e031426120140980010910b07501c00840c54902d44407500100c5500c01c00d400510104402440c009001d203100ca10405204030103813800b00340045011a52003000700c1d498100300d24640315074601c040040f001c28400021806090102408e5980c2c2800b400c1c09003641c2c030303807050b16030600c44100700250314250310002c00d042c000c0042e0701409801105032940007604030000106405140020041846155001c2e80d0080e0002040c1c420424011558003042000c9402c88011075124040c2504a100a020207000c542c400e02c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 402694235 1250 402692985 402692987
    0x20c090a0902131e050417070c050414090a0b0709031a071103030621071a030a05061f0e010c02060a030c03060905040c0b0c0102040f0f060e1905040b06090901060503091002040f0501 80
    0x1031504903100d1f1000c1800034042e600040d0907600020000c40b458030390010100218502800303141181402810034200310b050802820b0f580b05034140c3c00910040c03c600015003141d00811451005541101d055065000600031500f0040c0003100c244012845111b020802400c0000641e0301c0f03450301070140d5900c1407d501421301085002140402188103055020039a658140d0a80806010b54011240c0b070382400b03100302e0706888000382030600824404840c100500020903e200080d146820000300303c040c0000100c96160750b034400a504080e00048044016034564400b10b55400a941d04100030307601c0b1074100f02620f81c142c8000d084e1024144041c07110640368402002d2014000d80018a01a660507003ca410446603001a82100d000d0000700440c503013048014010882c1242d4034011024a02000741d00041c040c0075036800303103654402c520800d4407000308941c842c9800414564096a541000500680c0211140c000c41c1c000d40da00d20f843e8039050b00039607060320007130329515a40c00c0c20480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 402695485 1250 402694235 402694241
    0x14070c050c2808011b03020a0e0d0f050f0618211308010504050c090906040b15030f01050a050106090e01030f11041d010902010e060c0c040c020c090a0902131e 70
    0xd44004071028142e004041d01c640402c54000300119400401e41140f0848150094410002c01d03d0516004016040380c00c2e50007145010042800c0740c86104056031070a11007840103941400429034880c001d102020b01200081c0144100c5100c0c603008640d8583c11140742e26001c2280701d0240303096145e07001c205881505801b400002201c1107988070410341e41c8a5003800c0d0f400a071001c3e107142e00710480c10400d5042c00c07048158421030040c01000607040c25560300400d0b410040c60212803000704c012002d500c1da02401000758a210f908004d000c4c0b8201350308804000c1c48280b03d0440820545000050300c152120f48040c12a13400c420640c00034902c6485a040c204080105c0c1a440b40d03984032181a600040b1024451000312071000049181c071620025000c0c02d1070054443c0b10310f40501015866140c0090200c50014055902042c1c1c0c8031180816460f140c1c000c02d4465202e0042d00800149246960120403200c0c000c59100729206504007014048903050750911500011000c4481c2004889030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 402696735 1250 402695485 402695509
    0x15070c120f020d080a020d0503060603060f0a0513060e0604060501050703050d110403031121091219050a0c09050f01031e050d0917030c0a120309080d14070c050c 71
    0x801c000040a950340065040c8003c1c0404803940c1c8800302d1011001e960400c00c59841d5607071400c05501d0340c1048000a0303128040100994803405a0144168031a190444d50b0001480c010703001c984c0c920038900f922405030440e03014025203c0d0718000090903924088c015001210410b844913407130800130391412182907110801035185d40e500e03200300e4006805580c0c001c100079800ba0707803480395180f61240c0450429680442c190740f20f0030040003100c0a8440c581c100c400d807400c1180c0c2c045141c40c021400a0900c031000f04207003c00101040c01e1000d1010109040c10036610030790041d503015458081010850b82c0580d10703030000031003c60041c0005007451803061114120341d001101004c6040e0740c0c151600c107102c1c01c406e0020b417000d41c08200140442040c03072200c4251300c0180d0b04121941100e182e4078105044040c1c800740c1350740fa01c07008131b81c040d031b000c50301381a0851850359480c850001000003810f070011038190b1100304800001c041030f00c103014040507d603115000c1d0604500320400c00811000e51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 402697841 1106 402696735 402696743
    0x180d1103011b0801231003090201090e040c090914010f020a090509060310020f0d1104030b0606030907090c030e07080109020312120c160204020c0c15070c12 69
    0x10385605641070314030b2450545511721510104040c0d034103202c1d50424940b01d1103803103840d4103802800145000b1b0702c41402c0150b035400d05072468181103a000d00703a40d40000c5c00388154019904800002800f070108401c51848400d41e403402c50306900f40242180f175000901100041c0c1001c9080014038003251602d000b460300b04042034a655800315003c0800c2c1d80040c00c00b611a01200070b5a07124801e410382080b50500d5415247e6007940580800e5485800403030001b1801c3c5460070881e1703c40c45c101c10181150038503141c0b9110207000225503510502d62214000134007401c00300000307401020280e00208803a52540181406c12100f03100041900e4420803208091440c2c0d01c6913a03030444a405442035035452000642c20303021041d04002036000e40001100f402c400d000003103800919078222440e903d180c0c0704841038541d61040c40e82c000d000e1400345104001204440d00b44000c05402 = true := by decide +kernel

theorem cover : BRFrame.Cov 402517985 402697841 := by
  have h0 := BRFrame.cov_init 402517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 402517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 402517985 ≤ n) (h2 : n < 402697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
