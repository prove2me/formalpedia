-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5423
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:49:22.39457+00:00
-- url     : https://prove2.me/submissions/a5be048e-618d-4ff0-a193-a803a9dfae1d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 975179856 ≤ n < 975359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 975181106 1250 975179856 975179861
    0xa0c0e0108031c0b3705060313140d0e0916050f03070c0218190504050717011b0804051006080d14070b101401091202010e0d12030f05180a0303 63
    0x100f0250b500080c00340141000c0f40e080d8039901c80405542c54003a030750101c0014102c1c0c3e5025224241840c050180c0e00b003200042d21480040c001810b2885900c1001d4244050f0358004c1410400c010200c694810041e840a0000400380210902c40d07060f040001d000e6a1501d0500440900e403640d59a14140c030384051024990800b910a000b080301480c0304100507100e0003e862400d401e950b04245041c5800300350031701d0213500d46000d40750382400d00c01840005030001607050203035100b406400c01c040342004040360041c04002d9219804054640e0312407100c94001814034082c6000b20251000e20080102680540300e130341c41450055800f401680020351f207d032410803041340003942d1240c0381c0022603d81400c0290203684104103081c0e065410031003814102590078110100f800c05621142c07500602c0e051540684802905004900401401580d10301c60302c14100c80e0302c1088232880042c0c1480003001812414401d0321b1903841c0c0004540c8503519501d05511005140c001865050405d0382d08501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 975182356 1250 975181106 975181147
    0x181e06050c0613150f0f3903020c0a08040806131a18060910150b0301030803090109080307030b091008060a0e071a120609040218070c020603090a0c0e010803 69
    0x80045006a40740302160130f6016644d8980305104020440149101856040b2245841590700704600341882001e00c2c02c40e400d400003961700c3d0344031440007030074141401d40c003903c110250000280100800041002004005441601e404008844a5a0f2800855801d030280200e0140040c440310340c80d042e54400321040294403038496102ca05d40341d0355500007146044420345c3d01c0342ca51b401030b02c9550050401441040380381c10825502d42d25152912604203410b12040c0805880014000300090f020b0009411032040c09078031500c0c00d541e0f4689824003e008050418941d40300342e82010100380242c3c52050008160ba12107c05080b458071081c1d0203a0050690021100c890300031040e00041041c0702c4004462030300c150004440c2c0d9080103070b40c10100868001c00003031041303450006200c0981c403085810051500502464281e41e282da0900343d68001070203100a620660000030001d803c0c6001c074610b402c4601c2100d6260000d5101c07612110f00c444d0074050304610354000c1c0b002107a403c289060851 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 975183606 1250 975182356 975182363
    0x406060e060a181b1d010503070504060e0d0b041a01051504090e0a140c130507020a08130305030a11010b030f1015030b0406021e0a050703030c181e06050c0613 70
    0x241c100b44981da28820404c0e0100c4030400300d03171410064182d40e0b004a480f00f002c44000d01c0d20034030f5813609020181950086004100c08c11022014103401e903100c2140da0160560080c0c403265003440c01d860a03140321a0881c1c44440108154000001c060030050142082104189a11341c100790508222100408040141610700c0c405c00c400304011424180c1503401000844001c0d000c00c0e00c0c10b40030300810700b054500b4401e00b01d2600c0c0130040d045501056800381a50300c2a01c0640d02da0361111500c141c140e4940024100307000008614010302c3e040181d40400d802007100074002138901000b09a114107285020f642d468001c00c1d06003014980c6540300002c100c018403040304009480744c4400310014000c4504a80c2681e0009200026195001c44004060303001207806140402c0724400130920b0240c4030000f82410780b100300d0044254010050030300c900d0300d0011341070b40d215514000e00100111a403404e01c00080444e00120f1558407400072208101180030007440c0c1c0d601c03002c55540004a0040095 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 975184856 1250 975183606 975183611
    0x60103021612050c010b0f030a020108101512060603150b0d0608070803071407030f02090a0e030309071505040f051e3303130311030409140406060e060a18 68
    0x1980010300300703010740000401d25034400d03131a800000105403c680724030401c0c80c41081a1180d088079a900000e0120945a0a1916a81544078804210302424060300110118500d070000f11400c070350b000b8519075424180010500c01940e070303806d040e0102c5034001001820407020102c18400745010000608024000e440b0008009542d0b000390341c20505503800030129500000303625814130140100390100031140c000540020303071451f5074803005200314420003406a03109000041c80140c140d4840c07645601c421060f40e40d03d20341441c04036241c40d000e025009504480c4502c10781010f114a064400380c404890740b00e07440038209800c00072000284164480e801103031541c668029221a040c2030720b8034480064a030140322250028000e9414960101030383c29005004021031042011244151260103040644400ba0140c12190451003150403100500b810007881005076044600c00038451806050104020358650b468188489400d5032000d0740840d0584040c000c40c0c0388403e4080700301c2d0000400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 975186106 1250 975184856 975184897
    0x203160c05040f021305030c0306070309080909040f021203040b0409110c01022206050a0c08031008060106050403050c0d020a03140c090a020a0806040b030709150b040321030b0906010302 82
    0x40030344000071204071111340c001c246250051300420044010b4031044018049150400c0e001c25603840000740106c0402d521100c55200b03005903030080300c1c4800c4014250108a04d000c0c14160340103801b41030f04030302a0389220040204518003100f56020f4030952901540360500e03180c042c60181c8000f030480c64264404000d05400030409100402680310340c1d2007c01c1ca4280d1880011039900c0062f4000c200b03005042180041c020360040c9012030b103641c400b078400d0f1a03480f000c5d48072400c2c1d12a40c11444003482848008155603400801910842e03200350110f5810003418014052000c0c800840290441890780742171000030390005030841862000b004403642100300d01b00087e00100151140f00c0f10075400205170748650780c0240d44541c401001d60701071000802900c0803176501c0645104080300343c1e9861341040203107054207202c0c00040c0a944501902ca41e103908000100408517044500082c4003480c042d9642c078040c1c010320b0849071008090303c48964503000158061f5100c50440344d00400c45064 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 975187356 1250 975186106 975186109
    0x1c0f0c02010203370801060503012112181202030a0b19110711030102120a02030709030602071109010e0c0d0b0f18010f090e070306021e0a030c0801060f0203160c05 72
    0x101d0f522221842204000000c803800018040d01a410f40303400b0421100b00e00502c0b07490740201c12030381186c6615040c002519400842f03843c2c1030880c40d2000b461500031045c06200168000140300414800300d14032580c160f5190860300c81c013003010400075019003040102c10049070840010300e6100e04039290482c000c02d01d02e00c212003101d0350141a09891100410950140100107400c0b8841001c107a00840c40d00d00c1e02c0060140106001f050403c9050700000040c00c1c09101e4120030000390b03400b0380255214a00e038581030701c1406880385014003683c1040c00009012110096a034042d54010100318500009000b03410082c0000e030600581102c44010800040d444522002c101405191040300310780d41425280610501c130703940032119007400c10100c15010391303000c0b40803412280e0100c03005941c3c0c0302017010031144640084082e40c0300c05001c20b4034030209816400520a403041556003030820307030306e605047e54000111040da200591051000d0300c840c089515032218124000e200510525690342c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 975188606 1250 975187356 975187387
    0x121b0f18010e16171308040b040b040e060a0312050c010902130c0807021b1c0c080609061605190e040f1541031501030201021c0f0c02010203 62
    0x1d21900c5602100001c01c03c0000c0403071401202c60505140000961416640e841c44007500608840c1e40071995003002e00030000b08100326001001d038000340310303121541d64403082659006441007405681080c00080c80a180c0342100c0401e590780000283c1842084610884203500545442201d56584406050259640c80c8011b04885d074403600104443d0010f030350003004840040c00304415940001001d8000c1d80e40001045000754040d103809075283e021900114526081d80b40240100103401c0010403174460102d0714a22400200d01114007a46070799840c80001141d1120000002c0e109000b11200700b5821303070088034a100b003071415603407105060300041c00b00c500e07a03219208640d41d54003040310107040301c040b03e100038600010550b14401c40e161100b45600b81741c0688850b0368420302d252a4001c544450300d5141c00d0380103403c5949030510001c416140e90000c0c0000c2c0c0c003500c5400c40301038032802280d5a40c59100780c0c075614010036003003001d015241840c5a09049065001c1406030404801004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 975189856 1250 975188606 975188609
    0x12705120102340606030f03020c0f0112090302030915041a030f0105040209060c2a061c050c0d020712030612050d11030c0a05010605190e070806060706020a02010902121b0f1801 78
    0x51640d9402c204407841d028aca0005850023444c042d005980304056907a03003102111041529400c0301149500481c9001c904601c24050740603407200220804401d88503191000d0000c0e10703a03000070047e50181c0b100c100c182c0c40c0401c503800c5204504030001440705050030340203804000405000c02e400c0910703040d00981410140700030780b50610510f00c886502c07400d41c03101000c7c09220a4401034075200c90f002c111901442c410f2070302005151604081201703050258215007152200c4202103481e94407a20b001054101c8007107440300024208080460849401241d100354590b11200922000c1032642d001d40c0c6190986c0c445c00e5850009100d401500007007801600d001600c20700c0001f404900344020007a052200e15048100c1580e44a070030b100600c00780c10705e103401180d0b50034054802c0d034407280040ca25100b40d0600910050011a00305504c035015007298410074821204e10300b04460081e1304603036448103403041d14240401400081c1c0e060510701d001c00801040508840000e1401200d101ea110400313 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 975191106 1250 975189856 975189863
    0x60667020d1d01111c0c090b120f070f020d0f021e01050901050901050c161e030e0a080c0a1a07020613060809072301270512010234060603 61
    0x2990303010304809400e11501d0714030f040c00c8100c6400e00905a44c05d2507890754404500640c5543c68a01c500000d024850000003800d10482c0290b40b5074640811102d8070200752940d9800c245800c020510a501540254818040b40e0340240080981e10f003003182d000301200462401e60182240e842104101002e24410300f80300c43c000401e660901540c02801c40718020004103031a4584014042c965842e00c084524010221108224410b01c0717041c1904d0b4645056505a01c034401402c9200805800c10041d181c200b100b154440000c0e680c4225103911070041d81003031039005100d48000d001e100c8100d04983c5085140015090070710a8660124001e81e026002c1c8103040c3d18041002c01c18250310008481d4000c1e10b01c80504145850000103103856403040541c1300c1605002c01803244070340d01c81c843c201c2c44100000d803040082042d040c40051540440d02a84d0700030000352007940e041200c14000c968111010980140d506080854041012017034212003070740f0f07695494a810049900c80c001c2c000a03500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 975192356 1250 975191106 975191141
    0x1b0f1805090709050f040207021809031606050f07181703160501050f13081602030a06050106030e070b04080d050319020705010b010e10080105040203060667020d 71
    0x44c03404011550003921074891250340104400340050f140c2a081c101c030110380715210b00c1c071611100c0d102401d5008050104511280040002081c0029034000c5e5000d03407802c0920499580701d055044941c10044944011070b009488401c11a00d0029040c440c1d080e448031058900f4045680d00580da086048202070703405a444100344208116036050f0142c12281d604406160311001da5500f51440c0154000a603070a0036002000065403414009030b50880d40c010001c002c90741e101e2801500070440e000280c41107206d50b000114091100c582200c0c1030f6101381000740071442052808403003541c0024071000c000b888802c1c10410710140c500142c1045845180003281030382055000406910407030415622603020401203a0400b60402d00690558006a8026903a6034a40d03011440521a011804100c01c4e029201101c041d40180814259605a04503c1140c40f01000c049501c180d0341044c59004000900b008546c1c1035226600c3e003400e000310110150030400b05218183c01c0701d500e100c14940b00c12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 975193606 1250 975192356 975192359
    0x200a0e060c010c271217070609110102030901350411010807091d1f060c0b0c070c0e04020d060e011d01050903160203070e0c0a031b0f1805090709 64
    0x1d40050010340c400d4007855098044131850b03683c2e0b000c0303154240301d5041c02c1c0714111955000d01c00c00c60045454240141d070790550700c1c25503182800c020300e10080165100c1e4621a000105580301201710b50903840142d58100607a4804c10341d400d2002403441000d402d00ca00721001c2d584118002c805a80b2950241c65044180c8070301d84000b404182c8000c000004000c1e20041c03d110301e8205101125101b0700849886001ea5140034031752180c0b0080c50414111880030100008802e58000c42e1140e0341c520a0341c500c4442d0b229003032070407c1801080002803c1c1c2c0d604000500002c80c0200820780d2040c00109000152020341d22001d044031201c0345010382c5c076511150440d4811301440090200100c444008110a01d040103d058036400788496010404c01a40901c0e400e65608125420240025500c0a4082c2c203044024070381c2d580c40007903c00d010a09201c2545004100e5041c03a102140c1103450b100d000b111300c0541214000344a40c044000c440302d07035601007442c1e182e09052610032a40e075115103803810f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 975194856 1250 975193606 975193631
    0x330e0c040812030408030106050a09091104052e0c11040623191e15020a0b0c0301030302030a1115090c152a070312030902090901200a0e060c01 63
    0x26452040951101010030a004c0016149412641128801d2030500d48035158032070304854000b030700c0e4000642076040444d11030403001d24000a104461080f5001000015500c0c04c0441484040d60214400100020096046030050701800c452034424401d844907400e81c40300003030880f40350f0f80104800700c03180c10340c1d90001d4a5503815820507000803181008565180e114901d00350480c1d0280c20780f20381c4510810b0428035a0100c0940c080c00350502d2a000c102c0500b14001e55850134904150b807181114004242c03154000c00c2124141c0760554040c51034252103030400d8030005a00c0d0424822840703449402d001d0440700766405409460003c0290224000307450402c01ca82d201c4215602c1c081104004900d11a51082c0c0708170a44508100d00d07040da0f1400025060800050343d00103404145c818410030300856155100b0300e1b0040c42154142c6071621000602805c07030700c5100304800568055050300c0c003160050000f9004442c903d140100303a1000610100b0599004032412810316034454500c412039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 975196106 1250 975194856 975194863
    0x15030504051b0120010b010e1e01031a1201020c0c0619031806051311010e0a0329250302070210080a06150203030610020c061b07090e0c03060a330e0c0408 68
    0x523a941120030014440c00001280401e80c408265a414580d54074103010042100a141808604002300b0200390140c0e4140014041d42c424500a41c20f40900848501c191800c003055465070400380c5c420641c40e514600c030a500400c03440d40c0001c04032106d83c3c00803002400c14050301e446082e050081c07500c454003078030b00569443d141c02e0b0468180b207121520004603884103103440d41182c1c1c20440321401d0144a24601410a00007a84c030000c3e82c1d00d24040008030910b410500501400380c03801078014070715140c4118128050a08025070124030204100301542c41680c40c10740100034000d0014046585003611030641c07008088031000350b000401005103610342032001d22540002800600488604d003000200c03e4803c0c62500300003079000384ea001c22035210421002c4094161100c2c2004030030100e00071150f4407852b0390b0700b0a20038030405000910900d5640aa0302c92411304a0148403e031a95803480d0301d01240794044d4400440c20320f40d00060103030644a40500409110305c0b600d41e00e5040011a505 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 975197356 1250 975196106 975196127
    0xe0406050402090303070f140f0a0b0601051903020c16180515030a03050307030204050907080604150602120f0f040603150e01060c020d111201050115030504051b0120010b01 76
    0xc01c038070620019a8940380403044071341c89030b4000b2404401d8403040c078003c640010000b10b61038003482810f401e50300d503440c0010440c20a9001d400b10b00515600c00c4011074851040b880701d00300c00814211010354541c002d4002d04080e03840c0500b03540450182800b4014100b1803580114000301c1c1c0d10049001101c49071180542100089003485203100240003c41d0b540c840c05407000b41000800800a07104501c40e6040e04c0151400501a410f5800c001c83c00401844007541c5991045180001001c0c0511384100c0c442d0440d450350300a411076a02c40400c040c084d4000f900c200c401ca41d400c100311004044610010009000301c0c1d10300042104008000303c002119a4000360500040c8034014410142c1041815a1a17541100c2c1c1c602d4442e00c62030071007456030003041055000840360f01c2c0101c0e10441908a1410b81c3c414000c0a90f200007150703004c5050b03803001d03200500542c018801e00c5980700c0700305032401041031042c14100080300e502c02038620b12449521060045945d02d0a0a810382c1da4031070740201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 975198606 1250 975197356 975197359
    0xf0d0b0a0e01060b09190902030a05010302040b060702090105090a0609060f060215010e040f08040801020315120a0b1605131212030b01051204032114010b070804061d0406060e040605 80
    0x7841e070518a21540798401c200004c4c0c460a042e4038000030010700060010041c000002042d0340703908ac209203050280400380022841a400c2001103045d5003808016100440d40040c00100541d2a02081c04402c0324054160116035494207008190704000f80140001005003280501c282e9186c10002400e1400c05560141e111022100400864551190407034101c0e0b0400005001180c96260042d020702c1140d0003c170b610350000c07080120001c1c00c508060b103080ca0543e44078900b0840703603075a0350700ca6880c010014482c124200200304107001740001b1845480b5142011480c15002d07001414107840261700c800241c115003103102c0d0400c440e5590800c0e40744440e003402e002d01c6031802c0c0003a2440c000e10604500b404907d00024050501c902e4101a0042d00703103051132068120000481c0181a48022001c5150b03442000041c01d2520b80040395100703604903141e58201424000103c401102c1d10f1682034064115104030b20b0103035124800c0400a21894032488003911002c4244000d40301c1503032040d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 975199856 1250 975198606 975198611
    0x30b19120c06020f2a040c21020301081005090a0221160e0c0a1e090806060306010e1f270516120c050403080d050702100c0207060e0f0d0b0a0e01 64
    0x2554540000c0e110000302c20f881200c001d18174a480000360390b046040c2116405810302250f2107200350040c005588545810002d40059002051281c00ba80700c00c0c0300384001540580701210201559600c00d81e007001c0f801c816510000346940004510f04414111884007410003a40150400c03000c00c001d02c070444d51401c28154141c900220700c5080030b070003082031101e0040060746e160030301e10030040303041d0318071031500041080c000840d802005000e0b240183c82d15032058030b0129245180020710141255104154024281c0d01c255103810a60860308040001c00e08414010070121301d0704214112a49454130310b48154610182054147c44029100c01407503030305500e185072201e031300c055041800307441c0b0b00e40414588071100c002c84240c41103520141c52a000030a109500340c107103401907406500d1a5007141c001302110070b8408100da1203c181c003400b50f0720003807081020701d01482c0084000744000381101c100010031400303c0d031212800442141e4180c64041005801c08051007250240e03260a07008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 975201106 1250 975199856 975199873
    0x61003051906020c010c20061e0408220510050418090f05070806100909030206040201030c050405041b02010c140412031b050a021c020a21021e040506090412030b19120c0602 76
    0x9ca01d4085403c04804501a000e0001010311860300c4c22240300c220038005104100d9203000d82101c40c407203180549440f40350318401c11180b5500c21000d480940b01da0f6220541180c00800150303005002040d0101c625042d4445054080f843c10f1102c0c1d801000418050a228035192030004035480c06a00003125091401c0c01c42c9001c82d82c00110b00754026030a080c0000c0701c00c44c400081d00c203406268031042d40203081094500c04040f1200c0c0c1c80d81c0241d110340080c86100e55148003680c41c01d28451600440e9071080c0030800080c14520401102c40d0f000781042c500c0c2c485503003071900c2440c1d0860000c1e903140d070010000340c045041070700d40248003005640e034140060120b0f90024440301c3c207034810742c5908400041c20303c8884405a6142d40c0e100e0f401440d1240004011542d046060041054548607a14150009003070303040c407610640c86140d0103108807613604568034056005090308040c00d50015100380c00e5084174212440010040d20004c8010f1145040b28030b002041481e040e0040000c5400c10f511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 975202356 1250 975201106 975201121
    0x60b100203090901090e0309010819060b070c080d02030304110d0b010e090c1012020c150112051b0d1b05040e0703110301020702091803070b01060908061003051906020c010c2006 78
    0x95440b408c0c401d182a08840d1030303401018a0300c1c0c0c6005a6419910b280c40c00005515050800400c2c030648a2005055015500c0b003049403104509490741001d6042000000e0000b1400600c02591860051900d078541c0b10540b11403070000300c00d030452400d850440d01807049000042142014400c1c1c1151000b01118810340001c14246566a2007070038550085449000d01e281071000502501001e01c00500ea0340e554040c0c01c1c4401804282501c0c01d0144140f0703482011701c10004221008006845502d0070b000c241d40784080481c8013855140c075412440c1000c103960f40e442c018030300f01d0b00c141d900406109044d4108154085501844540309a1041050b140161501d0a24541c0034468201708200c2500c2e0030070580c01c5208042004003a0f20360b440000c24402d81001344081034400b0034080f109607a44e01b0712030454000c40d038080600103038412040180c040f91100e8010056a01c1100e0150900843c0181c144c01c0d10003021588001c10f914441c003a503502010302003490307a1200e120041c0a075041402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 975203606 1250 975202356 975202363
    0x10512070506040b0c0a05120702090a152d0305030c0115050a3c0608070c030c080307210e21180609100206150d080d09060b100203090901090e 63
    0x1251307001070680450195408a07060002c3c0200c9501710080da4011200740340006030560110408a206200720000f041d0390409621030307000304042c08020710707a0507070508400702d1001c40c4c00c80e01d1022901d94441030f03281e481124042480114400d40003162200d00230490b00d42901c41558018041c11803c500402c40750341e41d003411108544503820301880c242c00d4415280f07801c84900e1076101d100440920141c0d0f0004081a0080403607003180d503106000e4a4560381110706d1800010040d00080c5039000030404070348003000468000c5c0040c207018016070f50030800e900c2219524422074100b2961400c91a0103800144018203c2694256034169403011801003402c0ca409420034080c9100c02281e900302c5a034940f6407c0303c0c0e030100c0043c0134001d14411070340021364464044844480e2400d2108510f011820300009440c18580d0040d1918107090100c0107010081802d04004d4601c0d54440d849642c040d1a01000052000b007150b000d150344010030814082c6281c8181d1210b1f990501e40030401c89071f210080b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 975204856 1250 975203606 975203609
    0x110919080d0e0f1e090c0301080114090d03331d1e0403022802130209130e1005100e090a020d0b060f1c0b1302030604030819050f01051207050604 64
    0x4039a089800c140640b038130b07000009102d00c540c1c2c010400409005042d032248002d5812101408024003610418040642080303100f80d4595041d82c1c8543c0450310743c180603402420070340d6070030420700c03051a502c0304540306c006c450402c1402c0c4405c8551428800001c80f00280041c84150b80d01c0003001d41006c03a0300d042c0800c4403100145181300c080b07000c01c2c10980700b84100c03640c640e440c4c503018800305111a50140c0110a6100c02c030301ca2020010070110441003402a17a0209100401041020082e0480000540240007000e91507010f102048121000940700d054001c08030300a03e0b21042d802e03d1810b808000c0702425031043c940c014045100181d40c0e02c00c440e8071a5034410b40340384241d201d8034007284030020340316042e42c1d115459500e0400401140300102100c540103035150350250b10b81510006c5041030407040a034051300503e00080211703005015030740d0002030b40d11160320b0160051034902d08440b001d0368103021032035444004110901e000084040c54420340c60141103a1482d0400050b0780e88030320b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 975206106 1250 975204856 975204859
    0x9010e0708010302012003132103080c182e0203070803010b180a060f020c01091a0c1912142706160803040311060f0109110919080d0e0f 60
    0x8031116180035004e0301c1424415030f481ba01160740b10841c001e20b80603103601c4c030700600c0390340c00e80c2e072910484018415144503d802e40640340c400d415110722194504952090a045402d58080d10b000d0740d06803220040c0300b454052602c1c140060750705424413420402e5a04940034210f60092180c000410030081c1140e0454281f090b4041d5515100400c600e40312102e400d09903440042c010300010b034541c000d4616180f28040b68251a0204140b00c01502c4040e0140a5050150101d105104c650030603c4001e01080e140001102c00d01450324400300da190a82c3c0c1c40448440030200014a4510340080143c80b100111950b141d04054103840b455146000000c00d21018401d245021801a290132044400c0484207114054092800c2e0078441c04950042c1e90803400940042441d504428000c00e11070701800404240080c2640f030091440007500c00b00510f054107000c1084030001590f40c66440060510b0071001c91080545824007842c10b189002c1101001d000c0e000803188010307540c010721480b40c841c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 975207356 1250 975206106 975206117
    0xd0e3615100206060f0d0b040b07020c0d0c120203010209190f1212080c090a0f081c0516020a150309021e0d0327230102010b0d030302031906120209010e070801030201 73
    0x30105c0006124240d5464081c080f614544288000d00c50000c1015108900d00d400720f40300a002000ac0c00107004000174054550f508100d070911802c007801d0b00d480103090004001605000000001420000c005c020148404155030b00c10022804a0340c9080c009102c1c030102c4078400c4410f52580c824500584a401d400c12818000041000150130265a10590090038880b00030781c45010901d20304d01940a000514840c0071010f90014240b00490110803076180d0340c02c4c2c28092030507100ca100801c4500200ea01800c01c003008a440c2e030300004003030803481040d41c004c02c0307140060061295240b840402c1000e0380030510360545c00350b05c880c0e204225240d07241c5003005204d51412258240d0501120b03840340700a030400400210b0520000428003040e0541040030f0444421a00580c02c0341c1d46c44075000e0b001400c0090090200b4080c0d4003455010184011003039000c5401030a445c01c440198015034100d05910942c0e07415802e200303a00c98003502d100d10106003141070800001d000440d051000904201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 975208606 1250 975207356 975207379
    0xc0312072a05070e0a02041a360310020706050601140f0c0a0b04111315060c020d0c03050d0306290304050708120307110d0e361510020606 61
    0x1200f000110010001d6188a401d40c1c2000c207442c00181d03126205000800c0c0700f0b40c1542d0001c40488007203070041d650074150b9032042006403920402c082d03e000555820810001030092058400780300d00c4001c2c0208000050303076249185070820480d0005801070b810440c400711801502c04400d400c4a0b50520000c900b80e03110000d12a00d1890824884401849100190300348010000001c407007003480c5808035180c0039030424603800e003012954071594001075008044000c1029600410802d09084d00240c101c80c80c20080d0b46030322004078000c1c0d00031526688241050071102c0d41c184544000b40c048110f40c01e1180e0b12007001640c0050054290710010400000072800b00841002040000c2c4130301010f6030700803ca03940c090440c82e0000c80c3c00d034000c98001820180c41d804041071210b81c00c3c009841d28140120f13410140700031038128400c5000710600c1c2c60140412150b068a908050750f030301e036880181500e0040c00c6010a41c5440c0c201a01603448505100501d039000300340c8592007a819a421324910 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 975209856 1250 975208606 975208613
    0x60a060518211c0f45082415040510091407120b030a08030a1506121104050306131401140414030702060d1104030b07120b01260405010605060c0312072a 67
    0x910200710105d0846400001042c44011604c0040c101d004080f1096002c61500415410402103030f11031243c0d0407502c480051481c095010320703003021240c045100c6a503150501700040700c4106407404030751403000c0b0401403000e42c0075040c0809018203200510004c010580400da40e0645407200404480c4044001111020703030740e001039003038103030040d170168040e60f90800a84503601c510b55040c80d090901004411401c000c02c105d50883e08060000e11040d6203000280021229689040b604d01d504038120100b140030074002c0203040c03510740c17032011814201450b0200c2c1c0101040242c10701500180240409661a1429283d00700ca40900100d124080c0e038401c8880340c8a281c10007410342e860081403040f140d44c88520300c004010240760800c410300400300159642c440540b000130280c40400c00c07140c03840085034445500f00340f02e04008100b0307941300c5000540507004201c40324451390000c100d1080e202c0c10341840582088440c1485c010b040d818a240141d2500400e111154640d40c0c1803209041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 975211106 1250 975209856 975209957
    0xd0b0a0e011d061f0e06010201110d1e110307050c030d021303020405090703050601050d230a030807030e030901031121060a060518211c0f 61
    0x14015460081041002c4010824128080c2e00701c41d0700103104040c0024410b2215021a100e00700c10703016901400e6143c91600b9140c4100180a14115521003034000760701c801000140051f1640e100c4007041c004074100d47c1310150f10011000b214a90f0810388400b1214006100700c030741001c594a00180d4a8401d69061440c41c41041c0b1181030992002170601d50071801504840300780da100b12020310a680314914080d0340c0c4d42c09400060010341200004200c2440d00701840314500d845078481041403031324070a400c451224400854a0070340c00401c0719000301a07002ca90503510040d2414100102d07000d05c0106036803030192040003410702d680c610190044980420a45480c0b98042307011010701000803e82c44481300c010340e0324a0182d00814800304255000f903054428a00d0143c8c1c425a20f044100c01b04403081c0c500000b0541440088a40b89156100038440d0444824003c400c1c10308881c601c00c0010480460555945c04004030803120342ca013210005524542109104809070400d440b10186401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 975212356 1250 975211106 975211121
    0x50f040311071205010203010f0b0a020d030213090501080708010b03030301030b060f0406180606033602041104030809010f09260f0d12050a0504030903170f180306150d0b0a 76
    0x241441410f40344400c00c001500294140c40c00034400301e050903600c10207a130160141001d6107025030131001690034074038801c3d800384c04495100380020804941d1600038804031002a085084039800035081131203480000d016500424405070010742c030310341c59902c800500e49405005144984600c18045140e907a50342c220a001d84805858200c80d40d00da4050f0000924440c810400402d0402c1c000d4907a030300243c240c88015020450049031200014002003c0d140740981c4104c0c0e209503141000c40c81e2114580140c8060352190514a541d14036480001d0b2121210740c01c408104800100103020000107076044240c50b80c03116a82944204502c41c85900f09008200c2100300745c4180800d55407401c0d0300c000c02040c00a01c1d1501082280c50300181d00c0c0c03d844044602070042206000b04200084c00401a180c5411030440c0302070400207000d101a80d55488541a030030807040390503441115203014045507401c081003011480500380c100000c12500b02c0007031809480c5141d1000000c06494850708201e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 975213606 1250 975212356 975212369
    0x5030705070602030901050601020c090c0a03020705010219091a0a0903030c0203100e03040e0a0b0f10020c0a0e061806090c09040605120a1523070e0d0506090c04050f04031107 77
    0x15105c0c035003c0e0040c6e0080100711001401403094500b480400d0a103001000d0080c100c005085182502c1d00c1b0b4160065403009004031000d66082010070440e10310705e070625425600c0c035548e01e52500c4c50004801240f80d10081e030702c503c3c03040801034a034405400030040c0044940c58141302041c0100c03800042c3c2050b545400200740320703080c4241540200c3c0e001c40240255007d042c01c050759901c920503c44121522106401c1c1c000da001c03aa41915450541c21101e084a40380c4110391f00800c1810104211440581c4503445800c0e40b8820b100041c640f403d80ea90f034690701e001c1600e001e8648040007c0c030300c20700603250842140f00011085039607140c542000c0094100508141c50760550000120740c0c5000100d002d0355507030340812128841800600411180c070000030443c1e4603044600e404001c401d50040d0205080c0301020170242400d031607000768000410302540141c401e0349045085103040ca0a04042c0503c034900d09001c21072900100c0b208140c01c160140b4020b50846190341369585049550b40122 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 975214856 1250 975213606 975213611
    0x10c031b030522150818030a020303270607030e03090409080310120c1a0904180201090b1201150504031b030201020c0a03030210051f08060f06011806050307050706 72
    0x110900d9000001042c2003400c080c1452400d0441a4062000940300d00442c0f0003442e0031301e0f60016042c40b03a01c921360000742c0014484448920012040e145d03038448640c240143c2c10104c100800140443c0403080d01c0c100300020710380c1e0207814095050315060300603c0d5809050303a6801e00f8107212400c00580e0303110b950141c4100700c0c0c03410302c0c00d00a440342c204a840200003504100302091040d5004400138107a9404400d0815150800c07046090f03150315034103100007460003400102d500707540d1400755076903500c40d442d20340090303e00600004040000c260403d540388101000702118502e101c0b00c3d114112511041039003201d42901030212500d110703e90000d0100300390940c05121a0b8680034800c01103078800d8007110881d500300000d0124440f610b200140142c2c0000415135108046a00401c0e801000d03140c11440a400c1048851510901c0c0d070040c080c190701a00400c0750249030030700388030f03041502402c0400604403401641c907103001c41d60240b2001c01c0310200c08a0b00c02c038004c8064488150344460213 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 975216106 1250 975214856 975214907
    0x3091002030d1418150c1804060e0703050106181e05031203190b0f09060111030c0312011e180906020f0d0f0507051602010504050d0638010c03 63
    0x403e40004016115006a240e000e210582c0d8401e000944a0400261400108071582d401c421782c4aa03410201e0b0180da400a00c0d200b80d2030940d61481010080d20007144801224204800014100d840580000050180040c2d403004c00d014454503000071140350706205440d034818003001d014010690390005801d4804d180340c3e0342c100c01145018602c107441d0141e482d03030042c503803410200680381020011900441c40e84004102401c01c1c1d00c88a50000040c14104941107820110902d15400492002d6440d080800d44a1811a0f49900741340180011140c0c0f000000508100046540c05441402a04c2c0102c0101429050207600700810590b080107045407100300701c4402207403d81c0000088190a45024152241c42d912440780c1e5004080d250340d42d1f4180b031660034a1141031158404141e060010074040025181d480c000480ca11501c2110041581c0313080c201030383c80d58503031980b4103180c0758000340000c02d60382c218480301510300209181800e205c40c42418151800f400c141c15240050f0b442100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 975217356 1250 975216106 975216131
    0x80f01120807081b0f03090a060e03030c060f10090e0c01230f0403020a210b0703060306050a0f0e06040503192c030d031104052b050703170a0203091002030d 69
    0xc03800c904d91000c509894a81c0c486401861322403081d001450760140c05110141700c3c492085603030034804040a803c4a2416400e08607007841c06000b102c801400d840c000301000015505d071604800207052481060100c1d41c07900c2403440e118000c02203900d0400101c4140c0504845200d103400001034400f4040076514210000e40d0005581715010a1707005c0d982400b800034002d07202110700d881a038845598020019203580c0c0702c41c82c02c0c2c0040c0c840010151108004400310344144503c0d03004190a00b0001480000090103c081d83c440f40f880320001d4110741d0400002c130f01c002c4126400504130100c1a112100c802c10152404010001e802c0208111b2096580140c962110401843c400807001c4850b0910013080460548a410041d14038240007480100003500b49402041420030103c044100d07411100820021181c000800556030f0313070720070303a010414087c1c9803000340e8136001d0b440c0040d40f40030100754010b9070340e2041111241c01003038016a6000a5031082c001e44000902e0074805012034040b050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 975218606 1250 975217356 975217387
    0xa0f050102011a060307031505031902030f06060d060903140301120606080610050603040611130315020a1b1506080d0801051008010510120c0519080f0112080708 71
    0x1455000d9881c024a603d11041c2c0c0f0554444a010010422890b50f07440500c100d000d0124644000803210010001081e265801d02442d03440345018410340503d001680101803501031068140d1403e41c000009000858139030381e8100c420950030010100f141d0250349401c8038260281d0402d0491040084004201d000d5196404000280104828040c0945940318161560740c262031680c03d030319040c00108000d04061010310307807040c05983c0001785142c00703217001c14040e40008030041080c01c00c108144200140c6c10500750b8113001c20b10f0114140350059401510369006c0603818200c90f24001801c0342007101c074204060030011808010b00406d43c1c0e0346512070ba28803101c961813002c1307071514002086a0812008000c0d01400b42e0751844038036443c1c0300601c4880d03140380070440c04002c4040724006100e601c83c014448a07c00036614a540c419004403000110518407001000708400e881c00d2201034041241c215040d101c0d251030412002c11036142c051011702c40e06900900604010561202d0866500d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 975219856 1250 975218606 975218609
    0xd03020705010b030606130c020f01090c06020d020c0f0d150e010b042007060e030d020a020604030f2d050c0a1b081c1d04050a0b0109050a230f0a0f 65
    0x280001c1c440d043c640010107440e050111456a001650283c16407010181c5400404403c8614019100c00310b903d001d01e1425241140400d0720b141c0c8041e1410811143c0c10051000300b0025407000c5c0c408807803101e000469aa5280810522440340e41d004e9109000900c840102d08420710b0314100b1043c151100705c5806815540d041d076115901d00514011000700668042c80d606119281080c5403c400707645400041c81100f206105600c814030104035100c03058801041180d02da50004c0585103000d20707004181c007011130182420400c0000c5114055500d94a80e081e801c26585580891641208012602c03030242030818403062003510510014401220b04a028035200d4105406001e41c8403446242e40e0861003511219034900c2807207600100d03120350080d8001141c0c003510002c11111000016013a190140c91069030650b031152141002c0d070300300784e40e84010300c025288220254641000c140184480c14400c01c0b80e00050290240c01d41c0e03400303c640100110050038101455120300c00f816100c00607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 975221106 1250 975219856 975219863
    0xc1327050a051f0501201f151703070311031e090f010e0303030a1107060903020c09010515040b0f09030109080c0f0a110f01120507020a021305040b040b13050d030207 73
    0x140f0320b401c15100d07032004201064a5040c0c440d50041c11a0302c8441d400c0c84240240002e0034024101c502460009152031200106240340004c01c060043d4000c00c0f0190b000d075481a12690301d040b5062044440c04410f9582c0540c04d410310824a4500805240c1035200d1003403424000d51310003401e0002484424058044204261440b003840c605081c01500c41407c00a20903605034810700008410031413541148103410114203056003003015640e91141584c20000d421005a00500e400359120b040c40c00c0014010141168480440018496039541600c210700900d400c480b000180341e030340c1d036802078110f4034a003001400030040300e1070500340ba0400383c000d03d008030b07403a00901c2209129200b0001d40c00d04000c0e041904644840c3e0180104030a5044900302e0505114207846c004042c0c0707032030303109451055040381c0250138070010358810814003605020404c0c50f02c51500041c00003048203408229400356000b120203010342c8652124400c4941d95140092046c418201c80405166260b009802407030300c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 975222356 1250 975221106 975221131
    0x6060b1c060803031e040c050d12031b0f11031c06050102070603060f0b0304141c090503072102181017060712050a0605120c090c1327050a05 62
    0x12501c40b015140e1000b80c82c55039000d070740c0300044811040895040780d00240306031050350b0301550f200d02280304c41d0f81c45001902c2803800c110034440d4054040c0690f0f10b400b6001c000503034585a040202030000e0b95070b81742d40c801700a0348600111a4140400803548c005107503907400b4881032686c2d4411400b4203c14060140140980c650018005000e802494142d5445502440813039040c10013000141e00020b1041d55800e641c0102c00303443c1c88042c8103658500240000b916501155190050a5134180e0340c05940242c0c0483d80c2080740c035039907002d0341c3c18039503000c440748511100358000514140f901c4001c2aa248030a5400e005e00584010030510480e200705041607501503841e010795485420407640c08010501510300a849515030b94842e03903012001d0100011996280c0010981081d0459044200c692003807200904c0307841c0c60f04440750300c200d010302468584245070301d0aa01c0c4418500c580c2164482c50b0128000003092104194001ca078008410080e9140a5805001400003500e0303d048008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 975223606 1250 975222356 975222359
    0x6091b4b090f0b0a062109140705010e0f012a0c0605030720031c110c010f14090a121e0f1130090411030429010b0706060b1c06 56
    0x130b00544103c1241c800761200e0b211035401c0841d400717500700b1401c010348010b0b650300d400ca4001084134440040c8441c50000404400342820005400c005218009521900021a11074113913a03000d00c004159102c2d0a02e103070740001c0c41c9810a4202d0f80c03d100b0003490f07003c100c140451002d40c0072006d144162905d41d211089548080c101c05100d8000b0700b00100e240d0410011020705985c003408949440c0d50042c8005914514003403c40b280d50017640744249941d44445005030380c0d00700c5008082c000042060103110b01d083c5035040c250350303000fa99401401031180741034800e0344500681c0d0482c2c48000d0190520340c06152400002c0000c1802c5040e40c0c0815003a0a5003100c1d9180041c3c41d1003040c1202d18000150100c41d00e001e940c100d14110850f0598808201000264856000c0c4800050500f20b40586034245480c29003945415507181009200c0f001c0d283d10000d40ca07540c5003604494221480c240e945506041c420003030400c81e00607007500f100000312081700c0308660041445504100008000c0705 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 975224856 1250 975223606 975223609
    0x70806010912060218042318060f1b030a2c030f0904060902040303022d0c010f050910110d0806100e010c06091b4b090f0b 54
    0x100c5a4000c400420a40b0040840000c1040e8024824a40c1700041c00c0900351442d4001801e1310194550400101d100310700741d42120b80d10001755601f01190400045071089100c48095482000401c802041c0d8200300200b000c090039610750480320352511241c2650b03450b12207000b101412135403a903041c906c00b48a0040407a0305002120521001210024601d000c0d80311107000015080711160039030080c4d58001c00100c1e40c3d103910040000354403a4024105000007048541e8080c580d00d0f6070220280a00869015503100c041824240c1e94024200b80000c6d21280d88115030b20f00417886526001000080418600c5801041e80000207500728119100d04041c00c07802c50394a4000d4030129003044174400c2c0172400398002e2982c0c0a041d04189010100d8484a4458030306842050505944da0207a05203d80c21101b014907036140030748070034201c1c1d23031070440303000c100548020710380004020240c61292070040c00d00c0903510b0b01d07032045090007440c0c2c051a210064040104065500910030354500000103809 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 975226106 1250 975224856 975224867
    0x908040510030b0a030b0702070b1c06050a060f030507050c06040b0a0b0f0d080918181501080a11150a1701060207030209040f06110d020703171306110c0d0807080601 73
    0x841c3c40075151040081c616a0383e1450010064030050039401005004681c0aa00001420070594110f0655960820422015003160b4030798006074004c1d02c0d030030f60078020f03180c0001d0525424120303454001030310ba44e181380460f014081c1803c00a958041e41b41403005101c420100f050082c9180e1104010300d55540040001211441606c070342c2050720100400c01282100d4040c0424520207000c100c808020b82145580a81c03045030032014051540504039201d00d02084a194180f007100c580128950428900968400d0000b0b402080e01a2944102209450b41d6044201842028688907281d1400d03c2000c0d0140075030841000e403013201c1d0700c000101d05100040d1802101c0d0090315000300d54646448402a034440c0c1c2c00c1c2a03400f162507550400020748104020440c1000803100180ca501c01072400400342c1101c85032105d5250a48801e11100e004500386030b02c216a4826800102d04c0790024182c42c05014042d41d000300c030b0050f00d500e840203c1d00041c0d4030744244540c3d983c04c8a16038602005454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 975227356 1250 975226106 975226121
    0x3010902120303311515030f11030a0b060f0d150f1a010e011103071a040b07032c0a0b01090603020901210818030d180806041a06060706090804051003 66
    0x3c0e6204986014004940504405410b0030420880400c484206d18441d20700032201e54012105092010303008030501611482c49040c048003200075040601541e03d98100420001c4c140c20711840c07100c020a00241e0320041035070542d42d0700074224664101883e604400502c0724240c060000c50034610306d40e080340b81d034240e104a42c5605031030f208a00030a140c0115090200c0131600b14140c0f104224130008242d80042a500c02c0c100c44041140760b1621b40750100c81820007030a88400d00d07061050184404e010041401d0101c4c40740304190b01d41c0020300842c03a107042103644010340003541c1100007207a50141038105a080d24003c0e281005580d82e203601c0507600c41c1e90400c0350b1004101801c82440004c650000070040c8040c103005000170070203c880002c1c1001c4155032910081500d80480c080060031035110b0200921300072000d0034181c603064a40d0165409a5840c11940c41c80150000b5201d58402083c1c40d42c464100c0c070108030103106407602c0c02c0c2c160301a01501c1e1080c801d0000e0041050700c40d018448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 975228606 1250 975227356 975227431
    0x3040501030b150706051f08010506100c030c080309072102030d02030f040e0a0219020a140d020604022103030106030204031e030e0409050f0307050102070c060e03120903010902120303 81
    0x745402d95a031108801880c0283c0000b840f580d011225410f1407d14410a8000d05504c038000100780c1001c8041150b40708000070f07005d0620502110034004290041010000c02c3d8010302030541d2a03941c1001b8a003004010f80000e0624006d005040243c1c002050500c4e016174820b40c03c81d800c130f642813601a139036800340d056483c0600b007040100f44000c0901c01c0019411151441c805810200c5443e0f4031110042441400001030740031030b540c10203020034201001d507043e1001000e0005080841402522000020000784c00f07848501103071103490240e204851841c1602400341c90301c3e540c441c1c1000b0080d42c89031000b515074035080d050b07107011400010b02c00d4a0540e4140c540455600d02c0304140409810b1212080d10140035004618144a0041c03005040151007400010ba880c0d42034607109082222542100707040080d15000030020361030004011070100b54250310242c640680200081c0504201e11000750006031280d185001d08200202450080310a01d0b000b0280d1044d03510005150086143c0e002e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 975229856 1250 975228606 975228649
    0x22081501060f030207020409080a1713170c0703080403150203010506040303110f10060e3601110a09150c020616080f0315090705190f0203070c0803040501030b 70
    0x1001198000e06a802036050b4908000d42444883d800003030480306040c0050390f0814000541b03151a0307500c010b40c021168421044105c80d03090520311017085d5204402c0c02804003030301082011424042106030b4901152040c1160b204a07101d01e01203005802031300c0211100030050100401710096402500c0c1601d00c0504214101461920210744007820451481054040d01c00901c903007400030321010303074840340d0b480e03000c100e6510b00407040210403001840b81185000010140580b086015070200180c1c0c44602101b2845a00070308031401041100fa500400310800607401106035007080c030090455011441078030002c24040d0003601d0a56810138000e40c0104200f00c4502550301c2d1107a5244620b0107420a0390500c440d82d0740400b00759206485920090b541c50320704078604d1800b004041d0f4004607a2610604100803000b4041040c0d84018540003407088403408200424800c0013603801d0560841034422050f41d030340301d07540d403a84d01500840c3c3c0041d061200c4a221410001c0c54034043c5869010708 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 975231106 1250 975229856 975229859
    0xd08070e2211040f0915030b1807030b0a060e040b01030615080303011e1d01290723030a12051f0923010302031f1122081501 55
    0x208074401a40450210040c840c02a5400c50054540b04648900342c503107801940c1c807410214888034801455003c21611402d00b14440007140c0500c0d502c0d412603a024962070303401e0300c51003448060a10800c07480b2030344c3d204080c400001d0110b0721600038011003000c1404c21145840f88881d40030300070200e0703001d0500300c183c000400c0043c0040d803140301c200c002290354018aa403152509411a4000e0340000c100712a59051607440ca003105240000405084291070600c400c0c4007013410b035013907051065441d810340304040076034a5070170f400c400160b202032103800c1665001c41c0d1400300000ca240c0075416413070782070b6038014100d403600010807600c8408842e150101c075000c07040d0808010701001840c1a00700c1070501060001c4420605803d006000102c1000c608106c14040003421041e12a10640104400c0001040541c5003c1000704100580c051201c6400b03e9000d8508084c18010908a011002c0003612307a0000700c003204160b12011603850b00162450342d400e401640e50540d0381524a0207a0b08500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 975232356 1250 975231106 975231109
    0x1180e0403080402011b0b01050306012403020c0a02100c06050645010b22030f02092703040513020a020d0f0224010e07090e16090909050c030d08070e 66
    0x1042c41d4840d10500d00000d20921490135082426406d4a040390014100700043c040f600c2c0c28800b19025007180010055100801344400c03190012070506001850303400103007a0450b0b5014010040d8803a0017800100e81c9101c07204004080200d40c0f242a1030241c40d00c4042a240e1500b00060107140382d00b520392101d034110032400d038019030f1144400018855070b004294280402c1004025009003101c10610742c98080702084840040100b62807510420300140c02400001c0b00c0e000348403100381d0141e4401240b40d9400070304012014807200400c00600c8804012071084000100800a858007928085408024094850181e01030010b036900581c2207a002108494880c050041404180c1d00c1201c04c002100e00b1109540f19254441000003440d06006100e0030286a03003c58000c6854640304c40182d00d00040c140003001c01601c042c440b40f03041e403c01a4054821500f000240c000d05204104206442c6086a6240c0301d80e40c1d050b00038014102d070150000e015041d401d2280030a601d640048021210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 975233606 1250 975232356 975232367
    0x5090601180503061314062a1c0c020c0f060409050c1c060504050708070207060809010204080f06040b2406091315030b0a0e191a130201180e0403 64
    0x8851202218078103800094540d01002514080c00d074410003c5040161424801c40c5210b0603000d80000d40d000105110101c00c0e040d000d011031840e1007540e501400d48044010702c1511400d020030241044007408410540015403003031400e0100354089030184c14880c0148004540c5c403500d440da00403070610041000032542d802c425480f1040c2d46d485c0b4940001400300720980d04052141814295643d079041c0300034286880b03807a422000c103081004141c6450722000f036a8903c3c0f400f80404010942000c520820000d406540c085c10804094503018032002c0c1000e6510b01085031b0642c0c0101c010004248801c45007080c0c1c01400850240c1040048042d9050001780d90165030720079040b80082c1803004920410b0b10070f0482d04900c3d04081c068591950411314a0600c02400d0320107032500e041402c032804280040e4104500406d910048840c03801d03410101030004550488501c001030781c03010050398003000606116024402d1300c0390389080c020030f0700300d2a50007058041d51070301012540104000c00e0145 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 975234856 1250 975233606 975233627
    0x639070e040210020307020a0b040504050606070b13050c030307030206250c03050c10050f0a0b0f06161e050303010611011e0213050a180e010e0c12030408070b07030f020705090601 79
    0x41c0110f074134051b51759000c01c89541c0b00d40d210014041d0089014001460207000301604030004940c1282042c0307541e20b0308180e2101c007600700c8a1010440012004000050100602a05000f41603985800071820041c1d200d20003101d00e103640b01c102d06d162550364a00750b10803030a411403641e5821168041550709171250760201e00900990b200d50302181c40c80710104e0045c0c501ca0b00c040700461240b42095845441512403541d9114403441042c403580940d9107414042c0c0303529040c0040b01e03004a00740d9040c4902c155002e401c0030640307450711286a0080c00030000041d4103c51055480174540c4040c00941422114140c003040787c8414101c40d40d4412252680240200304000d401099403250b44500181009500e0341c01000428244030b40841c00c1c6106124108004003c03000070b00c0080e07405800180c44110390b41240d0710070700d1164003008440d4010010365010b042c00808032541291900c0032100c0c1c03070700040340c114000707103343d4480d420140c40455405c040f1030001e448017480d030310341a006607010501c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 975236106 1250 975234856 975234889
    0x50c010e0109030e010206060102150c180907032703170c0c0706030c090522020c150907180e150604020706021c0e0d08150639070e0402 60
    0x3a4102002042030a1041666080c031039141c4000c03454141001a06002c40184050305640002c06202d0072a100c01c8155580103009074101556840402d1146030041c44030440d20ba0403030741c440308000016402d5441000341903107100c1003d912f1722207c01055045040c440006001603200328440c06803801107086a600241c07150500ca0514041304001d6241c8011076110070000380d213a40c000e0004980000224015060a07a8001403103490b0001d8401c3c200d40c2e40900310310440c0e00182d09022107005101480500c020442042820b00780810401d0342e4a4007070083c0c1b00f0100c4062038600800106102e690190b02080f4007400704454a107040107440e03000140300980180c3c08015140000d1749602c01004d100744050084100840d0180b1000c04644d500e6503000d80c6540000da4003079421340c10510481d4000c6141032854141222079000c942c281c040e4042140110a02c2c01c400101c200f100500b06e0741c1c034000038102901d9000d002d0021541c60b4854031a210388181e260340820054104140150a141c90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 975237356 1250 975236106 975236111
    0x80a08100b030a091403040b04051201200a030b04020a020a0f0309080a050105090606010203130905280902031606140304020a0b1606140705091e030d050c191101050c01 74
    0x2954401110707540d00488034000c1c1d4590b229403080130400c003000c400d50155591801941801d05203204290544a04e02420388544840030718220b03020800d40061a4987c005d00000600d41969000b00740b50760022121603004c24103119490400d41403510982d0592240c660040a95803e45e0301d980c0034003503034600150101b01411a021070000c004100802c1c50610a03400020301d49001c01e50309041c018041c0100341150000c07c80d4010580660082d1015a4247c0d440001c03562503400d0038195a81513903103208104c00d000524800028555445404240c2c020350940e00d8510003c00ba5180d800c443d03000d100c01007094145803200d14001d001c040c541c042e201a040000584d02c0754120700840e080010302200c40500c52000004105850054020103807155004c00c041341011a0040d20300e02a00424a00409451403001d4240c00071403001c000f140405000d5606902000c0d100400d1980b101000c2c46943c82514410b00d03c0c01c03da010b40c0364a65402c03500407084003018000440380c1d0391182100c55003030364 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 975238606 1250 975237356 975237359
    0xf05031f0305060903040f0f0e0c0a0318080c0d0c02030607030903030b0d0b01061b0302030f09010c0b150f03120306040203040309080616140a09171006030b0603070f03080a0810 78
    0xb00c08200107801104504000c40c2c44034a0032910610107492030300310076940240b0440c100010400c0059054100810031a030984a40038460101c1c0203018400990717540c02100c0000500f4040704d80c00802030040b1b28002c3d0391401e50700b8103040d118001c3c10a40250950700000000380d0492084d40f010b0031003442894080b030300802860001d081c1c280c5d8035000b542d11030400300040009a400450300c104041c07155008081507021504d01a407a80100c10010302d4041c80022801000c1c0e00c1408030f108070650201941416040540342e011a040c00c0d03a06c0240505030600c120400d501d000109240d2421030610040d2a654030b05003484040d401c058000c03400d02001400c08940c02c04188070b0307030b031051050410844c070200c43e0079002040d04c1c1740c0e40680b500c020003c10050751819480b1081304141c443da50320581200002d01c40d4a442e184042d816134030300d11318082021041001c40e2114601545048080b110b025031100e4881e0074140c1c0501c00200fa0540030002e070302d501400b8000041c4c1c0f00b0048200c542481e03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 975239856 1250 975238606 975238613
    0xc01020d020f1308060c04030b04150f05160905132313031b03080f0718060e04150f1e170d171b0715060f030b070f05031f03 55
    0x280c00604101c0b00050021659414140020b00302200900d0307140010300e02410304460103015442940006062841984000303810f1105203e201044c03240c0c03000003000342c2458200808002c0c40309132562003446219611800ca4207204649010135110000c007401850f0b4000c10040c0002d291440c5201c0c079a20b40c02280b003001424610705640f045040301419900300c0b0381d0345001131207421083c000c030032800c0198000c0b6003c01e501018080e8000044441c081d800d48640070143d6a040f1191100c11010740c1c0d000010a589921421400300c1d184151000e11441460210b882031151031030007110101740300840c0800408a104502c2c0c5482003089080792031041d20b03040c000c02507009110115159601c007820000e10140c0c44404901d0305099018810150700f85040306202640e141d018400e150000880e80c1024043d00600d240410f14120000704241d60341e0b81c00504a95445100c2a9580c41545001668680c0143d191402e030301165600c0360310b07641e20348001b0360384561030111850400a07001c0002c40007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 975241106 1250 975239856 975239861
    0x6070818031c080a09140a0b130f02060a0e13061707030506220b0f010e100501020615041b0c121b03050a0309060c0e030c030708100b01110a0f1202030c0703080c01020d 74
    0x107070701c01b541c0a4a0b42c1c1065080c402600032014004056400101040c00d012030041040042c01e280d046810036500c4803010340484106d07a07039581c0e1a50000303403090a01000c1801740d005070304541024501c1d004425100210603250f0301e0602c000780264022a0014405e00d859810145110886148480280000791207a000700201151100020100080103201d80691140025405841002c50360107042c18200001c0d1295406408000c9a18000311404030359030f502e4002c0d44030612054690310510b00b070840700800c10f42d0102c0c0142c4101c00345040340b40300c06101e90030000045000c0c0c402c0508080c0b00c2e0350101c500b0760000542a0405d5a80e5280302d0001d03101c0e000d9040f400c50701d42ea4580d00400d5440405041442c1c10000a10139807052904005030800419110b00605108200080250700b0a006840510050030000203070300030401d41c1010080b00c00c104500c0640035804542c4407525058090f0794a1040d20b101c0c1010741d0000c40100000b4071250000c1404814940000d402c24828101079401d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 975242356 1250 975241106 975241133
    0x6121608010f0f150b03130512190c0c030308070504030b130507051009120804080d1119031e030608010e010e0c06070b0f040c0506070818031c080a09 66
    0xc1e944401000c1d4202050340100c01c010660098204002030440b08034101c1c0c1d440b1403040c00909840800016041410620ba001e0110380040c195044504030314404102030340314014240500b040ca00981800c64402d042c0c0c1e4818036844119081624150b84054542102c001e020f0820031004100c08400a080501642c1c007030401c2c2100c002810440349001d90415149401160103407880080e5001e03002c0e404080001160b4410f45c1210603034407030382040d51080c401d40c0c01032000303403252002c9041c0d65603000e08281400b0b5503100641d094890303403803202940c0f80900302c009000112a01c0c214000c8107180c4951102d09000e03401e0000340c041e600d910260a41d00c2d01014008165914240c0444508052009040b2110119419490400c10350748081c41858041c00358003204040c0750000d010010060385120140a0041c022516600c0e107241810f000e900034030448840d00708030450a007070340c1800903101207e042e88024801c205101c0c02000ca400d4500280b1521600d1340307d80000000c074010903107510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 975243606 1250 975242356 975242369
    0xf0a030e0307080c010e0d032705101509060905040812070915110f030405010c081804060b04090f05160f14040b0a020d0206011206050601050702040609020405030f03030c03061216 79
    0x2a02c0280007010324100000c04007e1002d06090180d985011700000100071240000501000c1d500340c0c43d800c25038580040020031041041c82d0804811007069119821f0044401d00d240602c07883c0d490b0b0410000b9141d007958014040201030204640e840000b088003a8401d0756403a01c8001c02e031381c0d0181042803101500040001c102c900b0b07100001200140b20a6034030081280007986401d14100009207150341140020340401030104014070514000683d100b20f200d0001e00600106886100401c156400780c4250401039281c201425421713500d030f000d1284505240d0b500c1003032031009503006448240010100da4108000e41ca940c000700000035015001400c0c0e40d5074029142c1e40c400f000a4071341106c04001c40103552200d4010400b412282c0504a00d856001401107041e03103d140059400d40240b06c0c00039403107800c0a001080300441079001d84102d8404030300b01c440002da84150151a84026500018034000401c00a9140e09014200d00f00070000c10048a401c458040f4021041c91043e41100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 975244856 1250 975243606 975243611
    0x6090f060b030d0206042102071a04051206070f1101020d330e011a0f0c0a0b10180e0304030206030f09060609011214011d010906050c0f0a030e0307080c01 68
    0x70705181020030402c0c400c0c84a80c0010511814a92501c210148080131200200b244c980f011500840c401d00400000704010028901980289440704659400c24024103010b0b000e21681440381d8400000c0280c02406140c48441c107030480042e04035941c900c5424800a01d42d0200007110034030f0068811403c2c40b490000103c0c002d500550b501c0c4450b56000c40c0400790840c2154024420341d6061030011b81112201d481040c1503580100d103442c8240a42135100e241b154021a000c52088004150142200c1c07003504951b101d0b0350ac128040e01e4141c0c0500661200ba10756688a183d00c000c0c40c0e000205a18000f0110b904113a41d0f54001360240e40101c44a400c80c000403414029180f00c20441141c000404031000c0b41c0d950306082042c461154441c00191002d228003040400c0503901b903002c40e0400049100e002e5411100750403c0d0b010340400c40d01152060314280000d080580b10a0680d008458004962894142c803034104070701926194004a0440c04200466000112110020716031308240d400007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 975246106 1250 975244856 975244871
    0x30b0a1d0613020307271a09010816140c07080d0507050607030c12050601030603140708071401020c06070c050a330503070c110d05031c020c070b0706090f06 69
    0x61120364000030a0307030b1140381e0050080c00b80c1d4540182c002c88140c941d50f082005000349058400101d03101aa1003220301c80710242480c3d6140640300d009210071502031703c440b00f0b03070384038480e0303050040d44d031180c2c13505c0002da807484020030f5442c4160040070f091101c1c6040fa01801e0711500320038100500e196112000c00c2e0000350000c1003000c1881055840b240c10309080103a448400c5019007852014103110550543da003001804a078020b82c444805550007940f00d0818400207418656640c00d14099141144500300001400c030302c1d64520300c042d850040e400350a003090081b0905c42560028032080355449110000401e07e500c0d5a20303604010700c1c0c02002c10b1030b410200c41c105202101c00000300c92851620205001002d0703040021030740c0100132843c0642401205003081e01e41c2c10b99076080c0c05e61108040c40c9010138400004054402c40702c01642c42400c019080c54410304902c03603001000300c150007004041141d4031104014110680c010080412685944c0e550209201070760b01c4101d4503669100360 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 975247356 1250 975246106 975246109
    0x120a06050901060f0f050310111b06090c030604021503071e120e0105040221030c100b030105010f08100506130e0a03080c0405090c0c01020c03040e0403021912030b0a1d06 75
    0x420014118004400d00140c240001f080e103c1200c0101008002c0c0c41d14140c00d030b4084483e0458440070b9042000b0902800c402c0d04494880209494141c0144100700201b03c0724940811030b00d021f10b90052548402070640791140a580e00010040380509c0070f9a120400c3d4078502c031800d42102d00305a035800d8400e014075400c110440e03207241240f19141e80b51204100c0141c0729582c2603012007410602c00701a20120390350941c90351040d826407070303214005c0002c000101d0107960040c1d030420703104a0003407289070b89901e0010024403882c482c101c4103034803d844500c082502607200755000040038010030005403034000d208007613800710340c20006154490404135042c1503000d01200d82110090309820724292808000030390301e00c1c01a0007050444c03800110790285080035070440340700b81c14070000e803511542d40d00c5403002a020100c0d4260058016511a03000c0c104544132011003d40d84484861074848900c5400c030700920040e8100c540244440d40301003100c4500d07507d084401c4114011070142c03880d0000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 975248606 1250 975247356 975247379
    0x5030a021201060f140a0f060e15211603050708071d270f0105030d12020d090507060f0807091511011b031d151003150b011805030606120a0605090106 66
    0x7e103d1045c4030b90200c000e02ca04c0d5440500c540441004982086110181c801c621004e40f149109a0004421101c0c640e003242c006070403100e1103010701c90501d01102c000c0c0c041c181c2c00d840c421141440040d0b08180003440107401030403903422030031402c50329070321051401c004201022124000d980031030000344241700010300d1440049074025442504038940303500d13120101c1c0e0381f2940900d0550900901a0a014402c0c0701603041c1c6515024807002880103100c07a080554a8603040d020b004000383c0e10000c00464207002d480070602a4803107035120300c1510314064844652000064800d410402c1d4031402e002e9201d0240500500c11034940603441100542d8203000d421100d4000300c1040c100300061034a0300c2c4500114000e0700e0040082c0b03802080d0350300c5424400350f1800359040204044821002003030044c0c1e00d984408900e480030b89030030242a10800307124090b14003512030709615038050400103015080c1801d00b034200031400b60840320031180d1540c07944240d400403100c1005036952030104020302e40c1c0d03e8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 975249856 1250 975248606 975248609
    0xc010204260a03230c06040f1203050f04061a18630c010e0906130c0e1816090305070b0a0c0203030c011d0705030a021201060f140a 58
    0x8030001e0100b200716035009810480096200c10216a041208900c90400c5604540307402403050180c0709585010b14016403030009901066071011600440807018900a1045d14051006440c00030016601d5903116005004103a40160b0900c02c0e01d00d499081c0c1c1c0b103c0c0202031890140c1141901a46055500750651814020001c460400a8100b82118618a042e00b04000030b1440c020141031984d844a0041202880d221400301698081100c03920b00d004100144802401d90362096220b2201003004107040381640c00075884121201c110440c1c0316076901c46079294080d42000110288948001900707000005950301207074007540304002508030f100348000c040008c5410a060756505580f50240d607001a405481409800010701090541c05000020000d55004048030342c4d44001c00d008038041c1c84048025070300e140540d14000c0d10f6600100b20300d01650009402010f4140c2513400700b0a03402e500d002c0301140795580d1400880e01074211020400980740c5200600d8180c18401d0500c21070320031b00e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 975251106 1250 975249856 975249929
    0x11e08011a040b2b030e030a03230a1209020411040f051c1e020609060a180504180215040905010b03071418010e011119142d01020c010204 61
    0xa08030b00c03800080e110b4103000b1821a500503100c149010910341615202d0500181d40c1d4140704080348e0340105980610b44050345030202c1c1c0c0301c07000040311001c90b0055000302c01c03c14011030011040c0c24a101c59603402400da8031300007800403a0b01404140103803480c0d03100ba0003160071f0035040503090215041c001010315105003c20120750340d60215841d0012442c035400821560100c003610301c8029582d40405881c20301d17000900040e6640103d010140182d040c42e0304411402142e00000074040c030f0148200300120341c60b00c403040b4480310741e5400c00a5101045103454a148801d100204904030345200fa54060f011490710303180e032810101c10162021610b038070310400c00380e8200711003021580103071119800d0710002e081ca010410701d481c0c0182d41c0c3c0391402d00c1b014400d101c0c0055401288103d2450050f0681c0109000e049003040d40700c10b26151031180c1c6042e0824170400040c0f80e28000050600254041400001820120b03091105800eaa12562040300e2902c0000d80f00740c03c20002e20034080f411400f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 975252356 1250 975251106 975251119
    0x503150705040e090709020a080a050f0622060f060206061806100f020c040e061e01150806060c01021303062406030c0c29071106011e08011a040b 64
    0x6003044001d14074410b0740500c00d0040d50b01004104284000c0110602424042c80b055445400068000380ba001d003c94004541b80d00340408547c0600b040c0e040e29014940c007500c1481c0c0c1c043d02d49503480c06002240001800e003a698040051000b0740b002081000e00301681c007404080c180401041100103210307082518411150003800902d0f27031116202c404980c01c0707080ca410780d0f09420000740d007800380540c001c54219040c440d215180610114080d80b05940104031075042288038018a03a50307642c02d0040303030600410301a5091841e80582c0c40c039907204800420041c50801041c0c1c0c450700360b8214140012124289010504c100304403070068026212621180443c01091810600c10385810317407081000341aa1014520001071140480e4407805400500b01042004c004448229140a07000c50103640341071038020580151085c5001c0d01c03440070520081800f40d082c1a006100e00107005d051034903400780003800045c0b0f030b4000c0c0944030f02c1c1c3c100c0321162848001c440b014001680c440800c59840303000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 975253606 1250 975252356 975252361
    0x30901060e15091506120106020d050f030a050c090d060b040b0612071413120b0703020c071802040321110105060a03060e0a0501140a0b0a050105030c0a021c09050315 73
    0x2070109680b903440480c11100840142c45500759104142c1d8043e2546070015000115420341c5000321807030904031400c66003120000910000c0440e000d009a02c8071000e990300400115030b400607583c2010f03402c036014000712498000c100000806018204008541031a281d42210b41c0c54940351103108400001901c1d282c3ca441c0c00c0180603c6209030051013a030900c07000301001040c002c0c1c40001c0d41e1401900444120042da01e07042100c1c00d81003400001c64840c4140000505010b209000741c441c4000444008d01d08c0b1810015954040d1904020f42654164240b2000000c039014007680524503020702003401c8000c1c85200300402e11100880307181e000d42e04010034040c2c0360b1a0307440b943c000c40b41c001400041034040200d0060900401c00d0000d4115801d2085d04044505500d88480c01400540002c2100b9030412081c40108945480340c1070114031306000181034420078200904c0a01c03500c0c81910809400d280e2009103254102c01d107035000400c00389060002d42420400c041114041030007146052 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 975254856 1250 975253606 975253621
    0xe160e0c0702130507090b0f0715110a110c130e2506030e0c06030a0b0a090b0603070e040b030d0f0906050c0c041509140a061205060c03091501030503030901060e 71
    0x100300f05160448031903561000440c1280314004c00c9001d018400d084554415480845031550f8002e040191192110b452091420381004c1c824281c3d19101117001c141008130135041a900626550b510002c01c0c003c0d810f403403146554070021034000344881c801c001354200b02207041b0b9191181500c1c15502c80e681126000c017030701040c9642903080340c0c080c0c94003260f0300d4030190303030b180c1006611500c541d0031020102c00c0c00164041c51b000104410000d60300071402541d24850901507a25003403100d60054820004650350a124541d240301494010b0000b14601042201280c40c0400c84003075607000800000da84000f0941c020486001807200e8074290741450f030101003050b101c454140465100340c0e41c485400c03400c40350400d400c0005022400bc01c00040c045803004090382001161401c84803482e0820114610700b400070725070591500034004014942d2a03800000b46640090185640e500ca041c500000060104c146107018502c05c1019503221300b031031703486d807801e482644d000207011504200400c0108c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 975256106 1250 975254856 975254869
    0x12060405041a1003062307020a1e030309140a050d0c0c050906010309080d1509020c030912010f1d0d0e06070b0a27151505060903010e160e0c0702 64
    0x402c01c50300c5081d940c0e41c50701100398400c142035500c003c0845040845002d60700455040b141c81300a46007440d01e070a0f03a100c600490310f40848400040c10340c0901c2c0da19503842140c148035000d4440c860708001400026545501d004801025004211303603100d1031054040000600001101080a080c0301e000c81c078250713442c1907243c0014001c1d14018100a8002032090307210307800a03c1d800c1d4108500c1035541096600700c20240100001c583d00c0710166a100184507122842107516005032a0b0146003010900030422403441c510320803100c2d940d0748409604071200e01c1d070712070910410410310507100030b6221300351800e007401483c6041d8800c8c0100000300c040191210011514156030082814003940d442444101c010b020980c29005078a900c29400b40881c00c03050806120f0034010300310310301400303c08021507081d0760303c100bc80d0032b4500a502d0200800c3c188503000d0101d8401c000c0001c1035500c51213540346c3c6807841c4000e41c6640001c0c1a8010408000194036440e0003511540e50245804215000305a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 975257356 1250 975256106 975256133
    0x9090d050c01021231120c051f020414060a0f1419090e18070b0d090209070e0a12020907050c150405070f050103051501080903040b0f1206040504 64
    0x5006000072100002042941150040083d041207070601d410304c0601c000c00e100c13410080409245520103103060f1141c401c074200a03c164080c59038240a80c18840c01ca6130030905034011900b501c02d04204034280c4420f243d0012440c400c020005880f240742a08104c0343e441915000c81c001d1604120880845610011010301c0b51800e007400c20049101c0a51034889101d20500360707604015250003041c0690b44040e10a08562107641448450740b50b0341300029404102c02d405024542c05801c0410083c0320b00c00c041c100c07084201d00001060b0005402144540e20201c800c200010864000d040b95860070012070340160043c1040c041800e25180d000c10310b1402c014200c43c0a11401040c040344000c810052203840d81401b12100d507060405150a598448482c0192094103007200804100307548070744601413040340a80100c5261b20800c0300151068a405040c100e1203001c1004049010b07440c0e00001c10f80711410310f500f2943d0740b071000d007541088107000d02201c5c4194141000c3c400861440c00c0c2062 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 975258606 1250 975257356 975257383
    0x1a06030408070f14011e1b0e03030409050c04170f060606030c3009010e0a0602030925080c0103020f1c1e1b092301030204181a0909 58
    0x90361038049081503c240c56150a000700340e8000070040040c410410b401c401641195103428116801d04012400f00b55001c1090510110300c0c044089070038188030300725801007030130041c2c00e891600b034456408006039017040300d030b805040b000090108024a59407000c070f0380c0303159084050070514168400d10798403008060800c0d8414a000310204954041c032400316402003c52450382e00f42961041c84040c42c002c0b24031b41103040144000c0006052480600881809007400c00c040d01948625039504002500040d2110a061142c100d100340040b1506c00c200e0684212003c0e801d4451340b602100703618040c0f410900c5410907006001e41d8614002d4001541c100b4a003404100620701d5564003010000d291001d021442d03022121030440301115158001e20424100c41e1400c0310540d04004161142d0342d140c4626a003a09001e02101d065030100c0000410b6078205140161515130740f080038104c0c41102e070b10240304540d540d80c09103000c245002e10440700410182d41003940392500e4000e8a49803c144208035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 975259856 1250 975258606 975258623
    0x122d050c0d0504050709060603050a1b090303200d02031c0209060403030c0203010f02030a0902040b090c03041e12080106031a150a020c04060803093a02060705150a1a060304 76
    0xf82040014803903000035000d02242001001d1351460700402404040c0d6086511510308442154186071043c982c103424501d9032918401240395540c1100d40d842510111000d220050080d20b010600034020301e121244d4543c0215141e00b03040c111109030408540000d14030758410001450152104020742d422240c15040c03c1103031440c82d0000c01d026001c18039148284510000401a4209441e4083c0c8005130003a00c040004000020174001d443e00d0070380b5403000301074042c0001400580d0540403142d0218814400f00041d0429544004080c252104014042022100103103d011fa0500c40d0080402089510758441d2858802141030030441d40d600981d0080001043c1c070001d80200019030903050003410070040b0f90342e1801d03819201c4d000700000c1d42c841e24504020802403410300c7c0c0850f4064800f800421000781e00b44112010080b44d041d000c81c1c000b40140003030004120180410f0310b03520f545c11488100c3d441d01c40c0d8030200701d803041689001c0c0c2d1280c1000d01080c41c1c580c08140c1340e0113507018101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 975261106 1250 975259856 975259861
    0x60a0221090f0616031103011412242d0402040507030209121015031e020d060504050c0f1212090303090a0602010b150c1b01122d050c0d05 61
    0x40c1c50a11038441c0300d0b0714052082c0401d020025118a40b5203000703c0e06590100000e2421410050142c402842480d40c0c02c1e001e00a110303054500314451205d004111f004a80d05003003040c1e205c420303040c0308042e07030708103c8104d0040040c0e18800010101c56510108401d03400e0401211581200070320240c4083d008940d80c40010b0a064002d504507800190004d18102a00081902841d52100a020003540c01c6003011070307600160030320204c0c810a5903440040c500407084c80826040c00c903006078005907448440181440c000c102c01c1e00c100c0c2d00640c082c0014015000c0d40409000e585407070ba94803940070f4040944400c1c9031f80ea010419190070714003e1002c0350740d0b018000c0020f01d940100d1091a501c540050000910150154000e1100f9441036484098840c0c0311074110107140640c045800050700510250b1203a0310f0b00d4543c0800107841410001041c0e90200c045c0000c5521020b00c2400000421b884120316400640b41c050640c040403e050040749403580750314420340500d400e18079119032204003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 975262356 1250 975261106 975261121
    0x3070e06090d050307020a0603020901020a030f0314010603140903191d09250309150b0d0605090109170307090e0903040e25020115230a0303050a02060a0221 69
    0x22682a4070700200211403001c1e56043c83ca0303c0c1c1e030241000b01e100300d401c210006041406802561175021058001d00417001c03041d03c1c01d980403004c0c034100e40c04040e6540700070000d0381c403450300107800f901041d0350024107040103900c10884040007030310302080c581c0244100d008003a07003d2040c03035000b5071074a000354041901800103282000030942c96940640c008003000f002159003000c10710078403c1c1c1000212000d07a000c005400702d4215800190101596104c494081d01441d00500700500000e0300c86001a4040d0b20760508940342a2152640c0343d4480a4000c1803040304e10000d07110078040c0080c0780c030314100a00041d1480340c051154004102c40200010103e410134030954005141c0c610301e80c101031410f4040440d81081900341c40d1308240f400c0d000503c0c00c5205126411140c600310045801c00360030190050701210607124000b444501c00d249001d00781d1145003103c00114030035112a6140c5040d64806030806070010706100b441c80c0706101820144012000d0b0380001c060364203218855403510708 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 975263606 1250 975262356 975262369
    0x40b0301090807060c0f0f090512150709050406050103140105120a052407050c0601170a0510020c191509020d0f033f0c18030c031a0105010503070e 65
    0x19015100c2071003c1500401c0c403686420400b0900103540d110201515015020f9a007a16a080d2200004003981d00034807e50070012154041c00e40007000301c0702d042e40080c440004d041402c40c1c4480008004020810a90a09000e180c02400007400d050007110000441c44001c0201446090b01c00c040721000d400714002c05002401c94646c0043c2542c40e00544100d20310542804a011702043c003020030f000503034252248080e0b4812260032000381810340d1038000c81d200b000d0161113200b43d0b2405041c4003000000c60410007803d51216142d4096100c008142d40c0505003002505103040e2101496160b0000414501c08200d51012021002850324440c1c000305030140e00201c00242000318001c0742e40141600035240103840142c6406180e007444044041d0701ca107242c81c0c0c25405140242040604100c0040c1e080b45a0040c85841c00c12512054504180601c045561050b1610f8000c601c0c10700c14020710118003040f100e600000c410380e0b5490480000c1c11840000c0601080000c0300070010059903d0a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 975264856 1250 975263606 975263621
    0x903030b060409020c060a1a01031a0a17060f041e0f020402030f0f0603030a1b151508010608071202041e0507090e130c17030421060c09080606040b0301 67
    0x203041c10751075030f0f2a003600708000c0d880648425107503c50140000e19451040c010480440d05240c1e00c8015a48220f006402400182c040300c4030243e030380c02c051240c64640d15030034001407202880d482d440442c030007803003410004060605004441da00c42000003144010b04c4071070001d441901d61100d00c0138141042d150084403518000c0d0f20a00010500641060002080d80031703c040703134000100e6807184020035940e482071182d4180882c203180f4104002d40b9205180740303100c500840f00468150190903100c41100c8a000098505d040030500510002900b440340001034100300000301505810511052804156028028400d5803100c804000c041941501c000032400c80740c8091003241054100500000c03031030700550b0144c0d000c074000940310104080e50b01190941010703c1408090030403240c01ca034800718003502921440108000030384104040d4203c0303c48810001c4029090040c0e160030000c0d0782d402004141001800348003840111030105515401110072140021101a11008a40507000c038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 975266106 1250 975264856 975264859
    0x6080a0f06030305070501050a29010e0d06050f13020604091107061b020c0108010308040603092306100909120e0a09060312180e0106082e0611031c0903030b 69
    0x1803500002c10180c02c00058140f4a11805c020b00c40c2da6a00c001845c221081200c2803100790040c4041d0000501c080307180b0028000c010b14103014030300d501d42c000c95440038400400301d6031150b17240c3c01c221200b4000400c098109481c81c0880702c0c030340c529400007082405280151a0903550720b070040510288140103d80c1ea1640c010740c140701048a1403050040c03110541c41600c05801080400341c06588103a032180d068aa016000504040c20a00308400078010517108417801020103101110f200100604001c88a88140c020102031a00f042034503201c40c0079a00c440b1686082284000c001820400c0946005000c1d1131b01c50340e03c14034640003400a114551101c0034540c6090710100c28444040460021000c0544030540c60a1501c0ca40900000c0c1d103116000b1401000f0f0f005100280c49804019088940c140c0c40030310070010201441854001d02c405034820f000310400800c011178104881540f000b40030005941000814401c00c103540384040b0200c0c0ca00d595562610701018001d41c40a011201c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 975267356 1250 975266106 975266111
    0xb0303031b180d0b040302070f0305030f09030115030b0403020714030c040902150c01050a0b0d030c080a05120a0b150c15131e03110615041a130b120a020a06080a0f 72
    0x60f41c00d080030040b03070aa4041c0e0050181240104a02042d0070310300d002c880d8080c008610b804c00e041c81d0200d8a80110398103c0d03044d501e0b003045a2000e1100703030701107015501a2094592500707041c64080d02d04260f42d48058050717030840d9080a0281d0f80810060708804013510082160384003440081c00072000051040e048000100d06440c031703202c0540c400780c4a80740c0d4003020003940018004000c80c0303000d112801030001c0c003c9030030800040d00300c001400600301c0c1c0341081c600300740844d9103175601400101c03001c1640f5540c51110482d245054550822895200c12019140800e42801d050700d54141e41c2c1d08100024000c00420705100400c2c2c03d109425401034103c401c140901642c000c0348002d004000e800150300b007903408500c2d41020440f1402001e0f40f0242e1141468542c05010103851451100602a2121103402c2c4d420f8071403c0c04e140501c40300e1040010075081c0360041000d98404042d020310558005054400181c4801d003030301d8150395180c00d00240c5666040400b501070002104e032107003140d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 975268606 1250 975267356 975267379
    0x9050c0303130e010e04333b19140d030b0a06051801080702160f05013225051005090607020703030302220e0603010b0303031b18 57
    0x10030102c2041c03c0e6083d556403010140d90300c402820500e102030742c01400c080c450010311f400440d00a0154807001420350b15510740400304803441c4048440b1102c1000604c0160105519410300c884028a0200342c001d6401c080841010b041a41c1d0721000309458801d8442040c0c0041800b8140c5400c010421200342240e0b45090b00d070340014003414803c6010b902a103444100030402d00d0003202a0348172281d00520b40d82d02c4402480c0112240800502a141980034844038201a801c1d0745003850050601c800f402016a8900ba00050400340001100c0048030380486c05060144580c0c4400e411004024150a0300c07800303041c0445811000c00c0e0400400d980606a461041120100707038240130003031000d020402540c507200300c07980b110300444a03000140c1241105000190090f809807003003180054a4031170300e00000e000c405650042e48c11608404220104008030b52500b4042c00d94201d00540103142182030440214202c9024041c1500d40b150012442044400300300d050500b03803407002420401c448 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 975269856 1250 975268606 975268627
    0x9010504050a0f03051c05091e0d11120a03050d020702060408060a0501030312050402010e010c211d0103090b071b0807030c0b0709080a02090405030c12180a0b0d09050c0303 76
    0x20f04541300c2110507000d16054642c00100c14148802c621440f601e917280b61030800c00810000e4011020280030b038001e060800742858840e00a1007070041d100755050f00b24403440a041004072803020000c225680e010b2040c403800a0390003810b985030484250800350b2124500c1c8000384550249806c0005a40304640801c0316070500bd401c081c2c12a806511061903c80300350b14480c00b5078800301c402138003040e624003540c1400c0d4801e511402c01c0a001d05880c2c0c0c1e02c0246507003405047c0207038100c4c00380041c4850408070100d00d035100008000c0300c02400c08010300e0160303580d80d03210b02d40d0007844402800342c241040701c0d50000306e0750480c0610740d000035240e40d500914600a0801020842d0507074240035694000744405015083c1d0405565252000b8599501d16600700074580800400c200d849000c1804142070481080008500301c0d240882c1d43c40d00c41640034145206106454400d91003154140003c1000742d007a20221502e05044900106050f202d41c2030030b920b4095813404041d058400050882e280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 975271106 1250 975269856 975269879
    0x60903050a03110304020a0b16021e0a05030f15101206050f0906060105030c0a020a06150e0f01060504090c1107030c0801111207081803030408030403030507081b09010504050a 77
    0x10111035101002054200c25802e03d40303000c2160300a40218001100340540e401c2e02010303042a5401c808040d008240c03507800b050404007050601c0c146048503e100c0c544518202a100d406014140c005100e400140c4c400195038000b074601d11054490200f000c11101c11456100601a0818420300940700c1c00610b07100004180403104a040c0a000b00d0218404074030100b495405407005946407811500c405003028525400304080005500c110700d0304e031001a1860103241c15081405010302201880c0009074446140014071100c0b802c0d0444005011461304901500d0a403007a03504000307007102c10020140c80299042d104900c0500c50308000000b0406a2980380d001d840c41180240080807042204d40454012401c5205c1002c20420000300710501c030f01041580a003660b001c81c254503038541e00d81821540291340c1900c22440000400c001d258142c02219007080181c940361515207000440d44055545030241c4a1503904c00144000d0203070301c16800d079805444020026803640b6690710300032a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 975272356 1250 975271106 975271117
    0x909110103060503011407051b1f0b06070c030b0a020c03032502160e040804120b1e010e04241d07150816021c08070e12030d0203090a06090305 63
    0x2802e118021840f4101070044c40a460145855031503030303440e800800d0f540c1d50091204403407928171113655507074031003c10090000203011101c0850418451840346005441010704c9075401341004112a800041c6d100d41a08122034215480d07a4860b00d910780348501a2182e02d01900c00d40c030010081c8807151184a103410921810340410110041c5182416a200d01ca621070050052080d80030411800508080150744607115a20151070f0030785843d003502600c00c240b44242c0c0c005600c0d2f01044440c07007400c0c0708400080c0032100c94080f2580f4001c141c540000005200500001c44000300e4006400400c0c1d454a010070020710500412114500d1030408400a4860703621900c01e441d40020001950040c424035a072480d40c80048559410042c0e0080881c1040040b045201d82c0e843d1b03011019500c0504d96640900740e41780e040c5401c19000c006d100250301510b540c840e0591080d04c48200340000211030b0151801030340507231256165000c1501f0500102809496a0305040c2c0110070150f02600400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 975273606 1250 975272356 975272359
    0xf1b050f15010f0504021b01020c03030411061207030905150705071a01260c0310050118062114060a0c11030c0a02090a200a200604030f0207090911 65
    0x15100400038212240c000000c0c421000c03c00f4201c203041c407450406400600c00400d02d100440012140301741100d003241c5c861030b850321241c0c0000c81070008001d5000101c2c603141404841c00380c2080540c0e1654111b0040180c503600c14150f1b915416800c201c03040c440071211001c2c021449117585004100900300c0d40c409030040302c984065600f007200e401d105904950584801d16001d00b21043e82c06042c0d02c44900950715001d841c400e1030310041a5540070031000c4c06d020b070b064034042104e51400200560750b040300030014950904180003401f448000d40d0042030403080502440300c45110340d04000868104501c422081402014200f20350307002140c03c184100301090380c490951364142ca004176101d0240100d4852135070071034503c1402500d00440803642040b0f0344040000e4030f00c0350012104040300c0c0b10645011008020480b02002e0340c00c8111110800d002105051256008504550b03c0d4440100003c0c1030003400100320070400c5c801c008030f0000d41000d1070300304500b1440c2d09003101441e8074040d406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 975274856 1250 975273606 975273613
    0x40902182707030206130312091409040210081b030406090b010f0303080604200c1b044d04081c170a022a070609080d0f1b050f 56
    0x28100405000c4100d90700010015021907421a420030a4990000020f000d424000c02808400708901c04020a000e01e0180c40e6444c04a150040114402d04050021442112494200720158542140c1402560300d00c2c070382843d60742d42d00b1200390000031850070b541c1c03d820030101c00c0000300a8641e21042d2654010110b0500b140e076584001e4000030003902009002a081c1000704295080c41e4204d00d504448580d008005404d074012a0006a04051801081070b400f10400e0300d407481168000340c0300c0900c1990248205001038074031540d14450810040b0b46a40d0303101030901c00c170b600c0100300403c0794115110614983d25100a400f0350380c0181c0a08a06030081d0b402030841c0b20f05415603414102c1d0301c0e071588410440c03d0a600000b03400010141080540c081000b294404000d001071008102d8460010301c0c0780c030b59250003a2603c050343e00182c09000f0006424048400300045080c03501d44585005d0b42c491500103812129404130f46004140c0d0901040c0010070400003141d89a1301d13000500c100c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 975276106 1250 975274856 975274891
    0x912030e0f030303100603051005100e040e06010602070b0d021323010e1806151314030f1c0e060d0209030c0d150c05070f1b08070302091504090218 65
    0x8160722131100351103205c00c862506104020700c80c040d07000f040d444030201d100e9001480d0b454012400603000b8008800004082c0c813016030f1285050310070041c0c00d240c40001003440d0b60601c48080c0d610401409000c0800901240240c00d00b4040c0d011076030442070b40101e1808503541c484050800740441008a05a0344623121011000d500c91003ca9000b44c1000b080c1c41280e05111030740106a08015000350341081064041d1341e6050070210041c041c101a142541c21100d107001c0c126000580b005510900c60b400c01d43c00c13014644000035030034984007960b061075800382201c880e095841caa0706022081e0080390119001d1403407a40c47e80a400c1c0903a0940c00c0d19070801084c800c004040307104440040660b5a006404e00d40b03000350358000000c0b0700460900910f000a103854604400c07203440d4046454002165120200a840300a410010311445000340050f07404d540c0001c800030001003444034035040e9a031580c20390780d556400004080e500504002c015210050100c58060412200d888907160541c15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 975277356 1250 975276106 975276109
    0x14040f0f02041701050f010b070501090b07050d0f0b0906102109031b0320031b030403020102012a18050621070e0603150d08120103030806101e0912030e0f 68
    0x7800341b0518281080348096801c21804040c40e8224074800d0ba215981c41441e5400190500d030303018041ca8403a120b00741c0312070000002e032080d60520502080f0007400e2200c050510703103901c0d1040703030071080445000b082c46114441c2140d1700d180e503140c500d50001e04403183c51500c502d15441140400d000f6a540150b0142c51440c2ca1003440e5040b03801000a00d200c052604440c481d80c0c954441a40b003501070f640340503111141c002403401d0400c3c1d018090340000404004540e024425005c0c031152000e03120300e2026a10b001c91002003090340e0007600340940074041031100340010184030040d110040515171a0881208260300502100786c184881d1040391000c102024098225007504100041040d442d40e81d8a0607005100c44071084515040310041800b0030005035510090204008480031400d05580f5505008001e490007074011401184004000e10302c1907440100750451585401c207800d440d0002e6402250122078070ba110440e4101c3d01080d5604140e0712000f020040082200e400e4100c80130b110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 975278606 1250 975277356 975277361
    0x2010207090513350f0a140405040f051801051909020f150a0e0f2b240c050712080612120a0216150c0602090d03030504061506080114040f0f02041701 66
    0xc5c0b00707441820052003444071030ba100e0409181055550310300345050541d694041410f1780c81d81d0314188030b21a1990100141c05420095480c107021944000b409141004041030180000c43d08a0516050701c86c0a030b03009540341c0c000d641281940207003c0078a54159940c0c00030090300030b180c2400c009481104a5405482c1c4403c0d542031058000b4580010020076000c0d070401901a110100000c00328031003c0801b003004207404100700f094002d01c0c0004056100c07140422100da0400100c00d1140c140818004120000800c910f815031a0800310516183c90000949030410030200c40540c0c07040d1010a05030301c90341c402503d0f244c5450380856180b44030120804410544900640720601c0c4041100c3c015244a40740d130007a850f005040c01890b01030210045140301003091387c180c0101c0c3c2c4810901c02041190305c0340112002e10540e8800d2824100387c401401048107200d41c00d601100403841c0b000c03036550381e0701580c1400001c90040041c10400070201e40a50094412444401e00c2c940d1061088401070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 975279856 1250 975278606 975278617
    0x6050906041d030a020a1e0804090203040203100c030606030e0601051f1b03030c080705070b04060c030f090c030b06100e040207030504051017060303070201020709051335 75
    0x14481215030340e40d031090000500001503000492107001c2d554911000c001c1c07000301896075103075000d07050109082c1040c8600361031003522030b2010300000d950704020481c840705503019142100005030360780d211030000030314294984025010b080d16025140426a41540c003d00855041d0345091001414401401703882e003000344100c0b42c000492118202e1440b81e41c9284c0c07464440e1900b0044c201552a403072400b50300300440801ca0100c0e6842d0b4040d1210303900004103d0748080b035840c1c005e103403040c1651001403000001c4c000500c1c5586401c1401007a5019400500020340c42c003404001007011400c05070043e07145072100340c404c0b070381c0003001c00c406042414080b0340080d07030303500d918502d02c03101c4003400000c2d4845182130301000001c1c8070114a0756940c0990980e02040b40e43c0d200f43c91072511152200601001d00401e00c40e600410078500140d0700403a1040c11a01d180c1c0c4006007030359901d407403480e50001413000140b50402001154ae0030104074001905148250818288511600c0c9035540340b51250 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 975281106 1250 975279856 975279859
    0x50a0b15070b06040c0216032d081623010515011103031518010b0a0e0a081005040809040203010b04060f03020a0e190f231f18050603010e070809010605 67
    0x1a400040c6203003440d8100503595005841140d4900c24041c0799000507c2c07080d001160b0308140b04e007520311100014a2400307854078006018103640c2c200c0c0d90340e8a81500c5401041045108d08598040c2403111161503a0b240d08038002058120f03030010072903280200421142c182d103074686c00c1d041c0d103082e5119442c040c0426000e9002140b840d156925006a680d0b1001c001a500280141000e510044c8110205000301018a81180c0320390a1200240c9100484440d0502900ca104000c200a010000b01070402015180000485407500c0c28142c3e502d101e170b050140c1c0c006000100010b500180f0900a2046401690320f0355500300f80440100c3c01d9228110b041e50014031700300d800c88141d14150b050049040c0e00d0703c0d060004e6a5440340411030b200042d40c00141d40d6103012880440c400e020600e02d500381c00003290050a107200440640b940e8101c10a0342108100c20203080405d441c0c214182000540380003001c241d1a580c0d50382026481c0b032001c41302c1d000003460b000c0100c1c03141c81050107040e058450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 975282356 1250 975281106 975281123
    0xa0204050c03060d260a0905120c060d0b010908010603050703050717030909060105070c090b01140408070e0405030d06030605070e030109020901090b0402070606030f21082701050a0b1507 82
    0x21103840365400352000c1c1c4410840b18a804017000d14014808000340304004461707e4907600343d45040c0c00c001c103004040c0e070b5151144d040300500020743e40e1004101c0d045401040700006030350312800012078000c00300780c0046015600e0941c01009212002a1a0040701d12420440d250180c9544e000600244190480e64495000384042d80061420141a5501410600d401420440d0680314884460003503404131003000da98215048565920160344184400c802c200d80d07141515050295585d051b0341d110701844bc008040c045005c100c01403040380d50308280810248200b6481b800c00303400401081d9020070108507000d01c4603500c2c0c103040c09480b00c1941c0060024030b46038680f0302a8000361411500c0c00b540540d0800401000030000c1c85100003035802850030034000c070343e10300d03040344941c000482c90320100d10108501801c084e44807038031941c00310400218200a0309255104004005034006c411255402d200400000c0361030366105040080f81112504915422660b1003100c41c0f0500202810440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 975283606 1250 975282356 975282379
    0x8040605070e0d1b0602071a0717030f01060f210507021207210c15110c0109030e0301150f290c0d17090c04020304020a030803070c050d03150905100906080a0204050c0306 75
    0x401040c007408009008100ac41d02880345801c0d5099180c1c411280034099600c951300500080f80d018980aa00b01894185020901e03004109a0010680c1c1c0b502c50404d01d44070000a40041e2007070002804501e202d224260303c1e4041864016040040c8020300641013130003903141c01d0300610800070503044a40040070b2600c0352040da025440545a01310304031180f14010441510240b8007440f400d82c12501950711201c1c244ca0750010142034401c0710350205407844e11001e0502c02c03181040060801c9401c86100e8010f500c080300440050600b480100e14401e0794040f4400300e40284c0450107400340c3c10260f903507070004d0b41d070300e400460146401d0b11944110380c03103c40d152400342802e47c011900036000404600209a9030354454001d94000c0320f02c00b0001710780c582401c0400c8002c01c0b1041500d0b0007800c0510080310382501c0408540c80354803070318418645850201c0c140c4264900418090001c054052104580310101243d0310500301c28100d001c0d1b86000700040f00c46002d6016079000c1e0348010412010031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 975284856 1250 975283606 975283649
    0x18030a02090106032d02040509010905010305190318090b01120501030b0601180e04051e06070c1106070507080303190501080727090309170c0108040605070e0d1b060207 74
    0x80c010700c5d5545c2900b002103000801a0280c002c0300c101d010f10411400369645091005212520006a010440032404c140045c00003900c0450443d5400d42c0460f501c00c9040d0141c02c04130790412405004075408080500301052891030b98010041249003038954940e81103400810070119442480042c04038000303d408541550710030506d0606986220810289040c0c4400c000d82c000101501c2c1114180c2c450b4000c1143c411001c054046400c9001d4040c10580c0b901d080003502c002002500141602c110501e0078246130384440580382203c0d00241141e0110303440d1031540f03540741d00556420450400c040c10380320740d030041406254140c503119806091700e9450480040c5e4040c4003d8001c41c681c500003000c440e1081c11030b100c0c0d666120b000f03aa4040c1801e251495400c1032260b42e5040300c0042e00203a46402450341c020405a03081907105000150b03503a607051040b122410101d40246e8444041e01644040c07200d8250350700c11103d900d07002111083c0e516801030340c0d03542ea2449100d202c0021002c0310380d0715 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 975286106 1250 975284856 975284861
    0x16080702062511060a050906071701062006040b0103020108130c0e1018150603020301030f031d210d020c0907140d06090207060b030102040b04031401110c0318030a0209010603 77
    0x2c2c4445428840600741c0000c040500b0014200c0e11840400c0ea901c0c10012848010410181c201c00300c1d09102041c09074000c51462000301c140111024420004291040d01c2c560900400c2e03544410020380c0e6580c145440e1140d1000000e1100742d002031407100c041440c2100c0c26085482060384542205480c900d0910043d6285c800201034440d0403581c600c0001c0e264842c80185412041c455500107015111076030401d0207000283c00102c1050700c10f000620000390289a00340380c5036010b0409030307580c010b001e103031024604410749000d412100c900c94003c50348001c0510554489140000d55914084e140ca003280e8076600b618115610410300008a00141c1c0684020080d8640f9080b01c54641310312202e150055940c69031182203400d500003102c0050014074800c00c160818200c00a51910b443d2900040c0c007400345010140404c2c00350580303405001025403040c0b00d6200c075640115240c1e083c410800b501c1c0e42008112101003990303115000954600460707a29282980105131101c66402c3c010202c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 975287356 1250 975286106 975286171
    0x312051e1b12270301091b0e2a090a150504180c170c090d0c15090806150303121e010e0f0a0c0c152906090d0201171608070206 56
    0x709556202c2d01c200226858420300c01f0641d0b20301261070407813032402e000300350070401c001c00d0403512680c0d1030054074440c4c1d4030b0007071100c1c2c4007000618982c6034091000001d074108000c0e88010003009510601c0500b16402c04040c0c0b0403142d40300d0004c0300441c0c00011000540700140c5001000a04544142c410306540c90a440d0300008806682d9007807403541c20102d408103e01581c141d482602c50311040141c134100480d800c9012580f80741ca02c0c0d0051034520801e5440c031000d44024100c0c072503241100c1c4203403410001c2c2c480031001d601080a0074104075001742011150045440740340400b010010400300d10166620307000e8500b40b80820380325510884407400414018110388100210310001d035021a45129144040b950802c0000440710000481880550500d0040382054480c0400110140e80d0b0039040c2c03010f104041e1130413001d0780c1c15880120b6849204203c040203d100000c2880a881e50040c400e010741621a21001010348492030141c0c0d0318403003200e6250f00d108004201042c01c5110040d5200c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 975288606 1250 975287356 975287359
    0x10050705031911061003230d0e01053c0a0f210c0201050f1506040b031503060415050c03063f100b0a0312051e1b1227 52
    0x101c2d01010807070b1490030801e0a8407801409148200c0a00a210b0503140f080104030607100c400e10b087c00071407001500c0b480c1b0f104c200824001074640703001e42c5900400c100c505811034840e40d0347d8a00100c240108074a0030201c01c081c401d07505c2d0b032034880700c0d036000c442129080e40325500c0d01c26204140550844000810100400400701500900f200d8041e107170040d4480c0711031603000410707a0328010002d00310100e0010443c24902020300c4034010300d91504006c50317007500e0340c14440960366550b82090030004a68006082c0d00341c8102c20401c01442a40c1c0c01020f15070007a910148115141d0803944411808140d52140e4000517036002103400040402c048098080140c540c443d140c10a64410041d241c00c45540102540000c2c6101c142c00c1046e10446201040881c0e0490700c05042d5100d2094000711003110400b803010014642c0c0e226103450507400800754060341c01583da00c92059103240b0203584560146018400e801200c1c00d0401260165100c600900900150904019586020101465003503a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 975289856 1250 975288606 975288617
    0x20010203040b15040b1e010e030d140c0102090a180c0518010c03110d0e0307080d050f0d0e0d050c0f0a0305090f1903060504261b190b06100507050319 66
    0x11805e544620701800c1e84010340b00f800340b0101c60104005801158020b103100e1083e0805611441a0b541216000511480d9421f00c42c0d100c04c030b0300000a00a118014405074085410940010a1001080c0d95188210201401e000c095030303142c0c2c01d49090081ca40c0c200d910030f410300d0805020f13502c90101054524000d29094800a1070741e040b003030034501408099000a814001c0074041800c08210280040c080c4c0c400034444415a010000c010307005440d04915071380c4e000070b14205545229003002c1015070000e420b89041c00c81d402806019139010000c0d0001c90b01503800302d880e00500121301d0344c00d41901915014030b014004420845001424a00544d02c401002580394001e1055101403000e5403040900007400d0401341072090b092501c04c0000c54510048014034980420014166a408464462500c2041c040c1d064103d003800d4281e00d00700d240f80e10144941d400e024642c550b041c000c690603a03036488600c05000041b00d180c4100603018000b0303031040009480c190309001900b8140305030f07407404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 975291106 1250 975289856 975289871
    0x1c05070e0a092f060403020d02210f0d030e0c03210d0f0c0e19031707020d0b01030c14060f091c0503040501020106060509100c060e0d20010203040b1504 67
    0xf95a000110720440810758060301e69603c0c0000c2d00c443c101c64205100315641d500b424615800298800f000110090181c20b500d822100e8100c2604072040fa688101300a65440e40601030b00c255035002110546d90000307040420303140c0c2c0002d000c5149001000702502034070851a0034000000c5032000c020004800020400c100103802c00e0034800c207042d0301d50004000c20158420740000302490b501a0072a8807441e10354814a8070342c03544031099011258401c24140c040e100d82100c03144076000c3c0750b10103500704074985065010041840c881c0c40c16640305900d074025158540d40000d40c070880403c04a174004030204000140c02d00d0080103021404801011038100c407410020712031440118000448595002103000d008542e020b0041c280581250b1900070f00f082c2400f4002003070301504c3c41d041070a02c8907900d83d24041c42081d811410110840070b08542d0080b08030b200c01442800d03900b24204902407080070b000043d44045c000c4900541c3c202440790040d4070398955058001c0c094240301a44642d58020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 975292356 1250 975291106 975291113
    0x6090105180c161b1a180a09050c0705070819060b0a050a03050f12090109030303090302010b22050f070c1e150515030c06030a09020d080f091c05070e0a09 68
    0x1d452203003903c11307100c881100111484070100410160044031408102d4040c103405062003100340c91540c030500d10001501c82180d40440d41c41c10440d04244012424a402c21400320641d000403c85544148200c2e14010765606d0003c0d11084125071011804041903045004288150440040e8500c01851902020365600000ba0010000c2d4421a50b81c5c011000c500035135503080c050310141d0f14456103620b15060800c40000c000801c903000c01010f050ba141822000d243c0700758015501010701904040b24800c80c400d50f142080314858100c20410b08090005140004103816a0700480031a120300ba0078910694448000104a010251701849151003440120b805803003d1800508078040010301803c4c81d407031000c0c46600d91365030039000350700014070303581c1e071341c440c203040f05da100b6540c1c800001c4501545c8002164400114005060348002164132607030003038114018511250304a850300107001b40e40c01e10540d0206062009440ca03000344130304212854028402c5a4090480103001801c2d032010399 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 975293606 1250 975292356 975292387
    0x1806050c1905010e0d020c090601120b0d0818040603020a09200708070c210308090a0f063e1b0a05060105090606071e02030f071d06090105180c 63
    0xb034602d6911102c90100d515018400400803038914400f034000d1000e21004102c444c2805000c060401038001380710a80c03010954000d0203500343c02054164a1704250400b0b044a8000a003c13015001c03211041e17004500e414810341c802c0b60390140c03160442c0e40c40c10000c90028240c189100b1030401c654490800340c5260400203000c00c51107402100e03102c0e159030034900c82d40c181c3e0b41c100708082d9804041034141c0074548031850304050b51600d032070741c0c0c50340c0ca1401990400c05c0c40d50307006017144d0781c03e0400820002d40350400d01d8610309002441130341c011120101c10540e040c8098249003174045171004161491400b000703100741c0040318004000d00a0380c128042c41e281c00c200c0e041e47d46400c01001400140703001c282541d0014002c4030303001d041c69801d4440490b451181c80d180b5815400340c0d9010b00031520f0510002d1007415201040c0d42400d965610a800d43ca000f000440420380f0850b030000d4054030707103142d890741130703840103801000b5824494503894016000a001c0160091080c080c0302101c01d02032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 975294856 1250 975293606 975293653
    0x604030203100e0d050901120f150b0403060c050f1b030909010311120105090304140f09190c031b08061f09060315030b070507080409021602101806050c 67
    0x20b0a00065003203c0b50380381410300c50448489000c05c1400c0082c4509030380c0c4031400c101c10700142d441c0060700c07400300446500100759400207465000880d0382e0015448221001030b00031203004290a0005480e00c07001150b1b248514a20901c1b0408203110460384240400c16040d61401d221084030f18001c180c40010f0580340e0700b40e00c225a2646030314500000c0d030811801d40f032450741da01d500a000340e04080540350b8880c0554020000d00a85510607a0361a503102860301017900c4000c0d01d0150b1030708150620240350b40a41c2c001410309420300d080c044006100303116010076110600c22a841440e44407404855140c40500010341c00030070f00407000000c11240c0303092544006183c43e0302c1e019514100c3d0280c262803180304803262a5070111810004160fa90400300c0e401052442c0c481d580e00302900d424103680c000c5411519940d4400328509030204c001e01e40c070b184010b000300d0300c1c5000c8840b8a4022242c1013408866190300346031000e01008964024405010b44201143c04d41700581c04e004102103039840030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 975296106 1250 975294856 975294883
    0x50309032b0b040524040f020c07051905010203030c1c15230a1a1306081b03071d0a0e090114011a0a3504050105071803110604030203 59
    0x42a160308526101d03101e101501d000c151010b001a24042504448010000039501e40440b00703034480c1e00540d0707280d80c0040340c4004050400c54a410304940030070755a14060050a00440780d10b10b00c2c500c0e2106041d22341c1d04581050b4000c40c40d5540b1901010700c1d9402c0441100195403a034580c40520101c5070080d9448070010b080e0f070101c100d10340280faa20070140401010344011190005103e00c2c2c6803400c820003950700d480c030002c610820840084009200308003106026544403940800d480364401c601030700540340400b84204542c003e0801d00d00600c0709540c8a400f1034010b031080f03250b604800300ea80020040061005441d00c4c2d80e18200003180070215002c01e0165901c1e402100b1000c002d02c2c07880d0141c0b104031403c2c0031184141c00e0502c0c1906c1100c51020501c111507000b920b40088884078103c0d164824050803034203040c4260110b408020585084586509000000d04c0180c401ca54501056100450f40d580003407a40d15120203411100390343d0381e0030020030031001c03016840c02c000e988041d008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 975297356 1250 975296106 975296167
    0xa090510030921020a0b13080301090c2c040c020c0406090b091302181018020c01050c090f060721050a021005060d060509010b0a090f050609010e040305030903 70
    0x142031500b81001071800c1c06070842e011440d10b404192660005001c0140c0360b1010011b412501c0340e90405481842c0c91400030290680080040b070074050765000041c074001542c40308035000000000780303a805011000c010366141000045601513107080d0708442e00d41c240320b005880300c414421000c1030958040340c208000d1503840f00c40848032414602022940007101c98a103000240040c0d000589003002c1805442031600d41e0008600361a0791481150010800641545440c0110616940194100c1024041c03d5443c0c5000281801040800c460303000900030a600480c0c0e401d1001c10103240c10190040d11101c0780d50001002a0f1210311000803940000d0f20790648617900e00c2c6c002454906801e10b41e070111801c1105100c05600c441c010011480c1e485007001c43c09603191034456005261018007143c0c0612a01000654010356501940d0711410174002401075954080520032400d0081c0308240c4480d0850000801092154000c0c1d5001070400c02680e107070080c1c0c00300d0402401c0780704144007085103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 975298606 1250 975297356 975297371
    0x20a0206010b090102150c09100f0e0a0b0a0f030b03014107030b040e160906080102071104020705030d1104060f2c0406270606090b07080a09051003 65
    0x25010010540100514540103180c0342552000035103134003206040e204000840d9001c0f40c07884424906541032075201400407a079491500344000c10148060091101080c2d0034500382e00c1a04001c00c000055078040300c0c01a14004020030100ca103266845200810540d98000a0415913428064140d48264200190031104000030146034200211286109010540c417814158a002260020380c460480c0c100050001c0f107950224001e008143d0951030903001d4030019001c140c0101045000350f41e2801020442140c4614406080713104100340902040240981c07102c2c1c0780f9180d00200301c8a0310880c1a64200100d011150051315030204c0c0600b05a000400c0030701020358840700c60840c1710518602034000f000c03808082039200020204d403070700080c000c140285d421303100c0350031181c01846030f60369400e0b80038045c0c9400b0b114482403100c0e0950300ca06050000400c0d42c8584400c83c1910259030089190111580d10600954000f841e01814021f10a5000549070390340ca044c00340180c0c03542c8011501c0d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 975299856 1250 975298606 975298627
    0x150506030105060303121f08060901060602010b120c060f0919030201020c0f0d03230c0325050d030207020d06021210050406181128031104030b0c03070908010f02 71
    0x440b8001c007440c0c0664002d105d207941001c2c0ea4180c568010715000d240800082020150741d000040d41e41140015116210078041c00303100c1544508200c400c40e5000700304178225501000310030056030321907501940c801d0500d13466610b4808000e18500f90000f050070f140c030109501140100e00e444905111070800e2250400a42d40c0501c03130700f80c0c0010f08540f0885002c50000004000303807101e0501608105103074901204020501004280d0201d01c80d00761a00c414000a02e1550703540408001e00c0ca000b4402c03106000d82d40000724000000da40003000e4605c111504400f14004e4001c29000c0e640012030030280e00109010b440148070a8011030710700d003044e01e056480d44c40c0307403007043d03010b14015464403030208511820128642c5030100680390106440e03080c0e0b06241c038180210000001c1c1101d40740d0940721172098000051000818a0b1010300c4100d40ba428107000300d024030300c070150080303544c000080d031050b490310700845e03100c401400c214401ca915100b865007150000c0084090b450b0307000801c070005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 975301106 1250 975299856 975299861
    0x8130615060318020a06030506030c03010f1e02130e10030b0f01060e1207060302070c0305010606170a06081b01122c061501051b03070318090207020a0302060c0a1505060301 76
    0x43e6100c00c444841d8031020b9022843d282004e100f08000c01d540d51012548541d400d0088a00c400300050091105026101d014401020b807001801e01d0011f01140245d900135190003a540c808c864802c20608070351508001d000301d414000d014100c0007202074000310004040e10002d90055000b840001103641c10641d02414507450b504405101f070b52203501543d444c00c0000b40080650300240b80141c0c0310051480d04500340c896940008041e5420a4004940e160341b020038004502e010826000c850340b03810601ca07044405074081c1c0c0c01a9080740c1d040c0d800c0000c058840c024010018905590601114404c2ea4200c83c2074050a411701d6501c4114071004800d0f00780003a0281c0d0b01e8030050072040c02c0c01591180c030011684441d80c1032101c04202040048070050300b02225461101c00d40356071b50483d10b4000d00c691140d04101c100d5808008012070200c1e0180b00740e60003e40c0c080d040380d54140c115004c12006400c40181045a8800c807540c81000070350f0800601d007007000702a000304950600000b054207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 975302356 1250 975301106 975301121
    0x1801120507030b1e241e0301020d0b031e0c060306010504030501020c1f151a040f031b1205100f0209030a0f0c05181b120903030403080106050f0406081306150603 71
    0x2480e0a110600d130050310141c0030300300d160358421034441e0100307034041b04161969044210000d0b4154808129111a40040c1d00028003104044090301c1c012250280064414011a20b540c0101c0c3d002e150040003d0030008011600720b6014180a07050642c0e940c0c489080e0303401300205c444150014030302d4034a07507071381040d01944840c000c003814011889400515526030010380b00d1280078000ca1030000032001000000c56001d44400b41042b840f5907100d00b4031040182c6030480300600b0102c02135002922440e0340e4801d40e0310540c04000f4000d00c07490022000b0250000624014085500b0032207000c1310340d001c10444800038440c400c0a43c01400600b4407091030f48007a40694080c07900307094601d00c44140e10745456404000030800b52007000c1030310f40030003403801040c4812043c6070041b8103004050b075000002d5841248256240300b00c40e0b0301c407035003142d01e40515554401355000600c1b050055901a4031629405111a80d01d03030f241d80c00d15140c840c145c813050b00004000d451068024811035078140203811 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 975303606 1250 975302356 975302371
    0x60c0109050606060a0e090a110703081b03070801090203040309051c03140c07051507081803010513021e1c0b01080f01050115050304021c0b0a06051801120507030b1e 73
    0x43c1000e500b19400b4000d103c45100307680c0704810031f00000f4008c40d1240e00003003075a10307482e036000e07115007880c9000380030b0b01402e031031155640070444080d40788828480100c0b84580c241d641c403c04541d1a204940c8003941000d030088041c01110800424592a90003082c0c00c041150104105102c599003805403041005d00038424403200c0030002c43c0c3d0380e1440040c0c4034040340d1080e10005031015490000d129140141c200c014113030080055a03d01080741c01000d070a0090048008004c1030711614061013802c50364583c025000445e42d9200000d05e00100b81140d403480e03020b001010404921171202c14940e05505044070403e0b032801c01480320300c41c100000f1031070701c40d440000c014a50500e2500c030007800d41c420840c3c00b01301e0b001002800f1910781081c40a40444890b0080381c40644502d4943d0403107d048510003c180c3c9841000540743c900880c0b9800550b00c40c0d00c00203e0350b401d014070b00c0d2160f03051300c00949807481200400000904503e03c8944200e4101620380c01c0e15913102c440d100000c00141000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 975304856 1250 975303606 975303619
    0x11040e0616030c03090f120903050f0106051203190e030a060204090e1c12020a1704050d033207020705090f01081605010f0807020f0304060914090115030e010b060c0109050606 77
    0x108000f40c6c4107500d0784900e50b00400071039001ca00c044030032564810150001460b6005480640c00900e005402c024140c1d0001c0341c40d05010300d40240942c0d41d901481084201144642070100350440c040d690082c0011006405d031204805d641d107910b020380c2d000394010b104555680444076010701003809850a1600c083e07145131402c01c48160000c00c07901c1425a03c41c01c1d183c3c005407001205000d40669101c0c40001c52000d0705c02d1a040c10034030f4613940e0442010340842e00b880805002100500c81c036110480c14401c103c1080c41c0c4032494044198002084c0381c040d40700c1c141000c245030380e030712600d64030800f4020141c15440d070600c0a05810601c001641904000025406014903038010601c50555252803400710000d40e100c0030224500f0011207622020b0703001c0010f01040385580607804c0000d6a02c103520340c40c2548001403d21000e0a0244039024001000c601001c030b10134401d400940311840100c0000c10705541c4480000c0036544041080301260b95901552010854140034031640040119081e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 975306106 1250 975304856 975304871
    0xa110603060a031506050907020c04050106030c1d04061d100503151303180b0d0e0a0222020f040b0414090f13020a080604050304060818030711040e0616030c03 70
    0x4141c1240d00d90000a1010407074a1010340844a140e003c1001440000d02040488c2003050000e51107101303401c00c40740110305101c000300d0303128000e0081c945224a180d444410246044c8840b240034840152015441900e4010004040700b402d075080a40011f00410307a065170506600b88503c03400d459015070701a400c0062400c80030380c40201900e80c40041d0105601a1105c01d18044881840b01d03400c203c540035040501080d80307040c4401814a02d000c6140c2005010f950011141d60741d520007000035402900700e1910003034928184000d1240803440d0307402500704507281071560300340d8101d6004200d40703210115081001c07440445216595907001c1d503807035906080401259199803070041c1801c0e1301c40c5942c03e030841191a8500c02d0401000c400b400c0e00c84c03d04180c542543c03242c0c09480b840000130035103000310304a000c0c0303214510400781d03440d0025460300f4180d42d02e0400c0e840032108550b0344156100070803000a071003030006920407010706508031010b84101c40d024048400d9401c0c61400c2604d00b10380c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 975307356 1250 975306106 975306109
    0x15031514100f08010306020304140a08181c03110f24011512150317040501110f0d12020d020d0f0c091a22030c030201080a141906080304080a11060306 66
    0x1202c0c0c1c11740b07400000144e036035134450412103100c1e24001601d820520402854400340040070014044405c050a0300b4911681c85404220310352101401d41000c09000d441c4a50003e402003464549032403100c030540b940d1102c8808440e082ca80c1c0d040802c101003203141c050404800c4016101405444190030060007039015210003000c004c03d0066040da120b0369131403001084058422b6050007558000b4111540300a080e0400320b05401030722445011035070142b40c44442a101080b541c1038416654000c091480c0c580da01115448109005810100d0342008081040d49150000b80030002240c00701041e0101e403020841e080b1024201c0d19001c1029209060000c03500c01c08004583c00e160381c22131601d510100103903854660340c0714503200009034180340c00010001f540c0030003011603000f41c0340c10036a0717552044a01e09440030501d002940f1413514000031802d0142d4031031200780389081c0d400001c5507034a8040d19842c5501c6a0040c80003a03001942c2a0200004c1c0070344800400d0040d40c046085051110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 975308606 1250 975307356 975307367
    0xc0f0b0c0a0f060b13060905010609033c0b10061d010e040b120f01060501080c0a1d120c0301200a0507030c06090c150e030715031514100f 61
    0x810040000c00e9030036201d014407901350030202000e000140320503840c1030451060310041c115403085020031420203000041c010b00030407022045a4000d89104000180c00ca0118299106024203400611382e00b604291012174050741340c038000f841013543c802c60f41080c031170840c04000d4a512000400034030b0000c0d00a01640d40d00303c40310303001c0203080c041540e00784040000c0280603014119900040c615544a426680c00500e4143c6405003100030445181c6030302c0112100c000451f40555030543c1081607082281c82805c0c040d9250303031210340d48131000c01d50340c002402c10a00c00c00302c4800395011420520b101e01c1d003841142101c000000310300040080ca80c0401605001d1211a60705000d400320b0010245400b80c851100311b194070100c10000c1152510f410340070520540650080441c0d030513201c0400a0050081134200c000041c01080640e1800c5444000e407002110b010040503201d21b032681710000881e800c1805480f070205d41c1c0540500d05000d0121810000c00307148100411604032070f080c160042c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 975309856 1250 975308606 975308623
    0x3081320121b1002070515070c1e0506090402070f031808150c030910020a0216120b0f062b05370305160506060f15030a0510080601030c0f0b0c 63
    0x2d849154007400c8009013a400c04503254062500700c659000c04001402d440070017003104603c00c03d130501c140e54070f403080c80c0d16400310f041d840c800c040c120b54000e02c102e281c00740c007030802003000402c00b514100966072500b40415038500d007207001c2000d007003600da1258800c03140a4003a085642c010600702e40050080c00321000090643c400d843c0c80000401c0807200248407005402c281a2010742d81c51009504c001e58030340b520b51030411600341d040d1001c54003400c61300341400c4e5150040a945403513294407040210b480c03130240140d54030511050b10407800e8507040400c000000c40c1d010140d0f1004510707007030180c20b03c074080300b025860101007c60310954400c200d00b9000603000c00300321803644540501e003c1e9002c1c820903184103195080504030b1420400c00168103880399500307032446a0603022000030310141210306064808840da00340005083c1c59015484194000c0301c01110030107059030f9030741140c00c1000c2070f001502d0f40d40c0510021b003c0300310703298181d400400f04d06401514112020141d5a141c656a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 975311106 1250 975309856 975309859
    0x601050f03030d05310b010b0703170702030918091018030807050f041707050319030c1104060b030405150f010302190e090115080c01090303081320121b 67
    0xd0f000403400b491443c880d41508001c1c0d000103a01d000c0c2d0542003c05c0a0043d0410848414800000111b2000010410354801c540e05484801440c9050810803c40c002c000301031504600c01407141804031b1341c400c0e01140c4500030100098040d802e01e40001c1f42420303841d0903106101c6080c8050f410780e4401d040661640c043c0c1603e85408281c441101c12100c40c845c030701c1d9805201c1008180814030660100a2001d2411003108440c4d000b5626014140c8568003a05986491804d621030600441c0c040c013444052103114070200d000c111080c10001c1c003103e0154025840e0130310080304000c10407108010141c140d400074070075550070b440e2880c800c5d18501c2050200038052115031001400d5410300d404500d020b0714283c0401103803403611500d00d074000c00f400034101101024003000010014400b09059a60003010303540c114809007192001e86544130041d018080c000d001920f490701040e59a000028000165608105821040b4080000c000c0201a1901c0c8c150040610040254040c2c400949800310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 975312356 1250 975311106 975311111
    0x60e0f0c120a0609180818030a12020f060c13090f090b04110f09091c05070f03120b06090901030b0a0204030b25050f0304020f0a0302041404050601050f03030d 70
    0x111440c14403054007841129026001c1c4020a2064000390798000405540706907500b0840d580b15650542c810b400c141c1d0000d000144204010740341c1c03c0d254000741440a0001e81202d002c134880d507440c2c1d016101d80070003420050300b03c6031405101440501405402080840305030313023014444891000700011a00c00c0910a07507a520420303180010580148021325000003582049180c81c0c00c014120940301c84155104030410480b00d030706480c145074850b0085100900800d00c0021054486080c070f0101800c00081c44024000200004d81c41c8003120100341c802d994280070501103c60040c203860b010340340148a41018811036400d0b4840032515030441707402803600082c0c0e40303036144100021311079a00080d0a0890030f00c20000407211510215850401c0c814100c041e005445900301c86600030701d001103650101c10400718001d440d00300c071500e02c04c01c0c00600d6050b242c0d540b0b500007001c48912040b6101011291030401052090074003c40d8014001942e0f0b05080c284480c0000b5164841c0c1d05811141c1603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 975313606 1250 975312356 975312361
    0x10905100803040915090516091d06040c050c0a0c0e061203181903140f060f160212040801051605030603030706090602092e020a0c0e150a18050109060e0f 68
    0xa0103000c4c070740014000c6d54000c02560416070301a240c840703140310305079000c06c40e41100002c41c16a2115040e85205404800110549030b040400000e08044294201040741c10320254403503003410311a02c0407040c414034164038003914045038146a00c1300100440d1240c00509022014032501004499080c51b55501c0301114442c01c0000568403107008802e594400d109078030110400138450000301d0b092801c082100c080c02d19008002d80e54180c211030005401d0140c0c00402d5070790341c4405c0455a803004500654110180003545030506400592010040d6034481341031141214500459080e40d0009190280ca1031078880003081c1d81c0c1c40380b603400030802d40d50703005180c00380000f40e41502c031301d440000c10118500e181c8010102e5682c0c1814003060019010603d0402c8003800015425440e0398824025541c6902d03242200c1507098006200c401b00384081e200c2c010b050f0f9100044040a013650001142c900404410780f003003140d00581040036000d04d080310070b22045001c1002550b200d20070800c11600d96 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 975314856 1250 975313606 975313631
    0x30f030f06040e01020f0d0506120a0305030a0f091208070804120e18070327030905130b03011409010f0e1209060409090f02040c0c022b02060301030b0109051008030409 74
    0xc3c00642d1646005503c00306a43e000340d03200c180103000b09501e035030081c043c0d6112082044151851041c0c13025003680050b182600083c0203102030343d80041c4110340010030440000100c000d603501e0800031070307602c0c0401101800c001c1d0001545900300380349180158042c6003560303d43c007044016507007490600445422800c02c80c0d0b43d100444007442e42804454080c0d040c6018082c1c080c0403100060703a020202c022166600b00142486c5410395a090b0740c800e0102450101071007810740102011646150700c40c07100c8002e0741c80c01d0190303101095030404002083d107800072200d42102e03610031030400c5d154188000655601000101e07654404030030020a95a850028002501c500c2a9400303a1820350a02250000744020b8041c6064400e000365001d208244c081042260442c80030840250f00c028100d03901d001c070510561000d11048504403100031881c2d415000181642c009038004c03240c411310b1100500411511340180d50b002a0741c01c04903042103040890f01512806280100940e1583e034820f043d500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 975316106 1250 975314856 975314861
    0x70302061b040b0c100605030a0f020f011b0b04120507030c020f0301090b0f0a060b0f0a08060a0801020c01091b0b0f0d0f050a0c1d060f1303140706090503030f030f0604 74
    0x91100c0b4a00503980d40141c13048540340c26904914400080c941840029641408501800069441001b01482045aa0030041c03a4000e040c1d000d41000312a04002800e03071040c850104145000719800300c103500e03052403c860302e080f40001c042c00300801403240780002500104041c180a41c11145000c0070460710000c68010084c0324005001e00c6941c00a12890502d070100f824010090305100307000c3c4070707100d880701005403103081174100d841e0f20104000c50403503100307035420b07074101500070001a0020741d07400ca02400d91700400d01860559540e080940c080158100d00d1002010700c1c10480340d60681b506c050765a0074000c4e4414481c5210b80042d1401e40c80c4099070101c12649030a400030011400c26035001e4004008104010000c15601c0380e040070240100c660f9091000402802c043c0b402280c1000d5052a40000000143c1052004000300000341010104140c802540c001070281504d4013400810038401980000e000380c008100c08100c04296504403a8092a804001c218075103409002c20b00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 975317356 1250 975316106 975316109
    0x260906070f1a01080706030c0e01180f06020309010e0301050408190c0501060f031b0524090a0b1e030105060a050315091618081504021c06051b070302061b04 69
    0x1080284602d01161444407821681a40e21340c034119407180c0e0300c03030300c09030201e40e994135502020440e1180b0b030070b82e507602c103104000b90307204522006900c155491a00b6210295035810200243e000403980b0384855a100031185200d80d01100240300354146070311404242d220b020000002401448080303000c0500a0541c80c2daa0f651101c006c101e026a29200309014070b200d07000480e01080822076010b0610a4001c50209407100107040000394401107040502e00041000300c1c40f000c1c5010311600307000359115815403000f00500d203001d9582d946150f054242a00e154a5203010034001880103001588842e03080e508800100d00b03000fa0780e9102c40080e42807240d000010f540e4040004400c11512035111008030340d45940700d03100c0e000c3c07a18517210011907400c0c20b0f0080892990011501855120045070066007090024003000f19688080c260504810a008025151292541c0501080c0301d008040311183c0000300700240d01300507103a58000e4603040c01800d1041181030012000c04410403a400700c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 975318606 1250 975317356 975317363
    0x9020a0305100914010902151308060f040317040302070501050711040c0e100e0306160e0916021b0105031504022512021c030216020a060c260906070f 66
    0x3074103000742c900307950b0241840300740407500c140c081c0241c0f014166050180a032019130040084000e0b640340701000145403c41e80c4604091070911000150f04002400071a00030180d091000da040c0c0b6060401406814040c2202408081074900b0000480d501154550075a0401d01c1d1031079540405090440384a00031071001a40a482c02d18107005107031300440d0300b400d06501629420401c2005020540b5110319483c0c81d543c050700040002425545c54140301c4201199a00382041d104a20b400840c0c16004210780c0c41c144004090074016007a030f01040b0341c41000141d0b0050600c880c1d5440e0000300a17000c003420450300e091101c001c00b01e0a56540d01920221210b50748800c8074855000403210312400075036810f4032840c03580d413501850382d4408180742c55580c40c80322407009a081410780c100c000b98000d48501c036001d261101d0450060ba81c03146560001c2c49a0341d074886401800b070401040d1103004204900106808640350001c0b111006c081d0b036030203102201c031141c07540b6907803c000000c503003c520001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 975319856 1250 975318606 975318613
    0x206100b0a140a020604031101020f040506030a090606030510060803090d061a03032208010605090610090b1902060703050402210114041a150901090b01051306030c0e0402041809020a0305 82
    0x2000103544c00160103226a0207941c03207041c0d04910482203400c074031440e900080000010070080c440c5090150085802140d02c08001400c0e948645905048070065002180d064000c0100d00002200302d024481c040d000b00d80140d0301c0c102000300007908001600900805181e12030b545031515144034162500b6540c406010799070341d60303003802d04140080c10310181d160b40c0e02d01d200c0f40443c0491052140006030389001e407540c0ca00d9140d407800c002506c000b03500d64100300111186d0220f202c0e40150040e00c0381020500310624510580c2c200a07041550041c20b06081601e4441000056603410050301c13016800e4803079182200c507207648214090001900002d003034080900a2104010900010340020982541105402c5c0c80b01d4102d640c4c03283c180070307142c0e50000102c0c0044c06040c0b19039001d10790010341410444c2c42c1806070082a00b07650250b41c02980840d81d1540c1c901821a08a0880b40040300225400c616180c101041100c100c03d81f180e00c0d00940e907903011810b0454551058580195030444c0c01c0703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 975321106 1250 975319856 975319867
    0x3090c011b05060c1b0105010509040204051909030315120510020a050c030f210103331e0606140d0b0a03150507030609050121230115060206100b0a14 66
    0x1d910381e5000326200010401c45c50700b6204003403410710074581a500000d00482c1c2d41d03180c903020000a02070180c10021484001414003020300c41a00c20348809500c684c0300460504040c0c007c03180c80560a0b072000040045048000000901c04103050f40b80d14040c000050301c030f0080c142c040f1028000d03200606c501c1e1200103018020188003502134103039620f410716a041100301c11403a101e00804288001040000c0550240a0368108490542040102004818100f0001e1a461001d0343c00043c01c4804241c61010b911845144900802c4050140c0c2d040160300c1c50018184000c1d14400c1c440f920807101d40c1d8684650181c1e0b240301d00d8800854010b00d10003c1e030440075208100410040d0b5100010034502840080c640210307014441c100c81d004a2412581f00350003000d50b06a41009004450381203a005498420700d02d0b141720100300030500800040c500d0fa00c280720b01d9803068103810100c00d40d403010040041080c03065015005494120300740e60784403204240c055034110b40002002480100200e05e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 975322356 1250 975321106 975321121
    0x301050603042d1b0b0406080a0207061503032d0f20030f310e070210060801020d0501080f280501060e06040b042007030507060204090e1203090c011b0506 68
    0x86100d44440c00d034004000c245c5c0d1403104414038480c1e0711445c401300d000d580c0000c1a04c080c903805050802e0003079001080c0601c400f80340b043d0001150b08210045002d0350024800d10002c4449a24503190882c0c04481c40101c1001c06808500a00101010440140d01c54208040041112005455050112034559411214695450304490742c04121080400e6150070802d20842c414119029145200b00d03480341000710903461940000c0014041d48240e04030381d20003240c184501401407039107500060b19541a10b0310041a244183d001607129840510040700c0c4032408961014549500000603410074840040b080082036501c0e80a0019444c094000a001d600683c80910444080703c4c10024080711004110480e4110804541c04103505040c46602d4000300004080c3c59000c0d040c10383c14a005a62414143d900c660090083d00d40c940d40c1c54030307030080e0070080c180d50b40840101c000c1c110f183c84403000341d4031101d43e00c9103810068951414000510382180c40309141c4cae004001d58089180030074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 975323606 1250 975322356 975322373
    0x18191e090e2e06050a0b03071e140f1204061b020615061303060908030f0f0712150f030818010c11103e1f0b041107060c090b0301050603042d 62
    0x1294140031450780100007004507007200c0e408103502748640700c51066450082800e902c60304000d03807600d00b00008200036002c2c544800c1c2c02c1c51045220340e038042485840c00c10400c1d40ca9890755282c4007554440014440200d85191100342c081c1000c1d00c005072a629500110355013070040b648043c00c0340e440c2520601c24008074100440c440c2508105c802215112000e06540350141216444002004080f107104c03800403079041070590511055803015180d4030380070b61800145083c1d004a505c0741001598004403030384000a111300300310900300f20300303c031202e070301d40e100f02c8401510780e5441650158190300c00607005030540c2842c001d207102021211040813800e02c2200c0519110b02280010080301c401c140c03000002c032200b03510f10050710f0340907650b10710b00c01c4005003403040c20103a40541c07540041e13070300d5165200c060001c2c81d0141c94041349060500401400d03221541d00408100f84007000140059190281100d030825803024140390000f84665400303c000c5504140b03280524004030380c1c80240007000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 975324856 1250 975323606 975323611
    0x40c05090604031a070c050d0c050f0d021f090c0e1b0c0a0b22112815020d0f05090409080a03090506060618191e090e2e06050a0b03 58
    0x80d130016994503941016181c10b0002640101290322143d610020588039042601034548204100c4000b0714403c100182841540c2e000710b001039010070304848180d400842501c0b1000c0203d08100510411500c4203800740102d400751081c1c1d050740c840421603030111403040004100e076801006484403800c1c03000a803903182058080c1d4503101c0c6440402c2c0a0303951000360451403c01c0400c2d0008400300e0341e41e80c11008d894220901d5020800c143c03440301080d81c0d0080c0c04640c60044209402d01030404c00d1082c0381d40c4441800300115803103088002142c5400200b080e102d0500303410a04d8940103400b0001e0041c001c654001441050089001061140c164222070a0a4802e6041d90126640c60007440710601608154110300b426400c0d1080d2603040a91490102020740c15001c00666100c9101c1034000c0c1c10045d45500d60301c3c41000400c1040f865200300a010500f001c0071b04030500b00b95150440065008199a001200600301c800800d2001e62003100182030160013054140e96598008680783c004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 975326106 1250 975324856 975324893
    0x20327030c030c1c081e0705060705040e0106050904020714060709060e100e01050c24091b1203040509011514130e0406020c060405100609060e0105040c0509060403 72
    0x650071841450301d0b010620804100c805480d000d024031054a50340029a01508152120b0381c0c10000c5030140c4c1c2d40e0014084030714480c202e11641c3d959061404920300b141c01040b242c1007100c20b110a20900c2050301046044852a140a54035804104001030081c82124002002680e50009952245402045407441490580c4070303907801d55980e10044d66143c42003041940d100c4a201c030002c0c0280e00810010910300c4040c903109040480c01580303640340c20014403840749950b01d1203c2c0950141410041154440180406003002e40400b00d0172024010070070341103e10806140c1040c1d00d0340f42d020002c2d540180780040401486503580c1a04801d244002071013600000c0c903180701d0382c1500e0320000890f1781c80303c1c6078482050210720701003a640c2812006841180c40365001c02c101c40c0e50714001c100d0f9501030340c0100e01400460401075191011108030354800402c1504004080044440103040b081c1101d20698022940120f6400c04580300c1c4075402c801b50b404880824044144000c00407082500c911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 975327356 1250 975326106 975326113
    0x9010e010e011104030f03170405030304050607031812111f0f0605060f18060705030306010f02010b01020a0b1308161106070c03030c0f0507060201090615060c1202032703 75
    0x14071605442c281c4030641e10200b420344040004100288009406140f004c0c007a02d0112203180c0c0340503110b210304e40181c030159a5680003000340000e0041c10f0201c6a008200b03801c007004401d4400001541d00116031202400c0c0e10107545e19030781c01074001c584090702e50030707a442030b14a00c100744110046180141190a00264945036a2f01c45254452054800f6104002d1500341041c0c1c10101d40241c41d4081070f0300d960f0301c46085500c000603031506009031490a101707802443c0c0f45c0c60580d00040080c01c0c0c40c0d11101c2107a0608041e140c241e60081081329200b500424031103182d030307141044210781610040000b030441c50009441200e918101650401d01485070018500f450441800c0042c580112080a8048011400704000181c001c1d111008078034411152400250881d4680a00346042e503400200540d450301d1500003005101d101c1c0d544150040c6c000c601c001410014010302400e10140003e14030004441500f201c1c90007003064514948100c5843c005400011042001d041c94034501203001e4807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 975328606 1250 975327356 975327371
    0xf03041d1e09011112060405100315020f070c0815090109030203030105130b04090318290307021032130602090409020a1e0b0307120504061409010e01 66
    0x10008014500441d03410680c081d1990020000800c0320708040d0010100d50343c1ca40418a200d00200302034180980303c00510300e00b82c9807000c240825120028460b03e0b111818103018000600491807507441c91b4004100161140c0c1c804105d03043c9486900c2c40034021903806400060340c0b840c001070b0200621203c4181e07000070740b29050b0081c243c0e4500c0760700402580041c130050200d0f040c07580e0983c42600c504003020501019250108003212188501900090b0001c400e002100611080a10082c07a10b21039800003c2d2a800640f8140d11541c6982c907031505001000c60840b5200300043c0e2080f545159080044a2000f0024103400c4c01c8280032158031002803c1c000c0c9020098084540300e0920071101d081c0b1621a50388410095200c014040d511554811000c0701580b541801d03070000e00095400c140031048040d2100070800850f03400311240c54820800c011090707a100d560501024a2030b4008550743d100d07440c240010f4040e502c50080713221181c1003003007503000054004118100350b85000304541c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 975329856 1250 975328606 975328649
    0x20a150b09190c1107050108220b0901180503030f040f23240f1f0e04020a0b03220f020402220906060203070215090405040503040e091b04021b0f0304 66
    0x710100d04d4100035800109007000700d54003450106520111414003940540365505035517210800328802510241001000c008010f5000d10031440340041a41290721311003030580d0380590300c2c840148889466050440400c040081407100c0c0c0d02c0050380030494050100c29007084404a084079071111860b4807400310281e00312810b400c0b000042103890300e61810150742c0e100b0050088400540501c114101002d80b828401030f003c050b08000c1c100c802100301050500e401000851030f10740c1c012110000d001c006002c08264007010b5003041c4041382e0700050a155183c100441c0e0115951400380d006800001c00301034070000f066810705070000d041c240c1c42c0a1512500403408607174060081c87d002d644204280805032402407040350401401201c21441c04401c00042019280c00f82d0f803c03030b003a51001ca414000309640070002d0b640800b0540003045048030070001c00300100300b4100c81d41d00540d400900030300c0302c050b00b203003109a000d0003800b11052911100a92650303513002d40b24003100c01c0307804985032164 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 975331106 1250 975329856 975329867
    0xa030c0c0e010506030103060203090f0d02210f0415020703020a0b0901030e1513210503071205060901230301090309050a05090615090102190c03030e040507020a150b09190c 76
    0x60700c0b8042c2ca41410b43e821030369140c00940c005000160b80b44211800733041000c070b040001d418520495401341404084440c8000110070702c1b10021299001c00b4842d000e01c0c0080b120645003100c1a251003880e1004106a00340c1c10071242d600003a4205d0201100807400050035001440038810a99003080003c128008be07903151061070303080074035406c040e0b00030902011106524141503805252500002c0701c0c001800030404074601d810a010036004401c0000a40e006542441c54101c504002e0106107000c10029030101e90500548440d24a00541c20400f1020a0502c224085001d4000c00115810b03003000b0300301880c58419207108002c0a440494541081d082c224002e1134050100c8900041d16800e0710380c075820443d0100d04501c146482d01c40b1106417506980c0b001d030700403802c8400301411401d000301611000d82c000ca0050741041c0034800e41c42e900103041d842d26a080070b05d0495a030540c2d08400e029151001700c20364071104a03828003042d603080301d085440850701c01c02c041080010081050700c1c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 975332356 1250 975331106 975331109
    0x30309040c180e181b0906060909041a0c040e0403052803050a0c05041208090316060e0306160206072d03021b0a150203060102100c030b010e0306090a06020d06080a030c0c0e01 77
    0x50203e0100c05d1251103042200811b074000070018201030401035101d010450f400821903050700d00200380d5180800c4904180070190300000101002072506007040c60806900310b002e08010100074000500c64030141d04440c0303503c00c5d502d0380c00600c41d101a80b2000107020f00f5003a0380413032907507290444a09119020b081210100e1b601d0315040200b200658407040308540011607070903090300410b00700600700e2414a080070090308450701d4119013010319500b814907000700204800c25480341c0520020b0382c00d0300018640d50140151802d6003081d0fa03100019100c800c0d00da540060000e41503010250440d0701074000e4200d6502522440352007600540003107070b44036004e64024002c414010000400c00b50290000c0d54000c0c0b040c01143c182542a2a9220480d410501c115001076550f4404515039a40480c0f6007103801401c5008000e91b0a08515094a0302e84030a0b000b004190300103a00c40312001103400101c0100004415582a5080c0e4180500003083c544403c0f604503c04040c00710f040335440340640d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 975333606 1250 975332356 975332383
    0xb0a1a0402270609040e03130815161116030201080912070221030301120b061206151f081b0307020a030302180d1212020306030309040c180e18 63
    0x8040c0c0ca81c01184190301c2a41c2c07000990486420481990141c4681c0100310940151074011a40d8202c1e05041c141417103510f030090703081d580055401c0000d01f100754021079081700c240c0380c0c001044110b164066420700059140d020490240303030707104610700311812001411a8006e807502d1410b41c4d10031b0056601c90200328910094420301380a55070150401402c0030003c810f07800324128582440c0442c86181d0b8009901c0880c0321124020740c103007004101c00440307410030800d660f60461124600d0381180c45140003000045c103801001116002a030b1007219100c0c1403940100c503998408401c88006004030400c4600084409040c441076880014803411a8451035041e0301178080b030040360750200c000c4e502000050f8640486058800080d5540800003121380f84a00c401d036000388040f0340d000d03106194509924558500c14001c100054502108960708140c04032030004100141143c15034440c5161480d440d0000c0e41d86c4000b0901c100310700d80044c06640c080c510064804200b40d550b41c0c6c0c8400704003282 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 975334856 1250 975333606 975333637
    0x601210c1403070902041811030708012309010b0a03061203020303011e090e010e160e1501030e06090601090b060c150c0c03120115030203160f0c0b0a1a0402 69
    0x4124110107041100019103005050380c40e1550303200c10703040070307a04103812010307840120120310310184520b4030911030000242c00e440c0d030031843c0150b40540b2801c014403540403808154074004080c010b881081109009000f0200c54441d6129038130800c4a4001480100c0401c1c0b81100105000d031400741c1500c15030740e0540c011403a50f0b00f07150303440c003034000502c00a45003c00041004682c0c448207004105d4a201d22000024000e41c100d00e5140c5401d0141d41da41d80c02d9000b00ca41803100d0708040e26181c2d0b01c80443c0401452032484040100c00409060b103c6071840d009a509000751010082006412a104882d00b030010403a2007080168038410b85011800760392085200c11400c00355480c203a40d00c0f410b5100420305010b1400c4041e825980320148104030401010014050500f41015421090311242350440c2903207005491406046541c482c2001482000b0842d015820720681c08080305c5030348074803403007401c1c01d0000c1500c0c0a4844110031120903600010348840b10705192003550b00031031801d40341d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 975336106 1250 975334856 975334859
    0x4030602120901090816020117040503071a01052b060203070824011b0c2c090a030c081c0f050105031c0e0d020a03060e030c060c07030c1707050a03020601210c 70
    0x44110106c101281070017044040780440c0001c0407413503840382c0d000c0c0700910340d22007042c0303040c018018513000705440b4849443c00501841c1c03610070705122150f030180c90025800d1013403e054802c800b0b00030f0005107113034000410803030940c0d88680c07828054200d00400c030101d50391900915582d040740c546502e00155140d0980b10710b105194888840550007040c1c01d0703a4468a070744610300745c0c180c00c1d0218545072104000e500c10303282600c943d299000c03044401412000801d030f41c0c010031403591448040c100480104080c411103c001d01c51011031542c001e010411190f142e8003032009403009105040c480c1c095103181c054480340b1250024541e030800d40c0c46100081401040000b44620040180d810410400c0b0101c001145442115109013800c3c0045480c0d6051030101442c0200091410b003100d50141b0000d00003039044040e2400380c50740320b64160b10659244140f50300d00e00410700c024007148203880d6054103140d000f10f0a18165400d94038480309001c120f6154000e10142505c0040240c904501c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 975337356 1250 975336106 975336127
    0x62601030b06040b3705040b062d1303060f0b0a051c050f0c041d030406031109030a0c03021017040b0a09050d030b0f01080c090d0314040306021209010908 68
    0x1c180c24600001740300100404800014613652140703102d41003404145008000c00d100d8001c03070950000c1000711000c1c0440c1d0504008613041c0c0c0204540400030380700c4070036821440d6002208802c86a5200d8449079110340c0c4030441c0142e510501d00c0142c494925102e0016002c04260054900f20704001e400d001c8000d1400e005d04c04100f0a041a910030012004013101c002182031042502c0d00e29030b480100082201c00f420001281e4020089454151a00200b080d4a41021003601d0485681c2d08000608405850b10600e40f8403424514682c03501840c8a64010064031781190800d0360b00a80b01c1d1305042c3d024013800e646036440c080f1355441c0d510300500001c0000700c581421952100484a000c2680c2c005170380c0340b6140c20781c40303810b00300480d07100e614000360303410300490085580409281c520302508060040b0b03001c5100d04091603005440a0022105240c0242c2d1980706140e000810543e4942d81da0510200039085400b580740020418004183c10003014020a000030381c102100510b018104503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 975338606 1250 975337356 975337361
    0x1080412090b0706060510030605010f1d1c0501050604020405150705070902030f0a23010e1e0a0b010810050a18140c0405010e0102010c0915020a0c062601030b0604 72
    0x2000820420416030214002c403200c4064900140305a03c082445c1d07050600300804800454000c0041500d030a40c2041a44e9226050508440340e03418055408081c505020583c02c6201c6081c5400c001e50294440301c84403500b8010200e01d00410080105454a0b41048141d20880c803d460348004c40142c0704c0d20840c9861b004160a40c0f00f841100c1c1d200d542c0380644010381c1c0040b40c1c01a600da40880030022203030900d00811440c0c0000d0141d1503502c50120300400340b04801801a020400711150000b04030040e00d008000d443d00d415034101101d03240a03881300000c0d0030903213216800600b05002264845031000360801c2a50002810160900c1c240f400212020003480c9440001c0750f21040b081320303049112480d85026003031820354a59520708104c0050300c032282007207809046a161004004040b0741c051100030660305040c1826181e403580c104101d161242141019085800c0140700040300703600300c1e101e03114046640d200d0f010406600040344840c10384c244406030420f00c440d0002591882d055 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 975339856 1250 975338606 975338633
    0xf0f020916091a0c01050a060e09030423220f06120f0314071208150f0a0504050a0b040f050105010e061231121821060204050d080301061d010804 64
    0x3c000e51810302c01d6583c01c02d030940720140d840000669454000b808040c5010b000e0980c084000b4004528152030602c01804050844080000015802140035a05e03591200c1c0e980c1180c13000c030720040b0395502c0d02132804001c1c10440c1d4234000c2145400070018144020b100070403103603500f000c220b64640405817000c2d560788031018080406020200600e0b070000d100e40c00c1c06441e040c0c49075103c840a140015111100701000c982c00c80c414140f03407020000a5849030480c50036208165000300700b64a82d03028400c0035088240f0a103501a040802e00f01c41c8280f075a100034100c0b00c0990703640c1100440042030203070318070031507844a03500c007a1100004c81c0d08100c40130340c007031030000c010784410100039000c440300406030002400c94a080898034156405075000c0c40850b90400c117948021411803030100c1a10518030140d440440c195000340d020014000c565069600130540506040c1d40031481e4640340c44039610901510700030607003042040883c81010071300c0102210060711000c0303003900d0740e0301e03201c82100c4c07007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 975341106 1250 975339856 975339899
    0x30d0c050303240a061e0e100f02031605100f020325050405060c032a0c0d0204020702060a02061e150607210f030b0321030c070f0f02091609 62
    0xd5010902103031301d5000c00c1d10300070000780e0355412040d400c4154842c2c50500718550328080041006403103100ea03407491083c20164038107040000160510b014280c1c10350280c04502000c600c0800ca0355020311201148a40b064516110200704907020031504030201c2c0001e442d4003826400c801103a00086580071071600c0d920195042c40c0b03080c203036100002001da86c0070f4134a15021b03400101e481c4c54107001c8807504406540d042c107454810055030928480d80d60a40e001e150384120a0744500c90190f455990480d100c194018000d0340e07850201510103943c03080241c40e9888000c150901c00d201d040c0d0314220b017902401010010300084448442000920b030004081034401c0d031241401024000d03441d04107440091856110861605071650007d81103841b40d0038035034026000581c1101c0c40c0311003507048111200008103d19141d44034100100007a006900d0014030000072003c8000502c0140380301c0ca804540708503011002a41d8a000360800c00340414031100200d141c100c018040740102c0c002803880c0001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 975342356 1250 975341106 975341161
    0x70b010b160803040f05010518030d021308010e0309010801120b131103060709050312070c0608040f08041805010b120606030a09050717010501060503010e1501050d05070e030d0c050303 81
    0xd8076150494554070136103040319a0064a40000c041007020701405030b00c0f440603010fa100301c5c41d181500e03a469102e1504c0010915500081d581c54210019a052001c1c011017002040005034203d0340503031700d500048102d0b0115900b4000052520b003070708400300c1515442962940c580c0c56850f01c8800820540e0001c9500c40c0980041102c0ca4a0400c004c0d84035003410351b280b07584039140c10309050421085652500c1442820000000411001c090180032203e061414030403594032400d06020080b00c03002e005080c4c500000c2d000581c0b12032909481d11003498100200310ba6681e075420443d0f580301d41d10118400520300f0000600314a0494055a8030404100003c00c001b002c0380d0381c06003440c0f1503421098400c9280020100c0c0c00100344a02d501514090600c540765504080c40700c5030030000280940000e04207000b45d004240d20400030384204a041020a004e1428140006004440441c8e0840c1c041e2140d0000304c0f107524031400c11058000c2d0800b003d5032554648840a5000c1c0303848000740c02c11080f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 975343606 1250 975342356 975342397
    0x30c090b0d1a0105070305040e0402030a1b08010605010e130c030e01181208041a0703020f12190501050a0b1e04180605041a01110705042c03070b010b 66
    0x40001032000303a00709240080e0030098800440b6854041c0c1051074100107050144500003a0000100d13400d44103030380b4140034030365106d200081c50a4810300000b0302c1c841e10411868500031491003078000b6145054000d001441c2c03140011240071401410440c1e0190701e040c1c1408580e032081d4000d144690349894003098050301c42c400c450a45001c00600d00f802c0c80902ea4900c10b118a51001d6410074142e40303403401890919031120002e00103c12107980f103645014011980c1c41e4000d9048542c0d14000400c80c5858800404035002c04240844164400f03410b6644450320450017031007184c0c117942000788000d0032035040c9000294150466104c4200c8600c20700030310604035500a01070b10051040403103000d480c0380781308082020341d0910b501440c081c5003030a52400406515000c0045910828a0700c00c107040303421500a460b10501c0d031300c15504145803040154851040340c1e420409140b680803850308040400c48910f03a00e02c204100a072030103808000600000e100b900040207040c00d054213101680 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 975344856 1250 975343606 975343619
    0x2a0207081204180905031603090b0906040e15030607090e0603010501031709030307060f051f12030f0201022b06080f1c17070c12022406121e0625030c09 67
    0x142e000209403600d1f0b0106042400070558004481c00280080c03504250a01072968081480d9002d58040c1c0800007030020000366400000703070180c20b510701c00241200d545091062002e0076902c040c4c0141000f44030040002840c0c0d040501460741203c0e80304182e120082c0c8021103c880c01e411003042030394103000420070280458500d001c1d0209194030f00c400001d090603c5a460304000c0040c0c1182d1203002c890140402c071025019070708105d40f603014103007803800350402c02c0100d00900c281240360012556800e10413040300d0010255040a07440755400b08899519104100e940390910145c070045c550100c4504100c10354041a15144205a801d007016000ea0902c420400b501c02115a9400641311540090900c04005100c49060006002a040c00c0141b0281c0c4403000710b402c105c0410300d0f280342c40800d20585907481c190030380ca007082003511101441c800420303900b0f002809885106200ba01c01051100d40c01c21a41c0d42c83c072038510040b801d0f5107010001a0b01500881c0d4030002408075400c00050346 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 975346106 1250 975344856 975344863
    0x140609090c2106090f2503030e130c020c03060c09030c210618102c0309180406051e01030609110607030201140a0506150d2a0207081204180905 63
    0x44d180c0030016000e41c403c0c44070040e02e46404040102a1204400440d9024039541c84c068001d694040c54804591130aa00c08900c4114842c0076034800c142c6040710030700780342c1c1e0f02044126011300101c041d00c1441d10340c1620b191503130003085541a8103030007881d480415407030082040111502c210040084006041040e81c0c180f071002c0f41c020440000210071411260818407982445a0f030f9131508003e0b210801aa25010014021982c03561201032612824291420419213482c804008d042c4809007000580c40503072400184c0d0300301d41081c102400704c0c0510b13811003d0785040303040c49040308119078610340703d10300500a8280b0070380c0e909940a801024644881c0018040c0f140203400104800329078480156418000902400250b403400d0240701c15580c850800090078400a00d2864480e0fa1300b070510402800001d044c031021260040507501d0402d0101004000351002d602071b2100180c0e100c603065102c0201a400c03040e0483e0810090103040c040000180c0c3c640c0e055000014a506599121840e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 975347356 1250 975346106 975346111
    0xc120c0d0c02030f0a0f050c010305070912020a15180b0711090c0408070b030f0a06081207051606083408070c021021021c090321140609090c2106 64
    0x441c40e00d880b1206c82407190401c0030480401003840c0800540c40d110038010711540b424021401014007000c0000250364490500d03e01a09241e4440311841200c1500038207600c0d5018130251840491403400030b075001801c41540c0849820140c8003004c000441c00304030003508001d010711b86001c024080458840020840180a07007018214035036281400c1035041020100244501c900c2401c1078401d003e60500030408117002a11560302c1c9481717051601e0b283c0d0800c000454544025041e10302d0006d1140c0c0d01903607540c01512549080030000c0c0407045120801500c080c0b114a122182e00c03003090508e441900e000ba400803803850700e0b480d5103541d40c2c001592030a1110005000034080421300d00502120f410800845d0381d000011441c111a0107201d20301c2101c2120071070a99507546600400307260240110680b0744401e0b00321503203240b140c52200c200500c4515481c20385070f9075030400921282081c1c1031203409040340800901c03446825030100b0031807010040540700310554041c000a00b60004206460 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 975348606 1250 975347356 975347363
    0x90b0105210f011d2419020f040f0806220f080705060402010201150303020606060309010e0307080d050a052404110c010f050f0601050403120c1202030c120c0d0c02030f0a 75
    0x1e1302001a4038130300110051100e01600a401c00095100030f091030101410000030403031244081135540c00038a04610401902c031801e014000610703110b0614010004006644234991b14008450b122003240755910000c603000900c94820a000401c01411004240c0019100d07040c4c2d000042010740e5410101e411046c0116a19482003050004560302030040c0c000e9543d40c1102000003e1941c0c400940d22500504054051032001005c16901242900016070440300d040c11680c0d59803451514015030360000c003020451a00d00004110440c0860080d01d01030000c2d4481106e40a680000b45a850850456030136072040d91044600c45114541c40588084102600000350045100c4012425900d00400c0d031208000c0c043c040103070301d0382c001c8180c0b41a203030000180180b0804694080e580c11418120140450350410007003003501c0d0b030010051840c100c90101303551401d500041d400341980107140c00c3c49a0703608008012424188103419110380c0c2030000f0221580034003030f150420306007000d801054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 975349856 1250 975348606 975348611
    0xb0f0403060c020a151104060507050a06050f09010e0309130b040f1109120706050a201501080c030a030203041403100204090b21030a030b0f1005031603090b0105210f01 74
    0xc0c0912154541028842d90317184418010788034010b601d43d8841c840e0380118018004080354000a1010421888110700e50055081081d41022222404003c07801c0362030007800e6080c004007101c078240100584d28815000341510b20309800c107212030382c060601c1c21300980d00103036a00d5501c00b0114050043c211130740304581c0141e40c0d52074200144000d0194880d00000e19034041e02c410810240d2000481e0408002841c080342040502c0501300d031200c1c5020201195445940482c009030011040500e040700ca09034100c801d0820803205054036007440c000007a0243c1c0044c4420412400c0c416102d0100764402020380343c08080b00c000420491700a50400007010f070b42ca0100c1902c50400030410440c210300040000114071f0004e00181d0b4074840c590180c410103840d1420f0750740c3c1c2e454015000e00c80400090240c80c0100300010024101c1e0411561800036100340c2c6a9207031800d00a11416800035080340c28044603a0810b0309010310304465600700c100311000c540d0043c0103c4803c1c400720b10003c100c0c01c000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 975351106 1250 975349856 975349873
    0x22e050f07180b03040b0414030f1801020f070b2b0606020d0516080a030603060c0c020405070e0607200604090203090c1807030f0209030106081e030708040b0f0403060c02 75
    0xc189039480000d4880251900000f0300c071140c01c8a090ba039029500400a030382c113503220700e405c054810030181503006a101c003150842c0c2400d5000058135650143c041c607003c2040402c001280d443c0d44140300b05c541a0404a070a1000c80784210040c02402d20915190310b1070b1100e4059040c040f41c0091807494840d603a10001d02440d0380c1440400104d00d014138100742040124012080f41321141200107081140c000b80c101c2d0703901d0203a00180000c40d0000760800141e007035090003801003250308a04900c5946402c0000300e20a0050803800c81d9a00040e010038104050b135525002e103c0c151030a680e0154030350542144a030390b5400000c1029110315400580c4030300b01703400b14030726104513030000030311401c1c40726a03403080050704041c035507444221072801180800103009017100034891110f28603015400c081011903034000c00145103084c1d210040303104140c00381003003000f5201c0c011000010210b440800042010b005050003810781a000e50018501d815034a40c1c400c012940300c0b00400d00986c020b02030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 975352356 1250 975351106 975351121
    0x60b2b020406234612060b040507090641041703030402060d0c0311160b0a0b01020a021e0904062f0a050d0905012c070501022e050f 58
    0x140e000404010841803418204952154080304e0010000034076800c041c6143d60114800903000d40c1c02000081c600c0307421100a070420b1030180c10960b505600880c204404a1040d1348a41280800c450031542e601e03444c1c4140d0014200c88030f0781c0c1c40100104007011071481c00c1c5402840300d440090030b171541c40650b0b101d28001c00b1001410003c0303001000c94005104100241c0c0b0303080d08454100009040005130011a154290024070480040000d16480801d00403840d440c5804042c4171039004040315082c903507070700d01a502950b000c0d07151107006811684c41031005050110a02d28230710380e40450020b2203280040443c0e402101100d01384c500e25115640840c030a514a6000710400045426007a9203000c194443c030b00512504c410f4604120b0001392103410000c2035800810101c0e88031000b03000540e5140c422294180d000e08180c3c0c0007890085807030b030030b000c0005040802c90b42c06030003522400c121281700f0300d040c8074180d810802d00204003d00c06d5040c041803113400d12440c0714002031842e5041892 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 975353606 1250 975352356 975352369
    0x608060601020f01060302010e04051f0803090109080a080d0507170c07030806010503060a170304090f020901081008100b04020d090b041b06080606030405010e030c060103060b2b02040623 82
    0xf04004a0792500c0018009070340c1c4000504466042510041f9080d00c402c14100300c40f240c010521034a88079619404103074480088000c0c040b29000340ea80b022420384441281e6112203e0000040c080f000400100d10820040d0300016070002c140c3c18409024207040840c2e030880181107407052040c0e24009501c508054025180d150416800e1074558214a80b40001c01d41012603400341c50303c1001c401d2422410101c081040710050b0804420902600b08400180406908006000b6010813810340000d841401000505011101c0703002c000c001c9900c00e00a2000101030746466260801e40801510264551034007032140705c0c1d482400844c07a140740c81d0500103c3ca1036003580c14842c00170180410442c441e401040e0302d80140045450f1075a03034407030740340440c01460b00a480d40301034000490180e242010119156048034003030142030068041e0201040000c40c0700341c0c0c10000b5013000361089003215003181211103682e44046c3c000200d544d15111800c84007201403001d01c2d6186215199001c1c0e40c10203c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 975354856 1250 975353606 975353623
    0x1b120709030c09020c0613020a121a01060c05071502010b06031302010905040b030307110a0509180715080723040b07020f0603090705090703271a04150f090204060806060102 76
    0x6101142040c9075176182a40f900800341c00d0b2040508840111010740d034800c20040014030041144050550380c614255a200c41d0325100300c007442c2441e1000080b50b600807420030000e41d0340f00002d002c0c100d00700ba40d071640a002c0242220115136070b6018013051600d4840045015600300e1881c4200c044032440014401c07083e0b60402400745040001d0105181c400000750303650181d12440403406c0d48113102c040759028000c0c1e44010ba00c14190002e000240000c140d5801e40703020070f00152003040f500c4038906401c0d201085545000102d450f0001864144101c0c005036030008512003080d42008146003440141c1c03c01c0c2c01c600c0f985000000d0500c210315280b0420740c2410f10548030b0b1415490140c03c8140c46000078800c0743d004058100c0007803c3d1034425800740840d01c1280c025020071950b80c9158980d03c1075907210440c2c0804041c0700c00d0080b4038503004803a10555000e01d4110f50160601c0501001d0030b00c203540c00310002d803220340301d10044c0d84034081ca80c013400c810070091040380b500307100082c03422001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 975356106 1250 975354856 975354869
    0x90d150c0311090607030c080f0306030601151d030a06090311010b0906030a0b0c0706050f04170c070b34020f0a210f0b090a02190e1b120709030c 64
    0x70841c0000c1941d9554060f144800c50403a041c503290700140c242034a107104207100080c50607400040b0081d100b18000059401002c080d0204c403650380e03c40c210036904d0300ca0004c08002140c503040e0403642e071511604a00c0d6103040d0140c00c0c0d0f0002d4405594010036103110f80c00031404581c04059490b00f10b20240320b800c800150881d010021400c0041c003007a118481400c025040e00640800100c070700d014039044911080e4031144c1004246020041ca00728150190341c111411512042696036103414441950b40030b06405001e000c0c0b65161408418041d8059051120b0702c091681d07408603140c0458031030035020f0a0061008140b00354070310400810140b00005144524804c090520525211001020412804514480d0b102504c1c0c00c0c00d0250110110000f0b081c3d0302c00400300300d9244004102c07228103a1080c0d64048802101544041c409002c2e4003c40750390300c11440000d20b449050b8079160a0080c0404c00f2035141200010519036419003c40f00c90020403025402001045602041d41006101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 975357356 1250 975356106 975356111
    0x230708091b1e01020a0c0e0105010212032205070510030e10020408060403080c131203031a011407080f0a09080d170403200714031501050603061302090d150c03 70
    0x7100000601100200410960b525825000e03003003180e4020080c898501e40c008000400715599810b1100410100340146c60060203202000641540f9505c2520300400c21429002c03081d41d002c203050035004c0703010740c3c050300c062040d07c80000d01a1103880d04010000e005a80200b0344e0500030040c0e40c0b41906a41d4004032480c410401080541004202030350408e50601d0484062340f10860791a003140106400502c80428601000a82010034214801814840c1d00c0030301c07400091200b41c0c00da4003070032004039011800405441c0580080355000300081d0340300b00080b0b800c010004030010840e42024400801146041d803081c00321907030410407400700c18228a0f1448815440440d00182c0300c0e005407004050052021004c0b0400310320030011050030322031104840c50b0580c1d400c181a4110600c21980e1b0090080300c070200303203210801c40c44030b0694401400c0a0300e59100c940a0180c0305070002100c0380e907a81d0910551000d50381c2c28180741d120b180118480c0d6030584030070410034201c17052403290000317151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 975358606 1250 975357356 975357403
    0x2901030e031603050a09270c091809020111030a0e18010311040b010221090a05030123040807050619050106051815070209040b09011d0c0423070809 65
    0x10702c64003000300358950502d052610341c4c0205074241c0e280d0866030800d40074120041103108403050310303d0700590418500c22043c48546c410f90350545e08110280a6102d200115141c09071600580d500005143c81c418908900d40a48402c0042c0c01c41d0882c900b26000030701e1060120f04c01d0300d00300034845061036000303100c8031807940745545148000710070300c904038002c80e01c2e861002c040c1e0707001b445001d03044245054245003210182002e43d025030700241000348100c004800c007049900701440340c4042404000c048040b0700303111030380e06114000c00a108030740c0303c013040181d0000100d040c80b01a0085214507450280241c44c02c040505452058000d082000030500a003da01a445405011920710030396408450541049a8608038807960f04013070341200d007410030b0008001e2081c80062052000306c008208901560300d4203906101542101c45159005c40c044005502e42a802283e07140115000124411a4501d0f03080c4c40e00f40481d9400b010036088410441c07900001e0000c124804c0d5901154044913 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 975359712 1106 975358606 975358627
    0xf0c0705030d03111c060f090f050c090306131b1215050c1c1d0a12230714120a0e060304030c080c012901030e03 50
    0x30b1040c4110841180d100703106410240d20910700c10341c50000601038081080007814042c8841a6594200280032104608210000c002400d400b08028030040001c1c01200d00c024076400d02200300f00150002650081803165000081d0b1612500c0c403041401c01c003e01803419030000c9401c1c1407464022070b00344101d41440030340c02d00c01c4014a040620241d0180b003a22000d80f6100c0b8840405c4c401d0400e00a00424038010720300420500244d2031010700d447c0e0b2281b1141200400894026103011300501449038140b00403000c103402c2540084d2640c2e200700c01c28884800c00361318401e00210341c240c1000b0b002c01009a0442c1000210340d0311a8592191547c954000d4901401284491207904040d06010042c2d030300c11901902e0b21911125592101c90143d88403258030b0103a0f543e10402c81040e002d21211407c0b82c1c0002c1c090100c09441020005000c8480d070b80b0056600358401d00002145 = true := by decide +kernel

theorem cover : BRFrame.Cov 975179856 975359712 := by
  have h0 := BRFrame.cov_init 975179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 975179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 975179856 ≤ n) (h2 : n < 975359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
