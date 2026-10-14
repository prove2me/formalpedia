-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2285
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:38.975725+00:00
-- url     : https://prove2.me/submissions/c98150b7-d590-4cdc-9a6b-0127184090a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 410791366 ≤ n < 410971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 410792616 1250 410791366 410791379
    0xb18041a150d02040e011e0e0d050f03060d0209090a0309080a02181f030c060216050108060d0503070209040302070e070f05032404060b0d0f0203130201030903050c072402062a04 78
    0x4640074985000c00102101d0010891f4800e80185502c60600e41c1c0617040404800b80090500e1140c040540f80b0320070b0000000308180d5030148041c05d4980c0241000c94941f0744044503607aa4041081d09401182080c14001251000014000032156002d004040905080c2503084040c040c00342c042c2c800f0b000315214120080321000079079030080d8020401110707000c0c86c000001e0700f4141a8001c030002e085038070760180b01c2a40c201003040d0f0010010b4590b6801241903050036030030f501500d08000e50007034040003440207159000408400b0755418440507201602e03080820b03606181e5a00c400408540207000145855012105c00c2c2440750055800c1000c0b14050381c00901200c2054000e218010400324001407142410700c0b40410544803803034118591b050138406a01c3c0b2400c003617002410103458502d41000c041c800c1e01501c62a0180794100c421131500c89807003000e18001e241200036410740311440092038520015130540103410309500020343c0c80c469034010f0003105040c1101800c1610030031001603031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 410793866 1250 410792616 410792621
    0xf04090503070605090604060e2a01091d01090b0108150d1103060f15040902010207120c03020604090605010206330102031c05012301020d03020307030b18041a150d02040e01 76
    0x407521617025010600d054a001c00480d02c40e51880080b680c05200800d01003164005442c1e50110440440440e440c1140d0040314018096000810064042d100300318011001c0034005040c0d414800090084c10a11001122207074030441b0070503000054012040c0290402d4103185040500500c00703d002490f00c140440d181c0001030340c6403420102d080d810002a014804641140b109003103505003d6195907400003541c074513482c09a8420b807050550200308125070441d0b1a00219400303007000303441d41d0b41ca981c4031340181540c0c8640c50242c0200400101c0c2c070340121903440b40400e8022031030940f0044141e41042c01120184e620b9055100400c01280c2003001349140018200c039507030002c1201c1d818208883d403540c204002c00f0001000a01c040c180aa030085100c00d040a040d14005841f40da840c0b4049020346120740100b034003d19060280c0301412041940701e44141e014078003003540c034141c0a00841240000301d403802761045426600340686c0c03030060740102a140c00100081344603085000c10f40e08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 410795116 1250 410793866 410793871
    0x3120c0a0c0b07060501091505130209030105041a0106020a08070809030c1f110d0203070b1f09060306050f060a0b090102010e10050103020102070b04080d2f030a030b0607020f04090503070605 84
    0x2c420000301d4080704000260107006d000d00300c3c100d41440048400d45002c4035106280c06041d21450300010186620b504950640b41c40c1c0c0c00c0103000b4072040c10181003070360b8468540d51101150803030b4200040f80c081c3c0009050380c40c0543c0081c20510f0002c16850f045010341003006c60079814060604014a244c0e04d500300d24185580e4458090682c980c000300c06810803d11030050170650b00081b95006000360040107031403401d071b002420038541d50b0f542c048514074021910701800c0b58260043c0c010400440c6544854140d03031007880e0810080e122105408080401101d915500c5040100300307001c40c4481c04003038071304103c040c000881d445c070710f0954040c10b040d82c06003881c8010390b60b8801002550703810440c05c4020320f10000c095160604141629071500ca02402c20b500340100b0074070388003420a40b403260f41c04d9400007584c01c081511107481e429480b03610080e4488002070038840401350390b2625108075010750358003c0c880400b1071200b10a10016192214080d1001d0006106d5940820302074014a803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 410796366 1250 410795116 410795129
    0x10020a0c06110d140408030a0504030c211d030a080d090609080a0314091c05120406050109062c0a060e07080603100203041a0606270f04090203120c0a0c 67
    0x3603d07506035900200c201d0b0003021200200d25a0241030001003851242180c0c0c10211406001c107244d503483c241503460a061b174900510340d0a47c0503070050b8008540c02d0386c100c51403e40d61000c40c0f00c0700c0d0741820ba0b40344110000741b56241c0c102410301c10010780b02c400108448502080046030f203001a07140e80c0115110341c0000e4a020300c0000b1804032007036261003006054440c0480740c09450411882481e500c44298000c00742d45140c0000c8186003900031070640f010661881054480c62502d482d181015000a2241c0d201003804c0c190040303500904503000c01c0c101ea002003d1482c0c0d1035154040c42075580405803040348011b43d0303a04042200750451010f1441120780c0d40b134403a87c0c0d04144041c10b1230b2174a2a0040d006e5144140240000200a00c01d081780316030701c5c3d80c034200300f075101e000000d107051281d000c0c40300c5141c2612842003459621240d42c04c00300c2e98112691841c000ca0501030006581449500940c983c1203551003949000b45140540301c035045040c12075035500c446036030302954a0360079000341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 410797616 1250 410796366 410796401
    0x70908030a030b0906270601020c04091208010509130308060d0507061106010506030f010504020702010e0406080c090921030406060f0e04150b150f0d051302090108010e10020a0c06 79
    0x10940e0074501c0344c80d41c220744250f8200300d0070f603850907000580310159000f0480713803440d040106889a00c00c01c0605400702c0300500400c110760680c909543c80310b28040e2402d000c43c4000c800000c3c00c0ca021020f6520511030100c402c910101e03e941c2c1145c080134010060b035030002920080d400440c5080044d18060318094071580003032070b2024140b51601034141d01281c0706070300030010005d103030140d481c283d81151000e0780c0c0541c40c0c072100d01c0180d80e07003808404000d400c00e00d42100041c40c01c1d0f0004421085800a840d004404d40f64501141c1c7c8541c06000d03000c0240c03648140c18814900181e0003150b0003401081c00041158580c00003010504080d44140c9184003030b40107000038000405c102950a00101904122000c548404900c54800d1a0810002c05802141501c0d890f10150300715004007240d000208254508829012410780100c5000c1c0e01600138a400401c0c28101480340c4088002500018100848040c6c0b14101a5010782108030403c94000c1c4403000156483c00344007400703003081105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 410798866 1250 410797616 410797631
    0x190c030f0507180c051b0a15061404050f010608061302030c040905010602190303020d02070b040f05010c0203160b0a1116020f010e01090b090612040f1e0812070908030a03 75
    0x48a1540700d400d0b0740e50903d44c600b5460003c2d0755004412900d0510b0240b40c03040d07900841ca03200d581440c0019002412203604018409500c070b015038040c4080e145100320244161210000340412a40c2c00c0300c20300c070028040801403081c50301a865803070b4004002070000364050800c0f01c0550581c2c00580e0715144514000c2018001d201d403e004441c00b40070b10340b0041c1540c407482100e0380048541950045c0905600143c2072030780480c10340484983c11741044071000c03075051614003449904031880c015101940b07010440855148007008590303402031848080c4030301805580310204408000341c020020300f9983e621a119080c9030308080e0039030000440e4042c22800341170040c001c80002441d0060304201c154060484036a03000b4100c141940c0b000d0b422141c44514a0012805038403940d23f161000c00382c1d00041104200c000c8410b44000c0744901d448590050240071a080050300701e110081c4500070901000780a18a4101603d501c4420783c42c140d1016561000420b0865106400100001c3d440703000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 410800116 1250 410798866 410798879
    0x280204050f0111030a030f0f060807030209010e0609010303030b041509050609070f05040b03091e030703030605060702061206040f050910061d18030f042d0305190c030f0507 76
    0x1c00300d40d400820708000180c01c49282a2a40724415001140c1c2450340c0c4078811a0a8030080d88564544140110100480c030348a0303201039599010391000300d1144108000118039003d140d2401800380c000a42503494507400c43e5030a8000d40307103070b285079a0080d0b42c3ea00310300803103060a04c40d14000c0003200e00c005514100441800400b20006000c00c09029540504111440c1d1103406c98044076004010365440303031a4460307903a041020140c0900e041070381c2e0007403d6101800210082a81c1e61023500c1c1004a00d43d64028408540180c84019600039003e0204440000303c03030b017845500c40304c010400a5400c88402c40d0000704ca2003940c0d01e12065200740da031040742041038401c83d800b4020030b40d00c000c0b45030a8010040601c40005158001080c952042070014841c02c00035204641e08264402d0340f0b42e07032614044100c03400303102c1082c2420314070030205400c1d039070008840f50280c0790010081c01c1a069040550344441e940324004072400100e1044c00804170b0000342e01d0902151048002e080414540407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 410801366 1250 410800116 410800129
    0x6020c03010510062f0105010f080a0f0807060b10020c032416110304060c290a180b0c0901110d080f250e01091a04090528020405 57
    0x2145180641e252100b03008203c560b4101a4040b00c3d5140f03800303291044030050110700c010714403580c82110b85440c008501e0088044d0007a038161a550560b500c00303d51b64034030055455078030310f10180c000c61038841c01c4404141284010011580034540100703500c500c05011409030500925040c1c01a001407120301c80c249010b02514143c401c03507080123101c2408005078500f5150001c0c00c40c0c142108040001070003140200f001d040e584c002e01054070b0f2150754905c0060300808090004a0b441c40403440c80e030007403d0110f182c0146500074048801c1c485d6035100c110380c004100924514a801900250103400584100043c0317100ea00041031682d1109051000074224a04c00d88090740f040d04541400e0030182c1d40400c2c159030090300d6900c10003c07a105d086042c80c400d1010008212583c03c0103889000140e000b0004002c410001e83c1c40402c0d00703695105516120900000451076104100320403c4071300c0300742d0455030300030f1a02055151201501241070054020075005a14100d4000c90100500d10f0070701c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 410802616 1250 410801366 410801383
    0x20105060a0308030609220609031404061b02060417010603060b0603060913060b040914100204050a0b31030c05030102040506031909050d020f070902070309150c080706060602 77
    0x3500e501850303505550341d0301c00c5400010b10b800c0c046c0303516400140f80c44240640551070030001c1160030b40030050038140800640030014054000c941c035120340c0301c44c0300d0036a01110222841640c0300c40d418070510301021008036000f0070690784002c00b070101003002c0b0854281c4a107c0c045040000030a20b00d145000819200178881252042d602402084890317250110441c2e40800044145100441030f46095001454220000340e0418a00701c03030328081140c800f1000c4e1408080204949000803043e07050402d92190340955500443d103000104170222000c80034100d1064280060010405900c182e4035445550828850503602140400c0044c00007070309035103019020aa00030340c82c0504000200b206071101400b1245140c000001656100141c3c1c0d11801c58150b2002c1503880302c151040000b50b490000b2000c0e40b0140c014484001111800c5108603600a80c1c540c07144941a8074141d211a0b080209403611014081c2460721b450005001e2002804440c1c850710700001c41a0030040001e1501000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 410803866 1250 410802616 410802619
    0xd0c0b0a23030402280603020901081321030219031b0c0b0402060d09120201020a18211a0a02070c080a0c0b030a0e120d0c050319020a05070f03090602010506 69
    0x207400002007112401000c4a50064042d02d290a107102491980030310641c9540100c000da540090000c58100c0e0b040e00200b11030102681c1e2015191581d0a20145042c1d07041c034024590100c550003605503459040d0305030072840c442c1c14014101400b0700c521580010007442d607400040d540d0b02c1101e01d0a0100380c08050b0400c4a07140110810303106a0368404920406003000c0c1c03082e400440c400304107900c40d801c02502c4640c005203a2201006405010303003c1d4010482e2180071410011404080b6154040e0a000b10741e03c1400c44581206840028004074034111b0003918100c3c0800c407011104510403111502805d0090001a60b407045818008080403440d0410304691b005580300001040c4403034041016585060385437a9aa120104560004c015900e10102207005e11010004c000041101410f01107495490a1000000742001207a80344000c0300c052101c500c8124940d201d010309540a4194400780d414414074000c51511040c07015a144c8bc0103c001613407404081c0b041035420b0094a400800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 410805116 1250 410803866 410803907
    0xa050606120a03020705040f020405040c2c030304030602250b09060f270f1e0111071502070303060f120611041805040c03020405090607140304030516020d0c0b0a 71
    0xb250b4000b51107550a01c0344511840e00c030714a4001e001080d5040394014000148100300740140b00c04082c1501c22002c0ea444182c1914a51003c01446480c04401c15000014061864182195070b2031b0000d410604551441e060421003000142181c42c1d8001249401281c5101d01460030380c4503d413911400801a072510502d441c1406907445040800c0c41c40c1c81448a280020035800c1d00da890715000d5042c1c401c2303000748240c010b46800f8000c40622040c0c00c0d0441402485420001040300201e8421490010940351031450382d0514603010798040c00724a0301c00d160100321b10b581da1b0303070450610f81c1c1d41c2c01c4001c03086036441000c02088560720540c101011440451070901d4030b40b0350300c80c1080c0ea401c50400c42c45915400010304200428010101456004008100701d0400c002c1d00c560b604000c4940101242c02410b0083d4010110740c240e911413913055031807a00e1b02e24a4030000d40c41c21034406040340c0200300c0700007110004103411224806091000304403600e604840d60020007910b4408a060700341d44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 410806366 1250 410805116 410805133
    0x10e0309100c050a1b18020301300204020d0f15030510020a0207080607180e0105060304140316081909081e070906090f1410061d030a05060612 63
    0x12a9075040c1e9045048505107071200b0005810450f0901c42c1c1c10000600703c60718960041c00e03660310034540005a910407108660311610145512040313100c20b028007403d0880409006540c1c4000580b41c881a903040c0441e454400c941d035001c1401da8000c00c1c00c1120030b44d124000e0310340310b0070745208002001601d10303400102c9500d55101c280d1920380301d003111141a9000940d4004081c020400038000340b244000700d0740e543c034108800608100480c00349080e00e208511000880301105404070f811384000420003461a100d0b1740d148000303404071049842050109010b95400c40d80b508001800c01c9005032240c5075035542c0c001d90413103196288580c400920103107910074400755400081c000f43c401c4400e00c0c88000c501c6840901072510300a03078000108907040c041702084041580c2c00c101d11310704402a0a114003c80102c850110180072181a903401344401010409640328285032030283d401c020030702e45013040e0100400d00340505c10340180c0340ca80c404000d2000341e04203c08082c5025020f00013804201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 410807616 1250 410806366 410806369
    0x6080c160314040509010803070302060106053405010203070905101403040b040203160b0706060b0f0724060e0105120f1b0a09090b1603060b090603100306050702030309010e0309 78
    0x85400d030203400c202c64404541c011440c9201103401a100041008100c0e40e99118403a0760703580700d00c1f4200d0040c040e101c00018454099000c0d514120750380101c82e0f4001c407801100006801c03800c01c11440c10b0460425150210b00c007840114050049075949082d0f9509000c203105440c00100c220340100804100385188030040711040da174010781d2000901420307854500019181184500800c050010303501c0c1d00090a041c4800205085441004144410341e611014100030340038449018034035441c104004000603500840c155040c0c2041f11032116811491110300046034580e0700076039a18043c04005001c18603040803d4000c00102c0705c000c0400c0100c10500319100d1098040d1401000d000403a800490381c0c802c04124081c2550709020040902a42480151100b050301e0300c002550741101d0382d1a84a03c24000c10781603400780b02000f4a0645100300344645680000c2c801d40b0b0b8045458000300c0011b15500a0f40d000d00100e034015030b240e040c0800c5807030840307000402c00030345a4820001400b19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 410808866 1250 410807616 410807647
    0x3050d02031927030507020d12021006060314070f021006150e0d0305090613090515190312050c01090203121e03040b040201050711030109061a040e0312181606080c 72
    0x91340d043c60810b45500562002c41c10307581c92014001c0c20110a0031158030303007643c0000e20101c1ca6044850a01c10300f603031203900741e044448010315503148000020004003584e0046880302d0820009104844103041081070600484205802c9848000300700b1041c050301c2e40d400035122820a904075054440c0b2070843d50080c2c00f900c2030459031409524040340c4031910b4401d00e02c04000602815106000c0c5103446c0707814281ca06055030391603200d020314140000d01c01941c50520003e4079401441c00740590340c2c1d05406d480705d40280001c01400c0d92140d0308900141c4052090b0300300c0c5419801c80b079441b4020000c82482007815075161070780c1390038140f0030040031411503508183c00940a0030a01d581e54400c0c04d20507541181d0310542e03a055820a4840c408018840d4848900b1705948480ca03440c200010041000b554203400c801103095209000940500c140a00030942009900d50034400c401d04c0f005a2609100c860450201110b04118040202c0c0e6040703031405511592080c9210300d40765040c0741c492403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 410810116 1250 410808866 410808941
    0x26010b0d0c090810050610080906310b040501050606160206030403091706070e120714010905190608011a16020f04020f18030106150c03050d020319 65
    0x111580c035410141600ca01807880403003e40210300644010205090203d80136041c1900c180e401580c21006100407240b040c4c100c180102e01d10405400c846d00d401032041001c2d16824440034400400c070a01c01c80032065403074481181da100301c2d4000360500d05410003a00312180180014000c203c100000598041c40300300701c403003440d03040752010384940b40d42c181260380f040560000107441506400a040d80b12002803a00d00ca03030b21741d6036550000c903808014099041505003440c0e0403035110300000e108514640001182440061501201d115690310000d000d50310000790b4171210b280e0104040c805c0503030150010b400740000780700110300c80c0d400342410002d601c902480c02209032065041d10003103503203d03402404a414014800c2d5117031103c10410a0441d801000e4013000306c640c02100342e02500301804ad100880700a01403400980c4401741d815245a0f10741c0303000318200b00003046403810b5040e0510155000701a8020b5089414646030b2200e0100e601042c0b1000d005c0e00310035031280c07901d90003405501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 410811366 1250 410810116 410810137
    0xf0d020f030f0f0405211c0c0215070f0c150903031d010903050d110c1e10030213090e100e12070204110f130f0f061b0b0726010b 57
    0x180d43d0700305a15541c0c01030243d41c104586c44095900303220a02c40103180c4a4500c4034404041c0c1d40640800300420352034281002000001c2503110381c90f013015180c14810790740200617542d1018944621952011400074600008684006c4009018000b05140364065003180c105400d000011908503100a0000d110681140c81e148902444200c0350b64440d845000045138400202c4240d41d4503401c000d41411a00040080e45204144c100c2d1303010725010300d024940707000c09502c0b0301c2032680384800d0116a642c0500000c050640802018022100c6c0042e54001072012210000c0d002c8540364209040003068103049000f54148030100c01d41620200e180308100150442065494009101140c040d24100c0390503003408102045980e80080b142e0000c0ca41081078440303000380c06031601c01045001c0d8083c00b454600080204007440a00d0040800c6c5140002001c0e0249922130703503980d1101c121404030741920000741802d4918241c0589043c1d6580c10440b03120064a131581054400a01c6006092000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 410812616 1250 410811366 410811397
    0xb031302040506041d07180605100302090a0e0a0f0c030911040e1f0203070912030903060902060c060717070507030e1302130b030411040c05031305030415020f0d020f03 74
    0x91039965582e120303002400000e00003202c4c0c0c400c176400071a160307091440380321a21a0045401c580401d00742c400ea00642e00e00030400d0450280d085011402500501c0711141c020025000205540c59240351483c441e80480c00041050028181d1a80c25074041ca4220b206150408401000240c2002d50740146c200c01514005612200048000d2600500710500586426481d0b1400e01c10031094000750b1060800d62252107115070307035060103442a90031060180014540360020310008202c0c2d08403080890000340014204000e6400442c201130041e180c58001c00c0c40310302400d1001d030418500a031312804130f0070102e040c400c0c580c42c058049100691410b03c1581c03030a00c540c00d000313003e905503094030086007071180b1080e45990100142c0d0b403061300e055983c041d4000c1c01d018076103414054141d07400c0c03050380c60900310f8545001d038400048490030116080c0c0010310001c1100c4111100019450440341c2c001c203a007907488081a4144450800010704542000c0070321060408000205c409441c041d1030344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 410813866 1250 410812616 410812621
    0x106080411012606090c03091216020a090c09053a12080103110427150203090c040b0607020109050118080607050c01050901052a0405040903180b0313020405 69
    0x40b1160078041180641865a1500e0581c488000c40c3c4070038440c84d41a10680d20303d45804412900c0340c00100d0b07240b00c003a4083d030307c6034100c15442c40107480c541c1c0366001005c96600c031641c00560200340c84e400003205103595201182000758000203420081c80e00382c03401d2001c0070400b802000c2d103114400c01050300340d02c2e001c101500468202c0c003003d00701d81c0100c481d401b03462595000504146003031106a038040c1501d071140c42c5900c1c2501c81d0390706041c0344201030040d02010402c514000500e0b482c0903545407940d0030b030090860384240001c600c5009410301418952482c042008222400c0c0d80180340514014171250740182d8204503003405030384003428102032040d000200300d00c494034590040c003c140203217814400f2141c0c0084c09011030030140c600134003056030f5040d000741c03c0f5041122007601041241600041c400c00082d201c01c00c049070410700174942519200800c040d03504100045001980000080c02c04001826040c1d010740741c0b11801740d146040821a8003500d01c2d981d40041c2c403490b640d101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 410815116 1250 410813866 410813869
    0x41e0b010507060e070303080a020f0304030c020f0405010303021c030b0f0f1903050c0108090307110f040603170a110a030207030312060504050405010e250306021e0c031c050106080411 81
    0x2030b116080e60000d0140040450720341880d4403030213584000c901080501010549441c0e0301d0080c3c40c040c0300501105411540d40382c07005c80b0718405503101641c10165220303503003140f920b807401164065402034000317141e540d2800501100080010441004044c50036050b0103031070740c6280004c0301c0c2c084100c841e41e98586a01000404440e000152a03004650b519000010400f001c5280340400307609880d01901c959802140c603489202c4e1600040c02d481c0705250754035503450089481142a1000307800014210384a50b1010f07070110f0140c4458184480100d000c900440d40314040b002d19042c007401400305556903070380181d60740415010040c00c1c04481c003452910002a94081c00c010400244123114904090504034004c01004950700d480c1c0c0038080c070001e080014803c080300900308414807a00c10a180d600c403100250032004c0c22048815041d14041c0c000003128000d49983d60f541005565a080d95100003e1030403900e000c0c42209a050000402c0f009801403013440d4441d802c50841c07100c5400000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 410816366 1250 410815116 410815127
    0x81005070519030c090608010506120c1312150606170402030c1c060f0b010509040506031603081b071503021b060a0e01060506121305010e1911041e0b01 67
    0x80121581400b6000c0e0080d65856002811191825114079000d0364a0306800c5440241c00d010314ac0d00441e040281070240102c06003807640c8000c8110a0300d00381580c004014030030301d40303032b50210100108003404e1505208800042490361504104e003000454500344010700182d11192101c00344100303440028013551018442c0c1d0b070030309800030b141044041c07064441d182e0041c48050180c808620700000c00080c800540b00394030811405847c2c01d07081c103407904200310282c10700a01e00c6405009101c520108034245502f1600510311a0341200c1d00c40c840305900c0494043d81da01010915480244104220380340c0301101d030741c500180c0c038000d652003507181c845460359403041400e04000d01c031301c2c0d0801181c0221503200141c01100d001c02071045540d80c00c00c000d00350290301e01c5805c10340c03060740100d40129143d9151416a074401c200201d44071008040b10784c184501449084405030741c9000c444104141c4030b40001071003030704172000c00010307003000d00c4191501404482c4074201540c0b00d03c4990075a0040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 410817616 1250 410816366 410816377
    0x6041505190f0303050d0f0c1b030e06070803160302071703060607050607090603060b0903060a1e0e0d0905010201231503100204170307030e0607020d1a07020607090810050705 77
    0x4640305102e66038074600244581e000f07040b48514185088086200c01e9000d0250350a01071a41e0385240801c1d8006440e5800103420180071401d0082070150710700d154503040041c0100d84d0168a225407a8a8014181c11180040518940406204104600c00520040e044d1101c0e0040c3c50a00d58903540c0e0000891140d1044520150652080504015a841e40011134000b540d05580c0d007484020350304c030f1036075280e80601c01040b41d25401501c0010800394482c1d1012605c81c09011044142201e80034000040302e02541880078160416040c0035002500907000700c00a103030a03c0204401d242d241d503005009055102140301100a500100f216810200f03071001c056800201600c484440c59101c8000a41c032500c03540700c0024020b030306070400310400b0040d21001c641584a10310880b940100b00003940d405000d0483e807145003981d04101040c503500a00010b5070212601074110b04042102a1900c00c000307100744100190f5610910a501005c109c80500d05034101000c201500c1d1424251054040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 410818866 1250 410817616 410817629
    0x70c02030a060b0a090603030504090c0513080a11090132040c0c0b07080106050f0903030d18140d02151003211b0305040605070501150f030501050604150519 69
    0x60701101c1c41441115848074414880454000066130303a24540001903400d01d00c0302402140b800d00c4104a004041e0704202d0301c0350783e40c1c5003281c9032a1030040c8413003910950f40c1212901d9400000c03042c00b04082107001150b070782d6088980900540c505811041240341e92007078118001c0034500e0140840d04142c0014441c3c4038018001d1166180201005007440204401514490400e50106400c07901510006060741d40965885181420701021081c09601000c00d10b60144000c01c44d040c1246480c0c410020301c1000c0c8040c02044805606081406d41c0003080c02ca090380d040761004040a5800140200207800c50300083c000b0340da50000c58a45480742c90f0300107425007401c1690300700c0c071213620303420040101100d49846840501c4020040901004100d004000c5a0200b00c18814a406180680b01151240c400400e000b01d40070f03560019507441d40c4c4003082445420000307008015003802100c3e131008081e80c0411182c180076040c800c00c076081d8412035025200000ca0100394000b203001c0c08003d0280b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 410820116 1250 410818866 410818873
    0x5010e010207030e090403080112050f0610030303150803030112061407030b12070f0b03041416060215040b04060504080c06070c021e21100e010c0f08040b040308070c0203 75
    0x110614580030354440319045000604044442005242a0480d0b5000c0c03030301540c0300640b40e82820849407143c0070300502a25580f00b555000808c909040000510074a25841801075251451801809540c26a40409a00f85011409114141000040c1c0341111403e00001501c003206042c0030b070040c41d01201480500d0043c0d803c0242c01c070b4144e00051050324064a0129404208c0c05442c0d40f03440041c001d20300c0301000114100b0104034030001668215000708a042e540390035800040b032800c944401051001c0d800c0100804ca0b594050015144405840014001034070301a0349072030480800400080040d541c81d804102408080001c1c0e60004040d00c04450792810881405070006e06041401c0b840f03242030160a030f020b4aa123010310500d0003000b801e40c0504d14000611541a6402e400d00700d8400d00c10f03c4000c12091748203005a2200306e981f80c0c00042e00040d99840105060044016542030041c9131090000040c1c29107600d0b94007640510f0240c5468030350304400c8402401d0703003001951510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 410821366 1250 410820116 410820131
    0x50f090a0b0301030c120503070b040312150501080c040e2409180c0103020a02060f04030e150c070609080312150901140102010624081003051203100602030403020603220501 76
    0x1c0303109006606980c056010501100d0755010040345a011103c001412500140122000a18031021260308140319040200d000c040401601c07044420a000b140c55180da550300420285d600404280d4101d003601c07a10713a180c18103003d112070300f2403030161028842401c480e000d10100481d0b01a18501b07000e0013881c2c44100d041030320341c0503024a28000c9407509030150f205000203940c003a00c01c5401c1440c190300903000c0e40e90760500c4c02420407802001030b1700740680e480c00000e031641c400041c440c580d0720400559072903030b1a06810503d4690a500640240b1451800a0084010020070b54480c003080085d01c0103607076110018080707003410b028051a00420400004074079002d6204800083c030f11301f030b070080212640c0c13001e801ca07000b00481202001d11012480c80304e107192040040c0795204d8800c0c840044826903e98406241c14071214201b60101c01c0403040c0805158034861140c021300c081d2005504140c00d507000942c1da844080c00c3c900c00ba010b040e54064100140c2072403622030f145c10100130800301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 410822616 1250 410821366 410821379
    0x2090f0105091504081e06060109031e050303090102220b09060705070909060603030f210209031507020c01020d0c3306030308100902130509190e0106170a030f050f090a 74
    0x6c210042e443c0b224540c02d40c6104400c01c20004c0d00c0351048105a4070410b0403440e40c1c403170760082075624074040040d1400000c0c07900491807c00045008040b801300050f0303601c062582c465440c1042c3c03100404107086100082020343c0103801991940c0c40216021a900c2106203403582c505403440e8030a00615040c1400344c410300c141ca5211a048078001c6d01c51201c00745909400f1a40c06100c450501e14038401030754080e00c007004540c01340017210006001c0b030307941d544210fa01c4003401104a95110050b03201c10924603c40d60b050101407041e0110303090245441d040c0b03645504516108080a00144203c024803551a1601180c140030703040f100c000400604d0744a05000300021400c403501e4414046c685da0000d10b100682c4201ca61201c04400c10b490746038203000422510100103007c0440d80410000190850480d5224600c50841c1d81e07070000580c540703081c01601c00009400701802c455004000d89101194002402100e10b6045181640d0344519400c0b481a1501403030300c1464000401c041c022805 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 410823866 1250 410822616 410822623
    0x15030f050705010f0e031b06070203010f060306110c030913061806030516050a030807030512011403012315190303020f210708090103060308030708060405070302090f010509150408 79
    0x3a0b42d000ea0350b101c8030080d010400d503480ea4803002102e4140d80040810b800224205400d40349950004052a00d05440c5400090a45500f07542542d02d0a5842e0002c00802c0740c503120790040c06249941d02801d180d60740480c07548a0140010b024010440300101c042c3d0354009900500281004001c50308140305500007280061800d0300080f0388038440d05044800380301c908007003c0115440144101825411a66006260b4201b1380b070840c180a0140140420554044d04550103010803411a0305c10303041c504209400d4581ea05180303648606240189640e00e9011140c55910a42986056920148010104013402c0020545501c9102e4a600100815038040349028030b481c04501110002040c20032806400502d02d1b0312500b41120410101002404500c0a041a40c070141070015495580e0f4403218102d50040b01d2800006295608001d9035203081d118554100c11945400c41c10720710810080b5080001070306440d414071901040c081c83c2a500c0303410010380000180c0c034040c0c60302d544d044825907 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 410825116 1250 410823866 410823869
    0x1c0302030d0b180103050102070213110901031d06070c050d0302030402090411240c21220812090108070c020303091c150e0f01140105060d0e0d02031b0304120615030f0507 75
    0x100d88042f0580e070b103280180b4011a00e540880d25482407170411040c0042d4000c10141601107001e00e01c4c036403100201141840303a00e11410b0309840310360f802d24079403030f10a00703001034001c012040c140706105100240e103914075010745c0180e0155030000300c0c029180000d440340100d68040d44d41c130446141c05401b4060000f000d403190038261005c070fa1014a01b4000b00c8009c00c030030300d006100d81c0340c10b01c00c0c07004000e81500703d10041d01041d510205e4480d12240c906040c0645440c4501725542c00251100035540c3c041811a8400700502e040c00400da903a60021b502c07071040c15080761140c10105c0e60345001185902e01c400c500c0b54444110240502440c280703601900b030084c51848580a803050f042c09500c01806102e03510014064040d40503805c18003041015003000b40c850020540c4d6100300b0312483c070108010382d42005d043c1c004503200c1c00f0340c164025440203094440d14113a00140401c0095034600b2803850181944084045014248110201d454120340d0f400600008208d00d402d00a121000c50505c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 410826366 1250 410825116 410825119
    0x313031b0b0403051b1f081b0c120306130518120a08011e0b0a0206090c01050c0705060304030c050d030b03060601030204060818030f040605091c0302030d0b1801030501020702 77
    0x9404560381c54503010a0b0055100c050542e4008500d203204030200300104142e2020020005600c6d42d040440c0081d4601090000d1404107802e01e051100441080843d05021280c400346036141c111403280c2d040c0ca6200d07049500e03400c0040440800c91340d40d0390080b00005641c00100070003003847d141d00b0a080400f084840d01d0068050010a00310201c2c440040364005c3c501034994078800d1346040445000c81091014070302c1c2240c0252004140d0b020081c0040c0920581079005155070308045c0d04050416094480315410b00c00c04001281884201140240880d001152520b489548500b401d650b40804800c2c0144940500e520241c0680d80541c44488030a200350105c51250b9101c00c01941284101d0042e4000b29440000040203082500018525415080c054a05000540307405c004c0c40c1d001904542d01050001c10300741002e0030852100ba0360110303400c00300c4100f8542c1e91000303500e900c6012850b5442648a0400c0c01c00b035107458460342c1c2e1021400310382095642e92030920900039040708404a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 410827616 1250 410826366 410826413
    0x31a040e2a030111210403140d110c03030f0f1003031d060406050703170408090906040902120703030e0603011a030a090b2409160518090108070501120509030a11031303 74
    0x481c0705c4211a0a5074411a41a1144412007140d600180e040d80c00c64005005480d0702d4100a24072000783d00042c1040058040045480b030400300c842c8205250000c0caa40000200d40d8204100002e1a0b00034034220794241c00c001d1140364019040e00c8410f08400c0c41c00b03030060340000c0d000540c59030280091000900950740d01c0024620011540588501514044c1001c50188010400d901d00a600c003134024000800000d55002d01d0380c045074100f0092200c140c5280c0010740c1c108285904002d130b960604800b107071400c0c503540c140780820210280e42c001c0365006c04408400500000130540c0140f0160360028240e4041b031400e200c3c14601c107030f508041c1ea0810803107098544031500b011000700c4c0c010102c20041d0403680304049000c4800e50002d150200070503881290541d130b80c0d01c60384800307070281107000050316400c1e08001c005002d0303500e14800142168a0b000420840d0303200803094404032910f80c9404048180c50750f00d404d180d802074460b074400c43d6281e118000104142055003800216125090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 410828866 1250 410827616 410827657
    0x160c080307081806121005011b0c0909080f0f04150302120c0a20010219020312130c1d06150405090109050a021306031a040e2a030111 59
    0x4403500c90041510080804030107024007080c091014032804107011016003c1810800040500030007000152031b2200d0f5502c40b44030a000302e50b4007024691507500301d603a806d5040d643c942c1e50700d510794410344070760713035040d5540d40100c0108107070801200e80680f11851050b8541001e400b281e0340313941c014841c3d071140c00300034444120503900a00031380b003080d210320381040507698030079015a0303003a4040040d000030448585024030031507421368421122495030070001a2609102d0000c441c421700e104400b41c0940d4001c6c0000381c6108521400940d21030031a03a0383c00d001c00c0d064604503825440940100b12048046242d9330500c1c1d10444406d0302c42d80342104c00e0700d12400001c1803040c1d240305502a494001c420100180a010800d420240c1c101034246c500500e08094000144188541ca0b000040000d032201c00344010740d81c60821000c02280211403c000310807822184030f42d10105680080c0705044000310708401c2419a104020340500d01600038802c0c1898140004003a85c4001588101152070004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 410830116 1250 410828866 410828879
    0x1a0109060e0705031f18091a0105060a030c180e04030207150e1e030106030c0608010f0518040204092003070e010b07030c080405100305090613020303030a0b0411160c 73
    0xc00602610883d10380a03d19121000b40c00c14140300a4640c861070002c0000c00105d4400c800d4411040b80e412aa000515010a140036908810422419110540c80c1c00060129945440440c2c980864600700021031045818041d1101d02d5004540070a400d01d10704005403d61000e100c0c148039501c40e60031b0310b43c816102e80c00c0c9041c0050307107101000094080018503800c0c0c01c00c55502c00100c1c5031460164400642140001e094070380d50340003211500800b00c810440e241e0884141c5000d00700000e240c650003400e08005c903600c0004841004024540396010500303544507580410000d03900403002180c0b000c0e021003c0304400554070310ba18041d1054803000a00030f4241300100d4140e80d8100d003003510b00746107600c4c121810100d50740c1c1550101810480000c40b41d4406403185002e00c1c040d2070101c1d840c50906401c03403d02c44001c0904111102000140005036000300880e544014203403400114026070b40007160007440e80c0c41c6248002d010010790940c1681c000001842001d01c00d030002c4072160786850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 410831366 1250 410830116 410830139
    0x715140403112713030e0301020a02031b01090b0714090a091a0301020301140d0503042d090c0917030f0d0906181101051803060a1a1012181a010906 65
    0x302040c2a01c1c22903c081108840000b401040c2da84c040d150107003e103c00c1c01c00007400ca03071089449501503072002500c00b0012480c5144034241c004800001c00181f00d440c0c40b600450b06000300084100300101c0940c0c81094454401d43c2ca80031005002c1818854480707a00340000c04940c42845070041c407096840640b4581402142d050325201d03290560424619030910520074240c20701143c1c43d000602012407c4056000d01d80d05120001a80f0f00c10b89560020030712031344c040b98201c403901c141055840d2003004e401218545c210b9140c1000c56241000070344441e42140600381381d240c0506000504001c1e0364000e500701401e000d0113400b041000140710034440419800b103d03002000e4200100b07118140d903000714040c0023400581328108003020328600c0080e003403808c22502e155406582d10801c041d07404210551080d040c10a45501c0501c01c2c04c004060071100420400c100e90342e03185c8003000403240e1035075021034100e68056102c1d100c00784100c0001521000c240a0b4510451030f00500041007040e21 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 410832616 1250 410831366 410831419
    0x3100311062104051e031804180507060f0c030806150c0a03020a0c05031c030c1e1e1125030206030124030911090403020a0213020d050612071514040311 67
    0x400c02036147c006042e1008950700381200c06564000c1d41e81c804510464140f00c000280140710344094100d007814450003600d6805444007503005c00020322001170010750030030805c0341c002d101101c6448841c11291a0900f40d803142962208070b900460500400701600028800e04262144070001d101e01e031114213159850681c810720707442281050b002c0305d0026010742c2c00090b5400003490700151070100d2002020f0a5040500640000781969655001100c840300c00070081140e5803030034040380c0f0500c40f00742d96038898401d001c08010406100c038401c825100072903c0c00441d4041c010070746030342e52240010030703487c07d500d0b0140b400203490004c1c4034158441d00c942c94449074806c2d111040352605000344282c241009000b1419480790b03c1e240c00159079029241c0389400c0008002580d5030b030408242e40b0031394001502c024020f8000428841100001042c0c0703d042d28516209a040c44414240840761501c00740103003c2c9402d00005e01100b400106118560801425540340000913041c25100d000907041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 410833866 1250 410832616 410832673
    0x18020d050a0c020304121a1509060d051b04060315060f0f03030c0308060301021c0e0d020a0c06050309120301060f030b06090108181f09050708030310031106210405 72
    0x4000900484844d1401b0901190090106442e15046a01d1015090360300b5a44141c0030b400d03072000450b80d032a1010009600c50700c00d603a04d4100803000d54074656209000304202614a100100302d9010380c0f03482d40b040c0011a003100c04840560402c80d189801003c0f180102814251480f601141000c60181c02c0c60803a5410380d265036904955403003c50703142c00c010300420ba2654003040380c0c02e1600d040b00f031038020300100c005000911000303002c10303103240c01d02070302c100825908131141c843c2c08200c1300000c0c0d200700d5a032420309a03500e0741c1d4400d407241000c101c0718020b2140c031400300011400d1903102201c05921605910308101d1003c80d10104652030064203940c900040708000050341421445001000a42c50801192007484070801c00f1040e14094403101c00c116541c60b00704805220040107001c3c000d0501c2d002440c5035080c034a481d44030360626800041d00300b28000d41c041c0c3d40f90700c0340350441d205414071480c2c0034602c000f22842001b902005840c181d40034071030003642c410706030303810120740455044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 410835116 1250 410833866 410833873
    0x62e06080606180d0303050105010915172a210c07120201020405030129060301061b1a09010c09060e0a05010809010f02070803011d060913050718020d050a0c02 70
    0x260700041080a520199905108a00f0610907040030f844541807000c00d240300c3d45003c80c1540c1803100040802e40b072948131100b88064140c3d190503e50704645030700c0350440110408141681c0340303aa210300c014441c0700f1107029401d00d444900407584804000e016034005045080c154981ea184115130301c1401500c42c0d01c0c80c0a001c011b2440010750000034140302e0070300d80c00054105603441001900f101d5507004d00b40a5090b2000040e2117458545029000d01c0c0303801c440c2a420f550501000074040c0c01212410002542e003120900140001c050b034851a80840811a695a103002c0304428060140c480c2d04c2d80205201031404900c1c0c60082d40c040d050901d0150203c0310943c50040119410440a41490718556842c8a80652801c0f0341c00204586802072005c0c0303642c3e500d041500390f40c00380320983c120308410500c000d100082e0b4032181c1040c0c1141c104051070b440d1560340d040003410034005d6400b2000c41a01d4040c40c0704280c901c3d40150018916030481003140d551500072920583d500c04104000680 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 410836366 1250 410835116 410835121
    0xd170c0304050a0c0b0d23040f0c0504050103031e091a0f1603021513150b1206190606050304050a0308090a0f03080604050a02120c090d05062e0608 65
    0x600500550752050040040716419002038441e44000e02c401d8000401e5550001403450200b58075000e07101340c0101c00c0311032244a0401515007425510080c000420340c4501ea9056000d0001081284014180060040059581d40c0c90041c1c14040e1082c001c1c48064120000d6414641c0038440d200110b5003c04280105e04071495039a41d600e42c0a0503d0034a2940300384800040020309042c41c4c007c50b032094006000a042008414041d07920041c1320110204010702654006240341840007803003403d811000c0f4084283d0b2001442203094200081000d110b07980810440c410440205e440f03850055608100980c3c840d18201c505200841d4050b10b603502146201c00064810507546520020490a403100c65102d0f83d26a92507c44801082c1e00240088007480060701d000d100b1141c03c600d00c03240451400320000d0750a01c010301c00070000c001d96040455094855212000c1514003241c4c0003050b07d4281c50200078250001c240c000e0f030f141d09800704081040506051031454820746131280c035842d5981d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 410837616 1250 410836366 410836381
    0x801020a170a14011e080703051501150906030218090a0603020906012a0311060f0a110403020d1202030412050114070f320304050606010809070b1204081308070303020d17 75
    0x44a00805c0480450544000015454018030000300a18440d401804451000040c80b10b105c14044e00100010342100004812413608007102c14201c4509080240e1125480510f094000106c04907442c0c022440c10200480e043d4160710032000d4a10860f40b0340c0094548a0044520300084078410320030490100d411110050503884000c0c0841c0302c4e140120040405401b03c0742804004d480c550a504650010f220b1000454080c00401c0c0348089011170500b0b15640000300c07444800000548564110340402003150310910869001e0444802011002d0710f45c3d03c1d116000f000c8184100810780c00c640086603004d441404002c80003815507450001200001100e5002400d6040866008080d4225002c10603000f0402031031040e400fa40c050002c0d8a4403400140800d50018000c1e04240c22460051000540c010140e50b04144401800107055481c1d00d04500c55110740c040d641061050280700017210000001e005003540e20a034280e44110100c0e00f410750781181000291040710014000140d1036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 410838866 1250 410837616 410837639
    0xf0316150902030118050106050f0a0e070e0301020a02070504150302090f0903041d0412020604020105030c0a030b0a0f0f0605030105030c0f131508070e090d030e03040801020a170a1401 81
    0x10590380440080c007412141d002030700b1a0220900c3d0404000220010001e01500b80f203014002c20003951540504010440011045855400b480e0b80d08114803010030300042c46040c50b0399000c0c3c40600215914403604074042c0d9200300c20b1107050700c00c0d414881007009021000403100d040725406014100c090f00e4011042c0c100f01001046e02000c1e00c420b110010b52100745441c0a07021181c0c03070140d12000d092604107032800c104098602342c01d561103c802d200040c1d9114003181c2d80321400f52035183c4c03500c00005086029044074046541d101c3c0008602149888120840200301e407980038000810b1039440000ba10301d40000d20038194903400045000d040c50402150705905010000c01c20108000950f010380115031100e8a02c59101d21010b10078000c0c1c010400c610b10292801c00e070f083d4035074544041c00d190345070366260310b078010180c807965200d082400410540d0090031000000755150600541c005000b000600002507006807007601155079103005120b442e510300510b0307041020503030801040808 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 410840116 1250 410838866 410838893
    0x3010603020f0c0d03050f07030e15101806090c02060c0a0e040b060c011509020c030910020307410c0f01140a0201090501050a14070e01030207170306030f0316 70
    0x1c10002040b1011070f940e07043c0500c03c841d6206880014a070f051034642c0b8080e103800100003805052400a101c0c0181034001000c020701c2ca00310720048000e41e1030008040f0800e00c00d61090f800588034268501c002c22003038018900351960504108110502080100c1c0e0f210000c2d208441e114404004280390f07103208081c55040c0c0ca0000d40040350000341000814030031782c0918080722841c2d640394154a0b852003440010390043c043c40006601386a11040c005480f841903110162186004900800a440c005c0c030a4428154000040c0c5c02d6154000301001010031031b1107081c0c02d206100d0000d4038216100c603410503c0745054140100440506c1000380040c100078490080e0502403c000b4000343c0581c5600202040e014650001c00c0c4040391b49800d600752a0060700081040e03003070401043d0742c168071a44595000e0341615040c00b034011344a0043c0d0007442488000380815025001041600207000e00450040340e040d011200010210f82c80305459004040600030140600d41e204800300d00300845403030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 410841366 1250 410840116 410840137
    0x618050a0b0913060b04021e09030f0a050304030309080303190c0e120d0e1203070f03140301030f12090609090b010908010905062205060a0903050d09080904110f0301060302 76
    0x41d421106000a589240304030761000d9810030081e040310801042e4003940108940550303003981030444206a1403030b40e001180b800700b03030302101245d000340ba03640070441d4014010740d0070141d46400c80c240c04e06a03265801070100b030b0702041043e20001806900001117900c10b80c00c400a04031040c01050516001d05400d0804808101c0d40c0721000100c2e543c1c640001440d070000500504254260f00c4010740300c2c40c044003020344600701851901c09014400300407680c00681c0322911040b007840528090729003c810920b02860b0910210000c0200008190701303041d00e40c05480501080e0b55510421580d425030760040c0c0f00090521001000311015a42028011000505000454540701c0c00e806003110501c0d0400ea80651213001401840483e0300b208044a152006209030401140d0325a140d450f200540014980c1e41e0707e401c00000c2c0f5100304141c61304645060b0b800c0c01049100e042480071a000078075064451071070134810303500ca80c800307004440306841021045802c503883d2200580094108a5510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 410842616 1250 410841366 410841371
    0xf09031801030e0d0306150908070608100b070501051509060f0918060a0b10020f07120f0203030a0908010f090f110307030503040807090b1002061b130e090d030618050a 74
    0x703d02d000e6050040d056900d44603074002419900d0700e003c10f840070000c05034100c01d00c11024418001040042200e5051b50301c1810041039540303c00940c0d00b070700c0e08940d01074411030074040350b41c504002042d04600e02403503588009911180c00c9004100c103015003a03038120360110f0400700c40829400c01c014055480311044605a02411043c4035080c20040102e4000a41c2039880c03100c1c450340d15020040c45061500341c0300501494094440040c2d442a15015400505002c17286807000c01c42c0d013010f4065115809800d5a89513004114050290202400780744200e50034403000c000c07060ba03d0312400d40e0082e0007007514108042c054855400013940c2d86203141e010b006980d008400b04000b04002c10081c18010010001c040c9460102001c49a410415030301c80c034000080140c01d6507002079240d82008045021010b0001115012030251107050a00300901c503910b0800100c0b40c1d103d00e400c42c441c0d1441c0060380d08040c2d14078001c400302d80e0540942424500340c0045d003a4807400681c0040c0d403003401308600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 410843866 1250 410842616 410842631
    0x18040515120a05070803030402130f020f0a02031c020c0c01030e160e09161503021602040501140103050901110f0f040f0e090d1707050a02120a080f0f0903180103 71
    0x800c1200822641d00c00c42588818105410801c0400c420002005408007442c154101980041e2141c50b031200703c0c42e00c507030302c5624500100300960b041303601f1240034450403030b03a404c0b80c0040039403203401034207100c401444605642801000031b0300844150000c0b00016001501e4800015001050680c6110000344600603a00610010811892010704020045101289055841c4525108100b51034058102500c5402c121010b4614140d00030101c05080244e10386100d001d842841c4242408065070143c00c02000050010100c0000ca8a92100381da05010560360000014207039000c1c1162201c0c1c0381d100704007180d0020441c01c0038200c0c4d5850801032501d0aa03a9181c00e440c003101c0d03500500415007203d400c0c000210010020140c83c030b55282000c0a036040b460310302c52007980b80140751201f80040040c105100d03034030901c0310504900d0751111458565401c0840140000000ca5202001e10003080110f021041da0034626480b540c0c40c0c4000307624020251f0a080480c144201605040c9905c03680c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 410845116 1250 410843866 410843869
    0x40c150e090c040f0b07021f11060a0b01030614180c07060509030a0807030c0807050306060f03180c01051903150305010c0309120309030e09250f0806010518040515 72
    0x40c514040c094400e1015142d905101c0c0381d00326603404e944000b20a140410014005032901125140c400d080d090030006469a40e081c15103013100541602441e602400013081707002e03503a43d44001c60801b03081c0d80410829403a0403040146c01c00701c0b101c3c0c40d4001d100120402440a1075205aa0701100403081182040c40030b035528030940d07406490701d0700c4981002c100651035070b81c001030040e40101d003481c00380300140d90840c3c050302420300a080c0c0800c001c0e00000140d0315454035811107485040e01d9002ca960391416000c0300c05000042c00306c4071041d00131000c42c0003056100c0c20a0b0385d2038000c951244028060301780c0c07003600105420768018403c81082c00c0c002001c0f0f0000c0c4551071018609440c081800059490810040817451110341c05144c038101c6a0300100e03621070408200c1450a580702d2103d500d40d00b106202c42e8414440c504060b4901d0000d2550460b0b102c0d070b00240200b80c0b51100401380e1602001520203009030781102e035003184613035400680380c9095000a40c01105414200c00c03030301c0c4400b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 410846366 1250 410845116 410845129
    0x6080103141e010207060b0a03020d06050403050c030406033e0310150309020f09090a0204050c041a041802030f06100e100908100b0102061611061617040c150e 70
    0xc02c2c10b01a5404a00d40041c490603016145102c4421034a0240701c60440d40001c140801415016211646c1d0708006820940a202110401950802100d071243c0d91790000502402d516034510f00c95854440311101c50390041502c00a21a265108054501080321824602c68000401c0f100030020700c55000284406141002281d501c82075901240041090041c48645299101014018502c3c1c5041041c0307100003080322103800c0e42c115004203141c0c5070040340008900031608003e07140701c000040c407404030300c078a00200304540c5443c800315440900101c45200700e01045038003889903900100025882d1070038906819000c5c805040c60211180408046030700000c0c1e6120800c00f084011805103c400400c000290b00000800d000744007210240000035150300300900404031050b05040d000c0c071480d0003041580690b401d4482120458640300d01d010645004402001000c1800c201040043d92540044140b00303903000342450b5529458042102b135a580d201404804005c40600c151402d070380e0303d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 410847616 1250 410846366 410846413
    0x50415170c090103030806040b0f0321120903030106120b09010e060316080d030f0e0c01050702060d0f0c03140412080c0412060204050f010216030803130506040501051f0608010314 79
    0x960706c41c0214a4540203000450b0355141180b481400c1c078a00c034402980d0b000032a0b10031001002c10022181d4148220702e0540e00036a41200c00c081d07440340800c072000380008041c41c12070714655038908880c2c011115481c00c80d042c41042580080e00840140000c8003004c81290700074002904446120030080840d202070071302e84d041982c15801c104c5180c000680e00d8002c0e038890011541d020041131480d00301c03031a80d41107420320080c1408008648c840c00d640d2004107a41560786034800512880e1100881500240003403a94400441d1901000031181c0350783c0618144120b9020700c01d030300942005001170b114010010038465468904000224409801c0450015118480d180150311241041c081000c1030364020400360441d8807240c03200381c4d0000d00010110446c0d0f00500c0d403541c2d0351110345004508880c021750141592040505100c00c1102c15402140308a810840d049070b6040f02c5000c2d000c90304818428400003501d05030060001c100141c0c998010b50b401b44003180d1a030160b4000132a4000001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 410848866 1250 410847616 410847623
    0x509060f07050c150a0e040f021309020307080a0b06070303090204180b0f090114010b1303331b0513050901120c05010203190302070624030c050415170c090103 70
    0x8198585104e0919081d0324080340110750445040080015000306150711003003a580c813460300e4107440701e845040f65048485000c941c5c0402044244c503a00d640020758400c2d20100000703100b10703002601000251081a55a1100034400c03032408055032400c0740540011182a640030b03130350b80c0001c266030301840c403070203009481207840b80c90a24114800000300b020003882e0002c164181070f020444000c1002126041d51300304070400da00c4803d0665420b5007403c1c25040100038107110030440b081100317416240f407084c05200d24443c2c0c102070580007140948034198000240c003684448a143d03020b0050740500400e05409404054295903040001d110490030f07444038044040c200189d00c10b100c0c4c01206a0043d00e400e000451802c4041a00e40007800002c40084081682c040f44030002c102c1903820809904040c41034041000700c002d444108040c0c150310003160b00700071180c4005194289030081d910503038606480481000d00d080104c40c04400107a103070240174020740e0404c00c06c1c0e50f108180716029500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 410850116 1250 410848866 410848873
    0x90b03010801060303110c0307060f12020307081501030c020c120f03040312020601080a0c12110a06020f07120b010e040201110a03080a06060509030709180f050a061d0a030509060f0705 81
    0xa1401e000d8140310031b16181d01c2c226004030740c0841380c0c4d880c00500741c011100d4626013580b425440640071111401d03425800e080c40740c0000b080c081c42c3ca83c050000c034003441c00c078034900c1c000da401c250055044480309450880542c111070050071142c900b8440d683d100f5a0704c02d0a03030315240c200014150071503016410490352070781d80c40090354485504002075800340002c08000c2161135695201c03246009480c0c0300f00700840c070075090400308001803a00c4034008610302234090048180c8901d40070b5214003503001c1003940d0384200d5100180b41c00d10207005030300d0030b90400f4100d1a640d013000c0c44420402d00c001c00580c18801e488401d00e402090400c07601e09160301a81d65141d01d03041090b407038006e803000c640c090b00030850280440b03034407071b070300410104100d590607080000e501c404442100026006050040e20110303540b13171604240007000c0780c986600d600c603050810104402d10a08440820360780d5400980e0b43c4000a2500028041e2000b03215204008040c28140039043e200d0001c50303030181c0c0e03086075680c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 410851366 1250 410850116 410850119
    0xc1014070602040f0b04030c0e0402060c0d08070f0e010e1e0d1b050402070803070804140307050f06070503040819020705130b040e0c01050706050c160515090a0b060f01090b0301080106 81
    0x140c0301400c0130181000d0705040d860603285444880e18501107007c0c0c03103040000c2d4800300c0e08558904044416206907641039403540c041c02403018040000485003400804c0c500d40100703a4507845682c070b00207886016115041e0b1100101d003402489020500304685160500310802c4142e95280800c028881c8a480f91440d26032400f08440380b0640c05500c40c6010b94018480c11001171000416644d01501d01d2400008cd5591414650f0202e0041a44c1d00e129002c0007031120117001380810940c2d87e80081c001120101d486022040b00d85100c1182d0243c011042448584510b60391080305920900c590710454200b15210400240300c200c07000c0324104034581c2c4040f08019400c2a024154a08030f000018115568903540080c0c4140309400009002a80d42d10015900081c038005543c0c0d8019080307002c82d02400ea900c1c0c8195140d861080942018a20700009001d291000a41c921180c1c0d03c50640d003801d4031004140428603c5d0009141c1c18031210400100782294140d001e0360080240000200d2201d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 410852616 1250 410851366 410851379
    0x5090d030e0138060d02090a1401052b2c161202010c08030709050108010e040807030e03010e120d0c080903040608040825110d03020c101407060204 65
    0x103031100210a40a81d06204541c052400360b000394203c50441c00d60b540d0b02d100c0602e185551a092807410056001c0000b20340f07059030050640c054400243c00ba2a041d10b00340e210080c1d00b42d90203058081600203607007040000111143e00800300100d89425407402d140d1480644164203541841c1c0000c1912010840d014140d40d402c00e1005147c404190050f190f02407001c030b001d10184040f8002c0155102021103403804692003018550001d581115042d6203074106a08020041c2e4920f2240c240015181000400c1c85100c45050328003d80d8408051071401d00b060b601503520b40c2180d100984d041d540e0303901e9a142e600f41845800c400401c4242d0b06556980c1002100084842d44624801001425401c10490080010848040da0050f0034401603683c0c80749032040701d9101d105c0c44014105640410605460251141c021075a44164208076403d8039800601859026441010f40103a00c210004005410154804101102940780c114040010fa01662400f58061001101e01c19400103042158 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 410853866 1250 410852616 410852621
    0x15020a0209070e090a021309150f06090b0913110c1501150905041104050d080405010807031811030709090b190b010207032a06020307030f050306151c05090d03 70
    0x700a0400003440c803e0f44010801c2c4090091104548603800504040541101043c1d03030000c102180040c420b05403000310f229075011084c0700b0781404102240b0041901070040090b601508c851540c11400c29003071108201041090700345144030b460b503501500800030002401071500d11307d0701c001451441000e80e486651084140e1005107110500b80241c10610780c4105480100d610444020800c40841000e252852040d5031107158050b012021110400003040c0c0a002120800d07210350b84142d80e5141c0c141d081da8480b40740342d5401c0f0b17a01050180001c20004582011001c080c085410702030300c2d810440300721444000181c40f51940c2c103042000310f0101040213a00d24000308002d2040071540c4e00041d41d91103c03400020800c4a80042030f0b900d8040800e0103000711030ac0c16180225060742c0b00e0001c2d4803544038034025000034610906815485002e94100c0340140340240220030407403040b0440b1340050704640201c0080d03144d040844941c08030741d8003039607004406900203440b210390183d80c05403c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 410855116 1250 410853866 410853871
    0x80d0506130b01050a080a0204091e0b04060f150905030d0306090e0a051c02010b0a0f06180b09040207060e01090516060f020607030504020105090a0311010e03010e06010311030715020a0209 83
    0x8107542800c09a800d00e980c44020307a03454445c01e00b0401c2c0607845540c40b035000390245410041845240610301600701045a6112501c544d10107010132041030204c0c24403060390228000c040707084890190801c0034680002ca641c060b40b81c036203001028180c480d0000780c145042c0841400000b51501418404105640305440c020868440205081c0c6520f54801e92201e0103d10003034861030080f031101c1080d078000e420854402d10000c06404101da00d444082e10540210f02602e000940c002840032200b4401c17840c41c0c1c003568100041c003420881c1c008d082002a50020001300e605a03101c000304401c8003805d00829401c188100c025000c1c3d51007050400c0b56414440d44454100b09400500044030740d00414540d4000040d8a00450940d0f00c03400103a0b400c3c41844034036078110f1040880001405a114038060003010241d80f014505407032003003010300362a0110302c813506a4001c1c5004000259469903041c0c10020064185c8041558415140d400c0c5100302c0c0c0000d01507080440304004524101c0952035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 410856366 1250 410855116 410855149
    0xc16080c010905090609040c0e07080f0903031504020309010f020316080609130f080c030316080702030711090a180807110409050a020d0c0b18030d03020c0a060203040f080d0506 78
    0x9082e1464440040d00c0c8850203404a400fa800510220f42406441441d00015140002c44116207080400c4020714403042140d902001e44e1801e400f144145a0110480740035920071a814503241500e42c08100003540003404000d00c642d40c0f07a079407400c68503840c0041c6100302c1c503074004030400d5440010003410381400241a170341f1038285581000700e0703c0480503030b09080c2a08800d00302540b42c0145880703500340c407603892800c0c01444040100940c4030540c00f110102c841265590020075112000160380d01c0c000c4440042140c81c841e417482c00c1e80e0400500160b1b001da08110b0200d4080d0751118114016000b00c00103a494480003c2c9c04030074000040a100301c004415107041211070a079441c0c190725807218080c028801c03c0c90300c1c0b006080c030003102e1290b40640070000d0b40e15584c2c00300c110700c001d000b005130714014024003d030b480c03490b0424000e10960715a40c6c00b02c0064104280b00d40d0752a0000c1d4030040082359140140303105280483c003000302405c0e00070150f02c030005032810700303008001443c0640001c51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 410857616 1250 410856366 410856377
    0x2041503021509031f0c091712090d0c0b070302060f06090403030207020d02092a0406080720060a0b01030f090c060e0d02030a08031b0309070b0a050c16080c01 70
    0x3000142c480c2e4500c92440c54076070010329150a80c1200190400c851441d440e034000709601c070b0040410069030b215880000c3c0c40d80301c030b0344156655564158a907400c961800d9854200340311002c12804103078010019141d00a00d031102c03808040c0d8401c070398400c17641c0183c6903401002c5940410146c040203402c2d00070300342481d4000c2510304900064581d0a006000408254000c0b41742c0045464084041c3c692550042070170729103107000c50029406045140040450820800b40800c0c00a0040101d400356091a0348135103041d40c54803c162814030180c1b807005a240500c1c141010317013910602c03030503018075511400442e50b24540c0d070004003518603042000102031718040e64034001404034070040c002c4803941d0800705d6621071010f001070021180c9403006501070191449071020001c581c00211310074a401c56141843e180c404800004901040f1001c07419075000a0040c020340c45103202400004410340f8040e4070305140040254141115201d852401c444000c0b01800904014400f40ba459a03003840c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 410858866 1250 410857616 410857619
    0xc0a1101020f04120515010806060a0b03060307030222021305360606040b040902071a070c08030612010f15140603010e100b070b0406060603060305060a2406020a020415 74
    0xa0b00d0180b2640c800c0e5404a80001c060008010707051042c0142d004048039400c00c01e60350b0f14041d54903001d0480f4040e20070240b450001c1610200c66040e00d001b5080900184011802e581c20b00021258003011140002100042c150841029000174081038020714032401146250000703102c2e105040d20b070141011040000c44000710440401c9180e080c00c1281440921a100c0101040d0707207201d59000a43e01150019000c145078a940d0000c04c400d520480f452150240440001d40781071500751600c0f00047c1501c900b10005c581c2c1c0001440c0c010f41c00400716a51071413030050250071142820010710100d074503a640030315944100d0007200d00034220003022051000c00c2c680054034502c01400f400c000421184081030119030355052310030103440082d18896858419040c0740a0302c59080360120385503403c02c1008074640f0f04c02c1c055a41103951100c01003000d51508440d16018144007013090010f80301d84c9400c4040c100382070700d58500405168000c0c002c03e58984c01400195a6034042240700b18052000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 410860116 1250 410858866 410858887
    0x105150304060b01030e030c03090a0e161d04021603120c0509010311090a0f0e06060403020d020112090230030c0a14010b04020a03020408010507080f060f0a0e0c0a110102 75
    0x11690710a034018000625880403000680091420158144644c403010680280840c80000200135450007240c0116000b9524066100115400c8402c1c0c203914500c020b01c0b200c40d07805000440e4a200c107030000032060401400104040342c0041503040c0a00101c100031000b459000b04e4810f401103810401449171a6003484041c00300d1250891031410076a8400c0510300110102007038482100c0b00608070101244e0341c0560014003074103070048584060015011a810345440c404980451750301806400c0d81c4801500190749982180180301c40300e507156031003c00107a90341402184c0c0081030021014030500307490404840b50322441e801c00c8070340e4400c01c246920f05034002121210680e125903071118941ca0402042e000d410051222600103001240300c003a1036070142c0150040c6e94504008022030b540d1400102c0b40c0510541e01c0b030316002400000304000e8107000b01d803908200006008603203003540d9414450308d50001240c1c0003414480100e151100f0542c082c1c5204401c0c5820402542010040e20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 410861366 1250 410860116 410860159
    0x80706020f030618071d01020f06010303030209130c080103110f0904050127020d080a02070b03010e060f190603050c120112021804030e0d060b060c010e06010803071707050109050d0302120105 84
    0xe03003100441c445d8614041540e01c00c00c164860010350349e00350b070055650303450090003035000090014440e00c1d0391002c2d18902d081d0b070303c44c4400e1140a41d03505202c591841c0c0702d103035084401019150704004c3d501c5441c4c8403502c50b520250b00603072060000062081e0f520346210b194562500d06ea21800c1c0e2a08140d801590354400c020821030740100c00d0340c1c0d581c0f91401c4181c1c5403103c030780d00c644030300a004400041d20080806402e88102400e1b6005480507801070b040040b01c60340e01c00f0800e0601007640c0140070340d030f01c690700160b400a20388a041d880d18055000451100c0001d900104400c03121100c00801c40c20441c2e414865520310071742241c114181950090074894080c00b04900849003580b0a000740511f54000180058015020036685d605e400421800713004c400c40b000045118910000501482c0003040b01c1305150071061021581e4046082040c5075840080147c2c0c40c0e40d240c2e01520081340080c00f0b03621040f01503880040c0d40f07010745017204031500b20583c422449043c42c408031a0a040010303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 410862616 1250 410861366 410861387
    0x13050f1905040f020c0708010905060a020301080303070c020f19090b0607020a09020a090e15040c05160807020a05031504051b0108040b0402120303070207090b090105010507080304080706020f03061807 88
    0x102c80100e1042d42411203c0c00900440c41500e000b48658400007825500641c40a11518018800c2e211a81e403803245000a0b07108c01c0c42040d125034004c2000840c40c500c900d81d0b4a6407944008d03c011040c102040c00240c003a2400710b07841202c648144810800d180c0741c3e00c00c800710341d0002e590403402c0c03e00700c7e000075100c2d200038494240400e0b00051400d0641703104054820142c8041d02c02201c550400302403020078101d9001d229405946484000184640203000340c0e503103a06020103200e030307291295682c01c2c03280d08111422600300f101030101007100d41c2c0034001000c1c0c0202c0d078040b03244980b0749400c04c945429090b8080050002900320300700b2107a640704400c0c1c0c1c1e000350803a410344060384462020404032908410b1070202808080180048982d011420500322800d1031811b020b02c800160410189076000e1007003034007140041000c50001344e4180060341d40703e40168402070030303c01d594681c41c040c0c0e401110b070000600320000800c1800e02e80100052450a9180c110794082d14064001800384e2122 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 410863866 1250 410862616 410862619
    0x1d011e030201050d1e0209040c080609012d08010b01120204080601051c050714030c2205041a0c090a080d0c080d0609110a020705011704120e0613050f1905 68
    0x107503c10200f021034011945804418003000c1101680891505c003e410894103036200e103040455190310039100313045050103010004c02c40e1000341d1034a99401d541010031096951006071032900c03020010b002125100c020070f0074000110b13108600f0307030004008180c0a000700d1a038038414002801810800035155041d00c0040d00c410041000303003070712405500c25522001745944a401b8011038451050101e0360132040d070941c11140c0443d00c4404004d4060303145941c0c0c0598900305901001440c4c4160003540d0068060440140007541803d08090501d000b10384000c1c00210008180a5908006001c14002d000f00006014405421040103000d00000a00900044c0b00032407505000300681d44141d00401100e003081080d101521141446500000030b1580540515140000c155000e0080e031003800c08040c200e00250b0b922940d407145108140c400000411010114002041e01c50300020001c0d41960107070b00210070b150101704003a0034070784800c1034001e4058030745041c241c007032a206d000c0507503a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 410865116 1250 410863866 410863877
    0x50406080601140703390611041205030325051e16060504050105090d120c0c08040b070c060e0121200d0c05030601050a0309020a050a1d011e030201 65
    0x19141e00403185143c2c00901c0c5035a4141c0000c24604068100c484c02108540b085100882041c180004032040c80e10044401101e0030450382e100005821944040402a59140b0f214200740d15442e0032001c1c41c2d402d5404403101d070300010501c12415003030340d0506041000268008200080090001c06900803080c14444d540d203003604854155113098151000290382d41080003010610f4207000000c0c0405603401e9400d03520340b00c0402e1540201040840d1601c00310341340c0f900200e1640c1c01d10001040b106680c0000c0141c01880c20300000c030311400400003403900140c40c80c1c1302c0f400c6091003408640290300c01c01c2404200302441c80c503640c2081c0c14640e00491800b1400168601001500161400700c4046100c1c240c10459281d110000741d0280c462990025410003410003c120156994842901c00c00d0201b00281300810b42c080c425001032100500c05000350b01da8681d1030021451600003074201400303c9051066450103003c4900341280146921020303c440d9540400e490001c2a84e2408080d0400c003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 410866366 1250 410865116 410865121
    0x209010e090406060e0a0c110a1101180e0406020c011a030607050c0f0a03020a0326010e0c12240321090102070f08030d05011202090c0c0109050105040b060a0e040305040608 76
    0x10f5004000031709000c07003036a040c0c0c035091440700014900d40c1c1c1d1100105d844186200c0480e040001d09900c126807012682c20110300440056070b16103451000e481c8910384020b008205800d03418521801180f01e500c000d600d40c2c0c52842104e09440c4541d041c0e510520344500291401e5400141c41e80e001030700e0342040c5580704212550a07041c4070f030b1080c840c4130074480c48596108240c0d000071200b030440d0082d070760b0040c402200002c01e90b05a0654020000342c41a2000507c250303003882400c01d070028801c01280e0b240c001401c034007820004048641c502889140718229880d060303e05241403543c0d0007200904000303140c1507109181d0380b40203e240412090302280200c0507074020030410019103d551600350415035920001603a80d84083c008501d4039052000004108404015614031141d00a100762101d551f907071203180c003c2e0000320201d820340d034a90720540c020560030300c6041d00840c05400355088a05c2c5c003000b840850601980020b40740700d030480820012036407100540d002e071402442c1084c040d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 410867616 1250 410866366 410866373
    0xb1c05040b07210525050406021f06030f0b060918061603150b07061b0e0910050402040e060909120304030e0102070f08011e020906070611041e060806040209010e0904 73
    0x15a2079454440500c4c5000280705650302072401c15800200600c09a2000398141403040702c03a40030b20300c1000050ba000e282510341280c2e4000301a92011458030000825503580d49030300c829a0711201060768036024030707000d1044a06040c1c0c80c2651025420000f054204250050740366a040020044442100070000303c20105109422a0300074075803104440724407944419035200d459002d40e008640c8180342c40c2503400045d12192030103540c2c0c0c0441e100d01103c8200702080c0000c14800900d4040c4050588070042080d035228402707440940007602040d80940f824205100494070044c00030701e060740c000302240c03448004403001c495206500d458448101545040140e01d0404160000c070310102c0c440f58045400030b015442100700070b85403440c00d01c800c481d414240040740f0400820716004a01085506e0100d6465081001c0d00d540403d1a5442d0580d11030082c10300325528507504c0b807406840c0e64100082071340011034a4000c0000c503400c501d011041c2002a00c601117034007565006800c24400501170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 410868866 1250 410867616 410867657
    0x3020c010b03150709080d0c06020d0b120a030201140103080306060f0403021e0102160302060307031e0e010b0a0f0b0403030e030a0507030b06131b0e031002040b1c05040b07 76
    0x101d00025048030010004a0300b007801e25002150311100081c500034000404503800150070003022440d880344030b1428125103600d00170b9800400d0343c191080c2c80f40180050341e15a12154080060040c018103900c565915000382500c86001d420403a5050762170040c40441c2c0c801044a4100c8012103180e580c0303401d8081c40710403501031640065400344090301c0260720034041e0f01c20515225000d0b0300791000c0c0402d4007904090b21000e40800b030b4001000780009242280268482012003805062140f0440587c400c10344c20744a02c00f180d917074143d464010303042c1c4509204102c3c601411010300c4d000d43d041d080c00160302250041c0d1001504000c0708103031800c5c29032010700c00c0c583e1481d08082601c03d01612400c0c1640703030010544030780380900d01d11105100c000c0c11910804550340407403800a521014100300464540c0b9401c0c507526458064a40402d101035442d10040004180303d08040780c507461228899500003104804071a100342c24041000700160250311019844207043c1010100c0c00103010391031130b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 410870116 1250 410868866 410868881
    0x1e010f0b090d0b07081501020123070c050613170c120313140a050d020d080a05040201053018061f0801020a050405040b0301022505030d050a02030a15050a030303020c01 74
    0x1009a00b90901c8219517102c5c18042c4141c1c4c81d03606c2d03a001c03401c0440049088070303100d04265450103003645018108100a069080e00040c152800c3c44411b902c64940604220081d2108a8038404195a483c02c12581d00b6040c3c246c2c0c02d500701c10b181094900c1c140b01c2d4445190142211a9040000004180c1040560303a0032030300307030030500880720843c1d030046943d3740d06a80030050320144103203c20103070366030302c0061506ca8101942d07856504588410801c0b034043d11000d0012410302805028510492144050502001c141141d41c0d5003600800448840d042801034005042e4600700754900e2803001000401c01e803c81c0c0124031030b00c0c070700900e80c01c0e200f02d001c0309402c813803110350001880c2c134085640100030780241d03007040717804001544203032b0109800c030b10500e86800c1c2e2501c54840c0070300107540030540c2d441c44170340a20240da00d007500d0a0b00308003c449044800f1081941c1c080b003801021450340c401d02e040014400d41d410f00d620b04200000303402a007144001010141c00017460901d07104c00307402050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 410871366 1250 410870116 410870123
    0x3c021b04091511120a0f061e2303032107080105061b070f151202070c1a0d0501091b0315090c03021b0a140601050603150d0c030b1e010f0b090d 63
    0x95032401d001c841100a02848000701a9003814500d0100b20081e23a4900038181100d200310207100e03e89840000d100c14016411b8944140081542c0341d051910240000c0903030031300c6d108504d54401491701c501203071003030054458001c101e030140060000d80c031003008a0f41030400041c2c01c1a211100341500929081355608424001142501d000030300900b241c14000c8980c0b101d403200414495144d070722008a00a260015000500000d020844500c4000031981d80d1540c0d0300d40300d441d080704030b24420185c0e1001c0e485901c01ca0355801450114009021180a02d08003a29040c8a00040054031007441910b078080d00e01015940c4010124150280d4119101504141e030b91115080942814944400702480141c1d8010000009800e0201c3d0110b1a14107a90004207501e003541c9a00044402c0c45ea160075080fa000380003015098049800004010300862046074a42001d181a5160120341000d41c1141e641d09214100184a040d2880781c0c60780540c1e850074103494461481c2d90000324a05403800014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 410872616 1250 410871366 410871397
    0x615063013080f180d030503070201110c150c210103151406010e0109080111090102010608030a0801060e0a090e1f060501020c0d0f0b010b0705010b010e013c021b04091511 75
    0x5104064007c0c000c1d511400107500200003e580d03480460344107220342e014202ca01c0e04900d1480b00d2103142ca983c0507400035828100c050421845e545482c805941d030346404000c03a0700079001002040150030203045000d2050a050141900c00c1802001c000c1c0098601814441b0b070f02c0314500240d2245d5900002003c0d50002481205031043c82003490398407444a0b24015401c04001250200000049600350303c566690601260f2824074225802c0e040000003035800603058500281815032401184851501704000c4d000100742840d180c0350344007100950401c1d00e810024104020303030300480c0c04110504151251810201145003070302c040d0074403840040220351040c00101d1141c2e10103020388000e502c500005c104031190000151896910504001c0c0000c994103940380e0354000760103000c20100e0300c007540c5000451310000300301c41e0007080c04000401a409040b000d500e0055800d080c100700b200aa03020041c4843c55210b2a0300401301041c41541192600105490f440d621000c5445140c1c070110342 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 410873866 1250 410872616 410872639
    0x71202010f14010f0b09010503040809010c080a1d0a1412030f0a080f090102031005010507052b0e09060604060f020a02100924020615063013080f18 65
    0x2c0614141c00e000d41c052a4007120700200c0c1d0240781e101240c07042981619000d083d036072180e451020980c0040c100d90f0400100800010000d9019000ba11201c0c03c580c5860700c0740c61a81280450860940c600306110b104100c00800807504104804500313180181c0b1004c590f480b10340340d01881c1d4403a003880b00d50700c410002540d01905a00103040c40c003c1c044209402480d8440342501401d07800160398180000b4080741c810000b96014000810f1110720543c00c1c0c60702c60441d2480f20200c0740040704015a00341c02080d42d080d45030b6006141e043c450303504548540c094100079000c21142c0c002d42c01000e042c00320f0a05481007140c02000f0300d0100642c01441080e00c001d034104010048095403044440e644d03404030050000071810050101102a203500074121562422944480501c000038003a420403810890722100e520100519040c40702449072948018800e56140424540c000b031011807120070b444080b4000808103000c85402404061000340c549003054600c440940120803a00d030301c00c02c50800d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 410875116 1250 410873866 410873891
    0x10506032b032003070906030506031506011b0308090c011704030e0a090213090507230d0f050123010206040809062802010507020d090605090904030e03250501050f071202010f 77
    0x135031280200741c2d1030085072a43c070321065007651400d85d14583d058000380d00d0b2208890400e1001540b107a014034003002d8411104107401410304004400342e00080006c800c00202d55403c0101107645c00f428a04041c1502101c44031200c6003001400050070041d281101c840c071075030748001d80340162009940031560380f001c851028045207400d10401d4030040c140f10000d02201d009002c1d240e01c00145d24005103d01100c2c000c0101c1c0c583c807240100c495030350b96070300004102c0c00da442101d02a144012a00d4090b08407052001c0704810f83c3e0700c1003811944250100b00000d98010180e03036054101b5240380d80c940d400c0e440c0c07024449400d092035021202a688112040310741c15040240251015026a20520540710040b1816116401044081a000c000c280b030341d410715070090355020f80a0306e080c1d8441c80c007010000c5c1c1000400ba00340d245041011010304501d624003500c0000406090130118038221200700c001d0814020080003409100d0904ca20348074241c001e4101540c1030f0310f108400c0184121418 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 410876366 1250 410875116 410875181
    0xb04061a1207210902030c060f0901082814100f060c0809040c20190b060402090301180302010c09300506130b0906061c110a0603020408010506032b03 66
    0x801e910074401c98147e05250704101085031140002d2108140c034110000740103542c00140944035003022030201e0705003108802c26801400700300d0080d4202003004600d0018040d2454809400307566540038040e820080210b000f24200c0841ea11030070208081145424084801e001d035608150300642044501a11039070300c040803070108010350107468004000130840707903030f24051011203180300410014810701007031a1201840d80510014409841c150340d40c00032900b514209284580b8003180b248600c4205a0280504254003049140c0004080e181840b6a4424080b45050a00c4020384207007000da0824807075992030b030491b0040122601d030b060042c84803509140c81d01d03003a01c0400345640880c02482000c00c0e10303401450014030004454640c01002040d59012690490364488089416102520f808842c0c1000b88840d880058176140703480c4103207080d01c60040c400c2d4480e802041000c814049211407400078503880701412a9400091a400c0d0b00405880c1c0c1080d21400742880ca4000254516 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 410877616 1250 410876366 410876381
    0xd0818011409010c090e0604150b040312080703020c0a0210020a12090f090902060d18050a0501050406061e1802130b2d0d151203030b04061a120721 65
    0x2c000300200e00a20204503414252401540e6117030760700d280414501d01e080c0d0041d942c90002c980380004c255030354004141d607680c41341d841119104242c41a80b16003a4200b600168441400d0506500e0104030014464450301c1c110b00092041c50481c541c4205940b0070003041400e550300803120078440e69266005410320400b4400c5603143c8168903001b09089800d80182004141d000e800c450a284051048034050505903e03610b0903154041e0320040400c5c41004941d0125005400000310b034185420b0550554185810400300152501c403981782060031441803e04507404011100e40c00704480074845d01901c035410300c0c079010940441d008074000102030f00400c400600c54002030268501c0c46030b0407900104400541c2d5141e1414446a0301c18887e03600621501000c80c01c404095a03141c0c104004400d880d0042500002d80e82c80c460130711800c091141c00090016024003103410083e09002400b00e01c80e52414402560011010401032030154501b44448814081000c1c506513135000004014a0072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 410878866 1250 410877616 410877631
    0x51614011b0906021b04090c0902041d07050d0506040b04060806091005090607050d0618020c010e071202010c060e030c0a0302010b10171e0c0a0909020c0d08180114 72
    0x5500451507014002d40c942800c49000b500a40000080e0480f059a0501d41d00503854000761660015400554841000b9000d0031103004016100d5040000f00d120603012440d0a0b5000c0b0842070501003425040b405855840c003030244045600c0d950000818060000c04100d0358010b42040408a403424000c40d040d0710466840040b24211444121204113440c015507500d040e0360000703004103800a01c81c600034800114a440041550340e0f54107001040c0c03c810240d03011604d540414900080c89c001c0c0214410080d44600411060f414901c10284001080000030305104036034409400b007110076001002d0008120f03041c2c0c0e03185c01c070032039640340c650b04180300440055103008003d454034505129001c0c04960699a03400c1c041c04518074601034000040c126408008100706108100004180c2151085681c1042c043c1c40309040e440140c2400d150780c120f0605140107003d696040100040c10000c1506c840c83d015001e07031104100800c0c4680010b5020740d065003400d1a17105001000b00b040b600030b040c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 410880116 1250 410878866 410878901
    0x506091b0315060108040512030a02030132010309020a0b07030c0b1e060d080c0a061d011406040203040309080f15250509030304051807020d0c080a05161401 69
    0xc06410140c41d000328040000140010700c0114809501c1808170302d6200380305d141120030740102c1d6107104080343c204a480c0305140da0000014440583c0004651001d281c0110010914003010300d0040380744241c00002c58105031f03440b51f00c4410741d074651301131100618007a1f00040e81e0701014100103182d40e1a80c081a40c2246c24400070441000074251040e1564848000702425601e8006c00c0001840440206881d0302c40148071141207003d0902060000710700c03900001903007800f03508240042c442c001440c0400d591400c03500d61075030b0590041441d031009080383c00503920342d124501598403118542140071584141c5404500380da00010b8100890380d0410441c8005940c0c0d18442e00f040a44510907842e010f00d258014106280030b0006802043d00041c2545d0415840c1e40100d500c14041e00c00c82c101240c407090501c140e031707601440350000c21030705482c001b1281e0050380c440001ca03103c2e0021030340421074000b815040c5500b08001c80721207207901114002c92412455196806044a244420718050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 410881366 1250 410880116 410880163
    0x9090b241b0a120c060204030203011b02010f06210f0b0406060302041812030902030f0d1d010c08161104020706022710081909081210052b050609 64
    0x48000344900c00b0710b074007440e1041100d854100031244607565074811130301d490b002d02020005035028043c008a0f52403081c18280030800c920b90081c01c0d0b401d910807085002c4d280c00d909102094600780d000b550344200c00c42d4111099042d20342500050a54900505940022801c0c4410020030f60000c0c0c0c1101c0c02200d06000550441600b250029400ea00061075030307c465481d43c025502030b42103540414002001e545245824008043c14007400120140c001030088481c0003501078007200300000301d1428640042c140b24a955846c41501ca14200d01c510502c440e001c200800c000120a0380803c01c0240003991949014645000a03401910965068203110070b050340d03039485040c0080b11001c000400035410086282019074030648094003580c0814414550901d80410b0b80c011020940d11408610b03554101e6003407a1103003100c000e8000c040311202500c0400c241c4d83c0d030074031440c030101c044155401340c4401084541c10215100000070294001c5400704401e44030081804051031150144280761134 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 410882616 1250 410881366 410881417
    0x3090f0606010905040b041b121a030303010501200a03030e06061008010b131703191e0807020f0d091d060d0b1807030f020a0e040309090b24 62
    0x40e042207540900080843c0300c1040285440e81110900280180000a950950202024450a00c034818401094a562101d82990034510410481091142c9048420300003a00001d490388010b02c40d050410541040003405403d40040c26440186400119641d0041a1a020f8003034003540d4416120350041c000043c003103007400c4e2000040c4c03240c26034030702da126828121945a190040c0b59015142c0c61022030204c0d0020b25010910346007401070000715180c8403d80300c0100052012043d1004020b05468401c03101003d0030b0f039520354612039081205407a60f41c41c1d004c07031920101801d501c1c3c580c450500c0343c1c20300d240c010007101c00b07580405c030b01c0390340c401c200e41d8946c540807006039540c60f00414600d4403503020070810f00c00141c200c0e400c0f00c0e140c00202100c10415140950540065410b520f90601c02421450104d054200914402c0040ca200745090b403005002036015200c0c92101e551100700f01c510a5590b03101246510b480150f00c99030900c01d4034081c0206030403a414a4041400d85968400c58 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 410883866 1250 410882616 410882623
    0x2190c0f2106020f07020a1202100507030203180d050312070e01110712110d0605012111010f020f100b1c02100c080f16030201111e030408040f080303090f 68
    0x3001c0440601a0703050314030358a00d0020b5001a560a8003810144440d00041e80c0d200c00450041100c8810303030f14400d40500401c2421160f100c2ca110a20604114000c006034010068940c0d098011031200781c18140640400d80040302c03040020102d0100055005800300c58000150107000ca41c0d4030079054041e800015152000000f0300c1d503002c2e60002404010011211b41d00210841c4602107103000b0345d4074440440d2950300a0300d42110804d0b1900018400c4008054540c41ca4501086046900c0390454807510590904041c1e0f1034100503104400f0700340a07008110100c1c0307040b0403404888040c541c000f81070000300105841580300c0d010034494061070142a8182e101d856400811040512085940903241d450044a088400400602c4181e151880c84405486214000c80310708040b443d803072400908640e03400541000c4a0380034403c1c034280000c030444010180c40c042c4039141d0ba0b074a0b01d04240340b880c02154440e40f00440011400b04100c0030100245029800e131030111440701201d003410a46 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 410885116 1250 410883866 410883899
    0x40606050904080a020d0f0c420f020f1b15180c0607082208070e0103150509030405100309020a09090506090703030215060409050d08100504020f0f0a02190c0f 70
    0x680c1810600c07000c10041c4c12280d4014254011004100c04002c1c449d1030840b000c400ca111184200d80c1c1d9842c801aa180286042007071541021880c09407840c00c01c4205005101c078604400186680b1085080000c1001d403d401c2c120a83c1c040c1c0a1916822044441c0301c0451000114044c80c0c0814855090010550b4140b1740c1c0880414180000d00180c5106880d00d1815507d150a628800040c000c0d411300c10513011f424a42640300c1c02c2e60560801002c4184410031481d42c5918000400c0701020780030050f41d0507554111201c000006104500b1400b50281030b0020b54419028500025004019800841643d1180c015200265181501c01d03032079524610014026030401038040c84202100c100d2254000c00041c40013070511415280c1514001100701c20070f000c02d03c080d082c03200b440c024002c803400806040b02d00b945000420580710310180100703c40200c503240d001c245400000e000384101c00d0703040715040540480740043d00f0240403e140c54403c03010b01400700200854183c940c800b4445 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 410886366 1250 410885116 410885147
    0x5030c0904080f160c0e042001020706140d020d090203121c1e0c0806090a060305150a0e0a050c1026040c23030d110a0b040606050904080a020d 63
    0x9081c082c46200601c904d90118081c240408028541d480004d8012600c01001e8503600c40071a030680b51074030f850f41844c0d145041341e09003503241c05034020540ea400103100c002d4170f0080c60720b003ca0400303c0aa85110b401039015072050240007042d40c50700701e13115030700c02030495008904440c0310041209042c5030305e21880005a2841141941c41c50025003950060440500041c1e03d03a0400680c1d803682c0f004841c02032447d6000600c20380240807407480c0c03070084c480e081a0080710802015242d940c429640b019411030030725558012000103a001d100c9079100c6165807000d40705a9018100c5882d045172140101d88400c0d10440c800d05210b0342c0346d485a00d4071019401c2d00b103480b03043c0c440001d070304450445000380122190700c5150008280f110400c20000221001e8081034421101c16504050501d8403080300042084072a0a01c420341501c00118032240d10740080f101c068540b140d08201c2e000c1e004980140703420031644424881040085001030890064940c252164000d6000d01269a03466040803030303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 410887616 1250 410886366 410886383
    0x12150105010813171b010c03050c0a12110708340f02061c0f09020102070531060b270306010e07050c0a0f0b0118060b0a050d09061505030c0904 63
    0x103101041c0c450f15031343d101810036040c040c0340f00301100301d07842034066021700f0303511100250002c80d018000e090300004030b00b00b154142020544000c200c030181504041d0340319102c90a401c00940c2202c2200c92880d041852103035070301520102040c01c0d0f42e2244c00081c2c01502840b1242241c15040c039000802548244041800c4400e50208010ba81241d001c0c1a0120700c401880c06050083d8482d000b9a200090004503848140e400068205909940400d001d60b009614820b100c00311076003024442c40565a00c1e9840088454034900204016000325600786400074100401070811816004d594503990350b081294010901407548512003031091801c007004a0020500305802080038141c16003283c401c4800c0e0002540781c00301503d849a00903030740006041c2c01800000014182c803151060b1605003404403519000b610722092058588245c204030000c500c04d20004003d810241c09190080824007207006000307486500c5000034401c1912920450308a56082c1c200f104800d0b10642c0c000e0000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 410888866 1250 410887616 410887651
    0x9021f030236121f0c090b0c0601090c090e0c0d0c0e030d050a0507060204030b160903031e05040e090c040b010906090302040209030a051c02061e0414010209121501050108 75
    0x5112100d4403500d402c400c00e00549400c0340c4d01c00c3c00d071201062600c8041d01c020401240010300949100841e4100042d503000810500301c951400280e8181118003c1c13000052000550208a030070038895007120408240b2038040c003c900100b00b0141a40b4060010100410100a007083d2180c00d40c03402c403260140c000080c8015928020030280c080b80d40141040b520780301c41961180200c0c0d00270381048605410301000d00404142c01e01101c440d6078210300300325200b1030441d10007070b05444000244c0000c420020361485c00e0540b10303405031001031100c00344000302801e10b21011a2111f1034080c10b14082d074a88070307583c0519071003400d0100841d402c50f20742c1c1d65007500315001d00001c3c1d840802e645805100c0c140f07131600016010003100f404100c503001542d200c0e100745400242081d00c0a001c003098070885495600f0482403111002d0340040e03200600d810007946240b04540640162081c041d4814420310341c4414041c800b1844004154604c0d140b03910a0380c07100700640e40700360141c49111140ca000401e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 410890116 1250 410888866 410888869
    0x70b01030c0e011d190204030309030611120f09280201020607080c0a110109080304030503010603060506040303090513061a0913140c0706140411090709080d0309021f030236 76
    0x2071131038000e500380ca50b801c010002e00704254181d9105034400c80018540c1c280400c18030220f8440c03190f03401030703100089141075082d01300b000080d00050540320a4441081c0414000b0717800300411010a480580c02e03440c40840913024240110b003010f001e9001d03002d240300080c2094810149030340309003044801241800100d1b107089174604401d00d607079201c40d9641c018140104403242c000d540b1a40c0300303580d00b95036503041000081c01c2d14250b43c0702600449090005000203500201c04e20b05540c42a101020983e2121252002506040e03110300350418800c1004082e20300302e47c0007001c3d039880c16070ba0303031100d0703404600c00c20100c8500751980030200e000e540102c1c003c600010300038800c0700d00400340840d28900d103210000e04280151004c07a2901500000c0c41c0031420203a420319804003490414080861800040c192981000302200303007055940d068020455036180e0501c0b1a181140c40741c0c06034404002c1d8060029400021001c041800e0351083d5111445207041e07204454480c80300c0822014406030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 410891366 1250 410890116 410890169
    0x307030c03052a0f0d022a0304030803060f150a0f0801080a0f0f12090302040b0111070b0903011503300906030c050d0903031d03091c060b0303070b01030c0e01 70
    0xc1851455400404c212000088a100a403401e00741102006139100551100c00410426030945802004e4030003004a05844011044e00c08aa8000507903d035a940c6541c00a6851030701982d1555201100500a200d4242110050302d4091000d441d038001c0000c10680589001038244907411055008010035000144040c03c0b00061710700c600e0500703d6858407980d0b204032450001e070b41c0c040050102c1008000358a03240c000c6e00c501030303002c1c01e188402915500e1155226105405101c251140010b036984081e1002d510400040c528105011929516850402040580c07280e458410fa1200007400910054140c483e0041c0340603511407038640c91a0903025005805102402400d111047c05443c050242c02c3c0603d4203501e02c02d6400281008401103029a00d0102c03d001d5800c59006200002030341e00c07214040414049011301107900304a03585000405020070001054040c0800325186080090010405060f288101643d04285460740140d4014480c240715840395104030a950b3f811008051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 410892616 1250 410891366 410891431
    0x1215020a050f0d051b0c0309091b160c1d01120804050d0f0203010606030b10051b030703050c07051503151203030c0d050f062412010b0307030c0305 65
    0x107003030a908003140c0c09000895508450300001c2c0c0d260300c42e400c2100c1160f00440d90101c1070704100b086400c041c0a02104e40e075074040c40d41c1090207400c0480c0420701020784019001c5911044058241e6110151541c030110710318500c804586403c114100802c003015216840000c00301c05480c0c0d2545a0b1a014141c00c03d560b481c0415500600708210100b90f07919202411490240911003018104041d8414142100c910750f1000341098500304c905541c03a03481c4d403614442541e40380b428039210b081c503120b1001003140090041c2881d01c400101d6804240e00440604100b168603401d40c0c0a05565105120100c28940116011150108005601000300e00d900702e2a4990142220302c3d07c4e40c00c03c80641c0307554800e50320303003008080100f4003000c0d1410074040e450380151600416406803d080c400b0030801c031800b4595a84d89140092800c030082d0843c0e048c0d0f00d002450186a0303416580d43d0100b4421540180e0381d40c40040e040078194003540340640140c074020195411a40341d1007041c448000c8090005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 410893866 1250 410892616 410892637
    0x9010605030715142118060a061401120e0304080a05070b12040f0807120e0f0a08071a190f110c090c0a0903080d0506030705090408031501091d06040501121502 70
    0x40710f1040e6581c40c1240c0203188642841b000200007800e41c0c0440c2854000003c0041240a00f0404240110811030b203204000040a0030004858010a414500541800c090702c814504c00841c0014810100045501c0c0450144040c0d501c03040c1c0b62204000980f14280c0241c0e901a08035012a0001e003d0101c0107030722078060004941049100c4e9207498844c03200120980c0054103508a804075032804c40307164480d4510032542201814500710803152114074074400c922403000e8488007408043c81c0f00302110106c4c00402c00341035420341d42d004003401c0a000003060f2400682407000c0081c0c11000098610ba01c021b0051000c400c0741d4031618100c61b16804007000504205c0c0c0d11400100046072030010b000308038500000070645281c07000c24103240c41d503540c2c0040e03c613624402c01d000100b10654101c0b5004005040803d61182d20b071401a034814140381d0042c0d81150301c1d42200003031305076030740707006400349404560500959a0320150342a000c0e6806001904002c119465101140790550060108294 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 410895116 1250 410893866 410893897
    0xc061501030b120706030501050307180c0905100c051e06191509060806060303030717070207050a0603050405060a2306040b041514152703060901060503071514 70
    0x180b00c011410305090b0418102c140e03070048000348441078240c001d890141100f80c0007051110700d00104205a10003951805222613621a00001103610694201c0c01502024200340c19002602c0c5000303160080221041e0b60a010300c807012034650161740060883c05022800418031502c5021400c064000000140c1101599802d280c00c3c004071039503811002481c2500340000c6007480d04038842d04002004000a00ca40c00800422600c2d9030850030302e90f0900c00302c965500d200c1d0340c0c5100507403400c03200d900019480780102400041441c0d050b0815841240b050050710700d1a00e48605040581d1080060002c0d0040c10714800ca40f07881d04030340000d0f8002c400900200c0d440c83c8020202c0c4c2210746041800843c0703088800103201120b14006030700302150054411880740d01c0d240070700701424080c6680d40e0104000b40201411004140030002c40c90040050545030306007400c090860091000388121800b1b07000303469000030008158500300d10642c03065180c2e0324442d49010707da00d00d19404540c40788031004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 410896366 1250 410895116 410895131
    0x504110906040644070b0f040503060103120f0e01050f2113020a0602070302182509061b15050702160816120215030903211b0c06150103 60
    0x4446014a000700c280310116603000d02c51104c00c10020464500302601d03200b66110503218038080007864004840c0403414103078891590b100c1c41041403240c0c0d4040f07036162107440c0000c0144105103034102407426940d29881103601403e2000e454801900d01414040f5000780030506000c50120001c5c80e45502072041204d074180c1c41d10320352a9000b0140c8070400350442080300001181482403200c800b40c801400209031951860b030000310040c984c0c15280c2040c40800000c101c01103252012000103445c980d81c0d000101114600046c034a000303910400b0000b81309003090000076510b05c3c4000c080c0d2a00f00c569410380c2010003000a001d054090034002c2103116402007031003218800d1440c2400b410300e01029040c4001c3c040e00d500c0101c00c003504252094648034401c0401039403803042c0c032062990380d00c02c105d403240d0b40d207c0c41c2401d40c012003041d5503c140e00fa401c5038280c180d465041178810402c000305c00d0340201040b50021071b02c1c024031840c06683d60107040801d00164981480c6074050105140115001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 410897616 1250 410896366 410896379
    0x40506040608070b090102010c110705040c051c0e0610060c08090d020d030503040309151215050a1412031218100f290303072303070b04031205041109060406 69
    0x2400d240e04c4107014400100303010290f90707828051000c8003480ea03d087c001c05419002640c3e2551104c0c070545215071703980c040c00d442c500d0150b025100c07010446000c2035000c80c15501d40c0c801401c055506074909004e1000000c002d20441c0b40b446068640c155a00c500801203a0b40744107a5a0040c503800b5801400c00c01948016074601e4030b482c041d00d01c44d907100b503201d04107841d006e4460740044e000b22004601d40c9060943c40ba03403107003182803028084d10000c40e084481090700420f00400c1d07044039401001c030620100394000f401764146401103007524294681503540030115101c6c01000805013801041002003019590349038000d0b002d055091003958494100003a60400b10b0b250450040105034545500b80b1103017503075104150301c0101e400600c0b00d2603100c41001035220300c42c0c040020b0180341841c1e0074004058400081c440701c80c0c40e650807243da50b0005c0c107201c01c80080440c1c084000860603105040c140712a4021640519072020a180c81882108200002c00034001c0c07046800660f50600003454 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 410898866 1250 410897616 410897623
    0x110d140d020405040e1005010801181b0b0406020304080c0d082704050403110d0e130c0c080703030e060c0903070303030b121e0708150c0c0a06051014100e040506040608 74
    0x301940d845c0244101d0718150415420346905900c80d951030b926000e203c2d902100340354820311802d54800d24800340c0800404848602c020f039500145100800401c010a5143e0000300400c1960b580c0401c565072014038004110900c02c080e0300007000f19805210f401c0c8080b2012402c3d59546040c803495032025108140880c0c2181d90890302940005c03030703001c12001c00700014000440c031401c1c03c0c81c201c1412608070b0086a003c030304071000f11584c0c2d50380340104a1080d00c00d000344d010407a4030564095444100703040050151001d01d484031240d02078800411404028802290101c01c40540500200781c5507031800d0380109110482c0c0ca03004101c0100c8002102001e010050640840200c2d600d801511002031a01d01801134028140c1c44d4420118050343da004a03108035400030074016219a2000f0b014011420700d984100002d00c00390030001400300c0c100f9008018001e507143c0114102c003000626007008403c0d0307600501c0b40041401d4030740480541c101904042d5000303201600c00300c0c000d0780d01c44d20380b4907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 410900116 1250 410898866 410898881
    0xb130c0c06090813140d080306030a0f061505120a0b1e1018020a020a11010c15050f15010804020907140a050c010e0703020a1809080c0a03110d140d02040504 69
    0x107028a000600100b0324985100244c05020b800070810a004001c402040d6501c00105000e00001d01c0400014031030760302003214613032890303000942102c0c00000d46807140c003a0100301c90484600b10407417030200d00e0341461545240d1b901140c1005004c1e044458803400e50750080502070002001020301503502043c6400b025600030348100d84030111036850a854400146003504c03000302064010040003001541c0080d21008864005030030f0603412a04c0c0c40140c83e02982583c0040c03a141d5170301c2e1403a070307800d0701036010714840d00407002c061032580e54890601094102c2016054081003024020030050b040c012400380d0320010a06140d400c10205910f19001900040c68000004100003094001d040c1300703001b1840d0100b62030004110a6095078005400141580502220a01c80a1190311911900c1d000050340395001110303181e036102c988002c16111700c2700d800240d022400c0c40c00f00c04200c20700001c0301c5a414185948500d01c640030b118070700000da4400e9500c0340001d038007403201040300e554511900c0d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 410901366 1250 410900116 410900123
    0xf1b040909080f191e090302090c0d1107030201050717010605031b1605012412050c180609060102060907060302090a0f0902030103020909011802150d05090705030106090b130c0c0609 80
    0x8013a4107021a00526010148208034000d0100107000c1100310741045841082e40c0c1e0445882c09241c0e6407000c4022076018030340c0042c02060422482e0724000510310010000030f8001d03402806642d40700f08040e03c0b400640211080d80745800740c010001d40703100380040c0d0b0b00326168032003079881c560704180000c1d0213030030020218100405105011042080034803d9a03c024801081200000d90050001c0300d114440d104170910f10212856890400800380030403800c4000042c41c0150407502d80000701c80c191001c8034101d0003804058042410b82d80002913452050300e0550080071041e0410204602a400410790f454000340c02c0716000ca81d103440f003050701024050403e0010303129855401003100404025104c510b06d82d03d0b014205c3e02c0103240761088928a601901c618810902d20480101603118074101e0445117858001070042c401d40215140d0101e1310101c000b8410261500424000c03500c0c1c213001540d0045000403281e01410058000306001c034154100440f91000030b4032400d003074407801e801c102c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 410902616 1250 410901366 410901397
    0x51f0219140d050d1a0d0201030e070f030b07030513050a0201030e0c030f060708060a0e040308060d0605090c01030f0e1b010c0803090a1502120a150b0c060f1b040909080f 75
    0xa069003070617441007040102d900851900700c212002c000c6070341c60440c4000a410103880f55141040c813101042150700400d445000d08555503580d003410880b2520030740380f10002a040001040e62591440c628080454000001e81542401c6600640041a14203030b91a140d008080903100907039000d100d080519040d0a003c0d10042c03070603c00c001c20300c18006201c18810348140e0390070320840144040e019849549414400401e03180c02c00003079864100c222006104a003040c080001462002c182c0f9507154500780c81c148582240e144500c8280d91500d14100610b600c4160302410400801c020034070241d1043c1041111000702e0b403a490101d038003c452840450388019944002c1112685400f8078000340e14504604000403c0c2e001c00d07458401a1440300d2864803940f10040c803c4a81600340002c0060009556071036842d8002e071038581c1000c40300688040310860004a1194090920701907d03086002c1c00c1d864142003024840007450480d000303440d060380a100801c5002030040042260b81c6c5406082c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 410903866 1250 410902616 410902627
    0x91b0703020601030506010b0a020a030806190803091003110a0806060d05010e01030b130b0a0c02120406020c0108130c0e09240402030f01061406090622051f0219140d05 74
    0x24600e01081030741b00510a9004200844409d43d01183c8071052550500e041d81d01ca0326001c000800c26604801076071500590f501c000100d00c40000300424070341400391080002294142000ea044852200c010600444101310104a0758071850b0050b07070002d40200310606060003517100404480d002d0300044290102d0340e00510610100001c007a03480482003007502955021559001c00c050805403031452110303103511102000c80e00a022440b101501e11300e041d5202c2e9134070500256a074a60300308081c04142550701140030700001900005049800c944640402c0c4c1c40c01401040c1048011f10048060240b081b80781c10b691840c2c44072600246c84801c450015091500400d8104840c090110869a14080e02042100741c044103125984d542101d42580325000b01010030480d10030380d50480d9042d404940c2c4825103000245444040d41d0003a07038101080850010041d18400800311140007503400021046468151b1000c190750f41c0780300714401c989003503e40f40d0192514502065010103e04c01049 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 410905116 1250 410903866 410903873
    0x1b03020a0e04020307120f0b0a02370c03050f0a09050f0108040b0c091801080f01151d130609060f0509010c050d02180a0b0703170c09091b070302060103 67
    0x1200000340039203902070320060815074002540ca0a09124500000480c98000d405000024032403a082c3c43c1c2004607400540b0b807e19140340294014114078159400c1004003d541c01504054848030304c003a0482030080d110000d0040c0c071461401b680850411030100103e02c6044064000390072111255160b0582550074182004198a40b00e09a5810003800408010101e1031400f84590400048003003103a4485400001c40d108400510b5045070b00303c182d00001501e12170006100d010b003039425000300006540002c01100055044c40b90492200b0720501c07440c9900c00522103650032408490794283c41540a0761004180d40320484155403141d07450891422130315450084070340c8012010020001c010130b9a0000d01280282e60040d45c2c0180d0100e841041c3c00540101e91044100041040441c1603840380402d2103540101d5044000640101075032840301d01900c03c184c00b502811034641d0624000c1d00070700c58240c20040101d94440b001000030b9503c070300320000414605000398040d1120758110708 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 410906366 1250 410905116 410905129
    0x18060c100501031104140f04050309062a030a1e0c0605040506041b053618070f0f060c03021518010e0304140618220e0f07211b0302 58
    0x1040b8600850030010b82c400321b20001000c641e4403040c04200c0380100d4449092a40c40c44c002d00e500150801c6000818007849900003513450503103001c05031070001101e244081c254803800b903007500741c001ca4004c2c1a001100c0180d000740354003450b468034000c10408041d880d284243c0d8030598060b030700b64212034140022b104401051251280340d02805180552404020960702c8418203120001c1c0d003001d01c04900c44510540d2075071141905017600504505100e8942240007041c407c01010522640800103910090360b501032048481d1403844150142c54103500b9208004107440480850050a001032408054503009038001c0d20b03c2000c02044202050040f801c4540d0a2544107080c0c4c4107010403c518111002801040f40d0151a1640c840720751034041ca500b4a2500c0c05243d200705400007200e00003981c401118070341c47c0d04070010711500350748a034890b440b002ea070400d40d040740d0803d040c00e0005810b1803450a1104506085110760300c8066100c0714144c862541c881041d081e10400304000350715001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 410907616 1250 410906366 410906393
    0x114030c0a03030e01031112041a09010c0e2e0206090c0301091205090d0c0e060f01030902010f030e0c130c0201050708070c24050702060603010e03040b18060c10050103 74
    0x140d407201201419a10082c1c00d010740c2102a604150700c546082c426150b511040c1c8a000c41007818103005030400349086032020800406044103c18003800042107000140942176115180f40c40b481040007903081400504d140500080e1441200e4501000c180349440018640c440340c11ba01800c00c3e4201944c0c030354100007120440320301c00d0b0305280683c00812041e00195000e0891800c005603503100c00c401051034203440c49405440310010040001e0f4030000f6590f032501c0344c5c0040321480380c43c0c0d440e02d006404840c003c4102038000388050305007035a00c50082d07101c00301c101140c804a450640c41040060381050395103101c00091078452040a01042d02401000e4000c015400c060405141c80e10b4000c148105901d00a0101c260305500c42017036060803604480c50350641002071119290400c00659910b505691490082d860041003035010403010003502e05a03551700b43d80d030b80307058284400856603440c419a0260710440c01c00c19491044800c214003444070000300300100c0eaa41c03441c1055207180000c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 410908866 1250 410907616 410907619
    0x80909090c090c0c060a0c0908030307020c0a090203090d0e0111160503070b2812020423060c0c120f15070e1e04020310030606091d0d050a140904050114030c 69
    0x103221340104070901280751a40005480400201d00365084412100703010b160340070307036541c0c0000000e1040c0c440c1c0c0070843c16404c08007603500c0d00540d40d980a51004900c070440303807281c0c01d82100c03804090080c40b40041e002000b005241c066040708040d40a142098050396070b210306040f0500041043d814284804001052101c08650a001c12502600240714000001000b40105800403e8510f40580306050b0111b45c509021034503a510707144070040051280c00c60311322034506491103d00501d4254104e99201144502400481d00032105000d40c1020300507413440c00e8000c031520b87d01c0e25071040200040003860341040e030016041c02000070b000441c0c91000c280c06840c0e65000104000c0c4da02810b5241c01c131080d0790041e5660303a03046c8102c40e0001907803c020180c90400c8000102056181c1010300107009100c1c00c0b000b4042e2404101e03503034420481e000000b0501c1442400c1c0000d00440b1041e09074441c40010131b2411f02404001811200c0903007000582c13003ca002044002d050410181d0b8900c1d50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 410910116 1250 410908866 410908891
    0x90207050f0615130204030c06030902011205060609190302030109032601060f26090d0906090e130503071a0703110a0903170706090b060102120708030c07080909090c09 74
    0xb441070200c164001c0c90900c05018802c21321124a2419117030f411580155000144015070340d844202c02405014216800d80c00a00754502482e0344007550300c41e01780607050062409180c00f003410b007480f02c49a010034001d942ea0800540000160f2420300945640d14400d5880c400b510003548140940405c102c525015803080010040c020a504094000b07040d852500b811401d00d9014410740c0383d18100020b0800007540300c4401d1001d070841c0000c02ca1540e2040d906d6660701180c464108a03072007600343c03240d1040244106c0100d0003150001d407000c0c841034000d8041e030380b4000352603c0760600030055985c402e0a0031038080400c448294548101101180d00c202c2c9a4601003c02000911200140c08060f0400c0041c02c20541c0100202d0204c4210560110040c8401340c0039017040c0e40400821220075025004101c47e01000d06860700440701e486601248590554685c1c2c03800840700e4000044c122000281000243c402d9038809000c248100312030002001c40d464000c090051074031f0080c22203401402c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 410911366 1250 410910116 410910121
    0x5010515070302031e04030f12121406060706090804060809060a0e060f22060207050708160b03040609080f0702040f02090a06030509151812180120010204090207050f06 74
    0xf5404021100d03400c2c103a0391042643c175170030034018140384101d60008096014034080341c420040b803000388921200841e102c0c2140005419180c4c400c2d200400001d211458451001400c1031074020301034094280101800203985c1ca469440c00b0080d0701542110021030094030400c050854100003850b8090081c020611104440c10032003941c03a4005046d0100d10a2140005172030703943c60002c515001c1c40c81e6142c01c2d04114032400d20380001d602000040e1020f02542c580802c0040c1d00003600d50440d1914440c081c2c40d10300d000403010281d00007038012031b50075403101035040101d044203003e402000d0403150085c0d0344000c107204100455007111000c040c6a0300501c54904541e868490175800c0300c1d1076090101e21543c0d1503031094103203459009903200d462407207002d00000e14080d18521403d41e85103400c4800c480c010b55603001d0240503044c1c0307084201c500200303120740c503500c117000c00c00da44e040307505e01946204203c86995017681c005400146405a0101d14481031040070408400904c0000000d04103e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 410912616 1250 410911366 410911373
    0x50c0c1801120f020604090e0f06130308041109040c08010b0409080301180605040c05090108100f06030c050d09030203130b03100308091203040303170a151413020c010501051507 78
    0x900501c50621104001d18890b01840318803201c10340d000b0b5000f0a1581d0b9507440c1c0006400500d0101024a120f201310344002054510000c0c1c800d00448581034110300b100c01e603540032110248014400c445202c4490b41d410226161144140d009611600122451a00341800d490864408080f4240304038117040c10000400c0c2188102d0341502d00b08075100f02e0045031110243c000c3c00d2141d0110390080c2c5003d0340301d01c4003a8000094880e460b805d0780c501649440f2030040220403605405410aa0170608800b040410b009611244100e941030411500f00021100e5134003c0350b50024042c1d0150f0030003c0e540c0c110300840030002c030251a020303185070b0460814401c403040319000c90000800c00c010000781041c0594032052240c014010200441b5a69500da1074003c00c60185098091414002400480c100d4860360107403101020740509900896890a840c914001420f0f0040c50781100080e00300b0018445980002d105600703e80d4000705141d40342009019504801c0c0d264601068414082903001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 410913866 1250 410912616 410912659
    0x31006152a021c0206030c120c0403171e03041b060c030912081e0909010608070f0f0905040908220b0a0e0109090e1e030328020d020a050c0c 62
    0xd8050b1220341622a0945400b01a80c9065901079840300020041052414146004003010b98107030380440880e0f02c42703210150701400b0f60701000386901c800703018050071604410050201c00c0092650101d40500904150416038400d5400b40e6030130203071000c030b514400006402807004000c60f02c0d007259101c8440d14014004901c0e40100c20380c42c0801c1f08410180301500042c0c80e000801c05202000100908a0180c00f591124007564090081000000740c40c0d030107060034610400158881c0b0103101441c010464180703000c440c820003032014042d40443d06407101d10449089a104150982d901e4407004900010380e0009555108404d02c164024040c003160311050f03880c55606401c190b007119a00700d00681b103282454210070002c034602441001c6031680002c482c1038011a00700c1c605c42c0c1682036100c9071785911080719018000c1110411254082c0c0d82c0f4003140991496401d401403c2c10f40e01502103042e030b801820301d1800103202060301c4109c51010b12150780c8650342183c20318900c182c642600b055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 410915116 1250 410913866 410913947
    0xc0a050a0f23040c050705010501061d0f0112050702010905010506031c121803050d0f090206040b160b0709081c02071406120106090914060f0603040203100615 70
    0x10249056102c210300020000c6020080c40014000c0c01040050a4018090b800c001420f680660800300002001c074000e140741124039030940c000d52440e00b0542c043c05a60505a150b181c10001200c480d090100c18920405001e001a40e00128010b1414108203080d41c80180c000d9200f038028000840f5102040300e29900c2200341c90921100480e505403040c0020917068100c046540003405c00f0303004042c0d004000b400c5400140070b0030451040c0c2c0d1210542103a81058009401c6181000b00344001005200a003000184240b2082c0a0300c80b1b950301c00d0722610041e030350040411a108030601c10041c051241e002600c1d0741c810890200d50203040025601c0006100d90742400701180c03030103011901c98404036140b8007805a0300300701950392a200109205214810a1200751815070105480c89168040300d004500003050f00030342c03119010030018564809001240e0610030780c45004609980c0380500002003044101205a04410351005080c2480f0505814148034a100a1501c807280141c110803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 410916366 1250 410915116 410915129
    0x10b07060504020d080d02120a0207022107090609090308070f0c030305040206040b070506090c03120702060d09050706120f0606020a123605010e15160b090c0a050a0f 73
    0x41c0c03502c442c004280c820380a260080d020440029402250000d213800801c4040d000b068019001d0303866903280d0007280609840250322442001e40403c040a4031404030342400c1d1000143c4405540d940d0505085038450f40c0406035003600c0e00b10b01e40605802441e6554807104130f050503544920300035402000f00b007070700b00c1c001c2c145070f40c41010409544901c401e0b01c0103040340b43c82b8140e498140d4200b09070344000c02c42d0440c2c200d1203281d503101034604000c92103084000940f0440360801d1510785c00c1000c0d42d0030681e00555030568400100010902c2001040010040c070348890080c4200304c3c0103d01952500b80c0000036440c202481045029070020306c140703605401400b000600701807005d0440301c2c2d03092400a03006100000a0900c1140c0600e0070000302da005d6901c04400c455130310b0780107580020303c04000d180d01c20b101402c0a002d4048080c0182043c81400d458188810880d903201c2080c01e10a45000b005584070151010f07040c10241d8603100a0401100d03a0001c01d442c3c4654003014030010f00580f03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 410917616 1250 410916366 410916371
    0x10e0f010605010c0c21080c06180705061c0e0d1e030203100b03130c2c0f0708070905040c09050405060301091101050706020c06040b190c0503151801060315080105010b0706 76
    0x12010306814006d08409900c20326407071343c907020001c07d01d554550507240c202e8906861054502d0701c503800150725040703c00c00303000182007181061101c80c0044501000466860321809011656802030060210019072511002c00c1a141580d001101e461040b81c080b013418030400602002000c511000c10444000109603a601d0392000302c8101110003011300145001081d41c00891010307030000c2e5101c210442006c0d010524480b00500c1c0e2814401520410090801d80c0081015035105880040c0d00c02c0c10340c2841e9440c2c03603503000494111081c0e0950000080c5500009000d2442d0a002c1c858212104400034400c444482e2500d000d00c280c0c550625051000002d044000c008181c0c0546860382d0800c5c00742c500340c6c5401c0c184189211000ca808162820745102100300084c01846040c041300580d40d210f608582d80d80c64400030340e80716005071940c0503070718900382c9040b03c1e50030702c50324003034401c0b542d0114141400350f502c4100e0b00500d822220469040c000103002c1d02c0b08840c1658489a00070002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 410918866 1250 410917616 410917649
    0x100207060906050a020405040b1815060408030f0d05010603021e0a0e0910060809150705091f030603120905010225030503040806060a1d1611010e0f010605010c0c 71
    0x300078110080028005070512040041c0c4803140d50240c811240296014402c1d14500e008211140003003902c1506002050700100d10303c5060220200b4208038081c212529050300c0e0000a0314581041540390b9803d00001340d0f0161044007401146d005010300e090960070100ca410203203103c0041d05003800482ca4022a007508804d11441444c3d002e5800681070840a0500c40c0b4070054005603409070301c021030401c2010524480d4001494807405114040c1c0185a0711307201800c507403c0c3d214004056020b88405404040004004801c011a1205490004070b6524602e0b1019280602c03040356018003580500402440e60080740803c1c5071282d801074105000003040c40b040076074030320f50800390040c803011601141d80f140c005409070083d0001c6551540c070b030341c2e14104800c159051602c03201d140310320703500461188003150116142d03a801a081c4103030346080c011803417401c6524600c0e44149580c00a081d014101000b8414000907120a00e4009840c124070303181c114450b0b40c00e00c52030000e10380300c502 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 410920116 1250 410918866 410918873
    0x7030f0209040606020115060c020904030c080f030f040b070305010f060810030519140c010c0b04060b030f0d09140105030103030c0302030c07180e070305100b0f06040b04061709100207 81
    0x4841c034000703009008000c4944c0700c8038000e000704203240c048101110241c10108041b4041c1d8002c0d00810780c0245041d40c50303540e50b5000c540001c4050412107440800341b02e40c46050301c1d454083c5204010700c40c0500314503d02810160404030014022009051410b00188204044c2801420660b2601d0811203000d88548146410690f6954000303007040c0a00c61020900c0822181c40018081c0902040c0080702004c071203640d1941d0a010341140450700700300340705000804070340304d05a00500a0324002003407503404000c00c0c200080c5040000302500070b26861000103401c4051a0003500c1c0c190843c1c451800783c20000b9009100600000d020f00015852403005c0610030012500c418011000396201a66100e604000318211301012707140707050809c11b036070400381000101001181d0f00b2a0003015514181d4000307000910362a03095642044085007607444944858000340020400c4800140d640c0e0701c0c0403c000c00402881c443c0c1e80000207200107100f00c485000500ba01d030a4601b10300140e95100600d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 410921366 1250 410920116 410920121
    0xb011d06040c02520f06091202010c1a0a0c0216120212070e04031403070c17120112030905011103030c0a050904180506010b0901140c0f0303130201030b060403080307030f 75
    0x501c001250440403c0e1813012610300c09100019110360104210705625000e407902505200d02940b400160502c904009291444040d10305180c0113040041c2070380140d4a0744080110741049030440740884c1024840711210b07601c1039041c0c2d501a8400350066000e00380c0420200e0703600e4410b803c200541160442c06564a111146085090540849210990302c403001c1e5a46101100d0503030100c0c140f40c140c2d40c01e42c906007080380d204401c69a40c4130314501c003a40d10b92113407aa004841d2040b0740c00070f100c02481d80104000103801307000403500c12000c10300300c1e25004003052501c0d00040c0c100a10090559509000001030365004500f44690399200c0007506c108075000d003d2405080d13400b508114000c48404529504e14002500501c02c0d41d546030380300c1da0344880c244201d081c100d0020f1014140c0d40d40940d440806410125044005d544800100301405440c5400030782c2c0b5050f020514100d884215a05072058490020050360f41900f85481c40c0c844c2c00301400b008040109164841702c02e176084aa456 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 410922616 1250 410921366 410921443
    0xf06090306070201050610110c040518010204140420030a110706110c120f041a130e1e061309020a0b030702070e0112170a09030b011d06040c02 63
    0x150407100145048034000740a444160f44107805640e010040f200c055200c0d40030600c1c80d01d80000202400302600c070901000b4140201011440c0304080038865107007a081c00200001c0545290f00401a42018100000c6076091015410321901c0000c00d06510050041901e9110802400004070303440700c0741e040d101a104090340103100510300200401c0c0050090040e03d54841480f080756400c258550360280307288980204d0081c1c41605100401000d4414200c0207141c500c140304040c1845c4643c80130305a05030745600045034050081007040500882041e090004481d0b181c01c1280c98108a008511300326440d1811505482d12400100159244c4c241844000c104103510785a6900c0c0040000b034407411580100034984141400004007000036401c2c1e0b040b50340d00140a14824070b000780362040700d030b13001e04042d40038040b828500002240c00a65024001c1c1124a0701a0850410444c2d51500c54002080a8419403800c45244c40c802c0c0d0021340007002140102c1198442160841180031034040b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 410923866 1250 410922616 410922619
    0x1e03130501050a02040e1e060628051902010603110d06090f030201050a060f0302060a05030702120301030f0b010518040602030901063308041a070e060a1e1b020f0609 73
    0x2e000078007215120720350007801201c007425090110b1f621036004100d03104640402c0c1c280c80c485d580020071180c2c50b014008107011000160341004500c200300d100c14041003c080c400000c52030110b0b4100c0114444c0410240c000090f100070807815083d40d465403034440c0b541002d43e02500c0c0014059003004841d60261902c6500f010034244504003925000723000c2c0c901216103004070f90038207000003440130301441c82106803130740140601e003814400c1100b01c0c0c441d08010003c0c01140f00d0348496801741c900c01030040d40610301800442d280d01b4010b040c42039519106a100300d00580d261081600f01e40403011200c0e03040396001001507a00c0d00c0b003018441c094901c82c2c11070350f548404120710380d80da5104101c20800101c802e03905585100070501c02078500310001ca802411511020b00110030107003010041c1c3da07100116080501000300208045916504155100c201156100160a072000c603000407158400d110340ca001c07004480704211444c3c03c0001e41d0802801401c58100c030308800e982e508181d482c580d40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 410925116 1250 410923866 410923871
    0x7150302090d050a30021002030408090a060203041e230a091409100c0203070b060114030403030c020f03092d0405100906050402092b0506010602030a03050a021e03130501 75
    0x281170803442d40c400d00064004421002504a4500400c80103c0801140a4000d42200381203229644040d510042048031402c41c100078812044d81c88412080c0138001a90056071160304261071040c50740c50381c00c80d02c10b1140803075104010709802d46c1020401101c00003403001c5030a02c4003001c18a16a41e40d08009101070900c4005202c0740ca99010075849401c641045910543d100380c20541125068040d040058100300604404595000004c40e0400010303d0f103400e4001e8840c085c03840942050303a04800103610741da4082d01469042145e072400355008401b079807400c0c110b01d000450807244060154554498140c18201c2c6a030a143c858102c44009001440700385041040445694200d0141a01c00307442c0c510f0100f90350600d131095450074034018180b040303410304000d1070300a840900065030200d445958444d4001420034131205000304a960011031315025818406810758a0080000c1142c1744103003c000910420924240c04500c04075034081d075261108442c03401d0045044002410703c3d130 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 410926366 1250 410925116 410925133
    0x10e12011a0f040e0c0d0503040b04090903031d0606010f02151315061a09030a050f0c031509060103060509100c02150c0702030a083010050307150302090d05 69
    0x81265585001800488540e41402510020001101c6001480c50313050340c000105003243c3e041a03000205014015030880781415600d515000180e481070b04404a0291615542e0b01016014002d2500c0301c240c10b550b250312204c00e040c100b6a24840100b005040040641c0c24800e118002d00102140c414503410311409072420640050807a0f00781031040303030240240c2c407805242210922850041d50700e1040c503a41d00b1300030302040c3c1c90340340c00692071191f1500800c40c1d0000094000c1181aa40134255070140800c0d000b14000c242c148400f04000303004512201c0204451600041002410741c2c0c2d10003400075603500ca07188242c0c64120345406c1c4920851804920214254001445105000700ca002045003035a030036a8808103801401d100079013541c4a0107844002030302d024044c100b683c516000700991000d5000203841071500440c0900f030008045c2050202d4941e18a06203c041e01003030f0000c0503000c1c41e2144008017400c8600065040542c0451104c8182e520945150010341d009000c4130003c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 410927616 1250 410926366 410926391
    0xe011206030b011509061706041a0301023f18010e10060807050f030a0201110c15031005013f0c110606040e12030c070c0303020a1101020303040c05010e1201 69
    0x240d51100602c0041900d886001500d00d114010020b1135401c8554051003075200e240c00c1c0320140402b162001d0101d05880b00e0402251001d00c042c04c0d2541c80030244400040010070a10407405c2c0300314442c03440d0001e01042190092400380f41e103400842c1c5d016246510740c0d1440340c0500400117a0709028680c014198000600100d40c1c200406403060301c0c1c02d40d10a0ba9945e0100060059940c44007070700b541081034076001540c0103c50060b0305c000054162000280c1c8500040c1002c1b03180c0c0d0006071840b0011007031103822260b038a00702c00601000e0910489200034410801803024a0001c010184041d481e001038000b0f81205414203602910310050010141c210405849019141c030701511911076000000c0303052405005030442c111022000d400c2181e0b80081e0514643d0009100c010600802c0050b0000514130401c0300c00114081d40c0601248916072410380301203091202200e045520603c20310010074140c0001d4002c480090901c602200700c404c0103d00d60000c2c20040810b00c2d46440d20700d8149 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 410928866 1250 410927616 410927639
    0x40303052a0a050f0d0915021f02040602100b0108040206031008062e0e0c0a0201060305030f0307140c06010501050a0c061a12010908041e0e01030501021b0c010e011206030b01 77
    0x4441c403c80030391390f802d00c01402280d5075200d000e849000185a82d0810003140780d11800113000300613984165147c103145881400b69025040920083c0d00f13900103000c000da03540c14080141000b40302031084c4542120100000c000c0880031f800070b88252000400b0954224010104c2002400c1203000d0311020b24012010008060105200800c000008010496080300c00551030054850307403048002251650440300340640c201d0800c950640d96502000310100c0c03030404c0030304100000080529582e240080004209000024000000d40c1c001e110104000c0c4011030b41d14196942842c181e9250700c0255000c490039821840080c103000c0c50720800c2c1e181e800308076a10410b8a00103030380000c2c0308080001c02c0307800c840c0300c2c80000d0724108007400140407100c503882c00041a900300320469100c02d9122107030f010400740203038000c80b2035a600244001040182c5244100e9042111002d480c880501c4400a05455010803031b860400c000c0c600b0780e01c00059941c0c05180510340021300d4441541e15100070008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 410930116 1250 410928866 410928883
    0x326010f090b03030a0f08100e040c060207050108090d260a0902010906170114060f0316140a05070b0604060909051509010e1207080d050a050612060606040303052a 72
    0x1207440c10302500320014200081114800303000f80d595021030802209040f40e42d80300244c1540203090400c0c00000c0c08001940e280e5000750f02507114400103901c0e0420103460842035230300150601110b00d040124031031010031403210441250909910140f1030340f09104586410041c0c03845108503c0c801e10109503c641d20101e1503500c01e8981d04480340e1950782c281c80081c2814865690080d00b28018071601140b103218042443c1c01509072800c0c1030300c00b1300e80503907038004032a0a60300e268810f07503090b0795503070041c5000e00110007d111a494602d504034010500d202d040c00c098071020550000c68140e4561382e10003402001c28180411200d483d52800d182c072400202c025004002015010803580c0d407040c40740c1d01100800600820303400e0542016402640c00c811004c2e0f545c2401841741c595190f1a078003a151180300c00c400d0014051426400b08528104217000d0100c80d0340c084001c2020b580c50328811601a03c2d0503050081c0c0b00e001c04040c00c031810f9074402c0c1c00d94100301c005d0210b0080c0d0030300095200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 410931366 1250 410930116 410930129
    0x12060f180302211c02130503030705030316090312110f030c0309210c220c0c0b0702280f020d0c030218040c0e06010309061d0f06010506070326010f 65
    0x500f21008050843c500d130080d402d03825030718446136100100003209640100382c150b2036200102c08443e03880c40003d065400041d8141c0709608000200308440700703100c4149081c0718403401c1224080d415511204001005c0c448000d0501141d44900b40012500300540700c2200c54800403290740742c445240107600c941020007000d000e40140404c034003412079030074401c070703048901c80700100941e10005041026216540c083c2000c0d0110f541e29201120149020b07620a042a50f2a00107142006260100f070902c4028000030442d00001070000006005901c0070562081424a8a50b90241418485140b41d21020004d60000840e218801007000c440020000c80b4000c903803021031074001a100000c1d0f08000c80d40142030b00718400e0140540e41c5a081c0954029406250026000c00680e441c0d404a43c800c8249030603040000c00281803a000411204030f01880040103840715501d0040820554002d02d9001004e00800c03040f007447e03408a074140c051400c001c030075401c12a544e55016410202c56503000c0ea4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 410932616 1250 410931366 410931403
    0x8010c0201020304021305100914180d020c040c11150105030c0a030503160606050d060e0c0618090a140a050601021002040302030c13061205012412060f180302 70
    0x211428010b1003501e2050790007a2103084901e07801900c0d03030010003000780b08d10104400d0380d0000c80c42880074811601211a241104551814480d040e401000e0741c2800c00c0301d40da40120301004c40305901040116a03210161030200740d06000b800d0550718941444d6190300365201c1d440d0004294842108000c0c12984103900b5a0040b00e101d40c24440ba0b52458000508691720802030a04203002c04150800750074000c0c03c000035520307180c0380040e58101c40405c0560b2a60b4980843c864280c009000c1c03844080300864220346040b030300003c0090306038986540303035204001e002c000420341d401a41015442e010307003901704401494400c0744400200030907a03c4a0052107019104022003c42c0d01c00c8a0503a034005000306105880c0000700404e0b07000032804440310503211800010400300d0699002440f034400c9001040ea10400810000070700da515403010b0030480f100804000521504001c140c5aa40000d40801d44000004c0d28402512440d04100400840e1607861414140d01080b10085500c601000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 410933866 1250 410932616 410932631
    0x60f0702040b01090b07110409021e01030605010e0a0909020301091e110a0f0506180303040801021b0316080a02010e070303121a010f0e0a120803040209011a071103160f0801 76
    0x111901402401a0101644100b04250100380c1f05503c00a84510003032000c1780e0320000354046482c01c55804400c03022080040c10180f00ea41e014091103001c3d0500380382c421807103041c040009a0b106080d10400307980ba5654030b20742041d520203400110740c2980042c03203801c00c0d681c0d090507084500850a002d8490301c2400d4251085032400c0074a5800701c80d4800c600c0c0c2d901e40d00304002c20500b0352001c02e00e542c903480365040507442902c0030700c06840203205000c001a12090030740b0030b121814042052610381904104650100078001103a03034011283c02029031031f219084180107034018014802034403240d20404e4000070130181d020780703040075104484009000f80540c400500c01401c07a080c807054080f801d5148003080072031260b001e06180f4200103210614550b640d00003a070f04040200c5003910a06c0d000800c01c419070a100b009039004201ca100140d0000d07828800d42c0d0240c1c06401c00003001c1205030b100300b6040b503808122031002c0c0e02e203080421461076074070395264038500070b1445080340e1542864131 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 410935116 1250 410933866 410933869
    0x3090b030f0f0a0b031c18081612021c03090308040b0406030b010314070531050f010912080f1c09050c01020f0717010e03030405010c230711030c060f0702040b 70
    0x500300c4c1849000c1e0050228840170f041c01d004508000d42c41c50200421401210000c0040e20002002840c1c480d0250182c0c2d084004461440d1a440c5c01607400a040d844405006845128080ea00142d80c180704a01c0f40300f20f460304a030105031580c0041c05132240450040b500c0c074111002081200c059842c104100c0d503c540041d810380c6c40c00307035464890039408000035903050702800c01000710050940c080c9850310150809a071707080c448400c001080191805060050342441c000507c0100b10034201501c4091070f001081a0804000700014004400400c400d20301800880a40301d20f250745da0a0200c15404441029006080e072210070b45880c4182c68224681e9400442e400c4403000c110405043c605040c0030203000703580360b0401641e40a6680340308600d40070200b48099401184100004030b41120542d400810445d00c010b05038248402c4d4080120810440d08211001c280d8044680034941c010b4a0000e0b04001c0e2214106401140004514940e40d80d1035004095603842200c080161480480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 410936366 1250 410935116 410935121
    0xa0602090103270b0601110106080c270c160b0403050307320f0c010504030207060f020105060f0d1a0a0f05100e0403230f1207031a01050703090b030f0f0a 68
    0xa940000c41a140f08607001140183c004690b0200f0103050440a0785050300701d03d170849600354030200b4181c0101000a10341c0c80c042031040c90f011042200d0b40c640745014040075401c0c010241680654581c0000c2d101101e000b412030b914800c07a04100036580514160401400c2680112241d00008850001c090305200b259000d0070610103980c1891200e51603129080920356000e4494541c05940510080d40514824000c40348114483c1d0b0103440002d20306074000e08a615000c6140081d0b9040004005058407488030308400703164212400da90b045210b0a1015003500311070200d01c203182d040802c11422180a4103c103109000c12032003001182d448487c4c2c8011007072180100000030010780c02007400300b40b10300102c00710004401c2151002114040c141070241c0d2200d4210800c80801084180003044500311440d40881a410103201103683d009034106c1075a260081103040c0100130032004e050621030b87c180805498004005980e83c140390500c840c0080040341c40005c0148942e0006080c1030290 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 410937616 1250 410936366 410936411
    0x70305070c0b2a041217091f032901020712020d030509120102030f1005010206161404080303010801150803130308071406040c0302010305010b070b01030611040302030a0602090103 79
    0x1980700e150344034584881c46540d0380003070320b5454003c100c06226642d0003100080000b84584107100b0107816071440d01c450904504103a12214100511040416442c1c801034136003405034502c807405100000b80070581c024480c560001c4084120b03071441d50204004002c00b8005108243c08549547c2d07a41e444290840740ca032100207410541c1c1a00510029000740c02030b00e000f500051440100302a03a101d03041c2203030801c84d41050b400318103001f0b2041d401074503001c4802034642032014150320301d0904401c44043c102c440c11a8100100700ca4003a0320080c10700166005020110241c1c0c0c0d40f035944420300d034060700360240312200082e50f0410020341d02c500002201d003845442e240d00b19078180303036071560101e6070080e56040c2d074039200c65040b0b100300713005c18040305204612801d0082c0440b800c40c0001002c55105030010465030108001d0000810080081c2d10b0460750702c00c4001c54500b00203010aa02030065500094140c404d240f10141000250380160401c01403ea03400c201c03c02c040c0d0031808a042d0030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 410938866 1250 410937616 410937623
    0x20a0809061006020c0f18072106120b0705090d030c0212060105030d03021c050f09010507030606120905010905030309060f1f1e0506030108010e15070206010608100b0a08070305070c 80
    0x90844048241801c06c101040c3c40c000070040d4440b02c2c0020f00c55003c030b582c00c0b600e00c0001201415440c5810f120520180c01002c4032071000c02c03545d8101140104d01c901425000742c8441426400504031510484c2119114000a00720004c2d4150324070780a0580083c19004901c00c035800111a0407001d0005000d40c1241c2c030040041c0702c0c1c181100e2040c5c3c001d500c8404a82403880d40c411550a0602c07090181c20f0003030000104c502a10314095081c58211403014001c401014286082000340e140e001c00c5060040c3c100c0035000801d10007928040b401007561240c004c0540c00088104050400e021883e103214021040c00034540783e4905036280d40d800181803104c44110703240c0a050209050302d000041c0410020f04016110320b40388c00006209410903801040c0c0ca83d1140b25804881e0030600407107020220484401290741400b00c0c0c00780d00c03180140aa0010810b13140c001994523407010700840d00518100c58490b82c1c904000702e000b45450700403900103000c07901b010003261703d80744100794003501c040d003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 410940116 1250 410938866 410938873
    0x203060c09100807030f060e041101020106030b2e080a15050603070909111e0102100b0618010c0b04050d0f0806010804080c010b1203090301060f120b0604020d020a080906100602 78
    0x403000c0b001c1c1c80c0000c002d0b04000402d6503610390b10500b200c0511626000d0541030360005410f1400785011801c0ca42060b0926045905008007000090040f02510b43c10076941030202c469020009180e98086940c100400c0719841c04101c000381d80c140104100401034040c039001400200d5254942060f0b410550320260168003d101c10418104291b010303490161007010310010a8040000044000c422002c0d8060307104011a400c801a6030100198085911181c0c0140700c555409400240980250b212014504a2a1140c4406a1707c0b4807541c02c0c0c0c070350b44007900c1345207410a42800c5a940780402d601e5408600c8010312061a41c2c01070341c0c92071042c40143e60f029615503590740d41000542005802039000c0d034130f504100b061651205001c076004426074000b0b60b11517104104140c2540c0450340026400c0c141a0001d000002e0b16809000070a50040b00c06800340d1a01c001190082c8076039110711840ea44007280b80c20507541d0100007a4020146030301141c0c0700380c031141101011000036116400141c0d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 410941366 1250 410940116 410940139
    0x70801050312092b050d020601090b0f040e030405060d0902031e0303070f0e2d0904050d050f0412120806030303060a0524070b0a050c040e010918020a120203060c09 72
    0x988241e5074202d00d44041e42068543d19402d510f030b40100c446290403170701d58014615540c89298100680780c014010007a0510090f48510046030014000210340c3d40690340300c1c50003400b82c0804004541c0100805011959610031221040000b8441503508074840d0258411f80b40c0101001c501e150601c60652014601d9070f01c5641064551210b06811841802204015008e440d40c907a50302c42e54201d00341e1041c102e0364010a0480c0c10030070006401c944940140001d0001090300051441640001030070b00e25a148214603860000c0e001704d501082d1028104800403040246403402010030085988482c4203645480d800c01d92640011103c158101001c0c51080040c0e181400ca81c040260061b1071820701070602e0000c003841c5501101040e10b09001038028014500035901c107040e44000d07840c407200c2c00c00c3d007807211042c0c034600f061007807003415a1100c850f00c0318241413003413203400550b00a0101540c0c5503100c60300c107944103141c0410791007070103903100141c00f507a9441c0c12104c1c5a040208540308d01d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 410942616 1250 410941366 410941369
    0x220501080c09010509030c03060c0909090a0c0e1008101d01051909060e010c200616031a040c0e01030b010504120b070c050a0c0e060409030206061003022107080105031209 75
    0x10717006600b03055858030a01c103280070a900c0611445000c1d10f0644881035a0f9407400091101010010349105c040b41c0c080501b90300403d20000785001500c0c559110001c003902c0e10911100c100e10030f500030303600b41d00800021494090306030380724001100415610a58405d046070f1018200c46003107551018091900854180415880c0c2c03080f007020303218403130001d61000310401d40d5085400e9454204082441a02c245c903650610300c480f101000d41440050020389000c41c068240000100b005000340350b161001d20401015800c0c05030003080019100b04104514280d0051240d1f00042c18280440c0c0b03802c1c00024103512035411201620b1103000301c2c0d10b0071441c0c0d80d511410200300a10a9040080c0c0c42c00110000c2d400b40b0200c07064500544200611070f0414080c2c0118a00c0603200d03510507032a1141c0940000e402181d13040c0d20090131107407010b40164a0070301703070082e00c92040c01d62900034490007643c07401c0d400e201d461800b40c40140c2d502c2115a890710281903442c440d034104002906001d00070440203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 410943866 1250 410942616 410942627
    0x318081006060807140a021207081e0715091103160306060b04080307020d051504051c05031306050411060f03011502030f1903060b0406030b01020d080618040611220501080c0901 78
    0x141b43d43c92040301e000441494080c50345401c91701040380c02100000d051030300d50642e003002d0f40c05800d0000e0050324009903540d61416540895080c510101e41741c80800051002e40c50200d48207402c00760960350505000c0986010011086c001201c0882c903044011803000100701c02e0341d081e02c0c0c0ca10021443c03c5600d0b020440d0329011108211068860a040f5403440c2036000c45503401a442400100329105c42a183c840f81d48038030700f40e010100002882007245e00b1040b000f44816480d00441c00165903102c2e07062004c0600361000c0e042e81c0104001079001070907038085004504a9130b004070207843c2004085000c0362070348680220340504c2e0b18140040e259400000c030050f405001d40707040000e03505655592401079a00300354840c0d00030079079990114156507014480305e001c0011903d01280c0c1d03450b0038000a03407614609041c04c101002080001820051241d0100c186130b00c280c40c156846008500014003140301c3c40d4800070402d05403a80000785035005130780180c0141c82b40e400c0541802600d8004594 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 410945116 1250 410943866 410943877
    0x9010f120314220e07031107061505041107140304121202100c0306030506181b2b14030f030a11070b0a02032a09010507031808100606080714 62
    0x40300402400007000140c2c01510200c45074201451207080c51310501401d02c0d24020104e6080c181014111280c0072013903002c0310840e81e4045d500055519402c404074540340499000340e908a898150910010124440680750f842d04ca20a20a0764620841c01c25880e40543c0c4220100020000140000281c01c1005c07000244c010348111045081c1c06490f020940d40691001008269216803c0c010700009000f407a0784000b017502c034440c1040e02d9240050380e8002d4a20300c00040041e1310f030b0ba808550395690b03184e80758218241540b449091740b40d81704102d2800611049603421a0007000300300c091404016a0240404880f006095a0b907428005001c0c00a00c40081038141040089000080031042c110b4010551041c0050b124a084010b050381414001030300c064410110044074101c010340000c54007040300030702c2c12580b207102d81c1ca07003541d469486d01800c6844801e240000f08090000041d0300c81d0b44100300e1400e000d0305942d020280e0f42c1d0710f000d4401500059000c800c80d01d808030340340020712 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 410946366 1250 410945116 410945147
    0x1409102306150412150221060109030606030c0f080d05040e1305030c060601030f06050d061a030a0b150a0302300714150a1209020301020d061409010f1203 68
    0x14094103030b040d88016180d100c0d420070b007120340f5001c407068180a26001440a0722100c0c0c00c0451400303801e41c2c9096520841c0001c0c0200e40030b03c2c0c4001031526403141661724000d56000754140005520b83c904408241c145000b08414000308110001c0c40650002c1d48001000158a400b807809041038204125a10001c2450403002e10030f203055400140c0c1040205007503c210000b410b041c1c00c00a0004064941c80440d081145003082c0040c08140d03903440e04448125805280042c030700030110640f0000c08120310076140e2601490313404009100308488c007203200c3e80c1c0d84100c42074840c00036000c002000d0203500000c3c0d08040d4007031a91450000b1300c51034110010920301c01c2c02182c010306400d140b40c0001d0f5080004560302507040d0414609000c51000c030030750a050001c0741040300f0854010420f542d03904030ba0318140d8460700482c084d0740b4294100c030b00344100d180c024001e142d1035442c0c007040d01c0c9400344000c0c010300c1d00078000100c1a451010200607a041c1106072810b24190351411551981e9810300c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 410947616 1250 410946366 410946379
    0x60409031b0c0b07060905010b0a080d031a1207060e0d0b240a06020a0b0a0603050c01080c0c0111030105120619020f04150801031403040609271409102306 68
    0x400d90303800c2c08004e440c05511409001c1801007a41c034255003914040100396028501c034610603c8207601c042a4540c00c1742091034002140419642400c81030300c0000c9501e5041100907403103509500703001c42c03400f0607102d0382e841e103d0200000344144085803101400246c421001000411254580d82e003482d5004021070710312041d5a05d0140c0012400a0154468401340c3d002404140c20002c07003003042c0d076004030040000c0145614546540ba01c030b002c020b00a41c10824048002009542030b80c042d102d81c0340d074600080201e0b225400985083c0c2d442802a07510896610000803185000015914440d540d61105c01d22148200701021010703400882030906a10021710001c036041902c0c80d03206111610a5442f9003807945141450285124000b0b00008282c00c03c01c018000c9a4104019404843c2224802c00405501c0300703014268031040d515015689050545080c002001d01d10014041d02a030341c03c2d110407010034490b407011980e80105040c2d4400d9844005980c42140706460b0760300c5080074121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 410948866 1250 410947616 410947619
    0x801060804380a0218030303040c03020103090c15080f010909030c02090c040503030c010b1203130303050d0609021b0c06121308160b0405190201051c06050d0f0506060409031b0c 78
    0x40924441044a0616503039902281400a8081e151445c1100d008203401861640c02c154032884001c0401e400040c4c103046c2c0301c2d6062001c001c00c1c501c1010041c0200c50320444a000399002c002c015920646210700d1443c0b0410011906500502c2011516540f42d00c0c1c5203c00d00700e950a00c44220300081ca64000044203100011b1280c80500003003d41400c4600001070803460003040003082541480042015442844440c081c0e841c1241040d0940360103040280c4c650307800710010400380c5510740000501c5800490841c524010040400c00b01d14942002d0310170000d0424240300c154060724041100003462003021810100280e181c0012080c051001c07585400c40c011402c0d049100030400885464519138100414400d0501c46070800a854040c0c109170800c250b00002e2180c003800c0ac0001140345070507a07030000c042499100e44002c200280c2440440f80403400e040c1e4038203000035000d0385d5500407240090001c1c8ad051040b02c0d00b0907450745400007426034001c0d13007a50076070404004642120b0200300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 410950116 1250 410948866 410948963
    0x606060a051b12040b0304050607090f030803060415060201200a09050f04111207090914060118080f0f0f0f0715050c03070606090b010801141905090c0a0801060804 72
    0x4002400c203100c04240c1d1b03820946000c078540035006101a04010a0300400c0c801803000380b06400031640c1203c00305031680c8605000030b000f0201001880e8805c00020300000741d254040d000b403a0800e03080d4505425010203020540c03401d00c200e03140c40340061040c00c41400180f03040002c0c2220000050030004000603a03046d0301d0825406000f2880342041d01004004603140e024007060080c1140500c10300100d8240e030980b41c210500640118103016034500b24100c00707140d4491000041c4038810488181510404161341c40300d041409a43c514081c60034000714260000a82d081e001800e0b000030541c00745403460f00d000c003480c140d48000030070800b0030091524100400180c1603d6000c0c00c00003901d1403909000600b00d5540850290500030120010041d01200020240c200e02060320412410b00c0d01035011070048229804c455400310b0741c3c60601a80444a1010301030003022078850b40c1650340c07945401e450719102140d000b08000341c0341132500640803d0205c240c0e03143c00d0003110750903030421819 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 410951366 1250 410950116 410950153
    0xc05040611120304110910031104020d140f07020d1e0f020f07060201020409062909061b0a0b060a0312212a0c0c030b0c1c0c020606060a051b 62
    0x4c03002d88aa5038200003a030303003920300300d540e1680005a00710740700005da2030355503a40001c4007040d04240c071555010032900e11070702e030982010f06040d100b084405821f103821085450007000c00d449080051040300320041595005d400c1c00c420248644483c0301d04a03091510449903c01d8030145103046005401169010410420401025100b00d4001507103603402d000c1e0f00000c0b26220703405880903a41601140500390a850703040510807010102c2da075540e600f0000451034511500d1b200d46011110704800d100c01c0080071421007000780c450200d1401944480040024200140c040981790522072803003c86058003850041015540403a481d80070381e4451711410080390090041e09461690842d400240310408107864666080749051a03505203802d03850782e14551005000003040a11944081400c081c1e901050700d204114540245019a810f071010f03034060401d00718010054850200484c400e450040262403415105540355400c1c20701c051504c041030080451440c449026100c20802d03c8000b19 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 410952616 1250 410951366 410951371
    0x15090813031a1b0909061c05030714161205070f080f2a010e0409021507060b01170604020706090c0602031b0c010203160507050d06090203100c050406111203 69
    0x281c2800c28203015144664180310382c002d141482240b2580204118a0041c5042d5080c0d1881910450105d5a4040c0420b0717151685002c00248a034403e05a4020044000000d0130024840d024001244031481c60070390b902d980e05401c03003500002020b0240b10b9400303071032101c44087e4014011140315070f0f82d425064195017495000174620b50403000d0360780d031210f1040007260700e80c040e450b000e82c4044c400c60100103200e45489a00b00d0402040e4820b021250f80c4071b42000d0348894000300380c03000c504003035148a501c65104c541d0464a0300d04006d1417003a40d6000b66180740b202e40309807017803140d207035a4401000025400b800b0110b400c940c2c3c070020f480c04582ca000f0384070080e0030260015503480005034080c282840034a1051003803680321100040459a010091710380da4155180114814640e134580300741810010f40000c0d030054a9001d42c803060080d9a045a11150b00a40594010070755024030a0142d070412451440854400c200c108441845001d89221141400056500e4a88101c84541e003a030f200307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 410953866 1250 410952616 410952623
    0x4020a080601020c011e21020d0203010305100501050a170a0c140a171519090302010212220221011e050702030c0604060203060a05041401031b031509081303 69
    0x4010400c90719580402100c01081d07401d08145c0241c0881d5080c080103200700c40030301410400001310412a114402110310600300c040c0105540351401d003030a0400a4109100030b503040d200b400030138503105545104140c1138a1014068451642c10503110404205032142602111302c1080b1241020031504008400a4030700c9007112071110044508200c800400d075040b110b0020f040205902000c10300003003000d28a0302c07902d0801041d5980d030000030b6079896002c450940300340c14108904201541940248080071210b482203115484000c00888004000f04102e000c0c0f801181006004d890034085142d881d5411440c1640e0100c0490b008070700f561080b07038804c2039010390460780601c0e030805405410b601c10f50a01c015401c2010100101b561030f8005440601039a0380080070901c42e440742c43e5104082c11000d0014403001c650352002c07103407a103000d11042d64900845540403850103d0a84180200c1e0341110050101e0142048041e004100c034810440d034401080121442c00c10640d00207a005500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 410955116 1250 410953866 410953877
    0x51512040f0b07030f0e030c0303041403130b0405040c0f0c140c100e0301060e0915040303090f0b1801020301050a03030e0a05180a0b0301090c15020a0212250b040b130504020a 77
    0x5174040040103035684140f906080b034106008036900614000140c0364019080310b100f20b441001808000c2c03c62084280984910010a80200d6010a4400100100c035010b680800440104c014100c0e40040d00224100000b6810302c844404075100c02d42e0580800b02c81f10944038604620750005856803011440d100c04940d1800000b00301c2c5c5028810540208500300c00200c062502c16a110f854802a100d5500100c0702c50002ca410700d4801d500c004040c0ea80320460150a104a0a102450341c03421a18081483c3e11080c0c04001c0c4001802a04c1c121503018144500c55410350b501035400c2c001d4004426002002280005900e603140c00d1480b40c03c40240848055506150045606640d9040c08450103a07040031060b00000703020ba50040101c0d851204034143e401403c507000c07802c01508900280d0311808108a150840601042c0750690006a0b00340700b180003004180c0184440451050a0003030b5810701080210240070402018030710200050784c40383ca0344510001d022a004030182000044 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 410956366 1250 410955116 410955131
    0x70209270d112b080c040801060e06031902010f21060b070209100b18060705121b0f030d1e020f0d11090a03021c020319020a051512040f0b0703 63
    0xd01844518000d0110110001100c2c02d80f0180d402c020118003108000000000604500c020000d4901070036100c0001d0180c030399200c0e50140903460685003a07104c0d000d0012511140311107120320314040c0c5e40c103031a100702c0030b03000c008281d0380d40d085c000160414030714011000401140390310400b4064400f6005c0f091303d40b0111300600804d080020000182d4091415060002e0000f0505031800c0f00440c2c144148044181c1006c1201d502480c0e80003001032003554600d2030040d007030101030010210304903210269041c90301d40c10759a071201c8c1b41080d0495081040000c09101850b0401c8010750944d000c00a00e542e040545039040345e2010561800554001c5128102d1080c03900400d902c01240310745031130500704101c0010f0820810b9210082c4a13050b0031755040100219001d0b06690f10760000c0650300c48206036450702d07800c07100008080344290401d4001003031900c0d05e190500c41c82200c0340b10013400c0c07041008415190039009032090325030801c1c540c4111b0002d40741c10482480b0310006e035808070302030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 410957616 1250 410956366 410956397
    0x10020c0d080307021c080c0906040b03040c0806070c0b0c0306030109050304170c1f1110020d0515010c080307140d020309030d110901020a1506090c1d06070209270d 72
    0x1005e001c1ca28000342c4440001081d00c42da02c000c109810640d802d03a820b580c1c10b00380300003800a01c101c2c2d0244030b14100200c10007041c00100d80100085514001c1900c0d5140c5c4d60160803154082560ba00030108510301022030300a905010140d030344942e025000040c44185901c42a00d90b4209911800c6290800501c04145e21014014008102000d4440d01c5c02a01e10488500200c0c420004074010001e04d64031140d0358140400099099a0b0382070005c560f039101c281c1e1901c0c0584400c480706850300c801003030145a01d52154014165882c1c100c031039141182c50b40401103032401d100b01d00c5203101500501060b0f04400340343c4029400b40b480d941c021580c41c480b190260042d607603030b91800b0038100c10a11003081543d03000302c1d61484403075101116900b11382c03541c2045001002550003d8402c0d80c03a00a0301806660800c0450740c0195407141071004800e000300400800d442a85c10007500092070f0004074400c94102e1502e03441030118509182e0302a902214401e2400c00b42c46a0f20700000d00d0382a011081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 410958866 1250 410957616 410957623
    0x110a02010c02070b0d150b040f05032406090703020c03030703090203010515102003040f050118030f060506180702160b070803060f1909020702040e030c070510020c0d08030702 77
    0x10140d0015000840c0b40081a0b520f0707005da200f02c1d0559a4039070030740443c0014a80500c1e001380401104041d11151520380031518070809019035070203841590412036800d1000342c089504001c0343d0015154a03940e18050280c0c05c1c201900d4441859028005010900d42c28030245200720010f40e13001640030303a503004041c2590800f5000403151003c826a4840a4039803202e1284030140a06109003858020480c51800401480400001e40804074000c0784103021144502d0485000340da5030f03841b000001109800803201da21004040c01100301e007250005505420250707000d0310080480c0420601841c00c2401c1c1502203a10500580000c01c40d200000c13032040c02000544650082941001d0003507076110042c0c40064841c0348141c4243e0248000f658900d103002c0044000034407040840f0b079540440c1c2001c0d4000103c120310560034503c144015400020644061125540003482c401d4a00403d0050041c6c1000e840c40850003910b60501407030b2200000e8038940c61048112658071b02e40000300904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 410960116 1250 410958866 410958881
    0x14011202072f0306160c0b01030b07030b0105180d0602040509040b0103050d030b03060f13080c0115050d03020c1011030a200a0f0b0705042301020d02011506110709110a0201 76
    0xa90a0400301000450385000615036800034541d2540c5c109100c241e035054409500c2680028000d01c1c12400210400c80c40c2c3c10b0542c0a070344991810300800c8070000c019111b50046601c01280216014141e41252500b40f80392084035000e481c0042c0307002c0d00c4102181c51a04211400d0f40e41486070303801041089410444484038104903e0104644084800065100c0001900f454075440d0280045049400380310001d00c4400e41c06008903550f83c40500e40a4060041e03c0090740a5400c1500005072504103a60515000c99140c1c2c060b19031100c241040000d000b10380b0440c4c0c810020b000142c074405407001c00061014408540b06d5010300c1c0b41c1c070f0880454208500350300c509103800112065001448009611000310360000f07440c0b4441d510100704417240e0295030b10032042410841052000b10500654450555900b070382611130860003614180d00b44ca0180341c01740d070404040d003401c01035a4840e584215101d5410410b0381e4004d69074401401c19a0fa0f4400c02c040c81c55000210821000d409109249 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 410961366 1250 410960116 410960183
    0x16030c0b06060301061407111008090d0503040b18120d02090f06091011150f0105011106040c14040e070303023403060f0b09040302030903010e030f041401120207 71
    0xf0b1444d030400c84024a01c11207406081c42e8403002140c4030041003640561041664000703852450103000e5110002d08080060b201100c00f40100351003089860700c6101283d21131608616001c40644441c00a1204444000f121440c1d5018090020b0f5007924400020848080b00c918003580340c4101c203041003007241c083d4155601c40c0ca0100080c40ca544c451150001c004842130905070f03030046500c500c1c0c50800e0300d00844464025801801c0103201e00302d103a05039040c2d031000c0c1e0703400b044c00c2c910300c0425944000694000e0310100a800d4104045401070343c107400d035030001410100e401040b600301d9624294441c1c0080700580c010444001c820365081c80070300111040e0180d103403002039a185140d402e00750240000b42280751102244d191007401500042c41c0000040c210058030718060400235225041030b0b001510950800706024a5068000141ca22401e807030440a40b4061600680a44101c044001c190620400a9007482008002d10107004402d000d81220300c210020810305000d044408111035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 410962616 1250 410961366 410961379
    0x1421030103200303041205160806240118080609061b0301060807090b1908092a0102010e0706030204090b1e040b0f040e0c040506100f080c16030c0b06 66
    0x41000c03550402d88180468820890040b148038000c01203400d510131600301580c040784404400041090011380d00c00c502040e030b400d0041c100d444903501a02c4000595140b5042c2070409002620200305160040b070b281c4050409500ba0250f0b1500c1440540c3d041d488407040c3e401010821200c1142030203010340c001c0c0061500c91041c080c10b0b11041c0c40e030206006010800101000280045004031401d4016044d0000c0c0103446034a90451102180c8040f48483c000404a0300460f00014000036050f1484001082d40c20042c1c1100c82c00400809401106504564a82004c0f010740c480c00e00c00003003e402c8650300547c0d10fa06200e42403041e00c00d00d00f00c0740e00414000914401c00c032000440c1744113600c0c0480d808120700341240c001918000030131076601d03442b501c5d00c000b003500340702d00040ca456480c000380d81c14091641c418040014004002a0201c00700d911840c2c0c0354071507889544050352041205420310b0a082111b001c08103500007442e42100410340d05080c003424454940409980710200300c0f2034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 410963866 1250 410962616 410962619
    0xa060801031208060a050a0305012c2e09050d022a0103090302102f030903030c07050328120b03100b0a1d040c0e040f0f02010c14210301 60
    0x10b0041e02c5005103190700c2042200c5010440d540c1d1403480c00c4004100040c03020701400d880c0d08049000b00b6030b8000104031030f08000280f4039030349440c000c04e103d98805103001c2d0070605030780d0b441c5103060030026a00c2580c424051103c4901c001091090301511030055000300003400b031840003e8902041c00c1c3c2a0001064036049582d5480c0d80e0401e45420100c0030301e0040707000409880c09070b00c0c0481b184456000107003032091117a2001310b00304454803922300038440504d11410300708140300544002d07294010190400c100058521111740d0042c0b00c1c45224404480c074001210b0300b01c10406401d110004070311001202c0761503035141d2220091042c044860020842c0d200c00600281d601d01d80078002580864494100d5111a0788100b0b280c001000c07812440d00302610b52962030305120608030340840f00901c0458010074411114a00c451049501076618034204d4425259a0303409550b809080703040282c90065400007030904600c0d12811200400140304002c003d1182c1c0141003003000d44008000400e000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 410965116 1250 410963866 410963873
    0x5010611012f07050d03020c1011030103060903090905090606010e03012c011d062e090f09050a1101020712020901033504050a0902040608150303090409030503060a06080103 76
    0x982181071214600d0400740e000740c0c0c060a0b0280c003500c10050b0160003184010198250160020001c11290388140c07400352410310003040845607000800c00443c3e00038401400004e03095030009103024003a041c81d0040707958507003145080c0c54040795507058940080c0207012407540c2124040340c03034410481c000d0000c0d110741044000d503088040500e084000d600c0740c0d07182403030600b9803019503503c0910309040c1c04154080c10813a0b0354401074820980c00c4180c680d00c0403001100304208140c22a07680f40c1114907501d424031810181601e2400480040c0d0354014020001d07004100401c5544e1203104102903400c800d200282c28200c1c0c0b6800001d0860320b51107510010394480681a041d80e610080445070111340d80c404051000451031020b0703a02e101e542d10000840d0350f140140088440482c2c0140020740c8403001107060b40150302c0341c54041040c480c00b0448141d03440340404819100902102c3c2800016400541aa48007482c1540803030000803e21807a42000007a40e00601f00a06102109501d1640c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 410966366 1250 410965116 410965151
    0xc1e0c010c050c01120209040c021b010305090d080c13090911060f0f0c0319020a0c0812030c07050c040507030213050a03031709150103150510031e0512040305010501061101 76
    0x2c410f40d0410a4070082412010740950540d425a14003410801c03400f000d241c0081d548c1c1c10001c01c800700b411241c00080e4029072180c081d1a00c0783c4401006480120a1510161500d00014004c400f0389030301031041400c07201076903581e08002d01100b5408240561030342000d12080340f0304888a405803000f0400c64231650307807540466603440c18500b4843d0fa1440100403031811802004044002d541585001044160340000e080740d00fa80502d0110000700d40d20400f0341d50782d2900881103400710000b400020324502000006d04031590050054440e038a042c00001000c598048510101003580403500f80d02c5000341000340c001510b800c1c0d4081e48140e05544000d042c03220700b131301c1c0241180507886c0040d5240d00e051141d80000c0070024a451201c0d40c42e880d00c84100c80380e5001d83c1211034034000014184083c0c92070007008036500b010f004a900e4100003080001d2180004080d1958440e0000c420354520b4444028002117009000002e007070350410300d000b4103901c2e4100005219030305100741c6179181340134070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 410967616 1250 410966366 410966383
    0x12303070605070c0e0405011b02030c06070f02010e060c0a03060f030213230c07030e1f05031e0112060501080703080f0a090302060d090c0803070b01031202030c1e0c010c05 76
    0x50034902d8588030781e07180003100c4041c15017001a0340e507801400d100400105412000d031680d00340c1e0300244d50203400d0030f08070f0342d134050351060041e070343d11402c04124901e0240b850f051007200b141c400450782c1c007900000b2503d44401a14101d18a8400080b105882a40345c820103000d096000207482025203140c00260026800b0f0a501512580d2100072032041000040000803000c80701c20100c0b00c6241c4400d9a05442d0406842900404c2540000809070715265041ca064075030144402296107101020458054100030601e28407400301c0603580d2141451103c415008062481000d0420001c80c0340c890300703640042c0d002c0701569101d028140001100070003034030480400e48261a440e5501040200d40100060340081d410103800100c0c0c180518403034000381e6019010340600300086903a0001c1503524450302c000a8100c038442d400600c0041c4210000724250041031040740d090001100041e400c0002c8045404000007940c07504240c21207041c001606a41c009003001010b41c00c0d162201c0742c0f0380c45003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 410968866 1250 410967616 410967629
    0x105040f140723012001020301030b01140924191701140109110d180605090705060706090c0e0910200a03050a090c2c0717040f12030501230307 63
    0x110803c1c00e0035070748200a011481a544031003400c0914854070380354004c0d0300a001c20b9820135200e4001089a85041c0780002c21003002428a0203540d035440d104050070202d00ba0303011a024500107103181d060380c1c2c0c0088250a0078506041c1c065861400f040b0001d803003601c40b00d0564a03410070030364814035a140651103044520060000c1407140c80145440d10f00e20400001280061810350103191b5850f0b44010041c01c5486840204041c1d1074400c0600e40d61021440b071594482e4082000000180c40c039040b440380e291080c407510b8205520382c1c4012044031001c40d19449181d03c07110106610310654012000c0884000303503665010b2641d4040410540302d40e146c64014580c86a01049030a80d1940c41202101c0d00300a00f803a003c2c1e102c01182c450b20403005070030300000c1040c0c9141c120b00d01c80300444d0b500800f1301c0c1d01d5450011116060080c841d14005109131042c0400010400c0400c1125003803100610b210742e0002500d41c105841040a041072926507001246001000f48060300d0019210054449 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 410970116 1250 410968866 410968919
    0x50402090606070807081204060e07051315030b04060b03071e05010f020c1201020a0210151a040305060403020705041a0112020f0c0106030803090d1107140103020c0105040f1407 78
    0x803e800c001e0322504c11044010b09550001070000c40c0b030b44220b80c07003038000e0384180c00c1445030340250404580c1d01c103824051315030301c2024001e000180071229808014181d50160181210b0341d40d039150440341d910103c03016203a4640b100c1003940d17189000e02001000d461100c6401007181203001d0071500e105450700840e414410b240c0e818001303807030080103454400c660080c00d08641c01d500c2a41036000c2c0d002402081d001d8400c80640949400d140d000b0556070b6880b41d6800b0401d14a4159030b082e032401450b07045070311078808001c080f021170818800180b0940c001e800800c01076281c0f205000031110441c6200d05100700000d500c00c02d50380c1c00100d0858000e10b01c2409030303d0300c038180d9081740c0502c289142002d09600c3d04100004000707220740a5481000340e641610168090712900fa00c585500709840e0483d60004907050046070b007425450665400e040c58014180140c0d80c1c1d0f52404c6480130343d000c0d03850309084c10700402042046010001d4205d40c51000d00010382c40d201c550105158001d004034400030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 410971223 1107 410970116 410970127
    0x50a03180b090f060a05090d08040e07030b0603060f0a080d08040b06040b240702040914011b09170f120d06061b23030408010b0f04050402090606 64
    0x1800c0908501d9040e4400f40030000554012009001800400c1c042004c054448100110340700d0b11906d06196103a04158000a00c03041c001e20322002c260400b54808410307180c2d0820360b60404c500303a8805031403416820004200040d00d40005c05144a4503012030354040d8040083c6000d0382c06104e003403549444e01d02c1030005444a1404c80c03500081803203c1040da030f60103c0107035481282c0703d014550070040980d0000e801e681c100f810503120a030048000c507607071250a00c108586a0441403805034505004840075103a5002403040300285c80d814520740d41d0680c0b09110701e020300f00c000d000b90390200b00100702245054114140d040c0d1721070321f4240d000c82c150340285a001841030301e41c0c1c03c904008000c1c4c2c0d40c84d54502c5503100c241040c4620052001c0c030481042000d000a0000c1d40000b14235041c002040c050030711061710b91144502cac1004c00f440b01586503102e141da04840709940c0361340c3d40d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 410791366 410971223 := by
  have h0 := BRFrame.cov_init 410791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 410791366 ≤ n) (h2 : n < 410971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
