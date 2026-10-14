-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2925
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:01.826578+00:00
-- url     : https://prove2.me/submissions/4a9c0019-afaa-40bc-b0d3-9159e1c694c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 525899280 ≤ n < 526079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 525900530 1250 525899280 525899291
    0x5070911130e090d0c02181f09020304060f02030709060507020d02060304060213080f2d07061205060402040315020d06050301020a050a1404050907080c0d0c0e0910080309040e030d 79
    0x8900380b115501d01840414098901c0c0180003002913604001111000f03400002880d0403510b02c00726611865802010450040c004241014480355108059084041403540c0401400140001ea100d8000540f80a82d002c5185040c000c0000d0415019481281d0800c40c000a0110071501c0e20355041e10010fa02070103003900c0b42040c1c54240302075001a50aa01009544d80e00001e0114001403400c0c03141080c0320142030b040f990701780d40389090100e43c1c015034000044c3d003a00204a07072003007161200402803562020011841c5a898100765400a041c0b207218034010301050021480c803241084403d80c5045005a86107800c09100340034242e00d030b104942c1544042410400039070020010704c107140180e510303410500400c0c18402414010350144503081400c103000240c04d140070b407520782d0300905041c514500f04850700103036006840000c8421000100c03421111070050038422034041d0807000071100c400c07072a424942829a01d004041880d8441c0d6282d444030010070106104441d892207290109104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 525901780 1250 525900530 525900539
    0x7020301020f0315100f0f11150402090c0c100b0301090506100f0b041404020a0c0f06020a0e10020d0503060a09060b040e07080705120408120a0f050a06030507091113 73
    0x2410f0700101c90181514030070508103130081c0303005084203448407603130740b1094510512440c044074149a281505401e12040101207a0a40810001544851a8089a81030500d41441030084040001d401c00c04000420712801160300e2012a040400310600100020f03010700140009001d40b820b0311014241d4040e050a01221030714150a410644030107030790850340b5540d24400484a403203030348901841c140c00c0c140401d406d40307880c0d0010084020b0f0341c580401c60102a48a010b014100f0034812a020340c0d000601d0a0030a070070050901c11070100300e07032207144900411800380d110702c4941c410008106001000486907a12000c5500241c0302010041001c5070301d03940150b5423507006006440300d4481c0d41000491145c451081107101c0c400a03990306080c03600c03111140c80c0302d000240048450301e90601000c40f0b101c07410a0001d115074111500403030a21200d41910040390005001300350301d0340c140320050002c110300041d224110703000c0500001c0d0194564904e0310290089109007840b000b10381c080040c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 525903030 1250 525901780 525901807
    0x309081c0605010903020d020904061d0105100f0b3a090501050907031e0609120203090907020f07030314040504150602010b06120109020711120d021e0705060706020702030102 77
    0x2911215812010401d080e111401510300c00003500c0025403044844880b00b0040c1003005401d50000c2c0300310b101245102c41c0140c42c4a2101103803a80c020181c1d9982c04000110b0302c2c2d482d860b001405c0040f1480e45580c24580610300398410b1199005e62580c9200103d810100c408414180d00c03236044420340300b1001d880074003401605e4075074030a031403075800c00b8042040e40d00c01068181c1181e0344080050f8000880300e02900c02c0011900040c0c4100703503644003030008070f400700110803240f100c6a03014642d40c151500411019000c041d100c00b04541c001084242c4e000000131300c0348192901170501003201c0000345240780140c4610741115400c2800d100c4144600003410715484141c0320b0f103400a00a551440081c80114002c400d075030700d400e184d60380040240700300e558010503034280a08608440c0504880c0422001c0c440300610582d5130b0711801e00e1900c07299050140a4880c20039403510009010058083c6940320900e0159621030b020000b07040042014a0303044942581c2c3c050025900d90460406a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 525904280 1250 525903030 525903067
    0xc020703020a0b0a0e10020f0102040b03090f011406060702030106051c0b1b04050d03020109020909070609060e0f010e0d0b0408120604090201081b0d02130302010323011203030908 79
    0xc81c052094682d0214510421005440100340c1694590034071000307020400070050fa130404110b00b58040c1400c204031020080c001000503000c03950000d6920304024400768508400b00b04035402c241d1500d07280802520503000d10903003050b002c41c0c80710303142d400c1c81c000030740100300591200d135110a146001140c2e0800e0344540903071644c000d440303c0030903503103101603000764800024254042e890300700400e00451a100300d4170500b5034007a100001c0c00803203c0d8089011000140c8450301164031007403007045017a0f071000c2024040c201c985401415201402c003c150648154030202d418050020006062910780e08003490b801074120481d800f5500300350400082d140c0c0700780c20100300c4545d40e00000780c13642800d0062030201c0c1d070306039140042c50f40c48403904c1c00000c3c18106005402c079410404620151114009050f0004240d01c00e111000d14600c000341c11500c9082002075151072b8158580e40d5024107809060444071f032000c0900e0300106a2500b10028550054010030920003c030300520510f0006144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 525905530 1250 525904280 525904283
    0x1112030d05040b1b070f060f020a0c050f07060c020f0621060306010e13032a0614010e0c030115020c040903021b040e1b0604090603051b0603071403190c020703 70
    0xd0700d098460030f0a82c0c003020b440004415885408100ca171000420500190b03c2440c0600c2c400500032000b0003040040e070344880486000540c0d41c0e0032982c1841014041c85110f0741400e4000c01d03019152200180024000442c045d1182c0c0ea0503c1e60882a201c40c1c0442c1d1110051480050b15119001d03070b85464084141c4000b8040c1c8180000407800d50400050f00740981e908004c109049400741e81c0031100440703040c070700441c040340c8002c0c00d00c0041080031040c0c46640c4a0207020aa25100254031500540140d2165107100760490034009801204c104072419209030009901e1016460381080c4d1402600f5844150040d140c034001c40d080c55400305403500403014006c142c0c103c1072140d0041100340c0e10618804201c5400c0000c9680382c0c062a801c1c421450100640406d04041d620441e5504840c800d50050311650440c0d00032001c51000f03000c0b06c400c801401c55203507096040140d00100821900b2400c484403100010100341141c1c50389404a4400c60b83c0741c01403051000d02d080003522034004c2c0c1b10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 525906780 1250 525905530 525905543
    0x240409060608010e0f0a0b06041502011515080a0204181b08090304090e121908070201060321050702090c04090c0804200109030b070f0e040e0a1112030d0504 69
    0x10401c603200320b42c0300d412220a2500d400c15521740e201ca820401d90007a101110242c4d1301c00840c541512080d01400c010801c81e4000861604480e1019013902c010b030b001e59040f51000c0c2024413600c1585500c008481ca207600c2c01142070740c0c13091030b01d000138426a041801c106040c0030798000d0905158012030005000c00d20000900c5156010a0714a008180c070360010301d400600052000d0055680101078801108007116503902c0e09110003000c50380320114000c581500c03002002c5629400614190700901c0910003000709614503207400c80803c04201000c20148004c0000b107040b644102c09542916030010b25400d00d0382000080d07050941c9c014403510b02000c1c10b110454061501517402a84a039400c5089402501289540c54540020f00746403181071242886012010800f008a028031580700761700d80c91105032800301c020700481c042528881c4500d04003008107a00b0413001c50107200702d03507000b55040e20003842c0000007100c2c0e048101107480c0c10301c8003280070304000342560041c0d0300660140740c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 525908030 1250 525906780 525906791
    0x20070b09011e0914030703140c150403031403250906020607110a0f1407030f02030601050a081009021c082508220302150903070608101202240409 64
    0x8241c079559000d0000300c0c808108801000c1040c0028103000441c1c91100070113803141b0649966803210001e1051030079810991101c0c050b0045400d00b43d100a180d81d05590907541403601d9598014000030051680852800001c000710f030000045034400a80d551114580d00c103100c402c000002c5c840320351813041d0401407003204049085c041c007894202d005809900c028092030380302611030905480007001300310b501d9200c008040004074400d00c141c0003d18800d4105100c02d004d2401003510b4440b040c0c000d940710741c3c41e0b5030040003030450010b140303a03043c00e0001000c0340c0106140001155806d4002c04100c03009600d90760a8200400b00005160040d405c022091800c00f007081d4400c040b03042928020107110301004440d800702504286440303094407511640030f40548070350105546804503503040069910105041c04075203401c0c0802030140c002464981d045103409a403001c0d21400f64400c07442001000001001991905290044a20b0b41c249080041c0395a481c00035035250700c10b20038001a00c0c5481d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 525909280 1250 525908030 525908057
    0x4140106121a030a17090d051e150a050601110102030c09040621200a090606320c010213060509030f0a0218150d03110708070803030720070b0901 64
    0x10304021891000360081041300e203603907070f408601e262601a82d050b00805100ca90340550798850250300c514420005840c0da0701002486400e000300922400410ba00140110384811034010440c2d540b040d003040c1c0100f0f0b240c4500c030059072014207040400b040c550000040180254440340100b6068506603410800155240b070424210302c440c480d40b6000d004140801c0c80030880d10055030000d481c22414580d1441e0300000011024402580a400c0003903d840702044400e4106000381740b02300c4410b02080c07103020156452005040c0643e03030a56103001c04a032041c80e2a60035410f844920b0086141c1e00e64403502c80202411503001008540c0c801e2140c11503e42140001040200200d64041c29850240c2c50701200610f01040007062050600500781e54031245566100a1a030b841d4002e807101040b11090f041002d06243c03441e0403482c140e504c550301c10041101c0c000300303d0341e10002c0c40c641b9268a040c1d1110080c03302031014070ba6000c0384202040491400443d0004000350380c4242c842a0050325007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 525910530 1250 525909280 525909311
    0x3020c0120070e19020a09050a12020307090f0906021201080d050f0d0506010c0503030f0a0b030c0a05100c0c060521010501081303020c04090602030411040b030307060b0414010612 79
    0x24650080065000842c003044070349200c0541d56001256040181c8400d144c0b403403048100e801000031400000c2c0000410806401c20524a03005441c20401400e500d0403103801084e9202c0062056412050740d40302c0095080000d0303485030103d554400c00640d80c5900c070343c0300881284004c0c010201e10f800381c620640e00c668040d400311241c8540801d1820706003402808800010103004080c0d906020400c024000010000e00045100303082c900224401030410120307000480f500140c6070303802035100c80300c0550241e881511441c02c94000704c030100c00d5004441002c407400c001d0f0040c0109014200400401c0c1c03190400090641c2c3c1608500c0000d901c02078805881031050b0030b21a07140420030040200b06401c11100048182601a0045450803001c40c40440e003118030103001030310020713070110a110030001d224046260320703041203405200742ca4030f120019480f403194002c0180038940d5150800155181c60300028880182c450b100e40141da03542c1d9000e48aa05000f0500409034503016401c0d111886 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 525911780 1250 525910530 525910577
    0x16050102131d0f1504050a2018040513020a061218020a03110301110c03040f09051e0405150c0c060703060f1a09190513090305090d06090f03020c01 65
    0x5140c26001d4a445280f09007a00b02c4029052030034848001c001801a61a54028280651491840080c071810394400030902a144120040c0011070700b0000340c0b0f48104030b100021140e034800c0724006010344548000c4d80f4800495480250000982c1354009400c0780c0140d042900d4255404091001a6064085050f204e062607402548403540c80e400b4004a0460400380d180c44502400001e69288a03032590060b54010042c2c61b11560700000707044c0031303442144100d4001000c0352001801a82890750404070403200d41d48080300000c19001c009018004100044000c0f42121480015941405031811130345600402500d0118402d45011901840c800d2082104443c0324182c1410002c2c1040c100c410261092503904001d1399050016501035a101100500c2600c241c6007040310741071410050204000c401141850b8413454805400086508901210115141262850140695450a10020418100d000d8030b440c25510070401050303000a011680a07809032038031100e070300b95400e4030803d200c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 525913030 1250 525911780 525911819
    0x3010f1419050610030b01111b15131e03081911060f0a020c070503011503121404050f01030f1806060819060207020102190503030403142104081605010213 68
    0x1102c40344d07110304c0c80c0d120354404d9825400500d0220781842030400303040e00c2c040c42c042113854481050441c1c201c581c43d04040105120b001e1040313941c100607185005000c0d402e041e03c42d481c2c4090310103a5041c0707180514460030340a1030380135a03002d49a00041d2050f01000520440d1140460f601500001024400184661060214024446e0310399103e82d10000030790040e8040030301510038000082181c0d40c00380200c1c119482c4210b00c64424518608000a40070710410005003886110f29101c941d590642007124240e5200303488040340e02002078012002010700111600c449407410a50388100e2050244440707509002d14024003510340ca8201054640c0c1502e00701d05034005c20044610006412074002c6c040305401401901c0804090341e1078001c43c005582c40454494000204010405802c00804480d00c03030091141820048200301000e202e002054900c8000e10226000504104445045a1780388034010701802c0d1001051401c54081e40000a0130480950740c100c02140307445410340350540d5507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 525914280 1250 525913030 525913039
    0x3100b030a02012a050a120f0c12140f0a0306050109290408151f0e0a0e39150f1c1103011409060a1403010f14190506 52
    0x148003682c010359014500d00d0400d01101c0b91003510111040e4034003113907040c1901460103001c40c07441d10710341900c03442c1d044540c02061005800454034600d60144400c501203900c44035200203c14124000c0d03600e10310340308a456401100040004595040c00043e2401c211143c07024003402c0d132210011b48810070b040c00744500301e20292110180d490200059400200703580d4011928182d00c0d110300505140002890703184681240080c4440d520043d030440e4002ca8005504071003147c00d26001c0b020b140c1c0c01820003540355840383c0c8154541c0318148001c1c0743e03040e500f03e0000241c44c030307418661a040c0c100900c00d43d510031400a050607181000300c0300b01c00d44d010300c884240c40c141c41480b800c60785070007a00d40d40c0300122440c0c0000202d42e1041c03007949400e8552903140c07a280e600d052000c0100c020070a002038000c4041005002c101d80304d07520350100b0340360b0a407840041c007003045010a0040c5820102d0407141418101d855600080c890555802800c9444d09001541a60b03c00c5000741c803015122a07400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 525915530 1250 525914280 525914293
    0xd061d0a081c06180c1b032003090a030c06030c09050603070c0525031e050a0206030622141303020c01050304080d1a040b04090b04020d0804080304080c03100b03 71
    0x2450080e00c01d00502c0004600003440c940b9020040c280c59000740b813580799266150807140030560845580340c81e010040490b034014102c256001841f042200c0c1c0e0080500e0405031004d85a0321052003590003030040940741c500a07a03907034101640029514420030002c00e14202038001194070801c00a0240c55014286a1550b111017008503200e0501001c03c1c0c4041c0200115403190618001c9580003031150034030842c292070b0039410f0010504050b80c283c84485121001d241d00020b0002c646c002015804864268a07070b582c900114a2b10f0250146849900315403001600040750640d000d2190071907265500001e0707580d1800300c00184031070528003030f0150b8090760070a03403190b10400003136900c540f190000e02d04002c80090346009a071001104440c0f8008408560300180c2810b214588810700b00f00e4042c0064561b81d1216860b00d80060301c040d00400c0140d07114024009030340300f246c00a10346041140c0e80c0f1380d51060110b4072502d001074494441d0146d005410710305101406503400c03400c001000f0300385 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 525916780 1250 525915530 525915547
    0x405100c120507051b01110f0304031a15190b07140d14070f0305121e07021b040e0102040815010609050d211206090b0102070f0f0e07030b0d061d0a08 66
    0xfa041c407117510141c1084030400e4010030050061084141c10401c0c0d00045071200c1c01d600d400c04055494107007803d407003003644d8200900000680001d0260740010784080d8403200703591080300c041000c0c90704048140000003800b0810001031aa0411901d000042035a4200e41d4122044610301c81071940c107610740d1000c0c412540441ca018407a11042803007400c04515100e4800d04140a1900881e801c502c8240800c0712a400301e402c0041d0250b00c01507600c040d004400c03c2242126402d428600054016652a01c0b038007000402581143e0241613500c040354020240146241500c2d0001d000b1310700050741c051000510b60510340280001c60358028581004410344840b00c0085500180c1c03401c08004800004c2d80002419100d42c001a000d0001c1c040f0b2401c0030b000002e03142c0015580071054031a8481c108103c01d5400b0b12020043d0761039201040e1507504e6401c000c0b40030300b0051710419070101114400e0340802803039070301006040d10340341101c500e0008402c031b4283c1c0701c00c65250068140e0104102100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 525918030 1250 525916780 525916813
    0xa060e13090320010b030115170d02030301141302072f0102100f14041b0b07050309040e070905010b070b06010c0b0412050c0703060501050406080f0a06020f0405100c12050705 77
    0x3d14880c0035400004000c00301030000b03420344024031480320450083e602c052204641c006c4c058021040e00030001c281312401b020b002540d0384014801c4291009000f4421100c41e40d0300210185c0c45505100c00b9034444841d030a01c0c882803413034881a000c280705090040e07281100d02c00110f000246058010300030701c401003000d003006094500e90303c00401e9900c0c0c4207609207004440410340918018800300421800994003411481d02a0b00301042c078140500075a40052000000c031803600c1400e4502082180c0788140740b51411120350014550103051000115404c1005c1c0045c008aa000b4101c001003603c03140019500704401020152841e20b4400008000c40c48580c0030203c0c0001c146409880c25500030b00310344c1844107903002298441c4e1075200422031890309004d05405059203c000d00000500140303229600c00d001c3d10002c00040d00414800c6984520380103843c000c00c00600001210790341e8010081840c90b4103282101c12003c0c10100c090400d114a0990310019444002042c07200114401b02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 525919280 1250 525918030 525918077
    0x40f03030f0905010c02100501091e020f0903030a05071b030803150a1e03050c01090b0d2a02010b0a2301050d0f0212100509101707050a060e130903 65
    0x8554840d100c02c4400c000032401d00c01e0101ca20466405024600e84c0c00740d2034019034406911410a031410404807107049070190446c8140222601d000503620ad000c00760081480c020b40c1c518650600001c03403420f07000d6400100500741180310350a001c2121052000440390000340b80409044d0143c00d10000b00c441190000c0c440c05504002d012007284c1342e6844a520302d43c0f482281c0e0070300081001c601081041300c10170041c20300c4502404c01400d03103410320000c11454040e80003925811501e45000c0415080354407071352030140d01104990281948084c102034007038144081c44600070014090006458000382d20349000c05003c08075031020904032000111059000b8403692164243c0d0383c0c00000341c009443c4014540007108440c101b0384c03890705281c0c104c5a003401da84601d0142001c0c1080204104850217541c1c199101c8810300c401c801d811200300c520f81002a0000d5401c6501002c0c0410901e400103620211341000701d85400c41003840324170400c00d560480034011702252904016880c90900e02d04007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 525920530 1250 525919280 525919301
    0x306081605060c0c0622120201171005101e0e0609040207020402040509041a0114030d03090f0209010311040f02090d080304031407030e0114130e100807090c0f08040f0303 75
    0x444a58020340d000145c250383c80000034001c045140440d09400002c0328000c0d03801008030a600c1d02c031361851900060564000d81d031a00e980240381c080000c000b8050f480190303028100160540c120458282e002800101c074241c01c441c200d4141c0d1641c0340c40140304100380f407080800a400316003440000014080a900200c1c4126400b40c0c0a12000c0781d141c4416400e03902c143d01488650f100c0001419480b120803038103030001d04100d10f482030300a1840d100000c005403031502c00c1c039000410801da800e04029000c84080c0007584824004000410b0000c1080c00c04d40c80307442244c0400c071003624109818100d06c2002c2a40790881c03254085800031481304c034061580b150090412202c2c0080c8080c2610965200400c1140031074141c10341c2c810203503071042540f60798203600104170b0319107a08401441fa100400344101e66520358044009110502c03044c0d13480c1c00a140300d800311070005480303051100290450603009800554907058890040d803007104000c0c041d41e0000c00d045e0380210580c508401514007040c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 525921780 1250 525920530 525920533
    0x4020a030b030604060b0f091b0d0603080c0d0815010c1b0b0406020303150d052a0d060b030f030406080c280c02090c0301080d0804111503070306081605060c 69
    0x207044820784003440302500c02c5210700400070302200f450041000c58810100c405000303503c07210401000c03501d085245002403400000c41c1d0307110114595130314068002c40d003004082d45004184465110740005414800f410291940c0c0c541e6514107514203450159155260b00040d2010b5000012074040e0300071034a206240140f0403061030701c451300ba000c00e40c03080d803096006074000000c00480307410251144c0d92080c0101c40002109401c0c0c0c940f666070700b52220202000411410b01c108030f4046003a000046070f14060300c003021140700c07170130b240d801810112903050090250b101940c041c010040211010380340300d511074000307030340f02c1000d000c1c415000495900b150002c2c000d1480590000443c20080c00301007555408200302083c0305020705a0405084401070040a00041c001c002003c14a0078115942e80b82c544089d541e40c2c1003030880303402c10b43c1d00650001020400b1b8016024400001e62256155850a009450341c0301d00e800c0d40c4114840c41c91030310654418050006280110007000d81440150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 525923030 1250 525921780 525921791
    0x3050304050f03031015020304050a140f0a08070504051e04140703020406030b060316290d09080301150206090a030e0d140601210f081606020304060207230a0204020a03 74
    0x80400e185900545d40c0981300400814200280f110401074844424428405141854542408608004103034096105420104128a020341d04c50003031a042c4088010955503600e5038030003186031542094012103010704e00306000918007200361f2540d40e841000311004601e05640d80d440d0380d20000750940b010b128074058690f0000141c2d8440c026180a10302801e102311107801d208041502d4440b6013560290036441d03030300701040041121411041d03540b0489610811004940d400e07004248200851900014942443d490520000380050b50507543c0301c244154100c0c3c40b0100a0344d503005c0859680d4104d51182d505a000030b4072800c10403a1915010b4090480b002030f9a4403a021240300380a000f80c29030000004004550860854000f40c2c41700824180c52a0219298001d0003020841e0140a198001411809981c45c0460401c0074035000b0100315281c6c203040c03400c0c4010750300903903080d50101011100d42c015405441d4028640b802c00390010084010250b092201a4202c00304050500d41d850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 525924280 1250 525923030 525923053
    0x90c09010504032405010e070c060b0a050312130f0b030a0b060d0c020105040b060a03082a06070c020a0f0b0a080a1514090c13141c06150902160305030405 68
    0x4541c105401c2901d071385025200840d60490b1401c0f44e005a01c01021035851005004140c2d81022038128019000403000c03a4491840d80420145d80003540700980511034005081e81e020218400381104500f400d40425215548920040a800550141c04200e09040010900e041900c0e80700000824015158904040588108500320b4444d40f0118016035125005c200810840c0ba40f542d80c408400c0b01c1203d086030543c2c4820400d409801038855040042c0b4818400341c0641849240341c3d200c48001b15000b510b0201001000502084001c901442c5205404140009250f0007142981e0711100c04038240981c07000304884241d00500040c482581e9181d4540038545041102c1c0050248550460312443e106800e100344107100070031210500d1b80510408640d01190306d465030846000b01004140071544000182d101c008144000008480000c04034041012542002c84024080e882c1c0c100b0702c59071aa06032b0168401d481c1c220350448a00b00c0e4490000e8020809160000d001c1c50448800c0b0a01c0b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 525925530 1250 525924280 525924293
    0x60f0a090b0c0a03121107020d0c030c182d180203030a170a02040e04030507050f01060905190b0114070c1508060a08010903050a111011091806090c0901050403 70
    0x600e8005005400a0f0034810a044c1c010086030261005483d0402200740502d06072480c5028034400203110348098070b808030601842044410265030010301c0c4108a542c0c0760104410015502003d09441c2d08200d8041c01c0300305801d4801080d0000f500d150721070107000d100c020004048154000002546405040015031020030140ca034081b1103807280d25007940c058801704070002009201d00540742c0100014820540381c0541540c12a0345400e281c0e8441d001d514100e0304043d80043c0402070b0f90319011000600d1001a04030b11300441c1994940b088400c0c0b1a0300c11400e580d81010741c5404244000f41c101c3e48096000000d15101c0c0c018100d400c032103034584c481d82281407240543e440003e1a00303018060140780100609004040b80e4000308160905980c0c042c105024640c111028400240700101014406008c00d80000b58550010040f0a024003e90f680e0f0740c0040b62243e000d0303104203130110002c4040c1090390b8040c40d80100301c0c1e0b03595a10040c410250380e001c241403e040000c00e100000010b0b08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 525926780 1250 525925530 525925537
    0x80f0906190327050c01050a120f0c090b03070905060918090c0406052707121d06090d0206040809010c050d05180109031505060a1805090f0c060f0a090b 67
    0x601e60b4010420031003501d0105405403079400c954045090300d40311540010700024000500500a091035512821110419580c0101007240d0b0026a03003411450f1102c2c8410340c2c0304094166454803580c07001900d5400c40da0882c041110f5403000701d000a1401d004514201000c0c0056400c000c190a086800c5031011010f0040251100340c400d0f440250206a1858240200c001904042d17403001c011b8894812103504200e039013220341d40c00240203c0890503180c07003441e011003c0503490303078248420112012101900e00c80324525070000d014820204d02804000704007000555065030081161307803584d48800c8556804007011605103c12445d0250002f40140960758071400743e62641900c0e18503006107565065005105141080410b890900004602c001c005080e00c65076000050070780e54071000b0441c607101a4201c5030302001081b0110100200d0341d0050351145098206585c5006460501c16546003801a16158050070a10041000d940400090900c9100e54544a0040c50740e4421f0382c0c2e911350 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 525928030 1250 525926780 525926827
    0xc032010151502011407030f140c1206030105060d1b0e0108030424050307030504050a1502090a08010608150403050904090609021009061b0303110307030603140604080f0906 76
    0xd0041c01c001c1d1460945440714802d0050009120b42002000c4482100b48004e100f1030915555004003400412658410f030200744122009034507505007508841601c0d002000e8640b03000e10280700003641424180034a901030704010f049548816055501c603002e00d40443c2003220b40c0d41c0740d017800043c074000c0034401034000c2a070b10026668407800d040b03801171181c2280d165410200030b65450840c0103035018084a502540600e00010943c071940340090400a0158000c0c200700034602c0410202506a801440c12103400ca0320f040099a0390403005007039a096100300113290b04000c0c0742803800c4141141c0c55038868480e25100703241c04041e100080480b800942c0a5440580c0c480018045040001c10b4049440780c83c05c1c442c03082c502d004030040c2200070340d6504d1290003803800758050403d8081d41011002841c08203005407240342244000f00200300a2205480b0b501600c2102880c00c180416450b00454000e07240318036009429020700042e5012076012604103008001e48070030f4104c2035550f4221813 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 525929280 1250 525928030 525928061
    0xa20040f05011e02060105040c020118060203010609170a02010c02010507050a030e15030907090e15040605062403060d140d1709030a0504140a031a0108010c0c032010 73
    0x181041c00060084208103050301c98040c601201210f1a6000503130141102d404980200348a45000000c82c00b40c01c10b40511100c280d8680380d0a003c01641e9009036060b11600d0755a150300541c0c0d00c0d407400c070b102c609002800300398002c10761503009544201c06580f5064010b06010b842c051203682d9142c540041c480069001806042800c0711a140c492503094034044840d001c82e086013400704c00e4a49450551190503070142d550078000e02c0c000c2d0180500c2500703044400e00c64000340340504020026020880304248644d4800541c550b100600020200c0d0075801510114115501d4109220301c0420741d0740145c1c1c1ca192004c880e484042010007464146003041d0b0340d601c82c0c4041040300c04078000009840f400c45500117005000203294002d06840c1203514003005a580d581d490740c0402c2e0811100d41002c3c0c800b18202030311001c1d01000e022001e040f0745003180200040f40b00b840c0100c40c01d044858000b0300143d5100848001c007100e890b0740c2d1030010392220070313100782c40e0b14099000c0840d010b602110040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 525930530 1250 525929280 525929309
    0x30b010501030f02072301061a09040c0503091e010213081e0c10120b0d0c03030206090303130209181f0b06030f180703060f020301081908030a2004 65
    0xd55070325004240c0c40250144095092040650758006071280303a140440c1e100030107013058000c4080940050b8000d025104c200c0001e01c400c501d01840316409118010f0141d814000c8540c100ca2181c01140c0c400e181141c00303080600d031841000003c0c1500c0015a041c0d941d024040000407182d0b106d100c50041c00450003e240c1c46010042001016100c1040301c0110782240001612680b6803d50800340d40c0c01c1403401c100c0c0607001001c2039006258800b02c02d0f030860f112044c00030410010500450650740242c080b1880307990386481140c1c0c0c030700c4100c0740790f01e00305540c12030140141444030020b44c201c3d01569076031140401884900c2d02e081080308801d2002461000700c405200700038419140320360002d5070110f165107803030441020310401c003500300c0b048103a4040000050100138004e50002d15030140302405980150416100650070a00031025a40034020758580055104c03080e052b0256844040541990b032030301206030060094610180c10503842400c02c02404035000005e1000e4541c4043d104034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 525931780 1250 525930530 525930539
    0x9101809060f0b0603071101020c070303022103090c0d020d0b0a061d060906010c020d0c120b09031812070314010207060c14090f2e030b0103110d09021504030b01 71
    0xba1402c1c4203822003600e141800c0d034a07440e12401d003200e501c1411410401090364005500c54024428110241c6490050003408020594041210001c45030145003032551440e04078160281d910041e039000c0c0950313200f50390790126424030403071586034140010311a40b48000c1130784a03510291800c8031043c100d039503110f40038058500c60400c1821010140c4007000002e04c0c151005c90042c510180c000e078144038803c01c00604556481d2b803800c0c00035602079101110740b955210301c0d03d20b02003d128101c40e0911b080000400c0c00798000140c07003c40001ca01681501c8103091305005260781e0400c0300000c1800341ca24044042080f032400580c40013900d000060361101e0034200241180c042499407001c0210070043c0791064061542907811f500c1088584140b20141c2c030000400360028450103d0b02e606451240403102c1d13030120741c0b03045140140d0703d0900409044d08011411142900000d0175008000c2c00468482081548402842ea00c00750101d1090181c204040030241c000303600480382850a14010700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 525933030 1250 525931780 525931793
    0x312030c0f0215010b0c1906090c05040b10032007030c140607050d0c020304260d0e03030a031d0f07060314010b0403030503040201020a080315010801170c09101809 72
    0x14040e000600c05003c0078218048002d1103094103100f003844a01000c00c2c0c00303034014424032a16199440c5421380b81240c4120307142440103004211300540394400c401c3c04c0011035081070300800b407401c50024090103028051081c246e00900c10346114420210300c60f0000c008600f9010003d15546010340c980360008001c0c2d1600484000c0714880e440382c95000a8248008950440181d400b03008010402285440307010300c1c12459400341d43c0c41400c10303102450b101c580d084542c006c202061000382003501c1c101018114261690004560a1034142c1d00422440e00e01911035409102c0300803a20307074500c60321490304070a80d162440f2401070342001e4011540c200400c0d07401d8070480700b03000e03900751f1044000d40c504051515903001310301c03000e0700344400080000d045a01c24442d81c000d466228910903240e06181845d034004000701001a0b01241041c400802d4081c90f215084400d0380d8031200a0652400103018007201a20245c02e410b50039085902c086020100000d4048480e04102d0000032a4850760070040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 525934280 1250 525933030 525933047
    0xe011701060f0f03031b08031005030606010c020102030d0c02070807091410060207090515090903090f19090c0c080307050315101416050f0a061104120210090312030c 73
    0x1400104140310b0400c1507400690f022011290035052400075031551030440d01c49600c032004003c140c80300001c00c00c1510702e042c001e95000e80d007099003141c5e210743d120401076411808484000e030242e031050004000c151055003200b6000207461065440c85a5104041c520300f894a07004003003450385910080f11440c1c90280c003a40d11020400c42c0d408200c1c94a00081d407900003d000b2110100d803104001444801e030a4980102400050a00c4d1014903281e40090345130b8010079180d6115020a0840c0545482e080300c03220645000f08102042d080d01d0b0030001d8009080c000c07640b03400d00040403841c401103648680914461269500c4940d034a190841414009502050343c05201c1c04404001c20501c030ba1003504c0000c03000500f0522580e501c10460444110380c14010010494070604090551001c00030400f00c0b010352280c10144030b21800d07801c0107413480c029030007442c400040d202ca250015282100d00341c990314041e070822003804e84d101d480c2c80c02808441d0f13288401203511031064825096004005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 525935530 1250 525934280 525934289
    0x3060f120703020d30090b0d1416110307081b010b030d0206060a0e0405151503030d020403060c08061f03090618030207050102061e100b0a0819050c03040b09070e01170106 75
    0x1042c0324055104000e03043d46c0c8140900c00e450800426003036101c8605d580018425220991001c0f89882d14021103040c3c81d100035855000241100f280f028104800400c1d030340308942c40071340e10781494461f0703c0140c640020822401d5007592201c00303185864500b4400c807001e640640d0302412461400100f07101c0c440300d0a070310070740710320f04072100b00404510301150701c0360307880386100c08600240c0b206450690141c070402040f9506001c0040d044411a50319401007040703d01c03450091216500410007034030354682c11151140c0182d150301d000b800da400ca1640380c80465059080014005605413100c0e0100c41168046100d920791514100e03003819010003040c0c2c0108801d200402451501c800300c003c00c0446540e111803940e00c0a40854001c0c00800400d2014000355800d20b900c0c2e0090200c018a4400292005001c030710032480c030303000244003a0182c540309400c03401d901c2e4615103956a4400b10204d00524211003801074000104018441b0101d19000700300f02c0e10003820301c0200d0303a882802c50710150300c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 525936780 1250 525935530 525935603
    0x1090501290a0c05060109060e0a020a02120c10050c070201030f0b01020705012012040611070b18120105010902091302090f190806190c0503060f120703020d 69
    0x4a000200900154601c07400d00880605900e4000d20241616103051401c0e00501d14003410300007003000c0c90540e205104403110300d01c45600b940c07a2004024102d2044404a100503003115132211a1161504020105003810b941101d4804600c0c100c031390121441074075145048403001648105641c0d16016081a000e9803440402c080340381e40340080e41d1540c49210b00c60500441d80800d8156901c2e0a03030561008203542c05682c81c1145a0300b0103c140c0cad10601032500842e48805a03c669140005056026105d590308054501265040320380b01c9001c21007451330b030021840941c1c582c03500d402c0c01a10300808000780096100e01258080107810720074052a404081d2051048405990300c094050702c00b048242d804d00c80c0100f42d45461b00003600a40c0201001c2d2103004144956131001114102c1400c1d4007034410400d5803088a0110758602c81035401e80e510000b81a8214150300c0c00ca05207101c0c140360f080440d40740f240e4a5010840c1504200c1e01a60032180110825102d4071142c81010115140b100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 525938030 1250 525936780 525936809
    0xb04140613050c0c030d020d140106020303041707020d200418060506030c06030403090503060f16030b0a170a140c0a0e190e160e07091e0b0703050301090501 69
    0x3000c1038620880808071440385469078003081c101d880390003c855a03030312000282c0c0c0e510154107401d04043c6d8081e548c0c215809180945040060b0301c03640c1100d050b14000e9002d10318503115038403240303aa98110b803820360000b4810814007005070354000c1e05203001c030700c150000f82c52041d82105d24040d000801460f82c1c025400d000d201c000c900d011800340480203500c000000380c582c0f03400010034a408240c104040c0c02c030710000280400c0c0350704014642c0850f5000c80c11140560f44942c0301c500d620310151280d0b801d00b01c1003101c01038030900903001140da040d00501414005540c82079292100f94007842c03922119008007a0306d01c280081000880b07450600341d4010860748443c54042030340c82505106100909000c0e03004540700105002d44a40c034480b100100f0b114036110303520b826440f215088521221041070f1000003030080300c07074000ca07031103800d6503102e128000c1c0c079000d0031500a5000c3c019820365100d0102000c20109200301c0900680d60190b900c03251203604000e1040101c54041e00080c03110484407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 525939280 1250 525938030 525938041
    0x10608010c05070327030f11010507030e0d0f0b1501020f0a0c0605070f0203010c080f06041b0507050a170702100903050604021203090901080105090c0406080d080c0c0307060b0414 79
    0x5048550f02c550500d00080a03404c9050381e05e004c0410b950f0151440c03480d03003500005002d4045000c0b05c140c0d008840e1000d03042e46200041d41e86103d00341c40100815100e400300002c500c1c081c80c0d40200c080c010100c00507290003076030b50b80504000031611840310300540030318401305507410448500180014401488140c980e92030306241c00300c0a2140c8410090001805400c01034016004408542e0182c0240f10403000d1490241520008580b442550b40d078040005070700703103014010360820a0f0039149200200c1040b8108880b160700201055402e4854000c0c001c001443c2600c2a0750140c0b4081840c40d19201c81d4810403410907050001c0030100318482e5018000310388045000d60304a54115070718110705018040c1c080c154003e500c003699100744108000182c900e0f064000c1441510036a058034036500c500700c20031040b50250300503098a80c5c041c041010b007850040074070581203c0340c02c00060520f00040410791039a0302a440031104542c50f80810055802e10703001c3e0414070072201a00044901c0d18 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 525940530 1250 525939280 525939287
    0x60e010e011401090b0d050118021e03180a06090209071409040b0f0904050d090f0f051009030b0117280f0303020d020a030b15040b180319050f010608010c 68
    0x18028480392000700400c0c0c1c103043e0f00641c004001000d42c40e0400381c4503410459918010306092090b031034100d145541c8204544454070894484640700d5850030001d42821030b80360f045810042c40c84a01e001599515115010100000040e2500c41d6401090601d414814821079600250051061200814140c0401e404040540349220301c1514006142008040002d0f01c5070741d40b03d08590020030344c2092005200c000705440110f0481c03038441d030940307542e22500141e00280500c00c81c030210041d00e106004a1800341c20031510310155140c0220690340b01c0e29030a19107403007a800802102c40c0400303030006a940520210911700064400c40103049100000982421503542e4010915072140810804040c001e0781501c01040064101319262014050041d0081c00b040d05001c0c400c3d80300d07001480c02c102c41642210180c41d01c24941c6414482044104002c14030150b00312641750081050540080303030080204400e260041c0010305998100184050840701c0c0754000d00c2031039040c0540d000300b2a40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 525941780 1250 525940530 525940559
    0x906060f0c0b0601020a020607030315060e1c0c0305120703080a180f06111c0b06030c040b1b0a150e0604030e24041706070504120b040f1a0a060e01 65
    0x70842e4208005564020041781489006500294800d001140c004103256255002102c03018480104141031a00d98206a07031240441501a0340000300500440a01c48030007031580b049071080c4580800140c40b50788003030819200304110f042100c0d0205900c006c0c540d100400d01d8002d0661101040b80a000001c00401203d680c0805000d401f02d4074041806c1008503400260b40d40b400300c0b40c09459001c51300e800c8135004007140440001d1030402c41b1740c2c0043c2ca4000110b07401401d01a00c5285403034030f81648180e041d002801d50324002109600b400c1e8a215090190305100303031246a542d01e040c44800c0001003100c40d01c03080c03840203a203d00c0801c00000e07008022001d00420031280401911a980400350b0500d240300c000c0b00590101080000d0b044149505843d00301c030000b0103032082d03940e400004031360b1402a07100702100e81c103100c00c00c01f02146c5601a650307001800f4a00801c9040d200d0303292070300442108880c031803400e00140208000410075101d200080c002c030781c3ca41101945031847e00346000701f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 525943030 1250 525941780 525941783
    0x60c020c09011403190f050f1c1106060d02180f07030608060601080c130911191d060f091c050105070e0607060b0f18070e06030c16020126010906060f0c 67
    0xe9406000000e2040046000340010b078090700b01c0b05446250041c40303462740080158241c1840c20814010841c90081090003408a0140d00802d07259582c2c80402ca00c9064414051760401000103507010000c82520070a4804c141f00460000c46003001640142180c149602000740c41e045041400344e9681e00c4603415810011785a081030701d452010f0040091403190307901c007140d400e1400c865510355207142c4000d0010480f101c110070140c0e5801314400c0d150580e0100403900c0d00c11029502c0c2c41c10340741620107031400070713000c7d61101e0034103411801180c1c070a1100c1c003100b06d44103c0160b418041200074040d880e030104642c03628902525002011451038013034248014111611403260301402e85910040e0058480001d1400a922461400c030040c41072040c1c403000c000442030704e101c2440e07080c0601124010394400700381c0c42c40c2c50400c809a010b40f854041d412810402c010103400c441e004030728608160f140c400144c00031154507001146044600e6036000701c00f8400541c03801100a9001044501140e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 525944280 1250 525943030 525943063
    0x7051213050606100e0d030327021f0c0804080a02041506091a070524060102070b040302040203090705060307020106081c0e060c030c03030408070b0609010b0a110a060c020c09011403 80
    0x40505000540c5c0000a1001c10b982110700800d601d01070540c960408003154000c02c0c0205120329004c0c00c882240c400c83d1030080d4009490058501c28210400000c408070325181c41c110f5031a91301c55460310f0382980300b50300242240d03014115002c1545020310803100080c909450000401c2d2401001401800c0746e8450104529a480f007200b003900d548908841050758008181d80d89040080074105144254100d428803004003500064001c1d400068080c5c02e5803a03000030b42c4c0c2050320356400c0002945c030082c00304075240203c04002440d40c03200009140203c100740c0000c12400c0c240a100751411a02c510003520b500160468100c9440d0803164440c1d01c0c8400365050303a52628901e42d607500d9446403565004551200000b080103001500c0d000e0030340144102c17100d044039207501c010070224803806e02444d28454820068078054a001c0ca01c150074a14141c800e0b10714138400ca80340c850403a41d20410340c10168005121001072032800360410782c054829070303400c5e0000192010202e6542e404c841c69684d401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 525945530 1250 525944280 525944299
    0x1a120601150309080a0503010f09020408031204060e060403080603010c0314130813140405090606030d030f090203030415021c05070b07210f050105060a020a02190503030307051213050606 82
    0x2980e02c40c2c0c000f90b448075005a0b00c0f035904c240c010801401c0364401d100b83c4902c000c900502090072501c9000316401c946914004504048115502a0f0424030184c000c80d9416902c00c0e00a0700010140f00c6284242c1c002d0b2940030f106d180c8030040c90b00f51072042e0400030400d8584000754014200c40e0300c0580d040b142c50f0410340c00d0b032902d82c5040905841072102c0841d245058041c0040c40901e180720540900d5421742d020700ca580c035020403147d6034400513034145070305802808003580c03024800c1c2d118010080300d5010100d00f031192a00401c0c2140d00c95001041003080140c5d03802802d9404100c0b60040c120701820185412240800052440c00389140003001c001d1140040750041f44a802c3c040b80c0b201c1000040542a2040891440107001404144200d58100000013030300d89042030540d0702184003500540320511595081100181e1240300070b01c543c6071032560100340d58500b0800f9520850f038a0329050740d151400082420f0314440102000203140d1032005072800100c001c80c5058004409450400c03c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 525946780 1250 525945530 525945569
    0x8010e0612120705160e100504060608061e0618180408030708070e060a02030c06060114070803060607120801061b152a0c1106120c0f0903060a1a120601 67
    0x400500c1d08100c440030308184000710300b0113174241c0b1a502a0301480d041040c108d54880900c401d8420501c01c2e500030560210000765941040000d910105000b050701030980c1d21103800250309504092910b038030041c007001100955007000141400ea03007401c42c081c003409160942d203240c003d10000381603900b001107183c0820f410601908907000342460080c9901d8446403481c07002582c94001c002100c806103d84000b18409500034583c0041951801004500e80903030b545480142d0f42c400340609030050130070045840861445005100b2032079151791008031552414000038011409502c9022131110207034401c4000410a00107403003402070b600300114200710a80110360000312400b2440c01403480c043c81c084501070b0320180a91020b4420184d143e50300c05103e06010880c09082c20111503140302001080301c48441c10f0240c11183c40144407a80351000071000f0904200080c2c0e421700a6030745034020040311240c4640307003441004043ea140c8118894013a6100c1d9541c2c1c061140754101901340c0c4a022 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 525948030 1250 525946780 525946783
    0x120204080a0219050411030718050a05040c050c01050717010b0a08070309030315261b0415090e0114070c050a061808070c06080105060412020103050a140708010e0612120705 76
    0x24014400148104205240b00c2640601640203c1d060030012702d15023035091122400d15402801d80c0c001800d20782000703041506001c002e03c00000e83c0401c0c000e041c00000403101090207018800c80b0960769190ba0303491244130400b08044180c00050010300140945410180e2110384039034000480c3c640482c83c0d40450500b64000c24082c820380b117150360007400c003080250740c520a01a01c01c5481d13804d52254003001d80225140c26003144030a8100c18010521005460940c100d500203c03180b0f481c20790304076981d800c40421140c4049408095944a0b0151401c0c0800d10412075802022030a0002c83c255896803003a4840d0703001440144501e645104802d1174810704079101c44540e03484841035603901c8032030070440d4a0320318034400c401c00036000c0c00000c103a906116040c1c8085410742c07000d008807060b02d640107402070300d8001c20300700205684502c1120040440b21819000d11455207030143e403541040b424030482c0ca00104031038090180700c00303409058076002520300301e00200d5041040d00d4000500e000c0303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 525949280 1250 525948030 525948079
    0x2010915020a2603040b0f0901090803011203050c10060f0b090f040f0b031f150320131a090109021903090204140906090705100e040c11010c0f120204080a02 69
    0x21051400c3c00b00c100700070404003c0b21326009401201841d000c5a4400310708a090750301d04980100510001e0004200120956251310041071082c18890b09010145000c030b45021050008100919200c450800c600300040e11418080c3c10200409840c0115150204074200369000d0058041c3390b466400400004059004640c000700090564074045549041522410007030107003e0501485d202a103000a44c480540c0000c0b03a61200410031002843c1604402c18001040c1464110248a400c000c40036854400c5003e030078009a80000140d0104c0d007400b000001c141c010800c8103204006902d01d50b08894802c001c0621360b86400310f0500a00d00c0403c02400c410658000f421020400340328008001203802ca00c2850000122540315a480c01001010384281c035005022440348412040c0a00f003c0e0400c0d030001c0c0c2075003800c6001d803502a090b1400c4501202845000801d00c500044015a0004800c40c00200e084c1e401c0d410141000400c07030301c0350002d0714000c0c803c044061a201c03400c03440c02d101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 525950530 1250 525949280 525949343
    0x70b031f0308031e09011a0123070804030510060324020f04090b0108090615091302090c1806212d150420130e1302010915020a 56
    0xb110384030b05040701c10407101507070007054801c3e24034098001240b802d4144103d031018507607040040310181c8000d0043d04d065516091440c4100f2000e545822805044001098200c0c41207605aa0b1286582401400d104000250404090400d4010000701c0d506101c032410f80112044460780d582d8860305801d00a124403158520782c50b2021034000b403820348907402200b026070207881d0340c5220760b0359031842c82d00c46008503400041c10329040c00c1d000321b41c1031002c0c142c0e03404080c020390495070090f15000120b00c00d6088400c2c201c401000a51f80d86640240400402c89032010f0b10320704e092200380310b50f44a4a00d8600843c0010b403c42d240080c04040300b460024034000000d01c240c0c0c08103080c08904002c030789401c0b100504400741050074072105040c140300e00e9044000c800380c07001c1c0c1016110709609850b0300c69150b48800400b06000421110410002140104070b0900c40130b5640c4800c0c400035106d00b8082e0300202000f5040c021400e00c080d0040b0303440941c682d00c00515445548a00b8aa50501c001c040c82c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 525951780 1250 525950530 525950543
    0xc071a2e0e15030a08090f06160f150e010e0c010e010801030b06041506020c01263c041a0108030d0c05070c0305010c030e01050c070f0f0210020618070b031f03 70
    0x8031340500404070010310b00c200c800c5e100c201c040c0c1c514030240300320341c820f607010f80404060054484010410090210705107510440c4850b80341c0480300e0a62080c1c591103402e030245655109803001e00d00100b00700c1040701080a00b040403840d4240c00001c1c2c065241440041c06407804000003032442d40e00c9034031501c0c070300c00706502407440d4540301c14009595018020106011515244481b0094581e005450100314408a02841d045c1e0300d00c81c222411109110354601e180e06d031090007004401458550351415012219000e61525083c10311310102c40034240e0106000d80341d200140b2140401001b140c105011915004c06d4a40d10007004844034070500310013800c10310106801104108040d004902d41c805250740500a001e1550031682c2220303001d0340d81d036480c11001c001d0413000a03191181100f0f00da0207040e24020703d104c1c3c4d8010900c0b0703e100d2090080160000400c0203c00c034040d0b803a00d648014a00024100c49091401e02e0b6060721000d020100021310500125407514062000031020319032005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 525953030 1250 525951780 525951793
    0x3020303070302100b01090315020717160b06040504081603090b0301090e061509060d1e0c05031009050a020904081c1b08060603040602030c071a2e0e1503 68
    0x14025180c03412142030901300707420030ba690320071588110000000d5035000030011ba14032441034450380080d0701501c0c08403800c90494500d0101101650043e1070b10302c4822800b50001006131a008030700c180000c10191049250030140b2012640e8407040e1003e1042d0602110024100d0b0b04054481c1d111561008107101d80000021500c41026082001d42c8646902160070540300c4040201c0d412840300000358100500c640050710b907203000b9100c080300078010b5040600b03009240368441c0c0006843c07201900e03008101c070006c1205050402030540003040030a010080c00201e981c1c1c00e40c540b100204064031640446022400380302189089a540111841800141070382050001028014841074030b03180f44600c1c1d030b18140070b034050000e452040c54000c090320300e181d48507605c607070080d000600f00050108051110030b0000381400119140340c0e941c4c81e041c85003443d2140c1c5440503c12541e00740c44610980d040c440051902412400094540300700000a69076501000c50350b0010a901115601d8850701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 525954280 1250 525953030 525953033
    0x60e1b070807030e040b010c050a06020a030f090506040203061305100f020d0f0e0d0c1e0305070f2406120f0201031b05030604053306040312080603010e280c0302030307 74
    0x41c4c40f00d5000b8060b18140304c0c543d0f1203c010346445c00e4804018000b40c11814088000444940c010080d000321420005101d1005000000446004000481f1158007610900055113010015158015403044580c0852901d5960781a03c0c2c0300c212485d12522611040c11940841003a0140c9064002914082004801140c12a40500500d01800c0b1032030044d4400c01d04418841c60b41359a80c6908911840f045a40b9140030129403aa03d02040c1c081181c2840343c4000110280b81001d0b00a019210300003024414080c020030b8000a03254400110745021410484c014154002c502040d42184000c0222421400144c0140601c2442001841500160300f000103030400c0240d03009180c140c42c2081113a40d104103250624207100c02c01e4055585a00003001c401c540810181000d4501520386400e0a80d25554840d0629240b880100807424100c00c0107124202403003400c03c800d503035200034550041c05508240c0c0008038104440c052039050107021081c0407805c0ba40c1c500031980901243d40d01c1166 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 525955530 1250 525954280 525954287
    0x4021b01050f0c0306030304050f0f060406110c040c09091e06090204030605060607020307050d0807150504110d0c0603020d09020a14010909110f1c06030c1701060e1b07080703 77
    0x8403403040c0342103002c0c004140d80e0b14183c02524030807607002c1c000310724041c200750030021400140f100b40d582c0034840f8503440220f5200c20009d80018100da4481600035490b40c566107007884084200107000c0c03440c010811500c940c0c0541340008850402000007240f82d1184041a00d00003020280c8141a007080000105504164002c0c02201d0007650b08019a4403003008200c8544905070000c0c1d03147c0d002610600852414400f183c1354140f02d001140d28003002590f5425981e1144c420800c4410740e940100000e00c98407aaa0308010182140c4020f206240303951407500040060041200300340d804a0f030102008050b078040c40c1100d80050036a91001d030b0744e200740b0203030940c20044103001480451001a4002c1103015103d440c0950480507170404214444803003c94001482400d600c8504200ca5072480d2542e01c26003000d5170091003500792044c100b030300034030381440307c10b007401c10310383c581a0200901050640303102c0c0c2081c1283c0c1d05184c034401c95100e00d2001d0242000c090410340c0001620020940c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 525956780 1250 525955530 525955541
    0x915030b031c09092003250f080115082e030602030601030b100206010b0f0409050915011d06040b01022107062016030207170f060f01050a030803040204021b01 70
    0x49940d5a10f00154407541c1d02820342e040c008643d5600700b16000426402500080075651080303560036649030440c900206400841a003000c50004030b0300c4007a80d0344050b0740c00340015000d410101002510000a800002c0c40d0b03600040c000040d24000042c1c00c000f03075084000b0688400101c08251402a0b141d00382107009610903201c4902203443d02c000d800141c100182c820f411041a500545916031a0140301c20403580160f07440e1540c00c00070003000c103030301980d84100c500480c0c1400050040200031001030080040680050300307103400070030801e0f05003984103001e194445410365010800010400044c0d140c0f40d2104240e034158403022048094800000380984a094003452090160418400d442007582205c0360401d0781c0e660301044409504074407280c4000b4150702c01e1040780c0c0c81c01e65544110001408507802d8141c00d80040c048a07885000030000d943c2c00418800850b02c00354505000182c4031402c5100c024280080400040c06564580c2d05071f55580c5084001002c4420540c14003900804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 525958030 1250 525956780 525956833
    0x614030105061807051e0703020d02010c0207080d1809050906041209060504050904020d02030105130203060a050108190303020d020f0c06070921050703060c02010c0206010b030402010915030b03 85
    0x1864200042c1c00381c5460b49111441e1034001c014103c0544a84504036015401076400c6030f400c00c828441c00110b242603030300400744540aa0f01804003440440f10090940b07215107410002c6621070321060010000c04141f1605120f0642084200c84088140440008030b8a9106000c114500b5040200b80240403400d5440f0701e07c20030b10500301e2064074100361103c3e10345011740000588140010300460078050710040e08180000c2c481220000507900081c00d4bd45c00321075898010780101505c000b1030a08020032600651540340500040d07050280c0a50b4034007044041d002d105002100d05c0c810301d4000e034106c509010007100b00390354031021440010000d500c1ba05a2000c6482036400007445a0b200d116a54281e41c1c000150501094000c40c0411240d0003409003610640142903000002600b1807081442e0030600760004602403072a00c0e000303820410164400e02c0d03911003c000b00001071b81e01c104828207030b0742844620501001410740440040c40e810358101c4e0584504641c0120f92118420b00400a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 525959280 1250 525958030 525958033
    0x3020d0908040f0f090219030c030b030723121002071a040f02090c1801031d06191409100203040314030711010e0d1d0103091e050625080606090301061403 68
    0x3517035689140c4040344650741c40c60b1011640d068000000901c20307002809102e005141c0030601c0003421001030f017400d82c07903800100e101045452445100090486000c1d00b800b0454070345030540d200e03250300340d10b51b0032800441070074030340c0001c10350108803c0c500d0244800071140c524084a24291074250b000f10104170b410b0788a41c00d0000040e030721036a42c0d0102c2da802d080d41742010032a40c0c1100b0054000c0c00211b814000744406d25143e80743c2c00c040401a0764811078210603c10000341c0012502d5044410703e207120480c50008004000c0c03840704c006090401001545001641c1e55102e007401c035950800c0d40d000c00c2400e4000010301207151380c0b005842c403a920441000300601203001044550796031043c4020008510600f50720718900e0002010b5008648040c100030414485985c2e070120052404580116480d00c00039022003404400c000c0980d025503801c421111241c1d0107050943c07000c618086a01c10003144130009009a11000103481541d0b8003c1c0003800110348814614030822040d06c4014001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 525960530 1250 525959280 525959309
    0xb07050d020c0402031312201c02120a0503130c03080910020c01020a0f0606170d0f020d0e0d3206100b04170106050607030512150306010603020d0908040f 68
    0x191030300f8800c9070700500074994191b01403412070765008400070740c0310000d0341804508000c1d0f40244010b040c9904032403507001c015011b0546042100e800100340c08920000f1175000c5403021060030031010480720210b0b0941016511380e5280e0b50091100c10002c54010070b0548000c1c800000c001c500c2003c0d04810344111840016801c80090072070782c030341580040c24010307840303400180d002c100b04684820a16005400100310140c0b1303031105a81040b9022582d081030382c0510b075800d003825449044203000582510252100b0050920006c0070320150040c03040c4151000d00b50702d410400b5013023070301c000d44451039294000040e160913800c58080c0e1903285003081c0d000340c7c07001030450141001350405651000003400d0520b0708041203000700c5420170f4030800c1507640ea03403001f0803031342d031a20701503e680d501c01d90700c945d591025071030381c1c00080c04c003e000e0394000311b007000c252005170703030041015410743d0507a01e80140c542e200404e004001c0d00b03c8001c0641101000a000b085411401c29010300303960a4090201c1c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 525961780 1250 525960530 525960553
    0xf030a0506120303070e06040f06090317030907030201030f20090a0501030912081e13031101090f080f09060403110f10020c040c1e0905040f0b060708130b07050d02 72
    0xda00902d81c00b00e1401e50000c20004505078014204d10400031006000f49003410385402002508000c02c0c0c0001020030007204c403c0007048500d40d440407000c096000b100303065041208810f82e80300c4803408028103040c0ca503607544000d5107059204029100780c1c00341c43c50009034001107242ea1fa600c56490710b4016908010046a154000d005070b80c0f42c00d920000712100640c141c801200c4450380a40b8007240c030480c4014051200741250b803254040c2040b003079080d02d0042da600c0e019102c0c09140c5403a0445034104800c54000c03501d001c2d4031409054000002c1036664544044810381c5206030008903a00c10b60104000c000d01440000c201480c1c003041d2060300c0310301c0d108810410f074000010020300041c5c4c40300017140c071039083c19004452604202c0c14040201010300821203445c4160b5010740340020141300c4100424a0503006621641803c0301003000840351950100303406103c0c100028201400008004220021416401d00142508060036071165100c0c40c1c020f13224481e802c00c5200610600d24403a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 525963030 1250 525961780 525961789
    0x602190804020411070b0604090c0521061e07080901110a0207080f06130609020105090d15050601231b0111070b010501090f05010807020a05010203090c030616051213020301020f030a0506 82
    0x100155000040d581d46c0c3d581c1c0c5070400024011380f620450760001d00e0500000c0076246c0440c1094441c003000d088a541c0c83c007510071986801c03002410b04001e0002421280c0041340e900303446a40000003458001515a03411444c60b0150440b500340c1e00c0c1c0301c60700107914544d807a030201e0250181c4041000b952511410705e5041036480109843c048800369441c10b0300800110190300c000c0172244103051240c244415600044c05000301403009403422244500319090000c03c51141c075a000340c0c242044100e9160b400e8010302400d4140241244403580003441c541502a801c2d68a04500c884000078046240e01640300385907a0003070001110701c0c040f44000130600390f004110b08000e40e641501d42060180c948401101c10403000b42c00f41c0c055010781003400010400c00c6c0010343c4921113034001405d00190364800d142c40e0150090400d40c200349140a1307241d030942e104080301c42000e00a4032445040d21030801c19503101c2a200c100030360540c80000e52105e5015440f01a61003826145002c100c41d42d106d00600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 525964280 1250 525963030 525963037
    0xf01020c09070f09083412030e030f0609031c060506042909030309060a03020d0e0303100603020f030a0b12100b010905120718020904020d14090304030515040602190804020411 77
    0x9085082d103070310040d481c1c020207416000b44086c444a41a0b410799100580050100020070540005412031050202030808004012071004040014485494020384c001c0c0c81c0d0250a030500c0f0b002c0c020403141048648150000c0000e45401421295110390319810806007281000740d0940d0110042d01c00b0203071128500555604142c0a0007640c6481540410010213034411100c01003855804d02404040d4051031140000f508130340705c020b640e603083c003900c001030100c5907174070005c201070040080000911040c000d51707802603007100c00400d4019980d000105540445805034005109400592004424940010404803420b0300c03100c07800c50b00d80c1c060000d92001030a0140311075112204c2080242c2c03151600403141c243c0034000500301845400000c0c141c1c0e001d61a040c0303503d502d0340446c0002581000c03500350080243d8008501c0d00f0301d50b40d540c2e5150b0400300300c1580345ea90141e000030140802501103c00740088422400c030700200011000c1e0450342c1c181c030103038042c3d487c20b511840401a000103d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 525965530 1250 525964280 525964303
    0x307060e091008010903090f090c0509060c0a0f0807034a120c2701060f12060608070e030d0909090f33050c090f01020c09070f0908 58
    0x10811010120014801c003039202801c4000410700304000011078032420301c1a907041e03500c02d41c3d030301003598078101448100c3c4240381c110820161030b00c0801400680c1042c11104410000da45072510b6440c6646405e0502c007501c1c031f019040d55250640b800410410700d00404002d0f2081c0c0720101c07442032004805001c1d501101e149070000303100186218100c0480500300d1408001c0400a0103407039040d81c0810601c4a03800403003005a40145411441c515041918640c80b0304004005010000810464041650184145024883c0380400780724054450107141f032900c00000000d1020300e9032114010103d40702100c0500000d154a40310401c503203800b2520024460195884156450070480503500074103904400b1a10b200200030010b0001324214000000840c00b05070500b03c08043c1940102c0345540c022408011900e46403c20801c9604081a942c220000390354070083e07540c0040c010303494981403141c4543d0020074002007080c07841d0300c03462040b51080d450740c2e840403540e601c803441b55403580440c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 525966780 1250 525965530 525965537
    0x114010b070f05010b13060806011422090803040804030b07020607081609050d031e0203094501060f021605010e01020313090203070906080610081503100209040b030706 74
    0x6040800c414840b0162603d00642c00025040e0300100095100340f210118a29aa500c8034803c101144061105500414100b507082031007250840c00210340f07021202c0202291720380030710800154415a40141031003a444000240c0e68141810300071120b400c03c0c03000b01c481d0b00d03e000000f001e01e40301040041c081c40700b94a8685068075550403140e401607004198000f00001400f000496544905007451528042c2d12000da512014154403031024100901c14003e550003000307003c50a480c1c5a03a40c0250038005003480c9070090540c0d40040008a003580d44003e0011001c4106c1d941c15944147c080c120b9031142c072031821034a0104000c0c0d031a8074400c0342481e04109421010044ca500a170250800982c052043e24509160700c024910342150541101520b01d41c0030042000050300114081c2c0604014100701b4402d00e42600001d1200ca1250602800c201000000c940070300f08002018030346607001029a40c000b501c0c0d00c15940250000b00d03000b48200d00b0000c0b00c48280c100855a00c003a503006a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 525968030 1250 525966780 525966787
    0x3050405040522110103090501020706020d051f1806080a030e010f090311090a1b0201051b03010b03070c0c090603030e090f09030d0915060b07030f020c031f090c0f080114010b 77
    0x1c4031091803851300e0708424181903c070090080010020300c004d0062501c07510005071605c2c9084449002c4800041a014042c41c0950720384c40c82904000c6520211280f6140000c1c0b03002f40b1407280d00181c1071a90181e90300d03100d000c10130000c1540001d010301044000303a030f816000d1000a0011076105059201c05042c10b40c0411003116141400088140c3c0190b080f10082540c00c2c000d0746890696105516507030050350340f94103000c0c201c6443c0350004105000000b4107819541040420b403a02e01c4060842020302864854440400c407000410313800519000310304016003592418003a01c40d816914140d4850a43c400004107a0951034400306d0092000b500258141341404005c00000c00c4a0380094942180300c000c004c4520400d40642c1d4043e00f5202503032500c480c00b9180c068401040703040840d0554000100e8541c150702c000490300c1401034071101400b064032420320000003c05802c0307405801c07292141c2012801d807404030403c0e011200404020400442e42c45400050004203001d8005410000c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 525969280 1250 525968030 525968033
    0x1203080a11070804031e21140a0201022503080708071809090b060306010623041e170a020303030a110c0105090d0f0216030209070504080102040303050405040522 71
    0x19810590310a46824001a5240da40003401c0055006a0030840b00400d002405000b00040403a82c0108034903c0c294401d05001a40d8440016443c4420a03003202c043e032094070007990748a04480d044503030320252503a550380c401680090203540703c1000380075201040c0300c628400f803560285840c41e607501583d6000c0203490300c10341200e140c1000b80c0311008120060111394034552440c001100100190000043c4000c0c40c0d00d065050020010704191094000d480104030f4203400070140c46003045007861510304c5070b0707075540c80e0b074210b001c3e50304142a2101d071050001542603402100c0c1b42070f2001040110b403014410301c00300e560b4001380d10000350103070000e00c00700d9103105998004c0c404078200c03861458104070740c5014031800c6803000c581c0b10340f0903449403032900d8200380c00101c0d000804210f8400b07032141d003050f20640103402d040b80c4030003402904050001261584510250b4001d000268001d654440d540d01300142941c029001d29031090f443d04010849920300300a140c681c002d040d00d5000b6071000c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 525970530 1250 525969280 525969287
    0xf0a030f050d060e010905240108071214041a010b0a081504020d060905060301020a081503010605180a060e06030d1808071e0506160803040203070b19030c091203 71
    0x62040060040034400c080e040425030280d10050010600d401040750f150440300426501c0150401c8c02d410212803003a4402c0e8150000c1d0314100074282401212034494481c1102c04000f05148081da46252881c0c0c13101400903002c1c024041c6008002000042d2020040c040e11410300b80300b0908403500800118840c00d005840c841d612460400407081ca6101c544041800c5e60721800000500c9503985100380220417251280c16000304059000b14200101c00c80e015045040c0a01001000e10400002005e20b94007500120040e08020340f10b503401281c01c490142c4424829030700012420300b030110100700049002c401901c01c0300001d00401041c84110b4064030700000e803055080024039040c4000c982c500007002013030004c060541048141c600200803802c0062400d800441c404c68007041007015001200110045454001c0001c940d240c07900e00c000792500d04668440402da0001080e55141c40b40d040d001c48542c401c00717031000e0104568400d000c031039505441c09504140700c41082080c0110b4070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 525971780 1250 525970530 525970547
    0x200102121b1806040f03060e06010b0a090311060409061706130f0305220611011a010504210b0705030a0b010804030503070c06240501110a0b061003021c0b040c020f0a03 74
    0x20003510162500c1d1320b400f051007000d170242d00181ca40310b84445001c212003004211040c0100108200310303041250002e0000c282d003407148006040e002c0d800c104202031b69a070070106c500070044400d08200c00c9030790300c00c10000f079103d9890130180c45c060180040c4140c82c1d0406544500c030b5100700711070003814803030b5000d0300e00d03030002d880c42c3d052950080944225507904103d00400340c40d00e515800d1410302040c5a503400d503210054206420007065070868400e98104003a54140e80241c070b014198000100c08241000040c0100507182c41e00c16000c3c810b2282d08100218054205000c0a2048404120040d1070700482500c005000607010000585014030807000b0110561003480b0103c2c1064550080341503c541c9045442c09140d0303248001c000c1584c11044d030001c0070400c4005042080481d44881020150040c00f05025078942076803903a0030781c403e90403a190301c0081405904241c000447c06001012012940790207549003040542009000041d4600460780c00c00040c112700c60785541c00c480c1001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 525973030 1250 525971780 525971827
    0x1002250305090a030b160507050726010f0c09090c080f1302041103071107290913140705070b04021e060f120709050f10200102121b 58
    0x1000b8407120038581d50398881c8074011800f4490390240b5040c4a03d45150b80000c1d9100305c828031004004280c0000c82c007060f100100d601850b20350010004030350011807800c210099807001c5510340480c4c03404120745540000d01c0005165614910640c035081804200c4002c50b4900d004142c0725000507180303a103100380d501d0b40700700b60703070180c89801800b5808503083d6400c3c0c424190a000300441001007540e880403070260043c803114000d00c00380d850149166030403103040c1940d001100c0302480068507082c01804554903085c001d400100011182d02040004100075001c0802c884c034010b022580062141054551036a0848840c6c070740e41d141e0780d0800c014044219002819024101c01d8450720360748520260100700030401c03642c0c0c0c0e1503950310503094a041008001c0b03424452404800d2200d42c0b40c0407240c2106510a545130195025030403410b4920303c803ca200508139000c0403c0c4181c1480c010740103030140c0d1941c1e005548154503042c9605e264428602d54a54420f6000c0c0241c150203ca40c261444080c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 525974280 1250 525973030 525973037
    0x61707050c01020705070306050a09200114030f040318051e0a0e0915130b07121d030406171b0d0e06070e010e0906150a020304081e10022503 62
    0x20490103090780c26030b0007108003a6071a4200c0081002406803d00130594080384420b01000004915070b140e081803241c2000351100c0244004161421740d010f2080c0e401c0c4101e2444c9003645074034110a0b07510503982d0896007217000170071560400e45c040988026046c1900c9000b050801b010b64004ca81d40c09482104a0b0303243d000310110000070307000281c40310325402102110090040035686040d1f241d9046d00180c0500000b2680381c2d00200491072100541b42c21012f64900701d5110382a20b900400030700740b4200031a184c00b03159500c441c0c032410000010412a2055215501456442c6000603d035000484140c940d010b40c02c4007030750b070395442403000b04240c0c0c5801c0800540c0000d420344052405200303c40c81004141243c21000d265030b000b070000660400c0441e0083c3c440e2503c07030f0120b49103280b1945c801d1100e40d030214440154600030700984c2c0150103a0403c0792011240f07240e00c150007023904e1158a0f07080c056055004090788140c000c40c0c0c00311384412902c90070740c500401000d13030b4040c0521054040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 525975530 1250 525974280 525974287
    0xf060e0112060306021b160e040f020907020f1002040e0112020d0c06031d0321071b050a0b010803270d08030a0603020111240903071b0807050a06170705 67
    0x1045058440c2101030f40c040d010060701d0b9850080c1011584800d8122451aa8405481e0b20254030b040c000b01420340794a10180b075400c3c0c807146006000e01b401400000d50000c41141001186a4009840c102081a8608890040e030140740454100e11980c010613903041803410061007410040294a4102d81c4050046141c1c0c0c49680c0b11208000100c1c0c01450019480d42d00c003403024405051711103010b0005a01a514000b401235204090340e1041c01d4000324903400c3c0c40001c0401c1d000d982d40501100040c40740031b207030b00581d18029440700c49504041710340901c1c400c0007085d0700740d000080d205c003106480c007400440308801d034140d030040d001140c45a520101424500c400110144051805200b2070503000c540c2c02d06620025069801c19903103e40160b0221081418030f01c2440b03403d0300c442000143d0080300307807030b490a01030452040c0da0300070b0801820394400c441c5292450110b801140d840d5002e0315030303094442c801c100075142c1c80e00c2403100186132103c1403c3c0c450035600340302d5009150b9050403890f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 525976780 1250 525975530 525975557
    0xb0609010e060906190302090f01030605060a030b031911030105010e040f03031e02180a050928020c0a080a025a0304030519051207061503061b02070f060e01 69
    0x140c170b4403070001c00f00001d0700841c848a060412201c00e880c03a90382400c0900030641808085030a600403000300c42c08040c1c4505002c072158800381711403000caa96103e0700c95103484460030040c103800a003daa0390300941c030345000050821042d208140c060303035010050f1503c403521078504a01404040100000120b008910b0180500140c8010007200a040c680201c481080e102006548942a0f000710f00940304070080202003c41c0b11100d0843750104c01404010410301040c041c024040d044a0307003014410011040b09002004024080e004031079400c680c001c8207803140e0041d500c0007000700803060114000d00c0344500c03412880c4214485050b040303002d4004801c41c403001100e4401c2031500c1c0e202d030000141031003485014400480d000b030719043c5203000311442c1d0340e45c96580d85803030380d9a0024a6000c00c88004202d42c68001500f40c946071034407085402c1c1c0b07a041000080401c0030203595240240e4500b0303608a8008034031b041c02c0303845159402d86a03030724240081d40c4107084039009504022810f079004a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 525978030 1250 525976780 525976807
    0x10816050603070e091008150a0e0114180c0402030c070b0c0909070c020d051510050423071205040c06031d060a110408010608031306050c100b01210c030b0609010e060906 75
    0xb015520120b44003080c40c1000440c01c0d08a1b140304145091690501e46111038082150704600c0e0002c00710201c030b041130dc4d0781010342400c00c09100010f07603206000100380b2400c01115805400c00a0040358600c0c2c07540c0f0307038100ca800244034004245810505820000d4003a0340504074170782000c0c2c009030400d15000c8550361407a0601000b040b0040e098170080d0f061142d032003c0001c40340d01030702040d1800c1003940181980c4044c1c40d10509203080441100e200000e5110b0301c0f910340042000f400707007000e008d91708081c54803078041640c5008031800a0720300100d074540300c2c1100c41c08808506892010703085a031605240040942400712b00910340140811000030490800d2040c3c00050001c1406075403241c04071101c1210040096210604004c0d061128048505003c101c850700c40c03018a03c0042c040c0c52000042e80c0c080a000850b070f00040d8030717800550380200c00e60800e140500559504005010788502000807078040e02e02420700080490010b1441d5003000745c002c18540200600d4103081811928441c3e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 525979280 1250 525978030 525978043
    0x504021c0c031704240905030109020102071505160302032106090f070203190305010812030105210703170901020105013609020a230301050408180f0405010816050603070e091008 78
    0x2000c90004100c00d42c2083ca034858409409030034100c009104c1c4034030b0bd400003941c4071f425000f8640007480c541401034413103000300d0840d0000406c00b40a20358884142c01c0107512508010380040c1c22100c900b40e40286c642e02c043e000c41c41224001c00001c201d40760060000494200184500705600c07082000620300e0409040809902c1a581e034080b50f10341c14080c1a42c24440c0601444907502c85c140010b00195481c0e501e48190388400c1c4460347c9081c0e842402d5507203441001c0e40090040640010751400c040b26140050607006c5080e0000d10844e42c0e11811030031040c4911241c4501c04440ea0713641c503c003568405802c24011444500411020305540000c1d1910b88190701640c41c411703a80000c088010084200059000c4044000300910300c3d19480b2840d861203805c0141c01281c1c20f0700340880b100ea40c0e907244640c030b0a5001d00204031035078403140f060b680c0d80c2d4610100c101030036039544001a5460002e00f2030f4864009681d4202880b1540d0341444514040500142c0d90b94000c8140800d4010707082190 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 525980530 1250 525979280 525979319
    0x18020a14031f0504020a0507080705011812021e1b150f071a0402090106030b060c070e07030608030f0f1c0f0b010311030708071b150504021c0c031704 66
    0xa25500e001c101115a011242c2507000d036005a0052203114201604a01a50a802d4002c41c0c640e0b92685c0b50720b0118011306101e000450040c206095088c00e00c110f04000040c010036a4080f074042c038001d0029080242c1c112500c000c581da228404403000108041300a0741036440103403103400c905e5010b0341c803d18207800100b52004035400c04154031b01030089446007030040800c6a01c841c0341d035041c40d030042282000140510400e05490321600b60341e42c0c4903401101e41d0034500e4806ea4564a0300c0d0142803030707241002c1d6212000a4100300c001701e540c0728080105c03420504a0003265140c6012440d17640728640007240c020130300c2c00503e07130341d407202c54140d0080d0810b8200c5890001010407a01e4009822600106c8516002070400c0c810002c80a401280498001c00181000310000100c000c6440b0820a61035004252140b080c0f40e50a0702d5001e6041107000300e108031112100c0403c540050030102c51041009000400c0249040010032140448043c20603912520b2074030b003d031a04103028100d0f9a031150b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 525981780 1250 525980530 525980551
    0x31c030b06041e23101403130c080f060f13020d05060106030501061727010222082808090d150605040501050a060509030307061104060809060118020a1403 68
    0x8015460204440b00f80161803884022803001c0c0b0084114507072184100919401040c00e00d05024040c0e0050451198040786000e141d41e80f40b600060160403011650710440c0e5146aa010110341004040b030810b02421a4400606080d41c880c00d42444502c0050000181d40e03116010341c1000d605c0c0c41134042c1400340241c000300003e501d040c00080440e01c050780100100b00464141e0440c00c45031403029a00000d9101d072140b1490b0810804028403501d25041c00007940c4006401140c0d40c4c030508540d6200d42c00319a0900030710f80d82d4040c00b6190f440e40c440c4110f0000a0701e190303842502c4c400440c0000c96002c3c0442904082c84a008201c023040346d45001d07030b03c8506030200c0d07004e419150700440010382801d42e01808154074240110315850584d000307280500c90b010a00c1c881c6d940303040040e0b0b94a590008001d12861428201c40f0006034820300a010004081e031002650040c0000b0701c450488211086607100c0901013810007000350014012481001210305912292103414009540140124407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 525983030 1250 525981780 525981809
    0x71209122907050415030216020d061d01090b09030c1e150f090d17060105180d2907020d080402061b03030901140417130b0d0b040b040506031c030b0604 67
    0x2544045c030040040c2c3c40358209401000815040d407920b42da008003865064400100c0f0403100c3c82c2401c050081c408007843c41801c810740400803d0015040030203030300e0088901d02060740710b8107500c64aa206100c01d005284d44070b101506810222034120781d00300702444040d00c00c040c010f40b68a000801056443c848810000002c1c0000424184455201c50309581881807003840c40350004d400b03100c0c005012605002000c0342074010050b0340c6c0c2c00185000702c003c00280d442019450040345500c1c00c12844500c035017158103101241030140140500450bc40d800818181c12140021a40568001d004981242040c0100c0d802c01c071484604450000d030b41006591a4a45243c8617400c4601b01c84c202c400c0040308800384404540c10b5001440c540c00710440c1e40d03544680f41d800e0a1055503496003e85990f640000e80c411403407841d07505c4459001e10403103090049080400070402aa00140e48103130f0703d600405800303151500c110440f01d42c80f0545003008104243c10310002406170b0002d5002540302504070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 525984280 1250 525983030 525983039
    0x3040b2a0c0309090c0a17150d06050709061704110402120f04150207030509300607090f05010e090601032309160e0705070204061a0712091229070504 66
    0xb0302c83c1d0307009980c01006410001c007000010701c0344002807138165a400400c80851082c80074000c84232800c0102504150098007249000340092800311404c0300052141e920103d000c510400d100090509004000d408645640d1600102c2c01001ca034401c0e8466400c101c01444100040076441c400e0864078031440c183d00d850f040c40c0605e261100c40c0300e013000307104101010010343c0000964611a9040e00d00040d5400203910941c0c04894050000c207081500e0509414030960005080c7e100e80c405a0347c15000654030600000404407500801340424010208010541002101c0d9a4801070524000c5040c00803d40c01002038510880101e04c1401c5620400008a4040100000070858020b002c05c2c124503191030b0155106d4054211000c201000685400f035590b9500b00074050568016904c8419003240c049540960242c0000c841880c0042c40d240202d070701480c9410304075081e240d0040725003103080c2d560301c0000148450202c40031940b1054041c00d0840782030710510544c03894803102d03075031401c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 525985530 1250 525984280 525984289
    0xf030a180506070e040b1e0d02040203090d12020405090a02130e0705040515040501020c1201020c07230103060812090a080d0f11010c17090f060a060512010203040b2a0c0309 76
    0x3ca1391014000ca040c5804a40207403900e8481007100410301840c00e0203c030754400041d101032038a183c060b6119001009024003090701040c0510342c800d203901c07a840450528440320059000700c4c031400798445207010001b000c0260540050029203462001c0e008401d03200d4403a04502070042d104a000640049410f00c82030030801d1480c80c902d4140e601160500e440c0c600002c0d5503006200f0000e024100341206191008801d4041d01c4da610014815520700c903403902d8400d41000c0460b880c4040385c502c00304e54082d1070f5010b80b080e64240c800500103020740644059503140203501070840c1d0780d0400720506001814010030300421524038082c1d66500b0810320907940062003e01445000c0301c55902d0300c8000d4440b150090715104d51100140702030101a0381e0f0746101400c05105643c150060b005281c2040540d21303050f4000000d070380c0c0844580c0c00e03200000541c5401c03400101c800030071009440020648401c08501c0313842c0081c004800c0e010300b0085464030400f89401c03403c40360a4691001c0760240d030a207032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 525986780 1250 525985530 525985547
    0x21020a0312210506040f050f040f05160608060f1027030602190e1e0118091a090a06050a090f020f04060c1a24190803030a05010b0c030f030a18050607 66
    0x42905052105041030744107003211404c040c00042c812182b4200003c204003090052200e0004d4603404900c00c3c130fa4804015103210800c881140c0300c0d4280c40b946413903601d440300706129000f0307056503070f005d104040088035140b40800840040300d2022020300007000402500080141a07540060b50300c0003a4004000b501c01c410050b081445070f00300700035100a00b0307a400403508100109103440c0414240031001e2075803540d05600304840c00c1d8100031182c1e040b48083c4103800352900301982c02c0542d0340c0c1da0b52031042c00c44d0302c2c40c090341754426905030301008808403a03005030f06014562580140341207041407003900c50f071b0321a510003008514030740300070810700c905031100b0009264a0022207541e0b107000c00c031510a40d0b0a01d03030003101d000d03071004076038203181c888691a0503c0c200031440446450f03102c500640e901d81049030084031040c2441c00100d00b41c030440083d114101800c0009600340100b84240e408160001006200c40030382c3d031940c01d0900d03152030b407078501010300030340c050300755818080c000601001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 525988030 1250 525986780 525986801
    0xc0302040312030f2903060711190804151d0103050402060403022101020d090b09070501021f020f03130210020a020a090b01020102160302030421020a031221050604 72
    0x148180010804074144402038200d0495901c2c00240354100b01c0c2c000401048460a509103101407034a0b0035004207086401d02595803412401c503070182da5500c40460b07503800d4810b54011250401035803a060600501c150034250740c410100241455285c1c01c558000c082d01c030401800090038244102d00c0085a80c0c20740804c01400e1a05120500c0c094000c64031500c40e030700c80240030f9000c0c80d400300160b1410702c500c1c51411034140001d654540310408020b0180c03c0d400c03402ea880c608580d02081140000085401c110790068004d40066000d8050b2041c2e01880d0281902e0800d400700324a10f55000303410000d40c420345021002a038104201e0040c40300e40350b410102042554005080320000d6559111004100c8404410110380181d046004030b000e40101d004145402882d40041030400d50040003a00c25a6034503046501496210381855124019011001e500f10190002c10300204180e84140b1040f0314090030800740040300d0541c40b40c9a0403056112800755030341c6805110301c6140a00400c860070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 525989280 1250 525988030 525988037
    0x5010e10030b0606070516060203030a06080118170c1f060e060906220624020321041e061401080102130b07020420030708060105030f040f03050d020f0903010c 70
    0x1103003140da40480142e005440a4490040811500e04101c400c008a04074400e1058001814544da030502075540d400a8801c400f0b40c5007071000126418005114504030107681801182820780d081c0c50303182c01d40800c844003140080b410003404002050401600010b44120a9000000500f00300d0060440c0c10075017000164103d106d09014a039600d10701c1050f045102254082200c51441900300341203c1e0f50740b50a80541d007800d400184074855a03c0382030314542103804bc01c1501003241d9040303840e803141c1c042c0501d0300300308040d44010001040f030340c4a03401031084145010009075880c0c110b000c002d110f0801c032445519946030b9480d400b10110b0395401010754400a5003004600900c4086284050107186855240802e20b007040d950b03650050710000e00040314049102c00280707800003903a0300443d1030601003000e2201180f00c40d4410300440740b061a1009c0c01102a46840d51484041e4502d040c066040000c240000c030b040e54180e2004202103010003080715039a031000ca06140c2940c0952078001f062 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 525990530 1250 525989280 525989311
    0x4020108060915090601090906080703120201020f07111305010825080a03032304050a0b0603030702090114010915020321010305061602070803040626090309040f090f03020105010e 79
    0x15082c0d51a90142c4540120355500c1c0075994200107c503110300503800802d4550524000044d580c4e40400c0d41d0043e030b40641104a000c1603200380607801d1f441502501d0008800821100000c20000081070400c00c034010b0055075400a42d007414800d8540c01c0e04122a40d801c403c1c00d004031000508500c0d90010760101000c10001e103400d0419442e0081c3c1c00000e030925489100818140260000c840201e21844d01860110b05203030602641c2e07600703044002c640000300c1d0400b003111441c0000580394204da00402c0320203a60f00382580b10b01e01e0724400c10158103010141c1c0d40410980300e5440c4d10713250199594011a06c503244140c550001d4820510b000400c4038400005001007030000c41c105610800e82564901d915201c0305d000ca240c01c680350300c40c0401c0d01021a0109115074810f0036500c440e110448101c5d403400c10940403171750410f03054800c03038070075842001000e103503060035001100c26032140342c000511080c0a441e10440354050500480041c1d64440061094608101e0701c2a005454825840380 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 525991780 1250 525990530 525990541
    0x80d0501090e0c13090203010e060c03060109080303060607030f0e03010c050c1b1e0a03080301180c081e070c1b0317210c04051206070807170c0906071406040201080609 74
    0x70b0001013000b0180d0340740c48800107003d540302501f01821030881c90b0100d032404e00c0c00c107065802a0704250360b158006601c1f007800240765200001030701c0c041c00c0014201880d100c0c0c00d681c140c818502d105900d40c14003a031003882c03490f40c2d43c0070f00c0307400000169501c3c0e03c1c1d65a500340081c2403c145a10a000e19045d40700c15030f4101e2501d03105196240d222000c81c1c42440d84025900007200d07192160700080c049a000000415003000070580c5005400304040c1c1404900e444030300c00d03100f80380b003110034101081d400004400c24158685010781c215000e0b0502c8218002e0035107501040300c0d520303001099100c0c520802002084030703a00c0ba59040d01d1345a4840d44c100f00c10355002c80140c0035400342d204078010120020495182282007100d00400c1c005011050040401e00b41e59211681214171101141402000a103024080d6480d80b6a0007490022004a03688224510320150480f180c00f9030404030520a0500094604a0703820310747c1030071001000350f49018400100202c9006010304d000d070381e54509121 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 525993030 1250 525991780 525991789
    0x1b020601030807050f07180c090e0f0406270b010503070f030615180c0e0303040f0b0f04080a05060a05011212030c11071412160605070609080d0501090e0c 68
    0x24152948005516550003403801c115185c00d407038a1103400107010f04a0b00091501e1072404140c10106404070500c012100c0f810192040c2140c2d200d5590661516000110070000400340709500070b00c20000020301c1009504640844084505001501c040c0707a403a038814081254412401460201c00400c0c8860801454105400d810301c401450703262100d0909142c00d50a0040002401030b14001750605070050601d5406044001ca41c1c1001c11180e104c80d800074180403007100d003650b100785c8a000089207043d07030f06881580410200080c09206000114903148240080d54a5900401c000c040a040860503803040f140180c2c41045101a1005075400041c1824070842004e00e45050004030990324480c107076201d400303601f030010050007281000300e0052007007060060b00c40c0302560200300040c4d0300c52061355110704a00503070303600800b000c6040265901c20001020110b00c10382012031a80c800e652100c095800402003c3d40e4151030318014403060f101c900c1600004a004030003031107144044400b15 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 525994280 1250 525993030 525993043
    0x3070807140d030201090f0303020414040b010e0f041b030606020f031801050c03120901020c0d05091c080d020f03071e09051306081c0e011d0105280c05011b02 70
    0x728021007a840020b02894000c0d44044052034000c20b90f000c5036422480d0050023948140941d503120703141c880b140d01107810b0611442c19104010b8454030007030240c42e4100006c1c580044852680951100300c5901c10064042c6000d2103440c19031008110a0308000c000b0381000030399400c540c2c1d0341d401406113444082480358551300c851003c1c2086a6030320100c0081b18254030401040c01c2c0864041d6050083c020415030041c901c2411a00503550000c0442c00d0445084c8500360189034403200340c91f0300944100882c050242031500c100081481d000741c002c0840c0030303600000e600418418020040000340e580102c8280507041a01d0300700501802c030040007a00c948910300489008410522010768015071540c80720010303005200480b00001240f4049114005100c29001c0000d50601e4a000165015a10f03900e000009480c40504e560462001107400380c101100b0420306421508102030b0440726840d211580c28200d9840686031201402c0560a4465400c8034840081d90381f000000055070200b40c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 525995530 1250 525994280 525994319
    0x509010302070c0b16050709060609030b060a05150702030c01050f07060e010216081306170408210f1b031b0306121204090f090312151505040503070807 67
    0x1600c0b0426402c0c040f8411045400410b541c01001441c8548180380c14608624944100100d0703818585680f01003080e200188107220204004800c14000240c0790040313994800c0010701250017080c1c1e5500020060060421440045e4200041c00c01c02e5040070701000840c41401e091551a095a000380d1110303d110380071001d0101d84d50b480f40e5400d021000e4048520010f84c0c000803c0b4515181c3c1050b0400d035011000c00c0504c01e40910001480a0240c2d9425084107a8032850034920356030b544481e8400c4c1e110760101c001c01c80880350710100000781180203074018405c00d103040e61240782103501906085224100d44940d580180104001c00d022580c0380d10b10314681c13914242d200c1c7c0b205030204440e402e82506080440c0100c030200350a00c0002c401030003c49402c03400510032444149041412944140c0016000401900040d860003400e60040c510301425148031002c0750f030b0380b022078060384000041d0740340c001040007508100500d001c101307040c05026400060b1550b2860074240000845680c0312 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 525996780 1250 525995530 525995537
    0x120a05042c07030f090210091d0705070f0302030702040f0230150112020f1201060e010c08090f090705030a0c0207150c080d1119020a110f040f180b01060c03050901 72
    0x4034030b910070115800140307005501500c584150240042e000c1c00241e0f45000e80027061003017000041515440c42c20b528090740040c0c5981e868a2185c1e140c003000d0082301142941988810011040103884505c86c9a130b6030400c62400607100ea605005054044d592401401017400f04117002110b42451029102d800060198603052240d2864005840c42c1c3c8205503540c070241d1000c1001a44680454010101980496440080c03030381c80d2102036900c201d002004c1800142031b5001c5400140c42280200100c4000402c504400c45180d000500389110403244036001501c00b1003444030340302490140e4190790700e0f01c0c005041c11a04000d031415058840d8000c10007005120602e840502c100801280c0f44031040110a12004c43d40c0c08610b1110390103608107080d0200d144144040c0c603840030444134041984642000309494200042041070000320030103a5020fa955065003007080700a105808500e001d82c070450407281200c0c20300d4140011b05138803950030b00000e24201d200095200b0216580c0c000f0908 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 525998030 1250 525996780 525996791
    0x40e0a02071e03121e0509010b03010b0109060f05030606160302011505241602030d030b180f07030b031e070513050606031b0d090b0405010507021605060c120a05042c0703 75
    0x2d040c000717902048024845401c0c035181c00d00000c010190040c0d80140d10035002407111940750030045070412214825000061410700000040512641c01940c125070010609824255034050315405005070440803000342c0e56448540140503280914030009003021940d00d00b500101105d100c100351850b8541e1411210001a170780d05100d44e4500180813245c024007111200000d4400140c014095243c0852140c1694400c40b82e0110351284441c3c8500d0004481e0038031038030785420581c042e150020072698180280329403260080311403400c1ca4146101c0500619009282005000b80e9401440003029140c2c10312007085219254882166001209949002003c401c004507007426801a044041a2141400310074402e2240c1141068003650094008004c980c480e010240d9940305e40628a9840b0380140d0002c20041c6802b41c042c101d0214044c01361210000041008003e0380d1021895501080c00031800380200003040148008901c5001c2c10300410005000c809a00110014054010149c41301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 525999280 1250 525998030 525998051
    0x607051614070e091f0b0a03030e1f090906090207050c0d03030216030905011d0907230a110d080105060f07291915030b0c040e0a02071e0312 62
    0x104000801040d594070f040105060003446a904c406212900460f90340c054140c11004c00902d110b4203103850001040b5017240c9245580540e2000b10380700406500551034041a9400c1c02e10f5185103100076169624810114105002c440850f100c9401003903100e441403200e48001040003a01c4220301e032086460301212104da00d4120301078411400000240b11002d400c2d281015040320703800090340d000740c07110303003081107650102c0f40f03c003009402d210351202580000c034803c60f010300c01c00340c410320030721400e5070b0010505414140b035a03018515100004400100342d00b0074110504c5000d50040c41c500d4a0386281d454030f0700007405400307580441d00c840710000a0f0740b4200710035284800420241e40c002c0752884a030200500d44420f400321055014484e0008a0311002c4160b4490003501c404491040c4011500316100c4c00407008c4000c00740115460f0070440400d421050a08444c426564040d02581e61903452400013149404560702c00000e004e811440000686c01500041112080340400540d04411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 526000530 1250 525999280 525999283
    0xf03030e120705010515190303030f0b030604050a05070e150402032211152503090e09060402030d031109042f03041704030209070c0302070b040b0c0607051614 70
    0x60481c0d034003100e00084910401006400051048800d540e1005a85105100f400720f464030048140c1035200003100c050000034001c1d4800b441c0c1c440d241b100018081108030109183c48025502540c0607400400a002040810000d40c406002c040b6400c0c4010700b440900126040d50002c0010310568010002a40503441005801c6040c0c03c50902e00300c02c11414107000700c19001c1c19000e6802007201c0250a42408010003c4890305405000c20b0380c841d2a100308580c1c00071307510344400c030300b0420002000100740740381e94078280c007a20125029000f641028130403d40f61002100c01801030504240ca40b17482c00e40b0090645010810a80c0c001c2061000c488a5003280022142c10510001c2c6c02d060201c03014800c06d0295220380d1141c030400c4901e044000801c0094000e500c0300a6000004000041e9010703c03440000c243d02e03100c3c0c012900080e45511440310290059009100104400700303040d00901307410070280303030069500d00b0080d01c6c01e0301d198280c41034044c1165000d0101d8400062403e0300510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 526001780 1250 526000530 526000543
    0x5070b1315050103060c02010e03130b030402040b03010507050c0c190509130602190e0402030c09120f1e060f0f01150915020706080a0c08040b060616060605030f07030f03030e 77
    0x44031002c0015603141e240c1100244106200c140040d8605032002501040010490320400b05a020700c901c000d1030062103c1c20343e40010400c036041a00c03203801c1401c03910240109400f6102a131507264951030a00109440c111110380c00d039101e10000a60024140240c03020f400c207854085d10f1008440c3d842c0e110480c81d08051150007004584009aa5061020300f0501c0d151005010341c1c0342400c4080100c10001070303000a0f511007180043c20400b20704036240c00c10740803c065111809489421140200f02030500c1070030b400840e0f0303c05114104151407c5d09108807a0b00141406e0510303100d092030385940c00d084005000f5006101004040c040940380140042c00043c140604202004000c3c800003d4480c82503108640c08100041c0104901811340c0c042d102c803076206a40c61010980d2251182c0000c124003921a54000c1002c00580401c0030b0203a440c408500c2c081e00c0c012a01901e0441454078003520f4070035107019030704100c00a0001504068451060542500d004908031f2800c0d28011304124 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 526003030 1250 526001780 526001813
    0xa0f0302091008070c0c1e05030a080d0c181d1f14030f0f07060206010f0605070f03030902041805120c0309060a0905100207030606060f05071412040906090c05070b13 73
    0x201c0c407060000c0c8800390107c200041d03485400096140c59560414142da0300b11094000740207503024131544605c0c07445503000c50790140140c43c00168030b42d074100b50580c440d12240c100325140141300804116054110040580000120302440d408032905c405884a9030103900038402e103c0a07600c40d5205541c0d040080e0001d07220f8035415030f0043c1881171142940c8003e644907180140c020700c400054900350150307400d021665281c894629040c00780e42c4041d00c2c00e502540c12814142c1c0c5040c000c0141e1268402c0303400a401c60307003804800712b246d030900324942040441c409140300010000c1c4101800c01100360b8550840c140c1c2c100f0386a010001065a0011150300410b422503c1103a5504209034000b485c0804c80e80078203010840a612054126550703074081c406800440c104224080010b10501d280c040052122002e5800e10040180f2500c00ba61059102c00300c1c10340c4488041c40f010580e4420b0300c141c5811401c186140c03030410350710218854401007410f400400d841d2840c1083c0103031500301c9049007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 526004280 1250 526003030 526003043
    0x204150f06120c0c02010c03051e0c0109020a0905060102031204050705030f060a0b040b011e0908120903060f040b040b090a020402030f150906010819020c0102040b0a0f0302091008070c 81
    0x2611101d00801c001d0010b810900340360b00f805070005215004000d480358203030f0181c2d9510308094560710242c4456000c03030903000300300800440140c400c1464a001c1c140b4405200008a0204c0c5c0d9401045100700450300551455850001440880da0700041241d80802c0300d05603202c043c1d5510708003181448080c1e407090b90107009182910007405c0000c1a89449014424001c11a1002171410301003203410410000d400f041e620445000d00348003140b18465441d003d8540660810b48607000d032420600ca14041080c0d1110108003500300d031505012090340480c9000820b502c034905600e400b0328500d0b001d40046d02502c160004206680028400310b205a030700904250350701c2c101113840c14030388181143da264004103402e14000540c64100c8103070340954070595a2040c1903e0321103914180264041c580e001499080281da94001828005003000301a03e05101c0e441d00c2c07031845c02030452400e11108400701803042000000650b04d05240110302d8404e4a00942aa520b648013aa0088400d18016041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 526005530 1250 526004280 526004309
    0x10306080a03030b011e0f11010b030a080406030f0b130c0210050f01030210050a140c240a050f0112060c12140121080712021c1119030507020415 64
    0xb0b05800d6000b006019001380c1e2119503030025000e0805410702c2c00c40d50f40740060301800311070030390510413801d103080c0000f040c0c00000c0441c0400d00107458000d1088044500792000b00c1c2c06c100090f010703c211540ea101e86801442091600300c00112207800c000513800c811036481c86044001e610810441400006002040155003020703c1011101c1d002484101e220f0403400c841450b459114100391025002c6903110500224000e5200c0603007600f0104043e205031103180913a011000c05011503600303034a2980c50407030250420540510513510300034640b0581070744a5004100e50020a071040e00001d0700104001801c5030013010845203030f2039042d414015542448015002c0c2c444a003042d41c12504014104d225040705259417000e08802c406001c0d005000600c04480440ca850080006060759481035a40340d0041a14003104c100d10183e15000244038902182c0f04442c1c104800c4502c0154001d20000000351558010103620520b80001e000710303124407100000300b030251880300141400c11816180d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 526006780 1250 526005530 526005533
    0x609180303010b09190305060f0901020c0111090907020a0203190303060e04120f03200904093509220b060a030b1804050606060703020f100e06090d050a0e010306080a 73
    0xf1604180c040a1041810450082c001c446080f58035003201d9000313014180640c2c072001d130124602c10040440c5d034655001c001100d0750700d0080c071400031701510100190f900c3e0700031103061050319070300288641c056501c0984400003580e000240ca0041c2d12000c4400c2c8613500040c0b404801502e440c0d48112100500f0909220410004910310b401c0c4000075501c5103410905c010044003a5174401a50b550100f281c1500d03100300e0740240e00108140e40c00a800402c1d0603203165609405451500034002c1102e4801c04c4102900c40d040b0700811820926481590400280100240300000c2d400461105031501c805c4200050f003668101c08601d904c010042034907603800000150260100341c124900c1018030a2019015190549449018a802c0002400c00350f0380e85040c040c4541c4541c0054042d407240207101405071408000900c079a011050001c070740c3d90100401203207000c402030203189903034001c0b80d040c0c0581540241625814000e500c0d0a004000c0e0110068006040b550048005030080b10181c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 526008030 1250 526006780 526006799
    0x51b2a01060312080a1e020705190f170403032f060a0219080103110607080d1107021c150b120115050909030a05040e04030e04140402101106060918030301 68
    0x301c8000c110385401da001d41e501d034411000c41b042d05955100700c09003504401c05c2c0c1c903190760160180c41c0c414000c1300d142e032302c0c00340a15045910303106c4211624000c5000d020104803201640c0100d40d50600304540c1860300f0340d42c016241803008a125400000c3c000e904031118400070300000f556422141c151102424040f2580d00a94030583d03003800403100e00200001c04503c20320689040740d0b0003c0c01034040c10f905008029195002820503a40c0319001e20400c070020405200c0e201034010303585200e03a0b6905007481031044010051080060300012080440080342801c6141c0c1e2409513210000902c1125080000799010070001404000350320380441c2c0c00300400880030310320075a20100e0340f0300342a40d40e407a1900c1e41c0344507000946000030400e000c10080d662140400076000b91203824a01c2084d01404049812107404011369010f114201081c80103504207030082c01c1c4800110700c4c4c0300d6005102c0701c400968600002d414030340140599000500c0030703680101100b0100141000b9244d40313507903c05004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 526009280 1250 526008030 526008053
    0xc170307020618041b0807090501080115030e1b030120030a11040b0a030b090c0901020a110102010b13090c063b03030301080d1b17130803040f09051b2a010603 70
    0x540403580c203c01045280e80608023003412500165140c0010784c2c24a070450003500c0181c12210b044c1500d800701d41c40301100030301c00c1c032078812221419403035044590300805080d1855803030f0b06510000101d07c03001041c41d00a04503039209031604c9001c200041d081c8180104c0340300d1079010b5a0010804141c0d444041d40c1a0002c0091500440d6550707a80c0d02c0c0c50a421142e4801c1184103405603208801140000f80340081e4048401c00500000030f01415010100300c0c664242180800c040d42c0c1e458146042000201c6076401a22080c41d012031869440d8003a1084001c288111005243d10350600601141004103d003444840141c10781e9160759484491070b5031409203c041c0c0010802c0780d0901013000c00010280c510303043e040b815810580644031818142c1c0d0b4081d0a2181e03000380e4400010407d002c04000400081101e64482540103140500f0581114030203403103070010910368001400084082d07410b950f094402c2c0141c101c00c0680e0845031400d241780000b41281203508040c0d001080c460b024000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 526010530 1250 526009280 526009331
    0x50a020a020a060302070b0f090303371b021c18050406081e0c01050a0e0d051b0f12250e0112140303130b10080303090a0c17030702061804 61
    0x1142c1d150131031048080e23402252121503d80c41800020800c4958101c24507100c4140d02e4202c2400c084188404140d129088100b2020f5460702e01c8024581410403005c0f105c800c0c0c0f880900507840c142c151a50f001c407647c45440782000850440a072241e610047d4603002040000e00401c01c181d69651244d4448503004013080300785d8424180b071005c4050119641540c80b105941d0945840c280b2030055689852103036400d5005101d021458001420401c6000c1e03150480e640d0a8000f4001d80c0e0420013208c10800580b40035030a082030220004800050048601101041c44200c0e100c0ea0016400750054660295440d84850000011343c4481481141d001b5030003500d446450075180d030709050790b80c0b00540b0301c1071a26610201c0040403400e05010703e6080054845107410140c0c1d9210101d04d140c1040c2e503540e41c0b03600440300c103808100e400c0c20308000a044800e00700140d0100008105d449005003103000c0e01514001440a481c0c43c07010300c405010f82c400400401050f07070245500c0d50f5070b0043c1502c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 526011780 1250 526010530 526010543
    0x50405010503070f05090403050403020907020109120903031d0402070c06080403080a06030206181f18050a08280c06050304062a0c08120106080f0703180201050a020a020a06030207 79
    0xc01d0340d0402050030029034000d8400c41c40c0a610b0a0705004402d40b00500c01c1c1e0401909000110050380e4981500b4000d051743d900104900c000c0d400c00702000d104101c856014050340c40020000241c02036089201203440c200704041103044603011030081d110f0408002d0803445c0b580008203c0c5074100e2903081c0118003c0c1e440419581d2620350700d504035801800061761081e01405140040f05d10720040f51605800074000c0300d115180c600c0340c42c0030089031603900400700f0f04541c4014070b22910000080300614045850b145900d20340304146450741d1581005d00003c005d880113002c513442811010f000e0565002010840f01d607a03070702e0002c0c5550000d49040300c2e280e007003000b40d1907000c204e0554200606c00720f00203100c8002040c60140c0b40c585401c50202c401c401c0a00941690b4183c3e150214002d10050321440041d280c151000c0740c9042d0f00800f10000d15140003000c02100c003007180ca081141d9420b080550751414140000d82c035008807000c1c025803000c070119010698a6050700640700d003911450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 526013030 1250 526011780 526011791
    0x5010302030112110f13060501020c040c090e07020703081801080a1104060e0a050301020a050a020f06090d110f01060f05030c030606030a02060708250c120b070807110709060504 78
    0x4405900c000e119440c100341049062901007040c0721600304807800300800740c88841c80a07202150320701100345a0a495150365400403c102d58060102c1d00000004990400009800d03c80243c12110700c0c0c028800072a03504030010f068203008100c18000b840e00000d14540b5210a4110310300c00f2903c05281500244d240070120300e100d402802000c000316010020642082c2c280001268054000018240e003d002d203040029240c40030f1005060000040c0c2e2030301e0303941d108184040d00d4103100c10580c02950f48420104015044003042305103101582d031409a1022461221080c9400303c0588030020a510708400082d01402c034080c050300f10b80064080d100b03e01c01c145d0806440c0c1c401103030200e4150b08000703800401450940300078174600f480703103020f2801c1c10480f504c00c0b0019105294403400102c0800c4a200a018500c480000146211101c58801d400c41d50b031069940311016210030103020484000c1083c2a0086d070314048001c00000c1214591642e420000015000c0d40c80351900491500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 526014280 1250 526013030 526013039
    0x3040803101203090b090102070b07060b0405100b070204020a0c051c1b05150a090b010f090b0a06020a02090402031e07050a0b0a080c0a03090b13051606020a0b041a130b01 75
    0x201c0c034810019030584c940080c15460000c4c060500d0b401403000358118080e40c00041003455500d4041c0c01064013445e0000340d02c01608092004407000a0941c504d608900d40c02005020346107800c031940c040c0c0c1900c5c0580c5400c1031140643d180070805400402d513004506601765414829499000d0724a015961850500020041116003072401c000160041d007002203000c0403068071031441078010111810008035981c8940710314019517020303001001055207203802006145654010310000c890100d88219513107241c05c03000303540d0b144e01c5400240103003000d10004043d550207000c183c2c2c1a03c8840925900e243e103400c08103458010700d000c0e00d4460386860001080c1010300c0800e0f110b0260761398540c00015103882c00ca200c601e03000b0b044075030708054035040304000280c400131034207010340c280350406110712040c0c5c60007504201c269000e81400700f030401010050650300045001c1d50b140c0002a07040703540c8803400c01200400241044194444106052000c10201c03c8110301c549402001d40c40700380e0342c85 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 526015530 1250 526014280 526014299
    0xb040b01241b050a0506010e010b0412020f0a0509090a0212070806130f080d050106030b0d1212020f0f030601121509020a02010b0301110415080c030406110f0304080310 74
    0x1d00040032550711424207200300031400b88203480c52800e070082016440290940d603091501d211010100c0d00754008200401070610340103012409020f00015136400c1900b03060031f500a00201d83c4010340305203a0300100c110180c4645903818050700c805801500070b80f0300746001d503681e469008030880c056010f45c0488500c1d010702003820815580090037500c0c041d16022212928034808420036284040001201307000a103910f8000e01200001c4c40001c240c03076140103070140455130f541c07040602a904101007000001c41c3c1001c0c0c1100320a070340c102a0301e0255071201a0009004915504032030034000110032000002c1c42d80550b00c00c410036641c030450f81c0d40741c0c2c180718103442c02c1c10864400807214420904c403c824680140865040b644000a03501401500090940d040c803d4419070061001500f40164040d4000c0441210203905110115003006000740c0c5961100030406411389969000c0c91b0242181c03401100e03c40342c00040401e40320705041c14140415442990601c003100082a000184e0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 526016780 1250 526015530 526015559
    0x8070212030411090601140a03090c09050f160504050312092704060b063c0a02120d09020303040e010e0a0504051009020102070506040807030c080c0307170c04090b040b01 75
    0x40c441c0d003031000c3c04210402e000c07804d6005030146050081c1409100301d40c0d103640e0003612841c0030a1742c3c003040d008000e081145030016190050311003541403200b0015103000701482c0c95001070102103586414047c2d40001c40740c6004039041a64980a910800b43c0c00301424800780080384811200058141400303510b0b40c10b614124103048200c4000300e80000c011400341d2340686802e4801a2400345000c070076080c040d6a881c1c920004000c0b1802c1e41c14a0700300c1401c450307070030f1488110103904245840c020543c069070703c00c0c001a0380658281c0001c5c00f0194003035107801045940d0b5000d400c407912181c4034a08406614801d0103202c04580034400000d54645d2a4002c803405103402c04060404410000e125801808048005034150701c2010300002d042d860780030040c0002c1212002508441d81180b81c00f44807513206c2c0c1d0151246901c90300d00c10341d4a5501080709022240400008000c0402e8187c003181425513901d902c5510526151490042c8000c4204540c412446450b01070041c2c0e1306c900c441c619805 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 526018030 1250 526016780 526016783
    0x516050114010f080706031505090a05090f061302130e0105010b0304030e0303070f021903050d120615090b03090705040203041101020c011706120102040314071502060106050f2206080702120304 85
    0x203104d41d0041190034000e9003c1c070320345688c031240004515218030100b4007906043da501c040442d45e58042204001003408145180310000016184070f042c440110361031001c42410180c452a505101d4042002d41940038000a50f102e100034800d80d0b03503c00c03400d08aa04211002c1c0c011500410103c0180e00c4d001c0100c9141d1940903201c81c1082c5c800360280710302a161071000d108000309040000c008120308000303a0300c40c0400ea0f940e518a04840401c854141c41d2180c0c0503c0d1900102003500203a00d07006010315050f184002070480d1641e48440d2807518207011035020b10340007403000007031006008281c81ca03081c01c00000c0e000c480805290200441d5541c3c0e403060b10042076902017010446a16042050000b602c104070009410151a40c940c140b4800ca0b03004504001c0d44501780c204800b0b94045080c2d98503040f41e0014002540c94804040c2c00c901c5110508000c000c000100381c4450303240c4c1d10604400b20010900c505043d03449074005400200c0a40d100c82c0540b09010300c1e50400960b140483c1d1213507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 526019280 1250 526018030 526018033
    0x3270108070f0f030203090a0c14120106050904020d0206071b06140c0a143a05040e0c03270a050106050f01170c070803040b01140427030516050114010f08 68
    0x100f100001c5000750000b8240282c80d014030405080032412505203880580103042c2d00d8801441c0306010030100d64413180c0c41c054564100041006640d4a4118641d403090301a50300302c511150714400181d0612515100800507440c80c104000d034140280c0705041a20f026840c1c20000500301d603d240c44d0f5001e031000303076211176001c9510200003c405402c0b1207040b009080071507a5a01110b40994100700360f14944841c91002c400e081c100003010388100041080f800c6c00c000e072907d401e000381c00c66a0b440c014104448004004041780e07010911122820005010a503865418513202c074a40703440d9140d01000b540c040d270034090082010300d0000552050340c141611507003010310a03818040704484004281c11181e40e03040c4104004110b8a40007540308074852441048150306200d04e10081198107085980124a0402c0403251541d0758140e1200e55580300005c400b0200141c0f60803141c0f8428183d54465014544014900700035054006054041010041004aa0f00c07450411380e0203000b84510b043c0d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 526020530 1250 526019280 526019297
    0x807020d0c0321030b0d0f02060c01022b02030403020604030e1f08040b06030f2e060303020f06150a170a051006030209090312010e2a09040c0801030c09020c03270108070f 75
    0x7e50f1000221403c070f8806801c1d64246030358404600d0882c0c01c00d035010403040016a0039034041c0c0c0c125031010300079510224000c40c1035041a48000b9603542000f00300038184040000100440e035105444410001d00078410303180361500201c00281615070a6408a50690059022030420b213404580c020758004480000c103203500710449020003031008a040700c582034800b4242510000d095003c0c0001544c000d4004060b2900340c030f840d00e441d12a00030010031000d00148481119650f600078441c1c1110034031040903407103181001000303041c80306100307005156101e08540c801d03e00c000f6800c1003080342c1c000c0b00c42d185190b607500c2c9256180c5c0b0403030120074044484d1100602211517103a03101d642042407000c056007081e030300040b240d0200d900209000301c0c0c0707c0b0110740c003151840c2500848444010600e0704100310f5140d580d03084401500b9004100300340d500801d1908a10404200b07030b8074041d1030054030701008107200726000504500410b03c9400130380040e0020b16100e0046120790304420069560152 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 526021780 1250 526020530 526020533
    0x1812081810091115040e10060914041b03052a09090714030a1505040209030a0809011704150c020a0309050d080403021207050f040603030c0807020d0c0321030b0d 71
    0x60480540488409203a18940301003501c3e2081640000c404c1113004664650424a06008030b46000b0b20b42400303c617501c8001e01003e40e01c994048101c4039244040040c03107000400050180c40c0030740c01400c8420b2041c5880402d0307581078120b140541c3c032440b6a00e040c0610b000100607081e84005603030914000800401c51507082c07090210341d001405250664039581e4100200000d644141e60307941d2a66290351049501d1001511882d0080100311001c42c5003c40396000b20707454035076852014081c03031404030b03240c1c1180e4081d451440031400800802d2071a071901c0e2030400309051601070000e0300d451410b1068011180001006464036807d5221915001d140c101040706e404120501100c80c00d20611000006864000303d0f14010b035148806080a141400b06004545082600031b5110754104101000401e42000185501d1901b203821981d407202c440c004511400703131a40000b483c124050400006015205c000009201034606224500d00d40f180030890035610f142c01078580c44580b4401040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 526023030 1250 526021780 526021813
    0xb040b0607150e0f0c190303021e0118080c01060f050604030f060912020d030509060c0d05090a0210090e0c040b0406050711120f100e030a050d18120818 67
    0x851100204008180381c181c1d0440303a802c0480d413082c034010503813000744003556074941600791440081600070201002446d5031402035484404065a110450442e000080f001800390400e242411140340c0c0341c0302ca0170040c0380070743d40e6030b008078844446946420301c00301d58561070a00171002c56500a04050034a81507441d1a00e0b074688821044451586e034000d0301000901c1a80300a000300c0054003c3d12160000100c081c050300c00040030b4824a4209404000c00441007c0c15537442e4044000001110350b2803004841c07400c00d801c0b0307004c2e600101d8804801041940300c143c100c1511603d041c8400961035944015501d8040d038069a032854030705120030b10009100313002030708002e07006074440040c0280440200d03200c515404101100ea0f08400140342071a1000c20514024015591303003042800c0740301c0301107030310390203a5034845041000000c0c0292510803d80c01030650620400300700b04c1c0303401e01e034508601180c0d0800ca140002c01c44120009001202103000c00c18401401000307421010101415070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 526024280 1250 526023030 526023053
    0x1205060603160201021210050f010c0b071d03060a02040614040b09150d09050309280e06030f01060602010f0b190b0901140313031e0c0f08071b090b040b0607 69
    0x5800f190341c02e02000c507075900b04584090080e10b0f000c00c411591410710f4140001140c8004510381800740031b0b22180c001403103190207268040080d02d8482004001180d1000c180e12444c14101d6161184e00144030142201ea4010011104036131540c442c0c1015042c40c0503018003652160f40716581080c409030340c050034052694440c240c0b1a0380744071b2402881c517001030111880c644054400754004124001141004c0348124240704000d200c80b0350406100f04800790030101806003110104a24000c250b6603281080341042c005011f400a201540d21060028002c0c248110020b0f682c0d070600c1d000160a09113030400ca002000b0510154040d141051b290550541c01104164104000d07100e8403964082948040c42c003450319084100280c58160600404240001e44041d10201a01083d500819004506d032894190b000b2030001d6164010f04140744075018802c0003604807151807480c0c0c1000341e0702d2041e080580d00c49180c20403c00c400c18050100311005141c84540041040101101040e1001c208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 526025530 1250 526024280 526024321
    0x105060904153012200a120e012115030f0b0402030606060307020a030305100b180316081506010318030f0216081002090f0409030f030e1203010b070c0906060f1205060603 75
    0x1404990094040e01c5868581d0f1b429041e0348a5116882821145520503903c48080d1824030380382c00301c1c100c408004200500d0100880545036602c60864600d10b0380041404021500900310703086c0c45066041c5007511901c00c6400f203100b809060000b034400e14001e02945d01940055005000e4240c0c41d6506500922010740540a458414900080c071100244001c040c0707502c2c03c0c0701940c29040403400b072601c2e1400710041c2c40034000343d800040c850384030005204e920008a1101040040d22410010780090461003400145580340211030310516030080c428501c00c1d101542158400c00e0081000400205503005400300c0e0707001131036000034084094000e080b040900603c0900c5081c02d010004045030340e9001c040b40401c040f0300b824140320743c061060101c084040c03000781100d2018202c405d405844140140001030102103103610900541c1e0300c01f030001e080d174200100712842e100c00307004c0d05072180384250400141c004030700202042c0c1b1038003545d400b400015040b98207549411203907078400c0385804c00c07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 526026780 1250 526025530 526025567
    0x3070c0c0e0c12090307020d0215220503190308070f05090402040303030b09132d0203011103271c020a0615050f0907080105060904153012 61
    0x50105804103060078480c0900d0ba04030019a072482e43c1507040080c0c180c02800e00e445900240300c400701584558031003003400303a4110340c44031001400403441d0351140030f106e81c045c42055444070500020900c600d1440f050324401c40c1291030704981000104196410040c00800140050000c00c00250042101100c1d04056040560800d01004081001c03030300582e02c1900003039141e04444000741807802c002070b0407906c02820558801120384a81c0e10562101c64680c00115444217000610075800c8110301c5441e034014002d01c40c0140c0031200f40c8083c0c000341d540e02044103101f03225030414992411100c1c45515281e028140702c1c0f04441211040780000c40500c0f080d801074840210004101d4413070900300c90003a0101b201950b040c08203000c802c4a00da2740c2140200d200a06000289400c004c400741112001c45e2484e583e0308120000c00e024216208102001c5580100049a1200c5003c1103c142014003040d10452a80100802594040700c1501030401081042d182503114401ca07210345406840c02e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 526028030 1250 526026780 526026803
    0x7030224071241070906080403050d0605030f06040201090902090a15020a020a08013c0b0310022106220209040204030c03050312090609030406032004030b01030c0503010207030503070c 81
    0x240202e441016285550f2500070340d011110b08030040c032002c1190010b0702c6207071175803605080ca00050314000e000360001e410700c000440c00e01c2c0300c461a81c0041000d08005030564a00320566400f29940348000c0e1000c90104485c40d0001c00d181c8118402e0350008400280b407001010b2618a0021740039010058941c00c6010307854031b090242c3c860f10226401003001e00000101b003003860000303103200103c410302a0082c41d079900c2d0908480c4180c9150b084480d02c29040020541c0d83e11002a1411800082080d00c29002056002c51001c0348011310b110f1110708a40f00c10180e55000400000030140001030194401c40d80c600c0f502e40354a507000e000c510b41d01400040c0f90a490352038030713011031619031703c1200c8a9100007038154560090203d40e40d005004100200f0035800c0c2240c1564690040b402450101030340c81c8000d142e07400c03003030030501c280015003141590f0355038503800e2140c3e07003a100340030694002c0c520201c0014181814802c071250f564041d59824115111290225402c01e032200c01a40c4d00b1a0b0034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 526029280 1250 526028030 526028081
    0x910050415050408070c1d01150c0b093f1c020f18010e030616020a171317030304030516020310230f0c130b070302240712 54
    0x10b01c600c83c02503004001d0760380c0320b03851441d09000181240d04014100321444000d620201c0136980c1c0a8190f03014405851700c0407080e1801120b045e6409100a000031541400f4029014804520031a442500d400007103202d40c006005401058000c0c0e040c00f034003048503030304110715030090350140c80b42002c5891544a800c02d0500c0101c01d03600010b414109004001131803180c4104c00000c1d404400a007070800310b8034100000300003500d401b001060243c00c003000210359500144280300711108243d1140d410000794029020444050304030800044203400381c414041040c04104542103503225201008601d15521568100c5498120a11800e19600c0b6a4050390050b80e05000012190340a03480002e0341c0442305d41030b1511400603015100088030703024144401d040b104081940c0c040d540301041c82d82c1d0500001170a044200c0c0b0b41c01715510722070100d030000400d540868100703e041c1c81040892000040750b02d44c0d18020006440103004a61054001c41c0019032581180d0503054404d0746013500c07400d50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 526030530 1250 526029280 526029323
    0x301050d1416080706090e0f06090c090612040506010506030c0a0c11040c080a06050a081011070f0b0601230a0c08090607080c30070519060e010b030609100504 70
    0x2981101103e500321180500c281030380710541d40002c1c00c500804011500308602285240380000c2c04007401000d03c3c40c0043d20b80281d0408445402202400c100d5a9204504440040d0389081c0c2d400c8401c1e00441c0000111703490680c0c1924020041180c01600e041c9026509440e0b0100c0c80400700d4192205e802040000d9030345110368140d541940d1201055440d05407001001c071041d682069120300c074a80300a02c045200080c00070040c6034100000101001946070740d00280c06155001014415002c02060410611140c2c1600030307102030300d072640f08840c0e800007000da10160b6400c0040506013889040001c43c8501d44415481d80180011841c04000380c0210f0810783c801e1909848815000031085c0014904020111910380164140d4528423282c2c40711400ac11091021a000b4190106000081c03040502401080c0200c1c00b4140d11140f0b81480d101025200d001c4031076009518100400c1309a003004a2580d01c18a00d29015244600301c4000c807030010840680260703009e03280e045008409800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 526031780 1250 526030530 526030573
    0x615091e0e090d1107080312041b0b07061118060904091b0611030403020307122d03030b0409050d030e033a02040e16032904060602030301050d14 64
    0x26000500100322905a026003104c40903855100e103544401c9040080d250044142d52002450b07289140858840742060300004882a040c3c0821000c0c81d2300025070940520010602c0701e20501051250b03941802d0b14207014000c4aa20404e041c0204810250340e00d042001060904002040000c00307002030340f20724050014002c90300001020082c400d01c122900154442900840240110328190640d804a078a03440107116030070910588106031410003103030301c186109449202c10703010500c05900c040c0c05030f41d0314440000d0b00404d140c11110866420940110904145c018000700360005081e03034100d0040c8100303041154903020511095000100e0014a544e1103a40c020201c0b100e610006410a904064150307204010b40c41040204000070900c01c1095100d801c001094004412021050317003c0e0101d489040724003006c2e0030002e5135a1419003800ba2058038156401c01001d51500d01c1640c0e06e100a01600d5407149002480c07000080c5074054640d4501d4101054035a10109121480410710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 526033030 1250 526031780 526031791
    0xa05070e090d11192004050408040b1608220b070b01050603060102072c0708091c0504031a01031b060516050c100305070f05090d030807031806020903010615091e0e 72
    0x384440c03882429444903510f45d00c0b400c01264100410f0900356500a1140300e14803c01c2d0f02c000c40410a19180020000c1101c9400e810014007541e81d400c0c00750f81110540102a840c0c0440e405200c041120b40c154420381e142181c4c40600c1e0300541e420041000b4558000900084c1144265034010402c003404018114080c0a046e150401000502d503041000030402030030003040016840810101da01d00045401a003080c286002e4488100a0000c440c948a660000340004100911a466050039a000941201e00034980f0126040320110020303202c9080c0e10902e40020824030140340c4280c50502100412031088040f6449000b01f03a012030100352030b00b00817030007090b076aa08201a03103800c03840171030750201c15143c228070f0202101d00084041d508024050108005080010728050007a0b204804846800d850810105914a4481e020f5485420300301d01039401d004000859400c010030302e1980c4942610360905083c24038800c0c2500c105425071400b076000c2d0341c180005000c80411409800341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 526034280 1250 526033030 526033043
    0x705030a29093303010c080906131b17010e0102090307030615030614090c040b0a120c09021b0114011d071214090c03121801030605060c0a05070e090d1119 68
    0x44481401305421503d15020f1176045c80510340420044031801305a8503070102d210b000d007004600e6582483d8401031104009050800c80f5183c0229000511070301882c4002d103103800a101107078204d85034070300385d000350210b2941560100409000040b07094000c41c0014190352058030000c0d680343c6403001500d0482e10f04c42e000f6843d4000f8000d52880602c040d20032040255400d1017100341c00c07404035a00c51458880c460041d07506000501c01c001e804062800240002e440940d01c500b500000c3c0144a041e10340112000d6203000350072076000701c0c4008024105c95201e00820b141c000700c40100715045a00401103010000c0d442c54028030301d00316109000403010074100240443c40c05800d060b280c40000380c2164841d92114480791445003001e03080700d120914140d01c038010b01e0300080040c0c0240c84c1c3d5410241d88400d0109a14802000c0080c0040c5000c1c058001c8590f510741d24100c0d0229a80c064407900030b183c120306842c2001318040c01d803120354000040102e0f07101d070584e00340080468070114011500d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 526035530 1250 526034280 526034371
    0xb090d0b0a0c17041502210c19030506060318150c0d0b040b0f100c080d020a0318150c0e12060f071407290705030a2909 53
    0x129900c100c020100141c00f110b0b40006003000e4580c1c0c0509050482c0c9001400e80004450080151522540c001c40103c1c1c0d05080045c05d0103040c008040d007000314000a0303003040c0030021400d2480383c060f00340120005411303907185464488048051001d841024810b84c0305002c0d00007840c40d0403e600c1da201d0748528007059101e00c248105030041d6400780c100588a2800c0c00c0c105207443d41c550304841c0300c68900710b0356440322103a070a100303441d40f0350303940300190848501144001c01100660000c11054000341c0e010000c091712880040c081d2510498007901c0c1c0b23074600c1102c0c4c0c58606a0791004c0d6640380079040c008001000e0174002201c03001040000038542e0014014409072225400540d60018002c0c2008001c600c68441081d00b240078504004e0a0050a180904265061180503200041884607030a19a140407140a041f1303600c2070ba607501c44103251141c80034040c0507130140c0c0000a07a009000782c44100c0a50704004600d2000340400c1c40c1440d00d003245603545814031011148110300c00808048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 526036780 1250 526035530 526035551
    0xc01050a0f05190518072720030415020703031406030118230613120804031e200c0a0b09060901050f07050304030b160f0203040b090d0b0a 61
    0x10344000c018078500711414074007409803602644504411040c09000300055542c0c83d80c1030300f240c51840310071000301070003100804103030001c08074039032203a0750f1003010103d0722099082d8100045034214000b011540b01c04418498402009800460b000340c040e4604002440038000023000701c0e40300103c1140440e0f42d0f01c01c80c04007001c060400c2541304008400802450180c9550704040c02d41c002401441d02c203410010100441544281031002c2001c1c0081b0741c22464601c0001001c402c01d950706035005036518207407803a9180f0a8680a114562585c0e44c030b084804800c44507500005074078800c01c28850350b03a14240101c02d40c5c0100c2c05040a00c0801415104009000d2010607a8550040c69020404000880c0141c0703039030003100d035414800e1074840d565440c02504044075001d10306008140c0d000015000007800307a124102401500e000024020311b0004040980c1c0e4a4405d40308400981c00610040082c000d0384405800c1003900a00308655200565641070191a0704461100751a41d0b100700801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 526038030 1250 526036780 526036801
    0x3040612090515091615030f06090c09081c14090414090706170c0909071206030605070e01030509151026010b1002070e0c0c1605030105090106050d020904060e030c0105 74
    0x9041e4800710301100901403c240c0e0252039603585454030340915485a09051344000700d580207900900505004110050407602f00501d0380400340300703c01c054402e14100080200d10001c4d41080c003803007602c88131040300140c8500c212031f40005180d6580540e80c0c020055404c41c02d00d030710b03520414403034015100c9141080c030040c004000b6940308849502c040402c008000081800702c815001d41181c500006a40b0303000308032448081c0f10001c551680c103000340001040000c1d00303c280680301544400300240f8508004500b1540200c440200c1c0c1e43c0482c2e05042800501a800340e0003c04a5104c0f08801c1d45908a200703008640201d6401010315103182ca0500d49800e10403e110f1386800c480e03200342c400036000b000303642d5121409035103000907084010807001124030044034540215042900d0a201c110144018070000ca40b2421f03009500f0940010b18128042c0703c1d12041c1d0b28010941c00b6040d00780e0302804107440c070003013003201c0880d82c541c0002c0040e1410400b50001c105400000318007071511b4448407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 526039280 1250 526038030 526038043
    0x2030703051f080a02121207030e011416060504290a0e1c0305070e0d05030306030c0105091305060301021b1b0103050c09060a020709050a061a0403050304061209051509 74
    0xd1000b60890800c2c4010280403030311302031031a0122440d0100000508445080080020080c0c02607500000c11804058000304656842e60003600c4052a003480b040000c01a445006409079801c1a408808000500154041c1d030708030b03005081c51086900002921500c8410500700200c001042c1f40403c09051424042c06048120800c0581030088a61610701c809450b880f11b40c005041e01c0318006110355201c1c4c0a203001c40c0d9801080d800740d0b00e04600b060340d00c80d4400e42e21940a8011700c0c00c4440c072540141d003140c5129001401d08008040c66502c218000e042c060181540340d502000700f130803141e050200e40724a100302e19001d0100104120443c0d2900d43c1c00c08070700c90506040034100451100f0140694810a40544903661780740700c800f000324201422904800c421903d41010b0260060080d4898000ea800c01c41000b42403540041402c440c2e80190300c0024a541d01c1080203100c40d5200300903a00300d1803030384040132494010560311142802030300086400c20074201010464020801c0200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 526040530 1250 526039280 526039321
    0xe01112d010f022107020c030d09030b060d03090b071b17100905060f04021f08010f0909050303042d1a06010f020d080702152401170601031e0203070305 67
    0xc40c41c00050240040d212804e081c1440f0700d090040c030000d40124002c1c4080b03600305034020b00752404184162800f4002c08180c1c001500d8041028000408508040300c08004880e0940c03140040549480c9103190154001c4100700c40f6003020184087c61b000703030750b10790501410180500e6180ca09010440c940340807800c00b0241d1180f42000407500104030049a00c170341040448285e41040d1303455002181d10305411000c620b000740070300c0c5000712169600a0645040e20b035401181c0b8603803555800001305440d0300300030280c41a00100b002c500001c00c402d074a00c1200c00c03461002d900d210543d441e45800d03d07040c008117840c0c0d41c840300201409030205d000303100d50208090a02c904035007024013000b9034801340344946100380080d50700030824150007004400d03041010764100c440103140085058242400e07000d4904429403200422004a60007501505208408411040495514880114050034070340691401c00d60700303151204840ea40d58001140300b0000c507100842d15081c1281d0110a4807400c810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 526041780 1250 526040530 526040561
    0xe06191b08030112030908030d0f05011205060c090a170a03090b030c1603110f0a170c031813020a05030601081807051203160b01090c020309010e01112d01 68
    0x20032030001009401500d05580b8580303143d0034803046a2078191009a02900002941d10012940e10709080b02504083c0c2c00651020741400507980e00c00182c03030441d141040041c07443d000500007540d20202c18010349000b9100800c00c1418643d039442140c03040d552035011b600d198010401120505400c20712000082084034112407551810b06540b05481c06148600303882941d004001406051180444210701c404201c141c6418010341e034102c550310140440c084807600d8284c120905114114025103104000b510050b501c0c0400204000c14400b49d41d00943c3c0e405030750a446400302c41a0340c4080d0903030350a5a181c0c140d0300d04044c000035040316801441c222020490305c3c51480c4215002c503081c811a03c003030b140d400301080e04030542e41c1940120802c9502c1c00c10010920800d0210700d00310241280da925404200314464014203d0b20ba21421401034042018403204101c65445a13402c607075000202010380b0315218180d01c0300201c3d803143d03900c00c5110f00300c0c003129034603469000c0c0300d180c140002414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 526043030 1250 526041780 526041827
    0x105070b090c150c2517150a0c03140705040e0711032a07050312070c03020907020123010312140706110a03060501020f1203040503070c03050a0b061903060c0e0619 72
    0x90032841503101501400003902c0030fa172071b41d80e20840b08200a048000309640c28100b28640a2000e00042001030f11180000c3d0402c1400301081f01f1050035140900e2a0303135202c0b480c0c1030502e6404000d03a00041e080c0002c00c200007540c402c08050500141203405640c60406410960094080c0c1048001c010150b0140e003080208204564001410540701917a14501940b101d09e981008954042e0b00d0b40081d402841c5c403030400c1234096040d409900e013004200c40680e51416950300b246100700c024000203002d1802c2c200402c3d00c8038082c4002c11203d03182c01e101d40d403400615030b4030f603020741d0700d281d005160014010406051050300350040502501081c4010291070070803814681c0d450085a0400000540010208040c040240221548a500120090b16540d036928000b550380b030f04044103850750640f440c08203e251601808407240c6105403110301815904684411000f040b081c9584002d0114180030310301c1c55214070001e0b00420b0740c040fa0a1040c09001440540250312442038a00f0075a40c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 526044280 1250 526043030 526043083
    0x1110312041103030904020f040e0c2d1b0f0f01140a09140a0807031806080601120b040c050c010507030b010507030e0a0b042303010b0105070b090c150c 67
    0x203140954029000701240340007256a602080c254402c80e68032039006400058200744000c0050b008108403804080c0200ca01d94440007494180c0c0036101c04600c4c140000c1000300003615220312103610960105482c986040003000d00c0c10000c00d5540398954803134100000f0351482d100c00707200b00c000c40600c05001b84600d4500510018a129008003490005c030341d510019428000142c505a0359002c0c1c41c1d0403500210381c1c42c02d00d0320b040e411411007140000c0c0e90b41480c061041c100d6121804a4a040e207c001c515110180151094081446a8180282e840d509511255110300600352500001d480c0c0c20340c4c807515500d00f10f0035550010a10010302d41080000f00071a644001101c06694140c500000b021214500140d01e91410758000c001c040c5000c00c0c041102d2100400b510040c8400b03444a941d03040d85841403500f42c40198000c50f001c180b0a0250707401240c440c3c9880c941c0302c28124191900a4182d2000804c00078009004140b2140c0218500100036810054108102103801d220424003502c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 526045530 1250 526044280 526044307
    0x60506032205030702090702071401021207030c060b040c1d090f0106140706021305040e0d080a1a0a1e09050f01030807060b030a200a0f1413020f09011103 68
    0x800061000310071241098028848140700b80c50300c0f117600410041403170410000080d0f5408460040704a8030b01c039165081c8031903000143c100108034000042d14140341c51a1070a6034031074065441175600540b60801501030b60f41c2c5100b83d0b00c14175955290381c1040415200249080c0d10101c480d1800342a510040c81440549040c040341164503504d81014042e803980c80b004e659000352203000300b2413800403912650101048085038103403642503404010703110481040035500e400000100c4080780c00080828136030407564100741d050958484121726150700d000045401c800940c3c0c04400c2039a02c0104600111000c524054001e01c0d06c0a001d002604000c502558078040600c8010a4004000384140c10002d494200c0c90b0b95000c001e003500e004500030b0518070440ba0140781d50540002c400360300c1080c68034044002e1819644404200c40c3d0f8503041c0240442e00d400d040b45071036070041d2041d480e80b003ea02580000c110580348200c2403a00d8194010000d0018016580300c52483d030000c0c4075030b00c100b284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 526046780 1250 526045530 526045561
    0x30b0109050912040f0e0f0f0105060d140c0909181b010c140f0607020f190f051609060f03021f090f03050f061302010c060c0909020408010c0306050603 67
    0x920160018441d222202c1d058500200e00c500140411004180001c00a00492211044a0390103000604a40d02c442070300070a00e10458142c0381030018100140601e0402801406025490030b0b000568201e11010031542034100300c1d02d000011400194190103800c00c0303021650003458104071040304c1c0e61a034089903101c8440b0084080c150b170716000e84003000ea01c214046100d0580001d40c80c841801c49401507506c0f4081d644100c0d80501c01c0501042c105072000034035044c0c0d41003e1740580f02c000380141080b1403601c2603c005540703004044042ca00072440c00d125884400d00c00500444032a49842540b0b010307122194810f6084604180c410405038842c20b01030051078200d0080c000c006144c040c41500c0ca603005410503101180200c070040100500000c00c0c0c4181207160081701d00c9070ba070301500114025040b0300000d0008a0310150750700001c240c2c1d046180724000c9810700942c2151994015412a04141e05c032a8036030707460314a0513042d070390580b02c1c8002a020980f8403c0c13644c904000030b070a4030030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 526048030 1250 526046780 526046789
    0x21c0e01020705100b06090402030f0603151006051b0616020705060a050f030414011107150c050f0304050c040903031a0a2d03020409031707170133091509030b01 71
    0x15100c042c02207171943c50104543c29440010002c5446c0c2c01c2441405413000c6088901c680a44103511010f6038644261032135520a00305140002000b80c2043c0b821591600703d40401075a504c0e1544c0c0c5884240303000d0001030320400600b5a00000340904410007440d18540d0380c4080d008000421900c06c603682d0000480303c4d804528285a5076a485914082c85004100c84020f00742e941703000b8860080310706100007021098043e00103070640903543d04a40302100e000e0341603480410000c002c40c51000c48800003640d0720034014800e031075407104100041019030f800c0c03600450000e03a07500c045100080800403101e00740c0106071074030f1404038100071801d4642418110401140b1541002101513014414800c20203194054014001c000751460f0103440c0078101c2c06046a03c01c085000500054410801c2040c146003c19400350f03240d10b0b1003109110050f0502410342c40d01c10b10008090400004d1101421614003607807a03105013807070b0000c0d402285120405000402c440034000b0004100008090750544 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 526049280 1250 526048030 526048063
    0x3050c03150118090302210306040605090f0601030b06040312080a1413140102070f0620030f0412030603020907090f0801020f190e1c05070518150a09021c0e01020705 73
    0x88445e04042e85403ea01c41071140081e1500302c83d00f1340e440a120080c500410050ba01403080303039154010032078414405c0741c104201c40380840c001201076220790030280d2071841c0606540d01d0142c59440701d224040390740e4503080114030390304280b04031103089118802c4912181552807130142030664801480f10036101004d029000004000701e420b14080d4115420300d6031080303c03100c4444541c0382c0310b0050060b84031742a0301d02d000a02203940e85000a82264030490740400c0020055980c1d0f621076480a1007504844101035035510080700685802d10900d000301d1a44e01e40d0107026241031354849000c00e00ea0003402140c0d00501000f0b0001e480d942c15280c038910f00650303c0900c0ca52181048403010351a80d005a0312030703880807001c41032114000c50310180600510554605031749500501c0000020b50011100f1300411400040c103080c81c401500d074200700c00500c18203180d036550b589241a60000017001e82d00d031007586480100c1c2c004e288203454500d12a01d0080d81010120340320551100707640314001404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 526050530 1250 526049280 526049291
    0x30d0e03100213031101020c0d2d06140106110d0809030d0606200105070504052707120b0a08070e0703020403060c0f021501081207060e01050103050c03150118 70
    0xa03603a060044000310080300d1011034440b8025044407a0b400f907148001c0e1401242d450313900042d5440428032804140d800780600359200d910fa540e500c1a650781206a03110000460240425009003621040f0200e01941c40803d8820780c48568108400042c0d01000921908840d00350110303101040407050101c1c14148001c6580d0703207001890a52187c0c80e104101185080c001080440e04111040d40c04583c1082c0418841c98a4032502e08851041c0e448034041a8140010062441d100448280751000f5441800314a4580d40c140c808000d02a500d00c008603003881d08507180600e0707030700c100039180404a44441c202c0c1d180c61500381e1035480074000c45101240c184000b802c2d640c0282c040300d00031503000c601004043c901d00710040100a00b840c0d804014010030b1200345100c00c901a0290503034800601800404d400c8485a40c41c503031000c0411601281c49050498020300c0030b224440c001c502880c003400303400350003004060420a20ac034800102d058400010f01c804402040c00d0340c0e80200c5881d0001e030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 526051780 1250 526050530 526050557
    0x3060f09062c06060d09171b030c0c04020703232203020d061808040b0a09090b010f0302090301110d090b0c070507030f0809101d060909040204020f070804270209030d 73
    0x1a000a0074080c0505c400741d00d07a44440c00d01003004014a21072301040d660000008102c0300c2e1203128070040d071080d941c8080200e400524040c0e00800d880b510a0030040c034038400310700b0001c0200003500300c50f016003c80414007540c0103940c428100d02d105401c1803500350050450740042c6543d01140c1014041a03034500200e200c41440000044401c4d411547c2c00b41ca891741c038080c01e01203503c0040d02c43d0016020131030019850009010ba0120000c05071507035024513618000c1200290070074100300d9419929030130000c0303841e16000000d20083c0d0281074089104010741c18004801070024011041d0400c08003c5500800d50111b564000c0e80c0c0c0c010309800040500e07003400b006500491040c9980440b020203504207a43d0412158854400910400c92500c40c54030100485409914141c0d90400d034950300150051401358028030b542500407041904114081c0c50f00c1c0145c0d040b40e04400041e4500d000b11307062303181140e01406040304a854065141c2400f00020a444590095a13002400002d00c540c41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 526053030 1250 526051780 526051807
    0x50303030a1817030403030b090c030a0e010b04020d06050405090601051c110916030608060603030a181203020a05100501052d100906080c0309030a0f03060f09062c0606 74
    0x500d95004054140c1203105003c0f000000e034020b440171400b00e0318182c40d010b4903042c4000380910441e5a4a040e60859968210801c05010341c0210b4601035542d46001a440f0b41d55031001c1c250042580c00c0008896040900f80400c0715400307804002c1c10351000004102da580c0e007906500b001007080d011301c2c4650000b0b10780fa80100c10071078080c541c803070042020084040c200c180760700034000c003540d000e12219a985c00903580314030007510321a070160001c00514040c2d0340500c48601000c2581c025020805d941c8100c180700f84000c40c17a080700160006100c0000b40704040058510040740034200f08042d501d02000200764869030000c1d80805807071b01d000900c0341b03c00d8620400c0c24000180c40120701c546007004c001e03c022503a0140c040401c2c210310200c0c60164580c425a072054420200075460440b0f00401510b031454181096805c1517250000401c22120b00640000200361442c0d021800f14140400064813038440240701c403c8010000c12480065200c8010b44d2f0050019500103560b01e01c03c44921 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 526054280 1250 526053030 526053071
    0xc03060c0f040e01060c0b06040e0303150a030f030302030405150c04140d06151802070503040302150c012c0d09030b150619030e060709050f12010f24050303030a 71
    0x103800343d01060000942e040d0446904a4220b00c80e0304108100e55030402000b04456110403c40c1c007036807051000441d444420f1546090692004203d5080c40e0b58030b5942700510354000034110000f0741c02006200400c40c0810900d00150030303e020f44da18038900042040f0840c0518031411284903580840202c003a290f42e141c24603002e070440014003c1c0e8071424090803402076248140081c10030a02e82010b4114158400d03140300c140e018000c1c40c90310f40346808024114440c8203004011160400032001451000d02c1340720384480c0d001041c10751260254040c803e8081611503010015082083c8010b40c02e030380410b0780780130780e5484010148180c648858112040c9085d210301c541081001032a00c80c245051418a4040e001c207036014400311914244032520740205072441000f04480720018480c030f14101c1c5113142c0300c2e0f10241441040442c5aa000d90a451080c1003140e640d44e40e40ba14000c1c085d00c0344503505141000c4854a5002c00e00d01070110307030b036884004c10b00f404466036491490380002400d0441d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 526055530 1250 526054280 526054289
    0x5030c07110d0609111005070b04020102010b0904290112060e0133121a04080904050406090201090902030c0a08220c0e01050a03150e07090c0c03110c03060c0f04 71
    0x100c0d215142c15160660003040307454000c0d00c9001442d0f003400b0640c40c00841419440352290ba86604200c0340750340380210351130301600c100e056549900040c00c60fa07c506248501c40d034058540050b6030300882a0f8090305003070b20805140507100610062282d0303a04e0341801154180c2c00309000841c1850005641d004080444181c5003c40d06500c40b46c0c2c06102c0d140d00d0158401a074407081c0352107940d4030b00d0f00050080c007004c0140f41190f0b0030b90032140558000da40310780c02400788070150300c0d0500d0100020100e8074119030031140c0710b98500c590019035900500c401c014103d241e80071440c5003080d03043d941c614013404001d4400c105407140091004000302c000d65000600510705018900d80602c0c01681c07113200750003651802c8a0f038200000e40352504040580c00c4075046680001202c00743c11044001e4074601880101c1807060301c0d00003038503070310358481c0000d01941076540b096940e0785031800600f00c200d00c2c440c2204543c00355658001c903680208a85030411010841c2650700d000540da6908140100e030311 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 526056780 1250 526055530 526055539
    0x709080706270807050607030323090c1005030a0e035202040c050c0706020d020c0303090a0e041505091c0302070b060105030c070c03050c03010509070605030c0711 72
    0x300095600d40004403070000c07020105102c2142e600000118001c1d40c5588503201540d40111801c000c1e40c1000d0000b458000c2c00303460702003804500c00e102c03000588000714542c04414281800c00c0070800050090007078030001110142100c0f5041da0780107240740009894001c11036520034444601c0801002180c0c490700000039100c41c00021100070400d44094100051043c0c0306030003091a081c2000424103d80c3e4114051000c48807441c0c0d002c3c0001405164091028003c08010140c0e00e080704005440050499a000340ba01c000000030090900c0646001c0500940c410b0203c102e41d81d42d8a90000262000c2c140440550343e03690030115000c1d11000710041c5139910301405c2c0f0010300d02c0801c018004c001030800300f00d09050f115800324124401c45001809040d04440416850343c401d800454010014182042c2058410b40303e815268400c0d520440701d07544090607100312800e0078040c013030740801980c01900002e860036601030000e1100900c45000c0c19000503281082101401150310020300141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 526058030 1250 526056780 526056793
    0xa0c30050406021b3f0c0706030f20030703090c060f020d090305060f07050c010f02090f04060506180315150a0e010f060c05010e060408180904020f09070908 69
    0x7040c0c4000d41c4681c039900ba109101d40c0e507031185401e0000e814001c4c507580010301070310b01c1c1c3c003c5d01c90a02c41d032031300301700304449001540c1c02d4525904000181200a090402800c0e26603d82100502216219600007103818185076010407016034081c2c2c102000305644401560740d07500c501c4110020b005121004003000030504d00860039950102103a030219600b9000c032400c40c0c02c08074080e1124a11440004c1c0680e00003000a602203210707248440c0c1040c110b091050a04044106203400c1d1070301c1e0a4280c1d081c69010907010000c3c07900b0040241c8005007030700c04110150400c1c011036a60700c5102e10b010300102a0203000842c0b62400c11100100700610074a000c100d003000c00c00301c07021084040106205201403400400d050900300301c460b0490f940d840d5001401840c00c202910514452101070f29603540e00e0787c1111641400b40700c0309220310b120b03210b110381e0348050b08482942942c04410045c042e0100508000050312200c60765414048215103000c841d550789201124036030b6254000800500940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 526059280 1250 526058030 526058033
    0x302040e0a141c030b030a14010b01030f110304021e031603120801081914070603090c0b091003020f1314040f180611161104050a0c300504 61
    0x20500001491258944101c03a002250030b09640301c00e100950f035920300050955812160080d400440c003000040e0981d5282109515010318002e03015200c800942d440e44c0b01d48141e5a4036109054801000c03c004010b120894088010755000c0108024011302000b900303414000725550080308002c07001002c03920b2141d0f201c5a0962403401c18401160344a010803a0030381150b0184090a06813900d82c030003420501c401d4420f500c41409040380581e40180ca8005c41e00c562041400702c040a42407030384001c10300019501d0800750700348040c0c0c01b5a0324a00284200c2c0507980e41d05205444c142814070700940ca9841d4995141c200344640d00c122641c40c40f40c8040090700684661100b1811481200c0800c0a00254807401f8103440c641d0000706a462400008580003581c4c070b40c00710300040041044075090684112910350340f0a100f000a0745c0602d24650880b001f803400f0f004e41540110740c84018815610200700c0500740c1c000e54110f9024456440903405104480d948141103d2821f1200501050030705 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 526060530 1250 526059280 526059283
    0x150304050d1b05031903050a0209030604081b011a011107060e0409060b0d03090504060503120306040c05090307030b1603060e1801020d14100605040b0d05040303090b07120b1c060905070302040e 85
    0x56080185c0460700b000002404002076200390ba40808028020707003440c0e6580d07510b41640340c4c00940100310341d03c0440100b50f0440c00902c542407108501d00c020190b00d0b180b450001d42660400d1000800c584d114420611815070711501d000c2042500ba00c0101d004041450800c025008001140d50001161881d10f003e15500c4954001102c00987d0104460358551080c55142c0300c80d102c0301c1034180d1040010510078280780d0700c07280c6140e21b50b01d0042c0c02c01c54890006400c04903980c0c002c0e41c0ea02c2d841c42c2486a0240d582d840b20040d050f02d030400300881440c00e004c040f0b1504004028182903180e070440003041602c2901101e080048480e0104016441d081804c42d000e8070030349061400e45400f400105005000f8002c440564403607028040c200f041d500c0d01440070b00b000a008804050b12034860307000142000e400c40d03010b510303a515007914008038003000718112001400780a110f03040c0804c13541c080c0e1120380b030800c1c03000e5000b40300414018818149680780c04130944c0700035001132900841d000c80c1e820 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 526061780 1250 526060530 526060567
    0x301020a2a1514070f0203160f020d0503070506090601031a040f0804170c03030903060f1308121e01060801060507030314070216090506210c1905150304050d1b0503 72
    0xa220b040c1c1c8044d0b160020226a01c0b0000c1c03140c100540d10410440c0c5403003030324180d140c0b10940f1448108108142c1d0342e0208251140c160703000c03102d40d0b002003421410404144100b55000c04010002c07c119850f584400000b00101c0881e0360560340e402c4086414008211030390f580158210385030695613591a0401c88403110f100c0d015001c1400f501d034039007030a0f28010048407208400280184440d4a0740341d01041d4401c0e01400c10341d0003800070721240c0001090b83c4007511161030031100742202031408403000c03100c3c0c0300c0000a01110b040c660006028694001180e036040da82240f5141d82c4884072031900340e008104100804880703100c4242040307a01d43d03000410031614900c0000740c2842542d1340700c104040e280141c401c194401c4c0a94200240c40000c2d0304181d07400c00b0950112200c0c456843c01140c0c40000b4159140c414160700ca400f8010350a080e08500142f8050101840c80c520702a1101a100c404c0052104104250740c100365020f00b0608079a00e0348a6000401d5944e40c15007a60450744507036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 526063030 1250 526061780 526061801
    0x40c0602120f03070f051606090b0c09030601031b050319020a080f060103060209040204051009030501052a070302070b0a090305060709150f140409020c010b0301020a2a15 75
    0x21610380407200c0d0101c9001a65035030240351080c030341180c58044060b41d0503610f0711074040c100541800358612142c2c49441500306a0f002e014002509207003410144c880c1c1d4030050103040d0441d42041500b4080d01c000030182d04481c1c0003c0281800203840d100e881c100011035200315414480c60325401d00c164031000703103550081e20844085586907a07500115441d00000d00c00c0559036000040100003158594000309900301c2c2c01040140340503120000070300d80394220410750340007810407001030080180910925400005001c118200a044e240c02c151400118007500029601e0204080e02018001c1040300080d0050010054544200740001031400c2d02078841524203101b0309010600b40303809000c100b01500e0b00c9092940b0b0b1081c60100a036492444101e031b020400c62136100340b0300f402110502510182c214501c0240c2d0b5807465245070b070f00f92444643c00310302c00c7e48100140c00c10103401100c5422498907208003e00106100c3c144845003000c00007010f04901d01030b001c10b0007040d07400d0348041e0014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 526064280 1250 526063030 526063033
    0x8042906030115030b1618090915020306030a17040305070b25020609060310051203071401060b12090c030a0f0b07140a0518150c150603060708090102090306040c0602 73
    0x40010010b903002041c0520001c4c003805c11102c04903012628500140c00003802c40d0030450f0800c00c00703911103043d0400c3c0d54050300f48035607540c40c441d04201c020121445103218200b001c0d0b00790309000300045e440f010301c98070041203504541c40181250102c0d4003503600450b084400c0d40c07490b56403076400000c644e02c00e11000020407590f01290410740115802d030411076030042c04d050b0070480300d1400e101d070b03d500c080d059240280020030000703030984c0e0b1200c00d050020041c038055602d0710105d02d846454040f4a0309a88040e904181d41880010614019640902020030051500ea15503c03072450a00a40320481b50b098040c85040c04140031101c0040e0751310900c503159400443d41e0781d20084800710248000b400e105071081000e03010007440390002c0e00441800c00c00a0307844d03c0000c0c0002c0c80103000d1681c1c12801c0c43d0003040c2c09051400503c4103102112581000044601d00700c1c0000b900d80900400700c001f030144041c04520f03540b000350b05407600e682c8050300301d0324030f802c0c18101440040858416107005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 526065530 1250 526064280 526064291
    0x1020703110d0909020d0b0a08030a091d041b03050d0804120807020c13180b01080105060303040612180f050105012d120302031c02120601030b090403080429060301 72
    0x241000211944465143c3c0d0f5148a164204451000650700c11005030740001c0d2240c14003055551030094120041c05440015681e071129604050154a5035500c1034120615003142180c200342211455640164011308844c050717818035803d03415081171500090700c40d21507018444c450791307044000d0a0281e0300803600039000f40e020745801c032840fa40445020006030412027a0885d5810060214a0b2034402d41c0008038058441303440310101c42c0203642c2c041d11000350800041008650a00c81c1c20b070055025000303107103080d08000340509004d9818001c01c075182d5550074080c0810103450021000164000c02000d000b4955050850282c4020300600e0701c2200c060b003059800100c0441e80c0302c4085841e010825005e8036202c101c12010201c0c440c00c1d02075000400402c80b0507516002d039549104c07a880801030321003442195595010707074010491410b00d498840790181e5552010b1109900c01ea05103404c000d99502c616080b81900f00d588207010001000e01c2c288001e112950300c000c0d00c01d0b00c060b00200070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 526066780 1250 526065530 526065557
    0x504060605090c0a030f06050303072003010908040303051806040603020d1a0d0b040204020f07052817090a0305070b0705060a050606120703020f03040c03140d0f11010e010e01020703 80
    0x81d0b82c200f40c1da880300426042002402d0640642c01c0703d4000b40440d00009540c0303a850011904550000004a40100341c141e01a84001c00320710003100c411405800801000c19203644000061040d8040a420702c44040b80c902c420010800e004000408017914281e250340d99070b00d014020b900029807a1010ba4107103c0304203020322408004a00f290401000c42000b14501e8a0b242c03005980540b041e81c100f502000701150080000c0000c00c46030b485140203103002004081125240d207550440c0007400d401c0248564045035075080800b0484040c003a510756a0346c5003100180e08000340b940010030a0099a00002e070f070403451809040750754002d009035085c0307540708544035045030380c01c40700290300000a02c081001e4900c10f05407039038040079034100186030000d922001801034000305d4040f100c92443c3c6009100708492540320030814003c6500400d00600000c0380070348040901d03175102c400c102ca2040340c120911000d40080304035805160080001010000841d400703584036000503030200e401241141c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 526068030 1250 526066780 526066789
    0x210e03061f050d0804051809070803040806041104090c0305030a020c0307030804121509081902010207020916270f0510020606060702061209010609051609030f061b030504060605 78
    0x1d2a010300c0000324059103003007a04100d468841e505060f100b9440a01c00890961500b00959405400e0100b07505210700c0d02c540018a40f903c183c002031003c0d00f007404204070210b000507803942c201da403100550059040b400c010600410740a04094000d040900c0c0000c01c1c0900407005050f07107040d9134241c0303050b43c001409060341d8603240d200060516000b08810042c13640d0120101c018284201e11050341e9000f029034940560301c0e494425900282c0001d048800003003000d20303043c00120740d0b00003076080016580005980c140001c00400208095008184071503100e81c001d0301c02c0500b081c450040f24144611103c40e012200c1c000c600071440d001c100402d840c0303480d08080e0700c2c440e02540144840d0f0b60b20002e219003600074040890b0401c1e418000010940046005240301c1d21404000280c03061500d484141a610068007091000105510446100382d0001e1200c0c1506e40116500e458811149802c03801000742080d50000f4044900c000b1241c01c0c1c1c107070001c500440c01000148900f5803500c00300b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 526069280 1250 526068030 526068061
    0x9180f07080c040c020f0d0201021201050411120414030a0809071d041113090602191b060b060702090403081504110d0b010c080a02010902090a060e070c210e0306 71
    0x700626401420040074516094208140303110061041e01c05000250700810300e8004901030107000f60350041140c40e0103040c86418070380100790848050001001c8629125490b04c148007000301c40c20b0141c80064140f141c1044112070583c010012207588101e111001400300030159201f081c0c6000e00740c0300041d03155181c09084800407488451241548407603468003446d10005490a4001c0c5400700c18201084540c4280f420070380c0150f20140c0c0d04c08030101c0180c14422042803000a00492044449881e03601ca16014a5940d10010000d000284800040c0351802200002503208408904000400d98800000750140041180c01d03116440003d0030001078810b081c21078618402c00b4804d070f050164568101c2452610181859000b24106885807049584040c1503140507039102d410300310460610b0b0b000158440601d0b14200003150a240c003030f0f049044091701f6003003000a901030801c20321840300c0000084010f9a2410001c400c1c0b40580507200c2d8902c2c114180c800d0140318001520814240e228 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 526070530 1250 526069280 526069289
    0xd0b030c090718080607050a020c101d0406051203070309170d0815121c0e0312130e04030f080c09030d080907031505160c240b09180f07 60
    0x1911035540c0b10903080380d400740d11200207045811011000200c001c0709100031401481541d44003992100b103984040d152140c100d0a190081e001c1d081440c00c0643d02401d4101000d44000101c5102c0b00e41b200001c020340055000380750711035140b80703050702000c0e0000300408503603100f902c59481440d520191624120050f4210540c150498414840941d204100b02540040b40700d003e00000040a00803907807808409a082049900c0040d107a20018203010068803100381900d40030110041000c040f82d101c101e07032900082210030104507002200240f01b0315070081c1003440040c000c00e10305410010000176041c05c00d1004200004041a28981c43d541150209440a030042030394226142c01103800c0040242a804640600300021000959801100c0c00300200c5210204450801400100941000c1041c2d80e0500a2420560300003501c1c80000c100c8106407980560a6a88030420080c06040c6000b102036000c14000100121030000382c1c120000443c04000300d030354000d0004200d0b6030302c80d07442c020f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 526071780 1250 526070530 526070539
    0x201080f0c07121b1109130503041806270c1b0f11030307111203070309090504081605031c152304110a080f15190308040b0d0b030c 58
    0x2d404082801038a0707001c062071051816074081041c035062030381e0007003085800b250704145144040c0d40e02d1600da1032094000c8170180101035619441d9880c01d580344154881c10a900c0000008011a0181507100d9001071074418090300c08445505101c29240350320040d403841c3e0a250103148528648200c8004140385c3c0c04410700368000020361540c0c07191201c1680c044695004540740c0402e07544090002d01105481005400a030303100c1c1070104904001840d405079075039441484154042a880a1610200c99403800001640d40b541c0c1803124240c4245401460303105c02184601c801c02000000a10656100810fa52f04c5a140311640d41e050f15a80088500c00f00380c441014044020f80c895052510b064036240341a10a15003004102515040021080701100100f803407405d4030f400610050380241c10f514500d4403490702c06c80076942c10034500186801003410b5009400c01807206220314000d1604000c000351256030303640011206510100070b1441950401d0a20b54490500091450506800a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 526073030 1250 526071780 526071787
    0xb0a050405010810090204140405010806040203060402090702101d16140f0402160f030810060c0b5103030714100513110d1104020f040810090201080f0c 67
    0x1190040c0340501400c10030340c0c0b406400030b0150100e00c01040103008481c01c208d41208184100411640305910203404c6410a1382000016540403031826031207070741129440e01a46855004901e065a14601d50a800c0c0ca0010343d203070a202c5031003085008981c8002120b0184070780321040d801c40c000c0d912501ca100d40c0328400402843c58045c0c0c4900700800c0c060801410404007008645500307014410645a00115031420320505030f001c03451030340c4005480201e800c214681100180701c017031015006082c0c2c9807284e0206121078541c00001480398210744201c0c090030307907001d5005040981400b103500601c4101071300040100e2030402060003410700034003842c240910b6840f041c503a00065401800c603809001101000b8080c148501802450308500c0c0344501c00c403600e001c12940c0c034600612482a580751860600140c40c614031541c00440658001d6281d43c03007100c255101d8000d64224104d140144584907010f60125840307440b85034000d81e907865164a41400d062100c070400d0320071030414403042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 526074280 1250 526073030 526073039
    0x20102060c03150604180b060315060703030207050105070201140108070803041a0405180a050f090d0e03010204080a051005070f02030301030311150a0b0f040c0e120c0d030c03090b0a0504 82
    0x10000d0340c0d2002d010f900c418140d610745000103100e948180c006c160102076811200624480c0d41c469500701a074165411465414141b041e04814140440c0e082e10607040040d501c02018440d4041d81c0b0803580c08802030040e400c0040020340a850b01072420040ca01c0c0035000000ca05038000307900d2040b00c02403805545070500700f02504504074504420501300c01c904000000c0c99490740300b4804650810155903c0b110705140041d1401d0381e0014011a00b4804408240441c06002003150080c10340c10341840303071100c411040030030b01a01442e84082020701a400c02c032001d008012805400700f6600b20320811240c1d60700179096860001c3d803c0341000507030081c40140700081c081c2100f03c135500060b204407411120204c03002044204211402007540e41c840105030040d0820020310f504030a402c0b10144104038006100411802078070348001e110343e1180d00c441d0440c0005000280d544a80541814490b08490902606160039903008038000381c020b140010740101903105a8118001650350326181c140351 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 526075530 1250 526074280 526074301
    0x2090c0a1205090f0f060f01060315060507020f0a081b120d0c210509043c0b0301020a080f090607020c0907032d140408191707050301140d02010206 65
    0x2880f035105446907040080c0424000c000720440d5074504ea00501d03140c40c2c01c1013000c01d0a04103034084010f04d400d00c4582400701039003101c0c0005a44661808a03142e9040d0300004200c2748543c0881900310b03000c0200480e00c0580810a0324480d188800140d8801e441303001807240048286044011a801c540c1380c000c02140325000c040074442c0a4010071000805408803030b20783e031500440f00404641d001901025604083c099a01c03103500c80328059040c10120240202c400f062504840d0041c2e0004c070280c041d914290307001404401c0054021500c0d100d40304000f8103041426160150320030540c200040b10308400040c000d114810b0fa90107071403100a82e0081c46403015010b00518185070300d80e000503812260154085a19880d0000f41d01400350384080b20300c04580c0d2080c0200441641e0608100104103081c007110240d10485070001314400d901c103421104000312010440d0005900c0041c441219401800345040c3c1c0c2c40301600a410070a403070304200c03801808443c001d0260f00f080d40001d500030341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 526076780 1250 526075530 526075541
    0xc240d020a0210020d1401060305040507090c03020d090c0f0506072f040903091a0f0418020c0714030105130b160e0d0b04140a0305180f0402041202090c0a12 69
    0x7180d0040b0340346290791510000c11383c0c100740107007001e40344c0c1d0389446042040210826801400241010006800c02c3d440392502c503d001d000f181107444e144e04409000d02c1c401c1d41100e024210206040255039440d00c1c06414030301d82e500c070f09024a1401500429035262a9045a6207240d000310304816820383c0c0ba4030802d410600c0040c031301c0c91030b0608003c086981c85ea4082d00301014403980c0e80d0038080f0305080507c050b0320b80346a41d68504180074403052412458810480301a00c44103000d0007004c0041d0b61001c8013a208000d004807090058400004400d0081d103224804484101c000b40a140c0c3c800c0007800d8800740e9098041d204401c4940810000483d000c8501d18103201460101407290103040030800c000c0f8440001c0b910200440c5c100300c14060640104c046500300e020203000c940e400c5840043c418021819a0304890b100c65480082c180e80c0c83d8a03051090308054015925181c0ea090703030640403040300c0307000d9018036045000a00920703616001ca0312010711580b0768526820b90415404002c14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 526078030 1250 526076780 526076797
    0x28090f1a070b0405061806090a03140f0c0601031518140109051f2004030b07020c0306160e031614030a02091609060e1311070f050c240d02 61
    0xc50420000010541440703050f4407850203000144481c3c10007100001180300104d8034150180c21890510142d42004141013000d070350075143c2200e210006200809091265031903640400d1000a220005040d003c58400e0481c1c0c011425004455804407428060342c9044041e8010314134035a400c0c2c0c00080c4280c560742d5002c600100006900713552039494502c0c1c10452105c103c003600c0350010010702404c05002e2000c2648040910941c85103403004c01180500032408014660815200001e03402132080101d120040c100904540c19403d01140c080000c0035203644400006050600c030701c2c403c1c1000140c0900003210071302003002c030b5031621180090080d03001c404182d00d805044aa0405a9240302456001d4000350414003a421042c0c1e0000e82030b0102c40d8080d40602c07100281c0c0412560f40d203424004c0400039483e0104482d00c0c0c182424032644541d01009040301070808400050001c009520054000c0075035955202c45242c1e00c1901600360b00c041c058258400c01c018a121603c0c1710740203000d00744c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 526079136 1106 526078030 526078079
    0x1b1d060c07030305160606060f0807020c1011010e030d0b042702012a0303050a110702060405130b09130636080f28090f 53
    0x401c0140310107420710034045026041294004040800964010000c00600c2d0b100d14014109c45850103a110020782180300051a59000180843d042d0500400c0c05c104600390080444841d018100c03491500d54840010300c500c11000c001520030845038035404911461a503003440121544a1500001c0510807098401c40310a15416102595020b10704954849014104a00b00392a00c00718200725032904014a401d00d07030b05030f00c154098000f0358000d01001c4c5881e03860903000c0c000d02201035032040003003008101070b1404508070700b4008a1018007044001000000a5905074121500700da40a18060302d9000c01065214205807803561415521105204c80030481402c500f405050000501c120310703003018003075440c0c10740b1a80500008076664891104920214901d40b03d01c01c0e10f26400217a11903007806004410500c1903030600341c04040450302d40441c1c000d5a1648600150b0b44 = true := by decide +kernel

theorem cover : BRFrame.Cov 525899280 526079136 := by
  have h0 := BRFrame.cov_init 525899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 525899280 ≤ n) (h2 : n < 526079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
