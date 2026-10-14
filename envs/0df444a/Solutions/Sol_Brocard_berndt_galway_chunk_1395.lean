-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1395
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:45:46.109643+00:00
-- url     : https://prove2.me/submissions/d3fe68d5-08ca-473a-9b85-18e45e3c2c37

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 250719424 ≤ n < 250899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 250720674 1250 250719424 250719431
    0xc030d110c0306011a07080d141f030308070309080d060305060a0606052508040305100504020a050904030e0105130305160e0705040b16020f0616050105010b0c0a0f11030307030e0301 80
    0xd00525a4030316080c000ea0905c0d010103000180d00300c00e0343e0000d1100c00d00c07880409061094401c010425a841c030340001c8000100d400030030000e03001c0f1260b15450980816031000080389542c8018065440c050900c40405446045801c240240c0c00d048807407280712894104203856503420716540700e1000b6030300010054241080007a0f02071264042d5900c0328483e001e040ca01001c00b16200740c040001308400ca400f00700078000000840e205004106a01c03c90b54000b241e40e24151042003180440b64114a100d60300200a01000c40e50161422030f5103007082c200f0301d548200c3d602401942e180c20341d20040c002d220384403009154081712403e00003229086a01e81e01c56480e10141a1010300840c0034181c5840028001c02625011100c00c0050650010f0640c2044000060209030154081114800c03112600101d88080140074851540140020b034400390400a0305a02c3d16100c1e0702d080005070070b41145001e000103202d110a20060301c0040201280da40d6901e61402800d00500410b00612030b529 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 250721924 1250 250720674 250720693
    0x305040b0a0c080f04050703170304121403060f0f04060305010b040c0c02010f030f060f030f02090619030212030c030c070815041505150a0603021c020f0a110c030d11 73
    0x100da014141d000307030b000e4454404550b110592410070103001001640e45208135180000800d4086145c109940e50206405649241500b44003250099a0009808108102c00420340c8184a442501d410007000c41da40d001054600c400030b0010f4001c0b005c21a4001d1604100101f0044154000d014168043e90240f0840340319500550301961040b41c064040350b046036a1602c500d1096102c8418012000700029849481d1a0802860551504121341c12404c2070845000e501d400701c541c139030190089801005101c14080c800700302c400e00d880028010a00e88240c00c410510501c15114020140c00840341c44440b0703080c00e81d40d80c114900c1120032500826036190351005400c6001407246401200201304607100e050b14600409000f00428805582120300700856601d90f010040101016900503031102d401c280c22005412414455140152040100094401c84074090300c03460055401c18260050114240d5418010203186890b454000c0302e546104403900660010000c00c0b0900403140d2455 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 250723174 1250 250721924 250721941
    0x212030915010914130309030f08070506181c020705060703030b120604020d02010f0215010b0301170303271002040305010c080147041404180b01031203020405030307030305040b 78
    0x130a065840464000e940c8005803035a4140d84004200c1440303468640342a0b40c3da521040c0c035010440030200c40400b0001890b40611408011540c0c0007220203000c1d440c1071802c541f0182c0d594148002404001a46200340c0107058003e01045006004c041d143e150340711310342e14000300103040c40d9111034424441c0740c19404085400148150bc02ea07406002c005805a19400542d11400a40c4200085205942d01c3d42a01d01940c0c1e0a2030007005e203800b9183d16941404000c0385008810009688654001d008011310f004032203052040400039020303d1340840d041c8000031810510301407404c510080c00002e000040040c15403100c2103c0d84140d56400c4142d88520303910801800d41c92800c203841101a40716500510002e034041592170844000307001c202d01c8060300300308030f412a41c0200750300b0500001c94540d84c20030340030f82c0d210820509000381d401d22131a03079074601225060001074400c800640304051160300030303411507001c0c21004084a460300503524000703000e4681102c0840c2c1b14009034020030403170b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 250724424 1250 250723174 250723181
    0x1f05150f0a1e0816120803250e041d030f0a030605060307020c100503010302060d3204050609030705060a0c0201020f0c030a0f0509030706270618080304060801051002120309150109 79
    0x10303100c8039001840000b45d03807194070541d04050018100020001c01c00c003543ca0158407100c049000030740342c401325142c00360200412603240c402c981c00010020b0111250f10703075010045a4000100500d400d44508203078000320000c14068024580061000040c010195000504800032400c120740c015003103a0002800c8860380400e1200a41085051000c00c02400641d0000c0704c100d4484030315400e8030100503034034061a42c0400b2006020319980f400348010303c039051010335400710b540e90085142014070b940d001d5455400426114034030340e5030f184000900f0b20030740465010b00143d102860f1180e6044001c141c42e513014885803804180341d000f12000003801501550341000e402000340041c01c2c9040700640c2c0d41c0f80d410740000c00c01c08804488122040300c98400c07901920041ea28410303100100c0c0d80445a02000d50404603581d031050008115055000c2c0605043d640300f42c030100821381e0403802c107a10700704982c20218800c0c0004030411800c10380005188182c6a60311910880c0c03640d998420100300c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 250725674 1250 250724424 250724429
    0x30403200a050d06090507060c0b06040c08040311210a18030201020c0409110603130201020706030908040501031e05010e06011b11151b1f05150f0a1e0816 68
    0x120103800800c000b00d1510700d07140c0c0304060180c03c005c1104491992010700f80030341c030707003100c0003054224a41c2014004c004880b594004400d9608000c80d00c0c481701e003e005510002c1c070080810182003150b062203103003444a0841d40c91203080800741004601c0c0c0c0081d903900b081c3c5c44403001500c9510b01c2d0007402e8030700c0c3c1c0800859806030082d0a040f055181030002818a1403419103400c5180f14007542c003502d034100150b10805004c4082011101e0300d10009041100c03a600080030035045c6403140c0007080300b02080700c00701e5909080000f51501d044032468820140b00190000b2507150100005c1c040006076100d80c4a942c1c242d88500f10502040300d91078140c0005a4040d2109044005081d40d40c10f01000341d104a02020800900f482c010580030340c1001c0300142068060b405c10740c1402d00004524000030780e6001c440350b06000500c2c109412410200320100702c10311a20b114542800a80c40300417003240604004032020244001414000103171208070301c9035903c0e0703100d6a0f00c0541c0d1540d21000c080f06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 250726924 1250 250725674 250725679
    0x160618110904020d020405101a04090506010504030c090504021c0f0c0b130b180607060c02061b031b0c160f0902070c1a0f04060c170301051503090102070f0503040320 73
    0x11400080d02403000402c0c0080607502c008180c0c0b01d011554509c40c94215561003190000950b50303905005004085c0e40000c3c0946060140c14802031000803004c40b0b8610940ea424000050319954500001321040c03880d6510200300403e0204d40c0303052288011080300c90b1400303403000d40c00341d0f40d941c0301c00708140c410f10f0000c07942c5900d100024885482c0d004000c00c141c41054580e440c2c0c400c400b5000070415805204100c421030343d03030151448007640601016902c0103103a0060008554403404100040c0b10041a040024100d81d030000c440c1002c010943d40c0046c9001c00f220326030074884100c3d803034040d05400381c080c5c000d0f402003000460038180d000301c03055039074400c641c2500240742c501540d600b00b2200d4010803100905014001100310003034007030801020706030f81e5104991150300709400700c5c400280b46018007200c108010b208a80300e01e0301640c1d241d501e42c035a01c2c0e503075074800c6000390081c000c0342801454007808030130704401e02c2000400341090700e002d01d85030003010083d942c21007041c024100c1c03134031f4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 250728174 1250 250726924 250726939
    0x30804030f2618030f0601061e09120b06031006150e030c01090e0403090e330a0b070614010611160602120c100f050a06050406080303010b16061811090402 68
    0x60402d11540f051030b191401074101c8450709000d40003d803c1c140241c1181000030041006110651140243e0004008075400d20015180c1804402d001100d00d542000d010039200c480450a961410030801b03182401124041110a0320707030034400942c1c080d058104001440240c51b0103228500032650030107000b4141c41e00e03c0d000c1c0c5046492b04525100030416418800e4510700051046181c150041c030400180712205c580810502500d803450001e605901041441ba4018110503114042c11200360341c3c81c0c080203a00ea06007442d081029107445c1a1414409000b54000508907030030100c0804040310403010345401c01c44100031481002400d201d0007006a025074a00354881161500034401c3c40ca41c4c2054520303006a050041c1c040d03890641c02d00a00503924001c0100e45205440307400301130201100d080c0000da10f0b1100642c2d43c3e000602030250310b4036000805ca103100c100406407825150f0b200a0034403030303038400c0c40101010f1582020161104c0d51074003800350341d070302c1c003850b00038400c95004080d030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 250729424 1250 250728174 250728187
    0x21b040b01020f03031006090b0304020a060305100302040f020a03060e0f04021005091e01080a0c0e0402030c040e0907090b181503030c0f0a1202010501150e0a030804030f26 76
    0x84050015288040c0c1980107508000080c660180015403017214034416208006150a50080605540c0d42c003a040c009070030300920006a40e0703201100100c501074500803c5546811580c01101112a48004d500c285132040d0350744550402e0f0050400e0b51320300d4604004c555920403140c40c900c1811201d0b403c800400b45d00280052501d211500900703c0c1305d103056421711038000081041c0001500d01503a07a071341e036246184400d41c0d0000c0c9840c1d02c840408014012041282000791810300b805441921858000c0001050550300c1c0003510024100c08003400c0d81402c0000a40303494140c24003480c00801e0612040c00384900f0685410707901070621059404159840c41550400446810b41265041c0020400240c01c04410406030400d04003190191524050515003841d20041407103400055904000040112080d800d41d0116030103905d0410f21002c03100d04001900e0340c0e00e10b0300300500e04c840101d400720522000440695035a40303c1c1d03260700142c03401c40d40403406450710302400031203102081081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 250730674 1250 250729424 250729429
    0x10e07082205120d021e0c1e0a0b041505060d08090d020406050307141e01020607180305030318010e120901030e07090212040309330e0d03030e0706021b 67
    0x888074050048069600c10841c45000c104241e10244280c002e440d000f080c540c0c0140c034044810b91000112045c0d071403a14100718034140d20340700e60144c3e0150403d0100d02c0072050110502882d00c01c0d035844540201d403454189401c0000c1119000340180d06482e0900043c2c00e03081102444003200e4000200c14100401d0320b08000d06043e8041040340c00c40e450340320000e11914200100c202800c4001c04040b2440e031100c06002c604030b0170810072113002c52201c00604046c0d801140454020b12146001e0040a41c0707030000903040889940010318a102c00010042012492010000030101e054024810719014024031359485201005070242080200302d64806580607a001d1500c4d84103940544c4d031072940d0b40d00b28000302d8100111603880300e803010041104266000d03070354401a01e109601d4001e42c141c020a580c040707180740201c904404010f60440011b60313014400702c1d0f894120082452440e4005841c0040c05030a080d403078940b0b02e111b4400e001c82c0c424000f02e4000128074402e00c1210b880c2204104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 250731924 1250 250730674 250730731
    0x40e070201090f030e0312180114120108011b0c0b0105100207030602030108210c0312191505040f020f163f1412061512010e0708 57
    0x54000c0d50760720301d21880010300108001003820b011361206041d101c504020f05003050550b0304091446141004a0604a18824042c0c14074040a20346045220160302c0804a1071280c0440140301540c02d0b4000207902c001500060840503000c0b040780d818050014041c1c5664850707880007081c2d031054500510045c140b51000201c042e106104131401c40c0d580361034040c12a4001c0c0c200600c0b0350000840c0081c0c4260340d400b41d500c092071028480c0c1c0344c10709a80030030751640580481d0f0420581640085031428400c140da2240c5011190000c00c0450300c4a0540b010443c182c3c49828000c90a01140c424402005d00c00c0d1084468102c0e841842e00c1c0100e07411181118500d181211064280c0584c0c50b8072443d1280303044680b40008600d2035003107074081c841c0b200140800f1102c804005010194001101c004003d0b200c0b10032051654000315140c8100058140c0c121000503403007c00c000c59400c1410005004090407074400d1040640b4075241d000f400c56283c0021103000c403a80042101c103100c10182c204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 250733174 1250 250731924 250731931
    0x2030403170c1b070e060a0806010e0402010c12230a1b06060f060504080111030c07030509030f010509010c0e0a06020c15041509031509170d020708031003050706090b040e 75
    0x44103140341150f80d4010040707030308011115022661001070309008056400d08290340040c1c0403a400c03400b407464043c146070345400501409103040c50b00008201113901404000c40016400810030008001c3c081006108000507416a0f01d00902000c0c1d810f0040c000008455141c001355032416200c00c0d100d1840365002070203480c111070440c0d0b11580025214140c020002c050131036640d4035507407145130404030350079640d03192503014209004000b48140d43c04900c1c1160080b0b50b240c1082ca444000c2c0000083c01c041c94828200904d50031f0200308200140d066000c0330750525039031141c0100c1d00554051010a11303490050700c01580c41264103444614090002000c441055a00703e4a81500c400c01c940b0603003e03039038102011540680301401000309040010322594410901001840c030b11b0f0320f402c032102034800c80c001c11902d400036040640b0b5003c2d804440c0410f4003d406a581ea0510302034403141c00304940b00541d114002c040020840600c02c50ba901c0c100c030401100a07040c5070800d000307103400d41e0020303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 250734424 1250 250733174 250733191
    0x11010305043908010603170c0705010f020f15071205060907030b06071704030201080a021911070e19060f08030f1b0a0b0901060b072303090a0b040f05040203040317 72
    0x16049849001142c1000340602641000410b000e843c0d03150144401c01301c0318200304140710a0051420402001458408466092800c600300e541c880c60b0507410446a5001c4c1c8009018440c51100a841040c02160291035142e0355003122410030358246007150000c1d03400c035910100c0507010036a00d510a80203081c6e0b14000402441c40c3c40e0f0035a035420500210801c80444070080032a0030001d640c0c00c8080154480d440b080b0030343c42c212600802415007842e2807000c40130b006102c507081d00710901c10000078001c2e01542024500c00e0500c254140c030302110a091072100c0701d05003640403882e5118000141c6c01c4031074001c01182400d0f49444e00d003410750881140849610401c045203940b00c1e00411202800301d0007001180344608050001d113003503508a403c010142101044142d0003e00b00380510104071250504a141c400b5104400d541036103e0b82c4c21055022101c0000410709004d000000c00446640048400d4056070728401d01099002c21a00078010454002c0c03d00c0c2c0c0c00c40c10020090b4403581c90f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 250735674 1250 250734424 250734503
    0x203030702041104261b090415061a0306030705060a0203040326190201050f06060a051b032107030501030b06040203040f061a0a051801150207030f08071101030504 72
    0x17901408001065002e4020728030746034088410300003003014042500c982080c41381c807884400201c0080340300706402078001424030400d10380c0202000240c2d8868400382c400300c820f0030f4041d1200d0010030b1094200360381161090240a000068614042c1c1c00c0b6141d02c86550051820a440e42d22031884080380340c950704440031404c4c130018034498040790080c544c147e90620900070054100c40001d00b1034900600320341042240e0700500c552640c1d50800d6481380341092070450343d80c14031500030601c480c4c009019032036503200105044003070703204610418404188080048101d81d94000040342a10020322020b40801015804241a0708042d0001d43c6e11501070b60300721044149540e24402142d4282c7c0310303420746c0b2407a0280300c203080c0b50110400000b4030044030450301108055400010f038840c1071081c00f41001c40e000456010600a00615000315000090400020232905040b00d15600040c3c084a4400d001040c05166600030301c10b4034000d42c0c0007440b40e090328030201004680d01070720320400b00f0360084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 250736924 1250 250735674 250735679
    0x24090a05060a020304030e0301060605041a090a06022425020a15020301051c0809010e031c05030f070305041a09071220060319150902070b01061b0203030702041104 72
    0x7004094003400c5581001683c0345001d00f002040e110703108040302d02c0b0380d061050030014203901605032004c0d2030740407062299410340051a0319441c401c002880b0303007091202c0d200003081030300030401c42107420015481e000f400b00906684c1c294028201d894072242035018601049610b900c08001a468005004450781c40215840b0039002005000c00075242c01e0300000103100905100c0a0101c602d1498000200c4a121950701c01030345006071180141001002503a0952558040282c04441d6074aa00142c52642c64003600502030f9200711442094800c05d4070218207480d00c41c2c0300c4c0310300c10f83d04006601c6410032220070b50400c03210054800100b07072042401c0846c108040807820001702e44612420710165100d401008400c2d1205c130030007481110244108035804099201800009007a2000000c0154101c8011081100340f508440d401c284086111410402d88048c680d040e50702a450303d1000b1500d548004201180075040290076400500c40d400040c03c20b90409012010b404280f18205078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 250738174 1250 250736924 250736933
    0x4051206071e0324080c01020f060c130308030118060608150d03120609090b07090e01090e01021611040b061c05060301061203020d0e09102603130e0924090a 69
    0x242d03813060301041c0401103608102c810002c011882c0c11031001c0c000b0304480c4200300c2600c0c0d00c41c040282040244000008c0740350032070180c2c50709070020f941d004d000a501e0796101c503504c44c14250600441000a81342c880d0204105020f041c206125401048280f20000100310622101d10081d490850500000c4c6507546e40312491401400b010348803c1c80005003001d45801c00401c18040541000148000c04806016001002c1005415500e5120300451288903c0603000e009102d42d070041074040b50280059001c101132030488200c44d060454051000d50141e800300429071040c80c1102901e110394902080561540f038220036400240140002042c5680320801d039454172a51304100c0c0141c02120010b0211a004000304504540c191804002480c00b80c1d52120a20494091401d0100112480c02aa00c410300c8041021062040c00e880e180c48c043e016001041d5890700070500300e0464400040c80e0700c540000c0300074000020000e0701100c0c4a005040314083d08029124120070f006046a0300c0209 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 250739424 1250 250738174 250738211
    0xf01030f0807023115060509060c150406020408100c0f030b030f061e0c09180a1503062309060106080601230909060105131e03050f0304051206071e03 66
    0x1100e41002c215040300d01d040d908045520b0140030300c01748080c0001c2070240c6548042034900134501562001d03560702e8110350251900c42090390340c03c9003510400400040104a401900440d0b8502d812640820302186414058800b0a4044000109500b00c9000a54840c0d00f2010141c540034060f190440c120344001410400c2c01c982458180c86e842100380444200ea0b014280e00090702d90890741040c080c100020707000081050324040380e0b0310002c04184070140f250301607403101460740c0001041949e24989040a4840c03003a03d01c0c20f074800500d110a0303800b0701c424194411036014000e41040d0703017401001d49500402405c00750402c00c0c00052175501075402031080550b00c902d22000d6455024110411910f100000e0869040180c00c1c001e04403007200000c903040903251940400002c504120b000783c0d401158550000c2c0030740c4503030302c68001042c0d0040001c005440d4161900e10b460580c030100946e407003d0507241400041c03807010703801002050100c1101c0200c2410706d404202c0c940c0d02080d02280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 250740674 1250 250739424 250739479
    0x50a0204170a26070b0c2802060a1a06130509072f0a030e030c061803061302060403030f02010b0604090b01080708070e040504050a140709050f01030f080702 69
    0xa42c0c02200000140302d000e00818401284601c40f00810390300c0d02c0c0d040045030040c000c0080c00740d4400e0010410703100000c02074600882142c0164141c0d21500d00c1d20310003140c1e0b400d04004c050f0159401140d13040945004010900540d0b5200c41807010303c941c02d0000d0740c1d01c0034a40b49040310400a0118482c0e1360b000d54940110b08540c0d40b001c0c0208140d5551007203140d01103406c4440b171041c0c000001c4521001c00c20300c101344d0705820040c0c0c90300b03e120086030410685c102c04960080d0000fa02c1181e50948040c04141032400380c0480d107107540c41802081303c2e91640741000e0b501c480d09003c1003000a204d42c103800b100300c0d460300c00400d18400e000041441500990848881140c643c208204a541e00c0400503502618524102c080760514039005400d107180d007400d003405a901d07040004c05004080100b01c581c2603000301e810308903202041c0650b855061500a56440340d05201c04031b02213107403005a26040c1d940040c03440103010700380c0d0b859003070a91241c070040b60000401c5001e504a8210b0f4240e1500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 250741924 1250 250740674 250740719
    0x90607110303160c08010b01120213030c080708121e070602040e040b070e01030b0109060e0d051212010f15120f0912030e0303010e040b07051c0209130507020a06050a0204 75
    0x3c0c3d0040741d1401c0c1098501c160000c8203281e240c5100c00352241e90045910810007900000141d4801e01d84007403043c244404e820117024090760820004031140002400b00031034031510207945501d18400e5403111039205000c44e402001c10408924440814154001c0000c175104200c0186040d6450002003400e0030100d60956201000c030041109040c3c000b40d51001e03500742403804210780c010500000c0d14240c0640610b0042141410a409058903214400490260000c04480c00e0381c08440c0209102d5010b85a400c0e00d002d5500000244a1040341282050303544481500940f55070100d0119840c2c1c485403001d010003a120100020200070307610034520098000c6007191115840074001030155a0074001640042d0307c1040100480d4450031452030b0010342c4901000c806072610001143d2900540d84050301c503416005c95216001140d9008140c009800c1c1d0b509040c1000d0380c00e080040320021940c07280941c200d4a4420006401584140e6100c20030345001820070b038640580045101c5a03409010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 250743174 1250 250741924 250741957
    0x2040e1911040f02030601090e0c0403080c031801020d080c0f0d02070c05091305071505130e04051011222319080703030c020f04140402040e03030606090607110303 72
    0x80807402c0c68000ca444003840d0341c4003076207141807010008003246400c2c810420781d00741100105410303203030701c0088400442d0425040307902c40400c41450754030303a4032100c00c0c00b460203480c42d44a030580d40041010741036038510751504149540e485041c400b041d846484038600240003001407045610007403006c0c150140c0200ca00070001d0317041a00380900e9000c05442d40044000b54840000059800501c070001d4404c01c034040300603450007250903607041c0035048400f045031450362008100954a030b07070424802c0340558111203002c09030324800b40032201129280382c480c0c2810015040341180c0c540741982828101487e1a10040c0d40b01011010711446810058a000e03e507200d001d02490405a06840c01103003071540c5041b01d140c0030041d80d580b15988002024000440506805d568074806601e802c0a006881032141c000c10000100d2034000490701240704501c2c00061003401500007081d01d2003a1030107059a4035181c0c0f00810414075812a0500704d4054883c0e00b091042a102440a040807218411010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 250744424 1250 250743174 250743203
    0xd03030f0b061605100b060d090f240b04142a04090e070519180209030d030b0111060f0c070203100c2a1a0c0c01062402070f0302040e19 60
    0x2802d2280340401205214101850300c1980c0c0c1c2d0702401c40d40c689143c044006901010f914004040100300d56020b0040070303038000c000803000800c0e660000c03060b0300302f481001020a0303e0100406c80c1c515038035503000c0041d1540050060405400e0341c03c0d0300a4504924080003000340d200a00c0399105404c0046076a4990041e084510b00806c0050042e00c81107480051000a1201d40300c554211445210004030008000326641314499045031100040a02504e44100c80800064094200300794031500141c04180c005040d168085003c60280b50060340a10042d2100650095a60403215041c1d9060007184200b0102801c68890f030308e46e03142030741c55481032400408481c40c0024020342110400a400054000005003070034401b01d00c142141d8840c0600d500d030707100d260b506802001c0c00c4501540c0f80501c04201461120703d0704480104041745200e03880404031040381c543c8107030320582d5583d0b450284140f0041c80c145e0084040c0c0c52803242206c01c10001d003904102000142c00c401d41c0c0303071045880e02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 250745674 1250 250744424 250744433
    0x10f0e0708030c1c0903050d02010b0a051f050d141509010b04080c06030c0c06130606050d050615010302071a07090e0601120e030f070b0105030607020604020d03030f0b0616 76
    0xd40c0001c00e00c0300301841c1403c0311144043e840d409120310211040c80702034070700b41c0514020801c04001e1a0440c0884040c0320b5401c02c003030b00030b1220994662003500c0c4058006214034100c0c030300350442482000c008541c02c045e0301041d202d81d0070480c03020111507150b240312017006508603403031813146600e00041d01490308a0b80a101384031406070003019294800308070a1000a1700010700418005040d14456604d0741e4041d10003105018801c410003060051005008001007001110320010340100410403020350340300100310900c802000000c2c010740000c80004c41002010705500da844d44107060241c5070203d50740c0e51003068010710140c000c02482c2c0ea4240506c0d50b600100340c00c054840c03816000a241000030000c1d01181c0006500107049441d02d01c066114031041c004d0366200c05030280c40613182e90081c500950608003d00455000c2d06c20703100041d003000d10020319940110307009031800c510b4525a032130880181c012a91840341d0951107400d031200c0c2d521400c00a04511020035001c01c11043d107440c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 250746924 1250 250745674 250745683
    0x1207051513050a0b06030c10050a0e040b1e06070803040803041403090a030b1b0a02010b18040305090d05010e0312060301050f09121308010219081608010b07050f010f0e 74
    0x140310464001c00c00081d0004070000361590a00360414060062030ba500d41c002031070a030908160750b030400581c19900e0ba18039000340103064208659100d5854200750241800f0898010b03610b143c0e80b010880d0000d0340c0b40d01410518500c8440050f1a5502d41540b03520b0300c03c113550058070100c0703041c0000000c11051080409081c08030640c1480035601c0d0042c0000055400545404007030f140b43c0e80381001c200780416540841030139118004250f45c6030211041d000c0e0003811150551400380f18500000049030603902c1d4481d2080342e060f110345050280d008180701e013269841d20103c54940d0b1b0f80c00030160300c01d01000680301c0c0306403041e18a03c0e145015824182900c0003c0d2600c00c0010440060012409000c01d00034005400c142005031121a80d00302600151025400036000d544001002a050b16401c100712000e10f003581c6421401ba2142c42c13900344d80090310103a600c0000c2201006010030750000009140c2580214102c1c0c0a2403a032070303011401c6407070007200420426aa142e041c81103450910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 250748174 1250 250746924 250746931
    0x4140103030f1103310f080d020328090b030a0c030e0a020d030305061c0b01030501060e07050a050a09090f0501090e0d08060f01030908030a060303020606040506010e1212070515 78
    0xe000d01c003540c00c0c1c15409a60307008505602411154542580d51402c034056100700782c0000850303591701e0859840860082c2c0c00014081e100003401401d110080712030000044801c00040120f080811200102c180312161800d80200810040c52480000c3c103030950703e01860190f030f8528000140e014038281c3c06000c507203030404a84e69980160404201590780c44150341c81d140e82500300401e55075502000944840b4410062132440d0314051021000d00c03009480480c181c8c0e2054000b0403445031500380903048064219880340006004004401d0103a200304c0242103120400c0c10410400f60f03e4400c071780141c420001d0050380081e510360040190400c0f50055064a001c1440501004208082c004003a540014145402900440010341040e4483d6100303000107900031840c280c03241048290b000241c0090b00c0198018825000070030947e18180c8601c03401800161078080d440307401e030824000c0b00480d14091a285000d0b0803c421018800100204030701403040c0007810b44007692403c0c0340d52910010313 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 250749424 1250 250748174 250748177
    0xf06090605180601090f060804120302091e04020415020d09050105180114160b0a05060906100f11070803120a090b010302060d09080a0c030e0d0b07110a0204140103030f 74
    0x404014036100c001c0403450030481200b40d40c1d0070f56204070040c0c0301c4600c0380d445074038040b5107402c000461580c04410340b40074900c2103a404000301880d083c22001e0307000382900e082d44014040b5141c0484440d200c101071403464054030140c10960b4902a195004d20032001078009a0440c0f0044e5031000d500c0503440e009088c0908080f810f201c0751542c0c01c00c1d40c0e82486a0346050056801072580180d1024082d11480040c00518901000c0d40d450041200c05099a208900c81e0820011074003078a40300c03000d14807030300e009005003600b0502100110b03042c010440c420401c2c0405841c072a207901d8418400d5401500e1600c00440d65414401d222006010005180941c407d1800004000113180008100e0440c2d40494a9503102c0030402a00c00081000f8440200840c00015120550580084c084203049010761a001c03042c550074400d101d01040c5420006140040d1807001400142c0644000a4616188422518a048070b613000c01d0840751900708078040b07c40060010410143c0c02900100f290501d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 250750674 1250 250749424 250749431
    0x10e0f1b070b150a210f0519150203040305030a05040201110d0e13060b0403080705161d090312040602030703090b010306050916060e0103020306010e1305041101050903060a05090304030c06030f0609 87
    0xb085c4502a1002c0200010366110120003040400e22004103044560f19400c2000c0d1030328401413440c401040c0c0b030303080741c211620b640c014450b50600c44584240e03840b5a825032501491940c0b0700603550000e00d40144100d05002565960640903042009116403114464031084810307000b00c410040f10506011040c00c4e03050912100340071300701208042d581102ea100c122a5101c210a2901030704006018807181244403100000150b6600c003800320503d92540818506003644400134020b03201d1040c0c103480c07400780f140752000c070b400542240d000b10b80c84080c0d40750010b05404195500c1a018100381e205640c0591601c09009010701e060001c0300190071601c601c072000c54a000000743c0b007032036108800707818540e0200002b00c19074020007080382081070013003030030007400042100507000306400d647c00d070b41c1440448075100155002c0d00407501880c034000c00270030099440c0d004100c00303860000e065103046e01003403000200150b00c1c0e130f41c0e1002900a0f80c038049011500703100e41d034044414503130060409504 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 250751924 1250 250750674 250750679
    0x5060711010e0a0f0212030705060a0f0c0903050309010e04110a0c0b0f06030a060f1503060906110306060706091104050705040801240b030604110a0e0306010e010e0f1b070b150a 78
    0x3001080d01e0061355040e80c4520741c20300c0c0980e82c2410760103080c9001c0c0030350042c6420000e595026601a440030415801d040041050800c03044903908100e00005240ba4802c110344141c560140c8240710799240014400b003210100d01001000c16002401460f01158218545108000c080d480190b44001d0120f0034030000d00e00200040d43ea0504040042c1100380e0b030360300c1d0248601841e040003480c420f00c240704010b001d90724580b54000b04615403003961100e141c010525081e50755413080342e00a0324020060f074144031a030307150b0400400e074070101100c508070304041a0855460740c1c029140b1865040e00c94984940c544506035003580d485030380300c1408500c132405100c078024050009009403203030344420307a8481d501c6a000c40c00502c0c885084078000300d03002c204995803030740c00141404d80d54029415034065907a601491120000d0070b0040c109902d041c1c400080103050340103281c0d640090001c0c582e031680000e1045080840d44002002c1e40c01c1000e038400c102e0a00340d10400c04c4617101c13040d2009203900c1d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 250753174 1250 250751924 250751933
    0xc03040809010c1103162301020309100e13021c020a0512040f050f01021e03010f0e190203011202040c08060906100509041109010801080307030801031e05060711010e0a 74
    0x2040c040d055040c07003d00744440c014071111204c201c0c0c0e001000f0f000c0310a2115111440100030b8407521440c0680c007194651601d1a0040001c00d185406041c0c00550515001108110310808400300300c42c20880308035804002a520040c80304d050303011140c07005945545050121030100d070070b4894413410032b00400601c10f015030b0040441d400d400181440402c0b80d00ca07480c141680e8621003101800a1192001d002520031040d4002c102520034414242907001c4c00c20240c0c0341070b02013485024090512107404200e8400d42c4205594440000c0c0460b0349010401a500c0080b60002c0c0c201c1401c401c1441c05110450130036101e15010301c01da90600364210b1500c000001c100143c01010180200c0c0101c0012200c2130055007035441c0c00d04010800c1c44204840b65103410907400606a036030000e0145000021140e00100454a50356050b5440c0341c507580c00c40e00ca408114001041100440c48440c5040d404100c041c4613080c01945d8030742d240304c1101c40c18509035003076030150030f03846040d40c101180020014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 250754424 1250 250753174 250753177
    0x50f0603010e0406021c090b0906090c06190302090d03050703020111070818010509030a030806041103060102060103031407020a080303191e05060315072105160318120201060e0c030408 81
    0x9074004005a1b50380654201065071403101d2602e14201800c000381d6a007040390241203e44100401c01c12246640d5588800e96942c07142260703010b40010013001010281c200b502c1c00b13103a150074141805450503c0030b4002c180074048902c1c098002440128051040690a0050704918440504510700303000305070300d680c0c03440d104800c00204000c170040b8000c2c40503400380042d035400050050584a80040c40e08000c0d1400904031403241c8254900340c000030851180c8415079000d030707406900804071a802c5580c161001d90110000e040d04640900000f80160b4490784010040e114100142d81c42e03060200ca40049144001e041c000940c1c2081c20280d030b4490800d03480a9000030444011031f0035201e000201b4101500d181c040000040c1c006c0401600c19040900b441818800301102c01c55140c038580840c0c00c0790020340f100e5800e03400d10550411b045100745c220b4500c8280d0f50361903a58840d440d6440c00030101503541c0c00809030751100c40c1044141c4d000c010803640004d04001c218914905a0360351200ea = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 250755674 1250 250754424 250754431
    0xa060e130203010f0f090c051e1207030b04150e0606030c0d0309090509011506030c0503041101051308100b041503060c090308040e06040b010c050706050c160e01050f0603010e 77
    0x2100e0903814010079960250002084d02c01d441e04100b0603042848500e80c09041040c5003920000040303400050380d81010801c84084040300c00780d1000007000442082146c8001d2159840740e40308150000c4040303200003070840c0c02140b00708040d1000b80b40881c400010b9448002c0481d1894021008011807624042680c451103070007141c68242c2600e01d440d00382d40e001040e803c0b80c41503c5ca84403c11984c48015400034090507044454803881c0e5580341401c40039900b5110307035800011020300c0407400080100c0039042c0c0c0b074541418004d007480d080035101c03014089250721240e201d602002000020850603c00d200e5403890903201440019242019000d0180c003501c03000305002d43d601c01c002c0146125182e14405147c5c0198071075619692100700c804a66001c1e02c4043c441c0d450010020300759170103541c00c04c80719036000019000481c0390240503078840d0014103102d4254040c03044a540f0154444203004060014071069060342d5042c4001d0000c0f510780c0a40150240c03100300014091207088014084c1e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 250756924 1250 250755674 250755691
    0x10207060807050c0307050c1804030e13020906030403031b050723010b0307080d020d0806180a0b06040303020106150512010b030408070c06201207020108060a1d0a050a060e 76
    0x4071621a0103003180d6611800010075014000400c0c24070400c03401207400240c0300811504440080344500c1200d5140c4802d480003030200d0014407141c0c0c11030420080c49625901300700c0c0018200140a004160030f40d004940c200c0c0000d5441c40f114a040807000b00c10091340d00503203040703420903000340d443c43c91355284d19203c11141c240c0c0700100700100c01c0940140b40701100150582d80c81658490300c15903907100c115a0000036010b1014000c0c20684501031407032103040003c161540d4018507482c0400752a5010700704807106520380c44060724036299040100300440c4207600003e40140b42c4900c280c03101e441b445051003040000c22450b030780d4181e00c2003018152906c0381112992031725107107402080c511511500800000c40040001030254100701d0300c50041542031800780000c9110303108c0a403514602c44000803030500912a480c00346d4803071034246031300c48009090300b12881d403640b0105105101492541402406050070030a040a1a0040540203020b001040c000907042242c00c078a041c00c0141841f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 250758174 1250 250756924 250756937
    0x702040b040e03190206090d0e040b010c06061202040e1c0f020f150603160f1511070909210912060f060f150507020a0501083c01050f01020706 63
    0x8090395507540200300301c00245080f00e66800310320518650324040c500520016005c0c001c00102040c0c1c0c0402e40e440c0a081d56501c1600b452521400c000080c00300d00a401c0c1000035420326403002a8140c86004c028210000980c06203450314810031040d501460084480b42e0011103a1a0301070890300ca90b91904801d5080101406125000483c9051082c0380c0a070a180301d004080e0083d204034031407250103490280d05417400512945240f104000662042d00100a500001005100c14000900740b040c9141d28208c40d40d21504c0451502c0e140464002002540e0b984000c030741000107000c1416440c080c1c3e0319414041c1040c00710060103086851150014901d4003900c0704040115a502010351541502e008000d566121921407014000d030f80103003132400072191450108103009600f920020340d4000c101109060902c80110323041d420143c2000340784041001c03058030451449891030210b00c000f0022034141b40070498880e00c0f00c1070603440740d40a9100100c1c10910369a0104014044c1d542506141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 250759424 1250 250758174 250758191
    0x4090507090b1e12120d15051008040311010f020c0f010606090e0417120f0907051914010203041703120f0f04060518071205010e060910091b09140903090105070204 72
    0x141005c43ca46040c0018138070004a032801645ca980c06440c0314814600740c03111564845040c4902407030b00e640180c000c1010007000500181c82103c0c188640003c51001040400d01403814030186d8000c802054901d82140d028400345070000d1203100c0040115161110640d481e0490240308400c0c058405003d000c00300303117510150304003801180c0e0001c1c0c03416041302c0076203442000152aa078054a00c000b40e40110351001805103040c00103200300d00400e00090a01929002e08480520b14442c00039066010a02000031110b0b020300703009001d8201c0001071540c0b6105000c45d600b207500004d015402400c00c000901403c0c480c4070f0601540950b2040e00060180c880358000fa013900b409407010401841003c602103514540c05918050310b5200d60000c3c4007018002a1068460604a4201d201c90344004406082c45a054012080c900d01400c0b0040034201d909186041c0911940c011048483e1102d11135210b000e0445c124561114008003c3d6080c80c0f02c00000a1440c070039030802070311070741d280c80c0b44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 250760674 1250 250759424 250759459
    0x10c0f0b0c040e090a0c231c020a06020708010516080c030a110d0204061e0c12030609020409020c0d020109112e08040312140a020d0b04090507090b1e 66
    0x100c60151100f6454504280f0300780c03540b243c0e500c01d4400304980d5801c01500010f500d4611148650202003040c0302c03100511100310610604100070340c205400c00b40b4030218400903031140002c0d00040c116550103040800d0405042c10309481c406130450010035291404503d1050780626030680210a0f800c4280d500e454000451010b054800500b91101c07038001000048580179a0081c4101d9a150315401d41c1ca003221403022108540c00443c0601140c0c4141c19074001400c9828208910725403800d0018080c1d442e20783c0380c41260802d402019680342c0c0000c181c558000c00700840715009009100a2100790410303a00c05814024640100f4011000708456884524100c28a00d803034280b640b8030102c91400c4000300401c00c00003541d00341d0200e0302d110383e0140400d40b180590f0303103034020408440d10151584001d01000b58001039200d041c543c3e80720211803040d55940210204a40144001d01c0e04500f00999007045440c02c020580c406c1c1c000000e0002003132000f103d8030503001022103548140c118400784 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 250761924 1250 250760674 250760677
    0x70b06010e10051e0f0d0504020102030d0f060e090a050d030506010210050a02030709050a0303080f0a022206080106051c02250c1806260c060a0306090506010c0f0b0c 73
    0x8203600c07500e4080e50304001c65012020b0213509a80304400d001c1c580022000400d18820340b01c40c09107541040013580103071812030b001141c02031302c107204603450f0202401c00c41c01102e60800c064000a510f0714400c00010202c005d001d6009080c000181c03500343c1256489590312000056150b05041d141d000107142603009015a0050000c0040140240c0c608080404001e51048441030042034183c24041102c0c01d02c090b0000549905448941d42d03a142d00e8900c03080c0c2c11004202501c5a0b0702000746548103a11100c050174105500c05081c499503041020150040c0816000001004024071200f44400450315040c1c508080baa400181d0b00c42118a402100600b16500c140c0c0500703000c001d03401041201c0940804030b440d1201800200b030241100c540603590640310300b00b0045461a002e00c080c1d207100703060b02050070230041111604500040130950540012503d1004240c4c0c502c0304000000d075500900c2d900c841e007460003240b4040280c1c1c4400c410006074002500c410203807400034000c00352010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 250763174 1250 250761924 250761947
    0x30c010f0e030a03050405031b0d0305251a0604150b0702030f030c0f10020306010905091003120c02121603082115130501050603010b0703020c061321020303070b0601 73
    0x10300b81c1c0d101c00c0f0541400340459100e8450300c0d020b845104884101024140d444070038140c0700030914000fa40803610102e503540c005444003154a1106002840400303404041c0c0304455210f1081d5840c80291105550b240c803000402c403034011820444210401401420f90005680111500c25110141c0b4000b192602d40da00e01088210311000480c901405400124007500815001c02c541420b400200e00c40142d00060780c940740403803003051040c0718905d003000c810b86c0d21003000d5440314a69580c0e0307211070795640c0c019400030020802600c070140640c185240700169419101c0300400340f0358020903045414140c2448007802c081c001080507903824105080b0080046007000009a4a0410300c45112801d08042d1003140b0a616040d200b140703080560103078034100c813002031a0b50308581c03900400040c81d0788862003c50850050500b200082c0c2c4c2c90401500300c9081c480e0744075002500780070030742c0c92200086114810072150a0022030050341c00004403107a80d5400781d0503090b292180e40040e614580b582 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 250764424 1250 250763174 250763179
    0x2130f0b1804051608030f0d090b01031b051221120708010f150207030231050115020303010b03070f030b03100c020105060a0302010c02040902010e0a03050f010c0806030c010f0e 78
    0x900c680c01c003004160050103103014105407141a160090040000159449240c140e50018089041070350303842c1d80541010142454041036680312513a440440d00c2090f002100d840385503242c01c505003645409204080d140a80b5400e000c1d103802011107655603c10700052028040202d66070122100f10303000e40d40c9090790068001220304000c9800303880300d4024080d02082e84418840050751080d100080d490880c0541c01420340c1508507001c0c019005d094401c0030102400206040714001c02250002032200140c0034001006d5041c00716001ca4140241d1400045500034030050010304010007c43e030308071840d820b00401c8482084c1c070907000703440b0700421690b050090b8111400704007019008000513000d2940200055035882c0c04100300c0915901001e80000c848004220040c10282d000e01e0149005050885200e8030b1031000904407030300ea40080f9295084914030001c0020240500b25180c1d80c582005545803070000040795031410040d0800d81080342c006c1103900b14601990282c240b24101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 250765674 1250 250764424 250764439
    0x240b03040c0f030506040b0c0712080604150e061206041203050a0b090a0902090708150d0812010807030b010f0e0f04230a1e03081f1203120c03050402130f0b 69
    0x49044c0f09444481c104c40595401d503060300002d6a0100e520111646254841004a60750f000c070042100d10907001001c15422030768800c440002c0240001807640189441d40c1c1c02c000c1803400509101c200301070384460300380c6980034a003800000744503400030004142c181d160000300be64039040044058682c040c069504103111009201000300280c012888060080d0781002c1d0075243c02608440c901c0e0b08480c0795070400041c04400505180040e20200f865000c0c030781d5642041d180c21102c03650100c080e40038030b4050b800a1007c00810990079041401880000440d40b0001c0ca050180201d10f180100081104201c490001301007002031042102c4040b00d102c0d907410190309050310b156560080684c281ca80e0302800c640500440b0052152010140e13069540c40581d07260802030940a0691500d41d814103554a4004600c844009820380c2d05280255a003824203002003207500708503142c0a180da401c00d8144001c00016880307122039910610704070b80001500d5846040b10320000c0070901400d581c40043d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 250766924 1250 250765674 250765679
    0x40306060b041e050609040e010204170c090a0b030a1e0614100f030210180b0c030304060e0f070302011805040e03030f010e090706200105090d03240b03040c0f 70
    0x40140c070654142e020842041900c028600f07804144511403150700440c03c001c0d600503420a80c200d441240640400075051030303181c00c0c116900c00203906c2d40080c254082e103080c00305c03071412054150b0032248070076080281c00720082c04a40c903401048000340035096841c803402840b01030503216100080d00580d080042e584410020046c5582c141e408080ea00500c900c0487c0e00340841d044501141d074010684401150b59031000e803158416200c492558580c60b050000d81403584200502161825502660392440c0c1850064100c0c2c030126070340740c403a0b445110b02160703520f0b0000d40081030300d40900b00f40030000f2107105d0440c1e0b01001904599009420643d6150b07490718004080c50050b000c00701e610860381c0e2660b89424820008584c03a10070380e80100381c208506402505a488500d00308a494500340e00e0114200e0700303464003518481926800400c10386c0600f0b07032501c40d00103c1c1d07a9084034034018662500c118030703000712180141318642c04008080b03410001c2c1e04c0940001040070284a102096 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 250768174 1250 250766924 250766939
    0x23060d0f120905150a05180303040b030f060316030f150e0f010b09090613080702030a08071a07080c0f030c0c010e060108071e21051902011b032304030606 68
    0xc4180c481d10b13005212a00084001e0021a030503038841d144160388181c00d183c1041f20391499043c0c0c030303210190140400c1001054010300000114480c0310191a600c0040c2800414503203441051407509122460340078081c000074a020072100d003030540018140e204c00d40b01860b113800410f2002221300301881105c034111b0f2000c1043d0001e4680d007104541d411915a5040d0705951105021a103400b0f42c0b504030752100d400104850042d140850019085071043c4006035149042580701a20a4500f900c040c2c6d09030b10386224048106500510354a0302034918140340c14a075049005020140040850200000311024020780c280d40c840ba0508000740710003001d13003442a80300c02c0300303002e500014000d0f0103000ca1031083c0e01001d188545210311401d01c445107850f980ca05000c0181c84140902130305442054003083c1d040005000d80c0401180400c000d80417840058091505220320300400c044074000a000703c0d40006070010304211440c2e10304244040a00d110300c0743d00c5550402020390340390210100340c48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 250769424 1250 250768174 250768187
    0x1b0c030f0a020a0807150f0309050303070903050606040b09070c05010b09040c1502190b1504140109060602060f0106030c11030408010519021207210f05090123060d0f12 74
    0xd03000307030f40d5207800c2900c40303100c01d84461280c082d0030146000c102c503041003580f0400c5000e05954187c5000551a1555501c1c942140c3c02500c410300012400417041c41481801d1180e039401000444081121060010116800007801001d40082c404907a00801c00c2c040c081d0007840c03080c100181015814a4180303494402c481603401402200458150800381d500d00001d0316440c180243c9000742c25548132075079034052000d401805400340c4506028071058585540c000e48106601c015010042903041a4103102103c0711544a8021907200c6c00500880c503041c2e40c1c0c50707819070301c651801051254410000b52804145500080c070303240300c0003070001103840b030650200c0c1c054402d8602c0884406004440f01c810380c0180140c400042c10381402040c44140a8203c1300c01d5160703844c0d4040c062820044c810710880d0ba8050072103082c15210001c01130b051500f0300c250000c0000540c152854000829584060901c0041605000d007020682c05024460100c003042c0ca02940800c1001e00e0000082e00107200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 250770674 1250 250769424 250769443
    0x913110d06050d150f0b130605100201060f09051302031b1905030d030c0210060801050a0501050d0c090906020d06120311060108030a080c28081b1b0c030f 68
    0x1c0c90400085460324002c05814070b180e4001c200c1118900712481110001d001655048002540c0d9080d0117400d034036120303050b4a414a00b00000100f0034600400e00c50802401c2d1302c40c50842e4503040d0248039100814080a0a80740c4130f020000b001d68401d00750380c0343c8840215002e9814481c05030f02c0c42404085400b041010b90007030310020345403081d0741c4107a1540e41c518001d00d43e1540081e104511a0b91083e0b1050003030358010b03c100c03030040a400d080c510071108a90032041107039441e4020414801d1240c000d040c0105015211014480c10588070108400410301a910416440b91081401d001954040c2d900c0915114401c0004503554015603034450400082107000ca20b003c05018000503000c65014100c410b210051803402010007400c84d071450004000c00c0d0245400e10401410a004420000d503e00200d0118a031686039150042c0081200502c0b130800c4004c04244040b40f01c0d1000140c41c03481409003569078004c1108507140c5d04000280510780d816101301890402c513140c00040e240c42 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 250771924 1250 250770674 250770697
    0x12040b0f100f180b030712050d0309030e010e031606110f0f0a020105160213020d0b030a080d2007050c131503030f1e1e0503060d020d02011808060a0e0c0312091311 72
    0x84427280c02c5415800c0d11440c99001c0e021444001c1300061030b501a01c4410103000c03000b016a44130905252001d5070301d060300c2c0c001000040c903642d440d08103518100075640c06107012500400e2160140c0c0c0f102e0341c0da00103114000b810418045020700d8038500f4145140c11032580189007802c041c803000740c860001d400040c240c0009d076040c40c01e681094103020404000094108500364a0b0000c901c04a40280c40b0a040c0c0c0051000c242002d1f40c0c001202e4030141c80713032a1082001d42240303400241086401c40070a40d4130100d81389800024014103e203a103106085991608045946841c0044103480d42428055800c0c40d40c2c1c0f00400b5262000d6210b0f9031548440c10840d29507440155081d41100c1c3c0d40411502250441403100d106c0015280028005952a01c149408036140d01102c200907074040c01070b4015185540008240940c049150040d540c040c03a400d0005c1c80703201941c0001030395030300340d80c19207a51310340d40003171301d00019120b036000c0701c4440102240600c81441858428111603100022450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 250773174 1250 250771924 250771933
    0x90d05030d050a0221040f110d0206070f03020c1005030f06150d0605040f020c070306092a03030e0103020c100504050708072c040302100e010212040b0f100f180b03071205 75
    0x80340b4201200041c6d0049411420114030781c1182d80d2040a407039681121a60b003d5002603001006035111001041c0c10f80c4039640d52006685280b0703010303140c804c4075400703244950f142002004109074403100307907540005080c0d4580b10b50749400000c074001d001e18400b504c440d000d0020b411103c0c01c1c0c5a4114004440f01a28100300c00041085610300320b010b416042c0c00d00e23400c02c4a0410204036990070040800d0b001d541c81c0700c80040b180c1d4504100381410075010107101d5140c5020418180c00070307113440e0f2400c802e00b4190b2800e580b6544940d12031003e072039100c80080c0e441021805200d820060040505010400c403550152250780151001d812180e045402a0f003594000c10316080161050340110340c1a002050317070344100e142070000b5240d03480c0782d528190341c00e103c88012030000401e030500982c02007080907401d0900030040a20300100420030304183d008034000b04058070440c0e0405084030004400da01d0078000c02c9100c100601032074540d407503051146403c0890310a0100c00d40c030745464031500458 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 250774424 1250 250773174 250773217
    0x3060315140901020c2a060408060702060c091f09090f02090a09090b1315060b0306030115050108060105132411070503030d1113060203130f0b090d05030d050a02 71
    0x2c6090b032158140441094004490564031140c0700d6010020100306207a186100d480c0000200713500d5000307a0700c4100254003074024170032142d4041c0216500300c1c540c0049a40f9050829001c520350b48e00082940c6018414082354080107840751034a040a003030b07031500621220a400e00300401039009148a18424044100300042c07548251041c0c1100551000342d100c2c4590750b50b064503c85030f8000c1c0050f5482145000c4031062103a091040402408607040090740700e017880d0b405d240c00c490620b029900036039040c84090100307030b070080c2c0c100394820001d1074555503c500c011840754001400360b1261445601003001c1e00c10541c1401c4050054801968a10b4401010600c0042e42c0394000d220b450740540041050000c1d400880d000050b0440c41c14520614064021040b90085080d66001d900160000705400c400a2540e404442c001c040ca25040700019040c94240001441180040c0d44181820220300040001c02d0094582d10070041004212074500706041c000a90700102143c3c02190ba665080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 250775674 1250 250774424 250774441
    0x619091d011a0c030c010e01050f1e0402060a051b0a14030301060504060503060f0d15060902090a090b01020106080604030906090f061209020109050a0611060a05010e0f070306031514 80
    0x1000d048442500c0000400b0014544500242d4010311280010340420442d5200a22090041c01d85098060000084901e016042a0b070200400b820440000400556804021450030040c640054046956070341e00c142c604401d840b03600c107407112480c100f51005d070140c0c800e000209050701114090700c2c01c0c100303004100f20615121b100900581002c20310612090050902c20800303035a00003005030004101c0c800366000150310700301822080f2081d05500d1207c6080d050180a00002000300c0c040c15410705c015480080c600c628103003d10105c40b075441c0c1040c2c425038400d40140b4010540e41054441714102800e008090401e1170103210b0110b4140c600020740150034181c000211003081c0c1d5222001e40f42d0181d110301402d48094164100070b40d12780041441c3d910030303802500520f0310380c81d51010100d003602c40c035041c01801410310012030300d0100100135010300d1140141d80480300a100068a0351006016802850140c001400c1000356000c2006a59071950181c0310001652166074081d40d50b4104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 250776924 1250 250775674 250775729
    0x518061b030d0501080a0f2d05160501020c030c01030213050607050d0e0619120e033c03061903120818060702120c011d03120108190809061909 63
    0x103004088005a03140782011420200d40104c08e03540354155484281c0d21021103451601d41640305441136001142c2000c3c162811402407002031203703001514052042000103615503e403c42c665045c50f1b00081c40345800321000c084c1c54017915000340116260b01040c00c0c0b41c2d55800e45425140040b81c4004820005423400a09590b45a074a445a01c0b992031481d60301140e17030709421001d2518507a110711200c0480581400a40418150040c2400e00c0d030b214108282c941e0101c501030950310103594800048201c0d1442c04496110905544000000051400f44540e88089a001a101c074000780e10081c0c10aa0001e42a4020100340c85c4052040310080760490311280140c0e0010090783c00301c580002310382840d1015282e0003031440e00008525000369402c044400d50f41c1c1c401c060980000070070b0245907081c900214090211500148846070000185020641c00302d039020f4202100400c01075107603542c0394101d0301420740c00c882ca00007170312071500080c06032811170080026500d44102c061100544418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 250778174 1250 250776924 250776943
    0xa020306030606120f01050403020c010f030509030a0c020a081f0e150f07030e010e061602070602030d09111c020405060d0f021309020a030f03120501060518061b030d050108 76
    0x4002d0001611580104640314007642d8802420b401064030700c40c080d24003071084070f120701e000c0e402030010000028001443d0038a015035a00c141454201449100761000040c0c413120012410200180c0003540000740c2d158403030798070071000ca00c02c507484200e40701d40110034003031a6040410140300311484564000d80312001c2c000e81d5400420894001180030300d61110007038000c80281400990003119541042c20b40b0030070465a41154000d106020350f0508400340600b01662620140c440141400f1000b9102d200b27107144058007540300d81c1e07200148001102e0303406000d80d000705104c25148010a8080b520700c403d00090344070794506400200a801c0016802c4007180c6d00c032184214681d0740b41d003049a40403081c817056a0b00f9a0b03e5400500603112914941d005d1801800c0742c2c07250424510b00106904101180c4054460615004000c40ca401409498024002440d10640c640703203480414035900501001c1d01c804403850200c000a07070408070081c0303000e062211040c4607981e00d0b00461540c800641 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 250779424 1250 250778174 250778179
    0xf03060406091401110c1006210309090e0d090e100b0c0313180b0d08030c0315060a030f05060402120606130905040606051c080406050901090909080405090a020306 72
    0x8100103800203400d03900060207684121020003078038881510541c00c607801701a8a52045100103400521a141004080c01d00940c03580184403442c01c1c4810213029814400542c14086210701c65081090300444010000e07242d802020132981505920707aa91b5080803c07600d201203654500d000c90400201c1c61001c0c481e00520105010f0549054984191940403103941c0d0308601081c801c000d080101c0e020314400030011141c1e10302985680300b03680c00c12909003500c0d5030f01c0342055440050000f6011400e032548802050b180035143d59421114105032094042c0d01d944c04038002a2041c291a0150300280c008050704100300b06540c4c910003070004030300c01c1d01c4004100c4081440065003c0c90104000d104148003215129400d07580c40211000743d8001340c0c3c089800302e48030841445039003800c43e034800c000d08070b0a172050304130002a12136110780e129a004030020004d0000b194244c03a401125680000c000e0b048042141010b2404c0083d500d82240c02001d11aa0210000c202d0f1165580241d90041500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 250780674 1250 250779424 250779433
    0x402031e25050703090302060c01021309020910030c0c02090f07090806060f0402090a03120c1101020102120711010b030703050601030c0510050f03061503130201081305030d0e1905070e060f03 84
    0x81001c2620039800c914800c80c00c0141e90310f408001030300c824000c1c24940e041c0b00000351b01c40c1c1e80c01800c1a8990096005000c20b039206000240c49581c6810014685c10a2070400040c449203000c030480740944e02c60300117500100490b06011011804000c2d00d44514070355039500000d50b480707411003034507010251425507102c1c82ca000b015427103140650040141240082420440076620707510040c0303034400c4008600200700f1480081d4144400d51340c0c10740903140700748021480c203800e0104440e982c600c007602c0501000b05292201c00c800c03e0950020107a0b9200504075400141c0d00c3ca0242e44d545400d00003200c1d20180b440c40040d890070501d001140901030b544405040051101d1440748036000101070680c4a00c86e11520400800c840c1c000f503002d0010703150b0002d001c001d0f83c00090f03c13112010300300301034464003542c5100c04200302000303991381c20901183c00700380c055212500914011800c4100041200c99203c86001c000f400580344003200d542030341303001e00381c0e481c00c0401081d0080c49020741d4050b0031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 250781924 1250 250780674 250780741
    0x6150901051c050d02030c0d03020a0807030b04020c070e090d03060509070f09210c05060313080d06031b06020c0a1a13030525050d051903020307020402031e 69
    0x505400c2e00c2c4220015596080500400391a50ba280c5981d4414074009608006545001c4610600032029184210b0030b0075450000300c16001000e9480013010310f000c2681d251a041d880b40d55a804607650000c1c11403c03a98410b4840c860490b8405041c2c8035180c86104188024120a0003400303000211400204036103032a80e11848261390300c0810100142c00c00046060119001894a680c518640c40319812035100083e1841c1006d100310036030304194405d039000d01c00c0010441141d020001d01560101c0c40365140c04504807039034040c10302904000d008c000111104600b00503d4566101200c6040c3d0880301444594000e10484a00350b01810b12800040a04002602084d400801c8145040c400e0014555504d860f540e080ca10302990915002c20900c15620000c04000090700c09003108803008515511140e070b4103665441c04550014128210180e010700b818001d00035102003d80240056590b031a1601d0250704442c02d2205600700400302002240704540c00a481584042c0907801030b038034128 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 250783174 1250 250781924 250781929
    0x50f01050307170412020d17010501030c031b0509090f070e040c0c0c030302010501080c0303040810090f0c0b030105120f0a11280e091c03020a0306080d0906020615090105 75
    0x144020b20301d406204a003040301c1c41c00000040705030b1007140502515030781e440803004000e09080120518004020300780c04103082c00d10806980a0454009080001d2101e90070701043c0d018110102e0f04002a912204c081e01d00c068100c0011322106004590030310456841051100c40480c007507481000054000480702e1711410654000c01d0764010032700741400340050b10b40d1420542c000c02d800c2100103035110001003100d170404000041182d101100558209070401504a030380e50061050036a07007644a116440501203d9905079201e41c1d00300d079800880311b0f22802d10b0707a0254000e20865001c1d4040c075450a6500340c000c512150802d141c54007030140100320351108502003400c03803551030344400901d0130640c1400c80f0420145002c03010300442c00e81c40e45001001e04000c0c5006040d190541c000b02450301c81c070012429406070350403180c140180c440d0000e101c2100288060b40000145100311300441208540004540b8100e0360154200c6040c0e0f518034116201200b80240d0090701300c90820014005c51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 250784424 1250 250783174 250783177
    0x105070602040905130204050a0b2d0a060c0b0109021624020a030e010b09010f0306050a0902040c030b04110c0d0305130209040b10060c0c14030703020406060302090f0901050f0105 79
    0x1801000d02506203030f1104800c00031100b050b40c040070202e817560455011400e01c3d000769a80f0010501040003081129030101d08000b10298808403181d00c903002414002055040c90001341e000070746141105034481c0405001240502d40036903446864800001d000c0145002f111503488402504c1920400d10b90780300000003402c032072142c0500c4002c204845031100380f440588031070140c55802003841a00c08800030700b1500b03499031041c001e03240c175001032080c034050240d8007040340d03409400000c9030742d6092581e030002c190048009520a06002c100c007541036141c1c10403031381882c086900f040002a40039001c40588100c000c444090b40000040d08500d501982c04554400c2c04062a4044d0000c82d50004403440d5045404a030502c400c0800c4c00882200c0d02d21400c040c0c001c0b4203106140c89425101e1441d45042882040805200a40c0c4542103407018001c0c5002168007401c180701d416105c0e1805000383d000109644d02903501100340e40c05030b01c0e0084030075040b603002410b06013054404070011180c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 250785674 1250 250784424 250784437
    0x923060904091b0f2301111c1d1e040b03123603030720030f0d030f02090604090908070503070303060303140a082a160501060b16020105 60
    0x70a5a42410401003003241200c0740210314140000b02c80d05050004115210306541c2000c2c517044600040441e1640854501d402c0714002400c000e9005071403184100c0c07500f08605103008103081e0078005048401e0308080440400d103030b10700891015030222001e00103240300c1003000c0c200d030301031595039113001d400c15500213906480090251050790801610308842a40006000c84418068560b02c40303c000200303a0140c945100c0c031440b803100303c900c0030000361b5170300411802a0424a0341441d1000b20f00e2090b0505490440190513a45164010791200b0b845484014205020904100d00560340c110a0301c21643c0301500180454105800c02641c0340081400e28011103041104000400108100f00040c0500038801d5402041550840c0350040103001640302d4101844005c2c0000c51b040c581144045d6486000c00c41c4581000078060b01010206284680228140d1350010300d07148150205070b05d802c0d09500841c002d21510341e4450a0805d24440d08001140b80c0000d807101c80700643c800c400410301c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 250786924 1250 250785674 250785679
    0xb131806020f0f03041101030b09070e0f0609040c0f02010c09050d1205090310020418140f09031606050f09070614090102030409110304020f0603090c0118120c030309230609 76
    0x1098448507030344603e9030050740d064a20340d8581c8814007803581d25024000745020291007402c030a051465003d042e4200c0c0340c00c3d60348901d6411020030345540740c031001e403803911100a10901070710500c4600640b14001484100303005500301642140f4450181c0440382c00c50740090070b034210004098817448408540f80480f0410001c04205c887c03059a4104010740c210f405030f0b01c00695861070320818003000000c184100d240d190501a007005900c0d261010b843d44401050701c03420803907807000700c868107501c140700810001c1c0c820b114a03082401816030003107118614900020070244c0b10b02400c55038070b010600c140030001d2100c90141302d0341080000a49185401030048a00349911180c40d04180c800d004010000349030003008220661070059488040fc0c5ca0540b031103491030804000e40c5854001880d0818180030441c0c001030046050744d800c4600034090b4030b07627100d000c010038646070b45600302500c010f8000070b0708400040f40700002d2416000826035462880e000d045841000e1120030f4105102556 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 250788174 1250 250786924 250786927
    0x105010b1c0615021b010219120201110d060e06090402061b0a0209070f030f0e030414210303040302060c030105090f060102010905010c0e040e16030602070c1203030b131806020f 78
    0x10011002c2402d4407140d000c0e038024048081174a0760309031200010304070710380c1107602c45101280b030180300c00d2543c22242c0d0804080c202040c1c04e140c007079004d031600b850071101d83c050000da1b48074015150b41c40101510f900480d95441501d440040204800c2c003a00e02070340c850000c00c000c40d0100b100900811a4038080c8007500c5d1500010b40010b4040402122000c010030303d800c406108055051250f06403507a4425010091501c1c0307250380550300e010303074002c0510707849032496000b038190f4410a051046580603038503040c41184a08400f5204c2c0c20a54003180944168004540e21110f4441640c2c1a10000b60400e2940c0e0340314203241a11100261085066542e280c6100001c98001e002e00c079410b16803a140c210380c4018444c01d020071a030700c20031040c0d960341000d5a92940e909a902a1130200d94201d040980c5074005810401da00c40ba081d44840c40c06000c443e000d90030990103070840f01d40001d00301c60402601c00daa000394010b6800b280c002d04001e4107000c1c03280d000030b0712503800b5008000c14954642d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 250789424 1250 250788174 250788179
    0x10c2a151103060f0117011401020709060305010b0901060903050a0201080a020c0105040609170a050301050d0618060606090e0f06090a0b0d080304141501030f08090618120105010b1c06 81
    0x5411a4154824144035050002c10031205040c403040c8000440c0c428a44503000c0480c442401010340410f0194500482101c81c00c146541e1007040408080c28100c3d604003d01640c900d06076000348a0703034800314000e083e4000001241c5000e44c2c1e01200b201d07080009004143c00d03aa0044660790f10041140b40708a40c28460004400002d11403240b20b60f10070b5100041c40c8006003024592030450229105140d4410044200126448826641110019941000b45103403070b24108000d0324264aa800c000403980c1843e4090003159008182268442c0e140c080c1c4803522611070102a078002c0741c0d01344030a01e8410104000b420a48201076215840f0b1200103a0000410001203c0d0303040180251a280c001009210910440300886a1640c6240300103010702e640c80c0c41c3c21450404140b0018000d030521080410911400008035070740a20000e20742659030a0341312032240c4001414005900a00c42514183c0c00010140300d01810703a2000c4000740d040800c0e258103a030a17400341d465119102030f00c1d030400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 250790674 1250 250789424 250789463
    0x5130209190e07030b1009050d050304050d080a030e010207030f0c11060a09060216141201020d020d060612050606030a02090d050712120201090b1308091f02010c2a 72
    0x4072406010660381049050602c040000c058a00341e01815103e4210550071559081d0450400f0045a200350340a411690741c504005040d8040c41d840170b900100703400591000c000f0700d00c00410342810941c03420032280360341042c120700b00c1c09003c2300200411040c80c01c0c4e45080e4001c2d02c900e240c40e44698100920307481d0203808100d403078000810100c085035500c0c030144040c1c1e13018003015501015040c48022003900d00b030b05407406800318500c0350740a06014500075407504000c4d011100b40c0010180309654401d115015030005220038072680d0001180e1a807008640d070090f025940c040c1c000285001d00f1621a0300455000b513020004e13240e400020103205000003001813184000131b00004201101d400c006085c4041c01c1d405c000d0903a800c59252040c140005502c1d210b045030001a6400c8070410300c82e071840d041e502403052084590348966514100070070880344c2c208409000078a680240154000c4400c140c54103240091568090b80e404202500202d6004280356480341c0201c10110420a81001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 250791924 1250 250790674 250790719
    0x140306130c05030604140c090411070501182117060406030209040c090e060702030d020f07230706030b01120e010603080703080604150e1807080706050c060a0605130209 74
    0x240c10000c00c2010040100501d418464032809200f12040d24846141240c5032607d0340c0720780312101c0d00c901e545201c50302c84200382030140c42c800ca500a000700580302007110404c82c5244031600031605a04580091401c0480000200380d1100d030b15100e1403007040c00c0000100b8503c0c8014034039500507686400000240e9501c0f95905c5c003580c055400342000c00e00b800c4d0550159807407d06400c1b0390360f2241060100c9681e0000841d8003180c40c01c0c60058407101c203041000e0141c8a1640090440d040f03060781c210035031826290340c0443d00c80801c102d03007085540b0301f000d03404e440204840d94086401144a142401c465811400c0e42e454448000102c9907201d41c2c2da080250005501030340040e100f4000c00000b4101482400da040501c0c1807807110070f5290100780701c00002c00910754441880714003109040107030204806d5014040250517103200c1a12540700505640116811181c0c0d07200e580084bc80c100c070903125503070688030007031300e040703190081ca2824402940c444800c50f80c0201c42414012014018803e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 250793174 1250 250791924 250791941
    0xc08030f0603190b15150d02160b04060c02010e0106050d1719180e10030201030e0a080a0c05100b03060126030424020c011b03090306020a020303040218040314030613 73
    0x613044081c1c1440c0c03104076407568800d083c5034001c1c0c1c8904014400b40c0e0416058038030f0741500f480d0140e070310600501440c0001d4800c8800404c11000d24041c402004000d810801a4890700d9008100003444120118241c7d0500c1c8281f0f5000181c014200010a0030100d100c42e4070040c3c01040f914001c00f0000124401000c980c1c5d01002910040141350302c100300d5404100208a188140705280c28504620b035800328841c44001d051513135420090228032020b02c41240c1c0c2e2500b00f4085600d4603528407000c0c06001c850141242c00d4000ca1449902191452180303242c03040018009100580c03c000c1e2100d080780494140503001200284040319004041004101524114042400280302c1000800c0c000f81c0c455201801d47d0000c44601c0440e980c4440340040120700405100e901c800142420307510ba0344a500050039560001400400490b0004010750180340309441200080b2805c000e042da01500582d0001e00146010000f0050401ca11000d99081100100030300b14859030b41030610708a44606 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 250794424 1250 250793174 250793183
    0xe13200a090503160803040b07021f2001050c0f250f0312051501031a0a091b0516080d0e06040b090715051204030c0f210c08030f060319 60
    0x20002d000e181002d100c5000c01510307a501103120142802c41080d164012070041d8200e0080105094055594181c42c000480d0041c03400141c541314030090080030003044201030030f01600b10540c2a2012041446041d1040c5041c07030078937042031543c0c018001184d1045d1002e04089649061642d01106c000100c14002d0b4400e90300824405034510b03011301b20072010422450403d18010411402458520040b00b42e24001d20f0000340d207800c40c12042c250f0b19500c2080a0b0021a184004210700c1c60310f40c032041202c3d09000c0710f50303c0c0d422038204c00c8881d403168010b0000150f001c11805070000d4444400340940785581400440c00d041c01d060030703a1408400301c0c0c00741e4201806c0c030709000502c0020b0140001800107541013a0400d4a50351015103903101c3c071140da501c40e20715580020b00f814812910101e419600501c040c07009849070802d100c402c000700081e101000209580e20b641d0601400100015a40c4181c545085a8842202580400c0010f00903500f50040446801d41041b102c071070820000e108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 250795674 1250 250794424 250794437
    0xc020603180f1b0103090203150a06090212041e0201091809240f06061b060e03030c0a030c030c0c02040209130e0307050708151906080129010e13200a 66
    0x803c800b54010750881032080341854074210040c0056180400c00ea42d0401c602c0c0c2c1080500c2e1034074901d401c001d20560380324200c1c440c800b041c0560030b6211403180328021409440b242c0c080708400c10103d207a50303071090802070109003503a100700243c000d150204c04440b020202c0008a24540703842c1c100e2140000c0e0b4040a02d681001c0d0409030300c0b290b46c030a6a20505004104110300c508080c00584040c0d4000000019407040007858001c016107600300840200003138003969141d040141d02420280c01c54040c0501181c02c0c0490501240c0c460310443c4400742d8a5500d00446440d140c00340070003540050207203500950000304840c0f6030111400346e25000030201e8010341e030303070505800c02c1c43c1447c1c2c50b43c001c0d00d525000a07002661102015203040c0c0c000100c0400000b05107030041c0c502d40180002e60140c5140d5081114500c03203041400000d01900403610b641000081001004490203038039690941d600801451001d84e0548203030b8000000fa6103600130000340340c00d481c0d03600e540f01c0d040100e40c50009643c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 250796924 1250 250795674 250795693
    0x220f0602120916050d150e060601170f04031202091809070f030b0606030618160e01080403020d0f0e040513050c060f07021509040c081b04060c020603180f 68
    0x48141d40c0c0c1c0d901411a42c0075101180c1c018030142040402032103110312030303405000070b40244000c0a80c1000c05c000041020000080c3c40305803983c80c0e60f400c581d20303400705d410300c2d500559440c02046203d205030080a0300400c60b50321541d0503650b8815903900700030025420700c0303814881d885603444c0b040249243c41560145240a100c1300307281c0401d0350004540c544501d4004c000068188a0541c4c1119045a90340d03120342e540c070013240061400f03411100e03010b5104800d0100c0200d40c0c1410002c068255036600305070280002c0191100041660000d0040e800040001d031340310f02c80d200caa40969442d01c0e2403155010400c0c001b50030f88505981c4101340030741c1c6207942403c1000401028070041020f60301d1904052050f083e41c1d9041c011100b010b030140000c1c01e814490207200350302310b070300040004004000c2000f082c5001040071400b01c40d03440c5000b4407a401040e161102401352002c0381c0059071013140159807a0b080c017041c1c1c1c00240270301c88012000303519201d2080007800b0800c2866482c00081c03c103c0e9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 250798174 1250 250796924 250796947
    0x50106050d0203060c2101030f0201090603050603030d051f0815090c09010b0304030507061e0b0a080d0e2704060b0108060d060902011707020a11060f03220f0602 71
    0x4509601040c4150002503180740161030108105600002e1002c03541d0302c0305030304000710f80340c0702e228071041d80c442001000220400903010303c03615800707000303030b036900019034507664141d0481d1010f88d00194150f205020410020b0340d03580007103a0080f00c105003021408030761a4403803030366000354108450541109007108214400029540e501c001040020300280c404500403862100307041c01084c042410000c001801c1c1340c01001298100c5501100400c000d01512040e50940300361400002c10b928103140001c5901c1c540810000700ba42c070141c000d040c003000c240909407015035100e6a203a4100d50800300b403000f0b4034460202294612089401284a840c1502d0a902140e200700764050610901ca003d105181c3c0b02d03440101001c07a80a4400600c1c640300c0d00050700c0700c440c1c00300c44c0c58a07240407408104000b0f601050107148280b01c0d401d00107070320b09200101f0006014001c4078030f014110520003d0711001c0381113000c04c41c4610001a04540594580313803003101d0396101001342d41d1260000f03111032010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 250799424 1250 250798174 250798181
    0x60d090c0302150408241f030503070809040e1506060a1e020604120306031101080a090b090d020c030118230a060c0806010201020703080c0d0f051618360c020105040501 74
    0x8000021041e0349004004003150319500a030803040701f5a6050000020001e8849909001e5900070080365254881480e00c40001c0d844964498010350602c184940309010028603000006482640541c0e166903001c1400202d400014a02040000c400e480900c0b0b81d43c011281050391000c0d038050b01c114a050f0900e031400c4500c100d611010186400030801c0862513400440d01c0001c0d0034a40450070b515103107a260042c254441014000c848400709002007030000081e0710382100c0d03a580941c0c0300c42100000301070880380104040990390300d210442500080c0b100c4c421460060000da650000100025209031900c801c054048840c16a1100001542604590360a0740b000c1b0901c000d504d08025513500a01705000a00781c9091448003280100006646801c00d0410181a040030070091401e034980000c0100c0240401010400801052a5510303a52030300c2e40995001140d104600c141c0350300360403128a420801d600000d1900b203620514a25140902e14184a4690001c105401d01c1d0400341d00b107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 250800674 1250 250799424 250799443
    0x1701090212030912060403050412030e10030f05060d0b0604050c0c0d03020405010e0d080d0509120a02010f0605150307140712030905061008070b0d0902061c0b0f060d090c0302150408 80
    0x200d030b0000341008001fa40c000100d41c00e803030782910000900a26480c0075241540c0d150f80b2264440454040740104030350642c8441d9070001540c0302489280c0b581c000340246442c62200240032020510f001410600f0240c02c41900011070784012480d0280d1400300c98100260780009200098000808110030343c0e1207001050100011101900030508540c0c45c0110b074810783ea0403007206904c070700c000b503250042803140081c4c08010842e582e41d1840c08000090080c00b10544c00760a461800401150900300441c404003140c8801880a20b107031500300d8144c813041c002904101c42c181017004010b002908000000e50f141d074840e14007043c0200b03070b4030b021410160b00404110005000403010409490f00049203401c54140205c00da0f900d00960300150080c00d002d02e07020b90083c00004213803540d2450a4642c0ca40b0354800242084204500010499088a503403486940b11000f40031941070782c050780d03010082042c45045d14184065803035001c02c0354240c40044880107644041410082c808092165401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 250801924 1250 250800674 250800709
    0x1a120108060c0a0e0f030607030e0609010e0c010c080906040306020403020906010311030a0c020703020306040b06010801060f14030619091a19140310060b07110d030917010902120309 80
    0x7036514000c4026031440c01100a07520412188807007095150b1103202403000c4c0540040d0a5a0192400840c080c018202d0b011100a983c442c0000017030718210103104000c000e0705101f01070000c03245800c00441d5840c3e10b46d03d0942d1610700800644c951b43c0c2da03840041c001948030302c01c0580c403140740d80100828400e00500845c1890b0821b2289612416504100c0c0c0d804800c41000007240920300c0012898009039420003509032164600780b1081c003c41c50f010510802e0260794106041c1e0f259042220504d10512a440101303200070400403803079043c14007a42d80010041e00c0e050b00c07604060840c0511490590103500b103251b45518102401c021901d44015208082d44e140590142c80c04640003102014422501038407691030009450f9982070020f400c0c003c5032144180b00007074446c9180d000d9580f180104607104c00f4100c0111107c2e0500080110b605905601c2e61045945000340910305030201d14900d00071556600420401603541020640006030701c80c0095481c0e58141c4144110200051580e09 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 250803174 1250 250801924 250801933
    0x19030905040b09360a0b09120c060f0604091e0209070c0f02040209040e03040f0503070e011d18011505151204030e0a0e04050303070801090c0c080c03041a120108 71
    0x710b1aa590780c00303001c2c544408854150144c40d134807405088480704032140246805003104030800d004456020703500a446c000700359400070445900c03603142da200381d8629840741d82014001422152185003250b520010141000c01c8101d240c0d65081141c1e07543c260010441ea0418645000394106000401d0f1b2010090500c1100c40c80c0e251201d8503c01c2c80148024810368000408095035281c0e170b048504410800740c00c8070780317030340e16100c01002292f01409128020b01c00c800b0001451210303480d90f90b040703034a2814072180c8a902ea0130340c18902d0f5401001d41400d050050080815150248180c00c500c143e07112034008441e04007001c03c071101c40c408600e0801850f05104850304c80700040b94094000398503050110003002c41502007407900300c0c0e03980840c00c80340c0601e040006010003c001184916101d903a010700507a2907503903080c116541445850b00107200b00c3e00910014a00000038003100c525030048070708255039011000380c1d060318982690b101d0342010031a1b4811a6a210030035000d04100c40152 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 250804424 1250 250803174 250803181
    0x4060c12021615020c0316090b03030706060803070605160509010e0d12030b0103110f04150c230c09090705130f0612050d0905060a14130915060207050a0608070219030905040b09 78
    0x2d010382001e400323103001495543c14201d01c195010011121901c1e8048014800b180c1c1c0c1c7c0c0c1c0308a440c0e40020b070b02607800d2070078840002c0c000003030b49a880300724041030384485041891100045034074204240200d074008081c02101804a0080307401002e0019180d40c0100b180b0700d8607000101544c05910802078842024846085103500000c01d480648d448180403490155540208540300402610043e05449425180d82d4000b031490301002c0d031442c0303401c00f1210781000c01428010105000c86210b01240c004032828040c0f40381c003110060b0941c0e103d81e07022400d180c1100000044403055801600352000040c2070404121040c07028a00040c0b03241032103509a8a00000304003c1d119900b003107010408201250381410302d041c000c1e2420b42c0000c2c5c403e01c0065884500c1c8400500940000105800c451080001c18900c0000c143c41928009000c01c8903030713442c2c500d0603164840d02524041c150700071400240281200c6500441c051406650380503070345441c1c60b0911080340e0224000070700600144081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 250805674 1250 250804424 250804453
    0x1802030a1106070c0b03070806060711010f030b030f0d1403010308031f030f05011d0106050a140301060e04050c040606050c0c120f030a05070c090204060c12021615020c03 75
    0x11146456048400000506007040014000b8441e0321401400ca00904001141d0801d4800c05107114940c16110b80a068464030200b00701c60103031040007000005080030701c5599500c100c0d110910f542d00b5080100f912403800e00081d0034500e078582881c030750354400d0782107200b07030355010b117000710041440d8814501e5075045031203001c09071100500a650216184101d4070322950070307441d01ca0095411941d860aa86c1d40c500d0128040e188d4a00d884503a89405071403c01074140c103200e401c0455200900d2030200a01d04003209030300c10303032201c1110340c103540e20742002900344020b4a00601c41d074401c1c0d0180c4144210403041008460040d0800010880184041985c218000900d0070740f1060803100004052001d6a00a00d004500e510000c100d01002c204100710720740040240000d140f0a40440c00c5498913022450224091403092000082c502e41d400000700c0e05e05481011550b0b481c2c4182c40d813844a0142e403040c14901540040c900c910112000b04046d641441400310741b01044020b845e81d510000c22 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 250806924 1250 250805674 250805683
    0x1d0f01351302010215070909050f160912060f0e01060e011d0f010303081008010204120201020106050301150e040f05030315011209030e040f0f05010609030312021c1a18010603180203 80
    0x6040e41401c5d0300c0071030b4000d405010808020f069020f03040c4544d28080001003450141a54818203010b068030f41078807014000c10041d030580f030714542070507100b00326900c503000600402003102c20b038281d4a030760101080c2001e0181d1405030a0811040c07106515011558180c04c0300b91008050b001d103010240003a903c000080181101e402d480c0c0a151504d421b124840d07a101a5031101550f9880010002090010132988040c440d000342c00800c0b80a03030b1007040c9400d940c421500014015260310090094036512042c0540190007070300d000102020300d80d15136203180d00640345c612840d80c80c5010000c241d039100b8800309450180c80420b110301d0265030b5001c1c0010480862441c811a114a1191000740e072a03071103007104280f125014041075070345003000390500d280741c08242c0000320804851008103150703008565802c202440e134445190402600c07800140884103000081040c02c421080d030642d502100c89011040185884469500d45540034046401503034034402c005040d4034102d400350341e0104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 250808174 1250 250806924 250806943
    0x9090504020f0405150907020d02070807030506071b08030405010b04110a0906080604090f1a0903040e1308040915091b0215040203010b0a060305040c05011d0f013513020102 76
    0xc60100385030711220341031442507201e485455045034100042060395540003600f5031089d500d540030384201035164a501900c422460002400380d40c801e0000c111201e1080c6c456010000c4042d207640300341040d0b1b07074518625900998041e103880c0e46802c1c07400782c5460320b8400ca000c070385170300b14005140040425026104c481544074204c20300c00c81d40001000c0d5181c2d2341000c280558042500c8802c1c60051925040d12500c4140c107a120300041c0c4c3c0040d0204100008560960300703400100d1119648154050b41c4208111500310b803088000d200000741d20700359001d56038200710b41c030b072681da1118100071804007210003503950808503c424040300ba10b115000b146c250f9901c08103040b00801c540c3c1d81c0c000f1901411300b408500da0000d1160000042d21540740d8090b6000302d220300e494007000b41d40c5a00440f0240004034040080f80400e08074401a440c2105a0400e6074206040124403030306940310044141c1c550008403403222010303503c81201d04840443d581e03030100580c90710000e81191070700000e40d15140c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 250809424 1250 250808174 250808179
    0x2a120112030e040c03021608180102010501060c0f0501090c06030e0d0f090e04050f0a12110a0b1914090c0a0504060609151407140d0806060307050f040b0a03060609090504020f 77
    0x503448135a201740321360100c882d1004180c040d0989141c0700e01d003044041d4040c02c1a0140010320603c64007141d071042c000e150403070700c6170391359240b0024aa031500754210b80b0040c0100c1d0190741c3d0b40358020000b4403081c070f140001d10081c0c800096400e04440e40600740300383c000500c3c04200c0042d004800860708001100c09550605546d00c4055803103142c0640707042e000b0420451540300700348242040084407040101021256540d06a0b50032400e085030307a64031703500311004200c920402e0008101c0d400042241365482c0c0c0ca440c1c0414114003c621b20121844103640f5003c40c2c0c1c01480b0f0791651420402061001070a09660030042c1078a0028028080c0c1200c0c003808008103090140d100c03045105000089040704080d01c559600c40c00c51500c600e5081300f03114004000d00400c050301156130300400c10306120f0340d0041d00c07291441e594103100b1a100e500580c2a80c010700000c0c8000b0071120002405880049604c0d1400100c00e4184540584201d13815801810224108410000140c8440032004407180c000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 250810674 1250 250809424 250809431
    0x90c090c0c060905010203220309030f290115050408030f09060f0f1b0a051b041404060903090e13060209011715011d06122a120112030e04 61
    0x39000c04840050101c10003611040c20b001d5080c05001041d401180540d02a060440d004000031904d061200311481c405808191a50410404611403440e081c0072a0303c20302c1c607100000c00031a841c407800c021680e654644000b50000500c01d9441e65070403915040741d0342c107145041500d080c0c07650b9628071400c1c08200c1c02c0b0718040f94000c080d84509041d100d40c0211100304503100ca500d94070f004055085880103207020340e50070000c0380e01c0c408086001440c1035000800340502040102d0229803160fa03080d100d9030030966462221120041c890f1545015520610010840d00803500b0000c240d10803e800600300710120409101d052007008c07130ba200496a10041c007584400e00300b801640c0c8404003400650002d00c7d2501000040b080309406030400c0d1000362140d010b0302d041c000300601d500720303101c000c0307500f001c0f0400490003400680606240e01c40345090307000c075003170b480310700c642c0038807075048a031100340450201d02210303110b034096400d502520001c4200210031900c0c1e14000d00b16000e07070b0091130240da036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 250811924 1250 250810674 250810691
    0xc06041506030510020322030f14040b0706140708060d0f0501020d111b0304060905090a0609020c060403090e1b0a121805100b030d08190513050c04090c09 68
    0x14540250700195042019070340d1218407440210042d500894204141128102861000f050405032009003180c265640620074141030009803070814400842644040040c8000909400b1040c01041c880e8420b0001080c0031542c000c16002030180540b903d42031200c8981000b42c19207920700381c00c4025400924a41d5818030604069009114100c8000e45007410b148012401c001e00100030302c0e090040d00204e0725152080490a51240114010b00f000035211180401152402c0909a60000c1541e0000100c40e80d0380c030800404c80c0d11081504009401c00410481032641108003a0000c01e100914210245480320461030008120010700706d084030301252400110b88a60303100f2181d44070070303801008080b1185074003003100001a03008840318072906501120301c102d070f40203001c481d441c060001c048003a10044284c645540040c43c06058a00380c200401e40023455010386405040480466840707556a0300f016820400e400320202d001d0f074200500180000c00c4170001004076000840300280420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 250813174 1250 250811924 250811963
    0xd2102090108130309050a0605091002010b0603130212010f1b02060103050c210607030f060501020a080d1815020d06060e0a030605090c0405090304050306061503070f030b0d0605090606060c0604 85
    0x1c686c011940000f0826000704e041074000005103101c0c44121411941c070f18000d50200c0c26600444505d5821500501c0030403031600030b0310803004100b88000e2640b4080c040584105086602e8040b18582c0309489000d041c00f048201c40007501d500748684041c000660650301c4407581c401c5152803c6008070070f09046400040c0306001c00c01c1e50418110183c1e100750425060003000b80c0852038514400381e190480004040d0300008a0440d110360020340581442104c0a161000b803031a0140044060315101101000480c0751085207280010b0789030058503460000c241d0b0046450b46e801c82c9040c0501c00308045843d944101c2198110385d40b00002048541e02c040c201420f0218100c18690002d017440d050000101e000b1000d0019100c05400302e0315580c0c1c4100800c850710046281a0701d9604017003012a00140c0301d821940403c0e090360801103111014100401c55544903800140e401a59800a00c403290809201c0d06411520072180c190500c2641941c4548810005c0c2009000e500c10020b1f010211 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 250814424 1250 250813174 250813187
    0x110a03080304060e0106060201140115090b03090d020709050c0306100e030102070812070f09060f030219050307170615030402040f0603140706050f09041d0d21020901081303 76
    0x456122011075268106890520040d20050092a1865003040e00200e40a0703c141f242c2000000c9a1241c0145039103401f00d0b2007845a0850120420000c2e03000000c201130040c54000d41c06400f54a00411070011100c3e802401c040540c1c1101510300d05140600c95441580b0040c0c0fa08464101c07110490070011400c01e6841c0650100095015400400c1200500c031800000d8140c030ba002012900c403035a502c640c100d0b4840520b0504101040c0d50050070300040f842003100308013400300c6003001403500e10580c0715501551158601c041c0011000010010503070f5210307144803285e0041969002c9141013140c00590810081d4000881895000c8002800d55139190484440c000090600304011600e9050102124442188000d1140714800340019079500c03850840d0b100b40d0b0170150313203400d290000f4100005080c1d807201c0040130f041c518071103010480080c441c0b880d950075640c40382d4220b420004140300f8020100d04501054074818070141072070f030340c1005a1540c000c1d042203116142c1c41c400d2038265000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 250815674 1250 250814424 250814429
    0xa1704180e010b030d1d1c030807090b0f042d06030b0402160b0618071715090c09130b091302060403050d02101b0e120f1b042304110a 59
    0x540706814114841c076821044482d100501c006e48900c46150b01010711248034824004054481031141c4550040381c8120b104540181c601d107015447c5550760038000341c8503000f80c9000c004d080e400207000c21450715120382c0c20342d98000c00fa841c02002c01c000c2e903c8414501161041d101456202c42c5405000d0341e03664111020070a030300301294558a21403d10364424081203130010301410610070141c1c03601c40c002201c184034040d99952a19000c0b4040000c0341002c0c005032402c01e0030506102003030f00d1507480590701d5215441014000c0c0d101d080e0401000076080e40303080810440380c50700401d4510fa0b01c5000d00c641e03028011000928450816101007000c0b880341c0d90015000340101c2c0301900d1901d501184441e8614030482090080c0900c140c1c1b43c0020340c00711800603000c1401c2036240769450901241e242149034524050740c101c0303642c0e104c3c03590802009608002c0e09581607034803c4113078074080c456a06414100f25190305203e406140d00c0d040d0080160011305400e90380251200559a224591400b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 250816924 1250 250815674 250815679
    0xd0f020705010207050723040c1b210504050d0b130c0803030f01050a140409031215261b040204150201050709080102130320030607020a1704180e010b 66
    0x16a00c445003081c600030342150b00c0c00c4580d40a03007400010ba9250721700e4080740c40c10740076401c0c0141c1182035040000400c03003060450240040b0200c41e8044a8000d0780203140385014201c4250408a0b41c40b5050700c00070341d10003090a00c40c0601091080c0e0300c4991401d201c0c940c0c01302c1c00d11582e84898107440c01403030358070800806000c21040c0c086101071002c0080c6010310003115036040c20780d8030b60040107400c450500a000c208030a00140c0b181924040e0030181d1098020b04180c20388058071441d450503155100c0c10300d541418444030410a4641d94880d44607030520000104548a0240c2c50390f5488448605090b07150905c401d52081041d507030fa0341290b006201c44107143d041100b030000080c0c0a0642200c0c00750200d040c2d100c0000340540c040c000c403801c2a01d0b5401a00f4100d040d03541c1c1401c8400808105d1160301400d800c10f0070603460400c089402407e00d40c0041c0802d404514242401c4048000e540142e40400e120402c000b8280340b0344d0755100d03551540301050103440004d05a0040002c90f0b522503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 250818174 1250 250816924 250816927
    0xd0e0a12050d141302220216031103070323040803040905010503060a0b06041206020705120c1009020f0108060d0b07110d02061b1c1a0109081504080d0f02 68
    0xe05040e003060041592210410080c010b181e00100704100c150412524000c074a880e0620305070040c54507400c508000c115103000c0c0c111a01900105400306e03041499010703030070b540003050b0b00c00341600b04000340c0d000c2485074002d500d45000c640c0d0040881c01e5056543e00090607040401010500004c10b0b5170181c06440b00300c07030700c80c0e0303442c1140701c041c2c102846090300a00038280802e90080d0a4052029525006000305103030500d01542441401e04010303042d2902d5509110340740c0010410b002c00e00d0032004e400d0a5035121490121a641420113005918040320716080c084001a04c840304428150802403e00340340c90342e604004140c802030001801006012440204480c3e240c10050035403d6441103002c42d40b443d0000038050fa600d940c10390303401d07000c4040081c150000042990080101c0c001101103003a0f64203e4a0f50740b0291040c3c802c0800192000000c0042a541d000044030024107c050081291150641c54990310b143e0240001e41a00000100341c1702d042c0f4140c0245403c02040c06045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 250819424 1250 250818174 250818203
    0x130b03060a0801020f0a170906010b03090115090603030e1c060c030b0d0b0403020d050c03040504020904060f08030d1803080f0c09180108060c0310060e1903030c050601060908030d0e0a 81
    0xf031742030340a00e0204000c280c0e115291078143c0c08080c0414816001130340103000903400d004000c5210717000100030288540d203d4003041145c2003d10880c10040070b0f000008140d060862902901000384540c0050044e448401c07004001d04420002c07118603600a01c0010702d0180c0c001048020380309418086402060b40100c1a0030007400d428420f00c1207029500380c8040100665045500d03119a142d45c01e5250300c01c4c0003d000c40d182990040c40c080700010f10005140f5600d2034903201301ca4182c0d02000c400e80020a00203840000e6000700070705158050440b00b04460300365000351492501a111505110100300004c4040b201c081c111030b20000005d1605411a50318522100448800d01a2552a000d900e000c1203075903800c901501d01500201241128050400808036441d01c1c1d10103890790710005001700c0e02644410021540061802035071003011000090800d0fa203849010f03400201004900e480400a0038000300c1a1461240c0e072090200e0740101c0002142e21701010510003401403101007006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 250820674 1250 250819424 250819447
    0x123420060f01050405130b1f030803100803090622080f0a0201030f09120507050a06060e18070e0601120b0a06020a1a27032a1002130b03060a080102 65
    0x45520448101806110350b80c0c0303920500007a00c3d0305a40407403810314072a258000203900c03584050342c0054641c49801c0c40511100f01c81d000c00a96900a544089000051241c031030400302c1c520000d484540000e510300445103010031400e200700441c1d8901c0c2c1c10300410311802e242c000920403006040520032a0340700611119055143c01440e031049002c07030328101d540000301311389025640c0c106030001c0c0690698000307220181d90340c2c2d10a54041f03d9900580180308000b9100748030705005400b003007a4083d0300d458400060820b901720705884e0440c651258008101ea91340301c641d15988140b081c40c00d00c20541e24140e141d0040c101201013507501000c074440c04a003265002801081c418000c590003110111841c0c070f0181d07030001c103460300c0500c020790500c201b2601c01c2c201459001c0c6c92840302113a142024003041c2c04015204038402800820341110842d02444003040006491440380004510b41710418126419005141c0304104007401d010000807a203a03075106104000b4900c50f4000d40d52440290344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 250821924 1250 250820674 250820683
    0x3031d0a0305060a180f08090118060207060f02061501140f0c0303061f0f1407231b0a050d03020c09011202030d0e010807030e0705060a0203123420 65
    0xb4584401e61600014944426000e89441c1c4051b800c04c140c030010207080c0d1241400c0c1d5000700c1280b414411a84400e080c0202d8503201b51001344000d5024001349420408002c0084400310300360740465118800b44030300304025000c003880c003038000d0801c103101e1449000c100303440c0d000d1401e05c401d07100f2003ca1010b00d0710030040019481104111011a074050003c913088a80c45400c142ca035000454509007401d10030f000348440042c240241d100350341424280d5403452528040340310f260b120032900c075000d1304032031508201c0500490341d040301030f607507410f403200224542d2010307885054800c0440f5146541414001d000b01d0000850207443c1080942c0c4550600c00c50041c1110128042d104040c0494106849856000700e0785030140d4400c0a00c0e1034101044000e089800381a500c0c034054900005000d5840c5030041400303100540265499015528001e6141140101515949600504580f00c1c0203400c020006504109031802490010100070454040c48440c06540d1401e54030f09940c0c05080000a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 250823174 1250 250821924 250821931
    0xa1106090319020109170c2404120c0e04080a0f0e030a0b0414030a020d020d020102070b0103060b0301060807180501140a0e1902070606031e0b0114270f0906060a03031d0a030506 78
    0x21480c8c1c4804480031a0345400302ca4800c1d604010003020f2100b40039005242e00000d841a00480708a2039086c6c50b070039041411041600c5c00c031003541b40003c0b103208558001280140308001400c0400c128006000802d441e011100b0700207101100b103e00040800142c0c000c8008580d0044048a48901c94000d000e5620300700a05c621015102d006038900f89144140220b45406901a0008045920f181e4494018002600185034107548412011031002e07400c0140710000c1641d48a00006485594101d40803100103030820315042121010307581007501c2d01559035044543e40c130024450341d80e4100c00f100400305408442d01d001800003a00100f444081d070011800d50303010301e03000c07148068200786070aa500d002d050020076841810004002c3d400704020b00e803208500c0500002c0998a201072003008426100c2581c0086038604018003001c44100c11481e0f81c40318501009200c181080400144081c4407031000500300120100b4030b441500d4108000d01c140e0101901c1020010307117034601262180007c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 250824424 1250 250823174 250823179
    0xc0516031202071a0f090301090b0a0203060109050405150d0f060501030c180c1e020a0f1a0c0703020a0803060409020310051b04031119170a1106090319020109170c 72
    0x2030f00085240740d02000c6183d6051038071034a2900d854164008500690060300b207040d415541c0da1504408520943c54940c491a00903500503a41e00c4d00c280007400450068000d13a0140e0720f40740030072011300c460b000d42c541c5c0020121100043c082d038038509000072100600000f4003040c01c0c0f00c0004108a80c0d5100350341a030b40300c90304401c001706a2402c0002207034013040d0001c00240001e03101440c03011824219000709241407043e1954614107171110324550740b040360304403210b441c81c0c1288410000c01c242480e07045001c0c400709602c0c1c40340c0b07903d00960701d8010030005803140d580000400c69940d120761020340f400e54060305a54421381404841c000070141122001d4039280302038008810030503840d0403541a01d900244c252030001076007090240c0207000b1012080ca148043c0e030081440b40505084014580c9000003c004170031051419241e06c2808907170141c01003074140601c114550300410501c0a04ea03004252600e00d4206000407a82d070303000c2d03a000d0490034104c411200c002d00c2002c200d410250509 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 250825674 1250 250824424 250824433
    0x210321020c161802070f1401020f0c03090a06170106030b0604050d080703020f120d0504060605090420030316020f0a09050c1b06280e030a0c02041d0c010c0516031202 73
    0x907440b40f030b02a0302c1500700060604100c400c94400145d0599100841444281c000600303221317040690482541c400240d4142c91ba0002c98084014a0311845c820003525052400f510900c0c081030004a90400600402c814162280c40003640354a0344010380f00141002006011003010031304202840740e05c4140e042d0018010742810200e075680000304072519103c0414076030328040c600d510201c001c14000e001105c9640d04e44c000003a03203666507000207001e5409500c50341044203819480a081040155006009810230701400410400d0011401000c98064a0140480c0300d03c5001468401054002002c494900802e0100b441c201c040070300300f040c80d00c0007100c18000e072451a5958446046400903280c400c15412400c1c02040043d2a0007003610050780440e10300070b4951224215084400c911001440d844e0040342946818001d60984018411401c404100d8000b8019100c007810080d40341031200352281d900400900700183e0491041d0100e1403810390f6102c0c90007403003c144403240680184075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 250826924 1250 250825674 250825709
    0x703020a0e090f1303020f0d020f0d030501050306010b070510090818030613110d08030f040b0a05130602030622020703091a0d15080a060501210321020c16 68
    0x300205074a00402104031010041d980300b0400b12200c41307540b10101e0460203404d40c0d0b5010341000304002d1500076801d8010300f0aa074850003c8501e0820240e0950007094104401000f4035200421a1030643d036640d0100c03561010a42803080c6009611013107080081c0ca040000402e000e00c0c2d40181490710403c401034501c0c10000c1e41010f64601d815122100b0300c0006001120000301e221640340744084e07000d0b0a0204101158860001d00d80040341c09200c4030b2840820801041065281c49920240351f560400c01402c00c0311402005070a205002840039a0000214130642d1b502008241c10742c0c5401c0d0703107502d030040e554080000b940154038210042070b081d103408941d01841c07041100c4414804202c442c18482040c00c19000f0301601e00000c4c2000f240084c0100361914107022450600b4010540401e441d4545012802040003600701e034100030303030582028000268840f030702c10142d0088521105002d40d054000344002d00ca07000c1a010148982c00803441400341590384030003102c80c811000c050040c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 250828174 1250 250826924 250826929
    0x100f0906081203040c2402010507030e0c130b1507050c09070c060203060406031406181f050a020f04060c05011406090c0304050a05010509010629040b160501050703020a0e 75
    0x2011801400c80035003007000d00c41e00780c2c40888051a03201c0e00070240840010340da00c2803085420840541100001102100c0e03415150b024000d1a4200c1d80c1441d0802002c40c40301c003656210550050703101e10590034800c1080c0180c801d42c01514603400028001450241d20002c1c030075071540302102c1240c15000e1403070082134500d80702ca4101e00c54503d540320200c40444d0399841500951000f007066904c1655085c1c040003041304000c00c400c0c0404c0740130041445051140985c0003035080102c0750380c45944805084d482882c83c0310004074454241843c041030940f21342160320045d01810281d1000402d0100b00041d40315441080780210a009038002c101c85201803540078003048003100c4054100c002e840106115040b403900565006010303609a6a13031a8040d9106400d440b02660b03d2640d84c0e46600050002981901c1141e00c2030000c3c0700340440078140024504024051340c41810180c1d100411402c031101004003089000a900400030410f43c580b0500241c02900508009070020b00600d40c41403850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 250829424 1250 250828174 250828181
    0x5100501091502030d06030b0402040e0703081909080a120807050a1b110405091b01031505010c051002040810050601050901080105041503051e0c0a0e040b0a02040e100f09 75
    0x892069441c80801c0c1d0519800c1124019030048510031440100001c0c1c104018510902c0301452107184c18113440d00749401040140c540000804d0103e80014070304000040500c000c840b03219507002c0f000e4041c29990003013036403540e44030381c4102c40e9802020b803081e04000300743c0094803a0721f0290302c440742c07580c8414030704a905001c1d03c1000310110340340b08098249520602400f50703110340305080c2804426440000714060301e80a0312041255881100d071300001c1461540803202101c1c0130301c0c04100c5142e00010400807113480e8843c41d8144942482076000344402446200c07401c015840c030966a13903a4410800d5642e401000900e24440d141501040541d071041d4200e601d5200d05039070781240c0f0f900786403c2200400e665007850018807400400040000d20078031075142c6180342c4803103000e00f03004500c038002d0900b42004d80c210b20680e0010070034000802d4551503a900180c00c0381c810a019a11004084001c0c07141d0340040791410103110800c62032405000e0401c054a02c014a158000b40d510512202078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 250830674 1250 250829424 250829429
    0xf060718030809150903010f060602070b0a0c020907090e0709050102010518030307030b0a09090606090f050108100b19140f030105090d14072a080a020a050111151005040510 76
    0x2c02400c004203d02854082d5000c941901c00c014400e21300892400080d00b103900c1c01c020380c0d08450300c40c82e00700b00c031a8040c80941c000303103804403105141c03181107072000304184101800284650503250210700c100f48209123540203445094040741c0d050074091800b038070341d8040740715603401503003880001403004035503030740b0283c460100c0401541182ca813084150098442080019002012400002030540d20340c05540d0b811400307140e0014520341081401800d5507070103190b40039000d0409004103c1031200113201900e01081d403070002034079002c3d280001e01d4161a00360550652201400c00b10709504104030360f40c89604110b542a605201120034503003a03070000c98a640c841e4110100d8085880d028005002c911403071040194500f0781aa40c0d9002041100070000064101d860304140c1d140c1d141404400c0941400ca00421042c0c1c043c0c0d0019658a05070f00a01d41003001180d0444020340c4200200c600882c0d42d5516403246241000c03503c520034030780d40700d0750b88180e05090200f500d00b040080310805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 250831924 1250 250830674 250830683
    0x61806020f070c060212030403050a3f05060609011215090519050c0a0c0507080109141209030a08091206070f0e06120f07110d05070221060a0b060c0f06071803 70
    0xc3da5200c9d201a140d907040b400d01c0f40140300d10403d24940010401e17082e1030305050740f60203100d6200e450b0407844c400c5100d401d10100505103441c060042c142d0310721301030341d041903000d1030f00140404800309210060401c444001c80403260782403010540d0800354001d00e12a409249074100c00101070304100060303502c240c5030700c07203200c84c04c109000b8410701c5500d03e00e90041c003c0b000c43d10b0503980d54030350600310b444110040e141e0350110010b01505e407000380040a155040d513550f050070815040d0020741c5840b8454001440310b071002609038034039216202e03004e0031880d0310b00586c0d02c0e40c034007502c01501410812442d0340c0011080e6400c0c403140c1c640241910580c800502c00090142e440d162820b4080002034500ca060007400c41c038400d61000200442800c000142e81c17850303182c2c0d44900c14403800f905800e10f450001450116182040c181c00078107941d0040300c0903030210321b00d40c00307401107002840b072100ca05819000b02c011007444040d000904034000c10107031392440400e107203924a50301d403e5a00c0c00000e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 250833174 1250 250831924 250831927
    0x30c0308091b21030705030702031606080109021e1308070b070b150d020a0f0303080c0406080601030c09180225051905100501142b061806020f070c060212 68
    0x80c0541810820a40000c440305200691a0b44410301c451445e00056801c55085e0b00004281c021820244200c00c003d0400844000c2c400d403d01030040d004030382c1400794414040e80441c0032001d9a50100c1c080d01502d43c1c1400d41e581da41a15550011100e465004005442c820f20700c0014076061803c0444403c0d0703801034445042030b11001e500d500c002244410091303000f0608540f00c1d01503030342c01240c80300801898501a4a2501d0f501d40a4503d02e030082c201c0d900144c06100070400e0b0764120070740c11b41c0030341e0910b0006880001020180e68454050f00400c0e49a070b0311080800c108501c560042c80922401a403c0c01c2c0c40034a4030100c9086a0282e070300038920b4202240c0403111105001c00f0605241c481d0090321249910003998100300c032401d90100e100480d0b15805002e45040601e000e20869142104c2100f4841c040b81c1c13803402c0005400b0f0007c1500b079440c82c03100e4540c180144481941035001c80d00395a140d0084010150a401c110010360380741130745210001d8014000901001c520080c02c070001e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 250834424 1250 250833174 250833223
    0x807050112050912120a06080610140a030605011805060a0501050915041a04030212011b14190f1218060b0d0b0412020f2d030d0504030c030809 63
    0x10003511019182080c54461980c0c010324120b1200b014203415403484000045e2850101c0c100000d40d0100d80c86400c00c0e800400c1884201101031340182d040e55101c9900c00c4025492401082002015610141010380f4180021076003c02291003e010300c1d902c41c0042c02986c0b03d203400c000069040b4412140440d00402032032581c1d080c001c8812a45081104d251030a20756240041c0340c01032140c0380b01c40150640002e081c801c6240c0102c112107208282c5000704804d1522544520008000452038014001c8810340d5500c841d05403411205410182c0c0181c1000e1009988080c2c244820301c110346001c2000c415401c2d0001500d4810f418461011307000d01015400940c880350f00809040550710340000032500d0100200b440c40f280300d80101d1081c00100c81c40000f1400090400b0011403a40071a50040d40e80102910340742025131420320071904d0036071402e20404484070320314420b15005004190512080006260700018000c25a41c025142c202c51039a80480c215213501d01c10140007a170700c0c1e000812 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 250835674 1250 250834424 250834457
    0x60504110f121003050d09030b0f130809060f040e10060c05060c0310050d030f031b050711040b030d020309150909041115121e19020304030c02150a020708070501 71
    0xc10740c0043d98000d5070200e40c2c0d2a0384849050a80d80111784000c281c41c020704004002c680d07003070b403a442213003401110340c242802d13510070400c076802c110302821030382c00130805050940c1c80c2e82c112100c5a09501c029540c031a80c5040800140ea0110b492110b00d0010314000220309002d28810a01300d94050058032066035070780d10011042c0c10213401421000051040030505403626800703903107a01e029480d1407480028030040102628181141354000082d0181700c0c0c40e5054200c4180c0c0c02040d070114899412401000110f4001d02942e00c42580c90710506003440401a00803005004200b0255400c8000341400007500c5003c1c0304007003116070017081e00b02c0000c1c0450000c0300969420b503001400380003e07480c0d504c4a9051504160194031001c0c030700c03030184440b0496000110500781d0410101032030703d01d4442a141c550000030300014001c42d80000003c0c0805101e250300d044407940c01070540101c2c900c01501546180c100078030303940162085800110380030a0014118040b10b05c160748845141c40c44118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 250836924 1250 250835674 250835707
    0x1050409050304121704140a140d060506041103010f1d04020d02060d090c0602030c070504050606070b040f0602040e07020c03010504080a21050a0e10061a03091c03060504110f 77
    0x2130507179030054200445401501042e0092001f825000304503050880c401d0204010005154002c900407422501d0050480e1102c40e400b54682d03030803100001c0e050f500c2d4008640a401200741c031507062040000042000c509a40b4420705803081e8400304103c40304450030805c0c520307809a030065845155030b86183d005140c550028005084403180c00318082c03042e66911300780c0703c0c0c0540095026810200f900c9805010400c6041e00414040741c050186040500c003141261041030800b4011011620000d021701c408076a04400e07041e0300520842da6a581c440058880e5001070381c0f150014091040c0e0048503103014012a80101d2300403284030715140180358103079001c1c0b01c4401c4c0403603100040301c546004903469214440c0300c0c444140000c500c0c003100000c1542400750103940030308014600a002e0040300c4040b0034601d00c5185002c00f003582d07030b201c40341150f01d4510340d8188004009a1081c803200802d40c03582023035045903c2a1820722880440c002501403600175003020000780c0805100c507a111004003103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 250838174 1250 250836924 250836959
    0x30304120807060e070810091101180e1f0e04050706120b0301140907080d050301050d0c1e03051014060603041109010b071101081303080703020405190e01050409050304 74
    0x5645520b410030b0381d9600015101d1503070350a403d0381c0001c002084283d80500a03e80c1034400c0c007000b0000400070b556940a45140303444031904110342da100142041e81c00b000602e01030109100020403d290825017000d8050011130031300c0d060070464900241081e458212540a40c6d44403000d0030030709003410421030b41e013002e28611640f20ba858030315102c06502c003840340b04070507070844540c4005858440200ca18250a9500404c6554014500410196804021f913815900b041300c074002200114140880c00d94060b0300072040400d05649015070403280800d25a0403244500c01b61250140441c03032403030480c2d0210b0400601100c81780c000581c0751505000441e8002d1041c00c0c2008038450000101da4054000d0300015946440010a01c00f413120000000c00400710902c1c2010b01854017112400e00402c0c1064010240b012020104007000e0081d010350700680005008030b0b0841100402403820b00c2c50501c144070348111004000b00399810507000700b030303602500580114907043c40c1100c072414007103044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 250839424 1250 250838174 250838183
    0x2d0c020d261005100206151002071404140901020c070806060a03020f0a09050f0a050a0501060509010c03020f030307092301080610030b0d060c170106021f02070507030b07091403030412 81
    0x110000f0070555a501d206100900b0b481d0300401d66450420030041b42c0034000400301c1e200320001a00c01070800e81c0044c0178402c0e102408211845031101c1000b14015000010940443e01a03000400038100c0701503000c1c0041223000d1003117138540b994900c07049441d2202951845c0d005087c07a5400c2c000340c1811031220030340d54400790a0031500c541d200500303411600c00b928029400c0c1c0320581401140011340c0030340d5030051382000080000f9450440041c0c0346100c3c00c8022414005220300340d10501d4002d115024800050400f43e0b603591030322110040c0084814040d80c1d01480140c0305800d10141000e206480401c03041c0c41d20345881c0c0303611080240501c0f41160f00c104064640010147c692039180004034010b210b108003242d0a40c1c10180070700411034041d10074041030420001000300303a6000440503d0110f5031943c9600031820b198221019209580014145200b1081c1c0001005600401140708080c1551078440b81502c483d01c0d001900940400c550b450b0307100303200a100b0042c1544500403014440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 250840674 1250 250839424 250839451
    0x62003090d030315140108010909031106010f081605060901110715081806040f11010314010b12060a0b22050d06150611102d0c020d26 59
    0x40e400546068004041100060748541d000c1400304000300040004e4042c40005808940d40d1000007020504144140640d00c3d40301e1105409040c0038080c0790700c91480302d5040ea2000d41c3c40c1d0720b84452010a0b4440e0480505c80c001a081900b50b6110b200419034100130449854406480011036454068080a00d16401003240c006112031400c88520303441c07085030319051007515000d41400b03666901041d200045401c07440800c00051402c06080d031615030300c001101c04815020300100c000740105a21100340f01034a0700082079000c2e10074040c00e00180c844c54801c00c551340c0d00c42800240b980e40d2140c0e801844e401e01044a60300494810325050400d10350031662002c0d42d030030008400700d034030410564010740d031130202c009546103440021001e4185420110384018640600c1780c0c1e1b0700d004820805800743e81d00d110111848501c0ea035010a00e101102aa102d070104e111503130001d00050a440c001740c411000e2507003000c0d00642e0400300c1c2c81034000585003c0d4440401544514500034040000c1d8900c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 250841924 1250 250840674 250840687
    0xc1f09030f030908060708161d01080a020c010221010906031e05012007062417070503060c030f0f04020a06081b0f07020901090627021201150e0109062003 68
    0x90070014944686851f964440300340c181865541c01d41100070005070104100011024003242c01e9150782601c0030001c0c80c00904030f5440000e50381c001d0142030042c184650000504201074078200460104526500e9900c20f4641d0362600c80104661a51100030407005064070305100d860407100450200c1c5000d0000030604e00d000d40601c1c0841c00f4280c0055401c050082031940034072170184103c10a0162581c0e10303404001e112031461000d514284650f08415113007603a004407002082c00020300815006c0c04441e21824071989040b01d0307800c1110415000314501e80040c01400f001c1050502840d0090030302e424490034004221004240100b14410402000b03440200c550340004c028290001c0d801d16681e02c42e6a40c0c410019452010313400000042e007043c400340440c058401550070300040c07540d10312800841d40080c15000c0d0090340c80403014004024000101d002552781901030b40b50480c0c0e1015183c1100ca00152010f170814090781000030f204150306040c964140950006c1d060f14082242c5c103086 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 250843174 1250 250841924 250841939
    0x30b0105031c0503070c02150d1d0304050f0d060c11100207030f050313050d0504230303040e060307120507150503070e09070c0b1806161725020c1f09030f0309 70
    0x10120000c85080c54002944032a001c00c42c03184601101d4056800a0300c81c0320b40ad1019540d010300e010b02823281c0315a801704d900319070700c0f940500c04e0540c2c07018040c8607013948011b026000c505031611a0f5040c0c01131240d4492040e00c0c910890f0000c61b403640700c0074400c054030300c0211445d8100400c6031050354060f0154401081c0204900350414440e0350315941d4079803c28600700c00030180e248581030407490341d61501180359000310030785054851b440d0100300217075210300000c1d1034038903254800081858184055001d00c0400706080301910b022802ea42d4040340380c000200c13240d100860b4040005452948004024541703001c40380c4d0080202e144c910305da03180985134200040b8041c3d80c42607104001b4984044900c0b024000250302075201c6924007110101c503240a0200800c003c6071002c4a0017100c001003480c4071085591400c410700c4540d0000302801000060741e42d000c180d038024460451007403000c1c1c101060000450a2951035681c505403685113580701c0c114092100422000e021a4850228026 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 250844424 1250 250843174 250843189
    0x503090d201c030b01030605030304031407050913110906060702220f0b030106060206070c0b2502162103200a0b0f0c0712080601120c0207030b0105031c0503070c02 72
    0x10b0b0b00114501250744003420024040329441d022560601d420203608014540d0003005135011250800c0444103c007414002540c10001c20b5040198441049418009880074490b0540d10040c032910b0012a0f01001c0c03420030102c00350484400d40c0c004810007000c0010b040022408502d0040d44888401030340c0c0e410741725026034198106e15000b4aa035603040c5045403400b40251030081045001801ca41d0404650080c02414440805001c000b400c4e400701305031f140100a51501d00c04060003908401a90b040001d40f0760740d041c01300340f00e900488640400c8010811104207083e0141c2003020514056a98041e246455031441c40000d0400001481804400921038101810310030302c07007103c2902e071088501c40318600c042c08010310410240f1001000990801d4403000720451810900320650710800100e59903c60403502c05a41d0382400d044c0b00495400140441c1520f2182c0403110940c1e0304c8100340340ea90314103038042281e41e661440425011034000d00055400403230601e4aa0704541041d0041040d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 250845674 1250 250844424 250844443
    0x150708060d15060f1d0109060b03060910050d14010c140a1404030606030b0402030709050f040308040203030705010e031305042702150a0210050c070c03150906050f06010e010503090d20 81
    0x28004000c5c4c007002d040c01507854050421002c1c100700c42c9082060100f80c0313010003401140280c5100010601c4000c1c1c01041c00c0c010701c00100000400d18851900300c020100552224032150700303051022680c28000c94680340000b00d030300b025904141d215082282c101c0001058500b92078401c20000c80421414080c04010b94050081c0302e03181d00746071050500e004d89a03031005c11110f140c94203120b040c4a0980c1c000b0342054042c607201700075807070b50b0001908500c14104000d003617600c0c0a468090180011001e008851016003a252071a55100b05000558100d4084d8000302400c660507604061402d01c03d04401c0b50026108440c15100141080f500f0360190114001581c08980500c001280c58092a030b44022203943c074034100900703079603501c01c00800307404002c2c0185442807041094000c07079400800f10b0358118205003e0750a1800f80c0d50a08841074590324002601c0459804095000e14120380c0540c0041380140003030300c08010110780f8500d03103000180ca140c10412101d503542000300080d406 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 250846924 1250 250845674 250845689
    0x30e013c140d0603020a05060a05030a020f042103080603031303080309011e20041401080a0f060906150206070f0309030909060308030a2417010b09010602150708060d15060f 76
    0x90f001e08600410038401c40c2507100a02c00d010801200300711742d500200b581c0d00120b1100c005612804400c900080b80e015680002e10019001c00d54030004030104000e10000718001d8548500640310207041c19228030990651a64008414208000003a1082c0c000d55011000c4400002c00714203031404241c3c1c9140c0d2405400c003031515084008212000700c5000b505405210300964503251401c181c0040010842070701c40e051116001c001081d1b6402c82d0412914008001001c102c040e80b0380000000401d05801056021000c4140c5440d4990000070120b02501031904c810b40451030704602180504100b1104504114444100060003505401028051445070000a840c0d250a000030405c9401d09500c9104542d01d003a0300841b80e4202100242c2a140703e00c00390281d580f845000c0a0240094000c10f5400810010002440c1980451429242c4411201d05481c40c1c44652084480810940f59141d020302c519040c80700040724030f000040034154402021611694801801c1d40c0c52450364420701 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 250848174 1250 250846924 250846931
    0x906010608060a031a040c24020f0d0c0f03170a050f09010c141e1306022b05031e09010c0f020a0c030201050705030f0403030e013c140d 60
    0x312a00140440da01010540300310100a15580301d46441101d01c0400810b800b0000001ca000d000405240c480503000c94418013040c00b04d0800c50002c103414907282c49005010b1900c02051440c400308211010354403540c1e82c2e209030b204039116000078086840040b0140818110301c0c08142c0c8810042031310804a485000070285040e900311141c0d80c02c010041d02859160a1512130569082152101070500120744103846044d4a4849600420340c090f4807584180301003014400003808400640503034126a09a442003250190b904c41203818401c00680d030800c20b2010a0541441034001d150f0000800c1014500305038807442c0c401942109030344041d06a51a03043e2121070642000554400d00c100340700406046146440c0c03016120001c3c08020b040001c005039090901204209403503600007400491541c4c0c69591901504401a0445540c0421548800c050300220a6001e0243c180c00110302c0303182c0d25110350244005040712109481c03c0c00001c00545071a01e8904e40030700f098201480b03000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 250849424 1250 250848174 250848179
    0xa0e04062901020d1803170d2007020d060b09090d0e0102070f0504020c010b1903111206060f01021905030706150605041802040b0a0503040c0902030105030a0f060b0603090601 77
    0x28001e001c000260075450031100c08440c0250790f4001075403c4100ba940c030b4014040c101c424a4450b8075540c0c1e0340090b010307152102000c031006005074010644d1454030b54080001e682c1524100c03030988900c0b10720303c2011006100d40e60140c04c2080b1203c1003144121400618418841c00107405a141954071141c16072081000c1c00e401d0360040300c5119694400d00040c50301ca403074100607103003038203242c010103006a80106d61801c0c42e2100f50803458114400034007a01d920313101034080030112107141c40141e803d00003900c5181d005d4184400480a4aa001405003030f1659419090061320103000d04082d0451240002c43d802040b0300d88140810144158061551015181847ea041d103c41840c1d500240c4075014003000015005012079044072225124284a501c410880c1d2000b4040c0b03600803801c0220020300f20072207983c00401503100d41d104104501d03109442e519003030100c4c0800d0180030707015403000600300b001c10080d02082001d68030403130002c90340f210030784086100d0307800c00e6030300c17046543c4000c0c0103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 250850674 1250 250849424 250849451
    0x103050c0f09040e0c0d030203120703060e0601211d1018141005010905010501020f070501080105060c032a0706030b030c060d0b0307061e030501050603040206090a0e0406 75
    0x4040e04111000c20640c14002003103030610140c421032608911032aa43c490784102e1200038409542e4020009210110001d51414060340740d074006540e01002044000002c0e40c0c543c0288181d5042c3e80c1000403019099680f50015900300e1062105e410070080e079040c0200820400340200c10081f05410168805502500e000701d2800201d544100f13400d6007440d9100d03401440c000720b900030721900025000554000c4183c100d0600001d402034035940790500002150034400c613001281228000c1e821180920466050181c5965050184c5070000754030300010086407134280083c1c0780e218401d000382c0b46441e003400d0001201c924446070403076000080b10318400220405119100003081079040a00205c0d100a00103500d80115204403481050081030040550384180d0004000c204082d0442e5860303902c0c1c02c401382c07850321000403100040e0042c81011030751501c0307400f6890403944013500860840d102c903800c10041d508007800c0240c10102c0d100c4002401181e400341c0300d00a5000300b6002504c0701317036a0313403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 250851924 1250 250850674 250850681
    0x3070c0b04140915010c0f0503070f0c050607051f060b0c0a0b06060f03070513080a03171501020a2d0804030203070e0105030319030e0d0305091507090303030e1203040803060103 78
    0xb5024030a103008010040d070b01d120101450f504200910b0a006506440c1c9020300c41c0358540e000142803448080703400c0d0100301d01c0311a003d50940c01612000707500c80e5500c2c1040514402d001c002081c54005503001101000c10b1100c021090034038940104515440d81040c03851030704a00412510b550107a00448203100c0c8c684201600113000b640d0f000d2034204c1d4055251051b1101070580d2041080001c1d25105510f191003c0c44080c00c141420f4a40d61000350400034510720005e00741203101103030000030a080c04590905880104810780280201d1441912070180500e81320801d04280d4882030b6005003610012500034414902c12005544c4881c29401407501d8540580c201030500315061005002c0d41d54000107898800c280180d403034038030601d00d890880c00f414448040d107c1c580b082e21036220025800d500600d01c5500c1c020210b8000740040da212014100b03068030240049400e4481c10b20110344240c0201c940c040c0444101c2da101100101d1404043d031040f101915203403004000c0c0452580e0501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 250853174 1250 250851924 250851959
    0x10050d03050d0c140304030c02010e0405041a0c0301050f0f0d1707110a18091403030c09011106010501050415050c030a110607031127030f0102130806010e0406020c03070c0b04 77
    0x904003564035100c0302401c4082c1701c050701c041c050003840c24403141168411503d40e90744c0000988140600d0905151200c1c049400c0384039540f940c0c5202000030200072440095134126007008001c04020301c03002040c03240d6000c1d050b8080742c00204003a90349000c100040f88925000c9444018103035108428140270b1242c240e84000248104490a0300300b2600c0302d50245501012071200b03000400350b42515082901c255281000c0545000100400a0b51a6501f002e8149802d00303803601c1041e0881113200a031a03075000d0040c1c5011900600080c8000c0489009980410386181043e910b0070144280141c40c54000d1412040050341c0d160b211002d1200510010350003d0503410288000c4100c0720260500d40032fa140744076025105004c801003144038a140ca030401050180603074030600301001c00340703020b5840810008440441114006000300c400181c8904032480c2c54122143c83d2155510300020b98046065210355110a101c00d401081c0c24215440041101c4064540d490b8074000640140e0500030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 250854424 1250 250853174 250853177
    0x1509030c0d08070201090605010e0106090806100620011803090b0c10020a0512010e010302040e0a0506133009060201090512030705040e01120b0a2310050d03050d0c 72
    0x18410011280d10000d404610282541003181440d50b5180d022030050090b990042d2880e030400d000001c02800c1c400c10309041e143d842d540c1c1c584035515100815035a00c005c1d00d00da085448452001c0156a210b1505000e0210b148480f882000c0c01c0a42c2003801c3d00c980b09881800380400c13542c90340426800401180c010700c6400a900d041907070254046485900c41780e080d800319500011041e1195109008607a2144400e85c841ba600d540c491941c0445070509010490050b032a020310b1005001001400845e01c9071300c14010709042d560b041f0441e501302200340302290062810b0010820201c0301664880030001c5080300c07100b100f070f11250700a01817000d943c070030710035645000340ea040400c10206100c0040c2e02c070720b1181523880d00c45281c00c403a184180c0c1e00101280700d1560004c2130200c050080440a540500d050400b65116007001c1ca007111212440b0340c2464510103c48604803520058035a032108003201d032120742603524804039402e010542c104800140c030004000c011440c50f4070030a00c1c0c100e0036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 250855674 1250 250854424 250854427
    0xd081207030911010e03011b110111030603030a260c1207090b090111030904060f0305010c03021201090b010e13090c0b03070f050331020108060409020f040b150705150903 75
    0x303a0700c41494080c035124081e41044011704030b170001c035242504550f000280001c110960003400c9140140828091902c0c0080d03942010014080e2915030341c04e0780c0c01000f004029514200380300c4400e8403410100301e090808002c8001410141c100400c0410340306013600d0003a0740d07982411a0360380c1c03244100149210305000752131600380a40c07003404040d21380464081c280002c003040300c3e201d08c03442c2d4001c07041065070107810710002181d0f24501d03c0d000807c6034403510082c01000810001641030340500c1001282c0760605600404ca45070464015050014060400ea01c0000091012030202000780c0700e09168075889075441d10401030342110940040c950210041d0035070410010040603a010400000d041240200c0816680b0422620705000c401044000e0b21441c5c0081d8004880391001010503408243e4000008983c1d08050013003000d2164001c2c01d543e900c13800780041100611540c107500d85c10011480318448030818003001040000e006000900d04596000014400c42030000c1032000306800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 250856924 1250 250855674 250855691
    0x140a03021b06070519021908060412180605030612030c0a03200f010c0809010911100c0212010608190803060d17031008061b090d0303020403020d08120703 68
    0xa001c2484003807141021031980d40c601c19840000c04900660780090058000c40b0603410f03140c4a601825883e03a0710940b11041c504100c0700c3c80b801140228801c01d01503400203000200007895400150699a003e410521541403001141d2038441149130081c40104200109000062030400301d40c11014181c103004518001d0b80406954540c1c41c0118014140a800380071015155030032203d80c0c0e04000040202c03600d0020441075107010308164040c00c0085107905000c43ea05c1c0070180111000c0c240c00907203076060300d88064148001c2c51405032240e0300300520811040d00503601c0084007040710320301e180041290b5051141040c10a070700801005a429140006640010100004d680d0301000407181094803c11a081c482030060240805540001d000410060029269103ca105503a103050445000b9581d42121032940700b04c051400216620504c0a400d0754a02207040707500641c8280b40140c241070b0740358042540c40c215030780c0c11103841c5800b10f0080104401c6242c0941c0c06541481c05003c20308 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 250858174 1250 250856924 250856927
    0x3020106050f360415050114010c20030304031b05190b07060b0d0b09060c13140a08010e0f0c0604050a0506180916120c0906110f0105040609140a03 65
    0x49194120903a03802c40c141ea8a0452000082c0f4980c075602440c038100d05840c05203001205000d07404001e890300e07850708001280c0b03170303122005620030650113845601d60070300b044d00e0740741101c0b02c0318a8020300d151000740e01d8545c68a05002a000840c400e00740800c954001d00c210005000309504118020030704062031807001a00b030780700881182d1820400d1680d0b4469401e1502c007a01c0034031149030304030403452401d8081050001030f00f44662904000d0f5425a00c550030760959510416600c0051844040c40c107004c021445600d032034480d1002483c100185555604113401c0da08180450001c0b500940601102000c0c2809160540801203450503c0c01c0d0030500080c91410060041d1405806e000c070704003010013100706007200907680c0203203108a94503014280c4000b080d2488002000508501c0c2a442000c3c064010b000c18490140c940a800c10f0a0850440398082c441c04420041d1085401d02031440c4028171075203020b00e01804011403018020700f003103034400303429025401d02c6500454048011a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 250859424 1250 250858174 250858189
    0x301050f0c1903140103202e2001021c020901120506131b09050114030f040206040b0304150b01020c090a1104080304090f0b010216050d0f05010c0c03020106050f 71
    0x141c0d94031002d41040e49421070100c0040c44120705911031111403500210520a004040c0491101d00d0042103804c1c0d19910144030f040401d544004040140702d210200142620101070101d02001c0e1520185024140d003100f000b148101c500d12074665400909090a00488401c8440729264000b0a40c0761444a800090035442a8a8080562540c036404642d003a07961000c4500b59115404c4144501c9855610702c500c01c920030031105010a03800a00042d195009045128810070f0f00782e401805c542d5009034130010b050000304200e074003607800c210114980d00c1d808003840c00b5600803800b6190f0128000e030040120303040d00f1020f5040d58010a10b100d01552035400060b4003000c05031011443c0d40f60b060510049000795044241c00f80404580401c048403a9231210072111000341e000d0020168110043e601e90f0040f0054000400104200f4806802c00c8074180309041d22900d400482140140c0b103081c2101c001118520000d15032110010070701d1f071709000302c8003e46011650084e00b00752410006138003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 250860674 1250 250859424 250859437
    0x30103060c050c0a1a0a0b011707030e120408060c04080d030b0310020a02030d0f0902030a0f150e01050f0f01060203160204061505030417041503020310051c020301050f0c 75
    0xc00e80754444090414814402c0d6458040141d04031440200c081c0342c4600c8141801c81480030741c1e002c000c0051040100713400b0760240c140040e100c0e00080c410052004003480401407100040c103072521600020a5020000200c4002964281a80b50760800c4041400c0074009056403145580038031007402035031004682181d5881032814002105410340000c20b0409149070000c400451001c180e041d401500800200b4010b1b01080c020001c142c400b42c0114200c070032842000e501584240030150004071000283c507401802001180c0c0ca41001e440d0000964040d5404c92505075142c009201022440c02e80c0c50b604015105600c048641c10100003e503240a04001c107214442021880301c25922990f01102c05007806221000414840050180444d0300030f490440b1501007225484a91aa240c005c0e102526041400d01e94140586c25048000c0e40000d4109000050040c8001506544a00200e1814075150794074580c030f00d8090040600319038004006004d058114000c200c2903012420840d1207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 250861924 1250 250860674 250860683
    0xb0105090415021b03040603090303050c0a0519170103060b03390f030304030602040e011203050306010305060f220c0c17310323060402060918012303070605030103 72
    0x8445101d504905505413820815505502001a0114001d0b0340743e0010031585000ea00c0500264407822003c182600c20710512000050091080e44042a411103910301d0f4081c861900e81c1d055181590440d5550000b0b030f00c21190342c1e40d1904009201c3c101801901c07004110244418201d1024418600b00c5010020128115104e03a13201c0d401190b5401d031220000b48400f5048076112902c81c80d246000f54024001c898030f4500d508000280c074401d0303000e1548078941c19074800741076494240c0194003402c0003906541e0702c0f0000c503d55104039202d040c0c0000b2122044042012949000c800c070b14216080340c00d4500802c2800703039803d40483c0301d201041c00011040c948003640c1e054002c46034906801010700130b800e0304602c01401c08000f802c85420074180e90003460511a034081382004581800200d000c001180d4002034006009803900030003801d0300c600d010300500001c0041840c034080414007600060108076a03000345402c00c4c1d200a0000c01d98810035401041058102500544a404140b01c000d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 250863174 1250 250861924 250861927
    0x60e1b0a021002031303020f03160809010c02060c070311010518060a0201110a090303090b031e04060e010f060f0b040315020702040b0a12020315190902030c1c0b010509041502 77
    0x1456039100b0424490480311011086407a4200403d00050f020345d101c07010b400500c28a031090b540315401200325a2941d80440c1d5080020405030348400c03040d003121900034103204c5040740c0c940141e25010002c00700c0241c0140945040c60a5280c03281c110340d510115607041081c00d002a00805161001d140141c050844070030b5241d1041d014202e0241101903001c401c7d241000c6100c4070321507002090101901d100b40c031404041c0d03480d000c42c10600d0100325000301c080000d800085070344500d50078034140c100b40915804110f450000d108a801d58400000b4045000d0360fa502c00c01c5141c030f150078183c000e441e044c1895803805207992a2000030020b4410100c50050b03000a0340e00c210b5880354000c0300030700805000020f002d66510100c00c10100260407d0b4028010b0b0304c2e005280001c2c0000c02846070448861904081455400c1c038002088102412038141c8100c5a0f82951680e41e03000c282d0220483c921003541110942c9401d03182450f041c1d0103180038030058000c0c40300113624409001d0f12003000c00c9006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 250864424 1250 250863174 250863187
    0xb01090501050708130b040e0105041406012f070e0109060501050703051602040f0902031c0206010b090103060b0c010618090804031416090e010e0a0b04020d15020f0a03060e1b 77
    0xc440902c541c921031703400083d0300540080c0384c01407800a002186c1c460700400350141e903240c0034041a5244a01103410103c085030014140e0760060300d90302d00355141c08580d402c46a46083c40860000e00b41e150784030071036006041c200a12015105210301400d8400001d2000500d400006499801554070003018803402281010007450010207542e02e59800800070b102c42003c11010600401244000740d02900455000388075041d58400c2c071640c181070b01d070b005041ca6880d03c00d01c580560040a00241055200c010000e039109184024011a400301e4000050f07440c600a804090203450000f140074460070668084080740300d41007950100c80d040414a02042c40b200820b505013002148145071032070007001c010480c4160799200d040c456031624000c12020004401c12036648007180d10082c025a00c2c0d00c00540181002196004003e106120101c1c1c5100d01c480010281c2c1c014000158080d034002c102500c078140e00d80075031002014102c06812240c02c2c80c004c080194881c0b05c6004d8404d58000541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 250865674 1250 250864424 250864433
    0xc030c0d170f0a0e0a0902070203060105060c10140708060d05030406080606040510030c081014060703050702030d0809100605090a0b120304030c03050706020f030a1b0b01031a0a0b010905010507 85
    0x100e8080c8501c010100e82e4030303001d034500548a0071301d82010f1802600d02400c08202c0344811310894800320f4005004118036864032003001083e0340702400c24616801340341c80041d0407112034020728001130502014445923190421006000900c02412984120900c0c10740350081400402101c05540451038080d078280e40360b5000c2500d83c41a40d2207a50450200903d0080c0b0540c107900807450000707140c0c1c8404154640c1105008552100c0c007414242940c5600c00244924100f00100300d464440d080c09402e141281d00045d00b069428100540410203400800040400500c001e4401500d0b4041c01c100032414800428039071748004002c2103000307644c0d1f0a4003042c2e0f600c12008000c0c90a96a049a50712900c0b4a888411468248000c950910508001140540c00441d01c00341e211305a10045092440c2c428044600c1e001829002541822822000020590300c0420702c0c003850280e40800c3e41500c1880c4426034015005100c3c520300d52426000d10610303030b449015003045880918107180c4460b143d040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 250866924 1250 250865674 250865677
    0xf0316062c030a030b0604050a05060d090b07120b0a030f0807060905030d0b040b060301050102060621060a0504140f060a0c1101020a0306290301230405180c030c0d17 73
    0x1c0228108450040094000000000030601d926a990302070041e002284203010045c0920300446621141c40d020902190426201034440c0b03d400c02d0340420462146c0e1551840301a003a03d030240040e01502110164075020301030300818a0080d6025400301d461038580c110a051000c50081ca5040000351160901250341c000b00d070480e4001e400d40750740b8100c901c2040d00401c0c0352401030780140e00346a55401140b400b84152070407154103801404245d40c500c81040040503040809002004c1d0342440c06a076030404000302481003c5151002561b41000d08050700d00c18580c5103240d000f5409400032241300d1402184035038008041000c003040f00300511034251030100c81c00c410306080b0343c80865200702165041c0c000c00102c400d00e500c0c00d0030442658000010040d030704a40901e80c07070f2003000100b0420f062601002c44140ea0362840403c4440640d0000c1c1c156802914a003111201c807800c070200c4400140329054488100b10024000c1c080c4110100f40000035041028008d00724020908100754000070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 250868174 1250 250866924 250866971
    0x614070b090c130b03160b030a0e07030f0309030312090c0e0901090b0f04020a081209010e0d06090b010905070c03080408030709030503030711060114030307021e13020c0f031606 78
    0xc1114000318980c5001400034140725001c18400c0c46036400d0710803408600381b10304003502e02500b0918511380d00c1402000241c074050603a101030b8452140000301060381100b90207801d034825a145000c0d18510f040040800c0d45c0d44a00017002441d01e05240300082a0313640402c1200c505044001590b52220122401080160406404101074800704400a9030490b0207030310030b034801ca070b00c3c01c88a0341361600295121015955030b04203031410400d000076980100c2801c2a03c0000624100326034031255500400e44180d010100d41d683c080300014000740304280900783d4450060720f044070110425850080c5629400391001e09041c8002021443c403c0c81a4a075802454211040720b50700c0c141036038028007114551003c0880c42c0036039400030468807a840342d05109803c000b00158101001e41d002c1212140720140242003272050303141024800d4a50075810900700708940c000680303406020f0300c50307410b0110310074100300a50000c00c18800c0000c1d1001444c1444d43e0041400100d804031461050206400007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 250869424 1250 250868174 250868179
    0x3090312020408030403060c050a08180307120c03110c010e040b120105041a0a0c0f030f0b030106060f030509070302181306052d060105040932010602070614070b090c 73
    0xb0b0081143d01e40000140122440703040c0401c244060040101c0d401d0280380f4441000400540100d0403100c0860b82c81001d03c04682c043d00c0c94117034559629811001c000e00e034600130a100483c03440c00d050b082042099800c4101024208820034075000800d80c0804640f001d220f01d07502d0f1048215a12010821805448c410000f00b01900307060030a8080401d0040110000c54030b103100086030043c041c001d034030328840e150312420303901c2c06150300513800381226000451b40c483c1e86860198980d0740c2400369000030103054a0b0002c1550084000a0a50b440207100d508158407620040006071561030800c00401c60782d440051454840748021900c030182070401500d102c0c100400e0000204106d0b00d1008004244d11700c42020b0341c51101c07483c0341c50808030f406501003002071004000029064010880d501c00441144140098201502034040c0384001c1548000c020200188404c5404000b08806030449081c0503e811841d0074000e0818820040000c5c0305a0003280414181d282c200154400e143c0300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 250870674 1250 250869424 250869427
    0x5010609020c0618010204060e0f01030902031e1e100c0221030f0a140408180a15140c070909022205040b0606070309051e030f0c0114190309031202 65
    0x140b11180d0369a102c1942d46204581c160740d00f01070744820510840e000c4908035180c02000d403801c14200b0208010811000341495103130080b00006943c140120340211542d2095800c0c000e400512040c505200c1c250303d5100c00d1140da1070b200d40b108000400c0640c00e0081400483c940482440880c184001c1655810440f0356001c0f25145d05d61020010390711030340907504071110741d40c0c4116100d01569040d20b98010707040303400004070340410f254400801f15100305503a40c48102e808840030606110041d4011417110a40c840040340244d031007074a10401d4207015420b241051802d00c42035803134224901c00c0e00074440d52680c04400315141c10364840700074007d150114501c4207041c41c0c038030043c00c011502203445170580000282d140c6040010f07501c040d80c1582d9030340c8206041c50288948102d1500414600348a181e50b00a0309075010002c2941c0404800d01070002d82c4450000506441c08510002030303549028000090206a082c0e40356201042600c0c010800841e24142510140050140b40344103d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 250871924 1250 250870674 250870687
    0x2010903110705150f0417010207110103020f070308090316080304050c010c03270f03062414040509120a0c1407031203022b0b03075405010503060a0507050a0c0501060902 75
    0x5040d802b50251602408202c0514003a1600440491103030f01101030181c0780511481d40406d11401d07016500152004c203c919021281c5107460740e40c17004c4242150410380000c104000c0001c1846002c940c51420b00b000107880d5110f5030003410781c0c0017510700540c4800f410414101848602110800107101070020041000d80301e0074024060260407034aa51540d240341c541d01318503084048402c040b10b29035102c0c02e5074040b00c4400c001c042d0502404d420303c40c0c0305181c5100c4942c0240401032910384804e80f40c01000f0343e01868515060880b400009425400c64903041002c110000c1742c2e9000b410281c600169282060348002e00e035114a0901d00101444290340f0505000060b0b00606096070300310115007140780d8a125030003c100104c040b903005000c92855004044403540700303142c00c94100504070300e29001c020301500460301050354942c1000740c65000410403418103004441d00503899210521a80c9082030000d40325114030b0310071a0400c5940c0c1078040c14454207500c400c0150100d240103569500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 250873174 1250 250871924 250871969
    0x603030315060807211a030d02070b0406050904020c0106060302130605030910091a04050d11011116050a0b0a0501060e010c050c010807020c0d0803090705010903050703030c1a0702010903110705150f04 88
    0x64501d03603000c1c01f038814500030006030350002a0020458003659441807900381402d0f02101e00f0340018290582081d000e00145203500d10030f01804002c0c201c07640d001625250b1411800f01c7c240207580c864004e001f01001445401c81d4086456100b0701100900070500420341d103000c4c10080c2c82c4288541c100d45850044c402000b4001c990b4106a03641d6640d15002c90021b6080f0508031a00710030f010b0742c040ea04112222703d040c0c2090300551228041d0f810b0390301c0010a52a20800414101c405001d510369410061081580101140d4000302081c6001c0e2004c4055030307070309603480701401e80003030505c0f6000780080e0342d02c2d20803c08103a00c15000b924189074040c5c20300e0048030607001038940514a000d0034202041c0f55100c1c0d16000101c1c1c0e00140106640d0f07280d91000d90b00e280f003090058a680c003145681410001c4582c1c41540581c030103500000d19108a4280103103c0001c2c50590140b40d000316800f08001e03035641380705182034000080a50b5468103241101c0250f8803943d4402910751561200803000790 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 250874424 1250 250873174 250873211
    0x30c09030f0c01080108070807030f0519151103010b12061c0c0302031507021f150824060607020105030c0d061d0f0705030115020c06030a060303031506080721 70
    0x340b0300781c1360080c1e9030341c171082059101e0015004002c016403010780c5c100040b5050101251410380580c003135404a070f03030050015545111035141602c81c000301e0b100d081c11210081c40f48074661110f00042a00b15410315115000e14413943c080c0c074820300c0841c00402c1e503650742c120b81d200c20248c0407400c0301070301e500702d10b80741c1e01c000043d2205901c030303000d900000c0c0c1201c0407042c1014403622551380a04500e001d48491030780d5240c0010500075006640341d007445000401008a040908401d41c01054040d002c8207080c19074803a14038000131489254801d02c50b42d038035210241d4040940c2420007035200d54030301442515500070f617840b1820f468200b0800141101d88400301001c0900d5049036001d441d42e0f901140004480c055a00b00d0005030108010400d110205c41071421184161050b80d94034200d080000d4641d030800e481c542e00d41035480c84100100358040c032516400d102d42d008101c2c240c614040300680b0f1003400500503410b1100d20b18010700c070304083d1005d1015010400d0010002c0200390750800380407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 250875674 1250 250874424 250874443
    0x10290301091406030703021807270305010506100e060f09330304111c150e010c02070503120901110f0604021c050703031404080303011217120408030c09030f 69
    0x5070b02c21100890010b00340481c1c0181a00c2c0c01504211805408182d145444903000300360f98104540418481354034000048800503044000801c0004182141001402c40d0000ba118034410a01100c40c2c00d9065048554490b04d982c0440b00341d602c40724251444112445602c100030b5000c55510204000d98541503200c03c60251599181005140b101c680301803144400d45028240440b9200d40341d1080c5080721591440d02e00d58817150700b1100c001e60b06d000c0e4100d81c0740c04000f046901c0d501c0403000101e00340b080b00808a00d91005101952426001c02d840d0003a0f0400842c2d82c007400500142141d002d909033b00303100d018040c02c5442042c014a0441c0d00d405040c0c4049101740c0c0000b0136506214031800d0b440300c0c250b8015010742001451550141d407041c2e00000b4a900d242e6041c000014482418030203980200b54002c010100c2504500c1c007075482c0d04a022100c141c0180c2800101c9900541d0141c00741d21550103000180e4a07200c0140c0b40784c840c02007807103169052061002d080071502d80441c02642 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 250876924 1250 250875674 250875701
    0xa0b120d2114010f06141201091a090403020a0303051f030b15030f0709050a0e0316050c0303040303020105040c062a1b090b0f030f0c04050a0b09011e06081029030109 73
    0x8072864400c6c0c568568424000c4c45035584403c000140702010855004030440000c2030302c460b88004a90700456409003007100d00b03401580042c603a08084c140c0500440d50700c020b054400c034800d13010442e64007549082070701010305680b400400050440962540900303105100038121603000e00407450140c3e50302103c1c025448454109404660048441c0c05510f4030711050b000503500b81840c100110071043c104000c1501c441c41503061003221524244010809180254004038003440c080c109000003003040c0c0c0c8a28100a1000b0007403981d07002018007c512001000e4151601500c07500b4810301d4202018a0307840641c01501c0006203855071a4403a400b0150160341c5910101e000d4003c154403070f2489840c91001c0d4111381802c0415103813540c0315a038007400c01540020010411804a08005003d80203190016615810040b015001c2900b0000a01c6c1e00d02d8180751918140b07a82d03c02d0450a4420b03007040d2546500003501c0154201200e15045149040c825240d41c0c1d5284010040e04200380c4440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 250878174 1250 250876924 250876937
    0x6030516141f0e0a030212010209030114060a1205070801020406030c030b030d140714010c020c2e0516061406010e0402090907050702180a0b120d2114010f06 69
    0x40c1c81e050008904803100c040021240c1c0000c1c0c0c0d030741e06484800ca480c01050703100490b13000101c01651010340e212442c00b0701c1000162181a488145421a2401c1c0404070514188900704030207035942d00c1206090302d05005103a08541000e2502d986000c141740c003c14640d5001040100322181d15a1000c403208205a80501509080d942819141d028195038000010000003145180380c81c0c680c014500c60303114810b10842403030f080b0030709800c43e00d060b00c0000050300100c1d06d207600740c0382802003040458003407039625001d150240444111416566014414070101140c1c5882c10241502101150340d00700300c041c001c0d11003454842030482c100f21425401300d44080f01da02c110b810188241c030b401c2d0344040c2003034020b0b85840e131080d5180d0300000740032a8450188580c181d00c2010a40803240142c03d900404140c055001302040040c0d02d2003503c4146991010302d0b0480c009510042240d007003071022540d848003d102c80d042001402c84200c0841528100000016240e5102c0d80d07200101c45d096030320032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 250879424 1250 250878174 250878209
    0x30a03050417120a0c0219060204060e0603150907030e1603020a080d020303060906120d020303060414040b041506171608010b060319060911090f01030507021b0406030516 75
    0x800e00ca00030302d01e40d51800002c010004d004642c03554040d000d9110580110741905003011170b04501c01d030380c03400111140c81e00850100101d6410440701003540c01e003150403508614080c0310044102e2038003892030f80304100000c04240894000e500984e00f1070415000e8480c1341030000181c0d078801c800b501c000c90048035492400280c090f0040303007c20a411042d4095855501c0d40e00c100a82c5e0745014010710740c00030a5041030811044104010f4402d0903964015585900d002001c000032108183c460b4441101c4e407004010004045410240d440b9034011a0407030040308044078100100085d40000f408030541100303540a50400241d1841078111081100d0320407520344500780c1c281c455400c003440d00700c9400e00110740808070b180300070301c07800c503c81c500020f100350386440f100e09403808544642c22084001406c41c9107403c0441c0041c940803404e00b02404282440031009560704105003800050759030f10b0707003080031a0340c55030018002150040300316407044828000c420540b00c014890900742400441c0035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 250880674 1250 250879424 250879463
    0x9020c0a02151312140321090102040e06040504061e021206040e0c060f0c031b100605010f0e030c10030e0d0807020c011101140114030106050d0809060c030408030a030504 75
    0x21200f0311441800b1800d0301c20301d80240350403000d41020045030082d01441908101110030005810941c002d8020f400c408604440d080d48204809018038466900400080c4259554000456000102510006a0740c3e68506051f401012611811400101640400255529035401800d510001c40c41e42c4641900c131b40c010001251250500804541c10031103003c201803404001138101520321110161610038945c203080d00303603030181192400007030f02c442044d0000740c000c00136858120708840341004024140030000c0c0010084813010000c1010030003050380161401d2000c0040e000000e032043d044188108806030203010b82e0752225040740f10f40b404c0c1074049882032204a0207488150041c181004005c4c0045446100320f10340f60740c40b592600b0b40c01901c141d0b8040902d00030110703140c5d21100070920204141c00d40301141e0000748500e034070090b060049284c8130b0850305000350440e1401e58030107007201c3e8542503004aa000039580e00010403040316058064100303605c65881040b02003040303910400d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 250881924 1250 250880674 250880677
    0x109030206220b0c0f0d0903170c03040b06040b01030b0a1401230708030a0e0f0a0c06030b1302090f030d0309021c0320120c03040f0e041a0604020409020c0a0215 71
    0xd000354600801180c16880d030302c4005c007803008090184030b140400183c40b44007642c0c0c1000040300098644040c1921b4100000130103a0002007080000345542496100c0c10810b10b009040144280c2e40e400440c8141c0c3c0c000e62083c00600800b0f442500d0040d610580c030f0018251100b2098007007000b042410121000750302544101d03802c045605401c0c8145500c6501e00341e040201410324007076440c92402300c072120070415002400d00c140014003c1414501e405000701036a42d00280501d82883c0340c03c1216a12600740c1000b0b0200180b00585410100c00001c11030086a00640c3e010b000d080001012aa03040d08a824003c5c000d41e0440251070b0f0307030000802900504c440c080e0000e0003e29001c950003a20f40c4004170459101401c0b02c18220368001120210746c401c00c000402640006401c02c203c1041c040960010072181c4000807451510b030321010713501c24001c900010400000c9001501c0b40c0c4d260390680d0301070201c440c1c0440d02c880c141c481c0781d692030302014826403043c0c03010024040502c12100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 250883174 1250 250881924 250881991
    0x92e020708030f0307031104030503091005030106020703032d0f0e0603040804030305031312050903250506070c15050406030b0d1112010612060c08090a0b0c090102030c0109030206 79
    0x740258a040565003620069400151015007015140d403140f45910302c14a000c0c00155018101440e51850b0304800c000080d14800c50354800d10001348010803145401041c039104581d00b6051190280481c08807080a0904001c441e15000034018682101c981d482118607980380d680e40c0307a4071f5403075100404100e400e010031603008029000801003400028401c20145800c084450340d82c0c1030034030aa503240b007445036105001030001400400d1400343d901e8100400400d01d00c0c4000740354100d800382040c1c420200002d0003110300504000034044200720030100c06400902078644e45504014482a008000d540a40b044400003820011184c1961a00e015201503d5a000e145201e548694105002d02e00c0b07181204251103544e220350005080d00028010002136204507000210000c2004018007441c50103020007019a00523024140024200080c2e19005101411000d0f1203980c2000101c2c03852040301200121542003034180410150001407060148810f60308e6038400010005440f040c00580c0f2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 250884424 1250 250883174 250883189
    0x6060a080604050c06160b0f07090e0103020303070807020a090509060109050a2c120d09060e0a0f0209060a030f030309150c0507060c03090b04050601090c03091115092e0207 76
    0x210300d144a1868440010700800c24006d0040402c900c29840d0074512500490349121040058000c200c840342e40506040041c3c015603078107a03103650654000c00c2e9240901000104002030000b0503000703540e02c0e000894010058808217000c0c40c0b411211342c0d80c4a04080c0b00d01511141000e0103d00703c54a6801180e0703080794031004a0404000700c03402030562450502450b0410301a10b9854036080580200505640b031100b000441c0c2941e191600c84101d450590141d041904020395410020b4100844008510b0b0120703402d9256480b503000140b5030b4140360344014200801d440c121820140c054108510320703806045034110303800360b2010402c10b50340c410034034100240040000703100040c05544200510741003490f001070756081550b100996a08107842c2500d142d4059801040310407907600442a4a204030305e002d00c1031100036502c1e048181f48600703003148541c0e2207500030300d0704140941c00c1c0c500c103d400404030b5420302e60000b4400c03a0320040445400e904c1c20040c001702400f90000401ca411544035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 250885674 1250 250884424 250884433
    0x7053006010e012705030f06060108070e0402090409050a0209060f0a06030f02090405042607020609130b100513080706081b0405030307030509040f061809080c01050906060a08060405 80
    0x9480044030048050020541806420940011802c003110180310040203810303d804d45207411320041501e00840b414440155601910402c04241d90120181e81c00c031082c3d041503807110101d1800200680298981140c003d03240c000004c05012001500c08603250007a640c0c13190075118041880300300b1403085140354000c45100c0e8208070300c0f4444c0d80300f00d141050301100141001c0700040020141c030b00903242034444203c442c20808554000c41d07030b0889106050801d40389803240320b44c0424858090031540900ca25602da210b1001c0403865001500390f4280181000e1220201d10000b406540162800200084d202400420140b000144020a94880b074444110a42d0350703490f401003011103640b4504c0c0500081c03000051540b82003016049440c42034441d1501c4449010510048500040002141ca800c0401c208007014590944140386040550080388407607103418140218400c2540c0c1508a61900080080e40070010410b14051078048a0041c0c1c00d80d51007001640d151029140038081d44c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 250886924 1250 250885674 250885681
    0x11040b06031f0302030105070e10050a0c020d0303200d0c020304080a0b0612030c010203070e0d0f020f190308030105030105060102030a08150a030203150a0e12161703070530 76
    0x240e04101a14140c00d4060100ba03151240d000c41e0a484065910f80c1c0400c03150001408645050803101903010558a8004d0402105102c01031640e4a9403202074043c20907803500034203140c07081e0400da20004111007a0360b030004501403030400c1a40480d0881d24240d03c2c00c06107200c1d440c400700849040300c0d0755200821400140d07840b020340c94100503084d942e1211080808040e0316009101404180c81b20100050302ca103091403010300f5014125041612070b1500c00c003071400003200e03401030500154054882c0040c06018001140000d082451440201d0022200000c100708014006505a0300168028012501c90724016a42c07401501d841c900440c5e401ea0005440c14945240340208140041c07212070400c1e52a0007103410300008410303280c4820400740030002040c045009614400103100004d0501586504080031640550405100d0900214032000203010341000e41c8595445600c005a60343d040c8404013602c0d69000c5004c8441072041d21050480034101581101100400c0c00441c01050740d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 250888174 1250 250886924 250886941
    0x605010c1a09010204080f06060f0409030c030f1b0c03060b03011527050f0f01060801081e01380108010302060403030f110d020f120408031e09060d050411040b0603 72
    0x4026440b10365082c00002908003042102000a8a016000e030205040030342c14481c48080315031145000e5400d140580340080d0307100890b600d0098040c0742031080c0d0b04000c0c600310707034083c6000d0b070025a03400c82d00064020b1005503005442141d2140c2e008120b80b41704d0600f418261000d000c2c1040b420034601c801040002042c803070b841070300d0380a41c0080b001aa0f0302c2d0034903c1103580559002c10040c00003c10450b0400360440042d01525003030610044641c542200b0564422911091400c1c100144645011003082500912007c2c41012202e4840c041d00300d103250071400302000300880c090a458040403965000f101c002d0b05070b0f50058034003450b01381940c82c1030f030350484841280c0741084407450f00350032201814088807203050401d0740030300b9030300040384000c03403800e041c0c401021420300b01000104480b11000080300c00300480113540240a450000424005009449080b41c2007840001c50058a486550045100300d1090400f64143d44219080c40100c4030340000c00713a01700504102045410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 250889424 1250 250888174 250888223
    0x5091204030311070902030a290303190201150902070c150903020103020304050c090a020415030506030706030905072c070c020307062007081011070f0206030a061d01090605010c 78
    0x3010f01d001140c01250361345071520120303441250380c41d04081c1d030f9034500010f6000205000c0c0140c000e54503400d0300e4400280000b5101d10600690141110740c1140d0015800c2c008e41020000d0b03820b0712001c5100d10341d1000848040e602034141200d800080c1d410200f41c00d8001c84003124240d42e10740d074840520b130940d4010344c0252b00c050010384851140107140101c80c0d980594451042c000c80324050f071503d107400741c00d01170281c21401c410241030500341004071546000600c802240c440c0d10f40800c3c00c0300a0700305142011865008040703481d400740041048807000d1041c200401d00c104071100255500d4000032161981d000f00300a42c1600441c0c800c00015201c2c030580c6510329544040707080c9088011301d034549001c0d442e13405640a40c0008502281a02c0640300383c440d0680650515458468240d4449614a103254802880f40340c010011807190703111035100b0f80142c00c9490b81805030104000300f203842d441092042c89002400c140002c03849520800c0b49213455984400c0101500201001c0d02503031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 250890674 1250 250889424 250889447
    0x80a020a050f1c0c0509010816050403050d03060f0f1211060f0703030902030c0603090a0f03020c0901170c03070b0414120d0c0b130804050f1201110409050912040303 73
    0x1007000074410b0345406441c10b0000c010082c507400b00e440552066152420a4500440402c0240242401007000a9800024050748885009c2180d11120f0701310805580e54003440c2c20140042c42054606001c0507055481081580c4d004074420b84810b03a41c080c0454034240502504411869240148001884c1c003140310030700c008020602d41c100351004008280d2900203020640c00240c4401c0c0030800d50030280540c9843d244161112461031501c2c10003150b8501200100405030340800d01da40302814401d10540302401401042c4420ba035075546038124440f0a07488555149015413819101107240c00940041100d0814000f2810945001c0098038000588490345070040440000b076040924140800100041c0d15161145001c9160400ca030150740010030042c2071458400011b0040b50205007611b0449904480c001c24000e40480461500c48164090b00781542c200407501018000d0000034105403603804a04101c2d6586003202a45c0e02d103003c2e4088a85540300704014070100703200d80344103c034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 250891924 1250 250890674 250890677
    0xc06060a05060d0506240417010903090e041a0f060405070f0e0f06090402030109140a0216110112050c1b0a0b04020114041701050105010e090610050903070b220e07080a020a 76
    0xc1e811148200410031b820844160300d00c0782c0003d003c1c404041c61011052024500d00001c104022040d0b40191041081d801846040700032000001d0410525035014400441d9034a01c920031424403194881c1c0c0128280c038030314841c2e030a110015100c00c0c0304007d40c01d8001c03200c0c1d840840d4589a0014000c16800f0030310341382d4001c40104600d5446440b280020b6000307180c06680091100c040b200c01444003000074102d0303e601da00400c00181500da40600040308281c011107803941d6203080400680b2281c4090003030b0280d0608060410900030142d602801c11000110100c41e81c40010242094a900e991400284403001c4800440c01551241000740c4001c0801c0342418642a103c904002c071030000d1540360b49480c1c2d100c00050001d960f0080030480861403c2e16816058180b6800003007100c034410004070100000070440f0101e0b80d80410400c002001c6000c01150366107061034084071b50b1410380210f208110000da90010b071040d0748854080c07042c2881c0d501c8507a80d44403c40c007200650b100d03100303540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 250893174 1250 250891924 250891939
    0x20f0403060905030a020111040312030525030516091a0c0307080403050a030210060e0f060102030d020a0302091905010219050703120f0210050c0405012001050c0c06060a05060d0506 80
    0xc0010036a20422140c580603e000f140c65103a516402801c1d54180d0403a04a001c80c244020000146e110421210240b41c0e03003008205980e030842d0200b00f83c416640f002240000c8018000c40e89501903100a00071410f200412404603600c8509450303000b00d91182084204070000804901c58000c00030b449190605170a50b403401d40300741c6401c00240c04c1030300300359066085144040d0401d50100200e14028403c0001440210314261b6042c0070326030000c184640740f40300c2d040000d085a100f07108581100d58041800c42d01c8203d020030040c000d40200341c106000b00f0120070f4044840d0520b595107401c80300b0590003806034505004000b4405444100100d446110369440440052141c0001b40d0418030340d41d507405000708076820000e207000560504000700724035060a00101c5081242182e0070342d6401c0c00c11401c011a440e0850443c61958080e4165079403030304051200c0311091500400901d4040f808580d5151904410004012030340d02c40e4580c4607200b0003501c201c24003e90800f50380110020220f4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 250894424 1250 250893174 250893179
    0x30a110f0a080d0806011806030b0d020a06180b0c070308180a03301b210807021c020a020103180507030302060702012a080c0408011b0801060203120604020f04 70
    0x60408041c80d081401d0340c0c1c001201100740b081d84a5402a800002440c240070720703840130f0940035040c4c191402040c00b0540ca8414001e900d03103400800d0b07008154058a810505a5141d0340105894580061141c1207031203403c00283e0307540c0301c006940300c91800d600a044458999600c1800a07485a410396500e22900030515080b543c0d201c00290040d4002c01501514aa0074985040d6038954065620541140001d510340b940e83d00984015028000b20140d0f5560760250511200688050b081d0141000c400e6051900c940d80c4000c9031400b610264084800d03204021040c000d02150b080389400051b408400c9040143d88607400c070740401c0b0812021b011503103416403141070404481342c02c150007580c441020310100039424030400702081c8002c10022a0040e600858402100300620103204111249001c10b8440d0703a010102c0b4024424071008105940250310f184004154200140011480403400018003c0c000b01c2102c1411132840c1d583c1e90035a03529030405c4001d40016a4800b031310102071201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 250895674 1250 250894424 250894429
    0xc070b0a0203090414090a061d030304211706040504030302071208040b090705090a0b0307171f020903030a0f110115030b0a09080a0804030201110f030a060503010209030a110f 77
    0x30444901a80d01650341c0720307400c506000c20b0b2800302c0c1c103000c10b1780d50090400c901e20f500802d00403005980903401003808081c0f00c0b80020403c1c0e204d8100410350100006100c20003805030790003d64901c948036840c22604840d0002e45520701100c1c07848126180b50b00008100c1d251541c000e40d40a03101c0c1c2401400c14141e034542c8009030465108002c0811010702c02d00081c084a04101544181140c3c02882e4032400d01010070a000c0d4090441303c82242c4480340c0c2100f0756818041540074109003420009001d00710001d440c0d44901175140c0c10505481880440840440c600071511100b401074025454204900d00c100e40160a803d10f020402800c04c0c140c0400000a0040071842c2c0ca14410340340285045040c2010041300291414106a00e02941c3d00c0010350342c04140c1d4544161420800075650741c90174160f024040088600e00104e000143d0a02440141c1000d5401045105d01c100409900c0c0d07002d050803841a100c0150349070780041c040c2400110f55981c41c1c1c103610b4010b005642101d90003000f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 250896924 1250 250895674 250895677
    0x90e030f0c03030708011a04060e060910050403031101060509130f0b090106170a020904032d03020a020c090f06060a09081204150906051206030a02150d1d03030c0c070b 74
    0x2007009064200000380301a10358040d0300103003d024194400240385410b190b00704804d01c07591159400740550200c00c48201d650b0202079601004002d410050810b01c001802040390380580011408150104e0035890030030030500c01d01c0207440001c3d040304900d49907112001d448483c3c80204503003050b00c02000c1c0c1c00040c0404280d5010f0010300700041202414601c0900e01078070141c0041300030350f000118090240e540c10503011b030015010b0500c5000340d0085008440003080c0703e0103104a00d00800500351844d6850f81c002c2c284285a603098441d201822001c00074801416920442039030751450100e680c500c2c0c408000e20340a40c85040c50440295210080c2c2d007449180380e9071190411000c6420001640382c040909018129881c010034441e0034400c020f0150300813052004680c2d843d800004540343c500f006801d0300e40350010415410710100c4808440740e503115003c0303040700a04280460042c0c60006002100d142d60b202c02450860781c81303a960200c5504821072145081c0b14509001642458820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 250898174 1250 250896924 250896937
    0xf050d031a0303070c090209030f0610090e16090f06050a1401020105010803030c030103030309030c08180a0f0b0f03070215040b1b070201020c040c2001020705010605030c0a090e030f 80
    0x2240400c8044104994001c0000400541e6010303800820004000a03105c8244c1c8043d2695500b005850308103c1001c81c1c03130a8070780103042c50320784561000d00460822051a0070200c07810304806000c13074240e07504503d03140c20b15a81d8420703003105c1800c0140444046c0d90401c1411710440f12000500b140d403200000e450708000d40c0f0072180c1002030941845956030a01680c0e01402034800110b00e58100180310310303598401440080c0425a42d100c0d102c04052160706a000e403d600020341c543c940f0100350920400f050070b0400188102440e440010b40c1000c12940708003200d070b0a680c49414601061201c80705640014230003021801003c02c41070706500003424084c02107005a0810000e4609010440340311344030650780303103d00300c000d105240060f0303070000d41d03030b003600b40305460200741c0509600b000d0300c2c0541c0544400c0684d8000c1d4100c4d841c2002c055010f072500398028002407094036551028545c1700c8086002031070304a00b00400030700910042e80c0100341c5d40d620100480e40307003030030304100c0695681181 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 250899280 1106 250898174 250898177
    0x6090e0109051c140c16060e0a12020402040305030a050c070914070f0215160210060e0c03070212030c0405190506190c0512030907120b130f050d 64
    0x401110704070b8811350707104d9511a1206021142c5a026020f1710300504103040300e0001d41c3c1c5118500c50350f18000c0c0035143d07014407800d0041c002915104441c0c180d030001e03002c100c004006481000105034902c5142d032441d803503030351501003281855481d0b4880c7c540325041c800100104450b9600440d085001c44c20140748044078000f05a08000d01e002c0006409100c079010040b0300c4440382000002d4415560a8900d0f1907421854001190054051400441005e0300040c600c60304180c02140c00280e14011118000800c401000344d03548221a6440d800d07001050400071800d0400041e1203104d8440041e00c101d80c1800c0215a00340a804403898a2600d40000c0d030300e500703014030303d02200b0b03540120550740c1d614400a1002983da00aa41003030b614420b00d038000409006030054103050b00d5104c0c4403248191154588003030080f200000c160307000500c50003c880082d204105d0b101801605 = true := by decide +kernel

theorem cover : BRFrame.Cov 250719424 250899280 := by
  have h0 := BRFrame.cov_init 250719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 250719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 250719424 ≤ n) (h2 : n < 250899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
