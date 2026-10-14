-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2514
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:56:09.570286+00:00
-- url     : https://prove2.me/submissions/6815667e-b7ef-4207-847f-c878f3738c85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 451978417 ≤ n < 452158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 451979667 1250 451978417 451978489
    0xf270106061205010803091f09150f031518270605070f080103170d02190206070207081c08060a030b0a050703050109021303060b0307030b183702 64
    0x102d454020040c0103d90b60b4540c0c4980342d00c0740d04204e941040c10a80018607003e840800010403c1c100d00c7d194088a5039200303404031a60411000c000018803041d1a003242aa05004000d44900c4003080c1c0d11801e490400405240c003181c8214842c11070f20b81c811140040c1a045182c0d849e0500820402060300c0c1e0307803504100400c012520b04000c80c03030403210130303190500c0754881c0b506880d03010042d00c0400c180846101c1d00754214145a00d0241c0e000c01010100400e11101280b00c0001500200301c41d040150019007003075481d40003000c2c0750388080c0140055103030081d542c880100060a002c40580c90380e1010500740852504040c0c4064001c0c0305104030094541d001c00d204007000d03541000966200c581c210300303911551800000080b01c8035024001b00307050780c0c030080b14680d004003281c11066490344c40080d00c140031a1024410644c0399010120110188075071718161b40660285400e020b58548a041055100d043c503035440e00310000710b8000c41d1210180000d14070402858401e540b0009620600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 451980917 1250 451979667 451979687
    0x10e0a0606030314030709061b1b08010f0903091a0903070e01050108070f082e0e0a0e07050a03290a020a0f030c12050603030714030309070e0f27010606 67
    0xa600055040c540907482e03080d42d014010a03643c5413000c13231802d001201c81c498488180381e02101e40b043d5100000f25180c1d9070380b05902c06000314840042c50490050b0855041c204c4000c0300d2800c05c00900d001a600105080640b04031484031440c00b450200ca0031940d00035550415014860707100c0101c0c81403141c2c00346c0e40c12158240d0300c8403803e6803680d1b0b00711500b4980d40d140e18007013803602c80807803030300307070100d110341140001e01d12800c00d000740391407440c040026465110100c080d004100b0b2208801c200e0003a04030750340d80d402c001c1c81307040d1403e408100d05100c0d030710001c0c02ca03410104054042240001c5074004c08200c1400c100c4881c205804010002d600991848020998010310640e0242c02405111082010343d1100c14058032140c51440141078001c0c049176160004108039000a0075044228042c1165900115200d00c1c00a241c0b601c1c0440a4100c420310b42c1300141001070520100c0507031580a410a00e07062002e01c28241004400b41d00301881c503005500340349001c00c031f00b540122550 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 451982167 1250 451980917 451980923
    0x3102100804050c06040b120603250614070c03030507050102120403200f0303012309043e0d02030f07030b190e07060c08130306050f060f0d0b0603010e0a060603 70
    0x181280300f644080180c54031440c441c0c448012030a02c2900c0c034480345420010385c042805404e44280b0050403201c84810941ea8040000b02010080240540b0350b10401c4c050600321134054807840c014061b2642e00c2e0b0008148402010803800042c0f034010031401f9010f582e112044440080c4c10f504041c90080d101d6042036030328a040090001c0000802c22001030008030201c80180590300d07607400d18445000e844e56081c07045028603240300c10124035441c3d001e24584124050b459420a1440070402c80190304051818001c041501852030b40010600704000a410f040c104c90001c400d103010b10103c1d003406002d100343d030703070ba401122070000510002c00300c0988900e404020b100000880044002c0444009084000b065401541d0900c175460045041c5c0b030440b4090309000742090a0504041c949000d10340040b9a00d9403602c090010980c0310040d05900400d003102c5e0b410300400c1c40e1011880c2d0030781c1102c0c06010844401d0106640e62020350000e40d200c0c00c0442920071808031814820041c0595100c12 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 451983417 1250 451982167 451982173
    0x315110d020c0c09060402030f010306050c0702030a061b0903030f050a030f0903080411181303140a05090102010f1b0c0c120302031308070315020d0f2d05310210080405 74
    0x41c140d01d0711f40300704c1c0d05c14081e12000709150f07401c544403400104801003215007c6001000f00c0d170f0250383c0030003800401600c5914003203070b0300c0d03498a8201c0c01207505422900c107000c680541400020b4100300c0c4140030504501c0c05688440300d182085001c1d2000d01c0e19000704515110814090640c4070445070722490199181c00891030000041c0444141c00341d0200504c1000000880c0d281d1100d000003124641c00b901d08888070000125402e0460f9110440002c0130540000d00d084003940c080c0100c0d81114101c0d2010070100100c1c0e01250400ca40c00c0540901b040b004104400801c080d00b5040700140074581031110340028a4035001c4d41e40c0e8400781318008040c0b108000080c040000007a13180c140c0c0e50026495603a51014103540c0c0c0650000d03010500c2e540d840303014200d0f1001662041900700e042c40b440100c0ba01108440100001d1780d4001c07c50611810582004540705002c14445032074160350000104005164a0001c1d016060301f0001f94000904c4548040c065444800e05020328011015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 451984667 1250 451983417 451983421
    0x315060e10030506030f010e071a040b0a05030a0e030f07060b031b0105030408041d0115020c0906011b082212030804020609120a2a0315110d020c0c09 66
    0x19503004119100d4558468003449100459070710941185810500180c00c5480300981c02050b035095840d0041e0140141d8409841001304000e1034030341c00d0344a41d42140070361506040c100c0701c01451013803001400c2848400004035510060545c000c40d04043c3c2c0d803003540e4859045c81c4010085d40d101c4001a0b0301d007400c28101044030300c3c010403440200002c040400c501c45007490015107580c0c100034001d81d010b03a0107000c0065090b803200c14412085d9000d03441a00e003581040207c02c04240741c4640c190840d4000c4a01d40701c1511010324032034100000b401d1142d07010b5040800c0d004640382003100107040b28000703d190600c9030181a02c8583c50a80720079592882d5441e5500f0308080302c0f9282003d00080c600d500454054200f02d401088030f080003a0281c00c0426901114514041c5007210450b580452843c41200040403c00481c500800c05081c0302d080600e0758403002a82d0901070f6031610000d41d0703846d03540030725502302080798080304140c5c4080d51140205059640c031fa450701c1d04e08501826600c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 451985917 1250 451984667 451984679
    0x501060b0912031207140c060c120a050906040201080c07060e030c01060b0c030a05090d0227010512060a050717010303020d090608040206070609050705061b07080c06070b10090c0315 80
    0x800c0ea041c84948010000c1ca41c0c0d83d0441c2100e08150940010f1080c4501f008070090b644c00a0004034171410201c00c1c0144d035400440b510142514000702000c400342e00e400c05120f848a1301048058111382c0901c1d02c1d4020b40c0f215a080102c6100d40c04009181c58a030900758040c04c4408001340051220301d40c000c00500b0b80d04d1112410603c80c2341074104180e00308024004119000304043d1074026009803448001d508180d0100703503040341607031482e2003494841c1d0540b0800b403c5414128094641036800902c605000c00743d00d81d82c1c1d24040c040c008995115800203a83c4d9100300350000f41ca46000807400c109580d01c1c02c0103900c4035003c0c581c003000101c00c4400842c00a000e0560341c0d02031075000d8501c0d8a0070280e40c0b100001088240c1c800c0710305015900c8001410750304c1c0d80c054098500115131548002040d100c0e072501d0304180e81d0040805400070a603140140d52031100313864000340c01240b8071300c4030b076112280707404142c00c180c1124010603d002d960140c41d41d1f0681c05070700540c02403100140aa92100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 451987167 1250 451985917 451985923
    0x15070c0f06020a15050a02130b1c020a1403090c0904121205160e0109080111130f050105090d030320030115090302280f03120807110d0f05070501060b0912 68
    0x83e003146020b9011000c0c204c01c0d0707400a64030260900f0010704000c0d0500d114003813001d05a012000d134240100b00036000101d0041405181070b4580011032800c00324590140152000040c403c03103951022000a014640c1401240da01000007055040c40d440c0c5483d000c0740001075482c00720001403a500c1d985404200910500380140c02c075104580d02104901030440f2030800c0f81c1e144a0410000440013340c080c02402000c140b45a0164039988644c40000038810006c1107034003411071090045070030409640c010007140c0309407005031144142c801450405901410501c1051100c0000800c8042c45022030303440a10b05035503144e12000c0e5524400b640c112042c010750b0201a5005118844211340c01007034018401001200d01500240d0075a5191a81544285944165111401305900d803e07440c0d80410030179403003601da007042c2c64140c0c0b156034030503518603545450303400744510344022004150041003038401c2a648100248070260b03c51000442907000405920f00a180080d0342245c07000e404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 451988417 1250 451987167 451987183
    0x9061205070e15120703060518160813171308011a040e100204030503210c0f070201050c0624121213030c08150601052715070c0f0602 59
    0x1641d910103849090420840d8840e03c82c8a03c1da200ca00821414510610700c84005104905580700003a01d1844c0109000030240600c0c840e81800624901708000250481560200c00c0b080e4a002103043da41d4114517040009040805842c1c0100207060386501c1e000e1600500004515000312800e035541c0d020387e40d0aa6400000020a4580c0d82d80162150300f0941d003d01101c2100c1c8044407044000503904200700d91098000390380540001030525842040b0001d041c3c136462803000c80d4419450010b208400500031144c648428800019031364040d1781c451015148507070102c1d0151405414210085000c0d02c0c1c0e60f01d207118070b100916604106c50b181c030705d00544031407034bc081c06441c004540c1920032070258480c05001c02103100000700030010400e180011806090380400070400030003031401e000500c00000b8006810004100322240c0c04400103803d462038001885074420701145044e001a45641c03000c2003c5580c8480480d10341d090011449084088410b4074001d01c42154407548101c0c0c550f644 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 451989667 1250 451988417 451988431
    0x40305090d0602040f0b0301031a0906010b0903010b0604170607021f090507080a0f0c080102090d0b19020c070e060609181803130501030507021f0902040906020a09061205 75
    0x30300001115040050740c02070041e11485006160948a00c008000409940c001215405d004030042c42000400480e41040f0740c100b010100c01c0380f41100d4003030750301c070014002d0020000003c1010911030302c1c2501712940b10310005050907159034480b0b100f00002c658a0800500510815000c18402400401c0c00541c0d800f041c1300e4042040445040b0710040c080880d01225a4483c4034000a00c5100501000e03410300c0c460b000c014600d80950408005030341c01d41d0040c44c4aa4030400240b02c0e0340d5602a070070003040c0d5020b5581030f4240d458480580c44410b402600140203800040c20100303040d40401d01d0b4050700c241c58040c001544448041c021b043c06207030490b98000b03c100c100400200c100079011036000580882d8800d0607550580c2d081d007103406c00c0110f50454110b05405100035038160150f40e9104005100900c50034895184039600d460030920030032070595440042209540f9a900124203032500726205542d643c10340e0b07000810045c1c0b28807030000001d40c949074240c00708900d8011030b030040758 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 451990917 1250 451989667 451989677
    0x1090f05042a02031201091503060c18080c18010b04091d010903020102040e1302030601150905060708070b070c080d0c120504030c02010e10081801180b01050a09050403 74
    0x10034a4184070042090850b249044500c00c04a8114803900b00c07096144842c03254040c580f00c10b1980c800b40108103068009440507410100f007a9070500c0c4205649040702e405c201e0101d28444101d10666903000300c04141e10601000000c0450110000074210155440648000709404003000c101442e4080c28050140c16110410003005040c800b50004550180030300300c0c0103e00e030740714007401b4215140f0ba041180980d4022800b00b08808940004075400014102c070700103080c0c441c3e0f000985910050040d0030800107601c00012907180b1403100310000d4440a00099074400103410b00350915001004110f8012a5a800040d00580301d0015842e200e0741c4a1180342c140101070f032188000e071008403107030001c2101c00c0d848505d4130300391070040a010300e00a481c0c0031040c00c102d00004003100081c0381c00601842044a502039080da0200480e94010844903c05410305030389240c0c503014201501c450360911144103503200a0040210045041f52021207605069541d1405aa001c0d181c0459000d0003240d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 451992167 1250 451990917 451990919
    0xc0a05060903011512060501050103050411040c03060f0806040b010b070f0f150204031a0c0f040306050606090a03120206070201060308071b080d0f02010e061612020409020a030b0f01090f 82
    0x4241440540101d000060001c03a2900b5511450702c1066496031140d01c02810715240641442001c0c4034003405400286002d20151516841d1036141001c078001031401507558003009075410340f113548000301911400080e8100107070754901107030b075800c420b59098660142c030310300005002c07001d50110f0380c0140c0c6c0141980c0c1c101d0ba4075100c0828400136940e0030f440c445104076082c0381c2180c031407008001841c85000da041072028420032a50070000000c1c829126800e040201c141a00300d1001524110384c0d02141c0421030340d55840104025006016545400c15044d2034080200402011403110f0b001c1c09500315580755443c1c4504074240c8850f44009008894100b00003c013140800e1020b031403203d8078500b402d840980c0e502e0074a10b03090301d5881030340008659201140d076113a828000c840403c01010300030403140c1051800505c520b41c03604818014412100d04603924240c0315011755008160444046498010b20300000c0d0281613818003140c400c800d01c08400b070066000c1c0a10006542c0088501070120f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 451993417 1250 451992167 451992169
    0x90606070302030c1608060603010b091303050c06090d0f0e01050703030c050910020133050906130c030c0912050d08070201140a0b12070b03190204150c12020c0a05 72
    0x40d6104400940450004000e00c80303114400308815428524254400c1008515100a040c20040b002e00080c1c0300303074100b49080f010f50ba5041c078955003000f043c10305210b4000f61440c0c1038800744200c0a440c1b14900a44003000410580880d0000c03010b40303161642d0f0113561031105c048601d0082c500718140481c0040c407002011900c030b0b9224015601107403c07c1482c1090b50350015108043d111140720060391141b420b072002c2140021007008070188000c0014070503a20b031046501a906600402d130141042400045480ea52081c0303074003146080f44000c10a03181c5010700280503103501503205001c00d00440d00001d1820b10b80e00302d03d81d80c0341c020001d002008001201158000300280140b000c56403105003422502c81c40742201d5008011600c0001030340302602042c403107000e15044852020303800094040000a0391202140d40c0300203000305120784c009000e0907200c028003d139040f01b1700009101401902c02600503001c5800f0320702620070303141d40300d008440899030341451a5400740c000b407030944100300c0e07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 451994667 1250 451993417 451993429
    0x6040602030a23120a0608010e03070b130f11010e0d030206060108250e041116032102041503050901051b0d0f020a02030307030c050f0301050d2301021c09020906 71
    0x80194502100c0f40030340701c0851100041e030003101c3d100c1d00c261211428002d440c8414032900c001881980000d0242c106403045d010380341e0082e02c00240c01070301a01c00107585010b40ea11042e4a196000298046a04560500c142d501a130382903180e010a000c500d0a52240c54802d10145036254154024116a80c4143c011104420082c0500381c000000300c0c05252100c1c2c107452005800c0e45c2540d510301c0d80030030f442c0400040e50780c4d0581c100304000d0200045a115408003000b0b294141c2c00d424080803100401c52050100084141488403151000c6000320b92030516290082c80e400890350140116107130004103e080310801c1d258210083c1705c1c0307170400e0b01c040c2c078110207800d100c41071000000d94055211015802d0b80d101865010060f000081000003540e014070a80030510841e20703040f03041240d42488042c20b48018011075119060902c2e40313408000c00e280c0740c3c050761180014019004142181080e020b034222030801e41c1d400d203910100c07c010140038801e044d1140c1d00101240c540f82c56030000c3c009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 451995917 1250 451994667 451994687
    0xc050a051f021c020c1804051e07031b090c0e0a060f020f33010608220c2c041505040f050a080d0f0537050f0109050606040602030a 58
    0x55020b8108859030860f4002c0005180c20302d1074004e081d140389a1810402520705221030001c14070171607014407001c20310001e00482c022020180c03100410102c1e100c09407415001d071b44003c010011040b00c9001d0b032480c4e600702c001104c030401c60500c000121100c00b034400d00d41c102e0341681c201d1b05500041001c1e40c0b1402500e0481601c40c0180c400051400c0c403058140700d444040b803048642201c1000280715021804444aa00d214510000359410048000d019a2000d0410381c810001d2071001c0c1180d401810551503c1a8842c141c4090580e4600e020b050388002280008440010004030a28078418548920321031030303204580310030902c1c000400200070720700a031040c3c800148103c40540040c6042000c9035116006518840d210000c0542c604140e0f0100e084400b1014206000e2000030742c0305242080c8500801151000006e002c64500034602e02c400c400100650308040500c03003654942908141a500c00e0f280901032580e6820506c480303842144508030059100704609442c4501c0f8001d660 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 451997167 1250 451995917 451995979
    0xf1c090302041d0c0607150911040e071403030403020d0204180f150c030207020904030c03030f0f0f152601060506120a0506040b030c061b0d0c0c050a05 67
    0x29220740125040f296020303440180003503521100d056480c001c10584181c1102114800e103800030541c2d56402051303548410102041d1111702550800900e0160b950300445c011304100007a85040090b16a01c5810348034030b40f00e00c180c020407009035007400f000311403d8070380141c01c0314031311225a42032100030401c80420200c8040b00c1541440003c0030702152041150040301c2d9070310b20b05c4144140070201c0d081604400d00f4148100492401a165410b042da0f0003178040c10a0080b12015041c01c1d0050400306121091240c60445185060411588058040c0d209081304000001800c550383c0702c0b5a14500515a40e1200350044d1445c80041c14000011601d41c94004140140d649011602c04d8210307004070305114401c0c03000c10140484501ca120341c404001c840601c1030719000408039807034100019209011b6840091481d84400003500440d40c0000347d00c003101d4a11761a9070000b1b0266411074000c544000d44044005080d182000c400c000b59000104200b0602220690722066800d01c1c2043c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 451998417 1250 451997167 451997177
    0x503030f04141f050d0b01180902090f061908090102120c0a17040b0f090606150a030b10020304150f082e171006080a02190e010b1b0f1c 60
    0xf610322200c0000184480072400e840720350f10781c0240180c000c25201138692190401900c40c418000610144050404844422900598600c041d00126000017501682c40f50485000120035031110f186810124030900075036100c00072a140c0c008000e084c0c7c81080c07015103800380b00501140c59031802c10000c008800c01810500c10503012030042221440040314140c81c0d408411082061034000c0c040c8850f80300d020301b0081c0125142190000c0c0c400c0d0020751000f640028007190400d4518000d5000150703100b0000c04c02c4203281e00d2004000e5403603119000300a00c40340c0070220149807600410b55002c407013406c0d440f819410350703859500c801c00b4a400080c517002c400d602040401c941d080c0312140e20140101010b145580c01803064100d06d0300da030340c50342c0d0719404c0e190201c10408c00001260411485604848172030301050108000c988040054011400b0660f9450001039802c0700e42c001014021546010758554500784422251600c81502e41e0148503000140400c41000c0450300015030042c20f4144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 451999667 1250 451998417 451998439
    0xc03060114130e180604030203040e0109021e031003050a0605010911070302150604020403060212040c06050f04090b0301021c020d14090d0f02100905010902031005072001060b19090503030f0414 85
    0x2440c80c00f1406c1d9001e6002da000041d080c4010206000c16034050220941c0a61501590030459807a181015614042241c80800441d0780c4005411042e40116007250445201e1901030400740f0080a0a101d000a1180703801c81003040710000406464032140c0680180401103007440356034224000007400640c0c010ba00300004030008007540b02501c1c03100001c00c103450b031030318051030201c6092000d50010420700a003400041b600744451303000c840130780380c0301580490108165004240a40580120202402950140800c00014650140410380500c003800d100903007204940846004058030254010382068040c075040e50701800c0c00070807582007441128803a8120403e0315084070100141110583d444602c41010343c902001903035000b81c00780380200a2030030b102e035000d00250301c0c1c400309104403090421040d50b054000e42c808c40c02005d8000c40309649105100c0701034408980d800e1410086440c061010480341070000944448411a0040764a081c0c00c01c030501e141601d10030f019036072041d20030300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 452000917 1250 451999667 451999711
    0x10b0409051f1109060906250309120c0512102d021222020607150e0703080a0c0c0305030c01060312030506010f030906140c03060114130e 61
    0x41400c814a00903005010102030001a904481c0540e20301d2802c03079400c0c41009200b2150000445551000072501140e0724034221003c18118001d03115000b1010b82c0d03010302e1a24410036182c030001054401d030380340380380b49032130704000c594503240c1440180048010f0b04052000d4140500500c3d640460030084802d00d801d0469018103943d407000054140000c0e500036018400c01103c001404400900000d43c10b01c5803426007640c00a00040100e44030360f10300f10750031020482074462030380c90503005400640d403409582814407180143c260410741952030000503049601010900e40e0541e0341c0444014580180c1041c1150000e0000d181a621070810b00c80c000002481003004080403070b9214001302c4e8171459414101c896419440c1036000345410300c3d04210103607920030b221154940c801d040008200c902814400001c06420551001106041c0240041906100041d52080c43d0076030703420240e00040e05e4640380a00880040c4010188050b0381404010003d0000c0760340001500e12624003800c03418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 452002167 1250 452000917 452000921
    0x1107260d171312030605040b03190f08040812030417030f010506090a0504060806090f0a03050403061e020c0a02030601090603020f090601020102091903020307050105040303050a030f020c010e010e01060f031e05010b04 95
    0x10f41403000301365620707801c1156007824010b112030000e00700c010702038185082159011b008480c2400814038000003402c00200189842514040c2c04004110f6524203903041c4511000c0d4426941682c03100c5404581004100740c0c28212441581c101684503013603482c280034000c007900100081036120201c0d241c045010344551081d60020310b03508008006505100704024140f080008a010382500030045460200e80c100d030448046030f600c4400010f000130658802d0200480d5920502c59540c0005035040c0c01c1070f0000b801d00822030003141607500d640d903070b40c0c0020708680e00f500c0001d400241842800b51103207000d1000a512201c18000540307086c211000140c0d0768915100d45850070307040b40c5424415070a0801070307600680001e0034064034107030454902070014081d600d60300c02003544038102c3d800c1c89802501903640015030b038030081c0000c080058455020f0240030424010382e600c1c042c1c001a507940211201c1089907008103200000b0040700000b0100e10b411040190f40d00e648902e19204241c4641c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 452003417 1250 452002167 452002193
    0x31813021812030304050a030f02030d090311160f0303140c030307091404020f030402270a0204080114100b07051203010f1d040507050409031107260d1713 68
    0x307145440d07080d01032504100404064034600c42140d4030900401001413000580c14100c503405082c40c5d10510110f540c00c918502c20b01d11888052410302400004151300501d00d05281c4c2004810364142555084c50789841d00454420000b10401c10881040801d0007108240c0c0c0002d110058141307000303045030701c80d450765000759190310000300c0aa03010400d8001c414a0701410660481d42986007103500c141c054198040544040d10451061119a82c808400681488414070000c3d090a042c5080ea082030001c5d04584a008050350801200340f403041c982c102002d2248000c0f85102d8010303800c000841c1041d41003c02c0880309445402c400308040c00c6118040d600900b51002da0314013aa08200400c0141d42040490400d070755000018000060804900e10701580d03410740c0c00080111403802d00f2100c0d60002c01d02022140102c0d1004a0f000c061205045400300c1c0c40300750b00c2405c10f104003d071942c4100781c04007500095060300561030409c10724910f841c1c0005c0c86458907900010141c4800060380e0034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 452004667 1250 452003417 452003437
    0xc020a0b04060f1101060f052704060506010306080123070512011203030f2a050d052e0e0f060609120a0b0a02040803070212120c010509160803181302 66
    0x35020b03050030050340c003400004400244c0300080c07001740d1801409400c01e1089001e00780c80b9a404a0321482c40010880e480950320041070080403403400d00e4200303075006090550310f441c00241004404204804140692170307103504280c040c0074007001c074a4045440040d0250010080101c204440048880e8030680c990203420902c52a8504030018a40902103e11050300a81c204e0f0901c940d044085a000e102c804280d482e125190229002094085580d0f108103005040514075080521001ca07410100c0c0b912079041d40582080f4000c84031001c40c800b040326110b41c0041d4a03910001a40c003099413211a5003218010781954105990400021240d5058044150f8540d01040014003804802140d494110050030740031454242410789080e200c0c49907101c080e0164809120921400c2c1c0200407d04c8820b40450340039440e054502c84a50203400b0a0710b128845200f540715049034039003042841070441e00e151008500d00055906846820f2401e0f140d419444403d00c2030701030b40d00c42d8500003803126001e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 452005917 1250 452004667 452004677
    0x2030a080a030f1406010e0406080109080408010e01021c02070c0f1503140702070302040b0a09110a0807020c0906121e010222030309030b100510030e0d030b0a060c020a0b0406 77
    0x381c034400007000c640148008460490030202c020b40c10034941c1c41c421343c010b0400e05c0c1c0001b6050070400070074050000c0340d011410640c60b10071400f060141020282c4240c0325510002c0c070030100329134001030a0740190700c4031000300e50024040e680080220303402421306074840c005a6460076601e61340e80400f4880d5520404078048007403010312602e5414032800c200301204012200b414107040d4002996440b480c00001d0259940344a218296070b241d9081100800c034044042c414400401200394240e00214191800708600c0008214400e0010440da010301d00d0140860010f035880c0001c2201008000c000b40700180500c0c4542c03021600301c6003a14010802d15400035035108906011040400c020211101302924901ea003480000d5201b00c01500322030704460f0341c40e210349a1a0760310030340d40480e603c0b141d444030300c01a158103156003542100307141d61000001d0f6501038846140590075202040c200f282c0c0156418014407000f40038443c8010002d0000c2d090355041e54440c001e000f00c40d40301d60001c0000c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 452007167 1250 452005917 452005927
    0x1505010905090c12190c17010b1207140f130c02010b011812170408030c0a1e0c0509150a0e1803190c080c030307030f0b0303070f0b1302030a08 63
    0x207208000d601c20b0780b04113595802d20f41401c0e80c24945c40342038040683c004000203a070200c042c0b24583c0d000390007505600c040e0340c00e07140c040540d240c0242448041c25000d800107806006c016040428144122401142c11000e810840c1d401c02494a0703031528101e500c090088002c4580c180c59201d89000f03101280c00000d401000480003400b440c51140c00c01100d0840c540040c0b01c0c54034001c0d0395507000c55001918401c102ea407200000260f01464016003654440420800a007950006000d0f201c02d02410b11300302034061001c140c80035210551405828486005401c20103410181142540000c41e240d40d441131742508000105040d0302a840740d071740300120a06100044000d024220b42d1412414011450121610505c0f00d03443d12040c03c541c28004c01070b03c10001d011102c0308682da548051015690b403407402060241c028a4801d90800c1400d01d090320210320350400004481d207464101e210000901010740e0b810000c0000280300954095070b034560b04006841c1004241c081c40d2259100751340314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 452008417 1250 452007167 452007181
    0x1080d0e0d1a0109050606071a070e090403120614030a02090403021204090f0506040504211806020303090f07081f020903030c030d0c030603410c0f030303040b131505010905 76
    0x140c0c8018141d030f44640000c0200d2000034030042d500320780c0f09c03841b143c03644919640c0c242c0075100004500c401a42120341403003007104151f0b002c6410708200c0000701d01040000d032926170080d00842d2030171041d60194060b4080401526060109540c410301c40e204170382101c10580410490f40c2c02c40d0f1300003400035860b241903000315551070064550104054600708050301c5c0c0381c2c03611210640324890340c82e84503d140a100710143c4c0708803007070400e6444111141d40840e5131958000d540390b00464212a032409000005284414085122001c076001c62000380050900700036442c1502e0b4514070701d1100c8541c02c0000034540e8a0502c090034661010b1409180c5400000001405482d480ba450302e003010f00c1c1c40d505000081c1070340140c00c0e1909003882c20300d004145006007015400404240d440100d145144840f6070365600165101e07080d0000c1d00d56920704080030003032550f40c0c00141c400502019031f98001401445c040000e590350507000e404903030840c0b011032400d541154000e80000740e4940c1c450003000741c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 452009667 1250 452008417 452008421
    0xb130606030e06040b01150509030102030c030702241b070f0f03021e06070e03030c010501030b06131b081b0310061103090d080310080f03091801080d0e0d1a0109 71
    0x81c0710302c150042d00d501e2915a490300100c6405000703c641401401d45050800c0b03218906651030210054000c42d5a42030078a6030400c95001210210014482c1c007455022102410380011510000845d050341e05407240041015641c12106441d080b00009100c400d011800c01d00f1100c0b070441c01201200d040840b0b90030000d050070b84450800341015489807124914810020740182e21500c50300d0005171080f459000a03003180700d00d020310030081d0b09040011091145482405004006c111100700f1040c24455651007070342e000100604185040800208c6401c0c058003066612089480c071084a801800f04038040079001a9500a250083c050050080c95048203000040140d02e400841c204202140000d0018a0143d00100212004404220725581d0b13105001e0140c40c440c1e003641c0424003042481940d03508100c039100e120303050203e0700d00c0b2024801c540c0f80d07050b03d030307000094920b2060155007610015400c181082d00035040c801d444002c1444a1041880d16900b4a8039901951420551f102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 452010917 1250 452009667 452009681
    0x30a0f06051c1e0b0901060f050f010806041503050303182e09060f060810050606090109060f0507081209120c10052d040c09060f0314010b13060603 65
    0xc0221260802c82038041c08101d10600301591041224000750340b102080f6414044001c1d0080c20500200d0070312a5020040d000002601c203c0b482d02058256500100100400b02812140c01300e10b9607404038115051075003100d001b0442c0c540940c2c40c102c3d0f4070ba82c1c0502d9984100c4d2036400d03000b8a030b0290405079900340041c03407007114141700390505a40040100384071a0b051180180c0e17400d0340c4598100c108541c64003c5001e400b800c84017004220342e2143c02c2038030b07009012924a05d491038000082e9040c904141503403c0004103945442e0070301d08000081c0c41c0951000b0180d01800b2080c8039040c0054050002031070000108046e0b22a1403c150110500d0030340541030000c030716403040c882003010040c0041c0c0e82c00d8071581034002240030740b0780943c8100000c005d113039014980228145d19110850803040e919000c0c43c070610019078a1990f80131141304482c1140034154062206a8040000c02c0d1491002c030b5083e890300c80006030a24030b1030300103440c1901d0b158104d81500c0d100d0404000258040c81042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 452012167 1250 452010917 452010919
    0x9030c050a0b0a0315051e240f0d02070204150e130b0619080d030915050105010c080a1107060806031204081c090b070c090c020a030f1b0206030a0f0605 67
    0x922000e0414210440034043e00902c1410503550354401007042032900074a80c000d100103010318002c0c0b0008100a1840c5582216032400340a8610300c4004401c4024201c0661031003280e061801e00540c0c806805040d0f020440c1c04507a10b4003840141c025940703078422401902c2c20b0403601d043e0a4034206030be0094500c018998000f0340320310101080407d403503100c3d042c0d11400c00c0300c0118481c0d1500c850b11071292166001400c0c0f52052250301088950103511000c442d034050343c00ca0208080710115001900c009001d0140059002c070384240c0013a5001000c1d01c5106000c0c2440c3c41c210b0745031081d440c0741100e07a034032141c0010218020f0103100d042c14009240701d881d04208880c0707468200400325545150f503112401d80c0405d0380f000b01801a01c200c80500152180380300003070352844c440c1080d6480300413a014004040d454090314031030742070000900500090389600c40c040c200001c1d050030380341001c60121801d050300188845030010b0f55a000150310906d088d80740020f4160700114000b00700c0d442c2c2c5d0401c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 452013417 1250 452012167 452012179
    0x81c0b040c0c020d06051810050601030b030319050a0e090a0b0415030c0e070320090f04020301030b1f15020a060b0a030812090c0d05010209010e0f060405042a09030c05 74
    0x302c00507844003280720b40310030b41058000c18141c5a40003841c00403c10310090003e60f00603941c00504d0040706403c06802080300766801e01118a0b40c4040688a00c101e1b03062125078000030558140f000e01801c080d210403881c604120b00124032403c040341c00710104450141016581b1102c1180078070702403146d04411030f14420000c6c0c1060039070395501c0004001e801601002d082003400103894510075008003038070580300e100300150b01c0e4040071446a01d40100c1401841048050392426241c2032034401d0340e040301d42045116580d030722032031005c1d1010b44000b2a400a401d103941000f00c0ca000c8440841030503452540e00815005800b401c1c48800c490300120744500c500c4121034100b020484020a03540f9180c0043c1d00c807040e5444809481e0b1500c010400059001205400100c007403000c10760180030150030070781b00e0749084409030040040c801c890305603d55205a06020500c06410b09510050744034020069400e02c1c03054031007500b01d10f214540c403102d000880000040c001c0020744140c030b400400c030991790 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 452014667 1250 452013417 452013437
    0x100914040b0a0b060702120111120f0702030a0504050d031e090e060901030f14030c060f0a050a0e032a030d20030606070609050c1f0306060c080d0207081c0b040c 71
    0x21354500c14040040d12032942c3c1c0b500b030801028294000300301000d0f0f005100d5640c03403121000e08403402049035115130400242002a030180e0000c000c4031b4110669584943c505030501080041c0341e000c0000c26070030409501241d46c00f05031101c0d04141043c070b0545500c01d519148c55080c24030604010543c9005407000d40040001603420294080343c242d0200c00e8103000114070854070310b98025190349a48a116040a00c80070f080018070441c0507881401c2d05008983c2e9424901c41a076480c8900c01c601a031003000501c2094800d41011000c8009254040304244640312000345140c10920b080d8056607a240d07105400c800c1070981c60342c1201921641c0e5030a5249c040002002750003044005064941c03280c0a900400c0000d0042104445008129004000344000d441300d01404803001c2c1c0c00828980000414000d00401a603441c299000e41c000d03150030466000d0318041d400a103403c40760b0071014022032000c03803000341c10111801d01450000501803080b000b0001a0307410029540305218807464 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 452015917 1250 452014667 452014669
    0x100908010f180201210203010312081812030603010608030f0c010b0a03120e06090619081308031f050a06030c020d0906051e1b06160e0105030f100914040b0a0b 70
    0x3411002c640908000d803d5404280c2d04800b0b441c0c00c40d020000440c030000002c020880800600c0066414a41d14100e80b640c520202010707400c040d4852071120743c4019940d58401d907108000b03582c0301c1800b400228885a59000c5035240d5048041c400020420204528055207024420660954401c550303442c1c96a28546a0b0080042031000c80d804000c448000001143c42d01022038030b4400015200030390321003406118120342084840d0200004050002041d81174400ba81d4034101e29800ca581c9514503240c10100004a2502c91a00320103008040d00020b855601d21a10308014091038402040000f4040c40007400c04460074940400d01400410901407a6800f100340d4001503900f0706400c0841c04903a1002046003d0901107021800444404803141c04000c41e6441c0030b514030380c6000002402004050302c408015680712800144240700142e042e91500d02d2070754000100450940e002d9031114100c01c1950940e20a81100c07803001c4060004210040c82ca55a210f910281e0400a10800c44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 452017167 1250 452015917 452015951
    0x1602010207170702011704030309020108061f08180a03181d0606160b070c020a0b07110d110d0b040b0714043005060105031504020901051e100908010f 66
    0x40d9076201030110f6200b0442e4095540489405420501410140f4040c54003e01a00c20500c0403800666014049260303402d08015461200d2034a150115600c03412040803101d10b00000c11013101880448010482d0500c20720000c44502c2c00b0f642e13000310104901c9003203402e9485940c800000001509505996002c2c0e007040e858000c00200d030f882c1d035034608141d03004c00f00c0a08200040c000b940103a060000d22034010044041061003502c074404e15640d51925500b107400341e150003a2100b010142c180030075203881d98280030030b548115039154102c514140400c42380407034080100c40c2e41c0c00b41e1040c041402007444d4a168081883d1801c5610001441d00d084c40038002c0e8400d415101100300d2125070b80b105170f440c1c000b06046c2c00d0035407114284054103040703a41d0301c3c080c42124024042c41d880e942208140d41441da215075009004a2902e03480c15040c0b040d404880d1001e644248082c41c110701c031b140d81d602541c1c91120002d54440d4155810a04070b07500b11591400f082003160718081219140748a81 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 452018417 1250 452017167 452017193
    0x3040203070b07141614010512070806120a060902040f0b0a03170408010f061d010605041401140d05060906010203280507050f03041508010513052d1602010207 70
    0x40b8855465043d2881d000c1107034801c01c00209068000d0b00190380d0362807080c0c80640e0848840b250100200800030300103444600c80e408001070b074408410005205507000e4080c1ca9004100a0120ba880d048039030f054030b0802051050071208152a000720205515060280c6560031407240303410040c140d00e220004a07407450070320006010014506814001c84030a2044d82e0080c03650b40002c0c41720680358078800c00241003600504108145440c011268800803004e424143e50740c64035041d1605041c00c807285c20030b207a9030202604010243e02d451191a144402400354174003c05800308650401504009030408000c00b032a045501c00e1005c0000b5901d03503110070501e150300c60040305101086540890b038a02c60110060024440d6208031900d0100000091040b0b401c0d0b1341140c5e01e0b800d45690111007240c1c3c20721071954000280481060061400c1c1c0c40907030007070781405003201e8200c8107031010401c0b1041844a1800e0344950810011401408021030a503512548000c503d004d03401d80d1510b41100340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 452019667 1250 452018417 452018429
    0x6060c02120309041d0d02070609091113060305040b090d120203040507120b0a1b090e10091d01061d0720060a0c02300a050d02030f1602030304020307 66
    0x321490718042000107008403611682c0c050403e10100401c415250820030741400c1d0040f581c0f10320a00c2407141440810000240d8400c2d50311030f05024503102400c07000d003c1100b61081c5411007044210b40110340c111581c0c004007250740340452541b41504124030001c1005000f550a42c01c04540c24001c13580c014046268282c0c1d003c00161a034403903040c030520b00400c1340c001000d0025802d00038130502c070340040d2552180030040410304c050488250000741351800300d094000443c0326a40c041c00b13218544c1c0c0800d94452141c004810340195142100015141c0c00800141040d03030f43c100d1070781480e90a00035500900400f241c0c64040e0384420f082079000c428001e20210401212020b03240c5a2220061060450030030007080b25082e0800b4020000140801c00d09000944561451901c41d910400340800101ca48000c95140c4605c0401c0303508240e50054044404100d400c00c60783c11940e091303201542c010600c00e42c03405060310b00a24200c01c00c1030f0308010042554820300400006075070000b14101070701d013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 452020917 1250 452019667 452019679
    0x1802131b0c11120610090b060706020c010b03010f0e070902090a030209060112050a0b01080906060a17010213121b0b030604090609050d0e0102060610171e01032406060c02 75
    0x82c1410007042200004007540000308a49101000100194071401040000005404070395542070180881d80c80d13049480e0003a50500c00030f00407450583c0503003680358452002003410320395a0001303030845000714480c015442d80c3d4a9020b021034010055040a006480c00031442d181400d0005450240c0b2440001d114030005800039001d80d200302d40f500301e0030118040038000b60034008440c9011305805505a80010610340c000391b002e000c00903905004080250011401c80e08042110b2402000034005c025159000c01819010000440d0b850b0014a0301051100f504411840c3c1081070701c075004451152030510f007006101000e0b64004981d04820100c500060541e26031504034040c211006019001e4040c12030380d251660703048102d030034541409a0035200b01d9500c0d202002414a00e600c1c260b800140c04480102c04030035184075007034022002003081c00305814521500c00d07011500740c00440d0900c00c14400c0321003030b0407200b821484500b103503031080c041d95045c40b01c024400c219a03100644904 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 452022167 1250 452020917 452020937
    0x20d05160b0408061504091a191e05090c06070503042105031b070b040b120601080919020612092a0d0f140615132c101802131b 56
    0x3949a80c4045050341d80f200c8d103035080c0d5640120769101c1d0b0004480808044107862008241d428a07403007848140d08000300058000100400032400401000301081c01a1182d260900aa075660101620529200b0710003075564600b029026102440c5590350030680d600240035036000200c000c0144e890041d0b9107400342814802a120f02464061254407002c0c90100004020030200e103420003c0c40b41046492002c001620340302c00449214600700d815404030b4002c103140c541030f50441c0340c4040031070303000a004604010229881030318500060f80d0099541c1d11049a00302d10046481195145200c481c51051080144101045c2442c0500e0303c0103011340e0000c450201008a1f11000b444103003900703001c842062030302c0d0505940b5007400e040d42c00c4c481d2003030100014200034117010725209449400030141c03840e1015544004d003040300d95401a9140962000e103c00a0040c0c03040f040c004580c441d80e040d0180752401030000e5181c4102c00002c0302c909200c110488603407034644403d02ca54007450320320030310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 452023417 1250 452022167 452022169
    0xc04060503280606030b0904020109090f090b180f1f05130c03060501060905150f0915130f0b1201060f020709090c1a0c12090d020d05160b04080615 65
    0x152101003030410b910056100241440450b50b0002080e1070582c1c0302040440d007000c08101c0000c00c1100c000b0f0000348030820a003c00c00c00d98020000d00d03820b48502140400300c0c0e50300c5003182c40342141d005a44030300c2c0c9441510a02c00c00c000f190f005540c15005010620a24a0035a0a0245480c2202c190907220780c081400048805504038000d604510342820030780e103a140c108080e0000303100b028000340c103982d0701041e145400030045404030741640c02245801040741548801c0d030400740c070180e801301d401c8000740026440e580041c882d40c1800314002c0701490801c000104117400e2908414181c800c24480701120300c1e000d550581c1510502e04020843c1450400f0807490324440340c200300b500f18180300383d14040140102c07284080ea441d100020318424060358403d4200c1c00b4010b802c202301c5e80800301c41078120440200800380d03001c02400303250b00c00005802050755040600b8044443d43d00c883d03034007880a01c06000410290414581070b40c07410340380002030f0f59104c102500c60041c41000041c0c807a02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 452024667 1250 452023417 452023441
    0x71803021003140a1104090e0a080c060a050703020a050d050405030c070e100b160b040c0510051b06012318010e07170c0f070204060b0d090c08060c04060503 69
    0x86600800c101241c40049600502070243c010000c10307464078040200741c3c4403455000350b41c210180390b08000e0034a450094604007800c11009082000c0c05020b81e40000700d440c0c80c1c014010340008800425080c00c2c01c95a403001c41e02c005110b1000c052041c082c0d0310700c65600c0002c84401e00880c81c070110341a03c03641840360441c13041466031400c52050240c0050b02d2200a05024442e00050001c402b5155484241a00521543c2c00c09402d014081c01031100140c09001550b401ca4000d08140c0503803501c44010403c1010350484980203c4c10203d03000180c030b501c40c41d00c8104c1e1200305000c0c0405500d800c541c084404e450785000c500d51030b10f841c02184503807200581c04141188a42c0103000950f9240b50210ba000382c280d85810000d400c50700144200720b812403042d0300a500664156140c541001055030702030300260302c1203901917102c010000e1a1880c0030301401c4c10000e07002e00058640c16501d407100017040f8a910482c4281c1100c0c04001040c035172103041c3c40807038515003400e581e603540d2158a000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 452025917 1250 452024667 452024669
    0xa0206040329130308090d1e030e010f09051e1c031103011203090b0403030816050721120905190503190c030306080313050103110409050406150b03010803030718 71
    0x40100c00c0801000364070070f030741286400d8042c000c0d2580c4945448544d120f0b9110008011a000841d07200401034022068580501c0d0007807140d454006003101c0700009507030940706442111400e07140c80300181010711209000110110900d81c8180c1c0070204083c59080d00c440142c00d0325000044000780c40340c5441c2c080c3d00007000440b241c140072583d0350717115a440c426859000c039045e4001032018001066900c2c1a5048805503609a00c1d03268145ea00c40000351454a00f11a0500400000380001000107030b20003199042c0c00f902014204961840d840d00420609480300d400d40007504040c00b00021440100e80d501138000710f0050380401c06641d09200c1d20b988911651782c01241c10392401c0b05001e550040c0d143c2d009510a59042c08403990318081c550f540d000e0301100b0301c100d2446040810030380d8081d070b103c1d0840c00841c11407039007401e0340c40c0030602c100c41d011101070310242e494107446213805c0403c00d07602c0040c2c00405c00903030640d41003075802d07580c078000208060203100340091789005540000312500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 452027167 1250 452025917 452025983
    0x3020a02010b061201030c06050703081302060c060403080a150e060405100b0d050a0f02041410021e06060f090403080f06040605040e0309030d0816030915020f0a110a02060403 77
    0x140e501d103039440c010585104c0922056403141041c00b00070511900c640d044950a6825568082507a122511180b19543c85940c0480c0d10200411003036003c0394013400313030610035030098a448250f8582290041d043c1c6013a511001c8000030540e80c140006200c1d11460b50b00700200340c1b0000f4150740c440c180c0e404803940907000032401c01c6000c03a041e0151800b5400c01c9200b04041c3c1004c1c030103c0eaa9a10704016030203903014401007516100c0000a0034200386000e040700d8411881120712514258100c082802400d030045107050f00164100700560800d00f505180d07544054501103181d15042c0c0300100302ca83c016040c82c044485880101d09a42c1e5190003400c060900180100200c801652541d90b981e032101038072500070700805d43c0311031105002e44585c0d4451081084035020594180400302c1c000c0020000c2103496030b100d0f124401040c4814400b40c03851550101c21b86544513241d080203041e0161088003189a640400f400c0c3e401616540e082c2d80031650710550303030000010501d41c0b5103682e075105040e007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 452028417 1250 452027167 452027179
    0x302151c0f020c1c0f11010917041d13030c03020a080313170f030f0403050f0d0519110a0e061e041d152205041b050906030a1412040602070311030307020109050103020a02010b 77
    0xd110718007270a0041c030031a610f05800d241003e03000200900060000c03645a10080e4000301c40001083c054007110102c3c600c02c0c810743e80d40000300d42d940f0900b5002990441005044c06042104014049004c5a2800c8180050f1801c03c0f62a00500069110042441501c0720104003c1800c060050094845009074800031544903100420807a00501048403141e10b450400c0d071601c0940d030036501c1071500441720341e840c00e498140c100320241c40e4070903400b81142c1c022500300031600300708510345180c0e503205070104c0c007003503480e4036240015240100090840655400040c2840b0b01024100400450340300150350b442c0124003400383d170581d181c113103123600060a41081c080008001500d20141206c00400f400721400988070014860800c100f119070315050383c07040344c40c0804282d204c080c5550030441c4104950b681c4600002d020241d070031684c4007001580c041a0305100308078070965540d26224081d0019410001c50b500001c001c654503218440c1415800650400c0c0c07207100390800f0b2081540500740c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 452029667 1250 452028417 452028443
    0x70b0403030e0a06110c091512030304030809160323010509010615020106050a1806050a2c0c070312020f0c0319090302151c0f020c1c0f110109 63
    0xb4140c1c0a1554459205620582011806602806031603500801104c005c050b580c40300010300c008840e01424103030400044084000c1e89603240300403980029600300c0510b032a07013000d280103040b07154040c0c03034170061741c20100b80041c1152090f2042c40403a07400c01700c00c9911000000e51102d0300308006c05010529402c0c0030030401c5d00c201c1504000102d1300002c10000480000401c100d003202d0f250b0013100d511420380e807810090785107010300d07119180004a60001e60542d4074000031381000310311f0380449100580b018180a10308031081502090109000e82142113103055445100700d48100301c030040501c080004e00c08034102d00f0303a0646050740c6080300050303981d1a0301c018207030703407608101e030484079107802a4160750356144207801c114100c030350240c035215000c01c0b041402c010303a400401c0301c4045c07844004d40c400b0a144080c05403560401a001c80141c2d00c03480013884606004001d041a144907048400e0703124038540c00401420101486e20340b03030601d103d584c11500d0141c0441c000240c1950b024000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 452030917 1250 452029667 452029673
    0x1209082802061602030709021e1c1e05100e04021009030c0b09041b0818030f0406050c0c04060825030507060305090d08010b04060e010203090405040b010504060e060a030204090302070b0403 83
    0x40703e9405000b141181c02c080c0e07641c1ba00400b42d104054007104000780001031110107001d0708016003101081c950200e96060b503540e030050200c90800c2c4e10316200d880b10b9038901c0c084000e217204850b0030126001102e1450383c105014409851005030000b030080a001500d6800c540c85003a68502441c0c3c0110140c8180e40c1e12502031640f6044040312a12031490b211a88100c0c40281d982c00340c139034000da02c400074503646104010480b100c1300c20446040d408104940055102d1110081001c0d102544a10b0f49071440b101e0f80c03510b0035000001641c00f80c0e1030f040d0184104000000e404640140303041c07040b903a0b000c20041420010380c003584010564070810001140194068002c01c0c450b4132550b0880d100009000021203c3c84002e214031180c0d594100002c1c89000d1040c1c650448180e410700480e441d010704200480e0445004440a403420005807005025501d0107001d800700500c484140c051003401c1c040d0001d08808054400244290f0b40c030076a07001014000d1018800030031803001207a0300c80e5940c1c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 452032167 1250 452030917 452030947
    0x5120106080a0c1704020d15050901020d0e0a022b020406090e060601090f150504050607032a02011707110a060b0301140405030d110903010c020a120908280206 70
    0x3540c100c0003181480c4031031680c20300c9484107203003003690441c64180c55120f50b0244045107142c01f10558840c0c00d035504900b43d0860901400d40034086250006907142c01046515040b520780c2c041803d66a0080e06808000d84d40710b143c8885002c4110606d040000318100c4510090009408000c2d045414407000055004c2d0941c404800914850191120355a4a1004580d5241540100807005940d83c4080c0413035866007010700c0911409080451800f902c81380000d10582001e0011400595118010106130110b440c8003407122081e20b5452114104e00c1c0d00107446242000568154a0601400504107910601501ca04028400309a642484880c205080a000c0900c1c185000390708008a5151280004101d140300d190841c003c2e5050041600c51030003c1c00300c0c0007203034095510900026920707507420301c58800d02d9078054008299000d40d629141c052003a41000000500140f15810850040f020070b422241c1404118054807081c041001200d0a00e00c89a001c0e404c94800702342003102d90950 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 452033417 1250 452032167 452032171
    0xa080a0b040209010e0c030c0306010302070b0906091225060b0a0e0405010b0306070512060103062607050f03250b160201021903050a031d0a0b010e090a0b070c030512010608 76
    0x2035031807100b240c5e201d860092028078180c0d4031801655007000002c82d00c4640c4405140c0000e014517000d481d040c0f460301c4469041e03a054401240a4001c2c0c42841a0f507041041007102c45002c54207030702e00b0300c20481c80090f52f03415a1640340d51588494032242e020814140e0004810140c000d000007655030301e030164903845810484044445600e0010f07410707200c0c83c000035614490f51340e0740c0d42c96203007000d1032031100d0380300c00082d095505040d100c081c0820a050480800328402d103407001424030109542061514107410b1394001d901490840510700c0c9547c41c00300380104821902d415a03220341c0d40022014041c0c5034182e2220b03400301d2011132000d201c0741c3c040d40d4040d01075000740d007104c40c02c806481c0c00002d41c0803456000ac02003041040b4540c1031030b010342c00050700000800207100c040034202600314208024002c0844018880c040180700c00d07440000c08540110030000240072102441d40c0e915407040300a0041014851850a03440406105908961104021240020480d60b6400d8098005481 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 452034667 1250 452033417 452033419
    0x1128210201060609120f020d02040f0507080915011a0703090f08030406030b040507090e07050409050a0c1701120305032e03063902030c0703140d1409040b0a080a0b0402 74
    0x1030a80001404032580c85443c17a081c1e0807540140891409508200001c0c0307030b07000c0490300540c070780c00308149040441c81414481c0c00c407a15240010b14001c2480e608200c02444040016544000140303d110700006400307401d14074010919a40b0661400c045c0c441e40599400141c010b120314402094002001c006002200c2c0070792030038000c0c140041d041205403002140c075100040d070f203503808000b2180d00c83c2040750050042e007811803810b9202c24048060710f40031a040421036440f00000c268003644030007800d10307001556008511950404800c03d605200b03042002d000c1240100109003d0044107503100030858444d842100d90001c41c244041042e452807006a81c050325000e110388010b8104010003080080d01d03002d801d424072103a88a100d10f400f903420003800b10312040c05080051101085290007650180040c420fa4980c05406030303240c0380c865400081000800c04150300e80034000c0040c0c1d03914200c1180e021801d0211075011820400c40c5a001003e03911901601c401030185034240c442c01a40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 452035917 1250 452034667 452034677
    0xf0b100e1612060503060402041121010305120c03071407050603040308041104020c10020d02121003060c030b01171302030313090b030f0d080a0908180111282102010606 74
    0x103010b030b261034211581d0b44100c81d007603000003001a00620741070340703c601c2e0700b04d1100e070036030038160140c4581058407080007074488030b1041b68006105018040218402400d5003a40d01441c000900e0340a50320380c050100010322441203c0080140445c0a02000015180240441da03c82c6403900300100501c0080c0d8003034803651510b240303581d540d0515008881107040e45a0041c000300701480c90510007035024040c0010841d0742403040c80c030052500c0a005020f04280410404002e081d030421104945220080e60281843c1c061400131507600305c26520040b18503115032403990342d6211000c0d02d025070409030003541404000703461258424215284015103d11300001c00c05c0d00502c20926071790314003200c102800c59000b1701c86524058402c0c1c3e03526511644900b070208103040b041d0b484540c1504030b02d4901c036510303001203015030311541d01422140005101d80014808600500030718820a1050340c00000c1e042301d088805014040c144403910b2a1010300e0554150380090f000c0001c0c001c1c116400340e40c0c0012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 452037167 1250 452035917 452035937
    0x31c0207052b02010b0603070c03050409050703090c060903030804080901020118050313060203040537080a1727010c021225030302060c450303070f0b100e16 69
    0x903c14400d004403e000608204e1541e210380d44180c03203280301203100f202000780802010490340d01500980c2e004800380d40700820038903c5e038a488203000513280c00503010880034610400c0804d0380b051180350404d400400c4196684602c500407409044511403540d1000d50082c0308108000c0e0006c0105590340d003d5540700d40c1c0301e440b44400ca031680301c0d81c4203055006091096940510b80c00d0720f001c0a20113142d0460700d58a8400c0c40c00e012100e1410761095041d074124880c0e107014081454007100380c41860701c140e10702e01440000760b50416550306035441d0b0023085500411103d41d020341031080c1d08036001010001178140c00000199520388030f20034202018030002c912000c045805078a00309990b4190042c102990f2001381c5003815400c5400307400c209103a49402042104074818001541240c9010211044414580103010241000014a0095200b0003622002c01d0046c80032603001135010001a810740c0714801280c0030040c603034011201a000410511182d04c025141400328115540c0700c0d14001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 452038417 1250 452037167 452037253
    0x10c081b01050a0c142a01020307090b0322021c06060f051804030806030a120809070f15050924070605060d020a0b0d0f05010801020a03110c031c020705 67
    0x40d54240d41c1d5240880d500d011428281c6003030002800c101c60a000d048008050b80e491b0000a40c07000c4505108140d40c001706022071240c1c001e8440d07014023403850300185903081c0751030050140d00b031050500c40045a00b05401c011503990388400b800d5481e40f181c00f1a110f002509000d00241018803804804904c0300000055a0420105d090341003698222040f02603580ca44044c0d03900a802407100b23500d4040c481d040d80000d80440703803002d0f082ca1940c0e228400751070300c00c0e051850b00c05190000d0b107480d04800010460080c1200192002e10024505291541c40c008080350070340290107402c5100c8000100400d50071504039000d02411406542c0a00c899203405003401100f0700c64940103504240f0210040c0f1200640d5001006100c0e42c003c4006042c0c5410704550f4125442a00801031907500007c0c4124110750600032811440f1804000d1403412410200c07807566445400255400e502c05081c8185036550b040d410b039416079411100303071020038030100c0000c0c890240d80c40552050701040c50301400c034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 452039667 1250 452038417 452038421
    0x1050105090705090909010b060d02071a1006030f090501141e090c010804140a050f0d02060f0a0c050f0703050d140603060a02030a0b120604050d0f021209010c081b01050a 75
    0x3980b07503620340c2d41c60a550f020612a050000901181180d92100d4440f141034440c0f0000b06040b06520600603100c00e0303d03180441d0400f9042d00d24402040a580500c007845413081c03600400c0321a141000903a000909403014003504131f16001a1070f41d403a00c21403003103150700c41c00740381c4c41141c3c0c220610441c0240d10100410504055440043d07660204602007800d501842015401501600080d0b01d03480e04203010515060f01c040c0d0440700c0d5040070b44940c5c1a0310080250448000260010b07142501c0c00081640c00c102004009030345440d00c0310410b100060240c81201c040690490340b060355022103040150156000c001841140f52500e00d03451f0480310000f1000d070245800801810071619152004e5009e07420192600040315a9125860019520303c40c155a010000001400d544d1815080c0181040c0c401d2085405014a0590220182d6404580d00d4500d0715400c2134262500346180048403d81c1c0082c8004001000000d00c04031081d04c408500c8000c9000c0c00002d100075901e4006141c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 452040917 1250 452039667 452039671
    0x3020d1d030c0d021605010305060a0306021621121505030a030203040510050403030c0b070315030308061509150a0314130c090218150d05010e04030e030601030209060105071b0f080105010509 84
    0x80140100d6028006c40d846a085550868070040414845503125100e44003203900172640e10700b022281c1c0d2072200c2085060120740203008884121180c000d840031001509181000000e150815902c0955041010f00900c02c0780242c1000381c00c40782040301d689006540ea40c01405400d01c1081000500c4032450310032700448d0300b034907415503654002500554620b5842c4074050034500c1815102c040803001c2d42c9003441c2d2013005601079036a100040c140001440780703203000400c85040d01502001528100c0d00c1d501c3c2a01a03a81d10501c01545d503000780b0b041107004000100408000803040010b200740741c0b49240c410b085540c0984540d1901c10303607694116049101d1044905100c94408a1001080c90702100d80c4206416118540d890441e4038010001103440907000404031190308401d02040c0b6a004e20380390280700007a402011707a9410b640004070702c0c86005100604200000075810104042c0d481d5828640d68a100003201c419221900100910350354010350003d9072074030000240a19203261902c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 452042167 1250 452040917 452040943
    0x1f02070e010b03100e060f03030d1505040908042607091a120615130905030301031509150c110a03050d0e061b0c031e07021e030d03020d1d030c0d02 65
    0x46481803038049484c05c00e040c000c282580c090000c4100040b9502c0600c01030403d0480c180000481544007500d07800400c80315000140500d151000d0a800513100c042100c0a0f1203041d0000900b5420042c0000601c030080703801040240070f5260006a4411541c118841180c4007103201d91952081c0424400c81c0d415144000e15143d20440109860742d0741030211a03007a400c0075141c82000d280d80f41c011001d80c0d4800804884503400000100140200a1a15050705603115401e02c6204000e40700c01000d80740403040c2020301c590b500801c400389409004603150007411041a103046070400c0c02c1c094115040000310003005410140794001d0004040b807240c0c40b5a2003088004115540c00c2804280c40d0000040b20781c651104004c410b400703050400c3c0d043c07030306046456003940d940428418070040e142d01d0307414001003009452a20b141560003040100f07504145240050b20348406e4031038040503200c0740301078100500c603202c02c0d00700300c200100041020001e05003c8811010310b4040490f41da10814181c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 452043417 1250 452042167 452042191
    0x111308010c02100e070306090b0601020c03030c0d0503060609040f140907060c1218080102030a060e0c091201110706021201060813030305070215010b07050f01060b0f091f02070e010b03 81
    0x40203660003113a111001462664046450301d0780c0701d50702d910844414030702c142c5400310968100820366a0420109040d0201500a50f0404100205003603036072021760b000d88148000440000c174507488203415035400c500000d01c144840c0c0450715498000300302003a4520924100500021414079000500c0e000306c50003a035400f00740c4c41042d10340740284001050100308100e0321509055014801e68146009000c2c040d00050f943e081c1b00c49101c08272a00ea600010750740c0804020071054605880940e030a41405880c156010f042ca02c44450040180d26054440140d0114802082c0002070b40502150600d4071a201516600c408041e5000d0740c0403104440d14810324881740d00000d1094020300d0700041240120b03240044108074119400c1c0d000d03001010a00f401149550600c01c0c100302000a209144008002d92424005003080c50b1140055010510400140c41c4102d03807030b14506038441c3e00e146651603490b02407283d4000e40b12041e42c82644140210580017095003000c0504aa00550300740b140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 452044667 1250 452043417 452043433
    0xb06010e0a06140f071b0f0f0513090605010f0f050a0b091002011404030e03100b09060d14060705030105030d0806030a03080718470913111308010c02 66
    0x1c80d14100203c100000f80c180c240040050f00c0c803102c2c050b03e9200e104019002104908607605401440d00c1d500400f03036126100800c1100d0954840000240d507010303106c1c00843d640d1480030202810b400d40008094074581400012403121109100d81500c402c02c40c880d040594500c100988103074a8003640000a80411074000c05280c14200030102001600003c2582103070500c03001206d440844040d008515443c4684800b441c082c82400300c1030b510a40f08004000200380416010b000c014003031801030584100d410288040754401c0c0a0300d100800803200246000080101039800a1103080e000e88500e1a244080f03601500c0d44901c1080050024025409030b910202d545802c00f9204005010940302001c041d406518000c0740a4840c680012100e07002c001c4c1d415568840c8600581c441d4a8400c070040071689414003000c080c0f12075103040313a8403141c4c9000010082243c1c508510b10141c07a040c00307503481c1d8010402901380c0749200c00714000d03025900e10b4034500760740d58403d0500040c2c00000d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 452045917 1250 452044667 452044679
    0x51207030203040309120c05090610081b2208070b0a0c060209060f03090604050d0908060109020c0313120506060618040c0207150e09070f090603020a120f02070b06010e0a 75
    0x805540d1107070082c60075885403560f8240d031111b461142c2c20140c072401400e501c14040c1e42480104140c00c0142502c1d1040010305101e40100b0b4000003a001180e090b440c2100703035101ca0303083c4003034032030b0b44d504204403600340c000d840c214440041c960b104c0c3c00258001c4920029200d4843c800b91805041981c664416211640e80c403038000303603c40ca81450b805a4103020310040104458040d6208030302d107000501c560700313145c10002e1402d230070700c0c1c4640200700c8004014801e203400482c20a04581440d08050385680c1a9401a8218010549141c82005105c0710020302000c06d4030004119030300440a45805442c0d00341400038601c2031410200e91899403983c0c800c0c1c10b04241c1d1022101c90110300c1628005070b00c9480c81001c06c48807000d02c000084410782c07040e15034074001c1801500305000f42040220102c00081c083d00162041c03103a00207240d80810798003000c901a41c0d0127980d0385480d84081060311113507441795009401409041d90100810000101d42c0e5014120355851200300400140786145006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 452047167 1250 452045917 452045921
    0xe2d090c030112020628031415010309051e030d0c1b08090d0b0a14010f0e06120708070b04060e0a05030709090201020109023312270a080405030d05120703 68
    0x41c83c200d0b08004100b00310308840c54080c074010792003001700700c04031158010142c4c000e0583d041e100c0c005540d540d140003072144002d4030b0101c0c2c240c00c01081c280820544081d0820a0070080c2d040c800ca214030504a400c1075402c0d602000602c0704445400d001c2005048a510032100050162500901c80c07280c8000c4a012a58500140200010080c400322042d06036a65400c02c01c4410b583c004600b603110181c6141014907181c44601401c13000100c03a02046c500301e10503001002c00b03081c090280682c038548451150701404108080c00b40c070002c69141c01c0d81e40c24404a00c1d809803281c0c01c0050b08003140c0300c2032484d0904041040b03c030020001c0041d2410801000c0092542640032415590784004031030050300c8860809190300b0010069010310f0104401c880160002e6138408070800004020041c01d144000071140e820603209080c0303007d03080041c42d04805030321026206944504c80c540e49501042035090062040c0c401c2034080e6100980340a00a445c580541074100000403d00303c00100000d1181d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 452048417 1250 452047167 452047199
    0x10c02030a1a070f030203040804031b0b030408030403030507171f170c030c10080a02030a09060509061f0b070809011e020102090a2102010f0e2d090c0301 68
    0x30103680c0c41414540d01d5409100101c040200c0030354040040151040d000312800b481203e45003800d5156180c03d0f524034100e4422400300a06001522020380b410b803111481190290030000f4143e641c07420035041007025904110b070200d0022b410040040e605510401544810485a24407108a5155211001c036155100c0c4c4c1c855034400c29000300092a408124045100306800308041d089210000c0c3c1418200b1540301e80b0a80a81d01003080e00100750f61004000340d201c003500c0c00058032501c6142030007014101d038410103400c00d4181024000114000302e01e03a4060700c000d041c0d048000300210b0b042d000c4414584526840440184020310109a00100404000ba070514000002d94059070358140b1035070200103804010303036001c1901103150501ca207003c0e001d010a001e40e00700c440307103444400341071110082000b41085400341030030f40729500078440ca0841003401081c80101d50f030b1055040c1d03070340d40c12900c500b00f20b005003182e0b200d05420021403450040901c221568590783c24618207045407081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 452049667 1250 452048417 452048419
    0x3060f090510330e07020d0228020907030f062c04020409020d1a0a0902060414130e0f070b16121715030c0a0e01120804080304090b0910080a02010c02 66
    0xd00c418003848611048108000501403d40340c002c0641441510f65507110010641e00655000c2c548000a085d00050000b44800f464840c0342c0180d2032290f2040c180721082c0c9002904030511400b4000c0303135a0181c0007501d102c0000c2c50b0401c021a90792035000d17810010410070700c0c240c142900c080915556165881c81c0e01600280010842c5007841c0e000c00c91708800b410090345d11040d0210140d075600c6c1d4074100240c00c01d00e80882407001542540000e00e040c45540300d030b4400c44000502d80c0b6026214007950500803090828100298891054041d4891360503030110410b40c00380c4500802c80f5010341c4203485640c040703800b41600055041e0385502100c40b490b100c0d0010311410310000710200441040c103d100301c4000d0b00c90b4100031407490515142c0148444c4162285603003030003c0c00000100380c0103a04640c1c0281da14a6103000c01c0c2020a000d00c00c0760420b18180c0000100880d000110790098203110384150f8404406a03a2101004210106402080c42642040131984055842030301c0e11601a40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 452050917 1250 452049667 452049701
    0x1090c0221130f121a150d1103010c030f0b060f091908010c0e04050903030402150a0e0d0501061a03011a0714010f0e0616080a1104051003020403060f090510 69
    0x1c0c803010140e451146961008410040d20fa41013000c01024203140d007882c508060060314a4100b44512076220001a40c01030300814491000000703001c203117003213036201c900040c000b0030140711884002000780002030b42d4003840604182c950441c2d400e08100325000e003100743e6a0b19050860010420140340204400385021a0480c140400c02c02403e2082c90802e030300c1038880c4070080c0f6201d018441034a030b001f040704402d50400d00070000907032141490881b000095040203a0f46441102d401d03505c14000c0208541c206c0070003c903c0080101c1540300d5415940d007a0301d4140040040c0d0310008840c482400341c191100c001555011440e10b602c0003410000d0b10654102c0e6541c3d166040c0142100c0d421107042c2d03809a21418500c800d80014800c030b540140100308012000340080d900604020310140c503012166580d4404903049070801d00655020741402404a0404545000001d020350002d0005464180c42c103250101c80048a11a1a0820f035200d0058500c102c8160460f000501da05001d24007104 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 452052167 1250 452050917 452050919
    0xb03040204020d0b1305060913050307030309140d05030a0b0901080a030e0a1703072d02010809071a120901060317030601092111090105091305070f06030501090c022113 74
    0x140e90b05082117040c1c1c40100c0001941c1c502107040248549020340b90607030b840070b8183e4281c081000032040f1480a80c160802003940340b0036280a100c0c2c0e046040200c01da07030042860210f641c81d4440003c600403a10070701c003400103030600b00070800f41c04002c2c4035107800c0d03502c1640d0400c0040d000316100b15118600910b01145103a5a00c00844142592086881c0c55040003d0305810070075000505104800d13445040f12020885000d43c0701000c20160001c2d05100d100d00008550714401c02883c0040c042e40690000c0b0700385074441e036141030f80141001da10400c0f011000030b0310f0a80c0501c501000c40e40c100d1006010300802004038215a400034181c14108241404c1c046102418558200500407a482d0482c00212860030002901651a10402c0c42110fa100042251355618a81a5044400d04083d4000b1328010300c6c00c07030f1038002c940c2e000111003402d1140005003940c06a026504850112900340080c002c1070030100d89501c2d0101c064082d0000c10307120b420120300280d01030000d80c1c031011862007400f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 452053417 1250 452052167 452052169
    0xe0723030307060b04240b0c010e010e031201080f10050901021b0d0e01030203101401020a0b010620010e071703040932010320040902181f0b03040204020d0b 69
    0x554030150b03040d6062501c944090905040a2003003110020810080c1031108412006500c20f0110f584a6803052640c0070541e044400000c0d40304403000d5500748000c10400c1c0c003168501d626908000c1003089114086000000c034224040f80380591400d01401500900d02d00c00101001000090b201b050746641c2800580e825642100006c9001559a801484850101003009020760500c5003035904041c01031007806070020007484002c0640340d003896492044103070400100d10f0503684180c003400106500000282d181d402c0180d920300186403440703071100102580c44090a0390b0380c0ca00000e04503409140e003000746505042008a61482c2402540d04c1c00780da0700305140c141c0c0c941141410200c0502c0e5885000300700140c8404054254001c19030140e50314540b038401d11807030b01040d0000b2091801c1c0e6540708645c1c0b40d60050201c268001d103145060030051121040c0803400b29500e040c955100b800041400c2d0b004440b500455141c9542c0c14919503c0e5401d1001039046440801d01c1c072a200c02c940801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 452054667 1250 452053417 452053423
    0xc06060308071520161a01030f03030b04020a0c02040504021306030b010f080a020a0b0304061b0c120302041a0f0d020c0a031e05070f020f04020d090507090e072303 72
    0x2081d0040f0300440350042c0d1120380c00c0840d01c07004255080c0c120000b0034080072801c0c1e54255410710810b850340c442405990f042c8a2401d800482d03590861a981c000040200f00084d8001c070540d500a40d81048129044001c1c0001c9110761000790b800f08840d04040001450181c0020b036001e84040c00c034202c030840c1002d10105441d680d800840d9042100070040c010440500d90300d2000f481d0300c40081c059200c003074000c540fa84015001c2d21854500c0040058241301154105e2030507202000441d03028000c1340c82c0000c01d10b02c035521b01160580300441488803a6842402a6802e44600200c1400102d0402c41c030f451f00340c1e0250300b00c40c44c00607061014041081e1144050220b0003481e0015200e0346c070161400500c0c50358400b2803184581103107181c01d4501584502175524141d40b201003c801c2e0111400000e115810202036036030b0140c00000c04180e4124070381c01c0b4545840c41642100c6000b5154012441a15140032800403560f101c41d60400a42e40e821294600c0107124400c1030006040b0700c408241 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 452055917 1250 452054667 452054677
    0x30609030c0203010f0b030615010c08030a02070f03050c0d030614010e120604060b100f020c0f0f040903120b03070311090c282c12030c0303010e06040b15030402010c06060308 77
    0x5170460341c0d030501c0c0d03629041c18420241d200c00d58001c40c4000200042c0080c01ca54113844000c0c04020020000030b1003110170b0f50480b00480d0704a8040400181c1030320b0020206d074408040816035005040d01d46800b64024040c4809403504c0c10700140c61024200700440d680609519042e0b0700c500c180b41910000d107000d116107030244c5d0052001003048130116061021410400c4031040402110fa8046030000f9808100d0502d0408212141d5008034451000150300480621070700d68414a4294030408054020851480205d03a14000b84110800c1c0d03401c0503115002c130700c4041d06403001c099040159203004800c0c0c6503c003c022101ca420406d004603008244800c01c44800f002101d03140000c0c3c2025003042e81110f0b0f807564010308414001000c0c42101c0241030000d021400f0301c022002a00c0d06490a205a49000c1144800c0b00d0b260340c0e49040d00042010103542541c0190702e02907190046092941d00c2d1401d112010030326900c0e40c0c81c0c990044401c081c50000503545907559a001100240c0c1c0003000748 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 452057167 1250 452055917 452055941
    0x6150f0b0d062309130203010c12060b07080403060203060103110c03120a0c1706150a030b0a060e030604030806180106050901030b090106120911030d05040e0106020c0a030609030c020301 82
    0x592150781020440302124000d822102c51690701c26450040351403456180d42a00f481520610a2902c07040e502c03c8213100707151702c025495400c1800d42c016a543c0402c00440c081d41e800010b000556481408494a10070518081c0c4443c000300020300108030740c0d8004641248061400280003007c0302d001c543c068101c5010100c4542002401e291614280c174a41c0f5000842280e040000c03819a25001d00301c1140e0703110207000b5481a4000076000e9850b8488000d00405580c40c81d80c0e40c00541382e004005060305888144501c0000c0f101080042c4944500001c400d4003038010000c68649480c10b842089004044641c00840320302217045202c90b800301c1c0783c0205242d071102a120b41440c40058207542500540038011185c08004002d2294454a145901c400304100010302400c1c601304003400390354800c0e0300c0780c05106a40840c1100e6602078000c004450380c0c145046510398039054126241c0d00d12940719a0701c00e406e800e00340003007609035010798403003072007818041b2598140d6404682500c2c3c1c0280c9007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 452058417 1250 452057167 452057189
    0x3130611060604021206040c020c06210a0608190f0206070b040618020a120305040e010e041502040b09040c02030d320f0f0718080304031505040f06150f 67
    0x29552440e010000d4580248080707a082d41484045c900c85850207000a00b000c0c844d90b1100c0070004464001d011035074038800060711407507850000305a034002d4070204480b084001e80084001032007800c024414001580c003203502520908101c4064100806c034045e80c1518100258140c20700143e451800400070306200c0c1c1d1000000d41b13440d09124040383d04e80d000c0b01c01d114035000710480041c0d0301c150052301aa8007160f1071408c3c881c5603017801c803102d0180c1d4100d80e51010301e480000c605900541c220031703c0345205070f1b145009440e80140100503401203200c1e5400e90501032000c4040b900c3d05401103121388210b4030480b400c0c68180300220f800d503412101070319070100d025079112510001804441c505c00d02d6441d400041c1f400e2a40821043c5c47d0b005024062843e429408142e030644035500c20f44e48800741810034403850f511000a00d4403030713000e403204850305605801056558601405120310030f030341204001e0603009c01d54440c03101519000028001d0304060795800311f109514400220301804c4e440c004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 452059667 1250 452058417 452058437
    0x31006090b040e0a03170a090b0915090a1101122304030e0111070504051312031a0f0609300c10020304050901090c1421060a0b040308030603031306 65
    0x284011901e80f500a0303049a00304420400c042030700f04260010541801c24031030000d03a01c0c00d05d0f9800621344410010b0124040780240040d1510009210896211408200ca850f131107003507900d6515080800010000d0601c0c650489456004400e1000e12008215021589400058400c0507030300706000800032407500c82e028882819809160401000020300303028088450f103002c040d6030346110b4824544a9611080024078141410043d120031a900500d03480c1d0b004003288029000d02814500b48101d140f01110907034092400c924a03c0700c40c2405864585000e24000900100344518044003c80c4040003484e5105201c1c040750701d0070442e040e40054851201c001e401c100100509406e91411584140000e2050703503a08034940e0704503110350342c0c0050350003128002a1248408031441207221000401c1d1540b4401000c4c018110340c401204908070259600c204100351225039019100210006000c1440000d105000445d0002401002c480c20100740884940d0a61140d03000013001030003980e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 452060917 1250 452059667 452059669
    0x1c0201181209060503150f1302160b1003020607030e181503070e161d1e0414190c0c0b0405010903020d030b0303090616021504061b020618031006090b 66
    0x1d0b02c0030303005601e000d40c59400d1900e01080d0310048400168818004140c3c6119159140030105c81502c0c90f183c030941d142d1041d04038070f072a414400781c0103441407504040003500d402001c51681c800c1d2036000b84124141856034030201e4030704204401c2d181d08082d101c2042211003182c0309105115400815912100f044e5220030306040550640c0300b0702202e1010f900740043c1d00103038910444039045c1c0d40f42c100900e03207070f4404513610030501790076007a0001a101086444005491290710380244240d6052180950003131411031b0700c54013203880c004261028544003c01070b4550f081340c010490185402034003881143c80c0e081850700d040e03404135040d0b950713040c8103010545c0601094003040740500301001f80d4070b0b807000440e4592207210440c610a640021f41c661858200317071601844290003a10302800d60041075520030b03055015004000200c1c0140144c00420103051074088500c0758094900b50034100301d503140082d030076005410194140140340c190100c0704454811503004042d04034010a211300050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 452062167 1250 452060917 452060927
    0x6040f092906030703030f0909060f052718030c03180123071511030403020f0120090409080f0a02100c05040501050a180909050703060f06081c02011812 67
    0x1210301e0000811841c2000203e650209001e070880c0d400d030600079110810307510308071481203c40d000200301c04c1c50104003062510074006a1000c1e1001555150b1490407056401d2503481c25000030090100081c000054a58401101010002103981c040b0b90415030210903581c11600805501402044081010011907130b20bc0264000210400716405001d1078851654007076118124020f8240c0825110050403104998032a07180001807a01d495120b08003854029110f0034900b41503000c0d50b0808400c1020702c0340d40100b0700000046500b8543c81c1010450500003d0b246041d0150380089092100b00f22100c8014024240b8102c02e80c0900603c1c1c0709280c2c1902100c0c0360881080c200b180500040c400340c0d81100032113000600034282001c1c1c100e1010b0804140060340e8100c03091890405c003405007004000200d1030180c0340700e2041070100303192120811303084410300c1c4035080080e44a648442100d16240054102c01ca01e6840041495a048082110b640400c404110790314980c00300004001e80d408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 452063417 1250 452062167 452062223
    0x90d050c220b0a05032104091b020d0e0a0302040b130504030801090509060105060a030f09020613080c0306090c0d050c090c0301031101081501032a02070e09010b06040e06040f09 78
    0x84804000490800340866035030002e80c883d445186d00c0803050030500c0d040490075a402040202c5003445003107030a546040001c0e9106c00100058440c82c256003001c1d03405174030408001c40d8007900c004691469602004043c10740803e4541c0c00c41058003621360060413078018184a68082d813148141c95160058580440304000c2007607070b0b1500300c1c100520050751444100e1b400c03a4010b140100303101544407090700c018110080300a40c0010300180303020500803200030082c01c8030200f40c292030b0b00056507810b15484039400c0300c043e2541d4100307070a518401d03d40359510343c00c0d540c090011500170010382404100710b44010303100f4030302c80c0d200840104104003e283c01c6080040081c41d205905080076040141140702001b90103040c13685a08807242744000312282058802c04c1c1c0c600c8020701c0502154041d440c0c07241c45c0541c10450240301d000982c090814020034120040150845103001d18007504550040800b6288541c03140c5c0385c40a07004207941c140030b15490a40564400038000e25034200e11403102c900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 452064667 1250 452063417 452063419
    0x90d0f0c0210050904020d0603060c0f0206010503210d02031306050703230702010b1512011a0a1b1202150a060509040f08120405010e060109020f090d050c220b 70
    0x180c8545a80107031107107a402d141e01c0c580307801d00c241c0780c80e90a40040c0c040e00451484440461411030004140501e81d0820002c5040644070050814401d420490320f0b4a000d014854059005c680038440c01480e960841038a4a171054801e810003a03550812402c2c0c2c0c4c001d50340394010401072900311003803112607c140390700001c490608000320030304070002c440506100c801c82012005010000b030952070007034024840480b001400c0203100c010a080104242e0040c072407c1d01c90700640c2c0c0001c030305241c40340c400e80641c220320031102d400d00c8040c0c40c086a0600340b0360031340115426051350a00008054501040f51200b4a0f00a4031909110300303030302ea0300428018018101c0c141041810496a141c06001d99000303900004040c0e200400350400c0201440f07142140c4501900c00c40812051103c10b50100d201c0914a000362106640e0701d940b0f030801ea000c0e008084036030300420002d040c1c143c6002500f9030010f07482081514055040b1034005a00514a510360b00c0c5000c1d2a01030074025004a44604c40200c68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 452065917 1250 452064667 452064677
    0xb040507360b01021b0310090c0f0f051e1c03080f0a02090109090203060607021203040603060905040305040608070e12010e0105090a03080c18030706050702031b0f10110105090d0f 79
    0x1040c0001d645d458a255a0804d090010740c1091040c1c03418041c4985088450740184119641c078508409041502d100704440b1060207070340070918003c0d94140c80b0461301c0050044020000c04c140103007a00d4805686d842e44622212445040079540f9450f0756240390080c0ca0700d140c40c3c90302c03060f8a404402c1c02407103650f0307040c4104100700c81c90307801c6071a4030251007202e00d005840c0c1c3d640c84046611403161450280d8003035000c0c29011503a64000000704203407040e540e010f100d815604c4164800759038080d10001d001c00c00034401400700d80d11036122241d01141ca8036121002c0f005040100384000c0c21a0190399040e5121490740301c615900740103031034000b8908001441102d84a130ac00504240000d4411600b0303c030009643c103400345415007502d50040780202aa44880e5860320f003c1d245600c081403c0b0b000f409410402c0c0d612045640c1145981c90700900424011030f20b4504125107240004421800d003c1035548000ba012000d1007810b101d00c004000405950466440c0600b91100d42905103013000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 452067167 1250 452065917 452065931
    0x70c090c080a1e093f050a05070206071e032705030d0807020a0501150906050d0f0602160f0c03050606060406020c1c050115180213030b04050736 64
    0x10342c41e49019045008010000641440ca0301e040003402d0700f0b0b14400d001c021180c04038951030342c4201995494240b5007a05c0540240e41c581c50540b4030340034291840c40402d41c00d021040240c00c1150040048901c55074a074250381441204c2c0d010f6180c2d409130183c0000b07001c0300c0400b01c01f00340f8108801d881d104600d01d000309140741c030000a641d00c0150220004003c0f0b2480031920300c5008000b55440e03107900030020b010694221810901c581c020b80303d0510143d0401c14002414100345608401e0150800c4555680b8901501c50402941c0400c09ea4000c100c8a40c0c01d0101060442c2020440303a44074504c01881c061450034680d15000c000760690340300d01d5082008000554000650182c1e005059504c902c4000c22035500f460115110640030b4155420103580020204001205a0588428140c01140c80c000401224128069500d040f020a40001402d20126909040c17540c0c3c020301c42d80845038190713101c207104802c81d12102d850004400c0c01b0705650300e160340c02041c920101007028008000700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 452068417 1250 452067167 452067191
    0x9050c062503031d0307060b011e1d0607080d0e031303140c13151527120b0103030324140a03050105101406090303040614070c090c080a 60
    0x41c80301d4a20740c8940d80002806001058020780140700944154030020941001410003191603600194080710706030300c0c0c60030500180d8090f41130b1030ba400d40e061024114200c8117600c1070b2200140713690341000d03035a03040c282c00010381c0d2800010700a951141c420161a2404550044240d9240c0340b4115490340051142114000700c4000210450750000901601500d946080030709001c1a03900198100c500c03c01e56445007815070300314101c84143d5010f200784290356000d420004802020000d0005840301c401050041d00500c1688502071001041d022419620b0002801d0a800030f1011506c500c0c070800100207141d01442070044801d529600d180060f003061017015900b03070040c0039040d0384040c15040c800107600c500400c6400b566110000b00500d04105c801000e0100e0144201040d0b2f25582c40442480c0c01d0005c251040d81a000e001142054140321055460408104500211404c01d0104002107044020300c40001d011134000000ca441c60514000c04c4404028104800c15003420706550403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 452069667 1250 452068417 452068447
    0x11101061a07080412080c0d0c02010801060e0121060f0603050f0c03040501140114191a160c031109091908030709030212060906370e0d0309050c06 65
    0x1d030040340c0c41d56aa80d00300da072030016140d0245030040d00c9500005040d06040106100007000d00001060464400b03404035202210485200301c2e0081c0000d0f003800040103284e018486501c42640141000805803030011f00303003510b0011103c428000c0e0f40e16640108150040a41901c02506080c6410320807031030111905208005c2c094800324500d1400000902400406e500c1680600d881c546100c0c10342d655443c004143c1400181c1d0280f05095443c5280c501d540f000b180700007222002c140200071144030000d01d4000740c0059103100400440f1030781c10030000e000681e00d000a18814041c81c02c00c0d14001d001c1c841200c1c0020002030942d40034425240341c1400b00e8180c2c01a40c1c0e4000e04281d80d80d80e50646c1250305042590000317401c01541c82c10500c10f14000708039544034601c040102d4403180d0300d0124180042200c01144141c01040c031103c440e10390035a100c0599844d1010b0f202282c0d118900810515040300c103013140300003a17070710084801084418000480090000c94500d4209060003000190b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 452070917 1250 452069667 452069699
    0xd090b0106180b0d0212100f0617040f02150307030c0207150509040c03020d1802091302011b02030115090c02010b031c08100f151e080705071b090b01110106 69
    0x710f0710700003043e000c61107282c41e01252621888450742000c14141820752200d8a80c241c01001b84038420f04501044252290780c402000032a40010064a602c91f40c4500244002800c2c0a0741c00850a8841d0880280300e070340203500844042d5800200c0300c003100402804d180840d002041030300c18590042e00359603408010b5804a00c0216130028511003103942c00c0e0002d1164028031898241400c1050340d0942141c80481d405900a0300c1220b000c2e07a440c004109007a020420007404500380706446200b01c801c1a0f0101c1d44644040c00028130420352810101080209a00c0743c1030340390f1210a605507103a4280140c420400302a40100341c9000041e851510202031210250100315030000007900c603002ea44a6100180101c80d4180d25880c2c1700c881036442a18689003d0001c01c54003520b290360031100504e00c8110742101d40d41c24031140c444003800c031003073340c040031050752508440c000c0c0790006040d920307001e00140401344000852122000014000310400c85201c2900d91412104210302403002841c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 452072167 1250 452070917 452070929
    0x304050d110c150a030b1203091c05030a0f0e041d15070e1302130f0303180b03010b070212060f0a06170c010f1412062b03050a0c080d090b010618 64
    0x1075104c070366440048001300004222280e0041602a11004400d4040002c280300d000542300344900014120000c03e91082d0340c0380040455004202040321603100798424400c0e00e4051600710014245103000500759444980991481c0b0701c07462403000d551008020305140d425050341158080d2400c0d01c0060102107140490b6400392007041c902e1400d807416a070450b8403141417100c510041549808050b040d40030680000c401103100200041c1c01641295082e404650118804038596820492114000e070885c0008a82015009a06003e4101c007400303614452402c40c414650985842180102038400580c0071360314801e0044000c1440003070110b85082c02c22401c3c00c1042040c3c41c00d03602120501071409048035814004251108210415910217009460031508010704036a43c94209404004140c100c00403a205c10425900203800780024040080040c00c0101e01200552a00c001c20b9001c210b450151541d02c1141030304004400c070503580034010500d4000c2e040f181e0303454101c14107115030040e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 452073417 1250 452072167 452072209
    0x1140d1e0c08090c150d06030b070f05040b0405010c06090b040605070305060f030c0609030a0c1205071a030f060316030809100c350d1b030513020d0f06020304050d110c 74
    0x40c06032004120103d6250300d200740807c1105a950f800c0c580c40340d00041e1061000a410100484401803003132040d6802e0f40c6000b202280703000d25200064034444c820601c200e0b130594550840030003182021060501c51030146202090030b290000340201296402080d0500c18084003200210303540703000900315286141625401d80d205145400246031188621008040d0619002c0224150402d01e241da80803501c00d0040f50540c1d0f8440c0e4690b49101e10768600040c82c114107000042c091102c081c0311a400520140035608902c030304a0918180c440150015a600e5500044440250911484507202c031120381c54024104005581c40346c4c2030711440c00c5040100000d042820042c0140c00101c19a5856610440c582e80c44010400501420841c8051180b008020311010380c09070080c06035501c035510300754500840807910303402c120040a4190b815112700c1030301c1d21000c000a1441c401180546e0140004003031000c030710a002070640e009061310f545607402c009090413154a41030040d903450410f103061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 452074667 1250 452073417 452073439
    0x909050c030a0f0b0a050f0a0f0e061315051b1c09030801061107050a060c05190303020c06010b0a0212091c030807090905130201140d1e0c08090c 64
    0x840e00d000401044250316004540040303003088802075584281a216403003622850366a003981d0000c648048542d00d07607420410001607101c000650204000e1014800300080c10142c81425900d0250110f4010024200b025080010300c4981450a008120107003018800c07031030310591000102818100003000c0768004100242409107030365094910301e500c0c1500304903201c1c407070070b005200940a100300390108200841070680c030000800c001c0300b42d480207415003800c41e2800d1822124600c100710161441d001d0f54201001c0d542c074000344039a40034060f0f81d01607150f60708049071508004040e03102a0030400100b00c1d81010b5034010800340c401c1c203c030928481e00c45580d00d012402441c0c440c1c1c15251295a840340e000304058200b01001d014000507540d269125848400b482c08940c41507840c0a40540030007009001036202e105e0640130702c076603c1d4415060150302d40c102c00581d10307055508150700150340e0080c44020b01c6842541c4000c1d0462403c0780050500340305054940e40c40f0840c03e4028080020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 452075917 1250 452074667 452074673
    0x902150a11030d0b01030f090b0c090a090608160b18091506340f0b0a06050a0906060807050306090604153f03050a0e03071a0a0e0603010f0909 63
    0x900020095070040a580c0d80e041011207481c000c003100c4026a000c20b10340b60f1400c0c00801c0910504100303a5000003411b441d5100c000b4046040d41100241e140d001c4400740d00420f40c44168060742d4000c0c24588014001000e5440c15150110040c0d0442400200c0501410441401401058145107001d90b40d04845854481d266030448006000254009a001499600807862a0311029102c141250300803014840f49005024890700c1d11000b81c0004000040000070409280c0c1050708028030324400520981d031000800c1e007244c1694010031203165918010040c2d2341d08881d881e540302950b881c000b46145088000103543c0030015215078001d070355074a40b13201c0c002c548150391000b904505000320324010700301402e90903140c00200000d141c14403409401d6100124401d0030112680d1507150340f400c001611100f00e55210800c4c003219032504c142d4000040c10010150b0000100c7d0340604102d0f960b14480801421030207800f018640158800c00040081031045605c1b80143d807821078003c00c903030207a42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 452077167 1250 452075917 452075927
    0x80312011806050402180405160f18050301060803030901051515090301140129070305030c130312030219020a1e0303022502150304110d031e02030a11010902150a 71
    0x500700c0f07904680300140c16550b98101040260007480100d41c28800ca45d02e80c40ca9480300b030700000888000c11581e44504180c10702441142e50384104070000103100a5403140042d0945001387c0c4200c149400000c280722490400303005a40d030000d0b4550100584042d1315012540c101044104841c407420049018003c1c0d540c01c1d0000f03010b21010440005407561502a040940710020308241c240071000710521300348803800d03002d89842c1901521081e00f955241c10340d400341035000c040e80f6961142d0130345020000481c0b00107020890307180e961300140c89800041c1011600010240c000003503500148460740020103140c0c400f4101c00501214245108203450254040e004401e8811040500e030b00d0005040c081c0d50f0554100d540c000c65020184202c005510304580c4015a009000c003103000c000400c030703402d0940c40601103501c01e180110349609281005000000c0c0c40400c035006030400202c4e0680d459001a080c901102340900070040d020481c0d000500d001c0041c44810041140802c034540301901030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 452078417 1250 452077167 452077169
    0x1b0a0e04051c050c0c2b0c0f03060209010305070318081b0604060c2a0602070f050a0c0e06060a051e04120f1703060915120d030501080601080312011806 67
    0x102d4a4003082646405001e403694200e00020082d600c0703050311101c0140303000e0310064101080b07045030070744030035803194614070000c20321500742c0d0350040985000890003448481c000041d80210001611481014001016510301910400401d810604065040102d41e00c41045039680829140c3d80c0c0d40071501442c89070f11070941c05010314050b0000b0807087c06102c1c2c1002c6084441e65484040ca0100c0780b0b20b0180001007403c10b0640808150f03c0003001461940c0104165030040074640c89103511503403a14a8090401c0c4104d070011221102000312038012200d154100a04071500e40c24a120180001c18501034039a40074940c1140d5299220031410000403503000c3c0c8980c0c4260503030554581032101029203005011501c02005413542601e800c05402607a02030301c0002c180300e00c65210303840d400c1e2641c0843c502195005926007031107841104200300720400001d11b520701107207542c5010700c07103420110b050740081c80a400c200400b0022440c0a40080c0c1035540381c110008500d5448071150004060b5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 452079667 1250 452078417 452078443
    0x512100c031b12061502030414010309080708070b0108010203061302031b04150212090a05041a1c140d0c0b0408040e0109050105130c0f0c02010e030d0801081b0a0e0405 74
    0x70b440c0201d408140d204494500021040205021281d03590103014010102c0f0560180107801c10301042c420300300c00405544d5013190500d000b0032519901c0d10f4810990380a88401c4600b20030008060007040540c0c201d10780100b020b10b008600354900b0801095462100c030b04800794060703002000812007943c000f00013540e12542c18903151120340b142500b0201c04910905800580b00d100e10740ca00e1032945c441107071400f040160080066034581000e010280014804602070b1148000284c621a00d543e0a244401000f6000d8512011070b90b082c01030451130480c00300701103038125841e13010150f40c000104c652015400104201c0541e038a08041266010b10b40007031054178001d000001700300030749030407040c141c40d011281e0305c01300404109900304803480314980e00041541e1300078402da558000c0c0480001c1e80c0c01030400e854204080c00003c0c0c04e201c016207a5001150900c0c005103d007035800c0200c2d2030044291407110395100d40040004dd00c261080c072400700401117240000e0100407091100b0038510711 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 452080917 1250 452079667 452079701
    0x60e130e010c020105070207090603030906081909030203090a09090b150619020a17090108040b061c150501170a06020a110d0917161208070516050a0512100c03 70
    0x2182c2d04000c2c040c00f004e4a400c4014480e0300b00202c0c06a015210340821a5450b454841d0704d10301c0c0c41301c1a2000e100c020501c5c040b0200084499947c91001e002e0840034610039409155610302c00c02c20409000103a403c4050418a4000501c000035540904190401c128103c2d60403505180e5000507503911503292411909200052070b5010359030009112001a44500c203a247c92050b28000189640a071050042c0080c44e10310104000c070315600806500100043c10300c80011031011034940307c0c95034204e41191300c0c3d4620760030b59001d550180718040c09030100c149030403501034010340c0c0380e55680703000c4d171000c0c010a0b80001c070001002e0203504015030844000d000d40d66481e0b0342c03c1011b841a8014814440404201d80d0b156603205008561051440f016904030401e40d03040484040403050f80d91021079844104210f400c010910802c0b003800f8403850a04905c00301c40c1803406000340340d201a4480e40c024005616101d601c10000314030311080d0500904000395400d44848118003400e9460708c4524014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 452082167 1250 452080917 452080931
    0x312130206070215040e0105010509100c030306120b0405070b030c0d05091e0309010e030303090316110604030b070e010e010f030b04060e0a09060e030c19030201060803121807060e130e01 82
    0x50084042c05c1120001c44030060703142c2e40c410043d80d0620030380c24002e9210003901e032210400350141000030441c0307000346800a0515156860903041280c003407000d44004c10318104220401004000d180003800c6140034680c114142520b10924900036a000311165640b01c4000403108203040080301140c0b520100030403180481c1c001c80c075807a903106c802c10f180011201c2c07840900b1814000f0407240504003140096181c41c4030100303085202d55500000321403040611242c41c8840e42d0305005040a14080c20030310407a4101088050b20341c00c0300e101864140300148600c6001c0341e80288084803408040e0a0124244501200040040c00c0c20b8000301e00b0310000c10f0500c0207980059201000507441103d042240020070390071240e683c081c20341060f06a922070010004022400000072900780d119000119000d42c0f1000c2407404c0d60041c4001c22869040d5404101144c00c1e18100c2e60b1100c01442c2c09840ca07203017821401000040c14100e0749016544491004c42d0b0b40e82603521051000806030001c01141c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 452083417 1250 452082167 452082199
    0x328110403060b090601090512070306050405012702210f010608100c1403280903030510091416020712050303040b100b0702040c0306030501141803121302060702 71
    0x940c20900007a220a8900300c0c0811550400300038460140c4416120118040d28000822410a00244091030940a07004001000481c0e0340103140c003480c030505c00810354008241c4420302c241141502074061441c800501c00150f00d80348218000351024a039644003010500a000f440e20300c030101d80c11042d618025001410701800716402e0b5107602c0d54403041c00100701c01c660444101215500c0d481141c00300300003264440c49803940f08402c0405074a4a140c402c0c40300c0400c541200d041d40e8050b40440c0c2c4450411981043d4081c00c1400741143e06401c0122400b10510651501401410741d0400041044407130f0b40c00d402000582c00400310702d1503500381d10007189001610727504103580849441c24030b00d02140c5904120450102529000460302d814001c1e180c0030400074003400207484052655039400400410320038080d20705640c01501100c903450901f00c02c10842e80302c880303602c008a80c105008180420440644403500848041c0001c50f84014500005010780304201c1c00a51054800d801c107006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 452084667 1250 452083417 452083451
    0x1103130303020d020318040209032503020103051e041410020c030d0c09060c06050408041205030a0f08100501050c070b0c0703120c15051b0a0c051608030328 69
    0xa8a100b5825100030007402c0c4003ea03a00d01508002c2c161303002a8031a41c4400e414a03902a201c040c00041c21554650b101461389000c141000c010003010b942119414419540c050203003030303048900224608840000020f00c038014101c00344c001000800381714040c1541d00c00401070022055003a1508642d01c1d003000d2091641c035400f40c0c0d01320040382d0419031702030740b072178081c40140b0211032054179030688000302c90360340c03000501c001442181c42c8407041c80045900741c0050200e0000c2446080210354501d20b0b404041e1140401030400c50410100070100039021044d80c03880800c440d0b080c00c056494100340c07032903a41050a070307403c011950f8601052a042c540400136846088901400c540d170594025003504480380082a2009405400d14000d540058103c81d44060740c0b01414081040d4200300389058401c103940319040607000504001075003414040203108000d103221070b2003c0444480d281c0041c19440e130000405501c594410b10404010418941031816403106094400300a003441807804441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 452085917 1250 452084667 452084669
    0x40902040f0204091103090618070b0406092120040b04020c15091605060f07051b0a090510060c02011812030f022b02030403061416050a0f03020a110313 67
    0x254445c2040d0724003528061500441c0e004003802c4000c0d0516036542c1c4454260441e149001c403415109010740000d403142d51a01504c050102542c41054862921900b09040c1100306401c4001058a10f444000038488298112107080200c0052040c2003913100090000c004012420760040c0c00014442000c141c0403c0ca4401c60030004070ba1191612514000c503901c00210080300c10b40890800300780f00c20719144000e0070968040710036962030015903942d40e81c140704540301c030003900d1402c0c0780c0200628070344684c1d40c202800f41800304100500e000c0260803268400c911501051007014203402d01517911944c1481100b980d8900401c1446549090f00300915005600580000303881c062800d023181d201041c1c0841d0091040c0401d15103000c00488040c0c2108101588025031008201c00000a030050103210300840006c03102e864940782803984400710a90241c610340c2041001c01068422540004130450b8903050780c5001038450345221000d07503280140c4040d0012900c0003151564101e840400550 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 452087167 1250 452085917 452085929
    0x703111809090d020705041d2a06090a1401030b031b030d09080c130e0d050702031203010501080406050c39070605040e040c1a0406020c01020604021c02040902040f0204 74
    0x2074480d80e96481c0070398035003002115030740050300440e0040203980303450b03040380600744456920781000c1c0340014981443c2209039800280682c0780c0102100c4145c03042c403010000418241c03480e61610100d2000a41c801c4d626029040050705c41c02e8003030200c0d0f407103a1701400d001e40e0302a040720540e0710f1600d00111035488441d1818860301c0354003513021031184941d12103011981800c00a251a00303003542003080c1e40b0116018208150f030342d03840c004810141001010544581925090358612143c0180343c100280004440040002000100074030703603000903215801500408009019104c068240c550362186c404c00a584c000350072000070341041d075035451300182960884954041901c1403c0c1035240c412520841d0f002c528180b201f0800700810b2030007a81c1c441d01c00e02404040d03c1d1515101181c80c010b00a05600703c1d10089024840c264040000c052120024001400d4031f150581c001510001000001c0c555400c0140d0340742c0441d26143c0000c40000c1d4014021302c8040310382c0700e1620003908644152 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 452088417 1250 452087167 452087179
    0x3020f0d091a0112080403020906030c100903020901080d080c03090a02060d1d0a151104090e06010f06081303030c1b0605160503040812040203120301090501300b07031118 75
    0x1c0d181a90130a00c40d1000e0b48503d2560a0500d0340d000c1010501009060035054024912000229900d0700c410070101001501d40c0f211840c00c40c0140021994143c101250380d9000104414080740c000540c141e000848903c269038a95580040508111010100a400c02c8011850a0a8410580009201c1c140021804010703403070724441f1a41d52141c1300b1024007030002c0c1c100f042c0f448400070f4005064808003081c009152030790f40e080703040450303000c0158854a9040007005000018079049050024500d6240c041c5440c1008070070034101103182c042c02028596200d40e0400070310f00600511510607469042c406e008119410004041c240403100ca01c0300001c0c00101e008100d0294058a0240e500600014100050136900c40380d440005130040e0390500c144000454800341f0400294043e091101e07020949500d0081c2485050003c6500c00556000204400d804111051001d0710245d40041c916680c4e5111040190010a00300c945a9000040020100103151000c1c80c2540b10b0708040c1c40d9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 452089667 1250 452088417 452088419
    0x1e2406130b01140906040f0f090b010206240a0b03070206040c0b0711040b03150c090307050109080309090403030617010207050729130510110c03060c070303020f0d091a01 75
    0x5035044980310314506000c201114034610080c00d65902400703c41c4009011189000c2e1101048000c00799903078000c841ca809401002d0008103151301400000c0c071000c3c0000d084905081007134240210110740401203005820780144040d50360a0b5048000340f1401107006e949041c00d03140251600e47c00c40c0c1c10340e00794101010018584004404843c1140d0b0001003540e440d486401c1004082e02200d10940d505228204c0040300404c880c0e48214001c0e60880d0345036554030004000d06003015078551185040c0105880d081000c2c80c404011100325503001c4a1b460825a42d070701c0c00340d00038070b50707900021903404010b92141c8490005600a180c414001d00440d1405692512141c103000600d444030000081e6440301160449456805460007210000c4060071035920749000c40c031084203940100c000601d42e0703581065001c80c207210904003c2c00c25009028145003100303a04002d0f1191800007010581d000415401038454103040d5134821761403000034400340000d402c1070a40d00100c0482080740580c40340c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 452090917 1250 452089667 452089699
    0x9041406090f07140a0933060801050409020420041a04051c030903121e0305010506091207050622210204020a05120c13050409051e2406 60
    0x384400600e030184000741002c0e420203035141045213640001c0381e040b0f1251100400c090b842802003035803010b2055040c85000c4074540121840140080074000c0001e5000005d00010740c0c410140c0381542d00595000c0392155040c0b012800070444e03603107808984000119501e15042003c0010022034000d01d103000000050309488040340d218034401c803980603104180f2402c0c0d0905141e00080c00a000b410400039082e902e85480400b090040002ca00081c907501940c425883c070103000c0649080e107460704100a41c14040480c4081c407a54101034400c40c1440c82500303030440204901006400040d200d15100d165100c402c00050030112300b410b0088519201c0402c3d000c00d1001d000352540c8800b036130a4000c03105602030000135031003030b1544c100300f1200f0041d52004071403c844d45801562280c103419580c00e0900f042d0000208550861880b50303042480960114a001404090701020007940030000140300d8956482d10203940e1003045021110914a914100080e41c0a8400e94081e5500701da5140101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 452092167 1250 452090917 452090923
    0x12020106051516020904050f030d052e09023403080708040302060402063402040b060708040e0c090d0303060e010e0103151d0a050a061104050306040609060b0904140609 74
    0x480ca500207051180365a01510f8000e07201e1b40c00038096815500c600350f05030075090035a0b008404d00004191a0f2081c00300c40c0c1c030034010030800810600044940009004c0054483c0f100c94442d0084994000c51034022085500a007030020400402040708100203100210720340c060608010b40104a55000003070510b03009070030702803150b58076501410240d0340c0e542c00c001040c0c000e403090584440303050800000222165503080f02803400303540c0c002c825000520401040e1102d10242c0d1340110818040b490000303146000341c50a842030f078001d010300b5540302e00c1010218020b408046a12480315090748040c1909580100b0994800840c020901c0ea00c40c0038288000000303120080001440100c40502c000c50ba6200b9030843c3d00890428114828411126280c540c032010240e9650b04020706120411110340700d60504403503004145402d09152038002522070701c00800240c07103107817608200e508000650703110000343c2000501c4a4414141801d04200c01101e980e1099401e10424010501d80c0d2800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 452093417 1250 452092167 452092177
    0x120d0e150c10270f120306060e0103020f0705151f030b1518071106101202130b1c0b150303160f080a0f1202190318120201060515 57
    0x2030014100601407540341d10042c401e07200120481c200044102c41212503482c1c1070b0b401c480c002e242c100080311300750401c019070001130b26048052610b000c2d001c100346500004c1503080c580c002d00340142c890f2041e039801d1102e0300c1507040081540c010030b03406110030f08801c2c00c040d0158213030801d1031921110206050f01c10b804540409030a50507200001040da540c00114410310090240c01c84020070803102c0c10004031407003642c00300c0101d00c40c850310465804007000041e0f8030003801003803584114907044254503240386031300b006800b4039044484550080a260403420044901030f04444008050004801103600744410485696036030750086200a901e112025207544401400b851400130801c500d01a003030b910b80402ca421001c096107500100f503d45019120200031a10b030340c0c08440520300010b10303015407000504a428810300800003000c07204156120160024100050035154440d61140311304010f0710000c3c4580c075141e000c0107020b40d06410100c115030050320f580402d440a406002c40c10301030303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 452094667 1250 452093417 452093437
    0x170106020c040b18070809103b0a0812010501020604020a050405060406081203160f080c09060d0207031806050c060f15030703030c110607031d120d0e15 67
    0x1100c5298050b16181d4061003d000e80108412a1a1510b401020b4102d0b81117520002107501e090811000d0001804002c4018998010406c0003038250104a01030215000003071230f01181c2104403600b0030320706409011158505508680c1d04191501d481304969122000e8500d802c4515400082e5039400050030714021607000b0641c0c0c0901d401c01050100401004012030b80c42034032400c0004503451300f40700c0910400600000700d80d5a00d08154103c20b4504020031303190410007501c00c0b40304042d600008582d040451901800e0340e9101c4800040c805020780c80012021610000f00071041540118100b00e0300141068101151556803800b91860f01036801000e2054021000041ea81c2259445480d4000409c2d546100c0030742c03c007004645002015001100880e038122468401d1040440aa481c001001c80b8000d140c94001d41e030017006800055180000055480d0340390307001c0e90f070754464860940d100720201c0c0d100c9040868020401803d2506590290080d80503440792403001c5401c40301c81080c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 452095917 1250 452094667 452094673
    0x2070f0f091a0d1104230103050c0907050d02030403090e0a0f06150f12021308030403050712030f031d030a1d0f01080f07030905030403141504050601060e0118080a0317010602 77
    0x11040c0c0310300c0542c0b09559104e0b80c0c0142e80320350172005100d42e60481921880502d070980455811454602d150030214104544201c06082c2041039031a8460708443c1c050408100143c1c0f00c0d00c461400362021501034128000020300c00c0f040000400480c1c1c40501d0b80241c0340c0c014407400380c0d40c4200b181107110501c14500001d20068140c100c050051712015205080b005006140400300340e030194190207990428442070300002801c20074444c0c00c00650003c1c0c400001c4804000c2c14568001d00360030302085602c000e041d100e0503001001d002c00315451000310401401d481c0d89102c0300400a080300f0803401000035100300705146082904103070038a08500a010307120612952607110b030900041d00c00400d40000c040d00c0b034071400c000400c1440504019880356180c011405044400030741860341c00c0491050030340300c12007040040381002800b24112149420b1860140389401c004803034950382c403102e020b000a0070302d0000a003c100000d034524218000d40c1d800505d00540101e800302280203100350300c0180c3c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 452097167 1250 452095917 452095939
    0x902090106030b03190236130c0b18120f010c050c070f0e150a03050709290d11040e0601080703120206090c04181e15060803040902070302070f0f091a 66
    0x1800c0d581c4042e4080c407004072000d600d004600c2040010f141100c8c403039960205e49604400704003080313208201420701d001e2900d0500d9000e0501c0184002181603107480b40071500e507981107107181404071011045541000780b102003183c0d0b4005c2e01d41d5125144601c942e2051040014642d05820400c90540d45a52180d0b82641c450000101c00c030191941e5140d03200e144450004006001001620001c01c1c4100c130108040904000c5400c100114001c3c558580c00701e84500c100c659102890070104c0c56204102d14980e0080e04007050081280701c0b04d011940c4104000440d120030000f882504682c461108030a260380c2c0000102d0b229101038800070900e03881107428002d01c2c41e0030741122580514001e6150f071065002d484201400300d80d841da030248400c420940c41c05001900007070400c4003000070010312580b864600c025560f8811840b0b07152400d503021410504062003070101c0c2e00207010000500030003503114802400301004502c11403800c2c3e8600012001c0071544180f9000d5558001040d0100c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 452098417 1250 452097167 452097199
    0xa0204060219031106161b03051b0304050d08180303090109030b13151401090c050f030c04360b090118060e0106090503012405130902090106030b031902 67
    0x1e00209541102444142e0800130003401c020042c680c402c1d0b03030020f4917060407207440402910000c845511921612030400070500402d80007422100c0f4500100709182d42d008920200d00d04500075500602c1d0300c1303116032040e038044c01120780c05420007070b071141100e249107222103003090355a1196051090115060003400c002083c3d1400d043c0c0c1e8450540c100d2a000ea1030203940308285141c12440c46204140c0d10080c21002d40b00c990035983c05403010403000c100400d41c00c800a0402d01901020100e81e85001000640304101c0c41c2c180e80040907900ca40002007004542c2c00c8040c05140c00f00580d030018100b001c0f83c40000e00e400f880e084200b025049070820707400c065400076691031000000082d552036141c0000d400554600c5070b8000d00c801c2d510800e4841c00d00b0704060035210000b4040401c00003000c8200c403248000a0000121003048501908440d48500d00030007030010500080c1d4024125000040c0b5150150403140035888100c0903549500310b031401040509801c0d41c000394020300941c61a180d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 452099667 1250 452098417 452098453
    0x6060b0c07060201050a09170a0210020a0c1110081f050616051504080406030f09051006080f030c0c01030c02100509070e0f04170a03090b190e121c060302060703090e0a02040602 78
    0x4000c400e881134030304480600d2f5911069a00840d074240010b90660f01c05c2c8184040b03070040c001110b60845418005143d1201c00500b8840041c02ea400600c003031544c07004901406113903600003007d014141c2d0303480d05410101e10721007415a42040d9024010060061800780e00c6464181c42698407a1025040a051038011001011840300000655a42d00817000102d1000c104010203410540c0005c03400ca41064045805c082d10070603080281d900070303c104039007404042440007542d1030030701c0d00251265150400f00e1501c81e00d201c0c0e02400310b05c1d110601038000d0011a10005941082d4004020b680314440c0702c10000c0400c0340e0250141c1c000b800050449000400103141c80022803401203081c040f00d854949000e0340554a084a0604079004d45c07040c03d0740d40c0900c446406c1c008000d00300d03500d140c000c3d0b142248034918039610310341180905a04500c9507648404051500608020784400d03462402030051400c0b8003aa030a01c8001000140303184909008850549a107030b0701801c0d10080a40e11500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 452100917 1250 452099667 452099677
    0x117160303051c0f09050d0e030d050909150a290a0806131d2109011b02031f05040309080304080a0201110705030609030d0605040908120406060b0c07060201050a0917 73
    0x3400d4440d0300d039048441417401800e40c5070b80181c2c05004040720340c09026000b001180c44040c005c6e00000301629840e60010203480c6280b41c2514251660381e00c400c0040c240f800c8035036401d030741301b01250300100e505800011001015440764a00804284640b02a12a5401a00c44050000300a000051110301300349103101d01080c0280d8010640148100800c0326a5842ca60060342a0b0f11181c9105d12a80005c00c2540780c95040c52511842c009680000030070003843e000d011014240440702501c02c5440c1040b42c40c4503031041244055808040d003150001921041d41c06800064035040003003642c800100449080702d00b000c0040c2507a100a60054958409450148a4038010f2034000281d40e10b05000561040340c852001d195183d2201c04843d00311202904041d00483c0707482802000207512508903981640f282400b004195518503015000d0089074125804040d80070030303801c06274000083c140c42980c200f60024003080d40c929080c50201d4601c40405460164030003203c00e000700c04000140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 452102167 1250 452100917 452100967
    0x3020a1a0f010b1b1209040b040504050c060c1c0f020c010206072a080703020601030201080c12151212210f06061e030408040f060302160303020a0215011716030305 72
    0xd60f01303c400b204060030600d868071107596000d00000d1803142403030640300d81c0f1a665011076041100d8102038442e5951000e0502d0b00602440000915480000007040400f00e05100c044c00c103080c0380243c1c00010980c008042005000d07214550410f60f156001044141c45940702e680d501c0c50258403240f0358082c64102100d0980c00e801c11940079000719131010002d0070a58001d8001700707069455071000400d8224000c0144401c580140841c0107441c10039440036412101340205650450241c1c0700040340d0b11203070302d011500d900c2000202c007501c014100103000c054140e514040d25160603d1240a09142c1c100d4030b40040d40f0400700040c2061502c800507200e1641044640044036544800c0700b1420740c8240c5007a6000c09002c01e041207082c9801103504064022442c0039410030031b0b1120440032054040200500341078000c60700318045882001400500360182a206d202d55944004651000c4042d0804c5800c0e40549a0342d0708210707206000c903030f04a99040e40c9852410701140070541c8951b241c05401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 452103417 1250 452102167 452102197
    0x4031d0d0f08120702072d120f03020d0203120f0c040335162406060c0606050a0b07080a090506030c0d0b240304080706050403020a1a0f010b 62
    0xa040860070040601521a109104a5550b0f0118140c43da44880d0024a64401c650001e8414040c0000040d005040141d00b0300121244048102d800000103681ea04800081500b1048400038400480711600c0004d01035029a5008640301c401241c5a10540503100837007001d46005ca198039001da01c2c0c095002c59402c8021341456120b03034400060041c500840110104000c8050003401c035030006180752074601412051a04202e10700300b104c80c40c80d440d8060320252101301d644944a161120745501f54510310000c018464444202502300152514140c94191034820046807034144a4044820340b03c0c504103023800c0c0011030b82d51034071780c5d4000e00f0148204807070020f0000b029101c180107180103000c01e01c1c03106e455283c041100000c07030380c550076190b1082030000c017002558030140303031030082001e4941103283d44c0e035581d8101103542d84203040c4014107042c07a120820050507404039118100030710841d001d900b803401a149808030900142c0b4100c105c02c00d158010001240048000c02c5010004010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 452104667 1250 452103417 452103439
    0xf010e04110406090611280501110a21060503060f0a02091504050424090213030804031112010603050c01050903150c030106122007050a0b01080a0c05040504031d 71
    0x2590010b800591140004c952040028082d85401c4500c0170611036800008048040c2c20101100782c21800f0840c200d003040c940400441400400e400106082d0444042c80b030341c440a01c8001820407070403030200b48034158002c9070049500e9003405200129030004000f09816110300c43e1f141035000c03000d040c00410560800c03040c900c0343c46019010581e0540c1800e42500c03185440c09000030303a0701806000805c1d50800829030003a0318a00d8103a02503400a00b0016194403060014590420441d08042c19204002c6000801c1098005031100c0c13401081d1643d0000198100c0204d0070398203140402042908140b00c046d58a51050300039015104c0028121110000d010102c480381039026241582a80d0002005018960b08808000120b000740c4408010100740c24480c002c0d203c9600088070401c200010340c007007e01070b04010402189410070388508035035941d14541076580701c4a07102110084110100010546802c3c42194815500360702e8480311022180b010092070104200541c0d44a85c03080384d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 452105917 1250 452104667 452104691
    0x806060405060d17070201110a0c170a06020c01060302030c0306040c060302090609120109020301181131150b090105120604021c02121503070b0a02032719050f010e04 73
    0x1002e042c0203402450015682e11440c00010301c0c1d8000340480d21351030761010891000281e035083e910300450b0a600e2f505503c120006e0207843c1894011000602044d00200e4007400c091410360024040724400c40c21145200110000c1c951600c074201e601a0103400410000c00c081e81c002e800425141d18000c0425203466240d6000a010741c81da4081100d55a64444071601103003030902c25440120013000d403c0307803c00000d50311085c8525800a040380a002c0c1c140c0024501301e01d810030200014000c3ea0303000b41039a151500c0c0030040905091080840b188080300140140d4190100e903000c80c410b2307550625010303800c8005810510043d02440d00b10342d08120f1841c00b4040c0b0402034401058503d4007583d50880c100b400d100c00d580c05801c00140c200607c0034003a40f40e8000456104641303102c8030880d00c43d503131880b040e03086000300302c0f680c507251401c800d002030300560902d00106040710459194062407580c00c1d918400f82c245008440d0020ba03080403242171903010320000c03041a60010000706001a81d05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 452107167 1250 452105917 452105933
    0x70e01080109060b0a08030703110106030f05061e010b190e030102040f05040605040b030a03121103070f120516050c0a06060f06120e071202031e03040510090806060405060d 76
    0x1a00500499550720000c804000b060b001e01c00d0b813801e044581ca4500d40c00d21a4980d00c91007407600050600ca04c10b2611103050100b9040600219000582503115100900700680c407031108031101411399814807456203000030300c40031460580300c448a00a0030300700710204070715800500350a608148201004040030a55090006001400c1101095820545824240030948140ea00302e54441d50a04220307041a450000c0e5400c210368051510300c15103810240c00c44c000384900710301e5107401ca00000420841d48d40142410b01c402075a9510030010040e01c28028044400c142c8d224a80a080000e440707017190320540151039038035009400d80d501d1408640d66030044403e16489808241d58100b410480c440e00708210f1603c180207607400340241c0c6038070240c0d180c50708001e001d0100c545e040750700000300b552010402d003500c80a0a60742d04a4010102d80641e9403034210b8400c0d0303441911407001030340c40030388159a00000c40386a04010304c0d00d0f8882004100c0600801022140c1202000c551140032074400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 452108417 1250 452107167 452107169
    0x260307120306080c0f06031b0705030703030c1710180b09010315050105031b041802040c030608071217220f030209060103020c0613050f03130f05010f09060e0102070e01 74
    0x354800140c0c440c03406000768242900b4102540c850150392124103180e0301c88004603580888214001001c0300607011000744c00e4002c800c0054514803020900008051705640016050802602d81541c8041542c01c0c041d00c682c8115011071191401c3d0a040182c81601100e41150561521011410708400030200390107d100340c3c0705589408140711081c041c00102d1280e0303405440c0980103081c400c1d0041c4442440a940019a0f80c042c5176600b42c010554148848020300e0030341d00510a20901c0c00031f8a000340680403034002d07410503000d04600044c88920040507801c4013a4081c131035a004546801c4080d07415005500b10014408641340441010040c280b0404041d090403000d41c2529030540c0140580c6501c01006c160605204015180c242d501c0058507941c84940d0005016000006213485420072052420350308046c40302181c5600c0d648031140d460300542e1580311201118030b96681c01150b460070901d030342a001ca0038405060003443d2080d1404154241d042c011140519a50189200041c1003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 452109667 1250 452108417 452108453
    0x4080d08150d08030f010f120807030e0d030302270f040902120a03080f0901020a09050d020a03150902010e0303090a1e030c030b07030506010e132a03060e070801260307 74
    0x108001d0307110810f0046a01412503071f007800d18154200000c178a031000c08100058011000818014109403042c0c400c42c007417070801b6040c60341803031040c60041c000e90080c085c44903400302c0a01c41701844a501e600e80c00c09240d4028180302030b411700081404003c0540b201e040e0b030021000040160341440030005020040d00c80d0f641d410720751801c0314080c18205c20140200200d0790042180c040c000c0e502c041800309403070044407031100c06071051000400c02c20303459100800340240905a1003000301c040d4070040c4d215000383c8071910800012410541c403403040044203980464412401e200c50350285e504011007003026400000799544030b4550407031002d040c0d0b10403190b6890000030070003400d078940905900b00e202824103691158001c5c00107110804140d407010403141d07a5100c507000320701107040c051513401c00103420400c0500540000074054660303030082882503122100450141880703410128101e4904190190b1034000000c41960a00c2809412919500c002c0c07080c240464101a543c4030541c103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 452110917 1250 452109667 452109683
    0x9010b030f1b0306010f030e06011502121201030b0709030f050c041a0901060302030601030f021602010201150e010b0d0902121501051813030302040f1206060b04080d08150d 76
    0xa4001001e20015400414216451002100032603400780d00b4800d4903000035003420b04c201c4001d440c0c2412001090720b90148840c500c0351703e00018101205082141e0100c1940d030948032040c1071003101b14080c0c030840070140c920a001400400200c1c00b000d5107950098540d1408800182d560341780d005954010100681d05038000b51401501d602e440d00c98582d2403112030051a2105001c00002903855005215070024142c0002c0007403010ba03c2640054007226011004641700e488211003610250b01301d00d0300724050341c83c00e44044940c44070383c500c09003222054405041940e003803540901c0b07180c10408030210203c4d102e4001000694840045050a580d001c0092030645506205d103182c840c03042e80814040c8640000c2e130b0924203803088100754000107140d40b14980704120310b0114001d03c20341e4000d030050204c1020220310b01607603020300c3c1141c5028501c1807000075115050802144503501ca916130303980c07100c4420390007117008800c0700f5840424040c0d03c40107451140042880c2c0340480900301d401103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 452112167 1250 452110917 452110921
    0x504050a1818030e0a0f0605121b0f0c0c0f031c09030b010b13060e0d0b09070306050106170a0c1715040c020a02150a1713061b030b0103050702100e01060509010b03 72
    0x204111759894010a0f10185a803020381c81c10601800a00c180e42c00340d90760b55451000943c000d175840c416452025040e0601c565100809000700409030481d00c0700d48014003808507504a203262881c100f00000000078007800030005204407007108805222541001c0c00124030000001c43c1c100980503008204504910b40c0c2d442401d20084898040b0f500030704c1c00d0154071121035840791500b490940f9019071000f0b8a003215120104050314055140d40010121401c0c840041035642d80100c6001040c1d050814400780c5450300500241910f8505244500140442076882c0c4007040c0c2011441e04080d14903610700c1c101656074003050035070380703005400c001590082c0d43d03480460401c2003244941140300c0810500300f8403184801800d202c560074890816a201c10082107240410842c2040b501e85d000008110071000342104080c01e80b03003a2000e0300880d260440300c04940d4024000c09114001c2607002e400c200380203070342590060804096103152507684200210f5a61034045040e406086415400c030384038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 452113417 1250 452112167 452112169
    0x117010b0312040501030f051b0d0209090a0204080d0801061202030a090606150905180f1f060309020a06081017030c0109081b030412020603330109060504050a1818030e 74
    0x81c4050f0030300c04907d03501d48000c020781d0302c95424070122050746900b441a5075848003866100640038000c0a40e5201d042e00c0c2c28804038007000e27030080c03045400e000700b1703100703981000039098648800901ca00c00119152588e0320f44003103100d41c01075910001c02000040e259031107032104401c444064014003010303039011700146805074008090400925044803210080d105c00c1000ea4400a405070000e0070081c1c0c1040491841622040495208100c40b03a000c0503490b43da0038010094040b00307201387d00504030490302086440c41100740c1c5104403002e12034000d00703c5c0381039890510360b104850102c91030b010611030820780c600203005080304240504aaa915114500142c10001d0010340c0c501c0c10503801008104a8000a00020141a6011603079207849035554800140d10f4200c401031038000454500344060030b14000920b00911000a03a203554031252151000d40302403003140071b42640f000380c007181007164001155581303a2114504402040a4078460505403485019020403004039402604210b01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 452114667 1250 452113417 452113421
    0x7030c120c1403090d110301060e0a05010e13030806150f04080312060406080a060906060302101d030115050f030a0816051c08181f1a090f0117010b031204050103 71
    0x20340b031402e2010b140340c240100d0008980440d0300320002c010301a0406c00c0c114950302940001c00070050401c0010461030000b4150340140807d0042c0d0021400c2900400e40d00061502403021655054407001c045448202c00c001c03401c400ba01403103c1c2050b081080c80d2403144035102403c01040c00304011512010768108644031030780300400c154061131070040c1c10000c03144001a00c018032508442c000413884500c0c02c020020f000c60b600041e400164900001070950713440082d1141010100b294000846480000c0500740d405035040100038900841062041c0e281c072080b003450110b002170864040303940075a128040b540041d044405005801c11051050060901400c260f24a100d40445115080c03204040e003c0e0348040c0001d262090800c03a00d411020303041141d02e07040c00c10340350001d4501003810000c401800c4007050034414504140c0b894401130828010079800751400e0035400f529a0309100c1c094400c094846244003040d9242c440140381502c0034030050010700210710915035160b05240014007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 452115917 1250 452114667 452114693
    0x2010501120c0b03070212040b030f070e09070e03100507030b0a0609030309060804020301090204050c0d060e010f030b101212110c24040803220510020d030207030c120c 74
    0x1080c0c400c00702041c40000c8210030a8400c1d1000003605a0b100d8607400f41c22460040900d540641c0c0041c0003602190350055003014610038554035490f02d41e10764030144200c0380a407080c1d151681002c481d60100300558000c41c00015024005811114000840d803014030036680d003a035040700404e6079038801e100d06040c1030031500d0260080707061040500b461076400400582e02d40c0300b160104034180000c60110341d42034000d07076042a002001840281425042503071954802d43c90390440c035143c844005001401a4101d5040f07600c0e041030142e900f0710b1074841a17040b0000601c07003080c0c9104c100c00030450622200106907240d000749621880d9004484020701070045003501c10707010780c1c030441c10b149095840290846441c02115001d040b103030442c020204141c010340c0c000454502001c240081c40c0604500f05c2081d039004510501501a600c000f802170284031611008016001425020041e50013a0001d0003401d20030301e8818084240303611080f02780c0c00302503481400a01c0b004401c034240300c04284c104c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 452117167 1250 452115917 452115929
    0x60d0c030e0a030804030f05040e04060b0a050d02010e060304020109080d0c030201050c0403240e030a08090705061c0209130c020307030e041a0427030c1703010e18011e0204050102010501 82
    0xc04401d2043d03c1c003030300f6402c0060006007044400c2c40540c9003a0b11400654000f4046a400700600703040518100001e0840300703074400d009480c1300c0b1000a2516080300c0c59182d103070b0103031101e48403042d01e4030910445030b0009005a05200e2210ac000964000803c8299600c290a60300c0801ca441c407854000c0c00c1d40c8002e051140c1c108002e00c410b0000c00c4124032110f540f66106014401c07403201c81103003500600b128a040e0001c3d40408542407602d20303003040005101e1114036080c2c8030856101d000f04601d80c096409180d03207000c951000c0030f4804506074000d000304071004100c8c0c1d45660b022080f25060301c00220296006800206002d0700705070b004201c083d0255400c560910a52050603049403806003003400711481140c4441100e0100501c141400740300c000c50000500c0851060300703001c5c00c4000e001c901200c6e281e110b03c80c070817201c040b14000d49050350103400c0b040501e601d80300100c0a02a031750300300700c80040d5a01e984640b40c5407441c020304480e00901c80009a211480d14002900b180d005034080c1c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 452118417 1250 452117167 452117173
    0x20709090209010b030a0e030307020c01080907030305190e0402041401110106032d02040501120b0c03091c1e080105040e0111030606072102010614010f020d03020a0e060d0c030e 78
    0x9040142c2c0ca00744803905440e994800b958582da2180d001030701810460440c038802e07010000900804aa0114079511042020f0329500d41940b03079001e5041c0d8a4280380310140001d03405001c40312603400c80120322450a601c5141c0100c00d2482c0c003001038100e0f4001da01c85401204808910901543c202c000c0d80030100501008001844c0745484840202c0140801890000c07882000b03441e594150020b0718001a8014004001135030311914105003e0400403800d55405e100d590014082c5020401220b1003084200041c008260b101446620b880c40c141a901d41800604040b50490406100b10b828400000c2e5482da625549050144421114071156021060741080c4502c48501510700482c1d41040098500c595600410b0919264038458400340f10898030105034a00c07400c50381504a541a90103d5612190b842c0b40500150341c400320b4050204003503005001003c008a02950192010040c0c0b81088a04200044005404c81e0f1052690085c03141d40d5541007001c0641c18401d10020160314002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 452119667 1250 452118417 452118431
    0xb090303151e01080c0403080403050d0e190510050d050a0501210206120a0e030313020306180c0411040801020a02150c07240609050903071b0501210b030f0607020709 73
    0x3240b803035000707050440c0d0501086501081c84001c036581200e00a5030403044403510303a9160f117003494950b01c4102102c0c0019120740340d41c66184c038181400c01c4103036484c440041d05881c0703000144880c56040740c0c80d00c4144041402512040c0380e4900846e4491010b1090006543d0706081410b0710404521451140ca03c1c2c2d00d8104400584842049880544280c50803042d55034440d9180806003180d15400146400701200384250a44c9818031070b40303024400c0b070945450b40d95141c1e940203820102085a0f049603c510307a0403031142440d0b8002c5141020400302039141c0360b250850182640e100001d000c0060b8014120b0851000308121b29039000b0aa4012036440c2070f0f415203130743c200c200d8003800202d00c001040e0098042d1001c9a030091005180700358041c000c0389004000d40380c13250400304060b01c40540c01c0070104540b0303000b03000b04021784078142c5903a4050150460740c030005165545d1040c1f101c40d80c541550529907010042050500c9651005005074540408001c0c20a1401e6104007505810f04007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 452120917 1250 452119667 452119699
    0x708030a0902012706051833090a0b160204110a020601090c02030702130b150d0c090608240303030412090807030c050d05010b0d12090b1303030c0c030b09030315 71
    0x40002d040350218a015910f0b030080c2134003801202c2071624100c4d40041100307002240e85038201c0300c480409501c92341403504400f440d4000b00d401d2207810b94540d404401c640d0144101050103002e040790818000d55424501b126501060885540b9100c0c981d1341a8041100030b2001c0d070400440313002d01406281400b0a001280010355079016952000f4855100016900108045c1e0350090740c21078802003015111005900c0180b046034403400350b40603c07074101582415958080e0f0500411661103940f103c0203075440451942e05108601001c2e2540030340300c00301d080980d07000c1001c0e500860007080380121056504c00c0181c0402580d600851681d04060010001700d4400d40803041240c20940e092681e10f5031900e066401080b549603001d60055120005e541403040c0d04044442d400815111440219100c00440c440c40c060000002c1000208200c203200103403080444445540c03192b942401d040c0d4982c0c1d00c001404504462a40250340f011080040e07508400038106106901030b03601c0003581180f15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 452122167 1250 452120917 452120987
    0x110403051c050d060603052202090a02031902030f1e0403080a05070509030109050c0a09090b0c09030c06030f07020c060703020d030b060c01091109010e01050a1403030708030a090201 80
    0x2940214100d071403041071041c00c0d0701480c21581c181c0290701c0c042200304e48406014005203002c0e5442e038078044c004103c0c1c2c0d0040ea000c40445000390f40040c88040f555486030035602c0a940f00800e6488092107101c00c40c040656203002035809450b00d81211a8145418905410400b51020a03e4400e5404905000210350400c0820703411046082001c1034a640b401c0c001d442d14810003940e146c166103000300701d0f801c1c490049039580d41e8000886807003003019a0782684400707607408c4840182c50341c3d1000000c02c400080a00003404c5060015090342c3d10308a941000034042e400885000c4000e6409004200c005541402440d20b0040d044030141c0c02d00b246602d000f0369440b204207072141456900c0034020860341d954415149030340198002400b5589052070032403400c171403407000903004440200021950b07203401203d15050760300c041d080c03842041c640441c04894241846402d034140c04108148800304007280c00951103a000c9040206210410340300041c00004a0310f48500c00568503a000d0107880e200b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 452123417 1250 452122167 452122183
    0x6050606071e0f170909090f030d02180406060c0b0c12060402090103111b061302150f130b040527070f020c0d060b030d0e01020a120c0b180111040305 66
    0x1902c0b0201d001442d00d01454003910954001c1c04008204c02200826003801d401890200b0058410054549039860501d903503180245501045803c1071044a4582e0321641c0035194802021651000300031400b40410112419908480000b41500c0c0c03070501030240d04840b4a82010700000445c1c0f0f4031103081203a001c1c070707038003d8203c910882e0001182d680e0307a84a0b0f045a0b00c0481c01c06070959440509103403520000c20103142d4228540900c40000e825450f1223000d00d0113040c0c0182000c1c0080e0120f8401744042d80c804020202d80d500c0610407200808100c00718440a004803105240d601c5052904220428081050b126103141740980700000991201881c1a0070142034140032800c49a5001c040e802e01c0355140e02d05800c07105606484080c401e4541180c5c000d40c81c1501130b40c04c05440100105d807250701070b1045501580c0301e04811800201101c0b194011820a4a45500607a02d03568803092804400e64203e49070f8060025520721205080c421000090900e01c0954a4649981e44142c0c840b085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 452124667 1250 452123417 452123453
    0x1060e1501090e15150c2b080609070809072c0c07020109031104020c16030b0f040302120a030b03030703080106030c110715050708040807030507090c05030f0604020913090605060607 80
    0x170000703c0001200c1e0007040d00c2c460061300080e6641e444004410241e42c00300e041e1004218080f00030708040f12401800e0382409aa8082d0212066640e440c1c0107403460400944041618400c0b43c40c0081c007905a10910800c00f0044100000440081c1c0c004004070600035110a071404400c002d120010b0b81c00003030703003411213510884130882010030100080c002c0c014145001154042c40c00410010f582c203107100e005036445070740034450310f8596400c01022181c0c1100c004000d0f1740140f05041681c9842c1c0c021708020001840c001c1554425040441e0441c3c00101040307000c51000fa00500c0113035014002c1d08084101c2d450441201280b4080c1d203540c0d071000c0c0c40303104007071801c4044040000d4403075001c481803142c02180d259641d965941e14582e80e45064401621304d40075048010a82c4034580c001d006866002e031381d81c3d508680710340702d1160201030050312140d80143d0130004001c103521018102e0781d2681c0351000010700d501503418450141c40008010318820328040042c0000155081d50342d0b190848 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 452125917 1250 452124667 452124679
    0xa03110a062a03090f1d0903070b040b060a12080d0605060f04061218050609010f0b010806040c0e040f0b0901090e120a12020409020a1b0b01051201060e1501090e15 72
    0xe00b40c107060b9522025500055428851100046a0141c1d114084022019290418451662445101a1240640c20000707204d01c54030f10116020070941e44010707420901c014000c2e040c0c290f8a408114400e280300100b10303042a000f10350640c03145024801c000c01000255005403509440310f4213440c583c0304601801e001e1203042c0500441c0100e80b58044075904503048a4000e03000018140182e40d02d9081310201615820400102441c1c50785000c0e001c002601070b1203440b101d80f15071080001034491079a080c01003004140b60382c8060756480c0280e45160080400c0000c118042c6400d1242030f11050300204132203400d00350760036000f0751b00050700c10b0003500600e1526192400c50a044446011881d0101e00e81d500204000c5a03100a43d4004c01c1040e6007a101d15203902d0345950340281c140c0368034a001e0041003241c0c0040120b070500c01101c0e421608000b0002414549500010b03090350401c0e0f504000190101127101101e50304584c0f90b20103854000c3d181150b6280001c914a40381d00036000882c050030f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 452127167 1250 452125917 452125997
    0x70c020915060924041403060a060b030c0703020a020916110304050a1a0f0a0801060f110703140f060906010f05120303070c060e01021c0f0b0306010e0c090a03110a06 73
    0x81004c2a00c0c0c8581504005540c2d590b9403281c130b2201e1030001610240c0712380a5a40841c81303022140c071925007280c4140c0c00c2e040c1140e840010704251a0000da07025403d60241c1101c2d00016034408940d140f05542116041c208130482c48030017000d4108070300702c040041d0700c1084203004030741c1d6030b440f103c0172150000da4441c42c00b14400340e03443c0e083c02040c240041c000c1000c1102e42c0c1d080d800c8a00d0b58140e952030356440346140c05110303080350001d00b801000c001d0340c3c11680c01800480d2814000d0324800846004035140383c0720740040c551034008116a0050ba03a00b1180040c000c00e148010f001c0000d08048886c03200c1c41c4003a03180c982d1a444051f0407441440014a814420481c01e504031094800905008540314088441c1a245c1d2900c809548400c484c6401c80b140d500c40c40034426050b24000140c0201507907801e045569100d103901929105092109004201c817580c0d40740c038207201541c4034010b640b44031076012003441000c1100d9000942802822480c00d000480700d540d051507210781c01c1504403945 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 452128417 1250 452127167 452127199
    0x1d010201060e0a1a0d050d02012901080411060705030d050f06030d18030c03030e040606020f0a02041a040c05070308151c0303150b13050a060906210203070c0209150609 74
    0x402541300e2094004090201480600c0b40100d0300a400440c42d03002800b0f403484080030001821000f01611a11041001d03024000f544616907a540c028400c0134801c001c40c151900040c5280c010101c21901544000703289030402401d409081c2e0000c01c40c10b0480003a052800029072a41a8500b18804104514002410924a04c00010000c5421003d002c00c815102e0074020036045d07048110600403410300c0400101c0c0c1c2d1000a002507004400000f40031400401d5003000042e00160941c045002103945104445666034410814140c0306034032420b42d14103151a029124800007403011802c1d0039429040354840d1a00001c0c1c0e030044585409043d140405807070140c005002c0400d1200071500001000715810522000400c7c45c66000b0700c003620081d58440c00c100b41004c5a014100004161800401080b405075002180e082403014801a01c41281d4154400f01c1c1c0040303600d03034000748400007008258145640b0142d0458001642c95141c415040041a41d51060201c00c1c0c3c001cae200f01901c0d0f214 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 452129667 1250 452128417 452128451
    0x30c04182705100518061302150903010e0111120703020f0315040915050106180305190f050f0c09062e090f080c040c0513060309060f0c1d010201060e0a 67
    0x3003d00c0b400d04000600b0244030200c003c5144070f1403210103205601c0401c0f0b14000340750038009402d0703000b000d00c0c50342480c19074600201c0d00440022600341d9291002c80b4922102070013102e41c80014006000d890314004a151545054054185020b045c41081041403c0341e9007400c40358000c481040c6d041e50008070b4804070303000346000c076405032451074400040100c0d041d840d000b02d8122080c1d43c2ea003107400e540740d1002140c4c91020b0310004099500030700800c10056541c030b005c44021800f556009203555200d484080c141040e100361940c031904444a0300a440c600310340c1090300202c068415070855a00358000c1030128100d80d503100150922a1074800865100390004405031942401c402000c03581c540d140d5030350300d40503120b4074400d5080022055016114105413481c0750b0100b02c512106520344042900140b0390450203507070365074031082c0428490015000390103103100d0541d1000b010b1407055407241d101040c01041c0c103046906020b4200800c02d1100da06640100b5170101c00100680440400e0803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 452130917 1250 452129667 452129683
    0x5010e0d02060d060f080c0d0f08131710021206011d0d061a0105090108070804060f1d010c03020412080c2103180601030209070c03021002030c04182705 67
    0x5445540000d2090b0f124030190400c400b202c0001c06021030b502c2c2c448070050740f100a0504c241b034102c0340c40d41d04c003008100d007400c0c1421064003500105e0314014070340c040f00728466100d803c62183c40011490045400c1c40c1044034a8040500034011420491a07001001c03100c07001030562410800501e079905038154080c1c0e41c400d451000286110040c4a40b80b62050250040d00a00021003140c00d1800700254021411103007c150169100420341c0e494071700513209444054000d445260ba1a80c8880b42c102d0140308102a205002c0c030300c00f02141e2980c01d41421358203201c48800805005000412141d6501424140b003e036014244076220402031061a24007520b840d0441142541a00f5220060801000840c0501082e8151100031201601c03419602e030000c1c403009420840d03280021b504148140e200c16005442481594a8882000304020603a0403d842504142c4070003e000c1000f40070000341015140307860441442107201150311030b40b0314200c1c102c58011500d40e0140d20b4042000034000e0301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 452132167 1250 452130917 452130919
    0x7030b040e030d090c09050603190609080a0905030d180512030c0102040605130f05011403150907020f071e0b0a02070b0a031e092004060815040b070807020705010e0d02 74
    0xc0d807a0840c11804801070040e022080c2c0740d43c1c1d1105c2c00421140b2644c040c5501c90000a001410300e89401c5524060b1041001030645410f07a070307403107802c00180c00783c2c0041040f8007055613192001401c1000b05070910b0980e070400c034284480e6501348850080d41540c00000c58030110b90314400d08d00c044000c0c50a41c45511000700300c40d44001400704845411001511900030611016031071261034121a50409440740036007400314601a02480541200c9002540d00a01c42d11014141042200200c2ca50407400c2d190580035800014072281c074000200640d100411000310489143c00034904280403e8140d030140c1918040c0c00142c5892590003000035a0061800074040c076954112828020014800001c03034a0748111659075043c114031880c01041c6030541c2201021403580c070134031300544011010f20302c9150015100c1324005007021051050101d0021070000720300c02440c051500c00d9170a44020040b9051140050600a01c01d500040800542c0c0d02820510520320884000481e030400d803410003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 452133417 1250 452132167 452132173
    0x5040e12070b150607050304050603060604090c02060106110102180909070807140f040606021510080f03030a0b090403091e05060a180504050c0d02031305010e280b07030b040e 77
    0x10000c01c591491518440c8100b400f0103d084101c1a0401101e84142907010f060703688180024411072420600a6070060001042c240c41d00e5500c0201006981101003000302507007081c00100b007641e410030080b5520400b070000861400c40181071000305690f0010445000e000300e40e0000d40304c51020400b441c05030032030b1001c84404030358070541400801726844100303028000800e1841c1c00c07070810b0300540c011340300d06030090b040c0805020746900081400400740d515001074000001a0618203012041c11451040090340da2840c00c20301d09010b46500c103402500484481c42040040303a800300e42e11040d1a0440866003000151031031310100c40915402c0a5401000040c100c0030040d0003a8508004081c80c0513a480e282c0d81d030340200700488204880d46c0044680400484200c1d11040e4011903202d803003c800442d444d501c0c0d40325103003180c0c90310076075507940d61050a410112107280d90b11003000d4180354400c0c3e03107410780c41e54a044940708080c01d1002490f44550203000c2607501e681100410030840c2040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 452134667 1250 452133417 452133427
    0x402070506041208070f0302030702100203070306060314040f12230409051f0515041a030613021602010302030a0b150316050c1c1b1b05120705040e12 66
    0x2644681c015038003281d20b0301a62041000c26801070f14810b118010743e8070740300e6403100c20140642c082d40c0000c011000318041c1c4000d205a0300c80910207940101030303607a0300040c0c60382480005070403949030322008003440070682d003013000207107881000031595030340304406055000240000b6502400c41805500c5402c421485c0b0460318000344d80500100c681408040c03041d41c4401100d4421182219256444011040c2c001e000c05d0034800e10751071001c07200b800d4561400e0350ba81a00049169050482150601c0000c140005441c4c101c40100440300e032030004502d01030b00c0c00c1c0b00d4441c90520300c000a05254001c4000342228131168844a81c8540141803840108140e43c105911507004440c03507000c003107140c0c00100d4800e204209444c1081c4560005140003100d10040c075030706159504040742041043d000782d000000760125004019403041c03080c0c424120203409851046800c40d0001c5014104102080c003010100003040c03001c0701c0041d10000782c00001410313401d041c010901401d19500c400040c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 452135917 1250 452134667 452134673
    0x40b0304080d0b121209061c020a021608030706090f060c0e0301060f030b06061315020a02031c1d0105040b120603011109030706050f070c090509070501051303080f09040207 76
    0x20081051801002c1c04002040d801801c0041c007a08210503540c055010f25452031031100944010300c440c0c04024403042c01d100a91b40921910015083c0002c0c030150041034030100341c0c0d010040d45c00076511140b040c0705501c1c00e003250703950390b800341c50405899151252020300c2400a0041c0840005420841c14000c032540a4405018201c2449440b4040c1d840d2090018140c1c583d4012002601e503c0300d0350030245d41340d034401c00c003490304580c00c0710411101062000840c000701e602610205150794024115481241c01098205120300c040c10411241280c800345010b54801c2e40040402d032420603102140c59104012a000d0140350000b1b00303e10303400030700d040712450f2030344082e4030511040703000340a0f4140c00d0001c075440340a95164075425510508046c050340340102d014104040394074a40b1401c0c507101e602c0750710a00c0d840344c3c0700400242e03640c030034842040d0052268001412003801c00724a0260310b80d545602080680c4001b902c28400464000d40b02011003048400c0303803400804c15512880241 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 452137167 1250 452135917 452135933
    0x9080c0402070b07181d34080405070f2d060503160c1527030507021e090f181b19050604080106060207080d0503070327051c02030903030a030908040b0304 68
    0x40c7d5140c0301c0d001e1f02150b00d8038500c3d207031014421150101180b0800030380501015144d4140c05041203902c0c0c000c0c1c52021810180200c4090000d0807040c2c10301c45065100190b070944411000d003860030b0f5101e106014031003130ba040412a90000402541101d00c01c8219104540905070000014070504400030100452a1641c0110f103800180340d10041d0400b00e10b25082c002601c040200a000c5034050280401601c0c000c041d0070340200001100700f881041050000b0b456100850ba00499900300c913052005c500d00c0b11810340c100909040003402c2404444003a0003405160346806031107010300c900a03055541e00105240d0040801a000c5911180c03602e010728041c00f0742d8010709006119515000a0381400003a00e8441d01c0011b807605071454980a00440240c02101180c90400c285000f0792601340c0c401480410156018101a0003081c21001a04084840000122045500034445140259008811540341e08000d0900107003440080c075003012180500da11019422002000300310512444d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 452138417 1250 452137167 452137171
    0x501122418020304020a0504090507080f061005100c080a030b060f0405030f0a03080a020d0e0a0c0302040c090b121003050d030222030f0201030f0f060609080c0402070b07181d 77
    0x200c4880301d4800070701d101c1040b400210350195002181c244100102d0415a00880c6110b0142050703134016a2128482c40c6001d00c2078074190301130744c00715041010482d840c1072480c001c4c0c003080700d446407610b10194000786844800301010f442a500014403442c01402030740032202080c800307400603407140045504000d40760401d00c2030501034090013070035951070700300440c4a01d0040d9040d01e40d841d184e00c4106c076840094001e5003600d00c1140d910001c600700c00c0000c0045290161051080c1e0b8995401c500c14842610366107007100040c451009410304c070050114040c0da0140c080c211000403165606510126100e52590000d0300c01c1c09a250b260591683c1f640050024039002400103c8040c058000304102c036055100240c100740700740b0781c1e80006600c00d03003010104c048625400302d83d910252078490f040b00e4042c1c1c0100007284c0d0120f010000104240000c10a14104950850502003583c07250009680c0040c01d08041002003a1800c0000d61104d2600e030280070040c040c0f411040c40035403510340002c4c0c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 452139667 1250 452138417 452138429
    0x1906053706021e0609031b150c071101050414131401060203030a0606050a050901030b1809070e0a09020a0e130813080c1504090902010311030f1e06090105011224 71
    0xc0f4080039001500020094058048a8021840c0c0b061400784500d585100e8130701c8143c41c0c0680758803400d402c1c154841490041c5031403c205030350781c511850010170009500d66000e06201d010302003000300ca000f850008100690070b840d54130780b5075484801080100024813062200110102c00840d02c254000301842c07058030940e00402030541c4a15065070940524600a00010010842803a00354881d400c15102e000007d030410b91000124102c0c00c0d03c400e4202e0340400d160b880601e081050a03202c1c10041e0700000c2c4480308007c2c00505801045001c5214001c0d140600c40301008502d007c81d802807484107040c0c014501c6d94460003845200702c803030b640c54458031080c2d12840466024902e018003402c02c01d100f8400030350b0702d4240307001c1c00070000d8184a401039040c15a03410010f141203031204021841000d14600c554400d1400d0344070b4030039641748029800448000b4408110701034039081001415a0300034208002000f5280f0000406850410903030014103041310443e82c18868942098401e5402e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 452140917 1250 452139667 452139703
    0x1090f0501180e161e3302010e0604052518020c0f06040f02090105060a021f02090406150206010608040b01030209220302010b0109080a0b06040f0e030a0206190605370602 75
    0x180c2c0d486002e0300411b0780110074540b48100d00d0442581448401c254050000c60300002c030300480c0354070306642000003c030343c15a03a0360848100d840c880d521700031010031074004000f13482107001e04050380c5100d0412500748000500ea030008813030030448420010800824129000c641307040c50249003801c4a0803603a00100c0c02201c000f000818285061402d494164100342e00a140f02c807040b19090114103c215450100c181e42081920300036100c5000d480d016205024211195a545040092a10700d0580c45a002c000d81175080c003001074140c80d2070504498044920740500e4903074511015072011314010182c0c3c125003250b01401015010b401c11410124262503500040c4d60391400980c4900c900007009200700c50700c400013030315894680d0283c44080c0621000007034044121f482c140c41c5a009070303013050250381f0074020060782400c5454148001c8ca0203110a0110b103280c4404600c0312200c5948100600f4480004000510b1012080d6003031410103941e4109125036844010352a40112450142c03910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 452142167 1250 452140917 452140919
    0x121812030e060106170c030408031302190303091e0807031704090204290c0a230102042303010c05030c1b120d0e010c0801060c0807050601090501090f0501180e161e 72
    0x341d00da40561f4403031074002c0ea527245236030b46410454120341c2c0b0011040341e000000b240301030381300701070000500065446500c4409505050036401115640319060501d40d80040c00000d0280200203d05042100d603c5840702d1120300c4007200400b0280195040030400d1427020a00041c4c0e4003002c40c1510001e02d40001d25045c10070140c0c4030400d103204400c031580d4150701040886000840d240d015030104c2c0c180c1d12400c148941c0c04100c07a401e90b8090342c000c400718030494211201d413036040c491134030288000320000c100310490298081d190b030000400009501102080806060445011003500000c01d00141c80002d503000341801000e8000b5181e4024040c58004141401700d1b0510403403c410010344c13a090702a030705c1d0000859180c40030305000c5a0f1594107201090015408100981c0a400d107040d001c5101d6040502c00d80c1240d95007050b00442a0801004210510003003d074044034000a8002044004203552100c0c0781c09248040d45203d840541000540301d400d541408503a1006040030018007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 452143417 1250 452142167 452142181
    0x90411040e12030c07080904020c03030103120f1d0d150c270b0a05122a190f14030c03070e0612061e0d12121812030e06010617 56
    0x20b0700714544800c2c2c9030901000810740310503040e400340c9141e602c03c0074200c2c03501d01c21a010500b40e8021000e030810380d0303201200601c20000c5c80324419000038080d1910880c000c80d08000140902c5900c500101c0b0400c80034000c0c0425102c1d55003408003103400c54401011a1011443c10f4001d10445801c2e070009404100d506961340702c0290f00c844100700b003001c7c9107440c60924540e540c1a50082401d001170190400290b69180340c00d543c0a84500007042c841d210701212580700203c1051440898031410748200401215126007001404803403000b440d242110489460058503e030b03854002d20300120300c001c401c02000361441e10045208040d259140317039200c554101400101c2c0a817111664100d44140c000410a0500c801c8040000d484514000d92008024001c04c0707142c00590015580e14000081130542c0b160000920314400c090f03410108101201e40d5100941d00c603550800400e040d05d6402401c503403a1090300140341700c10103101030f244e80f560340c0c89025000364960020342203944034280006400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 452144667 1250 452143417 452143423
    0x180403030c0201090f0b0a09020a0e010807050609010f03150f0906080d0e0d060f020d02030109051501050306010906050d02070c08060118051003023a1109070203120a0b090411040e 79
    0x14056101207045245400c5075151485600000c3c82c540c3d80592301c04c0c0400c0580d40e1002d50500401c64288110700765410065000c0c182140c0e81c109900030101004004070300c1e41c0c410100c82b04203000380f07000540700b03086c030420894000c03065100d4240e042801c0000b10b940c036900e510220440f01007204907a00984009001c1e1074280c2c414001c0c0d40e0001403854580d012802c0c03500b101c10262141c100051500000049080890300300780c10442c0e00664400402c100c00303d42e542601001c04003428404e0441c038108000030200314280c0600703800c001c00481e20b404222130940513540d86aa02c207802c60903a41d21020342507500c1c44248650208403203205200f0310145814424540150408031813200014155028007a25100c0e856907030350b06090068038403600110300c0f035800400101820b0702d44185205401d00d00421200d80c003100348205440428000c03040d0700003080300d5440c465151442250750703070303800b03860003e2441c802602d412a5241c1d0400c810000c8010a508062208440c00c00c46209103d6030255 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 452145917 1250 452144667 452144681
    0xd05090102011b0c0308091c0e03010b0f2b2102060a020705120a050d110d061e030605180d0806150a0e010302130504090f02100c030813020d02180403030c0201 70
    0xf08914044d03590100b8865100c0f1a03204001108491164190208902c8904607413100700700000c1094000c0400d5103000c0c050200101c0c0101c5107085250304400008a110410400320b10188203046807600d8005154071105045940207002508016218500414080c4100d00050014080c400c00075171044c05500c21b03140b61641240040185103e000214500c030341c00b100200d0117000c0c00b480141e0403c40f0760700540d4139091580302d41d19195000c0184c400e05884950b004a81d19000d801d483ea400e185080c60700c80c08a0350849400b15013a01c0d040146100040716541100e00e90003030903140758405030050102400780500381d903290241e800102c0c2c1c2650b07501407500e00c140025421206601035620070740251650081c1001c01c216583e907110005400c48100c3c2c1c10480c1e404031600d078510158030f0044110100301c0c1c0141080c624080c02690b00902207180201004464a0500026020f540300da031201c44060303502030202c050b440410792520102e440d04640440c000381c00e0480c0c0c0c3c2d01841c0706000d406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 452147167 1250 452145917 452145971
    0x105100b0a0207031e080c0c01021204180f020702180108240f1f1e090c0c150b12060f01060318030809010e061303080c040b032202030d0509010201 65
    0x142e003d056a9442802035045c11704460004003011852020518030b400408254040c00014018620306000190800c00e200740b001031252824031040088643d411403042c1c0000303407039a00080008e401d51101c4d000307000d8054041d410010300001008955080081c03a410380d4805422640c110401c602d0711a8030b006c616440301c015060700404100a040d1071248a500810700c428891381007129a10b00d08040c8125501032034800784100300503ca0912640000b4010300820002403100032210a070280c880700341820001c16248092140240c1c001090b444412207003002001d0f152610101c00364150b9804003581d000d4950b84c4c1c44800051028000e100781306001d0360480381c4403240c02d11a28140c1d068800140030050030354850300300b80440481403284c103101d01e00720240081185d28030b01700100603910003002400d490303c0030030090081442841c26268802d111080500e991441465840c60340c0d40406002501442a040703100c4071140c2182c043c0c00d0800d02a40200101d2209003910a92049940c00c08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 452148417 1250 452147167 452147173
    0xc0a0b0406030e0f0129030a1e1a010e040227070311190207080607021506060a0c0c0906210b0619030b0103030305010f08010c14030a06090203090105100b0a02 70
    0x8010440c040d400011010740f40f1802d9881d1001c121060f18203444980c0031586103400c00f442000340301e0b0f03503288103007110101c00e90082010b07560300e40c1c42d500c0e28100880302e80c80f50071940e240c50041141b0380584060301401d0a407900c0f941c3d40d540c5a110407004098904911400d82c3c1130740421000b54036001d0303003240c102c050321702a55521064001e4009101881051040300c1080241e001c807110001d6400c2501c1502d58004c0c81214a0400710a04140000d41200115049000c45402248118002e00e4100c101101c18658410302d42006640407802608014405200480b0010741a4017a600c40300c2100e0400341c001650343c03206040e0610700d10100200404400c003c80c04520141841d6058400b5500e01d102d4020069480c0e44449409245c240d104400094840c00140b1088004118007801041071900900104c1b8807680701611040c0444515025100080006000002141c100381c00409005208542c1c03800c10440480c00f070241221036000040c280700c000519035401d241200ca04d07020560107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 452149667 1250 452148417 452148419
    0xe01060507050a03080612030c0a03021c02250e0f01050f030a031d04020412110a062d051c060e070c0b01141f080601080108120a03020c0307050118050c0a0b04 70
    0x380c1741d546018150326000109404c0000b0782070b000700010700300380034010700a1540d00c01d00d00c1c00918181802d01c1c4001c44070f94035840e511040741c00241c03241071440c100034000d11000b080c1c58080d0f01031849902c541101d0003041c042c0820515003101c105c1c107982050706c0001c10a00910181640c1d440c0d80407000300000c0c01286103d1003614003241c0034242d00c400400251a05a640c85040e000400c0800165400780d0300d0210612280350044840e002010141041d610100403280d160003400c3d02c0d44510b016588030b038144c0d403603ca40b1410480c0d16207800740010300d060040103043c1c4401070109000d84c000c0810110003081c2c1e91030003501da0014456010066803250f0b82804200d03600f4401c080d4199130400c2200e04000450b420030001d200b000303159a91059007a02e000800100012410f0307201ea5010740118101c007021507525801c803090041c41c0d040250f9220004a2214691301c5003600c05011075103401c8511420000309080c10341c0c094003400884006000010070025414454422042c0200003080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 452150917 1250 452149667 452149673
    0xf07050609030705181e063f03040603240b180306180c04090b150d17040e090102090d0f030e1504090c03090c06110f011103010e01060507050a 63
    0x8001c00d984030015069803003082d40d51001c50414408103544807004a0a50308100c0c02c0318104043c40120901c6002c0f024081c109000400e080c1803240c2d100d40c0030710384045000c1d0160f0180340240d40c00b603110100340c18900d03070346100150b40742d4000b0700032000000d06028004020059050042089501d10b00c041200c0e507241c04e64801c10b43c1e1280d5203026601e10300d008052010340d014402248100714240c20307020f640340390310200d50800110300e1030188502e2922240c84045202e071807803d0b500c040c1e1050441d010f4522400040c8060f04880d034014142400343c80c1814100325a1070241048450b503048548850315548150307800e07070140b4504d45030040034101c02c43c000f080e000d1030380f11882802814021100c03c0200d0100303400805202c0380c1c0d0709403003001a0030414030030144200040d42c0040e29040041141ca95a011a6104a4822281000700c0640305600e4000c0c20711540740303000320b4440200316180f160540c0b20519002445229280080c01e0000100303940250b013100d142c203500601410000e11907507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 452152167 1250 452150917 452150929
    0x20c09010e0609040311010204060f030605010c050a061a0a03050a02010f1416080d02030a060311040603110f0105040e0702070501090518041401060504090303021e07051002030c070812060108090f0705 88
    0x6000741c08000001008501c600c06c00c3c40204054812659410340340a802c040150554046600003410000b880a070300d4040350300890804240c542c00300001c40c00c1380154040844480301550074540c400b01d0080c000041200020710140828400c1c1c82e0120b191641c00303800c0e65044842401c5a00c1c414041200c49101e1121001c010060b40c800c90009041c681d080c40300404a1304100d40c840603041c1e07034003428001e11044210b5800c0d803200c112010b00c180780c00c603681c110300401c0302ea85450040585403421351880e80075100341c2d00540740d5080c940c0391609e4000d2009540704001d12465001c12800b480100703e40c207050110545e038100703901c5682850327203813561030f030914450107031a03101155070320640400e0540d1071b40a1701078103e000b40d41c056200ca030b5104c503802203c241c811046040700c00070401c03500050400f184c200341c0404800c400503200d03650300342c44000d9445130540050481e5000a10300c4201140b00082d1406a036080c2c1c2e40b441543d86070018690369401c000340c181d149601200c4104000c0c0303014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 452153417 1250 452152167 452152171
    0x1050609130816110a0b03061318020910180216030e0102010b120f190201020706050f0409050a140f1512070e0403030501051c0b060114091e01020c09010e0609 70
    0x8001c8149444000c101c008805142070074219131010114050701403c1c43d280c00d0b1403003d820120401c07440c40c142071000503100d6048100091145488a1428007890403007020849aa500035225441e40d141c50b445501c0c1c0394210340200100c071303580104901c1301c6c00c400d482620b03c0a10401c8080210303106a0314107440c20500661803504540d00e900180045407030340c0d68545d606603402030003400700700201034641342400c000c1803242d174009075100032180241c2c1c2d0005484045a0190400c240c1d0341c0704846820315140704580000c0c02881c10312007031140c0341c0d40175807118804000700080c248403601c41e40000242c80c4810b43d01024080007211201003685401100800c2c20385a100c12944881d94900d00c0405911046030700780c3c04207540708010080c508220105144001c18949402110b00c0180d61f44a400741c00a0102410801c224010300340003c200d10803550540310003000c4903281d5120007041d01129011441e82e41c014060413201c050070b0304010310018140d2348490440700d40c1d40d8404083c40754172480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 452154667 1250 452153417 452153423
    0x809030d0f0c0306080c060307050717071b210b0c04030b0903090f010908060c030703110c0708010b01032003040503130311151c09030905031501170105060913 70
    0x420444910100e8061040401a280011010941030501d080141c201e5a066200503240d40202404582982e1000d007243e500030810b0400f16103d41840c10300035002c54203116081c1c55801c0c0000d1207000e1091101d0505c0d2820303403c248020805031030745101e1501e003004c044031560358010101442c0000c0c1d203510042d940185034100300d80c1030965a03120704034400740c1591110202d403c0003403528698240f0981600f400c00c0d003800d1149e001031910f410190380e410300426107400c0400200120f021148a500000740042c244480c4586030101303801426103400032031085805541c60480c40141c00d50082c01078250412900000171540b205001141009610041c000ca807580020000c2240ca40c107092140c1d00a580618171040c01c164122040c0401c449904000a1403040d081c84400c034400c85111201e002071404c42404143c0c0407032494142c1c2d02c18501e801140d03150041011054504040810050480e00390311031a003840c1d071701e80d040d0600300c8505659660b000030040c00080c6002031000d003450390041c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 452155917 1250 452154667 452154673
    0x14100f0f0e1308160b01030c0503011e0f06050a08030c0f06090d03020708041e0e060306220c0b0307050903060c0f09090709031a0402010210050621030d0c032007030806010809 77
    0x400b035050130420041d400c2c04407615004c0e00300600501a0040d0350102800099000704807404800e0003011030980c00c420049201600c506420142d0400347c7c100e20000e0402400c0c7c04211034a51160b40d80b40c4c3c100310b000203114070800001200c5005c000403200c1c0509102405000c507403004480460180d4459a0240d50200040100042c801790301000e20b40001d4201c46800200d9040c8031510303080c18805402d1601c00e0303000b2024410786c5040c8284041c03040f807181d00c1c88403080c0c44034548409441d089038044003c40c003021040180c2c07290007800810440f0011000c1c0e03010f03a82d40f031001171014007559195044004080c021240103080175100aa0020050304000d1105035030b940e41c060503503004407100b00d12603a150007440119601000b40b60f20045090405028524143e400b10780c4000c64401240711130200405000307500b5005008030388582010804c00d11404540d0040070300940720900b0032104a076144004504180c43c138000361048180c0c15501d0744c00c0c984404004480d00c1d0406041c080141c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 452157167 1250 452155917 452155927
    0x4050409030513060f0906020c01080105090411130f0605030a1502131203030b040b01052b150801050106020724030f0f05130b1006020c0409030314100f0f0e1308 71
    0x840700300116000380503a54445d0b0380060b100c0750082c0200d03000e5004a00313661100e607049040d60307048000213040d1481034a8400e80d554490400c5030385d00250a140c1900418101c2d440c007041c3c45103401003070854022640600240c0d0796201450740d540003409029040c02581100e01c49880c00d5038000b4060030080000c0505e204e0b854490101007110808811404280e46d07020001030786c1007a00540d101244242022070038154502e107041c01502d960103c40d4510309801810041c0d040030b507800700c006902d800340c0702e808442d00c5a007046e000300400c1c041c01000d846a00d00c00281240c60f003615662031103200600d5405c21550400c01e901a01040d0f40030854941c40f00c5107101180300e01c1c03003001d21540400807401418566030070611188070016140d88442d0001c103074144407140d00050f040d04003101c00d4800158a020508007200240440040c08152001302c10a100c1c040081403400030940d60010211040241c5d200740c01c40b5903450f05c1c4191810184000e000400b407082000b540c0e503600c1c0c001c2310414a40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 452158273 1106 452157167 452157187
    0x5030601050d090c171f0903090326070818120703020f13050c030a0f0203040c0b1608130f050301060605092716081b040504090305 58
    0x86500d82d003921080050901c440e4008001010709505c03048112503010b61501100c070900e18042c0258000200740e05d0446c810300d400c00364035848048010f1700c0c660714a601c11011488900c0903401c1507420070441c40c0024010b0400030300c65115250364138403141c540308012500f10039142c000c4000303801c881e400b18000101c0c4019a1f40441e820321020143c000000c5e0089070012803034080d182010140545220044091800350711042400d02c418841094190100d0004580182036007104407003c110820031a002042203401e00700c0d11150102254032540010351004141941c0000783d15004c0010701040c20891010300000c50080c032816180140041442c01800403942c862491270640b408410384468000b80980d20403940301ca60b41c40c2005245500c416652000f03400304131031301c0014400c3c05120301c280245110f0040640e042904100c1803100414411a0440c140b00c1c2c20001c010b40 = true := by decide +kernel

theorem cover : BRFrame.Cov 451978417 452158273 := by
  have h0 := BRFrame.cov_init 451978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 451978417 ≤ n) (h2 : n < 452158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
