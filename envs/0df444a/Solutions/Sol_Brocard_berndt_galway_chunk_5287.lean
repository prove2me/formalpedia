-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5287
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:22:06.607534+00:00
-- url     : https://prove2.me/submissions/df667ccc-d3ca-4a7c-8ba4-2009fa0fc408

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 950719424 ≤ n < 950899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 950720674 1250 950719424 950719463
    0x2030a080c03190c0203060108060601050409020309010609020a020d2a060c0c06151a090a1a0f120603100e0d0f140a17160804110d020301050f0a0c0525 67
    0x100394040130f940b00442c900a50042511b010410380c060030301a00001c2c280500c5990000407282a11004240507a50f51945002c05004101951000c1d14051011840c4100d0300d902046000c1e105040380d8814141c010055000e0580034154191010040541e1340d0010000b400d580008039800d4141c146204240d04580301c0d0015034904141da8603504003110418001005001811121040c03490280c070b0a0603400340100b1120507050280050468072101d1054045203400e0403903490760141480c00d510f49600c0340080c01d0559059401030701c40e00880d1a40001000e0510840300301412103402011030501c54003090b51068600c5041d00c0030400b1020b00142d140001000418480300e0030341c0e4100a81d65a040c40101d03030030024007a14419200c5605205800d030b80480420340140d0089000340000b446c203000110355615603c0029050350800d01000700c6040c116005c02d218140246003440410304950b4101d600740f0031860303495050315584440c4424002c0419880c506207204441c0d15203415080841c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 950721924 1250 950720674 950720707
    0x30c0907120e0303090c0f370611100e0a050102030412020c03030c070927030f032f0307090b16050c01030c12200c010906061202030a080c03 62
    0x119240840c1403114160700008003442403000b00c540761805503040d4140303942013580f00c8040480462260171310455a01ca10ba44031005000e441e65408100f240c01080e1500e03005036040b03501032480c20030b40561000206180114000d9090843c1880075200509045107400010306031505e5911040c0301e03407451000025424401180078078040c0400c00010b2583d014001d00d00344c20804618026002400405102c1e00c000600b0301c00e940040300d0104002c400112441c4204003103d50341ca4850b10656191030506410000d48540c0120ba55002d01c100503500c0c2e8001c2c4550001582040100c8000da01401403625200155400c9007903450089040c40d5140518070182d0000350b1071030011740d207000d980c404001c0100a44c00c01d0040a080034080340308078904c0030706055188020144010385454202000e9800c070612081070324a581c0c80c0075101e0001c05540380c02401030030750440b00c0c0c91900b8004100b80003882c50440d4081da008004000500c01541d804465820040c0003500d248070038400411038200d180da = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 950723174 1250 950721924 950721931
    0x120f0617150705090919020f18151303030c1505071116032f04020c0304061d030613081225090803030604020a050903070905061f0c03030902030c09 65
    0x801031103128004001c803034024201424040511000304400d00032074a420104030350020040404c214040640000b1001922403080300981004001803950b030b0000d065001007420710000c4c1c905202c804000c86984849100c0c1d40d605c80b07818449104108000382c132a852a2102d00e02c0b951080c0c03103d181c0c01c084031095034802d90340c81010603420b141d900319484080118100c4507640250458210380b541c1c9a25403140340a240700e8060615110340d05a141c080001c06550786d06000d84215030310320021290300e440750464060240000c441d100344104101700c003890030401c0324004010709240d0300c2e412800713945901400401c40340c60390148040c580350215400c99610504c14191861684c550304600c084070481c404034140d040c0584490140110351000040d6039001d42c1c140e80050f6200403452098403540280c176000e03549441122000b04100d40d490b00020b00a41044d140000654a001c01c800d1900d074940200100040c801407605001c6803098004006050029007070f00d0b800c0d90500d01140c031020048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 950724424 1250 950723174 950723219
    0x16051c052401050306091603031d030a06060503010608161e0f0803070b06060304050735071d0903090f0a0e13120e030705060a09080f0c0108010f06120f06 68
    0x7200401c90750078107201d41613126003102c0240102c60065040391502440d180005000c02c02980446002c42040e030b442c080760030318010201c0c1d02907219403a00d00050701440c010f03103000b9424684006841d450003d50040071a000150500300103061501560200e0281000141c05400782ea1740003500745c0c858a0b00724042c107400800346070740c1e00c00d60038480320000c005840203004030390400400003c50350214807002074030041d540ea03500b06100601d000c1c1440020000307601a07601c590442540d00755001884030210307440101d2006007070134031203114000108200c1c1c10510a070070030000f59800380b42802000d5016900100a405001e840b95820454030758211900207e691030040b400040c48010035940d000031a45103000100c503680040400c0d250a80b52040901910300400c580c491320740245050b0010380a00d100321a59100094005a69159009031090111303684000121380f0404c1c680d15002512503e8403140040f60307000301404001c01084100c102070a940e10742c0880d0201007840740c05184081c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 950725674 1250 950724424 950724493
    0x16020d111209311a06180111070801090b0c0304150b060409020c0a0b060303030c0a12090f2405060a1707051021050f040212010e070b0c16051c05 64
    0x180c0d8200c1211404509400184001d442104e041e0740c50310f0844004102d240c00710404c0c03000303440051f1107441141d4034900080c01580400f05050300705600900300903000e0360000c1c1d495216019407a001d4031040d10040d044030440200c260035064103400c03100071100003910301c2d0710300b41d50b0f000c00408903001520841c5030340e0401c016010a000c9151841c03904210110050340c60342c10114040901031041014500c04d21880b90381010801c0101d0f8030180e0b5841d08900c01030b0303aa100d039140102e0b1006540c5e0007061a1045030041604110003449428490720010340184101030a042c00103e4007914044507581a02c108403000c1a143c03140c07100541b5003c02500c44004010005c0605c2d00a40e40810207001800d142ca000c1000c0d1807442e2009a4103c1d4042e030324007001e1124010054017510500f80c2e0200c140c400c1c902c001880300151001403100480e20410707103850041003255a84030300030f10f1240590000f410b00202404482d020722400d04507100c1c6084030306040903850001c645102c07103d00c040c1c1e820344 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 950726924 1250 950725674 950725759
    0x110405010f09151706030c1309061e090b07031401050906060c07060806100804080f21010305060411030f101a0306011205070f0b1e070b16020d111209 66
    0x803c101c131580145d8110094040703041d642010401a05490824004031500ca06107242881a9a4042c0c2802c9108240a44554900031290009001d1407002114425503040c00034104612034030801001c1840842003408691034074003001000007000c7d0a496100600b000150002c21080015400610352522107202902d042800c01070502c4102c2d807448180588841000001500b0804440c000c462907110a40c07140d005242c00e420100350b40c82c43c0f403c1409003d0010040c4100025858812846920055034280e000c906041d180c80003000700140310341c450b1995845440054000b405e6031220080f807010840801c8000910309a801c2e88014040035940541030103000782400ba01002e0089441c09001242c90010074183d1441030b032041d04080d1031510101824040c1503021110699002528200c6900340b059103800e04000d0b9227041400b40c8600c00245a860b4080c5403200503c2c10f558026104400030342007040520b03848a44881e17031014203a13601c44006000107001851500c040e0b01c020030f0b03152 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 950728174 1250 950726924 950726957
    0xf1f030506010e060408030d0207171c05010b0405011b022706031b15090406090f0f141618030f050d18050604210204050a020a12110405010f0915 64
    0x3d8681c20078000c40c0100018000e0301e02c00405c86607080401d2100607074491440c00c19100008103d40c0f2515607010005018042200171105511042408c0d041048a42d03a03072951004648124454980883c02d0300003010828100070001118460010700501400c0440542c85462500c03000f116400c5121901e00340078075420308000032030000c8107181400142d5546500003420000100c0100d40c40c401c000119050503403502d030840b030020300d50b00d1818000c00c1c41c90b269503006006112425070ba4140f9000006c0c0780c070030f0138418990240c800c0030f0803038005c41c41c5403208031003420100c02e0241c03564040450010000e0010741418101d01d0041c0041c00380790981030401480c91995800030a0340803010721041c01749503500340848007150000703d100e045400508035034900005005902035403092400040100c1d201d05600244104003081c0d40b02175a00100b6550a030444141c42000c6008400c05c9c0030034013485d4021070601107480c1c498108400c4095450440360000d0210b0792040c000144e02240a490340c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 950729424 1250 950728174 950728187
    0x60f0c0230060105031c03060b0f04061107050a09090212030c010524011e020f0f010b01030b180c0a05040902030c131d222003190f020f1f03050601 65
    0x29070110080c2205500d00b100181c1d86014036200c200044502400c40c070391441c000d0740981c0c0141907550142d07891704002c041e248a03d401610886c00850745208601c440d0304c0c1d002c201c66003903a100070201030325141810301050040031094800c0b42c009000030036448005000300302514003940100000306451034103a80280c0704e10014a4141341014807507080300816070304400c0a10340c0c114a00d440b290642900082280750074407013115007029008040340c40000400c1908000098002a2014013503203003042f040c400c060b00801a0f00d191810308a004c506c01c0448003000b0860b40796a0b103041c5050944035103001e02241d106a5800340241030004807016981100003042d001000740c0c182045822004102c03040c0c0b070307590042084040c40400082501480101800d07050b00b9078201803c423420110544079038084107801420b4038400d21504003250301c0000390003841030503160301481d01032228100b039092207040100c040030a03038018411180c818009003c00c0100341c0c900300951703000c06c46040c80c41c0090403d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 950730674 1250 950729424 950729509
    0x80702150c0c101209030f0810210f02030729181002070f0b03011d01031208042303090901080303090c150403060504140111070c060f0c02 61
    0x40314040c40410000d59010844219421041c0c4500320302d0404000120b8120201850300e40060b49461030072418164460703400c019400303a81d120302800f911100490341c1d90300802e1003940786911f5541100e034a04c5124442c0480320078803c9402540c1c250103607001908100407034108258400d242c506c2e00044101111202c401c10201e01d20091801101e082100300d04450a030201e405000c0d01e51050507014400c11141d402011910a120603458071640080d01942c820b00c11410004011030325480c9102c1d030580128126548a44080c0c4071a0380c0180a4802500c0208241d668600302c00da0b202c4503103a2505091400101400510348d03a40801d400c0088880c410780160385140d00070310404c000c40e400000d8005c80b00c1030032981c240c10030588010321201c40c4101c0d08010003107401c1070144810410000001e0008900b148001e101c10407a22030b103124903000d1287d02528800e41c3e03101c100304260194840601c401c40c546015000890260007094400f190700001101e44950080040000c1000441d00f000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 950731924 1250 950730674 950730709
    0x6020a260307030e0f0601171b01020a02100e100e0111070f050409020f150406260f090a0f110102240604110c0a06090b06030d09090f02070609080702 66
    0x180d0504810052010700004003104181a640c00c1040302c440d00800c0441001082c103070440b0410340c5c440600310400c0d91000c0c07642d03206100350b064150302c44a02c00d4010081045c10f074010013207a0303080c1c0c007003000703882c4108104010301ca07034981400c000b6102c050003140300c1e0990391994034415007a007000501b01e40601d843c21b003407500300c510140079604c3c040010308104c078003c94010404100c58000600c021038140200360f072003038500d1160301c81c103141e120113171040381c1d066203030440a03450004920010081e00c0d01e000c0000c403451400a4079070040420074642218081003110898500d82c3e903000c00220315144250b480840002c065910340d0780c10010122003201c0100341843c0c1d1a02c5110002c600c44014000c1841303651a01842030a141c40786080e80c0ca800d04100484034a0025424071000a01c807181d0181c44451081000810343e003400540e40040240c1030342c1e1028098038004003c4020146401d070007000607001c00050010403818014080d83c640281d1906035610303805d10421076244068181c0c0e00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 950733174 1250 950731924 950731973
    0x1303110c0907050c010e16030606080f0606090a11030405151005030c040c020102071a0106080109050c1605120703030515011b030e010507021011010f02090a031b080706020a 76
    0x6210380c0700c40340703455007120181c00c000783c84411811502d0702500c0d06500146641c49090003000e19140c100114100300d0b0301450f810009103032200c2c1d4581d01c1d404554458a803d034480c001040c80e0381019001c0940c807004001c400590b058000560b0101d41e071065a09548562041640080003000c0072907050f005000006654900303490702c40802e4507005510b10042c801c3c1e550741101071045000390111489194495010325902148110100640000f8011345001800c440b001003810100c0344190f5008011500045040000d500c824240901c18031034222820700400b00030300d1f40c4902c0b20006c1c004e418829100800c039440c02510304900b241140030050f041120511600c40c0008021540c3c80081da0140f4000641c41514401070b50640324680d4000c1d00003c4031101090495407180d41c5000520742c1000134441e00c0440c5142c0000c0e4081ca00c04c482d8000d015080810020342c9c081500c49040c9e49107a03010410b10398038000581841140e07070224008d600203e0354401080921a400302212000241c501c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 950734424 1250 950733174 950733193
    0x121a0412030b1c06020d1b021b010504051f120c0c02030606180f0c16030509040f06211509060506120607021b040b040504031d150d050c04030b130311 66
    0xc03c18100c0800000c0c100c2da80c0014881c1403029203400810241d581d1070700c00d010584011100960300c0540814043c86172800d00301c15180b540c032645c00c80e001c0f80c80040c02844a404040000c901502501d07002d8004c0c01040b5191b44001140d500861031640165100c41514103080e005043c00c0c0034004107494815100350050702d8951940d005680c1d00300b0a0140c8083c0c1507903407004882c100340300e104448410841003400140400d5440001004003d400f42d8003408501c1c20b175110a400e960003402040030119000310715941c61302d244a100f244050003083c0c07102034180030422100c1207946246090382e1040d10707101000300302c1c10712000c1e0f5104d4200440c0107040500e0b00301c100944440360540e07a02c42e0f00c4a0600d00d509075540c2c80d0030031800c2c40c0000b0020861428107290142c180100c003c252040c07020040e001341003e02d42070410355001c196484ca007614000426150800500000300b800501c51000d11001c408207d419980e24800e418520f4190001c10146c20050030f0b0408091b0880d14591013281d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 950735674 1250 950734424 950734459
    0x6010f151704030f141201180c0c060b01020703020603040b060114071a04030509040e060a0b060a0e040c0c050f0d02151311030102040b13140102010501030b01121a0412030b 76
    0x3000d51140e00352034222520b042c4550700300d175a20019440006100400704004031132080381c0103941c0c100c1d020691004030148091032000c1c107036404842ca03100030514010a40010501540140303080346814410b6030300da10b88075800128079402c299801d0f521000e0490404c2890358210007264100c00001e92000d0602069544076102d100032102454011040740012508050041c420740b000203030028400d02c46030090510244c3d648104a500b04041070501110504c141001d6046641d45549aa0b61501488250080c800074043d0f0103a0881004200c81c10324001c141e060014401003d500409000314402c0840000e1911200b9507480d070017070000b0001d02143e0020282c00b0249a0b5014068810802030701c40040d00a021f26449000707100b100064003010100b0a104403c1541c210700c0c0044000d003d0b2000480c00c86d90b09000081c41c03211608014002c2035240e11701740384083d109070307642542d02c1c4500f078995140d01c8064508035020b80881c09a80e0182d6010301828044031002d881d10310980207810340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 950736924 1250 950735674 950735717
    0x305010f0b13120305070c050a080d20030f03070201060b0306060d0903020c03100b091014060d0905100207060b030c1f12051e090c0d061a0306010f15 66
    0x1050750801002600c01d4207520910400c2d0000d0a02c0b2002c44100c503a43d0030060000c0e4059001158a0120403201046914000d640390781601d5180f4001d0004440c18002a00c11400c07040c4003140e06c42d1500280b2480c01c4080004000e8103510116564a82c18401d030080d00b90341154020340700c00901801000103a0b16100243c1d020000c00780000b05203e1485d080c141e0800c1652940715815005a0f0190307041e11109402004100805840300b003115580e046082d0320207031450180080109182a600100d860721401810105008181c000b900c094a91365151610324501198030006801040c07450900c1550310645000f6501a070180c40503000c5180044c1500c00b000003400400c2c0300c403c4149200780c0c030503500a150a20310450801c0785050942c036941e20300b54800c40c1c0d480c0080c12100086c01007003001c00c01245005024040b45681d2041ea41c03042c0280c8000071800039003907130320b44c0c00010350394003006030b54024909100742d000c5007030601459901700155030b40c00c07105115408001c17000300100d041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 950738174 1250 950736924 950736929
    0x5030706110d140706090f02040e071403120a0809030f030403020c0906040c08040323040305010204170d0c1104110a271409180a120201051602030306240703030e07060305010f 77
    0xb01d0006e010080c6142c010b540c0c450007100650001c0c54521440405000001c450054822010102e447d0552800400d907075a501407401400008081c01002081800b9502a0b0307080b090580681e0b08082600e841c00ca080c0c1c204880c15801130740220040c000609000e0360650304203800b547c0621001c04040c102419156015000034200300c112400300785681c55013080007658100c1203c080d5075a50b03132410864040c0d00a4023030141d0360310344000c001d10307114400110304802c1102600c0c0c041107403241e41ca81d4400068101c40700c40d0059104e5075660105004032004020a00e0f00343c449100540031440954004d06140d0038003500d6083c0300354140100d904800740300103145c170101e0700c000f550340e030b00d11646070811410110040c45108103040d140410108103aa100e8041c482ea008100a45d540f2000c2c204412180408002580080011501c241001c40745a01c2506074640c5040a42a11003100c0c1c800781e0000717a0a40000355100d54400d002c41c4144000340c02030613103207001d1000b0750608000320250040761 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 950739424 1250 950738174 950738183
    0x615110d0f0e031912090503060a0b0102160303182918031c1b030909020c010b12160b090a1809151e060e060d050705030706110d1407 59
    0x7403000001d0780d4812880340c4034459014080c0c0310701380724082e05080080140b0101320303a9a1030803a640480b1900c40c022050448000800420490311180c550030003d100d114a00c0d411405440c04c0140142c01400c04400154070980d0b0b144050b142d11701c1d142c00c03908103a400425603078981c0da4686800e216188054490328460031032259954080b100c00042c0c0c14120140180c040c0600380040e01c0c4800740250400103402207446d58041e41c080a208031118412944004010401800b0140300c020120360141018070308507000040c0600fa40400a034000301d41414114071030344880341d20121040f007103100380b000300200450a0706000e01540026075640081c0208030710194041c1000c003024240750030001c02d01d9040300030350760b1800281086030040c01c18004280e07040020b200f0030b803490380594860101141c0700c01076070610f6901c40c40d00704020340341d13440f0007500c180c07040724004102d5a9062005000074042911100700000d5003110003418990301424040920015450307244103011485c04880307620385d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 950740674 1250 950739424 950739437
    0x9060105010f02070812090a1203090b0d0b0a09020d0f0b0f0d0f0c060c03031a13110f16031e05040315020c0f100b040c17040305120a0615110d 63
    0x10450807840c000066005c0c0409201c1c2c0358140314010280390043c01c0c10517055644542483d01d50070500d15031200c0c04401000501c2180d82040000c00c55005405803618041001c1556400000000d24041882d000403507016400500091900810310030700c15030900b514020b0018074452400252320b914417100342d40c007d44103001408104508020a41d100d2984031000b08440d40c0c07103440050105007850012004646409614088002107095049851400a0107003c40c0c40201c81d0503400f034140032240c850301c1d0301d003806501103500c44240030b4200700e140c03200140e01d101020300300100005c980d4000e0070010b04050032400c01c200d40c450101d400b80c90304100010581c20b03e00c00074000034031031490300348010b01484141328510200032442c1aa82e806080050108420444c02c2208030780345e003c1200c01041c140c1d41100b0420b00c030a85e04a52150003414a01d060540c558200755510104941801049a50786000c1c0102c110202652444409514100340f455580165465848629402c1142032000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 950741924 1250 950740674 950740697
    0x1805180402060d090f0b0105030d0504030503091e040f090627110a050a0303020c01030e16090b0418030c050f0d140d1b0c060b2407110d0b0f0a050906010501 69
    0x20b801c21340c03a0f5540f00200340b00c51105400d222a40c80c900380541e0b4480e00a008000c02c1c920306c110140d8040e44d0300304019601c2c1038075060820150302070a032031041c0a03d00c000e10070b2800350ba641c4030340b10030418414804180740b4410703e0042d00316a5500c3c030740400820300140c3c0d02070f403245842503110b0903079110400071002404400001c01c4c070325150b40000d0b884040381d50040304256010481c00108402a01d0900070701c107000c250141c484140c0341d04402c03400404107013040300c078185400000090f54003a100040820703484440c1e0740903005e002c1c01500885c4008400350100442000280c00c0b001300c28000d01007041d00c0c4200140050b04100c0300c6054468040b44050070382501754801c40c410035030010340e40400322560001a00c690344041050b40d0503031030b00c28200c1e03950070006000740b48840300c0700906c6140300070303c180005107400012003030310305c0400340c00f510b40a03071075805003100f40f2800b42c3c000102a00c0d02c4002401e003c00004c255542e01030404060200000340010002d054450908000c41e4064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 950743174 1250 950741924 950741947
    0x20f04060f050d051503010b030c1014071203020403030908010c0804060b03011407020c1008063102042310120515060d05040203060705071a13050d180518040206 71
    0x85000202c912071814050201400204005070303402d07a030540080c40070a8848e000c054649448401c040c1e0800603030321100390002c4c0b007480703503400c0d051001e02402d0030039000d40c0701e805040d04100000404a98001030a20074143c0151180700280952802448602034900c0c0040c00076402600040510380c9030351860805a40c02c6d041641c0d80711031360a01c51454a0100e40003135a620b403c0c40c800d402211001851800301d48128035240c46040f002d8007d64115400101103c90902c01e011800e40f80101e4030340c0300310540d40303a0000b08010302c006002c1c50300072038840b1000070300940c40319107003481050880811010036400040e4126152007a1500181e070fa91421102c204c4001082c08003544141c00003049000d44809510980c010750003a0115000c9540b4030209503003a00c0ba201000d020804c80c050452a05021040020740c482281c00016010380d400341c2d18940341200401d100800b003401d4402060710030790780b03002c2c030070040c001243e0401c007a019010384c520080401070000f030300078000040d0900600303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 950744424 1250 950743174 950743177
    0x602150c07120f030f1a101b1515060206240319050c030105190218090106020d0e013b0603040804061202120105120c0301111309020f04060f05 63
    0x4640200103002c41c02a41000105400d09a100c40c1c070101e807400c0211951038440d4440c040d114030716140d500407000503550030000c079000200b95001c02c00c6800000201e0240c030383c4400c07440081c4206c0d8412503e001c60400581507940003070b07000040c0180e0702c03800c00109900181c515000040382c040fa5101c042410351010501651544544c0c1605c240300c4201302824210803100d4209015105403413480c0180c2c000c040c02e9038003c0d214013100f001103103180c5100c1e449550080c40d40b42140240041122141030100301003c400741d01c91409a04600c61000f441c0b5004400c0b682a66801d18041e641c00b03152510541c0d40300001641030803040407581013a041040c10b4004500c0c8400c0007480c160b1a4a80761400311015801400303220006031340e039002015446164001ea803030380d06034403c401c0916800c00f400d1051008481d03440004a124864004900d0348081c42491a61031441d86250703a07540e0b84100d1880e110721154030545140307104000341145224440309070b409a030600c2c6071002d070f0484580c0381165039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 950745674 1250 950744424 950744437
    0x1101030f0204080c121c0809010e100903180303050a14251a040c0e090102072f0f090a02030601020f0f011b170a0c02030706060f1d010602150c 63
    0x356200007008184160300044104070303100c044804808010568481e0b5440e0400b00c583d00c1614520300a861611a000c0c107140c1e80c1c030181080001a49240f44c4000a1503c0013200c2c0b80800b45a4800e04075090540c0700408808280d03002034001c0c3c041d481c56130010110302c5941c0146080145203d81c4c0e10880e03030711200700c0c2c0c0841d50070000411014540c0404100c01d00b45104100c9060b40c001400c0d401200b40c00e180c2c1d40c07049030010413442100386000703888000300500a0120007207550030096040060742e0f0503004942c3e007502c45031110a40040354055201c40d801070320b0040c403420703c00e04121400da58113040725600c585100b00150b100d80303c410041c1e2500c54104490b007414000c02c00709101104055000c41000340340038404d120303070070700e110401e840001000ba48120120942c2d0009180c020fa1900704042c0b182c080d00c1120b103884105e84075541111301d103400c0070903010f200d24010480301d01400c0c8682500501c1800c540a5035240c944040d43c0d82070300007500c180d00c0c15200002014080d00c0d2056406 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 950746924 1250 950745674 950745701
    0x503030a140f040518330d1505100306050105010903050a0f0f0512120a0c02031204050c0a08010501050f0102060c16020a03060c171006020c0f06040906120b0c0a0c110103 75
    0x3484e0171102c0441280c88001c0720401d5840d01c0d600c507014000945c010007080e001440c42d2401e400c25942500348038072403000140a0b41c180d00c2070075040c1c2c20050310303204592180145006408000f821403802500341c807410b9110b1410070410b00c00074004038401007110b134130195010b016241101014a08504400c4a041015229004440d10919012080801008a00c100301e1a04030540e9545004d40219680007a0792401039105101900712040007141c041c3d00207014500320f50700b040c806400148040b804d80c00c2245665116001004503050005140a041909001800e85ca1404503110002c50140103100f0b055550f0702030b000c1d03003175458ac2e150390b00195070442014040460480e10142c0f0000c20080828000e01c0120005003003603010082c40d0040d21040c0d4041c16560716000101306552450030700c501e17846541000000340e65402442444001c03c511240b0401510b12401e0003841108001e100740c1c442c01082100c2400107501030162000b03194001c03903d146441c1010300407001061080d01184 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 950748174 1250 950746924 950746939
    0x304050a06230610050f13090e030a02070e040b2410030c110c0a260102190207091104050d03031820030f12030403051606050a060503030a140f0405 65
    0x162072441d040400000001c82d4084101240c40348000c0c80a410940c8208100245003801940d40910000000b00031101c048a40c4c484c03120303150344200c0c00300e49401c1024412039000203081c00d00309405111800040c0b02100e4005500c0c6070a4440000b1004010200260502c20f4042074807039504c80003001c840b40324007070242c45d9464001e900180081440a180d840452020034448035610307000104001c0c5044c010b00314003001441d0a40b200c0b0f01c10048854440031070318104010884842c24409003a403080000910361000c400e42001900300350b003903040500b503a828401c450079200140c0c0126021190191a0317050900c0399420124024100100d00030035a801c140e406130305202c0d0313004505440300c000c0c41d040c030392800400e001c255450100c1c5410101035080361280c1c60012040c0f5000c3c50740103010307082841c6400481c0103c1c0c458070700d0300501182c46c680da0341c0a0007401201c0f0b10854002c1c3c8010b0f0300844c0f03891012000900200c030b130303640c9001100b10001408004800a241074a00410000d80a00e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 950749424 1250 950748174 950748191
    0x5151303080c190b25021005090f03030c3103122a02120d0909050411031204080607090e06150d0e2b080c0d150816091a04020304050a06 60
    0x402202c82c0070341d005e0443c11803448448000c2c00c4058940420000309400a05080c00803814120107090002c0c00c00712030b40030f1b6407908002c081d4244010341c410321903422000e603184131582d201c06a0803520340200c000c3c0d2040040d1060035074204c000761030a0307030f4002003222500c0d18401030444020751814208081c051460307201c01541419a140400d03d50f101300c90640e0a6240c20f14040d079076100c03034951040002e080b00341c10040c09800d513001f541c010f4080c0380042000a030840c00b28ac40d0249842c6101000000020104581e2205001403030b0030415a00d0700c152500e160521180b40400d020303202c80d02c40c801c600c140d459000322403c22034203032514080c000d002c2610107142032500c880c00c200340115440ea1010010828650414030101c6520264980c40f100e5251020301220540146401201a40e0b40703070419088802814080ba00514040c0000c2a02c000f45848031340c03c0103481d0384003030312403414400c6480c0070189010480038826400e580c010f890b03030340724280140340008624024144030301d0452403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 950750674 1250 950749424 950749433
    0x10f02070f110118030611120717060603040b040605090c10050c060a090203070312210c12060803030a0207060b0a094b090c0e0105151303080c19 64
    0x164030101d40100040d24407074080318010356880122020070031131007000f03a00920000700d850b4071078100307640301440c224103042c50715009940c501400da4120002c28440f0300c0889441e489181400c0d803203030094600a0860400382c0e25807450141c050310007031407135840d0310006e10121420050f021240e0f80041000c6100ca2404030003478216400724040c1c107018060340e00001c441c03008600401c41d025034064000d00c501c0d0301c0d50f140c03a443c001c00c200510003040050800d180c000c1c00c05100c03c0401104180c000910181000c0000c0c040c80c0ca1420300c162202e00b0000c0030020035030080240d0341c0c002c00b0303080003580c3c44902d0700d40741004103100c9001c55401140c1000c0464049003551015440f41084607044026200e0342c149100c032107807080401250040648001c1c0c500001d000125440f0906000000c40c04041d1540c4032040090301c0c0d008203030301622000042010b498140c0404a01421070094146408180c031070301c0d1003a500c81d00010348070820000e038000007d807080080c1c810038600d41d0f46e01c82003001540342 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 950751924 1250 950750674 950750693
    0x20301170105010f060f17010315050a180b180a0b010f060c0b06012f0c04051501080f130c09020c150c0a030e0106080d050306180c0d020c010f0207 65
    0x140010404180c5a148080300148549416110f408541c2d40c1c1c1c8510740101100c170f04600c03407000f178100200d1407801c503200b4800c2074415020390700c1002220407a201245d904812504000c0100c0300181c248540d144054911084503212950080e80300c2d20207a803040c000f061a03c919001505640c1300e01d0300510140a006210715050310310324621855140e40d96041202c3c9840d6203000a09200da00304049a0700d58055076850088414107201d10400043c0b010651200d0490b40c41c41303154a410003050040301c0c0c5850300c40ea560184066514140042035a0300081081100a185c4a001d050410203e2442078a80803003140180d84401c040410340d40b181d20400182d040603d20280910500740004004002088843c0c8110311000040381040c03203403c011809840e441c4600f10495694503c007098800e01841400d080b01c040c2c1c1c03a100d55904000c024068851148401200500410820f0152101c0740f6401c0321501d00310a4405a1101948101c49005102000c480c00c2c04038400144402042a80c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 950753174 1250 950751924 950751929
    0x30305090606030d0917010b0a030302030a0e010813020409060b060a0c05060604020301060f080a270c080f15182b1106070c080d11041503060b0f0a02150406020301 72
    0x209441c159107800c8249540e4011198503240030821016051013124150f01c40c103800300300401d0001c9000031810f00421207a40c4150010740c01a080000c0c1c890f138151700f1100641001c134080ca0280603503d0003044ca0404064180030081c45280c540c80d07042d00f88000c0f03402c41c074038542005080a03580c150f09080078020581d090002c072070602a0070002245071400d17100f6241250000c3d20743c114100175440e0100d800000042800300980d99445265144000b000c0801d03000070984147e04228031440d0601b88000601030b442020140c0c40018010501e00c00801d06001c0d441c444160f0702002d4449034001da900300020782548503940701e110301d000b1900d111b400908015610500094440c0004044200c441d0030301c0700401c501c42c1d031144011814103841031450103c0c0601070391440303080020350707003060050342d00711000c5450303503030021600780220480b11401c1d000300501800c080010301d1a14103c424203001b505061080800041110f800b9a4002c0c00741d07185603000c1084480f4545010300d4885c00941007030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 950754424 1250 950753174 950753191
    0x906040b0f09030a0c0302031210050f030115062015070e010e1e151201051206010e0c0904021903150503070b072907020705150304210e0607030305 65
    0x810104041c00c80304120103010700c0c02c40b8042c502d4200450826504800c01c03500460840c1300030084100601c0380080c2c07860140e4520020000f4907444e003030401c440810015aa01d00c2645420a8426031080c07020300807081343c0490804401c000c13041c0c02c60380407031104040c20009500400302d0741e9550491840385c042c885c00b0b42d9126a0b03071082200c8011034954401d09151900302154492005420b00c04205d50722040030014848600b0740340d040440034907030b0001d0312070f8104200c80c03078010b21140c81d117003002e84907401303495000b4070715903240021044941101800200320090001002d400c140c54030303011504420030000d041d0181d403000b50b80080c010100000c0c3c0d04814060700300b0228503071801142503c111072514101c581000c9030f076200d0508620a080301d22010b21441c805004079101c1d25580b46210340071940140210f40e20380302c1802407000c1ca000588417108410403c00001805084001080c9070a4200045804001c003800b6200c0e440018601980504041072440805a064000340d00c240e035136 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 950755674 1250 950754424 950754443
    0x515070c120807030e060c030c010b09090d02061308040e040b0a15060e060c2b1d0a120201030e011a03071203020a0b04110607031d120d0c03050d05090604 68
    0x694034011800320801d40d005001d80e030300700041d00c0420300c1918281c0b140d00c0c0007003005240002c0141200c0c5990310400118a1594482c4c245140d1860042003407648886400b01401d41d071411124001d486910003881a0a080d0041d6061130500411f2030507100604034403417080045082505210107280021141c2c03144032820021607101d40500e80701070340126481911240ac0402000080040e00c2d0031041e0303006102c0c031078003016580c00394500c400ba010301845428980f0044101050082408070b00c580c1c03c1d0b404031040c1d1100c0082e0f844202c125802c031800300125220040c441e20048010b4501001d05007070719806c028858000601100c1510300e203243c1281101d034525a00c1c001d030000c0ca1844040a070140c0c0018a400020458510a9035070280c45800c400344a100c441000032925044071030141c0000301d40e0a001152010b090201d68200b910403910005e01a141203100d5641c1d1421010250800040300c611104241c02181a200b000c02121010710151408001d51561340204076400e8414100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 950756924 1250 950755674 950755679
    0x50d0806120f06160c0b070c0b070302090114090102150c0405012c04020705100204060201050a0e2b03060b04090e1203012306040806070201060611070e1902040515070c 74
    0x20004000b10301c103030000c020b0005941c0341510411102d0703048030540140f1a5103490040000c403001d07240307031085040751662001340f4840e040503410000010302e11010f0610400095460b603800005103d60701d9000d450466444c2d07001c10040742030044a881c40645801c070f030030601c020301200704007600c10307680280e840d0740d030120f007002041c86260100e4800c0484900103500401050400d81c00400d00c050280013254a8210b00c981c00030101e0b440784d402000180d5451040c0015607015000d2195034526400042c070041d0035400c2c80200c90005618018805080110124242070081c0c01180060100300081e54407640d68500540240070500c6011040380140202071403030280080699060b642c02c04074007a4840701011030701b0782e01490801d10b55400203042c0000aa800010000207100b03010550000c43c03103d151140180c07208160751501401c5411140c0b00340b14100d404e04840b07500680d0080c00c04402e000155041c0024030a82e044070742c00848036240000c0c20b9404000400c0d20354031511078404200d0307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 950758174 1250 950756924 950756959
    0x5010503010b071707022e0c1707050f03040f0e01240309021306080a02090901020a0507030e030304260c1203070204331508060a03020105030a0f380102061f03050d0806 74
    0x1002360300081000700840c2184640c4071407000031f030040501c41c07011104c50030300100256103103030025488a84440b01c140340078040b801c8030003c40f6006000d00041101300d01c10136290700700307010300040c0c8030020113549075044425035803150702100e80000102000c100c025200c0c0382030b584401704070b4000d1340181e0350741003c5040c40005200b140d03002001507880505020040e5411602080d000d004680e06120503c404203001d405480080780c00780908007140d0340c0360340382c4510310300b400401090365102e40c10720300039002c0c9118084102c580865044070001045030b40300c00042910414223002c2d00317101c0381d00f514510a00c1c0b21503040100b66021985c100d942c0c03108100d4108c5000108035200d9030800d521100400c0154010b801940d04040406404148d4030150004201100d400c07407881420203190302900e007100800d02d045290083c806000b00b0000040140002c1d585000c06440040020805030b10040080c23481c0c4180000b075030f840415114402003202c40240819820f88009124000158040080300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 950759424 1250 950758174 950758187
    0xc02070303030e0606090105060c03042403180302071a040e2e03020d0f08090411040f0b03041a0414010c020d0f020c01210b030106120c05010503010b071707022e 71
    0xc17840105014500d80c2800709000e0f84e0303000345a500c00540f000784400b140301051180f046c0301502c00f00d0f15141040c030050324002c040d1011010480ca1a00065200c400030aa01184a40582e0720001240d42004035840c030350441c87c443d550010707c0900c0c41c0e90600c824a04c14200c48800b09041614500816594124041900b00c1ca48030095100d10340c407000303100080c1044940b114030740c09501c403c2c3c00e0588001c041810390b045007820601c0c0c0c6100107030600c400211561072034050500d00f81c1e840e04624013555a508042c100301c85400ea072405901c0000c1c1000400102e41d07000744200c000904c10201940d40203035942c2d001000b4800801c14100c042645948005880030411805940d08544440019004211207031140064200c8540f5060034012a4a0034000d2070020308008074840700c0681c240c10304002e6801c0c1500b003981040800c00c0108140e404c018103449245d600005040001c625040941c4400d204400c80290400010400d0200d0942d8444840b810201c444070500c00c5001100c4048410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 950760674 1250 950759424 950759431
    0xe09190b210c0f09010b0a0f0c050d0207030308090d02060c160f03050c0607030c020a0f0c0f120c0f03031202030606090a030503070201021209010903140c0301021b0706020312061c02040c02070303030e06 89
    0x6401d0180307c0c0c005624410b0703035080320100050034840804040d0b0748840f8181040341c0641000340c0d0042c41c0400815030712038609980a100d04010388144d6030000c5c0025154500900840511140480c0401c101d40b2006010040c1c183d111017041484c803180d14000e006038200d003c01140d1402241e00040d9411300902490a884e551a40a4580880d440d44c1c0d180500310b00070416110004106008a2070300030a04e0464050304601c1c04410108160f89010b45014030305e80c0200d00c001d403c4210801c0041d80141d007a50b044805120003584a03500d1101203070300c90240d00840756002c0b6003000e001003803140201c010003a642c000c2c2d003130f210100301d9044002d070780e4802d4480f110b00040304114108040f620001e2440b08038080341c0151180107101d040000c0c2641c101141d112072064919004260300c0d541000400008c04640c005581441c000c84079814040070300410f507500031809000250051380b68428050707112680140308001800750349400a540316000c2c0070490100e464009030348501003001403c00e10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 950761924 1250 950760674 950760689
    0x10908070b04060b0a060e271303020f030304290403120e07180b100207050102030315040b04060905090d090b0d1e0207030e010e09190b210c0f0901 65
    0x340c40250380d9080024100108152801c6540b02000321580d503031508898002c110340e039610b00c08000c81c041044807521420751046600080481030b198003403501c04000d54404000b60f070302107030783c0030f90b04069007000950b08a0100e04d020010402041044407148805002000e1442e0700403046007100b07490f000e000c190740190220301d0a04100f03403000380135000f12015100d03d006583c90749965903084c1c0104071410f50852045034590034041d080c0c0c104800346030200300c940d1000305509031615001075142e12010f03000494181103203401a0b11074036503800128031720314064403c020300b660f200010b20003000c05480000c054042d88604404061207809000d05951130104843d15006c035200002c00182103600c26001c040c4040c2000715042c3e80a4400360070414001c1d00c2c2c8030701754074503e40010034800000792010311a092003003d002a5004040c2520162260007200060480080002402c2034445021080408208111005850501041c21801c400781a5055403428103070108202d0300820034026640c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 950763174 1250 950761924 950761927
    0x31b01022a07050406030b06120d1202091c0b0117010218040b0a121406060904110f030309030708160f050d060c090302060c010b12011a1909060e04050c0102010908 72
    0x38030500c1e0407040e588a0320311141114542556030700810f09442c11079009446071150402009860304089040c1419518003102030f21240084400180802c001d40d154003403003d40c00b003000e28040d1100c4400140f00c2e5184030050004605030b02d0019000b15003400f410580560922040c070000388140260348090802890382c1044005441c1848000d00c2c0ca44003160740000d1400c800503400700512240340740240a10440900c5c00010300d8021725102c00906501e025400e0036081202007822100408014902103954800d8017848100103032440c0184684964903000b5040c00164140c4000348a07690000101c071210f01807a80c0e2008d6100c0c1c02101e2054075000303425420001c000074a5940b21204000b19410b110111603184e0300030a0903034100da22004190703991400300310301c145400300c4680c00030450f00000348030170b403060340389a245a50319034a03a40c020518561001d11001d40f540060018001c0c140c0708000e05647c548010203241d40036101078445004159040e01503510600418850940101c8544d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 950764424 1250 950763174 950763217
    0x917070902030c04270c1b0b07210c02150f070f0504090c0806041a030316080903010905071706040314030a0e0604121202090f09040f060905031b0102 66
    0x360081d501c000c1c00201d40200030400400c1648150340d91481ea0075240c0180440b150604020300c0c00c951103420420b007404803500c0b180c417020511100c801c136155440701c00604540c03100c541c2552241c45801c1c14001444607203580c42d20014250f03018000d000d8055080f1040b111082c134041034510320658003024000102030000306014010b50704101c2c084200d1a00c640340950b100580c04c21214039161040001d0603010a1010924103070141c2d90021800d039461224080109001a540303120f6030101900201020b150f503824480d01da03058070324242014000740f054802c43d20340a40c80b00c40030700070755042039007520740401203241c0042c05600c01c6502d52903001c1c880701e4003403000249400c0209080c50341911100c0302c104d05131050000f503004612828000a8410310400c2c081c1c101100c66840d0780c2d00d6841407201c85015522007440321514281078071034a00035181c0d0704060601346403c00f406400d0b1810f100c00c9500b00f01001004201c1440702000c07541502c111250701d42e0903840f0703071100b2840078000c1c482030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 950765674 1250 950764424 950764439
    0x50405120a090b07051609020313020f01120501080a060c050307050406180b12071d0607230f0c040b0609090403210e06091207030917210a091707 64
    0x240210241c07820203503400b907541d0900d5a0198000481101c060700100c07222502e4200c1c0c811080c028000420040d400d510342030704107038481004c2d07403806889109181060545640605003000c0c1801c034080043c0040e40c1c443c0e00b40d035628000904102ea14514210301c02508910907400d0300c0c06100540c0e0b440303140600c0c15000b1030301e001c0030b500c1c41654031520380c100280e01e4072a00010800701030301000c031092074a0110000f400d190a50f0100c40104034040c03900504642c0e0301801c03074031011b5002d05d6540c8a40c01003940080750610f050440d0031280300c1d2081e08503440070700040c07690174038400f241c061010340c0e00b07403082c0a918019000a51b42020001d008170340002d00880c0009180181c440058119248494640040c0c0b915420103c2c0720b0b4118005106d940c07481405103e100c1540c00c5d130102d16120030355800500b1800300e07120b10a1a00b00c00c0d00314240444083c01201400040006124200310094110040a07482101218086014000000f0342441d4003a031000759a03a074200134041c0f035480c2209 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 950766924 1250 950765674 950765677
    0x1501030327050d03020f0c15040603111e07060c03060b041202040b0405101a070308010e071106010b041d040b0a0906062c150310090614150a0905040512 67
    0x10300340a0301d241010041165200c07000383c140d501e4004c0e4000d000c9480c803114550700340b003000c0040303500601d0701e1158524000715510884048070414580000c00c03c24070580600c1c540208500f0004161159040c0350b0141104405400000c1c02600100b0101d10003103000d030115103080c481d8810f2000300340001c0041000b13070f0031403409041c0080c20120396042810b00050889d201240d06512201300400140440600c0d14004c0214510801c0e6043c5860500d07100a0a100d50508c5240700b8000c08500081141d846041c425841108a004988483d44c6174402294150014025005d42c0d041c1420b046555041e01c001d980c0c0141c2d00a40c8030303d00c2c1d407268150350014200d064425611796449000000b05c0f5070020500150803104035120750000026514001a0400040d00110164034543c0307814440359008540e10300d000c8603040c40014210170386c0c903001c4060324460706107407503112003042008441608080890300d4000111520151640c543c05603504540090b40c0180280d8000540b80300f0a400310030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 950768174 1250 950766924 950766977
    0x120201080603150a0204080705010c08071e05010203090c01141611040e07080601060311030f0c0304060608010507090513020c030702120c1c03080601090303120518010f02090315010303 81
    0x102030f900e03d20f101110950f40448159440200194001010415140144803001c040d0209181c49144816180c440503894080d003400500b00f43c44188900d540503040c480c8020a05620000a41d141d03e821841c0c2a104c4110340d0b6070502041d400c501e40303800600c40f00100d8581c400a0301668880c128991180400000801c0d4400e81050703330307a012550720b25010040301e001450310a004050035810030000506560844040e015052428000d21400790300c48020a0303401080558100d8a2f5912800c15201078038650344010359035460101407106041e0301150000c1078543c01d03240900d603ca40d0304d000038100d100301200140ca43c0c2040c442200103241a522081c0701c0c1d00c04100f20ba10b19004440080c60f1150b2004207582d0312038003203642d142055041008103034020000d08181c003002e455030301c0c00381c02008151450307403100e50340344000340420410f101c0d038007a1000304400070013124800f04619002540140c101c144a4402c0c801900300012000f0310f00c80c140c0b907141e6107001810701d41d0f40400c45c1360800708 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 950769424 1250 950768174 950768179
    0xf0a0b0d1a1207080d1418040b0a090c02060619091806050906150402041505030403030603060c050d06090203010b0a05070f052407030501030302032205121f05011202010806 76
    0x14030781c4040c940e24104034004034414200541040c2d0314004c550780c80d12662102250030b210380034103030040414091081c0d81131240c2e0a41c2403000c09180310006001070640e00c42d5180d103d8100003002c00c000400703900010f03440d0603503000ca4a1584864040112041c401c5d0f00112080314804010300000100345c0081c4451001e1010300e041c00541541c8400907030b042100c80230480d030f1000742080070041d040e4036110301012007662304600e4541801c07805007480005040b55410301000002107001c01d0310a038007080080da000b9500b0401d00d801c07101f0081c0141c3c00b446204503003904000000c0340100c07052007228125011018081d207840b0b41a201030343c0540084200740d035100c00c40483c801c0410300500c1103441910030030707a14070203001400c07030542c0d1200d00282030002090320b017034010b2000980000480b00f0340b8903800425000103106890800f000060741d000650040241d20700103004186c0042d40703000b40c0980054505105003044030040c01c5410074490107003090101e01c24100554024450a504990701 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 950770674 1250 950769424 950769461
    0x9050609090f07141f020f10140708060616080301051002060907120c03050609030406110c0306010302060306240304020909190201050a14180a060f050f0d0617010504020f0a0b0d 78
    0xa02811401c810144180e22026820000150000300412301c01c01014041e0401c08101b2001d060310f100c0c0f05488010084c00601001c8000304000da40c0e0002900d05080c6003034030a50b040304491828901c1e6030000c0c40b450740211807090b100941d80d800825841e22904030180280f40c17852a00b402420182244442651500b40030300f00400450014000284190316080042d90744500d0180010400f40c00c0c801c0c01c0751250450548a441e56401240b1241100d80465a4030385940b1442c000442030902030001c0c561000389107842c1103450403020081d512941c001c07918407065554040c0f4550b190003030780d421203850300d002115580056009002800c40c00340e2516000c0b0640f0314644200505a002c1c2903c03803401110714521050318034010391040e001e0031480c609881c40c0035a142c80038119028080d20b2070300910020a5004140840d0f900074402050101d104a8a01045c01c45050082c10180c9083e4090460080c41156608090048000300d801031a0000d1404c100200c101317004151000c00200328600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 950771924 1250 950770674 950770699
    0x412170c0d0215010b030c0306040b2106060f0f2b0609030c0c060e01020307110d0803010f08070b120a02070f150f0612033609050609090f0714 63
    0x108106100d56030560020b020310f0795104100054100141e104110042d0100f041140451404080d0398101c4030550700441c03510118400110410440c41c02c842c450300c08400e010f0f07083c2e60001030150080b101a600c046050101c0e6051140c08444103540c141c01c03088a20403440b07a91080307885810a1041d05440ca800c1643c19591b907400c0e80d074030440a4000a42c441d250b0300520000c0d9100034000c10141c00e21000c00c41104001035242d0003150005001095481c00c1401035854050711204541c0e4000040e40da250384034041813a054410f8011464280b003103000110f41840c1c00c03401c90340b210600ca4410030303096403a28611006540000401c50309564003c94200005041e0f041d101d0044910490100e901301c0b040c01460100da11a51049514841d60206640401e8000c5000710348101c100c454020006018480e06400c00c6441c02542040d80710101d000500203a1030384040d000d58811100c0698540303401350f005503208124007800d110381e0002c000c10002003125126410820700058000f145500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 950773174 1250 950771924 950771947
    0xc010c170403030302070506100f0515130e2d040206030405010e011d010c080c03040624030804050406050303030601201015090e0607170c040803270402041217 70
    0x20010740c400c42c0401d4010a104003007141c14001550b00800c11310900750300900c1e10307040d10ad040906100b01400352a1181d242c0c02c170004003a046810419500c2d0401120b43da403402202c0c0e002e8001c480944545113002c2c05180800c42e0791056a01d070f40400b05203440380f91a15000c00005601c003a0007150190340c1c0c0d94040640840a00503400001030480812a181e00390100403801c0da50100f10302c0c81005810750801c806400e01c41c0a49801580060700080c00d4104509442c1106007102d407003d0b0642e4a500000040040100090040d070320266000e1001d507544000f807642e01c1c001581e0003800b084a02c4900c1e8800d105040807240d4501c4040202c4170000c907215561021200315a901411481442c4018071441540d402808c00c4004080014001460700c0d4000134801e02e4a4a150024003100c00c012a2840700c442040c1c401405074001a241e03544440d003030480158488030609903171f403800882a18014a820310035038041380c24050300003075500c82950f100c29030a01100054809104180f05544d01704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 950774424 1250 950773174 950773177
    0x11404150302360307051f02030909130219150e031002040603051005030d1e0c211205130b061302030103150501080c1f201e070501020c010c17 63
    0x624004079162841080d492101840c0043c501c12580079500040e4200010380b141c0d048490310011194a0381e40400c11408102d046204120490341d205000d442842381e0300b89031801c4070355000c0c400c40d4815101c45001701d03050b4403201188100320800f40c11340d44000300700d802030b440091008001810b903a103ea08003030b028001c03608144c01c1000040d0343c400400615107000d880301005064114000e007500c0f1140075000b0301541c540e5803908a07481e040007034101054000d083c02c1403c0c0c0d910102c20221080082e002404410010070f80100050385011050950102441040d02800c20341c0c0d29200b100c505511031050251014048541100380c00000700107800301d0340b002e94081c602c60302c1d9403106003050042a8050f0740040c0c01403850303030704880c0c10000c181d643c6105c000d1401400c807000800c0402034800035519440513001c25124a481c440046039558000325010601c1550020360121844400d409243c0e54919401818003590240e080b04805601840201c0030552186d00183c08045c8500c001c01020b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 950775674 1250 950774424 950774467
    0x7020307081c090e13150603060f0c1d0105220b070f200a090905010906110c0708060f04081b15011409040c032a170c011404150302 58
    0x21401440003a0b042243d10001600080c40f03401341c1c0840d5400c009416440440081000400d145443c241142c5e92821b039030050401981c001c50304104e0300c01a0400000945221140440001c0c1e4071a184105182204062185040180d603180e04001501c1c0d410045a800f04420304440f040ca501e001624420380740050009501c41d1071481120782070352600d41e80c0902c0c40510b5091043e8282403400682c0c940307100c280700f01c50700d80703c000c2000191820b00f94014141920041e240500380340c1c807044030114a13402001d004241004030385090703070394082254555105807080c031080500000400c02080f2040c010304550800078201c0e410b00403141400500d07065010500d00910800100100f24114102401c7d03443c0803005d4441c1006454680e403400c5991405000090003940c441103283c0184400308030410400c0ca007803495088a50712040032604840713960110b08070302d04c569607a603205541308071000124610030404007400c0504120000d0a901542d041c0a801c165090004005150900311100303403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 950776924 1250 950775674 950775703
    0xa0e040c050409241a0a0f030902041d0c01050c1c09080a031205130f1203150311030d020c0d0b0601050f0315120c010504061d0301020408030c060f0412050702030708 73
    0x10510100c0071541078100710794400840b0403040c81c40d00c4d55061801041b80c2e02c0d040d240c0780076080c904a840003a8010240c58801a4200745040501d901034410001650f03d5201020215401035100d9001180c60780700d621003407a5181c005000c0181500d8651020384072002c81c0c0d00740010700949403150381c0c3c41e00213035000c00d0700003442c000095501c201d03891152903000000d0b150f04856041140d2150118900c840000800501003521030b139440c10310a5201c0036000b0740e8550000c000c5580d80c10002e01160003c3c64151280c0a40614122030700e00000e040503402c030020f0414041d100d4180c4840481d4900100410f040c05020802c2e42158030b0908025845407a0000295801402101c24010a0414040c400e00180e0202d200305c1c820fa1b0304101942c2c03c950b8170b07262104441d91181e9114015042022000c0d4066001080100c0d0114002c03016080800340318080301e1035682c50b55640d000040007030b86e02a0040305461000f14000d407082e8014030b0780c14006411225015034078020311b840c00840000804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 950778174 1250 950776924 950776961
    0x303151a0d0614150703030b0307090e010506090f06061842041e0306021219060b0405060a17040c18020c1e210301090e030a0e040c050409 61
    0x4100c490b1007814040c2c82c024100c0001040c864003c00c26000e4412025800c41a02084036020980b298208100d036040150546a00b030359038480e80300282c010b00900c00702550070100040d049040c40f0101c2489480303c1910181c290302c80c0c5c403d1290650002c1071441d0120601d0001c8034007174591090b0f1020340c8481585095000030070300309030a41d504900207000011482d03881401050b909240c181c6098480d00039210302030148072002c56040d002c0d0f42d8070003059180049113072442d81110314025407140300107901c1c4000040c502800107084415600510503045030074402480507050140150804032000e0401c0508844021464201c1e003104440489014103030a800b80190780c40c07202a040d1110303800405506200d6094031054403076440d050108100702c11071501d5000c24000f042a84a0004401c020103d0f410012200d00e60300d900c2400381a44050611041110708030001089544200d1560340f94801c111802c0c00304009070521a0803401080014400031403035400600c52804060319254119 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 950779424 1250 950778174 950778187
    0x101e060e010e010603020702030606011d030601030602030a0b010906020d050703050702040e0a050c060a0806120a02120c0a1410120f020c010603020906034207180b03070c0303151a 79
    0x82c60003401c140c200504060040c8041e900603140041c449400a10900345030200b003142500b04090499645c01a0740d04d031190000010500119070b008500500302580180644500e003070040d20110f043d4030036900164000c1502c00d0b07070035114001401000d4424030304245800060b0b000a000c0e522040042016134019242100800008111125049030107a8005003002201722002e004004000c000d04e000e42e00800552980039410300c6503e2086500401c034003014110030b01855034580a2105050041070760b03440c08214240018000310b20a840100448441403000308106c80c0b411503403001b13944980d2926500d03030304440e05001130314180d0305078000016810320314010410950f1000e00158002e801c003220768484420256a01d4000300d200660700c00044000030140300240c00240200d00d4060140400e020310395034040410303243d900a0303042da204007948402201c6ca8a00c003d80d20705020580d59140134000074080d400c4101c0c80308440e40741d007040d155550a020b1076040700e404500041840000d82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 950780674 1250 950779424 950779439
    0x3020f060106030b181008120403140a020904081804110c0c0607050d08090f10050105130c320711010801090605030a110f150c0f010e101e060e01 64
    0x3150040c02c0500e01030100034919004210b840944150181041001d1400140c10601d0307040d522001b003201c401100c040500b14030f02c2d400150014041103594a140d0b2140c54030a2000144004107250000d0020300540c075550366265465100c121401445c0c1c80303d10311f41c00a03a696102e030f5031582c40a504480d58403160049003900303202d4003541180c492803060203054040350340020011646000c9041060325511140c51147c80e240300311118600341e106060005641d0089500100d040718401e0f00d02030030100c400480101a43c280070444400280c0445d81c0180b6a120355054a0301c07031104400905815a01100100703c070b9000d820305a8606000394140101ca50340003140900614038108104a880e081000003a00c442c207500c4050000c0880404900311a40d618503036a030f024000402e101c418003050f80380301215800c40c4050840074060707000700c0403280b00107001d00e101d4072030281c024140c00510443c44000405941c07a401034419004e080e2440c4041d441d1280c20054400703032499880d80e6250042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 950781924 1250 950780674 950780683
    0x160c0602061603181119120b0711210405060408010209120a031d060c0d08070201230615040b0a1805011b030309082109010f060605030c030910020703020f 68
    0x5280304151070302244180041c80d07050b030000d46075808883c0b9014842c19200140c0c0c04010700c041103000d56440b040005915032840c04100910b4800c0c1c840103003555610500b2b840f04c0108035414021780e0817940303402c40032401540f0048900d40ca114540d505158076440499460781080e0400d42581e90300041c071f4841460300d80030482460b001030004000c801c1c22554000c101500195803000c0301c65040d10515000d48c0c9810540b40098008404c6442a00014000411884060300e40101552920f00301e181060b02c04550000c41080210b46c85c00c941e1607000c244890b40c16121000602d03d0020700010625140010041200f4640d40e42c8007507010300112202d11340b145d03040e400503060048110120341000040000c4040250b050300340015404180e0030a02018880d0400b0101f40c50340c918a0403a01492440d0114082c148400c001c100856001d00c0e1102110518011400491028800184440c040030000c40c0d1201c00142900c41c2182c6c405a5002660040d0744101e0140e080302c101c43e80710701d40811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 950783174 1250 950781924 950781961
    0x36141501050a15050d020c0a0f0f0b240904060207020d051c031506050c1005070c1a0c091203070f030c120e0907050705010e0601060507120806031002160c060206 71
    0x72105401998452016005101c5c42c10711801c03040d0045600351080009120440341d036034008031002420036091420004551207280216400d180000114955911114481c000310403091211008072180c002040010b40000b801100c141703400300581c000507240d07042034840840c8200e00606400c041e101d04035821802d50010071003094039103a030354042c4016040140e0115041402c01e580d881c1400380c8514200784152018003a070604020038031080581c41421f00c405a40101c6080601004c110344a54869000781d800d0541240d05114a000360314040d014407101c650406c040f01d14107000ca5031801080e1040000640229007a0140c03c414000e0a0089030f05500c0306141140101108000041c00b500740034006100f0804007041800420009600042008040342c2c2298855a5180c8004100d5813040804076042d05e507c804020242d401a0390090203100001c002c1d10290940380e80101c02504102000782c2061400820003002c00d02c86400302001d4002523000e00342c50700d042c3e800300b424a805c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 950784424 1250 950783174 950783189
    0x160b07031403240f0409030809071e0e060d06060b040e0a0b010f05300402040617030904021804020703080603190201090b0315090702010c0336141501050a 68
    0xc10410407800e01082a100202a0007800484500c0166004c180c290100c07490140c1c01502c2c21010605042d08601954410f041007421900150f448000003803d10109151004135910b405009010401000454031750051010780780105180f2a1348a50b001c1d1052944250045031002a0500081c200d0070180b580c080d1084c101401400b104400003480104294a49070401001051540c0d250701c0076424991003140700205071940a084d448001c1072540180c508074841c078a00103002582460700c0b08001610720822000e1f500f00408901800040d41c864080c80c0701d140d254240408040d940c074806081c1e028001d9588410740e01c2c140e01810320b0300025000c111303901410b02440c0c60061b0317441035040e0141c80381114815103070b480d00c000520f854260142520380c010b03458400c200340d060f81540b2021394001107541c240006a08504003070101009030400d00401502440414400341a40d500c3c0f00340c0c1e134030034841c10358a04a804166401c02c00e08400410034404850010011450702035076020140559 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 950785674 1250 950784424 950784427
    0x90204030302240415020c0d030b0a05090709090c0e0901090504111207180e07030302031201060f09090c180605041406040b0702011b1e0b36160b070314 67
    0x742c0340302ca00483c5004100908a51a141554140c898280c069940a9004200702c070050880d001024000c0c2265800c128050012070a000a07030f4035040d103001d4011951500c8016541e403d0114920150a00043e08002d00480454926407130706d41ca5a114020300c4404070020b07090415141c851441520809458890b91140341c20114944010402d8001c9540080612240e085041e44140240c50f02c00c84031030f01c9002d040c4000040c140c001c40188021118078280801c50780e203414003510340120358612140000d060503424021800264411b5021620364188001c054080c3d483d5107041c01da07140c1002c1c0006401043c10000030340801141001170008640460601d8102744001a50b400b40c440041e04014084072804040e101d000c400100c0b181c1c010502050806201c0d43e1840030746d40f101421500c0300484400034481c1030001a2209807a0320740349200c650325140b110303880d44610035001d152845007d0740205019581014107410000c14101510f0786d1928000c1c03c000e41422410010407511890 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 950786924 1250 950785674 950785723
    0xf09100902010504050d0204061802040312031a0918011d0c010507020f0103110d0f09140d0c1401060b130e0618010909080d020d050603010606170f150a090204030302 73
    0x7003080130f80d4260350f020b1341c0460300c1c43c4e60340c0002005004140e12240034412a00302c40705004440d074004000740ca02403c0310740380914118100718102d506e2140071700d4178201e0900c4030001510f0004907407030700101d1044039141c0e202e207000400c81c210b03844c89101d00c09500882d0b26100d07a0140074007141180c50000d0800d6400c00c0f00c0758010448411301c5c500701d0b90405641e045c90703004400395001610031303000148000700081c60000e01c0c200010803003680c040d00e80269280000e6010302000440119858a07030340c0e004c0c2114169603804e4070107107054800c26a6035490f0740010402124500c00740260640c081001c0b2589440d00041101c0b0303031720103401c0ca8000c0707120f900344450f06500380308110f0448100d031200064240c52820103030388a008001c00c540d0ba00d400016034840b2410142c00050144c44201e000304456075071442c0c02e403403e80040441c0032480250100094200c00c440d0b0301c1c241d00140800d111072201017081c0c00a18120b04903008451981d038003240c1441071543c1000640741125102030122501c4c0c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 950788174 1250 950786924 950786927
    0x12030509131409070f0e0c04030b0a02040509332b0b0a020f0703050915070318050f0f1e09010314010c05030402010c14010609050901020d05090309010e270f0910090201 74
    0x9005d401601e0031100d140c0017041c507a500190441d0000d42e0003c1d01c10742c3d0750411f044e014010b51b0003441100d200e0039290b804208440d0003144504440b80c2c01005400e20300040c2c2d0a44092010702201d0181e002c030f880c60ba00072303079110300c054903182881d13454204942041551405030009500508202180c41c17061090b01e260141c0d10046458407074240c200203840307000500015588001e10110219900d80129100c0201500120040c240341908008240c926460301c0c240a201030b0b2040e0065400555071280001900b080510040080c100c0c0030040c4003030708140c1c04243e200c04e0a038803c8584524005480b03030130207070a1081201001c41440d000e480d605060300000c0c040021507a01403c0c181c0500c2114801c02001d42c85800148a54142407040d1b02c0c21100140c000c1d00102c029184045c184800224039040c0881182c0d04800c0503181d044640c0c81c00340034800001741700700c80d10489009441600301c00481a60a00f03200720390720b5000300c1007480c15000c0a400c080000c03d603004440c1c104011a00140e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 950789424 1250 950788174 950788199
    0x910080a03080a09060f0b12010b01140c0118050d1d18150406230301061d070909050f0105040c05070c0b0f13030c050a0f0b03011203050913140907 65
    0x4541518100c2c0707041c2c94004545000700002080145070038501070b8005c02c1080c20b90090000341c20101c41d9500b210000c040060300782c8500d80c048600080a54004421401c0700e18094080102008000205107072000c0600c00c4032610324005544a9000d807528400c843da00c5803003110100d56130408040c03d04c1118000c603848451304281013118064a0001a0300210b54903e004e01282e03005100707004950781d8134100d072000f40c9925501103009407400800c50403810140211002c0714514203019070300c14408036940f4021000508010100002c5000c0050800414081d881c0200b0418031000c0302035141c8420481103504d1242840103015003403000d0740220303042070485412030710700703d14075030342c685070101003c01601c40c90311280c181514100d004001d014468088100340d40c404d80c0e1145c03209071501d01ea181000400e114180a100c030400060261070200c459040403140300342410390a10540c140028681c404a0a480c032400c1c2e61503090b021000c001e80196500b0040d204080c119280c00c0c008201d001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 950790674 1250 950789424 950789443
    0x30c07050603042d0c080118060f02070b0106030b040f05091c091203120c050301030f110103021e0307120c020c1207030b0f070906020102131401090308030702070302091008 76
    0x40c000220000c0c0620407256280c5202064a1800400d4503045010315944260110744c1941d98060841000c0b9410718144952000307200041c8004810355180d82d96400a000c8000800c0c0c3c1c1960240012400100544001406003035681c030301164848040e018130040300c503000c41903451a030410b41404032449021075a203007450052080d510f48809100d2040d120b015480c0d1000c000442610505000c2c19404120100a00c00d0400288015002483e0454250000b0300024003080c04651585002804d5942d820380030b00c02c1814050300303241040c980403001160803240501141000010021140c0e4804600005000100001c05c007960071904025941e00d0350401440c0680d01c0700b1454081c08070104001d500555101e03900c50300610304280d00c1c004401094448102141004030080744850040c000d50b0555050001001030003482c0641c0c00292243d907034581418031541c0e1038044007150304280154030821044e0028102145544140162050010514800c00050400a2084030341c0800e42001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 950791924 1250 950790674 950790679
    0x17010506060412110a120b06030607020c01112a0906090c0f0d1d03040302031903021c050706060b0415030603150203070215011211010309030e151209011d030c0705 72
    0x640e02118580649601c4e032140000d68890429030001a032041c1c0d9110011100b40305a140d610141c56841c181039459a0070303600c600240e00300095140311755100d40d4880001e000c40c1c104449008052600c0c0c030451515091002100c412440710a100300e0a0601e586504004141d07141240b900e01200801480d00a405281c14a0800015a01010140c039084180c103050400c10301000308000360301070b6603640e2252100701c5c041d010b1100030007004800700c00c00741c80181e01070700904002190308100d0710480e1031058101041c40300500025021901c2071141c0c1700031b4114a02802e5440c0e05002c051100f002c0191f000350205420540b0504c000351041020900700e800720040543c6945a20b8800da080c102c807a04600d600070520f10000a40100d1005030030401030141034019a80c2000b0300044040c2c0314481d001901042c01082003404034101280713a8036214a903d0100390804a500000b01121002a108a5940d039101c80da1034410707081c2614051004080303140110f01d4002e6292445840711541e1041e40e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 950793174 1250 950791924 950791949
    0x619081608090718140c0d2331120306140d11030c091e07050a020c01080c1611090a020c15040c0909140d05040f0b0306040222170105060604 62
    0xb0b07081d140030740000b010003200001259440c60212111540794101c06201f042c5181003560003107090910030102858104060a01031803a9a0502c0c00d41e03001e01040c2c4400c0c40b8100c0c50b0744a42d000908210f280300b035103101e104a0103c484084d80c005003658031903041840c4155049110105135942c2032445400c03c0d510801c0c400c0c1520701800040c0c01c1090320b86806800001b02820041d48002030646071101e5502100c0b401c090752a0b0300740071110303030041000500241e48600c680c03140303540c001c9e00300035441f00c400d40d205031904610078201046404210012281080d829034150100e140140205074810381090b8114180710790040b40540c0d880c2c244890b451048c00ea071000c1003d1210000a50004d45180e1070244904501e270301d0045615045142048014015140c003200b40c18400c03030403a0225030034116458a080d0525a04010a900c060038656001b0f81c00c10000d0f0740c01440c9440c42d40d900c0c0501241000c6940340480344100703c044403c00e8495645000c2c2048084c0e560b5800703450940e225041c044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 950794424 1250 950793174 950793209
    0x10090501020c010c020d030e0304030201140318031902070e0c03220210050901262e03030207060207090509060f07030b0a0b040f0e040203030a0e06190816080907 71
    0x440c020710070604014095420a45603020b0030750001080e140f0914155000c03c4500385013005182c0700d01490000a00092500a40004c03102100016603000517070b5480e2404880001a0361515550000271144642841400c2440d07940c0d405100c480000c0c00c05403103409070303031800003460b031500d00c0300a14481c4a520b280c50703d00d4407050000048203585d54094182103840c41c0c13506028003990064900c4c140000d45d1840359020800034148000300c1800d664420350615250705484003020500e80c00c41c2503081100071240401910000510710055011350054405c03142403080090038130340070350400744285080238140040703903000044240e0b10185041c507241c030030340740c86a0840c05000d0029034198000079913400402c421030b00e08006c06c11103110001d03580c81e41d9945c5400c41003941040300c010754141c00920400c0201c5000e06503032841104010207403071400941200c022189500503202800240c296020030081d410960a06a03501d02c1d0b509000c2c020b0b151407408183d44d01c040f4000d00c40302c000c4020b0131 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 950795674 1250 950794424 950794433
    0xe0a0f08011d3d0f0b0d120302030c09060403080a031d060604053408070c0312020304081605060615190e01140409091e030503040b1902040602011a0405091009 70
    0x12964103030001c9542e54807102150701100084d1840b54404241d0130b1a200e60203140b45451701c201046140c2c82080d244d4203003942d91040d0004c0d0402018090070070790803c08400ca0303503a110010400f442c8102c21003178036610541c030010120703124000c511002500ca8031840500714000185150b020104480218140e134411100180d604d50142e8400c0d010905c0da40070800a4504000e01c0c03a0744009035403100c90a61303d08030b0454401121440c05008110b900041181c0301c1c041c1c0d001564001d024002040c0343c40011a008684010001020b4941382c203d41c041c800035281614855206000905085040c048030342c0200b00c00c02d185c0e841200502040c00400819a40601c803200c508502406140d91296030342c034541030160114803011103803a1440c4d0424118030300d0f00c400310300c0302c2c41c2c05547c1c2c1c40c2195a140e8031000800c40c0a00050a04191a1892110400c6900081024200e160300224515411300044001c0081c0c0311750941c032560401e81080303244c0000082c0e9000140c0b10520200d084026810f1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 950796924 1250 950795674 950795743
    0x80610140d062903030a0c060b0a080f0f191a04020d050f0f0709060803030115090b271f050a03140412090806090703120e0a0f08011d 59
    0x1000300194203103002c401e0b580c85071000110341d100b0b41c0c4075031030b46502030f807070825803284a10010382c00840c0704000c841c00800e4042d40a501c10321009011211040c1c0c5580c242071a140c200741281c10f0319402140e51501c0002e080c0300a041040d43c80100000c100c082d03658810354203090900d2105190749050019055548001012845c1d64104090b00c0940300510887c03601d4803005400103d06209204000540410740c2c4529011204000061411a403d125100ea800100c00a500307040021808021507055914070003054103c803117410b5446080701c5400c00d607104051091500780300d2144041c1c40000f6544907001803004445a03c1c3c6644d44611170304081d8020f1030000000008140010100010031101610003020207165441d01085c9940d111910b554a1030100c8400046410403001000090940c560b9126104800d08216100100c800c0104099521545c401841c0100381c0c07004110f460400c3c411640941f0444030420301910b0100b0344203030b0340d00d82041c0c5040500042002c48208a04506 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 950798174 1250 950796924 950796949
    0x30c041d28021e04050a2301030c11010c09060305090d2a150b12030304110d0201120e0a1e0c1701150303080604050703061d0a02090a09021308061014 66
    0xf4211041855505090b40c942150049a004140c0700102107240c003070081070b59801100e2850b9400c1420500001140a00041d210007801d110030140c911000b201c0138003441135144010b40c3d5000c551480d0250080c1664409007401c101a0000c8034459031403a4403052a2003c1ea10390780e22101c00b030425401c1120341c80d90042c0c000d0b051754015000000c1c08055600b04103a81d80c02202e504181c0e034040b0304000c2d120b10040d41c0c010843c18001144104c2403c0c40c48014203a540141044207451240c05010025201003002c81c28880c0c000c40d0b102c40400420400300001590342c1420001c0213129941c8101e20340c03006000e2582c0d190170700180e607801000d0941082c2c100e440201401000d6a40ea4980504120b100b5a01203202c0d81c1448006034030300e0320038810f40d02141c41c0d08828030401c6111b400101180b030005403281d5400d0343c0030480c40b903594442e1004a40240b199042c0181c2d240c5403c184501203d401d0b801504460b004081488800100000428161031401d52514140e00c03034940052209845034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 950799424 1250 950798174 950798197
    0x1c17040801020703030e0d0e0904060902040f02070b04020910061209080403050a0f0317150f0a090507021e03040501051b0309100509040c0c02100e1203030c041d2802 73
    0x3e034000401d58113400505803030f0424001c0f103a0781b4007040c8098900e0a20604003d0308510382e03c000401141150700541c904900242000450b902c9103010030050340c2c4141825944045500d013480110f06144c2d1080d984605041030250003207007440c000a040000a40046207400d0701c1d09a07500a0208480448000315448001c40d80000c04501d0030301d00741000e514098000c1280c3d284008500059818268420b800e001c203010041e8141208000451340001440c60304890040808a1217510038031a241c003030308141c0c004050b80c0010340b28417207011002012114194109000c10026a40c115080d5840c1451145010841003012010149103001e0b01002d40c1d8007100714045041c01e56008401085038a405590034080d01c0456070064a0b020345844009400c038581e8003449a01a228508036454036000030411089420700c62841461900160b0b01c09034090400101000407060b5990032812407002d8064002c11854040341141c14400111900390b070540c40d000c000e080e13003200c40e4121450305c03449 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 950800674 1250 950799424 950799427
    0xf060f03330e0412080a2d150605190e031c051c15141509030109020d060b2803200d030201090b0901141302010201060e13020405061c1704080102 64
    0x16040c01c800140810035000041640745c030126940402c0c41c0146940d001001d25412075804170035404000e0100314a1101c0c8417503a0391038804102c402c0c1025410020102503480c140c44901c10381117018403014040e10310081c022171901c10016500d011500c10400c01c40501d0550000326192401c0c0c61500c551020190481511840016001504e0703021404e20b2030000c40d01401c4030b880fa1940d402041107031010071347c045948401d40300c1000000005043e1002c0140c004200542d259001c280c0da6180380c2c1c02141c005440303a41940c036604010130000c2d126140110084412100c4141c1c0c200c07112428003000d0308a01e40c020031304007800c00403002c5a45144020f030005010a1443c14024000c200048080b2051103102011480b00d810500401c0b80e040c40d107143c14845902d60b0f61500c820ba15402104038195501e4142c009000e0b11081c0c0d45511541640c40b04000b41500c0e481000201d0300005e00e101d201d803101011460001010300004400035900c070120750912881c201c504401030207a9444032105e50b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 950801924 1250 950800674 950800681
    0xb1b060f01030b07140910020705041a09131a04110a1403010e060c09060d111611100509041d0616031505100c030903020603010f060f03330e 62
    0xd8000504032409202d44040b5030b21101411502d22440010300c00c4101800d1281c0c04031440c1880400001a051740100e45400d81c0d1040400c0c203949224610600f10088404c52903001e0a141034800d43c814156107401e00d00e131006076a0401c50001c1500a500b030703411784a00103000c2108142c1301040c0c9120080004008560303440e1841c1091190621141c065400c04820320004980020160b000b1440c1c015440d007455400000d10209800849413807402d2511403105200e80700c815802017003c0f00c2d109890440c03000150900d0860001d445080600480703041d05868003e83e848000d8941c0304e0300071680070420300b1880090250b88900d00b03c1e01c00582c02440305002426004941c80301501400340c800b40143c025a4101034458461071080d85d80066001200b03101c0340b8481c80c1d404400a00c00c2c01c020388810b45a8000c00c3e02a0400d03000025024107103281032284a41104458085c00f199103018000c00100c0b10350b180b001a2108010146404400e01c001502021003608002425155049403400d14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 950803174 1250 950801924 950801941
    0x3020903031303200f010e0102010f1d1203100501030f09050615180f011a0c07060905040e01093309050c0103050c04030305030f0c0f0706050907060e0a0b1b06 70
    0x5050710041300d44018495052001c0007841c0c24051111000405203461000c4807001540c0381d00ca8141d4a41c119560b580004c0d4076460548944440842c8200c80c03100b007009294100c40c40c0544c1d040b40030780c100800344100304c0004d8121071a0001d6407000e1070301185c1502002c0c00c15024000a18004007107015480401192122491640d450302004407070b07014a0740c4401010003203424007a12100848554071005109460440040c5e403081301c00078034a64034200c1c00c94685030500156401070000a541414104000c0c905801412a1032610000030010f03808990b4850048442035065603c044151030343c060761207410395801c1e05d4a0521007400740070400d454500a5150700220105a02085c54640071807101ca4448069800392a07050312030a103980c035541c81a490802c0020140480308104219046140d1840d4000d8a00315204940104980c00d10742505418107105400c030504020021403d92090754401d492075081f51010040c0d030743d83d115048800c01403d66550b40c04005440b0b200c00340080d20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 950804424 1250 950803174 950803207
    0x3090f120f08060a051305151206100e070c121e050415020601080a1130100e12070215041509060503064e060c0708030103030503070302090303 63
    0x507580e091410f544140030842e05000c3e600485401c400e071405006121842d690000c0d800140c0c2d03480701540c0ba10b01ca0b0000d00c4001403000c41100d203410540034440c1401080e1102c00c058044c0e14460416031403c1032004100c45c0043ca07014000301105010501407500442aa408504100140d00d05c60301003a500a00154072031301c85e00c0c01d1003030b80c241034468040c804564541a03075070070350280810701242e80b075000d89000c61500749039101150040000c102c1021140d01710302208550345c01481c0c44c1c1001102ca003042c600344100d107a0107081c20802c1c842c24038085070300900d205204040c0b0380c0351012400441c040f9420445a14034415000501203807a052900200c40080c2c02666803a80641d2100070442c1c40340815980d41d078202d11021074800c11458100004044100d074040317002d19004000c07152043c0a24100c41c44040d00018041c083c91035003040c000c030744e0300241960040d482c0816565881c40f052005110180403c5004404101d030b80d8425011510415001822241c0300e810352180d210700d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 950805674 1250 950804424 950804447
    0x70804240e1009080426010504210c050706050c010f0c2c0603010b030402040f0915060b090607120c06020406390204181a09070509090304050103090f12 67
    0x15125506802c000d14042d401010b030b03419400025542404e10341006a5011110402d4011280801d0070041e1007941c000d203d04c500c21400346440c03400e542424103400c4885480c0100901c200704034044040040782c00081c440703080700c00340c2c0341960303940705075088450040503000304e107241c1d150514590307603245030b44007142c1c400103500f2040608140e005d0300103207140040c043c403400d0b800c0305090004000e120750100180d54058006407010400c200e8088161701110302c446d004894904e854903502d101043c461107000b01a2440c0c101d403d01d44002e003000a1414000e0b80c02c010060212807510b03640d494400c03940504442e50041d81951600c0e1a9503000c3c0403d00c1030700402c0418010000b039030038400b4080c082410300340265810758190158607000c0c03001070107116880c81496440c5015650000f400080c888810b40c00b1629400a1070801d980181c0c20b009490348034610401c101700501150360f01c0841160112182420009803d01b030601d00381c0f420744100d440c064200306418102410507a00a43c0e11b411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 950806924 1250 950805674 950805701
    0x51803190c0b16080d090501181401060b0904090203070e04062301031104091e08031015080106110a080a0201050a1512081612020312150907080424 65
    0x9050301c40b0b07691421030058a92401c68408442c00b000e01103907034607004040d180c204450210343d02c0c509803034103420348070685031201982c6100000b0034144168251850080103000c0000d014180c40c262000f40300340104191036108036900d4080c1070071590b04001010090020808411240c54a0b0401e40014800070b6a0303920a0b0210f40004007492140f40141810f82c1e610950b031000000070441400f00030001100125120b4812202d949460a001c0c45055030b6148644ea0140c0c3d07030b191901084490b0801540080c0000700107100c1e0405013a009016141510060310700300d141007c0c00314010380342c07001c001c20180244100140c0072000d20740c113411407849052404010300410000703040d84004450140b00b1010118020b089460004505900808008000c80c02c4a4031010450300c0c1e14a1160990303014401503807000074512401c540400d402a1720020100201c0f540d852600003041d98107a00421403003c00c8410030000c3d007007100380029201e80c842d80129951440c400e60b21128001c080f180e04100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 950808174 1250 950806924 950806943
    0xd02091215150d0b0c0d1401170f0604030c0b07090e16110609030a0315050307081f09050d141603021e070f06180e0a06030606140108010605180319 65
    0x103154103001c951040007542c050182c0f90b442e5940c0b40011519040090102d1091f074952910020f09640200458042c0204040984442d6001d1140502c0d2103241d0000ca106900030004001c04a60010900d07900207400651003000c6035035000044400c6846034000183c5004602c0510802000140f150f084600b200d4071030ba9689400d285038140e807121300b00c0e0003200c20750003001040b03442c03442900b281c81c60094407100c42800d60703203500000f4140011900501c010703900214882070058060407510350485c1039821708110700303810f686980c0d894607282d007404000c0c8200c400c4002c2485442000b02d0b554081b800702080a4060103280c02500c81411407004064000b500c5543d0300d00b0440812280101c41d040003160052a10300101034400e003100034400c0c61401007400b00014080c6850790b080d4032406840300e0010301d450452a2000484d181c1342c128034605d0041e40038014242c0d0b0030042081c10350719241400354684107a0b09030f0460303901c5012406505400f5000c1c0c0c0d60800d4802a001c0d001281c403511005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 950809424 1250 950808174 950808211
    0x70e0c090303070501060f360e1516020c0105040617060607140f06150108010306051003020d0303020409060b0c0a0213061d010503120a09150c06050c0a0e0102060c0d02091215 77
    0x2292402038905484020090305401c0c46078108c05900c0340a605d0100e00554140070004503d180c07100b00308441141504c40c100f45429065175051010036081c1c00242842801d060070048001c121000f603854401e1b0070808000030906c6a9981d0040da0b9203143d22204a04280401e040b00545a040019008120b80324400100700e12400c0c60b0b6064403058410307915891140c0c40c1d9141d2070054640504450000c542101d00032000da2078400d044904c850080d11302580c0c4520300028003040700c110790305c1030070002c80920803601c4a080c003080507545950101c503d1821100b0340f6001d240181082d6010100704151592242c0098015005060407120110305803038217040e411b64641640d124282a010004a5201c020f0180c081d00c0c0e1050807402c041441c062105000e1590b0b0310701114003d96442405501c0410b04e4001d59070b01c8403081e41200c0082c4003a020501340007803402038a00841c0300041c1c03400e40208a07440a6110740c504017280040990840381000c01d040c0c40d00c0002403007500c0110310160601c004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 950810674 1250 950809424 950809469
    0x403021507090b1c0e0a140c09060603070e01030e01020d0c090905040804050907020102090307030b041b0f14120316150b09070c050115060509040e070e0c090303070501060f 76
    0x11804944800c40c3c481e182c040f580083c0d01c444420760200c110381550ba1510101c41500400840700c0d1203104207501c0c01c01c070320741501c2c0c0c61030400f6401d2a284207400b1001003100d1600d803402940e80103112414103180e800840d4005902404180441c005a980302241e5007014050940042241401503180c3c0860380c0e0700e07030b82c1c04c10507154102c3c0c006d00500340400080199043c070121301d9078001e1041c800142445070140000703041005c2d40e4019a00a1081c5040c4000e102c10403210640381400421030706039081c03805142032064042c52040d020340c0e032080c0e4440d048584030415980a80000030f807c3c1c0e555280d001009406a58900d0800e4500d0380c0c1d1440d10001c107141c1480384582e04070008081400e6562081e0b001c9911fa81e038024100c507a55261540001c042d80019500400790003d80c0703904e82c841c007205080c0001c46640000c2d150701c075803151030104500d802c008401c0e50842c4a540042c0d075502c00741c50110380f80d4443c444c00208258070f40040050076544011683d0242c0e5124108607a040d01203242 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 950811924 1250 950810674 950810687
    0x501080402150304030909090b04020a090902091b040f080f0c0d1505060409020301090f0615050f0607020423090c010309020907080a0e0d020f010f06030b13050111030403021507 78
    0x8009402000d81e42c0b4a00007401144007442d40306100b40303440507000392545050f43c00c1c0c410800b4100d9020022509000443c0b400b0790b901805070840050400520b0700030b40005410180c090005802240c54003024110006144100d401900c407402d440c48407961350750a810740d18000c5403403000003805250030034200307441d0a008003011203810030002061000400d940d4002010003a0845901548c0e9100c950016102030180c19040780c0035045407052600075040400940d0180c000c01d182d1080c2000b01405207944240070403020f181d095443c0303601c540c40361012800500b0341c1c084091088054026921f6008403203089070307100710300400c1620035101d5003800540580d0840e05000394800107810015038268070a640856100c0040d11010501c403506424803414414116030800058004030050038000381c0074080c40c101600001070030415140355031161700004201501444402c440400180706000094115686040d15441401e90f00d0074140b802954500d0f0040c1b88412954022000130407c0703001e9407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 950813174 1250 950811924 950811931
    0x5060901080709020c071802030708060603060a09020903030706060305060103050706030c0512061315032001050708070302010e01050f060420040510140d05060a08030a1b02120d18050108 82
    0x5000b8908541441d000b40060341041e40950520b108031200015400300d990701600c1058085500140c2d80c1c02c003443d00424401c4000c6c8010300417801001440202e03114483d450080f2111001d0040e10380c03404a000078294400c0034030141c80310303040807008418054081802c5d8100e034410030454045e00d54401083d0180c8000340da030300c40410b04c14401380c828213a02e40142070340400d00030b00306900d0742110031041c402c0b500f0207003910211180428082c000c1001841e40100d80308101c4080c3c150f404c9441000070050302c603042d00184064130100f40d000030107000b50020740e0180c07919030091049291180c14824035050450b1400d11072400c28581741046080510940403082c00700d00040d160504003c14000d502d5616440c000802603410901900c80304401c000e003264094220002c01c003801d060b400c10034024025082500203030420013203a52015007116210040080c502c02d0600a4012070000804080c5070030400080e500542c1c2400040942c001025031101c640d03044e40d4610192950011241e59804a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 950814424 1250 950813174 950813189
    0x13020303070311030c010c030b01030c0e0a0b0f0705030c1c030504020d030f0c08030a0b030d32040902030a050a050907030b010b07051e160506181e180a05060901 71
    0x4028050100f0b105202803c25060844100c03842c0a0007212031500715441c1816040000e139032542005220340c4e02d4010ba6008003641e240604001300201c0001d89000c4062203404041b441c006100d0411055071020346450b150420181c07910340d188004c07265100d007041c1069042c84a074a142000140d03009209480c01107401a0103550700700e241d41c0d025201600007511b02030a014071005140000b6400d10019445804245800306240c100c10061615022030411000103110109149801d00141282c08424605030402c60180c050f03002c100303034203052266800030514103000008102a442058001c0760003004140740405c4180e40356803c150302c6a05501000f0000c20304100100031040c48880034140203801078068403004000d04038030789152100e028501e00c042d04a901400170248ac103119000c010036041e920b9a03d030141b00d0111f04200408141410f100c0c59030020700d00030080c0b403038030108502c55001d484440066203000004007418021140040700701d0030040010b42070308140440e213040b1000f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 950815674 1250 950814424 950814427
    0x1501030f030c1110020c10020a03080a1109060c0a0c08010b010e01030906021315140a050a050c0f07271a010c060e0303010605042d1a220e13020303 65
    0x11550101d400c03681c620015903d242a5107000502d65503144621031520101d60020320701603a1502c280106406050300410940d008281c0040100b6003050040b030744014403000c001040400003a2032002c502480ea046074000e0008140000184800a0342d000390700e006614030034426580344a400d0907541906e8800340094a40c121080665010b600324007003d91003800b02609101144130144081040340c1c0c4203100081c007440c0c3c01500290842020f04505110076a514503001c10703044041d1291140c0ca03049170400000103594422050184001d0324414004001e40350b0a0b03644800d004418594450300203141c001a480c0780c190342d0703507134031404804454081045003681110001501d070001c6c969400d0710803a8980c0380120320b102e03045c0700031400b0b0f040c2610358503140d600b0500c100003182268008181c10092683d003202120108280d60421948010341c29071940040b00d6154606024101030ba0031480f00250008a04004460a0350150b8a0443c02440155034140b803004a1003001807020f50103810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 950816924 1250 950815674 950815703
    0x100501050a140c03070609021930170307120506090106030b180405151e0c0d060b040f06021924090210110606010507030203030c0c121308150103 64
    0x940406004075940c29060381060540c200c91821175001c400c044812035030f50301420f002c500d044c41c502140075070312140d00400641000f40310344230101c2104104801ca040e282c1001c12941c1004900120141d000325000390902500707102d41c0300c90700203844107408543c560201c2c02e00204180300703c82c4240c2005200908903440d00e40143e0051211900d181e0f049001d03440340004071503006105501462080d401012080d50107200c0e00c0348058003604146420380c02005003da0028181c0c10103030450846d0740e01c150384110070400d0000814140d1300c0050000c2d8080342c00920044004590300803140a5000d4864941c0c0e000c14078400520243c800a1a603500c0c1c3d00c15200d00d0000003988a185c105142002441d00d02c140c00180403d820916800c0000305810740303040c10000c0c14040107804c400d00b0f080c61414010107960103034480c04010058940080d000c01c100300c40482c108000c0d2010480070204030307500c0300c281300d48024441c2d15000c2d0240c24030948107501080c604980d07485040b281c10085203280902c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 950818174 1250 950816924 950816927
    0xd0908030c061b1209070608010b0f0a080c0408011a03062503090204060b07061e020c42041106070c0e150901090603050f1b10141b0105100501050a 65
    0x9000150700214280c03d00c0701e0610104c006050700c0c020740c444401081001d2401c8402400000141c1045401001c20f02060681284040c21340303040040e0350511b02960380d01c5007150301c107501403980000031542c20b0460700c50304140d085500542412058040c1c0300e807599030740710302d10011069602240c048403401596902191095004021b5030303100074004142c96a941c0f07214a89904991825255196140140c443c1c0f10303641c254820076502401c1065042143c8004003540b28450a624540507403044850656419980c20b850101c2840084928642d81c0d40e90030b021400500032a41160f05091a21007400d440c54000207440e09076512801c0d524256003070400500414202070000100200d6000b005132169560320700c9103018120010000641c145141400b07450508006441070041d0400148542e100c1c1182000b0035a0740010b0710040c0d22015a83c50413034115018000c900300244020400050442440140480b01340c441c500a00c07094840780002041e100b0140309207808030f2410803a220f40607 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 950819424 1250 950818174 950818201
    0x51002130302060d02040315020c0f0f03090f030c030106030b0726060d0618061a040b13090804080a1a06010516110a050d1a011d0105012f0d0908030c06 67
    0x41c13030181805402c06542c4d580c0d00301c011010200b20049a41c000c21805484981003144101b0040818020040a50300c640c0548c1c030b9200d40b000ca2401007100380219102620100211111248003400810000d1394905003010301c10070991300040003414620b032050300c1e0f61601807d544c94050b001c002034403949420003005010240407404980075900d980140b0b10700c08110ba01003000902500020409a011a12480c0100d161a40007480b5070310f400040c106580f00e1100e40d0740310204003100050240100d00707000070170340a103030301c0ac0c140b03442a442400100020710f01c42000b40003c04807048216100c000055a060141e610410001d0340c40c0c000130008940c2c8084561044040030b056113100303d855002150410116440542da09415142e1000d40d1922840d2168010302441c2142c00c0080d213861120030f00108103125960410031a031200114a2148181c010011528a01c440c02c0041000807055280ea01240f00c0c100801d5034004000f491a2011086488030324070740000d0a800e66070445e00032241d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 950820674 1250 950819424 950819437
    0x20709050703420f031101090323160608061e1908060f010317030c0f1b0c0102012c0f03070302030423010f03020d1b0c05100213030206 60
    0x2c0640f6290301180c0b140312409607029142c4034141042c0410616206040040d00c003002000c0c40c0146944208220200c000001040c0d036400012682c046a185004840e0000242c0000d09450f14002c05002001501c1c641c0ca2031740c0c00c54000742e078896021100000300b0382130715108520210f4000400035840d8030f81602080303035203900945007a2131843c100e004544181c1c0007200d00f0340c0c0040340c0d06045c410042c1c104101c6502c01c09210700c800d40c6d903042d41d42d003503800c10000748a13035000c200c0803000c0f07091030800b103085da00f61155211116490328540302d121a800340c4a522621921301500302c819004e9403040c010030300704000d280142036003000001c0b0401e101e60000b01008220340a030301d41502950905000900f1014041c0d4000c5032528100003100f22781d0320711405c04010741d070598580d0700d500e80d030004521020070b5041c2c00d00503115659a52081c0140c05103120350200760700d0b061005900f01d0b0f00001501220340c000c0049072068502d61380303000102e10483d50300024500e030038a0100700518002c0018082c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 950821924 1250 950820674 950820677
    0x303040b190f0c03020d05010828060b042a020a11100e030f071d06030706030b0102030c0d2a0206031303020a0b24011e050a171f050a060207090507 65
    0x28545580c0c0102003c88a20041c0e00f00080c0c1c0004054060600a000b490701608105001e4003601207041c0120040d5000107440b5048908041d00060034000710342c0c00031040040103041400b51048061007103900403800b0940111a002003009800101d00c0068580e512641c018041d28102500c6e07810041c420940520100030414140b100020648083c4081c11035101a030307000b040e880c1d040503d828007202510301761040c0c508040007006880da80001d40b10302280c206083c005450400031004034154495404120300303a21411111594556114441d85a821203403444202100c01c11140c01c0c04500ca5210003a62011081c408140008026004240414800d0040350462211583c8075031800f002268501c88903040703940138454802102c008a02d90b85004d10b070174244000384281404800001e400e04a00308003001c80c0b00d4071814000d00003508002c00b402d14005140c6009843d03461700c0000c0350b03461003d10b143c070500000e15043c0420040e0990700d0940251200604044601c401402c00900701e40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 950823174 1250 950821924 950821931
    0x120b150903240604061203080f130203060412180b190309140d0e060a0503370605030706030605092e030506060906010f0c0201110a051507110303040b19 67
    0x445412841c02281d11a91038601070b0200c501d005002c00c4200c1d0400e41c001c501c1e4403102c110302c00020b60710201c016400110040300c2100c5840d6011145521600804001e40621400040c0401d10404065061640c2410361f5060000429041460f00c810740a1041c440c4d068002c1c00342400c0094010b014210707000046c500000d030040706d91900b00b42e144200010315400c0d004144400300c1c45da40080c9600c080c1d0020f8400031714082c0c03c06402805480014046140c0e1119480807a41d110710803240c1c1c01c51000000214140a000b4000050086c0110303c102e0b4071a00c112240091010b020303000b09000c8a8000341035820031b0b07480c5400402000001c48100d2006140a942180e07090b80c2961080f0145010b071b00104858640b06050040c8038001a2030346043c000b4803c4040780030780c1d1141100040d2642840c0045005403031041d0a03161421400300100700e405407080114a15100c1c1c80302510855240c2c0e43c4a042c0071210100c0c9440c0c1c40300f0740d0094501485180000c1c00342c0344610324001044039003107001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 950824424 1250 950823174 950823193
    0x705010501171f0e0d05120106050405010c0f0f060e031308070302010f051e1801020105060111030d0e0a02030a03081905190902190b030621151e0115120b150903 71
    0x50f4100041c2d07255171404140b0215030009074100d03508059008d0030603030501030318141c20030700003030b241c1e05407003000601040d547e00e144020002464000d02016901c1030307040c0708491900c042d00381c0700d8203e050015806010014006101080013411204498060b100da8000c0500700e44111115401003032071503030801c9404d980400c1e00548100419510442004d0403e80c42c4d80310000a00b55840035052078104a1201c3c080d089003d000300844580d200c2106001a4111800b180641444100503004e5418040c000f02e00041c0350f003104119102c1c036010400007440c5602004004102d8000317840800168030392032990880b25025034003080354140010701003d00d0480c80d08000e002e0440075004140602404010b20107207060a0003101071041c082d500d100c1d08c030880d00c101a903450381200e840c028400b0a81000c6a842d81440c4400c640080b124205400c0e25030310303001d540d81340c9102c21080b800000c40310b0003000b4490071940300b103900f8080000c1000c000380ca41001203842a80166148681c14055019803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 950825674 1250 950824424 950824451
    0x7020d031404031a06040e0738040e060d0c1a09030d030b10050c100504060204030b0c18060301150c0606320306090709050405010b060f0705010501171f 67
    0x2d000110b21610034000350000c0c920100310203040262a5500990400e0b031000041c02010030000251201e5a01c07101303107111001030020244002002000c5080043c03011160003103683c2d0014003c0c0e450780742c4d000c1483c3e110342c014000e0b1400c07000d40242c82c400300201c00740028010801c00d80b070001240388610b428607100310300280c01c0c581c40314240070109075540e400b20710a0601440d4900c0700000fa040c0305d07040142c040240390b1942c50302d046100d01d060f600c0000804000e80b80e810780b405560032292502c0c0e68075111000c10000e0b80260002094101441000c44c503e19000e01142e060b1000c400748607410a03e01c400030764410880141c112203180c1c440101083c410700380740302070079010034030f0540203000c41980310400039001c0500055802608050104000d1100008491086604807000000e00380d84508200b40149100800b65074442c00001c0c000b08a0550345000d030850300c0c0030710000c010030799135020024201c8007414025000358105c50030304402c141c05810420180312566001151a11001c0756 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 950826924 1250 950825674 950825677
    0x120a0623221403070b090c0d080306030f031b0c09041101080603010b06130623090d1506060807031a150d0204031406010305150c190314180c0109030807020d0314 71
    0x40340b0520342d1000c20310380244090092800c1d00505072401500c104040382000c81c10780c00000401400d668400404100070f0b440800c4030203004283d840a6030784442c1c10301d41074461100f000b03803401074a00c100750b8207020303514000750301c0d9004507402151061070a1780400151250310f001050158155a1009405141d0701d441c0c0c010b050448400b07824001d1503080440c064400790f9207140d41d0504c0f80d901000c0d40c111411000441d2a1000219028200c20260b868005079030501f2a01c0b4080e25400d186000070115017283d07129002d62582e88041c8a5500c1d00c00c00c0c0303142e44030a20740b4240e01c5804000344600c001500002402810342c0250050300d0141c907030315040d000441856810321950712020041050200921241c0382c210a80e651001050400c80301c0c803441070040d001c1c80001c00080611a41c2070074003070f5101204100b0304c100008010b02c1d017250901c002041048041400f406001101707426584030310f6051302625170100d400b600348603243d02804030322000d02070100c00348058401e6900710800e6240 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 950828174 1250 950826924 950826953
    0x906021216020d02041505030d030219030e1615081503060109270b0603150f15012a05010e030703050f091207180c0f200c120a062322 59
    0x2290704a040349087d017450f02e0080384668010415206010720111804440b000044610b0b151401040e01030000001360700301500203026000e000001100003c10b01440408624a100292100c0c40c540d590510b450309407210142d0210740c5908050014460001180d004150150300c21102003030030f40f1607207001410004494000e840c0d540d020010040c1c0c0745001c0181250320700c500f901d0b074070b0703d420804600b221041e005060750115106c401d10026103a4403400c00f800300720f04460704013860300b20002c0700c0c62807c00940d0020f45541d401c0c1101c005240000000700e80b03816500d0381da1545030045040c503c20741500310303040140d80324600024400612404011400142984e541d40900190404141c40c1c21180d85c00c0ca400306005100c0c0008210a801070101d410f001366075001510040481e076007035820f08022260655000c0719402c0d0004c0c500720b0020301c001c110fa1140004002e046c0c50094110b00c2008020306461048100000080110150070400c0c4148010303141d640070310180540d640075001042c074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 950829424 1250 950828174 950828201
    0x7110c0d03090e0a0b060d36030809071514040305030c03030109150506070b070201090605150312030c070305160506040f020915011d01140304050d0906021216020d0204 74
    0x20062100d03144010781141c0040f0846400c1251172640c5020aa090003001039007514650f56440100700200c1c42c09540d08409a5030800b05d40403001280802c0d146c2a050034250005800d200c00900c19200c000352041c240d0301801142a4528062402207603160010b400d46a4030041c18080000050703001c201522000e00715401440d12076040008000454803922400000d0310308200c1e007001540c640400b11000d080e00300c0d90501c072560b80d00000782e01509480d0b000400462a01040210b00e1507240b01718081103800310b059803030704015100303041605e01081c2c2d458029900c00f0002c800000e8010b200a040c0c00c41014643e02c3c080c145a201c560500d13a04841c2a01c540044041202c2180780410080d40d0003a072445807202c80e032000000090044854980c0e0b03800b07181042585640b268054003c01c0425500803110595900c0d2524100d511025141001008201c002c6e0010405d07900200d013845143c206400b10900300380440034200d103a07401501e001da80240f0200002d5000d6113541c041c0c40c8181c80300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 950830674 1250 950829424 950829437
    0x501060201062102090103021c0506240a050901290301060504140916120207050708150906090604330c120603020f09060114070f0201030c140307110c0d03 68
    0xb0150800c0d041c01072102c0000070f89146a11090059840100b0141942c0d010f650005880050003902e44043d419035401800320f2190b0010400d006003402040c08205000c1c4e5240d1168044403018010b007800d86c0d01a0b16842030010005004a400728401d41400001421000d45689c41807900f5078076aa200b0307086040051400103051004100c030054003c0100300c00c0d52900814030f44041454051091710190301c1c100007052100504401c203640568403019000025628001e9594400c560344411400e20400d8402e401d00c0010b001d184c012526510801000000d00300d140d6499580c00b0400c0c0641c2101090b00350401c5541030a8440383c0c1e08104489400b84c4000750412007620301a20b0f80400019100440307040980c28001a202c54250401c01d0382e007518030627516100c110040c1c45120008801b10401c81010910b1000d0010346222040c44038002e88003081400c00c0f940045407903001e200d281c001c01600c100040350902e480703002522201940c40003a00c120000036400140031400424007540050b12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 950831924 1250 950830674 950830679
    0xb0603100f05011416051014060f0418030507020a090614010801140a1208190801030c1a1b010618020409050c0c0c0907020a1703090606040515040e03040306050106020106 75
    0x1c0380760071502400c0e09082110b04454010345941251060100c500194403c8a1170320f02042020001d01d1944520403805120261481c4283c5611317060441d80303584510b1031000546d00c0342c100746c4241c5035401c1d500502e0484803801600c0944041d44500d9080742c1000318000c0c00036801e01a8801e41e000f07405e01c901d0008180d80f40e03e00040188106801c08980b90065034001c41b01c9035200c103402011910030318507000c8860290300345481c15020700b00240300061401020b03030049070741c4840050705032881545c242001d00e0b00c0308140300705ea4103090035440c00c40b00b04010719130080c800c4030141c44074520083c00206070710352503085d1004070060003010301d48030b55008101070103682c00b0350080562042d15602c069003099004c448181d91010303032151aa00402d100c40107c2e0101d8401c0c0030340b20215800401043c0514410b00d041d51403a07200b200d0204c0c01c1d0050601252143c5494000c982c051131028280182e054000c0c0c00f080b0081c1042950f86c5440e100c200000400580301d4041c09008003080c0d00009900ba2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 950833174 1250 950831924 950831939
    0x1090504060f0606080105191502030309070b1606020d0e07090b04060e1302010309051005070c0309092306030a0b0f01060801061b08031005060c49030b060310 70
    0x46440720b0b0488101d080c4207041c0a0240d02101c590304513142201c60810b8928140d4031440b40844a0b00201002c01181c1841a000d540010085002d01c1c840c0c0115004541d441105900034010000c08403081164200f00901144054019000c039203214803000815400c04140103141c03036034503800040302a4480078401c42364513003449881c0c0146280a02045149841c4681441c0f44280300b100038189980ca8801c0300a0090402440a051075415410482e9042480e0080c0c2405500302c01180001d00e0740d080420151868000c21074040060103503160400340d04980400b00751801015150180f03e055504804141601d1ba410b000d490025806125541080801420903c05030404000d110b0355805003510b018a0b4034001c400390b40c200c5140b548a4440307111b8223641c901c4551059600ca036020880c0281d1200c0814060400780501510700142803c02c1c502c1c41c07034201c802c807070030072158140119039802185819644020b0b04051a0000c0d100081c01c00080c0d003a0800c1d5040e50300344440c1402030011f00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 950834424 1250 950833174 950833181
    0xe040c0e09120301090905190c090515030c210d08040b06240304020a0302090c13050406061205040c2610090c14030a060c050c01200403290109050406 66
    0x58501902d0791840b61041c48403035102c107229060100750f030385007018140724042c02031409000c000b0701842c110342d00307a081c0035011078001e000710492286002c1c00301e03000100c0c0300c0303410070060005405031030040d4410f4100201080d4103600200c210210300703002000c80b98203001030300740d0360015204c1c0030590515040461681c000104618058120403403800002c01e02c0301c041c403c0e90400480a16a03c1d41d0b1880800c0c1c50070032a030300c000c2d045208a402e0100d042280d00c0604940000ba101c4072400503a42e004110176901c42d0300c43c64010030308131703030805e80924201e0300b0981d8018064000810143c0d5510320007101d070070b40fa8040d41c00208002d441c0c418131080501c103000b044240e01d2410b200c100f4075503c85000400151080c03445540310f8a2a80c61184c505221444010360800420002e003048140c1c060003c0e441b01481c04241e500e490401090458441d140140140400390524141400c42d0b072070042d00c0940403403004006a1000741105c040381c502c0c628a01070902610702003401c0c2410b1070b0482c180d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 950835674 1250 950834424 950834431
    0x10b04180b13140a030215070503040f0809090708190c080a020d0605031b0306010806190b01020f101b020304180b03030c101a06090d020108070c050106030b011a0406090902090a0e040c0e 82
    0x607487c0b46c40600040d184d005003500e81140d0040060042100c2c14a00501e01d40708803600107401000b079108014a5a421a100920510114030703090300c4c400418a0b03000894a012003080e001c0f03003910300800e00035501079002d0f00350044151700c00a103144d122000603280003002d01052403106030b4400f0302c02481c107090023f01d00409190000302143e00b070180b045210180346400768135000342c3c0c07140d039400160720030424110100c0c041c6003a00c070b5008400b035001000d08a1010103082d008642500c1c00f4400744000110380440311411020074030910707034000c884080c21402c0d1103690f00d80300c1440100300041040c000b2440310058410002050b80480e01410042650108240e110300030a00900b0120784405031391900c050781c2480d24203881c3d5035103070040d12401c1081074050301c558a00003001c010001c000364858144c1c2c01401034141c1c1c500100d40803504620882c05000005990036500304100b000d1a00a4000900d0050010310603a03107950b58140c00c407008540507216007610440420120040e100601e81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 950836924 1250 950835674 950835703
    0xb0c0d08010b191412060a0501140904050901090516031109190e01020f040b04180915090f060212150303090a060c08071a09010b04180b13140a0302 65
    0x416615040c9888960701521071050900f40301e442c0e03168501d91040d0324401d1009014207034180c81e010b00301c0c0700c203206000032036043d030080110480100300303580603280d503600c1071400d80103081ca050501d81c180005403002038102d1102e5901d528803040010f00901400740c030200b142004144683c51400c004290100b1000080c0c010301036202404139204405034280c0982c0021440402d5180c0300b2683e09009118400020b0f1500a000c1000708404000c6801882114803c107400085054800a81c004444003030f8001003040d1454a00000c0488190f084a2610f50050010108005550310b40d031050f640281140c0709043c120500304840f00044c1c0b94041801442640110309008001c0042180e42d1350030700415091104904150041010041c1241c01e843c3e80708581031501549d40380041100c0f10144d40031300c299400c00e58051001e0030316200d400c010800c030280003403c24819849180300404080c0920701e0400d4401800030101c0c070301340360b541c1c90f4201c085c009212420070b0382002404d180c0200141e40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 950838174 1250 950836924 950836937
    0xe100c0813030c0c051905150f071e170702011b0b0a0f0f090303020a020723060a020c041a190f05040b130501091d010c0906080a0603020a0b0c0d 64
    0x9548194581e95821560504102c0070f490042c3c281425401d0541e40150713070115610241d51545030301d110101045800a03210280a1100020302c6801400381002280f03080c8000e00484d0042140301c2d55400b400c007009040764907014055110781d5000e5213020048840580c00050b04801c550b8090b0011009610f04460004e24190aa03116880d03084087d0604410545070703071251150440d9a401900e00b0310140404004071101d610300940650403403641003025015046000038001c00d002c56080358030040403070034025916140108803041d000108001c003140300d09a020401d94855204421403492980010342d40880580304000b0010080c84a10001c41d0641100700003492800c80078806403801210045010000e11010800007078000041c4150541071200008101c145540881205500341060112511884000c0e42c04d0790004150840020f82c44d0310108081441800c400d900003a00090114105d5a00e80000d07800512070f4005110030f41e0700007210700d0804401c009080e0441c09504001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 950839424 1250 950838174 950838181
    0x822050f091312031d070f0b13030f0303060b12010513140a05060d0c14030d0e180601140a2c01080103030c060f1b0207090b0616080d0e100c08 63
    0x2c0091076600040149140200c054129030f1034000c2e0080c240600080c2c1544100102d151003195440e60b191040441540405101040c0040c0707a100f1948900080c0341c51100480c42c50756030080f000382c0f030a019420076a81c1c09002c2480d4003d07030010044d100780e8070754048595041400f000010140341c203c10500c18135115103d5845007000366295400110004005032030b41d100b03000f0902d1741d2184080103102d682820001b088448006105000c95070b01501152a1110710380f0f010740f520145072025942c019085030800c0100f45080c10104d52004c0107140440c807040c008600c000a903040040b008000c14640862000040200740c045d64401607035942c0c3d90403103128a00082c12649060001404100701d071480502400318641002c081030403446070403c141d0381c4208004e09480c0c194500310005002c1c102000520507164000c002205200605040c5400d429840c00a000a60740c035044a40d10401d000140040074588a0014000110000381041e080404000c0084a00b41503001d824000140c061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 950840674 1250 950839424 950839441
    0x8060106200c0d0f05060606120a020306040e0706050a021009171e2109070303080c0a020f10020306090109060303142a33040f0822050f09 61
    0x481034801c00d8880d101da1056240900608010016a00ca0342041c0c80326407071000c00082c0e2900b550b02900907019901075845000c200301c4030b440b07620308290340c0f01284004100041e074070707034000c40d0031a10052001540c0000c10b1401c90170000c407030b4800380104501041541c2130680611000580001c2d5200810042c41c00384d988428104864212803c84134000c1a490b0141d80c03454101c8004486100000d92280c43ca401050b0b488001941032114803c4e80c407000c1b9454020000f9a1016654103071104620b9070b58080c005070362034000d1440c0504500c01e0b4100c0600c601c50601101d94102e44410b0003603a2442c08500780000e112060b4880300d0180d142c010101b0229034828200f1220a60902c020703a91803210300d2100244805800000200c00032854280961100008003207010040d00f100b00310b00300c0e90f030005042602d021000f040e00601c10030720004001541d020850101103100312034031400c0c00e081c4442000c9650502003104009041d0785d50030b11261501440110f4012422030380c10307160b81f510740320 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 950841924 1250 950840674 950840687
    0x91401051005030403050f04240c1a09030702130203150a030308010b031504020c0604150911090606070b100303020c09190506130f1b0c080a05071b090b0a08060106 72
    0x204807040107000b0011808061045003142c00030140d40341070640f10390b11070b0303040040c1c1600402840070f2a440016901d00050291940d11032050300406d0342c80000c1e009500b83d01038008000d00030286800300708201c80c0140d0b10321540005502102c0340058407460a2503041416072001c40403144119042ea43c2000020340c810200c1d41941e2082800b242c0325150114030000381c10042a8613540300d80045450f141d0040b000500d1403043d401000c001540240c08541704040f201d10007009000b503401c0c0a12409181090100c00d500b00801425281c40c1c00703910b0300d40c00c0509a040d54061841c0c001c4840030024594100300421040c074040f0b13000000c03820322103043e1601c01c02010f81403407155100c00c0001d43d06d544203801d224458101140500039048106070640003412001880d00c1003880d907007120301d2900c0c40390720110501684041194a402a07140c015521030700261811550742022854032400343c1c4010036040000c1075400b4021416280740d402304612a4041d402c8880039905c94001001060b50024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 950843174 1250 950841924 950841949
    0x1c02070b010605032413090b0412050903070605160501240f0f090518070f0623030711030c01090f021e1e010509040204060503061516081b0703050709140105 69
    0x405d034501800b030020480c610701031505080711500c1d14455900b408030800e0041d00c114480c4407010a0004108030650341c0c0d005040140303401d540086000c0c40114024401401c8102441290340c40d02c181c159a203e003034441c150856103010303400349490800740266030640b00c0640040c2a80e48069414000b941c19502214498a88680d0700c50021030191205071200514900c50581a980344580751503010070a155280308010000d1071944d481841d101d014004130241108841c85a403958403481d00c11110154500d00785010b1780010040d80300038242c2482407504861060310385c0f5504005034010403641000c0c0c1e184400303640070009541803a0390359500d43c10b903486c01d503440c21400c4030030702d0001201c060042c00100d0703070050310004012a409810401551080108944031080610f51119a00c40e500440202c000c9440c00c0700c1c50000026034003000340480482d40382e2a00d003d04c00420b0510302d08145c991040d249604102c0041c4a4038503d8041d014004203c2810705804c1e500d4500810b0305c030030030310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 950844424 1250 950843174 950843221
    0xe1504120e13050106090602070618050603040c12030f0809062e030c1410090b12180102120a05061005030429010b040f050f06030402151c02070b01060503 68
    0x1c0440101580d42d11080385105603080d108000c190b0711900003521150407805a03070054481c4030341c0020458450f000701c403508280c440444514616082c1481b410f0703040504102e640820001020076540c0500500c200040e00940c0d594440c0b00c8900380245c1904009007803032400c0e40102e801c105141212880b020340509125010003014440021052080031554000624030720b4401d0000440c2101141d01034607001c003c480d420800f1055690540c3d018646104240d82000c042c48000002d1801c902201d9005031a9030a4520459581030900e0890f07002c50b00211a90783c4e0b08050148020f018030846510450680e6480e990020503038000d041c0d804014001012900192014540110440c0d1070b084250204041a00c155849441140f200d8202e0701038820061074510300041d0760720749a075200284c500d01070306a07032440d03d40342c0910440c04070084044180120800200c02505081c0702c1c0c48441d8408984010303118511454080007041060740310703a007000801e006009480c04203030710800341010071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 950845674 1250 950844424 950844437
    0x6170d0305010e24060d0c03241d0601020106051008191a190905040515090d09030311011113170a170d14101805090316020d020409060e150412 63
    0x740000245e081c0b040c1448115040d00b003041448409406400884201c9403096000025012001d400b41403061a489048129994000b80038001c113111044544c0254042c8000b10302981c03110041002c5c0340ea80750001c80000c50003400c01c5208030030020710342013541082c0004d00824a081020211100c0780103411480740009100c2c00d0039001c41018070348000d054000f010b1000f0b141c98100582c8800bc2c1c80b15106420040c1c40c00115003040c00310340c640c00700809407525180241146c03030403140c01c1d4034261a1003940d0340c0c0b41083c00c14014079001924102035014a1302c0c0c0c0d4a4180031502c0003001c1e0040c004001079108035030210024040b19401e8107040044001261110b031840c0f0110041c110340b078034020b400342220040c001c9030002c2805a0007070784c0b5814000000034000c1103140c0b00300c980481d00003d1a402c00c1c4144070241c0151100c0a602900003031611109c22110340002d01165444c04089510307954548480304143c406005505040a040c5e840340360600d002e469140c1401000e0460b8000c2100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 950846924 1250 950845674 950845741
    0x20060f1920090a03020307150807020312043201050106110609030301090209030304090f150806061003241401030608060c070f0327050411040b12090106170d0305010e 73
    0x11030f580220010358009044a036010340d2036410340f1750030006d070448178005043e540c00112507500000413203420700e4019034044042c0e07480351a20120394180d00340c210702091040c0021511340101c01c40043c00c000c0c0c602e00005d0b06501d007400c050112952000b51034810f400032030401040c0c0101005990443d950f0b030324090f0b0b0f01c110490000f0b04620441c0c10100e101e9142c00c2c22240801c900d42d20091542c8101d2407500d5195885801082d42c8850884000c2c1d407001021001c5036800707100341c100060300495174040d9090510400c04807010220300342c000c440480407d1454040541e4503009500c014202c4002805040c02c141c00e40708228414510081d103000c01c00040f44082510650000c00c1c01a001e00014201d031120640702e211038a894881d84d0710850501d8540400e201c0c90100303ca0440b00d40c01c41c04c0b860f00a80e010040c074180d0000f08800b07455541c954001924680c50903503a20200c4000014024880e980d0201500b1214113812a40a03a0784050801c00240c000c070b80c11803a4a0032400e482c1e0110b8a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 950848174 1250 950846924 950846929
    0x12010204050645040903030e250b0a0507030c050c060d020714031c0f06050603100303091211040f09020a0f0504050c03150120060f192009 61
    0x41164401e58200e5000901c21030203822011540485240038601c408601000b8074002102001d24070030500d25980100f100382203490075030300030801244039040214204180300e100030308220078220014410084030f0410741074044011f80b00741c0030f408901a16070422403e84802421401903650090622002850010512030104442c068403c40105860380d152004959000a500304e140d0403100c17080c050004103001e11010003030360b1404070016003000c1205502c4110704003910181c01803d880c10f80d10100440d846d15402e00961041040e8041852801e2031481d00800c860240d03031220390030b071003e12807440000340304184c40c100c980c00441c0c01140150101c002c078002440030b00c000030f41c40f02e2125400509865019131010454030300321000c01031503481070b0030408580b0040b035a540d035525031800425000d40c002c0b5400407501c81d0b000307540109007821446451611100340e4084000c81003030410040004154160341005000d0303400c0038020000c131080c8481c0e44240c002c18908030210301244070700068 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 950849424 1250 950848174 950848177
    0x30320030f041202040e0d1211091002010b01170705071202160603060602190804030204050403020304030f0605010302040b030d17090a060911030c0a0308090108070c060528090b0105120102 83
    0x1010401142d9841d5aa4a000300e0441d02038002240580c0c207144201c401174401165107030003242c0c6526461092180011220020b01000d100d80c54014024005c4400a80720020020b1400d807041e00000360745400d090014215060b40d01c03030100b110f8071680c10811445d80c01800da44e01e00e0f034421520340003801c030301605905001c505000d1100c0119454400580710346d242d0001c5003150383e26001d0f59620f01c0040e59888101400541c09001a0000c00042005040070f0780002e030f0141c083d205903806c03d07807269a00400d9a210318400d4455985500042c07003585410300ca0140da0110880041406c903200d26006400030341e441e04070b00d140700071450010b2500071044c000380c004280c3c407420070807400184d4645034151440515015009210b03110107924a0b00380800d002c01036039002421241003c038070500464003010010400010070408020301000503800e07004003400742d80103116552001045440c66032440c11020307641c5142ca803c00d004100410041c441050540c1d80654404040008411480740a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 950850674 1250 950849424 950849437
    0xf0f0c0314070e1506030c0f040e01060903051605030a0209091c02011b090f0b0f0906041212030209101419020d030609110d0207020f060d0e010509010603032003 71
    0x7204110703030a60714005008034120040e80d8050345003840319100c4010455441202d80700050300710344c0030000f107162264010042c0120074030b895000e510340b580760300904003110000c0e40442c001c16401a0280204001840211103641d440030100c0e40c0d01e032030000000e64951074084040e01810682c808100300e40c800f0300c41c00c00e1400e10342e141c040319030b800503500078000c000b0750540c040e903850361408401400b8452062001100c8100c11000c00f01400c0c03140b207102c1984114801e550303064040280e01c0f081e441d9540900000c100480f031000310079100c3d00b030400c1d881200007002e00405104101c203c509548070900d9074481c03242e615013002010008100c0040b0780c45a524100e0045031440d0303180e096545c0c00100d04501038003560f0305000b982ea072800a5002c1d24120f12008200344d0040c448514620301940c043c1c4507080c0020a865980c4003410003084060784910b010b004070b580c41c1c01418940c0e81090041e1034101107544002c0012501d11384005001000d600806204000b041003010078441080042d00c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 950851924 1250 950850674 950850683
    0x20603090709020f210f040803090f070b04050f040603020a1403030c10020a090e060306070503060f0d082101080604061d030c1606110606010f0c060509060406060e040f0f0c03 77
    0x140e07066013201824294014a40f080036945204d183c40c10941405101c182c0503e1540074000c01a480d42e40c0c4541a981000b00012146d1040d0b86403603201000410600c0300a0010002032961641001e090082c0c3c070100c00000760242e0308000080006845a078101801c4034480c40e00648071704500000039081d48104407940a19114880245502ca031242c0c0c01001c641ca2030f038444610703140d65582150000f260403100b542d4550000000910701d6402900159070080009040c404101c602000290040c21031050076160b0540c04906101824418110102c100c101b0380805456503141120541d038407140108010500c80c1c84ea0529080002c50061858902602c542526102d9041c0c1184d00d40da0060812644284032842400058890041c21005040c00c23100c809030695603544c00040d0341700944035011104008000c2e03500000f10340b0510505000e0f0294801400442c200307414000700759610340d0031144020032880c05000005d512030a1900c0550b5110013107118989550802c80504000c5500141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 950853174 1250 950851924 950851927
    0x240f0309150617060103170d0605090f0a0e1609020f0f1903200706150503030c030c010b01030216121707080405060705162a0b0d0f020a0c02060309070902 68
    0x1803582569800ca08152000560006222141807202c513568032001e1101605180c0100000e014940500004050010004102040c2e141d40c800208619480c1180c100c110080c030341c01030052071050703030145543c0c2d410401c0003041c40c048000c3c0082a209024440c0546403a80000c583c81968075401c19030300e451903100c180c540c80c0d41e00a140700d20a011aa00c201c80000d15043d14a1130070b4070190000e503c121443c040301800e050560303072000002c11003001d0300745a1030810440018035a508000418484040d000955180d510340c42010f800e5174442c2c51110b05250041c0400455620000c1182c401182c0092031b00c094a100d00314240c0d81312089804003811807640c4010032035800d8000e10581e014500c2402243c90710781d190b500440d680e010703400e00c0c1140c5a114640031404907031511101e100c509408040c41c9007c2c5680386103e45041025802490210008a03010324081040d110b600302e4451410425440c08021080082c10324514501c0240714070000b001069485204001d640c01034181141c045 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 950854424 1250 950853174 950853203
    0x111040602030c1908160201121a1905030616050f0415170906070e01050903011b02060702060108030d0c051603120e011107080a020f06010311040501240f0309 70
    0x94a030740c42000140254401ca2184c4400044a0424021500d030041003190502d40d1603c82002c0d0440380150503410040d400c2d504043c2c00183d4441c1004604600c0300c0185005c0140051100c40e080c190481c0044102420040200343c4001c80e24960048820b10450203000b400309059845020b031503001c1045405c0401c0c045100095203110030100403594503104114043c4a461015210b801c0354040002c2c0c001e54046029940111781030344130fa840504206007030420041c0884d00719000b0b0780d0804600820f003800d20012540600103607800619600c00703841550f0600000c140d07280306044035204080d580b0714a1200d4688142c09450020498410801c0c01c13500c1428000c01a10000740000b81503864601b4178280b060051090319003444011070007a0038144207455049080e005150340000350b0003075194001d2002d005000a5000c2c620840c400341e4a001480188000c0b104141c0010304416115556110070b80c40851000322100042d14041110340340a4104801a00c5d0469000f4816100a07144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 950855674 1250 950854424 950854427
    0x5070b04091505040b03070306110f07050105010f1a071e050115051f270b0309100507260a1508010f0c02010204050904110409020907030504030e03072601110406 71
    0x14001d0b4085040b10b503244a0380714420401103c1d03034400d0041d855030008804100040850b0442408001c0500b641800c10200099103581503100007802c850300c0c2d40d11001800560303e16580d45028084003601890708880ca400042828810540c014020380c803919008007022285109100750640c2c00b500031b000d6102c0c1c1c152201352603202401618400c000020201d049801d00741807441c4448541c4d51091501186101d9841100f15240503141c46554041c0c00442c2d030b842c881e00118042c07001c003002081d90301221200e02045440180c1100d08114030b2308003400403840c111000241c8070290104102003a100c10907144010409914503c039040d080030000280c40c48103600030400d281c0d101a041c8980b59545008030708071300c91409125132001d80140803070f0105004a01c0f0038154540684006010403040d0000707143c0c3c5200700c1d50280001d45840401040590103540250f003440e054000308071007801d000400386030703002401a030301108076104000320524201350820059907129a08030340e030b2a070701c9500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 950856924 1250 950855674 950855681
    0xf040b03090715020d0905120307031202070f030c0611031501050306042901270e09030f07080702010e2232060127140117070e15091c05070b0409 64
    0x40003400f15910b0100010182410100702140b4040300c005582b03015501d60f4103450554864400c1e00d010b035030a02040b40014111454280414001c1d2a500c030140c2d000c0c508103090307030450301c080034101601b0301c2848001030f0340c6514100080740074207049449545070008140107000d001c00e60342c1c19215802e48520400c0000810403101c80086e03880d20148400d00c1c41c00184141001150b200e8a038020008004140c1d400b0701080d000762030b40c01924540f00350b40614440a411558007034440703810001d22841150380025294214040c20340c4e02000040040506030810080094240c49a0f030f210300900c04001c5c2040c11084030081082543c2c4d0442002001c0352040075400c80c0c03018042800c04d45101e411410781d03800050900c0e840325050400b00c0c107090740091030b00340400d812030501005c01c2914200b4030b5101600da100342620b9444d0301c5440c0040e020002e91101e44103060141903000c00140b482a12140241c4994540b03a1070349910300c2c04180ba000380780210343c2c3e1144110710408600424015207a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 950858174 1250 950856924 950856943
    0xe18010f0501020a0c05120a2f0d02090609060402090919290f130513060612050a0b04171b01050f060d03200102070c08060703020f040b0309071502 65
    0x40d000c0d4540c48400680c0e56446403000a400710030b6514003006189805005820118032100544142001503943da024042c2507501490f00031105641c000e01994400134502ca001c0303c12540500022005d40205c0c030b10301070103460940070b9405440000c11645894045460b004805012031625260980580144550703c003001c00000303081c014034080540903c1265400c6191241c2079250b801000d03070800656411400d55240c20001c00480f1a40707014185c800c07144600d810074107100c9012640e140000880300d8070b40001600011b4080000042140010000f149a03404646070300e59072141d0800964020b105040051a1840000d074400380321640703031080c804c0c2ca0b003100080c480d03602da86411000c0c80d0411101503401010000c51031000c20300c2940c95007a10003640b0502d2003900c66185000f42641e204640c2170750380001c0c0410400091900b001072661054142c9011800c10240344000d240c20700c41c80c440c11071801c00100c0460a803c10600c4041700800300361031405103000c05681c001c0e4690072882c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 950859424 1250 950858174 950858189
    0x727090f0b04050c03070e191710150513020c01060b0a12061a0a0e03010c0521160c050304050607061415030c060c010908031e0106111c0e1801 63
    0x8001d10614200b50094038002c1450111050a40e03554010031507400d40f850b900f850b48072001c6101000c80c407024641c00c4001d012100103240c1000141200289003079000040408964546030b00c6c010181220500c84d01a41c808440c090351141b014843c440c06030185d8100a101c5520340100001e60612120050806a8050711242851181381d0130705811a2264462200908181e40c4007030510820100100100c0c0b04034100315076580f201c030012a003118040d2010390b0204000191080c103044a0300081056501000301041051810340003401403808450204810b0003241d1401204100f818802c1e10082c000c044e0000f52036010f03904041001e004da04c04800800d4001c400816039106901c1940b43d002c050103002808403c0c95034040c40341d140e10800040300c040d50b803000f8410005112000441c00b581840001c1d003401021400f94080303c201c1a8040130500031404400490f0b10000700e00011303040440c21a48565001e4203105135030b4440f000b440190f00c20302181710034241042c041412416110703013 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 950860674 1250 950859424 950859431
    0x60c010c021f06080d050d1b0801090b040b0a031b0b161a04030207030809031608030a0813150c051c0e010b0a0b1206031c08041a0403080727090f 64
    0x2c03030500d41211214003560100f80c00818661101e01d014800900001c0b480e10b600140f0f1110180070316641a09040940c40002c12641c010440000c16000300448808110f60230801501c0840025404c22290300c002008001405104540e448842c2d0a1034020722174500081d56506008025981c1c070034a20358120390340710619411150041449021612a9605400030703c480d60554840291a03002194401d506110f002d06020916a00007101c1004022803801952030303581c08400a083c480d8001c003504880d071500d8002c800814000308400700002c008030300004d03820201c50300072603c1e8400c8504d11003041607034022074900d01c1c8150b0b008500c0c02c290035000b005004108802c00089080c035100342c990404090003c05840b0300b03c0119590044001000c4900b03500b40c00e0340c0d01d8400c0c0c041084400220340f003c400c0205001180b49030051208211840304200d141955026048200190801080002049024201703a694018600e11407000100107041140c1d160001030180904c000007031021400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 950861924 1250 950860674 950860723
    0x5010509150103050c09040c05100c061a030316061409100c020303010b0703110120071202010c0507080a212301061b03020703170a1b0b01050d02060c010c02 69
    0x1c151820307040e690f029000d00742c82e4444404201140c0000340007500c00e41c42103400001c550b900d02980c04440032498541c1030300c0702200d007402412580c800040c440c5684400346840c80c1131358044211307090140208110341080b56a814008000c0200e030342c401e881401d143c410310042c7e8400161000d503902034204184200004850b00b240c0707030302003886004400030041c80004c0000340651444100c080141000003858080401c0135603030240e0354803180e039949a00140c1d4200380a801c0c1448001643c0a000070310100a0b030340c000400318402c400d070143c03102c000810340a08591140070004200340c861402880c0d007843c20b50111300201042c40c0e000320b0520301c8403a8005140088032605040700c0b502d49034048409006242d0b4006854040320481c218000c054020000840d0030208110038042074054a84502401c5805000c004c10400d0f42d02000c1a0702c400b40c40001c2c0340c50310f400d0543d0016a59014420b1703591010a01c5030181c070310003402c07950800c8181071006600080e0303209000c42c00180e2103130404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 950863174 1250 950861924 950861953
    0x30f0c0806090f1b2e020d0201140a05130c080c010201060915031202100603030906171003060e0c12250e0a1a0d15050c1809090a020d05010509 63
    0x7500c40540702c041e900320100d4290424249655568075000251030517200d00304143c3c0b07070b00074200b039046900941c2e024580c0710804140d040102c8003101481c0c0c0020819100690003e41e4441402411504401d494000150060301c3c0d140350b0303901031a8040440c29600761910003003a107510131204024010343c43c2250008010010340a100366400c1c2241448150301c1c00d41d01c400c400c41c141440d594056102e4106611103880152150400031400395880c1140c25007030280041c400d6415865420000d0000010b1108510a100080045a5000000040c490b03040e22141c2c0c144498042c109030f2240c02c0710502e004451002c5601d41d02240001d01020780a039829226120201c13007402000040c0e20a00001161421071354000e2410300c0d2840320032240036113144005403900e01c1c0083d04580404507d120b140386103500d4000d036900308099100036402c100c80c9050840e40c070800d11035440d2003076220360049498041c0c1448200c2490390050300300480d07000503081881c06000c00340c800c04103a00c5200d0601c0c2100303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 950864424 1250 950863174 950863183
    0x304030309061a0612060117010602030903010f0204061209051f050115050a02120304021503160210050712090c09050903180d02010804060c141b0f030f0f0310030f0c080609 76
    0x44000c04c498200308041c14522014035005001318140281004956101310402000c43e000304469401103543c0c00c1c8540505096604012985041c54011f01092003100d4000000f4a240c58801100042c58090b078240545040c10740032000021144902c450f03554150240c2003981601d4444100c3c03402c042d80214102c529100e44008400180c1008100001d080040401160007a000403e0444410581c841304034040e8005e445a1004e00241110002c1164061007502010070000d18108458940080d0281852010703942c80c401240c0c0d2110760702d0800192090f0340700504295102003100346410703000b0319a40c0d80300c03450840e203105150000e6181440d040c400c12411586c1a912050f85490756a111000f0302810352081c01030010b055004e002c1070801901a21080848140c2c000c0350845c486ca07140e080100d0000d0400c43c2d1740040240d40401010070049031010b90030075176041c0d07072030b6181d880c0e01500d03180641009065515109500e8288004e04020005481284094034620303198240203941d503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 950865674 1250 950864424 950864471
    0x30e060717040f0803010603020904180809150f0c0102041e1409071b0c17030c1e12040306060303170405060a02180a090c0f110601140d020303030403030906 69
    0x10440782410224050000030250064800c040c4410030345050b0f0707506005a0026004180002c0e03002c074009100340341c03501891502c24070400c0c0c00e400d082201d1b12009002d106618801e07006803080c00c000141c422030303d002c840301c0c8480741c404503842d0104510418042c0d03010740300c0d46581c2604510b00d510030b030040d01844000c445031100302d45030084401060042035032008000100340b000412101c1d014140015034280807a11942900e500c071410484100811004034080400c95401401030082c40c00000402c41c01020020150705500c69040c4e02c903901d0036202080c914601c02c0c0100d000420028070b50460000e5a10a4031011308a00004030800f005101c2204c01401c0c80c2d1108000c40c0c0e114415500625000842403e45002a0500408500e18450a0b8080040c450b5501d03100c81c070140c0c0c09000c0e10031150891505c4181210101d0b2060359903081802660484d401203036903043e40769100082c0b40000361740074099a0312881c1034140030740203051800e0140c4a039800d01028a00840a1100807144c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 950866924 1250 950865674 950865677
    0x60405180f3306150408150610090b0d0506122406100507240e0a02091302090103110117160801150c030c0c031703150402070c050603060112020c01020a030e0607 71
    0x406070b42d61810010052016440c804c02d1000801002c01c9000041c4030200551703102132048500c4d0b007050000c0c0f00d15015040c400d002008400d6400b8001801c100d401c4417840300e070140011446455210018001c003070040f06401941c03050038810383c110a2500c41c03005001054401e40c007015551042030000c03004100d100240022010080000003514007081c0070b11142080b0503c40c0041c040d014800c00302c0b481d043c821002580010036000451a10078006039110103001500040900f42da40030440030794041c04010a0640c800010301d003603920a04400b196815030b5000c0d00d403182000303a50901c50038005983c41c0000340212002203910035008803120207160382c0355540841003010703407403c8820302c603511030031120f0070004c4000101151000d401542c0a4040c8075040f9900c0c10500d4804a000c0c075148400da000f0340c0140710080225031a11443e800f00d03482903544658980d18900101c49911200c0503100640d48041440100318505601070090100e0303d4904018440b40610959030b240c0c01182d2650 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 950868174 1250 950866924 950867023
    0x60b34030915020f01150503240408160602070609021002070e0109020901050708190801170d0c0302010209090420030a080a0f090e0a052706060405180f 67
    0x1001c2c0740c4405405150158810f42c0c81082e50b410a05094030308260030002d240150040501451409100000840307651211203c0000036a5201100c2640000e2000e40f0b200408120711046280d4094561103803a8002011540e650891604100a040205050340104140d526400182c2d0000075404c05890355100461003682c6040301c4007010b5440910f510781001414865000010f4424020304074816440c030240c076038404040401090458141d20070038080d801c4100165164101080340d181e01d0486103040030504056044c02c0c0d01900c141550660091482010071080c0b2012a0014089030858580b03a142d81d80003504043c1c0d900030284001e44440340c20088140300d28021002986000c001b42443c090702036980f0035580c0050811034102d1061a191000c200e0340440d030042c0e003170442484618004402c20f07562811544c0c2c400003091036015a580d85c2c0825011030151000315400b0501404803032405000200b01c03a01c40304498414140f1102e640c1d00d06014202400740507488201002449 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 950869424 1250 950868174 950868179
    0xf0304060b040203250311030915100f030213140f0402010f050f0919050604030308012603190909060f1703041a1309020d0c0f0e0f0f0301060b340309 66
    0x743c0144d217080440c1d03818140e5030000815100c647c83c0141d8883d8072140090085082c0d1606c4150303d00a00900503010407400900c01d00c48001c454000d46c0540b13406540180c0b049182920040060800104109a1049a10800003004004840700f0300c41c07407003030340c80d40c003001c054000036909401003420304071300d6803824030081d1081d043c2104030804032411500c081501c1903441010a40e168015001a00001c4200006005440a401c000c1a01d190400e48e000c0e46810340090701a1240241e000051030400070310002030349640700f090b210f0054051741400300412980c59041080c020b03614810082d0810000b2400c00003110040f00341c90440f0720b00180681041e0300681086030030752044400c1c58003103101c4000452051420b1001d006e29030b100940008049030080409094203081200130010801d10540b40061074030303025502c0190180544079070b52800c2ea104000303805054290003140301d062000c18080c0c10128588102c4045800040c0d54034483d030403441c1c00201400d2281805408a524444d08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 950870674 1250 950869424 950869471
    0xd050d0f18092003071112040303050f090a0b040b1c15030b04050a050d0c0b1303090612090b04030c02010809070308030601052a0c19050f0f0d06020f0304060b040203 73
    0x441e4000300710380d0b1143e444101c3d544942c0c2c0c442c1c2065a07000300140c19420306016040f0100300c43d603808000e07203a44a045c04e1071aa0005c2442c4140040c980e00c00b80b0100707500e0000d444015039840604441840307140c495890380010080394100d04500c807004600d141000780440040e2080070070040a001c030704c800050070740c0c50703030143c04801070700483d8580b0078520706c1e1000c1603060101d402d95000c540e8070812004a41e04003004103040203007640d070715080c1c01081d000000c3d4102caa1007088a80c039003400321070000b002243c14010918104058a031180381401c110806034010101107800d8401d80354486240c80b0303000f1081d903070003107408010010070080012450540c040d5020341041104150100c840100901c8001d50078101103004e500140c1c01001d10103280d02c1c00310f810b03c11b075020040c01080480c0c40d2400250211000440e0a401100d0480080d03041d41c541c0d0101a4607a9001001595200d546003481c4156500c1103500343e8420346401c00400032071074240212030103a00301c0c0700c00541d101842c024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 950871924 1250 950870674 950870681
    0x100506191b0c0902070b0601050a020a120c1b0504050c070b04170f180306070f090e0403030608030412030306060c05031804020d091b0623070602090d050d0f1809 71
    0x10800d21000c845007071600000e102c41110760240c03105020150b2140d204e458920b000030340140410303040c00700910110080b5680081c0c1d0075001600400180016441a8000d81c0c0210107090042c158500001807a544a0b844102a80850710103403000c00c00d50b03032900340700c03012402401402002d5035981070114020a0a202c50440264a9444428600400300c3e8952115500406000010109100c10401280380910410354042440e040501e101164001c0c010508040347c046d603007800021501080a15200350b101d207002d446504200c96840d41c44001c00f03c4000102401180000d081003400b04200b84240041e4800e42e601070000c41c10f000107540c5001000741407001c095002942400070004003056400750362410b40c000c80c46501120a0f121000c0703a0301406401141c14880ca6050f12030840000b5103a03082c2e48261001d50b00d407601c0203032514030080d208000301190300a0080351f5403414450041a00316220125031510b1503440c1003410241c2d203040b41c13041c4000030921108010010640d945c2c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 950873174 1250 950871924 950871947
    0xf06011b03050c01270b0c030c04060518040603031e02070f0509060102210d0b1203030c07151b0f170c0a020f030f041809020f0f010309170310050619 66
    0x220b04291944583c5d400c080d041c8001840d0485400c202e541844040c0740b0b0241c0280d00f0f0540c0501c0d500d084ca60009091265105801c10400000b544044000708803c3c0b558072154010003d0041d59920b05000302030b443d00d103120300b108454408001c41e045000051140403680b41e11041c5030300701c3c500301c2000389003c002071166041d40500a4040000360701690110a20788950361100e031143c03900c80d0000111060320401c1806040b05181c0c000602000009496010843e81e40195a03103a40e4079120f4407880800450050440c1800300300721002c2c16008200a0714140c80e59001c0b4840c01000341202d0008440c03016125a8004501141503807042c4001016001c2d0540101c031100c0269042051070b40e40202408840600042810310a003262039049144035440c18406100c0218150005071002e92030392005031069190b0701070340c03500da4080d0300702074421500032001400341c8011024900700ca90040f60b5503450800b810303502285030300d40102a2400300000d485d0100e00180c0c0d00c2802c0c0c83c0c050030b51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 950874424 1250 950873174 950873197
    0x5040809040f020a03060501050405090411010c170909060402130501110a080409020c070617060f0a0e0a050a0e150c0304110a03030f02160b0711150a0302030f06011b0305 75
    0x304800241034a450103600c07040c0255400040c0c2e2028040c3c07000301203c20f9070700214100007080101f0032030341d90781c9848681c00540000a0245485001e40180ca210b01480700052602d91a0761101c510070788290090140640b00b0b480f180003c0e5616000c0104a02c142003040300004000c01c810700c403552050350500201c86440c13040301c0046120b0f03280c065954001d98402003810350000303589190300006110f040c0092420381030400e800e51802e00e403054454002131a05009042520382c0042a6850322182002003001c4413002c04070341060a91600a0f1204a6a1080c15030401701340745010100020b031031809501c91140070328541c0761100e002c040c561005d842510b5034800c0040980301540c0f0b19030008002e510980b204619202c2e90724000e0b090014468881400d0703007420104000340407401007103500712a1700441d201090140309001580940544c42410800c56002c1071180e085601a402503000300302c00d4030210741940e10b09004640d40c055045030f0718000004c4954200c0002d01600c0644a48207a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 950875674 1250 950874424 950874427
    0x6090204181109031911030d0f1202090a0602060703110a0c1707140a0303061d040f0507090213050f0a06021905070321030507020c061e04050a031103060a0203090c04050408 76
    0x84100185c5400c000005e0301c00250100350f1580b08000801a4a682428094010b07256024840380c01814035141c80031908280588100c000c010b400044e03040741d52110000300038100310b54032520000e5a9242c101d4404010a10f0001e1510b4504020426141805c006a81d20f466921882d03991180007100b11940106002040c410718001503e0100c03180502e440c00401811845e4803802c3c000c080d01d441e5804001503500c0d00141c1003422215101e60759206030004ca0400095010740b03402d514094117a40070060b4580b007c40e840c60300d00c003100c00b801d0440b101240c085210341400030411841030b4030f500ca040c015900201402e91040402d000301d414080c003c00556140301d03580d848100386420380c2c403a031032250440f5406203100203070148600358102c07040344010b1031409013100200710382d446a00022240c03030f81c00f5129090b1200c8083c3c100c4019201c0030780304920f855640c3ca4001e5505541501c45072180c008c05000a03603554491082d80d100e5480507000f042a9011101408003c0030040c005480c0c0100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 950876924 1250 950875674 950875687
    0x605090106051c06120b0708060f010503061311040f0506161112030304030e180405060105060309100204080c0901080307030806210d09080c180f0a060305150703060902041811 77
    0x2510b102d844c000f402c03e04060b95100d82a868150301c022002050b9006010520707080c404291a4401407410580c402e00307000d43d890f00c40100084000b281700c01851340580c1800c46440c1070245410280c8121894104e01d440c80380e03201d40800c4424000e2840c91001c42003191741070380c0882c0301580d443c0d08485016040c501442107801e020350959004580640104820500001250800a80d405040c0380358400d076190314203060f5101c0da10342c0418415207210b02000b00219489000901c00400e04407401141195600c4d51041c1e0f02e6205c01c20140f40d50b10a401d144d000280703148c0701004440045925a548099954036502080218104004004502605580b801c00c0038041044004c16140070740e15240d40441c80c1040551400d243e98404a001d00c1c4201400d00c0b50020b04142240c215034894402c40345aa503070102d07400203250030751002c0c2c120301c5511401100b64158800300c6004961031b03a4240880303900c4e290f5610503441a80305600321044c04035001006080c0540c0310300e0804004408581c80c160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 950878174 1250 950876924 950876977
    0x90a02210a0e06010f0e15030309100e0d0b040b070e030604082107080402030c03070b16052503030206010905100308030601090e0a022a250e040308070f03060509010605 74
    0x740c0010300309240d05041440800d40480c0e00c280c0c4004082480045c81f0307100d0740800c1d224040d805150380942c10b0031800b01c61490264403074903d0a600a484120810207500f007400080409680a0300d00028039008550194814880b5503001103000e030007800715484079601c01c01c042e40500b40c4545c208000942c42d441061011945501402d0343d682c2d0454241010300426041ca404407010901c0790344080c20070030100e5100f60a0710303102c10a4200d08030f4030203524208941031812089c220b0342842408030788642004940c800010941e4080e03400c5802682c2c9030b101c040d08450056603111141c0005410410004e0600c03401560701400600d02424065510803c1c460048030965900100790340110b41c0c1e0702c1076980348100041c0d0200040841004007240344e09030f071b211402c4440c03104c00c5449441d40b6841102e8081c00c0740c00104100f88441d40146040e0070002d240640540791000020107903d0354201080c800d0203035a007a035100070b19003c0d80340d190240c140c2e1281c0c040c80e0740f54244100107101102ca807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 950879424 1250 950878174 950878183
    0xb031b061e19020118050c010c02150f0a090e07051e0c1609110f0301120203031918050d1709040e1c18180f0216030e090a02210a0e 58
    0x4101402011450403004101134259512118038140c1e1181c2401681e0100d1800150072030080c0c400e00341071a9801141c004510040e00c2d000308a0792110780099514031801000c0c0c0200101c070044d645d540181e83e2074050060781140d05aa041001402c10f06c00030440308004141203806540c80508245000d0a81e0041400c021031444003e1a100b84100c0420808a10b40100e07503d40014181e0a1701d4440d4400042c400c40c001801942415038454000c40b08540b1301300f04480601510052030358500c00b000700300030003e08042848000030700d11200e00081ca41013074500c20b54101e602c5035038144440c0842070881d2aa4110524090b4080e40b120240da16200061000480481020440c0f414001141c440600320341198018260040f0282e107040000b00c508807012000c40f2101680400c00b0745020422a01901a80851800c24103a040e001c100305904081038582030a025140a4155501d0305683c6080b401068002903c03105040000c800c00e400c10403605034014600000040c2407020003d5940c9003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 950880674 1250 950879424 950879437
    0xd030509070e241906020f0309010206150a031e0203100b030c040c031104060504230307140105040504060e0a06060302160b060315040b070e0a060c0f020f03100207060b031b061e 78
    0x42d804080e409020042e41805503810203007c100040d841c01181c100002c1d9103040040440840d5580b210560784244e482e05542c030300454021400e01d00c014008042903101e2003650000301d1003845520125144100140600915014000c0103800880300003020300000d080342501000800d03680d02400c880305241040a00090055030b82c400392a5802e041c0303003000822001850f00c40380380301e8201301c1213181c3c0e00290600948001c0c81c00805d42000310001a94103001e65040198040d050370760103d080e00c00d20540318030980442000340070032a655102501203205043c15140504400321440300450b02c401d54090300300300701030204c07250202d50310f8804060890994040350026816400d001c413090744040c4072400403a0886a240e03045242c0745010703101c0c11540d032000700403401c080000819555900b48041c81c029000d015030340b144c200341940f00b00075480075100311011403405118480d0343c00d0018103c51031001c2441020203c415107003c0040742d810036542500c4544076040072000c5c00034a403028211 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 950881924 1250 950880674 950880709
    0x4032708241015050d0c0c030305060a0612021804050a06080708070f0e090102070212010203010819080403030305181005011503150e091e0d030509070e24 68
    0x101080140501403607940078401c0200036034641c040c00040c1e5908200b200407074092070f0064142c0050510140c0b80790143c0e440c160b03007051910300c1d90440346400180055849100745d6080040766902410004601100c1c050f40001500203801105025015801880707681e002e21000d5240c86034450018050f200210b901c80b1505403215030412950404000d000040d0159602a1070121300380018040705100314401d1407159008080030601443e404c1d41250350068001d003044803100518010705002c2c1d8400e106450840c40f4140141000041000741121100c0d44601c00c503150a01d1070301c048001d0100a41214041c1d0401d00b6040360381c400801c2030501c1a41060030204e2558581680380340803803540e1141c042407505200703c4600803131009c804001543c0720801101c2240d10b1340d41c805841e1007081b00c1c4600b18061402d50400803c43c001410b8280c00c1c2042e41c09104559445046545844180c454913040e0400d00022070000800a241081d56014140403071030b44844490000d8000c030701c0c1a04040c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 950883174 1250 950881924 950881933
    0x50408070212030315040906090503070c030507090e10020304030917060402040b0105090603040201030915022703010606050304030c0827030c061921020f0a0905040606050304032708 80
    0xc214100411511500304406014604510340b0340d02c20702d028040025503602c1156549050010001e003907009003c9140c01c40300322030300ca1040703281c0315008000c5400145c84610802900040c2c000f1a030003003013000e0410001030101c252551a154000e50006481142032100042000c661503130058a0b01c80702130707140307001000300b41014010f2108075580c20240c1410800208480e6550740c5452003101c1c1c205a0a1800003009441d0f420442c00c006103980d800c00003280000741c4000309480d0541101c0c071809a07000c2e191841c100180030107088800b03034403924012850601c0000c0101c1e001c0d65410719124042c0ea501fa00d06100e00444000c14811500440d41c109558968484107050400a442620200b59842441d080a440d082da21140c01c20644c44e0400c03182211600b81c6a6a16802110b0701c9800ea20a6480700c0380409061002d4000d8240500051540ea10019061405004820840b2a983c4545185032030b103032412201d013180c0d08607450f058484500201075015075459648010300d204d0b000760 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 950884424 1250 950883174 950883187
    0x7030e10200c31020406050306091b1909050a08120f1c0204060206371103131b0e0a110c0f071e140f130603080702040c1d060a050d050408 61
    0x83c50104001e101da0901688180300920100d0f03000021660032000c1241c4141c0d150341d0b403c020004001090b0180502660040b58072090903107115000346e0325503000c0c0c64050f403090300e0300107001488010348143c206950100d2110840c1201010041c2080000da454440c0b500c604244901801040340e1034100d82982e0001e000c00400340d040c400076400810000c0c66049076180e204000100c5240c5141071100c9007010100701038403a800da03000c0442c5540c0551010b4483c40c2040700d01141c400340744000c0e1664848502d00d0b107142c0040c01d02c1141030f1400c041c8018207940b20805910020500322001c102100400c125800e80e0310001c21200d11502c41c0708001f040064244503920845481200c0c0d009c4c0e20300c800034420320000d609800da9564540d0250342c030740322845201001031800010280d0001c00d1600d84100801481481c000410616000341e03000d1004000c266000c03201002076410401044481100c00000e40c54510010413107104d99180807800c01080a400c0c0b402c492094504807411f603c0001e41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 950885674 1250 950884424 950884489
    0x30c2d0319082802091c060b1206070804030f0903021909060f0302060d0b0f0a0306091106030108060708181f0608280203010609060303030207030e10200c 68
    0x2160344040c4045000c02d60b01800886081002801d0500f4440c0c41e8003c19108801d49031145001004441b44d0764114007803105040034001007010003002401030311a40503071600010f0004003180541c141d1381d244403903076480c3c1d2821602c4111201662042201440b00007001d66140c161480a11040344848800c0d01c0c0740c00c0d00f02003100d00d40da012a0f000e0030748010030005a601c80c000d4410140249002040c9442c1240c002244c416140b00c0466100c07640f0103000c803e014040c0c0c8401421032107041c40e2104001c4060030400c1ca40402d1068410036132204c400200402e110f4241603400481d0070301965030321410a5841c0d41010580d81d560b034211010000c07103035001c00c41d501460700204860f2010f4503043c1080d0f40e4420000c0b6140000203156842e11020703c0071902e00b54132400041134083c2c02005074907224900140a5401554142e00007901802500782520300b41d04c82400850b0680c0ba1100354a200c101c25068070080318134410040d004d07884640702944ca401408000da995401440d600c1001d1001e80e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 950886924 1250 950885674 950885687
    0xf0105031212150a03120f030603080409090f0b07020a0b0a02040e07050c030403080d06061805090604091505010608010312080c042112110c03030c2d0319 68
    0x984298403020303081000070100c0d03003111400020070441d10307060390310003004040c40e66501c400107070414000c10000061200744103110303034002001d507100c66800c000010210142c0c0c4403400f015224040801040040700403d0340440500381c414403401201440540318560707002021201640507812a0030040f08000c58030510603440443c04104500301810030340c41e8801a4002042c240c140040000c120a035000100150b030000e5902003000c1d56140000021036010300f01d0752068101080030b1140c980c101c218001ca00e03005854016002c45030680c0da00040101a06450500355800f4285600c00c420245c981c3c010140a481541c0319075100d54550f15050200000c0b6130004420001a142449402ca1a00041f942140c01c80300050416000703200c00404045407000c40189007200400346006450742250070ba034110303804101626142800c10f014103881c2d2091750101c1c50760303421508041c10106000c01000154115120764800c0c0e413841c01c1940c0b40355078841100c001003041c1080b144442c0990081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 950888174 1250 950886924 950886929
    0x160b04050f0607050303010e0720011406030307050c090a0b0a0308070203061003030f0f120c09061101090203033901050a06051005162a08060109020304021807030f050f0f01 76
    0x220620710f003c0341070300c0b0035803a0702043c0144000a6605404500304a00c51940d218102d500303c494800400d8480400900a11050311001c034991a81c2c00060b60b10300c1e011003510f00e03a0703030840003400e0507120050812035074040040106444076503e60004500340c94fc6044000a0341c0726054065640050f030040519202c001801c2c0c5c0f6118008003401c0c03000a80c00701c0090100f0100341840b848800c0040340944058460b41c010520310b504e08888403c080340e01002e600304480c0386031511540903901071071082c280c4078441c00107034055008010007400480300b5548400e428003203189002070006000c2d1103408448180b1b459080581d10f0f4400e0001d00805485210b000b082d003181c1d032401540112202411030b00a2840024003d100e6059000074090f00903602201c87c2d103030503ca00171044d00303403076005d87e49160703402189281e220f040008a2506128400c032405070342c0040079541d16031004030303c00750b1030300c00142094105925446411074540c19401440c4c0124000c20302c0305901d00c2c081e25200d00048059 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 950889424 1250 950888174 950888179
    0x10f0e041e060219021f05010602210403140d030b0d021806010c0b01060c05010e031e180301051503010c02150a0e01091208070801120305090909160b04050f 69
    0x6105010014440000444a205400c4035110525000e828a80024001c1c030a100c0a82d10000518100403070340482c500740880302c14455420502881c10314102203400c240180340140c1d001084c40d620910543d1040007840030030800c1145000c0d10b903560380c2640c040040c00314916502c080c921301e1070300781c044c0540004200161144d035244c404c5a00000c04588903401c82c100b4140214010035090391180301c005070000c0c3c200c00c0c7e03440b19581d40d400080a82c4c41d1004190303803d51821480003001c00000c41111810800d8000d80001c8183e041a180d46950050182800d10445100b003035100f600c01b801201d218008019126860060b00d50a06003035440540e50b003000c54200c401100c00c0c4501d5030580c0c0da04201d003a1000901080002d900b51f0050070700b00000f130007115002000316000c42d4405541885800036940d03681042e41c0e80c9504824a0301100340040c0410828400007500742010390703246901040c0d10b07040301c2c40c08c410000c0b0800020304079000510f000000041c103020f141890000304000140a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 950890674 1250 950889424 950889449
    0xe0c0d11011e08160c0609030f021605031b0a08010e07030309091b110c0d05030702040b0108011a03342c0d020607080f0c15042102010f090506010f 65
    0x2407200034900e96004200d0300558040c41003c400c1c20340f050540c540170036030050041018090b641000b0b808218100100801407184040070810341c8184500c54080380c0d0f000c0d005041e41220015158a41c03100c00440f1900001c20354000911604240182a14001c005024041003030441c00c000f00751340340c02e070829003449040001038409101503c1400c02c403a00213103803a001d07401700c0340340540c100b40c4c8240742c0c2c542c0702c020f08204a05200b404070017460b5442c401c550401c500680c0000544441ea4248070300c040451000d05040114881c030b80085900c81d010b000344400c0c4c02e120180c400d071a40b00d008803e1403039100c1450034500b00d03a00001521320300c007101c2080008003800000600c42e04034004c81a98003031501164488115200c401c2540da5840d8414421520b41030150a900125040032a2600c818480d000340e5407404007481d9410313401282c00140c05007034041180800c10900c0c20064421007190350f15241d4074840400c81c0b14503954a4450405000e6951610b03500d00e0500c10703150010081c9506 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 950891924 1250 950890674 950890727
    0x90118030b1b1c0506030c03070306020d0e120a03020c1501080a140105160e0303042705010b09010c03030506150301091d01050105101209020607060203062d040e0c0d1101 75
    0x4102c1c035094070b00840000f0200d10744c0d44e09000304e07050000e40d4803401c0c6c042c07003030301c80100c1009001c1e005070843c840402e5007000190b6259154075901c1581c14030440302e9120404c40701e40d00700c0c0310303070024a03a0421079002c035003801503040701c2614044401d0748042c12030740061440c9400c0060411a000d403540c030000c001d001e1810704844001c13020007030b0003805051286180d1044007585050013136800410000494010a071032599180c452083c43c1d190303006c0d090740340c0780001c90b00074003002c203407201031006a58020280715180d809400900002d001c490780807440c036180c0381c100d03071a00c8000c40c040c1c4800b04010a800d4015001352012302110200704500d40d0524005108903100c4101c0d0b6003004556160030210b02d403c08001c0c900400341c8d0b14021f0342140c00000d078642804019002140541400e6441c12882ca09900d075000a1480031503603903840c5101e010b2440040c0c502038000e100302c1903201b402d64242101c3d101c00210385182c0400220b074001c2d94158901c0b00b541c0c009201d5140104491090b00c000300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 950893174 1250 950891924 950891947
    0x106030804060c080f03101e081b01020a14370303090f02030604061b080c120717070f0e011805130b13090203120301030c0e2d102108090118030b1b 65
    0x40044500c9052020b5070701e840e2b260b81c420055001e000d0342020007034030151154506103031628215042da8281d00f0400341001d440c034400304032004c0ca050601c00c5000d985003666408030b028001d04002641c0c01076088240d48056070b402c1c08504d020318414400000c043e818804182c0d001e00703e880d00d090a2044840801c05190305100840c3ca50038842c0211301d65550303400d0002ea6222400c1d07030800b04440c00300010407800c107410541039500301500f07440300c00c0d0b00f0304c5941c0111540d194666200441c00001c01081105040101400e402c89001e188040350b010111408103025070024894041359580b900022070641c20b081c0440c00d070f51a40401c40501e198150348600414160a1044e10805842c0400060311040383c8800c540740c0070a2a03c0f4881d080001c50081004250280c4030301069100700c01c000680881030300200c100000c1009110703a00300e00d19403038415481c1c004d101e102c1c0c184910150000c515514482001c4060b604c00d407186401c90a0242c078000c07480604056a141c4108200001d50b00c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 950894424 1250 950893174 950893183
    0xb0102030d050901200a14030903070f060e011e0605010207032f06040b0d0e0c1c050106050a15030501060806130504050a150b01110106030804060c080f03101e08 71
    0x15005000c003080d10b441e01076003e030041414040b282d0540c007a91803640c1e1500740d404000c00d4a01040d03901c22500352140490b0020511094981d030341540d0040040714000740207860740c5900c407030003040000746d441c2c2800229825a1882000d00005114600700c03260054803d2040c0805400c0038030041101c90b08641c0e804a40105412645030501c02d4190780c101742526140725022a0340c0c0150007a620b0300c7da03500065040c0e811a01d107480040e828a1a4007402d14000540d810800c40f00420450780140040c07400103036226500c80c00d40390b9548601012656071a6213007118001c1c04802e4040500c3c03480990010115503042e04403008204e140000d00030b0039600c61001d2a00282c40500004140d1030b9031901c03529050301c440c0010059205c800c40c40700c586046030710800400c002078039080b0308200410070b4182240c000f404002c144d00402e000078041076102d80c540c051403e12840c0c00e5844e20383c003801a1100750704100e8050f40c45442804062041d4846126040c00c841c096602c00d080960400004503110b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 950895674 1250 950894424 950894437
    0x304060e0312040f0b070f170304051b01050301050d0305090d03020c0112020a0c23010c050a1403010f090e1e01020a0f0c05060a050910060e0414060f0c031015020106030c090b010203 80
    0x2c0e40000318000c0c0610000004411840364496070702c0b0032312807120000344a0780c2c100b214140c036a40140c855401c05009842c0c0c9901c09000140d54140c9560b00b054200404580010001e4040003800e020104150b01c2e44c1240c0c0603807901030307001028420741d0b000c0010049480b214410080314018060540056044805020000d92050703408241d00c84d40703000140c00d2000c0722403018103503082101803000b0517040700040444550070b95440100c0705100e60507410340d102c28032072000d819220641c00c1007207102d00c4c0e0040201c040004241c6030301e040070310000c01c4000804282601c059600251000311a60000d8140d0000f9426041c0408602c3d16601c4054540c04018101d881c0e4948900001c4c10801060141c04685281800d080100c10b88814031f4440045007140d08030740510602000c0b98580c07030000b44951040c01106401c0c400e03660392449030505a00041d00c4095983c1c2d100b000403130948128101c0c22a020030760b500021301e1601d103040c404500309840c1d100c0f0348458601511101c1e2a60b011007120072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 950896924 1250 950895674 950895689
    0x50d150e030a0207090c030e1e070506040608130f08030c0a020c151209120c010608010605191e03080406020f06011403190f05010603080307110c1e120304060e0312040f 74
    0x140d509901038284c010302410058940240508040b0327210700c02501d50200d031074014643c11508000d84030700901220303100300d0041c10b0100d12031340c5c0080c03550f4448034a01c006451060001ca45680600e56032502c0e40d420a0303c0c080c421010115030544601d0303040010084881049484000f4072440480410315841465090b054210315100001c800c94002c100d50001c08507014040b0780d40d5000c2c0d6800c64000c2c8082d004255055091000c00107203440d000003a50100e1010108202c001c3d0300c7c0070b0400054500f0606d04001160402800001090002001d40002d25203500540204040c5a100c241032190580006440b43c401081100c0036840010706a1100381a00001ca51108824103221651f1110044010000e40c00d00c1004030400c074103a809140a50703082c2d00d840c3d000a40a0b4010341d1580321200c0026000001d5010b281c80f101c5200300c40c1140030a001d00b00120002d0046078180c15640b10360070560210b01107004251090600304010b032501c0040c061040e052600b040e29200301e01c58244600798 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 950898174 1250 950896924 950896931
    0x602031806070305010f0920030712060f060e1c020904030908010507230a0e030106090225050a02130b12210304080307210504150f0507140c07050d150e030a020709 72
    0x400d003e412040c4412003000c01f440f42e6124a840203002f04510f03000702c0b00d0445907050041c0020180151100c2c00280d03011a1654131060a80205000e00c030b240b8852200003450440d1030302d10142c0c071416000750045000741c3c2e45595050070724802a00351040940040d0410400c1550640c010700d0b1315410100c48000b003501b099070f440518102f1284012500007640e415460720308000b81d400555070040422607080154205000c00c00d003507071108400400030103040c4e038214000b0b171b10041c6001012451000024032000403142c00f0b0308086244080007a190000541c0144000b4104100700610000c92450001d02c0d42c0c0f440c603065482000a00000d40301c1c5050002d198001c07161a040030b0010103414000c0e00c2c00300402c0c6003a080680c02d4050364010403221600d842e6038035048a102e4091280f00d80701d00d07180c5848120f00815005215030002c8803029950043d08404201ca580b10380301c0e440c141d4060982d81e00001d5000020b041140e2100380c51a01540c010460024440d80120307601046402c1da00303000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 950899280 1106 950898174 950898191
    0x2506020106080f0715051c0e07080c0d060c020705030f1609060b09100e03010e0102031503010b0d03050f07210f0f05041a04030602031806070305010f09 67
    0x3c1c0044e001342005010000c880910040d0162013840c200b440e020105203450101001180e80380705840d1240b89400225800b000041c01a1640c2000380c90300034550000201005072210008011a4030303407e400000c2c074003d01c0304a00400c8094283c542d0610700c80c03429503d6103500c00b40805001054440824002c3c92031003298243c0d0000c044003442d0802540c20080c58001070b0381c05100300b184040ca00310a986013801040d80f901c0e1031000168803820310b030040d03100304860054081d011361300d08071030f500450780e40c401c08946240d010b0600559516100360081c02c00d10410201414030811303203000c0508814402042d108900c0c0c0740e6900c034020000010100e40307640780301000c0000940103000c10300c00385450030014010324100c220407500c0d00365240d4900007a6081152034001b440940c4800b461102c405220040d844011440c0411103981030804117015443c890243e40c1c095503a90311407 = true := by decide +kernel

theorem cover : BRFrame.Cov 950719424 950899280 := by
  have h0 := BRFrame.cov_init 950719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 950719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 950719424 ≤ n) (h2 : n < 950899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
