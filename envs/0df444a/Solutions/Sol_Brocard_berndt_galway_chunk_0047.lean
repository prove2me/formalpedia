-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:32:57.836663+00:00
-- url     : https://prove2.me/submissions/82ad0d1d-c300-40a9-aad5-57d37210f88d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8273388 ≤ n < 8453244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 8274638 1250 8273388 8273411
    0x3050706050403151a060a030605030f07050111010b1c03020f01050c0405240703030902010c0506010603020403060f050402030a060b0a18020d050105030604110409110301020a02070503070f0506180105070203030c01 94
    0x40021015a810702000c5c07006482c010f01201000134035018030380c050400880c3c1122002e000790006400b0f40000b41c1200e10300709811090035540c000c0d0380b00f03d0340400c82c02c903005800c1d007206018126090401500d9001020501440402e129401e054150214001c039105072190003c01e02070f1074007408170001e0450b105c0e03040c00f041003003e11180d180c0101c440048122185504800020b880e10541c16080018903261031b800113850b074200344030000b000b900030080041849900350f4050001d9a000d00c00801c80e0042c0d0140d2401150f0041d40d001c0d615a002e5141030000030040e4000b1311040801800e6445803075135442c5413840ca52141031985411035000b1a00c002c004106104060041ca8214010103040c10191525019941c01080c250b00554a035410041404903d00380c0881c074480280085580701c20740e9030025140d010500510f8032034010f90b00009610740801d44000d00f9613000130404d51810311101182e0300d941c081d40c049141803081c04d10149016079000e001514401c1b80c00c900210704840f246 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 8275888 1250 8274638 8274653
    0x30e060a052a0c031b0d050a0f050303041b080a060c0201020409090501090b060301060b04030605060d140105040606050a080d0302090d080a020d0f05040b07030e040b0301050901090b010b030405150c0403050706050403 95
    0x400c0090082d0b012440c83c00d0140481180260303007071406c2c3d40041001d411820483c3c10704100c0c007800340214041b00f40c003408100c0000000c40c401c501480c1c48a20482035074106402c1c10b41a880742101c1503000f20701d0100401c5071903102071142081c0c3e000051500c2d584043c40d85c25180080001e462a13503482999606021503803908035400071048008001550405600003c00c0c05680000362040e6034aa000900310388415034680082608005c1000d2240071000d0501d028110448045410318104000000c07142040300100c000c0d101c00901810791032811000c114003e400126241e50320100b00b010328400700300d641c00203284240e0140d01818403101000e0002e4081001400040f082000070070080180c2c241c0c41042d1047c1942c540380101100645a0010380504440d48029515504c1c6c42c05000e02d0040541c01601e40e1803045100c84080da980344a80551070004503400740883c0c014941180344008213082503507000580c800c01034200342d141d88039649402e43c203402c0080031410015040c401c0c00750380b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 8277138 1250 8275888 8275903
    0x5090a0302070f0b0712020a02090103140f0109020303030601050c01060b0a110f0604021f0509040e060601030605091603051f0306050601081315020a0306080f010507030c0804030e060a052a 83
    0xf0854114110b45848003114051140000c0600030030307849609609180e200344a400d0030305070001c0581940d945c407814403100d001c910509050700b0348940f0307031034040304403042c00f8421070141c004014600b142d82d8203005440d107034003028440d0710303d5680b88070101e000d40c24440640b0780b44045568001e8076040050340c203868010f0054a5208581c03000c01000010f0791780310302080d162024022888021103128205441600400004d21ba109080200405131100f000400c01d1107003c3c240d03014000603690b903082c80100001551a0080702d004000018903460080d0405908004d0010441200100c4d020320300c8003c13138054004075002c41e2500305204943d80d21008543d02b003051440007002c1d6a400b6070320700b074404284104a01c0c00070340105480c008039000e61301000003440314105036411000850151802800704840c0c6101007458003849190709407164000d0703440b50b1351544a01d625001c4440070407195410450814041100401101000c4113030b08100c8952002c0c2420050507070005031100c036042000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 8278388 1250 8277138 8277149
    0x1c05090a050c0607030302090907120614090f070c0f03090306050c09030a11040e011401150513060302070609080a03050711031309050402040b06120708010807030c0e070e0405090a030207 82
    0x228204408190003007000b100d036003401c54030240d58076500e2509030060700403081c50039070069178481001f0a442d04001100c10b403005584040042c2d50302d41e584001280a00311800e0340003414440041c070070502e000c46080d04142070782005146045e09945054010780d07594022800528018030400c100a0b880c0103a58003d04405e220f107081c008520042640e8000c08079002e0204c505240740401c1507113982c0d0105a10346440b000900040e0b4080c2280c03035600800380701e404e40c1005102c0002420031b1062080d5a40070701c10014200040d442d024088001e0b4104480550789142d40302e1000d000203c21000902c60000300762004925803606400141010021801e218200d400c00c020300000000f040400b4070545514940005a03a102c90010800a200780c6080307503005000003e012401c9403510100301c1c403c100c40d03a00c00c8000e81c1c95285803521500140f00040c0030005508040c80780d10400940b032948580306240c1412a80300e1880014169001034030700300321070307001160a00305042d4144520b0020f0325 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 8279638 1250 8278388 8278393
    0x201050103030f0e0a030203160e13080405060c0c060d0516020a0201021c110307140d020c0607020405040303180809040c0305010302030a110a08030309030301060306080a0308010302130f021c0509 86
    0x1071442e10050501003c000c0e00404020100d412403240b607850003425409190050b0481f140074510600d074900c208620b00950116030fa44c00001030210700605114485554020252030900b480d20040c880990400c0030401c0c0c80d030286074010b00c01503c505010700205a0b079130801050904000d503d01d40f0140c00600414119040101c8240160340c00107803900d001c04001c100c41041c40b000707480840d00d203065040d806140c0d00001482e0700510804498a1030071000c454103aa0200000d2401070fa951055514090b40018050107a80090705d400c0c0c0c0280d510034068140441d2501602e07103441900100a03a0417980d441020a820125040c1803041a004200340d003410085941076400007556020740d81402050b400c00095014400d4540a00641c01042c123102241d4681c1060100301e5201d030000d02911002034600b07200052046c030000707813100240b601a141c003d1564203603024490b04140c031000102007a43c482d031011031801500d100800a524040700c20700103e40c0034a5956064880150800b070311903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 8280888 1250 8279638 8279641
    0x50a0603230a020904020c01060302010807020d0c11060705030a1205010501030209090105040c050c0304030b15010302070818010504050604080325020102100c020a020d050309090c0a210e01060f08060106020105 92
    0x104504001c1000955009002500d954124800010b8492405500d800c1400403803680340b0180705400075020359100342c8032402c1aa46001d41246d03100c400080c91000100689181ea0101e0182104001c058001500d0315142400ca03403076142c5154014130f034050024031948000243c80c1d016214142c0500402d01c1d0a41ca002c462038005510880e040c000c0340c2c81665100c5480d280940503404543c10b01d04580300f607a86803a42c1e400d001690810480d520300115900c240300705074961207882100e640c03640c415941810720a07444103c480300032100f0301c40c0381441000c10020420740c0e1004080d000031311000c4019591445440c241034004107000e599581405401c041e4000143c0c1c011690448101c00104001510f1110300812031420940e81c201039080741c9100c0e446c2040c0400400245007043d001e9500140c181c030b6603099041c0a125000360080003980030000400c112004036035141d4940c3c104c2e1000305204800c52030450031288298171480345010344140402c41d5080074080c40307005140390700003000b02e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 8282138 1250 8280888 8280911
    0xc010609060b040b0c0a0c120506011208180a0b03090106051201150b16021503060102010c08070f050702010908060901020301030318030b1506070b010e070e0f0d030c0c08100204050a0603 82
    0x2e40c05640140c14040c04041802c038000d502c200981400c103900801c2d05a8915641d41c400703d807021001030207940c00c1c06401c00124a2103401c24410301d400fa803003d001da1030641c10440c0401041c25a5041c3c40e801000c240002030361803e11006540104680000003400c540745c2001c0201b101c01c48002452103904119042090b1054aa4685c0845011466040daa451035250780c61180c22038500095115100b4032900700702c6014403001c1c51090000381c008104181d0701d442c3c00e546240f01181c0c00d030001a40e4515540110748598080c03d45d040c418104105402e4940c42d016051050895044807581e40c00701c0100300b4154001404002c0d82040c2152550103802c40e1103400c1c113800014841010860550a211441c1c0c99000480f12100e8101c0c65800e8075503103844003602c0e103500c03c1e201c0d6000100d1003464000c00b80782c517903803104040ca0028061021710300c681d60207850f0605201030a680303524400c800010075013001c3c8400d100c007054040d03005079075604200801c04649e41b03076081181050b01d42114800d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 8283388 1250 8282138 8282159
    0x50609010b03120a0305060a1503060303140705060a1a0406030b0402031507090509130602070b0403030506120304030b07020a050610030201021506011b080f0706020904050c0a08070509010306050a06050c01060906 93
    0x20049907141c04106c0340ea54502060710440250f002c900c221101000d40e541403a410751010096a00c02e0f6210103140e41d01d90700880d401d01410b00060314941024001c18802070465200180c2a21190100c084d042d000d00001821140b0f240e2045c4d8120341c10104201c11031a040c030540f09000380782c80380400a8240b2102c010f045920600a25001d4800c40000c5a0030903010500402c465600507010740d5502e02d286418940010709a41c210082414035000c00c240e40703030190003230444070b030b0110042d0b0400d0300d55112081140c0c001350914041d8090805504003203001403100ca4464400f40180c00010f0b403035072000902c0c05007000f000d1201c000b24181484526a44154409494850000ca418840c031507070901001603c2805181c100b4a00001260002c1242a80180c00a204119020007450750307002d906030001d105104150000950440000e20038a000e04060103201c541807500040064807080899080691500000c02240c40030a5102100c4000d01840b40076007400030b82406002c0c80c1c4852404e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 8284638 1250 8283388 8283397
    0x3030a02070608040305090607030302090f0103020408030703050d0603051606020d0215010605030405010e0607020a03020c030105090d050c010b0a030b06090601140405060a03020c01050103080403170412060b04020d09050609010b0312 102
    0x1c00300f005510105090600c54426240050f000401a07a03946c182854041c0095104a20f45c40c09401c1007892079500750f000e40f082e60110303540c03480514a026610f5504440c40c0e0b1004580741c03040c1740c1c0c3e0071020021a10404c025401c103100b00081c6249503041940180c80c0a07542500307034045500c440ba080500b04201c998150450702282000d540b00d8849188c0385014010a9a0800c041e10420b008c010300f2035400141d01e5500b6010707400b42d501d060002130a0600b81c4000f00c500c1e60b840d500203075a0500f43d61081c0001e040c4c1c0c0e0364140000518400784c02c00a00d003040d00c0e50080e03070b078841c0030000d100291a20600a0750403840900703280140040c264889049400795200c2d1610501004c10060340860217901156082c84c5440020807003903840380f47c008090b40150205a4610750981713190400100302c03074100d40c02d5486c1c65111654008041e9540d101421380301d03424642040d003e0080c021404c5150054040365413060014001c00c0c0b41100031035003141c105d1740046219a00c0300031780761000390065084070f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 8285888 1250 8284638 8284649
    0x3040f0206070206090301140121120e010909020304030201050f01080102070201080a0519060305030714030c0c06070303020d05040323070201080402040c02010b060408010501061701030201020c04092a0f0503030a0207 95
    0x10384540c2e0390f0001506502916501a4065082013806482c107620145018148c0700d0144503840207a100842c002d03402d52095070020b0044d0307c895158410740380a40540025410145000c14040f0b8944080c0e0302030f600140d5080303025130344400900030301c24482c01100f405491150300031814441c1c590002010308001800602c0107650310408141d403c8051043c0680050300b1140902155030380340780c620340d00e03444a441030360082e110507200c00250902004841244020800400b61078100d0300420100340e01c1054200d09040e42000141340c0240382d8020107100d02d0003030f200e2055034800340e08150090845581701d62035102081111100507a00f003c61607402c43c1e0107640c0021080086070090b40104030342d01c1616405040030400181030201504528140d074002e96480c410142000e100304103440080c00000e016070068441c00b0001c3c1403550003210400d006580355000c60907940008040d03481550b00c242c0001c01464010b00c04e40000f85a110020f20341580114504410480001d44415190154 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 8287138 1250 8285888 8285899
    0x151d06090a02090301060623030105010f050c100c1206090c0c06090c0305012c06010e0f190c021b0f1f02010e010c05030103050c030708060703021e040e04051203040f02 74
    0x1c41c501c0203030707581901c60425001d0000c20101e5211980580081d1924042040c44180380192070700050000040c1c034120381040c0c41c1e00f416605001c00039a15030300f0841865015228803007685d07802241030b02a00380b00c1000ca40b1031501400010041c0c1081d2003640d0846e00101e42800e00b419025a80901024a199001540010440402d280c4450590001d0380301500e82e41c2000013aa004015000c110b02c3c01d90302481c3d41c0b0342104201101651a903600b44240846424400c00040e0690344000c8995070007202607091075441c2410080400444118641402c01607101030001c2d09100b5a040103440f601000701c0d0206607244c0c013540000c640c02d04000007584001a1001e84059090007508150240140c8000070b1144190100c0010503540091100b6941c1e4410101c1c85030007414081900780c00d2320041c00140080d50b440c10741c168044d5120817081e0b486d0700804440030f0295100200904041d0501380000e01075810705e0b043c01842c2c11810403400615080400c248400240801040099070f94140d90 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 8288388 1250 8287138 8287141
    0x3030e01031d060109051807120f0201050d11040801060608060303030a2313060501060503070206042003030309072417060607080706061503090f0605040206090d0501151d0609 77
    0x100400400b031800001e080a11a000022500b00c503150011880340c000f14201140010b01c44040380e40c6e540381c43c4030320103c213485d90070b0540108080710a031720451070060512900d04040d000000c400c48050304407404c228440828103000c0f0f0403003809030100034003461801b55071605011001984a01c0047c10b80043c0680c0c519040e84c01002440740d50640d0042e41c800c4111a141c03600c500e00701080780201c103c802038585800450441c1c080c0c0240c9004808940c024146039403140d44d546068441c21581c1503040a20008032021950308200541c4180c0500014000e418680308146040755030b0a030320004110180c1c00e44070101540b060703406000340c58121905009440d1503000c01d145109900c00501906c1d400114207051001075005101115041d41e80d580e0002d0343c40d04100c040b502a032000501c1e201219802c0e0012680d15042540c1041c0010443d5140003030305070008022194211048880d42d458084400d5506c3c41d10600200910300c0c40c0c401c0d9006100e0103009640b001f8002c086611840d40c007030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 8289638 1250 8288388 8288411
    0xa050f1902060a0e1902010c080a03020d0606031109040509070503010908091212030c1c0f09020a08010b0d0b04170a0c03020c010206060604090e1e0304140406080307030f020309060706051501020703030e0103 91
    0x4c1001238058000300003d96500748080000d010354083c40060078603504100002402da4400d10900c00c4032040e080d082c504000845042001808006d013020215124100001c07030343d5607080c865515a18440d01c2100d55a40f10b8005001003904001840380c0e094002805004c06e8040150484c0c0d44000c404503031035138410988050052100d482c1c42d040555600e030200d5400c02d02c500fa071060700350b14004c071120340c03009035a044030600b40c84240c808244c01201903050315001840d907500c40b641140c07103603900c64490016007403121480d810180c00c900c0000c440300002c0040c5601405520002c0f40207202400321488d0402c0400c10502c2184924090140e0303680c55014440d00074001d031404185140c0460314100001d40c10f240d03507500075004a49018a91140051091419126260840d40280051414100c65407010b403901a10429460150301040002124a075203000080c45c00d94854600001e5504002109080340040d00e11494150b50054000340007082e0010303a080c14804007445c0100301c0c5031141c2e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 8290888 1250 8289638 8289647
    0x603070201060e0c03060103140114130e0102070c030b0c03010e040809040902030d03050106020c031605060307021626010902010c0b06030a171810080109020a050f1902060a0e190201 80
    0x6030b01c1040e64082c4032061107010144c42000318000d44090340c00344494040fa07002d80c242e4041c00e01c140381d0950405103140f80941007140c1203c50b880030001c4005a42000031140a0036607014131001c95400b030442d0807c0c0100100810440e80040078400b0340e03411581010350350850318401401c068400c003804a40030086903129081600000e5000c1c0564201c094111409000b9100c280a180c000d801120451200c80c10000760501802610480070a40c40d807406050180d5540007504440440c01809076450076503c040c482c5000406407014403600c0c0c468101030807545074040c0300001d0b103180d04100c42c500150780c3c0954000321003a00030101110a03201c080000f40303014142c0ca8020034002d14048a4401213015078041c02c4545241e224590808210304c1c01c0200703003094401c0110106040c00d005004994040d4040c00e02a513440c2061468020b00c4121504180c01c0800341e038819501c088000c02c68964107200c4190003100313610040c40901e0ba5800c00c0c1e5110003640d80c00c10b2900b0072343c0b10310b9019607200c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 8292138 1250 8290888 8290901
    0xc0304170f07081b0f010506040c020a030806040e0304050a0807140409030e0f03010608010c03020306030708071208030a0204050d14120301150804110909070303020606011815020106050301060b0403020a0504020a0c020603070201 100
    0x10040b10405d01e40307108007901801c0201ca0282c881c0e450b19203a6000140003140c070b09102a8980c2e510182541c0b004104030061161075070140304c52106000c0032a5544070402c07401c0107403070f0307607002410840c1c07500c100b920000b0540014540207900b0403004800081d000a091513078540100e455418110b145400f21740101820707400001d540d03007010302603800b0980650085006010903020b0310030030f5881d102140da841c000d6108034004000c00040c014081400c0101440c2c115141d84405032406644d80000f60310064441c0058030030045400c0340803280d03581005661500c00d102041c942c03d40d031410001d005103080e036254240c00e2040d1500014204840c1c009820400b800082c030648850800782c01e2690340340498002140075205a00119110b90b0185620340c000c050000d215841d06403c001110440d840c0001030031081d0340d290279010400e0390b070030300840c00a80543d18800e51241d1450042210607070103079000074001c074810094411210f038003141001c8050b4064904998a44410320100c3c010f144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 8293388 1250 8292138 8292187
    0x5040b030f10060509010807031703041a0f0a15030804051002030702060408010b010206070e1c14010c0f09060302040503071a0f0a0c060f05101a04030503030c0304170f0708 76
    0x100000003602c48081d42c44682a03440039581c502d0b082c1e072203283c81079444044c1e001c090980400400d025210003c620001c3d907120b4840c50305036103540b80c01104194195002d48540c11701141c85802c01c12840903603c610304d10245d030040c11142042c6541c0750380303009100b42c0c041c1a005817003488215890a00070005c0b40d104a6010344059030703550f511b00600b4000c245800340c860041c01410007003010f041c400c80040d1b400e03d00050007010070300c089000c01c0101380d0141d04101c2da141101107520003044028400d8800600c42c0342c6480440c0325501000a0610b40c181e000b440505105000600264500180c2e420989110199203907111076010754280050007800c1e551100c0c00302c0042c940411651104189061a200320400d01c62003083c404040300f90b45044802c1a82c3e045003800402000410701c11744089140c420303e0051905840e91119401d503441110282412440003080c0700c10440380104006083c2001400c0a090200c08148a407581c440c04002170205800410b24102c4600b000103244071012 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 8294638 1250 8293388 8293393
    0x9010b1b060c070507050d1104050406060b0c010f06050105040e0103140c030a0602040305010612330608071403060907060c03090509090a020103110906070b0a0204030b07210c05030105040b030f 85
    0x640024002c015510a400403146402903490008450500c42c2d454a1001c1c0c0c00100c0d03601c084044014031009020081090300e1091722000002801000c4c42d0040c00034584050010552007200b164440c2602c80c0d070b9000c0307810400c00f000708200784028241d05a054a50000b113090080c2d144480e02883c00403080403160307140c0610074080d0b003000115401070048038072920007030044603940d85510810640b0f0580c00b07099071182031081180c01550f40d650b6016030500c94001e0f0b2074044010036610071142a900401225403084000344480d084040e81d6404100d0210000c0c03e142c9400c11407a608c074407161240d072062201400d443c404160103180014050480a485402d8501d0080903042d981d41203954260302180c545060140080100d100321103000d980030349490f03d0590300d591003500040005111406483d828400070001401a07404d590180855540b0300e0034100010101d0300008103108800d0f050036280440351400c041d0803105882c1101c108590018182c0c0204c0e001c03d0800c0c10b40c0c2d108000d00e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 8295888 1250 8294638 8294641
    0x41106030c070303050109050c12040312020c010b0a0504020901020a030f0c0501050709170c030c010f0c0b040605010e1005030c0105030402010302120705130e06090f09070803030708060f0d0209010b1b06 89
    0x1c4610714007501e4440e0080e6000d0000c0d999600d07050003200c0e000e80b40c0c3c0e644441c007000342c0c0c9000300e2404207080d0000d2103450640003031a0346503540400c903081140c071070200e40d46401020040d032520520360006070408590441c40c1c8a414000030317640d41403019000f02400350724032103514414010702002c46055041002403042d46842d490003400083c00d030046000350b95170502c01c618001400500c402d003660713016004008851105005680401e482140c580c100041c560341c1c07100180b1100030380c50050780700c1c84000c04c143d4140400142009002042158421400340081200f0b640002c0d00d214034240c00c0c24855969161400100c0c06440f592511052201648040c00b1060354010010440810803e4200048603103503c3e0a84100300c0503100640e2002080020440524042c44a1504405840c0464512966a0380500e046800841c1e5400c041041075007040071504001201c0c026403c2c4c110307100008078035684d000814500060060f2002c0800202c0c1c140101c8244580c64184800c7c030f40220341c5036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 8297138 1250 8295888 8295901
    0xd0e0102070c1202100503060d0f080301030b01050d0b04020f040f09050703020312040b1206010309120221040b0307080403020c031905010606020c030703060b01050403120503062e03020304110603 86
    0x1030360000d18212041000b01c2800125612500e005020f02940104030078000c4c540030200300e0351138101900300c980c0b01d48000302540006811410041e6814416a030864480d8510308080c00c6280c0140d10081c003d00d003a01150000964000c0c20b031754002d504a82d4103110400090114000b44010060480f505d072802a45500b4050000744030340c00c0781d1007103040390110500310030000030700d004501c90030b050307110140410504076400062456001c541890001948121911070744a50301e00800d4000140c2c11000c0814245030030303507464540c87c2d0f00c50012186418508500b01c0c3c46484002e2001082180c1000400c0c00c03d4801d02c08400901070080850748000306050f403d4240c0b00090320216415031a10000080321400800c0d103510f130140080203040b6107480c40e207440001d04039804a040c1080020400400020750650350442020b0056540544070719000040c0031401c0342d406082d0030b90f2482500305c4541191070000b162044581c0380b8015881e0b449500e031208044180318081030b803084000c02000803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 8298388 1250 8297138 8297141
    0x60301050a0b07030c081b0607050c0c010e06090301060b0c070605041503020a09050901090212100e041511040e070e030109020a050d0804090207050a0309090e070902030916080106050415050a1a0d0e01 88
    0x44100001c048d074029455182d401e403111f102e042e10102054000000803ca20340c02503404209890b4040c00d203518000301c103000030b0708603a5150003c54411070040b80d25900c0c018200040f5001c0c1203d805d0080ca81410035981c52001111038030030034101600000e98490040c410703900d0000514000e0280451545c4941081010f034115203014031a030134420307001a1001c4038056405044440780031034010691243c0d00c800c164040701010354400703aa143c200d049040e14aa80c010f00c000c1c0090f00050400741030096000f008040d42c00d0040b40b10368100030360342015070b45199020b03080300c03001c6800030750480240c6040f80c1903015603400a00d10520100300e0505105010a00005091181c0d407014081034031910403404682040000e404281e11024092120003520380c0110303040306064045452120310040c0b98100c4031259002800641d4440c481040b1a08060140001c040e000b241c0c0e0340c1c40c0c141418007180f41c0480c81d120304103c65602201660446000300120f504058568006010a2a00e100c4160 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 8299638 1250 8298388 8298427
    0x30302060105100804080901110a050a05060106080f07120506030a0c2d0602030a030b0409120c03031a03030706200f03040b010e010806060108040501060f060c050c060301050a0b07030c08 82
    0x14010f82100000184051040ea90707980304a910504550501c14244011a5541041b040f03691481c0b0400104801144080002c03041e01031045000301890340c14200c00070300c46da5001d0b11741803001a0207824003c009070042c5d61800952003541000507140d4403103000925201d030803500a4071300d01e004c4001058079101446007407850f81c0403018421640030a56012041d4409620800c40181c0007400301c907210034030a4011510604000b0400324102189444841c25045000003c001080b80c1601840806030940103845d14440c00200b03201070008a0307004245c40c0d101d0220024149640e58010f103200203817480d8248103841000d031455403510351000c80d00e402c6600c180c8003a540e450004000050300a441c04025042c0c4460b58080c240c40e8072064015a1001c1c00944122115501d514001c900c050864080754010b007050303556480c915515060179814034550312901c0340200820001030107951100640305007100d02111989a88030060f080c2240d001c0b102c40402460140005582060700d1002034070702 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 8300888 1250 8299638 8299649
    0x30302030105030606030d02030706020706090204050a0b010206061c030e060d050108030a11010504030c02040203090f031602040b0d080304080a0302040e0c040608100e060f0301060e31030207030b0c070c0303020601 94
    0x1d1300c064985000305555010702000d8000180c2c010082480040d030b5680160410714803c0e4404900b012441e400074050703580032910030201c0c1c4d83c1d54a00180ea0340c0d0400c02d1a800200c2940c4403080660549031a04104d400c0d280040c0a01000200c0841a5261141240c481c8030741290300304910350b1038810003502d03903000c4010940090b251600604421006111385401554151242000c450342c1c1c2e402c2c400a07400003490045540101420102107007028801000e500d110740700f201d115030015204000031920030380d00035030040e0340c4d02c0130080000c2d0004003100e810540100310b040d103079018102c0c21006841690040c40c910744285046c0810940c1e1400035106a03069a21440125a629003c401292040b0f100d0b50070240c101c400411894208401c00704080f55000c0c00208605496080d502c401d000c05a8200d0342248044142060100c02101c0c00c09181542c400c008000000c0c03501e00070750f540010f000107000561800049200c00012504403091035034000103a04001d41d69013000781d00c54200f4441c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 8302138 1250 8300888 8300893
    0x6060501020f1f0908070b040b07120509030406030e21090406080105060109090209040609050c2107020d080a0b09040c080606060403020114090a050d050609120708030403030908090d03030203010503 87
    0x941e000310000f2980705000d0711100f24442c3c0c400f0900e86060090683c03008180c490f480b003003280d5400300e1514485148518012a040c25003410107620085c585e5820060070300c1c49a15040501414000101c00c03681282c805103000300b200c458103882941404055280c180d130300e2074051070112003020040090040203074120307410840d195032200031a003610421140503000465201052000851300d038041c00d101d1001800000304561242c4010040b66400d581c0d00f10b4500c0d02040030700888030b2100245000c00f0b00b007204103007107042600001c0d40e250160850f480c14440c44100142100907242c2c0700850a0500601c000461f083c1420920100141401200c0060207400001001c0342410341c00c403011241d0680d600100d11107828410b400c507400035034280740d01c0801408002490382d10141c003040100d010b1b0000d032480d41000c80c0e0952600d000d01d0075030030b9a02c2d0180130800120b140481900d80c490b816040104094035186412040e51083d026110b500105141500741410352690146059a01c290308 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 8303388 1250 8302138 8302153
    0x20f040b060406030f23040f06020c01060e010305010605060c060703050a090602030705070302010c02071d0a0e0609070906050409080301030807140f070303031104030b010312050c0307060c080f040210050a0e04090606050102 98
    0x200280411046c402041030000e00410b000401182c4200381c1503000b59001403c1550041c8451b096581c15400810303060303142c0006100b0302c40d00f03215500c000d0a044408915051240d0466521013400910349014190f13688001285951140c000c02c410660224045541e4a4003120181c0a5002200c0c1a00198607040e15071080701d000083c04030607151041c84803010500000802002d450b002032240200340d8452007001d50307005040041c41e0294500c44080c140082c10101500c04542e01341d404103118505003000311f800719048804903030550781c00200096895091f800e002c01d41205000d5044607a01c41d80f841e2041505011800e1800c0e07030b110342da080c80503d0f41c2c2420103040340190701003d0181d034205001000012540007842140360402c0c10704908019901c2d40ea1030954002c8142502d205484150b840c508680c8042055400080b10180c4070351414103802103692081b01c2c40c500c0701072010000724482ca01c0e010390b00f0b40480c400300074014000102c5900d0b05070302414151099601512403240c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 8304638 1250 8303388 8303411
    0x30a030f030f06060504151b0b070f0206010b0405040e03120a0506040b0307080d08090f060f340806030703140102040302090f04030e0d030c05010e0f0706050f0403020f040b060406030f 81
    0x181608848451782c4035420142042e42070a00d4620a9100070103000d00744a80025441c4170000c0c03030022500a4103402001e103800c40000c1c01d0741103184042011900003400501c601c4044405803411f03100141c40000350020382c8409546107129011981c6452807416003002140740564022a01c10001540c09010950000c0d00385039890b8054000c60b12150499010706209504c00c3c280c1d603500640d224200d91100c0c400c0408281414003d07222a031403082c00034200400c4c014103090320a2140301162800000014035040c844c1074104002c3c00ca03040003441e001207001a90201300300d4010f1500580300f903012a0003084041d000394094072040380142e00400014481c6602c126070240300b5509619110301110b504010482d80c0b039500c0004405104c100d020010109038244102c3e02003102d210000d007181c0020303002c81d91410045a01800c1000020014a0908a1003034140d5003200e0381642c01052050407040018003901c0f0120416422240215000600301c0c1c1c5500201c1d568080060b00300300c800d0302344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 8305888 1250 8304638 8304641
    0xf060305070512011104080a020901060806240408030c0106050a06030b0d0f15020708070311030c0d050c0102090d0f0303050f0609060609030a0203030a020c010215010609060c050309030a030f030f 86
    0x912018000e508608800c200a0400010203412402c4500000501c1c07809174282d0152600306422000da20340c44100494218182a104035000d400c42b814042401e02d4101c002905900407901c1208080c2d00900080c1c01503034444041d1006030929a040da9110383d045100b250090225200c1c0610441448200103280c500038864160401005001c40c00400e03010380790102e100c0500102290b40fa1001f894101c1140b40c02e10251030003501c91400c1940e10744143c00c0080141e6000088174000c0c3c0c00410540e01c011000148440f81910582082c980314170150171600d0083c0200c22580790422400301e100070800c400960100320541c4661410880307138948141a80d610801142c1031500f001c2d412020403114904032028008c0440020119814280310780c0c086411604030892010261740701c224400401c0d81c042c0310001d0004c502c50b403010003940c034019000303010040038801c0500748a00c031024030043c01810b0045030801174001c0c048450f541100c0c50014410410b946011000a181c82010200320406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 8307138 1250 8305888 8305901
    0x80f070b03061f0e03030a050316030c080a090317090f100c090603020c01020d0603080318060402090402040504020a0308070804170c030703060c050d14040302060601090e01030b06011103120a0f 85
    0x607110960700c086910300c0c160f08100c10101c0e80107201c4440c000c0c80c01590200010320013610f250350b0701a160304051b91080e0b0712111082190040c1418040b00c1c0540795440700e44039901c00d10f10716000c039803d84142402e6a0a00100305e80701d0000c03c007241003104000c6c0015049032400d82a0341103d04a2130701c2c0300c0c01c800301c41c80c41c410000090155581084040e201c4c8c0c005d001000c1100d00018503003400e103080041199565403007101c4148000c0100510114440030801130741039050090b04032807606d40e000555001c2d0081c0000d00c07540e6150040350554680c0400c8402541c0e10400312076481c0320600f130110945d00140b1414400c0900840c0c0c5800851021502c2c000243c009001085900d0071903075040042e089004c0d20408114080c80b540d81c1d581041c1c0164450f80c0c13100344455251742440d00f402030410f20000c101c0d9061117180d007420003213604080c2603c0e045036003000c10000261120001202d19035413100c0880308070310010828030a0f00e00408007180c001c6000040800c41c00324580004c2055808 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 8308388 1250 8307138 8307151
    0x3050102071103071202010c210306060201050615070f0f140a05061303080f060310090308090706030212150d08030a0518060c0d0e0102090d030c1a010e0402060c100501080f070b03 79
    0x910f0341c1040e00650007081c900148e18841d0081d101080700f0031807140f0700760301003140307a100003500c550040210a8084c440c1c6900040f003900c420504082210484c030351031248901c000e1481640d00558424800a101103d4583d94401a009407503c8901802d9590f25502e030001d0310300d40581c0000c04d00001c00c002d076843c80203070f0684071030003241e445114491012200400391a0980248114901001218494500c02510a0312402c01d2424954601c0e45000f925030005028944104071034824440e07880d19440c0e100d400300c00ca03030f402c19820314007003940700c24bd00c4402041c81e8408000c0c00351000c881e81003184104601d0030600381c410110f0f5085513944405071840d2800e02010042c076480e81d650f0360416040c2d822103000140c0303019400c3c4041410507180303c50503400103c891039140c0400050140b40002400e000300d4891082d4184501030300e8144010704002d2290a0000c2c08a01604051040b2412214440300401c955a0342d800c0d22911403100c2d044083c814012050b01259004651082c1d038090003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 8309638 1250 8308388 8308409
    0x9090402090604060803030702030a02060903070503120703060f120302010f111b070302030a1a130b0105010305040f020405010e061309110d02030304080706020c0a06170402040f020d0203010305010207110307 91
    0x446030340030701000c040040c0000d900543c0315400415800000c200450142000c0d5004564540e540c80c1c000f81880006000443e2a070801c021400129000005480e200e50701c1e10141855901e550400b074000340000d034495885a20070201c006130b000485100f21080900940003480420403031001c00c4211981e00d42e02d480c07600020300140c0c9800300d10b04124200040040200d440303280e1641c00003454001c00040c122a01ca40e190001c3c0e1000300800f25441d0800d00c515a508041c0049a94452600005010741c40c10507544400180a008640318060081c54000e0010045941c40b0072807500c01020403600c440c06040d03c004003418141143c0705191245070400f4281100442c528104402856942420790313141c401031001183e00303c000c1c410b000040c8955001001c00110060910840f44441c1d84143d0a0105148850b02540d1408070182d900a50403500000d400a0850501c8004e000d60a401111540701000100400605500406030300e4003840984400d10319440c205a550220341c050bd03609003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 8310888 1250 8309638 8309641
    0x60305060a0e0604090f080307090f0305060103030503070306030609150b010c1104050a0209060406030509120403030806040914010908030109110c0d080c04050d1b0e060a170c040501170607050909 86
    0x100c1002c005030400e500a00110b510076850700c50040c08404114240c401c207070008240103410341c100c081c10b40246800600080740510b192641516220144000b038288003002000036481d41c403d034080005950b019000b007010303151038104460740b5002e0750036103840d5900c2d0481140256000d8840640150383c0941e0700d400c50701c25901400f01515014146002d403940030f2202820603919034010300058031150303070001000d140441d10240303044501e00d200d0b1802d000401c03051000c2070b0302001c925403040e000c1c3e5000c00c6c000281c3c60608066941d807020b56030036500e040700070420400204000d604a0b075071140c041c0603000c6668030580c4c00388942c444c8203079140d000004100c202c500424020764024200e01c0100d0406555002190f04100f036004201d9042e140d510782c6481c10a140304011001d0000c52100c2c1e00203103005804224040030380e010715a00340d9010014070741c0c01d00041080c4482040e01810078010b40d42d659052140742c002e013401d031040314080c0344001052350703206038140e40c03400c20000c1c12030311903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 8312138 1250 8310888 8310899
    0x5030703030509030a1e15050c18010c06150603050a1503020907050c071202040509010b01020c1306090213050310020f03010506030606070501050708070221030622050907050406060305060a 83
    0x42d6200c110b5a030b4150090421900c0400c0500d120605141c1c14258915964146c501e80003030344150100f41d40c41018034202c10f01410310311041c00c3d1a40da002c040140144640340350016180b02c0710060006080b40e042c1040f00103802904602c00b412948180c400f44480d845000c88a400d4401c0080000f404200c0c0c8402007004d480c1040c01e680c0c1000362030501e00c2c500004d2590150400842da08204061202c3c10407a00c118105807013a285d12481580c000c01001101c0381c0000d45414800c03404034840c240b1854070101c2e02d40103510040c000d00d40e1580031980d990309105e501c040b0305541e11480748a40102e0002d41038115090085803640a0441d42040c0307540c0c00c2c0302c200120740e0800341480d9017090703041c080f5000003503003449950b004184548075a0407078907089500034a0980c0d014a9120004260344503030082200031410340307070072160440d05480c41d0715030600380c0700b81e101070380201000305410300c0d00340300b04a00c020500c141a20030544050007042d8175a14144d05942064610503003002080e8000c00a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 8313388 1250 8312138 8312147
    0x30403050a1209032a05010302090f090a0e0a060c11070e010501030203040303020d05041a011e1a0c0a0c030303140603030a0e01050c0102070b0a0b0102010b01050706020a0314040305030403020705010503010503070303 95
    0x102030a583c14000c0c3c02544035207600080b40c64034800511011040c1e0004116001c1ea146028004e10091905605c0c2c002441d000c81d844120390714440b40201d42c0f1501240841c40e06d0f400c918001c404106c120390545442c0d0402c1000b400800f584400495103d901e5038168071b0010400c0c40c103440044544403a982d00e0280110000c6d8001442a420594203104a601c80909800369074060350081d8141c960312040c1c622041451007041c0c2c442035420000c0c0c0b01061440819a840000322040394075030a107802d603942c04500302d52007501c804589a00985d071800080050840441084d64001e0307404101e22106014003c0c841c190035201d0560550081c021000e03400d00c43d600402c00070606141c22414020144030b190f0a98100f01d85c125044103041c0f0130011075542510070700c00e00c28400d100034005903841c040081d16500c00c0000244c001303500001c403035582c3d90003034201c11120503007d020146140303002d040052281c0c0007540c0031001070241000c0003270950311038001e983c180d8070000d029091980c41e40d6400e59 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 8314638 1250 8313388 8313413
    0xf031e0f010e040f0605070203120c0a0e06070c03020406030302030a02120405011b0c08010c120b0d0201091e0509040605060102010b0306010b16060e0d0207060f0302030705090f010309050105040c0f08030403050a 93
    0x1115150004184d000140941c0141c0780105a1500190303110310301380e0404076240d10700811844408006005212103240d00040c00c510001d01174a0389680c1d201700381031080d600d40141d000a5045410b1600020030164004002c1034a54400c1e800d940c0440603606003814248150b106581c0014260f60007c804c83c004290784122540c030030b107110788045955601440c2581c400c0b014180108405078a42c010707180c80c40c003a0045020b003c88505008404070f0380060300f0f040c00c80c041d0144004488070100c4c414250810303204007a002c001c100c0d2030345c1c1c9001c3c901100036000483e50303d8015420300c1c400400c1404c000901034141c0d442680c1d19828500345060103801e42001510950f80541c039451009041e841c1440f40108801c81540030f410900c1c1401e202401405502c12014200b5104004201100fa4040e003540c15621040325065800c8481ea00101c024083d20303c40500f03154038080a00040205601184044588000c0544940da5841542c0741d200d000340d20002c1c001e0381000c2009400a021140503c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 8315888 1250 8314638 8314643
    0x106080115141c05060109080312010b030613140103021305040f02010f050d06080703030809060702031603090504050a1a03030c03090409051606020105010f0504020a02030d0e120f031e0f010e04 85
    0x2d424000520503c080d1620300798038840c0c40c04c0da10300500c210755034014210070141c800000150301e0031001e42003080102c0380510030407280030070110200b0080d940d1109950020a10114280035210898030029001d031001c0c8800c920841680204100000c014060340d0b216a800181442e55418141c0040d160980c43d030000d02d0800504105e0b100002d5840d21414024101040c0180341c042e0543ca4040c103200ca0141c010f25030382d4084008c0241041d0300004540c80ca00c1c00d607541d907140145510b400c0e03070102001c2d04001da000b41488100110b050b07540d0b12820036500c14000060050030903209254984c13180000b5040d15410801802c2040e00382604100035943c8503800326440c0000660001075075000e01e4004e0360050f51a0001081440c01000316400603050031a811440c1c214079510180d40c900c40e900d5070760421038685030080380200013030210045011500d45403030341d100030041d42c400e1071742d004030f9080f41c4800c1d21f00c504071607a190100007140304401d074045040d4a64200341010800d030f203004108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 8317138 1250 8315888 8315927
    0x106060309051c120e0c1c0209010b0a18060c030207050405061804020f0405070c03030b010311040509090f0106060504060801150c080f04030222050603060405060a0e0715170106080115 81
    0x528040b14803d11845d0f0502030600017418031402980304005103026490010300b0790810b880d50039005039582c000c42c00c0c1100c2c0542c009a41e40e00c150a8260303500c1c0f45c400f03100001b1000e0500c000640a0f084080088094801e130f09807090b00e0740320010807040760820781d14203401203211388141c0800d0484544407030b0000e0009010002c000c46807400034060360011180300c80001d80c0c45840b0000c140d014002c010300702d0400d00342403218040c5080300c02040e024500c10305104038610380c04946042c1040c00100311100d0000001c0c030485031154000b8150b984280f00701c9002401600000801c911400d80118844800303a55200004c0080d442c0c0d56048c4d0840d04224201c80400c00002005030f07107030051941003411141a40f2464510b030241c060489000810f164020f4105804120000e03c0200d80a41d104c11400c3c400210000c002d007049160020395080b41c0b05d007103400d4a4120001d5003200b4042207040003172013407998507030300c90740111440d40382886800100307007a056860003003d000303140152100890307100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 8318388 1250 8317138 8317157
    0x5180102010f0c02030405011101050106020a020103020f090306100812030105060a0e1914090a0509120a030e0303190b030318040f09020904060c020d020a020102031204030e12030a020106060309051c 87
    0x8142c0c00c6564514a03540582c1c00081c081042e9604484003202d0242d01d00002c01207507140a40c007079102c40c0400c2c4024101a8005401d58609201605542c0d801f403000d8100c420740d1901840c20601c00c43e080c050741d480f40c410790300401d542028100840707040c0c640c054141c5041030a200805c0d12515480760301698803c05070388002d0107800c14001c1400040440d8400d0038003480440083c401180341c0a065010214180f03c100010000f0001c0c1c0b20400f0520080303000e550341c001d0403084005040c0c5404031601e5000000030f0000c102030700320703c0f00c5a15003040c904212a602c0740341056074901c80d4001e070341c0e6096407400c02c40c06a480c0c03c0e84951090b0100d542c000c038000d41d03240e0000f04c82171802c0750200c03411a80c0e04e21803d481c42d030411603509080018001025016050b80001c1c0d968020103240c0c50410301040b0010b403c052042d8100d400421018200340c2c0d503217413520511902d03500143d105000561901d940010214400c1c0101c400d0160000090018031110f000c1d02411410460004410300000b1701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 8319638 1250 8318388 8318411
    0x70b03070915120b01080402010c02010819020406030506030f0606030a0602030403050d02030117010e0303060a03060b04020412030203030a0c050a0f0e010c0219180203010302030705010503130605100303020d09060518010201 98
    0xa4003203a840665400204929a026800481d08a4180e640c1001b00f8a02000010b0341c1155498418580900780307901c1030741d46e4100814064591480b120607040c00414000f401d15095000307240100c00c100c058400d5411100e0180f0390310941110003560551040762540045100c5500464000b4040d28220345080d100c1909513003a81d10a81c0710842d03024468803000b40782c0380c2c288510540408920040c1d8030b14100301c40060b118003000d0101500840d500c4209031000e076110b0341294001c01414408094030740701410041d4483c1c00495501071f8043c104030080c01d00c248102c0845948030215281e80e14a4495014100c1c1c00d440180d194505001c0900d8411005d40e8a00200c4402104001400d9843c24100881c0c1050b8000303416840b11224018070040c00180d50100b80070059402c2845c001e602c982c1c80e103200d00c40e202000e40c4060150b03803408042c014025a040c01030004d4034082e408403040e4002130f5404440b0307150707140700d554002501070048084603401303290110a507110503c00400d0701103801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 8320888 1250 8319638 8319659
    0x509041e0c081501030201080702010b03030f09060c060c130801050c0a030b180108011508030301031e0c0b130504110918070203070501020309100c09060203071104020403080304060906110c070b030709 88
    0x441600c000f504565004208560703008036400da209116100a0200d106035a022941d80e0169105640803842e000c01d1040483d1556000d548088105204980c41e50604400081c101c1c2d01002c182c01510480c4480410b09180501911f40140c48044e60545015101d2801b18000d0400d00c3d40e6540c440401ca0340000c004054000e01d40c040c00486000046006400e03c005a40c00910350140c030352034006000400100301030340f41190b41d001724803100402002e454031f0040c0044810350070950140704082020003032a6010002c1d881034440541e000c00400f5011504503550707000d101c20b0164016864144c50345540800120250000700500482e0304200c141d56455082e0b8204544000030f580c0140c3d211200e42c91f0307a028110a462445c201401140c0c18040000d489120b450300242c140001740702140400e4440d541140c3c02507400501c1c050f160b04140c9401c9000e04298842511300720708240151504c4000300381112003d00c031400041c20198507040300990590001420041405003100c0c0000d550000e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 8322138 1250 8320888 8320903
    0x30b0a02160b2e030b070203121303080a05040f02040902120a140d0f08040611040302060406022512020f120105010806040c0b07150504060902040f150509041e0c08 72
    0x2d1015900340b480d000c0c1019800080315050b000c0d440303842410343d00da00300c00c000b2218140c0e038200b03000d16040c1d039880310203a1649c03180c00c00b880700542001d020007404000c01881c4051b800e01c03c0e601e0460a440d2114510f00f9510217032409410b1207407600c0000c00500d419405148c0491004c4c0c440300d154603899845500b850691203003624980e000c5d00d000c001d2030710300f1300c40460145080d05000441d406110002403000307000400c01010266245010000f4540060a036402954024203051b03580b515940001c0d2240078031480e6601c150034002c10a11128805e11042c2c0c07d880c90200c003130341c42c480c0a808010040d04c5084081e40c00000007000c9446100c4203010f01406090306600524090902d85840f01e0800c02550140c0103400341031200d100001c16922840c418001c54040100d0a62598101000108601c0c08005d5206107080007643d540f00c0550080c40050900901107181d141e6110203120207488101c8000f8a2000c80080701c00003007001203d00c542182c05288001205911407400da8a080c40c4c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 8323388 1250 8322138 8322143
    0x20a0906030c0915030603050c15031303020708060c040305011503020f0d06020906040b0a0906050c06040b070e0d0605070201060f030209070516060606080402130212060f0303070606090606020c0102030406020601030b0a0216 98
    0x111b8400910502c141000701c40306010081d240e010055290081580c4180805040c1d11802d8104a0b42c3c48140f610030001030000d011403205079051420000c0d5800300c5540315210403101c95080001c2444d43d2440410000202c907000303800855030f010751604000302c04034049000c50346075034280500203c50b100d502c06440601004843d042d42c84100c0c600c00f9040700040c1d445101003010403c8103420429000c20042d81040d40811010340c6501d409005448003039942009940000143d06501c05000300c6801c280e00590f1185c008112071600c070307807030701c400007c1c14000650811110008a421a44035800034030046080a0b401c0308401060b80d12041650ba86521000000e0920018403055142c01c04100075441c0c0c0d0324900310316101c40781560040c4c03040b000f04818400d15080025240c41e840520490303107180d07804042041880d8803014007000400f201d0003040010f215030002a19154000421907007910742c160000c040c20ba2950f0307070340310051030018411512140c00f84815031640080080981d5150f1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 8324638 1250 8323388 8323391
    0x70519120f0302011b05160807050109030e04051b0717091302040603050a020c1e03090301060815010602060106021504050304050904030c020108060301051e10030c0305100f020a0906030c091503 85
    0x925050007825034070309203d004070001754a030700e41d980300d03401508030b035243c600c2d000d48488100780b9420004036074015518098225400c0c18803040c03c05600903590400c50b42e04603820000f9844400450a02c0b8010420301c0b03d548008110380404900f0300380e101c080c030034100e014803850040550b01241e00305050458480d1015000702d0140300c15a010701940d540b200da441750442c2091080c45100f03940c0c6c10044000d2414000b2402d0300d06490030305008844000c0c0c8040c00038851603035508501503945000c0045840c0504588002040b018070101c2c049048482a5008001c00d881c100da1109071010007401c119000e100801c00080d0303644038800c000344130300d000f5100c1d106200d1131030001620400c0300408c654031a0f45400100020701044002043c40070010503d00c240700e035104604603d000340241c001516002c54110008200301000174980484404181c040c011031203014980c001ba070242d03003800004208189424032202c0d110ba030000c0103061540c030b840c0f81c01d1070351880c44d6501150801c5840000a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 8325888 1250 8324638 8324663
    0x1b0a0804031406040c03030c02190f060305060d020306010501140409050103060c0f020f0d051e0c030415050c070e0a090c0801020307030608032a0f0303011410020105070207051912 79
    0x1c90761400c103000750404029003d285426543c0019881c140d00000b02400340780260300055454003035441c0210010300c58800480342d2200d103462000011031003258006410200091154281441403002e650b07800740c020000d607400c01c401034601c1808186103034aa18020701002525402600855000703500a440010341c140c682d070401400c0001000491096510191059030080d0300011513003003111003032074050f0300c901d09503180250740710100d0404d110001e40403450700b441085c007000620846000154205222504040c01c0d141d6015020321865160407160081125504020358903620003411032000034a0743e45a0344010301c0280b40e8100c440281e5010040202c150f4243c42240003520042c2c00560030a660303021200c1141c100c00c500c180d00d00d042c01001100082c400c01204031582003c2094940307941c2c583c8514a40744805050b09481424440d20842c01980103108940c004d50050f809052854100030038490340d080301900c3c1d0603404020040c0000c001074500b05604107184601d0003800c92 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 8327138 1250 8325888 8325893
    0x102031207180602061009020d110408070504061a0301030f06090204091208070c08160201020106120f06060f030f02040506061e040801060803030f040f0f12080a060801020309030a03021b0a080403 86
    0x54030b525040320042d54005c000f440304448055001104882d003546c0056a03c00044081e84050004900c40001500340841e000c102c4081c040740342c006030b0310103481c2001041e640b41807003140d5008803551049500b90030070060022860f00c0000024050185030082881d020710350210b01203400c800710558025401c0100c502c9229070104d140b075080713501031501d0500b00500e5100c161042c0304141040351000b01c888190021139000b03400c110020000c84044004072413035410321a01401006008490701407405030003189169400224005480e0800c1c20001c0620040c2e0074000240f01c050142903000006200d4690009041e0b03c07848940d6280401103903c541c41c1c10015800c0d1307030851b0001841034005000704240e00100c1140640d005d0b8100080000503007613418024030040d82804040c0896207503c8900003c3c54112000780d0007545115010070609540f9800a4202d00082d20f172002d503a00104900d00c84184240c020708074609808044480550002a08034033340070304038400b180c4054010600300306 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 8328388 1250 8327138 8327177
    0x308070204060608090309041d0703030503011404110306010503040f060501080304030530030a020d0218120d090501050d150806090708010504050a060e010f050405010b1c020604050409020102031207 87
    0x30151130421450608115070070341d0300c0e40204140140601c3e0f507070024165184910300131010280e404002d580b0802c1d224200103082e64000d02508084c4405455560a241004c0c811207110341585001c10781141c031200011200ca070f10182069546480010000c004a02c0512170706000b04004d00045030b9681c03440c6002801e042c1b1600c40b00d0f0000350000b082c0429040c02c8082606c4074601c44403200e58039a208110a4020b0140640f01c03500c0500c08125440a04000d00c0c180040148c1112068520060703d480c1e5540c91078031412503800100441c40c1001994011405070150507140e00c0003241c054684948480110070661205c0140e40c052414002c4086051022401900c001c800910a610742615140c0d41d54612080003800c0a83d200d0500c520940294401c04030520304040500181c203185c107085019250b0412151704c1541d2108020541001e01c035031200d800c0703174042c1190341070501e0103040100034880200160f055010400c0103104000b60040304ca4401c2609850f00500c0c0b4541070f034001c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 8329638 1250 8328388 8328401
    0xb0403021e061308010f0c1103040605070812040b0f0906070207090e030702150703030e0a030f0806010c05010903020a03180501080604090203070308030a020301230904060f06050303040b04090e030307050a080915010308070204 99
    0x606202345006001513008010040f64180c500d10b04045a8a005504d402d40c905e215a030085c001032103180c4144010071548501d45800341d22200181e8095484001c0c0080d11a0804c0c2c6010000d644103640411500405400c440e015202040035242001000c1d0040760040780605901402e6001c0001c0e03550400d07030544114503c011500d801001c0f19011030764050200e481255100e010f0140c07200018440da84101c40c2010815070080080c000c6c4201440c000c0d56860040304114046034403400440220f81c1079054081c01c0394030594541040b520f0f5941400b000380a03a80c1c06a070507000d40a00030001c40c0300007008602030049030100603502c0d803400c4042c07881c0600e81180900400710003009550b56076516184160841d42020f8002014a4a1454800200080d51041b0b030035000203d00010321a6858003e4402c07900b03980c07024000c401d011450280c9910080341d048002c03440600c40f078003065225019055015060400b20b40c0b034203406403030403058480240d00030ac42d0108005415011402e01d0302504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 8330888 1250 8329638 8329661
    0x30a0809030f12030705130504091a0606090a0b07060e03040e070e060f0706020306030703051b1e010c03140f0d0c030b030706090b090f060703020105100b0403021e061308010f 77
    0x1451402c03021019a160344c4405040013041203808143d000005000700c000d0700003444000d01c20001c881d0030b46400100460341d0160030001c3c0c864840081c14600b0044221803050f40010181710b613a600301080706072203030040e801c252011a9141054615940c0400040c0301401380e14051000f2458640b0004000300340d49030708070707008400502075840c9050084054892469000d2805a04c9544034004245030005c6544040c0c21489010304250750f0021001342d600c01504280e90044c4100c00500f1004203030111503140c0f40c0001d01c1d0f5050000868455840c843c1c80d01c812001d9980780540c00da22030380858004103440304d01550b840208500d40c942600c1031148079201030300030f071941615000c800361102900b44240d5202c40000900740d0016070b0b4140041581c0007008010139107408084c20001d00801c0100c1d05480060007208020808528a105403011030350700511540c4d00303d03d00c01c40f620703e020103200c0e440c1c1c0128041c001d84480d081390400080180900c80000030301c4154404104080c2c0703c040c60203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 8332138 1250 8330888 8330893
    0x15010f030b0609040f0b07050a110a080904020307171603061d0105060a03060b04030b10060207080a150902060d0c0f05040501090312020304030b090d031112070e060405030a0809030f 80
    0x400004540940d0310342d02402c1103031101e8542e030b95410300b40001d00141e00c00030481c00642c030070490601e8000e0050090b000055a805072800415441955210010300001d44000000d11144640349880d400840d403055151500c020701882482d44104001816120f40b0b2107107500c92010445c495051207030300c0042c001c510950b6000b0800f00110f405c10340c010700425003c0c55000540800c0f0300c0c0282c210f84014420300051070b96642d42c9007040707407490b04261103d8070b00b4964030340c000901c640700040d00400e460384032001d4914215a0b98583e0750840c511008558070715100c200c0d0201598641e000f80c14070210001700440e2540345100000d00f4684044502030600c4402c4c00148a00e07603200500e031055940c4003540c014100c07508030091703145010700d5100902c4982c4010403c202d8050204400400d00c05544050080d030015005000c001e02800f03200c40508280000003070340051040c12034081e0400e010301000e03d07080e10f139000300741000000e80d41920520390003d1201c42d42d0408022002140303000358003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 8333388 1250 8332138 8332169
    0x3050c030708041103070f090209041107081206031501090207210e01080408090603010602030403030e0607020f0f04060305061311090105010203030133090315050606040b0703050906030403021501 86
    0xc003900c20400540040c25410f01d601300b000d07039070f00c08100001c007408042e052200210380c0c0e5003406020f540303c0c142041c0120704080501c5401da08600c20742d5240c0c0c0d4001041e0b42400d4000004c030b81404d07001015503500d80b00b210800850203600b40e0a8a0190400040250b43c130022400d002e201d803140e07102d1503028103040e80c441740c02c1350758042c8a80c80141c0f002d1030f1423103403612241003448090080d015a00c0c1d20030070000001420781d400000500803030340701e44c0f14a07413003501ea0310811606014411010750448058088004503142480b05000302c50401000000d10300d490751145890880204c0b501c6140c0c0c070000c90135a0034010207448440007541c04507010000c540c107140000792030740810710440410407003d1240026101051505143d00f40c465000180c0202c108a8010802d1501c2c0c1f00c2661031004411012010944500545205c1c0f40082c0445141c0b518064074900d85038000d4009404107c4280250480c4d81c0e1040021030145010340e004101c4e801031410983e003821810380c80001c0e204000f03035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 8334638 1250 8333388 8333401
    0x30303140f070f030603050d0e0102060a0204080a0f0201050c0a060204080705091b07240c0f02010b0307060f170a0f0b0907020c0f0105040b0a020607030b030a020306010b0d150906030303050c03 85
    0x900541d0044080c5400d0a580342c000300e084e005481c02d130700700034128002c1108814511307501185079031130380c80300b40c0c21540d183d2110701499080344031740e000d040c0e005c0d008142c5200100302c5081196108505c1850294034040440a0183c2040c810010440301550005000c010b58101085988040c14045805c24010300742014143c036441507000c03281d1b107030800c041200b40034040b841001d81c144c1c02c880b89100030340d5244002040e008158241e108000304003018000106144144650148403102130000c08a0a0400100b550b0036848040c00c042000005200300c041031017040092405480c1d800340c08103306c480d0100d000140d41007000854007443c0711104000f04590700041e13482030381c2020780d00395844064440040f11785202c1da07000440600c0303000402d2005281c3c00912a4400c1101d55010000d00000c041016203824880c000654154420700051006402400050004c60350f6040c00003800d82c0380e21142440a88590302c541a0035544034001c006041d0103006880d4070070202200d09285213400d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 8335888 1250 8334638 8334661
    0xa29030a020d020613030605090601060306031e050c06070303020702030601050f010c06020a05040b1914040503100218030d020f0c010503040807060c02160f06090515030613060308030f0103030314 86
    0x14140648200d020340b255000355140d41c012034540801c8481c0030010903803241451409004255140380c12407188070700000381c5030302c0380c0700e09801d4a51056448080481c03510000100914120081e20b0701c6c041c0d842c0f0810b031990340d80f0040c80214032a44002d07072514944e0042604108050707100300c1c00b80c110050f480780d01d6030b844103c0c5500a40d00c8400143c686d040c03803030f00325068011504005103020b0000b0340c0c1c1d500503070070038481c2e044070b44c3c036555241e00340000a083c024a4041c034030640b90180d00841245180a90f550041d243c2c00c4140b581c3e9504078070807800003070720f49002940304c5005030308083d02d9545600c82c00c3c044803010800030f0a01500d107052030f03a558025485209005003107955698401c1d0f010a100f40520380810764020180c904583c1c89010180050342d0a01c544000f14107400300001d52400d04440c0c80c007500c1600c030078145c11a9200801e11003000584040030808a5070740101100040707904004c1d6005604800c0c259000d5810b41ca009802c4454109045110b46010010401e054000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 8337138 1250 8335888 8335903
    0x406080106050c0c04050f0402030f0a03080703020c0a0c1e06030207031709030706060902090102010b120703060506061b010c0f0507020f01030c1407060207050d0809060403080601050f030a2903 85
    0x3881c0066407080800c20341411318055044e155801402d042c1407164100c0036914a81c0110700031000c2c1c4442040700302c44d840d0b80383e08491004003c0392806000411aa0181d4050407100c025541660220b0003640e50310000ea1081e0b4018501c008a102815070341621894908400740119060131458000e00342c1380500f00340c0d0301041d00b81c140740040d400240c0002c03050003030360041940302c08180001070716440d10341c01030740202e00410300642c60b1603514000c1e40b0f050040c9440d511041030182a403e0f045441780c8026150040019070483c408020b804001d044054400c1e9014805800000b8130040003800104040c1124000c02d0801c0360070310240300076a68400c7d031111390030030900700050345000d442400da900c940c10300070441c0254030206842084c403c05070010040c0030301c210700340c4914000c10082036840a800344c0b035840040c1e00010015000030b0281c0c0c030540c0c03c40740505111f401c1120388009031006034021900c13900e00c0c5d81c03103440e1041c0d078809400300c0840a15004084109442951010903624001d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 8338388 1250 8337138 8337149
    0x151d03040b0703030b030d0201060905070302090a0905090304080604060603030906080606030a0c0e0a0303030603021503131502090a120302070504022d04050411030f1302100804020f0406140301060b04060801 91
    0x41c005507640805019510160b0b1822001c2c064031201c840340c1c1c101a00070310140c030440c0309503070400f8000f85c05180319100f20f803101d020041c12483d006042008003001018001e080005a1204010116004008014a0717206600c162000309806003145002849120b2981c4450244860003090114907074440f825294404860400014202e01c8503c044840700c0b10010b019400c10601e00010043c503502da00602d0503240240d0364000d400c60300c4194a40c2d00d00c01113441c3c001c1c0d0b1503146068000101d05110072441c6800c102c10241c20b04007031b41c0000c0c403514526400104c000c020002c1490415805004032002802c085404505102540341e5416615414840c648003141c10201104c49441c074003400d07a401b80202a000300204042c00d960102c10768000d4840b110a1040c4500048090300c504e800d004041c2e0703019000e08201000d12006480900003d00100c1c1e01000304200961261030354400d010080c1100c240a007801031400d802e0600b10794183d005481507042c104028099240c220220764111203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 8339638 1250 8338388 8338409
    0x807030e0102010b06030901090506010e011202060c0102041e090c0804111212040e07140703090b0904020c0109051c020106050a05010c0f061514010804030c0615030807151d0304 78
    0x20032100403401000c400c0310b8030f0350224000c81400801c550550000b1003407440b81d011610320b44d07203800d004035102e0424424500416078000c0c1c6031005082140107440344142d4407001608040d124948806c0780f01082d6101c503801e8200e4030742000f22020303034000d0122035895410f1145450800e0307100c46200d4468501c0310b500aa107059107440c04240208000f07800c15210340300045e1141d171685944243d401c0305407403540009140042d00140d0086101c110f5038000da040d1689520a407a01980d42034907089460b880b0340c0a40d0902c0743c602018820700030060443c4c480c1001e401d8803072540003082080c0700c4000e2500d085a16040043c41140c803034070000415501d09080c0140622654030785103100745124000241110b042c0907030b10b1703041e94003089902e007910b19000600301d09200301d10044a003050216400b50010360b00e20040c1d00420861b5000c20461705942c6030500c0340d2620b80e22081e559900200086070800c0228500d88410181c51083c604000b0f216a000c05503000307407501542c2d5074025400f40c0460704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 8340888 1250 8339638 8339657
    0x60503190c050c010203040602030405061008060f061302070501091e020604120f050708011a04020a050316050c120702040f0203010e0a050603011b02060708010f0b0a050d06091103090706030504080703 88
    0xd03802a003d0740c2d402c241c10402550359262500d001e00194100f40c504540611625020404071150994228103880040c00108410341e82d8031400e0840110161403150080c485d41c002000c440140d000030300d00700e0700a00020450110b10716000921039038081c008082004007420b900010394440c030444040710800f401210316111241802c590400020074002c05911401200141c280019003080482070350715800103d012210f070041c402a4031403001a140041d400f0000a400c5052480d61503100c400b4524155081ca1520142140341680c020700311001444040f488004610780360240010304884c4900c107500f1545030041042e4011030107810751345019100d400040840d102580304500ea038100c4072900011030304121020b5107501094070480c0003d0541000131551140201510b81111a09002ca42c41e0040c5d000c4200c0c0c041c0c2102c0001c90740c41391140c5001900c481980a0f151241014a04141e81c0b4180b002119207807004541c0700070f0a060404c001c1001091800c015903050b41c0e01814250700c078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 8342138 1250 8340888 8340911
    0xa02060702030102090904150b060307050301030303090c030803070207080105090c0604060f031b050403060e01050f010b0703050409020a02010c0f02060105030601060c020315011502010c110c04021b060c07060606050319 96
    0x390107100417154008109904202c18481d103e40342c40b406071fa011a04106008818051081e14071085401e82c001c990100300401c0001e1003a4001d030310183c00b80700e42c0258561250385556441c1d005a0710080140d0010106000c210020f200c2d0542040c48a0014000a802c03000802e19038080da00c543d4082c480c0c51000341c80c6850090700040c0d100b0f02e03c030028a10421140740080d006400c203000544a0030b1404d400c0c40c980441c14850540110b414020b90540c40e8680888c50384182d02201088003080300c18000050150140c2c0041d16141c0003d4001044500354982c004100c210500c100070119404500100150345002c68480c1c151869440d01c1b007242480c44c00400d01d01707007005011030300c0350030b0002c00010028802c0c81100402c3c1c14a50007813290300c00c0150201c48001c9107000e4207000b41c00c0404d007a0700c0c903e4658018200100140310b4074881c0c01d03e00058900f0000100c9951040032030000d14002001564404e1001400c900d0428034154144012205010300c2c0002418454a507030751005101c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 8343388 1250 8342138 8342141
    0xc0a05130c020a0507030501090308060d0507030605060d020d0506010e060a030305041208090603041b0902090105030609060a2103030609020f16020103060906060c1205030c0d020a030603020d050d08060a080a020607020301 97
    0xb08181c1104c100c0e0001592494031a00074500c008041d0006a0050003140103480d141e00342201540c3c00000425001d03055480f001c000385000362515500483e240707055001a00c40b003104040d80b034090b401800710b83d8504200120340b900018083c0c2d01c02c0d98540000c3c40025048400d44040c1c0d5100850045d0380030680c5404851031050480341c543c851004810801040b0401500c1e650624401070345c86005a56441702100746d005814010303020480520004141d401d2204182d503001e50020540c0c13201d2599602005500640f0101480b2071aa29a004405240c2c15014880003418441421843d05483c8044601c5c140296a8280b5030281c1481e02c21055a03c41d410010207003202e05030811156640354406080c400b002d420844011400c000070035407c1d1302a900b40e9118030300d80e02e00549001d10030b03404000207504c081030282c00d155a0361404009078540541c81d035407461240004040d00321420f003028014503801040988200706018052110726400304002c401c440c1c0c190703201a212052440040e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 8344638 1250 8343388 8343403
    0x80a080c0d02030a020a120e03070627080a0f0504030c030f140d090302010201060801020906090105070f060609050702010f060605090118090527120403140a020915030c0a05130c02 79
    0x14030754004014080c2d06003140d0700a241d07110158a900040325204004034056404005110b01e487e0014401d01c400708034160841c4585580400d01d211755400c503e11007441e8661141015241c2c0e640200d04a8141504a42e1500d507004050502038241807443d9900c0d4107500450100a10a0078490840001c01c103000d0081542c6007000780a50f0031480107034000904000c801c1c4416801503003001e0000440a00c180708840d08004042c0a1a00c0c100301040195960b0b4040d0b54100d6504440c1c41400e4042071440c80b584024060428001c070307290501c1c0100909451500d808401ca4915000041041341d2f0028100e4032950400e003010802042d50021140c5040d800b80d000000882c2001c0c2001f41c88800c080c3c0041020540c030019100310444814207545c0e031400d80c80e0170302103400700300b10070710104103150480144004c000c4100d13454082e503a4003003000354005407104a41424800038680c528503040c058107041ca9001d51305400824508000268031803015044e4296040d41c4001d00120140700340403c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 8345888 1250 8344638 8344657
    0x1090c02030d1a03070504050903030705071b030609060b0910180608070e010305070b030702070306090204061e0806010602010207110906010215010303020f070911070b09010213090603110d080a080c 87
    0x204803146141d0301000e40604140446813007030040709404540d83c0b42920400d0701a042d13020041d8251703618000c3c00d4410340e11141041c1c1d070038003c000d12102e549600800c8580698030698002c41c2c003524074604042502c04019060b407003045c10004108034090189e01020499083c2c022005c00e279003a00114000400e96508044000d00030202b020803d40c416010340343c101c03481181240c00c2581e442d402c00065010036507000e40142c10001d810008950740350050f0307400c00d0008100051455407100c1040e05100c8220b519000c03180c84400810032428140300b1a801002d0a0000794640500c81c1d50f45064a0300c004104c0e031003000c000002c12500d034802c0005064410110701110b00b9541c40f8180655503100b03400d4045010310980c0d401140003400c90080038000504900c42c1030800801707954802004034001c2070950030390340c00d010004d0301a4840c07140c0340080010700400030381141903060044001b900304003990b008245110071000050038080846200410382c3c50020b1a5454111fa480e10341c0c0700b004400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 8347138 1250 8345888 8345891
    0x20403050f06060a06080705030601090b030906060307080705030307020103020c0109080304051b0103090201051c0f020f090a080102030403090302060304060b041d010507080106080c1b01020a0e0109090e0601090c02030d 96
    0x441081400a024040c0c002101e00311541c40c0e94400801141039100c0c011200000c01000c0441c02440c01080a190040414188008080c0c0c030b0f02c14400254108403040203079503000c0300900c052824140312603000f801c089405445154180f101003a500d201d130010085c10550b0004003040c0212003075119206040d40424526a281024108140d40f002e1104941841d500d0f44496906258001e04c0380701c0c001030341a118981444154006050840100f400090019864405550041c402c0348020b140d1000381c20170035600c407042141032001c40306207600038a000368410000d02000c29008408942203d60446040f0750720384c0c2d40d290007400b600301c101000c0d4016007070041311201ca40c0710003500003500d1260002003140daa10140116071640007841140301045050b000700c0c081e0f40644004080341e10f214081d048010030020403a0342203a00410b8014000380e02103424200710760740441e00f00e000382600c01c014000d80800481a50700c6031010302c00c4603442a520303100680d80c14024425103000b1411001d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 8348388 1250 8347138 8347147
    0x307050d020c090112020310090602070b070906090605090618060c010203010b090906010e0f090702120c03030a0b15180a050414040501050702191e02090103030207050310020702030d2102 82
    0xc0a956110a00302003481150000000300740045c0c20a4078551080d0010300620780804456903081c020049240d00303a50f41502080550040b0381401409030180155a4500044901e410f20082025140e03401900030448104107404117540e9031310954001040da0042000f2191000d00020058070414003004850750012000040f02a0004040c098080d4240c3e00171034296521401190050300030000c2c160700a6080f94801224141003483c0c65001800e0b00480c4c60055400304500714a4000c199629100c1c1c1c0000100b0001560500650b040d4013815074480d002800100540f4183c1e005c0e4421041c40c44801440710086503842500740b100030900500100a41d00803481c03072101d0910100e80a5400d0342c20800480c60403440000e03485111107005400030050800303035864035641301d070703044000030314110f4000c00c41c0c0580d81e010907140c007c61103a002800e03100c0c5020103050501452030390540c03030f1503c18044200943c0307002c030b030030500c0d40503a10703014a440325103101040498013a0b42c10b4007091840403c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 8349638 1250 8348388 8348413
    0x150902030907060302090102060f0c1b0f07090606050d050c040905090307030e0303090a05150903011107050105010b0901080103060506030703170a02070b03100501080a09020603040f030806010201061511030705 92
    0x14011809180400142c400b01c1c0d0f281d41094080e4070964491030300503070103200010240c1214080306504840891100d81c1f0702901c00d140710764900d40e00c1c2c040d468182c010f414505103519003040100000d0689080c103006c1030786003000c00b4005000b1410440105e98840300043c2e9140c410310200c9000c0d080956042201c5c0c205501005d540e900442d8080f030208040d402268074524001042e680b045800402880c4041c1c02c10080c400c40704141c1c81c0300710303040c0018070644160369401c0c068001c3c00d402d035800d0242c4443d20744c1030140c00d560b030690003110011820003805040c4d9030f00c140300d641965006140881d00340c89080c0403030306d40710130b551020301000390805001e0850405000100048240d0364200c69541e600c80700c01070300710710003501c11102280c1d01c01420056075003c1c10b5402e41c04031402d400090b000941c3e4011402941c0300300c03403c680c040714851142c000c03d500402000c0d0042c1c4280f00800442d0b08042c3e020070b000400040c240c0500a101200b0003505400700201c45041343d01105440c01400c290 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 8350888 1250 8349638 8349641
    0x903120406030e0105160507060615030b19030305073207061d030a0f0c09020708030105040c08041203050c07020a090c031107030c0b060a05060315040b0301021612031509 75
    0x10700521000900f0003001082040701406070341d01034081002072000081240d102a60140c1c01300104031005a10341400040421102074008003003811514082030000b0342c901088013002c0301240403141043d01000520200b5409800e80d41d07981d620003000c00162260196100b1906c1b000c0c0003625007404c15443c0025a1003000c1170903411980a9241d5050b088101009480c10740001890290154082d010800100d030690703501052050165003604d9020b034980b0505010303a80b01c5881610001c600200400040c1028400e0345010041c0d4a03090245050030380e0344581000c4540c00407010035850f01c010a070890126412101d07070340c0e0300509002c24555100c07d005e0203094082c254001091506442030b10034040403003115120b035490382d600100745103999103030111a000036145507040307000ca610120b00d03511808000c6005002c00c0c1041d0a04e4100642000207a404140c4081e00030307401403000d00b062a0079603650000440d4000240000843c079034204030014201e40b000d0140314140007500046e140e406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 8352138 1250 8350888 8350897
    0x2030a0b0607060b030708010605090c030c0c030408010608060109050f060904030909020703080609010f030c0312120e01020706060b040807030618050102030117060a110901030c02010b0406060201020406081305030412030203090312 101
    0x10f5080c1d900340b69552101c1401c272006d0344502a002105140020002e1003410003c0d5445140000c283c1c6c02d00f265a0340c01480c50708190881d4449a554040034001074100300005401411511000e204038584504110b00c40da00241010740600c2c80783c0301090416001e40382400190a41070030031522038210303050041c0284c43c1502c0260240f9910000400c5100880311050f05584d000034440700b51b140386640380c6541640082c000800c0282d005140d01000803d40110811040c440d8005a1105070600380b00c07080324125400504600006c000c100200310000c1034130001c6a4000400042e90380c80840c540d044102d0060004256510003c008940c025030501031803580c601a03021100c107990b50041c580101c810712010007035031007800d01c91240150720941003620a8000d40c40086030010084c1e0100702640c0d400c1e0040e1001d40d4000c00c0900180c0c0c1d011040f19401441c40010b44602e402680320b580e100d22590207049802095445008103040c0200112003515001808a810614a851061070307643c21 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 8353388 1250 8352138 8352161
    0xe070905011d0907210902030a1b081203090f010902030705010f02070e25020105040b0406091104060311100302090f190e0901021206060a0806010806010c05060c04030303110304120302030a0b060706 87
    0x1790b0704500b42c81c0c083c0c51090b079a685501900512405c00c950700e81180d203031140b00d208034071031000d08004503401d030f0103120424507807010050454480c180180b9070f5061104410001e600e6a02d40103050000da6030028101c011030388203091101d0703509406032040b8100045030700090441044c420a0010b524170441000710440c0711b2603e00001c031455082e0480c02c3c0c034401e54000d801020750401050104090f076026502c950300c6400700d003e10303000c5000440c0c00d4540d00e610039544804c45104102c59410010380b0a800910985421454600303101d00080c00c010901d446140145941c01141c0400c1030407004030f07800b504020141003902e192202025010750b0184071320602001c1c4070808900305060901c1900d5216400d91603002c115a541c000448100400400325410810f05445400200d4014460540984440007155030b840e07045080c00b0303095441d20500c180c0492000c104100200301100b520b12403c0810345409a40e039110b24513154046d00d092400191701060001d09001041610340c4203c80c01d90 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 8354638 1250 8353388 8353427
    0x80f030406031808090603061206040308060f030c0108010306020c0a08040b03070e01050705060f09030f04060305090c030706080726010602030909180309060702060d0603030807090e070905011d0907 87
    0x2400c0649840c0b9540d0507460041580e02c0a220072105d928180000d19402140a403040c449413620404181c6051400d079810f82c00b0400d084103100d41420009920749030420242d00a00c4c070303084d02c1800246034100c1440003034602580802c0740c1e945a14240401d070051038100048549441d25204001265802660300d0000300c2c180d000007031004c0d40103400f41d81d50540c10601801960351707200081c002d1018003c1106000b800100031022103008694050400341c4115640081c103450212200c42c94002498549c601c6680405020040d09030710100859000800c2d00c0d015001441c01131000c10490542e13048014541001400400c00310f80c0040503080070002207864020f01d4032850304400004114110251007500100720000350b034104800200904e510162003280782145007844101101c01d190011000115018107201005902140c1d8002400e03101680401d0340c102448050403000e001c1c0300d00d5050006041030122503918461102c003035207a000e0011803044c034051600401d404281da90111502 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 8355888 1250 8354638 8354651
    0x11030f0106111c05130f09090b010902031303110a050307200f0a06030b0604080106030c0e09010606020c0d14011407020f06090601030206030405031905090a1508011e080f03040603 79
    0x20800003441d81020a1400ea00000741c0d05020303c100c9156200d1101140b1003940040001141010345814000502a0305c50000b4241c2031417401032806001030340500b40c454014414800007000241c51711507007503454102002d192030070480044c213001401c44045d215000111351801440420310078402c89002d41040c01c001103687d141008461b51a807a6442e4201c0140d00003440b40901070f078000405110010f1940303080c0765603075164a003542e0b0076800c2156124603902d4100300103c4c544803011b40110104c0000d21442c0d0515000a558480d0b035240148500d009103050003d201202a14102043e60b50f0000c2c04180105200c1c07181404098903114018418000e141610940c085400360103100ea00000d81600d0346903400b04662b64101400c103036050702003081004110141040d55020b001619120740b07454102c0c400c1000b0b010002c546c0802a05c190b030a00302c040c2103910804440c1035401c8818101e807500d00c0f200c10000108400e0700310340d1043c42113000c003289a00002029004481580e40c041c000d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 8357138 1250 8355888 8355917
    0x10c030c020a0c060f020106030f05010b04150e060402030402061c060f05040c08010e0901060b031005090a02040521010209030f0703060e0102040e07030c02150a0e0c030f030a080402030111030f0106 87
    0x10b81e856808007a1103058600c80a004551240081c40000a0140300100c1c030141c80e41c480030315001d02c211044038280c1d520149803001d424640920014541c0c00000c0522580c035281412801c501e0081191f4441c542c0000050110742d1b520060380c8000307081d0081c00d60100000c1004500400160052400b810107043c00001c040c50940102010220141d40e2038545918040780d441580e103001c0c01d210b806548643e000f06103080118051841691720380070b14505a45410248000141e0140c010820f8600401c01404603440351034080344081940d0185510b44400a103083e40280641e801d00d603418018055050f0562900181d403606490180e02c00300111210070042034200c0c440c030300c01c2c910700c10b4a9030300060555010341d020700c91094803801a5418200c42c00c031110342c624011102c0d0300c400c41d80c5048002049000308202c982460007500180000320703980401c4c940d24010741c0ba0110410100348001f03801c54030290000545004800d03480d035107a081255502841c1c0328240100c10005002500c01d054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 8358388 1250 8357138 8357143
    0x50c09010b0901090e04080408030c030301060f0903030c110d0c0f05120303070c0305070f1203021b0a02090604020c030d05040303050402100c030e040504060213060e151e0306120f010c030c02 84
    0x51142c140c490142d21441d110a101500d0130040080d180728009100c00142e1382420b00c0240b041c0600907010303554075030401d680131b041c0c0419403490720b040007070f03c4505100094014984643c8036402614050400485000280350175020301c40003800c03080041c8000548116084205c8182d0300c040b200003411881e104251a501d00040702c81d100040c0040a0301d0000c28001d6000301030f00e40c009c850055465407140c494414440c082c03500800001e6000035404404d460403400c0f4503001c11018060401c04207140c0014051a5000d0aaa031040780d0000340140d0200c001c104441082c0d0354031b00f00380308a1800d4100a0020441207809a004640041400d40d21a01c90505010050b9040e218400300910300000d001c01000b00410407650240e00300134840c07480720b0b21419000101401c0da1416603212111062240c6550301030140c030111401401f504140c0661450465140044510440d407070366100400500302c0c11005440010500501440501ca100190049071103100c40ba1024001508808030882c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 8359638 1250 8358388 8358397
    0xe0a14030a09170615130c020705090601030504050c0402130306150303030b09010605030c160f050604030f0e010c0f06090f060207020a0605030601050a0e01030e0d0201020304050c06040f0311040f0603050c09010b 93
    0x1061904404002000c80340042250b5200320f40c09495401c02c0706c00c115210342281c062071003900241e0300c0040c0800042c030301030080075070002081c81c0610080c1000d58665503102030441d2401d2041c0e4002c0f071130124034014072000c2c000071904007400303105504001500510807440d46c0820342c0028102041807109040c510020350481c0c0980c0d0380c80386590b41c2e0304500d007215001032a42c00ea80914603482400415140285140010f0244026100d0f90815103805040040c1a01d121024002116621009607800403030f0001c03001d4003c00d85041700c1620740f400324020301c50554014103d2080c0e031364200a0040e15409418818402e0b1201014a130311500c00f5902c502045951a000500410481d09014440e4054070b545400c1810003140f0002a00400c1c0e042400744000040140c1d404010001480020007010314000c405485451503d420940d0161880403240005003c2d4000101c15014a44866010f000c441441c008200484c0340c80303203003080d00c500500d400e243c03040c0c1c0c60000110f5416200e00856 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 8360888 1250 8359638 8359679
    0x50a0b010f1d040e01020c0d0f020d0e1801230307051e040b030303090313090507020705060304051c09150201270507050301020309030301060908060f0a0e0a14030a09 73
    0x10a00450703007141201c1c2d051041d969004029200d20108242d40c07030318001c907a20020b40000160300c40003e0b0a00e40d25042d203039101d540402085030060341502d034002c540c1d060307248654500b10300b40c05410780200f00290031028100c2c0003841c18100014401e41c2d9148540d42415010059800b1070300c90004159032030181c1c0c090701c1d901100d9030000c4803a518100340380e1080d0310b20260000c500340e000000083d0440c1c03c04c880340c0003036800008070396190201c0c40310010b000d80034004042095007401a0004e40d43c585500600340a0f200000205082c00410401da89140304405410000c0180c2c030f05005000c8981072081500008101000c01003003070042c018201418104e20300400c2e002000c80080c2c1e400d60803603806440e140104040400c05031402c1c0001c61141824800859495242c0310000f040c3d8541580005103d070000c10900c0100900c071007002d0340200b00c041d070200d0342001f4000d020741000881440106101d9a24461820124020000d454103880d43c2d01c1d2803000d41d5031184003950480000c50316 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 8362138 1250 8360888 8360897
    0x100f030c06050703031509020315060304080a05031801090c030c08010509060601030b01120504060506102115170706090f05030a080a0c0b0406060e0601140d090302030d0606050904050a0b01 83
    0x28040d581c400d1014218407402845d0204645c2800300c8845081d21641e002503407031a40000402801d8107244010b40052001a20410314514107030700c8191550050b20b4505080000000202c0d114502c5010004a0070384c05600030050b200303040c0b0b405510900e03140300c1100d41202e00e642c00a0700c0001882140e2003541b441024107869500c0030011001410340c17903003850510005806040c003060741489040c0c4611700c40d540004190a01c842040034a540d401e181e601080f0b54080d91441c07504043c92498048000c10708042502d400c8402d19070170454064000102038102105500320000c00000c0580440300c00345c8407541403944425222100303c003d806820b404d54003010080340000d2181c0c00800b840e142920304080c266086554100a00c4001d81e02500d500703480e802c042c4101401a00c03c2c5400c0b18007400c00d0324850160582d81d0310326004010304118020b039981c0483d001c0c10300a00450380009001103007003214035160340000e03081e078100c0028580151719000005100a005200e00f2041c00c130161907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 8363388 1250 8362138 8362163
    0x190614090d11010e0d09090b0406050604030f050703020d060518071203080a0e030f07050c03060f04060207030311130906120506010b16080703050a020c01031104090e0321100f03 78
    0x60302d440d03102110450b850765891480105441061001110b4048a43e0b80c0ea0100d520300035003802910754290107139110301d250500c20406a50740780e00719000c580e80541b00400c008020b007040350500569078000380d044021103045404100c881c1d4030881c4200001a40d282504d41040c20305030303659210740076a04201540400d00380119008890709640b01c0c481e00d20108a400e1408082ea0564000400c0c00c2c3c4d4540010408404102c81801600c400100a40003000d01c0c0c40e151a0800030a00c001d8406400300d5400540c145c14540300b03130031001a0040710400590f48001c150106106d5180500c06c50144610b440004601e01605010000c0000c1d0030000a04440c2d007030080d0184158000301620481120181c282c40018140c0d9000d040e5450098950702c0c2c8444540c0806030928012000c031134101450301c0b0003500301044c2e1030141c2e0182d40380d005000503110003004041d89580710782c00300181d01d0b11544d0401002c40e52200c1980d071040c5105c1c10b040000c10740d5000c41e00c0b80c0c8807403400010105818080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 8364638 1250 8363388 8363413
    0x114010c05010902030a0c08071a07061a09010f05040f1103040201050a020a21030c03020c0a060b04060e010b070c06080f070c030c080a0806040501080d0512040201030e19061409 78
    0xa40c00140c0641c0c0002522000f079400245001c080c56030403140c220303d41808006c0d01c10305000349401454041b03540e901001441010000034071a205004004c107607036030031228025800508120342070380041c22000903561101d5112800704554404d90344103078146141013043c4c22142c01441580324000c5819030958442c0d50055903079401a140540451140c42c6c55100450700c0341d8000c48180b501ca0ba01404110711015008042d01c2d106007402e018580100404000c0070310008080700c1454018400281c05816180040c010f80b406038810301254012400105a410200000307003000740c0308910355880190703605030545103084100c5040304000c41240000d840725000b1944041824407034580300054101545d90328405400c501044000119031504100090a0a1254601524904c40201001c0e44070401c01040c500c19051031003940c3c06150081821039000350009a9156043c00c20348151381020300c2c141e08000e00c03401c800d54040d03003010b03007a11500d1245841c0328098004000034050108480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 8365888 1250 8364638 8364647
    0x207050a060207080c03040b070506010509010e06130e0a1a0109090209040602030403050d02070303021b030c0a1407030f0b0403120b06030a0209130c020c09010801060b030610030e0604030806090906011401 90
    0x200f0307081d2002c050400c1004400801400240090416003c2e1141c907488070b802d0503840c140b4140c004c64003511034040140115540d0594291780318070201c0c1c443e000b50b07800104a40c007610458030440b4492151042c0703035080040c5045507110001d29036621400503a40d5403400c03000e0303c0a4050194010384100041408a80d450300110350240c06400e00300c0c6000d40d0f400080d4100da200400a40002c0e6001c0b031000d08026410b07070800401d40d43c0f5001517050465902c2116242c46a07090300600c0070010368034a00080c84240724040045030401d6140c80c0c807001d00d0070309100d2008121000c600040d0030b12886101071000348220060b054001c2c10003802c0d81e44480f8885c000358000c42c10700f41e101c0f11013041900009424080e00e1404003140c0e026200848100040c44030900d03041e00f140e209c1e64101441889001c0c0c0e8402901c0c0d010008450303c0c0d100395040a0158000c29040c8103402203401030318200001c1c142c01c600290b00500c0d0a81d00007078a640c0707048003240c944000b0b0103a03c001140c80071800d402d41d0301c80c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 8367138 1250 8365888 8365897
    0x10c0c02120703050601030c030b070e0609010c030c0b0a05041a0106050706090201120908090a0504092a0e010617060f03060a1104050303071202060c03070801050108040309210c08010207050a0602 86
    0x2140102c80350607403241c9a90f868440f090380201e60b1034004800030f00800007d19050783d000001403c03d2007030f400454000641c58058902d24604000c04a0718600c1850b22a440076210260040307103140072810075400480140c00100c034192000000120410410690500d000b8121412541d031541040c5e440c2e50360001520030920141d040059010054000419a100d4180b280d88a05c1d25603941e11218824040c80d481140c1c4540e209515008240003c146015003c2100c80814030340c801220080ca07a0103030207800c694010841031101d640020441941001c208109000d105288203207580e525810802014505034440360180c200c6000705120382c001b50420b50200c0203d0240078149901d8a000c20b02e10b4108010580d0740403c0d03c10b0790426150107004140d081810360450b540707180b03440c8030b020701902010f100b4581084140300c0010180342c407a2039007134041d0a0f80c9802c1c6d040d0804460181e5a100348e503140503116074410080001c2c0e00d180c144201c82c0c2403035101001d4000400c1540f1928004e400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 8368388 1250 8367138 8367169
    0xe0d030903061e05070306060801090605010504050603040c170604060501050607050d081005060c100c03050606070f02010c0804060c0201020708011a0603060a030501023c0405040509070e0117010e010c0c02 90
    0xf111507207502c90302024015188030390020341c0d00046030791502100034000030b0180e10440110313240060900c003036644503084801355907040e54000d64a0300c903440d000e55030050303da01c90300c1ca0400640303202013146070100d910350080f402108144942e0340ca1b801001018450840018590b40c050141a11610300405a040d4481a0040b1344800180d43c2e01c0441c400e80e1055000c0c035084d0b00403240121000401c0d2040c80e400d60040c6c90104010728001000c0f800501c941c0d0307c082e02c6040149a40821a8440c603107404030759074884003281c0c40c8c81c0c2d41c04000e001c1d02980d09080340507016a00740031501c500d05200384c0301c502290321074018603e19003078140700950f84007038107980d045047d055001c80440c00274001002c0c2030a40809c403180142c10049150b102d0b190500080300400b10180524200f00450000e03031b400d4070f608590006d840d480b00b800451410780c41d548075011000504000040380a0440400c0c204030300344000034000b10b84001640c6007200d80c2c1c3c000c003001181078500484007606248045086285 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 8369638 1250 8368388 8368421
    0x10608060f070c0309050a0b0417010203060a0e0a0b0604090b03010509060402090105120307050703080309100b0604060e040906060803030a0f050f070503060112110301230d030809010204050603160e0d03090306 92
    0xa856031b000c1000e881c2150002c4201800003c1c04119590b0744243c24090f403a1440300840c1581401e0000982c0f403d541e2041c41c3c01401004e005c00d090604661001c014114020101941c071980e6107100000b821400301254485d500c0c00700061525000442c0d01c078800d0354010b041c4000ea80c00c0c481000b00c000d0705460f401030a88814001e0300000741040103841c01950044a205031030380ba100300724034540344400d000c443d62a401d100c1c0c08009503d40d0000c4d602500c2c1e1a01307112039841501e101140007814581c1010b46541d052400020f43c20300017100a501403140da0100f80042138071510703514161130b401c0d14000d030303544640d90000d80c2ca00e12a0b805036400a01c1454000341c0d40d120720512a09481846515a1922000000402218440d104440d8894000700a66848002e074000000c5501d42c040001809002d001d0001501181c400e46c1101c0141c00c00900340c41d00d0b402c6c034400008444069418000c04035510b8000080149445000503e0503030b4141d4950a0445c103580d6070001814030707050000d1254 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 8370888 1250 8369638 8369657
    0x90f0b0301020313050d02030f1215031507030c09080c04020904020c030c0d08060d03120906060b0c060f0a0203040528021e15030601090303030b0a08070e09010608060f070c03 77
    0x5036002e0004500400d040905001803400909220707092004c0f01c82c03850259402080521a4a1a0002075613100f520307400301c002c0955142a0411400180c0c5a5000d5050040764800c0d0102d038094280d40d805100580d0341008500a0300c24103070b03484441c178010303a00e150384182020b00051070b154000307205001c0040c2016080040321450289150006602e04480750081496072006036405003803c0c3c0e0006044603c00d802c0754a5881c042e088400840102c002581c4448000c000c0c0310260f00020002e0801e00f416950311004403103081d031184d4040d110f44820342800e501103100030f5614026603001d0303070300880503145180148207146680c8188031900e80720082c40900d5040941d03202480c00c00604a181059072681c1c80c0c3e0020000791110000c82104070500c14014800141da101045c501960f61600700002c07110002d0000a0003d411540030840c3c40c400c081e80440c81f040200081030040d103550b40244810768a44181540340c9001710b65080c071801090001a840520801d550380c0442d009040c1138044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 8372138 1250 8370888 8370911
    0x203040e090a081b010b03010b0f24030106020102121503120703030603020d0c140406030c15050408030307031b08010506070305030a1d0c1306031109040305040b0a020106060e0118090f 81
    0x10340c1c01c03283c007503091003951404c401c3c0599000e018130400400b04a0080251880d0000012031010100807014050081c070040007004a0822440414181410702c14545a61390703000000e02035401509000b00c2240480c0100380920b048400b85400e5400060103042d6541000740078900541202909804248d1102400000b58a031a003118150a004a000c82a1181020f44c0e03903200009140c000e901841c03900360200041048800c100050300c005024003a04142c0d0490202c4203409260009101130000000b80240140c0660001d50b4024850307035600d0740e81c40140000e40b41510b0920034541c100380c00b0480d14000906c640011544008a10b42c0002e0840040c801400c0070900038919542c580d0107141c1c114007510b44001a02e00124050304203001450651b50b82a04a0b000006070034024060349000c0b0302010b010b88243d401400050311550b407607a11140c002400703040c080c03254001190821168404552040d0025042c444c0300c2c0290801e0325203000306540080c08108171454600e9542c01c0401507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 8373388 1250 8372138 8372153
    0x90303010603200a0810120f020f010203120f06031e0309040f060e04050105240f0d020409020306070203070317010e04020f040204080304030c0905070203070f03030e0c1003020d0f0c0203040e090a 86
    0x15140e40654801c00d680c1342184034034607494a07e40052221801c0e180000300084c1160303405410035035040d10402030709851140140c2c5035002e05102218030342c403800708002d61406d074414454423880044007114002500a819846854011601c500306a0030030800311440f0b040c140c00100c1d0a82c01c0e5400014580d0340c6254010544106880407926a5100c40911600740e040300136a07011a0f12200c0682c1c0c8000050b000101d000d0820f03184a40102e4071140c0d102c00395035559001403c0560050140c9001d4603140070001d449a11141044002c103031021050703400003002c0d0504030f041c1e034403a403200c1a1f070342c65940802208112034094107034030940800000c20941c800b400501300171886502ca510086080c80c902070142d0b14000c1840e800c5500034004c0002291420101941d81901402d00081003110300c09154200307034020754116004060040c02500c0340390305a00030030b86070010500401c08450390106c22000e43d6241c05103680181e1049c4400c0c0007208400101c290000c1d107001c11221440560354070b401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 8374638 1250 8373388 8373397
    0x15050402030c090102070902040609090f0e060106020715020601030222060915090e0a0c0303050705030706050c030406050a05040201050a0f020309031009020109090b060d0b0f0909070f0b0309030301060320 90
    0x3040040841c4507007007945c0400561300030b004003001c2541800d041110007405170300329115142803580c0b509a0160054901c4c3d200e030b810b01200b5000c2d11035560710f80320301a50f00c0859124880900e4001591041514404202c582c182da40c01440d480100111048a00341d03014400c5c21010811340d20080055200164442d50071582484442c0307696441c50486c198044604448840802e44c210302007003000070324003000c1501620350500b812911703580d140c24140d1031801022402003003203250a0501c583c40103001d0140d031090348141401e102e00d58420035200291281510001d020403014071031320201074060f102d0700801c8107480c811241132000c1440000e1030055100074568442d0b42d110034000a65038440160780182940010070b0141d85010001304101c0c1c0703c0c0c01021040d030744d03503050159a280c0d41e0a0702c0307244283c40100320f000107080107030015440f41414030030481c40080340038000548d44501020303a032094540300041d5007941e00c0c0040640281000203801c054444000d440260810484000b40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 8375888 1250 8374638 8374651
    0x30903020c1002010b030d02010e10092303070b0c0a020c060c03070b010b041d01080c04020a0302040302040906051f03050c0607020a08070605030108070f03050307030f120f022109060103061505040203 88
    0x20075140001c05c00d05082c10001c2c22820116410550309000450300010130a441901043c0f000940c019a401c003001031403454149040002a0340200c060151300c0080030f440000d000d25800d08450301d030081c2a4004c2d11a18a000c0c01580002641c1d514914201000e404001811000e90f0f10b000031f203968603640d402c0260400c2400c0c5e80003183c1030100d02003010040d15141c085100c10380e61941400e03441945c80b022310303c06134400c94001501c00715042c4a03805490082da03025005000c98a21403402c000500390846504030001040c10a501d90003400d080d0040c21030b0303005800740080e9841d40f0140540350b400941c050380c204070048400264032004003c07140041600756202520ba5050520b0242490265800306032000300b2250207102094004c01120000d44e40750400b000d17900d02c2c91070180c61176140c03421910402460100040075481a0703030001c1c000035039015100f1401040c4680069014035058803100441d030701102c010f00004084c0e60060702e009100c82c94204465680b88002010780c0c0c0101d401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 8377138 1250 8375888 8375891
    0x3040801020c060a020c19030207031a070e03060606090103050604090c0e0f0a050402010e19090e0a050c031b1002010e120417120a03020a09120c050108010b041401030903020c100201 80
    0x1010301d0604140314598014620044c103626060340d1048240d0b031811202c1e10b00b08189480300d0403208140c000c1041d003008585c442040540707200c000000b0b00001d00c0c11280d06020402c200c144c20454074000c1141c6204a20043c01b1310300f0000407400440003090300820858200d55141c01c203002203a060005400201b01003030281d491860075a20781015010058041e0708407034202002e200060707130008007101e41044140c1d01070840132000d03540081e2842441d40102080d0b86401c4105100c22808140e441c07403140140d0860b8040740d048818142e680c440f4040714020420202c01c2d03105103284c034400d40040210144008150310800316105400c107000034802201780400040c00700074044401080700c07010703440d0201400c5e0319003440c02c00312028410001e45004055000805030704d0507000340120405032086c3e98075403503c0e111600d000400b00c0c103a07004490124110500004002c2e0b050400c0701e00751010108082c800c520030342d0054015141c04101142540540103401e5160b466550181c140f2504c0c41c0e00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 8378388 1250 8377138 8377147
    0x2010908010203070806040203040602090406080c040c080609070f0203040e07090302090105040203040201020d0f090b0c030a0306050a06020a0f0201090902130e010501030903050910050702030a0305040905070504120201031d0304080102 103
    0x14054201691080c00140d0041c000c00072129008051694030810903540581e9070703070311403608400a04c0365590099000745021004905032900140070880b641041c0c45c01c229404102000b503d89c038200700c5003154004905030004401d94400c0b901d0384055070b03082c0110707814151a641503030b8005401729810301c0010554003040041d40340c140340c1c0c2c60042000391000c61131400c0a400007511061542ea081091002e580c000d20b800750721a0502400802500f0601900c410b190b0319880d4880e40480080170001c1d0074850080703500c0c5002c1d0440c0c8225079803a0010501c101c10b0795240360801c090200142d061110b81d44002401324800d00041c02042411002c00e100d03d070400906800e000340c10b070010b41c101440d05401c44000380e0031134201e641031501110361100d118030102c402c460902c200a8020742500a0301260b90800d5040000740050360320107401403041d41d03a01b0340101c40a020758400c003120201d440c8219400b650080c1c6c003150306141c28070807048450707600540c039903e198096032251105a50024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 8379638 1250 8378388 8378393
    0x6040302160e04030c020f0d03031406010305010821040e07020f0d050a090b1b030c0601060e012f07030203030c030903101404080c010b030604061407031401120215030c07 75
    0xa03088015066888034090715041914145031450020300c0101808004940e020030341d0b841550f07000b03181c03100804800242c89107290090103045d2849500541400c03800c04a030456000e13000d80c0341a5110100200705061002c0b00c0180100e0312821030442068041001144c006101c0c1d0410344141c3e0750f0707001081403a000480c0945001e2003400c41c2410450180a07106901d64025002811a40070000c001c1c0c503840d85100301407010300c0254480180d0300c0000703030b118074254000c10520b042741c00545a00755403100040040d03880c60b10310344001e03080b0f00b29442089182d110851140c0909260503089803607039512540464519400440990266800490041c0c254503082051181251281d8014840d0712055030030103440000240005155001c00b10f18540d08041c25442030308100c0f00141203603824101410904000c003c00003050300c8121703d040000d400e0346d0181c06401c3d14166001a03200c0ca613882c104411042440e800e000700d81c403e07440c10074801c0b002e901000de94024081e06e55101e58595451 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 8380888 1250 8379638 8379643
    0xb1503090d08010e0a020901030f0504060b030d0201060e0c1b060a1505030111070b04020105120f040204060506070525080601030602040603050601260a0207060203070c0203010e010b0906100306030c0806040302 92
    0x181d0a801040080c5005000e41c4181c1c0034507680142c58541c015840310700c503200603000303410410184450f05140004003c02d01c0059000310940d010103409860702c07507088410880c2602c01e24020075580c40140d0700860400020000201441d14821410a0790400d410f00d80d1030401806464044126845100c0d4407620489124020000c101c100c00030064281d00c240e41c3c080034012100090100941ca400040c156409142119082c01c178561114a0924041090b00003000e41642c00341c4c01245001004526405c252049031401034000780141100005404800544068604491440e007110440060103d10800082c2e010b184104030141c2c0310350610b50000c0c210781000345003074100309184000100c00e8040c900c1000400103d02d0701b400c12960f4002d4081c01903c5513160042c44103100108100d50310b5404481304825900c2200240804589000414240c03100d0403002603001c100c00c030215141d450b144407114085030302d45c1404900c03965a625503c08110007907000f02680e400a100300720070180d06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 8382138 1250 8380888 8380903
    0x8070801080a03090308071403070303020706050709030803130c0503010c1d0604030c152a02010201110f090105160b0906040b0108010c0f0509010c0b01080a140c0616060b150309 78
    0x7004107042045a20b0061254500e440094a9814001424414801038000b600307840b106010489940d21528600240258880301c0300f507400e1498a4046074040784110700341c0003240e8100340c100d402e60b154a180500182c000c840200c03441c4400c5140050692028040c0083c0300c00c8940365954501002941e2409a0880340002071003440201310600c00158100300003000c0c0c842840c1d0f420140401810290341000b41d205990070110807034030103440c3e2512140358840c5002e02c04c0c0d0003401800a07840050783c8602070000c4400c2000001d2240890b02e5110301e020305200100280c40600c5980c00e5110710010510640c7d08000c160888400c00051081d8900118010100c2800801407402000001040c182407840d1000400a00041005080c1c1c40740e1040c84085400108150302035940d8242580e841305151412141d80314036081c0c030b21600c04082520000d04402a10282c5014031000f00c45020000d200421555540e9642007000c442c1c50303045030010140910b5003403503a07909042c021203103006074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 8383388 1250 8382138 8382149
    0x301050106090302130606140d06030816030215041e02010203091203030103030f0c020604051509090906070f0e06040302012307080702011205060102070302090705070516050a050d0c050607020d02030a0308070801 93
    0x6001e01001030581c480341941c60500b80c48c512076154510200c501c805804070350720203090791101040d40024030328050844002d60b842502116680b202c00c030090711903220300b03c030050101e00c49601407286a654011020a005105205036440c0913014400070b03141111032441c1c8401c60344084010310406811404000c1100b8260822405c00f100941c0091024030030360103914001c1c007461a0301c3e000a608803050710180b0340014405103580c9480480b8950345c2c01d0480d45500050780d071010700d0060300e005034102080c005e0043c00c050f241c181160015510100c0c9807181005940c19502c500041407601c0c809002410b11800301c1d41e940301d001e40001041990800c01d1039032800d150100b80400e0742e8000075200101c96060f1480d80007699141c400b92024045d80c480501113000300302015035010104550070007900c1003110f0407040d0544410601043c09440c0030003c0000290010512107498100080c21b5076504c0203010742004a02d60303000c20305007448043c0031008a604681400042604a16020301420 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 8384638 1250 8383388 8383391
    0x3080f010e0a18060e010b0f0a050901090c050c030406020304030b060603061f02010b06070302060603060a09150b15120709050906010e010810120c090501080601060c080903010902030105010609030213 88
    0x14140850111000400703882d03500c40c6607499a03101900040e4000303040055400940400c83d100682c2c525502070b00d0368140e001c2c4907189080e500102c3d40340580b8000d0a440d40600540c4141c0c4c2058038490040c00130710783c001c050150500001c085944104020800b500325607000d552928618a0184e40301a40a480244550030600030400241c403140550700d01284014010f4100141d00d4105900400c49001a15048400043c0c41d80030b250b000070f05940150f1042d41180c020740d03038925921085540c9000f004100000005042c0340e0194a82c00042081400a140d81444402004483e101c0e512000c0b40c201040000310422005030307008401003001740400e84418003140f078840c0000300100c8040c428541070003600400300304a055018040405441c0c40c4d99030001c80c11140c14001c410103842e10801040340e041000200e0141d80200e1100d049400302c0c0c448500800960781c6843d003942000a900d80c140d0360b542c0501015075401d000f49030080c1a243c80d12401c10742140140100420300d100c1d600d20381e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 8385888 1250 8384638 8384641
    0x1a070c020105070f0309030b09010204060206010905060105091e04020703030b03010506011103030604020f040305010f020319020c070b031915050102010e0106051804020a1205100507020a02090103080c0102090a090903080f 97
    0x50740c0200444039000e512522071300503411540b50958031100756420240108070a2020802003480550081090b076045408807030f516030f03a6035a900b080d40c2045501034009801030040c5620f0b81001d005910002c0408038003031a0503020040410103d030800c00701031b40041d4492403501c545040a1140079041482864210045900c11007801e50300d1102401c1240265800100c17103ca4400c1c0c5419034010b503920100070b10403694012200400385d081552a6681d06000551030140000310b0b01c01c540e2a1044440940001841c04c003021040341c1000741244460190f42400882c0100c00c1c0c440c0d42203d0008121541e802801e200009084070207001c4501e4041c0c0c9082d03401e0001e651031019600745604010354a001558841c0301042c4035025590110600e00c0f034441904081100124200d07440c11604e00003044a03581d5004202da85c0c10f44204041d4010202c0c400600204644900034900a810b03800054500010f106c04a030390611568046400c1e41d40d204982c104055100300c8550300021a8020700c41103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 8387138 1250 8385888 8385893
    0x702010801060806060705030705160f030b040f1e03180501090806150f12010b040b04060b03040b0c040f0b040315020c06010b1303060207080c06060319030e03070b03041a070c 77
    0x50a0060054000f4401c0c00000582542d907060203c0c5c201c01d41c04411b40742c642e180f91408640e01c000480c3c070800f800c401c401d008a0f141d1030f00300c0c0700c1088030340041840b034440e1180e451b8444071203000501034418480e041400111903d40c40078101d1315a00c242d807250f0162816040c04058130340680c000c0c504214064000700100d10000414070f0300185141141a014151940080c02030300f218049a60450512040d2640c002d42c11740c1300e5680d0000689007401045d00850400085030254051a45111801d03c041404506d4203141c0716442010002c03aa4035060f10782001107005205e680c003201182170002820302c100680b907510020018107902d029401d01050101250301ca1405010714100d40030013050041011082e20111002160410011582c075400350400b40e441e81d002c01c01e103403041d110340408079555003400100c0c2100c240885c0055510a1301d030b50360455516010415040d07151041d050040740081c00030004500580c81603614100c8130192078062941e440c0e000308038206200101152101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 8388388 1250 8387138 8387147
    0x605010506030610031a09070203130f0b2502090a06140307031101050706020d0606030209040b0121020708121e010905090307020d03030e010c050c1203010f0e0717040605010e0903070201 82
    0xc04d4003c0c0c1c00e020070185141e82e101c07034800e86058000d660100030b00e014801c0454000c001401c0304054002c004050b66140d0010140000c218800d21032503090800c0031507500c030f8070401000d489503802c00c0301040d604815000200c5140056504030071030759881e49c6c01c106880f9034119205001100f1303400b6107091861500d403111503010b0440301d5414014000b440008111040c0d04481545069a408000c0c41d51240c40013802074006000440c05186000584030341580034040c0380c4542000c42061080903a100301152000e508101011a0290424099070b0820314a8140042c450816102c2e820b4000f00c1d092039131009d0b6072040e03005158031880d0106000c4a00000301c00c44405513015a507011034406149000c50046c44000c1d00d804c12546000c044203003884c0e00c9401001c0f403101d0700c0102e840d14611404081d465100030b100e44100034001c414208203c80c04142c0490380b000d00c2e81000d11361002c08030300100c9060000c0300c046071100e81e11001400403080c1c9400c0d0f541c000801070015414000c1540c0080e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 8389638 1250 8388388 8388409
    0x5040501050603160212040306090209060d0b2206051504140c030609070c02030609060402030601080102090604090f09020a030b0a0c08040b0a0e010b0312030405120702010c0303050c042106050105060306 89
    0x10604058a010031341800c2c000c210840d00440c100c03610640c0c90342e6a0800d00001c2c0034805049105600000201d10300345001d00d84041e80a8000c148103d07191546150300908003518204d03450360340204010880400c00e1407094034800c090554000159194050402089034540f0a000d030904a01c1d0f024000301e14601d005499200c04180c400c00c0440d00c400e02c2c151403082c003650f030003981441244d080111188000c280140958400e80449001da622183c59a00381e0003805440c07604103400384403c1103600000d800c4402070b1240e032800081d0500c96600030134400c2c1b0264000340e84140f0b15400380040d012461040c89160203c510344185541010780c2c812008460103401340705840d8682c0c107030094080e429405074059100040413155000c540c510400000e800488054503140110702c40b2040c2100c820040b10b80701607050395010540c911590301903000341300150000c408d8041c14000415101c810340f400c2402d0100010250041c11024503012007a00d0058002c2801020144188590381c1c070384000b000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 8390888 1250 8389638 8389651
    0x90b0a06091202010302131202040c0203030106020d0804140f0313050409080904020c010e0714040b0306040807080c0304121419020a0902090418030503010302010801060507031409030a050106150905040501050603 93
    0x382a429050004a02034040c4c10f152204554070040c0010b040000c0c08207560030ba89c400d8134244041c0c2581007050f61680000d100725405070b000040754818052148541135407080c8a0a00c040032841074640e214034001084102101940c400940a003030301d8260f050300360041101302c1d01804008181d0b40d80103210300404820900458000c291120b03036050a400400d4102010710440d0141c1d03139a0720078090010300d52164035008a1900f0318010090070040b0b2160b2040e030300900028500001541d550102c1d0344542010075443c0000d00c030200340324110324a1810307038034000d000c1c00c42d1285280d80480d0416044e02400c03001c3c101c4010700c2000603154840396030200c1c0c0d5651001601d4400340d0012034054000303009440f5034818218050030030160880e002e541030700d00070707a41c0c02841c0c0e0700c40340c1c140c51902c00c001000d0007003040e0510100210b210000180180e9101074141c8142e9105942c0b2203080d980c0a4000c8071030441914200820700d9840784c9118000c00080f03a040c8500e5250001144041c440039005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 8392138 1250 8390888 8390909
    0x7080a050304050c030f010506011413050105090d1a0f0106030b010c02010f05090607060911060c0a08090406080307050a060c0e06071101020a1406010501170705090d02031207060501090b0a0609 85
    0x10b0511005002c000e60301e06000d010360302030001d0703411300c24001c040440d056404200c104040451400c469815240314101000c140c85449080c40010341e01d1b034000306102ea03031000c0441c201400040c110980c0300b030301c10329020001000c0d051a0f00c0188600605810860406103458030b40280c2c0d03a805040100e0300b54080c2060103001c070300c640081304c16204031110b4542080e000200a8100b10240d4030034500240600e0100500e01d04d80c030f04201d002e10a07040c489282ea402044c258010641e07078401440314902c01080019115070300d0a40c141980c00001090721641c00c0954003900380b1810b030055800d50750142c90704201006811000901502807042c01400f42d01d085800207030640d00800401325003540110700350440c40302c05105580d0310300d002d0007100d002801400a00103410f4520240038007503400d0740c6409050011600511040107803044040c0d80c940304480d40c00c446038004400501f601809144041880d41c180725611003501c0310300707490a0144210f084200281c5600001d0b104c280c42c2b00036407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 8393388 1250 8392138 8392141
    0x20604020f040e0102120108070806010320041e021801140a1206080f031b0601050109030f0507090e0c09060307060512150402040902070510050c0d0e030d050403080f0a0207080a0503 80
    0x420b00406142c10500d06540c80010300c5521707051281c01090490311248212142c550f1103154240d1181b100784030003069240d40304c0e8a0030304c0010041d0b40d0801d5010181c8000740341140c8818420310441c0215280354210b0340001e9803000c90183d41c07568415043c007030038681c00981d6076840f88178540c4100b458030f50412407400143d040c003030066007054005140040898030000c0c00384007040e460303600401c0010b1103149011981c3e480260045403150403100161038000110386141c444540104541000300c8450003850008503106205100f003107648003006000708060107410041c40640d40026140ca032103603015001c10025103174000d00f15045480b140910190503120003d9038191049034007035050780240080380c007003140b4040354042c00c1c060703002d0401c83e4080110040160125201511440e110740010058070500217459004412030b8181d05046034a080f050301520000c440d0242c0e81100060072070401d102c1c005103042e00c110340000c100c540462605c119551414000d100710a070080c1404400300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 8394638 1250 8393388 8393419
    0x60f0105060c0f0a08090108010f05030309010e01020f0a030801150507020d060e12070501050f060603041104020a0207030804090203060306060303030702070e04140607030c0311040b0403020d020f0d050705091602060402 96
    0x1090070545080c0807140030b13120324030307000034180c00018049000624020000444100d59080c100032254040c014629158281307004403a0048441641410751040c41d01c1d0020010b400c11000c00300e10301039a100320165050041000d00158030809100420005004040c0903980700714001d0852980840b0002c0e40c2d18011005500b8250012a201300401c404a010003c2c010190400307880b45400ca000e4038421303a03a600800003540001c1d50003070100e1f1601d1a4002660506034003d01200d2030380c0c01140d040a51381e030b9903c08035902c40c1d04030350801a00401801400d0600304081a00944110090350540c0f400810003036603162584600d0705a400000041818800210050700118240780151002c82c60701e060080c000e80400018000000d1410320718000c44140d00b010713a015540038646040c50249541c00300140800d00e8542645e104031700703644424890341c428940420492044c2e000e010a81c0c0750804101200000070418a420104000100d148540c041070b0180d1003503045802809406810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 8395888 1250 8394638 8394643
    0x6020d030908030a09170a0f020105010f0602030304061a0a03060204092313020117130b0c0301050a030b0903090301020a09031509021003020a030906020313140d02030a0c061803091403060f0105060c 87
    0x340e0044c00b480306e00140703210300c20b50300c81d03c0b8028241c0f880e0000d001c0c03640d807120390f0380541040d8032616006810034000701d00003800a401526407501c1640180704085101800a8034102c03a55104032a03480c1e0020701080160628000d803205078040040c0b06078403c00d01100c0c00400781c0300a104a000c10101c0004400f1a805000e14000403100303031000d1151850304400780344c05101c0503942902c16142c2c0c0301c00101916440011a8181e407005001103002502d5540c0d2044102c82c05448031009020a005c1100da5807000d102a10001c41c03c2e0344d481c10310602c2c504001c0c0b0020f1140181440941c00c00c608a0050f88481154080d42c1d41c851070b0041e03450100c00c0c0d04800810f50500c004004500000c140f0a0b03810300745060003051070050307500f641c1d40503c030200e084e03941141c407801c40c001d600103020f8440160701400d00c0e00c80361401070b41e0200b184c480918800d840113a40f40021004154800c03802c4c0003040d142c10415400d114180d00900c0141080c1d0000d40740b42205114040c0b080500056144d00c4400a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 8397138 1250 8395888 8395913
    0x20304061404090501090203060310090201050a03020c0123040c0f030201050403020105030a0b0a031b0b090906190b0304150608010e060114040f0501080a1b060e0907030207120906020d030908030a09 87
    0x2e207842013200e943c403140c1d2000a54810b480c428441d00c50013103142400250b03403041a0030694140c40380e5140c0b4030000d4080c1c000e0341141c118180030313540e58465880c005400510b002d6294641030f00040c11450240b4207005a0300d80c2d47c11100004110507410310050f42c100003210107407602401c03c03544a40d40e1034180c40c0a4041210502e82104c4000b400004018000403030b010702c21000316007115907a40380d5090445074000c0e0803a00c0d5001000e00082949424441140d840d000d412407c1030003100d0321030008003050b034025141296110f5021303200110340c8900d0321030344019100c40b2000f40240404522065030391001030003000070f00200103210506942c0e0b6036102d014001c000d80028130156a40d10301d0306480e81c05100b02643d00f0b103040600d10b403e021680340810107484c1c507500d86288003c0ca00c002d020043c88010f04401c1416401c01802021410031140b420945032030b80e45004815091880c024103140070307400540c0905050501c60300000b4012400d5071740c401c481c900c00082c01c040504000700f903082c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 8398388 1250 8397138 8397149
    0x6080313030201080a0c0512070302040305030f030f070e011709100606170705070209010605070510050f062805040e12040305071a0a08010b0306010c0b010602030a021c020304061404 80
    0xc050105109800c840d0084038000d80b90015203030390f05280c0105444070700c030384000080d07000c01403a40c0c02c095a4200f103400000c0c0703103030041c00c00e500c07651005d280d58003142c003082600d000072040050030742c0c1c080042c03680540d440c900400b44040f00c00000e03140005c00c2d00150002641800021804202082020504c181c151400d00c030865031420094080080c4400c40746603043d1401c0061074041c0a803040710011503001d441c043d15a0700c1d00400312000c2d04540350480b40c1c0d0007500d2201d590184035020f59405600b81c4485416103080c4401000b5900101c010500303240c400c595680455000b0610b4140201e0720191804908949030440060909218940481d003850000c01c0c040140140002e9600640b00421081200c4120000a10540e030040031403100008001900510030b002d444005103401c80380c10b05080540d00c4190f0764852020000740c01c0940160300109250301440d604000b080a01d40581054060b80d00a41c3c5e4000e44920450181a040c481044004c2c3c1e006400e8400301c41c000c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 8399638 1250 8398388 8398393
    0x306010e09070309050c03010509070b070309090204030b0a200a030c02030702041401180603020603010306020a120507020d030c05030402030a0201210507090609091503140709110703020618060a020d0608 89
    0x2c0d2400c405001415450021768240c0f1034020803141c18181445000e000c1d039080070040901c54640ba001c115142d1162000b00c0c101320600000241142d994005031014621968245c01c81d4900300541c4411201c24650404120385040ea240d010100400205c91304024a4580030407402d0b0085411792952041c1c0308020740203407408005901140d4034450141c103881d58020310300306485a03801c407201902c003076010181d03004200b040100300080041d401404900410708000c001c01c8000703229442190f408403200c10168000c035030305000c4503a0600c10542402001d042060950401c2d40110741c1e10030100d40000c2c1407003010503480350542c0b06580c0d50865001c4411051016103803890000b44640c0c445d120325000b0640d403403008103800d2118000d41c81c02c4404441071500807851910707030000310310344102d802060380a8140c4c00700c0d1418490164650741c040c0200c09507505c0d0040c3c0b40080c0f400724001c0c60822141c0c1da03601c00d070285c40c00204000c0d410514241002d40c4a1000041c208010700807988400b0003417 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 8400888 1250 8399638 8399641
    0x4020c030909090f0105060306071202030a0902040207050a03080105010c0b010311180a0b0307051002190201030e07080102070209160507061109090106020606040c110d110a05010c1d031209060306010e09 89
    0x1c00c00191011340340070004020b02c01038036140141a0b82d29030945000340800d00d503a000c2d580010312030f0702543e0320110804021445405a4010800b20f9000780420384098010a12000c1810340006c1c3d85801060280f0700041441c0b15519400100038046c00020b2050114005100d0f03107959000000030703c245200082c64060400c01601d4000380f841c286054024051141d0001c0e0a1038180c0c00701c0c0c480411078024007100040c1a82403019024041e1080f41415600c0d007003084600000c01c4048082d100e03803000144e840c41140100a0340c910024421901d520480085c03503083d0303903c00c0135203002c03035404980410442d85417140c0200c40d0060b0380206070000041000003824603030001c1c11600546d410ba508000310103004a0840b134442d007000c1665419441048040210b42c800c9104400042c4400c06440e810259640c0b00c900b51540c00c1d0700c0100180c1c40858200e842607594914403020201280200081d40708864242600e004405080b80708100100002c3c0190340142c040c2032020800a02140e0113 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 8402138 1250 8400888 8400901
    0x10f1d0c07020a18060b0a080103030e030a05070f06030e210307090302090a02040302090a0b01021e0708030301081c050901080106080a0209090405010507020708010b060301031202030d020f0d05070203071104020c030909 96
    0x10321014003858000744d81040b50026014240c403040318610030311036503024890382c296201070340c4c3c3c90742c02c031f6030142c05200c1e81807074a01107903046c440003001c1e0132592064194285401001816200440034003541c80d0032940f607068040140b0f0140f01c5148451308101030300c82e0f85110084d154032400f0790010390010302c00410400c125229500034425240f007144d4150302c03901d91a200000300c440c412503c6015901420f035090182d541414071141d0310481d581216002600d542029056400c20307448501c0395444020031400703404006501c45413036022460700b11f0528200000007801c8141c1889440b040c44407000c0440d0b040002601110141200070308010503070705141c071b05180200300c00c680590050186460218148a0600814103c484024841400e50b400c640b2008580c0d82ca81c46d80c0340c2548401c00c1140700e2440c40d4006003803944e4140c0b48150302c40b4034480c0c03154140c0303500605500031504100190000100002c0b490203100c8001d4a0058032200220a65440d501c50b403084542d2041616041012 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 8403388 1250 8402138 8402159
    0xd14040e19060e04170304110609060c0102130611060f01050603040c1d010306111c020c010e0615010f030c020d030902010207081009060b0105030601020a1103070e04030f08010f1d0c07020a 83
    0x2aa00c141c071174072003a181e40a0046440d0000740c03001888085034001d40722851501c603010308540240241418548980c501180e400c9030301c00c2d8540030401102c54401c002454200d40186000c0c0190f0020f0446031a01d200140380c44041401042d10840c400300124050001c11018000500340d101e280f0042181491100d620784482444110b42c11402c1c58031001e483c5003004155003a5060810b4812100c034032221210f8080c1d007161000c002c15660780c00c2440d901c2c0c002001340a0140015420704004804881c000421014141041005141c140411400d50343d0b40000d9541179200b041c0303800600e22103980b00407410314101e42c0c0301140702c1c4070380c0c840080c000c0c602e580481a00b0380314490410601524400564003400101c800501581040100c83c0114031041c0c2c8100000e880101590740c0b1503141c6c030b03c0101c3c08200f40c406030000f5040601c40c5103e2900f22400d10702509640101c0e003000381c901001d020384412036903c203418031450480400c40c003400440131342c3e07031050380101010030440c0c65492010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 8404638 1250 8403388 8403391
    0x70c03110a0803160b150a030f03080c030f0402010c06090c06020102090f031507082d0412090806071808060705070c091103060904020112090c06020d14040e19060e 72
    0x9208004250740050701c081c0000480f252001020360b44043d403290350312038400703944c0000c20505030220080c4a440066035540c11700c0b40990321803582d154407a004e85c00c005008a0008007a821118000c0007801600445051016885942480c1c0032204042a180c4840902940030008142040580003c10180c1c2c064018100c010070a4508000d0401c45030105507441000f00c1c01c18080707610320408281c6a902c61030855600c240d039540e081c0030301c0c0d840780062100c1302e0741c0303940c0031a83c0c02d4103c05020412000154142c180205490240c4c0c100342030940907900c03408090074201c10b000d9541e8a4800760940b0690010082002c50240c40c024581280060300d154002c58044a0100740b100700418161454421480f903aa000c4810504542c0c0d900184060310001034030036414020f0302886c0b10601800703402150b500718410300d0100b0000d0b18191001e858030b201d0310401001c1c0100992030780c462151440c10780c0c081b207a20401c0100c2c039884005118020340d00d91040c000d025428400c01241e001450300c6480d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 8405888 1250 8404638 8404673
    0x3150c0d0f0b12060103120f02071205010b0a090209010909020a180305060103020301050f070507080f0702100e03010e030405010203070f02180c07110d03020c0906060d0e010b0f06090105030f0c070c03 88
    0xb10f091105261042d900ca000034007009084a154500d81d0081a1144849100203045d40c0115514251940407090303031000344410441c0c90b03a440d01000c01c1d03075003084641740008005549065040035190400641000c80901400c403041e0390204480c80038500c503004540e00601c81400b0008001d459080907911a4001d001c01da000c3d41c00c00c00841d5202107002e01c40740c1300300c1d0300360383d114100501e59440308103a40c0b03e05980c402a90003800f1040240e070718507202c02d09810f0b444e1283d00400d450f41090500750b80048402592f146c00c1484104220398001c811110040c2d80560b045130300100e14400902002e180e1010301c1e12001c00d9204001800002c44020003046002d07070400300e440200d2104010b108000c6038002001070b0032081c4103289606050805580004004050b10b00b050b09030301d0b4960480f01c40f4407400c10180c0d100c450468542c1004e0041d002414815200325180c2165400041c0440c0301c0944017040c0e0381d11140020729001e151a0540340140c0d440708401815a54a0501208148000d03581 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 8407138 1250 8405888 8405899
    0x606040509030301050a03030f12050703020d0b01081b03060604080102040312090f0b09060318030c03040501090e010311240f19020f100e010906110c07060305010503150c0d0f0b 78
    0xc00c22000000043da4101d42006001c031a007a800c60360200c825080785003012090050f07a900c03892401841c0d010311341c410b10755a039006031100648441d540944021003029410703c0500020f000528901d103210385030340c0504030a855525260b42011a41c00c1c8070301e603c030b000c00b944041000b10401807101c85020501100d984c4243d0210345560140840068510540036606410048501c0a08286016607406407044140700642d0080100d81030640d8003210213030b58550000181880f81303680040a01024000310b0340c118560b5030440e50f643c6803030070800d0942441031340070080040050001d861508580b0104240182c5c460340400024141c0d6041090701880f000d860b03aa42104852002a1070004c62109034020300d130900e88150040010700c141c0c01c0700413044d5200d400000c00310f03089014000030a06000a0f65544c1c290142190741854a0758100e0340c1018100b0740104602d5800244d4690803580c0c404002160383c4408081001902c260300540c0383d00c90070000112a241c02550084500c02402d41700d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 8408388 1250 8407138 8407141
    0x705040e010b030708010302010f020a060c02031317030301060309050708070b04030b06010302030411010e040b062107020f0c100504030f0b0603190515060307030507090203010807090b010507060506060409060806060405 96
    0x80c2c803020b03400120754140c009600e0310010400f6600c00c509085006006005540d42601700340c0b1b0303440a0710f541040c41c0e0090fa10003c0d250295808d00d540000c0248402002c40007021023a007260341c0c4078801841031a041548500c0c0b02c005001041c05101c0c0203102100c1241c9030640d0f80d111020103900144010b4030450104000140b05501900031603100d1a0301c254011009100e540043d560900e017403c2540d0800e0741c6103130b441000c1d200c00c0d0040c0041800d01070030000c451501e2079115400d10340204a5011500190804a203213200014018209101120420003851031414200d17800e0060358405054181446519030a12a181603001d008036010b40940e0385403511109005c6401104040041c010b0348803c0d02900c443c410041840e810541c0201904c2c410740e41d0fa21101d03d4640390740c01a001c0c2e25030010040260110810040c0003c1040ca40d0500190080100207070480c0201034003d4081501c501c001a80d0342c1c0c801c02194054840b4910030401552207240990b0b40792022540c2c4c9000d14946030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 8409638 1250 8408388 8408399
    0xe0109110a020604061a030d020105041101020a02030a030c11060d090c061404031403040b0c0607030b0d02090f06040905010c0f030609050c0a110102090303070b090c010c0507060c1a0705040e01 85
    0x1400c40c0d0406003076400400030740d19141e0701e440082007018500d6180380c0700a00c10200a5606021007030751480c01d40e00224a904050400002c0f42440001071815540001c01d960016100410381207403070b41d09030400e144030700001d04002c84c910058155507984007000080d01d800072490380c0d00c0b86001c00c1c0034611841340d03952510810780d01d0002841126140b540140b0013080010703d0200b850300700744816000d482c207240d580c3d6107940451f004492451859040301e010006c5d60b650501c034000302c809040f0340c500500c043e07540106944031000360135030120045601c00610103442d113800c44020503074080001c008040b681c0c030b8003d140c0c0340004030f400c002a00700702001455462a01402e0701070502c0c03101c824a03140849805580201011000326aa0b540074403610f040c50742c0a01c090302029001301c180004038a080a40503040c1000c83e030300f1070305200c501c2902c1e0f004200c0015540302510340605100059030300300d041c41d0f02120740215841c500c0c960314000300003a16601c50041c004980160781c039440e5603601c96 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 8410888 1250 8409638 8409671
    0x504180b1e01050f030106030c030c081005010e040f030c1403030a0b010804020a05040b011701030f060b0414010e07020f01060b04050108010b0c0a061e0510050907090536010e0109 79
    0x100719000d4200e000400520042c504140c0e210840c600040000482656990300c221151180354015500114160400c01503c4010b00c0f85c1c1e1081031010a007000258140300c0401c030807800252010b8441400d11403004105030140c0350414046800200f0345c4498007588401c282da80d4401c50b4034041c0b46042c0000c3c0b80055000b51a0b060196074018070f9118240e00300010b00004100b03c1c1d02450411601c3c0000217080303440e4800880c06540078001c1983c401000d400c2c0359080d28210b00c18680900c0c50004660089502c1400d214191080050b0341c0f042d5450384030782249420f06008102c617041d46051000030b0021140001031049680c00e07200d090b01a80d0365a5008050300030394903023000580042d08150000791040c2c1c46050480c0405070300c01c40101120000d5030465200300c17a417103001e101400052103603141c02d4155550003001880c03d809028100408504040000e4071550700000e64680195901c0e20080c851031402840485182c42c60340c2d45040030f40070f040080c13041800d51841d1441c04003070442034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 8412138 1250 8410888 8410921
    0x10207030201080105040c0e0904030c0605011d13020a1a030f0112050a06021c09030203070302060609100303050c0c06070302060f010501050a0509010f02010f020d0b0f040b0901050d050102040504180b 88
    0x143c64046042c3c1c81d01060201a28818101c102006280341e806590b5559088030340d401240207039a0140410940d1800c181141c4040e0040c0c0c050518119a42810b40449003015074030544c111142d04100e0950320101c0c81e200c600b034001c588503064000c04010f0054101000e144110030701d07811200039036a60040c0d00c41300b04440c400504160894140000400c500d5001045425824013044903e5400c0d204060225801c5603c1200140c000144034414076604001c0ba5401c110700700e56108840c20800b1400070001c1035407100806101c404034454044e03200905c90948100c00283c201a03032200c0c1860001c0d02c0d160102e524404210380580040364030751140b81502d0400a454843ca4500400c503001558040700c484100700c1150340350305004a460000303001605a50042c0500400e0324109038040000745602c0444860050b441c082001815a540c20116411100b06960515109032503084c07007406441a07401c266001814162115250581c107402800c005000d00410300741a1500345414101401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 8413388 1250 8412138 8412143
    0x2030c04060b070c0b03040f1e020901090c021005070f03090c050607080304030807030902030303131103010c02010e0705030c1e010c050f07030320070302010e030304090515040b060a0906030b040209040509011a01020703 96
    0x1101c810040020300c041d0912209e62090a00640104510380c001781c0095230903007003507000350b8452a40c0c2032550380420845003220510030b07081c000c3d03150920b00140941c51030700c00c2400309900d0307102c81d509100d4110054006410080c0031665250046e0400100d0f551003501c04500050119002032035286c800d10034040c2c82580180918a16110b14201100c0e003426000e068828120090441c0345941d02480342c00d00c03410444e00017155651b40c0c60b10050800400c0da010740e0080e040328400020964a005030f08072203122680019821030f02490040300e4901c840a40201b480c41085d144c81a4030100141d007600f00c80c8690340381c0c440031204600e0003601c440b5280c1c240c0c5140d402441e05200643c09902d85007199140541181c0c24581d82e10081c0e02518030640702041d480b0314801c00c2c00984d017020b0050807040002946d600f490070b4880c5100030990b9010344500c1d820503568420a290540d6903404807207003640c0c0104144060304049a4290083c05404904454030f00640c030741100c80e500208400088130b8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 8414638 1250 8413388 8413403
    0x503070c1505030a02130902070302011a0d02031c02010e031201081207050a0b07030f020a11070609060206010e0c120f1005030105010b0d020f040503010e030c0106090605061602030c04060b070c0b0304 88
    0x440303844e1a04041d4010540c42c0a00f60915100410b020740e1500c05040441d000703034000300b0140c02c101a00c500c0c00b0340004020340521040c1c0c1142c405a00c000070911100140c400301400011440300f006c9005000e2000220302a01002078100c2880100d142010b0580702c1e00310030b8505410008086107117622402234020100d0f081881014041b464110100368060524240400c600e42c0c1c5000020481e07205c1140c6802042c001d0b002c1000c406401c00050000e81040e082c0740d2191420310b08040e546400510600107001d0f46240040d01e50710070001940c0c180421110b0348102814101e05001c1941001ca031017440f5260300c100001094a414080d4034102d49200350154900141042c1080c040d500000311100032040030800022551000d100c4c101c1c6200c2c8010103907841e54000740780142580c009038808104035080c58000d00241c0d03580000c40700c240d802c60780d03a00540106880400e042042481d1450b6010349800f40004000928070000c0c10f28030322503581000f01c0ca0705c4014180071404241c40140c40e07039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 8415888 1250 8414638 8414641
    0x3050310090b0d020d0318080d020c030c03060f04080d060603020a02061003030e01050904020403050a0b0108060f04110108180f060105010e03010501030803010302060304211706010e01080601030c050c06040503070c150503 97
    0x41c208085001e003031728020700c0c004407d800842da0701040180c1c65880005540d0102081000e501c0d0b05215009020364114003a020103402540020350310080034002288880341040820300708418101103d2a5468611003800701135aa994041d000f9000306121038098002c90300020009021800c1c00c0d03050766410380f00e00703810462180c01125190050740c0d6191b00690b00f0000400403800400c40c0c640400d00c159020081981000a03180c180b04001e007503000b00d09030003801c1c400000d9514030003046940081c40c00520541e42d46890342e209a030303803c00000003400341e00400c540c001d502050043c1a180c4c06c2e241c5003000315802c07062500300c801c24400900340036028401803005203403140085400c10701482c10a4600c5001d000100c0c44002c02820320008104041c0030400f19100340c0d024a07a0081090a141d5030071101400080c001d8200103000904140e6103a1100304140e02942c1650a19070040003107071294502440c00a5413a40880001d4511030000580020860511402c02c0c1520804d5070310103046 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 8417138 1250 8415888 8415893
    0xe0f0a030503190204030609020423071d1f02070f0b0d0c020a020303030705030f0c03190e010f18050105090106080307060e0307020d11090c0306030c0603100e010303050310090b0d 79
    0x854101800310035000d0f8031039401e8800703c48a030001e403000d54000e0500041c1c209251041104407400b50140c0c8030700885001c01c00311070a4003114481da10202c0d600301280c2815030b6042000a036554442c3c0030b544403c51607503200402c40c2000c521884413015408944d0f480340c440f0040c050700c280e184035110b20880308008514045e801340c0c105290600342801164255101ca50000f8190381044a084001074804400c200174803506600554000070285006803079401e21a241200c9075644c9035013041c040d9180c2000700708601c0c09602c80780c11005c103080c1c01c1100c1801e010021405141c031a07001e072015170800002c0740d1503ca0600c154022641614002c0d4035140f1181e482e03001030f00041c2006c21090005128003009078a0f181d001c0e01a8910510350005080000030802c41041c0001d441c40a100106104000d100d440c00220f040c8418822940c3c9a20303907982c5d03400200b51088a0300a0305403843c601d80000101500720004c0e6005503048035040c0161511a2104011140d520072031079800620500404003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 8418388 1250 8417138 8417147
    0x60616020f03070801020307020f06060409030801050607020f0303040602010204090b040203070206010303080415050a230708150a05040603050102090108090f071a0c07141804080904020a1b030c03030e0f0a03 91
    0x401d490041e0586581d039030798448180c220f801c2114140d02680045020422a034000d00042e5882441141c04210f98445a10018948801401420700400c1d00240fa00b044d55600d071887d8805040c001c0480780e642c0e4035000024040e4000d8490100004c1c1411020f00043c03815000b60391181e02d0760350041c0351581c0f0310b8600701c400710030144c41540d50070f03024111110203aa050207018401e45903110003040780c1207201203520742644601501745040180005120602d580060380c29041981702c0701c1c44030107800700d0001511711406980120382c480d140480c00001c0001c190042e20003602c013601c80e40440d41c4c86046560700d07216810141708a0343c000700010710258400e41d1720486406d150740700d07650400c105241414900700c019080342e13042e5a098816005185800002107113440c5810301c0301510b074102983c40420902800035454400c3c3d0300440c091250610511940400c452000c01080401d0114203000c1d010425100060b000a4100345601452a60000310641c0220504009010800c5951030840f03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 8419638 1250 8418388 8418409
    0xf0c040c21051308030a06030201080603011505010503060303090904050105040606080307030e06030c0c01140a1104050109051e1302040305061303051603091e15020601080a0b06040902060d0504050606061602 91
    0x1400c3c02038003403820003192042d80618451807550000046032400c0d0700024215440040c00188242e040008250002501d40280070444600703003000c0761a034440100003400d42c001c400c1209d420030b004c941040244081504254004c50007517804002c035a0702c58480944074411004003034041120b840e110252810100001d41e449841c83c0ca0071410590504045801e440207808460740c220024000c1c0b000c0e1408a11504011503698a411490245481c0000c0e1405c42c4034800d55101d01301640410700c1142c5030070070b18100028010984c1000e0110280c0101c001d4001d40000e07200b0380b21780d0340080d58010b00f150300c041104d81c06441d41400c202140d075000300c040607400011820018460b0000602d8095a040e601d400e0701d0010320085014181140388c440c141c449111001154420401042002000b091100e042900442041e4181c1c0c0c1d6000400c01038510140000d40000000410300e40e6002c0b254016406180b01d5000c1c1c5449807151401c0144a00032800d1003003107400e807046988014030b0120f8024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 8420888 1250 8419638 8419651
    0x7030302090d030203030a0e010b220204080118030e030a0b01050d0f0203010e0307150c05030f0405010b0306070507060b0d02220b12030a110304150503090f0f0c040c2105 75
    0x903150400700340100300280c42c012022805a80044140440c1010350b000e0200c2100111000b0002d98035030384001b51004058001703150f01e034843d110540f90290282d070111400780003501d000f4890705403404a0880c20864101041c0c00180c00054440c400d854003241c11403400e03400c28180b10703013a42084204456100302a408030f40100301e160744030005031800c2c090288242d0141c400f540d1280c01c9814039041c510031040158241c0c40c540240c4100300394100094941203485589942095903031446c019005005540000358140704030001c200040c0e038005c00500003031b0304c105003d000020f9550300380540300e40070340d00080d84a8440080304161a92000c9801c1080a0000c00030a41082840c00709070b5401c0146001d880a8100050540803190000440020a81ea5800440c9401e19020b045000c01d031440356054108000080800c3c06104c0801000c1100040072042e00c00700c8803810380d05540e0750f8281e400719016904081c00d00851030f0080f01821079180f00303c40150078020749450305c03030005c080080c041c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 8422138 1250 8420888 8420891
    0x302060a0e0a1b06030b0303040e01030605100306050c0a090602010b030703080a02030702040216060b100507020105090a08030c1606024c05060109090207030c2004020d1d0304050102070605070303 86
    0x70700403d034500c1490b10f802080c0c400c5892040c0c10000000d080d10300f8001050300a42c4100410040a481910986c1c1101c0e00706000040988880f0b02c50080c03040c40b580083c240b0350034407007400780510741c800040c0703030400850300c5204907d40c0d1000203038260340d030380402a58560801c002c00c10104160310010303e02000345105584ca488080d6002404a0b001280ca0280900c124188501004480d20a2011200081340c6188110720f105500030002d11813024000d0401c039020a1820080d102d8140c40d50140c01282d06032900c58055007130080e981c2140c0c3d00c0134545000c1035000014024008204074045644162040045800c0d06100703a86104c40e40300d120002c01c03e00100410b0b914884070f600000010036050105107410800c000410120322904403000e03440c410416180000e400044000402e031780440100c4400840702d0798041214041101d07250098000145800c8100c8281d1088100584420303020088510044da51343c0d40b0b0003030740180c0b40541e00407402072142c180200060400b1900c246030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 8423388 1250 8422138 8422153
    0x6070c02060f0a020a0203011406030304090b040b060712020114070e0111160b0711010203040e0a0c020a06020307020a06150b0f0c010605031005040204050601031406060f0c0a03020c1002010203040302060a0e 91
    0x32884140c2c0d02c03c0004100603084100768400b140b60070701400f1075185901d05180041e00744107000a0f200c0c40f443c800e021984d0ba41d40b503a11056113460304040082c0d0720091411b51286043e05040120039030b168529001546010b03048043c4c00c0036202158050714003540e442e20780c000c010f401511405480c15515030203204140300400010f550307521003400340c481e68480a40340c6a042c50081c046940204180d07040d0b400911003840858101124103600102c800350114028181c00c034140d003008490100540b99500000412001a0b00010a902401c3c400c07042001611142100498601c41c10301480b1040c00f020844a20004111406030510905c070400014545966100180c039044c3d500030308503c0551104100308c1986014411503a0042e401e08080c8034040c40782d0380ea0006040e004201603c6440301240c02000b40d41c82005564030101068111602d40c425410065902c41924051070f21407130b40c101245084a1040c0240c0307002d66450b4004010545681090001425040304030302141d01c00c0342c0c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 8424638 1250 8423388 8423407
    0xd0207030504120c03020a0f1401050f07021005040f0504050606070201260108070e0703050603070603020a030603020a170c01020a050304062001020307090e010906080604060f02071407150f0206070c0206 89
    0x25000c98440b8440d02c15003138241c0c40d502c140617040030564010000d00d400c0080400090381800030f0150a0042403900300c1e44c40800410f15850340c000c0f0351019411601c40d211043c0300c207400100500640e0403800c0d808224550b20303410002a110f0459902d6001001030090200550044015400902042c1501116aa41500342038410502607120994550000104022502a4503003480d082040e034502031005103030200110f40d0f1250313188150010150300280d6038020703030300c0703035014501a60f401071100c02ea4994402d0580241445c03865514481d005018400c4259800010407891f01e03a070050103035050030710706001660889071004241c3c41c2d00c1000d00121840440a1006511550154030340c4500b0b2400d20001c8105860160000c0c2c0c44a032174007909102c2120300055171030b40240d102101003921407501400300040d01038203400620180b440c0c420031591000104107e010750b096601ca0182021384004219101d880d100c2a0501503007082c408115020712540c0701c21603850001e020b642c60501e250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 8425888 1250 8424638 8424659
    0x6040302090403030507030f060b120c0d0204030302031210060c080921030703022e0203060a050d05031903020301120b0403142a1b010f020708060c1803120d0207030504 74
    0x315401c0300085d6a500c20000c000340c16100780810090304010412100d4180300c0300314038074420310a02c0c4145c07000000000d1103121200c0103d455410043e1400c3d03449a0f40c034507001e5030301e0700445a0042d501c40860009610400280d144200302c075001d5a68201002064462102c0f40d404100684e0b00048071a0010b4480d204039280c640070342e14814021586c40200b41002801d100410408044c0c02c450030346118880c2c0c004900b21040720418040c010390320303110079000a100c82d02d0783d80140e400900b059100c40c1031180110143c003020380104103000001d40c82520860032444240600b504101c06028003a001c20044206e9681c064883e040c019404004010610078075082030310b000c2403070b82c0d241100c0c2120701c04800c02c07030384201a94801001440314030090000c80034000c0d0043c80c10828003c0718044402e2082048800070001141035507003508020041d4941a0700040c00818941406032886015040001e681c0d07482d2101900481d080420042c00000a50701184d4150b08100c0184004a45c85058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 8427138 1250 8425888 8425891
    0x80d0905011802030d0e030615030708071203020f120409020f120f100902031302040b0102070b030702030a08060f030703062f0c0111031003020906010c080a0e0a080106061b020604030209 82
    0x1401c03a80c0305540c0b8103204061415144001003004c021009000301003648001440c03030703000764028000c02c81c3d64201c540440c0c6014826445040248203843c00000d500340c404030008010b500903400c2c3e844414450303005696400804100f00c11400041104100310f40c001d03800382088100080050707241c51184950030203411001e0340e0b541c2c04000458280302e201c90380c07111070000500414100f9030551401e030607414505148940081e0281e5100d00e2401c1f500c2c4c0c4240410310141c5620509191030b0b00388400029a01e41240b0391000102d41100d001c64028580f0248030f41201100500400505056549803070140c0800020069044214002d40321040e0403522001c040c1c5090360f1200340c43c0c1ea00011511f0a651044043e1500240100240b0034928907c000c6841600e030186e070018043e0b155400101c0c0d800b0040e982c040c1c0982c00204120440551064101c3d1010200300c0345000134580300d0004a01700e07000d5201e490041840c10100c05075004194000c7ca0307509000400584c24643c4da07401041540d0310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 8428388 1250 8427138 8427161
    0x1020705010e0607020703030503011a0c060f010302010914090a0c030e0d080406050109021c05040f06020301090506090703110a14040906060903060f05070905010c05012007060608060c07080d090501 87
    0x44401c070324410b003601081201da00c582c103407000748601850354401a1031440306008142d159003983c0c2d000c10081d1003034002c83d000101030404a820501d481600080e41540070300040313000486000c00029a1591b00200d0030448000421019450300c56411707a01c020304600c0061401c0c962582e003134440f42c901c2031010030800460758480c11401e20381484c080017214016000b4040d898414081e1281503004c0032004002c032a5514030008868841381090b401203c0782d910010007260000002250003202da41203103000e19001e039841c00e080e40b21312406030250b0380d810f00311001594081c0454541c141c4640102403c041021401e10315090301c0320b030b040080c1d9580d500481e012800c41c200030001c01c205c0d845180c1c5101d240010420036410001402013100259111340d41c1044800001403007401030039880080080c0e2100311611203040c0c01904178149400c00c0800384c1d1951702d040c00c000303400d03800420824803441040300010325101c480d980e51041074224544403107400d60303603100a20028070244682e200c800c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 8429638 1250 8428388 8428391
    0xa0609060306080303010311060c0c0d080403062306240403050c0a09020a0206041113141501090311060309031c09020a050f0a030303020c010e01090605160f020607050310080102070501 81
    0x14102080078041d40e600364041500c0b907008200420220759020083c400d8884112441a0b840c00c40848a9150030307410035280703500282c1040c4200811035150010411a80703d05418854050905800e1601c0107001804852a00d11140091042c0c45c060052200d00b81400454030004500e2500c90350031500540c204030382517071217540e46001034682241004001c01c14044194502400c07140029114030028000400400080e121106039036030f40700d02d510303041144400070050000341c48441c22000d0800c2e1103429502c091000523050329446181c0103801c0d0b80c1c01000c3c080c0c4042d002c03800c2c41102d0307000400254250006102c121a411440d05401a98a098010210312f0001600400811031711581c40310303100c2c10001f6000b00054450050031400c03241c2500f80141c403141a052503074054082003440300c25035442d26a009007080300c01e81c0080c0c002c140c402c51400310252004800d490800c44840c140c805a8441c20005954070300c03c00c0290351155900c20102d140300d507115042c03403e90304046002c45059 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 8430888 1250 8429638 8429657
    0x424020c0a1e0f08090609040207060603020a0512070b180603090106030309050612070c02040f06120611071a040318080309040509190201050f0c0d08090111040b030a05070903020a06 80
    0x84481112408606228291600e4051590703c00341039060004000b00141c1c00441d103000659114000e072201c010000d0001d44d40e814007440e01000802d2140000c0f48070f480820808209810300200c072440f00408600100301c0242050303100340041e008000003201c2d40c50540c0c004140c079110440a1802184050000700f0032505515000c0c2c84484903810807400781105004801c40c0f0f411501d035003900006281420031480b051400450050520031907801c1c405410180002015058401204240c900558041000d0703806009020310070300c074503080900b09808440c2c3c0000800580f4070059003151103030070802ca0411000e40038160004040d13010450b550004281040c641c00c182c024550700c450980c000d000e000500d4010300101d00385031040641008401300e0119a0440c0c03101c2201c15a040d034504681070042810002481c1d01c0b42100c201c6459400c0c0b030b103805e031003082d00015102606d419040d01d038199500c40e40c0c0000241801041c18041040c201000405602c40719081e80c080e0031180e6070a03901d07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 8432138 1250 8430888 8430893
    0xf03070f0e0108070c0f05030301080f010b030102120609070306030c09060302030d0903030807050a090308040807050a06090803030c0c0c090a021317101515020703030e010201050f0424020c0a 84
    0x1444a000880300900c8951006100c55a903c50b512079403240c1a4103110101602908001c0460795a9480051503440001f0011640c0702c40050f06c3c81d008500100203100a0a2608c02d02d800d074040c400c0e036044060021404a1020b14000610590103c41c40c600000c1c2e0302d5603500c68280c1103040da40b00d128110741d0b9034000d0081d4207040c4240d002d0303036110b402d01d413440504e19613000b03044071401850700040103c04900b11070450b2154060200840d00101030313903255a110380c0c2098580f800381c447c00d44101650300d40083c8050080300003404481e040405075003540d540002180d500d900c12031480e04d56001d0000964000d6590024181c0503034641040180c41d0403c4040300400f0b200b464120a003c2024082c0c5031282c90381c0062003a046540c20003020030355040b15030340c558004140303030440c05002c45442840701c1c0450340010140101c07402551000e207010700030401a400c885040e0341c1f284071003a81400107000b18840c110451035241d5030701040f140580d0070000500481e00002104003207500704491304400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 8433388 1250 8432138 8432147
    0x703110114181c020303070b09190506010501030b0a08100903030b0409050304120606030c03030503040c0605090f040b03030c01020f030412030506060a03050405011103071e030501060e01030506040f020f0307 91
    0x186101d111440c5810240021800941c0001c0e801c03c0c03049a5142041129407094111104699805011647c582c40b942c13521040111080f00c8514040c410403907010320711007180d8007001d411600200a41003607428400118040c0213440041904640151000281074008000c46002c0302c03d00c04c80023a105080d0300e00181035a1781c8490780380c895414401c400010510101c00c660403100808421302900741140b4041000c1c01c5181d00160100c10341110003c00d1542103402580302da445070031800105916034030155001d0081c0f05d0100d070494000d001034041800d05078400b046051004040b43e0030080070240b41d0b030aa80c060107071f0005024001c42840200300b541e03921a96070061390700701031001c2c0c600313031020680130f00a00c00260101903c860214040c02029482030469214002d10381c0c1c0c0e249040000501410b00070030104881c903c0c440c0c0a20040c42c401d10605043c2d912986c0d614a00fa520f460045010341000b80c036542d4050740e01d46029003400541e100402124848401040d02c2c0d00e88440c0150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 8434638 1250 8433388 8433407
    0x30c050a14011b0e012a05060c0c0d0c0c0b030714040f03050c03070506030f1b0403120807020f0706030c02070e01030c150504051f02030c01050a0506031b10050a020f07031101 77
    0x105014007090340480b10380c0c200080354007001400d086c449001040c521031014566a81d00702608a0062170284a0302c07020a60041c000080c40c0c004449511a44840c00c4921049414000c0c01c035010204084c0706015031000295000703c0d291510030038406c5c80e0440307082c1c9940503038007003941c90707861500400411506212100c050780301203000d0a0758038546800308246220003030054040c290740346c00096610701ca1660301568680c00800c55515a07449242070020a080703000c3e0500810380400002d0643c510004100a0041201001d0a81503151080a4011300804280c0d20250301400d50007050903060389401a00840c003e40da40701819140c6040c13500313030f4260003140c41c00b001001c004c01c3c4001d0b260b1800361444501c100940d51901f01c0d245000f01d0841c020744a080c000c42d401c01d418028074541e43e42106008450403002d940c2d01d42d0300a0001c1d1b5000c0c4040125603003100045980c42110760003407001d0260042d2a0041e904002d03101c00d0b03164144030091304100c40c06080c0c8c083390442540d00c0300258 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 8435888 1250 8434638 8434691
    0x90501050f0402130902030c130602060105040f0b0d1104060306050c03100602070b03150609040203040b010305010b040207030e060309070f0611010507030218040c0203160501050f07020a020a03030c050a1401 91
    0x4514184c01609011024106406485001ca400001081d0050f45006c202c4040002c2d001c40e5804440d22114025180ca10030b2090b81c1c0b007903041940c03005e003820861190001ca490000c1071f0351440780c21a03441e00780c0e800c80740c603040794404d03615000040851443c0c00707124030804c54140b0304c1e40d403441c24417038071a5001210382000c41154803000d0140a40c1a02808a94201c01504200061456044000f4400e4482c148540760481c1c004424042000071089050703050746c5c4124000c0c06118422414042207004240340500002e400150a99039414000c1c010741e040b100c014196103503940c82e0a518005a501070340b0803030025250b50681031406c1400c0c410310b500501c1518096140600e500d0304103007200e000c0300f039040c4030f42c2d50342c41c00c0c0007104e00030801c03541080061011340f8032010403410414001d2a048884101907941c020000342c54a10101390040c603d83e0050031800380c80c3c2140c0b41101d03405118201255507214640c0d40b02e010036403c1201d404000168800440c044040da10004940e100c0c50584 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 8437138 1250 8435888 8435891
    0x105090105090a020114030603210702010905060a050405061c0606080906010504090c05041d060109060e0c0403020a0308030a0b04020f07110d0305031b0d06060804031b0203030a0804031701090501050f04 89
    0x340186e90103184614503030b0700c3c41c207002e4480d110000040c1c18682c4542d40801501c04650800e03550512400240c00003074000d1705c2da52206903580e0705119041c8200035196002074010001484986000000351070440c121007840200c0c40451a182c600f150000d41101000c500da805c20441c04c42e204002440c0503003801d5800340310568466860700c0c0050014040c080c825500d0f1052065001849024004280d1209040710041c0d6581d0b4100c800905140c016102c0b0039059400244009140404860490764080c201d903112510319107a100071604054442080c06803a81c0c186001c550360343c0040c0483c3d1415003440b69880320707036203007400404065802880c0900f0302c3c04c0414011a4219040d283d020030890505c440950340990b13460031a12510050005e0a4940000441c581c0d030703c550703040e10480c40f90f00d454983c00c50304041180540b06901000b136041c0c0c801c02c1031208540c8502d101c02e800a1082c01d00c105042181da1500b02c2200090b004400f1103561140100070601e000819a912814260340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 8438388 1250 8437138 8437153
    0xb0406050306040b01020a0b25030e060a090201090305150f0a0902090402040b0301060302090c1803030313031d1305060418050304050d0212030706050105040606050f0901081009090302010509010509 87
    0x40036025010042080d4412030b80c84100e2002c0c0d0b4028004041c204d0f40c0182607980f64174000c5000b81014400e41845211a0715206030b221042e4000c0c41400d01003692500208440d42d40d105140d030107808080d1080b410001d45550000000d0401c1000402c2a140406100310b2454003001c20254280d00402440302281003010180168a4080702c20f50003903015640440c06204400c0480d0140040c1d9000a4100444d80100000c0046400140100d88a40028068a01c0441041680d08d00007a030741d424480d1040c02541e40084c0c019184d000074100a90f40928035004500c000601c0310b10b40b02c10b500d030810b072103104100d103c2c513051041240c0840400c0c01d03902410503680f95240d0781e0089000d180e0080300d000ca00b00c020756a540c00c0900c51412400c0844c0d81c0c5032454607103500584000c0c800d6900660600c180801c003980290b060741c03208038600780d81c681441c4144004544d0b150b406440e00d0400d0340300403004035900c1c1c0c050049450160098002081d1414481540303800c40e5002420010310340c22001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 8439638 1250 8438388 8438399
    0x201180605090108090102040b0f07020a05010903031b1509080d050109050c0405060c0703050f0f060603120d020901030b04020417191109040615120201020c0a0b0a11010603050a0503040f0b04 84
    0x1c060b2410210300713282c07064180d40c86078005402840341d504018100040070560200018801c00181001442034031040c0007240e441c0010344240016010003400316900f2100303032081400540818441502440c91800d4003105049404100c440000080e40c112400085000030148079014081c01070940110401035840e00352003a40f418040c80c0112482000001080700c2032540400c4070030040c54200003503a000c54491480940d03a00b0183c5030b1682c05010f030f80001441460089144c6207203451002400d0701e48541526844000c0d070092540078141503480c05070182030346640c07003c0c00240c40001c3d003070352900e25208103983c601068080401104050903a844002070000c0740a548184000d6600000c00d440c0d610381407014050790400c4c54042d1100000004514002d40da4542445000307809662100316a001030200340c4106008084251a0400c0701003002c600c1003d100703190045250001450306e8a0f66a550702b003c0045006407455800031405100701203207440b0200041c005a0031880c0b405241c030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 8440888 1250 8439638 8439647
    0x301150609060c060b0301060618120f02010e010c050607030203010f0902041508060310090602070605010e1005090c0705120415110a0303150e04031706010e150d0e060f0402011806 79
    0x2406207a0400c003002441c0010040c05030030041170705800034000d1040541707610b0020200365006014004840c0361100010302089048081c03061250442c420421a080c01d80056803c99801c81030f41b410001c011116101140701800024011041540c0261342c4e54540464802d81c0d06a58008100303e40c4100300421410729601051030500f1500d04115501e40ea4a200003810201c801e00a043e10a0400e0030398401c00103540d00418a8070300c0f6072810440c90362102c081c06030280003250751420b421300504042c0120300d031001074150b011409414181c61302d0429607076242030242ca0128030106140100e010301050144007a070705254003007454603006003800e207044540c0d50b40d5044005000d05680c3d48103c0d10f150300300c1a8550103410302071200e101d1418203140043c8006581421440c090308103001144041d0710039a8021000c080050040c01d050701c00440c131540760f900a0034003800301c40c1d40308e141000350302050010501c580b209450a0200d840c01340009062101ea070200001441030410060000c5070b0030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 8442138 1250 8440888 8440907
    0x11b05030a05070504050a080709153203030a03050a05010b030606030f0c04030609080711060906040b210405070f05060a08130c0308032a0f03010501050a0c0b010f030203011506 78
    0x31900442d150300c40304001e0700c003403145405c1141c004000d000c0100702484001041000c944402c1c20030029950005504010707800d65004903484242401e401014088034252424a0040b481c004034412260101c006443d6030f0241042c4008292218108a050b54140c8201c0c0c0c01803002c0f50075646145042d03c0010780e6448020700004400350048081076540000d40e01341c0340070b907500100c01c110002540c00c00341c400343c2212800701d5464001d214a17900780d0030241c05641c1c1213400540b003182040d0500c0742c60b0107142c02100d21410901304600301e01c40d1480082c01031034081c502801c06030141c0c40c03c280d41c03038000e03035520782100b4082e080801190003840e41c0800d607030350f1001c1034201e03122480e066071914001c2120740794401b0382003940102c180079038106607690480e00554000c000350b50b031080008030f140705405400b940d8180c081041c0010003182d4042c500a182191141c80c0c00080e0003090f46da01e0440c02d03403c1e080b0b5001081946014030441c1000d00c2f40c407054030304c0c0c2c24140038458500700c0020303e40a072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 8443388 1250 8442138 8442151
    0x60e120a120f03060b0409050f0907080705010509040f020409060302030d1409040c05070b09070f1205060105011b0c080102070303111813140c0901090f0803040506130e041103011b0503 81
    0xc1c5401c1c0c80a88070b110760300c4000a003110025042e41c61f03956080c000050324040d140b007840307501d254002c01c03c0224005089001c641d03654003d031000615180054034190403594006411540b140c4104e000d8000070310050000d0031802c01300203056411801410302d0f0007100800c3c1d80610845110b085840800d4030107456244004032008101ca00e843d800403104e50142c4000205050010f80501c4090039010602c1d0046d151781d69081e0904070741c2c0d010f8000142c8601e04000d495500840700601095100f401000c0070301e80c0c91480d1000c00200350345d43d8810700c6641d074030403100e0b6540440c82c1410103a1500608006103203071014a4102029001c4035580c6907500c2907510300c240c0000290f140d403007038140c009200c0c160a04110042a16010f5100c00b400c0c1e0080702c01c01c0c005810300e000803d2030b00021800e08103503a42c10300190b00f8281010280181c65000c400e0707944803020104000101d5401840c48244507134441c1d04200c40d0b034100c24082c5401c0d1842229050750070416030140710f001c2c07540901501d50121 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 8444638 1250 8443388 8443397
    0x60603070804110a05030105040605010e070f051804021605010c020705060301031e030216060c140a0308070c050c0a0605072f15070204060b0301031a010501050304030c05011401060e120a12 83
    0x54080b000844441141c0d11846d0954240b80800041c00180c0e84000e040381d503110144526035030b4104003111242034207092000816030500c0800c20802d151403001d1075000d800340c401031400d00009080c00150102c040100d4140e0b44800c00380c107809074180036500041c2030944106041d0750450340d445c0947c11100c140103141c04104050003050610030000c3e00300f01d00348190b4070601d6903103905d03000780b1518003134500b81d4005015840fa0302100400181a490490f015510050682c582c13038003c80d111ba44520045c1c540d0312800c0c159004507501c0d00d83c1e20000385140d840380e0703640701d14902e0a028010b030a045103844148802600034500c680a840c6c200d0000e00407036044107103078482c00c0454410300800c400690460f241c01000304444140c02c00440c1a03d001d1107904160300102c6034845481c4009000e0140018400d00104001a010312000f252091290002080c110ba085d41d980454140c241c0c070280c0000e49004100b00d46040403030800c0312090368400500910451034840c0a4000c403007804000401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 8445888 1250 8444638 8444663
    0x3060a060302070f0204020315010806090601050a0c03090503070b0301230102031608040803030115112406042d0c0e0604050f0a080f010c03050603240a0b0a030515060603070804 78
    0x3040e448196541350358020310440d140c2c10041142e8000e48101d00d03545001c80d100c01e000c25494a0041072a91003500140e480700e24041c0a008101e1341580b803000c045051181c0e840001c5400c0e03401780250700c0900034034032101d6105d41c90030500206160400000e900106040c52115103a643e000c4116483c450301203400070214129807901d004c242c400c80d4805000303400040004110f03400602c4400c0404000b541d200008810394401e111f0701c4054060194004c0716412500050b0481049220b5506c01801000000c2d800200710300e2a10010ba03540c1c40000e401814201d401c1350f20240e1151940403800391404460501401000c5151440380f405058840c1148150002060b61490710020141c01c0400c01d50b00c2280800031054041e2880d0942d01c00820304080c00110316007400103591550060350981c00420541ca411146014240074011104131500d403400c04940382c4441071280000c500c61401020744020650918101c054041d09851040008205021003664401620380d0007030b82018451160 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 8447138 1250 8445888 8445893
    0xa030305100504090606050102060619060305060d0f050f07080f030d02030c040f06090515030c09100210140604060914180a0b040305070b0108030903120d06030516090b0102010203060a06030207 85
    0x100c616503102c254841e0516800108018440c2c000c1c00403680d00380c0031100e40740c841c04108102144220a40900400d84400c02c0110b50301c03030703040960480c20107850455070740c0303045d1a03d00c5003154821080e14550301200e03007100d0108041000b4401020001c014041c0c091043d45010b44174441c0c1d20150007050780100125000035445000c1314000c010141244c0b05290380c034040900940c45030f100f05403003800d0780000100c0003001c88084900c24040e12070040d140841490030003000681401c000300031841070500640080c4560320900c1d18418801404c0013540c5811420071081e00c8054021840c6a420100d0403140b5a660404c06038100d04240401c0000501c0707041c41d01d2904040540c050958400741062109068000000701502030195100c100030782e0b04da0031803a55070302c100d14070140c1640c02840815851007500b0060800004140c001190456a985455141410b070600449201700a0704e02086508040d02c5204042c1400703000a600710b25202000900c031030030911400043c1500002d80008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 8448388 1250 8447138 8447161
    0x703030905031b0f010c051303030f030f020a030f0b06070201020d050a03020f040b030601020f060103020901050d060e060901050601020f0607080406091b08010606030f020301030b0105062104081207050702030a030305 95
    0x21001c140e40d0004288648021155954208072108084c495113040903010310380344900c04881c0b0112054131028012451070340c00316100c02c4081a80010180d644c044810441c03541c0c00140f032403040d10f03980403d5201c45a2180c00888540c2001c3c0d80c803c1d4020042080140d801113a0b4020010460400544500007000241c01030b02c41c070707405580c1e58130002801252070022000071b540540403e17030849070a07a006c1039804d90341d65000e0001a501c60045c00c010001450110a4000f94511500d404140528801c001d03e02e0640c0684449109944810030003075956410000422803030b003000000c02e81170411f114094510031001d003000d403035291200e11000500001c1040e010b0111900c11140408075941d003a030900070140c500901c0000707070501031110701c081064000d40b4103981e0003800d581000c0c0d1070441044841d81c0035a007a0b805807010f09158071005240020001d20403800788410540d00c1444603810107450b40d00a0182051010520500000d41c07400030310301c2e840c1641030500140d5611100c4101c0c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 8449638 1250 8448388 8448397
    0x30403140a081504090302070504020d0605030102040b07060e03190309020d2009010b09012a1b0e0612060a050a0b030f01020c06010801060b1804020702060705010c110f03070303090503 81
    0x14000070140011036005120910039104075004118a00c006030410003070321455803010303005070f109140034841403a0690051440e00c82444c400201136a51300042401e80c1c00550180c80e061a012400b401444aa80513040361080940f001d1072804042c408400e1800103801c1c41c05041550303c01100086441e01d01c5040000da400914480c042e140890480c020044a9025140503008441c0009004040103003900c0380e1000507100d802450501c551006203100040074a40115054440c6a001107000b002c001c0c4030620b40c5170f10030b400310b81c20300542000c00600a08414060f0200c40c41000c0410004070b011a00700c200060b0114103503c80c0c1e0a4070000c0c1005100640c0d06005a00c0c840b144444154002c040c80c00c1c07000142d5415a1343c3e260361900b2030716148200c9000142c100421080c2921081c064140540700900050404051740c001c030782c285e04000c0084030242e40d60b020140030310350030048010003619900c004000584000440948902513410700809054442c0b0314082004028000e86 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 8450888 1250 8449638 8449667
    0x30303021809040503180906030c0f03100608060702070501090b0a0813060c0309020a090501030b07120204121103010b0a03021e0109031506050a0605070f030f0c06060b130902090306010b030403 85
    0x5042a00f064213103e9102d50200c00303141413946041980c6060790424103100d038801c00008000d00350069500b4207001805c0992140c0d44d0b1305020368614024a150940b20340d001400e55000140b1191131300c00000303481e10b07402e074010505200041c1d404211130143e07202120100074191816032016100c101c080c0300180881c0000802240c00c0000034640789a243d400f00500500844418120316035810954040311003c0c0800390159130814006009a4002c10699641d601e0702c680040c41c1a59a10005105440c1c10fa0219090300c104031181c0d02519007401011131480e0111987c40480d031941e0300183c0441103c0015014901c156404005140e0003004020700441d0070000505d9143e60303101c00c0e03900a040300c0c080e25200b2550700e0004036105100e4010340d00841e60001503241007003d551001c2c3c908000030352803841002f40f007601034070020304e480c000c0f0307401015141d0000e80c4483d4035207007410104070290800e041a61041c030000e04103030f80020300c507030440c0e00b03501002e0303500e48507030a00b120b00305c1c40708020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 8452138 1250 8450888 8450899
    0x30902180412031409070603050c070b010f030201030e010b0907030c020703020a120c0608090c090a110d05040605010506070309050d0f0f0b010509010b090609041a0a030302100b03030a090303030218 87
    0x7044140a8201030050400c4225901003202e0402c440c40000c0302d507002d41341c18000b40d1280701d003030080c68080e41c81103030450f50b220303111808d103403039a43c4007521310500340c01c040e4500d504184200215600350140180008030500240180b4a040c00801c5040100801701d03c1055281c810750a002402440b40e2006150040c0400d01da554a0b43c21043c00d00d0174400044030b482090010026429100d4a00240030b400c440c5d0150070503000035000c014140d2809450029001c0e9603401a50903a000e441c01065010207114011400346040d09000d0111101648210302811040015500207035101c0c52600558004443c1b4034110040c500300881e003a9000740700100108404d01000341800a082c40440c12100b0841c1c0100844c2c0c0c1302d6010008600844401d1504641c0900c12000b81e450240c121340c0340c0100409000d8a40303165540003a00010b000da000394050f8000c3c581d1401a600c0794044c05120b288240e009600d0703c65030a10060062040d84800b8041581c0465007100006c104000c400440000500c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 8453244 1106 8452138 8452141
    0x20711061204150204090c08040302010c02070513050a0b0904080705010c0e011d0d020301050a090303050603060709170c04020f03011806080601120f0506160206070302040b040603090218 82
    0x41d0714a40580178007000c07844403071521500c098014503a40f062994205030601a086498202e4010210b402003d4140034a0301d80820070110f0b104658000135444e40c9030064000144280c00102d42c1c0440c41109010501c142c16029000040c06a0020040d0307040c196400e07900710110320703511804569115401601802c030182001003444015266071410829a40080c0c03c5500803503075030079019600d8402c0c0701416407510640307a0000041d00144000c6c103004201a004802074420400031201c0200c042d00200c9043c03182c100880c0001c1c00654076240085420045600b00b4020002441c00d14814044000c040d802400103e0301804098001c0d64281181401c08094034001aa87d1104c005200350014000b045402d109442611203c2400301114400034104507010380350404040c01032006110f0418010100c40480e026401c000829841c1c1e03201080c000a03001c45645e4442d842d000 = true := by decide +kernel

theorem cover : BRFrame.Cov 8273388 8453244 := by
  have h0 := BRFrame.cov_init 8273388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8273388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8273388 ≤ n) (h2 : n < 8453244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
