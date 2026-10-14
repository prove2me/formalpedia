-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1843
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:52:43.085368+00:00
-- url     : https://prove2.me/submissions/a1434fb8-571a-4bcb-8cc4-9dee7d4fceab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 331294964 ≤ n < 331474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 331296214 1250 331294964 331294969
    0x503010305100c0507020609010903050303070e031b0609012007240c0809010f0e04050c09030d050315150d050109020324031213090905070509070201050402210a0501060e06 76
    0x200903003a0510490702e4403c0c1810710303a0300003082d140f0098040d6400c0e41c4400a0200594207103240b40c101521500c400700c00c10030340c0780e84000c94100c2c03144280c080c0c941c0d06502d8580ca000c16400b400499610000c140320307030003495105c0c05644103810b030b041c05082c51129805401604044064205442c0c80200c0005181c03810940e00003080181518a482c580144858864400b280581c0000d02d0400c400c01c00008041031050000c54a5000c0041c42000617041c54038500400743d021924190090040d901c096420f20b001d5410349110300d8040c80400c150b031103400108104a10200f08850410406006141c00f0356158440e0f10b0181c1914840140d40c0d0520346650b4180080a0201301150501a00c01c1042600c0c007052916a40c10319003401f64803042c0d419140104001d807a00709280307840c60a4820b0060060020b1420200c4d00123440f150100e440d2100207d080e210704441c0650842d100c048940f80f10400408040d0082040350190f421680384c5643d028259895603002600c0403030345e00140002c03407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 331297464 1250 331296214 331296223
    0x40306022101090c110f07050603070908100e121e070f1b1e0513020d0902030d050a0905010306031a09030d090b06030c010302120c030c0d02040b12090705060d0e0f010504030503010305 81
    0x1245039002450081b2640d403003e580c0320074500403035000780e4002c030128008600500c0e815000d410b00f40d05840d03074024400c894078000c01c900c0c0002c04103841209100031005070540c044a81400144440100c886c5400d075202d416035202c0c0c84201c440e002405128004201c4a84850000154006070345541524015070666016243e069891002e0200703001081540e440300b4050031000342080b00541c540075590794040051604000194040c05038156030000c00354040010b201d0b07005c0d0360700c600c2100740e00c41f00110300326011400010413050006031000240ca080a0840f0741c090502c4080700d18000e500c1305203038155070751554210f800b5440c400510500f890240301c26101c00da000c1c6021410240c1400a108005030041c101c440348603400004654522403400454540500c4588159940d41d69004240aa03030b10502001c5480c50700d010200d82442c10100702c0382c048503070081403141812810140f600007071071041048041842140800300b142d40013030007510f00c01ea000352038060300c9600d1410300c1c9040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 331298714 1250 331297464 331297487
    0x312190606020601081e0106080708030307080703060506090f0a0b0408012a050304020d0c050d110f1203190302070c06090501080c03060117131407080c060708040306022101090c 78
    0x2d54000c0302c014002c1100010390030320240341e4000200070040120360028010034a07500a4030440c052440080b40c103030310000086018017940e9a07a003040e070350f480d8412000c403840d90051942c001800c010114462030107091130182c900000749241c0701c0341d90b00c03030500107280c1c06540084900d035107400c2d482145280c5010a50540d40000301a07078550081640300034a580b01c0180f00910800315100742c4801c1c40041210301020b41005404405001c2440c20180308541c21104030314402ea441c0c0601695a06022189107596140c0d8070065041c500c40105410603490629035101c10950301703000100c08100d0300407603072000303041580740c464190341880b000406201000700400e0700e6200c104107000059a1041d4299088801d4041c901c4660b281d2401080b8800070100c000381808a00001c41142c29001142440895040000302c4046140c07280034409a802940fa015101c0c0106000070804903200c5d0300101a003802c610404e00500119105114000c5802e03001000520756605542025680100042c4103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 331299964 1250 331298714 331298717
    0x311070f030209040b0c04080307081201080a121b0c0914060901030f060b01051b011b1103030105090a0608030a0c1704120f02040e12070c0902190309050312190606 72
    0xc91030450300803800034040a04000d008242c11800200701a1185055801400114083c0e9681c0d01c2203003000304564001065450082e0248400000c070000c3c00110301d101141e01c003804c90050000c00304169000c258000e6142d502c0301240300364800103440c107c04074010b003210b64000502403050104c07041c03480c140102410b00410401f030051010502403c048a0200d81c81140031440c1c181d64401210036006241c849000740904c007401c4000e0702010b4022a064070109400a4036480b12a00d0884050b1200206003001c0c2c1c008000520041c05c008607403d40c40f044180d40416180d54031042d203495580407101c280009907040842004100780145096541d120f51600b5500b440e06000503d001900a80d400a01500305d0714118400c544642e040740303035401911803c5d14200212201c1c0031000f035104900c100d8000c5080703e00440c06410b5031090364441003c10501d40c4c14030520303440c1038008241c247d509a03500d22090100e80c080c1011704004901c1004002c546a940c0300d554400c007016501503401203070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 331301214 1250 331299964 331299989
    0x140c010305100306050405150103080702040507031e1d07030507090c0c12050304151109090604050412050f1c061d0c090d140d02030304210207090225031107 69
    0x51211200c4808010f40b40c20000005558842d80b0f055890f00100007004a48110050300000170301001401404946000f945c0a1115039203131304040301125560714010702c44c0790001120301d62140c2241e00048844641c240c001c000c10107581040d92600401e6401181c2e40e13445803409000b50609805641c0108500f0306140d00f107044103aa40202c00c8034080c5002c0304214000c0300107070501c009501c400c07500310707400c09040085a10b0031441070461344c452465140662104008990035040622030b0604c01da8200302d9210070810b503910b003100c055100c004001c844507418440071210f90a140c04030b0001c030480010000300649000107030b03010f00e141800792100000001c400c200480c40c40408481c00040c2c01c50b003003610b5060703615003405a05a0414454254031540e403043d00c81e281c00000640c000c43c05401f00c58010084251640540c01d5030000080050700000c10400c21101503401400910442000c015002d010003071104801d200154420340024803000c8155010b400240000c201410542c540c44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 331302464 1250 331301214 331301221
    0x91a0a11060103080d1e0606020c01090509010e0c0306031f1a01030c1e02010905010609050109050907030305040e040f29090c060304141f020919050102100b0a080307140c010305 78
    0x40c4035502401c05c5a040190310341d01c450140100700034078945020401207080040c1500d8210095882405841841c0414020b14005c84c0300d191102e5024101c8520b0500340b02c0a90b82c40c00030200a400203010990544a0fa01d00000740b00c222043c500c2946205240000340e000103442002e9001c180030780541e0525250401b00c0c0b851650085071030f101c0030004424003240102c10602280104800480501907528003940401c1d0510b903500f14604036001000705124a071103182c3c01d56150555444010081034041100b001304a002d00c0005034064007803040600c40302c1d015200c400c0d40380340c200044480c00c1d10181020209080d142003140d04803414000915000c0001000f14a03144000f07000a03245a42141000c9500c11713042114208407000a010b1040c054a9a10034801039044031107200e02c03490640c110318031b03d400c01f10764103011581c0580c024003201468440c294001d14016103103541012048501281d00300e010002844002c1c0f0070854013200b8800c85c4881401d18959840b0b0030304160820061 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 331303714 1250 331302464 331302473
    0x506060906090108060a0f140301061a0a080c1c0b012a03050c03070507061101180206030403120b090903090a080105040c030320061602010f0908030c0a091a0a11060103 74
    0x40d101d40081c00e0030410026115280000d842c4012544054110a1740647c0404d40307060300500c0804080c410b5000344041c2c0d85811074074840500c1e40100b2820b400c1c090041007a9180704003a0682c210581ca021a480c081b038151036240b04091040e020310380651561001030081d40e1140c465200c0d6200e000d207c44107001c13030010340c008100840d06d0240400001180c1c070410800c0074011201000d5020084a00302542c40f440981603032100c8140c854294a094620802c00b0424071600780220b80c010040c03451540c0d90340d025a5030046060000c0300e82592003402450903203461000350b0044051000640e11038078003504001d182d010a0b000483c0c0d0f030741040213200001c0d00c05044217050703d0740340c00c1c030040b803030840b504a032268000810a041d251040c1d0082c001001d8400e00d500d01c003000b15a000380501e002c054612402e60305a284010001d0f01c0c2000062a0002c1140c007400c1c01005601c1d01c800056642c00029541020070741106480c020000340f07901c480c5400000c00f9000328141d6026041940c50360700c0c2d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 331304964 1250 331303714 331303717
    0x3021608190203010b030a1a01060206040312050703020d0f1505030c15030403021501120c150e061b0105040b062b060504030c050d020106060906030e072309090d02010506060906 78
    0x6103050080314030300710030303045550a410040101e03070060101c0d00000028140114404241c05001c241095250008512144041503080c45503806840340d000c03103c415440d803001400c0090800007015070078040c18203840024002da4401da80500b602040051110301882c191103501c0c1c0c01030f480b9901c002019043c035100d1130801e5440d9203000c034206490307507100d0030164100320581700140010160200045001e00ca440b000c005854040c404403249075440d4089000e1b8144000c0425000c40d00040c00e010640c80c0c21002480070210900380521440481680c5a081d540103440840d00c66001030300b08101820851424209145c19031074055107003241000b803850300c0748031074009400203032210700103810f040c060003a8640b075551241c1240c00324084104028000d240742c1c02007000150781d08100084c1540709000f898900804000a404d07280c0c41c0c5071921705605100c003081c2044844403005070100740d44001465209002c1e042c0500742000098900a0031114010446403003010180400d032203e445000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 331306214 1250 331304964 331304983
    0xc0309051014270405150907140a020f0c0103020906030705030603010204030b011212090b0904091704081b0301050709150903080c070819021f03180f03021608 70
    0x1248620105030300e100490309240e40e01c280074038500001074298504a40901040b05004800318035901a60f2800200300c141c1d64166201500f8082009140d441454a40d80403a04200c1c170342080c0d20707138210f042c0da141400c2d001400b2627805600100341084074540f05111060011a09107000c620304006000000c1084c0409031514082250200c00280181c4003541113802454212042101941c0e48800ca0010100140001c40d0210311b03141010300104e00405040003074880000f1840d00b0700b804401840004c3c043c3c00c0041e2005005150b0130303400b40c1140c100900140c603c00300076050303801c501a160300b04a500c2100c018000d1b80351404002d00b80742e00c03264840c15180140c282100910321460222050140e5400c050f000107000146000c03032002c0040e00c00125228507040e50000541d00003c4d43c1d4819164201940241440c003080c022110210707056000000e603070070000360900310a01d01c02458203080c1012035448180300c001e10b05140e0100482c80b84c45040c100d0351020b8030309009660b03840303c0072038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 331307464 1250 331306214 331306219
    0x1b011a0a08280f0203060a0c0e1e01050904020d0501080a03021e0a11060c12040510020604020f04090f050d0801090501171e070911030a0518030a0f1704050d020705010c030905 77
    0x10b0701000c10080c0c0d00401070300d1035030020201c41450400000c40d400614175004040d022410642110445040051000316285804203501c030404203070324011346140e07001c0050b0a500c503600300609020b0041c288100c078080c1c00103070001c1c101e50a0628001c0d14105403105000301c3c400c3c00040d4551803070700005051190343e911800500b0090392040200c1c60502030b400807100e40e0f029030f45a00802c4641c400250040780d1040300d1050005103c81c0042c2d07142c140c02d55000c0c2d0851000a17155081c0d060603000000058420a031002090312140c0b500b6003400961032215000a5030341004024040c0d182c0682070240c00030b0703441c0c894501c08650480f650f54554030100d40031307241d2061a84c04802d1043c480d100040810440a101d10314281c11a40c1d00e5501c103c0344400014507041c0454101006d010a41250b15185c2008628107504020b0070348900011000100801c44201d03654100c503c118910f0364000c5224100410300c680f0051006800d00800383c000904100c40c8a60b83c501081d8007809001c200c8100303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 331308714 1250 331307464 331307533
    0xe01020f0d0c0309031e150b030304090203100e0a0f0605040b0105090111030d0c11120901090b0d0f02070f0302060c0309120906160b04050c0a0302060904021b011a0a08 74
    0x50300e4142d4039940f1a90010f03140c0e0174202c0c0d00b82501d8980c0302a16040c0b501c510910703118400b01221487c1114540c0342040d405a0040c0024010810f2581c0210303000310051541c01c0180d6550741c0984003092080310b50b0104180c030340340341e501c800d00035016140c05408100d80c140000e85071900000c005002d102c2503e8108101800c0180d2115000d10466143c00b01e40c210038000d214040d040a03041141c103003080d42c0c19200f102c100c03192075017852098441114050707507056802480d01a4410b02500120f440c0090955103440c24500d41886200802c17034030b8403030b070000340c02c0078064100030f0f081500060a0f81c1c01281c040042280029000c140348040d001e90f9002d181c2c55883d440080b0751a030040e6020b24400108000c0d03d0707403d002c0e9480c0c00c540700707600c10000c8900c4050000140041c402441c0700080d0042820711442c01c042c50290058030301d209018520101d21100c003280103080d1510440c0114001450b48510040b9007000046800502400e030010024035488071501d230032105101c01802820300c1c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 331309964 1250 331308714 331308737
    0xd170c0703170a0e060727060801031211100504050c030703080a1808070609292502090a0c091208040510020a170d0b030a02030a1509210e01020f0d 65
    0x180e0200d01c0e10900303101185c0c11131034400b40c060210108044030300c2032080450b142c20060248110319100351007040d69240340591840c2d54031078201400340050014001200011004014200614030118a502d4804146810142000360802d42c441d51000d000342c0001105101258420f0200c85c5540b01c14603120182607150f12910f4040f40c1281c02c11007143c000c031200003941c1503101c01d9100039074018150300703d140702103408000405008141e00184505007070101121542c84886c402c8034444080c596191140c440d84c1c00074044410486a4040c4140d0740d0300e41c51600c542c4645104094050040c0b03500f9102155111405180260f00c1080c0c0b195554182da8250980300340159407200c0d80c0b002005006d807160074590a43d0307401c03110114145d83d1404004e103241d841e001601c0e07082a50090090050b01c2843c0d02c90740c883e0040c060000b00c00d0390b01c03003517440005000400700e2810f044001c0d9070340d5242c3c00402c400034105480d16601074119808040304c007142150200b0a201d042d80781781042c041190 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 331311214 1250 331309964 331309981
    0x30a0207020319210c02210d0306170d1403090102190306090c09122a060c0506010e040210030222032604080c0f0d050d170c070317 58
    0x812000300a416010b10f10f0081e1249004246060145219001e00004000f06a000001440c0410780401c0015005585003000d410f1000884514001c903159112545501c003000e2481c004941c0c0b040344c00a0b03901d0208210071004401340078040100030010b000d480da84180005e02001c0c0140406403510300000200341282d03801d5044a0f0502c00066040d14502c03148100136004240c248030b0f00206038240080c1d91081446149003005440e056289059800c445455481c440c0c1c10140c50202a4002d0311071080a0242203d4503030000c0c04d444e61084404520351901609119042e4000094512810248401030f0745034428007083c100c8520300161901c084000011301c0c010b00c0090380c030001c0340c06003001c8180030312142c1404901204e40007a0362180406150308199100701c0c070856415030404080140c0625102250040c0c14070020194107a0061fa5241c4034100001910b403038002c035519031900070040c121690f4140c3d115140e42045400c2040710f0b100030b06000e010284c4c0c1800402c84000054144 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 331312464 1250 331311214 331311217
    0x40501060b1314120d051e031603020a0e221103060a1e0308040914090d050405040e070302030304090c0807020c222009030f0601051c1502030a2306090c030a02 70
    0xc25014007107600c01769030a98044d106a0000141c07024580c0e0a1003045c0d400c100c0b00e800c5030b00030203c805640ca003910074500308600a4100051200030044500c203985101e40d100b2200d098020086c440c07c14807103080c201243c00300e0700c07241c900901382103060040101c16500c216007001190005e81e003891603403001002c4030300d9081041e00f008082c3c50001ca40490010540c0e4050b407041491700c11032340d0503902c646181d950358510302d17004900000e400304014051820141c0000d001c0010340c0e4106c40c8a5500c036030019085405c65000110090b98034410200703a00d0380314110942105190014000514403000071035040700491031480001003102c0011804507100d40d21070140b5025140e15070584900c04409141560710144e8820310034481d840e48841411400701c2c186048610040844000011a607201c2c0401d54039242c0603181586c440006110810403030000f0b5100e17238940200060071b0404c0c1100f21401e04040b12001ca170b00700c0c140c003c20040d43c95450b001d6401c40103c0b00550345075038805d2503c1000c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 331313714 1250 331312464 331312489
    0x316050c010905010c08360118050a02030c060c030403061802040903090906050f0303030105040c0201090b101a0f0d050c0408150109060905091903020304031208040501060b1314 78
    0x3250728040c0108107001c3c043d0f01007071282136940d582c148951104c80010000c03040c1040000e83d4000c102c1000c1802c980d01803001000701c0b000c14004101c96000100402c05c4040d8442e0a0b01c2c1078101080d9001185414131003154004c40459010f4107004800780026602c1c003d03404004e040307a564504460507610549100a50540d00070020b010110083c940281a000a4498880b41d02d00380040895a03251014000051240190046040d60b00c0c0108000c05400d96052100955580d24a80c0000c108114002c610411032450031040e2946031a01d628403440d540e00f56044000b40a02443c84000281c0044446d00400071401113a90303205c0392400152881039504c1480c09204504860000d401d4140740541215941c0d4400c10080755980051401c0d6101121100036a070802010091094184160741030b071b040c042d00c100da042c07a4699555000c2d01400e207001401165050040004001090103420040c00c1c0e40c007140c6050000350700c054032038012280100d43c0c25a40340b10100c3c103a6100c0200c004107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 331314964 1250 331313714 331313737
    0x91b0315011203030e01022d040f030c0f08010207080702040c2c0301150302030307021306030611120601171602030c0303070801151103071112061513050c031605 71
    0x455a560a070716100a5442e035048003c030382800f1240c401c0c8030043c402d690485400f45114010f06000d41d011503150b03945004070500000c410301000c2052005c0805100c003444c412080306451038144200001c040049a02c07c0d600c80c2c1c010848640082e02c01802c2e03c200309e5060790302007a45403100e081030320580224410720385200204c82e1404482d00b04503540703158609090300200000903125183c040c0b4114a8000603400d40d20402030390300141002501305a801e2070415000070260345079540c074000d032837501c000c24082500100707810401040600f1300c00d81085090900c0d00c082c120051240a001e2401401d07241001ca441e51603203881c9001b88201c1d0340b0802c404003569034900e0100c402400e004400e0007520340b0000c8c070428079011a40214054110151418001d6040c000e842e48d8550307151034034180042e041a80100d1540c80c0300001c0140500450001c0c0000303118076142d030280f05c132000d465184000f5041c00c0c0018428010f0307100040300d40010015084580040b08424191154441d160200a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 331316214 1250 331314964 331315003
    0x1a12030c060a0f060501050702060a0e13020f07060507050304020a0b030a0207060510060e0105040e011a09130911030d05030c09040b0306071e090819110d030c12020303091b03 77
    0x30341e07107a143d03010030341110001d80200080d41d201c400444041c0906039000350000020002c481d0914044c0f403035950b0700c0c1c500820401e0002b010070403180c2170b41c02030800c1248580300410000c0800040c1d014544e8003910300d1400c0c609601c4d154000664101c2c40d4412030420071800004101840c0054044480b143e8004d0300510084c100b5042c0c0c1d100800302c0c2d104a00000d00c14628103a81580b0407000c45080b00c481d188412102d0742445030321040c48001300c0030ba0b140030104111422254894001c010000134180e500003840c01c1080c103000c00300c42880500349219030800110114542c0c2c00800f502c0e049264099402d4403802c00b00301080c01004080015540340c4690310070803d400303500c940380b1440d4210503449105650341c082c0c020b035100d25aa004032038558200100003054070303540e10030020404d0700071800200b00180c014045a00700058440030340000310107100e420140072500400c12400c41c114401075145103030058442e41c40301102c410050982405100d04000303543c082001d4900f1a00b0b010340507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 331317464 1250 331316214 331316221
    0x903031d03041505121807090504050c10030c050406210e061f031a060a090c0f0e09060f0d0c050a170c01110303070507080c070f0e0a1a12030c06 64
    0x80c1d6494010384260f40b421801d07072101201641c40740054801d0001d01041c42c80003915200100a21000c05165014141c17003100400606820359000d20b17401180568007611a00910000b405829004220158140b500b0b100041044d10341c40700c226412107800349007040d02208c0f84100d000a00450000c018541400c12641d01e03200d0502103071040c0034a20360b08144407440800b162501d00000f85110140c40010801034071114082e059584c5035004000070001344100380c0b200041e50844140c842858009080c4803440040316800c07041014454400300d410010a20702200040c0c0f00c2c11442c1d480c1c86c000c4281c5012503081200424900019000c0205034240c0c4503111000301643d001d40c0107990301d00d40318843c1c1d00c03403141d4080e1003040e00c1c40f81c1160141d4030b15601c0480c03c1d95554000241203c42c507a00704170240110340d003409201d02400502054104c418600503c400b080c07580500018003152422052005655000d0041f0075090030130b540d07924008030170740c00c91400c600075203032000668041c0b2400c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 331318714 1250 331317464 331317521
    0x1112040308040e130b01090c050702030114190515150f0c100501050603090a0201200106030c080609190303150902120603100b030606091803070602040305070e0403020c0103090303 79
    0x103401030b80c0500704402d41e9507952004446401e035107602e02605d8803400d0001400ba0441642004209513801e040a615010303c0d94040303800c66214146005100300580140a102004400d074032109541e10a002d01003410100c50500e90b1141c510344003813050804980c008002c80c1110705441d601020550388540b01c2d512a04201c0e01e0b600d00386001d5a6403403401c2d0004c2128070300741c403d0f640103001c03080c0202103c022690041d520405801c25002e25040880890a01e4990901420b400b46120309014003155281007819442c00e0006070040005800001c142c040e846254000001100e4042c0340111703c0070400100000725085540080043c90300009101002e83e801644c40740c0103410982c111081c8415049a41c0100d80b00001116890b402c04c0c00800e40e1454141c6561344c01c07200f04580c3c0b81c200240060007514542c80003100700d5116801190800501030f050240d00020a00d04c0c0781516640740c02e54009450346a0510042c0c1811355550020341894803d0b80048007000c805040c051084820f10b12 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 331319964 1250 331318714 331318717
    0x90509010f05100c081812120c0f010b030d0e041d030304020f010311070201080a020c01060303020f1506011b05280605010503010207030c0b0c0f131d0105060a1112040308 75
    0x42c2c00d000c1c11803010303c903200c54850f0001040507508003208505288a12110580340e11280c500d8a5004882d070780c0c00d42c916041417054403440c4d451041040e5540101c4c3e03030f889041210703605410100780d03d440d02a03401d0f91070100e2103500910140c41d00030014140b800008000b410b19400001161082180141940900100035402240201c032251544880580110262201071050340742e031481c1440810010b5000d44085900b14242500240c202484684040c1c210f4040368000d400590000c0d0300c03611892810f0007c000040000178034641d280c542440064281a60030407011003400b900981e240901038240403002420210b20300c80066065164170310841d480800da002d03298140f6040c000901e6190520841d192645d054a0750003d030030b60307a1940b020240e03000b085800801c504110b0900c03981c646000401c602500f03040021502030030070800c02003018090b0500d0f40d01d0f101c404014000c035560b203000c1e128800d0b03da103403103508000c081c064141050420072a12038411030101b0048100b10f9540c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 331321214 1250 331319964 331319969
    0xc0f21191202070f02180c0a030207060f0e0604020a090e0c0d02030118030210060609081207050f0703030305040b010501020105071205060a05090103051b0a03080f1e0c07030201090603020901020c0d03090509010f 93
    0x15651181c000041410403c6e041080c1d860520030b101c00c2100750400d03030180d00070f0720201e80910703c00a194a4420411807e44160741078504498000f02c0030001146020400d0740302501e415081003215500e942e0041e0340d1450000300151085403494403680c1199001d400c80d40b1045056040c84469824501e0080d5580a0070140c03100c0b071900300440070552510036044001200e14403801015541400302c03000105900006042e038990141d102c507070404080030002d580085120359000101c0d0302e082d00b001222800306802c030a045906003800d00107625444250342040006072100069a41c070745400165640b41740340c0c40740d6004079813600000240040420440341101900b00240901d810010401c101c0c00c120b804000d103401401e120003035240c0000c80140c03030042d400400c854040c1b484a030304010b09400c85694801e03190311180d003d200310f5911111901c010500c40c1401d5040c40c0d4500d001035200d520411810380125130781030281c1e041c54030920170900240000391600d1110350315269980c15210f05c90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 331322464 1250 331321214 331321219
    0x1509020a2c070f02190309150903061104291e0d0506090c040e07020106170109060b0a0b0f070f02040519050c03010b0a0806150c0f21191202070f02 65
    0x241c001200d50380105818040f07900303641d000c1d1a200348608828401c031600d551064080051034107010822036111084480c20920585030388160038030b0340c5415015520302140304401c08106020800154501d00210380c640c580c15022550200449100388040f0b002e041c000501041d4441c02007030b4680c0440004104003090405c007844031390365070002c1c014401029544030a58641c00c00003041340d1144004219004610751002080c8256100640c0040c016000c0b07075448140d6444880000f004461310410f030790200c003900c0c440c2403142340a04440c898007950b0505c80460b00c0000b441c01c10003504a64041019034000c000300501d040c5481c81c0c105000741036a0b25403040341f030f10000c14203003180e000076a4120341c0703001c54540c074240c040b034030803113900801501c02500040003516500c1c0c0507448402070400411080300420010391a00c2c0098604440c0e80b148650982e01a900e54604803014400c40301102c8100d04565101c294651088a200c503000c090ba40400f84003151090030400c0105900c030240e4001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 331323714 1250 331322464 331322549
    0xc0f061407141b0a0b0705060f040602041a091e060d09060b0402030f090f190204231801060b0705030403110d0609060c0906050c0616090f080d0206010b071509020a 72
    0x41795103182aa10545034003400c65032148000901030740c624151a0b5005224003405800d25581380b00c00d980040507d6074804e2200c0d80420846480d092405d41019004503503050710003080c0c4401301145451041d0799503008550b031640300c3c2c02c1c10b100c8250040b24170710700c002c0c104658910b41460b0700d03402c10a0039207a081160103276000c080d1120710006800e94402d01019078401c128000b40c3d08101c0140900f45180103807181020042e103201c95160707071661060511318011841c20010707600a600b11003030350300811640001809001c0101c2e0001091340c00340c03584142900e00d00c40e92080001c1c0b100550140c02851141081c0c012400c021041d04030304a01e050326101d8203600e035112003058900303018400301e000c5c6c1503001c0400154002c01003400c0302c0302c66085007801900c0a40f0307170040340c20301d000541120030341e58040c0c43c440044580c1081454010f101c802d211501340307a0300742d403100150f2901c80b421a41c03240d2615003e40c15552a484000010a00794202e01c502100d404a0008203900300245460302941 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 331324964 1250 331323714 331323719
    0x2010f05120105040513050109030e0f030d1220040914280b010905040e160b04050307060f030f02070614060405091002031308030f040c0f061407141b0a 67
    0x58800d81d80c008001c000c0300901682090244001405d0007440c0603a05400482d001c4040b410038898560a24002c1e40c511880000c070701e0034401004088403070359001e0303804070009044141d80300b0003500b0501c00c0040c0c0802c0c103100c45019400301c0031524101c10304001c0d001400040310880b0340d03c0200c2c03240e0190301000069951203a024070320150903404500183c02d0444c3c800900c6213035440b141c0f0784a8141400b84c402c64694010800f02c851200100501e07501210700072618426085950b001442c076011f429161504007030100e901c401c035a110b2441032049000c42110442d0080d046051002c0259408640380c0d007940c00c0c80300c06040c0084c40c20b548000c0d5880421000d04050154a2080170b0320710080c030400000350408002548002d24180d80e10064400d080002074420000314010035005a4107901070415042140321040c1d254062450080b0480041044d550800c0700e5460381240314110f161110369600701010401055003c1317030158052101150b07a83c1d4505442401030440c26100c0c01603554 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 331326214 1250 331324964 331324967
    0x106080a0c05031005010e0a080303100f08060402010c02061b060708180705010f0c02011206300201120b0303091203030a060504060f03020603061f020703060c05161106130f0302010f 80
    0x1005841c0d41c411070700c01c00c2d810305c810350291085480c7c800c4080d00c41e0703c4040e0303138080450035500199604207688026a504029039480d98a4a03409081c110000d06100e09040c1d00280c6030410301e00d4000e0180f0400314281400d80041c030102d4003205950819241c051405003401003400c0f00c00c403000003400c3d011f84d1801104e20b800060701815214180c59041c104840040e00380d5048409010403810002110380d080d000111030302403800180a9900b1000301c40c0a45201031038906005030044c10b501c035141080c0c0c1e0144c2e9005207030104607883c5000001c0e1201c2078001107070842c4034145166400c900700884908074180001700941c45824454010004113072920200800e0f00c00318851550050f891071002c3c405850700170000d58014500901c0b500d860b081c0114448600c90a0702104405a00180303010000d000700380c0181e440c541c005141051600d0601c4000144103050118050300705000340070f0000d22601c4500860b800580381803100340c02142c2e607070701d001c200200600040340020394000c900420107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 331327464 1250 331326214 331326217
    0x105190903080118020f0c0a03091a120c1b0d080c04030c03300206071209081c240512060108030a030203070c20040e0c0102031803070e0106080a0c05 66
    0x141d45070380d80500c0d03a4a0800c050707180107292210a0050ba0f8200941da00d0703115404020608400c01c0d20140c015528941009002c0e28035580c03000d030201d4a0294102d103514081c10403681152007112041e01c0c1500c480d05455035500a4600d5075410344042c0c41d29140d14135000174441d556a0441d954001e440c5d41d09c03c15203240d070249100092501002c00341c1800010040c0d500f420002450110a540183c10038100d01000c007a032100140140e001182401880c0707a105032000c01d007648460007404603c2c1c2c1c42d650f03c0d415100b145d0400c50507410480510744140340540041c015902c40c190041f11100c4541d40b02da110414920905118502c0c0b020219101c401c0412883d040f1480701c8050350500c0300280e400c0d000703903000404403400c10401101003400240b80068543e0b11400003151621401d1588082c4012107480b218086c02950100386102e14503039002048a2107040d4030044801d80c0750002c00813a02d040070b650000392a003d0790400110b0a164400344d050b01c03540820b1018070014840402c241c0d0103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 331328714 1250 331327464 331327481
    0x105090712020409020312160c080a0c06031e020d0b1e010f140c03072f060306010c0807060603121412041e2307080106050a0e13050a05010519 63
    0x103038041081c098503156010300e84160014056540843c4540100f080b540e02c0000c01e25501034107010f40c41c0520009050b88409040000010814041c071529009a01061746c81804105900c0d06c03a181e2a83c010912030301030000790395a0640d200d0464081c43c0c000381141801d9280140c8031000442c1c8221000306400010356070684039040d11150064003298023004003000f444003940b08008180310041c081009204443c022003140303520307610100c1e6007190394031002041010160071004c014500d654003011a5000102400c00a50700d0846180041c0d1038080c03c0d002038001c0e0716113080081031018510b1003c03c044550740d184420a00d910302101490702541210081488941d40010300203480c04c04c030709030000694003d4841d1140b0380c2d03480344903400d20320340d58050908a0312100c4504010411001d009044074030024030200d82040d01084000304203104d543d10010309040402d00e100300381411084416040f0054070005169410040c4c003905041d2031036203170300d0003401c65150baa8006104d034242 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 331329964 1250 331328714 331328729
    0xc0d0507050f032d1207060501031118180106090f05040b01060c080f2a0c120f060a09060b030d0503040201080a060b0306010e040f0e0a0506090102040608010b070309052101050907 79
    0x80b00811504501600c0e09204c810400500c2600c4000b00740c3c091007009030551901c6084d0128103076046140013400401420152030107030031130322401da60726015844625031080850a520820360800c4114601614041e4003100403036207005594006110240c100511036070041000c900c0a981e03644040b568002d40324030141c0080024030090030111040f500514020320007404910300e003042003050707152000409900400da0b6200003c46030440c00d0120344906408841c8010300a041081c007152915500700500c651126a40c4441001c1000856403000072207410140c11106503a4079800084e00503071064900385d01040e0440000303903150100c4e000e000c0c03c0e921410304003030450700d030400107481d6a0803030505c03250f1241d2225045c40b0304620714891061040b049a005000107080ca007803150908002514a1a0b10b1340100014004260000641c60440d00d403555146e940e040141005c5850309034540000303501038070025040c07080040c01090102c40c00ca04400800c2a0741b00c0c4000306948120900c0ba214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 331331214 1250 331329964 331330003
    0x3130609110a080102070302011113050405180a24091e06090213090b0603010e061801150f080115061d040615050a081003080f0c0c0d0507050f03 64
    0x100011495049010094400e501c6942054100c0e000182203071015007011405a6020480100b41582400380c04244c1c2c421015052504040d02401c441260040c0115402640c0350408201204003003024107500d170340940241c90041c1e0081c40d0481e8003640c180c200342001c003d0700c0407000d049403461045024255000c070b108024640891440c01c43c0307461403241a81d522742d4690310b11015884003803603000703c0d0100d00707000244820f00b850088410a4098541c074040c4e8500f10351420b01120000b080ca400c8000809420a0115502c0944e4090303c9010000c0400051180c000203042281030711000a44941030028410501c4100a001d210340e002c1c400e010000740540c6014203035a8629600d900520b0b4040c0010464940314234a01c4580d2510f2000040010760005031100b156031700004454011400003080c0a0052030b544a00d8072602904503071f000303100000541c4200700c00041001d0000c0e80d901030f00010400c6d0f050306000340c89801604c2594042c1c50380a43c00d059501d0003040260b9202d40315112031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 331332464 1250 331331214 331331251
    0xa0801090c0e0a030b0a1103040803072a060b09010602011505060306040e0102040312180e0403030c092105120a200102070f06020322030804022412100b03 68
    0x14400740c00040802001d0001401210005480e5418010003550103841e04103032906010810307004640c458400b010f24104140140800590100200c079045a490300d0440d00104041c60311015803d000140c5001d0b031100c90840004110182c0c0180c0907800c1c0c120343c0a9080e80e03803100141e003a41c207200005405c0c503e4840091004e890b00b18040c58004030068000140b115110b01460708a0380160820382e020032269240c85049a40114500c40b042c84202030080881d29114801000501c00740c0700800341602e0350914009140300d13041000c0244050003207500000200c00c901c43d0b028203100c1040d1000d000c1e1120100080ca920000c0f034084c40c1196030f0706e0034941061141d090582c04500c4c80450555020000b403008104103904060701203014550060740c03401c0000740070407400b001600840c0c401e00d0400e0600c010a40200d08903074002e80544401e0352004041c02218259007841606040c14240410002c0611401807800c3d40f00b070060101c6d80c00c10310b449000840c2180403c0703400e91701c0e106440c0480c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 331333714 1250 331332464 331332479
    0x60a020c030a180902070302030c0706020d0503130206070b1602011b0c0f1514011d0103020f0f04140c0a0201061403060408070602090a0320180112080f0706050603070b0a0801 77
    0x2580081c200000d0210202900c44103200b0580e0b01401b02036006030310224002c418443c051200000400d0320b070005140003500404090f05600005107048440404030740220b0942d100c0c00308440e500c41d44a149840940340070400803031200444c414070701c0150b02c1c02c001e80072600011070090102007095202d446403480c00c2d981d0b035559100200001c558040d00012400c151b54140c1c0150111400c0760700c0c8504256042a1403004400060200160742c075074400010405a1510038018680c80d1058400045040d50300c80854054451101103840300c9515504120129440201422004055038024040d055550204601703042400a4180c4e164000c2c5020800051700381c0001d188261003100301600b41a4503100190303603041513900948001610300400312203800c12004042c0000b80845059061001c150000040780030305000389254611080010028401e001c1c003a01e071900d4034044456644c0c403051130080c1c00703490260f8206000380324041d00411580c0a19041d14049200781d40c3d205000da20f400f65 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 331334964 1250 331333714 331333727
    0x3141602010b0d050606010f14121e010801020405190f0605032d010608090616050901030b040204091d0703050a0f0c0e09010504050601051e040f02040b0c0604020102060a020c030a 79
    0x2599010340d981c800000c002602c68440c190350150140014080620708000090801c05140c0ca00a04011101a44003003040045080e038109018031440d01140e560382403c100c00320051381c40e070841c0181904000240800054004105541d0244e901000c80310a20340c01c4400307000c00c0c2c021049a01d54490040c01100c3c890805545d01c18900e200d0404d210303124415210324440b0034010b0901c0300d80c503480107000302500441c4d5030360820200300050103a441c1c84440d1410301c1d41c58404540401c00005a80c4100368071942024440c85d400800c00c543c1c0b1980d40305603100038070301d0603d5010f510019a0301c08020143c003181481c03c036504107018195450a554030380311408619503044500000c24800458030a0618012a1040000e00c00002d46030500707041c0f41340b4114059000300c1c401d81c08844a4800080c0c1d184420070101000e0310301040c0480c0c1104180080c0c0100c0c0c02104000c2ca010906150382c8000241083c0924000c2c1c013030fa41d080e00c07003005004c00c2e480f4190003042164010004803c03400d10512 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 331336214 1250 331334964 331335001
    0x8010204180b1903030306060305060618090c0c070b03041704030c0920070602030711010c0f03050a02120c19020d05030c0d1d0f160302101409030115080d0314 70
    0x1003e2104100c0504080e240a040c290415400650780b0740080c030601b5014881c06070044000c4032240e045c01580e90310b100c041650030410781d000e4100000030421192085080ea0140386080c000c3c0e55205031100c0007000c00c0c5c6c004a500b61000b81114860300498843c501c1240c1c203481d044214010308900300001c41002e400b4840305004000d4201054000c070003030003c094030300c030703440f0709005a500c0c141414014494810403210300b421341d240540303224240707070407034903c0006503842d0038081015900c64480c00028016072650001941100081094401100c0c0003000e551a001c12944000c1300070f03000807a502d040002c0c007074020031820004144041c0600c7c1c05004141d1400b407000c02d06281c207000c450380b45230780014032540350760000404958850050009480310a15540f02c00c202030300d9600018210f9050040d20020f100100c80c018108050190440d0441c3d0000f4000340101d41040c40610b0005d03c6900c202e1100d80540400589000c0c40b80c084c6110080810b10810550380b2446484521006004c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 331337464 1250 331336214 331336219
    0x23030f09030c120301090f05061c1a09031909050604060c060207050703030e030c0103020c100e1618050601031a10090f120303050105090403080112030c0602030a0509010608010204180b 81
    0x1031000014a200c00c201c0d45202c041c100c03c07201d459501d807011890a03104001d02145885040004000d90342d118041c070040c140707205581a00314070b02c0c68103140403c5180102c0744030f000e0fa580c0b42089012003001000305017160030b0703a0b2502910701103c1821074600741d0343c1c018140d02ca403080004110540c880c8010480c04ca014035001460303e03069071340f441d152015550044010500411401c070540c5018010140301a60a003001c1d0b10309010340421036228006091103485c034980e0b80c0000020460704000f1410203280002402c0440341e00c43c030104180e108000c41c0081c0c2641000300040c6554840d00508101d0301c120328410b011715032040104604100740d0b504543c100420382d007002034001541100c40004090450307440103104200d060060550b9416000203004080c200b0034030002a034000440d50444d051540c200e007032002546011100030044000141815002100380020700345103610060051000c04000c02106580e501120300380e005d41c1c8200d1042c64107190350a8141c2101c0c0d000302040c923000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 331338714 1250 331337464 331337467
    0x13051f0c170c030a2a110607050c12010b032404060c0e041a030d08040b010e0406060b031f050108070212090f061303030e010c08090103090203010b060c0a0323030f0903 74
    0x3480d15092031500a80700c1140045c0103201501212556078518500c02d001280303501e01000410b40741d00c204104c80300801402180300248800500100344909552810010b00712155030401610960180c6220070080788640260f20114840d10082582c00c0b16144101100620954850b01c0361070003042c41d800000188020f15011003c240d540303100784403804000440700307210742e000c841c00d25140c5040110950180810802404040340041902d681100c091580c03664565886240400142101e903101c0c40e0005400300c1401443c032080c140c5506045e21030b100a40d00a555240119240740d410b48a03039025801940081280380c1e0400d00030040e4150142c4180c4c0f0000e9600042165030340b00114031001d40f20944010b104041d17000d1040150a0003d1130440b20892280d1500d40c13252094071030f0581850740d204442421901d00f0741281c60230b81c0c03006104948030200740117986d4490000c01d008030001800c02400350307101c5e44443c0cac80035078041000d07000a007180e0790205407030311101014001c1e48a5120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 331339964 1250 331338714 331338727
    0x40b010504021b0f0d022416020a061517010c0f05071109270309060a0509031f0c020c030109051506030703170909060d0b0a110f13051f0c17 62
    0x1810400581009138010080c40e685818040003800c4c040300842d1941022000000116443c101c0300409030044800c0e9081000740a0a0f88281d261200381d07600141003e08282112414100201c850802c9404807044076590b484116050307422580003a600f0000310700402c12000c1c41c64818005402650f205400106203400306038006900c0d100d084030a594041c02c00f0f030160031980079991000a5a088410045040c080e410000910300d00981403150f04100b4081655159030742c04006130900a004038140300804000c14150344080c0c0b44042e050400351141641282090805104403505517402c20098000e0410084e031000302490050840c50781032050b031f43c02101003000c181c40d00c0b02111024a850707680c0d036401e406000d61354200801080c070a090760030307120002c580d440a201c0c0d4016105c1344000341c1e280c04c81c10700d408140102ca261a0b80d480f000308404150aa42240040544130121030106001c0c46a60120b4035031441010210001346012404500040810721500d0854001c03031949800c242 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 331341214 1250 331339964 331340017
    0x70509040e031c0606110606010807140c100e03040506030f060a0b0f0c07061e080703060f09090203010f09020607060207021302070615081618020d180b010509040b01050402 76
    0x1080100c00e442945100100f609910003240305040061400e420326100c22543c2d15a25034403071780000c010034180711401002480003481125149651142002c0c500e0300d850161910741d075074081d900160038942c2e00e00707440c02804003400400e5904032171005000520b50b07510b88022018091000e0005500715a0103440030030401c0442014118200203804525110058034480501e40303007a41d88004c061104810803100c0742c034a410002030714602c07103003411078654072094811002032519510201c52007905810100740511590070510750f060084000340415010685144222003890700000e5210104002c5900050700b80e4024001003400101803014428040c0307014400c7e80c1c0085c1d812207010356a0034542e240c4241505e0510003824004000340101051040c010403d0900e500640d13003464003141856150540c1601190001400004240001d4440200781e0178000d00c1c01c10200c0b03407100804008280b5091601c04c0d03902c5203401884201090f460f142c113020003940f040d01c452500e030500340304803100341 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 331342464 1250 331341214 331341217
    0x91c06060605120f06090c031f0602030a02010516050a110a0b010b0712020d0504091a030102040e0105030f03090a09180204050c031f030f02010f091d1914070509040e03 74
    0x2800d150300c0c0c0036a03c510b44460140d03c0c1000520b41c00c800d0190034140700164030b03011509980118030180c0e00d40d4903160032a0460741075404a5250030481000280494800d90200280042215a8000b8452500c0b4039080203906880b54800e9000100c0500419840364031503d41c1c03031081c1c6815400c2d280081aa500c820604101c00d800481801e600040d400c020094076500d040301c03080083c4068001229003100040c01849544036210035161109034000c8030042100000e1840034004008543d1580c1d10f0719143d085c01000d11509103c1d01940701e4100f140d5001008881658000528410426060100341c1c002410300003824810b84034005609070040e10b4078400c1030b00419080d080c0c0c1e41c403031516501b03803c00941403680c410b000740300e06402000040e80e02d00f46000031a5090814606014060071b0484a42c0703c164011080b1049070415191841310040419001d0240d2046603104011300d104400284d40c2c40305050141060160000341e1403e12800c040d02c8196801040400c407107000710400e034510b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 331343714 1250 331342464 331342469
    0x718080106050a06020d1e020c0d0b060906060a301404020a0501030e070b07020609030a03030b10031a04090501020f071a060301090c09020f1201031218050303091c0606 74
    0x10380d550941803080d4a858082d102c0203040f03900c010070030031411880042803c016a00c41491811041600c46200d50003401030003400f40c4090400072a5107000c0c10300844801098030810302402000c2c020901c54240001110014001601c1e80e6110741540034410b9400494604000100d03007000c11120102c0405001d0a40308510040c81c00d80b00d41030500400c00c81400c664415810704d0300d8044100e00d00540403508208483c6147c041580700d8080340046500c92180801c46039160181340c03814001c00d509540603100504042c0d9112100e8104280c00307070100d41c18184403013450f8094210480252a00c2d030081c1303001e43c0c4142e0016061241031400400c20380c0184000700d030203c0d0808070188100e400c28003041e9003c00218001c0c000c52003e610f0702034403403003c1e00030030b14066000a891341e1607980300340071115141c0401175074183e0340d0796900f0a021091041c60305c100003d1600e0030801c5081c580920075070b0a440d00107001d03510340358111b0204036007840c0085041c8001c2000342c441c10b0114a60b4441d01c2e00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 331344964 1250 331343714 331343729
    0x30a12021915060602070f090e070906080f060a02070b0109152301030f02160b100506041d0f01050120010e0f062e0302220c0e01200a0303050718 64
    0x11403401d244900640303ea50700b22108660111904110280d0fa40210f541116003500c00090700c1500e44400703a040c00c5158200707411050420b4000150f0f4040090003800c15103207a0240c0385070343c50304c1850741d09901c12184081d20108a880051201903101d910000c511640d0006e0078040a6944090621a41e400503200c4000414038652070f0b1503507003501415014100074542149040740502110403070455180c0050901c014160006c3c1002c1c9512204401400300140703174948803982d0300b440c801840c5114603d00030150540d00801c0c0d500842d4000306050b80c034142c65860180102000e00c1c5802102d40411141540d00d43d144600e4140084c803202c00c4030041217019242c2840c00504940c004000c0010303a04103041a10650700510b11441c1100040e2903040302c11070140750120341c1c0c0d0010b0f590800041c5042500d802d5403c403040d9042501c0c1078000b2003c1e01c0ea070f0501c0c0750750203c003041d503000e0089009481c5c0060780d10b140040c0c0302c9e6101aa1014407400d111001d00c405c0f2030007030090002e5400c14007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 331346214 1250 331344964 331344983
    0x90106060906020a05060103080a090f080c0a12120302030c2107171005060702040603050102030702060a0e0a020604050f0105040806090606041d0c1012090305040306050106050306030a120219 84
    0x450594070154010141c8120300040403a08141e81d11966585414440540b50348c10205180d4145841180050000c01074081c04280c001d0300c1e6607205468901103021148134104081c000200d00310079100c40c030000707a0002003091403003e8110b81500030358002172203503039290303000c000744500c034510740d481c0c0c111000c1c807611140468944100054108040c05800e6403424044604201241c0c9001c016070f0300750785040d80c111f03132075040d244003003005030030580c00041c5254008010003800d030760700065540c4580c0024905200d4102442049510f800040310080c0d00600c08000901c0282491884180002c4040c50240c0c0742c250390320701e05414070100b5102c1e000d80f50840300c1407143c541b409000700001035100ca40001c0c9101c3d5061200380d540e407a0036120500406086000340c8501c0d008003000030710760350100c00600c400c00707007450000c0190f4050f0100310303010303803800001141c4140300e0010f1364800d203c00340084c005108152a030605030128042c04400318411003040a103201402160000f11030703c103108a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 331347464 1250 331346214 331346219
    0x61602031011180402070c03030c03020304090c020c15040f06030519020f0a180f060c0501110d150b03041101111f0506090703090c051201020f210717040209130b090106 74
    0x101c1c0f40c2901d60b03207594880c0b80103001180108140d011443e040b00e81c582000d208100c60361400340d00358010750f40030b10040c61525a02000303090700883c3c0940c5040b401c54500005409800506000e8003a0b40640703c14941c00390400d010240c00b9500c01600138481d4030f00325040401c03038610902641d02804a4094290001c1405110103411480000b9060500e071030482d81103007040d0300c000030380d2194818030040140801d410340902c0741c2036008a5000200d4141c690703841c4054144100035080941c10718400108090b40010030701010002e9a000d240d10400e04c8058403551001152418100e1022908900805841040030b201014040e0000465000d0116640c900310341082403261000345500b09041c2480000e0b0000703600c80c503400c42940d04c2201c80c00e121907152554940207000d04143c4055000e00040c0300d0500316601070321f0002000c101420350a0560716900b003198440c84052824800c4991000450f00511b00300204507880030807007241c294041103584035006442070558003408540d540e00c905 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 331348714 1250 331347464 331347487
    0x60c030c0d1b020906180f15030a050303010b1309050a0501031509030c12090504050907052103031603020d0507030b120123060a050303030a06090501090b061602031011 74
    0x31800200716a0078424500380d81c181c46a9003061890398001d101d5491100024881d988521340f215070110046c082d500c1c14500310304d415110764416140c160300407100c880880103e2400190b03084149910201950071640b0380400c0e6041508950900a01c0c1180c40101048040d0103228640c0b150341c1d1140c000c5080e51460400c140d031007a15404288000703003401c0c8074001107500100c0213180d860388410113244110b10340008031410f81054000690290424080c40010003000500001f5500125040c090742d102c1c2401031034201c450801b807015103410a100040c5560714815402d88031010508002d49442c1e00c007032131441101c0742194500c010079039500e000041030600d00aa001080d02006c0200010b07240f20a00c0b82c50f51041d03420340c0c008040e02c0000a1341e0f0f0b40350041010010940581184c2e200e080c8106150050801c0f401054006490a000014501c4250080c1c0d100c010024015602c2d1182e40c1d61040702101030080140e8042c4640ba01c0301b59141c5481c4030f0740c0c000f100900c00b120f46482900340d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 331349964 1250 331348714 331348723
    0x60906031510030b030c0918030a17070f140a1403010602011505010f021b06070b091f05010b030c0706062105190803011e0e070507060c08092a060c030c 67
    0x6540201031600c4455244c0380c030b00103a81c605001003118036000703590360f00c00107030803c8202802c5002a8000800e200859680050641461031000107282070155640c242c200c1d04030706490024800140700d00e0901008115503402440204020301d001541d40075240d030709800c5030380213900090050795940d00e10018081d0b110083d1002c0c02007440c1c84440c140c08140020342c3c6903030080c042c00d540344007a80c0d0a0141e5442904460740190301100f0019503241203500d550b1509028070180d2b00c003a8890403004586801d52080038182c40880621a003580c46d023810207c1e6603080500b08503a8a80ea030080403d0b1404154441601034051040307810b2135140e1032400c076041c40362420600b07090340038001104000a440205403415245a21108071141c0280c03010303100402c40e00d900c240c40110303095046c04000d560020062101074001d150904c80d5003454030040b80d85250403104108a40c100c5104414910b1b01801c000e0003021b81280b007480b1a64800e80050302d0380d8480d0341040265840040c1d5200e06600601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 331351214 1250 331349964 331349989
    0x2b02120106211a060c0705030d03020a1808031c0f1a040e030408060106030908160605061224130516080c0108250c0b1611010c05040e04020609060315 66
    0x200240a050101c60384900c1c0e400164640700e04c01c01020444e0901d801c01000243c0050000408031401c42605580240080d031202d0850000505a502c5148141a8203400c5200300e41020000354500003444241d0594907111000000000340c858144004507d01809010700344d00d950020592030340e0400e0100400c9540c03402220610b50000e000400890902180160444401d4107010600d230b00f952038140072a01c541d580e00884a0785400a81d000d0102c90b92009100301d0043da0f0900c0040704c0b0070b2109a032856110320468040c41301200b10b800c000d0007041304540050b500c00101030070401c555200f40c18440c18091900c04800c00e60000c1005450400150745002000c2c24040d8242c2040a00100a60703d0714a50300c0340e442508600551041c0308450b06003110fa000300c1c0000f5981443c01030103158108402c403220014040c96041051000c062081408031001600d4091a0901d4040d6210300307014000c0099902034014004501d564450303400452160001e441454070700510981084115600304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 331352464 1250 331351214 331351277
    0x1b0616122003040305070b070e030c0a1203140f0c03130e040309120317072303060a0504050c16050d181a03060d12170c2b02120106 58
    0x160640409440c594546907034200451800c1e40d03281c0e120b082c103070303414460301400802c0b05603018101b0604990268910f000c1c0c010840c04c2e40c200c000c040c1c0030884001d520340104010385540d00d614100280c00307214604100c113030f0300038040d0501481c4141d00085420a030001a0181c000040e040400c41004100d540a171140b1601808103007003a0314001c100c4501405903c05010703400c0000428103029900d240700c0c00b002d0114070003a603d03100c9001040103030a01da034030790f001084144903204075412500780d91040c0740107811002024681010000030740405484104155020082c00601c41148004c400321035006030010180400302c4200180a06120301083d6048c0762407000c2440101845072204c0c02801441c256562207840d0040001c0d4035018020005100c403e28055103202c20b40c015030034900b100900c0c400200300e42c1d220481e4101d40d1180c4866086d44901c907034000d080f441c3c0c3c1c03207501494900700ca4a005092804130042d17624161020303000080840c580500044241c0206038160319004440f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 331353714 1250 331352464 331352471
    0xa1434150606090b071a04120f11030a0302130b0a0305040c060e0f040b030c180a0c0815150f0f0306040c050c0637020909011502060c1b061612 63
    0x10008003d00c0d510082c0520103080e0400580c040034411000414481c0004800c0000c010303080c94039002c896184031240c903002040010200100450040c140b0308180ca4080000e10715085440070118025400308040c0c001c10a03581da804101030315082e01426002410b034400054906040c1400200f001c82e1364050b804000c6101c201d40740e503440381080201c82c18810368021810f0010701000034200010f034211035400c4140d841c2d40001180c8140e154038003820700e051080002d440ca5203402c8580c2c130030855280004030f1216000f001c072400d11840802d800018616414201000c01d9034143c0142d004156040c016400401030080750300e05071150b140c1c0c5142c607003045490448403041d016115000200070038401401d034203141c58440c2e21b030100c1c84001d0f400d4950074004414199040d100035000650345a000c0c1000c0e80000c1814003440c07008070260301058004001645d10201041015400000440c5404004c9030014070300f140100200e90254216412002e201d04183c04001c141c28200030509003623030306 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 331354964 1250 331353714 331353719
    0x1020d11030108100f0207050d020a020906102309030a030f030606031e1d030c01050103111012050903071a0a0b19030f05160e0103170a14341506 64
    0x200e001100080070700101741800f510f01204000e01075407002410034000e801c01c0d05281640450b03a107840381d20880b4117283c103459090074002d2000b007090440c00800c3d500c1881d029242c0c111040c080e6410b00e0720316890f240142120110b07013405941d11045000c40c40d0354801c0008140c15000b0103003e002d6500e070403c2480e0f1a000420043c001600c10300d0b0742981e903042d004c2244980025840c20504951b4203ca684400250303010307000300000d00c020f507642d14032705201ca4528648160340c000800040c0c1e0324241c070024400d020070010200585007000c184810407800000800d9619064011080244a2065441c2c4100718105542c2c80c0c9507460321424501c0301e10001e25610f09136540c103980d00000f41d8010304129291407458000120700c100c82c002d044820010302e698815880506891107200ea81040c50700a406600140c000d000741c03e40401c7d0760001c50840201400301900040561105100d0b45003140c003a00c0d260061002c03004c0c0445040c210030313002032044460300760703040c4511800300300b19107403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 331356214 1250 331354964 331354979
    0x160c081615080406150503060705040812030402062709010312021504080d0207050304050d060b0109060507030801050409050a060501092009090601030504030c0506090a1109040b061507060e01020d110301 89
    0x4004000504440e500d07944442c5c0c1c101035030900d002030f1402808650180c01c240d400a8040e4006100d80720407442520350140050701c406082e00d0096078041c0040d4242010102544540010070f0080b02e0b01880342030741000640c1e030b590304050003103005004124850090403002801c0880003100030850680140c2404005181c40003202e041eaa510321780180c032107420b450603500750b2050b5030000394403a030107102100a100203136210b034100b04000d8950340c4105030785400503a40b82c00f811a01801154824004200500303107500500104e5100308241c0d40c40c84855510541203980a030440d00c61160784226038003a031505440304142801601260500f4054031800003403070150020301050415882d10b01144c2010b0003010f40e80050307a440b0b025140b440c034105070303020340e0b400d9058001c0d60f00c0503101c0a4a9550f00382019064041c640000d001050f81c3d42d0a4180a11242403a44015519030704106030350100740180714006c101200c11002695881001d00003100f0b4aa00900c41030040704200300402600303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 331357464 1250 331356214 331356227
    0x3030815120a12051204060b0f150403020904111306080c06040f210c030803060102070f08030909070e030307050f0d030c0210240b1b01050702070b160c081615 70
    0x20b40c2d10446a5a07000d5901c481242c2500400c10f1100c5520028024081040000d0300a03c200007010341b8903600c1d00c100201001600010004809403088040105201504140140d00c0e41729000d1202c0705a0606034002056911043c0e0b480008140e45d108000d218071981130110030a4158110342103070606080203034070903800441c0d22590705400d5000807400c80b2441c2c18820050140c0e00300000d2549155030741401616a4001c88249005010f6820040340c404031500c014070560310704000950610554406115002d41e000d4000010306c82149400c4032a581d081000340182449803016158139075003d4003140c40d0441079a4440103141c105218801a168001401614030003c0c001c0030404008402d41031200070041032131004c03000d41421000ca40c1d0042a802040303810103090007480c400800342e901074201c0300285d030848010b8000c04010003160308520040c05140304081c03200c0c111356101d940e400c5002c00c0c41d40c0c004095034014800c8000a500d0080004c00109036408007a4440d503071a05004224 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 331358714 1250 331357464 331357483
    0x90f0417040b0d0203130803090709110313060b0d0b0117010b0904080a0f0c0204050408091f1d13020403060b0306101215140906060301181a18070303081512 69
    0x60f03940c00310001d620308103900d01d40394800380c100020590701d00709040841c1d2610820300545602609100c0291403107082d07002128424080919100c00c1c180d00790303903102d000d0240d400009610106451004c004150b01040050007001000320b281e0316a100f01c980282501e0000440521488001d020400460207107401c4481c00d80c0c042ca0046109004041c055410300d01c80d240c060f400518000401c03080040300030007040c030310904840c0c0700141d51000342e080c0d00001010144800084216015146070441511080458980180440c1c81604050900002c07a0815401958425210f2682c5142420701340076698100e0080046045070b5402c00e10281c1110310071441c000c1802c0c03500420780c80601e41640c08211b022402107c50546130034280e4040d41c0d605815283d5a11a501e00010240c14440120010038120fa00640501500500d0440c4503041d001c02000310303040030340c621060183c0344014082e45020714440e0311200050700300303056101513101c0610107a6005003a22089014141c031300140c0d1107075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 331359964 1250 331358714 331358737
    0x50c0c1002090607230a060902040513020a0306051503100203011505070507260a030206041106120f0709050d0b01140a0e18210409050703050c19030902090f0417040b 73
    0x39075205c4100811070701a4000107600007801012803000401c4a00d07003184022600885092009031921070712040e00d0b0902c180c1c001c0d4007024100c03040001072500d4200da5840f141d0003103511004600200464101000d890030300300071560000050090342070386d09014191201c2450114140320b00e40c1e55036580c80c40f950003001e4001103c107150380b120914540d0011402c1e003184d42501c00000d00c91070301954900d81034604603823596501943e81c034a03007030020075204d6840c0042807481c907a13150100f218107807000280c510400c114020101042a403110502c200c100c0c0c0c810b400c0c4450760740c0b405c07032076a800c0c42082c2c0da5644180d050385000c01030340190100d09504030115046103048a001002018600404c5409184102e40b8041800c00074641c014050000c0300c86003030301403000b9610f4501c100c0446208458240803480103001030300304912010b0b81082604580d050001d9410320b00d80003e40c0800c0e0031a116545845518104010012081c1908504055401250382890309004e048010f41c001c55040d4107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 331361214 1250 331359964 331359983
    0xc10030207021302071101031410030f020303210114060a0806190504060620010204050d12020a05010f022104030f03230a091b0303080a09060b04050c0c1002090607 72
    0x10565494018901d001008008110342c5c8900030f15222132108021143c40380424980303001c081c071140990010b036224140b81200d0004032410f41c0e5a0410a03003002d4802d0717800d44000c0c80b409100c080c0d1845207140318900c5412180b22903140451580f07142060b400c4049c010700b018810040815080303450715030000c008683d4070b40c0c580e154086078a00248981d0007240d11605003840018080e40111600310951143c01038101010582600e05080c1d100300d00c00c1075084550b980f812000300700c05612000050280e4815902c41200740d403203003402d480380f91011554007030340054081040d80c0d510508568410f07140c05040c41c1481c0945000e0018041110f00909240d1111505198000c1e40044e0320401e80603040b114034281805c407660740007042c0803003013100d256600f010f02108142c0f200d40307070310202d070750560381c4203980e54412100502074510010100c41e0380d6101c0d001c13082c080d95980a0740f403050050805180c0c1f542c9059140d186000409a00c0c8600c80340304215505054817000100e07450305400100c4003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 331362464 1250 331361214 331361227
    0x60f060303190807030606080f180307060603110906010f1403060d0f06062904050103020a030b031533041a090109091a0f1302150406030509010e0c100302 68
    0x3801c502c162400c400244552014a814080d04a143c040c0036001d0b0769810402651070715420758a80405a03a000c00c0c903550400040c560008050011509000700004d69040c031041c3e0b906c11064520a030401c8070b0300c840356000c819481c10702001c03c542c01902481e201c10400701c0700d8006003401c41c4903010301030608000000920203440704040c5825a650001420310a403a5900700a4010081e50003001e010300c0c1400c1c2a01c03140070300881c00c514010001001549018030384001980254440d0b070740c050074952600d29007034240d034083c410b2101160210074155001e00c0c01c80159100b135803082c0c20a0440c11205180303088404100320884440721400e850000f0102e1542c40013101410303000d070200e41c0c800b4501001003203109103a00514803045c401e0000c1c007810190030780c0a86600e1341c03ca8031034a02c0d80030f820002c0c284181c083c001d040d80c18006081c1e508592030b146603003521903115400920201c1e07226414071040f4142485642101c0180310f025100c1810407200003030240c007030203210390101500810362 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 331363714 1250 331362464 331362469
    0xa0305040320070905070f1704020406030606090c1101051302060f0f2a010501270b121e01061508070201020c071214070b030a0c0915030905060c0903060f06 69
    0x100542c03800b458900b404450841c08074155681c0c058020242c07240c2c240404a011207025060050280c445a01d440d1480304e208982420000c070000c1c0141c0c3c2c415156000000400d609118140c080d02c50780e580801c100c181c6000103443c0201c0c3e1407080341c260b031400c400c00c8004108000b1603ca4a6811100141e690f045090209041d00400000d401003203000911303000c50301c0e44d5040b2a0300c0803404100c05055100302ea00903d00302c1b0424459000044100c4582805411089070141d062484285000402ca800c5501203a042040d0500c001d48650111140310784007003241d4085000480c01d40001c0c040c0500300007010149460300403180382030091324070109903c94001e405682e86000c03150100e410065490003400c0b4150300c1440d0a0342d0407418041c4600e4106400300300c03807003030700c443d00801c91864442c2118a402000400001000c1004261004c242d0400c264100c0c01c020320182e0340401e103000581031440c00d252001d410000e030340800b0080210903440200d400b65001340344c20004e000075030340c0901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 331364964 1250 331363714 331363727
    0x118050709110d0c0903030908070e060d050f0a20030a05070b030613050705030a051806011e030213061703120438010f090c02030d0c0918050103120503040201050a03050403 76
    0x81c48041c0a042a001040300345e44001241d085038020b42d42c0c0d00c84250303550909900c2c1c034642c0c0280c001064070380300042d0f07a40c1003100c40c422060380f00320100c91291641252003410b08501d010210380118880000c000d00104000c10001030356022005000a030b0000c2c1c0d15190364400301d2141c6200a040400069025601c04015600c8810280700500c06460401402481ca500894540d02118030700008248401c85404046092040d0b550041500d40d0074600c000c0e440ca158001e040010105000740440140c44444103038603181110400460002c0c2009214041c2840c400d110100d030354414410039146800150301c1c1a041030700700300411000c9d41100203120703071103010784141c2c00a2003c91040c0c018441030154003034126244400000c10a944070018141603032031f00d05a001c0141d000303009010702558650b114a82c40400c07420b20582d00395072030000301d40040680c0d035244542503840c0d0040040c0074003a01612406600b0380742107481e500d850307030000e0003501807100c0340c600701952040001c0405000d0300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 331366214 1250 331364964 331364977
    0x501060908010606023a020304031b060804020909010608031209190503070b06030304050402160b070201050c0406360303080106020d050712090e151e03120c010615030905011805070911 81
    0x1b25201b818410610040d5a0341e104d032004a90501142c100c2008043d03d41c131190f030a03108070ba51900003a4840b80c08001440e000600b41054656894000080801c41040148a0b060b4140410301d928600603440364207001140c5d807010348204540102500094010045645c41035200e0480d06654a03100c001c02d184d805550405030b00315100140c0840d40001015440039600d1040780203c0c0103aa51010032801d8039401c0c0c1e0b003400071900034130080c8101030147c4140720f041c138071b0f0040030959805c003d144c43c424218001101c42c10010200002c6c010706a00041da180500494001401d14550007500100703039109541014110700808040c07414418441c00070a4024049a621460182005035001c0c500810600110f886a92201c02005180d40c409000303580101008003d070241d070904544500c0564002120742c18076559600e4040352000c2525400303201c007032780c660b00002c81071035500d00a4210340c681440b00690701c1e07280c21002c00041c2e0024200c0b00f031318071081300402c21390806040c65071180100c6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 331367464 1250 331366214 331366303
    0x8121f090b0109121713053c06090f030a05160e0702030309060105010c020409050a031215030f0b040f08030108060714030405100e1e1605090c03060f0607021201050106090801060602 80
    0x1100701803840c8a60300c200e01c8503102c80c04485640701c04007030364604231003080404190010018030410a5a242c8964001303403a03034001d001d841c20200306988490910b5a44402c0c0c60300340518540510200c0075400d0003a511000a000940c03441c1003100c9595030340d0105105030703810086540d90340c030308549403500328085c0b00d50302000b240c104082c035140151241840132031411259150003000ca0306410004400c000310b940180b0ba4250f02400354032000300d80c0380000c01c01e0b035140310082d0f21200010380e200300450091030020058129070811203402010464010400c0414003418418000400d5010803680a00300000700009010081e40c00140d040000d0140420707629400000d05012210003c074050f02c4400400c1540b40340c4030384400411810440964100404940c04e0002541a040c15008400e4810004100d281000804d40c0040c41440b182805101da503510743c4010044680c00c040781c1009400080e009110160402900a5a4500c181d812034210000700100c001d0500340040c2c0107a140304c030f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 331368714 1250 331367464 331367479
    0xc0302060f040803270a0609030f0614010902070501140118050907080307060b03011103010303051602060d0e010902011d1e060403020d0b0f1308121f090b010912171305 74
    0x1040180389030031141d0710405c2070112416881c0c111468500d4084042d2080d82c0c0f244141c043c20350f100c42040000619040701c40543c0c80810021106054030000d00a20200c0b00144e9940c0d0340d40f5200d07094a1051840511007499000107000d2003842034101ca540c0b1500020000d41541c40303480c041c1c41c00019900c0707000c1e240130011708038082c0714031a0058102c6480a500900c5501800e070401d07140c0f44800d00c80900040c80602c00d5101c8081424a0251000d00042003182003240d81490030084625a4181d40c440e1f83d9204c25030400c55801c6121004c0401685c04c0c103e48624801000c40d56403040140d45002020002c0c3c0d41403695039480042c3d401540c0c02070f01604140c819403807d0711130403134295071201c8441040c000040102e05206410030042d580300400c1810300125990380300e1041c070003070719852031b40303154065140a00a03c012541c0041901c0c0c1800f20300c24502900140242c030940d000056800302e100701750004105140502485aa03200181c0c0d541c03107110356070081c26124250416944583c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 331369964 1250 331368714 331368727
    0x705030a1e0c0f1a270c010507031101060308041d0f04050c010f031e02070506011707150203120a02041403121207110a03021513031d0d05060c0403060b030a0c0302060f040803 77
    0x6180440445d58002507080504d060150740b001740d56030700d6602e4050f0020300100100340000b4450320244030381c42070740710000c2116500d90f034561105401a40000102154081d0003000f0080c1c01000c96400082c4032000c40303000c2c00c10341c0303d260701c91100380c50743c9050140000d01407048030b11a074080154080500040708100344154503d00c041c3d070000809031194451170b000420b079a001c1d01c010040800c011001881c0d06898914100c0014160000640660109004881100781d8100b9528030844d00304d5030050361a07040c007100c102e141001040446c0a603008030b40d07045104940104071401402d81009640301661000e10440d2601c03605a030031112070041c0c0e4943e408050b00001c0d0443c1c0710000e440b01440c917650702440e820f5002649500030380018004c0180040e0051948860048204050000001c11107039881301860a2420340780343c95002c0d400a0108144400e520031907a10500403006051030316019126803c00180a0102a1244000040c01b049941c10001200c0060101c403050f6516a075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 331371214 1250 331369964 331369981
    0x30103140c010f020a0303050a0b04020d0b03190b06130e030a02010204150804031710080a0812011406120a1b030506011e0f11010906020705030a1e0c0f1a 68
    0x4504640c41020320548008031440d42c040c01c445500d01030581d000b0701c6503840e9034074110003820004d81026040385d0366020b002c4650719107000a00c6260000c0f070300415088280c80038181790a80822001d50700e811401ca00b4400100202e4109030004002c444860800082d100c151005107080060140184000100c0d58a03180e0190007800843d030030b0074507100c0c490105a205843c0303060101c40c0180003805512010b20302460040c0d140782c01004a0306904a016191032a5a107030080415007030b69548000303d840c040b01080304c950b541c003404a12201c5c09030841a2800304a50b40114503100441940200010301c0c010a65800b49825002c81c04d40001c04007603074200903004000550304140003911010403161a000c0f00700c4050904034240d501c1c02c07034010907003100b100d440e888046003001654075451a05d001c074182c1d0019060050140e4082c1d40d0390000b90402401090641a0150070b522007001214045a0800e81c070307400d4540c0099070808281e10900c2c1180c2443c00c05429400507110742030600c509c04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 331372464 1250 331371214 331371233
    0x4050f0108070e0103032f033402100c060f02071538150d05090607030c0c020103020a110f0106080c0604050a060c210e01030b06120402040506060d02030103 69
    0x1c1c0c0d0710005803074949840e01003900e0075407400d00003d00850b024040c900900340c0410140c1c4541d41e0700d04900424040c0f103140071410b69000f101d1070030401d080602c1c0d8000c0841c4508091140b0a51640d501181044e1036010600c1d42a820b42220300380002c4112400074031029812031160701440e41d804541c0c542e03552400140034a50501c04950541c60a041c03141ea010404200c0021201c01c1c80c0410503c410000101480e403a00086160f0000c6010040c1c1020802c01d1000d407414113107008001c500c1d85001d124140c681a4010800b108040c28001c060f001e07030341c000c136004080039020b10700507036104038401060320710180980702d10341030b44202d00d0302411818040d800303003003a10f04030800d48480c1604102000340c0e0f4001d03402183d501006808040180a0142e03281003c0c1e00c3c410001c0e0000c586205031406650020b085400002c100e074030f0090001d9691501c04c4803d503200455045040001c1d0401041c0300f0000100003d000790f54a802049465036480300343d60019131152015903496840380f6004900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 331373714 1250 331372464 331372469
    0x90309090c08070e060a0203040801050a020a17070801030312020708270a0503070e270f1002040b0d0e0304090207261c0b0f12060601080106050315130b04050f01 71
    0x1041c41d100401d4501440307250358074010195950380801c01d4100b0020002c441d445941c204080d84070403c000101d4080a0280d82e1082c020341d00010303111340e107105020700440f1900140070004ca0101c42000a010f030070025607810b403038042c03030540d8a40315440c580c14000d21400c00b002d07201d4003022500d81c0360b40100c0480e00d03c10611070b215020640c503111003842050500c0b80039440c1d1503044180203000765400c080a442c0c0c41035440e11200400d40004400c61154030390900f40c1c1c9400d811a80204040c1c07032041180202e0980d0440085107050700d4019803906601079022550021a240c82003c0c041210420664020304941e01003156101428a803420050740c001011000c0da9074480c800c2c094920140301030310706206081041a50000b48181d00e80300500648008580c02581410000843c2d103651000e10355641880340244903604025002500c0008141d100c4000c1000c01c000b04401071000010014061a00f52040a01ca034805c0e14001c0145c8080c166141c5c0041c540810880d081d806881101d04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 331374964 1250 331373714 331373729
    0x6030c120312060b0d05090312010b07120206040f0605101703040509010506090d0f030c0501020406030c0210200a140f0a09060201061202060d09050a1b090b0310050c0c01090309 78
    0x9840d000c0d0102c4203030780c0c00780710340070013010b092107070076840013140e0030443c1d2200142d07059a00d0414869101510800d00b0b070459500070b0004140b020810040f103c00301e01c1020700c1c0c0020310907032400343c1d21040d10f0012284018a02525400416010310040f1140005000904ca0825a5070381c001001652a0494842c551040d2440c41c0005040c0c1004022601c00500c094058030302c42c41c868880c640c6c03444452408804002403607800c3c2001c80c0081c8083e20181101390790200c0c0e1001c005000a1608140d44200d400040c0b44c84619061030b07818140c1c500d040b00d1425903003500c9a0310401c080c1c07155400460010f0803010000b80b020900b0680000618034001c1c69180c030700c01d480d140d0500302e00f26486405218100c2480340a25800340c58110040c1c030000c0302a82c404a200c1c61990384050415043c00001c0302c64117405c42102880100b0003a82c0006020024000c000a6003188002030381c440c44060855881b560f2000482d001e40300c0b1100b00d541c105881002400880c0a601e40100b25a40341d12031100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 331376214 1250 331374964 331374977
    0x3010b060304150c23040f210b0601030b03070816120c14060906120a0b061c020a050915130e0112030e0303090d23030906070b090106030c1203 63
    0x20010300c0d1110a59015941088004010b04041d40004000702014036508060101019070300e00c0081001e02800c1d5400110000540c03030740d140601c0a450240150032803080050400740d4404d0750341402a80c0744c90300e600041d0281f52520741ca00141d0040c8040d422041e0180120304010407a00000200f0b0100000704000a00303800da92500302500e590480030005101d025429010443c14034080030604c916080100034a29080144000a007590300042509401b51560001c01c07000c040180701d1005d1400090f00c0c039902d0910940c2c900c8407000c0b41610103030001503011a000c0501440703442134400404000e401403000c42c5032003490b11440d401001e02c5500342c04242038045241c602556049040740c00c28500040851070070381e07080d00ca0b414545a495003512081c46650a255075401c20309201c64000c2041c1e03a8420300034180031a152840c1c603c82145680f0410400c0e1351601c5d00e00403191a540c10031004c0c80242c80b04407140c1e004d041664000b41c5031100640e4007203001c0c6002d22001c0d081c50700c00d84601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 331377464 1250 331376214 331376231
    0x204050a11281806081b070b0a15080c060715020313170403031d011106070906030609050106170a06080a0b090f06092508010501170f030405090109380301 68
    0x40303500d40b00a201c1c180e0f4002c0716543c20402039000d0308040380c11030030740c080d0300255620000c000d00f92504007803016900385109009001c1e01990a00c02c03000a1410240c0040140e070500b000140c1e40d401040325039020358400248801807001c01040b001040c071203000159542e0a00c544a60040701151b4070990383d00202d08840c4154000000486007100da1640b04c111011040071400c8200b80900418641800111220000000303003d0200da481040ca6456511816007032081c01021613085401441e5030034607100060080540040c1e50841f4100c3d81030013544d2940c2c0741544140500820340c010301052280180e507800300002110a00e2291030703182e00300c4009507080c03089030303580342c0054408a00e56003181d5036160310700d84500d498440307840500c0a24403800790395181c01e5003191301c240c0c421050a070702207840418a0b44184400c030341030741a50000b14102810080060070001c018455000003d54170200100054080c04001075800c5da4405000981080040307504d246c0c2c401800024405d512b4400c54 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 331378714 1250 331377464 331377467
    0x80702090a06030209040b1f080f190b0a0b15030a020a08090a0b16091e05040c09060e060702010908030703171b1c09020303190e0a120204050a1128 65
    0x2100e00f2240c00415514098550341c541c00704524029010488500a24000114490303403d810b5100500c043d60082c40c4070207940066074101100c0b0824140c3c0f004401c010741010610042819410413100c240014031990908000f500c90703c00c0820501094a001c0708000349036001d5400380015900d55182e2007440d5840c0360150783c03108020003004160751149000b040d041d071482c040c4810031140d203042480c112900e505c1300341d850140341e4184114100021000384001d0400b401104180714045c01d02c01e03000d5080000240424810100c0d01d805048007241389429603206001540090800d201a81e07070760304003400c000304070b0491890041800507804c00490950a5400780740d0300d440c01c103c0451070401e402c0c140060512618030414401c02929010480003580d4280700401d00c84000300407003210031101c0d003070190201504640013031280250003c01c0103500c41180c80d41c4c0b100c075411200010b01380d5403215407000915584290084a41c00810040030340b220160b4030301440a4103d180004030f0558050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 331379964 1250 331378714 331378721
    0x3020d1d09070806041d0f1507140c01060f090509010b010e03121b010c0518030a020907051b0303010609030507050607030e19031e03030c18140f030a080702090a 71
    0x10255001100c0200150810384110f101c55000300004001003468105100c001d140d0004a0307042a200e03402540c0501c10700798007004101c10036802c0300408a00d9107003030080500070f8084900070000c034071400240c11003004002e503c110b01410901503001c00054480a4803001000c044411061a42ca0083c05040560003105120800325000f0014050394041c88480030098102082280000b1221400c0d005421000c2c0901c104880c215a1801e0300c1d141c882c8010213000e141810304500940181c0c00c0d50b00076803120b00c0855404940e5046c0b580d594801048410103281001c0801500d07400044000300b503103a480018281100d00a4046034645a1580f08008191103000c2c0024040360b50860954200d0038014007045140d20452580310788640d4a488050190000c2d9a4072003030400c21203480b10405406124401c0404241c0c50003046c0d10480d1704a090030740040b4000c010b03483c600603a01d09003595401c02c11900b505c1c0e0190a5130920f4072149069217103030b004124102d1141403a003000400d040b91511 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 331381214 1250 331379964 331380017
    0x191a0112020f041e0c030e0f06100b0702060a050307050706110d0606031118030f1204050405180a0201031505130501031719030504080d0e0604260304110105090d03020d 74
    0xa840800720540044c00034000c04d41c4103200b605140c0c85200240d0694810302044004d100d02001030200e034540502c00281400e4641c2103420519020300084002d601c80000f03643c400c8000741003999994036104003d40fa14040e85a00a10431030a180803203c100307a490014026403a201001800b449032283d2064060b5194494400c407a4442400398400c2c81195050170920542c001d8141c6600175034520b050340c240400d482030820164000141000f80c0d05284c46455070002044800c940d9049220501c03d07168800d62501a04141e1a00b0080c56880b03040c000b480c00400005141440c014503003a4080c02809091006491584c0c412103e5032a540c84001207810840305442183c1c400c01e4210001d038001c15016009540c650030030311200c0d00b100a03034411a100c5000413401000c4a1a1500e0141845070078010600765020000915801e14040c55050b0382e009a8008000450182c0010048407140120708100c0c1e13025180003100028940c020030548580011f80d40c4020001c901c403118094405000c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 331382464 1250 331381214 331381241
    0xf0e0420090a030b07021b010c05063403150801060602030f0c03040b0d0e062211030a020402160b0601081b0a020a05010c030606090e0108191a0112020f04 68
    0x80854040c0c240308000c200c0d48000034a0340114503103c0e120030f4140c05049801030056880400500100030940c50040d02e107204c2461b1008818140380d0310180c5400010f8032010701140880304e2543c01c81040c070305000d41642010803010418445043c004d0107842c94a141800c1c030210103a02003002e400c10f003d00c000395441d03500191718002101c04174526652120002258030301081c0000300308941d9290041501c40c00201c6c0209250401400c201d05200c40601681540d02c124a034014a00c0340c8041c41824840c0c0165640348140380d420b0100c0e0034501c1b1158000e40c0640b000500103c0140404200c01e686401417240c0c4085075a15401912114025034040000180b8000d1150038044904020038190655106441c80b03035019541d8035003900c3c5001661f00200b0f840344024040d0940c000e503880010301a01040103c694900101d4513299101280b00c0c05510400c0c0040b0028060103180105c0084c03088030400c041503940e094203111001d00e507407049109002501c02502245414000c0d2100e0a41c0c0c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 331383714 1250 331382464 331382501
    0x213021b010902090f07020c030a1a070e1003020f04050913050d0203180d1b0b040612091101030917131d041a090a15050f0603120a05030c0c0d0f0e04 66
    0x400d081d1030a82c0c10001c200c02d0840c0b0412408d40541c0d2802c0c040000640d11580c2082201090a603034911641c60061900080040040310b90006e9580c404820750300000d2402d0040c0d4a20344880054000d01c0f4a8000c55004078a17041400401e00c034441c60001030302e009400341c44030340319000f0003203849115411a640c0e500801c2c0740840f900c1d00d00f5000c0307100c030f943c800c40d02c1c1716103482c40010034031103c0358a50099030100c60101c0d0410401341c01100741501c10241110811100d01d00c1e903030b54031074004500d4205041566440010003080003e0000003010041c2c6034072075403142811003496141e00c038180a941003192107200801303030b403005c0d0307402d864000c0380d101c0624800304100c44a0140c0381d08000700f250030b0601ca0b10300c01c5c8010540b0019001030364604a000483c66140145200d020458040c010a000f680000111030708184641c05441c18001145081d66507901c8000d45480c460280d4a4560042c0c0102c10000c40090f800c2084d000010041c0d41303074050880540b0040100703d82101120003840c800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 331384964 1250 331383714 331383721
    0x309060105130f0507020d02160b031611070906090c0c03080a091509080c071202010c060b1504140a2103030e16080f06010803030705090405060a030213021b01090209 73
    0x20b000740c0701203103980c5075400050402000c1c14880c0c162803042d9903840150b082182d000d462168140228606900091250300744640303404144a4144030003005c100d03443c01c05100381440e545c8101c40ea0364641010404568450703481b03042d0400185060710450501510f84540d800d030700c50081c00e62502d5a074040e203914015546691700200640302c07610084448010184a4050101c4c10348500038007140283c42041c1c49685007440a45010260b400c510001c0a0340c0c482580140e078051030340542a94010740c007040c00c40006020070b200550740054407070044000b0801080e05100d628503004d00380f4007191828840307595503c0c41d0401600310b103000c0e5004039001c6216808030340650000540c02c4040390071140c409004180000013152150052682e5410042040d00c81840401c460f901604080c0f014518500701180c001d0800e20913141c90b00c2c061602c443c0006d030540d03540000b1800940d000b8011035914151b52102000942c0406e031800c14100c005402c41000d0b02c0c05101e180105079000d00400f07007036107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 331386214 1250 331384964 331384969
    0x14010c0809010207150c02120609030306010513030b0a240605090f0f091303140c210705010905010203101202030a02061303060e030403060b04020a09030320061f0b0309060105 77
    0x80c004600e05043d44180303840002e004101e80c04901c08484183d5803410092140d1041001c040350135410300c085903025601380078a034130307010048035081542402d02d940d807601143ca8034000011298005000007000700104000315141d5080002100482c1e4403040026100704004030034140c582c050180011800e01500d0b401d07050258507a003501a0040512000000000000d02030200460342c05c7c3e5007a0b14034100e0360030180c1007050508804000c00300c0504002404401c0da50300c01904491818240b0001036001c491342030341d811503013100d81180c002d0000c40546e050030740c080e50040c0c80d030451001019200107813011504000c05130b0190300601034a69403445800300407032500026510889104021000400180c01d4490711500c80d61a50107180c0303c900c0c5060800446a12081e058000c0c2c1c0100008190143c5c0070140c0404d807130b0b144c209001c19100c841d081c201500040b034040d082c035202d050240541108824014070300390389013a0f44258020b407101002c604d00d0005565407a84d66004900502030391 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 331387464 1250 331386214 331386217
    0xc030210050a06080f1005010503031e03040206041e1509050102030315060405060a0e040605010e03060f040303110412150c051c0b0603070c030806120c0d050309040615080114010c08 80
    0x14010110104142d621140c020307007801d454205c40940c1d980000c50220081002d405240c0c014441203003d9400e150b04000300084400c0c0074a44856008030000c0020110340d60001030b05c020b0480c50501011400503c0b0120040c1511801540805041c1c5816948001d12410340c44059030410707070265045440e84030000d0360f0b0701c03103040d1415403140051001240c01d88940010780000610355440c1e600c24000d0f2014002244c0c8503403c014104803038030056801580300003c18075000915042410798a035200d003021001000e001307030044890a80007400155561025101000c40d40c0a59140b551080d070750b401480c115000310f003c82e404200240103000a081c81810341840f61f0801890114124850328000ba80c1907004681c9080451400c0710402e0906d075001c1035444c2c1c0004103071039050020302d0003500300390f440400780c0080340706065901e06001004400e00a40710101000f5009106c2c40da116990300d0901030904001c02c00254501000003594070002c07411005485040c0c5a1b43c008070710a0716046203e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 331388714 1250 331387464 331387471
    0x6160b04020d02100807080a05010f0e0604090204050a0f110c0a0f03090504020a0908010b0a0608240a0f0317030403080402100528090602070b0a031d011404060c0c03021005 76
    0x2100541e0b80001d601d556a007201c40c80070a507034011072894054005005888003a058071443c0713250000500c1600c0400090708180c403188209040240c0e40c0c600010003808804030001e4126040400f071080310790054105250681500405000c5086182004100d60081e050310181a0b44081d4500010603400280003000d00d01a1a1001d0010f4a0b0004501030341d110a042100060040b42d040144903800c1c881d103507000030121003503c2102d140c550005c2111030083c00450010b0141480c0c884c4400c800b0450281812000c1c0481d119150303074005140c00040d19200644100005140d0508103254500444c1e128a525844442c02e940b00c0d50248074a481ea100c2130607060100410269400e0814241d0040816003082107030403409500d400c004000720711642c000402c1d9400080d0501c0304c91100b078280c500c2d0201900d40054030084581750000411010321030201d040d4038149140150f4001c2c00d0500d80b00754000c003424800f031441e6020455a40341d00110240040c0c0015a09002c030102640010740c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 331389964 1250 331388714 331388719
    0x3070f1707060c080103020f0607030c110109030f050f160f0b0f0702030a0506010821030c0c0705060309031806040503100b031e0309031b090117010f050f0603070506160b0402 77
    0x411800b0740d01d030b1048452002001d40850900c500400841c0f030800e8152a180d8401e986060034100e190340c014003109801c48000744501707030340c400100080e40b060361510011508041102c1d454440b90500700c0e100c43d082d115009060003015900000310015080a030201c1d15049942c4a40521f81254988150084400d140340300c03c1c05c101c0ca10141c0e070100a0400c40500032000b0300601d500d0000900d1034030382c20400d40000a100c0d41510f0000d01c48110980754840c100b0002d25a032410300b8055607041244581000d85d00280201c01d00607a0040080030b0011101c1d03039803072460b4521006c82001154040e500c10303181d2542c482030704000c0e0303980c582d000180c1001e0054100c1e160540481e801d00e1410448203950078035580046a28250341c03408001c42003220f0301203521042c81444d03000115441c7c8005009800340c00b410000300916400003540820843c9401c51b10800c4142440030310810007a0055451030b2107403040340c101080e039140080c111014401400d080c801c0e1210940c0c0e64511f981d400030f00070303a03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 331391214 1250 331389964 331389967
    0x908070c170c01030b060a031d0a03050c0127060b010e0405074407180f05011d10031d01060b09120a0f02130f09030905010f0203070f17 60
    0x944968450000d080103200e07048003a056910141e1a188010201c681014200700c0c0c3c05401e0b07112401210000c0e072452402150581074900302c1c0310b0801030710b03001450703a1003210300c04030034541d000d4040e141da1001c4900a019001100b51040052040b1015040030440040740140000e02c3c542d0128501c000181000c540c0040341c00001404c4620464151002c14058981c0c101c0002c01311417414031940d88031880c00320501ca850010031020340c41092000fa5101400041008103024508980c42c49141030408092a47c882c044d84038500e440d03100b5107010405d8012142900c01600d03a1038100d95401038040384400006620890280152609480c05506140c08038001c5000030f0003140702910b14a05140d039610280001d10000000742d0010300d019410880c0b50307500040e4000e07100e40100d501101c00c1414203005404200040482c450f4100343c503840c001c040030401d504800303101c0c1110b40903228001c0000501609a03141e100b10100104081c0c0325103003c0000401e40c030b01000c990b480b5030b051070303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 331392464 1250 331391214 331391227
    0xd090312032d06050406120503030103030302070819090e0c0a0e190806010308130e04080f250b010906090c080109020703031401140a090c0215220f0c05011e030908 72
    0x14440e4525100542c040c584500062105080500500000341340310b0001304100e400940742c80b41c513800706001c000c04142e00003540106002040041c1ca180c101c3d141080d070891604004081c0195100c0d20554401095840001d100c0f410140b064440d03a00f4940c0700d191201001c44100268400d1010100d24004031105000ca198202008524041c51286800c01d94a0108012002801c0038603481904034211384401c000c0062074110a5403a94100e132540d464640c3e120781a8420560414075810701303243c154103082c00a20122810703240c121368401100700f1517503858450590640b15000c2000000ca649000104211030ac154001c00200d4041d180018407041801d4400045120030781c4424250100c444000300329161036100344009125003031003000f440f090904040c0d01c80d015031500f00950130050000030103611030442d922a5140040e03103074221010980c9441d81c10f1800d2080c0c196064003c071580459254002d0317800100e61390005111b0340b2000c10b103000c110080e01c400c01c01140c8058050140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 331393714 1250 331392464 331392521
    0x2070b010902030109110304153305040e0c01090308070f060c02012004150c020a0306061502010b04060e0a050603071a0c0c0406060503060d080d0c0507020108061009090c02210306030d09031203 85
    0x80701e03000b01810340d0b08490b032b9242208100c2036078010806001c0d0750300508a4070f11a40c2e04025400200e9620002a80d200d2206050210301c166043c0e5000d0680c42c203000840c0502a8190302000c203044880704c966660540d01c00c519003150003240200c40171014003034070b0918030b140075625200c0030760300c01491002402c2c0c9070b076101000c4c0c803400e0f8404402070300144041c0400c41c0e02070203034640040c0b06840801c056882c0c4450303861004030140c41e0006190b99400032400e02c0c1c505006001c080d0141420210b65416a055541505ea101c4040c003200d50045001c41041c0e860103018035411525103a44442c1161190010001d044812140444000304100058241440503010b0480020b100d031305c940391222410b00024141401c0201694401c00340c200c0c0500b441504001c07100c003600c00308400052006c082e400144d282408000170714000210450310442c1c03002d03c2c0780c000c51007404103405444880f101e4800503500c0900b540001010144c0c1040841c40d0745100360301846291082d134525a0320130100100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 331394964 1250 331393714 331393781
    0x213020f22060f0206040816030c05120d14060603070807050403290106020c030709020a030f18140f0d0305060f060d05010f0512120306010302070b01090203010911030415 75
    0x2001d19604400000410869401c04010701c40d02d041030001e44480d00d0590b803400f0140c8103002818070400087c80d0010103151150034440c0350079a0003c00c941c800d001501c480d07006038004608002e400c90074074a507003840014500e007550240d0805070509007191543d02081d104950300802d84001c1060900000000c10001102c0e0340340450043c8100050300005007070b00c048000142c01000c155030101d810300100c0c0d01c000442d4001c0318032490300140c076892070a400702c000d0700d0241c5110940508140058544040404403040314501c540101c400c10200d80c40d403d40c48952140901170680c010145803d200c83c0250890381d4004001810980720028000024445030004c0c9084801c0e20754803801440501800d851600243c10221920070084135411110340c0d40d01803030300e42800303c0e130008030104107281d000380c05540815500c0f00b41d1607107968481011200940091040f208507d082800c2c640c0d00c650158201d90040ea04030302140781b404858204200503018011014040b405009400010281a0700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 331396214 1250 331394964 331395007
    0x203040e010e1b130816060e0f01030e0d030203090d110a0b0406060e0c0c06010806060319060e0a0503071118010b13171e1219050c1905060a05040213020f 68
    0x4136012000d042c01100b919101c8102180c0c680c01d05c6809041c080d0f03d4001d00d034010f140100700d540700c01c0c541d003807401240940341000214a0b0f41c41102d030407a03a1603401d82c01039071086008074121103c0d01039400c402c0301d000b070041c1250b050540006c0700d444045103034120b81d154818007425000c540d80796120202130345084104c031500003c10012441c07451180040c4510350041c10094000c2409082140010340c440e52101a001c05040c03001343c4041c01c201079600007000120b4414191402400581422034496100c000300701d401d02c2645031506064070f48072801c6c01c006008000c810030541c0c02e0060401050340094164603421500902c0003544060319042c510350300c110b80014091404403c2e444e03608502c500035400c5050381080c031002c0c450010404c1507607040c1c007180201c0c56075484007000a4885200316010400c41d40608a114182100c40e204000000c40c8100b044840310359540940800300ca03030230b41d03000707601a90380a140780b00d0319400d4018000441d00d01100518298014445001104421 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 331397464 1250 331396214 331396237
    0x15060d0c0b120a4209090506011d1312030b130b130203160509010c140312010603091110020c0a030b060f1f4b0203040e010e1b 56
    0x10400910068001c40c42409101c290204130320301100724000511002c0f0301071502c60204158081a4800982e461800400c003818003001140321600b042600c48400b4040c20090040682c5010315030340030740c40041e00c01c2004040703440401000350740c5c04801c1c051124143c020580c1f150382d204030507540c2d8580c0c0c140c0c01c0406900012880b0010b400d020001754101ca60801941c41403080100c150030600e00500c40754040c1c81c089071313540211001620841e054210207011440246542002004000000c041c4002d10464111a43e03a95442c00c4043e9039058000415180030101380c00403500308030200b90140c0c0d106006907030194808801140e08401a60b00a80d10743c68008284401400c0c014441242c0c624195581c1c0c03542c260700c20440c40d102035184412420066080300b004d203042d214206151a1004640718002840e02c0400c848480c1e041070401404896556002d441c201800001144d007201c3c0c171200c00c100b040c0e182c140707034040d085c00c024801c816120f5800d60940000140c4d100603e840b2045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 331398714 1250 331397464 331397497
    0xc060f0e0a1104020406050708130e0a0218040b030d0c06061502011d070506180609040903050903070806100b031b04120b0a0b0d140a05101d15060d0c0b 67
    0x42e0502c05000c503074412259008a20400c4184011503004d03085074815500412031a6035140b80d07003207080440845601000a1480007003d0040e110081d13002421148207080c152052070791000c04010403540718080c0280d0590141c0c11000c0610701404100e000e940c05a240019403595445d41c28a40c4d0b089100e180005035591030050072102070900000d8a41032010380107000309030070800810a40c3c07051108286980b0750091400d42240d44002c00c80d00d004a0144c018800f131455480d010340960440c1480354464083c0d0000412503801c00100188644104030010b414185030110070b440c141e1016000054500c09613070304550408001c40100003e1003025180c2906282505250160b1340d005041c2c001d034035051403410503241c1d136801602220640c2005806112034100110989840c0050100030014011507001c0080201c1c1c5034812103001e61052200304075600001551502d400203900203140c4442035070003150181c14041ca1b0880b106220b000286500703030300d5800d01d00e0250040013440800050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 331399964 1250 331398714 331398733
    0x50705100b031f020d0204030b06120c2d090103050a1b050a060305070e090a0b0117100e070c060203010e100503030901020a3e1906020601060c060f0e 66
    0x1000c121003810014010310410529000400194664040c1c21992031142600344121a5011030b82d4101c54101005034000c565540c1e0380e243c00030700e0010844519100d51100b2a0000e84a01d0214066003200001892841002602014100402958200c8989030401020140c1094440407070080c080c41c0600c1c000c103d0303140c81d4540709940c0a20b2464000d126125204208500d481d01183c10040d1400b50902048903030340d42e42d00702c1d00082440c0c591648031030103c05100e0a80d0890f80021068042a41c8050f0042184418a40895410f54803610182c014510030841282c2100382c2e10740210311483c10300c4c58400e00d525440203a8000381c00c0f81c12100d001c10107010807013100030041c400404056020f142010000c000203501c6000d1200050044444144085186070000b0180d024110080c444441c2102c803221403901c0203038406640c1d6004400040685041f80903c10000c0c00300ca000da802000641c0c00c0c08400c4824500201c021100e0540700c0707080110012850041c10b4031b1648880090180b0740 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 331401214 1250 331399964 331399973
    0xb25060e011b020c090a0f15050102061f0302040b060f03040302060603070f0303080a050703020c0102041413020306090a0905280c0905100e040c1203020706080a1404030e1f0507 78
    0x10128035210341c81082810b00d0200c041d0700401ca000c4034850484110105940d190024006000001e60404050345002143c40b40c140041e5204070a84600f80c2c00c8980301d0790345000001e044000c0c010780001050464404200601e4241c12120748144068186c0e818100100040411600191411005078000201b0444682401c101e040014503481d180504c10a142d518003410b1080080d20350035035a50ad52000880290094049884107681035000315030390ba40d0303000d450418020715040780d8481e00c4070003002001d09507c2d0080d2800303140000d1600507c0e072110b0890000030103054608070f84a0185017032414031402c3c42103542802039848203001101000074078000d00070407607a03004885100c0c42c1205000003080b07140c41030740c162180c0d80000700c0e06840320b050582d0000a0780d801010380c4038a1030350120405d40d010500c40c0481e0607a80702c2072901d4840a1035202501c0c0850002c410341103140e800130380840e00c9070719640d00f14800542180d1035400151018051580504508004600000b6000007000b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 331402464 1250 331401214 331401221
    0x9060e06010b031602060f0a020c070f12050f010e030a050a020c061309050f040b1302010915020102130f050102031905090904050105061302120112051005070903060e03130b25060e01 80
    0x130540340301501c2d4600c1d020030070030500c176409131100018130303804140030b080700c80d00f0088600a85038414003030f824203545400d00480c40040000455960082c034001b000700030b0341400f0780d03035803804640b0185042c0001d101d404c4950f84c0015205070110b10841003580009d884180081460406444440310302a06045c1d4844c02d640020384640407248c0c0140c02c12000c42d00c0d55100c0c6411448050108014032010700040710040500c0d00012107007021041c01f14202c580541c000c0a203c84004801891155642480c042c8150148100c40c09608100050710803a21310b0186030b1a00c10301410070b01d003020240740100792100320440301191540c3d0f448051000e00d02d454041320004c00070b04c520a61400d842410300000016041c42000101903480b8035960412005000503039038038240800c10406441e100400030910500340c070003078510350b15111100d003c0f1203000c803c03503414a60010100d0003440ca4000d1a480e90340c001442190300006203109866201404021105c18500a81020649202032000309084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 331403714 1250 331402464 331402501
    0x120907050108090d0c020f0402070215040e0105060a05040b090a090c020115090b0d1412030405060f07090b09010c080c030705010f0e0d08010e07020c0d030203030f090c010507020409060e06010b03 86
    0x3980d00c121104e044280d407012050500784c1d07069500b0b0030a603802c080420301902640000039400232a010310007401220000c041d101b241c204d004001402e90369003050040030b1161820650000c0c0b800c210501107030100364014155120080c2030a5080d030350701c6014030100c039841188803006075102d08800480752480b002c9100649416802000104059000662201c4003820000e102461556400b00c901e81c0502202c030440c1f6001e1031845d07680c07509191241d2692401c64000001c0340ca060301261f00075128420303580030b0740c0c40f24005034900b1300c600340107450042e0160012101580100410b81044100740b02400c5020702c600b00100342d910f0a0040c4900344d4994004510969108200b0142c007103a1040c0d00504550300105004819111803000301c1c202980039a06540120103002c40300c0c10542d000004500c2076004c1800f14285858145c07a0945422003801b00500140c0184102c0016103015400400110712884000501c40d050315000d90400c0000d0340280c12800003c0104441c8902d1440700140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 331404964 1250 331403714 331403731
    0x5090a0f1202070f050d17160b091c0512060a0b0d141510080a0b030601030f06050601020703031d18070504050a080307022d1206070e031b1005120907050108 69
    0xd185d041c0310200760450103d807400b500002025544840c4081e42c00200c03800048800c01408a032046030504142141003603c00006510402100d0480c04071640c1000c120343c1000e0343d40514000c50040300c041d0117080944a1940980c0111001440307280d00303401001c05001140703001c500c1c5241200220900ca00051104400e81203102c400055540c81d030120124215407400d001029881e0080e44078001e00d12460307002c0d0148503131790003c000d01c041c5a03003400c51584600d000340500d643d40380c01240c407049a41f0005001c0381c0030380200c10040c0178400f8003d442a03005010380c1490700314168039411141e0f09a4803000414000141440301c1d081034205a0082c0c14400021840c1c1802c9501241c3c1d5004200d4a00881213610444001d00c502c003903901800649008040240f9000300004064440343c094410101055252a501d88142004215403030041414035502044590900c184100480365491300d504000c02000420021085013540b0f5010b582c0503c020701e42030313041034000f40610394003500214 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 331406214 1250 331404964 331404989
    0x102010c02071d190614040609140f150414040203060705030403020d0e040603140c211e1c080109060b03011809020102030c01140a1d030d05090a0f120207 68
    0x1c8030850b10606400e0b8400c1400143c0e40c160380c0d0015000040140c01c0b60802e03998104480011919501080e0300010b10003160100a81daa480c00800100d5000301c4040005629160001d191100060b600a03440645d040c5528189011100002d08a8603885200e2160f83ca01005001c2942000c1050301d81c002043e092052940c00d00d501d008c0d41e60110031300c05404104408000d110141c459412000040da03002c0c01114041c60300340304613030f15440c0042c03015015100884030b40d501c6c00c00703448502c072044001002810b003000a070303007403002031030036003180c610251103414082d00500d000880e00d840030480302d640f03404855040034010820707100103a1084003c2d00051005205803c83c251894206c0c203007a1400007540040b9100603800c500409001c000c441d4a042c03061b01407401400d4400d40305104003d400c110404010203004003540a8180b00c1106a009105680726044254019500144070800f1200d81280380c0e60303045c5911111070402c40382d4028a600c2c24200c1c5404010a9010303045084206 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 331407464 1250 331406214 331406219
    0x50d03020a051e09210105070201061409040c0e0705030106082a0d0f02031305160f0e090a02061c200a051305190501090b0301050d0206031512010b0102010c0207 71
    0x404a0064818800114400907840036221100c1c0e4100e070710219005e0545c51600e00d10783c03401d090500c80810300c06000c0d420301000a40445c418481c42040c4d0f0750304503e89241e40d121401340010804000c0c005c8840441d026000f04101110700d4806204d102d159403840d41c0c0398144400100b40000140180f5800c103198a41c08041c464070b842c03903a000c0100145d803651100d52052941c005807032010311942c000c1d0710000c00d00c9490115460000e0615001d032045034441380d4101c000400d9405188940f8a1034074650005101c0310809903081608a02280102c0719104d5660700040c40d80c0d07020302681c0d0f41541a00d02c1343c1a20300d101c2e01481c01203c454403c00300303941e00300307610541040c07003a08030301d804022001070802001405042c585000c3d200c0508014400f4250108410b000710550041501141c0c01c00400030f4a500c01d030b000c40741614405040c10080d0f040c1c690a010954001400c2c0fa40c00c1018020323001c1d216107038a42c0c1d03440003159030000444c0428503480060308481d1003022003011504103e405 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 331408714 1250 331407464 331407467
    0x6060109060509090a050903161b0803030108212803061d0403030e16030b0702120f0406180e0a090b060d0f0206181302040e0c030411040c032403050d03020a 69
    0x102c592114045c1c40104141c0e031002800e5045224500181c1c0c021071720307584180d00b4013584180d041d0511000c002c07841081601d480100b6075a0009114143c3c4d00d5000c00c2c23501d00707650000d04a030b001c1240c1040065003071411b25180c020149141d8080d140d0b0300d086940000c000706500d40104401000b291400581454800880c0c0320301c03000051000e810b041d2100240301581004001030407003413040307120a219951301c84c40c052340300800981d0309000500c80d590a100c0c03118004822203403800f00c0e8810042c5010b1821409580980c0c4003600c00503200104800050a1504241d5851080ca03031050002040724040c5002c07503030b41c4030252815003d1802c00346d0a00000d0140c1d480f04107600d404492903521507100ca50b902400189246540c4c0d00544040d003c45000740d010380141040e55414648801196500e182a05840c0000ca034090702d04c1500003070319400303030801d0360008041511516002c1280c64003201c0c0c502c20380d90160502800350100b90800c02c14407000340841a064481e0345825440c000101c0360 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 331409964 1250 331408714 331408729
    0x30516170402101803030201090203060901051e0a0906181b05030c0607060204030c150320030f07020124051815100306052e08010602030406180b070506060109060509 73
    0x402409903066948078503400e4020000700c813018840496400d00b0b59100e00d0002d010f484142d408030700a105584c040f0340703e041c0c1030155912603020b5055135400c80ca41e0000540700700c0006070200040940d030b0b4103c80f0214000b4001d41d071100c42800c200e40511849850045042216a104410f8000e000388081c48545d60202d10b0b03e0412204481c00794031802c89080600080c426588000c05c015180400011286401e03d4601c9107408070b51010403100d000c500790f503810045450b14a8540c00e8080000450030b0131740d01e000380c1d00308105200000d00c840010054844080603601000e0440c180c00d001004249054221040000755100b01c0600c181841c6103d0045500c403e0000c5d440740b9040030030885040e00c2a880a002002c0c000c0001c40b4900c246505c5040d03101000b4112200b0080c480c0200e000f82c0c0c019a0303001e04076013690380210715144c46c101084900b5407101e9400341d8407200307114000580550f00805041854010f002502480c00c286001605040c200e070700074020302205001100303480d130b030394030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 331411214 1250 331409964 331409971
    0x50c040510050d1a010908031603031805070b0d0e0f0c01030b060d0504060b0a0909050607050d09051213080a0807020d0804031a0105030105060d0203030d24030303051617 75
    0x440100c8001c052081c1980d5a00404070282a41403411030f41c1c0c554103c003140c021501007804c0c2c0703e09001c203844032202500d80c8910070080d002c22010402410009100e81d212000c102e680e142c2546040d071641d40c80600f0b010700760b4006550410049004414859940f05e01c0f0107030300980d00102800426026440d44585440102e241856540c0e0080c03005503c4100898850700c040c2c00041200386458601175008080e0507160b5800f989198070085145503080c400c550319960408002e00c43c0d96142081225154444135404401c039884400240c000b032010443d100c5c000000200c0540ca6a504180b54190151141e004406580c04000c40602060035142220042d40e01580c0c1701c05848143d0804c450540b16990004001301b1865207000540c80d46004298140c660407002440103484200810401180d1500c000e541500704024400c031100e4298020a600c0c2040880740c424881014501010383c10190b2058000c0703910713002040342207501c3e1140c0345801805400e024035035845504810741801c0005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 331412464 1250 331411214 331411219
    0xf0e0f150705071e03020d0503040b2809030201090204150b0a0c0804050d030c050d020111040b031008010c0f0f021c0e0a09020d0e0c06070b0c07150507080601080a050c0405 76
    0x20404075180030700c64012644900c0d0020085003644a040b1145140c2d0b0304084000c1c0d0041c00ba51003420162072168044901441d0001441c100c107407070b40100382c2e01098a40c4110b0155581c00030616024103514001d84100c0d6010b0b030000181817000340140026290350102c101c0c1c0d980f03c180014803800c0025000c1d10910031591615000d20040c40c5421001d074403454001c0b59005030300c01c0c640c4080660191b80c00b80e1061189003651102000d0390341c280e09880440a40d404182000e100612a408040c0301542d4462075005004a40c40d9803410b1803802c48130f130400c05c0f00004003c2200403800d1038116001b15828419880201890a2038401c10000c0075200e40c4414100103040c070b0b0303000a65503030501d9407000e00318810381150355101c2c07801d20f50010202d13800c44500074000c1450780301d481c0c13600009031030203203030007103000f120698868100c0755265000c45011500c2140c88029003020000c184101480b907407890b1600b81d810b00701040094030850f401044440420300b0081040309000c0d04030140d6048440a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 331413714 1250 331412464 331412503
    0xf0c04060509090322031a19110a050d090204060915060905130c110706202103100e0c040302010914010f030c0203040b120f0912040b1303050d030f0e0f 67
    0x80a280c0c080700d00c0903800600711a40d040616a06c58558072007d42c058410540d00d1810030701d0a41c50207080e01c1510100401070390040c00350100c024080e90040c074180100490000301100c15074001000c44035076030801b00030340f81e4900c24201140e0300340d0245809402030341403c0c1501890a4002040740841d40a42260b140e142d085e1080350a004000da070f0554200c010035945100d8903144000d01c03201d02d00c0e04151210320a09001003d140010910003050103035016901a081c4040c0c1e6004015800074107058007007000305400050100320382041a01610a480707016a88914600006204a02640250001c407546002d01c02d03440c1c0e08821215400300701800d01140003820400d00783d0271030055500161541d880054525403001c6074003402407041c09000340440480e290034100954500da60113182a5019007004240210001000502810100c07112018402a200e569440c10080d4452005001c00e4032009c108082441e140500c6a0707951100c40180b03507c0320401ca0040e51004030943e085c810442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 331414964 1250 331413714 331413757
    0x40e041e02090901270206071403160c06171909030912030207030b1806071206050a09020304110f031b0310060806010e010e1e0702070302030f0c040605090903 70
    0x40c044140e400480d0010808403040c9850718030345004c3c010801078060070390b02c00605001c040e008000301c000c109402401050401049540e5045440303015002c054440c4000d1003030721400d4007074101c501034003131152200c40c0c505031802d00c0144c540000b01d002243c4030241c0c1400c005003020001e4070518060a0040041032080721410b041d40c542006420440790f80807800000c400303160300042c65004072441003030651220b03a2030440c4100480c100071080c1d021340d0400f40200da04184612a642c0080d009002c0010b4942e0342d44000031101e50f5280e1020300352540100401c0700740b00594901d0241c00380180d038840600400c01d00040e440d030700c004100c14055071481c2c000741ca043d2002c00c40008000f11807a820482251610742c447c1d40e8410074420400d81e00a540d0011402485000e0900d0080c54000c6042c05e28495540d400756000100a107880c0071481900e81c00005070342e04110300c0b0b07072008609001d0003000301c1080521090364010f401460041c0c00c03500600c100f100d0000b00300c82034803040740c40300400d490 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 331416214 1250 331414964 331415003
    0x106080a1805240a0207030206040f05070e0703060e0f252003070213020a05030403030509150406051501020a05030901030c0c05010609020315040912140408030c01090201090605040e04 81
    0x50502010303003a481900e21200900d039003948044494110443d01c51003580e603144a00c416032181c2a00200160071800c003060010380e80000c1d141d034042c4034005035056140c40d00d5011448000445a440c000303501c4403020032100c1c0110a80343c4c4c22403d001c100760480e150020311800781629030b500903418030710380c030100c8200d962150781500ba00540399080c10042240c6210b4003603481d0001d800992080025500014034199240300319440c1b87c1c1d05458050941e662514168000e140050940303000340200b00008004007224400300d84954420180021681004410340131040030b2000c007541558040869200801c1c8008191002c01c3c03024030740803d100072150000c8400650642000303107607608145002c50f600c2c84c41d4019502c5642ea50180e0b900700100d22007048141e602e031a0700a01020300d51040d9028940c4200080800e030b5040c0c0401c0d600e8669240c0d8403d10790391121041d807413182d655009413030442da4001144030003002d41e0304d800b500381130408643c80c10741035000d03000901070345010010900c00c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 331417464 1250 331416214 331416251
    0x1f08091002040b040e0c1303240c020609070b04050102150a0e120307030506062502040e0d090f06030c05040e071e020c0906100f0e0a0302030106030c0611060106080a 73
    0x810308030035074586603503240c1c59009130803e0242d091644031000000d1040003507101628000d44002d80800c040514503102c0c0d9100221500e035141c2494801e0003401c4007141140900003808110394003c00e407a00d400561a81032050f1030b04801c04010f010041008a40c0e4001402c200c03c050f8940303204060b03100d45040703500506041c0c21280040c003e07081d91b03960090720354001d140300f01410f860074010f50341d822041001c140315010080d403004510412480041b50a80c403a01c28182c8090000502e00394100c1e0070360721b445044a45000041c200140c2802070010f4940034400030136481c10f0903c4480140c00c00580240283c0c010700944100e0580000c00f098824400d045400e042c0d50f0075110020700c2004001e403580340d0a0b2003280070301d01c50000701c7c1060401d0030100c82d0942c0d0340d40d2040c0c3e040880740e108860004404c009241d101420140100c0983e40c20701c910030042d8030030030305035014900e041406040270f0003071003040032560007040042000ca07400c45691540041020030000700c01942e40344d8007010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 331418714 1250 331417464 331417483
    0x516030f140403020304090b030610060309030c081902010e0604080415020c0a0b09040e0f0607051602041b0206070503040c05150d05191107050703060b0d0b04201f0809 74
    0x29040701100703000606801100520555110003001d0280403c0001811754400d800d40c0d92020003030440c0420004903100394010110700707119181010700ca541e030fa1280e102c2178001104030006124045941c0701c11580910546a01840701c4020380054035040e02d80011600483c4203003505000602da200208510900070031106400061808054645451220030340760000c0440f2801103180894446111b000040c4500e91454104c000301600e50f54a0b000b02d5603a00038403850b040c85154406c640c40180d940c0d02860098850b404c0f42c105081d80b0754280280343c510054001d00500c1020001d01010030781f450b660070182d1b04244e03888500c41c0a8855035213041d1268460200c2110f14003401d02110f68906071070b502006c80c1e0070400b031083d240c1042844909201d9098014003590120004000088903500180c840c010b00400c400403200490f1150011a5000c85e0111007069145098030745034400c0804095101d8800e4901c0c6800c00c0c0365840c1c01c5480d03152005c199051104003c00030740d0303d0604200c580304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 331419964 1250 331418714 331418741
    0x20c0f1507080901230405091f03030509010504080102190801061103040909020f0910030c050102070e0f0901021201080a0303051605030a11130e10170304142d09010501030516030f 79
    0x1202040d40311790005580050055a10915065010424890754000c500059802540305001b5441c0745540566150380840051418840c2c01d01c00001c0000b020b1000e00040d1240d408005000795101e0310003070401c50705820a0007070040400c10040a407200000751402d980e00b08400041b540c2031800000c5d0449411500203a010021104022151618505007811a0f100d03c000320303225900ca50041e80c5807100c5008410720300200000107007402e801070304c2542d04201c650000615040403050350460000c0c00f40c0009031958010b50071131042603410b10449a000c03040103451404482c41d1000240f842c40060314200c0c102e03441310091500783c030a103421906000301110004004969a0018510b03201d4101d4040e10314000e445800208004174405407012001814003441c41c050030000c00041d040c01c4954619003222410450800c0c600d6030900301d0524808803200c007241c800c040810081c01442c141c2200e4105807d000500020090b0303104964181159411301003041c400081c1c2d04001440320100707061 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 331421214 1250 331419964 331420007
    0x11010203040b07060207020a0e0606090d0f02030105040305033907060e0102042607030c05101211030a0b010908120f16080a020f0a02031207031e020c0f1507080901 72
    0x81c20050301781e0061021620954034140c5c090b80d59114850320034400c0342d05540040081100e000c0e40d26140041000c03403407060165101c21403107170f00800e0842c2d20403282100402d10000074001c0e0241b445200c0980d000c0c5032415404201203142d600c0620704081c410ba2003083d5800304ad07040410030a5004100d42302d00f100021520307290784206241c1c41080c1e24030301d038031201c951440f10b8601080125030b04059076007058000c3d03856480c1c072040c0000c4203980348418041080c9404007801d02c142501504542451030000d86440f81004410102203500316004107040c001940400c000c51070011640541034082e0b501e81c50b40762040e02c401240da070300c102a51101c0741507050b1141c104205000d00502524440c0344d00f181c40e07a4484000e05651030302094170103541640b1558496010008007002022007a120389441c0141d05003204015403481c480710040d04c09608540c0c031040c4541086c08010905d540110391031941d2070684a5020300d01e01c90305c54081d003114000249242c5c0f5074020018411156107418480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 331422464 1250 331421214 331421227
    0x307020d110a06050f0a0e060d02040909140609060601110a0c0b0409050c181327060507090f0902090d0f03030e0d17071101180303050a052211010203040b 68
    0x860401c0680070025104a119100c0480d04038401c5059a43d00d0300280d0769a854840744840c1590200c4194440f241d2000c02004089800c410600244c80104450712001c64000081c1c5480303151003070398403954005070340404100507844a00081c0d0b690429020300b04501d146550040490914009000241013402c070350707400040028800c002401101c860050400c80d0707854031829071a0358403030828804500030f0031a92081c01854560800441303a0020381000401400e0000721452040d11111094100390241149070184105400344940c0b0030348a1500d4048682000b1180d0302c80d01c1140540001541e02066000054403054600c1510640210500100c02c0e241d2070001e000d03107001c00704100c036070041006030b9141c00c1c02071820b6600300d014024030002075074801c03200300c0352107800d804421481e40d211071083d018102480555510729000b5940070903a443c040000006036000903040c1e0000e042000508040c1b80f600015166103194000e0b092800722100a004070b10b98000d54004060844002a64 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 331423714 1250 331422464 331422473
    0x271203060a061b0602090616080a031104062a060e0303040c090605010905040902210c030f0708072619030206070e09011203110a030201050f09060402011403090307020d 74
    0x654403a4200310703041d149042e140e600480d6000c1c48140302c0b80c1e0490740d40c0211400501507401821201e840600100c0c03e004000c04e0b443c6a80d44842e40507910303c100051f084108641c51300410356003118000d8041e26144c90504028102607140903c1000320513100c43e034001003603504240070601a0450010b0048003440031400b07460394425101114155143c1500051410392405400100c640503128000c40c00d1401e01404042c1480c464100e9102107028074005000030800c540c400b50540d000c005125212105050525000380302079000c2d41940010000c1103d940c0001d84002a1918403941e040e03c0d490310400681c20344010890b51384170340940c5080c51807940b680001404042d0003a401c8501d29111482c069034044100700d1083d401800070300042c020044004a0090454440e00d00301810200e01d0111901b444900d000840040c0d46460078016200b11a0407482d80005910020740702c41d043c01c0c1d0010385016816000500590804400a080700c0c50910644451907009060811441c0c541d160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 331424964 1250 331423714 331423717
    0x3220204050906070f09060801050105090301020d1b090e0c040b130306060303081e0603060606130b03040c09051b12100506160507090e0c0d08040b0403080702010201060b09092712 79
    0x6420700041e05c01e082030007800e4400c00a0000301c60700750715080683d90801004641710791144058035010341d002c1054041c4035240340f045038028004900750041c0ea9500c00001800001c40d9448401e011480c4810700440346041d40c02c171400c5440389102180d4a54003141041103c03412544060003d52800c0000010306d5004604107104110035600000380340c0032540038022601c1c042c0c5001307070968441c20000b00981002401010b45205d914052040d4503074441220109510403603044132621a9aa010805951140101c44c0c110440c030307101c0d20b841d565100d400380050003017041034110b00d4515404a50501120a05203000d48409442c4036624810b00316500050365403008c040343d0512400000185004281c071540400c0b1940c0409460021090020464061104002980d4450040000003401d412800051000707504c40c008054460350280000790845100c0d07407100050764000c01c1040407980d608503035182c1c0032019107003101c003a1600580d40c8800280c0c0147c07803000c1e40b01c0c0740100d0320306080400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 331426214 1250 331424964 331424971
    0x80601030201030b0907080412030615030b0307090603030507030c0809101805120a020103110904021c0506040903200703020411040f080a080a1b050a080703020114010b03220204050906 81
    0x80307040c440008004c06100340e9060032181840080c0070503010800261203580009800c0d01c01c2d00e0701144071520b034880712415504803601c1e040800e0391071401481605049c08224006d02480000b0000b15155880181c028032880308000c081190883c1079004015803002950300031800600789090380c80d500d40b0090700502c4890a451003000481c00006a10b150070101c08140001e40303c0a000500400e500540c040c083c07600c2c00700d400c04424081039229072294409800748141080b41c0110342090100002c040358005040603010300d00f801412320100750440921040c0c00e10741211101384155144640b402d200f02c0303420080d0b000342010000c03000340038100058010790b28500500105a42d507410300c035607240c0c4100001461042c003840804002c80c054903074280c80e503003400c0301c516070304c00b42e95145414150035580071226800c020441d041810323424803505251070030303d40e80d03d40154100414400b142c0001410840c2804441c841f400d410360740e501429a0095000c4c006100a04043c10025104c21089 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 331427464 1250 331426214 331426217
    0x30705071b031104060302061b0c090c0306010807022803020109021e0a080304030f06150b0c030d05090313031203020d2306190608070e030f011d071d0414030301080601030201 77
    0x404400c160307444c01d4400c00317007147d074020724051810300d10329501440442d1108080300280151080102261207000c05984110350300e42c2055542d2030824000f501c045005881101154002580e001e242e002c1240c080120707020000040002c0101c61904902510700c03c440250803a1030049440760304650280c3c120ba130700c10220340303048020781c9841e10543d50703004034480034000b59100002c60340441d0096025106035090b10b806d10020715210440400c1d981c4c0a002e10140e164070000d0070300c14210191140a80080280014610b8000c4106403400102d4060201a00480b0124141c480c41e90082d412100d07034008110062020114030008016402c54905041503599105000107003a0324100707400140107108200300483e100d08020040f01e0015000b052102440fa00700003107a034658040010102003000780b00003086424441c2e8a01058094000300f2402c0307036110400501128003080c0750129080c0c400283c2c181181c3e154140514025800082d04100380400000420304440210b0914140c178000e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 331428714 1250 331427464 331427483
    0x30c0403050d020d1d030a0602070807020604080d08010f031110030e10060302090906060607060c05040b03040b06040614032a15031b070804180b040507021518070b030705071b03 78
    0x2680172200440881c030106581a00072212010000d8041c0c4c0c003400380ea60240c06410704001d0241e0100d14a940316410196841d403010180c40c42c49648000040d014005031400d07900120b180d680c40302c1c0c4000c1a00011403151183c54000302c0868403a60154480f204080200c440e960065031900c401028a40002d81c0205e420100003000410b0001c0e105000c1c450290089142640e9a1110801040b410482d80304101d0100f000040501c005805140924007800c1c0600c2d0a00700002084201c1d142948080400d4001072805140c5640c04280c449103a4541003440c1c07280301c041d004121200882230040d9605c6600310210381c1c40c1c2201d800c0507500c00c1c1440c1240c80034416014034003009074051100010071a4604000c140410800760a2400918000354004981061400002001e650741100d00c0310042c0d00c015a030b081914001b041c01c0340c1004248840404564103000c0407a04d03040a405140103650000000c60b07074035440b50040703a480c1a0010051000340002c20000a40d1710b4481c40300b52400d501c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 331429964 1250 331428714 331428737
    0x201050730030f0e030403030c061806050a18020f101701170d05090a050f01210f140f1501020f16090b03190b0601030b120606101e05030c0403050d020d 67
    0x3d1501c1102d03400f0500c08011414540765640448a90155800865450343c44070212120318038000d0340003017000d11a540c0400c40e880d00c0c0407028201c1c3c11022001c1c0410301441200400768076148441d0b0032403071055030802c110b80d00801082c1c80e4151580e4003000b01824520000a5028422200c0081c89041c1c5040c0c400c904c0c1c056034126402e00440580a0f445254803400300201d18002c030b0030b03001e07942060500c509480220008028210f481511243c015916041030101c01d112034030803c441e01145c501c00420908000481c030240c10030003000d0b001300d440d001c066118140e00801c00103291031410021103030f101e0318040f030070002c1500511940c4c410710b00346a0b600e6090301e004581c892005000f1003880203803801c1620340350300b88900a04480d06140d566609041107480704200d01a0400c4104000d20150404200b44140c1080f1003000c881003000c59042c2c581008103c2140351600b501c0c81c03500c0b5407607480c2d00d508800c9600c00ca900c01400c41c8074014285800b16000309a101250105460301101e296 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 331431214 1250 331429964 331429991
    0x90105090a08030a0f06150306050307050105041a07051510090b010e0603190b280e0c0f18090702061602010213051c06050709030b130f020105073003 66
    0x1e000300c40141a100c060002134100440317075025080b0200001d20100c0c03000e646001104002c0c06070780013000000e44502050042c2e080c2040400014802031070480e01d07061800740c0c0e03650901c1580040e603c0454000a40d0001e100d03080002c0000c8600d025091040303800c140b004120031a00a12131602058244035402d03405601170b040a0100110140c4918038541c0d0b20444030703144280c04075961103002e0b80d440c40486140c440000c6000c0000a0523180e6164603003540c020074111010b54010710b02a00340c9401c0180b01000b180503200680569907541c1e44900740a0185030b89402c41900345500320080c5810003032007682c0050170034015074000c491043c030404130540c220309074410342c01356070542e1007009003c00c03403410059290141c074128440e80c044170350b00d140d5688003551015071348440003410402c400d1091160743da8059070862034185001b07814846a65403100d11a02c45003001c0d06000001c42d010007840700740c5034594108034450010042490310356598111417481c240c0e003d00044d1a048202ca07412 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 331432464 1250 331431214 331431223
    0x90609081c06121205072d051b061611060304060504140f07050f0303040b1801111606030b1801320d020f01090e09011e02090121150b0309010509 64
    0x2600101c4a04c0c540110540654582d03028106c02c079004156400043c04002d80da1040010f1424200d90200e1007441c542405071610b003801001d1051000059a40e0b112130b41c41008a8140d4540c04048441e88070b01d508100c000ea084007450303280c0003640002000f08001159101c2803040b403082d110320300c010f50740c500500d98440400e115000c8a502c002c0c4c045c401c80c9450710b20301d0300100f0000d084904d402d8840818600c0c980040b111098100e011b01880400c1c0e60b080000681054038443c01020a008045e241c00f080345624802c00d414581e442c954200d10303458995061081182c0c1c1d217101c5003035595030200e040410030004031036070808230068a200108514049101c44400d0000d14030201d181d002d408100e507050425030994144503c5a500007010320300c2c46103d5210f42d0070600005007285990342c80f80724148241404c5000544108920b00b8540e801c14220a00c492400c1c04d51b0201022079102500140505071050f1041d84000300005820108540251300c01d691fa00000d101a80b04e0011181d0b0b217 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 331433714 1250 331432464 331432499
    0x2070e101508060a030615080a1118070804030e0a03230c150306131b03091101080c0d0b030118050303040c0b0307090b0307120905030703030516050904090609081c06 73
    0x1c881861302c00c0020640e00c0e04150b4180c500b181c01c22100607030343c29005107402101c0704c08031003600800d01440d0452030304154001845170100b000029502d802c1c20024100c4000820040c280a500b10b502d44254a9102402d8061640180040990f1107004175080702d682610207503038010712903031441000b46d00f0034080c40285144410690b41c00c6807200d5080010b00f500501810801c10355403420f21081401c00006c40526076120b440000e41000c4c0e500b041058400842c2042d814021444103001049450104540c007812401000240e50141c0350002030140c449500c4500c4440310820b004018044044011030003244a0003140c030344e0f0b40d61083c5589080c00225a80d078042001074a08212081150700255070080d0503240520010304400c0c150342c12036400080c2968243d102180410405130184580780c0c01c880c1082ca4100350500c0d2100041c000d1040d060454001c80d100d10719041004039a401241c2010391042c0d400e40c4440c119203a290324504901e024041e190b0910300c0005e010b90301091010031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 331434964 1250 331433714 331433719
    0x1060201021b0c0a03031b0b1f0e040201050301140f090c09010e0a030209130c0803040b030402091e0c0f0c191b060f0e180705031504060b030601080702070e10150806 73
    0x4c40900c1c41e01e0580b09408070400c0c0700e080b0450b03003403980001090300341010f1088080800301e0321001c0c50070360f091801c000a50015031380040880180f1001d82e8002064a0443d078114818400561042d030100d10b00c1859001850380055a41c1c003880100d502d004060400c1038000e33600c200800700d4bc0ca042040517092488060740005202e4041101003094440c1d0b1849240560300c6506565540c08000e403440d40254084c440002d03011045c4411450800c0b0340e65045480407a000c00c1024040c440705000710340c0070301144400100069000c502480703039415661580b03c220305864041c80c0c410b21701541e801445804490715078035245600101c03000c1688a5054600940c1c40d40c500480515050b00c0a00c4000c074019130040b180c103c401410303050003840501c00c140f55510141c403424600042c860700d200c141081c5104a003012828011064440140c3e50310087c24604050180c4070300d03070b003a0b003400c400760815408078407241c04014101c000110b03d20110b4003860b03c203000361100c40b40c00710380350034055aa10381d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 331436214 1250 331434964 331434979
    0x61803020a090b0607080c01090b06180a1d06010305010923070e0c0d09030905040513030e04020a03091e0203100c020d0e01020115030b06040c0804020d030c031701060201021b0c 78
    0x340d41c406a21010320083d01030500b03860b0500ba0380b40d00030b80c1e400804200c07030f42e42c0d15902c07200104414600d0103034210406035499041d82c102001c2c2c0c000741d10780080c140c8078107da0303901500640d15041c07100c40200a02000036601c0c00d50b12803c01c40d020700f030614401d950018070b40d580203e41c141c1c641102402c5e040d51602420b001410101ea03c4408103000d00031088144c1c041c041c0031000580e6101d0540030920945900301290701d00f1742030105480c4001c0144050058032842440840c0d00301c80924801070003140c1c0140d0b0f0f82d034100c2042e8020941005c019103400346450700c40402d00101c844680c0034500840845095000041e01d01c0155003c070203107a00142c0000d20803000140c0182d40340200f110741400041001080440250040c81080c0c2c03013030350035807170160a020460401744125521030016150809130740c0b0700b54010600e44510600001d0030840e601d038407501894413a000b0030031a444a401c4140e000e594840c4001d0107900312a59110f10480740700c024006c0c1400c0012415604007016108a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 331437464 1250 331436214 331436219
    0x3020312070507060c03020a0e12030f07020406030803040c080c06160b090703140a0c05100c0b040507090606080f090604031b0305090604080715020610180b03010f0501061803020a 79
    0xa9590200c00740050040c0801800030704001641402004000a00d81d500180c0714600100000c040c100c5001c442e90280d10345500b600805c2d900401100c0e603141c1c0d0251034590301d10b828030100d8000c100c1d6600c0900b00030004014003041003024540c8000721604170701112a0004040c08003c143d2143c11240e6040078407854050002031030620401e54050b81c8002500c01d5142d49403500c0740c148080d45403940d00c035000121078000300002d510206000d00800e54902c0b6216041c1c0fa00549803242410002d0140c1071048001000c111040012401600d10280180845603032a00003038402c20054581e40602d00004000034198500001c200d88030b10b0701075982c030b281c001c21640140d4100700414816000c020f003c001c4494243c950600400040054500030100140f50862200156600f00600d5046400250600078046d192440050564023824142020307080801460402455810001c80d0154244881d0403440c050b5940040c1c101d07403175900c45549680080e96400c4d400802404002d5200c9030b828802d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 331438714 1250 331437464 331437487
    0xb061804170906041e2607350d120509030301053001270c1401032003061008010b091302220e07090303170702120705100f110d0f0f060e09011404030203 67
    0x1a440c42c250312321045001c1300030820034802030150003d03140c0311a4011010545542c0c0d012060b50a00d903401c00c0e08000b1401d02401e095124072061003030500c20ba241102c1d0048c0d09507012030504105950b80f107010321031118010a240130706854030943c03640d0f0041103414403601842d09031090100d0340c00403a410103507050049101001401414580c101036840b000700c144a411b2001064442410041d400c0c0c51349806002c120300c0d21000d828a404000b1240010071072010880f0541d003843c003040394480c0c15852404141ca000380211500b180182140d000420100f03800180e811054401d6400520411381c2e075050150b8100e900c07880b008001400e4202d9003030307800f0084a0000d07005100b0b0720613a001282200301c00d84603508800e00a5400d500a1700300c0c2d21007140c0f9846011290400314505101c0c000b0f4000300d02c40c20380616420b00107201c0e02c500005030030b450280e2051034038034407102c820041c0f282c44039041c0141d03460487c2d000c1a9503282003100381d0710124074820140b060754103900441c50101c1c0c5184 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 331439964 1250 331438714 331438739
    0x60412020c0a080c040c030e030403082503080f0a020d060e0402030d03051e0402060c0703080a120c12050405070510031a0406030b061504120b061804170906041e2607 73
    0x10106c04040c1d4401803041c1d0858144001e000450040006586030043d002d010b026201da8012400250144003001070002034004030120f61103403000401d03841d542d81d8100300700081d1040e010358040c0c42d880c00601050800b5103001c0107000b14005d400b1600300e094101d1040d81110000c2d20182c07007070041c3e00800301d240c5916508223503125101524581c00c040c41415101d1400071240c0081f00c0c9401c010410110081d800301c074001c4816110700d802c0c02807541c0d00d0310140000300e40c1680034010300d4603100081c00f03000041100000a00010b450380c650044061402001003040004a0b0740d104850f0b03098603101d00d0680500803c0d40e41080095106490f01401c1200c43c641e0798a029070422024000054410a51065014100c1c007802c00c00c14a881c2840400a211201485c504500d452110070310010a0b29034184100a07005081d541d695040f04200042d80d5005662008115007417040110805102d0035410504458021815054211030076483e000c00940c540e9526520343d0005a040004056140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 331441214 1250 331439964 331439981
    0x12909040b030102090613061d1309020d0b0907090606031116021f210509120306010e0d050714010c170d060b130510020a0c15090503060412020c0a080c04 68
    0xe000501c1c2c0300c45d0070081072003074102600414604c51100000c200d80c540012a030960b202901c0d200030440c1011400050094100d88001c040b09551460784c0d00031912441015066a900040300310b01034034200d41203560b6182c290003050140c81c00c000340050000d000e40108400400900f010ba400e02e1381d0b440440c140341c0d1200000303076407207044000c1c0019510044107181c901e1400d81c2d644c014039564a5050b40400c5c034640c2d500050100e150204014281c1004165502d00258a80c00350340d03241c1341ca400403a02d200314803203200c1c1e0003556040ca91040050014802c0102e0f03040d00aa04074225950740191509100c403000a0311844034101d501c60b080480340010085420464030004246499000600c8a0340120209107038a480300802403109250508204040746010b10040500d44059511b82414001034442c00d4000015442034450150280703448501914000d803c4403068601402c0807030044a000c0360b40c0d0054000c800f58020142020b110301010744420b02c005203078400d02da5042c08010078552 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 331442464 1250 331441214 331441219
    0xb0111010b0a15050f0301060905190302060904050606041a030a05070c0803070c03021501080c0f1005120c07050109200303030c0f03131b090f0203090607050304030c020604030b012909040b 83
    0x4105c00c201d809400030103540a072010340d80700c04c0c695040c0800d000400080740710b01195032400120070801a641c0008481d2850806c2e00c001c109502c98201150f101d0203580c0240403008540624030310143c0380c0c4000f441c070480c5034510034040f40c2c45010f4295a42c1420180140c5100420400100c00c0b81c00760501c400c405200388103c800421099200c10f18440d42070b0000d0142e40c00580100c4524545214421180102112203034071001100b01d0207840343c89a501d11a111031003074030014542d210407a0986074940e800800a10010120385020038401161b0f0342003944040c03104840e01304c681000000e691050462224031444d090310000c2815490304002e04050410107040c14001c00180c59815140d1101036050f5550102410f141e00c0328161440c10131404030311881441000304440000400341c1c0c10000c3c500301150344c3d490300c1c182100c2030b0416600186d00003c4c00580001009400512641298001100d0000c0941392425a804640c000100030b110301800344400b41c01480e00364411410601d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 331443714 1250 331442464 331442467
    0x1020415030605091b0f22051806010f030b06090402211605030a0504050a050a0302011e1503060203041509050c0f0306060109032405040c0e060a0621020d0e010b0111010b0a1505 78
    0x5501c1c10790002c03403d0401f00b000b041d0b040301d020452400c00b008003a0310000030076042c1e2400d140507000207003002d103c2c00b1343c1420103490706004d01240c3c89200c1160204031000d00155680e40811380030200c01500a030980c041c1c0390107800015040ca9032141d15201c120031a9840601d540c856803191000380101401c261503501900e0b4141c00022030401031000554480c1d00080b034440c1110075011f0307580103d2800740d4881820840140b810840c100820b105503980100c0050701d0340c407a800c00751440b681c0410076140083c58894180207000002512190140085440d45000c40c8a60700307146d2a004240d680038045081d4807810310010700d5035181c0720310f40e94800440441d040715590642064540030303681030700d416103850f07010b21280303c0c2020b0f2250301c03400030340e4416009407030028020682c078a8003031111200c41500400352181d0209030111040f28800b00300c00d01c01911540c445074000c0001e134100e540868407100344464081d806010b4000090b0000744181d44103450004006440140070002d8400c0060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 331444964 1250 331443714 331443727
    0x11403070c0809220b01080a060803090607030921060501060302091c05010b0d0b010f080304051f03020405040903110115230303072102060a140601050d0b0301020415030605091b0f 79
    0xa014130b501248000c3c12001060791000400090070540c80a401480c41c14284582440b42440000440b1100e000594049551304085d0504623104885a08020341110003507003a0402094104010080c107030291300d0403c1581da84020503001c91080041c1c11360855444802483c040c0488843d504400c0c0c020400494a005a04000340100003800300c1240e603114003000600c071503d200011440902150402546031500307001c0000d0700141110104d85e0744c5041c1148c10003010348280c0540c0d00601001c0e2051094181510700a4440d60103500030403061341c60454900ba1410101c1060000c03142c00c181c000030741d40f00720201603444440d1888030b60303050301c0200110000185508403194500074581446120384000220017030622801070481c550b410b00b0614411000000100b40702e40114003403d19030358030301240c0c042001500c560a1040ea05510100d0b00150303002d034a1b10b0410b40f20301142c1e0100b02c01502e450400000d243c0c107985a406413036046e10300840d2500341400610bc0c00410701c0c02130b1704114 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331446214 1250 331444964 331444999
    0x7030c09080102030721110f07050a12030608011401061d06040315020306120a110906180103051c030905060f0403090801022703031206100309051b011403070c0809 72
    0xe20030355005c00041c11074820180c80c5040d1160345050f59800b00b50a11001180092451050003003160901501100166460802c80d013000a24000c03a4007101e0401c0e200110a0040e0007071032184550710040d424a020003041407e11050181a00c4c40760311424681e000540604500303000d924100d41c0c004c0d20030840800403401301c6d01080140001220003584d42c6c5810700030f0040d0041d078000c1c0c1d0961a40540701c0f890008503020280962150280c40340c0440780d94160001e0740c02e403800b001c000003440c1c00c0c200200600802103140103c7d610f00c0c580002c21001e481500714119041108081c1c12904000c000c076044c1d9582140c61034120740680307020006591200c1c2c00c5400c80e840046c550203600c81c0c202284c3d54407456518455200038086024508040c1000305040d1100402001c0030312a4994449006035a4040c2d884805220b80210071a00741d4203590400680410300c0d520880d01103401000000112003400044034030840141e40c40359020b440d00c2d230301c00c0695000b00d10f01640c0007841040380f80105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 331447464 1250 331446214 331446217
    0xf0e0f060c0c031608040306150f050d060f18120207181a0307080105150a0e07080c0c07060c0209090307080a080705070209090a0b0f0601020d1103091c03020f070e07030c09080102 79
    0x203400783d011141e8491452900908803001f4403068071a8600300c040c00c1202b40d000c0c0e0310340387c1100e9007a218800350107458517000d001010310380064031102d85414000800c1900c40200000c109204500e0900c2e1504000f500340d079a180544a081441c2900c011101c401c03001e81d401019121209101040d40002014002030410303140c0d40025081d40e565104115603011107030205001244240e4003405401d08001d03c40000f040002c0c01107050140c00c80100e031031034440000721040510b014042c1c3c4c100b1a11610000d10411444100380e2140d00084007107201401e0100880d0000b5502c0350050f4034001c5820003c0c0c032200f000800c08030620030203200080260722051280361003025642c0140484402610f0000b96000307004d8040f0910403014000c00402c1d0b40c0001d901091031003103043c00010229200022840e601c91101d5190b00305c03662015418407003400403112a0907511940030f4032013103c3e170901d0031580c6000c948160340c0048810000324400a00a501401400e000e03440d02d0500e40c1c1d11000c240742603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 331448714 1250 331447464 331447507
    0x1103090d0f081c050a020301240e2701051e280b03071e020d0c02060904020a0206010612050405070b0f132312030304230601090f0e0f060c0c03 63
    0x240001c84107000060719513841050f0b44405618021070965044c4003030020005030208200355150b550703900c0c64a0107070080c180c0c03202110008000060035580910207110310354104c001d4240c86020000041503600e071043c1010302c203403021803082c003401c4840c20800c0103101000540825800b22411920950707444071b081c0390060925980d4161b581d0400560080c100320b001d0201c51400d0007000e8000b1090381c0d0204111800700300c83e1404d0301c0303141c0c0c1c5800003070788511607000300c01d07842440000c0213030905801180f080e0494010362145865180040011420b680d4100c034014159080000103101d6007180070301070086207d004094600700a546843c180e0468055008200e491402d454202c40341141010714814155050302c40a80c04030b540034880d5034074000940300800581c003000d0b861840c1d5a0040314100c03118240700855059583d14030311740008240105904d4402410a01015041c1c03100140d400f00b607170801c50003481141e0b50300c21a90041e400c1300d4000942c901080003042c15400001c85000c81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 331449964 1250 331448714 331448737
    0x150313060f02070b01060203072105130e06030c2430040213060807090509010e06040605010e0c040b12090f0f161a070602130b1209010c1103090d0f08 66
    0xd0303c04142c00c048600f007505a02a00c01c640c0100100000240c00c10340030b0a00c009590320303140c1c005809030b5091390b00340030301220a1001c1c401070b500001d4200c0f02640050040c80c01740e050720460000241440065030000082032046071401c0c0382103400d01017a00050030f803802041111030b007005884e88a069500040e0408083c80f01504007400709602d08000d5107418002ea005041007400d15103860142c60b00014440c000b0401d6a40c2c0006040c45029000060915401d0003550414a824984038004100038020030058205d4140040c002e03142030f00c100c406440d20040110308054540c01c5d00604408010401e901900400e034540caa040300401003480480608009480301103460b004135030701189103034810302d4415482100206084083c1044074045600601c2c090f0b42c90024200c9607058003030542c40030541c17070800500b0003030140c2e40902190003400400001d0240c005007140454061500c4030b01141e03d81c001300007295a9281661036070602e948100c01c40b46640b895610b455141c1d0b0001440d02c603 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 331451214 1250 331449964 331449967
    0x2150f04060c0206070c03030b030f030a180503030a0c080310180914160e09011b08070318030e010c060b03030d1509180212030c0706050c100902150313060f02 70
    0x2040040307074000d888a00700c00d0b1009150390301d0f02c0d00e001800781c202d0a50250074107544101546090310280140d140c0c4074100c0040300d6540707541240041052143c494000c80e48020f5400100d150305c0c010044495000c0d881ea100030041055807101002940094000383c503003c81c081d4000b170010362903030592222581c1c000001030600f41c181414200d8001d143c1c8540d01036013011108000c0e035450005030a0a4440b203801403034150b5510503416005151803c4020042ea6100007140001940902400d200e1656542d0912101c64682450309107905442d000601040303160303122503a19482a28144011805818049000010240804d045a000c0d498040d00c0549030f20f4001c204496040403000181881542004248408074085040502d40701c00207100d007869900005040004200341c0d0382409204054440d00c0381d40703140240081e031043d5851500f0340110611400021682d2181090940d00580501244844607080c00c0701948003d10704000d80310307080064404201d41d03216100c1001e41050006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 331452464 1250 331451214 331451221
    0x20105060f0603010510031d0312010f050103090b0a051e0a061d0103110f04020904180c06020d05030a09080c16090f0603110f0109170102040e01050102030a0f0f02150f 74
    0x64a8402085406200b0070401000703145c0311030390603642280c668500000c030b880b4211001c89142882c490b5440581c13202003450301c62840c0c00702ca001d04858a41c503648908a030740e0001502076a07080301014180c1010704000070000036042d040f86620200c0e00704a2414515950011101000107464000916035124410f01040d0070072031040d0420041410194010340c0b45588260420701402000ca00a4061562071040d41d1299010303140761040060090104058510034a4505500440140c800104410300020000e0010649000c901c0707144d40c8083c80c4d030343c41a040c0e00203405414070440340f010080061002c010001e100c064400c0d8102c106414030b5600d00201403041d190401c0d40030f840680b4000003000010340780741c0c06172a0340000380c58076140954203000603a0051001d6016032240ea0445128180180040d4020320559a1103000f1501c0f60340ca5000480e40c074068921003c01242c41d081d00c442429024104106000700c081c811640b80311400030351a41491004e8901100303c1c0b0150052 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 331453714 1250 331452464 331452469
    0x3160f1401020c060406052802060405060c04050315060303040e010f1d06011209020d14010221010509011206061503020a081b0412050109080c0604030f11070b0f1902010506 76
    0x12080c98103001d1000b48001450040011900d1207103115400c24006c2c0058a500c607000030041d00850740100c200c00700c2d40c0c2c01140794040d4a500c0103c40807200c074050b1200203807816116505507420b49401030000e00304c25420905a40443c90301410071a418801400009400016250824060a41c05945c031442c0c525140e03012880c2100850851100c1c1013040800c00d65981c00204407800c410400f40100d1003141a00100320540c1e1010301c0503100c103060002500390303682c0540041280c5441d015481400c01c800e404a80c254440a003c0c0303582c49a1400300402015052030310512000e40552000580e0b1035984030042c010408140040c40860707004a00503207001c3e001429558840aa03c0e520030b00788400207480d22052003a405180b1030101411001c81c24050250722030640740b0340c450029951103070f455000741d81d5160100c40440005070860040c031001c0340b244000c40038084002d001001014104401040b1a401080d0013481440051003a18030900782040d9090303002103181c00000713460405406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 331454964 1250 331453714 331453739
    0x40207053a08041b060f14180907050c070f0e01240f11030d15060c1104090609320a0312020304030507150204060801060c0302061503160f 61
    0x220421905500106045a03009082564407142a407800c695070740d80c2da01d000c00c05131140102d036010300c0d00c0b95000891070b103810295500c00001d883d01c40003c1c81d00301c4e0001100303500c50650110030101d0905001c03110790034140e2106400c1001400e20f40c0c201002071901d5450034216030701c80c4046050b030f50001c00c0444585800d2038090907c0c4440146992411442c4050007200a1401800c01c0303120111820000c3c0301e68621442000304800341ea5444c44004030380d6018190101d40242031405400c0700042c41c0d40542002c1f801a5484920150010100c00820005101200d0261011919440c2e04000074481d06d1441c8280c0301c4081103201220603482001c85211401100a660707a4407095200c4042608094440c11748000b81002580c1e03a5074601d4120707a14001d682c1c0c02410541c02101c14008814240c000c0d02c15111660f50381074140e0b03070307070304048859120801010b000742c0c00075000b00c0c039490049451181c1c81c0201504450a03400340003d0058286059444040100d29043c41130200610b80765 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 331456214 1250 331454964 331455013
    0x120307090b160b0c0309060f040213021b0114060108010611030412050f1e03070f140f030403170901050403120c080d020a0315030302032b0c08041104110d0b030c04020705 75
    0x500d00e05600d00b100d161669158048e29038a1407034031a1300010115542d10150040d01180383c24255104e000c0d060b0300c041800d03492544200c40d07509100c064a148040d040b1240d00c1400d0581d5a60000d9181040545440e20401c42c0100c95004c1000045449510880600a030700d100740002c1410b0f07033003002c0031410f00c4414090803074000b014014103540e01c1c00c00029a280e254120b0880c1070007420320f20780441c5168010301c00c200303d405030710500e41d1629408000f40040f41e0040700204141084400055600e21444841c80d0200d00140002d2010644d4001100e035090f0341402c0c4071500e40c1507615103400580001000400c0320340c00080043c1400d07803600440211440500c480000c0303d0447c5ea0294482c0100c0c8901c0800002c2880c140341d04903520710003e2070f0b01e41d50344c2c01002080c0d030301400180748000c04c4030159407204c1030064030003041c10507109580f140307030711b44025900380707030805e41224042d1000d00c074243d13450b2180307405042c0c0c1659a807000700311891055000b4145c1250100d82900e8400404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 331457464 1250 331456214 331456231
    0x1507050a030c151b201203160822060b040504140120090f0102190b0403080711121e041d0f09060f0c040312110601090905120307090b160b 61
    0x503802100c0d60080c41038004091503400e20b101c4422078404006101200320031661702da0712131840c40c501984606001540155442e00081e641c2c05092401030703e45e0760050782c400c54000c40c0030101b81400e50f01c8407040d4010504c01c1e080480c9502e040d40000b000e44d01d09032010f545910b990076031020120001d01c2001031903a4401002284c0020301d62800d101401034041107802000030104854442e0300c20700c488690528195203a9580c2d250b0360400f950a0082101c00b1030114000d100440c004a002c0d074295624a4802d2009044407500384424810b2500541051102c83c0e21210036028480800c3e009840503000903d103048940e034840e1000040d00d030b400f509a507000c401510038003001d030001090a9503c020301421542c2039894a44544100f442113510107010040710114025802ea44480142c611045800c11038202c1e0b41c0310300c0610121800b2000c0140582e02c41d60740c1e140c0750301d8400c01665024103507080c101c4200e6520041c54403039030312014a42200c40005842c1d00104807034000d0170340e00032904 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 331458714 1250 331457464 331457471
    0x633060d0e012705100b030a05070303020a060b04050f18010608190209010902090604091a041103100806010b1b01061208041d04120e150a0c020a08060709051507050a030c15 76
    0x1284c032842d0310b4210a42032140000e0712000c10508a4804103c0344400d20b47c000101c031360a6035641002501d40503084070407108141002d10040040c0b1741400f400380504c40e00448400180c075118400601c10740204c0115059540f00c0c4400a524482484180d48841d6042092405c0003440d1040100c4040160070411401d40306202461598540100380da0607240c0001c00003035a440d40070380c0c0c00280300b040300d0511340c02030070b100c00102c0c00480f11003e54050400c44801544040d155102a51503640074000c010f151001404030021189881107440c0c003100159000180544e11800c1d07084141d02801010360b001c02c03000804000f481030300c00b00c400c802c100d451958049402c0035a100c07000914802c1070003082082c901c0b903633240c5035211540c48a02481c40d10903582d0f03e1710301031170280c20b003110342d08141d21074982d406000480c0700000c504c46201c0c01140c3d0354580e1050a01040002d800060b00590ba11982c0c20310004002070010420854014003940340d00621117010300d403845c1000791401015985e2401d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 331459964 1250 331458714 331458791
    0x501080309060a090f03030536131503030201060303020d05030103020114031e01080606030118050c10110615100203160611090901170633060d0e01 65
    0x120540c1c024810071070304541c2d5041400802c0720000501d0b0044c1c2c80280d82c200000041542010003044d900703176251100002c4d616400c4002c200e040d0100b02e49000c500a01280000b5854640c0c510f00e410800d4020000d8500300c650585502e4200f140c008074003507952034200384241a01006480448540b41c50460301d950b05560009240400a0a00340400d080120110710314064105440418103525a104152981c0d900c05850b500c4000303441644c040d52070004010380c4003402c1084513503a075800c0401000c1c0f400800080c032501c0034021144008000320b003c402006040c0500c02c00b030181f030107400c1c060101c1210108219207802001c0d42c4400750743c820850554041c0240d1107804c4025040200011030481400001500f40700d44083c0c1607005208200218441403520324081c000381c00b180456840d5520386525810301100840b5082290328410070200005c0c0c0300300380c0001d000102404060505040118003010303540030421804207a5107480c02482c240c6180d082d4002c1c603d4410b4004040364a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 331461214 1250 331459964 331459979
    0x90f030e0a151805040905070612061a0732011d063c010f05010e0a0311041b0e0f0423040f0f030909060e0f010b070c03020a0b1308010501 61
    0x80710039807202e00f0702105565214400004802c0c0c074004000160040c8080007492800f26101c49050107200d0101d40e0300740d807020440040c0d104080549503505144840c4491490451080760070841080f905124820880720401a81800740840e81138401c3c40305110314000610030f402d440028595014800941c5000600d00b0b0000a9941d040760f16085500301600b005c0c01e80e038096242138805c13040c8103320100070100c0041e030300309164100c4210520f06d000441d203441c01150b030a40b00039126a4441c1c1b40398824400304400f40001000c64800901c00129000c0219045006aa0fa14001004166140b4002684e810030740b0030036000300305c102c03420451402e040061402c4800c21100c61000304250310000360402c0402c00c1c000c42d034560048090b103881116890014061280c43c01000340f0b050404100040e1006000d16590051520400542050b0b0038540e0404050b00040d00c01e0f01c0d640b42d5414004056140c26a000000c0d01502d0611a514000241e18460861f1250b20003582607160030010003444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 331462464 1250 331461214 331461239
    0x180f05041104050a0b030d02100e01020903120a0c062d110a0f02070509180d0c0503120a021201060e041103010515130902040e180303060901090b13090f030e0a 70
    0x81e080b10006096113828103801c00410071480b4094151060290400440c2e400007414aa103440d0041c00307011a40c0d4001c111030a03406140e000603019804a0040f01d24000c5010203003104000c289841c40c1c071000252140c2e0150b030038200f104180d00800039260f15900b48200d0028802c078072644030034401c2d1140140d10000c40d00c12611440c04124a20740b401480c00d2080c00500c00510000302021060300700015006403070313041c01c2286075441c070844240040d13040c001c90400306001e401102850414940402a100f5444024506955142e0800c8030312020203080410341c0c01381c2026928120000781c4141800211003104c06450954242400104416601d8038240009441d401d0301e52034507100b0414458408031081e0b0130440b0018004540400c154112603e40c92099031100758005040a54009040e101c0c401510303110341103140100144844d85440c0c201101c602c01c090400305a00c1c10a8103103900b1107100c00d104640300c0343c2d10b01b84c0000b496031040c81e28940305011076400c8030261906007804400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 331463714 1250 331462464 331462493
    0x60605040b33070b0a051f030b01060503270d02122b0e0a03030b011b081b0705040e030301030b09060c070f020a0e04080912060601020a061d07180f0504 67
    0x8090154146aa0b140003400343c030030700b5501020064283c10181905409080b080761400c1001250f180d4000390004e160070b2040c1104d40110010105900303001003100d0a07030004160a4411031a580080e200000380c40782e01d00e080c3c49000150401e184000d00c0242050b40b140c01c0111108418040c0141c000245041c2254200c500f107203464200c14013154040c00381c100c00801c02c0c10b034095100e503070090503015004580060400d0381d034655403110309041030056506420b4041c24107802449221100d00e86180c060b01910182004c60304510b41e105c1c00541910208500d001311504040300400030090307421200394214603132070040c00983c40d0000382c1d03828034000c1580160070300340814522000c0d2b440f0f0000300e80c0980074400c140307295890316041c0001d5590211081d44c2c00781e01d111101d0a000341000c07541c140203500590181101040c0783d12a400a04299404542d00078843c0d1000307003a0071000c22801c0010174082030001c00c600214402c440c200c803010780032030785018144410031000075100283d8020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 331464964 1250 331463714 331463779
    0x10b0304051c022802120d03050105061306030b130c020714120a08073206070c0203070b07020a0e1303020f030f0406050f12040303021b0109021011030c0109060605040b 74
    0x1480c2e0b000281c1814418203a813010750084070340740c0b41d0b01e6420300208846100c180503440078400ca0340d8503c00c0c00030510680c1c4c0c400c0c85201200c44207012540c86500321008860000341008842003805511f01e0480d00d00e600d00c0c0700503034080f95041000080d10030303540a91200440b200b00d4070b4400401d44544440f0522802000550006500810043e075041c1c0029585004000c2c4c803800c4004414407400142e81321142c050a10841c0c0000b00101e1283c04252031055001d0b01501a103031805014421a4100f0f023022a4030501024005c9a0b4040000101d4440c00210741004480c0760340d420064202010000000919002000031902c440480e408031030448c2e0123840c2842c0c0d1075001e0780402e2018012004103903089410003041c8000d040c0d241d0060128014860720300b180903103010b0704890880300c00000003504558012981c0050318065401c05004080d4801660702c0e041c290f68282d821074442001c21036403d83d4459040c840d07400c2900c1000b00415064903140b41c101d030801b50243c80d5174592440f104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 331466214 1250 331464964 331465003
    0xc0a260115020307120f030524090601050d140414061b0a090509101403070f0306050618010303111c1b03140a09090c090b0f070218010b0304051c02 65
    0x1c4641c1d10800c12201c1c5541c00440070201c80f030302d00c50300500c4004000c3c00800001d0420b40440d480da90f040c103002012020440c0420501c9102c2414425440d0004040506000d82806900300d07000b200c0c00b5080d0f0702d2500044000c40c130f107444e2904100040070b80c00483d03001e41c8004108600d01d03c46140e8417581c0034982035495298200200101c070424100e81129400035000c8041c4013080c50039030320210603241e2840c0c601068082c404241a590000d0780b0901b100150000020000714010b03030f101d00d0700a10082c110000360650703a5840c401c454420b034812400076408444006049000b40b10108004020b505201016104110014a40e1504c2c0ea4104541c00600c6600c80416008503d1403000d04049848151115040c204c041d00c9401c4500c2000506030034001080700301ea03c10444c010540760004c1003141440e4841280c014640c1000004a800c0070540c404088040304414040d80208404000e040d0b89182514010303043c414502c0c1035001c806400201c1c014020380205207504040d0b000540320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 331467464 1250 331466214 331466249
    0x50606070611091509030d0f120b0d0b01030b070201050a06030c0b0901090906090e0f0102070804030b0c0405090a09050f0c0609010f14030130021c1a0c0a2601 70
    0x50303103e200780001035511480c00e0081d1040315030000c02030000b5035022400e0310f050b28403070101a244a140056140d0000d40c89018506010580c0e03440380404c008013802c544880c080c150303107044222800303800c1940e0303901e0240200842d659090160a42c0804128018001c85245039a01d20b6402c40c640500d1b1500307200825507942c60b074800c1145900038010a41c080c17000a0b51101035500a06806e80e460046000e80c00c022030b00004140212003c1603804001107107441c2c42d6440e0745696040c00791109003017080030400007945540b2028914091040d0f85400240f1450916140b4070b091000701007203d41c0d401c14490560156a404140d410086003801d00d1009140150340441d42544d2075400c3e5001800c1c04400070072040288034400c035401c0c1c90f8848400200c400c0100103200030410403c001e43c001c5909480c0b251401c03124110125140c800c1c50074444081c49605003000141c000c440c4498030441c041012011203600c000e000d110898218070b0a900c5054039154001c0b9903105015079641c2080d25900ca = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 331468714 1250 331467464 331467491
    0x9230307020105032d1005060301081c0203070c08070905011202010e041d19120504080703030e0105040918051b030c0427050d030506100c060b060f0403061d010506060706 75
    0x179190b80c502e00c0c3c914000101c24900e94250381c000d0030780d160103d08005102c04504c038206101224140c0e020f042c001c02c0864594008018074104d500015021800140b0016001403030501e0301d0780242c040c0300c000d0300050b82821015000c54005034480900010303c0784585c0b01503600300f03101c012441d000b07a90200c1c0c50405142401c070200c2121422520521030400c4501c42c64035076014600c01184140c0390120b8040c00c00104031030b9401030340a885d0ba00e03004001c0c2040003074050091507214074018144607081075901e02c07000c01159841031580301c0411080171804204072080c810748200703a5440100610f40c1c80309802181d6500380c8000b03640c2c00382d917890308100344030705c1981d010205840c4103041141004206262958a038164401c20501080c1040d020450070718009000250340d0407140c1d0303030a01c03100058517048090031140040c942c1202082008111400e410001007000d5401444041801c0c52a169491021542d0083e204070a03407418060001c2036a0300d0046170b800d40d070001408a00014440c03803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 331469964 1250 331468714 331468741
    0x120c040b0c0102090405090601080616020a06290103020a090611070b0c0a151407050328061e050a030b0403050c0a230c01080117010f0f0923030702010503 68
    0x8608015000700e0404041c51054009000640c07043d81d0030712180e2500304000350703501c1c2d00b800361072070305c0c0c000c900041c00b643d00c018162041d1000c144100c1e03400b1b140d561a540c0481d580851b208441920a1900d4404100800140d0190358002c0ca0b04521344555810000c0c6444094060300d002c001c00400c0c0ca0101e00010041100606019041240e0351805040e990b5a500d101000440380940c00303481102d01e1043c1c41c8038040d5040d0201c00c0035129a5201d000890751940000c02000035413010400c0e01036842641c1c40703905d20362219480c00041c0c180c2403015542054800c5803141484100111040c400e07603c0380000d1000b00c0381c1c40010021242c031a450195400d01485401074800d00c981c0040c1024044d01031203045050085806005c800c1d42c99400e859240d41c41100302501007208840104000405002c0d110502c465010002070716608404228042c0d078112052100303203c0e00d5503580c5090020402c880d0440403030881040c202d0035a2080da4680b00c0c05442c0c00607051040100c00100108182e04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 331471214 1250 331469964 331469969
    0x9180606122803090905040206030106050901031d0304050312130303180b03100e01090912110111071505010506130504150e100305010606020307080904180203071508100605120c04 79
    0x80810801d5103a14886503003884110b903060700010702d400340000d0344071014480d041c05980c001d8003d83c0b5513030a1a00684099114806484c10582d54911300c004150305403480e050306084900256035124a0a0201841c240c0404542c101c844020451a003100c4210b1044100f2290305041c42e00104004603400004614a40d2012103034440010030803900c40c2d288844103059901600d02c400c2d05980b940140c030111440703044010041d200311800c140380d46004807400d912080e103000002c18030540240c0307010b00303c0d040114210707078091040015070002021401218054641a0783d041d041c103406c0c04110058036164480c40d4040d0f075445e401a0090b85100e1003800291511003501c90050910400e10450b0a0f018802502c0a528064001c101c0c3e41c4040304591400b0340181c0002d0428820504110041111500c020f00d41d500407441c180040c0c9041c82040018141c4104140c44100070031000f03000d40d81c0003031401403017800e2070a0034001d00303400138103880554214149038403640e560481007018510858 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 331472464 1250 331471214 331471243
    0xa02040b0a08222013021602040c0e01080c07050313080c0f0301150504020903100c0804050c090c04030b150a080a15050f19090803010f050918060612 66
    0x41e405204a800402c00390007000032074085442d4006010101665020041d0000c140c204503c4da004012410085907031312413100203042c92040980c100031441241d02100c0c1090b554292000000150f107001d204c0c400c030705012070905041c0c40000c0350000f00030040040130000c82e84002705609090080400075105c500800f00d01d941d0100307490703440782585d62494500708c0d071290043c9064803a140c1810300a01640c0e10b220780d0500074040c209000c12000e908400c050302d426104114400a194841d4060780c040500c1e03e46a0601c5414913050032070600750940c90260181a80100f44143c0b16038020450342181e4110100702c655885502001d0054015418055400004071a0214154002041c40c049241c864400760401034441811203054800440d00041c00c105072000091344501b0302203400e62500c000030ba0000e080c0c0200d030748010f0b242c1c00c281c1180c03c5100100d44203001a081103100141c0089404154412580a116142d40c0d9844000d014900030003040e8000c42c20794004120000258450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 331473714 1250 331472464 331472467
    0x6030b010e06041a0310020a02030c0a2109080a0f060902091f0806160c02010215102303071e0803070812071b0f0804270e01020a020705090a02040b 65
    0x445a507072004110a8075400c0c456441d0244250b84902104c2d210f000c0c501015002e400c030b0180c80c0c4c19001c002d42184290303800794082040300b194040400d00142c15164401d00034151200c0c500d07a6002d40d50400b9502103000d02c030200c102408900d0300015030500240d0301c082c01c403406003002c4c43d000d0b003e04035030b0328004c0d0440c0054003031040800300d910481a0301e00c000781e01c1030000759444100300d540d21000d95050080004554170520340c40c0c03140c4030b6056490f0041c011104c100c6d0501112140c00501260803030451501d8420501c8540e140340282c2020440500b0100182d1420400003a101e4000348200505070100d40309006045600c0c0402c00010b08420007074946070301d428103041d90143e01081d429000c00090000140001e40108102001d12102c41d00103000042d042c0d60301c007100c0202c042c0640d800740e01404009041d28000c429003084054144200c0002e041c0b42c0608400d403000220340305501e034010b020649085600007000411110116030648282e00c550401c180240b0a82d0411000c2540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 331474820 1106 331473714 331473719
    0x70f020a0f06020f0c070306060e07090308090d0201021f0b090c0301060c0b0a0207080c100c032007140105010e0f060d1523090d09080d020d08090106030b01 69
    0x2004079641d407605502217082480c000d40381d4002c950f00c544401060280340104015503802c6001424003040301e608640d648400d90050b4003100c0d0003102c1164404040d684200310300462590404442494500040d034100b001c1c004c10342156004441c00c10100300c0c6440a50200c87c108d031b0b90b5641c1e0102424a56440c551030000282480c40c00c50f03028030a81001c1502800248900d07915100100400100c425941c8152000d4a20030000e00d0b203400315100c11942c1e801c004003170240d07002c225980e50300345500c2e00c880d004084451901140d071824002042c0d5419944001d0300428168210f510141c3e201d004005803903160f0400208028800d02c040100d0380855000255800070742c40030004a0310241a500315039800c12035000c030041d0702c82c00d680c05480c1d410040a00c007901c00038001d0100380c5095030b4040e6a4203c0006400d0801c000c102c0003448207002135004401443c5d100f558000c040d40d = true := by decide +kernel

theorem cover : BRFrame.Cov 331294964 331474820 := by
  have h0 := BRFrame.cov_init 331294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 331294964 ≤ n) (h2 : n < 331474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
