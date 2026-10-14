-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2275
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:13.670186+00:00
-- url     : https://prove2.me/submissions/0eae432c-57d8-46d9-b7d1-702a9b2dae2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 408992805 ≤ n < 409172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 408994055 1250 408992805 408992839
    0xd2f13030204050c191e020304081005060d05100b0306150306041101111209030c0907050a0e0402070b0109020901030510080d120605040207080a02010608070501080a090317090f0c 79
    0x6905880080e1045468802050102404034100d905800070f00c0548408038103000300146c03040d10704424601e03601c42000340d4019620701c04410f440c00d443c1a00041c20781c1002d07480240c0302605011b02015840309079101102c001400c00c00007420355001041d00403401313203003a408150800c031005000d0b0811000810040c1620769010910036802035005030821640d100000040301c4080f060713515810b030ba101d42c8201c05019030400700509084001201141c45440d100414040700100548401011440920054001c5405074489409501000c1c00040c24014181c546040044003070b8420384180ea40001d6550255900d8001c0c5a800b2018032890070020740341820b065038038500c1c17040c5002000010100b61201030496000751009000040c001d640700e130194104800755902891540c801766107898400540c1c0d450100d51903007140d8050f11580781b596100000c2001400d84035408804000e407644201450300c402007031090080e03810b0f200a10610601846e01890b006013100701c2c51142c800490380020032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 408995305 1250 408994055 408994087
    0x80c251209120308090c032409030c191103240f0705160201030612030f091d011203030b04050c0d11040509061c080403030216060f0909110d2f 63
    0x143c0c2c2c54505a08580c1d80d0f40042c500705040c4980080d0316000d50075550740c040d01c4001c1c2c0c810021100110002c050380304d0f501c3c03403581c80c4680f140c80c3e404e84c1c1201c0ba10f07041184016030060f42d010701644c00504110205000a400d0890300c205600c039202c400c202e110102407a908840381c0c485d1344440707840d51500f049030000c2c02d5401512000c000400c00d000c1d5500859120303130007040003029015440e052030310052a01401c03219141c9000e200140f07810b1000160260034104442c1078030502e078102c0e03e485c0d0034241d9140170224000c101b40c1c20f2545070381c94505942c64620031a80310705218444151503406008540c000c0e100c800c013804003024402e010901190b960301213040c0d000481250114915100704a54810600a00360058403420010400009158011501c0d42030b003501c0b0781841d0101d649865042d516600a40b00d07550010b44201d0080c800500349502030381c1401255841c4a00702400d20008100350b45032403080c100740d4541a15a44044054400140082c407a803a0585d0704001a8601003506 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 408996555 1250 408995305 408995339
    0xb1801090521090d080c010c020604031b0602190905010e0406030203120c0705060408060a05070305190e0709020409140906010b071101051603031a12030703080c251209 74
    0x100c0e6203803590100a000d12202154000ca2002e8544020703030b1200e050541d00c507041070074030209a502380400c10421520100c1c12503c944c2e07050710f07071134507180c21000c44142802101d0f0049a500307500b0090307003022000241403900948826a43c51025601700340004090103a8292207074051805e0000034401039502180c10800d9000304428140c6550700403090390302e001a84d9020541280001801180d400c10110712540301d803890400510658807200000c078100e400440e446c10312070009900790805440503401610101307200c00c048514950315046448100e03845580407a080342da0701e4428480324480d040380319034030035403d80203407881e90724140e045000d0344240100140b202c15100c01d8160160b00072030a651500c1d01d2007034030034041e000600d00034001301021303042c90320310712403041d07002c002d80c504902c03204071800802c0040d504214166505481801c009003a82d65680c2003413207170b10329146004145903211010700c80b5081d028405803d20100b20b00300c42c1c6015040040300d41080c00501c4a03200b1240b2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 408997805 1250 408996555 408996583
    0xb04030e0103051014130603030c11090c03040807150c051c1506120f090c03051b010e010f02010605060d020403260f0702061219140f070f1202070b18010905 69
    0x21013908a0002031112600300c0d1a4006c01d44c076102012052603030003805e003019603100e200ca100c0300c8040b4408000088078211500c4d2417400e402c000080000d800800540f1b07101d403158141c440d07c42d0b410340b072080a8034030314044e4000184000c1214000700f0080c00003d40711401ca000100b0000780326a07260050110344d40180d00c20305c031290390110302004241c0c2c05895154580c0808011188940c5050035481000d4032003075445218224154400400d950301407010044142c6418280c0400c030f5005489030310342d03030340088150b56031241d0000d11a15000b009099980d003c2c3c800503501c504520380869030000200032018071818000a48601d407400204580001d21207103079081c3c81d4919440003810b980300d411030601100303e454052100415012054441c00814100c061185003441c00d40e07003401c210b049038040c00400990b004110207a00070460b10030800114a00141040c0d00000018203981c003002e130840d04282507400b0040250021110b0719480455203000b40000750703064880d103a8880015985038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 408999055 1250 408997805 408997829
    0x906060f0105040e06011b05100903140307020a1b0e04060518060c07150b06070f02010f03180b060a15050c0705060703020a060b0f0301090803010f141005070215070b04030e01030510 80
    0x100411f4040c074070058455501c5011180e2556020480388094038440e90120042140e1000c8044c0d40019541900d100307454036401440d8200183c1c4403001d00061a00080300b03200305215000c01e04402c24184280700e24081d80000c580c50402114544440031065000b10458020106025410700c01d9000c81380c142d86c11007170701110303c410b000c0030100604e00c903482164022000100c410411200c1e40d0941c00132030003600c80e042110b19010055082c0d54044141400040054403044001a246480d440c1c2256000d0012100682c80d030154601001d00c6c0006007002c20310209140c0942042040100c3c003a1000703890403402c00308c1d150340280d52404007410091401c2d0726801000d100c0e880300c0311401c20801c0002c00902800c41642002c101c20750082c003440c10041d410040204c5c1642c00050440c1d18080044e18001050fa0346031812100742c1c2200704200ea11071804440805285003030b0003d03101d0f41c0e0003841c2e454014100b9180140628582650301c505143c1003104000041c1d007140103250031189951491 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 409000305 1250 408999055 408999077
    0x1b0f0304121b060f1805032a0a0618090209090a0221190609091e0602040302060d020a030e0105070f0c030509040c051b01092001050c060906060f0105040e0601 70
    0x70b00b910201c0100811040011107400180e01075011071800c030f0407020380d111158003200c07840c0c101c12520b040c0d0055076015803164000e01d041c0300044101080307000703152802141d11307005800044c2040c04654003580000b070041c500c01500703400b030103034490042c840408114a4040e543e80814005070005200e00103a9074003041a141ca5803410100d40ca80ca41d0352800401c107881c186840601d04040c200b402541145007400204112166100c2c61034255000b01d040c0e10304030030130138080e01002c43c101d508035a025000c0c88000016114203010b4248099074400158980380100740c01400ca4403a5014080181e043c40d0500031140d800000d255030b014110301e411503140c0e0301d6080903947c500c501404190070601e4200441c0e0b003d60300a004c4c2450070410034100800f400c0060300c40342a203d000320040c180500b120240c0b000314015044100182106041c101d043c003040003051800c0840444007000a500726100300031803032030706801e24208110242032190409082510150810300c0c000d02c1181400000885 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 409001555 1250 409000305 409000313
    0x3030804240e03130621021b1902011101050709140402041206020706110f120a1b020a0308060414010b09030a050d020109050c0a23060405030d051b0f030412 69
    0x212410030404010107200c0700b00000a120358a030b0100040c4031400900c008045495449106d88080e4004000090018006203414420013513000382e140541560340e8400001c00308c4410302280813558498580000c0b031124900016054203201c40c2e031000d00340d140c042001001504502c40d00c041d900e20025980d1685031080100d0028401c0c0d8001007401c5c80c09010a00400145400400b0010b00c54182401480048107062019000f8850744442c040020300413070030a0812100d54a51141c0500c03004648040d6090300d00f21800607000030307030006800c07601c1c1d05000d16403c503031880d030804004d81e0200700c4e0400400307d494942c1d0041c000c1c24068940040c40401550f0300b0060500602d8001c1c00b0f0780c0b07880000c42d0029008140f00c0307500711820f002d43d422082e5940b4180c140d0b642107034641c6904601d0303c036917010420403100003c441c07540e0105041c0004280394404102e2001408029101ccd0790f921512802c0c20200404035070304000740ba52048a040e4030046020007070700c00301c0d0380d600d00e00b4030164146e1030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 409002805 1250 409001555 409001603
    0x50a1101020d0f050907090b03100b010905060313060c09080a1502040308030f0a0c0503040804030615030503130f0b04030f12051908070f0206040519030c060509010c1202030103030804 81
    0x52481c80c2d10341025040340f202000c41d030103580220003100844818550304c511030303000c0c0c2e40c19500c883c0d4150046400c645100c48590840b801c0000140340100e483da84500c0003c41030b820030346003010a5098400100c0c10440303244545a200d5040f800d000440e907280980d250350f9118640c0d00182550b1010266032505400b540649018650001025032240340020803030176801c4d02180e00340301e16400e02003060225070040040f24043c035001241c0c18035050940e100c0d90003802c410581700d58280001900080070030b1092000e03001f0724001c81491944c0c030b03291400d072500d482c4c5650400d00e141c81040000b04009240c01d101400030943c81b4100c0d07115000c0106042e2840c0c0690741104200c419940d040342d1207913a0004089120b08001c6d00c4003040a0740d07180f400c81c2c3c0e0341012079008105034001c01e1503080c02c0b0ba4006403040d01714803e240040700c800d010380d0780c01c0c00c3d600141e510016582d16514100c0c0d0198000c1044441d0344414201182190302d180c400510000020f0000b50140f00c604c41c1018062040c0e50f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 409004055 1250 409002805 409002817
    0x10020c03060711060a050f04020603092b02010b2e1e02071a03152107080f211207030902090f010905090102070203060a0b0427031d01050a110102 64
    0x103056618034504402d014102040c00c002c821001e0003608005a041c0c07400d0f00c01c003070203024800d4036001256603a50a1080c50307070010f0b00906182c402c03800f10042e850307110b601d040380910110040515070b130401d0002a00f9030300c0060a032481400d1100b400c1404078200e100c41d004003000600b540b100c009401106035920b010040300c00801701440141c04070300c1034002500701c04880504c03200402043c4500c000d508980425501040769075a001008a0769150141c28a802c0c44860600340c162001d036181001e1500e281a8407880c07194022100110480c18240060580706003680320340c6010700031400301c40c140c6100700100044003004210214500502c29131040c44c401d54058103125041c202011045000d000074410f1085144c1000d000410505040c0207032510681e01800400716616600324400150031035081d5250425503e0202c40c000030820a03103100c1c8003400900f01d82c1d41c2d030781d00d04000308411410441d8106105070400d80ca11280d07400400c50708040306500d85141078413044640d10340a03101d02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 409005305 1250 409004055 409004059
    0x1f050403031d010204362004091401050301020f0a08070207030b01060e031605060901050d0902041811030318060c1e03090102071706041e150207060f050108070510020c 74
    0xb595209680760415402803040c2e032001081018921489603000f40240350a420413000700001c0aa004802c500a810000146202244c0030030f0b500c003914182001f98229901c190700f040c2d150100c0c503031813050b0030b41114050710341a0b0081d031401c17404810303c01d82842022860702c104061300e0700007641c0300c0c82401505c026540c07042d6006c0741c42d6941c03039000389001207800b0a02d11a000300c2d05284401c010100c2500101c502c050202030800744598015120303a000b01207031441858a548090005a89911070312081c00018003500100142ca82000100d1991203848d0320701a41c01001488180200e00c8101c21605008542d1669211801010181420a103800c80c07070007608010700704051590f01001a0801c00401c0e17080362400e41e80e45080700151100c0262440c21500540085000709000c0460b03040e1004861139110040b80c010f80d030302603e4441030f4040d001240c0c1d01060300760800c11240070320000d50488403424081941000942502d40300180315007031050f401091402c092a00070300c4a82010100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 409006555 1250 409005305 409005341
    0x32404050a0944040b0c030403120309080d09061503060c0e0603010f06030b01050408060703050613090201080f070909090f140706050d0207020a0504020a090905091f05040303 77
    0x44090764501500c084070b41203d8840d0395503070700407030a080340458001844014040e00c41c445080c2080c1d00c0d0500745041c8032140300600308408694905032900801501c03403500000d6a4607482c40c1800c11080341000714140030581040c009201003890b26044c1c64520001100004070040d151030850700600319583c00c4080350160003000000c0c0030007940280d030a90060703160140340302e012000700422031009008107c2107002d21081072100310f101e83d0000280c02e0040c1030503071030030351107800300c614000d01211120002030300c40c410007200341080c640c00440011010804e00c9459030981c00070341440b00040140056403c405d0009484920032081c80d0001c10f0901001c10100c8070364205482540213009088c0c81d00b69000e4210350942000140a504854099450750700b0b102c41800200041e5000007003d81c0c0c00100e4500100b20356580381b004281441035600c0e4902030230315100c1041c098610082507000c10350040d0700c0b8088d90171600d481a0040d00140d180004481d540c40c40d050780106010b240e50700007480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 409007805 1250 409006555 409006561
    0x3020327070503060a0c0c110d02060309071503020f1207140d02090306070906090e100e01060201050702010c03021c09050708030f0c06090c010c14010e011b170c03240405 75
    0x801240301c405030b440a40a40385180e0321040c101d0191303030254035208002180b610040000c134550749005089400001c000d2081e01616400080003900b098031503e44a41001d1410800020300c052070380c4980340070f8103003581031000400700b901c107502910302c00311480449440001c6001e40714448580013590002001394590280401c070800075082021010302a11070000451a4140144904800c403001643d641401d03605180d11b45910700b41c00b420004ca060000400441c0107020691803602178209a8000a050b00d807410009003500c0c070030b0400c003040c14410400c041007011b03260024482c2e0701400d540855801f00038500300d8600900d5601120f0140004550b100d04140080028070704000b584089a03c9038441030159030711000700c00c0200c0c0c00300d150751002a000400e405816000c00704004000a4943ca4030340b081070940d00c3d400b1910107410042c1041640703070354010b9901c9010107201462601c2c23a182a03440920b05200103000f030b4841c01160462116408401a80c6544000025001b448541 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 409009055 1250 409007805 409007881
    0xd050409052a0c011113050d050114310c090e030412050105040b1014010e0619092904050f0619120f142a030c0703020610031101030203 60
    0x80c0105011181c25400d11004172000c04902e001e0354502d10150451590543c5410200143c414aa0070103e4113552108901a81d00c000e550805100e1034400c0d01c500c1002c44040c4042e03007405c0042d600e00c1800c05054030020b010500342a20325040e50b825100c0014903c940904003495402640c0c40403141015040c0c07400108803041d00214015032017141000350540341c1c0030600c0104003039801001c0380a502e20084010300d40c400c00000e10700d920023601d200d2421030112030b401c1c61119142e4a00f8045261007504014049d8407120980c402c0030907190203440e17460100d41c40e004a02c80d91007020300c9524440084020f964680007240c12001002c03d0906c0f50500c00c0401400d0182c0080c6071429082c9000039482254005000d0080300c030442c60a031b1041c941d10100500e601a40c2010701c403125000d012150308100005034000c5006041e456155610ba04540c5002440c05200400c803064469604008100241d01d8035840b026050090801584903500c1680d40c4190143c0344c1e0100660004595581c488a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 409010305 1250 409009055 409009057
    0x9080109050309040e2a0d021003051501031a0f01300b011e180902040b07060e0c0303271f080906130b1815010e01080d050409052a 58
    0x9000d8030f0600c030905a96010351b8940d00040c03a40100710190f08140301c80e115020900700305901000700150150060741d0003040080320382000c2c0d0404203948200b84064403050100d4107007850070902c0e0520050ae030351035250130610000d050aa0003000d28028050305030380241101d02c0540c0c4084061b6440d440c8508900a140d41a80810a1040d00d08510950f031544518039400748044e0380b032405030407580140fa04a44010b442e007909203c000720440d010484c9400c5000420003007010103c020f4407a07800b81080b00c200d6529a4180c40198000ca0401c00592000b0040e0740e8800c1c00d241c003108174401084486c50700b141407100b60a9020000c080c910945407100100a454002d0756603c0012950302d290504c0d40e5144150381340c1c10100700c8502c81c20005401c0200c1150b2084014031404600001c683d00b443c50b01c20809420040415180014403220409840c81401080202d00410000d000010040c129100c1c2d40180c6043c9600c41d00000c02a808408400f6030503c0458004030111903109072450407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 409011555 1250 409010305 409010317
    0x40e030d11070b07180905040305040b0304050a02131a06090f1314101d011a0904062105240f1e0a0219030b030d1b080f2a0616090801090503 62
    0x1850004440109102440c0d1049910849e4540c070b505290604084194520f6040208110307400c0c410303030840c180141c941404803c1c005000c0b00340420300000c00301114008482c50700c0504c0c0101001e02c00740c0c070240d40b42c8404084420b410340360ba01c3c00c0307065081c50340041d1804c2c14050000c044198103128045500b5410342040395801030002a00c03e20303070041c140710079a0a12a60502041008840d0305580d0007a008184010000b40300141c425951145032580746050440000b041c1c800300750710010b210082c03201d5017082d03060301d14008810102000c194811500680b80d6054000c5c07000c0069140612410303140805003510311040194600b840d0b0100c007a40c01071514421f010744141c0c4141c0e11500900414414040c01400361614a802c04001c451620680c00300700810514114400d0100d403000c0e00030400d01a900e21070310f5507031050003c1d100c207100640b15240101c6c1c041c00c4040408080202e20380c0c2e004140005144103a03000701808882c8850590459121946851600000c00c0800130003000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 409012805 1250 409011555 409011587
    0x2090a020a11011b082d06060c01050f150102060f15130e0a1e02010c0b07180609031205070b0f07230405031204081f0906020a03020a020c040e030d11070b07 69
    0x40668a403a1682109418488500f001c801e541084c205464500c520184e4003081c05231003241011520704c001402e45a055440d201030203250303000e110f5000c504803000d1400300750030300040ca003070f042c5440d03c0002510000c0c54047e40b01c00b14220b2141a5848601101516008540c00d0007580d085041c1140c48038645401160a5594904e11208a0600c464034084641d0140c603003404c0c41d8001c2d120f0840c2d440005041c0c8080001c48a00d90884100707450403030010b400c00c1d41d5401802802d40c81c0001c0260034101c4e0120600009000c050009408002e080f40c0c0466059000681c50b121303214103580b52440c02c50001c2070102601501c29030381074828054001c58404a084070000711105034400036034172890140d0085034014208001c10800141a0540414101d0700c0c0041c2c900c10359181c40c0100d0300000c8030b907400a40c001400ca01d69950400605580640881d01000741c2c080d503d1049a0320b2113968003600c4503903254002041640b03e010262808584c00010740400703843c02c481e000300035a01981640c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 409014055 1250 409012805 409012817
    0xd0305090d020c01030b0a03020d150606030605060d09170d1410240918020a081f09091e050d080f0705070308180708010b0102070b0702090a020a11011b 67
    0x24000400001d801038080e5815009041100d80d1080118040c0208602050300000301100000040e204c00d512054958020b01500c2040d600c07406400c001d44540b039100b50205800d0000512140c1d480741c08443c400251800c1c00185032001c1e1501600803110310300c8800c800c40011503682e00500983c1c04c100d14590360000400b81c26501c100321075055080a000f100416011040c200c100c90003288001268035107282000c41040340e41d07988003038042c040960f1000c2895000304103840b40d103402051898100b1720000c800700d110440b46118241c006584c2c814014044d440326506130600070140d1503031400c54001d81d900d4246221500b401ea03915080c0780c88840008810400246c40c0a100c055010b0183da6995625450901c003614100c0e100c0d14050070021542c05030340c00158a0744420440c100081a400d0000b080703804100d800641410701326440b80e40100390801c40c0700010380e50a590250f00103820b4a0050b106c0c40c001c90100c480d00041801103110f50f00c0c00489880c1d17004a0070b03608040c803582d642c80c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 409015305 1250 409014055 409014061
    0x140d020d0b01060e0418171c0204060e09090d02060703020f040801060f0e1303050306060a091203110106060905030a080a020c0d0f050601050d0b15011413080f01020403030207090c0504030f050d0305 87
    0x3005204032042d001d000042c2c5000d000054010404c01083d46901e0042c0e04231255100c030640c0c2c2e04981c440e903c500301185c07810383c980085003000080a90f014207c20007510381418100b00103912180001c154000309640003954000141200e42910040c2600c0e100030000e20341c4801150000015600801d5480100301d40000c423601800c1180c24941ca40c999107450468680c002841001e40000b05c0180a2285460703020802500c0c3c410100a902c4c02a520710500f4030a60103031508456103500310404100c1000c2060001d17031000942d01d800190700040e003d03681c016143c4200c2c18001e04880305940011019084024814002200200e00380200152522039030b980c420000900e400f110b0040107410b11740700140c4551030040d003d001c86803040c10700c886050b000d03401507645a4408960212096070054081c006d0321030400c0703001d030b203015800002c40c90301c0d0a540b00030350f80c0c0800c2d1254102d01d607100c0302c241e924144510145c400a40c1e100d5084000c24400746440d0b501e400504604400107454070b000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 409016555 1250 409015305 409015331
    0x170a0507140a1a040b03240102010204050319170f040303030b01081005040c18080a03030e030313120c05030f0d05100b0d0228030c0807020106140d020d0b01060e04 72
    0x1c010a208402040c0ea40c0282c81c200e50b600145a040d000d55103080814400010031000580003944200000800d4a5244c0c0001e00e54241650307841c2030841c11a1310601040c80140c400003207130006161300d54842000c0d040c1601d0016820310150341042a8030307502150640c0b41c40f0080c1e01401c26240329441c14032404644d2401110002012140d4440c107801002080049040a03840b07285070014a2500513280052000804080c8905501448156000d4042c08060560512a6010020701c1001441c50350034100d03e03a0500309070040d00500000da41000c060b10480c025030340f0b0480b003a844010750791580f4403080c3e01d58030343e0400c40703000d035410703040200040b00640d03e507000e58240c1c0e10221903581096091440d46001b0b400c4900104c00301c60152400c007100030071142400070b621070569030101e84410040d0f4010f1005802508100035607051600074014801c2d105000c903042201035035803881940340d0380000380b0889001400036200e5602c400000c1003040d17000e11110040381c825241849002e15005c1c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 409017805 1250 409016555 409016579
    0x3030e03100b030d0f0509040905031309020304080304110109080610140105120a180c0e04060c050c03030114060708033d05190305070617010e061c030306170a0507 72
    0x494243d26030020201400814001e420a602c02d4140c0c0c6419401c00b285000810111404a171080d11168030101c0c4903010703001c00ca031510740030704130000c004c0d41141000d58664101b8080540b008000c5042114140740591094540b5030040445008990032801c0090340d0000b001b20700d0040e0580d81c2c0320350740100802d50150b0112104581713a07206030b039420764851480b8801008000d20464250461a0682000c105804050400b802c4200180541c81c01c06141010485600949983c10701c6001e001c020380401d000300542c1e0444d180b42c3c410007801d002c08000038140340718a03540201410300120030711400c42c019820600c0002a41c10144200040076415441c411031550100845892111011700860a000706c420480e140c1d08800203000c50345030707902c15040c01c0e0a5002040011000d0001800d4000306803505401170071481320318034250411401007020040403200640c0308039001c001c00410507200354020b40c000d000c030030f88440c40714440d94105034940b000c030700040d20b541c82200008a101c940c200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 409019055 1250 409017805 409017821
    0x60510080705030406050402210601090501050102120a0e030a060e06061008311202031e13091d06010b0406030f050702150702070906152006060607020a0f03030e0310 73
    0x1481e0342d801c56880781e071504003404005104a0700100b14035118688008203004444801143c1800b6105542c14190f03403404580e03051b4403060440d4090107910a8400c0050121aa00b40c030601d41080e18032440da0202e0700c1c141c1c000c48010b02c220325200700312522080100f00b080c06018221080103040c4080792080b901031101381d50503907244884029114480301100c0344540404d80444500781150f4003615003014800003c140480036030800184d540303c5581a40380b48107445142ca91039801c1403040d00c28452104100e01442c81010741d4ac04110400d5a0081c403511510289102200c2040d80c454a0b50b50b01d82d0054442c0501080c140036442c0822030040c02498031a130342581c01440d07040c80c1440c2d82c070f400110151158065000c0c0c0304010440d42050300441018048072070341d200c965007850000401010b1810014032140b00f05480060380d0500128035580c020a00720343e00d03a151003080c00014481070300755003c40724000c4848070003c1019000004400381d40001c9054a014400703140b13144003034907191 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 409020305 1250 409019055 409019057
    0x201140105010504090b03190f03080c0c1005091c030c0201140c070609031e020106030c2c07140c0109020a1d0115030204090e0616090605070611130303030605100807 73
    0x4d200c1440600011ba0040300302440050072100030700300c03a2042c14072000d040c540c1914806a041039103010305401c00c0304a50001b41110391030346001e2540c01e200c0e464000c10303442040c03007503114400324512030000c002d4402d80480d80d0350707078060b845a50704015005248c100e01020155080c10f80c1100e1345400d40c0d1b0018402d030202501c3c2c40c9400704ca640c90f5802415404800c03070500003582600e19840520039200d0303042e8403035900002130f000c2c11810302245281c06540b041454035441e080b004a40c4c1511141848090050840280240c5a117202529a500c00d0030075652240c0010460200803c015000110024029641d0401c000d0b165190b20340c0650200c0d0f260501c402a12004002000a10f880074421048900d401400c107601d50903a0020754904a0820920343d101d030092150701900450000c101919605141c44d074286008000381440c02441030203001c00b5900c00c030600319044240b00b207174031a409240001c0501c0c2d0300c034900900105258001d40d0700031145020110b0109000f500725500074429 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 409021555 1250 409020305 409020307
    0xd0503041a1e06030f0709021e07060b1804050c040929010510020a081c060b0c0606010305090d2106080706050706060e06010801030209090a05010c0f020c0a0b09010c050304050a0308040602011401050105 89
    0x10007c60300c0103903010705914004800f0402d5a00c81c4812800b015200540c0310380d04c0030603036070328500401030711004074001c542c0124100b80c00c1c800003c800043d66108007400341c80c0030aa120076414024070200d000c1c8801c00391080100d1080f290481c01a2021741031ba40c04070b80f5124900f145d00300480e60b03410780110003000b45000f004054407a800a8114282c000c1d10030201042280d03c030442003d980c1c002c201e108081343e00442c2804865a01801040d50160516000b001000c1007840018510141000c500c145052000702002030303005160020005000d986007202c1c41d1554900c0001c000703134040c04040e50842e252500100307078031001581a60140c0c40503510104643d00b55001c004101c0409440007510380701e481c1180c80007890a0003000210b89041c1c444604803c072014000c0e00b8080d500b00203d202c0c80140c001031041080304805d03100c8070791083c42c10500e2000c1500e8202e107140314540005a20413800d132400020025044014801c0c1e90565000b413007400030120302d24540107001c1c060716000c104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 409022805 1250 409021555 409021559
    0xb160f080f0714030408062403120a030b0114030a0902040914060415151a0705060c18030a23030c070305160905060a03080f0904150e090d020d0503041a1e06030f07 72
    0x1e0f42c01603c0c04082d001000d0001c0c14134008c00007034680361120056042031240880d00421490705807140150b00d540c01e09040d001e0042141c070040151000401d0008415070310294141552a103030b00280200e0740c00701c040d4500712410040182d032100100c1e811141c90b0340d8401607010700b18080c0244800f00305144200c0d01e000d41011480341c410490401030740400b05d801c0c040c404c0400c10070003050780614441740b181d542d54010010a15907501041002c5806a400038170590005854814089148904005040c0d4403125101100781144290310107407045120310100403045c004041401300940b4028403900318425a20b0100030140d072000c480322640030034403210070004036002800815510035441c13044c601c1d120001c400030301100c00c14401098080010b183c1030181400788a80b5542051034000144008000e00400a5461458400440403c500440803c0810440111884c103d10005548040a103005041541e403110329141c4000218102000714442d82030100365003486807014000b8292440c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 409024055 1250 409022805 409022821
    0x702042309120a140919090605040618021602030618010b0f090403111c05040305010606050403240204050604081006060e0d140c0d030c0506090303010b160f080f071403040806 77
    0x84501a01c00c0c03008030301080b07031700c00581d82d07817003d0781c00410b40c040c1240c081e0341031018440444085801160081d8907051081c05645850350254084111254016960700070440038508880f903d003400a40500c5501e091110304e03100440440300c0315020a00820061000c1001c2102c4a03201509454001c8080c10201e4040381c0b0401450400003442822141075107080320840010111002140c00051000f060500400c00d082c0162801400715180ca61f0410b829502c82188600e013044101a0801c1c401c40b00c03041c071140c0c1d03405540c02418001d141e1511981e69000c01901d800f407810181e010700e4074241011800901400204020040203081c495045005039a47da610100995882020703105007192418650b03127030f0b007400010521a40ea914403000700c5161071440c1c0b01c000b5142d282d0541043c4018055800140305990f052094003100074001602030a180b00611440c4d000a40108030000c0d440c1c1c0d800c4410f90040418a20400418450040000c1c405469005500a90490b90041008140d0203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 409025305 1250 409024055 409024067
    0x130b241c0b090f0711100c090b0a0503061c0f112106010510020a050106120b24010e01180e060a050102010212060d14100c08060f030705040c050702042309120a 70
    0x21001e41e041089000f41603220040c51b080c0b01d00c280c0114180c5500303000150039404103c4800800a512201d418442c100d00040d005010013000180580341c020740c012001c900204020704004d81081007100229060705000001c03580302030300103000380f000d89845000c070592a90158059614400544101d900f420308204541003100b441c0d0f030440c480c2d135041001150080c403035100108014844500c105180d0315040b145850014010001c00c13440034055503200c0c0301071600c0100840700b4a00f8003011071080d80103039012000b14460740000c1941c0c00d00800d5070031070001e40c0d40c000c1c0001c0725070383c0c01030b641c4000480c245e11602c100c0359203400c5d040b8007140c414140802e03456421403080b00305000c80119907220a16103044900710407000d80c6c80380c10150640303810002c681c0e0040029165041c0180305000402d44d524001c0c807907203001d42c8c0e0b200c5c0526420b905c01c02c203841100e5030003842804205402046544400e0180014501c01468034003c0b03160200000303103005241811010841c20240c0d421800e46103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 409026555 1250 409025305 409025311
    0x51e040c110102120405060705030417090a08161802070203150a06170105060108070e090f0c0c010c0e1f270e0901050a110405130b241c0b090f 63
    0x520403056080c8103a80000e0001e401104d6004002e0b41640c98582061498964040c041e2814010100184004034407a080c644c1084411940c0082d03540403071801299603120203500100c458000c03072500e001e240340c1c0324000320219181a8002940035861000d00c004a200b003420080d45580240c2c1a203841180d24034102d64812504140007558940e031707800b079580b04032100b841030020f41d5544042203481c4d078000c0320303544c0c001070607181105008070001e004c04c0388104054020811207c104000415201c00130080b5800b001d074010090203210501c060142c010070031030108510442c0d8000349480410502540740405001a42c0c501d14801422a40592540c03080101190011000d42c0d0106001010f001624003d22101c2c000191910701001064100d589100d085c031282d1400308020022940e4554804400708803c2c0303000500d00000c0c10010f20942d540480c644035042c52220706141420000d070244c0290750b40d840751080c4a01c90322001004841610720460f600c20b80220200344612040d4030b555034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 409027805 1250 409026555 409026557
    0xc030a0c050f030f03180c0d0b1f080c01082203110a050717010b01030507020c010302130302090709060210020703140c0c04090b1506070c0501030c120203010803040609051e040c 78
    0x302110408040b0383c00d40c1d01a622102680b080003051194419541550700c9242d6072980152200224141c00110b02c4045610081c04082e181c401140080121103825508109103501e40720a0300c0e980c0914a0301d503800f89401901044100001845c8011a080c3d020100c0717401e50742c08003485950303650580701c24851421012080c4a0803001d1400100101f144034091320304038601040c0000c44d20009400d4034821510181014285802d210382d440e000500c8020241c801d09005d61200c04106180c0e80b000540e40c0080d5101900c0014003400e81e8211711040e040da80c0540c2a11092182c0c03403c0c00b02079201b1000000c1c0011001d00f00900e070014400f0140003451110f1082d1504d211180c800074056070201101500c05d00b10303290500c540115621000301c2c0406055030001e0401403562140803c4050a00c907803418541c8a40b038401c181e900c601844113814000f01811501c95840300100daa07240c200f4040c030360203c1c1d0340c0c61010a46103403c0c01410f9440035060f01c038918036105079050002421120b2a1a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 409029055 1250 409027805 409027813
    0x160c081b030706080705041701062318090a02040906050f06031908030c090405070e1e06030609040809030d0e040c092301111b09010603050c0f07030509060a1707050c030a0c05 77
    0x420510300b50030300f5061441500002042e0302f414074122903480d0600040704040120456060f0341561145020510076a400491101107665280300c0c80d0309190b40407000940c450701e41801c0d0810000503070310880c051202e514002e8026a225020300d03030344d07988502c820708408000e9070707185000a8401004562003010120280e0034181e114010800362441900e0142c0850a940700341625400c04034403990b8004c4403414010800a05480411038510001d440c0307034040d4103000001428885610308840034224060100c40e800703404803500926000c801d0340d1040c855410011000765440c0314a415100361109003403c8484501e00b902d4500b4400e00a400d040d0500c039011038080200d003c20f01107400c3e45028001c1804100d58407104000b110001600101c0c2418038220a000c0481d9000381924a000010409d155a4150f03500302a2954041d01c0141580050000f4a2000b901d500210700c40b896103610308d01030a04e45803c40705a13114058400440300b44da00a0041d06081442201da000c83d030790141c4161 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 409030305 1250 409029055 409029059
    0x20601170a0c060c02011805011b11030a080c070503010603030f05070201022d010f0509030403031b02060d02070302011802090a1d030301060206010f0909080405010e06160c081b03070608070504 85
    0xc10103454250f0f0090000c03880c3c4003000025560011900b0080201d0742406002840c14500068a00224100c038030f170440070079609a90130804031500415000030014101d8552107090714003c04194840000c5000c140100f00001a450505018101c00c1d65030548441c44403050850044801d0303040484180d0440c8140b41c0c2381c4144c03800803070344494000c44075600b0380046040d6040003420f440842001d0b0f0384280c6400e0420204c90008401d460940b230b410300d40400c00b480b04000300c0400c030070302d1003001c2d6124a00290000703000e4070f1540180495072094000380800d10340c03a46600d0801c0300042010b90081d240c0000900000310381e0f030081042411a94250039200203030210603185800c26040040540c0c0701c0c00052002800354140b141c0102440a0148200b034610342e41c1c207103036001d00e11589060000003000c1103040c0c5d840f001510b44a00c1d6068040404880ca8144a00b04040e00d11802025010b01c0c1000d030419001c0084199003001c01070001c3c14018a44001212600002801c401c01c1003002c1c080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 409031555 1250 409030305 409030313
    0x3180c03060c09061306080709050315010501080c0c03130302090c0306150d0908031005190602030a0e040603080a0815011407021e130b210c040c210f050105060a020601170a 76
    0x201005082e247d5600d40003441c1050001e0800c0b8200e801c2280b09034402901401103510300b00d08581514820701e01144a0f85070303114102060700600c0c1c043d00b8a40000310784070050130342c10076040741164000c8590100c5619a180340511354841600e00c030f9000429014842890120360008008111700aa40095110ba40b0348840405410a55085a51500c1001c08020038507200142c40110701440e0100c505052801d40003030340d2485281804028080c405c050520282d45980c4448000c580281305196640403880340140220811540c0e000500c48684104003030354881c1d00c0b50044d041d1640c540701e180070259002c108020030401146103074440300c0824044241c42c1c1e892416900c03041884040f40000d0b1080030040c60080c250b0030709030403c526000c2148108000100382c0440b41d01900d0002d02d0029440342144c0c14444034032000c0c007580f810340c46080100102d51050000824241042043d070742c0311000c00c0054418402507000607808100144280c8403070286444410000d4004c440c1080c0a59131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 409032805 1250 409031555 409031587
    0x9180d0f0504050418210c0f020102150a20041a030624070308060102060402010c060c0c08030c09040f020702090601140702180103030f0206041707060f0203010b03180c03060c0906 79
    0x2803040c0140801c03c0c0c03c10100011802c0350f031240b0300511020b4078501b80e42d01006000701038032000a07040d1240700c03207480156402489100c1c0c401d040164105030030701c0c2040078800038007040030060500642c8150b2500c1000e0700001585d0540f0341c00300303065100e000320800d03945007a000904850350191030043c1d01c40e40d05841218040c280c110380046103480c1d000504002c1d200d4030005010130f040d03402010410006030780c84200342c04840d40c0245c0018168160364001c580040015200514203580003090024108078003002d8822410120f80510032400202d00403016801680002500280d14101181203507002c0d21940015980a00c842070821040e6000140385200703c0c40c480e0128001c020041c001e240c0d000303910705c080c007455000030031540c04c1540d0b4a900d0203122072810b1170460b102080400402200c0d800c46040500c444800f9526940c542e10000c0300c0b03500a07241180911500d01d144003074400c1c0410700740890000200a40080d9944e00c10034807455100c400c05a900c10303000c0100f20480c0307841d26 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 409034055 1250 409032805 409032821
    0x32706041502060c0301030222200409180b0c09060c030a0c1509050706140d062309070206010501051c2f16080c0a0b040f0209180d0f05040504 63
    0x80601409411071110190038407001034501c03e4560380c20001130000d604c50b5101280f40d00c054036504801c0d48018484c0c000101807414440c1c801ca1840d0158001d0441c040001d001a90f40030722041000c080007000d00e22070440802c6005141c1d4502e5000169206802c03405818440c0b0081c200d40d00c3d215447c00d0142c156404125903101058021201c0803e1141c18018501c0e00400340c0e00c2003141000341d80303803d540d07500300e031280804001403041c04401030038184090381c1d060b0910075030034091541c44586180701403203421842d24417004260003001451500078000c500078103058001e40126400c3c0801143c0c01d50040400103410f16030b000c0e03901e006840e10320451900300a1106c2d09150202040c00400d8480450700f42003286c1c0406110f581004025080402003295000c005c0d29621501518201e0a1102c070450140902581c441040309011040f5098002c1324800c0b25580c032107a91340b0352119034a140604080845610444015010600034030502c1040c035a91f0034010b00301030782c8000150903a0000d0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 409035305 1250 409034055 409034069
    0x30e091b12010915080c10021204080601090e0c06030a0c0e090910061403030a05070c090603120f020610060509011413140904020607021507060203070f0f0e010203270604 75
    0xc000421110352980b0402894020484180c0032091419105c02e507a0b0030102d00700c91040305181b05074610703e0b00810003003004400341040c0c3e90311540d441da801502e95109108401d051410b00350080e99075a07004c5000407101e0f070000c1c05582103484140c9842c00a140c0101e504061040c4800008555030722415071520920340500200103c00d4480181019070b10039a20010038081000800c88803940c002c0142d42c000d2815191468070b41000742042c3c0000c501a5105a0744a45420804800c0c80f5010700784034410029034451500301594004200c0c1c1e1208100d50200e40100c00c140e0038003160740b151001300449481450b180242500462007424164885030824582c803122060400600400443c10060301000320756501c00d80c64180c020403941d100711b0400a1281e940120f0740d1199245180681345400e400c84411500c80c40d10080182c4440740e403810380700202e0b182d2007603058940e01c5440914180e46041c1d02030760600001c90410310315552900c96000d444484041002d03000d44031600900020711031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 409036555 1250 409035305 409035337
    0x10e100605031605090a0e0309040905011506080f16030f06090c11031207080405070807060302090f03160b03060a030212070501110607021903090b03040b010510020307030e091b 78
    0x68002050714120742000f030301c3c142031440c0c4020032941c0d48462038a6403200301c003100410705400744412030b411071141c0e10b01240c3c054a0107480d103060010552100700c00000b2030725070400b007a03281c000550b05c0b10300480d550a030740403000300081c0103540b9030b451a9621030160f00b03022600d1180400c1c004103070b030b0407501702d0001c00b50344240074044260310a0480304425400c0011b1480c000a03901a042200001000300d024461054042010070204220810041c074109064070341094440d03900401075401003a403548035003441d51042c5080d06c0c0c04503241d40502250b202e0b502d083d500e0440100100d800043c403495005d1001d40000000d0b88030030803044040c800e990003030f080395030400f070014044194850548150340e001c5030812043c00d0300000c0c0c030207810411224014080c0468641101c0e00601504410759916003c400d120400102c1c0c5001030590700100d0301c1c000c0541042c60100c0c5c4d02d010f0b500c4081c0004541c160050719504100c0c40703d03034004011482c0d441c1c80f04805000340f00c8685c0301100074814501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 409037805 1250 409036555 409036559
    0x160603180f0b100b07050a06090512120702160608060d06232401080712060902120a060e070f0c05030c0105091b01030c050a03020315090c0a020c04020426010e1006 72
    0xd8110f0f0b40b0040c10202001a05100c00303911007582d541c0042400900b01075803800e00c201409001c2100d00c400354461910259102802855111903403015142100036104220b01881544071002083c0c00303132022030799840300c1e035680d00c1d007044030f43c1031941010358916550703400300202d48a41c014182c00081c007800543c01c9a0426a42c180b1950700d001e04044050046602e1640c40b513a40301c0b0038943c2001c01d038900030042030441807403440102101ea0091801c144002543c44000d8540781d640c600c02d07041c00324204000340d0b8812040300d0500c822550b54000948208400380c44a010340d01c0d495255014500b26800d061009a1076400c60304e0a540d01040e65000b1003043c0f48101c030390800c0f0b010822080c81d0502c00c002c00040043c101c0e0007044211b009054000c40003172070b5444030100400500c500103000040707130b00b03101240420380e5200340d130203c006004030001c0c159281000d00072541200c0052518607140c403003008424043c50780c07020840f07100c3c0d500c0d2254008504802c00c001a0014980c24001556038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 409039055 1250 409037805 409037821
    0x905060c0c011206080a080c011401230d0804120c03120302071407140906011b0b0601030f180303090228052b120311121503160603180f0b 61
    0x2004802e0101c1050f41001405e1200045c08540ca440c1c060740810070035103440e40400510f02600344002c89080b822260800001c0b01c190500d4011008030039007424401d107812440038440483c1407a0310103440c005041000f003158141080c400c03440a0701034a071451920380c888e40c41c10190081419a00700094000c10b0f014184906c40d4000d0741594400d80080458503e071450902200d041c0c442281e21410000c0b0000c2c1c80313a4021900030001e11300c87c03403020360389800c14580700403441d40c1912a10300003450040a0303a5a5009886603140c081350a01c081c01d940b21455038100d028089406040743c11a0100941220003800503a8858402c0341000480381d00e981010184034002c90400248823225482001c00c01034610030070f62140704580c00c10407044041d087c00c0400d07005015200b2560409500002c0c000d807042a0380d0a420740910032402d462000b0036010405c060352380350142140f1580f80400ea80030000036009511615050304510303c2d051684809484010950304106029030302030300d58004000c17040e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 409040305 1250 409039055 409039067
    0xb060303160c0501090518011526190c1b03030e0d0309110103060b2205030d02010f050901111611220b0102070f0506030a0e0a05070f05060a05190905060c0c01 70
    0xb512051f10b040c0d8443d1110620030b00e4144040c41102200060321010211710b40c41001c0d0004001c6160b4804d41c0c000c980035101106440c1c08032894036059034415000200e040e090700400000706031360f959010308034001ca28111081d0084c80b80440501d5595285c652181c08103124881c2c5040c1d85480001707501030385040c004002d912010455040510700312060042c0300060044d280c8961024140c4002d6030b03006004e20300324403d9600119450310900541140729941500681c50f1f480460358140f045407607840440d826501d080d1807980602d4403c3c0124407840f404420035295050003a01852003008012000c01d0341d0029210802200c0c0a45007602400b100380717802803d04071102807000381400c5240005040703021549000d883d03c554000004030b0a84e40b01c0b9003004101507140026035890900c0c1380b40c0a690340c681e6101d03411015040000c00a5030345802401c0e06c1050b20f4548a4510741703480307560404008030407a180e00e03051014030740e00402c09455020250002c01c0180c0000d09181c0d98440016100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 409041555 1250 409040305 409040309
    0x303020f01140117070902031306060504050c070201080406062303011b0210020c0a171215090a0207030309140618190201050a0207031e02010f0203090307030b060303160c050109 78
    0x14503810102a40b00c40740d0035511041c1184c802e00303c03110200d8403610380641070001541c0300c001d1190000c000e021004c40d0688820700302c0ca100c1c0700700304025590f40e030a001c25518102c81c070a001510a1049a002d5409801610b5008c1d01c03070280082e090362505106c0b0300180810f030540c240b6920003000c1c54424103092041c003984071504803610328a102c66400003540e405100c0740640f48550040f8800c110090300b005441001c5034025040e1a8003040300141e84020b81101c256840031000c0c2101240c803504191a65240781e138006001e58906940da01d03000f00181d0b1000200314100341e0384064103c046031040ad03102d410001010003520b01400c0520b49540c00004070042001141c00145418030100d480d8030703108001c50360a00303180c0e40300e4030307a41e4085e401c0014540c005440c165089180b0100c0d542c060b040300505074802d03240c040142000c01c0c41265207005400100d90543d218010030300100710100c10860b4460740003011680b610148401c504214408081d044842140000b0309001541e000a54240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409042805 1250 409041555 409041583
    0x90d0e030f070b1e0c030d1407050a051b06091c170a090819020f1903120e010b06071b081c03020a0201020d1b03060504183801030302 59
    0x21200074400320562194050312070101d44580001c1d1507a03031000c513402c03a044450041014251200c25150040c5e48941c00300410b064007078036010205402d0118001c406010f841203035500c500b00b410301403040d20107034082d03420303900900304c001c03000d05041a082011912400140b00a4138002540d54501c280c3e001c0484068000d10805138244030310740350700c265040d074001084080841c9048041c00c0c00b540510590040d040caa5035040c0c040c0602c20b1b00015401103a820603404c5a14107042d040440c400c080603200c0040c0026407800103107140540325003024181c1c100c80000003400540f0b610000c0c410790f001d034108031003142509150f64098440200e201e07000741169405420320b05e2040900401d418080c3c1d90320030a02d0350110b507001c0d000e8401d505480d10b21118000c100301240c2d1307012072828124504017088000905200020405041c28080c01200c0c1014500c4480521a140d64002d4101c0070861a241590214102221403440c2040b030300440344e0f4180c11002035941075040003410b01c0e5070740320038070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 409044055 1250 409042805 409042813
    0x1b2117090606010e0103054611092101050a060512010605010804021e15040321020d0e03010908030a0608070608040503041401020f0709050604150803030105060918090d0e03 76
    0x650b60032149402a907142460f0000d940e07940c290300070b402600c0444407019001d40c6000f0901021842302148000c40d0187c1d4a24241460034034005410342d07c0c07445031198507510a11060b5828200031007001da1076281b000c0c07070318a1032140001090840300e044613010721041c0c80d84800c101c0340c01c211104213030281d0350100a100a600f001b00181400700d010307000070f009a8050b02c200c4bc3e8600600003041c5006401000e5442c156020301080200e500071380400d45079001c0941d02016103d10205190003c00c25079000f07805030201d642d009417007400c1f2400d10039030107540b0b038400980096244001188510b0303000000040340c9003480300040c42c10100d50030040620810f0401e2101081300001a5421100c0b03082c07000001244000040782440d41401e000768241c4110310000ca00032505070056445084203032820440c008400f0030110086010b84188109034000300014412414a80e0044c4044280600300c0f503d82100c0f8504070090030021144428180c2007031851401c116400516008a120101c00030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 409045305 1250 409044055 409044061
    0x222021905091513030b04030309020a0801150312090503031b0601050a0f0506030a0b030109050a031b03080f0703021303030302090102150c03060915030d020c1801061b21170906 78
    0x21519400d0001169072415a02180c48138454001c019064040c1d0750201c1091324034201458090050030480c00101e04c81c0c9a04040803400d03100c1441081142030801482c0200145103840d528508424480c940c0100110340e000410f82e41c07010401020013101e85103078000e40c2103417100101e05140c010b800052140b03144d58000c211040d0980b80090603158100c902661302d841d050340c144020083c803108290194280501ca60500501181101e00c83c0d001e51120300000340384030190030161441041c020085031056000c2600c81e842c103c210340c0c1c0280b4501b0010700d0403040141a207070905841d401200007a40008001580307503414426030180c100045500f0b189424404c5080e03ca900000785100c1c00b810740c8400144421908680c400180c14000e03080e00d0562400c0c000003900d486090034118000c451440c4200301340000b00c54400c1c100c1314039640345000503004501d00130303046250500c01e43c1c145101420442c2602c3ca4010412080d43c4562204005003d802020040600d401414540da9406c44420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 409046555 1250 409045305 409045309
    0x21c080603010614010c060f06090524060406021917040b0304050129040f0f0f020918090705010f050903100f18031d13090803060111060121022202190509 68
    0x7aa071b01d26900c107002050101401990303000900b82640030021090800017400b40400c3d41c0640303442403038441c2d000205403003d04400e009040c0305501c04c000041c0d005a440d02007403117035800b0b0303510300743d120f044103044440200350788240c66001504a400703618000004e11003000000d1280d0b01d894561141e0b19008808841c1c02100100c50107805a80290344030f4210307452010341c2da03010683c51000400d040195000405092001b03400c284911070044031a0b880388102d900401e03083c03600c614452070007090000d0400004540c000b000301c441100740b060910a00ca5142c1c1c05010170740c8420354034a000100c5a0b4241c01c8181554080074074a03100142407030541000c02d40c4440881d08030146101d1709001a085080490100d2020307990680040e8a0a0b0b501002c002c00e0400440c000c0400341d0301c0509203240c00b0f100a480301030038030510b40c2002c05180010f0714040c102c802e03240407500050010380540300402744105082c4000001d0700004d68000b46841d001c5c283c06d64114114902403600d81c1c1080c11141c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 409047805 1250 409046555 409046567
    0x3061c0804030602030414010606020f0d030b0d020d02130921110607051c020d050f010f08072303030318060a020f030c090d140303012c06010e01021c08060301061401 73
    0x10143c95a0380001c00181400120b1083c1303800c050350300b4006c000344e641e034807402502c0384070a1905a5081c01118008031030310780301b4016400784040c01001000001c0d6154204074611004030700c104c0e086031354046412800f80742445103881140c015501032040603c0503003400300d608c001a468105015441c0843d9140740c0700018012b601a146092243d038400c400c0c44091703c0c0c04183c140038480140005205440c20705550095805800380d016290200d9803940141640e080d200d02513803056030300c01ca401f08100c0105501003288040200100442c0e801d4000119086600c110741d0300c0402c00741252044d8810034100500d07030748102c1a82085081038103d5140d10b4662202424091868a020411055641d101090b0301640381c0c0c0700031303611040c1711407111503516500244111000400d46203c00c1848429940340c0030802c8513080942441551514015900c01d6035102e5103138114850202c4400c50361070042d44600344a585034803030f0301d1545800401c01d802c0d034007190020001c445079000741c03a80a981160b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 409049055 1250 409047805 409047809
    0x2031608040212120c01050a0b010219020409020913020f030606010c14070806010e160c02010903030804111c02041b02151b031504140105060d0905030c030f03061c0804 74
    0x1140054003a2140c1c00021010700c0c050000071414001c031000000411304001c0180b204803c0c0200074041c1c2d50301e0740054400c0307811440747c244c05078100032001003003020288042076071a440208001880c004613004109640000c413254501083c09543d650250714110005540b00d1804030020b010926001d00020400810041300a040d95009200301410f09810310883e4050042c40084480039a51130090302104074083c0c44c00307080304446012225108d80301e244030505560301a100c0090161a50f58121200d44005000b5940715610040c148800e0352000c01c01a02c4001c00702005000344058010071040b0355850740c003c110f0712010b808944c2d1031034011076040c8100703c3c161030304505543d031081641014030725600c89444150340002040701406003205032101c1d000d0280d60800000480d440744044951003030194560260081c090084807a0343c1d50417020500c2d02c108183ca00300162841400e2442c0c001405842c00104040100074a0b03003000210f0b00240131503661407400000341f130380701c41d1b42511581c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 409050305 1250 409049055 409049057
    0x40503060f071d010908030705061e0105010c081b0106090608070b040323030c030412030e040203040b1807050d12030e1b101707170c18130605090f010f0603020316 72
    0x81aa8005580c3c012603505d0002c2c4079040690341e58030035901c1c0040d02d80348111a41040074000607003510b1150940400c50341a1101070f11410112042519810400d0304540c8526040091143d880d0340c10407000c4c06040028a910300c800300b045820714800ea41881c410340c00c020001c803814071040002c200381131070380340d614106014503800c402c2c002002181507220b0700d10180c500744030004000400b03200035414101d2850180e0f03940c1d0101081d0780100b000f81d03c4240c401811988003c00450b02907491007030464180386840080f983c03519601c90104815030004a42664181751043c0605811034150041c11800150500a000c8141401d200d00d48043c000aa049000c0e00104250310b8070b01d40030750481e2203525107500c0b8542081c5010075008003c0030305c0750223001400f0101c0300840e0302c2810b80420b4a070b01c0314100304400640d0400e101440b461080510303486010070388602e400582c3d40c441c01d040500a40b582e000c0d40041c2c0d8140728807089541802d82c0000e0130907204004000200b0590040945e4400103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 409051555 1250 409050305 409050347
    0x90e340f09270929090106060f02061b04170601093c1104080a050c27060301060914040318030b06010819112106030d050d061802040503060f07 63
    0x140d030074a081c40c40b01410145004c01c81000700005240040c1c89000c1c412201e0b140240a03050b100d0030115583c5d41e1003140c00015034008800f15640c1082c40c1c400107180322280002c1818580d0740d403117446041000c524144410342000f80144605c044602588205820303c0c06492150420b00c1e2540e561003040c100c0e070070041d0201065092200040d40c2185894100c0319101c281c0304ea840e0401c03240c45150704001122544915022030009060038031804043c2c1402d54020010501800280c03a0b01c202c00900e2160305559420020643e030306540b1819034009518003046582d403800d0315000d00080c01000d0540c80b548600a400c00004180c1030429034001c8017841d0050460b168042030154510a01568040140c1465014070315004224040e04803c00c84900301d5218070a1240703a0aa50001a0bc0060309500031140400c14540590011b05402ca00e400c0000b8246c1c0d643d464592281003644502402c25400007000c11085c0b030100701d190b40220612409081c2410401005010014a01040d540e5508 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 409052805 1250 409051555 409051571
    0x2010f08070207080109030305090d03060b160317070e09070206010b03150303090a090b040b1f0c0302190809090a05060109030231090b07090e340f0927 67
    0x100c03d200e044014051400240144855880e000c1c018200450b007820240c40345001ca144418070a0049004a03054030440c0ea1901603d030b80c491400c20024501582405608a1501405a400e441541c403807036156940c88140d445400030042e10230805869213045500c040700502c900c042ca50100c1e80c0141503001403285882c603000c042400c601407031001c19804151180005422000e54200f125091011102000341020a10410903060141c01c142d04480010f4680000c10900a080ca441c0c142e0003801103844880894850760541510607200300e0310300c040484c211160382061092141c02482c10032040c015803804200003005200e541c44042d108140255800c8141a00c542040c2511015500c805022889408a0703a0150030098022506d41c0e001500040106105010510079540181c0300f0744815110300d420f49194260f680000780244152114100346200c408000311028001911944100b03100340b503024102e0b07440ca500c2464519003905082c03814620081021200c60319407040000c03154 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 409054055 1250 409052805 409052807
    0x7030207151b0506010501020f010c020c0f040e1c02060f01030201170403050f131a0906160812070e04060e060d0f0c090e0a1506030c03121110020c0708070302010f0807 74
    0x1010404103000c03150a6048030b400c0c49808100241a1103003070302280c02404c00c0c0a00c50b803c0307800040c1c0d0388005070080756030640d55141145002c0c040c101e000300f0100e907900003400c4c0c5ca410b0143c103941100049020002488035260180300c1190700c81081d07440744a8540c035540010b0300d500a80b8007150251b9200000141c1054080d00903618020f40002115407105440c00a5490803203081c02400c1860007a070704032807840e900704001c40340c0840d009820f003424019480c2c45410b056000310b8040b22454000d1180046800d100c0c07502c1c80c03050340b05582e11120801000b061008603103854005040b0040150f0411a1588a0561313100701c6941c0007006925980c2d080c10850721800ca260404c400c064249455035401c9500001c4030703030315980034407002c1c2c00903140c0314101d070300700c55091000030100c1d002c82c0b50400200d16441e0504080e003125007010200700001d04d403914181100544200d11850b4045420414142c2c2080820046d10003007006003422421500082c010000c8214900308200c2c80200141d102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 409055305 1250 409054055 409054067
    0x19091202060a140a11060f100e070903080a090501031805280b16020d02030c06010303121419061a07020402130b03040605242202120414070b0703020715 67
    0xb2400c5a0085511203076050001006001082000038031791003050041440c08100c11111401101c000d1755480e42c09242074000c0c910090300612041c20f10404507400000b04120500a01c403610240d40d440a1642c105000901150303000022210401c0802a070040066800502e11250b51501c0b61841e01c41458010035601c507116201c0000c101c80502410311401580000005c140030304a5001d581c4041ca001c02e0480e0b80f40103929410156500050040011a0040c400d03510340d0703100300c8000302c0c40c58105e03004030f800c00c60140c41d081e61103191100075111416a0344200005800d007001c0800b1b1004001407040444c1c0102880a031081c1d600040c0ca00307031401480f51003401828550f00040e2649424102040203003001c64041d450321003148203035807611504030f03040d0f2041107008014011134040305503030558907122604104c1040c1c0d403c0102d00c032469000d40d004c0748158450301d07414500d01240c100050400600d0b50100103044000d0040c200020707000324084081d201001d00188190151110841e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 409056555 1250 409055305 409055327
    0x6020906090301020c012a09031106070605132a170f0f0102090414060102101508100605030c06031e0702011e020309010501050f1003020d060f06020319091202060a 72
    0x8190302c00038280c4a6114190000007d02c507115240503504000300342c0c194944411140c1050004000c9003041c00060340b06010001402c2c0d01038036260410400369a20412140d00795580341545113200e0096041044000c24a100803d0034800708002d811505059175540c400c42c0181000d405645c6007003440c02400300b065a0380201d008003110614883d0a007054000c2d40302213a280e0255007000d0b080307120103000030302060140d54180d005120000c4501440d9004012503e1200240050b012000481e000f04005044a40b908410006a828500340415140c15900d5a6107400342c1401d0003002882094883c00e1884100c4139540f01c0702e1036988110803401031602d5643d03402c4c0b2441000150f421075041c1d5010b10b2242c107103407000b0000c90341c0700c13001c0100d543c6801d4040d5074003410404107081c45074400e40281c0540d581030500800c049464400c1400d45003066000a001a8004524102d01c0e04083c6041042d000c0c1d1400c0440c002e60801501c1c48158801040103402518001402c02e0464030070714070610f03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 409057805 1250 409056555 409056559
    0x1030f02070b010e19020301032001092403050115141e040902030a0e0c031b0409020a0803031902030103021c0f0b0412121a040c090909060b04050703180602090609 72
    0x314a6849140d030118072002510320030407051041805d45000e15452080301d06031394024100001a0591071841c4940e86001c1d031106040041d403103000278642c400e10000c3c1c9841742d19a503852604400b21718005048810503032000c4100c01c04242c5202c5602c0d00310369105401903188106582d81e01001003080206130080140f00c030b410030000350001c0c060a207603000d94041c0301c951400780600c80d41c100e04156100704146003a43d241c0c200c145442d003002c0007603491040f4850050400300c2c030803281c0e0700011000e140c1c039400307650b042c1c00000c10055400300184501c0500301803060700f14103550460300800c406200390b0503c940c45074181500d0300140304966900d0307001c640d0321008240491626117844418841003944034400304020701c201001c22106c0c2c1c00303008201041216040083d8559104100203070060364518001e0000c4102e0100e80003416004d01c10040d0700840c008240ba021144c2804111407006040e40d040614001804ea440c2410b00ca031381008680003080580c46421490000f5602c4c40b405410310707 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 409059055 1250 409057805 409057823
    0x1203040b120403030c0c0203100209030a060f050901151206020304032f010f06060e0f180a05061008011511030f04030b090d03090f1202120705161e0501030f0207 71
    0x444581c075030032040c82603100b40d8090010410754281614072100d103007002903254200d4403101710030080da5409889a10001402c5540c0388006446601c110b9450307682441c80c4507142c40400000707980034095100c09400711082c82e500c807480d14107100318580a42da0001d150b950000003040905100d00e8030300e1480100c02000c0c90460102421005448604110450240d4201812030780c0000c054452038080b500b079501c81c010302c1e10720803080000b040342c0480e940b5401b08421810070440c0c00c10000c694400d05038480002007504222040100c08101c811144007086201801848501c52000b0305015608607402c2c007902d0318203085091811400340b241c49801007a8040390000c00e01c6050800540250391000c103850300c000398004201c041d120702a801418882c515104040007511841d410f842a8903944140c402100e0300450b40100c0d07030b200000c16600f0354844201c9891204480450500070f18010155440300f412566011401840314070401e07043c15a07031062622a003420750102d41045500c4480701d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 409060305 1250 409059055 409059067
    0x5030c07171e03010f0302150d2d05070e100c08131e051f140f0a02010507032c030f0307030e0f0111030105130902040f05150a050a051203040b 63
    0xa003564201480c0d40042e1055001e010300d8a401540859058840100c1c040170000d08640034000064407804040700c105c4020441c2c10134640945c4204c0410500c5900716100b1541e0111190703c50103100040340381d01e946003909101c107294120100720882041610725580d5104100720503140310f652200041c1591000190303500c0e2000006403143d060780c0300b254031003583c80200500000c0000081c05041d400858002d640341000c00e0f40d441c01c00c42410503182c1000110f5442148035580d4000c07580c41e4050079800300d18204180d80a000791341c3c0c444041d26040020292920076482c0031440024000c04601300754040321480d07102401181c0c82040201d803855501d050180c0010001c200b190710790545c40c00741d088401207000060140399450a5002c40c0c090070359017490b0070426007042c03030859084610b0b030350900103005031142e0142054920100c00b0016042c51301da0507415000446030b20309482000c1002c42808035507108641542030700c8003554031a090294030420301e8654071070ba4201c0510200b0210b50307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 409061555 1250 409060305 409060343
    0x6080f1e0901150f03020609150c0f03090a0506070b01090c0c06051006030c050a021c0e040e0a0201090b040305150a0e0a06092108061e150919051005030c07 69
    0x490902c80d103280c1c1030802e0f5940b40240703c103508203404000d5000348104003180b903900c0c1c0b04401c496403901c0700c0d0000d8503001c01d40301745910f000707215134a10b42a904082040d07a09850601c052400408003a5489403608009541d070351a003510500421048070340c2c03502078104140c403c03800c0c5180994000001c0107070f820b106003116040d03030342441014002403c081202c200d4600c2081650301411943e0024407821400310011050b1a90202400c4104050242c4415850b80c442c0180d802a003a07010240100b01c4440c00010180c1c9031940180e071030368000300001c000041000800c22480030341d5510902e142c0e2125041c0c10042e00c00000260140c0c0b00340000003040c0900caa014000141c418800360088412004c1d00383d18a40540c20250042070900000030000d04110035107080b05c00d0308010002824106030300041c241c5984488041c207d200206012031542001000c801c05490b560201d802c0300c914000c0000c2e0b803800c94010950070800080041203401d00d00700e060b21403060384400e10549600b02511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 409062805 1250 409061555 409061561
    0x70314090a09050a1107050d050c0c06030408070516060e1c0209160909050402010504060e030a051c031529130303050309060609091209060415052206080f1e0901 71
    0x2820906481c5132902040e01c0c5e818681c00c85d85580d82c0000500494140310400351056080b45030000c0550048060078141e6179a0b6600841c8510300ca40400da89544850034428500340e0150104002c0741052102403001070740000a0b9855050b0440307031446214030500c1101203000c0480d02c0250080003900901000c0707008088003481c2001c1e55079846407110fa03952103800a442081d03030040d010507002c000034080144100d003d10511003002d01110124285036844030f01e007007050101e070b0248a200c00040d0312410f500d030040003007502c10200c1c00301d4000d0601d180310410640303001102219607a900840b001e10240303081a00c0e4100100440d040e2116a28100a00550f0049943c0c10280c051540010361a20340314140600a004510003041c000f136078119003148950241041c55800042400000390300300d911040401e01103c0740c1c0c1e9140c0c958041c003425100c0c2d1074500074030400340b1034000424011254410485a0710000011600f140c54a4801c0100c08034400b000e030300707083c0d404884108408604150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 409064055 1250 409062805 409062811
    0x91215070f110106060e040513020d0605150604030206030c0c0a060c09210b061c0602030a0e0601050d1101120603080309300d111317010c050a05070314090a0905 71
    0x74503402d0107003259441e010f080f02d2550007a1004210f19604440383c46c102603100d183d0102000c0c20345281010300c1e40000c1e410781c00b1500102c840c0d40c1c8490410404001030710020207281c5003904c00e0340c00d1504590020300c0c3e030301004100c2420300c040801e000020000c204603100346150044002c0141305d9071407000505c070762070301c3c054000345001040303020040d1790740d4402c100310981d00b003260307401c83e43c99210410812811a0aa01805460001051000c1545440118007845d8402c200085806281c1c0300682486016070109116035a1010301d080400c054890700c108400c0c0c00d19101440000c0c0c1c00302d0400410450300003410a40d0f020041020b83c090024000c1d482d551000d018640c21141103184440c206508801c0602c4481f00f403281c0c1d50a00301c81d41128800d440c40300c0170705090413544411440e150460342e00c83c10b400407000391442c81c814000c2c451041d0610003071400902e82103030800040e00c80d22804800504020120b40480048540c9070140c41c0301c1e440080800544564649000011301015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 409065305 1250 409064055 409064057
    0xd080d0b03010b0904030f0f0507020d24020c01051012080d0b031204090b13020a050d051914070f0504062f03030a0222051503040813060c050d02060c091215070f 71
    0x10b08200120340109c06803840c0e00c1d8010f02070400c8041c42da840968401c0d50200044142d00c1640c180c400404080c0042d1514103c208000141c03071600e041c2400c800b4a10742e201400d042d40207138901d004540d80c0760450355010a8040c0c0402c554501c0004646021032520300309140d081c5c00f04000c41d640750990002c1c006641c0886941d2009244075071820201e1003480848008a40d04210701d0b29144000d400a55020030400d0001d24442100c0b443c3d001a10000c0745074100c07080042080120030341c3c201c4140380301c00e141e038900a4140380c2000c2010380014040c43c003e042440480c6051074040c6410038101e0034032080c41c2c055a1b200d051810890000c0e40040c14452078004808407018088002c803980321088800007030422000004002d80c8135030f41d60010348156202c00741000100c0c0f03081f02a6503d1401000c559032112400103885c1052820070a4454024046422620910404400c0f4000b0345450020444031481c0428080c0003503031402007a2a4800101407900341080b015941110124215002d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 409066555 1250 409065305 409065317
    0x1b0405030a0b1812251502030105010807030204030f02010c080c1b03070602161406070813140904020a050603070903060615030507090b0304080a1b060e0c0d080d0b03010b0904030f 79
    0x1206913155484a2180d400d0314500340418118103040740100c40b002481960401c10550464035120011044080c107009a0f603000001000340d940c0c4841c200da4060031510301103091506507a204196072406280107030401c40c1101021080c0f005450880e440201d5810440d45401c01203040396003090481d40941d4840d000f403580001e050341c00483d40c0c032040100001e50200e1030742400050714054661180d00381d000031081c0703d160001002c074001002110710111641e10100d14104801c50286071944000340203105070410b000040e140d05020b0b0041e610211286a203a0f0740f0384500b103511442c0350b4009440641400d10000d04481b1340b225120402203e030b03070f0501580d0365070305081e601e510191054801e105c00c20000100446c1210340a08841099481c203088440301c2c0d41c030801100c6080d05801c2e1825039403049851840001000f020540b444152003030f03181c02d60284c480c7c041c5030040700900c520301d944806035007190356029404913095210081c03141d5250300b840e041c001e102030201603551000c122 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 409067805 1250 409066555 409066591
    0x3110d0906230f09070503030c060121031b0314041d06060c0706050a1403090f010608010c02070303110f03210f010e0601030c090e0702010c1706091b0405030a0b 71
    0xd444820030200e802a242c120380103450b04001640c080c84020840042c90241500204255138103000074424041030740c1c010207255040026a000d1140e001000810b0404180d0a04000940126401c0c0c0c040c0d03d034110111040449080a5418942c441c1c15043e0000001601240810840e840d131034a01020a111501d21740d981c00030f101840c810b90000d50501c1d48004820400b45100e0402844005890b103041d40c0314100c1b01c60314101319002540e010303c0941240b448c3c1e80328070109214803001805000000d0000c414284c0c0007039141c1900d40009002c2011a243d1030422000800160604003032100840b90755500c034010f103000f108011450600510080030108034039101a00c1d009050f1040c0780b0400006890703813801500104140f0501b0418000d10060008901c4500c24103e4403035802d90b000401d4261414200800420b0594000399003000a80203021982c1c0301d503600903a01070300810001c40704000050360070359140a19440190b044c41a40d2181080055000301d06008150790800049182 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 409069055 1250 409067805 409067831
    0x709050a02030105090f09030706020d390e0a030b090c01080108060f07030e1501082112070c020d20040c030207020d030e0103150905071701030f060c03110d0906 71
    0xc0b10a10030a68800b50307290200303401e5420321a055401504050443e8030305403451b030702e141c1aa040341c5c04a00c0c003565140c00143c40308401c181110344c00c01c0200c0410030041e4044001c04903690344c200c99101080702061540c031454442c0c5000601854010040301021702d0109207042c1e070b80701c000c5042800181803400004086034005000740c0141162905200c095480d16000c90046c107200c0141c00c1c1034171414061210704580300130600d01070040c1700041c0401d94803400b04411288690303580c00c0352102c420415840b41d07203a0961030030303009a0a803403c841c0d02c04440c000640d004c403500704003030003403406c10070980d01d6800e84802003074820006940034007036805402c4040d4100c3c040c051000e034000000c4410b06001a1060b41c3c0344d001c910050400241002e0301404607009200c040d0000c0340400d40d20014041c1664105402c4401290001030801c0958155030742d440d040f4032480c000500712600c4031900d1107103900a8204d180706401e89500380f904c0c1c250103038484000d070144000903617445150000580f082 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 409070305 1250 409069055 409069057
    0x6020705120319050708031501261f08030a03020c070f03030e0f0310020a1106061c06091104050a0b040501050a060903080d0b1513050d0f03052a0709050a02 69
    0x2500207002039803d00100d149040d0070000c03195121001c10078108240340000380c5980145004a00d400d410040c1c5400d00400542103000303c51145d06030b81c11400c00748400ba41c44a0149900035050745000da081d01515016004031081900240600d0101082600c00541d040c0d0150040c6c640103070480c2d901c41d598441d40c906029190001030b0000e9008018190b8a040080541880c3c00014003216028031b18290014100d800c80103914001030300c0d8050003a0115810001e81d40c0040741202d544010600500c544032022080000041002da224a001c0341804ec2020048400700409042402a4640040c0b400000d149601403d813141d4a420000b04c1c450a24000c1d002c10b840c12034590300300d05400d40d00c4418160304003202c81703c00961200401e2400e40c8480c601603003944100c04500c1d4948021420b1202d42c145540c00140c012290a0301e24408610640100408250141030256499030700301882540c0e200da04201c071401d100355036000401240c2c0010b516044803010f00c000c00a0341c03100d084407002d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 409071555 1250 409070305 409070329
    0x5010303050d0506210115082803020a05120417010b1509060c030409090b1b0d020a0309140f010638070f0602030a0c020616030c0e0d060606020705 65
    0x40c0c014042d04005407102d502064000707030020311003000004c01140c1041c03442ca048a0488650351602d0540c03ca00c0c9001200c0301c05402080050004040c5102e00b01881c0d0485003800591046a101404107241c028464840e0480c0c000007030f00c0085008503000c02c000d900511801c3e800307000c0c0c0700407101c0c01441072042c0039400ca0010002c00c4074204c00c03900074140d074016084150740040b0401c44031816401c07c000500082c4020040840c1c580014101025810300c014401850f200c060180c8165034141d0504880906644140c0161941d440c12012001071061000050100300c10544109100e44002503251810f64003030b0090083d1a00d40e41141004040b4610415030b81801c01101c2e9030180c80b00000440a445804680e4289002d50300d4200c18030f801c0a40907a04207070300009000d50308a03e4000c140c50311070140018102c0703040c000c00d00c03071022130002070100800d0b6032442c4101801303100780c1404501c80802460315040340d005041c107200a0a00344282409803080e1800051982032220718104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 409072805 1250 409071555 409071557
    0x10f020f0a05160512090f060c2d0f06040618030903030c21080f07020a0218180607030207030e15030604110c160914040b0705030907031401020a080a05060a171018051005010303 78
    0x50707420503800316411452641c0d0601820461441d2140c99000b0340bc1000014480c80880140081d09060805200300c4030304151705001c98440300402d8001c6904510428116641450569900ea50718208a54200c1c031500107101c8081c0c84443e041e403016405250305004d03105080c01500b540e220440c0603a55128070280007500841c40d03155045180996048283d80600c1d9806c00c0a400c101d088904c41c108030003124800042607021980805140d40480e01425007030003515100400107240c00500c0c2d281c000103002030311031900c440003848000112002d8a030300710000400c5a0350304000301840c02041819008032915140340036041c0c000030301070103400c5000e0398000b03281d6461a260042c0880b5180c0c0005d2050595115182c0700000181c0301d042d80b52840c0d440790b000103131501d14501005110380700203401c41880900300800d211007903072103d01182c01c03903000c41e0003848900300301002340b03003031000120716400d413a803400c28400ca4981542d2204c02ca0b0500c50025a9508500c130030745442144c10a00005d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 409074055 1250 409072805 409072813
    0xa02031b010612080c0705032401080607140a0c020303030a0f05090d0c0807030207080706050304060e0a0c0b1c0f02030603070e070e040504030e090c090102010f020f0a05160512090f060c 82
    0x43c041180540289a03410380d41050310301182d19100440d203000030f4030b02150740640c0300104a00310822049645809061190301804050170060402050b4007001c0c1c8264400c01d20000710082010302401050121b41c0d405001e6903241d10346034403c00300800c4144502e510160515000032001c40b00410307011079004603a21110035100d0151180012a004040b0480545c03042240c0030484108c10050300000700a240d40e056607910b098508841030321745024031030380d80f1f902600030303e000164001c00b150107840040e411103441d244c2c01d940d28a048000700701a50740c95480d00c00c00c5941070b030f00358005610400007601110801c6170307076551180c407034074080754104005802810603108507e002d4014640042c0170349450300c5260000b100186541000380e51400c007604002411440c20358080c020100c004c1c064007001c40c100380c09100c122a10348181c1500404000380018000100d021050341115000e41050445420f030000b000d9800c4254000d018152252100c00001c1c801c1c0d290404c11a4413545844000e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 409075305 1250 409074055 409074089
    0xa120f1b1208060a08010905030d0b0418021005040e15030f1b0904061103190501080d021b0a081005040201090902090f0f03242203020303010e070203040b0a02031b0106 74
    0x450700b95502400580d80b00095032000120004240580c0350320b180258051582c803441070718200d04840200fa031441c0550709060f580d082d65040110040d000a8041d1507a401103a0300b240700300c0f02c07807040303400070b203400c1c0d045c0300500881c14810034110141020070b0f001c4440301c9158500d1a0380d1081c0492070255001510f501c0307280142450078425070014406c11020402d0281c0702001c4c0142d400844240c01a02100041600204c1c082e0088500500111000d0302b0070104a503002529015005080000408104425815a114030b80008014210b0300165100d205c0d64a03500310180c00d050310305a00007900301c440800c0c030358800d01c221000103100030081603042041d1000d00601c007500c13007000e039818041d2885405904010b0300c01901c00d0301d20702c2882d0119190040700b0320341180c00d000e02100041c0001100e103000a400004a9043d00d0381071480035003643e100c181c06c91861003190002051010b010031141803c903000009409039100303000211218140150030207007250050720032402d094406500e6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 409076555 1250 409075305 409075307
    0x815041a090c190c0c050a0b090a090501060e061b060405101a010e09040615080c040615022113090203070f1d0607030302040306020c07082a0907020a120f1b12 70
    0x1c0744c1c0010b200300c100701d10301c50362080060040c2800764400c00021400040c01c14080c03403d0b56000000d0001c60764200150350400034024510800c43c00350600962001422600b5482510309610041030010100c1d8058685450840e0321250b001080c00c0c074207030074011101404a82099200414074041e990f01c929401c211003009141c541c003410540c1d40550780d00112140b050b0340009803000e40030901c02801d0701148001842308550301a440303100544d1081c40e00b4695185e01051403091041100000100400c100c1d000103524802c850103a804007010043c002150100d0b078001e03601c1514641c480d8903402182240030f540c14480752840c07004058410b03412000c5481c110700640b9105019140c01070601d41c81c4c2d551141260300c02c868014050380405020810741504020080003d03e081d484c58064451082c500c4040020101e446c0344a58550720001d0b100a208124030401e20341c210621841c0d00b402e201c400381c213103030035805001d0004e60124540c802c90b841c0d030401c0c2801c0380ea01c05c581c0c8803104d0340300750 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 409077805 1250 409076555 409076567
    0x5060310091a040c05120106030804090207050732030f0a170f0403050a290604020703110d03090c1703040e07030212010803040f0f0608070815041a090c19 68
    0x12046503402d00b101c68904481d14000c0025124a00c142c0010100c2d0f4200b00c01c01a0031400c458107046140c2c105581400092081026541140c07500b500140c0c50701c50b80c2ca42203081807400c1e040b40381c0311001d003c0448480700040040400c0d2518140c031990440c03051106041e1954044184090942e00078100d940000381501020b04199907040b12090518070111044c00b926030256109070f44962003201083d05200c0900941c40c0400d5900e43d106401c1c3c60b100c1080c3c13803050001042c00c0d21441e40820341c00d05040c015491148440740341010340d038406803900170103001880b00d488141c4205905501c046800031442c0e134188000c1c50300034011802c26160142ca240799200080c507040c200740d001c2c040c0a00b5000729241443c0a08200f0000c3c588031400c0043e05001c86003264880c0c0c01002903c0b03410024150010006604052240b0300252079a0f940b0341109407400d030320b5040e2a0450b1508521419200c0c18100314a640740007160010384584910320f50381100c1c040c0e000703004034400c03064502000b414000c5c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 409079055 1250 409077805 409077821
    0x106110c0f04150303031e1b1206051c0302120f22030605010e0a0c020c01050301090c0903140d1b03020d08070210060e0402043c0207060608010c0206070305060310 72
    0x1c0c00412043c088500c500845101944110080b945441c2c40444100c007041c40d0408008141c03a0410010010359150030700c840d266580102400703203401c6600301c5421b55070401c0018060203040c1030302020090001305c524400104081d4014022166001070303404806040f104070202400c40745040c0720844001d01c1104190700c0840066007140e090010010f00ca80c0035460081071540c90103011842c21109800607200c00c1701c440c00464000700d55031142c982c0c2080076603042d50244030b00020b138110811400daa0310001a00090000d401134042c03980348250019081d07807400460740d16012030714004403a0321a500c1030301070000c025811454440c101103101c4c549460740074406104580203142c24241c81c404840d00c0d508134010540054080000b903080c903015600d018800050500c0c6914600f14105605481c207241e8003100c5d88004940c5860091150103a491444d00084200042580d0b0000035001340401034050026020f074400041490b030081c42914812580a0090074640d004550541d00400d084 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 409080305 1250 409079055 409079059
    0x111060403140d0209040c020a021c030c060c05090301060803030601032909041a0405010501170303091011040f081506030f060a0209010302120f040c380c030d0b090106110c0f 77
    0x91040405c540d80c0d81c0100603407083c02e07030064003542d00680140001811036514900742402c00d21080340000754400c034a115201d0b0800000200e0225022046485200342c2c046242d2640c00d1140200e1070103400700045010b40c9090f2000c1000d00301000c0000030200c0c0d100100c1c0c0341c0d00c0070781c10902d03224280984402d50143c41001400100c100c08040e030300305450300f5942521140e43d07500042c00404a1158200380d81c450140c01542076280c01e41c841540e13030703c2c000c0398410300b0b41d2a11400541100c3d020f083d54080e2860a64203180a61510001340da5007000e1401e1034540e9180c04003203803103400c010815070a5070440d08090400c0b90749004070140a07600c00d2052904040c3e00708983c40405840218942c007401182034890518185420075048c00c1017140c00c407000d62016414903126540d030364000303881076503904045901c8084c8100b0030146503000e000f01103041c600000030300148640059000200d600c10490f41017205980b18502220307072545a40405204d40c0c080707040440d00703103440700d00e0401030080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 409081555 1250 409080305 409080307
    0x301211070803010e0f0606180f1201020a020f0105070e0a090b130203010821041d041a100602071d010e1320180c12041109010f050111060403140d02 65
    0xa907944001e003560003644480c006602c901c05006100d01c1d29184160480e504651640c1000310300004c911000b03050784061071241b401c8603002c081945824a42c40341c14400b1030001c546842c0e400601035140c03020060109150352914000640603802650364034100d1201508104429081400a00c0285091440c00b5482101c4554030700c1c4001c0c0714002103018004803000750441c500403a500074445c0595800128490701c1c107100c140403500301c103000825a84240c80010845844608151150b072441d460586000e026200800010090541c3d1100403101d0940c2241e0140c2d035201e502d060700c01e03403132003250307000d000b007180100101c00c075400f03000b90006803c400d03504041050b07a44039040d5917010741002641e21080206440c5600d403001d9614158154140303100030f42d07d03184c41c4070742e030380d21422a1240d009080b4101041c18026072001c0d101488001401412441d6181d14441800100718440c4a0000f01006803200180001240180c00386a01d41c0b02e03440c40001d444070b2001681c1201d903401030000c2d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 409082805 1250 409081555 409081567
    0x412030608031b15190c200c0a0f14010804050c03100c03060e010302060304020d0804090501061806020d0206010504180501020403080903060906070806040902010e0904301211 77
    0x1c1c140000d0400e442c2003441c046901c040ca501c42402c24a4680c2816443c2108008100c036001c001c807126400107900d9403000604803698541510442010300c400849151861145a002d070340000d213145110000b15081c24000340d1310000e528940d1b04074060f400c1c04602601000080e54000c0c0c40175a0014468016600b42c0c00d031180c0881d1403c801108945000303500c40030000c2d4a989c151244070041c0007600320b411140d604580103d5003a200c007510083c06010408081010302c000d100a49020381901a0b043c002035039038007802004075038001041c101202c1c4d50900016558000070300503040c0c5c60940c010b0300e000c2e032030001004003e080442d0785204a012003e0400c000980a10040c0060340c45040910340b541030302000d0501c1d103c00101110030f1544508140800c507074100082550212040301c000c10701c0714082c401201d900c0746484455401c600e2000c00e0204201071400500e0130071406060850515403041100c00c1c81e00b02d0720355400c000c20500e01750190010607a0f04080414001150b04502e000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 409084055 1250 409082805 409082819
    0x711010f20060a0608070f0308030a09020607121805100c0204020c01140426070803090316081c05010f06230a1709010b01090b03101707030b09070b0304120306 70
    0x12078150180e81c41904a582081050142d62151501074030000000f0010107041404204503a05280000781c518880400011031040b81c1e0741000c104258060903658a41c3d07a18070301100b00c01c141c009140701282408071a05c40f41c0d488603080754202c4400400360444441204816503054501100680c0c019800b040000c81c0c049007401100c031f01102e0600d81242515140c04c1410400e50540210000d41d00400d58519400340420151028150080d81c4c882d901d49420f40c0f10f501e91302c2084212412109410404d0040c0800d50010b44003012031540d00081c4501d02141c0d80046070024050f6005c4603041d01d00611105105032196251a981c00000301d4825190340450a060741204003208005103080d2a43c810030714a0810b07450700504058000d114503581c0c0030003e403064a0758085c00f65012004400203583c951b010304994014004912101d82c0503590503041900d4640d580811340e410115040415070720007000030503a0488046a40f03190441d12a991005034154145021000700340e00d866000c50700c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 409085305 1250 409084055 409084097
    0xf0103020d1d1509120405130b031906050f0622020c0a0804030c0801020f031305010b0a06030b0a050105160605070c0b070201061a19030b0406090203040f170711010f 73
    0x2400e00d02e00030000354078206620a01c1d02c0000b0240c507142e070003812801d550f000d8500e050318140c0b142111007030005200f801a0790014143c072a04180d05100d040510700c01c0a0000301c41110346406510248025130725140c41000c0d0000c2990480d8210001c14109800d6804c5000c40342c0300f1900d40c0c00301600c0c1a4030041c0e8540380c030101d803034140d40c20703100010204100b0844142140c020b200540003507007042d02e030702e5075092280801000540000e41b40d0210a0130000290b11100081a004102c124143c3d1030b60b43c024002c10011102c0340c02000705c82000304856000d1030644040c6254403810b86038140c0c8aa4552016060107440340d030a01008013950340005a8021074180300f12045d60000036024078005a01101804003408001d00c100c0402118000714681d40d42d14200e051903040c041190710009001c50001c0105038000c41d130140c408000d00c0104690012000d0000e40140010010070301c0e481922081c0340308440000300f141c2075903180d042c41e650007000d03440d0303000d292801d10460040c400440e130301f40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 409086555 1250 409085305 409085351
    0x30a08071808120a17090a110411030a0f0b0a0e0105060705031e09010906080405030919180f0b0102030301060903120903170c011b021011040302030d05030103030e0409020f0103020d 80
    0x2d0f00d0000c14001041940003010084858080380154054180440f00d40d8407000512000781480003110710142007621650840c6018a10500340140d172480c0c071004410003880340590b039845003402d150241070540f81c2071410000381c0d1400306206006900c3d050070003040d80e00229003221140420b01240503400380d4141c540f010740351408061075854075400b00041500b1041c1c0c02140901441d5020300c000301e5400416501c102c00143d540388626141050800001c40841d4040c0d03219440005211120000c15009520843d81072501400f15150b1032005a07241d01090280800061b0252030030808240c01203000c86011a41d03041c165202e45c1c03241c80b2403002024142011100d1400011603513034a131000d22440c107039000c420440b08404400ea810094a03404040c13182d12126841c0d814006404150400f00c40003542c1c0241183e00a40c06440058441d03042448140c0c007042c0d085001213810700b81409425592035000b8030344040f4881074401900250003028034400d00569680341030030801e00000701652 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 409087805 1250 409086555 409086583
    0xd140601180b03010219031d0d0504051e0d150f02070f050610060f050901020c0310060e090a03020a0b070e090411040c110c010c0f0f030818030a08071808 68
    0x403000009981500c15140010b03115030090f0310400905101241c0500703040b800441900c1d001c240400301d65825010021482e9400da035500407101c05c2c2c0a2280c1040c0100212101503031254914030900c0d101c114001a101d4815411042101ca0440068210041d008110032142d0700003030103102c0031006c1e004a8002020840ea10302c0d8004a2006005081241c95409032501c20400c02103800d0520003080e104010410506010000c05d42c001c4aa0090009100e9100064200d0310642126210200030b810144251200c245906021509100010921203e0150981c00a06ca01c2c004c980e074894050788000e000300c0070442403091804c86941da0900c105d00941c01150b0000c9000104c1080000b00c807a144c0e141c0040c01400c4100c0d142804000c03c404030220000d00741340d0703403030304440c2000000c40326140030007444a50011030704020560001c2c00640515251000032211040c449042540d80c40f41d600028007143e0300c440090422445464014040d0711254251503060365141c0b01039283c0003241020070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 409089055 1250 409087805 409087829
    0xc0a1e091805150402090301092118083313060b030a030804120504030f0812061206040b0c090301060609080c01030203161b0b13120201020c07050d140601 68
    0x10400c1241e00604460240e200100400d007802900b100d421012040c14500540d0049103824080c5d800303511914075503411805201c01b078400005807056071100200d04001080794414101c0c1088201c248050a03035401400412808000084920b5041480f0000c01d0803091080300c0740c03400e02d0003030408a001d03103415030014464481d03529250f4182c41d0080e840314042c1d44410017520100364040180d41c0c105070001e123400403151090318201e41034496600050720141d04110b880341001440c02c01484001591681c008003a22600104601c083c03407480319040960040c000308012800280c40143c00c410030043c410702d401e45a001103825100103622803000308100c80b10800075400c083c03110200e020002d103001c6155150003d0304103c544000c0c0e0414040003400e81c801c2d0b41c40210a114a00e210360002d6405000d89840c0b5008410781b0b00c1840111801e03450048900e4010f4014001d9031a40aa41c40207405241c4c1084140845012a180256070031485c085094800c418140240d07406008205000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 409090305 1250 409089055 409089059
    0x1090e0a200a0603021602060d02070c0e010e0702070b251b1e060c12050715020316030902010801060e01020a0b011716080a0818030d050a120506090c0a1e09 69
    0x12440800070392289040c10700400c4600a510b038040c0346c004080c0c0c1e040310501d03180c1050300e074104003e00502d10014003031514864085590440300611074100c810a000f070056a40d54030404170703244c201034800c1108100090001ca5441215001d400b99880020154030091201c3d503142c2d038890401008000310500250007041c80b44651468024140e09204003143c9400f6140c560000d101e43ca003804061322100c840150500707081d20517000c81c1c9809400890144412000e120000002d51007911500340102d180440c0100c25806400744c036400035016100d0030501da1800c0401d031082c04e1100c0c011b9046010f5040c1d80c40000f02c42210590182440500882003100826180d0349055524840700a41292481040000081c0000c4184c0b20545c45159541c491440d501c1201040c8002401140d15015407003010a0b06a40b00c009025480882c0e51042c1c01d011585040608071a01030f21015000b981100000f0b050012510040c01c0c21001460300c4004141d0303d0f8403101480480e40c0722100015000201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 409091555 1250 409090305 409090309
    0x9050715030605011704030f021005041101080105010206040f140c13050a0c020a050a15020904020a020a061a130b01020f0706020106080715230d0f0504150b0901090e0a20 75
    0x40754040d00c0203003840c40c1d001820115042001704000d00040030080f0440c17036010303803071310900000c41e85601550041c0410700b00344c5000c0381c410315440525800200101c00001c0c0c076600c000307403050003a40c101006c200f000c4480c0d203d00f8420500701d208031a40d40300d074448008041e102c2d0040140c150750107405c006202c0c03c5c5401c243c029990800741c084215400344860708003040c0081111000e8991004610a20480d460341d80701c064010352052507440740c40818001842c9402090707841146100da482000038490851644d2070001d0b51405080d040304203039000c1c2e1128101035021700344445050044490318655100310714903250031904107800603510b8035030402000000f0084180039006140300d401d4040310519000303051400741c0700c048a213141c002903000300c038051000484440d141010f50600122a100041e0000b5181c1624110303002749503200a10301407542c5116509418030b000300b60701810391800f1180809000030030a003e0322402440c0d55080000c1c1042820507250020b03c00c3c072201a45000b007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 409092805 1250 409091555 409091561
    0x40f03061a040b090c0309151303171b0706020412120f36030210050406020601080309030601050d03030b040906062c07050c03040b03010b0c10110304030e040905071503 74
    0x103406406141401d01e241550364656241c00d40c481d91750440d0948a030340d07001c4007510345103001c01e02074205030380c007001e004406103040c8080e00c0c054084d440f0400c40007408400906c0103041180c1048800350032808201d00100000010402c07280110702c0541400d2310b481c0c4001e191441c51500310b80d42450f0b2201d8108043d001090f130a130a0707005040c841740ea030600d49420591103001c6c03245074982e454107100e02001c0343c18070300c50400510f030081c05014052441120191407980503001d075502500c9120000103020302c001045904035480507014000356441d0a047c81502014600b00301e05040e00c890245406440352300c030302d9908500861012400624084000e00b0041c20340031201c0400d0350349901c020380320082010064021100d843c0969a032070b0606001c60850003a9000f0a010384800400026681d00d410050188180c141c0c05841c4001200018801110030300903255000f607a05100007800701e03010721801220b161014201007050701555a07024140045500881028001c9840c40001154148 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 409094055 1250 409092805 409092851
    0x9150f0f0608070c020a0b0c19030201050a0e0f1c02071212171b1b03030405150606030f061003020d0203040b070908010b010203120402120a0b0403080c0301061b0602040f0306 77
    0x1042c00c8013422165008107410b6041c0303004012440c032002445002c1d21208000020035203540b40c100906004840ca0028040c010a840103000356003804140060715201007121550340e41d14900500000c207450030396012524008240c02d0550054001c00960310700100c4c0301c40d80c45846400780252070084404003520002541441038940300032582046110002e0780760382ca10355460800c26070b032140380395956109440216100716410340000320601080100c00102c5800002d8a1180440c80755034420500810b40000c90706054504000d030042051400c000c0070441042005d442c001d8644407070440e03440243d91003550300311642c903204070410260036403104010011309180e60084c0140c80446000030b6881c05100c9992070205d08080201d8115a91010105000703550740090750950076040c10000c4200104840690106080030001005ca86c4050103e9058030010f441c2c50002c5034071421040300c030f646540c80c11651203508000c04549604071940703010085205100204d01120688880c090b203503c1d035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 409095305 1250 409094055 409094057
    0x8070603060b18060f040914090c0a0e061323060301020a1d04020405040603080406020f071a07051203281803080a0605060f0c01051008060109150f0f060807 69
    0x822000c1c05581003101c220350460081001020b070602120000995610072004001c0040000286c000340d40c0032660000c140000344480d0010f965610020165260940004810b900c00c4181c0001d001d45400d100e12036401c03c1015040c0000300c200b0070900002c0b5800f01020700d0000c420b411056444054265429038002002d900079401c014041002402c000c03038041c1140d04c1502000e82c0c50400b5220b66043c0c170020700e402401444095500c2c1082d13091345d80103000f540c0c018000e0703501003ca60800014402c0881c0d00700304030030841500070070701d03d22031341c202c1c440c226110b0040c003007200005480007001d5809900c2c2c81001ca00c100c95100948c41e00c0c800800c100071441420020740106c1c031315013100f204a010340c06041040c0c0b250385a61540d00180103982100354070100c00300b001000d0503428009014a1071b800320003004030b5200c1d17811111b80e03c0100d1007810b090b41c0c0420014800c4007159007141c201c40700c04640a810964454252000e44141a0010061264a07000410083e5440003259401c1034032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 409096555 1250 409095305 409095311
    0x605180c0118140114120103031205010305150406021303050d02070807180c110124051903080c03120c0c060c0c030406030902010e0405070e030f070e22020a060908070603 75
    0x4015a680c400020362041c840302d00307101d403d000f440364091412500c10030074000030381e555060905800e010f44002800140c000407d0010b0f0307506044c60500c1854140d0360041c00400341b044c8003c2102d00c001100400440e0041d4007031049914807040b040c14600514800d03c090425080d483c10000d180244580c00001c59a000c22000c201c1c941c1210400501d10300340e0100852402c00d110000e6580550807030361428150300e000d8100d00c000b0442241d1113400c0d04544800e4034143c0e5264104140e080e40505030400c07a0450000410000c1c1c1e0301c0c002418142082002e50f81050461410007c403020102d440d1300c114900050750010344542403250340c1d446544038441608083d0281e4095690703009a014410600d40d448401609682c040c00d0180300d0318100400c20701c0103213010400140200180442e0500a00c0b9080c121242c04a020540e14251000640c012800c2d81d1443d103c94201c42658180006180c0c103c28142c000d030f2680890000500003944031012154502003401d40341545130740c4441c08041c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 409097805 1250 409096555 409096577
    0xf06030a200d17030a11040308120415020a02070509160c080d1407031e18031b060905062509030303091103030c0c0a1505031303020a0605180c01 64
    0x410124152020316602042040c108008010441d0304125000191505107100442c5000003e16801140f08010045090011204801d003940d00d601550100808032241840040d0040c501000f0242d171050007825000c861515034100340c2c0c100e038881224500181c2105006012608140609607080100304944c81009600354800504070035a03004018001580081c401c3d2001c4101c1d0000d034620341d450001d440301810280030140041500d40c41c115114a51031842c01414540341c072a08100b201d4070100c00b0109020b40e9400c403042d50b0211600c0c03017049071000204010480b144500c0000d1807242000700b00e07074100014001206810074000f520b040d40d82925040300d555000b1085821298982004142c556140c070f003056440c04d103d05000d030180300106002c07400fa90001910060548195102420341d038035648150304059076820701001045040000c41c20004000540101c258007910659104540c90303a926415113400307440d0140181c204035054a6008402e21801310744403400d0130a462022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 409099055 1250 409097805 409097813
    0x20717070203151b0409140a05010f0909032d11031e030601121e063c120303060914060915030f030304080c1c050409020d061d0f06030a 60
    0x60784903866407042e01120007250388a0000e01c0440510750010302e00d60703100e81c6c440342c05134010000c032940c50700b002400c94046140c1720802e1123420706840d5900e89602030242019841c074050060400c0460801460324002c41144d8074a00031603460605007103054440e440d181e000200760060308001c103402500f0800c011010700c04911550700568a46580c82d0b03840e40e940740300603a0000c01307068680f41114140144512020039406000e040140216810082192a0386801204c8862600b10700300343c4103d00c0040d0b22400590040c0048044040c07a80c40d5029282d85002c403130341d01401e02c1100400c0e220307503050104801c0340c000d80c18040840c29181d0317054030381000018407805002d448115080c07810300801c6290745052109141c9100284100ca541341030038a03104001d54014046210240110803416401406004180c7c5180599076142c0b4149824200904000c1d844545103456240d0b54070b0000034202544c0b60281c2104d05514030010240c03422800450800500411851081d007080030030a0000e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 409100305 1250 409099055 409099063
    0xf0f0906120b100c031b030e130207080a0309020a090b030d030e030c1506191d07120e0d080a060605221a03012c070f140c01020717070203 61
    0x84206151114400a444440c032008107000c0b58039580040c03040110101d450380115941e01c03903500c02d5813680c000981d4000c001c1040e4082000017400501e080c1d245034807500c2c081e1400b0381c641c843d003040140b4105003566164010b5000520190200351641d108030150b190071080d00c00285016023080c0100440c03040040d403211502c289000508d81d0703c908500f00038500b0000c4d0341070300c488030b01111152614150000703030048080340d500d8402c1106d8001040d807454443d009001f114480f083c40d0310341c420364000f10580410010208000c100010800d190300c01c0320b5020301102c80131103d002d40070014101c0c9004001c0b4000070403115400d401c0281c1008403170360110484500c94520001500321b4518980e0503105900503600591414003c084e580070341c0c40c940c0c8021812200d07403601d24070042c00700c042001c1100042d4450038409240c00000074030030a000b00220300101910740342c44110761011542c940642e8001841038100c980d03000c80c5100410038080c0c621055039800710012401c0c903515500003562 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 409101555 1250 409100305 409100309
    0x801060507050c0445141c05121509070302090415090501080f071203030b1810151806030b0a170307020411070c1a0906030103060209010f0f09 63
    0x20800c001038498103100b0705001019420400810611181746032070007002e40030000fa10b009880b0281c40d250171094450051105c08041e241c0b0341411945d0100d515101c24115081080900310b0080d040e003201c09000020720b81c0794505068440d6a122403500c08050340314500100ba83e040904000c007040090b80d03e2910942c0c0c0404a445c0147c1d48410314800300c2c0240c00795484070380f041b40401501003942156504203030306803040c40b808c980b0403900e0110703ca6680d0380c2c684511420340c22400c281802191090300000035011020307144200d140c00341d440041031411b0858050701d003450f070319405001400c00d2503568040501d407450058220410703449605480201e81c45484245541c481c403103000c40c2c0700d28030854028090f045046030341c070342403148083d00ca40c030130003049108502d8901c10344031031200e8009561010780c0200490385654144103050720818040d500d01d910616081c4102c05560707980030700460180d440b4910158a40d0115400034000001c804241300a100125116031041c9070b1215075141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 409102805 1250 409101555 409101557
    0x200901081501200a030e01021207020f04110a02010905010b010f020613050118030906090b030c0702040504050f1207020a0501050304080d020919061107050a080a080f0c160e060d03080106 82
    0x1204200c0800580c2d0f40e0703100f481c4601029002e0710a007000690301280340003003240651109406881400300485c2c072510301c032842d26603042080c0880f102504200b4418500c08801034000a103030b624082075059075400c500b1a030f00050b0346828558080003000c3c010001416001e00781075607051407034000079444031001080500c000b0820a039260900100750031a24141440e10041c00200340d181c240101003000d54000c9001041c03803014000307903059440381168400c840041c1c0a034184041d980c01c00010b0217014009444510501c80d8040000c40c2c24084103034861102e001d520340d5070300548103100030301c0311580c001810300a0501c00c02010800328011606052010fa00040c0c2c0c030480040081c070500054803240c0e00000d5002e001150a81e044840c41114540c05000c403400150f480040200382c6510303014081030342e0010200b0313030001031a42c0040c101d03119941040505200c24080d02c0c92521260380b01403520001004070400483c904005e5032034010340c05031200b0b00110f5481c0c074064501030701071040c5c00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 409104055 1250 409102805 409102831
    0x30418020d0c0503010e010618060c06061521140c0307110304060c05010e0109080a031a04111c050906130206070203100605120102090d08090a0e010920090108 70
    0x15820011541120030030404040708201080800b04024400d80090050f1a8199040c00c00451003c4c050013000d101000d00300389540c0c8203808d084044814070112401201c20035110040810709030002c091212100c0001d94031358260454243c0081c0660a280410340341061030a1582c0300c07107035206006180e011100c0c0612a03900e88410b074084500b4141c0520768140b901000c0b07004100142e0110039400294060780003031286a0307980380050b081300c00c0000c009001c3d64040000c000d015009801c407241c291803014000c0b11107201000441d0540e280d0520b0309041240001c0e40c8204901b03e0301c98107643c2000c0344410080d91030200001581c43c2b402070980a40540c0d880700322800c542e5100129180d00d5800380c11f0350350856900c50440082d10007402034070f00c24545120030078502c0c4014404d681711720200510340824280c45460741d0b4001d0740300c5101240c00120781d05001c5203c000c00706900e402840c030500c0025200c1c46024480030604d401d18562406c0d25001c0000c11034680e400240d554104082071042c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 409105305 1250 409104055 409104089
    0x5220209060c0f0c09091507081f0815011a090f0609030a061407140d02281106010605070f0b060301021606050105131514040b0402070f1b080304 64
    0x2540714011010300500a20070b000300e60700c100e030010545121140055844646a0710344040080d11079a484142c051102c041c04002108140308443c2c81d40c11115003240000c50015001400e2080a078507049002d2a80c01690b483c1449680890746600418010842ca03800710070240395400c00d4450380c11060310822505451030303003aa41d00d40403180740e600000d04850016100d480e10001070821128610280581e510028020900034040111140e048240c0246044200030307000000350046c1160758890b268070100da8580c07a0130704140308002a265250004698106a504c52901030140c1040381000402e100e80300008098892000c2880c0d8046601c81040d518600400c0c0203019559401409507214000d080a00c815070740094140c0b8001e0b90940104090600c1c0d0105a900b8074113551b9220420a0080140544100b03509511a90060020400c00b040c0000242a83c206900c1503c581c1e0010074080300b0081d0918a20701d22010010030300c82c0740da140061458583c081e074899450240c0c00304d202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 409106555 1250 409105305 409105309
    0x2070602130e041a1e0901060b070f11010507020d0212010908160b0901020307170c090303041401021c090504020a050405130912020f0a1101020319030203060a05220209 74
    0x1901e000e440c000d010420556550704044880e11401c0e80c0540341848889440340e20040b0144070184180780b031002c0c80c0103d03c0300c003e041000400050a4122556880c10041a504209801055168003498007c90080b4841c180142013070000600c1da81800000c11841006817500f0f228041510307011503070100486903042c080c03030150021540003400000c0010329001604448071381c1c0681d06010740c1c000c50441da90080c800c2d00300e100a6441c000400d4684640c0140e144980684c07607844100001828100300f5031001007461504590000f4040a000d20b8401c021547d0401580080525038500f041d0403200007040600034090a01039503020300c0d0000b811030365031030040085a00038440074190343d44032450420035070001d1411820840321030b107008000d00c000ba4030005082d03410340d9042c4083c00000d071156489071f8006400008042c10360106120518614160303070000140c0c02c07040e440150342c92030043d00b04084a401d0390000c5204641c4801c030f00c604d51800440b1800d0310346440714016619800342d40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 409107805 1250 409106555 409106557
    0x61101020c100f0c030902060702151c0b040c081e0703150b09090106050315090601030f050702210a02030906030702160303170609010510121d0a1b0b04030602070602 73
    0x44030240e200d07041c42d003020301c0d8503a800a400e221000c401001003040c03100301103040e5951150041d50010081c017402015141c800003229071540300e40100ba180241100f503803c070b0200c0c5c0b21004072a50341d59100b041000d0920340a40000b800c80c1d0300e0b202c80c451800072402410b69052058100240c000710001070700c19030281d03020052554056900e0741000f42e481c14010803036070001803400c5c0100c0c2008000203a0a0003101aa80210101010030110301900402d110903148010243c60401d52903c0004118668510070b460040500d540074102c03039a000302900c1e0803940d1810060315010410011000f4656020051301c4070454100c580c2990780c0c41d851412450031380380040ca0813005181c07080000070590030414480080c0200b420900b41c96540000304110796600f40b142c15080500083d45501c00d03407181c81c103101299a4040300140744070f50091000141a205036200c140e560000d2207640031f020b246a9941d407802400c001d400712590400e8600e804a000724480108881d401180b40800c10107030360 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 409109055 1250 409107805 409107817
    0x80403030e0f012403050a030e041d010b040b0303190c0206041508090606030109120c0f060606030b030c040905150903040b270f0303031920070c15020706110102 71
    0x401c0b01d040028241c074107030080040a0b0104004c81c0200b00780c3c01012108004a0100c07500711028260b0703010152010380d811549200081e90040d030712103881c3c0d01603e010484542c501c80c0e8100016405202006000446842d1102e0622035403003401800d405045d142c04251210502c1c0c0780085411102d403010034081d0185412004c00360100200c40105c6940c003402c11449011100115101510751030207042c02c8079142c0e0800740501c0884114002c59501815441c07521030300c54403440c40a09120b8440038100c481039000320700001d80385d01c2023800b1490304010100582c1001c1781d0410420883e552105d64541c8140400070742012040b00141c4444414020303140240516214143e59100010442c0103010700300300d0521a8502c00160700f074542c10303c1c2c0e0b80c116500002a00075071842e117840078802c2c41c82032035880c2010440c1d165003204807a0010070380c242d0b8982240190603929804280303004103c0c0e03040d6400503070921200a01504440341c2c001004c00031036869003041c23035080c3c50380120346001e03104032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 409110305 1250 409109055 409109081
    0x101812142a0f0a03090b0403020607030302280503150118030f03120e010c1101020c100506030a050102070f0c0b0a02060103080f070f05101a060301053601050f1203070308040303 78
    0x510030003107070800715480903030f54420744da099140c5464864551560143e800042d40003e400d201c2170380042c1c0a03030300501041c158500d810b01c445030344a0440e104034031082142000250080207103c0c1c03140703c40f0001842d0180c00d0808881c92038404024031014006c17440081d04034a86070300203000380350050a00960108100009104e814240c0e01c1c098040c009000c1400006402e04602d012a54018802e540b400302180700034025108080503e2000317040c002c0c02d4a40c0c58010b00440742c0000c0e009200500d1103520a00380403a41c540a824a0385c3d41e1303412039010300c0c0070700340403c0a060099800b180b014152544010a03a8171101b80c41e4029290703000d0890018500a0071107007403028084006890000c0c0071803c40b0900c400c0351134805002c2c040c5107100a06400c01c0d8148018041881d1000c40b041074181c091948104440e02e04080c0d92020880000d42a0a5500b4400602c502e09082569000300501510f0240907001552841d40c0e5910071075030040d08002004001c1400c045c481d40000752800310b9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 409111555 1250 409110305 409110313
    0xc040c2001020306010206010e06010e0424030b0f0a0212011e030b0a36020f03010f051305011407080c031b03092404050c060c101812142a 61
    0x69140c085000390f100303445075400352140c04000240c2c034102030481d521070340045e0f407500c8074400030707074217000c050a0406c085032401c3d0390050140d800786250784c80c800b0046019040300f050b10b050040c070010a010001e03000980d0075004010030301054800d00b0449044031124000303411942000c021000c5400d895400c014150700500c4240000403159410000c03200e000b441740140b90403440301c0500941300e000403010b400084c0030314410f805480d0807130000090001c05400072800020170311084044803001c032000c1c550003d504104c181840400d102d4103494034104800c0800505000502502c0d109000317040b42c004100000c0082c207000c0b0301626110100380746003250f80e00c03070400d02030180c0ca0707003402107440895a10708a401040c074141207400b42d0086400030090282d0b500250203011440d801000c00c0041880342107200131445000d8481d0b04040541002c0d138880f42c01d0343d4030b000b10380008000c0d080020040341070040c42000700001d00702ca403c80b4803040550b05860060488446656141141031002d0003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 409112805 1250 409111555 409111607
    0x17031008031305091f1a0c07030f031115010909030c05010609020406170c03010b160f051e06070e100216030c09050f040b0408180d05160f05030c040c 66
    0x1040300d15031040c2e801c11588010300359500940100407690003566444181d2600404006041c030380c2089021990090f2886e030702c0d1401a02080e440d02d0f40a50084440013100402e24040c154003516404a1800810240ca60500e2700c181d1106e02480600410070a1680e0304401c0c401c05001e400a960359030b42c040000e02c0015a502148070081d0411721911000c80e02c0b0b901008541d440c0c0c0d40000d031013a519400030604503400c105115515821104138015075500c0211721401245042d00c02800b01d501c40c0c001054804287d10360714065080c0e00c0da0f00c03c0315a102c0c0c03062000d815000109607100300c134140d4042c0c4182e2b00c214412403800003200c2007082c140440c00303404028800000a80e005480381e0b0714081c4001d0312400e40b1681c400700c0465010300203480000200b0000342c030910003028450502e80e07003000b07120602e0002403e061f00c002c3e012203007544400c0e14605807000800b1a040200441c1d660701c45101e1502c0f0201380c0315500c040c0800d202d9561403080c00c100ea8021484010005079010000c2d074020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 409114055 1250 409112805 409112827
    0x1d07180806090c12010b090a02220806011e122a120507050a03021c151a01031a031f02120705070311160e0403030e0d030c08010806041703100803 64
    0xe8620f28407140120350031482041c1c2184140500101d13160080c041c030328143d48140324100290040700305140b0040214180000c141d6000075140b01400030203020b0810340d4546290f00107040e0404e0070a0040e000c44d504100a20010f0084107402035410129902c80100c040c003000301811650b010114005e044020080759003000f140d030850240d80304000301d56081d40c0780c00401c46103421621000703602c0148c01c41c03404840403d115035140600d01c18032400103007803911700554082e00d1420483d0006484240c003940034039030303141c06140c4a249000070400104a00c1102180e10b5600f444413031402d20f154140380e81000301d00360f411141004000300381c85030395007031000e4000e01950160a00350001003010aa00d6940305021074065007021010414946642c0342000100c20180020415024595102680d044815042c4001c1c01401c12995000842c2c007020070380071382400c00c181c100b24031683c010410000050076240c0000009480e0421068890f80e885000d802d6158041d003200700540070100e101600c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 409115305 1250 409114055 409114063
    0x70602160b100302031e060c0d060b0403032703050c04020c0c0d030207240c030e040f0507031d060903181903050307141b06160204110c01061d0718080609 68
    0x10300d10881c2540e41031345110003044440082c0a80d801980d030401c1010901e5280d021000344402740b402174002c00c4860303551180540942156009401003501171090240280b4902841200112401c0c01d4503035003811a158250390391805540340d4090350740082d120304222030401015114020040c40c0d02c5081c107081c0740c002e4031054244560404c40000c0402c078107882000b002401c2c0b405200395100300c404669034a08613407254416031019003103640c441c280e60301d0b8103260240342e1059001342c40c003045000314140560040c1031142c0e010340c91a08848148108018080304483e01240e1079080080703905ca00d64005560141e0002c4405802e246895002080000100284c0707046406400103100c0d00d01207140b0785440c7c2d8034006e040c81684141409001d01032400402409085070b10030300303600c4e050300d00e540480c0c11144803407031030030f01090301203032046c0c00040c00d00480340500200b03100032803800010151802c0d108009040c0f1800e0248404600c5211002c49100314000c044410885805040600c000c0b525 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 409116555 1250 409115305 409115309
    0xe01200a23040f120308070c030c030e180a06060908030a020a0b090c06070f020a0e070c0b151504030b06030703030c0b04081e07050606011412180d1d0d08070602160b10 74
    0x40381d0321b5000104040d000702c1600000c1340c1c040e200c5c0c1d280c3c0961036500301d84584504400d503a0040d041002001c40c0411064810701c950366416000070182c1c2000030140290070554071540340c9900412030816055404a031020030194000c20a410790f4a9180c1d07094100042c0305103040c4c014102060200500480380d00c16807060f4000c0c0e5002d400140c80c0c1e0b40d21049901d084078103a01184131040307004d0005141e80c807003a42c0300c400400b10f6001e42240d100096682c2044d40e0b000b09440798045405d0081c41400740115820050803002070160928560b40502680411500580754030b51800003d414001380c0c00031901100032a403240c200c8800e030070001800c3d58200d0001518107225030030008030b0303550203880003620b00c00c15881840c0c1824000009444103c0c0024410302c00c04015544402407c1020410b0b0508105240c64149586140c1c1154089085034072a01912580c264500e21000c41d030090105d8507510b40010300507980d5909502c0b004855843c0441c024100d1240104104110307204840c4801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 409117805 1250 409116555 409116557
    0xc27060621011a1809070e0901060504030614010e0c0a0c02030a080301090b0a060e0d1113230c090108040326070908030705150702100e01200a23040f1203 68
    0x34001c001c0403119444c05803090440e829504002202201d240011145a0009003450004046d12880002c00c003144403c0c0d004001043c0085810700402c030b4140034900404d4209411617106601d80308002d401603001819401e4803100010305003142c40d220f40341c3c0c00501d503006821603c59048900d005121a8030903c241c0100c989810400041454a0740340802100d0040e914400301c106440200241e4080303e00e801c81d05030705c3c590301408a40d21503004420840200581c000341038412039410034008440c500011004003080010404210b6007281035400042080ca4401240d58541ca010742d40903520b1054000080c607003060f07035501c030f12440035068480c00d216902d41c0b1100e079a504905580c3d00403014010203641028880c0d41a04000f00320440e440311f098070455080d07102642c1c410044600d00d221010003651208641003900404600c800c1141000d45092483c1411020001301102d2582046410002010194a9040000300152809031806d90034800d91266107080502c00c0c0b902d20782c4220 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 409119055 1250 409117805 409117829
    0x20f070602031b0109050c04051005120d030c1b0305030c0409050a09050c27060d08030f0405011b2705100305091b0a0314150103050c01020c2706062101 67
    0x811909818004e00c05d2440d4082d0080008800700000c20001d490b00070414a100080f100c40001e04e5590800140c003c8000b00019200703808080b200101030300c0512a60000744803111120032210307084080c03011512501803400a40342e803200b03040c46d0040c2c800d507404001c4407420a000c1c0420041c4030f40c8860a0b0502c90700841c1c0c0c84400150034000c001054580b106007020b400300b00aa03800b91200103081e40000010308403e281e00c8a581c684012342c201741d8080350030541e00000c0100f001024070544000b10b0b583c7c461071100e40603403c00101300c500c03190492040712004401407140d40e80403140d40d90103020024030044600e00e500d54020010101115242c8091140c52417070001800402134184e40a20040c00c181c2c401801e60302d0382403c1da00c10495100b150320484c42e070600d0010710900703014040c44c460b00191000c41c41c800f000910308146100994480c5400d40c1d040c1d000c3c0e951280c00c114543c66185a032400380e07039540d00014020702500080d54581c2061400381c00a00b4080303625030303058618100001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 409120305 1250 409119055 409119097
    0x3050909150a030611070f14010522020f0f0310020715020f1b070e1801052818080301061808010c0e012d02010605010e01030218090403020f07060203 66
    0x2807840c0031100d200258001c44110024004100503421694003054004802850410320741e8480c1c0307a1007540d030710650300c0c60765a000c61140c0c15800e00405810150000300095444004030100034100000c103002031050341e03600f4410b035003070311000a00e1061045c0101543e914101034810303070020b5400300384101d61042c640c052090315001c95100741c542da1f01300d10044500f0540400b4180585040321000402580700d600c200049490310303003c4c00c80c4502001c40345c070b0201d52500d1016900b0b403800500400200d250701d00300981840400d90815040451024000c205201c03111450580160040005000c0b0071000001065003034200c11503140208103012030b510302d969030740a01c50032150210907035400543c0603100c0d2900c03503201e01000030a070303541c0c46c0c0030b4500500340b4107040c01c1e480520088a405130b516150100031560304000601c040345820308081d0700d41780200c561607407541801000144216040004101031510800080b00004010811100d9594450902954035081707c000410761082c41c141c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 409121555 1250 409120305 409120321
    0x30b06010e03010509300c0c151e0a0908120405010801050303120403030209040e010e07030c060c0803010510020a020a08070806130809011110140402040b0306040f1e060903050909 79
    0x40c2846051280064406d4201100109061038101082400e5140016918a40da03459000003890940b02030b0005108007001e9409101c801c2103184007141c10f04400784099a40c3c00e030340000d1810f07111122100b81c0d9882c045108192408000c030741000320b07980300700c9001c4582100381d000240240c400c240c0310103807144e984200b0541d80784070354100800c0070752603100403400090107900a49841503006101241164a15407000d003111174064281d0b11650040d401003091000151612001e04030910302008058030f19100c0d03107107a01c03062007032501401030402100a428824801700c0051580200039040c6907940755038441d6200110f000c0d40e4414002e260100380c190501001c01240d440e0300050f0b6504041468005544070614003105001a004c3e50450904240451080001a80c6006105407160034540180000c0300e01030210a0b019a0020040c0004906c00e050075107162644103003049802d042c1505441d01403846400d00910aa041c400624201a0440702816601c001650303a00724698400038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 409122805 1250 409121555 409121561
    0x21909060f090e190303090c1a0a0f0503010506160510050c0c12120106031806050a020c0c0a0305030906070c080d08060910030201093302071802030906010e06030c0a030b06010e0301 80
    0x484d00d9210b0501008440c00a4040e0304900425801543d000c2001aa90036130550702420109802d841a040013408440c143c0d0004a104445072491070428250343c1072401084140c455914100880072020130304200300401000f070807401205260051199040c100c00b246950380040d18040c1e8140103411700880d85030611400e03a000d81c5203912208015900c0d103401036004200d8206559080c40403c21b140f804516039024090044807400e00040c3d45001a1032158200220304d9001446007501d00c004101207980042900c5103418100c1f10113a480100307180c00e100c000a158000640381c000e1102c003402154000c401581301d0201070329803d440c1e030380d20b660441d0307440601d0000901240a200b401d101000410744810342542140c2c1c089181c103072030048004c100012110412005a00680f000e200c149010f860004c80300c4ca50070740c190704504080e41510381320141401900070403200d9000048217650108001050000d01a00c4008a1900c90401882d40c07001140d0282c0070405001c080029810144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 409124055 1250 409122805 409122823
    0x50d05010b04090f0c1e05040903030f09030207141f1103130e040605010501170705030702010221060f0904120e010e0402030a15051c23060907030c1a07021909060f090e 74
    0x1181041403c7c01c0410004000d1032000b941050742d00c05848407a010310744251026240a42c00501b4450318169035210341007001d20100d030140240182840085004030311140750000c150034054125074941d600030740b0358000c8000805520719030b03900c00501c4030b201016581c000c07806107000380156a00d030300056802100702c94803d0124141d0710001148244039001845d0845038910015107041c4112040345040c185c00310f01d14002e80145c41c24000303503181030082944218025107103107240d0324041d1114042c081c14904010207004002c0e0710382d88130307a1103200300c00324100700104115241e05126483c03000614524509030300101c40c541001c140781ca13015455084030403440d01c2100044803282d5910000d0960314043d25403646d0140d400030108a000c1c00021300ca5600c401c001e010341455428400c035260110350107003440c0943c29a0410f940002c0608560056406a400a00f400d000040344041a07000794080c0c030343c003460720310045481100343c0d42c84d0040310780c220700512050001c1000c5039100c0c2148 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 409125305 1250 409124055 409124099
    0x607030c1407022d0406030501020c010b03010c0207090b010c1a07181512020906041d06010306032003210913140112080d050f180a0c050d05010b04090f0c 68
    0x2640032014800801506140c8506040740d80c1e182d0360728101c0401c0031b540c0c66820440362a50040740ca010b60100034480e25a655000b14000d1200d08580c007400b0751182d000f03018410030f480e2500d586890a900500003400c0f1079510030140b8005031030203600d81f052101c2c143c42d403a000445486180b144c88a02403014030a580c105035000c0d01c0c007907100005541c1a2074180e000d182d61502444921640c2c0d980b0b501500c014503ea103000380f80c91900200c0c44001400007000d140c141440c01a00b0b102054003c5401441400301685115900a040000030325250642032482400b0000e64050780a044480d4041e1100c01825503d900c0e111084a820b0010740310107468545504403510010081200e0b4204111081400b410301c081c83d00b00400b0211054500880c2c0f000e540541040600201d082300103521050140520080c1030401c0c1300d0b5441e8565a0614800e96129100c50120003051003801e620400c902c8074006e00410280004c1e00d0100c4050500c04815130303042107000310000c0c3d40701110541c2550100d00b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 409126555 1250 409125305 409125319
    0x9100c05010e1c030f110f0306100311030403050a020a050a050d140c060a090c170703020a0504020c25120c170d080412050f072001030e0a0b04030e030607030c140702 73
    0x10781030111300819940e901d01118035204c00d81240740d1b02c1003000030462203042400c13440e83da140a50074001200a51000c10040516140c1401c00c042c030b800055907000395261a125a45040c1d01004038a007140f1100060264026801c5400801c200040c5c4452100380b561155002100c4e1801420707410f0044907444000b44d001076002440c1000d003a804103545a1151042080142d103600d00030100301c00c6a070051790554040d0200b0300c03d51403e5100c60009101c2240d0940c940320398004143d444002800300e0380009021000030522000c040f4055802901c0c0b40510425202810304142d810b00707000303100703a030482d09407007609402203000401c2402414a49840d045c01984035943c80d1940c1d5600c903942d034400c10000340501440c1400d1080101110307806002050110030980240203030750320629840740d06040c90700481428040010624500082c3c024404060342d0742c482c1015a6482c2914a0003581800b4040800000b5170300b5a114507041130031669a644102c5107900212031520a8060180d44004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 409127805 1250 409126555 409126603
    0x90c0e0922050d03020301050418050d080711010e100f0b15030402010311040602100c080702070e040602041a0d0c08060d02041505220b06181509100c05010e 69
    0x1110340d490703103500410700006889161280c0300e882c00c1c0225140c409000a40000040100c2d28190107012100085610303600380b07151080d514580d40300c4003071424005000100307000500a50240c0401201c4244400080c1310f10401024500c0e150508810403011041c13030801d00400e010001e02c140c1c2442c54000e490303c10583d20a8410700071642005104034105601d9043e11040058000081c00050400e90018084000d01052031001d03920103206c074000b00f0041c803003042810303075000072000c0c2201c038140000030362510740d410720402030312960304200b14066a0300f160450300794060700102001480d8000800c00003119034401ca46042081c1c0e10f10341c0c08078100030420094546030f03001c107400e07083c0c3c90b1120148a07a80e1b00880c060003600c0141d0041400c0104980302c05030389900401c80c0360482200c40324079000c400308039061041041300e20180626108410212006020002c03280d28036002044200d0384c40c0c180c0802010a548680c00700c4041d400e02c950405d41c0c150000c1e40c02c0b0401505031050340102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 409129055 1250 409127805 409127821
    0x605010e060a260a0c05090f0702030a11010908070822080304090b0d060e03090102121c11040306090c210b0f090114090703210c0204110d0213090c0e09 67
    0x40031211181c0c0c15490400c01e6480c458410400f0740c41131485041d4105a641c6803108010040c10f00030800704001002004004800d6804802c581c80c0746c000b824403540303841d001c3d0307500c5005151002c0028440307070001410405004034000038184142c100300c426240003501100e10b180414041c89200714961040c401408003110326009840f16510240400569000a454040594000d100031042c4c1385c1000640045950307041c02000c0e02d03000c54016540c601100c0b42c0d07500241301c840c25180c080080d078464801840f1604c9000300d170021a0041000d00c0f2000c42c9042c407903480b081a20805101c40090360254001001c2c2c10020322340e030780c0c01c84043e15640e41c850031205110f5800070f0403130100b55a980d680510400a01603580e01502c0e41000403c2310606501d0041c7c03400c3c41041143d4102c030300407204c218109500818540f10350f40d0548001c0b0340c66030001e01d4105107000d81d148004066001059440d402e40c5148440c0301150310400c03040c00f12400408054920182c4e180015400417103100c00181c2c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 409130305 1250 409129055 409129079
    0x105040f03030305180a0b06031002070c03080306061308031c0507020a1b090606050909090a02091b120412081b0d0e0a0b390d1d0708010204030605010e060a 69
    0x10040424900c103010a00341171a0404200c900304992180300c0809008036418100400918403516080c2189811500d869411036504203210040103928004001003003622420140c2e070320395040b40342007940c4603244c40348140c0f207801122b9166040701d03403050038480303800003801494000d012130740150010301c4442c3c036000b03882c0c1d01c400740003425000d48100010b2400700c01e200d07540c01030036280d98003070f01c2c0e1030b01404012070300d01c020b44040e100ea03010715006000750382e550010a81100c441d04604405070304500482c10f81e40501c080e00a10824424104420310001c1030042840700350382c0d07a40051555402002c4849a014522903003910320741070000200d10111a031101024500c14011500d058910b503942d140f54220172604c0b4901c020115034608001c114091010740308100c4502600d000c2c403030b191402e1985010340782c410050161101c105560302c1461400050141c00017405580c40603444040c5e9902039880f5100441304285803000028400100f00d800a0181e003001301003007001c1d4500f0f8028102 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 409131555 1250 409130305 409130311
    0x1151e0c1a0112060f06080c13140c0703081f0b0f0702090c07020901062c220c0f030515090718030f1406040c06110f070308180105040f03030305 64
    0x1280c880100125000350003a4000d1103404410410f400b1140f500105807084541405845810311401b03200c1c002020070000c4140800f90b54564420090102010140c820007840f0404140346109200301e03519850004c040301802611110840d4803168000828403010343c0c0c070541c035899a08424854070a6050007000e168546100e95030405801d50005001d00905403003000d04644001880350450801c6841140100f00d1070401051000300c801d4a45031030441c00a1191514100f0b07000c01c0f03610364541946451504030468401c078140c41c0c682c40d0000602e140304a800c003140d501c109292000d0b02c24002d092083c0c01611140301c1c6241c41d1814444201c07030284c041001e210700150340b4909030000c1d0300317108015070107400483c13204a12804d0a000c1300c0100240d215140e00414100b001003410403103900122240c41c41c062143d902c031b51650780d00348185d19400c01030070300038244004240542800034205c0844503007129802c2e07041d0310380151042d214500c51044160761034502080440d000c1d621141d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 409132805 1250 409131555 409131563
    0x8071e08060105090d170d150e060603100e1f120305040b031008030a0201090c0902090612040c05060d090203011503150e0a29060603090a080304051e0601151e0c 71
    0xc0c0940c190b60f1850345d0003000c80c01b01e031402000702d85c0c1102c2c2550b501503046a80c4041e10b0b07000c03c2070b091184e5070383c40a4000301818091800000402e04960801c0c01510040009410100403410841d9a5505103403e815600580c0f0902e001c010aa1268560380f0401251341915602d16051800d1401010303900010154500240107890000e84100300784010114000380754000103030a42d4038540a07284940c541c01980070b0901c10701c072141d0191140c400700d42e601c0b56000054140e5569a01e850303a203c0c0d119401160304503034089a040b0614031035170030440c03070f1074800c0300240007101d201c000412005509100150608022000c03e4103900385030313031040d9009131600b41a280209500d46a0301c019680b4800c08240e025642074620251002500100c2d0300240101c860303600c2c604000305095500d124002002d000c5800000200b0b082060410564018401d41c00811420f903110546a6440708824820540700c140b11400302203007a07118000340e882481120700541d2102800705070440c0c0320030030000300b11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 409134055 1250 409132805 409132819
    0x50a03110301140709170d09030206090d17090a090b09070c03090b0a0801090509161a0409050f01170a031b0503090d110f03030f04050f1f08071e0806010509 69
    0x1014a90f0420218403800c00c5407100080585428492948054000e0049141d500003408003900c2070341c017106000450b03404840313194484038808000340a13007000f24001030928241341c001c2d400c2001064043c1c50f03051808c0f15044209a03540e030f60901541c1c0b14141d040e0340b00c0001c00024207001e00503524000d01c0da0180c9402002a501c4004800d0385520040b1520003140008004000d414040e00034071350300c8039170350b400b030090494003124800308a0b5150203503848905c000c501c2101c0080d428400d0f180145080b881c14080340c14101d01c41801948280a08248400001c2c6283c03504540001e0001000707503d640c440c240448992a852403020407400126102d02040094180319a01d10002c002e20303e0240301c03503140211200003001000820402c00b540242c00038004d0011300c0c104503050300c045881c1a04d07c2c00c081049500000c0511150a039140388400106010a032030b9a8404409403203542d4548403084010b11f81d0b10301030780a00b850b81d0f00c240090178100004905500c0388001d4802c0080c0a042d20f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 409135305 1250 409134055 409134071
    0x309080d0203131211120a020f1204140307060509150702100905012319030b0307030f0303061a07230f012f0a11070b0f030a050a06050a03110301 64
    0x44060364070558142e4840428940700f40103001206a10f0030140e801401c2040e145042c5400c1c3d07035200c000c2c08400781c0341801e012a621900394004d0080548540c00b00d403e46020078440a0180d00b02c1d04640200e01c01c01c1c071007201507002c0d810001280c106440c21511a141410441c07020408060940715203540c0341e0300c05128000c01620b80c003c2988512410f070311030001840c10000010720403009030050303002e41ca1041e80407003410300030304048550082005d18002249109104203801404101a10941500c90034000005115460099200041c401e503014070aa50799030604a00340c1449c210300180c2c203070003005004d0008036445c4503012409100c09952155410001c2d0043c00d10b20809900c0450380d454620f40c2c400307207501c0e08010743ca012b11f00342c82030310324012824060824042d40c0a02014042c130003900c50b40d003100800803640288201340560356200040d10f00c0e0391043d0000d07200c0c0f50003a0b0811300070981c0d548960040105441000c0c0c50700f048640f0715114200588001d11106416558a03101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 409136555 1250 409135305 409135327
    0x20a200703060c0e1801060c201228080a11150109020c07080d0c02010819060902180a060e04020703050906070302010c120209210f010501060f0e040b06070201030908 73
    0x24480041600d8464902d4018050140622034504170303610a441c54000c1d00601140b900100200100c58001010601d00701522a68041c440c5035007800561100500c9100c220321200000d0710f0901c107918501e81450340480d088842c03195124440020b040c001e0901c61108000d1141107122065a0080101c072541c03691115003041c514130a800064560340c0000320314800071070807c80c0c00010000e440091803c8981007100501c18244418000d0400c024403022900795a43e0024001c01350719959800c00c011682c940b4100300030b5001c03081e1203403020b440c558502094940170010408480b0551030707400c01140c2003070402c0000d502403041241030080a00a66201d41c94070005800094032940000818186603507000e0030740c811070403400c2055801081070010710f4a0384030047c418502001284003d520781c0c540c541d800c003490711203500c1480d0b06e02000003621560142944180181c01c1c0c81c1d22500422320700038030003510600c00c3c0040d000001004800c0055219900c0350103454012846c0c9810300c006402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 409137805 1250 409136555 409136561
    0xc0b0f0a0222060f0e0a1e0801021c050c1e030705070f121b0c12061e06030308010803250f020a060503010302090a020301060807030e0106091419020a20070306 70
    0xc60038091407490300c14821590041c1d18005030080b507085c0101c00c070078181c00003546c082e2640101050b1207242080000d1021600f07590388040c0c03180d43c6c0255140d082e032008400b048921010040820f90505004c204e0703420071001101c00d01c115043c0d2648510310f620b03000e2042c5500141660003082010465400800d030b004100e082e070103200d40126015050880d60040203004c2c3c2400c0c60703943c40c02800004001600d00e1640d9400c03100c0100d0803c2c280c0d10385044c000020459a010b14207103e40c03500c19000e40180c10340c40310017503d11035103c1c000e00745d072660f00184d901d0141d0203110210150b404a109000407841ea451010036104034200e2403090415800b14002c001182d0026021802c044014070851601e981c2e00c83e802459600c0450075903143c62030040c007548001d0402824181c0d01d45942030410001e40020010b4103000009100f0b4501400e07614030700f450f003100d6100450942d069414407500c0705000f21481c82e40c041c0d980020307043d00e201040803110003084420425100300140040092a580 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 409139055 1250 409137805 409137847
    0x105091809070b0a3c0c120f1707120f090201080705090307260327060703050702010f090806070518030f06010b0a030f0f020405280618030804030f030f0c0b0f0a02 72
    0x4c0d449410000c41854101940e88202d04e008048c004c0107070b803c00009030700404400c02d13107a1024000301c0d992140310044c1d4103030460314a0000c42604018020701c065042d0380002002078400c1c3c1e6448625910782000719441d00810005a80c15045148208040c203101d0740c1140d545054804401c00000d600301c0d04910f158401140c000007039000b40c1c400680200102681c140e03030042034605d9442c1c540c003964010b240e485803000017410b0125400b510110140700b0440c80c0d000d4040c0034202e40d4a400c100310054110781107000400454048440104a6800c0104040350048001c60061106909164107000070307400c090031341000c00d42d440d40040c400e805e03907000310307010701044210042c1d80c1e0f800c081c203108012901145002d4950000d20b6260440d18000201070b00b10742a40c940841009140410310b01c3e80ca80da68006016500042008024414640c0369049898400c0d00c6448415906840c1070b107200c1c1c801340d4041d0900d04100300280c0818070803491281e01c41d0700020700500d482441d110880c0000240c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 409140305 1250 409139055 409139057
    0x1020d051608210121020d0305220b04050a05011103030f070c0c060905090105011707180b0705060a05010e1e180d0206060103060807050d08090105091809070b0a3c 72
    0x20000400c4244200400743c3e540d40307003e1011794401c11072074020030010814454014200a00090003404407000c02c00c644c020384245110103e06d1540d9010341c035226400c10300030030380701e41030012001034a5801401c0c6030140c500d185004d1821940da0454040b004100200507101744400c41e42c8000028800c00c0d0310a0242c10702c2c0c1c484c004150305000500446010580209061221064403030b0485401180340e90b41c0524507190811251180b81040050030b082540400344262021409004004001ca10144102c4400030704000580ea0f4a07103c0c1c0c5164001e0f601c0840c2030454180050b0000e03003100180d0380c424814840c45101071075a016051030580680661801a00440284a03166926001d00001003070380c0c0004000741400d0000241c401018140010515400010b610b50664000ea0503510110001032003400244c01e03010000d82e12a008860010303250080c80c1e4081380d01100d12003515802c0310325036941c6502002801403200071192000000443c404000f40c00c4ca044c0c201568201190100b03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 409141555 1250 409140305 409140367
    0x13090b0d0b0f15040902061605030f07061d07180b060906040306020304030f020615280b0a021005040c0303080a1104090c0e1002060c18040f0e0c01020d051608 70
    0x2c80c1c00c00b014a010404071444c800d50501c14081d025940341000d0711400c25181c03004800101c2103241c43e0340780d032262590418a62401144442c00d005003641709003c510040c03004108511300d0009056180e50260158503801d00b444c1d00003602c804a140d0011020440c05099249441107510008a180c0c100354000c48180750004201f1041607072115956446000c00c1c0002e144c01d04002c178a0b190851010340d2594010300f415103c09034038a2041d066180900a8140180c441079101c0c0305000da0342d44002d03c40400b6105100c07085420301c0c00c038420548120b4200412003005c60441e40c040b50144405001d0050242e210001c800b80703225601d000380000e01d01c0c000300007140c0503801c8014094039150100c6520078507561390509a5a80c0104070075030b01c0007034828143d0f5070b8124162402c1c06407002c01d6015400624100810400801035845611200d003841d00321a0345c0307030740c08004998841d1005c1003480040d40500500585c2400c82c100c9824030341c41100201c0c209a02c84c0092003030ba01310207441ca581411 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 409142805 1250 409141555 409141561
    0xa0c02040207291012030c06020c0d0219050d0507030c021203090415050643170a020703060e03041d15030f0a0213110d0608070501020313090b0d0b0f 66
    0x96034030b000c45a00781024451020780c648101a140b2903032552182104002045c95604200342c030424560310304640c81f40d011512a198101c0503584c40151903045400340c8191204114104854082340603036903400002490302c400000d20441c0d40c0c0d00103150807400d00041801340c100698070750901207824180c500c0215240d0154400f040b069550103c1303501e500072403200080c04162134007000c80b00741c1040802d42c0003440c10b00440c82001807042204401400c00c1030602c0c0070b0b40003403019600821500842d44180c6a41c811590819584a122400000750303004d2802000007410a80025925200030803e583c1402c2c0d440000b941c4c12400020511407500d010303001c2161141e0700103084003800405500414a4840c0401600d68070381d03921001a2040c04040740712040b40a043e044078070320301e000c2186140c580280c02a42d40107859035004040c107a0044501c081800d501c00400d55504481e58106403600307070302c1c090207003000300b0364511100c2e000154810710f00702064554000c00c0c040c02005d48601c60500d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 409144055 1250 409142805 409142843
    0xa0b03060c0a02030301050d1a0103080a0305100e04031211121816030b040c0314030306040c0e060702060c0102160302030d0f05071709010915090204151a0a0c02040207 74
    0x18000302004007051040c4541d1080e1540007064906690040c2c400c900c4880b031500f86100d190003800f0703041d9502d1b0304280c000700c1044415009003020048075181030185031a29140c0e03015804681c09180e031203110503c0024042485481140f500418035000066980384010910b0302c02e901c40700c50f0410000c5110140800140c070200d101d0800b903040c502900300f1505855102c05000106e100c058038048481c1e011409220f0280007890007150b10400e29010340c80f4516070152aa003044800da071040c0c0c5420380200700300b80601c0c3c184400c244000c0040f0b291900caa400c0102030741202114046a66081c0005128101044000644035019030021a110141c9000700d0b0b05035100c1c4901040180d00700341c1400300c01904102070310801d0300500802c0401340d48240380315005009101019045c035112140310740e881000d50303200c20503450082e41c090116810b03000ca264404c95651207001e10803010500550090351101000d00320301200c903d003c20840199800040680e040260162485400034040013038179 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 409145305 1250 409144055 409144063
    0x310060303090504020f0a050c01060b0a080f090c01090b0a050d050708060306070e0a09020a05120c0409110702100305040f1529130506030102040b0403061a060c06040f11090a0b03 79
    0x104804c40f4103501c0c110b20340381545120300030344001005000300450702c0340b08a202900158040c024440780a0382b0384541400062029800742c81c0c42c840192454003084107440c021480e12043c410603141e100c0031910b0705401a40a900070801542017140900803e034141510303000d2180601d0300c035a00c40b08507003401001c140c10010041c06c440c1c00d0115120740c00045855800580d011034001020050719290040004c3c1c410303115626106980d0850f4008010303004a1540c040c1050b1040c1c003408001045205c203000c41203205001010b540101400d080c4009244260080c650013442030b80d043d8400100707513507500d954000f11568022804e4440300002e614060030140f2900e001c10240507074002c1c2020b1000f041c0f80402504881e1b01d942e4448000440d00c0d1400d4048400130648007000c80da9076940c900340714005108030452092404802c010000d454a810010349800400c0c00d005800c140c1c071290b94241c2900c030203400c1102e00c0080340b10464102e984000c40d0a1007a1f56881b8040b503c0500402010700b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 409146555 1250 409145305 409145309
    0x80304110901081209010302040306140a06081501050405220807050610060f030c181e14061c1e0c1701120605090c0d030f2604120e031006030309 64
    0x900d1003140100b01e01c0c81c3c001034501002001c41c0480760f41e0b0710312000480c01f9100329000504400e04000f080f004004000070003900c220114030f410003450303031100740040d240c0320084400b40b10100100300610681c6440d0748482e80003101980007401511407681c40c001803603000c101c19155100d012844000b031010510003a50300c05000014903034254207080d0090024000c0e10303603032810140e5035038032421340030301880c3c11485100c01c103181c242c1d00d1550f552040c0740880648002c00034100050300001217409843c1d0a0508940e001031503103092090080754100702d1044821140400c0c0c0e191854045001c07100004041d500c080340d50702040541e0b581c0c8000e01120310703046007160303202d0444004009022407505500c08803984000c0114690712503111b560320f0300301221089503001507172880b031004064000b060a0200c6446445981300355a0425090b10014071b07008000400501000006d0000341c1e01007406540c0c01442e04180e0151510100480d290800803000b0401c16951004180203064002e090540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 409147805 1250 409146555 409146559
    0x2070611041406040e16170c1c060b0a1110050c0702100f2028030207080a0302070501080601180f0f0905041109180a0c0e1e040221030708030411 64
    0x13240924040c0030200c3c88500a0850176180c26000100242511804004490f161454490030f40c500b400411080103920800d07601c2d505840001c5407500034a414096042202c014044250a1040b00080cd80b40041618907100310350240a10121004849200d05801425031070081ca031220098410301500c0c0d0640350f41c4006000306040482c0b00135502660310528040b0080401900f00c0101c0452483c081050a00070105558030781905809445010414195030190382120111540c4851903922140c43c180003070010380101e00203006070750180d00050b8200e50185080c800c5280302c0c1140603004011500481e400e41c1451108200b80051000c41c00080e246510040219003029910520040d410410a5025410050005480b0300c2d141c1c11661008502409458030000c4030300c0d04400c2c034022400f0707150441699401043c1040826488036094412580045d0107a80303494080020541d5620f02072000d519000702000c1d41c55a052000c0c0000601c42d82e0425101e05091400c5494004140d85841c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 409149055 1250 409147805 409147807
    0xe0a090e06151f12020d02030a0c17160c141903020105150901050d1a180601241805040e01052403060f0a0f05070f09080601260102070611041406 64
    0x2d02c644010400c00b10240d219814130200135054000b81801901982d090301d41030314808020002c42c1c021540100c0240342e002c2c0c5c1d84003c0c8000f0a242e94242000070780d01c542d5482a41d1201185090003a1003281c80d081c000c0c441c2d8003804040b0070f01203140aa43c0d1016100c2c004241c031541c010141c09000d00380d00691000c40180c800752403800440c3c44400140b08843c41005589005428006110b807180e200d280c503400312003d00d14100540700c0259014040042c201d111300c0d000003805501403401031560741c45080701000c4015468074102ca0141d004580710003020742d90322002456644074495480c2c10780500e00041003a180030600440030740035021840804100800c102c4010381d502003201940403055220580807500c42c90100303030090441c585200d41440c030303100510200c1504190441c82046256588142c40b5403101402c540b135550078030481d400c20407103004264941624240c14003c00f40c46a00060808407a5100c0380d041e03403180c01c4d01100d03540c2d00040502c258a0211403003070a80d10f0603140c0c0c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 409150305 1250 409149055 409149079
    0x1e020a0b07181703070305090a030203010507350609040c0e011214061b030c0904061409070c1122060b0a08090c0303070809180c0301091811010e0a090e0615 69
    0xf0684030300c909100103040100024010711141c1e03d04440801664016008200d0303858059405071013018502100204011114055482d0401d01282d200c4456900b0301d2001e4140c072581c4c14803400002c003402c1280c1c2e903d5045000b00c4c02c034540c01592030007400089910705040c0018107104030310400700b4075050742c1034005104214641c0c2c4145400c0608000a540791a50f0790341d0f000d111030040c05031f072894030b43c407600f8180001400c4001d0140665420001c50380448141c89200044d40e10280320070300140350480309401c10007580b400f5512280c90890070302c2c42c10343c0704010710445400c441f415000607608640c0130803044000e591211065074402080c0c401030003c4042c4d80000307940c0f0300500c40000e01c5a4000504005d10303881c1c02e00e82a4441918032903000306400c102c401002681c00c00d0160502d0b55142c14048244070b0700026828001ea50071440b41e0180b43c000000441d18064070314041c1e5042408a10b0008040c82c07240b141e10b18245403440505142c1c2800b2105841007500303000414840d072091000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 409151555 1250 409150305 409150349
    0xe09060a0303052a07050f300304030209091b03070308030114040b0616050c010c1104020a0c120e0906040c1b0c0504023103031e020a0b0718 62
    0x380d8400e40750941081901d6090f074803050b008405100c200d105400c980d468403039a41c120b000071000151a0111160150b000400051000768034512011000740c507071001441172000241c00303070050583c10140980349010344a8011984648041e81e01e01825845929050340e410740c292450445000102c01502110b8a50b480d0700030940018010b0380100d40d0b4100c0038024590302d13079011095040c2c0142119448003603400381401c4807030040106481c1e0b4001c0e0269a08a5845402c01d40181a4007000c0c00074401c8812061000941260f114402800506410741c00480c501800ca49101441d5503501032040c41600305121800310060000c1e070061b800c1812a411151308145050040c0d4028013030412041460f04103c17103c407102d030f807099420910000b060001c1503004545451500e00d001414001c001e84034401b6135000650f480040d0010b0f401c0d111503110100c82036030088030301e841841100c3c208100ca0f141c440308282e01fa201d1300040f610602d0300c4070881c590b80149100401070a540f50844c1c40c18003032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 409152805 1250 409151555 409151569
    0xb1209010516020d0f0207030b090604050d140f0c0c040608030a1d0d120c08030106020d1b0f1502040302090c07140c360106021e070609210f060c0e0906 67
    0x400042486100e40b1007003040c910801c8544011600850008150304186c11000d482d20bc083d102a50180641d40c0b0480095026694031420710036110701282c6491030004550016805c141c03602e00c2140502c0b0401c1d03c1e10f655a00958001e81002c4000d0340d6aa40001005404c86114a045070190f9007401d07040606680c603450110b0845411490050146892000032580f110050400803c41e45000c4004690b056002440c076803400000c1d2188a40103900302c8124180314079450300102800d0000c990b640010300d0421014150f226081d0000d42429107960000c0e450103012118059003010114480b01405480584101044c420a0207040c0460480b00440e1000300c0901d0700e00c47c1004200054001502341c2e2007248510442c0100341030803941c40d480000d44400031000c9000002850080840010401040540859071a42c6a03540030b03034640b074000306001401044120904c0300b41c00490000c900107072842080d141c8215800603440604c071002601c00b181c440200c8d03005e0075882c0c00704081a00c2e102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 409154055 1250 409152805 409152823
    0xe0c12030c15010b2a01090503041d01080721050a08180d020a050906010c150606110d0203040e1b13090f0e0c30072405030712060b120901051602 64
    0x3180301c0c5a042c103001d09000464102017001c2041e90f01e440b8400051010100181c41600c4140301d140075201d071940d800554040b000c0c068035590350015003003003199489008805c81a1000007107070101001c115116103040c411004401d4925400000d9a507184404803082c025401c10300f242c501000007040c0e008a005190a8024540a00410740100d0102c2e805050740701c03541c1d648003842060320900f032000d443c00380c100381c8a6200800d1000e04074080c074010100e40c0c00382c17208030390303000b1400e0902e00307038003c0d405000c00b038a00342d503496000ca80010780016070700090510800f4260300c0025180b400d101c85048815201481940f14a8821145442400841c441c070000c0da041700e80d90b0214454001c0c07014510000f01c001c140b840c0c100240c182030203c0100f02c510840307242203048401032002d04452001040b404c494900082c1003040000c0e4040e020707070740d000d41c00300da442d0001911603104c40d0300c3c1f4901d0f84000c500b0142c42c2c11070003c00030820800d00508d1350100c0f81460608003d0014000170f9940c0c4049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 409155305 1250 409154055 409154077
    0x20301210f0209041e0606030b06090c1801050d0c081504020c0a034a0301090c0506030916060203070c210311030c15041b06120e0c12030c15010b 64
    0xc0f00204040c042c42012146042c1c82d803100d0050004e041d460040c1c000d1246101c00c84000b00300c0350005010f4648900510700c5400d01c11261450500f21400c2e0f0698402d1800d00343c4d040c46010b01c5510084000d40c131803e00544130070345802c6a24201116044442c4010300703003052041d4010002c0c000300c010003250180d003c2d60706040c8111000d00782c0d03030160003403980040004a03900800c1d064960840c826035074005039469030b100d14078101015005141c00d031200750f4000303441038900f85400c20030380c117112005550042885055074151030031800c00e8040e9402960103400141c2c00032420809024403e081ca100030441c1703694003d01024141e082c884141c0300942c0117814845601510902400140100c0c3c1d64007400c44151001c544013446101d5402c0000d54060b203100070015854010013682c2604402503520036180c040440c200b01e8102c1c805841480351a4507140142a07084803580c40b040c101c861282080c8020f96140d01c0d030f00c81003501e420b080a0780c010340b40052000400401c0812800c65280c9981 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 409156555 1250 409155305 409155319
    0x120d02030a1b060c0203120a050408030403080613092103020c070506072402130801020a080a0e030c060f0403141815090904031107060e06160501140901020301210f02 73
    0xc6042207019441e000c000f80c442401c0000716616154048020009060030a5401c00ca54076000c1c0801e00f103500854004000171010400315000c41d001d88441c41d40001c00070a10032484c07032450002425035424100444031010301260501c00020030418504140c1041c2c58214102246c004e6034a543c3d10b400d2080e9801110002150001c0c015140d494180c011150120101c101c1040356a0100035440686c0003040d820f400c04000c164000103008940c1803041c2542c0d041069100c0c074902100600c90304500fa002884100800c4c1083c800c28440a1f00c20107440034910344078682400e0281c8240c00094500f0700d1504100300004400c4030300e80c5803c3d041c1034203580b0744614000c1c0d02d403114011300c41c651074154800845420031040641c00007080b01c0c0300c1009001d84080c00e40d00d00050780c1c0e034440d40f986a039001d0f00501440c81482628070070103801c50300400011a481c54940c00512840308151000111a5000001808800d90b401078041c1c10117041c9600000c04a8192170798881041040780c000c2c8500e0b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 409157805 1250 409156555 409156577
    0xe0c0f030c090f132a05270c0405030d0503160302030601020607080702070b0d0b04060503010b010203090d0606050d03020a11030604020a0902030415020a02070603050108030f0f031e040f02120d02030a 88
    0x11400c1324107410f42c0b2204500e080c24040031203141c20341004c0c00c1880e078001c4a42d004036860a2218402c50040c880100d03944d40001c540700d00690380700d8002c1c5040c49a081c24000042c0c240d03001c04c07208d0f00d10490760311010340e241051034044200c0240306000710181401082130024690780050460741c08249850080e2107911445070803418144c86a0014100c84004560500a038040e6172240e0b078004400c460803c01c4568170401d15090ba00701104450241c1c00620114515082031003a00300600c0c89481c00041082c0c07a040005c1c031150302c43c503050740103034400c40c02c82e42044040e40c1d500700210004ca00402c000e15060f40042c082d90418001c0301c90241c5c002c000704040010310803070003031540c109020554680344000002075442406214500001b800d0100005041402100b114801da40c0d039000c4624000400075003911950000d882c21a941c0c464180303642d501620442c44a0245100d00c0710b07107040b02c050703004100803001c040c5250021038018401414440c0c0d000002c071852110a810100d50480d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 409159055 1250 409157805 409157821
    0x12081207020c090109050108063907080406020a0213020f0403060e0f01060b030a2a0c020303070f0f021005090f01110a140303010e1003050a03080a09060e0c0f030c090f 74
    0x100b200100c1c1c02242038030020504040e1508014103a404000840d0491365603009500c2059035840000644a100c411041c0703903010041284050b6403681031151480c0502d2a0344800d000d9020741d006000580048002c0b1086142c206e8203940c80003070904095003850403e0107100841d20440c400204025618403218000c20800d11420920070507010007080201e0780c0782c0904c48030394400c844036060035147c580b20084035082c01c451540d120780e20b4134898417919043d42d02954024141c05050382e01d44424010035000400508058042c60b01c5225240d0008565106010f01ca4041902c8101446028001c21045403034040c2148210704c1c0034a00000219400d817952428807103480030292007910545464880048008000c42c1201d6420042d601d041d5154640d903a942203660100600d160014404103002c179100d0318585800190040340003032080c0d455139404080300e244c0001c80400341c101070060481450102100c10000c1c10039405803103102c0050000445440c03000301040c0850180320b0104505d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 409160305 1250 409159055 409159063
    0x14090f010e031603030e011b080d020f0406051e09132a020604021206040f0b04050111030103050a0501050a050105060d020304080f0c0601031e030c060506040f020a0306060206011208120702 83
    0x584040c1c03e8501c04500c0000000c40000140010390124410780c843c60069403140703040c00c001928000b900c410821403961002650780c0800c08015801d81c090041ca03944000c0d6000800081ca081d403546940d404005500005285041d80000303d03441d03003400001e800b070300c070780b159542c2d803916402000030809507008040080c000780400781c8503002c41c1c241d014070341c00b0740005816001e24022115544004041f00039941d0354201141c0c01402032440d0f080c4840000d206604460f0410320034400414280e010209a00964000360300548a9a03c4010441d0600c0300c207124003074000c11644800d200030360500c00410700c0340c81081c8000503000d900100080c140a01c10003903900c0c1c13850b0858655076510b41040d00541c0d0b038000b0302054030b40300c2c220300c8200310310481c50701c00138026981a1a002d50102d581e8407600e005103401041990441d841b00c801d60454a81c070f100411289030300303490020320103040000c0207151010507000041408800c040450101d8054015640ca02c9000000c0c0c0d82141d0b41c5d944200c1c18 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 409161555 1250 409160305 409160327
    0x7020c040c120b191412070302010c1b1a09190f120203070e0a0e0f03030405370803100b180f01140f0702010e180a15171501050114090f01 61
    0x10a03400044c0400c00381446140e1103a0000100c40d020840c1d0300c02c8440b940c44a02520000707020480d01240500001d4608449202a412801e014101a541c82410040003503001c2490301d402c50f00003801c01d8040ca403002000851050307010009014905054544500055500a8980d806ca00300707081c0045650400904000e040e41054808042c2003004040c4040d01000ba0044902c3c0603094100b282090008103603807084e90401c0040c46440481c1040800d120344c040e02c5580b1441c4100c107840041c90380d1a029507070140c8180700c0300b0b5403480c0c80c407801d4480b00302a4003c41e021700c0341040100c200484030b180300b040142c001c0710740301110f050a80050b1582da5a25202201001c0045040312080b65000c0141c02c3d10742c000c0c2c80d404441c2c50460104043d0804040d009030903000d0300c0e80810b0ba98040c0c0d5001158407801c1c503545000c81c2d51101c0c00003087d07a90b00b40b2171100c1075002c250881d445200a0070b0750f40c01000c0a0070000800c201d940341e004158080d0045241c080d4405085c415880da00c6003d005e07403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 409162805 1250 409161555 409161589
    0x11010e03032a010b010f0e010804020a0512060406050114131a09100302010e062814070605010914090a0303020f0403140a03020c010e0d080705030f1207020c040c120b 73
    0xc804481e410804421445503242002d81d528040c03140c44d1950188440180b10782d03841c0d4600d010101c0c140b0043d0303950800540240d801442d031210201e001d03140d1a414803c1280706000a20040ca46403401e0302c25110141c200704405410021701c0c0400d52110180001d280401d40c1011030500d6162190401320581803829907400740b064003c0c4070042503281154000c4c0d9000b80d031440b032003161481c28405207206684007080b4003c5482d07965422000942da1034a40014285014601d07442c41c41070301c40e129000b50905407112039541004010304d00961203038030440742101c0392008003031a01900c0c494a41c0c100b49406000d141d00040c541e103400c1c0e804000c80e03010715803014140710b989820b89665550380f140301a084000d44100315014501c0c3d07004a8200c110030b6001000070300195031035581c00c0d841b904401d20841c1d45220502c41d04a000d14102e01410740390310615046000341c036141200070f00c0c1c8200003542e80c0c051361608414a031801ea101000310346c804250350300030076858041004903000c003920554010b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 409164055 1250 409162805 409162837
    0x24040807020a0b1c0216060b01022e0b0414160c170705010c020106030c060e040902040533031b010c150209010906090e01260703030c020411030411010e0303 69
    0x440c0400c007007400341c060b410401e1211000c1c3c0d0280100f0408074806c03001c07401c10300c0380c0c880c0c1c550002031200d41000b10605010f10607228041c00c80d80302c0d0905181154000312001c6072110440500e441c04d44200055840115424455102c170389440c8014800050074460624021886030504107024403040302055600804d0fa42111a04500b081c89540103503c1c01c9a003542050100051144140901300a0303035007040d0040c060b60703d017107007c1d660042070803006504680c9036036900015035078070306c5040d1196600564030000030700200001300d070007551420244580340a40360480c0068500140e6401c48070407444070052038034030034001030399941c0d183d0200400d8950102c0215500080c2500a40035906c0203803a09404161280002e640d40b40c05c0d4050000c3c83c1100200400000400d18035003584042041260403100d80d42034075041c2064000c4d081500482c0c40300e22000d0840c04c2910a070326030310940000150450802d5500e0080d1812461030aa041200d2071040443c1aa400c0c400c54209a210b82862 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 409165305 1250 409164055 409164059
    0x10e061e1b0f070c0834080f010b01090e0f0a0216060507090806010f0b0f0d090c090507020615060a120b030109031701090203040b0a0507030b0a080c0f0324040807020a 74
    0x3002c180d40442c2c81225041442c0000080011000402d928056003d00c0c0c03000c0a03140802c0c02044468051000440c040746880c0001032405050000700e10f09203920001003603151003000003410003004c603803280090700540c908214024000082c641d07040800c5080143e84ea200f03251090041802ca00d201401d010702d40340070301079460341044010044a441500f41c2d01c460f80d846282a080400c0c0d40304110b0802810801d1414001b9551300070300410303002060008400c0225100c0001e841800c1d0000040981d459051200c0b040d010880b041c0e108000084c20545115030750041003060295940080500102c05500c0700304c8902d5820020721500d018008200b04601800c0c01441c00c60400c28003e40b941500001141c50700490080303d02c2079400c440c043c5031039103441c0c1910009102c0101082c00701a82c5051f81c00c100d80c1c2c0c0c1204440244000c2000f8442081c0d200100000184a0340003c0d22940c1315000103c10040b00481038001d508072903900c15a03039940c1c0e003444c2d40c081c810881c0c0290f001018001c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 409166555 1250 409165305 409165327
    0x603020703031103071e0806030c0108181e01060503010b060d02070309170106210b040b0c0c01050c040512011a040b0f04090c24020738030603010e061e1b 68
    0x4400081506e4800000499a61380c02d41e0107960513201c141d01a08001c1d084c0c24154041c0c030086800c80c5136064070316400c01000c03c8003814400b808808607180310b81c150007000c4c0060240110405023a08a0003003040107510300000d0101d06c01e24040e0320b4580e130086441414540101c50f010020008549004a844070b0314031041d0007000c250080c8104100e0300e0200704000d0f074544140c400c00940c090a82d6049454603200c50b61815001010400c820301c0412a0145405082c06030501400542410301d49039401d00d0100684015180c41c200340d0b030703032400400354003c00c100400c2c10000003003618002080b20341ca2012030b91a025160000d5082810108100c081001c2d41c0c038124200c0d00608071109c4444412090700c1ca005949416820069000d150244010f1b284003400ba80c0444407030810012a20702034040056050280300ca40005030f20100030820241001c3c02291068503d44003e8038540c50030784092020714000c440f40059502c0400c0008415100c01c0002060488029991a84440d0301000f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 409167805 1250 409166555 409166567
    0x31106090a060c0302310f050927030a08010501031a03060a1e1a011b211215080607020a08041806120804050406530705041b0801060302070303110307 66
    0x6250320200032046c0000841c11500445d10045d120007c1c10094261102c0c00e07444814480c00058001e0001041500c551158042000300681496500c4900c0558500310005d021989514542000948a4a80104242d030702203451030703121483d0100084c400c2058002803425000c13003514146018507009030000c49916245482282c1d45003680c036001039a9600301061821404010024050f59080c90740300c000c4c2000d03446041090003107240060b90784510351281c405031641c00b0740605d030000c2402000d1090260030700c1002d45c8404180021300c1c611010340e881405900c26840303500074401c420803031402c00c80d08507040f01d070085c402035000c03082c10720a41c00c2541e5140c0c0b1900c14548120b18001000400003030000803281c4140c0342d4060145442010403d03900c0b10b0000c1407041c8281c0c2142940c0c042c15204d0305078115088203806005203099406d040a000481c1d51414010380c258601480ca018010ba2207801581900c24510300541c850b1168074054001d08004058050994804810008001d50002d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 409169055 1250 409167805 409167877
    0x3040b1f0f0801061502010e0316080d090b0f071803020108100308070c0f08070b0a18031e050118020904020d03090803040e160e01200a050a050a031106090a060c0302 73
    0x4603d500175200910016800c90f00324103070800d484d4009000a460360a06241d80759140e50050340802d2030110106440c0044030048842190812a05406c3c003510500c0f0ba134023254000a2818494001e04110340d40d0150081d880c84000c1c10820400c0006030b9602e2115203840003907510800e0b5a40342e2107179150042c2121414002c900750302001500002d0044000a2400212031400015928040360840c0480c1e0480042284854034000b6610000c0040c1450740a12000d100341904450124014a4101e00b907a14038070040c40e030805040226005079451401d043d4101c1e038101d40051458a1031301d02580c0c020b50981c480781050001080001d040500001201d1154100a005203002d41f8050001d4921003041303900e0900207040c44601002848040381c0c91200c014080c4200d400110455036500c1c5000c011080c00c40d41600541880400c140d084000126808110009400107103031009549903100e620f207401078019510f51000150b03141c0280e04a451544c5208945886802d80d0300c4205080c00949d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 409170305 1250 409169055 409169069
    0xb091c050c03120a0c060b01031b080712020337090318090515040c02031c020a030e030304051507050c0a140709060f23060703180b03040b1f0f080106 66
    0x38a001a1074901107101319a888507194940f110060455252203000b402d40d458154145542d460740202c0542c00941d00c0c0c0c000300350942c3e40181c3e526000d40000d00020008454000081c010300910070f0343c080c81100300804640e0300f003010500b08045045007180e00d9031000c1110529241c60400f8080c036501a51008010681c200d11501113a900d00d15141280c508986880c0c0030010b0044104003860030703400c10765207407405104907801c08484000c8240640c00002c0c406000e1907002806640843d058000d000b91000c00f44055070451400c2d0f01c1d0304e500e540556500f140354090003000109514019000da48200710140100c4029503030302d00e0100c079070310b80140c1d03040c2d000e10400d031f40003401600034001c16090701c25060482c0c0707000c0d1429200340310b800200707500500e40041481003400c182e140c1c98013405446001c0e0391941205088000e0080125000707800c40704035260b080040002240c809202e041e040000111240c484500042c43c1780480e400541109112003510000007400c4c031015088201941d00c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 409171555 1250 409170305 409170313
    0x1005060414240d09020f030106080106080c01020c0102060f043806060c120706020417030315010507030507080c0109060203090f10090c15050f28180b091c050c03 71
    0x120b601e10a10702a4004161003400c5820803020350182d403150003420540d44050041015082601e0009007942c150340c2000959070740d0382e901000030310810444040b2001003030010345001800728000070340301c03000103103031002c030081c0da03000b007402c0000209929121454004044503038407032a81191581c0c072800003e842030000483c0c0403072076615008045951200c1d491004052640e07a180340309174160444e00c4241c0d461942444009200d419200c920800301c40d500f0080c44d6a0f240946079054880042043c890400100f07004010000f604013040310021500700c0d103100d4441001201290160410710f02c028000c0c3c1c0080103215090344002000d4000185020540b078001500040c44400c541120300b002e0300078099003c00704030806490088010110307851601a140140b109415582644481c03803949541807031095240100720403c07850070000902e45441c41120324280c0a110387c5441c94041e443c508403000485201981c0c1d41c181c00400704c0340c01301602c16141228246103803103103800e0107102c1c003c3c05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 409172661 1106 409171555 409171579
    0x130201110604060603120c0c05130902040903080a06050303091e010c060c08190c020703060b120105040f050d08010308030a0b0d0813060306080c06040e1005060414 72
    0x405902c0104d9400c0c90361404210313000905540104000340c000f00800061810100c807230442d04101e50703422007821440d00c540020007030303450000d5000f8940403400040681040e000b5125102c80201004034541e9401495121b1183c400340b1036000d444c4d99111160110f61080d02c899201041c074110400d9112603580fa4200c0b4140c1c00c040010422140801031540d40b030700d413900a415200502405002030840f000780d80c1e01c4540c08002d000c00d46821000c90961100a02d449108c0380d510020b2041c0d04090170000501000d0210545079809051007820819006035040c41c1229031142c403442c03950307a803071064200030161120300e00d500c496508450b41c0810200c1000d020103464400644c4182031400501604448081d0310407800c0d0b0308541040d210907680d8809132401c8404500ea0f890203903031504c000c18103a88068201a034081000705011840c00d508009102105100b500c0c2030031168 = true := by decide +kernel

theorem cover : BRFrame.Cov 408992805 409172661 := by
  have h0 := BRFrame.cov_init 408992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 408992805 ≤ n) (h2 : n < 409172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
