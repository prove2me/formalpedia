-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:34:25.340701+00:00
-- url     : https://prove2.me/submissions/1347f054-48a5-45d4-b9e2-63407c499cf4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 737589928 ≤ n < 737769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 737591178 1250 737589928 737589943
    0x2190803011a03070219061107060519020901050a0521010b1308010e1504060906020c10111303020d02010c021020010c14070c0e04030309150501230a08011a0102 71
    0x6805082e8514144142c00960f1a0300742c2840c4007240480c20f070301208222090b40310844440014540704c2e1560010f0600d000109004c888c1505404c0300c4401c201e5041015108903100300d40705840b05410205184412503464010f4104589022000c0380b401d5805554894440d00803c0898850b5030741d240514032448000c0450b074444881e5038103006d12004540c0b000300d1035544405c0d9103008018555518101200a0040ea84001c1c007690310002e624441c0c02804100c5258141d5402c90a002052030010684420f12400d0302c248072205966206000500c1c0c10310f4010304140c0141f520740d40e4800c030703900003c02010000d1000c101003220880510b039a4101d49a00210002144000b0050308625a001a1039000d074840c80c0030b0085400175280381040501d400510152100c030508840e149040d14000c0c00804403d80700703a60540c515640040c4000c01030080a0513a2146900244002c2c40384050004841003070030500d0f408107003640041040f01091240c00407107902ca141c0007040e0f10b001c01c006402c0840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 737592428 1250 737591178 737591219
    0x130060e0c04141801060509130212120d0b0102010f1a150705070b0f0408011401050a0b090a050603070c0b0f0f131205030a02070f0605100b0a0c020607030219080301 73
    0x102849580c08070b5900e90f03207130360000c1000d4141c01000c107403210b00390040030141c108962003403c40302404500b00000c120f4001da54400c2c1e640701d500e00010404907941d2200d078074003032401a504020400b0064500c1d0440c0c154800180000310303213102080f02c8003098490791016048080c2c40c03a003030306241c2d2500c204020325190217810758038a40710050321004e450341c41c070f40200e51a07000c00146a492440c0c14604440003860604001c002001d02c888103041000000e101d118452a02c030200858054400341c00c98403010340042003642030038500b5051101c01d0300010040410312996064241c08034201011451080d400800c80104c90324002910729401031b40078061002109800c48000002080807100d010281d5444c10401d0300c17650380490000103407143c1744000780315086240010040003076a40082c3e00441e020907503403044684490500503513018200880000446034141c8101500308400148250fa0203132060f41c03100000740d49803020340300303004800b00c0d0503000c00001008189042c80540e000da64 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 737593678 1250 737592428 737592431
    0x40f020406120b1314101505011d09092d0706210908090d050105060a15020309010c02040204150903110105130e1e1303030b03030405090130060e0c04 66
    0x4240d110903c03182d5000300014000d140c984900c5050182c000014800001d51030200d4064904181c0e040380a06044121a000e40c0d81c02800450258040c031207a1205080100c0d4401c201500b40c010001c10701c20160000c070440c080e4030b640022507503113541110204200740111031386d80d2541504681c500284d0768809410482444140e14004500340c1c1c8102139580c443c0c002054514142c2811a41403281c80d10503544010000441070400a06400c020b100300404c0b6541d0b5000c990354096042e9040304c3c083d0020050b0001c10440d0810b600442109001d00d0000d4001401c158440722403900e605003070005940815001e0004204100c80403070903a905100c2032814a00f403515111032403114403010700605c5c6541c02481e00181d24a96100540c00d84032480d052407801c2c5040c55448014280c0116000b0b5000034200540c4440c00c5c10f00004403411a000582840a01da180200401c0714005102c103004941700682c000c2101e4104ac1c106032a6180d005aa0001c1c0002280e1101c40c0340c600781648860199 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 737594928 1250 737593678 737593709
    0x2604060215010e06150c010c0e040c0f0504170c040f270c030201030b0d050604200a08030a08091204080730080f0405030105040c050a0b03090d050d0603050105040f020406 75
    0x42c5800c02504140c09403070201d43c00c1030752040c0101502400a46d000c035580380c4103509410f26407140185540e1041600c0412078416914811180c6071406500c40001c40c0b01003204008443c0039040342e840310440b5000b680d10a0203074000080030b50f1194010045500e032640c0c404182d000e41c0e5090b15145451030802e1a04114060743c501c00d010080d4400a4141640c44c0c0544c0e1258640d60b412544141e0320070140c4500d032402d45006448100c28040c1da264001c001081c2c1e81440c20700840810503990391200440c200310861070104d5180c0802000724441c0e004080b0400f0740b41c21404043d00150800e400681880c60800b21640100024071241002d0620080b20790149030326041041658039810617051982c0f9040c04000321020f01c0356901084d0950310b06001c00050091700348a9009641d021a44009060f0350350303a481c6030b02d000c195045015904040604090350b80603400624420040c0b007008501255641c48450031901c0c1240c05449940d4a440070b0340840c5403d10550b001742513501c031480986c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 737596178 1250 737594928 737594939
    0x605060d0c030e190204052e0305120a020303040b0402031e1029040518031c05090c01090612110c0337080a0e03160311060c0d09260406021501 63
    0x11340a034030740042e00903980d801c04210244407021024061079040c000300500d201c2c89124144183d501840195402e01907080c00c4d03003058a42d8002c8861480440e4004d40c21070b242d60310340700c2001c2800f40049905204420407000710400b412529105100804041d00c000da8241e0015000d0707030003403505441e142405104102c10901d6a2a0001a0a0050301c0009070390381d90103000d043c41c104035103e414407071101023403284000c2c00d500d40d49805e21404c42410721043d07c0c0c05107829610340e00c0c0800c1c18041420b00e2001e0206921034414142d0130410508049415904031050700201d52108801c0e41042d040010b0085134039558110100c050300c070940300d52a12251441c040381c2840213485640003003000e0700f8003060084213142c0221342c0120200e401d40c1d03901c0165035003004a80003600b40880120780102c1107250301c0d0901088580c4200043c1403c40d24010302c07007614038020720a000b0101d0b0b507560300c0c804003201c0c18a0b04035819040f041e080c1203c1d41d00ca0074600d000c1c0c40c02d268a050920100c6440d4010f122 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 737597428 1250 737596178 737596213
    0x100e010f0e0c090d021f0e0a050904081e190e0307031e05030403120f08011d0414030d050c0d060b03090304060309080c19060f2d0605060d0c030e 64
    0x1030101080c2e84458940d0540c10000d00c00c0884003102a5100554924084442445041e00c1d402c01d4103907102d56032807080f61028840c2c14895881880e41c450003860008012541503402890b11120b50941c9401c1c0d4201e00003203141c2030304100d50701258500050f5140b0364154000141e40c00c000d200710001c200151460362400c03030100c07a1030590031075013020303004500402ca0200b040c0d4016680c80403c2821042003104010109201408241c0c0090600c100009940d2501600c0094034080a02550031a40d130b9501c581d60075026000c52441103101c100b0502c9401c0d0017620555014025001d0388a80d00c404404100b03094032520381050703c4143e030810510000800000844e0300b01c0d9400c0c03c021500c518242412035041c020310505e120305003c1c01c48400c0611030702c64140e00c007a41c811001045a07003c0303081da403421103103440d030155812420000d44449201040c1c0724650b040e40c680d0300c040b800f1512840452190340011420400c100d0b10340400e00409500f6000e1801d0285c00780006051814042e0000351 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 737598678 1250 737597428 737597431
    0x60607020a05041a04060e0604180f0303050402180f090d0905010c1103160602030405041d060a0b04021308010902100f05030c0307171302040f150308090a0905100e010f0e 75
    0x1840b569442019004105138480503103416400140b042051664801d60000c404c042150201d206a02d4030342c030141d0124442110f204001c0d0070040e4030819008235501900200070182080ea444003d8403258000c00004d0902d0520829040300e20b01401d0414a00031803401298011210510144010521499920441c8417a2071504241c00120800c2040042800c048580c00c055800e5880c0c0a008100c480d0000014070444074180e40400c20345c0440b00390b0466819030444c000c5800d8202a020511021058001c1d80321031000520040c80c0500784803030b410015915500c17681c090394540480d142546000320100d0040102804c001005900d860402003540c400144400e0203d0300200103d0301d05403040000f240003001070345949080382405004560401c800500c12403003907040c021070541605941c06a90400065240100c40a0b4290743d0780a2094202030905034010203440c800203a016018000d40c1d01500071469810002410300800c69002441604110b0317080c0c810070000c00c0410400215203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 737599928 1250 737598678 737598689
    0x1a0112030c080f1201080f03182e0306140f01080c071a0415050721090201050f0301060507170412060b012102040801141335030a05060607020a 63
    0x100d0188840c640101e25000d48014400f5410f000b240c3c1e40309590120000342d0580d0090b4044039103000083e2142c0c0c0c6c0c0c901c1400b07940c40b0f05041e407842d003144500b4205e11004041202c5640b803d01800f00300440c5000240c42c400e5480040c0e00e80d44104038203c0f20042541004c00c0039640034a4460781c40c0d0000c0e00c40b50f0080d20000d01a140054140f040c0006200b44091550700002580304034209418005070300b801c80d4198107805403500b0040b408490048100030204d81c0384950305403080340e1006d4648028084184223a050000c2081681d010740d223150021400b90015840785512103440e400d0400c22a281f1417041525014200800d1000002c10200340210369404880852803400120048485000d03034a814103800300c5150000c80814219000b400544154000811803029204074040c54944152102c8103400340c050000c601003030715005200000c1d0088070001c4081c900350320740c900c15490714a401c520b55040200601060010380d00410380c0000003126010b0038017845400240181c00e492017074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 737601178 1250 737599928 737599937
    0xf19020403080412020d060f0b120d080f0a0f0f0903140a120b210c040c03200c01060b03160207050a03081c0e1207290412140f071a011203 61
    0x600c0d045540300815520187c0d4814400c0c8070b00c04402202c403010b002c9402d040c034800c91a10446c0348840000080c0c03d03540203003e82d554442903c4403400951040d1000c1c08507203404c2d0315003070140110b0071a400f8414100348141c1c00003d4407000b0b0704008042000016402e203c0ca0010002c454000d82c1c441c502c44000540210001003c00056000a02e580b55461403064149060b10f00c0380025200810780031480c020981e002d001c04030020a040b0125900304031000181c0d1025203520000803a14809002e0074900040001001600c503503d004194008507a07424a00312003620b5207680e40d505002e150020300e400da0750402d043e41199a074805a005500301207c00311300002100c19900071907000300c40b8405210060300d520110109260079075038491102550b010f42800444042400c00e80761440a110000c0d05040301c41c1c07580d0317540d0340c03030b2500000340d042c2081049204590403000240040c07142610790b48142d55904410b240a030b00084041c100359200180101c0100202c0c0680d29980345143c0c0e05113003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 737602428 1250 737601178 737601209
    0x7080a0b0a02090d0c1203080105030309061209070305161a131e0f0f03050f03090612101d0106120912230c0708071e060f0203070b0f190204030804 65
    0x482d01380422130b00d0240c114100883d0006851025000d015410b5002e90313600180380e82c80350300f03041e038a114000c40582c0080c820054104801b8840040030f40200e0360030252400c1544c0e80d11000c0c9000c048400e00394220403201410400706155000c03010841d5045109281050f07900707101c0b41031a080700d1143c1d038004d28008480d082d00014004007207010380107036004000c07000d4513040202914042400211018400d081c03c8860401c0004141d4a5a0b0f000800c414a0072001c0710340500e4a91001d0044107004064a0002c80c010294030540308a010418504403e00d600d4076100401341e1410310b440200c41c6107041808000314100132a51600240103040ca01c213180011a081c42d100e115080000c50450008649280e605401280000496007140e0845007156290045034007005c2200c00413078080c4140503001c101d142d0040d0140b4016407086e005407801e004541c2c40b2166000030886d00e003822410380200b0072a0082d590405411030b01d407642e00450805040d50740d015850f100c1c41c0140940a00f0200d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 737603678 1250 737602428 737602447
    0x60f02270a060f02102901020106050303070303090c0305030c06041a1501050a09050306010807030c06020706090e2d1605130e0919080301031a2401022a0307080a0b0a02 74
    0x2044c18808110b05c0c404001e05102c00c86a458060040e09502d0b440301103c498042a56205010322026154001d010307601d403651079a020b0300100f4040008841d1600c0b000300000c0460002c0c40030700040c00942c00a0601407802d4a4910880b403008041042024419002e001c182201100d03500e05204003820169035510f00c070710095030384400680c48150f142c42004004a0641d401041c5001100d100c2c1c1c2d41d1075440d0b40c40b203400340d0302c0340e0346030048030005415840c5c01c02896034512034440d000808502d000030200c1041c0c110b0341d0604020107510a21744510018428001194120101c60820502d000c03428500f20b000108105041481000b0b030002803800031407940042031000350702c55a408021000c20100074a07000c682e64000344019143c49880300300c00d800464010758032910800c0c038a10b600c01c0e111080181009800c45020400d41184038915011510066103041c1741484c0700748441100243c1443d84c200761800042d9045020140c1002a02c100010a01d10860350820f03007445016803119200c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 737604928 1250 737603678 737603683
    0xf1804050106020a030e12010603080d0c0807050703030911310501140d0501140115110309220b041e0e37020409140c0a03050c0d060603060f02270a060f02 68
    0x50107c2c1c005540380c8240081000040c50050899898405081c0100c0d00920015504482d08407481c80100b1020880c50300000d2281e40450b01961103609610003e1081d4404100c4141901c1c10002c0130b19241500d10448018038011841040c1201c0014003043d81450384980e00081204091802600e01c038101c13104106086d004030380340c02c0155001b5102581d460001c10186c80600d0500004100c1c000c0b821054008080100c0d4011200030303080400032a41c0c00302000e0700d84c18000c0d4032555260348a901e0a819a03c41c040c0703502c14440c810b044116101115011000c0f80c44801e0600625840140e4002320007a5010580d81d40343e00c05003c00d0000c2801c440000c82c0980c0345e1000950092030721101d84104003180e441106440c5145040360701203950391081c40380081d00c9000140a50780088441c0480b450403034001420310f48140e0012481b150f491307a601096441c004100c1042c0c03a0081403070091220020307540340c1d442d074841801c240410341c00340110380000c0d141e01500342005524092005218000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 737606178 1250 737604928 737604949
    0xa02030714060d0207030c021905010e060a031d01020a090519050d081c060609060f12051302030a1202121e03060f09090610060c0803010b0a020109080f1804050106020a030e 76
    0x40f036410341d9510810b00c0c004029141d0f19000720301c9101c503d580c402c8041710715000300080c0d58060316010101d42c44202005010b4001040c9003007019210740100070300c0204c50340c1d0b802014645200160700d810700000060840541ea4215038040d240c00c2c10440da400041109840c122501600c0304514183c46080c070380c2c0346201700045040c0080851100c585a070320240c1c0803004490b096560040d425071200c8007180d404103840c01084c00100c121070343c2d030400c144c0f5a000940085903003641074581c41c002c2d400b084c02c1400c000744c1916079006c0c44060040450301400005003400f503560b580d41c0740401d4910320907050140c6605c941d041d004080700040d003e465200c52018030580042c4041980d280501405588501c101c9441d9880c80e000400028421302851790160100d601c81c4d8581d09580c24039031611451303002000305104664030b80881202003803083d0000c001c24483c0d031200c1d0f6a5501e02d0442450401210402d1a0095207007400400141d940411702400f0943e052030306c8a0483c900c040040c041150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 737607428 1250 737606178 737606197
    0xa0e0c0d0501022104061802010e0103151502010e0d020d0f0c05120f031b0f0a140d020403050717031303120903020316050103050a0209030a0308040501060312030f0b030a0203071406 80
    0x141d42d50550401144000c2c13910591180200740131700420000707058400411404024086051407940c42c2c41503009812207068000e00c0200342e1009a99001035901d0810507c407000701503551b4042000c0000018460903504010742c0c0000c3c003031100c0c84030b001040304c20b480d543c6100704a00c1e43c1595040100c01d12084000421204240d41c546503512144c084951090383e4160305080f1019030864040c0c404410780e040103c0011140c0d007400e1000c00e06079903042c41441c0c111705c500001c01180b00c80d910244003030000307980507000030401e0905048451031101800f00c200c620691045c0a01e404540c04144d011054130760040e005004175025400689030801c0b242c00080d818002c40c0452107aa0081441c81801c488090340d0601050712001010422440390042558140e0081c3c1001c1c0003107401801000d0f00984110700010310903589880316407003044041c40e16800291509500300b5455014060b100914500310b020f40403007803050780025503030020761141c0c2c130b190350b4540c14240740d9a584500380c503000103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 737608678 1250 737607428 737607457
    0x70323010203150f01020703111905060c0f0d0804051b03031c0c02010609051b0a0c0b0403020c011e091401050d1a1c170f090301230a0e0c0d050102 65
    0x40c00312000c609205980031880c0100c4d01c0d589511240d40c4002401c1e02280d03080074000d1640c4040c1d800340200092801003003c1100e00788400001c2c0c64540200600e00d060100001e0045030301d440ea00da9040002c103c039510104644442070002040e404600c00f089e001c401c5106c0c54011810b003010034123500a00c0301080282d200c03402071401c10301d0382d9084124054050b034020000301d5152401c10003151429200f200000303001c0010091400d0029000300002d603000d04205041e4412a5914080d102d01114100d0050f007180101a2003942c01020403c4d0100f00702045a500320807441c0000d021a105200e0681218070001d00e54800da40030340e00300d944401c2e81c038105200b584005400d0b0400a00e516030302c94040c402c881c04a01d020403107894410207081d800300b5501504e00401c00800066001810858183e01e402c20900342c03980c4d82480380c0044038202003144030b00d50310441c044080c0c800c8014101c098907400e09415000702d00000c40d070504c00050844104202c4d611390b04005009024894540c00d048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 737609928 1250 737608678 737608681
    0x90318040e10090303050c0f0403081e040914010e090a060b0f1201020405030c0a240e120607020d0f0c031b0c080307120e090106030504050a0b0a020c0f01090302070323010203 77
    0x10b4442d40204101d01e01a403004e0055894000f00e2105d18482d0042006503801d090105100155412005000c4a040aa11028402c030302e84072802682e48261702040c503d90342c2e032003d45e102d00341100044e80100000148050303103140013a212526070300c404000400550707480d0308418040d540c262000340040800390140035090a01c06109000b07502a0250303500c03c2c4200501d040e60713813402694030b1058a442d2503a9404260888142c001c5166082b294502803000c5000c80041c01c1d11051905620380c11120020030403800c01c00e90190a00d04400030400c1041540100c20300d5150b041280c6207401545441c2c85049a08207598100d00700000060040200c99403c07000680035000002904c0c1881c09060910021012600190f40c45003400040319000f113011070040150500a0340300350342c09400740055541c582c0b1980e64000b1318610072201c0c00a641d90100c3d840c03510400c10059864218100c8000300014601510060b644041620000780400c3c034860010003114403141c0d5407140c0740c060074000e545a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 737611178 1250 737609928 737609953
    0xc16050d05090102071a1215040906051f030203060c0c01090c080618010c1d04021902031b060906010b0705150c12150d060209121504110306090318040e 67
    0x50b41e0000003100e005114010000c01e0351101c030503149001d0500395102c0c41c68102410f81e07940c0701005c010002107070344000b0303090401035450324007800c402148200d0340024546004410740d13448031200300280c501c1c850048401d10040e140001c0240e0820302002c00c468460001041450260807511002011850000000111020700141c40790042400c0c07000100e000d1488600c0794201d919030300050700000d40b4141504010220b0580c2120b861030058009450509914400341c2203440b1a500c0300010b80c00002c102480351410b00b50075220300700241c00b9100b1828580034060b540c81060042c000c012500013581c104128003044800b1400c0c0140c1c04544107403502140b4a00f4a400c00414840e21804441c0001c011000d02c5c0300c945100301d00104104002019925030000035040030400c680c101c05100200c2078040750070080700c2071804486c0400501c602c1d2a14103c0c441d42802a04107000c0da012205000ea40040807054403030385c8120102c014900c01c00c01c000034000d440350107401c0700640a4000076185 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 737612428 1250 737611178 737611187
    0x180f08010204080d0c0f021507121107150c0b100f030605040203010f0e060f060103060b0c03091503010308041e05060d09022107030803040804090204060f0e180c16050d 74
    0x2c440340380064901600b5034030b030152072541d100f600042007000c035461204018239125081c0c109041e5406501402e106140c0c4e039074900c582d1102c10b00e5004c103100100c800d80c1100108622000390076420101c050100300400c01070b022041c4c0c0e0400420304a0030030300042e150450b54100070000d00e510050301240e10317074034240300c07000708016181a40a03501300b000003d1103603214007500d582405200000c15095803032440004c5c00c118042c11180c101030700e81d540050b18180105c041c01445070072001440e80c80071544100201c024400460102210f001c0c270041001c00d1a40382039070221404408140a005070040351558503071019084580d0148000c51030b4440484a940030710140d40c400d035011520f803000000c0940c00ca02a81c3d1452a060303101540910005d0380d941d000c0c6801034880e140180c2001d40f10b0001c80241d8110303030065400036407807034440e100030390344004202c0d006141138580d03100700181a1020b4054050045c0011074000c0e00041046410b00d880104110158100040c0c45104a25450081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 737613678 1250 737612428 737612437
    0x2031b032805070609030303051e04060b01030e1b09060409080f0d02090406031101180311060c03090a0e061e010c2406091b030e10052508160e10180f080102 69
    0x20b0000c9e103032a0000c1c1820905181018030000c0d040d0300700c0c00310394444d911880a0004040003904144d05e40e01c00080100c405c012091403003000029401460024200b80258000014507041c4200e081140301d001180c0c104080b501c004201c066010381d00c442d03c820080c0a0321400f130302160014504200001401545150030440072402d03601d104504881101c03101c1c4480d800d00000e40740c101407103109589854048000d06c000906281540c0c00c0c404a039000501918441d80f000030f1100e256403c002640c41d2404a010324006484401c2c200100b5450000707000b4541260018102640400c0c0c00343c00320300000b100071460300b980005100f40c0d07403107005620150010041c444101e81c4507089000003140680502c1200152341300040812030103011142014080142180c10a46440c02c0b60b002100c007400032440c40088544c07a10300060400c010800c041c4403140c0a100108100507203280119642d02c00e00204890b0141f518403d106240c000c1c000e0501d080358840703104104c0301100040d886030190041c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 737614928 1250 737613678 737613683
    0x9030b0403090f2403150e010b1206010903030c170d4b11070203030d230103033905070e06030c1c11061602031b03280507060903 57
    0x4103480e951401d060440b0b001d4000c0c11001c101c4c01d10b844644c041c1c0300341c5c03202011070503104219815583da1030003451944005e0304089101d8030001641d001e0940c2544c01250009030a207010601e80b851520000c0050b03d00a40007803100341071004469494407071300c041d21210b21685070104400c0001202c0119440102d0320101c286810841ca2110a9070b4103410945480c603180b00305000011701e601c141c0008041c201c00c1108c03403410510008000d40c4080002e041d101c5100100000c4060303009998041884100a4902c59950010010700c00294410045500500c122001c000141c2481030609202d60208032081603c01070412640c1c2403002c0052900120303104110000019250b14080c1911400c03a115602c4d0007217540550828441c00844110300098000c1c840aa50140e103070f00000c00c00c0d8055881c0350840c085101040e01580340502c11009000580340140d030109040c640803e0b2a510070407403440c1c24500e00344e03003840d01e0001c044080c43c20360381c00b4080d1100a51514405040c0d803a10740401e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 737616178 1250 737614928 737614949
    0xf0903020606040e0d0305100905090a06150b04030b091c020c12010b010c0201050a0c06020307030e10140c0901030b030f0106080d08011d190e0102030618151009030b040309 76
    0x402c0842c14948215040720769507401420224074441c030b0980150501600310100c1c1012500005501026485101c1c0503480c04400341010820b5800c144040d00c400d06440044802c290300c6c200111901c90080f1000c9a0f03100e0900c0c92250b81d00c00106061203040341903014801000000240c1c0e80b54045a880008170080f1140b685405010f000d160072078012031442030100c0c0006270070101541c040c60140112090320301d0400550b148a58032070040c0d800c01c0e0350520220752203d4652005041c20310a80c8a2a451850b04201000404010300c141138070142400790139120005500352540d10136046490018000f03411981802200d485880c0206194420441d980c01120b13101340c02075204003885412104080c4840710182007251035050309140151581030300003030320341c1072400c840c3c0c4500605000305640c400058a0b0302d080c50501040607001030000408240340d030104030040300ca4a03811074143c8401d4a01c07440394000f03100b0035901e80010b90005070880900340304000c10141c1c002c80381401c0d6a460b060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 737617428 1250 737616178 737616181
    0x61b1c0f0e01021e0708190f0e0613060513030b01030b090618030915040e041439030a02090a060f050d0b1911130801060f08120703050d0f09030206 65
    0x120700c1c200c0c0110349940130500c505540b04642c014100303002c0c01d4040e0040c1c2c0060701d8144000c0a820305403c40704003110109560040d030307010260b04500c44480b071030425960305186c801024a20030501c0304e1402108240031001c41d000c4034040f005101c03e000f5541c8038114a5080d6100d0820060217101141c04524030310540c3c0020b0500314035400d8103060040078034011410549080100044140141043d41c50310b141800000350702001071900c18041d0340515030040c2045605a01740e0300f018001d100c4081e814001866106410b0600c5c0c08203a80b100c020710100c414240542c00207810400300f1440650300511003420700101c649035520032011a40d21003101004030f56a00140714030820340100c00303000b000510340000c0d00d03d030100e140c0d82c0300d9140d9040000358400c101e04504d03020b03400c01c2c01003524900700b0302c40920407c0400d100340e401030124008480c1529150840265495800c1e525840408002103502000c05000b8070540300800b0350382c0720a02007604500c2840c4000d003a26042034006228040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 737618678 1250 737617428 737617451
    0x12061203180f0e01140d32030a02071a070f0b0f0105030a0305030a0b190f090501080a12110c060415021b0a091505030102070501020a110708061b1c0f 66
    0x18242d00840f8024807201c1050b03840e040301056007070790700202030f6040403904039140300184e0701d00c044401683d820316002d8030b04c13000002c1791074100703620041ca1002c903841040003158940d00001d0f103804540c8036100241d840e2004c601c1d010035502451200610280003c1142010020350300c603030720710410340b0408144907680d0391000c041ea00d944000300903002c10010404038041c004903070400303d105a400352510390764401c9801010080252607100b1507201c44044418850050a03003d0907006218482c0148900e0002c2d45804108104509186083c00f52414001d10b6540d01803100080d14030000303003000e88685c1da0f50040003134106180c0b1090b00500611050401044031191525401071005d409503035101d007004601c034010400c03904002c0c0d03007101d04c20000415507803d00040448601c280000758980f035107041d02034500311038544400c032582c0001c1c105200140b4001406640b1000940002e00316411a8103480c4c2e581c0b140c2c00400360503e45800007425454441d4001c402c02890000742000502200c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 737619928 1250 737618678 737618699
    0x6020123070504060c1e082a3301120b24190306110703020c0a080319050d020c0f0c040b15090411070302010c0207090515011206120318 60
    0x403528074012070410b00090102d036106403941400c292058940d0f545080020b42032201d081d6520004071569071000a600801c0690741c803089007103141b91a01f420401c408114469101d0743c2c1c0100d01d440c80e94101031007a1100c2d81e009060240612411548007455848420012000b01040b8041d51203401308408507084c2296100b000881c2e0f000c52a1544100c0e0106007045881c01402601201c0c2d114440301c040007040d0340e48910440c003902c0307030107179540c4407164603019040210054109116002001c01000031901c00710840e030f07014040c41c401c4202d4400002040d52079014a0707601c5020300b480820005170f1424001400c844440360135085600402c10302d01040203a903041440603412078040b079100d490f46e01804001c1d1074115401040824840c0f140641c00d4040d030001e032001e40050303447d11001d503d415018860310001e008403034418490f604c1c00058012401c0c001000d154100400d440d0301c08042c55840d4810000781441031100081e108517400c0042c02004401d6000710111003414001641403c0c1c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 737621178 1250 737619928 737619931
    0x6060114030c0a0f03020d0f0615030b0306040602030a1b1101270b04080909250206040309030311120301090f061712030403051c06060809060121150606020123 70
    0x11981c0c0740c03800c15112004c8070850503007001502415000d01416040e00b11900840200004911000a299141038020040d0880c205002010f25107480d00c01d401d103407004200c1d50350140e0411405039890310750406e854002c00f233002200310070007202242105405e510601034440013400d40000d000076560344400301c5142da41c42161041981e9007164510014900c44030301c0d60300500aa1099003402032800210b01141800c0700c1d01d02021b02030380400305c1c00701800200d80100c01d03c2d6100404140c039283c2e80141c040d940502020303051010380710018008010400c00400403090800109459507034410204028003000340c02c8a0120303007001c0c40854500ca50b0345070100a1002c68000301020000c500d40410302c1e44c0081c0054007002400c1006405c09080c038006c040300350200500000c3e03801c0c0742500c0107200b580c1c041d00f00c5115800000040003009802500800c07843c0c0141d0325260b0b405680e1400440d00c40400320405d070304a007490350002c3c60907010b40c8515001ea9200c004850421107903598201008030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 737622428 1250 737621178 737621191
    0x209091e0105010c15050403170a020703050706050c1606021305090606030a021c090308070306120209060402030604140a091b060207060c030e0603090a0c080c0303040513020712020606011403 84
    0x2450380c0100724075881010b1509041e806507400c8000d20301800c140200b40d410880e0207402083c0b800e034201a00d84000b41f40a58420031099085080c042c095a00800c20710038500082c0c0140c3c2c460b004580c2901c0144119028251400c2c0c407852a56054500301c40607411030880e01035841100c040000311400e02c1e030306a80c400c54000788442e103150b6428212000030340041d9004400881003460b070031082c04140c03203586d150a002c6c1e25003200d039250061006003541d405ea0805500a049001c0241c0162904020140c11200031500540c40760788640105000784400c001c0340e00c840d94100d051160741805070348901d03005070003010040d02450341a010144a60447d10a00c001684200020401140700c3c0d4210706d15a44640341450400c01c05c0400070b8442e070001e03074045030385400c8001c00c81c040100328034282005116a1010b080030a52000010341c07070b40074600c281801485480d643c601120103950441e14031540c0a1005040c201514100a50b1031200b181c03818046000c00a0030664045890b0940748100c0c2c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 737623678 1250 737622428 737622481
    0x3060a06060c080a020f0307061406060f0d05060f13050f13020105030103110d08190f14040b0d09060518060f010f050121020406051c020c0307080319020409020909 72
    0x2d2496803151000c0d4480c000c540110301907030004030003c0b1414802002d945029070801700d014200300d10008a00540688030520812080040040e41b1495000790f0700008110800060703107a9480b008a00c2c1c1610628040361300034180311800d0780ca031005500180c0070f4409590000c9096880e244814181589454060b001c80c0041c401040001c50110150f4420b0b48040c0280500c0c40865450307250b56013200d0400034100c0c481c6441080401e50180098010405910b40541c000c0c95203036000c1003134450b9000350300c9aa07000181842c01d0142507040500882d40c0114104424a044012484800a0708000046038040c0c840811101021190580c0c16942d0341042c14042c545007100640e401415038807882d107011300c030740100b2500d20420310260000300710b0307500c580380d64424101a10301c2c0072040300864200300d44144101ca90f145000429600e002d98041801541d0f0f4980a40003060703200190203044203940009000324800d04c564000e4050070384241d444030120b03120039500905a1050b0000c80b09000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 737624928 1250 737623678 737623697
    0x30c0b030609011a090409030c051501030b070f050c03040b0a170c04151107090510050607110d02030f060126010e1c09120b01031a011229100503060a0606 68
    0x140381419192100d240c013405800d26003000308000c1400d5840104095020554024040092010600c4101c50443c14500c04005640c1556140d104801c40a44a502046150740c11120464021000c45580c007241d001140d031070f04d58461341e40f1481c3e400001110000344980c03c250107612039100d4414001d808846503a8103250504849082071003008610310308101310510540e114034003d20891028102880d40481e45141c41c00e03881e450000c40d540b000303001c1c02d010422000461002008000380107403c441c49030040080d800040c1c0b50034102d02000c0c4031070103483d0000815060403186c002429804605040d407840c0030300d101d10300b01c03110080c0c0080507400c1041504413140300206520001622030602d0707100e894480c00002d01c070b541442422510400608018024000c403011aa041281c3c0940c07150260f44c14000d0b0088444810344004100290508036278070408609500646601b8030b00404401c0352034140400c503900301c40c0b442028040c1c00b13000003245440c10a8052002510303226154040348 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 737626178 1250 737624928 737624939
    0x13060813031b0b041203180c03020d170309060a061a090d020105040b0f0405041a1008040c0911070615080d080c090a0b0a0f0804030c060c0908070609030c0b03060901 73
    0x20a0307401014410014082d1800002e40500200e0380200d006036030101c079241354030f28003a0443c3c96031a049542d92840c0f098042c00a8079000c0c84005030ba905545000e1f0010a502d0300c0c1000034001d0541c0100d202000c0100700b078428000407501d2142112003400d0000d036030740710349218110581c41c1c290281c1c2e1800300091051030038400701400c0030b2031062405e039140c95a18000344a20b0740041c15503640c4d22100040411003454640180400c91941c00d000c015210003034030018030540590301038503060000f00000581484500320111000b04807010003402503060191040c0c1c0d40b6030000d90100c800c1441c103403803490842280f140e02c00130341c0c580034001c140c0d19822043c240c8460b1001030150328412420400301c002da444440303c000082c00b920081544895244101130926042c45056000300f044260800000c1f030b604c001845032541d04020001081100b0940031280144960400e071320602c03664100040040e4080c0845080324010030302aa00282c80d0018880184000c1d940b0503400030316070005208 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 737627428 1250 737626178 737626187
    0x30f080306010e062d0f03010317070503041212030c09170705030f0607080c070503030106080a09140303061311040512030705101505040903080a0f140a021306081303 73
    0x40005050620410701016807001807542c1e030201132152038003c9150800084d44100c81c011a403421005d1099500f0022450700c80c903150f00051201030418402884003000e4005004211a0110341010580341e07102c0e1140e203034000c01400f12004440500c1c2c50649940c58a05c41d20450a4804207540c617812294a0208602e005c4e01000116440030b02590400040541c0d00300314100c6103244c0c00004d40f0b61881d01d20301c0608164401469103000920411080700090b9001c000c603411f50746541045c0d0700b15201c0342c50400050024070030081400e12100c0000385050000409548548821511442102030291514091321001d840c120b60301c000501013840303145071118072070007000001001c80e41040c003680c51382c52828a12804080340145d0350141102d540e9088502c03117024180503102400a8121958001d125860050190103a16901c055110002c02ca6400c03504110701032034411001410003408441c000d6112100702c11107510b030164000340c05402800842d12440121f0003182c6242c9160300c049e207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 737628678 1250 737627428 737627431
    0xf0d020102061612150f060c080a032c0a140a0c05060f0c06070e031c050a0c0c0f0320090f18010b040203070509130501271803020d02060c0301030f0803 67
    0x80c14410060756900c13004200f480744c002101c03001c01c0784214040c509484c07090b4001c05500920100302d0380425004c0820141801c0b40c80b011024540040c1511a400502c040300e620382d40c004c81c83c95659011451201b200043c4982800e0241c400d05042020b4011015136900318503000030a03038001c41108008031300d03244010340860390380c50705218134250101c0040d41c200341c811680e0700d011908910306000d65084c108002c09c8203001c05104d9010550701903c01030085c0c0111316444040240400b000d00400c10045107510052a90405100c0ca864481ca031030201540340d15082c41000c4206100c101c404c3c60400c00075402004c1d10810f044a5842e0410126428800c0761000d0344550340b81c40b4504900e8a8500c011071140407a995565180c018034010012050b00f805c1240c0e1040d400c0400500011103560320b102d0041001ca4400380d22844003100400250100519480d00310003001d04040601d600420f841804504d20f9084e2480b6980702e03141205280000e00000c2d124844100302c00000810404c01035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 737629928 1250 737628678 737628721
    0x300c030904061d010e04030e1009050603090705011b030801031b1d0708070e030304260a0b0402100503016003061a0304151107020f0d02010206 63
    0x1203180c00c034000c000c00d050302c074503501400d11032019a8808400c003520720300c0c03980501244081180f003410180c034002c0014140c0a00715101c1d20300664580d00e46030181021000070500548429168540513480d5902c3c1c101c2071082c0c4d400301c6c0000e0040e10403400500c08200480e507240d1541c007010303400e54465030500c0045540b00e11196a0034800820461800d00c00c0e0b00c00301403000e04200d480e26010308001d020140141521040c05802024103150341e402005550581e211030740810040350041d407240d00c20f010140b290300b425000341210760041c0b0900108007440340d07000351400e006071445201e04031124031091040040e05000714020900b1060004403a00340c26111034003aa0040c5504900501d130400c0c079250744181d11400f201600000340c00001c0130580c03020f15040401580b40752522047c00308000341031480030035100100040400c05050558003007006044d2040140180c000e2007072404d9844043c00b0f038481c034014808505140b070007120b400e02e10b07641079001e0502610b504800c0d5004040d6290403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 737631178 1250 737629928 737629933
    0x903030403032f0d0f0f0f0e0d0b0f04020315070c020409080d0c0c0507054e030408120403031209050c0621010b0a0f1b0f05010e300c 59
    0x1440c0f030108882c40c01c1645940700007420324490050310283c1581d898000003030a01c100c4500804c2c0440c2c00202c080390914241c2012400c6654420001d40d02c0700700c004004044101074002d000c40c01d420500402e00c04c5100b9401c03510001058440c8045c10b03d402c58200001540050308400181815004510160b1041082d43e0900c80c242a4003000d9070403010a000c001103e909244044c450100409401040b042c1c85a01082a035001c264a00a9280c1420000c1c40706d152400040f540000c0c1101004840c444008804100150341d010303101d5000d40710380b407070b1482503441764240c52090404803800c0380d60507180c40c4690090a5480360291010f00317000d40d46806000c0c10a0215141c07003000340700c00012407001c0540746083d40b07541481090103802c100c41509080c00000c0080b0340102c604071004c4031504100b41e5029000d9a00d00082740c07501e200809004e08800c05e14100501504406410b0580c03070141d880341c01d031104e000c40100721040b061200744c1e241140340400c0b130b4a00100901c00a54038005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 737632428 1250 737631178 737631227
    0x81903090e0103050604030801090204050a1a040e0c03180d051b010b090c130e0f0f0901090f032c1003151211030d050f0d0b0105070f120e06090303040303 68
    0x84141e98244264800c0d14140c004c5001c003c01c02d0350051704c90740540240f440440c1014145404200081064004c3d0088842e85610824140c1251800e030340040c0002c1c1d500d07410b0303031074005150701103604140c0b2070300603500c1d1003103a440300342c1c40110703004400b50b480b80d407501d041c05c100c200440c40602040f4040611035580d811032901641b5141710062103010040003890780c2d45065580381b076400401b903200d09005011001446407511070344038141d420212080d9002c1e070a889160f40c980c018601031000401d0851280c10304010140c00c003a00388400240240c02061003045d480d00c81c030280400c0c024060380800b0152580c0301090282d40101e07203400300c1c1e000b904134154070f0361740d84a090388400b0000d59421034040c02004407071408014905040110380b07065424a4222a4a04014018130880507401620b419090070180d02c280c066a914980246c00d01c50200003074102811206040246900042c00c00014004142407480844101150140045241600c2d60301c1c210303031020440380c42e2001c10301d8511 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 737633678 1250 737632428 737632439
    0x4020412051f020c120f0d0516170603062a03010e16030e0d0f05090307031103190b220203030d140601020309010804170c10060906050409051c0203090607030801031104050108190309 80
    0x100f050312a80f0649c0c0e010142400201c00074040100000751040210541403c1100e6610045a0380790090003540103400101820300d0302090141c6ca00450f200c0020300030000240100202c40300714004c415a04042e54050143c0700e00310190350030704141017030075408030040d450414414182c41101c10030310301e0001e081030340b6070740040d00741220340d403003030b1070540c03400799842e40b43d250500008600300b60364102d922000059a07074901000b10010300c03800502201e4040e80301001d50080d03104412a9008007501d43e55800641c0e404002c01400181c5624101e200c0c1c0052659400042100c03441c480517100e090325036a6036501c0c00200301c035a442000b0f0034039081c0004c00b20030204002040c490001924086403d070b040ac0c220904442c0550f0001d80b15a0800c2e0002d4042400410340003103107070b00f0200d0b141840710486400d81c034610500318490340260300060460141588114039606807803040e03c0c001c02e42168174007000700340d8000317015a440c1c0d50030407802000240c0d900780d5a440c10910a0a004040780d5488 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 737634928 1250 737633678 737633681
    0x10806040b10080604060b03130f0201021203070c060501080c0f06032a12090c0f01030b15040b07050606030303042102100c050405040e010606080105040b04020412051f020c120f0d 79
    0x10b600008030311500184081d030304d404e010342406440c07080c07085402c40c9843d40965404072203c1d940a4180d40650f5005030959109000c50102e551568103070316900c0c100f4000040c080040c801c3c0a5407410700d000000b0460705400300c0c1d840402d80004100141c445244002c001080d4400b400d0f24881c95070003200c40d840002e00d91400f4541d40e002100c00e54031041500001201d0b2080100040265040788120080c01d81e2075000c1d100c4c00c40020718000420f1354402c008036440c4d605203980300d180100c020a0000d200711100f40200326852081301a03908649604061543d00e00040e500209054220b402180c80c480350040080f42c0d5200920444030990151250300e0100c4a85103c00d100041c0001001d0105007040d010310840644880001c108a40c54488000c0444c0c1040c000c4502c0396480c1c100c0a50709940d0f1341c055802138904050650300b8444680341c01556410000328541c000100303c3e0040448104601c240c2e500149100c028000241c000034500c002680718804130324024074140700c240c9000b10075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 737636178 1250 737634928 737634949
    0x20d212a0e09070801060503041514101701090b13080d020f0301030605060603070c0b15031e0d0c110609150307021b060c1c1b03020109170c0c010806040b 68
    0x503101e07822900703400c1c07003402020300c001080d907420302c844040100801a8818116a0f016410a20104840f40700407070b0280a401401c00c440307150300da56400c0c051607001024840c2c00701c404585881c0300c001c402d40c901c40c1c26034080e400082d00c0e000b0003000240485040340c0000001320b06c0b5851a40c50171170312100340c07400c13a00841c0c00010f549501000500400c9124070030107402c440c040703440b541140340071840140750b148400401005040e802c0042544410005c4900d91012001426100f07152282210043c591b11f1401040d10f191281421400c8020b0086280117003c9401420032030010141006000003035000c066082e030440d103441d148001300422900514001c88541d405030900c04c0188070810002c0c00161030441c03140348108604085440001810249043e50107001483e0340300e50041a603480700e480141030120743d55881100c08055040d80a4103220748900c05001130101c0014606415001364004891035901c410660403d03507004001d10303607000c80010700204415003400c02081c8140031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 737637428 1250 737636178 737636261
    0xa02090109060306050c28020f0a0f1b0501090b03060a0f080c100f02031e040f08070e07021b130b1201020d0e1915060f0f06020d21 58
    0x1500c080c01c1c8100101401443d4000000e40344990601946012454110b00400800c003050002030301050368071f80c001c0c07046c0408901004144c428240c0c49050260985001240860705024581d02c2803000c0c0351b20390404010384070103a6900b800c2c9420310109c1001c1e0303400585080e500c4004198000381b08a81c004512000d42845000f80c995850154240500401c82c81660814840500c42108034107038000b09403002810a23040003205070004c1036501c0c402d842a40c01100700c8000740c00c4081041100040c00c20100d64070500f44291503503a030307075080361689524289801d40700b4102c0780c401d00c00e1600f9022070b480403550301c07030024282440388001b41c50f110f00101c000794240d40102d81200b000005114105101d031804026003030051000040d11142e8001d00380060034110175080700043c950060380028007618800d6084943d01e5290041c60080c1c07851403084800510031442e0764a04c062142405500ca81d10070044c2e00090840005d01602905660b5400c40d400c0c0240c0d0305200750040b80484180385d01a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 737638678 1250 737637428 737637431
    0x50703050426010b0d020f0402070c0306020d0c09060e03071710060e0916031502070305070c030b01030b01051806060c01180605060f120a0204020f22052404090e0a02090109 76
    0x1140503801401c4d074483c0404a8800c50469080030050380305d2040d0300b10b140700110340050761001281342c40744041d0300a400140c00e203071010a0640100c2000c0d80a2016120340303450383c0390304940e100d0f001c440c1c0303071501c602c0b580c0c0581018200700210681310103540031000550081d250b001d099104036400b11032055000c4045403d10b0814816403070b20a208d90142070401e11100d10645045850303102d4048513038a422140c1d0340e4001805028503124505641d0500c2e0711452146405d030341d13401c060000c1c003000e00080d9800441c5a000140a1603d200d88140d0321001101d18000c6030707161401c11040f07410400e03c10b0741554a4107850100480324911071080c1c1c030f1140800080c2030603c40144058110a206034500400d032040c2004c486d00c03000100c10340300580c103c8016035145034040c0e03000d40074010081c4040860700e881c401381c0c0121214000300d03c1902d1050320061070351000d00b11000304100b207008508203082020403003407041c0000ca0300a18007030760102040303e480004d00d60124045040903440180c002d0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 737639928 1250 737638678 737638739
    0x40204090f05063324180f010518010e0102100207051c0306030203061f05040227190e0603340803210405010906050702030705010f1b0507030504 64
    0xe00c0b51132034200180c0405a80d480c10040211841040b40c9101c0040c0348505062400254440c1d440070100c8003264203800d80d180c03074106c0e102c0002503940088240307034070415032000c20007550b501c50f00a4a40c408030b903020110300b48a039400191070f40d500d41c840c850f04501400c0d46100c202069400186802440380c4e008080441064403502115170040603001c00701030610f4010000340c0c0d4009000b50300a1146203240c84004002c00003100ca0100a511141d009800800c114100d101081c280e400d40c0c044040801109070901003c020024140c1c1c84020140c00f21198144100e03000805030903030100000c2e003260040511103010380414404031000304030603915017130f20100c1c9484e0030102000a00c2c2c2c05c0011400c0010818a00d4280c2c0340b0084841c0c568840c034000101406000d412003860581c00507801c004500300740324001c0d1254040c26043d1925801c101040d00c03c1021441101e07240e4400c0300b8a441406601e01c0c0440c3c480d170142d0750a6003005400d000c00710f540400c5a001289044285207a080312 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 737641178 1250 737639928 737639941
    0x151d061305210322062a1814040f1b0207080703030e0f0103020d050108160512120a0c12170901200a09030501020409150510021005040204090f0506 65
    0x81c000b240b102082001c0720550189010500d10041e250050301812140354081044800042d45080501c000750000c1d043c0002400305c2010203807811544415803540c2240155a440c0a4481c4440b00d0140704078403140307a204024131720030a05a4029640020804581c4480101080c400d0b640016105c00c2d0785022102143c500d150100000401058903c0186c05000e19585000c2c04121030b201c0e43c075000300361405002e50607078401c1d0f0444481910101041000f03585504038a41d44007030140c0344400680702e10074003090318940940c1c41c05400181100420042e8120703c40f00c2407640207207400b002404030303803482d80b40001d11071030751040100400d50310b040205002e603c0407954000041c0a03424281d242400030181d144840b82d42803140c003490703a4400d82d21400800121030b1150980d0000d0f00d01d51000c80c010071740c26241c2c0c004485030074100d40c1c0140c81c16180e804001c5030320084050007015a1101c99000851186508142c1d0302a000500001d00c054040d12075a44074181c0c050203c4603070b00704da0108100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 737642428 1250 737641178 737641183
    0x12011d030d06051206011509080a0605070909270f05150405010f050411190b0d02090a060806030a03080a02091201020d060915050415120c060807020a151d061305 71
    0x420301104c16100400c603c3c003186441d0601809650303100094184184810740c0104003d000030000201200c0501c1ca1a0600364006d0a040c0d904900003100d000c40007a40c0300c1c0c3e078001c01d684068018030000200025240c003200841259030200e074403061b05882c100208005020300302d51150544407110861810f0318085007110309206030503004a281c1030500c0049981c003c9951000034040c0d90716000007120850403002c190aa038000c0f10206000558800703450038540103051a40c0c425603408182d44d4551600b81e503a58801c0340c5090f05507010b00f4030381000c86d1140d68956084120710320f006162003207620200c0c203020b441501911580c0c0d00000c9040c8107500d140700361001018080c0003000121040c1c84c0381c000b10825846400d00c11500c2c0c1404e00700d1540500038890040c2010302c0ea9218141a074a800210101103100740b102240080d400074500a0010425070941544030104413100c0b100e4124031401496803d0840081049120280c10303c101c080085500411181e00c1c42c0e130f9446942d01c0c0c51403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 737643678 1250 737642428 737642441
    0x171b03180d0216060c1a060d050607020a0201110d080601050f12040317090f120a050d0608070f090b0607060207050a0605070921021008060d050d0f030509010b030c12011d030d 77
    0x41c100040c842c99000400c1c210b81400c041880c01b810a81c6594941900080da464491300b8050800c1c0502c2051021168000481d400900e20030f807105481d641468801e107440c1e01403198070304081419031000450661003180180703050010409041d003890f40f040b40c0341841090440e030450204a0101c050b00303040240c58015540008070301300030680c589540c01103c0d11503220741e0800074840070200d00a102c0d00c0c0074400741c410000600e101001155925400f07a83c1e00d140c2e0344203801c8079440d440008160356260b800350103049000540340e10b02e4103071207940f40c40080d400414103a807030740101264040040c4030383c02843d005c0d00032a1340e03540c002c1e42409005000014884104c1071039245124004005803a42c903540e01c080c400c0e50900c0216035a407078004c9001110b002030003d00a0040640d10101142c111a4840f04000c10341d90420940c0d8400c01c1e51303401c0b91088040c031035040e400390702c14000514081c4000c9503202030781720000c034110784c2c0468058524080003c07201c61580020a1000c0c1d90003e5102c1c22 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 737644928 1250 737643678 737643689
    0x902120601451e0e061201050420030604050c09130b07120b0a1202060d0e060a23190e0304050a080106030b0a05040206030f040c150f171b03180d0216 66
    0x1400030b0b00f907001c0d5110311100511800785410403160003d0103030754401c070031341008210081c004e000ca40340c039160416511000780c2c2c0b00e15408001502c142100e080016240d0b201d1036006d002030885604030400c02c11000710050881d20451060004c4200003070f401441d5501813a01e07500c1d010440840709040105031640048420f004454a000c2040144d8888010a92898054032040e5507110051070b42e20190103d00f489000a00c1942c0030301078560620b90020002c900c240b0340b5500da000e4031a0741266415425512040b0310030000502c40307503d480540c0008122100d0200b00c918055441d008110803185030342c803e10040e503440c0010400d10040f00002c9a009240400070403082c030b40350713000078151f0201500d103134169601c4c007002504000d0001c001d031020b0507450151003804045010024180701c0c5c2d0039800000903019148a0141c001c01520482c082c180d0030124000240c0e04ca0340c68400394000500e00407881e40324403000b410310b0308244131104034020f842e030141040c10a014104c1c41d441d58031fa8020b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 737646178 1250 737644928 737644949
    0x121211070308072d08100b030907180c270f0f080f06090607050a0c0f060902100305010513020a0318080403031b17030c0d0501080313090212060145 65
    0x80c8030100d010070040c1403503a1300d504001c80c081d280e0400850304070556401100791034000106200c90b0300700c00034800c01100d90401e010108182100200015200c641c004070b0041441354144109556114404000980c0d00c41810819596200c41200e5500010350040301102d01e125024032000714280114010349000100514141c18460b8030556244002464482004000300746a141c940c0308170056015182c1008034008200802d08110b0000c12110790201d01c101e179000700c21110035000340078003412136100604c21008194071b0b549202c0650f000640c80c20070035036181040380052b90000400c0c07034418041c15032651180d0940c80c1c007034100c0c4610215940d005209200c6100001d544005d00307980c0c5c003000e000c850b0b100d884a40420104d4001c0d40c8076201c000d81464000b041102c0000044e00101d00460004008940c0d036428900891088030051400200900002492075000300d08000311054840d0300c029030740003400c00d40f00d15031350307142e80b9111f0f5080e0407442650f608280d0001c03000903000d003810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 737647428 1250 737646178 737646227
    0xf090a0e06160f09121e1202010510060c03021002030606090303030a05090f0f07150311030711070b090d020d08041208120f010803031f1e0f090912121107030807 71
    0x9980100c0b51142e000400c00806c2c608440c5101c61082c2080e000c03242d220144c3c00d0700e1749100d10040e0190031b00722010140d20010102c0050007e1003100c10115042c3c040d000307400d040954540c0c010195000400864012404001c03292090314104015441045103c0300064542030907603500341841c014051070f0071664480a104034107094045444000c5611403481054000e200c03100c180d014100d800b990109410012080041c446e802000d00320708800e000b4295603403a0384400c0e6205c880d0160403100c41d0000350301486640141080c0c40309003107036401a040503040c6656440603504038260044116502040440c101a903600c0c0d5501c20741c0c1011074a01029815030502c2005980c1c1c1c0001043c101d00c003000d904ca800c0780000307160740a002801e40112046030000b40c4030050002c518051180010034008050001000380891007070100302940800c040c261300442400440d60491800303290b48a003603488a1010780490700b01b0007082004c0c0b0946500c071076807130202e4000d0700400210000c0f100050f01c800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 737648678 1250 737647428 737647439
    0x10e01150309150c050a080a02030c0a110307020d032105010b16020d080309070807081c0f052a060610540f050f090a0e06160f09 57
    0x44003400e80c2211450000303107000003818160384031224080030600c1c01d0b103030120104c203065100000b020010250b865050f140d0b103d0041c3c1c81c0882c4803c86003c01e00e07c9042c00b211080300d10500b107444c1c01880c2c00045a00f08a000d8002076083d001c00281180406c000068501d403c0d148414401070701c8030304000420966142a40c0101c4903c00c007640030b114500403007a11000c41d03a40400d140015a0041b900136240c0c0380c003150596880c0c00602407204244038450380091001e50000328000d40d014000406d030b100084524041d10071041c40201001800001e01c14201d4910080c06240558583d614607000000b80b9008010308102c006441680502c0300d8600c08a002d81c0c0100d0b085411032900c240181005488018003600b5000d400c9004266040e0070300f415101400901c05410429004810030308180d6075681401d503043c0b014890150007141032200641d103032802605460340821950004030b01c0c00c1d9104005420041c045032010203081045042d21809580306181c2d40041051341051801d51b030821 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 737649928 1250 737648678 737648699
    0x622050a060e100c080a06051e041d0f010b040501140d1217042118180906092609060414040b092401260a021b03040e010e01 55
    0x40340080d000300d0711212100900402080050740c8010400740820400d40300120060007a02e083d205820b0b002d081c071001107001d2030076003815818495001e0700c50403004140800d0001915403610b01d011130031140000d000100d002405201ca4007141030b0300004031100801c0c104012280103810000803610114441c041a03140c5003100500582c201031290036008103100200d0b403d21314602261450f00d0a00305020800c10403000a0030f40340720f40c86010101020f2103070103c544007460345400722050100071040000444840c1d43d452074107010708020500800540f078240940c0e00b00300b4201d8440c000c1c4a500080c18a29001e03c074920001d508407245000340d4030001514a02560062000610300090a10419501c50744405020780002d803003040c0515066840110030078429a00030b002c1543e1101224642d0700c41d6549a10004004451a054402507a55142d00b00c0004000c3c180e026403c200000e0000c80c0460310b81403469080b002141d5560800344001945041039100070010b20380100140b0920108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 737651178 1250 737649928 737649943
    0x30702180907212d060509010c02030f1b071d0907060302040602030409020f0706060f03140606010915020703020312090103110703170c0d02030f0402100e150702180108062205 77
    0x130200b19200d4600c1a44004000c1c10841c401c00780200070341622604202c09500824400d5104070020040550240c0b010ba03160b00c0b813204111220f50040100ad0b61490f0b040ba00c2c8881e807031103042256880d580704c10088a0070341035070340503c0440c0e816074200700c806c803401c1100700060010303440c056007441e180c040c1c041e6a9010f14002c21505c10b402040b0000e99001ca002a1903009410200a1200503507540d03499100e0a000d0005841c510103105104c800c202c00011124000c02c0b060799560f0b200307460205401d264408a031040030460085200010142e40c2c10050709840b460482ea1880d500c0445000240890765152807070602440d007070020b40c0109410821600a00b40c00103207200c0a540d55006011680c420103400c03001051011051011041b00c0b00600ba104510a4a00b58000b5440c901d01f924070b0003e41031407950008030505402d18010040016000c1584064010480b02c044c1d090001d0740c41c0b100760440c41450f03200404014060154144c0c44c50103190480b54500d01000030703110b807506e403d40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 737652428 1250 737651178 737651183
    0x90812101a0a020f0a060c140306090a051314010203060117010e152d01030c03140402241611011d04021e030403021b03120304021203070218090721 65
    0x20a03910b59180c000c1c41000300c4070b402002034500d065602d242c2036004011401c52000080c505200d0880300951240443e405060010724031505595680d03408400750000030700d040c002024051a003030018441c000d1000c5a213038064005038603440c050000410b4000401c044000810280c0010001c0d40004007003280c00400ca4400400b10f01c052001061030460213484500d119002c10326401003075100384518001061090760300340104c2c0708025085094609605480d15442c04801c0454014500900405102c200606400341d40550540d04441c23650405a01d008241c03103034500c18000c12800f2a440b103a400001d00300119085c4003003012000076080c01c44214000c50303001621502c01c0500078a10f1081000e81905540d4a103024a0000d450300c079440743c0d074005694007104204483c038000ca00c1038040040d113040301f81950342d40d408103c214a003148656080b07000c00c001c5030b400358480600622a110b1511602b6506041640181d841e06034540d01c0394a0328600540f070002400411000211072a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 737653678 1250 737652428 737652479
    0x11802060d0902030f0304030b01060503070f0815041109030d0201020c071e05330a1704081b0a050c0f0d020d02040f060609031104020306010c2409081210 68
    0x2244401080082580660195040c460f10004a1003205c0010041080d00c4c403420040c1d6080c2d0369070800752901d000030745010b00400c4d51440e89442e000d10032030384141c2c0455076924583c4640171003404942115203a40f9085134074800090080994102000107086240c0184021881c4c11801c0781c07456200d050a0040c001440b09001d0701c0030440408100c521702404000788613070181404a040d002c00030312480144186e05032202d0002c1102510b4105440d5003200c251114a2440c19111108a58510041c001c641c181403c1c0301c03075100781c0c08074111148024891801015070156a040c824606001c41c002e461140120418108181d11081c80c01414644c1c140c0b03a8180d0706400b480080c02400604c02010b01c2986801c200007000342d400441380c8106d031300560100c80d4070740b0300c0703400d10050b07100c2103412030b003c280748040440000d4200e05852158118181c030b03181124001140c3c0100fa03038500201502c00080c007140002c0644100c15005411072a0054040241c600d0000e900302042c605002072520740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 737654928 1250 737653678 737653687
    0x2151302090a0605030d030209040c090303140d06030c03050309010210090507050f0310091b0803251401020d090c12020108010b130504060b0307030e120904091103100605100201180206 81
    0xb080190008005828010240d030032881c0d80d070b80014029042010010702c11424404c6c2504a10b00a80781c08044d03075015030b581c50308030700b9483d00d15100f2343c0b00200906007213940b01030000218070f9580703440c000703980310350040d669956441d00024540018001c0000c0e01e41d10b0700b0008000260000740c0e00d1304890045d14400d009075900c10020b0b0034040701d80c050350041030800d0341c04070030031415181c08180140d02e0035907010f041e41c5400307245949010703000c444802c22078400c0c9981c1c414400c40000401c100d11460401c03030716540710752600b42603800403034207074400503103030901c1900308042c1030040310140c40440400c0048182680009120705070620035a914610001001e15514255007242c0d000b612000c0c00c140840c9546d030414071450b600441d130f003200091600c1000a2080400701d02104206000180c50341030900203020003000f08030003581254401160051250780792070074404e00b107044420f0745000440c1407130001070100804140400c0d1085901d000303056400c4140c0194410002030b019911207444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 737656178 1250 737654928 737654941
    0x90c010e0a05090f07110a050c0d0f0f0308010806010902070803070c060b03010204120b060d170a2a050c03030c0a030c0c0b07120201200304020103021c06060c030215130209 76
    0x95400c2d80020b50801c402e00c081004040344008900c2c040c10302c0356078040f00c05200811150b00ca43d45040001e03c941c015030802005803a10f080b2942205000d1040c4141070307c1c0320303074403501e64081e000c0d003c6010417070302c40040025142c2030051600402801744150b1515100d6540c40010b44002000305007481960b1300500d0a110132948440c81c040030180086540b640ca0340141d04031644181c030100c0310131010200040003410039003502c0c0074550b409802d50711074185e102d00e8444150001c819080400c00c08094401400000c0b03120084983c5030b0070841d018120150611a082c14580244180aa03000b0072050400c000300082403448a500751421800c0c5950520f031030042c0325042e0b40b000d07003000720108890092010041000650100d203800070840d103680d441c80450a8464050140c80e0f0a10510029000d035000f90000c0032050a11084d02020f06250503060301180c00300c0e082100000c1301d10800900b056010802404200b40100141d220b6181c070942150905008000c024001c90150011520 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 737657428 1250 737656178 737656189
    0x501050f0c0115080c090a20070602070b0703242402100912090807030c0302041d06070f120b0904030c1403070303090627030f020c0a0f150206090c010e 67
    0xe00403e0b9042500e40950b41c04115a0707401c1c0050400c0d00c1107070b0b9540441c2c1e10068a2041c0103003a0030140800072007200c0305801840740d4110b441c0665019408000c1c0400280d0542e03007a9124040030b07200080e0200e21280c61500200300a076540015500c1c1c2c240c02d12443c010300c180d212405d0107182e14a081005180022070520342c0405072114143c0c1040c405c0420007003400c1c0040141c5120740d031220700381940e0302107540d600d4000703101c0074226405049041c070150405e900100103804a00b81c500b1000010301c2400c5241002c100d84c00c40000782c55402990034564044220300420402303c10505c006101000000d00b500320140009050040007864502000800b03244003400b110703540c0560b0b03100c0809003805000741c511810215011443c00301c4408903e01001ca9140ca5500102000b1098080c581e40944103e910540b0746001d5106540705198680c0d1a00100409041c0111501d080d86241c0202d0041d0320501780c801105542203402001071240c40080c4a101d080720910b003c0a11100c59008a107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 737658678 1250 737657428 737657441
    0x20c040b1504030803090f15160507080a0306090506190512010e10020d0c030903021e0f0109140105010806010e0c0f160305130b130b030a0605120a050f06010501050f0c01 75
    0x2481d1400450300009100001c0081c51090b813100080d0307201d01994080e21034841400003c40301c1101024030218220500a14070342070018400d0828900c1d00341140c0f41c1b20a9a080050303a01c0020780c5401041c0b0910305903010303031908142c065540c1c541d9202904103004e100142d50203407038040c85003080f800030a55000d4022083e40350600003510020200c0300c0b01c000207540811090f01105041c1254088401e200e0321542d48800c1c0c25038040c11803254218001c01c0300d003240c168018180c0c4a000c0380444900e00a1048a207207510038040c00034080ca885103420b0030341d00144d000b05035a8000307200403c10216101003803640a502c411140b40e0311101e2100320b003140d004503000300e0b500c042d04507400302c10107400200500c8183c040c61181201f2a9884e2050f450501c2407011903848904d40c3e51081080b051038a01564111082180104256454902194105090703000e030705a01d600c4a4400f40a0140500c84068051030440103030401e5810300b00060140d1044002c54642070400003080031141c0001e60250 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 737659928 1250 737658678 737658709
    0x2040509092e2307030c32130e09070602070f1503060503070603090b0c030106090510020a050a0f150501180c020309041104030b1e061e0306040623060a060c050a0605041b060f020c040b 81
    0x4000e581c40e00150a4a52812100074005202d092400300d0033328000100d45040703c41c0c502015403901d0400c0040d000040320440320300145a02c5078000f1400380e600707000702400381a5540d000110302c1f58604010b491800f020308096103480c020001441001e80c015000d2064850a481d003264812010604a103000b22515002e8514002e00081208004031584203020343c900079082809440c0d049280c1b482252070a119850a00e10310065603024903190b6040180405494016a82403010343c401207020f0701d95800070140e403681c0c000b50074010000760305000303a04500404010060b4268890b100c59004002030b03d8a881418120240d81c4980da25070400e80c0e00c0e1001600f6141c4500b451720340301c005000240b280c5404120011503054001c032182c0c104074030694000b00308001140c07601006441c18030403d8016182070040034049404120240900ba014a1044420f02404c040d415031441007015103400c6001000700001001a10980c001000103400c00c08035400250782e1042ca000848490484914 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 737661178 1250 737659928 737659957
    0x71403060a15170a0b06010e09070f020a14030a140c0303190e01020d14060d0f06090314211b07060c05090d0602040509092e2307030c32 60
    0x3c5014000d001c150705121034840c4090a80c07075150741c1c00655092201041e06a0416040030001c1d1025115841b507114041c0d80e40151035000001d07880d4800c000c5403c181ca0091a07000140c6954801d500c11680d5201c5403c0c208960f041000c1c2070351003a120b200261200d1004021078074100c04415080c3c1c02040d0150080c0002c43d50741c0840b07290328000d08694000740100903d040c00088240c20b000502e8052550700400311300700030509681d60b0000305400b030320a40400540e0880e00351802a05402008a0101c01e00030144c101040b05600070030200081c0315a0b0455a10060261a80800800e540e080c44d403100d03011404003103002040342c4501940c15216840707902c4080000500400d54014010388409640300c0701c855955101c480c3d46d07006054490315448840c2442d03006c1400c20040d482c0c00842290034046205825401f0722140000d40201c000d00f44050402807002c2d05030188241802110681030040482218030712105401340c212990310103014080110400781d4802c0021500d05001ca1840e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 737662428 1250 737661178 737661209
    0x100207050304121b091503060e0712380c0903150c04030b0a0203090c0118050a0b0408010c0804030e010509150c01021306030b0306131407080609071403060a15 70
    0x1c0c1400c0101a540651920955050f0003040701c0070750f40114410141d81030a0800080d141d641c8280c000c000d1030700828024040e000b0042f92002c503040398101e00b54003502c00b00880064048140080413002c2c001004011840300c40c1c0341c01400d111040715880708a00c200681c407018048082414a08070705180c05c400c42040080000080800010b802600d0140d00400b81e160b4a20465008a210a644190703541d4412200c005096201c3c1c03041c1443c072041c0c4900780100e81d0307940c3d010410b084000c3d0003207225181c1c003042c1446010001d01ca00f0810384200d1a000815042503240544070603900703c0c545040180004025080c0d85508000e101241d0300c100708103030341d42484c00303205000350017950554100c900c07040380000381d4920074010040b8042d0b000700601030701e850350b0280000c400340c8044226250005081d490310781c2c03001401490010a030f408050200c515126095070704060080d04491000b100300c000381800c0b038034002942944026940030005001441e000711280c004099031001c0c081d982ea559 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 737663678 1250 737662428 737662433
    0x6081216230106050303030402061b0708060403080411040c0c02060f0405030609070e07021f02161b0305121c020a09080d020a1a0f04110616032003030910020705030412 74
    0x42401c48041d4000810060307450300c1c2055283d11059502039440700041c0b00802c42500b41e01d80300f0391100540d07411108113956608100c0e00b071050851b010307804525450101301c00e0080300800c13028041400c480070420040010000303040b10140d08400f0380610004122200e110070624200c030058030008041b22400d14054903101d0f550122800307011a0803110401040000740005440a40c400007030041c40c01a03a581d00d25103000390000c0302280500380b20903111802060500c0c88000901c07202a0714000e59504609000b4900702d0008003062000c141001000440044031506a958010f1a1800750740c03808c1c1140203c1e02d41040f90440b52180c0540c4c1b5900000c07070f4000503862442ca1051481e11001c0b400c0440340d903501c3c3c000308e441c1c0006038041d07000035001460705620700d100c103040107050b03034107114159012640b185d2400308124003007544188441404103c2e400c80c0704d0a0241500110700e945000300c00d0316201c006514203000b1854000c00c40704208a410300948001e41860116180342501d0303030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 737664928 1250 737663678 737663723
    0x81314070e010315020408121303060c1709030405060a0804050a050601180501050301050c070609050703080324060c07030b04030e2d01030911010e01050702060c0a120306081216 78
    0x3e200884422043c0c40e0003404030300c514000e50b001c0f0ba00318009080c550407154144040759004400621050005000203c00151944600b031905003180d601c2503c015000f103990f080120700070b800440c00358402d0100700b005503920422106a40043c1c0342071442910703a4074007613152001d480341c020b0550040a0001c01e01d0301c1444140800c2c000307600c2052080fa641d4000381803c0320001e0b40c841c0b183c0d8500f0408080881c1407a00809081841307907040360388466a03a15402041d030000c1d01d006080c0d030303101c00e0400d41500192113800e1501004491031071401c25000340c0a5921a803e10006124810000000d401c2c94015088407a08180117800380c0795111a040e20507181030788804086616480f4070780207100c654460b100398130020303a0000b0908801c0103820010366015401700340d01030400030204050401a21510041d2610381001c40c0100f00e4540070f45840e19000203010b00c12810123140240030424200e0014041d000390510307846d110f80d200001119880003042040010741401070f0281c003001800b03141c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 737666178 1250 737664928 737664931
    0x8010f020a1b050613050c0a06020705040e032a07080a0803010302120610032004060e060306011a0904050703020c16150c0809060a03140406091106030601081314070e 73
    0x1140d650b4200a0112000c5804050b500300001d00164441400204840c5280319910000c03400f0390100d4040888038400902c8002c1950400c1c80103811210b410056030078103000d00d00800071040003a50412441034400503285286424010307074a680689020382411b03007802940080c00745101520075007499401c2c07808083d8800c1c48101d0262281d00c1c1c0404c20040c01003140c6015034207003500c203242d0500e59202c0707440300c10464903050407800b4414182c8680d40d4a40c45404010181038940401e03601c1e000d4209401c01105a200102522900418103051000e2000311307428820300302c4e8002903135100c241c01140203000742c43c00c45203540b1544007414040041c110440e021140210b060481c041e2500d0706c100c400f6494020001c00d0315034113210290803440d0110207445034800614001403403103241c08066164220580781584c03140d075284140021720264105100110740161401c42c55030518600091405100520b040140010700c800c440401c0060354803024006a050708407642540c5070001c0c6040c0d00c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 737667428 1250 737666178 737666197
    0x9050604032906090f1008070f0905060d0312020d060504050103140705040e0c0409050f030a080a0b0a050109050f040e0d02070806100f0302090a060902040906090e060f010b070c08010f02 82
    0x81e90031070141034000d801014842d05000c1c2c403858581e21040c02075010402e01406c1d032004652041804926460104140001000840d01d02c038407803450000480115a806030a460040c3e003401c0c01c1902107504581c414038001a03c00c00141d031405092021002043c95411090b070080c00e00c0c000106000c030f0404104880d00e0980181d42c80d280e520400c03c8201c0308030380c05000582e0404c1100600910300b503840705803024003520954001d10301040c0110305591001d035034000440c888c807040c080700d4961403040c0100a4001e981c40c0700e03201d0804d4006001c5248a108151150a0b450072920150f11142c2202d40d20a84280454440d8010850041c0d1640014040c184a07441040001744540e070500d42010100d6801c00500b1391100d08540a0143c1e14000a02035075019844031000220042c5903c0240002c03d60071070300091482c2860240d4044d034011a6110020390b1000040c481c1031141c40c4a46811981249100f82e6260128035042419610a500c18140d5510b481e2071003000714441c0d00180503944 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 737668678 1250 737667428 737667473
    0x50118080714010504031218080a03061d0108060a050a0e0d0906030b2407080c030c060114010c030806010e011202040b07060506090f1302040603050f0a0507090b1e010905060403 78
    0x405045000f0300700c450484010300000c00c103154110404030036034000c3e44048581c40750f20310705440c1503c0f864110740c42018a000001d656100400c610205125101080000600c4220b815407404413440e0340c030100a04280c00c407a94ce600801c0d0007074401d500c050069500c0754251214110f1210000d070281080d4030070071000c1b0b4100381100b5154074040f510740803044014002a110a450356404642e02c2d009250101c64500041007520502c0070108041c1500203401b800411031581445400303800c00750a103844505005540e00020300207608480c41580c450700a281080c0f1010604004844039107141d1407441182d40b00040124031a6034000082030071900400b8140043c0d280c0b0424854648000c070380e008a400518800300d9003d0103d003210156582c001407001c24030f90740780c1d00d41d1410107a01545000c41b03a4894051042000418090f50005107120201000f200d400100031500640101d1000c0c0c0291280500100c0c69a0244242c880030785400750070182c5403502c0c2e26000c001904000c40200340074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 737669928 1250 737668678 737668703
    0x200d03021b03010207170703091e03110409050c0411160308060a0f0302130b0d2f19060e120d0c1506030c0326030c0a260402010c0501180807 62
    0x5003814000c417680940d0020840030509503034400030a60390403a50b4202c0c01c0013000c007030010340000c0b5008040035403460400c00b050312504d9850700329200c41042d98058051410715044a0100d500428001860748003501d0100d03540c5400f052030140382c0300f08dc4051600885200002c001d240e4408903951240d0010b580e0400b1442d141c8a0300c10981010340b0000390720441c600445818a0550340060450580290040c01074070440d40d2014039410840c2c030300413001e03891001442d80c03c0c0c4001c41103011380c0170f0949000c808a046400380d580701100e0bc2c0206024810410300148182c2c652240c0c40e0220b034428802e80b0b1031003c041c2c81c0141640c3c201c00d0b050740d440305c0300110000f0b0b00300c1034800d042c02c82c1d07800b5032074000580c5035070303982c80003507d0703401c0702201d11009220487ca001070b003440114810030f51100155500c00d000b49019150480b1080e09504090419041c1140e2603448030740d0507049902424212090282c511b0701501400c81c00094108102c1c405e07440c0020000c140c0013900031244580d0080e030700c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 737671178 1250 737669928 737669983
    0x20408010b0909031b0109060c11012301061b05030703030e15160305040203011515031a0d0807080c010e0c1206070903060f02070506190605060a0c200d0302 69
    0x4441c425510f08400d03800c05c1001041d0b05c00343d404c0d03901c0307000306010000c0784a103c1d644800040b105000032090204200c00d203481002402849219101250480e00100c84401244803920f100d0050040340b01340305802c0014003200d40174201c3c070710000f58460106c1780d44407040d240041c09404594909110b500c200e5401c03416080254920911901d0032134500a0010080e200440c007520014000366015545d4000c00c40540c50611040b5003c0c000c014501420051645801006c46148042141c95020411203000031640e0350801c1b04281d40d001072403207031500c24904040c0d10502c03404010700b0301c661a103841e1383d03079809011501c81050b030f10803502c1210548450703079026154201211103000107410301e0301c00d00000b40306501c246100c83e5824801400c018041d5942850000203a481d84524030281101861070403903401144040c0100b5110981405c2074048050000504650300520001001200c0080302c407030618032900c0c1d07040040110314000164107010307448451104c1031444034860b03540075505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 737672428 1250 737671178 737671189
    0x141c0f050c070302060f071b0b0f06240307030605030f0d031a030c0907022d07060507080307140906070b19052a09101d01020c0f1021020408010b 64
    0x300319015006003007690f8510301406c42144009100c1c0f000d021020080806200c2140c1c2e01c006224072440e020805804c0402c20040710b003400030880362103050740c003030028403082e104003000d000c0c2008480050307101d80fa11002600500391582295415203d1604030545031b032000545048030b80501d4508100c000642e80314a10302c2d8510541d201d40613803100c00c0c4e1429600300041c01503070000640c0b0645a12951008000c2040b14400d001d82100603c0c00c0901c9500c41d0040c00040c000381503605295181c8a156030381c0e010b0501004081c00140300b440384103c1d0b200d01400f4111500c5d5800140f45c40c0e5110510318007d0720314141aa200380d203296034003414400f01e1040b445158090b201e00904940703058418810820000042c100741c140a400512241d840d688440c1010f0044035880c0c2c4980c1600c030b190317024046205d8180300003141154000b1b1505d0219880d24030043d01c025030300b0380d14002c4880d01d24200f0ba949000d05c00e00610407640c144200c40e0341c49019409002920080750082c0722049a0008022 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 737673678 1250 737672428 737672437
    0x40906091401050f0d0501020c2104032a090f020a1d1509040b04090b040219150e010201140c0316022d0f06010b121f06141c0f050c 58
    0x280010301c9006120a180c5400c2c0040c038114001d241d03c03040c0c5650f51301c80f82aa00000d4140b140759100440000e403400ca4030744ca08841000d416442c90910746544c840d00c024080350090000c02c41c101c1d04684504902400c2d080015000380e82c82408034a4003002804004e506c4000100c000030030091100a0344200340c200c00f000c5000003407031240320b03030b80d4044450341c00d0f84002c1c0610780c02940c55102c071b003030794941e806900103060080131000740c0c52811b8014001100b0f407400c41c80c11440480c0b0801e208003500205694144085440c148052003441e4005074010071b01c00025a40c0c255a2908001280d414030000350b10980c18a00e440c0845091220260f03950b285100c50700451030f0208a101202001c810703012881104c150302128449003000c1e07807890130810207801805807000d001500706d07858460034507040c1d0040c60f03101c000c0000c20540c41100c0d1592000780141401c00440390714079070914030f000013568801d2171001d00034910b102c2c82e500c40300002c04c40c0e110855101400d240020324461916015203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 737674928 1250 737673678 737673701
    0xf19030b18060f040e0f0a03020c0901120305360a050f01092114060f0105121e1c03060314060423031608030f0903090a3804090609 58
    0x464141c1c542c01c08004000b80d85400241e007103556500b882450070303820455007101040ca10007400b40e1062900b0001e05104150f1a0140540030120041108030800100e081b4104e1305890f0150721340c070030701d2202c0000e10711a8106c100180030041c0d0b0140d001d54140c66001344a41d04549000c43c46503502c082c409989050980b0a0105e9200402000440020b01e00d081050100290f04d041481b02e5545404c06103050900004103a07011804000b4442c038a10300142c09840201c0d8000c04501081c7c071407030741c0d502c510385c10210190b80f4000f0442a03018104101d00000794155144040d50040c02c130008c004204c50302c01039414840d9180d90740210359001c201780780181e401182148804080c01c0100f28100e00b03107008031800d07101c200000300d25081c100c60803d607440e108401440e40c9040c1040c0c100103820020304602c6417900204201680f955468200c2401c0f40e1500c80342c00d0302d1042410038404c0e40000340d101030381c1222442e0304108504010708010b1081d0713020034030100300a585524503032084035801e0161 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 737676178 1250 737674928 737674969
    0x5090d030e030f030a0204031202251401050705101d01060b030705070f11101d0a0b1902070509070903140105010803090913060603060c2304030210050f19030b 70
    0x4440c0e581103c2e0000307543c0441c1700c41016141650740d940c4c1e400e909140821000058008002c4100032030644a2801070f590401b03613080301e6032030903c5101e0446e003903d110f0744d84c1405000164503080010a1015243d80401c2c0178040085d2244994070070302e00c4d03c41c0600303003506528150300461910221410b03207020b4480b03680c2d118103040c0d00703644801e5013412080080e1001e01c00740c03490882a64800301c581c43c21403c1c03903840200c0d4144640c1d0501d044003004124a108000154045c098031000030159420b13001c1107030074424210700e840021790801d02c3c5a007142d50401020810440c81d240c004106200301c074441d40001218212040e100780c02c03500280078881d015081000101071520f0a1002030360080c109480c0884644196620001100d400d07501c211503e9494003000d08040f90810070b1000328002c3e00c13882c01030903400c056044034148910b00009126481c01507410fa134007486181500c150354406028070340e40702d07501c1c072000e41c110420740d042000190500340e440e00242440000d800705100007092 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 737677428 1250 737676178 737676187
    0x1810230a0c030c2d180b071e03120f09020411190f050d05040825030810050901030602070c0b0f04080d0e010c2301020703030621080403120509060c0105090d030e03 72
    0x14910b410300a109913130080000c0e20f900d10f80104000c140c00b0005226240d2840d82c0c0e040580341c544900701d80258010811032640500c1e5000c0b030b4024a0346075124035080030014031750341034a400302e00608014001940103454020b42c000c0c450340440040028140d2028042100450306200f2904481d48002c1d82000400600c00d403144121076820246d0803a2042c0142410807802101e291240b05040703003040c80118201041005042d00034002d075402c0102c00030004089030074080030030800301040c84010300725580002e0150078001c44510000c043c0c110108407656030219038800840ca90054040c003100c80c02000c111009450140d440e050b0344140c1a110b40707a10b070344503441d0756403540c6a01d0140f00c40300c918042c106001035000c0c8000d0072450b20075200095040c1c20119540c500c0b852651813161800c5200d02c040001c070b24030009490031030780e001640c90362002d08040221918000c403201103400070008141210212810b41240d0301c5042c0e030340100d03000c1070440c43d000c40503543d86440c0a54240c00422 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 737678678 1250 737677428 737677487
    0x70f0b06042f07061407031b05070f170f0310080102071703070905030319030506040e121818010501021b011e05040503030a090e1810230a0c030c 64
    0x404510303400302c40a02d140d06100040d02c0380c0080c2c0b83c240901d100303002d0a003c100501c03641c041c890001140d160344550344c1c0130552100040d20610070110050002584a9501c10400c1724066140d88000c0d031102c103403610f0744806000ca005079001078a28205600301401d02181c0d0300814400d8030754103034209102130424130021002c0410780c1d001600500402c07540c00c1001c00c81da1130400c002c026194145c4c68441503210f03070400c000c085560280040e44528200304030490381000c005038001840d12008421582c8021020b940711030b038038000c0c680a41101216001c00700405090855504a60080c0c0942e62000000032000e15840f49240c1100d0100c0c8400e5421a8101c04150060586070280d0424034030700b50300c542c00030b890354109c41422400143c4143c001e1044c90000c4000355004403c4162020311035840c00809500e80c02c4070307144083e8840c3d0716201f12443e02c5031114100845a41d0103980c400ca400d001c81d02070040d00e034500850000c20704003110030f00b5403489407803540d0081e000b8038040c40b07500c41181c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 737679928 1250 737678678 737678741
    0x606030318040b1e030d0305130311030d050408040e1f1e030501090f0611040b0f090d140a030f0c020303030f07050906030f0601120e0c0d0c0b070f0b0604 68
    0x40005410540da0318081e241c540b114812001c2c2407842201300b65000042030308161030701d07000c000c500c4101030902040c00502101c5408510304160705040514203443d441440620354054181040d410906100c03d01051200010080c01561801e8442d00320b40d9945516071010a1030b0403e0100500c0313019501042150b0b1a9111100c0d0748101ea114213042d190b80703841c1c0c0da023036802c020800d450302a0180c42c601d0800605114090000003c4a81107080620b40b5282d03620b0b40c090303411810804080040e803022036a80f000d81100300580d101c0c0d00b845610505040311951442e01d02012404141001d50340640780d40149515118a07600038001c43c950350302c0401146d4054005403160051140611007003210b03903581000365106100c040d084400354035040000406507450340307040500309443c1110740403031240d000c1080e07002c00302e055441030380304a05803170701c00039884290340140001c400c00305511080014052000c11640e0044900310030395100c00f0108000c851036900768440602c180502c92080b41081d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 737681178 1250 737679928 737679967
    0xd1a0a0e1f021306030f23040f03020109020d06052406090d0618050f010c0807090e1806090c0f0609010207030f0c030b010303030203090f0a02150d150b04061106060303 74
    0x1601c05420032540c80c050301c0c01041503800070b01c00b00392030344c02c03084110340240708012410340e149403000c0b20200514200d41c0c00030000b400107032000038594048001d050003501b000d08180e5010701085410100c0f814004000c0ca000e0791050080c40c1c041c00d940b4141e04448400711580c010040142c4c0c9866000c0082107000d401c1403404407046030711800841820300e0143c18151f003440c041d201402c01120545501821200840b1403001030002010030b000c1d0903507001e213040b0195518200781c1140e94a4405043d808541c0d502c2c1404ca440c030910042081c04000403450404807901602c280c040d1380e00c1c0070104501402040302c3d582c0140e00000003000450150800180410701440345103956903140c0e00d801212000c01d070016000310ba000000d021075404100481040c0003400c1e4003500d03800c00c1d00e07800124000200290030341c80c1032010481205000e1194881e82c0c1c80e140c9242005c42d5156550180070098000384140000310300000b100105022020424901c45c2000038041d62800f400030000c090002031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 737682428 1250 737681178 737681233
    0x206180c040228090609050f01030207060f06060e062107050d110301030b0a1401090209040e01050103140d050c071a0f210903070507050d110d1a0a0e 66
    0x141680140d156211440201003226015500c000000060030705120f4090120307102c1400c00810724000c00403035501a0102e0f0075181c0440342c80c5070456002004074080c5c0035480e4045c003040d1600c118501c0910190348500129105034480316941408030042101c2030044c4400b148128400403107020300240d04003040785d4841a1400c20130b08080f0803860f1401110741ca803180741603004000005006009242e090642e102c011031106124401c070104a91002110611410080b141c000c030f004081c0d41e80d00d411408030550503000822403503035a13080c02115101a904060700502980c0c000d81c4400e40709004684101d5914002420810701e00880120040c1c08202e80a0840c1da00784941d007100d00242004084030351803030b500a008500351000c00c2c0303031010740500300c2e044e258010008400080e07070206025007101c40840307902444c410a400d210401c04407000340070390b22a0b0084500030411000f001306100707907810b00c02e10804a076104c181c2c6004541d007004c10700f0741da90b009040c0d0410000032021841030402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 737683678 1250 737682428 737682433
    0x20315030c1014220e041a090c090c0d0e0109020405070c0201051e0403060507030f0e160e04060b0306130312020909150a08030c100f0902060318030c1c11010507020618 74
    0x1016a03891341202455820018944420b64180300034400810054081000d0500000c0041d003005030306295102052860a80503040c1070000401e000c40080640c1d4104103031607028042c510521580300c0c000d103840c1d4400c0344660b02d48808500c3c907620031490001c00c5941038450b2803500c0410100030030040b0004e07000f094006800c10000c40055036a000e5a0f00498180d1000300d5021100c22610099590b400c0301c1c800c6540c8038114958402e500903038940b04030b40c0a0510f000094907a42000b034054100b0010098041c4a07040600c501240c03081d100c2240c5600032750310031411035210351036641a48240440c4aa120a0700c001180000340b03a02034140b401d4500030248010a41e0310f00d01d150441c1c0081e0b007003940e29040b00c160170385400c0b0b050043c13030701e2055040ca0410140c001607000891a010180150003503015000076000042d00400c00c688500718040304803100c030700e40d0a90000c090303440c10420070001084802440f0805005020b00f40c002c90181d006031220780c0c2c40000c031110850090000a2032071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 737684928 1250 737683678 737683717
    0x9070305010f06080c240c010e190201090f0f0303120b13051807180c020f07030b070e040504050c040b01020a020405180f071a1c020315030c1014 64
    0x38424030507000d501c1442071021600c0c9180030401d80c18454038034002030080302a21072009a00b0013460b5440d180808003826551144140899180104040700350f1001c41d00c00c103049400c0420f40d0408a41109200b640c0340d18070310b5143c05401070450082e1250076040c00036440b084c40080d010340c04603203502d028554005405c01c80400000d0411702144500345200760b9030b00030b00200381010b00101c0c00343c20601c070081c1049881c0001c5241100d06588800c1001943e421509031890320038410440c0340311000301117504250700d070300b0030300c15040c026100d80d0040740c0c0345000c0410504090041038411a0880042d1500a03050750900014040ba460000d0450140d0054400181e5540c1300d003e009480d8540405604520b001d1607610f044440c80b02e0541a80c000ca900b001441040040c80c2c3c03942b440c4070250358490780c42c0520301032054007526000c0a0340e0700120421020501c5a00c0021403002d00701c003194000031940003408803000c8107212810001d8190b00c0030300115071880c001401e21080c280701d0070010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 737686178 1250 737684928 737684933
    0x908100c030f091a060607261b03030109050a0902011b0c0803120a14090604030e0103090803090f070e01050f060903070306110733150e01060215010b0306060909090703 74
    0x40741c000240403928039541960748109048265142503001d4010381764a46020880e443c0c40a403124840b0690008004a840e030b20588901c0d841600e00c481c0d003c0d160400c541d4a810009c540702d170000d0090015541c9030100150300441c0c0382c011700041e1901a10b800c522110f508005002c2030030900710944081c1a0301d1800a00008204018404407541c00708a03040c508000000d2000d8880c40b421300c1650070420307010b03c0315955010640c203030080e6050401a00001c0b0000040e00a07100003100540180340120400c400408081351803a44510000291a40d06445400080c0300003420300500e41c12031650324007494035050000040090a03c020211402c251b0359940b21400d4400f1500005907000d00424003004026860065201c42402615074002e107890b8001d0904400c2a160003440c0c8072904e8003021a5a0400c0c4100c90016094103016200c8540c0c540784007079590308221201c0c11020007507200000710b50203047c041c0c0f802000010070407843d03e200c3d1820850707903c0340948070400034020f0500c000700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 737687428 1250 737686178 737686181
    0x9030c0a0609030605060d0209010e31030807080702030412030e0d06240503030901210c0504051008010b040b090a0f030b04060501050618041802130501090c0908100c030f 75
    0x400302595002c041a0a40c40c00c1c60603214081c000d58000c41d1500c0402006944039a012415960401e07140520765403018014640806007803841c000c54040002c1c4064440c401d08001400c01c0e010307403200109d0b51070300361003116510000c444440060b0810300082c043e003020143c0ca4601140130340b500c80740300031140e80021405810100d044402550720b140912800d070240401c01c3e85c42d0550040c0b220b08515110100fa1a48102c402c0c55042091440c50088052111410010740405160007000800c0455071702509070b502034040e8510403000008808851071065901034140c1da4030040c11402d1500d040350f03075585030b001104142d6003d40491004039806420309541c40096004005c07001c142d0809041c860101d60044e000903009880802c40041c0e003c0d040c00d0480b00c505c2041c0d4000401941107040c410b600240480c0c001c0d84081c05101e4449426003030b4224505071035045008000000e600d10b001d80d50f0020701c0c411080383c0c0d000081081d101d0000c541c4150306405140c10042000c0c40565031400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 737688678 1250 737687428 737687449
    0x130b16030806030a05030309012c03030f0721091407120f03090e0a150506030114150c0d020115050a15030903050405060f0d0b01050f07110a090e07090b19060509030c 73
    0x950341c0e40d581e0084000410b0540c41101000e5040510031040c00c80b45510340c0c49110040dd9a860251040c01181989200e090252070150307811150750ba1580901010030003404101105030341801715001c051141100118103142100d00f4151135043c0c2e4800c0b6911813100f00e80c0780c681036040c40981000080c00b003242c404614840c4190300d1000a15803c5409640d0040c1e10f10703000640a0a003c1c00180490842c410014607042e40032102031440e140f01c2c0c205402e141c4581e14a81c0c0907405607514425541d50150400c020040c00303004000f41241d00c1d101404081c02c020300c212500d0f100d41240318417920740264070042d940d45c0a460b00f01c1c0b400c0d4440000c181d01e54850703a081468108006582c407001e00091003001080102440c240b0f2070410820006c0e401401070400140052070324440c27035011569800717010300c0203021104040c014003540e111402d88030201449400111030406030106081e240c01280381000c0c04c405a5440b6890f81440740458640d04070018141d054840c200200c5a56500e040c0c188 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 737689928 1250 737688678 737688691
    0x5091804110a1e0b03040c0621061401080109020705030a0f1b1505090c09070e0f03060a05040c080d1d01030914240408160c1a130b16030806030a050303 67
    0x83d141501185054030f101c0d65039a12950b64074a092083c400000d03500c2c6110301c111121403501d000c4103030301d0700700b00050041c24200d44c0004030724003c0000744580b03440d000300b001040240c1340c049650381d0303a9803e60140d100d5088000c1c0160010040e40b0300c124040c0038091041001481c10610307140d0792030402c0550350304210040d2103110491140380c4114103a40501740c0e00080c1c0303101801c1454600c00c0421a1104041c2401040c070850040004107a202c0c0700000e425441c004044800c02d083c1426801d000b07000c2a101a10b07144001000455500c00c0015038040c100b405036101c252040c0c0200c200e0340a0141141428109910f171a8118082122507046803208000d141c05020070040340e8140014918500d000700c62216940c00170400482c643d58141c482101d40c500e031a250740c540500c0d01303c403265840d41251011000c00c41071007107900042400350200d121a424800c0e40c41d511b80340c2c50b0748103024541030510600d004050820009105026460308070130701070125044107459584180c02d5400c2101d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 737691178 1250 737689928 737689949
    0xf051b011a010e010806010e030307061a01020706090b030f0a09060905060610090605040b0a0306080708030c07120f060b060d020d020d050c0301030c06050c0709060608040c050105091804110a 84
    0x2201c0380ca00d1094400700125400d082801081c000c40001a10610000301985c4c18020141c03403040e03c58409004541c803095103c00104030010a00103007802070307a038540515006108088000c03694602600b02142551034000724203040d640c40884040c42680000c1c103a2200075203609840001840500401c0c40e01407180d0003900ca946040ba0030b000030980307403625100c10081c04403c10000b81d40c0181c102d6081d15090040d56681d1842680e0950141c4000c1d800b21085124140d0b00061900010000d40a0380f41000292004150f680c081c00101c07a141d14006425010440d41d0240001c80300e520221190070301802ca141401610407081089800c8103805160040c0c000501c035003840e02510542e031f40452401b9515045505680b02c95000101500600052100c006200400e02c8001c02c43c120040a51b6113080c4122078071110000d04d59581550111f504d800a208041150b601403002e440306101d024004c81e500130200704c40760f5050300000e00190342c1c0022800d241c042d1900d5010f9010082d1000d0801c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 737692428 1250 737691178 737691191
    0x1f02010b010810050604090e010b090108060a0f1a040902010905041a030606030a030c0803040c0b0415080609090c24030108070806090319140912070501180b0a0f051b01 74
    0xd090b1402c024101240410b001c01c0078450f642d03404080d00c0540d548800001201e0b070300070724210b004003080c01070310340d00c28504c4000044290001801c1c621540222030144a8076a8451002003079a00c1c464544031154811000b003031003070402d070b801010001d00515005288541d00d001140c04c4a5005110f1030458031800e150300200c0c24108050740e0001c100f58010803103182141c030b00600003000b616005094803c0040440c1c00d00284c8880c010142c40d9940d04150f942da0343c1c0103440c406040310f801c44008102e200d800105070703140102645100700140c802030400b4000700e4007017204a803c0c1152510745080174a581c0c0d5040c0303008202550107000d25900822080e8245409980b81a0004001c2002c5503c1000090050031030124140080b0006007000112051120017044d45070064442c000e0b008039401140504041002840710704486080e00c41d102070450050a1034242165402038290080041040d5001c56110b540e220307200e0003032894002c0c20190410441c02c1c3d1aa041c81c45140182e46650 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 737693678 1250 737692428 737692451
    0x20a17100e0d0f0206060607020d020a0b0a0503190e060c1e0f180307060e0f0117091b010903021f14040803030907090e0a020d38180304141f0201 64
    0xc00e48003080020b400100385d1490720000181d29807085990090180000080400c119207070814240050082c0720001078032203107404402840c07034004803488503208980c0d2443c0100880c01d44601800d200c2c504000e800d082e60351401b10711071a4001600f081080d1081a001c140c05514135006c1c01d00310403482c2449555146032082c130700114041183d210f1290300b004c0300804c055500640b046481d15001e0301c0c040301c1c52060400683e002d40d13548904103031700740340d0400b00448814045256090080c0071004005081189801107848515a000c029004007950101000c42401da07110200600356510f01a0a00c1c0495200001a03401c03580c000300301a4008800e021003101d09114240140010751020000403181d094415134502000701c1c0a40900354122030341c1c003803000100058240c024002c05003038071004d410382c0c41d201c3c0c055044500030300b01000c5401f01c2d04c515002c08003c0412009240154242401d03c0b1001c95541c0c1058082d0350702440c2840300ea41c1045081a500c0700c0710303495070000942e00c0b00b00c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 737694928 1250 737693678 737693687
    0x4030c03032c0c031e070909030c0b07030e010c08070f0509150a020d08070f05120a24050307173301090b091e010b070f0510051f03020a17100e0d 64
    0x481d9580d4420700071885c106900002c3d02c50481c1c46c041c801103400c0282d81400d641007040040c01900c20b8228808110b4015055048410322000c0b42000300072400582d00201c0384c0a50550341400040c40810131340084902c100060a02d041c4014001d840c10f50070b20101d040c5503070003070f03043c02c0241e080300601122890700503525507840f51036820301c007026074801ca400418074415a44c207070b00101908404203491060941c07100225042e50b221601018034445040320300210785100746c91180c80713440030100d50807013000414400e41c403440d001090041c1041c200c51900d50207585100030143e490116200345100d80c520181e0007411740c3d500c0042d1100c050700500010040080800c151290441069047d000091181b03034116884203203860717140e035a10700d414a400410644090281d2045c800c0c1e407034201c20076912981c020211269500e0030264603c0750403959940c0f604c00a980422100004c102117040300005030340140238081079810106542c0d04000440f4400d000d4207800d030380a00c0038120f109420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 737696178 1250 737694928 737694943
    0x3191a071710030b01030303050c1b030903240f0903220501030c08100e07022509061205030904050c1611030606060408060a0216020603010308070b010e04030c03032c0c03 75
    0x2602c024003070281144c03602c088551044c8002420903549800081d9582c402d0740540d070a060b14004c804201d17500c0449010f03943c1c0c214281c01482402403600e03a0501c440700c440ca0304662494030a005c0302a98503400e2241094034000c1071826a8001000b641c1010049000c107009000701c041a5941140c1c01c050004040b030b0a00c109800c01c2c03104900900000106002c4a642101d0b02c6280d08111907544072401c034241203e4120f45812032440a0b900540d44110100c1802607038054042007100590f110300c0480407095040002e0807c1e0020004444142055000b0036031054040c54518646010011b43d00741c40800c498080d26400d202007010000c0f46030900805401c030340c003120000d08250808508680310b00016010400c981c0e40052a01d40c0c500152030128842900202180d450b583e4900307041950307611560080341c42800c00030001c25071500703202c0c64500580c1c15945125403918180d400764000c00140d100f0800c00b08000d840019107225901e81e910940510348050310391141c440b014185071282c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 737697428 1250 737696178 737696191
    0x70510090503100623091602072c06030109031706010c0b180f01110d150801060b0a020607020304030f020f0a0e0a0b090c030103051908070507090207110f03191a0717 73
    0x30460030882e03071071b07450021607a00440d15000505050880c0041039180100a901c01c41d00c90b40214041088216031840d400c00360384d440410350840c2e0341c0341000c0500f01c9041d100f00801050b45103c618100341d10a00345154888030604000101601c20707107809401c98001c03a40b401d900e00404102c0041100144103142103051a880240036a20080101c060303a03006e24281007100d84d944400350101a00c0c82c4c81008002c01403c00200192501c51441d00010390100e42c0c1d90001d031042c24040340d80e05100100f102d00312900100583d034522500d40c200f048101688105560041ca00b0b800450183c50000d202030040017515000a440b05082040c4118403100816150400c070083c001000420b2002c074040000d0548240c41d1a02d00c06185440003050282540c0903205214600b00800d20359441c0d8002c0800d01c3c0100030401461030024104114018507004241d05074001c141e00644031031007402e03c0040b15205144858208068181d090381caa9400ca0307000e0001108503648441820302120300c2d541085 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 737698678 1250 737697428 737697479
    0xc07052e200f0721020706090b0c1b0102031b0c100c0b04060b030312040b0709091b05130806090a020a120f0f0303180b09100e0705100905031006 64
    0x201c403070428203028015411425071401c000102c8004201112400c407011003407090034801e4031456020000d54810040c018131000c201075010104200200f02c0030748030030b40c000e8801801207030021203020700b8820070f00030510f065210a000c81e0041104258201400c9a2040000d01400401750200225400c20f02d00000520104d9002103000c6039401e5000d6034407980003000071400c038218202080c6944a0f0028990101840c8014441046a02a4281e0150040e80c0d66040900c1d100e608075000c49000071411801c0c032030355615055400c0c0c0a40094003c99500050800b491075031035030a142404400c440381101c6402c00110042140342c8421a10080d041d501e0f00361036102d0f0f01c0daa032100341540628001d4400407199148204140c4240c1000882c00b01c0c604d4400200302143ca0080095841038902400f140110700030031903441602d10511080400d0f4000400d40e09182009018140042c0c8940c1410081c0c0c0304000b10b01c40d10b040104201c00821070500160103454202e0b181c2c0c461080c50040c0ea00034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 737699928 1250 737698678 737698721
    0xd090b07021203041d0406060504050c09010804020f061b010e07051e0402071509020906031c05031906230303070f0201120b040c020109021e090c07052e 67
    0x451690065950855050702c1c00c450b41c60802800c00d02d54000c9601140342d2183c001c0185803007502204a01d402070340b280f581445415100c40400003a44c5040f95810811481400240c0c1150710070805242c2240c00641807170742030b146060120301c2e15442004180c12010144140d81c031400d000344101c5040b40c5060003e081ca0f5802c01e07000500c6001c4a4424030702245581c4000c039880e95440d8116803100340d10071035a01507041c00d64030b06005801240310a0b482280c43c040010000c1c107000c540c8010065042000c01840642910255a40d40001c0d10f50700040d4100c1500c00a00701891185101a01c140c0b078105188000c0500e4020101c6522050540603800601c45500010410440d5a10b020b0f424209041d0401040d5007000c0100401d11107a0f50190901612801068041d4000292940203488a0702d612505400b49a80c4508903900190040d180c0e4001411110703100c0d0142c003075a40705505860001140901002c40c2503210389040b060a10030b044580e0340e0103070910401d52401c02360000040340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 737701178 1250 737699928 737699939
    0x1a0901020715090914190b0609010c03020f01050a0518070b2502040f0f140402030304050d0f0f0803010504270204020d14101a030903030705181002060403020d09 71
    0x481c025442400c01d02034070815101d07802030046004101030080301d103080080d482c200c921035000c50026149540341003800300011285110500590112002c041d01031480d2601c008011102030460a4065003103000e08130604845c0c1000713008550048440c024040740d5422b041c90202d01d040000d00b0050b00592006004100c0303015082306690303451340441081c0c146854101591401030040f0303240254020b01d00540c8100c0c0442d15400201c205c0f0a860040080100300e80740d20340c1c080d801340c8006e540750303205000400c09858940714a1100c3d9210b4000d9104081007961041c1d145081d00d141110f0412002c80144802d04252080354044100031700d601d108008142d1f803640700800506c201034000e1781c0010710450000c041d90449100c5060f012182980d81c9411404040d2840440c0651503454000c40503400d5090040003e40740a403010318055460740d1151002a1800d901c0b4007415003405515012070780b0076940f8203494001e06503054014049a02d03142ca0000d013000e0308410f0a02c18802c10080034001e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 737702428 1250 737701178 737701183
    0x10203030f0f070e040c030f15051507020a05030a06020910050403030f1116170c0406062c0904030e03010b040c0905060f040e04050d0206100b0706090222061a090102 73
    0x3000440c42e4000c250b035844168040b01c0b026840b0000c182c010f0b050003031961401c1d500d41d201d500700b55401b200c20007540450242001c3d00602d14401e83d50302c01c0c5401c8000501d00b8090000f0404184001c03c020261992800484d0030f04010060540c0d0896001c212058075003803070506c407054540180340071403400b400c5030380141c10071158240318030400c1096003d148420742c04100c20515000020100906917a4a144088081101c071000c0320140c0a0008848460b0400303015003015200340e5110b01c2c084a100005035201d4900610344a0b2002c1d024680c901d0721600c680b82038500880c000ea40f0b000100782504103040c00c1d2100d8800160280345021054008280d000c81c081064884c202c408036640c03022820703444907d0282d03400c0100601c0100d001e201c01c22030001790043c5a151903400b0f0314003d94030f459041c01140114802c41e00b606204002d090300040030750340a20b0300c1910080840e40b08007105000302182d0240350228480a980c5c442041c0300c009001112400a9030002c40407910300100c00c00000d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 737703678 1250 737702428 737702431
    0x90605041b05090301150906080f030f09090a020910092d060e030705040507050c0609030405090a1d0a1b1703070204020901140f04060e090717060105160c06080105010203030f 77
    0xb0440049500307241035500303410040782c40c99204144c01c02c00d602c6070080c80c0242010302c5040c0c1184201c001640001c0e6003c01a900e4061180c00014140070314241446080c0100805901d0f071164204402d42c1c0c940c0d42d40d52200d2030702c0450b507150300902e03040500b05415004000510301d80c803400e000e0f151244d070320400c3d03e10050f00c116250500d80f424401000c24038002c09608510f81c404c0c2401c003001511075024024001209a4004507661500c035002003503200e01c070718094140c01200450020301d00c04103d806c0042418520a109891291546101820001158806c48002c8003000c0d14041d21040041420064101c074541c041b41984025040c568900c50940c0007401244c001c1040030680e802000300400c500240b5201d15901c0504565103012070388240101c9011030047c0c0c0c40c0850509001c0940d80c171805094072040c414150301100714554140040200d41042005c100040e0540015411120f0162180c00364129803400c01c0740c050064a8140c1045046520501c1001004090381c4080b0713 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 737704928 1250 737703678 737703731
    0x720010b0f190308160b07080403020a11060d05190608010b09220206030f06010816020a060914070306020702030c03060f0a0c2604060605011e030203100911030109060504 75
    0x1030110b0082092285528015640302a00070030010880410b641a40d921030541c140c4111900c4045990b100e06c140d42d013640c00c0d40c0113030069218050000026480c41c41d03031045018000c107424100036202e440c2106442c0c00712031082c00e4001c401e08500d029040c5028150140010400074401e5425403808102da03864004c140140c42c00c80c5010249000c60f0350140c0c0004544c000c0d000b16a240fa00d103d402090039416510280000c1c0d04400148074103c030b440c038081031340c0c41590282c40142d05545694014240381041a51900c00203007000e4a00fa00400c42c0300025481940056121240c2c1d004050030b0001340500c043c000d401920400c1500c0002843e27130b6070701000400e0300042c94203050340201c1c0d0441184240c0c80244540b00113903915805902412440b8900c1001c040c04496203480046030380c14440c3d91080c20341e0000228500030300f40030b500955440300500d41c00301c50250b59030382e414064420764900c50218820000041c003014045004103c06008141c5050140d18180039014a8041025100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 737706178 1250 737704928 737704939
    0xa020a08180910060e01030506060c190c15090905150405192708220b0403020906012c18040b0106080921030603010236010c081902030c060720010b0f 66
    0x2100c41d0303216030070b2f01e03496a0400b00f00d6200b0171802c00c070a004941182015195400b20620008100e0701750405007604402c0c559a00040fa440e102050014202c040c0c00c506540007071304803c0344540c4641c03044611940c00184254031070700004035458122851880c070300c040030021a514044051038000f01c0c0302c070207a21411440da503160003020b40c00042015101610741c0ba44008000030382c003560310094001c3d02e008403104003040d181c460042d107904294041e43c040d0140081c0a845000211a606821050004c0c001c44076803507881c6900614058119001c8a08041d8000184840c0760b1195a8942c01801c443c0141006080d10341c0c4550280e07600222018035410010005649480a4041d60513244401821543e10348004075002a202c5920345505041001e80640c100ca6612490f502c1c14019000448607191050220072640d442c4686a4120294031040001205898003088168444c001d5a580c01d080c485035000081c4000c0308615140c000c0c4d03810500503c0704c954401903203c09000c01160b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 737707428 1250 737706178 737706181
    0xc132a09080303010e060f0607030801180209060301150207170304050904030e0909010b0f0f0d0b070306051c1110051803120703090f050405040f080a020a08180910060e010305 77
    0x404844000d100c0c0c020300d1640c0000f000004034041c0018030280a0b45040b1400d0558140000a100c0d03176000d90f020103000909801c0c01005020802105844c90403190b06000d880c1260140204181f85c0c42a807051110080c24407952202c42e030305108580c0581082c0e10b141d4216184510240c0d0360b805617020b514407903541480802d04143c051f03600325041e000701401819051401c01c1e40540200152408a4001c201c45601c1e000c1d2803900300f020644d50100141030f442040c400740c807a20b40e182e800401c4c0380149603a404002c543d6560303100e1100d295090082c7c10716050b071070300d103003081410150700601405141148420a2101d40207400e5541243c60382d030140c00701c41d91503400640361049100340040b020500140d001c0034168041c0001003a212a1003d1a41d040c5c0e8400a00040b20001c07600a0003208100010304005480d18000b01203400d01c91044034180211601c50341f2180e840b801402c46002840c070100c501344d0401c1d203005980013445407a4408220b20305840582071903654000d90341090790342e00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 737708678 1250 737707428 737707511
    0xb01081c2f0a0312051303031d0723011e08070201060510090f0e2217040902190804030203031302150a050903120f090607080c0f0c13 59
    0x160014180075094007000c1040416094164659510100c03d80000310445030b06403060102d0b020b0701c3d010b88104040c4040200190b14210018490000762030b4145484c00c0000355448410800d100140c580503041007800383c030541ca4501c5001c4003000d03140c11700612000b00d81c1c0120303000700790380315100190a04400c0c559650b00100d0040c50303103422540c2d01100b0086440ba04c6a0301c0341410068803050310800035502e81715078050104070b0781140d90300f01502010400c0031403421010315640c6c58500c101c4009400120704103d602144c1c10a41100342119404520015080650b2030740303105620040c1401d1910307040c65100252a03200040c010402d032001546280c0031500c60011038070251a48002142d114540340d50010302d80c1c1d02915070305200f44513807a8048940d18035281101c00c0747d1001d101161a000e6080240301880d00300c4581518801c2003482112400d0106000b1601034107001009084480041403c0010b00c100c60044840154903015521050a03d4040004154a6542d0192400c0820710 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 737709928 1250 737708678 737708717
    0x30902030307020405010e070e0d02060405121e010c090605120a02160206070b0604050c04060801150e030313030b0a110d020c0c0a03050d020d03020304081206060f070c030b01081c 79
    0x10b5000039003042c41c150000030380159006419015402a54980c01032130072078020082d2051050720042d5010008000c100302c546012707402c0104001c0c000050314440d0707d000001c0c4040021030707060041141d46501c1581100303a0f110b89048041c105500301a800c00e010240c640c40704500c0105039003441a400601000011180158182159401006555100e81c00c0c901002143c0301550000c0c082d60400e00410340c410554415102952015030b64202280c4c600320360501c6107002d0b100d1300c1e0244044114520034130b84090000f070400b40c1d45040740c01a114914a44030301d04507401022070400510746682c06103880001c108403401a40802000b513140c400208216041c445407401159109010705030010801030f01054040c01440b80e88c09071170805002d000241c0692200b10f8000b072550800704141c40325020846c0141e500810003030f002c141070200301c98242400e940320750001e84064036520801c05c100000c0090b80c038050003241029124100e4503000b40d02070b6000c4801d015061180c00c844900610303019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 737711178 1250 737709928 737709937
    0x14090c04090503040f0303050c010e0c01120213030c080d0f030204050307060c020312160303050717070305070c0605180c0d02370f080c010e030601181b18090b0607030309020303 78
    0x342c605d40e10b207240d403454042d220b0760100280d00007950070310034641c980c81c01c046008540c001e0181c48010044410b60780c21002940103185100ca191101800440486c3c8000d0306107003d1300240c0c009200b02e07510424090b0000c40d102c084c0c40c0415004000520040e01d01054181c101c038524205170810f010309100207420031041180300755140f080481d031100c0c2c805040d5196001d541c0079440405c1223440d0000200d5000b816515413022041141c0045501c1912170307441140c1c0803905181030702c0c1c401d4403a1348a4081d0b96081d5081d0200c03000c48009843c0e0203805010b40c20040200b2640a030701000c0c5035002c1024a01815402507802926100101c00b40d0141001d001001107c100e00d849070715103c03120010445400d0081840c01e01c11009503a003035500656152140c610001c00a0010307038648040ca000c0131418551860700c19848203401d02c2a00b0040c001004a102144c8a140e003e030420380307400c035007100c940d0302050186051985440d0316882d078038102d80c0400e4052602142001c40d90004c207103580301c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 737712428 1250 737711178 737711189
    0x10c15020307021c0c2d12050a0f0c0c140321041d0402090a0506130504121103030c12060409140a0605010b04140609120d020f0114090c0409050304 65
    0x204000e00d00743e000c5400e02500c0d4441d074510040740e4280c0d90881d01ea40380710000500c00321000400d120800c5040c2c00d000411021030b00301800f900229640c0c000d0040722550901c01040010a0707580034682c10241c5100030300894500390480a000f078948841400d510320500188000a1484a0082c1c906001d56804403207400f81100d21808000c4800501c1c0c1d000740300b09083d150f965008001c0c1c0f0740c1c480f11540d024a400410b4103030142c503400b05030802441701a018642c000d42d04955008000788a0007550f100394000c101c2500c0c1142d080f50090f2500e081040c914049030000c200b004400d10202d0250351000006408060282da00c10700444c008005652000c0c01ca402c1c0310781c200c005032000042407070a5034801c690500c01a6600e5907199030034001e40c000c0350050300010070f5201e0036041083c0a02140c620013000a4082d816924496080401c207008000041e08080c8501a00034000d0140203100c00e6860f1450060749440c183c0182c40c0c10340a440c1502c299268039a1a060040802c01c0d60090310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 737713678 1250 737712428 737712431
    0x10b0907081905060102030910050409090b040b0a09030c03030e16091b050c0c01080a020702090408180303091509010908010f150902030c040e10090c05070303050907050f010c15 78
    0x40003400501a444100c0d240303002005800740d04680c00c1e2450050b903014000c10b03002142080d083c0d0381002240c4031940c12640400206000019104041d0300610304140d02521200700c8605143c200007a82c0e1100502100035a82000c1c51440080e03840010010455018500021545110112103042c000350100810100d030f142e9401007440c89696211440702c2403800c0d81401e041c614040142c58502910341d2200311a0400c910004255001d81c40c055031005010100518201d0300b5400940e15100c242c0e030548036018040b0b002c82c0851716680c20801c0c440c3d403c40c000c42c244540d1000040310103551111800c40c00c1d2000c280c000311a4025814070007c0d0130204000c0c03090b100c412140000401c8ac0c4603520090701040c440025880d5078901c2100c0c05076031515407040c40c0504150400221080181c03481e65074406402001401482c1c5100d20080300100360f4819a880700f003400c004050b100d02400000301c0c0e0300540b608100681d600403c0040c484000c1c20044600c080382e003002454500d2125011034081e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 737714928 1250 737713678 737713681
    0x2040801021305040e070e22050d0c0302060c03160302071e110a0b0705060a02130315051008030c060612012a03150b0a1d03160806090111071103010b09 67
    0xc0141c00008410f5030000d44080210042c1e03c1412542da0400707204014800403242d0205040001301c040c8449243c40e0700d1015108100d02e965401d01d01004402001c000652000700d020405905009468108184062039803d40c1000380101c40c0b1124204244001d0550000e41c0e40c007005011300405379000c190081e5050f4000d050700741001c0001001c4482c1f8450b611803d00031440c0703c000130a45a0554004000b0030341c654480084200039804203096400f0104000300000c0054460800d01543c2607803003401107000d0a10004a0340c006000e500301e0121504240010203041d0b01c001038466018000b25081c4004c201d41d502e4080c0180f4411500800c0d500c071120305071400c45250344080c0c81c41e8116a60810404100001c20407144e0194050b41d48103500030058543d04034031404c03158124400708444162900e01c54030000c0e290041d01d40035080c0d1003103124020800d0302c9041c054242d0140020000744030070400b003c00e4031040d200300d01d8018001c3c0c900740c5c041d0700715440960120215640250040825 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 737716178 1250 737714928 737714947
    0x105030d1202032d060f1903060b0d020a0627030b0412090902040b03060f090f1f09020406030b0f01030c17090a051509060a0b0f060d0b063105180a0204080102 70
    0x13000f030101c0d00980030307450110f02c41c00b0320b040440ea00308454103a00c0390050514250343e5101c000d400725200030355101c542900344401507074031a500c1030b004120300d444e000f5440010744c182441c01c07244990810070a81800e102080405c0700100f200d40d100e07505c91201511495004025078a140c40c0c0c1c1c0004105a10201d0003040191a4400842c000c41c8200c0b040185a0110400c0141d0980200c4070b00d0040010000450b580d1080d5400041c40b5500440c1f0b030054003521070004074200d8000d40c1c080000640c845211102c0c500380382407040b00c074410a103000d0200294504009d00040d4030700344811601079881c2c0008090f548280802c0f06907070390180c15100c0030b10b80031404c1c103046201624172500300e024503004500120b240e4403e01105e400080c0c100503071a10f01104201d800d800584c00520140c2e1a980e06140e80c1c0c5d1a5002400c00b5021800c10b0508101100c0101840401c240981c10034080c0c1128280820340d03ca500ca1010000315514000c6035030340d500740550280c011350f807001c462907001182c400d10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 737717428 1250 737716178 737716261
    0x5031306060803070510050907030f06020f190f1106130c0f0306241505090423090f1612020303120a021b0604020906040e01240e0105030d120203 64
    0x860a005c1e60840311004420351800c4100e503010b071407090703456200c54404c000056101c05a012200d006d01001400e0201c0368070243c4181e401003800b0038074540364407482c3d40c40503006041c00782108018608240d90483c00c1003842d954100103400409101045407400c4100310100c41080050b040c03510301844460350324a001790141c0404400c8a540e100c07081042c2048260a801c1c0c1301c1104e001c540c02d080d0070301310510165031507403214010300e40007030b150070b800c010700c04a2401e010000c4480001072103062600b221440e04140d1b9450900442d5000460184401c281e4120100f080d42c0348100c03180f085414510000780b551203040d100c81640c1d1200410441c6c03220095000e4000c20821070602802c8442621301d46445244c102c900030351061040003c2030742c5090562090b1030400060300001101078074162035080803001d15103c070b0480d1500040900055000c20b000c00d00524094000380000c0c1030030000681040b401c054440661035011000038034001d1040150603114080003549080b2114075015200e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 737718678 1250 737717428 737717437
    0x2010e031e0d14130b030a060b0c07031e02090105090703020c0706020c011d010f0e190311040c080106050712091a0c01151202042f041a0f04030305031306060803 71
    0x1290001603500c3c2440019811200d843c54441c28101c0d0302d5081c0b58454210741c20103084580102c0e901c9101044410080c402800038080c2100184000740c654a002c00e800c1010740100821000c28201100050b22000583c40c15504103c0720303000c4a82d50440200c6c001d0040100e403070841c5c401e0345000555150082200d45000d8020b0707a03203a0a407216820130200401041c08907900103400700903500f02c11482009540f00350a001064140d0012000c05640c15081d5290030070349141e07a0124038010149014418900040154204054a989843c401920500845001500c0c99010403a0650943e00c40c44c1544064034050000110071400e0604a10280d0090f2200d0782e0305601c0c05001c00c1c040920070310040700b01d440410005d00e000c1c4140c0d00b80005407070120f030030301c181a0007400b0343d10200c9444440c0e07400030042503500940f01c61404d20303141100e5588900212000400f0001c0c9903000071034400301c03170030b80c0d4260030420b90300d480307100d010400c1d000e5034140500064940040402d14400120050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 737719928 1250 737718678 737718703
    0xa050319062d031a0702070302090106030209040e0115030308040f0c03081210241704031707090b0a2a080d062711040902030a0c03240302010e031e 65
    0x2010501003107865504103025404003400b140326201c0071080e0729401308201075003d000380c41a180050b40c1c030381c04540c40600a811400c04240c010940301c1450800e8400c200a1480000080c05038402c00d030303040100401e450102404000300007000070709018488030900c0c41c0c3c1d944038101060450760781c240601e0701c0d0000700c4211a030200c00804039418400e00c416003020313104052100130302c0c5034600040765401454444c542e010b01081c450940b02001a60585500c02d1380282c0b0f40c031014815641c9403007507400c00204010f05022001d541844080441401d4405021141c20035401c900c058000350100801600c130300640c5403529a10440800c4007c07800b03490300819448003031002d1038840300c03144a4814031078815134645058039000200c485840d0890b00300c910002c1e840c5441c0c1902d07041802e059034001c680640d401600c0f0710701009500d5240c89281000000000768280d040f4481003401e801410f0351101904008681c629000c0981d410302c0403980389004000c1b0f001618190b101c20545030603035580203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 737721178 1250 737719928 737719979
    0x105071404140f210a15020711010e13051305070806160509040915090506010611060a1a1903030806010e06120702102c07080a0b0a0b0a060e040f060b0a05031906 71
    0x5010106d0442c001c1e100c035954401c01c100190f00070b560045a0540c10b0b1110300d13910028203140d1200c103c0883c0704450003243c0c8681c256144401500b0414500002a84004900da00640c108400d0100d480307a5103001c45041e1419503a00c400ca240000c01411411a01908002110a0760b6030f031041941e00540400340702d00141c0e0000d0381d0320031081d607000c0c050310320140d115007101001500d00c2d040717544a070300500320804000e4520b00c08000440c6003801c24144503110200507040500c1490740100096078820310901e007140b92903100c000442c0d964018500090b541c641c0080115404a00900100510401c00030041104040421102c081d070300c042105030714040649448408444000309000c81610b54075030081c9040242a0307201c1c504000000c0106408640c3e601070808287c0c0d810340b144005192a94401040c00100d808000c22035410118003600d03940703080001c2102d0b066107000da0b21450300ca402d000c0e45a40e02c2480c4c0c1c884004003820800b41c000c0c43c10102180559855070620043d0141164 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 737722428 1250 737721178 737721203
    0x1201060e0915010e0f04090c0803030703380a270608010606140c1501121b18020705070b040801021b1f0c200105071404140f210a 57
    0x81561240302e518200354009a4508403c11803410050824904900041c00000303184c40251030b1081c1400b0641c100d0220f94000105006403e030345809031100014000340314441d911103050041c0d406261400c008407138101400d0b44807503980c0e03c485010703008080b440c2d00d801c50110310500940422001c009003c51082c98204082a4000c0520030541510308946030300501c442c0c0198900c07119003144180000900c030f10340d104105500300112190092000100c400c141803421310b44000c00982001c11111580d14096080084038000d504600b11030041c4800183e40d0000c5003001400c000c0b4a800c83c00b040080000d001580d504150f00400501c4008154180420070442c1055142c140300c01034500031107002400d6036803180c200c5d17010410405150802c4022208501c48118161400041c05580759558504005a1031b401246550101c40000281441d150810440b4034004208460031800b440152403c50b420317440c0c4a0310b03140341c0026040000c0030102c8030040b9581e502000b240c100d1b052120140d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 737723678 1250 737722428 737722441
    0x1020d060902160305030408040807030605041e050a0803100e091b0102070608013003031d0c03030706050c0c070e1f0e07030b1309050a0c0512060c0c01021201060e09 73
    0x8295003c1e0000607410800c00304183d01d0803030300c5420240c81a542040c04200c00109400100300000095100e4100410a480d150509611110005209008800c030341c0d00482c0010b03c020503021307502940002929100c2d1141c86c40d44410040581007615400082d03021f1120318480000d84100c215080303515540100c07069401281c0300d101505c0343d1000314424070010f11980e002c1c00c024170307220390b40c80c0c0380ca241c60003508200b080050306104041e400310f580c6681c040e012a0419082c0441c1b002c0150040441d10034200100382d42c0d10031b044000d0b090703e0340c0c0e40100300d100140c981264070654101003141c036410340342c001e074440285065440150b112619007080301d00d1090f40c0d613440222841c2c0756003007550381c0d243c1400350302a154000c0906c0d8880407001400d60740c0250b6104101c00e05000c1d9004011a0b00c80349440381840460740c00442c865409030650103044103001030300f1a0310400f030b01112502e600d40051500d0180c01902400c1c2e0002880100100d1119070003200b07038010032401c85800005440d00c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 737724928 1250 737723678 737723681
    0x30d2307030b0913060b06030f0402090912090d1b080d0801141c050c062b0b030304063b010206100b0919080106090533092701020d0609 60
    0x205015401001c9100010042407030000460900da00882c5d0200744000b6950028220754404c455141c0c400b51050705200660825441c51503200c413413000101031000309554441c2c07550003a94981807041d500c6031121410048444460260342c00f6540c00c070107180352100b0b00242c8894092500308005508100000380a00a0b0360018107121800f0b40520b00c10403020030010640c0c00e120805a82602c500b042e0000d503510b80f20003c0c5042c0c0240b420301141901c0f10030090300d11504a101e0040344608000403488079583c007004540480f40e41d810500121038451510a0034040d26420300385000300707461594805085008500101c1c00c9090382540c4140e0355079200070134038000785e02445015107000e1001001500300700c2e035800001a20f00104d224165500d420943c00c0d04d41d1908045101c644480c103003e103c2d200e030480c60340824a400d040c00c035103100e2401080340c021403d2107240c0c801c1c5d041a010612032100711034071052400000414506814410487e03c2c044d5100040d141505c034500070340082e1120710b6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 737726178 1250 737724928 737724941
    0x30a051212070c150207050c0904060f0e010203100b070201110d08060a0510022113140f06120a0c030b0409030f080106090303050f09180405010501090b04110a030e030d230703 77
    0x100481c4e01c01c6400103100c4d003009400281c4122414452004072440999030162a1441244549804100d170f05c404620030003600c20390710042072180c2c018400d01071002c0617a8a03403010344031100384507501c80b02c2e2800121481e41c40424841d40c0c0c0d026442d0501c10440d0300c07900313192082905850081400399200107000c007070200c1c0480e420058008040f85804d40f1a52211081203d001100a070b00b0000252102d11440c0f2080e0f1100da0170707401c000b014a02c0c03070402e0410200e075050b0480b0700c20b06100345441500414103000386002806036035451401c00c280d0080d80602c0d11004090710812003c40c00745030140080140e80080c202003848540000740c817500c6841c26400356641139403140e081080c8006841c4464100d1003e0640c0011600c410003c0c81491f41011b500ca107009000100b07480d4540500301044640000034540100e04011501d20302c5030000d0b040b00d07942e000c103280000b894040840c1d4035085002b02d0b144440c00d00e0900c0000c3c04500507000c0d1442c3c40c0c8410050088680e203d50300b00b9801c40c0c0303c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 737727428 1250 737726178 737726183
    0x6230f0121200412060522030e1309050114010e090304051908161518030803100302090a14061009030b0703090b13290a0b030a051212070c 61
    0x94400951804a03507540050a00010440d400c40c2a169450000c4496401a80002c40c00004030308000c0b0030302c0340c540100ea400c400240b916081c2d56902c1100c1c0c84500075140c2018051100e150904a81500c9000601114810708881045078202502d01140079000008503880b084841c60004942100d02d1a1014000c2c0c18090055150a181c0340901c002c5c0040c4140790311040c140c45d0301c006001003040c080c05448000b20440b28200d58189115a1412414400400c0800040d10b4290098046400810081d03a4211140c1c50301c0c1da6400c00182400c1c003143d00300940241400e014002d1401003500702c04501d0f052079440c000243c0d01e543c10311891078818a0884002808400200040344c00c0103106038000c0c01038038011450941507168000c202d00c090381c00301c0004e01805070042c00d02040c0c05e0281d8103490f2501811a40300c104541d50450030a01800c031044540e6600c50640e415901001001c00c01580541a55001c0e6800b49010519410140c00b041e80484440005102d0305d00c109041d0300000c3e0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 737728678 1250 737727428 737727467
    0x30809120d0902060702040c020d08010e040f06050c0d0e0d030f0b0a0510050732010e060f071107080a02040506150a050a0504120b060307080106080a0f020406230f01 73
    0xc0041c81c014041d08500d80280d8100c4810045500580c8590060001e0141e654004283c25260340e4170003490b1440c140e002c1c0a42c85441c80510000480002d041d5132255004000480d081e01d800040c2c040c1803055020030085a841c0c0200e54014110104240700b981d00706807800c10440071421000c3d0700b5100010203059000500000500c020b00d0036103160a0b69402d540792050070490540d1318991408014809907200300803458411101c0400710300403224601c0c01800902000c90b032810740d55541c034800340c414002c0c009110001a04a880350101d0340d00f9103269803c0303c3c91195100703101034503103981050603801141000000b9a0704e081c00b0b0144036070802030005c0039250a410781c008403656002402d40400300a81008005168125803c2e0903403113600520589a4504108040500d000441e9025000d00e906001003004410004200c842c94603420100f14400045103100180041c4100e40260003c0310320035490008005400ea454010745805aa40080200f10720f001520740c104161070442095 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 737729928 1250 737728678 737728687
    0x80103030906020a053013050a1401081321120c0302091008040f020d0b07020f1b090c070c0f17011116050705090c090301180803060d1403041203080912 67
    0x4403c0a400d0108503200b1030006d6161620030f403030150300d680c890700031954201c420328000d011900d40794016400070701c0494208da80403030184002030500c134401000242001c00341107010040c03156100c001003550080c510705441040000d40c006d0078103d40c44541e585102e2800210b03920440c00b0b4800c8a440603001880c0b0004e0304400d91080f100520010012034042e01d0000c2c0c0140141c40344d44510100300d02c51401400907142001c0001c1c07428101c80a1040f0f035074003410314450800c51496511500600a80d90703500e2a90783c42c030541d840361040c09402400c0ca002070340b00255504842c2002d8043d18064584408024418440c1c10300323841c4e2042c02004820070402131061381c00c407900c1c03030399040078424820703121819540d00c006440f0300c43c201c50000700c02cad000060315092844d0071320481c2c40100c16940c0ba004031a20070303101d8501d030707020040000b4020209501c010701440b801c40c1481c604172408204a030303681c2e600d8030030760030312203c5010080b008100c40c04041402010045480303444030200e01c8041d401d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 737731178 1250 737729928 737729953
    0xe0906030703260a090303030506191401020a080c0601050310110f0705010b1203131a0301050616062f161e020d1103060105031c0509011e080103030906020a05 70
    0xc000590207030407000c4415419420364101c3e160040c2080c03900c0d68441119562079801d01405980001301207a1040781c5883c0c200d0800b14082d1060303800d0307034064880e01c42802003230340042c1d191400d0b10401818100010440704015000041e445040e03800690a6440c5c002184440605840000e4401c0c0a421824030074010700000303260180c400c1030b0103140042070b101c01a0002c541c50002002408400c0d400000344500c1246040710b8070001080d11746032a6030500f5901400d80b10500040c02410300c14100002c6403d0321a96034a00d042e800c98022904001070072411240311442c04018000340401140c080704942c401e0395540507180011240c4042e100c5404060b51a03440c044008624000e156500040e00001358076229858003200348201850b02480400c4403c151510105920491095011403419460401082080080404242000b945403841140141c0f002c1c1c5440180010000341c5062280f110766000d168141228000c2d180c40c20780301e8440340101c1e203d075500403001c0d00c580d01801c01000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 737732428 1250 737731178 737731193
    0x1404050c15220906080304030201020601150507050f07091406030a02010c0302072d08071d0406020702060706090b060312041806050604080f01050108010218040509010f0f0c0e0906030703 82
    0x44070480440d07240c6402c101c0c115915001e00c0707080319142c450300e240000f80500c0710389100e080003402e5a10021420716142d031340000c2d5509014000ca480310a20365204e034a020b0702900c2500e480301c0d030100036902014040040745650f60010700c10b10301074504018212420150381d069041c0602000750142c000d458541e001501e02c01c2448208404500c101c00c0c0000e20b400e502528514050216160803800c0080d0000c01e0307079407a0464202180c284c211201c10450f0710b0314001240301e0400c0750001091030781c1d950b04040000340151000030390403410004201e82040000d034440918107110300d50b10101615001c05255840d540f451a038069100100001c3c8010102c40142c034030750034100385010400d44e49850204550340c01503802240c20750700100301e240e0700480c2800388038050305903e070007142071000a845045074022007401c92806240c4e100007081400c10700390000910b100d0201c000780017540014230300d900208400002c400002d00c034106401e00629201c05480c0c02403000074014081c0c0e50541d2a40c45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 737733678 1250 737732428 737732449
    0xc0b010f18200a02010b0f1005040608070e031603020913031b0206160c050102250b0d200903010b0915062104060c1b17130b1c1404050c 60
    0xc4454150402088618207180140f2003c50250300202c0c0f44c503401c00500900000c101b031514418103400d801160481d07400026502115060b1034104c69a848030b00d0252034059032480b03c20707018062a9021104914140510f0044034400c0e03030804071325669040c15242030071903c140100010710402515600a802039402035035180020040c40c40c1080407001d44604024000c0220350880210a04206540c0c043c0842c40241050044007585d21701011000846003999010b0103c0c10000403645141d540c1082d400642c103508040d2040c3c01190926003c0c841540108960758465030810b221481c550605088880c084c042018000350074010710410000c0940084520310600148100e50180483c20040001e000d28064840029110900c02c0300134021040003c144081408007211040018078500802c00c1c808640500551134900c2c41c00c2c092810145a401000d04590225211060300d40902000f000e03075812740e004101d2040205900d211070581111b0242494014182c101c0003800c1210703c40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 737734928 1250 737733678 737733701
    0xf05030a110f061216030b01020d140703170f060f0d02030a0f020d050d080f0135010f021b0115030b1b040302100c05060603060c181f0c0b010f18 64
    0x9504082280e48140f035600021140c059203008032000c0a41703145c0c0c2511410032268802c0c40a08a007003094080a010040c0640925000c00400106142032620404400300030100701d190310781c02410030344820101d0f15425582580308080134040d1180b6071820b00303520911154060040c04055000d5100d03015140106502070382c1000141032040c0c005007060100042038203003071f20307181c0180c00d05110310020204141c02c211071017900303110301c202c102c0940b500d10b00c0914051309881c076000244600d030f5400760200512400c6d4250000c6050300a8a0002100003000c403c0342c4020010895004010202d010b42d611004d880e440501c0086852480c403881c400060000c60b00400d4a019507075404240b42081c0449280e00203011003104e0410014140240385d0810403c400801c094207082440002070700c111010502c0c511003903658041684c03118600c0300d40210144103a003048445822014103100d0307454004031800c080030400805c504074908440801e4941e0035030288003404005400d02d0003880741e138042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 737736178 1250 737734928 737734939
    0xc07170a02060f070b0906040f110d0c1419050609120102070c0b1207031a0d0221010219110a060507021e0705040f05131704030f06060f05030a110f 65
    0x328405a1240340040054803038a04510359100002d00300a580d00001810588032904030100b8000070400c15090840c2c1c0d81e0308400d600b0302881070000000c0e0085103000c4003d010015201c40050140d5505600440700a4281c0d881c2ea60708210705070070326500413180511076000c48188407020240c1440e00100040040c400c2c0010320b03240c1151581740e04107806612250707486c440060b500c460b003502844940e411200760b090074040324407056901109910200f41540c09003e901c804c2c00c0655036032002298000124032401d40b51041d81040d002e0203940007010240400d8a80800d50703095505c0f90800c034007650b01040c05445075003030380d99448002c0c02c4042c3c03034401148211890007080e112070b80310800341201d0a00040104e1440c0405000549a40c5118000143d00d04810000310790001511140e06917440f00c0401c403119100c0301207403c0750149800182c00c0c01034800410341044450341c0319509882022108680c09641c8004050340c1da49603400c000e00514901134128042d00708140c0c2d007407603074500411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 737737428 1250 737736178 737736193
    0x31d1902060403080c030a140c06060609031905010b030607170c0a0e1c0c0504020403020a0b03040309080a06050106180302010c153c0b031b010c0606030302060613020c0717 76
    0x200d13903400750000004041a41c0000030f0319041d0340d412007110988200701820090900c640d03900401d450b00310003003da80c090400001d04040594051040b0a8440d500e44104042503030203040c41402000c01103041400ba10490703012030b00e0540160719108066a43c4000101c003a511240395020039080f19101000703205440701822402c2e40d0340d4841c440c50a000d0005942d4010fa0b42c00c1c08020100c00394085801988104020b1015031908654041940d0031041e1040e9291500d01d011580102d182d40030340441d0003101945410810b098001c00c2c100c4140395540c04000580807020072401d500b40c40001d004c121039202010000b0300f81221984c0720b451703e000014549031214000e25821400c5404110400c0c07501d8020400e0b9080c000b0b020320502103950040180c0e005031800300ea0360f8030114000040ea001280054146a841000544005644501d09104043d076914000e542c440717096506520641c00c204404600b80790741d01c01e6411721004a40182510323403a00401000000c2201a58540c9009010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 737738678 1250 737737428 737737433
    0x230604030f02210f010f05091b0303070501140907050306060d0204050405010e030a0f02011103070c020105030919080406110a030801090902060702040c02060f0108010c2c0406030303060501031d1902060403 90
    0x401a2110742800141010290b100c1c4c10500b1201544039103000580741206200b6a010001591800d420b07211a080302050078a0f070002c0e00d1405010380041c030540c2403000c9880d031104440c41c2035024880d02d00407201141d48440405440712404c842544d00412800d80240161400340c01041e0086e001d64000200064814a41801c55100704000070200b89545100101d032a82441040e028032034041d00f0f14118288801d00134289250000c000e4100304000c40031950785a000d122100703405c0c0301c00d03596211841d200c1c80c00400350741003881f4420220710f49103603142d81d40c07001103a1102d40b13951541d00d801c00d507802c01d04030000a0101d08801d1317800480611841006071201e109905001b516a00104001d02c0c001008055240050f000308a60340d050604400100c4d8202462418800044903000942030201088070440b40303059401c1540070381010300000c181030f0140e204800b034500c2aa001e111007031400d030140c00d00e008203c81b032401070341c05405c880000710703a0050301082d5988005c0c13240740341030b9694 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 737739928 1250 737738678 737738719
    0x4020f0c01110306030f0111030615161a0c03042102030d0905010f0c0c03022d010c091404021201030609020114070501060806070c0b0712060b0c0106230604030f02 72
    0x7026880c02c070324002041c408145401c1201103a400c0c10400280008404001944039500000e000e0901824010085c01d403060074117003d950170540a12421420640c090426580141c841c001666180b40b0040200d2042e410510482e44125044642c1c0602c00c600201c3c005030221901d0201c108500040c414001e5107180d07400751389602d5020b1000465031016a4030258111425001600280110082082c00007500420304813114200c030304144101c00c60300510039041c1400307860925855441c100104c20100d0300007413807405132600c00500c100c2c98805002440120312950103078060a01c0b403800108005481c54222000740b610615200444001031601d14940e50070100007114582d46409084c080d0102c01c200e2964001000d1a02909040c915100c2d07284613240980344a00700814001d00c1c111000b5940c1240b801804c82850b21581c5e1119445014000d0095000b042d00118405680b0340104099800790780d010180244210b25041c9180d444041580075580b04a800c9040d605005143c0d0200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 737741178 1250 737739928 737739941
    0x181e030d060f090b06040806070e0307150201090311010b150c070b1219090b04110d020a0b0c12090102060106081b040308212509170a02180c030604020f0c01 69
    0x2c41032040c9a00341250b06080e80c8107212418020f50007480100140d1070f001985070313000140c9080c1144010340c10008681441c045411251102c0d134040000040c0e46d40c15403205010780c0c0a40e907010b0302e0304c0340713801d00d03d00781c0d2403d44100f94001d107514080c03101050010024201018230008442c0c190340e480c0300d14515600110000100c10f1990800c00c545800e0111586084d080392041c01c01400e80c69a5403540d6900340584068159aa284804500d9484451401d01c01c42c0d00180700c0c0043c165240b51002e01640061030311041c902031605003020842074401901e0405a050300500351a83c2031450031039020000516881403085540c0400b8202e0000e04018070241d4020350103a541d913020a03c48000050302a02c4000d803403034144082250806581e800010101e44c00c3c0742c41c2d541070554900c00c0310000031940110000c0902441c41c5001721030000b8900ea400762094980c42c04034055405106104030040b01e0740055500d04000254041c60283d0082400205410380703503017040f82c1e000800303003111036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 737742428 1250 737741178 737741189
    0xf150c011b0c03021209130506010509220e03070b0f09030d0204030614010e090a0308070e0301060905090f0d020706031e050702060a0e0c15030705090d0f0b181e030d06 74
    0x2081e01d0b4000506505020f240c007040a00c006003450408001e010481c9609012120544aa9680c0100c1c48603032084048aa135000c000303084c5413070111800291050042500102d2898900d00707042e00407602800700583c0e62040e0008644419580c45c006400c280074401008440326000c20031400c60610031a01c0900007850081400244510700e01100040310401a04042101c801d02d4040100642d00024900c0300c096051412100300d4981a0041d40c4040c05915029459420030384040f8a0703106581c0003611518002c011a245014034143c800d40f03031000400c5440050300130590034048240290030180c1c101c4030003819400d80e0440342c0112011a0400d60342100180c104100b80840600c65001c0c180301000d02c9005483c11000441c001072241d506035184410f00c20011001885003030045060301da6090005d821000c1c40006450710548122900e00304843e07542102001c203e03010484980902c41081020003080c200010070400c61060b0100042001e50348001c00048002e01403030700890000b400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 737743678 1250 737742428 737742437
    0xe0705030f071416030e060c0c030d0c05030a0807090e0f06011409010c11040204050405131403160f050a05030a020f0705030c0109060c0515070804030e0f150c011b 72
    0x1d150221699240c4080c080c0c1c01000812082d800c14a60f10310110b07000e1480111081c413624140d450f068407000d10308480c00da40400301080f503800e00d41c0e000c110b030314071024120140c03100c0001c4501c0170780d04c0c600901c4010705254002c0c00040302060080d82e801d50845028240010b51640e1040354500704030b0100d41415602c0f11541c00d01986580100e03007059501e81d401192410305140200091045004080141074082e2414020381c1f162101e904442c09440003901c01d100034031740b103040300300100c45030501180d1001c0c1980880c1e4007901d002c81030300c0c00070781e00c0308489040301a20b44440d2902c2145d100e041e41d10340103170600b100000b00100014070780e5074103640140c1805a180041d66043c18a140d00a9010783c00400c0c010416030303800f12119055480c24103040c81d101c103640c10640d00c0c11040b001d04460407080c0005101c803a40c1c00405051140e40f1943e1030003960391040c000d03c580c100d4a8200b00c0d401c4580c1044010500c10300390098070203120031030300000c0d1080c03140c0c640004000c1c214100c007001c034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 737744928 1250 737743678 737743681
    0x702010e010c0f02060609160f1101110403050d0302040803092709010617070f090c1106071701170a02100e1c060510080d12020c010c200708031b070e070503 69
    0x8940601051b42c1c0000c00316400c2c481c514203251030040c00d05003160b045007000b128800554005008007042480700003290000c001081c00c5035840107055205000549003845111181c4000620034000c47d02070303400b400091070a00641c9000d000441400b412090711900243e0801045420700d000c042d0702c507002c2400046400780c81c0046001c01d2510246812210b074115031030910800d58481c18500848031484800242c1c00110074044880c01100c580c21902c0d8080c81c0140120a41e0003504a070440c1d090307150009403a662450134508461200800c114181c00040d050009131422280c2c90200d80c3c1d050402c3d4851072010300c0011082500144aa0349180c0419440c0c400d0007403d04c1a103601c015010510044035081044903560788051000e140208401030740c0d10007400c9469019a00664900e1b0003e0058a00d0404003902d080030340d0014022100d2106413520881c080003804008490000d8082d610b440e1144554240e854890700340001188a07074040018942c1900d10102e1081c000d035a035241d201d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 737746178 1250 737744928 737744957
    0x90905010f0b0609240909100e0a0605090412090b040914090102030f011503150b03071101020f0a0c1407030311010c0e092701110d11040e0f0702010e010c 68
    0x40b980391044142c000d42040c4001142038a074801100300740940400a100d01080c1c420480103203109020b1082d411100e2403003480344803818495024185c4203001c1034000030b55191041d03d41101c4452003543c0e4040b030380e6004180801c00c1e009107181d10820310b290a002064599188915075802580002405030341d8890b4148400a001021600551044000e40c95400d10048100300040c040c090041d110b000e00418204a60090f031100686840d100310101d80c1070341c0c1d50140623450308111034003008550040300b1201301207010f1084030049801190102c0c10195030300c2c2d080391012000e400440b0381b0382180316200b0710140c04104260045119541d90503149260300300071802e44108000460501c04110580707019640d074450f8a50b4001151415010101c003081c602080590844620060759460b040b610303140c1d074441b00010814031640b580c041c4846964100c00540074401d500c40c0728044440a0041b03080d00c0b10589a403500314601c0c4c4000304000880c0c8100c3c90850702c403e859540410841c40c000240c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 737747428 1250 737746178 737746181
    0x807050a090203061005031302030703140c0d08030c0d0f0e01271707260c070611060c211302100f0c061d070e0103140604110415090905010f 62
    0x1415281c4010360071420b008000c62607074142440c0b2017040c018003000103203030795145c0c40050f442c1d260010221404207a59050081d99a05107410110690068100f0017045040ca00c5281003904d40c81200286182e407a0000681d0f03c0d00100c0c24003805584610419800310038034019109121100c400001d244d188075901d600044410038100d00c4210208050340c0c1c0419038440202c00c030340800301d0403560f40f5000c5252004002d14122880d00940440c00803043e851400c0744041c11300105413004032400641c4561003564850b0303d6405250035648000002400808a1000b5003800880c00c44140900d0001c6c40c0c00280038001240e0910301a08030000710340c1546801e4034809600c840600b0212104002c0440003840101d8070306002e45083d884589032421000707044000701000000d00f06851840c0e0301d4540554900100384010f441d0510a0b001c0d1558941020944074010342c2c0c0a0310400c0008541d500b031201810107114004c401e400c0112000580341581e0159404441c0300d032000040c4601c800032440c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 737748678 1250 737747428 737747449
    0x3080c07052416080402060304020607050d0c030324050f120706030b040c0302030402091b1c09140106050d0b1e01060c02100912020d080f0c061005010f140a021204080705 75
    0x10020a81001c5003913400c0000d460308a0740590b08140e403560340d8008548544141035004000788968403800d00c0c40c43e0f00104c1c8002032403203a036090201d0548002880f00344465410000701c01c03080d01208100d2441e1054002a400c0c401415007244210030780141030074640c0d182c1c01f01010a4079030901c50b81740d250510441c4419580782c1011411400c0039008280d2100c03000749082ca0b2200613113201d5030b4100c0c204080d184204409496050030103002813414001c0c144281040722290070040d180e050380203043c00b0b800150780c00a0700383c0d258401c058555941040c4040d010001071800c00032241502c0c3c1908450034007030146501d03400e040c04817901c1030041c030111080071603040001c0764030705004407820028401c015580446807a0000c2c03007031b4101004103100f1305565110590300040d2000c1c8202010500300e10596680d0b0201010540e02c03401524034000071170700e540000300c2d681907280c003203643d55014006801480c41107031684500700c03104040c240e209400c2a1250340c400071080006250408558 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 737749928 1250 737748678 737748691
    0x4030806060f0d0b0a05030610140307210c0e16020d020c090114060909040f15050403020c1003090b24010320071a04120e01080f010303080c070524 65
    0x3440c20b000145010200d0281158400c2000d440d010764010f156521544c580203001c1c01401d44020303003098054400020032621980303e00c07a48003c00d0080d00d03d030102d041000c481019030300c450221140c00e520342d84603407040401c6500c6028254041800c12050a0691103003503c800340b10495191084040d1620120301503440c2107600415640a880e00c1d141c1c4000d04448031701b4206401202601d0000380d6034000c842c40d150300084900104001c1c0140400340745e94450060b81501103001c030340000035007910713412074000d005680300764500459410300000c1c511868105103000201240140c0e00d10401d8102940c2d44080d810740791a845042015481c802d440e00b00090030100050012448854448528100012241840414074200344910079181910313a02d400782c02c00f1014079051818031801c002c0c15864000050700948500e14035405021298000c000303c2c00020382507861030f6022607903070b88010080a40c1103024001000090400c0240e0307032508119943c1d403042c0492500340c00680d580014643c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 737751178 1250 737749928 737749939
    0x70f03021503130b0a09051f060b0c030f070c0902030906040c091e2d1a0a03033c11010c210e030714010b04060f051c0f06021204030806 60
    0x6010a401c0030040d040c0310f1aa01281c403065550381c490f000700040c42d4540000c0c01c3ea019401d0043e086480d19818450f0000313010604016039a194031b6142d5682c052148140d0250788200001c101100306031b0040c045562040e00e05494298071409201c041e0380064500c2641680000148020040904403d00c041c140840042007000e18080608000c00348101c23410059503682d01c04607a201048650000c0310301400c000c54050302100301d03000401089000200035001c008151224801d103010020841201e13090f40c0c41411508500c819402c80300c010100c0c0380000e510540214440d10341c5210004500300c1c06032901c1c00e00320750307004c2000d09407462186070408100e0f8040381e0261050700d04612401100d06032400059000303141c00c6030340c65803081038030280800b0803000c5040030f010070540168032a603405550504c01d2079a0760803142e400c1c079102d004941d4002c03190064241c140074440b54840300b05001e90002c41c04040e40d5203944040360720040c080220101d03000208010705030840441030b0020382c251071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 737752428 1250 737751178 737751181
    0x3030c1d03101a09090307150b09071b0c141305220c081603050f0c060a05070206040b04030b010e070203070305122701021803070305030a030518070f03021503 70
    0x1e48a8200b1200c9455039680d0780e1104152810511403040030b0440501130207010700300b203251903580c0c2c4c0003903000300c0b4102c080d6520150245c0b200d025140d0fa00c00b0103408013a0395240c50000b80c40c030540c0c542d03020030310103a880d034240042503480c609000102840031040d400841802d0522095410510612404c90b05180a20a412017500c40c8440c03c900a4101c5419944492420301e1452442e40d0007001c0d5480b4034488450940711000e002411203124504448803100308401040d21007600d61030083c0e014405025000d00d040c0120010f0003182c1c0f00a0049241545984581d0a15001b03504181d40006001e0014802110071842898001e00c03940002c5041c005c60f640d004119114044071000b0a801d610f011461401c034078130503a502148400310103102c0d642c0604880b0300035085401900411204c0d0390452230941000b04034882640e8000c8055464075440f1007066026081c083c1c01070440511142c1c40500740e50081c072842c00682840340100021a1a500420051102e040b0001540300c00400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 737753678 1250 737752428 737752487
    0x318070e3301030b36090c030d2a063c0f0603020306040516050f0a140604050a0e0910051e0a180b010510030c0906111903030c 56
    0x4030301d021080c80900c0c0c003141500825000c180f102585440d2403001c107940b0100c0880751540041107480d03041d034665100d2019600d0000b80b17940c420035000380d1601a00440220640e0912601c5d903250b51501100d00c0c41c0400001c0d1420150400f14a1410743e96682d0b50000c0b030340001c5501d0250300b00280d01110b00c20040b044c49080900641d9040b9000d021a5a2003281082200c480c0d0448002190018180d440c01d01d41810001d4a900da643c054400c0c56040c0400441c0c14134044030720204045004d40a00101d82c10841c41a29038a04002c03030b44d40c450414800000c1568a8200e00300241600345200710050400d242c102c1c1c544105401c13116035403400d000c104406011035031050030005501c031300020075640360925160001c20906104140b0540180116401d110740160604c0c100c85043d680c2e58032090a4003011412a003a25800e800092030300d8904100c000d10458100c200a160340c020307181c3c102d000344240d10501544d1a800c401182e2996509162a80c120704040220b005ea80e90108601c0b85070f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 737754928 1250 737753678 737753761
    0x2d0c0108070c0302070b0318010b0a21050a020306040c180c051213060614090a09020105030103170f040e060316050907050a09030b04080408060a0204050102120318070e 74
    0x20403031400c001060260303006152080017550020b00c1082202c1e5941e08044000c4410f814000c0390a514942c00d00c01c0300c0c501030504030f01c411704494a8845c800f0021880500e01c0c1d00c50369042d40251000e101340b421407405640e00340000d0380501d114511002500d450a640b85a050450780b0b16100943c0c50990b1038864503400070100c40b400803010b009a645a81c8900c0c6d288003545420301c024100b580340450200e40c3e0280e00b20aa4100c40c4111801c5a40340c3e1128666020f540036000300a0008209100400001e0003003800803644041c0c0009441c2040421410464180c01640c08042800d901d201440070300e040511881c80c81d5074200d072607151030740c0c146000302d441e106025040008000c1c0018540c0340c0d0350f210f80410360185500070305100d0300d0700389414511f01d039030001d00500d0403a020f90f9010600c0f08031288222000ca80040c1c0103043c0c03080d00034400b042242c0004010b40001d40e00c0310b004020a92051020318080d00342010025045e05042d22040061402d0741081d1505542031104505902c03400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 737756178 1250 737754928 737754931
    0xc0307090906120206070602130b040501020118021c02180c0d14040b1504090f0b0a11120708040f0219080d0c05070b180a0305010902191518082d0c0108 67
    0x55a1081d61b0380d4003450700c60000d21805402e000c230587e00840120752030700904000c1003110400d0f40203012020174800703174141820220400a5110701c0c02c210b40c48000100c81e0480038079074001020803c5403203038000c240c88582c01c100e416072102c11000880504074092807150980241c08170340c2d8031040e8903095440b00140140581200c1c04009007100140d65661545c0082002c50342c45003682006002c645054004007806079181e2211781c0c14400301015801d2a1020f0300c0c0c40c0d00e00d100e00101552141081070f03444940140041e04d110b804010801d015844d03003c00c00300b403180d511003a1401d251070050010304044804c0351207000c02c108180e900c008078900150100540d840700c1d00e820354032024454882642858849916040780141d0000018404191f1100314018000e0b180000b04041e0007404a502134034601136007003031a00324940b104605215203c4d890400300c440c401480c640d600d85180e5032400d00c4583c4801151071510300c800081007842400181110a548010280c1440040018149070030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 737757428 1250 737756178 737756183
    0x1005101b020405061c060203040618080720040e0a0606060509130e1c11060603011404081309050a1e0b0a1205012702040c0f02030d0b0f090c030709090612 68
    0x40f40c40129060f03668000901e0003400c24030000b10300040076443c001c030107500211016144035140107003103031a480c1c8145400c03000c01c1d40038007014606251581e840002d0303890341c0c0c0010150700703484260b40541c5e11144100454500414010031400000d4900b180c143c0c0c0c1150000010464140b00625407600d59035404a081c40e00048045603801e14411100e207000640c4022651a031807032201400502d0308110f154900f00ea989081c1d80d0709030b4030242414282c80c6040580e281d0030007104001408111203001410903807200404552300a6618590003058070820b6070b00c505903270707507404101c0f882c130000b010700c1103184101800500010f120f050000b944003038284554050b400c02455403038100030f020340c07004c50f420b0161466051100c6440700e04040034900c1c8041240a50f14103400c0103020f40c080c2d6182c1c04424059801941b07441d1400407140040c1c14148400c5401030041c580320b82460352003244507846886280303a09a00c1e403078000002400f03c800b0343e10458000b0310300401449810100440b680c4941e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 737758678 1250 737757428 737757431
    0x3053402133e0a030608070f03030804030509011e02061009050405030d0903110f16060305090606011206090908030f0f01031a18061305070b0903031b010e061005101b0204 75
    0xc035603001c141c1c1200b140d4042c02c070000000050540105030141e2203101601da00108030340806490304100780044941d0300020700400c012900040c0060b04c98401040b006c481031520b1004007415080303e5545a04021159000d60407100401c44c0850030300310208010601158188024202600e03007589a11a40342241c0005848182d940240f5000d292800a003181d410112241c6182c1c442d0328039141c409145031182a000a0300d80003c50074400d0281a0044c000e00c0301034250703520b6100040d14040d01c412085500d86844080c0011006c416126582c032140c019061190380340303040440350100c80c034001e12160304244000014004500c0c0d40f8401d06c034074010014a5860350f105c894010664100056040c4164800c15003000300021380e055000600f03610481c22101d403d500c44141070401d01810280d96055802030080b210842810145090184900c100000708440b070034140605103241203070000240c0c0d900c540e0800c0359080c0f100c007501c1074002d036140180e0040c50042c83c14641d04810040039206a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 737759928 1250 737758678 737758751
    0xe07050f0403020f0f0a0f06090501111c1b0503040f1203091206140108010e120a0f2001061715130807020f0307180e0a020307030305340213 62
    0x580b0341301c821485c03480c401494214545e80e10641e00d00700001c41e02542001072580350340024503501613104116201203400103071110340303284c07055080703030414100ba06c0040002e28101501d100040404e046500c0d4040c001465403982040400c030618059a17100006214443c00081c01081d8010081010759446403030b0103503019801d04142015011141d214501038028038000100100158404524540305a042d51b01003145003414100700e01a65040720089541c4286601d0300522500f882024840d166101d80c101c0a0090301e15400c41f00180c00901d0f82442d40d01072900a21000c015094041044820000e0540f600481d1100321101000e40142500700114070b1004640d9990008410040b0290403291b0309541c0d00782c51003e400e209900014a186011039050307408002103035041c0d0554026000f0b0142c0c1c0d286030b408460341c2c2e000034501c0c80c50358124003407084150408440c24082c4480c0a00b0103660300c150303004000b000b48940e0900b50020b03140c00d4140142c04810459203000000d0b0b1050308025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 737761178 1250 737759928 737759959
    0x30303150b030c0c030d11030601181a0a0203121f230d051c030c09090203040206070b06130c09030b3405070501060306020d1401060519170f010e07050f040302 70
    0x1c50040c941201b03107142c00d00e2401000a4218000f45100344405d0342d0700007030702c40841c402d100451814041d0040c562900307890030f44140c80380030040221440c41d10481e8a4000c1142000d40003a00644140b8a0800080c0c005900c030846408a0001707032000c10702020700d400e18407913144050400092064010a0002c803402c080c000706001c0c07903805007446070f00c4c03000302034403640300030001c2180d0499180400c8288002241c01c180c0ca00c00d49100c0d41e8082d20300303460003d0585070b9480070b41c0c0c0140081e502503070406404625280c180980061051940c070380c8400d040c01c5140240f01c84130001d100d003201c0078103e88107814402c000c0a0410692802d0100c003071601a0003070007128541300b0000d0142c49503003085400000c000700341e0300505103c1c41c210b0040103480020000300c04c01000a103d004002141841000314829001c00700e00c1e0711044500b0041030210300e102c00404050007c0714030a0704000f101004006451101800c40d5111003180f8160381f525008042d0030000740180c0c080a4003401020b50804d60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 737762428 1250 737761178 737761183
    0x3060b0604090e0d020615090a05060a0f0b030f0f0402100c0615060509040b09040b010b21040605100e1006050c100603120e03010b06161a070207030303150b030c0c 72
    0x16202d4101c0903c0320310314008240d60f513925040d00e928014810f090006e4001d411030a0b1b14820b8030b02c018001081611440c0200740075003400b5111a40c00b90340305000088001008500100401040c0d131500d03140d103003000c044103540000501c14541fa11200c07041000581d1031040701000d69505090601380c507072403410041c009000f642043c1d5100360301d040340440e2258000000d414032220469051002d400e0319020304c01d04410503100106040d5201c0c0050140022140150100c40c0c1d60000d428042c09004000c800e08040540701a0f440980d50414444420342c04840f0780701410000c10102c100f410211070300c25090f80307944503610810401080c0b002c66100c0c01c7c00302c03840c401340440081c4892502d03800c0000d209002c3d0618040814400f008140c0c2c0d506041c0180301030900020009418510034031403001c04441440000c48903403041940c06400c001e454500d40e4000d01155006020785070452074050100c3c0c844081b00c501180711040100202010182220750029007846695119100807a002d403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 737763678 1250 737762428 737762437
    0x190207050c120705090a1b141312140c1e0307050433050a1503090f06050901291216080a1713030201050a12231b0403060b06 55
    0x30740c80359980d4042c10b60341d000020350300b0507a0070440d11081c43ea240e80041c00c0403180850900c441a010300c605202d0b0b5540141085498110414511407800c4090b00020019046640041d01290a4001001d00307020b03841c5007030900d48c00d503100242000e480c0c3e10000381030410140307407003000144149821f0000c0c0d101484190000c3c40c002d0f20600641c000082003215138080b0240110000c0c4502004500b0840c40c81280300440d08041e000707203407150a0060080183c2d01100f6100145529030402c20001848003500200f1140168400511800d0a0071302c5829a0f20240d403844442c1448031034034440d542070302180ca8030b20301c04550560f41c861071002e103182407649814100c65040d0300507400040f80000841e018801d244100d0710b090240744207140d4983c4900900c00c07030300c0c1c0000012100380f00650184004004440407810322a40d1a02030701900c400b900c0f000104100c007031484202c41c146900501c0384040d040030544819070010741c55001d0b640b60301c1c01144000f40a1640b10404003259454140858 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 737764928 1250 737763678 737763703
    0x703090c0b03250801060f0504170f0c0303070818030f0609011b0f020c0103240603150f03240207021008160219060209120f0715030519020705 63
    0x286181d41c85400c00c001e40c00450f04555039030040c1c014040a049001964918180315481e00c02959091603030031038045a00815440500008020106048600510014035107480f03030000d004844507081001e04128140d031215000790300c1400700400062500054840d000ca0442c4411400b01034607002900c0e10100179005100c0c3c1c041c500c10f126030f15074190083c564800000d4015500740100030800c860700304680858400680140103040c1c01c540c444d400c400107005002d004100006038200d500004c45030300d94448400302c0c2c2d5821902c0c49070313120a40304a00a0103118a80b000213850760300c81000601d1000380c0341e2400d540702c0c002c1c09140da0301079040c0c410310760300035240c619801012500903120090076a03a10600b203600c62420403585200166500e00c0000c403003114201803a0355034484000e500700d8034040354441e025403a030244403003082002001c10102c0e04024042c0d40e1130901002c003200e4841840500301400c0504006940002d100d01d040c0c0303d0f41a0200681d15409400e04504100c0b003400360 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 737766178 1250 737764928 737764943
    0x1a090a0317030a0b0306040309030206070c09050705070201120615180305060f040b1803180a0b03131a04020102070612020d15051302090d0f02010c0507081501050d0507050405070309 80
    0x400680d000c0700d0003840c40342509010030460300101c18109980e640e0112401800100110414801800c0c10b03009005142e1041c8a2041074a482d4254601507075030441d5480b0000d03401003842001d644e0310880d11203401d50b081c401084454140003170140d6000c81b04220f6424800320800303454000525194500c01140c0150540380a030500c0e02c00bd2246102c10303a0141c40144094000c5090005842c040480803581c540c001c600e01503402810200303040c24800c80c194082000c0b1800030384000250029481030400944210100d01546010541903800881c04094003040104110060344c00040c014159045400c10358903607240800c4920103031083c07680800d600b030305050860080003520000c0c44155101102d1101e0880114014481207000e4588400d9024074062282004280310241072840207006260400c80c55185480e100c0c541790080c4d0000085901041d4002c6104110b0104280500030407a07150045a000f0342781c4a9540c0c4290140354490f48d03868002c103400d240254411201d5a038803450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 737767428 1250 737766178 737766203
    0x1c060501140a09181e020604080a0201020114370c12051b09090405071e0504111207030c2109050c0603190506031e1b03071a090a03 58
    0x10500500040e25448074011414a200882c07540800c0c018040c04000450004c1001030182d251130004c454144c503120500c2d1040b2519502507280d000080016010703400050100307040300e1000908540700c141800340c0040b0a80300b48060583c401012605100c0e101c0c4c41d003e0091402040c0b2486002004007205440d8500030781e144815801458464090070b1640081040f980c49804000c5101d0115004600700c0204100c405110300e45070200a070014003882c01c40b10780a86130707050b01d54411071281c4910110b0110240800451502d0b0094405111126100700c0c180481c40cae0310b40943c40c101416500038180c03105020818248a0070901c0390001d517490b250101280c0cac80304404001d1203000403e0704c45008107844c0e9556420050b040b24094010f0b4225915405100d401410003818082d02090380340c09005022401203202e4554404690042c8010b0001d02d1100c21540603000c0c1d9200207180070703030045102040860780c0107c810b4a24a80ea0080a544020043c002a12401c00f070300700400c403402941 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 737768678 1250 737767428 737767439
    0xf030c03041e051e010204080703020415121b060c08030f070c0c0f06090f0303050a0f030207020a0902270a050d15050c13060903022209120f0f09141c060501 69
    0x100700136407544000e1541200b0071251002030a1340305500480046910000040006040c6948881c0300b10b00041d0706a030701c16450342044150300c030240741d064035109400c256200d01c840c000000c001c000d01c0e441c100b42c43c0d002d1450380ca800d0796000003400810098152030000344224082c041490400d640035124506090322038440018120840c061940010300610300800d14404d596a10340c1503e400d41c890310304094424a049501215000000301016002c1c801407005071503000e02c0f03d0150854840140e102d054400240d940440d403d2149900540c0400204101d0346071324000d003003503c109944403a9140c07081d0502c0c91020010442c4404000d1038903007002018400f003405005222500103841000a030789030003c0f1600e030000d00029521400320301c1c0948035500c840c0c50b4a01a40c000002c0480c00345129162108900d500c03065200102d203044514140843c0d004548500c0481507040c20405141801c00d6150b4603d084510a40240314801103001115100d818000b071075503100c2d1040c081ea40c0c640 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 737769784 1106 737768678 737768683
    0x4060e160804230316030e010e0301021e0c01020f0d0501030303060510021005180a050607081f17030702130608100204080d180f08010b12030f030c03041e05 69
    0x200175401620401c001603115071406071300c40c20400301131980090014000c03040468481d0b40b04015501d10340c000e80c10442c5007440c482000315158002c000b07403940240b184c0007180c1c0d02000046052101c2400e1504024141c1c1d110760b4040c840641c4d03950500007061480d001200c05a080b0030b500310b13041030781580f109074403140c4d00030b10080ea8410f0422660621001d030b08182c0c6c15810540400c86525002844c540d0880e80105826182e04644401d10300008098090214403061440415010130340030001e0358080c1c0c1d00200b0180100b01100004002130205104043e82c902440d00e440e10403040a2094170101e5001c10050f2944068600c1c1c120307024058141d0031a04030b01c0c01100410010010b24030f0b40e000c1c1480400015141400700e0030444100d001d040c64205543c81005500345000844003601d4014045040c81612502c0b80c4c9020200350404603000c0004851211060045c800300 = true := by decide +kernel

theorem cover : BRFrame.Cov 737589928 737769784 := by
  have h0 := BRFrame.cov_init 737589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 737589928 ≤ n) (h2 : n < 737769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
