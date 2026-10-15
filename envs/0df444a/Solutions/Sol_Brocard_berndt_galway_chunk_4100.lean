-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:34:03.981129+00:00
-- url     : https://prove2.me/submissions/ebbe9c80-5955-4e6b-a9e9-26d1ceba6746

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 737230215 ≤ n < 737410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 737231465 1250 737230215 737230231
    0x3060501030207050c100e0a030c030b0c032217032e0308030a0b0f0312040303080c030f04060b13061409090105190203270105040314040605041418010e 67
    0x854550700a2003a1a0415004801808160701031401e018035145151420701c00d11205c120320013019902c81800002840c454100d50182900c0c43c50180461030000d8000329103c1814410801c440d0407803036075034840420118810060740c00f0783c1011074000c0744400750005040c200000b04491141109068102c0c558901c41a90b4011580384a4403080070260200502c50700c401c0000c02c0b45046a074002d0808907030300521050301441d840001a00e05a01914804940e4602103020814503030042002940084400a0140f0f03520b000d1442520080c0300810007800c1c1940ca94030070a060301c0e64501c10070041320500c1c1c10411580c840001003442c0c000c0024039071103a1004400210000010300501c0c0c05101402401c0840340e402640e00d070040e410040c01159861408001c0c0002010800021481008060000181c46c1400c0c24010301120074401d100c41900b404000c2040340039884412141207446080c0d007110060400170000d044965282c24002c08010108000305110744082c908901a03014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 737232715 1250 737231465 737231471
    0x409090537110924240306040f05010e0103030f020d141b010507020102130b0a0801030f14030d020c16080d03020c0715111b060f030711060403091d0f15010210021903 73
    0x146134200420302c0c4121104800d42c0c4000402d0460500611016641012004201007401024100c500341101c000f64490341d109003e02c0f0040080c0340d00300340b002d0011000c501c007405400d81c80d1f0a0191580d0203142c0340710000c100000e40d1303205110100751003030601c4d140d0328000e1019051980c4000e010f500701d402c2c8c24030441110000041d01e03408420450b0295a032549445102e03070301e551a00821101c00e03180507a1000b18200301d200380d4560520041c000d040c111400161900381c40c20803185030000455500d03084405603c003d200907540040d00b503100700e03540d28004d80d0b41e40d0b031140480d0070b20460750300071003030610107000c4440c01d40d800c06a001d1284206c401101e0040c0da4400310083c1c031520f821007145c0c01070340410640005d245070400a65000146042c0714034084040a5131074507040040301c081e8006441c0042c180007030a004c031000741001d905030a203100e85080001081c00d00702d50190024041300300b40c110449241c0d0082c00301c4010700070f601c0401c5484254580100d1461038200c54000c1c00a07103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 737233965 1250 737232715 737232781
    0x815040e010b0312070b0a050c0f030405010204060e0913023303011e0b040501030c090b030711120403110f0102070305030307020105251215050604090905371109 71
    0x4228800c5d00c0200303401c40e11814507919044c210200505001d40b5101c1585030411040b40035245003401503001c0ca124030001aa540e24100c0018401281c038200148171f00d0000302403016030300d00510800861358040f10b107440d40c452400454107409805030314015204c031005407201740041c91f1101a41c1242c04402119800748024844d10002c03641d9401190810b00040c0000e001070b51190744002d0407409642007640c440b689518001c1c3c1b00d500122100303c00a01d5005204040700014400c1d0700c101c0d455550b40f2403e040c1503940310006401002062400360b01401e020070400d078801c100306401076400200f030b40c3d0f490500010090290100700c41e02001c40400450500425052010000d090089a40d1701405040101c03c0b0320050980b06840d1640148062008101d079918a00244014404d1000000c0d075240180392035418a54400c0c0001648074240b15040107000340000c3c446480c0c014030181000c1d20030540f42c07a0151481080220790000110320030828104140d40c50880700d03445250302d00c19918 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 737235215 1250 737233965 737233993
    0x6080a03120506040c0212090126040215090102030d021e03090a05010c020c090103020103020d1e020a2a3801080f0a150c0903051c1209020904030815040e010b03 71
    0x615052180c0c170041e80907060402c420070804020303107100f0405141052014411404009210003003084407000f1090031000d001c00c615104ca645040c1d090480e404a00344009a80041e44a008880300002007540000708825580300040c0c210400240c4400502d4807030420540b06692010b151101311174540c6450165046140005010b044034031006103803003179903804c42c3d00440107904181f481d07840d40d9469401802c01d00b42d42c0044079072030500d942001070702c4986140004159048880407682d002400e04d10091141070700c0c0c0e40304002181c00012a12130340d203001da58019100d0070103004001ca1501000050540010002a14101c50644080700d079030303182c4800c0071500e4099503107004001c0c000c0f0500c0807500c3c4510f07411034651b880490800c3c080141d0b69446580c01c2240c1400ca841040007150a103006458101c40c81484040035031108000714091540031607050b2902920160a0292100001e861080e5401c220940688040c0c0140011100004424080d20900c902c09201c3e024119041d5072079 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 737236465 1250 737235215 737235221
    0x30a060614121902070b071e0509030a110307030807060207061409060a0c0201090203060f0703060b0a020c2b050705010e010311030609040302070f080c03070506161506080a0312050604 81
    0x45500041d0000580ca9003d19140500c4a0312100ca820f160280b14400100e041d04001910403044ca4945107440f180f003481c80d007800010040c91006001c41031002c3c3c03c41d0b480c00204007000a40c4024141f2a803404080084d140c219030b6400113040500c0081c3d51405c200840c0c0140640610a101c148031004010a0b01c0c44d80c82400c8984064650200001400c2c4400c2c3c0e81051200c10386900001415141680100b42014800c841207080c1c070003814180200300703900d07105000042080503d15820480700030b0000b1348600011703082c103200f07003031f50004010401c1c1030a002c240d103950440300003149610701e450041d803254128460a404907a0140b00c85205500038040e01c6034405620b10268615541c1000308200301d1340c0030300305408512503e80d01040c45083d4045079800307048500c0081c41034600e884100b5203421250b8000601514080c400348440400d54400c0271042c640c410019420030b00b800c0160f100070f1030b1585c041c3e041131041e103500303001b41a00700004100401c2c50010030320059031800240025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 737237715 1250 737236465 737236477
    0x3010b01090e0f0423010506090901060812030714070f0c0e06060913020d050c0c0613020d0b0601140d0c02060a15030b361e1f06030602030a060614 65
    0x182d800c400300003400140410600350f400780c8202440110f6480404010703e40194500300b90307182c0ea41d1070341401703d6490407001066014000d80c009000076401c24514030740726030a80c041704c01d00c2a000703c04582c005000c2c0300c0108030604000703529501c500103424224001b030b03518403003500c0f00300540d1000b20307180340c3c01c1c1c00162140501030441071801000c00c0600502001e034180004802e80d007401721082c0e041043c000e640c00740c009441155180d071541c225542c18084090081e6255040540c403800058a605040e00c6140f9000b40c41c25a5641c0e42c00c0050381c0c000c0c04024040402007000030024400c0c40389620250781a64554211045035884408480c12510002d40303030800c440d0080010400248810105548100004040c0840460b040302c1d44140c9020100da43c00340b4030075119500d01d0703c10204074a41481a9180003a203115141203030064a603030300c0582558864072842c0001c035503c0c0864121000a40c1d10031011076803403802540060041020780290340000f03061400c1458800c0c0a81c0680b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 737238965 1250 737237715 737237729
    0x50a0c290f061c0204021213020a0602010b010206070c1103060708100801090c121b03050a0201030506180714120a0b011103040b12040303110a02010b101812020d2003010b0109 77
    0x440c2c507a0004040243c80e00820b00705c0c0c4c400d408010909010821044250140d0040c01480710000303c02d104220301000b40350005411689020281403060b070b4005102c6401c00054200800c110035503042c1080c0d0004a8a8882e07010b11030701d02403002a69021000f18490900a01842076854a80101909907070000340d01818269020b0401c0c4681c1000c2400f400c1144e204a140240c480810700c855084204664815502900404400019543c150040903486001120849002c41d00c46810080c0b0340c5024080008000c00100c0d0300300c0201c4440f045406211050081e01d400c1c2c50b18100350006003408190460000e00d0150342590320820005c10b031800d80301c40301c2a039410000301005e41e50009000500650806498a00d2002071450300e01c010314083d4429800400c455006c001031051150414104004000f0302c2c11400313a030741440900000546002c084181e40030340a41c00003035080081c5100223091259016501410703240c1400c06481141800e80c02401884181c0e07005680869003803103103070303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 737240215 1250 737238965 737238979
    0x120e0603010902130509100312030c080a05180a05060603010b09010303020616020307140607030501050a140607050c06120108070e10090f09120905090a050103050d050a0c290f06 78
    0x4001500b05401800c02d564035030040034101c41d51a400107a8a100aa403883d03101001c800082c014052240102000b06040e030400344515500c0100007840b82200506c441c4d041540e0b40f0210384113009800502041010000c100c3d00283c1e4a41084c1e0f0f168007060b41c01c40e01c40d40c40c22591a41d642400c42426040701e030150060b0140f955106a10b21245103009801c0303007103000c1044040001b41a100e045000c00714030b40002d0800e8038068a02038111201038000d68490280110100150610700d50035481d41c0c1001c2d40c02c580c4401c072615200745081056445035602100101e0031280d50f10014074914104d030040822140499038a1004038280c00d000d6035505402e407081c580600407400355412160140030504000502d52209450f045009070100c8a00000500700c200104200e1030a500c0c0d5a4200180e040e04000e2945141d4070b03150741d82d00010081c81407203400710300075215a0041041c04003070b90700403240c81003d10783d0286d4600d220306110f003c08030403a500000318101001000c10329100f07950180c028 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 737241465 1250 737240215 737240219
    0x260a0305030c0a0e0d0602041707080d0507060f020f13140306070e010c060e01060816080303041b211e030e0f0a1701050105040e0316032019120e060301 67
    0x82549901043e03070b09051241e40c1c01c82c0c000d2030300d40c6254803c0351401084010f8032242031a1003c90300d20502c0b6406005540405018441d0080c0032641841902081c1000c513070b6411245041e2020f460030301d9041b203140e84081100c01d226540da100900106c000401c512000ca07840c0c1041c550b0b02d00d00d0180081c0c050303100f003001901c8140220040910480141488100f01a00341e5540003501e805c07851070710103030751110303820030068408004190416021031504c241c01414001d0881e40c07800020405040e03d0420886002d00c5003641506a001c1c00c0403e205090602e2203032000000d44843d840100d440d00000135001d8034650f01303540c1030000070f80c1c103659104040c0d15440800803044503900301194000d13000c040000d5803030314891041c00d0501100001149644c074110400040320103040c0024095001089280c82c0c98801948612400b603141c245090070042c1e58510300209040c0950002c3c851091b441d0140f240d484104105140038400d02c0301c40c40781c601c2200115610880c00551a0300701c0014001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 737242715 1250 737241465 737241481
    0x81f05040506040906021804050c0a02101d100b0906010c150509100f0b0319170a140307021b10090303030e010b031e120f030114010315260a030503 65
    0x301c0e9400410081c40450110500d807078140403607020183d118031410210916021604141c0111075208010b981d04070b0800c51295400794503404246041d00e09140c2d540c4204060203902c10305840072100c2082280d4800c0c80b001000c1c0010302d43d011000780308805902c0005c1c0341c0d42c0303e00c000c50403195020894403074140c0c0f40025540038050146c10403c19025404034080c04511901c100f5211400350140849c2041c005002d044c10300000207a40103141c8580c1c0d002e00081500b61403004464104900e0385c556901d0b4400080700d440407110b58070014100c000050280e0b4a500095400f0520314081d400ca4801d141031081003894201c1d030300c0101c007043c601e09080010074029402a154103045100120b8012569400030741480c9800d00001007000404c2e14a2182001c20429422141511000189440301080450310f080c0030503c229151401c4c1d1100d00e43c401d9101c2c1e0060b5848a00144001c0d451545807030702031030341ca04a026002c001b070302c4480e0000c000070400120807500f107030945ca40ea465030b02e84081d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 737243965 1250 737242715 737242721
    0xb060702090601300b060a080417070c060807021603110d060f020c030307080705030106080c0a0201020c100b102f0f03030c07111002070510111c081f0504 68
    0x82c0c10306104001211104002d400c140421800001c11030140e4004d2070a0f200c501100d07400d03c0000d0007003100344206520180c11085041e00140c1002800d000190b54411100143c0710b40c3c1c0d4020214080b01c68002072481d0425001c2d402210950243d80909084031085c214850452101501e900025504407185040c6034101640e580c0c0145404582c0a41c01c2101c801a64020201c0c180190f200108200006034403540b4113400050a25100c0d01c1c552600100500729203029011a441120002c0c11200d141d000b541121151b002e84016541d00c560f00d20b1284009100300300d0003900030240031511040c410700c504000c10000065089940080350668400824000c128228080320311480681d0f001c1b2103030800246104c0c3d0410011a60f0311465880c18402c20308950040d18010b10080659403103254010078864240d883c29940c1d1186228050b1040704e49902c054180c003500e000704190b810514039444001240b504068a480a580c0c66007141c044804451000c0c858003554401d0b030611062038150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 737245215 1250 737243965 737243971
    0xf0f070e010909110705010c08091b1c030905010e01052106030c120115090243032d0503040312061503020c0c09010b0a0509030114040c180b06070209 66
    0x201d01140519260f0940c03500f211480440000901d03004075070041040000d020b56559007226240481d0b082c2080c0c0710203952000541080c82c0003000110102c0750b59150710300005030030030140711440d035508a40c1c240902011b8040c0240d900180b070003144080c2c103500480031201c030700703443e55a15103106200030003d450701d61014046503814014011000495691140b44852035101100000394000348007003000e01803105903104a01550051140e0b280021041c030942c00340342c05501400f40c007041007252503921900c00100c884c0c0000818801e4506040c0d024114102c0400820381100484500c0c0e510181d080c401840c070107000820410001c2d0000341700c1d80e201a82c42a60260200b580c41e1102460445c450243c0e010100003603000c40d060084400400c0035100d8084150f40251007541081ca00d0781c024425481110244500040c0818082d182517020001c02031001310100c40324102854141105d1000d0322071400941d4003a1a42d0004000700d11031291f00b00c0300105940e00d02410f941c03d100da444002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 737246465 1250 737245215 737245217
    0x9062707030813060f0c0803161205090330270304060309031b080409020906271009080703020409050f0a081b030412080f160309030b0f0f070e01 64
    0x1201002000030b4007000038265500052485000b56400c000300141203c00c1d000c00c040401055070ba09002041051045a4001c0d0b1545017650340c01401d804180c03084a243c60300440e41510308020055000000300c094031480e81004210b4107c84075150314210070190039800001080e00c2000800c0660030604400007405c1500d9061054488201460324210340140c3c0c00320b0082a203030b0034408205580160702803040c03c10031050102400c800e1700d664515000d42e008420b8070a600003251045680c40905990250303070f044041007070f110031075080d1061000d1360500d41d84c01902c030040003c46160003003604600f80c03640c0100500c1c4581c9560204030140c80c200c0c6090300c0c1d50046598404a400f020704c00b0b84400c50080e043d0036610780f94540c0c11859440303061401012a001803200380640e0300c0d14640e036003005802451143e00d139038020340441c1030b0348600b00c54200a244402c9682c0c040580000d2040c046134010301c0c41c0c030312655810b48000901d50048695811100c41d01c0002205c40d400341219255030101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 737247715 1250 737246465 737246473
    0x170703020a080406180e070e060c07172506020606101106151906080c0a020c0a120b010b0304080720030f0703170f0d0b19090203040b090627 62
    0x1d181c988060a0f40541c000c2c200240c04d140003200340304102048032005006040001e6094585240000c2801c40c00004151007280c00082c1807040640c00c00100010740207103020741c0041d814680a10360381d80c1020592400390088a40340c2d46024005060441c03c40307103180c026046645e103110410241c10800744050090003181c0c81c0c0c01116002c10807900e4800c00d80b240d1058600f449100c10420b00251403c19030300e48030501c4000f40032050703008030f00541080601d04866125252040c080c0c0c107040b814108503800c124000000107a00c5006207062003a28050f554008413644c869032110755a2000300c078094104001000190300003580480b015591881910400c00b01880300e00020b400c0c08260305501095a00c200030600600140000c2000300807004584640f400380800b170095101d010f0a5a0340c4519941c034544c1801c03581b20340100c00c1c3d40e03621081551080c50f48880c5038100031740058405545004441c000a09074042c000346c001d004603480c002c00b482c00102440d181c3c3e6140d00e084924045409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 737248965 1250 737247715 737247733
    0xa05090a110f21090d0c08030a090614040606064401080c1807170a0f09030f030b0d03120b03070b0d020405120d050301140d120320040317070302 64
    0x2a03110041c00c04030341907110301c10100314101d42554840c080540b0144c2203800140320111001c2c1c200e498100f81d1540a19881c1e241c1c8da602c0c00410052031010070181c1107e04020044182c000799a5280788100e100303400c104940e5071503000132901041407240d0004007002c4100008c900740081340d1500c0d80e015001405603c00b10f9400e005001001c42079104102681c0228180900c0d40b0304441c4034107940385007644001c0d40389091100201000860804141403c0a09001c10031901f0660054900d220a0b908207000411030761400500d0042ca0a80d80380010745841814440d601c3c2c02140c240d00310f505961386030102580708810078020818080300070786c0b5105003440041c08011030030182ca000088004c00580340c514180500440011081080300341c2e1308144400710909802c0030940b0b0541ea0f07014040301e1801034010107e100b500002101034005c039052040c483e98541d041d00a00982c0350310b43c044007000c0300c0c00c0b54010164042c43c00010f14850100203110250181c1030040c10201340a03104880c1180c1c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 737250215 1250 737248965 737248987
    0x150504211104111e09060d0509100e0703021008090c0f04090606030c1502060910050a180b04030905010309020a050603070c0c030b090c01050705100903180807140a05090a11 76
    0x84619810040700c54000c0f503003141c84078041035101e00742c0144e51040e514221003030340083d40034032600450442d09903450000c5443c150017004030300c3c0c07078228400e0100300d10040040030700d81e90304451104038813407142c5859100030300748254080c5001300030003002424607040300c00c10455144080c8801680080c0e58100d82030105500340145e00045015003012418a814280e41c0c4222640251580040d5840841405075000c0009010606100c4c0300e00009840d4545ca11150040c01d120314104d0709900454011000703010750030b4400b030f0103580b2a0316180c440e01d07600d400540555a00c10b00c045d5010507030460401060821400450344a81c0d03034540300c40e6030416942c07900310080d43c60b00140c908240346400c002444004201480c503028007400c1c0766081c1a020780c1c40c181e950403511003a101142d16003944030304060090152360740c0c103408102090300f425103070804142d440a240c03007800c2d00d103064102e03265204d050460510066074006000000340740e81b2620702030050082c80451100403402003015540d15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 737251465 1250 737250215 737250221
    0xe2d150109060e220c091401030c0801030b090c04020307080f0f100b031b0a0c11031902130b03011107020103140c250c140310110a0c0f060510150504211104 69
    0x464003506c03002c4001e0308001c201903c1000c00c00314141807500d080201001e542d00401d0482c1140d038080e040c60441d40e0703400141820070301140c0e0083d80207400030060005150308984254800e803450200c003182641d8031b1841c8840110141c07040388011503002402d00c07030412050b004540c02000c2c00c0160000c203048031854a40340d480521201c00145603100d0300d01c10401c520f1403004800c1000c900820b20b150a030040e01c820003594100080c07154980340d400150717a50150308004818030000300200300443c03584c040041998441e003c01c0740028607007825540039034080300d211030041e00c403541224140441100c4003195481445c45410040300140312110010304044401c10160280448900c204802c58090500c0d0040005c61720354000c0c00c15040301c0d0056140c034142c0703141c1e20003443c055021400b24101b64195101084024041c5030405040110840302820600308075007003807202680c2030854000c1106c107400b80380103060103e40303200309142d80700041180e190300341c1d40600304030010300071500d00080403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 737252715 1250 737251465 737251481
    0x50c031603081b1305010318020301090c0512060f0a0b03190804030b010e090c01030c210603050c100207060c021309060b0f0a0308040e2d150109060e22 67
    0x94a0208200d0307141003c4a00c04481210155600e052520044685840009034003a0318101a07644200040780f00c038418a42c892a03802800801c10300c0780609065468854a00800c0d0080040140010003201c000404174482d0620041d1031a45855018510740a0320403034061b2a850700c40e20b001300706240b40c268000403006100d5444a41d540c0c3c40c501d490b09159505238494100070300008100b0a81c0e000101b4540171241d008d107000a21108031210a0354030003405c0740d4858425400c5040490756002c03d60000301628054001c0703038034101c0c0c0401040300c100c0d054074460005030401c807400c00c4001e00038405a000355200030040038115000000400840740c0750790b0140c40c40c0d501c42921101c0b03403c08895110701c01400380c07442d284007825511000d4103032045111303009880c489030303000400c4480c4a243c841e0003941019002c0c1d148040150074400c01040c10f07107130059070b541e500189590030344c028080f03c012210141c44403080035000e881017008101c0c6080c00700848403000c54020b40307000030520030130300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 737253965 1250 737252715 737252717
    0x2030403110f0a03050f0a0308010e2e0b0a0201020c1b061b010209090c031006050310030828020a0b06061309050612070f0609120314130302100807030e06070e01050c031603 76
    0x1500b10700c7d40c08c00420042044e449114003060380c03018030112780080340072540b000340c110f42d01456600310f003041c4185004081d800b01d02130501c0410034546c02507042d00102000a0f000003211900341780b10102c2d0f64444420003101da403100c401c0009501070a60b6140c10384901c02914001070501c0903403c0460080389046400c0ea003d142c001003003080d0032100c1c0010802a003850f08d000703420752401c0d00041422102c0ca0201410036440442c1d22203041204c04042e07010f0444801040c1c04580350110080d40c1d48480040031581543c10740009401c5040c080c054030866030307144400803a024a07144407100105000341c80150030001c00c4c8480803015074200442001000144d803402c00781490801f0041c81003125410105101d04d040d502d0b000842c0d0301400190f4160034201d500c980c6c0ced14000759034180e20800c0e0341c40250032199003100844000e801428075403042038292010302c03a000400e10519100d0208071520030220325440d00c0c200c519446140a02020072422301140c0c038024001c04203464801160384114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 737255215 1250 737253965 737253973
    0x8061909060f02072105030c0c0c06040b0403150227030102130f1502162c071205070c0c09020d0f0501090c1803050d08040812070c02040c02030403110f0a03050f 71
    0x201001991211103200000c131641e121700014440d20020500d101c040e24102c2e8040c004a02912084403e100503c8900c500034211a600c40d520b07603040303003d50001e20066807040f410a001c111002e1440c02142c40b8510506401d021a0341e0b404c0d0319100c01540395000702c2d05503500380080340a454440e50060060500c041c1c005e8541e514080c600b446a0900c101c080f011900404100c0c40700c0344410b00103030156901214007524602c03100e10b0413188074488401e80950b0760588030a00034429008060a1204c4200c01c0307051083d170b03407100015107102101980040145541110800c60380c5640da01608e850313490800c021030600380010201043d14002e0b0488144240d644207400f0344242c000082c850360101c0c00c5041c2207420702d59180c088e15810380d5110a800d00480d500041c040101d104204e500480382a00d00000303d04040c100100102d0030144101e0040341750015403c0d401d4000415107003240d0340103001b031900d203d07038606011110749041130f15600701406081c00300c0052401d02c0902c0406121f00010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 737256465 1250 737255215 737255227
    0x190507170603030a050f0901020309060f0a0207060503070c150b060408060a0b04060e1302010c1a041203150902071b0b1216050d09020d02120c0111010608061909060f02 74
    0x21100d1803001520461003984108510340901c0d400070242c2d0010340c80c46a0701611000d010005074294804c0c2c2001c940d1041c0001240034030030340d01401030040000302ea400c07100500d40780d0209030b815210a075000c10100d003512070800300154600081110f004114540401c10003115000700b16550070580014003250850010401d86122034480d03889030700c6003101d0900c4598035000960f46441009020381d041003003e48809019a406031803556481a80000c1032600c40d80c030345180400106003a10101d0380d000284404444003403280c0a000098182d07810451421454070130200000c2d88100d034101c0b010011408580380002c030b1030803100003c0c0400e44600da9100000b40c504c00400b8170084c48125075403810000034100a900006442c07192129401c001100c051900004402841411b070095210014513142940b00001003200c1c02255000c0e22240369031b10500307a000d03098031003501520140d82c2c050300000c1c40c142001d03071045940c0f80c0320390400204d8131000d8035441c058802e0050f000e215940c000a00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 737257715 1250 737256465 737256497
    0x302090106120e07031a07021603152004050118030503031806010801020f162a050f01030501120201180906080307020f0301020a020a0b06040605030f0105060f15040e190507 76
    0x2458072814041001e0440207045540e00000800a10100e0f8400c641140000d240b0701c0c009c2060030030050070108032480e55696894601d006600c030059004141e418440b00b50410b4a00c02c5a2000d881401c5220b02d00b0030307003490b00445440c40402d804800f001508c030000000700b40b007031000f507020b1301e801552400345060700c4803814a41030060348021100da00c10080440d03800c041e2010f84009061080151900d9482c82c28141c20400c180320401c68a104e900c0c03190070081011020304000c507901950840c1c00c4002c100015011142c1c01d1003250710700302001005500661003600f00b140300704c2807050140003d039210040c0e40c00715081c94101034490750001034207609524002030f01d0a50440214003d5103005c0d00354000075100e24100e00020881c01281e404a5100ea0392900040064040a0100c40e051411441c2c154060001a19010b014200d00d140341c007580d0500c1c0850000c01c4941146042c0f401d440c7c40c2c0d018406910040c0110b1400090880003800d41d80d0b5406143c0c02040c050340d40d41600201030303403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 737258965 1250 737257715 737257721
    0x90509010c18060203030403030b040f0c0207150c0b0a0c03140f0108120414191802090a0801091208070e09090319081306020d06030f08041a030c09090907030209010612 74
    0x40110482c15a1440030000745900204807036000e640342c603020568443c500040340203005c1022581e00911b00b4002c07a800c40d41ea001880d0000c442415030110701035000400140d5990100d8038010f824000040001307580b408140e001002c001e0780b503150024003a51444640c1e50040c505403040c0c1c14944c04d10b8010061043e007007088800820785564280e1509284c41451480318842242c0640600314000000314010280845d287c01001e07000c6100340c81181c141084002580248240c9101e00310f402c02c080782d014014840c46041e03a50045005105c000c03600c174140d8412000510001c10030441500485a0b501d450407401e000b141c1190042d81c40d101c0220309460300c3d55010b9080402c00c0f003407404000e115006880300c40d03042a04980016517070401555044064640ea030006000d4800450390081005240c500800850b0f800a035100c0e40052a50100c107094403003500c52500101c414400d050861404400041d01f001d40c036800c55582c0783e920350202e46039071003d0b0700820220700c5540708054011a00c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 737260215 1250 737258965 737258987
    0x11e05011701030b0402030705030610170708070b130b0a0e040c08070806010509011206080309011b030c1403070f12020d0804170f0d09080d0b0102030a17060604090509010c 76
    0x42401c050340101d5241c680801c00d01440080c007180c0002010a05645050100002401028050f6003c0786000c28140000546d140324860540c0510351741c0040b4902c0c01302e071110079200d110010304001407518005156507049403120385c1000705d43c0440000c0c071a905900900400f00b0a803035034400050010100b0088031a022071040902c40d005c010002c800da8001c1c90340764051800d00300305e5284e440030b40c01280d5220101c089012114074000c800f1400707510000192007800800d03a43c0d400038580540300c000039260140c0c00240458081c0e0008030000d440c5c1300750104841000c804403805c0c061a6200c90322010240c80c0c0540b1154904504c0c8400c190341070100105906550800e00c200e820140d0b1031084420074002030801903080458000041c12044040799110300d0981c40510034141641880240c3c1d42c445000072501a18006011180e13500200035541000041c0d00d5010001a080e0b20152070400018038640d8000410807000c02c2400c60f512425000317103400d60000403100305a44010304881e50740 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 737261465 1250 737260215 737260217
    0x111903090501110606060f0708071b08030403200112180c050a03030e2e17011d061306080102130509130807030302130e07030e0615011403060315011e0501 68
    0x48484800d00300013407101c1e0880c2054450300d0750b501000780e108209000d0715400400c1e4000001e4108140310101c1484018a440c00d4848041d642c3d071122095924455484014800c4042c000100c1e22034224034400305004a060400a85140300008001d04484801c4900d40c1c425442c0e04c82941030124078071003480070700382c02d5071003008043c110b84010f00403441d00100144908400441078001d13440b0307020400100e480e903d06c217402c20f10340601c0251885691407540c0c041c01c034013600001941502c5c1d0450203000c0e540341421810580300c000a004150644003851b40c0b1683c3c5401b0001a240340902c000c1041050305010002e101d81042c08110002002400b061240d036903500d407a00c086802001151007003a4503003030059a80a00c0312160f14080e20303e5001c910901036005c01c101034150150080740c40101140182c40003661940d03207501e8405c2d0200b20340c03400105141f00860b22420400c0046030000001400c482088400d11001c0304080d0003604a5900d43d50b50040703034ac0f6020000407115000c1c06007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 737262715 1250 737261465 737261477
    0x80307110c0d0602030a0b0a06081b070201090302060d0e1606020c0a0806010b030405010b0307060309060507090608160504091a0901060e060f0730110703050304030b07111903090501 80
    0xc1c000005203000440440640025800004500715092550240140040113800c4000e05540d4039030242059400b161007100344112126401c1400f8121422920f125a0585a0711480760030b58003807250940204101440b0280ea03282162054481049581e400c007032440f99518003242400002410192200d400038007130100b000c1c1c28040c03100003082c01d605413001ca458003502c0c1e07a9a428214050252000b110307030540145c8001098081c0c0c15007005150600844007800281c5450f5022503082c0924842ca000050b01400481d5852800c0a07180090380d55520b400c0307090a848118010454600c5500d0303035002442c18003c8074003130078039554460051a42e41001903901c2c0030400030844c80d100c0d41960baa80800e000604200300200402001c41654031071010444d1031401c0c0f050141e90f01d82c00010304000c01c2e602d03241070054010003c0c40005aaa00c5805141000d00c0d513580c0445084000e03280e130083c00312981c42c2441914041095400507400c52544900e1002d180c20060164900d68020b903040040f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 737263965 1250 737262715 737262733
    0x303052e1a0c0d0807020717100528020f070b0c04080d0503010b04031214130e0c07050c0d0f08070303150504060b0a21091b050402030f0103110f0d08030711 69
    0x4003c00c0d43d500c00c0c006800c2201080e030b01c1d25002c03804c00c207454011701102d111803011401042e8000171140440e02400c00c04100545500741c608480a604104691800c140da034116407403403646801600000c18041e84035800c100387c55445900620b0101c84a8480480c0402d0402a403801004000c562180e01d0600e18650750400510202c14883c601018101000c0e0456070071106203c0e100880301d01d1510902a5190900d002004401d6507231071164144400099000c40d628070760640855090942c8180204100c084ca50140138140704000c6007500c902000c0312080002c11205801002da00341300b0390700090b2040790300b110b44400c080c00c1d07001343d40540c1ca071480034400c0d5525801110122040c0781881c07100b00c400810000c40b00000380740c0c0f07105039a0503c0c0c205402c0041a00705090402d440701441c0a8003038a0304240030403400704032030421480380000010804192103915501e985800034080d28490010440400c00102410200300d459010010401c8916548050440e00303868550001d800c20304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 737265215 1250 737263965 737263987
    0x10305041a060a170a050d02010630020414040302160b0318120c03180303030c07080c0322090c09050108150103020c0a0b01030302070e010b03040303052e1a 69
    0x30020341039440d554007000c105940d42d02c103000c0006103480d11071340f2078058040300c5050b2103805c100c0d0100d03924403424010128280c018012602030700c030140301b40034060a40c0f40141a400c0e0500110887c01c0154412000240e00c41b40108080030000f85d6904220341460314000749003c400000c44501c1c1404254140500403140c41102d07007041c1103404041c1c1182c3c40300000341c10044051461150703440001241d01340190003001070300c82c103404142e4401030b0300d10903024182c40e48030131150011840f07002c11000000421440150000c410450103c1c1d090512101c070b4032019081c0c0740c407809030030400c503003081007070350300d01d02800d006810780e8602010b00c2441c01002801002c0003070902c10714001c9400c05400564441e80c1502d40014804045807040300c03030b0b400d000951390028041500103006003c0e001c20843c0580c0103460407644000000c901d1551151400c03001070102070800400320311100c0d1100008540340103180201110311680564517450050f000d2409442d480c188a02c840007841420601 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 737266465 1250 737265215 737265233
    0xa1401060e070521010305060106030c0e06041703070b150a05010c03140d1e050108070e1303050706060509041104050117070911120c090109170a15150303050c0c01030504 75
    0x7010241c20f100351542c002c00c1c40f842040c80d0b0220340000090381c0c41c00020a200001908904072110354608101c04110090200e80d00c2e510b2149040d001a010071080041008440c0c0c1080030700c00c0801901c0c1071030401da40d1103d80360011b030b0f001d003141d8141041800540c9441100e040080c0f0090a00c1c1d0014465980c0c0030b010b28101e054250101000421650421625a04420340c0d0b15241c4100380401d00e941d6043c100284402c0c09024054070a0075400301d8803440200403140031308040f107403030010140c01d46d50451b0176901c40507044906a4440900281545503014013502440c030401e040290305030440107000403a00305a0044613020824203085a032004003141800036160070010100f204001c2c0c1e2106280c03032150040385403d40c0e4150081000c03000f020005072003030450136a20900c1850782c40200d0504401041c0705024a41c000110506c009264441005440100c1e4070011910a0440409031110382a5900541c0410400201c0114010052002e110414001d0800b04001d0516031540415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 737267715 1250 737266465 737266471
    0x123030c09190c0c0605060f150a0203040b0703020d02010b010e0a050f0a0803120907061412060a090c0203041e0f0b07080c0304090e0f011a060a0e040606020a1401060e 74
    0x7904082002c25122425100310000310203840509000000c12040c2c001c240520100b41174407035900c0e0801044051810607010524038800800b01004107aa900024805a0080c030600043d88420040058040c0c04c510240c66042c0c000c2e0050900310702030b0080603007501c040b81c1c00d81e410010032019440341681e5034404c05041c2c503001c0c1d403080008480c02020468010b205e80040039240301c08100100082080c048561042500409441c1ca540e80c510050310580e4000d1b04061241e54140406642c1c20001d400c100d030310801c02003551005641d200040c50403030351007000e1100160030008050010a40039038040d00c19010011502826500d00207000c0d030f0a00c03040c002c00c00e02c81c3c0b001030301e0800e02c5003007401d4400142000c2c090300d680f195281920740042c001c0164070b42180c000c2d001d240d00c1d01d00c010312030940344200c4282001e1902c2c210408001d4180c0c071180058051064603415506152294450341000d0085500201150b070414203203036042c225200c0343c5440c9a810301d1018800c0c1d00380b440070660 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 737268965 1250 737267715 737267719
    0x30615010c06050a0902031002040b183001180c0501142b0b030a0506040201030c020a08220803070c0605071a1003060c170609040c030b070203030123030c 68
    0x8000a1840100c4822094890242415040c00c00f4800071080951020143c68400c4040711221400d54062000383d00640c40b03178400c243c0c400e20139544052415440d109043d03200a0050007103200350480c910103c0c9912544127005004501010110b9100344075401b0300400c1c00c141c80c1c000b09003503510401003140c04c2c00b51074100b14141030100c07081d45415042da20b000307402913005c681d00d003220045c138840044401d10b0507000c1810f00d01582c03070390304002c02c1000c840c0341c100c005021569980e40054000d403242d00a0034046116100001c408500c5000181c440070900006a02103850400340041e00c4128541100150303800070070001d00002c0c207004101c400c4501c0e50400a88a012074100740e642003d8100120344151075840820003030303000213880076041d01d00c41d000402100101c4001140c04000080c43c001c900c103020004280180b505c1c49420f03502c0391103400c0a0b00544d481e6a10100c0003442903a5110140e8004001405102a1200c107440103081481c0c0024110440d580007aa4401034030003440c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 737270215 1250 737268965 737268991
    0x1091a06031f0906020c10020903060f01030812060a08011104080c010813060b03011e02090301110f0d0e120c0601030b06030114010e130c0803070209010e010506030c031503070b031608060306 84
    0xc420400c04d5010f5a900341402e205941e003103080810882c02039031281420718480e004650001d00c00e800840002da050742c0e045503005050001140c07100c111548003038195a8000c419641c0000e248000b40100b034128510944801d40fa070f8a0700007000e2a0141c170302c1000d81070140f5481000003425503034617042e80068000703201040c0a2025000700b0f0040035422070818200303258079100c080785800d1f500100b4003044280d000f00082c59841c0c00d010080d008660030410a00700400140390008a99004004180c1580e02035035081e0402c8110585242c5c4102c0b80d013007554128100400a008071018403e5001c8401d90091022003007201e420b039441081405500c200e020301c1c4003c90030a0003000752403000594010401e0705100d4460450640c0d0750060181244180080400440d00b0b0031b070312074024103c5101400f01821078035801d400c54696003000f02144140c404a41c801c0865550803c03940300101701c2401e40c01d80e6070501c1c440c500e0604880c6d15200081c002d00105000c2541c4001680e5540704031069080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 737271465 1250 737270215 737270231
    0x7020604120c210e030a11120c0a27110304140307140609010b0f030705010e130204031a060603041a06061e09011e090303051b01091a06031f 62
    0x648040c4001e40001d003d0000d54290900c42e40030300701d42041400042c0c0c48200c0e40c660325008140d510f003121100200001d1a0b64500112401d00c03142d03601c8000c064600340c0f6001c075040b1011400d074400340da1218426039403074008005a0203812180c8282d0400c172010601400242c980c0c3c145035840080c0c4020844581c808904403007501c1401507415480e44500e1002030099580360640d0b481105a0b0316141e69440d00c021203850303113441c0b90100c010807006006001801d14010064402c1c03102c6200030f981041500d01969000030241c8020805507114030b4a02d1110b40c1c00118100d1860307401081d540c0115810004e2002242d8030303502c1540d0000561a41d03204035a01e003030100d800782c02006480e1600c2002d0300401e0300e25900c40b101412400000f07986044040c14900400c48042141c455208085414442c051021034401d00042c07165401c8810a0b0790400802c00480342115072800083d55046031280e0b604034880d083c02c0070700f9001003040340107105022620b03160a003400c130440081d030141c50b41ca9440c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 737272715 1250 737271465 737271467
    0x601051902060a150321031503060504060b06030c160809060406020a1106031b070f02060a0804140c15210f07080a0c0e04020a03150b040905010b030702060412 70
    0x458485104211215400318040140030303645200603034040b4041d40c1811003154001c21041c00c40e100320703a00840340864030110f80c5600d07034001c641c04035420b003055203606404411060702154140103603c00d040000b110700d0030b4100b000444804c80c284c1c501c02c034020010302c02c0300c8030f448042d0b135000b11140402e800302413054034000800f84140c402198010350085030006510b1b40100d0b005000c40d000785a80041c0e440303690200302580c40f044600700741100c070040715248503c0680d406401070b076100d148041c1c440c0080750000742450704400030010004048008200811605590f20706c2d82c81e45e00c5004108103005a800a4012007003455038184103a07010495079407405c2810000313221000304198201150500450071038800404803004c10202d400c4a0105101800600c2060b0700d88646030340c1c0305244480081040b000e94800c070680b400300b54840d10162004032442d022a40103207400c101b0b059955161910003000e44a059000c902184001d0040001c800e0300403a41d5640250300500c2103000900c07002d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 737273965 1250 737272715 737272717
    0x110d020f270a020c06130209070804050a02060711040b180a09080d11030106080f0f0408070f0b0a0b040b0307030b0103060e07030503030a020310092a02031b0a1b0b070209060105 78
    0xa0076a01c0c4a018040c090710b05807650090603640e020400b542c40303503540d2031840040303a2500800250003840342c00008a070306116107802c0303170000d206030b06903900c0800c1c603000559030f40c103c081c050382c55107150361540d1920300d064071848c00003000c02e4441c2c600c035005005000200724002081a00fa1b0754894458108100c5000129080c20044072001c00c48180100d030303c140d581d0024090200407170006004101342c4000780320b6181c46030040f004040c0c000d6a480e620000742d034100403000c41d440310390728800343c0002c0c1d26544c0162190760301c0b01000855050000401040e2244111001e0007500401c2c014404240c0302032146054030b81100b030214101c603134080c80c546051010b5002928500004c03051180c08070300c640003140100c044988031038029807101c03113503005c0b1581d83c85181d000c14404d503095114005100d00e0700c1d0080d4404d0050f6030501d000c0b20f15030f4403021610103200d481038228a030440f040100001b800e05040c024003003034095650034014140340620607040040d02c21400000050200d030700c42c1d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 737275215 1250 737273965 737274019
    0xc17160512120705040e15010e131a0406030b1b0418020901090b210408091c0c080114011703040b160203010c02030c0d1107050907020307110d020f 65
    0x2804031540050784401100c001c0e0011904500c80303800d54004219541e10034810f450035119a01c0960b003590307c4181800c2d0b0f081801e03007111414040080514060f036941d50710a411010000c078404117681c8400c5610441c0740e501030038400d04c114603084040c800300307c491a0182d40500c10550180b8403030f50320780100340e00e80039940c004030302e101d80c4100e04900e003115500030b00081c0b00213807119000c554503454146520f005c0d00c0e80304010a4502d102d00045280722362003164200e030040030810b24002c811000f080d01014082e01041003c41004103900411500112036001800e10100070801030b2002c04640d0042d907010700c103810a1421500252a07160018000c4030010000707a03101a683e0012003c078560803400342031003a403180d440e00407018070560002c02264a610341000107041000d00f003070400d031109001442205210700c600300700402c3c030391640380109015002c1e076002161150002d140080516a001d8416070140540f0003445c00140ca800c06002c160f100200c9031420006103090f1000c00200c1c8070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 737276465 1250 737275215 737275223
    0x7050118121a06060906030402090604110408010c0809030408191a0115110d02070521010504321c0201141f09020405060d0b030f10060e070c1716 64
    0x70804034401c0120612080c04180c40c0104020308543d41c801c1007007002d0045811040d00034208000113401440c0451b800e1380d0021006000065a2000181c4585c0c990031580010320203170365800c8001070312500016590380c0300e1142e400452510703007000811500c510844644242801c01c66009104100729081d0014004102100b0300c4c0a07580e40d08204c0c8540c1009608190109003680d054043c0301001007100510901d0726001001100c0c505414401c8503100903414040d075030003031040704102c100280103c0f8003c1d0f0149400c2d403800ca14085092005030140d42c0036034030a0b00e555401d10a035960125101206680482101401c140c1c030301000c0c0c0c00740152081140c8100600c60802519207042036543c0c41c80401c0d0f80b8401c84040e140d4019204900c13940c02000c0c0d00803010301901a40a000b50080103401101506445034a410041c1261a14564038620000c46858030010f00c007082c0318041c43c55128030a841c010661210b2070312040d1800481e0b01030000b10490015401c0300381051000545411030744 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 737277715 1250 737276465 737276489
    0x80d02030709031e0b1b0d060b0307030b0904030c08030a02190f03050a0612060b0a03050d0c050d1b0b04020f15070c06050f0a05031911031008010e07050118 69
    0x100000380000d01c980012113982604400070701e44031805132842c0d00140d03440303040d8404c640c03290f2032a4407990300020318050118030f0421a81500120754041c0c240141041c84c8032a841e07044c11000a001c0e5480101000d01400d4848204004203a00c0f5030070041c1190843c0815075241c441e941d1000180c89801d400c120341e018203c003243c501940c0a4010f44580901d60380401c055140e5403146025a00744d0301c00c0a116912001c181e80100d41a58404035031740341e00610218506a03030350f0391030781010b2a2032600c801103404080b585003840014482224032042500c3c01ea58940d02004003034030f00520000c1d01501d003624000009045403648540c01391405c1c002800031340061840c04140d511a4081d03a070484084008440009107140070f0b0056941c01196030b40003a0034080e0880007180d1942009040480824858850700344041d4a0321075046482040c3c4d004503602c0c41c041c3ca10444150180c0e100f0500ae81c54055020840500440c0e20402d5480900c0d00081000d0400d542c808000116000380501c804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 737278965 1250 737277715 737277721
    0x6070c0305060a15060f050d061a1314090403031802060c0d030624051e0315030f0d0801090e2b080c030739060209010216031509080d0203 61
    0x28001119840750f0b0031008148140c1940f0034190440540500c100303404078803880c8200851a000760058900d11020090000c0c000340d87d40e0a10448542048448008940008812043e0482e18170700d0400303080084061200c540b04030010607200d4200130320107420550340e1411b2030840e80c0d40880c0b0789070040e00203100b2915100302402e02d0341c5034041f080c2c2140c0444d2802600003013400300c0c200048200800000305998001c581c0b8405d40e41541302a144042e40c000b11040507496209000155000b541c41c20094012a0110428136260003f40041081203034848200700d1f0781d290f031000d06513040d00c0580308007081c3c9100b80e9003041d19114070b180c1c9214851030b815102520000008030480f03e086c506543d0450145c688500701c5480d44425a460400162a088001d1230300c1040503040c0003100410400c0280901d10f59500e03030f480501c4420841c0c0c07076900042c003100250f904015040c038a404009038003c240d0718555528151415003001824604c0e103515000c07050010101c00d4412440d92001d040d590b038a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 737280215 1250 737278965 737278973
    0xa03090c060f090f031109040503070b0106021c0810060302160f0b0a050c040819030908030c060702010c02010b0319032105060a090506010e09040507081b03070504270206070c03 78
    0x900090b5101c0016844403000240c139070707074404200c0460740c012410081da04601380505c0150384d8014001e5403e440104018000554000b480c14000c060940c0a0320580400d840c160f030412004600800410030079400340944000c6010310b40080300c40038180144c4c4c0d00120310075600c00e4010ba00d006003c0700c03c1c85200b02e040c00030080c400c0c1e00ca1781607008100455598108141e031140141e0164502582c0508822000345a155903c00c2000c2d000e4105142c01c81c1d41e80d170085d071540c0d0201c0343e48400d90704402c081c409001d0302401000c4407015140000e10820031844040b955552940028050307801d42c1140c00030915001d00300001e515940b40080303a50405940d001c0e603015081c00c0d20524010070000b000050446038034810b2900480059403820040c20442d02002002034020b0f005480074010014001703242501004001c00c40d600e00000159503007d07590804d801c1c5020340d4003140c0078500385400010185407000c50302d501c0b5900c580e10501d502003e030000c00c285029200d030060100c041c842c0040140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 737281465 1250 737280215 737280227
    0x405010e1204090c030203040f061a090103050f010c021903080a020f0a090806090601050913170c100e0f0a081819050f0a03260f0d1e06030b010b0a03090c06 69
    0x750740d0601c420310101c030603500c1c120100d00c070841b40902040c01c6a40c09c5000070f201d5400100007901100700c0f04a0074040c00c4005000040203038000c40c2c0b6030380f02400a0020700d4080c040c48804101c2030000c0d20f08526110100d000e4101001001400c1211004c00503080d1405a41954a0b14807080343c02c0d51584500e00018108280b030307000b54402c0c2c0c440c8c10700085c2da041c000503840313050726005405001941c44010034061004001d503012948038a000d10380d00700c2e5641d40350180890f01100300092446e03c1d410a0081c088440291843e08940c20016509a07012030000380d410b0640d0b40301c66619901c180c014810103900d403494480c41d500420600c8003102034250000032030290b5604907400395002000500704107a03900c203071000414007103503121b100410640c0c1800228030380c0038082c0c013189803c41c00e1204401962008010350301d44e40c2d41c0d51503c106400c9216846100f40c9210504008080c00d54951541c0034505200d00c1080900c0007a51081d0b061080e0010010301da401040004200d4682c40b014000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 737282715 1250 737281465 737281469
    0x112021201030b19020306030307030f0302090d0b061002370c0b0d0e0a0c0905060f1c1106120112140d0e0f04021615150602010b10031406090405010e1204 68
    0x1c08202c40180421344102842100e002e210002c000310314ac604555002e446459003500a1001c0c5a401d001c5009140c4a5110010465205461940f51403405004100070b9060500e029400c55114507007031050b0f035100c1c1410700c0c02484e401f42010300c00301e002c0e202c0880c92101c0c00c10003413400c58184400292503404401508550052407401c5c810b4058088005580c0c81d1141800b40055251203800c00031401154040c03904180c1c081c0000c1d49048490020500810800010480300c641c200340c01d2040c0420295180011070080742c440b0f281004c680d04503001f00c0c0303060041034407040c011403086003088103401a1800541085042d540000c01039240648220312144e081802101d9101c80748116281c10301c01c4480c046500c0901da85120200e4450260688070b080350498240c1c0c0e00c03030a5050850180c950341d0000d10f4a0b03400800c2040e000d81c2484800785081491000b030500b8144013892000c0010b04103540f200050383c8000ea20b0b61a03081040c0034001110302182ba50140768108020140c00ca001082 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 737283965 1250 737282715 737282731
    0xf070206090a120c05010f0c02012a03050408070911180307150c060c080c041e0801020f04090c030612030c0302100f2007051c0903050712021212090112021201030b 72
    0x1140651703840040d039140324034051080000d082005160019070040d68101140505a1485120144684180700e102035480d4416004941c01203010448640e0030401c03400030f440e0982060102403150742682c4864040d0302c00c0c8554030f64046c5102501a1001c00c00c41004000b84090031400200140c0e02400c0c052501c0b0042e0740040c1011030400d8482d000b12060303801000e8080103146424a00180c1c555031410ba07841210001e580c03508000303400703030090015100700340780401d886503102e1403d0f078a0422640c0c5054500c050505104040041c00b81d000e000081c5c041c0c01d403c10b0100e6210a1030100d05026080b018813000515080741c3c120082c000d40d0016440c2408010005140d0415070b00c13088860284a90090140d8414030441194111066000a4026960038132402060700c0c0e0751800c1c1001e842d0780000b10b40404424048007580303000f50180300d0383c2042901a001c00704690918804074801c14080030305001881801080441c40740e81103d00c18649555010401d58480c07030110340030001590840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 737285215 1250 737283965 737283983
    0xf0307140102070b15030105060108060f010e0f091608090606010e0603060f0a1e050306040b0105010c05150c03100b070f11062106040507080106090e0c0d050907030311120f070206090a12 82
    0x89c06030750040342c40600480008110031901d031448401102c4903c031948103079410a80d0301c0c00c81c0d40142c42d40c5d1000c070b00a20140c40083e18100f07101c0001092900020481c07102135004006001c8141d130030a03640b02d9100810340b95640d49540d903c003c40c1c0c1c0c19402454698120000240c001789103d642e2541002034420001c840141c20741c0cae081019607441d002d80c0d02401c18490100100700960003a01c1c08006e50303105409a881c2407690b140e007010055801c4482c02d030281000030030410350070a00d44100018003a1100d046d804d05210fa151561400482d54004103548981681c0c00020b07a2160141d030713184400041d0b0083e090000041d01d81000e8000c0e18224003560600c000f02c0c101600600c000d605031041c80d51216807007031820003010503050014100075042c88040100d1201c040c02401003500c00c1c0141d0f00140351641c914a4000c08105d800003c1201503004140107805c3d44a4501c112580c041c42c0c40b0b010f40e100e0080c3e00024516203c0c09516a9000406090015851100804001490f07000b82d09031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 737286465 1250 737285215 737285221
    0x60a0c0201150e0c0c0703080f0c212b0f0207020415050d0f03030f0204080d090609140d170a021b030c13050403180609030606080f0307140102070b15030105 69
    0x503291405202003103090140000d0254150348003412500c10b9176012070714003a989845890b400e5010390410540e00100041c0c080f0054420440d038101c02403031034800c1e45802d0000038030140f14010705032200e0044002070108032a800d201070048007400d4102d80104050601140544000d502000c0201d000e1824000d00c40c000100b00c443c40340881314003404c0b000c444101550b0b18010102c2c03182e01202495520100301022300454400340000d0a07084000b404400c00c18171015120404c980e202a0801c1040182170110705845d2410740e07a800e0090741c42ca01102c01c20b180043c006150301c1e1214860300d0f00400c40c290216400038421001c0380f45400c0710307030200c1c144c181490341351030980c074403640c20000707595120750f00100507803049038014024034103002e07900000714202d80307000f07000d622040000f00030304028810304c003240c0b0413240203024110040c21512045a04140c4a0003040c02c0900a590300ba605030002d41029011229102d90003081c1d90030b40e20340721010317401041d061400c5a00940c0382c0000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 737287715 1250 737286465 737286491
    0x180e13060f06030804061103071b231e010c05100203071206060e06030a0b04060303030605211c09030c090606140720181501030c0206190c050408060a0c0201 69
    0x920760a403500803007054502070800314281c41504500c001c2001c1d600c0204149d102040c00e40281980c038480301505422980d141c01c9204005c0088808001c070f8800c1c00946162659607010804040c45061a014218048807100162903515103100050414094141d0183d81e01025500840c8245070545071000360600b40d01826048808901426002c034024030345140c1c96290200c051039003d480a600458450284070104040c0d84c080e600031070100740c4403032040c050791924180039030b0b4100712495031840c00762120050581d200c482101c41c2090500b03103e01c1800e064410121003000d5500412104205a40e6101c500010000c038415400000c801400650180c080002117581098014402c0700601040c1d900441c00c034400072103941c6d8054a600d0f20300318844241c040e0b0a21400c032a4070416900c0490704000340036615100301580071504450b041144c10342c0d00d0301d00701d01440075030100017400400307240007541c0c103100f240c1208166204920030452012a160003210006000d0750091000b44a4441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 737288965 1250 737287715 737287721
    0x1c080702070e040b131a01031502160b0402030c091509010e04033606020105011a0301050108150d020a0b0a11191103100908131a03040201180e13060f 66
    0x1c041e6200c40010120b030101d44d800900c20b03002240c0e50040090160280d0702e16548040b0024030a9031050400b0041040c45100c2c46124600903c81809601e0f1055240b0145441c20300e418000b04201e22040101c1c2c195102000000c10100c00a08512064200700035006011030391440114031851511001141c00c016807402c56003c1d55141d1902d20b5600716034125541d00715079081081134800d58440b109138003c40c84084860061507203400004142d410444034244410180b9150400c00e5410001041666407094109a004101c40030550009041c400058024210a030019521100742c02c40401e04c251a04000c0030460700548031a80b0324912450b1054642d64000c2c202d07088903403c2c03242079000c91a030700081038000303a008094411540394006000c04544003403806440041000c07404204407003100f0000809000c4000038827140e03038443e010541441c840100020b040203880300244005a0f621014440a40100c03201c80155203886001020000e890b0801911054144203540e008458144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 737290215 1250 737288965 737288969
    0x302061c0e0307150b0d020a091a0409030e010c06060b040609150305070e0d080d060b1e0c03390d0e0405010b090d0311030304030302070308060603061e030c031c08070207 75
    0x100c10120001240c0fa0001800c6014511b134101e5102d10300303000160b450701064070240c0303149030300000c0c50a61003c1d10420f00c906000d200d8010362034030a1a1020a40200c04075104110902e84be1069082a140a20203060a0343c031041201001003404100590007800f80401d0756254140d020f038401e42d003002281540d0040c4d0702d8201203891300c0c034950b01509020f180851441d010310b07001d500d04403920301214101c3d4401d500c08401d1220202e04c1003010494a503078451205d0f03420040e01c4c10050b40b40b0055407240b00f003c05904032070380303205154a910301c51154103240024600c141484801c40001f43c00e40c036202400c0c4200001480804604100d107420310880c5d060342c0d040031400b0b04102669040c0003102e02c640c0000e50511034080100940c20008200851149110750380250300c4407494500507004c0f00c030242607140320300c00074010801141c65000c051610140450718070025404c655000c60b0411444881c0350340c150194040003005038240c541300305546505a503803041a07941d021000c0740c81d0240d40c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 737291465 1250 737290215 737290223
    0x30106080a0207150b01210c0e030f06060126040303050f061518030a0b13200603070c0314070803010e0703020f030408130b0703120f0b10180302061c0e0307 69
    0x18100d1410320302c0140c0c814202824181030940c403a401c41c510088103040175190052603075443c0c240398241c56074405420303620390405900412f090150141141e0300d94400800890402070b440c07400d2280c40504010000030500e181040c60b02d14103013402c00901600f41102c4003c00701029a01040300e0341070268204641d4034102203100c0c20702c8404003880c6004074140d03944592500c520b0f84803402046185805c2c90080c0364030784400b040130741503113440c51684686040324410a05001c2d200c00868a9540489610840b14903294511940501c6e0a40b2000f004c1c4403800003003000410070400704685480290b05861000407050426030341d4000071826031084e448960b20521041c0041000604180d02415100042d00b402d0021191103044640d03054200341c40640024a03411049001c7c0f816034402c0c2c4554610102c01805003031100008990b031304801d0b40700c0d2020464a07641c45003040b00c0b010750b0340d80595401800b05640d030000a4440ca0380c0000d0384c0458040c03030700d4000345020320301002048030350403940 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 737292715 1250 737291465 737291483
    0xc03070626060a0506032403030412110406030c060306181a090415050423070602070612020408010c030207120203090913020f04050a021806030c070809011112030106080a0207 77
    0x710050150788000903201d0743d0014250701c00801d03130750340342d038040c6110301d1030f0030410f2042200f2100031500e07109002e030360a03009820412007841030000034070810551070340002605114060071804580244660341c40540340d160b40b0b03040480e0040e419001030301203555602c1e0a0721000d0b100851801115031125407882103100c0120416031a081c0b40a510344c0c0540140d6542121041c41c4a1440580760110b5040b942d115041c19481c0303c0061040160500d04800001059080e0814a02a44d0341c90140a9003042c40015100c05881c03240680442d40506000c6000b40030940e00003c01a0194000401c1104c0610424414054191000040c0d9621420040c10340e0741c0e50700e4050450320301d50740010301030340c11450b0a070340b240858456000d42c0d4007901a000740140d8500e03100744101040daa100381c4e014854001001400210114841030714201c0e5001928595259100c0005858904580ad03640c923150107404400c501c1c0c192600065030490f03a4a4488403066a242c81300c4400300d100710360008142c2d0310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 737293965 1250 737292715 737292767
    0x1203030114010c050709180201081302090a050a09060e0c1807021018020301090312060b070f080a0905130510050906060d15171605030105061c0201051603020c030706 73
    0xb2140c3c64168499004000b03885803d170b00ea0100006503000600f08440c60024102c0030307411544c1c0140460381c840c041c0c594020340d0604030750000320402c0d4040c0c60701440b0f80d04c400201d4003000940c0e001c4480700c0c1d40f10b5820050003c0c000a0707141c0b00e00011804620401000c0819401402d508800500c10880390b07003d0200e2981c902e101c1c40080c10116095221003c800e0341140c01a102481a0342c034482c002c1d2602a20012444040b500740c903103540150800c110b06000207000580700500354100968000e1005032512110b450448072600701e603220b6540229001c0b00e94503032414a40c401f600418100f44503021460f116003d110162400751001d68008000b000040300448180e44169070003e404108002c5669807194120103c0440c200ea040b0346410400f0f50410128503201200c0c0207200a4009111920b40700300040c914111003200481c540401903848011a8816130450340001013014085405403245e08000b99500c083d80b14550080c45042d50200b0074500508400d000c134402c40034030300c2c510300f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 737295215 1250 737293965 737293967
    0x150f0709172814120403030311090a0e040311150601120f0c09140d02150a1214011716180e0f0a1e02090a1d0609010b120303011401 58
    0x18100c1d500e40c00350980b060501c1c600440c115000c6004007951104071100750a121190341c3c58070b20b56610300c0d80013041d003000d65540301c01a6401c0b80d40504000a020750074001c0d001c80e40c440c151010758006e20404022800c01300c0003044500482c000d0740d8100c1c09140d2034612541d41c1d00c82c0c801520a02000a0001c3c665601c281e903080c2013650b0070380303001c2040495288001c040d280c0050024020488132070092111340b0005e00d5004071660100d031840480400368001c103450001c0c40b10b0714440d8000000c0d98510082c00786221041e0005500d004001d028000d4092007440d01080c082c0c841e08000002c0365840c001c1c0300040c04200c0604441801d5000382c9050005d1607540e40b10341001102d107464214510394141c040c07180c40145109213026254081152070404e41041503410311840300101d0002035409601c4a00c0702c00da2000c0e228a001409190180c4d10656851440c07c05031007510808040200130300064015060310072099800c04080b0070346450f6641c80c4d00090041c0300c031130142500c0420140d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 737296465 1250 737295215 737295239
    0x70818010e0d140f120306040c0203070c0303090e06091b0d0b060c1c08090304090b0f04020d0609060b180907050c0303040b010503120403030c060506011e02150f0709 73
    0xa180504085241004000110308a018500429520760311085860f07a4440028011103440503100809801c2d041740c00c0c010085c19002c09000c0c2401a03135070701c0d140448140200102e032082604412031407801c654038680206560b075280140b60408074208007040a5013840d1160070300034a100c071100303407113444031203403409a07504901030101105450300d0846009803244c03002000300c002420081e08008518424111019900000604c1002072002c200b100394500841a04d042c2e03445041c001c00c03601d44180020b8a9064a2544154018400910f60702d042c6500d501c02000c6568284062000a60302d034000c0d44640a545012218400700c00d890381d5851804224050b408600c604125003803504a146c040d185400031602210220001c0c8d006205078501009001c924801c0100c0c802d02e02401c0d950010f0041c5441d4800504a913140e1000c1903d9130b015480d000408402000002c01919074034000030342d145000d00c60703034044048290106001801c8071100e40c3c4624031544444414526080e42d03c580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 737297715 1250 737296465 737296507
    0x20301030512070302102406110714030a0f0611210105011805040203180f0d110715080901110c030405131103041515120b0a06080606010c111002150a020708 69
    0x2d10201c0980c007503040004e001800078180560398884c80600d403146180c1b4100c032b00e80100520040e0f406007a00507590003d03415030401d5020300e08000481e2280b4002c0090f1694a500500b0080d000c1040820003071b00e1600f40441e40001890b6200d566030703400c01911803543c2204600a21180d40c3c03424045801d11390025078200b011580380500740044155502e013070200304010302c2140d4000708152a8843c0d0702405109002c54040050810ba07858281e6410100c52010300e006c060005440028584036002c4d400714820005a014072951010b24202c40d5860340d0141c003e903840346040d5070081c80d00301c003540300301c0346205941c441071071858803031303441350300b0602c0701259685c5e46c594581551301030050750068400005c00182c007c080d2425103074a0500d42040c0c2c02020403540303500d808400c01c9488000120180c22401c00e0034031100321030f040d04280d10002d46001030150031100c03400d0040d0855500140f0800c969003c034445c45001c0c1c070b556444c0b405a1003482c60140c600181805040d00d0b4800c4803424080c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 737298965 1250 737297715 737297741
    0x1802090f0d0606080f011406101b0b010f0608240a180603120c02030d08090304051807090f0b03190e060f060f0f0915060f0d02030103051207030210 65
    0x50828100d2000a11950300380c401151025100c003810031151a0810007902c8022004000b840788403051108451a4000100a03c0c0306100c0021600c491034099000c22003c1e000c00c07000940300003010708040344000e03001e2080040030100d200b00065901d00c01e078000741c01220044403d44030798280840c0d2040c41081107207015405004a140000e90010314190f1000c98854000e002c0703030311843c6040244030003001ca5090414480c40c04108001039a000c1104446100c6a003000703412070f12140d0140e8039500460308000d8014002810701d006030b1541480080c450b0340b9940d50507003016252440646038031a00d02c5070f01c00c1c0c11001d0003c5003a90840d50b60315200032561a030300081c914540c01400c0d181a0041e01c8064600404505000c0c02d4100300251400e22030302076449610f1104050041454904000c04140c90030390740030101003840e66920b00f1510f0340100b00c14559151528042004029030007071100f2030342403051400310214410403409403010b103501500940644142054007001070680007030025 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 737300215 1250 737298965 737298979
    0x90207111912020618061309060f0608280213140f06030c0306010c1520031006030b0301090f030f080f0c0f0a0306030203100f0b030f1906020405030d05120709180209 73
    0x907842d4403404003800c480c201e407001f141c024610741180003003101e600e600200519030061005001c1180c0011039150040c89a046900900c4041031003d01c0888524840641146c00010a80e000a19504001081d111401100c0350080041d500304041e25201c0c0800329004902400050071807282c4ca00036683c014810304005020142c0c1d50b54051103000c0c4205840080d0b65100b416180702200c1140360305151403086002881e50a203d1640c00781a1400d00c160300400d40c4032235141c0e403252000e410442d0700760390018034151580340302e140c00303000d0442500380180029100d80c0003551204100d07540ea40503101912401e0324120300301081550941c080b0350366000307041c2c490000200580b800c0000080b04403c00200003000c0980042140a941581d56158800e500600852042d10404250f00440ca100c0703400b41c03803060071149014006801244d0010358107011304a000e004294202300104500d81000b000b82d000e680d80c0420541d01c04000340602c0b42e4140040b47c81245045540e8010003102000a000d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 737301465 1250 737300215 737300257
    0xa090209040f152a02070515030106020f0111030103120e0a090f06060e03061303210b210c150705030c0703050c03071208090a0902071119120206 64
    0x20580c4030009403011200382c0d5200003404148103d8a1504007041a074160a0142c40759508070310744107036501140340c0400403120707016886a80c004c00c110b13802454040d04a82290002428a40f9242c209104244c00f5000380100300340c1c2d603032041c40b0720803030100420303041ca003541d08588940002207145854101402540545401c26584910040e03000b068490408500f60690040c0e0005a41941c2d0041050000ca440d000c2c030141d6011401c80d9108004050312094994541001c66200000743e0758005240c03005000c40e00c044255800080f8080c0c4c0603116140c800b11340001c0904409141002c09183c1d03000640b400001d440c101c4482e02d0074071040700303c00d400c000c0a519140e08651002900001075400321004108008003801703d0401042d0860207440843d01c0c00d0001111412035100003007040c40002a09039650355612010700c00780c400350b0021034480c01e5030700d0984000d80200c42114440e202d118071218807170900c1395041c010794110180042c002a810350a10141c5e0b00301d504401c8441046440b0703 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 737302715 1250 737301465 737301469
    0x291f150903060f02160b2401170a0908040806041e0816061d0105061048030e0910050604052b0309180b01080c1309050109020403150c0f080a0902 64
    0x5e51542c50b4050441b030001e80c10042400010006400d040803120750131005091310076070b000360b0072076010710b206071480b401035917202d02000013080540001071a410000c50041107150b40062036610451042001d80080048850100411001d0700002014090208002181d1755003490001d021544240343c04244d0020040c1c1d4100e0911204075003082c0e40c1c1d526805c1004a2600c84003005040d9518104841011a2160345450680c00e42418007100f4207400d880740902c901c1000c01120890229107141a02e9950780307801044424100c08640c070848104c000b0a95003840325802c0c4007205c03801070225190501c5e2500340900c203c10790030800300c00f20b1040d9414075220901c4100040705441303550350307980650414a00c1aa80b00c1c441110801c404c1c5446100c507050790f00400d10701d80001c1c100b01a151146e15401000c0c0341c1c1800e58100c0d01041e420200009852405500504141d81c03041300707030b44d0f054030103c0741ca01d00b19450121700200150415464410041c0203043c0d8039044a20901c01040c03170449600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 737303965 1250 737302715 737302747
    0x7020105090a1701151e050d031e0306060206100602030414120d080103051501120f0204090611180103020c190825020f010318291f150903060f02 64
    0x10115642e5181d50b0304240341740d007003009040a0708184400803a2800701e1900603030080004d00480d070003103000c61001e01c20b15000d180004500c008072074100300d40101c00303031008018082d60b100380d03c00f601c214030120b18084640482c02003500c031030340e0007107041c01c1c60500c00e00b1012007440401d40c2c004025440f019805070741030100801c803019a8032042d520307516500c0c0ca02e14089c010303c01e09240a18140051085132110b0180c01c8480d40c006038041c0d2501c0c021700000e4020705080d90024039480c80d01c1c0384100c0702c5500c140901500d180d00203002e502c0c0c2c0c0165006605030322424004203002d4100d626030300090b65680706400b010a00500d01d041c10203d10224442c1004034142ca94061a0a50301d0044110b1074001e486260101080c64240002c22541c11456119404401d004142c0308414804400a40b5481e4040d2204003c00c20b00c0b81c040c1c109403050030000403540b441c040449042d4280466580340191412042480c1e5a8800001d90f2543d207d03000208403400c0400e14264013000000b51012041c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 737305215 1250 737303965 737303999
    0x304030501060e0105011707050912100b100c1505150d060501090f0212060d060b1c0c08070b1e0702060403111002010b031e012a03060b0f07020105090a 67
    0x10000a000c1d03040c840140b0f200d1105034030460420000550164802502841c00354009059090150722400c624001580705040d041a11613507208581d45608030300c0c00c9800030000001c060744c00320919282c10340200c885011180024240c803001101c0345401008540c0081c0d44816202c021404001c0707004001201070741c1c0101c0c140d4135140c403107005200038501403040056000e50b0b4641180b030502012541002d00c0c0004140910420b000d44545042c010f00390820300e401c070002010115114461030000c02854087c85069034100c541882c0032030b04100c0020064182c602d1405420305084010146e9141c1100052183c984400c003031124900580790705000c0d2001d940f14118000c1d0401e2568203000001c9041000d180c11603042422144a0b6100840d00c0f91030440748580c80840c90045082281c09000d0015040c107020301c25200d58010310301120348000541c8020b54050050565804d0030b4020790041c007440400034541048100010f601520080000f0034002d40359050071640c4503501096000c4030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 737306465 1250 737305215 737305223
    0x30903090d0c150512070903020a05010c030e030304180b030a05070b0a02010207060507050306010e040515061e0a050a020601082107051515011103040b07260c03040609050f2808030403 81
    0x1c60300d8150a0f40c0f0001e410f46c401c80c02d1034001980c1c1c1c656000200845018410385040c01070030100340b001c1c03521a09004044010140c104d0ba61307076651b2100314248032042075000c540c6902e001c820308400d01e000300b08035203599040360003000301c2414682014202e83c0244e60100c29503508102400020b00240140c40c0f040c0c1d81c41e118940c803440c215002400f5401400780b15442680382c002044112951003c5d01c40a070841562042c0d150101000105001c0e50b061308100c0810034041a80c40e0100e6102c00140304900540d400c2d5030040e6a106545075891042403040c030480c0402210315068540b0340350103020858000d508848a42c001035071900300742041920a00b56090001d1081092943c100d035884404265a000a40c54a442d003400c807042c03400ba01400400301c0404400e20940d246025113000c41e6000000945a501e5001d045c226580b50703c0b500c1a9000f29030001c50000e858544042a032405040161581041c1d00f200f4814410751001481e014031520124500031800700000c1014201640c82 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 737307715 1250 737306465 737306467
    0x4201c09110108070804050607030c0201090f0b0a150608040f0804090e0706112803050c100603050d030504021804050f0304060903060b0303090d030f090b2d030903090d0c1505 77
    0x40c200014404074000349076401740410441400006040048d056034002d8962038001403040500a0807400f6184082014208648241c100410310009122140c0141d00a0004103e1113411150400e0300c22640d20942c8082503918001030f011030400600d1622442c400c04a85103031a4499414204a17990380100d811036600039601400301580202800c00b4100d40c0600409001c850346a080540030394007010310070404a4410b40c1c1c0100f42c083d00a40d015450130906540a04612121880c01801541303c04e07901031246030400b40c1d26501030b20506028a40142000756031000442c003102100101400c216100e201d901d91030346800400b4805400a030595a60f64805149142800c5041c2c504c0444201c0c880d030010046801240d5441c0400b421066250501c443d994881c01000da41d1410b055100c00c1ca21240066100c43c0c201d0019031340d000703114030403007601c0030a002c0e04c034030305050701007141c0c10001d580c400c200c08202c528252030701402d01c0f1312a20841002075210000402d070303006100459408200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 737308965 1250 737307715 737307743
    0x100c060e0705100e0d080f0304050c0a031a0402130f0b0a1e180605100f120528060302031212010b0c1506040e1e01060504201c09 57
    0x9600818149400140003064070500780720000c2c2c5100310100c01c407800c0c0074021001030810f032100c1c0302c4400080d030082e510f10f803a654031003242c029540c4202c908a8813401100c0e204001c516103542800c0c2035039040070060f080340121105104a11030003030001ea0b440b029480c040d204201d01d900400844a03070081001c03540311034520a101c0c490070380d50003696101e0380c801d21000d09484245403403001c44400c1000c50300c01c0803075052280c000b040d0740c0d0415500305901c020402c448507004009030300705406655918080813114100700c011101c050b92a08039103003050350f5400c5000c0300602031001480c3c10030400a240c1c1c3e07490b4002490002180c151562900003c07413010b28904000d090039004068042b9201d140a5062800f103454100344400c1648400424000c41d42c191950740c030200c0c00c00045401c680b5481c580c10001d203800b5454000e502407a41c02c00744042583e04050094001032103660703691403055442e903403c490250b04076114088485038666200c04d4011054040c030441c0340c1c00303126400c081070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 737310215 1250 737308965 737308973
    0x50f120103050d11030705210c0604080702011d24040f2309013816050705040c17061c06050105040b0d080910110a0606090b03010b030316060605100c 66
    0x9401d0075600131600309000ca40045400820a110504400201641c1030781402c1100c01c07441c0070301c54030351180384900000c100030820403c004000c0c46000740c980802d500c011140303005542d101c0010b0341f50021000040101c0a0388021590026855410f90107820903860340030a01100d4990b5100d800c1400280f034089810030200314100640030004c0e1858142503061005404201e90820040400e641584c0c1891559900700d210301d80c0d1290200303030440e90303446001112a200410b05101034070030340035400d0001500d242c103118159001c201500e8040080300c0d80510994034a000401c00381c0c000040c50040901c10b40307042c3c1c0c00d4961038411800050a5410401440300f12205180514000c9102221907008136a020082d41c000720400c03540341c1c4c4000f02c010811030304007815000a034460b100f01c0018808200d10b03908004165136400408000c01882602014240c0c3c0e6603143d00f81d095042040301c209012140c42c160142d0301d02450f004161075a0744c0b8089000d24220030540030014071000944001c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 737311465 1250 737310215 737310227
    0x609020f030a11040305030f03150a03030f0201051005010e06070c0b03190605040203010e0a1a0402030a0606080906070816020c1306031a060a2601050907061701060f050f120103050d 80
    0x55803050f01400e041500710750340d04e039982c4500740000480c1e100100009041c40c4486141d000354a10207040c0c09100740e52840c0180004009131100c1d009542082c00103020140840c280c102100c030141e40711075811030900c4c1803140d59403003480140d400c0942c0f49004243c40845500550040320b01d070b030302c490340003103d00c000c8000c50342c881d00602d100e9401000104840310b0400d102c560481c8111400152012900340d042c0401d610300d0030040d0f00f0a0000c0208218100030364400c03c1181e9135a200c111265480f8002e444e1514002c50b032140c0429049804905c24000900c03565408403e14012540b034080310380001428181090000c6000700e40f1440c0a0042094400498103404040b030244081418400000380d110211800b5400b240307858100100c8081d5120883c2181b01700440008004501303140080c0d079111800c07401160301280b050b83e07560146101c0140c0e100d0480351113a4605801c540340c08000c681680c0564661900700009224900c180080c00b4107003030003180310f44020710b04082940c0005d082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 737312715 1250 737311465 737311481
    0x237020f030a0f050c010b130605030c010e060a180b1215040e0a080a030b060f07050105160815010e030d02010b031014010b07030c0b070509190501020c10030609020f030a 75
    0x200e070414071074005a160001c6480d0303018152424502d803105215151a0f004102c504092544444070000b05a4000499881081547d800750305645170105000010f503008440b800020b904040100710104155200d580000040c0020003501d000160ba0340e6101e100540203031140111076490070052028140e420703105c00342c1c1b12405a40600445010040042c0c551144200150400c240090860f00541c0300342d01944080c04014543c9071501c044100904054200100481d1250729280c007141c102c2038060a0207210a2483d0b0301c818450b0381d0a50309050118080309020b051040700c0d000c0c100340707940a00503002038803020380c000684010380c0f07000c06140c41c0c01289490445c5180244d000280601041c4943c151010200f4680d640d49040c90b0460f403d58412602810214696003848601c0c6c3c1c0c00001080c0701d4108640d01c2100070665104940d401c2854414240543e121500520300d600b03161481068113500c03401c0c0044c0e01e075a900381c62020780e40944d0f40b00c0c118090010400c61082124452000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 737313965 1250 737312715 737312743
    0x7050a08031c050126030903070f0f1406220b0708070c170706081504090503031501090e0a0c0e1c03020f0615010c14010609061422023702 61
    0xf0042d4034240c0055082c2d022a801c0e0000342e807403001292407580c01041142c0310f0340000f03021a09055a40c4848650301101c038090300c00a24030f242c2c40000c0d040c00c1d0b985440801c1c0c80c0106042c0c40d22640c01e420740c451480c8400000344149501c3c20004541a4440152983e10300440900c0d079100340d90325026418200725000509114602c110b24070f103011000820505803206410038140c00e484241c01c40c0724414040031820381c803a042500d10000c00c0030101c0550300034107400451045000044005444d2414a1f000f003140751803200700010701030103441c0c1010109008605182100c5c9400c1c5001c146034004d8900300942030724010802008040d81002030701e40042c42c03100030b022a800c1c49400c0030003044800c00554100400d50070010144040700b0499807512803100d00800038141da511612024000310711840b52680841d00580c5c0840c1000b00d100102e0780d240200b169500540450410300030b4000d0074681050f80d40044032000200c0780380c2c8052b000342000d00c80100d802c1d045504024a00948809410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 737315215 1250 737313965 737313971
    0xa170d0f140a0e0d0804030c0b070312050c130f18020906160311031c0506040e0a230708060f09070e0411040f1d1209030303150307050a08031c 63
    0x120916480680003403011008000070b40e5505008204948400481e40002c2e40420304d681d6078402c00548100a008891007035a48001c041c0e5505400ca515007d1400080c0118a0403c201100c40e00e03641d0109900a8051545a00f00704600440000500755908030320600329565070280103084228881c5405000e012009501d00303003e40780801d046000d01d03c5a5030130162503581c00c20130940204110f00360b00100c1e100b00c1303413106448540340480701803d9a40400e035a00e002d011840a0500c2d00400104c0903004000b400c03204081d68071310f02151002102c12003420400106440340344000e02160004186c00720051500f410028985810301e0030141c00c8021707550064004110344080c5c42c190f140d00039004800d9010401c07103840420058030a010303080d88090b103000382a103542c5071001300d40010f054201e000c41e0b0303e00920b56003e25a178803071085595850342c014400200d150f100848003007500e40e40502511851640e410221b000c007210b0f0f4210202c1034001180c40c82c04084441a844c1d4500c041e04814 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 737316465 1250 737315215 737315237
    0x4050a02210c04030203060901050f060604030503030411030106050a030f06052203050f0f031f06080118051b03090a0611040f0303030902043b0304050303270a170d 72
    0x91641150801c0480c1000d000d080c0010682c0c9015429a001950081c09440b550710b49421250700a000c1101c0c5031307100c0c43c5120041125400c20500340e0f01626441001107141d510340d40c494201150300d6a10b5664990b49403000070072075880e103c41d0640250b208052030109040140350030415548010b0002c8594500040384003180c45a0304a120102c54140c104680e40390303c1c040100000c0c0c4039000d49001102d00000600c104280d1420070240658000082440029190042140c03918400c2c42910611070954105842c1000c3c1c940c019504142640f02c2c4522121000f900040241c004580c0180f081d00b018000a06100244c01150301032400700c00c0c1289420f041c100004144c001901004d000c240d0348240712001c545580e8002c88100d06600c102c0340101d00780c0e42c080c50345042e0640306005109215030b030800444100000341c8003034400c020080c5060003824040c10429600c0300d0a1032030886181541d485058550001c0c43e000307842c000598184c040190b00b0000d1400f140000e4800030081c2c0c032202 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 737317715 1250 737316465 737316487
    0x409211101180f1b0f0305010e1f0b01200d0807051e03040f150515030109021530010312020606181905090c0405100b1e0408010f0b04050a02 62
    0x8801c0b6801d500203096481c0b08583d00740300301001500d40014159002090010a1201c1d070448980100c0340700e10b0007840090614201544c4501c41c00c0d50640da211028400b21820001c80d030020f8440840602d0710400c01e640e074a444503030001c46050411603c1d001824412003296001d01156400744040c100399260100c40111803030385e200d03a078810114040c4080017040c20003400e0007410b00c59680198030807a80f0300501c59407000800301500c0c1810725040d040d1b5000c4082c141030140000060b002499030302219864030300c0f92203036442900c252001c1d04003425440c008841c0b80403e04001200300380441115030440c50a011022000e41100b0700b03541c41101000100c4d55008a889500491844c54800c0f40d2101c0e026401480c0384d5a240b401c2840c01e080c100300348000c0000301444400780c00c2310180041d4546480390f8071800405d00511020b02402c0000a02400300d80210026441c440b00314180b0301943c40c510389003180d51042e07e046026032103864500e92403610b130003101d4200040c03010452609140f180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 737318965 1250 737317715 737317751
    0x6031204030503121302040e0f010501120c0302060d0e06090703030906050f0307030c120c020c18010b0313080d050c0901081006020d110a121809020304150b0409211101 74
    0x1041c00c0c0d229000c4005a0030303407803984c5401714207a8050810b0240c81c00408c050f03a20b504440c448110f49610700000000e01c1100c100c0485565034001c00c1d010701d00743c02e68090245540c821580c50400684407501d1080100b8101f20f111700c201100700c09401d8950841c58010314140481d440042000428132820142e04007200440c1e030014030754240040e4100d5050410340702d540d0184500c8440500d803a0320000c3c220740101e00351702c03441c3c0c04940200c01483c05060303110b07540344280640d410300c040a2002901040d54002d500030000e00a0b05a2410f02d03481003c1c1100740d4408403440d01040300d020401002558100752896080f05410401460709400c00c1802580c0d401039080c80c0c4104101e92019a000d1201413203021142908010030344462860403a002e8202c0f00500c40c03c2d190402c0d88240010000c40e58401d5034040ca9020580c0d180f018201039a40c405011001d9906a1040c5c2c2c80304030000040200b40b00c004280c045203612910340038052000360241c01007035403101c0719904207030701410002d070008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 737320215 1250 737318965 737318977
    0x180103031418040c21020d0e07060804021e030a06020a02010e0c0f1c120509011d010e361005150d02030c0d02040f0e070f0c06021b100506031204030503 67
    0x1540000390030114160171185404043c4460a03415049a59116000c059400034002c02181c8030003484001c100000065a03480c651181c00c001910300c00103e4010314110b5500043c4002c0341041c3c80d002e20705400007a0422031034400441d14168000b820b01e040700d80a0107909843e45204010308000c000c81c40100d0030798540b814503284075030305400705150203000b80c0000300402c64010701100b0080c2e5100030060459800224074502140c08245000320b00d441d04400081085130680d00e0702d030341700e1800b400c0c001c854400c00301001c7d0410045240c3c4954180091000300380c5071001c03003101c41034141903c00303910512040c0c12043c05580075042600d0314400310402ca8501d9006c3d200b0040c1d590741c59695035407650151510a035501d5000180000300048840003007019501d41e1555100d00741c85006054483c03100910103540400c0340d00d0f54101c041062a40680210f0880e440340c803030f02982c40500d4500f06a6002881d9420320707a2441403050506042200342040494032070440c4c80c3c64219101c9564900943d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 737321465 1250 737320215 737320219
    0x30a080409140c13090b011106040b01030201200705040225030e0f0a0803070807050703050607020d030f050601020c0d051c0519050f07110120011b020304050d0204020c030702180103031418 83
    0x2624107000b16900c140312310201d440502c0166681420b1514005021980078802640000c2d4030040c0c4d0003090100700081080e80c03000b90010a0320030f140c402400041e4002c03400c00c1c80102c2c200ca005c602c00f0640c0114071205ea0744203688000d4002005070812812030000045140141e04403103060104a000208030f850003904a207043d610b800d00381c9810351804145400003080f90140300e040c05011074002034924641c4025032014404112600150f204549003120020b006901c034400c204800c0c01d1240c04403c00500500903078030f9200450010003900714500f00b2101c001840080d2510704810b400c034401a04010901c1c185151084030b40c505e0100e80685407018111240120500080d40c1c014100001c94003504d40d4008042c440d43d030101802000d24281513003c052020340d404e49150b2012003140c003612001028040340021a4083c030000750816510a042840200130350005669429410180d441c2d401c145000a0b6056160040c15408034a9195802e0903051200400288804141030144041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 737322715 1250 737321465 737321471
    0x17101a0d060504021b01111201060f09091107050f0a051f0609050f091c080c1809040f0c060804030e040e03120408090f0a1a09030a080409140c1309 65
    0x3810051004118a610a66100c2d20001d1240c0f1500030070740064884022000c020001d01d0300303181c0340c1e00b020710a5848960550350740900501c660b81c0a010b04843e6003400345803012401d40c9801115003100c145e000301001a130300200e026030402c41c0801c1340c507001d040034070060030100030a541d0300d0f82c4e00c1980b203501207040702c404085200d1000242d8818001015004010701c406d007004240b02c001102c094800c5084c41c0590541d00006a10200d80c4480c3c280d5903690b80346d01a42c82120142080d040854103005950749001e051031603079074654229004502401b0300c003001d03c90924080c600380b00d035948044144543c803020000401d4000303048980050040d580030491404000407a8250300caa40003882d0061100003c0c481440414030140c84088001d98401c109072850303008100303a40e0807a20940420500c00c0300d0b2440001c100a003d48480c2d10080d00329109042d490b0380f88001c603001a000000000e41d42e0303044040c10123640d07071003a4209108022092030541d031540b1202580b40075001c6c1941d4161 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 737323965 1250 737322715 737322727
    0x4051f061e1a07050319080615090901090b0f180a140c07030302070c0e0f01140f0603310501020a02010c1b03140d14090705090f010311060d0c17101a 66
    0x1800b4800c4400f9020710196680701070014034001f5003000019503800f400b601c1e044c000700c0340610444084900c40c00d0000c12041040c1c3c40c049424018000030145560480106103801a154680512071310603c41039400d0b086261038007000c1002102c462192004041d00b0800610003101100d00c2103520858241c6000b69854509050100481d17410381e000303001030f2000c0010014001c610034941d9040e03480d041c141c00c0f5004401070412030000e41c0c40e0384070741d40000c8c00c10106540c0707401810304140000c03440074115040310442000300700b000004032083d202650002050a00d5540c2845400301d50303001c07070a02c9001c003981c61400a0046006034001801e00c4a844400740000c1000810f468001d20b20b5101845802070300b44007801a0f00d41070b942d0031814420700f0320128192900d83c1c400b51150b40d201101e64816840c4d901ca41050b84000801c86800050801ca0f0340300840c070320b01904a81c0451a00c541c4c00040b80303110180509440113002070242c0d94496018400004074a11101c0c0000202c0d81c10307500c0d02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 737325215 1250 737323965 737323973
    0x11120a0201271502011e06080304060e03100e1005060103060b300108030405010216060c0f0303140a0911010f051b010b1c020315090d0804051f061e1a07 67
    0x90b0781d0790403100c3c18104401c000d220305a415003241c19400305240b0940c0c414000c035610201516a640100d113016042407100b40039083c850b83c4100300c01080101181d110302e034113050107030440c0c10f11503d10480c0e0301f203c05042d010710914002d20382c2011003071a040040c036144c2841c1040c0c0e40a0f5201a041861001c0c14004d490a0030008011502107480914030035540d407010b965981e0352180c490b5034003500803c102c603180c08880e498241d003210360715140c0b80303c40c9096035036050088000d920b003103043c165036507020045040181c103030903c147e0040400107044845801d2000a411142c3c448034104403215110074002c561003003c0e00d4002140000d10415a0160900b80d4090b191002c065078200b1001201000c05400401500c3c800390300941c00e0702ca441e03942c6886805a18811600e100d12030b4001c6906007c400c0c03007400c101c0e500c00c0c0070750241c1d48150070014607421101d28011500c0c05842d290b141c140070100d030094600301011504907101c0402c0303140914032908013407a00d80101280b4001706429042c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 737326465 1250 737325215 737325287
    0x1306150c0212160603110c06090c27130f06140a0e010e51010602061e0403090e1014120c0415050d0305040f090b0f04240311120a0201 59
    0x2601f000e064411510301022041d80c3c4481c010045445411100300c01c0d4145500b00b81c020384204401d80b141c010540c1c0300d42160180c9081c0602c100c1d19000ca02681c040454018400d00c0d4580d001c04024545a08020b103210040c0d50309228504030ba645012090320103444002401f82c503069400c00e18200ca0200c0c1d040050000110251912000028040b040102c2101c90710070100083c3c152070195503a41c07140012a41c59504403418100055080d01c0260400c104446003a8031a10901d481c5082e651141c0300b140b051401a035032501c2522007424181f140c842c480701590303a500e505850b1005000b0300d0003005d503900c4421720741460049546000381c09200b0410744401d0007401e000380c01130910807814a4000d056612a03c55240490074424021490f965280251400084001c1c4407051003261082000001c04074480f003601d960b44a4444010000b00a2045070015030048160003c000c00e01d1052082080b005010f20107923800410607940142e0b00a14854090300c0fa242c94241c900d4007068640000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 737327715 1250 737326465 737326477
    0x3070203070f140a05030d14070f080910021b010506040c1403040519030f27090e0a12050d050f0108031608070609060c020f0111091306150c021216060311 68
    0x1d0041303008220038440f0020081a029501c55001c1005500700e00ba42c5480010954031040040c041104140784180b240303001540182c900d0040c0d5105400c100a0b1100302c2c0c0c04021400190052031051203903c05003841041c0c0c1c09a001d66062058000c4050f00070011780c000c103103007440c00a0203c046018440308103d4031030b5111105015140a01843c10f000d4120110028004e0000301414190301200d6100e401c401a0941410405100c1c2c6040c9103030a80605030044101da580d105802d9254046103200401500026107516440c2d600d500e02c42580c001e40b540204950300d52000c000041110000000c1200c480b0005641e80038100c00c024948000c0c60721807001c014101c0e904060185c0d0034800c01d5403003100c0001e000d4088492080e00c60f0303840c0342a100080300c2c802e8070050910000d0007a081414103056032001807840000c81030b440c1e030000b044901c3c8184030440040c405140311002c42c14540545544412480014214400340180c004191030060086004164a50754856490550314080e00d0b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 737328965 1250 737327715 737327753
    0x61515070f06020f2d0d020705150c0d0e030310050108040201170903253210060806090304151b21020111070203061803070b191103070203070f 63
    0x9600c88130403550401caa00001001e80c500c003805050381480048008240100c02003d0f8511342c00c00080a00c1d043c000d41110809489600401362802c2240091080c00c1d032017060411003251301c40382070341260b07021070701d6a0040f050031390f200700180038070720064030901c50480d007091800c280d09070345a00c01250303210030014640d190071140030288035000340080040c181700d2002e0720010000207aa044a10701e48401900080c00c006a903040031100710b0380c203081c5c05281d101011060403c24a0100c0144d24007465008903142c80ca03550402402641d80c140001500034000c1c5004604003030804a003807103030121180500040c040315201600c2e403800c400780040403a0f60000c100786840400f00782d240a0302c13009108080c005520705107460081091440c19203800c0c1c1d801900a01d00380e6207220030210010044010f040107440244411400038800d5003101d8803130340c064801d0310009400c0c0e4031400700392065844226008a014820051083d6000040d50039403a00301c0b00341448241541009100e03000e8000b0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 737330215 1250 737328965 737328967
    0x80a03110708090910140411041701050a0605090601090603020319090302010507090f0f0b090d0503041e090207030e27160e060301030305030f0406240503061515070f0602 75
    0x40140100000a0300f40c01c0c0090b41d2080f15513481c901c408040501c00c4c00392589070542c58442210505050340100260200e00e00d0546c03a240d00d401c2e6044e2000142d041591050391a1030821280b43e0040c01550014502500d02c40c0140c18150006018200d150161404240d070201c0001c1c2102100d03034800c43c0d802e45005c1c08200d03018860030000e010309401c07584640030600d0000b00246c0e103c8161420001c544005c3e48980c126814180040002d074410760038107511980c000304100115105000030001030003c10f10ba000c0410b0255080c200602542c2e11410b1494418401d04010a41003651851945004c90304402c140320b00398140f0041d03510114101100002180c1088801d0445000c044c1e041345080c0c984681c01c010020810030741344002d01005000500500108444001d440c21a0fa0030510914011407002480d0250f203054152400c035032080c915240320100901e08052048640050340610604a10030002c004070b659401c1d40e40e045036580d000058030a0a12146000142030a40e0148080d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 737331465 1250 737330215 737330227
    0x18150a0c0b070912080c010c08070509221a09071106040b04050313030b100b07080f0702011b050a0212031614030c0708100e0a05070308030a02040513090302070909030507080a0311 79
    0xda091b013114489440d40e601c0c048444c18034a004444851043c1ca0a9440914180c0c2410504c814140442c4801e000300122000c0403405031518028500ca11407280001c040004518007040711190020b031042c000d12810ba090401c0f40a00070170388541c895000100c000c0d490319186005480c501c211980b210550a5081c0d012080100c504803e600030001c02025803031054607032003500d48074401d406000340907020402c1600300c1c0d204040302401005005040c4858102e103c41140c0005c54800d1208881c3c541003000c50f5011403030100c2c1823650a0155400071070524010700201030741d4811240d005081c150881c10b80c41c084007001c0080324070010702c6038250361080350b4407908543da40ba85010118581c500f081043d680c8c4440c0040d48100040d00080148202072850f01d440d621a40040c0224074055020071000c2204d4503210500030381c1070f2803450001404810b50a0090420350650031000e0050b043c070404001080d40403003030ba003072640c00c6042250744054038482a40141070301003144040303010100315 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 737332715 1250 737331465 737331473
    0x203010c0f120c1b150c0f17070c050a0b0f010905040221010e010c08010e06010f050a030513060504030503150f0303070201140403051213140901060c0203011118150a0c0b070912 78
    0x4018450b8a007800c1400314000a010030f0740e02000c0e03442c403500004d02312040c0b14541c2803203000c480d03005100ea0400094984282d100c4034107103401c070182503072140829000c7c009001c80e0200c40600520080008004c070b8140f9a00080e6103100598002010303d22440c01c04145120031f40c451543c000854000b040210340288014000b05002d206034038400c284800080d01c3d80d40180800340340c070050b40e50703491701d403e890902c02d40040002030440d400b21700f1203068403000a0078034402c0b207003d54020b0721501d88901d030400340900001c400c20f1048e0300035007407000d0342040350300c0020640f0301080d424240071600207201d490850544c0581d51000e001f43c130807811600f0040d45108000c0190208000840c45580d85908400100c01c0600c00b2154000b10a0f1004000c075600c00e2009190080c802030000c260a0100a101c1405810901505408e10201e402806480c0380c404c0d550f900441c080c111540c18800003440c06003a091882c440904544000000140218480c0481c88090300c0481910901c40b0100c0c24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 737333965 1250 737332715 737332733
    0x11409010f050a0b0f091f060905090a06030201321813050402030c211c090807030506130c08030f030609010608060f040218030106080a0203010c0f120c1b 68
    0x31031111058030b42000302d0f5142107103000d01d610140e00a040640c60410200c1070148081c3c3c010064040c440381040031501c400c43d9017003200c00a0a0595a0144441c100410040300c5000607000d0119545030610400050341c100c00506001c0311000301d2700042e20103802101c20342441e402c000c0c1140e40000506d20384c41c07a040c0390346e13100041e905a50445803103070956040800c490080c0d030083d500d9800340750340c000d0a00e06003094141d0180000301d540b001d40e6006020a2a0840344081f0181506a282420722142ea000303c542c80104207000013442c4031851601c40070b0322100c0140007110000584035554050040311a07209000309504c0003102c1c0c0d9401001c8400c4d2142c3c0003960514031a69044d00001070051246030868012007000740b8007032141e8115401c1100a501ca003480c8a03480104000880c0c40c0d0341c080c8680c8004111040182801a1aa104140c21903517550b03000c42c148400c0c2c0ca5a02c1085610803840343c400020001c000411070b000080641d456000303030f40c11009400035080b0f09010016824 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 737335215 1250 737333965 737333981
    0x1e0a02010e100f1103130206030705070f03090509060d23120703081f06120c180611010f0c090911070c06120e060702030f160b0f24010e090901140901 66
    0x43d104100a020030004034106210035540904c801120b001c0280151800c000110b8200100d820b11031320380304181da100c04803500b4103030082d4085800f001c01080b1070300f00f14212542c006001c0b9a02020503040b40d03103c9480720030340d0300c0000d5048000038400e02c24032820001c00325413405001e0401e0702c802e981c0c60010100c85003221000040f1150004102e0f10054905e40d160642d43e403070b190000500d460850035030003050800c00060030009041d101c6010346a00d500c924001d02110364a0302c2540301441c0040e42990200e0046200c568640034030640e0f01a0301c942c0c082e059900384100458503040d03800071501e00d80121040a4000c4940580016080d600401125203071145090140000e40c0c1c00c0e00d01c181ca0b50b004a8804001da0410819a40000303010001012807034811109000e80d46120f07101c502280340116014940a1040c0f018403c80d1042050882c400c1078800004c00c4440d600000000d05074044914030600807080c03000890701e44c140070b42010a000425010010540c0740424001d03010348003079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 737336465 1250 737335215 737335241
    0x2270a051207140301061404021e0309330c030405030403050610031101090302010906050f0d0c26010b0d09060b040516090902032e03060203090307030905061e0a02010e10 75
    0x5901003c0d1035003010300900080b640100c40e01c04404407440c042c80081c5d4802c9612089401d2105410580f2a000e8030103140212040340041c550b101c001024244562070135114003c0c2031410a00c98000c1800003000301d50300496628040341c8980725071074100d2442c044d541005106000790010030000c100400e4414084a0194803184003080c8100c0c010745148145000107070005100380c8040c0301050250005154000700c06072403030701d07014158640324101c0740d40c00100c40000d614010003020383c07009602c4040e07008503801d05003075440d450074026000314800d42001a01c5070307856009030800e008403640201c1e600d05000e04140154900034820800081154020401054080501081001d058420b0300d1065181c0404004c00e03002003000032004a51603200c035034004650b0340c40800011010f00140d0b00601d01d0701e0046071220711910300603141c2a01d60700540e004000610880080031006101d03450907608941d540c0c0e82d5050022012409006001031490b41841034070300e072200351281e03640011002c00007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 737337715 1250 737336465 737336489
    0x2001050901053c0c04090501080a0201030e0f0d0e01050c160510020c0603010308071416050a1706060108100b0406020610120203030a050c01150306050901050105030102270a051207 79
    0x115480c140b0f08194080c004044000b049203800d240070780c000426400c15401c440150400341e98400403070603108240c010001d80c0d000050740f84210b5816002d000f0b6282350010103010780d41400a400e5036603001030072268007004201034001078680d000d078080b00c0c0c064281d00d080d964280d50724201c00f24440c28601c9030600810440d01041442803020903c05080400140010b00c2d691a50301c0341d001d240c0100d141540c0400460080c071110050030403580ca0703040710401a44418500d41801c1110003400340d0b204d0705442d0100311014031021304c0030951550000e002d007001e625603100d50078a49441c0f48140c00c00101090005004607031203030001111480354003c00100b007851a200c50001c10400c0041c0402901988107000c48104240528042c10802c50508000541d03c0403102a030003c800b41e0794402d84409a49509004036500e01703010b09805440c0680081d85008420b21b49689840340c0c88000200003203a03044451800e41e50203140100800c3c00034447c1003061840c503000d980fa400d69208903044200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 737338965 1250 737337715 737337751
    0x71d090717070206090a0311070e010f08150402130213050406120b0604180f14010603081b060403091404020c060a0b09090a08190e03010c11070506031501200105090105 74
    0xb10016130307039204501000140c071625003142d505640f420b60210401080e4025500041034510b10b01e24414001e22900c3c280000c40e510b402006070401c0010481e640c101340040c030170440036840d000c010800f0301c4a54040140d070b0b5226a041030b0b240116507040140c1c840d0a010002a0910515900e80000f030701031007105005807107200410044400010052005503113056030000450540030104602d240181056080340d5078060002c1d0031516142c000300c51143c0d01040068103600e0380c0000600c3c20100c03100901807070038151405001c121080c820f08020b0802c0c121024501c0d210b9805680d140b40d000400c4030f00341e04140b00f80001804810034003d000f51602c00005680d50400500010070036048041e46141404403901000042a0454051705100c490716440b2074545007480341142d03980d0140e682d400102281560319042c110b082d4040e510421040c414880c1105090027011100c3c842401c00c00305040d9600250402d156400c05100c841b5480c0500b003008144040d00451b1040c4a44080741d140c6071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 737340215 1250 737338965 737338967
    0x40804170c03150a180203070b030408370509010909020c070803070c091116030807200604120320090102163b15150d2012071d09071707 60
    0x28503c0305c02943c15440000200003001c100d0b0700843c1c00502802c07a0710724004a01c041c5102c40000b00c20100b03080280000d4039084641041c40f1841c014070f0031714100c1d103088032940000340074800d180240081954002800c5544407030403c0800d004001801c2901d444d048036050040007108580700f00007a40303007003240944010b0116812500c00201010032403e40f1055514110f400940c0144100148141082c2140c04034a80e503c010100d045801d00420387c0d0b291600d080c1140c00004111003082c141090382c0300d0705440382d000f41c44c0300d4034102451041d2103111160040f407800d0307060505104009000c0c08089015120f02d210750888003200e1070940b81c0250b0302e00c580c1e0300c001d80c0c45024000020900303000c10380f4003031390554485d000c1d48000d01400f400c19140204803082e03401b000c1e08120071503030703540c1e40d084115006c80b5418450920100c40d5041250146102c0103500c0000c001c0810450b00321700c03281c14444071000750307501020007030028be81510389400044c01e45014946031002484500c03002400c89 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 737341465 1250 737340215 737340251
    0x102030403030203070f050c04180311190f0501110f07050d1701030204051806090106080708071a0a0504091404111207060c08090402181008040804170c03150a 70
    0x90398103074011460001740d0f45800030314400301c000c2242c02e40159000d02045a4076800b8141050080030400c5c100602c480c03501078050f05110107100445d40102c03907140700b040446c44104111075040451001070901500e0607038014015401c05443d0100b0206400e103502203003070701034185184181c2c2200d007030141c440341c01e03501000e151810200c402024801030005003000c0d0401900a42070b501c54103c180c1e681c030020b0b4100b6008580c002d220342e42d83e060070800d101c0204007900c0240400700190500c107080000c180009150006048254a800a020121103210f14226001004010707801c02c000301603030042006485050b80e090300d80d030010300b4081040d45444c0055200c40c00155004080452a28000b600d0004d0100300941d401801803059500307903240e40c00113085031084100003409102c111000c20480c4002403516008010000041100150040007104c0039920741b0200c1c0409040c0300c00100340303030004011a55426004481d0302e61034000d0002480340c040d0940c89428410a03103c1c080711008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 737342715 1250 737341465 737341469
    0x91a040f05060c1804020c01140a3905030421020a0624031103030403021c020306010b130504150503150702010614130b010c1a010e060d03080f060a090c1d01020304 72
    0xe003513132200e0000c02e1300c1e0650060100749050400400c00c4105a43c0328070080c1c42c01c68200320319548501d0040303402c6116100c00045280000c460915001ca070404000c045165a0019170902c44008045400d11000c0341e44101694601f0001c00000c03044604020344400054070129070711418180c0016460250f002e40150048007440b10f181380758079680704c000384c81c03440500c82d0760140001c01001c00583c40301e00d0f510000c0f02c0328003030007180c1003a184141454007105902003003800d0f4041c001d4410400d5400c012a0403a101183c01003483c0303602045000b004c41c019404586e0612504500d100150200700e5542d1003504076400070000d142c2c1d5500d41011280841c40d080c1c0d40041120b0b038000c030701c400b182d104103a40780b07040c9891081d0b206195200211100380317031604c04402d19550010000c800e0100b0710a940144207403002880c1101035500035009800c09407200c2c19008a100010f80144c8800300aa8000c0c220480c05012030012940050700794444080c40020800703a12104500a50002044600b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 737343965 1250 737342715 737342737
    0x30403050c1b010c0f03090807080f07050f010816030b06071103011406130e01021b03030f0109091505040302121306082412010908191e050d091a040f05060c 69
    0x2800c0c04d030b0f5503200500c4c42d0541d02102409040030010404410410428010702107040003040e080c107200480d140341002c964801449080599500046a43d00590312908440c2d0820355101908002c403013600942420712082d40c00c8007000c1454002d02401c145140c0034502d00f50020071037441140c0c10291130f40001c880d910b4102c1c0d585a41c0b43d043c00200c1d4020502c880703541000500308514080b80c0324503504648625802c1e680003000740b24000a06000e2a801800042c100b008005020f6440400c1141d1003c1c8007890360b40d0b100300007001d260080c4604001001040e88942c0d4440c1035a44000001030907000c2c95002407c0341c8002104d42d100d40703410000c029103095090032281c00007010070410504808ca072402c55500c921400e8005504503000e03004d0748000b0000c030342040b810035034003d0840100031a60740001c0c807040c50303141403260410700301d0707140118a07074010603e0106810042612081016100032181201c0208028840740c03070300d0140c80521400548910352182584984c1c280034601c0010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 737345215 1250 737343965 737343977
    0x2a040b0a150f0e0a150207060c1707020f18070f11060406150306021804051e220f0602040305250b0a110d020703060c090303020604060207020f06030403050c1b01 71
    0x1060705008841003016038265103440803208100b500407410500d01c0fa406806084080d01d208030201d501440301d20050030580c13410860344211500d4a0007035141c0a4443c07250100c0004100096450343c0100101240001c1c00300e02c445112211390544044080304c0c0e000c0000e420000041100f480380c07080d50160f003072440007032181d45c032107844a500130440c08080030b0580502880001c00156a40090158080e0071981209005060028070040d1440203000d00003d5100030340c2080841c40c4480900d401180c0d21050004608100801406070600d10001a08070090b4003010010080340b80c00420503a4400c0c8250368508103003502400c068240c201107120400b00021081c42400d0000c2d010b442c0e458484c1c6051020007040500c1603041100150300e03c001a003042d6014014001280102c2880c1052407420700d280d1495074500035152140900020042600092050259030301c61200f95040c0c04008c200c2590fa045c60f2801401540c080b8814482d14001c54140e025103440e4540d241e0900c1d441a12a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 737346465 1250 737345215 737345249
    0x260106150c06051e150a0e0c0d11270a050a081e16030b0930030405010b0907051210031509260d1a030c122a040b0a 51
    0x404003604004103c0740203800e084d040c404220f14140d5005000c0d107000003408261301c94040901825403550f8101c88082c5440034140082034003d00d0480b06600c0d4030403000982c105071304502c0703031781440f40d0b410b0b40c01001098003180d01d22240440141e000200200c80f4040e60315686c606200c404001403041032059040380c08c8a05890000c01c26104401c85150151001c10a040c80c048025880d250015607000268000300180c1040400100ba129040c14028669050300c0f01030036070030903080682000e451b0001001003010441c3c02d402080f800d03140103110318014a00400004c085070082c407507000c003102040c004580c1c4464580e016200b0360b83c20040c50b0000c50307200380c40c01002d4071058204482d080042980b44541e0a181d1440701580000301410640c0c1e140082542c0081d694562100305c661400d0b070712681160f507000100700701c200074256075403031406131000741d4541403911444c0804001d41c2030301d015410900000322960800c800817203040010318451414002c195451b030090f200d42c0182c507424 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 737347715 1250 737346465 737346473
    0x90b0105040315090602030a020301210528060c2c0a0308030c0d1a040f0b030706080c04090501060806010f0203030417031803070605150d05030301051306260106150c 73
    0x1281d03034640f56081c020034404201d680d6481244d100701c9074001100c1d03000c8014050f4201d61010303908200d001c003410040c00006078031180d4403041d900007640d000120340c1700f000054140821072121602d4108800f0001c0740d91440c0d000e04032456425100141d42081d100c90000d848482c19030120070500503082610700c50440d625071a0300e52010784504544801400605072101c11400b40040d2140301c646d1104114400c2d00602094031203520f4400e04550801100921985001403600100c40c030928001541c1d44503540c9142003881240c01c4105558203203000814201e8000c000280910002c3c1d030f5034603a816500c9812070700ca0000f0744009055100850082e2280301c155009550010303021141031001c002d58440d19465548030180490300e95443ea000c100b030340c00e000e4110340403601d8191000c0211195590341c40d82c03244030501030351344180f00500072214140400d078491000340c011040700120210340e0482e01c2c0c140c0f00503540701c0301f0b0350343c20804041419a84541c18602101013a15038040c400b8261b81d17 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 737348965 1250 737347715 737347733
    0x50909120306061b0f0105010f14060901030902100224041211030c010905011d030c03040e100f17160b09012105100f0e0105010c1104090503030109060f090b01050403 73
    0x2c031036840751090018081401d8003130104102480c95100400e5a0050340d41c0250079954140c0c010100d4150f4807204110740e101210b090301601030202c902913514020b0314011390090290700c102a4009604040d0b00d000c85400240d124560040120301007007103c1e00d40145109401d080300c0c010042c0d240070340c0034011f0340e026401080301100401d05490618000c40322490840b00c00310800c2e107080e13444007a001c540010a10003000c03020004005140382004880c2c50070b61340d1080740300c0c0807880c00d28040083c00414030340c02c412000d80b03500d801010036507a840101c079504a075150070200050098104201f600205261000201d902c7c17030740207600b40350300c100c01500c8400d600c00c05030003003a040e080d6081c41e940c1d0351300c1424496007541c1d030000324050505409a0000c20305822140311024000014801d81ea01301c17101120b03840c1d100101d1999610740402050240040841c000c1c1a448007000110310b0800fa50000025200700c5201030b10030340d46d5051980182e0b903940d4205404104c0402c818801f1540c0c1403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 737350215 1250 737348965 737348971
    0x708040e0a0b1f121e0e010902010503011505160803070f03050f0601050a030905060109150b03010506070818030a050d0e010e180c160c06030b012609011103090102130509091203 78
    0x1013002807150303207003200d03103010b03105050f1504800b040f0401e900070203e91144070b4407440d01c02c43d100800c072a40e216130011b07000c0c0c40f040c00f40c40082c50030701c0300e4031040a00c103901f152250404000071002c0354059182a1110390000d851030350215400b404100c0c40203100e48200d07440341c0c000c4a80da8440d51a0b10300151640e52001013804201343e101c0e5020404207000f0041c150090904690005d080d58201074800b80140050704a2081c030901000100181c1e81d900080c0d9541ca508000c6171950354031030b030700c0b942c2404107a01d40d540d0305030054a483d2402e01002140c80e03001d1407002d484101003030f03206500441e510243c6900c11a880740c110304400807119103510410b503104000882c142e20b00a1014428102e40080c482d00329418080f03104280f103025410702030400319070402c0c00c00682000c4004410003c2c03c3c7e50940c3c122031548074000041611800b50400360490641d508031035500d00381070700214040d600603000d0122603d40c00c43e0000e9182440208030348210910310203400014a50491800e6552000e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 737351465 1250 737350215 737350217
    0x2090c0705190b0601111b012606040f02090a1701090519050106090209090a090c050618040b2e030605120303071709210f0708040e0a0b1f 61
    0x34000a000201c1c20405024201c1c8002c00c00e0744100c00c00c0c81e03d50040c2e030004000c14100401071401c0000042d000500c0d02d40002c2075104040e01d2003200303004032041011000840305084112150000e08444000f1080c050300040d50b00703220544005142c0f20a13032095003010303a00315002d000100022017102060100d22041c0500104a980140c3c603010301e040c4050400022154001c0b80720009c200091140301c0040c00d4a20044d4140611030000a2002c4c2d0002c01d203000303040d02c0d444044100010761038000c0281a00820307840c0c03640101d00c0745030709010a0106a80c01280707008601001403500040c28a503080b10240203494480418030200c1c0f50f9030030b1603485001e25459140214807130ba240092070241140e403100558a0740380c00000100451081c0d000304444560f440d05201c40a070002c160284800d100860080b814580e01d038000f1200e11074804d90882c5044041130a030104803244000300b04543d51054050243c1d20f035410702400300e642d141c012580c0300e00e00074400754140c03000c1ca100792003010751 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 737352715 1250 737351465 737351467
    0x80c041208120f01030308070e120115051509060f0c07080703030e0f100509060a050d0903050a0f051309050603191101090f08060106051303050d03020a08010e060d02090c 75
    0x10300c0c0d803000c40c0c503519560119299140842c201c0184031421425581c003032010748000001c2e501d191009480402e000d014001003003503202801c0b400381c81c0e000300700805070101402000280c603a030000003401c2a540c021a0302c43d80c02285801c00c1d600ba040250b40040000606041c90046180c0e505622980007030740d101082d02501c0d400042c1c0100501844004502035101c9034582d402200c100f051700c40629000d14400d14503030040700c42859104094503111102079680c5c070b82d00c6402010640c4c3e103001e0544c0200032203041401400401d40d006000d014480c00c40d0312500d4810f00200001c3d10303075014907541e60f1040d4070342803001c00011020b500100d40211015050301c2540560200c8100190707008802643c10b04414010a2055640036510340020a0301e0150091180d04043e140b607101d102c188210002c110005c20014890b0140c000c1314001154004201c0e4403003404045c0113030194001600d1140404c0b08c4000025039a140064402d1003100b0007851811840042c5d030800c0207001e4042c0850f000088 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 737353965 1250 737352715 737352719
    0x31a10030b010803031b1c0e030403020306101508090309040f0f0207030e1002241b04030f03031d1f1104030501050609070203090306130305120c03070201051006050a080c04 76
    0x500d208240a4104030f03000d141d583c68000340303c0c4514000700c021704405250800c40301d00356402e040c4551280898510010038403c1400e00000d145005640001e541406a04140f215105030700103170000301e41005e6014100c940000c80c0030350b0500c1048400c030070290030411001c03001d86443e9000860043d4407441c001119021505040e04136004120120003040c0b403c41020300c20320380b40203100080f0049200030000c001c1c0040885030380d44c2412020250f0725200401240d10038103188164032202115940841c0c13125a00e041c056032a220254041c2c0100b46800010b0303402d064031411400c001e0309440e00600005402c844038145068204031034081a0f651200c14420484c2e000c00104000d6008400100e40c50812008001c0c5004000c0c060806560003008100030b0794801058007548a80c0228100c200e4110710b050030f83d2580324451841034000444001c0040d13500300c5202660243d0712503802080b9559a40d0b4000786c103c00f141c00b56174086481440a041c107544160301c029441100729108505040e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 737355215 1250 737353965 737353973
    0x10e0a1e0818030c19050112090f0f0c240f11030301061701090204050d0f061803110f0604030242090d180e1e090f1204031a1003 57
    0x2401020203001110399501018456180412013100264002c460203600e00166142a0440c00728511505052144108080e00159150740c0804079090b00314007500c2441c00140340005a24050182c00c95101c605803001103010340307420a01e002000c03d1100c00c1001c01c0c02c02c0505031001d2940c0f41e0128104880c0300d0f1900000c07203050025600030010354071940d998050003009044040016005a1040740c414442080380d90b8070003601c0d80000e80c00c90781d038564000c490f0411802900070203400702c0080c8600e0007464209a4010490341403120140140c40d02c108810406c161a40002d4501400603400800701840000c00d030030075017646c940f003011080c4940d818114010f0070780c01c004c1440b68200c00c0b40010491140000d000c141d0302840c051416841c8a034604508003808070150188000520500300016011549100c505014046904c140e052615008685540d140e1808030341c03400038024002c4c40d028042d2004148d40540e0781c40207081c0d0303c444200044080c80000100f484160380050f440c0003001c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 737356465 1250 737355215 737355217
    0x30403110f0a0308031008010e032a0123160816170f0106020c0907050a030c0e12010506030f030c031b0717030904051b0711060d150302040509010e0a1e08 68
    0x8520410b070704e580380c1c0b40411440c401c2c00f802e80e100d80c1e004e03410200c43c106881004400c035045d0802e002d468841c0d2101d114101e07019880310f6013030718929610b8100e141041ea4401c00301c592019088403c41881a03880d105442d0b00b00101c0f04084020507484004208020302c0b40030040c0000120345000700741d00c48031000005040c03205803100340001060070014080594144040b002c65082a5800c55079810301900040c898810100100c04050741c4410700f82d081c0d44102642e19814000a203100e8890307502c071900b24000c0000790382c500c0c42407180858004403130f00e012058a0380c044680e0051400c00520035100444d18620076011000c1d0301030048040741c0002c290a182980e244c4c0c0c0001903440d44868014001101d00c0a403001c1042030301c40380601002d0008204807240542d00100d40c9016150910201d0098065480010101d504045052004075a80821001100d0003218140516280c00703882c07a080326200303c0c3e6890b241c0c00641c500301c04611540300080382c8403603801c0c03044004507080c0c40d03064132 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 737357715 1250 737356465 737356469
    0x503191116021e0303030a02030a0209040207060c080105030c0109050d0510020a0804060b091315060312020c04060b070515090a051c022103150d02090405210c030403110f0a 76
    0x2000c10700403811041d414040c800700c203014620341059040c0aa210b002031380d01e0100400c0307410351a4000000580a198a405840c50003001420540d00c80e141403030106e0103060b1010800d40081e07031401c0006140c0c030300018069841d9006843d1502410300300000d03c05003500300a0b040c2c48611508039541c5010b0302d607200514180c400ea41d601061800c0034500b1a0540e40044000b900c01e080400c01d101c3d03d10040c0b900c0c01c48213035000001d5418a00001c00344005005140e00182c40a40784032040d0f003541c0c2d0046000241c080713044600304905511480110f9030783c00f80039030244c40f651014940d03203160003041f031300680c010000c46e00301c8220b8602640c80500d0a00c0c0e000c0508041d810311070b108455941c04101c10141010401007a09880743c41c10043c980d0b501006000300300c1c4030155500001d02c0d03100c1c0790110309480e0300079295510380e103018140386540f09020309030207062410703050f582481310581005a80d0702c41c0300e1300c2c0650310302482c540360b02041400901c1625407100b0308030001411039440c0f10407400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 737358965 1250 737357715 737357737
    0xd0e0919021c020705070803040e07030222030528050706030c023d0209030615010504120c050a080d0527120d020f010917030c1b030705010f06050105031911 69
    0x42d64a500d8501103080491b1548540c00b2580107000900071981080d0b1241c1d0301c4051850016140d0320307600302d400800c0401100030b265442d03000b28013205002e404246c1044804980030348c541da06080443d4603e00d2114040044c02c2508110b00a0200750322130f030003103080100c0c40e104a4540009880e2010f062684804803010b600604007016503d071240710f8844081060001d00c00c6080c1403106000c82d881e14801080305143c0e0740c0d03000903103103260b000d401650068000512030303004252080c500080194154024240b00c1c1d20541e000041c2c89034006450085c11289585880c10303c1000e03c1303c0d000300f244080c00005ea4024420000d40b072511242e81308402c141382c41008201d809424207010341022100320702030f0040d074181070002d004604118040440100001c50181d560343d1450310843d100e01440100d00b14000d90305a01954000001002d401107900950081200001c0240c50301c007202c7d600c0c03051318045101400010035600c1c0395a2030421440c904000030032908207000c4102c00b9a841190396039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 737360215 1250 737358965 737358967
    0x507180e0c190e01081506071410090303051803190302180d0501021e04150804021314100506120705130b040f06030b040e0a020904030507051606020d0e0919021c02 72
    0xc3c00c3e980d020080c5500a000425521580d09400c0003140117882901c078003402c0620003184904410b08204450007000b44090301c108422402c52030300038080c2030181d610301100c4d40140409000d0a00200c200cac0c05502051144022000c01c00d0400d0b40a900050319651214800f681540020b4482007400c07242148107100040c1e40328900b501000807400076140003440110240000d00040710f072918148440406c500300300c03107165981e00c0098032424079041100040b50809003c024610041034460740079a107010404242580c0f10014002e290103410b81078594036035030001190400d40170303070020900500072407486100c441c2c81d03601c2d003221030344581e00500c440c0490300d1080080542c1880b0b0801c0386101140c0601c20f09280c2030410380e03142c0391030700044d105640c402e021908150040085400301580320060740d00c17481000113501c01d0601d05108900c0540038004011040034480d101c05c0310941001428004182c0b50040c8040003a25060072024160703900304400301a0344892203403060120024003002d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 737361465 1250 737360215 737360237
    0x203060105101b0f1209290405042c0c10080906060d0f020d0503031006050f0306040c05040905190e01290105280905031501030b150d03020a0203010507180e0c19 71
    0x50501d48100c47c84440300300c4141030521103404034421102110012500813980400704441c0403890500420515541c1d480024459418480403501181d450403c0310401c48225040b003003903401500440303001501c3e80103040092020b1400c9500e00711024060081012000011744c00310351001c0c0c10080c1501c1c1a840401000403412013a0240c1004d0017103407405a04042503507518460320b000c081c210038403498480d10349a40c134500c41ca04ad54000d00346420306020341c1c204a12403104160790040b0b00d015180c1083c407851f01c142014015108080c10f65140407400b003480d0481440320740b81c800c100e0750402208200c0f61104150416400344d96003502074820009409400300a4001c4140e544924080d4005815103500b0000e40781003d030440707400884031111680d61905040c00310301898142d0b90702c01c1c40e80134220306143d8005130103071107244203400800041d02c0f2000180d401500744c81116405401e846020b21810302801d0a06400134002c0c2c3d40d580c1070030414203060840c008030a01c1d11001506e48400307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 737362715 1250 737361465 737361479
    0x30614010806060a03170d1b11100902090402040f0f0e010b090708040308010e0901180609020f0411090d0f021f0f0f090501050915160203060105101b0f1209 69
    0x70380b500300d801203402d650038900d995910106d124120090074001c1d90701041e00540d060741030308004007081400b15405a151150b07400549105580c1080e5240d0b03120300010740e025081c035841402101500104000156034230750342000043c2660010b030400b043d4030344402d40f25186090040260991030b1130f00215000c1e40d8002401003601c0001e01041c200030045041c0000b20741c01884480c1034400100002d080e40d50342c0305805024180710750040401442c82c0003144203004641d40001c400d14030032200781d8180341000c01000305032020000b4171041024100070140340d525288451b18602803013034002d04402001034000a4220041c2c040c1710314170099528004185030b912510000c1d4504580c00c004d503400d0f0012030000d040001d20b0041905100c00014400d14540e541030b040841c8500c00e607543c641d540121700c1155405210013004a00900ca18000032070580742c41a02c0744103040c9142d8508914505000000742c000489e0344040d203000d000c1002c90030100d85da0954120340c01500d034a801811030301d1300702 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 737363965 1250 737362715 737362723
    0x302030d0207140f061803100612200603041407050604031133091201050a020304122606030f070b0a09141309080d0c020102091e0d0605070513170705060f031f0306140108 75
    0x20380d03203000501043e42500190733151410b0365005900b04c0740c0560303620401c1401a14051a035000640d1220008c038001041054518039102015030039541c4680c0340e0a200c0c0400c0820345191510158001d02000303407109000c0e11409418945c100510003090000c05001c0903007160740076103c20038070036000003c1005100454403a0301420b4075604e0079170301c002c0c1600c601846a000000c0c141400c1106000401c1ca41e65042007900509807c403420754481907580c24400c07034503a0040c409040855508400095007160354a002a0201c60103018503e1601b6181e04820041c0381d06601250081810b00ca020350580d0144202c00080710641c0005a07140c01a40401030100200c0b1b2461034011842e007000c0981c0e450b8030039115510350b8400008605510703085001d6503540640f2146250a03600108000385502040c0b000d0705001c2c03498025105a9912002402070070b2281c848d080110706001c202242804524614042d488440b00702e401d5040360700c0c1d5440c00150740200744242c40c0d0481000041c030100c0e100388 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 737365215 1250 737363965 737363993
    0x1b0602160221030d0c0c1401051501111009050708060f04021c050d0e0a1208040f08010606021e01021c150e06010f11070302030d0207140f061803100612 67
    0x100da09040504559005580c031311926460b10102c1c0e0b04c5034090120b060050001c07507502ca61001c0d010ba040c10403c503516000380800c030361480f61504410a020311650140290380134502094016043ea20708000c0180302a100c0c11604a501e40b14410300050744030814803800e406404088860302090400c0d00401030340300c06501c2a00d16502c81001d0000004000203416040f442c40e07800c01c040324903643c4d80000c010801e80d5020011741d515244508042110041c024025505240c039005030468803040024200c81d202c0c0541c10150303220014103c040000100c0e1403541d8066a00054a0224100c000803040d50352071000030310726600c0301103010000d20b02094440c00f42020744150180f80c40d0600c0000c01400401802c2004c2c048072040c52800404203003c030340c002d0f40c1c014044070407415441e04002e5640c0f000d0300c1030046008005804800600c0c142020000805004241d10705118091025210500c2c180304403e03030500c95148810072a40700340c041c400060000300b1221010000398104403030364414031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 737366465 1250 737365215 737365249
    0x903011e0c02152202040f020d0f0204030507171002362209170306030d090605090103270507050307121a040f060203042d020a061b06021602 62
    0x10895010f0030220310002ea000c0004001614a4122a4402c10007207204180c0170307401c1404e040c280e80b5150b0380c9400030542c2c20180041001601008200c1030128001c901009106810005080203101041d00f134a441c000152000d0b1102551581e030303000200e03030000002d00c0051030000702c20103160700780d6500642c82e01f4a50a108060105200000700502101c0448040980503030441003903440503a03010414040e403044d080c60512141d04180460360f00201d2f02c132440391186100c81c10715035200f1804c070000c030340107601c8a50501c00f1746801035001c3d0006160802c10b00c00582018541c582c47c180308020b1003070003403010380006420b1070180340c20482c0c03a42114580c0c0c00704902110004482c0c18001600144401c071f00241e81d2564580b040d01c505103d0ba0240150b40040300744020b200100321412809800340c4121042d20501c070a100d4001c0300c4129019500c10184602000740a0080c40e00d04503aa41d0210201641c000f142d030342c501240c2120302c04d0031400c041d840c0303d0021402c106105c04062400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 737367715 1250 737366465 737366473
    0x702011b020303091c2c0405100e01151b03090317090d060e210c1c21061806030605010602030715020717160b0c16030309080903011e0c02 61
    0x1c03030b0740055510031400d094800b94420341d00d11128158406d10078032020510b804005d8106107144040100455100301240380301e5807806012880103039000020a044400f500411b01103030b8600714518801b1b0490020b0081484801140c045201c54141d1481400034400c1c0c0724001d80c0d03400c60424020b0749501c1c0c1c8815410b40000c21a44006559202c0003a001d16800400032a182d02d0020016042040860044098040b5500346e0400000200301809811014004950307082031403c0401101c00032945941010030950310312050021107558210324400c0c00c070800803c1c00c82d51403007515010010302400168440e0b4611040c01000214000c40e401440705200a5081c40f520b5104ca228011814070301d0303580c4039400280c2c4c100b00300b4810f11012281c0e0751407410b15140c091301c00000640f2440a001141d0742c403031001c000f900311110013043e00c158802d80350803144292150356090b070040286243c203852501c0144207540256a003401030700400980c082c0310010248007155100140c0f15030204c440e066401c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 737368965 1250 737367715 737367721
    0xa02030108121308060f04050c03070605030406180b090f07120b07082a0712030c0509130e030d06061b03080a1107150501061805090402150c060702011b020303 70
    0x5000459020450150500a50f91100c005078035103201620762001c1da0500585080013000b1001550a0703100d40d00030810740f60307040f04c1c074010591906403d0041101040c0c0c10720100c0c02195040d480b00040f1603e000010071003401545a544104504076815000c07907220400801c10343c41d0520241d80146090b0980c000c00201320b40d00ca0755541c0c0d0040c01071040201e144009038880d4101c00e04418441050140d40c3c410380640d06a60183e64003480b0240c030f01e41c07220003100236072a100e44201d640004860b0784d014101030700101044501d0f88034180b41ca0800c2e41b14a114803103918140000e0944000040e80021080d01c2c001019201400780c5c6a0061101484c5000710b0210b1b8008000b01d43c884103034070340011030001d046022516400303154009000002c40621980d0384020341d500ca036042c0d03079103074441c0c0207003003002e0010000018841c001d035500f2080701808100103003800c4084800c40d40c24220081e040c111250f50551501c034046401740c006070744030851200c062150203040c500546003440998518a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 737370215 1250 737368965 737368979
    0x3081b060c0a0305040312090807060c020d270305072603030106050d02160b090604140a03051e1209010b011706030307022404060924140f1902030d050a020301 70
    0x1008940c0d42c001071640340c1d8006401c1600c00d05521106080c405001c00080380c1354202410340d6000800c08440440c070307054450140b00e0002070800c11103110f66503907103840f141e00c210b4010303a0100f0381c00c0e03801d10008441010001500074440d800142410b41da48041e0368030303100112800441da130244022140c00c104011701c4260740c003408030754002101040250ba9861420321100d5800a020006003409803107070305002c855500030408501543c05420b200004c101100400c42d2100d160352401000305104001d2101710310140d05044401528420f000d40c00d08202c55450303803032200304540915142e5503400700303445070350703040700c9145004030f0821400010303481d2040c0482e07901e01c03980c400688030381d04524010003141084002c0c0c5950010000c25a62100d6a41d10f024041c4212401403281e0020a2100401c02c0da409801141a002c2c1c9a6640100c5501c80c4031403044d194000c0c4102e08040c041004003e80c410400071050a0311110f0358019940c1d254101081c00442e00e000e45007145007401000100840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 737371465 1250 737370215 737370217
    0x1305010c0b010e0c1603050a030b030f100911210f070f090f0e0d0f0905060702091b130b0406030b09010302030715020f010504050c010f0203130e13020a03081b060c 72
    0x1550320307500480c003c1d07200d4103064150390003403a10b040000c0810448420070950f0041c00b910f0b52145070788040c003c2042000403d40c403640d6180c100a0158040fa40c20000c190b4180c00c241d03e618042c00031f01c00306042007401b00e620b84621b890072210070302002120070030450f410071807100701a2014001e0041c540c2480f0020060214910030340100e40e4803521190398581c0e441e40070094950100c41141c1d8030302c2071040040c1444034a008400045000c1c1c0c0300c00038007420960211401d581d8014640c1580e070b5070b80c944d100c16846004e640c00d2800c40040c00880c0c020001c00301a00f01402c5a26085130319540341c8100182500d07034141d612409020390314010001601c000410388261400c1286404804d613010104a10b054010651290780c0c0d824601440f00b40000825400e50303600c8281d0750000c0e000c955103410b036686e10074200706031000714010074108400c412000845402c0b540a00444454004a40010303494140640066400d840000740b500c1040345050f654240d4080510081c200900d00700580b176080e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 737372715 1250 737371465 737371469
    0xf15100c020411120f2404020d0501030c1805010308160c120b0414010c170a021c0c021e101112070207080c0d05030306040213031e11010908061612111305010c0b01 72
    0x1640f40039006c640e20968494060b2601220b0b200d10820041d0394900701401c0c0355134140310300c0364041c0303420201d40c000500302e0190314182c9030045000c0389010f1400c8a0040c000d1400582500c159855003c0840d1884080440300d903098041c0141d41d81500301400e250240c85c18510f126001613152003000d6203c250000f0f980100443c5000c3d03045042d50701c61038400068071072076041c0c41e0307003540420090026244544c00709101e61401e60841d00c200f00441101d404e07400c5207825421907940035140c041d00c51003150300021401c1a02d001c80d41c0c10100343c4919000c03410410b030358203009030b000070005004a4004106902d1032103401c552201600d55583c840f182c59100140005020355000150301070f400381c010480070300469001c007014207222006642c0e540103041c5c08208448000da41482d03030140c2e6214405050566240c500036140039243c1c0003001626116202801090081081d000303418602140714000000442c468003660300d80c0e14001c403400b005015040f06050164044504010400600f60181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 737373965 1250 737372715 737372761
    0xf020a080a050606361f0801021b1618110d02070b070f090e06030705100207031b0b0d09060914071404060803040e07021516080f15100c020411120f 65
    0x421b8403000d4290750061007102046c8102e0001503000103034803805500030f02c1c0c080b01b0719488928521340c00c100d55480f100c2c91070307001180c28260b007000e001c4400c250305c1c3c80d01c0700400c02c40d0008000240402100c15500704002aaa801c0e5010402c1814845001c00c0d040d030003040c41c80c1c11124141c2211001c0d040390f01d82c1c040c16140c40c00348000102c5d5600e0030003078030025010003485030314940301000c4001d50f40d402c140001c075080180b011050000910561842c401e969000700d50900302429416640e00600d9000700644026883c0c0c20328601056000020ba0900c03c004c00103002c019060000c1c000780001712940503030040c0d140c2501007102403070100640d03060312031f0143e48000546481c0380481c40d000710344003110940a0240c00b842100c100210300c104900c201601d804c1056501c034204801c3c04a4201c803e5803600c800c048d81e142c21817802c40c0503480d51005500f05400440c9440d00030804803590b0a03a1842d00060005091000c44010034045511044510b6031054618100040c0ca0242203071b001101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 737375215 1250 737373965 737374069
    0x7030b06091e24181b0c0a20130c0f1b03030b0607050d020102180303270111030c06010801180519080c0607031b0513030f020a080a050606 61
    0x9204503140302003118084802003200d04c0d000c004001c4a225410180c070314a56809500c01e40808082c6190300360303902c0c411100c000d003880c080c807038984081a80d0303a03035801841d10000010440031503031400307200b94086511031000260742084c0e82020b0040351441c1480790600401a54034100d1007290440c0e12400c5030700d03103030200d155048100883c11500035040020010b000b0803440d4078605078158007401751650703811058402c44803200d041c542c40e480341101e01100188110318154035030103180d45020f500744062500b040081024201136003590811884100550080001001052400d0085800b8104ca140c044134075189540d90300341c1d6802c10b0035095410000c4840d901000d20003c0415181c408548030162100d514000d0001001400c0500303007100d02c2080c660203049100d20034019145021124004a00300d1410340d21910901403c00004a070704c00c100d0f18000c1790a9006201c501142481303000208118103140c0d0801c603100180d074606a01a10f5881100d4138060002d01c058602d240704d0f90001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 737376465 1250 737375215 737375251
    0x5041103041103010615020102120f01180b0102030c0102040f080105250f140c060f0c0f0414040f02070c091a09060111070816030c0e15130e07030b06091e 68
    0x2c00e000d4036480c0c1c080013506d544108043c1401d40c064004142c002e21035007074800c0d1991411840c540300082070041d5002584020782d50035030f0900503800120103920500499051107901d0b040c1c01d013a6030240c0c202c0305a1845d00c03c000c0040940174060541c002d0151200140c03064203550281e6500300100e0040810424410b07c696162402501d1525403018408240c0c0d40d101c0302c5003a00c9941c0d8600362004c81c0911440780c00145d0b035503050750548503001d1241c018189000d22349501e1214020600c80020343c0b2960301c80144049a0f02440207180c040c1c4a4901c0010041c64006a1411207800401d903174252101c9000d031a00782c0e0f50341800d090744040d09003081d0a070607105003011498800303550440f0140d880307114080607414541000c020204c03440f509002031503988900f00391f07801d0700e005e4801c1441d02ca0140e00507120740c0340c00100da40c8d03805e101c50b000180701c50f41c404500d0714100460384252101e4180310207110030b6040c0403240c182d010000c031200b000c03e007001c030112103000d00c0c000f841017903400303164462 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 737377715 1250 737376465 737376469
    0xc07030e0d1e0803010503190c1205030c0604062f0715020702030706030218120a121e0504090b04090209060f19140307080f0303191b030e07050411030411 68
    0x82d0340c0c0d070070701c0700340d48502018010b25000b032440e03100f07001c0c0310300c688a030b141440c4140305003807004044584e01c101d940b020380380b40c80d05031280d002c1400812125800248503004c01d4000803c0032601ca0750007040045070154100c02ea40322070203920b004400300c00c01e0649c06098040c2d200002c94000c1c0e984034003051340700e02c4c403030504a00901030400020b5241c0501580004c8566160f00907040340000000e501030190b015004011424940e26840314050b005600b16401241c183c00300c0302d1000341d29003030540002d0003030b42c01240400405403031075000c10400708050085000d031303115500e1183d4090300c0801a101003500045c0076107000070501c911905009034028a5500c4080580c4019525503410140c07032611136400711081d120348140c00f80640319461000600300710000d4000c0760350b01001c01451079922410801002e041c0107d6034084107946901d210800410f400c0b4608080507800d94002803021300d0195403a04100f0720341c0c80035210b241400e01500ca60205c8004803600142e0103980f4003010740207200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 737378965 1250 737377715 737377733
    0xc020301090c030c0603090c090c2a111012090303060504020f09040e0307120c0f1202161a0f0d11031f080307210306210b0c07030e0d 59
    0xa40650070581ca070710070404601e2414080d01c1c41003003004034143e111502202100c1e000a4003500c0032410800810040d4031650007002815518604000b5002005035a292049004441401c5098620700d41d4003e0040c441b1480120100488900c220500c4801d001061410719240b145540c95441003440101400307680910000c11020300159182c44605030b1522180c0c1100c0f461900590402c06100700d000c0002c4100c585041d031001200c08005002d80b4110381906000c0c1d02140c020004110130300110b100c9228180d009038140c0e000305401d01c8103559080401950303074800641600d200100d070202110680a555041c892005080c0d02c403030400c81590058a05049604800301d4000184808405048039045c0e04481d920803980500d036981000507528421540003604095040021002c0e030b4012003200e80344020185404565140c851404901e1080b0340384001c0039449200c4a0342041004940441c2d50240c41054524242181c4d914058000000b201070248a00d003030140050401050071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 737380215 1250 737378965 737378987
    0x2090108031803010218012007141905010519050904020d0f1407090b0901030f0c030c0f080705030c030a0902030d08100519050409080d06080a02040e030307140a0c1407090b060a020d0f 81
    0x8d0700b02c42c1125554a900306e100d60f41c44030361034000d4120300d0b01400700b006280b50000456a040e5100761901007070084030103503491102540010002c0c1000101e019070340b1800a00740c020484034000840c0340c04402e005007203803984212a011110500c00b04040d003500b00c00f010046a8620281599075040040124002d060704d40001032101d1030b0a5041082d560305600003e10180603441e50043c081c0400b01c10b07161800211241000500c0400002c1c1ca1310f8840c002a60b08901500c40110705102c2c0c036800242000341d851000d80c00905c6407010010007130000b071401c4008282c196030b003076a40c86650301083c1c104105030007034038010740e04e40c045c990801c0b9a020490302d881906103820041c0c50384466241d0744505032880181e204a0501c3c1c840c020414010080741d02800c1e854980008491170507070f14500300e81103e01410244400c88c07000344040b9904810615550400901170f008240c21b01040f44111013103403c5d1103006110521070408a0354000448511468043c2480d41c40d1880e4940d084411484003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 737381465 1250 737380215 737380277
    0x80f06030d11122a0708100902151c180309050603090a0c030f0b0f0114010f180612050f130f0c050a180c1404051201090209010803180301021801 64
    0x80c0000c040115540b43c40004e00c89402030442003241a140c907680d0b01010b0055009030340011541c40d040c0d10701903014148d0390344090200304016415030114152a0800d0300740311070002d1011a41401b0b1102c80c03180362101c0400c598014000286510024182100e602a250246500002194100070100310100303181c1c2d440b580740c11403103031645000c3c0841440d4001c02c407015807044011850f00c07400400c0c900d050341c0c078880c6019029040c542c011601e030a149000d0906000710028200301d9490009008009003c240d140c440303020400d0007451080712001440d2070748103000d030414817030b00c0400001c2c40c404180e00300b060303004c002007541403840e02d01d0841da004503440015000d000964124250581a480f8081c0c0070411038810060b6040d501c4004003501189001001c020900441c81c005110740d004106100c000038a41c030403907000c00c440c04020f0300060b01d66800031680807001003011168a82c20305041d80298100f0160000e50075156045030429030500120b0300e502c0c82d0400784052082c03555261 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 737382715 1250 737381465 737381467
    0x3040c08060405031b0615220f0902011103030c070f060e010501150f0201050402060301170102090607061401230f030c09070f030605030616030b060f04030b07080f06030d1112 77
    0xb0614009903640e00190091340b00300912000d052401501007400ca01c031341c0500d0842c04004a159040003c906040360b048405290840c54280d8031021603c6140c180603881c800019507028940000741480d00c640d000707481190b1041040080001c41d410030b443d40306a0000c00e11010301c3d01c516084000d0022040c0e24000e562910000182c41103040581c101703165501e031904541042d03503200481c01d0301c20444000c0e4014400b00010099400e000d94544140400b1000050410400300e00240c0346511601054407859100d4290955040d091061680103003080c800e040907001d2031202044030b8403031038158140300741c9021035990869101404046c44a0200800c80c0ca00e5241c40c9101400b111290b03c207090005e0300d00718012509040004450f4040c00106c20152805000e03c00304601604e070729090036401400c140301d10b01d00c1c1380d02207003c0c2c00a5403268200240b01d140c0f040c0020301a0390001c0c1075525061401040c090103842c0814211b15240180c40c046400305001c0e4001460100803075007588800700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 737383965 1250 737382715 737382721
    0xf07021807020a031115070e030a0605010b0a020d090f0603150504050403120f06050f060702120706020f0115060e090a0b0a030b0910050906131a040b09010e0102040b040b03040c0806 80
    0x10340401c0d660050340c1300341c66401203818007152460b510200e0198040b14402d000010a203140d000c0c00e0981d1070a54002c0031610491065514042982c0080c1d110904a2402086c0210100d8062111044038482440c104000519026a060840e5214407404060660303481c251000c00c4602030600c030103000081c10074829828280350040c0400c031510a44110280f90000a03100d0b18403078018041101e80060280008000c00d8081202e150b0024034200da000c40300746203c01d410740381808520000c0c201e03500686028800c000ca05070039249001c040101808600c41c4c203010700d540107031100749500c4042d00c1d1003600c2c0d0384010b6404020101c0402059016400240c0041048a20030a1a100d410b02c0d009444110001c01d0140f400c3d01c4041e14101c115030005400641100c0075100c0100300e080c00740b81858000d00c115203582d0180c0106a509a44100ea941d080142006003406070b40c072280b0b5890021807a1a1414030011050700441c0140c800e0307104000045020302100b4401309024040c91000c2e03c000341 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 737385215 1250 737383965 737383967
    0x30b04081b1605060c0d080901320912040b18090c0403140d0822080f070614102d060305341b140c0111060c0f07021807 53
    0xe150309809032070701805074901140a041c99010f1303411501c005c10041c2000c0001c448250ba00000080501d05c5540d42c461100c0b40762030b03d4481c4590009004150440d8500d0444252045602e0061080ba1550711068a00d00515a11021213048a441c024002c1c0c07190800c8802e5000e10081c14401c41d40814850240444414103000400850f445415600b281183d044c08031a110086082030f400890501300c0040c00032201004401079080150550340300084059468620a030000010040400408100e8108200482c85030313200c100e0f04400441d02503e0150040e442541003409520045440780d4010750b440303600c07801510310301a01030181900340ca4131085c00400a1000301c4018031440008600c84180d00708000c0e40c95640304000d0000329241449400139603841ca1102c143c500e80f0941412440080b0b4000011080c04030b6240d0b0103007450394007850005007852945800344456400071b80a00184810010484425095140c0c403e511503019000159200c202c1d8205110f001c0408003c0024103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 737386465 1250 737385215 737385223
    0xc0d0b1c0809010909050606041229190515010302090109051f080105010f050a0518041803020d0516060e070305120c060709080d0309140a050a0b07080709030b04081b 73
    0x60720003139803000005a664100001601d4050f0b8809070070000c100018002500c000034041d540c14041c40b0b440071841c500c45084c50743d82e0b0b84800300c0f420240c0b242050000e0040840c404c022034060040e024005800d01002541e03050250700303441814940c0c00101040340d40d000d6040c0000a150041c6a12403180034000100c40c0c5010425511000806100000c40c07250300940e094145d03c602581c400d410305501050548031580300c04510941c0102d0262218855502d41c0504407281c41020078001400005183c041d103420341c1100882c041c008280030380c0080160f481d8046076003c0e00640c0104503503912211440c02c0103042e800c00b4083d0b00900614000405445000b454007003e0501100c565903506541202c005246003c1c07100a50000107546a030306110b900500750a038040d10000e483d9a080b40501442d0020a503421070300368201030310080030300280c1c8104950110090402a016141c0804c0041c00580140401041d50040030b01040601c05401c0c140c83d07601c0d140710018200120b117030758002c2da2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 737387715 1250 737386465 737386477
    0x5030a0b120106080c040e0d050a03020c01060e040311060a1e02030c160b0f010501090509040b10050a2c040f0b1e040b01050306070201060305120a020c060403080702180c0d0b1c08 79
    0x6ca04005401c0c0018000240502d07440741581e0b605070425200324030840c00307940040c07400a441d648400380418031f6030f00c00d06024081c40c42915451054010700c034440c0d040000041800960918061100c1c1d004214103180315030146510f0b10069695481807070030000307402010400c07116000c0c886854030070441c045031030303500911401940c090f145ea030b070f4001140c4040950042c65008070b4071101240005081c00011703a041144038596100c1c40d6141d8000ca04404155804072115502011191201d60a010000241100c001102e00c4c0c11b4a495265a1071801d10800c1c0103280c040148c000400c00d50344001c560b0107442140f2042c110906050510305000c240078001c05110b4010407020646d6240144506c500316544400607002c00c1d803a00c2e1100c0500c0e0408403a60095028000300d051950b0f958000600165201d028001e449803254018481d10882c1050382031682c05040043c04142d4a030310060740c00c103420074540850740084e601c002ca40c550001d021055440c40c08403c03601c0c100400d00014280f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 737388965 1250 737387715 737387719
    0xb04030311070f1206020304391a160302030706050a0902040b0103230705090603041401060501110c04021605030313030e0a0e1b0c030408070602010c090605030a0b120106080c 77
    0x40b068640781c09201c04265489004681c01040721842c000400030307006180c0c4076006540744080b00101d21312080700d04103148196a0010851203c1c10140c20345805a00043d10704455820315007422405540818031881c10403001e48180d0382c2c3c6000c100740c03080045402140c1d0000303090000f42020080100a0304944504034440c038201000710b6100c0d40700348620740e00494030b0403600d4410000148140c1a403000a040d420070064200f07c3c214490700c590b40194000e42c070a16a030303800403650034211403c4821940110b0704210060300048622407001400c0030729040110780041c0e694040f01021602030070700c600010032601004c4200101e2a0551001070f14072070281d1030b0102c000040c602044500301041c003c0071390081525005c151050500484801c081c01c0701691503103000415070045295420551180d0003a030300c6448180702c06a8280126800310751503080003c80c040c11f00a02401c42d00000300300f01c0003260f0301c10724203010303a551680320f502408003c0020001c20740c503900c0040d1651030805800b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 737390215 1250 737388965 737388973
    0x903021216110103021b07150c0201360315060f2106090501090b0115020d210b04020c0a0b1f1701240302121506010302070305040b04030311 62
    0x14a915400d40c00c440750800e9404415460030096502e114201d00350240310b034100b590074840d4200d4140c07206803c400c080c0385a0010301071145821031403814010030030344007010450011403640040c1d0304a00b40e1844946290581d00000c0d4881d00c100c0d4801442004030030740500016400428810310501c0101206032424003441341035150803c60116100f14458100b2101072000c20015441e074286101c50380a105600200304110035071100303070954000c020281c0e1440b071b0741c0e001003080c9a10385503460241811400680380d4041034000103485c0c000590315a011103414684000c01480c400d90180c0341c5014000c10441d100c05056071042c4d50b450040340c04581c980010380100300410070000040341104400980003561074100000780e9040d40079803401d21041c1d0749940da90351030150000184543ca0b1390070b880041c150707450341c0104640d0740000807440f8001c1e0001a14212195009081c443c0d0188080c01c025a43d00c2a070b00e0101e50078891944200c8a80c0c0000c2808810142c0c00001d1882d1910704ac000c071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 737391465 1250 737390215 737390233
    0xc1003050916030c050d081e09030d03090506011406071202010f0e0106031101030b010c06090803060108070e010c08031e0907031b2306040b03250e03070b181003090302 74
    0x1c25001c0c02c031800b014105081042c810001841d22400325100c1c540300f00040780c00c244a002d43c83c00d10301d5000003c40c0028001260178811f9003010012409040d0b1186000d101c4160360741c07245511040706012f0442249103e10040207140c030381178115445250712150600b120a00004028001c24501120442e010f04110901c0c140030414010002a69045509001c0000030a40150300800c600080541405005a901700c0030503128441d10040c24081c00841d40da07450000c2c00104940c0000b0b080b04244031308010000d8569a02c21038881c00e456001601c107079030361100c000080015541b10a001490807038135080107803a00010819900310788c8503005500c10700354540f82e1100040454064039950301c800b40b140c0588103400a2030500c40034806003080b454151500e4940320a54002c9403800341c0355982270109550040406001500281a8600446000d4400c0c0000c1c3d1505220f01c50b10030900c0001c0b40309401d0204040780f96000d9600240104046094080e005c0c014100080b070a4015000317041107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 737392715 1250 737391465 737391493
    0xf0105210f070e031506150d0e0c150304121107030c0e0a050405030a050315092802130603020d0213030506070f0504050927191b0e040f050c10030509 66
    0x3c40280000c010b0207085007800c141d02990001d00002c001c01e9100340310440c0750418003600d0004280d601c090324070200d101c0340040000c0c0d10708080c02e0311090051281075a00d25078103005400380c076001640700344c02c481c80d2501d1300b008440100851080160034029550300101304000400341404403220b0ba08504081d03621241e041007141d01c01c55001d8150740040014102480c403076402154000d0f0000803110300b640d0580f0116000ea081200c01d0440c0011040956444128803108203c40f80300c54441581313001c5142584100044c614840d85003459008070b0070076a22519a01030724a07481d504010081038a9603410241e83d81e200030b84014000c9401c8044500005215004031004d440c006003065403681c0ba0104c0c401d01625402040003809070308400d07401c000b802d05002c80002e2580302410111120390a040003860323100c00681d071030040c2020110401c07140c1c00b02001d290784160050202e41c2200c040c2c1c00c2c440d00308891840c19541c4000d003140303908a440e4150f030159005404070300444400c0100040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 737393965 1250 737392715 737392727
    0x406091d0a0201020d081305070b0d050603160504091a0411010f0201060f120f0507082404020d0f1502040909120206040b0103150e1903020d0504140f0105210f07 71
    0x10190050304050505d06001e801003450310340020011790303120311601681d00c03410b081c0020380d003040e501600300040d81100d04e00c4601a40782c00030000c4014000302c030304074034103000040002e1003130754003c9840344030640c00d221228401d10141785813241c60881515040c0b03000540c42003505c011a0200c5c540100610342c1c41e10521800041d902c2c40c6801c2484c0504004110883d5540710204556001490301c2420025000f400f40343d0003040610000e0054038030074041900050215150907030481181400c020160b030742c6e0b210340700405400901c031035000a51401e006034070010003c51801390300d00000c4c0000b1248001e0b80000c04d2540641894540600b8800007261102e10039140a44040d48081c018000304002c40310401c1ca40d4000c84000504d290320104040c10268910740420a044168401c0c2c000c2c140c0600c1100d482c1d00091074030b01d24060810321035010801c441c8841e41d00591801410412030303406902102c0c62404c426858008611411031980382e01001102c507243e11540302e030b01164110f0300440c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 737395215 1250 737393965 737393983
    0x40303090f0317090f1806090a0c0e04020306240304030e0402040b0a08060f181f2301120906150e06010f05090d0206030405070f060f170a0b0406091d 66
    0x84040b150700b24680f1003c24603600503c1c134055010715070f45214045944c41e4440d2085642c400100721000d851b0079000c0115111001f021310811504141d2004a8241d200200003080202100c0050f125103400000c10010f941d9a400e005032014070b045016440004903001d1031290381700e6950b4084011412042c0f00507401948108440c00b041403216620082c0030b001d01a61119020f09091000103220000071400498580c03a481007070079960500c071003450b2428180003880b10003501c81280a1400403c1a2005080541080781710b00e1561180c038160f128101c029181079010b6814406103004c1d04044ac0104614100c0c01c1b0034007500e220000300c608070031403024401c4038140c4031110140c409403000d4800d54014100d41c3d81c0b100d080c1800b00b00582d54540034601444c01040103081d0b4500b0840e40015520302608100c042c06010400380c0b21166004030403800303c800c000132180c41d54440f01004070141c0080201982d10904000001c075003650315521a14847c6015504c060410052104944d2274a0b210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 737396465 1250 737395215 737395223
    0x207090e0d0804110f03030d0603060b09011d09010212160e04060501020d0507050715020a0b0121030507060f0501060e010e0603060d02040506011704030c0b0c0a0c03081f0803040303090f03 83
    0x2842c00200480e401e24105002c0e2a00a071074000d80100d481c2c0001d055512003040d00541c60382d03483c4140244000c1d8804d030072603000242c0e0b28040650416200038000c202c1006141e001d00c100c000010200c500a405030307010381c454182c441b11075040c8031151600814000c4c00010025400c0780c465061803404c2d005050481d00180c01601a040524400700c1e15035200103016100ea1040d10b40004510402d0844d9803042107140d03000e40004029403802401511040c0c0c808036850b04103543d5007040c03a100c0600410125494240b00b0741e07421a61074100054024601d0f610402403a04000003486500b01c1e0011800060903656001156903000c20407040e4002910b00c143c020748011071101c01802c00ea8005900300e03105041402c407080400e024a0f109080441d030850003e1858141c0004105030170421582106801311924108400d030403000b48010603d11019080117404000b0650f6114a541d550900340d0303604201e0700d0f1450315140000d503281c0c014070080300050586070700011340640600b134280076a680 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 737397715 1250 737396465 737396477
    0x60117061c0506010f0e09070f050621071101050108031305280603021c02030411041a10081503030c03120a0621030e03010537020a0207090e0d 63
    0x18200600440020510300031001d00421808100420010400c850003400d4000c60250403e0410744041200c00c1c001e0200403595000030b4041c0030b83c50760840d403002601c0303050b07880716140e48018103240322034804100c4e0b009810100c0700c00d0100d021b900ca143d06c0303d0704a5450091141c0d99070b41c0c103565941c3c1314401e20000e03074038059007044c81140b5020118030610118800554882d14518442030000c03001da5101c20042075000400c01840f903124824150480800305003141585019214a000c2c00e6500d400c6510860340c40f0780819811001ea0030b142428000600190048a0950750141c802c40c1c081c0c03010581e40050134100340140c07400004413211541c81501642c01c01d49032005039601d00700041c00c145c0e640d03510b40c0c40202c0d40612840c0204490390869818250841143c1409070001c0003042030b10780a40d041900704800e50320090b200540f40313a10100e0244251081c20300040d076101c0c02c0c03244400300e0380c00043d107240102da000031503134117884c40d40004210700d84003103071100c3e81d82040030400c002282c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 737398965 1250 737397715 737397721
    0x10e031b01080a110f0304060e0102070f030e030f010e0114091c11030d1a01110a03090b07060605060f04030201140c0735030c24150120060609060117 66
    0x11041c0041500300920403070116801d81031192020240e000f58200400170304001c0204000d01001d4040c03120302503c108000c52428038141c450a48071000084c000c0c003841060460b904454800b04003094003211100001c0000114445550740600211151100c100c500c0e10045000d0a001281c5109140113040039039151340c03003481055992052003906400a4007080c424102d01c50740038014950500d10100c00013202c03103440c0001420603264000c20701c00035440180e00000181c1c000c100308048e5440c0d0104552658464500500503004a4120039000301c004144000c6942c0410f000c1c100faa032003600e030b441802e04180c070000103900030782d1036100d003c2e8802103040040c0440d17081c3d0014001904581c44510100c003503c40d00c0b40304200511484141d0000841c0040443e040c00780e4203645009200307407103451620080004010001038010000da0000f02c01c3d101c116802901d40700388200003965800d43d240307414214151100c2c01202c1c030900500700c03c000036420b58401e140c00c0181508240a03444103031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 737400215 1250 737398965 737398967
    0xf040306110d2c031305131e0f0b03030c0a0f030c021009081c090e060126070305010b090319020604091e150b070b060a090e0c010e031b01 61
    0x4807024450706011000c0140300780c51152800b8071100407266855800c0310454840b030303600052100110308185030700240484030008401c580c84a040f580122240380e0258400301020f0014032603011851614030b07400c40c04500d03405031500030403c052030403682000f050040c041410b450384038001c4011016080010a04000359030185a94a114003a141065510710f640d0701007600f403000109080042605401e0030048844208800d41c0140c5060000c502c1180f51200043c2500c905030040c0d00100d07100b0000168580d10850100c0703140d40c941d80300b10028455540c1003040c0d400341601c00c400003a0409001040c000702043c01c403510f121020b001000318012503401c4070303090351000e2402c0741d01400410002a80103c580600d0b401081c1502c1500c0242c0d000340c041204448078030381644445000c0003020020107139044c003035801c3e90341c0001d0407132980d44d1540001051440c0d680c001008061800d18110f0240c0400600d01009a000ba00c40014100d113a0040582d1540c0c5501864482d41d4400b00342c4000c0c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 737401465 1250 737400215 737400221
    0x607030309170c0a0203060a150905150303040303050d06090c05120709170f0106050f03061f03060f0b040b01030e0c04020703030b0402041509350a0510020912030f040306 75
    0x325014a00b84115410110100d45066000000908075940808403c40a5103810700207103400c07101c0030b01d04100c201a201e6541955900d14414003441c250340d0380002e140e0000d116200c101d41200241600d54440c0ca034540a0150303002400041c580d185441c2006c00d02443c1c0b4450509602300d00d4a40c01c0c05c09104c0c41d10700290a400408a10030000090400581d0944100d54500041080005000c0300c4042c00c60031821903e599121030301c030301e100165405241d140402d400742c00c012044100c0003440c44014504070003000650009148910703004640d64203907140e900c000506501202d06010340f02d0003000450640340b00080c403070303021f80000c01030341030751303c1d00382c1c01001c815100341408520300e0100e2000030308a03001603119000079507024240c0165654001050400b90404000c60390040140300c1380100c80005040010410311180014800c05050400040360b403150f112080310f400403030095170316003e90030075041103000f1440c1003007080c0402c40c0841610b003010f60b140390240c1004c0c51910703802d0107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 737402715 1250 737401465 737401481
    0xa060513110903010f0e0f52180c0e01180512070806010e070219080909151c0b0a051510050304030e06041512020f0c06160e06070303 59
    0x80104100205001600c017801850800d040402c00001c0c1c042e0304842d01820402c4004003940340e03801208210751480f04850034404980d216404003091050700000303070301c0c8880002c60040841c1c4603100b14000c1d440346034042c0c0e109a0340078040f03040c418a403040c0000c05541d4a81b4286001c9091549203a07100d504c034988020b00b2000c01c0044e4648690390710086002241c1c03000d0300f0091600159424407a6080802c030140c010304401c0c031841032600d44510001c0d11081a000080d10485441c076003d01806400002d54603200c00c014003441460400110120323000300601480b038096a031b5038002d4030101890300b41014000b40c11611398107540d90f41c0414500108030042c803000c00c0c05a0404e440c41c4c551921401c004a01c140b03500c0300c940e203041c41d080c0036040c200800c4109105010400089c059442c8004100b4000501414440c400c140542c10010180c014041d00d041100304c040741800c10301000241c03280c01021040003244024801d4242142d200100e0511203400c450204005800248a9400500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 737403965 1250 737402715 737402741
    0xb0d0e070b07060f0b0a03020105160c0504050a1505030726010f0c02030705070b040b0906070201020f030a090f09020309120a020705030d0e010318030f030c09150906080a060513 78
    0x650a07200d00c05400700e5000b07000281c8490b0b55420151503c10801e02c1030501e910f5041b0307411160145103600082071384c81045040114903085040e10400c000c0c00c10400c00190100500074881881c10382c41703100061a01c0b9022000581039032100050320309002c1a40403d0b6514030701c1c543c0051001c0c1c2c104503617001100c0908030843d941c55000620201441c811611094a940d0155545003010b04002d407429240ea0000401803e0400c800c00c6041c05040484084000a6420300c1d02d0b841e240c00141d04140140d1041240c50100045100001c1c2d48907004005651000902482c3c00340c460007201c00301c2c00203c41185942d03100e1760300e290f800c50031100503101d001c419104541c001905c0d98042030030300721210807410201d00245c98818281d030b0076024185100b1900070000b403852010386c5006081e5004c94081b9001e169642004441c41480340d140d4002610395100700200c43c0104d404014180d0005108180c0001c41d448046144109103006040884500629904803c0c500c0301140d801010710388035442e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 737405215 1250 737403965 737403973
    0xd0905010509040b03150408130e06010c0611070b040516060509060702040b031606090608070e0d0305030703090804121b060804150e0d080a11310f0e090c04060b0d0e 73
    0x250251b03400200b00b5226500c21400c4580310049103030f91030381498094200464100c0301c00c04014099074885e508460441e0025400303d072a07002c2819103131640c403803a400a0001c00e071142c1000301f032140000e0040181d058801d4084e403065510b01045401b400348030b41e07042e44218204598409441c0603000441361850013015912840362114400e200c0740d055034426000b0460f061010015550403402082d40036400741000e0300704042d5800000c2c10414681801802d03c4404808079810790311a81c049580c00354050300242d030340c03916156000000000032008a641180101000c4a00a20241540200e41013901c4100881d2140e0744d50200c82c010003000070340c2596443d140500790150800c02d0010038502d43d02c0d15501c0d4141041c1b20001d6402044001001c0c1d50100322003e1006440100155050486003481c0500e10000100c8070040056034025185800e00003404510030801480007030082c03080c1011030340050100710501017900c5040c46030348000c0c0d600b8000e05e11321004a4010b0b0010414600540e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 737406465 1250 737405215 737405233
    0x90203070b030f0403030b0f03150a0f0603030801150c02180606070209132f060d0e010e060f0901090f02010c0302070e13030215060a0b0705070906090e0d0905010509040b03 76
    0x50000d40d08220390024240e003d040c1840103041d094071490b108403d0664005000310318800100e5640c6c0380015600002e441d100340041c0b500c8a245d44207140f03900001c44c0502c00705030340342801400a00e0070f0048004a0342203e00100102c0e0240320881071080c1d0140c551041e078560390709500119a801449181c118108008a500590b1410300c120320460704029589c030740c602142000140303500a000b42403400c24041c1802034505800c2004012010001c99805945c1c0c10242005000782c843c03520207000381e41c20601c0d42c403c1e846012950781c0c4a050688102d00302a580c040c0c0329420b0b60b94400003d4140041d009464025500c5054007140e0103000740100d981490742e5080d00c0c0308100303003242e421a00ca075441d04400205641801198080385418002485a04000d00045c0382c2d00c1840c811440d080c4000201401004000e2041034010504290b0070800c841e5289404006006c140c40080d9560007000da012642c0c078011a495425114103a42e1141400151414000100741e00071079143d0521418040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 737407715 1250 737406465 737406479
    0xe0901020403170a0e010e0f120a081222030e0409080c060c0c0c01080928080a0210111206040203090a0501110d0c0912080f19020d090503011404020409020307 70
    0xc081c000f581c01451882d44c8021a00c030043c442810300304a181002001c5400351400d135652006256490b070215403030030700c2c2c032100707001c05103010b070f880c000100740000200b50b801989598659292151000030b041002c0028110808010001e1200c0c5c002c01103079828110380c2e040d0625910149625200e9460a0701d40041d041d0b0131032414508a0705801200d90018002d04441003d01c4113010105d03080c2018075003410908031191716081d0031000801015041d40c040b6172030301c0e00f116010040c1500181c10716a110400e80e0002d40301e007041680d08480508010201c29038032010700c2142e00400c903030312681e10603860300800c110107944083c20009c0d5522541c0e4008012030428454084a61080c0c11030070303039070010300380650306071001c2d100c00c1000e028001904015003220305010100c0321703a01c4101596117000c00007907214640640a2a00d14008400c01d1100d915030300050406220581c07a200c2c907401c181d5079810542a43e500c82d44020b03c20100030f0100300107080035085440c0462005040d00c44260315111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 737408965 1250 737407715 737407733
    0xf0403080d050910060506031603090c08010b0306060a1d0c091302040315020a09031101020a0b0117070b0f070816061e1a18040c15050a17040c0e0901020403 69
    0x81c1c0044160303070303003042c4010a5401c01c0700a1000a1802040c01080e290000140780c900004000082c1440e51050399007400303200c1d500c15140c8a900c00311031582d6586841c60b260081802104d60f03402481a00702195403460403000020407a10f85045d0319004c0880301e48101542000038160401e1702c2400c0c070040203569901030100402c6c00003503800603201c03451420085100d00507449142c0d181c074410042150025031080320710054035003001820702140c40900c0101c0ca00007d011010b4807098a600c004101c41c9122806501651f4100044a00d1207072200d441c1803d521442005811010041050700300040c0200d0150184000c03041c1c035000c8441c00c6440b00c0091301e0000b001d040e500c3e403030075448907400c078541c0c0320b030311954140c1d01c0001c1311491071038001c92540300303480001c00c00012017000014100080048100040d06410310200e10140d0a800040c1941c0c02015100010400d08040070041f202c40040c518461038010010b144418a0312503661611900a02100b026540030040030000c90f029078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 737410071 1106 737408965 737408977
    0x11252306070c0803030f0402040b031618020d0e0c0a0e040b04030818101505030a020f061b030406090e0a09030801090507050706090b1806070f050f040308 68
    0x2003005006202c441c2e22012031403100108121001710032240007800740b80309a40038800399005004140e00c96401ca200d550004440309420401040504100d103200120000018034110b031100c107010907100a0800504c843d800b4081021942c02c285107040000d008101050903282020fa4a030864000d02810140401070220081020b102c4100b581c08030b80301c3c160049641400e400c0c10781c02d015000c08811084010903000700010fa40c00e01040170b07074034907500a0040c0e02c800416010040c0300d800810640c2c94125400078150300c040c00400040010b40703075549840c8041850469003100d08200140f900704920308114520300080c0e000141c15041d2801030034007140d59901da000881703541c06501c002610040c00c1140050510040d03440050107041e0358403079480c030340229486e8039560b983c041c1d030030100080d044101008a28450400b070140d14100716005451320341d0369242c40b82160004 = true := by decide +kernel

theorem cover : BRFrame.Cov 737230215 737410071 := by
  have h0 := BRFrame.cov_init 737230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 737230215 ≤ n) (h2 : n < 737410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
