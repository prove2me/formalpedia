-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:27:28.865257+00:00
-- url     : https://prove2.me/submissions/01c56393-a213-471f-914a-c2c73f2e5ef7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 730575539 ≤ n < 730755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 730576789 1250 730575539 730575551
    0xf0b03010f051605031513450b0c0c0f0d0e0f030109050a141908090102010509061003080d020d020d0b090105030304030f0602090604030c080f160305100e100c03 71
    0x240495105003e40e40807041050030810490030540800e142001c0510644003030700d43c0404480650300a19983c1442e03801c10700e1690750b401ca02d001c200c007904100d400301c0315518071055101c488448207020510008002c2044c00000401d4106240c01400f115a0000c0c1560f0402c1e003100c5aa03800c01e40090f9140c030119070303c81055101800c0410000601600945c020841000c40d9100e90750f41e80070484008120b04003001030300384200e40500c15201c1c039402819075190600034624000c9880c0d0060780c1e1130380c0150b190600141404000058042c000c60030803200d183d002e800d6840e11500c03603100323401c6d80300317007640800134050b2801e21440180360301414480700107011841007041126580341079100522a41c01444148040307010503158003001940480010381e40c014010103d88640902d80c0003901c0301e10305803c0059a9400810343c0c010b202501c5042e5100c1e501c070aa292075005a00740009060790380b1800c684500000658081031850707015804465061080c056041e00b40c1c1c0807000c403040042d031156 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 730578039 1250 730576789 730576801
    0xc160902180604050f0d020103060906081e0d0f03090f0b0f04150e0c210610080c0303161e02060c010c08181c0c060207080309061305030d0f0b03010f05 67
    0x1102010042004840641c60945400000785d00c00c0400004035102c0c10005504500b1a80258844401004184001d1008130740c1c6141d40c40d01c1e51550098214240c40d00f03100000d860300040360301d14001c0140e4a8448100f480c07024120014a00c1c294100c038146034054142000c54504004103108040000f001c0040d890240381200d1030820807650061041c3c10103102c075000c48400300d60300007000c00c1980c0c80c04800710b11405100c001d5043c01c2200401c2e000f900e06001c2400440d50b50030b0107646a400c11100301c0d101d06c0c81410b581c0c1c42000e00400c800d28540320309400140c5c1c001800b644d003d15154904992040301e40010381284c2c400e00c8608800d83d0f50342100b03101036820284183d4170850b60170801c00c80c0f81c2c1c50003807543c49100f41c1200b440114074120000d902e00d405416184c06090300710b801152130789120b2612a07815441a1074551451080d140003a02c248107070b05405044c0c0781d100000c1c0d4101503e285407900034080c0e4404803408142c450800f824283c409220340061603423241da0104046c1454 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 730579289 1250 730578039 730578067
    0x10e07020f060c0306060f07080d0203061e03030406111f020d0f05040b1f080d0509011b030212130909050709060f030503031605190c0209060d03020c060c160902 71
    0x40c44150700350b50440420004458a000240c035070107001030f1040355440c507103070420041d24411810010440500070401c054602c1c10b0360b001d544034800c2034a0302c3c0c0d540500078898030039101c40800b249506074001c01060041e54410120b01c0f503925004021943d110740304d0000720b404035460702c06940f00e895000c1488040307094140914400302d003110350300b0051801c0c103456501d04110003c0640306c000c00300402590000c41e01d503418100400e181002e40341095401c1c500181554040c1c500380c0e000610f00b24220302031520b81400840a20751503001409985400c103281c3c601900901400c8801c590b00c8a00000c0980d41c40c00b038245040e00c1880507020543c01c2400e000304480c01034100c0c14081c01c2e1a241070001500c000100d940081c0d1000400300e01611400013281e541c810242c414412100d07035001c2d95202600015000c03401403013180c444125070740307c006000a81800540180050340320769084070690a00c04020410101d0100070382c4c00004018000030514030440d80701d0242c0c6a8001342c905112105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 730580539 1250 730579289 730579303
    0x5180d24060f0504020a11060c0d0506101b05010e0a0c1d01050d0602090a0f092a05160f05070602030a021b060301062f0307030809011404150f0203010e0702 69
    0x202001942c0c02c02d4600a2001d0180c01035902642d8006a030b18201d60091300d6171240785144104982e650300d8008444201900060000c0c100142042701080c6c0602d01558034580136480c030385e20104c08542e030b4118843c210740c50440c00d42e125580d0b821b600405900501c0510f521703070700550020b1581d40c50143d14401d1040ca280b8608100b0f51110014007091b85c51080d0140d500303401000168803241003000060100c0c26a9200455510340d17038030700045003009070f001030401c84455880c003e80c031040c0d48140c3d80382e15070000303040000074010030602141130b10151400d00e0301801080864003203107240d5100c5283c05c55a0704a540917038800319060a0381c946c10014920b18000242c3c2e803410f240341c00b0000c07404900040c0240024880340d4a002181e6045050360f4000302c8070300000249040d08040e000d43d0f26603002ca10164005101c420018540c4001401500d0040c45210044010396407561074441d0042ca56819080c080e5407038802540940030b1300d00186000e842c400e1224105420013040207850091 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 730581789 1250 730580539 730580603
    0x70f020c0a03080f0307030f020313030e0108011a070309030203010507030516020d1e03090219090c09051c030203280908060906010b0a0212120406062405180d 70
    0x10107410301c0003d00f50820784a10039407080400b40c580d110702c407040e0040d1054000d1224094400b200708181400180b10004c10b960003034a40111110b07424004403540b5109006604510300542000131a45d042c010080c26918001e10740680a04d40b03d45c002404d4550075160503000030344440a00c10103520f0740c0c0d0307010750142c03040c0024194045a0500600b8040c04680b003214050a42040d03807070118040d42001c0c400ca40c0c000c25610400d0500703000c412403501680280c512080c83d103c48c10074021f001d64101010365400802407185040704c1c013028149030035505800ca007140014044401038060f202403180c02290607081c90b01d10610300f000e000f07046188903032003404c81d41e000c5802e1024048001c1003141c1500d05034580d181e561407405505a02e0401c0448842041c008000f480c07020408814910320b008910603c010f00c00c02e61b07074028840f842e082c2031941061052246004c580e42034080d10040c01c01145103644001d12003198030020740c80e1a130001d41030f0342c80d03040184000c82072041140e429200c14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 730583039 1250 730581789 730581799
    0x30b06090709080d050a031b020604140d1b061508070e0609070e151c060807080d09120201200307030807021902090a020408030c1b040605100503040c0e070f020c 71
    0x50324043c501955880c2e801030303400a209000510100d058440e8200415150400488040342e03250604001d545003011202664400500c1082802c03c0002151407031810b00e4642e921809a038405240e6201a08031510031a4000d81c0c0d41e41041e079489422a03900014000000684032a40c0360061407a1580b40c010100d51207161000c04100c5000d070030068240c820a01600c01131605100c810605c486482080b10411440200d6042483e1484150300440c1c01d640f01503007541c1c0c265541d2004141c5e40c070610040302000c11902002070001110040d588081d441c01490541e1410500045401c00c08650790703225190344e040000c18900307154000c510203030400c0f01440200049541d00c01042c1544c2c00c0258000d20950102c00403503c801c0107601610040e102c200d00b42c9940e080c41d05859503581c000f5901e0001a90954a001c6420f0f00d0203108010803240d0151100180d20403040c01243e00b0380c40200101c0303466440007008038088140d4980345105e22019103074880b20410400e030184c41c10304954802c40c401d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 730584289 1250 730583039 730583057
    0x6120e030a1403100504020f0c0f0703030c0b1f0306060509072307110306090703050601080a080a140c0106030b0a180807020918190311010c08011403070f030b060907 73
    0x14940c0a800c01c0c0141580442150b102c4c0c607071070f07032003191000c0e603900c5a0703400b500100d019601c010510740101550159542224038642081c491181c41c2e02042c840603012030358805181c00070039549020154000d07450405201802811f44220f803204034141c01c10344059076a1034042c0000d00703064481581145141c14a03201e00400000108006421078020152401021071214100042030765081d105903801411380d0070614008a00c99964048c42c802a03030503201d030030000114001d0200b21000d00c0d42d08070381c0c40c03442c081416405441c80e040c1920481e102800070012051800310070b20404010f1480303400180130908000d40b0342c4c016690f646048205010009503c00002000d40c4104e5002c0c0764159400c801c16555150310440d220011004c8030304600074200d80d000320701100c003159440c0300d10030b403901d00ca01940c0300c940900301c466038903d441c042048280140f00e180004010745c1e81c01c42d802130845010316107450003030340480741540c4111425100d0500340480c42c601800800d82c040800d20b050340d94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 730585539 1250 730584289 730584307
    0x10204060f03330b07050f070b0f090103110f07060507030c0e0904120507020306090102030109110412030e030f0d0e040f020c0d05130510020a0c05120706080a1506120e03 75
    0x8032940401c41280b4203c01103800d20b0086800d4140d0038014191004640c1c2c81e014a410001c1d00c64400940085140c06184004a0080c500d2000c0d80d540d00c103071312005e0b424000c5040040d401846112017800c01001c0501c4100ca0042c401c40003400b24501c1000c0126460030f1294014007a9203d2207181c0044c4880f52000d00002d40300c2c00f80066001d50041c20981c0180501c01040c1c03114800c038074020f0341601078941004105181500154103e03800f07a0f9080103044920310180303034207000c0c50140700c103840c0d21441508046442250081040800101038885034445e501e846494554903110490106d81c81081e450500d190909c20f84550014440055180070f2210006e6034560300c0120010040c0031001c201202c0012280050402800014181300b03810b00c14039070069078800400d401142c24041a940118160600718003002c00308030f5100007405580c0c241001a111450010004526a0740c0c90704128540151600000024400d40d2070b21a0707400c144004180c01d448403608140b0080c1c0c0104400d140b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730586789 1250 730585539 730585571
    0x20f06070e060a05030c0712390326010f05090609070e0904050f06010608060916050901030f14010e070f03020306030a020609030a051b100206010e0a0207020d0b040302010204060f03 80
    0x103d110128a03015a4079603c00d9403821180c01000800f4110755040141e078081c01e60400350f60941440f0070b01c1f0200c5217110000185590404052010045000c1e00003083c00182c000c02c42035182c542081c205003074200000001e17440c071140c00d9004c0b5035075162010007085036007010051107401241c1a00e519541c5d10740018060100300307170700e0900d5024040010024060007814086d0140010402040d6000781d6944e0000811450040d42e0551052a102c40411a90002086618041d075203648566003040ca07580b0065006046500681c0c014a841f80241d80700c03030111030046806800d0000100b0321b20b0600381d40051500c02c9040303410090502c1013007072184c00d81e03000035007106981c3d04541c1e8503502e1103010f02103801c0a0030010300400911480480d0300125240c03000840172940c040e620f41b80c0c01c05506801302c0e034400c020721880302d0000180c40410b05060300ca40080c00c0382c034006010644c03055165669071402400c11502500143d60100b0203000d003591003554240358240300c0c641400000c412070200e0b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 730588039 1250 730586789 730586797
    0xb190608060102030f070c05090711060f10031502040602150108072c070809010c020a1a0a111b060a0908030a200c0a0212030a080f0403020c0d03020f06070e06 70
    0x14080c00903000010308640c0c03080089a00f038070000e865881c0c454660b4500752150b40d1250185900c1200603200040c02e161007030320030000003007801000b841030381c9030610403401a0070007078a401500b850643c0f010011422101e14842a101e403041d006903642c0c60854000d0401010514030740300e1181000041000d280001041c000769881d07024100c604000ca03506441c0c9504030a28481b8080b01400100314031681c00854482c41044130130006c1c000b09030b03440012078a55038040002414111100c0c1e0115807111075038141030340b01c1842440010307514a88451a881600100700c842943d0040503403055070703014180901c5401a9010300240040e102c55a10300d41c20b03020080948004594035054408080c880d0f41100c20300725102c0d13100302d07514260603400ba40c07a00300300401039001c0d01941501c00414240001240d000b4010b6988046054841c0507055510b040c0181c800d40443c492070405c840c0c147da5040c50400524400d0300100034022080c1e407001c0c1040c80017024402071000c03003400d29250707441d02c004803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 730589289 1250 730588039 730588049
    0xc062a120a0b0409080708030a090f060506030c060f270415090e0d0509100207170a060608060601021f0906050c1c0608030a0e030f2d070b09090a0914010c030b19 71
    0x7c0ca8480d41c4210000d001000440e60103400000d01003406000c0c822540d0040d13000e44429410b86051104210a02a941c400c1100804441d1070030040140400b21490115220111008100b5006684200041c084e10030320324610586d0507000508015041a5100713003c3d1108481c00504a64201d10a02918602079800040d00640b032800b08001c50a00c28840c0001428509072949107214013070303410a43c0c1b0340344000201c0d08249415400b1508841c0080e00b580b0500059000349405020360503000c540100302c1c0e2400407520b49500b02e100009440f4000c03944144081e540040c0c55600154403139610494841d00c9080e105e02d450014030850700302204842009410781010f99400c0210b00c08246418a0404c95000500554074910b210808580f080091246086140e090030b100c2d042006894140c60702c540842007004210061a6091501740c481d400000364070300103480f13003968484e0b0400c5a01c480000119954a00001e0700c116003600c28400d00b010290f6150350700e04461510549194034034000c2d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 730590539 1250 730589289 730589303
    0xa0608060627010602011b0207030f17130b0d06050607020a050405280209010908060f0115050909190507170402040b04020f0c0d02010606050c062a120a0b04090807 72
    0x784280380340040140d101200b0009010120340e5550b0000f8001c1c659022294240e030340348000701d0051440002d800301620f03042182458508034540e511039440c1c4115507165203c08007488070000d080c5000019070024000b01c400c06a640541580c0c210845509411040c8600c000340220750240c2c407a0f118034820340d40c060300d00158070f481c1c1d242400740d04c1c4007564002e0200085441d83c050308520980103441e0210b02a241c3d1400c041c0c503003080c0c58503030404a0713001140310482d1004024400c9d00c1108201c1c2c0d103203682004c40c81d02403e000405d6000c80c04403404030b4408141c0011520707255503449a0ac1d4452481c0c0f4100146141d45001c2107906074001d80040e22a03034454841c40b41980e55903044078403100c01489130b142e0b10540c0500c083d89515040c04010007551802100054290203103049400006603080035046550302c81d90340c2d600e900d08601c8c058185d0a009689a006400000c0003440003012240710260185085d01d102c0b0152a092070701c00340224185404c0314002401d8409076a900740d48402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 730591789 1250 730590539 730590559
    0x5031806090a0803090a0f06080c0702060909040b060307090c09090b1201061d07020105040210030e010b0901080a0c0f080c0105070323030609061504091505060a02150a06080606 78
    0x200050340d60080c8460396a01ca4819440029002000401030103610000c4e20401120b40d030340d902440310100688914004903c180e00003403141c000010080c9502440100136504014a9034041040000c0880d000c480b205440c0050240502e400c00c401c1004011440b002e00140c0e40100c0003d00401081c0300303001790692140441d01941c0c0d6058006840e11140e03c0080042d13039522440e414140c05012041c002c40c80d9001c010503403261060141d03601c140c0d000350118202c0d80300080110002e114203410091255aa00343d40c0e011541d07040d5299008180100041c900c1e0416130402085001c419480200b2280c01c3c908100010880490ba011222409080207900c42d940d81c10103071466800d480300002c08104442d1b590583c00702c14000f0f50b01509044d6000d03091641c0e1001884800400c0004a2000900600c41006881601e801c0382c00c41001c540260107103940c0d500003040140d04400c0380f05d40940c10404a4003203009a1118541c0e0007500444103001142ca03010301e29880b40c5010341528000d0703030404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 730593039 1250 730591789 730591837
    0xc241d031c0203070c0602240a0f0603030315050f0906190b0a0507030e0402070b040b060406120b160207060503220203030c0f0c061c09060e0a0f050601050405040503 73
    0x102010340500e0003003110301da148584480003500ea6000010858244151310300101d2180d100180000c6002e0484500c081c0210400c0e900c80f070312000040c080f000d0a03840d03c2c40d01c0c7c0380310810302803e00118420303180410682002204d90800c1079254010501807a0803240c4141c0e29992891041d401003001d441940201a1502c03c0c2900d50013550010320041034005800100c45502c000100b02190090351800500c118003010801030784140400500005042d81c00701d0003080f15001c2c40c54101c000103000281711aa02e07119407a01e000e0440301074035007d440d0401c01051401c04481c10400c142a440603101403420940d015009010151101c11062214650140380c440554400c200e9150002c08407a114a10660704d40d64130401040c48501d207000d1550700f2180fa08040f0240d4001030f84400540c20103410202e1a480106500070b015144186c48030300e1640501da0511a40f0441801740035038482c0306e04a810100c2c544001070b0b000350b020324a0310702008041a000b10030781e000c01000d0900405481005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 730594289 1250 730593039 730593043
    0x1201030f020d0c060c020925030c0203370c0206030703050a110d0e1b0607030509130513050c01020a0818010c060c091e030c05150f04030c241d03 64
    0x301c00020050364403c440802c103141c100c074105111302c1c422600003c4a42e03645554a45c5010b051441740120606003c16200c8540a81c000802c66203107403040b030341000d00d460006003c4011000c41100401c1c500003800b03030403280d000c000060b031601c1802d0080c010350707a07a13001c070300c031440000c004001701a0348202160801c0219080042443e5a441c0300c185c85261001102c4020104400350384043d10030600c40360307003102100c0754810b000040201840e0030000551400e0b10780d0390000b00c0403644480c00e0300818513286150b100b1300340504813440392300300740c0c0c100e80c07030000e01d80051811642d05542c044054800010b2144048840c0b0448103c4441180c40c00c480c0160b495411507040100000d00703089100200650021011080f100884240100d0403103002d800c2c10b450f4402e00015042039a22a800d105900305030b042d140c540c1c4269088240341c6903090031040c01e15002070b00222401d0012132801c2014104440c09505110316a01c170807170901d14403c0c0081c2048ad26074606010180c2d62807a108901d64007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 730595539 1250 730594289 730594309
    0x40b090417041a0d0b2b030306050307060507050f03030105090c07050102121f050d051213090f09060b220f0e0304120c0b04030b0703020d020c0118020103050c1201030f02 75
    0x51802c3d4a51044905400c03c0360702c0e044100100c106615110356200c80d880c0840240c03001c0780320b403404525103c00e0b8840c641821141c82100390305154540c180012142c1703003084a800100408d0f5a41511902d1a1034513a0824608400c17010f80c980c814801804160f45282c01180c1107141600c00781d5a4200510703007640a8010886058098044a410071640102101c04419002000f98000480304d855000b003100c1407410000181040d0722040901d000300c0c20b0710004110003180c65641c3d84c0341a607102040b4042d2080c03c00c402d031205031140d006a0030001030340107213450380c142210106a00c3c074220380d5001d100d400a01c030000c0302e5503d401310f030b42040106a00252440b84094207030396544c3d481c0d4841203140075003820100d03400c1c444a00c00042490b20401510152a80b00c80060125140c00354224081c0d00181d10034040907500300400e5042040910540c41440f0328485001d00300000d40c0000340403500c00500303945032508108041008a4020344955064030341c840c0c0074a001c1072180c00440c5503410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 730596789 1250 730595539 730595549
    0x702010c02060a180b0c030f09040603080d020a02011d031c06120b1605070b0f090c040212090d0516020103050c0c03120a110412030e2404090b040b09041704 69
    0x800040c000d0400f50303102c409280145140800301c01841d694092460041c490058540c005400c01d001018610070004010048000e00070070104e8031036107c2d00c81400c2c41c0d201000c1c030003159600141035424190280541d01200403040f01c600c0b84461411242c948922540401d14246107820060740040329141e0f0000002e0501d802e02d0b000007a90134034000034080c030190780300802d605000340c40340c0b030252041c000c89130903690021030540151540c200d0020032010150022881e80610b800e108020346592020b001c144803041c5000f50740c2d007040e075102402c1407440a5120100402040314202a0b82c00e800c5d015a5a0b90a02c0d001906540b100700f1401c003402400141c0c0c8050000249210b01070840d981368601514004400b00a00e02d109190344002e44039178424401034006402d0141c0c04240254485d100c5900013506545221203580310010702204001c050368000d81c5e01050901c2a440f042c4128000e1110564040000b0010b0340d0004200e030400410003800e210360a032405c003901c1c1000098800601d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 730598039 1250 730596789 730596799
    0x50619120611210a15030b04030504150504060e030a0302030a110c0a0806011a0c07060c0524011403010e120a122c010b0d120215010b071a0118020702010c02 69
    0xf0704844514694a841d150140092801075020580002052160780d114820412201c14aa45540d4400c1c101000080c020b90074800b080c0704c0002c0703011019000c40c0100507a50380c0d803a912420315070064520070200003014020741c000030160b80026000821a071b43e2107880d0030070703c019881c0c400200b807030038010f5007010303400140341800020041c2000814505890000601d01020b10138480c1581080c01b410340b541c0c0d03955200110030000c041c000c0303500056480c02a015100c201c42991402d00e00085840c0750701c2c0c0313652070800c010480480500849000281c1c1100207021200c110442e55a0300c00391100e00c0703190800002080580140030300e080e03540b0104504002c0c17001c40d207048240d00c0044c101c803202c0c00c020034a80f070641c40001070601c9420158000204400c0d916001a1901c071100c03d031031036624003076103e520880041c1480c0c2c3c1e40564020440c00c110035a5035841c5180c286805185a500c200e8142000c030018048180200407140d0115801c1000585600e41400121000042c0400280d005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 730599289 1250 730598039 730598047
    0x80d0905030d060801061703040302010e0a030f120e0f03070e13140c03010c030b1e0f06070b061c021c240e0c060c0d030f110c03070303050619120611 66
    0x45482904200f080784d540710003c00965545041d0003440c0040400707151a60303042040103200641c00341400f10111900986644c0c41c035609c0780d58842d03404160040035605005010806803800c0c2d80400d0303c806e05032058420b20218990000031941d580918060704103134400680c0000c0c1c0328110031086496054004199000f0904840803058441901c1c8109030300075401c07c0300c80f000d004c1c06030040384400c250141854441d0500541c1034005042a190120f600c900a503e00c1241035940001030008070340225240341d0141440000c02202c016006030310038640101300070b5000075a884400300c0956190031083c94665594034601000c45111910300130b1112600e4005c600140c880710741c481c011010300c01c0c1c00c4079181501d03c000c2180c01d0142c0704502c4242e40c8800700310840981300390040d410880181c0c10225500d200740240340e02d00d401c44404004945c0c03002c00d258042c10340c0b41c061070341c01000c183c0d00904c2c0c03208102480ea0b01d0000034025980032062503103005003088015800403102104615080e03880e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 730600539 1250 730599289 730599307
    0x909061f0513050d03051801140a052d071412270307181107060207030302091c0308071d030615010201060f050f15130e0103151404080d090503 63
    0xd40100070040a0404100b00210312410910304010700c0e290076840751410940d04066203001c0c01e00c000c0c2c282d810441e10849241c2d030f03011540040c0ca10a1031507182c1035150f106180302210b0b03625070840d4402c0030260001003414000000390840b81000d820031449951150625400c2c0d2821805080701025100005030718404495543e240120460b0312130082e12150f200c100405680741e4144c00f5159079004c80004540f03100b1456403200107210407001d0b80030b08050035900c134072040340c000c500180d010a13000501c002c0c607807030813540b00810701c013000c441c2180103100c58400a00d4501c00616100501c10041c22118112404991140e051a0002c080303907030750b14150101410303858182030f6a03405582480700209031039030f5500c400c00a030344010780600345d403000c0d032020030954100302400e400b1048010000e007050505281ea030200500300d4850999140d500d903180500105842c2c03140c412071107150000c28000794a40c81c1c1842e821036000803d042d11900380c0d1500c00024420000d0050141c8000296000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 730601789 1250 730600539 730600547
    0xa0b0f0301090501050906030c01030c0c060614030c03030f030c1b010207051506010c05120912060a09051207080901030905010b0604180b010c030906031119030b030d02070501050909061f 82
    0x70590349010740902c840e0b40c0c1d40d400d000d01403074103464003603241c0c0040e03003070300410f501c81d500402d8002c43c00c0c500403441401e5078a500b01211040e0300800c2805164507800c1101d8203003044060b0b001d5a082d40110714240b2101c0c1500300c5130001a02158000c0d20004100b611a02c40c0803203420200f000000171940c8800625000d507440c40007012500682c2080c1000031040d60045186110702a002800340ca2032280032075400120f030340030003039059004030780300802c0024150401402d0701c14112420009621a510700b072580c9480d41e50440c019507441e0400c0807400040621041e103198600070300b400b14040b0158541030740585514080d460b0011000309000a5040d07007440a08414078402200300078000c1c007440110f501840480020300803c20112041243c5440f80d07014280700207501c0741050510b88054403224241e00d95640b908002911000d0a01c050f00d002d200a40b0ba0303254600061441610700700000e0318034020341c84c030f143c826454080021440c0c1c590354048104003100161a00c0c3c3c20303000802c050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 730603039 1250 730601789 730601791
    0x3050c1b0d030507050f090607140105131106130603180803090c0111010501030203031c152402060106020d0e12060a1b030504080909090a050715120b0d020f0a0b0f03 73
    0x700c0080e041c03102240c0c501e8041e600310380291142c03d00f401c6ca45254002404136a0b401040100d89405c4001c45506608400317118443c013034040050500402c0d2000c0c240740e800c9121100403144240c07400c0080f40c2c80c801d0801619001c071107a500b0040780c0000e143ca030011440340d80d048041d0960000004016142030b0100c1c01d581541c01c262902c0b0320708010501000c2c04c990b000d000003901a80100000300e01c00c121041d503c0c510000c1c040011600040009586151589590260740b0030b58089241480c0c54013a40b0901c182d41800d44010320f004c1d0300d80b02009603100d00b0410700c4014403141c04107040c40354880b095500b4002200000300e42640c103000880c00004e020010004800ca1002e40d5031104091081c05154025500918050f0074490000c041054000016000b40d4503441444102400a00c041c031040300180140105640181301c0c20b48081d00441e00d65a0408817680b8003402c40300950380e0040c0d420480c64040d601045001c03d90004242c42011503040f50910260106142ca0402c104000071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 730604289 1250 730603039 730603063
    0x80405210309040b0a09090602030f0601080403230705160518010605071e060e0f0f0106060207120303060503060103050106080c01141603030f1509060b0309060703050c1b 75
    0x80c61080c500200c16420490618032904a40e4200300050545860550441000204000d0036078003015640c1021104036041e408003180d0087e0088108101c8000d10300f4a5680084d0a00308103065250550b80101035640d00d48040c505401860140c3c145125003c06407228980d100c1d04036201e0b850704400e00b80c4044050b00c2954441d492443c0c85200d076941948001c2d040301c61940b0b50506080d21956a00a09512074008920300b4140100041c08500d43d1f0240b182c61741010000391030410015060b1505020301d001440310240c1c14080d080102c81e44c0000c02d64200d07a0303a1402c500103802c07207240460180809601566244c40341000200070f21a040d03224070111844030045445006800005451403a40e004102507071042c24007074003c0715a10030140b0501140f180c070707002a0407a4613a6040c800c494807841510a07420000d003050240c109184140b80c00b60400c0315202d81185006a40c0980d12000200801b00b0540c4407004107065505a00035507070341400d9030402c041c0045c01240c200703030794120600f05c5d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 730605539 1250 730604289 730604299
    0xd0f05011802190503150d1b0e01060c03032304050d08090106050112020703030608160329131115071101090614070f080f030708010605210702100504080405 69
    0x1001050118910031504001c00040d4818018695401c0136140d0341c0000f058006030500300d03c0c0c0c1001c00d696980101c140503100d0700340380340100b80254040034442c1c000d80018640308d00000052042c56040350106050b03650515021801e148658413001520004030748142c6040718030000d00c01040740109100c1da00b42c9007540d4402d515550b0741c5009082c0c0d41baa1090902180c0c4c811042d00c10341d110394000308230300c81c060700b808100b0f00e07074840202d40b03880b00401d554519150003d9041c02004484541e803006000b1801810350f4041280d15030b140b8040780038203000d41250701c1003c800b0410a55502012203110000c0c410300c0c0d01c0c04404264061a40300c59402c640800a004020f002503020f0308414084c4d0300169035a0050401c1c15046e01601e038055041a070f4590102800800059120801070a583ca142c00489841c0e0602c8400507011010681111091103003e100341c5c400200c1e5015034102e40c0140b05080b65090712611000d904000e400350441d00654203080030807044c01a0400240112035065907 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 730606789 1250 730605539 730605569
    0x307120203030103020d031101140c09190302091f08030c032503080412030f110415090e0c030a02040e150f030f07090209030705060a0908100902030a0f06020d0f0501 73
    0x6022616440b0900000b50302c00d06000d402004a8400d40c211080c83d4a100300001e02c00c480342c020100d20202c100c1e410344107410000341180701e03401c01c100c07140380200c0304260a80c89241180d0000d507025100800b503d62410b001e401900000c240207031018010200700302640e40c1c89441c0039402d43c5031b41c0f10404101e0b00b08851301010990044540c14034101c140c1640d90743d401c0e80c8540c2d99124034402e221020200309500d810314131600d40070520a0418510400400c1540c070f80c41e090500c405611403d10038000c0c0840d5201c00c1280788500005d280d406500c14010369564ac1d41c10003a43e00074012a009500c843d140f0000300f100160700710125007610b080845004001100010070156181c1072482044041c3d0030820341004009903980241180710300003000e07540c007143c569001c44e03a00d030030150b51880022405101004824001d00c255101d10114a505104013105c98000c242d5420441380000c0007445000e200c807003070100c90388c10355599440b0044103001c1c1881004402d80030700000e00500d920741e00411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 730608039 1250 730606789 730606823
    0x305010f03020d02120708070b07050706030c02060a090309030c03030302031b16020d05071a030a110702010509060706090215070c0803120417040801050a0c0e0d0b010510110601080307 81
    0x8524004480d40241003000781041d5600340705d0600c901080d800c615118104c4007082004003401103d0203408010180c0d62590710506240d480c10a03154000c1040c0361424581740b040a40c007054855221180c000d01140e800392074a000c41c0c1c0000300c5c1c1c0c000f40c45440200c901000305585030b0025801a0413000d210300291441c45010540d52084100496030795a5207010030b0014100044007007906400f800a1f52602a80c4580c0742081c0900702140d03000301c4500104000c032090062213810804484401031605111803a40040c2a0b4810310301d40c2c5118200c0822020204402074200b01c002e207501400403440000d20060f402d407540c10044048581c0954102d01240c0e45030000195180340c1a0421000000d44598882e602a03031940e51411800420030440883c1a078002d00440e400b03040c110800062010132284014241800020180c0c0f046454800e401c002c208144000380c1074804c01c4a02d04c52002c5002d00c06d42da00f034000701400c5010300032038000040648011020b0903903140660411541c4052035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 730609289 1250 730608039 730608059
    0xc060c0f071a15031c140d0501170d030905030a080c090a0305010e0f16031410020a091410080705161407050906090c040e060105160b01030201020d03140a05040602090d0c0501030501 80
    0x800401001407170341850b03080518492031b01006403560342a4074500e001c85240b12101a10026040500900d0950300300040c103550411502c400c1c22900c0c0390030001200c2980d5400e480740309030303079070241000580e4010841201610b01182d00341c25000300820403481c0d5070b291550103400c903601c1d2902180600c614401c0202c1e8003080203148001c0c06503220314014255a207400703000b90726030801b254911541c203484a00c109903100a00340c2c0e6159844213482c85103040700c0501d80d11002030b142c1e400b4106a00714030301001c7e040310764280c20102500702540c44031080d8400449040c44204003401c044400d81013103807403031408111031003074540a4804440d1a603591042c0301002c5c0098801048001040004101c0031701c1601c0c0c201c0d04400145041c80c58003c0382e030b0890f05c1c01c04600c1000c0c0c4014100f000104119a010480703014000e26500f024440d00a07920092444080000c2429041a40340c5000804006140d4110341440030024400d4041034181d04020503a10b1940c024240420318002c000318464a02d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 730610539 1250 730609289 730609303
    0x30f0f020145110301150b070b040201030e03070b0406050f0903041701230a06090b0a0302210d120606030b090a0b0109170c0102120c060c0f071a1503 66
    0x7010090003a20000c055202403560041500030709548a0107481c5000d09010b446a449258000c007401d0010210480c00c25013118640c07031402c6207a00e0558410003d5200c900180c0b044250800140303440ba5030f0350300041c1c0280161000000f13a5000006201080080c3c1c4210300b40214082c05041000355038649010009410076521549254020b0000f009180d181004003403540c0311801c00442c104044040321800780c03a40041054000280c9020440308660502c02e17a0014102c9071814401064031002240740f0880d0360202134001e24281d0310340700c54800c4c00c100c0501714054a201321410200384000c0200300c4141c9240141907039040030310020305944240508110035000401150951300c03004414801020207002d910f0600c0510000083d410f110603100c504510f02c500d025244440203035000a007040c1041d944c0c900360032020300941d88040d400095182e071000c0f1500d5006e9941221b00310501c030500404c4001020040c8805100114642d1440380500401c4156030179042c0703403208810103440b101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 730611789 1250 730610539 730610561
    0x31505041d150c03011208090d12230910110d0305010509090609030d1e0608010f061e06050f0d020705010b011b21110132040c14011704030f0f0201 65
    0x8020700041c0070031440e11b1426400313544240e021902c0c0c407840d080450691a801035003070300c42085d00a80a28003a80140642421009494503540144138020310000e06010300e039101401402e03081c10702c2c1525401801c90145000c4040b0031280081c00e00c09000740070300f8090050501903032040011600d80600024042d0040d90540d01450501441d4243d000080c041c1c80811000d080003e40703c4441030015202e2a00504021000410381038a402154000e41c0e90315172110f921060074007000300c112181d844000e020f540c600e1400d1a42c903425400c105156000381f0402c140d00601c0002e03110208001580240e123115400e0300c803c0c0501c0300001da80c091018007420007401082001d4103222080b0114180140c144089090003549054184e020600f1148a07000c29140c0b03c0300b01c01d82c42c4540b4498030003a000d50039040d01c581103a18103039a9101048199101d040301951211040b0b1000380c0c000c0034240e00480c8255641102c078501420f00800c809014142070000c141000f9100c0b44803032040c0a20300c2841 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 730613039 1250 730611789 730611811
    0xf0902100f0f05090d020d03030f06080a0302100504020307030215070c050609010f0c0c0909050f07050f011407081e09121618020d020c071701090c06031505041d15 72
    0x140000c2e80c00c0e2655405000c0341a0701c030f10b004501e000181d45e400c603810a100d029590004003c00c0c0b002d8581300310b460382e07003100800d030380700c0003502c2d0011764009040b0551008848020409840d0340c1301091500080b40c10096202040d141c1d420010110f100103051001c1c0159144c4030300c255504144186071143c01222030001c2d69003a00f1200c01d038010b007503212500f44611a4001c0c099581d090000032204000000c551139084580d0340701c01c4220030480b070340207040c0485900c218101c0403400644040702a0307640300c18240c0081103020074840030000392260150321680b030a4000030248062411580042340461149614920404c071108000407070f80580c031681d030983c4c03080a0074140d40700030140002120822103602000340d42841c003014005499010f00c0c120041510031f0a0a21182c08050a01900001e0303a1400c1e4202d00810a180100300c200c03840c41c00e000884034801d40e04c08050f10142e402541d0464101001008003c9a00101005d51b221400940f400b1009000c82003110b4002554164001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 730614289 1250 730613039 730613057
    0x109050405060d02060c0102041d100e070513030309031a060303030703090f2010020d0206070c11150318060103230f0d021e0105091e0a0203010f0902100f 68
    0x140c2015072015030828001081c0e0400004154009107940c0c0c0080300c0e0300c0085c1d40203e010030092901c240072401202a1040f100841d00e040c6a200400c941617101340758000a4020114a85a01030421224524221071000381d809440c0d09000c4c021000b98031007152a04d0204040c02e20081c52601236601a12009010714510788803071a048016100041e0305950a03124140c85ca80010001d000c0740045d00c26154003000f22000300001c21004641059840c400c1d900300080c610b241c40c0d80411411703031002207070900138020303884c07410301c0600c150511842c260001e04c20220100c1c154120f40181d842040819480a800103444643c1601c4080a1000a06041400c80820100d44c51050000c4008440320704440407001940511032802c010700c481040580c00843d4000400000c2080350205007008030001d000d24100388441c4c99403201142985140c01000d044e140c407203010188034903100150020004d00c80741c1e80c046074480007044055012846a5800f1107088111405030082850041030380c1c440b4045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 730615539 1250 730614289 730614299
    0x1701090c050f0316080a060e1504060504080d0c12050c04291309020c0c180711010e0f011e1806020f120a050f0108070506090d06060e0403050c06010501030b0109 71
    0x8030782e80d407681968103003d00e510210340c035071180540700b005200369001011609003d0601d40d0840380c15040c50859604a640c501c140900241c6031035070004d074802030008081d5154100400300d0b000d07030082c11000074240180d49440c00d5118805007510944000200302a449581f0203900c031b4400c922801300c46510006002422058050000a03c83d040c08a09450700304006e803607025001081e0850b00d4400d0340030901800700740042103a0745a18000362096420320b00300101002000724010300e02c40c02c0008103141021080000e42009000c403a03a60110740200c0b910040c4c0901070594400c0307032452001d088407046d1034120700e409407411030385e400050400c0201b01038550002942c0f0044c0c0950490904010100d8500d8800001c58404c2086400c00105420440704410249106a2201c049075001318001d111540d900001c41d2080c000c12581407403121054039145019005075805001e40c0c04140040009040d0800700805201c0e0420042c0c40640e82c903040150110b880c0001d049000446131901444 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 730616789 1250 730615539 730615549
    0x108011a030a0e0a03090602150f01090c0c1407061b03090b0c12040e0403080609071413170c1807091a07020a06031505030a122312011701090c05 64
    0x1401020800d00807603800c0c44410501d240101441381100080c1e030a210400030180d040c011090240f5031031a281c0451700b00003001e0005800103005500300503544100c452001800f40c003a11501c0c640c40020740109150302c4021a4550b241c2d889804045030400c03040c2084c10340312a501684003030b0306d511820107541c02c0c14101011a080f051107100d1038410364110b86c451440c143c01500c001d0400801494031880e203480e0061280c18040c04042c001c0034214180280580c0140320b600c2c0ca940c0340383d0195150700c4a070140c0f0400f203400d80e0002402c1600c2d5010030103400c0700414000c078191019a042412003101c1c684903456060102c9a12001550b856028401c00c103024004981c2c814501300a42d080c142c5a80000e42d20003010391201c804242d5070034001442622001d02140103220880152514007825200c00e804204001001003c0100c41e4401d82c1003521405400034095802d4250076882d08043d00081d29070348021700600c4140e05012501030903420050194000144e0300081000581c0c0c0b40c001442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 730618039 1250 730616789 730616791
    0x51f090e03030711070807031b0b0705151911070302010c170c07030314090a02120d080402120721200f011d13090b0a110403120207090504150b0108011a03 68
    0x40005c1c0590480040c001000304610340145004505003003ca480c06664031140d07004170f81c00300b61a0f01c000d105582c0480c03c0490441c203450401411030100d5070f142010070607906440700f10529018038102c0c0c031a024a1400e8090200c1a109030020880180b00e42002d41d0aea5001d4a901c144e60811031001400030040d000c06000824464100400d1648038015502020403040307944440c2c55200318044029442d000300d135510f00000301c03406000c8950303d124008241510050020303029803a0100100d0442c0000c2003540000d00c082d90282809100c0000703400c049482808054648103c21241441190042401104e040310002c2c21007140c200700d80700544003511807030840c0d900001c4003135414525480310b1030103020044208800040300c0c1d41030305c1c2c04022010003815007071000d840c0c00c909101602010003154280c07504402c1006041100d00422842d016098010310b48240c00c2c50188010048040b50a410000d8070200600008441400449040d90b00348a241c0540c54450300040007118620021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 730619289 1250 730618039 730618067
    0x1e060509040b13093323190f02120711070509130525031502070614040209090109020303030c160233072f04051f090e030307 55
    0x110340344418100040407041c059601120044e11280c0302c5007040300035803000c900c50106050140d002c541c03407070745013980b20300f01c0c0502c158031542d40003c0c41081e0500082e014650655584403c41842d00740b800c0807030342c40d114020404860a0100d0715081c3c3d00b007402940c40d01aa60a641c0545550380102140c00141310a10509203000e040710124040c0c03110a000f601c0f5000c4c1944290780c00c00d05141051404103048401442a844209120000741c0035130b82620440303030800c6002e40901e09581e440700013442203c1d00100045d00c0c09010006580c9049045031050f402207031000c81569030810058280c03950a400250b16800410014080f8600e0001401b840718400c140e842240f0b6403a8045113104921054800d0f49200a20700549011000d01c6207100b480c1c2c50034041428091240c1c0e641e00c0f020406107003500c8001d168075604004503044001ca40e59404002c0040c0024104208a004c101100042101e030015094078080b4400c00e241c0260240e00500c00000c51855444400440c0c541c80322140c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 730620539 1250 730619289 730619291
    0x30405031b040f11032d0408090303040f12020a060219060f0b120609061e010b0d0209220e0d121d030304060f051302010c12050d06030305040e011e06050904 69
    0x3055500041e1051030f0a10080b058103507546e0500300c40105041500f20403a180e444e0a0f140c0000d2000104d10009402c551700c0081140c4680c0300c1c80020307045000381d4024030654521520001200500c010300071030b006000307843c0c2d017038069118501280c42e1b86c0c40c1c101d450325070b0841040000005e80643d0207200c40f01452580020740c00c0c81100060300d0034034440703000320701580b1050501c94002014000e16410040c1c0d40602406d40c082604821000c01b0140300d20900608003040e03240c2c011100d50100d500b43c40c070082117100d600014070110b080d07504144403012003140c5000000c02090380c0000f0b0307280510201d034803540022044548400003409100361001a2a07482001c0c229046604102850003540b0800000c42c484060782d1111089410040c803064801d6000c0d840301700580d800926000c03e15030013429400003c40c0441c1d050300d0034810f21051822203441d0181c00414180d004000d0820b80e051500f02c0201d03641e9549061103400d2160418000c103d00c1c144007084140d0003000100070b18100900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 730621789 1250 730620539 730620551
    0x313020f04060605131d190b0904050f0d031a0d08070c030b01031a0103031202160c080a1509030f0f0e04020d1b02060f0a150b1317030405031b04 64
    0x10201e030a45074580d014201080000c00d04054501d029091840a07118070040c0305000840c0950009510f0400b8064040106c0c2002c18500000295000341c031210728040c08841140c20300e46442952407040f80d074485041e014004020650f148a401900506035414079a0036100302c0503010820308004420007168042000c002c20400a020b80100100442c0280c1404109602d1820072003d59056200c1207802e002e2740700c00600002390072000880c2c90303c802e2000140c5510f140c01810440250b140c0b40641407035000d132800640c040d00002c200300168441c100e074422845400c0781d020103a500310708000307021405241c81c50929907c50f681000380c1d0441c2e8a00001c0303100496010400300d0b07208011082400380c03103850490f02c805d045003894920f001140f00800951a09250798101990040c10038190252500782c4501141c120184031409042c80b65015135541030304200d41d8122058a126003810400f51400810540700040141d078100d89010340500b50135030300c41404c01d500000da4401d840c0e0080d580c2c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 730623039 1250 730621789 730621819
    0x405101107062001050f10080c01121d07090b010201230103030807021504051e0a0f2613050405010f030305030106080a110d1401090b030a060203270c150c03031302 72
    0x409000c2c003940f20741c20001c0d1a818001a503003100d04a5808c1020141d1000d5509030169a010070741140700f41301d4620008101c0c040c00c42e002008605c14004800e2840303038150210b80d8900c1c2d58800c2c898401d00f600208080780ba02d110803507122058128414040020500400100b03020b0482e680d07004d5440c1c4142c034890b43c01d0030307100c8032811001d07a000d440543c032000c16007044842146142ca02c920507800101107a40180c0e5807094020803100d070007801c0740301c0030794040b1003c1c040c100c0e4003440304407070414a42c6400d0300d032460303841000c0544a018070690800d0000a0340b90b1000980c6001d0301e4040d56910702c1c60b1708241044e905000003038a01d50005071b844d80c210500b101c140c00501903a075a512004900211110781c5000103e0040c7c015240403450500e92050650b00040c110709101d070702c24001750f1269034881030f00c0348100e00c1c00d540100368502007002c14582d04e0041550030006404075448c00744040480001480390003074523607888095004001150720780385c102145160391407000f0a0108500082c0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 730624289 1250 730623039 730623041
    0x604060b12060f07030f0b06090f030304090f200309120a0905090403050c07060e060a0809070f030506040501180f030c0c08030d1a0420070c05060a050405101107062001 74
    0x407604000d43d400070505000d4015494054211008181d050500c2400031010020782c0501c143c11039244908006164500d0b00e0328280300303541c014100d0000400850119080361006042a00fa8420a90324084198240414400192802603403080f00078802c8a0700202035448a5016120100c10305c070751288009025940c0d034544501c160300c00c0c0c1c1c1d032584070016101d03820310b082000c2c0c02c1f01e414001100342c00c65031a1039070f1003034542c1014549400030180d141c0a410300d0400c1d01e00e80280485c0480031034080148040044c84500480c8118020010071255002e0b03050105c026020041c0120210f10f030003001720b84140794003000140a24074505a5542d20103544c1d00d10350086504150b555282d040d60050045881c10350f25145c0c07019101446511543d0003000104808030b41d06141000000c41c0c01c40030301c015951441d0107840090409a620310305000c2c06401e0360800c0c07061a00ca8540141d400381024030a1010100501e000c40082132110b007044c10941d43c100206c4200e45181c0da20742c02400034100c3c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 730625539 1250 730624289 730624291
    0x8120a02071718040c021207110a06180b040b0f0a021504060b0f060403020312130f231816031107111809100b270712060303020604060b1206 62
    0x1c60880355030703659503d0840f0045048200024450b9103886025181c0f2500842c5d007000040c203801585503100d03510326291081c00d03e51b44440b60000d10000b0b01051144c0c00c00d908078038036842446500e031441e540d59400c44591055006c2ca56074814240302c48200c140102014040d101c245006540300404d885102d01d030480d90032241603840c182c075000d010368641043c2e04170260406007a0742842c13400b403d41e000309a4450540703401c0c24604c4400680481080f0b0100f9110001e040000d2900c4000d075907844c012929840c880c09250130b8040d010791943e90f039141003171600001052640076007907140c0d990140b042c24684205800000e258807140b8003410030344100028850366101c1d0211181c104150b00502c140b20704054000100c110004082c442c000c407000501f40d001007038030700c40400c2020303905020460070080040343d0204c0c05901d01c0d060122071203800d00680b14440503521030311080e00c0c20f141101650b00c54072018004d6005800403c01055aa8104001d90311020b4000581d1034880203c0a2400c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 730626789 1250 730625539 730625573
    0x30a05161a0a05060907050720030a020d0303090c050406060e01111f021201080f060406051e0906190b0d0b0408040b0a020d030e070f211401062108120a0207 69
    0x183e03c000300080c61814a0500d500202d00d0702d0000c0c02c00c4032952360b14003903400c049042035450200d012815441d5401304006460580e02406400d048102407802802500800c1c0b0708030341d05018180c007c102800c189c42036800729644e55a070000c05200c51001500c001c040e0030302900c03060041d4000c46090000c0e40c240071040d400829801039a520001d44080850a4180c000c0c1400760004101001240e80c0002d15a4100350020b800091544078081d0b1007549003c00c2c0940100900040100801b0f11404a845403007450000003140600c5031009040085030742c1d00c40c100d0340c0b0014440315500803400190080b0b5010344a1090181340c51b80b01c0b04103407416080490a080103a01c902c040c4090107516000729240501d240c030042103090706020a18109038910f020790310070039804401c510024400c8210b40c010698001d0f00e0203070845990200d10f800303001d040c005c031200394104da164200000c0d80313018010741540e0066140d0b41010041008420405806012102103030340070300a50b0081940b201d440711001d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 730628039 1250 730626789 730626791
    0x80a0515130b03070b0d061d1902040e0703020a020f0f1b060f0f13120b0402040b18090c10050c1005040c210614060d0303050601111c0809030a05161a0a 67
    0x104140da00801074605035000035000c16001c000423035040e42c0c160f0311f180e00404001c01720030840c1148242000240940d40c00100044c45402c240416150140d0080001003d00d9098640c0a4070f500394065444e40d2945c03016149074801c821140f0600185841e000d16440c00401080c0303007002c0f104bc2c52100703070015145541d04e00350001d800b880500b103440001c0c00504612054242110080d22541000304005102901468031040106000d0340e0741120390703038034480011850b0903904000c102155120140031283d4010f5010264507a40d45001d182551142c418600040000540c00c0d2400d001426015000315140c880210020590a5002ca0b0a05c1d1901d40e450003c0c240c600c003400c0090981d00d500050307244060051052114039140d4180d04100303290141008595034882d400126201568a084034003503000f00c0c00d044030f103051010005013080d00b040c1e40302c20b4151039020115489120300e10440c1c001c541c08004080c80c51801480140da058050915449624103849a0309004001201d00b52406 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 730629289 1250 730628039 730628047
    0x270103240e130302030901140d0f0509190203031905040803040e0a11040e1f0506070609050c0306060a030b06040914060916050307062307050d080a0515130b03070b 72
    0x1441510407030a500c0104400c409005001070f0718041c1d2a882807100f400d0402401b905000580d44012085a10700180800c0030014501e00001d00d100070031040c2d48060650058031058405102d81d4201440f1013a0018047d40c680070b501c4580d0740703007014000c0c285808c2c41418800090071007014006400180b4881000c0780c805e14004c0f60607000c464001c00302c828810300030702042c051010001c051551102c2800310340c4182190f1300c118203c003254982c0c003807507000c40001350800230428146c101d040440e00c00c20880e030414a41200300358036044100c0301030380c02c03084a4008001040540120a401c4031000d480000c01c1c0103641c807801c3e10b1030b01c001908061584010103208103200300300301d6400d13010040085110882d0409002a4450040388154010030030074503840c40039100c010710500c142c3c464160b01c1e2644c411491401a84452851104402107601c05000644042c1140295445450716400c100c80d021040d0003003058408120040129899407244111361648081106201600300d4407845519 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 730630539 1250 730629289 730629299
    0x50a02060606130605031801110403030e060702030d0c0f020a09061809080a0c030915170c0c0a0b04030e03010606080105030d030b0d060b0d0f060902090a0227010324 73
    0xa00038000c1d00090190004002c0948205561420310b42074411915045950b500c4503042c0510390901301140000b15480c0418242c0d01c101008000e0041b2031103511070b02d0400600104104d014004e114002c3d4040d00400d08100309203214402d1007051501c03c1c4124111400e4540115003140a41d8002c1135540c0e40d05d40c0244844401403078100c4e0741c4400c8a40500c00c8880d0781d134840c003090040d00c600d00c0520403c1e10030b60b41098092180000a09492182c40381c4404c148100107161009809418160810200c0401c1c800c50030a4101c4a2800110340100810102c0c6d42d1045a80c0400a0050b401c102c0820b0780d0600903030b002c0c002c41000b800366644000c00355040500b0103041818401c0000e05151810140c240244c99031030030024180d03044000040e202c90190041034002400c5040145089001b00c60b038420000c4982c409000a4020b0764001e0884d41e420150400324400c180307408418107a458a1010462400c101d801c1402506150200d0074504280901d86960010740d203540130b01c00320790010700c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 730631789 1250 730630539 730630543
    0x331020a080609151e0906010e1609050f0a090e011d010b010804021309080f0705070b180f041e0902040c0f0906030906060e070f08010504020f250b07050a02 69
    0x10103404690040c0c00c2d1410b150030004d5075801103d41600044900c42c0000f003424400d0500c0c0c5254100c004107080c1c0c0c62501e40c1065032a00c2c800d005240440741c0000100f4008640b0005084a00c070340c6440b848043c074201000c01824180010401d0b9001450000100783c00040d801440305003810f01001003402000002c2d05e40450b908034050384003907031614181d0080b90b030340309180741c3d00660142c8804c1c0c030105001c51120003414500001401c040d4000810310404401c0d08004c001d194010400da0306200e45075920b41b2140e11840b0007100700560140744442c414a0a1005c0f00594007008000045020349465020644071840324200c0b007040d521000007040d810180101c215188603441c5c100341240188201038203e9045000394002c0603a56651346080041590015014280e07000d100c8001780362111005020751141811100050013034000010395050500a690141c00c440c041c030790405131105505500d06600e25900004240349051030800702d410300074640c0c0501c40603a695551042c0b1054003078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 730633039 1250 730631789 730631809
    0x6080c03101b0806120601060206101a0a0e04151e0b091c050a020d110301150f06121407051b0f030f032a0a031a1005033102 55
    0x20422800d101480454150b40c240704401e4100a043c00045601c4d00400300d000764102c2c400e110a5485004000b241c21900091030f98072441601d54000d07621611390382d06103035203100603064800c1030300103020343e440b1240102240380d40d00002500000384854001024081d4081c254004c14070300c001c03101e4010b1901c1207440c0e400046c043d5818847d03e804828004100600d52400c4841104403440701c00c803003044002c0c408411306035001080e000e0299100d08242005503501380c1854801d61074050303403d0520084c0c1c1a140111400300b82c8d45410145044416101482000302018105565600d8540d188240901c010f0064000c0d41d941754499400c3d241d00850031604081412907030740991035011540000108440b421403002c881140c690701c81d0b4001120704070000c0600c0040d031085440071000362038501c0c060701400351956002d0001085200505031144070038640076401400082c40512441d0183c0010760300840707403207a218443c05442c074030b0012032001c0708580614152842c5c1c501c81917241c150161 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 730634289 1250 730633039 730633063
    0x618061306030606030b271806070e12160e0705040e090a11010c11240d0f05240907141c11030f1602030408011d060c0301030218130606080c03 63
    0x5845000003e4400710180030302007c04103019201d41c00040c03c80c05e10f84041d2400218200c102d4009040400019100781184030015004d04540740306c00c030240788001010b400c20596414135500d01030601e00300340d440f6880181035000b401420400051048600c250192094404c1e40260201c0303840d91604010711046c402c0442c0c1002040030301100404c03001d860840a0803011900000031100d841c0d8407602200c81032022845820000c00c0b0303001d02c0c2402d50004e030105240400b0030130203650f400103256000008290500145401c00c0c80c4400342d8103145242075044640c07428580e00560b503802c40e0340b241da408407154060342c801741006642244a28041c410f240d1046c0749429080d4549840d1810707043c5802408000426447c42c0d04005a40c001e204940107804004000c0c000c401c50700010154400480400b141d02c0d2160a0003d520599048256410380743c1c020030000c81922000e44644c40381001500c03140615080003480000202c545c4079400040000c0009040001d015404060078141c880f204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 730635539 1250 730634289 730634299
    0x180a03110f010e070b0d0609020406080708060312090919091505010b0f0d091713033c061e1b020c060a05070602070807111e0618061306030606030b 65
    0x120f52110480030880c40141d07240108902c2d202e009160108014001c0c84e40412440c1e80f0000300400d402e42c1c8220a03500c901c403162078002481d200c09041c941d8a0f10404d00008050f503003800740340007900d0800303055900004611207a54464544044641c100d51600e01c00311075943c003100e02400248010700416004202014855041141003403488680344926001805000e65400c04401000010303114071420116000250340c61b0301e41251004e904081a02060703404e007985650002c10710003400d410340058055035407404032640c60710100f4039154252510886105455481c240c0c4551200640110380d420760020100e001c00421100b0b40c82000c2200100f011508085000c5250381c0702c41d000ca0711922454a0446d940b0021070501e5402070280400060030040c0001d0300505010140d1320410403d40c1c103c0b05203040b15968208094007401d9519169040403050003400010303441c510030300360201e0018220714031f080c000d0034000905011980122011a60fa030105000681c1d040c4a0302086442c1030321 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 730636789 1250 730635539 730635551
    0xd0608071d07080f040501020717090406091506050c0a0f03021c030b010f05030712020c0c0a0609060804021507141005181203071e080703270b180a03110f01 69
    0x10020701c85500203000f030650402e13440200f01004002d41c11540103c4d00641d06580180050703042c14440e80c0581e00b020b04c03e40c2410000300b071141851203004001c800100101c64020f140000030b0b140e07a000b0710b240000500490880c2004030b0317102d01203c40400e1107a4054070403074600f0f580c003581890105208004141c13030310403010740741d980194816281c50083d051003030b00da175901d50088076a00c400c00d002e42c10346400802c520420341c00000c4c052556440c01c44601c0c1e440d588a110869031107103688075040000b0b00000c081000b6007003d0060345402c02c40c03052031620709005512900b920a1a2a5034010540d12a900f9042d03116014414940c01c008503000080c4d0315001c0c160910340e981080a56001e013910000080360b181d0340030790000c07181200049181d01c103101e060003025005240032140d20700880d0400e824036043c009060a80a0300b0032003000301a0744240346868105020100503c1d103030001070200e0135508c0321503080203280c51701c510035501d44030058110b5a50300d003841e625280a91490f030500d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 730638039 1250 730636789 730636801
    0x5180108060712061706010312050f04150306051c0501062408090705090c0c060105010503011d0a0b060c07080c19030b07021009150c0c0302030d020901050d0608071d 73
    0x46034907070b080840c07890001489007076400350200400c4107500030a40560006020b407117001e00840c03154126400303951811802d41c031101c81902c04d0f06c83d603007502c504210204424401503012940b203c000c078100b0b15000403282d40311000b1803500044408440070100000c414841000000d024100103041c0740ca0301d0456000b59030508001ca01a0800c22105200201d0b002414140c1d0400c070358001088002d0181e9803905120f11710f41507a901402007d440c6014520010a081d4042d1007100d0488030700c0c030b484502101304802c0c100c52024000d82120241e41c1c480d000c000c1580d4520010701b1042101c0400b60684601c0d002c800351038100400062401070104410006d00c901941c0911021a60810544002903442c440124142000c04c40c500058074500740d00c1c20180513051003117500d50080700c1e0381004008441c8409542d40a007076071000700180d00401080303164031070030740141c862101c040c10b003241030800d10001902940c0c1c0540002c0701d223601801c01040740c0551080c003c405100b0b880040e0030b07242050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 730639289 1250 730638039 730638043
    0xb070c0b040909150c210b030604080c1c14070809150408010c030915150e0906060a0e042003010204050301020c0a05060c03090304231903020f040e0c090601141305180108 75
    0x20a034041b85000d103d2100c00300c3d0f4020b81d0003500001c140141543c00b2880d143ca0050400c0e0020140310748284150015001540100300100b010b9403403a032990043d88020b0040e80030981e0003258203d8079420300780000f4488c2d4440c0e0100343d04013110381d40d6407910b46040021450858543c600030340704041c241650340c0045212840032100c14044c1c9200850705002d513401c8103110001c5580003001d05c08080301000031a240101d1001d0040360101e441103900d035075a0030202000c48040c0e038090215a03140c160104c030001103940800510101400141c03c059680000900720380081441c0d600a80103105020100201842040e41c041200040d081c214203180b214907550b070089004100111187d11100359280211507001c803140380005140210003006003100030030b500e9441c4000c03401200180c4100003203103440e010307540381c2c0c00d408401400c155180c5400c01041c038102515644c14403424010086081c0300120007030850140c0503003561000781c0ba2400340300c004c001c071010381c821850704000140086500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 730640539 1250 730639289 730639307
    0x3050109112704020f0f22051503251203120b01032a021f0c02060906190b1801032004020702090a0203040c0b0a0e03061509010b070c0b040909150c 65
    0x1034409804040307805e0045540800d40c400c109070701645070300c2541e41808445840a540e07011450060041d40c4414807031200007015203c3d443d41c1038101030354500d038803801e030b90850386828103210714188900c0d60303200b00041c1040b500d68190000b40030003a1518001e44d80e8042c0d401035400a19040243c070407440446680b02c0b450003000b4040141044550000b544200700c500c0c07513020998045240c4000391000040248840b840e150b0160140d0030003c3ca41c25804505c45105242002c2d140f402c228002203480028042e81008940c459007150030b40740c015511864a9000c1c40c03281100c2d0030300c00340b020079000c0b128002502c07461046004028440c0140c4800d41c100d9080038200e0001343e1a0b48651030910003184694003d652003034001700e925a04135600c05d0902960761000c2d0f00384c500a458041c0b64490210700602e4041c3c201f0300200c0104114043e20004044407070050a502003041e864806020050340160b00805689403510090b01c184141026002030ba011800000c11220242ea0409840d02e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 730641789 1250 730640539 730640543
    0x1205181503011205010605040501060c0b09071a07020402160506042607140a0609111008010b0f3f0c12060f01030213092004060c12050403050109112704 67
    0x44140f40041004000d41202002d407100520034402d940c0c465400034800c22610a055901c1201c180218900030800704086059032220314010300406202100c007441680041f80c102e070816400c0000e101501e42d02419940214450300260505040604000303003c44000c018000c5203503807521040000024080895040c0b80c0e1100d40c0804490650300d1490034000d00e002e001c1c168a051107128010810381880018110004030703500b180800751042c086840c40700900685851080411021501c4402c083c0601a00112240c81c002046510320060fa80120004e0100c01e2040c0d0307071050540e001d14034030f5402ea0320400300346504c0c0c103100030f03107410b4500c01c81c0181102d405925144d500c20b08691290701183c6001e0400c600b0005442d03583c4041c0b070010500d090b400000358840100300b400aa00c2201114101c0348650b89401a625681d140c1c0704c0344c00102e500e0380c81404020000040010400e0051241050003020000d00307800004090006407007840001c208598200700168511554420080d81c102d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 730643039 1250 730641789 730641809
    0x70807080f0a0929100501050d090f0c0308090301200a0305040809030f03280c060209061303050a02090604020306011d030a08130303030e0102030c0409050a0603120518150301 77
    0x1499580b1440d008100600c2c025026400404c01341c4180c0720104c403003210201261403810040d0341c42c950145021425030254a0010300104402c1e04c2d103032003036045960b0f01c5000e1191000c0c2d62040b50380700e010044003a442112001008180728800d40790a201c4c1e460a05131440c5a200661840098110b2a2080301c4001e020303d40d494002c582400400c200b510f006000c050221000100a007003070725601c0c1c011354001188240700f04030641e08a101d041e4240340c40784c0e03c0c2d2981030105a007541ea2001a400c20055190002428483c003c5906003640e09c3c44000c6026030040e24500000e40113210b40d09000405260103607004005020290343d000090f141300420942040d80380c082180002400c6c00d0a00c50040c040312808100c214900c5002035000046901c241c804200c01811040107501780c1c00101c0300344030f50389002d010400c0718420941016038004c5408030700060803a1250344548486210303801c140c0c0001c1c4080703104001d80c0180c001011166030300b113451002c0480c0340ca190010520050107521000e07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 730644289 1250 730643039 730643041
    0x30c0d09030c05160306051f0b180a09020c0115080d030902041509140a0e0312090a12021e060108060c0c16061223010501030b0a09060e01050405070807080f 69
    0x1c503104108103029207a2000648640e00700d4080c02058802c118041a20f0306854040420048440081c0c202584038030342c04407030043c5141022041d8903400c85d0800e58910301450341503400d1035440d0804480680a111401610340a554150a0031100c80391003480b001d6181c0203040c00201d00000e06507038076401d5442c02060300ca8041c400700f409400e0003880b412006503442d4000c2602c1071203030408410420319690040041da20b8954600603166000d111118507001001091041101d000c0740726800005041210b03d0200036540b03509801c01d01008950050f001100c41e10114005039131030b4142030380c4800060140b0f505081c0d450b500c03880060418036107040000b841c040070a00034401800c4070402d080c119000f003560b40c0ca01078010582e400440d515180340c40e42c0a08211001c094031007010f0706500e441c074801d03030800d00150300400c1071500313a69024138180c100041900b410b02502001d03142e59250340010354504800d2000341d078000741071303201400034013010400e510364811f00c110f1384550700000841007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 730645539 1250 730644289 730644293
    0x60e070c0210050d090c030b061e01200a031d0a05060d02130e130218090d0c02040225052b0503040c09060e04031106070c0221010c09060305010b030c0d09 68
    0x11413007440808080d0a08266002081c4034003d100601201e004806c9201c031903a90b101000f1170840006d6590341001181d14041c01d042d44a0007910034007034641f01c085800d031116405030600d4581c1c100400c030005621419403080d90021505412890711007620318000b0a41840c000403880d000b203503134180805a0104070f10301c5480f80a24154000c2c0001c20f40e4034a40e040100070080001c0c420700303069003c3d007605408160403542c02c0c0a50380c0b01d001040b001c1c01c0300c2c1040030402c40760f1080414007641e2064091064001c1000240b46600c0580a030503c1541d40502d5864140d080c010380c01286212445000c00108943c0002c04c044800301510340740c41507583c1c2d2603240c40e8505500d1504903107002843c5c0359003c02c42c0300e00302403054061806500c401c582d010140803c0b0f40e99000440300040055214601e0b0030040c1071498511124000c4c50003081d450084c80440701c0e00b150500112680016200d140401049030140724445c05007010700d0640d07107940703400c4918916600ca01d07003020b43c0f019a03415031102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 730646789 1250 730645539 730645547
    0x60303070218070801120807020105092b170406091802120709090e0d09150201291003020c030a0f02010915051803040e22140709060e070c0210 63
    0x106407507000307045040601e00003881d0464164129000c0340441c1d0001e00200e964141c0a42c40c1a075194088500e5180010b182d00449039034116861003a0030404000a20801400b07914105d00490072202c0d030250320304c600307041010044520a8409005400030881485600e600400101c10748800c2c1c0d500d10a404800f4140400034402d40f00c00c0321420100d4005d0010a43c3d003d10124220755204c0ba0601032040b0001c28540c0b80e148040c6a00c001c034404001c2000300000c1500740391185503150000140e108111180072007440141001c015120000003158441403030610a280c3c45d000d03403480d00711b081072031207900e9903524810303415104140070428110018040c400d4002c008095480500c1a90480d401410032000e000c0035250b03451001068155000703071001c00815581140c4204c40d19601c0c1362140703034449190b0881c0310b0440038918001400c030808240e240d150300805180301c0d4000c000c2d2518280300c2c0c40c100d9189800c40c114055015040c8803120f0380c003856509903180c04a1342d00490071030041c82a2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 730648039 1250 730646789 730646797
    0x1806100c0c090c03051e01030201031a030102120912070f03051c1b030f090c0504020f1e0702030606010309030e1005130803071209050a030605041e05010504110105040506040905060303 81
    0x703002282a880114200c020740d0008030446091340c40520444d100d00c01c2c4160340c0c080c4145105404d18188004101541c480d4128007949421085032514a0043c100803909a92103010701100004054051144031102008900784c00f25030200c43d1420300f0440d603070300044014100f81c0501002008503012000140c10021004441c0410004114465444e1205682040b580032903002103803901881000841c6580160004280c0c40700c0920f40c1d160a100c10000250480104520785a4060007110310b2004845c0151640070cd2030200e8944400462040502c0c08000810a40c10142410710301000a500300100c1184031000310707060b81c2d10500c0c256044507a800345030120103d40059050006041c407001c001030207018062913200d0180c2d040c00c41e0603595085070307110f0a908210034807420000b107092035000c245c00c18400c003400b40100749481044000000700300c00c10344150b503550083c00204400c0340340b1010001001e003001c500740792401d80040c00c40c2c0542d1040d18100354559000070200e0351709104031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 730649289 1250 730648039 730648043
    0xf050a0b030c0f090613120b010510050a1422090506030c06040e341707050406110705031b0310141501021f06030c060801051507030203161202010b1806100c 69
    0x101380c000703640d04001e038070340f1340c44c0041554040700c40b40002c0ac503801c081c070b20340140000320f460b124a888103c0704203c0307001c1000c01d0030381412007051220b40001e18032110300844201e80b030940007114500b041c0164040b144003a07e194803d0b8030006111030b25442d25003e40d03007100c641c184150941c1d62501c0e0401e02c490f038242d009100500300f04180000305003100b0150150403011307549103002c09003c0c40e121001d410742500d05030040340c0e080c082040418841c22084508110941c203841039281c0d240d021a251100c2025440c01d41e00d00360742c0c0d600150904209544490040d4503017030014440c0400d0b0141140e9010b08184829200b429400d00e07030743d008001050700070105017071000105040d04492401080300f8082100c662000840c00581d0522500415041c0d8100615120750b0081d1001d10584913484200308400b503000900466004110500f41c10107218001c500300000d4a01c250300090031108c502245031700c501d1410503e080c101114502480c0d00000564422005101c1d0130004e4072201035030100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 730650539 1250 730649289 730649317
    0x1009061208032a031b070c0302060c0a060f020a1202180f0411040902030f0603070e0a1a0607050a051011042306030c0c060f010312080703020d02040f050a0b030c0f0906 74
    0x7450381d048503e0011403050001ca48415206003441205254910540b84081d246e440802000e1002d0f244c18401450703842d4070075088800081c2c683c0d40e10320a507414208030300d06050703012900307001d483c0c3c004100c001c181030902411403500c040c1c01c81401e900014180180d00030142026149800d480b81da02140c0724800f08a100c68443e5030f1107015001079801140e82c070b06601803650200c4c0f0181000100ca00c25545844c400c21525610440f1701c10061440021a49411102c2d03500860191248002443c44074016006800c80d1041424460720b894108510045074901d45081550361400e07800558007038900786880003039054a44440320640c1c007031070401310b03034004800018041044c008a00501401d03610b5015240184d64a100c0b4142668003440050014182c8001c403209481c403d400d0281c0c03048031800d0050030f11828007503200403a0096000b184542e85010001e114500e42040d00000034a09001050b00d9444e2107000e40b001c80c0942149400c004201042e810095940c03079003030744e120340f00c1c56034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 730651789 1250 730650539 730650601
    0x2100c020f0a200a060c0f020112110a08090714220c0504031401052203350a0603030c0b0a0902150306010e18061903060f0203100906120803 62
    0x144080f9075a100e03441d102c521207080c42c01000300e062185040c2d00304c0b202c0f070f11480300090aa443e022001d0041400485c1000f40c0c191a400400040e80b1904d141012048180e0352100c940d0400500010805400d2800550141c4c001b00504409031091050040c0251454200c070844140310701c80244491081c208024103041d142d4011aa02101400840c1d0050201c011b655115280ca5400c030351050f81c030060750715020a4081c010540301c1e1040403031544030f0324001504150070411494100b04a02c051000e0700d140e03800c28400d00e41c51150a54021907010310030004a031031641c002d8544183d4034401440324a128000906640c0c05512602106802a14528103076644812603152a401240c103d070100320307c070701000500e0404100c503041501c0664050816921008100107045500c04104109910150008000a1f00a00038440325200348180981c80303052211000350000e08903003001c0d255610b8500304011100710b25071059004c40e04080416541c2e00c9000c03003007004001e00c1481c03c140014040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 730653039 1250 730651789 730651793
    0x15021b100329190501020a0807140706050a020d0e0306010e07091a09040e0102090f0f040906020f0c0c0909060109020f160308010f05010507110616020d0c0501091502100c020f0a 78
    0x4001c0e01c15400c0203c8035402d4035056030401d44035840e220f005460050340141142c03000190420010030343c1d40c2c0a5a0108012101d405049103402041e41044000604c00300b490600b181d0100840720040803a4144101c402e41c904000c01c0d0b40701414412046a0705002c07011550300c501507401c2c032000c0c0c01c40b0721616042c4010f450603102c07150310140103103000d04e15010580b030f82c80c00117109852281c10b00a0540b0f200c480030f1010002c1761088401070f1a4401c1c5d039030032480f0000f0700b98401040344400646030b00c4d440d044500030340c50401075010304403401854480c1c2089800359002c071340079040d6a84580016110410344081c000103002d46030082d44070503d80c041c41802d258100e5541c60403680903c1070074030401c2d2200300444181c05010402070507650039403007603011445c00030041c2c00c520f00981e0301d20304c0e40e10450300040e80401c4021000d80f0b081c020310006100951340a0454000f6101b500f1661544040341c3c90001e42e140381c0220314580075680d51101010151081c890409110002021199200c55078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 730654289 1250 730653039 730653101
    0x21303080a0801170d0309140304091506050306060304030c0302070f0e0f090705030c06030615031905010503280c180605040f1505060304060f0507080115021b1003 72
    0x41c600300c07004103000030000075260404070348012400c928580940310308660880d0603000307040c1e490811200c2c490003c070b1010841c0c0c003c001800041100100c0441c1c50403024035081410800c940229081204c20010086281ca0b05011079400c50360610f44491080d00e142022402c0c44420f4103d245101c00c0e014002610f500041038a50154048030710207101901d40007040e0b81d44201900c03942da0950020b00303501155181c0000130396484403000c0c001e1000443c04200141c07890b80129441030071040c4070f100d00358080c00f0760701c140e9006d00740690007000501d040040c8500b9803200340c0c03c81d0310044803000c0749504004440c3c07015002072107a010014440c1c50707042440e030040c11450081d07030f02a519001d19200c291503940200808008003904200e6035a0800050001e2580020800e503544c0d0780303400c42e0044005051203100c0c492042076562100d03950400102c0c0c601420034240030803c55001400104407400050141c6120940440d9142500400000d0681c00b40248952041401c0400115549005c0309 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 730655539 1250 730654289 730654297
    0x31203050a050402010219110d0c0f121a06120f0709150f0b250804260601140315180f0d0e0618040c0201090311010c02061902130308 59
    0x1610140055540c480344802100c40444000e401a0b01c0320303060b076544c101e610790483e82017405a00010300145981c0003044100304a83d10440d62090050f07c10416440450584000380400b1031102c41000b0b400e445810304617001e0200c5001046510020030b2031a500d040d500380300c0185400645804403420702c986a22041c8905c01e1940803410620030103c007003240701a2106807000450074042035030401d81003011038dc000da554520520192120030459480207210120503c3c0300d4030b50259200d0400c90007000704108219000c070442545075091034005c0010807554155511140c80005546080c00041e140c075910085245020f203112045c000781e05100c2401c603886058200031111000b6040503a10340d910580308558000414040c070000c2507142c8140200409949012440d8211060a000030100e915941410b400741c0c1d51254014101508140c80c0295983e07840002c00241c0300c4414040e40720b40d07000309020300200c00007103c680300003803541c155a0500c41c0a40c500980d191245005031041e80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 730656789 1250 730655539 730655573
    0x280f0914070f0e04110a08060a0903030f02090609220e07090605010507030c06052a09010906050f0f0702120106170c040c090e10080616031805070303080405030c0703 73
    0x640100424880c2031125a84225001c0c400321060303503136890310703040c4054807024003041d48200c0090b0006480f003020000300d4010760180d080002d41c42514540034044540b6100318000c1d02d070050000c032195540710400c1d80c080d4181541c00001d81070076003a6604100a05d10344044000b0301e0000c038020385201c0011110180c99040e94100266900c540040d00c01d0701580700010005169040b1000000e03605801045e0008070060241c400c003904c5018004805045243c6643d40740c2020407055525030340544050010032003030406900d0305040805404203071240c55882c1c2640d10000510303508648485d10103403110300c071440080201544915030403220a21503c0045010f20904400803c00e00e03740c0700752000b800c0d10340c07a0040802c0c41c1c9400340507040d00c01030850700c80700d8103110006401282070120300d11400030011035200e200d4015030050125a040100007866814131104100060380009404c8140c139058282179480380e5640c40c00520750710422010844d10701070a4000400c0202040440581c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 730658039 1250 730656789 730656793
    0xb01090b1305060c0102040806070503240306150609100c0507091b0e010e0405010602070812071106070212030c1006050d050a171315110303280f0914 66
    0x580c0d5204101840c02036402050039126540020025854140d00030100800d00030009401d280c1d0b649101030a0a00844840000c074000100b00000714240e596804030b142d8488000902c83c1400f600441d60b20751004084000c04031907019090040d42d180000c2d42c465007030003071020145540d080401802445042030450b9980b00b04d02d00801c10041b42d001d14000c0348809800c000c1120309003c0c00325a085803000005050181c8085901010703202c2e0b000e128040c1803d0303001480428a4201c1252801c01c083d840c800380a4010f1100300b000806402e04c40c001c0d00350403155692130308500e00014000f00c0c80901c56003500e100002e00c50707d1001c00840c8080003e140403800300000790b626418841c1c03201a10400a1542d0040001c41c000500c12014920200c0441d090340750800c0c064010401c0d40c010aa0000e00700307003c40000c2041e041c0d9003e072051040c00c0060016504500304200400051640b14600d0040070042603002c45881c511a440200c0c4051070801c01c2c4040111401c00b214844492046400c0c1340c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 730659289 1250 730658039 730658057
    0x12210103051506030613080d06090207060b01021b1309030504080f0d0207170d03110c0d020a21140f0f0a0507050f011505060711031e0d0e09070c060b12010b01 70
    0x141c900400c5d101d2003100c280c205802443c40d0340d612809240d102c40f00d0401120355803d400728100701240f01508500788946000111000058006840d042c4145c41003400002c00202004480d1a0803420340600080ca050214403100c16103401d84560040303820840d2584603018004071601e40000d484204001d0503000d40d4501501c0b80040d0314140c141c45e41c07010444d801805142c07000382c4030782d01c41c0340d9061810317080a09003d015407000d41000680841c40d0011f90241403641d09008400325601c1d40ca054600070b440240320600000f9201d000380e44a650f1407a032021403078a0410f41117100b284c414142c95901c20799200702408014200360002007050382ca40c4550744444000390340520580c4a0f41d1820f00c0200d040c107107413404001190703125890880305c07605010150500c5440400c0b27911500300301503650a0380045482c003174a1134510740710511420410b480d500740b5240e8982542ca10f800005510f01510b600e011400d200014100c3c40001c19000341501c01306908001040d0700120000c0c0e405d81c0c440d111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 730660539 1250 730659289 730659301
    0x30a0f1208010501140d060b0a0f14030402090711010e0106151101090b011203030b060406021f0b01091701021204030807090f080709020922200c122101030515 70
    0xe912400d0140f140491030710b4809001d80341e032500c0502584034049401007074003600c80c01c0c900d1482e08080010341c00300381307884000c0110a8012200c4503040840000f0b2a003186401c0c0c00040c080b840280c400b506204607101e6201007818290003254003040094001e2103519a40e2404010405240392400c0c006110a509a041004113000c1c2c0010780b80c118052030380380d90030502c90050900b080720045050640c3c410090003580c841074054801804c4940140c1a100000c00710750402c00e00000145411ba481d01200c5103250380c100c045042030351940c000840c4028400c8691900a1182416002d0000070002c2000105580000b810340f0500e881d9851002c1d10740d45804070001d0180c00c4c020000310343c2010700140f2100078140e01420188000424409081c0407055221020444501807000d03c1910b0b00c4034108102868161600c0b80841103814500d0702c1074600a444e21648a14070a50318204001044d5058040d181d60b128444507416201071903c1d42d42c0d241465075641c0c2c1131030030340402940c4000205 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 730661789 1250 730660539 730660547
    0x1203030f01050111031b010e01051602100b041d0d0f020d0c08090d1506051c1a09070803040608180109080a080405011404031214070905150702030a0f12 67
    0x101400e40400034000503420600103441042c0c800c55102d070a48001d00030000d501000b912441454040400000344d50b00d07c4865850a40e4001041d0400303100408030a2a2981d40c0000e84600d144400ca0f40014010b03034220019010746102c201006d88a50344007000b4203600c0020a42c07034132340b17030981d01c6000034100b40307640a980b141d80300301643c2d0200d00d52584042c0803503129070003030440319030040c803421800e0919030f00e0f11058101c20b01004002035403280144042d0809a0680341d50079800a101000c0e43c140d0380c0c6070010b49140c092041e000c540d090380401d880c800e04001d0140a011558192615262518402045250119200705684526044400c000401841507915503034011344020b2034400c901005491001c0043c10444166603640c0c10f040c05040620452030240c0d121350344401e000034940c404081550405018554030a020109000c04590068125801c0368015224021004038a41c0502040e0040400281d09070058508442c1000f0200b500042407512034607074444031480c2888100c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 730663039 1250 730661789 730661791
    0x102100618051503030316080a1b0513080105070c110402040b0f0c070906030305030609090705090a1a06031503070b0313031119060501093204032c120303 68
    0x20140601e60402000700d009150041d591010100d100024440d0460340032901d11751007224030f0400b091150802d59000c41e03000100fa9081000100144940c148012246c0d54000c001c500003811700100007844e000740400c1c00944001040c01c000204101d2078041c801400884192800304c84054401ca500c80c00d6240034401c1c0c90a499001007000d00b400200d0711a00000c0c2d008401100b40c0740f042000001e1034000500920000e10300c6541c822307449007001810b1005c0c020020303000e01026002500c0c10321241d01c60b203071b00990200741a03801003869140080f124091915040381690030090000400c0b4402d081d5040d40141998184d0403078803003d0751420341a1603030000b900c4941421410715468404a4401c041070305543c0d9031002a111041410380f003003a0800741510b011524580c8800c0104803070500c45c0314814120002d0b000c0e0600c0e10620403280e282d0002044074801490000d036001c81c050610480d034018442004600000d070008010801000464480e0407031b40c8180c6101c400752105c40f602006803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 730664289 1250 730663039 730663049
    0x306030c120c041515020a021e010806061303210e180406150e1f050f0603012303060907030c0b040e0a0905100f0203100501080c030403140403020d1101021006 70
    0x1421072010942d0400c8007500f10260902c1494582190114070410a5091110090010b03001000c841100d4414800742e100d10f03045004128807010107041850340c0040c001039008500322040d6a8135114030185401505403500701800d10b4000358649a06807042c07019104407410645c5074400c42411040400155a4811800d0681c14410902150014001d60002000c01800c4011901040c0e1100074080d01c00754210341e1440782c07800c2035440d0b80c41116684511009482c06442800d1070119501c0819440d00c0180b162441841d000c00d407000c2c2014100944003003003580203080e6641410314141407980c80707440e404143d540304580000026001c00e110b088404403103451802281aa850044030380051290b11410b965a0246640d03405601140b0f104041000040d0400161030f800d00b41c00020704801d40e908040d060108010520142d101c401081e02d601a80c589481c000903040c0390f008500c02d019503803000750011030240e1907008001c0c0304107a842041d0020f0742103440c00c5d03c201e2002410740e002440340d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 730665539 1250 730664289 730664293
    0x510080f0319200307030e04180b060a0f060c05010c1e0302160506070908060603010c140d0e1218010c17070503040b04141002010c02070608040f15020306030c12 71
    0x30581480003020b50750316520481c00c100d841e01002c48928140300b81d0b801c181a500390000100701c0209500720b0814052a9801d481c10061196030211090310410f500700084c10707010001c07001030059501c03803a900000d01265001511072994540c0c0c09008d40014040843d000e500b080350002156124507a50f94240c4071118114031b5200880d00180c00070361290304d050000400d4000c1c24004980200400c5002e40c02540e68407030030380d00d080e03410390a010010701918401e9040c05580c41e940b40c1e1001e982c8002c4d201da030744007654440700c101741100209040c0d004105140142c81400e21041d2408010f070082e00c0d100380b0710340c500c070951100444681e100180002c10700e52164480302410318900001d0b2800781e1141c01180e1905444514054250b006503015100241d14031a40040c1c90078200c6184605000300d000034800e100e01d501019440e0071300e600500303040000400000c1e040c0800d114132012010740282c40c91000d5a04000c80d40c000c0d50049904901038070503800c0c66031580c1019408003054402640c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 730666789 1250 730665539 730665547
    0x3030f230c0a060c020d030c03021201170304030f050105040b01140306010611030c01050c0705072709031719111303060c0509030d030606020723150f0406030510080f03 74
    0x88a24160080020750400b441454010400038590348a065840b50445d0001e00fa16400d8820003010750310106043c00400d4014084842c290031001003007410344201d8031000b0a03c49204800e98558060b50b84041c0c00c00300700074031400c203205040d806180154026030002c0056a01c50003280c891184056500c0c0e010350060380100410381c440c120344131840191001783c900c0c100340011803500355039066410b22200c00c4002060020414200700880061580340381c3d104806102d14449546031680d24105034038140c075603004004251041c0c0d50000008200d0400e0700071402c01d0096a10303040400b440b180c0d02681b0300880e008004071504217444040e01c81c0c000200b45541583d41e40d4001d03000c0d01c003951051203030500903da05036030188034041c08205166070015459107010002840d0050542c02841d00f40500c14550804200c0c07071070010b8000000b0358164401c100d240d6100301c520311808010070090708000c00d011551590641115016407203451950301e0142d00c4040540d2191000c1815041e0ba1348104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 730668039 1250 730666789 730666847
    0xa050c0f090f0a090e060a060e010509190b0a060c0203011103011a16120206070206060625110a0b09041109030d0c15050a0222150e041806050103030f 66
    0x102d002a500c040180240b2080d555820603a0103a8200c40803a1003d50000b000300302c0031003407030b1240700c00900c0b400c19900065403400004c2510071401074002600e03041100031040c0400c145422000380000050202c900e06a03460200405ea02c03940c40c42240f095081400300c00751201800c058034181c0308610400b80030b40514400010301c952207442c4c0000305a000286400c0030545803c0d4141e0001c5103600504100d1410240080c1440001401c10344074080a020459079407a10703d8030505e4403034140c0c6044104085908094904c5401c84074900e520826180c80810440c17a048090501c051041c1d0b014005922200810041c40c0560035003990182d00804032800380038801ca004401080c0219a40d0f5800102c1d5101e1100761841110344140d0076800113800711701e604841906400084c00040e49003d400d0518078220514a80104408104640020f401180e07903180e80c00325500351000c250305181010545820f0014000910040d07011650a04021440038002c0f0600e454400c0801603d0202c50040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 730669289 1250 730668039 730668049
    0x9030317240a150201140a050c0405040c050c070311100c3305101a0a0206010315060909121709030a081302040207030e0a0501050708030609090a0b0106080a050c0f09 73
    0x440e4116840307480c000d000902c01800d503c2c0c004841d0916400420002a50505560815400782008000e2480c00e001c2010b900306030800d640030b4078001c403400301d2010306602c0115524001e412503203559000f070740000810003d0409418081c40410358280c0850948500190b8864180c0400a00301d0902c80004a4461903240d921040b030b6a07809403034a2828010078060700485404072039001c120090000f041c05520b0002c000d04102c0b00003e440c00c0e04e00b84070448000c6d180c50041c400140012413101c0040d661884940103000541000442042512554140f491110b004400600c02080802d814441034445035801c940c403640764640110700e072a00204046494500041c514881d8078008050540140c1e00c9000421078980a80c0d0341011410901d010000c1c120b45651000d41803010412800c40015801415654022002c541742e0010b42c3d61820317050b0030814845c900400c02007010002140c0180c000074000d0103116a041d0810040d45ea01d102c001940c4a0003a00f115411018441c020203032a00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 730670539 1250 730669289 730669351
    0xc04050f100c1209030c050616061a030d021c0203040501021902150c0d030c03022a0f0601031202010501140a05090601031d2404020108062e09030317 66
    0x140c1d00c0c0251120000d030310740f818442034081102001032003124040040c00b5032540358002420b811038905140940000313414000c00b0001e00001e0049407580d01e0380c0c044440380390500b02c1b42840502561030950222000035240c4050703481106031030318040c0c01e19100c03601c0001078a05540c012303002001611054282c43c81c0700e0b040d2000890380500302c0301c40489080d00041c0a0f28200700240000d10700102c0e0802c9c040c069840700b040c0041010f00c10711107003c1c4220303402581e041c48020107000902c000c2142ca626030414116101c0e04400303218100000041160003900380d040e207807032640200556600c0e00c0c0ca44404071141280b0f5603024055000c144910300d08a614190071480505000803284e40d120761003001d2034916205001c1c99004180b101010f6001070fa90391003802c0c01051035943c03030301c0d0903400680041d40113171800f0b0003031810000102003180800081114000141c00004050944140003041c004540c04100c000401c0c0c05034000c3e080181c1d40d051030095690006040c0d103010803141c1d2500b0030503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 730671789 1250 730670539 730670569
    0x20a080c130c091e050a0f0e130305040b0a09091406011d0303030c0d0209040e071d09030f0a050c0118030f031a0f030109080403060f0b060a08070302070602070b090d02060c04050f 79
    0x844c111000656640d04072101006207903406000303814070b1400c02d4484200d04018940341c00c1c0644041d00303900080d480011030381610010224151a6503a1080850350350038560849056980b800400b031080c00551012076100c0c1809a075040c00d5182100c4502110f032000105090b0142d0050012819a810301d501038039610031061001801c00c1c000900280a440c810740b040000c54214400500140d25495016085501c03c1c208142c03044c00e200700c14a039a440344c9018481e4160002c508100740c14412400c941c3c06038074850090150400e1140c1a960080d0365102c01c40118809444410b002d13030081c000d0007040310842003030f103031800141d105101800c1d00381e150f841e506550758003090000a8040000d40061401410001940c2d00c900c0407041c11100603012641c400c444c1401490f509070f502690302c5034044d11519001d80c540405140001c043e0094420091081c0c1c4440e04000000100040159100880758200e85064440c005100040d1142d80940c94111003042040019801d01c5541d940303103a1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 730673039 1250 730671789 730671839
    0x40602101808030703050103061802011205040c0b1b0114040503070308041b0b1b0708030f2115100f0c02060318030c0d09050f1318020a080c130c09 65
    0x48050742e580841d54000c58400340400d5490006006011241c412a1a00030b00303000d00355801c0c401c40d00060001040a00e4420710030b62201c00080030841d555542d0401452003019050b01d030358006030b400300c0b800c0c800600b40c02c40b9031070300700244c800c2171204030311030300690300310014629004494408488600000b0401c0e5800c12041103849046804000c3c06802401c0500002c0d480e2150002541480400c4081d1540c13180d1001c0000c1c0004500801180e0440d0801d4610590302c1e41040038510099021a111214941c0c0c44020860800d42c1018040701010040703d0405002071404000e03603a110754502c0020000740406c00c28001400d041d40203542100000c0000442a0004400c092869020149000c0140c00c82c071040107449420108100140608507051683c4d07413111004142012040710320740c4c0302e103034840045c0c1e44c16079400c0c110141456005005440d8060721410060382d031701410380816000b40d076a092680398001c024440c1a8192007076a1340d14400310310302480c00003a41c0d1010040520305c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 730674289 1250 730673039 730673081
    0x40c091a032a0a0617071e0302071101030501030b0115050f040306060612021c1d2e0506060702060906121905010801020c0d18050603040b0907050604060210 69
    0xa981c1000b01401c03240c080b1540c1c0c580045840c841c20000909080c10340e0080390401001d2241c20b4001400d40100f1702a17a40600840c1d544000444048500725013202e080801809100103160703243d0000d1080740d02903540c800b507000c0c403c801101100d40034800948200381a900600c0740c040100002041e00c542403a041c1e0521a0400300896580e216070700440714155140310030040c00b40c001d40e6079200c010048504505004011045403424400a9600c1d400c2c00c0c0c0e00d503001d40d000000703a2805d000e070a00a50894881d0240000188070001c8039101a190207006942c0f4405070300030b140511403060360042e0003103013405065400d01501e0741040c04130b56070095042c00104540ca044000041c483c10203840849503070105000818121740d0180c001c1070302c42e40100b208041006000440c1c90000c0e1003881c02d085030710342d07500ca0700204486075000300e503001d80e0000500c004c0c052258001402402600d0946000781d41c0e40040000c44d1146109010242e0054031590b006006035502c410100b00450907410f0030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 730675539 1250 730674289 730674341
    0x5031308030910110c1b01050f03040506090f160312030e030705030d050f06010c1101110f0714010c021503090c040903080a0c080c0706020309070801181a040c09 71
    0x10307001240c9019069003e808481104200e500601204410200d4420300d80205c02c000c058881c1c40807481e0803141e413861960202c2d82c1c0d101e4003c0f40d040d1042106400d03221308040c50280d0b25840306403848220380c410145c00c1040c00901180031a0b2500458104d2851186544c3d60324221000700e084140906030b8540002010403401d2000780070492240c2c002c0c1da502d40d89180b2107000c444010306a01505941c0c0410401143d070807011076092650031218004840229400489805188a8404486024002c48281d51800014500c2c3c103440f20015240c1c5040150401111120303145840a0741c4000180b48462440322064021a00008038000790f500102025020400303a81c010b0340114001201901001a031000740e2041030816142c1d4602007400b4200034454100ca0700500801070f1810b6070000c081075511008211003802040c90388001d1000340f2584080c44042c545c090003d0f03070700d45070721428075650004840342d00d485254000001d850107420034440d50003c01241802c005025442c3d0030001d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 730676789 1250 730675539 730675553
    0xc080702030d0f062c070507120804230f1c080705070f0f080901030b04050906160203041d09060705090d062f0409110712030c090f030309030b0114030d050313 70
    0x11191406609801c8850070b01c90002d002140046c0484204001445128005a030206200012001034540702c40303240c0f5181481801c2d0f030700e41200c10303034248610080044640c4000c901d5182c440c50745415903044802c2c007401304070b4400d1031400c0200040d9903440007500d4280182d01810100d401242c680c20300c141c4d91f0b82c1d030541d02c003854a01568a41c01c00b24624646683c50f01554580c100296001d00003800c000c4281583d0f050041e013092101d54200101454580c400c2040c1d500624420360441c002c0d8603505003070400d111085e221102180507500001c0c28480c02181210002400a4429544040c0303a880b220000d10701450346812103841150481a00d00414080c107281e000b00b40c081a60302c5142204440c1181c0b039070b6140c250000424030010003c154881509001c442d01802e0200c1c000c071001c13500301c034030b45543d030001c500c6410003807008000d141e0320101c0101036902c50a6035100360398076034201209900348003001d640e065210b20145030040d031091001d0f54211010001d0780300d43d08850b550b805 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 730678039 1250 730676789 730676819
    0x140a1a25050102070515060d050703081803030316030c0503040f0f14030d0c02072106020d060509011401120e0a030f030b120115050405060117070e090a0b040c080702030d0f06 77
    0x40c0d00740d0f02014000800c40d070b1b4120703496003040302115503d10404107950794a864002901c405085a02d01082000d4080781d00061301807100401000e90b80d80345800071414169031140c45400000a203000711046415026004985c020380e0408010740364981680c0d103010710803041c18002c890040e402c00e0100d400002c20809031241c040c0d100008204103a25650091809400d903100ba145400210340080100079401001001d49400c4100507a68040031400132000d826907900031900074044200000361186030340d5104110304801d9072540707506080b8521183c29600000d010580c0d42e04031207480000280980302190b4601032904011498048420005a031181c445c442c1001e03694440e05000040c00110340c1c8140900000c54041155061100c0002d00c540c1c02c0ba41c0101c40825440c1c04684240d0003004901c2d5178010042c0640034034036008007504050000000c085010742d0812042142690180714010300c1061203030700031803c0802d00511040508500c3d05454192503a990000c110f10701d01101765 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 730679289 1250 730678039 730678043
    0xb0d1401091b02060c09090a09050d2601031707050f0618010f0e19060b1017060f09161404151101060312050c030d06140a1a2505010207 60
    0x35407044039888030084900034640b0380c2c045401ca10104002c800042d000d44040c00c406642c0c1c569142e9500141c1401044148005801c070b215140c007a00c042e6a100340e245a407090521214030604c1d41c82e402c5001c038201d0a0000410302c3e50500481384001115601420f1024040d8044400352000a9080c0b4180b4000b61141c0d0a080380569202c00449024051000501148041044211701c46400f194442c485240703132800440110380548140040c0345c20103d81001c1c01841c100001c03c490300c001e0141e41ca03032000003080c072041c4000110b04e4074000074100309950700030300209210740e00c00c0001842034500200040c240b008450030030000c0407801c0041c1c000340118400080e005680c03075070050858900030b0100e0000b603041c9801032000075030811210344602c1c803504140c0d4441c440e00b0041e40c1903019007040c40f414149044000223a405440d216131180910039985079113025103409065044242490811480040070400d40a4184912610152501004103905500401030351410300303a078007200702 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 730680539 1250 730679289 730679291
    0x130b13110c01240e06010908010507020c18070c060f0207050f0a02030c0306040f12031d07090506030a0b0c030c09030a0309081b030d08060a050a0605070c1e0b0d140109 74
    0x4210740001c00344640c1c0c4041c50b5803980c00c2d4030790506901c218031549941c080c6189100c0a40702003045a4007030413642c0d02500c0010003c0c0903d2610520080d0344034994018144075804052001c408003001e6040e1034000d9026907070761f120514007070b1140c00c0a0056488013030710310740e400c01c0b01e1404142c05210030300440c0300c1100501400d41c00c90041510305026242540c0c402d801440c244000101c06818400680c1d61112a0000b82000c81509400400e10060000c081079518003420300d808802081c4402641c4100004000c20b0300c41c6030a1599440c3c0701c10380100394401440104650140383d9014503072000c0402c403440d00c1e200c402c0020904152103c0001c801080101c00c0a010300c0209016507403120a5622212001c1c90807180020396405050031a6414810035101150301038440c00d2280001d40400340240620365511000100603a00480701910f04c94031a03c2e021032545000b060b9211480300054040e04c1c42c50603c400344103e98401c0222852059444c00503609001d00162824001d241c0c07550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 730681789 1250 730680539 730680547
    0x40f0803030414150f090a0611090a0807060e01032a1d0102060403270e180105090a080418020d05130b060108070f140906040e01080706020309130b1311 67
    0x1070a0850301c2c2060143d000b003500001e52004442c100300d0f1200c1e902500c0407810303090a4440910003400e00d000a4405495030f42403401e0034410755240e10003016000703010b9035940e024581c0c074100310351207000740d000b6280000c04204000556611a0300a0200c441e6011844001c42d8049002001e0544440603840045000d110b1a1100d81078540d9940320405020b00140c0301134642958018403408904000a101c42c40208202c030001c031780d00c043d00d405040191801d0480c0d0405252480030200748900c00001c541c205030000341c0340c03078021401c0241182d0040b51181010f081c42d00354000d800d41012074281043d4240418009916107000789801030f0f0a5030444801203015040c00c60104400070310041c14803040105101c00309a200c024036003c4040d51800c0c13503801c81d0764050b4403814420000c1d680e6119070007040c0819000d5035164101c2c121071400044548441e681c1d041070340c0740d01942c0c060390303840302c09450019a4071000790884038510000030085200c4a018180a4084804e069440c40e0046004a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 730683039 1250 730681789 730681793
    0x1080c0a09020c0309120a06050f160e0604050907020f010504060218010f140d090204020711030706020f060c0913090f0203060c0403020a12021f031a040903021c05040f08030304 78
    0x28003a018000d201d800358502503001030346558070b100d20854203000c0d602220761810050400d000c9030199a60100c018411810401e81c0303501a45400e507100c100e6402c155044c1c038002401008450b2038200064400e82c1481e03c1c2400b04001464024005801e500a20b03403020001c1c0300a1080a00c40c82c855080140c4403100c41103402040721868070400e06210300c2034030700141d25030024249448d91001c0c88100ea61200511040c2015003894030009401a0000c0b882e00e0400c00c0d07100200400b800290110786000d981c07030004aa458090390300382051a023091000c501c410318810000c01c0781c0d2002038507452590b80c03901c80c10811074000c1c1e4015070f881e071071040310001145028440190490701841050f420142140c000400300090780c800d03040b50045280c40282151551003174036504400b001c0103000300301c040d4400580a800c50503070590401112071030182a510f0a40306450b01c443c0c160307006040d214004c000b510007084004908106200b014480090700f8003030302c02810042e08803640996140c0c140340c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 730684289 1250 730683039 730683049
    0x201060b0c1b01020118081207140f07020316030b0f0108071d0402030a06020304080301031a0c0304030f0903060218130c050901140408120307080a050412050706060e01080c 76
    0x1600031859041041004451029000801d03065203a01040001007072052900140c3c010400c1500380304d0b040c1000ca00540c103200d000c2014240072007000031038044a0b540d41804523030780d43e5801c048403000c0f0030502c1500303100c90b582c0029100d25440641107034038500191034880c0180f8100c0d0f001700c45180b0781c80c0030800000070580050340101030200042520f1400e10359180f1800000b417825804080c1c12000117070940da01045260301954010504541e03a040a05084007164000d0009a94150255072499281c03180b40b50702e61300c02c130040c051040c25501c0f02d50301220304124801d01e010400525141c04408604144020012000d1010543c00b160810702d09001c80c0b82400525083d000e07207003600701440b01c0c1e00841100c0f0211424607054114400e03042000100d405260403080140c40303098911250314400000545c000d41858480c0303a125503882e0031101c01c0d210112001001c0c010080c610510b6903000384043c004c000c1c440d03030010a18070b8540581d041d80c080300341d11140e40b90380160345200c914142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 730685539 1250 730684289 730684301
    0x2010215010b030c0a0207050d081908070e0f060c060903031006050316032a020604060b092404020906121602030712050f040315060303091e0b0729070201 68
    0xc109036051240d8034190328103405000041c520700c52000000703100d0a89520034081e05026090046c1099503104041c1844001600880303d6401c00114181a442c400346c019040782c2c0c0b2414688d42d600140c0e64000d42032089111116140b50703046a002d03c103a00e00c0080602c80b2031320916949000395101d10f0200f00e03500d42042c0983c014810b00204000780003030750042100ca141490043e04012480907482c08214190440180301201940c120f460107855480c0c0c041821401280200000c2c400006078408014101c030301900d00071104150001070310001140c40c440b085417010b00400c0181070500780004940d0300e5220300d2031000b80d0b802c1501000f00b4920280d200000c144101d100841c1081070a940d004c101e08070001490302030100c0420809042d68400c0100c030090366004540660100382c09000e540030f4107907030100f2404266040400b090040f444c80210144c3d030421401129101d25000081205511160090340e01c403070f024050080004001d07070045404043c88140e25060f00d0940343c02400c4a00c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 730686789 1250 730685539 730685563
    0x70c0302031f051e18070e0a0f05070f0c030f020120120a0509070603050c040323010501050613050d020402090406082404020a0510020f0706020a1103070b030f04060b061204020102 79
    0x210644c100980102e190075016800400e507400c0c0801c1c01ca0282207149000303106e0b1b2000f002c00c520082003001e103041c150441c440807980c0325014400c98032008019101d41c01c03e8485140014107000c060000f2070701c504000017001c0700c54000041c402a0341e42c00710800031400014804c14590014503082882c0180001c40d5002c0041c1c1c0c2c040025052814816480302000d01c556010581c91f100419900003441084074025039000320000602d03460400710171424000740c144503105501e88800007499017065421110802840c50506c4403940c02d003020001c3c440c1c801e002c00e036049542446050b1641e00c503803003500041c0c0000c20042c81c508038020343c6001b5905183c01d1082596401c0d9083c0001600c8500c41142654800c55443e40707414030450049243c400302e54a00c00c407611612400080079034010070b040005600403d0303c031882144071024555070307641d548913440f0766200c1000000d04d122803058135550403c4c0708010101d89040c00c0c50014203680c20807000c20842d21290700a000440d030301003010748030301701c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 730688039 1250 730686789 730686811
    0x20030c070506090a0e070324080c09091c1202120108071e03060506010215101a0301030c0902071704031b1401090302060a2708011d0304060302070c0302031f05 70
    0xb40b101007482c882980c1305d000e44c200041400700368030601030f0300106400718140151010f105812440280740307880920032010035019011a000980c01c3c0f4090701e40c0b007245203a004101000b070158840600c2c1417002d0045040084c11400355a068015000801500d240640c202605504000d12542020410b5001c2851099680c0c1c94003503905040d542c0e54200d079009640000c01e1307560340780141d0030460499010341016a10504200c09500030221481c20340e0403d110012190701101c4c81440f4603c0280405480d540ca41801003180c0e2500d90010030455100350440040c02e00722240c8081103820980040b11810040b4001444030001a0500b000400070807000d10410148170740041e114040c1c6002c06409843c001690801d5075000d4640401581800401d5004500350340600403100c20650051071525401c101c4108294200a503a040c2e080020801940c80c2520300300702036000b940444411168015003200000140c2c0d41482010381510f0000c10a006200080000104070b900081804c0014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 730689289 1250 730688039 730688047
    0xa020c0109061706011719111c05090309060301030507150c0201050d05040311030409060e06091014010903080f0304060b10020d031e0c020a03090504050f06090720030c070506 77
    0x100c0d6200156080126040c5480d0304151200740049800e0480c41a02d100d091410746c0c01d000158042503003c08020b20040420000303140e2340000102c01d031141a00920780082486041c2100c1061a808540c0010103402140d10f49000040481c0350364101360310959254200410070061400f4140750401d03900c10610b40607071f0291a0340c0c006030141c0100749444047c503036200300050805014080800315100c0c00700469403103035540c900000c003400c0d00340110601c1e240170740085100b80c00c0c40c0c00700501518418545210140c14a24480f085454144050707041003034010000000c41d07070503401405080e1060a00c2c0b44d4902d400c0c01c2c40c0c0155010705031014029001c2c003080c860800da0101d400c0b5500d0320240341c0881c1d11203003201e101e03040258210310b00c003800380781c80e07141c2500079000036008007128400d464402c115590341003000f080f110100ca02450703039003045000506910340403110991003441c03801c2542d041c401c0e40307000f4012421081010fa059500006a491348600e080141303c00508003140d0079494 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 730690539 1250 730689289 730689299
    0x209031f06060203041815030507080c1e060a0c150204060f021c050d0c02150a1d0d020303060d082b06090b03030901030209031f060509090604050d0e0312070501020a020c0109 77
    0x456200d04080001b010f0b92210032000d200e001e60303d944015034114003124441516284001d448580b8241068032980b181d5504811098842c00c0b901d0811000030070039820002000f0060b140b400b41c0200858481119182e88007003c01b0340c0c4040c10150a569940c0b42c5a05403080c0042c0c940400c1d0419280d05460b01052201c0e0b881c2d01c4400c80c2c0b022095070202140342c0c0b45600d026854070070349000201141030994200000502142d11441849607003100700c00c0c2c02504650302c1606d4150381007101005800070400250b050800755680004c2c036126a41652401e40210b2800580600b8102c007461a21114189031181a5082c05008040c100c100c1c1e0420056601c0400203641388103c6040c1030505030007061005d500d43d824000e980000c11402220f036111230030a0140c200414003402158442d4881d500481c039407040000d400c0f4400c0c2d03482402420010b00c2000181c4280f602c49036a203900d4801d0790040c0450341c4548029021951146001503100e520000019041c507417001d804504110100b001040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 730691789 1250 730690539 730690559
    0x5010902090a090c0c0609061505060f0304080702011e030b090a18260d02130e070c061a0d0614070e09010e0703020d0504050a020f03030f09040e010209031f0606020304 74
    0x4215008000700040e4511480425242005c4402c03001d403045281180303030000e00c034407a00000b14125010a00e4a90280ca030010001c0c1d80c05580e0054000c2101400001c00042000d801000a40c0c014103101200b1980700003c0c1c8501070303000464100298817043da00c00b05003001541d064020b00702076400d20600f884111386000c0c00e1100e80014043d1400200081800210a00080168540152342a58031052110081e020b0350108000c410860394500000500201d03164040740514815a5a000e0610306a02d640f0085c01c9190103070110750740481c0607412184d61341c4501000d614400c84010682590400603d40010703001421a824400c1550400c0f440781c0e5001c1d000d81c19909490b114112039103450800714024029210b60103012440c040610091020014140300c409200f1aa104428030f09201030503203030701441c002d5800b62942480888010703d00707900b02480ca0f072801e000040c1029090400a445c007002130000200030788180b0680160410a40129000713003207240010b6141900c0c200c4500c0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 730693039 1250 730691789 730691809
    0x819020f0c010f05090a41190b010b0702040e0f070906080703030206011a0415050c011b120f0b1c0c231c0b1f080a020619020a0609060501090501090209 67
    0x40180005030b01c517140413111a5480c6e030700c4045011f1059108041900144005207040041c80305c18401d0f0120915040300882d00a040c0c2640802405950391070801d072001d140d00300d4901268031a880303d115507010034007006224451b10200e0024800d040ca8070011004540240c2c03c0040e0304d800218003030007c0380d00019034a0440324078013000c12915192044042041c0a01c1c1c12001220460380300c0c0e0310000b0303407100251541803151030007009001c04071959100003030350070b021203000f041506203c00c072101e00ca40c0c091015140e401030b001c03039105407803800105070703003480b1045c141c6104610011348280079000c40c40c10041d045141c074200d14050343c020b403043c0409401500610031009400015999508482114a401d0b84800701001c1c80c00c00901d060b41c404400b5401450941d040e00c40022001070001d10f65664680140030289892080c101851800380014807400951081d058044001507041c8110038225000e460001403070f5050803007013820340740180d02440c42c580c0148400b2020740e585075048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 730694289 1250 730693039 730693043
    0x31b2d0f120e04020f0f13090c052104031706030a05100f0e030307170c040e090a0501051f1a0c19020f040614040f0b0d05010e1204060804030819020f0c010f05090a 72
    0x55030300c8021f0b1000c801d5000815401c0400058108a095188140c121000d0b12801c0840d01c1c40d501c854480c88901c8200c44401c441c043c0019810541250001010102064210001130183c1c2c5019001d07485642c40c107003c92000340401030303844000c804421000e1280001e00e0701864061403079800e2008000344030f24035a0b801602404128000320342c20540b100c0480b8000c1c00c4800c1c0c07405851406448540d1504a40d0105645079420700b000102210084807a200103880c00c00501d0780180d00b450700c201c0c0384c07940313591000382541800c00141964610421514542e00e1031070b64140c1c42d0a40030b10510400c280301403503060003141400020310210752842810a01044152070000b404110b110407080640550800103070002110151901440f0b0190021048040880102c030703803008110a92440c0b0b84240c3c417624000403055804200000e128000c1c1e5504882e50700c0d50b1041c505510000041282e0205440401d44200090b1006403200e0078007840c54000309259081086103003454585450322500040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 730695539 1250 730694289 730694317
    0x6030a030f030e2a1e030706120b03120a0915050703030b04062303120306030c01080703090203060115030e010902132313031b2d0f120e04020f 63
    0x8155030501d010040001c5000310003281503940f134408038501280f034983c130000d03900500c4e80729401400d4161040d268490344101800a040f5580b0f04072080b92513500c0c00ca1003108064a030302100740541c0d4104018141036615241199803038040030b201401c1844164055641d2440152032454402d4001050310417039501800d010030070410ba140014002c1c1060342007201d940c414081f42120248440d480038843c03180030740482daa1440d84e40791108003804129074050340b55000000e60324282d4490450270760440c009040201e2030340d911740d0001c1d0400500742c012818060f409003001c0e043c507506005148400011000030040d0340072640228060003600781020850070340f40c401c904801050302e00828400c10003480059083d0800610310350b1001c42201d000e400046000504070100c641c3c0e60000d07511785a101b8440940c007034102c11103e5000302030400350280848103842d000c010403c00d41070550258030540c44400c01010220014080300341503031003540106e1040c481e041e260a5140c0845900b0044900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 730696789 1250 730695539 730695551
    0x106020708151312021c02030a140f0f160c0801020d1b1e09080303090c01021c0519141602031204030f080d020708120f070503060d120e060a080f06030a030f03 70
    0x10085e4507040d107203010310340b40c602e4014404c1d2040380d000c80501842c1450340d4840e4480f03050f14030348440a0181400c4410300b10020042c0702050303903104000301451410302c00c843c1205003150b1100c8850060715405030304180d4000601054084683c421001011042034400814820340b4400030300200121074517650034145140720481c05030041c0090401042c07a482101e5076840c2c030040858440000710300701d50242c4250751604d280050f8401c402d200e1190195115801c0c50700c001100080d407031485c80800280300c440080d02010100c520700404440c040030f100401110480d105152078251078850042815034144070500c00154004495419035400c000c12035102d03500e10340007200903c40d800004001103070001c1c1ca1004040c03540308491040288510110240d5503985044c1c0c0c081c40b049400c241c2c0700c0d100302c1c4840b0000e0449981c000c0981c86a1078204a4500c5850210f1110b0340031745500d4001c506803904001d00307038071029219640000164041d1103011542d58001d482da00e4052903150615403941 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 730698039 1250 730696789 730696823
    0x516020a06110c0d23160f081606151a0a030b0f030d090815010521100f0603060f0c08061027170c2d040501060207081513 54
    0x1406940e4224105800c0e680e1304120001c2c068020f41c4a2410710180800344107005001c00444810b4408200304440310880030b08142d0f503120340300c2503c090b08540e045002c0c0b188661203404000b503a20550f05ca0040028042d841c4551005081c159502420800703462442200c20300512070140e07941d2103828180030401d4034034070300020000114007030141e815100328500498115442083e48044070b4541c41510b503034211000740ea0043d10424050749421071300722107011054403250100c10a14129840a880c2d1185038402140d054074401009410342c143c81d50f409105101d420300c01c1e0380c0d841c145140b0410090300c06c410083c0019100074802481240c0420300c03030b80014050b034417a040c040b042010080301c1a07481c0e90408004040f6016a841010407181f0042d0740c8000082e04481081c4010444039128010080c05024103134071814100844980402482040c5c6990060078040e087c40c3e00505403203420290218a4010307004101c01c600c2c100c0d60248480d600c0072580400425070012070150a0013140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 730699289 1250 730698039 730698071
    0x3090b07050c120307031d060301030b0703020d0e030c2e23040501020a03051e16090513050604110f04030204020d021c0603120903030509040506040b030a060b040516020a06 76
    0x840d4000d8220303081c1c84601c041203e0100081c002c1602c40e40303400c0070758115010382c40301030a9070281c146c0d0041020030050001c580c00d00c2c6540d078032090502d00545001e002800c004d0940310840b8000341554030208160401c00c0050200050707800c000c07c2001d800d858045440c0010fa03c010014405103941ca1802c51051426064850020f124460080f8801d00300703890300c18001d40c803508a4a0019181c40e002c07070014180c4140d0400244890290818940c45500041405480d500500402e004507004001083d80b2240440180309160000000355072807c1010701060782c005140511000f41c00300207000340059000e05640641c0c0d01a50016220803003100d1000080c0b182c8403522380c04400c1c41408500d070b6601c940012040d40e00c5002c1c48000e102c82c1c0c0109030b03020703446400001c020650901c40e65155040030303444154070240040c0082600c541c00000700b81401005041510510303110107480c280e42c1868042d498006002241248004185d004029110800c10340300500c0031f500c0d17642c5c0d4100c507000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 730700539 1250 730699289 730699303
    0x412020c0906131b050301090f05150f031c12140105030a1b170c041a062b0e0d09080307120c110301020316170106080c0a051c021c060303090b0705 65
    0xc020f6070b501c40c0031074041c0080c05e03a400900c11007428030705000e8043ca00c0d61203801914010300d0524040429071000404005c83c1c924118a5607030140710b10b501246c1d02520021380c00858078401d84400c05514500c00030071040d1201c100c000c680b00c1080c0b600400141e100020320310740094004251032a8400c0216951690a00e10342c45046180314440d0094040700c1c0118603440b0302e80041301c003041002081100100c003072403403522595204205012000848036080c2c407404148404504d00c1010030789036284141140c0000440d481c0072f42c0640303000000300342c1103c60a0040d00e61080114202030080c0e4810804a00103a600c05c10002001c0d40300081080313050710009071210080c0250744034071b8402014090517400409200001d80010000d00c0300e81c10440c612410b030b070400e54030310083d50f4409641c001079a20014441c000c0040401602000c08002c1a251502008561002da901e0b10031300781003949100034003000200146465020400640c200102c03030100e0b03c0b454030725500c4000d0ad080450034404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 730701789 1250 730700539 730700561
    0x3011b0f2706080406020f0d1434020a080a03020c06012108090d020a2d0e0103031407061517010c0930060507030e030a080402060906041502060412020c090613 70
    0x40707200303070423034065422880b030301d0500d000385c2402135850404290596134450896100b0381440d102010300d660043d44005074a017054011511140710641d18041c05034852007003d0006580440c0b6189603403404e2040301e004003500754555203290203e10240d0146124540001d260760800103e030405174030f034003514513603070303074004018002c1d00390341c0c0e4450842c01500841a1184035120110480c20350403034841d8905a4091002c0b00c415a800e40c0e030140c4981c251880406519135007449564001803071406420704d807a80003118010320624100750a004c421301b00b0031985050341058601d5111641c040b44000c100c84101700160207507030504200d0b4102005030380d0b481c00014071840a0070103011003600300c0b41c021100f998003004824a07000000c0d89a016035400e610000d4540c02c0800c0251a045000d4407100744010300c41d600d41540c0340c1500348100b484203c0381c03000d0b0f003029003000240030041d11402c09022260002d00000315250000480c94100108280c0c4100d14102c460508202c0940c4485041d02d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 730703039 1250 730701789 730701817
    0x30901080402040b27071404090c020705120109050c0d0b0f070e0d081902011803030209060d0f1a1c0f0c030c0f0812120f0603011b0f270608040602 65
    0x8028040404100c09004040241c00180001061b03c96104801958442185005803400c1034180b00392100070b40840c51150045201c0c003040420503642c2d00c1c0b09000f04076941e0f0700004641410f8a4198288803541c1c03126072040c5d030401014030104043c0e840c1291320645a501d20b0721283c0d140315041d140905400400c030f40209030b506200e800c000c0e0741c40060600402000c8e54002804080070101c1c00d072030280148410100b1034080f03150000340250091b00300d400d4001c00d0103061100d41a400707002c03900c000400285807134407140a45900f5024040411052a09031b440980114034009c0c54a104000604003d00100d1088081424802168041809942d10409010000d960380e0303400d8a00310300c0c0703002e11800c40c0185c03503010700406480401c80303012180102800c42683c1d01c2c038070350341c0a0b5200104a907415540b40d28924450103d040351041c4011480d0b01c928608840054009080810600708182e40f91000c890a5200120144a090843e045441d103803e5a561320714203440680070b0b0405403001e20f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 730704289 1250 730703039 730703059
    0x1120f0f050c070308061005190903051b100305060625050102070308090708030a0f270315061406031605040905070c060f05070806060a031413051c02030901080402040b 74
    0x114542d01c00500840d80280c2c1c40020f980c0701c1c5000c025061403d05594070108104200c00700c05138000401e00b41104445043c12040076541e61a61801c01c0803a0490001c550346500c0040f4031460721040f0222000510724041200c2e02c0c01d4004500700b440b44007100c9015a1034484180c07040704c079410011143c5584000203540390721355440d014000d990190703070385005409600808500c400c000425200500020740e0303000302080f489001510383d100a40213203200080290b401440c075400110510f0000c2d48074504011151807406101011140302c0e4015107002d481c0340d449826960b0b9403d060740d0b007000c2d04400c00c2582030444134050701e0520075070348502406424a0108000740e030300418561102030151105010300415500002c5c03c0b10001c84600f00803900706c178081010f130b09043e00a0f064024881c14001010a44200c8044800c103003199040b615850704000d440c10050306100d0142c00d50a807001000072400504006500c0b8040c03501486d04019070a00020309641d05d03a007000c42c01090150201d412 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 730705539 1250 730704289 730704301
    0x20309010f11031006020607050919091506080105012d0c0f03170c0a0c14070f0f0305160608070804081e03090607140d020d0f05011203020d0e01120f0f05 68
    0x141d00100c444a030b0320035400d9000517529002142042c802c046642e1904d24250004040040000420f2a207038014a01820082070000c62803040344500c80716170008142043c5401001042454160016810040078a28644030308100702004d40711022088403840d075000b032407a81255424807100c405400103040b4079001082c50b4120729a102040003880d012200c07540d500e84800d03174500c0f46080b9140040d0a0000900100b03161507a809014001c0c801516030184e41c0d42603c040c1c481803034012486112001d002001040020002c0c80c82099142c00701c3c0c0e20b51440d0503c0903247c90342c001c0240c024007080301c2c0082c04202d021000c0728072034599004020a06004442000e40c1d503001221404040d100344404690005c1c0200409000c2c03040000030545846c1000e098440a500f2042c07111651b03e40b43c0607031402d00b05680c01044d0290603000e00b408000012420b0080c544225415403a0502000882040c01341c2d074807103105000d080070a00081011380c0c15111105c0104004c1007001259480e010501403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 730706789 1250 730705539 730705571
    0x21e030705010221010504061d063c0907050f0d06031a33120a060504050a02090f0123030a0b07090f0504020309060703091a101502031c020309010f 65
    0x40d2401d003c4c0c0310700000b6a01c5000b404200c0d14540204201c4940301496403d00e08244804540c1c400800380139050a400320070040540b40e00c1041940c05102e03c200c030399a080d000141c00c07104422070111042d1109080c03112020303041d8840c0d6052015810400a802a8591110380200000750381c421112000300c0c019031a1460040b00070b441c5034411300208403d80b00d11941140c03501c07114101001c04000300010701c1c0100180c66280c606210054007500e00b18602003801d911442d48030f40d0140c0058114504244100012808010301d4500d50f01036840040c0600420382040c1c0000b400742403010001d910908000901e0001c00c51001041440f804007000901c3e03500035001800c407110203111311915a183c5040109a0004a8000c14540c2c0f014001032002c80c801d802c018540b60040c0c2c0039220b034030102580d40d08001011181d0941c00c080705207041100c3d02c40d16090a102555a03c082c50924030305854041888500258541c5402e402002040c0c0b8070400f07600c04912414018020820748507000041c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 730708039 1250 730706789 730706827
    0x909011205031b1005010501020328091e06020c0316051005040306020d0f06060c051515090702150f04033204080a0209010801140a05040c051302071202030a021e0307050102 76
    0x1104c1d18100700c000a01940004241c841016081c0d0f40d0001c4000c0400354aa002c0c20142803650406c101070300002505403038241020a1481d8109102c1007803400c001c0041c1c6080c0340c0041e1580698405000c890388481c0900003801518030450301f010b000503808038100c505010f99000944894800201d0023034111007503000c880d141d18001c400307205185d5111010380305141c2072180074149421802401156102040c903059102c800c01c2801d207040210203020550201c000c80c0c00c40090f0780241098514071a00e881d002d94014245030034990340745050b6034000c10380143c04000c0049a00b143d040c070640112440d4090724410900312865450720390301c181c00360751303205809010790040020350004500503006000d4103000301e400d014002c03c90f45416031050014600100280ea4802c01d9a01c00301c3d040d524000200301c200b00001740943c80e2415420320148a0440341c4004096600400c10b44071500d4000c02e00b40741ea400d2016242500304c588645c01420761258020040155100080340c01c1d6070900d107010b00e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 730709289 1250 730708039 730708063
    0x70501021b010b09160f050c1204030818031f0203100504151a19120b030601030b040618031209060608100231030b2a03070e04020909011205031b 64
    0x102c03185c540c003011301034140440030141d0028841250800c241070081d002400001d5441e4125803115402c6510301c40385400a804c1196040c50000e140c41c1c085a54240c5c00000000407005072030342e0301d090140780506140760581003407020b4000c400110b4840311810007100401d0003402c140480707034142800c408100118020880001406140458180d00100c02da40c80030b0510050031591807440502a122460070401400a1a0300c0f6910440c20b038406008507402148601c4a491860400d03140c5002613404030404580e0f00100d28401c980866403081c0a10300141d04000c0004101765503003400c40c0a0400c5410149162040c690710000c042c9150b070081400c56181b00d542050004030040c8000c11541c880744010402151038000c2c0041600c4000943d0000c83e04004943c01044448034010040103d1114095502d004020444426005001e20030680c00868045280400d100001030050034180209410016601c0042082000c100f0071101810084400d4182d40f1040184450340d03401280b0032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 730710539 1250 730709289 730709299
    0x913051c0f081e0c0f040f05100f020d05090a050301060305030706150b0a0f03020c06090109060b0f0a03120203070b0c090a050904050d110718231605070501021b010b 73
    0xd8200c1c18851000e8034050048603285030610072011207800d000d440080c06040300507500704140740014090000504c020301c41c4003402000d1503d05010000c0800e00d40791076000344031504010560342c0c0d5001c01e029102c100c590038540e0300d842d1a0800704924401c3d640241e90103620f07100340841444000800303400b86c45e20540303084c0f10603d01c86a0003c200700c4144a10861000103114154000d0302234200914826240e00d4014180702c114185e113860820255a146485c0c1d43d14a64801803094500a58000c1a41980c114881e00c118002080420b01588006070890300c00d0350319040c00354030a104840c0040d0304500c814080e402c0400d80010a94080d4086600c130354500f00700022641006042c440c806da400c10068814084520b9042e110701440c0f11951141d07005820020608034003003d20a401c501d5030079000660711414501c500c6c0845200041110001c40010411a40e82c584050166090300c02d4944140c446c482d030300d8000e000e401780f100742d2400ca941d003001d460f0040d08154800c502c80a02221 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 730711789 1250 730710539 730710557
    0x1c1a03011503030e0612040f0203070b0a050a031526060f07050904150b1c050f04020609010c150219031803080115020c030a06020306190f050913051c 66
    0x8040c201c421264858900c00c444190800c0440d005403040000c0590107010145040070700c564002e0f04a02c00ca4084a0306c618009284d82942003c1000d40094401d5100151822100440c0138100b4010850b18104264545060300384092191b1440c0c001031000c803200c10a0425000000344c00659240d15810700e40c030407040042c030001c50308000140140310300e4965a1404d40c030502400302400300300c244103401ca01c1c00c0380c00040c50446d10000740b5004802d25000000a400d9918206c2603e030301038900103040e0062018080940e8883c17040711a04003090815415a80d694501000c00503403119000b084a4408200f81000e469000b2590744807920035a010040c00889221000f00030840c404081c0028403580010300040d1070502d000c000c640b6690040304c0320ba000001c00246020703002da108680d081e4000c0306108941c14405007404000085000704843c1ca401c20360043e0103013066101c0d003882500e001e0003044402c10000d405e061840d402c01d0a48a130408040340191081c0700540c201400681108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 730713039 1250 730711789 730711841
    0x20102070c090b03100b0a060509030a020a0303021e060402100c05190f06060e1302060c031e07110108070c150902031606082a0706110c07030b010f0b03060d05031c 72
    0x4c031031441b214400611511000782000401c854541009500c1c941500c1a00311040243c4c1d140042071004520940c014080060424280c0c041c0d040315900b1441d0f00d500110521006a40f00c601010310f4240340c1ca400ca00d01521420194034000a10b840e02d2301085102c0c603080240540c0000c00016540140401e201c27480c0d83e00c80c00c11049034125035040403038145620310401450322900510f64101c4510450f0b003020441085d21890fa41c9803071001c0c980d00d0002809808000c0e00304692a5240b80900380b2136104d10740144064030a8180800c02040340811042042c811905a80016560780e009812950b8264814000c4000e03441c2c00d00441002c642000d00040c41140b030780340e41d203060400855810300c0b013410000f021042d0341c1104108a030314507118407640d07480d4184000903028490710351006280f110b1450424000c00901a00501c0c03058000c10014884561100c003100d070000e8003a103a01103550403d0429600f980514803844803070800303840d00030320150b03504e81205004031500210340da460708c80c107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 730714289 1250 730713039 730713041
    0x32106010c1e210c060f0621060b090105130e01110a02102d020f0f03040807060e120304020f01020703050303070207060909180b0408070b0709030b090601080c060a020102070c090b0310 81
    0x2c200c9070300002d03130361481000004101c2d0304a9841080c4010000c02c9003619421403c200d02c030a040c5c0d045148910003425414007000c2d00440e220000b050314003030002d5041c0404039900c0c0e1035500204c00c2d0182c454511188162007540800508080d852000c1d80710707450000c00075121070381c40301c0401041341455008088a01d40e0040c41c0c105500030003140c0246940c29001d90701a40148021003070020f010310548041401d0b280056208600c500500750f691800e9140000465001c00c0055400360301459440b41600004d80071031380c1080d01100ca00300c801441da00101d01d803403c6600028000d000200600c040d4070340024070710041c1c1d000c07620b540100907201c26600d006c80e42407803201c83c0480d00700b9051102140e01265030503000307401908020b281511603210b161141009580c4080040c1c8109030030003d0240c2014181c4d004440351003e00303a03035403400d0000c3c0c0d42c9041410b8560300c03410000901010081c000d60441d48010340c03165101c01001d98070680d82d0001c10503070b144035010b400303a074124034004038032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 730715539 1250 730714289 730714343
    0x1c0302010b04060608270105011413050f04022e0810050303120103030f050d182d020906010210090b06100f0816121418032106010c1e 59
    0x5145d851011a656440b00c10340c5181079040540b01300801d480f18100800030070f0007000d01800355900805520000b46083c800041180c01c0310703035403451500c002c0c040e80d0100c90780b02c0d54100340c040742d19500d41c00c491039414462060002c0760311700402c042451180c0c03550300b1540b039a1141642070441e1005c25039580034503440b48501010305010440c05001800043d01030000c0f5510050b040c90030508000424844208940002d540700311030382c030200031000803c01900064000d10030348008864488203416110a8840100600203124048200c00201c0d140d02c200245860340780b6500c010b0006804508200e60b4151054940d075000e00e40300708404196a003e40c0000781c0441560f070b00c2041669858a10001a00140a29000f01721900c0341d104003001a40c00385030b064a240d1006440b813810300003003c01c00250b401e2090000da030001d0002c100e960340701c10300c030301100d20301c0044880c0141e4400004071070002d00200028002110035460750000c0e0005024000500e2043c1e1800c3c01e00c203200d21500c441155 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 730716789 1250 730715539 730715549
    0x71113021201082e0e0c06040b070506010f150f021216020a050301020c060123040f1410083307021b0321070302120d02180901030b1b04051c0302010b0406 68
    0x54030540c4644040c450780c0040350f1103102c5d200740e444511080001602c594011340c00454136400200d950014054107005450040400401c120b54451602e03601031440000101c80c4800d014083d01d04040c4180248a82456400010b000039070303548080300700054581481005a0041860000115441c101403080f904440c4440f001400268a0701211410010999441c00c42040f6a014003c1141d1102d00445054611611011803135481e10b041500d0400300050030352010342110b0100300a100c1000ca1070740c03100d482244c0f400d22600103018020034401203080020b641113404400304420b056020a00614040c2c00389140c520001d102c108040ea10840762194a800b200c0b44484031031001000e0004200480c4680140c41484c0039102502605422102d003005149400207051003610f8810480c250305460100c0e4107050b0782d411074859015002d0018078007114034100500784c0084510341d00a9400a05008088101500c4c1c0c0100b540070310007290004a01540c02e0801c0459580342c503001d40020742d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 730718039 1250 730716789 730716853
    0x80a08040302091905070c02181021021807021608191506080c0f04050f0705030705041a04030209010819030e0a0911030405060f070507111302120108 66
    0x41c1c1181c00300f14281001408190300c2c0741c0c07010031300304c0420302501030b09202c3c08544c0c1380c03000e1547d480e00611120000408543c86040440d40400220030310346451201a1011000040500070b20102a026101c0026030040d40c0058180345e010065840d05164500c00c8417560f082d251300000785908100200864019918181c0018105c800c0803044440d0103540ca6015800740d404000c0308480d600308403221034014040d580c228420010050410001c9004110404d41d0100154640303560b21075182c803009003c0b4010048000081100c80f4440c2003035401511800c10b03030900c040403000724100c40394081d100c00c90049440c01c1c000280b030100815968455500007a2510700e0f90341f00c0d0f40c120340b200c54000106910090f4040d020401c07216078400c402030046411a4035a41c1d00f400c0c01c00c903241486c0106440b0218580c00c0400520983c8482559105a03000c0311a4140c1042100060105000300e4a040d50144c4045082400d420408803102d0494028a003a2462119041414841d5541e1807592103441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 730719289 1250 730718039 730718047
    0xb2421010f05061e07060b10050a08061c02030706021c03090b0604090c0f030c090b040605100e030123041b0b090910050402041e0f0e06010302130f09060609080a08 72
    0x76007040c50003000403000585000b01040241e00c081c00d00c17034000e501c099506030368038000580c41d41010001c2003c40d0196080080c105403140d4401418540300509040c011102c0700d03100c1070080b05c000b5003800706a03801800d8613252621100029607421301410404004070080500c150028001c1c0b061070707030030f07074000c59045032a545050600018100800080360903d40d00740c400075000b0084c01343c002c0910300c0303903843c0380b04c4503c2d00700301c034003511702c900780d10f9104070b141c84410046656001e0b2140303c884142c1c00e100900900f0600080c0c01010304d590a003540d0340001c460f002101e1030303401e09107204901c5101e1081010304207210781c040c94103690244a04039a010001c00900d4075020500c035500400783c1007030455140e220310204082e41c12a902c80c2d001d09610b075041d04800440040c41c6000340a8000d41201c0140c035041640c00440c0e4003030002414035900086004048016140c0140a885844201c0e89a2955545e42d8001050707240318580010318002c1000c81c00e21804074200710096084050309040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 730720539 1250 730719289 730719299
    0x50304051203190e101a0f041a0913060507031e2c01020f04030506061302160f0602070c240305060a03060c02030c0d03050103060507210b2421010f 65
    0x78640c80f1101222071148019012175514940505001084095003000305400b19006104088288090642c481c03401e00f2100c00c5048205020014064011604120962100040b100d2070030403048000c0e02e020b0030b01c801c200c0c83e20f41641182280040c000700340000202000c940f0021070310008403581c480b5443e412505800540299010405500301000504e010301c8508074560300c0e4400e074011034442d00400c003003112515111401c0e2800000c020703801d40c6042012100c00341842c8545100825141aa5841100b03100c01981034030300c0c2c66031002d109000a074560a40c00c14a804000440d21081c0e000d10090119900c00d024013800707800c02810103028681175545000140c407942ca2054214882480b0345150b040c010400d44801e1580d81e14001115411400c0c044203940c4000c207005c0502400000490701d00380541c14284640e000004c00140d03400c15600054031628050f440890f52000200825080402c41001050284054010f020840494020140a03030009129207a05c0300e405000400c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 730721789 1250 730720539 730720541
    0x2409030221100b0a1e03020618030321130b0613090c0b0306040612050c121606110114090312070302040b190f361505030405120319 58
    0x200d100080d81001c9200c00c00c140300d80390a4800c4580320b82551280d0440005041a16040020b81200f00c0c665010081d081c80030300308403070b0601c0028000c42c8001000c08003a420404004506c0030001c0550380c0c1e03018111100c0c01c01205a1415803002d100d24800300d0103003c2054894154594001c0314110240d540e9002c0000ca02000300d020b012481d25181c106000840250541000d01202c20030306460781000002d010444107250400c4800020307000342d004c0410740020304260341000864180c0c880b074410036070041c1401b1464605400490480724046a0aa0801700c2e1070b8602c40708200804c2039002c0307001849460b10080c1c07080002508200291503a6030172090303c141d0301c54a5401c015280543d20bc001d284140d200e0300661640e00c0702071201c0361186038815640511400c0343d2910044c08188511103a43c000085031491824242e4800c114514107100032644009148948043d401603105040203030995104840458081c02607070305000c85a02c0b0f0364141d9010b03441d07030800d5411034014212500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 730723039 1250 730721789 730721809
    0x5031003030c0f060c020f100203150d0302210901180b0406050a02190f021e060315040603120503060a0f0b0a0302030604140403201c032309060124090302 68
    0x2443c095401650a00800c510740241c0c400806281e0040480204c03031542c0c030341401d200c0c013001c41d41280100b0512058002d000343d1002c991404881b100500d1442d03180a900d0902d00c0381c52008030203504040a0080329404024026210084c3c80d514071152003480c5000c0c0c8034865014504030810188014006180305501400b1b190445004499020200b0703003440072941107900702200c0c94886a44071000314240300e983c61072042084555500010b0322000001c5a500006201642d8041111070104441d51660001d000071608010900d81e240300c044401800c950040f036900303020316511400043c0c1c0d248010410005c03552070052450074800d0142c0c0c05ca001e940081c000d90780c42500c070200350307000c080caa03440d0380c2c0194801c0d100c1c030759808a81c0207042032403071040315400d1854012801c031103240c1e050b00c02c03210348443c85881c002a40300c1d0441ca202c0c01d41074440c3c0200186904190402c5100c132800201d49059459141000d04503895090311401e8040c4024400c0c4000741c6042010001420503840003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 730724289 1250 730723039 730723043
    0x30f03030a0b1512070e0f091801140f0717130b10170d0906020d09090534090e061309081c020417060402062d0a050702030d05031003030c 61
    0x200580300807480c014109030004480e1030341c0344c014402400140e540001e1103070b0780404140d814051140110001401001c03000302503400c1c00d88034074901030901c1400c0d4000c4c8842d0346180310030080d5060195450400d428100c0e19000821070034071071078807150003450115218800354080007072a13520b9951401c1a10398060010400554000004508070b400200102501c821040042200c4604c003000104440700541c040d00542d003280700ca492120f0f41c41400303501920005000454640c03111213803205010000c4000046811281442602c81505450203408509184d603130304001c3c50720f451a5421000068a025501200d00340c0d11000c1c16120341c01c03103480030340130310451070030100000000c11948045001c0d003810140d000905001a031001640c001c002c40c80c87c07006081c4c900c5d103035011500c58070505040181c2c0c4903c8400a84040850079024202c01c90650100e58a61440010140864102601c100e10900510341600b44141c0700320b054031300c14a0000c13440c480407071654600355040c0c41380c6001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 730725539 1250 730724289 730724299
    0x1a090f060a0902030a02360105010e04181a010e0a27060e03030a020903010e07030336060909140c090123040b0403030206090309180c0d0504080d0605030f03030a0b 72
    0x14500151f6122401350300903c100124035519854061021040322000e1140c905020386c11200501060341e000c40109030800082d00c0010f0100c8000381c0501c60f00c040c8040042c944d1b0f00344500c4d456620420381e80a8100c81b00025544c2a50b00c5a12081003640e00c0000907242000010409594024440403e085400c0c0111000031301e46080c454401c0c20b5500454050490740e4002450101a0409200f14a2541e0b0307424081c01c04036003176a8000300722180301121104a0012966a0f00780040c075000d49072000d0307281d80d0400d40a5650340d4000b8084030003030b11400910b036142000f201503044e10824854030a101004c00903140080d250010750309008010340340041040300c0c03a0040d0006072008014409045082501a280c40c81c40ca0b00a261420090100b40d080d042488400f0b40c075140d44640358004401c0c60341c0d000d10360740d40001c0c250b0070340071303034407021141501304020312091085180c02440c1c2c00200742c0c0140115516101855a10f8142e04040c44007980104001214007110707502806203a280240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 730726789 1250 730725539 730725553
    0x1504030321022710020703020315040206120403031a03010b0108060402031f080f06061516111c030e0a050604090e01090f0803010905130807020909010e0a1a090f060a090203 76
    0x540008041595044400d112980c120311400742d21303003941041c4035007040b03100429441c0e0135a030102c0e0300c8010400c0c00c03103580050407000c50210741d102d0017581c0581100520340041ca19160800030083c1c1005400d1024228007098000c0ca9400c040c05041e07403900042e1500415030319441c007400300079440100710344d40c01d2000444c4c066550784200c603940000c1030000e0041640c3c00740c0d500001c1c100b8101801d5036101f4064242020030080d0843c040d51540c3d912540b202119140c6810721001c4040140201a4429500b03075002125a024454141e000340c080d542d1581040c00000511400b50414020258080000e000030004e00c411038120282e01403400001150443c025512240aaa02c0c0c0808840b440300200c01408804c2c11032007103a40c8054040c210040d812425299003189110b4a031000c1c1c0174101110004042030001d4102442c406808005c80713501401c02c9c100801c0e4841000c8407808840d40c4400480c800f1000060740131500c40c07501001d40000d45583c0e540b8002000784010403a010f0150075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 730728039 1250 730726789 730726807
    0x5011707030222090501150c060f060504020f0c010f0501080a1e080703090905130804062303010f05121501060f090b031e06040c021b010c0c03080702150403032102 72
    0xa0320381c80d8442c00d5403403c06402c0c1081207850595405811116000501c01883d004a40c2d00075a4800100e030406000900c3c181202c102d80060b02258100f00d81140c0001800805441444003d016518201000300510040c20b010002601c07000c1c441d04021b035001c51002000304054501901403100c4240b00145207400030798810826800030002500840c502020070490000f181c000e60354440e20b4054044070b121071640d61042e6602840c01090200800001d0020b80b006840030344551001d05102d540c2c0d16581d41d00408502114079004132806a5401c6440c011903a00019504107282107504502e2003d0782010380c11940b035001c0c0b458180c208140c1600000d44600010029800b0710800c03804609004a24400a40d002c03001414541c00b070752503c0030005003143d01050418000e0300c103200f03041940c00c51a0049030702120000c00a8200500e81c500007040080c0000182030311071094980c0030148090200c118140d00880c8000740203c0c110100700040c0214580c1c0c01584041c0d030100050400200d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 730729289 1250 730728039 730728067
    0x3060501080d1106012402010b0a090605040b0616060e2407080708061809010f020c0d080f01081b0607052509020a020309060703090302090c0d06050901050117070302 73
    0x281d100c06081e4012203502180380e0303071081e1055541c5600000400c0c4951510b51542c01e05510301c1c8404002d0000902c2c40128180300b9003088840b0003004181d404460344404141c4018601440b540c0e01c5103280c07203010380d03003410700300e0940e45c5040110040384032000143c1c442c200070f803d0450a00100f40107541900588414842c4000b00310760b4040034800345c0e40342451000d8929540640090184501002040061343d41c240801c14118005103000f1860344130408528007518490008801041c004a20304030621800640c1944030741035036403070307007030f170362924410b44030032175004e000d8000983c01a04006542c03200350b00030914490809400c841c6020500d807115803d00810b01d6210311342d80c10900101c0703000342100102602600180100710b01e032000300031000c0d56070f1044100361405800007050410625024225a20003180c014117011042e180882603003000c0c2d0300c0703904403210143c64401c0100e59400e0811136541a1749060b103401150307011504885d545400c0007000d9908040c0c003000310010b05804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 730730539 1250 730729289 730729291
    0x10e060106030e06010905010315090507050a031415190b0d08040b1b120a0c230601090f020f123408060402090a051212120405010e070b0904020d06030605 68
    0x1a03680002e15001c00d44240e505209045c6d11921400e0b040c00d00510214074800642405400f0741100080c0a104c1882c00e01e003809039960040c2c0e03110043e00c50000600800e0303c9001000c4c0610001d03030300c131a4102c085074989500180c4c0c00c1d052020842c019408080c03044c0e440501200002000d0780402c502d02d5940184552041e0800030780c0d01c002082070050b252151400c1e1540d40c640340054181c940e822100c1520602840a0000812880c0c05551003031050b1034007420400002d21003c1e241000c00c0c0d03180e143d950142841402d50003480c00c03c0d0000c803811980b007036403204200e04004070714101040b100d0f0255880040c12041404402c0c0e4031a2012000c0310050140d4019203000130340d07400006800c040d0011400030206802207004101040075560b030380b203550041d1081250303004881030032500c0180c64000360000085110230001144072a03500c40303010991103a03100c3c5000340309840d169101152205094866031103001001d001c81020b07840c1640140404c440781100015100d43c1c0d81e1a14401e4441c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 730731789 1250 730730539 730730549
    0x12070302030c0a030e040b040606120f0624110309011d060c010c020106090b0609092d043e04050c27090f01060906080402010c2909010e030912010e0601 67
    0x621640c220744a070a041c0110400750408423000c100080c9042c4018204102c40b0245074034441d42c0d410740000a281647c4090050000c84e800b070300d01c005451200348426004010010045200b0361003004803003000000310780c44d120045c0d480441c407a403080c044d641401d01c1882d01591101c0d00f802900c80c07040d000d100b0024480707115070010480038500080a4210742c62010854080c6508110900060300c982c00016007240810b04a100500c182108401a110751141900a80955542444284050303040f820982c090581540007144141c20000400107080380b00d802a0103031203010001307a0b440c0550113554002586c00070700b494010040003150620000d0610414040800d03607035400750f81480700e8000d500c040e1016902546505252000c0c2c003003001d502c507110421551400207011a41704089120300950b1107102c2142c2c0304100400720201d00840240006c2c000140c3e030000d80c203020305010f107074800454800074500c1d008103001440b00b90703514039088215035034070303080b00110303000e01042190700900d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 730733039 1250 730731789 730731797
    0xf08031e0901050f070903051b01021501080a020f09071b03050d0903120b06070206030c07080f03010b0c0f03190804060e1509010b04060303120b04060e01060e0112050912070302030c0a03 82
    0x403030810b601d906401d00160102041040058042c4002070001030270880d505040108941c40e0100e060041b45030544004009050b030200c18000110b81d8400100180414030072112008a4000034040c400d481c001280c01c94000341d515218030001c0340c00c3d5004503001c0ea020340b502d40c3c682040600d0500070b440104004a0000e10715075010704541c1264465803034100021513845180880702d400080031404058440d04030900c0005010081001c141c3c1115021101480c8090b100d6030344d84000303c0b0903044640c141c400d42c00b0306070024085142c013000f04c403064402095683c60180030600f080b030304004014401c540c0c0310b0b510b0207503054201c010801000002038110303440c01140380940758030b401e4506000c0301c58001c509081040c00025000ba03040151201100400107030402c2c680002000380203d40d1081107079840050002c15180d038412200000c001c001e0721006c0e400c5901e60f141d1000c69100b201c7d03030000c94110b03458601c00b078072120000308040e40c02441242d040c0780e0a105d8190400464a800710085 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 730734289 1250 730733039 730733041
    0x20310170f0f190311030c0706030b0306100f1a0d050f100609061707031e051506090d03080702031b07030606061b02120304030c0b031f030f08031e090105 68
    0x4120030814801d100441c04081d00d00710452148458941d540e50f507004050000c8101d500c0300603102003050f511226250f20450310460f0307403483c004c0d005010041026020380a50000500a42034101201d003c50b02d0a0070b221071000c0c40d10b41078414030847d07250690511442007001d0344000009000d0b0328040d403844c104c54034072810f0441041c807000302942d00c441e0604c0185070041201980000e03c0d421011107411888099643d0310710110010002451032960b0011640786401900800741c2c4954425005044046c14a1100c8070400045000f02021960702c440400032001c0064492024a5013140a40c0100c0c2c0c1845440250003000f104c0002015401e90b02813030b420001e02c103681c052100102030504103048150f183c0d0910416100b45c05001078040d58128000090102007007080702d00454000c10707102201912020300c2030301030340305403085004980c1c40540b1403004422461540c0840c0ea10000e00344d0121483e5980c42c13290b030801041104081e13800b14a410400405059030f0344511101800003440d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 730735539 1250 730734289 730734313
    0x40905060a0e0c030a0c0e040510140a030f1203060e241008270102040602031903020306010f080c0708030a090302010e011b03020708040521060903091302031017 71
    0x901c041e00e80c04211007550350700910900c6200d04084a4000a00701e1020903030100041060f201c0018031700d0203a8000e85050200141172401030b0101c000d481d1100b0121003020034680c100050f500c1980030240c11201442001d0000902d40e00070304134800007504001c1141c0e0364580c4000c1c06900122071124010304103440c0c00700312960b901c44800400d40704468a0742d804103501340040200800400207002070964201d1951268200c0681c0c1c03250b004003600940d9901d40f01e103402900d075040403c44010a0030300d042da505100e0300a0090324800c031010b945039910030f03011400c11540c480340501450f0f41c1c0c0a08001420200d91403600030741c07140c003d40b1307408142c80d10185002800c48002c04000619030f40b51800f003002d102c80e4141d9031029500f861a001d41c4484c404d060002d110300c982e601c500d91004101201c84120301c3c0c800c0140300e8021303800c01134074800e5503280d0110392288203041d8810b0741b24202480c940d41c00007081c0d01458002542c0e0000c0d51045844911540001c0784e41c1c6191061a888052440c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 730736789 1250 730735539 730735549
    0x301090c03110a1409130605070906230919090207060911030705130c031b020f0d08010b0a050a0c0b040b010f2102091b04030303050f06010503061e010c060204090506 73
    0x41600b60035a8901c00940ca05207000b0741c84101c0e016203c2c4220440000b1070f042644121043d000283c02071350820041c2028140640304061511519001c1240080290100003401001008081079000041d01e4a01c0304010003140050040025580050016020520360090320180080c503100d0800020503001c1401c002004105141a5078070a40c00f0f8102485907888086071001040303916140800d000d4010b29042c1c4c080e20312030003a0400f05418501e1094110703030001da0141e510304000c00ba83c21a544010f03084480d081c0074000c07014503210030040e480c0c00c20b200344010305100703446107401d40c26400039a44000c44c0003811b65094a0a040100050049a040f0340e103e000800403951101501840891050141805207601900c1180d1800010300c42407503208807040e51031481e0002c956581d48925003e0028138090310b00b410032034203040c0000d82a502502c11030303001e214010001440003402130f03003060154050b00351190401c526505600700194030350000c0e06c090101000c0215451400d2001c0c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 730738039 1250 730736789 730736813
    0x3070e0a06061d01021506040209060c01090b370e0d080601020c0a08190c05031005091c32160b090102130308090d080c03031b0f0d0e07050301090c03 66
    0x12011448040c0700007226031300001c0c0d09991020380306c00740b01e03107544500024000740a55050395402520000d240b41d070100c019803280c04290b10035400590503031034640c2c180b88200b03082d010310994082d40c40c20140b50103007200c076071412125428502040c0c0b182407514035402d2918000300070020400c0e00080c00350343e60301030012a9141704c040d90241040c601e02000c9550380c0300071400c401d000d4803105c0c43c800140401210401c1c081c1801404030b8040c858190001c50007003004651800007406100f0b0a008503407919041c0401d000019580da07030050320075201d146d000c680f0225903480d0109821000c5052001c1c440f02800c03071602d80c00c100e045006124204035095940050004105901c10014821850603030f4541206032600b290f4051748071800c01d8042080c00c403031900003419801c001724071100340b120300200841c400c0c1442c0c0e50f4035442401c40e03591600c0a000f90041c3c0f01c52041b080c0283d14030f012443e4002d0040e05504021609003954800c04242103900c1000142c0f03000c0c40031102031050000d01c1e1108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 730739289 1250 730738039 730738067
    0x4051c0c0201080903031b070c050627030d1421010f080f03090102121e12010510021203060d020d0c0e071e1d031f0c110109050a0605040203070e0a0606 67
    0x1845c0f9516040d0103140740e0110a8102407c0c0300b0010441005014003482950301404000d03080030365810700341201c62501465040e040710072403170451a5802078100410760b41c502031802e4580d8403154003041580c4003180c100700070208030000d00d01c0d154010082050403950081c5600c104455555080461050800700d9140052007941c1c41040b034042141da000414950803183c0f010003036190704150314102a00900092964400e20000c214018031481c20504981290011200d404868200c5242030ba2100c1d40950041c0f000c003004c1c0000f9071241044418101c13504e10040028541d1249603940111850054211401c0b00f0300800030480100d41080804076801f41c03100c1d03d28440c11407140000c0543c00590b101001e4040605a01000d0b07840402070104003040f6094000742844184906800811000a0a2001413089025420141e106110320300e00c4641100140c0f8102c0000c3c0c0300c410160201070801c03a014850341c040010b50b942181c100380e019488400303020540d00d280c2039005140720405104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 730740539 1250 730739289 730739293
    0x61b031a0a15050304080c060106120f0b0102070608191109030721060f18030225030f02060a1e02070503240411030102040f0e0604050a020403080f0304051c0c02010809 74
    0x10a02c444810801c04210304882441c1c000d98994441c40d01d9040360003001c801c0302661141c040041243c03074006064108002011904101c3c0710034560300501500c0e072500e505409030f0006803061140e64031035400d8552004c84100744150303112014950608507a00b43c41e01d0301028401040b64222840c061000d0360090031410502070079805180d402e001c0d280041d0400801c180d507600385030000c54545400c5180c01c154a50112900d014060074040e46480c8042c80030682c10444440002c80c5164013810b034001e49802541c0d00100011580c00d108a60b400411500c0502604501e00c034044288a00b6000c1000307800d40c09850340f0b5140600b41454242c941c1a820f844400c02c104004480000110382039016402a54442c48030b151350010038024400c030342200000c030603144400b142600c0320495080c09100d05580030040e40c1d894488107003c90080340001403c034002003281980705400e4002458100d8058401d4600f5407850411414020740b4101180001c00d030807108030021342da08100190b44c0700c0042c2d40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 730741789 1250 730740539 730740559
    0xf0303040e01060522060e0a0e0903071407030b0709030605011d060108060d08130e0c13060c06060f121a04020a06110f01020304060b1228061b031a 65
    0x2004000c00e10701405510308110000c2040640900200005600038528840b10303100c1c01e480e014028241d80801c14a9801b550958078009800c03003104803660300c112189000355040006075610103603d180d440d134100384d0038801c0710004400325140c04a40c5000e000c1c20303124902c00d6480c40c03411388140c0d501680441c01b40c4441c3c001d040481c185418026a00200034a8074038060354400e000545820818100a42184000f0030944101d40020140380250303100d02c610042aa03030f03005044140d03446003010403a61080302074002c000b0140555110743e607182c0b089002080d081d40740c042210f004025079110754102107048096800b48068480103811b582220341003580d1924080d0042070041001303128000400040c0369890441132420300c2481500880360000f5503907410325041c41d20140c0800384005208402203140000300680c00101040c001c641d8280c5021003500d03017140f1048442c4038820903121242c8400080600450f078040300a40a071b5181ca0004680003071006400e180f031024a180760048002d02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 730743039 1250 730741789 730741799
    0x4050303040f0f0501050106050d0f0605030a0206031801090f0201030c030c08160e030105090c0109080a1a0705071a10090612080c0f031b16180902061b030301050f030304 75
    0x100803a54000c1d0404030b51030070001c1030f02c0d00110480e0346010180071946008004923100c0da0050041400c9005490706000f0005c4104c08881101c03502d20419625030f0141c2c4c0c4400c014202000907541c0078030380401030707071442080049490a4071000d4404070b82c541d604984150843d070301481451100e0015140400a003c4010005080c0582c0a000c2e01d0600c1400d1000340b40e03040c0324042c8540a44000703402844142004008540d540444109103804180301210200c0e07000d10014006c507096412040c0803c010f140c0300c5110790000000b4100e8001c224040048c2800b14611f0103007003050750113641c000c012920702002a2040d4a0584e080350988908241d010400c040b540c40150003045e801400340355890044050b224a013859010314881e13240008a00c2c821520341e1b182400800319441810744840314030341440b0780c80e07180d25800b810b08000f04012030310300d400449500461145101901803450140c20081c6580345004154038920f21743c1c03000005100074201502c60144050058000b117041038204 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 730744289 1250 730743039 730743043
    0xd0f0512091c020a09020d1a09190e0a0b04030507030305060a0b070206160609080324090f07140d0614100207060c082703061006080112020303041d1e0405 68
    0x100c0035110308401a88802d4003556030f05990381c4000c0c04145811580d550101c418480544802000c030201211000103c003514182040007a22410214030001c07898500c400003a0028018008403010621882c00355000007a202e0340010b018034000c0e15120340f80c40342c1340b4001f07040d64001003a2034041c6143d241e08010750001102919051541211764544cd2111050b6042c0b580103410f2011700b1881c20104414240f20000d00254011800740c0400c60000c808094480da84e6100158800e030002c140740d00140b500000e03042c5080c2c02c1442403506801c0c040d00c018440816030002280e500c00380b903031450200451503c0090342598608203890b0108080850107001e900c0e107500384111401c2c003280d1003044c1c00b048500b500300d460456100e40324811140c0420442113011036501d280a01074070030b00e004191a40e031240d038010304640b4a991804180d80c02c1524181c0303100010182260180320501022584200311981c00441c4d00b1044142c44c420700c0e080383c845004503100e038031144c040400c03401404089200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 730745539 1250 730744289 730744309
    0x90915060b160311100204060906030501050d06020a0c06050412020706092409121518210c0203060f060f0d080d0c050408030a030c1107051e010e0d0f051209 69
    0x500c680450b94800780b410207655a020701041000c66003d1800c1407540e0520f00c4d4068402d45869036580151541c0782d10081d400c0310300a010b040d030b100c040f12480d200001c9181d0002c080e962010b240102060403980d076000e0a44070181d5003254030340c880b00104041c041d0304100301070091180b4500f00d20b605142030354145c4000d86000900c04001e00300740055000b0b501454441e00105000e4070760005011041c1000d41c003002500005007000b90800c0d2a803072203800e20502c0884031030703007000050780020b000d03c81440500c051b20300c2c034105000d0310827030041c09070760248a01c40c810714a0211101180c078042c1c0402c8102c42e1402407452040030b6020743c000209140c98256405590031040001c1d40c8035055109507924055903020401c1d5200c005043c0031702da03509d0b400c1080c0006031901e5240c0b41454500b022500e0780c55500489070040281e004076080c00001b05544402000107041601c6800c01680200c1d460b220380080a44e01100900300e14401c02100308070641840d00c440283c28285100c0c00d0010340c03040a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 730746789 1250 730745539 730745557
    0x213081c0e21060103060c1d031f0f06180501090c05030a1802060721020706120504060e01020a0504061418090415060f06032301050d0c0b04090915060b 67
    0x2010718040480da1880090070000d000002c41240c4956a40b80f42c401c0c081c109110203080002ca0942c10072501c22030701d0121204aa030001d001e014122030205900c4c58039100e038000c1c03003a85da0300c400310f0042c056032510071803001d40b50280e4100071059807a241e18054a8041e40542185c524040c401c40685a100040c1e81d00b040326290302140420705031155005103211002c000e035000f07100117102810400c2c100100040404605940c4007440d00e094416a1100c01c00c1c4030700340c04100c00340e554010324441540b117a54094812200000c403c1000b13006582280c101e00304400218200040c1444095000f80b41c95201c400210086403070680030100e1108210f2542d50028000d003400ca010030108041c050484103030140081003082515501c08405000803007034800c0501080c5419040101850900000686a10880039000311a4a008107020443c0c2068105480e4104100360114080c00c49500400013000080400700d051405420564450032401400829552401200700f10b0342c0098402e079041c0d10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 730748039 1250 730746789 730746799
    0x50c0310121511070308162106030804060201020c0610030f030c03110105040606140303030907120c0e010303080105090c070b010501110f1501031412030c0d0e010213081c0e 76
    0x80c0382441e0499400c503000403140c2d003850403e4048000d024040024102090090382c0b04401ca843e05586000c1818200c450f10f4005109a80489020380c884801d10001c46064500002c00d60381c0ca440302000da8000d6040140140d4002071419102e48080120380e0300701c40d000543c4550945540c1e155041680c0d4a02d004080c4685030146d20145400303000e00304510a0040300a002c0c5180610305500200640c4c050a413059040c050f581001c1e08001080d01d100d0220f0360002c0c54400e040c20215042d036081920100c0f20781240755008655451310030b4485008600c0307034440e91815414041000503640001b0700c41c000c0a542407000c0e40214400e0b43e20303d41122000c1c20440e624221042c461810501c07030600403074440c8540c46401d440c18a21300c284604a0380078142c24402004e045203070325202c55072013024880d600c01c14408144c0d103088510003440600c02c610b000042c98499906042d0030390700440141003a02c0d618007001c006100c1300348856640f151150b41050001c0d03042c072001070240425100d4450090b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 730749289 1250 730748039 730748069
    0x608010810110f2d0a020316080f070606090b0f10030f0b0a23030c0d0809032407030b030609071e0504110a020c091e090c04020309010e01050c0310 65
    0x52185041100c40f25120390045503911090f0b21158022070000e00b070140020413605801c4180900c01c5403e48144421503400785142203c00a00c94103c1005100c0a40301034070100042121100b06000030842c441c81002c01103a0649805601822641503094450042404524660140c3e45500580c07000c8035007070800249048185c1300743c000514100526580100c40c416012070000ca5151200c034101c9607400110744200280802d241d160031020305400d030007000b4610404009000b03c0050140722101500700c0e51750354840501c6000b00040442070840c04485031041c40b901e55494020890b0000e0280d00516481c00d1814501d0742c1c030030f40d902c0b680b00c100b500680102c0442106003886001064000c009100d5034074840340c210040c1d40b000783c4039809846070310000015414031113102c5224030003103022104014250001c890f02040000c0c0207582c01d0144610a04003070340d6600c0035600485000e4000179001c0c140499041c2184c0000d01505d100400030f10412680608500a80068030402c40e005042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 730750539 1250 730749289 730749311
    0x102160e130c0803180d020f0915060a0e0306071e0c020a2d0807030803010905130b0708010f06020c060d020a17070804020a05040b0312090120160608010810 69
    0x21441c5180d40c010315154048000240c60000040075110390822403603a208030028070000c22605007143c600c0250042d5615202404500d02400c009500405480085c00390030400d4001400c0e035440100c4580108440d00802540c46c14200a89540180103007441544806200b81d51a0000205240ea104000710007075560704644802c101040140580c12070740e003a2030b1038141c440c284059008050112742300030b1031000070f14401c006440c0046030f4002e60400d285900701604140501401030072103000400326070740d40c0c001502880d469480740619584550040d4140118074076446415840f0f001151301c145000c0b1200d943c0c4000322040101f11103401a50780b0741d801c1c4151082c41264441d0240594020100300320740303410040c2c2a10407882160544141c0da1100704010880b0f40e03800486801d940211103c0d040041c011004051000e0705050040d007961130115080c5480100d55041002504002c200329640240070310700308c0141c006400e2002c2c681d070401d11202da07203801c006800c0b42d88030b031a6107050311 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 730751789 1250 730750539 730750561
    0x90f05042303130902040501020606180703200d06060e03210304140d0503060118061b1b031a0a1e2004240e060403230312090c0102160e 60
    0xc40b032a980c1100050039540c0c40600c00031b400610441e13026000301c40000311030b460000316600180302c21680803000b54555060840041a00d540e0000031501c1000c28036003550400b4015020f0a6160200402c04c6410444010041c004058201d80603600040102c000900c84e41400460b00300b1094070503031260b9803410b110518941c60584000140580011048201d600000442c8030764400c3c0c0b949031001c0741c56060342e8010f0300d071441000c0004a0141d90184100340410006244502413100207007078840140910f07031546a580d208a4031006545001c400300022004030f15400003204600300124186089240e40c0c02040c810000c417107968034282c5920200301c2c0811440406200c0240f162071340c1e2210300380403010501c400b0100802e001c00b10b03641800392003010f0300e699206000e44124101451541d81c1e0318815050032405030040245081154010000c00180840503500c42052209060002e000740c201001c6250045c115002180301d01030741070303d540030807003105c08540703400d0515a22104145 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 730753039 1250 730751789 730751797
    0x2070602130311011404060f090e0109060e0a0b0607020d03031803050d0e07081002070503040536090a12020c1002010c030c050309070902130b13090f05042303 70
    0x204140c0c804906a11003408106a1105480c46680d491400390700c0c003001900c070f080941c030071200c0c0350b0f80800084c0200e0b445203440a45030541400c04050b100c2d115208040601400d81280c4805036907030170304000380b540c0383c8001a009042400304024114003100415500d20030b00350041d0040341000d040804251183c1c4c40107049101003000c1119101c0a0310b80100700c9d6000390001c03520981094030012603100003181c6a1b08680f080b1005001c0c0d1460f2000381300181d00700820035150f60005200008450301d801507100300108ea1780a500c00716445100c0d80c0c00c1a01104648540b401d4004020002040000140340c00e18a400c0082d10788041800c901c100d1034a58480354460b005044000d044154980540040f803240920703450610181c10a0002203401c3c2c00200c0340010710b40c0c025841001000d16540c01400001c0d0301c003003609400340e180c140400c69517101c480074224503008040d00308029142c5201d01004100e000c0000d001341c1c00c10b0b450b00000c90003043c0d0315401e0754681003c00c00c42104200211 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 730754289 1250 730753039 730753043
    0x21c0507030b0f160f081b0f130e0f2202060703020c01080106031103130614010b190c0b060f0a091103060316081c030209060f030403030c1b030e03010207 68
    0x21992562686002d6140c48001c0d203d4440100300c40300480c44082450600115281503941d50b0000c410807110100c6030304101514188040503402a1700e10201c1d803410080c000c002070b4903142995594172002d15454010b050303016002403030181007880708070030b50482d046400c400400201c0c0c042e8841210034824400301e5080007940f00200140b1081010380110300b0844140013602c8074403171a85d945006600b0746c4c2e440083d0003104003040002030301103911209031903101c0e40946400a00190f08030714044600750280c100c0303540d01710042103191541c0c4005805801c0c0484618001840d0700c82039031102e1150401134242c07071092402c000650410348810701c00c88001c00002205100f40c8450141d03090581d0300030b4603828000c0c040c13802c000901028008135881224160b00040c10000030544030403101c810912800c44c1056006c000a045598a0078098044081c042030f00941e0390505281c0039048649000d811410312059681c44401d107180c02d0b25650201e13030141090341c010360000e800a802403007079802c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 730755395 1106 730754289 730754293
    0x905061303031d0a0602030c12041203051e0f0403170307083106020a0305090a051b0f0d0b0412030e060105040e161e06030612021c05 59
    0x3c1220445424040c03102030741c92200000c0e1514080d5400a030041e400420005003240d4107010103212002c6039004980340030720746810000401002440a0144140480e9040804030104401c1d41000034481c80181e82e40d0003040c00c40740c540c001c4e0000381c80324001c851800308290207980480e0b0066a60392039440044d40e0341c03030181e2007030200744207032210034240c0d0142031b6054004400c4513400d051040a001da140c074481c84004040310340c01400140c4542c030804030719002ca080410a40d11500d038102100017203e0540001c00d660042101442d600804014640014000b508032868040e40c841d4080000d420302e0078100714107440c1681c0807442280c100400401803840c107607000510012550702520000d0004800920741c840d400d52041011105e040d0f00c00002c041e40c81c10900103031005050806c40c40b802c000303007400c0703580080388000c0c020008a00304031861008a4904400355501c031003 = true := by decide +kernel

theorem cover : BRFrame.Cov 730575539 730755395 := by
  have h0 := BRFrame.cov_init 730575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 730575539 ≤ n) (h2 : n < 730755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
