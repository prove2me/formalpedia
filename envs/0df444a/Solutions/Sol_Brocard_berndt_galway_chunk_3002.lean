-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:25.697122+00:00
-- url     : https://prove2.me/submissions/28ccc86f-9c91-4637-aca6-a4deae85b99a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539748201 ≤ n < 539928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 539749451 1250 539748201 539748211
    0xc110601030b280c11070e0a020d0209100f0906020a030e040b030c0306040609030806120303150402040f0f030204050604090f03080c0d02030f06010e01030606021905010204050303030112060506150a0305 89
    0x2118848401d5103280c0f5400501401030f002c9050b13844080c0300c034040d00094014a840c285401900f2810704040b0b0b408204e10b4040c000405181d8049441e002c0c0610980c1140c900c0c0c3c1006003012892402008020400b0a0403028400081d00c16540080c4450001a011003401c0d817584450281d01c0051003880014264600c4c071507403504c070303c41940034191001d0120a00490050b10045141c080c00e0030060480389001e003e0f280254080703080c3c007042c5c01002c001d0b260000350014260512030200c50025000c1c2c041d40e0002c0c401c201507944002805d0f8022100c0d40116031098a0038041607903000c0402040b9035482c8409401c0d4410a01520f001a1052000c250700100981c54035041004003002e070003c0740c000b01c0c0c40004480008051000d95a04854141440002440d0600500381400c0c3d0003915107110000d9002081000e036104007c201c802c0d016107000e400050103e907141d69640159580855408200f603400c6403600d80401c6207400c10040405611500b040708030310302a00d10004400034030000744 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 539750701 1250 539749451 539749471
    0x5100c0203030d021c0c051204060e011d15010b031303080702070b1317011104090b01050403050312010e0c090108060f0f04050f0106030e0109020a03290702060a0c110601030b 77
    0x4841c070f429500a101400d40341e900c0804000d2581ca440c0107a0044800e510485401d121086c820b00310044500411564442c0e408480410a4403401203400c3c05041c0b00e100014181c00d280a2805445078002080a1076a0300182c021a071640e0b139602a803101c5c4010348400c2009520300e003031500441e0207402d2058101070b03284111811250b540c0d0034050301d07402c07400b485800484440c1c0304005000010b102c6200544180d0020444003616400c0c903041c40c421481007084a548031880700306241c0c0030300241c0b4010354000c0184c03030b40c40d844c81b032400d21000024022000b4203140ca0003c22400001501074441c000300c10784803019140c50b81070401030b130850740100b01d0380d0080b45d00340c034045691540d0003814000c20340d00c0040c64040d414400090181c660000010340b680e0b16202006025070b980f1890300c4102d03500005800c29071000880d001c1600d441070004021060381c0c14040c00300d1584d00103511032089280e120100031500c4820001c0b5403410305c00c2c00e0804103030701c89801840810385404540b81c100801074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 539751951 1250 539750701 539750707
    0x21005040b062b1a0619140a090f0203010503060f040302121315030f110c06040209060f030304080f0c09040503091201020915031e01120f050a0b04120f0905100c020303 74
    0x900900480c214200300e0342894032411844500d1820b010058000201b03e40f40e899002d07510100200f004454443d4050160f042d40d0a101340e61144198100500707030403c1c1c280004101821040d01070750081c40340078003074840c80c030029803000c0c1c408021900440d4940c1c09880c8111040b070b040c1d00540c0010a00440381403091a001950310314034083d180000d50180c0700402c0e400044064001100c094090703081c45101b04005904481501203205640554102c034ad0701c82c140c440c4000b182104801522041d0503220001700400c3e40a400900c140003040b0035412610f00c002807506010010400b558004c3c0582d00a000b21112854000c0c51f41c02c0c0c46a072a00010b08120000001425030300985014a190410020a20800c0ca441441703000400701042e0010015503d800e4070780c08410a0002d024110588045c0118104031040c404032081d19000308410300c00f414941820796542d0480b200503004101030240000d01140280341070344c00c8420041c5260411260004c0c20b80d8038580f0f08100300d84c140010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 539753201 1250 539751951 539752009
    0xa0e01031506030f0507080105100309230a050c0303070b150d02030706170612030702010807121415040b0306071b0c0807170102040806010b160b09010507021005040b06 74
    0x4050000080a503607030041006504e400a0108030b0300301605140405c42c80d000180201d4490202d091000559803900141c0749040781001558109030080b0030311605030564480074241030002d40040a41d000e03a09658000640c0c0c020150f07248038203140103044c1e144160010301c01c410110031000940b40040d0444608511541c0041d040880a030020808a02494124a106081d0b40900d541c000070540700c1e00d05440c015000d166807400740f02d600030f04000f66840081d031414864020b900703201c0b8202c102403220400c0d88551300407504080b0341203148140380010320002458640107060304402d001d03015100716201e14500f181e00390207078a01c00314008681c26100d400900d00a1445000b049404058030180342020541490b80d6100c141d000d0250b070040c03105001940c8041030f112304503051112016910000c0c00c3c0d20424580194401415249200c01080341e08081904854820310b075990942d22560207845007501120410b48002d4400c4e4a104001140c0703003402840702c8402c62640c030700c001d40c41c929 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 539754451 1250 539753201 539753231
    0x31209050115050102070305100c050c070906030312090b0f1b030406051b0304050304051009091802150a08010b030a020405031c080c0f07030c060e010f0509060903040305030a0e0103 80
    0x126040320280c0d900c01c0002a08000ba012a0300648424409054501d25544800e07030b94001203854a108030341d80c4d107a08003c2c5ca00403030468169540703c20075288425640d184c2c040081003148025000b00e0780400c40d4446540c100d204912040d54851021403030340c1c4401456940c249402008041a001c250400940303c0394000c3c051031049210340c50102e0a890810300c0f081590915407130000e95420b00f0300038000000c4000c02910181d8000f959001c505a0038074a0032589141380340d100401c6130707140008843e60030348411141c00c9024001d41d4400900640140d02584a208503580c480000c0c1d0400c0040c40551958802103420092108025041944517400281441202100c018200070700c08180b60900350052301c1c2e260b1104600c1d000741d041c00848a1085010303c0340603801401c02041d1100c3c02c0c01c01c82c0b254044603401507a20020054110103034400300c018001592650064441d4400040740d02c2400001c54041c1e03030340701010350f00b081741c09441680e0078490700c04464107141d12041003c4d40040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 539755701 1250 539754451 539754461
    0x6051b070b0705251505101401021608151501050d1d07080f16030b0705030a140106050d060e0c040b131d0a0b010f020c0118080f0706080109020909130312 68
    0x241e14822080c0450f00d900e00203030765031451740d0000c00c41401c00d01006000448556030200721410248051100c6400500407030030102c036800c1900e6840c41c01da0001c250311500142440f490130742000f021105440ba180c00d41180c1441d071408500166080141992001080e0040d444514411250940c0e407868403c2250901d41240c006a20036400400d2a01980c03d04004104210780c0f8990a400f4150840e1203200002c04010111400d101c40000407401c0c2c100107900503112884400c41c0103c81d07586400d402059075100780384240d8511708000340402c10052105186008190103811a40b8003494800301512581095a03101c010101c0d021001600c0364a000b0807120342800c00b0b191080c0ca2501200803001c80c0d00841615040203241c0c41301406030758001400011030308007400c2c482400c0b2008a800f1120030404e80280c44075020b6604800c0956000180c0c403130a40d00d09407505185c80c1e0302c17a58200200e004900505902a8010011800101b05001c0b441c1045d4007920b410f80285e0340b4680b500080d15 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 539756951 1250 539755701 539755747
    0x20c150a080c030103050a03111509160611070603112b05090d0f14042c0f0c16020111160302030c01030c05123106051b070b0705 57
    0x29000aa101046070344804003603409505403004a0455065444159403000b45410040134400c00700300c1258010800c1140d9810034410f01481c28480c83c1c040b810945a4614002401c03100184107000314815005990192498840328020b004980c581442103003d040300f01c02c0a1804e580030410981201200307600304d0348000100f12101c160500000451046403c010014100e0b034108903440307801142d0103c11001d00b44090700d015130742245040c0c9605c01d540701ea035000c01006107110054220541006200d084405d84481c0458216940c68081c4564601c0840381c401540d4002c02112800c0c2400d00b00b00302c030150040c501384040241d05202e4500d07110300c1159508444e078070040200218a020040d002e2020f03000c0ca01403200c182040409000350050b844945091700070100018007130000101d03a40b01030905a980508185202190500c0d00b208404050300d01c5802c0ca800118414003c0c80b014400703d4907e2510343c5400c5003522130a01003000a800c7c50200402003011003040318100c09945448 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 539758201 1250 539756951 539756989
    0x6091302031b0f0a0503060a0b060423180103020d170f0d150602030c03041a090405070f090905010e0402130b0306100f05030d05030f13150b03151603020a020c 70
    0x780600d00d00f00001d542c0b061592612554450714107020720385010508035003001b0862008070b04640302000260050044c2e07041415000c50410080300102107090300103030292002d5403440e08080ba1360744101b0900400340400f0390050140c01c0c070b0a0009080b005011035980c2c0403c0454102502ca5242812940c0180c04800846485809908009410000c00030042c1814002540b07400c0040030820340724001c80c490380505422032090380aa01c18000d0481c0d00091000308104694900030780c018001d05454800407000401c603450128602599205072410b0f01c8101072250007a80c3e9507401c02021150b10482c014206454500080b1551401c000c3e0385d00441031050303a64480f5041049880b015010307644034901c40d40c010084100c81c503800c00212604890959100840c40d91003016410750440f61982c0100411005184180e10b40385990140d840d000d411020b981e042d02d0411f0300c1c441c861000341c80344030321b4001581d2000701403802680144100719890041c0c441c100c1030500000c2c0b104040e56204444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 539759451 1250 539758201 539758243
    0x6030709060e0406140f0333090708030405120c0a03030e0414010b0901030b030a05160e010b0325020106030804120501050105100c0602031330050a080609130203 71
    0x1038242c0045007800e1060341a1401c01c6103904d84881d5090780d49940706000d010740301d9440f010106441c2400300b900c907040c405884040c01000c0c0080030b0401050550034001e1150742e1342c0031515022005c60303d10704070707031020000b141008d04000c10006001103500546540d4424800350b040d090720707a0380c0040c00850094850741c590649040034441a20310030988000c1c40c0e0140300c01800588203141c140c9104481c280b80015401c8800c5e800310f0702e00342031440007400b00d1003035020440308511942200da05030f501603080180140da039041400594002690030505c82c041c403401008800c4034504514103c0c2031180700100e002980e030307180c2810740e500507004000001400c143d2901401424014140140342c290340503907104d410700ca002449000014001040307160004046865401d10000c01c46419400c60b0b60301c082d8410f0160030b841d9041c655481c1d0080301461025040c1072600031026104110300d161240049540c41c01c0c100603040f580141400800300c0e40a4882c1d004d0388040140b21440842d40b0407000e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 539760701 1250 539759451 539759459
    0x1b0604081b040b010c030914271b0702132a080610020a0b07050a03021c020703021c0509090c0706022101150c0305131a0d1404022d06030709 62
    0x305640c500f01c80325050141c11840c62000030f900085810172203460070b0800100420f080001084080f0312014401b01800304040b0343c07814540400790600138010098000c514841c011040d01442c01101e034042e50054000d4858045541d154100c0c1401c1000905402e81c80f24180599001e01d03644600c0c414001a8a0b004001c19824207101d01e80f0f1004c214001045041616691401c440c4c600034074480c1040300114400d442e99000303406030781510700c2c58103000e01c043d01c00a05200003500007800079030040c030401079802d01821820440c05e101c050140d50f01d40c6420301041c280049a100500035100601c0100081c00200325540b001d4400740410000040511042102c01c0c50f1322101030308001c041c4049800c45901003030704081c1c2024140d5250030007588600b05030140b1200e0100560000c3d1409850000c94011140980c008100c421444c503004c00c200c42c0703280c032020b81030042281c00075000b094075080c540070384000f10380c500c110680102200c20130041050100d0400c0c1c01c103a40180200d0a0703104284 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 539761951 1250 539760701 539760709
    0x2010b0f03070b040b07030302091e03010f0c0203160f020928020c03030a1a130608010c0c020f0d021c06020d0f050411010320030114090105030d021b0604081b 70
    0x9106010101d0042181c00c0c20700071400d11600ca1351040700158800011030404150090301941c42c9884000c019050780a607403029605805000251144a1f52a045500104041511503440c0415031a0300860400110305c00d0a62000c640c2601550000d211120350001aa81d10700707000c2c81080120300550b2007403403000f00b2482c40c01001c0710441c00507005200f01c501c8100d0020659600c0000e03c9404110316500c1841000003c0840c030340e090b04180100701110381040c0a0b0006e1003141c49640007000038172a845d5007159403141180e00207500009620000d110b5152045074034606a0008221138000400d12280b4411194200c10868003950003088000d0519031a11442c0042400500305110920b09952004031001550300558141030b41c07051004040008005203c584000164845d50b49585071540341c6040714401c0d1180340315608000002c6503500300800c060690780f00d140c004014040121020404e030031800182207401800038000020442d00800c40443c99120300c00600b188a06030500780 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 539763201 1250 539761951 539761969
    0xa0513090204090b0616030309150e1b010e0105070209090f0a0f020108070f0c0209190c120b010c05100e1f020d060b0c0705060d230711120f09010909050702010b 71
    0x14030300c81c80c000e02c96103140c6d2001e8515000300301c0c1d140c40c0000340d601c290700c5c2c10101510001c8660220300c0ca80f00829080c845c0005880e01c601203a41070700310640b200003004461610b6400d00940c0010010b100800040c1022003419401c04a0207040e50310b035003400103500f458000060000c1d40c0803003a010301a002c3d56040725925802002501d0405004006444007515406000500900411500d8009410700915100101c1e1107c0f06440500803c0c06841c0001c00150240b40100191868640c515800c0c0d8018407a40c1152540800a00145840d01d0311000061a120401030841d0152001009644c0780b04500c8031640c0718491401038032811005040310480e205500300c0244504100580e4042da100028004200c4604550090352880100505001b5150f040f440710300007601c6600c40c40407403145040380b44c824040c035514030104403890900144c1d103213007070503000e08a104c0c01c0001c0d40440c0e100c08000c11402406041c40803030380d5510080034080b078408031400401030b55100c0d05916285004518 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 539764451 1250 539763201 539763221
    0x90f050d030e0c1c060b0306010f030c05041443021506061b010f0e03030108190f02091510020f010b03011118010c0602070609060e0319050a051309020409 68
    0x240f241c05115001309440302c41d41e00131401450502c0701100b04010440c0c002020405000e800d031400c03543c1d220700b05400040389000440361030000c040003040d2820030b8458215a45d000d00c02080c0305465013102890009447d420148440494a100358404e01d1900c140941c007401e5850040f44245041400900344a00041811220140c6c0e10030300a56654040030384902c00110458501c4d00a40ea00c0b0860041004410070307270708541809000280c0070000310165040310380c00d6080d1b8805000b408500d107103010782840020304800c00e1484040c0582810403100c1d6216080802108514806c04000703180101441c01e0000143e1103084840030b10307003081c001c3d1031089000760003c0c0422502100405031600448422440c01c04000b40481440d0303209840e4040c2494201c18115958480e82c04c2200c050220a00191403083c101800c0d4060180c001044a1900031102030001001c02e6150086846900c850110b60030031009001c181000e40080620300300a2400c41c50050303669141804101c2500c0c40c000e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 539765701 1250 539764451 539764453
    0x70201030c080f0424050109060501141c0c12020c0f070501020705010512070201060f0905070e0f061815040f0e010915090b040914010b040b0609030c01030b0301090f050d030e 77
    0xb0900402900303021140380c005a126406070f0440c41401444022455011148800e880c01d1000008505d403d540c005825a031080c1d852a0407204209200d4a19220301c0c0101a010b50281418100c2000250300c001a00030044c5016500e40e03400070720401c04d0ba004400c0d80c016540140e82d803030f00d94403401c00130f00004100a0000d00000303840c0c003002806500415085c541c40b082d06400042c1028402e5202501400003011341103c0107440d66001c000808041740e10342d01140e0016022502882c06801c0d00503001c1005225031b150501c00c40300150022142a031090700168004c81e00300c00610003070043c0c40a410030800402d1028a4441803030081c58040c1d01103c0306619240c0d204c500300345001c4203041584c141e95400b0842551440108006000d220409460340042c86604824503606400460510b84200e4082c822184060b04000d924440c0300141a81039001c00c2640c03602d940130740c01120000c24024000100740d01d00b902c42d4034869039000790849413500801c1d001d0000036014410007000100c0c600c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 539766951 1250 539765701 539765717
    0x30a1d0a020906030f1f0b0613030609151803090b0703090512070801021215030c010e011209050316171222060c09061205040f1112070b070201030c 65
    0x1802540c4511a00c24041c0c040c290b03240004146403020021104030207483c0c030460b15050960001c84031251070000000c5401810800b1074044ca01c0c080058400d100c1c10060520310f0649590781c1c88000f050403240c103d580b8050300c6030f0b076500c4030a10307c219041400240c024000031031141c40c0003010300780305801104404c90709225450110f60b0000119007a280241c40d030000f07198804116510700912640a641650300000e004c000b507100c1c0c0c0890500a5000180340080003502004250700c4094002c28180000d51002c1d00714610740c40b5a44110114148040000ba0b82665841d51410341e07100c080c460700030b8552041c0030010000d8074041c2e0441070318200314a5090840100c8440800f8002030701030070108140958110641c54aa1491111281e11003400c000c2a00b240c00301500b4041184108008115058410320901d500b07030094502c0785030300401c8100c410400740c2e01d00004c40f002c89c001d5904500a58600380400360101710380c0001d0800f0414142e160304a900c0011b054070310052900d02040041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 539768201 1250 539766951 539767001
    0x4050f0a030302090411120a090c0b0c100b030c1302130527130c1206020f03070305060a06030213090203091c030b1c0201080f040203010209190e011d0106030903050405060708030a 79
    0x3d54003903408c0302050a010540d1285810964103401c00c0340c0040c42c04020002e01e02054140025421101c550040d000b480240d8070042016107800030442c41541043e000c01c1107400b8a40c41d40d0080140a40d03200145084030380381c0780811210031a80300359070b00500b982120100b0314030007120f0280d4088101525207200d82003c1c0e891001070b8281c2d2048900580000105800700310381e41e010344105d030013205d03030040e242d29241200401518065450741c1c01103e10440c00b141d814860300854480d001610003102070213182c00240e0f80290f000a100766018064841d2409081d0094058580126078958000c11008800c500b044013000d880049015001504096640140d82013031000307500a00e09001000240d0f52800481d019104200403a981b01c0c0365840c801d00481141480305054a0418280d0507460b0b8036140d46088559490940461072200c01c0c00400c800c6120f07400c1807204510034581f42c0c1c00d1a54460216201390041c2108840e6000080200710203181584500c0941c2000042031154035030034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 539769451 1250 539768201 539768227
    0xa0c0504030b1306020c0a02090627040f0b04200301140109180506010605120a061d091204180b18070309140d08100f0503060a0504050f0a030302090411 67
    0x492100600000c920302c0000c04110b40e03140181c0266400240c2550741d10000c0c03c0084d10340300015002c034440c2c03c0c030740c1c04030b101d50401c1f202e081250030030880b01d41d980610000041101070001041201d0a4114541a500141c05100c040d07002c0c0d449000b446440c11300c030902500360301d04044c100c9030181c0e24001c3c440700702c01401001c0341e046031040200052000c803652000007001032400742c0a09184103000000031460340c050000c101050305580c10001c1c50b1641108041500c0301840380c0300c2070030307030021058804002c0400e50703a4001900c0001c881004402c4465102d1a03002a80694030f41043d012901540380303800d00071050a1081201e000b0004076851005417403d110290070b020030903645a00200c2000522110000c44113003900c02c82c0c80301110880018128a01150501c007003000d80301c00029803038040b6100c0e00659100030060001c659030741860100402000b031090712184149061410b0b00d0308d0a201200c4028003e640260b510004801030105541c41105c500b084410704200308281024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 539770701 1250 539769451 539769457
    0x203070b070f0b0604150b09044b1515050304050d0813350c0303010905070504090c020d0801170307170c2a0105030405100504171309050a0c05 63
    0x2602c0b410f0b450464607142d01280045c4103c503c4c45031700c0c14900c1c00200321076103084040c1c84200005c50b01400058031411009000310b049241011241e6030b039142684c10314087c60700c24018101c48a0001090030401003c01c070585800c405e2210000c80e01c1001403002034241152203000001d1800c00625500345a50381954640555010600300b042c183e001c1001c1c258400c1302d6201003030700500903281c410001d004080c0c10329000c509e00a600e2a0200f81d1070b4101641c1c5080d00c9080d105040a1825a172030550400c0150600800245c00c00a0070040410181d2451040d1100803940740e0060545c400f05010103000b1410603001118100080c3e192158542000012100a01d40c03240300c07003c0c1c520307100c4064615800707154690a050b00401d011000c400302410a030390015030100c00d0190142c0c1006005450901c4243c5020341580c0040f464122030300c0140d00490742088c400c0340c20500c0003000c40c210303454075044003031001856142c0b44020810b0001e03d0107400c8d041800100300b00000c44690780050a644 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 539771951 1250 539770701 539770703
    0x90c150c06090c230301050907080a0b0a06050a080f010b09060d08091f020609120f090405280f0e0c030a12020f01020f0403060e0610180e010c020105040203070b070f 73
    0x2e03110700b0188100b2520061010050590900e4034107aa41502c1020301c1c9402c0c1d4040346400b9610b41000504c0038980000c000c030882c0c0c400000703022800441c0d16880760342c0c0801400f1980d0345840d80000034094481607081e1000300703a2403000d01066514a0400c1c1d0a40300302a01540c410700008044c05070903551000d500304502c0d800103c41303940d059907002240805c0c02141c02c3e0100400c0040320000789580116255100301300907010390382203403c0d15041051034080e007030fa0780d0a5140184440038480c18150300958004d6100d0350418400c08192102d01101129032242e00c041c5511a81090407290542c010f5485500000004e045020850350109958036403d400160a4914403003c140d1218000c2c00a404c81025540080d03555a40c8030000c0d00c0c582d8003600c0304640003860051030150001c000b05546000d12488425041c00514200d03044142e03030800b680c05282550b40340d040080c44a400d1003042c1c0c1d00b50030768001144a2510340101420310301035030300071400420b003086010f00040903861065825 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 539773201 1250 539771951 539771963
    0x70e09011512050a050f090a0b060603070c12180b16020d081e042d061101272f01030203181005040c0f0308180301020708030109090c150c 61
    0x304100380002c454a440030410b0b0b03007505250606100f0188007540000f845400c1d104070000003074448000316680d445c0c00e038070701030001c003603a03000b0402c035243c0f0070015500b140d0030f8035000807251559102e02403200c2d001070755100458900d0b400540c034004403203d4040242007204805003000f1110390f4030341c2c2c0468a480002e00c034444450100781000101e40c10b594502440c601c0110b2451600200c42d401d03a8031500a2000c04610203c52a01030485c0c41501c0c1c0c100040083d0448016103000c0c401d40780011082504c650554a52200350200607900d000a610304e154111402c18a501d20305084800150f4498480e04100074035490701440c1c00c990b91091003611086c81d005990740c2d6515140d807000089010a124030b4060040e9420081080d900103074001c9009032000102039071b8480705d4502c00000c902c0010309000041c00000000d00d100b2500c0e900d400d41c040c002501c0c1604541e81d0400c41e0340240c0000b0350380c6664094000501118541500203410741040c115000748500001170080000540002c0131 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 539774451 1250 539773201 539773229
    0xb0403032109050313140604210311150103121b0b040816030804022107050d051c0909110708092e0504031407030206030115020f03040306020909070e0901 68
    0x1c0c00041d40d112581d110f400006590f25545100c3d51500f12002d0781c030035284040b40c00304104240b480c2040845044410031450003c02141e400c4d070780c000303c2c0032480c819020320803110702d9540740700401d22604040004080c0ca0380300c0c540c1185004d0300f544403070114140400600480c100700200320001c4844015030804503200d19540c0d0b03031510245034030841b18980011860003411808040e00315803035a0180d81700b11401640d102c41c50382e549800310700b1105002e03041c0d0b00840c170401090030a0001d0700e03143c0d4050303030980d01c0014030000a00311407103900e090800010001c0504200508882c890f0039110320b4102501481c1044680703c1c07204600071785509612070703814020010403c05202c4e201a442203003c40f41c0c040d5030028500042c116402501c026600030380500038031041d40c940802c0c1c0c0400c0da03500030042400c1da402c0200039080401035080d80410340c0300c0c183d51240440b20400c0075000451292a0159444c4e418a0a2186c0d801014200c0380500c480c4000c4c0c00225611050700300d0540345c000d03400141c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 539775701 1250 539774451 539774507
    0x2040b040b18031501090f0c02030415030207060903020d081b0403121e0522050d0303020a092d06032c010b04020d050103050c150a0e150a0809070b040303 68
    0x40d05514503910b5030610408581d00c03a0840e00241e0380317040350b40080d0304100350320510b41c1c1c10b003d0300c0c1c40f00f8000c40180c02c00c02091008502d01c030500142418980380040c24001c0c1caa60305821210340f4801640035a1001002c0002160700022039035011250b03801101321460f03080b8440c162030103140002451450400b85440303243d8410b0000d0794908800001c0d10f060041040c8024019601c82401920011003107400040514103d0200e50110b0704050b168a541860319101100250089003089041010a80c0d000440500d41c800c000c490400c4a003c4969844807600d03040c299031400e5004105041c03c10000603420084d0701002c11f80007003401c1200c0c0c51000040111b07030041003e5a0416032052012900140c0803006130701c2103050702d100f907007100e0b40284800708020041013001002d0320211020005080c04d01c0c42020b03c2141d80360054080303484121070450005040c0c03c100e03d208005480d960070010481d108102074801090140700043c5001e06580700100710960201d02d5000c606800440310b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 539776951 1250 539775701 539775727
    0x9090709030c0e0417160c150c0b040206070b010306020a0306060305280f090317130213091e0302060901060e0c1e0403050304081501090b090f0405120c0c011202040b040b 75
    0x480540724074192640c8504c01c0c1d01c80c0c6c00d140440b030016200b02042d00720118145170344014040f43c95031661a20f0006640036580e1004c1d807240140308031f0b002030303080c040d4400149802055a019510401003da20b41c00043c0d002001c443c8258045003c260405090150b10050501c01141c403c00030984400056111040c0341e006c2c080c0c070200305802d240781550030424168000526401107050a2910b03400d61240380072445c24526556001c0d50003000298100d4034030050742d000a4001c0c0c4914801c10306503a0300390342c044440c07500e10010340240e003101041100c1441c00307110322030140c510200c3c980d000b41007c8014038410b0091003d011036401e00c81c580508000c20362400d40e4015503200003100d540c0c0b51140c1510380c03100c40402c40040d0001104002281d55051405661846000501f203c000b6503650800c915030b400000c0e009940d0381c000c1086080d81c2080b0326008200c40c0803072278003e084420400000400701c6040041d00341c0d001703105000c1441840300d900c04490864401000041e2140805203d038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 539778201 1250 539776951 539776973
    0x2060f040605031819110a0509130c0e071e021002030a1413080d0b0f190609060c080a0302161b330305101d06010f020a1101080c0408010501080309090709030c0e04 72
    0x21b9030080300c1604101807c2003242d1103001d220300c0392241d00c600bd076886c51003054918081e590700010400c540400d500e1a20f9060340d02c040004184110380508807420400300c101d03031054500048280e150800c814900b4070b84150980c02c2054454404a400d01c41e0700c3d02601401201d814501d4036807502842b4840740d6600000d0110140018040c54088851034500e0300c0456042c0b181602140419000048590084d0030341c00e18190015400303407500b10070b00d03411802507014010860001d41040c42c04408110592041c40a80070310b0340640c1c00d02814420426400c164040c1082402400c2900301040c50401c010184120701d268100802c075520b0700c00c84d56420451a0300031224481412501100a08049080d580550000c0c0c0b2484000451001e0413a00d0318082035019100908009500c840347d403240c440b90350711030200030815080c035464000c0076082d1603003139005004036407021424505c00d142c07404038142c20000c40e04042038001e2466072500218035503032084020000c51800084d045c44048214 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 539779451 1250 539778201 539778209
    0x111010905070e0f07080f0103030f121b02010e0304061b02041820060313140f0f100c110706030506010c0f050a0c0504020f09060702060f040605031819110a 69
    0x9545659031030303c2d50060b070103000300c41200100780034002081070240a500310303030300901c20008800c0c1168215242920381d480b0b80c40c5203108015071307a4401c04c1c401544d4811012a2424100e80d090b5070310844100a003515908003a403c041c3d0402c000803c8801c0e041181d00110217040a0351440190441c000030f001402720702010f01850955404c050200001d21a503420703d49134425034511444462024072919000480d4010811300243c0401030104007650f452842140c071140454100f512119071003420004c10340310000d41584040c0c0500da0039009d43c09a010541594942081c0c1281c000700f10503074400c1d203403184200349944c490200d01e40382d125034000c010544d00440814082040c0c4e24060760390304249801075480d2100c080d0041a24a4607008488000007150070b56801c282c090804c12010b80d01c00b0002720f9200341c007007200c2050a468000500b000f40b5481c2c0720142c492400066222507032400b0001080203070041c1607101009410008203080300c1d5041401c020f03010301d1030001300355041e440e900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 539780701 1250 539779451 539779453
    0x1050a18030c06091508040b060405090a08210114010906050a0c0209010b1213050714030a14160f050303120c3906010e060108091608061501021b0111010905 69
    0x10012504130b41045086003121048040e075040c4100084049410070002e441c018042104000490307202d01d4281c019540040060007901c0300d140b86d0740e803021040d078800301d2841e5036901c04901a1084001000c0c06500500c5442004046100d04600007030801c1c1a9005110601201240c02e951203881407009203603166016000d441d0a507181c030f04140c4141c02003058200880e0801000440140c001180c11503066440002049000c1c1001c0c44806d4a104400c200c0c2d4043c0305448207900440c161050000c41904484c010300b0190010900c5080000c0041e00940c0c184402503900708801d8030004106c03103480002d0000c4030020385640d12040654031400c0cc43c60035608041d6044007034020b449614503004a02c0c1012105005100c00f00306031105004d10ed1030881c12030400000701194054030031076a20076846010b651040d007050343d10f1044640b250f007100349075622600401c88400300748400351103116024002001070315800c24601c10b01c201a500c950303040200d030b1200315480c1c000c00d40244004d40c0d0701c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 539781951 1250 539780701 539780723
    0x23061303081e07031d0c1f03020c011401031106030f0c090f100e190e0f070302070203030d0902150f0315030717060a050c0909070507050c04060314160501050a1803 72
    0x424020060f143c0c400c510982c49840d01d10170461070f00002101a54124060006d5084000e0340c1017155a034103d401d0755400f03264003005207180c105002c0c072070110004d000180c62406941181000381c2002c0d40d8504ac01d0082c581081407064100c580c1d5080340c4d002c40140001a5100c5241001c5404440710700400c642100e031001441c00311941011a00e88a4041a548445082860700b50100c989585126074540c101c40100450801c85a11883d03e50001180c1009494016103901117481d651084181d00b01c03a950780e442102c110306d001d2005215030b2016010039414400142c403640c07518803001d40b0713901041801121503105034500303116000c02050b210303101c141c0d003003c44c04500382ca8a07002c40d00c600400d0700c2c2c800000e0ba405418000e80350f03880e1024082c105d45a80d03900b0140c8031903101e0070090f1410320442d4650703015543c55004000103188901e00c8aa01085d01054082c58113824401c1712141148000307042c40a070b60310505031250029946006126900000c0c1c4158105940d038102404242d010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 539783201 1250 539781951 539781961
    0x20c0604060512061e1201060b0c1c0302090105030114030a0b0903040f12030e09040303090b04080405030c010305061c020d05010204090606021203130b0402030c0d23061303081e 78
    0xc48090143c412a00101000c2d90b41e541081000c0c410000800ca00b228072481d0400300b003401d05c400c1c000540802400000b4603036031241d0030112035030800e18141056900600f103501e202001440d1380217a20b040d0b42800c0d801c3c005c2510000e41180014010b210a240300c8038500301d40d0303a0f8208110680560040703440e10320340c00c0140c0d0b4180c603544140101c40c0d140448100028140502a5810b0740254140d80c850529002a40420011032806803041e41015195042d05021031104241c0500945c81510707a1030b5624905002e140c10070f04141292410305107054200b00700d03500c60b940c01494044440710b110040d03218500c002022144840e101901541c4042404608015694020b000356206502103e200c400e480307150208522080fa689100300800d4281c10002610220803290458030003425545142c108902007448801c00000c103680b005190000c0c411100c0f086503481002820140252180389480340303003109174840c2c1d8940142008090000242e1015000700888a82510890480c425043c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 539784451 1250 539783201 539783207
    0xc0d05071d1504090e1c09031203140604020a11010e01060f0e07020c0105030601030b09090606040609181407080d02031c0e0c2101021b0c01020703020619020c060406 73
    0x1c0c850980303405150968500055162590140141c080c410000c2d502e80b905214400000d4012503501035214810f03001114445400a440040c80103100e94a000e2800d01d58109841076000009140c01071501e4004403444076010f0160042e40208181c0e4056600d480d020021a4902c2c000b180c002195480c1507007419440a043d003242c4102e8044420300a102c54840200c440b01e036109444082c09a0300101c100b840c1540242c3c042c3d980000c05040c00036110100002003614410704681d4401907800c5501049a50b1074184110405048100320401198104004070040c04045075006859485041c20040d2160360400c804806003904006466a010310f801019690341c101101088140003847c270074541c9914a4442c0007180e038040d10040001c04108000d000c43c41c50301e036076603084400c0d88424a00c2002d009000030714541e4840d2000450b0320b059203400c142071243c0801000d045400c00001000540c1c1c0f6001907074010703509900810020b208011060b8a810115602d0a0308800007103070000d143ca030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 539785701 1250 539784451 539784467
    0x30f0b09091009111c060c05030903041517010e0a06060302130501030908040b0c031207020a1101080405010e39010818010219050a0f030e060109021809090309130606050d050c0d0507 80
    0x1114606c00c1c066004184010381e103034001150a060f0329401408104600c3c010040918001d241e03078107000d40303c10510b01c000c15102c0d05c260014162000c268062040000c003030302c102e600030091803408508001d00c06001079401003a40c46828101501c416140c014003000030100d900074010054645d6540c0d8040c04459142e80109028034040c990b20000a9541030000c1461000654003050302598010100c0041d203e81602a20071354141d940d82114407005001003042c0c51020a000f09c0c031104111050860a5042c07103600481c1040c00340025410060b0f0b60000242c51300b00013031480c03000700c900c4901e000900a000f0080401c800c1d8044041480b01143c00500034503014203180e40300c20013080e07014400d50130303910707003c40301041c88d40030310010020b40040c0c0e800b4149032499802002ca1942c2c0324000103000721030a9032118615003001a511509250050000c442c034a80700c41c09201080c60024090300034024800340c0b100007511000042c4140d5981e1040300c81e07509030b000c0200018100140000d010380 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 539786951 1250 539785701 539785703
    0xa03082a040305010b0a0b040f060c030c0203060708100f0b0315120a0f0638060702031c031d0705040b0a0504050f01090606020f030d0b150a030f0b09091009111c 71
    0x40a1b0240030a04082e080221400d55090000c4c051800746440d404851805000d0300640404c60b14429407801a54140072042c0950013541d1410041d040800e000f500000041d4042105c0b46e80c2c00c130080081c115100c060f0b0364484802041030000d00902c501040208100340003e2145000c1c1c01184020881e00041070100c480c0982e600700b001c1c4c080000c00c591245a110000100500c814039090b1243c00045000881c4d55400303001103040442c694080381c42c0c0101a89420f03105441403484100e00343d490301c03031110044240850b114020309040c2c00c81d03440f01c515004490190351100708110720b680b9002090401020b01a00030030580c41d01001004540000b03000b04500103091040005079144005000b24450310050013543c41d015a91134050001c8c480d41c040c1c150070001014050020480c084042c1030130040756140450318880e00a40b100c100c07040840a5442218094184015107a00007103070704440750a0400002c03440310302d05050800581041d00103501034201103000c045c00603401c030015145 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 539788201 1250 539786951 539786959
    0x14011205030c0f01141b0304262809053304090539090a0504060e19050408070212151503010f020a1e030605030d0c030f020a03082a040305010b 63
    0xa0380795040707a6038006d18000135514000000340082400b04144544804089403080848581201d601c815800300d50091800c080710120b00d840e400c440540e0200403400701d0026454204083d030f04040c0041d5114211b4001e0204029218114080c80342075030840f015503100c0c000b401ca807a240d46003a840040e00c03049841c2540b1003200004079040d5141c0d4482544607100741540d50b24050402c100088154018254859000c0355015000030340780c403507120349009040d0140e00300303411340b030154a19800300c0c03d00c900064025291004120100d41d4140a980f1000e50440310005200c4904400e145800991403003106580301110900140d180c04101d80201920700b03600034030032604c4051406003280219000c00b8007044060200c0c140c0d100304500381c0c08910b0314a081c000398054940740070902d414465010303100403d09400501086c16040702600044040c544020003000780c59a800a20650340580410722868414007e600b1402c01402080d5540481010558030782d40d8034103010b4080c00034103002c2801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 539789451 1250 539788201 539788241
    0x4030f1a070909023006090117120f070b070503060109060503010b040909170706090c08030a0c0b0a180609030801080d0509011409180103060e0114011205030c0f01 72
    0x441606814941c411249622407035901403030680d8140c00703540b001d0800c90213035101c07201c42548a01d0040d1100820070b403100003440719162820501044481c1a0004058201b000300c030309500c4c95001848005841000e10f807662200400c0c03424001d01e002d400b030000d0801589008011509900601452040c5000da0300c02c011180d98140c181e650f8030080c0121011f06000300004d0200240c550002e08449101c1d680c0388203a49450501c0f614150082c401c22100143c84d46040400cac4a0851010800750815030055443c03c05d5600340035000d0000c0750f5009103003100da1800940d41094550220130b81e42441c00010a40348801c0c9446401810780b50300440c049162100003260884001032100165415900d40515090300b800c01950540045041c03c0d5500c2c00400410032161103000c0003950390020495032195079411481d004090707490601c0e030714802d603140c590a0501000e070f01544904443c0c4108500041050b0b500b050341c29485440c1001a840c4185070244807041d80550001a00580d041c2c100c402c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 539790701 1250 539789451 539789483
    0xa0518070e0607020306150a15080402010207050604060203160c0b280c1a0411040f1e0b0a0b0c030d050c030f0f01030b0a0b010905030f0d09090b060412030c060204030f 74
    0x7810f004a603000703500340d40b00100065000d040038000c030903c0c50004013544460343d624070000070750108002c0c14a000500030b40901086580410500015010451b03486061605065000703549004a0702805442804647d60300e041c060711410180240c01a440719a030349403007007407008015550107500030460f1001002d80741d10452040c1c444001c656489110300000c0000c88002d16042c09010f04155103400005841c200b581d5524490721940014001010400f4003c1d613820081e61520910015995030900140300d182c0d587c0c40078510150750810b6034044e01c402070041901c0c0755009400b180c00743c16141c441400102c00c003840145d803151407824103150003079681c84002e000002e020300c0000c1924046101090007103400341c000d8404c4050615040000c0303503503580060b14000c88140269200d4200800d1180040e82c481035000c09002c076440140460221407011806d40d1003a442008a200801f82c00d41b0201445a40680040c641064095407030f1610382c2090307040c01e90b030b40c1d80840316200e800100301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 539791951 1250 539790701 539790709
    0x30a02011508150705030405190308060117010828120c050d05090f040209120d1e1b080715020309061e151002070e09071707230a0518070e 61
    0x203800c603220000404190b03103944c0b2055500350000f4104131114084e002e11503041c0f0580640c0800420301071303507074070f410b0b810024000b400540c040380c01e46902c1048900180640c42c1c000a5200c000c090003090707807546001c0c046507215880512180103114100d164510210568401040c0ca01140150103440030800b031b11131f00742d0300f83c41018a0b40f60012030300994611640340580c00307048603200c05000070307060910448540742800c0344200041e022800890700003c04007090812407280346254242042d0001c1c5410f00e401140c10611002005d250000031401f0400507140300301e10030800e002c0015922400c041c50200d03104d910407900046061100c2c0c0051200041e150702e0710f07018043c000441042200148d06000744400d0b180310800541c40b507c80c0009011003800803551203086d044c0060711250b428410203190949010038041c1259009000c01e02100c1d02c42c1c0800c84038040e0340c40504501803107039000b0038083c8210781d01c00c03540680003840f480c50000541c1d10861090760180d840307d46c02c660903001c00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 539793201 1250 539791951 539791963
    0x60e0d0201110c0c06070c030210120b03011e09030e030d09080c0117040f020622030605011401050a11010b1027151b080a0c03080108011b0f0e03030a02011508 70
    0xf0991640c0903255074055401d20034010108079028131954807000b901c94001c01c0d000403c42c1052000121003c40a84c8202c406101c0e4200c4000c04030006d00080c4000c4000300c00e500c40039041c030504541d9600850042500900380c00201e40009015103c61100c904406007c10741d040c8910500d60260b540d40c91510361168114072148440707100d8a006070307104c1c2e485032221181b035441e04903082b034001c20a00703600ea0b0300b03240404103241c440054034000300c0c10740c038140c816100706070300580ca02c820303c900c1b62a00b0b07a003003015540c50a45600e0440d02c00042c0040c000d003d032000325011500700c00e411100420382a0b00c680d682c03030083c1f080341c10003918141c0d030514079030711403403d1280d0b81038155045400300400d0700c1406108c082e43e44c1001050040099602c840b007070380e80300c202d0000100300042400b808040d040711695005144150080044450310a00466418510800c600030400000654085c45000701d40107000a003024044a0f03d5040c1000c011380200380024051240341006900003030102000101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 539794451 1250 539793201 539793217
    0x206010801050f0c2209330302010e1009030209041203150b0d020703020a0803090703030206150d03261501120b030c220c0f0311090907080601050403060e0d020111 72
    0x81a490880c064034015a107044000c1d0401c5e00040400740011000c10501683c03d8684001400c8034141c03040150304000c1c3c0c09800c500d80c40c0c110540710b007003002d0b0383c00030700740e01101d1419070f0b0380c44213855201c0080f2016045034100035031080c011001d00c000c1c400040008600d620868030704100c60341a500e038400720080c0324410303504080e20802455038030100f80c0e0040c10380f1070300c02c1c01140d0291200350b4a074140c41e00100c0308062598403100d0104185a410002140c00c40c0c00316645641d071101ca1004110700c1c3e03000d008060180716142c2400320074015215808001c0b003840002508036801c1280c0134020b808603240115000074030729507440c14100c1d258070500072408070023401003440b0041d10301446186068403490014000c003060841104078205d0181c0c1c00304c0a100e94464040c40d0303001c8030190448460b4040e07a02c1c1414107012007112511070525650300500b85050684e07240c0e40b4080122251711072504001c003d2428110520350728580011040282e0200390002c4c00013656480042c1031900481034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 539795701 1250 539794451 539794471
    0x9031e0a0b090a0c0312030608010612020a0e10140a09140115050f120603030702060c010207050d050c03090906040213060903140114150109030f11040501090b030c010516050109030206010801050f 86
    0x44200006807060740c0c5c0c11b0110200e82808911140c0d140da01d14211180c540c00304544522080003442180703407140c8100e015003c00c007080000c0341000122078940c68940e000b100f6050201d80502c00341550b030a07410301c0040c1410401440000c100f1100c0c000640c00070322a0111083c51425204203c5028800380c0300d10058420400d420078455a40c2c11007004800b403d0581c15020421100e409600c400000b026201040d40025a80b0500ea1070528901000701030318804208061040c540303116804070888454580840c0d040f00742c1d031039403030000c0d000b48180003100c803901078070311400143c00350000c50200480e8021600388000f01f924001181c03ea4440c150101102103c0c84000b40040b1808031180580c0d042c18903150096503180c0e91764010740b2400490656404160f0030800c0164901130003458050415500140700010b25440800d0b0f031268440c2105d4103020000c1480c81c61240c42000041219400c00024041c0c80128100030352900b50030300441040d942030a00003681e44815031419405480d03006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 539796951 1250 539795701 539795723
    0x130911030d0c1104110f190503010b1204060f05130203210301060f0e030607030b090a0c050a03200d0603030f0201050411061c0c030b120c1509031e0a0b090a 69
    0x782e03070103c80b8050707020450f51007941d0300c00c5001d10b0141503028095902000d50b078141d44041c1880780c5540313183c0419421003044420001402002c9410003a10b0a810481d44000001d49803860010003610003203405070306041c6071404003e112071501445010700d500030b50035910740b910324103010500243c0f10322110b00f062004200410140344600b05006110410b440c1c220b4000c000c2100207401c084040e80c030075001135103484c4000c209281102410380c1200c0002d00400088001c0c0001800c1340c003407009c05005050361406400d804002c0d00800301d440300b00c50030125a41c0c8101090040c000c0c5110301041e800541c07000c980350491401441250301131074200700c18113081c2c25621308000302c40d40b0444844a0248a66140d03900080207406100320051190320041000c0d00c140d0300b404040420f001050801e0b502030340602800d5150100305001ca075800b840150365400c0540d0110b0303c0c00700140002c541e410604442c1102106003c01c2544d1414407407079643e003054581c0d21310543c1d1140402800340c401d2010b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 539798201 1250 539796951 539796953
    0x9050d08030402030a0b040606091407020604031b0236010e010504020d020f070605090c0d08041a0403080a09050114030f1801060f1d0c04080304090b01030b130911030d0c 75
    0x3140c0a56031051005048a82c3c100b101d9a804c0030041064600310303030080d21340a06109500803070103a86040740c1e0340c035050419807900783c0d4020340d900303030243c0050b09118644070442c1c80c0c0b0098040c580308658028100e03a211103200c007600164402c5034004140044070000c0032a01c0703c000c07560014100c804100e59100a079080508100082d4085815211056801c1211180c16200203024100060040b440040d49190000381141826400a07000b4803d032547c128800005100c1420780d030540f00110000d4105c07110341c2d004c1601c54801c40e0409404801c011424090203540201c1040c10342e03d080e40c480609000380c2010b08041d000c00d8881403800c20022f4005204a0b140c1c0d400484200304885c00461125510300a01d05500100c4d04403407036802c0750b4905e920003e10824090740c1c0058240c0122450319140800c156268001c030301481e9030068641800404c035070710070f070403080c0c0414005255540b000c6007000070f0401081c070a03004403400da5498401448914002c214141c04020ba40c98041c000d0300f00f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 539799451 1250 539798201 539798213
    0xc060a06050111070b031e011205061f0927150c050a05040b090a0906090c020c0307062109060203190b0109231f0203250c1a0910051909050d 62
    0x4002c107405150b807400c0001154407c0f084058034000c200402100080500e03608100d0b09150004000a211102440081c9500c4805040420458034030800c00907405070394581d07214900c6e0810405000510700b403c0200180503043d8000d8001c03100c440340800c2220354681054501d0700584e0020390108400b80004c2140d000320000500700c0c0c944c01001002c415803688030013000c91f1440c2d04001061a0340b0490380813255010072540c100744100b00c0007042d446144c076000515180d03c1860b039505a2600382c03002c00361000b060300603402c01c540c445410b54480c50442c41904041e5022460750028505184008005502400c649015905885460307801182c00317108840c0072440c0d600e61160000340d803540c601181a4080c1e00c2406004041e4003960751408883c03030006000c2861194030502030704c4000c841001801802002e005c0320700c103903816051603c00d40040c0c0d11500500000d00e401a1015030400d107441e038080005e040c001e01c1d0983c4819004001c450481d00e42011f4015160040d104482450210364 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 539800701 1250 539799451 539799457
    0x20d05030a0f1b090f0506030402061e0d020c010510060302120c0a020a050f03130b160b040c030b090c01030509120702060d0b1804050106171e01060b0c060a06050111070b 75
    0x380804550040c544000340f042c1c3c10802c80301c00001c0e90108007440103000e0000100d0051001301d801d5401c60038540c001988a21400b0321940400c2040c200c59458040902d0070740c0c41c10740c0403034021500d030044640301c03074040c00089850108401a48038080344003806031003580c4440480c58500112a0b03141d1a040540780d01c515010401d503c0380f1640c80c0d001520812091491001480241d51280783e030444144105442d50042403081c5d90900c048034041c1080c7d00744110b02c0d5002110b8a00d07075102c90a1505043c90b5642002d4030b803610040401640e044001040c16802c2d100313aa0400c5aa51881c040c1a1500041c1c1094050303520b08002580c0540340c1040038201d10780c4a07a400060b05140e41000414a464611002480038000010403007800820300c103003030090040030f41486560344c2e000c80d00c90b102c0d1300501100f10119405a040505501d003544000040c0544189180d6204a04000541c0e00c1c0300132942d0114150a080d008030f070703d5100e001007498240d4088010030031a4100b2100d001c0f250 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 539801951 1250 539800701 539800721
    0xa0305060a1e05040501143f0c031507141308151803120103020d060603060e0c0a0f080d140c01051312090e13050304030203100516020d05030a 63
    0x202001e4002c502a40d54400580e05480c9032001d01c12801d2030030b024001501d00517400314020502c46401c041054540603084441900c032006403181c1000d01c080315540b00100203005107550803486400b1810240000340445101d0f604030221011188000c00302941d5810071a0719400003010400f449200c24249800781020170402d110034800130b601d41c2c420740c0ca480115031008048124103020300038208910aa0101a88030010240d4940505c514184030581030610000307004001900760201031000030740c400009507602c4002407082540d0105071aa4403040c100c2001e11840c802240020904600c048100481c0c1c40300d0040e00c0da0104c007140a84080121104180d0818001c00054050030b1080c402c030ba10424a00399206d09880c25410140308040c2800303a6072041c0007000c0383c140540c41c0311a0780a03074801c186001440342883d607858114190301540c1d1001350144520102c226480845400c4144606070b20300200b0385a6805040490b40c0e240d00824a802007441000400d02d0310003d0b4214a03901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 539803201 1250 539801951 539801959
    0x50c18040e0102070b1006050c152802041a03150609030a0f0302030a08160206061012060e090d0c080904090f08070b01090e010606091401090e1305060a0e030a030506 73
    0x40810640e4a09a84c4840822641c1c110007000300030040f000c03006480050030301c80c90554101114001a290f0f184801207402c07400c00701340c03400220a1741c00d8100c2c9041139041d0b55480700080403042e134048086e4002d805036070310361011f200000c602c12180c101500c0c40b41d0030b5512103001900c0007101b0b02c04254040d0600a41501900d0300c0e00d00801d8003030000401d40c52003a03004607907a401d2918014000c0c00017030074882c984485c5100401c1d28560016059410200846401c00003104184003601d550080c94100000b050070306c08000341c0580b1030900a4071550411082c2d074080c120b44042111000c4440000400c050018000c1c4030081c1460752144240380e118080310700d907901407616460b04503000074804442d0b1203602401405440568020080511000780090019909012015000010a0003004000b01050007080c0c9668070a46a280c0180101d550f40b102500b07103403005d41d84d40b0a000b407003940c151090501292004c9500e00c240084a82c1c040080c6040815203c4118081c0101408641d40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 539804451 1250 539803201 539803211
    0xf010302090a14090a0501080a021201021e1305030a0203061b0d110304020f01031b0309110d030f02010509060c25080307020c03011407021f0608030406090810050c1804 74
    0xa9a1a0300b000c00b8094040000c202405402c43c008108040c0c0d8014092400181048010860710a0000708490780c0c0341e040b6101710345483d80b40c2c84180280102c0b01e9514070900e840c0600101e40540400414665550351901d01c10180c461050554800c08d0000094043d840705000840c0210040b48a601000c0d442040620300540c6205500943d820f007000507083c9103000080c0700851501004d151240c210a01b0309120500a00401032120000300c0460010b00d40c8039000c501c00c00c8144405c5d40c207402c034002c10249101301981001003c4406180c400307005903207094045100c074040003404904c140b060140151422820340c020f40341d5000b0f817140d42a0203011028980000410840107140328209503401004076036801c0003014255112410030401d88100c1c20244584c1ca540810b500182081d051400c0018a984025a00042079035900c910307411700001c240421415800843c10040710350f15000c03166202c03e4844408101d400c1507508201c3c101c1d0401a0038030a2004240303100c100f500003400015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 539805701 1250 539804451 539804467
    0xc1206060c07090c030c1101050712020f1b06040507090b0d021011060a0510170607050a0c051005070f0e0a0e060a03150203010f170d031a0d03020708010b10020c0f010302 75
    0x44d61103100311000800d4545050303c911320b5000110342c000303440341d00c000c1c00641000703040034064140e200300351820540c000450000c4401c084d011a903410b514401c000164503005520140c0f11007082d90100d8160250100000308006540074190050320000c0400c00980129420490980f008100710313001d0003910343c59104e8514050100c03e10803000140d020807585001c000100e09081640c000308015045106000000000000c60300e0340007505007031150344c0d40d401038002e64184002c08002070240c41401c503144148071003900614040c200380d848100c404180c268080e1400c540a03000d89030040f80d1924200040c0c0301c583c1042e0303002a4082e1a1340541da8907500e41680020050051100d10354000004102609005e60f01000401c205a002e42c0d40345a1065465200d48140d01110100f688510000024094143e00b103070f100f0000070007682081b80107250107511b5500700e11402401e03518215816680d41002c8150f2070034100190301911910003110304102501003210805410168244241c507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 539806951 1250 539805701 539805719
    0x30712080a090510060f050105180607261809130f03031514030c030a0b0c1c09120f0504081002030c090a0e0912090a060c02030a06020a09030b0c1206060c07 69
    0x10ba803810513400c00302c1c0d41800c01d82c581c40d04000c50b81c01a0b041003010401c060890000d21040c5481c41c0040361056601e000d2400d0a10b00b07410f06112007003603286409900380b40180c0307200c0100080071051814a20100c250b00c10800051800c480d10003803841d10305d041e4400181034190030300c0707824802c0c00e000400c91840e4413400107001d0190003403411141c0200340741e40f00d440d00b0401a01e00d400200c0081400882e20394070a41140c0014001d000c24032404511450390a404a4201c07100c0c1c1048041040f040115041070b0b080c0c071542e1621312000c10515001c000301640704208490036240044014000c402c10710046070001d60008208000c4075070148002d08a580d18521104010489100384011b41d060010005040441c46075070705100c0c0004100104040d16500141c2040b14114148101024800e0011a0034044902c10080286100140c1440740076040100701d02a28002c1c02c00884d01d564101c044c1c0090310620440c403120b184988001180b602d0101d00514a094113071050390b8126a44482030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 539808201 1250 539806951 539806963
    0x7270b1b2401090e0a1707061503201c0203070b030108071502030310030201110a0609051e16050907050d060612112115060408070e060102030712080a0905 68
    0x41411124100c10010446003550642e02411260303104000e0840344480c2c0a98802400000030070a042e408045442d20602c0301c00d40b040f00340c00a005110340e42d5011091441c0307010501044a4296140c90542d002890144500c0032402001c0c2c0b4900011880c4000108034150b412005ca0340341c80343c0300f404a40d0b004e00001960007000b0032402085114180042e00740c1036030140601c042107500a10030040c0c04110030303c242c0d00301da4080c201509004407410b4031504080d4079000103031516003006495002c0010029000d2104106080c0c85200103400003580b540301c2c00701e00203030f40340100b104009010b0381c0350003100710f50015942c0c1002803500f17008000140a0b07601c650302c0000440c48075042c2c00c2e0096203034056200b0355513900e107407145841c880c12442c1030b40c43c10740040030003810440e00c0000d100c20300301e00680781e0145004008984030366841852a03907441e41350089441491502002c21805e50001003a98181ca80c00032913141050340c450f40841d04550000e01c0445026190b141a80c040b81083c804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 539809451 1250 539808201 539808223
    0x4090606080607030c0c03080406021309021603110a0c050603060a0305060406021206090c0307120e030706150603020c0607120b2d011409040f0f0e030307270b1b 71
    0x15001c0b61074072040213421580209440c5060040300381d900d00c00654042c2085501c550701401c016180d00d104103444860085c03036005403101505c00034801c0c480d0010000303042e01d1385100e692410b12074850350300001e4980c901d44400038024020040309114514052014503401032002d44080d842580d07e841c1d061505a0641d81601c0f91a80082d105a420382d941e0b02055204805940ca401035042c00e01c41c003100c61000030b2100b010446095a8550074111f583c0000900010800860361110345600f844002022403441c5045486850500011820b01074001c0e80c6810440300c2c081c0059a9440d0707004e40f0110000c0c00140c2d035003036403a0212800e43d5201400d84e140405401354041c003034851124511440004080080d060000b242c040d0390388500c0784404c030bc4001c001074030302040340c6200c40382d07007006441d080c501c4000186c10300f203400c4c0c43c00800001862041c00d942d9202c0490780c00c81c284c80d5008100403404034040b906103040c188110303880000200701c800303503030000d070214100c2c40f9140b60700b44040414 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 539810701 1250 539809451 539809453
    0x160311121204060b1005190915050417010c02030f030a06050a03060b1804020a0501140706091a010b1201060f120e0c03100e07260105161205060117060409060608 71
    0x28401804200d04c0b62240000081c2c900044a00c07240c200070b0701c507015043c64006016140c4d00d0030f1250302c0c8264644002403160100409041403600c001030714981060081e00300d00720041d510400415414015490080c0c0b42d81c014518184c03c0d003c4d2135080e6440200742c10102034881d18005100d484255024002350300030f07007001035200f42d9042046003141e2110b14800685c10301d8130510015030b648501e69402c40301c3c00d090400c0036214240c901141c80c0110000030300854500700e60042485084c48500551074800b0305940441c0c0e8944404a03000e0240f11441409203010000502c1020302400c5410304412440c04c103201d00082c1184040161800d2034a559071503004252a100d860408109074090a000c8500503c0458180350321141d03610f08600c16180304003c00c40c44041b2060403070455440c0c4900d8034009008a14002c01030400300750340c04049030000f034804010b440030103903240b00b4035000740016901c1411624903070311045a80034020301584d50003990360140c00002200307481a8401860190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 539811951 1250 539810701 539810737
    0x1150b0a090f1203110a0b0a020319020c060402010f020601290c01022d0f0702040c2006011d07170411030d03090c1a22360216031112 59
    0x4a4005c028003d958502c400690044400000084107900101d03801400500016100d55a04203404042420b078408403c910b840061494020309000c955540b185000381ca50003602c2d010228200c1e5110002d2194801c0700c0590744481a202d050200404882d05d0150103660415242c2002d080c00ca9100c9a80c2415959030801e14280282039800c407150b0661564400a08000403150703804064811900c00911440e0768800c0054502d0140382c60307580000410002c1407103001080500d642d1001d007801001d41a258212171008a04e03c00848240308100035030300c0007104221103c0300030081102410480740211071416041e850f840030415000100c1050f81c0108200d00103080142c0880b807582c00040502e1322810441d10415820703000c032140c0c42030021042c2511244900d80071000b484541016485441c2c540f00e025030048034011132148500840c15404d2070340c103900f004e1012481400207841c0d4204403140841c0110303008aa0350264205030310242c65500b000b1a2440546900c48031180040c00d00301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 539813201 1250 539811951 539811953
    0x6150d0b09011406062b090c151202090a05190305030a031e09030203040e0408040909150b0d1e0203030705120417030304030903080c1515100201150b0a090f12 70
    0xd50302d040e030001401d1743c0321441c05421100019410002d07a180003030324078400b21200c03045001035100318202900800c041001729110442c140c01052021402340009101c5282c00f200b009481c4203e9a90f100700822300c00c2c40301d10b8041032180001c190015000d21700d114103000408036205200600b4010401c5d640068000e20f00c0109112a01c3c1d0f80701c1a1220a02d031580800010b40c00200b04c0e01540c81e0440036030b4550780c492404400394441c541010740f1f92420072040c0350400c442c4d07d003158050035402d28148038032080700c000e02041040740040500403100409400b80c00340091101030041c240046d0503207103440400d44078603203000721007c5442c0003134030002420001d414a41041d250b40c41901d0010310714609103a18000c0c4a00300d03a020181c04400009a00d0041c000c040141c1e02c003540b405040620340307280c914041400d81d28440d0980d4022a210301d00300d100b1502c1031055032200b11049907034a03005400c06060036065005860a10140064000003003801800d030790203400246070301c030b000700910b00107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 539814451 1250 539813201 539813231
    0x1805070501020f06010e0f090f1506010e0d0b0c0a14040312020706020d090b090a0503010f06060818060a0b0102011508100f0c0e010f03150b0301030203010e07030506150d0b0901 78
    0xc0d20b410f1400c207402640042c044848800744072508171030501d0305c070722150b2200055203082071480b00103825188240c0e444504903007105152144a5802622070a01c018082c00601240d1412808014418a100c000045100440d040034040204041c50840106c1e40741c0d113503160071980a9001900c0d0110300e0046020110360402001006d4040c51001e013043d41030701203010b010481103001d4075081540108004141d9101c3c00752400007000010020301400c1000f013480c0c4001c0039140242c20002e102e02c00090100404031465072095542d0200601c0c55070b030781e0a8180c0c01880c92015480c1155200c480311442c14404240c61009090003201030425502c0000e000411101c03500082040f850900b030350038070a01e0704400d19821348103080c2010040858880422001058914200110403000329004188d01541070041c1d030599100358020088407058410850341e6404921008205501c031600180c0c80c48800300d4840c04004001d03040f8040340340700743d80b2807a441c1d20449446046a5580300d0b21008812 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 539815701 1250 539814451 539814463
    0x801060e090d0c26090a0603230c09090c09030c061806030a0f3204031422121403090913080f042706240e060f04231f03180507050102 59
    0x805003420410483d100b01100401c652700500c1042d003a11100c0018104000a42107900500c1d000b407490304030b403504c044041c00d076030000c01285000c4d1091002081707c0e800c004e000c454188203103580c05c0483c00c4021041203465400105580c041075200e1516880301103050191041450310408071a411286440e4110103003200e82c01c400c140301d0f140780280008070350402d50302030241d221908102e644011004010108200c00c2c2c1e0910821092011300040e11114140c42c3c0c4800c503c103603c104180301100621b10795a0007060780c0960302521070b04c04100c004044044031800f01c0e200314861810400d0400d034a40050300158031049945440400182c0c0356a101c5402241d145501c00081100b24103140c070f00044500c0e0a00f4400c0b140031044582c00481e030050708240303240c14004201e81d9980f5091140450190131521401203a045c80c1300e41c3c191300f9a901454000448409480840c05600c080c50500894054003041c0d024036540c1c451591901c92080c541018580c025001001d200d46008002071a10f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 539816951 1250 539815701 539815709
    0x220c091809020102061f030209091911010f021c0c051903020d09120302060403141e07020109060918020d060e1003020a060e0906100e0612010801060e090d0c26090a 72
    0x682c11400c0318410300600f0f07884252078040e50302001c9036541f81c0b03441c0e00e045030383c11032f0780900084480c19004001d46003c081010710707400e0b80d81c042c071400440000c0c0e9442003480442c02d4006583c490131503d030391080b43c0600d10540620101c65000e0b0414000c01a5134142003810ba005800440700210595000a10007006040300401c0811032031054070b009440d58000b43c80141002613400f07841c81d0354034601c019943e8500801031001e080514626030119540d10012040740425043c800004080d03000b00803880403100d41c4500c22510001d950b4814009511030380742c080c981c0f0307130300d4a020501e00401c40c02c4c18400c0490b450b02c1c8514500394010480542e01550240c4200b000001101e001615444491504145d0030b4904a0203180314600a50368000a110f88982164010a0040803014141c004904954114008001c1c054517403030700e80913200007169a8622a8001e8208102c1036204102407000d990050021646801c070381100c080340c0f20008601d40c0407094011624005620708003d204c0020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 539818201 1250 539816951 539816971
    0x1511070605090d030c0602040f090207020f01020c090112030203070c091508010b0307050d050f011b110109030e06030403170a0902090f010609120321020414220c09180902010206 78
    0xc01c0ca00001082004107000c001c00700480403151750f04114154040e01c018050a0141d04136640e01e0781c10b100025080070005920400700356040190550003c1400c82c2c40040c003a1010003582c0c00c040d010410402d160400710210f1000300041ca001c80c07014001c00c000713071058090105599400501c0e01c40d5400154111012a034900f40212840da50005a030b202205c000351582403503690f07241009810704440440c81c180315404d052440030035181d0105e0800c0003620b5500c520700c02c003008510550032940e25100003008680400b00c0740d082490440041c5900c1071003850841d050010b685181000d40105840b00402c031074481403100c0271460f045507940ea002c49400d00c050280c1d0b25000005203c01e8241c401e920340c40715140312603006d0510441489800c40d030300c010845241880c4217200c4000b503205114010000107603002e00100d0785000c01218224200004481100c241c409540e040103041880010043c810340c081c0002d02e107044100c40340000700c813840300050b1607803040c0006070030b2550007030040d140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 539819451 1250 539818201 539818207
    0x9070201060b180f0603070201141605030c0d090f050708010c020c1c0c030804030813050906010f0e0307031401050106083714160306061404030b04020105041511070605 74
    0x15a050a494103507082c83d0540c00f201100c100070401c01e001c0586015002100082001480341c0c05402c40c0840c03c854010800e815a280c45c51443d10b41e00c20b08809001130420800709418980c45806041c0020415a0010303010140741ea03a8444021805412100d5400250007000100005e00c10a0a1185107002030038005c40c559001032802c51100702c2640d0900b003266010307004c3c060f80d8000303070000d158401c01d55903485460b414510202e0300000140701d581e0100302e07008106410316000883c0940c0381a190b00e0800c50f0402e809a9501440846e05a0148200d1900002048080002e65030790303508000002819414420020981c1e02c0060400035985e075100e528403a04007141c1e20b42c0000c00900000401405910140203010b81450311807100040c8140d4284000001e642018083c1180152010054981e82d007800b03841414030075080681c0401c0078401080400c11406495500c5403052501e07034a440e80301d00c426290401880c2c01803001421041c2040c145440400050003c0c040038280303541 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 539820701 1250 539819451 539819459
    0xe011a01120c0e120109080c0709110f03070c02030f0109110405150603070503040507051f0e0a4703010806010e0103080703030e0a02060d0f05060a030b07140c1b0907020106 76
    0x120f0f414003044031500039603201081164011083d4041802c455000b0452a1b480003041c1c0000c0e81d0303200c5030064140c014902072040209401ca03c0440f40d0500341e41d100503045d03507120b020607941c41400752000c1e42c00d80034810a42110401c03c0c8540400281f02e0840303440e40044410901c822079100a000c0d0944952171300301030505659030016039a00010300e03c0c020383c0c3e070303507551034003505100c07541e84415001441505405041c0c1c1c0310440018107150035035900c3c000240008100449107005104840c4542d14002009054142149840e44c0f006c0c0c111a4031044080780c4000862041084503510700070346d0f800310050044030310a008550040c0000301c070710300d150350654640800c10321070700c00c2c0101030540d90924501c00e410240070201850382c004201d5511407004034640b0010707004543c030144980745004009042441e1142c0700c0d00a4a800400c00f4a1654403210142c031450303c0804c940c101c1101c14003a149605204015581c041d2100604c155400c00d0800248601c0e194041d10030030a590610780144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 539821951 1250 539820701 539820707
    0x60e060601081f0305060f2410050d180c0521190f1208011703030408091012110a030e01091a0711060108030a02072c0601030e011a01120c 61
    0x20340c21900c6101140c51140401c82c190060f0302c40d1341e000070564060388003003202d102c072070070869071051038941d4900c0240c0c0756401200300848840c0280d19442440fa40d410b610785c41c8643c01403c0342c00300b13000d40091a000d869121500c5aa48150200c600004c9041c0c240540c0c1842001c0291200c00304c040e81c0000e51a680703003283c450340e45280094200005040e4a001c0c0702c0409142034595400c800c80012415824900500000e001d006020704c0c201580216121454000100d920903030304038071054140704006040000c0015005045002c00240220b182d404195030300c14a0040301c440444103981d2588000050281e40f902d0421105c0c50340750407813a50118005400322120b045014081e402c4583ea00e45055468010b400c2da00d59140c41500e0001c50040300010003013044003011340848030304a6a525100c0b175441602180c1000030201c1040000000c0c0d0044443c682081c41410301140b00c08a120300c890848550444070030502c0b01100b144080c03540c201030003080c00c4c2c2c10b010045c4445c10182c500a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 539823201 1250 539821951 539821967
    0x30210110307061137170f04060b06040801020a0e04050717040c180608071a19020102040b0f03060f040b060f0f070819090509070f03020d0f05010b0403060e060601 72
    0x15000136110b291340508000040203d85206001101d21444289420702c0c80c000d40342450104400c141c0c07811254441e050241d810411a101014040303d002d03500d4280b8440030642c0035204841c40c0c0d03101c104d800c000e6a605070152000e8401d0301c000503216850540000e1800d03000011150080e8604802c2c04100d0380e002001d2060400c0e04001c41e8866280e0345030a07004904d190340700d204120071303411030041905000d4018000701c031034040464040d076031195026180100905105004031b0000c1094407640c88030340c04070801d84403490000606146c0d8501c03404495520a25500e0351108000042040f00d00d410701a01503040b401350b41c100040c05500c004514148684070b2480070304c0c500401e0250850841e9030881c3c8000c0d6000d440c0944848c003520503040c020340000300c0d50012544a140110f81c5080c01c0c45058418103ea41e904c901140c9614415002544070000b15000641c40300c00074250300e001790080354024200502520fa40340e2071800c00c0c001b25004c000c1120455041907060000581e841145 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 539824451 1250 539823201 539823203
    0x30c1205091c051501060c2607150b10030f0f0e0c01110703020a090603050d0e091816030302030a030b0d08040b03100e090309210a03230301090501030210110307 71
    0x2d0405000303a2030924030f1030080d140c00e0960060b040c44001003501caa20040106440f4413035015040d4040903412035800e0b01101e9441c070007028505003d62408105203214048c03001001c91000a1540b00200c045000100c16104950100e0f44412019520f506d040c170612031145052101040704001c45601d2584030340c0d9102e0510b04202c104400c0b224002d0341031100100540d40200580304003070b43e070402400a0005d51105031181d004543c107840540380600001e10441d03100a141403070a03510200f10307030368402c074824800d15a48100f811004d8203102580019000c0c50107900250b440707121001005040c2c40c40700c80b00a02a04070303146203600081c2d0300030654080e030320640c1c8035130f40302d0303680c7d16804e0001c980b01e40c418044803900c0420301c95082800310060858420641d40003000d1540e021010b1000740c0d80d01490007803980002241404284505025802c40150981014070320a1100021400350000e0b0081a0a40c2c4e031791004004524019030100542c5a980c00c08151196071405660f403680200e0700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 539825701 1250 539824451 539824489
    0x41104020f0c01052d0c07060507170a060e07020703170f1312020126151908013201090c0c2a17071202040b0904030c120509 55
    0x36940e040407a25400340e40d03412100034020000f82ca40120165904900342c05141042d50b6080e80c003002040c581841c641c4150b401016162405245907501d01c0105402403485040102102e100000c402644100d00d0180e100c43c0c0000c22030509001d2450000d80303000c1d00c0b840c250349c84000104009810780003031400d0030303106101594130707001c011055200922402182d14590b81040401181000030703130a145140500030783e220701306400343c0c0009070046081c40f50b50011517541c803000a86807503504109105508401f4028040b4580c1d030100031054a0741c0303500192841d07510341a291090b1094444400754070624007080111900505a0000000700180106082140c4400e003001c24a805014040c0f103050707000d21000615094900256400801850404001807101d00c0c0099117a43c151104252886081e0140c0700301c40c0340c2100309458030781005003281c100b6224001a403043d9a2020424440c87c001e445100e510000d174034002c486003c00c04d2a20b01805018440f00505441d542032007041511210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 539826951 1250 539825701 539825707
    0xc01210506031606112e02160206030907051c121112030c0c0f01060503190201090f0f0501120e1203090a060501150e030304030203030703050702060f070501090b01090504110402 78
    0x901183c24048000b80e910500606800c00041c22039100c0c0340030004100b00d02c1a0b900d5819010016444d800b0350014401980c050a0203e9514609030380c01400000c030841c00c0807100000c560b010074401e4008941e400c100c0e8000e020100498100841c2030b1940107015950b1086424055960b103d00c0036005100350700708001e0000310100f00701e00304808aa50461400d6050301c81c94855808a03141c0c1c810110042140100b582108000320705010302e90640b280240034010070f01820015445401c8402c1046e41007090b02c01002407003c074060f00c0131000e4200b0801001d0080c0c1004009002e0030b07080e1300803020f014503041d00d0241c040004943d01c45040031040360250750352100600c0718034000103043c010705214941000000e620360720540380070b040c83d01512865241000581095264026072201940641042015a000030b00ca2001800810700c0140f040c4d0070401180c40765002c0d03812002040760039a540343c0350403050149881c1030500424840c0c00034401807506036540841034001ca4a40380c0516004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 539828201 1250 539826951 539826961
    0x60f0e0103170703090b070b060f03030c1b010c021c0201090e1504020a0c080a020c0a2309090f0601030803040b0a0c0e2214040b1501080408090307091d0c012105 71
    0x888400780103290b9040120303140c9440e13043c08c2015030710030360b00e03140b1504010a952280b41404800e85210013a2000505003803448030f4400030800030041c40090400130003001680042c5d859000c0103070300480001d000008000c0520014080c0006600100081d8461100308104086400200071500ca000d6602507141c80b000001900d1640004800070f040210114042480a50001d11108400c0302294009015560340d548030381c2c1640c0c030b05040d410000c0c11f01201e40c0c10f81441c00f40103030000080c40844480b5003080c0100390500c4000e80040790702030000420311051094407180d0340d400c2040014100b040001d0300001510341c03510210030314004c00601b060980c42c038444018800c0c250600c0c0805100c4400700d502400ca801c002118101c501070808400305201c00080841001a060180c6444a02d502c032501c5468454200c000310035418030510002042541080c000e030f21242c0e5081244d2030200641501103400c012102030620b0402c240078141500408008213200b801c5010750000050036265 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 539829451 1250 539828201 539828207
    0x6031207030522030f150c020c12150c0d0b040b062a01110c12090f09040f0c0f0501020c1203030703020c01020f2b05190e0f01050109060f0e0103170703 67
    0x24850702590981d000d0100006000d205c02c410542c3c1d81c445c06d101d030b102c580711100d000d0884d07181c82c0c80c003401640000303030003490f600708100055201040807003103602030481d5049100c0c0a0300211044405120049503007640c1e0425409011500802158203001c80b50700800420414000d917240e085030400e4410105015600e079210398020741c54440000c1c000d90341c0706074142c807680d40005030190b06403154400609800f09003200303440b10004010242c00e040003602d0204846000d0182041d510f81014210b4000000c11000384600200400c02400000714640400a400c0100c100600d034010524184110440c00003c01165407040301c80c1001070300c4002450b0894024000e01a202c0b4000f88001255200c0f554801200424180c1141e080d41c4c00d480342c06080c00c10b03281309460026410035000d10388054008160001a08101c081c4200d6038611142c222403425601c007a40320a03040f955801d0180a030783e949082c008081c00620140c481c0c2945182d40d60300c84034000300c880c8905210086004810188 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 539830701 1250 539829451 539829487
    0x90a0203191b0e12030306210f0715180b0c100f060e0916151218020310201e0714010612080d1a0d050f06060312070305 53
    0xd54003000c21a521000d0100b0014010325901d0401141c0c1c51002654240342205109503012001000f650030f40d1140410702020100d0f400d4003842645500300240040f690400c1a41c100c590540b00510040d450032082030884000040c8000c1040301c1c403070b1515420880c44039003074103e8965202d10b5507101c407541c3c0d180703041ca00320140c1500310505040300812450040d07042003040e2216003900040d5511000121552540d00152900340030900e140200107800c00540d003e102107009003003031000c56101180890458418928060029458107955025400c04209032400e04541e0b100c1000301c1e0041260b882809400d00500a11404e000205481a54009800408440c5080280a80741c200030b107400c09d20100109081c0300550b1800e200040c10f0414a8440c9080341c1d001417085240461030744031080540300075100c208450459458034907030754542d188000c90190040c0094007880303642c0070100381050400f5000910039401086208034a82060040700c4009500d820055500c01c0b10026140f01c0c4c03e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 539831951 1250 539830701 539830741
    0xb0309061005060712210c0306080706020a030f080a02040e0a05071e0c3c150216110406180b01020c10020706051803071517010303091703040506030705091e090a0203 73
    0x50407c0b42c07881c021a0507422000c1a10f072054103441c94143c842c04103e80d43c10900602800050225040c54031041c003c5850f10380205500e074015151640360707a41e0300c0c0b004100741c03a62800c0384d41e01c5c410821076907482018065400d81d0801e65070503002038180300a06111018101500307a801170800241a41c010b0302c802001c41c1480b100b0160340d4007030120039541f04103510a003582e40004160f0100d100084030300c2280c620070340e1003441c0b1882c5c0c1e040d600c403000c014880c1d41549801c43d0781c1c1d280118142034500420710101102ca400410394280f501c00080c28034034592051409281808900c40e06950082400400c0d10400d2408640315215406441000142c448445070107000d00d8002081c4007075003c00b102030540c500d440781c1c00420702c0c40045003158042440081c000030344c109418054800030458078441c81c15620112802c040c0c0314800620941c0c0251b480e100403490020710340626041860700760082100101d502c40415444101080404400611840a8980c000b00090303401c0004500e0040c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 539833201 1250 539831951 539832017
    0x1051b060414100c23091206070e04020424020a0b09030403290a0b04020903100e0c011407020904170a1d1203040905100b0309061005060712 62
    0x140c20281090b040ca800440c940c0100c80c0a08240c0e102c400d00c507400750012401007560381d0500e8401c0c0b44030109030071802c10219212524104102280d0b0b98030805031256480340080604002e080500000e021014001c0d4030900944c0144000c1058010030303401034401c04c1745a405000307846020041207080c94540e00d00188001c0781002484140078001000e0000e4030310503000c5a0b250754901180c007000c0c0780d4910f02040b01c0340410b000118224441e40101d404c140c00a4805030520860400003820100c0044d800351203280d0b40c200a803003601040003006101c1c1000e0030881e041c4051050081801d200e0404043d0044203000d01141c1040809000c841191042011140d1580440d41c802410b80c0118070b5039500740c4d010f01c11003c00a103402413515804c4a1070030b0040d4031785494412030030060500102444050700560303d0000c0c841d102c51b80114401e03002407001c1e103d80e2901d90314488010305260407c5000c1c880c103001c46000140c0403840820108840e00b820420419000048460895480c142c1890 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 539834451 1250 539833201 539833213
    0x90f1107050a02011d032d01020a0815101d0f101806080106020a06050907050a1d010b03040c03081305060d0e01060806040302060c1e04060c060f06031101051b 70
    0x40c040c001c10311400d40b500c00d0f039a00000000d6030440104035100d902d0041c0d4160049443ca06020b040401240d41075010000034240c28001d070740181d401c80c2c1041c0e18020101e07401d4000c011a00b1038169400704845001c4602030003611000034000c10088002080900d007002d512600c0320141c2c4e0701c00c10400d041a00621a0110300b62181c0b0003014803450b21132002804404c10000705465008492242c180d4034240e004213110741003501d0360000b401c4090004205401070300d00105050b20f481900d50080e03e40210500340403080c10204002e444816401940109002c3c018000020704003140102180d4011910540f5155048600c2c2c41d24901ca91001d50710100001e8242a543e00a8000038000c0704000d00801c41103035181c030103035140c0b40304403002001a040400003482c480300304005402021000c3c1415569541003018121913030b482900300001080307400c8031340c40800c00d007400754100c1800d44480500445245540c0c940701d520441020a060000104400000708908901510410000c80071210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 539835701 1250 539834451 539834453
    0x1b082b020d0c0516062d021b0d020d0308040209090c010c080c03160c09271e0f150b0f0a05060f16060f060602150f2502060613060b04090f1107 63
    0x4020b032010100c1748400b400451b0600340c07000380c00380000001c41d4035170041d107007108907602144200c0b000c01c2205a40034040d00d0140300582c43d4181d41100492090316510950b040500400c8190400104070103136660010b8074064242c1d9026030740c024031070792200740341c0d84620f0b00021080c11400703120f04c0444a40440201c0806010341c100d60041243c621090400c030700c0044074159100b100b440ca0b0030481c48580070050800180c103d0308078280000700400441c02800003079441d65110700880406031450400304c607410203c50344030310950031300040445034006903c8a440109400c0180d078072500d031043c200407502900c5401c10108440d423000f003002d60f800f0121414501400101156071781d8011292030324070045147c3b400007944840051001c412440341d9642d944000c00740e140018680d001403800100400019550000041d40e04011a005407a20b80340940c01d000713215500d9940d0103080e5041c9101000f000e0390180031203051741c2038031001265070a02c420804020b0f240e201c0200c0c1d482000010350074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 539836951 1250 539835701 539835707
    0x604031a15010201151701060312020a051b09071202090d0501090c0b040609180f020a081b03191107140a051b090604091b082b020d0c051606 62
    0x51203241c494281c81c0300015460012801c80f40800070240c1c0c12200d58206014002039440d5240c4501041800824803903161796409002c020200d5050300583e00140e80d410401105010140d00880a9200320134216840b2000070203c240c0506280103000340901d8031000782010790125034002401600100715641149401c40c020040424245c1307110304ca0010106618001170304a50440e040c5a442940d02410182c6071076552070007050280c034841d42c40d00310441c03644140c000b41414903100d458220360761500240c2c02c2116403603000c40402001c010010020000c003011a2000c555417032903030005410401007403450b035a200741c4c20f000c0c01030985800c004606010004001180511850a40f44004484880e09007000b8030b05020640c021454030010f405130600f0b51003200c0d411300502c1951482d1030240c0b0765201c0c40c0441c0e00039064075080440824001d0303405200b82c84050b00403020480c0e0280c044140203488564071003e400c00c0004240504044c05010000299607060301d86118031002e540390009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 539838201 1250 539836951 539837003
    0x12070803040504140f01030201050c030d1a1f050d020c0708100603050f0c010203040909030219050102091e090726010e0612010b01020714010c0507080a140f150402060403 75
    0x1489141040c01000302e00b5001c0032140c5c0284c82c40c0882168590840d801034034950803100e002c1c0e51520041c0031030801e1040344e000e1500d40d20b0b100c3e13800151100307210091008200041004079401403076210b05021060344001107640c0003404a070016107944040f4107032400c1264981c0151600d101e0401c1c100002e0040358400411079201e1006c85008590756111079450328444417036140560000e0104100d140050740020014512034030550ba5003890311502c3d40803218801c2e0081d0f845d41e6002c14610000c1c101001d002007403d1080846011400501000848110009005004000e43c061100c0404900b40104440b6500c1c2550321820035a184c20b100da441c41001c40d980c3d840340d00c0420720350601d2030041c45444000d00060b805403800505264111803131020515440341040701c560a004046041440b008010b0402d007400340c02d01802a0034060b403594801c90064400350420140441600b0300050080c0001c800041d107040d01c1d42c1c450001800f42c0c0070740e902c0a0041030740720403002a01c1c3c0844001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 539839451 1250 539838201 539838209
    0x100f180c020f0a1205160507050108060607020d060b04020712081609030f030e150708070c0b03090601060f171e0a05160c08041a0304030e06031b091207080304 70
    0x40000165950040b0781ea403564180000a82c1c215980e040c001c2041850240c91404003420300394904650300060700c03440c081100003542d081c0c002c10303400c1c4059a4085801500203008903000380c1040000e03000292a07491488000303000e05d5880741c050400c1e8032103406031500c885d0400309428048524040c00f1744240340468841030040300410000398a24003e444640c26650070071a8442da140d00c950381038500f440c2075a107a41d804040c900a000d0703442c07454002016038130303c908011034484140b8a416031000850f81c028014981c030500030000030902c00101c1c41d04450b601e1030301e4031340214064016500c03041007900005125a001e001c0007031002036200da8a2154408915588480e0703290350305001100d405035614615003500013030b0041501d00c24840f8a100c2c07400b80181f140b41966079008148601c0b00c0002c402c1283d2008000c120a264020304c5005440070b0656035145503181103642c550f8254136004200d15241e10208045900b41c50f138101c014140d17140041211452074580742055580e40143c41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 539840701 1250 539839451 539839499
    0x5010c110a03031706150f18060a03091403032503020708160b16020d230304060b120304080d0309030e0a08030c0d0306051008070507170a12050f0c03100f 68
    0x42212414500b0000503150b8040c00ca65060004e020403d000f00d508c81c000203604000c682001405940d039140050000010b55140002c0103010340c40c2402c0704c01c20890500c4010b40003841080003140d481030700286d404140b242c8030603d410b1011016002401a01e0015000c00340111b06007040103113209680740114050044039106a80380300c00d80442a20f1100b202c03006800084aa62420303002d560700741d00d034036100180d0f0340030302d0441021300000d40c100f10360990f00d694071441c0b44206801c0900d5200d003807403c5803002e10f07c3c1034144612a5aa95800e914074820542d480401c0030603d4801c211606628030000d09642e4507946c1c803a503050b540d4000e80609103403401041012134bc001d009126501c21550081c0c00c1c0c00b0101c460881c241c4001c00300401c500103026003040408006410011103006407000020101e0710b540244c240140800d8561a01001191500080c05840440c0540c07543d48040183c0d4810350302d540d601054020701d1803540c40f601c01c40600c1400843c0712080b111300d840d04401301103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 539841951 1250 539840701 539840747
    0x50c1b040b031f180b13020f0306070903110f040912030506010c02090c0904090b07110616080a110d0e070e060607150c091a03070f1805010c110a0303 66
    0x1e420152a00241c41403d1405444a11140900846500f0802040454007100c0f00380101e140c8840d2201d05040b11301851602d80c200b0540c0451901d40c98040840000740c0050a2602c0c110602405860103400050400903500303040000e02d65030143e00b5244180054010b101159562606d01e1074561700340c454001183c1840700040701c0b544181c1c800743c41107400400c2c4890030740f1000540c414903440440140d41140d101c1c034520021403050003986005105941e605044542641802e0f800e00e00e002d41192091000c1c6440103820581c021176041e0000c1a880b000528041e50f240802400c0c071030b608100182c00e0516070719101c1410045444800c8a0203a504041c2c250b681c07800b003004030711074003000074104a1400310402000e02507901500500b1240e0521400081d21800f01c0b5850032240707105950382010020403c2022903001c4c00415440142d414604080a00c04c081110100c81d0f82c02124100b0007014141002e001e44400c1c040d8150002401044070319481e400c00600e4103481d1511081014104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 539843201 1250 539841951 539841971
    0xa05060a05090a0305090d0209010308120f0f07080907261c02070605071e060e010b09041e060f06060503010f0e0114090c0d0e010203060f0a0e0103030f050c1b04 71
    0x90141c144202c1c039200242c590310311295025103154001c00c150941003c841089000140c03a2503000030f000e5401014419202c0c49509241050074078000c1503a4403203240c150074441c0074062401403d41003141420100641d56a000c840f5180c414913500c040ca80c0c1c4904103444ca201100e459200c00b0320003240c8156031a01d400101c0302d20b181820039003140c0040c2d121100c00c0180b0381c03003038001d002401d108a90007485001c202e050721150083c08182079500560f10907a8501c161424890f00790391940903900d443c0c140c9072585495032841d4002c01d0188005c804440b0030800c010043c8c2c40340050010f5140100b0800d41c031840000c080380c10902900065001240c9c0100380c02045242d0141214919003540460460381410b02070804c0014010402c220340500082c042c44807180a00d40e00e40303400d04001a00c0380381c0f40007042074880d0b406905a005a0400c0c000f880b4450f0906861030550b9007504012045d1052000105c42d40e10455029501078000c082d4801e4080a440380107423909501118140805910 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 539844451 1250 539843201 539843221
    0xf0c01112106100807120e0c01170603150a1103043806010309080405040516031503050303060402180904050309010f05030c0a140c010f02031f050105180a0302120a0506 74
    0x5a812592265a41c01c01e84621441044c45691084d0140380c5428585100e01140b003d07640e6682e4001802d401c0300d1415003203564090758000708402d04c0400040c050409a010a407220031444c0203920103144580010415044d5030010030007544850790180c0d8078580f0341840311003440c0510003a007500c2c908d20b41c1c1088144490ba0760300d1162a80721140761090f00e130840150300070b10544100700c0b140c503400e010000700303603907180300d141e11481c159440034542c403040500c0101156a42d0f040d00302025583c036014404134a0000549600c06d0f4180c900503a99080d400e6481c0d04200c07503608080d440940c030010402004008006400003150030388070b644036901894007c1c0d807140070883d40c2c0f8030032800030f1203c81a07142c46000c0d00300d249503150703110320301c3c08008100060035680d0020f050040725800000f40003214804004060040480301c51281c078040c2000e0008105214903d0b0301c3c0d031502d05842d242e140c155141ea250300000c503030003090080c2403080690316544542448006071180e00501000851481c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 539845701 1250 539844451 539844517
    0x110d0506090f0c010f030b01021905060a05060102030a050702040504140105131502070b070c0c180606140f03010501140c07031406070804020a090c0302040905180d03150302060f0c0111 81
    0x1005071500c0f60345e24070080c002c4004001802896045100d07000e24010703442864101001994010300c0034100602d00703041c00c1030aa40010b415035045600400c100720b005980b15047c7c0324016811034004c9101c0d21981030500c6600f1111211039040c1d4600720902c07095140b80032013810701d039100361800c0284000d84440d80d00bc0b4060104060401403180e0000313040f852140d00d140b0192449503e91700603e548070318078040390405130700311000c030a60707913510500505402c0700c2c154400c03580900c54503140403540c42c070301b03d00790006204450601c0020702400520081c07120a440940000600300c800e421352fa401d00851402c0d43c2148124a401080080350051340b01d5902d4512440c1c0142c88641c8252801e840500107041300741109007056828440420100454083c15000c1da10020800c4c0c1070b1038484280c1401d0981d601e208005040c034107074a11030b88200c0c40c04070a0490f80c044811a880300006110400c0764071400d0306402c00c9502e07010042c1078105841000c0d04022031101502030b2410140c00003484100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 539846951 1250 539845701 539845723
    0x3060e1c08010e060405040503160309170106081207020d150f0506270601020124260715030605040c09180605010c06090c0b040b07030e010504061b110d0506090f 71
    0x3220b00f200040a50402c0d410642d007103841075045034a4400710703007100140200800e6044001408071a400c000d840d0000e01c1824171103800c90000c0000c1460019250354642a41303501e9481c203540400c18509550b141c0050f610840d40023105180c1001c04034120800400d8981343d50754106240801044036424078048514051090072441c801c00a5210032b0f000d160907000303200604640d00c0b0f050b14440399205518440160b041403c0c1d00d1a12800c1440c400191101c01c1c40c24031880801084504c0c03c520300007040000c490005040c20070803031181c1001c9000c2e10030b9801094125080903201d40d00d8a903c201c210044951015403074200505c3e8000c0c2000383d03056845284d001800840051010a82940c44800040d21811200b03504c00d5030b45803c10400c1d00a86d000e94452200410900b080c07580104080b041404240b82403460281000f60240450701c00342c0703190054180018440c5c00700100400c81990b0244001c2c20f80c0104849032030010350b03610301199048154060218a100602e000140e425402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 539848201 1250 539846951 539846969
    0x15010b12130c05030d051c021207050a1202030112021306050607022707050304030e03013c0203010b0408070801050c190212072003070602031902010603060e1c0801 72
    0x16200c49240000001005074151041a039400c0300003903660707003040450503503580313602d840c0e0f110010041643c1c1003c940034140c80000e401000450000c00600d03100b41d605ca80242000c80d1144d2a1400840b54a1203040032002c190f4070002c000303e8041c0405030500708052088802290803010818110b0694010744640380d00000709200090040c9410b1a001010340441b84210700040c1c03036080c07942c502c240b09a400102260f000014003080c99400014030300381e55403e40003400340307600c0810745940c0c440018a4040004007810b14000031550496060000d4408043d404c0d51256141d00c90700c01c081d44580300303031021803152400010f1511010702842d4894603031a030300503040181c3d1001002d103085003654413200314020580c14012507101140900b100900440416180880c0541da2542c2c0040070341129104ea44404400c00c1420707400002c03a00341042074401200203a5640300706034094105500000c20407824014204c80c071140001e101c0214004903c0800f41c0058600300c02d907110b1000b03006441007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 539849451 1250 539848201 539848237
    0x90601020a170a0c050a0c18020a0507060b0d021819140c09031f0504140303133206090c011b03080c2a0c04140f0705070c0815010b 58
    0x2a8401c0283c0034860640c01c012152803c140d6810707003050100a42111b00010586043c00101c0c0c043c0e401003c86031550808520b801c0150364081c01901803410700808154569801c1c001d980c88012510280980c00b40050400c0c0c142030741d07202c0c00120101e800c0ca007050405415180451a40c1c0207503031b040403d6501e0940b140e211614601040e500820009806100e242d420101c0705880091340c03461400c0380000010a81054607114110b841d190341c90312010707403040c0240300c0050455541c0d462451750010845040c03c071582002c00301c041018821100118084000e802e16800100c1c03c10322a000c071605903411070300e13910019101e60504041600d4104070044c81c24000a005005076904070b80c61b03103401c1d42000c064000300f413242c44003080c441908007400c1c1c0c0c113103000c84410044106860340495083c00702c0d04000040b02c10507440101407074599415600802c4507a8001d0303040320811604080051001c6440303180d0035684402c2ca4030248003103605640009aa01e401209450896543c035a40c0c0301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 539850701 1250 539849451 539849483
    0x1206040c05220303030e07230a0b0d0c03060e0f0601030518010c05030f01050123030411101d01050307141303020315042a030803090c040606030605030c090103020d030c0501150e06090601020a 84
    0x8d0580d070100e01031a085007920300c0c003040203003503e8080c2c840c005043e0000300c0c2a5680500080c00d070b0742241c1c08010211940d00034046c041c084254050b40c40781c02882c3c00103040c0d55482d8041605183c5132202d1a9552030308140005c1c40703500c18000c5104086525100b001c7d0303641c2d2001110402900d114207681c0550003200d41c0100704c0c0010045400502a17140d80303c0d200300c05030001e03400780041c0d00b1030008030760001c100c03402c424500c0180c0c0c488407909017041d03419850a101301034035003400c2d01418204004002103031440b2034140c00c1250091a005021120b26450030044060ba0030070944090340c2c242c4170b038000d44900003c5d00c50b5000020320200c140b0a0218650394600f04a6000681030201d28001c95110381c01a032074070711420000b0080d56502013041e501d042d003494200549800014043e450f00001440580c864115003201d141e07040c50326003117041311800e14600419001d81d182c03034201e451200c0002c0c80c849103401703980151000c80c0c4c0c110903512120016aa91003a00704000c1030000c0f1010154 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 539851951 1250 539850701 539850749
    0x210307080a02010204080d0c060c0f140d090606030323040b09010e031f053c0c0d051018020a230405040905030d0509031206040c05220303030e07 64
    0x4404070440380005424141c45414140c1442482200f040004400d801c41c0401e000c103600801b591031f400c81c1000001d00554600040948124041c2c40701041000111030650540e41c0d880541d6003074016000708442c07516131500074541802c1551275183c244000c0d140c441d41c410f14004581c2102c4240002030314201a40d03006440300920100c51aa0601a90a001150f80005903202a41032039095000866142160190a46d00c02c040205200040426400e40c401ca10070b50304034400f0346500c0101d004907510b06a208c991841303080500d98810b41042c4c10301c901c400359551918240d034082c418071004682200300650490044200e560b0025042d4280a0794101d8008240551a4401c5400303600e0b00c3d032544041410b80d80220002c940c0c59000103454400403000d882081c2e00301b040203015501d01074245d4040101b0074005040f00741b00380d40d140301601840340501e048800518032000741103440100088018910903c42c4400c1e00424103000001100070740106600c41907940310004415000520b0368a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 539853201 1250 539851951 539851957
    0x3012903010807090908090303070605040303051501020c04051510031e050606070b040c0b0c030c0f1617100905030a03110c030403060b19030b040c0803040312050307180605040521030708 82
    0x5a84114040161f50440d407020b00041c0900340c000d52010801d420285402800c8a000500e20101c1e6195424254071907a40464285003281003143c000c1203a40706e884002080c000390340001c07035004550310b400040907a0580c000d000c034201c6500b070880401c9081f51110040e50b0046845a5000310b0030841e10b0000740700d10400d550814060101400d07a20b03154141041d007030b8441142c88500307900101d030b50740d154481000b0392040d40740040c01500c0617980c002c1140d0034101141c050428901d804030045ea050440c00c00403075280b1913000e14140004003203418015141c0d4030140e124030010342001d421040340004902221a076405d4400114680b601d1511120024844035180d00d0b88402c3c4810303500c80c0d50030707103400e00c5000d50301403244c030006420246454001502c1c00e6000c2c03034264100740130800125400b100d203003000e00d01e00e080044c0ea07981c034240c0c1210301000c409034051038800100c10204143d9404030140041e21070644041c0c000112410709101080c400c06241c3c0841c0d403003001404009003ca40103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 539854451 1250 539853201 539853203
    0x90a020d0e1b19030f020d03032307030b010c0213270606061205040203030a030c0203090a0b0408010b1804081b030304060c030534050f030129030108070909 69
    0xc0010300d600d05032101400c210440c02c1c41c859a001003803004800b031400d95284a400c5840040d5101d001d40395613030f80000d004a405010b03100d661162001000d041c001e8201a00e0407940b580e4142031582507020030b0710001402d03180c01340017138038281c5a0302c040c0d40070340c500c2c15141d07070010700303102e401565074002c0809004a100d5100b6100081a1071914841c8111886440f66109940c045070840c1800c10013010440062207410016003414140405614040f046071100072035880d01040e00b682c1c20100342c1c9184101d10809030000400d55002881e40402e6000d0300079154882d0017030080a04990402c41e80c50f800d5000e07505000d48582c0441e0004402d80300038800c01040c40d4002ca120901c3c09040d43c11600115803d455003a00c0350744850440b541071103150341c05925072650610380052114183c1c50344c454601004007144008040090842c060320030b80740002c0c0d0503a4419543d6845401e43c0c50f4202c0b580000810b101a00c0710500c82e25004041500d05aa0018000704005072a101109014044c070301e00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 539855701 1250 539854451 539854477
    0x10b030c060a05160c080d14070b071403040303050f0c0f0d05060d080403060e100e0d0e0102010e030a03091202060103031704020105070609050a02010909050705092e0809010606030605090a02 84
    0x13208010b00d01111511900d02401441d4606050349014205803e140440e00450204102500e02c50101c908030410b95410b180c1054040c5041e0703441031819101d508204200c6c080141e40401040200360707164001034451105509a0200c0d529040f620a00700d02070440e8103030981c0000d1001d0400c40c42130b42d20041c5d01c5400104118200119910344061560054009490494a545001002010400445290329500b05e0200309190b005040710b40c6880350400d40100f007102229032258240e100350080b942410161090302d42d10300201002a000701420a011906c0e025407280da0080c0074008201c1c1812a034041e10740e44034071004000f41d8199558014412414400240096004102984a00f02d0744500c610001e001c1c1d010203000141c2956107a46c40390031b8641c1042c00704009140d00c401980c8100809403140e0107080c64014022481c030109240f4a605407100c0c0f000d111006900194581c0200d201c507000f0400346031500c0c1c045055130214001c064204502c000480c20b440d107254010600314181d04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 539856951 1250 539855701 539855707
    0x72303180f190e090c0901030c0306090201121503050f0303061c1a010906140312090f010c0f08071b06140307020a14030901020c090402100e031006091a03010b030c060a05 75
    0x160b10501841a50700f010129a00e007108102d58540c003000280c80e0341804603082c02c0d0b00e40c910390b5000d855105c1400000d1010350ae8400c1c0c0011079019900d10519004c15100520038120800921500746805100550300c0c1d2140d5045001042e901100300c03802810058401000648103001508c0b443e0040c2c2011200d081000e02860040442c00107003038080c1c0f02542c80822003501d003d2400130f0780070980040d240319411501002140941c1542121640310741944c0341039044041a0060f206202c403c1d0001d800a03001100b014200b00d02c02000f0a0503a106550180900418083c40d0320301ca4500c0c010b100c0810403001d100385041004a0246500c9005441101e08141c0320380d40d8402c92800415140c0b5080d0300208000c103080d80c05000305258100c080e03403000c40d2803400d03800050781f9103000800501803100c01042001c09172400c4c8113042c4424042c02c424888030b5a151455001000d5000040c1c03010741625280d41101c1c54180074010202c94018002c00c0c0242d2124208a0303944c0c040401081840410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 539858201 1250 539856951 539856979
    0x40314070302030a0906051c050903090310050f010b0f07080f0d0c18122103020405101205011d04030f110d020307140c0a030f020f06072303180f 64
    0x5000100500c0703200b9806151245084100075241654039000342c01802418000c41030400044000e02280c84480d10001c207160f107070202581d0642c442d901580b50180030304041d01c08100020341145029102a00d003c114507a07840b8030b08001c0d40a5060040104941040020081006170010340010031071301e00d038103160400c00030010040b640718941c2180442e034a910348240c1800c0b00360004000f0000d45c031115001d035145d591650040da44caa00380321007000701113044170107140c41b940c10b072805000d000d0801e1230030f0200d4150140620b9862a12003481c43c0c01c0130004510400502c060241c8084001580f9000e82c80d6964241c50306902040d1490400910000c00302c005c50040114071a0101c0320b4000e5542c0e503c0509001e10340c4c0b040018544a42d90113a028a103658980482800440360011840800c005161000506415100c0da52070b030f004801203001c40c144040348101c0c40c4603407503d1030a1044121040000d5440e805644008558007440207140443e9007004102008401c4000b80300002e00900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 539859451 1250 539858201 539858237
    0x9090d05070c21050c1f110709020a0914040624030e03360102060c0c01020708031006020d0e010801060c020406030203010513030f030902030604230105010b130603090b06090403 78
    0x320401c01e801090f801d82c0c80805021050284081c80207040d0358580f602400140300030308285506144004020b1842c43e2031072141c206122450103099441c000390741c2c800301502c00034500c4101d40603000c50704640c1e41c00075a240c40c2034031072102180c5200e000c2e08542200206036168100c0c0741c2a024080c15101c6154184c035076404c2c402480c5264400922191060032210080043c1c0390240c5650002403910f01450b24588e000280d09078040260950165a40c859521050182c000c104008040c0c0a000c014400340c80d005a00b0302e410f65501e0760844100541c010300864840ba469002e0902088601d0018880a80700d10b03084444140080d002042c00b0b0780da40c2c00709007128400c0341e0061a10940603003003c02c1607886000c40e003501d0b40c81d00e004c2c00514010380009849102c0908000c0c9200740f0303950350700c0014802c1c000c03099450310001c008014641c0d46030300034485c50b8080c1c007617000c0c0e42100c4103000c18418028801c3d0f548190704071050f800a66929818080203c42c060019000d11030105558030101035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 539860701 1250 539859451 539859479
    0x61a072f13060e070e12063d0e070207060c0f021203070b04030c030f0c0309050111030f040b0a0e1e04021b0f060702061014040b010905060406091e03050312040201180906031109090d05070c 83
    0x8400300500d45515040c032b4001e040c900075400020801560788540f10100759810343c103541503501120202d010420104805207035214802004211000702d07420030040c16007010740750341d0301c0d800ba0300c403180174407040c0d1030444202400f8a001008241514410b106030351040044003e1031003294216481c2540e12108040aa000742e48241444000081e101c13603a1030340b06102071100d90341074540e0081071403c0c281c0400d03005220410301d4001c0f03901180c902021000b42c8054500c9110350002d40c1c0c82102c1140c0083e803a00f00c01c8a0400152003448007140c1d044c1d58201c8904215443c101080c8034850064040001414031602070504205d00000003040a07079454006100400c0141c442d64001c5152051f401c2b040881e000802e182103442c040c0c03c1002c118080221104040c012111400965480c80140c40c00ac0c1548504c1100c0c14002001081c500070310380c4190207880c0a2201c441201000c4010440e100401711600f43d140e40081080812540c02072019210311803050320980c51450700c034901195144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 539861951 1250 539860701 539860709
    0xc161106090a140a0504060e0c031e040b1b031b1e0f03040c090c050403030c170c0d03140402010918061a072f13060e070e12063d 57
    0x900021003d2400c0c4c58100c04001c000d21050310103101c0340385099801c1c00741c48002407880499110000008007000c5181110039454102203030b4448150806080c41c60545104451303003800212010080d0018528030804d030383c81040c2d042ca03075060307401401c2c186009030741101c018189054100e1040c2100c0c10190400341c200c0c003085025540d280c1c9081e0800d059198100d40c4921200b03444c094082445540c010308660a99400d400c0c80c0c0d9034201c2c6490001d14509426141d4401c0c02c0c00400e08018010001c21016012219903409110780080e650388032194403000d03a0001c0c0030415013102003200001d080403031500350300c10700740c0014095a00c101841040c4028194014908400a55039080244041c0710381d91456030215283c1100082d0b00404004d0754140003111712424041d03440710a04142500410040d00c0e550310101d001e41071000c00508030b131090110207442890420b4214821100016000f442200340180c1502c0b1141790312000c043c10060300f0b000030900303481c09500e03985100c91004042d00030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 539863201 1250 539861951 539861969
    0x140418020409062f030a0b03190602030a2405010e0a15050403020111011a12010b210c0907020c0904020103060e090610090608070540050c161106090a 66
    0x7907010545015814012900140d2692081c40c01000a202a400385c9034422030a804c00030703600075907000191402c800043d0a0004041c2c00040c0301c10407285402550050b4900d04d418807200000c0c1403403102202401e90f5540c0b01001440c410011507101f0725030b80181c5c450140c038040b00c1c40d0700c3d540c1c0c0d2940030750790182c98804100d00013400c00455a00800e1080003421000c000c100801c0b0401004140d84000d010003072081a116421a0b4104820b5010b80d509200c001c103000d0702c0d0702106c01d0700f0b90b80e0740062441480c00e016588170300c030301820400300d06c610603102175028013400103040742003144030303c00540282d04140da02d00001c5082c02040b070802d8007c0f035141d0001c00c81440c00783c007a0074440c2d400c1d801803100365050000070071000b800000c1540654a0485131361040f00c07421410302403c41c2101c00801c081100c6030013514a07074448006402c40342c5a0040c1e062081c1c3c0d03030320700e1120034038855400399408940520a680c1c0101d8001308004422400c020501b0345054041000a002801107410000035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 539864451 1250 539863201 539863211
    0x180f230c0927070306021911060403110f070806040210050a0903030305040804030b070309060605030f0c0108090f060c0a090806060904060b03010915060f051807080709080316020f010914041802040906 88
    0x1040c0e0740301f010400c54032080c900f50600346441440162110405031004050240c0400b0710b00c000da209010030800001400c046490362070303480541603030f2075205440a03030203805500c0c41e5100c41440780c4200c0d4800c03e8030b921000450b43c40d5641c1113004000041058900c0036040c40088005104c010519000341450f98001c1120022030410070102c030030a62029100c1c7d4049035a510080c035020138100c401d28000d003002c49017540c130b096159051421110000600f401894101b00c1c1540800c0068007a80c90380f50b0341e8109140e1900300056465038151081f51b8003560803030010300099000d4011030000d040180001c20440102da8424141380b10003001c001490362110300c103008040d40152128000c110440c2d01840d185003a8440300c0c0c0d4001c1c00b400c01c004006000e000100f005001ea4201002030010000300e07560b0f000040d0040c89484000c4a040388544580b1a00546030341c0301c1d8010400b0347d000d440d07002011400351400c12004003000c440e0301692041c1d60a48d4005030f42c8030b128290815008503000304e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 539865701 1250 539864451 539864467
    0x605030f19020f0306120c0319060204082e050709151106010308091009050d020d030c1401050f010603020c0c011107050a0803030405010b0603070e0103180f230c092707030602 77
    0x194031046c0003c420841d4024000740205a5000031440b00c8000c1451000c0480321b15414a080a8400c64102c070405200e44000480c007103801c41d025082c2044002c01040ea01c100d06110801034030419540b640000d111b040092040b180b440382d02003c25030035800c3c804416007040c1c00050400740d090340169000300c0045028481d9003044c80c07901002c2181c91802c20170729414807002032202801400301900410611b402101010b002e00c130145401900000c013001081d42100009018040c1290840301104651000145030b41c0a8000c0e54850032810000c1c0c0b06000d0320400440d403c00f045810843c191042c200006295103e100d03d2001030064100511394a18040c100079003980c0542c040c0c0b42c05500c04004021082d42c4c4410a032140103001d01e000b007600641000a0340c010403042c0c1c4040d01c240b124901721401c100244030b400134414482145600d0700c0f00300382226512a01854075043c1c02100941c00a28004a000c0045518804011a4107080001d08040d1032401c0c01c10b40040b5600e070703030000d0214 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 539866951 1250 539865701 539865709
    0x10c12031506050403170f09130b010e0906030a0204050910020d020408071d0f06130203070503060a06020d021209040609020403051b22020318011506110102040605030f19020f0306 79
    0x140900203c1c10540d2500749075903a55458403002c01800c821007a80402c108101410720b000b15404401c00911a45800c200542d00e40020100a008103011800010301341085007840e02d44140b1440c3c1c000d01074500380740b550b0203200140500825800c800c1c003c2d40c0f280401c0c0c005610140c42d080740390680042e1514144000e5620703151aa03006042900c003400c91a8000003104a0101d600445416090b81e294480d0030208540d80030160380c480c502d034004000c010902d54000d0145104140485485c0e40b8941d035000160307144d01d81c1107031000040c2c01440000c0320b0342c55600000c020101d03001c1c00c0004d203d0b5071030600c02d04907041034004407000d8102c01d4103038080ca2201100d0310302c008001c980030740001c42010000320f40443d600c0746015409030080002100b01c0051014943e540f600303c07000780820402c5043c03400101031a8092640400c1c0600380c2085014814400c2d24242d40464561528607140c910590380c0c0300340000d00c420880001e200080d403a60404d80090031007824440c2205071a81407010400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 539868201 1250 539866951 539866991
    0x110a090e090a080c0309100c0b07030618022a010606120506030d0309020d0c030b01090e01050903120402060f07030914010e18190212011403031204020f010c1203 71
    0x1012004a2001881030180300801c00b101110341c03000001d03580d5204404001e007540900860140d2045520407040f0400d6001000310702094420079620100d55201a41035007250181d0181c0d0010506070415030049400342d034010101e5000c80080840e1103420184c10b400f00100d001504852a5104c400c00c00c121500301b45031104911800c60b0501051920002103a90344104020340f07010161201145419511081c00c10f1031415003084080441584038100300da0700d6030b820b02c2001c44051500e50010f0400006105240c042c0940034091842e0210708c1580250040d400b92041c0e90143c4104800803003121004000c101c200e1281c0c40390915280340c0b014940a10380c00000040c14000c00005031140380d6500401b801c4098100101040d40c2d8a40101202050200d034040c080e40b5403002480010b01000940c40341d04841e1761084080100c41d4010505450b40a21034000c02610064404103005143c211320368024200113240595014156032941c10520b80816280004130f6540d44000380c08004162003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 539869451 1250 539868201 539868209
    0x10170a1511032d13120e06031602070f050a0b0a030b1c03020c010507050303072a050a0c120f031b0605040b0f06121b1809031201211e0501110a09 64
    0xb0031140351909490304000142001310080501c401414084d00e03290040c12150905400608810381b24501300307018001e0300e06510152409823054100000300750035480e00b035106880000c1c1000c940f540c80c2502064070350300141d481400741515540c10343c109441c0c9203102405401d00603030b45000700002d401c0184c1070440e01d61000b030400038100028804100d0000841c2e4020b840d42c6005078442c4807000f00380c3d6542070301c2d01c03a9080424206144405210707002408000060061014445459444039074494064010400400100904002d40c01003800380146001200e0000034022480e00c0c80c0c0d407403900b281d10441741251001c0942c2c041c81040c0030040005503110740181c403d803403a280318006103540d0f0828031200344030840c2940e0800380c1c1600c2c0c4448905d0214040341ca00a5075042508100d622900940c8503055800034031000055940c1960400c14200104280c1c485295030980c3c4401d1101d9440701e0305001e484100d52000b5000403424070520800303417182d0340c0c01e40e101c00707810030020800403081d44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 539870701 1250 539869451 539869531
    0x31d12040f080615130603080a020d0e0a0f0302100c0605010f0e0a0903080a0b06040504060806250801030605060d17031e1e090708060106050310170a151103 69
    0x400c014042d00440103105449a00b210101942c2c05005c030840f0282c103542d040200400300100d081070f5030725000224003403000c9290300c0304901d02c2c41080a10001130440d100703106401c05080810005420910783e422041203907840c1c02c0f8141103160310b0715800c1d10303400c0c0e00100060081d0303d01001240c1f4407402d060381000074035000384003000740c0361401801d0040103040c081d1038941c1c401140c5020354418040368014500900b00303104060741e40140984500c030442d0840800d0b80700c5491000d45150300f183d0204c01002d00d40301e1039090b90860b00d41d034000780002803100350808988038040010038010300c000500781400c0d6000d940d60b031400340c5d280c1500b5401c11030082c42264100091007210201e6102c500c0b040e41114645c1c12103030b52895402440c2c01e509600800007400342000100e039240d40300009502c1154080700000c1029518080c5101800d1550691b0b41d058221050800006a0791100414001c0411901080a424604130b92103983c1c030603182c581d040351140c00d0304580f44411030700d1078002d0b0813600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 539871951 1250 539870701 539870713
    0xa0908070f030b0105010e1809010e1903090617041106091207050301111315020a0213091e030f0f0509060d0614090103050307031202040905040f05060c040510031d12040f08 76
    0x207c040380c44c1050b5480302d220641d960000184500d4402d500034540882c000341100c845007800c000110740f072081d02d8026070008021410101d901d500622458807100700e9003000382c050f40c1d1207417507a0350b2000c029030100350320603410419010076543c3d95040002c00c0381100301030842503151408141c00c454003104411034421040c0326401c005c40449071160b00319400030740540700307003001540b040741001c40f10500290301c4072201b52201044405d582c480660648070303603442024401460750003014402c040390014000b8100c50115401c3d41e100791039111161145050036414030040b000058450f40266450808040e0b1781e90041000c15030010402c036440c0c038161650320702d0b0750454582d29124812998064140001e103007147c200011594111001082000390800a82c18103140024542000260039299446507e0110380e030742c4400800c880032500d0051000e00001003440041d40030f807180404078560708414001c28107500205010800700d4409100c0c905664905200c10182c19280c1c541100d1442e43c010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 539873201 1250 539871951 539871977
    0x20c0d08060d030320070b07030c0c0c120201020a0204061401030f06030807080703090803040e06030d0f080615040306181509020f041806060306050610080402150a0908070f030b010501 81
    0xc1c20b507840c1841c1d00351601050b9100c17110401c41c102c55007001210016407002030000b00340310400c0c0095001d0262950180940d1100800454004107203910203040c07801c6455040081d03040f80305000e0703446841801a240c410350541c00003030803200e013903018484030007504002500543e8107124800d40d11036450003c00c40705003103840c0d25206000c2c07448000c1000100103008002d141c001c441340402044823008481d41c0355111500d00252810980d2900d000e440b450f1428510103000d6050211407510540c0c550209a4a00d420002004504208400e2117981000044081011030185a50411031448080341c10110362404484607184000401142850b0400070001a9900c65131a207001c43e046030702203040d8030200c007000d9008640410060a092400c0d80000406c9940d03000180b090700b00710740a850503026600c0a070743c0340d201110000d500401c0c5e400100e01d0200c21902414240c1018070300081141e803184102807510900b900058070300380e00302d4001c001f0080107030702c07032405450b00f03203014403180d520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 539874451 1250 539873201 539873209
    0x80c090f040b090f010e0c090127050619140102060f0702072705070e0f0d030203030a0504210504030c090204051e01180902040510080903120a0b090a020c0d0806 71
    0x4041d200600100d1500041100c0d600104001c03914200c40d41c00030011900130000940d911190b03121120300909030b1500024041c200031075083c50f20b03681c5003c1d106c0b41d90400c004030f10040400130b00d1280d0145d000f40015007102038128888018100f03e0717070041c000300d0f165400680380000003400c0d400f1174194030080081183e800309005003112600c1403550700074000583c091880c004d400b41150041403424003001680d42e4030000b84440904144c40c42c030700501d03000341844914482400040c002d43c2c81013000c60a131003401d5200c1540240200031043c01040003107803a000150900c45c803600098070202d014000d008400c1c2156005150001c1c046280c0b134940b0012826280e900c80342c01c2c0c1e1a04208210051590080400c140a00b40c42580305020300c4c1ca904010300290005d01895010701c0018004d070721104e001d01c55035402040f0b400c0045003000c1c0040c0c00012200740040c50660500d0311095100d140d9150243c2040c05046061000f5880e02d5020780c00c603161440b400d07441c034200500c4100303200781030315 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 539875701 1250 539874451 539874481
    0x9030c030c030e060a0302030f060a062f0a210206010338090106080c040203010806180c10200d050901200304060e0a06080114062a0106080c09 63
    0x19050405074240740c11424103585003108840b0850b08070a00003000d2640755410781c01944200c4000d9040b02007901d0300c0090001c42c03607483c007c1801140070075203800d810b00030321103078000e10a0342c1c0641c0c200e010100c290080c0c200051083c0442c2c800a01c002c9201000c800402d9965078010300c0c3c801000d00707616580b42c03e001d00304c00d80c0b00066480b41c41c42c45d8003018480b40c00080403558140080b108242420900c00c1d00030700e800d10074414180903080d0406002d140600850f8103e0ba10413000703003040d07180e2040e080640e2a80b03101c80c9080c0e204100f081145602c65100f020f041e0034032078441c4508504d4415214101059109224031240c101c02014001c0f00d80201c25508008000c1c41d080300c1e069003828070000110042c180785500761201050002e0425407090030307a141c0200656a480c0c0c400d5446409494001c804c0c01104492042c40f000401c10381000360152510400503440310188500403e0394454000d10424042e0301ca9460b520103010070441006821080d15050b640040d203498a001000c680b02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 539876951 1250 539875701 539875703
    0x12071b0213020306010203191d04050c0307030b0303040306050c1c090b0c03180601120c1a0405040b010e0d060501210b22020901080601031104051e090327040e0109030c 74
    0x703030740070010078030a034420000d44080c02ca045420001c400501d40016000940321030004101550342d046070082d0b802e02c1c0c0280341c0940322039034805055403503418041e8081c112070840160940300601000010131568040e00d8019006c01103c25170700c0444100703038101d8000130f2542032070703460034008602c0009008500c22030b802040001003e84a072150781d8410601d180300d590b40c1203503205030000410700482d403404c211100ba11903608880c510365221140b450005c1321480d0790740158800c0c4803c0080c1d00341604103410004051401104a21049001802c0301100b890181c598560f070780014419aa0008216021200c0c0b00180c7d150004d920b0b03954003100e01000785400d220218984999460340c00b0a00302c0b500075139000b00740242660b1a20a41551044244000e94100d00e1016150080d82010310905d0f000c0d103542422015801c10504080312140f0001d0044c04891004000814103a80b0740b00e44c50110341c00b040d4250a0700d038110020401521300c00301c204295640f50156036000250018000510307a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 539878201 1250 539876951 539876989
    0xb01050403210519090503010506011815210510050f10050f040314030a170c40032f09100510050405090709080303270312071b02 57
    0x1440b80e02045074240291440c280503070341c80d60010030000360050800410b903401174000300300598404004440d00c0654041191030319415034018001212143d4450907240a64102139028900c1180340b44e03212a03007070b071684903015a05c40031721903894055076108000b810b08940d02d4290714220310006403c41502a10201880b0f000684410f112920a003070700d00640e08480460039010314036118940f6980040c89820014a850400c0c0800c4880c2c00d0343c00d40176401d050980c0e42001ca00740c0c9103049560361002544150070b409c06c03000c06101031103100a00d00903400010390015629601d41080d011413250641800004a41c507a0000085420020303540340d08101c40540b0152108001804a102550440c40c3c01004010903012050780101c010403c45030140c2d0400701d20351351004125582481d501030100e00340c004002061782c5031401384c0c0902081281288095009014429143c50b42e4808588048101d403180c0c2080f107070036000607440c640ea14100e00c0e0000707803075000d50000e4003000b02d01443c1c01903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 539879451 1250 539878201 539878253
    0xf1715030607090b250204050a062108070210030f06170d05160219030807030323271f060f05060c070303050d090b0a0519020c100b03030f07080901030b01050403 71
    0x456942114001900f03071b0003400800c4241011038489001e401e8501038594010049503041c55400103045080e01c580d0340224030720f03051030140d900304254482c140c1ca9140405442d6002d141030868248101c00090075181c6a00141003c030004641c245196480142c044c4982402803101c01c001c449501801e042e4100c4801052280007951030300d05003400d0300050481c00340440c40b4810150968813030f21080d0311018422405041e0b40443e103154030310480d0395900c4000745042c460360b4075440095040f4030300600003d1fa12005e58400d44240d00c1442e001c0d200001c40d0300d0b030000300503400c0141e00303640c0900402c3d200d407490300741c030301864a60780d03002072200408100000400800e4081c40380c1c44061429071080d8506172900313092001001501081e11076201196004c000c00546410314422a8240206031003d48070481c101c5c43d000c4000d0000411580e0580801c01c0080400d07001c8100502d0214400c4000c43e80703031106070000604450240b01004d050043c00c100620104a40844a40142402c42c40d8260 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 539880701 1250 539879451 539879497
    0x20327030f07080a0c0509070f0e13020f070618021c1b0b090103050f151905030f0604050d080417030a0e0d02010e15160f1715030607090b 61
    0x1151401c5209000154050280007050004012601d00002c6000c0e4064415058440041040c028025211003000c5044503c0c000c1101d8000c035045100224014050441c0416040d001c0b03080c0c0c2c1c000140820b0701600041c020003040b0091003030540d01010201c019a004409902082c046100c84000b5111120481c603404108a50040021040004c01d001c61107030035641d48141007907400070000b850210f410b200004503a002c103510708501c500101589030382d40e0b10b0b22105004121080804c80c940044010780d012070303541c408004007000e40394420010034841c6000c1c1000e0741021394842c1140d080089a1081c00b000c80c120400032010003000701801540c0342c5403094060004c03c420014003503140200818201c0c81901907212070124451182a218010350131202c8a100701c40441e00380a000e86002e440380360707081c032910280c000c017455070a001502000c0211008000c440485141c0d00c64000603500d02202c0c05c0c107021498201e202410040401800d00c600303141240103140c1412514100007a03c44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 539881951 1250 539880701 539880703
    0x510030c12051b0c010e0d050901080901050705190905030d090509010819020105181f030e061603020319090f06180309060e1306150f020d0203030a15091a030d02032703 74
    0x2281b0000100c0c1100d50145141c0809485500300840c1c01e03001c50801000103680d16418000e2a100340c00036510320b454504943c0340148007190301e00f44802040140c1c0b901003100d480c104814a0601c2c129121848418038050402140d0038058102c00718a4000d0324186259008002d055209941c0c242060340d21a180781000065400b544d06086030301c00c40c0410104e110410704581041150703a16901400582c0c521030140780d0700d100503610400c804038000c80c030420961013035018607040001540d60f10b85041c0341a04038020344001110a640d5070116281100c1041201e00c603442048404204209610029403000b924182c4036105480c207121480d113800b0203c0d65414658881880484030410000d6185e60040750009040000c0e00f0214400c0c1d5408502980001291001d4100301d074015451030340c4000100015020720024018001d0a42c0030204050686008011135480c3c000741040003181c05408042c0b91840c0700f20b41c0fa095410030800722500d0301600c0281c1c594841c1c680130000070781d80c02c2c4000c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 539883201 1250 539881951 539881961
    0x30a051b01051821030a0e031c0c03052412010e030a02030414030f100b040612031710140103090f0501020712020f01061d060a0510030c12051b0c01 65
    0x3500e154645020810408000d04908046000c0da004880045640a10035001004000000614000c0500008184401a4100c0c18030342100700c0c140c074104240701c5100b20070040c03c803616100c5292076142d8682a5a818404d60794013500702d4070851500d20721000d0901010078a2400e59028440b5a210307050007041c25040700e100d400441080b681c1e05c8140b603000070344a8105001e1010319090280310701090307240000b035003e560401400602042103a0080d004000c3c8091040b81c0e401c1502c0f5080002c0b00503415145000c0d450003070b141c03104048036074516000d1545004003c0c04001c1c1c0100380600c60400d4410220380d03058000c0c20000341140c01030800309030308911020002d0056000045070300070059021440442c0000b540c08035480403c07040c3d108c509030356250107900c81001111a41c0c2440301104415076405c824041e0006520980381e03008500450601327a00900402c4d1900400001c2a60015007110f0030044103004000c0c1d8103003c401468803400440c00e072400704a020582030a456020740c08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 539884451 1250 539883201 539883247
    0x712020c0105040636050f0a081c021f09150e071701240503070e060306060d030c05010608061f0305030a08040c180b280b03100324060f0602030a05 65
    0x145c050115041a21081c030301a150050301e00610840303102604034140038943c1400c0c3e60942002e0801c41060042041d00110004841c8046100d1010381203400225800801e010b18082200450803c9840c1000450701c00072600c0c581c1c9071440e1030080f14412102013075004c20b403092524202d002d0003c03001c600d03000d810303505503110390802001d014200c0754074400010400c40310241c0681d44942e540320382c10403141c88210380454041c0c00c60000240b59180c65030000000314401e04010400c42ca9545a0740e00319884d03070b0806040d903804002401089009411610a10810108030708101411a612640c0702e0207044884024403121501240801100f81d90410140071f0724440905200318540d07000c03000c1c1220607401c03401940740703010003450202082e8104c0d21422000f018070200600e0255084440d82c0000c0588910502601021001880c00e003201034011211741c604101c441d92070030f045c0080301ca40d50f1101c3d0240c4595801045066004002c0d582c200180b801e0032521031140350758941401c3c5022038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 539885701 1250 539884451 539884517
    0x7020f0715020f0a1e02060432060c030d0f061d060103180506040f050102130f0f0f0e0f04081603030212010e19020304020d0204110712020c01050406 66
    0x4042041815804400714100c25039003141c020b0100e505a40d92518a2502c010307049603290210707800100b40c842e404030440362000e007996250540e200c03800010301c0b282c1e0f0070ba180341020300312044404010300e0300d0180002030216001440c14640d0341a00e0707641d100780310b207080c406610b84401a04c54904d9070320000003841e02991500c0414950700c0404c400d82000c441d2140400e01d00b40d11003050040047c0700300001c5502400410090b02c072038036080042c056203441215a0b6400300105441c944416031301c48000e1499404c0000340901b081c08440c03503562150001590345a0100b01003000403510f040d44c0c2d4004812140078041c644460030424124030994881403000415122131504141e8154010b00c00304101c0041c220590341c98003e0080304c048281c603580121072046031030600d045501c1d40150b0300310f0701c005c140d401c012055a0204003628201d8002d15400c0c039010603100c00780004001314102902c0c0b0303440600b218200300350000c0d1240c0124000c0c5801c01c15682c91700c2d007010301c1140c2003100124082c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 539886951 1250 539885701 539885713
    0x30b040b030309030a0618080f03090f0d0525061a0f2707093f02030d0e06070605010602030705100203040b1801021e0a030e07030b010509040c12060207110906030d050307020f 77
    0x70040c19403540295004140c62150f201c5e03d840004020492613715003441e80da1034601014000b800708151188410013403d50034034007910002803140c7c8218070110703c8285000e0400c106036003c005d60040b030101110f00801d00701d00048411051003039070744841e040301c0040c469581c862075800c44410700d00350000030f4409015905503c0c211080b207007501414a1100c0004444481c03c0304d0b8140c00074148800a4050340038120701c600301070007010410010031000e09401d00b0321006894034015908285d1000d005608001064003d01105006035054204014400d40c81d50030182d44910788008000c0c00c4080d9046005140103103a402901100e4009c960006201510403000c14441038560140030640c02003480e10300030703444401001c55460100d80d0414030040711030380f8001c240100080020001c80d00340848040c04100f844070b0244240d0a207004007001601c0308968034120742c13a40d0003102e2840c030070b1031400100f0003d03580009103030b81056180d14019449131100a804da15102803d00e441c1414002e04c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 539888201 1250 539886951 539886967
    0x3020c04050601020c09241806030618070504050604091b0f0f14091e010f0e010b04080d1409041d01050a0506010c14100c030b040b030309030a061808 66
    0x144240004208580030051a2101001641d98405401046801140c84400a05c6e0400d80260002e010001c120114902c00c5030440025400002020b0350030b002081d40040c0429400d0412081c1e83c880451148a10406201039255981d28590310a040c41151110300180d0389817980d400110f6840d078410107654021004424901d01141c81c9c0c081c0140383d0460000000d4142d030081c0400c0129a41184080551201001030250780301d13004014102c3d2607028000d03000e085d603881012a00900c0940d050000b50384c202000c5843e20181a0302520300e9140a03c0180a0318802041c00c42c01c0034501d06103601c4031003007044a050140030300907100f948507103400100380c02c0a00342e82409a2030b47d2903200802c49a0b840581e0740040326025213110f40010170312108400050b03c05000c8840042885045a40815003600320f00b0030303a0101c0d408200080d84801c034400743e50400e8050b1110800b421000b4500b010303003450110750395006004020307010715180c1d4207070441c4044281e180f50200781c21040a595908903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 539889451 1250 539888201 539888203
    0x6040c1401171303081f06032403121b02131a03010614090603161503060e010b0901021501050907050d020f1602031005010f03062d0c020c030102030f0105100507050105040302 77
    0x11001040c1d021950807000100110902c0da0346d52002c600f007520010303400c0c0c1001400c40c000d08101c852020a2940c0030180300c0c000440003030000007907220703050040c0740307500d5107000908035010aa80350301c20b484441060801a50344101035004861451000502c2c44845002c00c003418100d20340541d00341d480e240c404201391f0b5800070208000103003070301d00c0030719038070f4450915030b0700e0300c074a407001c420054412424070582c4c48100302040410b08030719000c0745d000c3e141c080548943c042039200c8020a03000007158480c3e540c0511811110302d00f200b9044829601d4500440e41c04039004003c130080101c0020509401c844c90b42c10b90322258180500715031034441d0b81d13103050040303c034080003a4440e00c20100d11061885040c01021f060b2540031440d5480b41e8550b40d075800c00707440000e5140c0840c03034030b031030b411800602000d20720b07124a020350401290840603802d01070300303000c4181d001724041d0f4010000c11011a61203001e00341110310940742150400090001142e450061440040c85c0d075003842e052009141c0c3c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 539890701 1250 539889451 539889481
    0x90b0709051207031101142d0c060604050c0d18140303010305100b0d0609051608010608120d0204050a0f181814120c01090c050306040c140117 63
    0x125165001600d0300c52082144403280056081c00b154090441440040c0700c0f990300c1c006850042c18142041903d0360809421600125200712000c000030520038100e05090342144554007042c40340f54504440e045c100c9440302001001d403030003592142d010440030a003040403107200d001d581c41c0410145003415074445001c00761441c10750b02c0201030070480c400420b01204a074100c81c0d0102c02404441c0f101c3d143d04001d0918510440c0c0e008031201c0e628000311b0054090001440c1c8140e01400300b10103610301e030741c0e0100c0e00ea4000800c203078900f2105102c0d0381c0c0006500500c50b5211010a51180c00c40c9844001038800c6400460300404140300c0000c0d45040c070380041c03041d500c1041641e0380c000300420b030880499241c0d480e4496920f00464005003c03070146e00caa004421451015501d0340707010148402020703400041d502c082070307540f020f040e001c1c8510006658041c0004030050980c81c20030b916810300d0441f02e4080c03075a000302d000d1004001680502906191070640c11450a0303107103800c07080840c010b0b07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 539891951 1250 539890701 539890711
    0xa020c0301050a11040e06010e0915010f0e030d11210304031211070213090c06020f0606090702070308030702030415030b0301180b13030c020d12021203010e070f020c04090b 76
    0x76003800041050084039018440c8040500c0c4402c608091401c0f060306d45202c0007030300c1e6a050018a020404498a6616010f8420104880ca0240721511140010281e13010b059604041007451301d040b841e41d54000c28905401c110030324000c4400c085000810341000000f14600c42401145007055031403c0002d0091403041d800b94894440c5c04134129824410b0b1290010206a40f90003000314500511f050000c940c004502c1c0080000c01039556038a6182c001029041140940d0100d544041070341405c000055100d0015034000702c843c02d00d140042d40d0790070140802060504c01000244800380b080080e0380041c88101030107119081009006401461006006802075082110269601e5550346c01d040a80ea0302c2049003696940e5401d54007008060544201d0070070810701031031000745e51000c44140761140203401621130621000b001915100f0b0055200f80c7d00302050004115158070396440a0744080c160508e000d94004000c0c08900f0500e80443c15640031340780000501c28001042ca100b03200d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 539893201 1250 539891951 539891953
    0xf210102070c0807060c0b0a09051006260705030d140c0a030c140312010b0d06031515121a150d0c03060c0914040b01020a0c08100b090f1b09060a020c03 67
    0x4075445040486e07080108020107402d00c500580400c1c0d80c018545d004d400020f0289007681d141510490006054a00ca540300305a0005020170b00c0b85558451848910405084c100070083c10b0310f42004a0b4440f00c2203c940c41c10710800d2058210a410032408880711050311000b42d804202443c54003070034001c07600809840800392440c0f041310340d4000204a9080302d2021109920316860203034109215400b00211074170241d2201400000101c585039141ca40c0c540c1c078070b00448c007043d03098511000c031403040d400b0411289080d4a03680118510480000940450f80883c00311541c6201d07041d4a5070903d04030660300410b00d10528400d02c40f0200c3d0240c1603d10405003440007600307800701190001c403103004111440c1000642c1081d603141c5544141441e11040c011b8590300301054031a4940300c0940da0081005400a40105d19410310503c2941c1100d101110016603d046c00c58824a0f0f00100030442c81c04600d105107a40341440840301940c2801c14014030304c59881035030035002512811004039807030217 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 539894451 1250 539893201 539893213
    0xf09071e030905060f06030f010c080a0c09061d0f180a062705090c060f1804020a05070b0907031b0911090d08130f0e0103110409020f210102070c08 65
    0x6690301c2400368100c1e041d0000d00402c0e03152a1000e0b0842030080c09011a41e05114410b100000044207000b4501ca008890304d554046203010102c0c0c005a582118140b4200110035800380f104981240003590100f91011028580b210140082801d240d80300f0b00c2a23520040e50b2011005240d640c0034810f00c02c5200e11028041260b64100b008000c1c0304811071040c100070010840c3e403070a001c83d4001d40c1e202006034211510b41c0e802e0b6000c2000c41d8003005030003007507582c00a900d041d40704e11840900c0c1c0c0704a09030b07821840c0c641e107808000c205005c3c0f048001c01c00e662000214186060030003652001c4c54000b80c04828400c144122600010154231030000c4450070802039501666000099540c0304002400c0000014030b40c5d600c800b03041d80840c0307543d04110781c03101000c50682c0300c644e251400780140740701d04041541141803a1006171010042c152049003007450b02c0d80140c0b5940384c01000060207641024000641c400d601c0c00710300e1ba017104290158804540c05051080c00031030042141c1e140016142 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 539895701 1250 539894451 539894507
    0xf010305120f09060414011d1309021c0c0e0f070203030c07080c072709080d0e0a0b010603060e090a0f02060a030914011401050d03020a020d020a0302040c080a0b01051806090f0907 79
    0x906102d08d0755210b40e125504030001c250302c0005402046000c2d10041041340000d0589003031410322070ba86401a601480400c0c41401950240e103000b58100728060456507240c604014003d44c5e80c0300081c40344010b004089071060410071a0001d07140f013500720000366410540c0f10f54002c22000c0e09406c42020383d9106040d1020390b6555403248001d400c2d080081c0500e0080945101c4e000b409810810030114400c503e45400840c40002e80d960192203184c0e4086015403501079000d051010140104109400492450001807405004460243c2d030569180d41c81d075511101c29002042c118034054110403a02c2040c2c102118107501c80751146130341244152450b600c2c1d0040c0205200c60440c0100940d0081c44006c000d803a2054296502a1004100701d5a803506c036404541a07610b00419080032404600902070100f045002d0088881020318000c1d0402c410b00c051034102c0899829044d0085c08005065005500c030103003c9a41070740043c0904606042410009040e40c60511540311800e1400000803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 539896951 1250 539895701 539895737
    0x80f19030b19211205030603062203082505190302040e0a020f280f0f02031806190c1214090105030720070503060f010305120f0906041401 61
    0x5003515000302a64010319080c00008018081d81e0750300100c0340f900c07000fa000b00080d007041c1c001c0c0184807a07690340d070307124207090050600d0508090921172202c46400030080e018030311071000c0030b035203901407900b400240c640019860141d818400c0c0d065134040c5c51a02064420b070803800420188060260b06101c40a0f010011030480c000c40c0551008244644040ba00c06801600506a0190500c180500d006062619031180b21355240100d0381e0030327101c0001d4003086034000441d074a100c0c2c09410080d0b440020301c0700094491254401c0d42c1400c0c1c1c036a10840d0440d807078120680e11030622000142c44840d542440180c81c4001900d030031500c10705503000a94009114200040d0b02d000034803085410a654030b001560315801c020040c004016071341c809d0585d0821141000c820f00c500da000508406424002414140079005105915101c100e03801040003445c0000c82200203004141d041c1e07203506c0c000c00101054800c404006502000103c0d01090120b598621070fa18140d003621070142400340d5900348 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 539898201 1250 539896951 539896969
    0xc0408060a0507020a021011160509090105310804030b22031d0f040504060b01020f0a020a0501180f0f09050106111f02120903040914100b07080f19030b 67
    0x11801600a00c0a04c401411f2408480f041e040c42800e0941c954a002e80c4041d14110700440035503102c1503c01d00400440c1015a000e54220281130001e000503d8031200200d4035280610207248084008607502456011310741d41e00007469807005441e40e13110303900c0c20803811401d400d482424a02c0e00b0b0154402d800005091001d4000b85e040d00d6108404500c0da090301f0106035148081a04030014482e507140c6544c551148921032407048100203002c80341070000911700b50030b40d805042d03160b00c070b40d01403005661451018000c44a003403800340c101d5440000111461021355100d645210305041c0003280d5000440c04840640350300e200200031580e682e04c01101c506a40b0004200390360042c0540c2004081005940c0c400030307100b800d000d440d00c0e0f20707124860868070b4200c40340d20f41604042014410050140101e01180b80c03010020f40c502c3c01d10721051082100310707100c0c8030682d0310000b6090041042d00340c00d4030052001301e80103540707401e125425103040040b5806888006443c1403404040f91626004c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 539899451 1250 539898201 539898211
    0x103140f0a050c010507060b10090e0903040501090e060a050d06060602010c0801180507020f070803042903221e0311030c0c0103020915070c0e15090408091201050c0408060a05 77
    0xb0160f66580d4801500c0700c2c1d000036410707110103480d0300c2d040100f134a58490304003140d075a554070021494138202ca5201e005101905a88807900108000c000c00d0b030340012864107482e040112501543c8862001901e11401c69101d80c0c2c02c00d21140c5035a051000c698400411202c20b0340091140080c0350b0302c11075100c00d09004280b410140754072075001c270441550180c3d6001c20540100c456881c288030b480d41c42e018859120b40880d0f40001814001c032421840241c02568265445040031500c1c6080e0a15038000200940c44076080e01c1140d40c82d121348010520407140d004180288c211040d48014480100b10100c03e5012030030001142030311034400801c81e9001d604550207040c8038000e900045000c0d60040008950041e0001130120a6014a000030300a40d4404c00c0146c010b076191031004400041c005000031b01140c940910b040301c0f030f260508119842039011024a643c0c1c03445000040744010110050388440d0300e81402c00c03040161100050081d5241c00741110200d6a806482c03005450003120 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 539900701 1250 539899451 539899453
    0x40c0906030b070c1112012c030a08090102040b0d0c170c0904090201050706050c1b01020a0801030609082a0c040b0d0b040c0b031f0806090a0224030103140f0a05 71
    0x507102a2081060b102c84900c103081e04150912140c0011b070012640700948030031655940f002300524055600c1002c2102410088940100102d00680d43c4900a402200b4140000080003d40c5004207504840c0075003d5a881d42d40c40b11041c101c0c4030024403507510b10303101180d60110710784c0107200b50940301c0e80b10310300c0018103500c1d00281c2ca05100c003414002d481241400300501039400041e00a020b04c070302c40e01c50402d41a0b203a82944105140600c812000d6079a2a44100483c2d00700e1076100c18401e042d44c0e0416000700304820145401c410611600040c030b034003001504440b10b4600c070111003860b5080e402031300f02c0300c01c080b007501084211442c0300c000c20b074000c00e042a490b000a003440c611aa216006c0c3c0303001000c0550f510712a2190341c1c001c84512003940c1d00e203e45500dd81d80604040005420000d00600951400d101460b5566a003500c01034428030480c68440b8207032451b11081224050f24000b141d0316035035203280072410844003100c01504c90094a03105040d010001680e00f4250740c00c24 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 539901951 1250 539900701 539900723
    0x70212030c0109211d120f0102030f04020a0e040503031f180507080c180f030c09090c150a050306040b060910050702150a0206010603020705030909010803070201030f0e0d0509040609050f040c090603 87
    0xa400c102e40c406c10051141e2060040c892a140144d00c28406503105081c408120820740c0360600c10845010b44c0b80d0006907008080c0b10a21011071320000903207502c00c0101e81c82c072018181500075080c2c40030f0b407540500346104200e589031394003100a0300304030700501c002d444588490300d49040c10b40703160007100b15451031442d0b00030040d00360303140644400c89101e801606580c4c4210401d00801c400070b46c100c13046981a44540290920713810031012501c4120096100d2a040c411100c90051044c0b0015006d28030407615044111096901c01c0119080208000c0c00e0a009904440c00078089802170b10303041e481040182420219010703544129000400e4940c00b030f00c1903a090100c00e60081d0881e40c0251540c1c40188485440d82e26103208090107444004001d64a6402910004058130000001415a24101358a07072035a11030005015280980ba030503c1038661140301c0115005100d9580241407042c182010f10541c500070004507802a402100b04801207503c600f5041c094680510005281d21519 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 539903201 1250 539901951 539902007
    0x60302070c0b19051e0c0a030f0c1a07110607120501050d020607151814370f050d0305070f0311030c030402061303110307050a0b070212030c010921 65
    0x10b00041c1007690490100c02405c030140400000c4035084044840c3c955801014003406050300640498119800c1c4d20f4001c040f01350b15600d000c254514052000840a070b40c601041c1ea15008011445243c8400f00403145140382013040108048112074840856915100000c281810400b400101e16034000c2c0134546000c2e8203a580400c40003040c0900f0035032a54503480f030612400c1001c1803805c1140101080c1c541c0d040c00e00310031400c080308004030308041a403c40703c80d225550121800148082800041c0044a441c1d04050780d803031014040091590240603089083c20b80c26521003401070b5450354032044079050b1108150700710307026483e100031840418000a0015854a0000c40e40305101420310b07402c10b8800c014105529005810480c0e081d94440600d494030f05040140070000d200071031b002400c1d5441d25130541c0c154440d403a00607004494124080169100c10000c0743e5507a07851134020402e5601c0c50500003074800703801c09218242e981d040e094014280c42a070758200c04010301c1c48510928591 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 539904451 1250 539903201 539903207
    0xe0402030d0e0303040f0305030d0605040b101b0203150f1003081c020f0307020c01031104030218043f09080d0e0a050a0e0603010e030a08041509020a060302070c0b19 73
    0x10ba0b50185a05110800c4049420500d09801c140214446c034003c54840320113100c0e4405484041d0403a03030003545040e410101c140c4e183e80d01c0040c04152400c0100303203150402c441c030814200c07102c0080d41505c00c056016001c020350303031003e901c1800440e444501070780700c83c500c581c1c000125200c00f41c01c81c40c0030b100340d07208890800e000011090081c50018a0106000c0091240d40c004850510240c5c000c0925a490b07560180944035443d040d0f42e032061318042c2554006080c0b8840020268296441d8030000350401000007203108a200000c94100c2841614622005c0c1074816600c2e02010140440064040c490180d01c0c1c0780141c0e84079401528919004003000c070b03803e0100000f040d41c041e10714040000e442c4c071403520a0015269000f010125031800788241801e403048904003405a5100b00243c0c10000e0b0f0044686d508164024921041e1201181a039405408807040c003075030200d03003180f00191264066008045243c4910302c250076440d900c0c0032001140c000e02600d80c08050040c6400042c0700c3c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 539905701 1250 539904451 539904467
    0x20f070b070504090603050c03160605041a0903070305061b03061e0d060e0c01020712020f1c152a02030906220803130b03040312090302031605160e0402030d 69
    0x10442c54081d0506a5504c481c10569505510642e1345030018001c2840a090a011680c418070f01011581650b502e4a0001000c601c5140300d611000f41da0400c014003072000d0202118000391001f0100c540c2192a42070850321081705039406d03008000300c1120400d00752000815248502c10082c501a4142c2c4503082446131510458501c950040511901e400002c200340300c0e25054855100042c1115000c400029250000e0b54100c2c56051078034a91701c100590703501070081c8103158252000c0120301c1007090485042c80042d0001004085050385081404901d80c0c042145800b01c18501201c00e01c03201c0340c80c540b04a26005100050708100319010040c00c044008041c0903205040a8001c80300f404801325154a00d81c0128800e9007000941001401011000101402c02c040d41a0f140d420551381c06050002d0a0030714088880d15980c4941c203060090003076030041c0500c18080c026034000d500d4000e440c2c98588031015108840b0b110003086030040c04446ca48034550140040071482d80703401080d90510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 539906951 1250 539905701 539905711
    0x1203020702030118030f140f04051207080d050a0e09060102070b0a0c050f0c0916050706090206041d04291f0f090204080607260a0f0207110a09020f070b 67
    0x9904c0b00382481d49003400e54801542c19000b07a49240f2080c22004009001503102d00f91001c0280c07090040304100591700d0111000c403441101e1016002c6203a409090034062aa4040c403001d003c4c0a024050a54110005014402d110360b1040548140b110400c8040300056401c9801644060411300c0030a07492801460032240c2c0d401c01c441c01d804c85950f418035110007031030000c0664018050b005400d040c000d00ae00d412800c034800701c0b103034644025401040c50181c2c0b10003400f250303240d0201c10107540304c6604a8004e4600090b5507100f00708840f40758060300c1410f83d0200c0d42d0341500c1e520240c821040e211080f80001400c41021590303184c1310361500b0f005c0300f4026103c80200c0819800071781d846014000d04001c000b040c6015803103500c1c090585007400401000281481843c6a080600700d20050710181d00c900d506040d01840e484414400b4010804400001e907038910008203041800b00d00811803890304000c0b241c840400361a0143c00043c0d00606a21840104040c000c140004140c3c81e9010703401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 539908201 1250 539906951 539906953
    0x3120705091005211b030a1409031c060f050f0301020f03090a0b15010c030c2d0b090a08040b0304110924010f092d09050105010f0804120302070203 65
    0x12880004020b000031030031100120b140000d0400d10814034444413040e4262144611013985401c1c100d0140c0d21008a13000894044d00000003000110141d20144100c0c0c07000340c6810341842c01e05c14070340e0790340d0105a00921645541c51b103001c0b50700450040c2d0090302d00c83d04101c0310140c6020103010b0036000c0d264100da81950240070041c01d0000c60ba02961040e01c00c880100041e0616041070050420040c04480d100700d110010200c450342c22001005045615181000030b1b04120f0400313090185400c0c0c48551450be0004542c1e0583c11039414070040c99005030b007a00c9040d103940f81c6080d918260503e000744000c90500c400c0003020400d4010b035034002c2c040c441203003040c0c030640c00140c0407440440e05960100940140b8800c161600300c010041c0d0442800c0629104610250160000c6807074410240500f4100d40c503911546002c0e401c0e850181c01c14840c9000b016101e0001c440905000d010b01800240c81260000585129040c01c5010ba5044070035400b80c0c10030900c00314040d51000d04182d0301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 539909451 1250 539908201 539908207
    0x90a15060c171305091506030118091b0503070f0510140c03070609060b040903080604021812030a1103070305090108060d0b040f02010f0e090a091a010303030c03150803120705 77
    0x59030002e000619501c0303100907003003030038034184000c01001c880044c002c00d04194403624a5840c68a032801207070306450260b520041c8240e041e000250242070038140c0100900024031110310742000c1d501c648400d50304200c4c260703074110340c0303e1507050507502d03844c0315840d801000340011605290007041c03800c00390314682d59038510f0302e85c5a281041c61030b0301420080300c100c0d55610303108040c811103100301c244140d0201e40c28482c0d4411a1002088000c000e030403284a154000307464500c005030b07049007500d48031001e840190050030051900ba00c07904032a040002241c10001d411400c62804001c4a90296041d2201c0381400940c1c0011a884d000044c20b05401400465039000130401310200c2c1da12540c400c8a090158000500c001869031406079451400d100c3e10754014641c0c0d95411b02002d90080d120900002c07000a00c0c01c003400601c1d2854855245646144000702c00e0652580100100c900c00342c40510000d05041500031700c5480e10320400b080c9030400d100d240440c00304500c88541058062401c142 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 539910701 1250 539909451 539909483
    0x2319020d0507060e040b12060402010806040e01090303020705010c0e03032209020f072d080913020a0504091a090403030c0905041d072c07110615090a15060c 69
    0x220b00700c0303035400400116001d25030b04d015074506801803001201c0c080d100703010a0280903500a954001c040c10082c140042c05001802684456006045000320030009102c4040d203402d024009500850055600d9401c00707040b080540c1c02110403c04124002d4000c5180c2a540c00c40c8205403c03d9401280c203000307001c1000200308030a13001a0039800e441102c030942e1440c0524181e1241100101841c034009596500500c6400c61480300002e9207400400e0282e40744c1900d000242d000c4801ca1041c0403582c4080344203002e0310384c404042d00075100c0003202040303c0600d41000f0b00e80d580d456222598440c507190000703000244030381c0203140b0461040c14403292003a180c0e4000380603100385541d42c00c4194103501908030840d40400c0480b0040800d03141714903103541c0e41c150b000c00111084800b103500c0c00f0b226000c03942040c0b16003640f4030b520140c603099a4450426221410486164030106403150400344042a0402c005105240c641041181005003d40c50102e06450301449040c007aa581d050920b03e032a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 539911951 1250 539910701 539910703
    0xc070209040b011e0503030a03110903010c08010302030624040b0301200a030c1112070309090e1515010e040c051204050105061009081005100b0c0a2319020d05 70
    0x140914410300c4038003070b29070500b410074900c0e00101c07803c2c58111100a00801032a1008804c507015510a4540401d1050500d60b907038616100c3c0d000403039019171a080b000c19080d54006c002138180c0f13200b28107079500b0383c27200c0e84150714130581c40030a617841c003140e403807215103510300340d4451118584054004221103060500c0e100241c0c120202c514038505001810ba01010307454840d400c8003041504042c3d0340c0d0a108910a40d5030021b0701022100c14a000a0410074035005801c194000d00c9840000d2040d40a19100c054852520281e201010301129000c500443d941c0c014606a091040e03540400c5d80304498108009491840d001000303100080140e4181c103001210010300c114014000403502e07092900078054805001a0004108118698140720321a008030700007114624901d0003007243e0326200b0020038101d055502c86d8540078070001b80e484803020003240803050740d0700a02003018422080e0300c1243c0f54030500b4426900b10740090b4034064940c0e00074501d143c070b400e001405001130311400359030346 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 539913201 1250 539911951 539911969
    0x807270b0a090f0b10110a152d15030b061302040801140907050a05060403030e060d0204060c0510110a12090b0108160b0a1d241209070e010308030c0702 67
    0xf62010b60703120350032031406040803468103412001e10700d84a00090601d1503590740740c20034084010050100030f01d6806505c0096000412011041c0882c9100080039140c0703654001c59001e050030402c0c4c03d0401540503603100e120303480102c0707070084545c2c031642d07403400f040003a8aa0821101c2813015400e010108103264240700784402e00032002d40f070b28070300d0901071542c0d031400e80789900080c0309076a2145d040c002900e94500b95011260300d414010201000c00c00000c00500039043d1000c10a0b10105001403500c0d13011201485160003441a20425030070303848008243c0d1042c01d00444c00c031000b000a664468880c1caa50b8203e65a04040040d40008560351180c1409013a80204e03c00d51114504034401e88824034401d00424113500300350710301107601e0b41c040c00c1042080c034010000544840782d07814503250303240282040c02c0600341003d5241c11001d007114031904400c9004698128003400240c040000003001f90a032408450b0701a003980c0395603600000d41d44001c00001940d6401e201107001a1a0303d104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 539914451 1250 539913201 539913221
    0xc070c08010c050909010905070f0c030323010303080a0902030c13060f17100e0a03080603031e030a1112040b130b0702010606110a0308060f031f060807270b0a09 71
    0x1900c1e60341d41d9100100130110b17006070000c1240f81e140509104ea40c580203e03c400e800380c2c3c14208101080c2c42c0f41000e40081c15a1007150200c40308072001ea030744846010b00618180c1c0d102c0d444804081c0c8852003114100c81860314003e4040d48003c06d8066a403800040e91002c0114010340420031075107415142918403030a5106188901d481e034003190145105204030002503880d2801000541d018400043d900c9017200c20140500104001049541c0c90a008840a6106000070300c6a20044510608410ba00440704239681a290480c4501003d04210444001d06c0408040300703455141c5894143d0b0f400005013025480b44c2800c54848001a02210746905c6012507400004d46145058800340041c0c05d00446007007a070f0440d001040020303401c14803468100400792181c1d01d4851340100400d2401d407416610b2207000442200b031016230146500001305856605c0b06032400c40d591608400c1c6140101e40840b011142c0d0341c8090018001070345d10803038004400a100c030300324580d01d201c101c00311031100700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 539915701 1250 539914451 539914457
    0x8090c130b0916140702010c0204090b01090606020a08030f13170306030d030e1e010b0307030b1801110f0c01062103090e150108061810061103030f0c070c08010c 71
    0x6403040074600306211a0307010b003052608202446407640002c200d454135140944402002280b1441564420303030541d10f0555001c1c00c07c204100e1641850416003800b4400e03880e18606040c00410401d1000c24026001a4403c00590a40d01e84820000b1418001000124903820520032040031441c4104241034000503120001c1d600c1c1802000d050800c1c02e00c29411003410f00701724404203140e00003d50300b00d1903034103a010030300c03080000b00400340504944a80c9a5140c03182c905c010040c060a142ca4601070f00c5240c3c4c000300780f13901209402e426100b41c109400c18840c428404a0f440880c910001c0c04680000000042c440303456a5003420120703160031a250f00c80300c181410700f00b0541c204039035001501084140980e689000c2d102000c05105401045040000c5400400c80d140ca503c111005402d107603015607040c40c54115104034450486125a8000a06e4110f00c142c05080c08000c4901a840b407048a9000796202c8400a01541c080d08080b03a41c0c00360f05100103540c2c0001e12a15806810703a507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 539916951 1250 539915701 539915711
    0x111605010510180c0c0b01090c0210140414030d060b04060e180a1806050705090315040b040b0405031b060610030203011203030e0307170913180308090c13 68
    0x8240942140d1004040728000c80380010240301c420107414040780310b40700c541c00209040d04c40910444450038034034401403001e4089400480e1410294124030b061300703425802c5a000700341034500c00098a04a45c0e040f140380103004086804200100544ca032aa0701c0181200c0c1b401900f030050340203c415541c07000e075501c180030400340401ca501c10040d4444001c02c03918202c1e4851a0907c00c981850b0180c40740e03090f26510340024041d4202c1e050410340280e00280100403620341142c0c0500300398000c3c0c103040e20030b02492103210384010251004030301030360300a00c41e0f00c69943d950b43d8941c1284005481625944800c0c000521500c2280f035544081c41d6815000c0c103820704180052190341240801c440003414010320052007600305501c9940e80c020b4051a000c00c910a68117081800c1d48100710015021002c260050740c81c0076860030041c11020026100004150006d2101c4001c846030b032034615400c0034410a00c000403901ca142166049140380081e80c640644400c0000c07450301491b800b44446a13254 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 539918201 1250 539916951 539916953
    0x8040b13030c050906090a1806020f0c0d18301b120506161412070905040c0c02120c0a0807030c06050309060c0f070c06051b01060b0f0d1116 62
    0x75202d1030001c26066a00d520300b03050080005807903480041007140c0595132883c0d00b544a06c12458a0100c3c1c13070301b0480456070350026001d007112a511a802242c881d10034020090400d511413101e01042c688071401d5018014289203944044080b10f10200841c0c1c1444005100a101c90a1400421a01c1940c5e65849800101c041c2e0081c8034059010315518612400c03008041800894002ea2006901c85040d0307034140c141000b55500ca5646c402c0b04003404020070000400c00264481c980504800e0304e444581d01e540c3c0301013205a40201206c3d0b000586000000401410f04076007908840907494244d0380001e50f08400b080d0640c28035440405c403940302c06820014484800c00250140c4407030320f00145149041d4404ca0380c1c880300a003055840060000d000343c00f880c1c640c803e4500709640682c107020f03d241d480e00c008282c0d030021094800c030909580d6522203c25014030640049a1408422034200208041c1c609909d81020803665406a11405100b0304041440c004121a027040c0c250118a2019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 539919451 1250 539918201 539918213
    0x100f1d030c150c07020d170f0c070f030c030b060429040b0904050c01080901020d11071b05220612061b020111090409060b0909210906090d08040b1303 66
    0x40300450382102241c1d28240300c60010440c048410b01034040d0b400121b481082d1925940c02c00282031244800240031a04910300c54440c0021300406444030300322104961034505410201c4410310004080301c4c0451020400507032001c8405500501c01800001c514448405252041034030240790340c42c183c05800c010200c3e252600c1001100f84003569600583c1c41d045d41c5a0b41d44a1503411000e05110b0b8020000b04440b60940450f25110710300d44040c4101e20301500800f141d03802045007111910488030030410101c60604400301110300c01030203800413000c4030403500b01500444029980d41e6455042c0400c1401d5100303150301c030b03683c422840000d07408a00c3c8221001c103a600802e4408590404d480055040006010750700082021240012042000c0c0f8182c0d0042030301c05c005d5030b0844644010041c00c0780020441001000d40c4511141d00200c045a0301126845909605607103c030081c000c0310424140b11400500d458070510b4060325003034950300d90300019048801d40e80c3c0c0c080c4a0040503c10428 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 539920701 1250 539919451 539919463
    0x711030c0d11100605150309030d02040807060e040e070b031915090b101d06090907020709050a0b0a090f0603050303010b13050d0206030a05100f06090f1502100f1d030c 74
    0x546081e080003454145400942d0302440031b038031002903000200108031122800d00884203140484031046540710364a0000c240c6518040c4128004555500f4007018a810180038522540c0050009401040d04007407140e401ca400262407070f0300e40d21414402e00150607281c417134081c080310202c4024186c60301d05500c0b0410340b0038101d4603e001d88200100d03030884a40041e00080e6101c26540318614080d41c07600803804601404001581c0b2000400902401c00d03004550402541c807050f030706009070ba1300e0a44510039980071010440c0c000c1d851800c10041d801d01035002d01146009e01e0000324107a540c2e52a806d2640e002a0402c41280c0000550303201c0031858003c130308000780010f030380309081d40403c3d800048460000414072203100d03440d6000900306003780c001c2c00000c0d010740050790062a456000007086400c0c28092a2036003401420003044d0030b4081d031651180e21504e54010030002015a50002c0030b44100b1b102659015110382540500c06403c030803c41c98107111400440e143d1600c004a00e01c1d01e5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 539921951 1250 539920701 539920723
    0x2030a06060c03080f060f060d0b10050405150304171b01150e041b050901090c120506030c060d060f0303030b0310060b0f07050f0f01020c07140102060711030c0d11 72
    0x921851090001e60001416a4412031748620341c1c80e659151004514040906001d803035028500107884080e2a0a95002040c0c0b140180c2d41400843e01080080d22544214060f0580c031441c003039140c0b051000d8100007540d02a100d0307400c480d409800c58404107003a8212108803100740061002031384c001c400911914290001a608185134246410300c01815290042c0028081c0e0410003107214404000c40180801098050207041196035644551801840403c85400001e60b200c1c20036100c0e900c0b07500905000701e000401030300b1a000a0b10400415900c40051064050b07141d002c0010411308a9000d600254029200440c11489113010181003040300d00c0310401c1e003440e0203c2444054502d0042d02d4841300303d03030766080da100340030300300a45888070b0245580a1031040e1495810500701c19006000f00040714021030312107941342c42080304030903414406140140d120100040c13185101d0003c80d4050441003040c0da14045d08405c010382030640f603817518804640c0c0d0881c1545811301c10042c8006d50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 539923201 1250 539921951 539921957
    0x3040f030b2410020c10031d0303011d090f0a05101b020a060b0f1e1008010b031f05120a0506060409080d0207050322060e04050609060d05071802030a0606 68
    0x54030b18640358400540d402c03400c1030300a800490301054814020000f240880e0030040c001d10711a03c54842c0140038015100c025448042d00603c0c80d41241c0000094074141d0f540c0c42806501c9215071108580c246d40e0003000f000d0148121811034079040818480e8442050084d0043c0800000c45c11101d000c3d266001c000d141d000000c000c0d040c1d18982d01142c2614010750141001c507140c000000003a0031500003d080e258840350b014100840d50f031480011421606041d107a102d101c0440302e0b42611001400d00c10203005a0040000401034074420403026801140415500070030740d101c0020490403001c50030301e41c0a40e80503203100c41c14003408000d035a030f011804650a12102205654a0610340240003511044030340100e450000c018040c17041d100041421030802081d0400c41440baa4186550720800c008200c4051380c0c0361141c08c007070040358400c03d809482e010700f603202d05c2d06020540c0c21001e0103840c0d9018828022030b04603e9004508081c41c100380001d610790a280c0c5147c011500c0990000c414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 539924451 1250 539923201 539923231
    0x602190f02010c0204020d020a030b030c09040c091e060801050a0501080d020a0311070503190b060307030c0b031005060a020307020a081c12060b0d092303161403040f030b 75
    0x85010500c04440c0d80e0a2070700582a40b11440460085c0c05502c954940b81800410b0400029074540d1168030014021001c032450503250006204e801c020075140942050702c0361000b40704060558220106d98504418103244a100b8160b0403c00c4a9498000c6c2ea0a07945a8041c0040e101403405454007500200000d0103013207050b0b002c0603560348100c0340028140801d0b58030400c61288244051401020043c0694105076541000c0d051131a1300003400720f55450103040422014100081c100b0240d992286d40c1e00c031000d080580807011600002c1c4495480044828003007807945034900034218220564005548411042c0b0404c2082041394002c158607034881441d51710160400e8491025513101400e00340920649140000043c10043d0042401c0207000243c0003000101ca90103c2c2005004080c0d10440070360720001c6e100544c078900315144d055441840540e850040c3e44581098407031082c010040b020740d00250950450304150320901d00303016942e60030814841038030409036202c04d0351035602107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 539925701 1250 539924451 539924453
    0x170c04030b01030b0403170907091e060b040602120306030307030c02040b030a06021c02070209160c0b04123203060402040e130b01120c0614090301050a2f0f2a07060219 74
    0xa5500d088ac4510b028050f19040d558170310798126008080c0c034076a010b805100782501d61500d48000d07031092103844014800c0d43c2041c1c8815010704296402600000d01035450092961002c41c0d030201502c0b0241c4e80186d4a5140c0e50a664040240d1076030030307120b500c3c090b0b290301c105941405400342c1c0501d00d540351170041105030011b07a50707034030740540c0114012503052a002029008442c3c0061b03203200245500c03031000611090000c2c02d1407007031500d070507aa80e014400b20030041d84003081c00004d007440d1642080717881140743c9503945400355501001c0540018282691011004101001510320548500200d54404144110b0010b41ea01410814816600d0865076030f0b181912065240315400c1004131200c0640b09107544042100c4241c81c000b40248114180000c4600003051039500d428920003001340d0b11007100151076012541146415125814161700c81107518150340108404410300b01048404060b951001000300e400b409002d0040041906148019191441d0300381006060301240c140c000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 539926951 1250 539925701 539925703
    0x50325082d130c030503030a020304120f1707020102130308090307060905011706012c0103051501050d0510120b0a0c090b0306061b032d0a170c04030b01030b04031709 73
    0x19030001c20030041c0761106101403c180c8600c1000d9040104240000424020320b0303c40c940140d802903003d039845580b80b00c28500c0603643e5808642600011a00401c0e12200c0302c0d0f501d10129902c00050f00001d4a45280721210750031030b0560740c100b240c914030040f51404070307404d0410020300030740381d5411300003081800d00d0006065180d14229600d802400380f0002199a440b8810801e0b045007540140301c0402c000c200c1c40d090700b00c682c100b00e80c00a8a01400507402e010007202442e0010011f850f031a24003291610039801a21000b072600c3c401605941c0700107991403900803440c2a0398055112020a82000e800080507034507052000303001c100120006000301110b910840750800011560103a80e403542a000c50908031070744202c403840340030100d00c5440700040b030305800c030802e50910902c0c2c220099140500b00035002d0b000e1020700191452111184050b000c0070800d403c407003030514042c01c05a50365561484200e090b003080303442a60030402d21007003607001a070031803c4100e201b0403444180380c008085 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539928057 1106 539926951 539927041
    0x21516060f0b010207141201140f0906010803040b040b09130e070609050301050405100513150b120f06150a1805090d0903110105032508 60
    0x2c10307082d80b02107000310903039000f00080b8000103280c0f01030041900c05012140e1180d907852404101c202c0405005520941080c03500b406031b454942c2d00c1d0313400d286043e8001111030740103101c140076503404a01500c01303681c10a24081d4460390342c00d0010703d080104c1140384085900d0030001c0c40282c2c0c0041a0b05042d10b0041e00c1d01807a60b50fa480a150884d5000c036805881c94012403842c1c802c511040d08420b4001c00ea060088003404081d8641102c082d01c0d281617482420340c0e601c41d660179414880c005008540452019111076100700105544036400184400b02002a040d030140702955200002e0001d000a0079640c1048607410180800425068a10b65820b12039041c800344440d00c280300345020399038814208402d81c0c11031780054980d0380004d80035600120094034402c04619102c003d9108103020399951014508200035503081203080b0a84904640541400c1d0b013692003054451 = true := by decide +kernel

theorem cover : BRFrame.Cov 539748201 539928057 := by
  have h0 := BRFrame.cov_init 539748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539748201 ≤ n) (h2 : n < 539928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
