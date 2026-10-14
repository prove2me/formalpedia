-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0460
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:55:53.422447+00:00
-- url     : https://prove2.me/submissions/06d7a107-2685-49ed-a5fc-adc175ccdb8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 82553958 ≤ n < 82733814 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 82555208 1250 82553958 82553963
    0x90103240320010f120213120302060f0606091903080a0503040b0c0909040305030a1410080c04020f0d09031709011505010201050403080103030f0504080a080301080705120a02010c03050d02030f04 86
    0x901000d02d24090700e03074041c040c0d40d00103000616800c00500203500400001841c130254100144c2070580180c0041c003241495400884050982030701c8009141e01400b0507a00021000f46009652034960041659071140b1701840e80103202c0021241960b545c41201500a9a486085a40e440d120715000500540050354240c408a900401080c110244481240c9031a50082d01380c500564642d01e0964030760f00020440c4001a44030841910140c41d080c4c4540e204181100364260403904000d00b0900d841125074240303000d188100f06405001c0451002e450706114a0400031423000c803540780454805074107410308050000c410301481480d42c010f4101c1c0c203104202c003c040d4106692200124241c600c22b460280c0801c50460052002c00d105e040c1001c40041036044c141e00d03180e640d80b03001c5d01e07007102e01c0c40a980ca294048018001c0c0d010a100280040c41e0072a01da500c07045008a03401e03103c4000f400003d040c407229114007400c05002d00c0607560a4003403114215100e162501d80e03c400300c9000c803801c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 82556458 1250 82555208 82555223
    0xa0e011707080a0b0f0c0403060c2706020601030807030512010306240b030f1b0a02100b0306010602061f05060d0902151309020f0705030301120c080619020901032403 73
    0x1080440e000541101416040003050390507441743c84804a030281c000e00580d02c003e00410020011807050f00030303007414001d980e982d04803c018082c003030f0442d1502000c00c001c1d4074100e5501042042d5000070490b0640e900608450b0360386649180664140c4a0100094001605000000700f440400e901c0380c00905506c000b092180000003c0c05607000c000c500403240c404109001241c50808420031143d845007165821203901001c54201d100a5004403d4800c01a402410310100d038a02ca03010722148114141d00600055042c41000303515414020040c4401c40b892101c1d203100c410442d90050020103026100c030355a90300382c011203000707441c03900c2080c1c0c001c081d07441022180b480045c08949080d2402200340311240c1c280400740000c0d5001c1002662642000d1140703601141051000f0b500811103244c10107614042c07440d003805000446d80c4a05101d41080c01040b1001e406803100f940e040300300140c01a600c0e0018001070f0010180640326100300c1c5c588400040001c41144000002d0f24041c414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 82557708 1250 82556458 82556473
    0x62d03100501171c0c082b150e151003090c060801060314010612090804090f050906090d1b0807150507031104050307050103200c101a0307140a0e0117 66
    0x20b040ba00400d10b01c42100000d40c2c5c0e14203860101e65800080e0003c06400614025050a0715004502c1905200e03800d850781e03580d03883d16001681000203414014070318085c4111080c034003c002070b0b0900310003004044c05070071000007045c1c1e018480c1d401141c409030700401074035419480d103e0017041c0e01801d000c5d020120f45041803900b0058070000036603048425543c1e80c940e2110399031580310702904a09004035081c00c3d041c440440c000810f4028880c03440c00807880000c2070302d4920181403401c40c01078242d1440360411058005150b62096a10000003210301180c50150010315003c5483d208103200030380344041001c0c02c1800210640c101d07034060401c07a0385c28006034804583c440c142d4400c9100303840d070640c1300c200c08001c1035009030084103030f504003641316001030300c0525000b0b032055120071b10102280d00300c40c48502d46a81184981022004241c0701c00038003805040109030303620002d015030b401841c281c00f200400c9940d54070a8030080d24820061101d1075030364644403002101e4800700c040c4103009800303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 82558958 1250 82557708 82557733
    0xb01080d0f0c0f020103110903060103050a120c03050301030204022b0e061509041101030b0d0b06100503040b04020111010b12150604020309100903050f0c0d08062d0310050117 77
    0xb682035880c64011100001c01011076006500411020b00c208201c040c0620160145a03014050a8025405100541001301ca03515000610002242d65071044c80245040f05010035030040580b410741c0d03415140180d8031000e018000140300840c4601c170030b030500d039150380741c03c5c102203500700c4141c1c001ca8004440190716103401c441441c8014030b03481034000340c6810018010540300c1c0c001104200040c100080d66031864004240d1000410100390364001c00641400143d0408400800c1ca4030814501740f415410144c2d103640000c0c2e4040c0001e81005881038807420054020740c40042080f0004003440e01625100a9454441c118140424082004c03a0001041420b1030300071a031041402c0740141c6040d520588488000349403042c42601005401e12840300c01c900d000740200420340425008220b8030b0441da00003031500c90300030701701e40c016040101c0350701c08200411100001c8640c03c50220703100300d114038003003880c203c2d181101c4403500703003040000102c0011445d000e40681c4a010305903400e00c98581c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 82560208 1250 82558958 82558967
    0x15110c010501090b0f0613080303041a0a0519090203070b03180114040c05120c0a090204051f020303150414010b1e090109210506010b0a1b080d090c030b01080d0f 71
    0x507110f2a0042c030302c03c50f04181707450020b00404201c82e0b08504200040c0c4c48482d103525680049504650703040740714800c6074044019400199000504070010701503440d000100402900041d00700038111502ea065000131540d09100c01ca01601040740134548070300d05082c4031100c0900044504020303501c0e185100c0000402041d400d407185400060955000f8a0300c1c0a00480c40a56441c2e07a180d0701450050702803d60750b0503841d600800c17280c10050303140da0401007007091454620b2400009210203032004091540c0100640350320036840c4502d0100a083c02000c6005889108900c00a40206000100e581d86410004c2d00030b80081d2584014140c1c40c443c00c0e500188a14124103001c00d5404404210058001d80400702c6d1080647d00100d40400598a0a1802c0000e0300712524165000c625643c40035440105007030400140e0303e01a6090310b840d111541184100c1d01a140321a45643c01c0d102400b1083d000100107560001e04a0800d40e03403814802c2e1034080c0001101c00080700c000d1001c02c510b200707 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 82561458 1250 82560208 82560221
    0x4030e0a0803030c09091003060504030c0b06030303040c0b090301020d0204030b01030c0e040506060607020d0503030708181b0402181201060f05090f070c05070f0305060604110c031615110c01050109 87
    0xa50699924082080b806c0050710440103000d034a602591582c044000f0380c0d103000d001e010f648251220903107a8414078114800306c40c01040603000364818010800400c9045903000121548100c180c0e903104007603000710340640310b50b1101450440c0001400020094101c02e454100d078041e41400314066240c00d28420390303040030755020301190b00020204095180220003090440c0c03004100c81c21301c640c29035401e0b045400071502d000220f5040d030104445900111400503c901033350300900000111344880ba00208680c1d80b18900650740454007002110041404002100740208800450b06940d022280a01000d0080c890340314542c550000c0c4506100a401d8000c664000140e80c0039a100007003101d58101d00002516203110f580300026940710000744110185001e6809800a45401c4081c042a607102810b030040c07180301006602c2c02c0326404000c2c0d600c041c00c03801c80104030280768140b20041007818a04c2c50501442e20b4905000d60190500901c22140360300004e105903a607035042802110036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 82562708 1250 82561458 82561471
    0x503010204060215130b09160e130609050f010e06010906050406120305070f0b09010207050609070302240c011407030b01020c061e040b0301151e0c2904030e0a080303 73
    0x68113125203c0c074200e055020300200000b030644540d0b0346a00d040b0503010384103480a40c10034101d45000203414814034016000b1409640b2803404c01d01c1800e007120482200140c40541d481c420001003207400d100582021055000901500d00c001d001329403580b03020b104041c0308a1401000092a0415000d0801100d140316201f08509000b82c0f0243e449500644007251a11500f032901c00004095504441c0115911800146c81c0c1e0501c0c50305510709400a0203400300c690100c6420001661040000103109a40c00200e4040420b14200000c4500403d60084065420328034012144640384445a00ca80c06a5400b44250a01c900040e6100c0d1042040c10742c002c0b1003041844203807030039540c041101034400049a450103503a1148450325410030b0b0800740e803a4210403202c0d542c10382e000d00903807001c01d2010105440c0139807102020b0810410303030a0080c85c182031403082c1c91184900d48030042501011810030242843c003880c0c001c0440b01c40c07021842c070400701940c003c115000c001060700c2c03103080c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 82563958 1250 82562708 82562713
    0xa0b0909060c0a05091903030306050307050a030c0501052b0b01260604021e130504060b0c070e04020d02040e06070305090f030301050607061e0504050c090c180109080712050705030102040602 84
    0x305550f000c44107940414405600b1840c81c0800d019030601d000c070064001c602035980006c605080404060a00d802c5a01c824421480d0080134000b00d40720aa108040b90800d0030850368980540c1031544094211041030440b080125005502c400c030720b90080a4102c0d400d984508550303011400081e000002c01d2050011100e2400c00038556060690040042c0ba8281450203c002c0e41014941032a84c4a42d091441900d0340c40c000300f01c5410107001e0318000d01364401c040741c10140d8500c03d941d980c03100c0d0b00c180424003845101181c00d40d22030010840c2c002d50080c100340020390f81843c1543c0d0380c2c541a03d880c1d000a2501d0000340c000c0d4000f0400464002032000a1880c5034a40380c05c100c1e0503013102c04140c42c442d9540d981c2640c82007131440c0c83e0301400f005008c081920b01e040d0500034209590700304030741d008a0203881000308072801c40742210803908007a00214a08031038500101c40f10030154000e00007900c10183c0106030b040d0108040e0462501ca0300485046e191200c0c1810b090340110311800f800b5a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 82565208 1250 82563958 82563967
    0x9031707200f100e070611030f03040204061a07030f090807051210140412050a09030201050c0a080c0a061802011e140a031a04200c0304030203060a0b0909060c 70
    0x4420080c04201c0e40c44008070b40d141d02c05100c0c120b041c0640310b0401e860040d980d08090b1081003040c40002c000b02040c0c00c20000162a5484464a0b441002881400e0250010001d021955076a000308040c0403004d41c040001d0071181c8052041c0c1d4841c0c0001d901203500c2400c0140c1e1548140b058100340c0f121750303000e0902a40303883c1c18400c9a81034400003010301e000c0ca9139034990070042481180390700803508041400b03d0609003080c0c050020720031007040130480100072400015800034901d40817268280790407513460306011100350400104110051034007000044048084100003074000c4028020344003004401c51081941e074500724a508006c1c0400c00b135072083d05002007841e1070104800c02e10b081c200c03000003070b03064074440300e501c88200c14011030303600c600201e80b07025520501d07101141c1c15601000803480645003c2d42d006d41c101c64084984c5d1000501e2500344d0028401d0343c1c01542c1c0a01210f0030b6003410b10001010f003403c114008d0140700c8070f100044c3d03000c00000d9103038017402e803182000307180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 82566458 1250 82565208 82565237
    0x703080a0f08060d0819050c01050702011b0507050606010804051507080a060e09060703050402010203040812040905090d02060a0b0f04020f0414032e0e0303041a0105030106030809040e1203010909031707 89
    0x803801000c2c1c4806c00d000c0300303200000104c0820f02507a44109202e900004015284010610a0310000490901081410b000030000034030009842038000009081c44843c03503446180007490300800940b0340c0e5440403014103100d034490b040486c01e800f5004584003481900d0b1162045410038108580e0785107294049004940081e020798040d0790071078018416240741c2500d804030360746003081c41402c000e61140d00013010048641d00e48185a00715400d04007034450280c41000003540e981c03026040c0c4950994a4120444c0c0d5950311200e407200100250080d510b89084c00321521450b0082c5c40390302070098200074026260b240120301440da0402040c1d0856095082004100301c40401a02254009a8501694030040c10400107103100b6072040e900810303c0d5502e801a0340000c0810780c401c50107603050080a1000490b941c0a41c1c0c0c1d90b000a41d00000c06c3c3c002041c42c80e1412010503074101c00f039140003001050210854000e00d141714000e440305500003070701e9606041556011180500000d09032103a5818 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 82567708 1250 82566458 82566487
    0x50307020f1906020303070807050a0e0910090c02010203090d0203090102030d1509090503090f0a060215090c0d030203070b01051c020402090406090f020a1d03030406110703080a0f08060d08 83
    0x4414038040d01200030002040b40e4044210099003020026030300110402030ba02da80445510341c0040d10b4603066040201010700074101032443c2e10070707920a40c40c0200091100031806801002022058414010123038020400fa000758005e5800c14035a00a404421420500010448107861412303070045285c074442220f601c0c01400c800e05c0e800400c44400400003502e10342030044541d090f0091001d542e841340c100041102060004075214026000c4140400c403464000c5040180700300c028824041568600000a0411a08400d150740c44036848950006042d4000050304000d0301ca140d2921a03640c07540c080016a010185a20314131a000c1c0426500608007a009003c41c401c002c1d10205140b519006032406072688254100502680072880040c4182c1c0000c040c1d50510780300002c0d4030075070700c80d1300403d1b140e00c128050481402610041d9001510040152000843e00903842686804d1211401030a0089540d8440002844800401c00514210703d491805a6018843e07074940340b0250712018 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 82568958 1250 82567708 82567729
    0xf0c2f060f040c031506090f0501080d0f0318050a0201091409040f03020f01060605090a0905150d140d05030a0b120a0201030509011401090f110a0801030303050c0910090e0604020705030702 83
    0x30f5101555601c0007000455108001c0c000b00400a40032440c1c83c14070308800201e80d124072400c21080d08020041022400120740400000e03443d19050480300d1407842d007580034000d2203d61807900c00004403034400348200412407800c00742c401d136240400c2d1075031209100324090702c203a00740764032801c01000b182c0096207040303550661511900503034400f08518100d80342122103580c454008500b0000d165401c80c540040340c1406098101d20411a500b0403152601030007035440c0d4030b1809401b19a54540900c60200004010604000c2c1101d1032241c142ca07006156400580b05400d41d94100075902d41c80385445851052400722910040021180c40e4004401030311000e4111841035503984001c3c0a807241040c0031078003030415605c1c04290390070a078041b6422280140c1007180404414090101001d42c09003403241101d415150206064a80fa010000c1c188600e0305080c0c2d11030740300b008906500350081c020305d0483c1c403504600c40b5503940308410300090b8480c4100080580d0810003c6000610f01402e10030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 82570208 1250 82568958 82568963
    0x1030b060d240902010306060311070209040204090203061311090103120f05040f0605130803040b070f060204091a0f030d020307060e01060503011416050414040c030f0c2f060f04 78
    0x10169030800100404021180d08884801070300c820f0000150b5800d1b006100080c00d41340380420198a125250b030f885805510b2000307103c0c0c1d0000000c0750640d507032500281c003d1500103054441c41c0c2880308510103160316100040300d40380385c000280d481601d4043c007014102c076044041b4145003036140720b00329883e92403410564288401031202151b200b030064482c201802d1941c0702c0340e40c0c0c2d214120440ba1694060b91003480e155000b00400e002115a9200341d80c44c60ba0310240c02c96203900c0301e19101c4041d0003a600804d452503d003100b202c02264284801d19442501517582d2424000700f02c05041d00d4091580b404000350340204810b10014101d68804a01d002c450000000e20b951114006400d58801c11601041040b44100f0b00c0301c0c800880344070300b10b42455804c00a00d494584100b6807950f41d2041111031180f070b55042d03800c9405000340c0040c41406201d40e03003008906801e0401510100305030702c03040000d58001c07205001140684812241c0c121101004001b40d6803141002d0340c20b8600103008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 82571458 1250 82570208 82570223
    0x209090a091b14180705070221060a09120306050108130507050a08010507080a0b180c0715050106020d0804050a140f0105091005071704020103110708030a061d01030b060d 75
    0x1003260301038030300200602500d200d2200f2007503800841c08002111000041d110411200441031042c1d0a4201c411910f01507415210b810070a04c80081c81028815210a850203600910080207902806a0b120542c0c0c2e5110b0360315184c1080e150300d0101d0072146c660140d2400300d50070307001182890800907848000d4a1141007101c0c10291100085241c0c200540c1c08030486a4481003441001034100020341c0e4031030b01c400020000b500f041000154004900c0100852460401003c03420310b001c0da00464401075040421041280a1901004010a400d02c6201d005004000200030124403819069000755080301c010080104281c940d10010100700e01d210303c0c0c910910318042e0b2509428010a0702c10041500900040405422800e0075582c0040c201c408119240c084a00e018864500c0e15070800c0d020b190008020140c400e4030401e42c41000c0002d8100b94012003000031622241e041917041e580383c203070301680350a0b002e60140c800580c2070000504c0c484a460000b07010b070500d40741c803000d024056001e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 82572708 1250 82571458 82571483
    0x20709150b0c06090601050d050309040c05160f02030c010203091516050d09060e100f110c040207080c0d0c050d030b0102030d05010905040b0c1c11130e04150209090a09 74
    0x8118541c0d0380800742403074554210100f0044120000e10401d401480150b0f50b000d2003060f43d41c1c0e09500c80c0300d240000c0303201d9503403140550349052082c0309480f02d88502c0c110342c85540059042c009020588800d00300e01c41c3c80b441801c0303207840d44017000b03071007904c500507040043d072000c4490803113059003092a503889000610504000403a9042205250400840c2c4400741d0481c03c0020040001010400c0b0901401404921008a90340304400e807841e181c0780e1420702c90000900d18401e040030303c1c4a50307490740607002003540e00500c020030b40181b400c058804110f640d01c510029084c2c56200807000041c2c050740003008548007250203034014079005001441903926200283d0b03042c030100c45003070304a00341d040e549004000401011040082d040403001560600b007020000e00112a0742d414030103111800d880d0481d211040e1030070810344110102032044001d5264441c8808000030030110b805403a0341040041d2440c010b04680708507042100c019019074556519144407901070f1421716411208100401d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 82573958 1250 82572708 82572719
    0x150e0f10110114040b04020d020109030b16110706020703020d080f030a0b120616110a0206211014010804030c0203120301090b0303030121020d06020c100f020a02070915 74
    0x4448036a8031516100e00008030042403006084840b50101019480c0c140001d00020800040709194460703070495400c0542c14403480102c0d14601c05500c024400720710b24081c4500c2c01900d07011301d12140520769030162800c052001c5241d550b030030784c4184805a000350b9000d0015062000852001074054071546144c048044600285507104550785c1c0d003466503e42580071185071080000c07040740045801044030b824084991122441c40d15034807402e00041c491504600a0306000e00001540c00030300a81e15120300c000c06418440c42e202c540540c41301910700040702040c0c001c1d00389040c1c0f102c44908034900042d02005544955010703100b07809001e408800100107a5003005040422122940580d0b202c0d4904030030001690b410f692064800d42041c4010702021034403028072203a07211560340503103140f034850011034214045020301a00c0c0500000301c40d0200b410000b00003d4041101004002c03080d500b20211080b402540b01d00380068014200800500c0304030b4001004480b0f0110702d9800c0070307a0780c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 82575208 1250 82573958 82573969
    0x12050c061302010e061206062a01051006090609060f05070609060606020c060408150c090604060f0f050414150c0307110f040905060c0310030f051507030204150e0f 72
    0x80341e002550072801c001c54021540d100024080101c0240e500c64108844d8032050803803090010a450701800d40890103e07001a0761140b68220580c0282e000a1840c0c3d0580080f4041c00088075160b2a40401d40740000d4400d01c0345103054102c40711959034450301410200221104c046500340c11042001c1402034001281d0039104051740f05205040c00034105d8941540030b8101246440c080c1c3c4034603028442045010030100700350904c007400b1401e00c180b940c0c0e40382d1101d815009000055401810104020508a403c030348a03c12040c0b0a8840d10760102c91000308841d18442e500607039252020700e11680b80242030490410fa035013512031075001d0800c2140c0c030401d0304d1500042c0081d11051017001000700c4504018026403c1010b0a49042c850405203851b850759880d03000d020005400300c004000f440d40300c02e0160b640069a401042880092442d0030f055564584c1ea90740d0130107404a800110710190b00a01c212800c99520450400007a98550b805a6202000003101d90700402c3c10452501c1c2640c90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 82576458 1250 82575208 82575211
    0x20109170307110603010f090b03010f110a12020304021f1103030a0c080c120103030503070c0507030b04021e030d0f031b030207051207021305061908010c0201140103020a0312050c06 80
    0x49000950710b4801e6400c0508041c0000b882480c0030b2007041005200325801e908041c1c1c00c1e0340450901107404c65508000c240100880d80012441a00d40b60143d50044c0d405401001d00344019951074014258102c01001244000d40d0020347c0200c17441078054010355141d030700b18500310f181d0512180d071b40d0f00e04050500f558411182034280680c0d94400700101b542040c805a000107980b04202e040506c08684031030050010301010381885804400900c41c90711910a031500e00d50311406580b941940d0b4a0407a41083d4180d400720b10034050494203000389861898a9075000340000c004000300180940152800440765494100709500c44440804c01095480400100112650016500d4107241009400c1c0106c2c626444a2507000b00710f06d1006d681c42c400c1d101800002030704001016181c3e4400120b54041882580f030b028942010005582d8a044d40150407411141d0000c1c01040d0f911103400c10b903c2001d0100950000d400c2038144041000314850071207508403801d0041c500744c41486503d140610 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 82577708 1250 82576458 82576499
    0x2070609110312030408030103170d0c02030301051503040f02011b14150705030411100e04090f14070513020310050a141503060907030905190606030c05010e0913020109 74
    0x11039081c00000350070100943c0c1094110010b00b02d04605166030745999512061001038003010059000881640141d42160040001c044042103906407070350b00a500c0340c00c00d01c50a84910720714984140403407501012607200781c0e840707220030042360410381c01500c03000801c0c4d0782c080c94600780009881c0004c00d0200c41d02e00046001c00103201c0030b503110382413599983d4001d10b45002c010040c018000001d8400e19950352500003200d401c038900e5042802110362005006003140e1281c24003101c02d06014400c0442e019050082c500040390bc1910543c99941d461184909070308803603c442450300195070b5070701071078018a9440342d61500e1a614000220503200740d800056004401c0c04401c1c40515180031200c0c0b0800c1521095421454080e000070084107005014000307040e02c0f512484100407060055880070000345e040d080c141042403c1641c000c00e07180c002114480b501b40030100c2d02d98000c040711540c030030f002003c3d07400340e60754502c0c004d070081c10100040341840b1908034003264040d07072075204102201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 82578958 1250 82577708 82577723
    0x160905060d11361008130f080a050a0815010507030c0f0c0602030a02010c02010921180b09040b04060f0303050c0c06030a021c0902090109020a120e01060609060e0105120a02070609 79
    0x301007040704802c84000e4260b01344201d1a04549050782a002500c1a034050644003240780c080f601da0401c4500c098100170001c200b0140020308000d1650060003030544920281d446503c182d440c05a0001e49800c0564401d0102d00d0a02030140020b00c9601411101e9214103c0580404a140d0f2100600700070b541083d800743c0c2011401c01c00a45d8244502c0c0c2c8003042510007400345880700c0d110303031000c1c050a1a0719058100451600b03000c590084030306100e40c41c00c03400c4036a00550303241402e04c03036a00220300c05c510986c1443c0508510303207818041c000696050346c07a08808070749155001e4401e0b038003481c620380d00d81c0151100540955900800346200d241080c2001d0b9451a61589031700c00c0d1400c51001c2c8080310b00c2d01c0b4000e80903031034440c240d41c155400e00708010703600c4409a0066906040c0781d15021800c0b8207101c00c036070302c1c4101034110030101d403819103c200600c2c0d12014103458000a51500c0c50014509000b07443c4600030340549581c2050034281e00610781500740c4c80d15004d1b156518015950003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 82580208 1250 82578958 82579027
    0x80301060f08100504020a020f101a0402030408030f060d05010203090a0c090509070605090f0a030f0210050309030a360503071205030f0309010b0901030b160905060d11 74
    0x41e041240d4850480d80c40c40c1840c418a4503ca1100d083c4400b40a45401281c1c0880c024a4490080240d030000e1005042101d070034074030219001014200c0f40e4800c1245804400e8800111f090034000c1d24042c3d680501c00301e081d980c550305d044088001c0286120b9110314060902d00109000384000c1d0702a140c410083c03d1a4a003034204650104c21950200580c24030702810840001c00110704041034600600c1c01c5980c5940220014a04c1803410360340a0740195101c0000041140d00916004643c0c03007503680560341480000d090707945010403100c0d80f1711030300200b20a52030741d845104d000b1200803600d850400c0c820602090910f40c0305032000403207070a000c51802401245403c10941000b84410310440809440541c1c6480e200e002e15403101e03141590200120740550000e41084d2107545000d0448020340d81e5904200401c1c02e070503120010142d10b91100321404034412070841042d544007a00c85481c0c1a5600165401031000e0f801000e8031134407e011030300841d1090740a03043c8400705810040c256 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 82581458 1250 82580208 82580219
    0xa05030906061e09101e03120f0f050f0d02030108010e0106080606010c080c070302060a050d0e010501120219090f061404051e10031a07080603070b0d0b01090b07080301 74
    0x40481c0a4002c074440c8402d4844403105140000307158000043c25264142c80d03440702a041c1c044c400e400e80010a22800c0443d880580c1290b40c40104112030250171003140c1c1c400056000d03030340800300410345000220594502c00c8118040c2c0010850341c000345150515142e2224044c0080740c00c00e80281c0d6040c2d4440b0f002440301c890034042e00d400b4098101c0584000e00303041c030003e40301000043c0010451000030030107402d041c80a010300320007160080e002a45d00c00c1000c00050455026203481c1c00a03615040c0703d4021444140714a42c1070702c60303040300c440d15492190200701e140303034003040890601c4034191400f04401c2918010001d0310091100c01060345420540045c24020030024114010b92410003040350080d40c1c0c4400b415261180a0514001c0e21400890483c50700f071600054050204242c40c443d10300b01c41d4210500c10002c96484c07032223a4954508168071205544681c6d05c25480032f100099590107182c0c483c0090708414140403410a603209001d0030143c01c040e0b019a803100e40070004210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 82582708 1250 82581458 82581463
    0x108060f010819020301060b030c07020a0f0303090509060321040614090f15070507030305070204050a09050604020910051801030605070206011224020705010c02010605180412050f0a050309 83
    0x400c219030303a500e80d03015810400c00c40e6a80c0f2405603104400360907146144190b44007984050050300c1c143c20038590740c1c5400d96040074298005407089004170300001c000a00c80d02896880829240e00d40d0319451000d1421003006011000681415418014080003510342c91030741c001d00400c1030764035200a441d00e00d400b00250210b245080621080203003040b406030503548006404911100440f070345007003201c2c1c00c401520140030310171008015126004000c003e15402102401c01c0074800c540c00d001c10b50394903022105031010084010415032000020400502d0101c1a00d584001e001c6011205207a50b03e000401050f070412225545002e03500040c014801c0c54024954444c2607400100519407402c048001d6041d044003010f4180d0700001100c10a051129424402c8400c40e50720664030780069080190080503079030360307000141d8680741c40020a4184444264100300f8540070100155640303840d0f0002000d0a244c901c1c0c1001400c00c818400c1d6080880982110341490f50b0f4142c880c60040f12651 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 82583958 1250 82582708 82582711
    0x3021615050c0406140f04030503040b030a06050a0503060703090809130203040b070e060301061d150904050702010501052101020d020c100605031501060302090102011b11011404080922060e010806 86
    0x70000c01d401c110604c24240c0000c02804c401101402d079a13034441511003d2141c2d40115000140076001c000f80c0050000500f40c041d5014002201c0c0400842d6550381c1080340c43d80042c031880c0d4068200a0020b80300600a80c0b11506050150088a00d850313102c0c00042c0c019800b03181101a8182e002c81400207114400c0c83c061b0384140c00303052801c0301300e01450008603140030502c964001c102c5000c1030004550341b0400e00d140000005060744191403500c2884056641040005c2401103203450001900039205004050407120085c0028030600340b18401218050a00d03402d0301010b44d0200300c0d0010200c098801096075001440142c000c40f4100803d0707070300362629544068800e600604c9260306a0004440660442d24141001650380400b000140e004d00845080b036038217512182808210190032080c4551411343c450001c009042400050084109094038080d08541c41400707200c620b400d03c250440d241c000300010014541c0d2801d00b034403050302c007180c2001040122950041080e03034420800306 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 82585208 1250 82583958 82583971
    0x63c080c0f0301031e0506070f2c12121201050a06050c03090f012d0306060c0f020907021501080a021003090201080402150706060305010c0f050403031e0302161505 72
    0x15103850780608001034180010f000180c110943c95181040c85001031800d50324907980601a42c00b00d141001000d880c088100c50060041001414800190740300c00c1949068001304c607000440351b2400d0414030042500a0365a40184d2003821f05900c40e00c1c1c07649012345885054441014078541c1000c0601c40704d800382d6030000c000e0003018446802406d4000c01543d00018096401e5040c260140b8012a0000040c041144c503901c0c0c00400003c0c01d12020200c0151602c2580f01840050340d1940111000d410000c3c8c0506110b05039040200186845503070039801c0300d0580704a95540062a0101c007410000380d000403200da0210070a0411801c1081306941c0101c1103003002c0103500025000a8001c9500901c000e00c070b03035001e22000c03882040d50350507170741240d410040c1000025100c0c07619074020304e0220303a20740100703440d88000c1140314451400c0790140c99260f580d03151410031206100d10407021a40c695800d250f000c1c0001240c00207410103484001d402001499168110041d90100325080600311 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 82586458 1250 82585208 82585231
    0x11180301110c0d080a18060c08100605091203041e030201020c010e090609040302030c0f010906051b0a0809010b10030902010807030510060804050307120801030506060d0c063c08 78
    0x205031081003c00c08100c2d00c54581442076070795444054034801003110115035a010034900c2450824001c4640c480c6130210700c2c03901e40a0840d1140c02c3d01c040c1c00ca00c1c0c2e2060000280d41001880c105003028000c4d10301c213800020480e4103058580b44104da00f070020b032901210a1030040c0040043d5a81007242003402c00d82820505811035101c00400c942c0080140900c0c0614000c1c2e0101c1d0805200300b080350401300c8020281c404541100c13440c903001e098509419030340542080040348102c04006031080703151208a83e00c030b182c01c1080c40c0980d40e401e4020308440003950382e003400010580320020a41e0700100d155500180b80f00c805e20001d05410340141a0a040519010411405880c0303480040241c48a500b0144c3e102d945903d812490751245200003408616036144a8200d540c11a1245058900c20410703a5429a0b0b0705040c4a203941c80d10f440501340c00c00d45a810080b4078001c00da0721a0702d0038104402c1044d1005210341b4100700a4015a0310f079010155040011034a5000d8480750f00300301c1d010074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 82587708 1250 82586458 82586467
    0x10020d02010f140a0c110111040806010506120f04060e1005010303030e0d05041206020d0216031101020c3304050606150f0904020a05070b070504060f020606010206191118030111 78
    0x1101e1000100113211400081e5159104291980190480c040d42c044a20007440900500003945980760024810b8195a100e840c0002c1260702d0060295000c1803441c2904110310354442c1000d0b01d0043e0003070b1040d607040d6aa291084400d850620503150506c01655000c141c5503d9890002c0858180002d0840d20b9080010310034a5113900508032801c4410050f00140102c5050500800a10841d607858145600c0014154548014000389221017070107511941003401c3c0800444d4240e00c10300709206902c0d00080c96110350090300c0344e5200c444208581d038006080c42400911200c1d00c0090342c1c140c41c1584400304110341407510800300b03110065001e4031a403d189003180c00080e1030099200141c441ea4020504500051150050f00d914a40100d1080a5403c089001038074960043c0070f40c4002842c00b070305c00403c0c10700000d50b81d4020388041e4020000c6941d5446d1115440700c2e41d1513410314a507156922480c5080340f05028040c0c0c0320500c181c0f5408042140200744c2180c0c01c00c41d483d14030348010f00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 82588958 1250 82587708 82587731
    0x415031d060906240405010f171f021308010e16120f0b130507060815060705060a05041104060303020106050a06180b0306010c0b070507020f0906031002090f10020d02010f 75
    0x150941e044880c0d4041e007089005a203401c100e965403c0000d1303c0e0000e103020000a010400c0240120407a900802d07199150f10450107101d40b191b5001820f000452014000c0710710f0311029034010160b00c0c9108009142c00350b110b0081500b940c406085d0390b40d0a0f84050004141c020a180e440c500801c0089003484c4251b025540784801085504405443e401c6000c4c0061264180308118400899000c03054528464864601402c2c440041e0380d9101b14040014040185060440803101000c1e0090000c1c00142e031031000c1c04020340801481103440780c0310380c03804405036100ca009201c081d61113500085815418035050050003a025484101001300403012680741c0010000c1d0070050b680c00340041c41d520794030100141c408400701d0704000e00030351704c0100700156160700c000901007140c82241d9410920604008100560105648043d45a0041c3c90000d08865450b401481807100280a0300b480c40c3c00000083c54240600c4d8545025030044c0c070105032966828811544052003610080100d201d000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 82590208 1250 82588958 82588963
    0x6030204060c080d0e1c14270a030804090b040e0a0f1b0e07080906130c2709050a05060a020712111c09090b04061406030c0415031d0609 60
    0x141c000c2d0140c03d00041c80ca20310015038010700001e00c0c070042141c80d4009041004c600464500c2c81010014040c1e80e1101458003c420845440352074420326020520180f469a40c640040f0030030041d8000d5a64000000094002e00030f4402054400300c0001c004055000380b00541e000702c0c0e41201143c10a500100001c1c440e04140821590010b500c2d520304280700d01103880102da560060400300c9240b80401447c542e0041e100751003456034800b520300e5a100c0d0798011104001100e4001c02c612810b0368140690702d490240122000a0803001420031420340c203808040fa8800c081c00e0310660094804581400340c10850560001c5240c0c00442c900b181c00c0c0c860000c10b0707440701c031003008220f400d169800018908014500c00c01803003001440c01d41c0030b0940064880c020078828407200b60708151101040b4640352103420129070416130224664614003040042070751000744007504a40781440b0114a10004d1001041c03140088e0f200000c401041003040e1840c1c12044100b04400c1e40000d04000c1000c001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 82591458 1250 82590208 82590227
    0x20d080a050f030c03011a070203100e0102070219050102010617060a0209010314090a0b160503130203010e10050403080a050601021509010222090c0305240607060204031b0603020406 80
    0x408842034480164000c00c440382e101d141d4804a0001c0044280001e605031500114101c0303849800c0500405c0305003481e10614024214060750541100521800310b45050700500e10000c80708000514050032580060301e02c850075a80d501d80801344441c1403003107503024881d0038040e0122a1080e00d6401a48110341c3c2d6034500100103a40072900031451043c81d902a400080c5050010011002c15261803071242c1e03911040928256a403d941c1c00c045128a441d910f00050034040d1a030340c2e585542c3d6400030014070314020360743c01c0b41c144d981e40c0307035080c0440740c01e00004581d4080caa8000c0f445003003906000301441e03005400402460300d41420302455130f800080d405020510007418918070764840103010300a000c0e6034880c040e5a0000c5010705450b600d04650360701628140c610030030040f01d40310340c1242120411900d09444a011101c6501d590190741054401072500504440c83c11150303580766016078005900807220741840008001d0752043c001022030142c0b80a00c0d0071800e0620300b440c01821002ca = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 82592708 1250 82591458 82591463
    0x15070b090f100e07060932040515041109010507020409020604030b0403050d0605040b0603010e06281806061704081909090b0405190b0604050d03170f01030201020717010b0d050d030c020604020d 85
    0x1f0b800d5803810004007001da41410414020f0081009192174012402c12030340d80d01106104602d400d102ca020030050b80140d9030380e810180d44850402030583c0c24071005014280090b0b911043c140400000a6400a1014402c9119030749694440d500880048261000c1e504031911175400d180d60750000c0c0d15882c3c260307411030311164055021f9450360400314968900c40754000c005005130f008518603100601002c141104c10807407180580c01c1016240408442a41c0101c038001440703c1b01c3e403d04442800145034000d230050058a10340301040c2241d10140c1c080070320300c101140540c074082080c8400c6104902c6000002d0f0707010b0015180c80d1000d03099043c3d105401d080a00e0350303000c8841341603c41900390740240030b0103000c40f411103e0b94200541844c8100301aa4a000b0342d810010303221034001a110342c122a13043e0010850903080801000c214482d24541414942d41e41070352403150342e01d8400100e125402640585260209408010181ca20b480210b006660040c1c082c08010307143c400314102800d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 82593958 1250 82592708 82592759
    0x3030a080a020c010c050a021b060a0302030714040306270b06060313051603020a0503030408070501051b060403110607050a0206040809010e09010b03010e0615070b090f100e070609 79
    0x740c1d0000d00c80300034001c10759030036125860a4041a005030704403006002c0040300d6002c4902c0800c20035818402d00c0d089854247e000a418032020310a01d010703801440d0000c1c194206804901d103650100006600942e2060703c0c0c80d9181d5182012801c4882465407600f460b8508404000e03039646c4922400e08005803102d40030b00c40c0000041d105030510304090300702d01da1200540305040b00c40f9004220104082c04241d224540310100005c09107030001c102d0f002c8032000c902401d52a1f14000055a0f10381000c04400b03074010007844000c00581c401d10402e84074030b200c0d4440031a120b030241200703890007000070941c0f01031100070081d04e034986400203400c9500540c8254103581c1c0386902c0004841043d4400e42035600160782400200b0f14030b11300d10147d8144d440107070b15400240d03101000c01c00b51903c0b107a411841d004007000140b02245207010015400040d40003160008003a200100e032401a55207400103103507594052044a03500e062080300c0061019181c07519913141413005140c0c00c070103074002c1d645046 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 82595208 1250 82593958 82593961
    0x30313031407051005150a1401030f0609020703020c0907140309070308040f1a0703080406020c070e130201030e070509011203020c1306150c0803060d05010b09040501240503030a08 79
    0x161041c07518402805000141d65103540702850100ea40e5031418404106540c14200000d01c1445240d040022001d00104034040e0780e032820003c401c1411940113014105a12003558013280c0c0a07031f0141600900001034016650426420001e08003c620840a0303c1404100140f002959100004d01146c045480a05903640c89070031082d454000f0a5100401404010600003421261810b0040480780d200040c0d103156084c49032b0309003207440b40c0b0750000c0218240d040410b002c03a4440c0e01801255049604403101551174810400c41d610b805c40707082004003e0040324a0031540e00d80502230100700002c000f842d800d41850700042500c181409030340c4481c184040302c030042c10301c2045500c03c00701000d0810400101c00301b11420281009000b1071460b643c1e403040d030000091240c030110115940008545003075441c1c5104018000b05501400c5d2a190b407180b02c0e914459032a20001c9000c1c500c42c000014030314080d40300540c0e015005000c0c0c030324410310001040046032004011240169814074040089 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 82596458 1250 82595208 82595213
    0x50a1a040c05070516060f090f09020306030f0a110f030106030209060409050a1a01030308070513171002040f03050f1911010306210519020310020a090e0c0a08070302090102030313 79
    0x140d0040d90009002c85c0b180c1c10b0840305140d0b04450081c162022642c3d4004590703807003001038518603054410020780d8a8403050801035081c282d4040c58005c4030040980d0b034484081e0256500c1c0c0724042d0740985502020045408561509500404a40074140c00912065155400048900d000149020b0155445003160303401c0040a0245d5000d2640c044881907400c0070090201c40e0900d002d001c00c8000c00c070040007041005010301c00b5504600c10600421042c2c07400c0a204030000060560640e071544103c3c041c0182c00000e070700280001d40481401135000a03c0c50500034585407544c50780304200e030000d0f102080303900030600d9a10310568012444d84407070101040100c00034136107a880748038881c210001c1d203582c640320440e46c00d80381d501030340480e01b6802140b01504a00060780c01d00941c154090749120700f448040b50090000340845050441c1c030b2130340e1004001c41c402001c641200300844005100752005800030000f42e0001e02e10325085080c03001c9a0000f07581c138071014140c00e802c8405000450b04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 82597708 1250 82596458 82596467
    0xa0b100e040501050f10030506060f040204080706051c05190506060909090607020f01050601050904110f04030309060f08040c1205010e030c0d1d030a030f0e041a04050a1a040c 77
    0x520400395224094074040c00c1042c020f010980d82800d541e44a003001c031b00149103010503072040d00c0e0014040d143e02d4a0380d00800000c03008154106030070907028400000d000d0381c240100801400c558840b10758a00030850002c00407050f50741101c0e03619240c0070034062040d00c9506040c400c802c200d03000040c0b685558001507180c0c001c82c106540d1004040b401c0040058010a0243c000d030883e4080311788814146111500b07a900403510980064024010610b2900c1d0a4119052035000034281d6490030380010728501c280c0c6e00c01c0d00f0660110354072250822060342c0c4030b02c2c81400050145803224260416075201c0850407064460ba20741c80d50a80c4a402c144030007903000d00d00103460002200d0391103c4044450307460f40700702148003000c10903c21003180107810050070201c07a2240280545040c08007039809a902c802030703107404000c00c000e0110181c0700e07840720b00c5500444141c6440300400c016840c0c04220035075000418002c41541032030350400d07000703401147d2803005120031940481d001828800484 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 82598958 1250 82597708 82597741
    0x1802071110020f010f020d140f0c090a0f08030c061605030408071a2502010501082d060103150c022b02120403080d050105011103041203051902010501090e0d020a0b 72
    0x204213529020f1450030745103166005103003280340c40d00240b018804003031300041d003010100e42240c06a11480002580c00740c1c0f0780d0060440e548001c04c1002c0854132103100066000850b0400c02e8260b100090202d0091410060598800c004401c1940c40c18040070004069001c0030b040102402008035030300007003003070090780040c0102030801c0d009014548030301d4402c5420484110344140740b003200c0504107047e106000b5141070740c2c08000104940a4801c1001c0590219420341d1004a801125001c19051050200c40e00845c0031b0700040382c045081038129000c80e0103040481e0195400301b4240050040d61703140c641c0818031400100110403030411820b034101815004104c520080c00200802080050000351001e01c1c2c3c42c810400060fa20f8200641c1da0042102d04a90250b205000800000f10342c216901d003540e109192003810103980d0000740d040000078074100300140c1d4685005010140051042c51201c040d031400429044910000c043d495410345603003e0b021000e0395000138400d116112031301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 82600208 1250 82598958 82598983
    0xe0d030e0906041b020c0a1d061309050307030503091606020a06110d0905030c1209060301030f02040f0c08091c09030b0a0603050d0207060224060105030703110d06180207111002 78
    0x252901108050000e40780d5a040042d64414001a4008126115519408200010924292344039615501c08202075041c0c40040748400644400d940c3c2d0024105001401b00c5a01c01e4a41c1501c9040c21507039070703041c07081d01500400000d841010400c4240d07400a04003424540200c40022929159000d02034030b8802e411440746c0e01400c0c000c40100b000400401031401519943c180c404914408040c0c10541c440c2030001580034200307000601c0421f0003003012030040c9100400001d01e0000c0c1386440f2060f144862000400304650342e0401240000c18400417543c00c100d81903801d841c1000000281c0090704c9408058198204040001e1480038070381e01c558061a0010111655020042070080d0380320b141d0b020310310060140b008074605950920200c0c0e039422907111f07640c040300e0f03960340011a865040100505e007090b17180d282e242901500d01000b01b00000040d500412001c1c180f40c2000340c0012405880720459204015080200b10b0b5400c040d40c0003071049030300c800c4e001d8110504915026818400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 82601458 1250 82600208 82600241
    0x5040b1305031207061103060d14010b0301140103051912050901140d060815060a09050903091905030106050111030306010806030a060c03050601090b0a0e2403160e0d030e090604 78
    0x404030303d10005000e08125071103028207100b00822808a048a07000590300d413600109640381c201c0000d40040e0981420001010002070f9031100c81300043d007560000c0031a0201c90744280014030901009200483e50409403030707040c40e1440c100359990015a01c80e401c00d0b00c100000414080c0c0e50743e110b502610300985a90719841c2d1101070b05108007009214502c00c0e5802e51040011141c01c000e020000140306000c000c19803c5802d140000c803101600e0b00400311490350204004500340ea03500c254601851a08000c1c601010b54188014582101c1c42a0052410f10851500c0381c66100300003c103e0368412000e10340003407030340c0310035000c00d24100f054100108403a0810007400172096043d403020344100d009030307904005666101c2c01440c031841464810300010300b4810181989040c40d1082070078600b036080080350541c10840c10007a01d500191540d01c6481c0e45407003001807203a03102c0c100701038070700044a80c152905816071700030344280c13005015640111500b20024003551f0ba5980703d500e24082c842607 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 82602708 1250 82601458 82601473
    0x3050708010e0a020f280903030e13060905071806030b062d0a021b0904021810120c0f0614031303120507020f0706021f020c07030f0f03030f090305040b130503 70
    0x844c3c051b030b0600041140c070210780f03080030000e4403849100b00200700ca0701511050f01440300b104c28031021002500c608034079140c0710340700001e86150720303c98507200b00825524042c0c075907911489800c0e4150070b0341c0901e0405040a00c0c1a0442d91920119280ca803103074401540003c1c2801211100700405132070240d0484000f044610b509500818140343c05035034030585d521440700203005c20801c0e070420358019420a41c1c12500261083c01303c03500580005001604000c01c40e40d0f014a02003500a40d281101d45580710641082540003011280c40940801d0038113051040c0d08901d00d8805020003065103074075120001e40c250900d800382c0e2807108503180314541800fa03480c1011000c1d5840503800e001480b60b101e140d000240f554408104c1e80c0b00500f00802e40342e200f60003144ad680181d041000d1b407001d14001e5002c000005041101c0401c0d01070310641c91003101c0040f030708010b4120b03031004614404960a090500c4002036002c0110f50990b0303070120312280c5485689d400b240900038184c01085d0503104600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 82603958 1250 82602708 82602727
    0x106020c21070b03040b011409270c031038010f140d0203010509090d0203181909050106081302010503071d0d050309040e0c0a06051b10051603050708010e0a020f 71
    0x4181b02e041c0e891101100f20309290250034800502e400329100048844075002e4001003400b0107464a0560341d00604482c03005010360300190030f084c10640f040051956580c040d80070f80312a440300700d501c0b5401400c1d9090f1800720446600c3e52400304560342e41084460901c0702c5505003c1c0ca042c136010204e1598858844200d00c5001000303501c01c0c010188550310f400001442075600060401c1240901e44c099810301c42c50000340344101e80769500c44c5910a170a9841495060300f060409001840d280078040303519454207802519200003c1c00b1865071000c00c509c000050303600202203c0d00325807545000c0704800540081e100d40c06503240c500c0f07076001021407e01c0c1c040c40800006001542c1e0212020881203070080c141d166610240c550039500440351100c204400380c01100540200146101c600083d48403408103941040c0e11140c2000081e552401403002480c030700d2110402c02c03001410f00700301074144035501a10500c014400c8042c40c040c40d20004a80001c0707901551038500078407074007985070389106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 82605208 1250 82603958 82603973
    0xf0403050705090f1b0a11060a06031208010602030322050307030c0c0609050a050d050c0303070f0b0c04060518031218150a090306020f04230103050106020c21070b0304 74
    0xb449424414000340000c282020080b001090145a02440780b504100c01091415200d4000a405806001c40820362960302d00043c000d480c89030521007800641241075107000002185004030140810074080c1c0148201c0380c0010850f60868588041050a41a009583c400d5400ca00000030021300000c2880c0c000c1540055011a20030301c69803140c1d11050301c0d0041101d840c2d030b0390f03c902d5a12140216040000d820f003101d454032801d02502c19240304041c103001091070340d1300242048900496095141051010341408640c1000c80984020714043c070386400180f0034000c401403a081161640c6070306486640c01c00610011084c1004100d03200e201140d503950203c200c59a07014003078a0040101440c801a4804503280002191a001403a0341181c03102c000940040d890038450600400001c6613050300a441441d0388984280c8004400c151300c0001025220306900840c25540490542c1c00d10b035035444016440141c1e00c05d1040d84102045202c145130040f1179100f680d55450010a000921915 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 82606458 1250 82605208 82605223
    0x3030a052203060e0d020c03030406030902031009050a060b010503041a1e07020d030e0106030b0403050711060301150e040b030c1507061418070303090e04140d020c0307050405090c060307050f040305 87
    0x40b400c0e10f800c440c0d503000987c4c80388205041d481e0305420400042c0310081c0030781e2000c0d08450000e805c5070b0810340d11000c003804580c0c801c4821740e020760046100c08100000c81c051500b10700b0084c40d00a0850800d43d44280940034a1000300040030840c0000480503003100c01e607254580c0c1c003014400c0c81030804440103521203102c20101c0780013904102070b5a1010b0814060b6008803907004403107124641e200d440c200c0c1d04e80c000714401c5032040e00c1c03408800e065644800286000c1c0c004045502c07050f4030144000b0700640101810140038a0400740f200301c25a5020400040b20002600e15201c190862241c02a5030305c00d00100030282803401c03244c00e1015080441081c882e2045402001d00320041c0c401e40c40c1c1e0f4103a5444014001011418240601c58880321101e400a120f0407250340348804040c00e03d42000d1030140408010f074059a081e03099440c08005080007044243d8040042c8e04048a03242c2d214a040741c0f61034022030300080800c4000348508110f0300b0350902d10341c5081d1510380724500582c98188 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 82607708 1250 82606458 82606481
    0x20c1302030901060b0f0d0b120a08030109060608130605071101180c081506040b0f030a050a06151a07020a03020901060e150307120f1b05090907020c03030a05220306 73
    0x1c4c04102080440e5114102d442c10745040c0320443c02c00581c5039a48000c0d007440c0500075040354006011845010b41005162040c130b00c500603a68032581443c4d041c108451940d4000d104200c01d400c10712024a9960f00d12540c4941c00c000302051a03900c003c001e075521000c1c14044829986024001030840000445042607030340b040c12480e41d00c513511070000342d98070300b02030029540c9900d00340842d40d6841d0550052a001c0800382c50f0b803040e90031050020f070924444400503101500000c80401c20054144a030b10ba450000005011405042c0b0340040e84004500341a4440342000080000943d51110722070402598020601e12080d0b84882008100d038101241aa00a40d544e09a01c550812901c0c1601c0c40740a2a660300c12442c002500760360040c00e0480e02400d052592035980c0c0340034200400b404001d940c4980c90f10750ba911565401c0c402c3d4604000c2c003a800b150000f400c440800d50b004011510716080d0fa280c000d884003003021140e5401c440354544000000c0c2d00d00ca0000c10041140c000e03003110407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 82608958 1250 82607708 82607711
    0x904091e1a010605030915040201090b0c10060611030f13030203010c050a03050f0105010f18080d0c03090b040b0906070501152402010c08072631020d0602030601020c1302030901 78
    0x26070781c3c07900380c41600068882c4d16681c0c100c4e424030403000c2c03d09061281d00c9401494500d10042c8e96010342e4039070358000210109190001d0415100d00104c6004540c010451440d004003a111010045a00c90003950300300c82241c82d0001d03884244121504881c00599001402040301001114025005600ca49800700c0400d042800040421543d081d029040310b8040e140c80c1460a19484200e0b949510801248044149448003140c0840208070044003802c00b034071010711040f254107015020081070382c000307001c0010401c01802504d8600c4140c880d030741820f8030f00c9920f07104c0782d05d00540900030a044003208183c00c014001000710310328403003608400c040b032507404a4260b5488100e00b0385904c1140f0302d0108000c1008200e68600c100c6001c0721046c42030b42d42c0d40c4081d8102c01c031402d013004103684800c0e000300500e0078052220100f00c00c0500c840003400200c0d0a070503056011a0011542c048090102540800062000e90092040c6101c5410051014200b810103510a80c025002a940c11820790f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 82610208 1250 82608958 82608961
    0x20d0609060302190506071202030c0f010c02161a070302030d140f0f070c080f040f0308041502061311040608030a030e010b010201061a091f0f030c0c02060904091e1a 73
    0x16131000100400d8410192160b0700d8201c140c0c840002041502c00940c046102c2001140d101e05014400503020501c81400411010074ad40340081c9071201c40308042820700890442007149005116012460a003072480c01303900e5070300c40c3c14240d003107004009150a8090408003031150001d084540140304803107600c801481c81c0c0343c01c20028100001150010003050b400d90007139011440354030141c0040b802008050b480c0c40c0d00c0b0301141e01000416481129841000310f0244a141c01e42040540c4041a80c801402c90380b500142c0031800010f05a0f0241c24480190302000064886800500241001004607940c80e901828010000c00b8030894640c0310317501c1c02c0c0c030300117503580706009240c1100c0b8010803840102181c101410059481303018010361160300e01c0c0c040c0c041c98011140807800003095458116984403203200150030789030181000020821041c003420b00603640d180544204d400d00f46e40004010b60586414000e0054100c10700140ba4020b60500040200c90760681c10340f0716840001688a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 82611458 1250 82610208 82610239
    0xb0403050705031212060112110f030a0c051603080403050409110307140c0c01030506040b090f04030323010b0315030709090201090b0a050909040510090f03080f040b0a0b04020d0609060302 83
    0xd5000f54400385c2e6a03840c070321004c2903896110700041007031241507150000300e8581c1010030340f00e04e078400000e00e20313900340c08800c000d81c00e0414450410008078601340310b4030f0074591034001188882c0c141d00c001d0500c04408042400e2511400c261000f178854040108440d01c1ca4041012242d0402c0b141400003454151440380805942801c0d41e4120140c80c0c01000818034840054000d003000808294010f41d880c01d101d80340740d4401155502807402c150a401842c10181401815540240012181421004020101c03080049203030340c11540740c60031b15a140c1d11010391000645000d0042a07a04d8801c1e0a00031803a19800d40c406004140300b41c8401401e240d840c42c01d66600c0c0a080002c4001c2441072013140302c641020172850340d100c2e1091054500b07844c0b0b40018241150b0b4180010b603804070f002c4602108254022003055081588050502000e25180d601d409503280010142030b002500c1d60704c9451641c03a140c05491540709919010304c00180c45e076204000605044c40b0a9100700a2040f041d80c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 82612708 1250 82611458 82611493
    0xd0e011a1207060207171c1812030e0103020c0a0f050c180c03061c05012306181f0b070813061e03020a0c0f050d02071d130203070b040305070503 64
    0xc45000341c0280807403034504000c90000c00d00c017045413000390040b41032200c40341b5820347c10b4080302c10054403150003035694440b400f5035100150b0800e024018407640350802003900083d003079000d07401c04d107405680c40d40301403015810f24140b4000102a4040381e1040010850082029401540d003a6142c10301620517103e40951400d083d91001c10480041010403104c0c14062503440d583e0071900b44043c0c2c250510b640b250300311031001480740c5010751006400b070058180c004489401c481c00712001e074001c4c207902c9001d1001001c0608450300001c04000721014a81d00c20400030f0042450b03080d8151070702d14905051001e50303c0350042c0c50103031188400c003144540c0600300703916840c0038000b01c0034000c56118200703400035402a110303039060100746440d09000614038500c0c444aa449080546022342840201a1400401c0d4101e807140e00b207407000a501b4070105503242540700b2461100300e0111811070003c070f03040c150560005111640000b40200901100184076022a50305500701c4c0c401403141c940041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 82613958 1250 82612708 82612723
    0x30e0406031106090d0b0f060a0f0305251703090f0117040308070201020d060303030e0c04020406050d0b0f10020f0f060403092303030406020f07050a0305120d0e011a12 74
    0x14070b40002001c1110035410442c02400d40030802402a031301c1410151140c070000c00d0201c421940700700b020020821207040a02411000b04464501c184041d400e40d0744064a03109001ca410382407042d144444030340150341d807807080c000700050900b608441108968054803a4055800b05000f8204508095025442450200000003406c03541d00b2882e1160780d0200c64882c40505038004542d002c1c44180d442040f14414140214032948000520040080003581845403100c0e44a100300d2050104202c02600b1400b201c1c100070040200050b01c0c0e010500150845031100c2c0c110750805400201080c0c580e400190070072050113007400315914610400c040550f00c19040320002c001035070f403000c10401c6040f488090103402e03996401c07040d1000103403c0443c0c03564100307500450044c2c0c400e0342e0381110745600340048809000142c0700e40041a043d510f03410341da090310031005244210000f60000d00316080754043d00c03c94941c08024449100080105844135151101c07241c0b045018500155412a0008641 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 82615208 1250 82613958 82613963
    0x1060315080606090103080a02160e010302030d0f08070f02070e07080f010e190504060b0d061a0906030a140a060f1a04090b070305070e18010e06010f1211070f03080103030e040603 79
    0x10685e82036581c0c40025810002c0d0a10540c4900300702050f4003040f0304003c401402e10b0200310300c1f456246004140c94643d10b910f0b82801c0c0042d4a01e80304c001c95000e045164001c421707051078540c030080400200d00c1d2000075803050515080110610004590180b203441c014000c40c10400120703600c3c4e0400281c60f03102070301c80b200082281e0300440c9210710940c000642c4607000344400a05c10300c0d40340c08103451246491040390740650f5545800d003010000344540100f010161480c1c2070074035000c004240d0f0360700f1011000c2e141c1e812840d1081c2035032504010012010350700100c240107554010414070054003100700c80e0003030f00400d180c0040301410709104214401d9000382d1446419200d800f0300ba00180b10140015040100d10315007031051340c441c040c0a130300040c00d0544000081d0301d00000629500d001808150401041003c504c010070b901c800a04200303c500500010b145010310715990151248000080050780e070341001c80c1c14180c0020020f030490b0300903140e4100e580720210802007190080d0100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 82616458 1250 82615208 82615219
    0x812190b030d0f0c080f07060c090b120a09081c15050102060112050f120a0e0d02010c11010203040834080a060209190801090b010504060f061211030f040519080d0f1401060315080606 80
    0x40c2c13284408148221f37900036060350400128512592500c0000368060600707144446c1c50100c8200390700710030b441000140c180031000c20004509080000351100c2043c80340e442443c280f0303c03401091000c18403800c50b14204080c12a40f0710720f5060280150f90704091080004541c10b00141880741c140507141c070300c07890307416515001064860307694540103240000350903045200c2030001043c0404100021580350803900651300c604400341e11041e0160001041308045124a15000c02c07a80380c002500b8024660304c0080546c4520781c040100300c42c12400001c541e403a19610b040002d02a5040d4030044030580110b4a5207030980c1c0304c07001d21041e101c0e40d2140d403d1041d00c80c0380800030240300c4c0030124400c1c40c0b079800110f41c100088a0340203464006880f6101207194150512040002c10800c9803400345c12403006595002a13502c0d0311005008100c0111800307616407c01800e130407466803014260030303080301860b00036507100c40c03005008060401c0c00c01c091424600c000b04048400040c250300c9100010403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 82617708 1250 82616458 82616467
    0x150702010608121b0c10030603060e010204060f05031b03040605041103160b0c100603120815010e0d020102031201030b0a060f030b010302010c030c0812190b030d0f0c080f07060c090b 80
    0x1240d041c0c0c50203c881130718020746104c002d566451540007262640710740d07000714010b07045041c2a4226280c1100b1140035030705c10081000540d800c5944c03030a03101d43c50308180d40c49a40304901095117030000c58003200d030303c280081040b0811105602281c0114011444040c07038003045001e05076a05004e0007880035142e01c1c003604002c04034106005210b03640700729040c0c0b544c1c00c017209074140507036055410884109403200c5000410551140803182e200101c0c0040b82e80060100e000640b0421002c89030b54003d002c2c8803551b00c20343e4000c101f19003101c0043e8a4203101036959080000c1009000e035109843d4604000c8001003441a1810b444e050381d410000100d00c6900c3d660064400201d00da000324144600e0b46c0c200000f0400c4007000d4072503450001c81061083c5004040d51180c003560001c0c1100f003600c0c0415402007610002001084c13810f190800e10704c42c0a02ea4019074030070309410402408034070f00045d0341c0d0406c1c04181c050550a84542c1c1e0070700240482c85d42c180c0d9140094003d440301044c0512 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 82618958 1250 82617708 82617727
    0x1207020f060f19061d060a12080702041b030b01020d02030a090e060a0f06110607210b1906020c0f06210703021905180405060f0d060b0315070201060812 67
    0x2006500b000c201007402d1a030300e1a4901502c29134201c1d03484081040d21040340c4031284900e40701c0d5251301c02c80c11242c0d8807810f070424824601076403500001510f486400f0a1400454030b481d1304c8a038807510b003490b40d492502000e50008014000c40e40d01c05005000300c00011040d02e0000007a10290612501c07000351040c01d0007183d04020b10014085948102c140d100000e40589600c980000b82c041681c62207000b404050303125180c590041c0c03e00003003000703c01c6a20249100381c1c0c003040168090002c08a50b4900c45800240e40c00140300c104d902d82400810001102500001c0c600381e504400d64030302004102082c10408540034a80e4412150301c20000800078001121f02200e5000d02c05050060501119590500001a03900c0320304001c60400a900022010002042c05000b0300488003884035103412004074411480181645024821071005001003100300d4002d01c05884c0081c0c11910b06842c40b0580044404043e10342901651804201150f4124041074841401007203a0b0070511300b40c11070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 82620208 1250 82618958 82618981
    0x9090402030109120215010e060a03060209040923010e060903030f09030409052e080309040209131119020a0308010513090b0a0509070f0311010c021804081207020f06 73
    0x2001240c0c95541c418074003002445078824a44180143d50040498002c50140502080c0060304001800c2d8074803010802070f0380d20742e210941501c6d841000580c45014900c0440d0180298000040c00e60a45180380c07403421b210728a07580082c5800000038001072650b008429214481500c003941c0d20342007080050046203425101707581012a00c400c03031b0b16160f03545110b03070b007103d0742130b10210403903001d66000303c1d08080c1c040701d5038500040110142c02020300e4038140d90303603030700ca1741d55514001d640200d0880416130301d0040c85000c1d01e105207130030b06c486d02202e04003410543c418098848a203803555108240c0f98030005101003403a5043d12049090390808040142542c0806c0d5951081521001b0001c00103030f24412160141012000200d0700342008041603080c111290401100720010f45010004220501c0c501c0515100a0820741412800c50001c162741c0800348040d240d551851034140b00030080200d004107661007540a5244071a140e0003800c0703884101001c1c0b400e030950b2040000c1843c44c1c148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 82621458 1250 82620208 82620211
    0x40b03040311010903020601031a0907031103070f0e0703230408030402150a0903110d0302070b0c070b0a0206102103080907050d050a0209150d03050d060e0f16030c02030909 76
    0x82e08160070480ca00032040c40c01d43c0c0c0400b400300c0042e00084010010052100038594401461076111358051511620305595914640b1010b0700c18140c80701410020b0700d05201c41800b4052964480c7c44042c1c40d40c0066039008403e8480c40002868072440802d5900013886c451180c18044031540040d86898403880085e40000c2c2080e68044800001c4400142d00342e4000c1c14405021f45440c21510303c0c0d810b0480390b600140f46003d01402d0f84520000019a01041c5841500d0003c8050f0381c881d1008005985016510740000300d46006c0028540d41c00c940010301e0510031180e03207841002036501d440d0100c90a440f40148803810000b40c0f414440001d0040200d40c3d84860482c013114000c0b60b861700001c0340780040c1d040c2603840ba00000108010b500b048519070740c4c4950303440007160001c2d1540740428812088854050200040460130001c0040c007a08244010039907825260f0160421070030b41291850223555204504801c2001303800100e00030f004079410381c101c0d038001c0e500340003001c024007100200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 82622708 1250 82621458 82621463
    0x903020c0402031314030f1e07080301031401061401080406050604090b01180e0318010f090305030307030f0b01030e0d03090212070801022511040e010f1b0201060e010308040b0304 79
    0x6041424005500c0e5031000e90f10812900d40c00c8030131480c40d030800c41d08007001000c040449802c204202041d0811920468100780e01c81705020b4020f007500040f582080c020514000e01c00100040000140600c00d13079940c43e0800410000c00c000d6603035800c0880c81c5124480300314040340c030001c000b5000c10f1099000c0e5600800281c0040381c5c400c8266500e10311060300341c1020883e050880045030700e101241c490003605414804c0107500c1c0842106d81d001640030b44080c0f942c10091099540d00d8194802d9036000c0c003c5502030b044030313103d040580d4050094140c0d402c00859451421112103450340c801d008055540c42d0b03002c041d020321071069500310050048948180e07000441404240f02c00c4000b0000c1d02e0007084580b00058403104014060404504c134410b11010056411900c1000b0607a034800518264004590001d0380c21180700c8114058113250a0803004685091060b0710907040c10b403101c0c4100d01c440d40c007c002c1941c59030300321303c1c20607428080035245690602c800e0040f1000440215089030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 82623958 1250 82622708 82622713
    0x15050304020307090c031e0501080d03020403230a06060305061b03070915030204120f02040e0a08030106181509090e011404060b0a0810020913020901020d0e01030e0f1b04021309090302 81
    0x2a54568a24007c0300c0407002c941c0c0180d80320b0040025100038025034440c0800707840d055160500d141c0307031031916980c00d25041e00195101882d0940050080095040e103a51245007801a595130381000d80d11004100c4248003610f9400085d44050024182140d2044801c1d4072000fa0090402d80b0308112401d01c1ba490500303050b800c00010400311080a40030005030300c14121640401da513071041c04159491050b8241c2141c0c0304070403450018207200705a80c15103126242001c0c4403050302c0040030410200d54400c4948860410014682d6988221007405270380e8440c400b072100e4083e83e0210303800c8a51000504003807418000101e07000513015000301100341c500030300c1907580340c2d12514000d0410300141d40303480249a0000e482940390030506100030909c6004a4218140300751500040e449a034050000002c100a0b031031001026070103030780007481c41c04d0704008558180000c404080d41d0b48004c0420b034602a003140c44100314501c1d0034000c031014680b4800c80c05030082e14060701c00020780340e802411020350 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 82625208 1250 82623958 82623971
    0x114010c170c0f100e0a08030103080306010302040b1c0516020a11030a0501110c0f01021c0506131d0105060409020d020105031e070903261b01020702030a030201050115050304020307090c03 83
    0x20b00e08002d103880600e00000a1300b488044e4003c040111113079080d8921903600b0125001c2c02041c48003080d2030442c3c0c0c000d0759155a0303a9881004070000d100b5500704000310480420303040008000d0306140404219803110800c0240c50300c0940300009051425000c005a21000e1413000003410b0262440501b0f0f0042d088404a01d41a5119801d565000071b001100c04404100d96141c20001c0100f900c008085000071450304008400030500080442c0d20000c800b5126804100c090b103402c1102d80b403e03180c40100300036103a625150103040442c031500d00211582801d001c01e03032520303152107203100e0349034014042e110710022640152101d41004140c24400890500745102d0500d0448403284600825600c03600b929007140b4105400c04030911241c0c044a81c0c001c0b016000008910482e2071018246900c070080c039080c0c214082c00f85c8038804000f5010b000d1034021500701501504a20305a580306100b101ca01040300078102d170903003c02c4501952550014008111882d40c079031041e41d081040345400f1485 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 82626458 1250 82625208 82625227
    0x30c0d080f0c0d0219120e06090904050606120102090904060c090e0c09040614100e060405060d0515030a0f0305070c0506070c0602100207112808010204030204050114010c17 76
    0x22500505542c002c00d800405000e00440d0f41881010350300b0b58078000b0000b52000e0f0f601c9010a807480d503c280c030f0601c026240801600d5071058240c2e0a07030b4000420032901c2d032400c2d14005896410030b48046000d0b003013205291407176203410700079078410b41005400e2407900d0381c07507481d40f00107403281c20441004d008001a0124500c002008510710500a00ba01640d8444401c000d100032100d903648240c0c0078040c2e110f5500c00941c0c0f48180b69101d1841407078140040c681d8080003810030311803a403200d0f07441040090391000640c600d800143c07083e200007506604001c2940d0034151070f40c6686030000e00d800740d50300303240d00020301481c040c040071402083c9028101d903e036004184150701541040e40d0341c2000301000c000c403540c10031004c28902c200030341c194106903613540e030b0404d240c203222041d0b0710414860740100c410003a400c41d0302c6a40940d250a030741d50195070f504424000c4d0302600007a802181081c2c000300360040c1d06c0f0101020124183e540c10705440460302c0c0c410b1190075032000300140390401c006102c0c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 82627708 1250 82626458 82626487
    0x1c0f0c082706070b040510020301081e1213080d03050615180406060809010c030b0a0306050408130b13051801050d03021516031a090f0a060305100504021905030c0d08 73
    0x6400340b0504d00c0340002c0c20181402c0d0316101c0c0c105201d440c0b05004200500c000c2c4000700707040c00d400402d40202070490050080c143c3c1450994071545403000000303d461140c040c4010084411620440d043d40d184181c0703800d0403825184111442508103802820707190210740540300414510012024034142180003030001b0302607500550103100082c01c1c0b81c0c1440b4070090f00380701d41c0240d84000e0a040004141440100d2541a458030002d005070380c0d00c5000800f40950042290344076100c460b203110030b080e190800005160080000c07806412103801c1e000c44c0e103003444400d0000c0b0314483d0080408980c80d001c20000c00c840007103400c500314040e5600081c0d05c03125850072640581c008000303d51410003c810010201d803000b814500c0c01c2d171002c031203028941e19041111138200c80ca01181070115900d0508443c0030b0a850b1740020550f1041c1da40c21400e905c06035003d80c2c060740c404c480c02c0300300025510701300b4100100c178000c841e0b040c4c210310104444c51030006030a5103c2071142c04041d0800f20044031600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 82628958 1250 82627708 82627717
    0x9030c0303040b041b03020307060c0206070c0605040f0803040e040807020d05010f0501090c09150c0201170103080a031406150309070302150c0105060d0f060b0604081c0f0c082706 79
    0x151044000d00c140002c0001c0304801401001d40c5c0d45601030818135540009640d07041c0c51141000384000c20818400b50340703402007142d6041350082744130407482e5078400009249900c03c0c420001e10b40b01403500818040e801104641c121402107100b80306584403a1104009580140b004907030003807890310f032540010710070701480107a01903030346000420f5850003500e0410313a220307820741c1c030300f04044603006021030801d1080b91a04102c55140c000d90010140c40141c9205005400c800c1450301074100000401c5844001008281220303134003031046040c2d400c40e4a41d41107040d1011607028802c040d000070613468500282d0313441400c130412910701035070744d0700810000c0302e01940b10820640000384a904040c400d0069a4100d00180d0305d02c28106001c0d142c00c039800c1100d600042815403603640c28505580d8040c1030f038018100041c20b44a50100c0c150300400310b0024202c1c42d0707020070780801800300560302890241d004690800301c41450a00d01c0110310007542080f02e1038452060340c4d402c01c00c13029255940a407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 82630208 1250 82628958 82628963
    0x30e13050f060a080f0304030f060b1f0e011407020d03030b13061d0c0f0c01111b010b010503010f06051308150910050606040302060313062f13060809030c030304 71
    0x20301c042c02c00806000f0814415000b14803e03030b210400b14404000c0000c1106c0459801112a0b0b1114020f86860006007521607141503201c03050b8a01c04008080d640c103c2140300e00c064030340000040140c0c0040d46c0e4443c1294109c1c40c001000d2110f2409414405400915144a4940000c2081540c0c0015100340e01d851001450640e54820078450049039449003e018860700d000c0c2c80c513920340b03001d41d1881c034410700205140c0c9030313004a14006101c03825085101040a00c0d0219030300c03882040c0240e0404040e00c694080a582000102a41940135908a9068400c1c0406000317509003003040654559200303580100782085501000220342106000303c003003090458010305060700340740c02424504482002c0005009140c6824002c8a03038425086074116503060390810f03100e5644035040a00f0340308049003d007901d4100316400b1804000010340b98007010308160394002c05581c0099900741405034001c4182140072185040c071100740120b01c02540109074400720303460548030044003400e50b001903504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 82631458 1250 82630208 82630231
    0x5010602030903061e010b0a0306030b01060302070209161d210105160504060e010e04090b09030903010c05030f06040b1f0207050109060c0201020705040216050313030317070804030e1305 82
    0x511903a858180907040d003105c4d1301c07030340c820000040302000005150706100d0384040c10800100c0e1106a40a600030a00039174000d20004241d41e90b0300409030103903001900483c450700d012070000b0b40d01d005100186842c40c0640d692200b00201c0413120220303454500341c60700c4d440140e007011424484003400c1d1000c0b0020400d80045080e0a0420740e0890342002c004184051110500c03040c802c890307011108040c40d03c002d1800340c00c8030204101003001000d0f424009050034030a0010040c4410b030000081064500c103500800038840002c500321003501090310107859001c0e090000c181e4a01d8140c012120301640204000b40b1444607074601da44d55041821f900f00940c000c00c100700090368000c1c4c10b010041503181801441d1000030360000b915901140101e5204981c0460004074068803010f40602c004e034031500f280e503941d00f511502d111000c002d200480001e85120029024050054000c87c040c0181c0e4031a208152201d5070180c0701e0009581485400813441c44070b01056402901030349001e503c403a510b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 82632708 1250 82631458 82631467
    0x70906170705100203070803270a030801050a0f0504090812040c03020a050f180a060807030c05040c0908070303111006060309021302030903040e0903070204060e070905030a0803180708010501060203 87
    0xd00e81001401c0d07020740e105421481000003140c1c3c011003111030f4694007406080d5290744904404140100744450402540c00c102c0620528910001c0c00711030090090701c1d20203d82c3e9032201041748903c424001e003850403010b608100014101500007104151044002c10f0030b14003401d810700c400503001c507420b54507071402c45000c00c01e5003041414980908026102d00644a1065000c40c080b218503061400d200040000000c1c620310040c2c0c4160090160b020a460701e403035490a00c0036000c03d00d8080d0905c600c1c904069540c0c0240504c05100c205c640490203800da840c50360301d0079244aa03515041c0040c6014403429404040b1051081c640600f8464030005429280e0340180b03c9030000c54122942d0349403040083c45010140003090314101c84808040c0c1c12566070f594600e80c19802204002904942440c9001c11444d170b45000283c41030006542c0c1c0c1d03210999940c00c250f6648107900c0d002e003100b1410400315840a403c00700b1035040b00035000442e5806907443e00c0003421101c09901400042e0400314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 82633958 1250 82632708 82632749
    0x903060b010509060a08090a05060a06140f01140f0702061204060507020a0528080d05010828020603060d020a0f06021209031203130b0702010614091003080c070906 72
    0x4640d0030149401c1c03034003904095984000c2140c5203ea44000c0c1c09220183c000218a01c604002003401c2d030391300100392111400c00194800c0540f103140224016847c0e040644401404c110004d42000c00c0d05a44074020a00500e400030079aa11140e0392403200c800400423503026881e05001810424001002c403252841c06040003801c9500181c40107007190040f9250078007080000030401c5200c0603280554084410f884000c0d000c8664004008000030004541c1451040c41640900d04030385010003507450310880040001442c50030b04506540d00e010941650001d42040c502855100d030380070b420078401d00e04640000c1c0a1a019070700003400c06900c1130092052030b60522000d042c10f4031950b40b6a08090800340006d8841d0726085120291040220004801803413107945c03e451250020104402424891802806032949011300a000703008075108803001e081041c000b03032240c00d215004146150441d40c031420b840c1c0c0310044016941c420f0788000701d00b4071290312400c0014600c05808140203812103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 82635208 1250 82633958 82633961
    0x3070201030614012114090105010608061504210f061a040b0904020f030102070b070807020d0f020606090411130b090906010302010207090c05120712061502100f060305030a090306 79
    0x54000c2100344141d014000d94a0b45c0004141c0b104800d02001c80940548291a5000805041641034000048841446900c1d9419800f09058911559552180d0344d030718000e00400c1d410349034100c0c2003000c1c00c1004210145828241200707281e210a00d2042400003500c98851645420000341c03a0302c1e6a504d211000c4514a03829207140350004e507800d111443c3c01d07000049040074002c0010340120b140c3c0d03c000b92644d4003036040700c0c00f255006017000240e040030000240010401c60700040544100b048078440300d801041100c106c88096401403d00f9030300d003002d111091304040c204440c100d5070030b45014019030307640004040468042d180043c80305201010000307100005000c0c040c0f560402c90062002d40d83c01b1615009403112141c01140e68041807100300c840c4e01c41c00c0e00560902c045c1106226009501c2200303000302d0000440103210701504c03850f2200c404080143c00b507001d640040b41d044a0891150031034241d401d10320310002031460341c1c0d0329400c0c00d5500c130106000026104c0035040c020881c45 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82636458 1250 82635208 82635221
    0x51506040c02030414030a08043f021009050312180f0102070b03041121060a2a02030d0e0102090a0905040f02012f030901110105040c0e041b0303020307020103 70
    0x111014007600040c110003940303030320941c01078481c02c645801c03048140c5d8504001f0b20601942c0600500c0c3e4540e40c41c2642000e50f41d1060070508459009400340c03000064124804554448035441444000c0f856802c01c00c0f04e1444000001c00d00040c96000141c55a0500c9208405a000c3c0030460313880c00419440d000e035800d86403070365100ba6001c000c0421103036030004282007a90911141d0a41d030b9221414101d80c400110b00000758802140f544890f07000704030100102c0391042d0703441111300c04d0700d4140722442a80c84182c0c029010140045507812200100c040b06030300c420750b0340181d0f40340c10f4203d0242c0c0e050351650700c41d105060390001100d01c1c46051004c0440000c0c003180408004904140c0d580340f40300000f210f400382c100052820342d0004184030306288409410528038140c00e01d0b00b00e6a0352503c0c0c0d0450352146010440064419400d0785047c0034031482a68006404e280302410310800f010300110203071090b940c0c8028800f4060740404010010400b8600980003140c40d02c40c92307c001010f803000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 82637708 1250 82636458 82636471
    0xe0309010e0a030b0a02160f030512010611060601050306010c14060f01050109180f060801050702060708150102150a02070f031106010b040b0304020f030c03070902190f020a15090206070515 83
    0x3401c50041004c29074420915401212040002d40e0310304607060f6040741c00b4040701c005041030360660748800c00c0503045801420075200b010f0510750b81ea0f99074007040e200c6a465004114203600000d001907801c2d8880d1008550082c0141083c00e1010095201e042034100504c4030032006a0207002407181110107107500a0042c0404d1074030412050420b14100301e034004003010005460303181d081109101449400c0000544640340003007040d4035100d44000c1d0380303082c2540d0745400b040000c8003180b0030480380072410107014010f070000c2020103082601c07600e540c42d0080c560303e0346940c2442950006459815400d4407240695030b0180581400310209040038010f9114441c1c840d01080100404500079040e00d601940490f00001112014404a0f080c01d0150315100d030705019401c0003060b880601c1c0d0240041803d80d02403545034a81703001094450b44414030021000d40d0009244400140d0031850301580c1c1028020007140840881e80031071007641000300115080c5d00180340c000070f0003501c030344502e50261 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 82638958 1250 82637708 82637719
    0xc02012a11040c050a030e03070605090c0f06040b09150f0c0f06070216120606030501050a091e0305070b130b011401180b04150212040b0703110624040b040e0309010e 73
    0x40300e800043c101d40f054402170014140c882821001c900e80c1842035a8401781c001d00140540d1a101d0300c4152910380c0e0160700742c40703650303001070401d024240714050354207a401030a41c05d8a0443c004003040031600c1c000da01401248010098000d04000b101d0140083c1c0310454002c000d00c43d4005021420074400a00420441d40400740c46100d1035441c0c58540b040350614000300f80c1100003400c00002503d00e44e00041c215608000c10302c442010030794050100b490240f44840c204401c4500c5d59442d08510260240c0014001d00c014008283d5202926030000412518901c00300955541c0c03207001e1100f60f000c10503074911000d0440b403550f0091078441c0c40220a488650445003080202c1c078035400b440c040c8001060300000e0910881d4003c0000d0f80b8038800c6400c40545503540c031380d004445584144003c0b000141035008150140c90005041d901418011101c2980c2c102c418243c4206594108044d0340e000352a0110100a42c60302d01c03c2c0c04442e003a800145545443c404009000446110303e01400784 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 82640208 1250 82638958 82638971
    0x70b0c060a0506090c0f130e1915060302130306050c0a030b090723090301090503030105011106090d0309020427020f03031602370303020d0f0507030c02012a1104 71
    0x31342e034810007035a0011740c000c0480c0c1c5802d591040da4805004440707114440c90300407200855a01101c803070380740c80364200d40c1124003212108254001038640c840c100300d4942c85440c10920016000740c0191a6280d0741485146950703907261100c6054800a0350094a0800f00048821b0742603498000c18411141c2610000040c6c01d00550007420700d0044008510000102e1810001e0820b0b00c404031008460f00500038032043c041428510b40701d900078811036000c01c0200c580f040d0346d0304000c1004d5114400b200c01510b000402460240c01810b85150226401035a46402c00c40c6409c54880498500f48400c3c001c10700c60344244103010b0000e00c40f2200d6032003a482844030300020000705110585d01c0d50b05503007031050f2343c00c0000e011409500c4007000c9110b00c88818010b01308445600c80030400c0368001e40c00ca8115071076014095a182d00018082400a0f40810250303001c00c0c010a6805480391040c034040035441c8000000c0d900d4414001c41c0e0b0520142c05c00c0d8030a09002c1031410a5003000740c01c90f4200b080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 82641458 1250 82640208 82640221
    0x504030305030f06010e131a0d02031e12040e041709030c152808070804080403060e100c0f090806100e0702100c0302040305150412030b03030408070b0c060a05 70
    0x15400b0080000041403940e07030010b962a4400d0b504010050400f0b440c1c01c2051601c2842e280c0940745c6004030281090003031814072004e1608030310060010b60050080c040840b820403c0c00480e1020140400e050710608022840c152904001040184804040148942010300e4011542d200340140c51303070741e06028003a11030a683d01041504828104607203a004520205045480c40e0003031110b200381d0043c68801e0503e08c0600f842010200c0c0305d50f070f541d040040d510048151008075043c0d5024003d02014441800000c44662240c280d0201c02021141c3c400c22240704641030b1107a9040e000001640041e0085400d40c001070402c001d024104068000c9140143e5182005a050b2164245070055140405da0340727030003030080f13240b298103000302031103480d0002c0d0001d006540548011520b91207004103039503809818100c100e004a601c407010b040040d1030420100c01500940b01e102da032500007004005242e05041140304010580043d00380c1c1c461f440140c6460602c840100b505180314141030030444d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 82642708 1250 82641458 82641467
    0x507021c050306060a0e030109080a1b0804090203061809030d0c02070b070201031107050a080301031a040b0402060307030b0603040b01030b070503010f03030804030903150b03011d0a020d050c0a0b0d0c05040303 92
    0x14811410b49106440c5c4200a00072282940e08940c15074041d440c205a9100344400340c002040803002c640c40d11118030014a03034803044041c07141000303010001c040c00213214840c40e40c0c008503007042c00140241c4492817100da160403800004c0e500d0700301039807000400580e800414003801c4008212800030300101842d20b0841807052084d514000d041598407002441149114401d48030500c1e044401c60398030311214900300c943c036802030100391031005000481c00300d0392900c10781c8103100d143c0c410784c00c012644541d401e1014941014000da001d040e01c0d280361050680360b2030044c5101d41c1c011010100341d5459420140c00c003810160103401044010001409000c410183c0b08040340d502d8941500c7c10f6517542412070342c0c51075a0704000d02404104c3e0f042902c144031038209a4000c0400c40c020002016120200004d0a411180c805101e401c42211b000c0549003100701c0c0c0ca0200e02a4080d2502404014000b40c80001c5581100c951010086060100030800340300744104808075050003440c250860f1000790 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 82643958 1250 82642708 82642711
    0x3020306010b070615060507060b0f010c0f050705060d09061802060a1202120a1d0105100506091201021209010c020601180203130c08010f05061906050d090c090507021c0503 76
    0x7401c0d40300040540400c92280c2c01202505c404404400140340c40700d03c0102907a2064070f0649001d810b007504a10341c1d282038a07800d103003070070161a5030f900c0c240c540d40c454440b0704c0340c0c0005846500a5290006542d00c0d000c004040c401e00304200060500c01c0c40c940a000c03500c1003903130f9841c032582c0803d5079801a04c40707500701c0342c80d1081400e01070780039501c0c8460b2038003a12a010788110400e510350b062081d031502a40040c1c00903e0010b10f0545501325100c020703404c90780c0440e982d00808004050410480c20b2500080c503c04001408900805084200340c5099034040e001c1c01d0741c24403c0c0d10421108420a2154811404c842d101505042d45004180145041034581d0000000c1c0c0c0000840c1300c82a165003080c00702c951003910200f14076940c50001e4002c021001d005101142088001101450b09001200d6400d4061a503860b40600b440011144c9800c1584601c0341d090382e41c02c8010100722681c10308801880500c1c80411989400b040007070030800440302162311008039a055600e000d400c001541e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 82645208 1250 82643958 82643969
    0xa0503032a130e1503011418060903030a021303020306010605030405150f0612010b030618010f020c0a110d060905030a1e080103060e1011030a0501080706020307060c031b11010f060302030601 84
    0x10f200e180ca0f1403100040045000241d135500d50f28000300f005680c800305038428814082104e213503102030710050320103403207003412100a100f9801c1000021800d0030070382e01070046a9204d2508803c40341d01c1c1c1d40402d1820a00f80c0001010540c04010042040000c01c80c14002d0b504521118540703090600d00158811000b801c0948200414041e040300301c0340961220f640c04c4d50040480d03a06042045051551360340700c560400c420b5007403416910400f03409000b01c42180800e00b008000c010030702d44031050114400d940050b0b100b4001240340c404640c290162106041c065001355507160b040c444081d01944154940d002d076106070420501c1c01c2504100302c20f04581d0131907004204404c2e101c1c4a1410b10701c0c80120710016520704141e020b080b42050010310f100d1554400100856600c80e0010790340d480d0580b20320b8005920400013600010101d4100404181c40f900300071820244c0ea54060401c0341c3c0c0302481d000018003406ea81c03641d41c0424080c41000514150081299509540200303490792414004d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 82646458 1250 82645208 82645229
    0x2040b25030f0804060e01021602010207060201091509031704080409050708010b030420060a0801050a0803090a17010906020a0302030f0a0b0303180d02040204060c0510060f060e01020a0503032a13 86
    0x1c0601801b40c02078100e000404001319600d2440700e03d035001641e824082a03005100d0b42c10045807003801485020400d90b0081d0580b01491002d00f003060141c0884401101000f44107900ca9601140703a41c0f40c80e000ea4464104103403154244190318080764401043c05040103014401003103001034181c112a04140c001d502c00301200400c0c4500c1c2d400800700100d45401c0301000a1046040c1ea120f00b01c035058407c111090407002e9520030b41140d5901500d020300303604c0100c840041004050582c0301c00307004411a070021801415948504003281c1040c42503c000c00e400008008a800034010007550041c410035040080c07007100b0011a990340640035000550310300c000210760f0284c0c0c80d56516a10103500130030a55503291101030040002c0e18144048800e403051003007201d0003000902803241a511907800301e0102c5407138031004407005214000d0b428198040e04c142140821024401944a180e0202c480da10038080c070311480062507200480030349140001d1101e200c51490302540102220301290381f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 82647708 1250 82646458 82646461
    0x50f0712090503060a0204030611030108030f0705150103030c03020c041e11070b011217030c0d090305090a1e09090203070e0601090815040b0610080c0a110102040b25030f08 76
    0xc058075820800c0e00442c0c2c0c035208100400c003045000303400400030f480c800c02c02032116080720860881d131404280550b02c0030360428000b819084c42d0031005020290701441c00c80300d0640480c9002d0465100a0b00240c00151508011205064040081c0c842108003a10104200118014020429080d101e560407005444605072140e222450003601c1065810502d0340b80355581d0b07030b2602048070120440441c3e165140c80350441680174080148da2107011220b078043d240c00c015407208001441042d5044040c40828030a070080f42e16030a0600c3e010b04980301c0b000c11080d00407961045104c41543c00804a45c1c00c005090740140ca011030301500701e03428802d40e504a0740711180140c0340102550850925407141d0205940c061420f01245030003680520003440c1d05865142c140400111601b80c000042800b031b50100308a524001c00514150b405403a01680950003c10002e0036a40103910003414107602150782403100c0c1c00003c02480801001c40460345800d101e940250950030064014000e1150900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 82648958 1250 82647708 82647743
    0x10c030c0330020a02070e100e0a14040b0402030f0c060f0a0e0d0804180902030606150c030a021b040c2003090a03051e07050a0b09030102070204110a0f050f07 70
    0x2e46045081d0101c050403001d2a064010a034000d402815500c030051154000000e41d00110b00d001900505404100e076050504144030030b5108100a410110141d540705440c1801e80b007030708422405284a80c10701340300390500780109882c0c040d40103409000c0d0b4020b0218404966280000c5492254030180020b490b00c042240c15903039100207816a80c0c11070301404c1d01e0000c0000d1800203100351a9228034420510700c24140041c202c0d062060001c0d0560f000324040350382850024044501d07001c0c0c00c1486072415002c13500c05800c60b00080c00540c05a031003020b41c0c64a11513940100c1170001025a130030030038040c6000c8010015211890703030000c5007202c460b2000c0b085100b4000c9a100d020007904101307031a45d17603242a40ea50719484241d051182c58041d4401100c0d5404560300303040340c60082000f01103d00746850700c2e0181d80410f0710a98590345c2007081c00300507180c034010981a910141d00307450322840f506030081c0450206200395410001e003040341c491014400029240e1407900000c501080c040380e039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 82650208 1250 82648958 82648997
    0x10215060f0a08030403060e010207020d02040504170f0904110c0d0f0c0c0608060108180c040b0a0906030302071701060f03080a2f0705010806030709020c120c1b010c030c03 76
    0x20700240e41c1103144071201140840e0300000600440384590002c0080300e00d4081003034200e0142c130f031340250300842080301c040241c94140c0009400c20f00a415030180d544510f1400c80c800d50004409100410000c14500324602d80f40c4107681c50284102129894880c00030b00e40c5803114440f8030701c0b00512155401c41280c1500c00c075040501d00c0c1e8811002d660340b54a41d807002d0f00452044a00c03500190740400056000d0342c102c43c10720180f004210080c40402000e000b0080504074919005801007a40c60000607440d4050042000541c0250003501c611814161a036802c1d0f12480e0b10f008890307040c410108034061101516100708ea401c80c081548076100c82c642101c00f11003510211004118088240b4600c1c03810350070551041c0c81c510202c8214030f6954005507405407049510740d85c103400049040141018503001011260030301402e980707900e802e00e0300d030140350f400203031404d8020750000c0340c0c0003403813070b20f510002030b59200900b004405081590780050403808c6100d070041c100100360014180100170f0303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 82651458 1250 82650208 82650229
    0x605040935030c040f05101e0e04090c1a0c100b0d0f0501060608010501170c030a090c031505010506030c0901030b01030e1b03120a4109150901021506 66
    0x3440c1e540d50756824010b42020700781e0050300403055616051080055145403071130a1001080260b2264415519010f07608289618856801414003087c1c0c0240c400c6039035184110740340c240c4580440e050132400c1c81240100c40c05801c5c0b140109003000c01a8404000740014000c4d508101d80e0000326050000d42d01154414110813001444901e2090114040202c1900241c1c11b03a84280d0301e001240c0c3c1ea0b08011101d0320765201c2205151503902001c50303030342c10f0820002c5034804242903003c125200d0b16903a0543b100000c3d48103a903008c0324880b07440c1c140100d074040e150040c68200e588604608100041d403109200f044c0a860505a40f006481042e034020f80204200781407400c140c64405060803001c02c80c0d04510384885101c2d00485034110304035184002a14909045580c8844860025401c0d0640101d01280ba00300d05001681701c3c00e1015075030280901039030803808441c603121486501880f804010401d10380e001650203001e8601d00d07982c0082d00d9120202522b180c4801500c3d8100030581c100c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 82652708 1250 82651458 82651553
    0x110a08100917030901020d140c12060a050d080406090f0320010c12020a11030a0506040807060905011109010e0d0314070f08070803041203050f0a0225060c0306050409 73
    0x14044108284c201040d409050000c00100d01404031901d400410f940b0b506023120500c081e00001d01900640c0d541c89100190b00602c041c10700400c3c2d580750800990024044102202c0c5080b00107014480160f101c030218004003003101103984500c9c219a5098100d40d100d900442441d03c030013651043e00d0b80301d80440c94916422401c0b503c14110079200c02500c9810740c24082e40c0006840da0601090301703002075140d1065801c180035020617111a51001039a038084082070f1001a200d00d00a4003040c0c00b8480c0240d141200100107542e11003400000d0602c50328424828440c4040c5003240d40443c1d0045c2d624160802c000c1900e0703075541200d16150301411b031400c102910b07080b00425101c0c01c0200c800000c5006078001c0b24031708695411100b00b24203440c1d085521420345030039200814103500c040d0300a40304107800303521260490008a43d01c12100101070006452490b180e002c40c2e0000e46d00340c42180064682500c060110f1401a01c0d07400c186d503158602c42101001c51100c0f030007910610001c8000e0001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 82653958 1250 82652708 82652753
    0x705010c17090a0e010f050f031002070f0605090109140615100504030c091401150203040b03040201090806070905041a0607080f091c050c0a050904060e070f030302010603110a081009 80
    0x13138540f00c403801529003d024007018185212808203081c60700742c819111202000b402000b400100020110203034001800c2111000c200640220002d00280070305e5120b001c05000000700703401203003494110b9415504203030711560003180900840c010080c050281d00030f4150383c1303880303c8264002c04481034440e542c000303043c22403d02c1c00030501e20000d40103541003421000005038141d0300d601c8002002c41150f5410809039104110802c044039010f006954058014100038101c16540c040d06400c041c0c0031110b02000642101c0c0500c064a018824141e614102d801c10180c40d12015000c00c046100d06078019000c1000429420548000c040403242900c40142c0945002800699008a840c09503103040b111402184180707105400c24001c0c0d6422612300400f0f44a96449a4031501c005000c5012000ba56011307503480401c40e0007a2040d014000c620980c00080d40b280707181800c8039211809038401d44500b01c0c0000400a06200003502c00b1011840c0d00b000604030490b00c1c0984c0d11300030b510700c01140345 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 82655208 1250 82653958 82653979
    0x207050309090c0a021f14090d021209100c06021902060702070815010603020d0e07061d090106050f0c030405130905100902090a0b0112050a0504020a080705010c1709 73
    0x20011025215000c1c0949081240e0744074940c455045025150000e8016402071103043c2c0e68920710f107410030951480501c0011b880c0300d900c1101c204020100c94403211307035010482450f1078550400001c407141101c40b100c6800d00e000d02c0f0001d481100702c204510100100d81c41c0d00da0504c0b9103941101d003c40800c180380c041102c0e42e42d4000e525800e04584580140c09018400a58035402103400c0a212541c244d6030507403a03081007000e40081d040a8030200340b440e80c0705890040708074104208405441c0301e46529002484940c0713258131420032540524007888000e00100920f81d0064141e812a25207041a65160250403242528500403544510380c414003c0140803442d81d03482d030148243d50b0158094031003541c4042c0c51442600d06055000390042c1e04d07500024407481d074a60048034200350500d03000b00c0e41c50444040d1410b03940160780c46061695a1001e20045103009103400d130003820710001810000b0729140c0041c114241e80070300509903002980301c1a410159490403114044001400c00c19003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 82656458 1250 82655208 82655213
    0xd020901140d0b1305040b160318030801050a120803040212160303080106110105090d0f02100603060b0a06021908030403140a020106092d090507050a080309010801060c0201050307030c050c010207 86
    0x40c080f6445114092138068951348900222402040c2c1b0650f001070b1803144a4650180707400e166220000490205036503900c130710a601c2c0c4080a00080c6600940e40c540c010350508042001c90b4409900040a240229400c080000c0058060365801a011168801004401d4882a0404800c90803016001000714030102c200342e04010446d044c0c075250b9890200000c0303885c00c2a8202c45054583c01955408050b40c00c64841c481c0402804120840c4140c45440e1811186501614429001212850f844241344507007403e14541d010010036403407004185500001818665000040501401d5440001300140525010701c10b120f184015044059655240030f040090090840b1300039141610304042100c1110140d24500643c010f520302184501c05c01a407444000801007801d080346c1c58044c0340c60001e0a80d407140b20650050103614050f642e41d55042c0001424410140c110f40c060103040ac24120150341d100040e20307032140079030500003024150001c0079a40c0f4000d011584500d9800001c21008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 82657708 1250 82656458 82656461
    0x209030313140406060e0d0c0f0b0405150a08011206020f0406030509070906050109090e070801151403011103060d0212010c200a0308041509060f050402100905060d020901140d 77
    0x4507140719980d2501c0301241c4040100707070b078102e20410b03000404240e00b0321b181c1d15000c43c0d510328451280f09048600e82d81c82d40e4000c0d040146074081c08403110085010002410031603420603c494072404c06a01d40f00d040e110103806000c040c0688103070b0040c540e17420b07001c05c04250f04640302d07684044142501c80380e4991005000e054121050000742c0500100001e04070228005c0c401541d005031a500342e02400c2181481c0180003010000701c1c58417a2940c0011410070a114074610b2520000e09422903904007140c43e8a1642428084d500076071402000e0394100700c0e24010b580c0c000204807420240c410310741c00010500203000741003000551038500c00c241144d4000301c08044013649082030b81c0c452034901c40c0c401c3d180d0050f10340c05004070f580b010018001420445581c1d901203280200011401225220941154284510008a190390b842404103500d0401d4010f9419079680c5044500141810302003445809600d100c003034025004104220140e008148071000c1400600c2819210301d07521a0110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 82658958 1250 82657708 82657747
    0xc01021611040c020309040c0302040f030f02090c09010905040e0a050709060f0f050603130f0b1006030f050402030c040b03010f05090102180108070906081509041203390302090303 79
    0xa030030346a010703200d2815007054000d020858032603401441c107010441007803202501d10031010800700b6908000200740d0740f48005103240036600030070502e5100019441801100c0c80041c260b0302d1820028418404160b92019605003524000c1e900440c01034000006603260030702490700248a4000e039200420300c541c16502071001c4842c4650030100e8241d45012180f03001d1180d000305500f21900f04005100b5280c6111105085440746040c800b80078001d46940c1540c550581d81a030100c20a001c082044681c140078010645648000070003040c1040d0b40000e95030301c0c4003000c03d40140d0300d40c4000100f5075420360084c100100d50f01e07010303c000e18114190b02d000350b125460501d011468060035003002d502c103107201d0788a5034194803410100d6042540680b000c2c00300405408010029004042d900c1d110403031402d004502c14007096007000c20240010f000d4840c21a4010083c10380d0b280b00600408141c4c0b4007400c10b00c40180c102a2003541020202c001e1712940e40255014400000c0300044a0340403104403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 82660208 1250 82658958 82658963
    0x20a020c0102010b010e031e031c0203060f0a150c11040c0e04050a050408031506042301030615020703030e0307240e040221070c0b070306080708010e120a050c010216 73
    0x81014100c40001900c05190701b6140540541c1300c0d40003040f02d1050354030701441c004100822030303003030041c0c4802d031951001140c200d5125003a004810301c47c1600340340c1031001c00c1001c22282001c0403401c00020a803120140d1111720200301c00503250308203022404010410f0907402800500243d00961400b0b0128842c0400c168084e91802c00000e04091452090ba030285a11002c29031440e140c080d80c00c00b4541045468540c804820080012000010885200030a10714000d10301000340030b40000d022500107a01c1840c0401c2c0741d01481c00c240381d01050610907258141801c204540c00c22000c2840c04007a070308510001801d40320310a407041114140c1e907070540c166a8070710324a40d41f9078060000b45e001e100800040389030090307240320080301c52404040d070049083c54400e07054107035070300c80c0b00c9080005c0c0d42000c04250307240c00034066044140100c0014000a0000f80a9007200c50081c50707813210485001c07011a400800c5022003107120380d04843e0140c44c0c0e80b00079915414003100300c200100680204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 82661458 1250 82660208 82660211
    0xa060e03060f16050a021614030105060d02060f0a030605030d020109050d09080d0c060b04090b0a0e06040803010317070c0e2707090203060a0306090507031e110d15020a020c010201 79
    0xb1085601c002d00310380310b0420541c400c0c1118000400a4902c0d800803601c2800f0350095030386560b1110340070744c40d078002803104028404240342e0000c07e06003100c1c0040c01c190f0099001e60750440241e111f103400c40780c4005541c200c1c0d41c0d03540800f0000310000d04660300034030340c140642c200c2003020a90540102c03694500400545001c1030342083d06564038045803180114941041540241c0c0ca40648100600103000d01001f00714100b142000400311400316100305c85c2400303d0000c0c02110340f40d5100301300340081e29000801c1c0a00306902d036080b02c1e0105100052507042e40c000252144502803081d10095a480440c540c1202d886141c201003601040b41c820710030448131400710442c0010341c040c00c108280d148025100c1181003450010295000070180358200841a0000001540d98031400a51500850141103500d04500c0c0c0f1054684400c0c01024841e00543c8402011a8a4600f003020803c012203a00599442ca440c1c09466402224003803941d107440840c103c5522900070803500a494800d900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 82662708 1250 82661458 82661461
    0x905071403160f18020919030b0901140406020702040e2b0813140c1306030b060604030b0703050a11070b0f0c0301080c1905030609100b03070608040f02040603020a060e0306 76
    0x300c2d0300110258031950383d04140340e0008100140940740a41102450340c0e0000d0710304021100030446072020519548001d6001804c20028040c010344043c0c0c1000c04030009000e020707080c2c2c0b44800300300009031000e400964006a008110741e20b40e80001e050308480c10996215480914141503400100e481074103107640c07507a05001419100d50180ca100b510f0303064400c111401562200180d80d10006c040b0b08451182c0311450300e00755540190903031010700702c80c80031548038150300d04214a0f00c00981a50f00984040c4410f20000314410011540584c6a10700043c01c0c0c0c0e600c00248001e400c50240e205210f9200068841c14420708113251803103451a0445e2401c60740f00d800320001c40b07210912a0030856000798403000150710f060f01e05c000f18030b4a181000c14a0b6911140001d00301042691403c4450788032240e0515183c4540c010b200b924403045010b441c1140c82c00c5005400807070010402012142501d014804541d9643d101c03801442c0c01a1078459143d840d114090700d0601180c1b04903109100f02e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 82663958 1250 82662708 82662733
    0x8010509010b0108180a02060f0d150609030321021602030c0f0a06030c0e060406051207140a0e01050c0f010b030f0129010c06020d020306040b01020114190905071403 73
    0x540c55000406a49401541e59008a415001401580340d8417850003001e002c03402603a105c0b0003604265021a000b180d60304030400512046800c0c20302545040c0ca00c60308200541500280741c00102c0c0d401d410b040252000301d0100c103000d00d2400200404261000c104d15140d14009484281e07903034803e80031a807458440c00100000c807440865540e034030030340c10802032018070b00c01e40210810401c54106080f17442852400180c1641040e0042d200081011908403166401034038a40d8001449003444040f50f110141d032201c20744101d280308000c7c001995104515a4420001c03111000000130580d510b0005008040c1d028000110720243f083c4681c0c58050112507062042c80380ca0151405500f210300501d440b94102c11000380d0600d410b000c021404080821143d000070301c04501d811100595a15000c800c0004480b0070708502c0303045a00d00403c3e8406000403480740c6401a020f841510b0312680084a10809069007081c02046c9026944002405401c0c0c1880c0d086400c80440030759040380d080302c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 82665208 1250 82663958 82663961
    0x901060503060d11030106080609150c0c28020d030903060c050c030405040b0103020f0304050c011701081905010e0a050109060b04090c0b030a0213060206040201030c03020310170a020301090c0801050901 89
    0x103480d5141e0000fa4481c20100007103003000050386480d0060700204003940d5540185040010880e6070101542003205260300001d0112000c590107050701e0112400c080d10600650b03916a00716500c0340b0a02c011a050400021940c02c122000b80d17401000c0d02c1c10b1404610b0001c006110902c405c40303116051544102095000f44107440515000301c0085080c01d00d04810800640f107c5000d10b41803690810500c541c0302c00c0c5c1d4000758820360144004260302c1500310300041079410380402d20003000d19a440107204c0380d000030540c00d40c200002d0924035080701d1941017403401001250070051543c805c24146000700b200c103400044002d8095070041115043e944148802c1d6000031070010311405090310188410f8072500051030300030400d17000060404c5400703901940c55040350742001c000f6a0106041008541c0e15024000da02c004900d019810f5041c040c84020954200b40110264081500d61982044c0410030170a800243c00034001e201d24103050500c4c2c2c01804490050120329401c00c0c0c00200c414605 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 82666458 1250 82665208 82665211
    0x70501020f030d020f0f1306090b0306060a08070e121b030a050a200306040b01050f0f1e150406080403111b040908070f030509010e090c03070f1b060b0901060503 71
    0x241d8010b1460000b10403503110095002151541113000c062140c4c01801000e200941a032045a6590106c1301e420541c01034515201d69100c04101407080040020581380e510545003100740b281000005034451004c1940e203805020004d075080f40c4c02c110302c0c0325600000240300144c1c1c2c036003010f9101b01440c20030500d41c8031015203c024205920041000c000900050020104540a090034030b441508050001c0d081000039681582d0252180d00140264a4101011120a4411030b201e003468140325000c640e1080754030100c03413025404007140103000d0310794003041141c3d0a44046d007950390355166103015000b00420b8609a000590501200d811036800183c40c20b115031460b91409480701c2c5407810800601401d160440307070824107001010001e0101048400c00e9071003a01d8050700c805805000400145e4000103c40c0b140c00c0c040140100080c400048075040381c51858a02056100004152140741c882d5920400c00d80045400307009101e40d03a88081d2020310b00f1142c20600c0c1e40c6e90f00048526020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 82667708 1250 82666458 82666483
    0x1407021f03020d09030e28030305090307090c0c03080c0c0d050d0f05040f11030a050705360402010810050d020616020d05060a20031302031906050a05090102030c0a0c030e1f0207050102 81
    0x45501f0280b0100b070298014001aa000401b1508015182c02c50329050b580000c0e0030341c0115414801b16000c05400040071680405070000d1182000c44c3ea140051b03031990061064014000001450850750409400c03101642a0b10001032000d41040c1c80d002c0d01b01a140b00003641c150b603250401c9a41d9180120b00700c0e103181d030080000c0c003c090600d001c1081d003e1448009000e0902d4031500c0e211050451241e00385440106404807100b07242500000d404071000500d8004c4000039540280242d507a81070aa00d00700d5015550951240c01f5490b003590a038021a40280d0702c10742ca049060200b0034001081032143c404403409010455059410100c0701d0f14a06200356145020301c00507200301c8181030030065407030005003100d1741c00c000c0d100c2c10809a0392341c0009a0700c46440d90304212868409024540c0c004c21320000031840c515000000640074001c4903d03000c1004180c00110f0203140c825003c1d4030f04040000c007403109d02211480c1360740305004550a420b001d40a00c42d00040e0541c001700d0f1086903c40d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 82668958 1250 82667708 82667779
    0xe01090804090507050405040603060c0e010e0d0f0804030c080a050f0303060a0b03040302101e060b0322050325020f0f01021c020f0304030c05011407021f03020d09030e 74
    0x5081150b01c402800004061108001c010710001900d640c0728040c0e1002503000d14000501903980350001807400310080b005505028040182014079101e603503004d4201e94111060134002651481c01d848035204552000e010014104000304a80394080f9800001030701c42c1088842d00384c001c00044d9142d002c101c5149602060b0f00d10100720140041000b158042d01c42e1050701d803d640c0c501c010740111540d1540c080003416080148891203211072040c007000e00a000101421807078603065494501180c1d9070f9200f25920a42101002c0060400640e49801300c140d41034000a20000f50740e036100c01da04842a4400c45020503808010700f0620b400841c840010383c0034001d02840d06195800260031421303010114443e200d0280d1500f0824005080614031610002c00c08d5445e000005040000c0341501ea1035801081003800c0050703980349001516145a8282c500494020303400c1a00280285961150482d003010386000415a1100c619600b180c1c0407203004040c00400020f40c5503a0b21101e065072032a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 82670208 1250 82668958 82668967
    0x30a08100e070804020409052a0909030906130b030403020c04060504050f06040e0a061b03060e01080a0f02010c150603060f090f020f0f12071d090c090c21010302040e010908 76
    0xc0d8403c198031035010780043d00104080031140e07101c515090540320403501c1040304402603d041c8180d10143d17400d045040f030b500c24a5041c049035441c0c07a4410664602c0c401c80c000290810413529a45d01100140707140641e880e00da2038941001380d29504003c8a45104130f10b4080c0200c1ea034a000e108440c090000c1e5010030340583d031001d00303000c010101d00001d00c007103224044075540080d49a000f428511011030300c42117103010305154050103845035900458200c05500d401400a000d000130203034801d40c0c215904c2d0b0b0b940081030006072001d104000b00031b00008280e911650141d0196000041104d100c0c1c0300420064117410074035811107188500c01003107115030360841805494021ba0080804200038500e90000000000081124868041c06c0c0c41580002e1400c2054040858080400c442d10105490300341c600f0b45400c603260b00c4000d4090f813045001d2008078007104140c0007070340c4000c090125501c2800401010715400080309120481c42541031100c0e03c50101030600a07240501d07480700e4a1401d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 82671458 1250 82670208 82670221
    0xa0b07060b01050d021317032d1c0507120203070504050d050304091d060610051918080313090c0c02130b06030a02040e060111030307140405060705030a08100e 70
    0xd40329003458141004002d021180d40d8450905c0104500c807545054a107440f89002c1740400304108240307a02c4003542080c0924103c9840c42c0410107a082d001504520000741000c109d000540070342c1c100744d0040815400c1d02c0e4608480c0e548a14001c481c5911040070841c8802d0f651426072100b00d0720280000c3c800e120401c02e80c10030190840c413580c031034820340e070820362120044812541c204822030801000403802000041d1300b40515608407400307860003001d40d522004003420301d01c60380300e0109807221603001d0003001c80e214030f42408004400c01c00c00040380f682e40803e695280c0000c0e0080410000f070345070000d201019407140a908008544035200a06104e8081104901006011183ca1500c0e0041d01410744e60301c00003940f040722035200050722a8204003880c14042e400800310340c1402045102d0f84400d000000980c1d44c445041e2a24a0a04000d040d04c181c080c0503503440303075030407400c0401c02d0750030000d02201404405855a541c0401e650720381aa2030b203151201d04c0303010704003240c2c0c0021890 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 82672708 1250 82671458 82671461
    0x3050729011d2502070306020a210506060a0f030905010905070911031303050906120432060a151d0901180f06020306041e0515030d17090a05060405010b010e0a0b0706 73
    0x60030550f50060307031183e59603034958906136881030801e103002502c44030315011140c00d4041c5840750490082c0c010030182c5090300110351035101c0d2012031020301c441c00c40c1c407082c072610a0300001c984941c1f010080c0b00d42c442c03501d04280c0e00d5409019640e904c40c200020702c00000004400c0c1da104100407114521900150349059506070311010006403c0003042024801080449100e5409280f08414691002382803d0803520586202900c072454018040480c0850110015400350401e094240000e80f001c804211a401c0009030340c01070500c00c2c003841c02040b070319034001000361041c076002d0b009205441c081c69407411207000b0820700400c051440344c14500130800c185c3c0991380c8204040c000080c60f0005e039a403c107100c80000001c0744030b02c0d1180c2c03c010f02494209003a4045410940050030562207241014244c0f01d030800c0004074640318280001d140560030080301182c10340003400c2d12090f041909116001e031140903030460210340000947c180900b0595206400c460390804402d0510000d642e5040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 82673958 1250 82672708 82672771
    0x60d02030619060e0106080a0f0204120b1005040c05070b090a0201021515040501080a2a0b0304060b0d03170906130308150301020d1a0402030103020303040303050729011d 75
    0x1051aa2483c0c041080349604240d40c0c0645011b44070300000e071030203e6080c41515580d0101d811800d0040c4800c00640b242144200055680105500300640c0c60240c4050900c8180d070010341d22900344034516044a0b0810300400307c003400b4200206450760b684070107640d00c43c000400280180e200c4200f1318480c000a0510a420044088040881441843c0082d0a0380d000380c001000d00c0e00104101c00c20041c4d50214045101c1c000035444003901d0520b090703118400300b94403400c8a00f94000000400b04245035020f10014840101052940070490070000d244680440380540c1d0f10070320b0b60100c0d01114000401070b1241c070803408000219551503600f00da652102402da022003410b0245040c405541c280083c2400c201001d00004010b04002c4012017001c1c441000940100d20402c01407000d40c0b40071084500380c03609410910341d509810700c2e003414840c3c3c202c04c018018490161341c4a240c1c0c802081d1281c102d9008003102143d04d0b13010300e04c4407400c410903035420650415240c00e210242c0e4103c414203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 82675208 1250 82673958 82674001
    0x60a02060f0a0f090c050102010f050f0109110c01110405030708070b0d02070f140105070f050405060706020708041205060f01060e0d1b080a12110a03050405010c0f020301090303050a05060d020306 86
    0x1c03d81000c2e1280c44800d44680a60846050700765401c00d10095038240710b40005038914400078421803e090103000007a503018020000d03819103030354902d42113190b010103c4000117034800080000000d83d50074085160068002d5512a001d04d520010b00c089001078007000341c60035210954074016111010500941c804501140c202120520305004100421807048074424a14004a21454410001002d0100501c00d10051102c14131050055407039610544035110b6008400680d6a442c5041801d11802a6441910b100c10400a80c02c10481c0108045000780900c203a08102a43c80d003800755802e0005010300f0f50007800440400c0085051903030701f0404800e8114100d005280c4440700315050441c01c4105542018001548030f20031640329510044182081001c6c0c803010701141c0d0000e080c0d10691081604120b04005541c0901c1224944524031550080081004142614014016150031500d1617801b500e48000a803150070900300001d101c5500601400306541c9100c02900d02c60f00b188400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 82676458 1250 82675208 82675211
    0x50307091a132304020d0e030c0a060b0a0305030301090504031106090c010306063b0d05010b0306060f0a030b06010201020f07030c050105010e060d0b041b0608190606050d02090f0901140906060a02060f0a 89
    0x4000c0040b1f0280020010007c0c01009407168020130304044c4c0039a0020318445024440103501000480e401000340ca043d12407441000c501c075100d600701210b00c0310795015086842c1c01440e060002c00d400004144e103000d4030a0301d007400213903520801920003589840601c3c4080705104520351103100307018100040703803101e03025505000584402040f86d20489140469140e9134500705102c00d40780800c078003603006204039624175201c400e92005c9082e659161100400c0c0c007007030320040f43c5103038000c1d0180da4034100344107001503c450311801c004021003084030054039103510b050004030b100240b500a1610030072015240504100403645c5500c080b000041c010345028203145421807a00c041030040d10020030701951940001d00f40410528028094000395242c540d01c1c01c0c404002c929000000c2e25040300c4804030058852024202051000c040c0542003580582c0d00d40000c0f803000e800c40300808014006444c7d41d0841c0d45c500303041c0700740c41c41014100c002581c04080010500f015030201c1c2a03200813890070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 82677708 1250 82676458 82676471
    0x1115150301110f0d060909030c080c1f050a0f15150201091e0209010803090f041a030f010608010c0c021804080c0a0f11030a030c0201050307091a132304020d 69
    0xb581aa0b90030500b25005002d600140c00d13221040d4078000c0c4006042400c0007000750003020b59003c3c8c1a5001c89000a01c0c1042c0401c25200c041000c0c8a4094100d6003110a900f11003081d41c540001400100c07080c1c10b81c9454241442141e52a074032030b203259044c0d01a90700b031941e41840002c503400320b440d005a0045649684107400007079051503c02c0c1c5540241d40260f1004c48207841000850b2005030886521980b044c03081032250b607640c1041002daa4819100002c045c45006404030548038035480d141e400d0b118050800300741c0d0105500090488507084020072141d6910041101d80e00c85210000e503002403403960700150768510b40e92403504948a509010b141c00010202103007403000214040d10001994141e00d0140181c048c56001d00310800c602400850720035035809426080c1082d000780c1040008000204e41c503019003842d6000e0801000314404c0051101154503090f40144845820540350000010388201c4281c0c160307100d81d03007508a0421001d54002440025000700000a031101c1e16803c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 82678958 1250 82677708 82677731
    0x613110c010e0c0a0506071109070c0b070f020705030c06041a091201050403020c0901030f0b06210a02030c010903230a0c08060f0108030a0c030516050d020d1115150301 74
    0x300d040c070b07081d08020160224401103400c0082e5850241e100318000c0200708a4800020740e1841d1800030740324222036010980e200c00f0b0048416980110006010700720781014010329039002045403000b820345034200c1d400380b5110401d142e114500ca40ba95908180705100601a051032000030700384461081c2410390404204000140244032056070b09000d0340d6598050000f40360b418455804540b10540d08413100b549035946e440744541c61034001420540316130010448540e20f1510000103542000c1c4441110039000c40e401d901c840c02000100c0c40f074850301446110380e502030b200c1c010849802c08075413103100c034050408d4407845004217052050390081c0402c010000b851190047c000d000908020011842c014840303414070041a000840305920600c85200300f164001141c14110360b044c0340481d201c4001083c1020002d8000000608900807454030b44c28a690004015052410b60340c0c1c3c0340358200015409039203400395800c210811ba54042c00040c040030b035140c0e40c2201e120303018000081d50309040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 82680208 1250 82678958 82678961
    0x30109080f071707030e12010f060b18101e020a05030d0203060108100302060f070f0503040605070218060109030305091906020d0215060a09110408030f0a170613110c01 74
    0x2040141610310100b2400c00f0301241e51242c07460070081100940c5402e1041d203003d486d15100100b00c46c401ca89a04030306c62401e1013900309002041c50741900f884215220100072030b15400501c1c00d0b810340c0848100c0405a4544840034403200045502d550805042c14104030072412090200e4500f0b602c1904c40c1c100000f807042000300407031441c2c690010380720b042101c001440e40401900d11805450f241c80280050b17a03820003140c502802c11103901ea0344001500d441504e09000082c0a0001d010100d40018031640000c02005000d00c215284055102c600300440010f04003a00e000d400030741110403d00003e17001384020414014000d02042c0e401c80103007807000c1070a880c0c0d0406001a00154010070178640c0400c100c5441141c00703843c50881340b401c0008035041413101e105e20346045844000340380302542c80000300c9002d05144c10a0b40da403020001d0018a0903481000f1081c00180f1001113000d800244d034201d10701601005100380b4055002c40c80a0001d0624000392018034070040104500c00d240c04d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 82681458 1250 82680208 82680217
    0xb01021207080406081608070f0306050406030c03060506091005040506040914070513020a0e06070f020a030503130b0702010e1905030d080105040c080709150212070308040b0105011407080903010908 87
    0x140b0030381a507880c14620001c008480103041681c94016950210031300380c0c2c210f412030f0ba1121080c9080c0c07040b190707405012000303085147c0c05150424074001d004014000340e01981001d6034015034003400162600c109020b03005400300e5100c016002c0c0c0b2a41400145071030382003d41c1104000f00b000c240c50086854000c0c50301d17820140720081350b100d200100040d00344420300c8035655408510442c14180d02c004098514200809205c1c4540c2c0002110400c1040c080c50201d1420b4020b0b000d16041c40d1a490610359903448009a5416803c1108000a0054480c01242c1080e03906a5031819940f4554003401904c1180f10f048804040250702c0218031503c04108612140620f6901d03001154944820311084880205a08003009841020009040d403c4400207040315803002e84c1000041d88070108a049c00c01003044144c0c0454002500382c1803540c0088502c0c0541d000c0d0301032000d00c0e40d890300117482c038891400c031814281400b40000008100c0b4600034006481d405800072620403507070b5940b91001e034003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 82682708 1250 82681458 82681463
    0x7090b0a1d061008070e0f190b0a0207080d0f030f0b040e01090b0901140103150207050304090c030b1002060606071a07020a031b08040504051906080f0c010903020d02040b01021207 79
    0x149010410b1038035104620000c000f16500b407102203414a0f0800404481607900329030302509040c2c40c2800262203641007078050984040075400d50545509100039960f0042d00d051006100e6640046501304010403103500081848c0c0f11a151404130160960140c020103180384241a902c040c02d001a440ba4010b040b11000c4045c00002d2441051414942c00e01002d809540745170b03d007034480c061881742061054103598101c0c1001c80d000001c0c003142d0019104544c0f0080660002240000d005003981c5c1003c5030b00d80c850348081c0100580101480787c03040c1c0050300d1000580c007050101c0e450b0708185005141700c90040d24018100f083c0070500205040081c4c40300b400581c0900f0404043c15030110f4042114004251468854040d50719000c180303000360301460740304581d51004550b150308032010313a0341102c0e0a01000e12246da41c6640da551258201218580c081c00340c08100007080d84110f5148040d281c3c001c1402c0110f008980a220040010700511410352040c404000c030f007059120042c110161 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 82683958 1250 82682708 82682759
    0x90406060f030c030209150f0d0906060302010f020109030801060509030f251505030114060c01140601020714060301180207080310080d080c0a0815060705060115020c0307090b0a 78
    0x201d4048010200e071181810070042510600181505544100607400034809490f9481c0d220346155110071101d100d62201c0084c26407070b02c0c540b8005c00201d0740140b000c0ba0f000340c8806010110030704080e802d840403a100140060541e400521540e0b0050340500070300100076040342e4000c64800b0405241c20181c030145d00c601220380000c102c4a0428810080140c50140c001d148100c400f000c0107401404180224a411364051084040ca5250042a22804400c1d10001c0c8a0030698003003129480905449180c01030146180114142c0c10304107000f0490b64000d0407080c0b03160310f400c42c00f40070303198007014405540d6020000c04002ca0120710113135020390044111000342500d07100c1e2191520483d03203008418003c24004002d403001c0104140e822085507070420301c41941d00c013408809520443c043c0c040e8095404a81c10090010000e0040e0689440710904005940807003816a607603801c0b046615407691003600c00f803201c584039800004120501074407140720030b07032950744104004031038882490a49 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 82685208 1250 82683958 82683977
    0x301050405010506040614030c0d0c0305090c0a0501090302010c020406170313050109061706130204060e1e06091201060b030403030c02010c0e0609061308010e060717010803040e0c09040606 83
    0x61a00744101030040c0411900a46418640140640781140003180c45810781c0300031000401c05017284049500302c0700403402c10425060b40c480c001d401414191b41b401154840c142030a01c01d030408103c40c5045d130b00d05071500d0351b41d83d16541c01100c0304524450300b00d0b02b040e11080e000424084c6101e00d1002109040c0280d07441d500010030261042d08903500c00d07030420000c040100702954000c04003003407200d216540c03014660341e480c01080d2403d0084400c207401503c00140004c055620030503180140760f0884071809580c1c04151004074a42d000c00140d588490100700c0d10400e841d050880d402d00c132000c10000310f100c1e65030b0071000d4000d41084400f6408243c6580c40d0301400360782071203885541255800c14039000200c075000318840b401244803940c0039003000100851203081401350032000b014418024802c0080c209603503512440180c4080021610604000f00c030b401007520024140e0300301000840c1850701e000808400040c0142a82d543d401c01085103c60740e4690f80202c1029010584400805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 82686458 1250 82685208 82685219
    0x1006060807050307050d0513051b01110604050309010f1215090e1f0e120f040806060307030f020103090f12020109030807020106030807080c150901091208040308040b0c0409020403080301 82
    0x11031030040141d4104a401c1081122068020068a14181240340001000d0740c1c2c05202e40b00d80304007404040d00500c0789004501ca28040c0c0305000199000c01e0b40d074084c6003908412200e5680300242c0d40240903800c14030854401d940700d01c120a01103030031490502c64507a01c0f000440c5c1141e1040007180491250b8160034805a0503500540d21169190b40c01000d4900310b18220020051105922124058481101c5e840c840c030100414030f06069507d01e40c0d03580c0d08074441542026131240c40b032880380c1e0186c070000071a6494080340307034011a45c100fa0172a101c5402940114001c29071142d0807516800b0010402d0b0202d0300c580b0481a081010303400004540809007000b50034094000e000d44110380c180b0005200042402c01a81c1e01998480c4015840306100d41826003007d003e40d08400340c100301e0b0820410040c005422810001340111038a80000b11540c000b21480141180c010b8040b82806010400054564400310f40c06104904c586080580310003024081e0707400307648159a5900040300503c507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 82687708 1250 82686458 82686467
    0x110301030b090114040b0f09030c0f0c04060b03010501020d030209150408060703060915061409030f03040f0602030918150910081902090c0a05090d0609050d1812030c05100606 77
    0x1120700c004c004c0b400c11807400303035941c10b074126000345940219681031011921850040041c1c0c4c500c40041025200707451401440740356150015100e1520a40c100040080c040802d8811281a0340701a4041c044246000300c0660203580030800795600245010342901c000c0d40e07510060005070231068003500342da00f0034040017801d542003a0000c0c010705262100201140d5506030131042203404c030341040741d4095043c8561001e1f42c0141c2c0700389901400303459118507007900301200510986a0861000c0310003038a44d00200d0383e0380900c0c0300d007541000d944015068000001c5002c145e10810104c440c0c0f06c550310784030104021007010769008020000c0801c050080701814080741c100e03401400c4120303006440940000c1c1480c1c00c050203030308480e0310000b10b02e000d0390b00c20011070340e03410340161051003190303a5460302e1401840310080c01c1c0d85a01803151010b009601c5007c0030f000300c0c9526408400b1030b6040c10161282003002d00e008505105844ae00b2100281050040c09008041c02c0c0c1c0000d842441c1c030b5030190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 82688958 1250 82687708 82687721
    0xa06030b0117010f05010e04020712020a200303030402150d0c050310051806010302070302070803030f040c0605031009111b030307030e0a0506010e040c090e10060501090e1603110301030b0901 84
    0x11a0b81c0c407860051080e0040303102c26800b01c42d82480c001c41c911a0200125000344a42032020f440b4442d04500d100d1b00503000614003001d14410031800c2941c03d414031507000809441e03082254141c0081001c1405441c003001c02e507480e103582d01003442c50319400740e24000840e0040d4031443d0204901004004a03410b00d48401001801305981c03441c4241c0b030449020844080050403a4107256002c00d041c0c040c18420403004000c0c029400442e540c0e030601003160705200408560440321200c031004c001c6071075403181003502d008540b000b80c140b02503403c0115041c040c001c01c0f214407102543c103120003095607440105250101710018059a03480c10082c0e03000301901d607045012a200c2e440250000001039000540d541100c00c20010b80100762120315041440e400c1680c003001a85007809503002641201103174280421404080401c001542d4600564110752584540c400b00c0304544001640a60342142400341c0007035070710380081c00e40e048400440c0c1070740003070300103840402754030040107052142403017001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 82690208 1250 82688958 82688987
    0x13060b060405010813060209062205040b01020c0409050c0604030f050d0c0816080f0a080a06080d021024060206010e330102011104080a0b0a05100b030c07020a06030b01 74
    0x3840e042c200310001e001100c000c0d042c1c400c640c0503084017a003030100c00d40c107840c0e05c00300003400c4943da16800c2c40e11424000c062140704010381051240046d031490030303100360a505001078016055805000003000010701100f24180e40c5e901492140d07403078a58860300284082d40c880e05960108014a050451801008844034004e01c5034014a1902152000b001d45504812503840c1001e608a01d250848081c0a404668200403001042044515420588207403082c1f8030710b00708120240c0d40c2c102055031081318070f207000e015030030608100d445118140c010ba69111540540120700c1c0e500d190802e802198a42c0c0310702c006821010042c04185803081c01c01c0c1e04500c4140844851450726640d20000303890301c142048030110b6400e01075085034000e403c8541101224103056882e00d82d030f10b102d075440740c0180c1011102c0701000320020705007001d24441e072400740c0c503000080c1c03c07020306141250403554405040003c84031014441c0e41c0040c1d44c0c07203e00401520295070041980740c040400580380106c1020075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 82691458 1250 82690208 82690219
    0xb0703090905160810050603130606150815090705031f050d0506010611030702060f0c0c090a060f062111040806010603150b18130b041a030c01261e13060b 68
    0x400c0306642d0042a01d411100d0405440c9c800c11880c640701008040c541c0c8032891103a40050000b034420713004103140e449101c0d84241030a92450107000c105400c0e04c2100d04002207038080c008206421454030f000c0c1c08030001040806241d6403601c0001e100007915010889460740803000500c40329074002d40d07080c44080c000b8000d50034200e85500280c00d90250649500f03804001068031692400304200711104000090800c2c801e9050092203d0003900843c051580c18441d1860001041c070301c02c0403168103018805071615180402e00482a01905c0e4919440108120501000c03650070018000b45000741440c0d03c00240300b00d11120200801401e070303405045020000c0c068501c1c00303000c14080712030500301111081c0091012806006c000c14054200a400900d03180e14074006030341180240110010481c112001c3c0f018000044a60b0307500f030113103000038031600444443e124050341c0415403c0551100c1d00c000c4150b054003a910524800c58000040411041c0400207108251184080e9150203449 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 82692708 1250 82691458 82691491
    0x50d0306050d030f0c030e040f090203010c0504050607060e01091b0303020613150b190303020a0c0f030c090903030b060d150501031a0d0203010b0301020406050a120c090b07030909051608 82
    0x5004d800580400e2600d4284804044803c5c2003501c0f84012038254803005001b040204012000403005000700402280039610700915040454020000d540c105c40f00200454500309941d505d00c0b01030010600b84080564880c1c0c0250000740c2e8500e258900340c502c0a040401c00303442c6080092801c10054030781c034844650369101d04042400420418452088860042007442401c80480ca580101550181c607044443d14040201030340030135080c5013540505580380c800303a218160422084041e04c401020350840440802000305c0940040d402170313000741000165203644001188041c0d00200340b809019540344c40f000d56a0300c0c50b80105028190a1904012009107851714840c17000200c0c40c182e01c075510607800d440440d0f0f03094001141713224001e8001d549896440d00041c0a60b08900c01c3c10340071441c0540c040019030400d202c0c04428407003607510810031a18000c003400555101c140c094040161042000c103220400e4040c0714000c01400c0c0303480b4210100c0500c0242440700203081c6501c2d5080110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 82693958 1250 82692708 82692713
    0xa0c0c0210081803030a02040303080105030304050d120e062a0d02060a090c05180f01240807030e1e0d020601030c1512060905011706040b040308090106080a050d0306050d 75
    0x2248010105030805034083e8580030681d880c008800c090043e400d03c000010003058600f20303005002100d02c42d4032141c4c01c40e40c0f036504050700da000b240100341c2c22503003420034500400d0720b4920108445049003461f0000700d40d000e020a0b1558019001060301280c442200c0803051041c2c030702400e802c01c41030b0103018020340d02c040003520364030b010304178002d12500d500b11003051000d8010401e00030b0034014070792090300c1d6181c4000304443c141107800d4843c004185d4000a0250000410400303090240c03e48000d140c0410001a01e000300040c0140041668501441d82a10020400b015071040d206d164030485102c4000d44a16040b4494400030454001200410005000c1011242580d41c5031200012100324410111050f13081110a441c0e440e0409400180055555001d00d06a40c5504d0412420611907207002d0f030b8a18040d82e0003400d102454000401180c1301d2507400e5000342110300085840303a595100e56250011810b400d0350150480705e41541105d400d4400c2c4002040c0c00c0c0c43c110301d101d1a54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 82695208 1250 82693958 82693969
    0x7060615030207171b06040501050f01120308040b0c0705031318110301090e0f07030b1f180509010b0604090b09010801090302071205010204050a1203020105010609050d060e01020f070b0a0c0c02 85
    0x480c80e51034410700101c2c441508210003128034180d01a180221b8443e440c007414250302030301080d00c022458a20301e030004036061081d03040104995406d61039801c22622165162469454000c15074181c48500780b004100007881840145010a885c5040201c8103082c05902544958681031501146203007200c4c00502c1030004041d2070440382002c1c000640f08041c000190300b00780101440f04028010780c10b021041000d50030405004088035100800d02c401c00317601c3c909501145004140010103400c4c6c0008001c803594204551200310b8070700100d007001e0154080b072280c2c0c006e0f40114541a484004c82d036803038101824101e0041003114002e000510007501d001e910350425006141701407183d50302d0701c0144a001d40440c0c0091001030b0600501551310a06d81400040c0c8801c00c0f0015400d03d000003410920445e02c0c3c4095600040c50220400601c0d80c0b00c10003020040c502440554087c0800d010800d0620007030701200e8060449040701303150504c1c00308101c07240000d80c101840350012142c409030301c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 82696458 1250 82695208 82695233
    0x218030123040501060302040207080406080105040c0801030b04050a0507080c03010b04020a09050d0c150f030c02010e0705010e0a090606090501120603050a06050402060c0a200a05090c0a050408010207060615030207 94
    0x407803040d21a1511542000b901402503508040e42240c0001141030402091030020f2044602c1c0d80d07514521070f45c0b50010001910b00e825880c00018030060700504c0403e41c0f0000040e0410310880840300c07021041e075900d50402156a02c44400c2d50804880300721141028094094014402c5400310316103200c58102400d11000c40c02039a015080e000402001c10010a109101411201c5000540d11f94480320040c602000c0200050001c0c0c00c0400141c80c40b0b0050190700c3c1c42c600b0100280c08590308107001151400c041c1c401c040d07030043d20020000b4109549204103000303040540d5520074454104000900001c5c03160445407a401d1404c2002c00c0400c40116140f50050b030f001c2c1001c80c0e40d0f1a0780c00024114007800b1081d40360b6001c1c00542000304408201001c43c58200390344207060001c86242084460031042c42000d0b0000d00318000210400b0340d43d0020178048400d420110b0809807150025800c982084400f15402c55440a040c44140c41c2c0703800300c00c3d05090500c0c065141c2203080d500d1400e05d14a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 82697708 1250 82696458 82696511
    0xa36060e090a0c09080f0102040306140f04120c020904050705030f030406050301060f030b060d0f06150e09090304030506100515032203052b0b030307020907050a021c0302180301 78
    0x3603e82110100612030b10715100100219011620019904c00400d4004d6100e803000321452443d125a2046002141c0c7c0954456240c0360401c18145e0f0f51034803000d40c4402100c941d50f08100f402c4850100683c3e801514a000328085c0006006c01414941071501c0d14814504e49580c541c000d110030044284d220f000c5a040d01d0103446c00c00003200300c145003a0082c00e08110b51640c014808a013414495896520200c0c800141540521907140e030b8020400854001956090004107160300b01665420b00034052034004010a044900d0f2075503d1303c449040a1040d1010104002d0300c81c401c116600d80070054641c5074451902e183d00d1030404001407090801003907190307040d18100d080c05005160203003050b140c0840039020305012084260b00021090a040d640704000140343c103250302c400b402d000065038115507003c3c0401e05151a9132009039841c3e0442c0e10150118841c01441d0600c41d104203d0007003a900c915140581c42e201d031030080000700031801410500903031401d08420b09000501c8180d003c900c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 82698958 1250 82697708 82697711
    0x50a090504050d0c0c0504020f0a0801090605060a08131707030f020d081501120614150403020f13020c030f0d0c14030601030906020906030127060b03010b0a36060e090a 74
    0x128286400d40700d03640176501084d4801e10106880c6010424a00104151102951284d0080e031700d686c5c1c0401140c4503409510b801c20424401c00c3d1401e030080c0c1003560000004a00c20b84510010b40e1141c7c07a1140c0c001006104a40101e030700410940c001c00c2d0400354038828000f034490300300400c0c4000c0a141005095040d0842a080c0c80001039028204020907000850800e0000c140c039108a0b400707000c0d200b1384650190b5a55002004207260280944007030b80c0d401040003072040c050004004107a0f08041484640300da0070050721f10410303070400050840c10162001c039620345280102d030b1011600c81c0aa00d900784071020844000b01d020183c01c0381d81c068000d0800080c0144107040c040000d000b0651400d4000100100100341580c500c0b568220f1521860b04050206400044407000c1d501c241c0700c1d600e81100203100500c01c0b9181c7c080a41182195440e00c59910b0701c818984581003121500e4100708c580d84842c84114100009501c0009402c2c1e40c201000340b030102c000480c040c0391005001c0030695 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 82700208 1250 82698958 82698977
    0x905090408160c0e071407110607031806090f12210203090418060c050a0f050f070204050a090506060604050105032e06021506010806060909060103020f0c07050a090504050d 76
    0xc0c0c000784440303003541114561142030348407031303544003403220585013140800e0491002c0d410031121601101c41c6180c0c080800385812a220303090208540005404809014040044400101d201000103008107095555211118a4a000b121300d0040313680007a0a41d840000900300400d00342200c0111180e111800c40030701200c1c6207400c034290b00490a81e10750042c107000310250b48183c10306c140400f582c05079408004810100400352024410131101102041140c02501d0041d40a0b40142072081180c090543c58040e6590000d41111001c840c401030b010f42d0350343c001042c044201314441e03024405641c2245042c1c101400078000b8000204031600c06101480180e904540500c0010210410100e030801c1c4244c640b1400303920341d001e014048130050074140000d419980b2803007149001d810050440e43c075103c0d0385002d002d04c0f20001445541415001c21818160702c05500c000e100c0085807101801c0303d6410081005400003103513001800a6040000740b00210b6008203801a030748586090101f0b6a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 82701458 1250 82700208 82700227
    0xd05070b0c010209010921023007090507050307020a0321140a0c0305010803220b031e060312070b18060a230705030c03040309050319020102010e21090103060504020c030702100905090408 82
    0x46030240300412540301022211b44009c0d034800940fa5042d2144104117122585d51580b04940070b001c11980d43c001603105004941c0031900400c0c810300034000c81d8000700b01b0600c0b002d100d0300650340110818000d490403a4100311000c2d09038072911044003050701e07080c03016515001c40c0f40d03030301e00510b2102c2035904d246001c050485250303100010000d2050010b41b0f520703850300644844401250101101342c0c0d5404000041c01d40c41d0101c0c440d002000c481d85003d0801c2141c3d1a4480400c00c005d040041002c01c814074020174010800001e0312541c11402c1c0402c00c101c1d00c6200007140042900d0041c2504480024080c00b9a08841600d920841c2c5023851030710380c1c3e11402e0884881c040d580c005501070196041405000720224246107259000b81c009000d040e03024400341e682c5101381c1009000d010003000340101c042c1079041c000c142501c014540030410544442c0003038100d07846000c9004880e44000341c900114101400e0102408c82c4e142410025030341341a020404c50700c00144000d120f00c0300090045003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 82702708 1250 82701458 82701499
    0x7030c020c13060e040620030402090109050c2101050a08030306211203011e080a03120c030b060309030706060803040b0d051308030423030f07020d05070b0c01020901092102 76
    0x3450018040e140c2401c060a003000103021000743e07405051f400b0369a030741d403882e00c01c2d0441e07025039405020310485030700c1d000500c0e0003001c000d0b140c6040100100644c501e1036111452024881d0b44207811082994074020070008001c400e0750200189400500811420b030380d920303d62070544030f00c4100341144410501c01090810314814401c18400b01d01000200304d41c440312044903103420003041c01015107511010401c1d55000c40e0380008000900c1c981400480d904180c0088802c00240d04002c21102d903890001801a00201c585048680c00482c07008188801406050b00528820025514003410001c01907028402d441c0d0740120b03180c44501141c2841c10100108510170707042203d040c0c90341068a010307030f04d000300d122004c2c0b002a1a0042d596080c2004400c81d03062160540d1031a103000c406a090020303c215020040d10035000e1580d00050b246410401002144004c000050f0780e4103642c000035092010310b03041012200b4007402d402c0302e8025180c004240c21901200c0d0040040e400103094507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 82703958 1250 82702708 82702721
    0xd03031d0d030b0105030906060d0206160b0402270103080f0904090813050907051602030f15090d0c030c06180602191209020a0302060c010906090b0f07030c020c13 72
    0x9030080403402031032088030302040781d556124566070184030041c42a4011121400113940d0307080ca80e0441e82c04180c0c2c52400d400350a2411348040d08240c10511543c00600240303004183c2540c95901c044108000c62404600641d81c079030383c80105110b001314001c4510b4074010140401011294001907600312840018155002610001d109101c1042c1c03034a4091040d8000c0d1803031294520310540c0109881c6041d02c91030344a4000380e9907041c10f00704500311200c16920101010b903010300440200c82c80010b03080c8030741a192844010203100d603080a2102c1858001c0c0d400d5101d0411584140403c00690f100511009103900310101080c10781e14a03e902807a030f09200070040c1074600c0010310000e001d1114888481c1411103807525503240a842c42d449058a21501000794007140d042c6042c0010b00d020406484044464000000c01d02c1c1a07076078510440301e8514080d80c40d1030500c3d0411030041d010980042e40300480785000c0c04051030410001e0368600c81c4082c0d080c80b8800410903c07406004691050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 82705208 1250 82703958 82703981
    0x3040305060103080409050f0108101a030607031e02070201020c04090201020f101b0503090c012106290a080121020d0606080c0d0c210503031006020105060d0309050d0303 75
    0x481c01c550f56880c0502e007650091181074241da05160010307000001a0114904907604400540030100d17100722844018004420706450300500c0c80d110306c500f605d082082c0f034400c2295880c001842080c5000c00390008100405c80d043e660300402011005036404120024510001c0d074012034110381c2c901c01031f410000c0e03034010459288a405104d0403800d109400c80400d050107a540003c008600c984200e52034403040f640300340503a008001409580d403143c010340c41c0c1030304d02c902981406048201c501c0156040c651240710300c07416080c1283d2111695007400f00000d40080d18040c9841c40c0071201a14041d01403242200380150001d4405551140801c4291a0f1380d0080018805c81100c4c9482c00003081c45004403d66440b0b003901d0400c203800c02c540012009500000b5100c070076440d000c0e031000e1818042400d0314503800c2d102c1d10100041c03000c001550095100085031100e05003400002802c48000405041c07143d01c420385001c0100e03070080028400d8901c06d807088480b951f02424181c0c09090307140000b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 82706458 1250 82705208 82705213
    0xd050d02210f0f07030e070b030901020405100e041505090402040f0e0109061b050f030f101214010f0209150304110303161203050c03190f1803120207030c02090903040305 75
    0x400c040c286500908030710071904060f140002c4e440341002102100d00011030300905a204500c1400324050b04005036074801c0103500090301e000d4840012032403407403801c400040440c001c0640b010481ca0907010706000c0950024180c2e0301c140c0341c4000a4141480130300007034007460b501c010186c2081040d800551601c00c90380000c0c003100d400c5207043d9004020180f1219144003001003000c4d11a48594201c1c0c40ea0058a0301242c2180c0754031a90101034800502a556035000d40e00f000284841e800c00301018150044490b4080e03c4103d699003400c0d1500f080c00c500460f841008500c8031561040b0641c259190b0101400c0d0300d0795079034a043c0101d03840741501c680d8184000b08007a0850200d92503045d00c03181c859070703268480c0c6000070815130503180f056960414201e401d1000034010001038248000b00307180b0f100e000c41d15a0042c00a40102c3c0d8540018003011001030003c0d5003415000403411010480000d070841c0741c080d0b1740e10004d1078010380c05c01c004e1044071414082010703a01c1c00c10a850245421400303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 82707708 1250 82706458 82706461
    0x1206060b130503010b0a1a0c0f0601030c081501050a06030e030f13060210050f01060e0d0c090c1103070515060d050f01020306040b040207050c01120f060b07050f0d050d0221 76
    0xc1401001c100c0d8840d42d0310a60030081c1c5400d07142071440d9604c01311035032403400c01c0343e03441c081d0300c15032450b004815900c18500c640780900c02d04410810085000314051644c20300d696041c2030318503061192a4200400600c0c8403070040005407030f41145042141c0381494000742880300d06100f54294401d416000e27220010218840b601403020b060a102101d07106d0702291800300300310f824242903070300441c0c1c104007804a800040200d5401105030700002c52006001503040c942e90354400510710030340d400019500d03a0f00c07036007240e0301a0092000701300c030440f0000450034120590b0b507083d0f588480c610203410002c110030100340f0315120302046503560b552000684404504c60800d541c004d4100b202c1031441345040484c4500c8508040c42100c80940d0040701410800f030458005517010034400745400ba5140c1c1e55425071074040c2e518071460340502088101c0c65510011402c1651828490f00d0101c192034100c191b0440d9015004022034001c0c802400001d0b071501c400d00b42c2c00d030320b09004422100f1394014820 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 82708958 1250 82707708 82707727
    0x5060301080c120a08070b060103021219050c09030a060c0c05100903020717060411120d030504020a06090b030a0b030a1e02010809031314030715090801050903030f011206060b 77
    0x40c0a0104020a81e040200e560203681d4036540c0b4110302134082c1c00038404100c9100402c00c00c8403d943e0000e41070401501e4039400c0d210021075260700700e90840d010300c1e618070b0048440c02d660051942082d40070744018105984240025100c1c4080720008011941e40d518821356a4020300e28800300a4002007a1a100a44101c80c41c0140910140c118010f0260754004280303076510003040c1c00132a01500090040356a1969065503110840c000360740d01a0038903101210340c000400004a41041e00e65020a09040900c14000d6a0030290030400c2486990802440280500020b50350303c102030410100b605000c0d0300219082c842020000b40c1140310038003c0f6070b101d40002d40b031501070038800e0340c0d05240f503070b2496540e80c1c0701e00036000700042000b0340c50010880340d043e24810380035010b0006c1c00e9481083e940c0020b02d501d54500ca22035000310300b888004006000c4203118240d4403030140ba01541c513514206500d1459140140030351850070700d51345612030a002c4603501c0000909607030843e003951540c0b00e1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 82710208 1250 82708958 82708963
    0x50c0a0b04030606080d0504180f110a080a09021c0309030c27060302090c0f0f03090d1d090708070216060201020306030c03030c07030f080d02030411040c030b030705060307090506030108 82
    0x500060f21114100400020f6013400000c20205810305981e400d4181405c250694a0f0560040081901b244c2c4803998010356001d280b0608040c00c0907c10541c1d640e040118007c1d250304001000540e0740c0340351050800240c0c0300d002d9503101041c01c202d0140c11701c8007686010b89624030030342c1000d461981241030104020b4024249601c4c081007031007400d03050141060101050b98440e0100a4000901801095100c00100081c0c001c200001030300600300304c058202000190400c41d107030710b410360240c0c8c22241e11942048204480c03011252018050584810200e0740403600600300b1410094040e0010311010702c207000503404032200c12800411190345244c002d010350020741d10760384603000d95039100805103000801c4440c413560300005084103500d5611124495000c3d0801510b12200030820203000404e144020752055109003001c3c42c0d9001c0314424401210b04000001003418904040400315940c00144081200c40803200399582c0e42d01d0a20491f038105003680402e800c4a008800401c040401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 82711458 1250 82710208 82710217
    0x609020a03120207052b06020a03061d07090b180f0f031005010303020f0703110405090c060408010203011e0302011205190608060405300c03040e1806060102120901030504050c0a0b 79
    0x85411310b11120074204407511003d4022010134054a80340c2c800c0300000d031560041c10709c01c2c40508000540030380d2005002c080c0c028903880101505020010801c2d05600709409a0140160a4015051850004481043d402040b10880c8583e0320440040c206613564202c4031010301001d4180c8001002c44204000913140c280011000b600982d80c0d8208180c0300016854100d0342c0141c280e1100e14a6402032000401d0060710001c86801200066001d075154003005100405543c000143e4a600d80f0301a002c410300400c10310100103033000e03070801c0584e80c00b683c0042800d00d41100019143c031014140c0c48001c4400c85c0090f02d80e030401d00000f0f4000000300705548500e0082040c0c030001d00c00c3c80740e4040c02c26000c0c0030407508103035228907000302c0c52041c1000e440c03000c028904591820341c980c0458036142500300d400011201c500d240d10044e029047c00140d40000d828002042c100030102c421080764041e40c01128100f680e914002424004d0412074071b8402803020349501545070300c480068006900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 82712708 1250 82711458 82711469
    0x3040c0906032003030c03090d050307050105010303020706020f0106051302210c09041104150c080f0f041e03050327040f02090102060f1303050a020c0301051006090e10030609020a03120207 83
    0x1c3c0c0c1043c11069013408070441d05010181c8000d1890714000c031040010048003040b055031180b20500226001803024030999003e0350007038000b010060b1901e04000c0c51f00c0c1c88103600b4502c0340d040100c200103540702e59030103c40300c00700c2500160b11a42c1240500071140d40c44007d1a20a0000109010aa250b18401480b00007000d49061000c804081044102446180324009503400310540307151601340b103407200701403051142c40c02900e0019030455901d8140c1142d50201c8000000203010059190202130b600711204442041090071851344c0c035125144d01805182000300c1001801c1c4100c0c40c125481c21224420008008101d02c0d10040014402034000d004141d02504c00c07030700030030074000c281003810703204c2c0005101200e500010b5070f5048405801100c04ca00961040b02c2c0380040c10f039805e001d082c2c070440040808500c01d500e80b040c028680e0400b0341c040e005861281c000d00c03000c0d00c1c0c0120000162600510080361000103031020480e4400742d075001400c50b100080e00c028401d5400b042c150708071344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 82713958 1250 82712708 82712753
    0x203070e040e0a06022b0c0f03140105040203100e0f0103030e0d050a021005071a040605010f081b0612040b010504050703020414011107080a1a0702070305100203040c090603 76
    0x20310302000d120490705514510141984258070141c005002c9400804982c107240005242c000400c003100c01484945080c20081a03448507a40207007140e2000580c01e8140b0146024070103824800c410f90382d505e80601560340921740000028040b032440e400034800a01d0071a00709001898004c180d940200300a0000324000340707001c005400140740c0340c40d14400607030b006005045480802d034204400c800d00030b58a0b0092110038021140810322500b07240480c182c0ea1400900140303403e00d0524116030050b00711050b4060340c087c5c24032000c24000f072003504d5003000038440e4101c0396201c0d000495502402500808400d0800d003003004100d001c2e000c260481e481074405001c107498800301034080e070040d400350010051102c024043c42c0e40c860010003840c0b80042d0142d6034075545440605042500c41c00c42900c6074000a9038030035209040c90700487e40700140b4400f6181440c15550780076140c48204228034103030b64001c00450280404c120300798004280c8407a0403c40d04d9030301d2921188050754a18182c920a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 82715208 1250 82713958 82713977
    0x181e090e01020a140304030c021f02010c05130e090703080f07060609020403080f03180f0102071a0106091719030e120c010e060f04080a050c10050703050d0509190303020307 76
    0x288014000d562040d50240c0365195550300c40c04d41010301e90801002a0100300a0007820405a1a2040380c41c46000c03c2c180304010440300b43c1c001a007500c2001102000f0060100108041c040c6c106015100751a401d400000c003d032110307038005140800030340014040781c10000741004105020402400054410001804442d9444030b01004071300880c03102401c8031004001c9540071200d08402136601404000304105440509244246080d4800c070094a581e98000303141c000b80311041c100001c122440c40c080061941c1040720040060744503115858071802c0200307c980d03a080081c4800341d408022074402c111a2502810001c18462142c0da01c2c1f03014004e14180f407800807002080c1403c0c81801a1281d02241005201780b000a612921101201c054248400b003000c8209000110b003e500400041040a00103410010710b200b074072600340c0a00108006500000f43c2000c00d681e484951000d00003025564500040e0811071501c520906c0001801600c10405405a0165010744000d54444014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 82716458 1250 82715208 82715231
    0xb031015060305010e060d14011401090f0504080f030403050d050c0a1403070c110d24050f04030f050d060e1905090a0201090e06010507020d080a140316181e09 70
    0x303c500c01c0c0200d154521070800065041e0404582c1001d00c0d41c07040c5041034101404004036421180c415a5403440220b00e040100221723206806509a020807902c0100090b0a0541c1d84407154414031080c0640d8074400320004007818040c80549505035003120302800203280928540210b580100912030104403010300581c0f2008070001621322030465500c410500341c0082c0c5490070012540600c40d40e0151396900c0342e6000031500400b0b0b2400f03420484400316114500204074094034402000c82c41500142410000842c0d4403082002c40c81105007172595031032482076410005480c41c3d82000c0707513040000080c021030b401d040102e20304404202c40100541e40f42e11350250348074078884074042e0025082e00300920804521020003a0404814100a031800100e6400700d503001d0310941c1d040c0c44154000c104201c10304c0c0c00c40c0c0c200d000d840452400c00d1640c94013100c035070300030b0150300411020403502c00c01c1142641001043c1201603c41035000120100d4060780e00001e081e118000c2008203402e00041515 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 82717708 1250 82716458 82716461
    0x9010c030e0a03080603071d041a0601050d0510050a08030910020f0a0326010f0f14010c06020a030b031603060b0604060c03181503020a03050f0c040501050705010b0310150603 77
    0xd61a50301002e00000800390324216410b01d4003800303441d4540603000300051200300c3d00468540c0b000c40c00086120616050610901da14180c0c2e12543c4a841c200f402c0120030303a4050700700c6004000200740001d041c0c443e400d62044040cbc807500312581100c43c070200418101d60002c007404240780119204280000240f0041343c445080011051603640020b00c094002030007440003a0600540e50b40a0401022440229002e141c00382d00a8802e0042c41d08203100900b500301c6407034043d1205004041c590420707a0002050314844020103044550302151030702003540f083d00080d5081000400b02e9902c462802d1140103500218807040329001d00d4012031780018140b14064400f2209140c0740c925000300c046c0c90990305180d40c1440e08100a01000012400703661080c442c11000b4010380d801a03d4826114018085400250261b404100b181007042035140101003118181c90003860526120744461424502604c001c0030a29810b020340b401c115200d400b00e51281074105d40c0d48185501041d900e040030740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 82718958 1250 82717708 82717721
    0x5040e07080316030201020c0105150a080c060409020f070203070e0a140609070f02070b0301030821060f1207090501120606120b04030f110a0b070908010605130518030705010509010c03 81
    0x90700342c005001c50481c08104800c180f00c801e00030b0001510300741030305001d9402c4078012100761100003c10504a51a41440703e000340c007401c1414018a0380c001d500001900341c2c05a8410811b00c1900040c07000e40b42c0c1010301c20364010a5001e002c41c0e40f01501c03400d64903800c40007240d510346001d00d040101504111400c40481c05480c000e0a010026181d080085454000d01480401544640800040c00c00e4280780211300031401400051703264000402d000d00c0b1442d0224928440f05045024003540c0d075202e4802004d1070404031648005e012981c800c55090245540c804170380d4601d440b00009500070802d0240070150b2049030108140b549900304111003815184001d0f205581403400680080c0c0903482d50100c41000b4104070035442c0e80c025001d8581800f03013404644041d0340c6c105014005401005132009040c659009020281c1428040368800070306e212020000c0781c40c1d10100c0d0100c0c1041c000105400316400640c0e50f5071100341803003400b0301004c0d210503501d51720780320140c202c4a129229a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 82720208 1250 82718958 82718969
    0x30f06031c08040b091c0c02030d09030312050a060801021308010608030a08010e04030c06180201020c12101a030f06010e01051807030902030c090106031a030a05030405010c111905040e07 82
    0x202c216211521000e9070814000d2510700710313110f0700e0350085c20790091002803007141056035104041d904462040c1820400d500072130360107002001c40706000080d0040c000c040b49034142000003a1a58030171040c0d001070901d503400b84c1455440014901084400d0450b10780507110000004c0c004141d0b545402607503881030003a20b00016000b80e005200800c3d0a2840340d070494000c0c0381100124081d07440d03003c00c44c0d007141442e040c001c0292030f00f03504658040c01000c41710241202d005108a000300201c3ea01c0307414001d081400c503507407982c26244442c00c003080700107031580c082c0c04c80f400c1090f00359015070b40764400c0c002e04032600c0248000203041d2409040072002100140d1104e402030300c4103d82513026044030780040340d050060030500d400b180c5841c0a154000c2625580214440404010300c1c0c0c3d2112034011403c1c002d40141c1c03208030103d6000400c44003215028a41001c05000341d0800c5810340c1c9032401802d42c800262042226030038410b0100c0740a43d1401c880811400700960b004540c1c6400500c00e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 82721458 1250 82720208 82720217
    0x504050f1b0c010b1003020409141b2b050f090615060904090f060c030b030c060304032313150c0b0408030703060503060a020c012f0d11030f06031c 65
    0x44040070080c00003910300b01000c04000b0414050b46400200080707486131109001075400318040004075014020f0a108061101d00642a030500d041d49400c074205442841104c1c01002810300e002d41d40ca1080b03006441d1f1b095106542585d0b15142c0840584016184004c040d15024007103511107101045145c02031440307154001c60311740ea510034010141c02c040422507000759030b225590040b54400b920940340743d204910005101d18241b5010341100c030b407401d1050082e40104560191174a82e4011a60041e42600705007500980700044008407100141d100c6059075000b0440903800c048000c0f000c4103851100724454405160440c084401e00c02941016145284070f001150204281343c00446e0000040d03c0c0c003107080790301e07034000c240790482c00c0d20104003203540000c0e8006142d17400c1c807400500022624039182210b104030258000c4001b4a401810459000900400c459035258420359102e81108156a20b901d8090807500e4150b1088a00c83d0003401032415488803915155441c0103511000c2d1034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 82722708 1250 82721458 82721491
    0x60601020f0303060d14010504030e04050109090f0809030a0519030e09240301020f07050a020306010501050c0607080c1204030e090f0907121707080301030309050f0d0326010605040504050f 83
    0x204817040c102580300350340c40f0341803200762000d40d0428064248180e00036107078440000c43c60384c280000c442e4141d08c00a40e05217080d0500000501450407144800c1e000001c20b86c403120300e07000107400d010b2040340040040c420704140000f0074441140092034203000342c403000c040c2161a018000410b008841203000042e00d014034010400c0000c82a05030344401070001814106194254107403580281425141070384401c0d036250031464200643e6016020030328052782042c0d800b04440b0303a5180050280d41c284010070b8009000074171000141d6520b01490f4125a40d2418141009007601540200a900606018000031541050310503428011002c1400824080d4a001c881c01102581100d0403542d9248621104984000142c09001000e0069a02c0c1d070341e951440c500584070740950740c407040c000d402c440c0070303c1c145581d000c514444a5070103082c8101c8200c5c00707266040410146429140d4a4a82c0b58008a40c003a80b14001c1d1041c0c8209990400546c0c4450707070a11420341040f00e8005042c1c10100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 82723958 1250 82722708 82722721
    0xe010306060f2105070f060513090b030a20090a020c0f0c01091e080105040b0601110a1106071e03091503020304050c010c0f0501020d0f0c030216110a050301061205060601020f0303 79
    0x800c40f00740c00d02680c152030480d0348500300b040600c003160f442100040c0c000305181441201c401c10030002032208113000c1202c6250740c80403d0b242c89142d5030181160501b002d01c1e0000d0665000c03012186040108510024078140341400e00a400c030200c014070034400c846c601030100400181c400e60320030058507840c150070b2400d62000014003000c800e0791010205a18002403002c0d007406224000e42c07084c5841030302c9145ca20700061a521450b441220258407507508440031070410f9a00d91180e41d41900ea00d9920303ca2803c01030b003981150f114913402c403086e0404c01c1d002d2542c0304008000395101101d90b180c841100180440c1a030009842c098103039048401034010303c0d03003c0d010749070302e09200320054039140381c560304c0711400ca8211005900b14140c45103101e20000643d0b22402d641c401a40c141141040b05c10301340305240090740000144440c8045880c0b5031250b80d148094001480001c1c002d00c030b40c41e202c1018559500716001c045400d0b20441020541030740c0040741d02d1500751000001941580d1703a20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 82725208 1250 82723958 82724009
    0x80d0905062a010b06030a02120609040305220b0c0601050306070314160c1e03020c0901030b07080c09040606050d0614010c030302130e0c0c150c1b12040e010306060f 73
    0x24000b03050b0543d62208111540e441d04000b81d03115011000005845050f0401d01e140302c2c1d100101540e2150300f104080000107074004050b40c80301c00f8841000380210358007c100412200300382d004400b18180208250024010000e9918141d07101601a140079032941501070f01920036088a070b00c0202140d40005106805940c40441c5021152404400090a40e01c45054514480c07001c0c070110b020305400c4c0300034180c04010000c03841e141654802c0c071640c07641e2079102c10820058408020081a4008505da440040d0306880e0441c000030300412600d995184090f1245d40b1864685000506100d4001501d60152880540844041e1510340d92031036282c0e0114000e61220388c241d2141c0d4103034200407031080c1040000c2845504080717055595114420b0340c0d0f600d4661035802560b0002c4424040000c9500603406640182200307280f10644200e120b55158240005c4000c055280707a00407070f00040400d281d4150301d0483c0e0066504006c031685900442c03120310b00760b000c0c0c0784081d10519001040503440703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 82726458 1250 82725208 82725277
    0x405011d0f040e062a09090415020d020c0c27071101050705040303031a101808100504031112090909030d0609020306030d080105030a0204022101080d090506 69
    0x1030180314442614000101200e0042e402000903600c81001c0000c41030822007a100d80c4602c2c42c00c6203000000184e85e076071403031180201c004d00034900c02c070105003002101d0040d5103100644107411364603038500715140d50094100b4045041c05118a201c2ca1442c0c0c00c21289009403000092204c40e06e05500180d5207528000240c41d01c01001a0940ca201c0b0060080c031035640208165075038030ba51203255050080980b4982e0300d00214801644c0402c801643e0ba01882d004003040b01e060000500601030406142811542e00014540c015640541d50300499580100d01c61803094807100300c0201c1036400c00d9500d040030000360320f00d04020480b808180c600428540c0e0b024045900302d9280ca400206014156102031b071040f00d07203075004418030584c0d24081c841d26014100c02d143c01c41d855803500c0002a80c5060036a00a40181d90001d902d850041039040244082200040302c6100307940d5690384990340759850200d031400610440004209440d102c800c480042e815141152001d010880c22034108810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 82727708 1250 82726458 82726517
    0x1b0203220f1419030b060a05040513030807050715061a0c07120c05100c03030f0c0c0206070204060314030a02150105060a0f020106091a090a020a02031b070f0806070e0303040501 78
    0xb400c1884241000c0300d68100303c095407240c1c10165184c1003010a00c00d141100b900103a21a9050800708141e202d80c5800c01c504ca26050302d01400c854640c0031050700c481c450602c020b86040320300d840f00c8407041c409411910403a40b0307440030100c4800b000030f000c0d03655000719500040e09400990741002080c0c1e079a03c0e80341c0540c2c002c0b002494056500d400151a0043c0c1c3d100301d5010540a4041c1c2c024907406115020004500e203800703121070459681300400b00d10381510024480c5030040345610035512103502c10009594130031000500d40c621111220317a0394010400420052141c6135511003018070a54819040b148094100e60920b10800c9060f2010b10001c44010300b150f40e2020b0014004009000310064940d100301d12030b400c40d07038420900c00014802031180c20a9401044202e019540c00421200080380c24110124000c0b136102d100b5040034801c2c0e00c0704881e0711036540c022600c00800b01e2064080d280d0b54540007a000316580c24951039005901c03a590220350210000b401c01084407150060060 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 82728958 1250 82727708 82727719
    0xd051504020a0305240a0306020f0c0a08030f060a140105160c17010605030607080f040f050639040504090503220609090612080d1b0203220f14 63
    0x100480c049801040404000a80311028810140c080341001a081d02060fa00600b2094860001c100441351902c002000207a000070010b09810214068466101e5403005582c00d0000d80d00b082240c0787c100759200f04a414002012403030a1405c80071280441d29a070301c2913180c0150980056829402000c1d1450750090004a00c1c40054008034458010701444008860b094084040715821550f041d0486030180d800360041c442c44640143c40a0f9122442001078051952079152058004003050001880c600c50541400460503a8240c042040c401c40e030603206d120000070040c0c100c000f180c0024660020020042805103003400d8201003545409030085134a0401402881d01d24080c4403503198808094061052090941c0035820000821070104140a060f0400e00380282d0098032a034002c0a6540024100380030f41d0301a0404007501e503002c162000c4c403820007940130b5103d601c0b202441000d900d000148018480b01100507909846541c03020304109801c2203103420001554a8159030300a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 82730208 1250 82728958 82728991
    0xf02061b071e051219080705030f070311010902010c0209090708060903040602061f060507060b0303031005090106171f05091003030f0c03020c010e040204050a0b0903070801020f0d05 80
    0x100421005008040c2c40c1e000000000805070803a40011103600040c0c42203207281080c400d04000010070004006022521902011039032810a00c0ea128001c07000300940004154420f4801d00500500303000c40c000c1d1a84203210000c107085500300d03045100c4c02800320300d40c402090f01604200236025400403011003280c9000b5142c0c5115441c00a00300e400001c030f075000141c06c0c0b100300d038144145074201105507840b034210402c0c080c6601407170070940200420048007245041c00e01540d0780000040c240040c0660703a903801d142c040341103900300c28000d9501440030100001841807080241c15001a904000300500791240d2010313a2070750750103800305818160550404141903880030112809400203010030303031150f031130b41c500540002ea0360100340c014004101041d0021075000300d5a140448000d19050002013a00070008000340a150840741d00032501403008200c807541d540c010714920008408407a4002ea584810364242d04c550071505c42400c0c81072000c14008110341e000140c01c08001d08884401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 82731458 1250 82730208 82730257
    0x1403031806040f0b091206010e2a030f1005220b0d170a090819030507061512030305060f0f0603040606050d0305090f0a060927090507030b0c070f0206 66
    0x40803144e0300302c142c0c0640005400e404514003008840400010b4002030701c940e614003030300c2181441000300284600075403103440704041065032003200c5c20b030801d52600f075449061212514814040c02c442255013100351031004202450021415096443e620b07403540840501c54a11801400c4424044d50b0004102014500000c1ca0102030001100c0528400703902c50400c07441c01015012143e100301c20603040507174592800c108050980700750580600301280c3e03400b6145003810082081748120180708102c00c001003140c801d00381c84481e42c1801b964041c466520380100304200200080c13405507000c1d502d007503858401d09003100550350140c060740c00002c1103960313540461592500d240b411000107030009002c84840c42c0511007915201015103a5910540c100f003070142c44031155014031068080f0803014035400b03003401031030703643c040e0b0310300030140301034034107031405503910f0401e4003007222080e81144c00150810418000c1d2054160443e51030a880040c9400f4046180e200a04d1821841b00704270340d0320203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 82732708 1250 82731458 82731479
    0x120303090812041b050307060302071e0302030409060806090a020f0d080a030f1b0804060e0f0a0507080706020d0c02040b010504030f050c0411091305131a0f01140303180604 76
    0x1090282001e202e10b4602d8a490b1100da603003040303000d541d4443d13460314007407020381c50025806041d82c00f64140142d507036805090142102080301c54491703040d010405480c04050340480903000710380c1c0c2180305101068a0304001034803580100c503c102680e01c402c6500026203480c42003400c0410014019146034000364407030204a034081c0f50003d02181e1501c0c0c1c180b000128501c07801040075110700e484a05c502c0c0d502c2e801861207001501c007a02d41500c81030110003d010a004000c0600000b400310b5003810840d00d0020f445174001d10a40030343d8000c85100140943c000b05150f1140c81c4195152620150716508100c024113000e801d280c10000c06010220018104200c0d502210740504003c1201c489140c0c00c020544580368020340d030511062001010640710b1144040303185661500100d110383e00d2141d01c0e00d0100c9140c0f405000400d2110103d8540c0b60600055405440c4100940807142c2c1c072080900341c10b0441100068050f84100b045600802b03141343c40346a142c03001403140d4502995001d0544 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 82733814 1106 82732708 82732717
    0x50303030f0a02040b120613050609070c0503040504020a020318030d0c0b040501020f19090509010b04030822090209041406030a03080703090506070309110315011203030908 76
    0x140b40b26001c0d0141ca004d04010031440d603c4508250501410500035140c16004002d020500c03032441c02580242c034030814000d0511400c540740c40b0011500c40030070400980b40d03400240400f08240d40c442c00104480e120710360045490307000b20220b40301041042e04a0501c070740e0000c4502c28200d604802c0c28000319801c030a14030103139074460510a001e80f00e0541d100c0c0008000140c0c0300d8407014120040c0744c00590550301c2c2115a038a42c0148250000c083c000c55581c0c0c0b03010f11082000411a000070054080c1c0d408040500c03c0002c020540808036641003404015008500103003e400c041c45141c0101408408120700c41c2850004252180702c0c0c22400b45c01c002a00c800111190300903048032009644c030030100d0302c0c28605850002d0040c040d1a904441260301e49407840d200d071800290f038003490400f80c0d0f21404507919010300b0111a0b051100e003103052540742d060641c0030420340400f03007 = true := by decide +kernel

theorem cover : BRFrame.Cov 82553958 82733814 := by
  have h0 := BRFrame.cov_init 82553958
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82553958 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 82553958 ≤ n) (h2 : n < 82733814) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
