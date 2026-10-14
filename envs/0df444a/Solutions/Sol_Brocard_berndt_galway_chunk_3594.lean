-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3594
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:11.463851+00:00
-- url     : https://prove2.me/submissions/7f0ce9d5-b209-493a-91e5-9d9977730252

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 646223021 ≤ n < 646402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 646224271 1250 646223021 646223051
    0x807050a0f030b0d1406060312030f0705030621010b0a090911060307021e0a0218060d02120708010e030d0f0e060403050d0207060609021c0234141e06060f04 69
    0x11344144d0440316030038140c424000069500e1500b910a1400f078842c02e4019a42081108145c901a81c02410550400e44a084084945400180c40c40760302100000c064074601d001c200141d12009038000001c00c41040e50002c100f40a002039000e100c00904202c5d80b14000b0300300c0b0400715005030342102c0403a169120741c43e040345858980d03a404280c2d50403900c6110b000000000380340241d00c1c800c44055024010344007110002d5401a102581c02828244d0341c8401840d003105c0d91010b071701d1010220b425140d0f452500a0a48a42505202c526000050000c403100300034001c0e5201c42a18140910968080c0341980e46e48840060024082000c007007a00d081c00c4420f501200d4031203800070024848107841e01d4003a0000c0d07101400350b1103040c407a001c004201c906540203582c0b0111000511640345040d940440c034003000303010010880f80d5031001d08ee10000e4080030050f4502001d032802400c0307500154603600703c1a00700444103d0654041c00c03c1000b55502c0c00d40c104013202c01980c002ca2029591f410b40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 646225521 1250 646224271 646224289
    0xa020405130804031a0901060f14010e03030310062c010503041b0905180105010f1703040b0a1119050a061a030106180b09060a03062007030f0807050a0f030b 69
    0x2409803100050000600c0005100310240c54101780c2c036414992a4418100c3c01c80da505e11603104291601c49007003204160705440310954030410b04014441804034800a07007554002c07a201485000b00307110a00c084c40e4403101c0707200e0b40303e4100c45000180b0071465895140303645011116040100c00000101001807000c031038450a40007419004110751500b50300e0b009403004031143d0310007941c0d0084d000c03419081400781a04031742c0020100004107052130b2154840c000c090001a001740b108000000d02048050000e008000031555080e8142d4a01a9601d00f820301d0350301d400502c5014419a0030200f14007040408103180c0c02100001c0f02100314941250541e100035800d6499443c100b400200c20042c4507244035000002c0c4410802c032a9034408214100304155241600b0404003902400003503102c0c2e2000400b41a10f21290480e05400e000c40726259200d100100d0000e01c4070300c031803d15035400c04203154112500d42801410182010b1004000d05d4000500c1d5040549402c4440e059443d00702e08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 646226771 1250 646225521 646225523
    0x9060d1502030f0412053105030708071a0f0a030213080d0806030607050406080c0705210909010b0c1f06052e03021c2007050d0e01030e0a02040513 65
    0x20664803490040b2070203032001c40468040e14114190030910030b6030341c810b40803500c5a91080b0518021107c030744040c81d802203625082c420228180f0750000c501590108026801042d040d03008000d42c50403c045030300c1e0700c9070b180d0304400d6a200604c201c4800803000301c2544e41880540c5001a12a01b443c02c02d000e0f0501d040d48060074038083d0080400405d80e1100d07074541b15050607400c41d0017540b80c000084070f05108920039080010307843e04c007140c5100d90a400401c1c0b802e0055045a6070320b2040c0140e00100c64045078032003c4504000341d01c0300241041c42c0402e00500755080304c07605240b14038000a03205d00103108076103c1003c2421260700302c8800342d03000d04003910014140ca07a0140f0703281504031240d503008508440031a05401c050070b000f4403a00850b10b0060810800442c1c0ca410560003001409035030180c04c1d5161041d00d018800500d4007005044840c2c0074030000d0105a0300028040c18850766080d13002d04141c14503144c603540700400160941d100e079040e64000742c40d980340c00c031025400340c00f000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 646228021 1250 646226771 646226813
    0xc0702040f02120a0b24210118140c070b040c0306060810060f051f1101020d090b16090b0c0f01090b0f011401200f120d0f0b09060d 58
    0x141e5240b0400ca40c001070b500c510300b018002c0180703100b04003c2010010844020301c80b285140101c0c1b00400501741d0240031250155240317020104881204240041e00c26042a848114442421080040c941c080e82c200a0221005815941490201c0c154103115040b000340c844160000030604203c0400d00600045411000410140f07440340b40c8036884040e0310a01c0d02d0007509211001c10445d0302da1205c4801c6510007030100c94560800c0310a000082d101d52240c0080c41007180103000340c1072080c0020095524448030001d460f003094a410413055030041d00d00c0f00c0c40c11903080c1500341c06402400401c245e800030403509466039081000c051400d4030ba0803554a207942800c5000302000710010002c0d0140d030f07101410010680c0c0b501212680010b52548076030005554003002010200300000700c0705107040301015501120070001c001c601d0684170745440b0300340e1030380025046e82507600c5200d01541c0d441c60303080901c9003503921000507441480c0540301c1c07071250361030221320410802e4407002041001e074444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 646229271 1250 646228021 646228027
    0x8010f2111031203270a120909110901030c050c0618070503151e04240b1c03080601051e031e040b0702070e1303030b1201020408011a0411030c0702040f02 68
    0x1040d20f9500203542c0903806554014030250243d00302c2840080001c007200040c101000241c8a101c1d00981c1504c1c00400c0c031041050210b9504080d0050000c2e2644103108565240a403100060844055455140811a0a1240080c00d0b400032840d940c00602c0000107450030300442e410316003880f10a511060307151252045c442c2c861030841c00050300c200c50b0441f000414802456014842400440c0c1c0141a00440e5140f901c0c018894100d25a404a001100180c0c0e002d420f80800da80d850030101c0d19008e44c0d04010b50b202059032092402d0340c4541c1c00e180180c2000c80200000c40251a002590884841e003c0000345e202c0e1112030010100e400c50700d40350361690600d800c01c56200102910454018004d0160108103a20003042c61801041801e800450401051b00c2c101d0041c85124441356210500c04040419200b0034009000600140f034000036000b0f0308845402c40071400d419070207010741d041000702c880e001068000d80e6403101020510656500c65440060014a1451104541d0724404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 646230521 1250 646229271 646229293
    0x111040e01090e03191b06050403020a0507061b150f05070f0212041a03090a051b010306080705100807050702150703080f0105030d03021608031608010f211103 70
    0x1824507040b40c2c030760b500400010603094042501e80c819030100c10700c40c414500c1d070a03002c244641185640f0a030240c404049078600350340c8030025540280c40680041c7c2c49a054002800350903c151001448281400202201500380840c281001014090000300e80304409506141c001d401c800d9103008240c40800032840c3c0035001070600305d80c003210040188290254a84072005400c11203041e00d4030031802110038109410324444650000f4440401070068a10800009404011080568030260001e03005031407288001421109954481c1c41a6886210100701546500c58400000001440c00401e20380c0c5000058a06200c0c840d40290003450306590350140010150241c441e03580300e662600603946443d1007190b194a000e0090780d40c9074001441c000c8405000741d00604210790700a40c0781c1a404219200d1400703540088640c514450480084001d15503441300c1480d0141920321002c0e00424109160801a00450060803112000c2c068200f001e0003200b1203001003241004048658400503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 646231771 1250 646230521 646230539
    0x6010f0609080c0f1003150609090c050711040b0102070807061709061b03130b1504110c030306211c02070920070206070203030c061b09010818011104 66
    0x1612400000603021100480e210b000410101104a0024114849140204100242e85c1030a4006201b4150344090140d018202107070700c140100302031f032540c2c20441e1824010000b5692010340110030810108140400105000e032000021401a90001000c42c003900042c1d1401e20181c00100080c13041c42000205a64003e80f0b03604203142d009010368441e282c180f0420f50710714050714800f610200b000c000100741c01e86040035541c030180718841e05607403c0494842071041d40c410354802e41c054862400700c00850615010340f01842900c40005841c0410300d20b0683d0300c0c2c1c00702511507442040e5103a20401c20001007847d42e000358020320141c41d00903280344000f28840c15003035907450141c040c0c00c500103010364113841050903040d41200c03900f854141103140d4103141d40c8031139000c03070f402003081c4a1417016890400240003404d1210008040300c1c10000c0d800c038902c0010002011002e981002104020b9904c401d429400c00624004141c3c01e4044d03080c05800f4284200310f071117000e500802d0000794041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 646233021 1250 646231771 646231799
    0x5060409051005040e060403300e010c0207050a090203060d020405070215150d08220f031703100611121912020c070509070e031501061b1518050601 65
    0x409000c10b012034568403820704c01601c1468111340441d0b04040c0c00200480d0041e485029807810101e40b032400100c1d0010288551069a034603400300d00c0d078510060414900034482c1c0780101d2042d00051180c145003c000850341c100318082c644400e6008400704481c0e072929170400103c42d50060007400342e031415035402561040400c8c201c3c0b83c01c41b0403001042003100300603101c6003010380c0600110b08001c150b464941003584481040d441101119401e041008216040307200504680300d03003c081246182011400340400a0015000300340400c248803e42418004c000d00311030203401c005c541e5210040307005084c49501c030f01e202c215400024031807551030309036841c10501902c643c880e01078031020701038035800300d010742800101142e109403002c0c001c034608a8800780d4410507501c2c102107801c3e001008681001495494000c0b004000001400041c0e000400011b481c1840c180000880d0500d480b040e00a90b07601c0394070300040743c0d55083c0014041803606406805500314040303400c50b50351840400000703e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 646234271 1250 646233021 646233031
    0x190f0501090203061c02100309031107080610090204060e12101b02010612112101060e010f050f010f1d06072105030103050a0b0a141003020a1205060a0908040506040905 74
    0x500c042c0c0035420002e4824500c85c0c4150f40144c042c0701110140710003a00248480c1038264144801c0c3d41c07900b10b4640c81044401e016100d1600030305640e0800900300e55902d01240c102400045c0188000e118003075021842c01c4010500b1200d08242d00c0c07805619a00307102e0f803429070003405401d0281000000f0800c1e0400c010811542d0b008200056840c4030b0354500045a420003003004004005000007407420301c0c1e80c00c00c10450700104486141c0c0d850006400c6940581c4610078407a02031004010712000c0c001c131003006050a440e2006100d5a01c00000c20340034282c4482001d128a4042403048c00c0c3c00c40e82401d1941c20045c01031542c8120604098028500300301c0d541409003c8503074140310b0075101e07070141c0e8103c80c0d000b00184241003d90307582c01c0708a0802894017008955400c0c101b14030b9080310038201e010b044d03100c6002c00300d5815401442640340a43d042001103086d140303450b90010b003002810b075500c50904400002c500c06140380031306282c2304581c40140d00c40d0000c070b80440c5902c1194413081c016 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 646235521 1250 646234271 646234279
    0xd150f060e15090109050a021603030b190605030a0518010e0a02041112070e0105090405071d060309031c0b0d030f030612020603010302092a042903190f050109020306 73
    0x40c2e51810301c1e4465002209100c95046928400100002c100d82e03005a0b4100552500160605500d0170882120018940c010750019855001c5542681045c4142822491099145007003940c20900081c0c071510028080c110b001e0390396400107a42c00718460f0814801e00c446802400544d4001c14007a541d49501c040c1070f03218030b190080c60744c0c001043c43c0458003000e82d0320b004044d10f0ba0f210b0130152840b0b060b100c512414001e007000740715a166103622610344241c80c65101c00580d01c0046140c0440e0020140c4a036008120070400d0002041000007039030340c0c0309000510041c8032203c0780303a4440a372505440950700a52664075160401d604103804450340c00c4299000c0200503075519814901d0f83c0d0300c00b4042d4010f4070800050001d41007205186a200d8520007402030020702a00e1040c603a0b16401e0040012054040b605000c6050040301c0e00f00c05400205101010f12055544008641f001420311a4900030300d1098441d00f404503040045000c100c542c0400856956004100103980300312102c07486 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 646236771 1250 646235521 646235549
    0xc0a0b0f0105030a120309150c02010b012c0307080105091e16060302160b070504060e04020408070b0304031416020f010804230f0109080705010605010f05090d150f06 73
    0xe09640d00855030407118000e00400e80d000a50b124507100c400c844ca0b04904050f00c4e41764100c08a00c40d00c0c1558881d42e200d040004200c4900b040003421074914218081c1040b5a10203a540b52100c80201c03207214980c03d113000e2003083c47e42c030300007841c24650340c0c0507031215400c1c101008107036000402c001028051303840c200740c04d8401d00c0201c00d0b1608070000c03281d610094035540a03c9190b101e40d01400710781c22880080000170151340c40c1c6140b801411901c040000300001001d100b200d1b80315240070410388041c0c8056042074148400f164031610700780124200c0080100c0018280341c81145881d64040c080c3c00390507540c02c0c80201c2001e0910403032100764080c106441c51510554802c080b11881581c0040d249180f429040001206800580649022911070004640103900c020f100d6043c0f8a440b5403807445d40d030030f4a440c0c00d0b400c0d10035940c84a41440022202562600c0c5c0060031107070603440865100d403050340d280c900441041c001c64482c028282c03801c050020110407aa00ca0800d0752801411006c07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 646238021 1250 646236771 646236781
    0xb01060e0111070e060409021c120e18090a0b040b010f170d0f030b1806150909010902090607170c0106150f0c1a100314030f07020607020d02060c0a0b 66
    0x5510407400240820b1a4002501004039402c02d041868022100400c04140817246800042405014405c40f1000c60404200c2c81d0030004040800d080004d0a030070080008111300700015041401c804506c02031161000003c1c400003810f004000c0358035800680601142801c0c101101d80a500340100001d030300346d542c0085195400d261a143c00015018010403c1d0401e005003122900d4590303010206054440c2c03c6202d046e941c40d0310a0700200c002d5100110580f524400300128040491a03884e100d80c010071540706035481c0c090043d4150740c8030b00d00160f034030554007000c281d00303200e0f81202500ca01c3d0030f106003150325241a002050541c2c0114000d2100d2519401b078110072042400c03000d000304030f01c6800d14000f039002e50b5004482901845102e00750500091903580385400468101d84491041d03142807007049003040100199003000c100039414100300c0d00300307511507100e80c4501074441c43c40410114115a2510800304449501401803038035210707900b21203039844001c050112800c96100340054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 646239271 1250 646238021 646238027
    0x61e0c0206100603150f06050d1b0219140a1101110c010813020d080406020109020a06021617030706060e090c0d11120709050405030706110a17070215040b01060e01 72
    0xa40102c2d910340071200200c0c588541a001407841c0d00c001c1d40c92240b000f4000035020210120880100700a44803a50388c1d4980e01d24a1084401d1180a4200030b02500500300340a0f600213584504a0081c1070480003d40d0207007800c5440c0800d10719443c0d510702c2100d03880000c020009851300d856800a80710584100d11403c901629146042c2070303240041d02c0d103000038071448d46079036803500c5050002d4500c002014090f2614503055100342c21400c050b0303451300218011030406c500100000e08071407010b0644810604582c20b4140d6417071080300322275a00c540c200e0b65844414022601c0040c1d2001c0c041002c941d4a4501944019040354442d00032b0003010003a041500301440103280c81a8800171400c00100d1a400b0086034100013034011a582c400d400c008210750700c1c0b610406000324003610007180c455480d49050300036110200c411a04294090140c440465040710280c0a181083c440303689a690352800200d1130700d6040d2514003002c034ac084081c4820b000c80b0000c1a41030f41c9a030343d50304c2103011200d4015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 646240521 1250 646239271 646239283
    0xa110f0607050d14071a040b01050d0809243c0316020c19051509030606040914030f09040b0301020301051c020a030c03051e0c010c02090c07061e0c02 66
    0x240c20b580000c903002408511800d0303420700050465180c1410000d25403078100707590107030f1000ea0006450310350902c4140302080307001900500c01210381d00f0102680c3d84e5000054040d180c902802455041d04041d40040214450108185582c0b0300ca6110101c08203c00c100c101d90000680e0840c1444102c400014034428840e0314800c0c2030100f00f0f07d140c03600c1c0c24000710325040310005421030064030a11805035950000114a04600451030204141404204000050600042003401a0030082281d00752000324030b19a0140b011900054503026506204140401c0c141440e252804002100d0514001420207022115000d8608010060030441410b080348800e000c0c1507032040300e40c04540c41c10040940b1400e00a8400307805a00034070f5480e9103400c2c5c00241d54008075484d030001d50305082c058400010382009948540014a96860030b4400030302150800c041c080d02407444c6030009400014080f0846061552045007009140f10750b158010000307540701003c2c1c540c0350400d0340319460503100040c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 646241771 1250 646240521 646240523
    0x50405010c090f0b2505060906041b0e04080a0c0b0c04090b06120c0d060302130e010c020114180115030609020a0e010e0610030f05070206060301200d021b0a110f0607 73
    0x102030b103461740070852481880880e10b40c4a03402c0310703580f403410000351041c0b0109020f029400020f100500302072030301c0d140b103c0324080c10540b12802c1d5041000013440c404840c54006820203101a56402c80039000c07141400300020140104141c135051200c9800364000810482d001c54508100b00041a01002214451031180100380030039003001c500507400620003024800c1d00e40d50700050301a07481d4041500d590020079500045556184c14144044080c0500040451644001c20007510700703d10b01c125040018065210040150040e4420180e007503002848001c0c40404090503d0703601d2074580c0161584200481c043c03404400f00144010340040294140c820240008000da5030304801d012855070301103200c10426850b0011307031420201c94420140121465400b42525140ca041410f09460880d55071161105410203141c0c5038103028030aa44240346030071405a070301e44c3c014184141030b51442d42d44842c2409031600640800c548506c6560700d040080e42c20765103020001081002c1c500944074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 646243021 1250 646241771 646241789
    0x12041406070e180903090f0a090f050402010306050909100b1230030912090f040504060b0321190c0c08030304060501090504080702120330090102070213050415050405010c090f 77
    0xc03001060f40b070200307d00314071b1400c080c0446600d40d075140e00400c2a40d4806103298071040c0c0c0c58040c80250350b4140034280140000360394460980c00c0080f10266030704c0d1600700405120303035210160310843c0e4448042d044001c2141003210500544140500c00000c2d111032104d96940401d0003c91400740c0036025640b24400c5c0401070b1500d6503a181c075081072503101c54003817a4040310240c0044103541d40c0b8803842e405103010b100005404402c000925280034000c5150f20684080d10394443c110055540c22948200c03035041031003a614600710001c2d00c00c8420000300500615110802141c4000004040c1d0311580c060358050050307981c0c071410b120480f0030a48000c0c20300102088110090304003a802140000314981c1180d01d407201c00c41007400030b40b0030f500c0c45500d0b1404824190009100800320143c0201d84a0000c40c609a446c2d03000481d100510000c80c01c049840f0710024007481a0141d0144080c00a50b105010741e162a281c403500804100d048800030840c1840d0106904c624000314000b07031a0000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 646244271 1250 646243021 646243027
    0x506011b03351b2104030f08010503030a1b05030f030a0b0d0807030c1403030106050d0e03040e13030302070609061b08190209131a0907080c12041406070e180903 71
    0x400e60800d0440303001000022201002107410544e100c8000903160001c0700701c0c0403060b090600c2c00030030703c1002503c1d10301040b90040c014003140e940031048401124841c10305044e0952100b100c85981044894058080d01020030030041441c0c03400c009600c2441c4c4441c0402101d603140b42000b46504803054003400c40300080c81a680020f00030300c401071507580200c440c0c10604420807984c9240d64807d800c050009007001c1158104a1800e0280350440440c000255061031304041c0240d20301080144500c040865840403042854001c0e8101d80780e06820a1043c801c18599090440281084501c08a43c0c105004c41d00b081c001d11402e40e00b0701410405c4044200011501e890342d0194004e041840e60100408403005001074061083d50000190426088100d4110030300300440c00344c0040055090142c548104044950018100d80b603060b190904c0310840e8a49003000c6030031004428281009216010038400c1154110002d21441c401c03c84154801a01c054480f80f00e1100039540b03e00958014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 646245521 1250 646244271 646244281
    0x4360204050106050a110703121103131e170d0e0a150e0901050d150e0c09190c090b04050904060f0e01050108011a0a14010215180d030605090a0506011b0335 69
    0x54ad41c50081c2030064001c881c00e06a101e1104031603020345602038480c0302c0300340601c44001214001c01070f00600c820440c1c1c0980450b403d480b0f6865694214501080041c0a1340014159903000715620141c581802d42d4a07a411004001034180c04990b15420300c10565880001051315028060400142c0d0120000300042001070604010704034000d00d02c1100d001d202c0d01c02201e40c4030311444a22601c2c41521400054001503088000c441507001d100c420001010814000981c1d440111b508441d01a0b481c00056a07503800d141004001500c03907072180c039040420f000c200e00b105422450586440c2c400821400c03c000c400750b003140ca0f40f140b860390420000d070010000074282d00081c640302a4107005807404241d0003030300b01001038001c0b07403100d0801c60f8074503400c44191420080a8211070329810208100384c28400002e9104000a2500c8420744e100c900003409030340b041400480b4208660300c841204101c030302d0050158294082c40c84a0b101c0d10504407c6441500754190201c03031032550041103140c41d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 646246771 1250 646245521 646245527
    0x31305040e0307030827150708060d15021309090203100606140310050904030f090f0f030809010c1506062604020918030a0e01020c04360204050106050a11070312 71
    0x4010000c1408110503854002102e88460200c2e41226924004e031540e207e1202249003071544c05005107040050003c20072501d51a540b05135800315811400b107803111055585c030034019110f01c144041a801240341e002030400040e810040202d48202c094130311080d10382d84e508080305c03207500c90750740007511a0102c856131242d544021904458207400018201d51244046401a40d007960218005a94803481e84480c6500590703400c064034000105041c684e140c01466000070038540005007240c84c0c00200c0c0244d42e8000e80d16020610750081c83c50843c603072041c0c40b0320020a84c601c1000003050600203d0fa40002409a00301e080c0444019000301e03640703e5809104000714020140c80c440c00c40f030f558800200d6410000f800c11004503684810880311350400090400391080341d41800b940c10700c2c004000c00e4062074040081040e0302c49c521502c0003185d0071500742611f42c650002e50494a0640040351065000c0300501d580300054645411620b1106803095403400d00c1d10001e840f2040e5450003815681c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 646248021 1250 646246771 646246787
    0xf06120f0a08190f1b020d0501050f01030c0905040803061318052805100b010c0f06020406170f0117030706050f16180905070504030b070e030f0109110f03120408031305040e030703 79
    0x300207840f5039190700b088d07502c0900312a0140e0300c1d610105159001001045500c101c50005441002424055400c0640d528141c0e4080030b00041d1090300c01d2503400321541200d920804a20940e01e5946000b0314450a055480743c405071a40500c1c115500d400f40039512883d010308442c0c0c1d9210006222580c100112034004008140303180313040111041c008004a100c402d0b1003000503024001c010780d07035403400b940640104006c2c3c1d00e0303a0607403005004100b49016550140390464440d1000f02550b0500b0601300f5040d072084900c020084c03441d000c05e00c01045da0041c03159105410400740307040c1c120b503880c005540b0220111403294040b690341c40140462100e80d00825044041810070310309054980d950b201c0355070800c5441c51300265440400b801c46180801140755003c4180e402001900c1c100c0d110524048015a82540104028481440552410484100ca05400880264895071291011381d22035021600d4102101d1800d080401c10745400d202c1c00b00d884100030300a500c7d00c078650742c0c103940c202c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 646249271 1250 646248021 646248023
    0x90807090c0215090d0e0f01080f1009020f030f01080f120a090906090207110108191a060a080114090f070c060b0303040603020a080f0f06120f0a08190f1b 68
    0x40a1001c1e142c0c0a05820f1940b64003035400035000d07140c40da03e03403c0002c184c4a404181c0d507108802d94042000795076005600c1300d8101c61104c504044540d1b840030510480101170340100012072001a00000e03c24416000e1400341c02da040409403241d03a0780030120303510300d115070050301c0c0ca0b000b91160001060003030b4014240c640003418034440705a80c590792001281c075598481e080c041d4002403000208003990100c0c9070a03000c02d0902d00001d0802c25510b02c184901398039034440d010354a01031840303020502d090440b00c00c10003c00c442da58101445000304038100c00e108000c010004000e109038a440c141344030130720881d2415180305842d607500350304a800c00540401600c91966448152a8984061000300050100c903200581e586007182c0b802401070b400245000075000f03180d014004041c024291a642001c0e044901c101c81008135a00c045c00c042180001e101b00e03104040707141c8108a02000a407250050b80f95151300707840200340c425070b903095a00c040341001800312007000140ca001540f048000e9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 646250521 1250 646249271 646249273
    0xb070503070c080f0a1e020d050706090b0109090b0903093d090f060e0d11060409020313110f010f080703090501050c0915180d061118040606090807090c02 68
    0x205807510f60611643c80a090400303451000a002082240c1005491070900048071a400c080b21016030020340350070b400038024041060005054080c000f01d90001f500c0b60303402106180d2556510f14030003004151441d011100407614100041d0030410100c15500001400780003118a01c1684203c41c070160f210030907980590102a18440031044c2c0c04090300110b0301203844a180b41d0381071054050418215030306c000c007040103503200591030b500d80a03c42c0300b445520085000781d0503206000034059000d1a001401a54030210401100412185140d2005800b819101d0501d140f00424032103108240300d201c80c0400e00003105507070741a20031481254008001d01e0000707001845035807454207403034040c0d40d00c054000020072158901d00c2d0407400f480d8091929070941d860308907001c20342841d802c0c00c0e4800c0c500c01d00700c0081c1c440c03c0c090950410083c11030484030050b5a140b855491920400801c29a07602562500c0c2010a07040c0c0183c07500c0c41500e0584e401402e0703551078807072407501409100e2408811 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 646251771 1250 646250521 646250537
    0x12090e150a06050307050f0d181103061006021b0103020405120c01031a0f090a0b0a062001050121020312040b030a06290f0904050c030f090606130902010c122007030b07050307 77
    0x9c0780d15405080d10341c0b5445010400d0f10b01a00c90201403810001802012209548101c05c101140d0000740020408904141428500e50300c1e1006078020702407a0300c0365410881f2180d01e00b40d4140c021030019550700e400d8a040000d120a41300d01100b2110041c80e0725000f00c90709100c2c14075858150020b0340c0c4900e401e44085031107040035012400c001c5c41680700c0c0700480d421614200e000c00040c40007d000b41d0f0500300030006507140014082e135070f04986809400b54030100da4a030065440502c250241c0b2410309000d503984995a0007118a258000c0341c504040c41d03c0c00c0c1011515403208400d0160a56082d1009588040c003009400030035030120078880400391b010011124640c4441c0030759031003070075400300c4980c5a10b407100d040c0103203140007885446c0340d410284c100030a6503100040003640e41000140003803906040e20050b500c108031418007070b0100d040e03903806c0036226600046c2d00b400e1915011442c0d03842c00307613000c41559842c81400005c0c0740319400f80005100e1807042d0061a480038040c40e290340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 646253021 1250 646251771 646251791
    0xc0f030603010609020d060e0c130e0712050c040905060a061d19030303090b07050702010c170d0e34060804080409020406031b180312090e150a06050307050f0d 70
    0x8070b81c800d90040c00f0031921f900007080350062081d080d03a40001b10001031481c08200300381d1004103842c0e030f028221030740e001c800115000c0c0c6d1180700d500c801154801010050303803c0000341d022680c0c10520803080d090307007000700060082c204440d030b0b50700b21145520b809000d00c0789080000c4201e1980c075241900300b4200c6080608100682864800550080c0c50010b5038010314240000d602200422030418400704201210060741d0010882c0c07402d40d00010300ca840041c91041410380c40c8180d103c00c1007024145913950410700e0001c503075981c03030950741030603520002d0210081100c444c01f803d801d5136405400b00d10030840c82c0d0003140b0246c0e01502c603512280c070303168a0307e22a1007260031503005000000e55901020151000c1032000744140c10650421085040940660125039100ca00004005507200c60740c0b170050f01d015680303580207001c400c01031704801e1400c0d040343e42030307880701c043e0052080c141c052002566500482c03c40c0d01803081980c849140107038901a0322030561003a80c20301020390742c91000c18 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 646254271 1250 646253021 646253039
    0x60708060d0f060c2703080703210c080702010e101104031b050a1409042a0308031608010b0d090302032b0608030313020f030c10020a0312050c0f0306030106 69
    0x100b445115041c00141941c0d82540103124a0303500c4800201100301010610140282c030010380c0480e40d114030a99580c203024a400c6a40c442154903c0c03080c94082040112095095000a10000020764840d0b5240d52503000803800da943c0d0302020311482c0c0080f564681c000840750020500c003403010714058685a5a40d95104018016152250b14101006002d00c06440c0c004a040300034262800e00701070014030040061407414016000804031084c603407000344180c0040c040d040c81800001024074400d41c2c0e900341403405a200700c0d010680307050240e505503580e9020b1101d06040c7d510203078140c1c7c1002c08039222000101102042035040d1300c014000c0d1f45d0307900d1500e8451201c0996000c2402040406130a101095481ca07410407044e94100b070082100040407552480740458041700c00750028084980800d0a14101e4900c031a040020102e16940070741e00060040d000350320a55410707450070500b000400c2101d40a440c4103804881c100909401c080d8010061604010000c3c0005240c980e142205 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 646255521 1250 646254271 646254293
    0x15130506010e041a210d02010b011b060b060d0b030127081e190e09010317070c05150910020f0604020d080c0115051c0807260f070c050f0102060708060d 67
    0x21107028220000011034001c050041c9041c401c0c1500003842703040040c00019002c080741c02c0b50000a01990303003048003031106c0354212140b4142c01030301c541c0c0c0d103a640003550300182c0b055607121070003507007090132002d223041020009940344001d150004601080e07654418001e580040119140348020070300b03d1307218040c805c000b0b00740c254a0100d107101c100d82c0400040c0550080a00b0144160340b00d00041001c9800000035005c29484102850758504507454076034030403101504025080a50090b0711749103a85807800030f1140e2007084070300308448400351404907541c0d18120580c100d50b811090110300141005a50402c040340308000c03031400c2141064143c6e0854843c081450340c2c45040f00700400481c10160310340108003860340d60614603043c580c1c8503c1c44610070044c0081c5000e00e01d0024085440130510201e0001200c907a83c0c0359a194000b4041d0425000504140c035240c920110024503440d00310a200803031801078015102580d60000c1c03d681007032000340501e41103007203d1180c00000c0c9600300301b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 646256771 1250 646255521 646255549
    0x904061e05210609071a030423010905010207050a0b0f042a1d0718060903112209021e011d03190c030506150303160c0e15130506010e041a 61
    0x40170250701e0304409040700b85526240c00e4619a04000b8040810801c5010a01000e4144484031074035000d82805801800c900c1405022540b0200b5442c04108001c1407104515000f1000d880b5980c946400d0840c00c4000ae5030020050a001c4494186030790003920700082450f1000718180d0010b680d2044101811120740071000a00c0c040010803004903003100640701408120b00c04040003505004020b0b0422035180009000d4074070917200b4090360340e5030000d880d406c2d420700035014a9000d01c0c140380074080c1868503c12403041010030366008608100c43e43c00c02034800160b4903202c914407243d895030160b1080b045025018040c100207400607451040e001c0e92041c2c0702e001c012803190b28509007076042c00409401081074024181f40540c02c0e82d0004152501d801400f15031400da0f0501e4600b03c00010309985c08102100d43e42c404109501040400d131003a05081580c12884561203082080120f07102140d070503012911126041e83c1506007907000003a4120280c9520a4804122001502040003201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 646258021 1250 646256771 646256773
    0x15060f0803071718010806040e0d0f1205040c051e0306070c06051e070f020f0703060603031d06041809170405031c120b040f0905030904061e05210609 66
    0x2d4000c1002000720f24140e40305451180c1c00c1c20080368004001404c42c005a203a41000250300208011703035116441103030701e0b007545001c480c99400103400c0505240e05456030300300400c804045c80c240344c0c0054003c1600c5164445281c03e0845d041c0020030184c09441c41c4ca8546050303010684680c40d031400c109050240a45442d0000e40c410746203002d8040d5100140380d4024840c1c03501c02a44440c00400e44203402c48214188804007100b688400c038a0a025650200c8052207454400001d005c0c0c2c550149003030728000d5440c140c000b2280201401c2505d8130014050300304404000c00c0081c42c802c14243c107a0501c02d0703040440c0b20142c5840b0080342c01ea1a0080c0d80311094001020080782ca010056426402c000803280c04070318803070301c00103041414a410303e012500c1d00c1d205000000e80d2541d2018400100000081100d4031441c140156079800118200303024514200010889404d03040881c110088429103025045051005119516079104c82680001012403810f030070b00b20042c0452449620540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 646259271 1250 646258021 646258027
    0xf010b030705070c1e0909020603070809151005120102193212090f030f2a011d030c100e1501080d030513030206070804380603030909010315060f0803 66
    0xb16032011100d105e64040040c4c03602d00151280141c07104010740750301c0b00c403d0500700c1c01a03503420038141c140303015082c4000442c440c4004101110074629540415260252038040b1071025207003c0508034840e110700d41d6080803041c0c1c2c108120a10594084960148419a00001b4821000180d10000d941d0490284084003c140c040c1040d0455103000e6000c500c107002400c4403020401480d0716481804000c0f02c104c0e100149150f4802914000c012440d480600f4002c000340005200500a142042c0001115400212009644030000064a5121384240050000898403a0085000f44054120040e10340540e0343c0005012004d968490700a02d07a600184c40900f02c0c3c08401012944000c0110403400c010030000e41c00310f03a0000e40d583c0e0142c030341d09041e612030725942410300021501d0b41000301c080044220550010040b44c00c2071003a611071942c400c001d41c030f41030308068403070041d04101c9401174110001080407508001c010501d038000e444000850365201d60243d25661925004044298800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 646260521 1250 646259271 646259309
    0x32502100c02011a06070209010303050309030f0706020d05060915010c06061205030408010f11220905091014040807171905040810060305031c0f1a010909050f010b030705070c 77
    0x400130301e200303410040303900e58030344003007640050342130b2806020140822002000084402e441081104c0a0080d04002d50707480724101e10300750007c0d620501441304030904000c040750b128142281194000d1040c030a80c5095203e01c080111910342e44424280c80e8103486880011f0b460040303c0344145000d0060300990307611410004c0aa0945010001d2988158070b030032100302d042080d070030035102e01d0061482d0130031001c010340d900728103000066003148012134980f405211040b84e00203451900d0860040040c4040c884400c0706c0030180000b204c01500d00d803001c00c0010700080301501281e602003040d0001504103640c100d41103c2c2540400e13981404076500040030301100e0003c0084180c1882e80b208140099421a40c580d900c03070007091800c0f8411070301c0251100200b030b110b412000f0100e56903c0200501001104460609214400c00f5400b140d42200045809101401468481c01402c18110b54903480d22001c20f115902c01810401000410700c02c510000d079010101d00c004084111100340b44501d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 646261771 1250 646260521 646260551
    0x2f0d0501141e070f05030703230a06090c03020c06040f0c0803070609060f05040c090b060f0d020d1d1b1f0201050708011502070e0a060b0f0c0111032502100c0201 71
    0x8080c2280f424083e454400d1899194820116035001a00d4640420599142000390040030302c102c0382c128001c100e68040004410013980101d0481d00303804d200740702c62401403100303500300d2061000342d242c5500000001808120158070ba801c1441c403d201d4a5007003580c6125460075500010f0302100c40641b1000c02d04248100c5001d00700402d400f50f13000704050b0400741d9518010072080d200c4c03020490345a4a00c003169035109000d441c002e0390b4a070b501030b5541c400304001c0c4000b5808210006000e07403030013041c43c2440c58000c8459075407104c2d501c000c0100584500d01580d030054030010b50340d800440404e003400060707c0c042e00e014064825400210381c42c204604042d01400050304203000142200402c030049a42c0080ca040848605815980e010307290301c044840580b4168004001840000600a040206190040200c5007011000304401d00d010340c03071900c4ca8030040c9c0d02c2031800999402c51a00340e820441c01d029141030240102c03507541e080258a01e00781d5000c05103040245c4d644154000f001c0311 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 646263021 1250 646261771 646261831
    0x8060721050c07140c06070602040f06030c091e050d03050306041b1706121e07050f0604090203180106150210050115140d0203040b042f0d050114 64
    0xd11000e010501d040102d0305040e02401d0809000d00d1404460001c4900044c40074034403c0c00040e2030781e40e650419046c0040a90f2140c40380440c086c441000005915100b4420500101d240380d0320a202240b1b85900710b0542008840c107590b80b04404040010640d559040f043c504511a403550b6480f480c20404000481d1159a1030010071819960302d5654030b640001010b402d03c042400201c01d5880d080c0118034100b000c008c04030194800e2000100c4498040c800000013500000211602162940180301c3c0090a40280c981c00c10340502040c0320a00c820b401541d0b100d92040018210a641d0072002400e4500c00c1d80441962450035418818950303060001c2038914003081001e014952500c0d545004902d03408410800304a0b0082c00801c00365800001c0341c8400002203425500e904160528100401c1c003607408842c0324605400080500b21120742815880e2214181e8200d180a40e400b031015074401a07004442a55840e541e1010f0070382ea560100340252a0030031700071141050000e8114243d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 646264271 1250 646263021 646263077
    0xe090f07030320070e040602070c06180302040e240901110715150305010e0318120604060b06040314030a03050f101e03060f0e0d0311031807080607 65
    0x60031298092020a42210600c0003a450048000c03500300090940c0b20b040200c5078208040b45003c82041c80288007994000d82551790196819809103540d44000340c0b100d060811105011114100c8100007520b4243d0246803082950010780e510118240054602e10f9080800307502e484244205100380803c007480303420041f2129100da11b1030502c0d140c41382d0741c41c008010750340c0c2c0c10243c5400344c80d038427141c03c0030760030004682c090b00038804200c000b456180c4039002070b581f041140e102c4503000029480d1048a104074841001e0107085140c42d103459480c05084034201054200504010000002d48074040345c02d14400260007075a00d800c514640102507072000307080c4010305c000280034095981a842810300c11542e00608041c442144071a21040040c6641d10240000b45000c5036420f201c1c0c141d80007502401c2c0e080068900d02d5007003480907002c5a154000c8818081300501c0000c1c1440e41784070b082c5c03002000f028100c0300d01940d162609803070030004461410014403800d00418410105c484400041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 646265521 1250 646264271 646264273
    0x90f06060918080705010e030c01230420030c10051c2c010b04050a090b07050c0c01080903040b0301030503070c0f1a090f031c2a0807080c070e090f 65
    0x1050581c190914500500d40c00030f032581c80009490010440254425907801c00d09506036a00e408024103207500a01c3d080103190640e1803854510402c00c1112441a4402c551111901c1020742e04018400b60806007148426058458041001455a11200f40d005680c44a555207941c540101880d4461003034200001a201c9041c40200907418080400000110311615480b80702e011304c217400680903000c00c039801c541040c988400c0c06491030301d640001303113180d0088030700d003070740d40c4030308400b00c40c01d10520070f003042140c000f150b621100b5846452241e0b001807080c0304690400781c49110428295100ba40100d07080d80c400640c0d1810040a1b00715940184003004600a10138680040d00c11038003034030300c03054030103410015024070141d43c1d0020050018030702600716150055404c0c80b541c20580480d2506011558a18141c041304141c2002103824102c11081070078018896034415600341c2008604640030f44e400d002d4204029001c01c001c800600780710f000c4141e40c0c1404560107050840d109103070034803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 646266771 1250 646265521 646265531
    0x11d0a0c1e0b030a02131410110303060103110c070902041815120201030e0604030e041415090601090b030f04150b0a1a0d02190f11191104090f060609 66
    0x2000780e8058000c000c940300450140d5030713555098603540092007003401079008050062404a6025480910850b80c11720584d503825401e109100113540d202c0401c00444065441040050340a51103904043c1c0e85990704c1000c5802c02c0c0c056005282081c44641081000b15408101007041c44802440790a14901c0d80034100405e00b84281801418900c1c0d004100c01010511188403c591081e0b10400341441d066040e100350b4145450002c00e1044441940b0348540e042c0b140c819080505852114024814040f14110060710f15003403008081c80246054180880c1443c006521151800103612a0701490340f031a0303441c40c01d403a100c041014080598a5160b180c2032180c240394031140c064601307a80c00d03113000803100464015800c01e03d116240c02d1506190000c80c9a4003112907212444844484a4076100d0100e4000601142c0f0b401c5450000101c80e809001074040355402d04841d54512806002140d03603065a101c003040980b00300c1d15045402032940c1e640682070000c18850f64000c0c16071600e017070203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 646268021 1250 646266771 646266809
    0x804090c0e130f11120406060b0f071209050d0c050a0b040b0412050111071214040e1311030f06060f0d020d06020a0210060314060f0c0d150302030d1101110307120b03011d0a0c 77
    0x905409002f1006214260000002540d50b0003000064000c290040002c22030041034038002030301c0c0c0f2007885058000c070710940020031034086403815503064038281141c1c9400c06140401001c800280030b403040d10555a40c00200c0c2c4002c40140003840803a0207042107081e00030a010008010443d802d42c103042800d0140000d00c00e00280202d45030308001021a024199030315400c0514030401900705990381403284602c1d1a00320007010600511074001103c02e100e00c44864014400c941302c182c0d20007940100003021941c0052555400307000c2c04d54243c4101e90302c0307040002e10760085840d2a0800e0b56501d8903158612000310b010090f607030340b048414800c40c09600303148005000d14010012402c80294440f41110803c41c441a6540000c64000f001c907400840d811501030070100360450003075038035400e1809007000d0103403071801c42c0e0080c483d554032a030000c40400c01c504010603c1c54030086d07055403185604600305154000342a2070403503010107040082d41c139140c9450340409603403083d070a0071030170000300c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 646269271 1250 646268021 646268047
    0x4080310080615041505100207060306140904020d2d0219080712081306050301030c1e21060f0c020c030708030910020f0304030804090c0e130f11120406060b 69
    0x481184415600400c4a040c44440e00782c41117184e4100d15000107140c0681c4c01c403117500042110031217101c1d49007001140c0e100d140c05904030454080e910340205030395000c07a005042000384480321300d002d000380781d07155107640048800e0103240b030418914441e44000c190083d840c1c042683d161030a03020a50500041c549114141c076030796641300c0da2840030103690340807003400020f20460351800400980040143c0e110207002c1d0143c2c0080c0000d4404220002c004624200b4032110045221900c0390883d511030303c0c000e0a00c6039100505070510382d86003810072000c000741044c0525021904034060100d8440a060402841c050100c1802e40c425403040c0030801c03541102204480359180c0030b49155002c04aa10010782c90100e415590141520000400005000480780030304295218034200340214071b50aa011a0001c140740c88140c1e0010348000e0300c0402c8030355644414130003a02000c0105004481c0000800c69800135044c800c41000c5e84400c0104200403482813002404640000d0b03410401d94007002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 646270521 1250 646269271 646269301
    0x213030206160c03120807110303010b13080d0206060f04060b0f07050a0506010b030402030d0503241216150807020a030c020102011b02030a110118062003040803100806 74
    0x81e00030000000c403001c030881020b40d00c02a094128602c40460f03a80c4e4680850340c060721240c00c20024203004049480d0502c6080e2181c0000d050b400110b04690030001e024202e42d00c81300c181003d87c948200006140341040c0840b00e001c0e81d07540c016112900d0f0070310a1105501940c00424410b900c0c2180900c6203a6004042d1214103401c801d420352281389901d0520f2070403010142c040e003144592000020020327050801944a24401d600343c80d203a00c50b02c0b400340e6507400190740d420310540801030301440500507081013007540744005000c0012411200001030814100032104982c401c0d9007c001d000003510740c00e0b201d0b001800c034904141c00e460704203c02500e8820f0300900902b00045c65401c074055a100350003214840d5408071032405101c2c110140690359912180c00c2c500420900302d015504080c040c4a40a0803141d501104120110140d4404000781100d1710341146802c81401c03001507204170031000c0c500c00d6218240071aaa82407519000ca00d00744190b000749280c1d48060208102c01c4000c03110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 646271771 1250 646270521 646270523
    0x6041203050f0403050f1f0c08011809150606020c0604050a0515090603010b0304030807020a05070603110d05040501090b13080409090302010e0a1b060c0c140105070c030b0f0a021303 80
    0x190b4849000d8540011980b050f6070000e02248264841042481c402003003074108140000f400c481e0448902d000d1106032080100382d10041100b02004025168034202202d0241c00c01340745c00903c103d019514200714107504c0380711010740c996500d0284903e5404210509407810f01326009030805180500049194500380105030088600c0108641d2018144040c2c41881c00000d00007510783d0785800026510780c01c100d40550000f80c1100100313481c0d82c00840c20007002034010000c1c140040c102403050b0068004a544031481d1201000714036403010092084c603000300d11407000410361030b0250401450000024120103101d550340082c10f80042c0b4200120780442d40500800318000003e405d00b03a0050810b4035215099001d002d8800041040b84250141781c0701b0b901d0000c0c482c040d201c0c40c04880e035525203c401420218085014007084030004001560254149401e0346030640955401054030140c1e03104807a44e40c1c4100900980c013109a0915a000c420720f0070440c1811504240e00c5145125440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 646273021 1250 646271771 646271777
    0xc08090f0f191704060804020a1e06080705070b0f040c06080c19030902062b020702030c0d02030a0c0801020a030501060c050a110a0b16020f040203060a090b01091710050606041203 79
    0x15000800c40b10f10466001000c42064080d12540e940c0d00240000740d0840302244120080703000829018014400184104e240d00560460309051030000d0301e494001509200178014140a41d10029007141d600a10030302610f243c03039460381030500e401d1099180b59000b800c10310100e007080108014092041e114100441c1c5410040610086006e42c001d0006050194000300005541542103603451000c6100f0241d81c20080014031004181d80120f005180c4002c0d8160004940c0100da072511222400c41a03000038242e5040b0f04690390b600c81d004030079500c0710306d0036500800c1c1d8000701a0140708840c01004c00c0c0c184041c80e41c401340d071071a84076104204018129000d81820f00e41f41e442d216160000b500d0512003503659540506078005460001100c200d106508a0b04040024205802502e014143c00743c0580d0419090410800c06043c011910324100100601c3c0001c01081e080d400285c520340a0000c0c052608800d60300c9000d5400051040d80038103c00c01040103e045400150011150140303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 646274271 1250 646273021 646273063
    0x80d050306060d0c030b15030105010e0f0f0a0806160212040303030e010f111b010b210309090403050d0b0108060901090e0a0507061110050f0402010806040b040c08090f0f 75
    0x600040d28502405900c3c0342203502d040c461510080d050351103840307181002c481ca03201d06100300c0340c0c0343c110b071100f4043d060004809440c0640c4a04000003100003410b0001c0c040703048501c1d003601203107840e50503a10000c901d0b4083c10a201c105424800304540d0062584041c203038001c0c8451038044c032881584801402c06980b900348a038006c0007035001c8941e038600048107201a078901c210092468004040585c8005138600361502000414030a500c0074420140450001400c0e804030f03807030040c81c0d90b035507175095010400141810b5030301d88a00074820762182d02c031036448031043c0481400b00d801280d4901c3c18002c100d420301c5400d41e500040f550445040c2c0300003241c44401d170402d0034240380c0200030040c568820301c8400310b030641d08640086407804605007111801880c805144050382c40665001c4501071000000c40c025510a1030030320350001002d440403c20242680104c1c045944111650300001d21110174058018003d02009000030400c20003008600c2c4580d545caa21418044540d90400c1250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 646275521 1250 646274271 646274281
    0x307090515070b24030a120f0503091c0c050d080f0603060f0c0c071a12090a11060904060b211810091406090601090f1a01030f02161515080d0503 64
    0x48241d0608800005d0242c030000c0a0b42d2030494480e0814041038000309690780c9802050f5440350064034400e503d001c3c000c0c17003415184006480c03000f843c1c032600020041e400c211107001c500f0401014000301020b90303580386140b624200b4403150340f2010380420702c030740c0003a018050390f0084220242d400c240700d1014103544843c0e1611551500c2420740c4100384950b20b05d0442e5110f0061070010f801440c2000000c078000380e5900c038201d40c444203c0c10006250581807110392010b41003590150101c44800b030400076400e5107a0800500c0d80c1c11004400c500314500761094003040b001d508040e50000b500c0d6440700701c0b1581c0d00600640b50f5503002c00040c07405590726074a009006800954074098507103c42501c0700c500704040d546803078940901921500c1400c1503180380c11860244100404d146036408010305000d146401100900300c0c00210040d1540c00f8003208085802000d0032944041c461941140740001907103488080c0c0d00000c80f460740070b4012040412050001103590800044685001c5030360340d580b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 646276771 1250 646275521 646275571
    0x1106061207180912030e0a08030c04050604140310050c1b0a12050406030b0f09070e010e130209010e04200703022b0e0405010b0d0b03010e030307090515070b 69
    0x566102c041403800c402030404821140740c0c00340074018011002c0001070004580d05405440180c80580501c0d80700d903a00401003010030000c0c1d900003002152462134280c0d9900024001e400c1600000a0a000312044c5d10240c9001c1000d0642c0c0c0031056001c1c8200d2500c02030031034541c003e001a00c1819500b1900c0d0501411080c014500c480785e04c528451342d4404403200061107504540078075004a8030b00661066a8500304100704441ba00003071099407180c1e619a07044544011014a06040c40304c1c4020004680d0758900340c907400009100c100580742e80c4180001043c0381c007644842401545000307005a22024041c0c401651090140d0707015940721820300e0120300d00460400300401165005d090b4a08000da401030103411501541d40e06810082002d0400c42140c10038420700b00d0b080001c10000e204c8034042d41004c1002c80d0000c00024000c4030480080d821a80211002c00008031103140c184014902241d03400c541001011101d428981180e0761301c56040c3d005400150340c28001030ba00c48040103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 646278021 1250 646276771 646276783
    0xc011a13021605160806010905090a020f2e0e010801120605040f1a01030c08010c080403080c070f0809030f070b0d02030a0902062118060c0a0527030d11060612 70
    0x2078008201c91813003900384481c4c003030350341140140321240c0200800058120000d014440c0164100d01c068000040da0f80d0070401c1035810000e807d0380000707038890444880c2ca090100700d000000c00c07140d04400b106000c0c10041c000804215020706005102c07005210349a580c20b0b01d0307007080f1b0340550b0000300c80d103907400c00a500c00242c103001040c0b8550202d45001d00b1140c40c0c4070604880c030451001d01401d407941d140a082ea41c4050000000442380e90004020902c5600c082e600a268404c0c1c540c0380c048541c4940491010404c81035500c11400244a81d50741000c02c64885004040ca024290460526490401500c03c50303c0000c0b4498002c030106003c10074a900030900740d507008046070303540c0c05010816418610903644030100c1c0d400d80800140e520584000296840524801900c107603a40d035401900103401c40c2100e94100407044c0301d03103000396072540c040b5214444541d001202c070011703600c00c043c90610202d00020401c0b60940c403038820780a00144591704840102c400d4084030300b800c1c0107507240038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 646279271 1250 646278021 646278023
    0x30212030c0702011404052d04020c01020c07080d08041401110d0902010e060c030412110303030106090e07031a040e0127021504030222150b0c011a130216 68
    0x41000018080800324000041c0b01e854401c0c3c88185020f03029181040a074003540c82840d80145180800300300d920a4044800c940095217880f103000101e028001c41c0c12600042d1100702f050303600250129550400300203e000a100d0340000344020b0b04a220020300051024000a1034500000319031112a4030031b40200800c4150313030009503150031080d81050003400b203c072020b80c00b01d41070109116460512070104ea858829207002540b400e490f01035054186203260b0003c0d64800000341d1892481d60702400114000c200f25520610a113003000e1106c000c03142c026142d90141032501060b01800c07001610100c13016002240c5c0050401150303003e2a02410315500700d0b0000e00c0822035442d0050300f2588211a0540c001c2d144030b040018841c4160040e445940000381d4482039524102110120745a42001c40010000021503030791441c1d826400c0c00503841d040403418110100d101c1200c8442440b40e6802c0c0c82003242e85020020200020610302034440e4036842c000c030b4000940e006680f460030b903130807240c4d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 646280521 1250 646279271 646279303
    0xb04020901020a02062809150305010b1606090c0b19050c0a020f060d09031d042003070c08030f0f0c030403140912160f050901080c041d030a0206090606030a0309030f0302 75
    0x181b08180c0300140740f500350f07000d0100e0340e40441128400d414840d1081c00d0580702120714051402c0040180c81c0000e408243d0111081d0303464515a5001a85d003c01d0b805c01083e900c207519856150044000c00034030b0080386410108071003070140d5429040d000400580700ba4050b180f80e114441100017081c403d22885140c010110300308120075080640c00820282c40c031640402ca50203124400b000c000075501d5109111442642e0342d04800451000ca100440d003100040c203260804a66503554400039410484011514508803010403c0b2228800e80d160383c0038031200e40c22441c1d890b140c0d9000d1711100b51000c45198515001c9030860300c80e1607041c100000c0420000440380404030001d40c5c040c00a1b07a0380600341300705444017000038403410492a82810703203550030054041c488400301408000c0900c40701d00d042c60400021001c001100c1440203012a40c0e50b43d0191032145000e00c1c14501d1301d40c02070300d1180a0381c0816020804654841062015a40d10074461480d490703050404070710b40092101a5480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 646281771 1250 646280521 646280587
    0x11090f010527040f1103161406090a240302030f070f020c191401050c030f0c07180207060b0f0d08030a020d23100e06060c071a0403060b04020901020a0206 68
    0x748615229030b0103240784203070701000300745c280e1600703142e1100140081c0000010028505024415000700c9400e8401c03405002142480795400000b41c0c04442540900241006403508219218006905a8440701c1c9400d065240d070034098558842000c004003441e00b0000300e0b41d50203031070610174001040d10120007041d0300e442c5901000203034000c4100b840b50032050803242c0110080d6500030802d65483c8944900950b0400805400902c0d85a20419000310103010300c103030108441e03441e6200d120010300c6200005031190300e14a04a000c030f442010030079208403801c001c2d0b620950b844800e0060300c0303136016218903202d0b1100020341000e401072140300e01200341802d450700b00c040c0410000741c0701d408c201043c200e02c82d2034640e4001c3c1e0050441c01194406500400094681d0802d540100400c00502e01202e104580c1d80811310742c10b45105c0d643d1171041d01d001808200f031140d24000e0b00920482280c0c114504000c04002035650340000400038021103000c120102d4400c440104007010801d25600041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 646283021 1250 646281771 646281773
    0xd09030c021f0206060f010203030123060a0806040507030e071202060403050303250f090e0c070507090e010b18070c0206070f0803040317040201120f020903071211090f01052704 78
    0xb402070044460801403040b8000558185401045000740c4201a006549143d082004200840c024131000003040411203a80403529200c000c014026120785649001d040e0424400b000280c90380900350604044c1800c1c00d030100c84001240d5903040310074060658100640f140b0205005005640c0040c09601022042083c214288040491240403039070f400c0108104588090b07031041540c00512000480840c028000080482ca00c103800c5248845160300f02070480c1c0d9030506e00180d6800c50036116072240c10b5120345401c2400307644440c0c43c08071608bd070244849000d800d0a01030003408041000508007443c000c0d0b4441c41c0c2250b840e60f4004078080c003180b4103030070614019482950200c0000741900704208030142d180e440903004903816540c0245051401c403429004e803c8032000c0c2d0484a07400c1080038802e54041202c1002801e00b40c11600402d1802d04101a858881c545294090451030003000f243d6003090300285d055403421200007210b00e0603202120002c4091b00d00078116264034800f844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 646284271 1250 646283021 646283059
    0x18040209010e152718060a0b010c0813080f01111210080607023d050604230115030225060204032307080c1c0501330f0501050d09030c02 60
    0x790602d11184080c0c40640c499840c01d9174081c1741010400c02030341160020904c0d1015036042148241e01c149403c0d21182655141c0003000e5008800303405180d20007080c02c000041d0103104e54602c800c841c800811181074030b1050760f040d9104170360b00da004401f0500c0001d600b62501441c1071014104030421581185042c040282d5210514043c6195003015199a00903800542c0080c500040f41c0b0170f071100d4911455a06400030340800b030680c80d4807a80340c501015081490024130b188080c1c1078804c04031554503000081943d596034010f140c0826004004420000f00c0040f90303201c1c00d10b000f410303181201c140c0b802d040d0000d0003203410003001c0000060310014951038288601110740004410358600d5580c40d21125991289901ca01d030704503565000114110040c0c1034a00282e40c069000803c0d24103440b104080f0b8401c1e0b591814000182a001c605450442c1501c00c4000d001d54400003e02141000000791113401460010000030fa2641c04080405220711002184a075028040c11402900e80d2070ba1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 646285521 1250 646284271 646284319
    0x121005180a03020d092120060d140907050a03080c01020d02280206070f030e0a02040606020109030f020111030609040819050c0c01030b060706050c160506040218040209010e15 77
    0x7000100c03030405c081207201e4189000680f422022181003a1641c80d591944140302141085806601c90840402a1900c0b07c41c02400d240c1d00704003001400011840c1441080342d07014022402a502c024401d000da40c0f00c4203a18400d4a4000c0666511406416142d45c0a440390b5841607440600109940d5090704c4944540a024400200b040c914510b0302d4008a80e200c404480b5200095031540709000007500a40c001c280113214042554610202c540100e030686103240e0008005039511041700d41403540c000071104103080c1910081c07002d80440d0082e80074500000d42114402d6540c0404201040350b550b04032403040703044810200301856814800740103904590036040c000c1c05619007810a540c400c0c41200b0b5200d50090000d0b0a100711030302c0d031800602c5c0c01400d60101c84801c0204611400f00d803013901391024410802010392345403a1042c003142e0755200409120714200c1000b44401a80c800c081a07042d608500a0b900341682c49401c40030400900d44090b40d000a010306002d2003d081d04844 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 646286771 1250 646285521 646285543
    0x21071416081b030f07090c03020d11040905011a0d05060d06090b0109051b31030f020f01030513060c0e06072102030903070b1c020d0b040506121005180a0302 69
    0x1901001600e440a064545107409140c0340d5541045c07000b84003c10540e03012203240519850018145000c110700c0c2401c40e620101d6100201e01c01081c204402030080c0102c40c09440804400c54411700c1c980c1148030310f4015444d81ca550300d0303103d0300019400d44070041e105499a4100c030083c400f80728130f41411494100c1c03c0c0909400f26007010000348411441c0385c0d101041042004200e8a8062048280072440c40429101d20080c030803414187d00e04c2c0010305a8902031400f400100740f03006118410007442d1005003980303d05040c01e007804c01c41001c5d0310441240714140c010402040c00000d03100c04032403524a0074001030f41b1103004102d03081030160380540e943c0d036512020700a0701584203854050742e0301e000c4d401758541c0c160f002d40024044c00c6400c6020300010032507035801c40301d02d240c00e141a00c280d8100704410990f4503034410600501d40303082c0c0903081d004041625a52202102280f185440c0d5032280c3d00c0c040f4858030303080403600c2264403442140c4071610034810346000445034a002922120000c078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 646288021 1250 646286771 646286803
    0x109290304060e1c0c0b0a06270f060e01030305090a03080309030a090914010512011503060c0323010b160f0602030108160815090319050307022107141608 68
    0x2208407000041c0350400700c031310185911011140c800759580c0c104064802010043d4203030710344100103500302036604505050391000e42c1c04101160a00d01110485000000380c1c030b4001d00700038080000c549117004d0319042d20380515041d07545400d81d00206111400300d90008140140c004200592030502201800e40c0410b680d88810300d180d554034440313080d01c0080d295030041e803900c1c80c01005645082000d40c1000c8401d000080351200d0031500c92001c0202ca50300584005032107a441c031000e25454450b0046041c2c00c001c0c03424100403489150314046805000e40b100030100080d00980b038001418550342e01d40d6101000a008200d2490114042d40081c404c07185144260307040a040134414405200c03d9070300712001480b000305900d1102040080240032141140400c11901d80c003a501500c521403420314548815941e070400c450b009282181d145c100b5081074111682401d515441c000c125242c0d42c0d0000c1e800c81c2204500b1468609000921b044031030414680c1e100000c561401054000994403090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 646289271 1250 646288021 646288033
    0x1140c0901030e0a080a110709060815012315090d0c030c050d03050f0703090305161a04140402130e09010609050a0e19110d080301080c0f0109290304060e 68
    0x9104680d5a200e00c0c00010404c10007403140c07400151003400e115043c0507c100c2160390a50f92090f01c81d00301c419a8008946640004036210101789011101a004000c00592a0504140c98602002400341800924411a4650b02079841103110200340c514400c0010b241001c0d401581c5046000304c1442c1c071040b603242c040c002c1c0004940c035003a008111348070780540364540b506441ca1100c4800d5031286400300d007031056248010000c00c0040181a446805102400c6106030902100803104120004030016921003080103002c2c405403480038017000441544c3c0580c80780d0b001f10b81000812041d0300700030325100038841042607400054111000f1281524020851502e0b144102010780710a036031a0040f40d0300540320801c112100c101c19040c05801496600150b8080030000b400300d040e0a5026112040084010f0040c8841030200b017644200071900f005110000100107000c40362107108040802d2061042200c14088080005c00111402c0900c90394a180914040d401271500a4035008241324038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 646290521 1250 646289271 646289291
    0x210908010f140a0902040906020f030a0b030106060210020c011d030d05010f140d020a0b0313050c0303030103050703030809010f090606030b0604060807150302070c090b0907050322030201140c090103 87
    0x644112200d50080490b1051143d664554400180520400407a00300b507484030810301090240c4098006990303000c0040e6501c1c02c10000a5080c4c5180301840385c4a82d242000400c10550000f50f10418a9116580581c5440b16076a1540c01001e0300d00c1751400103001c03034401d11603100c0040001e0115070b0441c036040000da40c03142074007200b0340880d001b03400150401d503c182d5050f02e0f00681d14441940b00801e80d4101039120b200c6462039800955140d800c0546000d803600400c0020701c1242100171050b070007141550f14540b20207a44400b80d11001d401e00030060082243d407403085d0088060340c048668140a515154980b10380140480d11041d40c3c810100000714120b881d0500620b8100c420040c02045001d05064a0a8140b420a83c984051560800265000440e025030b1240180b451010020704154440288141d503d0000d015604100c010420001c150420954030b5446071b02c0c941000e01c4c0b0b02c519241c1a401481c00c40c0d001d2000d40c02e1141041101c2400070000d00d1552801c1e44e09005c90108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 646291771 1250 646290521 646290551
    0x90b07090b0c1e0a060c180909080306210a0302100c080415020c010b270903030c0304030f0e060d0b0a050301090308060f06090a06020f010b0f03061321090801 70
    0x3108142d11603500321005450f01048080b490007002e00ca00300c265600603040e580c59208480003c685140401c180402451424034919501c400501141e241441042c0040e500ca0b0958400101316a214140e428940910022804444000e682101702140c0c0517403603d0502039550034000b140350040c1418140d01c2c0303400c584601c4240c1d000700d0340580500311491030114848080d401c24900c0560035035a03200c03010010381e0f4043c44900807040a10402803480490401e51242010040c0075812650080082c461100c0070541240e600c1609031078001c00d00d0702042c0c2c0840b455601c5d40702d0154028004100120200015030002061500480340200c285079034405240c26980580c070041c0c0032030680760009081c5d04100c0200c00b4081402007005152190300e00004100702144d0b00f100700142c0c80004044240d01d42441603030000c0d8021218101d0803442240001d03034a40c001441804900d1040d091030041080c0d50400c40680c114158070040d0700041060014001c03000f600c07491030190b081080e80120466 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 646293021 1250 646291771 646291777
    0x601060e061b011509140a060b0f090103140915010e01062307080720040204261f0c08010e161803060501090624020c040f0b04090b07090b 61
    0x58540303818444000c1c1402d40b0104070507050581952940d01d0300d44544482403e80c0301400500031700183e81c201d40c074a600483d02c00101142c0c207003898100300380410b6072900b00b81c441340310000e0603180d41c924182004070007800b0404d8118164200820034080e0140d004520f4a00e00f1140c21041507650fa03030b503040b80840e40303828421880894034846409503180c0044a02081440026000c0c5280220940c0d45e2402507001e1041030301d03070071510300c40201042e00700590503a124500329825400c2900300081c0320000c11001c5400c25003000f2003501402680340a0108011070790022804e01110340c102c100e51005081d030007480c1e1002511080005c1501c4110405c42405040c0c1c2e4801e02545480608003601c40343c040101c5000c1c40080b010001000034003a0003210b010340f075290307800326501d40303045107081b07070004400703202c28094000314154003e55500044281c1c1c008030407580810078224a0700540001c007100c0607035640042c20000c225003800000c00003140900000e994a03199156910945a5240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 646294271 1250 646293021 646293047
    0x150102010c0e0409050c031510141e030c0901030501050117030c1e030415031a010509030616030e12211003020d0804080303130c09230c1201080f060106 67
    0x180c0b00740d4426415040c554130000700340d8845c0c0125401c3c4c41d10003000929000010070045210802c0c14104489813601109040c001d00d001ea81c3c52280c8482c1c0000200c00030400b221400e446802101c52a9090f5810401c4500c1c0c10b0303003d0060f0b1310703a507164240b9030301801c1c003401441c000080c00c40e40b00d15031900c00000ca81d5544d003410064010310170b080c002d409041c009003841403090b02c41400046100c2001030307220400900c554400107981c41c201c01006071101002c2e0a024144142808400c525480c04600f46500c569480204030740041c0c071002c11f5004244501c04080c1621400301c1541c0500402070043c511040d003080c16980d0b072522103408508910b0102c0782c18650f401282401c00040c10401541d4110601c1250f160342000d480d00605440e54204895110103268040d003d501440000031817040074021843d000c0c8104072802494644030500c4644600900c0069800500711040303481c10b030341c003008001d0890303061941e42e54201a035034001603003280305601400000058a9010b02c210001c41c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 646295521 1250 646294271 646294277
    0x2060c0f03040212121201060f0e0907180f03140705150f0702150a020604021f0219110409080d0e0307110d1b0b0703110d141606060e150102010c 64
    0x10780e01d0b54207101e15464404100800e5205c0c0621040050340250003038460040131103003d82040d0300d45000104a580818204410700803008034041c52515440f222540c407195908140290341820b600c1116946d2013544501481000e0004c0030081003102150900038940da0310813110303401c0d10f4004000c2c410221518680441c13004025500c451981d06000e40a00e900040510150100c1200460388551180c2c44c0c0200580082003080114a882c03150b201030041c02504040ca0402c0188010b95a81110004144c0c00e0a4004000003048070b01200f1540088015006000c0d0500174581842c0a4109140c51082c040c104400fa54102e0000400d80d0342c01908200e000245c0300d218000e2004202030b081055400c01c802100300720401e600c50407200000d19a007100142d81d0001414000c0c0310000e0408284500e0300012120309480764402c00421580680c1b500c0142e4500e003c100d800c4211052041c020801741c04c04200050747c0980f8002da501c1040d1040110592403415001242280c00801c02c3d6404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 646296771 1250 646295521 646295527
    0x1509280501150c050106030b190e012f0f0706050906130215070809031f0c0806030a0b06030312070c29040605090f030d0c181a0721020d02060c0f 64
    0x6860f100e440c00046090241c030000500036105d444208042e0b00455080003240b001000d6070051892510030174112110010007000031400042008000c600d15030642c00405820145070749418481e481240c0000181c503513801d40d00c0580d40b030280301408003100c2e0041e1034050710002a02e079100300c0f0b05801c0110340c0146a454800c8a03030459080320341161000f51104071041c806240c0c65101041034036256010040f005d15000b14200d6003800b036929038032000c42005008070a0041a407000903010b491541e000211080542e10794010900d0350203260000a18841d0070410b01c640c4a40055802c0d4016004501c5080e00d0311041c26489640220b20040c1e5006031941400100884c240c1c1e84019008101d03c4e0680b500301c4032035a0811302c5c540181184c800040d0b6140c54101429400403000300141c20050903090745a0318220801031240b00c0c4105081c03100c00001019010480b2520340001440c00070544c06040105111000b5a1402210b8108c0090711a61000c10740204c0e4600a450305006c0c03c40007246 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 646298021 1250 646296771 646296809
    0x1503011d0d0504060909020a030f0e060103020321030604110f04060e0f12030306040c0e040e03090f030a080304170910021005102102030307120c0b01061b08031509280501 75
    0xb5442300c0f208408050340d40c440b4a54510540c010290550354050091140e941140101030030441d0210f500518482c001200c00d140c0e50454041d290702c40790480e00040c0028814010952610501185c6070181c0000034000c68550380110900b104500240c40f041455082002804880401844103200079030003480013030f10501d072a8101484509451400e103c41440d9000403038151b501c002201d600a8201183c090340d1070410b0080021440f10450003004034034041d0b107412007a440081d1002d4003030080a98200c2d5840361701001c4450049001e8140008501c080c400251210078096003440050709180100d11030904920713a00054880c3c00480034146039580f60101076044c541d4100b260940820f00c0340700041440080400070030b0400362a41107080020346000218280160065414001300741240c0316146078041c0384a10350344c0e001d0709480d9079032a442c542405000407500450360042c8110200308881404142c0140e0003056151400d43d101110061001520404d004c0e502c03e8841c441d440c21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 646299271 1250 646298021 646298039
    0x408060a0b0d11210607090e06190303080c04180501031b063c05070302190b0403030b0d140f010f0b13150e1e0a020a0905091503011d0d05040609 64
    0x15104e14040c041401103030650560301d414120200c50140c041509564200000e40c800c600d442d42c00702044480c201500d1820402441c0710380b10b800017070300b08200306c00041c0042c04130b1012140504042c078011104030310b4012100e80640700900046422100b507450b140701c12041d00c0e80358000d8034542c0c0c64144a220122011804084a101010003041100040c10200d62040340901c041c3c0802981d440c1d6642226040c0603140c03070400440d00c0e40d100321804200010030003056465401c140c2c50b140c041066400b4600085801c08240b201901d032005000302c4070b03110351001070f684160b099074038000e000400d0f00c1150b1030125180c68501130f8200d00c038440c4014149405900c4401950103a00c0b1903c402d80e100c001daa00080e00445118035462005019401c524a072054041d521100d004015031400f0041d11004000403c0c0744601e5004109a00220b0300c4180c40c207001c004614000707002017001c03110303001c1da080721031655103e8900b4500542c946141c03058494011201607510503200e046045103000303104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 646300521 1250 646299271 646299289
    0xc040f021905030a0b040204081c05031b16050d0f0e0d051e0114011e0f0501050702130b0d080702100e0919090807030203071709011b170408060a0b0d11 67
    0x5608030903071721580001e60756114030240002c0c092403002040c138a0107c0c42d0b0b00d10850b80403031401041c40b10034030801440c502d01c030421168084001441a84074031501e089044650400a0002c0481c010003030104446607018810075480c072600d81d21440c00300341c0b00c810300610f148400400b40141d000b90b034031030107038407034003002c0c2b080541e40e10700002840e030b802d111600c8107000f00781c20000401d0012500c244025400403840d0b0041d01c80d0320071340e03007400c0d1070200081c0841c807070287c00034010304402c8000b00b0501044d61100e03055800190100000807800d18025081754040c40301203129022032400446404e21440380d000d51110054403840e4642c859610310a01000645070740d41c41107445900d88400548000e0150a0851094000b035460b504603191443d10045010341c0002007007000e01506829030390052051400e50303801045088a005181809000000c60200c0d40310490800200080c2c030500c002001480346101c10400c1005401e00b4041000003c42030401030702c0d4001e4401d441c001850080c0300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 646301771 1250 646300521 646300531
    0x6140105070c05100c030e090114090a090b010801090212010203060f01050d02160f0201021b150703030f05130b0f0f04200907030c110f0303011401200c040f02190503 73
    0x70b180b41d05941e900060103400019914000068420060404240e08001c2d214102c54088400e0500d540c100100f41c0164013a4000ca184074100050210b44207020651005a50a40150000200750f03180d0208030b0203480d443d0f100324020100340c0c6010089400620903a40103090003850aa540d114280c0116041d130010b021998075140d00f0400400d5103000310b886650349030b1150b034511110000a0002900307003008418107000d02c09540c8603d11103980d40071600c00d0094150b0f8595038880c0100e0804500070550700380211500b516002c1400415070200701130440030740c42100300b00714698400c48240030b407050607500030f8003102c00e090100b40011200c28451011044031a0304282d0410b00d01c0001d0800300c070551710000400d503683c400b06541c0b0b500c48900320141007100c006111070b00462054030351368401403040d0707070b00c0e4030083c0d800c414141c3c802c4500c039500b91a44518410100340e26101e05445d503e840d00264800d903d0316141160042180c0240c03292400f100602d1030f40e02c4045001580c4e19800100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 646303021 1250 646301771 646301783
    0x503011b0c02011407030c06060503030319111608040302240a140d0f05040c0b0a0203190201061a030106020d0c0510050c0d090b04050c01030b0d0303180b0403031506030614010507 79
    0x4d41401c0050380350010345007482c042c0c0c3c4c0b1204901400d040910850300e15420450007604100100000368a0304161344001007a0010b00062659154510348203901035013520114200b282052041800100700240007940d00880e18032501c2800c054130799040030310202e010008100c1c140580c1100e903015001540e034170240080c10b98644031240c8203000444080001702411903503500284800d1200360f0410402409141c90385c2451301c00468070295882c012200415001500b007d150503010381700b0f410003001080703a20707800c481c2d2218184a03004550002d00840006100b40e2135034a0314503101e0172000e41d6458008014021203040440c0e070304054800141411300f1018104036141301a2481d00c20813143c1c030b0003202c40800c0c90600c1e00d000f13410508042e040c0c0c1e04040c1844c0700c4840c240d0b103c031900c20030f40ea8581000640250445609400041d1804010f010a00d000c410441450340580203200e0601d048602d002d8140d460307007400d40c00c803000e50050010220381004d8101165005030004c0c69000c2c0622 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 646304271 1250 646303021 646303037
    0x801240807140d050c0310080606060d020c0f12180301110a1206080f01270c0b0a020f1203010303020c010f020709020d0b040204030c0503060c040e061003092a0503011b0c0201 77
    0x1d08405446081e52583c4249000208005c4400a46031409000d401754101074270341c90801c81c4c0001c0081c020b496034174944550000c1c0ba0000303400100b00007020309034688213580c48500540300c007071405e030810298510409c4024100c0151842c0612481c40750200405409080100c091000c0320700180d60404100382e19581d290200d10500d08004062000b09507000118001143c102903001840d10070300c070404503803080d06480d070014501d81c01190580d102505a26241d0081040403407906111010001c3e19000d9401c44258904d00c81000f141643d0080d001c4503803e803c6c000044030385088a14408005800c440304c1230003549081d8009144c1c090701d181020841d00c0c241800607080360b11a901c1110300710300700401004241400d2001c642c0c0501e50741c0d109030800b49031588900c01004010042e9105010080814003d070b0701903400010526004100b1042100a441c07400381a022400c0c281540307074030780702030018051605000b10039107210706882000070070516500a0305c0b55521014101d044c4080a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 646305521 1250 646304271 646304287
    0x2a0a0f1509080a2c010c030c1a060414150f18010e0a14011a1e031504060801091a04080c0303090c1c11010e010509040c080124080714 59
    0x181c0030349814907005210581e0b40f841d4440e0060f180490302440ba40ca0030701c9038581d881e519492508200202d90003800e2641c003140103842c0480c2c0c0c00502d203000400d01010300380c088900c070100d200c0c1140b10341c000703841c2000200001c5003050384902040b40c503114a0075003940c0104441c01c28855035402c02e0405030602c21105090901c62989400036000080d04030003050070068007030040d001310b2500080c8840304001c0c0354103005a4a405403c0340301004220400018a01419025030303c448503030106541d0300c1707601c030708101f0f400c098010000d81010f40310324100500462228010b110b002d1425034005d509083c4283c8000107509042d030001c2054134040f105103c00d41112100340000c61040c51404090059420803d0403c600703c034200d00c0040003441c8800101000508040080c0003007503007424036a0900303040c00c2c0103c407688501d0130036580250a0580c2c03000d0039034000d006c50f030581e00c26081c80824a401c0b42c8411035440c108031000800110960085030f00a03014100300a217494503410203030701e05014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 646306771 1250 646305521 646305563
    0x1111602220c051215010f0804030e040204080f010e1f0905030405030f07152f01061505070b1f0b0f0c072601050103081c020d0507052a0a0f 62
    0x240e803501c407011803c0011089000e4254044060344403078099204d820340170384040024590320048605105000710300c4045001d05004102507106040d00520030366035280c54881d05604c031104040140d050758245002c40041000218911000712404520340219803a5209a0030203095681e406850a0000b08000305181e18140400d4840d0a104c0c002455624941541e01800c80c03010000c500070071155801d280003040011100b6910303103d6801e070008640155040b9680103240591004100880701180b05204070341290250591500070301c2c0e02036555503694440b0544c2e10700c3c005080103141c1000804e0000980480c0039010302c1c002c100c8503500f0603c40c1c58400717240050a40280f50000000003c80c8002c0c0443c8450f0183c03900c08030004d01c69949150f0740c500060061a01600030700d0400e540541c01201268107445016034203550a000f5030a0006014050794040d00700c2c20149503800088414491740c444a24201381e907c2001060080c07a10b842d2400c0703410703d50604a5042d00d100700d640e000610 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 646308021 1250 646306771 646306781
    0xc02060d02040e01081e0a020907030b090a05010812040b0712090f120c05010f0c140c130506032a01050901090506070b0702010506030120032503020306030111160222 73
    0x11846104801c10750600901c0ca01d45a00e100a480d02c1b0441da95811600000103d46070741065030503608214240c88510007038001d050b80320000c4c0c0e0050300d0b60b010000e8030b0340c8640184d4100c40c803180944102d400c03481c0c1109898411402010000c02c41080794200041e4130b000b41048c2580703145481510f03251150010199000f03203601c000340c5036214035903184c2800340182d10000104400d0038035a04502000030050500c0350703814400351201c0351107501c3c0186c5180034807036504903110052810503c0c17404400c5501c020281924940c0c001d2141142000b41d421900b400f401c140c00070002083c03c0b55144c5801151540e00c54424141000014880051035444450246c20380b42c0c0b1a500c200d10514140c400242120305c018085071190307041018060102440508181e80c0c0c00405070b801d83c2d6990f902078904401d950207041c000c0c0c941c050003440411280d2642c0034600406080740284180501010050000ccc014003201d041581008403040006292516010400340e10401c0b250a03003946c2d441003041120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 646309271 1250 646308021 646308029
    0xf0603060305060c070b04020d03020c030f1e0c031b030a0222110313080f0702030d0221030c12180f0d1b05030a18030203012a0206160c02060d0204 65
    0x94940c881441046001d0050302e511001802c031a038240319550711420700307904e070152000e801504103480c100c06240c801c2c0001444a48061f0450354810f0240c40b0301070381c4000c42d41d542841c0520311a00020300480118004800b84802801001d0368044445407902c500b4120007a030b68036101d910102c90050b103c400400080e0a080c4000085020007000241d0070317194100300110141804104108034100f04000070329040c0e412040e000d0711151b0b0b441c20a4030500c0b911101a47c1445050780c1010819800242840d180010010040b00c0c01c820300c0b5420039a000541d00c1c200fa0000600c102d0040f14854403100380d01840300f825080303441e4a44800c0314200000f501c02c00e80160098126880c0c00e0347c00c90110050301c45044000136080105481e00703070f20b80c01950701d103c0404c0804403d2407280c100c5203100e00c0c00f4540041c002c02c10711015040b8401002181084811b00345811008803e00c00d0011030f84d10310030f03820b20b884800240c0e20b04000f11181c03002000100d921200c2844044078480d01840900054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 646310521 1250 646309271 646309277
    0x503060412020f0a030f0f0c0f081308011406040b01020c0a23010504030807031b141c02010e06010509130b0c04062d081e0717160c12090f06 62
    0x800350120000f4100401c55045909942c460350316040002d0380510070303803945000c500e070480c0e020082010071102c1c00910300001d0040002c0301c0c0b0300014000128020004101c2c0400100d45980da680c0c0740c1e50030b842c140000321010030740220000b0b0243c18241c105014805051058540c4600048001a0f034840a50401c4440da403500c07090000b44440b800401d40001824244141004d195945000051207030f842c00030100701e4040c956029901240c503040c0e041c503030f100500f411a909040300381c0c0d81d61444400e644d030122500d9400b5100b0180180b050302c1c61440c0020191286a0901303090010407030002d03011084800400d80668081505401502e001e1801c02520f82d940c1c0e80b43c04801801c0c000d004e0226500082c80540d110050240e4003840e01814a041c103020380780740e59205019404039840c46200080000346820440c40a900180c0040091002c100140841c2c440b040c8404c00558681c046601144c040801c403404140415100c01f0303410400c1c50302c000c1d010f840e0742a080190f1440e62043c008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 646311771 1250 646310521 646310543
    0x151506120504111c0204050606090a1703070503040608070306060509090402040b011b0302071e08071202060f040923090d110a050a0f0312020901080403030b040e06010f050f1e01080a0605030604 85
    0xc6180c28007405c4d2308181c084400e00c6c1052055000a00da11080d445207026050b0030403d0a5103000090041e50071250f0400150380e10743d556500003400b0310703108994401c0028074284012403460f020358140c13414070b90060070310f820a40d41c55080c00010a450b80b003040c1400030102900c422896100f2811001500c0380d400741000d64503100c60f0051004004018944014080d0014019813078006005021913010692400b0b0044440c00400c4c0c06225800c44103601c47c20000f0f000c9480b580540001d4000d040c08002c03210710041c16000c07407804600964503002980c0020b02d400950070b1080c104800d810305001c0c295050030038150348407441c0001400c0300b103c0e14481d24444ca0245500302d00c002c01700741d080480543c5042c03c001d000030500080180003d06156480c6400e04803911503070320950038803140200706c2c1c07050350310745103100600c101e58480c60f88220f02a034090204d60502c00100b1400c02060004188411780000064540303800003803041704003540e038202c0090b2641e030800c146030050f40030ba02c0c41c0c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 646313021 1250 646311771 646311773
    0x60c072c0105040b06090d03050d0c0e032505060901030b060d050f07020a03020705010f0315081018050303040204020304021507230a050d110708030304151506120504111c 75
    0x30120a0580c0898440d80c40c01445039016103449045a921801c1128044840f899a1909448a02918ac61001410301c0d02d01000c2c101900001c0c1d4030f154a43c01c4048440219008070040c031616100d1110491b00c0c0d50b404010481030802c00c015004407501410040344480d80000401d681d9004021403180040e10360082c0070000411401c1181c115038580701074942c600d07607a100079658040a2060504001c00300030300312146407003035010801302c0846507074508285aa0303c0a4555443c800ea0640c0903551804d54151180100c241c0c1500000c1e521030050360a40e5201d400308802034000420517600300c51100240407040c0440e00c01041c1151042a01c1c0381410159089840c62a011180c01c40a0b9404031804c2c0c80482d000191088030041ca524141d0900e441c14549a81408600e602400c0b42c1d12010082c4010002c40d500e200d1400c02108104104182a01c408403070400708500c40d85000c502016256060140e40d9041194480d0052035429100340e6045d01041c000035502800303085603000100080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 646314271 1250 646313021 646313099
    0x706090f0c1211010e060d05090105060a0f060806060c0c09040309140427060e0d02030d150b0304060b010e0a121407080d05071e2d080702060c07 64
    0x300180035000c500d41c0c2665142e6450503910026100ca20f0706000c00d1700142a0240e42c0c1d83c0407100c4140c42d8610520050410380c036203e0107028155560f5101d0348044001240802c0c0c41d000c10000c440c0d03103a40c1c0348410745882d8140031050784510b0440310940070745020007401e51034208001e4040c61295a8003141c90f490100d00049595020f01d810b44030b03074140b22a5107000d01a00c08031101c100058954a501c00042d490841c00409440c91411500d0140d00d0754252100d4010018041d402c000c2c101c14804008020040d0f040001a400b41210200c1d0600200d40480c003d548031042414041c1403c450300d030403510000304502c60581c4600103584040c2c864204001c40d0185000b0020440300060052500b440b080c10307200d124000c03503042000800710b4241c0910466038003076081c0d203580078104010980181002241000030041e820b141c9011015040300310b908120101e086190402c3d00c16007422507603400c105031507210840241091003504008078540081c00b12881413440b92038000660030003420300031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 646315521 1250 646314271 646314293
    0x6060e0f070c0809041503050714090604061a16080f1c0c0503130503090d050c090f040209010b0d0b040609021314152107170906190e030706090f 64
    0x9208201c80c000c02980090900c0c0151090b90070229804546c00402200c0a00303408003c0d03002030624030030340e80000b80d0300111904011500e0300564a0b0329140c0e0302d100511007600c4081c850044402d4811142081911070800644070040a401e2400b4188245466840e0560003248518480800002d80c0b1091000c49401140c40c0e20030040003071020fa000d668014041e404000e0442c1550321104040b0340030400144101c0360921401403084045104034140140d9501001100501075496600481e491a20b0504858803542d070080500440b82c1c00d19001e030303040d41c03c00c0104101860b140c0c030706002c4580d240d004103805000309540c0183c491500782c10700c90702a01140e0290343d00741400e9506c0406d5031140c2c242d2200d40c0381e401013002d580301c1584004581d0200004c0c0c88440c0354030170005001d601640201808040014013660003001c0c0c55012050341c860034241d48058100f00595403110000314039400480c1402d041030b094a050900c00c2c5c640c2801e50b00016022203500300404400c2c01006070706024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 646316771 1250 646315521 646315531
    0x10605130c080114031905150603120a1b0605090a051006062c18090106060e0303070b0a0b0a09021e0306030a0609020a090e011515051b0a06060e0f 65
    0x4280039407100054007511040060040f80c001158118001c64980c40401840b90040c4100340084030f40600d0f41002e079203800c1c140b0b1000202a082c035010407114a030019440081b41940611580b03044402c660070b580100c0e110701740c0e081104080e54994081045403181501c5080100b002d4507100085103000380c00d100110300c81c8030040b890100b003806071552202400d080020151004410601e049101640c41c1d00004034165000300c010310100058130604004038000d24008000380069501c441040d076040120040381c0d43c050380f06020170b1002c02c464100c041e0300240b2000000070101150000b003000e00540d6009600100e800160b500035061502415a03003c030702506100b801c40c10312600207074644210314000341c1101d40b01c40b150025951240041c0c0c00130039183c0e908021859075044024040c0c04201c502e245008000c42d4001543c41c0011030003003002c01c5070392b02c003454401e01000040020000d241c5500c05032090301d50442c001042449540040d06081341041c0ca280381180001d8801000184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 646318021 1250 646316771 646316809
    0xe0312031b090301091b03030e010203031303030f06090e0a0519020f0907030f0c0e09100509060616020310060f0602031c020309160e010503100b130e0a0c08010605 72
    0x30403000040741d251100d4082011002980c0c0c442018000030b01400b40070401901c8600301800c683c84441084541c40e01322486034a47c0140b40c41750900598072800b084420601940050300d620340021312950040500c0104864001000e0740c50324a00000c40360611020405a0f00002a55003444820480f24181503085943c40030001001c2d0301203849900244052406803150501090101d0b010340c01c000c074905c1d61444100089045808010203080480c40d406015903400c002103503500035031642c65029140d004d0030040c26a00c0f544140000b50344080100080048141c002c403006a03401e101041030502481e80104119042c0071940381680c42a17071020040d036208019110b40110041c0317413200b4910841600503181e540e05000c01c0d007002000142000304c0c142003000801c0d10600400514107907002034003102c1c3c0402c0c5464140048404000189030710a40c40c14202003064441d401c05400070b0260401e96182c56440e0f51070880b20510b03a008213078143d4441c8020f00490030100021045848281 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 646319271 1250 646318021 646318027
    0x9050c01123b01050708182d1504080301030606080d020c0f12030307020d0e0f0307030f020103061a030604050a0908070201140c070b091906080a0203060d120e0312 72
    0xa03000c20524844204640b81c1824180034441d500d64403a158458074519a0001d00582c038044900910b9090115205a00c0c101c105842c001150000201c910150440c0d0701c09170042d0500142100d580503208240756124800c0c0801c461000b000c230705440340154813901d2880d840c0e5045150950a6401c00d8021540c42e520021400300103d5000401d400c8203082920700c107a03001d02000c0401c184540c1d98010014a11002051017a82c95000a000c4014012a40c800c00c10001e40b204206002010080c0302e03505900000c0305201042031868114001e5105040009255644550030703d55406105282500d075540841007191909041c000d15a011170104000c0040080555824000e4050000007071304200b890560780c120700c44508210340d2641d803164101c1b03243c142e13030b14010b00c13403030348401c03040f601a0404116561640c0c01d1388019500703686641d100d1606650382c482c03020000303410003058158880002c40410000c1141016045403118082d5a1a0f0744481d0300000d041c50151202c45100200800f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 646320521 1250 646319271 646319291
    0x807050414040902220c02011506031104090c090602150f040f170d1a06041518120b061c08030114121b1003151a070609050c0112 57
    0x115086400795068940e4018241c0d070500c0c0402c0042c290044020740160100d04c0301c0c00840c01c03003641c14414003482c0c10103001182812404909891700c9800019122448400602c400342c000d400001c0c644618a440c075042c103540b20329160654119503044030100310030b1502070004c55418000019141100c010700b008078144141074500e49800200040c00745020525210100054942111172000d4071080b800d0300e41040419400040c0002c001088045811755030a80160401c141a00d007251100785076a0111031242206880c01004a40c0c5084e01e20009840410944022554031907241d0240071407445e245040800e02c0490f11054469940d0110109011030019440c042140d0644070023264840c0850a41c0700800e82034003c244440a0702c0c000c081c05c0780352010101c149155241412129500034080d524420f4080700c500c01644501001c41850a0005555141404c4c042c0c2241c402c0e15850311041e40c41303000484130800c208072903540003000c80441940c0c1c01100d031034240054a0040090041d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 646321771 1250 646320521 646320527
    0x30d08060904060e0309100e0a081203060103051803040603020315010e030706032f0903010c05070506060d020d1202060604060504060608060904030c0f0303020904151203270e160807 80
    0x10080000f02020b84445800680040034402d540c05075001a14645520036040e4001d00b20300d510743d000b603000d403c0b00740000805400010360310680701c501315415865912807400440c05010010942140d41c800c500d9020001d0104100070300003040140c0d40142c07641850700920030041406a551410001580110f00c0940e40210300b000803a45d55007000180c6602d03d00440e041070640b0400403403d4414030000c080000c040c00020460f18504a000700306040d0300d0300c010350301401001009041c0b036002c100021624141912079902c4140024280350481882d907503022500048044581c005070454014004c080c2810b01404000d001c00300c805029090500000a0100b000184841d200782d145a001c113040c140a6940c0d259440d410050414542106040c003070069884002e000b03005601d0250501540900c01000600707130392800002c6403008841c0d460403a503e81d032185082d2000742c4905084943c04080d20642e0340140960310280702c0c0c81c034000190b14840c008952032803042c04400b174200412564 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 646323021 1250 646321771 646321789
    0x1061203080f071b03051c050c0301121a090312070206130803061306030b0709060507080418150f0e091204170a02030d05180a03110f01020f0d0e030d0806 68
    0x30318030120b42443d030341e216001c9901d14040c07080e0a0524007541910805c0c90740c0b12004040ca10041080d84440c21010004c12046401c100c480480445084c001800021282070554513214028a40e50141502480150040060503a10a0010382c40011210320a01c90500d089510100c20300140c10b480c0b070103241070700f00d007100e140005055801c00000200a55100c1d440d24907041d48590701006400d4581c5400c0b4550031040d42d0040208414400c00a03001e440f84085881080d8011000c5007014542603103000c00c089500440300041d074442804503001020b000c0c1c140020411949100501c5262090400100340060050203107500030606401c000b0090b0703002c841c1140c0e4144d4003048142908880c81c0c1c00c02400c0da5000f9858043d908201030016440741c05080195413118040c401241380404000c40c0141521004280000031158000d0601e400d050609000707006005444401040c0791119050682e0045c1c41408241900c4a094207418100300804c80f10f149402e040805003000000110844 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 646324271 1250 646323021 646323031
    0x120306090f09200a0314071a040803040504020309031b061602030c06070e010c05030304030801143709050c220807030f140f0d140a2c06030112050106120308 69
    0x500040f01d080e45860301440740d070083d41c1040c5401c0c00a0908400b941d11007a051080310380101240702c03a81c10482c0d000084400700c802d0107004502d042d213408103000103900000d10103d5071340814440006045100310042803e0780030000507050030b1900c0c1c52040c68829450802008550040c401000203071000a0440c0c0c0040d264100791040400d1800100c4014030090001400d501002c01408201500400e0040c180c07501d1107542c6211854480a011030f101d01c1300000c1031541000c0e22080d501070700c02581c0200510b5044810031040f41c9510614040d2101a10114034100b400140d41e51010070001440110310000c1c42c0140f605450f15103800d5503152140000b400500400d4640d80c05c0008031100c03034006182c103100303a58000c02c60036009600c802515111031301181400346800c00c0c1c00c0104040703940d00302c01c13500c81d15a10000c0c4502c0d404044503820400d242c3c1107110311003400b2991194050350007050400851074210381d1314075001c1c7c03d403034041c0e00440403030006425500c006a0000300c2280c0c0a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 646325521 1250 646324271 646324313
    0x50705040522020f0a0203070b0c03070f18050d0b091002031009230a0504050601080d051815070c03140303040f08032715091204030816120306090f09 66
    0x100044141c1e0b030080c03241000725401c01100113440311070250044080c0c00c1403402108030040c1591010009007a070f210480721040094410484040070900800c64920f43d03000b5414054610780d200c1e40443c40c4c09010035801d5921000714010080413000c10014600e052810007001d50941c14004c0415030008158040c0304070403a00d038501d0143d4450310029144461004d50380f030261508150b0303c502c5c024441524261018001c2030008188500000340c040314014107a65a1441c1ca406134410701050b1140008140c0d211200074200360101c21680060724540f8066003241c0740003440c600d4054032441035642c401c0e035250010f104000c00b140034841454031a0707420581d403583d039550701c07203042020851f801c2c00c024004039800f1001c9503c07440011641c0d0700781c12030307003412500d500d45d1008642e840c071102c00380e040e1180c0704001c1800010120740251090200e601d51201e01245e6030794400011219040304100041e0381c59504000b90b060303d002d401c0c0100d048041c104512070310740d1075540207844c14000803804 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 646326771 1250 646325521 646325569
    0x608030a050a0c05150a1d1209040b0a0503030a030203010f17121804060806160504050306130c0f151205060d080f09030303090f0c030609100906061205010902040507050405 76
    0x13880000d003c13650384403031040c0310f194983c034200341c141d40200010f92501220100d2441c0404500c0b000094040780542c1c4018042e0826880004000c043d11803c00d40da43c0002041100040c0741c0c40404c00360018001030f460150301c82d81031152020003034000d0b41c03148004400111031001c0403000814000700003910710158658903085c02017802c06000c22498201c0d04245480c1000034282d4004c035060380203001110340d25820f001d0b00d400071038850040f4002c065040c0c01c5000800c1211104001a00805102d00c2d00715517801e503101030111052403180d00c0202c6030800c032245d6104c115800004404110f01c1c44200f0000c03424283c001c10101070b048000180300400c00650801102c0f0203005441c0e0f00b170300060440307a50780303032030301d0215140d9a001040088a206190316001c1c5480c022805c244500d40c071030000d00ca201c50b000e0100b405881c510700191003499403841c010610070b2020600c02c5c17056015000100b00d0402c10300c14002110401401d0008104043c001032103503070740e41540360000640e81600f040d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 646328021 1250 646326771 646326773
    0x7050403080a0e1003093507110909010515060403030203090111010f150f050a0605030c03070513151e020c010509060d0603200109060c1b030507060207090608030a050a0c 75
    0x10101e01c15071040d5440418519002e8000e17505821100c00b0318440c03d291440840c40204540c00e4a607103002160306820040c1d42d01c00d1060002d8017500b8154013913600c0012100c0342c903010580111064641d01900d0b5100d00403c503030b213045065000c154440948007203107001c1c03441c3c0303001b9140d0140c2241581005130148034207810711000d4110041409a294040000180c005c5091511200034460440800d4040c04005032524084190604845154852034550341e99600c10340f4440d480200000c0a1007028424100f8002451803d030700641405400144500c5025802500d103c1e07000e0240d140300c141c0588201d070915400310f40140703800c0c0d0a007880c2d41c8807540c3d030000640b075025074034408540e9440d0920000034080c000803540200f101c1c0c45a042004010354004480c1c083c031900442010800045007100003800d4800510521036184203900c0e50f0355140d03076945050816a80c85400164803905090080d2107240c4620b60080030280d005510b4402c480c0e001130101c0c021910010b00303000c90120110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 646329271 1250 646328021 646328027
    0x180904150510151106060303040305060c0a12060f0905160f0f02010914010b010906080412140c0106031103011416181e060e030610090506030c1302071a07050403080a 73
    0x503061145507840d6240540c04020045010318120020b40d05c60034001c6800e5007004400c80c0c0c152500b200240242e50348018001c0707801c1e403105054400b044480705c1802e81c200c90502c200c4018202a103501600a490242080140d40b4041e04d4071040b03039034031000800015006081c40b207141c41c4608001d8031001214205a0050503100340c007814031807010044001c40f41041d8403803445004242ca4078104280c64550480e00510102e40082c01403011400240c4a40e000e4415003040e04500b031280e928040100555509642982d0310841c0c0c07030000d20700d000709549801c0c09280d510b0700c0340d60420340c0c481c41d00f2610102e4041c580840c94040c03018051210790b42601c187c2c0c014010306040b10001858802c5002c8544044800388251000030301c52451032205494085022070052070405251503585041c100085d0082102400c502d41c984a0b0400840d01520703540c256082c49294031000586039a620300303000c0b111440c0c03020b01c4215a8504410080040d810bc019107003070301d0300035890940f91200c640c025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 646330521 1250 646329271 646329301
    0x40b070b060f09311407170a0b060105030406091a0a0506040b010e0904060905072c070503272d01090506040f05011413060b04020405030304031103011508031809041505 74
    0x500a051780160702d030308000300000d51004075416841000c010095176117116440d0100d54038001c0c03031409038401003511036201d20003840e00540074050002d2016101d684264100b0305003408800c100d001c0c041040b030340000327511805070700520540d001d0003183c01c0013000a00d01c04410031802e2003070190201040a00520340d005600655026045410341621004040e90320b6110502c03034140c102000d1a8081e40480c0082600c7c01840305403155403e54580c40a8001e219002d14401b0140504c2400d0021550707008110700100c6d00c020500c003e940c1300c0700103500d601d6411181e5800031280e06024520000550012302b46500c50340104240c0c0c0c0114840c40c00d180500060381c40390501131040030501001e4140480c4a80075144a0941004020030340c0c000e00059028070320030b03103500d030b0014441040490f0f00801c1c13504810000500000300c42841d0042500e184210b80c105401c01c0c0d01c0850301d0005a0365240c0310034003400e01100d8803074062410b503448035500f112800b11141c4040e251408200c01d0307420035800d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 646331771 1250 646330521 646330523
    0xa0e010c050705060606070209130501150b0901030e062a0712111e061f090c1701081614120109050102091c02101103040b070b060f0931 60
    0x240114a40c0500007091500003a800303030365038000e0602140c41440d218040b2003503144d018201401c5541d0b0b0071290a00702c0c1540314296469500d40010400e42440f107004640903000000000752102185800117080b641d0f0f01d0394522081d070000c3e0920084c01c0a000ca00e0b0000003449800c80302ea1078401c0b0002d2800d014103280101003183c04003010096603000a41c4810300b4410314115180d001541919030307105005242d240040e80c01c210b010688034011000700b004c20071084038103e00c030640d4031001070013128500d802c20b60000b409101320301c58120307080450230b0041030150000d01c0c0480701c89500c483d44107100d00c41c6550b42d40300c03030000340400d0700c030302d0307901d4408110620003005040c3c0203040290103580a1000d1520030b10807400303140c80c001c840c984c00421031600034045103456100800c05589050109400e04110f20080c0000500c0f0015000181000d920805420718141010010b00502814a0812038403840b8040100040303082c411400011082080c2818a44441d152980500d0694040701c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 646333021 1250 646331771 646331773
    0xb07031101020a0801060806040c08070e0612100f0b190e0f0402070f020f03010e101a0a06020a15020306030d0c0c0f030f0b0f09030706050405030f0309010506100e01170a0e 76
    0x2800030501a042161517040380da180e02c8100882d070300d0714200701c100c139400d207010400300702a840441e580a00c81d00214038500c4001d0505882c0c50f14881105018002c1140c1007800068004000e22070b100d1598401740042001d00d15050403c152042805108111107101e40104206900410300315035a40c0c800c0e94841c100940110740d074906609002c0740084803074000f80e0007450f00451030304403400c0500c40c0f00004d01c03800010385071301d03501d40c00c0401c0074103c03c050b00304d001c01156040040da640c400c0f00010040c1902d0f00107082c440464600500940c000d403602e00c40551043c01001160380703021961542c154200d2410b903107207a00e549084c00300300d02d042d0000075143d072030503a01104002c25041c3d02c0b00b00c1e9010781d800c804c0a699105003403004007811110704000740c20600c0413100099040d0495038009104e00d0a413070900406884480300342d002155142c040303079120401d0041d142801c8070340700c0813500c403443c1c9650a010f07001d00203002003803402e21054008580c480090780d1001c040e4800b100d901e610784 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 646334271 1250 646333021 646333027
    0x51e01060617061908030304380910060806101415130b0c01020912030310030b0c4f06120e030f07021801050f061809100609090608070b0703110102 65
    0x503483d5940703410454040b41c040c20445034112000c427a100401c4002c8101a020044408c00716001400c1002d0241120100e80305466034403c02482c036014000c060940030000306058500542c0002030807a45074046c5031445106201d44c8490303220f00e80c884140520790103100c2ea44100080c0700c01c050003403552244415080214010400700410b40052025400445511386200d40820f03c043c3c0b00e00c0f00340c8500b000d640c122441003000410680341a9482503074070000706e04219481d074425940780b400f1440000003400605000036412100030885541c1c14100c0108071012844c24050085c0b0322a0340646400e22103a603c481d03441000c02c1d0050700e000c206540c19a910390300400c000d51055005070100700c1c440c00900b401c87d01c4071808541440d0413520f0080810307020904000520000d5840790111000150b64003c1c004150b403a00c0088501840c199120350400f00d2404000034062142c40c2c011551190404c0800c000480b00003804400380c80420481503507034502c6107400c0c1d9400fa00b900100c00254004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 646335521 1250 646334271 646334279
    0x211902070213060f060f110a060b130f0f0609020a140c0703020d06051006050a05070308040f060e0703020f0f090a1109122a010503150604090603051e010606170619 72
    0x180d0013200840c1d07015241d50381e20a0101005407014000301d440607000360b109400c0a004a65560050700906d940541076030b26500403c040311042d00c0c40000b06400c00c6840d8482d800491905100701030041800e00390031230503c00342e0f01c00282602034aa031740348404800480e0b54440f0300c009000d808000c6500401e0058545e046143c074502a0104881e49907010903100d0307000641070301800840d01003821660380c561420a0640c1c0540c2c00000103030090712a850400c032343c200025403c0c400c600305c030341501d401405c40529520401c128030541204460141440a04071411901c81c06000364004580401c0030818075001c0311805001d0040c110300d15070042e021103980840e01d8000c903a00c4514144003034106246201403114000030724507144600c5c00280100002052a40c200e1070b01030440c50010402480c090b42e0ba6103500035902d1682040e01d103500241d1140110a2a286903204128402c034000d10600e840d280d4054041c11144100c400b00f00c484d000000e0a07507035a000800398108005154410403a00c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 646336771 1250 646335521 646335539
    0x303041d060f010c05070b0a090b0d090b0121060b0409020913060509070e0f13051c030501051903031209120e10080907050103020702010903020603040821190207021306 74
    0x39a00c55025030400780400b50b85512401c49102025042002420003528112203150b04c0e901c18650751041241309640803500540f14401025891748142010030b0780b003070600340b085034404181e1010f0a9905014480704507824004000320b0030301c2d0009000281c2c0300c20352021902405004030000c1d802042c1c0300412501ca120139141d0030856024030340800c0550795241015695070030758054640344414100001d100e003050364018079403200d441450041e2840b030603170701c440c644002c6002010b041e400340300800400c20760501c651401450100e6076400480d10103142001454401d000140070010b61800c25904da8500d5080500095440501808c031410340300d40080c03404204001582c81070244485406200c1d104450482c003d4503a400500303c150b140c040194000c5d884650b00700c1c14418102c6001015030703161005144101d02a2040982d503808055062076042c4002c501d03045848580d009000e0300b82d090045100003410520001640c4419a00002e20345403880d001244059042540200325074103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 646338021 1250 646336771 646336829
    0x303021201121e030c050d110d0311070803060d1401020d05090607020c0f0f0603160305010501050435030a02070311030f0c090705070503040b0a0e0901120201030b030304 75
    0x10010314103400d0362a4844202c42029410700a42032050911400d4141048040b840b00308a00c00e040070501000382c4d0b81c460303040c1020740e403800f0b001c1025580c5070181013405200c0100e40f804645402c005114103442ea612880c020ba0743c020b0034416000c80091500d0b150000814245078102003845030544001030264083c1d8840300380300c64a2810040401c0800c64000f6102e40a8680780e006021489403d00502507000c2c1c12001c034540c090521200302d480b0340c40f950011802000c401c442070209082082c00a0180e1344c06038025410010204810800d40f280b046c0441c080c6000c3c001800396a055008031400105405103500d000341c00300081c50300340641c0000e468011a4407601282d40910003920401d034660003c4071520180f40c00c010400b4101d031800c940b5440e807001c7c00b401d00c43d0500c41603440d2070380b0f1900700760443c10140c01d0014400c203089401901c144d9034901c04440b00b008642c18171003034040b40301c6000002814183c5840030254156400e00235140900074028012414440080030030810340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 646339271 1250 646338021 646338037
    0x1a190e0108161202030903091e0a060306050d02100504090f020d0b180f0c0d020d0e062404020c1002070b010311030105040317250c02040e03040b030606031317040905250f1704030302 80
    0x84070141d2b001072114040d018203800c0303500c001c060301140b005580901c06800722014062040141c06c00004c14044420f00c2801d0300c40c2c003034140050300c41040542c0c100464202c400501c0c49102880642406a1003198000d40e00181e0607012a0300c0c0d8990b503d540740789018500050314903c0c00819560402981944440f000d0024042125a1030b110030711044045041c2d805031985440c0321807240e1000c0c4c1040d40051840c1030803d01180d1038445880180310480c0c002c210110307415a0182c0c0100140800d0019020b05100d080b00200450704040d070300a070030030000e12618070040309540006441003040002405004400e104400140c041810008081702d91100c0100c4c0328529081d6030304548900003081e6001d0360950007269207542c640900704201a007000303081241d9a901d03548500001020380400d005115040c0c0d00c2541c440f410207000005940000700100045c0e00d05003103c034004004d041403400f4640341c500701030100c001c1080c4100c652540341800040009151414001050b0303155004102032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 646340521 1250 646339271 646339279
    0xb0307031a06040605030c01050f0918190509030306040903020c1002030a110a1a22080409291201060b0315040b0105040602071a190e0108161202030903091e 69
    0x50756514200811075415014164140c0d05c0407d03140d10070f5000354001c0035040002980c46003403905400c00079070903d04400d0400f5070002d56006111844501c9200b10424618203903050001c5e1410b0306460b075407400000c00142c402c40e1101c00300000d06000344519412281c010702070321301c002050310700607541ea030080010000007000c007a1a82d1081078042141a2002d5001030702c03241d4010b41c80005044000c01a20309142900c4613000d14500d64206030700383c0c50507131080840d651220f1a004800c822180045441d1690045008148404103005400c0c4004402c0c111040c0d103485c4448075006004242c950014600f0704000000d2200c42c9071049005511032008850610801010000444290140d48601b1025074402c0c14103006062944030014003409440b02014201440744000301082d00806141d0070114482e030800240e82d5a224050940c400450701942854000c03ea034000c01d423482d20890840c40650100101d983d1400c144100c90303241100a150300883c544580c007180802075414945481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 646341771 1250 646340521 646340573
    0x906120f0405120c03030f1f030f0c050901030b07120f020c0714010f0f050c0102310f050a0303081e01150909050f0c1e04090b132c010b030703 63
    0x50720034010200c54130000c45201550454841401d07100b01840b02400d110449001184401420100380c080b00005502640c05001305c1001030a01030007a01050700003a004043d900014000706081080f119002020380c504540b0884048034820003d00c0d8442c603541d4203a00009503a10589070000713400080d0392081c60130906115480c001901c080d1014011800821250f130140d0a4190060005d04014a0860005460041d102c44800d0890221141e8000c015049416030815000c10b5150301c001743c8080c1c1c2c603c0240341d041c580003580d154020f02c00102082003800c005000200122021601346054955122030703540c4592102210010841d03074100080d492800c0001c04d0b00c0c1d2806400e000315180449882035860b070a10326812640511035510b4400042424010440b1021004000422218500041c206441410804130082c50441110080e01b48088101034042500b1007182c2c1040c01a0311042101d6289149405800141c100e80d515000705003000061080d58543c000402d4a186030240d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 646343021 1250 646341771 646341793
    0xf05090a0203061c0819031e0603051b0103020c1005010302090c0a09030201140c0d0201020406180302060307180810090303060501170c0f090d11010f0206010e040204020906120f0405 80
    0x102e000448400e42d00c0410032410305051400d442c42a03108034050925036240500641040d01e510004042040001e5522840d0302107454040717240501e00440c81d04240011440c41c0c030703901d07580c03070f001144007490304c00c0c5005044003070b802507044480d054280000d54020410072048103004143c04d200507402488072100151700c00c2000300850768100444d444500159065400450300e11001030341d0007415080070411052417203010407000d800e440ca99070015a0347e6090402c024043d020640790980f0428600300107100603a03401042e20307070040030f518101e000703840105541481c1000a5010507200d01450104114601042d001103011130302070780b801d0180c5a40c400046a06407100710b02c0022000041c03022420001111008141ca00e84444805080080c944001080903400d01c0b07003152000f0340c2001c000f010356001290b560050419001404c134070342c905410166140401403000b841103170f00260792249a03940342e054514114028848007102c0c0b82800355282e0032082543c09607514412003404d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 646344271 1250 646343021 646343041
    0xc02120c03190c0506040f03022a0d0303021e031b0a0c150b041503060c0e030715140a050d1a150904090f150608030301060c081809010f0509 62
    0x5a00c03854120029850030210810b903030818181c2c0c080080400880c2d56003540410410000e2501940c0034010500c141c08991401034a88ad200d0300d51100444a4024000300c810406180079000e040140d40141811940c0e2604600034840c0e4545c40c0c8082e03141141e4000b1a4101c0f002851103400e2058102140d00e8800c280c40304075000b00d45c004000204610402400070701c0f42e600c030702c481e0100480c0102c0c1e080316070400a07080c1c821451020303142c0c046120f420001d000d0306006010400c0018200304803546010004240c44014500822200b1580d4030003d95800c1c0c800c3c0c4290080c500242286901d40020600082036580410743c844099401c145003040d807138141040415580c28002c0540e1003003902207041c04641d4010b9410300b940b2030750380c10241c1c011401d49100300035594402e0300e80540211640381d00f0310413101240c000419035803052005001440c0c000c841d003041c240d0880200b0751598043c0019203183c0c0c114140517500682a80c00004a106c01c0030b500b00152035044409034966642c404040f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 646345521 1250 646344271 646344277
    0x6110c0f010207120e040f060617060609010c0b2d060f040509030d18050f1c08091009081e19140316120c02340317070606090c0212 58
    0x64036036001640c08078000b5010701c02200c4001c0000c1d101041e07c10146489104441d8203030300410110301c1101502440c080b10607501e07544005d044980c2c034245403069000a10b581ea410100400d903244403404a40d40300000c180c5002003500c2c803541700c41036079850ba21060000c3c0064420502580d00700c1da01c444a0700c3c1900555205841900055040c54036410600740a01403a13203204010700c11082c008400b2a8091222417540301004004080c003800c50075100050201d03080c105400c0202c440b041c08078158000c18450309840d0210f0700410b030a042d60074070018030710071600c0040d1034200340d104c28040b0422800151a20125025448156191011058451603140c0c0340713604071100d081000800c45107552406030101145462711200c1c01c1030301d00069085400381c9012402583c0a03581d181c04216036000d2211056800c0e04c1100500001d84011641100c024040203000c4c00510300425410140e62096a1080d40c00c00000d006d03040d900c00030580240480c080300b100602507910071030f94080c412811 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 646346771 1250 646345521 646345523
    0x606070b010f051f120b060f040e01051f0507020d030923040614031e1207060e06010f060813050c0d140105010e01180b0f040f020306100810060e0d06110c0f010207 72
    0xb450105c29000d94030310020f04081d428103910800c10f000343c0e108529000d0140002e0306074003c4500e181d504010400541d071104200c0c401410401051110035554010107948465034107a40241e1800c402c1d1809452180b87d43e003208003103040d0641d00060880199909040e0400207131400c000341612242200503603110054800e405600c8010242c080c2803c0303103288200b0852100c10750340650740180c401050340e8005041614010386411904031400018401d113030040c403804001c01c0f40c2d9450000050700d501002020140c0d02e103898603406040c04000c0c0156290400010404440c01c5e06519200440d9046405100110f6103010b001003201400d1b526400c1c16a01e090f2600e501031204c0142c01005081a11146a041105034100b0403c07519240075a60b001d11054901584916154081c400051002c110100030070694400b401040c009a031140400e8401d01d2500d410f014003007401049101d0003201c0700801c020314014038500c0419001000d084a0810481550170940c5c40811440c01d0303001e0448 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 646348021 1250 646346771 646346777
    0xd020703080702040207060c0507060609020406122a02030d0501091103180708071202090f0606030c0c24100e01060f030b040b131a0411070b0606070b010f051f 70
    0x60500108441401604007288001c0c0003510300a03150b40c81c0310a59400c0005080860008691001004224003c0a0240c01da0200440c18107250460080c606034040c0448080b15507a030780c4621501a1036150700b1003400441075445108100301c0402940d0341e010701c00504445103050000700b054075080c080c2c0303030549103440e602c141982c03141c0380b011400707040c0c4550000c0c8905c5130360b03000140e04006000c400c000380350f5140d561030041e0300c6005028900500800c0c03441c10803035944c1040b000d0f0b40c808056070307003004c40441c2681c0c0382c0040c450b80d146000201c00c15018a100140b5a1307012072025965203501c18001d42c1e02d840000d80e82c0301c40131000a8000e002c1e10b4003141d480c40c940b003e814801d522403884050010030100f00d2420b0240414001082842c00f011601c2d2240113200500650181c0040766035006d840410800289800010440c0103c0000801880c020b81c08650583d546500f55200644c1042200c001c55035140c041c0920100075101d4640140c5a5038900d008800e0000c00b04052000f035a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 646349271 1250 646348021 646348033
    0xe041806050907030b0405030a030c030e0d12020708040b0403060b0111060c032206141807170a0206180a1715101707170f030f0d09170304030e030d02 66
    0x1950305406040c005120580c0c40c800c00c2000808a001740110600680c0124007540d44d89102103002026a0301341100d9505041c10f10100c14004400000c00b1030000b443c901d000084882d0010204019108500002d00100004240030030100304020042084a2140740c0401c5080e41c0e00005441c000e8085004c0c19690b08034400250007000d101c2c004503400620300c000304035004058050b507011010104000d9441c2541d5113800c00100281c4070748982c1040c00b10403868000f10038105103a40d51180742c007601183e0000c1089104010100300003502141e5801000147c403000002c1101c0841185001c5040c0710348c04841e40010b2048660142c09503440d400b0000d45400c9501d10036041b04a103001d441e56401c01840040010f203490603044a900c1c18000c0300c054000350303162030134451805a0448110850b9040481030000c91040041201c0e810641080c0c41078695001880aa00070034000c031300900401c90714100c042c50001550000c62007203210341c42e105c4100700e0100038160340d607422400a0015038015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 646350521 1250 646349271 646349273
    0x1503030f183a11090702100507080105030a060e0c030304080d020d0c03050d02091f05071106130e07050d0c0f080709030b0112150f090b010e04030e0d03032009010e0418 74
    0xa441480006409a60000f600d04190004200054800c42d075000050b0003604130074401640900506410410034506500c8550600c00025203070000044014049940d5254070f9007907000a00c900302c0c0c14240103059030b803165074502c0d00701d407900e03200c2e840100180507080303111021a01031070b4811007440e096500c150400b54000402d070029404484241d92110baa10802007940c2017020f031078200712680d0b9444a0310b40d103071494a58841d20302c03100d003244034103802e02c9541040307084440a2400c0300c9142323003c20080c1c1c44d86e4000b40c400d4482c05030360340382c154181654402c0c0305070403498200d9004c0c95030352102410b5540313002c202c4800605000007000d180800004102c0780000c006001ca80d503000740003206e010a4800815001c64170480380491580b03884103030403c00d0000905c4464014450080d41d20a00e280564000705072001d030920092160304900c0003001403612950024900121100d84800e202010302081445500404031881c00681c05c0302040c5450304090240244803a8100c1d0b070041001c0e55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 646351771 1250 646350521 646350619
    0x1b030708011b0c020f0405040813050f060d2301030305040f150212031005040207050d0207081c0315050423161b24060602150702061503030f18 63
    0x4003540c10fa0381700b0000032030150107690314454140590321414445503a510614a4040700309010b9110718400e03a144c10740d4889644035070003281c1601c482240c000400c200c4419010990b0700c01d41240580c0900100004010560400010000c0d288025001d4032819624119540c5403900e501c0200010381014201d5418034503150040c580010740c3d0300180b41c5440d01c9001250481c0c103c0c1c0402d80e0345500c0148141c448039010f22140000c0d2003020003810000949030510750f82d801d07070008580109a47e518201d2000864074040002802d0001d0050108066100490794600c4060007c44c0480c041c0d00d01060100c80796243c1d030b0203c8a00c9031180c802c06e403011701c144150340c6402481903803440c0c503494003038410001e984d00f0b8180c004103c9400059550403c24002c8c6030590141580c607c0d00f0480c0c0074000c20a400048190b8001c60103040440f2103032100c00070034198058044855842031010414407841d1610904602a2410035680740c01c45800604000882c003460305620340b0030b1150499084c81103c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 646353021 1250 646351771 646351787
    0x170105100305090c03012a0207030b040f150504050a0b0f10060509040b060c0319031806021e040602010b2e050a140409050a0506120d0518031b030708011b 68
    0x903d840c291404210070801181c00c2d18941400304100e007403030090f190a91900d810b141d4842e120305d44010840c82c0d041d540c0344202501c01a201400c0d00800d22200e004002d01c20a40716103583c1d00c2e03a400e00445c107140c58815501c00c80f00c801211154011400070b240301940e103c0191143e00c0c40841e1010365071600005456950000117800d82050b11400c1040b110744034000200640c3c1e4004008550300c1e84880c48040c41c402600054030100340c1032000101c4400d10300802012000d410100040e591700841070a81c80c00b10007400c03d03c030060004900080d9064040d0b110344080d20050310750440344445030480801d2252104a8494221a0802460300713040c03140c005002199924103002e40e14002120300c41866800c030307034018004261210208039401c1c1c07190103029003085003640e80b0f0304030410300107a00d621050f010f6402001c02c400403c0008008450481003945000c0c0a001c2c0c4031181740000ca60100180d602030502c2c042e00c03842100048141051180400d003100000c4022090320300300034211a041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 646354271 1250 646353021 646353031
    0x405031c09140307050d020c10050f070f081801080606030403030902031504051e011a010503061305010308040305010e0f0a03210e010506011d18091516170105100305 73
    0x266555001c0340007600340c00401103024646001192030f4481440c00d1440c12070042151011900f02d410700c400760f030700d511105010411050910301e03101d10009011140c180103140024140d41c40c5589240700f4402003d006241c00320951181041c4801c81a00545642000740c40d4190003120030000100032074441c0e07100c0c44030688000c003520358440741d000070b055110000340d500b607816801c454901c00c0d4000d0b01c05003007425041c81070300030300c600c1e000000070304042c00705149002d0521000100142603a074401555824202c845030b000c00481d41c403030401d001c4540007408100d038103628000d1503804100000580c04007142c1d8102c0184401030003582c00300c8600f4410310a600d81580860115152110a8000d1280507080c401c0002150318050740010010901400928004040d80c01d04422544410141c6e8440c11990003080d00c1c2e07030300c4501400749014070b0807080149500c03a1f28103200e08020a40035009041c0710995810030b8055124441d914280028807880350300007003400122511038002e80060f5400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 646355521 1250 646354271 646354327
    0x9010207030803040b0609070e061b010e0307030305150901080a0f17030406051f060f0c230d030605090609072f0a210e1509060d1d06040503 62
    0x35540b9600c1d500b280d003040e1812518105201d080000f81d040c41e04103d0307405245880d1800b0f038000700c240440c81d18410060b205081c21100c0b09034181606d825000500d070480c41d01c003129624035190074000d0003441c0030f8901342c45000208891090920303290b8001c074162072000303021342148043c6a450b014044030251003260444441051020040d850303030082c2d44658003840c2d01140350300c0c0454007528283d102404604154122110611600d0741c003c00f231215444041c10800c0090600d4240036881031600491000a600f9080b55402c1c42c080104220070452241c0e1002c1c0304041d1584204504258100c03411071300841407400007007209200f15010b00c1040c20b00b60165000306d03070f80300140c6000c01c100c5100a2407a030150111104000c0c0041c41031045007980c2c03150031000682c0c0a030080c0102d14004080d4403c440e2001500400541501111810200200300700ea0b5a401d585441000d03014202c000f12002d004140b8818a01d20045030aa10955000c805985041e015000480c010740f048034a000300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 646356771 1250 646355521 646355533
    0x9100f23060d0b060d09020301050f10061805041109130612060203070c0b0114011b23070b0d1b0507020906090a110c1b1009121103030a0306050913030503010b090102 73
    0x250304c076000100710103411208041515a0320f4010716080d0742d03001e08a00c00c504032450070030135040e200324071003415aa8249020034038402d4124141d000040b00e5041a40d0151a02211800c50f45450006206a400645948811140e03401084040b14618824082d03884c0c0251102030005801e13500440c0e104009007031095000d00139444400448070241c000d86040c0418508951603903030440a02e6213031910726142d21003100f8255640c05266011046002c001d03698444041744105014000c1034040c00c6801d0314143c441d060099803601411032075aa440074001180da041c5180c600c200d0440c2c807613176006401401162520b000703002c03010f44001d1800f0301d12a41c51480c41c00c0155031000520700000c0d410000c000462502d0107401c1d14290f440200d82c42030912400c0c01042c1500101c07420f040382e0f070740302445210040c42e082010240c0c40c0059483e615000c00181440c0f031a40552081c0c007511800e4071507886a1b540d611560456208944014001c2881030004104003241c6100806030a281032045d0f40d2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 646358021 1250 646356771 646356791
    0x507150507050f0604051002040f0509061203070f0209010504020304050d1d130f1b12050c091206100b090d150b09040309170601032003070509100f23060d 68
    0x8149122900c031200f09070090014481030240c200000102603204900441c40c00b8a0450905c850016a1050b42d000d820351000151050303544000400700c5412074401e4a07610a410700d041e07261805803000480c170804ca120000b00d058202407081c1c0b0711940d80a8010a003231503000d4410340f911800d40c1454110380da15403102c00c03c180c540301d1030615200303083d1401098200c5401d0311007064440c690082004660700300c4805901c5644500c070403468141c09100040d0581740d0130f40202c1d4503c15030340c14503000814040303203d442240000c0d010b4800c19a16424150b81c41d2507e00c0e4102902c10721101d140d001c0682d001940128258000218488400d42c100141c01c003000300c08141010b40c122000d038045801483d04010046040183c80c0d1050050400b924140d03045958840d0202c01c80800d20020410800071414207880c10000f140241c2030051a40c281482c0403041000d4a45042c062a10502b900b2100003501003000f06032500b45042400c1d4440b020071144081c05041e4011a05d00d04610b529655114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 646359271 1250 646358021 646358023
    0x150c0f020d05011d0c0d0c030209041a0411010f0306030b280c0c03090b030f0411270a0605090903040b280f080c18092a070c05060403050715050705 65
    0x28200c1e8254810f81d6680344030791240b0900307004034900c2a078002c0c0d080420140011f604400c2590030340f541110300403403075111814002c0040c46601400c03410700400078207100a2001080c5840c04500b0b09a95456607901c64640440681d0388920005214904d0803020890782c0042c803ea0402c094403040d4011111110180c8000580d5461608031010681c00d8412000740340c0d05c600c102001d4803c0c061403d2950502441811910100810150079850740310302c40e1146d41e560514441c804011002c101401c181d6402043e08450025611040303424940071000555040c2701001e244038031181c202440c01d25103480d541d1500c99104800321381c0c1905201c0c508440c00d0011004140c0b091106980e86201485070740c80c00307044050080c00c1d80d000752106006040080135604103981724690103aa40240c41d440e210040c0311080034031541d41c80101c41001a02c12040851005030580d18082e58800825a649805024482c800c034040501680c001c10000c1c000b81c104908260f40901061401504d01041c68942d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 646360521 1250 646359271 646359281
    0x5010e0f030714090f09071418090c0f03010c08042022060e010b030a0905030c10020d0b0402030601080711070512010218040209010e04050603010906050408070c150c0f020d0501 78
    0xf100008200b9045809542054080c1d150321010001c0d80c88207504124000c1d41c5c0c0d4005c81d03c50044844000400e41ea4140c071605440380c3c5c041c0307240401303580701c2c00c0880784a81c8550061201074020245c0c40c25140441c0390500401c9580c04aa40740d02565440d40c1c0c035080c125940c40d20860301d043c84c11081212080d103c40940c034203100743d02e61100c0250720b0300140d000c0998440340d026a003c820803400500c00c803002c80044a40204150b070300022440d540745800380c111300908010f40201d0143c980d800c48640741607001043d42c3c244400c1c0803c0900289000c0008a010603580c031800200780d5070014a6070760003922444480c03e02101251105552080052075901d8044508ac805035008201490030080703107608100030500031101541800384803000200b00c40000341d90715124588880101d04030303032000c0d840b012145800200501042c0b826040c5002194000f00089801c0d00005d400020f4000c0c54194400d815142c0e03540b80c62000e5141e84800c0c4074a2410201070344d1200429680c400060024415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 646361771 1250 646360521 646360529
    0x606030105070e10030b06040f2405030f0112050708010507110f1605120f0604030507020103200904020a031104080a020102070806010509191b0921020306040b1003061e0b1905010e0f0307 82
    0x14900402c0c5c83d90000cad400c850340300c166500a001c018818000c9048030324a00f941501c1405441c160101c030281406482d01ca045d07030000000307518003000d0103034240c0c0c00780080c1404807001040b94102900380d8001c1d03a0300c0329980d55040070305d4980c0e0f6040c40300b458090f4a801030300752070310115002004c43c0b02c01c503403c3c410181c0c0d048000c00c9000814600b1560107003e814048466505190803618074043c181816108000e4600d200d117a00044480c0c80d00d010341d111068180c4414801034032180c0350340c1444c3e42c810f84c1d008140d025105101002032400000240c1d90305852000d001c0105ca500c4540140c1c807002c00740c01c0000351068075810102c8503103250b84c02101030700081e9a80c1000ca580360030304600c3c941c0800480c0b480c100b900d503203280d400f41c0c80c0018025003080e40480740c14004e03650783c1c0070b8070f500c0d43c1c0c580c10007004242880202c4035503d04180d00e1881603102400104880c6074010208580301c9030062400e024a520444c0400c6958021800e8441c41080035200390090b4044030006410010a500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 646363021 1250 646361771 646361789
    0x1e0306060c150618060a06050a0c05011401080106170309011211030a140106020a0807150902030607052203030e0d02010905060c0f0f03091c030c140606030105070e10030b06040f 78
    0xc0020f54505900d64242076081070002403d02d04080d001310784400300e1402803500b44040021009241c44c0f10b06444070f03c403500034008204540e40359451050042d428810805550700b4800d010480080190a828030707440600300031407400c0e18074001076036401c80d0014412011940d0761030345100140c110008600c103030703903020000074002c1c61034042403114003040c0c201c40c0c02c642c80503003040300054603d0112181c0c0341d00020b49c0d010101000418901910309040000c1d05405a2001d02894603001400f4051064074000d0f40e20416005000910044855200240001d1a064007140003400d00083c002c2c1c00703e0040c5030565280b0f4403807012500ca94048032848103241c1c0308150f0740c0d0301e1803014440c980103440c0020203103280c091001c0001d50780c046540030b5001c9100010240b40100750040400307840d104c0d401901d440010002100c066211b0b442121443d0007942000000342003e03109260046402c0d40c002c007034145101500c4011030040c410000e410707400800c10400403d0085002c88800010035100d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 646364271 1250 646363021 646363063
    0x160e190507110d0201020a050703030b0a170f0d081b0c0f0106060e0102070e0c030402100207150801030b07080103031d0a0f080d140c030d27060b010f051e0306060c 72
    0x3400c2c2c80ca0501d42250000c210391050000c0c50010382e00104803295180c051401049081e0300c07170006505050703a64021244103108400c0b401000744040b0301041d1203000482621032100700300030180d81107002180d80310700d10001d040b0180c010921031006410000090b40c1114400410004400e003111000c3d040407000c640e40f00d40039002513070f0400400020f05200c40140195042080b0b0608550202410092044210351004140d203442000030340020402c14207511801c0103211805808600d003801306a038800001c9001500040c0204007483c104c9034565035446050a03c205001ea1800a040e8129440151148000b6040b06c00100c010064540386000c0c082d4200701e808050a080d8104155110002e010b2042281c04100071003500c041e00781c160300101e1030800074049000591103c3d81d0740035005601000100c14803000d54890281301c0020303214a900480303140c800f96000d002d4014110340500400c02000346e1490840003550304100050440303070034403544440b8981050030759501002ca180c07040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 646365521 1250 646364271 646364297
    0x90903130f05032107060902030a0807080301050906100f11010b0a1d0f0411040c031409010f1d0c040902150f120709080a0f1e0609050f160e190507 65
    0x103004044e0701132041c10094403036820b0312001c48414054090041e08940e6148465015914203003e15154143c2c00a80242d55500030325003282e958000b8007540b4010302b0060001001400c0c4000302000c640c14588600312001c0354000129900306d4141c4600c8015500c8102a9a00d92107030540b442c0581841d2a132034824400311b0070480c02c1400c009041c04604008401800003045203014505506581a9008106040300a10039000740c02a03e00c0060314030a00c108000b80305806501001c80c03204003003014000b120012609140c110a607005050568003e649070000c1c903c5c181d442503230800e1000d070003410445c0543d81080260340040031000304e20200054420307070185158a84550101d1181443c01000c0d06180140755a044944001481019010020000e1212100c84449111480a04041c51441c2841c2400c040c1a403040704580328400d960280c0d03101c420100b11001c0460a076040f80c00341a241c26205815150050480c443c0c04c15050a13150101c07946014440c8101100e031a0241c0115203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 646366771 1250 646365521 646365523
    0x20702040b1807030e07170f0705010206150609040e0d0215160801182a1407020306281b1b0c05041e0903080402190501020c090903130f0503 62
    0x400e040c10b01c40c40145a4000d010344010024540054641c64009503201407690000e02d040351030341140c1412080807004e40700d58440065480d22100306001520b03d41c580d500010381e596203003034518813007070070640d03409005c0781c01c0c000090090440010008504c0c1550440040e051404c204000c2e80160400c0004084092200d140141c0041020300c102484d5800383c40018070884060003007840c4440c00c1500d5503c0d81c0c406400064000101507004002641c0c882c20542001500d0344800c404101c800c8200d0100300d00107030541f00810307000fa014161507030303401c0502099610b080c000020b40107540c070b07200d0440620038880c4041d8040300400001b01000150405001d0481502c50b03041c010195071019400610410721400c12201c0c01d9802190300e90725200030b109000c035414440100180703029451810315901c03081080c0030b140281e03031511001c400305504c041040c12901440340984d0000816802e103003000408142d01c60210700659040000f00c040300026605203034002012075100b0392040c441c900d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 646368021 1250 646366771 646366781
    0x3030e0601080d050a0c1b0b0d06090b0a03080a02070902190815180903120c0d18081206010908010c08010e1303080f13050d03020a120903020a060b0f1302070204 71
    0xb1102006100d5816200e42c000c0c001c1c45500520b40c10008080c2000e010860000343c02840010004142400991121800d091680000440107980e50034a0303c0001c5041c01032040e00001c0300040c0c005260079045441d240200c0c0e01c1141000c045100f80c420000f1210400e101814005901c03030000380503c141da40d001402c000029010040101c00030941100f9a034800c51084801003200511000341e0382d40e042021300318080e40302156140008401082a0070306294010286500908400c00075a6020301060300c4550041c0001441a401003200000001c4c00f8445030354031070340500d030498032180c54500142c203440c90601c0d07010104107080014441d109401c032103e82e1181021002c80024105a00d0080105601038080803654100201140043c0031491040d01c1242e08a403c03105020b00c0240000c0080d80441007030340004825114010340c0e50040c0c0200e210007505039005004000464071180018404003000c0e6502540c80c0324100b130303e500c90014500b584c03e10003000580b42d0f400717401448140c076 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 646369271 1250 646368021 646368029
    0x5032403030403030306180c1209061811040e07051018051309060b01030b030d0516020901060818120a080a0e06090109110906060a050a1101090f050f150a0c050708040303030e0601 79
    0x7070522001234401607011403d22845082d8420104113102e040c10942e000b001344090840c00b680740c1c0c031190384c107104218201402407002540d0410541904d006429200c0748d940c01581e1b2712144500b0605080d40c811000c80e00e110600e4002c45e91786998441c00125141000541964240d80361a800d0041c02240d11400048400a0805004450071500069100c03194840b014007400404a407000345d0782a09512020181e41c0900311111658646070302420364032044400300074003e9030302002001c00c1004a503181032801d4070100e490901c2401070083c0d885400007461521000ea542d4801a10f8080800c030741030040c0101d000000700d00c000348c02c0040600010800131400b800600092140c152a5401211503045282c9480340d2a000488170464001c2000c1c00d590800790300305075039a800d200f814505440030a00c21801c0300c0d0744111203284180c880d014882000d00e0341c2032443c00150300211a822441180303c882c81d0052400e01c80e540d41204680041c0c2065001079038401c400303680710a080007140d000d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 646370521 1250 646369271 646369319
    0x19110d0c061d1f0f050408120a1e0c02150a060510031a04020f1201141017010311040e15090d1106070516060f0e0105061005032403030403030306 64
    0x9006020891581d41c000aa00c98000e03100018590b41801e4441e440610041c4c2c2085044c042c2d824241805251500080341d07002044001802168030717410a807040070500380648550010f0b10303081c1c4600c00020004c2e24015000c1d0300901c5800c182500741c8001c0c0d81c1c40b170715440200080d0a030601d0244002c0e846481080070a140ca41030460750816030000040002c841c08540150703460f61450078101c007a0040c42c3c010b850192000c0300110301c070440c070002c1c25000841921081a000400c03a8116841941d0034041c2540791965001400882c000d20070301150300002800c04100115110031491808503904d02c504402007480040c4001c0d00c0e03003848000c10343c1780315103421071071500d80d202050b0f241e00018002e4070a1200004a09600041556100001030341148040050310041c03440f400140c154102d141c141540713020000388c0e4030b04e0400d90351a00200c981d9a0641140c1c0c0c0c1d109851008081c03c05690300e07006080d401c01186903400c100810103107201c0e03900030a0301450720203030300c07030f04980b002c802411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 646371771 1250 646370521 646370561
    0x3020d061b0f1d0a081519090b060108040503132304090812060102210a080903160f1b030c1703090108040303091103070f0807091119110d0c06 63
    0x342d0b500600b40001044032040d0702c400c12031000009400d804250344144c90307900540120308884001246034520424140b90070750b1540b41d074564440104c501030b400042146407218042a125442030721500d41c014412001ca17849c142444c070a4001031000e69208800c038a6a59844030312425008078000d090000a681c107004a4415035030b00c500900443c4d5259142010090016031360381e100b0010203008d915007000e80280c0988034011425540d000003c210041440c101c0030455480d030000441c0e01040500c40b0b4281e6070991696100141c61444105540000300200325283c1e80c0210900c06000b14030958440c0092450100c0305030b8441c0581e500f602d459007003840001308590b004180194010b03030600d40010058020f02d0f01c4c203540d03d10716614a406100b202400b00341200c514001500f91084603044854003990f49290078141c0c2c6d070400001c0403810f4240200d409a1000340d56072100c3d61480c3c1480d00c001545065000e02c1c10b80b00300e4089000910000c000c0e0203100d40d5200740d07401e0000075058140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 646373021 1250 646371771 646371797
    0x40605040b090112151401081606080a1109100203031608040f08210a021e16021504080609101a010206060108091e0d09061b02130603020d061b 63
    0x20300b20105219100e0501d1244900d41c0c10405001142a01c14950b80c404202814824503035201402c42405040e1540c8155183d151540305030140400490300035030386da040d0075510800900088c0100010200d8071050521064145585051010103214140e90085850b13140c00c40007401c01c3c01001d082c0200740700310701003840007088007628000455501304041c1c90707030781d0000c60410107051350344c8004841070b940c0300042c02001101a001007046800040c90108808a40c1d50b42d210705100340304510081e0420140c1c464014105081d100ba003400e1520f06050800c0c1d42c507000c0341e0a1000840c0e8010282d00017080b4084804000c1c85048521315030450261426921040040d54030400504134505000c818000030300b10b010f0800403001c1580181c2c03180694420000c44040c3e44400342c03403941000c02c640c1c8034042500da2103582d80800300e03001d21000ca00600703142d40034031070f0003605c0180504072a610b804011015841c0e400c00140340d984a1180061210355400082c00c1110a0034420020040c134044001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 646374271 1250 646373021 646373029
    0x9120206070c0506040b060f1f021c09050405040c1505070201080a0204121506080d18060813030c020a090207030518041b0806030a0203161d01061704110915040605040b 74
    0x503a000e07500c607606d07000b0342c1c8407403000801e8402c1c551505270340900f2014800000e1202c814013425103010940844003944500d00003003440c6240e181280d0000381d1180010012413030240c000c143c1090040070340303000c82621141450001365908014801003000003131002d0071964070140c0309500c07022903001142024140690581c01c0e490504014050864104240c2c800c0c200b16800a401000020708541014070000c0300074110803040c504810350100241c00010b40c040c041d45d002441006907842d0500d0f44441c1307640c1511450850b000980c1c2242d2051400b003081101803005204050107910b41580720000d8246501906050300640c5024a0038408030f929120201110600705003a541040c40c8075030381e0a0b02180c07824034042400b035458407444004120628103c1600400d0f101520480b0100d004007080741440340100f0b1043d900007904c0001d5200e80c030841e21481580042c401d440303510321900b03503400158915000303844000d00140700d50024495443c0510446000b824113aa0520280c4403400c001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 646375521 1250 646374271 646374283
    0x21b0606061309090c170c0108060603060d080a030e100506040c030b1521010e0708160f050a050d0c091d1003020d03050c010203040c0e010e060d1704030609120206070c05 75
    0xaa50056104d801030020000e0421343d00000d08a40888524584da010004540d50411420818042680710b00030941c40c1c00d01204907442040083c004070340d2100c496440c16056405580c1d10003c05940c4c0c1010303402124140130910410646072804034a5007130038000c020031946182e908001b850b02c1c140b10a417040d00c0e00c079101c0383c542441100d0b0766180c8c2107441c0c441d40020116110b04889488072000402d04101130202d041c081d106c25510f00c0d84940d540c20280c0c140c243c0c5144144085180040d0070034440b841580104030b0710245141c81c504240145943c00c080c0ca9080c502c0740e0101d0480c15050001523070076a451111300c44644402c0c012828454402d52044004bc08064010b07680346c3c40001c00c2c103000e0342c100c80802d951900210b550345401d040400000100e4050070580c0d6032124000200080111030b80c501407076005081350460303400d0340e07941c0035603803001488050341400611000003c5045032090016960113580101118420b90000904200c3c0003000902406605200307000031038000685 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 646376771 1250 646375521 646375529
    0x6090a090317070903020a09021b030c070e040c121112070b0d0e03220905070905010806010309050c03031303110d050a080904090c080318010e03031219021b06060613 73
    0x1c81c90561610343d0304035503c454a40000e904240314200000f40f0012580c024492a441e18402004542c0c0c201c01782e80e03c901c00d1007181180d6511100c010310803003079070703480c0385800c58442c915002800d80e40e40004c2d110340348501170a851281401e03800034103d06000b001c10300900358880203440c0540c00c060144949002c1c40000f030010a5869110a480090400488921403d0030070819001c80035070744030481e01500d50084040450a11005c2074020f8054410340050b035405031103c3c841e982c4c80c0c1c2c00450041c21800c209542d9486030440c45c0506803420b00c0146401984005228403150440c180071950380d0b40006594010340303d440c0044082900030400e100c070075a010701d40c40ea0b04d90040000030041d00c02024080c10f014403e10001480c1c5d81b000009281059480d050389004002d194010346401d40851589a003641041000d44140e092291140750300c10041e2012a801c0056081140c003283c216104400742c920000c05280c1e402002009440d40c016001c8652503c0c12140d120310110521240c49 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 646378021 1250 646376771 646376807
    0x50a022a01150b0a020c030d050306040203060d0210050a180303020a02010c0c1a09030613151805060c0a08090a08070b0c221508041716060204080606090a0903 70
    0x2105458461081d08102c0001c0030703030005007860b640c0310b18204030107078491164003000d4480e50603240d240e4180070400300e41410791500c450382150340380801e00002c6c1d40002c000785d92004c0c400304040010b9a450800440340340341e6686150702c54545110262a90350034032002c1c1c084403148441003000036400200304a84071350a1038105107208d4207160501c0300201d5a001038026440441000c0c4040001c0c402070000d0307000850031070303c42d80c48120840c07007020310130880130b003041e042c0c03042e0000c0c1e08000e50040000004907221041c040c503021303140c0c1801c0103001c3d501c5000070030000840c2c5c51070700d5018040a4015004401401c241c2348a592202e260f171051050050104c3d1182000807052070400041e034a440c013181c04c0710344101c003400302c1164904040d03015400720b054040c80092200c51281c0b4609219a034000d55140e4000042c0314120080d4112081c20031050b02c41602440014540780003900007050044002e1407503050940411001910081c0800000d618000202c0c2c0442e51203401d89141d490702075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 646379271 1250 646378021 646378087
    0xc0a110a150903051e09010f110705010e0d0c03081803030a1d01110f0706030608010b0a030f050313030c0807090203090c0d0206040f0e06090c040f1a0d0f090303050a02 74
    0x101c3d00703451501404600507024a107009100f400ea440e42e000400016100341d884803420180d0780e0382a141d0395044010302c44503501001c000c3c00380d54040c03031500c140004000c210440c1c0e02c40c591754003d08070031a504203ea04030404982101c5180b40b150340801c4c05c603001c4000d181885601c000060840c03508100c104c50303e90482e50501ca040e406500b0300e01c6285040026030f8000c948501d9200d82d01c0b030303061081030300003490400e0015442030184103034543d40800503c8110300c05d2842c3c442c0000c10044940c2600d25002c100000c80700001c2c01c0301c108000303600c04d00380000c03940d140000b464208a0180c0c490640c0c24010010481031100100384d18038501d004a4028180203001d0012501c14001d5030014084000d5114000c521030700808050340c8158012034901c00e150761104241492030160703204884c0c11695080060100c13403100302008120805058256042c8954448904261400b144010070b50982d00da608205040c1d2500603660b10884a030382c00e501c1c003e46008442d1b0307404400c240030000d2014035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 646380521 1250 646379271 646379273
    0xf0609140f060a0506041403100c200712050a14010203040209060418020402030c07060b0d0209010e07020a08070c0302031b1f020f010f05063c040e060c0a110a1509 72
    0x4400c0b0b40e005008054171041c0c0369510f4000944400079071a000781d2183c4640480c00c03270b0703401e25806030920059855884a480b406440d1f00e140c02485030710303c0047c0600070394101040c607806030500442c0e143c2c01940223002440d1070b400d090212000c41c481550282e40104100400b68461036040e80c1c02c0003040e14006112000c3c4100c14402d8544014001e40c058000018070040700b44a002a0180d98003480781040b0b480600401c2140b008000e800081d001a0140f00400843c0411980d69134071081d14019203c1c2c8104035510707030115500100085620411040c000e00540c2000c104c1035031120544680c03084100c1e14000082c0c200c2480c900c02900c80000540a05106882403008560002c4d00c0002485070707948803298900a490112070183c000c0c0c80590803455500c40c1c00048a048c0722410b0303005000c410a011400b00481c44005001c3d03045520f4845e01a41d001041200510074a00681026218a0a450002c2030985e104500341c8403030380700388a801d01045180800c1c1c0340081102600082041d65 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 646381771 1250 646380521 646380529
    0x1a070303020d06090b0a0f1d060316080d1b03020c040509101404120519031505100f0807020a17031f090203090606120c0909120d0f0609140f06 63
    0x212030302e00032224200940010a41219082045001c03c12919100780030340340d480540b2805031510407458400f92204d020a44646051189604000082c1c02e440c4810310142c640e480d01040303540307e00f5807076204100340c0300450340c0103941150342d541c8140e4105064255413002943c81425410140c0b1640d80c07640800c500c4202084401c0c0c0c460a0703104140000b804c440000d2000520860307040d40c2da43d03060085074070a640b0030340456490b00508004d5424100d0640310403802032600b181e80682c8250144004a02c0307589145210741710304c0482d607401100840f040001000c1c1ea0015104506540c44560142e00007001555024080c4181c1c0050710340303039914440d1411420840c003201c02ea050001035404280305c0d41c2d41e002144113180c05c0085500c3da80340c4006101507800c0c8100b020002c3d070010381c10b02c1c1e103502c0d040d07507640e81240071351b011108041e1405a00d00e40347e90040300c001d003d03030355240740c8072010780001d019510040c0040c040402c181e10131048503881e8100d000300b0300c0200122800001e45560741d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 646383021 1250 646381771 646381777
    0x1080c1b1b13141602072c06010804021309020f0402120601020c060f1c020d09080408150f01090902010c05030c070614030915040302030c030f041806050109150e0312070212071a07030302 82
    0x280040f15501d807c0954541d4400440120000da0f107140b1050001900743d4042e87c0c1c0749005650103013410000701042e5051000420780301c0d20481e804980f2203002421580c950002d0b014a03034040d100c2c00014244200003a280c07518800920703008105c140654942450524140d50040640c4040f04071100400b100c060000c0c45040401e0004c0b5143c142208140480c49019000340c0c0c1805086403885612500f42c1070f00032070110b0f4040d8454442034014000c6800d160813040c01c051040c1440c01c01903213541d41d000c0c2581c2040d4461401b03075000d6001000151350000c001440c520101d4912440c500740000216200c20310420658000744140002c00c0c20981708204644030b030944c43d002c2d00d481e41e40c850485002507005108441d48412164440d401c4c95600b48034020450790143c40308403195103000039410f8070801c805400024030481c41241a0075843c00d10000940c40c18881c2820790707500700c41c0b04000364030380b04910002c0c0c80d42c412441070120450202400000b540c844010b02d0721031140d450203c010784 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 646384271 1250 646383021 646383029
    0x1b060a0f0c0507030f12031505100c0c1811030c0a0c0f05010501031203110c0a020405070905030616021501150516080c1608010b01080c1b1b1314160207 67
    0x103c1640000428041c040001c1e20781c031303407003007225064055480c901181503400701c07801110311203003c0c2c4040015207404503c4520103801424441c8914510b600c0d188140c0e0359580c0820781d002400d5091940100c41840751030710034401644280c9c254202501c003803001c0d0050510700c03c18800d40041c5030301442840001280c5055005009205944c0c42c1d10b01001c0e914409400540400d00300303c40320203040044025201d2030ba00d000000c0048030020340801001c0c110143c41c01d03060002e8040049100c0d05c0078444140b140c41940102d180d8500501002490400c03042d10f0f91200b009a0750041c0900c00c004c028983c140c20507494034684410304100c5502002080c0c0a0003008080000b4840c0020f040c0400c0c2c4070701c00c014240024030100da60f003003003d0a131034030103440e54002403413a070002e500229000050142200c50b13016102403161240255460a00501d01c045001c980b04820090680307441d0310880b24800014000b44101d1015110325180e040002d00b20541c600d8a01c4400b081c114401c00c08503000f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 646385521 1250 646384271 646384273
    0x6060e0a060e0f0f0d0c050102011a032a0d05010603020f04111e090604060c0c092f09030607050301180c0f11100c09090608011802100201090f0804081b060a0f0c05 72
    0x3008031703481d2800242c280c40c854540954207002042c80c03403001c1e0030944108148050041c1c9054405038076400320419401800941204141c07850b0300880c0c503045d50f4022014440c0c40001201402e40c010044070019a0000c0b5114905101c5070b6504005004140d41c200c0d049030740d4a8080784442c00350360f1094050844029042070003c0390000381075a026522407882c2d4054001c050b1600d444035410b0b41605c0500410341c008100340009014892107000a80703141040c02c1344c205003403800e010002803c03c14291845070002e18003000500c00588400601c00300c2d02c0c802c180400640d440800c1c06818031902e91110014001504201c80100c0001d1084081400194101300a10000c406c3c000d494074580d03024029400e071810784042490301c8148070b07000200e850400ca610890700c06608112020030500140c100710f549a00d00003000617040304520040901c9000d43c141c80b54207013501186401d400071100e140e0241152a038580341d480308412180090070f81d01d0a0a00544400b03025141074200a10003010703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 646386771 1250 646385521 646385539
    0x803040c0504020720031b0d03110f030a0207060e010f030f0207050114090f010513080c031215011409010818150a090209091b130f050a06060e0a060e0f0f 68
    0x8000351045e007456111501008501c03548580c00070b00d59103c06000c0307880a410080d10003d1150b10304240c036401500d01c80c2c0b603d4a05c082c84000e14034100703584c00400742c0305903001103036141489405100003406001d0328500503021400410009111a003502c0f0440705159540283c00f0245401e60101c805541c1c1060080c000690841c60700d5054070011120103540d8001e54140d00c0d1401e50601445018201d140c4000d801300c4a01e0302c035000c0d030341d110107011000340c030040201d840e86059400142c0d01c190bc000c00014803040303c880016010300c4144000801c0b08104000d07500c066a080018250401c0d40c9001c20006081c441003514900204034130842e40e0210b0600401c500400280c0084030400d01c01e445103482901c2c0c0200983d952101120249a510341141e000402c030300b0640c0e000c1400f10310003100400d444880e05400d40440d4420380d020b641840e2248414404107811001403010b0100690300541242e1801034010040703060034083c5480b0f4440304400c404195103c4105d81102d800040680072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 646388021 1250 646386771 646386773
    0x60402041e140a03020f100309022809050f0a1d010f0f1406030a0312060e0403050a090f0b04030204090c08032b020a1b030201090b07091706010506070803040c05040207 74
    0x7203410064428040006003046a14829050003219401101d5010300a100500415000c0110001801c4803c03010180e1301c0d40c0e030001590303503c56807140c0800210035140404501c940b2181c21851113803c181186410441403103080c005e144035030b41d400a0010400541d56685044135100601030364040c0c0b04540c20284800ca103021158806025401101010008000c008501c24841d007401c40380341e1740c1074020000740d00101c1d0107441e10120161600100280c05a203400f10605a4102650141d00240020485100054000e0009000303040000340d00c0303400d185000c80021180c480e600000703020fa5150034080341002280c0c01180d001c2c14451003900e07180e08410640d22902d410b03010500c40198001d40742c0103262141c40c030855103950255a60000848804134548243e0420b0710400c80466507200441c1020401843d1058040c0403156104200c10f1300d454a00c41c46407481510294060b00300300c0c0100415a45c520844401907449294103480f40d44a080050484c10550700150b00b2031300014000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 646389271 1250 646388021 646388069
    0x103020f010e090a0f0b040605010519050906040e04050c030a0b0c210708250804020103020c030d090510060e0921040e070203120a0b21120d06170f0a03030506040204 73
    0x1d017090445c0c4c002003010b075080d407003003109640a5100e16404241d0801403c1ca004d0704100c84100c0d4000d1a003800e42c0380145040c045195688580d2280120000038410301040100038040510084801c500801d24510182c45000c172060010704410346402000a01450bc44441c1c503080d0320500310301c42022114074001c400500111401c0355107134805202d804042448891420441900000c01da840d051217a03150342c0150000d6001025111176444244800c01c400c2a0742c0c0610291207100d0006031150054003042e0358140c80300ca8012500c450842c2c2d082000c2210000b602603056166010041c281d0080d01c00c0b84141c5118a030000010345545d00100910580c0010080c524580506159005540ea400c1e00f0b40443c0d4503144516404650b8840e2010650301120407580c0b242c0652041d148080040380c840c00b0503a206a110f0490b450300c0d00403c00949032420000e9400006290181003030511a813581500c1c0e004c0c106005040c1541c40022580c2525207074181da02800000d54142c0b40c001d01d40d1084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 646390521 1250 646389271 646389281
    0x31e0231230106050a08070302030a090204051303080115021b01030902030f030a02060c040b1c0f1415030a0b07031a06160506010f0506160f08071a070e01080103020f010e090a 77
    0x1c041100764903000050304921038802c440400f81141e65903c4030f500c407640124081c0d4000380132507561646910701540541c0c0c452182d80d004a00910b550322281d00701b0714000c1c054000580c0550711454070107030290800380c0c0104201004030300c03550b40303091006159001078008101d00031000c2c2d0103100780b404070360503104000020880324005400f00c941980c1d480080c0c148038460742c01495003c25083c00f24034142d03d500c0c041e100407892100c4010413200600f684000031100d0004c2440114440789040c4441045181000d66070b4103801c0e8040c01ea100f07800d4036120030303084001d08414201603480441d04a020b1074594980e0070b034880100442d64589003c607540b80e80c05c3d40c40c00192054000e0300700005080e1000c0b41041c00319000544841d04100b500c070542c401600b256103060702c9010b42010120001502e50009110f41881a03103410300381045030703c01c40640c0c10000c1c501e0041c852034003000b102980c3c2081c0014116641280d035000514100c9004031224050300c02c608d90810207400c10700c182c80c42681c1007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 646391771 1250 646390521 646390571
    0x303030b0303040609030201050c101518050915040c0b1809150f13241a03060117070c0b0414010b06070213180c0f031e0231 55
    0x814418080680d04054072440b607442000041003880310100015401000a03208506880041d03d41d814161803980059504540c0a03800c8042c080c24144090408150481088848500c0c20011840d00483d030541d6400300c0e07a002620740585c0ca0005081188460441d000380c6010b010060b200c00c8601c4800e08c8080d0350300c0f9642d204603000340000301d10302d911519a00d1103690050044603120603510505c50702c9580f6809410030a030f00d0710000080300c3c0e03404000c031101103048910141490b02c3c00b141300108142506223030071540340070020b00c41640c0e440600c03206643d9600c100e40d841621500300c1a200340820103c0208504075030002c20051083c002d03055610023980320024450043d0003c20420523100c0d00d0b8001354401750504c243c080f043c25650040100c44055000317440c241c0d9642d1990204900c1c50341c130082000402c2030741801044000d018510301d501b00c0c140f8030b6a440c002580000c100101464100354600001d5176020b05a40b0504446048208500810008401d4400ca0300d032000310000c603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 646393021 1250 646391771 646391777
    0x7150618050402030a02040c0c0b010b0a031d0d0e0f100e090106090e1302010c1403040305070506030c1206060d09060b120313030f0c1701050a050709080a1506030b090303010303 78
    0x31034003549011500a262295034028080d082007101c50b42000014088416680c04010325900c103000001e03c1090068040c01040c01c0e031030f4694018400c010701baa001051060302800301c03140f201e81111070000c1c45460032007035401e0181c8800380803008220300e03002914609034010841e8200650344c03900400d4201000c1c0081da1018051307a2038000690384020240324a458030469200056442e00c0c891308a405031601c1403504030a4074400340c40d5905041c00c650880c15003600000b408008102c41040740a00a040c00d517011030851a0414080c0743c240a81013181c80008a00e10000b8019580c0d10100d40d41440c081b0b9082141c944c0908110004208046242d80540710441c1e032900f1041002080d14001c2070030200801403681140e0380c1515000e4400002c41d440032446001003130001c1303008190a0400710100000a861600d000362009550003d08081d040c481c0142c0284400807020610400c0a41c100904203043c1c8603d003542d4000301050740c070245c01100010217200311100301100850482c0d001395 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 646394271 1250 646393021 646393049
    0xc0605070507081c050c03041d07020105070f0e01081509012309010e18010207170a1b0201022a030118031403010506031303020309090709170102041a0f071506 70
    0x7070080c1d40d80d001c4400031680131114001094001803040c0028914984040700b50fa050590320b100c44100260402e0036084110141003c011201c1d90910910f944a640e0785401a0341c51019800906141128a000e604204074180050300c0d03a42c552000442041015095140342e603520340b07003541007840180034100e91045400900e0400d203024050281030718114040500c1507254924000400b0740c900049403495502406001d0200c0c0881e0752810303084003400f940b15a9598080c034010700c42d44405420b46001c4145071600c0b40542d9000403984441000c010b0171300f0404900800c6409504160441a85e0540c200340c00d042d148240700000c0311a46220343c44105a1056040400c406808240903076500700c1000d000042484c2e4003150202c510320301a0059070b00c3d00c2d245c45c2c00f08a40070401c540d1040420050082000a1800e2800b041c4401c40084002c41c10142400a09030f46042d0001e00f64901c5880403441e03031040091841100d044030350000d0f540700002c04925442d006040c4510170034003117101c05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 646395521 1250 646394271 646394279
    0xd080406121a190f031a1602060406022b020c0d0f0212030406060b12041709011d030715210e1914030a0c02130209031b0d0c0605070507 60
    0xd000300b0b400260811054080e1100c0c02041c0080f115000c161079406000070440024816030138494000170b540501090203034843d00603c0c1e00c85091025180000150205262040c242e50219a541d0001e60101340541d40c1c5c0302c201e003100c2d041040c00d0700600c510b203a0352070741528940090b402020200700100170b8031021080b8130002d88040051801c1c0c280540c0001411014482922005550151180d0000110152100394903500e6802c906118078000c0030381d80601c42449016040c1030b4400410f040b6007498801c0b000c000a0040902c01510151409039140c182100e45d41030140c0c034058151800c48a0100c201008000c00c1d07081c1110070700707408134100242d1565a0105024a0b0024181000244640a004883c061801c50070712001c0e24141c03034002403014028010b00090940201c07580e03508050358540d00400c0b01c000c022041883e4202d1042054200b291030115100c0071910091020076001c400000c00314044581c8500009c00c1c00c01d1072800802c81039000000340001034054011141e075191a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 646396771 1250 646395521 646395557
    0x301061e060f02060a0504171909090c051e12190e0607090608102c0c0403170a02030910081e01030809120106050d12170114010f0e0d080406 62
    0x40d0066802c01a0844000502c1e60b4040350032260b080703032181085080007c000c2c0d40ca0400c2e1b40113074030119003180180ca100300d00e90b0390045c0c51030050b049440302000400544035025100f0f2290340e440403086040841030500101d5a041500c2443d816088108070b1460600340111400a044500305ca40510382020409035000004440703204401503203035007400d5402d10000f40c0e400d000c01045940040c40341d58020950f14001c2d40102c07441c0240f606c00b50910000012540507920b40101090045802403008001117544140c80488081046040ba5602e21005404904500c03030317a09040c4d04440c200d1400c100c143e9104c2a114855691446006949400e21040d2105a1003c1c880941401801e010352400c514041049206c107050a100010b5450780da40301003584a89950420b440702d00008002e01e101c0b5070002c2c07034200000202c071500001981007800c121a404628030115042050b120002805c0c103000b03116a4005180041c1640b484116030f20b8000200c0d48180641c0d4002503081e80e035806a401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 646398021 1250 646396771 646396787
    0x1512050a052a1602040b0d05010e0c0103090804060503070210020c0d0815011718060114011b031d0409060e0d030c0903020901050d0f12080402150c0d0c020604050301061e06 76
    0x5100a903151400500c3e502e10b20f20481640c2d010313680195500c1d032034412903a0b400d903149286d6114600200305444008241414148000e0560b4141810098404005450072013100c003540c181d41045502ca4503048002c030315190940400e01040ca100080029000d42c0c00201c0c0d506010031b81d03407003000690707542e8000c0c0b15000c00f260000b404145664409844a144d25203240d50004a55a01c1581003d038003c01070320303101e42079000d00d400004010712403040303507800740c503021440000a00f840302d403d0b4981c0d0300801c00a451081459030304114803100d01d899840d5004006610f401080600210b540f00101644940110308648080392404400d210140e002d1802c410480342c00400c44000750703283c0010301c1a6070302c016074110760000303422480d200040c25140e01c14003904c8407503503200181c0c0342520501c40308000d024142040d80c0414032400541100003c1c00c035071141d072285440b8044002d1840441c419015540040786d041d401d0440c0444c203001c45c03140684c0d41e035180c4282c0c0b0014035074800090718500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 646399271 1250 646398021 646398091
    0x1404170d0507031b030509040f0219050c0a06110724201b032802160b0d09030201060801050a0b0405010b030403050a1d09040b0115090608011512050a05 67
    0x14201d00100c41c001c00002d0005403445e02904265180c0b0100400182c00c50b00b0700c2c5882d00d00142d0100744c1c01950200100351411004450401601d4000080c0c1129510224003d004280d03a403100c00c201e02d0030681030155011a90310941d004018000b07103801d0741d400b02908800c4030145140c503014401102c41018080050402c90050341d01d040560010302c00e0161012681204601c070800c8192981da9107100c031208100b6070100725540d0b011141d01d0081c142007917115800c9402c0b100740f405000301c0101d0821594849201d420001e24036001e1f2500f60301610302680106c140e54a080100500c0489075000324018801c01c0300c2c10031044c0e03207078500b00e1214003080c1c41c0580010814081d025129016140200d00320a10420f215507001c26400003404885d01100d08072811301400c4010440c034048040401c41086160803d541c100f0300701070004124800501c2ba04035041c66405100c51140d0281c04201d04141c00c0650a11040c50a001c92001400b01519600140c2411445105401c451080504c40030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 646400521 1250 646399271 646399277
    0xe06031c0e011803081c0b0a140111100507020c1507120c060c030f110304030f050318030408010506030c030601150305041a090f07090b060306060a1404170d050703 72
    0x140311103503022100c401c01c200e0081d041c0004100030107031040380c03207031000c00a501c80d00c81d4a80e00d01944480c541c250200407031a05000f410f040803800642d468140c803005490140040c61003444020004980024480b00b81d003c0300d02a116107203407801c4031604410f1291036035408942d8074154080038460000c541c400e69001602040c41001c0000d040300000302034100e0319181005820055481b0242119044034080300440c0c0d54801000908145000729048000d41d030000c9411417030f141d00c1c090402150760101d002008000000a4142100c0c1c9140704000508101140d898a40701c40c0e9a038020300c8141d82283c404d100b00c014600382880e0001c1d1982c10707610300000b0030940200380c084c150060b0001070001c9400e03160f2200c45454403620011310034454000b0a0082c441324a102c003d00c1d040201c141c1256002c02c3c10300d000171402d6162182142c0d0009816100a66980f15181c400c81c2c2c010404240000300110001e0009244152015400da840700c100081d92a10003990b4000c0d0380382e03c9100300003004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 646401771 1250 646400521 646400563
    0x151501080f0703090212060907090b0607020904140304031b0905090d08070e0409030e041a060f0c0114092a0a1403010b03010507180504050103080306091506030a02040e0603 76
    0x21841c48003001e58215205040110302c4c07a44c1603002500c41002602c50228903408201040f00c1000100240c0008101c200c00800c041c424580100d07005102d0000040d00458841010508011610700c200003e19406010740b0344071030716450b00b030000300302082d82600041211b00000c40e03000302d80d00c245401904440002c106c81701007508203407007900c0000d02e0300d01400003a0144184584a81c042c0c0031882c0c0c400d03500d503030603803000303408000c21148001c3d510182d0b41204030000341c1c0390702d42070100c5800c544003100c941c0c1c842500f0001d0f0340c05002c44140c540d14004c00401840428240041c0080f40c2c2a13540501880300c0545c403107161000040308850582c080c072003031810002600c2564520300e4141024001244210207400030900f96207090391010b002450031140405042001d074010f2010305002c03182440f15500d9520340c3c1d041800080d0000d489500ba0304085400104c194000d0075401c1d0020b0301c1d59403a0320700251500c1c000c0d0802d201e5a619419a030001411525000c074402051003000604411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 646402877 1106 646401771 646401781
    0x504060210201305030708030301050112151206020d0e0601060e0303091008060a08010c17010e0906161b0f02030d0c1505040312090515150108 63
    0xc0c900d4641601060040d01020340d030300090051191450322500601e0410a43e20300b01e9001c03640c18410101300040c81500070020714100c6009883e00c04400c00402209400d66490a03013040d800d408005c414050005025202480d160203100014200310300035003500c003126480d0940c4c0300e003640040010000164000b4403d0200c86051703001d9420b20f4007490119941c1e81001c14034005020505000507441e440d8028080c00030310450009000a0122041c003800c0c8101e05141c42d0090b0184100102d0000f84100c0018003400070900200495640da80320b078080701c03564410301e01c20030401250300b0704946441c548040a960140c0181d2961050f1881014601102e8407c01d00c10b000300503c0c00000b0640314490a003940e0808000811140d44901d4120f4002610742c56560000e86042c0c42002402000a014440c985290054518940f00d5140c4c020a89000500c03050000ea51180010 = true := by decide +kernel

theorem cover : BRFrame.Cov 646223021 646402877 := by
  have h0 := BRFrame.cov_init 646223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 646223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 646223021 ≤ n) (h2 : n < 646402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
