-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4416
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:33:13.881358+00:00
-- url     : https://prove2.me/submissions/d07bdd12-4400-4c45-9b5b-51aba5cc4bf1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 794064748 ≤ n < 794244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 794065998 1250 794064748 794064751
    0x915070f0c110105040b070c0e10080a03030f0f05070302030a15060c020603040f0519110915010c0c1703120f010e061e0a03060e06570901020d0c030206 67
    0x200603004002900b0602d80c05007054030018a201801a5512035082c0f4240500041070701c2420f41c8004000b011402495095a044060380ca0a00081a074207040351000c60213840505004510103aa80c030b0b49007414030041c01410b20561054502503524282000c1c0c11040f00c0c0d4260004510852060060203a2030f4000c0210214540489049442c0c1d2201e0400d08403100c842500209030340b145c03c60100400311191052018a4000c90080c04081140343c2485500301c4201c03003030404481d100559402030f40c0118070300d00c0442d02550180403250388400401c08900c41480b00034405a01c041421581000d008841a910102001101307045502d410300303031168450f007e8541403040f00c11104410816244d0001d4508100c0c0c010118004a40c2c0c1c0e040180c010015100b444089000d110006660500100310313a4000f20350311503040740055500540980441c1d144034845941c5486940c10103c121980c0c07142d8820f0500c1562085d98801d4800006458404040d03000d20a2000007441c01020a40214403a07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 794067248 1250 794065998 794066003
    0xf01050409080c030c0706081015050c010212010b130b09090a0902010c170a0305010608090606040b01030618020d14011d0601030605030f0f0f03090303180103020f030915070f0c 78
    0x1c01d40c04214540060180601c5050700002d120100310262000c00c0002c140d01180c0207510742c18840c3d2200400301c518114107010350450804451411040c5c01e02c120000c2100c40c400030001424440d20072010f84d078881003a130210b5400d130303008201c0a040901d4000360100038194040d456291418034000300b1421407004114038106030303542040106690207283c0c8100c041d58007513000841c205c440603030000150060141600003e160100200c2c02c94003524405005030000030081406544003401c002c050f0540c506120b04040c6c541d100003d91074032001c09170380c07028100c2c0c2002d03885407802d100d150304a8507280e0780030441c44004c000401044141c071140502c800d5650070301e07950035500ca4005a01600440c0d0103550903104103030380c000000e400440c3c564029800030050356007041488443c10380e80d0044045581d8150410003110928a18030074003e281b00c0710604001d0b041030240520541150411240185990403a264007030280c07401caa42154408000d080031040e60a060a005104040c2a01300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 794068498 1250 794067248 794067251
    0x1211040501091e0b0f070302010c051206130204092a080105010c06050417070503090f1212030a14041b0603020a080f06031c020309030c0a081213121103150f010504 72
    0xf103207110183c04804074080e14803840400d58500d4448140e2085910016007640103500e4515058501485002110014940002881c00a440380001c0003182448441d80c1811242d08001c0050240030b40c4c021003c100440c456101985410580d00c040c11000ca04440f4003000b5420700180620780e0003038a4141c000c1d811920004071030f80d070f616140058141413050420080004502c0d502003241c0000100701030b00d0140ca540d80280c8c200382c1440040d0558505074440d07904541201c8424030a91405076600031040100851520826042d400115109503810303190100004641000c4400e9102030303400a1030986811803810081c500018078000c03014084c14000d6000101046449c1e81c01c00c000e560740e01c03403413460070707001c1400d420040c0d92503000c055018020702845055500718641489890308840701e12010b006a07800707003254145240d100002d0919601150503020505110010001c40842e104419032020488800c00301403600004001080c0b2220303002c41004050040c07001810b046410a450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 794069748 1250 794068498 794068529
    0x1821090e0408090303030f0103200906011214130c271d06010f0801060819080a020a12050a0306090216060b0a1809031b08070f080c010507121104050109 67
    0x8001919110b4030050f40ea06100100501000400348409141264864000007217640c0304030442d80e00d42401408a139502c51244800100554011030382c0c40040c148000c000a04501c0414041a03030301d000341d036800b0010b54050501010800f0181281c0060074004480c1c64084d03051000361011601107a5501894545230040880303075180d02c0000100520b401d03419940c0968480341045d141d0f8526108101403582407840006a500300820003400d9554007002601e0703c41940d44442c84958000c00840c021441030300d4050000c83c41800140f00901038540e601a5100c60300c00c0c2c002c0540f5082d400400c90644104100c1182108080310308804036807110740811205009400100c2e0315541c1c3d4415a1080e4a2554201c49008564030213030f03502d4800e0702ea000e106640031030501044a00c1080c001e01c07030704040080c034001c2030940524940481c03182c800c3da40351420541020703080d564141c41c2e420101b080c1c980700140e074603814010401600c220b80c588909003894000001d041d070b600d920409012070f14409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 794070998 1250 794069748 794069753
    0x10e0621030307030b0109050a080303063c0306060117041202011d0a060e0631170d05090f0d030e07080d0f020c0607020604050405060111011821090e04 67
    0x312040103000c1402078a0b242d10300724102401a2444600403400590680408940f52070603001c2d400549401400850131580c418080c0b080b116a5007000c518044942e041c40d00c450084141d0000554400046014440c046181070510b0040e003d0400c6041c8a080d805280440040c019520f0740250000f00104845c0f03400602a40101007148814016a120128800c0751410014030703504444e1245100700440c0481c0010540c80e554241d4040512030218129020490032600e03020b560f500d0000a51003200e001944c0d01d1440301e480c141f0302001c3c440045a160050303d054072400b507000402e240504004c101c1e0b0665280c8a441c1ca020290605030381f03620213450148200070400c054009802121129030b0355031000b80c11501024840c40051051203001c41e154144601621905a40641503508140c1400b08210207000024081410004002c0800414801c24006d81c124140c00045070710490300641001407039140340342600711400f1140b102c0c041c02103520226210841e540125080001d84592 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 794072248 1250 794070998 794071039
    0xf0a050703110a0b152107030227040305070503090a090f15060e040c02160602012a14090f130203060a061110090f1403040905070c050703020121092603010e06 70
    0x242501124a64150106c0c150030000103440050700d000316450b40a80e80207882525a907010803105a492903111004a00080e01850203403400d2440f850507030b4100200c080220311401c1d40395100300d44040d200c800600b6a549244680d4240e00c011407209041d0900303040014008500c03894a060045a440242e00c14031482481250840d042002e4140000b540d02c0740024013030140100da21107080d8070314000e45d20000284d5001062034107a900d40108401d44c90281401540040c11050780007070b001202044c050303030f500b001045d0596510000507140c0c141403003031003c05401d541104081c00700740040c00144a400080c0d020894030302000114240e0f00514041c407036204404001071043c0c0a401d441e41c41207c022000c0c02c25280d64001c100820b0380d0701392080342d8030f0792003030310181054120300000d1000d94492100b008041c010b001c109460340b00014a032100300c0d50f5503501641d925120011203403481000701c0b407014402d200031402508550402c40b107208100c001400e042d105484202c455000c60808 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 794073498 1250 794072248 794072269
    0x17070e0a0902040911042304080f2811160e090319080a0c080412030b04110a11010c110d030e0a0807050a030806090c09040b060f0a050703110a0b15 65
    0xa4030501c44e1050b0f92070910103140c2d10b05080340c45a401c089244442c11051000d180aa0620b00c58404081d02c80f501ca055056001c200c0d03108a2031010800d0070801c030b41e401c2030840710a00c18581c0e010342079001c101c0144004400c265400030b681103002036222804c115000402a100f6140c01100c0581b5208070480c80e5104080c452011803035800380001c41507405c40e45080c4108a02d20041c001d51b40c110108036080d181c00c85000b42250b840c083c110550900c280e0003a240102c01500010f02240c07811560b500c590466220070000482c0008101801748081c040c60000f0200c074100030800d00d01a602003a15084034079241001c040c0d540ba5a0100c4400401c40c244049420211041e0f8400e45410a40e8880c00348400c10340c0407601100c0401c4290400c6244144102030b00b40ca2681013043d41c20400c4090300310803480540c0310400307025045000e813146004001418030758882c150b8a038468a806005811803a41d800c3c513580102c04101c0108198054072a4003c013010603400a038540440001c006498 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 794074748 1250 794073498 794073503
    0x60a051303062a020606090f1b0c0a03033207090506130e25030b0105040306020c0105010e1501050f09041407120e07140f150c010207060617070e0a09 66
    0x3c01041c2d00300d4411100360408194001e5207106006102c0d500241d03074990066504542111040d0005603070f0545a04400c0e8006841d040070030716104011100c10f240c0d8100e14603000a07a0081c003001e10805405100c0c06c002e19000b0341000300048502c03103400321001540c2118a98405216000402580c8100c80000c09002c00410880c0c8489200100098002d81801000c022441c400d000c16065414244421190074140c40c0c041d04540d1342c14400c9015003950940c0c40e040c090207100100000d40702d80050401c100c5600000035003036242501d02030702c460001c5d00b41d00c0c0f850b1a030002c40346145d0707001c400c0322800403c0786030644c0d4810710380c130225004010b100d08010483c05885c0a01120035030000091080e400145414052000d00346031032034882080f4402e0004070444401000f0090a01c98108450004014070002000720b4480304401c0b1a4004107415007a6540050701c1c00800c4040d1007040e01400307001c1080700070181103007102e69403a0458007400c051030720351a000a004441c6500a0690550f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 794075998 1250 794074748 794074751
    0x80304031107170307020109060c0c2303011404050d0512041704180603170f09040f020c190b0717071d1216120804091104050d12020d050405060a05130306 68
    0x10007100c1a83e142d4111703a000320b0000c8d6481100040b42d030703c5101422181e030b411001340c0784502e00c5c01e00100c0c610075801140e0309403008079403042101c0340d4080c45000844120442e055100d841c00307241c101d04000981c079040e03040c041c00f800180c541d81c40b407034451a4003550148100e250021481105203e6002d241d00000d8040240846180704000c2ca401c1170044030310901c00580c0c09440b08000600c140a02c1388100e90300f550034428000e043c50247c0108541180103500185009803003410f190500504908203030700b18030104249020882004c0e111a4458407a2030f00c195015841b064540b5129005010b02c8204050113408440c000800c0001c0e13144004010041078402d05121002500d07400c800624115021702c070a400600c2c0c00110b140b50354000d40c401903a40c545802d205900c001084408a11041c1c041c0034000450143c0304e540e00c40c1074031809440440303016410b40c017000b0315144180c0c500c4070801c00203110400c05526000c00b80c90308031060b03040040d00e81c44540c100324080c283d02e920107800f05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 794077248 1250 794075998 794076029
    0xe030106170a05060708092e1113051c03030c170109140a0b0102031e19090305190201090b0702131a03070e0402010c35030601170103080304031107 65
    0x1907000801141c2d1500c500e00fa911300f9500c40c0000d443c03003602256200760a030400b4010400c00c40b040c030070004810f020080309000c0003010f40c602000303c540c4403070b0007120000002080071240c1c0034901c45000500044517040c00c00340000755110715014082000405041c1c903039000440d00c500880c0842038840c00c4442080707280d80d40e0f884c100040c2c030841c419146240c034100c000c141e1000050003044032001041c2c00847ca45183c2c5108120440081c082d00c04420900b403152024074610380220000844c1030342e483d80703135107801d50a0141c200002403101003408807161001c4e20040c1d03001018881294020504162500420300124514020b1505580701481c503040a01d12104410481c0840156041d400c0352394003600e90119420707020050703401038046480e9002e814009070080c80c1c80001414545480f010400381441d852000464038125220303501c0d4040704011195074080310394030001c03400d49004101c82d40345849044007032001510207410401c620b4580c1a00e0340b010087e1100911681182d200d08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 794078498 1250 794077248 794077289
    0x140c0309090f0615132d0305060609240f0d0b010305010615020714041505090403120e030405060711030f0a05030319110a0309050715030f060f03120e030106 69
    0x40482c1c8084c401e06180c581c501c20041d4041c240c803001030000007400071003800e10100381d0700c0d400c0b00543d14884c0d00d04110f01003640700c000c40305000114441c0300240554204202040364400e0010328140c1c0c000c0c00030f80c98041c0380540c560a40d80001d01a43d54007046049034011805032010034401400c041344c040000410004d05601070000c890100d0480203a410381160100d0b1281031621490705101d0114200721070501d880e40c0305203e1000340b6031a80846d1a0b03a200407980700e4908031415400b02e08140319900c008001400385d1514100b03e4005036261a05000006003607000d40c07440a0007031220100c80c54451b49003002079019a003c4d1908440e0300807460b01d0010394075071044130015081d100d0200c460307000109600a000a02003046000e50030140b9400d0200c0040c40b20400c2600c0b40c0c81001c0001480410702c800035000a0340550700071406400304801941652619031050035034051005003000422401d030310000c2c48022901d484000f0000800019000d40115045084000440e4800082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 794079748 1250 794078498 794078521
    0x503030402040b04020702181f080303060f04020c030a180302190602101b121113061404050904140a210806152b060602010b03150403140c030909 64
    0x300340d1084400744900b03106007090106a000301c44c070094003c02c4442800000c00082c000c0240d220984006c070000c400e91900380546440e6007944030b0906600000140043ca0a0034407607040040c01c19101507181440380340b8035030f039a442054900c00030480d11694071340d000140f49605a00846c3c006100000040401000d01c1003a913061180102500c40d03503900c00300440c0103005041416517000341c0041d034003800c2102a203d06c100300d80e49982403599800e152040c1075841004d0310442020022400c220350030114080c20444400034500010101070208010b00c0d41d501745141e40c0142c0c400744800c0c606d0402e003c0503141003108a402000b080f60044540042d68038010755900740d0061380d030703824810b0701c0d104103003c1e21404241062201c0314041141181000c0c07554100c00c0700d4201c0a01d80c25810151282d1201162400c1d040b0000503512088070b0409443c040110048224000b13030003802c142002e5030007070640707099800c0901900c6008100e03d0150242841a150983c001500705040c600c0e11500a48 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 794080998 1250 794079748 794079751
    0xc0a08150102340e090d0801030b0a1107120e10020106180902060409020301150905060903060106030b0a0816091d07050d06020403020d030c0b101419050a0e01060801050d02130f0b0d050303 83
    0x1d10a00c140d10f0686c0702107128060180c12a90071800444003a168421440042c0c4210b45c00b44801d0202004507000203076402c1c160b0303203030300b40b050b81e6143c3c05c1003005d03042042007142c2c40001c0085a050010038415600303100a41c100d001e9a001c40003c440c0c0b200c1c8042100790045902c480782e494804400025002035008800d50100981e695400e0741c40c0c0c407542044502e005400502e0340651054006000c080e01940c010340d80c00200a0541d00c440c2d98a1000d070745082e10303005e2040b86d50030481074200031502ca1030107207030020041d096451104038030001c07416a540c041e0380b09440c8640c00740051a420b008113541100c01854000d03007140c407881c0481c1000b03855048064421907244151200240d581e801c402e6a51098550380c00200422140010410490313450780d5450003280c00c02d10310005501c8d500ca4041800030044200b510b003043d0324103c40a41a0b0300e05a0010b8010001d1282090069413030034000e2140c109900000142410814451401440045100ca420940f00704403030051050000146 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 794082248 1250 794080998 794081011
    0x212070f09051b090906040b060705010608100203091222120c0602061b0904020409050702100605090c030115091a0414180402090702030d02030c0a08150102340e 71
    0x38041515029120381c4840b00c411071104003c1d40602003403d6a00e00703c1074280d0021001480880c480c4141e100007103d65000402c2202e150b0b54031350007006844410b00c141412030610940440c10340c901810003d4440e01c8045000700f84020000c1c034840009502c400104080c000342c1806401d01d5141c000340300c03101c0050710046c0c0307688400d0000000c1141c8002034885c401c40100744c2c4030303c0e00c1203151350400068010040c03065000d5000e008c00b09150085204991088500b503001b001800940d0404400f100c4140c3c00003070040c0740450400c18a000b181041b68111a80384d0885544000f10000c00ca4000d01245c10806004032124940b5998003424406001a41c02c100087e4a04252250400800401452a1624406509000030702600d840e038a40b941c00310a500549182030042110300040380e000b1603502545980108240c1074580c2d211016603840310104c80f117840c015105a0000c0d5403001c4032940560302d0706c074001080d2038492002c004c0c1c9280c041e01c0480041046c0d00c0b00c1c5480900c0c0c0084828 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 794083498 1250 794082248 794082251
    0x6120e0a0f030806101d03010e010e15010b0a0c020112150e1008012f0c060403030609050a0924060509090307303b010206130515040212070f09 63
    0x120340145000c50305003039104040d81306d00c490240a80c8006800780a580b0707070325625560310060410030b21028054800001c61007000b0304908408120540041107040c2c001086018085c002100d810b034109105510194090078100c00c0001d07419444000b9042212810b600d00b07080000c00100241c072560524010056201c152200b42e0b19044150300b03d4403806c803081e1311a07408410300300c880c86600110841c101c501c0c04a007480c0c04a429103c920301401500d0480000e0781c2c47d0410005410039100d2150000150003043c4210110b039169a0100d08101e8440120152580c41c11a00301c1c8051380128024000a4403605441c9400005240c4079004000150791020280a8842c945400310700106154101d01301c4600340700c10100e50440d801104540109c010303032445404007262a94400707030341c130708110741c41490310710404250002403d0550107030044000c240c05501040019001041c14200c40202a10601d580d944500009050109a03e500102ea02803400041260440381c0d0202080e00c036040300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 794084748 1250 794083498 794083501
    0x90806040809130f0b271503030f0c06070212070201050a0e040605030a0516120b010b07060b060705030a1806091415190906020d05030a0e0a0c12030806040501050a06120e0a0f0308 79
    0x900400c1203180f84025442001c401c0001f82139400f0244594500c0c00300a0110713400d286054990750403d038000c052001c5039030300c842d0400c800320b42e0401c101c001054401d040c960410a880d400a8124059144c1000c2408010b00701e4141c82d4489902030801420700608458446030b65050081d26a0302c0d0b400d0700c20902c100c0c0c40c008a2805030544403103150550040031511940e2030044401e080780c0041d40c08480309912626040800d84d14500034055943c041c40186a55019004010b4a400041224148042c1e000c1d1010050b50340c00100e4101200c00c10340d4052550120180010380e6050301010b495018003002c00d900400742019070329541c510140b40c540324109038407140c00b6a900c44d4084032a0780020820400210301d840e85400445105140108031007199000d661049205440ca4114600c10b84205100790181a8095421500300703009403400c014a50400d000b04030442400e004043c14004014000d07504450b41e03900c0400381a0920003038540345030070351402e48800d18100d001600002c12600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 794085998 1250 794084748 794084779
    0x6150f0c3c01060602060708040c0e0c2a030a0e12010c030e150606161e08131e140a0308030903030709090c0e0405070c05031216090806040809130f0b 66
    0x114643c04c0d6821600200101e6a030020110380032100100201c0b01c0c04a600b4000500d040d000c0640c502842502030543d03224030740c400c01c401e00382003110395001d00403030f44100a030340000003c0101c07400c2e00014034003001c0c0d15200a01003002c03280c0314050600385600c4c107224260000d03030590069650704181010f442d03c0b50464599495400000d85002d540010200300002c040150070114496981c0314851b0302c0403d05404682c1c007003c007000b4800fa03a0b0004009510410f240c406a0341f00050a1601c1c00c00035800e0010449003428600e5000342d100712001e0803205907143d52a608040c1c005c41d84640469074a02d0107a6005849030419591000811000341c000704000c1204c0c0111001c030881c664403170a000c500c24040102038032000c0c250fa020b02c2402c2c2200d4001c07801c1880108201350042c0138090140c201101ca40c103100a68854a02c100001a1002d0000100104d0440e803c5a04400c9440d100c0b511319001840440000441588451600140c3d0403101820307048151444d000b16600c80403200c122 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 794087248 1250 794085998 794086001
    0x18110a081e1c02100915050708040b011e051005090d0602040302030114040803060f04061703031f0b0d15051e01020c0105040807030803130212070e06150f0c3c01 71
    0x810b2081d02680003803102015045065000550960041511a030f03107031748000466007201da043e42c09030b001843c801c040100f4488150186401441c0d1080708804183c10109510900f40490249510680c0d0b034098200613580304006940c1c407424010120003010001d441c00f58001c0d40584406c034065402c0145060f00034400901c0d86102d140c0281d0041e1445d0303154402c12000c002e9915401d54041c0d0382e01c402240c60b50000340c9080943d014003000307540e281020407891600d07145001186003c075800c1e100a10103003d501054a5400a4042000ca0945030301c0500c003980c04a5a04100c0d001700320464461801101c000c0407c5042c5001c0c1c0aa40c4c1d2202148011211485507000d956090b07802440200001544003000710762244044082c2c4070030010540c009201d600321110101119400340105001141c05100c101c1d8212000700d03030707100c0c803c800911452a1402001001c244040000c104091981020301c03001c1e40803421540110703101c1c4501645080151201d0f581d5142e101113040752101c285005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 794088498 1250 794087248 794087293
    0x6020106080102120c0705070b03010b18040902032508150403030e06010305030a0f1b0c0302090c0c06011703070c08011d07051807140d1a0418110a081e 67
    0x2c400850200e179a42d00c4405102d40c0c02100101e0f600c2c0700d90749000550303804105c081c42c0a48283d0761401e580e142660b03044602c55085c01c549038810340c030b07202074540180d500003601c0b084d651a0071009049021f9403080300c00403101c46e910124450003842005100a000c0091142c4114030070748013081001f10709d046040c1d03242c0d424000140994000c1094840c081d001e045040c800d03040d903180c4a40c0c10154032600c4d40d03007224021030448128504043c1403007103240110301c20394451b003010081401e00c032000320250354441d0180b10320420018400c4118001150600442c0e19552b00202068005551054898004c01d151803c81d00c4010824485c81e4441e003010503154200c0381c00800c07a080d0009403050940c0d00348000350440f400d000a1210001c0d94141000261001440002d0300144d100d200d0102c104001c0d440e588140c0c0314518010a010312000d46440c004501508034410001001c1c5074808600c22a046d40c10011440c4100c01040108544104203000e04101c0ca500351403032201001c044512a608 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 794089748 1250 794088498 794088517
    0xc1e020a0b10080106080c01091a030109023103110d030522030c0b0a02060a020708191206031b0501032715061202041104060207061d031606020106080102 68
    0x200d40e44200100710152101c81d00028000d0490650701e81d141252802c6071142d83c050151600242e039141d241d0360300029000014104007540058460255200c80c8051205002c0d4030103403503020813021001440c00100e5180e681800c2006100c090300b030138040740b601c08203100840b8511b21060510480d420310341d51000c68541d03d6140c00341800c46141440d00c4e15103001c004044c00c1c5440900001c0820500418000281007040e0394642c0c52102420007030504c4802004444041d004200c032000156030078040350901c0190050061000d80d440c042240e5000700c841d03200c2d0b40786090040105c10f000d40f44a00100d04130300002001000ea40d500015401d45000151440d001c00d240742d04000200d1407103d181d00c40612880b601c11001d4030315164042240c50b1500612002408104003404500307049c41141c00d4200d0240c80b10741480e2070114000d544911502035042000518400050141003a030201c00d411807004050712030b0320725001e2402c12500c04070f105150041d824a8400030b070443c018401c40c0c95188 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 794090998 1250 794089748 794089753
    0x90f0f0105011d3703030e06030411010e03101a01020705030a02030d0f0203130905070216030b1902130308071e21120510090b03010b1c0c0b04090c1e02 67
    0x540c440d0401070701010794004400d0014440d42c02d01c22a0381a5240880c042554000d04d044141c00c500380280401c3d051348600d806800104107110108284018203078030003074246402c02501c030411000c42d007408040f01503040010f00382000591070380843e0988142e1303400700780e080b1954156a41d04042d60f6150f40800690540c02003045c000d51548941c2c03141041000600450740790010340000c1d00e0345480550301880195580e00c1c1030286095061248600e03840d5140110417125045490f9000300c244060480118100080500c2b45070391611340640d40400e185420f0200e016540c3d04100c0c0150340415030807a070181c03886040452001e14403608a00050700281c40a000d0b900403d4607200f907645158104040c0034a118080b1a0340c6198003c0d80c0c402d05128850105083c80c008000c0c1c01c0e10880b0b2480f51090341055041840c0b42c803400350500c0d031500c2030591208880041d00b80160700c0c142c590440c445500d00024041901030a9802607950040166100303440d0309140c401c2d840100303005100300d0300140c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 794092248 1250 794090998 794091047
    0x28060e030f01111e0c060c040510021f180206130501030c1d041a210f01090b1501050405090906011a0c2d0a0302100f0507020604120c02090f0f010501 66
    0x102c1380c0c0c10108502c020044075140c01d804841807850032004940030440c020780080c083c04242400b50088400800600081010072840c0c984440c402d40303050340c1c02c4095039460559102c01c0a00006905007541c0240159a60b819080441d60004c8101e01985001c41d04202c0e0108003240704060040c00007229000d81900440200d04003c09800c0350b0324100070302e0024010800b16503668410503c000c403144030800700c140010b84403c5044c030b040008021190b914200c0c000d400f0803103444020394440e00704240506440d81080c0140c4007070203190020b0b600640a0010007180380c0e000141d03107040e035041d11440d1b88007440011507090240700304c12074082c1542040c1c100c0003200181c03c1d109044000d115400509140442c91480d02d00507103400c00340e0041c1c3c080004803072443d00620541c00d000d0181c400c1442145041040a941c0380d001410050448a02080c0c50707054611501403040c01660081100c0c80ea400c0403966415046820f072407138007551020350b00008056000c4c11070440c48001400022004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 794093498 1250 794092248 794092267
    0x302190b04170405011413090203090604050c010f0504050f03030c060108150109060b0d02070f080d02180a0501080f0a060e0a050106030c03050105151806031303021903050928060e030f0111 83
    0xd500403000303200c41503010300008501c41008d0b0001c1d511508170075008050518250600c90318017105c4107842414800540c4808811942c841d0450301a18421f613042a0101200360100345140329400c1c043d5424041c1c0000414001c90126200c1a1500c0261840c0681c0c4d80b220f07180300880d900d900c070b0400307a00e208200050307a409042c0c0140c00c47d18015007424074001001e44884d50790b6031042041e401240c0d0b002030040301d915100701d0100020300c010f5869402c29420320340080d200c00800742502e081e9031082c0300007507180340d160341010000c0c0103ca00c2c41d80140c00d115000740040c000038020080400c1c1000203c0e65514864442e05040300c1d00206000c3c0342d40c408218842c02a44900d01d0025000c0c607641ea50103081c1c03a80381c000e5024040d1000211100481424000e06108602100892525440d000800031a5012094901486003140d0b050443e2000d24209a4011002e02d520444c249401a00140540d048610504107c0702175043d90b4000d1810002142210309007a8001100f501c00d001d0040f0307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 794094748 1250 794093498 794093537
    0x20117060307031205091008091905030a052b0b0f030604030e0105092110060e090a020103050a0b1806190506180d1505010329130302190b0417040501 66
    0x1000ca4513405c0c058a40b04081c03001c9020412001c91140c0420131901c248180450208500b20311102880850851848142da5480c2c492044081031400c001c80440c2c0a1360b004541e001050342110820109000300381c00d00c8408024007240a04236114118200c030040035410040381062207164076a540344c03444281d11005603140d0700b180503402d03002020340d03100245d0054401038040711142c0b904010044030803041c040c401500c201d1741021a0480184040c003030b00c03580000301300701c0300c0d40d090070041143d42d601c0c80c00400400f03c550142c2d9005c0044604188040e062444281c00751900f5138034145a0044503042a604007001d02c03c07240c11807410490301091a1f24076541030700c40440282281100d4000d600c80900041d00030000d0301c01c090740c0c0d40c010000c0080043c0b00419402e0035810300c0d10f11100604032404c070281c1c0200340300c50560004941400300340c0f0038403a9014081d44040c4509583d005030401c00701440d000c40d011107502e0f19844186c281280311009980031214140e40c0da8904000c507408860 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 794095998 1250 794094748 794094773
    0x5060a090b01051911070f180209030319031b0e01080f06010c02010e040905010203010b03150405130212100c020a03080603121902010f0507030b0108070305011a070503160c0302011706030703 84
    0x30001c1c5c4240c1e40c0103094043c07040e07000406a80d02c40d40076083c140010f5402d25400f151103015011f20400c0240320a45010040d6104d201c04d2500d428118040f840c01900501580184001041030300d60030300320034903041982c0d000070034000c3e81c40d440c09503100f800500f42080161091804103c01c06034040c01580700b03886068100601030004036039204c2c19600c250036a04280c1000c43c0c03980010040000c0c94035003131050b0b1460141103605101314204281147d0180c842110068000d5160700031405a40908000d904e100b505141e10070402c0d00c00c1d22400944a00c400b0744210005482180851294070303002400c6920141440070040c5002220303004801903004a08100c0c065540b188031050030002e5900c94a0321540d03450320040342c04030102000410b5488010300342003d041c9040018840ca500c130841e2642448014190035554013401e062030351440c000e00c141c0500000c0b110b18441e0030809030242c0181100e00c00e13280c4a48106840c0d00103502400201c842e00d4140c1e10243c6c041010510034040c15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 794097248 1250 794095998 794096047
    0x15030a150f05040b0a020a020a05010c080117070f051302190e04180b060f12060103033614030a0203010203010306141003030e0f12061f0902070201140306012105060a090b0105 77
    0x1d40c1c275075055983da2800c2d80c90080c941e101142c008070041240c1c1c0484101c14400700e45d00c402606000381481781c2e43c8a81c1c40c4a000c0c02d8000c0200d1001d0000c010480c0d41120700150b05e05901f81c2603031150a0008010ba1482c90801d40581d0400900c802c00d21855004055010ba00803c2080355a85000a00c100d075071946401503840400003440300c042640600003940614003d507100380d40100e6a02e1405907008002c004c02500b041c0071001102c864400040140c292603100048035960701000e0002403a26000e121b0180d8594030000000007006855800903500102c3c001d450b00f85555001204480c4030514400031300805e6200c80c2810f80751030003180000c0c021b00b008049260b0004510502072038a04203c508090f252060305540c012400d07501000b0009050011065190010680c0000e04036060684c1c941c07010503000c00030803802d0780030b00c1d134965010729800803d8075011800000c8001a1900f951624091142c05030003050f006003a000d0380d0000c3c0d606071034a074034000300f152201e80304992100c43d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 794098498 1250 794097248 794097253
    0xb18060604180209031c08040f140d030b0f01050306060f0d06030f03030f0b1203040b031b0304050a0c080a0209180c1c29010e15030a150f05040b0a020a02 68
    0x11a0368a100856400560600d00e030050304c6140e000305152500400c03508054100c0caa24200b0f0700e03620360091190340e1003603015240e4260b41c2c10074545422a00c100e00c40c010070502884400d440801d500d1360094055000440301c0c18484991000150f82c18030040d00e1054100204106035980700312410010000b81160a10025034544c1e280c903080600c41102000b00e0010b900c0c1c104104441d01030340144554103e040300d214103004c0c0c880d040304e983c9200e10f02c100b4407041c602100050705151096448405079140201d1203079640b0b841d280c210380b100540b0340c040b00c640100348070201e0403150000e0344801003940640014001c0d200e0071000c1400040f010506a05441110164152a1a08440103010300c0b10444c1050a410781460400c00000c1d04403950034240c122070003c00d486110046120781103a07500c081c0b00301c03240c4482c00c0d034050340340c1c01101035a05031040c08401410014080802070103100f00070401c005e07080c01c200400f01034800c02d60700a000303841450040f80040403982c0c024400360300785004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 794099748 1250 794098498 794098507
    0xc040516021207170c070e01150e03061012081314030f0c1011030d151d0f0f04020114160c090e0703080a0207030c08033a050402010c1505010501020c03010b180606 72
    0xc0c000b2407100243c024602008803003240304860303608403072b00c1d08404100f00e0203040d0700d1a00300101b08a0201034441c0c00e400141443c2d01000740b01700d40044900c4074207103002d006d03402500d460302101e00030301e900d042c07900920030003510b503644400100329001d0043c0010041040c2142000381201c082000c0c814110040c0001c025000c890700403440740b1001c00009881b000c200900d0018101120346a04000100c01d0b0118410888182000301000307a001c20008110442900c807400102c403004240c0304400c11103080000d940b00303440f01c0c201c491801c8500c03414107480340e15110003180040d210000c9d242d200319400b810040c00060302d03107005000c901d8928030464130a1960b0f40c0f981700141c40103510160694000241d02c400c40401440211040001080703105140c0b101641c00107000c807011099007a94507941c1003c1400c680c801c200c0b00c90419002042c490700115983c0214009001c00c4c0700f0703240944204402640141010b014002000b40d0040c0700401c00c291850f29240132030402811144e10180400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 794100998 1250 794099748 794099759
    0x1c2001030e0d02010b01110102120c03150a090e2127130609110906041e0b07030e011106100b03060d080a020619150303110c040516021207170c07 64
    0xb0450462000039400070460090a03000503150407a03580000540c0c0e4010040d54100e02c20040d14150070100c1c0d1800301d6543d07500e1034008420740901e602825440700d1444000078140c9141c1d000f0681c1417281101340c1340c1c41c00d0f200d1010314480311100d030000001101400303012804000d89024141d080449040000c00005e8080090300324028a2344009905558038420b00051700c82e4440d1400c11746c05c1da580c0e01d18003200d2000169450290303100d24924800e250b050310301107076040d4180d030000384403030324403d900e030340892801521104190004500050b010342800c0728000001034900e00540440e0b110381141401d1006000ca113920060540b030300b0903e00207400e80003860328070003400419000c0d13018094604181d00c0240c55041c100c441488500d0810480010b4004001c214408807a49400d005d41c0618003004003074240b12120f0b40f5154424a000204884500921211403072241554240c902d1005a01c280043c90f003d0342d20054144400d25241c0e85a008510740244010b2400c6412a64503aa840 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 794102248 1250 794100998 794101003
    0x40e0402102f060f1003150e010204030c05040b040b06161703100602060c0c03250606170d05160b180d09050901060f0804060c110610051c2001030e 65
    0x845000e812105400400c0e0207800300344072940d000380703e106070358407a414640c000d2800c0440c00c6c0400303442c180c140c4000c51403200180d440895494070400080d13440701da884c100300207064910705c60b480c0a98184512039a407840c06204400301c8400c0201001c0c05c04400203a041100c402e00d03030b001c88909d00340c01119120302d030141001d10f00c180c280451100005042c280000c0c1080005084441507035014401040141c00c044140c0f1044020710346d0604020084011840c0c040e0a81e5402800f0301c0d1411101050007076064141c0b084440c546400c4546480c5a88002c8072103105003140c41814114803200403001844481d00039400c0048912140501c44500d083c40303080c003d404400c0c10100c0d81c5007200b0002401c00340c03800c80c0140007a0600401c1a0b903011000741003c0740040c001809280e8501c2d082020501031f581d41c1e5182140d14013118218a02002c40c440340d44418081c0c28440d074205404040000000b1481820300e076402540a405452107141080c501c0e000d0301d0002d03041c10389401c500c81610508 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 794103498 1250 794102248 794102297
    0xa0306020c190b060109292b1410060c0b0c070803070e190303080a0e010e0703080d050f040f0b0405010b0402030a090b2a0f07140703140102040e040210 67
    0x6400c4003503541482000034041c0c1c0e61680c00719547d4a991280e02810382d0201c00e1061040401c003d40c070380c0d50240c2a00d00658166940c801f03250621038a001241024110343c0600601084209101895203501c00100500c20080c031524000503841004100014403805110341c008960700401130400c0070603541d44c41c941c0c10403502e2400058000818103a146004000804201c0e051801c4035140741c02c50320001d00506c001405683c5540d02c441c08162040801d50060a0a101c02002d959200d0340700d142182c0f803a0301c80a400c2d00310038202000b0502c00100c450505000e0b6a000c0208109070416507940d0900300720081058031603540c1d03044490040d0b06e071781c0004d52080c0051039000902803128030788654040700141200c201c556406001d4124070340c4014202c6030801da154502500c55411a040110501c50000010045205110018030700100002c1100590b4030840e6070117102640080d100b401c074042d52143d81d95135042180071070058140101c540841e40007510300703086060b55066900104202 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 794104748 1250 794103498 794103503
    0x20d020303090d080711150d020711190e0604060b1608040e04121b0b0601180512060612160635070e03010b09010b090303040305060708040c0909020a0306020c19 71
    0x20002400c80401114807602c13010104112118542e02060f04114200c7d4014101d1443c802540001c1c00e03c03d02201c1c04010300404001455111540080b03158100171442c6841414030383c1c0c4460005c600741c1c0c58203000d484107582070104c0c100e0910910002c52900d280d4004030a84200a00300008164044450303a200d11a42c000c1090405400c00340c0c0005080300145100921124070156160b0002608058000d4000c2801d280c102c0c0c04038842813401c0d0304498241e118542c003070301800c2162620f80d008910144620012941e480da481d4100d46410348560b4001090040001410300c14048a80285c0ba100840f039100710b00801058414540080f40d68525240540140185010800c41580c0001c6d036050201c029402484120389107404248080410302548a003072101154000040e01e04105030350081d60050202c0300c440c1424800a4040c0c202901c050702d001010700d0020501e80c0b580e003c4c2c1c1d600b455001e40300c0c0710708924540700c0310025000313075030509068051044500c90b000205110500000e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 794105998 1250 794104748 794104763
    0x50a050d0204060f26190e0105040b090105130c06140702100c02030d0e06030115020a0803100f0b1213050f0304030804050a0f060909020901051303050c0103050f0112020d020303090d 80
    0x200d50704400360903000079690310003507213140406585c119042d030a0b84940103118100440c210b41d500c18581d8020301002c003541c01e80d43d86044100414032060300d10300c038024142c890003049a601c903880400072501c0d040002805d6883c1d280403c00800c2c1c428401c080744140d00c0340a16040001d550300007444d210405c5510000142c3e001d41e44000d40c43c06108030101c41009041c81000d0000401c08210f403400144640113031080d030080d02c2e079010307802402700c0d101c03595200411176580d18254504001011181c020032849200719080414005100d000b1207412200c0c40d4104038841c0d8a0480924a0340f00c83c420413140c5008403107450b0a203030b00810242c00514880c0722403039210350403c01482a1f40007254400e0140c1400e5031010444183c109a640c020307900c43c20005681e032480d0304016aa5481640c000d8008121189030010900102042c1c0100c43c0209a0301070000b61900748062503449401e00030400c0c83c140300f02400c801450100d070901c440b14400740030359040c0f1581900250a03450000e1081d500300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 794107248 1250 794105998 794106017
    0xa0902060a0534030c0615030819080708041211060118050c040f0b030a020f1c0b01091a1c02030705031807080c01080402030a060e1609091101050a050d020406 70
    0x40100c2c02c0303114010b03442c0f2003040ca2144071400751000110300901805100400c04000c0911860360003007028441d181d43c903081a160789103082c103c1a404000200160004000e808410620807409240903030101d641d5481951240d03141d0105060003444403409000984028140462007809404e0003046c6044292111016445041e400d642006042c42069441000180884509a03d04009944015182c40c0d22035641615180007442811441244890b001c5512800720306d41d100c0500080d00b42d031505002003524500150782282d00fa010b00101820f04400c48400341b103001c006003103884000d22905880398818010301040340d10175501c95000800c004108070201c0400c090115004d2120002405c09501d0911a1500c405101b02d0719410010031002280566808000c902040c17500300c0c908120b0306aa040240c0c0d0b0300c241d64815022525028407002a03002e4551141c02500c44d04180041d0030110b4100c01118244c0c840c59080050100901400c091823070305102030400740c2801e031074034041d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 794108498 1250 794107248 794107267
    0x50d0b0105220f0e1003060e10020c0c0f061905090d15090302070f0b121503011401090b030a0c1a2505010f0c0c110a08010f050411090412080a0902060a05 68
    0x401d26421580103c440c403014415880180c0440c5d200b1260440c1c80040c1c4105000590380c1002540210890102e00100c0c03180410071011030303c1418110708840b105444003441e024840280a910806070300301e586905038558280c007a90007032070882c4004200e03d0244060740d80d4405003110281c43c0280181ea1844102d04050301003001c0409032903944e4010103090314080078000988103007a036500b02d08018401189003185901560004000010000c2c0000c20301c0100014100000344211198181000702c0c0c0803c82c2400b10f01400f020350403820502c2c09609000706265442d40050001f1840502045000d402500302d120002e10200c1c842d03455681d29040d81025800d407540742c009140302519001c1850603031904126125405940310fa0900404601803002035001210b90744030080303175400c103c40b403400c0c841540e008902c1a4850305181e2240d0704400d050040b2003100b02c4d03004060452651000e01d80d140681d81050380300f41601c1011424002a50101f1030a41180c041d080c00302d900414040e08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 794109748 1250 794108498 794108519
    0x6010e01171b030a02090106020f01061403070302040513080c0706030c05131e030602180103060f08190c120308060f030d1b1b1401080a0c050d0b010522 67
    0x10030754100c8003651200c6055501d61502d0340001c0360314600c1104090781405403014460002d10035002003200c2459030352404040d4581c0708203205c01301e05500c0d001c0d02050000c0c0103031500440000c0640200785003819507080c00001c0202410318823600e001121541c002a01c80002005000c0c41c93b0040d0441c54a400c0b00581550ba40221b014240071f01400205110132410740104200c0c1c621131408002800c5d2500a90500d105a4101410b02030001690003941d00181c0c9000308440360a90b010011199200548100440d45000d000f03966003114090881018242840300700c0b85010340320740408259543c4c0030700c210b04c03a900c0003200819040070400500e40f504510040d440e00f41500503000d000c803175410040608403682c00d1844607001d84001c140c24880051008511620071040d12804661184200003401c90911000c07400034415000046680703146000b4103e005d486915054201710b0f08400680150001d8880329041000c00e01600302c6851101c81c00040c0d2041030500c00d202c65080c65031620 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 794110998 1250 794109748 794109751
    0x8030d0b191d1b0306270906191b2f011508061302011206050a0803070b0c12010b0f0918061201020a021005070306050303040608070806100e220e06010e 67
    0x2c4805100501c040001119072040300d5102e00d08845650715016006c1c60008160300543d502c94030784200c0020464880000100f05d402000ba00c108650324000e50809803003a1580d00800d000c0149210094018450180c560b1b50303082504040100090300f031131004500b90304045080b51030341e0b81d1101e0840c42401102e10700b00024205450144c4150329007244511010309155000134100a00e2044081501c8969400341d40900300040000d01130f10783e2000c1d203994079080030b4070036114191000b0200b0200d0300d51400302c2c1c101d4856011801c0e01e90b031a004c141c41b01500500348a842444041040361120350382c2000c1034000c0e00f07808a118907182400821320449602100300c4054076881080074032103003500064007510240c40410003140540d83c050f0114043c2075140d2115800d8403000ca004119a90480394a610514413a40c85c881d880d0345180030802110006051000403494a0b00310035030301c1c142303071100141600304a00b0882075085060103c004880342e000070984e05400800050010a0540403600e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 794112248 1250 794110998 794111011
    0x504050a0207032c060c0102120c0c190602070b0f04050106050a06120b0619020a050d02070f2310020102090f0316170a0f0804080d0908030d0b191d 65
    0x110b080a440e6940540708691400303000d2090307960842200d5000d10006040080282e01405550710b07107802c0806a4040d40014818940d00510100040c0040034202c09983d420b02d0742d007000708401d00d2504c07087c0c4c12030f2a10250a0b00c03005d8082003a14042103800308024040d00720701c16203242600e0b05040107821181290003e40c40f44c090880104015a03010781211700002007000000b903072540140004034a403150b0f81c1c403420822001424039450780c0d008204154540e0240d002d65109035501d480403071300c803e0a4060f601407110703000d10600556007a14249182c0000000241c4001022500003a8540b01c800301d503400103039000500c201d0315041440704024002800d50090100e00e80c40c8001c074030310100a024880007044001503602e04007030b0401201c103440703411082001d8080e0003810b002d421640540601030305031203180843c030f580e2031084281000300e0f520303140954140300c900e6080c24058140c070600d030ba502016540010014410780d0000c4801032a455a0345800030403d030440c3c024a11004104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 794113498 1250 794112248 794112251
    0x5031b1227060613090209150108010f0e0403030209180906010f06091404090305040b070305041d16030213030804150f0207080d0f05070b04060b04180c0909050c1003060504050a 78
    0x301c002020000810079000340c03040700c1c00c9000b4111010600001d01c80b0a501070b512412080c00d004210400203104543e6034001e0340c0b1600da5a803103103960006010940b00c1c0030101134003500082c010074866806080c1418004083c070225038003803680c00100200a07501c0d55400d401c400010403580003c2200312000b44281d00305805114600a601c000d42c42803040513500403916603c0600405200d08116000303050b6034444581c85110301c0c00c00920a411074081c2c0800e01170040345c9440c00c2d45188401034070035039412140717075170740280010220040d400124140ca81000400c9002c400100780302c0251016148220243d050309000d89402008030740c4075040b01c0f06540058030180000e150214001090702810700b09260f11510400c0304031014464148041c000a181c9800d00c01007080981101002d20b40884062142c4a6058003507501580c6034000202110051b0b5030802628000f0340041e078410f4003450544010385154400f10714407100d402c4030200065940d00090220340713002c0c4100b070f0b008240c8100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 794114748 1250 794113498 794113561
    0x40911120f1b0d02060a17150307060c2402090604061707082505040b04090b0306070306050634030c06050702070501170a09240b0904080a05031b12 65
    0x120f00304400d81500603009807400500b4100b41d81c001c0311154068402401802e44c2460003280108084080381c204504c68042d040c2c001980c0303480f80100c00d21207500300c504808140c080c1c01c14011846692403900001c150240101185070380c40102810051455890b07e842074003890040303403940d0300020940024044c0765070503c000c0d0f40c0e0b00c50070002c041180e8400038601c0418860700b501e490180780e00442202c8000240130481606540080c09840c10540880b0300c652204402a41036900b03500607150000000e21248c1d04148201001e80721035804034603200b00c0d8031b40e40b655500d0303038401002050300032034410318131a410071070640b00d100e44c000d640e8400707092140d04000c0020701c8920706108a450b242d000c2008a40640300561125403001e41c000c0b40c9c030303220120350107542405000340c1c0710780c48840e1720b050a03034030301800e0050b94944100da01200305803401b1945030301520103420251101d40b041c40c11081060352a40d5460041c2444a80361410f080d81c0d26204541c400a4036690350003902c034480310382 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 794115998 1250 794114748 794114803
    0x20a080d0507030c0309050d080903010e0c100e0402091509032a0d061404051f050408071e0c08030403020913030c02040c0c02031f05060d080405040911120f 69
    0x259299103905282880003105541000c4807880b01b2504100c1e0b00c200c803c104102000344490040c00700c0d200940080c0305840e170158800e52610b00b42090a81c03c0030a894070a202d49100301c0fa074600381c0c00700500050814401d580400ea640c1d0b200f41840d20301c004002030080705840d040040c038010b14452120f0f0b50f90507000c5071121040f203000d480b5490080314801c14002c00c12103a03030000d180c03051041c080240d82d45440e080040d0f8031110615284a08c0c00308070320800110b009401120f115071b030404012071802c1d0300c5541c0e04040b4107521002d01402800b0380716107400507808048440041c030100d0001c507211411401048161300c006000c4050620003513404400107034206110103007140c1c0444000032481030804080e01d603034144081c0290701d40a400c00b030003245d16295180d003c1e4000040010055540c40b44140a03c400c010310313000d010f0510500c005c00031890b068020911061050f14003050200782c0c5808101d4200c140c481d690425003005200241a0b10100044102d9a1514619034803548001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 794117248 1250 794115998 794116007
    0x2010207290706060905090606010806010e0325080a11011e210b040f020301090b030c030604060b21060615030c0714421006051b100603020a080d 64
    0x1d08a00e07090a03008280300c010701c001030340800001c0440c00c0741407010380b0308000d0311070b120a4121900f41c0070482110103c1d1055200e110080045800900142a2100c0a5001600f4000781c2c1c01d908a0400507110f0201d108032041c050b4940851150040720b01021141002401d41822601c0742052400d4540c00400e1503a4008252302542d11003684510b400b0b0f0b4204074940c040c1030030000d803607001070401c09410f04811155008504a640c410010081c0e407601c40101a250300050700030f41e074076030301070404100030030807d510070607004800500d140a1014407210f0655400c2c441c11180c1020341011040044900305820786441d800c0099580d24a5481d20300d500e170003a03001c0c1d04000b0b00b800346c030034034003190403002000303903e07aa6402c0c15a1280c150441d17125100b0451095141a2552040c000f280542c42203400ea080f40141c041c0c1400305211410a0300403030398ce0f000503003400e2200e4007940065100d50000e00c1055001442c1c1003000c11110b0550050000d900155441034001c1c2d03100c0010501080e601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 794118498 1250 794117248 794117309
    0x7031205070e06091801260102040b0a27030317070309150e070e0924090a020103090201020309120303180312150109091a040b09070215070c060f050402010207 70
    0x3250803a456000d6800499075410074109008132030300201002050010002c0d070788102c24a6a000181221607d10369018242d00a5204000d02d10b03400340b04404441c1d00801c0720100e41690002200d284510780c45083c0c601c101203900590200b180c00900c010304c110b09074100ba600ca101e0f410b041c410043d0954422030f540710205100b524a42e500d18480322a082c0500c060801425045504641400c081c244c03c0d0f11600407050007a50a00a00341c0c140b98050001c4030184520082ea0140c1154002900150050702c5a00710407411400b00300b00e094086c2e038500440c440507081799002103031030707103030410000e01480a48400303000f00d540305100e07a0130000240010755912500b503a610745880000800183c451003080e8100c42586801e1510b180103070b64000607036040c452400c031001c1c0480e00d07040d0103002060b542a2050760068221540506d41244034142c107540100740342c980b40500050315200c09040328034012126041360b85907030910080d90b0341044100c01400d90b1620382c2a83c50658511201008107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 794119748 1250 794118498 794118527
    0x16030609300302031f1502010606021b0904080c06070f021b060f22030305070302070e01080d08060f030318090108060f01060f0320030f09030c0d05070f06110703120507 74
    0x100080007600003051451214080940005c01039040c0d0780307400d001000364411180120041d80781850014a89200107101081c580c044d03c10404076022403000d215004400034403d54400c00c04004810342510b0800c00765201d02c1295585280340c04801c0402070801c40c0000400c0701000c0707200401d480f81d90f0340c0405ca82000c04a242c0da1540d801c08035070002005038000240402c00c001445000082c1500040101503d0b8440e80c2601c44c920b84031100a1840c40083c0a2100d140c1c0c841418402424018603403550081d2b80180380b442a811140300080c0344d5481250b01651810640032162601c0c100004a18050300c03190001c1c100c01d1408005030201d03040140b1a8100700104084a80e030340c02e01961003141c014000302c25816015009080da400359a0060700d000040c00d6200c40014090180030080d910a12a12005010f140342d44840c212507980080c070040c2c176010303040c0420800213000392148100e4820074804103500e0302e0040c1800b5003000070106038441c0084c10705007001204c680c4500b03d4683d280 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 794120998 1250 794119748 794119751
    0x9060d0506040902030d0f09080303010f05040c14031303120504050607080c0913060e09070303050f0d1d240405061909060e0705040606110607030e160306093003 71
    0xda80500280150110f04070281d018007400e144603205991102084200030101d48070364a590350384e40030b104d9803444244901e008140b0300d550240554600364111030340503400780c81c0c020300c22031411380c41038202e030f0055681d88050540c4546034401c15801460b40702001007503150402642c07038151140c0b80c65090082000040111900010f05103d41c0042034480c0c00c00702a00d004045114402800000d0403c0e008602c89145850009410365500103144003e6031b80c16a00d480c14280507020028598102c00300ca081e9245d1610480e0140500034500712010b081c5000040c0000d80000c48183e000b00a0081c2c500800c454810800020400000d10307d5045100c1c628100840042c42540704000c050001000703001074241401e03680c580c1e40004d5500191281128108115981e48005481102190b24288510f030041800110300a000b03611401d00e488100741660203d0300010705410014800fa001100d8003a5104644003d01c4408802c01c005641c0c00c2400d51140012a2032102201030b07840030403030805 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 794122248 1250 794120998 794121001
    0x1110115140a08010c0518060901020d03020d091505040b060a1d0c0d05040309150c0c12050106030503040605041d0105130c020f011112160507030e0411070807020a080309060d05 78
    0x6803240503103000184a980001c008410007120010305a5002d940341c21f841e01c4c1405071103a85483d101c401c40c3c0035914143c000b8810403c0c40c40040d0069080010142c011a98801029000c150440c9491085140c200c500250916084c58012a59000942914000e449481080c098402000e910818a81203041080e00325547c081c400c1161703106141c510080203051000b4041010340041000c03084d100ca60300500050780c0c0ea400101d42030840c031000500020030b08041041500103d0040305d0340c25004030008200315880e41c4500d0703e15801a8003903000210009001c100400524054504496210b44400001e526140008003c04203d221148a0035601c02020901782d00810203110f4102c2000024810300300805402c09080c0c02982050b1722a0200f8000581c1c100e00c0c4003500240410140c48807810221162000c64600c8500640541c1040d682c444e00fa01088205001d004c02c0361094002075a07440340784c41440850300c819030101055a00074031190850b42c0d41c1100340c2e169403619540c0000c46 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 794123498 1250 794122248 794122289
    0xa051002040308040905042d051e07091104260d022e0e070603020703030f0c02071a0c100b2701050114070c08060708010e0705030402150d1a01110115 66
    0xc1c2c01d45161420551100c230010240410381c08102030441d60f00620a0340c00d00049000c28070192110701c0c1310b1042903042070000703000380140da601810108014100c42c5051a4072500442c00d8400c1120018080c14060051850f1480040082800f00c103418030241c16000076803030300d841c1cae40c0380e031840f80d031560044446d00c21502803002e42c0890400100f180442e10040d98450b40030b002540310400c1070700042e00700f4601d505945c455000e010541e10559001700341c1e1918080c001014034401404150302000300301703d0740f800d16000300600c1c9000200c50038002115044901000142805400b15110410040301d1505403484400d0390281160710a00b07000c0d10389000d82000e807100b8032406500400410450342c010400000001d00075125100c1c40e265030810342d0321101c0c1181488011031b691000141c0c100b001078010300b802e4030313040d800d41d522155003420020100110001c2d15040503010700c1c01e03d04550050780c03179031b40001422a99030845000700b0400344043c000e03000035442406200c000b000a03100c82d500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 794124748 1250 794123498 794123513
    0x2607020a0f030503060109090605060d0c1b030306050111010e070512010f0e0a020a0b0c1216050a0b06100e03060a0b01050405061204050c0f0303270d050a05100204030804090504 78
    0x1081c0d071001c0415403034112441d01070010b410a5546034002583c80314086000740483c070441d015030340024509402c116030040000c010f03101901542003005020368220303540d041b14003030301240d642c4603440120b142800d21000412600f5950341c504056030411516490304030020410f8425240300ba07445004202c040050640508454000b02680030301c1c101000554810202b80e510481e0b100311407001e00706980702c08006060241701581c2d00c10340c2142d0500c4c085490300c0d40041c810150041600c20662210340c0304e5609146034040c003551012000c804100d4036140900d40300c1104140790400c4004201003030301096461138024281c078150b59507556408020382c082c10540b4001c040007000310b40ea072440c112410b00381110558046806210308004c01d84103280025003803e0070305000c6d0045052610702440c80e03094080c0c0c003ca292041e01e041d4003610300c41d2518002419102d00407401070100c89140e00c2d00760b2800c0c250b04041c03480640b040c881400020391400485080f100c0059012039141c559041204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 794125998 1250 794124748 794124763
    0x10050d0b010212270307030b150f0a06020109030f05160201230429180603061f03090c09110306090a020c030301121a01051c0302011e0209030706260702 67
    0x140031a001040c925013680d100720110050703015010074000c845040e1004d0640e201482d01004100d140340e140081d0651003048140c4070b81c0e0b1402031540c40101c030140c02040000101d07801460050f51100010000d00d904921500d940c1400f45c80c01c0c6241c2500080c034a40c5c44103d043c402810004100c00c001c101110401d40703034480340002000603540726620089045c442502480c2c00750404641100c0e0210807032600b050b91940c000414181004042000800116030300007000f050340304800e0181a40c0010380720172861300031307241c548001031410010705203000103998560142d800c0341d080c1a9002c040c41da29509485d04403806450a0500391500290b44020340901e40c0003035490701c40840000351076144200070680450061169101884141c40b0354400c50400f40075854010070820303680700d00807900c030540c506142d0003407000003440000b210450244510002820f8041038000c510313145a40390512981004203100c3c1880c500008031401801c41d100c10418902165828200004003224002e00c1200e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 794127248 1250 794125998 794126023
    0xc23030903030307020a05070803120a11130308040518130f08040816050901081b011202040e0c04050a080615040504032a030206070518060a030902090405031810050d0b0102 76
    0xb80d0316032030400c400940c5d50f19401d4081e0307054070462500283e40c02001c012501d0323001c2080003032002c5644d0019804007070090250b40d81c00701c3c1001c00c00b00c40460310a9204201862250200310f0303031345141c20b0400c6800884600003d8014440900340200400c20305d15074000e40b50305c1808040309151074109a01e26020315407140590303024030080c0080d6040b4541012050b210f045502000590729030a40d00d03580c107030f08914081d03208040c8000740402d40c0141d0900740d1449243c2c401524060702c80510091801c0255242003900e54085000e1005182c6240c011002d040184014402d524020090304440e02c55a10b03100e000341d0750713000400c007414072524400041c9005403010600d882a500486c0100f200b1101d0150f0040c0149000708054511400494405d015003000329080c21141000b0891a90300807441103080c159240b050030016180c0403070709845a40903202442c1c59400345814240031031f211501d11881141840e0501d20820341100a0f11146181e5440000341c610070709005034070305600101d10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 794128498 1250 794127248 794127253
    0x8030403020102030105270601121b120b0105090d0f02151b1020030a0e010504051006060311120901060509130606080a08030103080a0309150204150c23030903 70
    0x104400e0680540085040720130944904541c1c1200143c11711400641c1450110031800c481c1c042407940d803045031f10360703c04c0003501ca0000b06044802403500d1414818420400030800465001130040c03454407515030000000e00f400ba1410000c0c400089024140040003016489004210750564481c40a00743c0c50008a07010f03140d035003040140701141c4500303110a10043c3c1c03281381d0038048010401d0090300380a988841e074144900e4480d03c82141250402401400a20754410241d10386074424052103006500420150020621041d0341c00291490741d0040828103003040000d51800c0c2100084a0010b41d03030410210058a07520b2600c3d000d0046540b216501c00720080921201c8546d1340c100100d400d00c5148100210356883c405181c4802c100d10014104020501c0108007242d080c0c5c00504030700c80240740004d0004060355a070941c2c0c0c050f410307040841c03650201d0140105a40100c010f02d49842074140703401401010798800546c0a800c0c000c0d04411103071001d1003806120200700391504104001d06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 794129748 1250 794128498 794128501
    0x3070f08030f060d11060a02160b07021003060e04380a0b0f0306040201080907030c1d07020a051b0a0f0803092b12050903030307031401060f020709180803 68
    0x10440c4694000351030541c241190100490740a14210b0b07907500c0d040340d100600004582c050310030420290000080c000030b60113080b4502ea241d0109a4007040070340301400c0d850740c54860038010b00c85000400500101030602e130940078820340d600950040c5e4410740c0454030346508003850781c0070030b045481c9030152242c200e84180e10a003080340032042030b03124400d142010821701800004200c54210705900d82034058201d0000320b03001d13504c1021603c3d030003250b4404031120203a80703503244031460716154441d400310541043c01c0d516001203030f8902900800103200411850344151126621403c95607000146504a00c09403401901c0348054500108001c101d1075248030ba443c0800c9440b0344c080e10f82b0030b21464804c800c40c00c150f46002230701fa10cd21684c0c080303900d80c1c07807641d80d43d048070b291503085002c02d00501b0b00c620040c5580401c0258400c020542e804a0b072007604005c80d0040c20010307040002840074180040b81c0a0390300280140450307581ca4008156260283c49181001d90401c42c090401c220000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 794130998 1250 794129748 794129753
    0x503030f07030e0c060301090f0b060d02180f03150405100c090305070504050c0720120c030708121c0f0c0512010e0123220b1507030206010501050c03070f 68
    0x180144984015141404081143c440ea00d807142c0800c50b4255005600740010300040760b90703a006200701c2c81c900030300040003804c840015806801090b4441c141ca0740010301c0300784803464170000c5c02d0030203815a40e0525012603000080c1c4c60301803d21b04004422801800101806020001c503040b400b0100010000600f0220000b40381140500003640c0394480e000000481b410300d445128882c43d0940001402c0c18002e5451500100401120440009001e83d0709403040da02d440e400114942c6410003000114906000c0c10b00b040d40d00e0381b0400a940250481c00c0130090140122501c1e265807002c1286030b0005540b0640003800c0b2071090b11901741c5028400d02003c2e4008001740790500030704100c209160f03a41d1100c0c44194a003402400c2c174407100d41104010351300e0302c0342ca102d02e0460b0043c086034007101d040400340e000070b4022249000203a01c5241c01d42c0f4900307201c01070307558141c10318504600d08245500c019544a0040c41200c1c10420001496140303139000b8000c0e280c40c26846042009402c6450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 794132248 1250 794130998 794131021
    0x306010c031241161103030703020c0d0c031d04090b090102071b1a0906070609060b040e030304020a060f050409110915160305090409020a080106172b0507050303 71
    0x101585640b040c0c180586480d442410f0041c900381c80c80c01d003c9102c042e035800440d4800c007006090240248411070704000c09808041c001355100310301c507503401a11141114885840e01503e80f10030740078030030514500c1c07001ca03500c1700039080840f01c48810000207034000f00c0440c00816170317000d000d40030b00710507000c0c4245150190000c210b0980504001d2013501c2050a06418081492260800b903407041d0000540b8018108081c05940380020f00e6142800c40a4030382c00d0a441040c202191000e42e034840d13002c124134151145150302454900158218541980890101c0546000d070b1014007420340c0c003011280e4030401c22a405810030a01c184000c0c1c940d400ca103610750300b0526180e440780380701c1c1d402ca0801e90348510035959420007030300d00490650690b8500b907805070700401c14150090342313407078501003d83c80d62208180100107007400002c00510300100008038014a04895a20350082c01d0310034559516284405030703000014880100c1d03105c0c1c1c41c0007681d107403040c07160051541c00084100f101c01c5200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 794133498 1250 794132248 794132291
    0x604080c190e0a050a1d0c01090b0f04030f0507030f0b150607031e05042321120d020d050a0e060106020f21070503070c0f0e0403050306010c0312 64
    0x3614401112034040500c1e0301d6000003801181c04408041c400070301c03103c1c100c1e0400c9402264001c4c1c0012025450500025403601c9520950120380c84400700c4009035074060007000040030710341c2c251810002c01003840d1140e44500c4c0300c041c01c0d1a0b282c045000c2400340a00110b00190707400b20f201c110003003e628003a00300d034108640d0644404406129803405041201c2114403ca5050340c0d0b00140c1c1c80c003940d02400918103007001104000052101003207541c80c48a50340c50307485001c80c00c800c8407840002042a07403546860350005045000c00820314808000502c406940f01c1c48810a44800c0b2080d007031402802030884191009042006000f442000c5a000b460550501d00c00d45040c1ea807204420b071b9443c01d10710882c103540c0c0d110340e040b1000161040500b003160304804440134a8070b0440c5e1030b1030f03145400240041e500055080b501700419410030410000414414101000700c1c941900c01900900006100320305018507080700d081014840c910f090030446503140200f0104030390004020500e101c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 794134748 1250 794133498 794133523
    0x1120c050901030b071b0213020c010f0c020319140708041805151e04050406021209070515030619140f06030f1519120c06081504020f09060408 63
    0x200400040344a0404144240c107880e00084122010b4450240880d40d60402864681c2c0414094884c94010f960310030041c0507503824014050780310300c45078140c1400c44502d014074907000b500d0b058207840c5194001c0152043c40c000c403d0b03840e4034800500300c2900e81900c00d201500c100d1100241680400191070060000d07140202103410000d08020141c134200c0300d0a0741d4250f0400e2040c2860a0746146c030102d40e020b000d050003460583c00159101040c01c3c2c84007560f04490841c0c004c2580900410169480c0b503000741618001c04c083c500c0d00000c0b0701200c480c200302d090b20300380000019115882d14551110000300054000f803000b0f80d9180c8094220704c407148454400c1c4141b50788040c00345450f03010f581c00323081c2001c607514068035225201413507040a081842d820040d4129450030281708600d410b001440d14041c907440c0707510030b4900f00342c264030380e42c0082c0c00b4000030030207022208424601c0d030308030608280d174010b03070701c41c8100c81070169030003100e129980c007000004010502c130300089200c0c04d165a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 794135998 1250 794134748 794134763
    0xf050d050a14011203091809060213050f060f0a0f050702130b01090f030b0f09010e1c0206010603020a0e0405060a080f01021c0c0210090317010e040b01090c02030d110c060112 77
    0xd81301c01812413001c8030070001400040000d40148240720182124620b140d9421a0008031030643e0b07a1040282c0e0800180e006200040190810003414420082152100112421850042900500240b07406504000d0701000034464014a029000d1001c84090030b40090414109040d0040a1809030100400d5603002401c00c820000d008440010300c541a82c2c0c0c0840703081c400c3ea41e02c2e0b100030032401c00240038500c0c82d926003c1c08400d440d418806000c101c020848910180703091404040d00e05036041c2d01c10310406104210b420181c6038401348020051038111404555503d600c0c001503500b810a41246a490040c80007041400c0015801080c4030829081e01d844800c11a14900d022038604110b8507001d60081c5020b205074400355440b18040320703c2070a10502e40c825410701d03515050400d0300074181c801c040c20203110074041009205401411844410b0042c0d00d00110002c1d140e004200038071540070b03101c58000c070400f012001511000b40400048503015070392010b800c0e2460341014016200c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 794137248 1250 794135998 794136001
    0xf030b180405160b0a03020309030412080307030b010206060109090c0c02040f150b120c030408070602130503060604090c060f02210403140604170c03270406060309120f050d050a14 79
    0x1000c0d1100c2850884120841581c102011000151b0203940300a0205005001c00c100125141c2010150000401d009140c0c25499280100018080300c421700ba01c14103662104c0108902c5a0f400841c00c07050f00c0c014030300440c500810010580e550581c03800000d500600b8442d00284c030020a030301c01c002d60081e10506515569450a03946214491400b4501c400a02c00c07002654100407400255003040c0304640c814609012916800201e802c02c1c030000000203010802007010740f404000ea1030300400c048808000024141c0d85481003030904d48540c0c2c041c040c07290022220240207001035060481c54a1200018914003c056465544030b40012980c0c54060600c041c0134240000340248a15400510f2202014210a04000940001d00b28030742c10300c4200951126244051a5030400c0094150421446154101080b09030303105070300040101481d24060202081030700015100e88042420540303c0d100301080d0031192440b07422402001c0742d0900040c440303031801d103600ca8a00d1075440c01244030103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 794138498 1250 794137248 794137273
    0x19050a0207120f120207030606080102040f0e100311040212010e16181a0c190620040902090105070b18011a0d060c111006080d140a0f030b180405 64
    0x10385890320b00c00303800c4000d100840400558003032000304c02141203004440e00725036a56504016624241c000101694010504102a001201111001e444079100c030b000c00b446e015104200100d110701c4003074a100034152106a036611a681100d03110191000c0c800318541c0c640001e00003240056820560840305c4580f0548428821000c113111800301a0380c508610b85081035001c00202c14062000800da01004007003961a0704000e2410ba118440000100c00c11060821404a502c4020103a0380644041c24283d0b02c50700d900c003118151005028010386403184000106d8003401180402080e040148003449001282000d2661003141395600910285a17040d4981194200d004070040d08401c00766002000103145400290401c0442d251810050b244500c801e464294455804000c081c0d0301e00041c01211002c2c0103080d40007c107401e144001e44405d0740a103a4500c5407844c075000f0480030080e511003041c800c0e0080d0742e504200810340070501400c4a12410740142c1982c048a1070311921502240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 794139748 1250 794138498 794138519
    0x20402130929060a080c120103060e07050406050121060308030903070b0c0403020108010303081b030a15080d2a0c150f0f0e060f040f03032001090213020f19050a0207 73
    0x407002c03002e4030b50340c01c01035030301400d0700c520002400d4044140001d0003211600504101664001c41c001c50012402c03c05420105007848003980069000b00d09044041c000c40e60440007264001d244200400c0602401485920003403044ae0401882d8590010605c02c2008000014003409400344d0503615551302c070000d964440d48110704c8024041640b8800420120340911002c0d544200e0010085050201d044600a200d90044400c0e042035651460f401d14020f0142c1c103004e01a00e240750081c612443c2d003480c0a030620000034040f84240c1a010b1311403412036498102400d2a17940030850700d5043d81c6400018510301c5040042c44002001008002c0303200303100f004614956000d648901d04010801c9040c011313180e012001081c0031817403c110000725440e481e81c20b540254002d070340300d00395010082a9005c400a500d182180700c1d13814100f813240565103d0304010604500c2c0d010060741c5514880c8651030f40d0081c050a13013803e6000001103150160800005c2003000301982c01d030f4a0560302d801c60b205 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 794140998 1250 794139748 794139821
    0x302010923062206031a06041406030907080d0309030815090a2c0d0311120a0902040b180f012102101b05030403030f030b06090405040204021309 64
    0x5241c40891804003803801c003000180b50040071080040581060709445042d400250790100b000a9620f81100c0c4401813207034941c1d4000c1600b103400e01e181c141752140242e030181d0901412841441c001011660840303080000400804200054030044609a2805001400d03074079800c2d000304251034001034012100401c030b1044002d0040c2501020749510321040005d200d818081041001c1140003c0304001011700840e4641124200602d10100d51050007400c1e1441c8071071404540f4410304c102c055201841c0a601d41c401b9801d0710009250169000041c00b404214440350b4001340c4440e140c40d40e0750b0200c8042d51284000034942c4040d0303660b231107009000100342c40121004c400010400c01c010b1504650718810820503107080d07402010300b4441d40c16a42503c20307003101d00e54400101003081540041c940f0b9410085420104a8a00e41c000460094032522904a20850743d0380005005c41d55640d0507100858842c0003050007290322104010010710002c0d046881102c42c420704403002030403c05845 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 794142248 1250 794140998 794141039
    0x50105010e01050f1603140408060a0c09030323121617070e040207020d06052415090d060e03031f0902040f0527130209070e1e031204060903020109 65
    0x546001c81c807059080800f24172800c02c500b0040216008012401114050005010b000e00034000c1411301007480300031607080c58090024455502e20410100e0b8014040240b5000c03070307880e170001015040c610b85526104052100040608800070300100d088218100d0a40d004103403500140846000040201d20108a5101c4002012003407079600c070f41050b07000380c41001d101900d1844074619558840c1c041e5074085554426504450105158013080310000200c82501070b9222004c7d21001780300c062652190f0710706c482c05203a206070041c040182d260712206003802045c058035102e04025208a041e0174179104d94038000f0741300306c0e408a880245482104c0c119032410030b0042c4501d10304400c2c4040c6207442001c42d26030191f1130300024004000205507510440d0844140c0b204034070329104000e90000003500c0340b010440c10784026186a00d030003070030701c1c20b98002c0302c01d00c00e41d10300d8980003d00d400407610034200e00d0784001c00c00047c101e42000001007070303e02c02d823543c00d186911200180450030650141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 794143498 1250 794142248 794142277
    0x5280b1e070c020414070503191509020306031c05040f091a040b180c030406110a02060403120b03030c060f010602120a050703200c01081e040b100315050105010e0105 73
    0x8103540780d000d08540d1200c00d1000d003000c111104c0304002c1c02010301044480b000455000401c0100c046180340b00701c0407160101d54100b29500d152000882d00107100d00520021039400404141b107550100880c54202543c058080b1154401c07800040030794200b44120b50003100009404502f00b065401152080b0389008140044002508100b0000e020916040c80c1c00c129611b2704039207222031030006140b00d04c00c40586150340c0e04151030400c00711814924552a1032200f0302c401c1800543c08121148c0007501440c20281114180211200800070610000d9240c40001140005958041041441074030030043c648030a0303070f80f50000d0740c990101221900305000204641d81610b80550040c10f0514003a1415100c2ca610f0854a010045c200e41e907080107a0b840030308203845640c1c0c055010307503000c0c00580c1107082507851202040c038940c2018200514000351240090411644503003c0401035812103855a4034000c55660400141802c0c0103250000e0540a0301c0d6001e940207504662003007000043c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 794144748 1250 794143498 794143501
    0x1200708061012081303120e031c050a11070503010204090e01060f0803162103021233060c06070c0c080a0201080a0b1201060f09063005280b1e 63
    0x200e001041e400b1a03054a4981c800c00c0c001b1005c101d1800c2c603e40c031041203849014411103000c042518154070a8606005c151300c3d070b90310520169000080d5204000c0605060f400f00303030b20030207190030f09400781c12542d0198804540014401440c4c0c0240c41c150301580c00800192b81c07030b42c0f4044000003a0740a400d90700c2d0f004000c16126200081c00a008660242201002c50021040128201c006002c03036100041d4010948101201d1503c0e8000e401420040b403050440b141901c52041010f40e10346040a40d00d07454030310100544410341111883c150710010354140385020b0340d021340001545101a01c0d80c0440280126034040d0000e001a4402e030161507842a80e0780c0c40c0749100c0609000304170550031180d6500a2080e00d40d0901034070010703003003600c00f5490450802c11000300300d800c02c0d0301c02ea80401c42e0010000a6240301010b08810819800780001d0000450074550714004001551448060310300c9a01c010042803c140c001c0224865168007059844040014020941d5a100e1010061a100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 794145998 1250 794144748 794144753
    0xe040519060509040807080a0309020a0e011502070503060c0a09050604260a021c030c152315010c020312030a0c09090203040c06030b1201110a021e06060d0201200708061012 76
    0x40141c40364238924034000c1010030711035010981040d07040d40318151803900c43c00140a80d10b0401f80381e6070080803e10050110030700d00300010f59035643c050440320070341c900012981105842000028003511001d03000315901d0783c0d5458050700428400401c801101103030182e00508100c0810b022903180c0d0001c0c83c5440491086c440380e510070b400c0002c00c405200ea4092030300d000a4140c40c0c940c180714241d0300c001400324000030300503001c1409407a060a00043c07002c100400103880d030914100c406000c1c030b40310030310080320f2003c20715060b210704552800d02d0b030100411010112541211600d158203655000c5842d640301c20030400c0e8001500c0007000d00003500000d00566200c1e078028a02040d0007440500c000240910305401c407040c42030347d524103d100040e00c0c2c04032a010412040e2146140c100c00c01e4038602c0f072a9081d2103d0020f000d82d84190000c18414003513a1140d0b500300c01e0880c5903074140c494506440103295079280300b4469140140543d900040d205120802d841c03044034843d0024411498095 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 794147248 1250 794145998 794146013
    0x1501030c03023a02010f0207080a29010f050f0a12060f02190305060a05010c080a05221403100506100e060d15060809030a0e010f0e040519060509040807 67
    0x144880c3d4006540d82404071000c4015044110f0842662066a00c001e2014000100940300010b10306c000c2d54072040b02040b008600054000c2c42c01c1e0071006200340e075819131912030300702c50104041244203038036400003184e00a185000c0204a94080368000d1003490400184041d540c01845079201843c0540c40c0440440c0a030303000066031000d481c4005150105c0c4900604003c00030810750704c0001d40e95010044a81410300303441010300000d003061a4000580d507501700c080c0c4161240e480410101055000000000c20700d03d000494a43c2c651009040d120101d4500d150014000c1510038851a901c4103805e81541c45468021100605006030f41091303000107803107042a1051041c4c211404015010a100b03084c0300304062980d038006400c80181c6072aa00406043c0b0181213202290420083c0720895608441441c0d8400e01c04e08018480c4d0341905026140b0408000c2c4e4107810504110402202a42c610703d01540c440300000c0400200c1e80743e0f424001c0789241180c001b04016420802c0c2e81c08202c03503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 794148498 1250 794147248 794147269
    0xb0a0b070312021b0106091107080a0e3c0102030a21060b120f060d030c1103011b0f020f1506130c0302030a0f1a060c010f1d1501030c0302 61
    0x80d040c00202002414465803c9074000c00c206080054882d000d820b0b904402e01070f40b001412001c1c810f003e0740003000c1c2402064480d886e80245600400200020800d00034a00041008802803104220031410384103262100e000b030b460014003a07419404038410145084110342e1403801a4000d5040044d14ac00a9591512001000100900c01c0345800100d106900541d005050310000c000d0701c40e0a19034140b8000500500012980320301d00080020b2a01d8590558042d143c152400703007136441440c208400081c0da074081c9180c0550800a010b0011585001c460704800c0055441410348241300c4030481c0c07501c4c001080140150444082d502d048540d0715400c54204400518201c0d51402440b60b8908580144d011000441c1e0044208002528a8400c0d5111484220014403d181405442815204507a071106120f04004110b41600c00c83c00d510006596149590402c8100d05440c1643d0124100804101e07407845640001c0000b6401380c0703c0c450403680e025100501c003d05590801001c1d081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 794149748 1250 794148498 794148503
    0x801030b1e0406020c0c01080c030a1802090901050702160b0d020c1912020d08010302030d2312041101020d0909020c0a060f05150603060f0f0d12090e0108010b0a0b07 73
    0x1200820760006590075903035000d0791040c2c20040c0e903402e0b00c402c030030304107102c508805062101280400003c04507800843e030344600b810174000350014450490000380c0d481a1f074080e401c1950f002c10040c0754481540b10500610311a0216605910080708600d400000c47c0601c0052201c01c1c8480e0740401c0f80c4d6001f4042524000046d0703100040204a40642e03030415110a5569849000c080c0d4080c907010701034920800d800345080e40b550760658012aa0702c101901c0030740200308094042d20a00540080035003821b141d0700814a584421503643714003907e030203072030a403240d101440d004a041e40c0000740410407480d464460303401230f528101001000703402c51851042107001d4220601c00040c0c0301d00c102078441003032000019440c10031103055080760824610841c00b9420400a00c0f1250ba15030784600c0a03c5402c81c3c102c1e1000100d880802c035000f8000e400288003182480310000159001031094007550101d4541140c02d03a43e841019090312031000b1102c1e000f4120000501c084003180d4003c11001c1e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 794150998 1250 794149748 794149771
    0x318040911100206180610030f1b080c09130c1e0e0c04090e0d0e0f01050417010203011e060c020f04021219060902190e1c150f09030801030b 62
    0x90240880c2d1082c4070151070900680080b010001130751551240d0000500d1840020441c61800388203601c3c50303000501010f88150340361000c19007000900c002d44201244583c0507a42c04c1607440304455540d8500740301d0a8800d0312042c000520743c0c200d2101004480d508001407014240c904030b440d400101550918152924540780c022690b4801003403040d02404e50701070210b1f030300d500d402c040313404817007954407a0051904500250448a40e100202254010049a003402a81d007070381c00580d00703407159900c005080d504e240c40b0007078100c8040d0b010b14102c07007491850070901120340581e0051012a40207000100d10101c01d580054109510183c0f60100007520040c500b01982c180c074000711008580300e080c00d5a071031150700d0340c0e0010350040800030700c5074840645c1410400e401403001e09442d40707040d01c09c014400da5501d4480d62205c0c464030818851105203002d0907042d00380507800c0b4180c00000d00c549030500350f402c103400784c140c4104100c0b00d07055950a14141d00b035541c2c0e0500c0000c050207030305002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 794152248 1250 794150998 794151023
    0x1060503030928080115050901240f090504060f0815010807090c051b010501080709020c03030a05040302012009041404121d03190215032a070602070f021203180409 72
    0xa0400340b080b00801c01b202e904001c1c0152810040204450058004411076a107003245a030f9112501710255034119031030304012010f0071460350f0840d804000b42d032050354001d0600307400241281c01000b14805481869007640d110f59074104480030405428410780d07080758070042c01008801c019030b0020810345180d1500c43d21307002051016000991003441d400803142d6441d00100144c0c2001c001e29001051240425410080c00400c0c054486c00004c110740881526000013500700b604c01e6102a10524140072403480301c200010a0410a0700040c0c1c2044c02503152140c404207148070601d10b2449154416400204043c030041c0c11610085109466640070314050a420401e5a0600518020046003104818124200c0c010440c00035000b4a405203140820402e121320710500310000e0b4040300103e440300491540c071200040c0d0500c20030380e01070700e03461008c07030010300304003410341103080f580e008842541c3d007014017003400c9451348290030b44241451041810079140f4103094010040d900e00070180030100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 794153498 1250 794152248 794152259
    0x602030402221b08090c010e18181b0603040f0f240f09031b080403120f170105210102070f06021207020d02060123101101060503030928 60
    0xd03041c15000540700340d01d8008034070781d0540380040054030f0290352600000c1810940700090302d405002000604100c0a900c044140d030301c3d130348600510381c003299101c06444c0c81e0030700304010070225141e0b045049010f045542c0ca900c0040910b8004601d8000f0301c540d02e980c6940e5100e07102e08081540442d200c0150503e1800842c0c4c0d286250700041c1000108030110b94240105001124004002d02040c1464000b40c80c01003944006000604005410004c11620701414000541d0145034001003603000700d0060b601d03105500c00040d400e260702c940c0303d00c842c1d14902d00d062109000300b400b032980c0040007001c4810031510708050044070300a803400010701d40015926889a03100c85a1016155160005900c100d000c0301030903004c4e80015180301a00c3d804018900003503e074441881400c1200040c118007620350342c18441d215161140c010020f02440d000140003a00101c035404803030015502c0c0840026550030b0110880b03810140040511400300d40c0240c03030034040b481203840703000c469029030808100e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 794154748 1250 794153498 794153539
    0x7170c0703021c0c4704122001060302101d0118030204050103050a170703051c020d09051015050102030d1d06100806060109030503121f060503012d030602030402 71
    0x6042c0104e211980381c102c0072061208610060700c118405030404040104880000d0403040b1b80040c1e0140854400000542d012229a500900f11000304840f40c2030000c0701900550158080764402e807800d0440404511081d604120a0b0011411980351854488021b610903584011040c0d03900103a058499142d4000c0740854a003604101c41c55480300000100f80300414014074045c21484110918048080d43c00400b41c2c042c05000d451003114407101300048030b40d00e0b01983c07600c1c08010001c21030709071203003400e0b035481454020220340146001c000f603030b03401019410030080d5181a001980b40031030b005103050003070032103040304044032090400081050b281441302501403103030410390003600e5060907030f900e04000c40603102c98140214001d0400c00204080180c0c0d00001007030071a6100c580c0c400d6200000c0e0050307140d01a203512000800400c455070003030b0165058482d200c000001c0c0000000441101900900e015010514107160400000349150000d60b13100e80302801154075100c7c04460042c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 794155998 1250 794154748 794154773
    0xc020a0f14120408061005010203180103090b04050c211b040608010507050d0e060106080a0e0a08040618090e031b0327030d0e3607170c0703021c0c 65
    0x4102c0b24000030100310703c44e41084041c0d0440080900003911030b142c10b002035524458481004a0340944c2140010260b009520285207107801c201078400d85e107803529050352035566182c0c03418495081c0800c4890076249600c0081c07044030070300c2d008220074000140c0e04203078a10700c080c00f00d5001d03481e131402103104c51003801100e006071555100c040d2180e0554800c00e0070380300380402a030f00c6a800744004001070baa00100f05500000d2402001960303080000b0341d1801c2401c001d80141c081c1800007000640b00f540314261800c83e0003181c0c5215809a1140c030740360243c41c1100c18251007a4020320a1000305006213020311180000001108d00c1c0c0120303001d201c8a000e01710360082048d004c007009461300d00e0a05200328031140c6001c1c6403014100840300009010344a0442e41301c45481e0050700d01780140324080890040d4a940700c1c00b828014607140c00c00070508200f03001542c138144205404103424000e44010b82d41c0c07099041d005802c08103401a010f036020b8056a142030208208c0c442c818012405101060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 794157248 1250 794155998 794156023
    0x506060d0209031905010522080301060305041e052d0615011b0302031b0c09190b0a0308090f030d080c030403170405100617030d15051905130c020a0f14 67
    0x416545040f070855005860208d240c40500c560918000000441071011241500d10754140020540c8450500e254500c118001709141c49100696440c20f001c03000464100260043ca10303040390211000c0802c0802c10403050040466101d1030210f040300301e204e15080d6801d0702c1850004d511120286e0a108089200384007a00540c000003201201a015009000c1d03c040d1708200400f25003581c01d01090141c507006004403444001407611100419094000c400d409000a090701050f80d1203041c501166071181780090310925094100142508020407800c0701d103109500c40e40e0b41e0780e031101e02481c03040d0310042044080020000c1b8800180c0d480800c4240141d0251004103240e80d110311044d070466045410004004000030354008010b1000011113400b542c9003400480c910081c1da2000500a02981045500c141c00110041440b482e8440c01001c456080325100d032004010542c06007101c0702e00c0110b600607000300c002d40e4003003a400d2403600e80e031038401c4001144040c03034489000d05100110181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 794158498 1250 794157248 794157251
    0x6180a020f1f030207031b0209061221040f050d120509060403080a050c011508100e1c11010b01030204030827040e031e0a09180207080406030912030506060d020903190501 75
    0x20506d580102c481f10b1440b01b00b90540030440098001803600a801014039200b1054007483d1030989070280148506450215140040784c10102c0031038035280c103d40a018415150108001383c1c0317241688210104170342000c00c030445400781303260480f0036504c40c10801d90000f40402000001175480b0009107103405052b41d0b62900e50401b000d42900b92034020100c4544d0400511052081c6030300862188040700d03108400040c4031900c000c8140c2005d2550251404500481c010503652982007046200c80d074900707000800218500e04019022070041e8080507140c00e4080c0a11507a0001810000a0b4000c3d400d00c0001c1c045046000107099074443c101c82e40380340d00f000c1600b414a0b41052034082500d0455000c039810221200320080c01550170740315102d504458104a0000740401d68100c9000c00e03040024039079102e0b141e09010b806890721030300c00c40e81568031203040001d50b44248981401140010035084c904200c068041020b5007104450b25814000ca101d900d1080c1d1003041540842c40c403c500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 794159748 1250 794158498 794158507
    0x1030308090f0309010309051c0c1502042402033f0c121e01030c060801090203060d06050a02120f010311010c0c1a070b07080906180a020f1f0302 64
    0x10010302041014100c0e941a502088840b4440b038000300544041c2c0400b86800a6000d125080013490038540b2100c45800f01c8902e00d9040f401365010f0540d0703003a24010255404104480c0301c52408a10072441051842c912022003e22919010105454804c1c2d451040301d0600940d00410701d561102c03060305011b1030861081600d0850303440043e100558140318522840e6161581003c40b0a00c10130900c841000000e600054401049d103410a80190401c0505035043da1286841c081102c0d40d801003030081900c0700d00024407401280201d070300c682c4000d03000d03594036543c81e519003000d084081d01d0300505035001d010f480d002c3c1c03402c0001c482c410200c2d4401075180e9491400c1590048601090300d1b4104400c42102c240440c100030348410840d241d00000c030a21554000002d01035003c0c1c100000c2181003500309008009500080301070042c424072064442c0c940b00c0b43c00c103240c4041011240340361500505025005441c10b0508002c50031005400191a10f03214010494480100443d0101081d40400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 794160998 1250 794159748 794159753
    0x20601030213330609030308010e060a17030d0f0e1e0106120c0e010602030423030a060c050310050307121502040902070f030306120b060d030c32031e0705240103 71
    0x31103090044c111810421142c40c110744000301304e02c0301402902c0586488a0102d080d50301d50b050708400030501014026401d10380f40b03500035200e41c803a03100c8c0c8091504140e1300718111861445a41c0c02040000001e0100c0c0960040a0300c41c1c0000e4075614007035558031000041c0b102211441a4a2070340f040044520542c00c0041e1a0460740c4103800a4046610a00045c40340e62940322209201c01003000d0231510b203402481c0020b1030b000c048a402045030741880000c0c0d8030560800b024501038407074407500074000c0303844a06259941c038a51088102e61082e070b610f64000324480c2810395101100b505005440c00b5100d1784100180d0b40324003c201c0d104401c9000c403006055042c030030030380941140043e1000300b000c1c079120408200000b40034288074910032043c40c2d080500804031140b2499002d620020329124050b44640d0198518800344510300102070404034a50f000320840d40b401070164801882e0030414910300010b0f4001380e90440f09449503560584221400416a41c0c544c0c01900c602039a560551 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 794162248 1250 794160998 794161091
    0x1200a120c02030f1e040b040302121c11010e060702070602060f04020a1503020d0e16050d0f06090c0e010b18040b0d06020d0f05040f02010f0f020601030213 69
    0x1250004034062800d000000d81a40c04400c0382c0400501c0078505495810080440d16141c0c01d49030b455044800010f030026a0700c6500000d40110703402100e83c181e442509210b860f0312021582054070740c1e00d45c0850414100e50246c03a02010040d444800000d900c03a14071602842c0200039201e0a02682c0412400c10a50380d0402401e9801400c0041d900c185082a5002c6856180300740140f41c80312001d006022000b0740700c1c0c0d05071021403080380c0040c40441103d034100d50319030700510718110108140c1140440d16003441002c4a813640d60190010f40c112403039444035001001020390445982166110000d02c90b05001c1b5a03a010708004140103550ba060000f54296071000388545034001d07410030a90071080d98802610316042604020b0150780e9002c0d000c0c10310003c00011903000302c0c8916040921040c0107480d00d094207218403e80390701284090314181035600c01000043c800041e400305005200500b44201600c4c031064001c480480e4101554400fa5031540402403e40c02e0142d09107010880103010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 794163498 1250 794162248 794162267
    0x1d011a04051806091c0c030c02091b07380402190b030702070e160c060f021b03041404060e160e1f021510170c060307020709060812070201030e01200a 66
    0x860402c43c244086d103a80182a0314801d5a010344100e481c100010390582503000c028604220440c040340e9100990f1404082251050704200048000044810b9a200d01e440381861040d004ac030350306c0441d0303860b0b03404c0204100d41c1c01e2130700342c01c10081a800500480700c20042c9d80980f015402030065181414042050004001c0c40b1042400110000c0c0318280c4d00709000318001500108003007502416882500c0c06441610408800c10240a28400c4079a4020025006540940300e01000d00070210040006950490144a8500072018017007608001c0c90305d0032013422091810703c190300100040000d1280020741c142502c00c5450f82810100d542e40c14030040100c0210400e142c00c00f800c0034110001100c0741400f0b000c030036074219000f07010072010400500401007401840e40d5500d01d400c89000751503806500c24140c085040c9400444c006d01d01003061180d0040c889000342c00c105080e0011000741410380704828065584040c01c1126924a50003070203401400445550344a58024004054009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 794164748 1250 794163498 794163553
    0x9131b08072f010612201c060e2104030302161d090a0614040204050f10050d080408010207050d091203050702010f210e0d020102041a07021201020c011d011a0405180609 74
    0x200300002c00304003507100e1a02c40c0d11500300100140d040d120654041c503043c030348040300314080201e24ac0f1011403441c07000144240c074441e60942c0c800e0a1100c07042c0c0105030703960040215a4a02842840c1120301a90480741d0250f6614115007a9001c1c1c0d480d01012140c448404a8051211104100c1035007040d000306074000c129010303410030503c0d01d40e40d0316407000c0c05805040d00c94209500c0359814401c0850a4a01030411440219a912803c0c0b420700c1c0d54543c003041e1300303021900e818400174502d06503504075100d003905615154a03003491513004680c2e1030381c031407504400d00403e030800d144001d80300c1000701d08401d40070000190100003003010914201102c04c03d00110781c0100300030721004101f81010300900c01400b0b0701c1d80c6c4405092002031403510403070210400343d61020036002100081500180f042d00011001450300212000c0e8007800e9031602504a030fa41956802d103c103080c01d15500c50340e4051030491107000d075042d00300000b0381481c400341c4082d003e079400050380c1e042d030350b03100b14000c01541d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 794165998 1250 794164748 794164759
    0x90603021206040201090302040e121207031409030a050a050408030d0501140a270b030f0105100f061e020f0f010614060a021209131b08072f01061220 66
    0x3e01680001d1200c0103900009005a440b417a0314002203904109011000808a01c1c4645070b05541c5408151582e08607030040000c0d042c1011081c0c026842d000403401501490041c61400d00a02419036156001c0315031001044000c100c0000d14107018009449541540c0101081c0303540351000c0590040240c00741c180c800c40d8a0001004082c2d000000c640c4c41c240240c1c0b800c00c10207170380c3e06e141000385084005980c040c05541440090b001047d070240388201c5000f0300c891621900c40017140321b40c41c854098000402c03040c00e82d06400344038a08900300079450b10b1040364200404c0350321450030680503558003201c50303449880500555510600c14030520400307440150800030301800c003c0d0b4801d40303c90f004030ba143c0005507240260311a100c3c010a1041003040501490f0400c0084081070038101c070f42180004d07580d50200d4200c0d0b1044103103901c4034042d03410300000010034420916404040d000e000202c0c0d965804005440041045070a8116004201140028040310358040080c1003000c026441031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 794167248 1250 794165998 794166001
    0x5031504060518040822061202091e0d02060c01020901031a100f050702190819021e061e0a0f0306030f03050d090b0103050f0d03050f0705070813090603021206 70
    0xc0d141c2402e041d00c4602c001c0152401a203845c180b0f4207003032165105580041d0b1070035818040548060807414212582c0d0b50760b4201802070b1401c0da408034000c0c0da040950014030403088681c1040341d5100c0804d011f2000b0000340201f0520703400105664004203c01178103940218040c0783c01d6070180700e141000c070291016101c0d40c800e41c00015600400743c20f40402481401c040c0723880214880d00994840c5503015008510400c05c00c02041d1800280b4418102d540c419518065103155550100e0800710741d001d49092410703484110000015614040d1068211405102080c002800c07801ca404003000348903080c65995141c0a40145980d0030108204241804c100c42000064905e202503861680c01d40342c0580c8072080c1c03d00c148040e080200002d840085040c00110034070a01255041141040c082202c0000456213070940c15107208540d002c01018411000a81007401503000340b000310302c11a0060314100b001624942035400a8100e265102c2d52000c0030b00441c14512101081c0041460041116 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 794168498 1250 794167248 794167259
    0x905030c010504030b0708100333140402120f0a060c110f030a0309020a0824150607080304020406030506011d01090b100c0212010c081e010e041b0302100503150406 72
    0x41031703c09402d080c00c02240380d0008000c616a114540c014685c00040802400e4200042c410110f44c081040300b030f41c0d4001c50305600c44504a205100c00b030511801d0222380c0755107640030001640001c1071280f516004029400c42e00349014130003040ca003441100e001403d2102850001c00030b030b07543c5180240b140c1c882d46070790400c400d000040d100420000c5c039020642d2000f602c0403952141c0c041d80090000d2140440074a2154840c00ea20b2514808100c0000ca407940c03284c84102d0f2220000d0585a0068403c112490126100300c0040d50b21600151005c2640750382d03030b40e51614200e030980c0712840700b0a0000c8902c14448030f03003144030300500020b0828003400c039142000500c101c3d6410100c000f170004982c01d010031915442c004000d24403821008007c88440090040d02e100c0045401c178800c100b01180c2080900c00492561341070740c103407900060881e40d032035a0709810022114840d4400400c0320000000698540c018054110365a95400d45c907810300070351511001e894030051070301c43c50400d1400e222 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 794169748 1250 794168498 794168513
    0x50c03060c03040611090d060c08160c0308062701030302010e011a130f020c031323130905010c050715090b0c18060c0f0d210e0f0d0905030c01050403 66
    0x30465044030300050300c680305501061481c460040c0047d040800c01600c03805008081c1e00c010001c80c0d5541b28012296201400410344801c01e4a0324400319038100c540d4800b00b40310303c0704503503c42406040c100303140100c1c41007110358403000c03080d442c0b00c0da0b41c0754010b0080683c2030141e4005808204004d00603452081c1c411104034400940e424001d2840a580c0c1482500360703001900f009158410446d5900340f05800561240c3c06419075010700d0320381c2000001c0600064944104034501072920a400c074481e0020441d101d903202c0010703982303030f91a0807091f0003107102841042d4420465032109590740d2158507051900001c0300703100640c2c007490804094040348d4200391980e88888001080f554038007a4030031040743d0308009030308a504440040780744500740800003103103001842c0302d10450f0100c2c11840c40c111812034522101003029460803102c0c5a03c1d400f190407040e50034404e08243c0d881e0700404044a49415422500d50001840114040000d82000d201104560b40b080c03a02d01e280c07074210b8a480c803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 794170998 1250 794169748 794169751
    0x12090e010e0f0601050d0e01060501140712030e0307081204140a1703060102030d0513260a180e071e0f05090f0f1302041409090a0611090d0c03050c03060c03 69
    0x6850200000150b1260b110760106c428400b1200c4080140540c03010b0101e00800440c02050f0114134441c000d001c0b00140780c0d003a07450840c1d021106500074140180c2c100d01900c4882c2c0500481d12040c40304100089000303003e440c003c60211141900780c81c15082c00340359440030304a050320700d0308042802c60115071540c144050344079000c22015540d445d00c80040f840d61050512a090716480c00d401e2090300c002103041480343ca4084c42c00c144e22741c5030010301d07950303200202d098082030368070f041004848542c001c40c050380d4100c2d00e00c012110036540d55141d40f00c01c1c0608440c4040040c00348005148441100c2010304d2078030300945400301d115200d60710040e201d0300c0b401e45450320030135a42101d80140e0b982c110011100745c502810700c14001014024490281d0064043c0d0303d5a525250740c0c2c0c502a08181020318841c103280f0005201d0340c0c91540303803c0d00900c1c07100090504c070380040180303850b01d40b558202c64624501c140d0758040543c0c6103040081c10402d00c40e028a00c282c00003c24440c0141000054a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 794172248 1250 794170998 794171011
    0xb0a0e15070204090809180406050a0e061906150c0c0b160803062704050616170405010f0e031314090c18131d0a2a0f0312090e010e 58
    0x184c400b055082001841c004c4014269014003d003400c1720034410b203041d2150285100b52010f000c1074491880c0d4800f41d610520840c00242d10813000100421034a0183d108590a05000000e0f029100c0502269400c1000b0540c80400e03401c0710824100326188000301c0007003d440ca400c50074810314421104c808500d00b00c01802d008808404101c0c0c6545002004940c6e02c80c280e0f43c1c52840c0305007201641101c10803101503946004600c0001d01803401031443c52050700550f41d031201d603201c0284650b80184030240c015100c0c0e40d030354040001121494031a41a11010380401140c44028610b000c548020035030f04405411068903800c00d000e501c640340e500740c011125035a00b5481e089031103040343c40b42a816000f207034401923004807002003070115445402d050f01e40405401c0c29004c56810551340341d0b03a01d10000c0c10700050661200600e840e02036100601c01e00704480100302e40e9100c900d5200e030841900150360f136400b00c5003a41c50254010180000a140c001d40210312503240c1000d801003050000c090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 794173498 1250 794172248 794172251
    0xf18070b0a03020d0f0203100612060f0308180d0c0f1a070807080d150e09010504170307110a05100605030a050c0f060d021902060a022d130b0a0e15070204 68
    0x1c035413051600540c1d0080d01134001103480f407070011180d084840403840f0780b50114500d9085a00c001455014050170754615100c1aa0800c0c03541d55025616481100c4113160303200d956003d81281d956100c154806240104c1c0b031007001504004400c0c260a01e980d2104840d00080c0345110640b80d4594190784116800440c0d980d2204000d00f06510710b0320810382810f800d6440c1c4418420704803c0f030444c800584400c46001c20a560314845041d00301c6a05079005410502e90350401003404482c034008642c00000c0e883d0400b001d109428a00c0c0c9003813407440c0119000e0b0000d81c090040780145105c1c1000500c0128018480c4818545402c0e8448c140e03901600d002e11a80302c41c80c81903460b001e00b01c40840303002200440da1010510305030160f0146101174500103008803404a140c420070381c000c0c1c840c0202d0946003051505888001c00c400c4540d4102e0001c0702c00350034003030345800d2034603000680300030030b02da80c100e664444000c02d00410724280041c10903c20200e50546036540e00200050728552a81503d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 794174748 1250 794173498 794173507
    0x5091809070e090a05070902122a040b071203110a0518060f0c0609060c090906030f060c03041716030f11330408030426030f18070b0a0302 61
    0x55090404050b038102a00c1031440405202264800060141d09240210165907036181c5602032203060780314203008034070310b40c5a0402081440e100c09100c0c840362104440d007c00c2900000449803019080f5030b1015040300301c0802c07c2018401c0c002c2810400180c103280401c41c0c180c2003125501107010346ea8041080150102d000d1801802484401003903600c024007151700c91404500d00714641d8005900c00d0964040e5070b000c01c601d800009030040c06059510945803c1c1007010082c00140000146500d50510400480450340307801070001c10b00500750744000ca59286440c0c140f291240310f4804002c90a00c030704000d0b031840c1e07481c030003903010510b540b51a110040304050901290701451901c000368040c0500c100350440750b00d04442500004480b212203280b01001804031100302c0700110b80260100c0005c100007030006840c0040c488400c29207001801f1890506050304019400403030780c00d4030b07440a6005102e103044c01d0803117214800108138010a049400d0860381000d03806020141018540c020a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 794175998 1250 794174748 794174761
    0x70807080403030905071523090d050c040501240e0f0909010b12011e0b1f170c030f130c0303030b0f0d0602040e010510050301052707080a0507050918 66
    0x4c0103024969000341c100c400075a1100c1065410032000402e000c04600000c041c010002008800011307181c00355543e03242440e0b6050305100032004404003c03540d50044080851441d5030341d20805000c0c086004584140a82c12240f06070760301a240c0980e001d10a209030080c10365550303400940300b90481903690007910384980701b401e030141031100030083d80007410144641c88844e055002201240c41c0b030004e4101810710311420011a0703049006a60480880641c004040000301300c00c814031101441c0494400c440c40641000d0b2134800d607800c501c02c8600006102d400c8886100858014444030003104c00c0100a660b513410a04140c40020149501d030921040359a543c0440c0016000016254810755900e5240c050b0080d40117000b00c3c50014401000801e05081c070111818400c902c80e2a4035144d80d007010304001e000100c503459001c900c004401c46a1091904080d0f9500804036071b01d5100c900c1c1803c21035002a83c1e001041d00c020800c081c4441c140395510150f000005401d541440e0201e07881e0070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 794177248 1250 794175998 794176001
    0x1120c15030b0a050a0503030405060a050c070b0711011407110a1d1015080103031d1804200a030305091504170705030d12020c0c0405090c010806060307080708040303 73
    0x56008048150580d0110209103815400941d02c1142c212034600d1550344034000c04c55106080c4c05281c1d0136a0061109200c00d0030000010b00440800e0f041c00c904101120b40301c586808a190800d6450100116020b010007640f00140c0d8554082420180b890301d194007109000d501038180058003001c10310320b013642e840e15003481c850003402402d010001c0400503488803100d03604094811040008405500050b058030a142c407492806160361051030591860310304451000000104003246d18060602c10842e560301612034039401d1800100100c24541410a94003019011420303002c0e44d80034200888aaa03544036140054079410309209841360b84440c0400d080c2c44000f001c0d10007401000401207041d44208005814445414045805854450b01416120500d501e244404a4840d024030b900724080c580140400c034132503000325080d010068000034207440c0241c0d1102d1594019520b24106542d10406183d8810001c1d80c40511b94140340b10010084c07240244141d040010140200c1c007018880d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 794178498 1250 794177248 794177273
    0xd030c06060515120f16111216060507020f0309060a1b0615080102090f01110c0907080702010e071404110408070b030a05060102060402010206010b090612010e0103061d060112 77
    0x28000703958003c0319415400d484e501c65480050070381221000544240303c00728480d40f00d200324200740d0f91940102041920a10341c040c50f820054000e10030850145d801c0d04002d0300d58112541c1d40302c4e0103036016041480494601405e14011034100c958a40c032180700010880700c1d0982c090ba003403036030740d00c81c10320407074100010f40340b0890042041c00303002052065682141040c581204401c0c0320043e62102154200c1c41092041e642100c8038080041e000d40c080c4105c210810310110564080308140c400041e00728504a44c0007011a49071000d020102d5424400c5000080d2041c005040040c107119a04d2841780300450614800c07900e03450411004600541550300428203681103e111644842020015400071680b0310f400a14180c0080c40075803001038820f0280750107030040c003c582d0820481d0701a940c001100e507170b0080c0c0c040010f01c11841000c2080780c02407007445246140380d4190301c3c000d0700f074a15403020050440000340100780d00140110b0a10304642d0f8020485040b88002d182c450241c409 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 794179748 1250 794178498 794178509
    0x3081804051005090c1312020f0d0b0403090803040e01140d020316030201180e07080903160302070e06030304030510230702031b012007060b0a032f0d030c0606 70
    0x30482480302d00e0742107080800550703004903a24403003070740c944150312480e0080f240d50ba0540903802204014220200300c072640400e001520404014813100c0104070a8401c2c248200c031006100c00070002450740c440303402404ac0400d0005036241518015840c48814418060704003040c2c04030101920715a54079242049059000d030599007048581c4041c208542807500c010381c003060003002c00c0085c200c10300e510303441034408900c81030501e030720744800866113004010003a020030711003007001d900446442c03101c5210303036407081c1c0c0100f681c03074140b0908400704038018010394069807050006000080c0049402c0600c18501c41000807618000c0068804001807406041000b809410a1003011503001c8010712003010740104082c1e0100c0e01c030303445908035486030030300c0e940c0c0d030901c0c1e042c84086c035040c8001081500c1c0554004100e41c888840020210852544112030880303000540102103181010316184080c10004400d003c1cac4010400b1409840813680e00170300f0400e20900c8042040401c1d48510060305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 794180998 1250 794179748 794179751
    0x1e040e07080703060b01020a15050405010906110c010608190b040510150509091c031d030313051b0f011110110a02010e030306030304090902130c050d1a090103081804 73
    0xd664103225030b25080039000aa400ca403d041140310f06500015032941810350141c44000120100e00360b850060401800c00c441d40e54a40d101c1c0408103066029242296164411050752041c0200c6800d08450b000d03803101265400c004940b40c2002c403400794031009580c00c0318858042c6d645a107002800c1101c420710300c10401d072500026107982c0744030400c10001e88205441c1c0070103a840d2275000ea80e803240d1a000420103002a07070b402070462442904102c000c050652011030207404a1f4070300c903040d80c2007111035254101d405003501007840410414020a540481169604e450000012407000042e840006062191a041c40048000204007580e0b014190480400a07a0008200c503800c580c046200c0318015800d024418541880102c202e902501c1d0040040d40341919188030600944444131050341d004611003500c071250482d500544200046c0e50341c40c1541c62116510703640440390300c0a41407081280042c060503081d26060903d0381503d810210064540364203070003840742e1201003080d903078009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 794182248 1250 794180998 794181013
    0xa0c0605070207051c050d0513170f1513021e030109120206061e092206091a01030b191b0c0204140702030316030b1c021302091e040e 59
    0x40e82c0031030b007001514012600300288081d8154140b02280012501405580000c003214080350300480041c01040e801d41e80c10320040e80c1da12041c41000311261900d01c6580c0040b440301000203804c0c080c1c103404103068055440749081210155500f8600102e0090003007812040f80001e0b01d100c10003400020364002c00a04c5446114a000301d0000040202440940b0a400c0410541d291054040c41500c10940301401442100740801048a81c09000b41d62a0140c47e8a0440c042441064901c1d03003030b0140d41e0100c0e003181907150084010121448005040030403200602c00a282808456007003560646e40002820b08003401d14000d08282d4214040121566001c0c60240e0704010002c00e0700e07000725002c12800652030110041048100e4540c070050704200005200301c0c002d44800161000c03980b41c0000e040140d1383c04038941ca40c0c5115080143ca070401060030031841d1030402003000601041041d41050048004600310b03102e0307591400c5036520010902c84460302d031944201041d100d850100c4911 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 794183498 1250 794182248 794182261
    0x1051f06110120090103140618060d061b090801060f0b18133201060f0216061d01031a0d0501140403080712060506040e070203120c041d19020a0c0605 66
    0x80d84c00160524040707410010700c800780c03811000c030180c0301d410301030200079406a4040d0340725105400140350783d50050032071310030901007a803034032410141c40894402185036003c4040d000c1c10704a82d95121101580c1005418491b407200484a1400c884e000c58004ea1180210814044001554080d098106000a008030042e04594014901210098a00404010708005205600d098401c03990034a60241c03401002040d101d0134108184a85500c141e8516120ba50300c50703a03181ca015401900010072940c04c0e00c0344032884904c45500382c5000d00b070802030318000264908103c0418800b20340b06c2d03603079040203405011081d04503840382d0301503070701c0c245161401e464040e0485d2400c2c1c40440001c0c2c080300201622189600ca080d050307680050800f82864500342c0c200c0203441e40100f1420840c081070000e0102000c848180ea801030582041503511641880003001c50780380042e030705101140c0759000303000c18407030710310041c0c40300484440b000350707031010711010540e5000210b42c0000d0a90f450a400c1041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 794184748 1250 794183498 794183561
    0x5090328110102011d102405101101020406170a3b060c071a0108060417040806040c08061b0712110a0c03050613050d0804060e0304030602070501051f061101 69
    0xb81c8150140c0401840a4111203803658103480913400c2ca07555507544c022310092900c008800f020b407505180000c00c01408003a0a803ea0300598400701c007284d456040b1960009181501d0781d0322140e5164208003d5016a0140c0c210340c0f103103526075010002420b02c081c0f1000c1941a400703102800c2d8800c071100c0c7d04241200400070381c0989410340c1c200783e038010a5502c0200e0f8501150403901310000070111038491b5115901620400d4000c00783d4003000300b0000030032180902c5024452801800c1c181c0b01030745400304171030070a50010000500412442c1e41c0340703030202c00e050686540942042c45002c1d85861103500741c5000c681180000501c5c03050700b8954003004088520401640c0c400c1044c1d9690f034a4440c0c641d21030b03a5034068000c0aa4000e0300d9010100c608c101207083d40076004040105121400243d00746c25503005410076075601d90001081004d00500b4040c2035040702042032a02c0795005400c41810360b2040d00c1c0142401c02020420314055607200350084031000014501351095500e03400c41072034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 794185998 1250 794184748 794184763
    0x50d02040608101401090b03250e040c0509100c060f021207022b1803020405270d02030f49110412030c1205090328110102011d 56
    0x1070024940801041e8900c0c2d0300d0104c5401d00040e11a107120a0a00e100c01c286a0401061400c0b90491003013200c48148a020441440007480d4951300d0344502c84c43d0602c4251072800da410000e0040400008000b61038502c803141d160b1886140800012403a841c112001c2c0614201018403607001059001c02401c1502015005488030b030201c0e1285000c044102c092150254510055040c00131200201c0d20b0080b00e01075940354400b8020100356450b940024115001614803010380c1101441c0801184254040450120120001086003130380e00f02c0000c7d90380c030030710824027090b001c00b20780410518009100411583e905840842030600c82c400f13065004040030f0141801003100080d2a0f248600d0340c45035031a03c0c600c400c0880e02e01418103a8138881001c90000071410131440446050103e00f0220b0f85000d980384c11346e200f99842440e0010140b070a040180c06509420031203c0e840180c0c501c110b600c24a840c0d009106080109a280042c0e00401d4558113410341c4442090382042070000108050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 794187248 1250 794185998 794186011
    0x2010507020d03030516020f0312040501140415060e0402030d1407050708030d0609140615041d0612030c0307060b1816030f0903020c0f030703020d0c080d03090302031801050d02040608 81
    0x2031a106d060a0f10482e91804904040006904100908450b440524800e55403041c002da0002c521243c031140e00368002081240c00351801400d024003e000c104135401034a0042c2401070760740342a03042c190002034a43c40d160400740d0a110042c41d0004d0100d90050581c0c0c141900b00d410782c0c0031103965494182e1260310440c843d05220b46132400c0400c1070500c611524840710458450402180e84403000e1003596a8040720440c61040140000281a251482c002c000005400744090150400f481488909401421402a10f81050009002030030740082a19182600404045250080c40c40410003a100c82c6c20210920071600007041180c0d0171408074080310a8190ba02002011484034401c07044a00d4190010010307040070104601b186480c480c5485c20010040c183d51106580c1e0b400200c1d4120201c0040364003040d100420003a500c13062200030303680c45490038248540410b65400030341320f12451440c054182c03540400040f16074807840070790309220200c0c0c10071076560fa1241c5001d0080c41044684 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 794188498 1250 794187248 794187271
    0x3130c0b0d23180f030d0f06080105040f0314040b031f080f0d08040c0b0316080c0301030c0b0706060302060d140912030f0a021303140c04090c1202010507020d030305 73
    0x9500078000b022040711041000c202c81c0000d45680000355255144942d100d11030340304084821101070b2060004007842440c100d00040c0c1b00b880c514824083d03c2d2154031445150349400108800329440400b00e0145036454030344401c10203620a100340007400745410103900c81e603011040210700400d80000c000b0980c1075400c1e0200785503903012001d50320748500030b051040341c104031030541c0e03501d014447c05a0014818109030606079113034000c941c15604103d420400d0141d246054400954012440c40d8103c0c203030b0a00d00d0700c0c66055403105030010642d44610a2814000103098041c030003654001400796034000d06599440c1060301a00c2c003d4200ea0348da202c0021008004200036004c00986101078607600c021042c103603130b07034121340f10745050000744a618449e0b020414020341c0c0400d0030103038000d07610503006007900344990b0001a15102c0a04941805285007a4036030010540c0440c0200441e00381500c0c03000c10301d0b494030040700d8602441200941180d1360380480c000f01034040d00301c94400d00e042c2d00e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 794189748 1250 794188498 794188511
    0x1031203050603120405060c1e060f01081506060f191d012105040c030b0703050a050a0c021c030603061811060703081308040b071b0605070302060c03130c0b0d 70
    0x100351304c52107080444001240100400c002c181044d101401c1c00ca00c001080e07400600600e041c034241d00c40180c401c002950000c904100c1200c050702c85642c0541160002048981c001ca424a1000040544614410030b0045240c03022605aa022140c0045105001c410301c0c078031940d805860402c549045481e0582902c45460095100300300c81200c000805003514000d404003410100140307400741c01903d4005c0c0d00c0601201045500c00c01902920341d0b42c0c2c0c0005c183c542003042d03a0440d00301602c208402c1d070408035100500d03540003600010b442105500e0020401086000307a000b80600d0340020031507820300c2811520750f00c0603c0d203014100d00820807410f00c0f840c24020462184118a80140442c1c09100840d0f801d0924141c044e400350b110b0f01040b890603840b194100d84075007092004440744203400c01c2070206450400c01400060845061484c02d0945a0390042d49440c0000c1844424400c0403001134100c1302d07181e0202d4515608103000b03103400c0b030321740d04030301c2883c1d2109000b203002c00e00b4102c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 794190998 1250 794189748 794189761
    0x40305030c1e010e06150f180703050a0b032505100e040c02032502010e13020901030b0a0b071103030f0f070b1b071101170106020114100f06050d020d02030103120305 73
    0x307a4200002c50006815141d44e80501c0c070700d05038410040319070080810341c0d0250054030303510701070750200b0030441403241d50307260809d001001e4540040c80d000350346045c0300040c503139900e0008400d10860702001e034020880c546c006038600c0c0588554005503008200320b6200b404c0395000030000c95440e03010340d02480011280b00341a81d40340b04406000f070240028004001c95042c0c06109000e400d03105262105061009000103042001001003c040255001030a04800d60705032181c070701641d82c155a2203209038a4600c0005aa0107584000342030b4141c2c055100080380c2c0c1c28012920010b540300f0103291030310b003100050282a048244100c0c0c07010943c40114010080c1d00d903000340c1c1c495210a51600d1306034196501081c013242585541e041c05005081c00300d010701d1140c845800b030700b40c41c1d0000482c80e14240d500b0741072200140511901e0f610220303050040c01030820a00060b54000d007000d42e80c402c54904900f0092046d02c034184070f404d201000110811a4031200d9200360f4201307503030a00c40303901e419 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 794192248 1250 794190998 794191001
    0xe0711011a0411130b0d0608010c08063c011407060618020c030d020c100e1c05191103190f090b090f0f011202160201020607050c150c040305030c1e01 66
    0x9851a4490351840001c0001e405179000601c1c12890120740841e20558590309282910700343d100110204044008004180c01d040c110000a000c444040307441e00503a0300c684501400720405801c0003108050b01001c01a40110489296916124000c0e0781e140e40c941001e800800c03280c002d10b5032000059440c2c0c4030480590017a83c401180d040003951504039641c0c8681c1c000d500000da542c640c0c0c0075065055904540c00e00c250b03c03c540c003a03000b4100c01079104a0300d85245142082003400e21006100320318076060a90f0490b00083c80d80c0c1441c485d1441303030720181ca24602841000302e040001050100c001207510010740f048004481d1030303255259071110750200c100d0056450ba00d42001c0c4031041c6c01c402e8540000041d0549006050540356240301100c43c1090740e0000a000ca10800a41504011540d04002c3c2130b40c4100146049420034500c9401280c5402d150000d80c405820302c5404101c402c041da20031500115841401c60f55610001c005181d1a540da4151041010380006a00d85520300c06 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 794193498 1250 794192248 794192257
    0x605041209030305030601052a1e0106140f1c0501021201150f080a1b08010e01050a24031d1f06141c0b0112061112010e0711011a0411 59
    0x5840c4c240c11a0368000c011a1a43c00601c4107440b607100740840c03803c0710008000d2110714801d1540c0036165004099061655a036014071803040640c1c5445010003900d200d2002c1c100c122007007290b84010105185002034100035554040b9040040c29030021810404154000c006041c4180c0e80b81c0020b07070740d40c0c46c3d42c0702c2d4480134598040482c0d403800c0d503100c1704e81c03242804a510018459002610501d1056101110400015254040f88080c0010f00c40300c00703402002401003a0882d2004ac91508000c02c01c1d010041440d40403507a40c103080c4242d82018044e07040b131481c0016001c80e412030007000b0b030b202a684002d81c00c1c040260b5540b800d5803070884503560044e001a101d0780400640a60000720034048000d9042c80c4a550340700140c000784c0000b4800500d26802406041610140039405060210843d8401003032200100c104110440076001c488440504690a040c000151070780e032418191903a0280080b4440d49510709840003003070600d40a9400c01d42e00f4140e0341044a0f094070580c0603540d104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 794194748 1250 794193498 794193503
    0x13031b05090705070303060b03090d08010e1315200711090c090d02030c062809060806010c0f0c081b03160e0c040f120218070c06021b0703060504120903 67
    0x720005440b49005400404045110746030001d000b80c1e83d400e88100039081030751190000d80100303004a030890382c440200c5024003490007a002d85400c0c0020401c421044a01006201d4214207140e45200c0000da4001c0410f03000c00340704604400030380015411168043c6c1001c9500c3c0d5400002150305040c903e0f1258407803045148882d250564030401c0241c00900c52408903818440ca410180d1551100b001030810524508842110440480c29003511b803145400f81c603040080f030391000c0001c40da002900ca90050408c0c203040c1012035107030030003000103050031030701070840b42c030700c0c04002280040026041c000c440110015400e0070409010175449282741c0032807400c2e203407110703034207008001d00a014290420b140da84010715003641c80c03a143c00130903107552212a0038002d041c955010360528800b22090700000141c0324245140809000d005000312040240100750b010541ca6800c0d010803400403103d0341c0b5141151803440d5646000300290000b00e40440c2d409812581044160f40a400010282c2e913 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 794195998 1250 794194748 794194759
    0x216030524070c080f0903010e030301081e0312070302042304050601031e022203060b011b0b280e0106031401050408030112020d0f030f020601061803030e041113031b05 74
    0x1080f5161303000709800060100441c4c040801200510390380900c5182140c0016402a54072507140205240c1801a98441c2002014441e0701407048e204000c000c1311041910710451160315200ca42d4210002d0040390082d09000c118150101d0640340456500c0d51407400844052145a5415004500382d9407000c0105a5101a110b000c2c0203102e140d401502d1200e003883c4150190314080d403c2d01414050350340c41521519a1258a2659541d1000f624524a11002c030180d2811011b42c1d11306034102d10051520300011a0113041d04546008600c00403910028407205115446855a41074000c0c04103100c111114404514860300583d01030180c4d520454204801c01e00b182e182c0341c284941100c01c03d00c126840070303d421300780b400075164203040604140660390f4205c01c40c0005030017915006041e00502c1c10b201c4403003200407051601d50036010940c0c0d41841e0000004d2400707800b1502514141c03020b41c1c800003002c1485102c034200d030340480f01200e0003501171441141c2080c101503c6504680079003508503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 794197248 1250 794195998 794196017
    0x80109062d0207260a0806060306010e0904020a0f0618050a120b07050f0708190c050705060a090911030615030417031806070302130914010312021603052407 69
    0x10095405002124011424101c3d207013048140080d0501e6000044000c4150200f68034044c107030310414a990181060314603a04d9410031070000380c4004022120644a404041c0001c0d046407209502040284840d41340b0340c1c00c060701d403400941a908102c0036400c141c11a0f45002070546400400401114141a00c0c2e0f011900349803580c41c10307008020000800d0110800070645003480388001494502e02914900e074a8803100c1c01281501500b103081c03001000403507062003021820101e5242c00301d400c1221072590301c4d0052541170710480c806903c4084001d190841203405046a080103500c9803c04507080c40f08211048109905400140c402914007680c10854000e020f03659030045820801400001c42c50070f00c4e82c0021840e000d01110786c8400030360080351100c4002503242c5400b0103418140b600f0b00c6108101038440d55900300c14400500115200c00785540528024080c0594100800c09008010b9480e81001541c43c80e40c9102c50443c540d03031000c01040c10741000e12083c0201070958800005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 794198498 1250 794197248 794197331
    0x30b030304180528060e07231608040312020c060309030a0507060608100b0a090608150a02040806040b0108161503110d02040303320a05071b08010906 66
    0x1404000c1c01c0c48205540155130000808240045905090318124045411814035000d4a1207543c0030f4400c81c144000000d46402c080c0d805840340e60380300b0407082c0c141c0e02e981c201d510348440b082850001829040c000a400300030b001901a48099100540c2c007110500901c1a083c881984001c443c0020349800600c1003095080c81040100062406841c011a86a482e0107205041070f40351802000400d60380d150664250030400146401088150340800c100c1d0b1800410729212043d074501090302c10440c8000a50b030200960540d0090017601c8201e4200340707010326001100400c280a4031805110300020503180c030540940304402d40e41c40d0001e4000709082901300f5400740404458041d0716110501c0903488400d814805000110301a58480c411389455260024041154510000307094920080d5210306910700411512154642d15000e5070f9048141818805196130094030411305807031000004001405421640c0d115010343d00820016026803000c0d410b00c0c1041400d41c1c41100700c1d00c0d1a100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 794199748 1250 794198498 794198501
    0x110a08060f16021902130e011a04020a140906160b19150b0d0e0607020c18090c1909020f07020f040903120e01110a0c0c0b07080702121e030a030b03030418 68
    0x80c961004c2c00001b0501600800242681c0c8004241000c40e035465510005003c02c0c1818001d03002010b48045142c4500c240000307001140203030182c1680000050050415202c6004441541e00201440070f000065864118000c01d0140d600e800d1403d550040d41e0030904030b6204041c07080300c1c0c440b804442a880c0001ca0344054000e586041e103000e981c0c41200c2000710741070048c644110100e5000d0050380e40e40b6020441d05220060440d2200d007105810002071110020f2002e9400c0801c0311031002040516005044001032604448a15400480c04000e20421308000e4280207200b250201c00741c080d01d105110890380c561030041d00041c030040307610802006552166840d91400304c00441d50114250b80151307140d11040e091000103a003a891801072004901c410806003a6902d83c81c3e18140c0107840b106e80c103010307558019205000308490301c108501c0c10404150443ea52200b05404810700304d0415489070444150301c0046070a00c200c0c1e4030f041c40c01004490a0b508042ca036610700e0070060110f5070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 794200998 1250 794199748 794199793
    0x41815031104021908090709060308030f1801060306020d1802030a0b0c04030b0117010c02030a0c2910170a05061621090c0605030705070f110a08060f1602 68
    0x41e0041d600b00300803484c03d04201480412500580c898110360704000c00e07410302d040a20341c002209985803c00a100042c0400b044a41021421a46032016210403204250703580d044034000c420741d031800200008200a54018040e80003150b802002170440c12040400d4043c0f900400031340c0740e0480410200010fa21404c803a41141c844100f042c1002e450740d407980ca03040000e80042d0044e4400c140c410b03c15040034005c0078072100640c0702450400c50b0060700544034040010008001c0712254a90510700760f500b120080007050b1040c15641c0900b400101c05126160500812801950802001209400001341034182503448401040d684e6120740c030803c4a84a170603106000c0080b40c0136080c0a4000160300c002000759080030004500d901c0d880e110141e100305500c0b00080c00001d0040048094010702030724810368018010722109180c03071900002182c0e00e00d0103c0d81c0024400c9000c5502440050302030b00c644880c0e07000d20040c0d01d131201c0f00d500600d13455074008010f038003c182d15845480340000c2c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 794202248 1250 794200998 794201033
    0x5090a0504061b0908010b0a120b0402130f02270102030414030111190f02011107081b01020307030f0b030604170a0527040c2d0e10020304181503 64
    0x10f050a40308941c401903100040e00300000980703002d01404150000c2c0b0079414600e100300c614000d114640120407040510044000c0d00000300880050195181c0020a0f06465108101009444107120450002703401c401e03141d004203106507d41000308451320780b00314802c0005800443c201441e2464110f050078020486503015500c0341e641102c1c001d411b0010300300c440e018100000034100507403001042507501050300b40c21a8100f012048031034500c0f03012110700c41d403c40e4100b5601d442e00100e00c50b8800d24145940150340c400010484065815400304210002402c0240325200e6821304140e07441c42c0c20303200603019500034480c0c08a011a41c2c8001c3c00c81c40300604040b41041007881c41040120481d003201802c3c1c449a507881c03d0185443d1203020000d0038a418204150103250b400c8486500003035001695913202c200301c0c0c040090042c805070780721190003003040d50b450a90356402500c2c0d40281c0f14415071401d5050780307084c1d9021940110380c1210082c42c0404011841d644903000031515800c0c42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 794203498 1250 794202248 794202251
    0x806120a0b07050912031312110d05030c120f03010519091e0b01020f060f07030e0f070608010e01140118030807061a1806123a0905090a050406 63
    0x540c002901e071100d07032840340081ea19220f031580c100e00284640700300410b881301183d4101700044d0a020002c503100c00c0942c0c0d01680180b411740e1180c03400507403241945040b15441174121629508001c0000000c148e0703030310450203603008000e103400c07015850b004241d00c46803941d80c184014071050800490050340c0c40003420900001a95510300309040710f00c202c0c141580390341003402c403854804082c0030b84032050800b0720050850404a024a54940c14098101c0d2600000d010104840c3d5110b40c2010b9402c00d0300d0400d880860411914080d80c0708014400c400219a48000005240003c0204c082c1298240d442c0351841141010044504192160203490107144043c0c1c0480843e40a0018000e40c3d031248000041c0321940c02040c100c150b11901d201803044d030803100d620300400d9a068001d41c000f08107030b800e540070fa040f02020f182800603e041c000401120104044554061154282454050303c0d110140c940a0510101c44100843c0545504600500003182c1d05400300da00c00e40e48140151300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 794204748 1250 794203498 794203513
    0x4060c0b0403230a02010b060a0e010305062202030402030f0105090d03020703091a0a1d0a091e09080d050601142208010c022409120c011103040b010305061006080612 73
    0x20060301c3c640140399050f40265004c541c0c04034480c1c0910583d4002c1d14111010390804001650040c26000d0300320b851410903172900041012601e03201c40f42040800e0000401080c620003000c000c0081d081103c06138468412420085003108040c41041e01600c80c4002512000e800980706802a6100100c11403c10107410300000d07003030040d00942804c0b4244001c29659480410500070180920440d100030481010750000e54580d486a6110003181c140f103801003000c1c980e07101c40a0400c411f0030714981c007440c00c0c00c0409040000d40002401031440c0c8400420868659500440c0d00300d071100c0024205400821500b40c01c0340072100080590038240415410242d180c13010304e42076441a69070000542d1001c2c26003038240c0700383c040320144001c01440d044d04500e08254516650404200046443e0800049074030305418207401000403c3d0350351a50680c0c900b06481c00d00f800080034401502d01d4020200413a81c8014001064030403140b059892244540702c04080080c21203a0070103075a9a84142c82 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 794205998 1250 794204748 794204777
    0x40309051002210301090e0c060a18051003050f070c050a020405130f03090f0b0c03040308092803030f05031003060b010c061a190602100b0103020c1b010e0604060c0b0403 75
    0x260340401d040b00b050030f8182c695143c0810b180940b0f401c030b0381c9940e40d504411903141c059151348058030903070b80d40e902c2e000004c2441d8402141c0c0740c01441d00f2050300f0000748419044410380641025001d00003403001011b45a0316400e04584031981214002c0940e0410740500002d807926802040e0408404c00c2043c8005840da51441401c920840045000c40c0540780c080000b003800580803002002660140c0b440e01c540c1ba0807450b104e204a0100504000700400c10455640790112008529500d01116200c3c624030042c200d0559040b0307100442c0002d9808006008051054040d0707401035600da0790b103144071801c0da41d40320b002d0306065170811b040000d038120a0300440c44501801460806986241e40d07910944400e04c022080590f0300701c1c00803586990700700011540002c01902030748100d00300280b0005100300480180c8154003641d6064850540c6039075007007901c00c0807080341e444240c031a040724902d148240065802a403180c030f00884c01d500800b0000c20240c074040380c3c2c0b0611074501303010945900d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 794207248 1250 794205998 794206033
    0x15020c09362e090b2d1801050705090607020d030e15070b0105060a02070b0a03150611010c140a0302030406091a010e01050103060b091002100f02071a040309051002 72
    0x400b005290354007800e20444603421000400e0a0b54008560140200105501c80000030400900140c00a014082d085d64600c0000360b0081c18000340d009104201e41030a40280c000946a040d10304055460030011a0080c2d0060080352010340e4050305150414100d40c0130045500e102810980500040d1075801252f5981e00c04111380803031a9012582e02d41ea1982080c000300c900c140c0125008460030044042c090b034001030f0490441e40713200040c50343d4200c45e00084003c1c240c001c020703a0f0f03200c0440d400441c0c402d0700941e146071071904040080140c6041841c049507542301c1c0f00e6481c0c880e4030007000059030480c0710342c004544c464041d10307001c18109100d66900071600c90714417013903008100034401440b80c904c480811500400f001d18040c464603081c01c8038403d0740c0c441d0000440c42001c0201008030150300078401d14000380440502000700ca00346290300806544a20001c403007540c5031484020010a84148540c003c0da016910300a40c5810807080c0301407203890810160651158405050350f9000b207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 794208498 1250 794207248 794207263
    0x6030204051513271b17041a16080a0902011409011b050c12010519090f0f0302030901030e0729120108010209040b030129040603050715020c0936 64
    0x22040d055804100425444205c0742c9003009400c0d6680d00d051042070244d0f2010f0030b40700c800c088100e00070441d00e0324a0404004c0540742143c10103201e4a03c108949a9140001e5145e020340703545034041c3c140e41c0c0b08039a000700c804410000303010540c4c46103080001920340021b402410740604020a14488240c104a00c0b184864001c8525900602d2405601d0800d411240340c01038030000244070380d0030541d92861070300c141408141102e0399540020702c00d1021034034980c18165000203c0256071815410000d480fa804001c50354003085c02c0c01011510030710005940700c2260040008a102d078042501c8420f100e42c95140c11081c4d940341809004210200c0b81903460082120000040e40c43c20100d0034001618002901544640d2402407800134003a40030707419601000c1c42c0c00001d00c00780f01c6800020b001300304640000d4000d114180001c00c07000c480d0014004800259001c881c5c03038040317200c100305400608503001a1000d61030108136801c6072742000500c4c102d249080181412010a540a0b89000e05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 794209748 1250 794208498 794208539
    0xc13150e0108300f0a03060302180103060b0f0d060c020a050f010f0606080105090f0414010e0a05070f0b040b0901020a0f03020604062702190510090f06030204051513 73
    0x3000d400f84200d4258110300c0f5011410341e0f8641203648400880c0d03860090991108951134009080001d05129900800240d40e00034071145010308010b84807850001c090000f15101450254001140e1a0a8011660070400240740820b0b140c000d560300406420700711a010250b104502d02100020400e108402a14004c1000090340340346028601f02a1074840c1d00c20010310a15400502c0691034203003840b0b6203d408901c007410280c54034649030070030840c40025082e00c1c1d440d002c0c03102c038600310208014500c203008104650046489a4094844a0a40c450400c00a00402c000c0180784d8a0002030300a100301401a01c02c030a6880c0c99198007603030a0b0030110010780110042000b049103a2050302d4031454032143d5103200d544801d13842d084141c80b00e1800392241741408504c0d809003201010b2007019003809040480c041e1090303480035001e0390030313030041c540303c901c0c13614001c01c10501c28404d4508842c0c00420480c074145038146c0b80041603100c040c4136046101140340c0410701c0c0d04412154059040b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 794210998 1250 794209748 794209753
    0x201051e19021506010f0305060f0909100506150403020d08040f141207140d110406090903170f04080f22051203040308030615120403021e0c13150e0108 67
    0x105401000b41000480303d41444994201414040c0741e9a00c400c0c2d07080c0900c003c0c00d001070241c41c0d9100040712040101a83c42d48022004c00300500d038000402e0982120361540410b101e26100c030010882990107401d9200c00c100414041007016103442040304d20300d240103c3c0703070030300e06622050350b9886500650800c0c41402180f14811505040c5149008024824031018003000c0307041510700c020315840742c1c00451041030b0000301c40d42402842943e840015000038402c00080d9541d210540c0941011401940401c02030307e03501c203c0382d800520342407003100301760800c1e009580e86650302071590b001085049803082090200307117528009002c800c000d08060020840d00346243c641041026203103000025060b81003800104006000c160540390003082c11074403a255034000c14914040d6000c8c800d9100002800c050901080c1600456a402c0e40004401b40c5000c890004c0501592120f40804480c0c03c4038013020607090011856010030f11890642c2c00c0c074504141d0310b20018901e0b21083c0c0000110742c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 794212248 1250 794210998 794211037
    0x206120705120c0901080916150207050a090f2306010c061b020106031e0305090f0118141f02060708040302100c02061806010f061d0a090b1212070201051e 68
    0x661b0000615580500c07000000c103c802c81446040f0000049031154034543c000b0034018480642c024041c42014250203440c429000c2e9680d0403001c0a0035600b039044040d5441c002e900864550b2003d02030f4043c2a580300d8807501078890400440340c01d042400150f070000d568001d980b203ca0321750b00500d01240429400800d09034118140030700140b0000c041024000d00c80165100000c0e0018196882d01c6402c07101e2140d800420b40c0140c030040485e28503611035150000d0003050700401c41c1ca00200b00e07107080e120000f0006032202820b550720100424080568044c1002031944c9200303040442d841442403040d103082c01d40790811801074814050a060141c0c104108010704440303020a2002410b05060040246501d00b0111000310b007400d0140d0301c00c104840d044544848081003084240d04405452803801d203070740780d1400000f4464191560f201d40c5100f04940013005002403400c9100042c000c84034074000300c5600550301503200304000c003106107110b86007560701d60051020b0101003d10340d0400145 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 794213498 1250 794212248 794212267
    0xc080f07080a0e0108272104140102010b012708030c0f010f020304030f201c0f020c0306150a170f07060f0f08091c1115040206120705120c 61
    0x8000b4400d03c0ca604000d00c01003048211520910001800e1034038040401c808034000400c03034100211911001070742140d035514510030305100c0f00184103c99a01c0941c041e031020031001242a2512280d010f800508907100000020b00d5000e0312124840a50440b50340441d5154001411608105200d24a541081460b8503101100b800b60880c0a40c50031360451440c90599009011581e040c404001049811078490700c1c0e2555032007408030a802c04408441c003000392240c24540c502e007024030303200009240382c80028005000040940385000014041d0819a81349603850640c2c800c0601119408204600005070401c040065910320094100181040c5d040010940e4a001c4141d44200c00708088500071181c030300c0e0322180003d02080340e071030600180d4030b03801e0303a851411604941c042070101c110451025600d405c0280003000d24100c1c816200c6040340f182c1491a800403c481c041d4010000300b03c45001c00c2000120b01ea40030003a42450303414200b035006150b40075101100c3c00394014000040b40c552 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 794214748 1250 794213498 794213507
    0x3080114060405090a0e120d06050a09200c03040b030a0b0415081c050405040c09060206010801060b091212120417040302220608031314030c030d0c080f07080a 70
    0x1540c6401d8030007525091a0070003007500000010712420701c89545070410004d5072410301903000d448801d00c04035611081010046c2e40101114030a1340c1c460350001100080346402409060911070001c4403020783c41003000c0902d0300d554011104a030071360004001c0410740e0b0610b503002c1c50042c00038203400210303203604500b80002c441c0700100105d921000c804007000030b00c00001d03548451608200401814440b40001034500b030181d5040258440e08162289240c207078480c550004445080d400c07034045076070316280c240c201c8074180103108140b84100700da8180c40c101030800750b4410748101d00700d5041d100c03104400f80d0950405581040d20511501c14170082c0020b0b445a90041880e4010443c0f6040c6141e0005048101508131003004903540f0503070005085541e4001002440040d05990703407041e40701c3c034100f2038000c01c0c09030703210404175400c00c0b110600300090a00c18600010700100140c02c80d0600945042d00301c3e020441c0c80190811401c04141c0751103001d01a000d100d1084030361541050303d4040c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 794215998 1250 794214748 794214779
    0xc0f07090b0d0c03110415031101030c0302041d040206040f12030306081c08090c030718060e16080c0c010f02071203141302030703051b1206070206180316030801 71
    0x148500b80c02a0420302043e000c1d01c4200c1141e41c448003c031070511400300450701034502400050221070b5002d40000c1440860b00b1b03400311400c403d0703078104510045030000f0b030200c1c025802620060084c01d04043e11090034004440d803c60b00082146003070a6407058050744114098000b070b0f5401000000c1442059054000c0d800580070001c00303031845020000341001400c807100200b00030003140801150003500c1c10700c40e50402078800b40507108001e0b01c6002da144007440910366407165900e4401c0c002044075980c0c06c2d80b401244080801c840c00c020258040f01d6185000e1301d01c3d0044030040203e80302ca01800d214500c0011581e41000d070b19a4500e080c02402603103510800018141003c515140740480002d180f54082d600451495419030107001003890b04043ea00011701c50f1007134030700d50f01c54042d801ca4220710100c01111791850500322200200c0d100c0000340d03a030b80090703804800491102004484101c892030601070440b81450111440410034080d048425004501160018008209008030a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 794217248 1250 794215998 794216021
    0x3030e0f01060b190314070e0f04061404020304081201030c032a0513020d0f02191b0209040218041401150503070905040302031c020a0306050f09070c020102030c0f0709 74
    0x8000b001c0c54180c50b1103003485070703032000342085010365550400c1c00d01960044c282400c41d201620344a2609600140c0030500e0030b08101c2c821480c403000c00c000b6151601031748050700c8164018070000102389091001a42000d003040340d007024184a5103150345c1044a5050080d406005006142441d40c00c191140c1c40301001c0040d42550300c001424560403041c808801140d00c1a2041c5040362003e010640c0240940031248502d0760034201070320383d050b20f81d401502d40c090220400b55284064a001500c80d602400a04404901551415005807a00713004269201d030001d4416030700c048041c6283e01a05008075012602104010880c65078400c0c2480b030721560f2480d4040c0c3c01c1540781404c002940d105042e00c20030303030715544400008040510902c103441c03480c0c1031030307644050007040401c1550194121042c0000001c0c038006000586140c071710a444051103000d041401540c4071208111241c542064003a41503101c2001460b06039082000148014641c484c041c200c007038180f0400e00d041d1000d500c1c11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 794218498 1250 794217248 794217251
    0xf02030103020d0b06060d020a090311220b0402130b070515090a0209090f01060803191b15060b131d1b180307030b040302061f14040e060403030e0f01 66
    0x140700684401110f83d0300c0720740110000465540d07400000c0d400d881100030f142a100e001092200c801a0070804c00d42c20f0720310a4144200741d00002c1c043c03020b0000181c14043c0309052820b01e108003400c1541c0f2010300d69030040e001514088c008207240b080440035501000460304006034000a225003400a42c1000d226000002040d04100c00d040e41d4500800300d01070320540700000458014603007001517100ca46c00e000300911440742ea076180aa12a003041c1042c0090400d0181c00390f006a00c210315070b004150313910045544501d80c94490314280b610a110b917842803982c980000c51041c4c103070b03c050f000900c411003207406203074204445194024895100e401560b0708030003d00c000842100b20200050030484009611140c418000306004040c0c80f000030f4041c024001c0220074864404501071050380a5000c0300c4094580d4064010a8001407030201200750300e0f42c4e000d0240c2a01b241030880c1100300188082031590030300508900303101c0203030790450101c1d03907481c03420345443c03401e003c500703550300500c1c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 794219748 1250 794218498 794218501
    0x6081005010203030c1308070e01030b01080309010203030c09011205040b060f061c0b0315040c060813030e01030e03090a09061a0a05030f06011e03051b0a020a0611040e0a0504060f0203 81
    0xb0b0740c1d0f400301400c40901c0b148045460328500103680d500348010001c001c101c8028907928000c2c000e5991081c001510301943c1e040c00401c0c03003503000041b1a4203420680c010340c078681d030355842070256400c40742589040001c1400c12035295440b500910b409170b03001315580720003410550708000c14a02c00c51400d6008110a200f4900032180100500701c1504011401180404150000030708004900d06c402d54880c1d021000e2005000390f402003002901e2a603101c803081c5480d070744038824001e988100020000b94840c52060690b501c60f4100315400c0d021041100d04010a100c0041d00810a80c1c03c0011042d03a102810013400381c41c80c41484280c0f400203170581c904140c00034014128440140140035400c2040301141d05648501980703104a404240200c00c900100d2000401500781600d0110302c0c2039002c899002d540241e40c046070810281da800512452407156103401c007800703040a040c2c03945d038410700000a01e00700c40446607104030058080003400d8030302450f141c8104c03104003107100c403050310500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 794220998 1250 794219748 794219759
    0x6090605071d0a03080301091d060f09010c0c2a080d05120109020a080a0207080d09080306040b01051630020709060f0f1214030a020114060301020705191a010f060810 73
    0x181140d041d01d035000004918800750827103410810038055000c0c010b42c0b185078100220050300c41c850a00a03c0c00310001c2c49184c04506084a641c0d90351070000d8074003c0300403960143c40701d0503040c650040e40345145408080340e48400050511806da002d04011502c00030310085a003103910101405040c0e240011820001c1c4440e0081c000d0500520702c3d1412030b40000c4c08000d0024201c180c075012400704800f40840140c900d07248200750420f551481c0610b05040d00c10500e0b6014509a420300141092459200d8046031917040c4010600703e031450064070504050b00b500a090683c9840201c0e29070001c000192a00401800701c40705c907488240565003c690500c1007401401c440012600000401d001c2a21142003a14020083c0b03501d40c48240b00020b011111150107402c16001d801c0802800c59a6a640303100345406e074030030040010001c5d045200b150196529007080341c1d100901130011502c00c0c07207407210360f03808000c0c0a0304401c0fa000700c024030400010380e010101d07590203034403e1100c1d12840d00d0b10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 794222248 1250 794220998 794221013
    0x9050f0708061203040e0a02180405040b13021504030609050706110d050a03020d090b060f0102280f05010f02031b0c060609070c060218270106080406090605071d0a03 73
    0xc2d051601c503a19140f441d0300b040c002001135038043c01200d12410400d08188440e00002e42c400303910706880c55605411074402d460f05104880c89a03030481047c10542c0d41c2c000d414148074110500891384011480900f006020746e00c0041c03c050740c847c03000000c9440e0b044c103105103000c809502800400c03042030030b1241510408522112440000d00700103403030728607000050f40a0702400d51698400b602e800c050070107026070300e5089401500250b420b0f0161040350001240c4070521000456041500e000340300401c241e0100710010103e002e810362500c0801c480d41e4050a690040c44d01c00c14075900401400406580c1001d04803440d4458892039240a15201c1002c2e25001d00406840c07003800640005401e141c01404401d2286034041d404550300e2061410710424809594007040c041d10445241e4801060b5511010300300d1890b003100300d81c0581c80e2480496102d20024411115035484002220008070540a42c0c1d0090300c1544407098a11112201c65100590300c023078441c410a4885420404030b20031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 794223498 1250 794222248 794222251
    0x5030a08160606051314010506120c1e030f100b03070f030b0301020d090f06181a07030b0d050a1a070f080c0c0f160e240a030c0f09050f0708 62
    0x41180c062481c0d04541030050062600e9402aa0803881a8001e41a051080c0c0e00c031401850100e000d01c0001d98030754040c00094017412411050b90f0020030007140151100c07001402000a002ca030070140154486410703c0e9542007660340d2841d08511a044c00324103880c0007410b10280c840c0c00c40c10350451501300c800400c80340b0801b0140c42419540c40c84902aa20290110355080040032801d00201e071491926100011004c1c0080d94420700c0c01002248041040c54840d5000d90000325281c10044454460782000001500d0001410782d18041911580c0780c6010403082d50b401007010304010485818010302c603000311402a01020243c0080181541d00288003440c861001e00d4a0061940c0f82d0405041d0f5206405d8502141e116240c50030414010015003044040302880c640c400c103550b20f03814021280020f035600c07030b0119807a003c22070351030b17518014203103890200030b100000726956a111180d16441540040c200f480700c0c02010f20030101035001d01a0024141d4102c00e98510707054074020000f800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 794224748 1250 794223498 794223517
    0x1080c0306030a0203071511010504020a051302160804080c010206060a06110f01020f09011e08070c2901170f060601140705010212101203020d230c0309090105030a08 73
    0x32020030002d440400003c0d0200c0c3c1c0c082c1c02c0300c0e00c09894080c580320b1516400e2560303000941c042c000c80850401800b4440c0940d17805000030074040e08041c01c0103039030b0090f255100c4e9015404c1c06070980051000c50780b0040280a4000380d5034950500c001c050509078402c3d582c90641d0702c940140300707513604e524000741e086810910b0034034241641018803a003800b005600580e10b542c0041203516200b03852100401c403604003622407c4400172103c95242c0380004416095012800c980d00084a6a0050258000180c880e0009882c0a90004004548940910300c2090301307440000040c4041b00308181200500c4a80c04c1c0100f40301500044402d540c0c2400a000c03078108106200824145280202582c40c81c43d4010001e540303d00c00c9100b01d42d00e0780340480d01c040d030011101400050380758000180b40f0a85415501418143c4142c25065805591006140d100d290302031040ca010001490080e04001c10300d040a50b540e0341c00c1c0400c001e200041078101d54460f42140300e00e100003d40f07150880c4d41149 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 794225998 1250 794224748 794224771
    0x510030809040204051905180103030203041a041503060e06010e030a0609060b0d05011a10020c09090f010c180f05010c12030f050f0f100f060e0a120b010807080102090108 75
    0x41ca000c0802c020340990390010f80c100440d0a29400c03854040c0b00c4010540748181d60642d10242003030b0b810348a0700d6080c8000390160b0070801c8140414041c80030703809029450396510f01c2c640369072400801d0070414080c1401002076901c0d031341070000104080c400c0f23400803802d281c0608000401070009894400c24240209129a140c107030b0020818241c104501184000741174011038251030501502910032503000c3c6000c454082002c0c400c0b4585162314481002c1c45600503e200d261000c148030b5800005404ca0b0418403c6c2c0209048652003402403103050702255642844901c289900703410500515002842c0344044810144030030399012045454003a009001b041040b060040190700401158215551845c105803c011040156400843c01070525100d1021181d4880102501d003140500480b4541011500d040003854440c207401079104a00030640744c08241d88280c882032459034100704075011059800100480242482110010902c1d4002940703480e002200003004000c009015841c0e10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 794227248 1250 794225998 794226007
    0x7050c070f0b09330408060702011e050907030b07181a032e030303061412120c010e0706031e020304172107020303240f04020a02030f04030606090501050405100308 72
    0x4484c240100d91464146030030041075401401c0c24150158000c0c0150b00d524451100400d509510500c10800026200c150a07180c401165000d00094040540b001d19544500000400801c0e0803500141c080c030f8894549078030f0303904002400d40c98084181d03c541000e03c0c01400f0040400030000c1200d5000d242050383c040700c5c1c52000300442c0661814102d48400004461300801055055408082512518183c0d089512140c0301002902e48000714040741ca90800740351049200c0c0041302420038024540e0020400d1181c1a9400c0c0c60701c80650300190004c0e44815511522000d0745d1712000c01494151401d52031840c00d0340f160f012a101c3c01c42c820541c400009621980807030800c50001650200d40c5c0704080c1801c0800d80203590350000d43d4841d24017100035820341c2400c03008004515081c64090704c511590b204076070400c0002d42003113100d50709502081008031042107000d0020409144502d200065040c2050032040803600160041406146007000f40704109038640e040c60100c81e8400781e2903545 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 794228498 1250 794227248 794227279
    0x4081504120e0604081c090e0402031e240402150a080c090f030a06061716050d0f120807121802130e0307060203010306111905070f0b07050c070f0b09 66
    0x5522450740120f10900076030040706034000b50003180c40121b420980c0c8541c0350a444080c641041902900e0007981944100c0b140300c0394903240a1031001e0080d50406403005040001c0c46040c0480344050f00d00c9011907480c0c1000b04514201241d8180a11511030040c200394400c1c402401070840544600e60255010502c40706994624908141c41c00c0e0140c291041c130a00d514182d0f002d8400b43c0240b0004010a030b1280c0c4100b200020000259000b00322400e50062a02d01842610b6410003001e80c2c0c00410078030b0307881c0402d40041c02c1100302c2c1403940c0d0b444200d140141000300a44100080342000d9402d08039201e12a10a01c1003c2c1070480d011201420920101503100c0010400c000c01e120490201040100030f00000f680614100c0340140418016089001180d920f0340c801c045910840fa00081d00811040d8402e902070003038a032148510380c959554a840b5040c0a43c421505800050030004404003500c000340501401051000250300c101070400c019103045008441c165800703240040310f0003d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 794229748 1250 794228498 794228509
    0xc06030b1c0b07080c0f0909041103120d180b070509031507020c040e0f150910050a020a0e010c0b1602100e030703020610030b0109110c011104081504120e 68
    0x22641005000c1450381c01d981c0b81182d103079201110030070702140b00240014102c0c6828421036902c2181110724a140c01540410000c000340054803e4450385d0102d005802039440400489440036001e0000b151038641e200002000c0e40d0407104a009480404107080000601c1800040d0b0032141509266441d0b001000200c1c2c9402c00c3e40c41480118848007051004141e0081a0380e151a00280c80c00d003c40d406402c131450340d50071806629200d50740b0204003c0d856060701d1400e19001241c01e03003038501030407604030500c082c0c45054608981c161f44c001410308150381c000210420006c001c1c02d20780882e94280e260680323058001026944c003400c40b840c03100c0d503061007481380e14002c010000c03040080c0d0750315000c02d90b520b422008007107001d4483c02001c103528891a040701c0341101c0d8000d10100140c0e0038503400744003030700d0500c11007803c0d03401c01c0c041c080717910320280203003075840081803880745c0c8035480e206c00342d40b074000c150504508540e106020302001ca0200d0505a58442789400e190840d0700c1e100d0301046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 794230998 1250 794229748 794229769
    0x10605180901260f0d111002070602030f1518070e0307080a0314041203050a03141305071409040f110a030804030c0603020f0a0f0905040e03040e130c06030b 69
    0x15482846280007207126100c03910203002d001040d40800c1c0044001c034240513901e111003001001203901998240030007a00c01d0440465290f0444240c82e03141644090342c3c03050303070402c01080308c4094000c800c22048605c10740d40c0591050300c211003e0011000c09001ca200c01080428102507030079800c0004141d41c3c018030a03050b501e40c02034201e0707854a40d1035410f00c4c4c43e00c03240c050071000540502c1e07130100c1102c991011f940c25904041c0104030712800070754007900c80394020807008060544803514141c0381d2600b520301c1c41c4280301601c0503240f408203503e02a400c0040c16081104805c040c10300c00da00d2a140c801d88650b220368040d0002140c0c07280e40c101341500c1002544015031100340480b010040040b800080c100310383c802c0d40d840078490384404099050b80910210868943c5007440b56020003481988aa0450b0280e801c20300b00580e00c810225040d5002e07a08403030b0140d030000901300403070050110000d600240640c06240144070f182d4501c12031640c030f84030342020182ca841518005943e41d28850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 794232248 1250 794230998 794231047
    0x90406050711030d0501030b10362406052b06030507031b090b06070f150608010902010e0d1119150c02010e010c02090a020a030b040608011b1106010605 67
    0x10f03901d921030b2007601d9019004c24042100c03501c6031240411940070b00e40107030000351080d15544c00003203252408010000d11070485451044205c0742c10100c0c4640052180c40d449003e000180b641c1080410240b6002881503130201c0d04000c810050001003a00200c01c0340c50000f4000382d049501030400461034090f0141e504007400c14061544004100013403031040402c10107420640e4880a40d80da2020b00484015007801070700000c081006000040d07040341c81c506214424050800403010044c2844202c44580d0070a81d146d83d0b444030314006640c2c0006800304059001c49004403550480d079580c120090340981507034040c1814081400c40f40d00c50460110290500003803541101c100c80000600d00044074034140e011500d1031800707200f00c5d445040f60045060300580f0403030f01c1d5201d64030b01c00d00941c0440588001c01d9038070105451550b0b214061840140340040000c179821110034000900311012481d600f0902c004192040744000c40480c420303044440c03d00b4150784070640911075900c03105074070440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 794233498 1250 794232248 794232253
    0x30c04060e071407120e0102010905011b0215100302040903090b0d1b0c111002160308030702060f091506040906020c07230102100c14030124090302090406050711 71
    0x32038010070a5035a248111803c3d96154214001c469150425100e0000301402c51a40d80c1c40801096000d20268051614180300018065a80c1e8440d5801c45a8071141d1000041c031007083e071000d943d8100b02c0c05c0c3d001450b2514060326800c02050a2401248034440240550744a903060b10500d409810f02100030950b04c60342c3d0740d03504607091518006160700350451594840300000400c80500c02d0f00c409000542c842000ca0951365000e0422a0510168806408610503141440d801400e1042c4030340c011440369280d00c0d101d040080300641083c0000b88042483c00300d00007082480400001c452010311590300e40001c19840c1d000100e006001b601760b0140c1034600000342c1c1c411505001030000e080f034042c0030001c48050380000320014020314821001e401a44039050112514030158400400501d0030f08003002184403c3c2c000102c42d410990210400701c8250b03510805010b00c1d030711145800450362400300c440e142950700085840d80043d001400c2c041e620b00002d614a8007408000f00e110f1000c00c03c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 794234748 1250 794233498 794233511
    0x1d120f0303011802040803071401020912030c15040503071b1a070201090f18050a061509030c0f06051903060521071403030a140f0403060b0315150f030c04 68
    0x829680c1d8028450a0012010500041c1d0090114820781d0700fa90f001c80d02031480c003007082e11916090441c00d40700c0c0c149554200481662950307400c0c5c000716443e802c03001564480210701009401c0c081d4144c081640082c00a04000c00120003004403103006601c40006003d900c05022a404213410907040741114585c0801449200d01e192000b82c44034070300c01d0340ca2202207929140e0243c40c81105106006901e8085a421780040a40e600007e034440304210b0001405691a04070490490481c45054040307084040d007402400309810344c100c05081c1940c031001071145011030042c601d205042d0075030041c91007442c0180f0313414030940000c001014000c1c400c09049800003c1801c0c40820009100c41700e00c80c003c00081c000010402d21721007281c00401440c100742c4001c0d41911b4803041a40d094140715400c0000041c41c41013035002d003000d180250800510203210324141403601c1c107941da2035250401c81030100084003907150300300c43c40b5803001d40704804407601d030704042480d001c0d00a000c29031090070540d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 794235998 1250 794234748 794234773
    0x60308040305100e19060902030d030e0d0c0305030c030402010c14100608072d0e0108010506010806010815040c0c050703060b010f090e0705071a10050301110a1d12 72
    0x6015005036801101035030b540485803c025022907824280340121034001c84800102021070011106900c0c0c0904008503806102e40c1c002030a0070900b00318070011030b03900c005002203110200602c0b00c6080c12030800e03440a12a5803405002800020140642440000300003000c692282c401100c10341c1d031101c03070400101c1c80f00300a00c0e11002044142e82c4064503003d0f00041441e8002044800c48070680941960b1b14110340c1040301c0013203a0b56a1801200103500c00091900541001c0340c000c000c80400007841e17040580005091481c0908541e0410003500140904140c04290813000e22000b2074000070880032041007600e072041180400785c802d01a0200c000180091900400c50000090717880e014240c0502c401618810480d02401c2066400500060011400f0310000c240340741c01000103006121600c1000078160a040320500381071000c460003000726040900500c0342680d001c1101c03d0812008140090100500500c1c40c0102c1300e50000a400d242c07542d40e845400585d495040c0da200100b01d5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 794237248 1250 794235998 794236013
    0x402030a06080a121805061b0c0d050106050f01050307081503120a091e030c0918020607060b0108060618040504020d0605010e090607080c0301091505061c0605060426030d0603 77
    0xf04000c0040340d00c0c0401c080000d017241c40f811060743d400405007030504520342c0c2d62500c99500a900b0002510584480107110340e900e00000c0f49a0f4800c0c000450322500b050305210400740450b0301d032414000e092060040c40358000e044036034058070103903d006100324030800107851315a05058001c003410000170309190140d4000052002e4880da54010051114804400d001111072484050207402010000784040301c60360304075901c240703400714003001c0740300742500001c9403580b10700c00c111407103540c1d4061a042542c1090041d58400d81c116940703410880d032100700d585482e64500b0304511465445000604560322120407002490300103404200c25070311031a107900440b00c1a44d01c02c14500c0398a0004148034825121244210789100115055910b4031700c0031405020b10180d50845140558004901500c6a0029090a8114081c50228900d001000130100c2d0100d4104902400003000140300c1408140c02f0b5500c2c844a50f0b0221005541344104642580070b2451a1030003542003850000622114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 794238498 1250 794237248 794237273
    0xc0a0b130b060306010e1807180207120e0105090d0206040b0f041d070e010c02030a05010903030f060603020910051b070306060302040c02011514041424010c0c050402030a06080a 78
    0x1989110006445070310030150b13121001d01c2044d02c403900000010705040509801e1030002040c4604890f0035607220240038050072445071400240c2035000c1544000d03c03c4144603c01080c13464142825000703040000200140314100c501170140702140c09260442d200c070000c40c0c004044141c004e0342c42d0f40c1904d00e00200c55000348901c450501c170903c400b00210b00461081401143c8a8a490f4210701c1c0080c010764040001200c1039905000d00300700c0318007143c0700303000d1200514443c2c2e90004110901ca0380c800c0803a2821703009402054414002c00c1c07038640350601140401c2d83c0c1418080e8a4183e80e000d1003c844002c03130011102070151100010821007242c00c400e0507284212401d22940d00709040485c00c03120341e100c007641081e00c0c03010100240300c0c0039224a050080003600204215603045003a103140c480680c0c00c440086800ca1492040c1d1181d040f003800500750034680106100c001e030311500402540e9000c0d55204030350010204a1066466016000070941801960f038000c08900303080c5501c1d40c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 794239748 1250 794238498 794238503
    0x2011d04050c09040e070b0301140a0806090c03060106020d050d0b030106170303092103070809030c0a0c08070920211e011a071707050a0c150201200c0a0b13 69
    0x5041003401700920104036070041e0b940c0400b404d400c0d07070f1800506d20040c1c591a41c0b09504040724100209040304241f109510070b0006500518499a61900741480d0683c168008011500b01d0248040d429600c8011200c28440c05400420b1003c55140000e00400c5035030700c04803100d402c0010840d02d104c80400074510039001e05040c0d49074104600304007000000ca481d1503402510040001408182c0542d2006401600c41e804890030045c01300d05452924664030710545654140c600d08000180d0b04101800140686143c2031000441d01c0120341601c0d0001c081502d1350b140c0106022007140c1050050262032207000d0074410060400c1c213264030010990b07540c042a6643c0401c0046000030346544504401e5180c82086441c0110302d490702c410b034410750280154100d0341000031701d0201c0c00400030466884d0060068588443c0740c03c008c103403d50541c00443d403c0d64108145101860251403180c40407440c8200415070761140c040c011820070210388401041c4150f000c0a210119000000b0b0300300403072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 794240998 1250 794239748 794239751
    0x2d040303060b090a0e040c031e1401182409080301061b03020c011d06070303020405011106011203140d0e1b1905011416050d030b0d0f02011d04050c0904 67
    0x1612410b80000901c90021a103404c0050303048200860740582c002264054010410440180d44035030f500d9011802d02c014903043d114100c4442014041030240c40d04080c058900200301020f8814448800143c3c6000041c1c0b2412001ca802d043c03c1d6240a04a00d00e1021002c00f000ba0403080d01e40288150428040c104c0058803184104503607212000da44190342d9010b400030030842039104011202d0006072a405030f450382c500028805a9100c0d074015005040c0301e61001740c2c569041c400010616640310201c4400350744013000403c0b001d141c01040364101609447e002856010240c6030100e18807500000c2040c1615081024803c0940890a464044908075500c00251488010000c40d1111681d12401511445208111035030142d03521242400b42007466904050701000e6203540d00c444001e0942d00c64101581c5a6552513042c8038004540c0011a18000c0c01003098a40402074074100500a050241d51410509074050701026200708090040080c0040e107042082d000702c33504002c0d200342c02076 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 794242248 1250 794240998 794241011
    0x19050c0418021b0a020121090c0b03010515070b04030c0f1b1e030312150b0d0f0f051320030d05041a040503030f0a0302190507151806052d040303 64
    0x19402107404102c045e016911007001c0c000c44903000764521014000c410074565070319681c50014200175080402007441244984d01d80d8074010a00944028450142258280402940001036980034000b5045501450040d00c180071501d0716540c5680700c603034090800c520b8600c00041c1d491150780d100c07059406500205003491050780f611030156103540002030108004000040da010740f1a0302102005681c2503200d50070958800355840700c0e60202050314a9152a051020140701003406400c900c4151a0000c001c1072801000400d0740480c039a800904d100100c01d450344030103c0c1c0003408200014000c1c00e48481c0600e004001d44640c3c070500c13400703035464001148400b1842681c0d00b550704540c000b0300a1868000c1d1078003900240c1c0e0014880e203050582c28000e59014070701100d481c0c1c40505045d00c4a643c0d031035480c00c02c041030104000744980c0260910301075095403d040192aa130b030540c00f41c00072075280c40300c80f078414484124025600d0342c00b540c030412000c0b1008460000c0c0c0528007944081015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 794243498 1250 794242248 794242297
    0x17040f021c11040c0e0f0303040e090312100506031f09050c040602160302090705130305010204180f06080705040e012a110c0603070804140a081306030519050c041802 73
    0x642e0b03078030b540e44c0703000c68022850802c00e070401103a40610010000e0503289011703128062000300001c2901d09110301c0c0e0000c2021096504648100b030703040901507101d9a107062400c400103036544402082103989850030b5010606213145c4910540c054500b18000780960314203d6404170903074001c0c4c481c0300700502c1904c1904c86595450030300703001900d4024100040c1e40c2c1d1154001d450381d0344a8100113108000c256800000310340d080c800f4001030210030222202104084003081c00342c0c3e1002c401d0420080c0740071010892a0400108841210b000b039a0100f80c01903e04041e5005040c008080b403112803100420154a81d46800340381c1502c1682d0b140c3d10025550501600d599950814040360000c000300007046400c1d000340d0110354031603c00c845c11914810140c0401d400c0c000101000c840059010905c04411100d42903044060240e03840d0802c000d260005540c040381c0c03d4440000c0040f03a5030408280115520402c950240c4001d45031412003a1101c40030100a501c80592100c4861210380311155 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 794244604 1106 794243498 794243501
    0x30b0403020a05030720091005040b060f030a051b07050a030c0c050d0f2109090b030111030c0408150708040632041e0317040f021c1104 60
    0x3900600e0710403c11180b04c5601b540f9100300e00795420858030034004070340081114007c940c042211f1074003401190030762188101c021100c1c4030000400030000e9a0f40c1000703000e1804049802c4000f200d0340d500580501602400800c0360b0050b8440b580030070700c14180810814010088081140e03681c80c0054464484104211031b40300e0105450428080e0101081c8109422004404241407405800404094442c01360f0032550350748002070030440e102540000c04c8803120f02c210568a0038102d900150a0f00030340700f200307420311030510300700340c0902c4101c00d9034000e240d035444054543d00d40369034400c007400141032413042203600c0141301c4505800340b41524042d10440503140c9500e0a09080840340c21a00404480240ca8070380038400c00203500000c1d840404002c500800010344503860071607541c0d0018500170b0b6000c0da24403032031641921140380c1c12152074426084d4450407030b48c9509010 = true := by decide +kernel

theorem cover : BRFrame.Cov 794064748 794244604 := by
  have h0 := BRFrame.cov_init 794064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 794064748 ≤ n) (h2 : n < 794244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
