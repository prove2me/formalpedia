-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3950
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:34.849298+00:00
-- url     : https://prove2.me/submissions/0acb0670-e78e-4a5c-aad3-bd3454a326ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 710251798 ≤ n < 710431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 710253048 1250 710251798 710251811
    0x3020307050c0a1505090609073f0203060106020604210c08190e0307120210051317070b0f07110102100603051b01140a03020304080f030a0e010b0f0102150a 69
    0xc0b54108045140e4070b11407854203400e111101500790507140301400010540d8414014072444a10201c0c0000566200d030b0054609d00741400e5440f40c0398602c440400c07018180b03110980400c1c4020807614180c00e8000c0d42283c0c503d036600c00e0226a240c0045a01801d50501e13a2011061507014050900b03200c40075190081d0f8540950329404d00760343c4480e01202d0350280080302000c0003034214004400082003240a4010b075441c009050060880c80b1000921903d8402110013030b0a0240d82550003143e002240c8003085078480e440350f254803c0524120082d0302c40c1f000c2c001140e80030b050071181c4d1400003581090510000c4c0d9a10304000800342d1086055014182a00781c03000094480e01c00114003420080c40c000325208014500340d0481000b00381080300c841c150b0806400c0c03c2040300c3c018841e42c60016542d940750305001120780102e10508044002c00401c0c48424103c43d00460b501d4a040402008105891810040310350045160240907030400c00c0355030007034243d400f6400d0b0b101c8000200840c80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 710254298 1250 710253048 710253067
    0x1614070204140403030c08070c0b0c0c0a080703030b0409021c0501060302150d050f0105060a140c01330f14040e030a0f080f25020309030f100b030313060302030705 72
    0x2e99200034810002c000a000411060640c54002c0c00707206201800d20112509141d507006100c20b0900d4406010910300f107010408045140381280c054004400a40f50307001c00510700004940c2c07000d9001c0c1c1c0024206295543c603403420703204031425264000c0c4154160b40e0f50340742e092021280319034103a80c9075580305070020143e1107400c0da850707502d21000d0203255a1910805000c0c2220301c0a41f100c03411180300f00040c031203511400200c4082044034105090080140d13a61000c2510a101c01c602495003820000f641201400c0c2c00c2c950354040500c0d1031007940d002c40c901361545141034412205900485002000248004844607038048006440170401c0c8001441003459588a0250303034000aa202400180aa500c0301d0402c0e00035007107546485141c20083d0803000840c0340b409070544445c035102d5403000c402d4020070448520300b81c040c007551001901202d80d603898900d005040014141400703154483e034a0044215203068210007136800c9080d0400e40708a0007034000a00007000d110341005122207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 710255548 1250 710254298 710254301
    0xf280501090b0c030108070f0510030509070308040e010608090606010c060f0605190504060b1204021c020d060606090602070b120402121b0f0a0e060f0a0906090603060b0105031614070204 82
    0x30450554503c5a136a51600c660741d03180c210170f03074410001807140e94810300c126598802007144801c86454040b6998403185c442c00d0034401d56a100525051000030300180d601044594070b41281c8040d00e820f8201d90301d445003e91100300449080b8001140000c0482c0041e50a50140070707074109d00100060100c0d103400104516000c0d03000c03051895061110100010b14050080c4000b81540c0c04051742800d01d210904161444041c00080c4182049908031a0200304007100b0740030a90018440c01401ca0b8034180b10000340000d000341c4000484075000401c000d070001076003074215450550700a140c06884240d41a00300d0b0054012640541c5134070f11320f02c905d1800c0000b40c2a41385200031000e00c209000042101560316000781e58000c03645a04100544803040150f00c0d805070b4187d0303138120182000c2d40003420503c91500040c100c2403801d0004100644e071513101106484c40352104004c800c0906005550700d000841d07114404541c00c5501000d454403502d100030403402a04d815500342040c50340041c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 710256798 1250 710255548 710255551
    0x61b030718080d17060d083703020702011806171f0303090e0f010f05100e042903060103080a0f020705150a1b050303061504081506030f280501090b 65
    0x83c0094485807800c04a002d1158080da00311a003200c001c4e81c501c4030780c0d8480301c55003d880210640d000da00100000c034180300100b4400080010441d100780304884030702c081c0094001c0c0304180d0000e580840c042c0e5080340600000015255140c49040c02c0b2244e42e07004c242ca440b802080000d078003800c410313a030300c0350100c8803010302c059442a240c81506c5810075a0401c0c2891008200110424641d03004001c284a904d8440040d80e9058826010001d0815015200c00c440d510016821034541400410b20b901c0c5103426442c5021202892003c40c045c020415681d02001c5c08080d2510404010407604180504441603118010340151142c4a0ba954002000720194000602040b6400194000400d5204400c1147d031508c104c401c00d12042d0b40d0f1200780d80c0707010050403e8000c1c0c140803010405a1015000d90300102010310458000c0c050a900b81020048241c0751039000c0d2003203032292b000c00340c004100801c06060b9860710b1056580e0901d103a0501560420040d41e039950f0790810ba0f8045142403100a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 710258048 1250 710256798 710256823
    0xc0d0f05060112171c0c020316120207080c090609071107080304050f011107050402090d02090c070b07022b030e1005011403031231060905061b03071808 67
    0x310155800350805000c45812061a142c131300004000d03001480c10004480400c1410380b40000500320f21060069140d0703c03a0aa10a00c024505555402002030a02e4041144031040d42680c5000e981c81c2e00703c513076810640011660242151001505030b0a1610260f40d0000951414100440c2c100280504000c43d503002040b40d1740000400344003604100b00019176000302032816000720024401e0454503003040c4c2c0102c42c492500042d003c0416541c41c0005402d061b002018511113040c0b20180054913400f189003283c4000c1c80400082040e0b00110780800000e14510114862280710501e441e4590140300040d8141551180705c15804a810031a1410109000b00700260384c1d410b040b0f00c0c0c0410920914003900c82e42c0304218407151001007104480e000f0380005c0341500d081e8145514418102e81d01809040f1300742107025480244aa19000f614845000b04140c8030142c9844030010003002480000c81c1e174a40c8104003060000744030b4640e0300702d04000b01a100c092581c0740c0300c4e00c42c10241c0d1906807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 710259298 1250 710258048 710258069
    0xf0b0a02152a0301050d17090a0e0f1807060f030f020a03050921161119090b0d080f071115120108010b0904150906050f0406050703050403020c0d0f050601 68
    0x80d042401c1c10603407007402070020b50455906540c9040d0000d0044000d03204000c100703c8441a400034500e000c181a205440c00007440e040c1d810343c44884c09810008104d0b6004100170020b00414071110686a1300c8405804140141c1601828048280c44d0076030f1a50401041660350314042803104024030180c2881011613030080340310708207440c10b0703880d0404441c0741500500b031200d100040030100a0031540a140b0031445451a2001820315080345000d10100d00c0d0003d41c0b0f00000c00001140b0320401054401c0180d0030040c41c0001d5050021194100300c004240500c200305200114405001a000c0248507401a4a6128221011406040c0700103c00c2080311400708101010f480c010005e9030250401400800441480900042250b02d0151001c5c0080e146c41c0d4030540b02044503045622040d81098044c44642000c1c4542801002c0450702500d07050326200204050610a0142d40d004581660082c03150041081c10090040d81030041140c2c40300030180c00200240c414003403a07000380154101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 710260548 1250 710259298 710259331
    0xa0206130e07020d050a2714090a0209010509060f16061e05090a032d0f0f020d080703050c070b0103080703030e120a120e10150f0f0b0a0215 62
    0x7045030040d01030321100c01d541040582c460f540b5072080660307851030503a1a10201901c0310aa595058600000080380303100c0c1c084402007428602c0045c0c9200305007040da10351807560b407112000800c82c0190100107000810802103c0c4451621402820301508600c00ea03914080301c103040c58041d4000040200c079415200c40905207030b581e011400102d42c400503074044c8260716080c2022a00e03032000072001004e02c18036044030441d4411160f90025003091a13010421300f18030886020f800c401d4984030502c0001c2c4108410303e106480403d1000300b0180c0c0f40c40b140c1058595004c25000b4110052a00d007000c002401484003140c440311606000b18020605a81d0713916850400600703480c0202d214529907807007041c4880c5c0320b980500846541251030318000880f00b00e000d50204c0a81a50781d42801d0341d119000d5009280041d5901150314458920b00384100d4503500c2e44c180525120038442e80c12568490700c001c0024020181c01007480c0402881511008420785a81c9165081d041d1264001c6064905 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 710261798 1250 710260548 710260559
    0xe040f0c08071209241d06012916060e01020f070b09060610030905011d0309010906140403031101090c0609030605070318020f041103070c0c0e160c050a020613 70
    0x660f0741c4203100240000c2c4012485a260122189103001001d0a50710691040390044000c82d4046034a820b00c6200c002c8410b14000445644c410007030061540d0780c485015803440030500446d42e0312010203181d0007542403a03420701180c50000c0c200101130307440c0b07925003800c01241507081c0300806000c4400b1100703a4480c6540e050500507484001d0442a60764422018090155161001561102c1d44c1d454007107030001103132030310702e024207132040300030a170700c9141010301880341008030282000c20401e0344c50301086580c030b4000b1a0310507882c04d014550f2101c200014404030348111542104800000004140c44c155660359170034415079a0710080010f801400144200004c9002d001d8202621313140611480e50080e079802200791309914001d01c1445040201c891545071a00555070189507a020940c6a1400110252506420003000c82d034001c4407090100e9520726510038a4001c0d00c24580c03140602c0d0703c1000607a036001c4d007072038180c49a200b2010006e005079540d10040250540c080c4c025041e084c0f07040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 710263048 1250 710261798 710261807
    0x10e09040c050a080d110721030c0b0703022106150f071401020702190f26011a010e15120c040f060201021306081302061602120601050102120f0a0e040f0c0807 70
    0x102807140d868000400412241840b4245805045c440c123080140040c032a00e01521140c046502c01403445240100b0480e940b81c141e405841c45055844054241209584d2078800c410411545640d0241079450500e040c40101806007072041d5212425a144c0411500c6126070141075088110b0a44c4d00010203030f0071820070811213070b4242c51024040003e203051000300c000b000e01602030329024100c480910440d0350894800002250341510080100540205082152407005080705020412510000c6d08500303201054880c00c4034003220443c1030000e54020fa46a000014140d04084202400045040b00c0c3d0a2900c030002c01c0c00c3c0d00010380d103019041c0803100480d169071091080c030281c2c20800103140040c420b0000300740c1d4115609951031072403103410000450381132000381d08000c0c1000140c5801d0b50014001d41030362426021140d6203006000c02001511806602c5001c407441449210801c0b0b024007010b540424008001090912400d8803007000c40d0144940f00001408050a00c000300d03401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 710264298 1250 710263048 710263067
    0x11521151a0f031e130b060f090f090106080708060a1d0303040312020d020a080414070503100b030c090915150a03080c1204030812060609010e09040c050a080d 70
    0x8064076040890016400e4114014080a446009000000190464010300e1903d2090080303005120309404c103a0140c2221500b0603c04490054010000c1210342c600300440141c40140142235800d0742c0da94084103035a080c0007402c1001559200c404c003041c0044140680c90190600720018012482e1108801d81504c032294000d0303508400801d81814580c80103c102c0340c0c01609414a01c14001c0d103a46100000c0c49502d2011166500c00b0503100c1d0400d500c04c0d18240224003c0c40725009420344104074546500581c4101035055105100c070000142c0c440e00584000c1d80010181e84c020340014006c55608401111844055046600448a142d040220003034000781c0c080e03100d4241081010104800c40314601004d04500707004540408036403000c00c41c0c0344010601d140343e141c4590347d070f15102e0b100c1d40066440030074441c001000a64142041c1082e100003450503550f13041a2140f41c0b05000000a020f8825540c5010300b200c041042c0c1c40340e10a500c02800440006c0c42d20341c084c4e013401058240c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 710265548 1250 710264298 710264309
    0xe0703031e1e051308100905010608010e0a1716030c060e0610062a0507060219240207021810050901230d0c06030218010c0b01152115 59
    0x1110501050355540704140e0000c0c2503040c2883e43d60703401c0007008007650b841c031a17104240303512503105d60688403031840c0c00540890344a070000340301081e12104100d003640c066124400056008034148400b2030b8600e03040c5840b410382840c10626154080d640304030107211200b402d9012402c459441400c100d41442201d4204020602600b01c17400e01c2000c4170743c1250130b84142000c015550792092010340b0054220b03002024810100388182003186049512100c0522810b0f0140c029120104004105000304050190780281d040200440041a01c0d610a085003030720014540d003800b50800603101d101001860020310b00841d1164600801c62004aa0f8290021400784d081c41004000c004100785071500c0c19018030301000f80c070b00d0403a804120310701c0b4051400f034461a6503400001e900c94040c1d0041c5018007140c4000c0074640904401502d0b070310303c910700092204a041300100500c0140205c0350a51240c540303440745414051070440c141c0e102a4014800d4000c0da59410302214004254900d001043d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 710266798 1250 710265548 710265557
    0x290403081509010e0c040914011e060c0f03050c19170c060a0b0f0910090c050a05122802090901060f0909110d05010602010e060c2b0e0703031e 63
    0x71425001c41e84079030b018426420188107100202d074042c08041c0964018111030081002079000210045684020078801e1030900203842010b10100540b40368040c0c02d844940c1c403804407a040c10782c0da030442d8040400c0164100042484000301c0e40300c05025004007194042e4040e00240520b08006504482c04140c2a292500070032242c40030002c04910603520440d02400003c55031481c0b03011031284d903d90100300d944100d50034108200d40031000c81c4c280980703052220410140328a031000703071164072030800e4910118a090100146c0c1c80014003165a20086170100d0032062844610091110303001107400002a60b00401d840c003690815005581c014035003860900f4004150940142a503030007170050010858840c200c9004400301c03803044402c02452814100407541e07507004000d008000080b1100c0c1c0d07601680020400c403c0140058440d4414440e0303480c02400c05424100700103491064a034040300352250010020b0403014000600218065211a8240000000507030300c8000158940307028070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 710268048 1250 710266798 710266831
    0x3150a1b0509030d031107050a0302030703030e15041217070f18210501180f021e091602010e07030f03080708010807030605090f07030507080705060304050d0c29040308 74
    0x640d0005105054003031242400544072406c1d00310a0003c0c4140038000c4c00910401021204141d030000007441841d000765406c2000000300343c41c49071a01e0320540340404100c10580420040b8080c000c02541d000000d04005582e8502600faa01d02d901080ba01607001c94072072a2601c95450700248204141d00c0c2c1d0b2140049a64206000c0f070b502c00112000c803404aa01c101003080400109501c0504080803040ac03004001e1840d19004130201d402c100704a0041c50500c00c0604a0341005110f2010703150000d0020a440d5079108400e40c3c0c140740411000700f15902c400c01007090706c030140100e030040e50107015460b05100352400d0261984402400003020061035500410445034007180e07150950f81d001c070020030345480d2103800da850b2031107003203540c03002d401260000400c10800080b40f030100c64500c4152070340181d0301c0042242c0d9010072a000340c0550007011503452200d20500d60410610b01c100340700224a847d04c0c002e000e9080d8414131803500c560303045081c8010705410400ca254881000d054103109d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 710269298 1250 710268048 710268067
    0xb0d0c05030f04030c0f050303040c0f0905090c0909120d0c090b030411100309060203092d19030512010303270303020c0922050318030a0f1103150a1b05 67
    0x141e80d000304050b00300320f1402d90b05010000e81c001551b0340d00703030440f048030340342e003400d0404c0d1448107040e1080f118200b01c8640b0005070b26031180142417144d01c543d8040d0440150324030a1005c00c0c03100401d9030840303001d0245450a4400400c000c1d00000c100f00c440002c0c4d030400900d001d00b091209030491600141c0610820001404151000b1000344050340c448135150104001540601041040280420f0000c42040f651f2100000ca0381200d8021a042c4960403421560030166013941c99480402600030042802e0080a240c1984410b1482440d10a01d040b05032a40c04d6500002a00704800050100d114400c00751550a14280c1d171051946850010500d1617801a5441c001200228003400c040c0d400a16078085a004000c030b4515203000c19410b00100e80340c2a0307102d60041c01c8038456482100b0054105080004404843d258030441d4400344040944079001c09440c0110881e40c1807040c0005411034281e8030103030f14001c20500300d0201e010080044801c20070519003c83c0d9040010a0142c01207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 710270548 1250 710269298 710269321
    0x10020d02180d170c010b04020703030905070b13030605040f120804121403360a03031508070e090a020409140c030a0c0501120906050c0703080114150904020c06010b0d0c0503 76
    0x4115807481505981c4d0f403620301984d0140460000d019406440890a1000e142d0190090b0803454468019a241d070381d165100c03003e0301d01170700485000d50360f0585001d00014850b5409141c105003d07103904004c8900d1941e600030303502c1013070050600241c1c40c0400d0000b00105407a6403102003515050100b980403104200350901c0c007000303003020340c68800015024901e604203442c280c0e10f40c0d0040d01e26a8100c203214222965206d184500300c002a140c9040f071410a021510704000ba1000440509000c82c503081c0c01c10041034018001c11002e0140b07018940041e9554403d10308031a115964044c52259026240d50038000d0b04100c1500941004152600260400c01903005646e000d081001007100300c00d00800040904450040200d0300d04814010f8000842015010161182c1c0e43c0307011503030b283c00e281c1141101000d0425000002d4540c802c145000c0403003c0c1400e081e002e0f01c010704102100000c0c5252803800e80c8003a0590000095503d5030203668000c0c0d484106450a140e881c0d03080a280d1480c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 710271798 1250 710270548 710270573
    0x129070803070e010c0c0b0c0f0102030105060d091a090705040c0509031e0708010203040515070f1b060b100305010602060a0b0904020907050c030a050a0e120307110310020d02180d 79
    0x41001800c40183ca9507a001d040d620842079044114a94143d8840e6031009041d03100d14141c0e8682d1007842d1462510b030384140220ba060360005004c403410824000701c0540540541401110050100e00034852200b40c0d8a481903c5001c281e001071280d140362800340005c40d0040421601040010411703060720340c0700041c00050300d020781e10b1188108109045458207007111038219000f954000400c2c04240040081e5020040d072010750001d0041e140c1c184d0940f68400f4011010740420007982e40c28803841403e180d8020042c0c060b01d40403900c403000d0000907840790106031490001c603035203a00505c00664108281d41c0e2020030017400b005203d040000094043c14000c05c024401c04025001a0400d882401512a00200002241d80303c402020300504a0f8010b154501c00081d03120140c2d080301e140100c0070306000d100301c50243d0700d000450b80f60145a031504c10740c1036405218540c2c401c100c15140d48002c02c0c1d4000100e90058a502d0f0390401c42410300d202c110150f10480392204d030709011405400c5101c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 710273048 1250 710271798 710271811
    0xb0105040501050616110612040501050708060907030b0409150f0f200705100204170d02031305090a0b1509191a0a02010905190b0a0501080607050d06030b0129070803 73
    0x802c205003494090069a203070480180c1001c804078036210680d141d0000903009d9881500240f005989454040302c0c849000c4442941c07041c0c1082c0880c502a000b03070b1003204040e42c00b03071011603001081d0301c071030408403181c2050141d00756641c0306070004c60405225640e075440d900c0b14207200c903030b9201c0d078400070070104032050046000b40010302c001000b00402809125000a01c3c05544699851058049482d600e600c1c1035110300070800d030f032101c031b0703101008407070200302d610005240e110b0904c410300c05540001030400400c00d680714960381e015a81c0c91405226050342451441d5103001080912041d05000b403404401d82001013001e0000307019007003100d19041c41e00000d440e01c0d03040350201203003d070020810181c03883c049d030420801d5a050200e05010042c3c000c01c5603a15a4403004607440880e2070900c102c9016030800c0707000c556850302c00d40003030a841c2c1002d10042070b0140c580d01c40000d01c0c20b003a800035070b001401915021800080084000307110418805260a0044940b940300c203030711000303000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 710274298 1250 710273048 710273077
    0x1203050403050a050901120e01050403080f0708040b04020f150a180f0e0c0409060b09120d0e06030c0d06080a1202060708280515040501080f030d2a0c0b01050405010506 74
    0x8801e09910800c4480803910b0b04040a0124040e40e5901a0003030ac0c0641d400e80008207401c0000f01e110141c040a14040e12444e5190b000d26940c40d02d071714411343c01c060320407a444a034070300b0329102580d2168402e084102440b080301e40d0301e481002000d4005a4283d1000b810800c03030100400c80301c0e0040582000301d420f24030000c0d6055070b46054000041c03003290000c0322180e203000c0021850303030781c01300241022503020b03a91000d18000e9072451035511400d500408002809010000419003840d01c083c58012500c5d07480b035410700e4820000d11003540e48541080c0d88031780c0000c1c02503040c40121620030110940d280050420350038240d000600105e001841e21190034a003608403061030102606508024030140c00400050404011403156070b0303986103030030f032085040000104440c80041450705800c1c0d5100000c510700401c10282030040c048403082e01da05c00d80903001034000b4290034114090840c480f45d0741d40f070303540f01a4901803016807010707045140510301d040018096a01d4044c200c0e045a054400e6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 710275548 1250 710274298 710274307
    0x905030c010f1710050d0501090c061407111302120921030109050402031c02010b01121a04090c0e130506010902030601090b1b1e1e06070f0207080313031203050403050a05 75
    0x5003041c204d80c0e940c01590494100b1740c141083c06410b612090a051042c1403000c5103554496048031a1050720b01c2c0d0140084081001200181594442101c2c0c92006032034000442e0060586c04201c0c0c0150302c81c1030b6205050300c00c01c28000018044540000b800201802d1a141c040103200a0340c00140918031030b050703861000c41d066540802100009503000500e80e181c1804807007009020b03004000ca05030100e00590a024070103505402484120001d04070b12001c205580410803019000c03000c1306407a22001900301140d040340e60f01c0e07210b107c3c0c0d85541e003c806940c2c00d45009443c04005038000000144180188504d580c1d0080250048402e44640300c0d403144910341c50f04020000c00d44962100e807040c810540e0100034400d484a20320036041064802c00302e2040700720707603042e120b0071403110a6421502c000b840e002e0107400d0340001010341c4d20486082c01e0300c88249914550041150810705900766608000304240c0180d0488049000c2c07030706001d1400d15540140143c000d1240c40c40030b2000124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 710276798 1250 710275548 710275561
    0xa150608191a13060204060e010806030d0212160204090503030603060a020c0606100512070e040e160e130507091a030c0d080a110106090f0c0521190c0905030c010f17 73
    0x40ca20080d16000402103581b50381d5031300042c1c80621440307240b90200d003407040000d4040ca00032a10003002500d5801030070501c0d010400c4600345034051100c0ba010154403414204c00b58549106980d8450b20540085940341807200c10140350070001048241564010007a8501b6014045592500854103071703620461144504e00550342c0740200c400300526000c60f10100251a07611400b82d011011341030b41c0c2001892011200f0039182c1d900d00342d60040f401d02c1031004005d0b040c1d004100540c8001003505400e40f40c00d04d50f480743d0070b001856001c1e0059a841b03151030390200104210089415a003100146110202800440e10965400b0000340507a0000300d4901940c9000b422007003011003520ac0200203d40c0ca40b03070740800800303038403211524181c074040704400064000d07000c13180301400f005402014004048284460340600816084104a00210b8404e1310b03015401259581c00c01510340b5000507007040145843c0c0785101e0401350401021080326030303420780c10941101501742c800c0d410300c06a0340ca04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 710278048 1250 710276798 710276821
    0x317040519080c0a0b06010e0307062c130c1805010806040b06090d03210b011d06070c1d0903041401082203090303030b040204030c09020304050a150608191a 69
    0x3000c0e0a003580c01424541c80c2003190801105d0710032082600c850700c110002070103042e0340304003d000d104045440350744810248030030f003d4035508558034201122120038040011814504a51103645040d41d02d40500307039081504040c034140d410310954404000385241100007004034030701526660040e40c0d504074002d00ba84035007085a400c440042d140760002001c5180041a14031a061114000c921200750b4488000203070060002001c01617441001140c469084041c20300800762249500c21410040e0300300041003030f070b4204010808001003d002442144030340701100c90040c081001ca401c01c00062200d2a26036407440e00c031480a10340202150390701544405030228041c455208801900595006c040c0e12032071090a0b24070a9030140130004295083c00168005d41c00010602e5a0f0b03400c090080c100140e010b15880781c045c6044555001c070903100c3c042030f00d254510f04c280305602c8a005000c014410042c0c4100840398151b21199409907485001044030620000080404254080343c094a201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 710279298 1250 710278048 710278057
    0x303060f060203090102010506061614240a1508100e0102070204111c11040909030e120106060e030c1e03030f0a020d0905010203090a0b090604030507030c03031704051908 75
    0x185009600c050300c45102030740e40e40066180364010740c24000010003504140707051391240035050203941009861542e401c81070200d115001c011620444660102255906118001082c84802c604e034050401148030003d65200c48920003000003110810072041c20005428400410180400106820381800486c013903c110300b1301951040c01c5c148c0d00da4184049400905c042001608010300418030f000d0342c4410b032000d00d101c08074140010700c0100a4604280c1007102014404d2801a07021105000001d100c04c00550003d050340e075603040e080c40b00c560016035003605070400310000c1c4004035046000641120782d454180e880c4106804855138540c50400c01d407501c1442c0740c0300958031160b00010003551000c290341c488000585201001402d5400401210405400681240c00c0303a41401510030095015010070350700424100000000300d44148034680280d4840d2840d00b803601d15504008103114145c441144020101c042070000103540054011070009081070b0806154070181840d101501a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 710280548 1250 710279298 710279309
    0x14060103150e042a0b19050408010507020c1009080a120c0503040603140f0903180109080a051501060203090a031202071a0c0d030213050d020a120507081002180409030306 75
    0x10b90400788002c001c40040309140709202410000115400c0f20240440d690fa184074080421360200840808410b0000000305c540c441420310700c2c50540d803018001e08550084900360010303040280105450301e0710302c044420f4240d2071701c1c0506049003032100d115214612614000c0148811020340d0700300c14011039542c0203d80e081800e0b0b980711b60b5100e1010b0017419018220012a903000d50000d1b4030034400001490084103174400031400d19041480725031443e10340302074a506000d00d020002800c4102000414038880c8100043e002814420891149540c01a0480d02c10f5410a220b030029a0300e5600c104c804a076008000c03661455040242a030400100d038200c1c80c444421404a1140c04090000400c40541103404070380c40144030250490483c0030743d901e0500001c0006004200c1c51514001004560340010011008640d490324641d401101112040382c840e00010f1040000010501040e8130760307403002e4010b524289030204000803071038540c40c2c0d003486640d955200c6828180f1982c401400340c074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 710281798 1250 710280548 710280569
    0x30402180f04050f120306010e0a0b0a0c0c080f0a0321060b09190609090e0c03030d1409060f04080f0912010605151204020603062707121406010315 65
    0x41031034000070700807002c6070b06444501c500c2e02d050b030400000103010011100041041e03420758449500455818241920781640301c03000f0000840c036203844100418001140f0745500b2034806192422880e04260b81c1c1c00f06c8070301d4000c1c1032492500c41001c18880445541890700d00c4036000520105400302e900b0611034403400e4a0b001011030f43d2203c0a0050082c04400c40b4102e68031030030f40100c641000c2131030082400003141e05400304032402498201c030b10011000700c10b80310b0100079240801d00d59002032000c080020307102c0d42c045000307041610b522034114006001030002440c0800c0901040e03400500020a5030400059072030b1880b020605851220500034240000d03544e01c1544140a080369010701c5100b5080450242c91a08909007160b14144142410014994a0342c08014a40e0001040c20f5002440c4030400506600b00c1181c0102d036034049007003c409030404000c014020305034070241f4241c16281ca0004071101c1c00020509a100c502441d000c18a24001040128000156070100d40e800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 710283048 1250 710281798 710281801
    0x80f191b0303050901090803030601121a0411090a0b0f03040305070f140a06061401270b0d0e010605060304020913080c0d210b060301060c0602090a080d020c0604081203040218 77
    0x40d407100003402203244c2640e03542021521400c01944a06c4141d0341680030401304100c0c03441c01d004540204460050303040250000782e0f4560040b9064824045800e8805200051116940d241081000004d400d0a01601c0d00f8030381042c203031484a1202070f10140602001056501c1040a800c04028025a00105001580d65041856580c0d803040306411102c0600385074000c00c60b008444000c1940c924141c3d1224680b9010710400984c4003c0314030348818280303106c0c001040d040d04540041052180c05540054051391984441d800c40c0c0d540c1d082184101006c10620000d60b840c034409503001101c660607100c0e84081c03450041254441c2c440f14102a00940e5030031601280c0080c00d0380c00760342003208002103003142e992800003180c0e10100840d074880403e000521100e4031998480807810b10640e0b006141118034000101001315a03030106240d076002030f0494840720303418015880300c0f80c4107558a609060521200300d44507a8900503403010300c1da001c40007801355550101110340d26080c141c8980002d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 710284298 1250 710283048 710283053
    0xf120b040305220e04060b1903080d060f1d0a2003090a0506071107050a030201080408030a061e26030a030207240e0d05250f0b0c13080f191b03 63
    0x4e560480302a074400b441c001082d070070303405c1c01034036034545407407043d13110303100070705640d00c03170205800c240a0018000d5440d41c2c08221a1000c207801005030100344800c502d5050303014403012001c0d100400c00504681004204d01d98102e003580300095030207090482d1038803652042105440c1207100c0001a059100304410721000c1a045200600c001c030500303040e103840340d8560303003802802003591000030300080d800d600042c08100c40402a54200740e203880042401d0390745100040014207040c20b601409440e03c18100000c0d08031b6900b0001405009010084440d8400301aa0310fa0040f14401020315800080c04070410941c001d6810302200649541c0c007940e11040710703540c01801415a09001885200d0071100c0c00d6004100355090a111458042e204803003804244050301d02624084608800443e0f07043c00203200b01603c03038425200c8546003600d1380c000881854408172654010701d82500325055500706032a010039210b1841d007540ca603441d038a1a041ca810f08540b441000180c0492103010404401c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 710285548 1250 710284298 710284319
    0x33060403021023091215040305090d0f150c020d17060301090b190518030a03111209060603160e0109050601050702031f0506100c0b07180602070f120b04030522 70
    0xc140036a10a05c0f40414034010540d140152841d11158080c09000200000e206a00070b080588001d0100c0700a00390366518040214408501180c004448030000c1c0d03482c002134440c0740001e08091001341110440c030031018200c041181c00e145608070352400010074646094104054042d4840c45201d003a150085100307201440c6a850f51185505008c045007005443e50740d151450442800a1440c1041242e025070041c8100165400703540340500000140102e000049845103032294003400c40c0345001c1c0105810407082100c40161452642414041d803400c20084a0540d0101d120000742d9444100042c0c466015640000f9031600c40c007043c2108525a540051b002825107410620807900c48104010f004105980707581c0001c4c82100300e01e0b010a90030340c00d0035004002030402d5180c0003400c16010126904a40084016030b00c188030400400300b18400400003406940a1091105103517610f41c43d031044045d00140c100b200100d4001268900c0c0104181c0e401201861303142155600d00705650b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 710286798 1250 710285548 710285557
    0x603120804031e180b04050108010b03071e0c0611030907090e0708010e0a111804020f0d060608280302031603030f022a0705090a2333060403021023 65
    0x890501c604c0c00000c4d8008100055409949050712891000da081007444071454100412800030402f100c080d1103200300044145e00c0d41d00321290340d42805508107003450019144400c4810f43d201100b00304001a846c0003152000c00c0d680b030a4000b007901303191035403503502e4031381f180c6c110440d1540391582807443c0d030740c00003201c0790014425007524060001c0c4808001d14804201040101c002d1840c0015005181000042d40b1041380103000302061203054654208581c0c80b6088458180d0104003541002c1c012182482c02c00c211225003038200c82d2480c2e41c025228002c04019450016030440018101030082d041080003120003041191103d0381c0c005060103e811070120f08400303514200d2000c1008a022500c902a0360001c0d2443c10b0940b21005c0b40c1c40100b000102180c031a1100e03000d42810300b0224540c45025400034542141e8050481312000400c41c16841c881a01d03d401c6000704400d81c417031206403403c42e0780450781041001c3c1078010030784402419800103a1a1f209130070400754014a040041d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 710288048 1250 710286798 710286827
    0x3080409091a070504050108340e27091207051f14010b1c090b0106020616020705060a05040914010f050d150209030309150316030603120804031e 64
    0x3142c0c1c180c0a501d15403071504050751100c0005004005c18481c55010755201500500c04010504040d041019940100a070500305840d0030795408500d069295400410a9507500040340c00101c45604603000188031020740507190041c1c07020320000340c45403c062100c5d8010300880101d072a5583e13090b141607030b01c440400604403030400417010200d8045a65200d00030420703642c8002507000381d0800b00c12a540390024400d031186188041620044180d8501510509a100d1480c00034154100200a4100f4200800710030003007207a00c0c080a1180d600040010881d001520165907030441f03503c04079614840c507000b1000720b60800130f01c6988054030a004a040f24460000420043e440d401085040c40901c01c0c05860112405403018000000c2d40c000c040303c01005080b64940b50380708000c5884000c0ba4401e4060750b800c04410014070f100b01041c03c00041045207810802c0301c0c00c59031140304151041c00c0070010400320784002000c0602070140c4081c0110450a188002a0708400042250080c101c14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 710289298 1250 710288048 710288063
    0x91302010813050d080a0e010609020d0c1719152301031b030b12150711010b010c0609022d1914060a0507150204030b101412070308040909 61
    0x2c03010400c216024400c41d40c00340240c404c200602d0411590584080c0c030044d1100c1da582e1071440300d19802d210314002050100ca001d6140c00080d40701800302ca4002100c04217001c03001d86d001c6550103d50307418560140c084d00c0401070f00ea9048901d50001c0582143c0c0b22100008900081503169424405844c0c6041441a1004050b0503400440035140840040e616902c001202b8184072806500590000c09024014401c002e4200c00060b1509880c001c84600c60740c2c40000f88070743e00f50f1081d4443d0240030100000e1010841c0e42c00000e010400400700a0b20742a41d4040d2202155211401d01c1038601136074465030210609200142d2120850f4113189210b021582d003100030000c24115044100c90007402d803420107101c0b0b50b05100d03040d40048505400c02070200034083c009803900c212a40e8000c40004010b03100c6040d81f5002c1038100014080c4110070171030318030810001100e11040384c0034060544020300801d8080610602c0c01407140c10040260710081004201100c107a8096503885025011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 710290548 1250 710289298 710289301
    0x305070f020604350c0d020f03060103030302030f01080309091b070b01090b040e0609150912040f060e030f0606010e0f130902010f080705040329070914010513030b060d020913020108 80
    0x1424040e034a110402da01c1d1a04017445254040ca4498500c03070072030b070015200c00a41003c031030000781802826003080700400d030f0100a000c5040d43d4484201d01500c1003c00942c80c0c1403103480000d01989008041003448070388100004079103c400e8094444441c0c1c07040c2c2c5400c1d035507143c010b06800740c54030005503402103140883c1c4216080f0001011406481100c02400c01038401d0030007240d01950050001101e885800358145903041c051300107100800101505284890910100820581c0815401d07403003944202c00f270f10180c0310701045054100d902401c1c4404403490041c04500300001c080c1e441c55002400052402d5981c07100d4008055a138402da0321245050651103080d81c42c50b109544050004000707000610006002d14041218501c03920000000e108031500521141d6408481903400116142e0b0100008d112290f414262a802400c001d800c050f02e075032542e600c603605031002034884d10358800030074000e4858500000c000c640103007e04445103090904000e041c482d040c4c1c200c0c0014440700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 710291798 1250 710290548 710290619
    0x40e012004050904060f0b06040602010b0f0a0e1321020703061803021e100c0e150931091a06010c1101080703061e0f09180305070f020604 61
    0x200c400b40d500091101550381c96644500c0000c00c244a0840015a941c0c0c0c1840b10b40d0740d9510151001304095400403030a41e03c0d49048c064500d42d490011406540303500800d01014040b201d4542d4823445402070301c40c9c818540d092651200c4044243d07907540c00003469555044d40e0703000c00c40c3c0c1c0030b907801a98103101c04090207080d50b02c0702001100240c0140c0241c40400300c020303010540100d0002c440700c11142c0d6604034940300c9044070a0b0201d11008201043c0040e0101e0404007010300084041e101240c1c01c00071035001041c402d070100c04110001d0500700c0c0040800d842c012101c2c202d50030740c42c501000090303854a0800000040c608000740c400c50500f00081c05507201e0b204501c45c684c0d001000f01d411003420001900c134550064108400e054071100017155040184089061004400003102c10003407600203d1041940c04c1d81000280754140030260080c18a1580b07251500703036043c07900d650303a80000c1c02d0220b030140404200130f500900005000407003011344c0e859411000c1c10b40301c0003803460b84c810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 710293048 1250 710291798 710291861
    0xe010b09010905010813080f0c010b040e0706180308041205151902091815120105040f030c0309180614040207020d02040509010b061908090a0c030605060f040e01 71
    0x1000981d0000e0070100007440302d5441400e03259005240040d41141d1515207640e00c85040c1c00041c0f0f01058074034042001c1c40340c039034240241e05840700c09440070801c40c07910890958880d00503020380020b2010121111055140c131850443c000d40d0080001030f101c5490b400120319440030307100242c9003031007004c60b4040d04074951100c250213048900060a551100744180002030341040c80f48941c4140f010300601200421100d255204074a4550118148100300c0c003004041019808108010ba14140402000540d601c00540304584c240c100103d51401502c0c007146c4110142e0080c0085e42c0c0c45240802802c0050b8210205550203000e20300d2201d540641030100720b00400002a50210060740048058203180d8001e03604850003000210309130141c4404a000b55000c1c00c0f4048000c40039001031901d490340050a2a08049614040c01c3c80240e40e4840110862140c000980082e0341c0d03801042281da17500500c07070102070000d042403012540c1d820400d4001d056008a121028070306d541c0f66040d07514030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 710294298 1250 710293048 710293057
    0xe09150f0109090f0602030a0606110106060c110406030f08030702100b130c110a08090a09050115030213030c0b071104111c020d060b040f0806060a03020f130c0203040e010b 76
    0x104003150605038a060104406065225800d40b030001e2401d1101e808544640004e5208400018011402600d4408018080c0003a141700b0f10b6a80d14100f000d1000f240d0015000c0f8103950401100240d411100d800640103201c154001444080c030350400c201040b1a01000c1c1d40f103910343d902a5a000051016228251078401410381c0c1e000b0300803a03a0f00002e094a500140320002e0030b1a1158404a00480f160314101c070320507007510021030200e90b0039520720303000f001c88020b41013041d000c0c06a5407404100f03003081c80d01310181c00141030300030400140004048070110011a0443c2141903003e983d61804a0b696002100070703a240035415030b95001508003801410300d80d80e40441054a0510481c802081e112240400d0b0740072a502002465000356550107504e014020340501c0301e94035480e100416058000d568440200da0f0001020440c0942d6030002c0d440407285c0688490b9119094100042d0100103c08a544041841c1070b4a640801c0e0740000980241c404204e49820b06988689511550307004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 710295548 1250 710294298 710294311
    0x5060c100c170708070c060c05220b070b04050a060207031d0a0602070b1b0d0e030f0a0201080f060d0b040b070905120a06020f04030f1a06041404020f031002040e0915 73
    0xb560003c205100d1007400700650101d103030310b4007281a25080c0d840106403103d40e05440f000403004510200303140c604580c0c04051540a000034a041454039108404074000d10710f0240c40001e0800001d81408004c0c40b00c01d030815032210303046540d880d16140161581d801d10810f080341801540080800741000c0e071030102512503a40050064618044100c4250f03404012282c0007068000c0012800300d5003004281c2c020a0151502e0003a400c111090502e0007181800101d03179540038003003034000350342c01040460b04074003600d481601c550b487c4c3c4c0200c0c0101d102440001c0080821004110078052a40c0e04d440c01100543c1d50000c14954030f408124001c10300a50311022a0403940b91100040ca050b40142190700c0c10800c0d60782001e135603464450300d0b04500e00782501c00c2c078001005900d0180011a00c147e00070000c0b00d040110b4228204840482400180020b01031000000a4034590750200250400c00040d41d10555a90391948030060880074140e0720040c4910616444100c07810450a0b0b05200e0702 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 710296798 1250 710295548 710295587
    0xa0c03060c2307030807020d0e1504051306030510140606161502070c0e0108100b01030209120c030f0606061e07020d080a1107081207020a05060c100c 66
    0x904584410008003650210001402500d04a0103071004084020350a004100c54190703480c0d800c41e0401a20301080188418210b4001150b580c00c0c030381d001a40c400d403d20003600e196049000004040c1c140740b085420040d406800c0d4000005038245540020f0b007503d2060f000c0c2d0b654041403500050507180300408000300e8030f1840300000c8090900f4800362400b82508500f125600310107803603511015030742a465500c0d403500044e001d4248030700040d1590080c049041110002c3d89007131841600c2d003000d00410907515458001450302a0300c2501529003007031009010403056030316511a10340e43d1b41c0f80c0016034000d001d1001d18480700440450320a11502d800392505282c003031680c00306000700c0f080320b2186403014400e00c000c4015807904400da40c02d49104a00350b9070751784814800505100340344800d03003c056011180a2183c00ca02181900503103151718000c944a217528800a090304a4603080310781c05c040085032210803000f001481d91030034040a002042105030501041707540d09000c004210000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 710298048 1250 710296798 710296823
    0x5070f0f050a0e040b090f100f0f0608040c09061511010203010501050403080d1803030b09060f01020304260a0f020114040e0708090f07061e02150a0c02030c030d090308090a 76
    0x583c040c0d44060b08404000780000380c4402640d000421403a003d44410210040c030004000095a02a90507006884400d440c011203d01d41034600342400101d000e204100822640801e0801c040c0c1006000640200c0e2001d001094031a02d21070100050070032940c0000d20380e404500c0b010001031003220705032181a510103141078110786032003025074856079107000000da4460b401007503000145009405d0500c25a40031074001c4480d010003450440c040c0c0302901c03035118540c0f0201d450780c00000315000c4070a0f10000485644a0000d008403040c01c004018000b40034142180041180031700041c1e402078806d0320341002d00c140001d07041c0070342d000d40d014540c80001c886010490407405240115030011040701210000d1002c10815410141c0300e41c400320114110f21141d441500c2d50307840d0440300e0403091008090000042d5101e9204d1a005000351011a9803154003881780c91003401115000ca286204881e40e91140840c000000c000341d1030f09500080c02e843c0810340c814004547e0306078003a00110070174444c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 710299298 1250 710298048 710298067
    0xf061509100309020a0b070c0f0e0f0435040905131101360e070507050a11030f060f01090f090201021f060f090603020312070c0e060d1505070f0f05 65
    0x100803c0070240d9005c42d03001c0c030014508101800030b0500900c40e00d00858160311f0700c1509641c025254201944a80c2020708001a8075505200180c1c0305030402c2c4410292252038881c2d074481c1c07602e543c40c0010f000c003c40b1600b84030103c1c0c3c002441101c140c050200560b039107405041101d800141c60040c4000e04c41e0302c20a01c150301c602c1e520a20dc003203240b0205c500495125050440503600540502d420241a8080106000501c602380d8030601130f0401c1458415a556201d80314a6520002421442c02042c1124503440400c004018036080100f01d81d018101403d80c490444000d204100c41c1d40d003031552000280c0b20300d0161014596042e0024441ca10400520700c00980702c0f1848030b010140d45030000555041e080ba40840200100000004c926007180180b605080e0600301c110401d0104211070000122141980000c968075000c5001c2ca54a0300d600040140e200340c0009460701d507079040d00c803100c07690b0b1754003807070007410580c68214602029050507121a1a00c03000c4401252003880300c00341b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 710300548 1250 710299298 710299301
    0x2010c020a080a021203160801050102030a0c0f1a1015020a0f111302181908030910020a0c240908210f04080c0a1a040510170f0615091003 61
    0x44892041c0191100d004e201001200c0c179070002c07200904280ca40440460290340c0000c1c0440c0505028800340d4506040000c0240200705200c1c001410900c031030380d95505100040b541921510b406440c0401c06042c001700d540070500c143c1c06607401c4400008420001c1600007d007092178542c6c48020081d02d10f150703450311001e001040e4100703070700f00c1d1039501c3c400c5000050784010140d01070800704018400700c84800f80f0510031205401000303003c4680d1001d01c400d04000054424480c42204e001d0244d8410300c00482c1845081203000f000705481d03401c08039249011454840030802140c4d4900030082c03401c80e0403600302086204510b01c5402003070010030104416a817002c401205180080e28100007035124170302c0e0764426400b09441d90002000130304039240100c40540144858071014000440600c040b082500c218450103110f002e0280c240703200c5600644101e4034001103007005e503a00c3d10340200400004601200c1c02d0380308100101c031ba224021022029501d10500c068a00000f5883c130364400d80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 710301798 1250 710300548 710300557
    0xc190207050f012d18120f0f03050d0608010501031a0f06040e0a0206030c0d060f06020304150c020d060507080603010240090903020c01080c032415030f0702010c020a08 74
    0x21501000c440d201046260003503100345600301c0c556500c114400c03043c02005c4044100d504428012042c03084904040b602c0005550209500402140ca00007441e282c295418819101c98039409402c20500050b015010751000e4100c9004001000409124075a48181100c0c00c50b204d191a50000000c10b44a050a50000c5480441002101d4002c2c0a41e000240390340c0040f1000c40c1225030021311919412103038015003001313240d0310405400040c1020350107505c9021300c0c05000d4078482d8050030a402c061148201160660300502402509811403c014018103412a41c40002c90072020118489080500c00c542203208140d288a0740b2101041071400c41d441c00f80f02c287e43c41024658403802d07030300e980c4421500510410500050b0081c0c50314021707040a42481203541400f03000310800c402c101020044951203081650103549042c0311810003da0150104281c41c0c11040b00311201408040d54001140503800300340705440d031680d40007400c90036641d0342035810006030403002160000801800141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 710303048 1250 710301798 710301827
    0x211a09010b062a0703020307060302030c16030e031b03070b07051005010e0702121305010e0103110a021005010e0c070b190c08190e030313020f06030c190207050f01 72
    0x30418900190004540750414652040f1042c1500708800f00b003d1480380d03a0400f5000c0b14081c0540790724640000c1d466000070301c24903060580000c0060b4030080500c040f1040c400442c1d001c14001001814010190304500e080304d40a44180d0604140c16044c0c1b1007035030b00d0060014000e1140300e00f00102e418240c2c0041038103c40c00e1207400681201c6126a005040c040d03e10707100d842c5054900004020f10302404a600c40c0300c0355030100304404842e0405885a0700342c44003801c01101070000400100c0081150b9801c01c0082e04003c0703681c0d94480e501081042c0050b500301400d00042c0d0301c5144505001c4020b0ba1426018072041103103074000b80813080741d142d1100041115000c2c207040590494144d60112403040005165041004412180e072a5040001c1900c0f4804201030040c0c0c000e103a1366444090b1034003c904000031640011991040364102d04203038042c22290b00c9041604040a15802c83e09401d4146890544000c0359030b88001025821510300416808080d101840151344910161104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 710304298 1250 710303048 710303051
    0xb09010c0c0314060405060f0402010f0e01020309041a0111011416121401030611161e0812040203010c08090601030605062d011e0207030602030901060806010f211a0901 74
    0x4540e03500d180c02403c41c54003000c0c200c2482d0a02e4140d0404800074040c00341c05c0348103c14800582d0344551011541282c2d030600724043c515020050786140508941d03107600505011000300d500000c02c4403000006c01c2a250030303090513203400080d405e0301c2c50100c0c00079003148881c0000f00d184210800000865855050801071a0020840d9209643c07000c14503034003102243e00100100002442503070941d0280d0744141e8181a40e4185d0559400c041100107407600c01d81e07a17100b4003024031401038a549154044120b075510195044035440d50902154240e210394644001143d0391801442614441c1c10b880c0c02601540e0b0855940d0341c000d00c805084540c201007102c0d04050100d421910148407111440f40d48540d01d4124000145200724800318a111103401c4c1c034000c54a00c1d0001031800c142d07a030103d03001d41c50356035803d1072500408166200003541c0c429000002400c2010b141c04100303440103155a60358201450000b82413820080400512031846652a0110b520a0510305904680d62100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 710305548 1250 710304298 710304323
    0x6092a01140f0f16030e060c0c21010204170d0c0c0e04050c0406080c0a150f050c1617072102100905090106050d0608060411060d06050d0f03180b09010c 67
    0x80f0320966820141814941040c0590160203043e04280c001280102c11200d0703502d0240c4884902c2d03241c0280704101c502502c47c03819410b54400500920340034803d0120002c40d1101e33a01c0002c0d441e040d00510f80441a40108017460b80814800c0141e108803542103c0f2080c0c40030310303101005602690040c815a030600422080307000f40da032503008400c0101407900c002c2c0300e02808003080000301c00380b0394041c044200e8815213400c0d8080e0044c5141c10780404ca42405502c6800c030030800e03400c0c654034203c0759211141d00720000c5401c5014611580040304210100e9800d592500c0008800f1066183c188506001301c01c4030b60018909101c80d842c0154203403803e015119924004a40503000a0700804007095000c590030b03803110094452540100b8141c4001c2ca080d00740340e141c225a0610038480c42d401007000040081c52000d003034100f0001004081d1079484035117405c0c02c02e40745940030008114005031072120300c8031580c080310001000740ca0344840d0091601c1020700055812210340c9000301c500c86e00c01035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 710306798 1250 710305548 710305567
    0xb0a170709050604021303172802100e10090f05060c0a3f020c1e12091c02120a030c0204051521120d090303050c0a09091d06092a01140f 60
    0x1002011480c4481a0f0327950600c0c1c004020741017019100c620054146080c030f480ba9034040016603081c45403a0150002174400190409405400c04143c01078018459503081c0300d14000100c009060a55665841104070225400b0208900f40318609101c107500d003618581c0c40c14100701a60b0143d20380c203070328010b1a00e0765010941e4184005000c086080000903600004280801c0c003540c0d819a01c44c00a4601d0315000d000011f0b1103806000c48803009418041d0000115101e4061440c2c4240b001d004403903002100c0c2c50b000b03004022819049010364101004500d400d01d800801000003000149001e40d84a07000e000409030025400d621065072103218864005000380341300407c019080c40c2c3c0c000c902800715040103015500050080100d0910030401c150b4460381c04500030044c5d8450200c0800e0391014030504100501000c0044115070040f0024088000c0d00042c82115501c44042c055440f604a56848a001c030340440200e404104484088004c05851000070002000c91401d020705003200302d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 710308048 1250 710306798 710306827
    0x20a03020c1618020715150302120706030605090705070b0a151418010e010315060b1b0607030b0607060b04090b0c030405010b06090a05040b0a17070905060402130317 73
    0x78460112045098101809070b0044024070810f110064582035140400903030b50618a44c0d42d1500b000300140d551245441100c1c1c80c2c1d410f6500458000f0709002c4240050962191221017500c120404245021000203441c20030f045400d10035075a6840341c0d41032200300d459034145224010002c81000d070340e682e07860a44044034001d40015040000da1207000700c00d458107002d10f04045074103911040f5003000040150003031407040c03641074a9001c010322909100b548810000340104d500800418000465030030801c00e20300f200806210280001c440c400e84601c141602210011190b8540010741004100042801034000d8032060202510015400c6072a842307100c0118002d407000000f0784d800005200900c90240610030030440c0c200c0c0c0c100d1421801000041007008181700d43c038082e40c1c89007940410390341ca418055000304041402e1311064a0300b0075143c1d80350406070040094180c41d003408036016003007903c282e03a040e944a1301e010705c1c0d06042d81c840c000101c1a2108030010902c0400c10030f61401000f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 710309298 1250 710308048 710308063
    0x3130506130b0c0403050c01140d2a110d030e120406050705060702010e0c220c0302040807090612080328050612061b090a030c17150910020a03020c 65
    0x8901500003450600e10740003480203030150070841c034083e051206002280010135948a03145003400d290082207403e01e0524083e014400302c1000c960701e0315403854844503601491300342e103800c0c40d041c5281c00d400c90365003924448510380d156252644130316412017400d40280e020f0343e03c075012070046480207003010200072407543c0290001000140d001c1880d9003005010090b0a0f000005030000f03000d180754070400c0558840641d0302081c03013000d14020000781101815488103051900c2401480581c210314030180103980607210300d0415100301c0740700081c6046103120b80e9055403e03030b04841c4034114050315400465040904688a000304e02c101150442c2c456601c000001d466020000c03516107030003400c21440301035105850003290040c3e4208002c2e04131069903007081603010103100340c45070090804611a684150070040c15480c0407900811000d11a070b90460074401d001046175010540340748000c90f021015140b001c0380341d01101e0103001000c104c0d0041c00c0d40505030702e80181440540c455282c6070000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 710310548 1250 710309298 710309311
    0x8190f05070b070333050406170d0f05120f010302030601060e0105040b13120c030203010f02090d031d12010e0706020703030f051c0f0c110c011704110a06270f030803130506 76
    0x5d0b101000c0149052a008460041c9841045803415030030650341c443c1c1728486001400108142580300c030b04031901030015070300c0c00808860203500b00e1070315045e050003400c42808140d00c030344200e100025405201d6034200003050b60694502c1e0034240381c000550100c1e0404143d40715540307002c12010a10031041282840c00a01032644504441d1845c014035084809048002c0d0f01d40e401007004070310980311202c91041c443c2c1d2525180119403414180071400c0082c0004465021001062041250301c054001039081c14a420698a106940b04c2c02a1790783c140a20004000c14003480514440c640a070028025070394800c4220701e85864030061240442c0c1d05450004481c550796442d0107501075100403a920a40c1d2020000c0008401300e03030000c0c3c1380c1042c441003491007120050000f03007000002e00d040c0161040103032448440c0398803010f029150081c11464403807807500c0c0c00200c6131401c0c1031585000c2107c1d107080321010001c3c00d545845c40356a00c02024601500428140440002c030b040190034070502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 710311798 1250 710310548 710310641
    0x82508010c02030a03060807140609040b04021603020f01141f15050c060a05010608220614060114070c09020a0e030d09080c01030209090708070c08190f05070b0703 72
    0x705041300a421504075801442c0681e0102d4024050501103002d01d44020404030342c2d0b5a1500310a4002401400007880c1ea10703000360000c20114a10460010480107986c4240c0079624801c1400810a088500020b0800340d50005a004100718404804c203070b204158641401102c22034844032002d251460300078139400000d2000414200c0c0e4017050000030b4100d210514144620b51401c84e0051425101801e180a002d40b120586000640c40061110819601c00b109001c04103100c0144520948110f445a011400d082e0640c1c5410030104200c070300c6507a010815030091810701c000c036030094202c640040c0c00c0c89004018440141d038108071a20500c1501e507a00c10a00b81041c4585042c01c4000380d40506040c014000d000c81d55540c0d802e00d6a1004d0790345801d4055036902c1758212141d241a01000d444c1d064002225504480904079182c106145916582c4484490500032525441008070160040079040c020403109486a0000300c40702c144002e62945403c140300c0703034281502e05110014140d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 710313048 1250 710311798 710311807
    0xd06120605070302120103080c0a0b0103150506010c0f2603360a0b0703091514160c030c03051b070503070f03020a09111201150315082508010c0203 65
    0x100c0240199540a4502d181c00e60402092080c80703024000d041c08000d00a0307401280080c5482000c1241c484210b81000800400d560b40c1c0c02e003001c0034078491400340080c505084c001b4103e5409154088842c9a000d0240e0a01c40025140c008101c40c841c0000c03000980f00b4424086140d0541000d140207000b904005070a001c0400200a249081a41c0c5c0107034145200301304419521004c91031072000c540060700e40c00720f60748070402200100726101005048144000141110f8200c540c03004641021400c143c03800c54139030a4210f00d1342100b54102c2400501d0b0141085c0000b0f11403d00880c0d940d10a05100b41020346604071015200710001803c1100c3e849560104198907040012078000c0c90520301805005003180c0104103402018040d0008080e01c84001a41605d03107103084480780b0b50108403022036540c40786e51034554840a03200400005e418800a18101c00450022000b201c10010040c034200381c01140d1051200d900007041400441c20b080005038400082c010200e491400794041c641e41d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 710314298 1250 710313048 710313053
    0x90c09050a0c0207061b060906020c0d12060b030c03150f061b1e0303010611190b07020615100c083f07021e0309030f01020a03112d0d0612 61
    0xc11800341c0c000400c100051600304500d94201c071805400c20b8007c240030980303000c10700b0100042e10841c425442c541c4103001e02403141c40d03407011980e60070380d0050905205155541e501d024a0340003e8881c000c0d1101c00300085450300c5c020513044021240c1c085c2c40c0c00340c03c0145500080303039038100010ba0001208101800341c0c000d070061140086442d40741c00503500343c800a0180941c2c0e40014041c0c1000d000e40c0000b02e81c44000104810385440b00100c0c0d402013940514507000c080401d0555041c4050b20034900400c500414038070701c8410030383c40501b07030303404a01400b40101c0715102c19940a5038401c0040062407007036040c1035000307501c0946a10000c1c4034910000403000c3c0c401c001e4201d0040801c150b4080c4000c40c0e03408940c400d801500c404400c0c00038500d10f0000c40c11032003104500340e41131145506590395a04190080c2ca41100142c0b82000b81209543c01074031240b040c0c6d0a003158201c8004800b800701441203588036065008000c5035410440e0785401001268100d170040165094081c02c030004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 710315548 1250 710314298 710314303
    0x110903070806010e1503070305190605012304050604330b07030206010e0c0c0a03110c0102070e040204270606030b06010905091314010c080108070f06050d090c09050a0c02 75
    0x5041c450020192985004c14113440000d0262591155401c0310165150320b550400c6480003440d08007040d00d0f40901c400392101d00d4400030344c4044038018144400011040c01c14035114042c0707102440c010031070b44140c0b020030005100c000c01c102e40c0950b4030b003048843c42c40162140400001c0b8090b003809201800120b903030f984160381d030001d02070090410518000a9010404030b04440031400d0003910780d03d442d0050303810f50241907203907481440ba09044109269005103081000c2010605840005090000480e101d030050700400340700c5050400030a00504050384114060201d0803010065104520003d055180c8a010706941198641c0410f0050290502c01039800c0003003402c0405403180362001103541d1650061061000c0c0300c80c011198148040f038108480c041140000800103440b40d180080c1110400b03014074011880742280100c0ca44d588000d440d0306968440d00c8541c00e0541140c6200050008000110341d5154806000241000a8080e081c02004094008561018440d00c000c2c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 710316798 1250 710315548 710315563
    0x1110102130f0e2a090d02060c0d180602250312021c090e060603090a02040e160b0a0509120f0102070b070e0409150b01110d0503010f0e07020d030c030906110903 71
    0x40103103d2042d50b4128000c0c00708138403a0fa0619030150540c580017030030000780740964082c0c07000c0d401150000c6c45840d26003001c036a900381020561038280c040c0050300611155140217000e80b0380907920200d10402032200c0900d11014102c40c200a442500b5100c0e61407400b103400e08500100503038001c14182070b904d0303440c0301f01d80c2d407951403071034030710301d00380c600340c09000b6221000e001c0c00d009400c00800b04054081c20300103a150a50040d0007400a00d030219080d9964a00c0c003030009c690016a50808154480203170125003002d0340d0360f50303114144a0581c00300b0024196200019529104006055405110030300242c414103000e064080e01d540303401c0300042c02c0d80b0119202a80f10b2454504043c7c0000c820303020b034038855048541c0019407189030900594a44101c0711490a0383e10400715546174680e030180080d4141d0740030708078041000307a4074400c1c3c8141810507a51500960008059420400c1c86a0300c0701e070103030b525850301050340000d94495400b03c2c0c59402c0c04281c00c420004800b541410300700300c0e80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 710318048 1250 710316798 710316811
    0xd03020a110f100506042301060909140f1807240e09010b090607050307060b010f080717060604230114160609080c120307260601110102130f0e 63
    0x4150061210320500e449540314207003461021307558004074185855591140724900c03640c041e0503007850780308500d84007515424410310f40003c103140408a114a845d000b401d050999128050b00c0c191140d2010784402c09004051055145070342028006044d4200701140c000c103001c1074843c403c500003070314800c5008208071108080c051001d101007055140c1184050444098001c9aa2595032031000101a8410900050f205110129154041c0075095210b04204a02600c3d100702d018601c400940b100320040360b1281c040b8000464038511400c2d01002a60b00c07240082030249020741f90159035008114166003071100842c406c44031003070b958122480c0075007014407403143c6040106002c5600e04d400740c403140003403c06032201501c0c41000315550607200a10740003801e568090010300c800442036001241c8032400201404034541d03241003480341403040444841150441c903942d0380d0042d5040f1142d170700c101d58150340c00c12000440018101445010380384203000b01c207295150001540d20b811024084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 710319298 1250 710318048 710318053
    0x1170f091e060f070210021824070b04020d080d0b010e0306091906060b030c2205100c0f021905090a0e031e090301020d0f050a0c0e0d060e0d03020a11 66
    0x180300141c001444035803016041100141996404104a00b0961a000800491400400c0390300385100484507a0308070030030540e04403140300ca481c417103480300a02d00c1000080c050320400c03154010481c0110390a42c49800500390308241c040659550f121a030180704068a07055a550811000e90381c000030410714948110018406030601d0b03d01c1544508030004d0744204da46518649004118550f0846401000c0e4440c0050701c0b4039001300c1940d800d500082e90f4410b08031011950140d0044074501d44402d4500282c420a01240d98a8064440505003101034680105e0a4403a60051b51503001510b803030b130450040700e10f40c03070300c2c050074170408540113001582c042c0e092030266000c5200000a40300741c2883c0c05003000601ea5116110b00d914411780050941550000408c02c0c0100c001d42c00081281c140d05608000c20360380e00d20000c00700d40504c0301c1c0200040040002c000640380101540c031070540680b00c0011b110391408411072030074070044040400300f500032641340020b9804c0200400c4d110f010328003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 710320548 1250 710319298 710319343
    0x150804113c100e1c060e070f03030504050603070c050a03021e0604050a08090117072109020907110111030f04060b01021204050103021c09030306050a06031104120201170f09 76
    0x9204201c0307600e8050104260f0780080034096540c1d07008404d079080780ca40d40c49081038541c14002d025120389112504180b00d28140002c2d0050910400d81c22039403d540c40134100f40c1020308022180e4005040381c8100039800c001c2c10b010417018001d1144503882038000304840e46403d943c01311100c402409440c40c640000040202041000c03556160136076120103c50358031482080140d0358038050441420805080300100180550044103408003562110b041107420501400e00b00180d8544101c0250046502008100f699001d0400e00d26038510000004c1240d003040404096160030880f05000d0018046042c0014002c96118030600c5900c02e10250141c0002001616002d210b103100720b60402d90f00081c3c1643c415200292103000c180c512205020310281c604000b0701030440c80c090301e840752000d20b0303000074a240a0311940d003240325003046231800c20780b8040708140441c24145c0141d040c000f1044000c2c840c1d451419141c6e01c55040701140c062a400e01000c036625000d074440d0000f408110224 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 710321798 1250 710320548 710320669
    0x4061202090a02090d140d020c09041e020a0515040314010203011a07150614180601090909050109080307091a0a0509090a14070306080c040615080411 66
    0x1c0c05158001045080582e4904c14100401d1a565030220041c001c0b6642108020ba410008a001402c51034168212490038609400b007140390070341030342c0040c120900d0000361442200010100300740c041c00100b2100700f0302e560f200842c2134002c0e50500d405a85e01c0005041c4104040c08045040f01c0280200840c00c540c100408554031702ca060300629038100020400c0020080e000517110300701403105006200f4140c0d99103e01d4001d10819112502c01d44120b07407a207004008080d41c691041105a48102060b80340540b01c100400680c00180c6180d521071840401282c03406008600594090f6900a6002e1a01c1003551216898007800399140e04c082040744402da40c41000d80303100b44002c07500e5100c01c1d100d48031640000c24121184480075090f00040140351501a0311000807211440300751003c10004204010803038145000312038075540c100e2070150110b841503550b01d61040c8105911854114200300203428150140300022031641060790194211500718078603400c40c0704101ca0307032a40e2541071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 710323048 1250 710321798 710321809
    0xe09030a0801081528020d05091e0c0d06090803070e0a08010b01050421060608010c0e0306040f081b060103080706141519090e0303071e080a02030606040504020d0b04061202 76
    0x900b028034001c609000c41d8450303844d4a58900c03240ba0301010110340e1f601e030070403600028040c215a0303007006010b04500110014222415503243c2000ca07800381000070301e01070401007400006001602e4260b44d80c86404e0005900c10000d500071170581c4c4468610b0311564003041080c148607080300705280d06007880c01509907000300986095400340341d1103500d00304c0080500800000d00d520094100341c1003403c0001c00c50010750142c8010500359844900070795135030044c50380d5201d060310018a400940060f5002003043d85018058605002c2071092950040d002c07030300d19012081c0c005603801c010014020082000c24403e00108011042c400c4041d850541505c223a1180d80d20543c41c0184200d03210100d81e034030200901d8024211408003000b0203440503205036643c0e002203400350046816a5034440d40c0420701c0d11140040342c45965100b80640d0b07052041006900b002d804a500013809101c00b2800756a140061b08600385160000685c0d42c4010040005a80c2190b00121240c4001c038814001f68842 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 710324298 1250 710323048 710323051
    0x17010905160f050f03062710050a060c1103031b0609010f1e0b010912031e020319031a090406050a0c1803030305090a060e03040305120a0c0605060a0e09030a08010815 73
    0x51301046922660345002065018048284550160343c110f4507030343d03101d0031640c0a0740c02681da08410310b10203500c88090012401050280b2008142c0403c6040000754000c58a42c0c5020000f8081d00d0406a83d0030b406d41003041c07685e007007184640000c010066104400d10030a41da0094508003400113602c60310035101181c41c00070001c0c00690726072410718142d0b4080c9a0341c6005105001c1000040c503181e0800400c1e4140c103443c44408018200d1210480c00e1000013a142c000c00b41c001d5010503601003880540003005450319098400001d4a01c00841d036640f00c061500c958015880840c007071a10307080329000c99006400603006d200d504120040c1c4280c0c9011000c1c1903a40c1418001201e8507071030500c915044100360024401b81c1007100c50040a00040007400c1142d01c1241100d2429050540108076030085c1c2d590701d00020302d2012420081075140d00400d07080780e0040c140305411512240c40034003484c0c0880380d892969000281044030383d9404002e1031b006200071030160040107604101a4000c800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 710325548 1250 710324298 710324317
    0x306010e06090109030503040b070201120e0c060c010e060c0711030105013b07090302180c030613020c060a0c020f060c0d051f090b09060409020f1017010905160f05 72
    0x601041c80b1503942d0040c10f1000280d6002011039440d40e41c0c614951005500511007240083c01d0410304081c840d10500600032071800a50282901c0c0c4805024410990041c60f2031803265034035601380207100b04080c0700d030900448036405403076520500da0604a50b4101d5041c4954000d03898103004004941702c0c00b142403e5a009544242c3d403a40b586555107040c8164410306400201504052040350340d003044004084038030984103411a00d00c880880c12001804643c1520307800000c2000400394034000d00945c2c0441d030001c00060800480300401407528000b110700343da0b82940e41041810290301041513001442603071008100a00e00506c0702013260043c2504254000d442e0400f2402c444404400701d0301d0f440c441c1c0f181f1112280d8036032808015201c40c50030240a01103002c045840e0307003064095507031216006440710b08000e181c10240001500d40001c41c00c20043c500440591420807189028002c0070850008030300b0b420441004014507040a10230400d211107041c0528000382c122058a84d41c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 710326798 1250 710325548 710325559
    0x312080708131101050d0608060126160b1b2e09110415170105071b081210050402040824220206040512060901111c05040c09061511030306010e 63
    0x3081b0102c4901900458000b08081d00482001049521901000c042600d00c600700c514034460583c3c0f5016210031024039840302c45500c03d5824442c01c0701450080913900441030b900480c0203c1c51070b1140c2000d01e1998011a0b14a120354900305090400081504e645034580d401c00c10010a555101050740c04d0300f076050f0040707850300300384814841020b190000811788a0000c410310f81800e9240390080c0803c40c0e60b400801c10310219600203410110203054000c1e400060580740016040402100f050020041c0c05414010580802c0985450009e030006002c000014400c4c6024090b25003840b03c55903180200b882484400c100003025404040090140c0c4145a402e40e8035060000c141c280c8100c1d049242c10a134540d1011035130f180005000d0f44945001d10080044a440942000032803180c1d54101201502406011030010226441070b500544100071408050340d4400130003040e203556030300a14102440c00b101c1ca21103a0800d40c0c107002480f210010b180345217404000a08070790100c2000c58000e8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 710328048 1250 710326798 710326807
    0x32b030f090501060e0a0e0705010e0105070c090f0e0714010e0d11030a0309090b0a0b030c0a020c1302030402030d03060803030703020703120501080c1503220804031208070813110105 80
    0x59540764001c2084940100080c03006607200c00c26405c0c810b01c02c2c0c0f00380244030300d04400c0c256040804542c00c82501c10580d0740c0031032400c5502c011105900104400c0e101d4403401403000a8941b954452004854203070f81c400301d0343d0840b07403401138141880f95014494401c07901c4090b07601d580e400b02403260030039005c40d07080700d03140682d04101580700c880c86c000c29014880c4488001c01d040d0071120000446a5030301d000c2c84811610428271426140f20710405990280610124010480750006001244000d2040740e5445c150480003540fa2000380c1c05101c02654000280825410144881c3d07965002509040c06440d203043e903c0d50343c0e480010051001c1550104a100400d0300ca03030702902d902c05110070705020558580c0001034481c4000703401240300f00a91801400c00e40400c0040d00d11404103910b44401d00c91483e00b51030304840c808082144c15200c1000b0205c0000c08081d041c00c0c10803820f03a11811145005500034144400c00341c140c0c0784c031447d100712002c0010040881a000041c3c286030450310f4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 710329298 1250 710328048 710328071
    0xe03040b07142e0e1509120409060e0c180d081c050a1d0316050f120408160311010c08042105010f02040e0106050306220b032b03 57
    0x240000340c03500e081d00c1d00a900340c00c1400e00d054600103c3d0303540300c801d5200450010071514000c640c6030000c15802a00050304040c140310440c080b8544c0f1850a405030b40404411b494010b00c076901c0740d080321440940c1c0d0a0244508441021907981c07142e0824001c4c1c0c988514240200348000381036a002c0d100740040100c150412440d1401c2d94400c0145604600403500c031115810080c10342240c0414070f00340b8006d41e40c00ea81100d05040110840c0400203141792175210340c8910100304034580b06403180d1182c00c907826801d02d01000229449000c1c022040e403118188100e1a007080c84441ca00c449841100c1401e2000c00c0d00807014200720502400d01d907014000d5442c1610791741c040c1c0da001c034071006c01944050700090801c81c50070608600c40c1d0000c10406015101980480c0203a0080207020047d003401840240c2c0144000d580041000b0540c60380248262a0070300c444041050031000c2a44940045e941414100000c1800140c07502080f02140114049080b0b00361000d11640b08154542f00752128 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 710330548 1250 710329298 710329313
    0x80705120705010b03011505060d0e0322140f1806040f0608010b030111030c03010621050a1416050a050901030902090f040b13110603070e040903020705030706030e03040b07 76
    0x300125a040e100c0c0d210344060609900074003900c1000340c025404c3c1002c0e816002c1c100138000e401c5e240d00426090070080a030b03104100a003048012010544820443c1081c1643e40440600807a600d020014072000d04200070001411200c2610901441e048014580782c0d41e0740c1e283c11824880940941401687c908000901a08c03401000c5410746150020100380101c06400980c41a80190000c1c049084426842141b03484200c45028144c50300340014090103108015440100c0c9074000354241d400b0014a002003110310545594070100d0355154624a01c040c50000c0750f50010401d641101240900038001c4c4c03407445500c5260f400c22000154500c647d07800399000b42800d5401401c0704410f441c0103184040311120613101a5400a10035000ad0401c04e822540501c08952001c4054200c107001400c0c00080e81016000001307110b07101d410a06191154400d80b169540264010311a0300d150405050410740c0c190806170030503080160f20300c4045000001ca078229a800c00007150748070110304243c41e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 710331798 1250 710330548 710330563
    0x50f03150315130f0515041401060b03100605030402012610060e18090f03030c0a0305100f050d03170f0411040902010e060d1b08091e0a060b0a080703081b19080705 72
    0x2852840c8078011f20041c0680c080b140510b906040000b080a80c0e00c850351541280411510b801402c0c0c0e1221003400020b102d00041c541103881030420b440046602c0c11a5100320392a680b8810450403103100700442602c1c00000c2c80c00401150030601103100d030f1070740440c0307408032250710310403114100c5000700350303017601c100078266209c08480c00360f0b070700d90401c00840090380d4040d00e290800241041c1c0410307881310502c400782c41181c2c0000c200d400d41518220a0104c0c80740000c4080c6c0c103005003081c04903151688903201e940701d4800341c8020b4a842c641880c00c1c1d091100c0407051a03001fa031070198546d00507604001720418851088905948500c2c00403070402c00b800c0600850784015480e42e80803020141c01001080c000c4480b8826694450199101c00c44100780007c82c050b080e41c00121a02c0c08200d031a03010f0b46030f42001411002299444a41c02c9d45055625401201c80d1140018285c001200495000c0e42621264000d84820000c0c044021395000d00c05902515844001681408210007000313400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 710333048 1250 710331798 710331823
    0x9040609150905010204090b12030a0f1b050a020102070e13060b0f180f0f07140c01060308030c0a030e0111090111010902090414010507141801050f03150315130f05 72
    0x41c040038402c0d2070168041c1d0024460904a542805610000e03464090194101811528019428030420400440e0b00c2110b5100081c2130003c2c0d0540c00c00340050040c00004c40314014030051240309411b00c002031400501e5404440641c3e000b205018141e403021001c0e03a90f25410040c00b05400345a2000501c4640c600302e0b88551260b049852000c504404c003034814407400201c0e02c00c186946c0c845000c00841c200c1258010001060501316140e4070036924050700748242302c04000a10251603980305e0041340d0017900c940000070004039140341525450302507209806001c500a100080140d0301c50b0360359008501143d8140441c0544079074080500758040c83d0240d4005104d103500c0c2c00d2904001c102e00c0c500e4a0100c41e48e508000002c0c00680c0981d0141c581500317051328092900851010b6001c0704102024104d04122080103000c0c0c5400724100074501814650407000040306ca404201450202119214040d80c80710310304002084110141d8074074080d401015140f0507010031300c2d1035400c0c0b11078070700e80f03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 710334298 1250 710333048 710333051
    0x28020105120f06030d03140406050c1b1c03090b0c0306012102030103200108180a0501061707050a060c08030a1103070807020d090b0f180603041101030c030b0904060915 74
    0x100002071082090b02da005403401d805441c81408003140c114180c52011021040c8144400c02240000f00c169010755444403c03c0300030341c01e01e100f00c0e03030144982c01041285805a0701005104c01d246130b500b80410b2020200341010046141c40da80c03111b00208008001a4040e01e01100290003039004020101250800350344071000a0000700c3d030701000350800c2c082500e0144001d00720342d140300c0d0b06620410111805861b801d01c01d0b50380d015020b00c2a00003001483c10fa01030055140000313131090141ca400b410710f01007504585000707000c0551400c4150b82c41076102d210b54210400950b40c0024040c520180c0100007141d80780e4841011401030100390442c1448100008100020240d10034031260091171380d5820341d00014842c40d0201c41408036406480341020003002040040c4d401a00145000c0c803001c1c0c0000c5007001c0100000f681030300101c0d8103481814030303050354401c0c1d585c0c18403400003000c4035420108806031003000403c2e05180020001400c8a90f9038100c101407054060aa041c1c8614640c5c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 710335548 1250 710334298 710334301
    0xe060406080a0c030302161809020f06070308011a070803190212040813050907140d0b180709080d0912060e01111206031504260403061d2802010512 65
    0x105080060107510041d4014000c00c01c1051080d08486c0000c41108c410151190b00c081c50340c03600c80024410000102c2c1d1006040028400726210400a051a01c3c041d40311048a9854042c1039004200061410411308200300045030012f0b0744482a02d4100207188840307030002c400b000088000744203111700d04150710940c004100070050342900a0110545615041d00e1165a0394184403000800ba903130355012501496070a08207008400c05402080102c40700850340380c1e4080b010516000204070401c4000c1d5096082181450700401c00302e0003407010380003c0a0b10304162000800300b90650040045210110704920184281904100e000650f020b00030841d446c12000e0407600c0741c1c8031115141c1a5841080041d036245404a80030b000810311070628070a42e40d640d91500050004c0c000c1181c4160002c0c0400c40b00768034040e0140000e18880c0a00103180000200300d0080c541c80e59107110301c182d00141d0301600701d81c0c0051000c5200d0b1002c0c1c03100c0129403c01c2c801691240203c541000241c61143c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 710336798 1250 710335548 710335553
    0xc140c06041710110405061305040c020c01020f0708120a0c170918040b0601080408070c030f140a0c05060c0f2a1504030210050d0c120e03070c0e060406080a 69
    0xc080d40c010751807402110460415007840d403080c1c13001c055001840c42e005000c204010708212004204564006184050090b19100024100c404100036400140d0100075a8000707940c0400002c1501800c500040c0b20701841e100c2002d5a0341450b824407440c0d200007041040903940a5030802d44112381c82030942202e05034004003074149403c90f02544d0b1080540700000c0030070a1544c0582401103404c042d900700d560391000015949144064403c443c0c42d942080b07101c2c00f041104e04000e001d184125002d898001c1103003002140112001c00d4201c2d190000203220001070040e440c000121101510115210600078a41074105180440810014010069001c41c2c00d1021004544070110503403000c241c0c0f0070f80d00180b004401c03401c50070031100c242c1000203101515042c010540c0c906028908986000c0990410700c041c0e540e1550344d140131541d0703103015840c00c414902421341c1030000e41008504101c602e4503400150483c80c0700303a091818904012078225105c41c1c2040c07000e02815011110351240b40e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 710338048 1250 710336798 710336819
    0xf09050a02010912081603051e09090c1c24060c0b160903031b0c03032d1713080301030317060d020f100c060609060603060b09010c140c0604 62
    0x100d00300c1c00180007400106844c807201480e6140c0c29002507607141002c42c2150240d2001d5000314081e410301c0800c0c010780c030180300751160390354a07000e80001c40c544445202d01030040c41540030704005a030324424040049030816a28030703060944032503140130441c05884683d58042400c40700f0b211881c007480c0c00000c0b8096400400407a030040c4500d03489d41040e40d071094851103000c0f20000883c006040c03620f042010912910121a07091210386600386103104a07940c1c07403684034059004401081c501400c200110f442c4030399140031aa17084281510a040c030307203002030007120310342138090300c061a1501041c80300d03480d0080b00c1c1c50594014a01c60362035850b1308028203105109114000140c1c3c080c0009801d6007414803490105a50103054207140960000030010016083d4207400f04200f030000000d40031a5490080038010301c2100c4000502a052001c01000d40f0030035085000c505204003c2d03201c4690703015140a05243d00108070252035000520b80a0418010455041c2d00020220b000b06106850 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 710339298 1250 710338048 710338063
    0x402151603080604090506040321411b040305030a031401080a0f0308090115151101020306150a0504150503150d0302070b0f0f0d0605040b1504060507060f0905 70
    0x19850302c103503070b40e00c02041005480403502e0080c003a4220801140000e030107a0811008401800e000480c50194080c200c17088a0014840b068141038402000c5810000700302440740801c00c2204d03850340c103287c0001542c00200064051200340c1242281480c400c0d0044050310b000e1940241900e541d80d1000200601811201000c00d40c0e140703284000059001000400007401075008001160101c61a101aaa00b00005050041d15500d80c400080442d203074018010240018203110845503075000d900408940c1e82102c0402e00c3e1f0f20410a001503070703441001d91086c0840000841d60350780b0450104031a5409940d001c101d42d24805104803d007282c1200185111725090300e40806004203031403c1083e50b800c95440a40580c004c450b0512007032800b0002007401d480f0708001240f50071490380522040da4081d800702c21459944503014000ca19040c0120361840c1002c48042c1c1007042e440903c514648660701c54039080c860700096103000c1051030f070441700025045031410450844e160810300d488001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 710340548 1250 710339298 710339303
    0x1e120e070e180708060f060a09090b07080106050406020318012a0203101a120c100801080f0705030d030e0c0d060203151f030b06070b0711010b01090b090904021516 72
    0x800104056140340e00085410807a01c4d03141c020301841d1a50090041d8200c3c014203050307000004d0f46400300c1c0c0003c140c094203001c14412240305825180581c0028007002041e000402000f000300320420115900006a80410f454030040950956070b6000503200d100c1d21141e4032566200b21080401c03210000032900e44024002d505841d2159681d560070700031154404040c0103e030038003a43d070414504080c8000401010300f03000f207070380041301c00c00000c040300f113504054000140c1800060140031803c0c042c450100b5041e00041441c00d08000029071100360404450f01010f036200320848045008001c110001d000281c508541036180742040c501a6100b107650b00c80484039001c40110074200148148001a21441c0403590106540800c4010301502c03d502c5178000e005022034408651540d400c90b00440a5442d1504040d41c40050142034640d403455250600c032070003a0030030036580cbd59021941c150a0898400c20556100d100068541030b01c801e49801d40c0c1c001040c1481046039801a03440841e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 710341798 1250 710340548 710340571
    0x106020f0c0a0b070c1a130e101208190f0e03072907060203090705030f120a1103070c080102210103020f0d05030f03040b060a061e120e070e 62
    0xc0c0c0340d16180d80da5061a04806800800c036100c10800d400c550300107090050b21611250041d181e480c0e100743d0420300310a00068144c180000c240000c14400d2403101c001b401400b05110342403812140c80d0303410708498400c0250704441008084108464202250520a0351001d2030124118008008004180c0c2d00301e41004600c1d0703c4420740d041d103000a0420102c500b6281c0b900740000003030807020010041028140c111030350a004a41c005039250000d036100305071500c01004900d1401080501d400070752031051130140c00020003405240200e004030341d200009810581c01d840500880310349140300e1400041c00050ba03d03079000c641040190020100c00c402a800c030640c5940307031051030501130402c0c48000d6003c0c0210b080e0142606103d081d603d080d5010f80c051300d081401004101e50558012201101c50950420802000b032502840f103402800c42881c1607000840c200310032100d000310140c890400c1c0309501d6190b880c0621240c1041d8a0300c00b5290684244942c0e41d43c10004030030f8259400d50005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 710343048 1250 710341798 710341813
    0x91a04060809010b030a061d2b08090a0602161b14010e01020a14070b0301080c04050c0901020a0609050f03040303080603062508060a090e06071106090d0e0d1703010602 74
    0x200501940c13451120080184c01e41c0d481d00d54801780109103c0491100a017110059003c03904410b020b04c5c51241488030313540c030044009860344804080d10110f54000d2050290520094640008003a0070150f40410b0050f6112403540d00e01e03180d8020340e200101a203013840082c400003200032050800300d4200024807040007040a0040d00d59500d004840c900690114442c88081584d02c4400300c031407503442e800c1e1911903403685240061548240c000380c0300f6502c02080c8072020708103071040640c4050400f6959003401030f0000000c2d1981507049015150640321030079501800700c1844130380c80e000c0004088950311035a0785070180c503ca0040391014401c5c040c003070009009052426101040741022100e021614000e15810344000c01c019000c0380e006500454040750355105031251440c4070201400604144ca00490000e11924040007a2075841e0091424042060400180c041002071030b8200303269080e0300030b804038940d24291000540803a2907c52660300e94084c10000718161f410304c1c2e0a59480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 710344298 1250 710343048 710343061
    0x910050609090307020d110402040305070e01090203060f10140c0c03010e07050625020d0b150114091e1f090b04060f030b030f010912030f090506011203091a040608 72
    0x741100d01d008540c00c200a03000c01454001b020030820b51003010b403650084081c0e0003040c100e812582040b02c0c5a03214240a00003c076071a0086c50040c0602e88040d840d43c03500d20701007212a030313007100e03264001c0450320340801082d40a004480b100703c3c15541c00c2c42d2503268650b249a40c8a9504804a01951030b220710340003241c5c070201e0315034251500907100a2400c1c0703503c041942880d272a5407940d20b03e4041c074a08900103035503a920307081120307000380030785045d50620300e001c5001000d8101d40036040c0407411920b41c5134009010241c5080d10b0307003226240b08101e4118944902060380c140c2c000d6201b589285240c2203400000b0302001000150381c1c1f540c15903504e4100051861042d03000d80b202188007407201d04247c2e03220340c000c0c02010b10050700360f9064106562005083d00c0c0031210480c0d2410f000380404070150f60510502c0040007030400c0038072a0118503184c003074503444180154410b80c18a0315140c0c0906014090500040a10400c0403035507440c1c0d41c0082029402034014200044c18407004583c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 710345548 1250 710344298 710344309
    0x301050a0506100c02090705070302121603110327060d0f0218010c03050301140f1003060e090a08070b1b030f15182a161b031a10050909100506 63
    0x74690703019080340351b079496003e01502d040d00030b101e08408511601c1b1038240c50030328410140032440b0f042c10503e0ba16009500d8040c110780b0280740225160b82c018003402030710302c2082d8403c0990508000010040b4a0888007056442c0b16008211205c00d09000c1e01c40e402c035070720f64000d21180c00e8038400079907071400303600044034464451034010f000640c05000500c4100d80300400c6160001d40203001d0650740c600080490008540000c00c48003196030344408211010402160380c2d40070700d850b005443c0d0501c0c01e03540c0381c0b01400b554101800810540700003516440505020180d00e40c40d6004880d120b04e000c0742c0007010000c0c00c407400404401038031040c480743d04002807102085411000424025a038164210300c01d00c0d8030b104000c810205028414a02041203401030112091190141e0074030000c500342440140c000da100e4111028140301c080011904040716a042d9003c0d00d8042052915481c0c43e0f080400d2694100d01e83c4200500b0078441c0480d00000c1e85540b41c10100d0090140d41d40c1c0030100314 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 710346798 1250 710345548 710345567
    0x10603050304140a18150522051006201009050303100f03080403020402070201030b060a030e060115080118090203030a0e0414093301140909120a030e0c0301050a050610 74
    0x1c2c11417000b9024050301419500995031110380000400c68042c0e503000010801604088280304030fa0555403840500384d82406525802640841c1305505c4516069000b001c4551004c00d003403818900c1c89448c1c800c400280602400100e20007024088541c0b90300384035803240e00c15580d02e07000c0148014005030065081540d402140d4002e613407681002c2c5181c0901010b07521529040341007680c4c03000135111594810000e400c80b1980d0b95400200a0543c102051510301c2c1a04245495070483d00100c0003162301082050540701e420168a500c42403005902c3c018021500c4001e51500000c00e002005582c07081950740701c620100c50611100000318501c80c01007105aa8001d09a0811202c450b101c031940750459680b045207094030000c2200c1000b100d04030b00b01c280c1245080e0601c0440602d118035011031040e81004022001e03244420003140b000d0400d21410f10342106050b00c2d00b201000e01c0e107040c041f801090b00e016000344414945450311500921044035000c0c850408420076501c0c642c0309110300d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 710348048 1250 710346798 710346809
    0x7180b03030403060209010216030501050919020d060b03030705010c021005011706150f0a180b06040f150c080a080106022a1207031707060c08060d0f0302070503010603050304140a 79
    0x1c600c2c00d400d640b0703110041d62001068506512074080001c0c0010001d0126100443c00b6000008076810314040060400c4400c0e1031203c40c000d012022840981c0d0303614040b8011aa000c61300044403080c2030042800c6000e207440151455207410043d1044d43d8021079180d14000e140c84080205a0701c62041240070351894024800b00e030300ca000002c0f140100b6030707800078100c10000c000c0007034003005900040740d42c002500504820b0b030400e200026940a00d01515800420840700c003802c1a0030050181404075032882424260141c03000381c2122035008030042d0011a8004550540d100c1c1100310160511000b8840d400c01032144050901c41504001100c09540c825902400001e07480c070001c2212a50340b007444480180500c10002000030041c50210388210074058456480d021103090041c100c2c2c070a400c501007032049174010030000e030b60740801c0310010310740c030480c8203480c3c14041c2002c80c03914085800142e010340c41d064010050184c004050001c0710012200704118112160138040081200c1c401c0303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 710349298 1250 710348048 710348053
    0x1603020613080d050a110c07081e060a09030302090901030b060112110a030f150e0403092c071e090e0901060b0a14070b010f0311010f021f06080601060207180b03 71
    0xc0f901c0c00c240d01d070400e5400080c0300b01c1c0422079514614400c02268000890700d0032035440f06404001c0b00790140482c0018080140b540071988008001050b01c0d8400144003d00040c0d075403410004050007581629206000500840203642e1286020808043e044d5100303404900d595598459000c0d4501400640d00c110103d486c0c100382100c03406070041d00038003180c110101d07100c00e4440ea034000340c507031310b0f200810726110303030301e9183c00e1070b04001d080910f440d0007407144060711410f44030740b4010310a0305071100c042d28400300341c05644514085131191403400c5405066103121081c1c000c040d502c6070349881511043d92030680c0c90b454449c162422101544030b02202c101041c0043c10394507028096242c3c54000204565103020059901c666502e03000340c100d0440c03229001d005105000311408203a01020f02805c22050329460020065910282000c04807040c0381014840b0071000240d40200b8000c00f806405c558070b55231200e102940700d00341c1c1d00031055122401400d11100701840d00a206a424002d8003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 710350548 1250 710349298 710349307
    0x140c0a140405040906150b07020102330a020a030b09060901060f20101a030618010b0d20031c0305041110020c0405091b190b160302061308 61
    0x9584050415040c0d4603031220074080081c042d2514000c0d41c041d94800c160008032000c9404120402c1c0302150050584610140704e03100050760000b41c4601c0459078904860310160070203c40e45024203408100e07210084108003405012222600074001c1021162010301170030417050280071544004139100396002014100400105015911440c808038881c58424829946c003242c00d03451700c800383d0100400d544055040c40400b8124484c0e074400d000f07400d0102602d245081c000a99400002c0e120255a04040c81c1c1c0003034022007540684d00141e400303020002d03a52081d04004c0076107003811130105580300340c81894103110319012030890703010000c2d80780c04440f0648001302100108070041c02120303040a602d290030364542e00c02c0b81020003025603900600300600a8402d000c1614005490b400441c0d00101c00d61203658020f4841d01448482921305080c4203031899402e5041c286540d03c20000071000140e8822100e1a01d140d8081c1c040c083e4080740c0c0c05445500b1684070030070111001914045c000e11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 710351798 1250 710350548 710350567
    0x2041d03191e0f021c0203032e06020309040b040204060909020d1404080904110a0c0828200601030b2208040b0a02070506030108120c03121009140c 65
    0x3071190351007040d1450b02d6112000c1184400d005000b0110740c00e030103e001c07628a4600c040e81000f4207044c9185002c124103042c59148000303580c07400058460351310221940d8032149800e030021510a0b00c0c2c00009400d030091aa1403502075143d60104052501a5060102c06444e60509008840440d1308c540c0e0f4608942c1c0c0380002c000c0087d00f148503107144140d00d5403020b142203032500c841e0714010340c02142c00d103a44005140420045513400c06038113840c50320500c0220712061304003101800a640000082e96600f60350910580300aa146010090444200c1c07035524005030b014110340c8250034405400c51085a8124a165032050244001402c1c0100e102c001001110085011b5405c3c5803119107000c42c0400655034418203400c1030700030101d0071402107580d5500550410001d4010201511260b1030344d41800340c81b544681d00d0b641c04c0382c84e903280066400035001c000c2085403c82003a40030000543c3c10088562260801140308880569091004e03040c00f060040c040103018280c0369800502d4103c828 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 710353048 1250 710351798 710351827
    0x801080a0c0614070c03110906030d1407050f16051509090105060904140702030c10060b09091b07060605100201140609100e0408040e070504030309141c0308010302041d03 75
    0x24a10302e5500300050000301c0001c0c1c45c030741d1a4805180300300303004146001c0380c10503c442c079240140118404c0c0e01180100f1784241d00308801194642070707550260303551545800c9c094580022110150720920440c16542240050920100c003030359003c94242ca041d0300038606000c01d501031494240da1089921004001e903251290003001c41f03890181010074803144080c1c50800d103c10458500300980c000040742c0e070024006008010a00c4c080c01820070a050500d114181d8902808a01c0703805218800c01003030011030704044051441307220702021540d40c00e507864180080d10080c840d240c004d441248204400300d0040c0640201d00e0006486c10510359030700010400140300103003400308518030b07005c0081060a01006010310aa0042c40c00913035980c5826120b40c65944024048d40401405020600000750300800130b20407150311018413618041c1450018440032405044451400202c4502c0d004068100d44954122402104c0c2007140c42ca0406102d80c0324000c0c1041c070300c0690402c00c403410142c03080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 710354298 1250 710353048 710353067
    0xa1e060507060609140402040501090903120c032702011202090904061a04111c090b07080a2c070f15110307020a1e05100f08091f0c0801080a0c06 64
    0x7100003280f01c0f50b41e2481d69085860b82d210703030009950508204000c1d0704050069038010500710104105401203601c001345805c16807110000f40c2d94903603040c00c20052213604500100c0c0c0c0103002c5540700c0c2c251440045030312600d20108030b001c508030b8061410116814801e841c1244c60103001d800c0c0ca07a446590361801080e41103460132070303614000405806900e4038407030700c01218503449500343d41d000102c113a0ba41c84403040c040740112a00f40580240000c5450207a41c2c1c0201803030400301880d450307c1d10400d0203010509400800341c2d078010800412221070f0310b0100d5800b25420155065140c032000801e00312034140c01102001e8031107000402d402c40c032641a000d64566407100741c80c1000c026500051080419912540724142030102e6900c0582c4007280c0303e802007108079900e644440c48000040d0080c1c1e642e08220040c4521700000440e4690103000300034000c0400040c2d4048061220341040040a41d01d18200c006103080e00003180c60703a00000c80c40980791700801c0d5001103d140c41c208548a00f074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 710355548 1250 710354298 710354303
    0x80a1a07090533041a040501090302061c05070503041b0f0b0a14040605120c04031a07020a0609061d0a0c140d170909060108040b041e150504020a1e060507 68
    0x1ca14004110111000f03695240c0c200700e80d000e0744e0328034280f00001049000501c0704054001000200290303a009050301040301d9040d80e401c1d031220421001d049480b00d80b1045840c020f42007004000c211988070340103621851050b0071301e440300a12a565294081403600bc4c8602ca0200e040044c0054190319001d084d99840a00e03003d5110186403e2071441c5822682c020340c041880492800106c1c1000d806150744140203001260609203075403107240c074a02c01900800340d8904072402044815109020340030307540b60000001d00015540d8a030002c01805030300c041c102402110900030214001c046440402c01c3e403c400c1d81c2d40b107141010020341c2c4002c085030b149644409001c00f050001000c1c0c1c08200c0d03035200b00103456515a420f010a10911000007003c8034100f040e007004000000b2403030320419030000d0b01701074a4044201d07645103815103a0041800a0003c490345900c2c4d8038080b4594100781c0c4254030a5a061450550321101c4810700c141c48c940121202c80c003101c0600c1403512a1011f846e0060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 710356798 1250 710355548 710355589
    0x8011d060624041707030c06080c071509050316050705010e0d020906031c050d05060607050a2a03080306040609020f070b090705060d0506030610060507080f0c07080a1a070905 77
    0x3a512030f2541085421030070014010b0708028170410034406600001c00040510703081008491910912a003458440d0910040c003e100050708040041981c1d8005981158410300b1240c0c1c890030103800044007004014122403034404e04038081001d51150700030300c803075240280244234006265070800003201802406d40e50188100107a230422034501c400c507080c00071140d031145a940c080700300c100d10903110020b1107140504020000900061000551074080940100000c44078004c0300001140300414082e0384000d480354050040140700d1014000c0d030040c882250204021655184024107901030703c030354920700400a000c0d040102e10301010b060b03449101442030745d8500381c407800041c2d540d070032541032038110715528010095282010400c55810191007000c1d1040c240c54031100904901c148980208100c6c3c001c41c1701050401c2c42c109458072600801d0a4846a944882d0259036030401c481040c1c8544c02c0c01400e2118410391030440e1401a035072030b640d00c0070f154107000a01c924030420010a038244c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 710358048 1250 710356798 710356807
    0xd0b030102040b031f03080406031e020f04051207030b160e0405130b0609010b0417010605040c080405100203010f051e0d14071707090e0f0708011d060624 68
    0x165001e10060018003201c0843c50b80301e080504010050705207965450628210351801071012030403c45c140c0e001c58202c0d20300031600000e012072002d203149001d00181040c50000c1104402000759402801c00c0d030b0340c00da0b01e401aa41c444117059588840300d10000e80051100008a40d101390040e201a0380b00011f1700b05400106d5041001c5001c6078800c5541103c07005caaa0203030020014806843c91300000101c0c0c0031001075041869600c501d10440c0f02d15802d03262000840b5102090039040f800040600410800c808014800c010303144060840e8121000d0003002e0111007401e0360351080d00d040c0c070065407206104904020030f0042c2e02c100380411a810500002c3c90b03012030364035242c2c01b102e400e10486580d200c0500500329540f81c5800307a00458075540001d1030040b841030f0005209812604211400300310214040303002400e01c0b1507102000258003803800003003144081508502208400e822041724800516000507440c0c0c18156003143c1c0c001d00d0180041c200c020300c150307903150310300010b20204d150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 710359298 1250 710358048 710358071
    0x1704081605060f150405070807030e01110c0a030e011b0809042c06240f0f0a090b03160e240310061d07020607050a090b160215130306020d 61
    0x1440740440d0039a842c9003d000421400500322800a428407070f0658045c401400c003560050079250004108008141d501d101c10b1070081001d400c00c80051409a17100f80d0768100000308952600c800e01400c0d000315041c204503009551190702c02c030b0079407040714032030142038989070b030b40d201841e482071000d103a009464140c40300c1c041407103d1b04110b001c1012400788400400d4403000034182007000f094020245410400c0900080a4040c000c00c032910440318031001c918207000140104124010f001e0b0810680000030460f94038603484070210150071011207802142000344444001090300602c4010480d01010860540c00303201c091605032003c0c00c00c0c0300d55910800110785880c0e0b08038403d4011507103603282004501c44035400320640543c801c1c010081c514210f100130396034100141c0032500700003000079907880b558810910007000d040c003040c3d82541d9618a0040a05403400200b0aa1190910601d440124040c840854280176003610a0b0340d001c2d840c50300c0c2c0d48001c0d003101440d0780c000d5445074801c542 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 710360548 1250 710359298 710359303
    0xf060a0e1005041803020d032304020a0b13080c09040807240c090504060b04080c060309010b040504030c0201020d080906151207090c1403010506030a05060301020702040911101704081605 82
    0x2404d0011505140382840303e800c1c024a4540e605440300141454849651018500d80c3e0b04c0001c00250700d005003c09031914800300300070740c001354801d20900c100801c00e90218034102c028142210103000894000c150210704010350b090065400401040e0704204000010702102842a43d0003c0c00311210092200c013503c103416908041d01080010752100c030184802c0c40d0910800018210b01e50400d814035081c11181580c8090006940c0e10502c00440000d0f00b075042500804c000001c080c10500c0300f820300b8980a450404401c0c02240940140b00440021070321981c0c1c050710600521004006a86403038144d02e607114080440c483e00b10181034816040e800080085000501180c0d0340019040707000f200c014030300d40c038403600004071400400040007143d0300c00c02541d0b04086d080c04009116201c103070001e8024480c5000c001e400504051195090109100c0307800134000064400228141c08c11408444140d8001c04017903441140c00d000c98003007072003071015040c04c18408070302102c07001e03880c0c540a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 710361798 1250 710360548 710360561
    0x711060408190221131d1006030b1807050d05041202060117060402090a0605030118020f030a05071401110f24190e010618090b0f060a0e100504 63
    0x80d030902000403440705000000d4114034840342c40c3e01c0038025400000911469010304070100702e1201070003240c5890108907401c0741c0001024110700031010001100f0b01d441380b5543c125161140082c2044000030064007078001c00284c4c10f0002e0001880902060415403e000043c16100800106012603c03d155482c0700da80d000c0c1c0c2c0642641400541641c4c0000d2a040f030503004035030f0810440c5800710195800041c0c098000d9411a420415903513150031400051550703900a41d49503090107a6115403001c0c031159000601e0003500c0c0d1413074605031b042c1407642d01c450760040182580e0061404105034508807030081407510052414030f441d40c84101640d0310b007212820514409401946061400d003049c00120148813040d0540e503a00c500d006036406c0d100f40507440c0d005101c69240e0341040040042944004080c0c041031030301900c0822481c003441c00038600a2011646840c0900200b0301d161411040c2d54810900101a000c00c40c0c24a41ca051041d080070b40691403021900c40003090540d210301031320 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 710363048 1250 710361798 710361803
    0xc091a3003070c1a12010e09030d0903050a02011103061507110d0c060206061008160c0c08010c0806030f0309151225030e060c1309090b0f0c0c031207110604 69
    0xf50700f69800e2006806480044e0710710020f804a0400c070181003081042001411590042001c503440e40d06c40312494290300c2413030411414585448550000c0640000113400468440e078000c2010003000b02c1041c90f42c1c80203840c4194811a24103004140040c00c500030582140f182c0f0612898040b68000b280308200000811214214802c00c140880c40e810000d0340e034402412541ea411740f4441c1403025081900c00f80c07034100384c440e0b021403580e041c600556003a0200d42d445046603130f0b0199540c02c0c60b8020503038485184006000c010101d4140d02d8001850592003d2030380107940f8001c004410802c0c0c907150452801030b0b9400611002e00e03180409030125101e59900712202c5254070b41c410001001d074a0401d9110240351408000303002d4000b0010359248c0c0007100c01c0c2e01e91307503c102250008250961980c0400c0d400c50500e0a448100302501c401c0e14084c80845403207450384e864081482c0c9107401403507444026070381f0038080c1c00018000394070103d822030598101844070b4155442020300302003003210306 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 710364298 1250 710363048 710363063
    0xd02031005090705270402270702070513021c0c0915030911101403060105120124360503060a05090714090627040c091a300307 56
    0x1c001c40d04111614126517810030504100c540c02e883c0d01124040400f8002030300640002d580d1000c1c4200a14046c480d0040d0700c2d500e0b40d603610340110020340c0e0b420b5a00559004d00d00841600b003243c45507000317036a00a40c0e1005000d1801d01e82d044140c0080c40d500b00c0c05c90800400100006900d07a0060b05044140d183d42d4000c80c01044508118110820784a40680500e0281c00d0001810340d1025800c20003082e4011090390b25181e4800407911750103103140c03804541155100010b00c000d404190160300703401c0d800c1000d01501a0170410f803480b01d089041490600201680010b61211002c022241c2c101204820044207444101180ca000300c2140d012499950703030800c5c051034640030000e480c002c005941122540402802c04200303800d4000d4002c0780940301c2c3c1521407004071000700603610042c00b507010b1004c092416040104803102c0f039110b180340c454034007181002c8144144480315040080601078405917044848030200786001058021080703508550b0868141005000a00c000b074002c803074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 710365548 1250 710364298 710364313
    0xd03030f0c0801140d030e060d050f0112081e070c03030e011418130209031606091a0a050c0f0303010906090e190807110a060801090f06080c0d0203100509 68
    0x240c2151811040902884035000041255080c009084100d800c81680d024020281c0d602c1c3c19922103a45000b81d962183d404075504c40004829030006106500d010402e4500d030f640e038003c2d4180440d40309009402070307200b0400a0000000400199039106410240d070f89810302c261600300c602c0d05540c0048002440350340a9000c07079a44060550b95500703100820502d07210404111020944d00001040c0c09107101903205904070400d40c1c1034414450020b0184c0341011105007080760061624011800800d1003060003251074140030b404e4213140690300a20502d030860305201030b20185c001004c201003070301c242c4010285981c0280b018500804286101060060525420401790307258804402100e5204007828214075401e1b1617100001c4d50044540380d9190300505000190610ba0a58a0f402040c0c4800001780305a0200d00c403412611a408100410b0780c82003290410766241744140c02c00399104d20300b030500920301800300000d003134802011507010182c0c1c21a50703015a841200c61403115001285c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 710366798 1250 710365548 710365571
    0x11272d060111010c1209080c01020f07050d0224250905040b06090607030e0a09050c09040518070614130b040503060709030309030b10050607060501031205070201140a0903020d0303 79
    0x8075106140755024000d02c4002d05142d001885c040c08034102c14102c80e2500c000c40e0030301c0f41c20002ca6000c5410000255612012840000c0495110200031104c41c49000c00b100e003040e102160501008005507090b50380034050300701628507000080c00c00c0c9040c40034034000003001408802240900c3d2007513121090b406240004001c101c440400d0003d004078410080c0d109695a400101e0b554140c0c10304046082030540008520050180c0c1c00c021019884c043c10300190b428540090030b0b1807441210180a603548001e45800745014000c1080c405510000092041e02e001c1d000702041032803100c85070350a003840f41000c508081d4840c0c2c4a28910300c00014140510704044c03004550200850038454005880c5030340003400d100903031201901410000021515071442c0c5040701c0700509000700940d44070300c4141802c0000740801e120031a5107440751030106c0c080c98000d5041d90800c54058466840b2000b4041c5410b901d6401014014100041c8102c040016030b9009000380c80f080c080e03600021301d014400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 710368048 1250 710366798 710366807
    0xe1314040c0b2107020c100c02150702030d0804081e190f1e02160603050a0605040b03031b120f0307020606010c120c062711272d0601 59
    0x64200810031001005258038500300514519403048103610f01409603500c030342e01281480c0c2c140412a9100580c42c4c40002c096900200149146008640148020704004011201071265800081d0113400820000061074085c81d4440e50250040041c00d00e04212850900c80b00450070090b06401c0301e011a42000442d404001c0c202401e619040292008011840252100700c0e110300d854020310554444c281503d02c01d0008188a8004030003ca0500d074455001a01400c03080b180d0122681c90444001110300c4c050140143c3c194014000e185031544130025001d0b284030030200101c1c640302e41003103001d2014698000f0410300580619403901e034107000c07100070705142014081c181080302a2040c20041500080b0000030141c1c5410b106000d9940d52501c01c1c0600b065403400c8004081c3d8000e5401015860710000e156a071281103154182c4521108000705c20f0348401c1800300e52076240d5141c039100c1c0d001ca04195003202180300c108005680034114040d540c0f401c035081800e410703540030600c040d55801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 710369298 1250 710368048 710368073
    0x10020f060c0301030b040f060e1209030f2e1805011d0601140607060e06010602011b05031512031918060c050d120603080d14070c080a0e131404 63
    0xd060070585594515102d8540305040a031000e0442c40907500100d0800c40c85a0081500d0b0810074207440c5580300c0510200900d4002d6000c440c0a8014100115421840490000711180c0401002c500e014405624a0300309071221186e0b0070040d03511403c0951715541d8441d1580321900c00c10020403920380d110700001800750f14130b9014891b1b60240005015040d0710009161280e601503070b1b26038440c05141440409000031000c0708107503008002c000b051165064020302400e00b656442d405401070071200488251000300c0c0e4100a0044484002c101441c00c81045e0780243c2d9440122800d201d0f0b0030b10f0001301503941c101c941b0082010b425045000d075103c0240100180b043c0e0812a1009065403255520340640319200c2003045400100200d6000099100c034005e184c000c0c030030a03114640c03018041d008120000b180c11001c503452000440b072621511915211a034004665824000321441c16644442c100c01104d0703001482c0c0490040a0b00c052143c803400c2002000f100ca10360401d030900c01d203003401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 710370548 1250 710369298 710369311
    0x60747010303091e091a0405040c1a1303060902030c06120105040506060a020a0b06012708010e060606040b0c0c090c0901110309010f20010504051501060912030e0f10020f06 76
    0x8082c004c2d0150407030515044411605046408140c40302d030b0b03a0480d900300ca04021000d0b4014501000c1c4000d20960b21010f10a80d88a1010601041000031020304203001d500804a13941124040078070000b001c5030000f80c50b0501c060102c4d10104200e400050311030300600813103c1c82d01c4162004002130301e40740c02400d03003114040e110720303180441642c0000d490310401c13140a801c9003466000b00301564821140301202d45000e05403440e200c0510005d21101940c140f1581d69290b0030032003090030410f030104d80325000d824000c018902d0249018048481500044295116070241c0c41c1d50082d07546607624218031404c0440c074102c2e640c01d039600000d0010001100d80b216558810b100003411a6000b502d00180c0303146a007480e075a81e0756242c40d202200d2200e00079a10995080c0f90a01c81003002c0001c0510039030860032603115041e07072034040440f00b801c0c02d84140c504400200c101f09022030702a2400d44480c10024084841103800003000c00c0c04c1151002c0030348010f910039480d0400341d1000380580f40c2c001c0c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 710371798 1250 710370548 710370569
    0x8071212031a040b13050a0c031b1704050708030a03020a26060d140a0c05011d01080103140328030f1a0907021606030b0f06074701030309 61
    0x60b52500d400001a07003040c20350240b59a00c01818007559400b0708159140003500d018452480c6c40180e2001812607582c1c0b40c00481c1c204401300407030314001c0000b02080c03403180e03441d040440842d0480c001003050280003a0f58600401c031005c80c40700014001040c690545480c090707513801c82508000c00b040943c00d04100000d0b030f20345a0208100c2040b40c556000007044444880e01611800c1100034080030100606140c0703e404071010420201040030003c45109880c0c01c8990101c0200c1c404016464001d10740c0090320a41c01400040d99900040300047c491400301ca0504c810300681c06c072100050602c2c400711030031080704803415546c18020340303213400442ca200b407080e00044c203030003140c424030400d001e403117021038034006850b2034401c124640782040407900c081c00590752101c01400901811104501510034990203100f9400c2031002c882c2030581c030022052240c51000d032000105903d00041e00610001d140094240142018020844690703250300c0d50095491460042c0c10486982e01c24035004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 710373048 1250 710371798 710371811
    0x8090a080c010f0e010e090f010905060108190513081218010605031906090816030207091404110a09060e061003060f061202042106050a0506030a1b0807121203 70
    0x10307640850825490f040070b040101e014030501d00180c44000e105408a900500307d04104214072440101d024103c802b840400c20030b5440c1c000c0110380d424000c66203000d05e0003240c61001c01c041c0301540516401907103080300d04a40c507160307070f03465440ba408a0a12184031801000703001203d8410042824a001f1800c02000640d2074a40400d4440d0380300c408081010001c50915018003429421440a0300c0e8460034140d40c801e0303020f80d1160141943d0400350010700c145100480c48120301d00c55240211180e0301141c004d50390301e560b1101d1189024600c140c01c0b5105100000710f92200703000d07140281c10803000ca00c20320720307046c0d09004a041034042d1400401d404d0000410650303420041a4090790001c2ca0594244204199690003901c103a41c00503002d0070919010002c040202c1c00000011407144406120ba42c40301c40d0b580741640e1056414a6140d0841c2100800203891801034002006404021516450b591492541499079690141aa15001080440421028440c10081c01d4420f00341080380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 710374298 1250 710373048 710373073
    0x6171e0a02010c050f0a0f050105060d0f0f060e030a0c0203011b09031407081b0102060703060f0b07030215040b04051005010b0f09030c09040822050f040209060d0908090a08 76
    0x21a100d100c00a03050010b410070b00000e001082c01104012030b100022100b41c21468502505a10f241003400d0340c42c0d501c0d04c408240c0b01e02d044041808101d801510170042c000d01c40d1038100002c0c4555804507107031075a0310903030070051001b4030183c0010802030329408070359081c900606013501c0790882107001c80341404100440c160340140115094035001520403104003400c2000c64074201d6190080380191244110309041c80204c0304200c540520301fa13007529003607141c094041e000d035815801101d44105001009105900d658805814228041d10444100c00c00d0313102131114061095806640c0b5401c0481080240700040100c4214074411280802c00d80d031528000c0001800340407242064a4030001d48000706940401035210786e50070090242e000b500b441e1400e204c0c1607001c82c0d41c3e4100c80360241c991414660400780f1940440f2006025035805107a2a01000001d5004145840d400001032040081e03071203080c0f00300340c0d01038402d84646a0302c001d600d0810411440e95881148958010700c001e000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 710375548 1250 710374298 710374303
    0x70504090e0c1c03141c14070f0e0f060309060a1112040204050606040308030f0603010b06090d0f0606080d09141f36090b010201020304022103040906171e 68
    0xc8104142503d40701d129081e1400301d5500707a1014540700c0b03030000415074a560401e0940c1080c03a12189520401a241c026041c1a1001c3c00c22903880c000304074000d61044c03090b8095000c0c000d080340c00901c500b600108036800107010f030304107484003e1664443c1d01004541487c1d88600c04203010441c104504012016100100b4a50014002401a42c83d000498080d4840e0015a0003450303101c2802034481c901180c4680781110100c50051185d800e100d071511250601400f118a0f000c0c028000d8100c00e07103680c858103260003410004603082d650790880000e918070184440d0110304607982d6094a560300c0c005000030104007414200c3d118240c86904c048401088021682444480d400c04c0300515110300c0c65243c0b03c1146440f81c403200f2120b40c5d0454041034004059609641c0114010880e0b126054012802c030701044500a401a8100c03202d00e070941101043d07008148120f80c1120310340703500d41c0c03102c01c00d441569201208400c5d181d20625800401848040c0810031003c0300015142c0400d40c0c200d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 710376798 1250 710375548 710375569
    0x20109020a17010207142d03040918020301060f081605090609070309080310050901082d0a0206160b0a0908091e0a031214030603030a12020909070504090e0c 69
    0x250700300502c4480c181990030340603280d0f940d80103409035851240c0450150b45131058030412120b0803d42c1003200c90401100d130068031070040c1d0340b00150300303082c107001e81e450040841c40308800311046444000f10042e80c00b40140000f038080d00d0b140100107454a4040f0346448100c40a03001c40b00600e02c01806a511120000303070f88a0411141111903848101d016002032002c3c00015142e400c0000802941d0038040c13241d401110404d440032000d80e80c0e5171901d10340304d10454805a1102c2402410911b10001d404a0707691841012740c141e50001c8003d5001420700c0e4440960006541105141c1ca401d01c8230342901598130070340e100c40a02a10310a60342c0c00e5103070310407004000c0c4125128001c84c440c00c458844128400395001d4412015951071781800520221150580000103200e400100b40d00113900341035a00480000c2e009500b00100c886e025200150340400711650b031a4248004800796442e9110310b030143c3c0c0d00c4d484040c0d0752414200ba180c1542d420144014159211007032000c4103445440701036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 710378048 1250 710376798 710376809
    0xc0f070e04050a29010308030118090c0303030c09081c0806060a080703020a0e03010e06310f39050612060405150d05030d1505010c02040e01150603150501020109020a 73
    0x1d42c2e641e00456102d2400180c0c40300a04c04d804128001004100c00c036002941030300d140e40d40e4441c43c110700518806c1540e4024100802c1400b4400c0c0800000e4000c0c0c00489031442d90f810000303c3d07140ca40554515002110505203c4014403001400d10643c015a256070089804d895403441c11901c0740703010707120700d00c050460420180c3c001104000c041c4200300030710703158000400900c400c074502d2010590701c003002d480500c04115261500b40700402800803406482ea0701d82d92100c0340c1441c0392140d8150785800c1c6426a0101e80444c00c0760340034480c120180200008110f0b0813252900001c22031144c52805411240c06842c003045228024940e4070070a99101400711404a800e036a46411130342d0141c101d01c61541c001725002810000c010011000c1c0460320311029080141003000103030b040d83c8141030700c900c0e0301041810028001604194022031804001c020000c64101030011210440e0310031940080006a5941c609401c142001406031005150900c002e220f20b107416000079210309414402c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 710379298 1250 710378048 710378063
    0x2070620190210020c15100e070c03050f070f0b0a1505190b0418050a020702014e0f05360601060504170f0d180503030c0f070e04050a 59
    0x30100207500c00c1204108026004000f5511580d08101959031951186008506401003100003480f140440355128110b13900c0a041e6155910340950a840340e00c1004400e070104081007000100280101c401001c4961007451282404000e13800c1014000f000600a001c00034100b070036040406483c10154020b4500445416200141c0034642d6010030400781e220455104010500040c02010300a0207209002002e006000c00e56904018000720300c0360303074002804910b003078009040e64001c81d83d0520144980c20101c81f07800601c4204070840b071404038481000d40b040c269800c8607a4a003405501e05110b916201030210f4248609902e0a8940790899007141d060080e03862150b03641c58210340303003c080070b0310256801541c545a0003092607029007d044150522400f4000303140400041c00c081d40034481c00a0440e10380d071401e08613100809039140c0e082440400d01d021440342d60510081c1500707145c5000030700704080502041c50605840703a21101346001c51100300808554080b4181916592028a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 710380548 1250 710379298 710379337
    0x91003031d0321070c06030c1806050a0807030207150203060f2b020303131806241103090402040e0a0c02060f010308131701090c050f0d0807030e0607030302070620 72
    0x322140c2e54003843c54017410024039944002002600b550090fa054072840da20154546240c40000618040c148130313640005104018140a0a1081d800c07681c22152a2402529042c003d03203454003065030200b0f92851441c3e000042c00001d03e000021601c00090a448038501070705101c0c5c1400a040307868000040d404c00ca41001e0045580520440740d440090f54211b501c001d80b07071100c1e44000e182c201c8040000c035213001000f1070820b200504500c64407170007440800d4038000c420f40031100400042c1d450881c600c0203000c5c070043c85d9201d0015002070000040b11100038941942600c06036540303c0140d0056410103000e000d0b11000340140700d8152030300812510b0f62620030031010032215040d544807018120718800f1440224006401c45141a030103611a15985601d81040210f1044441903540e840f103001d460600005400304c02514a4600a007460007428107101f0224001c0d511032001140040c0d0b00003610300401c901c1c0d200e40281c0c41c6410800800d80c2240d030114803030f10320400c00d081d0004040c244 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 710381798 1250 710380548 710380603
    0x711070e06010509030a050c0108010504022502010e0301180b0a1e020c160b12090303010602070504091a072a020d03030b0f1026070207030803090a02091003031d03 72
    0x1100e2503600013401b00c0d00036080c030f0304010f611181c25101090004044100026051800d40260b0384d541c0128512100040c01e010081c2d811010401c004030705001d003844d00b1146075076081c80307108000314000a11003980e099900c3c00340700381074000305034500c1c20780741a038004540b542103036401c2a000c80c00305005995031a2011142d161800c40448091003c00e010008170768404114054018034a90a03030481d000d0300d507141c88a40300e0109000308001640004010030041c0f505030404c00c4464040c080d5a400c40e0129803000c0c104503400c9a00e080030420804c440000740710840c1c0d2050704a0140c0360141125051540050110500380d84040c1c1090b07115142d1880a90b2265501c0b007403010000c001141c1c0d180940d5020b454056940746da080b803080100c00017000150006031080c0300700ca06a001c0c04056003584d981034043e400107807a040440c03007600300302c100581f1809283c0b40100d40c00001724075040e02c0d5240061205909010b034540c40c0c1e2140c240c0302215240026034907500061501070343c9070080100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 710383048 1250 710381798 710381807
    0x9150409020f04031203090302210c121b01180201110f070312030b0901080a0311120a0309060b19090e2409010c0507170d0b1f080711070e0601 63
    0x503000944014800a0580c0010b81d1180051044910502c418403400720f292000764100da44400c000f07005a00102820b0a006050340c090301d51a49501100c0c3d4140140248090b180840f04a64501c2e80b190019107065a440d810801094103000e01c2c0003132040c5007070f1040800700d40501400c000c2c1480f25405412009602c1071001d51541d11030081116100d030345ea818401c600007032180b064408203192500341c490900f08004040e0691304001c0040030104410fa608680d0301040e052080864010089100c4040684400410403080c40d41c4e00030810100e0350030b26504440722024001d208802034186803e00128a03c4048200d440c07841000541da964410094101070584044040500d40350317840c240e90b8031105060340e014440c03000080104a040d00d406450030f00c04c0300b0b03010306205656581c00000c80708400050002d00e52451020802800c10300220f588074204c40c081c10480c0350503949881c40c0683c0b20300d22030f0340300d207161501c0724006040180d06074881030729004132881480c0c28000240d559009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 710384298 1250 710383048 710383057
    0x10311041e0c12110a08010308090f0d1a0124120f06030f050c03070b03040b060406050a0e150a050a0e060a0e28020310050f030f03030c25080915 64
    0x4000052000180c0341c0e8000300710f1050244065500c6140030118807400140e9030035075601c2d0500c1e072248034040e420764940317041c0d9800004686034850031200140c00c00703032a0048580c6e03c0510541e040b900c0784010b000b011089500c1600070a09072034210503450310000403201d84524070b5849082418108490050b00782c05456008001c500c4603041000010401c00d40c002128000d500403010788541c6008002016207443c0f6078410651200002c0c0701040100d420f0a00d0303103420280041000964079610300200f5114000781d480728003085114820441c8000489803c40d03030100c021205806202e0501d000a000d5a295015403040b007100f250006207103440b06d50144d4090920100c82d004507281070714204d28007090350080c000d142d001890203040500528002e0764012400b44281c041010f0620040c003940345141d0200c254541b041001d0282c0d550003e000850180003c0c205851713540c107102c04420351b69070810b040204100e140340701004c003040d500c805031440b40c1411688145804038401e4801800d019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 710385548 1250 710384298 710384351
    0x91807030606060507110604060f050d09050604140c030d0801090f06050616141f0f0b1203090a27180507291912150807080f0601031104 60
    0x140040110f0901d821002038583c0c03500c540c8589804141440c103003d000e0099215460125545200e180345290160303024004400c405c210001e03841c2a2900c4451605909440c1600c00e40b4503500c4138030750f914050003481212041900209034054070000000c202600520a02d00e003107585440600410105030000802090018505610381703003200340c1c00c1403204030103400f1142031380f42c654401035400001c103910380809001c000310294454100c10300005455814400c1080c607685100c4001140d1320b071402e41e011142014010340e00da50011051000c032020a400521a03101e00352a050095a00c0c06101310141c8403c16020480340411504d070340d0103424410009045008114001c650811502e081400a4000044641e800403a41e074100c0c20901c50000b01c030f59003d140e004401c514500401410103100b840580018010f0303040b802800700a10b0035000054141c000090402100000b009040321000740c0c18041e182c1545035654080c80700410340c4e2940d000e66100c054041c142d00d031141d0003001c2c896 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 710386798 1250 710385548 710385551
    0x90b1e03070924031d1015120f02030d09030b0a0e07080f0303040b10030f061e020d1a03030a020a060b01230a090b0901022821110c0918070306 63
    0x80281040641c60400240307400001c2c5414a807000176003560720500368000d000c001034002490180f05c00809400740e41c242c50a1007645420000e81e5a030322044144540b070140600301a00f0b6039610400d42403c103021160342c01c00001e14014408140c03220250380d000700045c100042d036801d4244903a401c01c4c141d80d01c04001802a003d101088050210045224510520b0048080d686080f0b240010b03407005c0c00003600a9540000080008002e41e03c026500088a491020b203d02c03090907140c16039209502051420340c03200c00c01c406810080380c034041c410104901450424420100c001e540b441e0703008010b410940c80388005409640180403410401d0500002600f2440c10201d101c071040d440074510200082020300300103000100c070401d44149810580c06048030b940490492414212103421040381c03a2000300e50500019442d181c80d4a40881e01c507400e0095511181c0042c01c0c078180406415403a4002c24403022140e030300e0100143e41300503010345c071580c1400d80b026803a00c1c1200641000302840d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 710388048 1250 710386798 710386829
    0xf12020d050d0215090703030c020105220801061a0405061608160b0403021603020a0b0f0d092901050f01030e0a050604051609060b1204140a0b07090b1e030709 70
    0x450f40880d0240c5101055081010b45032a110350440c2d0710784c524407000d4005400315101d000190301c120001d003d0b91000103411703c2d412401d004642c1d5144032581c8490034581d51840100411418003440d07061241250004505080c5803102140300d5216240403c6c0e51402d4010611041140070000c0e02c4c84c0120300711030401c40c4000303468168107000303003030310300b607000d4880c6000384049034801200313080a40e40d01a103081d4500e4038280c56501076401c0f00311802901e22041c080400074030348502c21100c1d0b06004d180901108036a10040e803004440007044190591020801804542c84140400300014400e10340000c0b0001d01417040da00302584840001d1072800361100b4882484000030308503046190643c0c00100d41a522224101240d000e80301c3e03511410014442c00805822343e00e110b80e4800e00030b040343d801d01582d00c4078090030f0a014400407244c0c600b400080c000901d80c0b1a45003030180a40c40c00d601e2602c456010328080d110410360b0300d030f0b0b407400d0000005201144124291401001031f0305000214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 710389298 1250 710388048 710388073
    0x12030c030711090901090218100b0d0911032404172a0102090102100513020d06020406140421030525050d08012102030102251502040f12020d05 63
    0x3900c110b0340c5061240364800040b03070300c0031300c103105100400b5070003440c2e03034192518001240e00c1418010913641700744500c80c40018170503001da8002c2080754500f140005001441c0d1520213940a100000750b40690300031000d00c140750046005165410a6058001c8200c0d47c0b140307088000b005580000340741c40b410100c1c4000316026000b1032207214481d0010180c080d0710450070f22900300d0007071801d80e5005034090300c0c41c3c0c0004c1005500c4250001c10880c030907101d040a54001c152500c841e98412140e965002a080010540c000740c252113048281102615040c901111402c1b540001d0082102e1940c50219017030826005200b10380841c1d9107294401100070300044440701403c00c0070001c2d5940c0c05031181789200c151090b4500c50503140c0b900c010420454080d08000410300382c2d0603041760150b60030031181145c4008010381c0b142409180741c5600c00c15059180010801c01c400b450000004c0c01800240a100040c800203419074001c10040c00300b036011800001c00c0ea042c4c07071402405d00e010720160180c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 710390548 1250 710389298 710389313
    0x807020706051e04090c030f0b0d080c1e06041a0f011e050a0b07030210150608070302090a030b0601180602030f0a020109150b09010f14010e032103090f0106050d0212030c0307 77
    0x40c10b0707e840410518042003021400d41c3c004066599000130008014000030b00b41d0005440c1c0042d10718129442d07429001080885054a0b50310b90901b039000c84c0030841082481d00903000d491002d4010b003600c50800314079480c00d03420103001d1070401685050303540d4044207001b40282c006060090113582c429580c1c45000703400c4d60254200b0b9006003d07004e5050f131403010034020048041c46c41d0703a40c00d00062401d00119480c0601810220401d6000c22010041d40d84850b00140514020840c41e00c107070400ea0009413032114840c41c060910507032101c0411a50b500441500c60b000d841400d0580d0b14a0030705002ca005020046000b482103840da83c3c0100c000e22960b1040c2403158040c0c80d4441c4903600c1d0300d4002081140c510800313004020003041c41f4020351180155604051000d0122806c0780c10300b14050340e034040404131130300000001004201d86000104244104910341d400200a843e0070038001c100200d000301c0c00a80650880004d82404040070421a6840d14601e01aaa00c900052500c220f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 710391798 1250 710390548 710390561
    0x106030e01020906040506090109090207050d0305071e08072706030e0f0606010c0f0f030c060f140606090d050d020a03020d03140f09030c010603050f010501060807020706051e0409 79
    0xd141011480034260148200d0345001c9008104904061a090401c1201c0e4800c43c07801e070422040b42000650b01425001030030340f82e4403902c06010b205d513010500500310b941c000d10751401c0012003c0100c942d14402d09003001041000c0ca0882e0082d40c030602d05a50b0350381420401c03c400c035030080f203e01d01d0010710001031060301c3c81f40e1782c248203500300035035502ea480f04818046202500b048000c10781c958018100c004080e441501a0701110820b501d84195176204071b00150013203000c0080320400c2121610480b1740d4030100100402030132000c1c181281101d14020505800f03480e00103442851652641d02c401141d41c0d002049403094042c1140081d150340c460b6904401510400158407201c40c0203000d40024030300303110511030107a65a908208035005000e4604511030204008800f0100001c1c09144003850040b0010321400308454800d50840301c050740308004205d1400c7c24071840700e50100c5d5a8084030300c01d25201c0d840e91000104c140e8400e0a40d041342c21030f20400140011600241c0c1c1011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 710393048 1250 710391798 710391809
    0x70305060615042102100f090509010f0605030c070803070c0c27021e03070e0a050f09040807050309100905030105090d270e0f090f2e14070801 63
    0x40c0d8440d2216000d002642025100c040500c0d1414001030151a0128050884030210002c2004900340700da00482caa80c038000700c54000040744c218801c44503540190b40d610092605640b0082998503104528000c21014052034040040000100d5499440102a100c20a4001c11815a6030034a444060704404100070112031181c1403000016082d04451600c6045c0250b480c00d4209050207140350100035400003242c07100c1c0182100c420828407180b04003961080240d0340305d12900005103400c000d50486540e02ca07511a114030081c80c030301906c800c6125a040780c2c1c8841010f03103414540c80c041c1c0c218040d0004c02c07900640103103104032400f82e0043d001d60845000350020811074807480049501c940709160034002003a101600703007081e0b4140c802980c03110880c8264030255261101103014103504250b6090782416080000d012103031006100ca1880b015108004003001f55800d50056202a14600601c1700c0301e00d901c0d00360710b04030b029030820a54000150301b2000713986070414014002d010280100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 710394298 1250 710393048 710393053
    0xc0b010b070b1506090d03051216020f0316080702180f07030e06041709010c0b0108010603060e0d1b2108161d0409030e06190f0507020105030a0e01020912070305 71
    0xf140000c07420300c2420200b000041e02040c80c0507a45028000155000c100072420004200b01500c03510ba48014414000c41965000c0c00d039085851800910305100510181c0e680d4204008502034002000d850920241d8880c50b120385070300b01800024070026501d02c158200050758400c02070307004808100f0307600c96402d035103007000350400c082010740c1e56290407240181b032203450300320711403085800c68080c10500205140c0840214155910064040800c1e03005000c140e456500610030400349024058000c24243e0003000d0180b000d1070700802201c04100e0300c011a0f17685031540340a0101010040c09101c420401c1e08231480c503d96002015040d044481c0c4810b407503194101d0703030030901c0340c102c0c04100400880030b10104842e1004010081176810422418050400010802612000064282440c40082e001e851040c145000351143c00300e107280c2010450100540e40050303030083e040e40c3c1c104411550000310049620302090080c071030800c401e40c1c8208280540c0e15804000a008400d880c401c409 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 710395548 1250 710394298 710394301
    0x60a080a050124140d05120c010605120d0504140a09020a0f081b0f0c03041a0c01110f0d090c03150b030f0a03080601180f090504110a0320010c0b010b070b 68
    0x44482d0f06040074068204c800d000c04240302d42c81d10b0b150b2440c040090140c02a98604640d83c01824042d6111788240c007003994540d58200b00c207262060400c00c56035800c0340074000d8100301d103078000c29510840c00b444441ca8840c01c0c2c1a10241c80e11011003010b001840700031592080c40385400b410307403410820b0450008202c10001101180580984c07620340080541c1e06e42001602070070844207030002401222030f48024000007600442021000400d21414104640e542c04050351490940c2c4114520145451081000c2540c001001c003c44141750359020340000c46902c145468008481035510140c08100c201c2d0202d25101c40692001c1078194084048030312042d04241c000751140e094010103000724884d0030000c0c5142d4001c03d09d65402100c407940200000d500c4020788918070500d81c00c600080c55036030041008000b8070303510010b0740e0300044484045941ca035a80d00103040090308042030218007468100c001a90103816044007440d80041f040090b507031180c0c141c8820f40c000b10b200f906d01c40034110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 710396798 1250 710395548 710395601
    0x5040507031b0f1707080f0f01050901060c06020c060709080d0e030309040509030f0a020d030c02061b340209010e070518060715050f07020304080a0b060a080a0501 72
    0x400c0107180150b42180c52800074804000361080142c019840c4140301070900024801d1040300d015610920301c030703105c003041400c1c9807201011a01c402405400300350500001884103644450406045030103518100c618240c0034540b610107400349400704e241601c100b2052101050f00b140000e0141c0e001003003120310100390300c101101c054200303800c110b400d50400c00c200300310303405c25800255211100350200c070300d4071060b05400c0030302d8ac0c030040d612001070700091003070702000b036160003044039403040b509c020315160070f0101c2c016043c0000c0d603429441002000407507214040c440d014080c11003501950341c0481c440e000344118076051f44520300f02d01c616503a0001092080b0641c01c804d000300882c3c1c2d00c05052680044440e40b502c1c0e044910781d0340c0320f00e052005c1c40c00207a1130380b060714146847c40b01c082110b060403d1402100d14000d440e2406540082c48140004600000c001c12425000091124507858210208681c0c61040d0003541c098028003081034103024054001d4044501c01c0c2040c00d07052078208 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 710398048 1250 710396798 710396801
    0xd06080f0a1e06060f0b09041d060a0506030106050a14100908030a12090b01090f051501050d0504020a030b04030906110a15020705100221061f26010f0504050703 71
    0x2000800042c03010718980341103250003103040308061003400001940340e21041020134404441d8030644d000e80b00011510220f062500810b0b503c0001b000e000e00940203054101c948489004140d0800c1c1ca6070740c000100300341c0e03094100300000c00015003a80b001c1c980b2200040c018051820f441802022241003403c62288504100012602c400c00510b080203909001150000000c0310341d2220303151a944403201140c03419007010b000306425040001d04448213444c1c0301c00d551006150050702140c1d43d82e0102c460f48c00c8003c8810207401901c000400c0c2c0c0c0d6610004800161b65000506400c240000300420103411040120564500f0f0325120810b644e40700344290380c0c0f914031000400704c2c1409100c0c17141502058001d0310078544070f94103030388100c0300d88502201260080704d8294408101c50007207202101144140da0b07000b440584840304030340340b44410044a00010341901041001c500702008040c1483c0748900b0050980c004503540c696074850700352107804882c3c00b030107110328030340380115611901a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 710399298 1250 710398048 710398063
    0x100e12070f03030f11031204110a03051b030307080703020c030f010b06040e0403031d030a09050301150302060a09031205030708070c03090303031a130204081e0c240d06080f 76
    0x110341c11a040c00c66508980a83c04109448103011060b5040c0707480f4501840607107003070301e01726880000c01d00d41820324003099460646650301684400c4028004104046010017408130a03410340164580164003082c55440782c403074064903006003c506041016404502d105403458210226031611000c40e508600b00e824481b08258030003820002009403100c105010fa500c6402030800080c0c03403450480340c135120000075450700f2107a000041c108654907003080001c40504000e40003040021a90f681c800b45203089400003a01c101c2d800b01e0801d016a21400c0440003460b40074500c0d0806000d01e19001c2c145800565034803010581203800035250354422042c4541c281c4d0160385142042e407840e00c040c1e00030129035100041e43c0002c074084003d2500c5440c4c641c400d4501280005a40d58901203100d030402c1d1900b21000c20f2a41c140b101c2c90002000000c41091400d0100c0c1e01040d00c040d001c10401d14640100100711400401252510308000154080c004a80342002034078103603590380c65941e40b00e820 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 710400548 1250 710399298 710399309
    0xf1218030307180306050f01030b011a03041103032221080702090907080f060405010b03070b220e1501030b0603160311040305151518010b0304030c02100e1207 70
    0x10320028482c02d00c540b01000c80ea4030100880c02101c0d8036a00c0746000c0e0b42040351482501391740710004004015212401078010301002036010940c941c00342c4604014030020308041c0a8001180320500e80c0d40e400c0c4111920201e03425400c11585109983c0704015444c076100d050101e00295100888000c4050140d520156010f420f1b503140044c5a420000c0310940902842118030803403070003043c101c00030416034603604c1c2240d00034003040c40c0900d81b19003510b0214803881d0081d00440800c004c1a542a01a03070b918080c41e0b03c13001707103104071a83c0c45000303004140c2c0658422451401480340620f12101424010202a40c061007010342c40c100381714070761006560301000002107500c041081c92003a070020f5203404c907011403207180c00c0d81ca4442030300e06400785040d03031610484001407160b00a1080c232914642001504c0c0c0394000c0180f00b07100d103080700051291072441640040028109132283d40c400c50341c154014983c01b4010b80708040107009440740b01a160080c1d100c2003a101213070500207000c3d0111103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 710401798 1250 710400548 710400553
    0x150304022107150e060a232a0a0804060503041407031505070807140c070509040b0f01060f0c110d170a03060902070f061d0106061e051305010f0e060f1218 68
    0x3e02041007100c0c05e1074081440702c011900141d000d4206032011f001402d61004009200488028051440e0031035815030741c13400b40382e9200410000020b80340c2030035141204c20b6810030030344a03600d500309030940415106105200d03020b108004010020080c0038520000b03106282041180da4510b800e440ca0340081c2c0f60440400c003403003105680210710700021f242003032042094900d070691340c402240c0c0000040d101110446500c100304087c058442c22110f0042800c0d14181d03800c00b0b4405000760840030000d4000e03241100381c2012141613200d04011002d056840303020503082c11242c01c150b00c1603420424009000078103040d03000880c1103c0c1c2c002d0360041038002c0010690203c035543d400700207228011004098568000d950707505400284503420007041d4540390282e0100441d80000c560b90844120744050080c00c1c40007048210401c0b00032425a2400c0c01c00c800b102c07003188000d42d40c204248ac1c9082c0e1040000444140010601024000d0340d160301c0c940790307010b0716500450141c1c4503060724a41e4066 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 710403048 1250 710401798 710401807
    0x91c030203150f1309081206010516080a030b030a03120c0c05120a0c021807030f09031b1401090305120a060303081506120403020a05060c09150304022107150e06 71
    0xe203049508010803080c010720350541030110340007080a5078805c03079080c5c86000000c902c0807640c44511809580c8050240b9005203045034002d480c20b0140202e8001800d001c1000c1104507620307000c3d41c001500e402000b011500d01c1046490002d10303542411007500c0d601030500c0c415030300c20f5000c0c0790552036641c0e105018004880b034403080b089031354200c803060700d04104154001700b0150321903040c001240c0c48102c94041300d61500341c1001d41600d0703004140c222160324000c0e0303580210343d10051516120042106400e800c29140c20900300e00d0884804c0742605519150400c01015001070060403140844109681140d0b5030440d81402c50b0b45030700c00903010440c80c1c40001c0c0040d414809280002000800c014100000f0420400d1f00603c111403c40269010400c4071b420f11004100c43d641c0103014841152401d1a03a502013210042d1540802040c0d60001c00810f0441d0703600d62403e00340a0003d0310340045a15028a1241d4615051003003140d0b05406144440d00244106e00300c490441010346150301c0c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 710404298 1250 710403048 710403091
    0xe060f03070620031306050403050705060703140a3e0d050a050c010f0c09081504080406030c020109020d06150602061506070206070f0501060515091e18091c030203 72
    0x195000c2c18000045000405c4a001c40c44121340010003c4c012aa8a241d215411f500c1c2c0180350010640100f4461031040c080741d4000f03540708492101c4030503080d5505840d044080000d84070311200b502c1d0403000e1091440e40c084107210000044038481b095880001e9443da061110588412101c4c1c508000203e01300102040280280001c24800348110000a1020030079440c4004681300c9050b18400a00809030403c0342c03010800020012440f544162041810183c0d510b0002d84260f104820130702d51141d8254010600030340c408084950003401c003440700121850118002e1861504405e0807a42101c0042650342c4001915403144907a83c459010070070030b0900300070080c7c0003032204a90000080204d440010014280c01410394400c0002003031541c2803604129080c4c00c42420414400018842061079654985241040b20b03c070700d4000c003440000c072011844c080996103600200680303c4080c04440300000640c044400e0400700c9107503142640e404110264401900c031500c3d0051394039011140d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 710405548 1250 710404298 710404337
    0x209040b06310e0a02030403030b04150501080702071706010f0e0403020304230409050f21040302040c0e061216050901020616030618020304060605030106080a0b1e010e060f030706 79
    0x1001c00c10b0700c2160212a83d5000c0c984a02d42c011a8400401a00030040c0800c05415025900b030000c2c00300d4091002100c81160429002c6031440313254100a480c90106411500034030008010b08202806908030340700b580843c0755034590a120f00c40d4107810491b40020210032040c2402c0c02a0340c103134065880c1c6440d00c1c5050401d03489500e18403103110a4403003580c4150342d4034880d00720b9044c0301e04058200b11030948003035070a1401c00026004140180f03e0409100c0340b00302c1c102c1d415254103ea0004840300b80c0c100440300300e03420119a42d00b00c000043d0300f03241c244007511303558494048603006440880c0d64090854240c0140610203000d86d21500100302d040c403500000c2d034002e190500d03000a865549802240d1070342024035404012a03030000600043c840304e4012800682429002801110701e031601c0c2a40c1c418644001030300e180300c0d0b60003044460400d000e903082074000306094400c040d612190009001c0070251822413107030260f196440010706000c9501c40889190343c98004e0b1b101c00a0f050b621 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 710406798 1250 710405548 710405617
    0xc0311070f1b0b030a1512060510062102280c1506120b04051023130c0b0a031404030305250503131b060504080f011103070c0809130209040b06 63
    0x10003007106c5100803031500c2c080c1c001c00884500614002c48e075810f00d084201546400742d0461010440100c001c103100d103070000c40030312f2599180d020040e034880c0442400b4440010102140d012115001d03030103900c0c5135200c400c0006140c0250090389012039951036801c102d982e58418001c2003246140740c01e02040c2082e00e4650310501400640300400300c1d61211b0411506800080d01d42a08541c2c51601c3c4010707410381d1107500c50303c3c1c00200c150b100700f15281c0913a94401c611074075040075030004a02c86024445d0300150340c0a14045250030007801c1600d0041c01810381207d0380300c104c11a0b5220004801140c06ca5554411815114036255031a005001c0140c082c040c2c8090303c155030380b00c0210410080e4030f004c240091201b5500c0b15100c80c1451181c5040c110040803d1400b82c1c10700980c2203a04c1c80640031203400c403809091600d05c0f840d00d4580180c9074059142015403112510343d00e5601180300350001d00b0182c1d42100c2c10065414140c0803c15640240900000030801004000102049038035900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 710408048 1250 710406798 710406821
    0x1b09040807060e0609070506090307150c120e09090a0b0402010302030703140a0903081602060610170a060602070b0a02060a0e0703050a05010c09090905060a0c0311070f1b0b030a 78
    0x1600e001d04684841c4252003d009421405030300c46810445540024460100070300b0003110081d2034104a0340020765a000180151042a0940c04c00080715500a284c54000d10f80e02c60460790104944200140944041c104481d0242004400044040e070300810354640895104134162103640f0f80d500110000d420041060050654030751031305280c40d084002c0300303204811142c1d011507a01010b00e1300410404014000c10309009104000e01c10080c1c0100e155503004c41c00b03582e102c1c004030a20600b2a0001c612051410380030102c0c0c000c0c40200b4119030403000a9603000d80032500100d81e076030b41050242c440e0080c086c0041e00a9808600c218160307810104410711004101c1d080d25803a42c80709401c184a001c0304030380c569903510305121240c1c0c0001a1500800e0107203130030403810f2020748a00d5210100203094002d0b5036540d0300740403a40743c02036100102c82c0800c40c1c8151340790f03c13061800052a00740c00c2c5040c0d0300300c90209082c490700c1000c04400825207410747d042038115114910701601601e0510b504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 710409298 1250 710408048 710408063
    0xb060301062c1905030c0901050303030a0b130e0c010207080f0c0f030f01020f070c050a050916021501120506010f0f12080705011416030b09060f040b090408030906091b0904 76
    0x29116940e0b00190b003c0c08042240203080d80d520b45010540b80c020484441c50143c000000104950369010080c0c80c1c0c0815115004600316401c1d0b000100d040d20300c8110501941d10b461810640340320009240c01540b20281c085654054036540220703500d441030031804125034840c1c503421840e4184044a6409400b0141c100c41241c10b11485050980c2c00c0f01403a40703002c4c00081141428040440301080c014002664a0410a41010080742100b00b004203240c240c00f030100501c0b4451442042545041c40702e0f50361050503540c40e01d580b426020600c52042d5a140708070000882d050048200600444150a001c0440303203207846c8140381c01c1442404240c4910400380300700000301d034082c00703030403140104c41c2101c45c680d15007845004022203d80c100001094500300e07600100d9290310150383d8002a04950b07003140b030f1000c070740002d015050703880007243c0141c01c0c6400d000801008502943c0107040725415500990b0307510b900d140d610901c0508650000a405025100c9420034007000c0d03070001e001e401d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 710410548 1250 710409298 710409377
    0xc020f0d020a0b0a0e0307060e060d0b1909060503010f0b0307120c09060e0403090611100f060b04090504140604110402180603041104050109090c140619030f0b06030106 74
    0x3502d5501c2e0413440341c0380045130b01509250b0302ca2a05000010150100313080415002e5404808102c49c0d0003140485159556610300c115a10f603140300301c9d9420481c0495981034010380350552200600418481c1074080c1d0300788551310303902c285680120745040c03401030014411070785031a500745501082c11070241e9002000901c0800e941545001d900040c2c512441d40040a0409207001090383c180b0760701100070800412240c00e15500003040a001d0428840d1000c100c2d01c01940c164802005545e02c0039440c410b0004002408010f10f8021034407542c016498511a0108100516140d0300c2c1281c1c002d2000481c0160003226140580c0540340c000c00500c900901c194001c000b250f95075006540c04d585e4440743d240c01401d1860b25018640c05031101450078406681d0995990402400c94040c42111030001203c0c1d80654803030708255003070303190b0f87c60100440e411900400703002090007480012090b418034030842502c8c284203003104c0c101c0c0c400740e4800580045e4569080f90440c051401005403490421 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 710411798 1250 710410548 710410559
    0x1803330a14090c090c1206130f0e010603110306010305060106050304060906061214070b0901051e1c050a180602130b0a02070e01080f0a24020f0306040c0c020f0d020a 73
    0x15600d81c841c1e200c1100501c9803c4600c41000000080100400b01c444001c00c421905400c01d046000c0d0007590039030b8480618540401204082c042c3c012203010141c1c0380c041d441040310015044002140d00628054110b50580c005064841e0400d00000d0802d900c07410040090718815801580d0240c0143c02c0001d6280c030315618042a500c0d541c1c803000c07020080c51445814000283c1c0003240a02c8403c0062103041e10708440e11015002c0d2951144c140000807a02d00c0f01030340503910380e580f081c1d00c000001d61f0f10003180030034171400004580d020300d80e5440d10000403501c050702d200318280400c420003000c000c0c458941e43c11010703500545036070390320200c0b5034800130720020a24080c1c1200d40e45900901601c0742041c3d280c21070f00c00140d2100a46521a2004c0c101c42d080209410844540140a540c400310021174844281060b002e400840c07103200181d907400d01d44484010b10300800003102c0922004148140031640c02c0c8000300007940c41405000d2044151400c048818405071000e0480c0307983c5a51071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 710413048 1250 710411798 710411831
    0x13092706090203031b0606100f0f05221e18090501021209010533120f030409020a0801090c080f06010201060e09071a0408060c030c0904021803330a 65
    0x40c5da051040400301c800f0a06211403d20001e40d010209555825442c180660010205900a001d000901402c001d5040700e01e03105100301c0f0040c0340301902d010003091107440e6520b0424481e109801050007800c01c41c882c51a000401802104c80982c90030801d2104900090001c4c40e16000449956608210110341c9060030010b481c03083c0054000040c80f49060528000d8000c0048151344400d10105410250029001e415036060101079854020509152141511b00100e50510544a2002140000319250150028500a461a901d0150590742d480e512401d46040d02e0101c0e022607244030019440c402038003c010742c0500140b0012032481c0d82d495410f01e081d202a20000840d4002140a0002c0e03140165200150b01c6810f07040d6180501c0c2c42803041d140d50000c0c1148070f01c81d0001010443d0001c0d80380a59068034070003070003190780305500c0c4801d60480c00000c040b24080d025078800d9088034904081c900b081e5000d01c6c50b1600142c0c10040518032f8440000f41090325140da030700031095200618 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 710414298 1250 710413048 710413057
    0x8060f090a050403030e0703020306040f1115070203210a4506050a0f0315030803011707081209090a0f060e090601140d0b070e10051309270609020303 66
    0x50074000a038074105414028141c8036080c22481d4640c2c00000c04000603203001441503400b58200080c200d0100b19442c210000016131107034168802d10810151941c2442c2e00010485103200310f040303d540d142e041c109030401d5907180c0d203049043e030b105014109041c0d00469924480040354005008020100781520b000d56900d2005280701200440c105401c042103055070501400c60b505005040c0303000d40f0070007003080078005003100030540c880ba4810000780801014a0143d648009825101e60b1103080c04001d030301a100003a2210701c11030780c001400c00710100d0b100400300030305034000785000502c4c400e00c0008074001d01500c010503a50300c01d071011140140320f441c0143c0704a207480341e05030425128013484c1210680000201c40541c1040442590f11401840c640300e030320000708059996aa5415aa000304c21059103401034400e450086080358080014200d82c101d48142c200750b00d8480d6002d030308481d00e1241d208403c1c2800c20b10300da4131640944150050900c81c0c01c0c0810110401c0e40400d080d03800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 710415548 1250 710414298 710414311
    0x10302010806031e030a110c0a05120f01020301150e0a05060906131e181517010f0e0706020d08011a0c030714061b030402220207080412030e03160608060f09 69
    0x1081e1b074190a5030007409500408070300720040c000068044001882e540c3e0b64407405114020124800750034030014800c0001c4080901c0086440e582d40d40e6010840c0029020900c00090080056501510341071088400307407030010340981c1c14003075100d0a00165a2000c45030b55500e100805d80010441c0f0a4002101e000c442c04080980c0c041c0b9145c94a1090344070f0003401d220081c1003810415130140000141401c80391039100c884030f1003464107045401850a100301280e542d0601090380d80c2001c000500b0011940d440e4200c40e00005d003088104c031204001e014465400b05520103032034041600b0405442c1501d00761041d6850246640d07100f044054032171001e2500c07600701c2400c00c0400c44d08906000805580c0301c41e82d0f459441c1071390001d03104144141c4156401404607034800000001030381680c210540c844801135840c1d0f103d100410705001d492a0450009009007105040c5043c00f01b103001041946088040c0c1480c00c200041d501e1110051803d030308548802480041c540c1c2d0340300024000c48 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 710416798 1250 710415548 710415553
    0x100206241c020108010b19030f020705240108010905251e0915031a0a0f0204080309030d2c060d0908031f18231e0f0f010302010806031e 60
    0x11074500c0094101e040c168403c0d0358540d01807002840c44000c0304000038021030240381c0010079403040148000203001c2c02c0800f0b41103118a00b041300c1031a0361003200d0004905448030060030703a0b80e240c03511802d8500394400107040b60802100e4510684044c00c1d41c1480300703180c45000021507120201c420340e129203403170540d030004032201007000a040304e0310071031034030700202c4d114154124156200c3c3d440c0d81000301802d0526403d643c0004000c40c03040c2c0d03c040c8178400e03001010365503541d40d01c2d41907960303411204140c0c0c824005d102101035194001c505034000d80c0c80300002c018003941d41da410902030300c40a20f006900060204030701000c4400c1441500c400500c40c14405890f420213965060408030554142c07290110b0f425008c3c003207031000c60001c0e21a4003000c08085040d1040c0302c400c40345039403441600c10001c0882414003c1c0540c0344031108a03151491003130710001e0fa5a8000240303000e00150703130801c07010030b04130018805944034108813a8000e0b8041e04891213103590412200c0c0d402c8207811841001d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 710418048 1250 710416798 710416849
    0x7151103280504030c0f030905091f090624030209190303020f0c031b030c1206040510051302060c03070f0c06020d0503010305030405060c0715050a090510020624 71
    0x7220500c050304580941d10042010b842c003940c000e01a4140f0f10380252503800d03200b00f10410580316020400c0a0900035181d10b00b20300700707480c01100d0050100810340c1c18922000e40800c10003124460346040311651810746c030f040d002c0802c0d0f4079401d402480030101016000c0103802c2e4142c66030074001c81c480c104560400ca02c580b6608000b4288511028402505c0d006541900751036a000203913404003000140956403081d8080e8002842d0903403103040b550b0080d50b104412200f0100200f2100c0c440d501401c00c1c2c07100c1050845810b001c60b40304480820048003821205005410700380050614070317503010116450000c042d01c1d59403655030301d00403c49a1201508043c031a01d80d06100c195134805107402d04c24215411981d40035264052801010b00030360300071641c040c41c00c8040021500620800c10342414a040b00d602c001c080c0d920011640c2d0201d001140300045030f00b1b0104002031054900d6002e031000f034541c846580144010352108414000306220341c2c1c0c070142d407403516000c107615101c403070314865 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 710419298 1250 710418048 710418091
    0x609020303210402040b100206040b07030b091905010b2503260901060501030c05030103020f0613080c0307050109180c030b1903171e0307091701020703031401050607151103 76
    0x41d03813401c42c2c03224091151030407e600706c0c41d0001685500103610042c203841542c3c90003007c44c000c184150040d60700c400d111052014100d44090aa045d4146008041c41141c1c0c80e072126502602c0384008820a81e4409502800d00c060840903a81e9454403030f2802c50000c8000107002c084440140900c006414642024845401024030499000306001e0805000140c0b502c003004d0054041484041d005a40000b540203041d600c44007140e03003142441d9850000c268941c01c03501d58412403009158081e2144080100300d96025030f0401c4200e0740303203015540024030719203c0310016042400c40001815104e10044803650345011500c5c1c4030725280c299103401c5501e9402c01640d00081e02c0700070801042e04201b071610801a00d00e01055880c86022100d41d6034460b03110460b5200c046900070749240c00718400c884030740b0406400401869009030b80911103605115210084640c0078424158000c0b0200020340011311140c0041c40c0300032121a0000e84031440320100802d03a4022108a000300c2a00084d03000b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 710420548 1250 710419298 710419301
    0x1d0709020711210622110301020702030f060a14010e0c0a2a0c091b26070809160f05130209090f0402130c020303060405060628170c0403060902030321040204 69
    0x18000d40720070742e1408880c00340d0003803c81e622005c031010740401c413201450b02c0107132025012a64025130203401c0f02d48080001002c203450f01415650a010103050182a038200008143c020741070701d41020340142180c540365980c00c41c680c051070f10003050000710b65000100c01800c841180d55041800088210449a45031401d1034180c25080108020700d84065400742e1381150030300580c59241030600c0d0540c4c040303805002841d441b103100c5080c1c10100306010003074000d5025440314050030f0144206c0d170501001c24110a85114280990701502d203524000700100c1c5014a0040d0410108800c0186042000f8001c1003075000d0444680030681c03818000d000c1141000301e00148050b5028001308031039094098001d4aa10019013078604c00ca44540c085544c42d030fa21001c6503d8080c0c11940039844290031a1350392100d010b298092000b06440c807680d400b0503500254502d200c0c1c0050f805a624143c1580d0b07a41e001464100e2040e80c040c4400d10510350301da00788188180740780002c0310f0010403a1034207104020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 710421798 1250 710420548 710420551
    0x1c05010606270b07030c082101050d0302060f182a0102070b1602010306090203090106081c090b0705070b03010906083c01020c03070807061d07090207112106 69
    0x4000b98000310000e00788080c8241598281c491604085030354210a040c00c603110b4420030300c00340c0040000521420304500f1034041c101030700705030041c0011607030340d0f40c0400c1024014004040c0160f04042c00040c002c1e0703015224ac50b481411240c5580345610031681d100d107015044213000017003902641a981c96403203d0450500c1c4080248000c0620506186204107203001c0c0b45600d1f070420014117405003c5a0090304420098142d6030011912031804200c400c1c00707003040e4859100030780a10180b03045401c400700140e008509180d11080d40c85450802c20b2850b0340c0c40541c0965050040c500c002c121041c4110046000740621070012420b2801c185030541844142d0003040111454000040c441003802101402c0700303203110000801c2551381851840c06407103001c2c041c030440d000c002031050400130301801401607203010320342c10444984681188250001051901c442e5680408410040308025400801c480d038813803602e0081942035080401c215a0349400c011103c810030320704000d044402042000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710423048 1250 710421798 710421827
    0x3030e15070c03050a03020d090f020424030f0f0203010c18090212070804050a05060c130801110f031806010f0602011407090506130b0406170a291c05010606 69
    0x4802030308041c0c0025204020400005041c4440814800802d601980c19182c600b9076031790007440801072601e004c3d41500e040980c00c0348200d01c0c02140c4404081d11917080c3d22440f9158204000480c155298078a075000c0908040f600f03c0344801607500144c401380644080301c02180c0300d03855858032100070b04144840d40d0300121215032050150030b0114491070140c0303070001390310700b0304002c180c4590030301d035041145400c0040c110b0300c12003090060162400d001000300004807129191815260142a805c2c1d41c0d9504400d001390750180580d011b481d80703040c01190001e0460500c200703425406220941019000d81c0322070120000d00c1410045290280540c2e07013003c1034120104080d1908880241c04600a40541401640042054049205a8280030010f48001c4251948481d0348a0b0010040c41c0840c10441a06080d000030544070b80c46d03405020303160b8451650719903030ba032140300140c00c01880103214036920100400922103101110342c800510035001c1c1001080540c05c0c103102511844002001c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 710424298 1250 710423048 710423083
    0x430f03150e0307022b150605190b0a050c071d09031e030a02040b2706040807061b150e0c0a03030e090406060e0901090c0504180b0a0608030703030e 65
    0xc20303548070008030803078140f40d504851040150f0f40d44c200d02030507824421040104c00315100900014000c885105e103101c203850b084180100b9031182c00303012115551213031603042c603180d648040c031518000102500001d43c00d85001070800d4182e40416141a0303642d40a41c907204041d001c0041c1400c58207020b40d80c030071a000000c514018181e042d580200d001c070f1801d64188900440816074140e801c0d0100c41c001d141c01116162103803114094102101807001c58500d182202e40444501814a0001c0c1d400302d9502d1405001d405140040541e0501400086134a014000340c40c403c0000c1c1c5403020000707480f9136104000460440040c0424540700c1e41016151150900845c10030010382d0050655882403010b880481c150780312490300c0ca0152600303410402e4100a680c00b0044800740540c0101c3c099401280040e400643d607005001c2100e001019813510000c501c0d0a19001c07611b0305003955040b110908000481c5075a0b00d85250131a042185c04900281d100c03081424074a904002041c0300c170b18040c81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 710425548 1250 710424298 710424311
    0x5010e0a03120f02031c05060f1f03020901020c130218060414210d023004030f110603070905040b030613031b020d03090e0702430f0315 60
    0x940c03030b01c9003000400e642c0c1002000c20340004641d1091041e61601c9041d41c2c0400e901c000e1481c0307503034040c20f0f0440d00e190240014121031301151509406084a4621035040e0701c085100340d4408402940c0544086410341c460441d0420482d1100601c0e42c0c202c41c5202c20050f00d4413003070301d09202038403c0c29080324802e401c240010f001045a152000c080b2205c1181c82480074004582c100340340c15401000f80e0a01e004054080c1980350300404c0802020610f00303100142600c200b090400202010f0103078183c0340c0e40500c01400003c0e540ca80b2001014000c07100b5007403242d0407000007405c80d481122610300007040090208803d042134047d181809a040f0044e050350f02d44407410810260000728064104a4040c0203002c0144241c000004200d40190080101107041d00703003c0c0c0081070600c244200c500c98000041e500368404661100d01d0000032901810326150a100c524114294000360820b40200740e0700061481c01007400030300100007604500c0311951030b50420103101c0100041640d440c504251 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 710426798 1250 710425548 710425553
    0x20d03090b2806060801181b0f0201091704090b060f03130c030b0a050f2410031107050c010f080408040b070c05060c060420010207090f0b0303040b0405010e0a03 71
    0x412a580525900c00d09802072a688520209607100c907488400c05603c2e01c080881c1290f40200034505a4580461140340820118071080c11600e50451003004c5400ca44c2d441c4034140c1c0b01d442c904500440510022501c0e400c02d0312050320044201006103403402e4001810440581d03140100c3d80350010858209080c840c00c04040c0260b40300050042d003a0950140074003041021030b20049026582143d141d00722844c0040714440245825220300304083e22000000e00c40103004110744030400d074031402c9030003500181014442180c9241102005050311068840e03101007000015000743c070b004000030114424580000b4000c0c0b003007841503070100591a420440411503010440702180c03000f4456a0799034480741481d40d44604907400a90340240b0000302101080c0740044d00f140201c1c050601e410355901f8605000300c0d207000748401d0f18003603000002c0411488060f540714078903c406c001320210750f0300c00c000c0009065900681008400d800041000c0c001542c2c8200c116000034015108900040e0658 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 710428048 1250 710426798 710426813
    0x3030c0304050d03050415050301090f0c0c02041a18011d06090112050c0a0b03040b010e011a03040501180f11010305071209020a180c0305130f141504080307020d0309 73
    0x50180d5030084040421640806105508441c000c2101d51f890300280c00c3d00400042441d0310a22030800442e04000c1d40c900f290b120341c8961000140e0603194800201120740c2404050501c50300300902c2140c0618207100580c6907884003108060022802016660500c048100116480340180c80410022020420310b9101d0b11080b5041d14090214142800903507d072261801e00010300403500401c21150004d440c01780e12019500451103901552201d0b80c807030303008487c11030003403090100503000c035051002051300f600d00940d0024040e400104194200c45003240d00040300c6842110400d410b551840309120044403c000012002d00e02403006082a00000b807501e0521501110f680f07079280324620456907580c103800005c0550101c518821481034a501c802490021640000b007400c04000504203161400c84c03688003a80300842c60794450050f107a0f44688200c06503207030024419465070344083d415884074284901c1c40748c2c4a080e0750740b41034072000f420281403012030010b00d42040d43c000001240c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 710429298 1250 710428048 710428057
    0x40e011a0f0f07030e01030507050d0b0d05060c0901080109090c05150c070602011d0604080304060c090e0a020403020a080c090c0a0306170c0f180403050706021b01140603030c03 78
    0xc5082034034a62522000c421192280c81c5003080440c0000a000702c0b261079520250007000e0280d241c00320740c542c0a40c01034013034880031a10400080d40400807944400c2c01a80f01e0704c2c1050001c0e00e10080076403903680301440c0c0f0f14251804401100049401d009075a8401020350146c9060754041c0400a859500d004094145000b03461003600c0c080b01c0d03a0f00300b8058405803101c030f01340740c42100c07001590b942e0081d000300555a00503500c00c2c24116a24400d00e400107005002c2c0768040e000c41d01d9607071584c07540c500410782494040304003c03e80c0380001e01e00102c00c85a501941c0100380c0146d40703602e0b502c10003488020030782c030030300d807681040c0c100e00c0c81a2b0f10354854aa001d0000380c01c0c5a0b0b1218200411002032410303400401e100b0180d01c0c1395030560240050a017400382002c0d14810b03d2520503d0030803601c902807200442c07543e0210400100042c2c400c0020b001c010340705490141c20301c034030300288016001c02684403a01680d942d41703500e50b90f408051401340e00004154083c1d490324070400080e5859100c4c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 710430548 1250 710429298 710429309
    0x307241b08070c08190e01030e01110403060b18071106220f0309050a0906080c0103050603030a050703031d0309100305130308060307050d0506070e01050f160c09050c1b0102040e01 79
    0xc500f010601030000f54001c60300c00914600b000c00309801170340006021080450748950000c0d180036000409180144501c02c91054140d01150038146103540d10000341980004550f005000d1121258402c250000c17000e00a407000e48402c4500968160341a240000003440b010080d030400001c0740030307500e00540c00c62440b6005444000c03001ca490a00366100300d102c0e80a260072041c058000078004e012588101d05840000c416504e601c11880b00440590700152051603154004118a0310b4050080300100006803017801c000c83c5c2004000100c41c0006040207080c0e085400c002504801c038507000340b840340b1242845c10208100c0c140700000d01c4014610f0900207052051081c0491a03075641007200b4001444c00900480010b10680781590319100141c400501240c2c1c1c1c076030010031960048042d2812041d0780d801080c14100c283d4020404a001400b0a07201d100700a0408a08680707075020f0103204003c0381d00b0b09961504c0069a03d608511801270980a5900c1844140b08000304000310904484 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 710431654 1106 710430548 710430557
    0xb0a12060b04050603060f0403030b0301020d060305010b010207060509040207020a1503061a19030b011e030b030705090c07060203042904030905030f0715020307241b0807 75
    0x3c105554095054022000041480f04034120040e4001d01078540415070701c2d8038401003404c83c1e104a90310680c4646030181401406401d0041d4410004284024645546000c0c4020250302903e02a10701c11600002c10328107544d07584507040058030700d10a403500100a036040140042c2081d01c0f85411b5043c00d29809014068140c09480c12050443c84041403070b401c060044004101001b4861f061100c0c004101e00d26031008001e03020290b00d95140040e0044000c400c152500f881588031a10489011042100b00851a02510318807684150701507184d844d9031910301c5491600719466110003108a196018007895451600e0185001c4c1d00c0b0740c00704a484800303258071031542c0825841698059041004803440d43c80c0d44068220481c8103176800c0c03000c130341d58100c031080c50140c1142011030f50900c80140c00e059441284c20510341c0032116408a083d811001d840c103070b00100400c0038030 = true := by decide +kernel

theorem cover : BRFrame.Cov 710251798 710431654 := by
  have h0 := BRFrame.cov_init 710251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 710251798 ≤ n) (h2 : n < 710431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
