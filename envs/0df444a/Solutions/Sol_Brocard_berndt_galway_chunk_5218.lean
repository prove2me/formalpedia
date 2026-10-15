-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5218
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:08:20.706496+00:00
-- url     : https://prove2.me/submissions/28a3ca63-d5d7-49ac-a529-f2f87d094292

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 938309352 ≤ n < 938489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 938310602 1250 938309352 938309371
    0x2b050a0c0f020c0f0609011101060806041202010e0d0302031503070303032304020f0402030c0d0501030515071b02090a0920040509070609030b07030902030d0315060e06041505120924 80
    0x1100a0100301718480e4486803066040c400070b001d08074400002446107201801001d80140240d040c9030030800b9103441035500d0401160704021101d04e0520020580c0440c907207c1c0d00340503031280c450b074041d18040351401031242d0f054030a0302c0f0000207240e030581028089420f586225076003005865007151112004880180d00030443c9602d03032407031b030a0950046600062115000c0d0504014451f03003001e07518280e0054580c1e40c44081062810314106200316008000b40c1040526048520301e403400e90038036410b021380f16010202c00a114108250405045036a004031043d601c40003015000240c180a13500850103145040000346c007003840020140141c54075512101042c0c3d103147d1b202804801d0040401c4205511107a0714401a00c0c10004410b20004584022452400c1101c540e080c501c905e500410802901c0d5901c41c19540383e00d401c4a06580a20f0032280f0b0003040540c040e10180b0440c1d947c040481013100c00c226031048007241c8611005a101c0210400400140c0c05244d411401c0d07624450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 938311852 1250 938310602 938310619
    0xf010203070b0601091a03070201060e01140d031b06050a0b0d031b020301140f07080f0c0403030e0f0604031511032511060114120102070302032b050a0c0f020c 70
    0x480c2ca003440c0c1e00c2d0700000c1490590040c4d41c60b411440c500c1c1c0716108040448003804030034014000d8082c01220701401d00210131481540c03502c080074070032180901010f4003540251002c441458443c2d05a014040202560700900d40742c0362404070010303d03040b6106c1789014130f0b250321060680340540307411034429015a0f900340071000500d80fa40c1742c60b403d00400c03a4159030310981c0b80c0c805482000e865200c0d100f0000c00c55098500140058540c000041241d21003404e16020450601c500c0015541547c0e05807600700428034000020441313007203500b5080d0340e1000020a000040200d00f02d0381c1146604046c1042c0420560340380b004401e03000c01d079400420302421800030f41344d040d211206484c0610681c6401c01107621000d080b40e092080c2a0800c1c0c0c400042080240b03064200b0f20017180c00403c00f88000c40c83e05041c4e0302c0082d164003614040e102901c402d500c00703000700201100c40c0200450b0b14107003080700e4141180f850004241c840e14100100701d00c00d02c1e2001e1180003040403140c59074090131002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 938313102 1250 938311852 938311867
    0x207090501030222180f05010b031c050d0e0609010b1f14160b191109090a05070507080d020403170304170c01090c09151a0f07020103060e0708010e060f010203 70
    0x5650380051311000b032080d5108102401003024456030380c0301c18065103080400324198102182941d01562a00c1d02a84c011070822031401280040e644114005151103900e445849010380d01038480c03000c0d41d005900c02c4c07a00b4814500010341c00144060011a602705298140a020003034000000c1140c1d40403e51261401120360880b90061000002d60240e58041200a507118503450205690140c8905a8201ea00c000c000301c502c1740d540f120700c4420401d810102080700140301003100501c042c0145031940c002c28845806407041c1c540569100d21100d4540440300314042c000e400601c030275500794030300421020064041c41c040700d02460700500d50703242400110248070710503408201410415940e071007003080401d0062041da80540007050010030030303a40803100304819085541000c1c06041559094559001801c0f0884640b004200401911941030703000503030007408694400001c3c040b000e02040007a603030251204d410b80e050f0100e030900c540c5070201445510140012030340d000d80d004010b00d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 938314352 1250 938313102 938313139
    0x9060b1b071512020426100603025406090c07020909030409020403060204030b01210b04050a0b04060203191b050d0e0a1a0c090a030210200a0302070905010302 70
    0xc508034964403c000d45071583d213074820380120940400480d052211000d04100c600001d01c202408840c0c1c00300140081c40c1503030002404085005560703c002051000c203840320700342101d1003004504903881c201030610f020140b00801c3d00b200f4249a00c2402c10880000e60794039006040a001d8045050b055041c01415400c3c0521000064115042c41c4402c0c000003580c03d02c54001000654840e850243c0c46518500e8105800355040e0000c1c0c50744000c84000c5c00100d131a0303910b8198026042444000184c50300e0902030306041031000081e107520042d0f0108424003840c0d40045002d501564141074804886030203120407100b0b5034a1001e4914807600740d40001d544201c01605005059001c0007940d40117003602d16103485000b40f412584015840d800c900c0c0152650540c40c0d0040c4d4509489290940060024452a645010007032251082d8003200c4581807184404107070343e8a281c615108070b4040003459607940c041c20101100148074004000ca03030300c0d100d03000c2c286c102c5c0d6002d031001e10301d5031021400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 938315602 1250 938314352 938314367
    0x80f01050141060a0f090509130206030c0c0a060c0206070216141c050c0913020306010b0d140702011e140c0703050705150403120c0905010f0909060b1b0715 69
    0x458030b10b040015000c1c02e95958500003401d100010740c80f01101c1500081001d4480043c1b580503921401951040105601080c3ea080c04800d904690f107a6403940c903000840c0090080c48500c43c03580c40b404202100704a01e5502c070040f0480c43c0d0b000ca8403d0f0342d40002c104c0c0d40f41ca11742035031807144198203000c00013a10f40c1c03142c8110030703400140801105041d03040d0001d000f2048982c240c40590045041c604a410b1000d0001c0c0c10102c1d05941e0b0105c440c1c103402003681c3c3d910600c9801c1014400080525400403d94032074612400401e00721003880c104804000d0290244546034a0b58504528140924101611444400043e203074000170702951080c1c121140764011030001c0d42842410421640001d009200040f6920071800e8508440e04250400401a520300803401c00d101b40b50030b10066020790003103400c000311902440d01100c14002d004c030803224200b05070700c800703105030402c0004581920440c01401000b500a0303070382013840400e5403440c2e41c0d40f03480d0b200720010150b801c40c080c00179502c507150 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 938316852 1250 938315602 938315699
    0x303050421270506030a150b0c031905090d0b010602010c0507020319030504081006060f170a0b0105190c110307150c06090b0a0f0b06190302070212030301080f010501 73
    0x3140d41540d940e0000c1381c41944101c07403501d042a0340d882c500c1c03607101c8140c4002004d020302503040360400c7c000c1c01c05540c0e00d01ca10426000000c08441c0805007581c400e400310f821040f0050000144441e043ca45899407480a00492000d07500300780006007141d216105851005800400030028030b44444456414846800015410000c0800c400314800c40d0400070b036103030101550400114140380c0340300280804601c03101303102003140c1108cc00707019450700c00040da00100032000000300c4907402c0c00180c61b01c1c81100b001e0203400003005858074640f900401c01c032014a0080c244491181d66910406440c1e40c61401400c481408105221071058407134071a49000b14402c1ea0002035030902034540542a0008887c10451144c84660010700050580520005500e040e110503060502c0c1540c45070030701e19a1421a0105540400c00d40d0555480c0400c00364550813180507659256110107078584c13210b541100305140f541c24031000040d4071682558441c1389018101103504105c41c4034818861803590800c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 938318102 1250 938316852 938316917
    0xc02090601080c1210050301110a181a09130c02151e0403080c070602120718081002071a0901061a0309060711011b0801080d020714010507051006030303050421 70
    0x85c00810540c6003417040601201103030880d5a207810520000070295a01140108004031800c481049800d440031a14150400160141c584030912100840c03000003640d1105e6041a0905481d400707034540103c1c01000c443c08403140705030955681d107204014032114403101840e40349400e00180100b80300350364030381d00007000e00b11003850507000340c48800c16a0414030407003860350102418402e00d03503004200c5402105555006980503450403840984034100100c080500d0790300010041c3c10408101c00c506803e1004000006123410001942030003044a40900d01000d40300c4428000f8001954041d40d10480c65807000b461a6035030003000703e400c40d032401c084544940d00c1c0d108140b0041b00703071300c440a80709c0115650f10302c180d0700d0701d00861315080030300601806540200380140b09645401d80380100300c40082c2803c550394420341c5441c81c505991007403110350041c50404044201580b540010340500d002d6180081c410114641f0341100394051000b41012170001c03241e2010b140c10b219841e40040c035581 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 938319352 1250 938318102 938318131
    0x90d1107030602040f0f0504050618060d0507031a180a061d1b0301110705070308071703250f020604060e0f0708030702041a091f150c02090601080c12 66
    0x250b40d0941a6001900003a0030540070380824405020004600b10042030b080340c09205505150002c120700c00690304501402d5044403002403203a0700c400d030100305083c0d88441210035103544c80c241451209000150810748600507800320303980b40c409407400038140764141d0241c4242141940e0b800010080d001540600f4410880d004400160134402980d44000c107007030742c22440100078201801c4500c20060820b107c0790600c805008038030002102c0003036aa100c2c0c1541d03030760300c441e00f02981819a61b01121028120000401041c18800b60f05420301410030520100c0041185000740c908090210580d80181d01141c00075010032072503002101d2400301c02041d10460680a0410341c10805103800c1400b1580c0002800070440c2454860b0141545403041c0442e035800c2d4050000300c000310050407440d616040d101010703500d60310440c00c05d030040900c48010340040c0f295990180c12848001003d03480741015500007407041d4020356225100f40c1c6002c0903580b40030904580724080582c09400502440c010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 938320602 1250 938319352 938319359
    0xf060215070c0c09090b0601090f03020f06070203070f06170114091504151d070507020d1a040c03120e0f010311070812010e01090c0203030f0a1e0f0c020105090d1107 73
    0x844507030003403d022880800e000000e406c0c43d00300400302801c0d0a0400c0090309040104055141284003601c0d4102c503102c9203291100f00043c1c05008490019605028a400009101060700700110844003a610398207884070030188000b40f0060709100d413541c420507982c01110b05103800180a588040c81e84418444882c013100807a04a074a51034001c5400c2c00c0740c903424806281c00c20b542c900ca00040c009000120728118400428a018804009010314542d14042c0c04020841044840d503003103a8840102074030345400c0801041e41c03144000d8469040001d030090b12244039402c0100c90b041d0140550490712100c5004400a10505c00c081000e98018040b040001d6100002080c1b1802c5c0480581100e504150860202c584183d200c0040686046620030f14a5000300940350b0000c0d99a5035014160f9031652103c015100f00c40c410301209140d4038801686c1c8860341c0c440c20301c80d02d4044003005681d046680a0303080740c03010744181c201540320340304a0001c03038800c051120040052a0a40300490795 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 938321852 1250 938320602 938320613
    0xc020d0f0c080c120a0503090d24050610030902010903020112111801020f1c0806060408010f09030e040902060912190c0801181e05070b0a090f0f060215070c 69
    0x10303160002082c5802c2180e0980c80d619104d030710881c203907490700094200c4952591710365950b485420801e500801c49103010b00d05000d448100454041742021784800039400c10001403000f400100c03110340c8034452038503c407000540b091042e24012a810384901c41c0e00c03402c0d6001901d86290294000302c906031104041000e2000e03038806403001c449240c03900c0ea801140c05001906106581d40007040c26444024451a440c4920303554000c00170f95402c02070380946031100810300b14030036500000115801e0201518040c42d060744220315240c001d0b40c80f0798601c0d009c02c0c03c010036542001c10203503201d00e09000d460018074080d100d00b43c150504004862450741e44c1c00d01c0c500c621140ca5002c1e2800c41034040c2c00c04c61007800b8000c0071840e0540d1b4030b14501c1f440042da1290204d2300c1303001c0b801d2040351120000c001040400c2202101a200003082c058540c0704103c4018100c0d02c03d406940c5403420b4250002403080321440d01c840c1924000d4020f4441c0c0032208129944c40321004010070704004414800300c02003071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 938323102 1250 938321852 938321873
    0x3040f050c130902030c0306040b01060c02030106050909101b0906080a0b0a0312091d01120f0203120403060b0301060803090d0303060e0c0a020c0919021608042903070c020d0f 77
    0x5000c1c2c1d0b001c10202000d004140c101a0b02409503406038100c0c03020000041d48407204541034940c036044c0340c111055203001183c0104400e070012030b0411218018006044400a00c28090342089001400109990510030b210f56510800715808682154001d004050003062001c0d48900c03034050000d0340c8000c85000400b1941294420343d0406a5840c0e0010415440166107000d040000b148200d22200389948000485051040d0001d8680320620202001200390428000c0764008040307501440f058128108103070300610046410905d414030309905401d06004110444003c880550f090103800ca05201c5440841c003408c07810503549080105503402d00e131001d14000d91007003180741d484601c2079401031715000a601005100b10074440410000100c6050f101e410780610017000360303c0704039032078422880c2a001c1c60b00505d03541c0089004509040001240912541805800841c002c9000c008066520040d81d4400008182802c146c016052495003000218452030303495000e20041d884800c4201e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 938324352 1250 938323102 938323129
    0x30d030507020d020304050102120913051f09050906010e10030b0406050a06062f010e010e0f0d0c0f060b011b150c09060c170f041805010b03040803040f050c 69
    0x10340c0d03400a01c041c4070350400541e081050103000a514140c14200040c1d62105003911a010742440000d10040a8445403820798903081401c5d818001420320705690f80c40d000382442c8030301d104041e01500003454042406090300491000014101130313404c0002e01114048010f200311503200030191b001001074403042d043c0340702300d001d8000044c1c03a0030000c1c40c01058440b207900075000c001858410014540320580d00c04d03804000b00204040d050103203040a40540514040d0305020b5280c9164243ca0307000c0402e1903003821406406880c414003400005446aa0740101c2c00b805c5107140c0003130f100c0080c915a11011092505051000c1044148540c005030b0400c00c000c00c951500304081c03501200c0d0842d00070321500c1e40c1d041c10030701c982d079060207030081007409420809405001d91100844101c500103003140c102d011b0a4190a40d140d496402c659036007005071950703000c49860300c4000540314250f82e0649024592101c860b5145d6117442e2552000c42c02000c1041c0e405008022108810f0341e12518400c022 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 938325602 1250 938324352 938324357
    0x2010216031b05041103070c05010e0d0c02100809070306090321020d1a030c0d1a100311010203070314032e14030604080a0f0e09011413200d0b030d 65
    0x18900391603900340c2c603240d0016009605254403c0c9103d070381c03003050341ea10001c1c03890b000c0381526950500c1c3d405452554034643c1d05020761000c00b400242c1c4403d05080040c025242156010344d080c0e000c5900020490303d00c040354100480c14030010321a0381005080324064038001581f020701103a8201c50420756200300e041359a0014020180d140c1d14001c82c0300c44400c108201c9000b07a02c0703c2c013103600d6648180d8114030440c1052048010414000104c0d0300409000540c03071040c2c649103030002c102041d03a000c103660740d080c80c560707001d001c3d8800400c6510031a816924802040504100040c1d1900007411000c0e4005406000c8035000d1114000a00b1403003811a1f608401860030821808101d018130320035000f500464104400f055100c07040b40d0044020303140c510f600e0400c45d1822a6001d0308681c0752a030000ca84000020910301c85d031400900d2030f0702102c50011070700f440c032501012250702000e424501100112055902c03503003a00507150001031181c01089612501000a08190b040d0160704007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 938326852 1250 938325602 938325623
    0x1003050c04110406181814151008090c1207140303270105190e0405070c03080103030f02070923070516231b191409040201021603 57
    0x90050802200c504590203440c10000c03041402c1c0c040c035480c4a1070091500f400b0034110711500c01040341d0303804c0004001d40b50316581d007103102c0340b0002c0180c01d00c1c140b84801c040c0c034100801d0b44c02070042c00810207003c4c000c010640700b030402d40040c0d0711490000d2200c074103402204071540b481d40302c1a80400307451146401600c1414202541919000f00118056001340d00c203000300d40f4403401a40c506061010003203540c1d00001c000100480e503912582c0120004002c000d2000c0440540101c40850107880849082c0159038400301d00b2500f0340030003000030300010320100040000c24082c441c245540102ca03c1039541d419101c5100d075003580c1c225407a8020740b03809000c1c45680020b06011640d00403400f0f140103440d18250559940c0e0040c00a18068001510742019400c041c07210110f0450074103145051742e06400540040c4540c4406400c0328901405842e245007644a01c081d5501080d1001c41c2107411070102220140200803034014412415840703182a07124590b513180c0b20080045105204052 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 938328102 1250 938326852 938326859
    0xa060e090604200d020613180e07060309020616022103210403121814011b030507090e0c0904060b040f050301180809012c01030b060301060801151101020310 69
    0x8041010b802d01d0300640c441118205a03441c0c2e180900c100c071080c5c0403101c80340c40d55040440303c1401c04040c2c0c0040c241d0320a0348003141e011245904514264040c2c6400c1d0703102c40b03035507000aa09942c030b03a4500130f60010707082098490203074840e515151154000740c1145090700c0d4580303e4071340450028284020702e6102080c54400154071162805030f41900e0082420fa42c2001d82e405080c1000d42d8500594039900c07000485540c2521f0b842d91010b0340e0300500c4410514409800d074500802d0006448403110f484220041080d6000740112805180160344401e00070b85846100d004c0c001d405003c03501c80b00300800403d10903a1300d90242d040548810764007955903614042c2502c24a90041c0e200c1d0340640d040c00c0001d204058004841e000c0304c1c0d0405000d0b9503986503400100c8008840712440146440e00b4144400c04d0840a00e803c82c00c0002a00e0400866910b001000660b020034440e000008000e80014000029165070340802044241480070413881a02c402500366001146c41d860140c14190081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 938329352 1250 938328102 938328113
    0x41a09010222120b040312060b070605090129041b020312181218040906061401030e0717030f040306051b1309022109010903180b09090a060e090604 65
    0x240b0b1040c005840c00c192580c90030a1903000604031020103401c00700128000b03010f25021f03c0a01c418400610810096030b9202c00b159030041e0065107080d58590f250200203003102c001442a102c0ca000340f07000301e8401d800c654100181c40903401000907003080c0c030382c03800030641d0004250411a00c90590051919a005d0111001d0881001449000c80755203603081500b01e5071021401d046102e174030b02000390740c2e1001180d200020030390483d040354000d07141c000c000081c460b481d4003801c25500c0590f140000c411001d0011420740d400f0300700b848041d4120020400461500c21031038201d60200320f00b6130b0b08000079001000c07d1904140d000340c1e02640c40c4d90400583c0035215101303030310104500c080b00d400c4c444600c0c004c1500d101d8038060145016400100440d04100460a14858002c00d0091448514003107a8050180150b01c000701c0c042a50144080f104280c422214070568960f000c140d0b0402c0c40e51001c00c500c80c10302400c3c982d4103943c2c484010402d15805040ca5114090f400e0040981d0b0030146000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 938330602 1250 938329352 938329387
    0x60f04090e07030818010908100501031104060617040c051804020112021c0c02030d060b040e090c03030a1d0603160f03050732030f01090c09050612041a090102 70
    0x3441c054009000600002c0c260106032000ca00c0304120344500d0040180050700c00d01d116030006c0f03140d03104110481e20601020f41126058922451404c000c448107030050105503101c0b8010303030001c104654014000124405020f070380c001d02078011b43c000166150042403401410700b42e0500c00c1203440040000359600070031190440540400210328082c13001c4600b40702c183c145606510300c00d854103a07200d040b91080064032580d9200d80d500b0803041d540e40c0041c0d000c6521900c1000845501800000c58100f401b01d150b50140d44090065458070000394021140403003c00150006e01584000e00003064403101e0146114990f005c11105003803048400c00b8203030030051541e050405060070100450700e9070248043c11031a0100003003050a460780c02c0d59400040c0ca0b16001f101030640402001001c140c04045035048800c1c0c040c08010704284810100e92172842c0380212900010304010101001c000c031158241c0c01030080031389042c2c28411800201c2c1a0009440c0b124582e90007041141c80000128003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 938331852 1250 938330602 938330621
    0xb0f07030207060c170d0e060c0d0501050603010815090109240f0501080c010e0f03010203040f02120d1d210606040f06150c080c010e16080609101109060f0409 70
    0x14098100d910360341c0d40724140c0c036420032140c0101c5c20204e00c0c0400f034200c40d008040c418039520144c500529112041c04050380001b402c070049075080500001e80c9040000c02c59050311240c001514280c0c803041351448078841e01074001d0800d59a6184140c010556454009030883c010307011405194603079050840549403102c600c2d076036281c0f07000c0c010400c000002030380711325585080c2021124502a080021403500c42c0d201501d8141d4000010070040140c03039425042540d100700c56040f40c6981c0760880c1e2790750b03100103000500490344081d00a500b040803490b00100758100104104001d58a1880310000d502c8a245000202d0380300ca0148010303440c080c013484034000040c40d001c0041c40c0c506481d04080120941002040c042d050081c1c1c401c0c005003204465500c50001c0c02480b0f002a0318012030b60b00c40b200c15242c02c0e04800c00001042443c40800c0050090000000900a80c0b40601404008119a090201c81d281c030400120703601d0703115040a8500040740700c01c6203407a513207400d40c64400e0394040707034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 938333102 1250 938331852 938331857
    0xe0103110301290a050915010f0804030c11270a0501120206090f0a0b0a080403120c02062e081b0604081509030906042403060f030602130b0f0703020706 67
    0x40c40043c140c2d1919000c0e1101004250900c80800010082141c3d0300042d001150860500c070100a0200c440010442803c2402c0c1e03203040d105507503500111418241a50300400050b038940d10000801c14003540641510b000074840f404000c0c41544003c00e2f84014207456016a040f0420010395168074481c09005040c80003030b00308002031030303800a00d42e4481c1c0e800301071203124298042002900c9903844600501481c1030803550300d030284c11024100c101c08590441c00604d10226031010201e0601a10520310301c1034004010f103803210b0005460800700da003da0000c140300403801056040b0090f4900008240c07a2018020314140c510142c0180300071800d10358000c2c2c2007000100503007600012246d0b220400c0c04102e205603104c2400d200d0030743c0f00d4600300960094010501285d004003400300c12041c261605000c0c46200111141501580c0c505d20076011800001c1e001000840c0c0240c00a007101ea84401c510b40000c2c0e11444a03004030b4210341048109100d01081043c00c041d010032000e0302a01c0c890 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 938334352 1250 938333102 938333111
    0x1062102030c12030d050a020d1404060c050f090f1504120308010807030519050f060411011d03032b091a0108070e0c07060207020d03030509190b130314040e0103110301 74
    0x10b0200d84d030fa0311038850301d44d2049a0382c0380021000c415580c152202d600070010140701da141500121300c404030095406a40d02c80c41c1c4906200710038010012220b24480c8021003034200f80c002d904104002d0380c0c145449401410441c8000503640d00c400c0100050301c080c1d07910010360703810b90400801c2202c05800603401688003032010700100700f00040078642c100c000b402000858001d498980d007401700800e14004117100f8203041c003081040341c1204440300704080c0d0755240c004a211881003038a050142d1026056041040f00303801c3d44c0407403046000c1d60080f4912042603072400c0c0716040e08a0301d990310709a43c6c008620644620864987c40c015004101e080c0041c5542410816a40711a034005003e480c4045000680c5c0810800c00d0340540d030009070010102c0245601c2414041d0103032108551042140c0a280e0040381500350002c41018407541041c103201c400d6740da01d040e5817103642d4425030580074081907012a4042416071002000502410a680ca080b0f501d1868040301c01041200d0052099040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 938335602 1250 938334352 938334379
    0x503060f041122081018020f0310020403030203190e091605040807030b160c05060f070c0503120604180807200a0909050105160e090417040b071709150a0201062102030c 74
    0xd041b0310b004110780440784034040c13607800c00000b0b142c00c0020746240103160011030004140740d0040080d050000310713800740044031500c01500b2600002200725041e800500d5101140340c1a40c040508402403049081c810700d0700f40c58442180c984141684112407003046ca0003009010014154154480682801c0000103141c0c0d03076807500e44440b401469101030850407800941c0c024030034008581440d41100c00e0700d5450070828040310b0620411102039005c1c03070409614500b602011403501d882d590300282d2490031700c403041d562007180340c030080140550440801c1240d41d031542c811991100a00e402100050b2940f014a002c50940350002d140b0031807054410300d140e100c960840c54a90b06602e08613500c2c011940c6034500009480c0b4040c070403c076914008600031401d01101c81c01424454050b05030501ea0440001c00b41c0e48074030400c1c5200e500038241001c3d0044150300c14003c0c0c813408081d4000868250348a801c1c0c03025201d02c80c1c2d07031280514418003020f001d5090510600c8a105000e5a0040e0141003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 938336852 1250 938335602 938335631
    0x1804060f090b010b0f09100309051c0203090108090c03070e040b06030a030906081923010e1017010b060d0b040f0c08070f110a030c120503060f0411220810 68
    0x1c1440f80d244c80074000521a16298100011603036030030001880e0010005c1c180c90024003c0c520020115010312803044140710b03044845019071180d0419600a40c544489003004486d0070b000a40700081e01d10411051103c203641c00d126520103414000d070030300d0942c901070a1203810394078007900c401e001390040307841840843c1d4481c00000c1520528100b40a86403503480403400c40c08802750003034921500d0f1840300c07019032802c00c49401550b10703902e2010003642d03220039021544250690710083d64040c00c8004016207403501c0445013410b10b00d0800080e045151001240c49544145c40c003008143e40c802c0603038030314502885500ad0410000108120102d16440003801c640b1001c0c000109024402460700e51251040c18074200f001407100a98074548140d240c05400c5180c0440201c0300a0303824099001614850001d8920511008120f20300200840c0117200050100720441c0403048400c00403554030b90011022b01c506500d2091124581514103c000c90030494554010141181094030ba6000c180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 938338102 1250 938336852 938336873
    0x301609020f12040807060e03090324070c02130e16060809060604180204020d020a0801120f0b070e03060403090f0f03080702060a050723070e010b030a0506010302091804060f09 77
    0x40c801119156403101c1c200151640a1003800506d02420540c4200d00e910005c001740442e41d40680807990700c00e800041550102e81c2010040d5000107100e0000317110144202c11210003140080e03c80382c0030003000715182081c2e40050101c21507590000e6401c502980f1040c0c1024001c00c01d0340340c00d00381414405501c42e1201006010103100d4bd48409418000a40160030000d026600500840d41d505509520402a40080c0b101201142c1c1d140000200359151142c0000281d900100505c0781800daa9201001c00001030076a008004c500420b0302141d0320200012030145000e034031045500fa160108400400e140c84d0495868005401000c05c00950624295419568100e807182e40301c8186100858490040703c8002d07018107401885c900303968a00d6004507400c018180c0c15640196140c2550000030b443c00c0c400c0c0c1d1040c03041000001d010840e164403503a0030940514000d403a10100342c000900d0100c2c07162440d405003000340c06020410040d4400c1d20441344110b101400344080750b03258440b488 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 938339352 1250 938338102 938338117
    0x30e0c010c05070b071b051f0809030d0603030503091e0304050d051c08010305010b1017071404060f08010f06140c150a0b0102010b040b0906301609020f 67
    0x141001c07141041100c14406400035141800c1c0c0140c0303a0009080c0401a10f0340c0f41d21030743c1515215000400c01d03080c040101021410f000000c110000c1e0000c9003140c1f5604000e01001243c0428404140240d10502483c80103600079035981d0341700e041c4940001d0400400285418001c0300116082d41040804030544080fa5400c40320740c0c1810324103081450404002c42c140410041c0c040381c81c981e400d80c010348800d06890090008203c01c1e003858060201d4485151200008110010a8000d072542c42810455100030a032034065504a140c0d010400313150060303002070021403242d40360461401d038050707406c9004009800d421110140341c40005040c071100c0104c2c000c0d00b02e1002607288501c1c002040071003428504c1c44106400ca181201402d0018440300107254015420b098603001c00349000d005600501c01c0046c56200d250325100104611140d41c0d00ba00403c0b041ca0380d0301031401ca010140d8515072010b03040d0152400d481c07089001546054141c00c8400801c1c818815660800004410744988 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 938340602 1250 938339352 938339357
    0x902030105072c03030712020a0327180b0a030308071d130c110601030503660a0c050607080a0305060406030f0c0e1e0c03060d12080106080601030e0c01 67
    0x1410050800b003811441406c4010b010200b0400074800440da0029420300303031a0180e910f8035504840968106c01e044c0078480c8888a491001d501400940d04480f00240401120a00010180700150201d84c100603141d100740d010070846010460348070b03000780031002042840d013801040016400006080c40c06002d291140f03a550714071606d0b044500501284548032030b990200c80c06503a403483c000341e07030360702c114000e03500980d03d00e2864410380c25460006c44243c00800c2c85008421000f408030b410054982c0c241c0ca206160b02c45d46152a143c6051960040107985c8042c00e2002c2c40350402d6019990180c0c08076001710300402c504404030b00c4100640c2d02c06c1d4900e00c0e012806440e5a00014003074802c4e508094410454050800104540080260104d134000c240101c11a40e4011144001c018507440704595a4101c00016150401c050300540d48040014441c04d10f08425840d02c119100340c0c0c11101c40404d005034014000c2981040489078400000d103014401c0c0381c81900e06130344a0850b003940505 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 938341852 1250 938340602 938340677
    0x303040e060613080715030614010f031118040506011110050703150815070306080a020103150b0c0f0f0a1e02030a1514060a0f03031b0b0703090203010507 68
    0x300e9600e40045500030590584001403c2c2e0b101d08200b91985c40030300c2003410113240580100b0790103000f40215821150450b0011102c4038180c001941c5040000c100790081580e900804492030903000040c01c0c8a108541c0e5011004805406000480e00c01411041c10b0010f1002548541100014003400f0501400c42c00300302030711100c0c000d81c0944000096800700489103a004100f01000040020405a000c100d65101d9150032500341c044810902030803107590040340c40c0e0700c0513500070f801c03000040d10f1108a8444056441d14008250303084003d0401d915001103150042c0350408201d007250700028000030741030300040780d030b07401030151820020010009074a494900a640d000d000d0300805542002c6c0080d40800703685070000042840584039989540c5d48000300d0043d05040d08850192040600d80020b01415501d0a450b40400c00c0900798040b125000340e86d001581c844105401203206850201f8181d2103841003601303490000b03102408100409030341a052072240c1c1c00b100300c1c44c10515040b51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 938343102 1250 938341852 938341861
    0x609030313110a150305060a060807050c0c0a0807150509131d06090313080a0c030b0c1b01021c090c090216020d050c1512010e1305010903020c0f03010b0303040e 71
    0x48848504081150700403400780f800200c441c1488000c9100c0c40250394100b000d03503900e0041202401e114042c1c4400a40d1038030004400a000d94000c0c502080a40c045841d11880600003036444800b07500581096004098104903040c844a181a2044030364102541007010b0280842c039205d0744e07005464442600c9880714049099181070501000d00440c05941c213070310f40b149072242c6da5405145000010a9090400107500d4004158104610780c0001e814a005103152151400100d004d0280300d07009400f0445080303090381c24041010503040e61800540c55511281c51000301e8052007503ca04a01c1c10314035405c0c000380c20a4000c1054403100040180c0b02c0d44044410231804401d040025004101c1d13110050900c038002411b02c00180c0b08890200a007002c6448001c0e840c041d4400d0104000ea9520060120140d040611540121950094198038204d521502c0c20745a000700c00380c000d81c1080301030300d040f810301104280684006500030f0000104200110f07940e4821403040203c9140403a003c40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 938344352 1250 938343102 938343113
    0x901030c09030506130b1b190905030f01060306110306030a20150904050c070203030712050d060b03060a0b04080a022206060503011e0509010b1b100b030106080609030313 75
    0x2070055504901101c0031803030400b96001c210b070b0381040256582e4216a00003015095a0120b1170120300380c44020a0518803080800121801d180c1c1c0c1c400e05100ca95040803469480030005e6a000022902c000726141c0c0ca141081012a012640400c02d041020410080542c50010301d42d100560300c0b48a044610464a251050b0740c507112500540c00040341c0d5181300740700c1030f5001070f00209404860400554603003101740240f41c4070b1000000e42580090200c100403c5c00e042003107240502c0da040c894640940044000c2c122440c40d0010f820b00000802031010300e0070410407440180800f000450715090074800b402c4c0c1c0d01d12040000130712888421021485441c13500045603140c81a03c4028810030b61502000303821038100740140340c40c04082603038240c224201d500c803042c1140c10103000740e00c0590820402d4146075114101d4170a0394010010080e071544010040d41d10b6010580b1310004012005000305400c1d548140d110034043e41c001d00912101000c040101d9401402800b045110300c00545440f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 938345602 1250 938344352 938344367
    0xb0112050f07080c01030509010203070c170f07060507181a132309150603040f020105160c140303030420010c060e010f0506030a12140c240f0c0901030c 67
    0x1550302401907000000f055040018810040e1100f62810700c2240ea91620307040c00c0340000c5440d81d00041c212441c00700459400c0520842148c1c2007890586000d54005012400307920248080710102d98803000c014030964002c1c0580850550407a03c4d500040c40c01022229540340b0680c036280507a40010104428503000c43d0705002070a1503090001c500c0136659980012086140000d4090202040062201c0204104c04898920000c00711030031078846884030107424001c031800328184042001a025942c0c0304907142061148a03074000748100d41409a1040072100d180d501034040c0e44188140b00c0002c0b420403000c01d0001120009407a54410000100c6103007000d403030050201890021014070082c010340020481c0d4800c18020b000c55103410f01459035401c40705102910703502140c0308200c846441641145c4140c0c4000d00340c241891683e030306050900301d03240241c1000d0040030702c1a1000c600c1054103260301c030b040030315130b00000c0c80d11100c3c4240c81d00c00c00403d141003507a180250b020b114000c080c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 938346852 1250 938345602 938345623
    0x405070c0210111501091b0221040e13021302131e170c0306160e010e041b02250509040b1e07022103100b070606090908120901090b011205 61
    0x468000c402131026005401c20280240001d150601d140c0c0d0801e00d40504007400d500d2099802803042509803640000005048a90410700701c00401c000111052042d808034081da003060340b0090306520358030401c00040c03081070b40324100c1401480440c82003810302d01080304441007804920b00702c130729001c8480300b5030100760440f161401d840d1040311101980040d04036241d0300d0036402c0314042d459040c0015000045000103100281d0215042c2019500c150351111654001400110345404941c5100d0310f1100c2022102005034080c1c8100c0c910850007104000304402c0f2156031408082c1000049100303d48000c2000d002e8903035400c0803802002e07180c40800a102221003949545042a480c000d4944444242014074192403695134800002d4107004c4078020b14900ca20104010f1070400c03518050381164905440e101d03616980018006241c1c0110203641d44580b4604d903640303500f9025203d40c801e02170800c040d01d07032601d492035000641c039400480c1940c10703031000280300e07094519020f0b10344100c00c0e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 938348102 1250 938346852 938346887
    0xa140405091507080403090e1006030c0e10030c0801141c03020a0b1303020c03011406040c02010b0402120601090909021507141e0106142416110f0405070c0210 70
    0x2d080001156201d0140c0d8050b9119503501c4c40c59a50740c164002c981c0704140d400e25204912160304203d0300b8081d50000101c03c1c0c0e241082c090700c0800304000b45d403441c0002030340d40109803245000d0010b5580300c003195000d00103041c945005520302034049882c0010300c5c0d002d00c1c3c500140110780301c185802040000241c84d48800d079404a450040554101080e4000c4224054450441150014581070090f103200404140b4450510f5561030204400f0707003c2c4d03400c85002d5558034800726201e42c641d0300003403071307010f001d080c00521b00e051a2000422450b00382c2d0091600700d00d0304907081b0050340c4041002000c0c0840301102c1d5100c45d000d007402100001e03605540500c0303128043c407a40148c50b65054101d148841d410003004455641c902c940140b0b19444140d59000d245003460f610102e403601c03204005004501e00c29402c00c00e4016400886a8559a09858504400b0713500c112501c0c2c0070202e0300070303508107843c180420304009402800280514030020702c10312140b061000414411003042000c4d003980b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 938349352 1250 938348102 938348143
    0xc0f081303080c03250b06100903020312030906060102191709120c21060105090907030b070804020a06140703081f0306140a050402100f050d02040602010f0b0a14040509 74
    0x40c1e4056503940c010f00e0302a000750742d0740400038180850b581190a495411600342c1e1900c0e03480c0c000700056a0041546c8c1d1b01131206060b8040702585040003840c0001c0305c1714044943e00d05103264190700c2c14800420050442d8016210414466121940c181a1980c41030008010008000d8901c9442c000c00398441d4120820351148010070200050f0a900d000065400e0203585550034281c46d8040343d80c082e480c0c1c01d0390003600100200e042038140c82e94003842d0103003501d0a240d1641e1310b80c03907400c805850310b00010b0020003d000941c0b0b00820410020441b60030480700b14504800780e010746008020700507090010010006d800b004d0380e5412407500903182e001d1680b0541e181d2926000900e040b5a00d141c9059142000403107030300652040b41c1c0104d0b0020b014615030060781c90225a1010300362241400c006040c00a03040303420b0f450020704042d140d6600041388259649040c1c6e82202c5030050303040d200d2000c5040400050061109515105000f6070380858a5500e84001602d045026050740c281130196 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 938350602 1250 938349352 938349367
    0x112330912141602010c0203030d0204081501080d0f0503070210060b0a080903181306050901240e0a090209062a1c05090906031c0206160c0f08130308 66
    0x21000c144691100d00e88540c1d445480b910164241401810700030107040ca5426200740156020b00b880c00d41d60351004044034941004159403c003a07030016406620203602a20b038080115065520960240081c0001420f0b507151009008204035640c0e842030041c041d0000110704034610030302900c11402c0052405024860362460711031902d910003100100080c00c1c82d00405c80c400c0c0c1c04011100100c00b1400c00050000344481000112041c6210f00000140d039118002641c1d11800d034014003c0255110712007050400c450b4160380602c0c00b0400354100415101c840f0600e5541188007800c0d603609080060b243c2024101150300f42c442c200c1c81e0030000600c4020500035940d040c2c1200d02103000c3d44203648515084040d490b088892100d401c4002c5a014080e400490a20113000343e403084005045544181e0f07200c8070715090103e480070a00068100320308002c8103000149590120144a00e070100644800c1d03200c0307446045420300d0045c214900010340e4002a03815182c200c01554000603081d81d2844c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 938351852 1250 938350602 938350613
    0x412210804110d1b1a0f030619031703010905360a0813090b010f080c070204060b0a0f09050d23070b03131703131211010207050a050601123309 63
    0x5482c0b00d8a20b01d465031810f040341c440c0903501550000c8440060703403400e40c8c0f184010004540c40c128014500900340e0f807000004500c5840700487d1000d07a000383d10b90b59505040766402920001000380220391070441c1d0603403800d4007040348600b10030300b07215a0040e0003400c2100c040c200042e0120150074140041074250b01d41d090180600201c420b062010818903006c0da00540d5540030200010380407994a60018890b4036142c2d009140051004000003240b80e1503007860f00150f000440450002019101c3c1d4100050300710030084041c3c01c086400004071260b41e0b44e0a2401101e00d98400e91404030090524030401081020390050110740c41c1d141c0e12454050410001184007480030b03a0f001c6003804850120002c00e20441e4000c107100e6910161030041390f117400032501204044002008103059104441c0c890a02c0a0700d0081d00c118040c15001c05141070003441e01078181c03c61603212000d115607400050300d00c4507080982058849080c0b5202c4420b4a805440d400f070412036002d10305040135a410000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 938353102 1250 938351852 938351903
    0x7050c01020d1b0906050f03040f060606030c1106010b040302450a0204061409150d0b1503061f0c080a050a02010510060f0302070206040b0412210804110d 68
    0x104600744140c00303004080f500b283c0141c060711079280401c078108481001c0106020003541c0c428000d6a0201d91101d050f0b4451003101c6481d400600000c2e074404003902d10940c42040e5103600881c00b00100f690b035040c00300c102034a21030b52200070320400c16410007100c030781500c03801307000170540d09000700c100ca807842c0850300b881e0001e40d600c0d100098840d40008034000340c103200744ca0945504e6a0340c014042c1d680396030500c041c0c0c410003005500024a41041c2800d462880046c892280002d1022035446105c60074480722003240c084040a42d102401045090303102c083d0a83c0e41e044112100451076103a60b070b016900074080340c90250045c800003802c0140c1c143c1180050003c12403950003004141d4800b4210b0276489074034000d010004d40a4241c0f50b03000b80c440d4029000c0540001c0803146481c0d44e808a41a40346e00a510004801c0308003440401400f080c00441040d50516858079484410b140200904070100180020302d074140ca0510b40d082d03615030402040e59140e02000440b020007030300c2e00d84562003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 938354352 1250 938353102 938353121
    0xf0d05061f061d030f0d021015050f0103110c191208130b0c0423042003010302042711091303140a05070507091a0406050d02010807050c01020d 63
    0x2408600c034062040c1c42801c0c442821030315240d441c0340800c4a103801c400d594121190241d54103220711100ea820b181c100b4030141d142281c0a070001e00c1496000036601007960a0b46200010300c500c0001c08202548904101c680d110000f481c0c0011038003c00403c034101070080b042450a00d2040c2c2ca1134145e40c800c2046255240750041c005c00d429290714040407662a48112101e09104981c0d01e83d103030000c0c1c1c1120000d07801032040310f001030400e80c484040b18400788220710b041c907812965031001105424907120740c0300c0d5480034501c00764003681703801103d541520040c40000d00035a038540700e94416200c1c038076000d0340c0240c020030441c821503101d082c80f12030100b0619800d442030b4020030208440f03005000d0318086595268035103001a501602c102e0341950441d91940702803000c10486400050014070400000d002040000039100d9501e0720100c3c011500d0a0809004038a040c1c000d002c40c0d540c031508a03030490390900e005022965140812109400707803682d03c0c50558008901001c2e5035000d500440800d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 938355602 1250 938354352 938354371
    0x9210809060a0e0c0904031130030405031b0c10050d0e0303160e130f0b0306060301021e180306091b06090109171612031409090105011b0b04080306010815100e0f0d0506 74
    0x20081f4808031109da440191001070696104125100c0c9207370302c0e600031411b050007841c1035450382c40101c07020641d052501c0020000180001a0401202c5024451540307544101c00c011811860540302d00180300c0d1206411405002102c46605115501e2171000282d070303100f03d14240f01440e400c6100a002c0c000d03480181d4400d000d00800038a9504052003034131020b0041e040c150058203000024482140e00400103011618910780c2405501e032403c2004600914804000b08140e0313900444088a41c000ba109680c442d0780700308111003050b80e00c01c0c6071200780e0b1502d20510380c1500082030403925004018501104010b415000040c1a2040000d4402c0c3c4d01d000381c4410306008090800d070140c51003030000ca6580581014010300c010b501c648040c0c0607405408120f400c40124075200c0441d60207044a080301c040c2e400004000c03180d640301120780d400c00321944121100b0b1b07041000013041109464203042c108013200b50342c0c64665030b4203030b0018054040078024860411103410020744802003220420365 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 938356852 1250 938355602 938355673
    0x16060c1d0904050c01050904020d0c27050303040e0a24150206010302060414031009050109061802030a06050a0204050406080601061709060a09210809060a0e0c09040311 74
    0x40c509100002500c80c0c0d0703100700640706900c41640159180d0300020303116a0816424006074102102510494140900036291081083c1c2c00740789140c9030312000c0d0610b0780c008490580802040d10000300703450503103082c0b010800051745c40108107801000c142b00b07030041c0c011520000035101d003100c004c02d10503545201c1401e41e0011a03000141c0c4d8884081c44020741043d4100001c1044008140b115078440e8801001e41d6200030324450f00c0f1042d078410040c2075905943d203404040c1041100e125500c1c1d0301003000311450b81411070340c00103600c422050002078089922800003402e024107507411140505402401003000c1a10303074200d20780c0c03260240640c001184109501000d480d041e51005846520351500420440d550000c0380c0014041501e82114600340f046440050f90741072500140d00c1e103c05581b03040e590720701441007a1a0074005005410303100d142c895000d101c10000b280101491030292a28011038a40e483c040b612014020356502c034600510010010103582e1140001501e02c0b00c004032030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 938358102 1250 938356852 938356907
    0x806040c03020414040b12070b09100c11040506040b0a03050115081c03090204020d0207060b0a0e10053f060601030605101d0405070203071b05011416060c 68
    0x18200e100d14000e8150505071441318283c580740c60f07080010700403409130040b585281d06507003640c41c1420030717080642d403603401081181107030400c091203500307500041c48c1c4040c0c40c018a4031181007401350790300000d0103135490300300082c1540c41c1d907040540da04030041c10a098055403070401f20700030004402500400c600f180301c0090090000139040d13503403550032500d01d40c40c1c40060750203500410b80c07180201e81040c0c0034000700d10881141d10140400a00802000c20401d0352281003254550854000c7c80e610a110018480020805da101724184c902c140c8442d07401503004900002502c00804440200f244412a0400084401980325494070348140880c2e13180c1d1951001941070380c4581c080e10340c0088004003505051807103000080703440012000380114040000000c40d041c0c8008035081c402503800003413014100403498070300b40c040075090743c155031480f424040002c00f45080346444410117070000c24521500d58030490110010766000408114400040c080a0100d40c2d1813855803454200012244 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 938359352 1250 938358102 938358107
    0x50301090905330a0c1407060f0f1a101e0c061d0715122a020304051512040b041e0614070201200310030c080a23060c07030c120806040c 60
    0x148110741b0f403101e034400e100d810001c07503410241050710110303101d61103070388881031a11408901c1d080300e40000c41d43c584010140d02110304403442d400d0007020082c01030700400d9408003600034034a6500400070003084203c1c070200c45003c0d0b402000792a0600c1c0405617402c00c05604030351100041d02800380da82c101e44d940808000400d401070500c012401c0d03403517040e0420219a1240310143c15000c812441c000e00004c450201001c03410f40301001d40e0001600307021602e00341003014038040d48008a1403604018812404007074030050300090a107404000842d08128581c402c01030340c113031001502c0300d9002e42800c100e00940100d04061a18038041c10100340d803a44180505500380014005002c42c3e01a8000f0903c2c4036400140310300ad0072680b104000c000604000c00301c400601c2c000c0004d00002e02d083c1000203011100c0d064421440c103c1190041410001050483d44111103403045500c603105824113460003a0ba5090050030200c004051610302a0001d941601418040c4c40c200241c20040000303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 938360602 1250 938359352 938359361
    0x501050a06050f0a0309050f070e06030d020709150e0901091a1512030405031501091506170a091a0702010c0305060d0f0602040e0702070303030c0e01050301090905330a 74
    0x410000072000c01484030443c1c60080101610000d928002514040700d40311941400c040c030303400d02e541e50420242000752030103040c01290003000882c00741c1000d203044400650750f20f049105002d821034680882110048e8070b060450002c081c4a8130482c014074159500500030991060121401050100c91501c0140901450351040002803c0c0072060200442000046803001941e502070303100410020407076450600c40c07501d04104110301c02105505001da94010340d0b120242802042001c0403081100c130758405c40503154154260f16040854a45041c0500a814140009011000304000e0030450020904040380704007155030007088a04c255641c01c4058481c161036159000d010b10b20050086580781100840300c074414400145400e40e503428080002c5000c640c0080940c0011404109054040c050803007401c1e01d520f003d015202020002809600043c02800c0b61650f8407481c0c4420413208020a052440307004d500020781d884a0320994030003074100103801402c00000400b258080015015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 938361852 1250 938360602 938360609
    0x4150f0c0f06020706060b0a03020d05161707030b03070f031101110705040e1c0f090b042720090f030f0a02060f160b0103230d120b0a09050a0501050a 66
    0x100d2149a05803502c036880a034102c0711041e200301b070f40c81c18001016180c1c100100310709160781d180940c84a004c1080501111002040e941900d40704058000385154491a0f52170a026407190004142c1c6031400200c000741001c0b01303080d40500c10700c000411803040a841440482c0e10618540031a090000c0c011109100c0641440c83d2a03840720b0014812071500d5082000301d6070b41c013412200418603842c448103c9051700c01007a0042000f000c0307c55651540450a02e0142c400040c1c1c440c0341a2400e080540103112140500c1c070b1131410210305401c0c1948541008911402d0303001917040c95107001e084011940c5c000003085e031051500c00000a410b007400300f038022034504002d002c1d1006034600d4091160a5015901d5420a140104021052201116529001c96000f0307940c10900b0743c118501840940791310b802400101403404d0b10312210600c00074180a5213522841c12024001041e20121301a10200301c4240d070080040c1000709083c80103602c100e20540044000f4011641d0701c900b8440701080901 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 938363102 1250 938361852 938361863
    0x1030c180b01140c0a0204020313020a0b0304030509190b07050d0914060702131119021603021c0201140c030d150506030109053102030601050405070903030305100b04150f0c 76
    0x543e2107640d442d008000e080c14580c8201550380c070340d5241d030000d0304a91007203a03203401100d850070350f040035802c29180c01c001034144660458a103040a460242c05402402c0099100305d07a998030380c00c40300c803499005100501540040640714041807500e41e0322410310a60120000d02e4600c8009209007444050b1048a113028210b03d140401076000e11001a1101d0720b01c0ca0125103c149600101890368000d000300c0304803412240d241e90342914024142916482c00882c1d02002000610142e540d1200c01c403120205480c900c44080040d1006985000c11048079506113070b804030304898044004070042285105440003001820b4184641030b503d6400303400741540215040c4014011800d440d4400e5401401d107a00b10149a545610008007010300c1174048800d103a5004104d408608041201c0c50140c50103c1301804030f89401c5070000d109007018880902056241c0d0082034060a520b0300c84006400b160035199550b0f0f031601820764000a0440c99400016400105451f900d440307021103243d41503004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 938364352 1250 938363102 938363117
    0xa210504060302090d080406080a060f0302130203061801080a02030c03060106080c0d060b0a09290a0c021201050c0c0607030509070b09040b030d12150e0a2301030c180b01 75
    0x20070118001e4100710b603800d40115150610b10701282c8650b024000610841d50381c0c020a203804141c04054070040c1e03112032001c0c5540c0405000507a60b40002c001000c0b03007070380d0058580d51084001005031540c0c811303001214004c4000800c420310041a2941b04500940c01c80301c0c00381d0241c05060313590109100c3c0340c00065214000c209551901b000030f000016030f040c40810000e442d81403013a144c0d44010982000318580745800c00604442054003040d4030744503501c100d04450a006050b4083c0304181d000c008000c100462442195507400701e100c8003140320402081185403000840861350301070402c00145204100000301c11520034080d4030b11900e00c0c0001780c440b0750f00d000c00390601500003a207402c0c0c4c00368484107141d40945040003500c0340801e10faa20020000142c42000c81100d40303680244000c9000c84400348030003000d01841c0c64010004080010f038001032101e01e40790288880402c040b480144c50000018020307441d6400060320310308600003815100c0013444074215058005070364007041c142d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 938365602 1250 938364352 938364359
    0xf030c101d0607021b030c0d061104081002040905090703050d080c04093917221103070509072c040c0201090b130f110a030b090a210504 60
    0x45070000e4010401c0404000091076512801078107003001240d2410040c2d1001240c40250244102200214082075015204880c00440480d6004a044001805064403811800c60901c0d50310115401082c001017518881500583c0d1000617500a11418040358241070102c1c034100380110340c0c84116175104000741100000d840096603e048000c0120002c0041404005051540d034003507948001c460b41d00240c1e80b03d1000c03422a080d040713000c490515095603c04500300c001d0300403a50034055024030303e400701c4507900c3c2c0c41d41d9403030700100d030304410100d002443e0f00703204001403c86440080344044040d610704c183c0301c034180220180100e40540c0010074a1030045201410380e010341420081c0315060400381c84c030500101c0c0a8400d000031100050f90758002c00700c1803081d001501c82e007020441c00318032600c00e05515141300d03540503001c2c0601607032560f0106000075620303250752100460740007029404510b80490400d44401a102054404204603d869856962023603820104035650f2340355103061506 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 938366852 1250 938365602 938365633
    0x30c10021f05010b1c140906100b0f0f031305011e140f061201061a070213060b0f0a0e030d08150f09070f090b07080a090f0f0e190908040501020f030c 66
    0x90100045c2c00d095403200040c02c0345000000151080c0c0111008221500b440078a8207134820705036103c001040300c10b11000031800880f104407002c0c486451030013a200d44509811410009119500520715841d00c1c0d014140045012204e110341725480104010f0340d903000d5080c0b00400e004031070b8110140300300c500254030b0346040d14007101041c1c0383c4400040c01985816400b004840c034410041601980891010118a4862500300003922807503024400c4070718020640b1060b0140c2160a01d8600d4042130702207070a44a01070018030350900500b1550b010180c0f030405411508256800561002043d2110354603080c42d12000500e0300380581022174540d18a03a04a59610301074007540d0402944000008406a512700544800c0303003d0300d045655400c04c0344014001c18031540c804014140748150800001e407441883c4070880d090b030070323410709a581c0d00c0d01400e1000c8014082c1c41402840c00c00e8a4042c0704404025005071903081e000c55201c40208041280e8078000e22030a0440b6a1144139203056010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 938368102 1250 938366852 938366887
    0x480303010306091b0308180604050a060e0d081c240504150306050c030f01050111030304020618032b0513090c03020f07030f0206010b0c1506030c10021f05010b 70
    0x50103800c4d1080d00c4040400d0040c91081c0360384c0245c07140000800c00060716001000f045844d0801110210b280c14903041c041000c000c160301c5030720705000b4004003d00560b140c001c1d5000850f0342c4581c02540d14201030003210407200d1000c403d0080c1520340f40c2c06102c2e0403000d5100c60701c020340305000046050314100811024102c00760164120303000d90b000c0000056000d00445006410318048680c80745000e840c540c04400e07050b0300050401c81c0c0d103c144510390f40c010044130381094040c0c1e000741c0d5540c420000440c29680b501e500035007521a82c505003040d0301c58a554418411200e044010181c840040c08581e40d0040b0040e08042c1d006015041101691560014810240d20b090150070030301c140540c814240c00140c41a00850001c94001030310a46c1840a9409071094600690502e010030410596500c20f5842c10425100610041801d641e130030080c1c81c0384214000e201d0780000200c20002900d41d88503203d11980c02d0f008000d03903a00030f40240501030607500c0c18500303a41009005015070a9a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 938369352 1250 938368102 938368121
    0x90302010b030304090f0b0301020313060b0604152d1b0f0803010e011503020406051b070b130806090c0f091f0905012c01060c08480303010306 63
    0x540d6151007003641a101400a00b00600c22980002480c00c140f06a00c0c09841e1040525403085e48100100212150340d02240b68030b49800c50400544080c4400c0400e4140c4200e4212120700240041e2048040d40c2c44403460410110b00e00400144d07401688040c100c210b94075100c40301250380c03842c9900c1946282900b810b4490702a0301c0710f20410159803a800c074158402e80000c0021000c2800500a204407000c980240725034515045280501d00320f80100607016404e00d1640d89101d1078003041300110100100d4018000b10241c65640711040041e034004800c1c41d05c6400030600407800040c01003100424000910341c8050800050b000c1380c04e0404c100244001e000094113040d070754000c44944c003507a01c600301400070620002030950600040d14030420108280034004d01a0b09544460380c801a0b11150445499050a00040c92545401c079818011414400e00720350a21541c40200346071190342c4c000030310401a48548802488001c150214140d4408290356803040004000089a550069082 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 938370602 1250 938369352 938369357
    0xd0201290109091404051504080412060b0a0e06101110050c040807120209091b13180501020a090509040512130b0c0f01050703090203100902011b121403190903 70
    0x1e00c0e201c403140c00c02c884c407681e10442850001d030100401c1110404c01d1003c1078504800c11074040c13806584030136651040d030213046038150303070085950704018031a00301403020354009080e00400e98861800000304e801c1202e015200740344001d180c1c41d1040c01643c01ea90759103c0f075006494925a54120f00003d003001404c109803109042000080c540024040b4001600484c04515074000440c0100302c400e40014001c20610703085070701c660003002481c0040344800c1005031240701507403c2c401100e1000b000840081003441060035404e20800ca030640c0140380001d4241c40b800407032912101407080301041200c004110b41d10012003503141c2c80b90007000d0140e4011070060610f0306611114224034942140c108080d07030b0307444600b008407244402c1c044c00c0e91011003490104000c0d803054000a42eaa410350650b00013859590f01c0d20415a482900d110301c01001503000070484079201e1031b020201d0507244d80c0b4800014900624901040f800310100d90040d0413504c0120b12007806406c0c0c0e031006000b440c00c21000e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 938371852 1250 938370602 938370617
    0x702060a0905180402090c03071b021f0e1228050106030804060f0210180206310f05190e101701060807090209013207060209030d02012901 61
    0x5a90f501c568038034a0003c4882c80342002810b081c8103002071003001034603190f4108001d000b0000407590007884d120020162080b0740946840c240085100c2142008a080c1c144000b440440d1402c1e402908202090200b513500b011183c040303441c400d032104a0782c182031554210301d0403005500f02c2064081140a400742d00006005582c81d41d5141c910f0780154403600204940d03d500c40035858041c8400800c1c2008d481040c09030140314060410300792000d0070024800c036004206480410001405c0b080c0d1401d01030605005030700318000c820900915481101c1040014a901140d542840d00a048105090580221405062404400300310200030321541000d03c40a00010381c60f41d15030b010b10201d1009000000d6605d0414a42034281103641c1c2103030107858010440c4d00c0c0b0a9134403028200c44500e2a8207034899400807800f40d4010b000c9070440c0080c00c07020100b07205080c0700310f560040c10000e10071003c42c1e04c04028028103034280e80f05204510703103e88100181380c4000040e4128401c0c0703020145001c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 938373102 1250 938371852 938371859
    0x1090c0e18010c21110a0f090504050a0b0a0b0a05031303020c030615043e04150e0103180c050906031e0105010807050102060108070605070f1202060a060f05060702060a09 75
    0x50840340910f00100010b2000d4600044403400c1039004002ea503058102442002e00d05c60394100c40f48101c0a0b108100003041145c00c00f4107205507800e00103070030018004d1100d4104000414050f10b0b8200106204440805000801c0040002100d806141c0c1d070f1196070440c6e480155620f03901c0121f10007901940112010b030207180e5802c1c84064031030703c002019410240c894805210846036501030a101c440c6003e401d000b103151259010f800b8088141c3d42101c1310840c00e1803005902d0180e1743c00a00707003214080c00c0c10342545e0130248a52090700203980030030000c00402e0103122003035061140600002e90340a000d0026080030010b42c0d9010314040c0485402103504800c64044401c0c0c0b581c1030300680d5461006220090051180034001e0109200030611541055282c41d1541c0f0b440c85254244440003441d00c08002e022402c5e001e641742c12550b1020f0000c07202202035150a000c0302c440c0c11240c6010404a1440000c00c0c00005682c0c0142080707082000703642c01e0102d0342d4480085072085c41401403001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 938374352 1250 938373102 938373151
    0x6010b0f04050303120108010c020f15341b020f0f0a12060e070602060705030f0405100501030311060c0f0a031d0f030d05090613150e03130305070801090c0e 69
    0x1450700505a0170b50707031070540c50b000a1508640d0005010411500511014134071500001007441a8691411039440c240e181d290b21500e1400e030341c14540880c125041e00e842d00464410b4a0a031000d4015202c2e00b02c1c08100c08a103d55840c00220700a40c0180e50025205050030030b4084408141d00180c801660380c1e4845460b40300543c52004203c0300d442c1c80352540034452000b442041c0040c100c3c0e000824a60801c5a00070300680402452902e014925100080500c41f0422510210074010710040000d96101d090090400d01708051901c100e1090300003241200d4151021a03120801d090400d9091031100a8102c0c0076080c0e0152420040c0701c038900760b5424610034005005400324280003183c0d03403070204462500b55030000b04040c0c0260001c104102d5415812081101d00680c4034122b4107105550034200c80041401448400c081d110109000c0c002c40015050203059070300806c1250481c0b43c1d02ca04071400d80f480e000c4000c0420800e120208501c40c440040103401070102e1400c0c0013440f441c0d6010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 938375602 1250 938374352 938374357
    0x90303030c12180515040812040503040902072a0806160203040503151b04050d03030203041a040b150406290d1103061c1a13050708160b04060206010b0f04050303 71
    0xd250390301000500300f010000d003040355144841c0c03003d81c580314501c0c154550b0311940c083c4142c0c07041c2030840440064208102803041360081d11744a10119110100e60514075102807001040e180380817229420780e4480071050703000e00120707418800100301700e40c0e8500503d203050710305240c00c0d02540b10501c00480d02ea07505012000c07507e102c8419420040c5081c483e07203002951200c401d5600407030100b20078040c90f25808105030302260103080150303407500e85141031840c000d4001e01200490300b980c41804108810103a140d40075100000084040f00c055034108821107409100e000c01107503180080104000d203446000900900c40038445042003408010403064800e0b41d401403510301c5000082203103d180a4800400c02402c0100d0340811018507512440d01c24215a0f148000c00780d03040000c0d031400101040301001550000039920580d0b80c0d4032034240e0340c12080301110102d41d20b64001144860b4050140d404644070b40e8020903171a480d00107110a25482000340c42c209140400007c207007130720b04100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 938376852 1250 938375602 938375621
    0xf2103030218060316080705030108250509040506060307060e0604150e030615010f030e060406150f030c1d060108010b090d08030f15010503100302121c0f03050708010501090303030c12 81
    0x4c0d04401001c0117001400316100904100502c8428401484440c0700010700801c04001e03d4100e801041c003c8145461a4089030300040e40030304400200020041d003c241140101e00540840704000d4592009031042484155801d8002100303200030401c0303011149010781c02e030201c1d00b020011551343c0404a424100100d481c40b07105070007002260147e5a2104240500040c0f07444c040040800f01c894450325024080c102418541d22104c01c4008200c983e40c44000420027030070340c1102d080c1c2c0d80c40d0580c3c41c50794922030005101618256980000a03442c541807103800c05030740350083c607824035010540e65003100c43c01c41c0e0800009045480010386800040d03011b5101540c080079940340c4010380f00450f56541c10024100b2400340248043c0c03e000d8155842178a0307045407420403416550403007500e012040352078040004402c007188a14503401c490a540400c00030351f02070045984161040c0c034501028402c441c0002e200c50340400c04030f88241c0c001e8020761200d152511000900024200990b4000d90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 938378102 1250 938376852 938376871
    0x406051c021f11060c040b0409021c02040603142508090a020306040f02131103160c0807030e130b09060603180a1b090b06030c070f1502040f21030302180603 69
    0x2002030000e070f0001c0140f10b80c8150794400d02031900d030818541101500440c807039400d02030b40101e44000310400d540600241e6841c1090300319207413542c0f00740050240c5540301c004541075400801003a66081002c0b4031222f1003142007807030308040c0d0001c181203e8248000740740300e55a0140508040c0141d4060001b02d00541c0078400c80a944035007401009807105c41d903000c901c035180c58640b001d9107116210044d00d038002c1115074914880d074904c0344159520b040e0b00c4401000b14034000348040030950800c684200a0310300782e8444139040d100e4090801141c0c071080a003a801104640080d4061905400455101700400c441ca52280d50a084180c6003401142d0101d6560075200c401402111504030b00d90024800c40c0400e00030801020f020402c40c2c400a0b02a0820b07510002d261014043d44006081640b0f82c80f10014a860800a0301c070002500180a4020801098003001941603150300404125000001c682ca403042d041c6d6905500961006070a59030b070207143e40076502c103980d894002d144140c0c45c0301c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 938379352 1250 938378102 938378117
    0x111e1006140f0d0b15181e090d320a0314102d15050c0c010e03151005060c031b070602070603020f040902031f050406051c021f 56
    0x18000c1100400d1551000d07802020180f50200128050350707942500403001c20b039200040700300440030524210b8903620b0700d01c4031145902031060750b841c40100c82c0c41d540d00080c0d14154a44551303a9054442c0c040401205c00180080858544000781004410a00500b0078851a44040c445054907540d0001103041022a0b83c540c1da040a00c0c40041010354000c0080e81e03940115410b00120011201c0f100286042508035909440d100a6022811002820664a2903000d05001d010000c0c500e9000c0d802e02c0e0598020050f1040103540601d06a2000080c0103002d04000414010345002d0031200620b40014021560000106621000003d100301c034088400740da41c4244150360702486801041c6200843d81c0320355000c2020343d6001c6020030503a0214600035958800b0109204610701440d0041482d4510000c00e00070342c8003068842c060200f900805000340c860b90751040200f1070741c0340e10585401030003040d80e0a003c0c084144001559620080c05840ba40c45011024801013000c00342c404003040c047c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 938380602 1250 938379352 938379389
    0x913050402040c05090303071428050c0409030504090903120e0d08060307050a03080307120507110f070b030115170f1b19030c111c030c111e1006 64
    0x60260902c034840d40d040541c54105d0100c0426606e00c40e1050141c40107020181d43d080300e45050010700b0500c0d0041d514143c2841054070340d518078000105080359a48a03200002c443c80c02c0a00070308440d26007640765181000d04d031442400281811982c200d040010f2040d480408803524428100f81000380c10040c03e00c21690700e03014041080245c401842a40200002c1045035243e01c0703000c040d02d6100340c4440e1640c480000955000844036400100c1d90308050800098581c001d0302c420382e81000a040b5054801408079440e11600540601e4a411904100609c04c099039406000c4000c14680780290140400350100756030b90206548610f41085000103000704486962008140780701e1500d003281c6804210b0707943c5441058045810400c0c15225a1054100750003829000b07203003000354007500c403c0101c0c0340f046590864044401c0020070328001c00c480760107100701800200701080030b00400d981903072002014003201c81c00016680394811403443e003414160700d004120040510708900600140d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 938381852 1250 938380602 938380609
    0x606020303060f040e0c04110412050c040506060306090f0603030c100213060206011d2701141803070204020d150b0a09060c15050403030b04020f030417031303140913050402 76
    0x11641d80e18072075402d1605e44280440c0208615203050011100001c114400840704503940c010b80e03001020260440134000103000f4049001c00d0608411101040107a81c1c090402000780030646540d030300711140300700080c1001e103003a9041d82c102074010100c034101440359851900e0007101d06506000e50740c000c40e00500030a40545d00101520700d5001a00702d56062507040804061030030980d561075483d07a004075402d07405240202c8410120a036070094200788084400340a440c640318800040103032200020200081c0c41c0c528000d054030300016500d01041602007201039000144042c0d00207aa0b550030b01c2402c124035244800404840c1880c5d602e605c20340c50040c01c0804140c0c841000e1010a1058600003504e040c0c02d00780c9110001c1c00000c0d02e440d076050031002014030710311498220740300040c09200151000065882603104907900b5030100c0301c0c41100c0082d400191900014420158808400030340030f05030501c0c0c48152000b095017814032010020f40e0030b2803443d07451980f00b41d444003031209506 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 938383102 1250 938381852 938381869
    0x1061403060a020c030a0e0f0909010c1e0c1415010e010303080a480302043002011d210d0c03120f020405210f011418030c01060602030306 61
    0x42040504504090f0181c21590712403042c04135220407c05e03c0342e07001c07135a0f40e00c24060f4006110060181030091600c03600b5140200066540c0b44086054102e550708034516440711600054400d81da0155190021b903a91307402c080400c0109002d500030918652003642091050307900904000e5408001c0d5491400c0c041c1c044480036101c0f983d41420480d03940b2400440c1c00314004851800c07100c1030300c8640080400b000420250036011040c01514002204c91941034010b0015104581c403040c003590000d000d803041ca40503030703020741d12407400c54a2182c02642c001c403a15200380c075066252a081003e107000181900c844031b600c10404e21248481c004601a080007402d03140451800e0030850400e441d10050007400e080102c201245032180070b844242c0c0d407140c050390000c1c80050172542500c80484107510b0403001c2c81001030a00e1044522002464005016100011080ea0b103400415240d030b03c58020702a420400300b62040c8010051203800c0002403049000400e45035000e10b80b00d0401c1d504012001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 938384352 1250 938383102 938383111
    0x1090f02010810080d1b06050a021306020f0705040e1011190314271c260a05040c0b03040c08010506010e010914010c050a0b01081216060509030c0106140306 69
    0x10f0000c003009014501c0b0000e440d49040b90f082c140002c1070b40110540541503c0da1000c01400b860400080c4050b45040b80c004c0d007010f64070224548100c5440f51400c0340d07248090190030b81e40d540078100c10021414a6801144c0203100700e03083e50012800c2840c0401074866461910845050000302011440301609008100451900e004d1040403180800040c501e40c0c003406400300700701c48452008580310b188100f40c01c4d100440080e60040c407000d82900c680000e42810010205203a41c80c9010070003003045a241c0b90884800000c0081d4940380074840040c41c0c01001180d02c120094008140c21102030051845144180c4800f1071103410107030b45500b5590080c0c4801c0c180170100a886084d03a03081210181950084e80e400440040c03030744012140380d44150b00c00391560044888100034800701010a82c1690411011907180703014401b1448010311503400c00c00c80e1942509501c20000307079660000381c0c03c000000704a0b41404059a101400c46045510030345000f0907204584070103003401d10071550320 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 938385602 1250 938384352 938384371
    0x302041a060a0e04150f180507050301030623040b04020312030114041a0a06050a02190f0f062a0e041104151106040303020408010f15050402160501090f020108 70
    0x300003030002040190080c00070307140034444408202015500c4592241d4040844071508885030341d62007401d08465030b49401101e000e036210ba60050000001405018041c3d6402c3c4e541c03514682c80c586035640100b900e00b4403d1600c0b6030107a01c0c1000140742d03a207041d002d00d0054059102c507003071034410580303130000c1c540600c003d403803051004100b00c124000102c032026000b40ea02050000740f1012403110810103400701903202058650200c0d034107901038043c007292400354007103801d0301412817003154941da81c002d40105003d40c6e2892810000b00041c000640030f922410b0041400c11178a40340210034246a00107a840c10882c007520020326610054007d200d24050f078082000c0d8250601d0610036100b203025002c2200e0b112042c410b21036110320b009c1c0c00c03012030f103900f5a1040e0406190080180d0b005100d503820303c4d82042c00b842c030610034501c40c0342c29801451411245051811040c00041d422410700f841a14902c0810a00807400030700500321040c2c82840e003d0300a490a1001400841001d4980c0c00b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 938386852 1250 938385602 938385641
    0x905060f030d1d04060b031f120f02060a050c0d0201020a0215060d0b13050f0a03030b030c0127120807060c26041112060103151a0609032104030204 65
    0x20003d8001000800c800d036820740c004201c40c80000030a0190031140c1c021140090000300301704418118160401c455080181c070b901f24030f03589403501d803880c104070500030f000601ca590aa40c0146802c02c0117209180150a00303078100484400e2850030091840c09050144c5d400050010130164140402c03580305111512207551410b1001c045040006030311700003071450004a0104843c1e1f648074012180c681da126044800c07074003140d1051a1142501602100803a0070700b48141114900810350034000d1206950305400e80544100c0c8450301110310a5414002151040110305d49882001480c0d0b400d00035403a01c0d82d12030307040ca801021180050303240010000002c41c03100348448104151520400200c0f0240510340b03132424001301600380d20a9003940140c2035007180381401400700d4840d040300d005001c0c0442c0720049200341410340d21542d255055801c0000c0c03007001203160600c00f41503800c00140454041c0d00031010020916088940b03188218074010408004504d054029a03d010007044003820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 938388102 1250 938386852 938386873
    0x12020d230f040305030304030e03150105030a1520030f0a0902011e1206080f0f030f1b031605100528051806070903050c10090314160905060f03 63
    0x203024051881080140d1200024070103201a03000050b5006140c00800b581e076070b820b0a280140c20801401c1c4c07101c1c000e010b100940800506496040380c101c0740060098150380e101a83c40c660421032030131260300344c07590b06d002c5031100e0500c1c81d042500c0001e4065146070350303060010003588491402440100028181aa00780060b40d000b880c40c230b2415070b40d9408001c0f441012000f910200341c0818032030482442c1c000001690700d800914a0401c0e4000c0c8192040d100316500c42030703102d104030740c640300d621001007001d03c0700406064012581218901c003640c0c10b10030b2102134800307407a03901c40c1b050b503199000f10b00360700e0074000d903110b451b030002ca0000c0c5565416100340f40312140c2c042c0480034103040c1c503075401c0041d0f03a14100e5140e84d0f4001c284002590713000d1418000181001400307000542d1540b0641444101c9410505030044604026848001e411440c40d520701d00d400700c0158440506029940000140703100030318484c40a08801c2001098514145041c03141d200486c0f032002d40700f9404100501d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 938389352 1250 938388102 938388137
    0x5060102250b07030c030807171b0d05130308090706020d030e0307020a03030801091d06180a12090510020313061d0604151403070206010b0a0c05010912020d 69
    0x1504032800011000140c0d01103140a00c601d84941e80322041015001641c1000c0540c40011010814400d441b0000381e600d80300c01c100c030540c42c040c05d20314402100707801080851001022690000c08140d111601c1e185456120b40d050300c1c415145281e002002a816408041d002510a5030020701d1400500d0910310708200251b5892410100c0028180d4828034860520028401ca0ba00c1540241800c1d083c2560384c07400800030802407180800c02407401d1218810010b606000b0001c400c1a14001c04141c1c0300e0407000d01e1a048421102941c91003102102d00000300d002100c0100030006031100062207191405000d8801c500403900811500100016034000f0303400e0800c942543c625141842c8082962080000d840200303411441c1d20030070201c3e0004201704803100903500720b030351507030742030300210041034102a5800152800400758011500502224103098040c2011158900c2c14641c00d464a44503142126290f02050707440d19031401e4110b200b40e80400c8030703c6004c1503500d8410b00d100c1881419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 938390602 1250 938389352 938389363
    0x60d11072006120f100e07110f0307031d030312010306020702100309122015240a0e060d120e19050f1201060305010c02070f0906060f1b050106230405060102 69
    0x48100c20502c490214440c0170105146001070050010440407074144600080c01c42a40341f40c00004a2061400c981d44108021042e10b102e02e0340741d00e40c0f40d607c00b1015083c9481c003c4072070785941c040c80709001a4001c00c00d600101d90080d4001c207001a0780d130717000d0f0052150b448145c41c2404117250401031103c0009440200007011100c0519200310003003410182c002e10396204401ea0704041c4a10302170728000c40031140050380100f900700017040000c00c20101003c0d0505c429a40305500500d40036042004c034401c00b000b264400c1c4003c02031150700b1229a103802201d000081d401c00043e0f8a4110303160340307013000c03019034680320b0208820100c82460480050b240f5400203d5160156111803080c010555094010402940e88180244412444a03d00941e1240e0a00c100188480d191600154502052146100341d424036a90000c0700000c020090b01c00d2001c00f401c141082202c0f0038680f02160084c03060038040d02c25144160080d03083e841d11214140815100da40c401d9150109101244c2c0e000904c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 938391852 1250 938390602 938390611
    0x171b070f0f090c0306030b070201020a1b05030a121107030c050606010e0f060703020c1f080a09030e040209061c1524260906011a0c0705060d1107200612 67
    0x2400f14240441941c114003401c00303540010320398901001880010394064000e04607085250741c4130700341c3c6004114020030802c0102009041d6420400c00980350a02c11044018004400c0c100880c6c440800d04021260790310114007907000480d000d150004002040c440250498030900c0c001c414003400e40d000070190f0710310060440c8180380001d0340004140c000d00500c85003100040c03411406003000000e0090701c074401106000056520070009203001d80505c101c066141c1c041da106c5110b02d1020060200960118500315440340c01031050b211054000018000300c88965680401c600e020349004400c04403560300170341c0030310002e80c0c0660300e070500c079095211501c01c6034600b851900e0004081e4000000c500f03400803004400301c208000e00400000346076070484821011607400d2000c619110500b034003031107001e000b00390080d60080216161041c06461810300507940011043c0c0084203448840c1d11420080f40c03501740841298013420f0351214040e201c002d040e28454075109000311025400d500092 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 938393102 1250 938391852 938391869
    0x51f15050910090c0c020901090212091507030504021c0507080d0504030f0b070504080304090912030c0c12120e0604121b030c06060308030108011b111207171b070f0f 73
    0x44e90001d040c81103403101201c03500903000001c0340d41c42d003203004007942c80b02c080540c1852900c0e000c1040c204000450518046c0c80d445c805003140c954060480250601810903607215000380e1800c141c0e800741840c6140f2191180c4010030503d49003801c0d550400c0c40c40581c09051010601007040030480320078040d8100307a8080c407481e01c540d0701c0880948180c0101c9d001007071030307110100e000f0442c400340d43d00410615014528594114459110441c251003501a0351000107100d00d5a14000841c3d840c000407500f4820300709808011013640350501101c0701144800c0742c0c0e034031040500092081012999410100c9440c0c000d40041c0e10025210344030a4121004042081d003990402c14403003150b002d60080c5901801030b954a5135030307044850280c00144a10a03800d4180c200242001e40070700f00920801d80e100002c1c0054800891260b89a03400c03181059030f60002401e5004206009100105401c0900c1c240b20b45440031100340e804d00e02444d5412405040503001070138400e5030902ea181004490160 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 938394352 1250 938393102 938393111
    0x630061f0b0903030f0c030715020f0f0a0e1216080607170a02040504181a011401110c09100602160f0513021606020d0b030114070c051f1505091009 65
    0x424a944940d0524034817070300300400c90f400701001c044000d2414a000b243e0708400408650203003012440b480043c02d00c241d804001c501c0030901500064180c00607503080040e248104140416080740c1115000d400d250403041c0701108800400e008907002c1e0075184018000762900c500c001d4100c3c41d221200d911071603564000103c05a000d0707011a00546406031040c03295491101c072101c0100004003084680f00445408822002d0b450344d4418121901e940d031a281c00f05c0031400555a004004401b00d0450050b502c4101c2c040c0c9071030717820500821224032100c2c603180c035200000b824816072040c07031120030540490422441407450702e02420303141c044880b0013144e003d11507800b00901c51031511503229100f444a2138284031541d806007041030001d0074140a8804070000b050308850b44101460880044038004c03c21032403140180c110114810380c03c43d10110314024184001d0901a40c920402c1511940020561118415440d000b4102560006040d050152200b80000920b000702c00381541da4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 938395602 1250 938394352 938394367
    0x40209040f05030406120b0303070c030209060105040b2a030a08010b0a0c05150403020c06040b071b0e040501050a061406072006130e1303170630061f0b 67
    0x1001c014088203900c802269074450b600d21024000d8000b5404103010350b4941040c174481d509000c001c64074042d520030071803042e842c01c5500b0410341d5000544101e04102c818003000c6198101c2000030002c4211005c1c0140034100f1107915040301403200e40c444041a0010301c00342100700c3d008010941583e829002103500c422810900b110b048c1c440c500c001d421440f072044800015030008140c140564040d909542d001c40c100424440c151045125658061a040000c135020a0440c4000d84034940c01c10611300010740e0300c0c06d58542d440c5c03055a054030386075980c4044c0600030b0501d10611b802080f8000e00e01c00c60b1944080016414050010082c0c10130001501445420810160b04d10400b90001c000540300c43c03034801d40c0d190356071082c01018203410031034001c01c11000040140404403a80350350b521900d00b08d45106100d48810183c1031503085085598409400790a40f4000646036060341020040c5100d80600140352030005401000c1c107415111042e08402c1010817120166130480caa283da50b00b10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 938396852 1250 938395602 938395613
    0x70e0a06020106081b1f1209140f060702070e040213060f1409040f152d050a020405030a170d020307110606010f05090103090201182904060e091504051518040b04020904 74
    0x8124a101502346080116020000d6000ca8414041007501c00c0342c810144214100703a50714000c0ea00d21025030f004540401a098085410311b0b03119101411054010542d4140b5809554058005200c4400780c0c0605004042c00a0031000d924842100c600c0c0803400c094540d5085200c0450f0041d00c650107032492540c101616800c6280f2024084001e404c01000d01c00c08003c400001c488400d100c9428100031440e03009250003580c0503280014060102014243d8896040c2603071300c0c01800c81c0d07641c284805112140c5a1001e50700c112100e48401e080001e4280145082000040c1241c3c18080d007003062042141d880002d951620b03400307003000180380e030300c0380016526080c51880000d08000c82d507401145500e070510b40151801c0418204444030550a0a40f0003140a14012203000908805a1044500c2d116100c1a0402d00b211800b00c032210342c03000820140d0f1300c2201c096800d079121800c040c07007500300045800116600130f91070002e18180b540c1c9a003694000544040c3c443c00c8030101037424001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 938398102 1250 938396852 938396867
    0xa060309021f03021b01060e0c070213050a0b0109170a2303030a0c0306120b071202161b0f032109170703201305070e0a06020106081b1f 60
    0x84880c882c902c400036120002800b030360000440c03500602e101404091490014020882510010b1021130130355941e046c0340c510141c0240c8000e981c82210900a4100304003a445050300900ca80305c004036101c00840009465071041e9400001003000204921025200c0400e01d40003265015176039a048007074a007900200400106400040c3d40170000070300000b440303140d1090790110003580307091007055601e1408001500c0c2c40440541100d02c3c010001c0c0010784154101000038105640040c14503901c1503405040d198410001c40307019192050121550101d6a40302c0010400a1144023415045a6440c003c04804400c8800001c040703a44030710310317180a400050080c0203580d5001540c00d01034214190b84e11268441903408100612200b0b4003180e04104040c1404005800001621051070b1440f000741401881a01041607802882d403055888555400003800d8640c00450102e041195043c00e000340e2580009050107480304104442c0c490340014070780044030541c0e60508510804081e501c10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 938399352 1250 938398102 938398129
    0x150307021606093614100b040e070c1b060e030f0c0a1e0306022a03030609070c050f12040e0a02030928020402071514150409410c0a06030902 62
    0xe80c00c004903001e4418940c0c060b18070458040703142c0020650380b2600e2121234815801401d41800c40038001400d8207004620680c04144100020940f00951104680c3c40c1d0f401d40d0003403c0000c0f1502c146000034601041105512640e0002401001000e440001c0704a041e521402500c0c0b13060b611410658074080d0300901c01550040420740d954809942014040d07424a044941c02c210390b07401c01c0003e5a000000d5910812014042444580b245042500c02d40b01d1600115928800d40d158042d40c200700f4812604801c00b5060810b850386c0c24038100403c2810018030700c0c0c0440e4410f00c00c0284000c4002404601020074110081e081c0c0c4894490f455030840700c650194000d400010031904003d410f03c185600c01003001c2080090341c2c0300c92081805010b082e44c80480304203081d15100303414070702a40102178952240e49000c5a0f818002c66043d0b020b40500320903200f910521401012603c1d6612080918680d54005424545103541c00568016510b00903041095030b08c400c1c0e2011174a402000b4260b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 938400602 1250 938399352 938399459
    0xb1e06130f0608280c050108180a050d12181b32030d080402040f1d0a1110020d050a11012409090f1115030702160609 52
    0xb5201d02c0b44503a40c02c0988010035041c1c80241c04480c500c0759041e4071002e62179202c401c07508507602d80b600444803050043e000c4805a842c02c1190301d07240004010205025205502a00d11075030841c0c40075007501c2a01c8030040d291820b01c440c07444181046005110456032108403c00f0010301448958800ea01c96000300c0716108600e83d8a081301d04000104107803004540794120030103080013040c582c48001c2c40c1000c101044400e80468018071b841d8001540a04104000041d082c00c269480e42c07014217005110003c40e01312101410a00044500c4c4000b100c00c1039414194900300004000d54a6526148940c1040000705990280a100381e03260922080404003d00c126138800c0e5001c10030711844001c4440881c6018000200d440080c0110407140703030040e00810003211240c4500380b0009003101900e03444106116011050023a0a024600403840742d130080c05201c2d103096211028486c2a0480f00a00a210b40700b01301509507911202c0243d0000d10102200d00300c0c860f006203044d08240c0500d0031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 938401852 1250 938400602 938400611
    0x509040c05040503060f0f0a020406050315030c0d03030b090903030c12061503010b2107020d0302030c07140a061107080403030c020d050d0e03010b0d050d0f090f0906030b1e06130f 79
    0x4010558801c0780d4081c0c61f00d025522225103615400d40d0407485075100303020118105000007004400a0040e42c03414010240c1614845005680090311407001c48804801090342d4800400060401c003112030780c4a00c0c3c4034001c0d071560a08820035003540c02038024008040030910001603603500c4a040700803001c01544074060700e95031280c880103071079000f00041c0b100714141c2409604d2164064411640a5502c0fa0003400c403410840c102200658001800007402040401140300012000148400078020071000703054810514600101aa001c1c102c4c034200c8400284090400318030030908540803a0f40c1414000b80e06102032000c10f000401c1c18901a00364081c0031100c44a4075009001004050800c40c020801515850200f018541400d50090000d62240c480e0803001e6000f1000b20707051000c11305200c5101c41d69446840c00d41006a04614a02d548481042080018003542c0076001070740400300c0c0481180400140e91113150043c0f04612590800d4404030107050b07503038020146458174810500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 938403102 1250 938401852 938401861
    0xb030c0c120306040b010305043c0809010909020a0e0f0102010b0306040b07020d020f0304140d060216150203040210030507030902120705011b081614010f1a060a0509040c0504050306 80
    0x405410440b803d901450a10502550a61080c0b280707510580e400310449003c2e66603030301c040400d10310400640e68001c42401e82d504a200280c42801e6082e4070404229568900d44d000041000d1050b90141085900521a1002207038200c44070b03101c601410386003440d6495030800101d015040b27494203150140600420b0206012801d06124410b144a408440789118641022a900d42c00302994170419042404140029043c085d00d0400100005210340c4889171300da2151001c0fa8001c0c041240c1942c10801904100f00000d0080503199610703103011411032506402042146003081d880000301a6501d0002d074206d4043c0e40074080042d0041c1a02090b8911100b2059880607a8084c070f80c0441c00d48803142d030b2401d04440a03280c0c0240c0c0724a5890034a18103644801245150700d2084810a1052400d030101c0c0c00e0034400d1040300c0303020841c00715480390219668049014005102401004100100d40c0c0c1550800c04079410600305a40001c0d00d00103c0308100c41a001d0345c1c0050390b140c000c1c00e0a00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 938404352 1250 938403102 938403133
    0x20d0605060a0e0301150e040809030c0603010609030b01210201032013030203150717090a120f030506010306060c03121808070b06030114040b0709171b040608070b030c0c 75
    0x12094101070b8000c11444c1800c46c01a82460050f200e107a00c0c1084684c001400a60f0300000b400340440b024046940d41040400082c1c000d8100740c1110000445441c4c042091001000781c090050120303000350325520404039100d000707850300882d019060680782c030700780324251000e42c056140a41d81c800b02d55488041c1d008001d81c071040540300c10381c400d12412102042c8071070882035081c01035125848605000004c00c00c20804014020284240f9000b90007152011035041d1070301c00444561685c0719412440e022304050221a0060511810145400c00a005c156081140c140301d9941604050046603580750f580b5001d403a1800c0e20800c620361108082042240e404054920a0311405138040039540c3c5400b410f0803258070000c0301e08987e84510108001c60b01301c0e118190011902e25020054545501240d40511a507074941c000c654800316610702000c401203488041444126400d008035480c020509130755942d1402001c1400301c0000218040c0d4080d07074100e64898208406031140d845500048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 938405602 1250 938404352 938404367
    0x15030f0703060e07051c03030207320606031f0b030f03070b070e0604030b0a020d0501080d2006150a0e070c02090f040b0720120714120d020d0605060a 66
    0x3281c000d8207181810050200204415058880240c1600c5485554005046c1d9059040170140c080c0340e800c000440c0803801050170440c0d008441c1c03030303104070155a440001802800040e244000e5070800400e20030983e401090790640706421072030500c240b02d0f5141c10480104200700d40d0704e50510900c540007025040c0032002d442001d0080210500d00d03034130110107550b850b0b62580b207107901034000c2000b032002440c0c3c1c00003690080d9008034010b09002440343d41c80100e030007c0e0440b81440d4403095030403c0c038a500180c50781c1d01c0e044800c030020b40c80c174805400070b07501c04c03000d840c0103206280d0301c5210406440e0303980d40c04018a0146180101c900302400081e0805074521301c1640501c1a880000d45048030358a55503001d00c0e4030003220a8240d80b2040e04544d240c14101050b0501804001304403483d4004100f000b41440c8a080004d80e528403c4c0391100c002e6005e01600c81c0700d6004031000180307045215050b02c000b2401c00101594502d2101c030341a00130102508510303801400030501c1f20300c05501501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 938406852 1250 938405602 938405609
    0x6021515010216081b030a0c06030908040504020d0605031e070923010603060503071401020d120e01091109090c1e180f07030606031517010204090606080f060a06050d0515030f07 78
    0x400e02c1340505e44000345500e81407040d10140003101c1c3d0300c00030001c092083e804151024098403c05017040d03100c2c00001c060382e00580b64020074940b03c0c0320901051800380000b01759080406482510407a00200031a11541c503846030035032450703644e91624003c1c90311102c44020002e150b09145c0e01507864410103001465140a528043d2185071408030719480c0000d080180e480b0142c0052211005507602100c12007441100300c0700841d114915601c118034240641d0b15020300c1111054a0020240280200303024002d00050f550352180c9464bc1160303d402da21104135941d49488ac1c032030100420041242c664410501380e034102900000c0007a095619540c0c9801150203541c140700e03081c0d451000b18152011004484d041c4030505200304100c1c0a58002540c083c0e00c03c000140c1001d81e51111101181c13181d90044010031184001c00403510b01010a80b6070000049031168003035400e2980042c018040c1450480ca499a9000824400c00a480059210310700007012101c0d660360a940540e1100240d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 938408102 1250 938406852 938406883
    0x305150906150d142a27070c11061b0c0409030e10020a0c0605070228030b04110a0b09010315050d0609151a0a0602151501021608 57
    0x80c003003018410908841e410054000f8045004405503403100a100a50940f0f501d0031440b81a188201d41d9022481000d81c2c5060000c10039110031881082c4461250b001d8040c8109400c40311000300009406c1e82510b810103c00d10300540301c400706241c0301e01000e4009101030380c40b17140498a0b21158240c0c1802d00150751210064601c5400d565040c0401e40b400c1c0388004000c10314004840485040405081c5111103880c4116500900e040d102c1c0071801304603401800020f5800900101982861131011fa0390b001e80d845c0042d40205d807103040c01c000e60505d010040560600301301180500000c846502442c807002000130502e00c0e41c071610055990300c10140140030900b00b04504245038081403400302107580103031982d44014074503600c0700001c191054080b2006490540c59001e207600300e100d4000c841a0401121141020403002c10203890380c294440d1045600401035900049004031619400007111081300c1105070390140183d0902d020004c00524004804400095455000400c042c900d004e85 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 938409352 1250 938408102 938408113
    0x1306110703120c020d14160525030c0b07030c150507020c030a0201080609090703080d05270a0212071703070b010501300605060d0c0e03061003080705030403051509 72
    0x1811801940d40c2c880654000d03070402207215171000c0c00760703140c42c0d0400c5000a41e245042d221400410454201d51402e44040d44a40c41001045015200403840c40718203031010203400b8a1542d0780b0020700454002e04044000c086aa101014000c2032021440d0f0b0b400181030f1407410107607942c0780c0113000c101e032030b00300600c100300115101d0f0401107280e20032503806030348500c940d90760181408904003006d000a1418854001300001092100010b085009440a0081240c1c20802210401c44070803a07000c040200c3c0d95419002d0044001402c0c0c03820f103906039103000324101a80b40150910b08075602c0040d0000c10841c41100381c007408001401c56500c12103481c05281d80303600045401070707134a8810344603a1070b0f0710b1b0312211040a180c0700011365038001540441d0403529003001c5460303a081000c100300d15944402685003140d42003012816040300c25001031a062800c0153340820010503c07000d45181c10004000d42840420f01c2150b0145410000f03c503810f0380003103088003a1314000c032200042030242 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 938410602 1250 938409352 938409377
    0x1f06170d200a0204051f080601082104050f030a0203060118110f03010501050c07091d06071404060c05121b06070905030303041e0b07020102130e0402181306110703 72
    0x850740701c1072800d24030000a1601c01410b6003800014400a000e0043c0714814410070589003070280f000c0d0018180c132002410941d498404d1071450102d000ca01c0c150080702e0507020700003001043c82074404940e02103418010010201c404281030480c0701001a42501480d4004604a9050b00e80741484204d600001c20000840941804e1140182003003040c00c04002c00c0100700f25849180a40825622281650300290751028240304607045032100c5850881e0810800e61280303007d00441e584154030742440034040e810171907224024895030041c0402d01040d0755040040c03242c100701c100c4d600300b00c3e001c0c0c03d9540d540440240301c801024442104c207a10800000400c003034030a09110701190006001107042d40c83c2c1e030380c5140c008600030a581c0f040707034007145801020684191199000300d1498000580d2889461000500281c1c3c42d04030055941100041c0801038681c000f00144d0128000c181e030220ba260700d0f14924401c039907198058422810721101029001481d0300038181a486600c445101294 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 938411852 1250 938410602 938410637
    0x6090f0f1209013b01080a02160311100204180b060c070302040b220e070f0302011202030405012c01050106080403120c022a041107051f06170d 63
    0x21034a4540a16075050152500c00c0d401019020084180365000100d14040031400c0b400b01400f200c40c451010022070140e61540d42c1110a0682091810074290f142c285a0aa20b2112101c5c2140050811000724a0318503501d400740800c0c0109140d01c0b0096683d25552418903400c0040800038102c05458103403421882d02c0c0201c211903c0411810141c0b880520719000c200080c0790300d80e803858024086070b030b9010709220b240052000e540400c040000c0c000d41c411070850b01d400100d400c141400445030f0010320250381c10080070f00070410041c1d005662a91070345400790260a030509003054508481c000041440d0b02c000707c0c402d440362880020409a039860300111130207141500c025000c58240c1503404400411500080341c01c155030700440302c1a000062150000d040c1c600d8a608a50074800e07100c845501e443d00501c1c100740d001c00c0429041c00070a40380c19480d504d22400100d907008580003140c184000341d41200d80202018045410208884000d054807503a1144403c00080e000c030280c04402c59 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 938413102 1250 938411852 938411863
    0x821040210081e0a0204030c080307150c0c11060403020d080d0e01060608150f09010f030c0803190f02010e030a110c1909020f16052a0319030c0506090f0f 68
    0x4020f401c0c1040e0321034091650701c02002000d041650790540170800400443c0402651000801c0604000e664409182c1004902c0e4100c03e821080ca09044c82080c5456a50180c8135444460f00b00019400030b0080c1d100060301441680d00094105150b2203042c400d001c10300000d00150f5440c16802e20904035030f109401e080f074141e40110004140040f000c03402c0713121100c9c01c040c4c418101400030201a6220301c0082c6c0f111314245d1240c0c40c40c1c100701d01c041c8100818240010003d16104004500742840d0000d51203030068115030f030104005402c0e100e80d1420313100b5002251514a9401076079510007040310011b00c030201e8460316400610642080741814100045030704034030803140703000007081400c00c81400c01a502506038040114420300100031034074910405082542e02c203c00a00c070315011505454402000002420030780b2800c206183c0c1d5688002ca00614180d5012030790140700401480c06462080b402000600a486003000b000307443e04000804480001240341120001004280070760307a150b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 938414352 1250 938413102 938413111
    0x90105010503060c2115032a010e06070f11100f0e10020f03040f0510050708030f060d05030a090509010803090102150a0e0307050d0e2704082104021008 67
    0x540c801e00c0004d011000810141c5082d134198040e20703806041154500c4003806003583c080e10141c00c00044007145280800013541c041e80d0b1072094030041d4045c0490001d064000c9204030b8140040f8401e0754901e80d42e18401c40d0030496100550b003150700000d060024042841c400c840e40200c180d0b07a41c0c0d0695501500c07410200300b81c00d940b460303200d00d00c1c3e00620103482141300d000070951140641c03c21860f40240f02a0010f01a8850340040a901d424100407000b002401142c09010081040c0c10206580300200da600c010218074030450364451901044010640e194003601502000c145034080b254021940d0040365022034025403e41d0700c4640036a1a0702c40c2c050f0090269102c0016407056520503003200e60b0040e15590002032500d04407509900b5607000b440111a1074108903481c01240d90031011014040c44155005010358123081c4103100c0072860405101d080c21254030005081001d0720048450481e0041403190f10114110702c8070640a009a804074405d016400502400134861044d55104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 938415602 1250 938414352 938414359
    0x9030606050603190c03020c1e240103061e06031103060c03090a0f05010b1005030718050a12050a06020426010b0109031403190e0f0d110103020a0507060c030c080901050105 76
    0x80002081e200001040e0005d41c02081c1a000c1c08160241d10b014400c8145202560780ca0480000000743d0f4035007890341103c3d84c4040008440d02ca1840e1030b01e801c00142c1920391001000aa007042e05a010b4034007801c91200c4131810b81412008020855580414403030035506404452440e191403040b408240000c54440ca0182c0c00901c68002041007054041d007014040d5000040c80c130301007404982921000c00c666008154000103015240382c1c018007140c040018418010001c50030f01d00005d040c514984288503d050341100f6a0052100038042c10203078942c41481190f4540d0b8070085070b000e85510b0200c240300790600c0340302c01606c503d040c041c0e5003e8100583d80c1c220301a045503600704002844035031342200741c442030004016180340500d00c9004c00d40070741c903403807000d4164004003e101c5825044403030040c0300c807a0520002541244100c03040032424200035880b190404d404880601941030301800d06410409240e0405415610005882100341c0e111b104951f1101000c0e030130394800b0704c5010780 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 938416852 1250 938415602 938415631
    0x60b040506010509060706060f06021e1209010c14010507110705031f0e0718050103020906010f0c030f121104140a0e011a0f031008102306011e09030606050603 70
    0x3901c3d04200420843c1d2261f000002c0703050311005c083c0c0880105401990141c0d005d4400b0b03108aa11680160402c501c03101c0040128001040701d134141409180005414001c1c6510804100b080030203004241d000d450000300102d1278001c1c0700504c0c006000e62060010300070202c000c45c5c01d05020034001c01d4031200002840c564113403c0b54881c020145030100c91002d002d0b030f080c00300700e2800104c4042805054200040b85950640c0108280810007400460611042019100e13826400c1081e54803010b405041c1034080d0081044c0548a82052500080601d841c0c20301c0e149840004d1409003050340ca500e01a00400b00d0645e0610a00c042103020704500307004030000400501a4585207401b0107480e1410490a10b2035100000b49590011340d007105c5841080d010600a030b0f102045001d10001d55944240151a0303000f03514261068a40a0380c0c94180940c2c0010b00c0c0c99000700c183c02040d6086a42d400140c82c0035003001400c0246a00049805034144940021a403a20300c00303582c0104542d4171a02c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 938418102 1250 938416852 938416867
    0xf050c09070f0e062206050d1a0907030f110403050102070b06040603020d110a321c0f11060c1b010e0906040c170a02090103050f090d05071a070309060b0405060105 72
    0x1c841d0b004460200316401c858200e4480490b80c80400500620381520b6464950b00301404050980d0701c00c2101030349c6082e40a421b4401039460040c49a0000c0560030f0019070701017a80340c108054011518001112440002d0001c01c0040541c000c0a07280d00070505664942ca0321401c0105403070b21072101960144882582c20080381c038480102d13040e1400181402da25581d60400b000f5000460419081c002c400700c03004c8203299050307041e01c01c0e46150031142e01e071004810017020505590f0000003d410051050b26550400c046054083e21803400101050340f50341c42803d44540d00d0300d600c0100c6005190400e110f100f02e5008140118075031070018500503541c3d0720b90b410711000703202002c0c52800f0040304070310045110343e059044501601d4003d0026984110410014040e5500600902d00f009110070421508180c00700b11140040c02078904269154117070f00b007915030032454011000d00c0c1548103040c004641d8040e44900900380c882e070400c0c08452580000c000840c1ca045038202d020070800c0000c803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 938419352 1250 938418102 938418109
    0x50703021002032b05090c090109020706060b030f0402210a0b062403011a070804050402092b0308131203110705150601171902070804030f050c09070f0e 67
    0x26082010710443e070800c545442606040800d1068030902c0788200c002c0c60b0306540e12030203415841007038a0001e06100814030f0100d41000c2c41413103107241c21580030480008021032900300000502d03061488035101d00f40f007414a014071805580c00c03071182c3c92581d110400890318031002140c1402c030001400f000c24080d113a8102200c4010a5650303c002c0e0b200c6000b45418018138400b58155190150684943c144203113a04d85051617002405003039014081c0c00001040b110840c0c0658505940250300c0d0b0200c50302013401e40c894810f008040261403150741c0085a503507130018079918029524100280c503030300c0c501003010102d117002402075146400c240c81028069000001e0741d014031090189000302e1900c1d014149140e100c4414041c08916040c8a255030f401b20168201c50301d17611074a03845040c40a00001c10a58480d0709641480c1c01003100400e104145042c0d07801136401080d0070f1003032000b074984180ca4514070010140304141400200d0107081c070407141c4240682030b903203a003403a001c0502e081 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 938420602 1250 938419352 938419369
    0xc0c0b0f13020904060515060705100c0c0c090e0c06120a05180304031401061a12060a0509190e012705070321031109010e1c0605090a15050405070302 66
    0x3200c02900c030034070510060f00c41d12420ba2259000d00320000c0e40f418241c0c6502d01004000140610410080c07280e0800301c2e03004241c80603517201c4090002100c091780c40b020b5807000c00030710015010240581c03001500c02e2464010403c8041c2080c1510b00c43c090000403c9081e008205a0a40540464000400200941c0d0010b41c00c05480d01e0200086240320350380c81d1950340181c0084405810101168468800900410018010028084070102c0102604020300d00403400c12180c62081100410070070307200c01590038040d10000c1c0c02c0507040d2401d00300844000e4110090902614a0546900300c24181840740c020981c8990f86030120110030852038a00440c4204401d0710342d80260364001001410220040103200140640c1d5801d6200c8000003504541c0d0b001103d1502c0c42c01040004132a80c1c1c00080da409904c02220002c0300d01c1e07068000a0403490560f80e00400c0140341000f80150b90200241c0803002a1090f850340d000101c4804110b030a481d803d13207000f8120340c00802c0610040c600307800b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 938421852 1250 938420602 938420611
    0x608040b091e010b0916081f08010908090f09010807061103090604091d07060e1c0f03020c120111030402090705192105070c02120102090a090f0c0c0b0f 67
    0x102c490035542814408200900307091410742c603a542d142e85110a082c42c1c008168400c26420032400c0e004a80034001e400900c0042020300074602c15402c007504061700007004409025001c008210305000c03032030401c2c8a40d206041251050300440e01802085c500034013118142c03034004000d00005858240c0541c0c4008025031410540c0c08107000007900d03501c9580261004115a080c04150b01c10381003030781101403000030140c50031900511070138460260086c4c1440900f1030162504031400541e0030315502003100c1c840340140b00d103c100d40000300b4140c1c00911804890301c100d0700e00308002e107502c038104d0884469038000305810380c040c400680036103848a20182d0244446c20017600e031481d040910110541510301480c00300d42c0b07154100c09041030840c4043c0c0d4070031080300104540d0034494030260001f414000028819030300e0154400710740d002901544c1c00c065002d001100c81d19121541c10303000d0507500030200c2803180303040b0306614142c0c45003040715402038000255074126240c00c9851081e099000b030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 938423102 1250 938421852 938421871
    0x30e010506010917100515010e010c0c03030c0c05190503071d01030615080304090509060705120f04020103060b040605041e0b0a080405070f0e0901151404020715061811040608040b 79
    0x801707001c240070500910b489224a030814402d41c6141000161503011f048045030704004840c65a80c0020f4045c01d030010641c0c1d010f043c00017200c403052408914504c0250000c0e0780ac42ca2039210614000c038140200c1080e0342e821030569030300c1d94684840c1c00701c0345030020041c42d2445503240104086015940201d603280c2c1c164460349081902c5850700e51541d4130540c0608030142d961802c0022038042400f400c1d4201c826031074681d2400b00d281045100c0c0c04e034054402581940c2c0c02020404680c0039601a2000b400c10101103a2125991440505540c2161003024a958518180c00011240f0241504142c0f10000502e82c28044006402c0b201000b000300304540c1d51003140004640301c1c0310070011400518100314080000e18000d01160b0944d1600500118110502d0400784124025090b0002e012102a1401603d614545c1040c075411102000700e025030502c3d20382c1c0032945490780804008685141701e01800001304040c603100c806c0c4554070981d00010cc2080100b00043c2405014681190425 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 938424352 1250 938423102 938423113
    0x6220203060d12020d0f170705030a150816050604030b1914241008060d030306050d0f050715200f15150f09041202120c030307030e010506010917 64
    0xc0c0d482c00c2c8039803c400b000d400503074402c004c000d001030742c030407003840117900149801c03609003824802c40340880384c000e071040f800e016001c400514083c1e0644d01042d501d1010f0a0381040c210707601d89402e52204032262a04188a01072400450103040c684201c40c00c4079404103902c03851b95910264000003c5c514010007401644502c240f00c10240341c44c81c094001c00e5000c510420600c0c007605039031260a084a403444c098141300130b01c01104d1380c020344141c1d030203d42030f1400240e042c031614084005001a07007080d030307005c0b0343c01c080c000502c007000d80892000d511400403503000585904031070726619007400e41c41c00056441008080002d41510141e000950904210b03001040402c040c036091003007404000d0285807070f10b81002491711602c07a2002d180c0e0300584a51901c0c51107a0042005902c00400c0500301c5030341940a40781c114800c012800100e00000c1a461319070700c84815882d00d95105580c4100041d0421007400c0c00384506106603030040ea016101c100c0100e02d000302ea50501d0703078141c040c40214085c6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 938425602 1250 938424352 938424379
    0x150a1e02030703020d0b04090c14010e0a0f090e211303051b010e0406140f0609090106030507030614030607120f02040611071a03040f0c12030302030f0622020306 71
    0x94009035000300700c2a140540c64001d4176610000f100c0e40000e00c01c0c4070703030304001c20307040412081c00460b4241c0340b90030320b1504080030150040c0c0d1000d05000d00d541d0050b8000c6000206030151010f144142da040329014000b40101d1a4a640d031000e03010103950712001c03a1860842c1c85000d810007065841500303426024011340c0c0f40c407081d04246805400c0c006c5000340300c15141c1c01d581d0106c0600550282268104030745824011240702d0401c2564406002d1a610180d0361110303130b15402034540410005204000542e10f580c401009440c042c0e800f040844d04007072022079103c003961900114014094010802c0b9902d0802c200c032940c0d01804084090b030360b54a0b04122114050000388090800c0340c491420042c11400500d152202a40c06150642010504564280909000c40f600143c110b1139080e000031144c10700340c4000e1210351026031007a0742001c03840d08051705a005984126904120b401c1d5940d43d50007172001003400090944041d41800503000201c2d14a5070245401c6600a058505080311 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 938426852 1250 938425602 938425661
    0xa061b060f05070909151a0f070305071502030f070507021305011511030f04150e03060f010503011802090c070f020907200307020a0b030601021906021b150a 69
    0x251a0660948541c42c0d50030402030540001038207004104c055410825204410f1042e00624085d00403d01900c1ca0f03507003e014034a25010a4a105442808500343d54110514001d8040c0d03014a408540c041c1c802d50300380b80907181a100b682d1207086010b140ca0055078861100711120f9104002c100ea2200084510f105000040d01c503050103061001080304108140c2400a8003074850100d42c2d00e050380c810850f0f89842d0b40008141d508035500c0380800820102c146074140c95180a0070341064151040604124030300c440002410f040340c0c01074001704040c10f200d1724207040c4100360000c003940041c0701c040861069243c100061a04900078102810319a2496000507d420310aa4031800080d10340883c0e5240000c0340b800c618410014140214508401580412107590303a61160f440e82001c003100107104c99009002c548000e03507140c803640c21140b0481c40d0500003900f005650591104022010145011000a0410305100400c01c110306503910300402c00c0280c05107640c110300160181c81011210f01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 938428102 1250 938426852 938426861
    0x3050d0504061a0f0a030308131b050a0608060f010e13020f070302011d101d0d091a121311030f06090c100c03030b0f0307030b16030b0a061b06 63
    0x41c0305a10103d403e400340b0750b860341400104100144101540410302c078596484500c80d004882e810304260f1802d03500c0410b804024803400d0b202070b01d80010840d0240210810700c0c144400c1c0c1d9801c9444000c6281c0f1094101e88202c4103c40c100c1d081586948001120342c02204d191119840040003a003180c1d08005410f000c1c0e0300148000029030101040810130950207000341c1000350581110140c213030307070410072280e0707100c2c48501154503141e651078100030075140d8400c01607010b42c600c070110745078220541c42c0100301c0401ca200380020854a564404080c0000c602142d11451400350f42c0b12903a26038826209110480c40030031079806000c4a550009500c080c009144003102d050081c201520703200301402c1c02d01c44052015441814034890500c00e00d5003001c3d600020369050b18000401c0c60300c0388082a45d03003a64001c440d91620a4402c000100b10005543d5407048483c00d0407801420b03a064002d405848100c0740e0b95601509084041c01401e114a118803030b568640219000401401c1d101e100848 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 938429352 1250 938428102 938428111
    0x160501020301030204180b0408033c011406090f12010c0504090609060e0a0e070f08370b09031303060603051e1e03041706220b0a0903050d05 62
    0x6940100c010015813409200e52008048540001300f1005074540da070b04141d00000b003000b0280e0034080041010001030714881000401c0c50b014106521400400b920951140814200e1442e20100b0000c03690845241a24008440240081d4200070035981040815580c1010058100f820041d140301e02880034040c000aa001548806540300e00f0040e03100256149900f1014072103080100c10000c080000786180d034071105000300081d900c0c801000050612800340e00c0210040034420300070400860100d00c0101c00148000b2207081045e1362011880b10740c0d180d600620005041c0002080851440c0a44036030000030f19050301e03c3c029005280107992100f5402c261549a07440c2024000c111041210110166070701008410074040d130f80c0556901c00090011022901d21385104440451081081c2d402a052a481c11020b20106201c220780d81c5104a0711071100503150041411140f012600700c14002d42c21094000c0d0300c6ea6250500006845c44400403802c02c8001c000c28101c281c110305c20305004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 938430602 1250 938429352 938429363
    0x1e130f06150c0b06010c060b041d1b211e010204060e0402070b150319050f010b180f07050702030a050f0601050103021323030a060b03060115050a0806040216 69
    0x414200908006445081c400000621041c42d0030b00c80400c8820500700d82c003c20901c0c00c025021403d1074040060300c107508805800c942050040510507003094812080050030604a92880c9170b214200c1c1e121080e070b0703104d05400420f0352039210300c090021b0741c1441c00101e40c001200c5d002003081032508425800004843d03010f950100e414010303113074001088000e17a103003200d065082501c7e03510f800e084004040d00c01d840502801038480083d072414810407030020440e402c4901086804e04042d0348500e0001180d035290b5103010644d00035441c210340c0c40403104000d100044001c1c0e41d41081070034800c0010340040140401813043c01d005030703010450b141340c0a10030070180207094084803550740380c00c40c1a00514189401070141c00d20107240200d040d011540c1c680031002480620751003030803049542070846034150099103155000d001c3e841e0814032400b14180d017220496a69509681241a10005d4403400181e0406c20100720030310601c85207070004801000127192455001108000c91505001200d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 938431852 1250 938430602 938430611
    0x160801171603030903050d09050108060f03070816080c010306030305070609020315091f0b060702192c0105040203060f190b1b160b121b07031d0f1e130f 67
    0x1b000814081020034407450705144107172500300000603000c1e000050980380140c160102c03403446a40c00b0032004000700300080546100c82d01d0315254504c0c807107550107907200b54071407205e440c691944280f04250880750155142800e10009640740c2c4040d00d03800d44244d030b00d842100140e0201003d180c0b6a00d00881503100108000d650f1503100c14220718071106203d811a00c2c0100c60480d584608089541555044034418003d0403200b03003c8070500b04a401071100c4604810099403034280700c41036032980040217078002d01c45a032703500c0401c802d0703210403204103410440c0014009824100300d4280400614500c100302d0141713855121100543c2c0080754418030300c070000b4601d100350180c1840110303020130500b503d03200168142190381d565446981ca145580142110000d00700c0d01c0141030b81c11012036034415183c0e40c0c5003e824000c0403104880c0352280c3d00d0000e036080ba201031409042a802020b805040c4c000e400c004540b003071040000074400b09030002c4070036802942d241c0540c42100f184407483d1f1400038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 938433102 1250 938431852 938431859
    0x261303030c0305060f01050a03021903022214060d020d1a0a050d0807080a0c0507090917070c0314100e01050403021c020601091a13050f1608011716030309 68
    0x3415103a455802070309061910061100300d8541640b000d100c240c0c00c0c00e150b5079031114900210001e20910712114418411020105041c9905800030441e0302c03411407030250b0403421220b01c4400c60080b44aa4000310051020107140c03424004041c14221040c0e003c01070400c1204000082aa0754000403c0e03c04181c0142c42c4001345840d408290240a040c1c1d24000c2100e1550b542c10f10b0b51040b030001600d00d040208509668510400030390400350351060559a445a60b000301002801c0d03481c2c0111040e40ca802e5490726100c3c45c40c0c064480280d0010708064901c2e00d11340300c1d1b441c03211104c183c0e1161401800510807101c03001e80194402c3c240380d80300000b2145000d0600909142d501850082d0f040401004008190f60004440c0e0540340051070008507882c505c8882420300c0007003003905403c00ba190f0340b105100b5800f54000307132091030828064081540c682880d0360181102e080c07140d000c9150500140f061440c0110041c0d591841181203c074124005090002801c41c180d208074000740c500e02c400d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 938434352 1250 938433102 938433107
    0x5060307180b070803040f02040e121c0b010e0d0201050904060806100501030c0c06050c040504050c03094303020a0b0c0d03021201150309080a02280210261303 70
    0x850040442ea4241c0741440e500ea074031180e140c440036001410110f004442c04c0d0035550340307074002200c40d10460102d51042e820682002505d410a01c402c14002c1100c54580034441e4a6000e448520340c0165910b03200d00e442081044480e08140105904000c001c0c4403071002d42d1500d02c0b40e030000d8a0a1802041c480c50803441c171030070712010741e00304604040c01c040e80c040751707a0341002d91030078680c2d40f000002c1078607590910550958000c6a01c47ca6010742080107200c00b241c5010020750103504988252900d00c13161790b0101100d00001c542050802c480400084102e0301c8054060300e41342c00c9107030340410302596038001402403c41a0484840210000340c2e0359007024040000702d10070b07a59410305504040e0b80c600001200c4005100d004140d07a040784060000720301c00e600940540f40e00900c02e80d100d0704696402556143c42c2e11404d1618104001680c85e4400f01e0241501d00d554000c2502c8012540d02500f02c55000040d0103002c3d540083c0c403181440c224000c00c41d50302c1031a12011041c000d0800c0e0400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 938435602 1250 938434352 938434397
    0xf1b0309031210142b11030d020d2c0a06090e0a090f030e010201021306030507020f12031807080d050a17092a03120310080d02030910050405060307 65
    0x809103088280808000480c0c42c40039007440702108482113039803408801701d100b04141c078210710a0341000154030180c080041a1140b4241e40d88150111500b600794490705a0f0f440441148180c0843c01252907580c20401a0754203000440ba22651852844003080211701100c6813600180081181c2034020b00071951400c100551000280500f400000c0d40b940360030071004095100a803c0204000c00b01250b40d000f5011500c9004101038122900c5541c0e0200034011b14054880d800180180300d0315003201c01000611345140c00300082403600c0c0d620341000faa02126128154946203018003031000458543c00e01160b090801c171922410b603518040e0100402e09543c000102c81a0540d540c28060b00c141c00062841c40220b801420700b20890010031400074903843c40d100103904d4802c802d6000902000c420217140100e1780c100742d0329202d03a1038512158031200380c0d04000005a00a1028400e1468880410b82c45000107082c481d2410342c0324008030b001507000f02d03115008215004514140c0880c81200c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 938436852 1250 938435602 938435611
    0x9031e030f140d0b0105120a1a10020705120705030703050705150c0c090703150807080f060105010c150204030611070311060c0703051804050117010b01030b0105030f1b03090312 78
    0x10004481200c1d2500c1c0d10710b5000300e40b0381c0d0b0750042d512800324040b41d000d9021500c8a03840c55080388094a07012030020007604c001d40d081b41c0e126414115100044c142412503007842e20042d00640741503402c08050101c0c04040082e003c00c1c5100d84080044c881e00d0034001074000e580110040e060a80c02c02c0700303000d0fa80e0644081c2480f242410040d1952012000c10364620304102100d401d44151611103084010304070242d0311161a03480700000040f1074030001440001c071402c501c10354150301041c1e1000740c0c40710303024801c0300d000c200b04c4608403000075000034043c10344004c505001801d15031241c40314411500881001608040001031480c10b1540024140416880c0f800c0107259524140c0d4025170030b405400c4000381440408100d003198003103242c0f44172030110000b510402640d80e5a0514a501a02ca030184070040c0d4039000551049501c00c0c0a1444030800c181c580300d20f540c44152001d400404010280c0d0100308000d42c240e01099003c00c003c41c06404210003c580303d90102c40c0c03130b5014000c00b40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 938438102 1250 938436852 938436857
    0x1103040f0504110d020310031b030c21060c0e011409060f0d091a0105010e030105070e040902060403080f121003030507030c11090708180606030709150e0109090b0901021c020a09031e030f 82
    0xe00030000103503040c007642f0649441140e00050003036a460650b00b0150b003124010805824082424000350b0322210082400c4402d90b589094900007041582c00b074400e001d403003034002c10100000303107580b08860000c0c60800150100080c07141c015880d41062036809558285c0301e140d903117004000540e0302482c03200b89000218002c110500b0040009420b14440b142028001d640b911104010341d0f4441c020b990040d03401041c02c079034a12405201142607400140920702203c05c80300402c0088c00104052001e41c0c0e0705403a8140f41010b00e0b10705070341c0c11520352400c858a0b00c00c01040d0205813600728216000300c82c15143c0390035a0501101c1c6611210b1100e8079804c00781e0001041054507500060500c0840d00480d00c00603c0382c030324610894010300c180d04109140c07040c841c00028181c2159000041075402200c95040355100c1c40f0850303082c3e12900050030303008620b015201d5500c08255008209401203070400101c10765996441c4050405140c8108100c0026a900c41040c1900f240c1c00c4803444000c2d2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 938439352 1250 938438102 938438153
    0x5040305041e0315180b06060412060c0216060e0910031a01081902150c03040305062d01141201022713090201020d2105090309011103040f0504110d02031003 69
    0x2107060017420103059400b425842c0ca40340032443c04d0b20360008540141199081c0b84003075600d03500b0000060020380404400512480050408011891b094070381038403000c1d86c1d83c4e11012003d4003042403d040251003680c0c01e40c003601d00000025800b0210001c0c90b4003207050036400798503280c2194140301000a8110390b40c040d06c540f43c401039440340600344006d4207440c6440d41b0b40030306c003050f1450340c00749420003007540c4078000510103a2000e81c080544604c040b00c1d11401303034503241500d09447c50028450301500c40c030303110400e94940c60030b40c60704140c10b8410000182409150f01081003030064141682071040a41d0080c5085414140005500b64100140c280185031459000035a501c50030000c1c502040004200c0144510002d01e03a41e0145103464000e105a0520081e03442e10380d0301501c103890210300e091603202d148840c0442604e003120000d414152009162a050201510030400c4445441c5420024070b085010340344040c6024400316400700380224110b182105041c25603090045510300075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 938440602 1250 938439352 938439371
    0x503010807060507050a0b0106090f080318060a11100f0b09060d02091f030b07020f1c050f0c010504060203060a0819120e030f060907121505040305041e0315 69
    0x5184045074541c0c600302d03680320041d0400601b40465000300400707180050b000010904d0b4881c0504041d11402c1103140040c0759502f03800d40d50313840b4002903001104660041c61006141800141c44441420705240e0b0100581c0d24456007411445141540841c0e0350305031001d1000c650b032181646820040e1442d4074a410030300d000512000301100000d1054a4540c001b445d0060b4228051034604d0645621600180e101d1808400340c40b000c0b81c3c140c0052040c03807800d44103180005504a0300165080301100c000d8001e90085400340d000350502c0039040c1c000c0010f4032101d20309200e4203102e1401040016202e003080020412038840c0c83c0d100320b6041e400800180c000c40409000c2010050307200c030780305191010030b030f000340c8015107001c52060f4180980907040300c0304c18000c910644101c0c034038415503844580b2002004692000c0f114060800360140c0008486031880ea40b1031038100c0c1c02030404508013a42d40f8010441110201070040206014200410400150104650052a4004040c03201c25039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 938441852 1250 938440602 938440619
    0x20f03040b071e0c03110303040210230c0c100206090c0915130c030f0e0604020d03020102090307060201060f090218210f25150f02070f081c050301 65
    0x500301900844140000c607035418000d4942503c00c1d4020b20300c07100c80301410000070b06007101aa0064022601100d034100d14048007204891180f5802000086200091402225101e80004030300c1c0d08486140c102031358540c071000c050402d501c0540c008180419480041c000b000044010321410755100d61300b8488204c0c00459522440b45095801021a660304d200080f2000300455070150807019108502042c11196041076002d40c480f5203085c068070104050780011105000094003060b0400f001003401460300d0b0b188001221f01a04c0054140507441c0000790a2103940e501a0000d40c1d50f0b00003c218004045454000a100c1d40e17500310305100012800c440845401c03251240309801c41441940c250185180f190342124200080352444010f01c81c90a40d10640540c074045802c0000030146089990450010151240c02415101c11180c1c1d40d0305030b402148001a0f202507005511010810201f0280c200e0300415107440105074064141c2005c0e01d404180c00d240c042044000c00c01444400e5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 938443102 1250 938441852 938441857
    0x82a0102270105030f07110c130b010e09070f0e06040317030103031115011502070b040f05030c1e0d03030608190615030507062703060203060a0605090f1c0606081f020f 74
    0x245c0d81090340c8603001242c0a903040c0243d10340d605038441c0c650707803411064001d1796010700c6003072b5002c1e2035000e03564040404200440804a650350f000411950304c2c80d001e01d1041101c01c0c84540e0180104d41440d8896941080410901050001d144404030040040c190710415025044d081d94010302000c0d65040d51141c03d842050143c140b490460320007240c0254402c02c5414002d00030a1030701902c65842d541000c43c980d902c3d21940703100c0d225071402d04616103021090211162039200c0d41410b01042d00b0284001106841d20039410b040d030b217800c00103d0a20074800124625100c210030f5610000c01e2503e681121503c04111400021018051000030f600040020903142603040004240c200030b043c03c900d5072403030303072140c00716003d03008001081003103d80145001e0541207500c0380724141c1300c09084030765020344a09a07a01070344000800445040c41060111000c124410181c00040c440d01c03150243e032646d80c81403e0700c1d8003150481188046028510110441a1006610b419a1081003d0190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 938444352 1250 938443102 938443111
    0x904080c15132405071e05040e0a090524042001020606060f1c06050f0907050d02460e091501020a2004050a0504082a0102270105030f 59
    0x10090744180c28090920340e803c0c0c800e0003404000748441d01d070049000344135035042d82500490340e04000e1205a0640604c0944080c1c50b440d201a0301703141e4951550901400000b101964180101c5101d100310360f003c6640b041c3c001d03014545040303443c1407030314143c2c00b03c100400a8103411501407030484016030f4045801500000c08603100e80e2140c52500040300d4610442400c515101c1e40400604040311154107e0000c8540407a01c1e440f1a0310130000b0f200b07128508a41b03010000300104080c00544500d80d0152200d01e00c01185d10307101c4c194100d04801511003505009032a80302000089483c10800c3d007480d40c0b00c13a02403a2181c80c00c440c3c0e0012920f1081c010b4a2009902c9107007004087c1070b40b0801101c0c1050b1740081c0c46070b40d2250440300c030a00000807c200940600d0800c00000c03100b45150003071901580c1d0000034280340040340e00010107114842210350b03088004040701301403071000074000b60050703101ca05800750018400c9a0b000f0004a604140c40b81440300500411540d00c0d8180c0080c0d611 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 938445602 1250 938444352 938444363
    0x30a02090603011b11100c05071e1a150a05030c12010b0a0f08010608060c0a030c09050a0b0901080609060f12122113080a0e0f0904080c1513 62
    0x840d124072000a000d8041c4000302c0891080d418510301405511070202401c0d1081401510204e4542d090204143c4000d2195140030440800c581400a40418100c260032400351140848648155030707103440702e26240c1c8101d0401d80904051000c032084079038030382084c450304680808150713280c180801d84440120091521550411221250708070302074200014032000104000411a00c404200408140358010000150710f415004201210001340d000c3c0925482c02e81141448060300f0218090a03600700000200800c400c00052213865450b495070107040046005034440f0450000180325501c01842a44600100340a02039070b602c0c0e210301d80480603019110202c400d030514180a141c148003114454040000280303000044040f00c0b41008219010780200c82e16807101010304110985403e00074090300c4042069000139806260b60002881000c1c3c10443c0b1005071100155040030202d42c02d69981000161401c008401841540340e454100060305046007000205414404410b5000800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 938446852 1250 938445602 938445619
    0x91c0b0a1e09050303180a0510111b010605041a0f091e07050a1e080f0907030507090e0601061119020d06090311060c0424091802031f0302030a02 64
    0x1144907000100203054090180310898003441c0481c0d83ea841221034030029552280162214100132070110305064008009011900d20010351400401a07000d0006060744100701e41d80789403402407a10702800501d5000002d14525210602058800b9203842c00c4c088141c102d541c000c90f40d540304607004401d10960360550565910202d1800300a010154120001d001a0812050a80c400e004240d001425551482c00890342134083d4461200d00503028089400540020340135418825459030042c201811580816500c1e12603508001e1641c00501d183c90b1504d0306032413584c0c002c01800e8010001d41c9015140074207c65422600c4004a100b0349040303005070700040d0250f5840714250408550002c504018600c1c1c1c519002c0c0c9070709552840b0034058001c40002407a0807841e038040d50308407500f085100c041c05003040620302480b91401800f07400d000c0a000c001c5803294039140c1310070319908403c00042e903d00b0304104403242261440d00b0140c41c0c0a01220510051718085540856140d041c3c443c40d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 938448102 1250 938446852 938446871
    0x20304121403070503030c0d0c0509060307030c140c071e120803060d140105160f0f20010501031a01151215180c11030309060105010503071103040b091c0b0a 69
    0x2c0c150f1103451000341003403201006102d00301039070340300800085081000030001c090300107905071050700401d9001b55002c601800026000e40c06600030000b080d00c0391500380c040c0d101702c10b00000c494104414203034003a400100103000c2c04a088042048000130108031540403403800c0da40219004400704003e00c00c03c0f0110200c2e0240e00e0390700303820b103041d03500500d43c1444a91108030380b8000c003000c072110540c0b08051065980140e001b103055441707071400303a030b5a1116100000c4081d201702103034080b443d9181108040210aa9a0038880c081c040e51054580210b5241000303c10000c880c0180c026030103001c4c1000300301e41800c0d085000c13031130001c1c1440c50102d080311402854102d66142ca0b440a2071501402e00c0c00814075615600103a414100da4444402d80882d20000350760f42e00088031020304d5640f05030010b003c190b016402941d40849549041e0044540046400d421500f0503403003144400070109482405280c8481400c0890011045201807004181c950191449014206c0880680d4681451 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 938449352 1250 938448102 938448143
    0xa0e040311030c0a060b09070c0b0112050a08160c0803090603011a09100f02070e01140919091b0e07081603020f040806010e09060709090b0a0302091303020d02030412 73
    0x40f1081c3d107082c4269072100046003081c201921000060034070450f0b40c1000110880d006060501903150094101c41183c0c1c2041540303803007841911303000d0b11184a8101d070580052449001450640030700708402c40c68020f00d25000100d820f043c0c105840c05e80080c0054a0541c403660305990440301c0e054006c103a810b40802c8000c0740383c0700c1c10804035042540302d542e0720300d05a0401201090702e4556400c030394055580c1c2d04860f0104000780510020803140d8448150185401ca000b03c0d0042280306060750030b01c007d808050225240c0307080031101a001d10301c80c1002e144400318800c0042c003403a4103080c400e180ca4030b401018110000e0040d03043c0b82e03100c6c0c1c0707044003a0310070750603122030328480e040041d0b40329101d004a95440c8000d00c0703440210150800080c003566004901240242110307181d10f103800d0300780821100030700350b9012a1038114401010006c050390320403400c94014a8080390100c522099402c6c0203040000004011065501c00c220401408101e01841c100203600000212122044d02202 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 938450602 1250 938449352 938449357
    0xf060c0627031908090102070201050712090b130503061605030f1f0305100b030d1b0f0209070804111c020108090102120c1908040b04080306041e020d05060a0e04031103 74
    0x20341540d200129026810f00c111501140201205850b568240c1e50340c80e003282c0c02d0344a010002400620b0602c030b810002010028800140c41c118104480d410340c943e400a48036821204c959207064a03500c03c00c00440c2070078044103030011081018480360030101c80e400b8100f44005050301101d485034500080b0740208021120800c4100d40405060403550390500941d07448401c0214a08146001e1441c1001d1500144c4c18030041203503101e080c1c1894800507601010700c200c3c6407ea03002000103240c00f00695070a054103108485607240d004650a26060041c0c40c61000d000351070060118924001c5050030180016184070350918100c82155a0094014060b00600140c803001c003128500380300c01d081e224070140c004140d290424150b21195014100c41442d81030380c016040320f804402240104480c1801158045009030001c0703a414110848256840c0d00b00b010641c40c1c640c0070652030038200840c020302c2e800800c04c41e0b03900155401c0800b50300300140c000e44000c0602040905000d01841c083c000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 938451852 1250 938450602 938450671
    0x14090412020c10120e07082802061306120603020a14120f0d0210150e090321010501090e090705100207091401090627200412020f060c06 60
    0x1854001071400040504413075440300d02456240d0400c100d01c441030b280003800d03104a80c0712800624106d4111403800c1101301e941d0ba80c05000d2615007180030096101d05000f03100105034100102a00d03403400000404004a8102c2000c0040c2030100420242e503440740a03100b9075410100e01644480c0d0130000504038030410108800d1070144401502c04901c01003403000d120140c5070241c0700e0001e02004003900300c035004d1040404203c016002444504a40c681d165030080c000740441e8036094101000300403404000380346e80305002c075040050000f56407050303082009112450703611080e81031451456845ea0200c2c02041c0c0102d815800d5000010300c03c1100f00e009002031107003084030589040210680e24400d00669005505001e40041c1161240790b420070045d1102d81c0e00d2400313415505c5071401810f25107545032010b2806404511340c101c01e9500500081034400303485840c00400e0302c1400ba82004c50a1561b10410051062072240c03100031501a038000302c200f1400c000140b00f8406100c00c3d091614 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 938453102 1250 938451852 938451859
    0x20901030807051203040c0e04020a08030c01050901060906080c0607020109030c080c010315061e050d1503060e010915020d090c061215080c1e150403060614090412020c 74
    0x414405101c0c01840d00500507400c0d10740b0941c03c0700b00500c082c40300780d5008101e400340010401011145540d41c68016100a04880705107a07940811443c6070820003041100e655071b5030502c00404800d204403001040d0010b024014903141905458407081921000c50041070001103000031a03104218040103503030310900d01c00215483e000141d545004c102d40d9103004c42d16000d034000007500410012411500c00d5074800d202e50017a81604a501d288182001041c01b03004c2c001c0c0e42185e0814080c0d8a030340500c0c0002ca072010352840c10301c1001d44040780310000d5076915040402e00411140741028541c8810b0138030240e41d07420140d440d80000c220b01100a45030304d4010002043c00e0f0340c080000c804503954240c2c28480404806115400e240b090711650b001c1e40d0018110b200d603030811081d220100c14040312541303640308040c00820303003c0b41c2134114107400490005042c0100310040c4a0400a0840c42070440032003103400c004154072190140020b8041c0041912035174101d88200041e5070f0041014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 938454352 1250 938453102 938453119
    0x30708090a12080c0d0914100c05030c0d12090b061e030a0b15030d05030105010c050f0106080c130c02101e09030306080c0d05101805070e01030b0105040c020d050a02070302 76
    0x203040000c16500300521690b451702802011080451003403002c07105030303010449202880c0154004000e05640528001c1d014020180c031110b000c264280082d000460242000d046020005c01c0c00a0581c00c0c45d060f544081481c1c40c1038600403600c42d104d43c03030b0310080544078041c0300c50111f0306501c0ca01c14103e201c0c40d03051050f20304c088108907061800900880000b581d00d4403590110003010303110a6072005c0d020010f00d09000400c00c41d8458503ca800145c001c0c001e41e02100c4d000100a170035609a074201812980c4031204200103410181072680c680b6200704820440c107284c504000792542900409400f0954459100d00c0301c00580d10203944921021440400540c2410720300030700a03100a01c911000f9000341e14032540c01d8206800310900d40f69100d0094813247c0e000480c594000c002c0c4050950b051403000b040e140000c0d4003000148060010510106140d6142d8901000c039150160041c03801141400d260301e040c950002942c0c41100c01d03a040c195110010260100c2c504100350f44060341c0721404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 938455602 1250 938454352 938454389
    0xd050703050a051b01030903020c0f0d06020c07030314070b0f0a0f0f0f06080a050a060f061a070c060906080a11220e06062d12041a0711030708090a 65
    0x10340000e21302150150b800050400001541103e800740806409608201080d007458502070750305d003180c1e880c01056203411040503228a8120f0300610481303a007688c0000400c1c014160440306141040c50f07035240c0d4038a00030a96a89031001d6101030040c40c60990a0701c04924001e2203a00180c0395643c100004106072805e0510b00d0024107a40d26100500d02c0c43d083d4041043c9001085416003550040e000340156036044c1d460400030320803800c418201c1580c88001080c1410540030703482413951180c1c3c101ea2140d42d282031640c14103015511401c2442540ea100300070681d004186c1e1940803200840001c1c0c070406403a1422036500c9100b900c2c1d9150106000030f40a08030030400718405456513440c024100c0e0b0340c0e0000384103407071280d00000c0c400640490050a0a20312000442020f4001d071100c2506050201c0080f02490300d05860460b40800c501000707600440401000c1079101881d898460038050030103820703e0702c91041510203002240d000079109010b48913a0024002070001515182c0f0000d42c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 938456852 1250 938455602 938455613
    0x102070204052203030209031c0c030e01141206041103011e0914060f0a0302091009050f1510211e050127090209070f1419050d0b0d050d09091107020d050703050a 71
    0x11580c0701200428000e80039180c840d4440d2540b11040c4650224491400c040c039607001c53f035404000c1202d50301c1502d404055513410b00460181d4000e001c400b003000403051000041495205040d0042e26090307142200100c4030b055404210358105005980480c1c41d210b641000c6500c24034150800ba41003108a000e00c10400341001a040484e0329554003080f05407122040c03181a14426140003030030080e21400e150003481e0450240b118074200d0300301202001080410442041a014504850203503103042d15101404c80c0b0000c0d0f055158015010455981000010002c8607a51518901146608000c090058181e41d00c56034180d27400400c080128a082c4c000100032000034080b2500199076490329801010b51603060320f1644e03c0074034403000880c00a9104440ca1b401903580f1b086003545400d4008202e0300c3c0c90306c8140e445406140584183d00c0c0d8560301a012160310b1384010b030000d29040340c18403a10681000e6461a07603044444500054036820040c1c03a080707003504040c00b64010a50240708214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 938458102 1250 938456852 938456867
    0x60a050a021201180b060903071a1c05220218130803040b06030705031c14040909030e030106060203040b030f07051207030903030c0503010803390102070204052203030209031c 77
    0x505680741813243c401781409011180c007818034455003642c420f000a01880c80c020301a81c1d5429a0043d00c50f080c00d8043d0000011b0802c480746440000e541d44d001d005c203071107000360204016403100c0c40454842c17000c0e9010403086400144102d100c000e95a000c00c200030b5140341e0900f0b20342d070440c240544034181414000c101e848296038140c800c0c40303a00300000d040d00303012a00204028200303881011211511100380e9411170130a5500801d640d08000105540300c040c403038060010b010b5610301e414409624141401c5400c56000801950710900c002c00c020b54902e8112540302102c0b175444204e41e10f440d0416103c5000b120030400c0081d20303100c10801101ea16a102040c0c2c2e9029a400b840082e400308070680d00384c07200307000e0351040d900200302e0700840c114074154842e800482001d041c0541800108410b80030b0401c4000c0039207076500002c01d035056103420300400340c00500c4151091140200303001040081c4003506001028160003060b1000300e9070301884440305e5444614403002c4080121007004200d107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 938459352 1250 938458102 938458139
    0xd031710091e150302150702130905060a0e030310090902031005070503040b0709180b150d0608010b03030c031605031e0702010305090d1215050307140306070e0102060a050a021201 79
    0x2030b40f50418000404042c5032460080b0f9401802d1500000b18040b580c50385a4011101a071304002c050350814440c80c000d20800003101d0040005d00007a04055134110f045e510052160700c00c0368018400d101034a8451a0800c080b1340c041c01d0006074428007880800d0070700d0810412108294504402c205049070804011440703640704000005580c0d550100a4592800d180a12480c82c02000d00300320010034540d002020b0540028000d280804400c3d010261503886241c07001c1080e51900400c0000c03540c240100d5001c0e6a08070042c50804450807501c0b9a6402052415404000c00f4806801400000d10484118415440d0800e48a40e2000751854003175007c0c4000b01c0c0003a1824001410b1040023184030305560785143d0b1160355150080d0b84100160180d01480620926018400242c0e41c0d42044441d004040c1e04c030740c803c4810800c1d030426051010040180041c0081515103081302c0c1c0e0b011898540c0500300000c00074050300c892485d9402400340d0045e0035018507200f00045960040c0b48081d5000303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 938460602 1250 938459352 938459411
    0x501060f03021801050c03120403020c1905030a0b0711161805041112010209190609060903030503041209030f0b100f050607060b0f1e0a050d03171009 66
    0x10100e034650228120321030382100010500c188200ca071484d40c420401040050b2003041160f051480780c0440c0d00440f60706403400c0b0007681c01990350b07003581d050508108400c07551034000b00801620300343c0400e4444996501c01030036808810005408180180095000e0300780e040300701d82c16800e14000c1c9140e0040107015204042e08c070810880783d0200140165882164021800d42c006c00091050007070030080720301700d0352855400b84490030305511180210341788503610700542a0a06d103000c0c400780c05002c05401170001c210318142c080c0007186c0c010003240d4001d54440c0380700186100c5440304036003619640d00002e140031002100c50007030020700d6046078001d100890110802a81d1006210f032036504d80c0c0b25a1303410a109200003000300b03910354400010303540b0140000c0d020b506001c00142c0b40394050180500d07544074007051900d050900e4400b80000d418180d070468201d81450310050804c214100452040d0800c590020306482009084e00d002052014002d208000140c0710310205e165542c000c5801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 938461852 1250 938460602 938460617
    0xa0308060109150f0f091d15030105040515040c1502031201060e10080a0902180708060316050d0f12050c0f0114010302211203040b0f040b060f0a030c0801050106 71
    0x18650103102001e40840c0c45512181c085960049040c2c90006031069404240411b0000005850000b922950301e0354a845486254610b0725114042d00001c8404040d4080e031b02d8039040100140c07001505d01480d0940201050b0543d81d2450040f8404603c2e8005070314040f40e83c1c01c0b9031b0b03402e81c000007d809203068140131081640e80700c401c05c41d4119030001c0e9483c4d000f240e2595a4000c54022207250b03400c00e215042c04110a01141c000c00c03990110501003800340e8041108001c0c5407a40607c074990413600031000b400e5015207068040f034000006015a91083d070400260304d003049031901108111980c450440f034411201000701030700d20b801c424880c40f610b001c0d800400070704850601c030320403804980c13496150040e400d40e02030141c2d00403041c15001001840c40c000c00050102000481000241044a213580b80340501e030078100500080c1203240e000c40784000740b000040302c3e1001958440c00903900c0c90110b83e0000c2c00a44181c20036800500b106c43c0e03030701000c1105401900141c1c140d0b0120b864140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 938463102 1250 938461852 938461859
    0x120a0201180519030512070e0108130209040b0c0903150106030605030a0c0b0919121101030b0a150c080d050f0705040e15010329040b03010b010203040905040302010e0a0308060109 79
    0x84044a100c1c002c045030050b600c2160740ba0180790248a001c0e000e8030b00f140c00c1c044c000d85d28590070001901c1c1e031742c040341d0100301113481c541c1d20090b441d90010115408600c04a907541c04192000ea0180008000c242d460001600701c1200006844100d04020119101e10000ca0080c3d50f03809020300460300042d040c04008915400e00150380c50100d540880b08000c458604080c0c000c035174004000155000e2103a0800700d032040b4000c20014090001c1d440611000c800c41d15003049800e10400382e4034185400d0200300c904d182e8840408070b044503185e4114400070450703540104c41c0d00200c0f04006100e07000201350401a07600d96801f4078454203402900b8030307998980c0d203807e85282c080c40c440d604446145900160549010707049407000d102043c1404140e00c140a0303c040000444089030a0000250241100039880d0601410f43c980105a00802150b0240ca0000f5100c0c42240200d42d6520748134008182058800d40c08120100300500589420820900d0001c03d00181519103a0001c0c03805100031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 938464352 1250 938463102 938463131
    0x302030d030207020d110d021008090610080a060e16091b0e0303180604120605060a06050f0703081003050307050f01051e010e10030c0b1b010204030c0b1b120a0201 72
    0x301d0f05103070000c2609500320582c1e0f45245100f020190b01e282c1124240565200503100e0381c0306948520510784aa5020345460aa001d04e000001041070590360052901005080710105800d00226001540415005d0702c4031001440c4c1b18401d6034101c5c03201c840c90800101c40925501c0a14402c040c00c4148025110381107084030400ca0322001c19905030820040901000300c9a4071007040904050901820541d56280d811702c0c0303001c01d044c00d803a002d0f15541080403514015408101800031405c11717506000d1041c40c800d07010300135584014203210412700854140212416118000c580c41000c490303a5103242c0c0f504035220f8880d07404100ca29030818021442c0100304000c035031800c404e4403c101480313a107409818447e076000036001a00e82c402109000c13020850f408a01c0700030b05000a44143e070b8640c80340c1a003006559604001545900c103110a20000da2808040c008032403400d02c000d0380360700c00070190500c0c0000c0115069014400d04116a0040c1e205c80090444c140c5c0940080041d001c1a007001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 938465602 1250 938464352 938464357
    0xb09090a020a090b0705191a090a0507170a050a0609031701030203120f1303030e030d11060f07020327010e030a0314161b0302091b04030f030e09040c0302030d0302 72
    0x30302d0128540fa04103200c030303810510190030240d000d142205d005000e031200580d003149181d40159884405c1560594101762510074507500400c02c6001081c142c4000d0f03d07013540b1100f440c06084040a884c2c2c004040740201000349050154000c000e403a00360001d40340c000001c0c0070b071001c100c0114250b801074176112400300b081681201d070060701800c00c40ca60a5080420399020025a222503c1c1c240001e595080f520b1841801442c0300c1c1d101c0351074a48403e010140f504245003410410800c41ea0000401040c0214110f81c00c69480e40584445484403201030b421400b8a002c40901600c4000b94011009445061000300b42c4080c0c9445000940d0340052684034200c481014011a422021007000100740000134613154081d05560f840240382540c0342455400760803921003001c0300d1007106100f94a08048216044441c070820301034500030216492005014170302c00070f132031080340342508070516003d004850900c00d00140510064a06071800003141801c034041640280700f07068010f46c000c0d00a208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 938466852 1250 938465602 938465617
    0x60f0403050d02033111030a050304150e06070510050a0b0904121202070803041b050307060e03120c010509070b13140406080a05100f091a1503070b09090a02 69
    0x1103082c40d250103500c0719006588043e0450075540c226400d0400512401da1000201c01340c101402c4040000a091045541c00840b0740f43d4803a4104042d8100028000400c0300d040303800122916400601d424070695000d0704945034190040c40c00100b00080010224181c030f003a8680b1071041103580c45043c070100c1241c890386140307900100702802050102c1c003005814403000e62145403165440707281580080a136040b020041710700c1640403050100708528086036982c1040c0820048818500d0a0b001903514201c80c803030030f41400b0401c02040c01544041c041001c0340045003c049554070407940700c0d18020041140c441043d400f1345600856992004001c89821051440f10714140c0d600300591b0b0090309094405450342f00342d40f45400a440c24062000040c1d02d80502c000e05010618408203906803a4411151118140f801080800242c2c05d403443d40c00703c801181000c0c85c50758603000801c0c1100285c003106a0304d071088020004940d11038600820b07103914242c602c0f880940300c030041c00d01640100d03c1d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 938468102 1250 938466852 938466857
    0xa0207080f030a05250204360209041401020f03010e0402130e0c220f0603020117010b04090b030a1b081509030304060e03131410050703080403050901020a081209060f0403 75
    0x4040603241d00340710803441056000d03801e0b03080790889560000b41103584406544000800d00c5203040e10500b80c814048e03040007100b10356815aa01c0940c001440754400410083c01c8000c60511240404001d42c180c40d485120002202d1ba2961503610381c0f266140c088608a114080170002803400000b24000c400112450b00002d041c10a00d95007000b8a6074802a0021000c080061203015446018000c00504400b04080095401d065000040498040c0d82015541c40340350001040920700a10890b404c4404083d40010900c50240005c1c0c105180950302030300341405115030f102450001c0d40d6410071201c0300811071b444c80c541031540c840c160310104c4400400d50000e00000d0003042264212600d0745e462003040d246821146403c9003c854030356004400400d036030341440100c82c20f1030300c5542142d00050406504260150760014224100104000c040100220304131009034020030030540c2140e0f0180c22162611401c0300f0040b64036100700c802c00c80510542001c60408007461544500494041d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 938469352 1250 938468102 938468107
    0x315021323041a09010b091203040b070821070809010c17010b09030a050322090912031e23060108090a081c0c110c0907210e01020a0207080f030a05 65
    0x1108110090440031820380c0720601103c140121035440e5000b15018210b400c0c3e00c41c1c2c6620426050026820710030311142041c0d40104814041c41108500fa6502c0980c0324a0680c0d0721820703010321894422039500605440c00c0c602c8113101d1020341002825100c0c05c1540000c000c080f003800801c6a00740c04d8604051203c032036440040c40300c51030b920002d061301c08001d0104e0380c14001e2665084c2c070b16405240da1090402e0302c181408482154603d070000200030003c0d052201520b241c039000e0111550100100a02d65148002a24903075800514141c610258004018800c0251aa581038001c64019409510244400540070750301414003607002e8030720440181b01000f202e40d02d06565030302c0050000c144403c2d008a000b410600d070b01a440740380c50b1f15942c0e44151030295240d64540603514480b244100903034010450503591200144840081041c24820041c2d5042c41900040540d00c00ca00c100e9400010711881c403d40014811003109e0300d01044070b0302e13041b80f0380656171640110b41c50400062001c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 938470602 1250 938469352 938469419
    0xf04060602010e25050d1a07021c020102070314090109080303010605070c08010203010b0406080411030105100524031b0909041b060507110d14060f07020c06070503071b03150213 78
    0x80d90307460001b83c1c45594055a055130784650300400345011680180140c2c42040d0707443e480300c0394401104941d00301d40000c0d4202245075501800c10140c8044100340b03c00c005c2480c550680c8036074089001084104156603507561034001c024840c0d4010b542c150707040c42010070b001410032014801c0324101d80442e8030700350500b800c001c0200c4080101420589103d200030500d110300d99800c1c030415001c0d880041c032041d82c8500d080107010808003c0504039000c481080750a4080b400c00301d0449070f000700e0030120541e07044603030152201d19010301104541c201110030200010480303a840b4010f070a010340c69511800e90303515441100e8a00c15140000c0000c44aa207001c030550030b050318011701d51440380c84d003140c14030703070303140245182030403c50b0318150010115003400441d540600204038880302c2a80c4952511803c1c2d152980e80e0300c69904c005242e0440d00c1d00c0060415415000c2e10051503001404002d1b0040440c1d0b000c019403c4440c0000c0ca12030443c1340040c3c3c000044280d051104045c02201440020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 938471852 1250 938470602 938470609
    0x708040e061909020702210d050903210a031808091903061806150608010302090a06150905130c081311030d050c010b01050301060c0602090f04060602010e2505 70
    0x40280103950408444600c0c18442d81d50200d0b0800030342898580183c031500203004004400614140315822044144103103124800081205d03000103440d410300d142e45031031510200345426111903142103903540064501c0390380e1008500030718110040d550248440300e245400500020715008000300712040800c0b41548078144030701c210159250300565000c50a40c0c81d160141503031005105103141e5042c0c0900304e010071085201e40341d000c0071048080c3e030f05a0300305031021385501d0040c00064814251400002c040401503009000508032440201600c0119000e010700658514018035103e18184041030381080b2980c0700340c05020705140e03503465064075002014550350b450880141e4511030314103101003680d01c08010030082070340989c1c0c80a41c1e07845440e1080c0c1c00c56400d20075450401004000400c1010752011000310440d03004a1f00503a150194030004900e4081c14070020340003410004006002501075018884241d224000e071503000c21444c042d4580114420340d50342081002001c20301807401c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 938473102 1250 938471852 938471879
    0x503061f0203300603461203051b0a080907052806080c07140a020604140a05091302061602030604030327080406031505040203090a03020d020606090a05090a170d0e03070804 76
    0x900d90718400c003006d440d0031904810010b00c40654980b2025070005a005a0520410741e03c221a100803202200c20030082c202c462140d070f000a810054a00d01082200c03006121001c01060014014002c1050070b0b650a040c9050f20340d00584c00d601c14800000f81540640c0c1c003180310320000c005241c60401d00360303202e030302000e282c0107004018401d1000c500016250f90009002500c0d01c2e00d20303a00d245a000080011266150700101c1c018800c440c01e000082d04840500c01c20994102c0f42152585c2419202c003c0c0b1400581020350705120304803d00c0b0515030141d010400c003c4201ca1480c0c1c0401704108441c030300e43c5415200070218503081100304130081c8039a011486c00e07901042c440c810b040c1c1d5640010141d8000f90f810240b1504400c01076002c143d010800103503000003c2c0050480d038074061000450701e29004044400d040c0e150b0001950782d60040c4161400558410440e0041a00d280c417001c109400041800303455515004600042440020a944001d6403024805140c50304080a408104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 938474352 1250 938473102 938473183
    0x1813030c060213090e12040b0a05030603211215010909051f090b041b1209080d0e070302010806030c0306190603050a061b0503061f0203300603 63
    0x729401d00111648440e03504411008111610001c204900359001701ca044c50b002d44112800c1690405c010800400d00d0001d8807605545802d04e130303480703075940707004039007482404041000c000d103003084442d1480389031002520640d0300103904c4010350f99944420121462601c0080b0f0f0200305280d00c10410745259800055222240c1c0104192417501c603880fa00310703d615504800b90380385e10b07855003500c2070406121302080007426446980c50b4044d10b80c4040c02080030044d00340710240e01d414280081c40302c80c03011240346060780d0b8400c0008002200e80140c95512600040b0300041020303005c5821031400080c90111800010b014240c25140c0c50121520070119510b001c03003413526247c00001003401030009101103070103054046402c0310410080319076280e0701c2c1510390500c4804c1c424000641c890340402803020400e4540c280c2203608e120820f9145001d2003078102002000d089186524543e10009624040c60702d2081d0303226a200c401c2003680380c085a8045d40503002d030302003504034050924800507505 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 938475602 1250 938474352 938474363
    0x101b0521070611040e0c0c0106030c030b090d2105130507031a091b1332090c1008070507080304060b09090a020f0607230604021813030c 60
    0x810360340803201900300c00e500904042030301011a55a003030101a01504111101c20101c013440d141c1040e81c0007006000250800907010404140301402000940c403000c091034220700c3c0a0a80340d41c07454407140107030040b110003611303028440c880c0100d01c3c000c00d100300c08280800700503101d0b01498030120001b06001041030a03144945019079003c90300a10030500918000e208a8240d08549240090703c80340181c28045940d01103454000e00c45510004910162400c0381c4194142c0060303101c02c2c024007034094542484032041040710b00c00406207480d4807040c000c0702980520607910000695292041d07110010b400c83c60305402100000d1042c41c2d0680c0c0300d0700c40e08002d42050100e840720300c40c036041103c2c101c4090303071340d0340001d461480c00e029001e50100c4280005c1135050b9682c3e0108250761241d0640034082d10303010652404101002c40300d59484101c9006a8111707403a2080e50507039a1206a0b8240e00a00c07880105212400c0a51823062081c0c040c00903907000942d46036021224405601070569a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 938476852 1250 938475602 938475613
    0xf061606020f0c060907080a030305040302030d1b020c03032d0708070309051e0a21020607060b040b0910030f06090609030306060e011805041d07091a101b05 69
    0x1420520203401200800e0307082d140c031080038044452801402415150300c40d03018050811203200006282920f03564949408600c54031240341c1a4914042d450803400e4090030517800071002e2280d0074080b103602e415503007203034241441907080c99100c2c80b4684602c180440824005030b01d00800081c85e80440c1c0b03003242d44510b03140b0b0a8403520703441c0c0c100f02c504800062040ca820002031a101c412518030b800410303030a50345058810005058045644215200e03209101d112030b20407103510200481050f009041c0941d10603a80c50800d00400c014520b01c0d1146140c86412850790070000e6034913208040000d054480503046032105501c108030907c2c1201c0341e0351201040302c0055051300918204034842d80f170118050b070030202c000d01940d0304108058100569624040c905840d01141203045407000d440000701d206048111090702c0080000f072440e40e104041000030034284903406082070302240e040d58582c408080f02040b03602aa640307000000140c0c6011b03141c0300e03c0b800c00c404400c0d144c400c0c01100c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 938478102 1250 938476852 938476897
    0x6070f0c03080423060d0e0712141b06071b030212160b2118030301030309060905030a0201050405010f1715090a051e0403030905070b18030109020f06 66
    0x300c01042076001251003100214040010800d005490a28218410f41201448500c1008078204d401542000c10700b07551104103002d6169018003168019100d04200081d0100045c24500b0026009203820b00f054444c1c0750b203010305080b40081c903c00140340240070702e24061885d1a554170008500c0f0110440b941545000030069907400d01d80b5603401c3d0310b44050144c0c0d18280445160880c000d81c46803044d81020000d25051914101c01c001000c1c2c1840c080c2004ac1c0c4424140144504014003031a049100020003c410305412482d007000320b503007599800d0201e54950b000c2c983c880c5550310000740410740a0209001a6020b000309202c0f0300140d10300b448400f080c400c0e0511104000740d403244555006615112110300f40343c0e0445502c001411000d104504040c0e20b54100c01000c481c0b03410070301510030042410180b10307400c42101d10740c05c00116903025495204a06866100400d100c01300482210f4030240c501303044c05208802c0750003c0829034400c020034140b141d240c1c4241c41c0c2c00d00300c0b0500344281c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 938479352 1250 938478102 938478113
    0x18030d150e1b0f0c0313090c020615100509120c09010f05010f030b030307022d04021204030516050106140f0904031d1512071b050c0f1f08040201091508040206070f 72
    0x10000c0d1071b01064514003051900e40004101c0b00c88000c0d0004640001c420065500c1c1e08034401c1407168400d0b16a207003207900c011411103127070041808440d44604000c0e0240c03c3d00400141f0401c0c10041100c4402d25a40d8a401d1445500614812103001c540c8019a40d91101d010358002c40c0808000b0b015649480030300d50015020460044000000c80301c8080801c40d000109200c10a5080f0181c404501d0000400c2800b10a4000203000030100500005c07100401801950700341a4168041c00a11026849051000c480c8602410460080400c502c0c050010714240031114040c64044c0c0f58015281c04480f011001d407011010b040c0c6d0013002e14800c0d501081c3c80b2030300500c2c001074443c10240e15402c12a60061034141018021409010200040d0700850004a01c04009000c11074001420f00458000720f13140c040c94200305054000000740d2031203055000315400344924401d0b620b100300076849a04030410028005a50000550510009801424020003c0402c00d000e52000d241c60113090b640d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 938480602 1250 938479352 938479357
    0x1203070323040303060b1e0d02070803013819021c09180905030d0504030e2e1b1502131502010c0e090f18030d150e1b0f0c03 55
    0x642480c80c860740400040c564584a205c002e0501e8000da1868400f0401000d800b00e02081e0400344501800200d610516260350b04a840580d44018000c1c1c69681d41d40d1508240c0c04885040102d00208000f4100e10007180c0c0c2400f855440902c0403107051203010100d440d268408286e1100a501c00e24165a00110360000240142000c071703650035104906000c0e140c85180382d6484000501c0d03050005c442c00081e00072082e00c88010941d04000340a41d284c2c00c08590350326407195400d07000034000c00b031200508060b034400402000c480e801c2c2c164000c1c0381d030421600e500000c000c03131911502c00744460f00020f4400c5000300c1c00c42c0c010704015040c2200300302d12440e0201c030f942c0041443d8402804034564160280180c00e4081c5080c1040c500c1003504c400440e80300d40c4000c005c600a00207200c001181c01c0490354128602c0c10b0b01204907a00c607203003030404000070a4115411000c0341d0380328900080114076006281e11442012a01e480e00150240c3c060000e85c1091201c110890803e00c40c0c1100b05004001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 938481852 1250 938480602 938480651
    0xe0108010b2118070e01050d1202010207080d14070c0209190e030a02070503120c06060904031806021006170a02060a3006091b0f1112090405010503070812030703 71
    0x4040843c43c03040c0c0f032030782c50001e90b030344080c0c0044804001001560f031b84000e10f584c80343e04600d40c5504075005a50032802880307680c400800c180b0010891a0040c0d0840e031042d100c0c8042c07001111019122510140e407081101c000095000d424000003a0404044040b000302ca021040c10109000c0201d02406040d500611040c000507481035900700300d41d103010403160042c180c840d00c02508d003114400649440c0c0e94014031150099203000080b0302018030445248006911541c4d41d089444d448800c0203460302e4207a44441c100a00348140440d07a080e401c98500c040d90038404c01002c425059900340007017508000784000c10722070800210034400e801403218090a60a40d400c00c08190001c502120848065070040000c551a0001101149146401e4802428610309001311587c203852011164111400802500c1d4000c50841e124001c0c0d9200240074003c008032000d1065a07228401c2c141d03070b545a8440e401e155800800f40380c40310300f500801180c00100d01d14001c01c10380008201840d243d1081c02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 938483102 1250 938481852 938481871
    0x40c050d060e060a0b072f040207140f150a1d070801020306131413021f050304020f040c0503040b0c090d030e1318060519090c0602010c0e0108010b21 66
    0x1c00240303142151144000c1c046803e800c508100094443c1c012059101c50700c0d070550040368a00c030907d540342d002c1c0c503002036100810070366496205281c128000003c0b940d0018030741c4180038444002d01c4e00800c0c01075420500102043e42617803091211405070842d07508040b605800300c0c031141030b005028071249011f800004000b503540e04180040c840c2c100380c07503206503030514503080d1450540b681d2340681640094040310402c503111308900024122508418010307110784200c1d004800119086405980b040b402141e050b10100b07621002d2105a401507000c060004100304005000110100141d80c1c000c40c0c8032071140e0402d44068041202075502d460160f0124803040c1c00c211301391500d41384213560004200d1040c8210704155052343d00440c0b112030010030854445000540303406c40c614001d110318100c443c2c0dd0050f880c0c5030a01c1c400c4c807119801000e0040d420080380c868040e005448103001c484044e510995240e2034903621410581045040501d6541202d21000b2070408034500d980c010040305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 938484352 1250 938483102 938483129
    0x1c020d0c0c1707020f01030b010315141f092303060a0624050a0c1e0b0702211b01200904060f0b0a0c050a080301030b0103110603090c040c050d06 64
    0x50030860300200300140c0904061200308411001629001041d001c5d0031001c0c20045420034a190059000d4403100c05031a8031004034520015503c400710b0381e4000030110940f0180001581d10b480583c54064810003100480d00505080041302c003060501e1a82e0310b070a030558000381a0443c002420703c401a9038107002d1544400341400701c01c04030031150508101104800d59008480140a402800b91282c05002d00c14240303406814080e0040cc01a448421f0300011846480c46107001107118400741c2d044001449081c030600d02c5000d05125442d50192000380d0746e410907105004c0d8205115110040c10403c0d52071343c1180a58607215050980740a440f581d18076250341c40e080501080308d40581c4214081030f00c00070704000c0010158200c03241b8804524002e4901c514504000d0300d8015600d00007000743d8000000003080c41040e081c0d847c141da1060355071090380c00c40c1d1400c21041c0e02040d2411216074205500c0c6c400a441c0650183d017a001d054200b0b141040b000100307241c22520b136540a52114a0075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 938485602 1250 938484352 938484377
    0x30406020405010e010c1502090d0f0602070318080c0d0f14250501050306060c0f1c020105011202030309220f02071209030f080a031805010b10090b1c020d0c 69
    0x2000c80144010f4080c030f00310000541a40320008007000c887c03a01c0b41c560341c0c0011382c4000c03915a22a42c1c0a10b0350044989884018145044030003980318040c20390000300d420302d03a100d002c44c0d0303810f00100b00c820103c020640c001c10202000b1041481070811200c0300003240703084000514045011001030034000c050200c00c0501c2242e20a19242d801146980d02c40d441401d000ca03030b8210080d41e0700000241c4a071901c440c01101d0007450105840500c00d158821800d0141d2001c809241c8030700781c3c200c44c1d8000e00440e40e0741c03101400e0520f1ba01e270000790b05420900c040d15003802c002e41c41510181100c0b41410b0482c0308882ca4800316003000c408404500c0e00000d070201801420301442550150b039107014078a403451602d6000c44100b004c200140440b00c00126501524400d4021640b0078a101a51080080452070202c2c02481519002406429034800020030310303004414003011554000a8549420b1038041d90982c040305c2c08441600d201d5003400312400d0f0055600c00e8400c8900d941d01c6a03503c0c140d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 938486852 1250 938485602 938485607
    0x1803030f0831020d060203100915140f03070905090f011d0705060714031b0f01052514040f18090809010c1a190e1c0806030a0803040602040501 63
    0x401400c8102141d03185100010380c00c0c04003000007007181c1c40d01000ca006602c40c80019104682c03241c0280000f8000b1040c46452a80c0c507604800f00d07042c4072820010000b500404002001c818400c4180b015084148000e060034100110100d6a6005050f105910740b0b40038640c0c03c0710400c3e5000d04607039120200d240050700c0240f113140e04c041d5141221a203109402047d103562105240180d5004040200c1c0c0e40d020845052884003210b60000c058a8482020750082d010520340c01c0c41003101480b40d00c0c0002500f02062103000d02414800c0003400c00c1c40c0c1d00301b08100c250304e140c44020041110401031400210b4010700036001402d181c80750303600900d10701001c01a01524500e4942d489034944004040040d80603811200054000c4c245010350314a0707401c141183d2100d01b2030710a1a46808000c214078007001030325111030142a44410420101400940d59a407104259884003604a00801000e2140907004090340301e04c00504660f403c100c1d0b81d5a100581d001503d00710fa8441d00800d050000c0c0d0f8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 938488102 1250 938486852 938486867
    0x2705070906020c061207050f0d02040608070f0c05060f090703080408101416180e07021f02040e06131116030e0f031e010e01060b0c010c0503251803030f 67
    0xc0c0c049443c130b4200314412891110088026116006102c000100d00b045644000192800e020000721308548407540d861002d0103039003046544400044071000814507071170140303807005101500200142100d51340c5e4501c1c5800c030708010b0310079416445010380000001b06500f0041018015100207411007291400601f27003640c55100780f40000205200400824441d0b0301c80c0844540303a5454541500e609001c1c004401084541003220180c480758100640c076500015030040701d8145440c010000c0a202d1500300881c011400dc3e0401da0342c000000c5401c038a00010542d0f040140c038600080d6140ea000d181c4804c40c0e000e0b15101089600303620100040c1500901004421902039541e000000040d00001e80c40d10f0413452464405024082c003480040b10035400403040c0c9214400030030a03d0340358050fa42098000b500c0d05207440d0300701100d0940715031140701628002d000402009901c140504c041c03010101400358201c0400c1007410001c203082d559186030b01e00840c02522000007450704030b40c0080c07550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 938489208 1106 938488102 938488123
    0x1302100203030f0c040501020a02042003041a060301050112030c110a092f070b0408120f0a051f060e01020c101e0201090804270507090602 61
    0x390000010350080c5004100c03280d42c1d60b542240460b55104038010301c1d0061700000c001c00e0060078203402000c840409001d4030b1002c43c034401a00c0c40c00750800c403004e41d0761b180b81c1201786140d1094040e900b80c00200aa009001540c140660040792a4540c030006081001c0580c4902c01c3c40810b003840013140030018110070711241c1d6501444054014159803603e4200400c0c0c00d0303030b1100ac044603503c1d043c601480c0c0460401d4695140e000b01c4d07281c0208241e400400422102da001011005a10310605000107000d00c0c900744200d0440c1103820003080010440710050703140201c500456668001c950640c42c1c2181030740d14460040307060202300c41c1e07440d42121158080c0c1403000d400c1a0506148011203104020b2145002c1d0f040b426944c0710070303001d0003890003000140103810402c0b6002d100d031102c910700c15140d44520b9100c1800c0381e8040b94078000060f01d01d0f4040c00841d40c14000348889 = true := by decide +kernel

theorem cover : BRFrame.Cov 938309352 938489208 := by
  have h0 := BRFrame.cov_init 938309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 938309352 ≤ n) (h2 : n < 938489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
