-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:49:59.133363+00:00
-- url     : https://prove2.me/submissions/32cfbf0c-e5bd-4347-b713-81185fab1fb6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 567805755 ≤ n < 567985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 567807005 1250 567805755 567805759
    0x1809010c02010b150a020a050d0e1305060d110409140d0207150905010534050d030e03040e06060f040807050a06090522020c030c0a11030705090c030406060b040602100b 74
    0x10340c0c0150000140c0004c40140314110f01080010412107040c0204011040f0660080c1603c4864120001c06040842e28005160148600811082c0603140034400c0c00d211740d4004054000440840d154070003100700311211590000d9550b00711038080350654240040c0c4244000c0100307240b5100e101c000b82400e201d54000c0480d0885000300742072058003d504001681d02c00e1800fa5203401a02061064105030822035004140380e42003100151620030710701600290091003101d44049031114124100d490698603244d0b03a40040c4410f02558a140b0348980d00284010315041c10043c01076a00c7c11580c0c0260f000c0421648204010001c500f03080103540010946070402c181d001c3d2524002c16406240411075800442c000105040c5030801507054504103008a401c8945031000c5081d803541d1a80070300340684884080100005044c50001418415030700040c00100702500d80540084013500050421200d050315950701186525003400a0f05c000e00f5940c0c010550500240b42c6c4004589103403081d01c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 567808255 1250 567807005 567807011
    0x603150c0f080c0319020a05090103060e1302150403020916030c2d02121308100207080f180d06050105120a03051812060c03070801120201021e0c1809010c0201 70
    0x441d003500200312590103c1003041d402d949540d900111310080780038142811a052000c51040c0c1c1070782c0e1090142403808401e0300d04001842c1c031030f05002000b0b0f1080718881010184417400710b0050611507811424078800007203260525442c0c0d80000d0b41c0c1c1074101d13540308204070201e038080c5081c1e40c18000c01c0340b4202982070a207002e8520110300102507001104520385243d4544210490750710800c0349815482290412a8444540501d01c0030428450b2140d1000f82c031461a521400b03080c0c42c801c075a500703940034140614003005001000c101c1c0d0031180d11070521800303c074094810b40c0c403410418038225110300d00c0000c0540c1031008204076101c0e8601420781d6580000880340000c3e80004c01c44040701e01d1220480701c201d0a8000142d4064508100c010460213484184210100c401c1d001c2c41c0107a05640f04c600d51a0303265030305003142c0840c01d40040d0041c2d10010341d00d0041da0031f0300030007000d9030b4251064418849803180460b0244054613050614240442c040001c031003420301c69400c80754101d100034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 567809505 1250 567808255 567808277
    0xc06071104090f17190503091f0e07050303030112030e0d060612020108130c061416080c011107050304151101090f02031c09030213061503050103060b04090203150603010f0603150c 79
    0xc0341940705c46a400d6414000c0000101d007640c80304024901c0a080c44e20032420001460345054005000464807201c01c40c070a9240110301c031700d00442901e051300c68101210800465645080384c1c000288014141c00c80c038501014000300d1414050b21000d0601a0500c0449005910004220020082940000b9003002440200050781c01c01d2142c1141e880346000b040040e0911100c070984d101e15060f00d00410300c01c00c645010000424042c21840511a000700b00b40c0302983d4122040c0d10031640001c0c0b01c1d030401c02c070a21104a07640c580e10300744e095500e0081901e0000700c0d074141c03c4411101080d510782014401d440118030781000b10003403601c580d00590b09080b03075403040500840c10900000340304200410303c221a00c2c04940c8600010000c090307640d62004002e803000360041c00c0a000940d00942840541041c0d1b04003806025481940030300246150752680080700800000a0805540755490384400740c4401510301804018501903000b0b080020000504403044540910100051002d82101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 567810755 1250 567809505 567809527
    0x9150408120a0906030623060405040c0309050c0607020d0308091e0c0906040b0d0b1b0301030b040c08030f0904020a03110f040513060f06050c0f0118060e0c030c06071104090f17 78
    0x259500701e48a09684541f400c4d84003000580d40d028640055802502c0d0075a080c0341c0d00d504d034000b0011240110103585880c18004203010052151007000b94000c0450002000000e104104565201c1031100c10384003140203050750b4140203041590389106582c0440901509441c041d00b113582c018030b04032402c0021001001c0412254080c2030005011990f52100284071400f54612000c1e072410f040103002d03525a100d2501d20240041a102900c242c3c0840300c01040070200041210308401c0310141c9641410702030410000a9840003000004054848110000e200602006864845080d6020a032154200320900c40b40c02070704250303002014223048040104007240f0a1002c1522a18609242d0b035202c1c15072030380e260040303100441215610301450390003000b60507018160705030b100d01401e0000c00f0610b200c90f542c81030408003050b41a04014442c038443c0c94040000d016852040c0b40003002d200c603190006089404100c0140c0714039100c038002c08100212103510030001e120151405040ca040f4030320b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 567812005 1250 567810755 567810779
    0x9060e061e06090607020a0b0406090e0403021b180403030e0c0d021f0504080d0c020f0103020705330c07021906080a0203040809030f0a140a0809150408120a09060306 73
    0x1d001c034025500010030105a407565003c8450803500682071521207951004080003d82c4a44a0503000070304003407000c07964030500300d400360140e501a030041032007400c182e070311688050641400c55400321038000c0c02d05c41005600e410f54400c1c1d0103034500003a030b40305903401c540c01e1240c00000c480c400d40081214800680d10b00c46c1010070350120211402040704c0c1150252828801c030740160780c0610480e100113910703903407100035074401c41d100f0b0700c0e00c1e466440c5103001981039006014005100b03401c250a402d8040e008840402400881e0b070034010001940e4042c070070390a200c00c0d15506195407000030003106505011240305d00c42d810400144800340e00d0008018030340700000c2c204240340c54002020400740080c0000751285404000c4c242c03402c124840c0c0c185c960303941180c00126021904003078072014404012981c0c2540c2034021000e60719140e219010031595000c141580340b41500d0a12010400400800400d40b00365106a4040d9a4190030b41e8050150807099000178205420098203100c80c42c4062 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 567813255 1250 567812005 567812059
    0x40f1a1e0d3b0304122d0507051309020f0907270305060c0c060f10030c12030e0a05150721020609120a0e0f0103091209030b0612120c011509060e06 65
    0x1d600403114217424500384048290062813000c500c108000b10414803802250448c102c1e10200c484110011001a880c01550340328a00a544030f090345c00d1410f014200000b0140c0d020480f0300e4025403490b0110112004100180d0409400c0d2001c401c0c18010408104031042d08001685c800030f0402c20b5610616580c2c000080002072040e0b45400071800c90303200100110065580020b0143da101c0d11020305035081d201030442940061580c0391400250f08101000d00c003034072000341840c1e0b134080c0001e1440301b056100003005c481d51102d1148058120310b43c00004036100b0102d50240c03406041540f001c41c5000340c4072413401105030b02044078820042d0000d1007014801000e845a0150089000c0140d00402410001405002040c0e810810b51a441170b64034003920b00c82e04408040c0c0d1501c03c14040341424030800301c2480c1c2c2c4001c0d01c400f0850b0054002c1c0c204000c3c03010011958144010320400300f00100c4d407142a60503100c81007400300076560348901b60300800541d00003c00c2d200380e0740f03420382c0000300d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 567814505 1250 567813255 567813263
    0x1140108130f330c080a0b060a0e010c0b07080613050f010e0c13060e122829040212010b0d02040c030f02040f1a1e0d3b030412 56
    0x1110f03a480c94012450841070290720b40d104901e04208028285000d40740c1c12007000000340b810000651084100d11640d035505001510140c00c01c0041c2303209031086040101e80905200c030014110000071941783c66180700b00140c0da15800c060a101c001c5c001e900c0904a807036403801e414281003009110102c46101e04451001f8442d0025440f00301c5030354000e22036480002148e038203101011640301c0c0c100f410101f0804050354407121241074200807544407125580c204140607080d110750400700d08809070840700f80740a402c0003182c07054004145500b241460009152030301c0c100040009501e82210f01d02c040541a4000340200103140e40000d9529070030a030000d1046540e90404094148a9401074011107210350045558503200c120469403030340a4030406412000c50700c800c82c040e80700182540c0e44d090542900f242101003240c00d412990b08011456032490340d031179030b400646030704001400c484150f524440400c507084070410341d10380602500c00d04010783e104000c05c010500341511403c40075030300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 567815755 1250 567814505 567814523
    0x18010f1407080304141624140f0c1b0a0e0c03060d03121a09011703030a0b0409020a0308070606080d0e01030525080f010501020c010e09130b01140108130f 68
    0x1481c40d01c880030b0b4102e00c0c04101c0c24400c820305072003440800c1003000c0940e4082001f40021405600d040c00546694a0b02d9000141e40f02842e48200d042c2003001d000f800c24000400d41c03c010201c1090b81c9004120f4180352041d01d100321a101d6142400708040c40a007180202000652525903140e80051001600c0e860003010101401c1c2c041c14429011103240064020040c00500d03404030f61108a0051030b4015403144c1d810700d00010301c1a510500c2d1200d003902703a0001e91705560b60305141c20010035040e0030007a081500c0c1c40e01c0c80c0045c0c1c0c64000a8000e903102d40502a120149814000b044660030f4100f404c0743d6010240c0503032815007045030100505403d180c00b0072a699150200d040f0100e18003c03440001e100060b4410341d0304d8120740715a220f246a10121041070380d888004903507841c0c06544442c0070030341100000500e42091301d00b06502202500031018040007075a10550402c01c2684186c00748000c0b0540700c2c503d5030388801030780d410144040b801c010603030240d207d0300da43c04030850b002400958 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 567817005 1250 567815755 567815761
    0xc19141c110a0509070203071a06090f07030f111b01050f01090e010f0e0606012d05031e090d0215190b0a092a050a020604030e0111010218010f14070803 67
    0x1542c41c030054003911000e0908101c505004401940d0380d000310804941d0384090160310201c2c80c00c20b80b8001d120303400007005004640c607964680b1401c0b0750090003000c101a2a014080000f0500d030081501c81403403021816603e00030311900302c146c100803040d212036a90600301486100110b25818034155081000000f074011440240c06004004c0380c0d9143d280c235801c103190204041000b1a070207214a0082e02c0703110030060b916400b40b040d8600c03190500301e4954296440c030030880c8141c01940c0c4c08900c0700720b2250801301f62241d650b40000f0440b81e03000640e012100c031183c0d190f4144075030b804000f40389103035610504013110f640c11001460651080d40c03583d2002c22543c60358809240000500011500f000070044000304040c030500e200b80382c43c1d54421031690812400e4494011102019403950151415403103c0c0c0e030480d02000d0702d5208904020030a200101014020310042c5007031120070418083e01c03400140050210340c070000c200001c2c05a0b001250094003201021203591590041c601c0355256 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 567818255 1250 567817005 567817009
    0xb01081b0f061204061a0d030c0303090c05120f0d05180d06020702060a080105030105060f0603070e030718090c050603010f0618030c170105060910170c19141c11 71
    0x8041d182400e5000784403035040c001030210561101401d151040f4071440c041c90010f0610030321f03003980c000040c00106050350060210b8841d80c03104224038440d5845080c13041e034500c0054215651740320841456000345150301e5414204000e4205a8000c0f400e10504041d911004080c40c0c00001310214091401c01005a042100b00d904445100c1e60050460741c513031018440c0105184424094035009600e00380c040b4001d0f1812045200d011680106001d02e51343e1b07251000c894203210121256010f1040c00c80108000c0250071092010351b443c004002811215410101c1700034082c1e03030001d8025081000140504015200600152600782c20943c103950904c62401050f89080d60000c0c100704030000c804500800311109000e00240750400911254135410108103482038262010f805401b1980010843e10445072500f00701070907580203841025a190011070421a1401d41c0a81c0200000c1e6041c401950750f584d540b5130f070600c00c0c1d5000300e58200b003c80400d00f1604000015280c0350307883c020042c4a0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 567819505 1250 567818255 567818257
    0x10c120e070611070b1b0c0301090c0b0d0b0901090906050a14041b0b0301031a0a1103061011010e060906070504050a090203060d02030a3e06031e0709030b01081b0f06 73
    0x402c0b068841c2d075610509175246041b0941c0c1d11038090440d01079980da00003649014001c0c450303000d4200c0c10490f1140c2c6006030515141e440a4002c00b0b103141c8a2641c010b0595508030428001c20302500c0114501440c0d1034404100c80008121034011486d0002000c0104240d04c0880d5004e075200700001000b42d00315480e0100e080507588a402030450010022042004010300c90100c6c83e050070f030312410b070380701c43d180901a1800414122048001400080c4141c0b901900c00c40d030005e40390800c105440c3c140c061090a494143c0c404002c1c1750b00240034441006010040389500020520b0210300341401c01001810a43c1e01d8841d1000a40c0c000c00410055030760b15192242c02c503801400c64403000550f152030032080a84810f10702405286810b410905010b44101d80024604190b146103000301445c10404543c1000c0c00c0d004104c400300c0d400d10401c404450842c0d02038001601c070100342518628107c442403c05070000d60301c036000320b0f40d80307a00d034900c440079029042811a40c500d1611480c00210300c0c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 567820755 1250 567819505 567819509
    0x1171c0302090613030807170328060e040b100b07051b120307121b02210c0d0c050306060607030c1719120b0409080a0305040c0b0309010c120e07061107 67
    0x904e41c00c100c00010083c41100900b0002c2c03050842441d50643e01403103015500003250010070401c602941b49001c1e50b90410b001e07060308040200047c070185c841e161032487c468216012900c8080b82c00900c6404141c070155000200301528546140c01065520b5070f40714090040c3d0b800d09180004006035503540e0b01714100c402200c1e03480849844401c035050105c0841c0c046141c40000c158500c08140a90100140d1a80103c2d0040c00b801c84052000c46282440c50049991074018081c80c3c0c9550100d40e9115080a18140241c41e00c6048500348020035042500c09020280b18032010840000001d4000d6403028001d82c10003198009283c5a40780141300b0f20880c0907180c0142d08111080c040283c00c40b0311201100911503041040c014a082031104450980c94042e2502c58180a010340d1907211b608141d40c814800c45401e044144d55441d008550780003070320040b10700d03511014010700c403640c4800c0029010f0804a405c0c820500580f00090316808940604e03c03c1004510521511010401c20b40b40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 567822005 1250 567820755 567820777
    0x70602041706040c0f08030f18030f0a0b090c012109060f0f062115110a090806130c090c030902030609210a0801090b01021504050601171c03020906 65
    0x100d1103110750740c01070300d0700e000b01d900701c50400d12040c0c041624170006034064103440c10003000358506403030f294401905810a1072001c500e05040a4031041a03241485560f0742d4681220080412103594540403030311050091100c0c06a40c0803c0f003941040e0f920044c1d1000d00302510441c280d0884c05a824003014080c107000241c00c0c0c03030034044c141e081405141d0110200c005101020407000340c83d00a100c0301d22105400ba08880e2020100b8003001c42c041918555600408500028550030324070911529608040311410104a030348808205646040c4501984058181410f00316585d40d5501c0e80d4040030a40102080d00756969640031807a802688510310036a001800c0b1401440c0882c141075a40700300700f1084a058218400414800c5810005d0f00c605030440d4541c200141c3c2424240070062004050f514110b00c103500c01c600c0d00305d020400707060085024030041c00035581080141c04000340f04105510507a407001c2c401030002c443c05040d021030101146000b5070340307403410b100213620ba014200d4546 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 567823255 1250 567822005 567822029
    0x1e020406060503010f0914060f0d0f0f0b0106030b010f0509040b0909061005220c09090c110715050306190b041403060708010303080402090402060c0706031509050702030f07060204 79
    0x45903542d080809141280c65200d4200d8015031601035200940e84000d183c0302003620240085561440c00c0f00314506246005003c03001450420b0f12203d070f0070003c41e5815544c014016401000303000d004d10049016141c141400c0c01164841400205035402d20030b025010080d021404e11029683d5410000c00d8404c010198010341c10f0280510741c44e1201941c0e25200c5021607d030000d00c0d414207480f990440e5040e4840c4d0b00d040100c4040c641c001d40b1100380c200c010010401400310316500c02d031103030f004d000856669a80c101000751140c1da00c1c1c4803003500003250000086901c9144180d2200840e68840701c141da440b208003004041d4042400c407290400d4002c0b2401003008145004440441d000c401411800c4910300d89400740141d40c0f841e005e00001d000510070b17200050260804007003158202c1d00c0a0012071070320424806080c01c0407482d4200e1800a62541012800c542d00d0801da0809080306150401c81c0d03050517070010f50b983c85010070aa041100c042111010705c029541a10002c0580c0c1c2055 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 567824505 1250 567823255 567823259
    0xc030311072108040c120507150f03050f09070b0c010b0a030b09070605031b0c0a02090112050c10050313050c0303040e0a1503051209060c0f0703170c0303041e020406 73
    0x1014a10007038076802e58110800d6103a40040c03072160341441e0007a600010b80180690400401d240d0610440c20103451602c607001d0002480603400c502103403a440c180d6111070720007181d008000c0c1580c0303002e000c52203070742421402d000c0502000706480007229045030040f95290000c0700c425001d03203044582240e108660030400024852560f05035885071800d2401c0e1a40d1075120401a5080c0c0415160720300c00034000003c0180307812404005100035090001140c141c0030247d400500b007407400740c000b010311203040003003c2d040200c00c1020310007064084518211f502601d0000034447d010003840c202d00c0080121801050100501050010301406810740350b68a460b2040c0d1000e81006540740403042d4a40405603c60403070700c01ca12402d6075400000307404e00200c0001d00e03180a8200407009540700f00200f003d00000303082001410f002e010383d00301912800b461820114a50104243e10f10505a810016040d0300304c1e02000b103a0380b0070791005800380310b1401036108102161980e60025003040c904140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 567825755 1250 567824505 567824513
    0xe2503080f03010f090606020c0112090b0c091014030714120901020301140f030d03110903030318010b0a120f060f020d1d0c0a09020c0102070506011410080c0a0c03031107 75
    0x2c5040e220380c45006a03003965511a45400c5500921600d0010b03080040c80b215107600c110000d681c02581c410700841e400310503480e000410341064400300b44c1e00000007400320507824072800c0141d00c84034a042441820400701c07419405840020071487c208861510354044204e14071050321280b21703141ca0b540d4203030319248601e54002e6000b80503e00680d64038030140500c07071600011084030101c010300134204660b040301040c3d001c0d081446014041c03d00c10b0111005984080004d1744c4120100c0722080113142c991030006084842094100e03000700c04204080c0428844500d19030055a1700c003039508555507650a1001c020401ca51881290900005482000304129000220500100a040028603404800d61541c0b255081c0019410104401c2c0801200b4080d5001d03080c031103924800946007840d1940d5040c28910240c0000c9413010301074015900070f0a00428003500729406040c00313030311030805c00c044c010140640105082085407440441e400c06200b504105102e580545000b0345840040c90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 567827005 1250 567825755 567825757
    0xf01020304050616051e1603020a06051308070b0601140301090b0307050307150c08090402070305041a070305160212010c23120106050706060b040b03040203100e2503080f 75
    0x2606a4030782c826640413850700d20201c04022005615901d0782480c01d032100310301000d240030f8014908041d50003808924840c0e100c8500d501c4a03540301e90b02606c1c05181c6403522100320303900601001422a00050b00d070300010308520803201c840b270700326141290720f0350780400480d05410103030310340b880c1c2408c00b000000d81100c42d60005106820101c0503107800c1d540b81c2080c0355480d2802d100b542020042030400c80000c60090001000e03490003001d180c6d1400c5e4900b00424103903804840100c000480000e410040135020550040b640061502c03175a00d48861a00c0040843c000c000002000342404104002150388525405c1d0f1500301d940024071101403908000303007841041000b02c1d603e4281c4040a102003450307080c00c0702c10340f00340e281c0103601907402d16008803101e0300004000c0740d603d0f41c1d401003c101404510041c20007002000b03a12941c1e03284c540f06141c248083c51160f2041641440c00e91080c51078040b414001000c000742c1e00402c146012801201d000700382c0d40c4080d108441c00101a034468500c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 567828255 1250 567827005 567827011
    0x130b131a0406062102093102010203070c15081501440a0c0e18100e011e080313180f06080f010b030d0c02040203180d0f08010803040b09041d0f010203 66
    0x4840c0c6c812940d0708110f800900b40c801100003044a081203800003c0401c29080d41c80060043c0704890801c4515030307c032401c44c4000e4001d01207440c070000e0724201c2962f00c4840203070310001e85400032013010380710303400641700311040040d11113600200d815800449540351078002e1070b0b002240a8841000c2d18094410b0f2000041e5100c00705d560070549090085405001c48000c5110050030080303331809400c101d207540340005410052051026100010680020700e40340e4003070b100d25500401111502083c9441c3c091480d070140c1029041030082058040d80c0c6041e1408603140903141c5401d500d1b041021700f00400c11310840f0320317100c0c0c68080c0114282b400012215808540c40008001125000081540c2d4a0b10070403082c00044c045908440141001d4020b15013103113045891844040001c4025410074204210306400914004c5201103030305d0740500380500410728500511300d41400c01403050319500c2903505030350083d915414111034064045040380b43d8420400140e4080c0980d0150380d038040c5d801070f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 567829505 1250 567828255 567828259
    0x2090301050f06120d1d043914030610030b0303030f090d0816030e030d140105270c0d0609180303050f0c16050304031218050f0105031815130b131a0406062102 70
    0x103459611040f074003270564075994180364081c40d07003150b80308030801c4104440110007204040d242e40003008130761010000780d800f680501c65026614038145100501e4070141007200800c0101c40b10500420071580c0c421030303030702e00901d28000c40e441000520451442c850504044c41261401048900040c1007012032410307154101e0b000082000f65903001c031160b0540070b1203081c0441c5010b0203d51030480c8078008014030341240c1000b00c0d1603540c4a410908440f030980f010b013815601c1c2d0680c2810140c5c54401c144d4040e402940c003586909216240c0d0714507000305032480a92002c80e480e800188602001914000c685c4070402d40018280217000409060701e2016100451007480c4000c12641b809403c0c2c0008460182d50701c50540c1e88901c400108a030548a00c8039503800741119030500c180084240310310486070311000d0803484915203445203284900070710900406104400c0d040006400f8003040c000c80c401012891225212820208018129070748403c581c0001c80742c8540c400b9800301002501c039402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 567830755 1250 567829505 567829601
    0x504261b010207030f050304110301050709051206150126071e020a021324030305090a08071a0a1b060b040f2d02090301050f06120d1d04 60
    0x950140c40c00d0703010b032203401070100c4d40300600d007955203100d000030b158868040c01d160b81080071808040303402c4820940b4001c0c00035906c07110511850030222180c0d24940c035820010021840c01500b420302d80111010314030b04001e0311034100c06803285c070388508010054151600310307468182100094901109034200c058500718441144500328008240300c1a8150050030803181c0b11802c2090300010840d00e540c40010030f12a502c43c508002034040c100c00518881e4071100c1c0d0700d40d049010862004216409041a03610080051100000c0304032200c00c241f01c00070a568403120081001d0341c0680d050021400107000880140c4144581c54000c1d182041040d0b40401541e0741c07925600c2c0a58440c2c240402c00c00f17400d100051062035084182495242d02c1c0d03c401420000060300090a644d0140c554460440394801484072524103a00c0c130050210112000300050300d061364002c1c22150350314070003e503551441d02440e0000d8039240c210426446608a9004441519030000f81c80c2c6180501001041d0075 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 567832005 1250 567830755 567830797
    0xd0e0c01080915010e0414011503020a1703120403091205060406050c0c0a02130f09060603020306060d12030c0e280f080c1203070f050607020c1e04050426 68
    0x31000c904008500c80f100d400c001e4681c00d00d507405201c6100500704032808101032490000390b410030f00c1000051070006109a504a1840c0100001c050f0305410042e844441d45140a0000b03038004120340050401010601030360741c490801f600e840c003440d803102400c040e45902c284108100414038901c15441031404000c607444000704241c240c050249030090f04da12000c2010702601d44000c0c1c99101d0000300c0808106403e007600c0e480c0980b00e01900884089072651f8003030085280038811203601020566401030810a45e803124207000c0303c695442c0c0c0606941c0c4102d2944580b080350348417405c950103010f0017080d5070302100064a4040300da0b109105843c0c142004100c06910b03800d50412a10300760000d00c40c40100104200c070140350a00f04004a2008118441c0001c01701400010502d015030040c4c000c1d4544280d0186c1800c2c0d1022a462251142c12a604583c12050803021005c06007558006526992498006100c01051009501d024041148004e420040c44000c00c800100302c02489074000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 567833255 1250 567832005 567832021
    0xf090408041703031006051b0f101b0c0206160c03150b0d0c090c0219051e0309010c08070303091709011d06040b0f0403081215010e030a020f0102030d0e0c0108 70
    0x1010079117405000720308000080100d540300d4809071a0703203000c502c0540003161581a103140381440e407030100310450f048940c00c41480c0c64617104070040d25414099282c600c00700510f00910900750050003e10808021580095420302011a556030641c003000d4415415224100003240004641d0011006420402e480e000c5003090303442d03550300b150f00c207103803500141c2005038820107860200641000c500ca01d1910030590010312003105d49080c007034009803421001752102d12001406620034501d0550007000118010703640300c41c011842c00d8024444d80c0d140c6001e440e0403405081c0040b40580340e244000080d840070b040580c02040165400d0f200d00180505c25000d0805403c81809100c6d440b4406010401c02c3c03006941c0140b00950030301c0055440c040c0c032507071114040c2d00418041240c0118510402c00c0000d603100d00100d41c0b00342402c0080c4030081c8040043c3d034810580030001d01455006424207026402003081d40c03508a100042404180c07404610380303035130300c1042080b43c0c00075400c1c0000c942c0c29 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 567834505 1250 567833255 567833257
    0x40807021c0f0b060321070b070f02070302040b0d0203010c0905040b04180b0a06030b0c190c02330d050603100e0a0605101d0901050a0e03090904020f090408041703 72
    0x1e42c0910110300c10511601d81003100034006003501d03054011a050103500c2680703551114082001e00d580c107900e494050502288245008102d0424001c480c1c0c1c00c2e040042e00000e107981100d60443d80820b0040d41c0d0030102c0e0324000107441c025010740c2421040d01c4103a402481c0c01c41a1013064a0402c41c480c100001c020613600d01c2c42e402892140710169120100341140c58480e80415070840c08103546a0b0b07a0b46100800070708448052070b081010030814660000038601600741c80b110702d05201040744a4001506076031000715580007030341e424060a650110036445c5540c0c0111140221500c81020041ca007028182c112451880790080000306042e800292142d002e403111200020702c00f282045d620318004017030142c83c40c0101010000c0008508a8000e481c228a000001c41050107041103600306084d60000f80c4540101c9003400350501c98228000f0640b901c00c101120b47c5c0f8015120303070001ca02d0300d60480030080d0304130600500300020302c2424801042140d00303000e0b05c003542c036800300c0c030450320703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 567835755 1250 567834505 567834559
    0x307030504031716030b060c03070b150906090c1810090f1a0f0315100c06180506070e040b030a111302040503070501030e011407020f07080616050c030f0304080702 72
    0x31106070b40c294051594840e80c016041024040c041f5403400b96800c4480e0f2854000400441d40d0702c48a1003081250101e00890350124581601e00d080310b8104a400180c0b0074600810305070210002252141650701c081c0425004c1d41d40151041318080d443e00001882007d07070b800303004503c9a00c0c3ca40002e40200030540b080c2d0190f103902c0303990b0030190300380e080c0c2e101a400609414000c9144d004032341c60b155980b02800420003040d4842c03420f802160b2a1440036035099604040745c0d040480c500c9004543d02051184e4040d000307180c90001002d0b600f000900070a00c404500790503114204403407007046990482c1c400c04003001c4403070810104100951406030f204600805030176401c020310803c090f501a03017041582c640880300124140c844840c2c070200e44141180c05600684c0301c0890f02e900700109010003409885444003421440c9084180d480e0034a0841c0450003c0150000e6800b50021003801641c41c1c200d80030100300c9d0b80703003490f0803c8000780e001504164490300311901c28240c1e07540f0b09100300070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 567837005 1250 567835755 567835771
    0x261306021c08150d0228170a020d080d0908030406051807180f11030a0f1a0a0e0408071b08010b040b090a0906150b1c02030601090b0901090b03070305040317 69
    0x10b40c0200724418094030130481c9004a070441c04e80765450b0b0f07201c4440e90382e5070b01d20400c4105003d0510300e400045007003100c0e0480481d013103400941c001001f6848030340c1c090280075003044c00c05a40340300c0905440018620604003528106002c001d00082103d507800076809594082e0a110308003004441003034443d00141b051008400102c140800c203104ca0742c004c001007190019000460230300c110004050303940300301c40d2159401c0e030354052140c0ea00702c1c0344115001c0304030600140d507040c0c20003000309a80c1c4082e03000e100544a80b8000182c2008203181c12103800c151f000700110f0749245540e003d019515404d0041d086203500713001c46602c1c1800c0a106155a4410080810401d500c965403010020040b4140c00e40d1000d441c0e00960515540c0e10410350000c05041e01055a91610072144080e4596400900c0d46d180e801001400a90307a03010090200b5513442414599440140800590325001c0360703400b202103030070040100320b0380c1501503102510450190318bd00b00c8262040d80c58090381441210124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 567838255 1250 567837005 567837031
    0x12050601090609181b050a08090712020411040b0f0d060e0408030708130501291509062206031a19060f020f010f05040c12261306021c08 60
    0x111041c00313085001080244803000404200c1c08280c40740e0004210200404070b17000041d22a1002c1d40080425403142c03001e07014029450505079050020440c401001c0d1141d500e654429203a101050b04684c01400703079102ca079a8130724074800d85c2401178202c80700c003441a81c58900000756407002c402c1a0382c480c5900404082c51540da050054500e604040d200194401140e40540700082092243c01c3c0c110f1451a511030480860404c080d0107802a0810035010f108156000f10000041e041650740000c0c0855042d900da1051041248507408401214a01114045c5002451076003541c40035074840100420954140201c5080c4080c20444440e10b0185d40a011402c12141c1e11030030100c414503855106848620401422490030343d1904038951402d00ea4139800e200030800614100402454800c00a111000b441e440756504010740240390503040e030010a2244407007140c103042354071030441d040d4400203094942500941d903116a004038407024030f20347c000403642c0740a82941c030310807446030a9103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 567839505 1250 567838255 567838259
    0x51201020a121a100201061401020f03160305070f12090e09070302041802030609010b01030e0715030504020105070b0f09010f0926041815060f020c0d020a0801020a12050601090609 79
    0x1442c020080140e000a1050641c90050300030354400c14815006402076001156050803c0c030000b0500ca034031344080c4c1c159032240e015042c1c0304502000340e0309850450001e503009160b0740c2c01d00360f445200342d070b0004010125900340e220800c000a000d0022a100c542d81c0e036410a0b880740740f030540c00c1130251114005079215005c1007006260030781081d50440d182070703101c40380714260b58040b038540a01a44c4100b10359448118102441d41e052181c50201f4403014024a0301a240c24403582c00014a0b950b26410543c58030f00140c1513900802c111010583c0c821a4000207160080f012581c010095440924035400c0041000d005045800780c2c2e01000c1e00048040c0341d1104501900310354407100090040809014800040c017000b1180700c0c41e041034108480400c45c010b01c6c0c2000030303040d110b84d081002403014501140400541c000b603803041c5244207480c26280798107240000b9401e000c0b20b070311412540d800000d007a00110b5100c2c40750302c0c0b1141000c1e802d10942d280c41d40103655003255030198400042a45a017 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 567840755 1250 567839505 567839537
    0x614010801060e19050411040504110306010f1827050c03060a0b09030a0f03020a050606030109030503061018060e011b0323090a062607020d0e01110313051201020a 72
    0x130845400092031071881e8195910004101520501800d501d55840045020026803d09010f07000483c0464000a451031800300000b814062210742c17030350f0800598101c82c82c006234440141e24080c03c880c481c0801884e4a4054458140401c2400f100000d810310012408580210081d00e0040740c004040c61825400d05d01d11002c1038000c0414103038184a800e941c0004111403801000c003060185c0d0250904041c41c2c24150314000015007003c0c041da151202c0000400d6002051700d40000c021a40c1c00208090414221140380340d8000c40da1780d45030842c40003d8246d401c94220501d92200780c84210094500703102460040414042c040d01007000e06800d251a150014483d404041c070601e641400c0c24098000b0a50000e1150406000300380c030540c445000c24291103810103000000314060003240b8080800a4440307090b0f800b0341003809416103042c0c086038080d468243c2c220400004403500d03801b0005d120380104103584949801804000300042400c0018002c50304180d4443e2504603601100310b503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 567842005 1250 567840755 567840769
    0x30e0d14180607050a050601170c04090f06060605030603070f0311010807141201061704030f0807020a050f07210302150a0b090f06030105060315010512010e0a05010614010801060e 79
    0x114826004581d5114002564602c400340101d140500018400e002082c0b03415498118181c12044c2903c02c410400441c06400046140e007401e0b0984000c56188242c0c40c100307101207401c0310300078019400d000000c0340c2c0d10750040295105080440840d002c061f540e0010300891045400050242c4a5800d09900c03554001c600d0360b81c1140403403604142d92401c5ca003217241b4641001108090980c0b040d001000341c1035200348005141e0400744c111a03500d081c00c2d9070260501d90398128a400340030120000806490080c00801501500242034940c2e0280402d00c643e2102414010704031183c280440d02c21114200074107074285140d042c0c000703040302e040a900c00c0d40c2903540107001c14840350711030801001c0e54460b1103509000c2c0000a40f01c4d0603908004c420103003903680003041c1ea8002c1c0e01c039021014441700f15116450440d0350540e60341c14242c14150045001d40418007080d822b0b88500c0ca480d60030080158070010840b1202005e030724040e4480801101d12000a20461000035540501c9102c6854194 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 567843255 1250 567842005 567842017
    0x1706040602030c070c12120302030903031305010e15160906170415090506060909060c090103020702031908131409010b090d23120306010519111c030e0d14 68
    0x1502c1800c040c03281e07070b0b5000401a00e0700140141c01640005001f008444035406561100b0f40c01c0560071864071403020355a9000041594010000e040c5225050081c294000a46045c0d080c2c01d480800313555502141204800703407a016450f604154013414411700c07072810740f415100140c0e51391158206800540003084c0c0041c105075803191181c00340038020441c5209600c07206100d0400b8100d035250160400a80c058001e10016960300200c0801415020020850f034800000342401a00d0740a18000710b45440c0d40c20803c0d1403a146d401510005000d6440050400044024240914240c542c0c4210800000341c031100d5801040110052200941440282c02ca41c2c0006d8604039035010291585246400001610395060400302070041031302d076042c005001078004080c072043c81c6042040000b0818440c80d10540d509070140e409168040d0302c545100d620000d0000b085495403c1c90455241c02c04009a2040703000c24640301c8181c5110700c010071041c00003000c0307450300d0132821900c43c0c08041a0b4004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 567844505 1250 567843255 567843271
    0xf070c090e060f07140d14070c0305092e021c11060118020705010615030c0c020306041103100609050a050612060a05070e04090606030c0e040b0606180d0b0402040501170604060203 79
    0x800e0000008030701d01c406041c01b017112501c0400c3c011014030074180a0b4102800324800c0000c5003903c41e0229400030200c0c1d44090007a00c0e43c0010340808050800207030b051050303c0b05103241c110310f5981182d40c0098410420b15640c50140c01400b101081910500d00081c02e134140c680103500108684a022920906501d0f22800003510300800303a502d46007141c445070010108100402080885150303d413203420b443c5009400d004002030001d80009580d000000c0005110030001061413801d03441c280018525000358010611400c0d0300e03000c030708010304001c40d01c0100303161920000903810700c0e2145261807203050340000b800359505d03224400d00c050240108144140b028070a000301036a03d8030b100b180ca03500e0088000240203402c0d840c140345050001e030302c203040100740c5034240804a00e8100c10305420000842c1c01030783d0740255040286607140d2403c4c41b00e9202004400b10300500c407141e10001d2160f4821201081181c0e00c5454003208440241c11400303042c2c5c00100000d0016025034015601303c042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 567845755 1250 567844505 567844517
    0x60203060d050616110d1707030213030602091507030c020108040501181b090b10031806090f170a0c0308060a08060108240c0a21020f070c090e060f07 66
    0x81c94684030318205054462001080e0407030000f1218581c4506402080710002016100e0b0345c10711300008000c5003076600c8894140300d00301c0100d05203600950449040c4007040580050b03d50f50303401c0c50b50007500156502401011040e5000c00c510042c50200c0d070078164540c80d00210300905400440751f1070710060040b41e4035075071000744190401c0c00491501c81c181c423038440600c14081ca2030a0b0100d21055a0090021500b4601000701a5444001414207161149000282c01220145800c0404402c80e005011640b4222040f000c3c800c2c40030b041c00030280175040d0200417020756034000e00036119074100c034400143c0d502109c0303000910429900360000b40c000c106441143e2240320550500b00d0130303440817415a0180c0d9440c0031252402e0034001c0c40501d00b05807040349180450340b5034000d2060300c0d9240c003042814500441180c2e0744407920115118000411521841e0b202d50100300e0b68040d52b002d56042c82e8480b0001146042402005101c001d008050071007500d41c2905001e005602401203014450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 567847005 1250 567845755 567845779
    0x318020910080c030703020f13231f061d060d02030703021908010501020304030b0a0f09110a0801020304110d0f06020a0c11240a02070521010c0c0f06020306 69
    0xd50300d10868003507800c41c1400c0300032615040c016460314030405403640c06a000000b013000503985078045007920a0080e140c0d1010300c807003020000020000903520500551b074610b014901c101044030300911914402020030f004204d59032003501001c070680308010005042c861461955400c0385c54014000e100035107118100103130b0b4109903080e604200e0381c0c43c1c0001d602051208800020450802900c542030500790025410940000d40301e10031400041c3c840340b0300d2004100801030907445854001c059000c00c1120710458135010120b0141c04035000e1252407542c90214400d101031080300d00541e884500307602904855024001d01c00090141035400301c100c031341c1e841b000c28480c0c0020700e070101e10b55950710315842c01c3c2e14004106214209001d0701940c44200e0202d400410b0f0840e00c05034200004500ea11000c1d8480100d00e4403500307400c0075401001504811070503034880d140d4501d0181c1038500071301c0016200c204c200d41f41244144040c1018203e4040c00002c210350358021504500094002c1030014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 567848255 1250 567847005 567847009
    0x509060c091507050c09182121010501090f0e0a0b03011413050d030b0108040b15031e0709090201140a092304060608060102030706110403050601030302100608030f0a031802 76
    0x41c00041050f44c5940103040c041d80c00b482c10034000d0340c5c00301c1c042061403c0f003958542400d50361641600c40860410b51041400c82011080060b500710007070305010700003d10420082054100000e00c00d030f44c0801c000f50320104403642d092a403003081d6201c3c04107116070f80c0d030713515420009040110400c9405550703403102821020008d51f42c2501c03c1000e0051080140e40c0b9140c5a0f192005d0f10405104140c60080102a907a074040d6005400c00d40180c500400c1d0380707400d21121444648805c24a5142c480e001d080c0095030b942d150407124031040103080e55007050365900384e9019500038a2000b400174032013813801c0610103a02c90142c4008009880d001c0e91082d01c4500e681040740704e5001c01c0000c5148801d0000442c0342070300641d4064485031034982440c0c03c207040003030354030302556a00900107038451798880440703c1f1030b0050b00d0003103400200b2031721070f940d407820069222030800143c0c89810742081400310b601d0600108540700d404803a1001894078480c51000c600510b150400000c140400d915003038096 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 567849505 1250 567848255 567848257
    0xe06070b010e01150219150e01020301060c02040b03071a0a18030c08061003031b050a08070305030906100f0b160515060f040513032010050106120509060c0915 70
    0x103031004402d11115941028015843d09503140e446100b10750100c452019004035441c41d041c00581c0c060560700c1441015004c00010380306410f5215415880032000203141c2d81e2084017511428000d481c104104001d00d414140c9440481c01541403100b05c84c545030382c80c840c0c540700505400d0384902c2e10a400e5070020a5160301600c056100380c8140058000a201c41402030010b15001558456403e00c45031640d50041c04031540603100e1100c80c12006581c4090000c10b00003d40210703403298840d581d4220301d01d0043c1c00398100382d4400300684555030014500700f142c0e110150070340345090180340e4040d00c0d01c100106a50b00a012001e8415070040503170300014001c0021102c0380c1c0c0322440400292502c501800107000c001c41e5918426410102401591400040c4103030006406140503103801410708824450010308201c2c2c40110f20400065020350b5000f41e20049c140c500650301c4c00021180c11040100744e031401e5500e40d110350048000324451500c02c10081c40002c4002c0c04071200300170310b26000001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 567850755 1250 567849505 567849509
    0x5060f0403051510080c010906050a05040803070b0f09030403031403060a031e03081b192a06060b18041d0a200d0c06080c090604080a03020c010f0f0e06070b01 70
    0x2c0843d180034040260381d034141c1d00001e0000704004010b0340300e924000810000c114070a40c001d10a0001d003c03071819203d4811503000c0c0041100722036a51140d441e04085540d800c4550780100301c000004200e11440200499049036056130300c0c00d22000724010010350070b60001d002c80750b200c0c4210b08004005540b408916030418a00321191600d80c3c96401c02800d02880181150207003846200c0048040d20103009550004401c10660460703051598015248000641c8650400c10345652030790202d03080300e031a20b25005200315814080341c0d0762010641f04c80d014182903000811950109a0350700e042075403000d00c41031070707190071700d011410a124842c1c2414442c0c0c0003607a100900001c400091f4002a0100340071a80603103480c0340320b503102e8a8007a00346007207006402c2042a80700c0440d072109402002c1da4100c44000b441240d66945c3c45048e6556200c01d81c00c118054026400007100315030013032108141c89211600c82c103035200d6202c0d2040f0380f498840d12071503920400601080d00440c00f56011140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 567852005 1250 567850755 567850783
    0x2060c13180f0e0627070b030c0703090501172206110903160b030118240312080f0a0c030e01140907092c010b1e041a030705060f040305 60
    0x402d1540c0402ca0350688025070404215544601e0038813180c00e9851800952140603c00d408841d81c00400480d030400c0e400d54803500c0307900d10101c01e100c2c1904071540101440d920a440300d2156035a60700040d94041020440071064010200c000394200c505502824501407402c0719005c1804035580c2d484003240e440c0c9051002a00002c80c034000d25040c10000070940d841c2445803030004c186041c410500d03d2105004061310580e046040806040454009004a5200d00b1400a552081000e07141e4008070b544010340b080303000306580e40c02481c05141281e0003003041c424000540d60740c04458502915420100320105952aa0640c00916082c4513807400300c14207000c055500c1c2030102c07095241c0300040e04690841c503c1c0180b00408000110050703403024800c035144003000c48032020101c0c0100074800010b074000301490649801c50181000c10302d00a082280c00300212112030544410690201c400680c1540c00b41d1000c0c40301c2e20305074018010a254162166140036140d035290340c1401c4075110744030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 567853255 1250 567852005 567852011
    0xa030905040f060b0d0c0c0507270203130b090307020402030406090303060b0c0a120908151b041a0318030f1804050f0f19020418110a02060c1318 64
    0x40018500740c09031800298480c441808034a0500c1107010540c0314007030144102c00d42d511925450140a550264000f50300102900e030300d5640c855009501d0820300840c082c1c40c5040f004000d441c00903a10071b590081d03082407103240d812001130795400d000250180814034144014028800140d40d03c0c00210701c101c0c4502004105003400d4500a030070b0f12499042b0040c1c1c028240302c1b40d1113810001550620642d00990001200074241006a0b10b240a0f6003080902e8040c24208452180c800c144c101e0145144e4104110140c1e03172110388901a000d180911441d100c011310713151071200e142202840e0458a10309c070500f90031512012961a5902081480381c0440c1c000c20065044403d1010022900c24103580c144007170702d40302e80e00c03030f5010f900103045541007543d04011800c02d1150184c15405980211021940c0c0c035107403040f1125a0750506041042c95003409000e1455002031026551100307503e4000b40441d07100c030881000181c002071408100450403503000513801c18400111405150b000c4400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 567854505 1250 567853255 567853259
    0x7150c0b010801020301031a2205010209030f0c061c0b0d1a220204180804120b0a1505060a050f030c0403110306091b030c0d1109071b120509030a0309 66
    0x15459044050b44228841e9106100400110700c03280d000b5800c0100756890a2215034400d100014281950f803148000e0b180c4d0301e140c410810070705500a05c181d00d0f0840c101d03090b03100c2c021402030b510310b4149942504090288034500660f81c5144280c41c0c038899540c8085240c1099802003400940020429240c0d03004007142d64000082810155410411045070307404810340144901541320401c00700207002c7e0344d1301c400c007582007103004a038941800c0d84086131558640d603039000c3e100102c0710700384140e81803548440406c030403c00f035100d401c50058280c00c0d4500f40a00d00f20410150390461991401400f50410200c0c00700400e1030003d510620411400035200c1d400d504065040242c6016158040d41c043c2051040111000404400500700c1c40803407c410380340040406d080901030409180c0100003072007843b042000241c042c80c0006401c1d503181826540ea240f04039045289081da03124101c84d40580c07000807460542400c00b07250114240903103000e181e0707030200b03241c444410002e07800a8803941003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 567855755 1250 567854505 567854513
    0x2d0d06090309080f0307080703020313090203010512010e0703060b03070914070e10081f0b03090c100f17040305120f0103060b10050d05040f02090406050a051b03061207150c 76
    0x3400281c40d54500600044100fa90300545d6485104c4000d00310440114184041600c200200c03184105000300c5004240c0d942c5890b40d0103034000303004651094001515921542205200720000110114010042d0714074580700c180040011540d003503014015401e0208540a141c010b40c1d80c2c0401a0119200d0ae1030900e4000341a12010314103284900c0b081d1030452102640160b50384d0b0801c4545005d042c03110591008501c182286030300080e0ba0800210800503031004c081a500c101040039101c840d03440070980c0c8100d50015801301030b5004500841c080c00344501c801c1c40422b500c01c0c03090820500d4040c00003840001c0600890f07034107174181035910046c0200b00720780c040c086404106443c40d04c070100040e080601580503101c080780a1070b5480e0b001800340030950307243c00f503d5074014180348a00e0600e824040003900d0111604c01d0700508180120f070343d001410b461181c0e408450b9000e681152540c0c010030004083c08004000d140c4652840451904000f010351100c800040e1146a81002a454 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 567857005 1250 567855755 567855767
    0x2060a0c0509030d030b03032208250303082701052509170c0445150f0501060e120c0904121101060905090115052d0d060903 55
    0x32403102000402e0050490301e4500098203080290b5a003004101215140701182c0396024480da100810202014040b240800075400c4006490451040d901106444c3c07520075803a003c2080c1e82406a907044c6410004a4400e1459a8020f5420040e18509941008514178000c1e03800d4440380b41655610140146803000d10300c400884080c031401c1410201d50403030054625080c5200b40d90310b666000c002c09070010340600818038a0440208200480900d0045072041c0448a1540e081c00301c40c0c88018850745d00100c2c400c1420807682c1240700300b4500181da9140d07495003000e460014019120701c83d4140c0b441203030180c6800707084141c0d18900c15168020400001c44c0080000750915041b48901d2051500c0700468550b0164010407068030100c2204001c903910903504518050035440e101300400c00c0000381d0400ba00440c0041d000348074102800c00880c00e000c2c203d2107007580c00045450714910031007800080310150420a40459030941d103003804205818207410701101c049079238401c62410950001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 567858255 1250 567857005 567857021
    0x209280b10180512100c02031c02070b040f1b080309010f05070203060612150c04030c140f0130020307090e07050301034706041e05060604120302060a 66
    0x1c900b00c001d8211200d00301e9184203840c051280180314440800f40ba0040800943e4414000d00e201046131602d0510000e41740c0d00150700803c0040e02014841e200703940c0d50b0094500058100e5070904080c0c8841d903075186803c100003411903140140c1c0756091001c0c100c80040c1b4004050500245565821180005110488120021051282c1800342e007003d40c400084540c0d01c03910a50b5007801403035110351010b00c0c000304c0d141c0009002403140c04001034001690044c2048a21691500c0c50054940d507401c1c0d03032400481c2440780c0001c0c04141031826503105054000c12515200303000e034002004d28440014070407a10107440c003040e40000500482c103034000b04040003481c5c9510303650400e040c1f00c44000c0080c841840003401040700c0200c20000300044280160480c070b480c45031203d403090201100340ca0524268141c4032500403604c0024000d0070540074655a1114034120559884101c0c0908801800040e000c02e804c030b5020f00011641d0344040920501d52406030300100085c1c5000c1440000381e4800d1307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 567859505 1250 567858255 567858257
    0x81f1d0a03020709180f0f0206091216121e14070f031403030f150316140114180111010f06230a05060904050a0e100e1506010c0209280b10 61
    0x541170b05000b01c1c070400d0040c01000c0d880003074817040d42410300006880c1e0250702211a8008088246111a100e0006100001c0003510010032146540c45001c400c00043c0582e001e0b10004480c181c550007256000756880d125841504046405a03014100703a2800c0e000360000b08011a0100e4103100344600c1401d120038000c05840110301c2c5140240312000e48000c0903203818040d030025102503400b5078003030050109d00722a42e8101258981e44102012084902c030b050b440c0884c074610000c0207103000c880b0444480710318181003840300001c4040112054941d00400e51402c1d50b0b01c5031030185d01590303402054010a0181c000300d01665011035801091140c1230135051107511ba0703039400c00c040c0e12004159101f00200700d9000038640d0342d18040760003500346120040c01c50f010b21841d80040031401d44c0104402042c01c130458a2605c1115000c2c05114001d8070030a01203081021184c00502d458010a0ba00205940350900f801d01c5940010b04e80b50504c2003817480701ca8817000499480d04001507500044801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 567860755 1250 567859505 567859541
    0x5060901050412060608030304080d0b0a050f10030f020c010e1b010206070c1a01062c09160908032709130212010b09180601081f1d0a03020709 63
    0x644400608684142d00c991035140c02081d10002c1800701d00c1d400000209041810b59941749001e18112105502041d05002075500c0e00102100b541801c1c3d0880b4280c0f840038040060301c02c040020415040800c0300303038004042d03e51b80d5923010007116002428202e622080085102900000e40504209054020040c00c440b02084040c00e0ba80c0000c1301e581010751800d103210b00842506000b07900b81e4054101010031038450000040301d5a02042d10810064082e00640c07904000c2c411a11840a106424a5000340c0950100c2c0001040c02822405004942804c110480d610801c00b130554025041d03072104110100c01c000f49644503000d0a10700804111000081454514840b100a501110000c3d00a888030600500100004d511600110350002c003045554507104040c805010040000100280240000000ea104000424420450011810842002425092070000d003000041c0341d850f80c0380c0c0748640c544080140280043c2c5406503000e84101c82c10075a8020550360010350501c4401e203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 567862005 1250 567860755 567860767
    0xa0b0a02060109090c0b0703090e01090605062502091305160501021b060f0f07050d11370b09010c0813030809010902040501080a06271e0c0815010506 66
    0x1034080340c45415a0004800040e075405141070054a165468000d0741c5a0307080043d80c0e106041d0801c46400481c0c0758448036404c1c6a0701c41d01e0380c50584242d4896035130803000910991501c0d402a449048051100d950300e1860840e098000600ca02c009a030820007a800e140403420500005010803220500400f504501c05032030100001e550f04074003a00000070036001880b2500320f6a03400d00b1100400401c250082d29040c0c0120000704a034081c040c1214075200c4c0c00d5201903500e0142c02c4001c0507030001c10280440c1201c048041025100c50008286a006404003200c204180b5140c55402140034810900181c40e1042091f800c61719014180b1083c0401e15041014060400c180c03690001c1d414035100c071494640c0303000f0078054582401300941c020309080003c500c00c040004d007540c1c168010f480900c2080304a141111760303802d150514242824610b03d01c3c601194443c2480d0540228603184030100f0131494544490344507490304036540316049810100b98000501d0701b903a01410341103c116180035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 567863255 1250 567862005 567862007
    0x609040b07080a150807090608070b04050d1502070803062e0302180d111306060503060d02061204110307062f0316050102070b0f0603100b04020702060c06060a0b0a 72
    0x8030020608420884000001400c86109412140c021090103900b010926110522192150b82500038140aa46003660001c1c640400040716000c80e0090f0310781ca8501130410b014007220501c3c015090b10041016120004018510f10003400d0846c064034866480b41000c1c0100000d0041c541a2440e03031007050031003078034004200c00208200d02c3e141e090050751068a158485c102208124a0503031100302009480103008172404050110102251000f15840025070b16130b007295040d0050000080050001540d81d00741104400756041c00284003030b080c040b121041000d1100100c1e42140c4050415518030814201000400054102400d20f0214140c001e1441502c9101e11405171f8010b07034407240302c0c011000c000d000700c0d00882c100c2000d401c0d0340d0b010360406038040c1d805094100e884011120001c1c0c584180020103c0c0640c40c004c0282c03203010394501d44800544807a407850b5a01507400c02c880300c01070755444002e055944030007025240720700c0e040041060403c0190311030100c210b0308010406003d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 567864505 1250 567863255 567863273
    0x1a01091b020d05130306150617070e0d02121f0c0306030b0402040c0e030715080f1e04030e1e041d0706110a0204050a15090e0c040b0f100c0b060904 65
    0xc2d00d06031400b5915281d14140c40744c04194558405460240741c044a05800e851104c070103010b840c41c3e0388a915000b03040c9404100d030860211091000110003140c104442d2420f40d0040c030395076000400102e4400003803107005082c20f002c130044403c030800340003031a05d1000140c00380107005006401c9c00c10a0500c1d64442d02e0242800800080c170a542d141e003181d140394044c2c01c8100d103410015007103034840da8481e603580c10314450414111020841c8040040c140c1860007540c54401c04000c0352a46290000c104030315010354010b8811014800d180e6003104083e118001030b0104001e2510f1040d03219a200700501040720403030240303060150300013400c0c8503200320300041d0801111100c4c600034181403040c41580c0c0c01c0507894030000703600c1400d190601c030102c2e401e500070400d00411690a100c0e450b50301c0350448115a03c09507500c8064002c003541060900d8030380d10151000798058440c1060b198140c002070100f40a2281610100d600e40d40c0d000280030211410640c4030105503400101800d203501c5075050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 567865755 1250 567864505 567864523
    0x31b02010510180212130515061003020711120d120c0504170a0203060f090610180c03060302060c0a12030924150807060e180601030203040206071a01091b02 69
    0x40c0c561140c1100b10b40055044035079200d007000c6400e8040c10b00555080b1b05803804202031343d40303201c2c81c5800600e80380e01d109828007800c00101100089804641c098000e90000c0e0740c155030028000c0038000345a01e0f1811104043c0002d0340c00f42c0540c44e03d9040181141d01d44c034500c400c80314940800d0803003441d044030456055802150000b60720103000768a0529050003043d00a405014100511040100c0184c1490141c10b80c034042d00d07240c2e51000d0301c1c490030820b14412003084400d9119901044200741d0b0114641d61480c2c0341c04a0b409407243c001c18081d50100031b118469034405103183d400c1c4519140c0000c042092442d0900000b91607485002d0385200070548940f031a40107000203801400a540101c120369071080410000c5659980180e403580c08038815800404d07002840d02046150030042d01c9200d500c2d00300040c100e0746031400114001d4200400481c1c02c074200b040010082400621950036160070707076500d05141c0d07042c0003121040d100713004659883e01300d43c5150010026004614100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 567867005 1250 567865755 567865769
    0x6070809030322090c0c02090c250b04050c0303030c04061209060e0a03080106110703140a0f0c090b0109060c020103051b13051c0203120310030c06031b02010510 71
    0x18440e0020000641580308400383d441082d80d400882042c40e41c40500d0460403105064001c118140600a050f01c0d82c81592400030351140c00400000c280e00645400392044158100c00c260240c00b42c014141016503c881003038881204c0c1000308000c01c0b00400424100752815405103055041c03040d118066406503005103000c0c0080c202132151041d0b10784d4480c0b070798a90440414015091400343e00e80d203d446400055000845040001c20304600401511501c13210000090440d5450341c0c5824401da5a500102d451310302402c0d07001030101c2c0030400b034208040c0c00307000744440c03441c03502070340d48100c0e071100140b42e05010384948100701c03154200000c00402502802c02207050303610482688110755540c412411103140104000240c0001d4464a0301903a000b6249600b458543c00d500510601c440000294150f0044440c1e102c404004e41c0070f550440a000c180000140d166500c18007450000d40010300081d42d00c1191540d0a4242036016900240d140000c10080c281082101d4110265014403c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 567868255 1250 567867005 567867007
    0x414030a020a0209100e04060c3501060e0d0f110301140f061804030305190218030c041104030f08190c021908120a0516060b2e0c020402120c19030b060708 68
    0x22011a010b030361000b08414104070070907a4ad01c00080100900f2028445110445804030f0010031705c680aa01d00442100f4010603514075100145e440c002400701043e030807a0303130450f1446030748210b032024003805c000c8680050b00c1f29014a800020025031002c010000f40c0b040129008550b00e0640c0400e045412a07003501e4089a0740c3d642c075250302c0d9511034652080f035180d0710000d202100300c4002c202c80040010700300d080c2d99070f1500e201c003000b044d42c40c0b411021072070a9081108000003074404e40340341030191040e0341e0076040000c5e212460300b03070b00300314910342001c55402c93700c600071031500301082509541c43d040038441d0141003e0341141d84003030142440c0002d0100007840c0380b5450240b42969550030301504c0460092400749000809030501c004442d00900c800c16032241149440e1a2031055008000000715801c000054103c0365030003a82c06c140d8000e6405c024501030b0101840c4114416440c00d804282d6a0b5001280b4460524260003103808151501c40909010b40d905400c8400c96070b0800702c22 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 567869505 1250 567868255 567868271
    0xb07091401030b1f03061701111b0a0804080c040f18020f060702060712030c0f0804020d150207030f021903021c031104080a031409090f0414030a020a0209100e0406 72
    0x110305101c080906000360030600c44c4511242960680040e02038030142030014445900042001c0d09a8501c5200b03450740c014107000b002d6030343d00124a5000440302c0c0342c1c00c442c401e050395244c021165009800210b0f25400c002d00e050194100341c05025128407a01801b0480039104601d42c03900420a0394000740301d02d10303080c894007403556100262000c8a0300100400d0b5164140e103055000c00b00c528010101007402c10355141120350142c400e8440350307040d540700d01e91140c1c0c83c1c0e03003000203184d44010100e843c0c00b4034244204000d0841e1000e002c0c0c1c20b04c252581d1981440700000645042001c0e00414014001011101d0000c0d50218010310311940f810652055076035404000e50181126000c03141800c200846c0001e880200003c04c948900d0207a00c0c0e600b2044c0d42060480fa9510030f500d04c0c59001146c0c1e2000c65441c079201c16503950301c640240c2840203a41201c004c486e085601640341d41005a012071102c805500d412090680c1100c2c18840c8089100e00e080900d00090074010005080eaa6480f001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 567870755 1250 567869505 567869509
    0xf0d020102030409110d0b030606060703080702123013080315101706030a0c0e07020a02060406230309060f0705070506250905150c03070b070c0b07091401030b 70
    0xc1d10b01410203070005010840d91840308500c1a00246c080c403071028144912040141030200f1118010034001e0019845e0212546040d26051805401a8210300c2201250194240800090040c0b240d060208101c04404207007595001c8503041c0301c43c0c260349012001c0c050a18440780703120030071300c0d0310910080e100c0c4da500c2d1005d9469071403006481d030803a0200010b40030b0240d002c00d0311400301031000880706680c0c8924081c03669417072102000422002e51024240003608148440503407004092040722940003042d804155103400a41c40000482c072901a0484908004d418050002d80741d1403515045180c03120820b9500d41c00139054091840b44100403c1e507051044040b180c0d0150072204071a01d40c10800113010615021911081881140c200a0011344d4403502c03480c1d04840c00180340039140c0303481d141380c3d4119511900c000310041c8002c11017500000d2028818078072421403612144424401400d24070300f624001020f03881002841002880004452414610340784028a0002540345010740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 567872005 1250 567870755 567870757
    0x60c0e0105160501150f061202181e030a06020a030c02010e2808040b04060e0628021f020408151b07020402040509130203010c020d0c1518060903080c090f0d02010203 73
    0x41e1001d445c0e184c1c0802050b0300980511250440350f0a9030b440c41c440228220003c00ca0003240b080e1900c40c0241d119508552406881c441c12a0640041d8180704200c10000203180500b00314007101e901da0045100c08002d6018440c074079818440e80000e1210481951403207488241d102c0e4928000c808009242201009150040d40c5407544030103450390781c584441170000740d500b0921032140040c2500c0f00380c0d511402d01c04e007518080500e00f10100e1980c1000040e420b98604003400d032000f188200640e426076102c4400c409410328000100050f40c49060103151814803450107401c0b050328104006200c4040940c0c16a96410040020b0860700c034403540c80050040d1140d070b4015507103e140306051010050080c500717280e94910840007000510036030f040c16615002e8414100011600105014020500000721599260304d000400210b00d6040400e0070228a1201400d840c0b07140c1e240c00c407000b01030304030b4007182c1c200e009800100e00b807554000001d00d401d8150001c035805069506c01140c00c59000308 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 567873255 1250 567872005 567872021
    0x303051c090f150f06031101080a0e030d06051903030203040e04080d241502122d040602010609050c040312020106230423040b071713060c0e0105160501 67
    0x91504010a030701803c040c0341e010303100031480749094500f010a0800c0707040f03845014112580302c29040f42a03c5018015240c0c0c2c4401040c040c002500c42c0401c840a05003840100010303909002d00103421420f01c02405201c0741220a404070821158000b8404603400209075001c4407440f0580d216240d5603403a0101542c01852500600e00d42092400407807030074400001e0390610001c0c1c0c16000b003695038000d18000960115913174030268000d034080c8008500380c10b00030860010bc852244a006604d100c03a8a10b0300c2800c41e19411190002c10b041c08540c1d82800780b14020403074507500b4807450800010a5450380701c0d901c0024800d82c0040c1e012111a8000c3d00b20b000206085032400c103240c28000e0340c0703401403151805110300c078070715000541841d88402c1018803081d8080c1c4490340c0040c0c1d00d507501d505a214000c4e00500520075541e880c0d040d001e1140da1500d12030f60b040c503601d40c1c000b030051909909650501001200b8450f000f080d0b1107490768030a09440c1c1c10902c5943c1e49162004d60708120303004000807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 567874505 1250 567873255 567873263
    0x230f04031403011410021209040908120114011418130e100507030c02060412030216080d27170a050408011104050108060a0b070209060a120b090c0105040303051c09 72
    0x2c0000241c8002d407800c12481544140c46407250b031804201c040341c84041c030b6100043d1201003808815554145a888101d01c10701c40c540c0c076482c003080c98480d68415242640b11086074090924440e0306541c2c08080c1628044a0301442800d00d2421030501c9140b20000c11043c0c001e0000f00b441042034409600b0800d000f000020560f51101e04101844c000b07004111f81c0c80001c81c1c20b00c07042c00d0110f440040c0c490f1185800000070584882c040354120040d41c00440f00c080c0141152140c1d101141a250080c003c1c0c208000000807954030034071034985212059212074070820906044840441d1000f40202c6100000250456441401500c296203601554001c214290f1170200d440c103800130307100003c0c8240c507000d0322860340507030707895040150f5600d290003213044003003040c024200182040403009400480c018619060580c5544452143d91100001a100f036014002803085c00d40701131040c80b00c000c6007840c0c190700d480e0550700c2c0a8214802c4031952904031801680d4400c03a00d40b5544603400840d44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 567875755 1250 567874505 567874507
    0x702010507120903140a050319090b03130201080121060908210f0a0c210f050705070c0608090d0c05070e090a030206010602010204050f0f01090509160201230f040314 73
    0x5a80c000f031911659002c22180003032030710b20b020640702c0c0005081c10541c2c0c0c4a80203601d81200090403415a021102d00d41c0140906c82c1c00c007041e42503948000d103100b00030409080c0b03080142c46c0001020f421043e0301041078201b20702d2a0717140c1c40c1c07242030f40da100c02034011501090014103403811350380740d100f00500d2100c1c0024480200180d001025040f40c09452011540245034580000d448120781d101e41103078022841c2e01d100400c82d510703083c295031a0500b00702c2c1e00099008150240c20107491003107403000001000080d64200304101d40780487c0250845281c80885072400044056a03800f4000381081400b4000e0001e40800201b0851078019100c041e107591480c4c14a0342007142c2e90795031b4103400c070013500640001065440c414070a0300d0072600c005200b03a40290707050090001021704862072504014082d0320206190705c4c0c42c1d0360780b40a095000c2d290030360f00508190080c2120800c070300314005a044088400c4d1044440d114164011a407d80381000f40c0d20745240646001074550426580000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 567877005 1250 567875755 567875783
    0x403030e0f041d010b0306090601030f050a0c15020d0216050103180507062d0507140c03060903190c08041505040e09100c08040b041e0203100b0307060c0b0c0702010507 74
    0x3074a003c886158150500203201d48280c0c03004050f1148001c545142260384140010004102c2812400050032f008405494101009840700d005441080e0400341c00510b0781c099907541580d04002c00904e41b101440a4880c103500190702400700c04561050504050303c0f50054042144100005d20f003040d8028125140c441d9140e01c081d2103042090401485244000000b03045400ca054424094402c1543e8541c0381007004d50740e110b0035024a5a000d030b600d209040c40480240c404221042c000d03106100115100ca01441040402110b0011180104204080c050300021846400d0303030b0a6410784185440210207420003101c8034040ea0b4400c4241c3c00d13103201880514103010403117a080101031a414402901c6405040c0e9240d003080d0750042a222101e4006804103078103010b00104030468030031402c901d115540009103040c0c010480110304ca540e641c8196114981000040010709440c2003015601c00b9035116892608402031052106000001d950340c110ba114004407202035910101d4043c106c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 567878255 1250 567877005 567877031
    0x3020913021918060207060c11030a0506010905090f0307081b060109020d06050d020d03030905010e07060302190207030f1103030906030c0702010801350a0c180c140403030e0f04 78
    0x21951802c5040440d060102e40a1410250062981510002d070001d200603407402d0b00403540140e0f00001030b2401000d8405c9455550340070310400442174000c500505c1c02d0f50500409804a89015000e04255402403403101d0400b02c01105407150150010f03401074886008504826510381100004c02060052000100301c03502194080e00351944643c07002c0008a803a1010300401c403881e10b00183d4411024000400001c1c404d4001c004011b20400011804161800d81039140c003800c5d82104000c2600840c01541d4076010361000c8107008018401001500d107036403541c581140003c480902241da1024086400c0d0310b0030801c9586c90140540300c1a070324500038440850741c0d0000f0904030700086a00c030001800b40e420741b003040c944108400710a50034032041c690803030740800b010380806613500445520001103608070f40d08c5001422051205404180041c1c8000102d40744d0460000520400001090b40c0340840e40564007681e23890f00704180103600c8200091384d4072000c01106580a810300034003800c25 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 567879505 1250 567878255 567878287
    0x809070801020c06091005071209150e0f0f010507080705030a060e01060f080a2007020d060207050c01110a0308070e0d02130e10021810050f0a0c0b07110601060302091302 75
    0x50020171054440500c48040c80303c05803001030700d00800055042e02802001c0a190340301d200c0c0548640c2c6a4002018140038190a40354203010155980c0c20600c00c591201c02d05000c00000c6410381c400810091405290140040902a080200304000440064404145940030601920700c6d24501c0f9010340e51054000c109602d03401c00040090030050208040200601614091141548101175140f107441c4400c403040d00075041c160f038031424159440e00454158402851b100e03000e00041e00144c2c881200144c07030126000c03c01002544035040a60100b94400310161300301000b840c001c000001c2c0d140000c0c1151640d040c0c060360024420701e15400e80c146030350003070200a4414040c0e070300040e0001c04c4801240640e9403442809402d60f0300d00c2c0010303d00a12201450340480c10f02900f80004120800741071307000b20450b28003041d5105103e0050151189030a9802201c501e401c0c0100302c0e2809107283c0b120418030800703050540100d5003011955810864403081c403404030045450f00038282503d206 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 567880755 1250 567879505 567879511
    0x106050c071e0614031506130915090e1f09020f120f0105060d020604141c0c0509060d020303070b0603120f040e010b040503071406070803010e0a1b0f0809070801020c06 74
    0x100704c080708014051010401502d00c980100203105020203000418080e41c0c0c0d1021040d103844074510800810708103218840c44410746160329200b0819400d000741201124120580300780585d0185e00081e4042e8054510f45d0345c0100c0e8140c0204044000d4408200f800c681143c1c110b500c50341a800a60011000054504007105d81340001d02c20354407404240314035480012b0b00030703400640800c000d20802c07583c10000d10900c030300546003010302e910030b0626245050030701208580d07002d4440c03000c00c041e00c3c0800050b43c01800442c0c1a201084680d80060340c0c901c160000280920142400522141d60501078904080009074090366101c400c0011601540d1041c020429440808c030000310fa0f60580d0815101650700c0680103040f05410038511190b03000c0d00c5150769078410801c001302e100003102d01000d58002c2040102059aa04102e0a130b4001d0b00e020500e10541e1103207500b050700308568090000b07401c080240c00d00c0d00081c1c40380d156590509256803c1003c1070341c0006a1011254000254644 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 567882005 1250 567880755 567880757
    0x1c060207060911040b0915040515030f030d20041401030b090703060305070e0412050309010b04020706020415080c27040e060103170301060f030e030c0604062708030106050c071e06 79
    0x4240b0007a01c080201b004010b4944580034a030700e070401c0515041c19032101d5046500800c500001d000318400003450141c0d505140c50a9810108a10ba003080081c0180e41c00c40b0115500005110300f90242c41c05c20780624412130300d80317400180f0086582d900070b0303200001c40500504180054a00186d02030041c1a040c441102c3c1c83c400c5080001303820091503410f82c011540f164020460506d440f00440d0b0641024245400315560341c84145102d65440c402130010521502015032558900014a8000766064122005000c520801c00c1030b10116039080b151104502c0c0038210a645030102c400c5480c0f105070304800e800c14070f0a6915071054200040e030f9070403a131080303144510000408003080e8142c0420702c07a0101141240e4402c040642c0650441c01c0b000306507108490410301020a01850f2030030a80c0d040c1c0f6800d50725002540c00094448030014a0b00880010542d032102694512110f48014460f48013040800709509400c16018403500700203140c00d940250b00c00072500802d410020083c4a040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 567883255 1250 567882005 567882011
    0x41409070608060607020d0201090f090f0f0203060a0e27060108070510082725050d02060702040510170625021e030d29010503061c06020706091104 65
    0x10300610440b6402d1207154060009401c03e0400d81c02d201c20060001c40403414044409000300e12000c600404d4401400b0341140030030803d110702c0404040b030f89000d0150310440d004108018468440250140c2264030b44002c5444035540d07001078031026490440c4520b090041c2281f002c9042034001001810780300c8450540392540daa40c070070081c0540030940890301040849000a0044d154444e4440d41080521a441019180c0d82042810f02444881c0c0400142009035158080c43c100003814000d064103a45030704035400c8580000f0500c3c094490001d20481d26800014000006012050000d02481c00f01540344011071f040c80b511008122580030300b40500440c14000740340341ca0009100382190707401a12880d11004040035540d105032014081074801003181103551f401608c68005449242c5169441d5868001c001040409105100c10b04104052091100729954040c2c4c4207100b9540c034126a610880c54603103480070380a581030240c1075503c2d1070880b40c1400740810980c10400000c440c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 567884505 1250 567883255 567883259
    0x3061e0605180a0902060a020d020106060807090b090a0801060b0301060e010302040f09180210020f070b18120a05060106030c180e13030203070506010b21010b0f1804140907 76
    0x248046450034070540703a204541c0c0e45032201c03800011080d50f4004840c41c902054000c501d07004034100e80e00c00304034103005074800c510b04801c03140e084c030440c0c0242256181141b418102070301c000b040f1080d07902030b2124492002544040d9a5140203464006040003c000c0c420303543d0344e4803a03040340d400034480d10011580114400301d00798131034804c980651340741c80c0c4066811030400721000c0c028543c200d28081d8925a09a5400150380c8079102c44a900d5600d50045c21000c14000076141400301e1648401102c010500c8070902c501d60414142901c1281900d04100b6030f228902d842d8a0007142041c050050701802d400410110383c15000350004205944640b041205903040580306003586105050300c10300d07220081400e04d10318102d4040d06600910440741030404d5a00e41c5802d2485c203174000f2124180000b001c03c01040c4c140c4c440002074030340d40c85d842151340c504103c00310b851103000c1e91003c040c5800540a05401400e480d00b004112010f070041000035450004817160f200240c5141245100c2c0e5000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 567885755 1250 567884505 567884561
    0x106080103200d0b2a0301060f020f0c1009090f06050a06180b0a0311040e1e13110a03060c030c031802130e070b03160306053c06040306 60
    0x25002c0318040c040c140d070710400b4140c3c0301d2002820b40500b0016820010160384202010a8020080c05815040145030f803945483c0014190707031102e8400400b51b41208941e8100e0740b0000c1a0524043c0f0103441c00c205000620b01c1c200d400c1880b58200001440c40e1540d1180e407103820750301c05401e85009136994401d00d9125107080d6208100b501c3d0101d04030702c3d8507070140849040c410242c0007040e00c170304001c030b03143d25a101c4266051300980c102312404000302080210399442c4039481d00810503000c000181605114007480f40361060014094815004071840342c08503103a81941ca401950003c40401141902082c0280075211000c000c0d80000e09100b543c00840708002c1014100b00e60040a01400c5504604050041d009400001c021806100000506200840000c40c0704d0568505607016120300070340060200c3d1050b81199016030900c00300c2c1590700200a50351070b66400c4040845030f84940007058007140f804443c180503041280458008100b14058001a0a0944025040c1e1a09000d200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 567887005 1250 567885755 567885803
    0xa030605100801080d1202040906080c031b100f0e0418020f010305010b0d0b0409330902090a02031305070605070203060c0a02031b100203100302090a0606120e01090b0106080103 78
    0x812100e504800800b4014500840c040119002c07081d0001d0302302039440c850760044032403c0c0e000105076000304100700707840d19060201c000c08201d02c0000c0202d65003039030046001c205060003641c0c20311664680b4414158014040e09043ca41d00400510165441c0c1e00240e62882239154100c2c061801034803080030941c028026141640c403105030b600e0030044684803d0015101c102d9203103401030303560b1203002c5c0850100b0000765902020400c4240c004001503000032072540e41511400781c014070300441100182d981a08440e0864168080507880b61034400d05200d080c00c660000405030300c2740084c0001e81035041300203040300c18000c900741c41b010380e50301041c286c1c503224060f160001a001002484540311100c0c0d402440c40d10f464040f14600c103c0000316604070390003503070340c80c0000e903a299040085240001c0c1d0144d00190401c8188282880d040740984100030a803c0b03085048d8882011805003a42580100c1c01c0f04d8200004000e1540d403840041c3c6141001e01007174641100d441455121115200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 567888255 1250 567887005 567887009
    0x70b09150a2a3c020c1e090609060f0a03050c130e0705011b06050c0318030c0703060b0f0a17160e012c040c14180c07020a030203030a030605100801 65
    0x1d143d82c4168106242c1660b428480704800711241c402111615100045a10556144410540081040a000302c007003040030a0000004050003408000c41079045e2502c00020746c01040c207461003c1d41e600c42c0e40006120480c42c9042640000c3c0e000000024004001202d182c5e202082d6442800001d00070013000640d4101800350715903a0202c80200055403290070b84e50540240071072003049040c1155100800e4810995118081880100520039091040c49244460442140c004d5141c5004000000d848191922000d049140c0d100d980301034546545103ea030021030001c08604150351107044c0c2120103103403250303050000c0c070031000324543c2c0d00c0b0780b20b9044c4181e070b201011510090f880c007d0740b40c0644c4040050044400c0880b0b2a603020705444581180c011071180e074403d440107080c176180c05142d43e907a04d01184900c40d2035085065000400266a80084181c081c503995038a0314000300e1043c0300c3d6a88029098400050001c1c241d0380c0c541e1005c8140d4408481d964402c030b0180500712034050080c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 567889505 1250 567888255 567888257
    0x20408010e010929061003021b060103170a020607111002070305070605010905060a140d060c0e0103051005060406050c0114010e16020a08030f1f0b0705100e03070b09150a2a 76
    0x20030040341c09854071500c03d0f09006e040746005442c205140749000e0b01e509508441030307002c3e80000c005104100c10b03401142603e01c0302d10310b8242002c82e00c00d030003542c41002418034414851040c1c0301c0f000070103042c440f40041000b900270a550301e201c540380c020070030b520100c4191042407401c800801c80704410f0003481d006900041402805c5420110040c200c4a0b8004002d5071042d001c45100002507000e019014030100315840f10b40502440c0000501a82e400903c049451001e00400b888281c0d0f442d801d50341900c08a191a6032208059582c2c1030051001d400030560a021600c00001d90500382c0b0840b134440c3e801b10480442c10704252134181da0303034140c52000410181050000907142d0360045100e81e4401074520307940070250200440300e042e6480582003043e40d0300c00052140b0910004020000b4400046901004942d416036076094484c00717250001481410f927000403981e01d01c03042103c103208102d044010369440c1021250030700201050250140c0740349214207080000000700c00810300c9001c3c1303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 567890755 1250 567889505 567889583
    0x601080d02060c160c0603020306040b042a05040306050c03190b0f0f040b0901032009010e010504110f040b0703031415060a03020c0a080408070e0115080703020408010e0109 76
    0x40700f0ba044001e4019803841c07042800702030980408035a076105854000c180a03140140c2e42d040607814032007614070201d2110700032805c1102d40000f145142030801c8441010311940b0b0211103281104907490311071030344003418080c03d00c010300000b074410314015401602e40c0c0420070b01c1d00d48260028007da883c07148120303500800c80c000118041c201200c503801d09850003000000d401c02e10200050807000c082e001074904483d00d290210741c01c4076400451450f4901101c82c00d09035803400850040c43e00701401528000c0341c81d551412040c214000c10b44001c0c00c40441e1481e242d030340320ac4040b8a1070700800c81c01e400003401c02c1d405003242c50020050398024003140c1106a0ad044160050020544c8103142e85000c140d400c002d04104c90600b80104035502c0d20500255644900c2d1108451410000307822040700c00180c0d400401242013030ba15481c01c466803d0404900d00d0f541d246064000380519882243d0300d500348212510308107c19404160f83c41c0c8a04840200031a40942c10f1888002c03c005001d03003028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 567892005 1250 567890755 567890761
    0xa0302070e0c0f070302060f060612220f0b061503011811040503070e0402030c2209110d1a0903031003060908130e07020609160603150e180601080d0206 67
    0x60551071150340b024418031110700d00440142d4000740d581c40383d0402e5006030040000d00000d00c5600a24940108040f40c0311414000a07640b00c401035540a801c00c807d68900100303d00f02150803103501f0500d5504010700c9403804050742080b8030a00e8040301c00e039120710784002c5c5168040032100140d81c1a148a1600700381c1c0c0c0f0f0007013040e40005064110165094000078440000e859404000805c0644260107040505041c20301c149450300c007554006910600c40980c2410740d007103e82c11002505040346401081c041424240040000f148111142d0086099032044040c070403d01254007100b641486000b00a0b5141980142c41c0d0200fa280b107440458440e07000c202141c4560449900315000700c5095103411000240301c2c1c41c03240903602c03524803000f00404100d402c2e5018890b40340d109542c200904082111040745c05004030f446d024260605903140841d000c15801c01114401500600b0030001c0d8500f040314400026080700f0460941030301c2920008500444003007141406401c245c0c000b4100381e2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 567893255 1250 567892005 567892019
    0x307060f05151903152003090a3818010912030c090b0a021501120b06090703020702030109030e030d1103070b22031d0105030f0106110312010e180a030207 68
    0x500d0783c0380a4840c0848080040003140010a0240030b820a0340381c0003500751111010304038280c50704842400c072103000b0300400c10805000310328a051541d120a06001d0500262100c03490100b98144510040340e501c868021107500b030212460040c1030401e502141d03c06100181401e0361042c030070091888806039005000d06000703030001c84890f503543c100100100d0300e60300c0707050480d00700d50700311001607111046e0030282003810500240541950f8200000d81101519088a607000c041c1060f401003a02d4800241c420740700350b0659402c9a4000c3c000d10a492032418010a40c80d83d01c25000d10901410203508078031406402521a500c2c1c0702000340d818818640c03501500c051000b07001402c40c0c0308030002e01460308480d00801740001d12239201c804124180b0750000708641c000740185e0b81403000c100305201e28031000d401c60a045030f00302d20303001707252450440c4900e04600401e10100144c3c18081c001140c83e200800007a442411101d8514007100e803d504101e079180f10f1500c0181c0942c0200c1420310546c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 567894505 1250 567893255 567893269
    0x105100c030807170c09010f080c251203060503071d04140c0d0b1b03040317042301090b1b180114031602100605060a0813140307060f0515 61
    0xd169041102d0308108504c40c0004020003100c002c6070080d1300140c0b2100b01d607044960011041854949460385240c20344100c1e029100300f0030030b00e000b00900100324800300f1039a0707000e4000340c1e4040004443e080b1248405000307003056008261182c003410f00085210007890310f5203404040d2a0064031070355201c51720b03a00c011000000c0c440c64140948001c144140c0c4820029001d50f9201d1a0107a00b1890004400a003e11503042080c1141204000740000b00b83d112404a0b0010403441c45052651140c1c60000c0f100400d072544c1207032600c440340c502d0350300420640c0b000300b10b68080e80c11511b00d079451003034100029010390b6070742e000e5031000d1004107401c5c159000d141213a0351041c10885000f0001c961207038100e800c11034183c12803904000011024960600024030f10614030001401b006080c07200081d1a405240803400c10880c800c80006c1490300003180c16913800307030030041c04000c1011080c40e080e1a544602000d945090400302c4c0700102200318480c140c490142e00b100c005003905002c00300022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 567895755 1250 567894505 567894511
    0xc1504080702030d0f020606090c04061d120a0b10030f1211060c03011d0402010f0f0318030201020a0f14090f010c02090115020c06070816020315010308030f0105100c0308 75
    0x500300c090080000589003000b0341c010203c00e03900c440015030356036103009280100003400d180c00792182006001c000e196000070780b819103031075040510f40071113000a8405624050212907901c582702100c41303a50114003056001103d4000c28810300301c0c0d40d40c40d50302a200d0209100003403c041c1c4050000d4042941c440d54022194100d2401c0740e90400d81c1d00e46940341c08420780308410f010b80c00000420070071480e0700011103100c1804c0c1114040f403620381c001902580c407516001c1c0038881c103d01018042480307075000120543c14401c400800ca403650400a000750070058a0380c0c0880c0f2250030038950103000741580d0f4121540401c10307525102104013032040d192000107043d414044400c0c2c2d2000140c2d92050854060030007045505050000c1c0ca00c000e28041b1140d001c54001c010410141021503400401c60707460100c0c038016a180b1981ca4808a0320b000101e40384181090500d00000c000c004400c001540101643c03000c81c0116600c2d0310130410300040c541401c4c4080394076110030800281c000c2c040030758 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 567897005 1250 567895755 567895763
    0x1903060510050a17044d03010b0603010308040608070912030f05071e2307031e0f06020408010507030e1b01111902030616080c0c030f041e0b0c1504 65
    0xc40004030103014481c805450458440c1490f40d03080002c000583d03034600d19a50104950920346440f0781d2160f80081c03190020311404451b200381151280c03425044200c40f000080d0500350b81f5a0749042c100b400760042d000d490700254001000c02c010134441da842ca01030b01c1a411000d0700307a605943d4141c5113040c5054060b8144034084c0301c48404100a0401c0c18251142e034002640000720601e031071500030a00003440c018541a01100800240001812005999200a001804030407003122404c01c207480080040624a103040340303c041010716006030040b90034100c028445902c030395506034191800080c283e42d196004c0c0001d000d80351306c02c10b0f00750300100e01810407620801d03500c86014103040c0504002415510078051460442c10100603032130380403808000400d007c00120313900601d164005004800348a40c04210342541d01c4050049480310f5040000f60f943e560703502c0b02c0b142030304042c0c80040640903292038070009a18011004940b4080c480c4005801c903040365404541c00864007074801d075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 567898255 1250 567897005 567897017
    0x907120510090f0c061b35180f090703020a110d1713020f010c03030f1a09070908030f070f0206070f15020c280209010b1903060510050a 60
    0x10486840038468200b11a005003016035540440e400c3ca222001e40a520080070000c2c00c89542d12564000086070083c10341c0800701c0e0007018420f2180703401c03503246114848101c03014100c1c80348800d00040018000b45102010008050242e40c2c104694a5080c0900782d030042c05e0080094070440c030039401405040c110f405c089400b4800186c3c1c107490461405888808a181c07403c0c001440341034040b5043d804804815165440c40950f404540203080007403045050100c002c0d200e908142c02600a244c034400c60340d60800c04510026181e0452040309203606025801a0700401e0940d1320408030101983d280000542c64020900c14201c2103a1001c80c05a61701080381002c400160784800040500724018006901c034a055810103000005800c00d855981e140b0401000c202c2e60320103d8402d0b18058811860000400150030f6030101e18410301c0b00035445903420b0000b04540c0400342c0a0540c0381c0c070113850114000c00300c4800360100c130028021554000c8900c4c188182c607900c00e000608003055035151003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 567899505 1250 567898255 567898273
    0x2090d0b090106080708011109040c050d0218040f0506010c110105040f1706072102030c0c01020723011505090a02040f090504061104060e040e21120f09071205 70
    0x400e9080039110003405946414080041d54400c00c03c5c070000d800a40020084600d0300d00c1d49102c01d1003281c507458080e40e207501c4c24502880c011019916052507440c0d056540d110084800060b00401102c01072142d0300d0504600c00300413180c4a11840b034041038403840b140c8141920707070018095540c401581000b404020225241c8941e41080c0c0c001d02900d5906031b100480030351540e05180c0000d03c1c402c1041040d42140102c141e240707002c83c0d000c0c0d0304010f0060f50394590192441c00391284241a40c2c5a45c0009542000c001c500d040451100580020003044003403c000c44600740d82c000360340c01c2c0041138082014880b903d1314506c903c0d00855010001031030160b031244c090702107010740c2d405001820b030381e6010002408440c0c0118182d0500d040b51052138a801c02c000034003403a02e034140741c60107141d4075041d0b610303117410800618005110f01005080000300c0d00240300103903070116900c0740c1d0106084020410480c15034040310700807007030103000e8202c080c2803c2c0780724810001a142a90f4038030602507d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 567900755 1250 567899505 567899513
    0xa110405040e010e07060206100b0307020705040608031c0e100203090c0306430509010909061806050d0309122609182e0801020a030b030609030a021002090d 69
    0x9060704140510380045141c03240d4001031403c0117526032042003590841820401143c0c0c204809500783c075000f068640d12512801c004919240c2a078103c0c3c2d800920700a0701058003040000541030801098858040d203030704540110007035030700d03015003030308070f07502c040c0380182500710603005590f12401200c22600200d03842d00c0000c1c03510070709441110142c40c4011400d0494000d116620700c8410300e40750304441c40041201852800c03803042d440d200800c140428214440e07846007000ca401400560f00a01c1074944800c3d50284580d0070481c0c030b141e921f02d042c40010b0a0300703024900b00c840642540711103440b24500040c8000c1100510b5003102c0070149414540744a10300c183ca050b0800014140c13954075114840140685625000c90285850a4040c02c1144000003082103990b01d01c801039045003004003811524200000c542c00c2a68103500100d08e540241c0c1d03260340000101c40e02142101c0c06625002011a101d20801d80060016041601081c43e40325494008000d120740203403102d402c4a1260b16 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 567902005 1250 567900755 567900761
    0x110111190b0f1b04060327030504080708190303050612010527010e061620010e01110f040509060a0902070302011409120910140301170d050f030a11040504 68
    0x1c40320145010140180460280701c11035002c8103a00110001c1065007480a065010314400c500802d40ca4140850039040d24005429810600300d5440001c140e0528000d0940e8101e80500502340c890400000745022000807581c2d110a150340c09404800c0564400314050400145915004045880e44ca15805001d1040e180b08600426070300124040441c80020400381e0f01e0b84c48210703681040c00511100300013160f21f940219000952403000f040f15041900c0f840180d05a41044039000d00c004802c0786019000540c009203070340300812007801d044500d00500d00420781e80c08200d920900c002d002e00d08207a000c0503084940200800c04007941d8683d0306003642e000e0081240181d460700034585810001e07944a5810848610203800d020090300c04100003030203000b01640c40748004d4400b40702807a02660389051408800c403402541c0750b0310b074591604000e0b0402100300042c40340151140030140700e0010740e040e540002c0001032550301c52084c41806000c1281d20039291740400c06c8000b9469442c1d00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 567903255 1250 567902005 567902053
    0x302040506190b0d111c0b0114030720030403060504172b091e0201200c04020306180f16051602041d030a030e07050616080c0a020a030804170703110111 67
    0x5406c00f4801c042c1d00080b05c040c0c03102c112a032410701c0f0b180703182c000f0080c81000549520840e03515002c1c03140d03d41840089000308a0590418060100080210038400c180d00403030701c01c900038a8401c2c040003001d0f000300720301d2080d5046441c0c002c00c12490000c00c2000b01240103c5000342110100e08402140c840071620708110b00001d1590102004190442d6008510700c0c3c010b00c06805c100d00190442480d407511a900c10110a21482e4000002031031035841401c48a502c4041c40550b14862918800c516040302045c1c5600841c1151046a040058410011607084172294500400001a241d090201608a00a644038026030300700b10707003600b030404101501151001d5640421640e0704500314508010300e94020900481c401c00480d42404101c0281000050b4014401542e07403400001a5013072290100e0020b6221344000400420300904c100540103541108241510610041c948236a40340203502c0010036003010740f40e501c85250700507041c480c601940c08003a24002d044412841000000b44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 567904505 1250 567903255 567903277
    0x15020d110a05011e0b010f0e0607240222140d080c0105090c0a050405010e04020d0203120c150f06012f01060b0d0501060c081210031b0302040506190b0d11 68
    0x56403450704c1500d040d01607910228020308040c0c1c03111942000080c005000740030118062040080c0303007820400190811000000d000c0d04040140c046078142d100654808a2007610850550f4400c4010b220300b8401f82d0222400300d0a65181d80010405010140e602c0c01420b4449901c00d0103401c0b002c090a0040c0d500c503c1c100400b50880391044c1c81085070500454220074012890040184011544c4843d01d170340054044a150048001d0b520010307103040341c041d50f05850b0300e10104079540070001c00600040139591810300032000b560703240d070b141201a070115227131800141c490f0f207603050b51165410340c904421400e104410a90100d000d40a0964095a0040040e2880014100084000e610419000d00741514203402d0071045d584403881c41d401810780340700c0400000004a00d040c00c40401041c015030348107000d10160800b191181400035441e201c00d0740600c0c1040002001440d01d100324440351382c0008821000141003001c00313038440d0000500c81c0e00e9566036107400110b1060850291500d4040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 567905755 1250 567904505 567904541
    0x504111806031e0c0409020f13061409060d03080a1d0c10020102041212031b05030f0702010501082802030723090103021c0302070306060801140115020d110a0501 71
    0x40482031501c0c09602a00c0e00d0020140040110b20f203e00204554920407011103010400010300d00008114000d0001c0850307007c92082c1b2040f003400d0750350f080340c801c44107003041000d2011502e0050044d041c0c001c8654680c02004000b90b48002401085840c0c0c01002d078401c0060034017200005404080074a6a043c0b60f07941c070404a80c1c6842c07405170b0b0140e82c42e03069480290f06051030101c81c0040740c1c00b80403006003403400c808103445449100c1e070322805225074000221041841142405401c0b0b50050302d200d078404c1d41c2c100c0041d41c15801401114101c039040c0700201142100070040180c1e2032440000e1040750b25506401c1000350364200200406401d000c920054804012180d07400080c28840034203001e59407020041025a403544120b1145904130480b0307601c4041c1518040381088a6600001c01c01c0c1c0c0340110205102d103056000c0c0c011f00311050240b80c007590b21402d2600b07100f0f00c0d05801c6401030f40a4503992007044e21070704501c00007100c1d078012a0b042070b80a40d5180e0030f43d46c5881c1030860140d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 567907005 1250 567905755 567905761
    0x6091406010f17090a060e0f070b0c01090803010b0409150e0c091801090c0210050c1207020c030a080408070801020f0f07050f1207060605060304020d240905160506130905041118 78
    0x192407054407c1604030308002c0c03881080d905006038450403240700d240301004021440c404880401c1d005103542560103a003143c1d4942c3c40b2005e407607885d0498001c803aa001d01d0304214055610b8181c920a06842400d11050043e0b40e0fa05510b0601d607122150041c0c2084501e18000d9900c52401c1e000c031301070029068003080d13a402901009180070f03010605140118104000d005041c065041140e41000ca00101d92855070b44091080e0b1802e8032241d8450741612803e0b0035481400b80080107003081d103030307150141e071603060b51303407400c1d034241e00401c0030020b100641080f01c1445404468014486684030b41c1c00d66032925032191303000e810500382e402c85000d21440021500100291846810302804007191801d003582000d07000300e11115826080240f2000520456400074603803100702078031140c607281040c030502006141035911601000c0105040c6118640d0101e9545042026602d0001c000041c0d1038400d480d041d440d802914000d071042e680190188080300850315002225440024a2012112941 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 567908255 1250 567907005 567907013
    0x8160e060c03041e060c03050d090b07020607020706050c07050409140304030b062e0c050c0a030c03170f1206130e0a020f060c030a210c0807020106091406010f17090a 73
    0x1001c07000f1082c01c081e40f08181401707803a400c01d03150040c4a800d0300d4400e0300c85c1010060702c4001c140d10b0034041c04034810b641c01c0100650780042c0240c418685603094a665540d182c0c402e40d00b40c050112003403c640c000700020f1040b030406911240c240c13401030b02c1450703000041004950555100c0d400503a01121144104810703030500b00313250b4030000050f811444410301410b521091440d4002e82d04010420741d040c3d440301384541007003903207502c400c0103007031464065491800008400c1e00303200407151036001d11421411040a54141d2f04051206a44145407200c441d28031940b04200804056006540401e5003161190900c52841c2c0c1040c00030040419540030300400900c0c1900548142c07081408000d880c08001000c41526810102c50074000c3c52403050403408080c84407000010390303410b85403c186800c80c2303a02c008000d0007000a07070000c012058454808030261601c11a0504c00001820042030455105440c10340d81034003a890000d00ba041c242c8124011902c0544040e0420307840141014180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 567909505 1250 567908255 567908279
    0xc0a030b03060103120809070306060602010c0e031204050603072a0213050415020903070e07020a0210020a020120010e01110301062a0f02030a0503030901062408160e060c0304 77
    0x6030440c000d140382d40c59581e6080795a00002c01074010850351070040341c95180204844006541d004800703004c5551a014005e0003461050b12210000b40e11144020450030701195a00790051280a024a001c2c1000c080c05a2680090030340c0341006903082201301003c607403103c8090301c98001107140071501440c0c01003103104100020950b0044e46000140000240541e6854001d000701141c0035071180c0076031000070309000013030f0320000149118000b0031140c680d012940c0e0000724800c540034085200c55030717000c0f41d54030308122001f03020a105000c02e0701510003000c010803072148402d0000c117000c03101c20300c0c45c0e080d60b011f400c1203004018040010300026400054a860952002e540000b140102c9104410703d44640c040c0a025840c1c40e05911096403000c0c000a614940c000f8103c13581d0781002c00000b8000c1095224010900c4840c0354411540039071101340460242e6956114074045d240c0380d00703003080a444d5200386014010f840d01c030f01c0e00d13640b6113001030a4001103400185444528100c220095 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 567910755 1250 567909505 567909521
    0x604091b0f050c0606191a07060513080306040513021f02070821030406020f070f0c050402180111160e060906011e05071b121407080d080604090b0c0a03 67
    0x20300c001400708500001001400e45d60100084a1a5100c208001d03c0c0c0d02d20307040340341c00c2a0f2084221101c96018005080001d1213040d2042104000703942c1c890000d00c442030503c48005100c410108003040d854070b090341080d030700180164065800e0390302c1035001424215841c0d50303080341b022140d03a01c4900d890f014003000000340311312005050301c0100d0b40341d5804580e0303c83d040c01542c41c90100c00300b4184800b581c1075540b00c0c0c00c03180301c881d583c0006092003c00380d1042c0e5801ca034002160400800c440c2814000d40780030301240006040d001010000640c2d41c4400e04620750807074441d000381c4090315100c00303480384020203504404100500300354086c8041204004d1001d4180900c4c0c800305290a1321021070309003401c40502d0004d40f51540e40c50b061013805911840b2400b100540d0f8804900070070144401200300344503400c8026800d20304901544c41d00d0300d03481001241e802819950345c40500441142e0f41c4440b00400018401c00c45540b0b003084040c0c10f80d14640703c41c0004c210881815098895142d0f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 567912005 1250 567910755 567910757
    0x4061503030804051606020304030803090316030207090c0f080f0604090602180a152709020a081e010e012d0608100806190903050c011a04140103080306010309020604091b0f 76
    0x10103086c103401a590784214131000f02a00c00c0080050614101030060314000c3c101c40345c0c4c0720504400c0d82030003075a5200074018031701964504a4014041806503d90040b011072607120100284e03200c14044a151100412141d0015110f00480c000210b07988003c041154400751100c0d40201640f0500400c1003d6411400c91804410b41c1c00240750341105904c040c281c010154054035140c54075400c101104a0303809503104c1c03070020482c0100c1c01d8010781411320078034503401c80b0b400240420102d2410380300c0a02c244076030300c0d9040e001402b001041c1d8101000f1044031524640340d01810300b19a0070300d8500e0340d005900184118040c400e4201c0f088102d0340040c01210b00501c0c0c01d08001c018410b02959099140441a58400c012030030107003c0d4041d54860583c0360020001c027908610030100c8100e04c05400d0344943d140c0504254050105203007603060325000b060b00303402d55840500540080109203026a40b080b020300000407000458085e4521340341011001c0000780020381c50140c01039000444040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 567913255 1250 567912005 567912043
    0x3080c0c01110a0b040f0f0c030b1311100219150b01050c06150d050105070f020d050c0619020712020109061104060c1b17060402130504020a0e0406150303080405 71
    0x1050300e0000200322080c0e50704030030071150b00e17200c9150000d0030400e0003100804140d2119011024070030b100c840300080b80d0152901a080d50340b048001c1c0300003610283e009140c48100210311081d42400000000c0c10308046c011035100c0312817502c50704145c050b91401119440c902070290701c0001d106000391021207900f030074003a041c6018204002c0e201e00e001400c02e036141c000414140113658404803024812038000c0001c000508240c40b006260041a00540004d4814420260b415500c1072007190400707440017020f0000e0b82c881c2c03c0c601210701014091b00807403e0b001d00ca20ba0105070b1090307014103481041d0f000041e80000e01d10b05a0b00f40d503210f0803c400c0c0755100b0b220400a030354203d0120707070707403036078071121000072601c090311840100c070001e400c070790b2051507004005031300138800044c034601440c000c5480c001d4508107451100181c4d44101d5000750000c1c0c400304100700d2500722080207034100c0c0c49100082104c0700807104044200310b0700d510aa0000341d902041c04248501031041e2041d560042c02c2c18 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 567914505 1250 567913255 567913277
    0x100c0305060904080a0311030a140c09240f0f040807120803010303030504050109050106260303010b041206020405131409011407050706020904050f0103021206070e2803080c0c01 78
    0x12104407000304050100500000c121790074130b100c1d500034100c1c107408490742912130a0820000c001418411120790744044408041004030850009a5800c820004d12554103450420203104000303494440c0c4080322203051141d2074a602c00f081c043c14001285600140e201d51908604600d03100300c0d0740c090700102240d65410000700c0c5140c030482c3e065940608000c00e690321580740260040c02c44100142855103884400300f0a00c4a44010080c240840c002608550000d54851500d900c020300c00c1c640910000c000070480340f41a01c44141c440c1d4050107006041a0f51038000c601c0c03600c24283c03226141d540c2e0b40740002c00349000c1a82c0b950880f9104008010700d08846806010b4a40060b000c20180500030541a003008900d0f01200c0b41e6103c058004e1109042460104c0b00c691400e0000b00c0c803507035171800155082d07030f800900c480c03203030031385035140001c420035030f4140064000e558121000e0781407811248042c1c035403a02c00402c000c510550031369940d0910640382d14100082503101d181044581081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 567915755 1250 567914505 567914509
    0xd081009062102011b11040605090c0301140607050102030c0301050405090307030f0e042901080601020d0912020a0801180210030603030909050c0918071209150e0c03010905100c030506 81
    0x200c149074108582020800842d03400113880706010060084400640030020000b009000d81959001c2001941c2c00d101c1e035a2150100440c0c0d000441d115410044140b0040012000c044099400e005002d030041d0b140045a455507400d99200303d8502310780301c5000004105d641418441c0aa201c00c0d0003000d103040102075070700200714102c5400c82c0e00030000d80204a015540d100d511a01900309800b054101d411f40e00101c008000d4110000103010514001c0001d45550020a410310400960703910840c46a0400c0d05005c4c103018845002c1c0d0304255a445c020800d040d00f44a0841102c5a041030015071420034410008100700d41b885000c01c00d41048000c00000340c10400398400c1e00d02250004c25a1358030080310717170414000d4104a5070300c1611842c031350050890804859008040c180d0b60354002960001a61003600c40110006068a860185400c0500740c1e95001070011001e5800340c07201680e1850000c0d00b96600e910b002e07100b5400c0040c558143d01d00501c1403900769400380c1800e00c070b02c1c940800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 567917005 1250 567915755 567915779
    0x40f020a2408060303190c02030c0d050d120b0406090504140d0509011d0a0e0717010e0c090109410603010519030f030518030708120c0f0d08100906 65
    0x701c1c05052040b004049910780c2d80501c2910078800c0035070900e841c841c0c2c0d10240242007031142d801c140d020340101c003890216400c10311001106550410002c21822800030001c4cd4001c140c100c0910360541d54140074901551070f0701448000b05808103011640f820703d03082c100503502c40e40c504c202650303000b074003901c2a0308c2d00202640c050300d0090a103001c2810482c5140c018108480380000d60040c6440d00100e42c580b07c00c2503441c090a99642c4010ba49100b0341d4181d443c201080c0103d1b004802ea0a000421116001c0010240010180b40400a10b541d4600d100300e8410040c0341400c03449c5900c02c40c82e03995004004080342000c4005044c1122804440200d0000d1006000310340c01060b1102c0360403290880d0090607030066a0054281141100d01e050050150b048881d189280e400d80c0e4190414038030700098100180c40c0200701810f00d11032486107902403036000740c1c0b2507c040e000c0ca004402450000313105140c2a000117450365070051500d048510700c000c8594021a0300c0ca031525805100e0952442 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 567918255 1250 567917005 567917069
    0x80702100806091f0305010501081e0a02010203040306090f0501060603201206120307140604030f0810090506030a06020d0f0b0306070c12140307110c010203121b12040f020a 76
    0x1c00c400c0140d114071120105004d05500701408035800d00300001104c80f400500d1040001308801d0903105074941d241c01c582c07602012840640103a006000500128100d98046401e06109540361991f080e11951800c0c00e603003040c1c1c8100301090761441d800c0340300602c0d100e140400c042031044041c074100781c0340325110000c00040e00b8940244002c1d554544000000c1044854140d0000100c020f00107400240c03654a507800c40301100000c002441100100e8024520140100310820400c68010b04102c0340c0320003400c004103400d5061161210f4800425040c0c03000b0710858118007004038099906500074402d543c40d0385041030196001d1401c021406600007003440d8001d9214000c0980f40e0304001e0100c034440d03200000b0040c240c800101380922507400c02e000c4c0c0116680303201642c2c1210520001a85c69004844071038050005600c001120a5030100d1401211003512a0706814600d5070081c000061900300c2d0100c0340841005040001d41c034040c030f1160001c0490007804407044c0c01000d8103400040d058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 567919505 1250 567918255 567918271
    0xb040905060a02161506050a0e240406090c080109060b0a0906030b2706090a020a0903240216050105060d0201051602010c14100b04060b0a1103090d08070210080609 72
    0xc28043d03102d01c401c1040b0031000741c000c01500c05d5200c0001304000140210b110300c512031074440ba0000390780e903040744a0520610b10f43d21240400304c030640e00071900544488800d0340c0195074103c0842c602c0e02e50b01c9100d00b4020280d503200c1d055810400381108485040d08406400e000500800c9034199000c000344055030640d142c04641000c0f00004510001012000d4080c441e04000c1c95610044078010010311550303045600d580360b9290791100000301d00c2000d60301000a55009c0c0184041012408104604000c00038000421200041c14034100d0300203c038800000044c1420710310074810300340620394020000302c074110403450b810b0f0300103031030382c810340b1f04910151a00192000c1960b0040c660381c240e054010312000300c8140e40c040700ca5100e40c0324410200c0120700e000000e040c01d0030300d4400c1805540510b45010314000d0040002d07615a80d205000c040303988000c005054040e1502c00305102c02a11610640e502c0300e0440c0b04019004814031450707820407070b0b42420480746a40c0c00d030002e80c104c421 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 567920755 1250 567919505 567919507
    0x2070506040f1106040e04030f1d0f0102071a07030f022805010b03120a1803020d02090c1b03090112050f22061401050103182a150804060b040905060a02 67
    0x61506144400380414070661004e0041000504003244142c60f40c13046100359030781702200c0104030054407a1100c21040320143c84264050014606142c41c3c0450341d0401401180c00050f0340c1e041600c40c1d0b540059070f488500c80d020460000705078010004181c00d180c0f034006040c0c0c5540c010301184040340303d001011086c9000e0303910310050000c20352004900310f50140640726900b80e5018840419444900c0041c0010340849103101d41c03075425444401aa5402020008144101c1e020803070b1746040600107140e48203040060f101d4000e0010051b05103503481c0e2001e551208200d4001406000740302c0300c03101442e42001c04000b00001c52001c1c3d964851b125013111304e000c0a0b000707108190701460240080903030f813400001d00440c01102503581e040720000d0341c00340100e000360b0700c5641c0b5203008101d00400247c035a072500c551a4459820468002c881035030b03800f21840d900c0342014103013603200400c1c0002c560032030305000034400f03c1d02503102d201d0402c2d40c083c400300e141c0b03903181660390200030004125280c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 567922005 1250 567920755 567920783
    0x5070507051506090a06030206071202070e0910060e060904020d05030910090f06210902010e18040c05120a11060409110408010506010e0a060e030a02100e01120207050604 75
    0x8090810348041a400c14115856000d0401d0301980341c8009035111440b03807811100141180c6428001d0205881d809007250b820101e059840314040d180e180000c005501403c84042204890416000d102d0041000142070810311414061300321221504515a600c1c500802c1220070707101c1180d10303608943e05444000b00e02109040560650081e05c80566202d404501c1840e00107600122450039101d038025058259603a40348282c600700e160041300c408028480d03041d80d1585445a0000420a0041c18040b08049690000030b050503070007942c40c0040382c003d501344420b2180300c004c0c58003e040c0944946607520020407800781c1e66181000020114140e902d140070042d20744006540c0246540842403001d24107000040f840f98010707001c8c1003050742ca0600040c01c150311582106600d04000f0301b403090001d042000c111000080021001c3e054803642c802600182c45640304074080744001d969040d503c03840300c00010125174030800e10b40342c0b5038018401500490780102d641d070f4020f640a02c40403241c40d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 567923255 1250 567922005 567922007
    0x1061206030b01290301060f020106090b030a0209100812032202011b0809030703081918050409050c1305060414010302061207020709180209180a060b0427031103040b0d0507 76
    0x2c0350b03000b401c4d9070b141d408800003840e2904148280c00b10310183d002803103840d458448820031682904465a81503011801e8a40981003800d14030740c0005400014400d00b6032600803c0c3c1c605502040142c04500000007005040c0486280ea00c04400c05021f01568115041d00001c1c8880c901810701c3c19444031a0304e0a01c20071400d201100d0104d40d01078203032806140d0701d00b030204860704001070808840c40c0303d000144250707204425100350f030449070078089051420042404001d11146404584a20411410040c241d40704c56115003000340f40000802c0d1490f01d2014003003a40d14210301034116450301e07001400140e0700c020076245004403401ca001855604d4503000c030724244d0b40d9404001d5640c507210a00740f003000c1d0010f40e110007034001d40e10322007240c50320050450036200107020080d03079401c904101000134841d504103a14403500140007040b6200c040c0320743c640d14005c0003800b030302c02d011889072102055000070542150201480107942090f2502c1e24180300351203480f5103045030f641d4601c0010318203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 567924505 1250 567923255 567923309
    0x4061104080609070f170a0303020a121419062d0b0c060f0c0c0a060f021c0204180b0d12090f0306050910230c07170301061206030b01 59
    0x345410303400c8440700d040c44080c450304c3d80110701824100000c40600451180c02204404400140a10040114400c503072001c43c000d4018074212000c01c110301d00b52048070000b0380914440e05803245022a10b0f42440b070480c00c4030704c8181040b54206410b220042001d08118500008103989408850708141c20140c03800040203151340101480c0c5001049241d011900050403c0c4124000701500c0340503150310b0721980460080000c0f400c115440040071400140f00c0da0001287c480c8044000741c246108440380361210340c00c0c003160070700459012904201c610000403807020398440142042000c0c0d880c8034003242d004801030b50302602c901e000c803110000480c8560001401441685507074008140c80e0315140004d07000c25110100f6500c01c4541104040185120300c00f040032400c401ca00702241210030401c001c0d000100b03d800f6034582808031001041413450641e400480c000c490565940c14580003410060103c0030001b801d07460a01c05000040701007401d00d0549850501c108408080d10f0240080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 567925755 1250 567924505 567924509
    0x9150507021302130e090705150f130f080c0310060e160903020d0c0e091c140915040305160b09040f1e0506030d050f030601050f0c030307051b1504061104 68
    0x1301c13041003000025032421607056503000d10b0760070058a026640d00c008000080c02c0b0124003a500f070b1000c025551040c04204014520040103020708140b0079924910100007003038641c003a00c002d812540c0311801a15061040580c2c80200303040400000b4108a101000c84600819408050032240002da00b924094240c99009607401000c134803240215241202c52030906108548441c0c0d05400860031300f00b4082962500ca041c00c8e03c00300c0240303811040450314500d0303051075100445010030400069480300708444c40c5c1e081640d5039146d039451031031400e5894143c41420f46181c0000719502030140c0d805500488400c075204032800b203180000f00800c2e00003000aa43c000310344d01c11200d81500d04501c550001c030b204210480940e0450070800030151060320801c0d8000045080420005451750300450180c10a0b10282e103a83d424003440c00c010754610f910684580011410104801482120358030130b428035003904801070481d000c41d441d07840c2490000a48000e00d070540b01c0c080100405040016180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 567927005 1250 567925755 567925777
    0x20a08070f0315020c0a031805060d02040e090304080c060d0f0e0a0213140406110418050609130302032704150815130b1e0a0c09150507021302 63
    0x55040e07403030520a4030700105100c1161030360068030303807214440e00724425100300303400c1c400140c0b500c072540e940c0484010440700303607131400000b42c404040b40766100d01000d0b00c10400354140050303445080018807180040c00030150074055000b044180088000451130107a1901d0a840c090b0300c80c90200f81c940054403001001d108510301d81003400b0701ca03800c006030700f40c00c0318000d0310320b03001d024204480c0e00241d0368180060b0318518140d40104000072829800382e080c00361034500050400c0d0f201d03403101d51940250395030f16484030f0300c0d0400d1080d02c0c44d151800b10340100520380300c5070740d01e08607039400382d05ca0203400743d0301c404400c01c050301e010941e40380d4862084c100f00003001001076524001c041e0804942e1030284032242e03c1404e600031140c156603041c3c280501d4155554140b041007960b26252903450050205204019440030855091024010303a40101074941b00414113900c603940c01828081141c1c826012040c01c1d80d5640e1500d47c0000440e180244c06650881904848201c2d080207446070b108419 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 567928255 1250 567927005 567927013
    0x17100614030a081c0203090102121b1e120f0405060108210a090b191409030c090a0e01050a09030e030706140912030403050c0108160905040e0c04061e0603020c0613020a08 75
    0xc0680c1f28103600400055503400a00002c5440d491103441201d070140741c84900c125001c115101c0b0b9084c0c1c2c034440401312055038040038904001d401c4141082d0031305aa0321100c116040e4140800c01c0030600041d40500010b1005180d9035094a902d00e207a040e410302d15860484002429030a110b00c05c2c5c0d1048007a140008215a48100341000c088003c5a501d81d0300c00011100201c41001c24040412070b08400340c020b0003000743d210401c01300044084003921a07a4110381c0c1d00111114200c0038040c5600c40c641940000880c035000e400e010300160000c030452172003900f000c003040c0005074010389502c02040d0441304860b104c15900f808200b544090340403c0d2a00e100114000040101c001401c44284900380d032a140a92203140c0880340c541c100380b0707040e0b0205020b40700c2817006081940c440520038980c1422511051a802c001c901156115040450400d40c604480c40000c83c40080d1503004020070f1408502e406114a9480e4945801500043c0700c04010f2105009540e42d003000d003009480e080d0169 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 567929505 1250 567928255 567928261
    0x8030402010e0324090d09050334080304060e011e1808011d070501020d050d050712051003140a0209130203030c1002070c120b0a05060a17100614030a081c0203 70
    0x81030756454102d480480510800c07070350800340d47c030500a94085500c0900140868500040c0c00da25100c440c0050602280c0d001c4c120b064008c0880c85514010a90344014540d1942000341c0185101c08181d1964140011021003640842040a10100140d8a4070b40440303519484100c4081132002940651602d60a0030700e001021220800751819020081044843c00c0e0b41e5800160380395201c10085a010840510454245118a4204d50740c40501c03840d020b0a0042c8036202d42c400ca07030081d13440300e0340791069000a108020410511001d001000c000410346001f0030341c00540301200080401019040c10b0341da100840d01c003002130350101031f142d400765a19408035141e280009e41080c0f40c29500160050400183c1c040b150114a81403a0882c123001c0055460078a0000584006400d5541144600b0b2000401c0d04503080c2046507001c06034040c2c8a1421001d1041094130410303046861207038009000c1e440250b07000107034a1051903210f0412a10b5000102c0703d00b1484603400c010080b014000010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 567930755 1250 567929505 567929563
    0x90906060507061e150504050702070305031b1e0109050105060108130609022e090f0e07052101080706180e0106081317220501020c011d18011a0708030402010e03 71
    0x305d055607819241004595215042241d0303545440c0310140190b0010008039a05044030401e0380d20003428101218403040350324030074616001e494a811019a55162104010440c0c00e00800350029000d290801203828030020700b104064110000502581d61035288038215100c500c00c510381d501880c441036002c4410b0305080910b1204102d180e400041984130301044440021018605a5100c00c40490040d40d403c0070580e819401614030003d10355030046444c174030101581819000c6c010540c05803032070f240b0703020000c7c08056040c0c1c000020070541c0c003028043c100342104102c0c1100d1682c50f0083c01c9480d0004010440740080601600a14200181c8001007c0100043c030114111458985801407061090b140000103809000d006070004018912258402c1d006441c1004580d004600701d0f41c100300024504046801102480a17034160040084044009a8004480103605c0f503519000d46503544001e41c0c13000500003418000468000d014948081200303900c444000e1708000201103034401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 567932005 1250 567930755 567930791
    0x311100e0d0c33020a0b060d08090307030503091923120d0305011706091c11031204020102150c0a051803030c15161b030e03120406090906060507061e 66
    0x103000903000d0710041441e04510000e0705c050fa0b0343d00081840c0c11034403070ba001c1100c041d4040c10192505001400800380c156000d12080e002584240025a500e244030410310500441441c2a4448115075402c2044445ca200d8426190a240340c05d008083c050f000c80080c00212081c4040c08581c403c0c50350101009815030b00542c1601c0e03808004548034a02c1055065030743d90304a41e1840b45c1e400c100c40340e1001c1640c00000409440c580e0801c640080402d031411491600400c0d01d440c440e5a5503018001503580511003100c40c03800700e480110032464448011205d80c45139074056420005c000400f41e500d40595021003004103401016030b5601d105107114142d9440d40094801049030207040402c208460781e5800010000ca5511034110f420600b84503007030305c420159010b4040c840d4460040c404e941d014030000b10803d8461134400d0300c843c104800140001030540000d0020b614000c2e050101981040c184c030200b80c0c3c840008034121610311903402c02848009110601700d400c14180c6907945008031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 567933255 1250 567932005 567932069
    0x1050403080a050a02120c0d0e011103180a1203140d140f0406141e0c07060504050601031208150607030207081b0f0913020d0c0305060c040311100e0d0c 67
    0x170742100c0c00c00340000c803c42c49030701c00e113110207040383c0c052605c8034421809404546440300c4141008400011081e031002d0545c1d020a10442e2408514000c921040c03402803100d4019002602062001030304503680601100701224841c1ca00060204901d515940725410240d01c00d007140c007020a0608104002540700305050b60121036240c00c0c00310340001917000c05075580c4105441a040e48041050384660030b0382c0342e0b01a004440800080000724007150040c0506801144907038000c10340c075072641c02e204560705010951b02c1c0401174800c043c0012801c0b42c2015185004048440c1980c03104c0a00d03040c2d203440150747c05124180110483c00c1510100e43c02e455080000650700c241212640c1c07820001c0701001154450060034450b0081400b6091000d28640171520420000c081c80380c0701d0315001d150807411100c410718110001400e0041100e5035480c4c2c0014007040d9241042885060005460344c47d50198103070044e0031405c100c406000e201180440200701042500e03620090404081130a4100380e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 567934505 1250 567933255 567933257
    0x813090c02240a0b13113606090d170406180f0306090f0c0b0306040612030804060f11030c04060206091b06071103011401150c0201051801050403080a050a 68
    0x8040aa0440344042103214489030340c504000d0320030741c3c50b10b0410700208a42250b494005c4c05000e01890442c1e694400c003200c500c2c4180620740c6910318900d07122a030008130720100e500880e210500d20105008120404901801118110703201c019a80c0840d4552220842c040e008880c000030103a00e2005080040040c0d03242581c9900300051500c00d040c1400c00d06225a21003000a64007c00c0030400903800039040510558480c28424015110f40035190f0180d000301480c07500000c140050340c82d15204101c001c0c8003911060703000340015103014200d080002c1024040544a0b03100c1982029140d0100402c40f400110701c940724201020340c9880d5070014050040544980c0300802ca5590f0000341c01045c04024200c0454400c40c0d04d024400c06402c1410201e900f00706403048090315030380a01640c0518030341e680500380a985061000c0300c60b1154180280203010070b13120031a0140c0d0f400001c5030f450030f17101103c11806100c408012505ea104944c00a0310308000403540c400c103990300030010001d00e800c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 567935755 1250 567934505 567934513
    0x50d18050102010603110f01050717091e0627030a0309030204050108070b04030305071704090b03010b0448080a1103010609060e0f271e0609040813090c02 68
    0x840c40103908070b5456000162903103400c0d0003440c00c0e03441c0c4020800e0365104185001c2d420003649960340daa000d0a140c02040c5480c8003c901000d6904213200010b2680718945185000b40d4620f0000c00c4c1c1c1413040c4d10341c10030300700041665141d110300c01c4401c1440d407a1001c0c080b00c0c1d2010403800c005103100d5113030204910542c240301c000500c060b0001078410540711580c14a51600d0302d50380d02074455620034103040f140102031010301c8000d0030501000c0e100030020711801060458a41c01010308448055444500c84c0f840d0980600341c0d0b0f07105400c004202e84120101501e41d0f22850380c418481d10060f000501444440e94098080b640d0256140340510041c1c0d0341440004940008810140024058440018460f16040180c1441042601c030b4520303015081c11010400d41000c14410240b00c440c0301c3d1242042c3c910b60b0321640840d41c1c079690000a003010082071942064011400a03c040e00706880f071440e000114040c0000041141c1400c0007114180d40d25954030401c0313401514841d1003800c09401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 567937005 1250 567935755 567935759
    0x70611011104081c031e0b01110f121c0603080a020d0f020a171303061a03010204050a09020c071d070306120302061611010207050a060c0c080301090c0c050d18 70
    0x15041d42664161010704003d002c407034060313440c02c001a41c000035402041644071886500350340b409400200e0000c01d43d03040400c25010100000d04846031a41c8000d000740d10840900c256420b0205442c524444955070a591f904d205440d040b410301c601d40192005107281410001c20032000c2401440e85201a0b003c3da40440c1c4152016100c015600601c803002d07070019625140000c5102c00b401d0200182c19180303130f08103284001111041a12600708958480d030321007150451b1110000c6418800008500039484c2900f00030101d08219200e1044c5070380c281c0c0214184100c22000e0220314042c2c41c42420580d07100c0900701d03180c102031800b550490086071402d20082010901c40d00d0580c90140c141d001801d0940310800445214100042c40c101041081005540b41050030700040c6441c078061801081c49814070b0401070211000f1248440c103018019008100103618070099174116400001c00240f001000c0314150f42a0102d4a0020a02c0c000c12018800d007503046070000542c080c400010401890b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 567938255 1250 567937005 567937031
    0xb121618020409052715010315020c01150303030e071206090201050c0a030e040b060f09191a0c1e070308070c0e010816170c090603070905040507080c010c0804060c02040603020307061101 82
    0x5d240c4c1222806c060240c00018800b041c5030781d030500c12281c00490018500400c1000c400d084802d801c0c0708440e20700d1003041c00c01c145075050150482505545000d041200d190103407004030304110200042c88103449021070400d5a0148003034031042c0682034150382003580c49207402800c211a8602d0144280d00e0240010054244a01035034071800801c00d540f4034100d080001c00880300054040107900c5902a1004907034180841d408212001c94000d00544034a41004240e0401c0c0d5000740c001c410003c80381c5484690035001840320102c1c0d03000b0300a203541c0c80d11b50034403031540c80346500319000108184000081100c0002280d0888118500344d0075000381e1100740800400100038081e441a40c003001c2110000d1030411605604100000e04030381d4510356400301242034800464064401d81c10908003046003050511111011100c2403070540348005aa907103a039024001d5000d100104211b03881e0b024210340b02e550024010359001022a11300942d81c80c001402043e079810940c00d95401e141000c015030b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 567939505 1250 567938255 567938263
    0x14011203030f021227012405040c0c0212010e0109030e090f061e0a090504030203070c0b0307211d07050f010e030c06030405030d0c030b1216180204090527 68
    0x4c905031002e11540d1545151000061a00201c04e00e06211007541e850b140701c000d1003645c94900c00043c1c01c00340f40449003c451400b40b55540a24000c9040c0744000d06400d40c4040f041440070f6040f600400450030072007000d8010000030400ca8041d41c40c0910b400c041c1504003614401e0180200c45000242d9503454004c0c403003030410707134000d90008001c035140341000c040b4104086420034040c0983c24100c2c1c1d00d49558050385c006540c154003607003001800b0300900c11603420104c064030150380040e2450504e048004d180d49030200500324443c1c0304030950440d101c080e400211100c03405803000c150041003c02410b0310f41c1540d200311407140c200e4240300308095001d1180c0da020f013600280a0305c2c509155009200b5507600050044030745010400440b2000b6001c7c0c4a240c03510742079680c00180650a4009001ca4610001c018841781e0340031a040110541c000c90710b100c2a00c4004016911380d52000728120301038000e0b40c002081841c20700d001c02c4040d224a456001011102d102d01000c8004079800041d1030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 567940755 1250 567939505 567939517
    0x3021e01020606040e0f25060518130e0d0230090603091207060902010207120206030a0c180311130605012703080f0d0c0306051804020414011203030f02 67
    0x1d600008000f441e03610740395102c0355001c141c00042c0e4050441910f00c3c0c0341810480b044c0d004400407605000c0c8040a14140c0460140c1890f00b0440d00e0b180441c041224408103800300e2612440340202c0400d038000480e04141d51513032900088a25a982950019480d01018180103211502c0b01c0c80340c0c0c0c0d1840440c1001d0f2580009050f0891074100440240f001d240e000504902071441034080c120f141e003c51100600c01c5e240070765000213503408507200090410583e54449000226040c40301c0001d07a840c1400c45e0340000b9040320001d813100e00b6240c1540c0014800701d1850880b07201513400005d200003070050b8001c42c0c0c0e0480369016401b090b501d80c00120f804a01940b0b00007404031842e0006080c28111054045d03d0020707182c000180e50ba41c96044580c0458241e40030718002103403070981c2c184680100c50010015050078801c150400c3d004c20103011181c0d95441e058500c4201003800d6450b1544021052420003070a80041e40e11402096604901c44604a001a10b0881002c401001074400e680c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 567942005 1250 567940755 567940757
    0xf060b0102160b0405130209091014030703020a05060c1203090d03050c04032a090c090801050708250e0d03020a050f070e0f0915090717010902060702040510030f0b0103021e01 77
    0x10a045c1484244004910807110001317402d50300b046000d05640d41c40c1d0769184100c411501c0c4162171802d008040c62440200030206009a10035142030005a450003840000e481c13040c0c454585075001414118036140408a80020120b0f00109100800202068400030303940c0980f000d0090340c4980206980a2240f84030107401c0d001c24048100c480c180c440741c280b2082c09103000c916480c0d030f00c602002040fa0060b045500100b1a600800c00c410782e000c4c05042c1c0c2c080402c1c204000d552410101103812803441541c1d140149021405070f07600c0501403411859600c02c090851848003e00740740c041d40e2036501da1000d450900c02d159210000c044000f5210f0b0030349503c11524046600e800000c0451840040c040e00501c1c01038511600c0e07a03034040036065224004660082c0b1a4528103183d452060100300c04026169040119810142e1140002c86850380d6043e5000a000d90755251030181142007500000c02200c0114a0901401050348895040e2070088907490b0340211303a0421000e4112500203442c2c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 567943255 1250 567942005 567942007
    0xd0507080d1410290c150108030a110a020a03031b14030a1b120e010504080631020a0b0304031e0f1425020103060b1209190f0f020406030f060b0102160b 67
    0x580b81300040301c090051a00c01c2012100c00ca41c91061041d070f0840260030046459002242d10500d007540080c070203100015100143c001403207590041005030035507000240901c1007034082c030060305c0174212031031070074035008225058120341800080d03440c0d510003001f030030000d404040740344505c2134180000b2500301d82c0251020500b07151f200d02a1748406500356220b0600c0340c10301c070008c0c0c0000140400f82c4981000f070f180c101c8240400c281c032201800001d0b0064003041124a1910040c0c840f0b8184030309807188500510748a9649190071180c5258560306042d50740c1c1120928540d1300d4100c04034404013646a110764203e14400826420ba5000e17400c0554580090110a161640c0054180ba1101070040c9404200c058407071000d02c03c0e681c0650a086080030400040240803076084c0300303104508955080d200d41c1201e05803646014021300b240041c08518600d10a24110740e02c66001d40c0041d42d11080c10300d40c01646003040801070110344a02405401845200e9680325401c44400701a035500c2909a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 567944505 1250 567943255 567943319
    0x702121c020f030a050402031b06040303030e070803070813062609010e0616110a170309011e0c0e0415090b04150f060f050c0d0507080d1410 62
    0x9200c03a0412101a04180c59080101a09080d0b5030030046220b65041c010102d51814148181898079a8440b050324500d180059600e90079500c04088604a0350075250200e02c0054547c019420300c00c66900c45c45807884005598410000c00d14054410894040c0c012440d4542e0307040156861841c6094503018603100701080c001e5451450042c035003100c00c034000050484540c07108070749090740c01e40e40c403550115211040c104259015400c181c0c010000006002002015904d0000201044650404d01d01c0080700180501900b54400160344040d9982c0d80401502e8440510041c010001003800040c1a11000c141505041c06090483c031400604550984c0c44c0500181c0104095640a41e0080d2204086010007132010007180281520341c3d503c108a5103031100241a0440840c0b00d24240001440b414940650128080904480c0d82c1040c1c0d64540291810090030b11030060390b0342e603861030700682c84552422914400e100c0c44400500041482d00c8030492500301752400e0301c5078126018a550f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 567945755 1250 567944505 567944527
    0x30323041a160c0f050d080a0f12020406030b010e10080403050307050904050f060f0907090608070c080c0a0c0b1602040b0604150c02011704020303090405090c0a0305010212070212 79
    0x500701004400310507207090000150b02110062102001a2030b03480142506221004400f10240000e060483e02c0045440c05941c0c0e4209074007815031040184181c24036544801c03402500a0f008500207644110340d11521601d0190040003506c904038001044030208a0140c1000240f003a54103405840340314150b600c41d5022101548000c3c24901005014041500583c456000f42c0e130080c1c1c0340c00445410ba180481c00d000c3c8007520f010b05584a42002c170300380b00c0c000da040245032090754414a040700540d07840d82c8040e00e9034054100000e00480b000980b1104500001c81e41202c101d1180705628240d81c1c0c3c4a200d19024000c80e1844441c004082080500521700360748641d1a5080151100b800c1580d03611002c1c1c03569607011085404a040c000b5580215070740f1448000d00c400700305490701141d04082d00420f40c0c9004602400b40107583c2c84000c611220030412107080320041c0185140b59180d2a0b24080c0c0c081c5d0481c94101e0400b920300d10110718004c0c00030600c0e005801c0b4407a0031a0502d5284c0302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 567947005 1250 567945755 567945779
    0x20d0e090f07141602040f020405090a180b04050a0224040501110a02040507020a060e0303070905010c02031c0f020708070b03070c0602040b0403061b021f0f0b060c0703032304 77
    0x50301c01440300c0224040b0550410b0f0010303207001500f44000002d180300a0041c402a22100d140658030240304020503c2103682d000e0000341c004030344a1000814140380b0b07121036228000110f000e8144001c020400c07040010000b01d11000600c03e5a80c4d200707008426180c4090750192020f0b0224081041c4414001c5520507294812400d450500300d424088150300854101c0f64185c441c500107801661206090049074043c0b03403c4442003d000318514a07100358018070900c000d019040c1007094503004e840c00d550b13041101201d4055030003e00c030bc06441c288005401c103584001010098060001c0c0020100b0012600340122000c003481e80c0d1859130b45010840b613250180004071030141e424000810b1294649c070140000c2e603c10f80b4000782018482e088080b41808000111003154020740c0c0c15450401003501845085000c0140400c040b0200c6003010080d0240c60400c40e0406004074064000c40c1000403007030704803806901c94580d800e44400251022250541c000455008100020001414400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 567948255 1250 567947005 567947011
    0x304060e0d0209091c0504050108010315020c0d090512010b0d0f0c090606030213050f0f1203070602030c03161b0b041a040318090216020d08090603070f020d0e090f 72
    0x81060303001003207a50001d1030411040c3c5100b1107981c04940e04044100d0302441106600440d07060481c04c191801000800b09401404020801d03182d242c4e0081050400390140c81c844131420040d1502c901042400a01c0c80010b07116544c42641ca241c1810f203000c0c010b104110000c0800b800c40441074001d40c075203a26450080c034003110840c121100c00100001103203c1d070000340050f40d0b07001d41da82140c200004910507442c0c012512401c10040c3c2c0c010140d81e000101000c0700c1e019607940d060320441400446c118041c100c009892140004100402d4281c9040190320503c501000c1c90201001c400d800c940740002c450b580c200035295903038280042581134640c0e980c86442900c10074040d4592003081e808a000944044021400140d5070121406425031241e0113031009032421810084100720721582d01e240240d011380a48414042c900c24400b480040780c50b440c0c00500099603e05110380003c005c007004c0041c1c00014062500401d42c940d104000c0b011038183d004184144944039038441d088840406 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 567949505 1250 567948255 567948259
    0x412050c030304121a0708060f03011b08010e010f082a040e0c0306180c0621131e02060d0f060503240105061e0a090909060506031b01020304060e 64
    0x200d818403a80d0707030400040024083c4500c2501c105a42c40c40c011601213504c0045e54203422008041051840c0e103d2090b0391b1224080b15100380040b80007010030300600c0c0c402e804003642c000c070720011110290840310450485407080c04501440e030b650780030000310f040302d4002c05002d60481c000449610801e00186c5800019030ba1038400555a54000102100d5080216070403640000064100a00e810320040350710102c5800c101c2c6809070110031030341c0c40d10b54145605110300404110887d602c0d00d0241c0e8800d800c01e090700c02d040c50b03041c440504222450349007011910740000d40341549207050910000c100350340e03000c0c000394103000c800c00140d0007034100c940190b203100b5980c1070b00144e1035130100002035280008031074840d00e83c1d12210b009030550380705801c01d501420040040e50440c281410800317100c034894810745900d400da1141d08450041450344250081d90520010f00300f84001980200c0c01084110b085904030080400f4003145421042415409600103000800c44140030f64203413400c003d00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 567950755 1250 567949505 567949513
    0x209060304150b0315040510060303020601151205010b1e0a0e0d021801090b010f020105011a1308070810050718030b090a02060f03010f061704060c0309240c0e0303041205 75
    0x1c0c0700400c5c0760500d079150340d1120b0200d40c014803041c00400c2c81a4010700080520501c5124203540300a5941d07072040c41609600021070203109200c604c910061a0034802a0405000c1035949100510003500801c4141e00707210904009800b502031024120760300000c01e91501030401844d0b004000342c03880c182c0b400b40c1e00559070345103840101101452041c081c10002c80e002603500815400104840c43c95004502960b24100c01884002d0102c420341805130840080e1554480d1081040c00680713a13903178854480751241c0000460984404106c401200245040c00c0216940d0101c0c11101061440c500320304481210100b400841e901d014501d9100c8621411602218000c0c0d000c510711b54040c070742c2040e080c1404401881000712241042000340114076110f003018400450150b1000800b802c020050742c2c3c0c0300c808251960082c1c00c07814900d900511070b840c20900d01c3c00c40301c4243c0354564051091510300458003d8442c06140d1070036035900068025410a03080c030300e040e410790b101003006031041e01c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 567952005 1250 567950755 567950771
    0xf05070807140a030809010b031905160609080d0f081f0b040b090f0406060f0c030c02090906040b06060301080d0c061404050f010f020a050a0819020a2001020906030415 74
    0xc422982c4010b080c800000c1c10720b15140e00f002882c0040c05400b00800e80d04150300c20307510384e0b400a104e00c5605001d0222007581c000a180942c03900d1403000003108a14000780340010902c2c1c210384c095041301d201c6420f80e03080a00c01c03c0121424050404088089180070000c25516022b0038103e0f00c003540c21000b0302d5550740e140c004818440d00241d000041a95000980c481036041410090000392401c0c1c5081c0314140c20168050101d01c4c0d014240c004100e81c0d0702501c400d251060310340c4d0320940e8019003003031560304001059070b40b00c8000300c4003940c0c440d4050000c5007041c1014401c5030304a400c0c00018040c00280617100310780c3c400b0700d080c1c11b894507921400702900394021458840c2c00b580c4180020502c40390404103050a6070841d4030000c03620341c414460f151110390413000715204100d00e458039080503680c20342200b4992000024cc81030551002c03803a24034540e08001c04100d102201401d441d20420268001800c1c4d101e40413503160031440906c04500010100005e156810082c2e0a002c1030780d003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 567953255 1250 567952005 567952013
    0x71116240c06021812120a0518060412060c0f090513020c06130212280303020d090501200301080703060e0307060e0c0427020907030b06160308010e070f05070807 71
    0x2800413089031001e0308403090481d181d403500720422184082c1d024064090313503150500c003130824060040701d2000d0120000d030f51b460310b64014080104500005090075151900e40700402c2c004131495408403036191034019096580ca0007600c941d142d114483c1d4654000c80e0519040c010740707803001c0e861581042c0c1c00780a90b1500316014419107104482480614603502190f004114141c4c0c000e1201c082c2e01d030040c00040c000c0b00801440788008651104076415011941e2074228020b00c12040e030002001d103040c115004115064109226015070b10041d2540e0b9460914105246d1101b0b01c234901d8a54800c0d00c0410004469400c42c00c04c112000c001c0d44c1c1803001d07544030324054501043d86030289811001d0b84da156071405100e0b0b601d41807405058001c41000003861004141561503011f0310400310710002809551213508512961750020303100c0354031101e070000b120b0001c805404088000c500c042001040c0b0500340c1030b54a104132003039030b00c501c0c0c04407041c2400e8805d035000d00800e840720305080040002003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 567954505 1250 567953255 567953257
    0xe030c042307080f010b1b0a0b010512010b011205090a08030709061b3311040f0e041203091719030b01031b030506040f05071116240c0602 61
    0x494140300d05680e1044216005410303801c00142807400f848420428010a0070000b44d506054402c01c0a0003036444050f09600612000030400040c2144030305c0c05000100844844260304230348065400b1483c241072401200d00b07807104410824001074495018a42c500c1c210f070405904140d5100070754201f14442d407102c603000c0e48102e411001107a0007035410840d01d030f4000103c509005100301c82820040c00303643c82400070b140c0d0704400c0d0340318101c200e50158000c1c40d40c2c85c030740c6242c0c046500c2044a42544802840e45400c02e11594001200d500400200214804041442158081c024013041c20003504280e00404412109498941d134212070000d440c80c030200140140303013001130804c803200c0c002a001825560a60061810982002003400000f124022038a001c08a1820041055034031840468014149100c0e000301c00b5003800705001c2c13030641045105402146003001d89100c000031659440300c00d9170b02c0c8240310a0902074090706000301c00710b804921008806207004100d9a4141c0c0301c000c01d07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 567955755 1250 567954505 567954521
    0x13081006090b15071b030812070c0c05040903020f0601140f0a26120a0504142e1b03090302100e1e06070b010e060307090504110907051c020a111501060e030c04 70
    0x44003002400d03c455503140c0e0720149e4450b90300c0c54111002100d640c3c800c509540144a51030060723880c0e4030a402010300a0150851345115102100e4140d0794034007403d4110145200c0050060480103001015030400620700c2e410303a810f605501d214400c0c0140040139011070706111100d44d0060041b591001c01841004056400381d651700c082d00c46090a810411091100300214800d0407a4101e4031545c0490854101c001c030566001c411024408941c251900d811010350120600c2c03048003080f04064114043c1020345e4025540b200c1c50080c40a0183ca0b0a04c4040016500c2800e10201c0d0034080711640320302c004c000010303044a00b04803460b560803290704820380094010350a04030402109082c100001001440441c00a011908040d226640c140d920f1240950003280604000340c0e009003c1c1048580209a08502e110404807211400e002900200d0212000402c81c520512180400140d204100392195820000507460450251202c0113000c401a0b098003071502121907954443c420407038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 567957005 1250 567955755 567955763
    0xa0501140612060411010305070c0c090c020f0303100e0411060c0105012c01090e070f0e270d0f0905031005040515070804030c02040213081006090b15071b03 69
    0xc01030802a0400c0840741c000d40000034164031050400c8007240c05150700742c0030143d0030b003000a41038076a11401c803000100c4400241c250300825078001100d84259111190b680b91070380c241e42c2e801007120241034aa10080d41d115000341150481400b9002c616103069802074807071410820394407400300102e02103410100340104665590001000240c2c82c0310410804600400d580b0355221010001c0120260018003c9080c3d0310b5076081c890f01c10207010003030740300a071034004004010381e651941d03903d103501c0e1f0484440c0324800c06a8001e012609064004008001865015000c1810f0504085800c02c00051100b01000708540740002c00e03403001c0c4140f4411030400c481c042010301d09410003914088255408c0444440c0e45c40811000a80c0b01403851f0b0030030343c1843d11180c0c4888900026005c0d004e0101102481d03212503c002031142400103003644101400c0c081840507556600351207084949080e80300da08640d040e0340082c401480b1320b0042038014824044007801008201602003040d1150304212 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 567958255 1250 567957005 567957041
    0xa020a03021b1e0303072106080102032d19050619080309040b0612070c1103030a0e010f030615030207050111030c1c0605060901030e010f0e031902010513140a0501 72
    0x1003401d100d24080d61011902c3c0034021451420503030f20042403000c03030f442d0b0116100080b1000c1003400c609500904010b200310b100035522420a841140c050100103e2a8400390031940076004e20b28881c052902c0c072a16000e07481010501c1c40611007005807000802e081e5010f01040b59100911080d0340c45c52010300366000007592a162050b0500040324001641e65216010034400640c3c00524110210b030300c880c80c0e14180910348110303e0180c4944c5a103051155048c000400c0760100c4071360243c1907030f111100982e2140240301843c041541116018007400141b03000d0302446401050282c0c000b0a0450b108100008580c0c000100c031007161341050303a81181c1c904001918810350804035403002081e441c507032800c000311450100090403610524041701d05250301c40050072040b00003903014900c07203102078406000300e20298800540303d501c440030440006114520b80c0710964414450640b180703120301c4091250780007075240c4c2001c00354815512031086c400e18481100044003030003007280410310700c4841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 567959505 1250 567958255 567958273
    0x103080a020f0c100f0203072109241d04060f050103050610020304030b060d080d0b01020d03020408060f13080c0604110d1e0203010b030109031e170a020a03021b 71
    0x2410408618129039080c3d004183d81000c0c0e0380d0303412260b407440040f030034404110201801c0a9065001c0c805000e4104c0c0300c44810b41220b450800c0600310030745615a510790340151900c030b580300d40040c44c255000035a14074030540000380f4050031078510796412504a00341d1030544040018203881094009003e5a021044100455601030150ba50082411207882440149405000b5507038080d511000e4115007201c0003154040d03ea16100c00301c0150000b05d8a90b44402c0c0c1404c1c0700c05014517450207070040c0f29480e0b004c0c580500c28420f0701c090701c4081c8041c201548440d01034040c2c40f40040d06a4500901b0a00f0701c000068000d0000e050130841040501901d2401e400c0041d0b41c1c1c000c0041c140c1c05145c1c400c882c0d90002d103081c40445107100703c900e070407403100440d800441c0c01400000301c400e4241d0f18200c10081419000070110303030040b51641403580741c0a140041281c1002d900010101030201079004504000c4545d005080d4041c0c5900e00182085c0341c0180300303110350507606204807003904034000d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 567960755 1250 567959505 567959507
    0x51017060a15080601091d091b2101020d0516140418020307090503030d092102060103080703270620030f07030207050a0321080114010806010c02090103080a 69
    0x248aa00540032100412074038030307110102c0c20a40000842c20704011030a00015110ba0080003e10040c0c5080081005814000f5592050140c4143c98140c0e4521a1744401d10340d01d1010380180b2003440340640b40080d2520600084216400e010181001d555020700403001c000c819445a944203420b29040c030304040c0d02203403014040860011121a10305030420040c8507240203583e090030800c2d420800141da941e2500320448028196401140d4140400034850b40901c0e1207410011074603000d0308100f5a0883c1c2d075074000442e900d000400c480980c0051004002140110780a00780d981e0003401e003030070502c00840c034034840200355854500c20031001401c20720619610004c110302002c1c000072040d8011007603044075a500c0c01001d500504140b0002801400c161003400188000c02c0c010b032041c0d10035910b82c0342403103c18100801c91040380340b050300360188030f51081640d24121168100c81e08413414520004540903000103100a05010402c1d0740c0500585902600074001c41c00350007090f441d83c6604034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 567962005 1250 567960755 567960797
    0x1121a041a0907030c09141807030f0e0a05070e100803030123121c110712050f0a0b06060f07080c0a020102010501171c210912050307120c090510 64
    0x2c42c03c0b00705840d2a0354403195a82244403001640c4640b00440ba031281800001848402045502e45511030004203014100b03030941c10000c005504c02006200c0c0400c2030400c0c681d034440b00d40d0003400d15480343c2c03020041c03a0074180130a0b8105c01c030303480c0342c4110b1a242d04a0903c2e56000380d1003010002181260702c0100c2c4130365410b4896518086881648402401400507943c05c400182002268540d5040d152506d02525a2125103401c0006651a15580700c4182c0b480c180807000683e0140540401d00c0038120010510482c0642d000e04101015200c60050080503000b00860400f00c54040000101083c40d18000d07140c4401c1900007002c081a440c400242074400c1179106070700e04900c510814010f8032012400c1300004290740a00c141d4034902d02001c42e9000354050942c003507400d01c0401d246920b499600021001c50080741184507015504800f1076051008998030000035010407102c03120b2100035001041c4e415070a00e0807096040d110400105811b007241d4110b000f160750340300ca0500000a8407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 567963255 1250 567962005 567962011
    0x3040e0f010b1603030e010221040213050f1f0b070605060414070504030209040503071e03022b1d1c140c01080601050a0215040c0602061501121a041a09 67
    0x102c40500b0042106222810640c151200030281a02e8070f00c4041100d40035030580d10210304690040d443c604d03000b030590b10f82680c29901a400b851070301ca0f01121400c404d000b0140075000c0481c8401e510f0356010444038151100b1070450401286104002a2034000308000d42555402000006a907040900c10441156030b10b68030352480c6078030b54080003540d50701710041c1d5046940541e04068555101e1504a08510601c080140303000009440a01010034408101c01c600d0300ca602100d111102d400301c4210740361016440540d44c580000b4042a404d80300c0c04d070300218084241c0c081030080384c2840000301500c9006031927901c9100b0b5448043c061003030411400b1003030324a01e0301405118803660002071481200502a03410302c8000170f12002554800c02c0036843c050960030092002e410310b4544070024050621440006204a0010540808074000c44110042d4161144503d4010401c90480502034000c185003040b00c9802102d02c29480310b0094006920102c62601c5012040c201002020140a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 567964505 1250 567963255 567963269
    0x16031b0c0e060a030308010603091110050a140306030c010e03010e010f0b010e0d0804061b0519020103050105010e091605090a1d010b130b130306090c051c0309090c09050303040e0f01 80
    0xf0700720800100e90005000c506403151032401242c05000c45c2828030046240345502a0084403001150124540c0600501000d1082d40e6030148180312028801c044c40c0410340d0030030340c1900602c925880325030192205013030408010f40082881c0e030185400d0b0b8212040c500526081030f8407890070041075a0f012001056010040303a044140d040603071038014040c084c9028010a00c40001500c09807121300700c0ca58030040d035006040b00c41d1a0043c040c2c882d0000d10000c8101d02003030400d070010699601030303404243c4144000c0d00f01c58056551080790406078500342600024400100b02d8000326451340c508900c064412855040b11902e680010000d0124050780102c1002b2030501050142e200081b40131801c90b015040030b9612002c0c1c4440c00b0403c0034182e40000d01c011319252111041090300d0032403900b1503604864030300c0c0840d800842100c580d02e45900040001c1c0c48488144500d00d01540580c00300411031414103081610b6101107860365005410408440d910305c1d0421262001d050303a107134058a15 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 567965755 1250 567964505 567964519
    0x7020d09080a0c091104080303011404051008031204080d0c05040824070507110901030b040611041a030a090507030c0f0501030b060406050a020a020604170f060601020316031b0c0e06 80
    0x8241c440303d079020307a54001c90003400c0d101d40418800111400903038020700041360541e07039a940d440d103000280b8a1035107902d500803420100020b0000f03851310401c104131450f40024620b44214a445140d600c0b60087c0203e981039401e10049030360b21064410b4032419501510b030a940ca03410850214034104404044007808000d41c00c850300540c0b140082a90070a5450034186d485212500e4125105501c0940c01034100c2007110001041c46018440d240c000c0703002e1034007004031800d59400d840b035074410380c021341d140c140e03d000103c040d445000004581c031582d0140c00003900c0945640d6541070001983c0140d4030b00a282005101401404c086100204000d080411201783ca100200e095400f840c072410080c01004100c10a0041c003d20000841c994001c04455582e5129103280c0003101ca0030b0680c180d1031040591210081c600042c4507401610140c000751f0030007488006624100da841f800403010041ca008800c0d91590702000401c0001d813044080001072401c0c00c188101c258401002c90f44101c4e8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 567967005 1250 567965755 567965773
    0x1180806071d0d030225091407031b020d05070212060108010e100615030c02010e0d1101060f0b04050402090607060c020106140303070b01140301090212010902030d050c060a0f0e030307020d0908 85
    0x3d00000c0014400e2117030110703404107100760086c404014089602503040c0c1404e000810240302c5a5155580c4034a449441c02c1061410021808280140c0d9013000d1001d0780c0501c1c6d0f182005801400507080c090302c01408035080308110440e16050000030381c401052603450700380c02c0d000c1c070790140031030307040c0750b00c418000c00c60325260004c1c1041101b000c3c282e500c1416690255400018400c1d0048170b00000b82c2401c0341d580784d00304100180310710b0151640604a520f011008544030142400300c008552811461900341803e10081100039400141040d5200c0d9042000c64009200da0165440444094000140e12484c1020302c8070350813045040c0070310a8000300110000140c2180e0035505540c61076003212484008400400d0042101e1280658418001c0f04001d0034900150081d02c00b492084d42503030340740d00c2c0380b2005136128011131a81030f107a40c001400044030f0b10066407080c007a40012030400f00c0d5100d100c502e400d003550300680d01c03c030050b000202c0001c0800e0300030058000038401780008140c030030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 567968255 1250 567967005 567967007
    0x307060e061302060703090815010e18030306120f161a120a0f0b13150b2505211207140d05090a0804060f02010e1b01180806071d0d03 59
    0x1444003070b8001c1c45030002150b02c4003070506c00c0360b401000d030003001708680128020620700c1218240902c15240524624000552a8204081da251642036400000d6095803140d2041200e540100100002688900c608207803141d102044990000c40d94242c01d56200d9003400803032031060101c031103800c40b684000c101009440001c01900e503802400024002842e0f440c00036600050410b0006180d170000d86102250111a5241d0008d124003503980000c280c03184d0b0b10b04c4648014020f0703000111000380b68030b9000340c00308281c2d0f5006030b44911030030607511082401899190360703c4051100c91003402010607042030442408a010b0741180460a0100301180700202460f05440740d1440039010030348901c0440c0000004026503820142d00080254440703464410044c0131000c111007850066007002803440c440400800d484000d0b000520036190510810001504c000d80c20818202e10a4800440010101814803955015403000d40c0c0d41c02252420003d03440104000400e510704c03460384962180000303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 567969505 1250 567968255 567968281
    0x20a03030305060a03080c0d08090708030909101e050316030803060f0307080a1b0f031a0612100b010f2c0d141c050307080f100807080307060e06 64
    0x880d032618000c074540d035400000c07441e007040682c402020410f01003980c0092920108030707001806410b6480c4103096494080555903601607128000703150300104520300031402c002607100c1d480740a641012078440c2d0384048500400707102868000007085024401d015a02d024010b07045401002c13014005458150b44030030110f0310003e04100c1c400c812000b07007045d181e02d061212740001d10500082e6818400a410709800a01c0d001401e84d4241c4a40c8501140d01c2c9603450b6104252034100340060304405060440301e21302c100113401182c1c06049505c01c000120b01c100144150f0100005001c1403182c4a0710000d082800204144014801d05c4042020409100c0001160500f070f1b02c10060914001d1101244030300e250801c010307001d540c5004499502180008011051f5200c50000c07090303445241d030046941e40801d58900c40050b4007240072503c0341600d4001c0030b4114040d2180c06001d1541c1d2080d45140031403540c00000f5581000c038898090143d030348102c26030300b5444030140c17a2500c2d0600e500000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 567970755 1250 567969505 567969509
    0x1101020307022508010203040b040b010f031e03031416090f0303122d0902031207080313080d0e010f0c0212070330050a0b012303250504031203020403020a 68
    0x202041181c46020321a100880f04010803c200003155a0300345070500700003004040b107041c0c41c041c40d01400099107505040321030302200e820140d0060211000426030f2070f80044141d09408040e100c01c1180707a00d201101086001310a01000d26420002c45035002c4c200c00c4990b489080010302d400c1d03040006c203810100c0c0041d4802038000c00681d0410000c2a036902584002c3c10403004404d01030a007100701d106034003840e4032600071400c5803451449000e000c4482d01c2840d03001400c100b010704c0032a02c900180d0040040340e0303125010b5181480e540c146d003607049412446110004da911000d080d440c10000344100c10039100548064095450804511820351165500003810041c2c2d1007254500d01c0402c41c01e90900d03d2012080026042a13407074248003801c3e0603200710410710f00c0d01410b4101e960165820002d610b074099419004010a50100010f03508004d00d0114000381c1608982148101460209554401c0d0380303c2ca5152802d60406407000814662181c0a06204010900160703540d0440842 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 567972005 1250 567970755 567970783
    0x31501080c130608120a080609060f0f01030e01020c160f060f051b07060306150e0a12030c05011d0609120906070302030c0a2006030f0c0f04150c0201110102030702 72
    0x15000c01d00150b0600101074690000f490341c0100a034441c004581a401003115088542e2041030b90740728201001035513601552421740c466621f8050f8080780c10681c1d00d800c1d222005060000d407801d02e00f0003040c26a448003950501c141c20080c45100700d066a1103030300c80500010159142c03840d081610150081900001c0c0806211011070509036084900c2c0c2030b40c0c0040100c801f96514907039a6100680900320501410b000040750020302060284507401289101100410b41c18000385004c0c41010ba12030118000d90400846024a0b4045442400ba000218028040d00043c1e1085101c0c3c440c01c141e0040d02110b401e4002e410107c1101003180e05942e01c0e040c04803241a62100c540c5816403452265040c42005409030044102c14881c2d41034000081c5884c820381ea2241060403002c000580c40102d42c44128590742001181034040000b01500c0542c0c00c0d0aa45480d003621401034103206101040d05400003514111960211350b40300f0041050b02c904c101c020b6045081034203010b0344840b615007800c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 567973255 1250 567972005 567972019
    0x2d05030c06131203020303071e0903080a030f020f03040b01050d0510150e04110f04020903100902040e03030c030a140105090610031112150303090102060f270c031501080c 75
    0xa85900300d802ea010001e200700400f0481080c0c5510300030751240c0007291140003240001a0b5000f2510b58810701140003540f607a52900d0041c1950703140a0140c21800b1060205582e551203c1c4080700c00e0310043c10346030040c0750066102d20b01072902c080c2507070058104a010300441d6030600d00051000481c540d00c42803038a40480e1a07846526840a140616400190141c2040701480141300f02028209540d00d0165210b0540d2411101400140d01ca80b01200c0c2c3c2540c0903410b080c14070402d6900c04a8000e20042012844820003415245103400c151841c0c0d00c41c00000052000b48207080c815040c0054000289409640c9081c3c000780300c092004000d1b60040d00d0f64101044c505221340c3c080450380884900761500c4032840141c88850510481e080940d0034010703c0102503510300003082d20b20388881640200010303a5044080c40362510003501e503040c0c3e80b426840200001c00800102c04194000300020241922000100341c5465880c0c52140710300090000180403903480032640004244090b1010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 567974505 1250 567973255 567973267
    0x71505030c07020402160b040203010b010509010c110307121a1b09090612060709050325170a0c060c110405070e04150f1d0108071514070b012d05030c06 67
    0x304010b0b06c2201c003000e1140e802040a802008504202c1a002d28004da00070001d0180c0307480103440d00d01c92060b2460102d584213420389d00044034a81c0c201408131000c0c0030348088950341c142c0c201920000c43d108031a81031060848400d410407442c10742c0c2c1d22105c2e003c000201c030310000501c0d24261080c0e4800324050b07412440010039070346610041020102800c02203c949140a040c0144103903031502585109000f400d5034040c0748801403003a00d600c102d030341c4080000146000554400580650f00700191030140d1481c10010444c05021100241003d4860b444290045d2601500c3e0003003417400148202c1c5000f081c00061a409603401c4104c110640d000280d0030340311513a0075602c1900f90b000004044111601003120103295601c00891a1107111f009002c2c3d03260366442e80c49204900808003401c10010311505514890060514103000c0540001e00e841c40daa01d030414801c400340c22407809042ca0806140400045401c0242d2410300282c0c00307000c1f1401d11001a4441c0007007800c85101e44c60104407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 567975755 1250 567974505 567974509
    0x1b030313060c0522060306051906110f0a12030f020a0c032106080307060e1b010f030e01020c010903020705060a0905130605090906100f05060306040903020708070f08071505030c0702 80
    0x11652450425884140d80301124044008160f04c1c40c014400020304007000003807542000103102d182070401c41400000c5500b0003604840f4003a5403201c00070343d03101390814840090340c1880f1030f20b4114040c003002038141c0e15005014040c7c51078809006081c510402074500035030f40c014610407480b94146400c49044040342d81950060b6104800319502c2c515068001640e00300c004018060f00b481410709000d20050914103d071078072003007200d01d904007040002001082d8030404e04001a075880b414002620043c1c14107627400c81e040501c24154984d07442101d1070a00d50100f0035440141401c41707603546042c1d0302100041090b01c0398450a4050075a00c2c503100070b031282e140c0020001e880d020308070a8107440d0031203505588481c143d401c2120741d03070488c00200300d6951491020050760800313003150345180c491006000042012050075400c601a00e00040b0b042c2e0300a1141000030407580c080c1085c0d190034621158280b501a40c04200300f2840c60740e80394180383c0c200702900d03801964080280d80b20491400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 567977005 1250 567975755 567975757
    0x903071713060201050109051513180803090d18060212091807080411030c011d03010e070f030204060e090d0f09090908031905061507030201061a1b030313060c05 71
    0x50440186031501c1000c80d815078150f100da412164804024001c42c0c8448855000d04550004800d8011f0280050080c0040080d08003403050950020040c5076154141c8440c4d80e00e81090361000166000500301600107035100c00c21158070521039640d40c0b4280d00d040c0001c4d6403146540c1d030f28002001e02103445262035440700384072040980c070040c00c0023207498400d90040440700708890846050000b4020b03420141000100b00c920a50103031240240c2c01320b81400003056403c4200410313410340d00d440708074440384010710001000300300c0310307080d00860b504510402050f180550000f9480410f41030422a06490001d24031607ca2024100380701e0f800b403811011207558000342c11115186043c440c0748001c1020800065116001040c82c4046960301d0030104401d60300309561055100b4800c1c00000c050084071402440914402e00001480700d658a20840480c001140d00603048500400c40b184210071415141d402800d00b0005503145140000000d5940c41000c40c0180c0602e41d070701031003414107011300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 567978255 1250 567977005 567977017
    0x151002070f080c0102100b0307030b130f060c11060402030607200d0c020a0501051c050901020c120910020a05100203070e03160303093519030914010809030717 70
    0x40307109500c0d5011560760b8900c4598090062050046885c040310541c1304104a00900602820845203942c8401c1c1c501803000d03040b10004a0442d030142c002445d1400c540c4840c9100da00b01060300d840004014010440c03841d40d07000141c10a00400c001640c000c1005684111181003d0183c951246c0c0034041042c042c0d800c5144078803454005904070f1f900300c244400843d10071640080e2464035a40111014080c1003980e0300c04900700c9510701e43c45000e42d0401580800b208000509181d5183e00841c94070140741300384c0041070f9000a1100701410f144269200f41422400207103030200d0281d4600350354140b2000800d05807503000c4013151090f840354501c0529030000608035580a204564003966540c042e210490100d0107a21000500700b07401d003c54504110000b0001d4101c2100f41081a06042e40525a0170b040c090380e500301d60300540c81c110300c0c80340c50702950707800a0450074500c82e100750a154552540c1030200030310400c01600f1000044070400c035841005000e80f40d045507003002c2e0a0080b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 567979505 1250 567978255 567978269
    0x90f05090c0a02150106230a0503160e0d110a08120d02210108060601030515060a1b0203151621090302070503060901090c050a262e1415100207 63
    0xc500001001d0b940081820900c1d581007c44104c00b4809060090061041800d80c5002c0b4100340000b4103407441103080603100341d0b41818401030400300c807400030f101c002c20320f10110b640c601540c0440409040c06104500a0420700300100019916410000c00a000c0e02aa210070a40c0010318003060f104261011007100d02030700620511542c5510020f40c40f64003c0340c003180000e1a00740000c03660400441201186078001d44560b1400380c504d08200e49640714500011404030884801c140141c60401040740d0440d00b080c4604141e0030034204400842122180c0d41040008a1510f04100c08001d1800d154051503070b840016140c06501c0e060303007404260352100da814000c1d04200081c9988c190481c84c03107513100e014055050390700d4400708031002119005000750021404014a05211200810204003404008a070192124403080c0d0808905085140d81c600108078148041d25a5034052120b8180400c01464400d01c1c005800180e02141046024854503043c0500d001e440d0090200368040d000b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 567980755 1250 567979505 567979543
    0x30a0c1b090f0506030f010921050c161d0705030109180213020d0b1806040e070e0403050406080708071409210601050f09010303020307080a030605040e010507090f05090c0a02 77
    0xd40b0b0421004003000c45a69020f4014030b03070a410002e4041c840c0d209840e50003560500070340403102d40c5010050390302d81c0c60000d00c181000b400d41c0002e4108010083c1d003410004a250490030300e042e10000e0403803034100f900c0002080082c0201e0a40100541e819603045510000750303407000e103000c0f128440d030a0360040c1d049102d04600340e81e0103096800800b80700002c1c407024003079010140c0a014058644200450003c40c0400105809103045d4005051651020701103500407910344004c00c04000050340c0442c041100042c0410000e9001401c1070f134406940c0c24611482d18164002034000c844400d0812100100082c095483c1c1e586d003030700003c3c0b01c60302003400000c5a01444007165200401c1c003645100d00360300b28104c90f0700d14210861505907a490b80c0950709200030350380d40740540e420000c0000d0038541c0700c20002c5500d4030340703200300d0f101050740000110b918102498041c02480f00e40d04607645029103590184000c0c3c03900f020007038200a9642e880b65503007000080403810030700c199080c59a00c1d04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 567982005 1250 567980755 567980771
    0x90804030209160e03030c070e063607050a02030a0311040b04120b090109350d0504030e0901051014040509180d0206100e07211a03030a0c1b09 63
    0x194920003034021000e507403113281c211100041015502c0c01a030131500c003a0390128805120007032400e13844980016000e41031210711070340c02c07072000300500b1160303000501104c180d0155040111b01200c0c0076003003000d42c28082e10300301d1009002505c80c0300700c1035410b05041d1695840c840106103242105c0090403100581a00c0e2074650100c2d41009110305000e40e01004038002048080340113200e4001003aa20009060b121499080580c1c032011340c030340035034a01c08034030446145000f045038020b004009c1411070010300e600e800c0c50094070b002100c1c1c49042c06401140010302030750f00c0d0340840c41c0c2e14043c01e0600074403620b80090804ca891086402a54004003031700103011061101d114522071900d0380600383c1e145100b502104030798031002243c0010031802000c108103c0051840072043c0c200c46a0b24000c40c00d5480c00000001100201c000d0025680e80c9e046815085620f171180b00400120480245191210302c03c0300410441240c0300241202e807400e00200c5103c0c60305c12145000701006202402184 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 567983255 1250 567982005 567982021
    0x80a110304141f0e0d0c0909151a0a050d080c030706090519030806090403050c1c030b010e03120c0f100f0c08060a0b160c0905010303140c060109090804030209 70
    0x502c948545000300b10301a1400294103072484000d608002683d03d680c2a900306004021003a6424001130b10083c3d49040089012021800f910b0900c07401400e50030300031a8860350b0f02e001c591141084060480700c124004540d0740d28903800800f128000c4820a0000480d401d0030f05c21486100003091540c0300024031041001519081001682c0c081d07016181c0c080084410f41001d428240c1d030080010b41d1850025035580380680d503260700b05001c0d01c0d2003420300040440c134521302580d00d914441c22640352400c10b2580380e851301501503003503c01e113010109400c11201103503480541c040e00d0b8070080e41c00701d002c098031002000201030280c03a5100301c0d040201c00e01c5c6400000c20b040104002400d08040b8500c2c8440e006010f01401003d01900c01b40d0500d1800702c14104a40040a10110a615505200010a9600c40c00001500d960100010716524528000d040300d4000203413001801010f00241001c5100400c40b81e04581030110302144405403490710790842c0c404c0d03410082d800880ca10502c9186 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 567984505 1250 567983255 567983279
    0x1020909090d030623130207080a0e0a08010e121b0d1707080c090d020a171b01020a05030d050702070f0b09010801081c030207140601061e1803080a110304 68
    0x590540b8100003050301c0782c820740300c1e09403964aa1011502007610340c5c981400e000c4440341a10615120040c100a51a5609012070b0700c00303140e42d00007032511600c1d0192072030007408440040404400030001c1c88055200c1c6c6840d0f002140464406c00c001080d44848411248101c10b00743d04803c0c2607404051401001400345e610f1625400c5001207582c0000d1082405408a03600072074010600605011042003040703a60b291090f400c03030300800304000020b1001020508040303510001d9014145030340c041c880c200242d101010615046510a40c140700c08207401200311841d11000090208441c0d0b90541c09130714100043e4801c2d1107800c01030030300003400745102c405000000c50980c0c50317003031a0341e803003d00070b0b540c1000501080300c480002100f502400d00907401000e0051060030124a004001c1c0209401c0440076800800824888040104201f07038030700c51400340d0352040c2042420401c000e454402c4840082c000240080800201e1055880c000d0f6120311003520003400716903540751540c90710251 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 567985611 1106 567984505 567984523
    0x190c080415020c060f0901021006120f080c10021207092409051f08011d070e1801061d01031b1808030307021e0307030207050103020c0102090909 64
    0x1036100d2a010340f07002140e400c1c17982e40307130f80c1e42d0b1001900740a900c41d80b0032440c0d8a000d00502488035000b212404481c1c011040131402011494248481d1240e2840d411040c41544440140500c00c0c0d0000c00201082001c2c405854039402c1055a055040f40a0001c0141030f0403c400030a020f041c00200081c0214600402c0303865864000c5400c1d010741c0d070038941c01181641e030302c1c25040b40c01000590052114001d4010000700f0384600b1020301001810050421103100030190441d598004051806002401c0600c459691014007a010070201e8044101c440f0000c404c6113040e60180c8103040d00101800003103082c1c0c4101160403107419980700c1c42031040d40e000b13940100e01c0d030908001552141c0755a40080030a1000c4003140c03200d0780d41c4008081c9180d407040064000107a0301050a600b124000c0c00c0140e01e443c01114001d0180c001c00043e9600154210b0400081d01c90004281e44 = true := by decide +kernel

theorem cover : BRFrame.Cov 567805755 567985611 := by
  have h0 := BRFrame.cov_init 567805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 567805755 ≤ n) (h2 : n < 567985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
