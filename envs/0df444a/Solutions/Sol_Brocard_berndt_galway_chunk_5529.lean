-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5529
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:09:51.75609+00:00
-- url     : https://prove2.me/submissions/2932171b-d0a7-470c-a46d-ce69c9ed0321

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 994244604 ≤ n < 994424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 994245854 1250 994244604 994244611
    0x90703093801120302060f04081204050a030206071b020d170a0c11040c1202340507050f060702120114012d260c0d030503010501090b030708070e0d05010e06 69
    0x9103501e0749a81c1c41c802808007809201c0050096000f100100fa016189821030030b5109000e040034078070301440042d500d031661904660503a503940140e00704508150741800495006001442e02008844207540700034048140310000a110307003060a11541042a10301c503610302140752003611030320b50050f450080c11500540804540315080e2070302020340e0385041c1c4a11400c00c41603589800c2429800401e1500a41c04070316007111003450480c0509580750b403a0003450f8030281c40c810950501d50a8034000f450050740d0340020303101e8014900c4144442e10384005880506804071103442c3c000c0742c05100d0500500203141c3d00640d10b400640049a6102a0a21590b46001e550160040281e41c089442d10030b4107070740100d0001c807011680c40781b071501c140c503540405002c440e030a84900a00e440d00013040d01d081010b0480129001000410003507811000060040002c28141782c594a08800c1c010038a4400410b44024041108036203d040c0c0c840402000c80d113070340f00000f008840c0740400a036540316401ca = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 994247104 1250 994245854 994245953
    0x90b01030b060d0b01080a06031a04080c0105161818270c0e07050c07032003010501090905011104270b090439050405060613030807030905090609070309 67
    0x8001f00d00c0c042c0b000c0c8200011a07800110075051100342c0241c00c14105c81c080c10540b000841482405d403002400e12a80e4021740c0101215141c801c08a500038104212003202c4080f6100e080e00101711401b00070710a2061240c68040001e40c1c540801d0500d692440ca8400d0220305039420075880003045000d0f001d500545e10060106071860741c030b03828110703128070905c0040302c295001483d0800c0083d1002c800440001921110f5040000c22907002c242114801d034040074650740c0307410030314060280070f1191003460b5102d0a120303494182030070b50030042c80714056510f04900b40150103d50100b01541e00070f42a20000606000e42400c06040c584089905546d18226451461454125071745404008401d8414140d8120700c0061038000ac0000500c8000c26003038208804100010b60303044c882c401003000e54810f24103a03495500c241001041000550042405050000180015580d401400c2079119101d403402060a0311703d45402086902d00d1011003460704030004c10f05088102c584c4a0075143c9003107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 994248354 1250 994247104 994247117
    0x813080303040311010f0507021903030e010c030515030c0d0b1e09011a01030e0c01050309070e040804030b0c09090a052a041d040305310b0307020d1107090b01030b060d0b01 76
    0x7459021ba00315081070b01c215002d6030040d840c881e503200e0300c82c0e44141c07000d000341030000d5001a110b030110b003034035046c41202c40026540d1003001882d5075060343d860042c500542c014800040f00038081f504410251030040c0409800c000054503400689411843c0e151403049841c0c81c60401780003082c0a4105001e0f20392100c5d51240c0c55111951080c410510281c14030f40091140c2c004c403070019102a4000b92414960b03000700350005c510043e144060900441c032881c2100d07a60b42c50742c148250120405000c00f4070068080001c18050350300c1c0509681c020842c1d2000180e035803134084140b09640900c0610245803c0381280d8a440440c2e241c020b00102c81d00c0120b2a07408000381910340420500c100c40060100d882805400e14215507200f24a80103078404d070490032090074404640c0a9007820b640040750780500042080a055414050b6650107006424407660541c4106d80ea2922600d00b0b00556034442d58030403070707480c0d00ea2080d00482e825500107030141da41c5050103820303000a803440c0e06040340810071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 994249604 1250 994248354 994248371
    0x7060c0b090604080d1107062301081507300b03010b040b0d0803040f1403070303062103180915060e01080708130c05030115091a010903081308030304031101 69
    0x1c1c085901842944d00c00200e03854650741700340d0080100700041003420220300600c0481c0020b8450f20a0245880000091500c0400c80c040c00810f100016045047d190b0000d842d01c11002403034458054001d00c960a04105102c61151440d070000142120040350a194682000c0c0d01389544d030011a00020a500911000a00c001800250b440710300960b9003041e021453320300462924000355070024400c00341c0f130840b24110b441d2500912800302e8494a80c1c0c000240c04030800d50580311f040d008100d5600039914080401c402450451807800016042c00905e16070798502000201c80d40c805085490401c1103c0c03401d40d100300e201201c142c0104800308034040d05002256002e0555140b00320110350303441441e070759031144025008880e98070440c2c51141109010410740d07030a0058080302207540e0359011403d450000d501b4144c41c0098045c4200e40c41000c00b0b444145d900030000001c1da0340209810b41d271950701921030380c665115640f290b10107009c040f0070311041541c0700c0381d03200d00004c03070b40003d00180c0d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 994250854 1250 994249604 994249621
    0xf1e120807031109030c040f140a020918090a0308070e0d0c180b090103060e070b03040510051f0b0c030c0d0c1203021303030c050c060d0c140304030806060c010e07060c0b 75
    0x105004c0d445034594000d02c2076003440e24140d00101521411207002090b81014004048403450f002e5030451151038000c1a04000380c10000c6d805540c000740c80414002e80e061805d6081d480c2c0e440288084d0420150100148040b4061482400000006006c03c610500076080c4400362007060f0050913412140307031511140c0241e080c000e442007210000c0c4408400c2c0d285a68940040002841d4021a80581c100c00500080914003461195002d10042d1070503d0600000004440004041d00d03080a61000e0500f030103421921104140c0c0d030040710450b520000b6403001fa2940c000d894003500c0030312401c40c003030242c185c2c41140101120312030210440800c4980b8400c0c0d003030340100d0300c11103e140100c42c01000802d2064114074503d0780580b058412074244007020490f554090103140c0c1c0340c01c0c0c55200000e29554040c162500b03c2200305511800d505103940c0091100d00040c0c03c6600ca40c801240c0c810700d0403402e5000460070843d6030112406d041e5600300180800094100699094210000051600c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 994252104 1250 994250854 994250857
    0xb0403061b021e0f0102030114031606050f090d080307050a080f282a090902070203060109090507090608060610051801050d02070804090f0b0d0f1e1208070311 70
    0x70865006030129621290f80001c54248404042d8814890368030903035010b20080c4000c6005e011041e0030011000108410f043c5450760032090110303400040740c1d04000d5540c0c0034068036040410602c0f80c66940c220709000170341e80300380c0c8100a010f0107000010701030441d4104000b412101402e4480e105a50345d10031300c0ca0b201e1901140e844807515a00f9160320781800000d0061517020014070800920150035008101020300000c000340048070782d5000640d54550041c40050090503c090250319040c03669000c039451305810700c54034500c4c94131138041c02c0800c84203000b8200581403100007000f42660390f42d60f40d03503a42000d4813418002c010528003146158490030071603c01c18201c001042d00300781035100441c0c03280e001c00f002d19606642032105038005094500140020040c4900104241071025011011142c1c000659486030a071511305a0000c1c075040741082c0c0700c3e50442e50841980307000d989143c0030b103045507600602c11501c02c06591140d5402907081c41c003c2031143c1d0100030b20742d050300c0c014856 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 994253354 1250 994252104 994252151
    0x3190b030a0c0302130e1b130b060906090307081002070b010f030b0f0c160c030b07110d0c020301020d050f1801061d0a020403050102130314150c090a0f0b040306 71
    0x2082c40044050000d41004c3c1e210b104030300604440001c0e5040d10500c0075081c1040d6079000e4154240a198015891a208034041d400074003910040104200b01e02c002007051149402490040402044d615425034042c0001d0000b004400141e030300040c40410f0640c0258031038542181c03800b10300000400c0c0c0c1d2520038605001c0ea079002c0f5070452180c0b144000d40441e5140240f0b64184010200030307a001541c6511003000b6110700c03404204500038114a040b00400c0c1005141408000c2e168010b0798400f00b00048070120345240d410644454040742c00803a000e8490700c00340401d514109414030007507000c4150342910414544a5239440e61041c8640b03070b42602ca1a10562200008440114205040c1110060b070044240f10f001031405559640e00c03030130790700301c4070704010328a08070507041051040c0c45c800090521510030190020310403110340c1d440c0c4043c01811005540314040b804045030380b248290100500424503550309074a58903c00381003554068002102c2c080e0800750070102516542c0034a200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 994254604 1250 994253354 994253363
    0x4170304030f1d12030d24061202071a190e0606190347070f0c0b09060702100e191a0705090f0d02030a0b060f0603190b030a 55
    0x81c000030031201100c00c070807210b4072001a4a03240c008403280d0360700d010310b4110300074404c005903032141102c0581008032404135600d8054140107034083e951101c0c90511180640c0e015080021250005106030030084c09120001089201510001c10241c080d4803640d900c900041c0b102400d5842c14a0040029101002810001588190040b035007600d1f04040c4141e4200b0340304030858416960f0f40f02c08207402c26901c9034a84107954000745004400003501000d8807500d483c00900d0884154016418004c84024042c1040100c52000707180b04500c01d484503640e1640100032401c95090503c1050380b5010305541000161050700d82d0b01c10480c1e854011541c600c10400d0142820b1400740d88880c10510100c141260420f0700e400c02d039514110b01ca201c0e50700030702c45d6030740300c5454011f1813060158035458003501c07621416844c3e410341d00581d00010103603d1107502c000300740ca1a46401c004500c103940c00550899000d400841000b0803440405c24207003a0780000d101c00d11006052109040d11501000310180c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 994255854 1250 994254604 994254617
    0x5030c192015040b13020913121806050307050c1f061e050d020d0c1403060a0207051f11040b090f0a0f0603051003020a03050d030e010501080a060b060405030111030417030403 77
    0x3c01080440c08099480f00d4002d4150800c2c01e00e035400680e01e40703000c580044c6d880814040007018098040541c880c2900345081850340c0c203003600c0c864401d07128648a000d040090000004403858862026240d41d00c00300c808451800f04c4e10070b0074011548a20012851175031505c54002074246080064600c1c4100f02500108600d041c402030144403428014140c3c0c101000c0c40700c0c40005101c1e2040d19000f0030300b040c03000c91000b8014003010304010000c0c01800c4018014061100031400111700000c5400003040c06000010802852001610108040300e680110101c0c002a24070080802490b1703440b812034110007001c2040d420003501c50b07140d025090484ea090309050100a009030701180d04003142404241c5140d0707032076000030340000c09a00106c4040d0494203050590340e4141c007038002102e207120000d0100f0b6043c00b244654801d002400604415110425000c0c0b548a00c0c045401401002d4020b228508641429180d20303402a101103e5021143c50803040201d500c01c141c034002c950650300c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 994257104 1250 994255854 994255861
    0x60112060f02040b130806060315061c0b010b04050301050603010606080115091503060330050a1709060105011b020303030604050a020d0e16060e0307050105030c192015 74
    0xd0051210800e0205519401c00c0302241c0b08040d90003501411103814241c420540c100050103050110240c11f06000ba40145000d517400c080c1c0c0800d07150721203002ea0300c07001e018a0a1031700c0d03030109003950405007100740844000319141c900b075801402941c07804c1d4000d21541d100c4a00345400c0b00e1291140c100040d2041005010b85002d600300d9055111007890b2410720706807601d02880c031190080c6150381c0402c4c0d540b40c0070800c00c1840031806038080b1410424492140d090519070100c440c005850500708070001900c0d00c01d050040030442d40d40354210300a5103103881c1010403540e64440a00030680401c4003007841007070180202000c0b891150780170300690700310307200c50007484081c18019000c99001a001d00401980724298400c40d000a00c445000b40108000c000501c000340615401c182c2c00c21144040b00602c40e18001400000c130b035428a8907555076510703809039141a015200201840143c46403003c81c2250340642d400003c4202c4c10901484041d0701441e0b1075861202d002c40d20403462000707002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 994258354 1250 994257104 994257113
    0x170f030706020c0f12031b07020915042c06101805040201050909091b1206041719090302031203010e04110130180305030f09071a0307030c02060112 65
    0x703850031885040803030b8130840100401070300302408101410f01400d0301001700400c1019030a074241ca0340e8500c0d007145207890980d802240002c0002010107404404400c2490302903101d5502110a02c840d80e41d080310780421801d4003020408045904209911403080450b01e41041c0305102001c6501c2c8080040710748403078400b0f12000d4030000340b0a0f030521805101e02e0582c2d40750004800e20848140002d40340e011b98a070401382189100700c0782c182c00b40e1142485641c1107000081d1a58009030040d91900700307400020700488140c840c1034244404100458980060340e5007100f092419a48204d0136292402940034107440240001d201d01c07003424000700003040201d0002c10540c0c070794801c18035040c500c189400c120100b085d420307084148207101c00c01024a0301e243c2184101031543d1001c0034811032200d0b06450003460f601000d81015955441d510101d00001410000b075001042052000070120388829980641c50f00100c0c0e0b900c1c0800d0a2030340d004803452000c85c03094141c1d6400403074030201c41c18640301c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 994259604 1250 994258354 994258357
    0x7051c02150907090504083402040906020408010617191e0203120301061115010303050f0c07081506090901050105010203030a020d0f05090d12110910032004170f03070602 75
    0x4250024051007901140c83d64130303401494031550040c0e10300743c0d5401402c00e1300c1e00d48008101200344030704078000381d424040d2030a00d000900e00b501240e01188503111820910000d104550158450b0340c07034503000240e4425803404c13201d0414110415102010a0f00e110201107074500c10004002890502c0144003100c80103c5498403180041d0440d441d034020459071045951003a003203100882c40c250a28020381500300101e21440d00f1003596040035500d0741c2c1d0003514500501d14614a0040f01103114400c50800300014002003c070306c4215080b0040309101d81403440c100740c91031401003480c0800598040e40500804d412a003060340111b00c0c5030340b540540340007900080c03114802103884d1486407690026500405020305110805400810741e200c00152500a028000d083c001d8203141c0400301000d81001a01d81060041c1c41c4588103d00c4188118020440106506101c21408840750552101070b00500301342c0c3d490400d41c0c54507404080105a6829550700c0600305540100005800141c00341c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 994260854 1250 994259604 994259611
    0x61205090a0b15040f0b030c030307120f021005010303031409030c0a08030703090f1101030e0607050904110f070c090e03071707030e18150604080a020427050307051c0215 75
    0x29028003c501e410006081d1186003e034004041c2d1603821003103844c902031141e040001c500302c0003180381400d0341c1d440005142c46208120180119880b60710b69050003440303000c02448003504108a25038682c640a030040c0fa8400700c01d180b10b9804000100b07040d4001040fa0a81e108190041c00f040406a58000b11980b0042035081016107409400e00010303405080701c00b605d480f48403d01191400390300010111220700c1c018202542c404400c1c88070140d0404200c6d03a00e03d1080d94041012407440203003c145207e2030464001c1c1c020005001021301011107141403d403a201c80b070502c880350441c01d81c142d5a0090103000303828440c0950341d000c0b9102880707004080d000d1003410900c20000b221400a2800d000200300111800b94880801540d03103100d1002080a800440f009030605040c200d03620381e50911031000030300482c3d0300d600c1008084044101100c01181100c1440e501585d1441d21607101e4000d44000c4840c3c1c4a40109004542007002c58540400c0c6103a00504040364414a114107039500a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 994262104 1250 994260854 994260871
    0x3060302062217031803060402100c05010603150207020a060206060a06050c0109050303010b0d050a0921020c101808191e0209040809030d0e210f070906061205090a0b 73
    0x4640016403070f030410001200300038584000d1500d412580e59076407191001140f04901c01d820050810005a07604080c91400d20414604000c1001c2d540c90200d004001d107420150140e0b59902000e412603001d90000c0403140d10940358100525526001a030340c030f843c1668034550180c10180c085c0801071241001d40000180003001041b15403007621880d0035540280c0148650131400240440c40102a028813900092000020400894240c40f0b91001d0703260580203441c20b8414103803207045540b00f042400c0000400520070003070071044040c040c1c011120086205c03000c0c2c152410024202070701281191156103000d020890a4a095444005180c0d107040c0468880010003205130150719040380c1e181c440ca10036458070b5582d800c00c200701450a84000e6282c402c110404038610300e103440704075131725050380c00c2c10307058015002d001c038219414101400398050803445100f0b000540e02603d0b40000e402c071941034030bd10404e403c84042c0041501c0d030881d00c4e0303076803940503244401c00900c10550059108104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 994263354 1250 994262104 994262167
    0x110109060e190b0c03040611150a05190c0519030608100908070b0106030b2e120b130c09060203070f0b07030b090a0b04053d1d07020705010306030206 66
    0xd9100f00d4886030840f4910002660010405000c09a0011000550381010000910000000c000303100384040c8014071400741d2544030701c003061440305001c01600c444042441c06001e040d6040200505e150006040c011503910360121161540c1c1c000c1c4a880d040e039039014042c00c10381ca10494104050f118041048400400c200101004038400042c01406000c0300d950100d144030103901000901040c011310041d2004100080c0f4540c805c82c0c580980415105027001011241d0803c00d80300185005400150005103081540384140c619510190034200c50303840b1065116207440301260380740030345c000040c4000703100b04d28400420120101c0aa110b26645000320390b08008034040f841f5180103403644016143c03034038141c44c80361a06003d02d0354800c03a240c10300307110080c000c500c01c80b000b0103c090003445080d00300c80e100020f41890101780d01410718103000158840c01c8046040c2031140c00c41c0d608005000380440800d0640c030078080c0c00201c0350010b00c1c690400314041c0401417284940100c0390fa42249 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 994264604 1250 994263354 994263359
    0x607050303010806060a060f1710120b04021806010f0302030903040b07061506020c180a09061e110a05071203060302030d020f060109140c031e010e0103110109060e19 73
    0x14104001c5002c0d19080307029001c1420b00380140f00c8014001d800c03032420300254001c4440c0c0242e01c100d02c001c505031001d00e80d00b459203031031507440c14500d0705801040d4210301080b244800e00420002d40c3d80103504c02d4130304181c2070906a00550722840103803480f030b0004035442c0c0b014400ca07101c1d401031500720030400280c0b45825a0340c03001480680c040e140480703006407074a0200400340c060b200b11f0001041d8900147c452090620001100c0503221651038800e0302e00b07400400c901c05244d500495260358072801c100641080e514001c900156000c04820b105401d2805c0d4110710b401c086e040d9001d8000039241e6a041500c01c5d5204d8500b000e20702103a104140c0c0e40d10001000d42d07000c004015a0400300e4015180d03112030180f42900749203050b000038100600702400c6005c40444075000c2035200c0381481c402038503038582d250340800d21002c507184c8041c415410310011403550802508141203a1254001c0080e450b079500c01501c00001d03034030540d000704808120109135420100c40c00020b800131001000c102a8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 994265854 1250 994264604 994264613
    0xb0a050409020f090703060e040c052706130207020306040f0507060203070506060d051501091a0301050c0a0c083609100509100b0c0607110f0309060a0e040f092307140607 75
    0x31202541d0212800c54100702a040030360200f81740004206000f04800407033112002e06c542c015080f41d01030031580313004001401144d8103490905900070161007403404c042c04c0241c81c00005100c2075656000d20080010044d0001040320101c580c090080c00960740c1e204100300d800482208248c640f80207007020020000d41c140082400703007107031020001c0c0c4100380b00c0071402604035900741d00b4080da1400b002d001164590750140c440000c000d28000c400399845141000310740c050307000c54546a00c00380321503200b00078585003894900700d468104425007079844020008800426140c80b21844580321050101b424146039696201c046030784034003060382d43c4100320840c950008c0304140c81d5811401c184500583d02208181c0000000302c0145140400c6c02200c64883c801c8040c03180c03141e400040c2494000d401500d02a281040007002003103130540300300000b4050f16094000315000b000740610714196000200c0e0f681c810f2003028000709041400c00c0c0000c1c2022100c01e030003a40c0107105000010005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 994267104 1250 994265854 994265879
    0x60c02042313030806030c0306010308031005060a0309050606101d061b06060f090402181b0706020702040f0509030a4e140606030a0603060f0b0a050409020f09070306 73
    0x32414110b281c2c4100265040080c1a100050000e82c440d4019114202c1d1940e400503005064a0f000b54025a40b9101d8800050319810320f80e004a81111011a100b224203803d41d00000220f401102650a640e968a04100c1d401b801e420b0f004000c03410440060003022520600e88024480c050a014603101072400104c4010081240c040d1940c1d12142c100600c9080c500860070603a40c3c140c0e60019542003507400a00c0c01110f00c41c4a43d04111408001103d8004030300e404503c1e501402095940c0b1400b5051440280d4002142a03001d40d0915004084c00011482801c0c8120503105c00303581400e00300441121408500036080a6090358580100d180d03140003041040144603503005000402c3c115000e14640a00c008948850949440310010326124004181135002030103c0da160368036551441014000d040301d80014002c58540210340b2280d0391194807089000b84201c44002c8950740e01c1c000c1109444204100075044a0180240c134100e0a09031140d6411504600f0301080241d01c400c1815140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 994268354 1250 994267104 994267111
    0x901030b040f1a040b1c03020703020a15020c030a1502072402370c051c080a060f2108070b070e15130308030604021309020409060e01060c020423 64
    0x40581d940f40c2c151a8100c458810016400c040d02c040c0708400305500000c000301c019090200e910b034140c2d10244101842440031038003071640103003007070201ca8482d0007070741102101d04200c04c05442003841352689441d0000b85800041e82c406002d01070540c1c1c40c52100d020b900001c4044913103080a9418030240304141d150034482112a1b4401a02c500d00c00040f601110510341100850100d401c001d034140e02504203045001a0142c100358010044a207002c628003049108509980c0c410851180010340d888610180600c501010500c2015128042e94464001510801c1280b8034201c11b0500c01c0c400b810842c6040358040e8080f80e0400644d5100d03140701d80e004a41010010304804ca0000c02458031080c05800301c603452060702c1c103000c00b0300c070002d4040e00701c0d000c0a01620000300000314180c2e00c0f501101e05c1d06448010074805240d45024850194202c4d001d11950301d801e00001151204011903194100c0e080759860b00303440090780c0c080c03200428003500741400403219400c20007404071035200050f00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 994269604 1250 994268354 994268381
    0x10b0a03050f01051b07060c1b0c0303200601090c02010213030804180216030309020301151d1e22060606170916050f03010f1d070b0f0f0901030b04 65
    0xa0104141d0090703404c440c4000c0c0420030190b02c14482d2004d03c1000c8003901d000d0750340550b002407208080e6000760342c0074020307407a060005040070b841c02080001c01c1295100300c81c4251200c100790500310401e400064091580020103901000c01004003903034503000b03511044140c0c000180f8200464031503004c80031264200f906c070544000b5080201410f90076441e20300000501d811414480c4250107500c40c001d250101a0805403140c0116095550a51203c10b89d0300003001240c505565440c2d4100800e82c03110303505001800030b0400110780b4940326014007080243c12481c0308039903587c0d401200c030342c406501540203110310318030740400029241d21541e8060003103503c2d42100169846035511305d01c1c80040130390016400c074104440c0a6420b000404003910000c990084c901d44c1d0301d90100340100a00c1200d01e03075090402c890344110014041c804141c2c00038110564101030745540d0641018855015824070000082005911b08034644000c0c012040c0d052601140519240c40020191240d01302c0044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 994270854 1250 994269604 994269613
    0xc08030a0e06030103080703050702130e0714040c0504061b0210081801090209061c0c0902030f10060206060105030c0706050903130501080f01030f1b0608070807020606030d050c010b0a0305 83
    0xd003504220010090700d4110307152407856045030f80d114070314014108014180000825500115038400d0070668541d0080181000b240320740040c6280e640045d840360042095007a10040d41d40d040c03501a022100f9142d80b21a480c0601e4000c00315407445c00102483c031207088260700d07800144e96541d40409004119604c4400900700b0810145888840710914003281c3e05d0010030380c0058070b480411f658020800c07500740200d200070840c0c0c003010040c1a01d0040102d01c1611010520042c55409035009103c0b1030000040ba650b40700525006405074054100075031700c00c100080c0c0b103601c103600071a4040c00e00200681028104d90350101564001e894294890f0070104403803d0075001101090000c2c00240f80449050404286980c0342d6441800b0140c00800c20b1003004080c098640303241d4456130540c4c2008a000ca5039082c00030500501603a404001680d4039002c43c42c42c510010b102030140c440103000d09010b800c032074001e84255001c10b030942c1540d5210f00310900c56554500d6a040110301480140c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 994272104 1250 994270854 994270867
    0x1209031101020c03120c07031401060311090c0301140f030a0f03021023060103020c03031302041a0f040e100903120608060702120c030d0204090e0709110f090d0c0803 73
    0x400103484606440c90443d807091503201c205940006a04d400003a0820280ea40d0746114840c1a0174803c0e01c0c0c00c050054a480d28243d0100441540541c2c00c490140ea103620200e6443d004110b182c0e01c05503a031050010042c401130200080416083c1180c1d100100b40702c0c02020f03410082800c1454141c0260f600c000c101c00e417a0289a0140070390700c442d03242c0160810a1040007800c6440c1420380031000b48030b10303402e03000184907039019a04840000c54130a003102e88a10303180c1c081c0309030300341072401c2240030703e0620301c0c40c90403480000c0141c024803074010503106081030300909020050040b2400c43d0304511409010049084c0544900300b980750013a6035034000060304114000690303000358003040303a5512207420444401c6c0c0c08100e6400c01c3e203007460815030718082d0000031444d600610f03589089080c400180065002e120b0b5022000c80b84c02c000c02e0701c1d151562003070310f42d003203800f00801d07103050400c1000310703841107481980240511200200044014182034840c60440c6443e500803000a62001844 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 994273354 1250 994272104 994272113
    0x1d070c171308010e07171908031909080702090720010b013e03040902121608160c05150f1905010b04180e06090d1101050f0402120a120903 61
    0x2000030b401c0101c024050098402d40680c1c1ea01414414540091480381c039896a064062140510070781c150b441e0102170151070704003030840b5070080c0d603007161009400c2d040100d4245140250b64030150011180d07810080a5001d100799000028401ca0401c030082120b0071680b13603070510310929505040000150390b0180c0d00050503c2c40c02060180d4040c0d01c940443d41207c0320160003840b0020240480803c8190301183c081c81d60017039422204036903001160011050f104507400307034030600d503400c544207440c00120030039030b00103030f0540d0f4480c59070201e8220520264022040440030a20907012154407081407000341100440c255000c40d5503141d00c02c00d2110a4095405541740302e60646020082c5524100342050f0b18452841030380f0b605981c04143c02c3d440c3d0001d038442c509280303c003415521030b850a0001d680d20303491540940c001140b00c500015a446105200740e81c41840040b00b00c0d0302a8440e034081141800711410290079503c1109a06070001b541c03c0b0514240a0540e124038504904500c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 994274604 1250 994273354 994273387
    0xf05011202031302041113150f0f080f101205030904152d030609050c12031201050402130803041403100507050714120a0203040f050105041d070c17 65
    0x40141920300500078040048842a0303603c422039070468000a10040c5146140918050040c2c15103847c00140c5001031194103400f80d207060b01c0d86994501d802d00820400a0b28800031070140c0c44001241c07240005d4040c001c0480d035a8000d00b4503802482c5d056a191000e0542c000080d038100d83c1a0000308840c2c190707040c80c1c0900718585005201041740f00d820b242aa290315100d0040366046401c040602604804048443d94055a002030090040b01070a007811a600d54016074074074000d01c0c04141c030991000c0080309a4103c046d4044099200342d02c0c10080001039000325054848003403907a9400a482642040100002c042c501c0d00300d14404044020075003090700801e00300704d42c14144810403c3c2c182e8880200c90002c1d5000e00d214141d602c000e0000c07460000300500424a800d0009444401c40303400001500c00c81d16250506911240c03a0f8004550501030b45c46a1051150001222200034846103a1164054400d181c01400c100301601d4034a40100b014184030701d504000510800c04950740030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 994275854 1250 994274604 994274627
    0xd0f0b01020c0907030c0c0611180405010f050904170a2706120f0608100f060504090b0601080a0f020a0e01030c0c1e03050c010c020c1806090a1a0a0f0501 68
    0xb400340401400701288000000a2407141096558501e450300b407030041c01011101030300310308204500400c007904c410741948090340c000d00c07040ea904020b69035443d150240074169000124045842e40c6000c0500441510150048a02da60260b5402000c58647ca01909405000e5650989040d01401303010035484004044c0030481d41c554403082c00010340102a2a0003102c3c48070300051204200e60319100200125040080076000f01c501055004640782c01c00c1c4c8150303400120030490b040e5980d0801084400c280c400410de8a40803001503060360040e06841d9000411002c040340c08030000c19000200da010514510108090302240d50155a261003002642d030000d060829a5034466110690084200101641d0307064820700fa11080612800940b04a036140300020301a4110000010b511044940101c501400c0a0355000502e40300c4e03c02098003521002e0007a40c181d854003180031700503248409030070b01c600c00148640903d50700d640f98018024142d03546c02000c243d00b4080010f0440650380c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 994277104 1250 994275854 994275857
    0x30d1e020408121c0c0801090e07050d1410090819170105060d140f01051503070e1905120f0d020c2d06030907060816080a0b03030904020d0f0b01 64
    0x5101c1801001e60000c1e030000b00aa10030003854450714641d030708246104800c400070342c100d4100201030800a4118070100c0c181e0b140d00c00113120708802e0804a60740c400d40ca1240039440f0350010341000200e48014242c80b103091104082d1244c400d41300d1090410386d01c1c0307c04211001d00c400103c3d440c0e0301c80c0581c1d400440030781034039258486885100c4030007a000810301416220307010005101024000f154440d104500c81305001c105180381505514009034800d114041c054400c003282c10040c0040c0d841101e00c03804103901c510030084d2110090260341c0c0c031609400c031a606002c1e103020036907907030b0001c1241381359001030000d00c14460380c904075908000c07141080000b50341c0195003442107030307444000c14070608610b00d19084104110040c1040c004049600c0d030358102c1000402d2000c60100810f0340380a80d50180ca54600c1511405054221415148100070006445c2d50200e45485aa60005100000014110383c00c204188000804030ba21030401c14404964501c3c298004607154066030032800000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 994278354 1250 994277104 994277107
    0x2404080705150405031b01051e03060f06091c081b0109031101050c04050402210106170601020309010e0603060a05090c0702011b030203071410020708120f0402060912030705030d1e02 80
    0x8100109950f0f801142d800120b505e03c81c4986c000c80d0744200b0544154401005407103855001290420020750b10a48040b405458440c01404c40c0742842021225a02c80140540104183e40c042590012031122001c036002001046504420000c40188030b404030601000090044054540503041d0801c200c92446164144020402400c03056003d40e400c80b0b80c02d440150b91401140c40250303d0f00303054403c2100300c208480012840720b42c0b11800d0840030382d00c0310f4115480d0b103911005994070b0045503001c1d4009010003480950301e0511202868224601030035410520342c8500c0000d241ca0b00c11a805006810b02042030015580d01070760381c0c01685d0400d00d0040710100c1c5130f10002c5d04d81c495140050000b403c00c00361008442820400340f1400c4042c141d046440c0c02c024904454180d204040c0d1807182c0a515010400101c4441130a60040b680100b445103025246030910038401c504443c0c14003a40002d03c4848045203051000b42105190800d00050208880200114bc141c1d02c1902d0b00c5d84610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 994279604 1250 994278354 994278359
    0x6030b2407080c07060203040620061305010b03010f0f060905090604030810030803010b04031104020313030e030a080403050106060311180409171308071703040524040807051504 78
    0xc604511500300440340c80940c0c0e5603000e400d1620030352041d1140505984504940000c1c01c2c2e5010028106913a155030b20940000105000a10f0200c0011450043c0390001004200d112520310322201c4451b10440012641590308000a403c4410a05248126549032100380e807880355103118110203880030800130032441c1003110040c1c0d55400d00031320081c24441100082146440702490f03c4004550000d01c00744c4da907866a54402c199009480200d480d03109105451000380341c2402600d219544030410484044415242182c14994400f1031540500405007040045141480140301560103400003049151a1502c01021901414480700305500306101c114504207101304800f121030b008442c04115004281010f80201151240240c209940000d070815280000c015031011240303d4019144019a0b0341c0030320303d0f404403032030301e200043e0001c100030b006901d400c0131107046041200b8442e4401c01c0c20002c8074541a0711540110308160b112040c10484d600c0d01e8207060140c1e641980040c2d04261 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 994280854 1250 994279604 994279639
    0x909021b161404091707050c0301140c071b0503010914120406090b090102101805060903041a030a090f03020f070f05090f0718261b06070c1e06030b 65
    0x1c05034a00d244210b4403031300d1142c00e02c4080420003030580c00b5401c111b560703880c80d07140c22961007001d0003949000b9401d01c201c0b030142e00048840d051145130071028852402c41a991358080b060402d01411000c240c2088000c44c481e2400d10800301d440740308180000f1140d0181d00014604080190300c0c00350036904020504c040e076480744d01030088070002040746898041c0e400045c0c4c03e02d80c52840c000080c601e00220418140c03012050000c2050080342551041e44900141036220f1240f030042d0340e00d41410310f1100d01e12303800000095a01041d41040019040b84542d1341800b408402001a00143e01c180c00001414509219100c0208000c86100d098285040042108000c0c024000040d401c1402d000400ca0b0b40a28549680c0c08505140d408560b41c41d04052003400000000c0c5034076044111408104c03c071000600c8080924400c00791270402c1c002e00e1308100195000305000c40e601c0302c0b0783e1000a12055034aa03e0390010702c0c0c01d560903040e58189034001b03007201d01303500d45603115004148528603c031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 994282104 1250 994280854 994280879
    0x311090a061101021c02091009150509030a020904050a150203070c02010804061d030d0c020109080d0c0c0b0f0a0e03070b070513030c3c0509070909021b16 68
    0x1100c440c100740029044108840f402400b131a034010840e80042d0181c00c0360009603500030003600500301d6005080f000501e008807008001402140c1c1305803903551840c821745d80518080c1001040003012100c1504503640410b01695055a04880700c0c1c1c023982e02c8008000003c070312035020813040c20086080d441d00303800007420070304000006810701c0560404071f4240132254004901d11780c101e903240e6003e044c02401417640e1307620600c8071521a42c07910102c003450501c1070255441284d0400c100d80d04110100102100030042103400c2e009000300c0300d4541000808040c80144224000600c0320325528025108409844ac7c506071100b6070341041103080c001640c524242034018000d458040c4d100c0303041c074100340c080c8030540c0c02c09170419403c400e0000b890049902021240c40302d903180068601c007800d800648003d80151600640081e10105010303d08100c00701c41d034042508c2c0b400750080b9550b00c440030100d90058804240c01091450aa02c4003082000151000b00020700400c800e1442c00003809200c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 994283354 1250 994282104 994282109
    0xe0a0503120a02270108060604050d140304031b21030c0b0603070506070b041a0108100b1c030e0f06190305150307080717060c0f0309070e160311090a 66
    0x2124890001c1600024180d050f00c4008014404c00c1400e01c3c0854940c02c1402000405240040d80c90030000b4102e003001000e50b021640041d181c004005204d90342c00001103130315460074a09200521000003c40c3e0206403403d0010707803080d480043c0c903051040003c48100f488082003400000032514000081e0f04c07110720565940c005000141d581c40f42030000c1e04241440d80f0a0340d2040f0f002c034018090050b0b50304d02900a80c450000492040350070078030420301072001d20500342d403030304801d840e2103041ca03080c0c000000c442c44c020700f890456801172040e1410404030980940018602441242d29420700c03424490380300200316081420400515040c0c5030900760340103083d0425480c0d070082180c50b00d04c5003013528201002019165a0b903181c09030190340d12500d119a50703d114601c2c2d9400d16032140800c2c3d40e80180d42c42c040c2c0e140740a12a2645040079880607042c40c4951040c0310b0001001c000025429014002e80c1001d00d901007403003c8000c0640701690114841c06000300944801555440d0340e003002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 994284604 1250 994283354 994283377
    0xb0315060f03011d0f1504030e010f03090204050a0f0506010c020f10091814130b010e041b030302011d01020c0604020907090e0a0510060e0f060f07061e0e0a0503 71
    0x922100e010100307001d401c0d24039200c050401d40707001043c444c10012510750340c0e10b00041c007201c40c42c4080303606020421000350b5018021500c010000e03c3e90307500c03c01441480c44503e080100380f825095000c5004c44104552507043c599845825403441c4034203000e582c0c0c00c46002d181a81c0440c81036000101d441c01c2000140d845640d02e032040461050203400c42034010800c00412200910080807010007401300070504800c4030131040d00140940c11648001507201e0340207880180d00341c0c24030351401d124060141013580d80b10000c0444c01c108882400f1407030083e6210b5400400c0c5182a1b0040b0154100210085da0f0143d0044c040d2070520341001451590054044440d044107807200e240a5a44221a0b0013072210707008a2030401100c0f10580c2c1102d405140d020140302040d950b03510301102c100a60b6044258802c6603024000c440c1c0c64401e01030104d0480807180d491400f1143d544a0048403400076165018040310041040d5515070785c03194841104801019080e88409a070359241c0b244104541c440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 994285854 1250 994284604 994284619
    0x60e1501141215040b010b0406090308090f120705040605060418180c060f14030c19091503090605060316090c020a1403090909010c0c031202210a0b031506 68
    0x72040c0d0b40d0007560700e80e2a8070140c1510802101c0c100b980081103000c44013611004101c000000b9280040070880301110318035514a5561800c0d82d6414007158030120700385601c118110f901380c1c003d6443c1040d580c1107404020007006181c0c5404113100982c1c1031030b889144038140a000030080c00b0f008000c84000c04807082030000e5104d400680520322440c010070041d0690740c0c952004200e01d0f401146c207a100d03080f2904c2e40304030405a01d10100309403108841015246800340000220100108010108400c4030700b000743c0d00c00e0f180c0c0c0c4c600d400884030588140000f40c4035100300062100f02d2050542120056010b0829100100600003030646036215001d0425620380200345454801c6c41000061030344081000640740503c0c0e0340030303034a811110a42e407142c2075407004035940781014825004004255180da6500000a0b02c3c1964404540000c10b0f007469000c002803e0300c0e40708050341103c054120609091542403044d0000211b40c2070354907242c0070b640b11340a4040100e84820f0450b0b800320080300d401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 994287104 1250 994285854 994285889
    0x14070f1103040e010b03011d0c07060b0f04021c18020303090118051305010315091230020304150203040f08070f02030a120f02120a050a110601060309060e1501 70
    0x303525500c034550140c1503480700031001050341c101c2d0500031070484201c1103030380c0c41c80c511116070442c58840549110109403420448400060b450703030809020700000620b0f0341006506000070409a03401000409207243c078640041800304042c1c420300c2040c00d0711103110304101056901283e6244203920006040c08403603004442c400d8122091303080685005047c0c0c14460303407c0740d681c42c050202030204440036030075490350400407801845140051604001c40241c0d8100601c0e050b02c3c101078880d03c0c4d41c0d2000c180c4034402c003012259156010303518445070005981e4902824415642044540055030982c010000d00002c256103985000c405a0001d07600f9903134403850307c0c15402050340c1180c00ad4140c002d003803000040c0820742443e0305c01040c80d03407121414011a070000b261121042c040d41e60011000307129000c2c1c103d100e50050401040c69003052100b03401e041c0003007803510000b40d0008000a85130f212150400c1414007803480b03c11070910040c00740c4d00c505884400c0e088014003c0ca4140c04150144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 994288354 1250 994287104 994287137
    0x15040503070b0309190302100c0c02030604110402070b130b070206152116050411040b0f070c0305150a06090204060c1226220308040b0a0605060a020303090114070f 72
    0x5c1c883c100b8000c1c0b0091030054040c640070b500c0b4544200503d170842c0c50090041c503940d014444081c607056000b0040e14807540ca235692500c0070140908030540083e8240040400150703c41a2503024550480159012052a2030700b2150440300600103000c41d0040d405209801280340c420520009003101e0050b84000701d280b00202540000c100407a00707214850300c6415051550010703a007983c1c01a2414005420b400c8941c143d28032031882031405540d4108000922000c40402501c001849158000f0010360769031180c2d46411041580341c42c14528000c1400700c00c6169204220060110940c2541031501e07200c0c0140000c00c82200182086409052940e8910b01c20ba88440494850340b03801a038440714000d1281d0206000c40f104549035102c000d0303426640c1c2d0080d8800080c1d90b41552081c0595070b503941d5a14503684090051003000352282800b0903965100000703806140c440d03a0013182c0f44d290031090f160a541c0e440040b40c0391901c5000c184202d880d03112081641a00181c00c022550b401c90300d10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 994289604 1250 994288354 994288363
    0x30f030d091b140f03011a040f0e071d0708060a0b0a030e0f030c0111090a0b1c050a271509030219030f080703062303240615040503070b0309 62
    0x40105200390b15240114400700e12550740c15000303a0644040032044804000d140c02c0320246440c072074180d007800c03184102c1341c075107500501d003c1c0a01c01400301d0b6008a203071646d490070b0a80c0d04942da041265245c0f81401940c81407040b68080900d02c1c20701c034541045070204000d0a9140600d05007850000f943c414018001d400111200110740e0807160024419170b40252030740c1160394124515400c10b04180340b100c00d000191003850600414291541c0c0c640300e0100c1031a07020300504c0c1d6202e681080403003040011481868841d002c540000304d580c05904040316028000d074000b00c044203c1d28245800824a481d800301d20150710307001c0c0000c981c0d000d41800c0e131421142000310f00100d04a5880d203010564001c100303044c030b011161521140d43e01d41040a906681c3c0d94001ca400404e181c04014010345415403000380d0640c0c000d0207403201010010f071500780040001080040c40c11480040c0030450810003041200902000139550409052100190702c4040d64440c001e140c01d03021000c1001c0400501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 994290854 1250 994289604 994289633
    0x19081204020d0203060a27080307180b04260604030215060612090309040c02030c0a060c1106180d05090102031602040b031c02060c041815090e0c0f030f030d09 70
    0x20304a13801c516164151601804c50407502e0803002181d8011500008101c85e500f007c1298003130181c0d815036139444011142c2c030411103001c1c92072041c4440000f40b9440e003600280302030015041143c52500d04800e0048a0003000d8681b401c80f98402d408120129501280140d2040c415088465071a01e40100160300303805140380794044103901500348040c1c0c400000043c00012019141404450f0f03840d107060740c880c001e001012100c1d8026045040010b0107543c820b1540400c182006910b0700c03210716909161460489241c00940c01070a050300c201b080422a0000307044051610724039003a00c0301c000035202d008011081c82c5000c400c0c0d403000304540d0385403c03030261a40302804444400f6056400c42e6500c00c8041020000b502a8801068244102e54100e4003580e060f40b5440c6084182c0c018000020410040200c0c1c440c40088030218843d42c1c14000c03002131883c8607004000c90620582008400c0750765141040c0300340d10800801010b81c40c08070079075001d400c0c801360001e007800160804500030780204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 994292104 1250 994290854 994290859
    0xf02190212010606120507171803040b0d0b041a360c130f0e06010c060e071202090f0411060307230409051003050715020106090207030e010219081204020d02 69
    0x881c040d03901c00041142c122080c3e000b84059211f400c5d099500460036248501a003103030000040e18400515000b0741d106005c88116407a055842510340426007291080ea821191241039030301013460140112080c0c08007014a802c00d5101c80000a50700090b400405a418290856000101c00c3c012100142c91007918050540600d810300c409000c50b80302c501003c0030b5844240340070036500007000e2010155210011954603540b5032800541c0d20340b242100864141c0c0d224521001c60b08001d016020044c409050340d807010035603a204000511170010b00c1000c0032151502004082038107000b004220b04e00541d0513036a2a21109011500f0541c540142103180380e21a1180e50280d1103400104200c41c400c80c01000a07803591400b91080190f5480081c2c040d41c0140004d200700203040ac1c00c40c188500d980000506540d9507001c00c2e050360881502540418601c00b016050303075030184140ca1074500c01c2240c00300350420039503a058050062007003c184001041c030016086480e00741c042214181c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 994293354 1250 994292104 994292111
    0xf09030818030d1d010207230102090a0e04060b0d0b090f030313120210050c04150c03020c040f14090a0b0c030403020727090b10080a1505060d0f0303050f06010f0219021201 76
    0x21401c2c0140c0c0c00700002c84941801d41601c4101003628810320a4400742fa1004010910071071400004002d018000b81007030b6100c560b9144084810ba0320255681240c0744122015103541c50322110755801e289100414080c1c070b400400070000f003c0441d10340310710751550022410000031280c29040345000c41ea00300035606145024280700040311030b0400b070021508000201c09440000c6201102c0340d01c1028801400340c1d00101c00c880301803038075400c008003004032940001040308009496428003201515000c84d00d801080c031079410f02401190069100c1c00d10300503d0700c0e604050303a000755610a544941401030071207111004142031049402240083c0802e81800021404d0a00b5081450180c035607545408484a0020305100007040303401825801840101042c900551442c1c042c0100902160b44102c01524000004070228821181d65020307640c0040c1500d012240030070340120242440c0c0c1441758010b154080964009145800745029001c4291240410f1010410f290780160002000f9401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 994294604 1250 994293354 994293367
    0x5090a051e21031005120312060f04020409150801111c0b041a130c1706030a140a11180408130b0a0c03090504020403050d0815040f09030818030d1d0102 67
    0x10442c007030350142c90310580f00c40c400d50b5180104291041200801d8aa0350070512581019985016480e07500400103011041d00c158204d0008040364415000088600d5075080c4c1405007909a491090141030b070b50000700131250b40c010048001c2e003c3e0700304140145050640914040145c0c3e004442840e038003610a11080e540d44410400034071404d040303a80620204503008190380042e0190034501c03501900c03448070200403030348074662911008004d1501441170600d51400500090700c5640d032201400083c2110f42c2503481c2c4484030140e2007140c98410345600303804040d02e4030111001c0303410960050703c0030b6880c0320303000c146000204141d001c05801e00005c0752140311150002160748486100c6d964034070b200c64680d0204000c0703010320701001e4029031249409201c011700a011054006648001048007940c030480014180c40308100c07100c90391901d03001b00000300341c0c22032403080d0001c10000d041c0d2800103a585100d5903030300902a9403410740307803101e48612451800d01380704030a841d07518009660750360 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 994295854 1250 994294604 994294663
    0x2030a030917011506050a020c13052710020c150108031308010e15073b041e0c0912081201170307060b0a050306071205090a051e 57
    0x710b01c510040503400b000d044208840c188a07404d0407003181060032184504002c4112001d42024000b04298480c8040c01007440d51086016000c10f9141180801d4a00d040311600d4503074020b0f039104135200c52040c80000c3c0f40d400d0100c0d01042c046e0004a0061b00c480000c1e5a95140004070030a030344020346143d0022a0709403010004001000d410004c0c040c01c260381d04403441c00c840705c8101805c407507003049941110024a40b0f1b4080e03005801ba07e0408001080141f505c0441e01000414140180c08405c0b000820b4007022540d845640080700c04026028548468402d1110300b03140781c00c18680d0707070850124000d00807200f03030002e40304c2c034032003400404090300c0c0c40d558a40c050344d14040d000307140000000340d90802c2c4100081d000c0d070b01c4010b141042d42c6680d96001078140d03a9403030340e840040e10382c01140640701000b03101e100d00036039568010178845480d02001124005807042445070400c0d0180004207400081401e0159101c0540401600e0800b50040c00d080d044cc1441307418040e4028180d1038417 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 994297104 1250 994295854 994295867
    0x1202040b12160207032301060e070f0e0a120f06060b0a030b03070519140406030204110304060f111b0c3d0f03050a0e030c01020a140a080c130302030a03 67
    0x2c0080907038805220b4441d503003d07681c0b0450340c4401010892044400300521044501c01e10244208200100740a40c941400014120007181d0581c0042d41440f00607603401da2002418000c0e040540d08050f001f420402e0503441840d000350040d04c0c41c1e240307904200810016a104d40003d040f00c00d240740d100c2c00c04c0c4000802405202d500c082c840d120340f041c041a84d1510003072490600c044031211a483d01d10707101c07030004513802c0c2d00d030403a038055aa504c0010250f1102d000d0286148260b030380c0141d0fa40743c10700c0c1a030101d8419000d0540c07810300d00344101b11135507842e10860b41011400c9031445403075034201c0d44852500e000e01e14404e4000724038400081c1c0e480c0c0d10042845040c81f1140c0303000c20804015001d036480c07012000d99503000500c1807000f214a039001360b00644d049001d1b8100400d0045114442515503403013450000d080707a500051000c010355101040c2445001580d6142d4500003000340f0060900f04068170381131850100040001b40030404120740d40c01554040e040c1c8900c2455030030044c219 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 994298354 1250 994297104 994297111
    0x190510090512030c0c12070b03010b12071107090f021b0c030d020a03120903051207050408070605040503030a0e0604030519140f070612090c08060a06050d050d1202040b12 75
    0xd0070200d100048442c1011040d61541242e0f400245811a0f514040010a0080e03860100c03030781c000e030200402c00038000c20041d0301a0001c0403185da80d0300309a004809840d10300500c80010072201d0302c140400300c07070041101400c4500c45180442c0b000040b02c20303d0001c1c401c043c01c40c1002c2c08000c0d01c800b4115804107440f644150f080f02582d80551400c18181d0302c80c11700d0080100019079142c0400c44c00d0f0b600380c1c8003c0040b4000c3c0b03403440c1091502c854036107100800752014030106102080c10000ca1408000d290050b200624016040c5403415010030365902514100c0340611000c3e03141c2c07100c60703140c02c41030701c00844d0400c0449042e07040d03144503150a40300d4040c1c00d80d001c80745034140160261000807280d0a140c0c0710801800b00c18500070085509940202a00204548030342500300802d44080b1524040c040078000b0303240c20f050409205003220601e60ac0240070703400310712151010420124078901d43d2241030400315800d5511704c514800912550f08842188000491548000300d500606a8071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 994299604 1250 994298354 994298359
    0xb060304050a17030c030c0d180b09010501050a0305030d18020d03030606020c01030225020f06130e0108010c0f11282a050d0203010e150a05070e09061905100905 71
    0xc0f44001d80c60000098803045803c884406020004144d150001d58004c0056001940f000503a420000180110100e5404400c2d1805020401802500741c0e0a105590041004844510b01e551a5503141c40d102d0062443d074460650b81e46228503686201340c07021140d1310364010120307808010245000303001446035019140047c4548281222154000c1c4200d4086003985082c04103043d0302c034036007403d00c0201d4030012078004080d5002c2e0020b03030310b40c0c2015210b200604241e051109023041840030f03407010141c1c05103040d070307050061a03400c0c180c120800300c01c03039003ca140c40404001d003442490f1600c1c86203184880c218060882040106107190060620107104030031010941d6500254031280c031840d005411014216480200018503022034075403082813010f000403a84a411400071030400a25007502680d43c2011003c0180610881c481c2503888043c23030030004028010354000c2010301400403c420302901c1c0440e24001405c0c036103240e240080070000d01d00d003c03075014104000c0614103176200b01030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 994300854 1250 994299604 994299623
    0x303050105010c1a04060b090c0913050c03010e0709030b040804170d051903090b0a0504031106150603040510051906050909030d110f0403120e120607050d0b060304050a 74
    0xc0c26602c81c01000c3c0d056a0031103115400c2e03809902c401500b8890283c0216660350b0758903808031480c3c135060035107445100b0500d0b8036602d6038140001d0051202120004900391484d01042042c120b983c201584d0660781e20f0807808549944040080d51000226000500203040784000c201c01c2001841c010310586082c030b14810400d030241c00c070300340d0b44800f00030700e00c3d012403024170842005408582680401200901d0003140c0707000361f600e4481248409071400c6410b640c54404000905402c408107901c000c0310140186803600d00340c041c0100c0d0800d001d007168840e410000c08a03051010421000d0300050480c48100800d05025422400c1c60141428080c3c426060510025592070064007007442203581c18051880c0100c0b500d8002c00400031340d0a10007400c002802900703075058504024101540c03150501c03403401003000c0d0000c0c00c0c428003050f60740c0c403c151105400d81505000319580c0d400a4150410a480c0c07107406040307001811132004855000f00000c0100000e0060006d4944441402440c044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 994302104 1250 994300854 994300859
    0x9030f2006090a09050c095109150a0f0929070804080a0606050a05090601021504050f121b011116170301030807110109050f043603030501 61
    0xc4103a005001402d94401ca914808002e60340d03082d000603501660004c501850044050009449880f140141d150151201204400d0b40d041443d0004070080c9509800c080400d80322200c0018260010341d041c0700c400000c10320040d503403104003101c0b911b004850303981911000390640c000d201c84000624200003400c1101c2c00500c1021100f4020b2103503003e921034a04c20140c00d8180c0e112680248012034801c0700c10080010f2030342041c410398000510540001c22140e2405007040341c42c034020b40206100c0c18106003840f0503a80c0000b1458068840c610007400656281d0501c1c504005020014194500a01460700381680151000f000500d4045415440c82d0f0380c0000c520f400c0300c100c2d41003001410001c00c004034500b07070746158400c11148038818154001012410102d0281c0081c4e100711000354001c9241010402c0b0400c0d4030785407400a19000209030328001c0042d1400740850100c074003641e40d03100c0310789000041414442100190f1004049008242d03e05109409007104060300001d103410000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 994303354 1250 994302104 994302109
    0xd150311040b090601020a0b2502060117190b070905100e0112020c06040803040c030614091b090105011202090a03050a030207062105180d090f06080103020a0e060109030f20 76
    0x200c9001d0300c4113070300400385a881f60751484407449001d008120900c1e805085110f84420285003810441e03507a130701400382075141079014240d03071005921826080e000301c0700c941d0015008040040d003058108140c080d0702e48403582d0503900001d59400260b0050041c40700e2484040d040311010700405021f998941c1000f0046450404074003950302d90b06041c0d04014003080200c0c00e40d0b405181c200e40261303141a14140d40e0340c0c441040300c9412442580484080703040046400c0c050207045150303040720442c0494000c1020004104560502074203050201c00140300708444519030549240201c054055420300d5100c1c28070594840c039000d012401403107414404100b191041d40c0d51003400c40c80d40b000c80e1844410034640c00140a004050100c101c40305041403030600800c0000049070205516030743d5426080040d01d2005500641003082804414001000180c6a050990b4201d8202205085860700c81ca00100e406109a03400074100350a84418a07040c0601032103d0007140560a007420140b100a005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 994304604 1250 994303354 994303369
    0x516030e07150224010f080f0c09150904050c28030b07030b03011509110c031806090a030606050a06030b01051222030804170903030706020d150311040b 67
    0x26605a044000d04101041c0d00b028025000c0c038280c0190f41e81079006070282d12140c0069520100c00c2c042c0c4400401007540035800719030140c112071020304110420700301e010f0f40c0da511011042c0c0c001d8425200080d01c150000c00115040030300108030036210708183c1030582e620741b02549141c0c802c10702a80c195482c0b402004154007c42d90740c4010b402002d2075500c91082c0400010310140a043d02d0307030204030042da400c0c412030341440444c03100c0303044050400b200c4d681210050707180342c4c144032004c20503141c0c504d40000940700400030300c0d02e601d030b244607070000411a140038040d40541c020440e0345003c41004420780060050f50700569019501a1b9103e200310f00b41c409c03503003102c1d000ca24200a9400d1048250120a03801748169504240c3c0800c80d03190400d0b540e2400fa8140e00241da4141131100b04110ba03c0b8080e10070445071005802d0148150009407644a0100010b0905600080030582030b100d5400646040342c0004440540c140d40f42051000740042d00c480a1140c0d240401c019810710f001134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 994305854 1250 994304604 994304621
    0x1f060305150a0e0106050d02041203030e0d030c020a020607080c030f1c020301060c02120c03062e0f05190e01090b010f020601142101020a09030b01120b0403031e0609051603 76
    0x100040300c4d074601310303060340c071a84a103401c500e03926000c000c007144245800c2c5d403a41c1c665104c1d0f85c0000f004240d0110380e904007000407111504040c2440c1e1008030090340098041c407103940465810b0b540d0b01c000d00e40b51900c4c2c8a15840c2c026240000328101c0190304c2200003602062200c102d0300507884c1040000c0348100e1200740102c0d130200d030440f0114005814400309000000141c00212030412410300d0001e4941001164100c82540001500b041101010a0181c03e013007000c0d8074030308415090500c0c884101607980145800744604000c0103a00105091554000f071034030b40c0d40b802c040c0d40c50f81c003884064000c0b692014003080b1388042c10300c102880040c0702412518000301c4500c841000c20200140300d20102800056072084003040300c6000340a10042c00348100d241c0303034000074a14601c1d011000d508140e02c45013010144070b202e400400e40c04104990300c65814a40001c096a8401c100002171407006160101203103070100c0440c0103048c50384031b40e0040300c03c05103036070a640001d14120159020384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 994307104 1250 994305854 994305869
    0x20d03090c120201170c0d1a03060135070603060839060409020c0105342a1b050a05061608030c03010f090908121f060305150a 56
    0x80100021440e02d452811024414549565800c002d8629821034a00c1030301c40c4400070b03800041c0340c8494090f41c400c81010751460114940d11110300c0380000d0300c40c20140b190040c0c0d4203c03c110302e40103074030200608040341c5080800558540c0f81c2c002d2195604514020880464507001012421400010342005002c4403014a90551501981843c820840000140b41d0707001d58020100210f584000141021b000c810b00d0042c2c5035440c0041041c02c0d41c101600c40d80503280c2c000768954910b8200602c003100000107100300100940e441c1d030100c4000c1e07610104504440c08031400341440700ca0f1120104000d13030041c1c2001e00c2c1c900b2041103840302061188141c46c0e10a145900c200715904003800070b0a5803628180e003151018082e9120190700e91302c229100c0c1403c07000000140400501900054098040644108500040e640c1d66180318884e203c52215001800e20005410441c80c0d11417040c0d0384940f00c40903030103d40e140400350240c902501c805035031320480b58541d209410300c10650800c64110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 994308354 1250 994307104 994307123
    0x10c0903020f010f1214150409200d020a15030501050f010e041d01110c010e06010b160609080d2f040e070203040f0f030b0f0c0409020d0e0a03030c020d0309 69
    0x30b4030040d110703051900380f4407051252030b20402224050324441d0703ca8803030b900b8182c524540782540c03561441922800c15075200e249490800e001180424200300580955018044000510040010103030604680008e600078a02d81004c1801c44501c0d541600c1034060391428000c0d41d807a9002c03c41d03e1100c11070307524002440d10000c0c0100f0b2034940c21148007031040c2c041c1910059400700c02c00d825940c1740510584e425500080c910300b0006d0900c14071441035490406400c665061004203a16841903031142128504c2c004603207024030038603602503185103901c404002e40c0d60307007540042805801e41c0ca00000c280311303445110042c15898441c0001030000130900700c500d42828006807404039034014041c04110f100522012505109900c0440c018011250200b183c80d4950300d4003c120500060122606100420511082d4203c4c4408c3e1015138100b0800903882d40b4020041000620412200741503a1281c1e504240a054041d404031445140a40c00d035000001c202d401a07040e2003048600902c8141d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 994309604 1250 994308354 994308379
    0x9162c16120605130b0d06060303091e08060417130303031a0906030c0415180f0c0c050715030b0a0e09011b02250308070b06010f021203011a09120609010c090302 71
    0x513650300c81410b00c80b0052050130201c503035071038040c04c403405600110007007125204107110f4020301c508a40345984252402c2c80300b045c10868202e4540740040d10003440c0c03007880d0b803589020b02c0d105001e031280c90340b005003200003080d52400c00801800440c40c0860424030041c038040c0b07541c10300401c158072502c6c010340104030600f0a4000d00005280380e85840c030b41c0180142000c20281302c503018022000b10000d83c00714040001154400c100d40785070319008107120450b602d0400256000c1072240c2107805090b0040d040030030480d000d901400300451115400805244003180a50160310401c1c0940039042c000c001d12400b06920081104009003c0405031b4040265000182140d01100e20740194840410404076034a40d1210400d8009240440b0a018850100b00e429680142c65261011161000305020b0030203030708242031840706000b000c6103c00e9504100201c1007580c002c4a52041000d80000014118510050380703d80c010394103406d09508003002c0c910b4551044600d03906aa800401d185500304 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 994310854 1250 994309604 994309639
    0xc04123e0a120f0822181d0a06090507050301020403060608070b090112020d0b04110c010e120d0506040204030507080d0807091a030601020a1203090b09162c16120605 73
    0x2c010000845c145c1d0541c00b54004641d00b150801801002940c20310050700e000c0d10001415200c1c3d81d044840c02070030040950841030ba000600e000c5035500900002504089803c146041c0f580c15001280c2640c00082c00104100c0307150300c441e00300c1d240c2400781c8031610385640340580f003442648241070003d0241c040d10403160086034014807501455050001d0340d00100d002142c183d403030000151080c00008030309600580000c0c002e14078440030700d50140406180883d202ca90038010a55042e0b0b080c4c0d92000020490707110b41c0c3c1114060341e0407a084030002a0f40342d01056a60700c0c6680b03110000f891503c00b069526001d03140e03120a0310702040790a108911001c2d1441102d0304001c0c8100d045200d04031000f0b0110b05e500c815034000c0400e80d0707030200b92020070303042a0000d500d000c1d00305121035102020705000b110712005503a055510501100c4003042c051015003d0307088009c0c0c20300c198103100c0710030301031120301c860002082560551100c1142c04142001c1c00201c644501c01c0760380002c0038100302074051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 994312104 1250 994310854 994310857
    0xd0906180e07050f12040b0108010506010c030f030e014212020f030a170c0c1905100c05011a0f01021f0203061212120c04123e0a120f08 60
    0x10280c074041404c1454200a4200200b42506d055514110300e100600090740207000300c0e84e000100317080144d43c03102150b40041807810143c84000c10599500c00c0100e0015080d0498100314410900c004208841e104040302428220814541c58001e88656080000c80111000301215012544c0c020054200c0e02400300040900e502c0641c180520704203900042c0d202e00d190362150f039103500c485031600390310001d0070f26010f04042203901c40c070344c3c4a1b00c0300c41807980841140262582030742e402207203002a03076081e14a1a500342d4010441c0d4280002010700310030040c2d581c801050215800c0503000c00039001641c80d20340c0c0300c4400b401005841c00034085070780c160700199080320000e0f04d1011003008440c4418200743c01d07601c0352000c4440c0000c3d6184100b071840038054110005c140c0e481c0c43c00f807520020070705070100f80c1401007440b2034103408091101c0702916509401c044801084061600104003c203900c0710004a180c1b040b480d07403401080f10780800d041d00a034a079010056018410051711058082d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 994313354 1250 994312104 994312117
    0x100c081807051314040302010903030605030a1104020c030f0304051b010813110a080f0303060f220507030f0501031101110d0509010507020a0902040b180306060f041d0d0906180e0705 80
    0x751134901d200d8100d114071020034401c60199000180c49005480c0c000c003075508980c400b030b100e82d00a10010001c1343e20070392030384554001150300507038460381403082c0340c11401481d03644000d4007004420042030040102c2d00780810003603041403086c040310620041d5456901910005070100d0340000000001e11072650070148000024682046165505852442c1c409180d41102164001205020322420103001c0105072003004c8461a5181c0b21004008840401c0c1903900e0304030903202c502217402e40740a0b40c0001306107003402c2c0050000d5278417402d091000c4a00b0040090019000444014250354081003440c1d00401c155074031850f00145800440d80d9070404a000d90b4440c407848800107480720144001c10081a50a410030b40b10061207d94403440d00f014105140a50080d0042001c665121340404060300c004031000505c4149181941098000c49082440c00e4030070781074000311180c0c00c00809401c4821907a1140da410b102030114501010382d52041940c5141c0c103e020030612402000600030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 994314604 1250 994313354 994313389
    0x5011d0105180a020c1501120303060e07020a1b0f0b03042010030902030f0708010b0a06050403020901051512010b031506040e010b07050f012f0a080105090c0c100c08180705 76
    0x1384114014045040e501c020b0b48000e805041c500c488c1c00c20581c01d805110010b0a031180c600d03044c0d141280340a07441c6c095200004000d5183c4410051003030989460000182400103007100c84c80d600c44188403030300e60007a41c040d2142c06c9614030000c5041281001b80b0b00008001d0100d141860843e0400c0d809004000e07012645801020240c041151003081007000030400e0000100790b150003401408001036440d0805410800104001c0c000350710340e600c80c3e0b811100107560384260204412030020041c02240003004a00381d00000000b094040807010310b0082100303035403081442c19200700300601c5114a02c500b0181a41400040080c26a90000740c88a18003c4040e1820b040529406a013140d10791250300d40358640030301d00341e024042000d2455615105d04800e0f0740ca000075001c03019048440521070710784201271b0000001d40c4550041d080e2111308110000710b840300500000003501400e080c40c48100020881800980c08035194108010352004000240c9030340c90400040c0540d8854100e41d064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 994315854 1250 994314604 994314613
    0x30a0e04021b0124050603101e03051b031b0306040b040812040b16080702061303020708121e070b130f021c0b090f250905011d0105180a020c 62
    0x3002c082c003500c0d00d41d00303455210741c100303100c009030b030050240c882c0c1c0113180604424400c0040c15500310200e02d00707941d04480410b595080020b100c110702605074000810502400d40038010302d01c40b00c1c400710b8914400700c007a961002c0003c5002503d0400c003065490385030b4071400205021035080003095070014011080685401320b030b400c581055100a44040300d0280780c0e401008071a272100c40900030350b15007500d411202403d00e981300960342c800180900e0b0740b10306041445010107008010f52001415080d0075943d0082d000e620407101c40c0c100d85043c082c14070506180c500101c4a0f0800c5807035555018071412616150b81e400300c0340701010040308565451014150700302582d40c0810340483d44051840400003140149080c1c0080d80000d0101c3c010b9911501202018480209141014240c1d400104130642250751860481c8801c592100d400907107800c0001c111004c00c25441003035000a0000c400040e40c0c2d035400d010181079030407190581c0d1508403000c40d504040f240c0043c1051030b100b40446 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 994317104 1250 994315854 994315897
    0xc031e0909010f080d03150302041e060f0513110304031229010f090317070204090602040b070215040b0403021c060c0806120f060106080718030305070b09030a0e0402 73
    0x2210741000ba00100f0003d1501c2c0c03410007000741c1c2000300700d940b000c052406200703c46140d4400d840c401c9513400024491901d40100304811070002c201c01d2030803502c1c03e9040c821300d40d42d4128403141c1c164038099140603c01542d080d00744403a0a00900d03100e481411951844e503074454408480401c01c00e181d501645071107800038075821240155081c1d045e0210445103c40c05020700000d0414020207450b0b4052103501c24042001c41c2e14140c074004101c4515070404d130798000a20010300202009000200307100c0c4003040c00325900d05904e0191004a1003030780d038002c074051280c900700c5840c05035215160b81c1304000c000c14001400d0005c40800c418181c90070501079403503203581d607106403130382841c0c1c0c1000624400e081195a04d401c5050101511464002d02560301e880304a03203031103500501844041c06600e4011500003032065a000200314125101140c01d1602d80c900200706a02ca85c1065449103056004500701160220880707095495544804541041d40024031005e0b40100505210550014801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 994318354 1250 994317104 994317109
    0x20d05121506040803071101090905090607082806030b0105012c010e03060a090c050f06090910050a0303020c18150d061b09030c0e0613200c0d140c031e09 68
    0x1d042000d00c03d01c1d1207d80140785c0000100341c080781ea400760424509100a0289059005c203100e0380100c140c2c03801c440959161900200d1295081011144240d0707860040f00b0b0520039640182e082d00d00c540e095181990782c4400464585030443d1400708081c11082c6060110240c040d03081d400c1c094107042c0014403c041d030300000e041c41001c0754030754045a1160302050030445104015000751904070b4280c541d16a0380000318846025036841035000d0f48490010a144d0482004901d00800c0c00030400800303591a460000c0d2222114001e05002d09840d00080d5001c0300c0110045111b80200301110221074050001c011440f40340d080203070b8030242d0340d41e05007103160340f02e59010000213219102c00c80c240703185242400190105a100d45440c805160030310216a03146402112072007011f40000c203a00401010840300b1000c0c2d0b0b40328400700c00300003d10b101c1500f0f0204003000411241d844100c40c10362882403102d014810036042c88180d803c10440c0c10101071031510000743c10010031940c282040c000101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 994319604 1250 994318354 994318357
    0x1170405120c10050a0216060f020706020a05040801140105150703090b04060918060501020c060c0708010216060c020a051c021513142a01021912020d05121506040803 73
    0x40b007806030059072100014030381034094560071026104c401c62400228421603c690444c0b50300080c080e030385944c6c002c0008922501a202c4840c1c1001c0701f15540c16444002402aa12a1042485035400c003072405200c1444000d107103040798809842815444104000600c1c41c0d40030945c110306215202c007021072400d107103801138806800152154020b590a02ea111010b410740c41803040401c60400c3c0f4180070599020405985405041c0c40460300c0f4141000030504040c12034104030f10561005c5030701545941a00f0140e03200f41d01440302080352001e0138070102d0f11001c00d1075010348182d000003024000c5224518407400c982c0b1207481600c0c480d5915800c004c04030b034000e0310001110010008c40c1410310284134a524a941120741c0100a070f1002d581c022010900440611070886d00e101e01e81c0c402c2c5034000e00c1070500d01400080f15260014451078980045080c070940440184552124101d88600400c100c80054120ba40020116901c65540071a03140000302c0d90303604a0018000055170100410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 994320854 1250 994319604 994319617
    0x40e0601021c020f0c0a180e1911040506030f060103031b170c0d11100b0112051014010f17041403040b070b160c06051012150c0e0117040512 62
    0x24007134a481404000380a00d400c1d00202d900d403090b1500304003001070b400005c8a0000d0318407890400300d5050290310030341d81445041c550125a20030b02e01030940800040c0310104080c0c1c03500f102c0c1004691200c00c03d00d541d81840c0c417001010395000e8001403010a0051070300d01804850008a44840c0001d1b43e24160240d10880d1400c407400008102805622014000200c04288919010200210001c03c8559580d00710501d000c4203036440400390b01c47e902c19200041d840040c2c503404e000ea418948080601c280340f5101e8801c1c54082c4441a40c0a50310580c440c01441c60941d079004250700c6900e641410645c1c02501c11109049c00301c250400c00301080c009400203102034920b05071140c0d41824084030f105001012408480d210380c41c02c107070598121034036600031342e0000c2000600355a00b84a80454814a0f00140441007401100108011110001c0b00c0046800ca9040c0302d8018540400d0301e00c0e01c03650101a0210b100110300480b060f10340030b000b03507001d80641c0440c0c0ca200642880006154000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 994322104 1250 994320854 994320857
    0x9270102040923071103070c080c15090d03030b1c0b040c0834091b02010b030a031e0210050408210f010623160302071208040e0601021c 60
    0xc1000c220a0925201c0c814a480b07025803007003011508444800c0c1d04010080080d018017103942d603620300d00c3e0403c2003601c0c8260f5000e8822a102d40d180c150301755845c09180030940c070840c418060300c925842401d00b40c550200c806005001c1584c0e07251340644c09400041e02d0640c00100d80310b00300541006003048022186c1c020350090103541000d0030095030010144c1c100d404154869103a0440204201124000b0100b003290f6076420131000381b104402d000c0c02e99000e004400e09001d00d0180c00005102000d54560544d0000c01c541c010711018152201c0d136854000d008511070343c0c82a1380e400240d419600c0c11f01a644151a0343c0002031a419044520640b0142c500400100700801d0300503084410708003502c40032400c8103480c030740141c5400301c90005008620400c00341c104c0b40341001d81c941005c0c1c02ca00072950b11640d103507a00190405043d5284002c281d006115104001070503001680044a640b0b800c03560a5103400d05149404204010181a00e0b046124000b5082d80010928890241182c0075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 994323354 1250 994322104 994322107
    0x15121006091e0b0903010b03010c0509010f03050f01030809132901171f0302180901050f040f06020a090513050f060301270812070206011802041409270102 68
    0x90450040189403641c010307075540035024081c1a0300b050101a12001c07144010080c5545050600200740905524200f4a0f0150708100b18000007540000162905980c280d8503142e900d04198422802e0b9141901d80307880007802c10005201042c4110010421600d01a0100d8020120b0070040002caa04141c604c9158030540030103240707007401050341ea4824030024600340300402925620b491a440340076101c1d0601c0b2404607902c003440b44a1200703410082d50014801110f01c0c10041c1100e07030f0414111107441c1c1c5940782c1800108802c154469683c0181e4010743c01d4086031115a4451000f503004800c2c03c01400480e00d40040c482c0e442010f009180c0d414050081400d04141c11aa0007071400500807038860f905005003010b20055a20454107032400848400783c68100d5420015000d1040e10f00c040100e59000b020013034009d40028009040b540500d0702d5503803050189800c04100e00a0303004071404016013407026281e0b417030a46056900001780000c1c04ea40c60f08001000303c02c500e6031400c41da407142d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 994324604 1250 994323354 994323359
    0x2010b01021603030f08100f170601050904170a0e0909100507091d06040609020721140a051b070f0503070905090a140114040f020306070914151210 65
    0x81c144030300280c9941e403041107454141543d4000c3c00c009035951001003000200f000040e01c0039010b8401c00000c1c1b0604512400a130b032a0084148004000d4044002911030f0320b000041c6400c050000c14891600309518a0f40c010070303d00442502c0c3c0c444840f40e010032500c0c40c1d444600380e42c0c0d1803a45000700711000051006007082d070340c1c403815150004c003020705000c6070440806c140e0000c80c50413050281803156810b46503031104001801010250007110445101060352801c00c0107484684000c1251560700003a00841028200c501c0328030f00212041e940340910003080c2c540d01600107010f605194071a20415a10345949040c0303800103da105069801182108104504003030000030081c022150007844986031035010141c0c0c600c003404008002c8100c10303096a404101c01e521008843c03a041e14501c225050600b02006c0c0d4a4401405038800c0c041c41010502140c0910760032070440c0c40c010260599200101c08020120802070b03900142400e0800901500810809441d03100d04141c480e180174090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 994325854 1250 994324604 994324607
    0x70317030712330e040b010315020405180411030a030f0306060305160f0c0b16030501060c121d0a15031518020304150e28030818030f0a02010b01 64
    0x40c5950b4511450b1092944480c81d41c405185040c04000440003038149001e1803255411009a0104800c000700e48140000c01a13081c600718101d9000fa5415000c1d02c44007440d00003213114507c685940200541c0c801040013046152aa52007400341182d022042c0700c04001ca0304004030034404400040d2082c0b01e80c09a1901032113944040c144a00d003c01c09480d1403182e00c4140c8030022800d90a000e400840c1316a540e10686919070300507801500d4094a0074000206c190111400c0c184401090030300b800890540d2044103400d011580003085200c086800e0401980c03404188501190741d03c40d80d01d2001c40c45d451340da401c84000c150b011319800794620703d0070006040b1148a5005900e207a50000104a8912050b4007804001000d41c401692911507240000186000484070442c0d10f081c0405a03d01c90390106400001d00d40720007400400920a61400d907040c402e2000c0107010a0309079000c14107058446c0035103480c0c004400f0480340b80c030100c0f03030540b00c8940054060a005039101c54036005c055 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 994327104 1250 994325854 994325867
    0x70212012a02061305070f1509060806300109030809060906040f20040c030b0406090b30010204121205030114040203130b010b1b0d05090d050703170307 67
    0x4801600d1480e809100c01c4000791101d00251104010001020b09981804020b200800003041c40d0490715000c1039881000d0b84034500c0712400315021036512400060401e020307001081c4602001002c0b0000a008803105c3d0012a28132021500c0e0440150b85a42240200740300c0e45403224025160307154a450000791062400c280200030340d00e035800010a00000825181c035000400350303c1103011050312001403144004050652996601c02c1c00c0640c161281605940100b0f0b00c5c0c0c105407400d0154546990710700d02a1041c1250407a000464612500107107420f010a10103050001031803880800290140c650aa8125400c158030031150410040104800e22040e50350080140c00c0c00f03400d540c07414514000c00300d00e2550943c02170350004001408030180d180d6503039400b5441440e90341a5612645002ca03642c01c010b14907068001f10742e004041d0750b0400144880402d85c0d9695180c9808103030740c24026581200d0303400f2034003481110700210010354071240724100c0107144000f81d0388901d008070004159 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 994328354 1250 994327104 994327151
    0xb120105060723191a09071404020702040b0a090c0809120405090c07020936030a0e0a0e0f16050702090103030e01021e030403020307080d022107021201 67
    0x10711410080d4000050903540c05500340c900024601c2d200f500e4080c1c00e075040c0341c401d64410344102020140704040007204500d0300492000c4188000143c0d0301c80000c159a032100d409110141010b4038031003c0c05242c40c1e00149150781c8041e1005c2141400d500120b0800e400d9908021600358613000107400c00d83c0e1011002340e0018071440140349110403c6440c420074869030242e0b9005505110000c0c03075001011080703c4145601600d4203602d480d0550000705052644900301109918003041c000c1d8120301c0d1002d51191410440155103401c29941c0c0c08d031132064240c1d40054000041150029140d80700444141c460150010740000d140f810306072900c1c801d4007010000d0140101031099a000d600e660071000e041d07940c9410300b0305c0c8842c100030042c0d1800780c0b00f607882c100c42c00c5d0301d41d51a807030814080041d100706ca100354102d5141c1c0ba2504071654646803003601e24001a071290349907039015162410000da040043e14131851400b101030300411012481c1d20740c071051688d12074400400304190030040c9080e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 994329604 1250 994328354 994328359
    0x100302161112030f09040b04110d140907080303190b1801030213020c06060d1403040303020c0f010306080d03020304020d021003050708061020030d090b0a05070203180d0c050303040b120105 83
    0x16103141362800800300d00030001514000c80c4e880b014025103031599030082c0515085000349540b00e442c0074940c030000c1c0c6401100096154040710104601d008c00203145801d680418002e1420340c0e440081c0040500040e43d552801643c4501e1102d060761129245508a101d41d10f291544035030450060100c42000103080b0f103541d510400c0014440346022031950b4011400712258a40000c4a0030316008410104003508450b0200140000405400144204902405032515690803404600650440b111882052000c0e009a11141d200350311960085600a00c010811107560096801140d585001403981002081c4e844090007980da4003e03003600c3d40b0a5003207840402105901b20001c00c20321001120030944408010070040d042d0301401680c200b100300c541c08005074241410003501d880c0007940c1181c1c0e868540008512000c1c404801c580d200c000140030001040c2200042c4801d01040540540c1e070303001c00c00d00c0401c1c1541c0500050009168118901e40c8030f00007030011855006060344041d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 994330854 1250 994329604 994329607
    0x90d121806080610231309060e04020307030222050c2d090f130c020d1701080601050f1305010803090f0a1508040f050105010602100f0504030e10030216111203 70
    0x259a84900c1030002e8a569458034144111410005e4460060041880e05000c07401180302c05e10146241000000c80d030b900d400138840e040d90754040f060b07019810355000c1e4064110340414005401c14040440d110160300e04401c0684003411068001c45800742d41c0440340c410f00140e00e6240440c007401204210a07041501c0325050400c200942a502c64041e24501444042d000c020407650b80640b018400e121300d08062207481e015400003901c94803144800000700345a414804001d0440410041c144c86c1190010301c116401c01c0704220151608801d0154000500c80c103511144407a0b0003114000c084d8500219180e001540c20004851070404070940500c030725010400500300a001d001e008200c5600f0b10311079a41f43d0303061001c0c81c036485a0000c1d001d50b00b41030002581030350004181b000b00c08100360400644000d08071080c01c0d10000c0d81d01500252004181945618040c5c200c0e845e0f007a8a41001458003440c110031040180007848182e07851540ea140517071680c245000c001700190010800395 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 994332104 1250 994330854 994330861
    0x60a0b270603190b12011806060e0f04030509040902100e030c190b130b07080310050406120201080916080a02090c030c07080708090d4202090d12180608 67
    0x11080300c1c51183c0543c40c0d01d902e4881c401ca460b00c890b189072882c0f82070b28009210214103811901545003d038002159803e00d00140000d101d01c8601c0480c2c0100710702d141c0020351344c8954500b11911b403c4046d030030b80e2141d505e802c0000107a407860f00c0000326505a880b41c502180400003010306004022a0b1107000741004200c546030701000c40d81e240c082e0395003102300507119481d602c0c40c40e08809568115018141d00010600217105103034000d18821407403181c08010300c40c0c841c0c092006a03080c078421003400181c1c4911500041d80180f485950005465046800b0318903101504580d04003940d001c0c8040750440c41125045d070800e245150740c8004d10780c40a500d10304001c081c03c1c4a910650038042d183d640c011840ba42041000000c60b000b04000403c1d20000c0b03203050803d9022503201c482801d20f204258000d80b821b090f071a101c0050413120034048241104400d4191002a520483d031840c1d000141c02c04480c001070030004000340400c801d5849540020180c131000315102d08c030360415002c4c4000b00d07082 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 994333354 1250 994332104 994332121
    0x304092d020906270d0b0109060b0a05070305071a0109062d0312030608030a0809010f050610030b030709020f0702010801061704031103121503010f05040f020603060a0b270603 77
    0x48501d90b0a4003580c0401c0180b40c07550030200c00801a80381079100030005d1241c0103001c0e10310b07059816108962001c012050361220007400a01c10110000d007c10170500c002c2012a004002a10341c440c051001740d40036101110031000c48440136080950010303614139040c40381c50000303048001600010807a6030450745c03103211003902c031840d00e210003810025805030444200b032194001030002e260040440e501c802c8040d90140c0040d000700c814112a43c0ba010350164850000c2c061503020743d2010302201c6411030f80f018100c0142c0801c103040d07a0140b250010001d54040b4074030041c80c1c2800f100c05020b4a840c520b2000401050069201c0803c0041d2101803000b19421a0b01480c1c2003036150130110703000b501c02000d40d42103000710381c100e02920b039104040000c0e8814030001891030003c110001c000c81107082c41000c0440b0410b82d0082d000007001c01e00c03000141030000c02036411020042c41076084540c1d88100c90b0690340080c6200200749071680000307000e10b680170b84411074108104e80c83c0b4214030384101c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 994334604 1250 994333354 994333357
    0x10f0f0b0702100210060620010c080a1808030c12130b0a090204060504140604061502070506130e0a090519031d0f03101506020f031b0304092d020906 66
    0x40280c418841d50070032440c0c3c60700801014103071280308401840490b503074910240a81c4241010346ca1041c030310300480c00d1540010300c65940200829240c00f0460b0301d504407404000d1940403256030a5160550107080424118405144104080c0d80c0403581d842c84c0c0f40c8004280d80c00506001c48020208002d0000502081d9440344d01504245000607001c840e03000281c06810103a0007550050b15000c04110304c1418082d45074401c800030b47c1c090003910381e07035410120703400704d034012100c0140c11405052086c2d10f000401460b1490054140c400015100d480c1d43e2403040c005d403490842907699100d00400c1200c103104240141d1500794110745a08410344015010200a500f0541101e03445441c0c40f02d250350304401441e5a400280480c3c8440032400e503544002e00010b81c1800d03581110000010701c4d644001240013101240d80051820100500020705040c603402500f8821400240300110345501540f0804001101c04401007100740480e8122610000e200011041c1a600402421505444000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 994335854 1250 994334604 994334617
    0x15010507050a110f0d060b030d23130b121608040201090b0d15060215090d0507080c0f0a080d05090133030b0a060528030b06060d0e0105010f0f0b 64
    0x42c401101d0882810000c1c51101c13410070300603070081c440c582e0003061041d194015202c002c019000c4814040d18280d0507140d0110320017140c0e110380d0102c100d14100a0114000d003241c95010403050908903280c202c800c140360003002440303810403030705003c1210a40f00382e08081201040b5003419440303401e054000074400714060144032400b04000900502000c61541b0801d424003c21840d003045c0c0d074403070130001c1d01e6051002024050341e030040c01144030030038041100c0301c075108191221854240c81c7c2d0380e032485a41240408540038080e81101940910303003404401c0038584100d42e082e0b99030f0003420816049403006000804582c0c0b50a241d2104000c1c486810055410442880c20601d10304400780040e41d5080e400c004c0c084803440e0140701070140c19402035015108121941203e041c21401e180380c0340f40c45c2c0749513005028030203101000801c8801811340d03007080000c0c140318a05182c3c0a07814081e609000d0000d0342c0b0ba907680c030040002c2c46240c5420006806160b00a40685242180c14001c070f01520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 994337104 1250 994335854 994335863
    0xb090405070203120f1b0c0d0f2d1d010e12070308040e0915040317061809071503060f03150b0901120303140c0d0c020705061215010507050a 62
    0x51010a601c240200260b8042c03040003512000d061902c0725a50710301140541c0c1d045000324815044100840145040d6641040321000030300c07000316031010880341c0c0a1818241c0d000e102c01a4040c04146c071b10a031464034121b0566402808a220711140100080c2100e03920005050141d08151010f070f034050440034038480c00b03d4200c0e4500e0b10f0341411b03d05000032030303000400d0034100190018050403c0c90005210390741c08030660f925403405280410700500221002400111090320000003088503d0743c1940140000d410a0300c0307502401058000c0241c199002d04040e445510100003c2c1d4405030901a501b040d8a002e2140c0c0d4900300015400c5481d030700004000320002070000c150010103510146019200500b40d11003540d4030301154001c2c00f50a1010380000303040c0441c0010810000000c40c0c003070792490f00d2588c40e20003500c1d4040c004001c81d02212045000308000000d0654074440584404070030300207012403034101a02000c1c4100c00610056040c4203043c801d4002184021403c0444190031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 994338354 1250 994337104 994337111
    0xd08040518153604050d0509030303011a0d0218030f0d0e0409060b030d05071101080601050909040f051002040518010803040e31110f030304051e0d0b100902040b0904 73
    0x54a101807002d40461000c04074102d001011404522525103c03400750380200166114046004000c86a6200c1e0383d0001d5015031042004000030b00100400f0a032a000298600382480114804071090380c1c040e003001c0d04100700072000902c00785018845e030344988000400800e002c04034480c3c0a00084000b00e003061081c0d0780c4162010a200154000001d540401020303513036244449207001d030203030704011010b44a80c001c41c1104529035004240e4580120b005071545403d059203c0c0c104840d60030020701c2211000490034154002807801c0194440e1440b0290300544c03500c3c14042403044202441c441a180510749200400141501200302e0301500c07203040c1d2080c91540c0700e180e450180304880c071408140801c0a00c00b203200f9000f0b080281d118500c2100c060040e002694108880c9040300c0400382d5250f0000c000c104568034188601c06054005988140036030003c0d44001850400c101c0011b079502c01ca00e400f004010221040d808001c0c0c442d0044c2141000c0c18030b0700011980c02140c11190150f50b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 994339604 1250 994338354 994338379
    0xb041e0903020c0d1407090b010c1203090c170f07230102071a0315030606031509010906050f010501030e0d050403060504080d1b0905100507110109050d0804051815 72
    0x100707019080d61000040c120f006500202e141c0545994043c00f0105d00b1070045135000714560b201c501880031003010596400c401840785848034000708400480c10400d06684201d0000001ca5002c86240200701c0340f03001105e80d945100849040172807050132041079802c59202400608040c0812400c1c201c40c585070742d54245503840040c0e181c440c42d0340100c12844000007402c180c1d5205040218490710840c8400e0045815520605036281800e41c1c0703040e455004860100403030b0075003401e078550104c403480010403d10040d4403020304661055406401d401072100042c011542c05000320070821040100a09989642c1c1c4401410b80c0124000109103648900108091003541400c0d201600b0180c0340400c0b00c2c1500302d0704222045000caa80e070001c038141030000a1285050447c4406080c0d468892620740401503560300a2081d00e400414180724003800040b0300d039110884d42e110014810800b180d900d50030401040420b1641c990b1542c000d400c1a82000343c013142011132840004c800b40d030001c1c0c9850 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 994340854 1250 994339604 994339607
    0x17040515070204021209100b0409150e031912050108060408030c1615020d14010b04260d210207020a050d020f03060907060e0a030503040614040321030b041e0903 71
    0xc10040d0103504511401c051000d041804039200c0304458080701f00304203039581d01d400e10098a0131488098003440c0081d844d82400c00c00364124040f00001241607a11300b004107018042c0d100c1062010344005660034039800c01e40000303441000e000d00030f0348005000600d040e0781ca11a00e8400100320061010780811521640418016409500da600248100340e401d40e94900d0030003904401d0720708028500309180e100b4111011942c0c281030366a041034031440d2030b06000030f0040010905d101c1d07528011042c414903000300f03c05e0020180c8040707a59102d082080191101c020f45140c20364401c04410f1040240d1801603841040d200304030744082e2040d045502013400010210810f11040d150907028031700401030361000100d400020384205444061404a002050001d0380d0041d000c02019a8010002440b40c82c1c0210007040114450b1402c01c0e113845d880b030b034810000c0070401032841e11000d00411508816901802801220b00c01610108451040d003180a415056540103190300d056a0b00c844000b4103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 994342104 1250 994340854 994340857
    0x50307021305060f120309121504050d1101060b040513020d090b071106060a050103110f070302011e1802010305180a050724081f0e0703091704051507020402 69
    0x980c0081c40703001245282203045000c1c1100325582c504c144042c84120600d890300c0515002d08082060041d0f0405202c44140300e8605c0b500895200184140032100c2a07101446108601c40c40c4208050000d03049032000203480502440d080a00990521030140019080841541d08444003190800e440921420005000b0711803d10102026030909500006202300844c42d64002e42c0140d46480e14040880c1140380c03204016101254404500031040080398401e80015103452261030f21035142c4000700b0000c02890340310400c205c0160b51034007048210a010204600394899800005004a0700c04041400c849070b041c01000307041c5030740c58000c20312810b80b15000f520058140c5048600f8010642045a03480980340705110f02ca0b4071402240d081110700c0045000c11032038948442401d500c0381b120090301506041180406261506c500040800c02107141500031900381d200013600e84442d00300030200d85085c04202c4103d0000300001c01c042c2d101e4122aa144000c1c8200c025110082480024041d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 994343354 1250 994342104 994342117
    0x10f0b0a18170a03090501030b130506011e0207080d1e03110c030406050301082b05030601050d14070207170c041d0604151b120203100f120209010b0c03030705070503 73
    0x30308031401e0101c0c240b01d001402441d4035001e62110f01c03032035688100460694005142c419004105200d98600080c4a1340240e6081281414580ca800c0d18080700222040303566041c100045e2700500c402c1200c0d0105000480303820f02c0342c1c0303420650a001000b4210b14000780b95a1a420546c3d501d4070010007a40324010b99070b030301c100102507a80c2c40c0d42d508d00040030340c3c100b03010703400c03041c00307244444a441110720000050380c00b40c4070042c1c2d01d0400310800c2624180c00080446041c40802c2106125508003442026007543c0c0254140750141000d043c001d01d4103850b034029121004540d1a04c080a810006149002d403c0848001c102030100590401c5411500007040c9024800c4c0f00c1803104003c498034401e8020b40d500c80e001c2000040140f01c6d0800081d000e40315101140301e166114481c00c086400860b032142c95407460b84440e5595004000030514181d105e0485842c60008180c00c505d0b15044132401004204021030404507503400c40c5403207110207405001403002c000764010400a0520940740d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 994344604 1250 994343354 994343369
    0x7030e092d040c0b03130209010b041833031a0f0c0412030f031e2306031e1005100f090c090302010305060312070614010f0b0a18 57
    0xc64244011003007a1210704003410103929088031040030003850003a50061045401c5442d4615030307494418500003950001d066024001c02c1601070074050388901100c40d00800702400c03110742d40c074074101c4254184500c0604106501d8281f003404600084a0460b18088211018400000d9001d090f0410304031146640700a019040349a4a0f51140c03406200321482510341c0070180400b0b5076002c115030003034851b9014801612001c8011540460311410080a144030682000503112103075450080060b6425400b2619207034450180c038250b0b4203582602407040300c14890098160800c2c00003c5c0d01c030340c407000b0740898241c4c1c1c0940c5007030140d200f0842c000d642200150100f105090a512903818140380b4080e40018070038100d00040c03688070034421501e10310b2569891044503421940114041c140c05407510342d040c0300d01560000c02d840002d000305001407140b0300004249005e20941034140d001680a01e26040091804010390120321040360b495400d00d203002940c018802d44c1c60028036045810202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 994345854 1250 994344604 994344619
    0xb0c0d0f11090a050303041d0709050301090b0103030f0e0904020d0f0f0507080c1206060f01050f0a0e0901120209010b2a100609020408030715060503030f130f140607030e 75
    0x49044070041070303185001c0d207006110944800c10b055491040d8840e61070412500c04c031a400300a416000c06800c880c103032400c50b40c0c4075a10000642514000d00040d5851101c40303004104050308640403440507111400d0458040100000203071026400800190048c100d100000d42003040c101010f00b000d41d801403e81d002501c80e420300543c3c1d00e000d800784e801d441c4103051301da881e50b192106000a1800180009042907070f50002881058080c0e585900c0c1441070a00c207040300890810302030100c40017180c1d0b6501c0101e4248040009208069011103c074203902e00d5004003589a8810050650727180039811907440115040c2d4487c0d6655111110b030101d1019800a84010408100101c610400c507200703000c820340355800306080f0f01ca548190720340c9610800a40000880d0450700d525482c45000c0d00056060f1f03038101003811544009201159448001480d00241d18900c011502600c04c1400200702c0c1e6003006c410b4a400840301c1040ca218060100b400030805110700b80380c401c81e00000e40340d030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 994347104 1250 994345854 994345871
    0xc1c060212090c031b010c03020f060c1c0c270803030109141806060111030c070f150206040201020a030c1b261504020d2a06090504090b0c0d0f 63
    0x54005800030384100b001405012150545450005001900929107951116041d4050701c01075982c1000d1010071000c1d40110340300c56402c40d00501c241071184c2c0c020035205685101025001c080b84108580000075945065017600031598031020f8280303060341c1d5440c0c031031500f180301e910203035200610380c0b0210281c0f000200200c0c000c081600459140d524021071082d481d2601001c611109003030740018800b1394400000a00c40b5803244041051000d03a05040d01e1510b280000054103002d1240c1200c584804171520800c810711381e400750302da201d510b1480503180c28105540002d442d00c0c44144003030b00300802843c5140074028490644160755103680740400c181642c4403040441f44148160425900640d41071030801d00c0c6c0040b65040c84220050443e0044d959140e0800480034074040c410340d040a4807400400d18070603400e071284144040e8115040201c1d00d080c0300106515980e400942c041c41c00c0080f00000244541c0545070040d684078107081e02c030004401d0200041120030051241c41c0d08010b0350 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 994348354 1250 994347104 994347127
    0x1020f040906061e1b020307080607020d0206010f1e080f0105040311070302090a02210405100606030204060507020d0303230604140f130204090c0806090c0a080c1c0602 74
    0x4004845100c803080c00480e9079500181c4136036032110084018500a1894040110b200d6480c865001303030450031540d945041900840d10b844030310f804c90446684464103201203a9010011100c4555072480141000e41c1013070f51001546400e8801c8002101050210644032032241d250600036000d113000311812008540394042c00382c00141e50903000300d1240481040000b002203030f01030580c0e07005014081140c40d0305d10180020b500817981010300d00b00c80f00c91002070308130036000c0c035010f5401b03040185810b140b4034650074100c0d00c40d035201030141881004204542d40c2c110094504542d01102e100500e1400c5040035006845a000340d0030780100b6112002401540b06182d507405103105480410001030183c1e500c4848500a5400540301c80e200c40004041526400c91030544900c05000880d003515969540041800c0075008055150030a104103c0ca2050420a401f0310340405c0300d8282c409031801001d1030721000b85107c0d0034003c40328841d03850002c0c0045810010101d600000441d81d4007011502c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 994349604 1250 994348354 994348357
    0xd0f02011b030e0f0a052b050106060504090c030203040c050907180b0403031704050a1506180f0c0e092a0307261905060418061a09010b1801090801020f 67
    0x2c0051054132071620a02181c24410061015a08080c1594806000506100302404040310036015401840c507501e00001d8001c0c00342000400180e1683d40d10380313050002e50400c0c2d4401948410815105000708004107080404130f50032902c0556540c40c4640701d1401c121035280708400b850345071300701413040000c4000401000b4001c4901a941c3c00c074103000444111b56940500f5a0003404a81c8103d24120210f0166203010701c240f2901d1310009840c82e078680031a54200b1883d01c81412450f5200b0107142c0d00b02c92030240317107103080706840c104440e0324070034000895882d0090080c0d00b41124850843d0945404031142034400c2c00c404010503140d25010900501c10f0394a41d480010540c090000031888000d040115405050500d101e444042c1c131800b074190081a0080015030311644428840c1c02c901c90380e88903008000d002c0c48020810f20b062942000c41c41c058103440390b0007038411600401050a1800c10380d00000082c25200c0071844080380101e680034013982084100f03520004e59890301d405a0ba0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 994350854 1250 994349604 994349627
    0x6011a0702042a03150608280f06080105090a080f13030f05010c180b0901090e0f01030203010e12090402070f0506010f0317040303020d030504020402040f0b03060a0806060d0f02011b03 81
    0x4580f00069004100320203840404d0303070f10600200d180c5400d028490203000034640c01503003c26851039056098003482c1b01603400d0b5592a2825940304054070b0704c0c1106001d14005401e441000340040e04200b0001076070303140b200718058049440844c00c00310031500001214100c00005c416142055241c1c10301207540881b01d201101d05610b41b4040340c04441c042c41400d0101b540c0d14800e486024900f0a103000310394460300000f410407200c1c05002c40d0f4001c00503511400350072100445485503046106045c02c42c0d0a281002095600640d4890300b0461003c00325444500151409604c929481c43c00741c21000d12100010300c80d000c2e1100100c0c0c15040100c5000441e0f000b00030055021480c050180d031584918000600140c200f4844050000d000e50441a040352001d0310041c03170b10b13070703500c011089020395500040191a000800d00030a45000510701010740a040701a10312801d081000070711a48840400030701c8032900e101c290f000d5a01030703a0181c161408110f100c14000e4220701d8010b1101c1c40c6c41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 994352104 1250 994350854 994350911
    0x606090d03020c04050f07090b03090102070b270c0a120507050603090303100504110423030105092103060105091909090b07021509060a0e010608010e01050f07080906011a070204 78
    0x21000030741c011700d40c9846c1402400b698444203101ea007440c202060341d81c0002d010006643d003c001100003d4003040c41c091048450702030000041000e148000329218410004082e10341c030883d8443c00c1ca55540c641403003110b908101182c10070040e0b15109017005e54592006a00690220400c548208080019440f45070802ca4045d02180c5540c00c0104884500b07001a80d4850140024447c4608240c80820141c015100310848a08401d0002e03080d140111160119a001612142c846000031550340a03152000d001a40c158070f03007500000d0081c06411145841221b4a50707031131400c0c1c107056400c800a0800450b00b842107806d18244000102e03000e441100061140048400400400104050140071030790003a00454440f034589101901500360184450355032810000360044003403140c8114544c103180049120b182100c50503040342c40041c860030900203820200300803918041109810750342400c543c0245a042241c64038441d0045c0c3c0c2c4000e4003d0700c0c1010f40c1a4000f200590144011001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 994353354 1250 994352104 994352111
    0x20c0a0803073c080a03060e010e070309171206120f0a03030b1219060b090c09060f0d05100f05010c03020604170c0d0810090b10080606090d03020c04 66
    0x1545486507a80c41500341c040c1c041a0240f0307482c07a52000c0c6902c80c2008503c41032405618011107000050115480c0b00d044034448800600d51032001e42500422004103408105400150301d05062124442402800b00041660705d40d504000c000c07000c81a4540c0341e184c1101c00e9181c103070000303800781004425903005204200380b0f861020703014000280340c540c0d0380700600600020021698260045c210290301564400420815032205070810404015100d0040e50300d0f90351980c8909210040344c0d1141d4a0700d015103405c178108a00d08d001c0398210b40c4500c1c400d807a9542d5800c0300c00d4480d1040e006984030705562030708002c01d1000144040a134034054691444501008541c0d035401598064030965005001d600b10030001000f00300b100c1a01c0400c1c040f000009460048404401403d0a083c0b40b140340109402c1010b20101c490300202c1c082c060801c9034020403034541001c0000d503680d80c0389043c05041000910000305192a258241c820564003d030050f582c000e95868040e44aa1021100340d015610703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 994354604 1250 994353354 994353359
    0x1c140901180b13030c2a050604060509040b0402040b0a02060a0b0d0f12050d050a0207060e0c0a031401020705031306080705040f09540c030305070302010b061801020c090c1b0c03010606020c0a 84
    0x244202209d04444550302c46902d0294071401b400050300360198034070b51060b4203120000300c94000c1c40080c2104240c540c080c19040c504428141d00311052902c1d9680954000d5581d0f00c00680c0039843c0c0d40c64140c02c074402501700e841c9070a08039840d01c20300e409056040d04100600440f0840c1d50050008540f090304280703c0040c062041c01eaa6500c40254544d00022840741000440c000c41038998600d11104009813800c010345d2100c40c615404034a5a480800f0320310400c0100c607510504a0342c100300240782c450320b001c0c41c1030311010145c2d0650042d03005a0355509a0071003501c0100c0d403002041039090200200e800342010122800c1800300c14a0881024030001e20702d680400721440405540d402a00d001945003075031800c58003a00714900880540d175a0740102c141d5540c03801c018020250b001c2c00700041c8003459000090078080003003141e50183c1c542c80c0501550060210580305034100001010501c19108000185013000a42c14190194644000850303950b03404034440786407240c01c0d6034402200b903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 994355854 1250 994354604 994354609
    0x7030819020c03071a04030209010e100b0903030909090c030f100c091a0304150e060712140411011b0c05030c01050a0f051c140901180b13030c2a05 65
    0x10318070b41296038544c00080b41800300d808041e44120301c0140d034449040c2010349a5020801d419003c0c1c00000c0074503004401c000d603d4517450031100c0504800c8464070305204041d00826928010342410f6803081c40c42d0b00c0080d0202c00100900f00c0380010041c05c460580c00d03c903a04c00d031105616440009110b00f4040c1034900c450054590604031500e68140c070002c0601207012151030340000c1e008507444030f0181c2c250394000c50940520003111501c20064400c1d404c00f00c2c40500415001d2036114201410018446c442801e1031030203e03806a00f003001100382c0e0912a004032202480115248400d007900301d200e100b80920701001b241901d80a070110740000b40d88900544540c042c2805200010b003d241140720614894070242c00400c01211b045010300c2c00304940442610b0702c036250fa104480a1104204d0320103024054500b000951404032500100c0710385132024052401043e03004100c2c1400300d0030b0200b6110b034004000d0250003402d0b0b40000381c0001c3c041c030745418641100c1c00c03169881100104951 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 994357104 1250 994355854 994355863
    0x60715060f030c03082209020909060f1e041b0203181c2a17010623220504051b1504050f220b043b010207050703081902 53
    0x26500110fa10b05014038550f60240da590050050021072200c610351440c50055005d041c2000d41407103540561150403450501c0080319004211611450200802403059203031745000309000d060b10340d44007450480540c0414041d14010700040c4000d461040c0b00c2c80440e1707010000e1f2001c0f840d015000698080c8090030030155490880d80100d80c0301b0310100b07000004414104202d00402880e164544541c071044603046803500c540d10004107e40ca1283c1c6111041081c0714100103400c030507440f2496008034040d281e40c10040070320780e54005c800003001d00300c812100d06040001002500c10900091406250003030f1249858034058504c0c8600002c80016460704264500035105040d4950741420302d042d00304000386c07032020182a00050081e248540c1e007844502c01c40c0b0550301807400031680480c00302c02c0c0000c44201c034201001c400180c86003d170aa4106007051300005111111002a04c521038490030b0091041c0c0000070040d01ca00c100010401c03540c0c102500c5443e010055005110041c03000a0ba141c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 994358354 1250 994357104 994357109
    0x5010f4409030a05180a0e0103150501032004090b0a0c02061506160201050702090405300d020714010c021c0305070f050c0102250524040b0c09060715060f 68
    0x40c0c00c1804009512031240d800780c40c1d8505c1004045501d039070310001080d04a1400e400c000b800c500030301c006100f4450100000c400441d800e2008101d50741c5540c882c00c00c2185180c00f517075102c0150403410030f081d54498000360320040d001031801c05107040c41000c440c01846001b0350fa03009802201c000500c0c13698a09280105014058482e52030060f004400d4608900010300403810300034103103c11409a101c500300c091081c2d21400003010450724880b6440380c04943c06103406410040b840f10500902e48400c1a200d0001e010100035072030f440b0307d150440e4002603002c420100d562074100401251907001450320b1843c20380302c245100e44140e807070048003035420454110011490249030103210a200b800108880c00b81e403000141025918072501210907840307001c5105c1d003030440361064144030f01401207a0b41502d140c106c4002810804e84901c15207540188082c0c15152404002400314100b5070464102010003005c96555420a03d0410b00840003640c1614081e441c00d80003182c4008080280703400e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 994359604 1250 994358354 994358371
    0x20c01020c0f03040e011404090501021801020613020102070e220312140c16020118032a0e0f040203070302131d0c0612041e0302030a14040e0105010f44 67
    0x20380c5c0c05c7c4444c1d11141d0044041c050f4125035203120f1980450f00030703c050301400d60b288840320300680b00030000903d00000030707104055245e242054400182c1c0c0003c3c070344c8100d0302045440103a41d5a5400070880c824a4041c00340c059440d60b8610004160b03000400c0c210203044504200544001c41150b01d00b007201c01c8403041d90f01c110805c0306d03981c00c00d8074515001095105240400c4c3ca0402c3c071003141c4030300003c0d81c030881d089010500d414540c02c0140b51585481c0c109a8035030800c5510307040103003841d16805840c0c0050040502c000c1015500c051000001858000c4c2c034a1405000b105100b1000341100780500b8542030f0b1103481048a500301080801c02d40100401543c18804042c2030700c501043c010348102c44510401e138181803e07061a0031358004480c02030b00a56118013001602134191600c901c400d5101d070310108014051041a141400c0c1592028031384107944c1140c201d001d407043d2400008040291544108821405031000f4180031203111410000800d0890301592141c0000151180030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 994360854 1250 994359604 994359629
    0x7150804020a092412060b040b0f011d06270a140f010c0b0c04170106120b0a021315020f1204060c020303040f0801270c0e0910020c01020c0f0304 64
    0x7061402c1c9130820400a24201452101411800d00031064040c956001803024201c0d0076214041c050f051003002d00c0000c1c1038405215a00105001517030800d00d03202068180a419481d03c4904505100c8950401c40050400d5564480c0d01400280e4280d00b0690f007034803541403021054560078441d012401b15000d00741d900307031b4008108042014004e44050900e04010a6a1b24100071070352556000c0c1c080d402903015990368034140900d0581741014075841d50881c0c0e0500d6020000300001901103055507800590f806100e4076010034060181c0f062105165003540b5002011580c804490f855000d40c034915000c58018140449050752101c02902011403000130a00c800c1004074081d01036a0000c600c0203083d64174198035601460b0107a086500b14204581d510030341e110540c0d0f00703869040070940c5c1c0c42d642001c102000e41d0b501b1031a1456170145541c10303071014012501c4d008040100e05400c0745005010b40d04c1d0012a40414003c2d002450401d1031441007090100303d0000201c00c5400f80e980040140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 994362104 1250 994360854 994360859
    0x9030e1e0a0e07030209031603020f1e0409080705060915060a0308030a1d07060c1e02031f020912150106112e050c0d0501050102031603080901060807030507150804020a 74
    0xc038003142c001070442c41071640800c441c01032070341c0c14041c103140902d044e16155081c90440c014001600ca8040403603000384a017140b904680510001c0900c03448204650200d11001203180c864104d0084107001029481440180840240042000e001d0405c001600200503030303d400810540d100c0d18880a0f00c03200041002c00c2e510412038110351868007401d010354101e03040303007400585406140d51003180001e40044c1440c0801110440c0b8403410340c0e20314500b1480c0c0060b0f800081c1c95617210500007403820224081c0103540311644e0140d0308480002410643c0e43c1808501040e12203822010381c1070301c0c050b800004981503001e5840d0700315400d03e48004103942c000c12580889c4203d1226440c6111080d00044401c10700e00034022f441c03040741c2d5580100d4883c09031034100020350701c3c10782056041d90000c0c001d020b03191061540d460081500351a0504040d15000143ca005240a810002c2940502c900100c1481070000c0d40030102c1d20380440c21194502d41e0507003291156402d850082d8080300a0004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 994363354 1250 994362104 994362119
    0xa170702041103130f050a080a0207060e060a05090418150b19030309030201050d060e241002030307031e1a030f0708030427051f0b030c04030219030609030e1e0a 71
    0x310240a00c071b00204c0d604400350740c03030303051503600300d09203800060f13000450038804d06030b1041c2da004da507000c1036407440c2c14640d44c00005801ca0150601c0c59016540c1c23898040c00003a07002a0300d401541d0010118900800d6802d405409440e5100000d030240152980b210710841403036800030101c030b8256603054422802c650044800ba40061712040c100e035281c000104100c00c40c460301d603018405407103c3d01c0725060241095081e00b141800b0343c0d80f2a04118840a5401d80c000c01226840361407450001a050092154450403a060350ad100700d0091a00341d00c020520100d0b80d09101c0d43e90110304039059071020031116503403540e45000d9100c080d0006d12082000450801c54075503002d002e001031a03410f54107500d448046071000c98400c002044150140900d101101d09400c010b40030341c4070254518034002e000c02c0c45034440c0d80708c000e000340d0105106499080200d88680701031548290280080c0500381002454003801d411110b1003400c06c0b1003210655103400211100c03551300a0720307140d24545401c22 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 994364604 1250 994363354 994363373
    0x1a09060d0822060815040504030e010f05160606050909060c0d050c1207090618060c020f04090b0a02031f1d06190303080109060803030c040e04050a17070204110313 72
    0x2d9450a1020b608120729030744000045005403042e541e0f142440d00d0011100d628118030007000c0c502480c0b42009101c0440c0c2e100380381c17074066582070900c505404140401100c0621840380500102110b4825050421200e604031000300c810440300b2a00d070383c8a10b1801034455a00359040180380034204001e6072020101d4002543c44201c40310b240e03040000b600d1a501c00104115038503c002006a5070a1180903040044411103004414017000c0c26400c08101410305a0200302c00b83c07141514500a080701d41c2d40c0c0e040007030680e6100c410302a150401d00403080180d0000d554642e050112201c0380000785d041d002200045800d000e4215050300c0d81d06208004001011304401e4010000e050081840c0240400c0080258071a03035a042456152140b03550032102d454112042540041050160b86c0e15820b060b5400e94818104202c06900d40f40b400d40e2800c254290700030440c0700200741540c5203007510406416590700a0310700740071080000f40c0b080c1213840112410801501407844181c00328007a02d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 994365854 1250 994364604 994364617
    0x24010e06010302040f1410020705010e060f0c010212090f0c06070201030203060301060308180a05030c0d0231230f1b0702090901061d040c09020a050912011a09060d08 73
    0x400600c0e00341c17140b030034070420626500881150703292240c096500b8140301c603181104810501c050f0540605060000341401c0719420080d10505c40418200c648040c00f404541308081e200d402199544501483e482d680001210b111f03200d405698408403a0840c0880c00031107000c2c00070000f43c6040030a0b40150025080903013200c0d019980c1c0c00c1c010001800d200010048903d61085282002d8128001c000a10020343c000c0f6001c1d800c12a034030040c50702d0307000084888030740c100c07400d411035075480040401410628a8001501000308540110540b0341e501c00104900c1c106121041c01d084004c03261392036141540d0400e191404d130b000081c1020446403500070142e000070700113460543c01d41c00003841e1000560f0b040249035900e4030100000140c0c0e01611103600c1c0d20a502c640c0c075142c16210000f00c444140300d10038142c0c1d000a02c050645119800321803881c40020044085918014501402005030156400c3c00b15050003001c01c00380b03800d04540b841414000d000b40708906540d980c20195801c8030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 994367104 1250 994365854 994365857
    0x80c0d0f0501060e1b0c060106112e2301090c092c1605030a091a1008011a06070f081c05060102060a05130f1401020d0e24010e0601 58
    0xd40c0d2000051000e01030700c0c0082c11240940062400e0004ca82111410110080708024008000c489002c950200d40181168901d04200c43d0030200d0209640c204030700207003c44034440600f030507200b103090b4041140c1040507550000300028040e9400c2d004800e046001d0031140d20001c0c0740104001c41c0346030400407007074440c1c4c9002c29290b40d85940301c9011076041800c100102d0034104501034242181e5030308551150511a4071003101c1c402010291084c1310191041d4880c82c1c1302c4170b400c0188030f880481149440809542d24a492516943e018601c80c46030003146215400d104118040101c0320500c2d0900c52030040a0b540350070703495074a5245185e150102110399440601c064190580341510b220702c205189107011801e460020300090400c01c0041500d854a842d00081c003409a8036140a403030000e43c014032400301e5080c0d6041030503038411540c89103100d9600015945e50a2000340d0001c9000c0c0d101c545c100d0701502120b240c0d0620600d41c1c4080c0a410102d41e50040049200e0300b02411b40081c4103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 994368354 1250 994367104 994367123
    0x10031b0801261902130c030603060c031b23041205010c020105070f110106050a031b08030f041707180603140d02123007080a0504150902030f03040807031209080c0d 72
    0x5044840058035040c0324504042566048c0030000c0c00418010880014068a0100b021426000c0c4006100100d80c4245003040010a080c51f81e8401042d20114014420904c042c0c0b159a41c07014008040e28402c422140c5500701506101820700500542d8010b43c03071511250030003030b03407004200e900e0302121081410b19901c0b601e0024040d2140c403e9200594080e000e030812000c4d0f0541280c5d0300d081903910060842d8000c11000c0202844203060b2015203c80c4921003011076a80e6030001c3c40d05080e5000440e403244050030700007030040107901c014100c1e4440d41e841d0340340ba8004400f076601c03000303484420805a04210303014001020444010300c2007581c000d8090b540803071118020f82d544002c2c1442e500001c200441400718242e000300c091340e4481c1908400b8816403419580d13450030b070b0001d00c180034001c0e500c1c0c00842e01195024854002c004450004981e11981c1d90100f095071000c05204c140c0c0c1800d403007080d41d0806e070721550080090b01c20780c40081c00d900e0180b4090200e00600c404040e1b1318400c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 994369604 1250 994368354 994368379
    0x20102070e01060509121609020f0c070f08010b01030e03030604090f05060f071d13020f070b04050c0f030a05060412090b030709090507030603050c10031b0801261902 73
    0x71031050450107808960384480c0c455905c01c1c14000c035644a40710590155002d60400f021000000c11841d041c0d4103c000056110b030314601d0b581e1a14010540180e009006004c00401d0002d40070114004468410340240229240c40c4015800c40e00140014511500100001602400c180e0400402188104601d1000081c2c81d15001e003000700c103840152140c1003080c01d2001c20342e44129146021211030442e644407100350700016011900300582c1c075007083e0300030550b40304440010090b00e2000790043c0c4900610700c3c0501c2c2081d01c41d6100e00441e40309041c00301e207040c803900340022500042544540104001c0c1c41700d0b110201c07000209103003030042003000c80707000c41d0040044c2c015600503032054a406050500303014030102910001403c04040520781441080070402c0010108000700e0280c1c1d150310883d01506044000e030000701304100d0666001803842035811303840b2000c2812607800055a04500d0445c91a80030300500c110380105a9500002080c5002c0c0308011143c20f01d03a1004158120215 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 994370854 1250 994369604 994369619
    0x82d041a070f05100b090a060b0307030c05090d050102090312120c09060f0c010c08060609030304141201090507060215060901060e041d07210305040b0706020705100b011b11010c02010207 82
    0x440b002c0344188440d00c80510400c40d05003d00c01b29040030700d0320000d000c818188000002d80e03000050080b030426840341070b6180301500030b40071244080340281110010310ba03241040340c040d40c03188990724000d204a0400c6004901441d040d10361204107403214810075101c403e03402c5000e03041185442c0e444801001702c00e00c1240d01c13100400320885010000324240c1c8640e0030190407040000c011500600f4200034000156402000321419524135010b04107508101c08042005082e40520b036040075882d0203180424041700040443c107d4807a40c0c07c4032000000780c1012200c440707023510015000003525005004a038050381c074680f40f4001c0a0000240c0c5410505540180d8090021003001900081c0d01801450f9401034100c0204032040e0f40c8036011072844e500102a0300c03d504c180b050056000c2112810401c10303030101c03058203402c5412140c20314002141940104054030001d804200818004480402c0001d054402d0603000318400c01c3c0c0c8400000196840342c46090200d0450180c0c070004070703106c2c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 994372104 1250 994370854 994370863
    0x312021207140610051003092109080f0309060a0e0409020d14010609050c0301090b03100507080121020d02090c0d0203090703020f2b0f082d041a070f05 67
    0xa80160750b6122949048a1114140340001e008a05116a04d00003801a5117030a0422490201e03079203000240100c245c249400314030034170100156444641440c0c0b030b407000d0703000d2880011348002c2e03415101105d0075000744982d00d100c0c440175213421050078003c00d40c4407401041440c402c2c08001d04085403102081e40082c01444001100715915030782c103400e0000b612003d1064a000c1c1034141003c0150f41010840f5031201c5c041446842c20f0940c030f44080440689042c010310100c0000d101040c08030b4104080041c00c0035009004096000700d04d444030401c440ca0f10402901c4007a0040c2c1000783e03060b555000d01512040042400741213600400c002c101c142c400317100440c45489190090012141503204118100e07505031030341da129050f030701641c5034564488400d0a803801e40e0481c0380c04506d6528903110300401103140000d45075901c00b04000000316500308000450308050700c1000003816142d201c04086e4002e071f00410321901400c0d9400355004140328020f28034140079010401c4200d120b41c0e40d06150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 994373354 1250 994372104 994372117
    0x2070c0e0702011401090b0f130e0303070e040c091d0a021e130f05090a0e010b040203070816020d02030d09062a031506050a0e01030e07060c0b0f1003120212 69
    0x6070340d075401e544e5550312071100c003a01400c0020801d0021814a00c0060520181c000c0f030306220b03411302a079030004104160301c800c0c03007025180140e80c1c0703a2400d8800586581c40400c40c050086041c18510f000e984e105c8d50003d0203480064400801c2c800c503100740c038400000c004203200c1c60513900b000501c428521104020800c41650700300d9a51713403d003002540d004248180e11003000d1032170700d0320288515644c9003c680d5002c09805400144084e0103d03c042c0500741c0d070f0b9150707508a840042030080c1c540e0b0017943e00d8802d101c5081c0301d5100480f500d01c220f9035900350071801d1006070010b02980c15070100b140c01c125003c1d0f0040401042c84c11862013118458103035522801100d0403030f11500e1490607090301441c4042e00c2003200c0b0121191400501030a140305480d402001c11000c82c0c05190542e01035030043c1002801d0070204c504443c0c40d06400340049840090030b45200c607600001402484031107058030702c50b00200c00032074886032869458010380c1c4003100003001507006101c40c01c26842c00c00c0c40034228 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 994374604 1250 994373354 994373357
    0xa0203062e180f060507030509060711031522080409051602060901180b0406021b0c041d2805010c0810151d0406090603050a0b0105101202070c0e07 65
    0x100700d0480000a00508a01c0450003107030030000b4010024040500144021140c2e40d040056503140b580c542203959100343c07920103170f0190780420000e09004040602e60080301c415400c0710002d0340c040c6414034032482c0c00ca0304202000000d041030b0368140444c07612000003d2003840198100b40d10340d2000d1045d2101200e5000c4802840c1502c00400c40c1e042080c0c0741c002c000c00000700082e01786549000e10310345080c90041d00e00d8112801042c200a0141c2c1244c96014101039800d103a01c1005c24800e0b107861031100c1240c4114104052034181202805030b62206809510041440c4c400001c017481d0722103000c4010b02102214401001c0c0895001c0c0107001e207900480d0380b03c0306145002d2441ba007880c04160402c1414050381d0128001e0542c0102440092070905000035444500c1c0a0020340580034640000407100d04020000040000008171456114424414a0300070781c3c80d80103100700d43c2c050142d40000117115a03050901038240b03900415074140a2420103000f2519411072403500b8409441400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 994375854 1250 994374604 994374679
    0x4020f0f0c0d03050c04241b0b0105031011120a0e060a091209081b031c021e0a030203040b0f04240305010602070f260a0b0a140601080a020306 63
    0x1584035810b00c50740b0782c03044040c0800c41c103142c240b00114021510300400c40d95200b080c050a107c0050082c601010340c0540c100d00146005568605001205401e210f01400780c8038a03400d0748000c143c2c4d40602c0411518880e080c50078035894043c403040c10403015040c00200da6440011700001c1d84148619803150b507408001250100840c900500100d14a42aa400b000007020080c40070620101d103091015017200a035203050108000001d04190245102035000354003900070500281c1c01103140340700701012600d4064038517000e10310303140c4070007500b4402401a00100424001214110050140101139404e414245911108900c0007110050240402902101e2900d000c1c26414001c0e14050007051000e00300d424a00b24107454641c5035402a8400700c5003000c0140e042c90040f41240003505420405c88601c500a4144030040560942c1d41181c02d42c00d04103540000c12410348414025281a0340345400d0344c1d10900d6000081d00050145a800007000b4058880c1a040d1840d80078203401910881 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 994377104 1250 994375854 994375873
    0x30f0a0609061116120c081b0c22051305060121050d050711040608120904090c0605040503070e04241508030d0e07120201050f0f03191113030204020f0f0c 68
    0x10b007076240385000140100b0401080c840006107e000645504a46040e6803841c2e05810100d030034203011800002c0da401240060303c0c1c1c180013008035090020851000020046519005400308420004183c094020340c0309400410500740c2c114290b12079110741e00041158206c40396246410500300004900c00610f01040b043c0500007100b0061541da441120200a0b281c0f40c400b500d521246200c103019601040400c0085054650742c09c042045035009010204941e19148090f00c1c0360002e000d19800317441100000b00c1e041400d0210540159002807483c04401182860b41022503803c90a80c0d1100b03032191103002c4c2b10241d9a103d07001916190010b103460340039808202c0d084620381945204e46030710090041003100c0180e40f40c0308420760203191030b81d59442d4086480c01c49114250040945c11000000c0180780c1c860061400c51030403600300c0078000d0202c000781c0c0075041e00810a020081c00d8549504100501e090786c014220010003005150030800181c203a0041c5411540d030007582500130100c41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 994378354 1250 994377104 994377113
    0xe01210b1e180601110106030606061403010b0405060307031d010c1b0b180a0c0815070f2c040c050403020909031603111207060e0c030f0a0609061116 66
    0xd590701c0c051429800300c554024001450760200ea112522204000102045203644145841566130081c40020711031550b49180c580000c0030b1601c078250010b1046003821a50007021822031f81250ba01c15020740c1018108800c2040075030018003060149a510012552003804401c02c200c2042941d20000550340c00c101d1000d002d49074034010806408404004030f00005071260340307040c0c2220301074103803c61407160081001d261101c031a5010741010120b000c0000c402c8070009401c070f0400030a200440c01c0d501c0d513003c00d80307110350225a5000880c2d00850090b18010003111113020b803001d441160011030700d0045c0403c00716401c1c00c12040015400243c107100350309102c040381350460006001036140201000180c104819122402400c01103100019101d4060410004692113030f00f40046681e80d1651912a0041804180d1030402d4007178507091403894640441c048904e9202c18018010280303c0355540e50003000c085008594003580c6244d400075811010019240e40c9400340c0130386101d03a605082 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 994379604 1250 994378354 994378369
    0xc22051f091b1b03031a0405090d020c0108010510080915091b0603010e01030209181c080601031e3b0f0307030c0b04020105210a1a030d0e01210b 64
    0x1070074401880f003614580300309a5103619040740c0510740001c9600f4004d41400c103000c1d1040c82260b203d8140b109000220b100814148140e00142c0c08483c0e0a06003000107491920091003401d80c44040c0c0c00051066600800c1090380c8980d41c4800d641e80c0c01c03d8040c0200d6245816a040355427603103c00c3c48142c2c00408249541907021080b5521401d642c90404071909140050000070b00441071000030900c6800c01848055000100000369a1b110b20410008410003158035002c03030014201c1008070340654040c0c410321082200c15031510030104041c09411014102880900290a02d155401d58120300107004070344080d001011210040c034401c401803403800e00780c0c984121054000f044a080001e802c02d00d8060b800e45d00808003d904d55917030005071170340e010304200940700600e440e0b060080c0c80c4c0358a517034034491200548100f25141d40c01810201800510071180d8056001301400700205004c0d1740c2004000f80145403001014030813145c4a201c81072210340d540030340c688036162640149400c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 994380854 1250 994379604 994379651
    0xc050a09060e06040c05121311040b0114090a0e09030301051504080712060b03030a11100b031209040e101a010c020310150b040b0304050c22051f09 65
    0xc400780012420114007801d4040090000d611541d41c038144102094012403c2c3c0f13800c83c0c0c10250f03800141c40d00c4180314070602401b10040710100c848030909683da15051050402440060355140300700424007025550661101d030b00075500c00c400c03820014030720441c0f16580c0e21a14500300a15100c1d49800140240c020007032186100d12901400700380144580001d9500440b0702004040303101103800e042c054024100f00501d1901400001140c0c00c0494111501c00d100c1c5518108486802002a0030101110700009040d80d0503004051015404102503014000c44ca0004000161055100130340601d496402ca040f480150340726005040c1342e00301111220450340c000c0c28901510f04856002030745030409440c0710050782c0d5403040d0011444d1a80440da001805c00309000a42d216200c40200d10030350000c6078215098803c80001c6044c0b401e280c08000c00f0b2054100219008425800081014050062241644110443c0d0003800800c696038140e009000687e00098103012102020b04006900c2c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 994382104 1250 994380854 994380869
    0x11815020306030a260315210c013e1b060403060c090b0c03040f0504090812090c0301050415050717011415040806012102030706030221040c050a 64
    0x184100452900e0118804a040398440e07000c41c0400008410170001c014907070301d800389068001c4200480e07600000d4900840003022241c14900313421004000750a070781d0308102d40c1506e0704180c000c04482d5005000d0300740100c4c4400c218422610503030b40c0c840041c80010f150300030074000140c03031500049001d00007201c0c070040d02d59601160384601408100703940304520004101c40d585010103030302d4500c0368803454081c04038110b10956490007009440d0780c9802c14010f8014000042c0341c0002c03203152900c500101c2179407209a0508081c429401c01d09008801400002540a4001e840005170780030b20030240305a01c5221141380f044207201092040f1800100244d0602c4034003000c0c0504801d404c20307524110b8404000e403c425100c45c3e07020075054400c0384030742c035060b0f140401c1c040390009000c1080c5044c0c0e074118200c104250682c80301c05e80760b841c0c0010301a40542100f141488024441c3d001460210000d04000581001142c2100040700c02104c040d14030703102d5200c1c1884680348c055410402400403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 994383354 1250 994382104 994382107
    0x60f231e0402270108160f080721080d06090c020a0302100f090203150a1503080d020a0504170c0307091512030e0607030206010e06010f080f0c040801181502 69
    0x14218181950140a40081d02c00e010481519802004032000f2440c03007072812030003542550b035030b81c90550348000c000c1140c4650240100c010481800b9161500100d4800c48028002d076443c01584110504002c4e00076600c01c0b13041c04074400450148401841941c0100c580020b0061905c40c0f603e0884141c5001c070821901f180400310003017640004c100c060040001000130f200d16050400790010100e4000c000e40500400048030350218100b2591807041f1081c0b2403d04c0786050070066139010003120301000b081c035103007408003803500400796000d40907058a50403c1032030243c81d0406c180c0405540251080c0c95800f071601825141028001a40100303441c82041c007403800403201c40d8016640e90f00030960b1090078401840c09040c424401e00b5030308503020780440c0d5509628100292920002d0141201604001f80821703050f500c034002e04013603810786903a80305490b158101030a031401c8000c0e0010b09030100501020030b41c82d10a100c0c3c40026021240c652080011500e02548444001240c241d03d8610 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 994384604 1250 994383354 994383391
    0x1403010f0b0f010e0301020d0c021e0109030801030f051513170a0c08090a24020105070f08010323030a03020d0605060f04151403070309140f0c0d060f23 67
    0x102c440803000c480e5000d0a2034411840c070400800d00a0184405141065003040180011980c0118000d4051707a070403000303000820203490641d07003601c65200c4d008002811040040000c1290208040031aa00c240141e5400c8410711450009541007550881c030302c4c21408801c20100810111194021040103845078101000703154013030000c1800d40005003070341d100007441080300d0352102e0302040a000c1c4669101c00d0420800082c076508040d00008402540c40c11001c1024580103c00d4401c614a880e41c07440d041e40e003181e0b00c18400d41642e510086a4034284036503181c1c00c80c4144060001403220303540c01030f01c5800028880d01030f980140c0c0300d40d000c1d640400010200140c400126420748045101400303103203810400403500c00030b070348200944200c00407060211040c1d06030090114075000b5189441c88009820005840c0d1205081002c0b003540309401d242000d060a51200c40740da401b450300010740207000000b01080c0c5000e907000344110000c20380d8842401441040054101802c031089004410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 994385854 1250 994384604 994384609
    0x609010b031009021311070b092109010e1f020c0105070c0b07082503030f0b0a05010e21010f0c020f030d020f041223011404020f060f041403010f0b 65
    0x100e0002c503110040e00c4581200554a0b110703104980b010107420104910342007004050751603003040100b11805c03000030700400c003001000203540d01e080180140b000420034480c014019603a016041c580e041c8a403004400b9950ba881a400501d0b1021000f4414180784206600904101600c0903090602c1018071981001c41d0340a50030100307079054880d00940c0d80c110350414075168000da803109054100c012025440340500301181c07010081c82038905000c2c600c0340410030420384801501c1b040d01302e80d200a04002030744c89134450160009001d00b000100d145202c0e0b480301e0b000840c03207407032140340e4503050228140915407086c6a4801030a2014104610344107a40f0340c3c4910900300c2c080e00058021440300190150201110001e2003241341c030550600f200e18261050b4400c4800c1e10381062103150070b014000206015104003185440b071a0344c0c26607201e07804c000200e40302518031350b0824414005501c8003420000103102070904182100c0104011030201403e40b02080b00d180d21031402c0000003200354 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 994387104 1250 994385854 994385863
    0x606020709020304110a0f080601050904030e0f0103200304020a0f0509070320041805180d0309140a0b090c01021b0f24070b01080d050a12020720030609010b03 70
    0x4998001c40966a91598102007550190311080c9a602c2000ca000c0002c6401180c02074800720f0f1040d10903900e10b41c4c2d03500200401c0c61004c98019021030b840c4107128180d4500540e500d448190141400100c08a81d50602c0d40480d0307406540c0d01c40200b00006200070740c6411100742008000b9070f8490084141000c0101c0c0406c80041e00c20020300d6200c10295042440c0749108142a80040c841030b5140c0c0e588820500e000301c030a041c9001440e00d86808240703480c2002c40403030030500b81c1c14024004928408000c500401300ac6030b041c0e401c0b48035101d84140c0c0e044184001c00366a030142807400d419092200d00c1c5410000341300c00d01410340d804001040401803021b80418081c040440b082e0020030802804141c1c44440c54840c40300328808400c80b40c03506402da501030082c6a0280c03140340c101c1da1302c41c003416603102d41081c441000300d501806450010f500c150412009400c40310009824500c0326503488808003081400c0440102e90b0050130000c41c101040102e0340003510100078000f5551803030229444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 994388354 1250 994387104 994387109
    0x170913050127060e1003202101060909060501031401050907170313080f070b07021309030c06060b030711030306010905013b191802250b04060f06060207 67
    0x102c11242800181c00c8260340440300401e01400958024542848110b03030281c1c1c0e501044480344100350b80c2042c00322444488684d04040130782941c0d2106d180342502c0f101004042c89648007907480381c00102c1c5c100b00b203001c0e90840c148100400f20b0b07594194500440201541d0005582c241c1c50a0104982c00100040005c01c40700d13074071181e901841c10302000c3d03810361080e00181c80003020880000245c9640001d030078454002002d0a40701c0d003588603d031410480c8a640b001031340c4140c0c19080c1e4038000700c10350f00510b5018440e080074032070b01c182503540034292001e13540310107034001000c402c20120340e81005010603102035403009149985012000603000c03140c00d0050714100459289c141100040c542a030300710030543c140030320440c42507412405403803102c031064560081e000110030106455804030b0100075a6038540c1a40c5182c0711a000c035074000d401c030902801d084029a510000d0342c1c81b0014500d440c07640210101400c2d031520741800c60a49042801481c030b82458000204411030b40400c02005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 994389604 1250 994388354 994388399
    0x702040e160e0a06120309030c080d080f06030102090a06050919180b060c07120c050102071503050408090a0810152111040e07030606080613031b1709130501 69
    0x82c96180e260380b45000b052941c00858140c000d03180b40038141500a074404003101e201e06442d0300d881d600c9281080e03d030300c0354140000204000030081801c8031608540a40c0c09000030f000141031a4000c0d0004d1003041751940102c012500000e805140d42c100180800d0518103c0a040701d6854600405182c440009040c2070b54415030751240e2403029900d044c102c5902c20b403240c0840e81d0454640d0f001d242c06611881040314201e0581200040b10f5002064480032909110038006400364050740940280000504c2101d18003800c20160003103549142c2d488015003001c3c001011700c00d1600f502038040302c90224185052105c407000c00c014580769000140d650000700c000c0c1603217074000c524010403007a208086003588181848858240d00380002004070440340100d40900460b9521540c035030322610241c4400090301d040030342c01000302c1e001e8044003c9607170500b13800716650f90a5444014610b004014001d00018000560710210f03c0e218414610400c2505001c00c5154540030141c1003464041c1144032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 994390854 1250 994389604 994389629
    0x302011b060f020f1b0606100f110105040803150f0907050a09080307050d080c0901020d051b0607020d140c0a06111e030403091211060310090e030702040e16 69
    0x10000d5a410142c0300411444040d5110386045000340c0d61900029801c40c040700c05c0002084280000113415070090307074058541381050b02c410398115075182c1c000c1041001e00c8100b2501c840c1e5060b091054034480c030700810103152a81000f55200c041c0d1141d0b070407050f100301c5140104403210703941d60320026004142410280d075151081c25003501d0380303050707a400b2100c3c0d0b00000c01d01c041072101c082407030307182c040782e83e40d6030600341d562044641c0c0030b4054445018010b0b0301008062050300d0140c0c000300640c1d01c2d20050304203070be200b4024040c517004040f40c0b003200607004070000c5007001e904a6164102c1c4400614080d0610203210711841e0341c3d03501003c010305500d49454a19030740b003400c1c40c00c0350500050001c208a2040c44c00c90544826032058074120b0002e0101200029110442401d900f00280d110f403204000c0ca02d0901000350301d81000d0945a840040c401e030014001c0403510500c090500090099501c0e8562401040b0846090031356116a81e0050410890304201056001c800d6500c0400e402 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 994392104 1250 994390854 994390907
    0x10212131205031807080d02160b040b070609080a0f0905030d230c070803030105010e09160c02010e040c081927062d0606090b12060f0a0b0c0c0604030201 68
    0x4194041e40000d510354038045c1c4280131600a8020400c40500d4000d50212030b241d124590880c00061060300c109e20441078244009c3c440303050340360014502580101804a0510480e49400d04190300c40c448a1010a00d48440c805d8100e0304048a540100f070203c0c040d00a52586100c0039182c0780d03030005105620b003000001000c841c4180015a002e510000084614080c0c8440034a81d69910078001c0d2030204868000c140c00a1901e41d42041c49000d00d1740082680c28140201910010200d800403030610840c2d858401e03171178856203e2048001125a00e01c0e10b10b0610181d4001e6808200d41005482c1f414810690307949139490242c451100840d00308810401400d061100080ca0301242402d001190b140304111284002ca014110000344480c0401c107240c2d0f11502039038142c0c0e41e03220744011081d06001001d14080c2d44407465a100c0701c05404003200c001c1000006031010042d401c140040c0c800890004105030b410885482490400d030340440c506400d54002070200c1c010044a01c10500c601c6141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 994393354 1250 994392104 994392121
    0x201150317070f12090b04065c0102070c050d08070507060f020d030b0a05060c0708070e04030206070c0f14160f050117011a0304170c01021213120503 66
    0x40b600090341203044000a01003034946030503198101034101c00080c542260100340c80300050101e804503100c07615070521014a00400f1885410200c01d0400ca40041c0c40215003072040c2103d0321000d0030b40c210907000b150300308602030000c0d654001d8610140c2d68030520040f0700003910460303071200f038a50894401c2448220341c6020041407103001402802806840b00c0018400c0d0000702c240300030034168013034852042d4003400407402c0b5500c0b8104a81d0080700d5002c10800c50809400a20711420180140c4981d180c4541c80c052a00e00c0c154401075000c48101c00304001e043d8140003007608a0310b6860004211039254941405030b2080c0c440141c000c0705850b01c0610080820058602002817154440d6000f66a64100184100c01e92203801d000c2001c090a130307a490540b0080d45410303a548040c0761207052040350017807801504020021651300f2082d41c507441c440503190020344100b1903020000341e40e40c0000f500c0220316060140240c0c0c0304070100c41030b00c00014044405202100c21500d410b80d16561030707040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 994394604 1250 994393354 994393357
    0x70f08210318160e07080c0711040f0e0118032709021804090b07120b03030f0915040902030109060f031218181401050a0302060a08040809130203070801060201150317 73
    0x80b552800080043c0000c00b5540b0401d034034801c2d9845c0e1101131413552804108001d620510130014069181c40c108210540b8150b131140380c1c00442650001002006120803e085038038289040c0342c400c8138024031000f003550010b9102445a480206e0605c0481d40812544c3e00c001c050090340c1c445c54000c00c20302d20b0140d107480385541c2880010418001300d138840c10720300c205090944e500700000780b11a103020100500342c010300b0401c60f400b400540c5001c11902d500581500400d40d0309500c000c2400052129174441c8014102522a40e0741c0180d0341c0d40340840c0d003002c42e0311030713400b503145041e801e4002c101184506500009503052801c000601c1da0800844418a820a4105110030068078a41d0754600c40c041c0d005040c44c90a40c00349110598030b600c10040c0c640d105210095101000300f040c10030151254074950b400a100340381306805e10401c0000640c011001200b0040110390200400001513400344d40300d8014160360008000d10000135600303006490305400090300141d812180c50001044180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 994395854 1250 994394604 994394623
    0x130305010b2704151112070206090f0a0813030c08071502120706090c05040c05070201030b0d0b062b210c020a15051606060f060807020a03031d070f08210318 69
    0xc20b125a16911600f141c031503800207486040c0140b1a010022b1240d1000061010b51010140b00400c0c07400b089940d00400c075801502060700c2c0c24600c100c0003000405200ea0240509466006403603514100851044017004246c82202198021459013018008030070403549a19000440490300400c5810825010b411039800250000d00e801c071001006075101c4003412449200341c1c3d041c40072421003030402c030030600b50a41c054620806900440e0040c9001c0045c20100101d2028a5800110b8581340307202c881c0c0c1041c81510031880e240401d020101e00f4000a901c100a54104644c840031b840d004240501e40d50b00811641009401e13010b0311090151003524150b020b20584401d040104d07141a4015000e54410840c1805042c038011901c5030049440030300c40e4003181e004200710042500c04401a19161290020900e0701d03000c0c030303c0c6501d410700c170501c003070841515015801481e18020514001e18654001005042c10b802c1410041107081169000104171104841d01e0b00e03104011424020880c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 994397104 1250 994395854 994395881
    0x1090b0f15012f2401140d050a0b134d03060a0608070e071d04060b2803021e071707050606030c0108040f0215130305010b270415 57
    0x320310542400c001040c0c0c8021009032843c00000052480b031003103444c828080e80405818501071080207040440e20001924000c0c8111210800c0c503449407110680c0903035802c207004861040d00c1c02403041460190b0310381400603408003c481849243d000d403c050034480f000d0250722548a4502181c2e1810301c1c1d00381204001c3c113450031410020341d004001d100d83d100d0f14095000da15000244641c10300340d8184030f481d46407642e14004d500f0184040d952200b13469629440742e5240c1021480c5207121005d0013210301e030300c1c8200c030410a010000d074600400c0016000308240c01000724104051039000d05000c4411000380706900ea0710546813204031455111024003070800c002c07600d041031280c006805405000240c081e139004001d00401100c4440040ba8041c02320008629131a0041c2801c081403809c0906d8200d1150814001e510045d031004083d038002e85090303469094864032403901c1c2d03040702a03400040002080c503c14040e005043c080c00140b001e041c0559004205180c1c0c00070342c101c012502c005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 994398354 1250 994397104 994397177
    0xc02031f0b0406150c08071a0c090406090606170a180c1701090803190e0d050901090803091809010906020708071109040c050f0409120201090b0f1501 66
    0x284001401071040300c0a841c4102d0078090001000f605103c56901c908040d03940312000c03144036445034083e55000303003022201c00d4a5030001140f080c0e108030b203180c004e4103240340086c0c0c5c13428400100401c3d60340540107001c2d80362926004000d555045540140c0140680c01c08081903551502c1442c024000c5c3e62045d44003c0000d80d840c0c0c1003012048040f03060b03441c10b01c80e012450320039a01080c2251001000200101001c0000c11401c402d105c44101c5510122840442e191911089050406081907021004104007042e0440d096030842140070142902c0c200450926495000049690140d0030b0044100c0320220041a0060429005001c00a820080565881603a840d00040581c80030100b55010741e8000b20b0850f50740783c42c2c00c00c42d000d40d03001002c070308209007400c0400c10810f602940166001d5a940d00c104d0010701070860b86481448280c000150110050500c0c16202100604541d4201c03d40d104004140280341c01404882d40280f8000c02c07144040c003502458029004111900c0744d11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 994399604 1250 994398354 994398403
    0x240c060608030c070807150c0609060c050d2d0b03070e0f010e130c09050c0d11030106020618150c0c2d07050d060b010e060a030504210206070c0203 65
    0x500000510145183d001103030802681c660300760341c481c0c003035015010070203131003140300300d0030314421000002c6c0c960141c0c00004480000d07548520813115007907000004240d02103886000c195003840392680c1c0340011407803c511100a0b02c0010954007007800014000c580d41c00040c50103880411024018102c1c200c1c0c5650380c1c0c14003c0848035000b50034811000400740d00c0c1c00085020348144d8010380020341c000586e0003103509003000c00b8040c0c10010092501e840083c4002a005c41b2240196829130014080c12030f940e50400304004e0a0480081111403401e11080c12486000e200059821781626403a60400881d112030f5440521480307807851107880d030300c6220806032f03003c2480c0c402c144000d040b445203101c05130580034055484000510981e0f40c40710000c046413000c10a41c0d00441420a0145071482c1026001c00c0014881d80015400740c0010355100f04000403c0007880840d045100b200504101c00c400b07080009503144001020034003000103200c00e1784115181000345510394108000f41020750303007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 994400854 1250 994399604 994399619
    0x3060d0c03021327050a0303050403140a090503060f0c1c090f050102191b1704121b1a0a0e150315130204151103040e0103030f18240c0606 61
    0x14407220021413041d01d0311000340005400a29140c3e80350310001500350703901107840550007800300400980a102381d65901c5040708034184d00621400c140d94698084417030400c0127061030048014405283c4a01e100306118408441000f0740b0169032440020341168044a001ca1000c0c002d200c0004140d514407044c820204a8190003500c5907608403550130303003540c415020032560560601c040c3c1c8503c886003440d400200f040014809441104c40d85d8643c40c0c5540e031000e60041c0d000b684820b031955800340401c0a560f6001c40b2903c802841020030b4012800f50403910f04259100d0f0440030414415500208220f6032a189000e030175251a845100e0389900e00803120303d40d124080c10380c2d98454003070028007802c803001c2071007510251a00e04c40340b12150b0680b408250b4180d038150102d40702d107120501c400138882d407860480a002e036109036505520342ca21030002a001080c0100b0b80e4442e085500401e00203450810302180104039250740d031504141c00f00304255076414a400d0060310003414441d0119500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 994402104 1250 994400854 994400861
    0x70c0605120f070e1003060803071b080c100c030201380402130e13050d02030a0f0e01141809040c0305120a0c0b040614090c010e030a020603060d0c030213 68
    0x303070039a03452198507038a032104a4a8031000b11214400f140c0d0107000f42c2214204600c0c0340e40d800303175141000100c181d02e4101071031031a00261400c80b840400320303070b10740d182c60680e0441170700401260000f071004004000005207024090310114007000f41400d042030502d4404d41102c00c03400e003080f1580b459030060842840100c02d800300c6800140d4244103209215007486c0c82207c0308240201d189440c02401d008ec12400b0400c060800101c41601c0154113010450502111f03203000011380042d45e0300c005d42d9601900808442e03d5540a00c060400100410b0740c0122420806041801c41184e50740d2504604400910040c0c0700c1c9070700040d0300c100300010015030a6141040d00e00950880fa40110302644103142c51055415001c000f55141c82c03448000b40c10103c0594100748a0a404580c54180391211030400300c0c101c50784c82955120083d0b030782c2d5658100b006850481c0381036015101100f8160007041403072002425841c000c0125041030000d02451160a4001e036600034035020342d10841001d924040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 994403354 1250 994402104 994402117
    0x81c0c090305060106050a080109200f090114071a0910060f090f02070c060e1c0605040209090706050a0503060d06020f070618030801141801060908061b041505070c0605 74
    0x1d110700c0002081d42805042500c00300c0d0012384c1c680303035968240100b403405800440e04000d5403605441441005551a00181c8814908079030240d8a600381040014104981c900850700c43c15020080500400e0b100d1403000d4407503a40c0d03040d551140d210341c22043c1c50000c114070b0448100307207040d401150f80e0142007215811034108410a11045169103c1c0904900c1001c0c40100646e00c150f2041000d01e0040c1071001039544018909405100420300c40ca00d120301d69201120380c0c650b124204002c610300b0350103058008000d2802421018100702c0c000c1c015225000e04942400030100000701c031a5a440440300343c00303a100c0030a544410903441c4e00149500190b60403141942408000e1101c9030945003409211500350b655002240d1808441c507040c502050b03c0a500224185000320117415641c2e03040d4003c22042d56001c500c02c2c51726241c5e50418038040c10070301c0e074004520540c4031281180b07425103040d640340d400342410750070300510251281d200781c01004250100c90480080c000ea0484040e019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 994404604 1250 994403354 994403363
    0x80c010c080604060b25020603010e16080705031506040302060a0201021902010b180601050903010912110c150f070c06022b0206010303120b090c090102010605100c081c0c0903 77
    0x222074680604002c1642d04500401003001c0b02407061012000c9461203000c100c020346c4884401101c1c0603008600d25074001d8001038900c184001c280002c10a040101000079251842d0480440c141450014160f01c00604540760180700c141088600c0d5542c1000ca50003594001c0c01c90307a44010404020b0b002c1e42040c509e402d08165101d1044202d18018040c40c000c1940c010310048a240d0750b901c20096041e00501910704204052003425990f48003442210000c0740940342450350410140c1d0000d101d45a10a000d20451300a200c2c80181c07030b2a0413002501d8110400c6000703444103850542d96a06000d1010080c0c429903e071036000904540114000807003481201c0c0001c0b840c00084075074840c06251402e0b650040e03100400400200b84581c01100c0175010465003c2060050000095002c99003505c0c45550448001100741d541d41e02441543d00401041c0c1d0f00751401700c90035030003415110780300002030009000040d0030604488880d1400002e40d40d414800c1180050307005004003081000c0c00102c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 994405854 1250 994404604 994404617
    0x60a09081c2003040b1305031f05101404020d0b1f08010605040303020c1e130f1d0303040605060118082d031e040b03130b07080c0f0a0903080c010c 65
    0x360303610505082a20741c2d641080c01545050300d021000d0066522a400d40c80d13803040c2400c004a2a035409020300340454421044203021100243c00c4401296000340010010389441c9100700008244020280e404282c201d80068540700901c43e0359004d4800d24900b264448040e4294102090403844541c00d840041c1e84c8050541c0e80b6244203491500c9a40009809030740b0811480302c29140001d840504040e2880c0d801c00308050050100b5844619403070300700e20040c0c9403042c03c01c00c040c0d103110b26001c000081600c602d04010103400307941c0b04d21001d0800781c02c164a910010f001c07640202d040c0c0031110b5144c02c5d03165542c0d940d101202d8403415201e0900840d80c18040400001e0500c0032070214100d05d840d4091442c051011030180c44804100d0102400820244000111010408007452054811000980c00e00d60b046c5400e526420004040505124400c0305002001c075a10041d00c0500c9261086140e07902d02081e000d48840620394801030010341c000814803100c00c41900005482c039401d03201c50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 994407104 1250 994405854 994405877
    0xf0d17030103031101181b0b04060f0206220312180602030915010302100c051f05070210020a1202090f041d010b120303280f0603150207020f060a09081c 67
    0x95080e80c46c2880c2400b810200c1c4290a40841c142e003600c50091080301c0b042910f0140c0c0c56074010181e8006602c200086507411301051101c070307018401e0a42c00001c0e0441080c02d01000090000703c1031840e2009402c1000740300155541a040b54010811450394042c203184e409a68a00343d000795204841c8029940245106140c1a0350580d00182c1604c0c1d000b012034403816018001181c00c07803560318095815100d54902107680452050017844036000030030000c1035074a40500007a1038505581c2061007001e10401440d10599400350715807004001c4032001580c3c40325690002400b02886100240e0b2061500c0d03035429071142c2103000302160058410083c0800501102002070780041102003820f183c00400001c1c000e0903903100760041c0b2060b00c610081c480c030b07440c903440740440b44240c3d29481e40c0c83e42c400080c010b000340b041e14201d41c1c004039030056103001c0c03880e804104a06212044640660030203d8000c0030240180c5500380a44411412907404000700200e4190203c0004a103401049814611 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 994408354 1250 994407104 994407137
    0x705030c250611190e01020111041e05100e06160b0a1406030f03040905130f050a0b2211030f10061503020301080d0806010215090d08060609030a020f0d1703010303 72
    0x11307030360900c010410030300d0319150404050740c440e040c03201824115503840f1500312000d15250013400c003034070790100000c0303d00c00c032800440742048030380c0c20462007007050580202d0550b40c071000541d02c205094480b103840b210360f11140564042e1512005000d0400d89041101d9102c0079881944005680c004400081e00c518080c543c96048070ba43c2094203400c20042031003108480e4010540180442810f2004a02d050300c3d0081d0340044008110b0741a00321030900c40520124415054115039070000d07012514951648003080c5d0500c0001c020610901c40c3d20003402d0750350601400240105140940748042d006224400c0204401e0041400c6103006003c1204494401e10030359040e0380044000f080441c01d09502500c2000c002028a41184035003070407610100301646c0d81c14050280c40004021400d045040a0314646000780100d0080e0000d00410681e583c3c0001e0607000c0c00e4041d283c000c407000d05000442c00c8801ea5010160418000440b0954440b0b0070b2002141203e020b50b6607000304525805a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 994409604 1250 994408354 994408357
    0x901300819180306050c0d06081c090609051c0605010b0c10060506090d080903010f0c03050f0601210b030601120c0b0909010302060d021e03010f0611060705030c250611 74
    0x140d02d841d681d0720241c18000643d07280e114503000760341012100d0070940b640d05400142c4031550000c0001e0b400009542c5403940415015803010314407410030365226400d003c4014100c14281c45000c2c401c0038030549550343c680e10a0641c0048070380110b800d2200f90384811018403140e101c0c0075a21000d11804074807003141c4800344541e01c26200c00400081ca48400300c000c00150340003c02c1c00740c0b900c0404001d501d807996424030031010401071003640402d054000c00c0b400f904455008000804250500302000982d03a8810998074480d914200030309041d100c80d07000640100700c100006601446241d0001c601c4401a00f51000214031071051214915220701c2c10f0802806004c0700703950440c00c075038010700062034100060030b024004a60018100702d542c40c240b690002045195040342c2d0800001408030000b603180d00c2029052034207042e00400350748102150f4900009004004001011000c28503464810b0221a0342030282c40c240c40300c6502958841500c0303100c02600300d80721464020000c0c0700700920b40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 994410854 1250 994409604 994409627
    0xb0111011a04020703360806130b0c091c0c0803120103081e03070914060715150305070608340c081e03090f0a020901300819 55
    0x41090039a0302003000740b101030b4001150440c14012048802d80c0e014100300d100400018004004444448103c001c61038010305c03a8000088a0300700100b04003000b0100349429035159489445c030595a034611078011628003500c840a13501c400c5007400c2d8241d0310342e41c485060542d8000c894025003180c1d00e5a4181c0d981c441d0840d82c841c00000d000042000c2825a009007051655a0048940b800c00b002441510b030b50044814401058411100340500c50840b0b444d0781450030309441562409180c0d46070300301c1c8554140e03000140c060b03c0750440382d40003420a1458000795804401c4400c80e40d00c41c00c0c080c0295208039601c00c00085084c40c203031000303100d90244102c1070103540065005200013803402c4880858800702034620030410451800000c40d00070032030000c0540c410b05e02d1703200d090a203204da0404550402e10780c4144d1184000c0740244c2c1d685601d07207046403582c01e0941d46802194081d030000321220300d0a2081540010703021001e004076a002400c40071060803c030241c01d034880000380c0714440b081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 994412104 1250 994410854 994410881
    0x21801180b28021b0301050702150903040b0403080304030f02070303141308030307020a0606151e020c0405070809010b011404140102030f0412020918030d05040f150b011101 76
    0x8080400005406000400d4140341d0a40c0b40503048070291040d0315807000c1031000c01c0040e40640440720034804440b1075803100003000c030000c1c4110f003000b0000075030341c001005400320700400100c0411070b4480104101c030014095402015166580e90400040981040b1000e0b00030450f0000c1d1244104c0c8049604802c0c1ca070f00d078131580000320581c2d581800a4020031a440880100c00b01c3c04142c2e40b00030405076110303403036507070003002c101d0020f2a1040558007560f0081002446040004042640001c440504030f600c040d0500960000058202c0c5408241c40e20190444d10341030500c4603c7d41d0200546100381a0000240305c0c0800f0400119144e80c04205004c0882400f03010034401c4101007940c10b201c80005204490800e861710291354890317030069008907400280c90710020110b05000b00d165030712040c5180030210307200c04902050f0316845410100207144e40d6403000182007040b1020706214080d009a0145a0380342d10681a40050028416250100301d003100c50520100c01402600d1b00e40c02030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 994413354 1250 994412104 994412147
    0x905040b030a0c090c110604020904060216060e070f080708211215092a1615061a190c03050d0e0c01031b0e240d150609140d020105040b0706021801 65
    0xb0794407810000e402c083d0f10032550ed9092401c00001c10403e01801c0f4038020303442c001e805040e20301280400d280c8015407140f0381513004481c0420403842d01080d0342d2110881c83d483d00d90610f40c010700707184180c42903801400380c0840ea0810702c0b030144280c6c101128040801d5642c001d65844400d402c401c20344007103402262189280c1503500207010b031342c00074088180e4420900c0d200040c40c1c1d41c6880c4480300c00701141c541c00f0341c1c0740c104026640d01c003540d103001d41e6918100e461800c0409002c19001941c8003040000b40260208800300b00351003401192070f0148010b07020045036180558403034a900c510210303240002d08015201c50400b240d6036058030a01040d807035819031070558805000e5420320040c41340001342c0050400003041070000700100304612006030300007a968480710fa411800c003c1c40c4c0100c005c0003880c40301400140c55503404040074050407039401000c0501840100d80710310941d08041082c18010480c1c80800c102c13a0040c20400d0700300081001200005070044032242d00a000c00c003c1800b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 994414604 1250 994413354 994413361
    0x3161704051c0512040306050a05150303070314090d0f1202010c090302090a061e17070608010603021c0f060801060b071109070e18041a04030905040b030a0c090c1106040209 76
    0x20000c0b10507001600c03a90035150900f0030590340111680040c0d00a503155920b40302086480040c501c50b003907028401e002e044422044490109a91b40110680103003400031078581038584030a0381055a05590005260f1407001d0064941900c042c60740b540122200d408000010380054010300411f4081e5109648400c0c0d02440c0d0740810101b00c0c0f0140c0070540459403414040f440c51101551494a2300c1d004060300000d0380361920000c880c80718002d030703552103400844090206036840140c0c00e04541542c580561038030150114995101000c0482c0703942249003200640c003652984d000342c000c03a000940200002a0b50351602075641c070545030f0042000c02d5a80c800d180782d161031640e0f0b030341024440c0760404d080c1c1490000f240c02ca21242441031004072030241000104803510484842116900d03030703456000d02349030b60003034920300803401103910540c1c40d520b0a030342da600c08211103444ca940100f0805002540c0711012002054005203850001c1c08440b105080c1c100c1c0052001e00a55001d45031002603903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 994415854 1250 994414604 994414639
    0x60f010e0c0a09030506010b030108070e04020f0103020c010e1e010e01201c1a090c18040b13021b0708070b0d09020d050f0c0108100e0105210316170405 67
    0x50216003070b1010f101c900c00d4048040b40c810861079002c0c02c0008500d030b54a504240031540b41a08c1a440107ca451005040000503101c030480f040c1c105100782400360715620581891030162500c0c100ca1803c91040c0300c0c0107484480308800302e500010782d540082014610000c4080c1c26100342c1c24203a21030f8510b003120b10902c1070780c00c00180300c1049502d06245000c90350302188420703611035070590800c4001040c55480030f440e003d40c000e034100c0c2030035038600d260040c440320154561040c0d01203544901c0d9100491034107521400052180748030b007880215a90384002c0d03032001034070000c1110203006100f411408030f19000c000801c4401e560103183c1250806078141d80719406400360b10012600b080401218a0004104011aa040c59424030140c1030800000c000105156030003424011a07500c01201007011103401c4844074150740003541c440350044c82c0d440c01c83d01190b407201d845641d1844001140c411300c008801a50317031054441c00f11640550701d050450507480c041d03030203280d6100000c500c0620405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 994417104 1250 994415854 994415857
    0xc020f0114041a1207170a0207031b051c0201090b0603072304060312050702190b090d0501270b0f0f01050f03010b06040602010b121605120a0f0f05060f010e0c 70
    0x4812030350318a071810942e0508050070380b03800d4680401185401c0c03103680d0341d142d01b901c003113600c044044001c41c01c0c504991030040440523113000d0003c2c0c14410209520500009202282440d80303540d410800101035000300034020280a6000c1e1100f044003800725a4510340801d89604480c00f24103021510f2130001c01c001040e009a11802d5032082c0d45080000c001440c01100410340c400b1621000d0701d481850045c000340d03801d40b406509000110044c14131088034200700307036884003200b0740310246001c186162070b50042203140003480c116010f101030081c80400c0c851401005910450190741c0359141c40c0300501038844140d40d5410100d48040c014051410003211060000348000c00100c3c030342c0c80210200d60541d02a800030300060f51038840300382d40360074140c600444001d200343c010303c1c0c0340c00050159130707400e6400e016451081d12103905c0854500b4041080e41001600845085054280c914004e000d00701c42e03240440d06030140100080106461b6031510f0b040365040e6050071940d0361200c83c00a680d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 994418354 1250 994417104 994417139
    0x120501090e3417060601030b101b080408010501030510050402011b0206090a0e07090b09060901030902010504170307030806030a0b0f18010f2f07022e0c020f011404 72
    0x5000312441c40855102c074610300d0303801450a22030400d18040700024541c203200c0c1c0140901d0515040080320392a40e01d588030010a0342000e1310f41400040c21846c070510881c100050042d007074040c04640810254070641c4518100c031711480880701c4085035140c0000c140c600c1200c0c003a010a446800c0c810108801a000260b110f100800e02031806041200051041d035058111844c00303401101000301c00751708402c461000c1c2c012418500e041c803030b0140018499118404800b410961903080301411079000b503060300c01410359611500b0b840d103001d8802c0c0d6900e4103c510301b5400200b0718004140c150402241c01c03000c041c2c00440d0b050703042d5100c0300050a6000080d0400450344200140c441354100c081c407401640c1c2c1c03403d48000c103207802d5035a00306003011011101307180c0080014066054402201c2c04403645240e068400c1800c0c00d8840d010071144598042d940728541c2c86014081d0040c562042d592071010344200d03000c40c4901d20403401158441c41d040003601c00b04504000c140701410034050b00c20007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 994419604 1250 994418354 994418413
    0x30f123102120f010902010207080c03061603091202060916150305044e05120c0403082d090a09090c05100c06060e0c030106110a0b07120501090e 64
    0x2c00d00403048101c1c0c50f0040c01c080d101031503591106048215030b811b00103500104840401003d03d00c00100000e500e030b100c00f811000c0309a4501040000160080c2c0281c2d00982d00b100481d01716505841020751140d20490313440f4124040d00d1020a80118000412420358401780c503612101d07102c419080c0c0c0204806030050b98000f0301340f165910310981015014030300705003065012407010031451b0380008034000c0d50350315070880000c12444554964000c0035070700304d101124400d803015100c20911014912460700094152140041c50709900180c41c45010810041d0501e110741001da0075040051500aa451455000c0903100080103510510f0300605100360251b0340500c0015076990000380801400310001c1d000c261140c807030800303102d801d10842005007001030100b540da01d04480800150300c014011101407003040c041d00d040c9100c0400c01c80032808d07407154248141d410103800113001c4141c900d034034040d4681028004500c2810500407088094114002840b10018441d00490300d101014040c08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 994420854 1250 994419604 994419619
    0x60c020603130206130302090906090a021018300302030d090228050111011b050c010e0d0207051e06090423040b1510080610090503030f123102 63
    0x240c1d13100c0c0c00828075452003c603400c50b100e2540c8103018410000030060701d2207402110400190880c0841c401c0340c107a0341107604560754204142d081d10f10102e41d0f1132042e68071010f9903002c540701c454818035640348070a058081110074140ca031041c0854900344c00040050b001486043c19610817600101003a81c0b0040c02002c4e0340303480d15011000c2c034505400084070f082c030800c030421855810080c45c0c480141040000c1c040700f4000c110406147c0208185001004000103409814481c20740c06020201d10820a9894905110000941d24146405480d12445481d02c0700d2061a900c00d481c1031049201800040c1800c50034400c01c0014928544400c1070440d0442001000c0007a511080b0b220742d1244509290311300782900c4a442c012900c5454034010740101183c032800a80185000d0b41c00401241d0b4003010202c1080125a4170080364001d980520001c03901040d0b44900001800c1d03100a0b2015151303603903980c5065030398103c03052000100c2400031200120545030303c0c5480b03220b2450002c3d12030f2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 994422104 1250 994420854 994420891
    0x10306030f050d09060503040c03031d0415060807052a0109050a060504150203130b221110020304050d060e15150906030303091b1513030308010e01060c020603 70
    0xa103600d001501007100d41c3c0d04490107920025400005840191180d845d0585c2145080c0e601c01c5468845404090203018600c1e444000c843c500240040320304901030002e1181165a08402141c40500d004203808151600c00180e2180d200300103540302815840300307a002c840c4103210050f80d8540e8115851806540340c032403490102e00d041250102081c81400c001609161500740360200e0003265132221441c90041061045c2e03014640010801c0075005209003000c0d031070700303801e0b10450b0012a010507001e038810780900c410310403100700e0f8151411007600e65154148484004076128402d900912340d000c1b407024034a20100d10300d81c0c040c205070b4144000b03c500148020340020300501d421282c01c0e0a220700c02c4103828080c1411110140c01960a40081d811400e001403015210400e00130400041780e50807040c00d090341c1e212510710603402030100d080c0e540c460300e1061604403600035010680c04034004000000303512145c000154101d801c039a46002c16200c0c40d50070403085501c0500743e000c4800079050503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 994423354 1250 994422104 994422113
    0x15100e04080c0d03020f0a08060d06050106020f28080d0e120c1b030c3c010801060f021e030912010b0f1816122405030d120b01030603 59
    0x14092030080d1250350300e92242c00754031840c2845002c905401c060050001500103103400c019610040d0090601e005a641c0d6040421401d01c010b0320041d045074108000056240c2d00407a411385c080000d1403c0d501409141c0b44030014141c024004803a080d0104014540881c4485024100c0c581340c4800c0491800b0360ba03041c40e8644284070a4401103004009142128035508120110400a0442c0042ca40503030740000241c50301310341340f0801d016460140d5051000b100112071f5203290002090300008040b003a000300303005001080101c42c0480d41040001c240c1d24082d18411222001315030050807079610610b8442d425140d1070107842040e10003881404c03120b03941c001c0c440941c0d8002c1b2000207002c3d07405408004c080c00c02c0e8031003240610000941201422000000c40d5407124884556020b02812094116064501d11000d030300e055140110440a0701241c483c0340d400f40c01d0b8004001130242d00e481c00c26488010801a0740040783d21f540c00b40200b040c0542003020f0040c0e0505001072002d50701e444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 994424460 1106 994423354 994423379
    0x1e080c0a0309021206040201170c07120908061821090609030a020d0f050c01030e1c1b0b040c1707030b041b171e1510 52
    0x1014034000d402600425800759001c0d01c5001034550a4401036140e40040d5000c900040c40c00901d44281c0080c140c0c1d05000b41d400700f01c07081c601400c5560383c6440e00c05002c004004e00c605500d000440440c1484803600c59107121441914003041c2402c80703030030840c01c52503442c165406006442040c850503000d54044100a0b1801507640d42c56500183c5400b81000700254800e190800e0745c03041100c40d40d00b200805201d001181e08004400d0010b4003071b41da21044981540e0b102c1000c41c0c400031000d9044107034142803414044011030329030304ca0340c4160801710005e42d1810307603520601c8108084250800001c020b401500c0e56001c034613040b016103d00d0984406071446101101103014885104139400480015145203010a82d8850124103c1d0381c481902003058050080d031203850702c05025036000c1d0440840c0281004040b4410b00080044001d8025510884a603002050741c090001 = true := by decide +kernel

theorem cover : BRFrame.Cov 994244604 994424460 := by
  have h0 := BRFrame.cov_init 994244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 994244604 ≤ n) (h2 : n < 994424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
