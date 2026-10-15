-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4639
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:03.603562+00:00
-- url     : https://prove2.me/submissions/d3b4738a-c322-4c5e-8d60-25c7d3eb99c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 834172661 ≤ n < 834352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 834173911 1250 834172661 834172673
    0x2422030308010303050306040615020c0a051509010503070c1a0105030d08240d0209040c0e0c03061309081b0d1706061909120f0c050609301c0e010507 66
    0xa04583d00740c03401c61b84a8a406002400070889940404d4020310303101440907045d6008125007034140021140d20001e00d944805100890700000040c0b80b40d1003040012004a41c003400186030400c1b080d1070066031501595440340c11400858994550080190004100dd46030411030001e4000c11450011040d003403040c0c1d01c00840801405500d2402c1c5000c0a440b031585840224003482c90300127007080424201410100c828a940d03000e0040c07400c4841d00055400810581202d000b1038000e403c1c0c0d400100d880940030300804040307000302c545040400184c0300c490002ca40100e00b20700c4c0350015008804240c40041c1000102511492400031000c3c10024141d0313603401034a4503070300203520580300324145000803644e03280541c00162442000701b03204418400301c41040d1140350b00c00e203040c03000c00d0f45a1081007001c4c040c04e092030340d00035003004203e2556a8900680012502000c040000d801d040c66101820134040f940d00480303074400c0e00300b11101d8560007104c80307010503008c1c00c009191a070070391101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 834175161 1250 834173911 834173927
    0x403020609060a09030c08150a1e0e1203040b0f010501050a080714040e0a0b03191e0201021f020703031401050306040f0602190c05070f031203020310051302070209090106120b0624220303 82
    0x199003140e50782070041421302d018033041ca400700042003080d99900e01844c08646d003010075078103003042d520b42c0000428554090011540d052000ba282c44c1129170300e034071084a00e10441103480c05288800e110010b410f0740c3c984000e500035000c1010210703540300034000341440d007840c2c49100c82d14420326018080100740c0320b220768040c0c00725002000b615500b10b07000603440d010050540c0c0840004c0c490050300310150550290039032601c00e80c0d041c8020940c0383c03d01c40200d0f000303002d2183e154018101060005041d000070494031403140f90090304104100d64485900c4080042c0035000c648854490410402c0c1408908042c080312411a51002c4c210f858881c404410011894141613002021901c032404002844005140003058843c03100f55200c90303e00650402002240142a008089884800180641000e6911649842a0460150301c40d0707404001c019084941003480e040441044a08540040c86001100c00100795900e06c242c0c4000140c680300171121350030b6044d40101f8800a6800700070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 834176411 1250 834175161 834175211
    0xa06050f04020f070f1410152105010513030e060a0509190e01030c0905090c01230c1212070e01050909180a1b0503030403020609060a09030c08150a 65
    0x141c031a159000030f80007510030080041c2c0b80101603031030f004c02c1144107044104c034201d144c0207640c50501200168002ea0381306402e90082889007200c140300b40072501100c5854591250f2041c8440c900e140c03030345403c40e42d06441004400161000303690074541c11840b2110f030740c07074143c4201d80b900030024402003031401032812441c41101495941c503008011000b00902a061a8543c42d1003941e49103840c2e014010980304a0880380d092200003400c0f0b03140411900c030004010707140e4011320718580250320f04020500c1c40c03480803445d082c08514083c4108000702d141d0540e01c0200155984066691000c81060041c0000c00300807803541b04c01403590784401503504451041d9200c07805601d607082c1e4401c1020070300003516414450200140709019891b078406540784240041e4040302629482032607200d101710f00010750004002c028203071140c10407400420100e40b291a00310030040e00c940c1c1d03841c7e10701d0300c591000c07159a10050000c0982889a006260040305a200070010300038002c500c54907110071400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 834177661 1250 834176411 834176419
    0x4030c0510090f0608040209090c1809160f06020c150913020403051005061f0e091b07110411181009081509062a0a030603021002150a06050f 62
    0x1c0414291801441d418015000c1c2d0710b480c1409548a0000808696084805a2107074203c032020460102010440c1c0b501a00c0c05818900001504039000415440207041c94420b807007008510b08840300d02030b117054041c0c4604505010701514000d0000e10f44000341d00a0791246030358071581d024202d00c07642141c82d148000d070354204108040c00704800007405a540050034500804129008082c05136005620900c0100c540b0324810f1407401440740d0f484004003a8101240342030b4084000c03481c020264035481032101c82101021404004a81507d40007000b040f120380c0c100224106035460140503080d0784000802071581402c00f03046940c510f0860740700280b0b028200b48040c280c0514810381e0f90401802450b42103c2807030000b680300e0b0500d40d00845000205008100110340c2075040e56144c020860788544443c4001c0c1ca4500040c0fa40d940003a0f02ca905259407244008010b894000e603902a01c3c5654000d0900c0601d242103000c21081c00411030141240740030780c240f0041c0c1c2d54507400603050b14199 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 834178911 1250 834177661 834177679
    0x23090d030e01090602040923060a030b060d02030a05101a061911070617090a0809120c1f03050f090d140d0603080309072102101209031e020304030c05 66
    0x141110300401681d0f8016005074000070f0085640c0d4803c5c3c00c80030480c1c4912000440404c460100d51150321810703210381da440b8221030300801c00700b51100c2d42503420600c000c00c1100000d030301d0303070000b071418034404800c4070030390040c640110b4501c606205008035079030703000c44118218001d640060354500c01d110703200b500320900c4889522014802d03614190110805011140403079210000680640b00f00c1103010300150080c0e00183c441d020110741010b034a03a101c100141030440007010810400384001221000d40b08041800d03000f1782d15a03400420301c09110505981603448072a00809840300103000d5880c6e0301c46c080074440310a0002074041041c0e8018500903600c0810305000d50424800c00b001f0f1200c46003005404400e21521000844c02849000300f00d0b4491561582c03040e100701d03d651900344034121442980b40160a12007a0107102148034a42001803099158040c0111100c181094000400f0940c0510720004082d46450b4101020300056041624554840c12001c0c040d024850050741c8036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 834180161 1250 834178911 834178931
    0x30209012a060501080c030c121b06130b09040b090906010e0a15170d0c0b0c090f0409060f05061801090c1112031012110405040206160623090d03 64
    0x18201140c01c4a0780004203200559480b11400d0340d82d048048058413034011303802c104482d403800c00c0c5074003460003d02015240002041072481c6a003403100b0031046e00002e00b040340c030141c611000404009040601d0240751030300764035070601003155500c43d01c040c05100300b10140043c407180094411304450070070500c210641e4448034540040c0550340c0030a039017050413503000f00e5604803da055044c41c1740b0120448004c01721020080b02c42290042c00940551500008181140350141c004e29403004003510300f084060360080800c085803260a802d2f2100342e07a400350483d01060a0040301c0d00030f142100c1c03100b401e01ca406591120f100c410f1045002c0242d658441e0103116025000070040803809074140c541c20700403407100202c80d070700880f050007610341c0c00600400c0400c201101c50792055080f0703892000c00541d500910005101c05017080e68428001c0c040b8000034210031403c41c030043d1240c0d1001c505040e03078a004802d0704000a10110044014001304100700400286400a000c0c09150201e1114070b2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 834181411 1250 834180161 834180227
    0x305121005030a210528020a0b070804021f02030d0e121201030b0606041d1902031008190317150316051c02220213061e03020901 57
    0x4254001c54240c090300010105120004014030f01280c1e003040e0300516000e811404445e60f00c100e5134140c11840c12401c00e600100b00309180303880552000e0040322450501625a4140c1d46400c68003000040c95100400c011401c000303030508041c86c250a501c00c145610030344043d44901803d0301c01c00b48180d0300c2d000719161220400180c1246e00040b06819910411601c5443c0c0c6040c2c240415292200c03c0d20220b0014100082120216000f41444030396602c5000542e07040b42d58058503102142c8032810712a00c002c0300600c010344c002c0c0c1801201c100000c1c900641c072030a10181c1030400c119410200d00386808242c0080c5200c1c8a950700b048441515600c650583c210314550000c480c0d01071058524030000e8031402c00403034058420849100c0c021034400680402c40d0601014001d40203c140d252905845050182034510002c2c440c1e005420300f100003013403500404055100c203000030083d0300b448c0089912031040c80402801490150b103403d52000000c0c004000018490303e90100e02ea55501000b20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 834182661 1250 834181411 834181441
    0xb090109091a0916080a020a0512010209091015052802030c0607020a0b182509020f0301051008040c14150c1b01050c0709020c120a030c030b060304030512 68
    0x4400105003075070910f40c078015a5920180900391652483d44004252400001510800554010000e105580c20700c4203102621514100188a540d000d10916601d55511100e40c0e00c901d013021b645000882c608030600340c0000341010039500303100b420054464201c844400302d914858444403d5408042207502c202c0c80d62183c0e0f0b00008490044d2020301c00515404907030783e10060302901ea440c0040d04e40e00602003005400307a40510059100291204d031200018009102d080c4050303055505499540d0302c100300f17a07400003640102909000006008078030b80345006001448079840c113900c0c5450640e40341c0500b80d513140100641500304000700f003040e980d0559140c20901c6280d2400380c403000c0d8007040aaa441d147c02d5046030b20241c01d8070b800f042d544a802500d030b03813075940001002043e1404050304020741c0034420f21011030141221011001161a0082400c0d00d01660001380c1c002c90380308020205e03140340324002c0c0700d200c0400c140310101c2c1c0c0c04020743d1000304038200d400c0d8035500d41d840c160509913 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 834183911 1250 834182661 834182693
    0x14130908121e0c0f070312110406030504050105090d050706090c0b0d0507110c06090d0516150807090b03040816051603030e030d0f18092c010b09010909 67
    0x40025410041032501050b403074200c0701c02c42c00030b4442d65210000c402c0e507640a07950707103101d085100b0f001c1000464440c4083c0104851030050004003ca44e90405220340c0c0e10039000407001c26210b100340710170072009214a0b64410403607400781c42d01c0a2040300003131861040f8440581810740b035909001c140880110f10342c005002e614215642c1c1c904425400000d040c0840344a8049070034500203c1034210081048484140000c0285182140d40800c011441c410b0701e03000d0360507100702030310480c082c24080d040401801900400403981c05986900418405004000c0410010f80d07440402054602c5000e43e900580e00c006640e4440f00f54086c1740400310117041000e03040f032254002250107085884940b03400c1e2802565034800c102580d4007450364444401101d1000a140341d811449840d00c50555142d2501a101207082e6180c1c0d1070141e44280e607103d1811041c0126641d0b0640e04d2444442141e1100304a900024420503518900040020300705201e01d411964030342c0756000070080f01144402843c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 834185161 1250 834183911 834183937
    0xe0d030f0c060e0109061e0b130906090501150503070b0a08010e090a1a0a2d05062101270b011a160b0f010e0103080301260f0609010614130908 63
    0x948010f0810138043d01d0100c1f111000c00f0710310360f8101052032150191200085000c0c10061a00da02688514020840d41d103040d546196220003400004800f802050110702205034040202401c0504140c18507065900c0200310b114100306c04a60150007400349411900e51400940003503445040c204d0400701160320040c4a801545240c80a2601c40100e440c02240c1c00344003003240d10307030081c0d82e1107021740181c0c07542000c4040c07040882e028074030a03008541e00060182605201d082000002010005416000442d03a516400c0d1412407038418206144028180c40c403804421600392160384003905c041c05614032a80c03a1201320070202c10310200700d0b0048803c841400c1030010143c2403181001074107460b00d40010040100000c0d24031070441c40b0a040e2030300000301a01d141d01c0d104121b1060101115407412100012240c11040001840300c8036041c582807028200e036191407e205400c6907126040150f00306450b034800c0c0d461f6141c900c0c81218100b60b01d5400558000c207424564503030300401c103c3c0209 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 834186411 1250 834185161 834185171
    0x2060604151e18152c09030a08150907230a02030c06060a080601140d02090a051b0a0903080f0c0303180d0306060c02010509190909030e0d030f0c060e01 67
    0x29004011400c100320764018003c0b5107205079a8040c44159540f2111003103020004103000d20005000c41803240300c1c00004030f03c010031544421840130a0b024220303290406074001040043e242030f003114196a1141900c1c840c410f01d0080030000590010020b801d000c10005080300c40769110b541e0345452003456511600c007640380c4907100e00c020b41e07940c0200640d007040e002d441d0108003e41000151002528841805402030740c0c02d00345c0081c802d0084039040e07070744007048024050160712100340f50b038069074210501241d82c1c03411650b40344410341b60b0b82a6440b103074800c018450320140d001d496002178a900a49040d61021030f05003404160080345600f407039901000041c49a1080c60010403000c00107040d040d241014040a400c1e0115440392007180040b5080200b4040190700c990020f0100e22001040c00200010b188107c10380090b01e03400100b001c540d2040d129042c541c000300010351983c0c04490b142c490031042e0b60001e1010100840c89401e01c00002090010403603070340c0004091001000007000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 834187661 1250 834186411 834186449
    0x3070903021c051204060507031103130b12070c02030613141c090602031213030c0c0e10050d020a0b0c0708010e030417010507023f0403021f0206060415 67
    0x5280e19040b002141c0728840d4400d000c82c620741e0801a58100c4615444a41c100040707074070309450389540c03d44400803a000810040c268030450644217009031000e910455141e5404054124200401800c0a003d0040d040d000000507600001c00070740c0612003034900103014130301e482c0070008200e101c405220540940120b6a00c0d10b144c600c04a1805a800d6480da4903542e07940700166140c0c421030036400000c0345581c00140d422424041c020221922925003400780302025201c40d429140c4942084503c440fa4405014910310002000400703050100e074584001c07100d550002e04012031612500b081d86401052000a01e01c040c09403000030001039000f400395141c0001c81d9503d03548580108020b0455a42084c0000e02e414070455108181a800600c9100e0500030354a10720701e01d180b00525a801140c070310310000154101d0b481d0034021f00501c03542d10b4500310310401803030503444080400098001090280e1096001840d60b030000707000c0c0c0d0005030382c10000c5801009080c03142c00144512001c041240 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 834188911 1250 834187661 834187699
    0x12020c0a060e240a2c011412101a040608010509040609050a05030c060a02190c140d08181908180409080306011e0e0111160f0623030a020307090302 65
    0xc0c4e80380090344c40b140c018003142e40002811440c010304214a800c64a0100c0345940110004100b45414525181c240800c1c4140600608800c80311b03c0d00980314401c1c1000343c01040c00e080c0d948041c01582e124102810541e0040480340b0500c103c0744540d25000104041c42055440303074403607a801000f0742c0c000c80300c0313414410b80d65480f2107440c02c042d11591000a1005071107109881c0040c2e00051000d5040358000d40c110f07040070009100750f409107901d1190345120795041000e40800038a648481010749440d201c03500710310944809a524641040034406051502140100d10140c0e000c08450b845103d140c044902180015200c150000d1a06040f04188100c0d46c0180d803003040e00740d8802103802505000310700d0f040c4480c540300011035100e2400c080e096000301c2c816042c03c4103603811509001e403c2010100384001a034090240c001410f103050100315031012445d80d00d282690000402d5061204481141d803000030304143d061039003c00800d401901c0b400c42c2400031500103004441c0103d50207811 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 834190161 1250 834188911 834188917
    0x3120f020f030403090f0b07060902040f0e0a03081b0306011d0d03080103110a03050304210204060f0303021216060902120a061b14030a0c1701030602040312020c0a060e24 75
    0x350003040046000080c0c0ca90a80322100a4494087c3c4545c2441060394412014103c03100701213901c641c130341081c0820300c90b140c429503105a40810040c240c203200c500700900b0318480500034003901c81a6031006100031094200300c03a00f01d0000c0c0f03000d10444401d0480c81c200d4100300c5024603440541c203131560062590203019907045c4c82c0a840307902c071840400340400841c0c0c441484001c24640003070208000710341250821090303402c281c2e207440d010302c607032355001408940c8640c01001030a84a12414828140d040200e40254481c50740c0c4a45040480450100c01606a00009100c5a10b0b000b01c0c4c81151922520f18a80d80107007000c031042c0349094500b050240503d040c0c440c50303a0607417841060941e44030315150940024000355140c40c41d00c80c0759490780a0265484d984041c0074050201c9840e80c64071502e454000c50103030100580765415481c00260005000540d0400c544c00002c402820790358180062045070b0a41c00c0c0b1410348200000441c040700444141c4044100e078000328000c1e5041a4001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 834191411 1250 834190161 834190163
    0x703080910050a0b0a1d0a0b040f0f090b0f25030e031b281e0807051b0109050906240a09090b040c05041205121902010c021903120f020f0304 62
    0x40c58aa46ca4250700c292001401c50301c8810300c03500c1c801168100f10316600c13001081c000500045134640c0311903042c0b026148401d06070382071143c0e207001c040300b44540f6461a582288400110072940d007001d031204c0340310010b0040c1070b040203081a5255841c540c02030707100c4000400e5010640703446280b10001420b10404007050320040780120043d098032614820390b1b1880000b5007034048035414a403500c03900401400000c2e00000840207201c0c0d9000301d0519009051010b10620081c00082c058822201580b0100340c920350501002103024001c550300c406056501c602c0c01c0e203c0c000004800302d00c114080040400c46d210704100019080c403415880205801920340c0341e0402e0200010340003e00003251090809100081c80610091080342041d00030b041d02540a10111440208840841e030b00070762007501d075108028960840d42c00c1d41a02800391062140c01800038240f2415030b54035401c100201f085d0011304010800030f12482d102d01e25801101100e030144070442d201c02c0c0042c45511a580186e070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 834192661 1250 834191411 834191419
    0x6030703242d02030c0d02090f0619090b0a0c06020a030b0907120501140603160915030501080609010608061f08160305060f060123070209150103060b0903030703080910050a0b 77
    0x140040ea80450300131240203207950700340240f415000160240003500100125030380320308801c2d072882003603480702d01030310800c030080389401c800101c03000000d801850b0070340c400219080140a0381840741d800200c0788a60750b4000d0405680ca20054400301c00800b5020000340c0c1c0500f0b0380d818822100d0380310f0480c060070914017400b00708598a4603881540482c10501d090303030000040002400022809108040f40c00c12400c080810545591903074040646031038601d80041e545900400909804200c80d50b04a4400340003001000e0415001c2602d80c400140b0100c9140c01284403403403002c00712008030340142059002e5a240300003401400513101d006100c281c906106500200d008959400103460140005859032401c0c070071079103004200004d40414001464100340095409a105d441c0424070600c104441404089004000581142c1305074001900c07203d4180610b0400c0c0c2c17000800c0b11003007038040c2010105680d50040d200c0ca0003c444081b2004141024207000358080e00d504058140d0b40215 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 834193911 1250 834192661 834192731
    0x160513050403030f0e0601210f1b17030711040504020a05011107080106090903030b1e010c060e0f07030c0b07110909010618060501140f030a0c0e030a14010f050603070324 75
    0x3106038060800321101c0038040c030527485240000542401041000e00b5602c0440f5000c0e140e445981d4010700161064015031504005089000c0001003140003481c070310129130810a0b41081d401145114450703000b4281800b17400b000d29001c50008000c0a8000c0103140d00a103c641c0c2c0320540600500f0b000b1a003100806c0c01c10071030403054034140005100780f0107104201c910501007800115903a0b042c40b1000e0344c6140c0d84101d10400100c052003600760b070703001400040440c076296107045c1c44661420381c007822920000748030b03182c0099942c9801d00128032048600c000c0036203460741c0300c5c0d00408040e40a0201364400c10f1040507455441e4010a049620980303a40c0080710041c0d03c0b104051250417446d03a100a81000010b0312b60040342e1048103804910700c1c211441100d401e0104e842d100321406c080d202e08030401c1c580006d4080c240680200c0e07100b5803a05202c0350a2038000f1982c0c802c46400001e20b08038080802001030314107904903074401d52141e0020701c50010081b0b00070f0703822401d044000340c10800309 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 834195161 1250 834193911 834193949
    0x16080708090118050c0f041b05090418050a0312110f0705190f0606090603083a0f0e0309150d180b060301360f02040e01020c160513050403030f0e0601 66
    0x6200c3c560303041c0c234656010a000e00180c4c00407602903001852940d4132550311212035440201005001c50207a1044004201800080c01e0140000000000310011981040646815501302c00161412500480070290f150b115528102c1e080103200c0314070b50300022a00c0e0103e07043c803a040c85441c83d550700401c0c0c01c0000d141c4138a411010355803103020140800e02c04200b500e15441c8c440304154111409480740c3c8072a0550046d901324008070306040f0148080d00c401d80410b2013005441a8050291108019803400c00300b0b5012540000c50b40c0180c0c03103103507030100b09941c40c05050b03008a011074501d103080313007c40900780c0707800e0280c401c0039035043c0d001e0b6281c80900c0700640c4080c0d03021b9150080c0344243c2c080c1d920841c0f1801d88034800b010001c83c0c4541d00001107100603151401003d20245500d40003584944c08582d890346408411a03d00191680409082142d030b101d0041c00141502440404140d0341d507113003019005411002c45203c080342c60201d60003415280410f002d07060317840500030f1241981030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 834196411 1250 834195161 834195169
    0x10615051e030c19031d010902030d05070c182a09050402090301020c12030f1b0a03180807060606020d090e010e060d1e020916080708090118050c0f 65
    0x80c00c061040e10030340d900c0203200c64403204000b46a104440c00010f0f4a0620005251411400b04820a40101c0d803140410344080c0090f819410791001d00c00d00030400c480303040c5c0010b070340c0daaa50240f000c01d1240025402082c400c0c10807000b005010810304d04005041101c1d505001050a01e20740f06101110516001d140c0d10004090580c5601660f00c8156031424482004000c0d809508030b29403544d400c00440000720b50034020141a801c2812501d51031b880c100e4841d0008640042a00945010a803010140c200e03a107002d8800d4003491340b400090742140d903c02c400c10a0030196001e441d40300046022020410260000303415984141e0030f1710081d501c010000d03619044640180d012007180e5000512100c0202072410760302c294000c001441603015602c4181d00303440756202151a620550340d1080940c141559082d80204c4044105243c8000c0340c600201000c0001d02a4002c000c4402c010a42d4802d0941010346c5c100400b01100c000c0785a82e0ec0c180f9070710720b20000e41a0180e29400f10403031081c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 834197661 1250 834196411 834196417
    0xc0f0503030d0f06210b0a020a0206072f03071b06020a20040203010f0801061a04030623070207081212061504080a110102010e0c011e030603080c01061505 68
    0x4040d004600344000c03040312a02509001400b002c07071a03a02c15000641503d80c0710410310792507100711489202d6074142000d101d04003008203455559801040100500d5a0000340c1c0b9900c03550610701030b0005e00380314120601220780103000030080c1141003441031028a0110080c40400e114040c1c0344441d800761111020120054461080580c0001c1000d1012503100d030f011002d1191003041c030548446c10080000d089070801c0e00610030b41c40c6480d10511400b40300b440303124003800c50b00c417039422142d00280b00d00d9064403540c000281581d4450860b40c50720410a40368294203403444d180c070112032805010096449029110780d50700e511410300c107100100c00140455100091100e0700c10389542e80c0000303000540c90040c4100030040c1e8100310001d45070b40e051091000c07051003420482c10704000b6900090a440341591400c000f0b4020800d00b40d107aa070050381240f00c101f40742141c0885070040a04c150010711141d403011381414400900040413803010b501813016150507c1016407080540130044139140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 834198911 1250 834197661 834197669
    0x30109061b020604050c040207080d050702010204051201021c0b1c0803150108010308030723120115170106120b03070f0e10060f08060a03060e10060b0a05070803060f1203070c0f 78
    0x5000110802c010303040070f030000c00d41c003801034000382c0ca0103e140d004402114cc04444510050354003040507c09440c00034120342e400b8a202c4001c2d03041c000060180c00418901600d1071829503a101d00446098803100440030818030b858400c00c0c45600a400c1038101580211510260000d14800d40c05d4036600903490300c1c1c140c94200c01d0090031591007a40035100203c5c00341c100701522440d07072488111300e0310303400040098108bc0021500c45500d03014070140f800740320907805000d008580e1052044142444105811186c03181f6142c200c000c81e100800c3e00405280c10710766098001c800d00131810010400c0c641007200c03030400010070382d60b8452181d20162445d5004250002c0e900c0c070010650300340700c0d5180c80d412a6004040c01c540944c1c1e0b40da104200d03940c642c0e12529a422013140d20b04903498510441e4001c0c03550710200b0b49000301c1010b0080c020b101c0c416006101d804013201107001c48c1c5442c580d041d01d420000d4030422400c1001c4a030307981d407038110750404c88410f00c0300180462100d014517100300c115 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 834200161 1250 834198911 834198913
    0xf090c0804080a09080f15180c040b01090b0f0c07081f0c140c060907060905010c060216050f060109110a0e0121061e050306040f0b090a02030109061b02060405 70
    0x2a031516902d00c6256403000360b5034000c0103550000810300d0f0500b48580c82d100002e440c02081300404132680300e210910001d0160f0308581d210311140c0200f0300042206a40264212400510b82041c500140e41248080d009200d4000d00850001c428442c408020705c0c44619100844501594410015030f8444220321601400001d440d10a0000342c500e4102c00300020700790a0503038849070380d0703000300341d250f0001140e4582940c01501484142a406e016001c00b030002803400034081c0b428400084c2c0074040d04840249295400200090313002d00220b004038160780c1c00406c1d2807400401c0380c8066900d210078010884103a03e800031403c646100c0b40202e62518ad01900d4500e4036804807001500c0c0301586010901d10804500109144a44280306150141440400544040841d0351218a00340101e4201e14020791000d030620010541a03c030500c079a41e4001d5400301242d070f0b00c022107030030603592850081d01076003814881ca00304007158002881c036280c8040d440d40610700600080783d89a8003502d0207461 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 834201411 1250 834200161 834200177
    0x10b040506061e040302030102030703050a0b01080c0a1409060a08072a06020a020a1406190522020d120507030e09061e012607080106110d0c030c0b07090f090c 70
    0x711801543c0c0c44014149041500f414030f641c0c0d801203801d9034003c030740407400203a98000700304a1400034880d48040050a180c0340146191880011b101446034030400340c14410b04030598003e0036034210499581010140440741c17115160f50000c0c00e6418103441003004140c0c022080c00391442c81c3d45458852908a250044900c1040c2d26108001d5002046400850141c4003030400411221305a94038854901703030041c440d510701062262100d200d100803c1c41040d05080500c554101c41d0580c002000450381984c4070506075a00c0090140d0044540c02001d030030519503521301c02a0440050314543c0d001c0d03100c5414180281040200e501c0003103c10a62068984c85590451945c0c4403000c0ca00b824181082c94a903448071101e8030f83d08102c4500d41000605910400c1482540030243c0c81c010049410800c2c2000c20300310100e900c502c01c050030b4004000c3c46501460601d4410f007030f180001604545011170504103000c00030065021406260b0014400c0b6200144921281c452040004030316aa070401c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 834202661 1250 834201411 834201427
    0x501092a031113090b070e012f0304030b0901060f050604030b072003040801020702030c0102010e0a0809010519020102031b13030b1306050c030f09211c0518010b04050606 75
    0x100c03030407140d80e065401820100c40c0c40d030b207a2801d12403003031524003e11558045e4500391800401c4032081118217410070444540800c503c0988004c8101400c2c0c0c55a1201c81a1000100061941c0100d1344040c20b0a500314003800a04401903201e58191245010381c100c002c4e441e04107020b841e00c01e6102c010803040400c0005103400d031164910000b80d001e04c0401c90303405600f107210280f0315042500020b41030303540040c1c50000c601e82041020100607083c0000c0c428240c1d881805a11b5440a0740c020700307540030029220400e40e00c0391084940c08245003008078005640444009d0007074008403900c070313280250140c6009080800500f99000c04010511803107000e800c6a4a2521541020b00100121000c190454002031490300625203c0c0c03100d52049a01ca00d01145502c400500103030419201e60010701402c1080b21a101180c4444042138074015610175282036101608001e003405820707624076180a004403440140360b45142c0b01e10700c4009015010041c01007004130348081e40c065034840c0f81001140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 834203911 1250 834202661 834202673
    0x10506181207060e0102150c0720090a0c020d020a080910180b120c0a050406050307050c070b0309070f05091303110a11130c1d0411070501092a03 64
    0x8114580038000c074201507201a0311030b19001d030760b80100e808244c10700b680c2c11907541e041000500786072074014540d0b442d090441040880d8850351030301408110b000d15030700040c41006035482c860b00c0c00240c000e00440c030707016180c00f0042680000b0341c40140036004a081c85148000303403003491a900440c5240c60000380c00104510440205222800d1080b002440c150000b8181301c0031005003805131056a44a0840310804c41e030880081ca410440401401071144495000050b141550345034200282c0c0c1c1c4c0c880190a5865024602e034031101031082007400704000c40110055801403080c0c00498504175190420560039021034016640c011851000080ca04148812445422030090500040110b0703d0900719091415508064840240700d0b9500356a5041a5096440d120310400d0100040c0e028030078014030301c1e965030410380180c17421941007480c0d40d038030f560008443c100451041503480c00d0a140c4140a040400c0d025140300c0d000c00710701c0d0814045922701c0e07581300041800c16040241182e0341c0ca = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 834205161 1250 834203911 834203947
    0x30a14011508150a05030105010e10060203120c13090207030906020111071115040312020705011b0b041407080a061b110a15060504020d020c060c0a09090504050a05060c07060b0306010506 82
    0x30703131241d400310000405031001e2065502810b40012904000d1405011164541c500340d400501194002c0000aa102108241507038220035010b07100c03951822550b964641c060034030b4000d00d41c540d2001071003100f0181c10506c035030f003111041e40003802042d20303060700d656960040c920050940414109905d110b40790682e0405201d440f410b2030341e400c05443c3e031244a011030000c01d01001503482803009000c02e680221341126090701281c82c2c840485c0d810703640c0e00c00401c0f000d800140340c00780568038032482040c00d01929020740340800440f00480a2406c1083c0a8000c0d550007a50f1822602c0040412501c01da0420401c0d0f1490002050040103d650b40304249200c03200701e00d07280d551610b010886903101c0c0014581040146030240c0c43c0c0c00c46500590800340d004e00360075955602009203924980c0c01107400c030100e40400ca40098a59a24100360f07003010000c10300203106010f00003c000c2d141e007007640500310b801e015203800c214540310f041c1415034a84080c00785580c011b4080c030140d42e42036000d4642c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 834206411 1250 834205161 834205201
    0xf0f070b3601091b030c05042a020a0b100e0a060503060606070606050a060f02100c0207051210020a2a20011b2001050f09040e070b030a14011508 64
    0x183c098041d40355466501240b50090500a0002c0000c0050010f81c14002000d00002c8604200d42044c114a070705c124121400443c0c60188918480c0c01594000c0c0000703504150012a061003516040003640d01220f4170380908800f140c0001c0220f40940100d1003034005860000e80103182a40b250400c0040503003110004541403a240d00010840c3c0c0c80b00304400340106102e0301c58200092203c0d402034108100503610350000391030075400c06001c540c0040c050081f1841590040b1040718003003291404e00d104000c0c11a5802d00004c2c0b4805415070017507881030040460860710400800c64000003003400910940503040f6015910f20301800021ba425110100c00141403902016158055418928101d400c041c0c070000c0191000d100100c0b042c0d500c060801e002403801c14a00248914012800d005c0c0200103401250b49042c00b00c03858004000002c041c001c0c6500d03940d00d924003400d00c0e502508d10521312244565050b000081da0302000220848000242e0311a901c05540700452a502800c14602e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 834207661 1250 834206411 834206413
    0x7020d1403070b01030b0c09030c0108090f060c0a1e09140d150902010207050d0b0a0c020120070c150c1103010b04020d06030c0506210c0f0f070b36 65
    0x24155080e94410030041c00200d218141624180d032450070b05c844140703030082c0f400a4a000030410106559800301309892041000d0900c0802516150242c61800080c208040d01c14030402007480417041c20b100240c095103000d591b555100003081882c4401c1d076400b454100c0007148468a041c007810031034803041e2110000c090540b5103150f915407511001c0c1344200c400703959901e6684800d0000c0d9607046c0450717000781405481074a110032081d91003552030003004180e000e40303580d24104180c10a02c02c1d001585c00d500c281d501e03620403000e0703000281c40c1640661421070302c40494013400174401940703003991088a08a82c0350b0044544040c2c4034a4400188106200e605550750100300c0c406d5030b51407010b08148868034000240c81c3d030943c0b820b038400c4001d54200c68400c0b4070a00c21040c100e09144082003140714030304460801604c0b040d04150003409a82403d101c90308c400b1541c0840c442690010301803890248524010036162070394808034440d140aa0b0b407100c01001160905a46400c0c10080c8140900744 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 834208911 1250 834207661 834207683
    0x6091206110d0b04050a060602030f13031403030a060f050603010b0d0e0d110c040b1f030b0a380d0c02070f0b0417030306030709090201051e1c0b030307020d 69
    0x8400815194000b02c0012030807680c948840101c0d04040c4126a0301801d0130f4001c0110509201c00a9528010042040b80c0783c040040d041c1c80c0d00020380034402c02141d1141498240241405c3c034103442307800440700320064619005c000200480214008402c0b604003402803132550f428000301d8080c40d88003002c10300c41035464115400c25441c040080d85400f50381e558807929050511001d407400d10069a034400d102d6820440f01c1031140e61001d100050220350074030300c050301e2080190141c0c00b400005416a03444031441100083c00a8403090902e401c0084069801101c4203c05260305d1404147e40c0841c0121001c1c0301c458880c0b4040d41c004186000d0500445121541d40d204e00030850070650800c44660301c0c0483c04110065144860000d041410320241d4110710b414004603656292900c1408402030b110303c0c10704c0559010348101c4518010324030007401e90b45c256050350510f5600a03400d0301c1002000003141c420820451180003550680103024606d07002160302044010010720100341c4e41002e0074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 834210161 1250 834208911 834208931
    0x40503212703280e03060c0a08041502040618080d0207032a12060e03030123130207030c02120c09150102070810051f03050618030c030a2706091206 65
    0x1124205050744511649034620f0329075007008040420500d4258060f0b0700034804e110300c07600e0345c4041d6221080c4920300100c56659070b00b01001007034241c600343c0720420310001e00442c040394480c65090480000780c90642109544514450703481d03041044484c010780007841e082c000640d01c0c004989a0101d0b0403087c80a000482e01745503201407299204210985064250108000c1c041c0282400c04031004060b6085600d0300001008080810a10950b9414074030314805d12540c0c3c2008070450b44c140484115250049441c02805c2d81079080740c280c1c0b0a0000700d1050302c0398031000074044111070002d080c540244c1c0f140c5111503100c2810780a40c606501031018007003854101008011a000f5170103801041508084141c0d00c004042e150040c1f08903034180400f44041140019817a401480f06680303c89035215030250203003113016041c040300e00c80c0000180c03c1141d540c4203402960b0390078001030f03c01d42102c060008aa80b4a2107100b5a00400c00306042000910110000700260f6400b4140204052442e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 834211411 1250 834210161 834210187
    0x31b20011d0307150213060f050409050406290f040b0420041a030c04120204060f0f030203010506040209010e012001020a1e0f270806040503212703 65
    0x1285490084079403000c10b5440038800f81189110344d8001d41041145004030100151100c0c0780300707015240038001443c8105812600c51400c40c3c0c000d00b40301c2d40822050402d85880c00152100d990385150180c0d120000854040803005d10f0307802403100801d08031441c851902880050120880543d92159507880307c40c03900d2060400140e40d01c4020030001d6501d9060804c2c100c4200801851620916414410843c0181125046800340c515140d016240d5183d1440000d0285c50250072805642c210110006900e9000290301d000ba2482100288101d075104400c0c0022030040c1030001d400207507107405d5040036501401880040541e0310f030006070741c09108030b0024203907401060348500260540350501801024140c0844200d0b259141c114401004404000c0c80403d44c0004201d800201803400303a815030250700480300400701141540c10074505400d095403241c0061300c000811408200480800e4607115600c50b10520000202c041d03069800f03001d403d550005030011080074032040058609201c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 834212661 1250 834211411 834211451
    0x70905070e09070e030327031b0102070e22030207031217010608070903080a09091409070f08100c0e1c12050c06060405220503030601031b2001 63
    0x55620744a0a0900c207100b800314a590090503002000200702c00315182e41c1e804412038243d01c0400d11000f04d030680a000c0a240752144004c5241c0c036118041141007083c1000203a0740052000340c0a42d58140e0351a52101d01500e421602008034401c10000300821500200408103414020b20444000c0350300d0b40c2d00c004034410302d001d007640880c45c5416550f01d0088840c03651405485075203080e104901307008101815510760360200800111010480c0051340c1d20a82d18000108402075040c046040000c01c0280e0000d030640e003901c06030158040110b0800c4143c071b4044110707681e0b500207004d40000d1b0b1340c1107401441460042c008003c145980107096940d161540f1082c0da41c482103039540310060786032044040020200d00001c1c42010300c4010003205000c00d900358031034000d031070200d941d41d2040c0308010300803040a582010440c2121032242808000805544602d50a8801b040003900c2c640d40c042c4803c411030194030002d40300c1e056219104498410b1a95640c48000011a100104403241d041c400303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 834213911 1250 834212661 834212671
    0x71b1508090106121e02010320071b050a0e15120c03010f11040e0414010e03030a0b0a0f03030302160b0702010f1d0a02060318190218010e1305070905 66
    0x5030152051180091007032080d40014072088a240d82103035a030740d40309180a800003000003e000d81c01181c1c94190b902030b030401c2d4100655160150b8440c0d0320820b071400340da0000441a1440c3c00c003002c43c280401c088400e8502175a50003441110b40310b1810301500c050070703801030108900400d811500002916490006541c03800c1920141001101500c01c1c1401c40d00c01d034125001e11410301080381c0355000504202c5007910301250500c1c55561721410002c24104100d03120854070342c80c0052150b400c450110203580980c0700d0f041c0130f1200005a804020002009004039540c4507501201080020b000f98018040c10b0202904280040a1a01d40c0d42d00610102c0b084001b5035191100840c00110710b100c3e840441c800000c08444040141550590b00c4000c0c03003000780aa1000004164a629851469004090b0b9082200c0712084294941031440003180802c038001c025180110b4100401050b205041e101000702d1140140c0c0c84401c00325a0f0360054009581c1ca000d1400007194040d124080e9500c14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 834215161 1250 834213911 834213917
    0x1201080c0f220f09110102010b011d0a03140105010f4e110f0607110103050c0c06011203120507170a090804080d0809030c030405211e010606090b071b15 67
    0x2002c242d083c850084c1d52170700080b904592510b803407807099030b03049258a441040041c2003001c68032064404a02c14141d141c002402c40703c58442c140643d00b4054104138141e45148005041856650300d841d44041c0300c0703100c1c440b030b40452041000c980200d80c1c004034103800b02840446180d00b0402031404c0e00d02120031010340706400c60301c2181341036042c8035101103080801a5042071400c1d580e034403034280d02034411038924100750303c03640418001010b0005a40c101e240301010740d8400e594615000d0303840c00c050413003140882c1c0d0800c83c0071900b000b00e2050a02c140b40c01d0702c1d4030910943c40e030040c4a65000040200390903d6039032811002080201000d40b000d4912500207110154000300c0190000100410f1440d542d4410058100e01c0b040202c281c0e07040321002d0ba4204818450343c1c11141c0c072060078228a09e050310070710603024034900c0051141e60154507140020004161203030340880340c0300c14900400002e22010401c40700014149064a9081e42d07522101c807a4803520b0f0383c3c1c0ca9403040300040100d800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 834216411 1250 834215161 834215171
    0x30305090d020706120b06220e07170a05040201020f03040f180207020303041418090a060f05090c0d060204090c200304030312090c0504050c1201080c0f220f 69
    0x3035410803100358036144500007448101d281c90001840c80c100030260203131540c1c07114841c20b21501c90000340c5040116202e41c507044000300d5001403400007100c2c4038021131001c181c0017251025000d007000e100810504460701416039070700310100c1d0241901a02c124118801c0000a9481c40700c00d0000d0300281460600345a291482d00e05c0d04440d8600b07100d400d500040c81004040f0060350000100c500316030005a402070300000c40c100140300b51046030742e0b0301e01c003100b90700c1008203030500440d0340c0e05818400c0f2020849044501216001c59008031001e014540c000c1c0a0300c1d800340ba0035080c0ea0b000a220f09800340c6401c0c1c45142e004140d60301c1000d00000300e60000d081c0d64040382c0d00030100002d581224000c1d405e241c5113486c002c018066450400c80407681d10149507003072154541100c00a000702030000d02c420f00b0075604601d070561181c040c1c0341c0050402000030542c1100401c05103d0702400038010500041503004020341203408011142008000c0340441403980818003030507401d403001c0840003c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 834217661 1250 834216411 834216421
    0xa0e0618030708060105220b0d03031b0e0f131512031b0b15040f060e0109060b0f070b132411120109240308030a0b0a140f0d0807030305 60
    0x45402d0300c542050762107400040041c08182c658281c2070b0304200d40a00395008050b03800c00d160008000c2e0620b8103400c00a4800120140764268004106084582002c401140035040b422202c0c000c1c0c1f00001540100c9194018a6500e08030800c00445040010001144148118400480260340c0d10820442a00903450740505800c024030303d41c114031b0310b0490405517980f07998501d01d9460041c09401c40085100350704001b61281c4d4052406070041c41d40401000f520f466000c0d40500c824440e04141d1402d012020030407005200a5540f42c44055100e1350a1507801d607541001040000d00030003110011441010101d00380b29000c2d801c1e0007445040890807496261007000b59040744000c0c5441102c00c005010078000e01003852411203031220b000003100b5401c0704200038041540d605c140c44120041902005002028000314040c10303d051007040031501000500c60905220b02c180c03100307882549482555414840902d076aa404010302004510115a40c2e10050f80c0094000341d00113075650302001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 834218911 1250 834217661 834217663
    0x5060c0d170c03070810050d051501120f060b0d050607030c080604020301031e05012c071d0109050c04090f020c07051f03020d021204120905090c0f0a0e061803 70
    0x10400301d01c02900780c0700500d0200341a080b1880301074015020040a100024075800580136070703401404000307200740ca00e074007582041540c9800c100002104208208000a8000c3e00c1400c21074425500c800b4560701c041941d00c0300340090581e88461900301c3c800120300000203c05000544c450711132610009041174400200521126006088500981c410070060011501010107035a0103588103520100c400d103180380690140001c64810f41c03221640030a4150410b12441148003000c50010484402c19504e54202c4200e8100701320000ea12008240144001031076034000641c032501d000c02041c074042d170300d0007a541240c001014610a517640451407070008039080c80301d0f03402054225046030741380000750300300c02c8849441a00c070024954001105140100c264054070321281e881d2080c03034064034203810100c14401e0410700c0f80002402d940c00c04941494180086406039052845181c2407400600d0312003000d034410024103051000304a603c03030701030b0744076402004101d007808000e031032019009040c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 834220161 1250 834218911 834218927
    0x1a030c040b071b12080d0209011106070e090a06061b061104180b0f010e100c0605070915031119021908130501020f030316180b071a1b0c0705060c0d 65
    0x100d140083c5180120b40480c903205c09842100914030001a074980c075032801650002400003845149000380300c01c0058a6401c1405201c00b401e06555120a507a41d90184400f00d41c0c0b2801110041070703440d4804030b460a00900350000c41e900c82c01c00099000700307100c4011103641240d0320480c041c00304001e13155829001c81c0200030240c4029201001c00e5444800080e00c03400980d4015401204401c00070240c1e00e20441c005e03029280c121408000c0e50401800080490a207402407036403070801d1191140d2510311900c6000c1c80c080580510604003100d00440c44510030800300c01ea0114460854804003070060100d41c1060a4410030705603955003142c9107224401c00e000d62140341507410410030030402c5d2101108076540500d00321103403203184030115005c0c0d6801220700328100100340744000c04250401030400070002c050146c00740c90710002c01c0c043d0072f8013003440884052101034a44078800d503403c4030350406040c6400301002a030f080c03103459102003841508180c1c6941c02603403200b034240780c40c0ca4004001d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 834221411 1250 834220161 834220169
    0x618130506190b0f1005160602030432070317040e070e03010c0f08150315040305120a1e2715060f060c082a1b06041a030c040b071b 58
    0x35100d500c0c1d00000100141401c0b80410140034000450110004187c02d0100c08698045811502c80c103007418461a00d070880c60210440385080303c07034403800c0c0841c6001003482e544440300615000741541d5038644414030303140c0038202c2000d060002003400081c1d00d03000c2d4851000c2c0e603194130080084408250a49040ba002c90080c4941c420b0f418080680c800038039940035030620040a841400709000c2440d16001d00c0b0600c603039003003550030703c401c06038410001d1580c1c60b40400f1011103919009016011929000480400540141040243c0c1c04c09508094600300006402c62030392810544580c819801c010006ca44119000c0b10300c2c603a0881e540706401c00b600d00c024840008904200000e07000010003540035005107000308500510403040c40b10144614200310300c1540e01620394030040e0340e40d40050448003202030502e4001d10b160030840140e800f101d408006403e40c4400a0707541e01e8032030b8005010510003400411012841c290740800074501180302c0c812410803107018003210350800ea01500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 834222661 1250 834221411 834221419
    0x3020a020a061d151608041a120604050709050a1401080a05060901210606060c060e010e03090d0501090f0309060809060114090c1201030503040f0e0618130506190b 72
    0x200326a61948440c03600000d40c8404d0750011500111208070304e007a40903c604d0340c006074120300c064908100304140a0000c894483c00510f100080c3d0400342d8200d80030381c00f60701d40f21001d80c2001443d9840c2680009401042c4e60500344402521800404c2c4104581d411103002506140030031061560300403011a0700141c1d6100411036801c0c29030004600c0e44045c850121b0b0801c0e5040c00c554040c02c0700202140c80c513446035003001340999a00c8054213060a00c0f801382c41c014a49012020901c1040c0100351810b841200a54580140303a4100015030036002c20558a943d0390b01c548100081c0032422802016000742c84d140b0456151800c01012601c00a19101c21a0802c900400604803007440380b10b0500021641c8030502e5584001011480c0103160200c0c049113440c50001091003404001001584d10f103404110500c2d0b111041d11040c06400d0b6045a00810340c80c400d940200e025a00c000e030045404202c2d110b101101c1c2c0c4403107290400030b507250064000d00400d130040714041c0f4481c11422a809070303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 834223911 1250 834222661 834222677
    0xc21020306030c0d020a170105060f030316030311041211091308040312030b0402210106140301090c030b090a050a060e071d040f0204120506281a04060303020a020a06 73
    0x1c0109490300c820403070309405003500f00300c00c60865640c0030215020f0b21914042d6440d80d0010f0007858043c01c000e944641c080c0c0300c0042c0000e014240071040310308418800190521614003030f5801c8008148402c4683c80e1198240408101010402500c061041c002c181a4284031016400c008103140c024001032a049060402140010750003030a99040344d8114a0b810520254030b88150050504d50000725802880041d00c100788003003a6101c00803603011490110741c01da07280c04090f603419070030700000c1d02540d20500040001e00c146800015001d100e034540412040c402602048984400b03941140c080c5031240c0400ca001616403017074000800306030130b0380541c80c01e1a1101030303d00d05000c5503a00c2c4030b001c002401d88a54032642c1084110002c3c103001190740303d980f108030000000c0d50810444150141c00b01042c109904c0030703100e0030a18144804085401c800c130090900601c0241602c0c040050300f444000f80b10340d01c2d03201d950000c5010307030003400b2024090320420a4803011a042003085c803d01c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 834225161 1250 834223911 834223921
    0x604030516140d0807050a1208040c0e1b0d060915081216063306030b24071b14131a10020307060615080702070b0f090f040c210203 58
    0x243d0104402c0c907812150b030954031002402e005003800300c10840641008140b40302d040d801d80d401400c2c2403043d409a0103107001c0c1c944034100081522002d80d20506004100e102a560032004000242145040d00d18001052640c4119000664a1101d40c0201c0c0145034ec4040000407010301c101500b00d9070000300289042e009080c10700b17402c1c56000014007880d44d51602500d060004040e12840c2c03098030840f120910074281c030707000c0003401e8900410b070010742403903c29429401c1482403101c170f1400301c0122031004603c850002c4140d4014150a891800d408400045684418190000a00420b02c48842c46000280074440100c80d5081c0411045140c280108030384034884694441206d030840e000c1c10403110400040f0310b1400340480c040c28541c900f42000914102e200d0011007080340c1500ca103d480da452400580c0c4814251158803c046820045c580000034420f004080701c600c011725901d401d00c079403c081422030752110f0001010071039503807803104100940140e2140f4180c41e00420b52841c989 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 834226411 1250 834225161 834225169
    0x40c090c0503040605130c140a0806040c05040207151a090106020d080a05061810090c05040e070e06041d0103060f06081c0203160506041b080c090c0405060403051614 73
    0xb400a405241e0750070200c6c3d500324440d0250070300d07941c1004800e10119210380e180003400c0a15226203206200342c20740051280300c0421410f1007150482e0100803203924000c1400040d5000380030440700445034101c402c5240ca0948102a5289c0f541e4403100801c0b003048051200105040c0c1101e015540a00c5000c0c1d2111f81c0181c001d54011403070300001c58a512450086460b200002074040141a00341c0c040001644260380500103d80415105104400f50200c05981d03a2050703000350805400b00c18000fa01f482c1c007c140e03c0d000b00c60040d004615082e034450541039030130500c076800e64101c03007080d00400c14042207005604c1c20344000702c030403c02d0500c0d021000d81d40c2c50340300c9a030035240110303032440500303250091050710001c884040040801000c980ba0003600c41008490448091103c8042c00d00d0041c24a1010002c0e150807000070258284000708121101030000c01b08201d00b5020000803600f034991801074001548170300000e02c004141158143e0f2860101d0300207000c0030881e140b52002c0c69031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 834227661 1250 834226411 834226417
    0x120310091811010e0d0b061903170304050c18091b030c040e0133062c0a050a0603021312050d180504020301060f110c1e2205040c090c05 60
    0x20b8031081d80320812820200580301141c0c4c04c21020f501c85402d40040c410302000c400c6d134500c609802c64030041741c0c203821901400c007940e080c01301502088010b41c0c5540206c011000658005009000721039070401d0150004074084200003000758001c4a510500c440c81c441000261b1301070130309041c404810251200400c0e6030703018500140741320381d8a400720310902c42c90a61111507640810407900030054098400300100102146003642e03017141300c50002aa05201d246c001390b01d5160111080c00c845107031201080308000c028100c03035001c1c40c0410300050300e581e036102d07040060a03251805a11035604e00caa4400040c5150311444807541c070700c5000000030300040b0300104400070600b00031104500e1412468150a101c0d040160803920010002c1000354100d102e40c0c14000803656000320052344801919106c0002c002600d0300a018510700e440e401500103540c00484001030316040d21503103222039401e40403042403078600359141d0715006d10091256605d11000684442502031100858046000f49188 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 834228911 1250 834227661 834227663
    0x7030f110d030906060e040501150f0605070803061c051b09091e10060b030a0c0e030c01031d010f060302010206060102070e070c020f090703140105031b0607060e1203100918 76
    0x342d583c0100d0000c01486a00110280c108031030010044d141901c5c100c1e009261500d480001034a0151000500300400e00d05442900c5d0956034917800c2603541d0740d4103000c030f42016040070351042135101440440c0012503079011000b80a000142036000d0641c240c0b111114014a05600628000c0c041040c104400512020314007610307500e000444950162840c10036490019003c2c0032418802c001401512081c090b50080705030020411104072020703001c0d1045542043d080e6055040b92520600075030003075101d0b0200410580d00c203400001240c11182c00c5426a0200905541d5030388001d005559042200c00e600c010700380010320780203003401c10b2500401c000802c040100141c1c070348500d00b1901e40f0900084560b0000d000440d01c0d0170000d0020300500040b5884070341c0c03081404000100b030301e8001001180c1c00c0d140208404030108034801e20200394405081a140b150715020820b8858100304a07141d2410100d0840c0c5499080541c007403044400f09610400b04c00c1d0822207503560b12030604151900003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 834230161 1250 834228911 834228917
    0xf23240d020f01181701060509071d0f04110415020f03030115021c110c0a0605120604180b0f0c13140301060b04080133170705040c0507030f110d 64
    0x2c0166030004a41c0240030650b1045207607001e540004041281e8011480500d904500030720600751501c0501032800b00440b840c0b00000c4a07101400c00c41103c2d882901501e900190007040010180b0300840c4c01d8605036100ca04405400050410488000b00c003a5110b00406e403000c1d0000d90200458240d5901041c00790201c00003403075108120b40c0380200280088509088003001002d081544050001c840c010581c0015000e580c103a09000c0c40e10b0b401c036205840140c1c448070300f0650041500c07188803500409c5940c0003580c1e52003040b4451a2859000102d901c0b814000c082440c214901c070704190006400c1c50306144003881403102040d002384128055900f25000260915007041c0001d000d00495841650b007030800060204455030107401c04c80030640144911095510f00724070000b880000364813602050343c90100107000302d030007591040c1c9903100c044080742e0f10a034540c40001d00b101d00742d428035000302c0e500080708420513030000c55509015402c1d09045c5071011035154100e80f696408100c00e010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 834231411 1250 834230161 834230179
    0x1606050910032004090510030506010603021804090803061305150103020304050a060c030e0d0c08030105010e061b0c0a1706041103010e01110d1103090706030f23240d02 74
    0x312602c298030980c01c80f21280300391103501d0340900c0520102c0d802400f50300301e001d01b0f020000702c541142c107102804981d0310000500d0282c0c6030003011002904580c00121452a0842d4424100d65407401035501181c0240c0b56950350341400d030100400000e240c000409594140401c100400c070741e01c10410741e001c0c000e0801681d40d60b114a80b05042c030841c0c8000a044078a010325155044d58580c0c000a4401a41e104603014818406000d030703840c0c110b42400130240c12040005214552007060300841c00c65000c4c10302070600030780f41c401141c0b48070b1050f200001584040020410380c50a20350f17005c01042d4080c00d1601e40349213580ca254403003100a101402243c1042c1030070300d071038400b50700c000448100c0c84000c11006a1040c07d0142590100030510071403400e102080d208917900f1000c580c00751a0140081c21403600e0018107402038040d500b0480c6d052070b9100071501d590368920b1182c0301110342c00d03d41c2c02e440d4540107845503443d80000115607031201c0c076100440d203a5200c0f40c41d03035000c0c55011210499 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 834232661 1250 834231411 834231439
    0x70609060f091e0905090604030905120c0f010e0303040308090102012a2709050103050d0503071709070b1909090204050604090209060f0a05070506071e0f120c020d0216060509 77
    0x10050f4a561260011610384010480f1055001c58064000e6103c2d940304900651b0701c504114000005e019030403c1600207401058492400001102040c02c047c10501c0f160100400002e0a640056005890b001c00000b00315284d5a420300c104503041206410903001c4459005a444a48100e0f2203000c042c40143d84010002211240c000500c03090340061806009440750f84001c0545020b21007220680b00308440c10044900402c03c1c0c912821050740c5801c8603624803d4146019480600038020034002c814000c034070032183c07000800804082c0043c0b4041c05912007801008020b05520801d911ba1040c4801c2c0310300c1d80c96604070303011120311180268481c000440001e04c1449a203078144119080001d44d42c10094024000d480c20703a0151017a5120f030703515000141d88540c2010300542190158403001146203004149a07041d8245502d064203031502c100d01454202c907400048940580d1105101034041d40c0c2c10000d0341c40040044281805079403030000007400d2801a41d0940b0720490001c5040c3d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 834233911 1250 834232661 834232709
    0x70207030c05010c3f030f061d040b04031e1130180d030305061206010303050a050a02030c0a050f0d050f03060f0114041202040609020c06070f020a14070609060f09 72
    0x451419000c0302c603001034640c008011b00144800700740303a0341441c00c0000029074013181c00000c035102c01001400c12040d55131581d54220044004100f14184460311244500760240b2070054400e184580d1610000c40507824850707481c00c0040080d598569002251213806c8011901340f07240890000d080310342d2500340349080b060300b0a441c02c480701d800c5242207554606060b0b241c3c200f02d000b26000d0700c10901b0344180c1110f117500c40c0e030240005000715104009040351701d40f08800418200c141441580d080a031a1402c007810039842c840240c94950100038880314001050244c20035103407440c14568502400d0f0009100c03a8080241b1551041400c4800000c503640103001b61890729160350340103561242c40d0b144400d109800090305030301513450708601107843c407960300c00c5400c0e0300104030041010381e44003e400c40380d04c0c1404c034004045008050b10100081d840c844c45400350f64075500508a060300700ba01c01007000466078043e07404c006d8242c01c0d111a481d0032500001c07d451480144446003a2080c9a507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 834235161 1250 834233911 834233993
    0x17030c0109060515030d05070f02010e04020a03050106020610030b0f180f032d090d0501020f0412140703030c03030f0213120c090614060705070e070207030c05010c 72
    0x514240d401c00c1e01c070504110701d0b68041407260070101c2c40554031070604d0050503603840d04002640b011680401070300000c86d4281d05814003880c8145003031000300c01d001c03002c902660070041c0101c0111b80c4800040c00303503030740500905501c960003603800c0fa5a0740c07a6442d04440c02401411141519580c2004a11040340c0c2154a4195505103021075580704445000c8a0b581d82c05030100e1089060382e01c40303108080b00a4442600100d5103020110700f0000860b04000354440c84402c22911503608001695032018240058001401180c0044c103446007e07040801480200060414840d04042c0c020b000003908103400740c3d0201c0e0980ba000402d08180f505040081c07140c490308115104002c40d000400c014802111510b81e8424100380d103000da903504001c0c041d81c1d010b005200101c03d03a013040300f6050901c1000703028081e000c0c03000c80b00a0f650b108600f00c01d4450076070760480141c001c01028018080d2403080c641c014103080c0391100320710b1000c0d19400301840d01c103c1001e1440c0029601201a0040840b107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 834236411 1250 834235161 834235177
    0x30c13021b06010810150501120605190303120204051c03020c03120a120c02250506041706010b0a120209042a09090905070603020c0316060f1a0102071703 68
    0x1a825141101c040c03580ea5800034400c960b41c501c50038403281074090050090b500d6840121292415031401e20005443d40c21050702407880099a81c10002019522428584c070b0074585002ca0355080c03815810020101d4080c0c2031003450b1140100002c01203925407100b11885007903800222402e10480b403400300d041c0450070190940c540700e40043c041d8000c0a9200411182c8010380740e00d0400c20746052020280d40d85610700c440543c009000b000d0400d900d400641d40004000070311600015103030f20000380f243e0007980040120250407088039050120400c000e9024280021450703080880c0c0603401020841c101c900b0f92040e64011807030100c241c486070006000b8a4021a2404030f4800c000107040100b138500e2060400220f405200058a06180c82503103d1250010041c2031528101a03050780070354460040500d03070784400c00030014061180100954510b1054601094440360f460244007903500d4545110a20489400c41c101c0981e00004d144003221950b841108900203086200f03425030250950b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 834237661 1250 834236411 834236437
    0xa0b0705120406021903051303050904150905220827060a0309050106151205041b060c020f090606160c0801020a0221042601020403170711040b030c1302 67
    0x10a000403c899038014280550184184800c08500c400049044d01c0e4241c0320650100000b96418000c80e02c910010314032002c0151000c541da04850111880c40181d5510045035250b94200b4800b002d00d004145144200d9070b2824038141081646900072640b040100c030840009004841042480c200b0b0388035075404100425058030b2b4000e100c0301801400c0000011126546089004944852882404600d24207296510800f080640d030040c0700400c00a401a21450815078140c980e9400c1016220080c1943d903585600300c08032072040c80110716580c44030a204640036010041c0d10f480c0c41003510350804000b002070301b0072030b03d908080300c0448054100d41103079400056050b0441d50001069254000841c2d0141142c00ca60140c06a1900aa004004002d08070368101a05210242c04500e00281108001464295607541d5102624200c0d0b41e6040e100760701151080520041102080c80040c0588040c0140b400c03d40000e030315521020b40103481914058085030524031503070305072030a410a90f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 834238911 1250 834237661 834237697
    0x10608190c09051c0218090d050d020c121c0212130311011107110603040305190e0a060906020d02010b0a0b0c0a0c120b07110a020f011e09170a050a0b0705 68
    0x10310750715124041c0980590040728044102c6010810341e280003440f402400015051210031008e0444d030303e40c00403036054000c9800340821084c092080c0320711210000101c804c9a5a06150000d59034180000500144ca161041c441040340d00340512503154015074408040c29810510f03d030070307030f0201032021071100d03250b21740306c1c8100d05c0350014401403014074010460311600307001c00c4003001510302c811100180012018071007100144411552480d03103100c2401d1a903150400e080c00308405010a50083c0c0000d00941c104201a076014420301020104610090000c0400709004c070f482da002c1c031300c0b070114540f200151442082a040c00701500c1240d104050746180382d80c070701070460304c509d00307000545583c1003101c040355426000340041d00003c2d1010018103400030705502040302140c4181c0700a410300040c0d0110108107000940518000c2c11280c590100306c43c14000b2807a032120311180400d15540c0720f11068408100001a07132407100c1c0e44400701c954035030b8480c1070844031030254251035404210b1003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 834240161 1250 834238911 834238939
    0x2104020d030e0105121005011403160c0807141b0d050715020309060c010209101809050703090618050106080313090c020102070c08010c081b0a08040219030b0f010608190c0905 77
    0x1b40980d4040300d00c02d0740d4000c5012401c000c1100c043c407040d109500685500103541e0005801000c92a9100e07000380103ea050907425104c2c0d5100c070030100b18960681e00300790b2010004109641004c0c0d0805000c1d1740c404841517a990390707141c0e80e000c0c0c0e000d000b100710301c09940048007920810072140d00e0080581525141c660941425000c0c3d045207201502c51310b01407906154107441080c003010740c050b0310348010101c103290050000c0201009000030003019201da4000f00440c046006802003030500c45540080045181081c030f003141d0301500310400c65001000145460720400c203040e800c1e18420031000600c061017100076030092081b660001e010f5500007000240c4040198061036001403103440c3c415156a0301b01032001096000b081a540e40102489000c404510401c6200da00030700c090807000380d0f0400150f82425080543d4401c80b24000d22504010003c4d10308000f90b4014901c0e81003001301385c102009003d00c1948514600d4950541e1481c0022459104054900c010017016051601d11404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 834241411 1250 834240161 834240181
    0x26010608010e1e0c0d12091a13060e0d03081807030b01080d05030717040302010603060e011e1505090c0d060b09040c090803040918020a0b2104020d030e010512 70
    0xc480c0306040b98295010742c840c40b01c1d10101305103d00a40003448111100480e5a6002c0c20740d8038801003000b0001564001b00e120a020051030b800c0e407400314034841d122034031030703080d0b04040105400440c108100843c05001c02d40f243d4540b0b00708160b060400d000a90340d143c1c0d0003440e0005640c00d041e441c0c411034030000180400600854141c401c42401c0c1c034036081500740151458802594401e0015000d54a01100400310040c0c6a8002e4400c1c400416516642d40b1948d00703486400039101030741c2e559244c04800341e14418a410801d44c0c0460400c0c06410054001e561211560744205801102d401d000500035000000445207800041c04003000b0705c6441d5240042180c01c154440c0e80a6890b00b41c8140c5803e00402c5064100e855800c000d40c039141c00c1c4085030307000d0690080d01411400d45074080b007005a0300c154040d005400718406607511000c0c42c25540440000c007041b2941c021451009000158071040074070a1600c0c2c040c2061100c1d40720f03606c0101c400b8450700903511804c640d030005001d08664 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 834242661 1250 834241411 834241423
    0x30c09030d0806030307060504050114040c172409032205042706020c010f06151701030807121704030801150512010e0a0b0d0b0109110426010608010e 66
    0xa815011603181c8541c035802030b64a101c1c01e6034040d505038000e202a10010310036812030b41d0302521650001c50001c049015082d031040b42920115042e01c40840c09009550424040b54000c91102c0d00800205400782ea200181811030b10000300c01086410028540b60003c004680d13480a070501560140300200030071044284590140b544114204a1166807e04551031100c0e2948560020311544031070039030b80c20340254003946020085e5500c072400031244200e148903c000030711910005051011000b40f00030682000181029107400c0c280c0d0052020801070b5080e2840c0b00d500400c2aa00001070710b50550f80345d207240c4840034407028402d0804c400c04d03a0098959041710003502441ea00d9400e81e48041d2440d0040c6034a031814029400c0041105c11202e18042c0e401104900340040c01307201c2003010a0021550309030076682c4080394001040340040911580d030a020300c261041c0d007080d0514411102342d1009041d2840704884c18005035407188001c2d0700002c014106c0c103000b040100001400641c40d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 834243911 1250 834242661 834242677
    0x71b030c0302040b1219291005030a0503040b0904023a0203060d020108060609060f0a08090a0b06220617011109010801060c08040b0a08040519050c1e06030c 69
    0x10307013040001180c0d814103800307000c694004103015001c4e1380038000c3d400e00c1c0c1e4500a0310950340e25040038030140d690b03085803082055400c40c5c0b95024000e0319009070140f0a960340c4d030307020a010707601414040b4046000403094900340c4024141481e03a0320308450024010b0b00400c00149150007540340c803100e8080c1d0000c102c0142400b801d080c2c175035404a8034000f1003240400c42e411a0084e800006520040d032007504c5041d40807000900d02410f060545c1c2c04100141c00c84c0d00701801203080042c2a40c801504a42100da115100c98010700300f92030300c0e0340e03500b51401d00601018001c1070b600340c1c1b2400f0742c00b01b91040110341048801c200041903480c0c00900800381c03071007d100007a5103400a8021032003404000c80342c2034501a120707105543d28282c42124500c5284409407491081403002040c030070109002410490481d07583c094817803c05092079818601040c1007001c1c00c40070180010b00240c8086130b140c901e00c2044601845015101101d4446280c04580040d8441c400204122607581488044d207152 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 834245161 1250 834243911 834243919
    0x3180105070e0a1802040305030304030c021207050303040e0a091505150109080303040b07020a050a0317071d0f0a051305070908030418050a0204080a030917031e071b030c0302 77
    0x96201c0c0c08007569640d00d03084003142c22841e051401d1101580c810343c801c84400712044c006240030307600d0301c0b0f00d410354100342c5003100082c200200b0394055203401000b0801c07030185d0b417020b000103918081c00250b49101d42d00c1286441c2e00030600007014408298000c01d072003a0810b0f230040101c0502c0003070b400113040890398210300f40304043c01008139511034421002500d540200070352941d00c46850385440c20fa40100290304520403815440c1c006001030062071981c510039203544000010410f400d14540c00007d0151080106105158442039902c1040c81d140100a454803c203200b40d08020030070102c0d9680210350000e14206e400d856a0301c4a90205206000340e5a43c040440e403600c07082c0f5240d2240b48540d2404541c0303a05901c8880c0c6980d84817039004215003034014034183c0c0c4c030352840d420580e070041d05034003203a00648100403151407140840600b2030700d0000f42d880d00c0b11a0754510864149008004154500800d80c0c0f4200b01c546191a51a400070300d0a00400640e280762100c4411803d010072406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 834246411 1250 834245161 834245171
    0x6020a2d0309240509330706060e0408190e040e15061008040303111306030e0f160b0306062a010c08041205280c022103070f060204050402031801 64
    0x2008449800000320b00388075075244d0380751007800410080c1c1d84000300c07580c0d031891001403504421408488203000c801840e280280d40ca076a00360518000b141c18a0b070000f42001ca44400f04070002c0d0303841085800507040d03101d0080c409c000c800c104903481c103503005445811520305401c034103140c040021403500382c5040c0e000307007001c6507901e000740043e40c2c40310144480815541e002040020b400394028001001805901a0501900102443c2c0300341080d80504082555110303d0442c00c9410312088440090101c018218200c00321203c02c900c2c3d100d41300700980c500c408004100107a443d4022611020307034900c80f00280c40c5020a82e40313103540003c03040800c55841c108028000303e0184440501c03841e0001340483c00e074510f00030183c1c0c10342d10075961213980200c2040c5d400c41c144503440442189100a603507000d0344200c0d030301c103000000c08a080c3d01e165000e1003200d03020000100004561003140e00811410600303016290041c06405190400360f402800881004042c686028003090803282a00080c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 834247661 1250 834246411 834246449
    0x20706110d06030c2405030a0b06120601030507111e030f0409051008011407030b1807080a18020901050d080706092402130618050306010b12010e0106020a2d0309 71
    0x6030117407240314481c13160310342c0345070034a49640034101031036101d040780b54042600882d60b000201a5400000c04c603030341084003814080c1550740741c418168400b0140c28003120748010b010b00300d41d41e041c0503440c000b80b200400744060346070401030080c0d4200c000c401c0c01960711075454240107405080101c0d4601c1c40e00e44d5010300011026414003a100500c8040451a011911910b03c21009040c1074605503030018100c121416151000700501442480d080d84c609520703040c1244080c00b41e911038134078005045249403148000d0790b141a00300d41112003c507003e540954903450881c905015480000d01264034200c00031003070101c40600b440c1000303000141c40100802c4080700c0c004a0080c488140e02410980c2d60511540d401500c00200805442d00c0070302c03070284c2e1a00000d00d4403509030410400007c020945480c6039444052042c0074000141401c1500d41c14050001e58540c9a004041d0801c0515008111003095800d24035000c2d8a20151402a2848508000d001d030031452203848440c0d80e030035070303040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 834248911 1250 834247661 834247679
    0x16090c0e030d0c1b03080a021c05040812030604060806010e0717012322060503070e070c030503150406030b06030610061b11040e0d1b0201080109020706110d06030c 72
    0x5404190580341d5225241d86602c6104d61050344030b00d1101400d00d592800300116007001e015110b00c045d19402001c0060003608504241c0c06194655014807000340800d0100c03a0380428412084002a04c005841c2d980b40c00000b009131013140d02003083c1e402005c0c00403130a0401c440e421031281a0301d4071900c1c80224540c5040215140034401d40800e541c01c48100c001310200e80018224203e80140740c00090b128031500c144620050354001c0c06280c0d511001001681000d021100007405003003141c0380585400070380500031b041d885c0401030400c080000006c8081011200488907000007a01c1003080d00c0c0c5074900a000c001055805038840c7c0f28500001d408606d8140d108000c2e04c6c1903903540194041c0701c1c0c840c600c960b4180b29003202c1d803000404444505407114420035081c520700400510950880010240c4501e41c1c62104011040c1d2911100b00540d07041942503044403070030280166900300500f01200206940300d911406034000150344045603a181e00240107682c040d6856a143d00c0d6500914 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 834250161 1250 834248911 834248923
    0x310030c030507031109011a03040f0c26010507050a050d480905010e01110f0303040b0c03160e040207240e0624011806050a0e0303070f02060c16090c0e03 68
    0x60391000c00007d902e90b60790140c11014640041c480d80c807229400c2f11680d107290890207190080384440c104a114502040c50030008a47e0790580d28008128a0034809401011442142d01074401d2000010b0b100000e190154030110228052440300c900c0c1c031800c0c8c2500300007c03205202c0030088944400d0896404a0840e80c1c240f100903a40c0c0360450707071030b00e00300040d1030140307070302000605020030002070303041110b030500540440020180c00b46540c1d02e813030714040e8405903016000700081c0b5002e00820244ca0400041c5034008081804e04403000c03000200050003a101c2ca0748001c2c401403994041000410303a9001380d00c0305002100701032182d584822000c9a840000700d6040c02c0c01c82e84418400003000102d0201314503504185000b20701b12444411501d40703502070340c2c0000b0000e0780008201c440643e000010303401d207a204034081d500d4040d16880d54154400182030103032240900007240800c3c41010046c683e0021000712401c0320040d510300b01c81004001c090060700105650200001103440c0110350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 834251411 1250 834250161 834250169
    0x41b14090114010e0d0606032306060910150206040203010605060715020c0106030209090303070e041107060e010b04230609010e0a09170d021306230310030c03050703110901 76
    0x3120240d0380b8144160500c0d000c14800c481c10310248550086aa031034005070031070114019070000c20517500d5490300803050b01c0b55901c90866600c03480000d0075012408105580c200390101c60000442c0c4404004c02c4203180c0c90b501a0304114440500d509031682c000c51020307c56402100200102130707481092000da803043d55001030070b421080040380722076103480d80508169030740900000b8007543c8a9011501c03800f000c1e207000c10594004402c000100c6da2001484540d000150303000d009020342903542d00c00901a07008010b025a44400f014131038140c096200044000d0002c1044c002440304000c441c103036007030112456480000e590000303503107820a000c00c507040315446500020a0399036400700c8001040380d031404885089528201c103465602d980050800702044500060790f5840090241817144440d502c1107051121034525240c0b401807070920b01c03803201c08001c0c07801c2d0760b5035803a46485001003080d0002094500c0e00702d004001e000001a410040d80d00c00c146d6055000256410414038220900c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 834252661 1250 834251411 834251419
    0x6060301060f0507051018060e0c150325090608150a050621010609051c02061803120c0f15040f03050702130e030901090603021201050f01120203041b14 67
    0x440c4081841c414030003414040e019030242d6070262000b5074131b001070b10300c0000703081070070140070b0b4403802401078905c0b402d0f6484c403000c0c0044c00316030121000324200d41203658032641d1400300400025101c840c000c0305038040c888801c112000c03100c4040b20242c80d15886002d103000140389070001902013a0003540390009042c00900403103440d482e000800c10315a000724130010030154121b40380d41e10014070705d210502800c41902c60180080c2000c013403140c070054510354003144a400751200005a00c44208440c1c0451080700b0b020142100600802d28101d02002d56421003400051400b20300340c1c0108007038035540410400c4e11503090703046002c40d0a40700140ca0244c0395102c00894580001d000710020032000384098114101d100c0c0602c45401111060b401d5400310780c100184294680d030340080d01101030300c0a4241103080c400c4044252005450500800e4091140b0200e941800e80c0514406501c1444c42c41c025540c03841c0c646800d113494005c462031502d00200048012941d181800803075055098054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 834253911 1250 834252661 834252677
    0x406020d0305040218070917070501140a081b1c0b030712030905013c0e1e090a14070309060605010c050d03051f030303063012030f020a0f02060606030106 68
    0x21706280709440d000b4090005000c2407400002c0c561040050824409200001820407585000c001503c4ca04000203200c010783c40c2004518600341c1c0103d941c03600885042404c184806d9501c011f41c01500c980e1222100144941004965818040c5c00c010182101601a2202c155440e050390400029104004002c40c0c15202c0c14006544154502c0d0404000c45424221914101000161701010803038140903c140c801004a049504125201024502030b1040c07401d02d00d01c001c50039403440059500c584210200408541c40c40c03036030b80040c00c1003890461550424280a0170150040090150031900e580c10324400085560050b4450054070343c12030082d141e42006910118000c0a0042580b140d00540071081b0012448030048000030710700c252400181c05007043c1e00c0041c40c0301c1c07907a00d02c0d111001010148145240c0b800e03100d100c05500c4000c105c0e1303071355100d02c0039409051403030120084103101003044449207611041c2540c0d9082d0301d409a6206072240c0c4184195407000b4020b10022a201c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 834255161 1250 834253911 834253939
    0x4200313050a061119050a0c06090c030506180c0603061c0c0305030412110901050f01260a1406030d0e100e03030310080d020a020919200406020d03050402 68
    0x111011544074840c0c015900c0e81c07440d07035a0303003400c03580240ca07080844038010510006210154040c444050104d0400300c0c18000e9040c0001e00451602070020003813a02c0d01e404404118081c0300c51f130f02869004090300c1880c034001c0032042ca00048503103404110311440c00205580c0c01d000044a005080140688a80c10312540c0030b45109203001a04540e08204a140000440e0090000c0c2000d003414010720340740d5000505103100c0031441200f105120300d42840c0100280c0c0e46203159003103c14400c1c20f103401c00407250020b882e036503c5580360300c01c4800740c6c12040103100012179010001d14100c030209600141c42368010705981e04104200c44003c030b1001d40b25280b003460038021654450800e850020b002c500d000011074150341041c2c810f0780d00c02c550800180455070f801c1c01980a0b5400c544000c2044e001c0e19000116000809054660320204188600051000030340146504007444118040884040c112445495106209500c014010611070402041c4280541806203400501890394100300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 834256411 1250 834255161 834255181
    0xa050906070203031e030601030c0912030c0311060703020415082a090d1109090a0f060b06040b070308040b07260c090d060b0306010609151d03070801020405042003 72
    0x70460781030741d26120500100000000b8940d1500c40f050384030003440c0c0c44c0c2c100b250002d001d403800e450075401404a550700902c2031b920380c540038055103601860600c5168015090136150407040b402c40c0e80550080700c041101e0140c154000340211000c2e02400c000716140d505003203038400c8083d1007001c5c0c3d24070400526070b00c8004a90f000080500c003441c44518107020000040c40d9002d21a80c1214440c00140c01c0e540c541c54140403180d40716880c88007501d69401b140e662601d900060071001468681d84020200c02034880e902990080c0c800060220ba83e8901d90070098007450085408075821040100000d042d18440c0c1c4120303854080c1141184402003000f0000c4c1c80194000f01007104034502441240410ba03910009030140034007076000052801142410300d81441016040041445584502040741d42482c610b855100641e0340780c02c54000d0345400d910524a500c1400e40c5034140f061401c0441d00304419801081103501c115030800108009401400b804c1e05040561400210184005104004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 834257661 1250 834256411 834256417
    0x1501080616020c130906060906030203120a1b052d10020d240e010501050a0f3c0201061401090b070c0e0c12131110180b130b0a050906 59
    0x6006442c00369100f07901144103921220043d141003a115541001405554800c1802030300309507006102442c00c1d40c010a5403100000b1407000000000254000c049119840c042c0000c003041c00d01207580302150074034a0ba80c081c840d03e41a90992050700c41c065458101080e001c07260448009041009071104a060003500b05100c40c0e04102d4844650101c90400301000380941201c103031402d04a24104040b945018005801980c148002001070382c1c0f1880d04410001d0046283d40b6190300321206801d0300725138180300c1d501c4086071203d05418002c840d880c3e604200803141d80d5640200031060791662008a0481c003a40f0850224800030014410840c9d2100200300031070045150903842580c0d20b402c01c5581c103040f80d0300c00e007041020810802d540003010149400c440a0751003000402980d4940d441c5007001403000038423600c540400004028022a510414492500410180c03607948031803440c52a030100850030746000540002003010b58001c01a01c9019000380d070342e50300b456a8a814840c49034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 834258911 1250 834257661 834257701
    0x703020705071701020a120c05090f133201050a090507051c1506080928020910080609150a020711040f1e0c021c031b1115010806 57
    0x1000d115004125034280f03076070903400480030400040c0c4c1c9442a250041810400c2005d5982081c2410002942c3d19440010b48880c1841110300030200410200029600e00e4503000c0c000e8014140100241c186800c1140d008207006145903035101018880b1044a10320424000c855010101c6002481b0010041d44019440070032410654540300b42542c1450800c07004922401f4020f80342d0300b45100c3d00641b4180300c00200440d04099802e81801c100c403d865182c5400c070340c0100e031034090303c400070b5109050b28401e502d038000c0d145148034288500c2c2c0b20759080c000c0c022440070344100c0e4003281082c10002400340318100e880610644584840c3d071f20300007031360202805946550440360010410380d42ca1040b5400701c0d0200070300181c80c680d641020b243e00c200c03814500306054540034265028035001308507480d070101201b5541f135581a0344541036000f400c129030058014102d208000c1c080c0c9802000c1851442410821940368102c0c40800701d01d500c0e0240240c070314941141002c200070611205088001c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 834260161 1250 834258911 834258913
    0x90d0f02030f30030106050a030507050d020d06030b0108030f0403062301090b210307021c120809100c0e120106081024080d080a02090306010e0a0f060e0703020705 72
    0x403624990b1200d1821843c03600998039207208520a980e0341100e08a0a407041c0c0e10002001d0856240190181c01c60068000044c207054840e00090720807445201110341404117050110b40320760104102400030a440e000460f040702c90280089544500042a608055440c2c1159441e0504698400000d030422000d0481040072a40e506141c88042010f10741c060a181880054126410000c01c01d55450000003500803030705041c1e01c040320300d002004480220340c0556101c1250743c144d4000c230400103820480600340503034491030080031540c4282264080c0907140c0440d01c000d20201c4d05041207401e03241001000c500080c2009555003400713401c00740d90718030410000038407958850285007807040031a06260b041d9560300000707180f05510700100c8090606551040825030622600d2a6100510700c102024040b00b100080c0c90413842c0d0301102c46d81d100207400c2c3c4403196503a0505511070b60082d03401501c0c2604007000c2c504540309510070f4074216044580c0341c650030780303d2f080107030002d502480054480d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 834261411 1250 834260161 834260173
    0x6090213210803070c0b0612250302040c030504120806090103240e0c030d030510090e0f0a062705100b030a0c0f050102062a0904061508011a090d0f0203 67
    0xc40d0b0410040c500c0790365280c543c0601500706240840b0b0700342000346258801c8025000031025940c0005030808000b0450712050002c1074a10300e10100340700c02c1d5000951090500d14440700c400d034550401c90040744159080143e201c3c10040541d805002103034400d4100140ca0010000b003011009501202e10840307a80b1030400540b00804020f0382c5010355044105da00c0258200c606050801402d030303200701d4515041003d4280780700d607120405030350f101d40b0002c5074031082c04140681080c03080019540001d81100c014080a28044003d402180400c20ba00c64484a0550001010f001f444039195070000142c501212400e90b03000040081f030300e1603501840f501d0440000601460101d50140c1a0007503950300e4540b03440002440c2c40401400b2a601030840d0408100c580a203a0510104520704003001c1d0322401c01101140040c40980d000d010301e503c0100e03420030b06680010385141a9159400001c1e1603460170400c02c0e0b0705108108807140c0201071030024001280c3e5580824001d42d200a095500b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 834262661 1250 834261411 834261413
    0x7050d031b022d0901120c03060c1e0906030507110c1009170307060b0102011515050712051305040c050912070e0f190933110d0609021321 61
    0x3e103482000e2602012264a070380d0001c81d49040a5141e0062143e0795200c1081600c554851800007418800105440e480c2e0407100c9240d4010b40c1240580744244070742c0030225002c030400034401c0741c0d18418000420b242c10049060720b449031710400e04409080700108445001c580c01d00126100402d02c2d8030411101e07071404900042000c54810440b450769004681f9010f40781418002c03a580c03841158190380c9031400003032076180e000c0d1445c1d04403401c0c000c0040d803882c0f1120094500c2d10410800400c3d500c0110b030390180880c5c1090241c403a0f142e4500e10018080c2c1c072601800220b880b84004040404e10510814409250000802c0c009405440c15100030503598040c42072440b5041e50154140000c86003001001c00d40d94004003a050802c0c1007c0c0038881290f02c400840200021507114154104265024407020310b5099480c0c0c0100f40c4001c00c0314100380380c0444170300e0300003050541c4164140000019022102d0098882c00c0d600340007a04c0c1d05138500721600d0201194031403007800144002101d14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 834263911 1250 834262661 834262699
    0xd090e0c09062b151e030506010b0d0b030a03080117060f010b1e0a05071505040b0c250b071404081213030f0807060b01031b27031407050d031b02 64
    0x3410310540c844c10b505105042480c5010902e646110004a01e0f15040e0100040382000500c141140c900c034060390703901c800c10074041d00500861034802d07816108961400e020141d00c000b2103030403030b40103084030301c401410140f046882d21003e490a800000315031340148241c000b0440140214406030507030b00700b21000d88000e920541c02c0110305001080021400744203104401581c220314250306801005546010390b9074961054010305401e804450100d401c003005107140355000a46204440c64103000350b83c520307000d03e100a003100d01070000350904a02e2000c1c0d44504bc01d40e0180c455640182503400106440505a904698101c9040b085e00240000205100f00c4802610138010a8080c0d92044542401c2c8146c0340304042d0a41018a48900d40c0310500c40020315140e10412880d04045c1c10626030550181100400c18407240c41d40c0e040000810444402100410342c2003181c2612902d80d540c001704140034040043c0903001c1001c40c1030100300240c0300002d20003810710082c11402e580350207056070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 834265161 1250 834263911 834263921
    0xe1b040c110a0b010f1a0f070204060e0a060305011512020906010c120c030f110c090402030339060105010522170c15160b060f030d090e0c09062b 64
    0x41d50701001403c0140b01d440d0783c03140d90034050300b4030400000b40450a070f24503080e0303032044104041081e00301040c02c204546c0c1e0703600b1842c0100260f541d800c1341802e040c00444001c0c502440121215031030800101c0501296041c0e92086511659103d10545500d400344054010010b00e8507041050103001a0005030074102d076205031a07020355510030340800c00d180c05804940750b144860107101c02c031a02c0c2d0000c0d80d00054040d1046000740d4000300c06071920700c041f81c614001c1c480660704510b08064036400b100545d8030b0010010402c6e00b0f0b00300315441c1c0158101e03252102030142c68000b4000300150030410241c02122121203494144410b03a5a0351416042003210110700d101440b0741007580c0038100341c5080802c04a00d6180403a040c0d18094010520161304040217100410381025a40002c00d02d6a542c0c030b035803481d000040d00780d0700642000040140742507890f0240d5442c091861012400764100b2205440d03d4000143c225450008142011040d0b2204208400c100c1c00c100f84400a9910903400f030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 834266411 1250 834265161 834265163
    0xa03181b060809010504110112060e010605300f041103060f010602010f14070e010e040203040f020306130503070f06090212100b030a08040611070b0c100e1b040c110a 73
    0x1120201410100000c045000103001c43c80b40c0c3e8108024040400d102d6022250f0040742403c2105c0d4540c000300107203014240c1507010b1840c100c049000000c0c9a0b8201c0300900904503520710450b0031081c4480c3c0b082114001c940040700d1140600e00080383d401400140c03d0300107000701040741d0b1038890080003034a82081218210700d0b94101000400c156502400780512001040c8414446028a0740002104150040010003008170080350060700381d01030001444805000f5105554901d49401c02982404d10340c1c100324080d1142400041098100e000e044c4002d0798000c1c0514a84462920341038800c08010000b55041588c2c1c10001005a0790380c00126803081c45000134000c00544440000e088410821420b40203800c10034444002603569401c6a0030341e001401e081c00840b042c499000e24000980e0405441d07200001040303010303c0070009000740e0180c000384041c4801c41500b01001d0710342c400c1d400304210012038605042602d18107074001d800148020301e0703e50400404807041078a0418003044c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 834267661 1250 834266411 834266453
    0xc030412081c09140309150904060e0a0213060f0f0309141903180501080a0507030b2805010f0c110f032b09050102100b040207021302090918030a0318 66
    0x60751010404c00c03800b030482c1c0d20304060240d41880c0140300030418480c40c00105005807040041e0101141e592548908003a190b9018415201d2a009054600a6020715100c5184003030614001400900c62074164640b42e0480d81d440c40c820002c2c01e0240c003e4440c00d041100c504020020068139203030200062880038020340c01069114030141000740600e80211804c2030301001d5440244442e98003c0b6400303401030070050000074a941c8031041140109106408158410700220300513950700c003a15070070540705003402086ca544507038640064805040f54168180400d92002c114404100c2d1845003540c83c8070003604490300c0507a10800a030520040920117482211280d0b09500d60201e8001c1c11030600205e810f050514a0401c40041d43c0c81607080c001250355501c40c40c4005d01d139212034040d00c5d80b05901800c1c404480280c0b209501c044d421044015010325207400000e50443c0305615012041041d14014500d4265140c7c0100c000e40540ba0b44607504009040552001844222441240346100c075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 834268911 1250 834267661 834267671
    0xd090c090c050714030f0a0806030703020405040f151a0d060e19060b0a0501050702120f0d120e0a200d150219031407081512011a060c030412081c 64
    0x1c9441003501c84d0300400a1002d52092205000034078aa90849003000014200702145545100020b0b1401c1c0054000030b4009041c5824001000404441c40d41150301c0341000c19180030200c0020300407102c480041075410102c1100f90803150a10030a0400460300840d00425000d0b0802e194604e450380703001e082140030f294440d85d01c0c00d02c0306522459408540859000e21050700e8200001d18601540c2c402030301c98200284464154101000140807900c09170040e68041118920040d122aa41203009a0200d0819603441c0c0c0494002c50300000c04c50744a41440d0004e20205000d05100d0010503600f2740027603007001140c0201f55441043e012010004501580d02c0060050a504a1121503001c1c3c081c54101424030360620300032421664403104c14074005180383c1c1c03100650014012000c03202908031400c8500c0c42c1010006400a402d801005040f60311000c02740800c0c070070544224207518074240c00c1444140f241c6050680c000002c18000c1e01ca80d4105802c1006069910800744240083c2c503640d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 834270161 1250 834268911 834268913
    0x160605040603110705030d15080d0e0a09050402180c0409050901090215040609050d0c2d0803072a180506130212150111030408011a03030705030d090c090c0507 70
    0xb40c05240c916018109481d400c010b103a59500380d4a0144d0b106401c4050746030090001c00500e0070401c40300030710810084480421048001405404403840701b0f03805101f00100200b000e8000f409900c4c0580da0150408040c40c03500541044145005000d101600c1010000050400a14000c46001e40346840001411840354810007560807000540d90031801c03403e00080001c2900b0002090440b030040c0c5040610450347d144c0b40c004003481e500302e2a4010081c1c210082c000c4004000513607074009200a01c802640c40d44904d03562405400710044c40e00d21100c446046500302d900000040d5444c4c814140c0d44540c036040460040000314004140043d9074100300442450040f0350b00d0701e0a24401c00840c5000359410404119031401050a010f01350008100b03401170f40b1450516440803c1c80054a403603a4171a00f0080c0079107502110711110710020360000d002c5243c0072080b200c400d0341c050001c61900141074505400b5242014090b034135411030500c0080d141c01c0c0e60040d190300e02070b20790722141d8032409 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 834271411 1250 834270161 834270167
    0x41203240f080d081f0e010902070203060109021c0b040e0d0f02060c13060807023c0c010f08100801060303031d0f030a300204030b0a0e15091606050406 67
    0x651003400a60f20088010354001d8000003e82d4102d0b898000d40508140414400c492407459030344206244035290000251024865010340162442101654078599862096900341e0007107501c0c0070742040d02c80040c15020b45056002c1c04480b44050004074100900d030303203081e00700816080e04501181c0c4484800010070760500085900986020055040c5102c1c00c40c07010b07402005014a41c107000004d4042410f403802040038114031204820540d16640f00103042002c10303c040c0e820f500c12803c980e04500e0b04110041441845e035901a235408c7c0d1401514442262035a00240c81400d005031805404510030000b0b003c0d840103940a03480c0401c601803d00c0c1102c07100010055106665004580001c642640201c2101d02d208054a800c0b400703600c83d00803800d10441c5009078414040390340e580222030711100350040c2045a00814045446a64011400702554001c280f10b9203590407030014102580111001c0c550018820400c6500420f00031000104d064419004400030400201e030400c64154 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 834272661 1250 834271411 834271439
    0x10b0414061c020603130c23060c0f0105091c0302162d060209150a14090307051c0309120803040f031106040b33040902030c030307080a080f0f04120324 67
    0x4043c400c842001404080b5614211015041e0b1034809c0d400081c2000d00c07000b0801c80c031001c54100744006c02039800c0810005688a4011035560703450041041402c034468003901c01e48161000d019034017448130010780e0720314400680e800c06100891203201840c820242da01001c0401c6d0364401c160050790781200c00108010076030001d4004a0720325080001444041d0301045000d1103454490305c2c0c5031100c03080c900290910b8082d400080d0400140d4080740040f002e00d0342d80ea18240d0007a1500d14031030303407265061072030076410365006040080c080006c140000c444501c0d4048441c001c0c503008ca81c1c150000d2080b03003017801c10b440c2528107810300c00910030a01418140803240c4c0b4540c02c01c030011452001401d1103c5011040000c1c0f0507540d03a83c4071010340d14103024041685034020152541d03505145040f0103da0810283c04002901c04030020703000100e100111800ba0890804501146d9240e0780c406515aa4602ca080205074541e9a50002114840c1c020400315202980c0a080d0754100354003400740d52 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 834273911 1250 834272661 834272669
    0xc021c080f0a060501051b0705060c01050f0c0f1803010204030807140d1d0f030304050607050f1018060902040902040c170c120c0703090e010611010b0414061c020603130c 75
    0x40c906941001141e03000000c90328008030a4000303041f100c00c00c0c0740d4142409065070146401110000d401c02c0000419406244582c1401c004105540c46020b505481c1c0d02503d9110f08551b00c040105440c103102c40000000380500c0280003616084e1242c2d20340380e103a00f10318001c8444000200501030702d00b00030301c549248031031680f420034110b0a5911480c0300b0b42d44410b4045000e5541c20304115095281442200e000e414040e0055554440798078015a46900340449070704070380501c030400808035131140034059103054415401e055160710f03500c0b90001058500c01c226805955021350300016101d9004003101c90b10541c8610585103020003a8160743c880003002410111410464a0700d030f296484a565005120300e00f47c0703a01c0707201600d000e94652440d500700a003000c0d1041c0000800990200311208000d2061000384030400909041c00250f456000c02c91501c0075450000511a08101326149007205400c14039a90713080003500840c072990300554042d450f41e64060043d0061000309082c8100174 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 834275161 1250 834273911 834273931
    0x6010c1b2310140a020c120a051504020a09020309030c070303051c020301080a0f05030f04140f030607080105040509010f050a1a030303010f1a0714070501020d110601090c021c080f 79
    0x1d0801d03044000c280f042091042d0900705408104070200701d108000d018a0407102030703c0c82d044502141e881c41d0361a483c1c0312003203449100d14040d401d0410145c1b129980034a501510b203c0d281c608044021002e904028001c1c0140d110920820030341d05010010303034000751f000780c076141d9a5400180b58400340c40407420801001034010001040600e500003202403070343e0b81040503100b41c0f04082c50807904520400149a000d00340108010030200e0040f10b0711a48650100c0319082032210240074036841d0001102c0350008501c41800400007406c0607046250700c000351400000e0a0300d0f8001000c0e040350410380c0c0310f0320001d56544402015200103403005c0c1d030a8900710022f6056600d4003120554800c031600030b1118195840d1018001c0b410090142c40369198410380722a80e40358840c09883c0d803051103100383c82c01440f802244e24640b41c0a9030b540b0608100013170181940d40c0c00c4c0401403014007207554006c4214440d01100d0f001c030760b030040600c41c1e0b4035846985090560400c1d440030048500003030584550 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 834276411 1250 834275161 834275179
    0x203070308061c1223070b0c09120708100504030e0d05101a1002030c030a140906070f032d140d0203010803030103050c09061c0f050d0c03030f1406010c1b23 69
    0x2000103084140c84040d076000710806419980c0c0248c40f22503000e0922040e4103c0b03101d0407180c0c1a11f00c0458104143d80f0090100e4100d00a07490b00c2d10250741b402d44028011540d4a10f18000d10f04000340c54000d0350340900129084d100f0b10314950000c49205060305107d210091044100c545030002c0403540c52035041c8021428015990700741034691080c03410030000e0002e199001502650f00009950050700d00919898441c070311414042c0c6402c100a4088000500c810385840080d9003400d8004c04445039a416800c52981c071075000d5461000c00103800c002001e060141c201581050f000541c060144100616200d514500d05149003c0e0800c2c0190301c25804002082071a44545500e1075400e02030f80e9180030754152031700b003c3c400d290724684007034140e0003110030290a01e6042024a07410340c0c03180c0ea00300100304098820104032502c038180e40aa08440c0b10204005600c07500c41d20000d5070052450070241004c8003d800d89030342d40341d40085801c0d0340300d007450380745e0f002d510328800c2030b5050903074001e50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 834277661 1250 834276411 834276467
    0x60301061715030714030c0a0305030405060f1b0703050d0504030b0a0203131a011e050906010f120e07090c0e030604150b09190606050a0203070308061c12 68
    0x10561030300e035071011049128000050300c2c048608142c0320b0550005019a20395544820300024401c000783e01c154000c0c0b040707a09003c0103040102140007202d8004003c6c5003450300300020040c40780c1c040c03030324021600401c0c810f03022034842c480c03a1480c050548034005c140d0300d4510b26285080525115000c0e080c040c0c00c0c00b0400208070140900c0f0380c49030400c00010303901d603503200c880069408100300181241446004040b0120600d07d1654142d80c04120340150044000c0060a15940c10b4040e05801411100104030154001e1410101c110400d0900c2a000c0c007500e0503003012640070007400001076010040030000421280704480341150b044c64036048100c80381020a0307813944050801444451082c850600301401da61200660b140b0081c001d80d40d6003001c8118011103c02c8580145450385040320004060780504225504840300d5000b4600381000f6132001c7e941c0c1076004041c0da80201e040110071100c900c0c81c40380883e80c2c1c6d04c00c0c4140007500b82150001000c0e40248041c5814110b4002e40100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 834278911 1250 834277661 834277667
    0x702060906040804090507050f0d0b030705030c0d0f2a0e06060703170703020d02220902090123040b1209070e010503120d0e011107060b0a03080708030a0b130c090506030106 76
    0x3405c0e181c840e080401c1688800100311200c0c402c442526a050401090141d01c0140c0c0742c101d9410080100d0440b61200d45038010180c9441340c000c800c2d64802074040c07030040040c414800400c1014022000c00d003049108a410b001c0310b5a40201c01d540840210405010707041c04036000030b401040c1560481d042000f1a0703805402070743c41218050301c04d8144000940c90034403c0c0c0480745000e40002d8195259402c1c0103a0104071020201000001d54100c0c2010031301d109a84281e8102e000165580c02000d042891020400d01e0030700b003458200c60b0300300000724407194628000c060002900d03080900d240341180805040001035040707d005070f10312000410060b17a000546940a80e920036541b03a0b039141e000b59500050010001400d955420180d0000d408485c1c8405410894082c0d4401c0c46510b0140c41000120b84803800000d00405c0d09000d43c00106100001071540105400780009850807070340d00060020381c0d6103000304852500c035000041701c1c9510221043c01001c0558001e811541804009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 834280161 1250 834278911 834278917
    0xd090e150d170406170906071b080403020604060806041802031f0e010501030f021002060721020c102301141002070f0b0711061317030403060f0507020609060408 71
    0x620501d280c4000200b40b00000c1d07903040c040c1d50201d24107592141e8407000588040030b41c580c42c401d00d000500c00103ca248012074144e00c9042c0c5517039203100021483e040c130580c3d00030f6848150750090b020700c80400103071104002080a00004d4566030313081c0c50180100019115100400010800249404c0006880005c5e40540e4000220001145982010800001450701e200411620b600305000001030000620b01860070303a0082c0c41c0211601d110081c1a83d0342c40064440e40c0000300b80c0c0c010745120815100940840c84101c0d0b10151510b480c031402c40d480c1c00b200d482caa85504d55241c100d5400a407000110000ca2200b040d0b0260301d540c900005950000707441c0d452140995400f64000d04028405e0120f100980300240d004081c1d29102c00c070b0f01c1450b810040e4212490000c80b05070712a1840d018080d66800c024005105411381c4c02c0400100700740c03884c200500050722050102000145c1140520034245801d9240050140781c055002884c01d080506043c003641c00200600010500300003c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 834281411 1250 834280161 834280201
    0xb04090e011802091902041518080601030f08070b070f030e070506090418020d15060f080a140f0109030c150b0a14010c0f0521030c0403060e0109140d090e 68
    0x40021259280303c880014501d17840784c8180c120303200150218000340b00300d0000804615560f106d41e0311400084038000c0b1520340d8003880880394810001000004c0d000d20007850202d104204160a01c50541d031803c44e038090039a44103010401010038041216458455608a0a00300006041052814003c10003921480a8981c013464072000083d4101d800f014000707036620fa01030907441c9202c40c1810441c81e0950800c4900410600308800050300002c0203000105444000015007140412071765601c880d190b5125000c0d5040c0540c654a200600e000c2c8102c2c1c0c6254001e45030740040801030719103901031604800d02006518070340b00e406c00440d11034030384940a54400f550201c903066030140060b45c03d4111204000c0c89100074402d540100f00d4041a031000b114141078be03101584075802540301407408100d8940e849200140305c1080814090b4001c206211455000002c0e190600d03100c03881c5e00031400510264952010000304912035010746984014100403441c0151420010003220840100d414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 834282661 1250 834281411 834281419
    0x504032c011211030c070b151f020a02190e0c03070c03050d0207050d030b0f0909060a09060608070f060908010902010203090d39080307110108040f0602040b04090e011802 75
    0x1400b14220242c0380d101e1640d2203a0b0104054403880d00746003224140e400017000b00e0f8260355010100304101d203030007003640c03608030300030200075144a10030160029070310041680f80441c415000d000700980c0720b031604603416840c1607041c031003158100b03402e21070300c454050109004a08204100907d80390300900b440c400e40d2307041c80c2080c1e45041d08040310380a80205000a02180180411340341666095481025910802e803401030710340c2001010480501404c484008168020030002510400c0c140c0c450002e81e8414800020351a44500005103041010307008040100c00e0600709212464200341e0144c000e2500303500921840718103500007916070045144050144100301221010841e06010218a503c2c901c900d400013100d148007240d10360b00d4000000642104250b40110340d00c54040101c8000940000c40103803c01e00010044502d0200100151120640603950b413000900030300081c0010421594107603181e500b40381300f035011102500e6030f50348903a00d4408907103c4400318400a80d010340d0112 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 834283911 1250 834282661 834282677
    0xd0b0c0703120f1e1506110f030301030825050a080a0504050d0309090c0903080405060a03021e040e01050a0e0f0a0b0a0306020d0b06030c03010312051308010504032c01 74
    0x32909607040d00c0c0040303148840b64100a0210080c54140d0300c9044c00c501000c1c5004040049180380800b03c0c1c076008091715007410042400e220f80340c0140c81c0b0b0000c1050420494829030551448903003103030421703081210b640c200007030f2260641502c5032964120783c03c01c00130892100c01c10790702d0703e42d0740c1c00c01c0e00c0040c04100301040745911540034606440c0103020140680f00309481524009108030304034000c4011407494003c0c10a000b07442283c802042e26445503c01c2c2c40e190030b0104001e21b81c1c00c4040c40e4000c04d0307001c2290310070024403060038400804400c080725850700e040800b000301070003050b0492401099440000c02a5180c0c00c4c200a8126044140245454075031403e044068071300980c1c041e400c48440d410010420059a00034041403102d4881000201c80610800c0060f10003031391005d41c24031003440140042040c46602114014403402c1440c40c100c5008282030445160303030701c05d0311a41d54450401049c5070304003904406000a16000ca21044000140d0501d0700c0b82d803410107410000c0c03035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 834285161 1250 834283911 834283913
    0x1050a18090606060c0303060b040b040603240b0318060c0702011107170307030305060a0501090302090a150b090f01020a20060d020403060e160f051e040c0504140d0b0c07 75
    0x19800716600980164091042540754280501480440002100020700e171260002c0e0000f00e041c15242500d101800c054503091a1503002c402901c200d0201c4902c6078214180b51a412009010307070001021400407440e26860000201c012500a804280b0300c00d801480070401e017000c810341168032041e42400c1160f0001070f0590281c1c94001c0903001501d007003081c80c61800350701c480000a0000c0d50b129a40c10301050740e80790184071510f081071160300d020944000040c8014a0110381195000c0b003031580018203401682e200b82154084c81d48040100c43c1d002030385100c1424805140001410300380010910040c840d40c0b1b08000003880ca085514220200500d040c82d03a90380e104407400184602d9040d03455035180d040c040020f1050882e904c0031840740f400e11041042c0d003020150220b9070010701c501c140c285080c0c00d009410840040024001c4164400c9552640e524811a03085d145541d0340d003900c03242085500e502d042d20036849580719034030465044000844614a10f030740070300030501e025195601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 834286411 1250 834285161 834285209
    0x7020a02010c060b1005031005010e0306011203140d020a0f0c021806030f03030a0e0d110607050d0b21060106110307080a030b0d0b0405060601030c0e24070b04060b060301050a 77
    0x1003070031355079002d00c60340d1072403048650100140d8021000e210300040c1680d95000103490040e00501c4081c2c1540091b00100001d0881025030310b203103400b03414110a1200e21f141500071990121262502c076aa001c81c6200c0950740c040c5201090b811701e170503c0d541d03054140c1c00066000ae01c6e80c00c02a0400d000400040c404c0c0c5062240072702560008040700d4490a010002d000600304006850b01a8424405007075401880303100002210340b008401fa20035900c3c0c41d04102d61543c44005804000c6071900910031040d280d04c07112000d58105200320980441c1100d003002c2c00c048040e40441c0c100544202c0780c4400c980003108a030051548150754a40c4c0d00c0714490b080e000f801e8117000d000e0b44044c0c42100c203010f00050003002c6d44103911420030380d80d15954420040d41201d031031405190020f10803e98124042c01c1000b030480c4c1c003203010070400002c0301400c100658513500c02c2034210307002003150052100b04499802501441001218094110f40c10034011485403d082c1c480e8810745000d24a0f00ba0441203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 834287661 1250 834286411 834286421
    0x1050913050705030a060203010302330307142803020406020705010c02030111040e0415110909060f090c130812031b040f03080301140307140f030f072c07020a02010c06 74
    0x20060140c94050180d42486c0700250000d201c145d009001c1c0304400b0001711100141c1581d01d6480112840b0311189004601c2180d8200811260901c10084d02c041101e0400e200903051107402c101a0300484c0c400c1348491300d41a002c403805c1e14141030050100303011158010075900140c84081c82d00d108800d200340006409041d0300402d056404a0018002c50b100010448152156011f00000c1c2d03045071b1414585811100301c09824191008180301c82d407401e140c05043c03a50084401072400c00c4e0700390b2510000e07900d1002960b407005101c80001d00c00f80c0a01c41039003814018400328025040e5070b1043c1130259000c0c4002081c42111242507562003984480d880f06540142081c440b41501c00381d202d142c04c142c681e00071f004803202c11995100300101498001544025188040040b40c087c150b8602440300c0c03600541d00440d494015a03040300320000c003c0000e100106010341040c841075049282d50303482d03103158120b5940125031000800104070740024114000d26070a10384411145020304011000308 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 834288911 1250 834287661 834287669
    0x201210150f080d140405010905040f0f0c0905040b0d02060a05160807050d030609020c070302120316120e2704080708031603050603071a0f1207050703080a05010509130507 75
    0x114035070020400e0759000629544103075a40d100d03000280490040c150440c0910b228080c006400c3e440c040c0840e00b01030700000307401c0b143c41001080b80d0f1680150081a6a59400700070001400c000e07080003e0324040c00740c420a003c081e500101308124035008105584201c1d01840103118000642c1281c00602c00e9040040703a0708207003456180da2117803401c2601c0b080c01c0124a0300090a01d0400708214034039208940c125001d05000b0300303955184d5800c1c48284c455042440c19030307010a02c01245a9a259811022040d2142c020f40070600c1b43c03114041c08205110500500a10021160f60030b00310010603900c0740c4c401c03400d030000b102d0313134642c0b4080c0000c1c400c141d402441848048244100e455000f650324a2108040e101400b4035510402850b0b9150310034460100d030340240008951914000d68010020400000807072441c000910014540f80442500c102c00010800034822040c5a400000590003061014090080c1d5142c1800500c413440041d102481250114019504110003004410014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 834290161 1250 834288911 834288929
    0x180405120403120e04050105100c0804181b0206070f18090f0b010f020f1f020702040624051611010215010602010c0e060906040b070f0203030720121015 67
    0x202c1d22460300110009183c1018400b0a0390808802d01510303060162505a5002030480382d81000c00c410304440f10b421188043e01c9181e000c02010413990f55140e03012600d848500300c085800b0b40c115000190001c2090051002c542052003400500c0358032039038150521840340b411045011034860b4105000d030f0180e000d22451031601e0000001c0300c401da006043d101009813511800d180286406a880ba8449102500150000c1072500d07142c1000000601160b040107000505014059001c0307401c03a003040d04020001c1119010580c851000b000b03880c0410803c43c9809420300361b082010140001e0407941c01020a6030720100032119074403c001315034071142000c000104550303641030080d0080a0712040000050140c00314400b440c00c00c0f404542c9624005850680303891b142c0b50810400317400084086501c84184440076016a03000c0000e020624010301504c460001c0003007400225142500a081c0908041414031804550100342540140d03600c1e800450503605000c03a0103c2441d1642002c640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 834291411 1250 834290161 834290167
    0x307050f031305061302060307110f010e0604230705010e01110109030806010210060e0720071e080114060f0f19081203010e1923060901090b18040512 66
    0x10b048030301c000c0000150180c815541951250044120000d4503000c001e0b401c1182000441d440300d00c1205211000000c0e00141d48403010138030301681c00d65201450121455201005101c180056075184100803040100150441c10301401ca1980310010741c0f0030f15051050680701c2400e66406003150000c2400c44a0003000980c0c1e1a180292030310030151001401480303004108054a455841214180d40d60840c0c520380079a14010304460f20f44960100000340c10804a02e40510f1608004030700251004201d01c103503504102c0d00d002032400040c1c0c407154030f13170717041400c0c0c035840b2801a9a0941c2010301502c441044000c030788081000072850515440c4c128a002078034042c801c41007100d030b60544404d802600c03070401e808400200d03070303010078080d00c400e0303050440200d1401e200216107403003913140c040307404510110078074000d800d00360080b07841c0c60140316400c0400216107801e1805c035000d081e029070104143c1c455940800c0041940c0c49048843da40d134180440c00b030010400290640d0f1808100d0565 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 834292661 1250 834291411 834291421
    0x70f150c02010507030e03180a0807031a1e04060f02090a2c04031403060d0c090c0201061e0b0304020a090c020307060e1519110d0b030f0a03090b0307050f03 69
    0x2004000000345100103500e44400b25224510a01038020001c050340c1c0154209003034001650000c40707072442d4040d0300040000c00022040409d0045500550094007180f0600740140c03c0c0d9241c1a83c0100510303052100d60f218a000f40034070b248407541143c1c000d48002801081b040b01c1300300038403682c0c14841e486051782100080e05231207000112540d80c00d9141e58400c00304c104142c40303103814080c0c8004010880c04080d4039240906c0001a5500010050128030407251a482d090300341129500041c44031920b54ac40301d14003a409001c2c210062030204884021200c40828020394106207024031841001c2c00808241550f8a42c1d0002001e0101c0300390800ca044840c130400ba589a00501044800d6814001000225800481e602d03408100c4041c0c1c6e07145907610103240b070034400007190302440e9030350b500c0404d85108160704001d4400d001e80d019001442482c40c004042c58072210030402142e950100500c140080d51000462007240d214150140d200d40300c01c0f809884500820092001409021003084 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 834293911 1250 834292661 834292703
    0x5031c08130602130503190f02120c0402040e0414070602120f040b041e08010b060441030f2a18130b150312030603070b070b07140a020c06070f 63
    0x101100e00c03c074100d0703a1402840c60304000d5401f0440002e40041006035502000d4107198500101c001da8840c15100381c8009030000030b0417030b080307070300171a81e400031303030410401000b42c0c0c00031b0010880d100d180101340c918035080c80250340e80e060100700048298045001d0381101440c00c03d940180c0100030350301e42c4071611fa880c010b03400041d19110070881e200c500f20000c1e141c1018412000c560390082c00d901c1c50182000050311951500c6050540f414803102000600c0b68081e5840c00c90345165441c1c8413180c00c100340109441d200c048415680c50380c001ca080303045020f0403c09441c01c40b200414201d03420307a41010014403003000d00c0c0d413000304282d03012082169620a0441c0d0b54500c80c400e034a4495140c0781c00e030007001851041340c2c08a0b01903024040e42e06100074000040c42d13100d80010b0850b41c826841d01a0240240c211601c102d4180700745109014a0744c2e0000744a1103040503000c0894200103140c0c80080d920f00191138494020f82d00081d8510500601c0e4242d003140c0e131b400c0050b000503210510450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 834295161 1250 834293911 834293947
    0x9060a0e210c070b130b03061c050d0f090e061005130b090a090902061206060c0102040b0d05070e010816030b040c0c0201110606010e041505030a0308040c05031c08130602 75
    0x10071860060301e5003c00c8044220040e070380850142d80d6a0205c40f82030007084207407540050011580f0800c050012403a11071080e819082d034034490f0010700309029401401401d41c00e02c2e08800b0007070000400c4140424011a020964031030f100721480f083c03012007181c09803103c1c032440d01d288140404c13600c0081003040300300c0014091407000741d40500b803060385d40d2025000c80d401c0308002540f0100800011510200c0103a581d0340010008003018540059050b15500726807099005010441c804600d84003c00c0342031064603840303035041c140492400011000200880030050514141c81000492502450f200c3d6000881014019004106e18001c01c04007908240e0750300022400034620510200c1c1e0070f480400d0135802150103844880c2005050002c20000c0c00c3c3e04040c11a106800c00ca00040c1ca540c200805403c150180d2503407281410503040c409a1082260055406603220410325071000442c0303903c03110440020b06d0520520384802602107001c6111080c064a420f001203083d040003000e003464 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 834296411 1250 834295161 834295177
    0x706020904020f0c0618062412030d061806030c03020d05030405030718053105160e0405071202100c021207061805040e0c190314010203041a09060a0e21 67
    0x7410f025500450440390f0b481f1030854480b0564110790381155210306008819294041700149080c007441020001545160004441c0721441a01e40070101f26142d000d440221010b41d094006110b00703030860b1202c01d000c2c0c40c0e031710009008864a03139542043c860203005803000303888000e0994491b956181c0360400000e851100d1440506d2801c0082800780150844004001c0c41111104003003566414001846440c44201502c1c0c1d4050700441104030304040441c80f02822165814107407500302410094501080c5030082c3c4000c02d603619400380544d075031200502041c0030070303c2c000342c0020b80740c80030922060b80c900c019443c902c40c00d140030407143e4101d0288800e240d05868100b0419135036000b0081903030207100091005420000c580008d5080c920749c14040c0d0000080000324030b030b0380cbe556198120418461640400e035404001e02003000203d511004000c840e90b40c0c00d107410f08101c0b285546030800548568051540c034540d614040b4002d0041260b0510060811f1007003c8420701c8180b86039004d040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 834297661 1250 834296411 834296431
    0x504080a0e01110c060a050705010e0313170c04110706090f06230402040e0c0306010f0e010f0e0a0b0102010f0c050405121c08060112020a030b010e150706020904020f0c06 75
    0x511425154450360040f150441844020540150704038184511382d40410a89000c01004111680102c4d60074001d040d040100100219134403048001c80c85c0001e1620b4000d601c0102d40541c0360f074500500007940c002c02003401c440001c2c008100d5400004140324076400241801d0902220310207011850b00302c5401c040c060078051010080c0038890200030440e09440d503103206100c10115000d41851340c0507403185000072048803103d0f08034a00003440d250702684640b01070412044140725141001c5945401080c0c120a418040c41c1810302042e001c1c90020500020315541d13400d14a030aa10075000115420081141004118007200c0c0041031607005015040c0109501c003881b07a0409030000c1c202840086407104010305d070001c40d07802c07944600301410142c1041001e850a40b0070a066100501e0310070269107001551014000c005000d00e140d41800e41e01c0350282108086401c4036900131500b4041c0c0c00280165100d106d5000200240a40c443d141012440810603641103100018000d001d52a044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 834298911 1250 834297661 834297677
    0x3001080303070305150a090203091011031f120201030b04060e0a0207020a08070b0306090702010b060f07061803020705040e010212360714030a020306070f0e030a0b0c0a120504080a 79
    0x90300649417140c0c00103a01c0d40009600c1c41c1041200b055502958100308400d00360784420282c0c29049054400c1d000304500340c2e401c00002e209000701b0a031000041e80e0350140d44580f01da441c00050000307400e01e00c040681407685035254420309a039150f2242010740030b2010f18034000d040540b4644000c6d00034000803400b440105002003291100050804102c2d0300d64247c044c650b45d40c0708240807083e0806000e04082d9901c03501c000e01640e981c0d002411400c400c5216807500d52083c4d080504c00c0d540400742000901592403800c03030120f603021400f0400c2d42c1080d1800700309010500d450900a02c213103209041902d011074148243c1c6001040101022220b04020f0252044104804140b6005644800c01503901483c403c001d00d030f08840c0c1000e1550402000c1d43c02d0801d00d500440d00b03001040303c482000601d80c9080b4a25130f5000074480f9016030068004141050b07641d65004c045000140c41002e00101c04200225070910490070280c0703904d0280002d1196042a14140a90f600041240408600c0803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 834300161 1250 834298911 834298921
    0x41a0711010606021c0e0d1403040308070605070909090506041407050303040906030b0c0322081603110f0c0312160f0b060a1d13020114070b04021507083001080303070305 75
    0x6aa1443c0c2a1b00000c04020303403901c0540d1041c01e01b5020004441c1c03503000502000022031211000343c08000e01840e0301044038908418001d1110310035401240043c2c0c03410b00b0310808210006401c541c41580103100c0d802d9642d031100d02030b00d010900e80c0b281b6818030000501040c40c1c1426040001200c1c0300d10006103950b2141124903140340070441e522500703000d840d00081140e41205031400d50081c003507442e00d0702d0070300092802800b0009600307054002c03840403090302d03c4188041103c01001003a0801500180c4004030000762284130b0720b160082e0207140442c001d29180d13070fa03a402e90740442c2d1007030881703105803264540b40039055022100b41b48962042c420008102d0429510b40030f03403d0382910040259607032100000711180c8009400c1c1e0401418500f090541d030034200c010b0029038080c1032100344925140c410071403419001950850500000d00204000600503000e81c0c0d48000c01030300ca05202c41603011000f4030320003903081425102c00340d01d000291401c1e001c00110b008181c60765040c000c50b594 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 834301411 1250 834300161 834300167
    0xa0b0702011e0c050d051320060f0d14040525120201030c0309020a141201020a1e11011e0c030e03091c140607020d08041a0711010606021c 61
    0x40708000191000101c0c0c9100b1010302d0941c40310b030081c0640c0c18198200070724000d51000b101c1c4112400300f4080300400d05071080c018100207a03280c08044191031001c070041e41011505900070010380300740c1c103c00450310200b6601107412840d000c99290544c02e107030f40b92034180743c1d9403400304403214490b2290400801415141c0c44029009851480d0300c4900a203c46130b004400800c5010944010554ac4055103130060b80c4071090100100380d0354180160085102c020001c0161901d41c041890341e104004c1e170f074085504141c0c03840c805901c41255818a29459005885c100c500030560910f1794a48080d0410180a4952040402c3c0c001c1000300000c80c2240c00585c1116405207615403240d1042c000c9007440d140110194555139164502c45002c6c0e801503841e4407c00c12102a81c00c01c3d900100304010096504100c200d40d1181c90f40751402c4641425214220b8040d40010b04050312010714000035007842c052a1000402c00c1698000c201041d07646000a40394144c40101c02e07604031143d0700328106588 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 834302661 1250 834301411 834301421
    0x12020c01020d0b282d080708011404020913021309050114060102150c0a050c07120515040807030509120f060907120314070c0f0e19060608150a05120a0b070201 70
    0x740c50a101551a41070801c5000c05c1400c81c071050103264942c80b0191044410381c191803000f090b164008041040c00c080980707013520000c0003d0100c0811020410002d6a540f1003140e42018040f40740f04800316090004c900b0340464803030000841401d00801008008055224294804186080b82d86c19103584004980340c048081102003000201c0020030055181100105810421402c209160000513000107060004079445200e02228002c00c1c481805401d100d030a042445009101c006841d003980c1301c0d41c1074095054040c007002000b01350b1018903180c000c00000300500b1641120801001d42000a42d5420b084071b030120a80a9010006022004482802d0348039502da1a5840b815176040e0014a060b0002c803c1610182102440041d000e9100ca146d03902407c0400ca0185c0d41d85000c01440da0a01d040381d44d41003625140200400403e5488099641c104000180d00124403603c4070000b618050181c02055000609540c8200386000002c5e400c0c40c268424001c50003191354046041e4201c42c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 834303911 1250 834302661 834302719
    0x12020303030a27030c0b0105040209030703030302070503090a0806090c090c0d18020a0b0301060f0507031707121a0312071e03020a050607050d151512020c01020d0b 72
    0x150050001c5821070b030543d040b0620400054420304070714002c04490000003484980260042040f140b5402d0910051200142c00341200352000c2d480d00004a000c41da07901d100e4031003e41003503130100300601000800d00c00c6405216000301003100007a15518100d44404095481690a00c0740c3c0e2008106401d10001c914482d05d40d80c503009040c003014054a40c003801e00c00380041404010007080070b00594500030403130060004101d03220f4403503050207405041d80410b580354006004007404171000182e40400840c443c0b0082c0c4008103140c0d103580500752074818807805000406070800c0c40e00403820340c1050b2001d421010450403910035010044440140b881088000f5108a1412540c143c8804841c2840004103210307104495400c0690341700c0c00d044c06c1c81580c0d94400104000341e0b0044074030ba20f0180541c0740001d50031400c1080e14101c00b96203020071400c080b0003881040202d000da291042d9054541c2c0c055500300035503540900000c502e0080450b40d1481e07126071255085403940d4103030009204607035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 834305161 1250 834303911 834303913
    0x3060c1710050d0c172109090a1a030f0c0103152426100608190b1903110111060103030914060d140702100b0f15160308010f120203 58
    0x4904007010300443c1c0340e5252050342c44000600300010048070703040740c0d006140c0440f006040301002c40b0752500b0700359910002d940d02c0c031b4800303000d420b445903540408030f0703003100b4242e800044443d101e1a4414100300c001040c2036240c0203085d01c09240c1040420403107403000017660104201c2c00e0b0314a00d0310103902640a1010b103d110391240c10720b260012290680c0441c05420506600385051001c40800c101c0041c1034080010082c00344514541c200d5030b104090001c5081c0440d45140108080c40b5400c29400030008150316080303014075940725a0520142080300710801142c041d01c90410002008070200d8541c000b542d50110b0340c01c980400314455068039416038800f03641a10384003041d4404003129046e207600403000c003c5d900981c6114800c0305460900284010040e18040f1406424207448090b03440c94142030200e141c12640c0d40b41c0719030750012000c80300c10643c038281c81680b84140c05140f0b042c80000354030354021424160005803460480d0403081e042c0e141c007500c1d01e0000130b8001180e00c0082d05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 834306411 1250 834305161 834305191
    0x504020f0403060e031b0a0b0a1a090411151206010302070b072303070206060103050601020c0f01053016140a120902040f0207050606040501050607080c0309060403060c17 75
    0x94020380003d00c00404150441b410225144140314824032100030000c003660142004a0802031204482507003d004624108034003440141d15190703940d0883c070107600c100c90700340018041102010000400304001342c005030200c00002001106580b02e010704a01900c12207001404540c420700840300d03040e0b406044103200b0744035628142e52482c03c0083c14494020705601d9608030540c810040d5109242980c0107001504007100003408480313010306a5811500120b6070009151034041b030070b00a2a400703103840d075900c031801c0d45101800142c904001c444d102c6082039140520005019040c005c2020030111810200101c0007512191206150001d1008041c040031400c2400781159881100e100c580100d21005150700003012107090340301005e102907011500c0410710500300091540610107803400c02265051000280729405000001440c3c4580040d800030341c06801d109468580c1c4029208a48507500c1e4508840900f4a04290348000354a8220380c80400751203040b80313400b5a40843e02004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 834307661 1250 834306411 834306413
    0xc010615021c030e120a080a09081c0f15080616120902010203130f180e030d0b0a030605010e18010c090b0c190b011401050304030e0402090d081309060504020f0403 72
    0x7040c0108000710303040c1a62440c03013602c11803052189078a40750b00d40180d55900e201040c00600360032030241610000b1894613502100041c10341d070407100100c00600d40f00344800e00285c0c010000e401e03400f007810031160410f0307070219a4044d41c0303a100d401e0751808c0080e90420b0f034414601841544541c5603420004d1561403015181700302c5907020362101d42c010300c1924130309075441039107444000c81c0764406002c48690403002c010600900038129003e021480081c030101c20000031066032809071401e00c2c56041e580c2c0d054048581d90341c40b004c00055601c03039404d0010703617520207a400c0540d004403250105040c90500441c2d4500c018420420360545c0d076200c0031403ca00704007a00c200c9402c060200c02c00c40c03103150101000d60f1114600482030340e00c00e588461403903052020841070700302800e1070207041c0300c018828400080e4128035002107900b800da8005865070305d0f010005140c800c202138044c109480010f041000b41c1d84034000b20050311381004003808450340da401801b00324412040c00f41d1030040e007880140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 834308911 1250 834307661 834307693
    0x105010c020a090c1e0306050a230312070213050708270f06011409060918160303180f12080d0b03070b182209050a12050c01061502 58
    0x2109180058510b030201501e810400301118111035202c0c01040300840542e14150344490702c00c00c00c56440c80c0520519281c82d011640414440c000c040c403c2a904491f5015900460485011508020201d0f80d1203000245030f10310350f902c1550160b000305009516005482a14040c0900444907551000c0c8107550b490420981001d00c1034060724075894a19070098404010840c2455122076200608910f501d031107450840c1c43c0000c1030050140743c591080042c190340788405c4070780c0130545203c1114240c07142c21041c1c0c10407a032000510004410700c2c1010060661141018201126512841c40c19640366003000481ca442c600c01d858401224000c000300080242d409020a0348031903202040920090001900340b134130582000d170361403202003580e6640444582982c184da000543d0b061508010032080c650f0380c01b2a1640f0300c506079485034195020450100700300141642c000d04c0760840001900d000408981c044407030f0140e250700701a0b0110b41c240070400d0701100030170307140c0080035800910036800b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 834310161 1250 834308911 834308927
    0x1d09010e04030c0b100501080a090c0515190509120105150d020a1a09090a050c07080c0a0f081305040b060703030c090f06090312021f110706090807050c060c06010501 73
    0x480070070100303d81600028142e10003180c0185840448020b40a0405000404a40d4018111b481850030a0309200210b41800c441c10290742007034074280c018160880d03040c50240b043d243c0001303485605075407902440d0742c0500074215400c000c461202c60054500440ba0036500f0a8408010102044441041ca4941a1800241700348007500040b400b0b513036000c03004000d0000a40c9809180000643e100b11458144525075021380301610412150030042441e000c0c40c050410000c2040800040480e02c3c0d044c2040852185075010360000e2100c12103240480454100c3c40b00e001703103820381c2d80c804039640c80c140c0101c20381010041c10060a185e81030310101d0240c0054806281401124400490b100c00c04604281c043d058035101e600351145149801101c0e64480b003222821904186405000050340c40074004d03425100c0701003c2032020032211991028424610000e00803442e0003140c10030014124040c0c59600e010f80305840c1d440200a0030700c000f03840744041c2005580c10100042c03160f58003903031207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 834311411 1250 834310161 834310163
    0xc030d03020a0909060e0a05070203040f051302040b0d0c1101140c0d09050f1c090b120405070506040807030c120b01030b100e1f05030f030a1d0d0b04031d09010e04 72
    0x340c4070783e82ea03d0702100222001c680114002d50b24001c1001791914090041c41c0e000b00045c40154507192401c071000c0d9848040d4040c003440344200e1000518044929010799015010100d80c00e50383d003004114140051a00c424010041002e0b02d4420303400460603c0350f04001140b210304021241c2c1e039104a041240d001c2e10350800749595400000b00450010089036010742c0c410401480f0b000307504600c0700105d560b0150654208100280180100c2c40241d003a0b54001008504104c21615586452070800d4959000340390000004900040e010a00143c40002c8034024030444658980b0b0700d824a042807020030001e000d60480384010030025125070a11030b4400f420b90310a4501a07103034034080c81910400d484240c00d000e50b02c81250070403002d80e03440b40e00914040f401860901461002e00b41c403400740720000743c24032500c401d100800c0107003001048a8520014080404da0125281c00c1e01c0c41081610705800080e0300e810507649334101188440e110000040c5420340681c81e140700c50f00c003c0c100401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 834312661 1250 834311411 834311417
    0x1e110d090204060b0309032205010f0e01090e1e0903090306040213090606060e04050a2a0c1520040b120c0904050114120c06070f03090e0405070e090c030d03020a 71
    0x151103a012006540101e01c880d01443d40c6a4401a4011003590300234207a150b802c081d09030420603a03030444030145d402d0705181800c00311048034a00507900c0d1100d42e40440f18201520040061208004501045a40d19101505041d4843c03101c0c840d40d9004000c0099007540c0180d0200340903191440c0360500080820740c0c04542161241d8904c02520020741c40500401c01c0810900210310b054060b41d640b0459603a000c00c44000000040c5d86204d180321103614000441800002c4405e10450181c514250404a9140300d5105058003000400006400c0c10502c0d10130b00c5032080080b4401c2c1100c00b100c2400442c030b41072641ca40718004012030041d100800000042003001065103031401118000c0c18100e81440400c25503006105100d055501d90152a030000b010404803592220190703540316400c854040c19582d05443c1c2a10384000b035800c402e5501504030200300404c100040d0b40020b07640150303903540487d1202c40d441603484107403c02e000d506801c1000b0581e05203100e40d01420911a25107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 834313911 1250 834312661 834312671
    0x11a160b10090c030b1f080c030a1d030a0908070b07120302090324070c0c0b0a0903050f1b0105070302031c0b060d0e01061a0f0a020a08030a1e110d090204 68
    0x104060040780c0010a48078081380d01c90040c00c0481c50001c91400c40c00d2540d503022042220790810003400201c4c001e045509000c004000310305140040d61007406004c10480411040c0c0448520503a40d075000301d1980390025140300d00c08640d820b00414404102c41a8044013400c001003540c92540384c0c0300703448200302050741c2800b1000c9030703640802c0b12500244600e14558289004c1803c02e0600c550010100c1e82070052064a810003d000703035039032004031001c800080d9281d4038404021a2480c8aa50016040b849104004400c41002090941c400d801100411221010384c1d8015942401000805030141c1c00600c000d60504c2c0d8a50f0a2407045603038010001404100d4200040640d046071b241340c9041076a0b90b20420600a00744941805070030030086038000c00480490307052191195100d01410b500001c5460720200340200f21100c50203034402c0c00907880340740081d811001400d02c036600c0724640c9030004203480046018071895a4550500710168036115828048070042d020221040381c101d41c1e60303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 834315161 1250 834313911 834313919
    0x3040203151e010602010e0309010c02041b180501080105130504020301060e0c1b07030c030305211302010807170a0c050c07080c01110309060702011b020d0308011a160b10 75
    0x80c44040d01c03846180340d69201220100075008407542c016000101507a1410201200f2421300000352600340e002440d20717a030b00d814a031000c0341c064510710914409200041ca402c4444580151604034608017200d405111607035550300450740c243c03082c85420740000c4000d120984c19030990300201d510a00107000030a16640c2d41c0440060098220751303c41c1105030103e4a685400c900b4119031200041d10001440c401d030442d159203400300000d200060601c00000313044440e50642d00c26a0004401000000e11185003050080a11034130004040340040e10030300c0040d050074011642d40c100841d460389411480d0340c906e0406d0004110a107848801d009050140c030350103c00422024000e0302990000d048281411800500150f04204807507109800510444c00f0603241d00d01170390f031001d0302440d140001d10b0800021031208224a0301c0039400069000c0130406160304070741a0f904a8517083d841a1242032040f000400600441c0612411a544205540d0110300311100a540100030032000c22280d941d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 834316411 1250 834315161 834315193
    0x3080c01090c170f0a150504170d0605040501090203070c500304060f08061309030f090b0c0a02151303210311191202040f03021e0d060203040203 64
    0x42d0f41e0200e4200f540b5984489942d0b00c0c20f000c264400d0300a000240980c505a90714492a130490954004045a0324000113040c40751005c0785c801c070300c0c041d88038069a90614000700b0010704494006c2e03e00850a040c00060741c828a84200c9100f0207482c0d440030348904040e910342c0c2c1d0001100040ca1096000c91421079181c078443c4041d100d003112118602c250b41040f0412a4080e25070366050a2926082070208014464000701d89039004000f40c83c251640c0d0303607440c0009d5a5401c03030600440c485464084110b04254120310518000a0182c4a903810141d0740c0070400c480f0310401329a8440750300024016001810034203260592540905402c604210408508005106a6510941d00702d26141e44280c85840024080c4030700600170b240a108180240010000c103104109000303117601b9860104250b000d01c0f034104603807480205031003903680715643c6030020805400781c0000e908c40d414516880d001c104002d02a17010041c0301a1980242d54138686401c03000f5003000f4003d0341c040c024075132007141c0821 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 834317661 1250 834316411 834316433
    0x127060c180f080106050103020c0a080703021504030512090303071202481b010804030c080406031a0a03050c09070e030703080403050c0307050102121e0a02030924030103080c0109 79
    0x100c084001c0b5041890489241c0c25580c1a42c40700381418030402662400d1480481c5012865422154041d0784030382900d8202d14194040340d10303010b0710310782e9030510082542c024000c013501c003603d000426413a01c1e91500b01783c492000b0b0307603080301240030300c42c0400764140e064002c1e081008416028001102001c00a0101c0000401680407d5690124034561048031200424000d0300014004d014000080394400c40744902c120381c081c180101c80c400102058805c09035005c9450744060b407151942c2da24030014020740200c50741d00c85201c03820428502c03641000401c1600312a044030080203d18005418040c1e20070b0042d1110301000000c460004003900c0030420300d4000e5200d42442d550310351540c00c00b5420403940c40c240c00d100e41c11140d000c02107070380c0c0052400e48020780078641603a250001425034000d81b0328400c002c4250b0402148410b1040c2e00032001d04004402070b60070ba441e40c0b00c02142280d1103400005040482c440038401800403c1c85000940b84200e002c000010301c1810f0742d19a0040d0301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 834318911 1250 834317661 834317669
    0x9030504080706181a03040b13050f012903210408010615030f09051507030f0f0902010905030a08030a0c09030f0501090c0506040503150402011e0f020127060c18 71
    0x2482c8550f4104c0b0314603aa0161030040420a80708032411810360802250340c880508060406486240030400c500d00261a15410075403100c1100e2288501d046a40e004e4110000c80844030211003200c1407000100b50004030490300020003812451b010345400740c02142d042500a101030700107101c040f40500c3c0074820300001c0d010884003042d60040d0480f005051740c02070640c8901c09400e01050900043c7c0018443c101640ca00d482e07a640c40c0e50340c100440040114504075a290303801c00080038802d421503840480514002c3c1d0302c00404a4581c0e0506070b0300c0c80e040c4401050008104002001e5240303070791200f444414a032915800c0e169494641010501d000340d020b95460759910052010070552080201c000c140980d4081d003031910701800a507c504410010301c0305940018001400c41e0710034054081701045101c105980781007031074401403002041c040d00717030050f40c80c0c544142c003ca18145045044040c0c0150507641b000502c1c1d03500310240000c60f020909008181c1d9595402042003168007010f8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 834320161 1250 834318911 834318917
    0x3070203060a1a060c06100b19080c0d09060504050f060405060103140309040c0e040b1212071407081e03090a06180e0a0e01060b0a4a010e0a0501021009030504080706 73
    0x241000c142d001c41240c0548d020420484c010803080701960320028600500d4070a50410250700d55070b085054006100b1070703585000392490844000c04100c199449140214058402c032070540d801c40c42680c0e0740b0304007502c001c1d00d960700241c01000000d00e0b58280780080d030110016281400c04440100d4113986100c4580000710304441a00d050320b00701445400281b8008891990703103136008034206500c85a510103d01c40e511070008440044c4580405d07040364910031002260500b503501c0111648800201c2401c06420f0350744200d0350000354000050381c840d0480245030700b011900c0e1090643c2c0380f0442a080c40d01441e84e0060018803050460b080600c103580c018030115902c0c0464400300d084440e95080264504002e01ca0b13442566400f108030200c10124000902c04416454082060702055041c0302e1001607a641000490a20003810030b10401c0c804e0300c5418484030800d0400034840e03058011140141e001c105548883d14a581150821074020300f055403406071a442c0b00ca00f052000c2d0800d1000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 834321411 1250 834320161 834320173
    0xc151003081b031204020f030a02061804020c03070303050402090c030c09010c031710150801031110051303050d11011803030203151e0a0f0e011e1203080f0903070203060a1a060c 78
    0x2503041c4482c0c0c5000385003084000e0107484102e40e000031840c1c00ce40d8440c9400b0704a95100c00c01503150707a411110400c0c460000c8a482c0c0340e4030314005024000440e030480c0140c0030040858000000c0340305890281051040d41d60414503103400441d03072040c0c055401c2e41048280c80c1e561141911036090940139a0380c005040301c00d60b0520094507611242c2c89600c108000d4080010001b103410445504140c0b8011100742500d0805203008607058000c03001c8100001303940c044004100600020300c0c1a0002843d1101030040b0b002d00c182c142203480f542f900d08a02d5105506000000303110350700541d409000852100100c500711400700703840111014801110f840e840090703800c240f8001c00c0c800d008003804030b152041103051840442c525070040c401c503021038200c0b481810404001b007800c000500b00c2049182606142c50070010704410b419510b840201d43da0001142c1840400b000b00c0c0d04941c0c001e40103013541d4a98205110040128a0703001c244100d9002c40710355243d58000080240ca0103440042403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 834322661 1250 834321411 834321413
    0x3004060c0e0d02010503011205030403050f070501140408030315060d0e010501140405070f0c080f0a121a0d1506091103100501031a0d110402030c0c151003081b031204 73
    0x10a4960600d0814410b0000e10032810060383e01c0001c40381501d844840840e01000c00d071038010700d18041d68200519034080d424114101060004411044807001d0383c466600050101e1911024442e80c040d1901b503401c1000000c000a60b107005181b4406000f800c07403407420070140072136000c6500c01903080c0141d0f5140c01c010051705010841e10701c010701c0100d13804c008604050314054001c03048002c0c4e0308180000800d250782441041001d44c0c4a0303800454942c0c0c0c0d245030540004008101c280780c031941302450414031089418181140a50046c0041d2140000c6e0809485030205240c400100004043d2120340218280711f0b40c3c01086002d0f4181440991281001501c90400386950b8025504062400c41003201340412103040d40107890003030b20311184885540c14145043e044200302d582d0400e0000060010b2580e4020003400008049011346405102c6041110a000400e59000a0381d045203d000d10110341500014801002c41502e500c070490681200d1905542114803101890402d80c41000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 834323911 1250 834322661 834322667
    0xa0510020a03150b04030b090a060f06080609011406060c120a03051014061e070b04080306030706030e07030201050a020709050c1c092d150c0f02070b3004060c 70
    0xb030083c40075684441009828003c2c0c0e8881c0d405203100141100c0302035004581090001d00c4004078160b0017042c1440007001e62640c0101500302886015aa44160310001e0011401882802c403c610745200c61080b54031810104241c0382c0140400400c41c0c05406551044414010020300070024030b5240405c0038904200036015041481c4d00c100c0044116082d11030f590303030f5003c04403010045c01003210328402a10300c0e43d0002900410701c0040051a280003804148400c20700510310403042102101c0c20161074030b00490540b00c01c1a6480c41c15402444203000560280c0301401d0809290700c100e6626554401001058440035554400d8100e0009096150442c05160b1196107201c100343c14088a5141d50380c2510510100d6142062040144501c903403d130041d608802c2e0035a0044415590142e00c06a41c0005003c0d0900d0303a03000c00c80c1e03010100d1626001050b070804495201d001142890310340544440c0211910069038061003402d010b003c102a10785440a0055000381d0000a203000348810107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 834325161 1250 834323911 834323921
    0xf4d28030c06030b0a080d0309030306030209040302101820030a1704090c050901051b1c0e04050709051c0303140c0a020c0405010f12050a05240708010e0c03090a0510020a03 76
    0x11078021140f8174020b019511000901800c01d4116240000305505a800d040b0300401150304025401001c0005000c20b0590000c8d03403000d504042c1100300300c003a011150081c15480c5110303004050840d40c1810000d58000240c0c0900c0d806000f0b002d640da810b18550761581ca90020006a14500002280074030000c207580c4601380d4070030b4a82c00c026150008910010744680a800039003580806120010220b64009010300d00410421840401143c0750801000c0c1880240a0050f401146020001290580705d00c1c19102203603005401d103103514208440720310b40ca00304800141c09060b01d4405c003141c104820307030f0750501c5022078001c1c4980b507050444000342402101003eaa11507405c1c1070060044880032081c1a08454620011083e1240703186410b81c2040150a001740484c0540c041907100c14200d8940600320f0051807820074099543c009058400100a020f40d2004000d0f100000d00c0141d40c0348021600600c9090440310300000075a50365142c0b40300701380c12840480e00030605500c071507018011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 834326411 1250 834325161 834325181
    0x15181e04020c160f0f050d0201030b10020703020111150c0a020106050306100503061e0c0a0c170301150815010e012007140102280f4d28030c0603 64
    0x213114040345030036084004074080d0b00031248a10f06c1511520110380c000d43c001114850060a10b516407655040003a44401d1284800e0380030650260f100e003181c0c0404200301256021015120342c040e1184d08000da1a03030410490030007990b60725600450659802c1084c90300c03607208011001c2031035040000349414043c01525079801c180c001099600108500c3d02c890340e204004140b048c0c0c640205510490703040180c41c8000c1c0221b0f0003015000d48491030040154181c13459903049407285c60780349008440031942103501040c1c807422617203008483d40c401d108600201005150071890034502ca09c8511103004010394419440e80703c56000c20117200410401d0712513400034009044988802c18080951103112000205c4100194030350500700150981440c50f031541212002c15000c0c5003251009107000217103160b008890004070750408100300d1071000a000304d118181e82c60708825001c18890310100140c800c804920700b46c800301c40640903042c2e043e8001c5000e8544d100c241858900c0c050100e070346200d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 834327661 1250 834326411 834326429
    0xa140c030d14040b0c0f0d1418060405060703200c06060108090705030304090f1508150115120c020c3705150906090409050c15181e04020c16 62
    0x70403022482402840c0e900500d58210603607a41c000701140d0f0a1842050b480b50003191908507030340c821211142016100301c10800c856270b05e4202c1042d40c50f94640d02142c000b88190310050000c6e1485110740c100c8000c4200c09006004101d0010305840f0b611341011030103d00a9021808100700c070340c0d10915031074000503040050080c80c4c0c1440701180d2284194022410110f40b00c1c0804c0c521090071741d220729001e0340c0c00e80f60b11403030f6900d035403078140c41d84465806002c04088040000c500c1d080d07480a10001d13652903440e00d8101c1590520150041d10000c0550015030082240b544199181c0d0308282c0d8074a042c0c3c3c00d1104480c440750f501a80b51610045043c41d60b48040042480a900c0b058698907030400c000c0b00c00342e1a030000c6030000c6c11921600b9000c0c0c1e04913082440c1c1004018001480001c3c1180460f224005941004120195402031498103400340e101c0d001101c1c8281088450101c2085488461414001c8120b000c107007683e20800b4500c00a03800856a0844500340302c1c59400500701b825 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 834328911 1250 834327661 834327701
    0x90b010509010b0f0c07080d050a030c021612050c031009051005150622030f0506060907020705040207030e04090c081b030a0b060316030b15040912050a140c030d 71
    0xf0441e02c41c0381c000e00150400c00e40c40051251a251410006040204203a00466010181d80745c2c005026810000166002c60704000700002e94900108103540c0700040302c4101c014491408004810341e1854100546d600c0c0600b1014482030380b4280204210300c40420030100384024070b85002ca140c03004000d01b0b250464038040c24401030512544075141c5002c0304440704c03a1915060320700c2540001802c40c4c44a49070101100000400158510181c8004c0c050802c0c0c40182d80da5078140003e04504541c40801a001214148520b10300350b03000c0c1040c80c1c002d14050910500b800c0c082000c0b641d6198050300c001c00c3d401030804c05c807a020000303055001c003800d0300c402d20f01c0054400b0075038400705068002d1108000e0000221140c07010070104241052103040040403903941d00b454148250192442d0044601e003d1098800b81414090308900ca0f41c81815200c282441c86000c47c1e607600184416410400b00b220240c010307940100c0581001c1c03840c40044e503901c00314010002c048400040ba840c0d0040c00352 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 834330161 1250 834328911 834328919
    0x7110d090617060a0e09071d04021e03060c0307050f030108010e0d3f18020a3602070f08030f0a0e0d120b0a0906080f03070c12060618090b01050901 65
    0x1113500780b01103603034018401600d0345402c10713151f08200030307608090214601104440b039001d032004001ca0080d402582c841c80b01d040000b066007410703203464034040d800d0b5000b440400d1040348104000c540c4010340d480c11906116001d201034005600a03130120410344c0d120a0307040c078180d20030f0103150400c15240c2081c001c0703803202c1011940741100c5c890070302e421800c0c0b5800f01c0c06080744584040c0380e21348a0020800400501c0030508241400c00d84c0140e00030420124042080f440311044072441c0580207032644030310506000001000980d25005010030f680900403200012289205000c14600c200e0f400d68481c85e007450403110b40e94000300018032060a14900c07541100d0301050300ba0080c075041c0340009100e00c40403401e5010f00000c16016030494904c0000082d4186590300c0b840507a1111030581b00e55000ea10300746566809040006000d04000402c00c00a1011000c103141e000d034417035000419032540d206142004450702111000b0740f1501c40305400c04200762010003c0c09800100c5000d4419410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 834331411 1250 834330161 834330169
    0x3020f060c12070c060b100507050f0d1b0f02090412030b040c05180409021201020d0605041406100c15050f180601060c0602040f0305010e0d0c11010807110d09061706 73
    0x1400c8203040c4940d690184d0f040c4070701c81d003249242100c0a00b11503c506400310740281543e10083d0705448038019600c3c22900380c8004910341c0c180741c145030340d4212103030f460600314114000c0c01c8004403080f4031841c181000603140c50b1092449540950030408101c031003501e014050741c0c5040e6443e80718501d004c2d000010340781c1210079245114510700e5441520f10202c004030b40241100c0b500a0341c0081043c44a0f484003905400800801030715a0049c003026540340c0078041030321032030910401e80c40c000800160ba1414813910440c03810710b040c0b420700007268154650000c0e104a810040000c0750f110010030141c2455007100b541c000740c4907200440d1a050303c00789141c94213810302402040008000611013031042a40640c6c0180800c80502d500fa1940ca1905500812940300510100d00842c3e41c0c4107a500d0180c94094802c94018050a8051108200443d40041d0040c00c41d010b0141550b404191450700704140303401c0064a80310b000f8400d0400300050000e9030b00d00d4a00003a030340310f0410000399882e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 834332661 1250 834331411 834331447
    0xc1208070503180f120901020d0509090408130b0c030706110306010206150a0f08011b170703112a060603030a021e2802040b091611010e010903020f060c 67
    0x2211483d000c040c00d002d84035003410240c004404910612401c0703803403000710205500800c0402c100340c085038214200d010007030301e10780103c030011680075141c0000a00032031010300c010321407003000c104101c0001e610703408250300fa500300c440d54441035840442d40c1d0041054038428254420007080320b440c1507240c0400003d507154030061010142d02d40c003401440c3c1c1038580c841882c0107000c05544003a401501c80c04004e000380f401c601c40c1d52070028001030034030442e80182c0180f1034411041740300c0c6510303a0310346030305501a1409054061601c1d2040113208425021021030400e0072480c0d0008020b8005080c007c0d41c40c1c80005080f03030b4881d030000c100b0322020715000038081591500e41590081c8020104144509011142d16a0f59003101d90040041c1d59001615040d0451442200c1c1000719104040c00d004e5103020407640a030011000404250540e40500300c124903200c000303000442c440c11000151400c0d00c481d040201c001d0b907c0061202c10070003061181c0b55204c040f01014034148160083c040010030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 834333911 1250 834332661 834332671
    0x150e06070303090203070807060203031f03030507080c0a08030a0209011205091513050105010611010f06060e130902120714040c0e0d1a27060105100e0a0f060c1208070503 75
    0x1a40d908512007152003d1003e000103200c500288c4152542c0c0e0000a5201e50086800840214487c600d0200b030851440740002a80d4159075820306290172651542515413000320b01c24990301c20b03c131a0000140c0c42d000290720a1600d0a400f584400081001404409400203502039403808c0c5030400c00003603000191080480204010301d03003907403242c42416aa2007501343d80030741075500f0304001241c43c03034000001c1c59110314030000070444680001100c904a600318080c1c000007420304442902d0a2030010801c010a4551900000308004903074005000700826280320403907a0010300d403c000c1d054402c0741000d4aa0410744003404800c078070420040500d04600c113411b228520403400300080c0056100f039010b0049042040c3c0401e410007440451542c804558041040c8070701c02d801042040000c990903048401c06480075042c02d21460b030035a000d51000c0c1c909a00110503040008804101204000090203151151018280b1904000b00440314005034601800030610901205561000499600c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 834335161 1250 834333911 834333917
    0x3150612090809030a0602030601020615010807081f0303020c01090608010e1b0c060406140a0903090b030606070605010f030b16050a0318050a0b0105130b0a05210d0801150e060703 79
    0x892551400090b20302601a019402d803050b82070980801c04a54003d500030082602211100c0e51030901074060b0304a141a80c0b40082e20240c04904c4071405600076075040180c940c0450342c01100901d8108200c002c4d0380c02980140c1c008074584405580118050740981180d03d041800c540c10502c1e552007868001d004069080000140240c2e03201c1c2100546000d00305200070345401e03003403c1c01c3c004050702d021000d82c0d402001100204030446054428003c440e03034580c071403000c8580b41114084443e040141500d8020308100103170300005603248213090180641d0304941d404907040d420804407406009248448812500c04100c211681010540c1c2584400340303800b086038032403400c00100817001031800030071070701c9000340c0781040151101600303050310001d845080e0340304004840c0606841c02000d5060300303c80140420301c91800e2a0400c80800c47d00e40d441100036940300307903940e8a042154900c01c4001110300d40148880d80e50200958052034203440c04d580380c803040e0b03800182c0038030901200400b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 834336411 1250 834335161 834335171
    0xd020d0f06090b090318040c021005070504080d08090709020c070b070c090f020903060709151803080a080415050403120e15151206131511040f050103150612 69
    0x70001c00340c009040350b81d0b1056100e405420480781e070315503e822041c01100f00341204c1500e9140c03800d103442154001083c5900400141a1902c2d40c6001004081c12000c1003010405c0080b90607441005203981450007a81d0350300303007407401c1c1040c3e41c10500150408004d841c0104002c903101c4400007140000d03074105002281e95800117282810a12207d9801700305003070309224542d6080d960560142c0025031302a000d0700d06559520000f1107414006000b21000e01c2c079844802c41002e440358425100c00c000b490705012080f0f0f01c039100c03501960403110741c500004010204100405c00174494211210440c4101071066003095074004c0d00d120701c482450f500a039503070031418180b030720104511002c01d0030151100241c1c0c2855100f0400106060003400d01030000c44100380c1041d0000035083d40326080880006c6812250369607690041164000038001c1c81f034841034682446c20310350000740010080d485151081520301400501a164154400b82c1c101c1c00c59242007100750340104034080071580d0a040099 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 834337661 1250 834336411 834336413
    0x51807080a0213090501090c2a060b030312180a170a0c02090f070e09010302090412121104031403180103020a050c060f0a060807060f0e0a0e0405011a0d020d0f 70
    0x1d001d5000655662040107100013800d10055000c18180e0b0340295080c022961008000c0d030710b16109100c46410802c141810ba030241020b03003010748070a84200c40c0410380c0342c00180081d1440c0c21680190706074000c3d40e424410300011030092a24000840d40140c66400216114180d1a250a43c89950558000903614480b141310f48414000280c0c024900a2a402c0100c50780c4000c003021180200030034010440070710f1500d4481c50700f034121b17540145190040c2e071701c0740d4a140c000429441c0035014080364107030a1000d074400740904038043c0c0c0072181c01e507155480c50070002100d6009245450040c0c0080204e070f440794a03280300060b88401d082c01c2c0580d48800d580c80444140c45035030800c0010380102002c0c06901da01004856014a10f0200144480c3ea203d403071040e200c0c0b4052180b0400b15002e40e807400345c094002e55684414040080002d503946558100704030190380111070449250f5500c440385900104038032043e65080809940403c4880026070218112412001c0c01404034206000110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 834338911 1250 834337661 834337681
    0xc0206091f050c0405040f0b15090a14010c050316020312030103020f0f150406051308070e04060b060d1109121c0c2604030605130804150c1b030b0105180708 69
    0x1031300805d006002000300c401742a02d020000c041c9258920302c111810707103015411020348410386403a010010f0009407118138002032900c5070002d600d040740c140041c480003403012032000d00c041d02d581d1180c0220000291f440348105130410600410752601c0f00d406000610161711a02c1042512520958150070140801e100242601c9046c45000d125464002400304240da4410041c1480898520510900c2c0791100301194451900f8015900303594403900000c0c011460b180c010728a03000c405080d0600d040c000010301c000f80c80d1900000054200000751b03021142c1400c0210380640207200c00070300812685010030024291046050030100a40686c000d414010400c00c0449812840130070003c400c4032030410854640c0082c44207407130113450000040d040030002d01c15441c02651014000e858941005d4103400000c000c041d8010401804149010004501d40c0c0c210f1410010710f60b030402c1c810b143d032a01525810050304074900411802180b440039130340d03400210307030022440d040102c0c80d03a58141001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 834340161 1250 834338911 834338917
    0x3060321180807140d05060601050a0509090f07080a05061f0203040504050f040b0108010e03070f050f07091e14070305280507110a120e010e04020d0c0206091f050c 72
    0x10085141c0c41c42001414100001e101401c44201c042038a090740006003c004040354240c1e000741407600403500060541d8811001000003000c00d06043c0c1c28421201d000c07030b02c2c0c0041202c20968240002c2c0034072107007941126141ba400459002c00340003e1a2120114640403190425250040103901020401c0c40c002d0040d200900b90160040009280c54104c03c070444406031416211606a0000410a004180103000390185010000c0d4900038040da2101014004c1360000d482da40034036800e08031404801d0111030000c0c0801080440d0a50380d02d64891359811a612000004502d0f20a5130354240c500e88000c13641c0b0150f1820006030036130398074264105002c80c42035044000030414003078444050240e448280200d85960381d50044040384000e650781c588446c1409001e02c00047c600c041f01c1886001810315809040c5408030640403500045420790704100403244070703a81c855240742483c0c0d90401003190f01a100500602111f03003c0302007080b038500041001d650072a11400000d040c00700d40012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 834341411 1250 834340161 834340187
    0x30c09400e012c19080901090e07021c0e0904080c0a050a080d1a01050909090f070305010f150506041e030b131208062b170c0601050103060321 63
    0xc2c000c00d0300399000300d144a01082002c2d40c1240020000b122124000030b440a40c001a592601302043c15680f00c001340e5401c44298141086054000445c6040c3c494050501a00d034a400400e21070303081498103102c08082010031000c10131000c4581030103540e41c000d0310750007176044115140d40312070010b503860922544030700207400d038400c1c2c601000400c06200c00030032161005020400031100d1410710301c20309501d4210f50740d002420a218a20131450150500ca80005494003203402d003403a40d81c5e04074148001c6900c10340341655189500d0407108014010581904200d01150346024100800100c80303020350302500c1540c004045140600c41061107194018640048140703402d842c0034140030341c0113202d40008030f80008a6040e40d94410740511034180c01403c00a040604800d40c0c2029800340303010070103101c4e540044001540c0d000c550508030040592007003d00c03003995941c042c540c00345842c006901480c101450130b00c081000c82c2c41c0300809652185d0f4240505404080030700202d50150300004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 834342661 1250 834341411 834341413
    0x702030102191701081c18090c05040e010b03070219050c0307090203041e02330a0f090f0f03080304020321251509020307030602030c09400e 62
    0x229050850f0043c8400c0304500f00c40250b518280e8a45c40c603a84c884480c4801060704022141c0a0500180601c2c0396440f528050091800c05503502d004c01d03800e0f82c900d40c6180c0007090001a09122400031000d00f00e0140049846051841c1001c0e0340081d0740c1d0080100030348182820b44004010440c0c04d00240580e02c000400700c400344d94480700d2070002903205980440300351b401500d2140030014880c10140240390000e04030b00490780703002e8521b0f40c090410f10300c4800e45c1c4140c111601e04141120041d01f000c0040769240d072000c442c82d4101a013000701681103100444690303101004004c8844500b4010b41e13078416085900c0303443d81c0c40824034004516844004004003443e09207581d801803030140c11a50022512189010082481901e00d00c0300c081c8e010700f2082c0394540c80e44214100350403c0007224406030844407010340c0c039101c00c4102e81080e05c404203281c40024501d2010b20700319140c070b246030f40a900e6840f4140717003030380c8292030315007020545203808030120b031006500d9041356100030040b00c0044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 834343911 1250 834342661 834342697
    0x10b160c0b0d0b0409020102060c03090a0510050f0906010e0a0c1205180616080a0b0d020d32061b1b0c04110903150a150801050402010210051b0702030102 68
    0xc500410703690484040000748502d04500380c100352410b07004040c0c6007a0103801134801903c500020200b03c0d0b00c0180304003001d115891259000a400304850200182c01140005090600260085503040064043c0000c0d0f03110500600c07110a01000d500e4101c9051080050704101c0e02c60280ca1046100403007460b0320385000304100a056402d00000000030701c1009032480b55440318010030310b0038000c881480003c4d038210300003068207138103520803004c4100007001380c4040140d03540058500020002d088032160707090004a041064043e10001031a2640b0390b040ca40c0329401d100f4560380c0e10b07000b0803545030880c510f0103500ca42100d90040710841c11a2011081c491140302c1d038001d90381d4030800155805145000d00d489404030321a0141c40e00b400000f0080c00c501c50b40c03102102034090002d014100301c2030382c0d43e50080780c2e00040a184801080500300201e03081c9014000a030920444000f03200b02d0b94280020008109089a20015051200c40800343c540940c1e0000ca80207014003040106000006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 834345161 1250 834343911 834343919
    0xf0f060f21190c03020a020705011115041407060c0f02010e0f0604060302040f0504050c040b0c1f14250f110a032304031110030b0a0e0a0b09040209010b160c 69
    0x6607282c5200d03007074450010310405880c2c0004400320310a5000150040e00240030a0000e90711441400f114640c12a045488503c2a03000c0c8044d1880190f0701241c6201c90241500280319040c00410001c1150741440403901040341c58000c1c500781011002410001c46c030000318429941c4c80c0044030b55200240000341ca4030b4442002600a500a010f0401ba0710b1070200300060910b01402454441c0760690030352420103160071034000e181c3d0010b078847c107410702078440c843e5102c81a40c0345860b102c41c84003001140c0805101d4031290340003070141615050b00300124210030884c0c8a03000300081091507103043c9200d98843c0000710f83d14500c10036880801d000345100f080506601615440300b20509082d0880c40c0307030300381c4007100540c81076210003015a4008003514100c3c2c54540044c25195442382000f245c2c0030800c40000e603201c6134030b4004114180300407040c0488031030188110b00c007101d0107a90a0020b030815400081550340e0520400343e07001d500003000d00140003000410305126902c06d0100795240d8803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 834346411 1250 834345161 834345181
    0x1050715140a0f1805070306091a04031706040207111908030c0114010b0715050c0903010e150a090b040206070201020c0d03110c0409080a0c0503090a140f0f060f21 72
    0x110341d10402d143c40c2802440001807204d03c041403101d03640301e40101101442c6561b0030b4050318030300c101503402c80d2540d6174680f46900b04401d0640720b50300c66510200541c0d401d0111903401c0a0103000c0d28003591060001c100004c0b0041000d122050003190220364802c61558903101100e0070380c0140180b8003012400c94000c8a0540007406200085011080e00d60b0301c81d1100450342c0112070010380b03482c0a81a540944035000d6001c550050700780708840346001038001c0424291100000c000600f94440408041900b500c007199681043c100703c802e004965460300e890490400181000e0300c10280004e162045a000b000030941582e030240c140601c1e040070b420003902000b242044801d46009400b400240d0389868812401900d6004448506081090404840b000c01d444012602403008008505840d51400c000000401c080c40700010304030190743c1030081c024415803036280a04c00040b40d103e0280d6401080d130b40f8410b01c0750411500d40000c0c030358004403e01c03084c107660407042003941840039400e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 834347661 1250 834346411 834346421
    0x52a0f07061a060a121a09070c110301020a0c031803170d060e0f13031829040e010501180302040c0c050f06160e12010203180f060601050715140a 64
    0x10645810301602c2c0c5240240806841007101e8000040c0034100030036000380c0030740d02c4264080d0280d82d40c48003c40e40700011544c42c510a50384140811203d010b20340c1003054250541c00101c034150002d600309918a175004e8188046408002d0920075002e0980b141c0140144031207000b9504040340d4085401c0038074a000d416400407078411211421f0201c08100030481000742e41c080e6000180070b41071607640f203d61407a80030506c80110200039600030015009580880ca41026029070b264155203101c81c131341054038101d4000004100740d941800100242869658524112442800c0903008000a0440641ca40c4001c2e00025405071030004040b6800f80c0c0a80340c001d100c1e1151040341c80010690056a50760041260140d02c03d0800c20b280da0315481c480c0d242c0c00040400034000201c2204402c0301c540c04d81c0c00494024442000a0050b565042410840d602110040501410003801c0050000f459407080e03804c05014160a01d01c041d003240ca60303034480d1040f40043c08001203036081c118504d4010700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 834348911 1250 834347661 834347681
    0x12060312140403081b0a0f06020c0c03070b0409020a0207080d0509010e1816020f010515150c070905060a03060c020c150a1e0905030a0f0302010f052a0f0706 69
    0x29428810014030807100c0d40842d4140c0c0d41025080782045c0310707580618940b04282d013203004507014006503940054006500002081c2c4110b0000d40c031042c0c010461071074808041c0103a4442da0103581d04011585145080700c0544140c41c2d400750b51b90f100000207034900071003948424030300d11442c1d4121358081d9004001c1e00440c002665144818800720041152401900030030b030000d00c00b4800400c2004000502052401c0c1103801540c43c1d004006852a0071601c04580c0c40802c6808041d000041f803800380400401342100001c00b5013420303000100160b60781221b0041404407544c1d2004207540d03a9808207010b000716840034017840903031034000780291202440980b0074054850003010034060182001524007051140d6074403140a40e034640182842002a001c03c81030204074640440d45880911100c6d40e940e0007080c80f09a080850315000b0b00711501c21050390412460706050040403104070014a080100e4100400035460004126515501c100d48114404c0e02000901c2c00822600c0c0d04125a10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 834350161 1250 834348911 834348917
    0xb15040303140901050a0305092509050a05190c02030405090117010e0d120b0a0f060c1716080304020111010c110106050a0f23100309021914060a12060312 68
    0x1002e02c101c080e4607038001d00070381502150302402001004e070301c20f5110030707030240d14102150120042031569650304081b005103681100040102801004094054507030021035070401000b0380d20f802410b9078040b00c07001401c402c0d11500d60210040c458400c1041c0c0e4090100103050406039603503a90001520700808203510131030750070513100e01f000c1c0d1070100700c4041c0c22859031074043c11111400c410358020f006c0001459840885c6030740104c0c203040c1c581645805005c2503242c03a09501c0c8542030410701d080c040854244002420014a13942e80e40b80881c040250b544011a00e481e0307201e502c01a0f411005119203442a9032910540d480040d43c060320f68040c0701002402003203415210028042c4000c40d50041d425072101140c02040b1032020030034500100c802082e507040041000b200010720000c400048800065210806a015072501c07000d50782d0b9280001000d01101854000c21424a003403c0c00458401c04002c034000340740a00411300c12224603041039040109549a252002480401500ca4000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 834351411 1250 834350161 834350177
    0x3030b04020d0515010f140f160803040c0b0405030706030203090c1206181203070809070f030602030601090b070c0306180c080a0b0705030c0403020d080403050a061d0111030a09060b15040303 84
    0x1c135502414130301d440080c4a41c0c580e80c050103500c0d200c1942c0c0c0d00040480701d100030100020005240c036501c0c0000f0561083c4401d60703403800d15041886800c0d100340c02044081d08200010405658000780c1c900440d056800c0140c0c407940c4849025041507101402c0c10f42005810b44407140410004c584c00d845130503026031610500500c0300b038550380d8020101c03100c1000c0c1002c10120392128000d40329150310000366001c40e080740d40c9810006000101075171044880c2600030080c00165a004200c0101074004403488500701141c40e02c40e071003142d0440c40702801c030310f80c1c40841e001d641e005000c00800f9550015151807020395202011031360768100e42002d8840400c5403010420052150088030300030344580940508103811502045426414144200c0301410204000800a2002e21054000c58020140001c10b01d088010210103251194a10f1640340d150425555550000c4001d4a0300140c0009002410324103514120f80280001076501c0e074000041c3c521120901420340092080d644640d40380c3c4a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 834352517 1106 834351411 834351451
    0x5180f030c030f010605010305060d0f030e061902030414010309210201020d0e0d0905030f2d0303180d0e060d05150604080c01030e0c010903020d03030b04020d05 71
    0x3c441d94483d4410040c940c2c15114080c1c1c850030541306050303c0c4103107179905c01c00042055030040500030300c0c5410100c0f03500e85c1c030262a50030703012983c3c0030009c3c0c261070070280d03607500300d40300e00c00c1401c8a5103412401540f00380501e8441a501c000030b0b9518405105015904414035100c6030115942400049000d80d584d024008402145401900806681000080c5aa052904030f035019074804d001010110400103402185d058620707140000c960010307204850901110070001c0f05a04c004404e018a00790b01258180704034041504440140303c0442c41991114024003e90f0340c064800c0c015510490016042a64800154150390308032900c1640042c2040e0001d8210010517807100d8005c000d1540c2600c18820500c104100500481d84150300080c4a20740a0200a00820b0084a40400c0502a1f00280c0c429400140159161881c44200750000c101c00c85243c42c1717420000309142 = true := by decide +kernel

theorem cover : BRFrame.Cov 834172661 834352517 := by
  have h0 := BRFrame.cov_init 834172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 834172661 ≤ n) (h2 : n < 834352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
