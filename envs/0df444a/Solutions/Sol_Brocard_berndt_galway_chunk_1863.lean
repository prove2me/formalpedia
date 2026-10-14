-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1863
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:56:49.502489+00:00
-- url     : https://prove2.me/submissions/c2aa0ced-ca52-427a-bd16-b9fd51d83ced

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 334892086 ≤ n < 335071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 334893336 1250 334892086 334892093
    0x40b0a020a0501052d0c07170903010c0e0609040f02070203010507110c09070503012903070903140309060313030e09070f0f090602101505030f0708150f04060b0d050a 73
    0x2441c0071007050341c16500e014041140c003241d0382e64420210091114007241c407829000610b4048100074014200b1142c00c1291600140c58a210300c1071b40714403102e0240d1501c1d00d00060500b100d0301510100180700000750030064550794941910b00200d0111070215825120300c80080282c0540003000350150300f00b4050045450f0460310b01c1c6045000082120f03401100b4004000706007100765445801315404000602c0034010341d800003a205400310741012200300c0031441030348403075004881800c000382c6410020301c2004841c41007402c880801000841c00d00d076008000403d1440080d000c000075000d100080020180116142611100000c1c500001442e0410028250794021900c0c000001c3c00190b04005080c068800e581c107452281d0700070b000d1000c030a1080700003814500b2407081c403c660700c4030010300c503030703081012041134030740100941846860007000a02d00128501740702010202081001440102c480340742d503029400cc5400310b0485841004620036059a040103843c50280b40124800e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 334894586 1250 334893336 334893343
    0x4020d0c020a15051003020d08090d03270506181906051b0a05060a180203120417030307020c240c0601031202012306120709050a05070c021014040b0a02 67
    0xd050007507455801007107140c400f03a0704464013200d0603440c03015861018005402c0c840030180309244902001d5103448000400107802d504a0f500442c001040070700c4c40001c07000704ea50b400190404045103031040038284000510b031030041801040d03840c20409143e445139a600b960302440401e020041c0d0000e5515900001c0450340090a05c0301801500303a14441c800381d0008040107031580100103405503464003500e04000c0c00001044100203954642c094000d65000e000081d104002c0c40d00203542c56140000500e802d00b802030300d12049800134420044016008143c000c118001114030214041044a91070355420844212660030389000c0f40c001c4032040e0025606068a020300c110302840200e004d012403e850401c4001c90940b484011002d07034060705140e142d50403030401008c04c0300845180708641e182200e00e80c81444000d1710340050142007082d0b0300c50260080700925003840c0c040d095030049000325521041e404104000e6a80c3d0707a154400c0101501d01402103141015603d52561500070b58 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 334895836 1250 334894586 334894603
    0xd060b13050109050105091806190605090a08061003030302071502040303050a08090d0e2b030503150303090901330302040501180f05011b0503030f010e060a080709090204020d0c02 79
    0x803036072401000c6011740c0100140c4141d014020030800d540b000c12190102c580c42d0107010a41c005100401441c1c2d594060309010010709650356440da20b0302c858104002201c038059006030303c00c0e04203800341310320501408000c00a5940605000d0f0740c803106890040146803c1009242000b440441c01108243e80a4020400036105a03500d02c0c1c60f450320003c05032200341280d0b09a010841c02c180ca0001da0801c1141e207071801401d0034001c40d1800d102e191005042107101400c8001610010030450030903004d00e0640c61480e82500210300b010352440118940c010103010303541091030744641d120f000b403020ba0100050002051101460004650700107006500320340546404a80701c1845048554501d544400403640384080d08031119141c80c005513803100304015070070506006480c0714400f1500400c005c42c003803c8003140c410840d6151408450240718043c10440c41020b40c04010420b03060300090032010f84005450000b003115013032000400030f1240c21880c1c0102800c21944610701130300420b4002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 334897086 1250 334895836 334895839
    0x105010b192f032a1009030807030b032d0d110a060507050d0e0a03030b041e1d1006080d2619050f01140102010b010905060d060b1305 59
    0x1540725880e0a4036016054084001d16050986002241c00c0002c1508544111184192403074121407050b4000d800480001e00032188904c401142074031041000001c1c582c0d0341002c0d08016a00e00c9580007410f074800a440c20042540b1800540e40b00d5070203110308554000c2c0200e01180b00d0304034100702d0391424400041208240a0511040d003154040c0c10b1300c00000b10881c0c09041e9980040d0b44101c0245405001f841c20050b0a100303901e20b44005100301d080700c07403154000f00549540d0349001020346084050322400342e828882e03207900c100e40f0120708949940400401240084201902515840e401000e0030314070322440d0329808096242d584503c041d1070f0540d00f52904502202400d484400a110030811321344c0c3d800302ca010078540e800c0003194001800d40ca01214170b07a0f03240c40b990140e80c020341e64020412402c80041041c030074a0200c00084290030300007030101c505400001b0b80a940d0900ca01405101c00007564090815580d0010024100d0343d00c01a4840e42c094801e540420058054107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 334898336 1250 334897086 334897117
    0x20d02030403110f0c01050d020304140307080409061424091008010f0e090d05251101031d0a080313020307080a110a030b0703020d110a020318040515010513080105010b 74
    0x14070022005c1544001d000c01030712036501e0b000d1595010002580000c0040d20701148544400c03894604c01d20080ca00c0c1d41c0501160794490341004941c80440b00242d008600c480840c544d0203034162941c40e05000410320807035407107810001200780d070601b0b4401c554030720f81d20842504407841d040c0c0c0c020f01010f043e00c002e800d40f2a07080d03454000c0e140c146942903c4031201c5500c440f40c0b49001510400013402c0b03400070071140300030034980c501071500003042c0c502048913481148003a2210559040c4182034030445160701c64025109a0308007242c5a0020f2203014140080000002e51486c02c5900001e80b81c3c1c0d40602210489030341c0c2c02e070003070b100e150000084403014002120a03909140507010340b01903039000842204036481d0428190700a61008510240e155150b6603c3d04950500401601c01040c41d034014680d1030340c46101010240704644205407089240405200b040c0102250041044a080c20503e43c1e90f04100c84c0c5507014169a84140e82c0c81d070900740042a0081c000024021040c200d0059 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 334899586 1250 334898336 334898353
    0x90703090c0509040503071211060a060e06240a0e090c09130203220f02030a12030e070b03061507060515010807020c0127170c030c15040303030b04020d0203040311 72
    0x400c001104262005171050b8414007007240404c4000782ca4086410090500403e4030021124607030900c902200c00b8002e00740c0c1c810040101801e1002140d40c401ca04603107505001d00d00ca90821120580c91541c0b2003040008211031a07a14018003c074050608024034a0055180015156540f075000d14107280c007400001182c52420300440c02601d00036a5041c840c004202c8030208034107442032001905403440030218160340d005d03031001c2c040100d025008500c1e48450740c891030400b405481943c4641540e0b94041c1404010703080648003540d8110300e044540d0311280d0341104840e440ca010b10440641140d1410081c441c1170305540184900500c2c0c00e80701d6481c5030b0b641c10020b90b1103028603c451808101810940103804c101c00741804664110032092403080c5444103826841000120341c2c8086d00c1d44005401c500c0c1d8070341040f603d4800002102c5103001c0c4d01e03980c0059103c500a81c48018107040c0c07642000e02e0f0f0f9980d6030701a43c0e45035000850131512483c0504004100d200ca840d04200c5c81d0190181 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 334900836 1250 334899586 334899589
    0x9100218030d0807170709030b0412090602030a120b04020910121109030307030e210105041a040507060804061404050a110f060412020406030c15081f060f0905090703090c05 76
    0x75000d00c01d9107545c0352110001c507021103450042200401034020809200c0b03003c00080d9452155600540c01451b91401001c56030b00d01422103600d0313410043c1994001d00041122903403000ca5540b42042d144c00c042400161388000c50064025040c195a10100c40a40b02e80c025601100e40c4d4a072541908003800104501804015548221203030603401d90000c03c8240c002c03a0051501000a450150101c0c41c51080e05600c100c412115913560380c03099449001740424803007540100005084e0302c031280c0080e410241c0d21103990b00c1880c40341e48144440600050244031081e07018000f54441039020252507e17041ca8161f0300d070040c108044034054401c0c0318180e203908210029100c54480030345007514090610555002040301900100d9010b1b44500000c000982d002c9071070801407070145081185a0790700d030030103807030700c00020b0101d1041c6900c840454070031101141200101c1e0028103040d4030b070030840f1504132018030281e040650031080f0035080c04015585540310440721382c058180c4020180e103a10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 334902086 1250 334900836 334900847
    0x30e01090b121308030112210905190b0d0615030917130911090909010b0d030f020a0b0c030a0b04020f0306061b010623010f090e09100218030d 63
    0x507211403a00280032082560498a112642000c0e102885050041007565000c0841d4026044210040c0403081c0d20001c001f14064840c0c59601c0a4040341403071800b40c10300030304c1140d092148900c5843d00c09150855222002c1d6071801038600700000a0741c1d13504440031180603220500c2452228450f1201880c4824400c0c401c104034194480028502c00180114103e40780d00007000300e2041c00c24240740001c044d000d1b4407032445407203070000344140c8950713010040119040d8010722800183e41010303203e4145503650f04002c0d14542d41800d10980030821345400300d107000e41d6180005c180341c166006106130b076a003e0014500c5805207980c280b041c640540c2c24031080e4007901500c1d0040c0402413000c2409850000d000e0700c003072030001d040030f0000c000301c541490a55840e9801448003000c0001c890302c54440c117501c0020780007001e003480b10303058840c0f0070010300000e0f10703114140703c010058021842d20402405031408180c06000155150582c0800038015021120b810520034810400c20000300341c0200c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 334903336 1250 334902086 334902089
    0x906030d080a020913060e0603010b01050c070303050a030b04020d1d0f060a0b010c020d0b0106080606093708150a050708010b0705210c1011090d020f090c07030e0109 73
    0x759500441c5441d0020b00300040d41000003c5907200c90341c1603960741d11180d40d10074a0f000708040e1902c90100e0a080c01410b08481c5020301542c1000010405e500441d540080c0900c1120f0703243c905550748007001e403c103c000b019440701c544d034043d0000070800c41014490b0081802c40098440d0140102a60031009642d081d00402c003d90340c1d0048000a40030074455440b41c1c20014060400062104031079000500b052071420b0300700e880f070360100011b0040950003000d05602c02e07010b468580c1380007030440000d26040c8a07000381c1c5404107051462080c2d0440d44031111110141003603900703080c0a0301d5802307480c2c480300860104200c0009600010701170b42070328000d00d806040036449800305a402d164842e68035a011600540b018460b102c4041c0a01d48094098404090100015500c4140c40d0000f80d0074484400c1c100c050160400c9420f4030355068003c12500c0c07600e0116501d0001c410130b40b003c202c1c111001c00503e98004006005c00c00865040e4000706071281c426510741041038095001540c842442d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 334904586 1250 334903336 334903363
    0x60f1205010c0e03150907080724030606080a0518010e0129010905100302040b040b0705010c02010903081f180e07080109050a140115030c05040b06040e0a05040c12060605090603 78
    0x800301e00284074074000030b1715800221500540c0c90b2544c54100741c07850000310f40e0142c8480030040c2c4110408003e48885e5400c510228a030912080b498170100070003015001d001d109030542d441e00800c41c441d24a071110240c50140c2c20080c012000e00d00b01290003000840b004035000e1a81e0b2054460780961300c0d8902c0300c0020161181e44200b41030000340312a000c03040392000c0600d40d0070030002c00e194206d8006000200030500426030b03262064a031a41c29251440010b8041da070605002c54002a0000301e9140d0010180c0700e88040d0242d10050f07030710001219840000348090b10307894545d4001503034200c1440034102e5812180c4055407174510314204c2d00100343c050407a80144a4100008481400104403141884000309400d8030a000b118a50303869940100d550f00503084007006a41064001c6142400c3c0c21904141000d01d054013200744280c000302a1144039075200300140801c600c0400c000301403c484a581c0d111264140340c008000e0440f401164420503426000492628000031701014080c4c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 334905836 1250 334904586 334904593
    0x110408060a020313080304050c01200c060c10020408010b01081006080408070309150c050d050a1407020301020c070905011e061d01030e0a0b15040509150406060f1205010c0e03 77
    0x4907040550000d400251260862064010f012070100e00004041c5000e207002c2c0001c1c0201800302400580b5500203806104110440281900c480e103101003400c0e100c0c600141c0301039688141c40b21110341415822129a040380e840810301080211055224641003203081e25a1402e541f1604030f0f0801c00041842040002180840003c3c0060b288802500025103c0e00304450011b44403004501164200f00048000031042034508040c048100f0650120740d5080c2007542c07034038604100007881001070013031019501c007001a900c01152401d50490350144500401c1e12081340d140c46400f4080c0c0002e1043c045003480e844074410006a816070444110f03000d0380c40d8074089202040f059015803008500150603d90341c0c803242c4411403814010908036512038005008113140c17100340c0d44498031105028500440c45c0c041040011240001d6501002c0001180c1584030703030b1545049005410f090308802c00c14280c100d0000784410302d1000c1d0804151051000b8000001d0890084410405a04d45d6030307070650 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 334907086 1250 334905836 334905841
    0x5030f0f0706030b06042105121e03090f1204060e060a050417161403010e0d0e060315060a050a080a0915090501090219061407052109100203090411040806 68
    0x83c06580204016000500258109603031a4a40d4244400c040300c20603004407100440310400c0018006041000c650092076820100010042101072161011050744880000049100740c0350030001035088980c40c004850301207040d0900020503410620075607011600d4103104010f00e191010980b00709030322581d5207a08041c034051803000300c20b880064045490043d15100000d1406d0950114042c180c10040702c4007040014003030500311010f0b08100c0c1100d0700640d282240481d401440b05109a90840700981c90380c5a01c03614036007480e030900b10740d9403000740099482c45d40c07908030300541081241521104820740d948a001c6003581c2c400c010080c144016007010983c500324035404004000e0081c000002c3d5007030554041206c000f500210b4400545801504000c0d590717112060101c10703021820750a04007461640c9255943c0c0d045000201800388440aa01128801c0e03416140300403c0100110303410f10301c50b00c0282d00c903442040040d000d40c1c108a40c078550100d203e0119000c40d54040001c02103039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 334908336 1250 334907086 334907099
    0x201030b031c120e280f05010c0e04020403020306070f09080d08010306060608090604141908030f09030c0c040c1e080a06050301060b0d09080708030a2f090f150a0905030f0f07 77
    0x14032000301c0c0c5e41800c116905d0030020134103070300c40d060506109000008800c4000d03d0050001c0d6401c00c41a40b00780e00400c810301c0141c0740031940c990004440d0520313400722500720100f40c0d5600fa49400100301c600c150b2503480e0032141e20240300b81c105c80c001d0b00c042203040d4440c2d1080b1810a0119542e41240e84800c0c0803500040b00c0c4401784901c9520f0703009945a070001c40752080d420000c014030544200202000380402014442481c58100700c82e00000e5181c0303203065100c1a00c07485007040c00e51281d943e4114405516000d407100c03140740c54411035101300144447c5e402800b802025070705240130925007070001c91035081c14400e50040d42c1e0450080c505100580e4101c902a052034401100d44000c240407a2002580c450003440c01000446004204204000608bc0c400c1d0950302e59a8100703002c2484541d0f079524090102e4200f0300e801c0d5013901890300c02c200481c907494503a03105800c12140010f03404245681c00302241c81074500c21816a039000595440040d61003545520040040e003040d03c081091 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 334909586 1250 334908336 334908373
    0xa0c0c1a040201050c070905041e05062d0108010203040302061f05090c0c010507170f010b04050f0d051f11041d071107030803010e0f0c160201030b031c120e 69
    0x410b00c14502a441c2844190000d070a00203103510882c05035480307105101c00c0011441d400720a041003c00c000d0390b031401e56150503540b070102510407010b0550115030142c001400300c2c10b01c1620b543e60341c4000005d59603900c015000354011101030f8014046c04011034080411181e1f038100050105450039080c1c0c3c00c0004120310b904000c0c1c8402d2001d041005040c3e002582030086902c62071858a03540080c1054412509070150f0003058600300707588083c01800400100002d0b6401e50741c0c151292400e10101d400442c00303440164034040c14030b205a10b54080290040b0001c0c602140c1189014443c1c000ba00d400c0594034090340c000d80c001088144556222000001142fa5011002d45030421030182c0410500d401c00c03080741c20030340d81040004018444000e1200f2100d402183c5003821110382e2500c03048118583c05640b607400c4030015000e21b5042560f2107a000004d80140040c25180c2c1050740380c4020981484000100001c90407100300300c042e01116105410f0f03145462700142c8110105a03607a42003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 334910836 1250 334909586 334909591
    0xf050f0c1308160e0903040806131103062703180603040203070b0d140f061302130504050a0902010e0118030209040f0f0c0e010504020a0e0907031b05030a0c0c1a 71
    0x344541d844000520305400300107030521030100c0c110704000c40d418401d1001090320010125807850344100700130050a580000c1d400da00c0817503401d00580030701c0c42e4900b4006c402e50360043e80b40e16100e640c0502210305034168201c140008880c2446401c6d210070350985171203024444d000200000241007408040c28180e0041d17611520003416500e8880d01e5043c40c9016402100c41c21031169615560f1002e000036407510070b5005190350960181d140360210000780c0c140140070260710084c1e000302d2001c071003004035080c0f807019100007481407110b40b4142d21408010a00c000041c2c1c00030700f000d00a44d01c15401100c202c406440d1070800812001e045400f03111410303070068030407038240651291050100d404580107650503882105200030243c1b6140e0800d0884006070045803289104002402406030444e03804452074100b40c40105a0360342d0858140c0081c60480e80b01100010041059000710303034060021440707404d0002080048504050040f9290b44004a0051a82d401c6840744465a00041e09030b90303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 334912086 1250 334910836 334910857
    0x60308130906171e010e03030705070201120506091308040f1806060f0909020a050d0c080405011a010f030b03070306060305030a12021309020717040f0e0a0203041a0a02040302060711040f050f0c 85
    0x2110070042da1b185285902c212480800035030040f4044d0115a401000001d2640300544140190b0500000103a06424040c090902c00d0042901d4001040301c65001e0390000c10140a00001d800e40e0740d038041030a8140103100c4074030b940c5030035400300d0981c0c000c07400c000900300d032907039810203907402c19001034001c0d8098469042030140920045003580c1c030390b020308400146a0b660344401410a07181c094203541601c201080f003049041c008001a903070044181401325104e28000c0b54490a00300428100b5440f900090403085c2050070100501c00004000c7c403100582c0d0383d0308800030f004001540200c0c01560041c101802d0340c0c000410401405e9006410700d00d000f0302407290500040001c5816690159110101300d19042a04003c030b0816191101d030b00140783c020942c6507241940d5051030100480d401a036070840c500c404240452000d905403005140e0142139a1354551140c02c121044a01c0851071901c00c9081803c0f03842e840d42c05000d018007600c0740c0c840301040e5440d4045000d165810603154103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 334913336 1250 334912086 334912091
    0x70c0521072415090506040905060c09011107090e060703060515030c0d1e0f0e0a03180306090506010e280507110a0b0a0b010810030213060308130906171e01 69
    0x20301052005103d000c2c2d08150f800b00c80385800c2c0c03404943c881541c1c00100007920443c03400c020480030610204006903c1000c006880b80da4840c00e00058440740c0c07581e044400d4620403983c000c0303038507aa80d500c107460054180084a003141c1d15810200c06079211409075940003018004903000c0b8030071304006160401d0441c0b9145082184420016044030b80510404206240c40f007a0300c22400818842c41007507601c4c007401400a011041d000741e0741c620300c0d80c030005e04001d8240ea407801c040c04007580b90340c0a1940004140081b0140e8288035944420a006002201c1441c401080c5200200703221007441181c100042c40518540061f002d0041030010103020a010024039400da200e10241300101c5800d100b01110041810700e02c40740320450303052007142070502022501b0301c191845445032400440703504a500244148040d844040504180c0c1d2004040b0301002c00c0000b10341c41d540a6200036204103074800c0101075606d50041600002c1c40c043c0f8031464005509903c5000e000b0305082e800444002c001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 334914586 1250 334913336 334913393
    0x9021b0703152d0f0501051903140307051911090702060403110c060a09151103070f02190306051605040f0b0309030f0a0c03090803040e0601030902030f06070c052107 73
    0x2444804a100c0b40203400043e502d101c0050469224417a49002d000c040d0358120030542100740450030080c450001a108480000b544000904100115941e07280d00ca026140c686d058030040000c0d0b1405040100c82d041c0d0300080c0b81d02030342010004144a00c03600d40c028040c644998a05556070f1104208400a5010303030b6146c805691903078801007604284030b981c1c0f087c1280c41c1aa4041445480110b003800700703e0f84041e001400c030070020907200c1c029000010039440041c03d100007408075038000043c25003410440000010320031140d204903c00c1c801c540d2020480c80303019404540b180306a003e00540d00d04d49000c14048991040081c5a1042005e0203ca00d00001c170460301003130b9003040e410348001500001100080543c004113032001000498000c608150520010030010180200b9940c10144c2d1424000c0c290740d020081e02d0035000c8a4400c0c1c541c4d6007003032130008000030780c1035009803028810003814081d0045120710b02445040103000c1c141c1480c0302940c9040414040c40010960f85110614 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 334915836 1250 334914586 334914641
    0x2904050402130b0409080f0a08010b090f060c1006030f02040b0114220b030906070908010b090a02180a061e170c0306060706050109050a060e1003020402160c09021b070315 75
    0x10034003007e901e00c01e181c4038a15004014a80c6005800a44140740c1c1407101c0c0d0403130781381d0006e2103030b007058215841523780007110b040c00d21705401c08409c0c01c0914141240081440040003041680a00031b81d8140005082500151002c640c0b105c03c10310750040405c84030044a1141a5002c0c00c0c540301c82108052998070035a0f070754150410740d100c003840e80000b01840000343d00241c008000f415000b009000f0404e914000886846008080540c415000247e0040000484c0c916900c0004000d00301b009032512960020b2140b01007440d190009810710300c0d59229103019108918003103c044070740100700d56813490001440c0d0000b601076a0060400d02504000451600030540030300308403d03000402c1d161402c0c2070001d640503540700310040d0602205001d5144607104281094036015940581c0c0e070b2070081c02c0c068118890f900040d04440c0280004a131514040e0020965406071100c00d1484403d03c1380351549801c42032100034180c00b484030341020210340c00d8000b112030b02440b05220a401d42d081a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 334917086 1250 334915836 334915853
    0x140111070b0105030708062802070206160303050c1204120c150e060c030c0d0e0c130603060e030c03070b1905090307050d030b0109030303020702040f2904050402130b0409 75
    0x5030494480c01e8280c01889603041c204445001001081c1c0242080c4c104030354a10300d05038240c04400500c468000c12450701001300e4045030f42d00c50f40940260356945e03500b00c140c81c000148102c00c400081c00c00c000301d60403001d000d003030310006030b02c2c02d90f240d0540d151540c1d044031890950b0780070340c1449100384640c0b0200e0040359120390214100c400110700307420a0300c1030a0402d80b0040c0300c41c0b5441001d005021035904a00140c54501e21040341c0007503107600c0346140d83c3c9040342d1080a207620061a040b903034040c2c0066040b001c01c8038410348007444000c0044600680301d001d0300d85000d40307a5000340941c00214152104c4181c00c8001d0b80321200c00d1213048198241990070843e0314154540c000180307042001001c0081e0306008416180400c00c56183c140020b05198440c803014007059004514041595a1070780140c002d000000e00821440c4010401180703401c141d480030b0b45118008100d0038551f81018080c05101d680d0052580203044a06201e0400038040480d203141c010343c1e0341c4044000200e00c0e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 334918336 1250 334917086 334917097
    0x90c0904180c0f03120c03080a051510020d02010b03010e060f07050906030705040e09010b0a12060204170105190216030c05010b1518040b031509030d0903031d150103140111 76
    0x10f00525281401c41c1030040311840a09210360802a0f84201072001c20750080e032040d000300c038010002c5403944030081c2c0c0d81314224100087e42d500100d100041d08020380c00244c15550114a500280b25628200040508885541e400d80103150001c90010b204bc40859030720342c0d441071050400340d06104e00303180820415001101c4180110344d0018081c899252082511a4007041c030000a010000c085000b040001d00c5500c214070000c603c06501100300300c1c06405440182140369203000d0b04034804400769019080682d001c540541c0c51718000170301c849a40c001ca40549081e1006021100c2c0b60f03a404840f03c0001d240161440c0d540d03004d06841540c0c45413001d0040046001216484440e0780065030752180c00c0e014108e109500d86800c059242e2004500080442148090010700b6610f408240d8154404c12202d4503916181501d40c0c0c01b0147c05510004c80495001e0b2103003907690000041982d105001580c0c8640e55101b0401040040c00420b201001d10f00315800201e01007038440c0142c406030f04807 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 334919586 1250 334918336 334918349
    0x315030c14090604090c060311070204020c160b270f130b01110f07030b040609050a030903030207060305060f120106050409080706050705210406060f09020a0905090c0904180c 77
    0x500c0101e81c150710305450810707000071040b90104503000c80340d41c444408501c80e20034a41413540701e2840410b0840d8040545a2058000e8429552040603210f940c0d250300c501240c003102c5196070b0401155464a003008d8034200040400109040e041c074007a02e0484140021a07203602403c07441401d101d507202c2521100c3d400244003800305100d90410000742500c03d0400342903800b076128410b8410b62441c00103400c2c00710703900400d000680d0748407801c5c004040c003030381070300039050740700d600d48403c101036000e0f502c8022a4001e50984101d01d44074100bc0701621020349906a01c2403000030190307820304d844000e1519100304540001070903541d81001c1002d0351242081034070090004152801070001c10b0044039440700192800c649450941034801c001910040c0b07101c400007040302c0c006801c000f00c6500080151842c101801201c1e07035282001d0300a03500100080c000038040d090002410f0428507095070081104509490900181006100040c6204022084443c0c0b1a8456501250f42c554854019048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 334920836 1250 334919586 334919609
    0x1805040c0e03010b060a020a1716030206090c18010512601801050a0e010b0a03020a29030702030406091202060304060c02010e120a090503070302030d0315030c 70
    0x70500c04050031502d5010086010b80001c1100001c0c03103a0109a10b40440c2d40002042a40e134564062004940980201207409045440114091580018600b40318142e02e0040380c020004440a00c03d407000404103c501c9403107080014041d80c50f080004d50880700c5c410003103c03030b030f429480c1c0701c042c1800c0005550a1104203450501400c00c2c12112128500f410f0304050542040807000d040d821240810b000841071171046000c660b14400e07001c10710307a84200f400000e2066082001907800100003850309108550310740390b0b0b104003600341150010201c0b50000c00e442c40c030915004202404600c0800341d0b01410380747e8410700d0280350032200a1030041545500030345d11241040030107040302100d1741049114810825203c0c0041e0b980c4000c40f940142d00107400300c0c4006100106a014005103100100240515400400c00608043c0a0048165244e65101e001980d400506459116502019400d500585104442d06001c0d802294900b0443d20040c16050b81d40d0300d074080d00d0840342d04409100748 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 334922086 1250 334920836 334920857
    0x4020304020f131d0a050d0c0510020d271109180a08040f060206010b16030e0319020a090b01120c17040c0e06060f09130f0f0509010f0213061805040c 66
    0xc1007040c01320403031080c1002440a54580d40760141e850b560450b41c401006140c4c2e1101b0b00b0032406100300d08190117007113000d544030102c002407a00170301403440b1111001d0840b20b04c052141211000d181012540104561200407040340c180a04608024403016450000710450f00c2d47c004e080007001a400e000b60401902e642c00d0040c980c5050f02d40d40d00c03150455005500500843e40c8c0f8104640e041c169038824092800442d160554607a005501820b070b1501801640418898504000c030318924401c6800c0c0600a07119070b000307012201c3c022211400201e00c4c07054080c80a01c0c540c05082c80103814282007500802c2d001180c0c0f007001c400c5030300315201c402c1e00c0b40401401960300d4884e034201c10304482c034a0234030100c1252820540121010144110140b022045d4141c8041c2c6c040d42441c003010b44103100c1444040c4c0400003426099541d038070103619080444c003907200710f0720139144480c0320082e4000c542c619058089920079040002d000443c209d0a10000382a03803244291801d6200540ba04820316 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 334923336 1250 334922086 334922111
    0x60c070e0f1302031b0112020307050903010615050f0f0d091407060e010c0f03092103020601080307170f040e0f0a0c0804021012060801060303020604120c02090604020304020f13 78
    0x509018007490000c0b030301c0c90420801654082030600c0c0c04450762640c1d03c150016240100c46240b400b0841c41000c620000c144024a07074414020000800309074001c0c02260742e15051001d4041e02542c1c1a00003880c140480001c6401d80360042c41806040f05400303041852241c1464100e8503520400c1fa0310300b414291090354000c00384a00c030018101ca06018170704160743c1c00041d0881e1b041c3e440003411500c04512040405000d00038800281c40003544c1d00a1710b108030180b86403450606403080d0301510070040009481403001003103407905944030f952043e03010358880d0b494100360442c06c080340201301c0078000402d1143d1000291803003020089290102414521a100e00300d07035103064168100404a810040540c9610307524101519052034007861060b080d0701104001c140a4010b01415400d0010000c1850b41c0018064080c0740201507603400e10860079400c0e252010403407002500400d4050000c2c3c064500f56015661050016007818003404043c000101642c17121300414210700e03662240306c052f5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 334924586 1250 334923336 334923361
    0x70e010f0e033a0c020108091c0806190f06200316020f0607030f08090a170d0b09090703080702220c0f0c02030a020904020d0b010b030105011214070806060c070e 71
    0x40f42d0490301c00031070034055100142010340810000e810700c00c42c4008681c12200410000e0701030144000d5000c185e5004040007811500107540c01031240322081001c03511a4070b00745819089890410034003140501c2e1080035120003d00c40c282c40010503c43e02032404401c0d05100074151507401510115020b41c06104001e40a000340c1c1c10300d4000c0005004100001c1c1d000044070029042ca41001da0303d0380c0d1100f501d145003e440010080c54550081081014601c5080291004c035401d00c10030321440409206000103210211000091540501410070208015400811380e060020b80f404030303203044540c0100e4580d04090a03010000d95608041c00800358424000700c0b80b880185407100303010110fa000070782e640e011070304041e00c5030900074041421035941d41030010409900c03441950b419a51020442002e03002403144a02080003000c0b0744422444074403031200c0360900c1e42140009520b402d03400b02d4000307500811640d00f0010401105180701002c116000041518819000380c52411080c030142 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 334925836 1250 334924586 334924663
    0xc040606050c1e03090a0803030a0f0e03042309010b07120305131704030f0305030108012f1303050f01020403020a1a0a080702032205010215070e010f0e03 68
    0x401c003050148940360344002c5441800220302d480d010311605007000d1420300354442c1d0020198004032050000450001c00300c0038601c00d41c40040c04105443c4145206410f40300000c400c0c2c5441d070010030050001c501c0321078240300141d8a000d1100360010110b0f0225014800c281c00240041e17401260140c100f00035040580328202042c034003805281003501e0070302000d040910000380244041400072400c50700c400c003501d0065030801d902c424810000c0c00c1c0500300f41e20a00403901a5400c102000c0c0380b0b004408451a140c4403120315031142001c0680050145030454a07104020f5050024004041f40c01008110000c07201140010b82d00c030310750b1040006059445d07000e40f0180015480381d40d203c1c001d0400751240c41026043c0f42c0e200d0743c1c45034000c9096108020340c5441040020b40e41c1e4080e441c00187c040b0960302c00b81c00300c0d8403142e00c2100b4840504403c44031800014541c80f40102a54031500705c45a1071000e41c10800c20326511038000a00b400101041643c0340266420a50445d00344900c040340c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 334927086 1250 334925836 334925849
    0x3050712030e101d03070602040e0a0c0215070c0f2a0807151205091c2c0112020d0b01140a14090a0e280b030c21030307020c0406 57
    0x102001004040da10769112000c03440407196104600c0c1031000d00e2690750740e0044130040c1900c0c2c0e1a8590324002000f5002409200c0c0f407400d400e00004e0300511030384070307500784400d40c0d80041690842c0e0800c040504007004000300c040002c0e0310f08110000b5400c005885101d845090306142d1030640c4410080e441e1a010503202c050b030740c054010480d400c00490207206403040041d20300c0c1c04d40c00c031000c1134404004030302c08035a08034a8031040210100010451031010a52136442e80c400300d846103422141070707643d03840210043d2a03d142070307109105100c0384441082d2043c1030512400d040c840c12142203801c04100f25144036103c502520035903900806c41c0c0032560b103005182e800c104101d40001d2011810307002c0009042000500c0760060ba580000780c100410400d01111014030780450a4084010107080002410140c4a80c03d50801c5041c01500c1007030341e02030000d0420868800c200030300d4291100141c051355024502c074814002d41407004500c950203940040c02941850400d003c1240c4050b070241 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 334928336 1250 334927086 334927091
    0x8040201031b0e04020304060e030703091404050105180603010e030a1106010b03100e060d080c1609021e070f0203031209070b0a0f030902030c041a040b0604060503010515090d0305071203 82
    0x2442c0c5240c001c000c2494a04058600581342c0d134913460048010144000f03529010720021400030b042581c408151700c1075070050048020350720710a2041c0815a5801c1c0541075211155800d000e11415a2416055200c04028000b2481e000711102c0c8500750381c041540e40c00014110000c660251108100355030041011202c0c00340385181c20071042c9440d1810b8041c162402034288086905a9114645c15030201d420200c2c040c5d03070b00e401ca14419900c1e880d6601c03c8090401c1c003100010190030034401d40740c5840b40c50300c1c10741c0d441c3e040c00764042560f848150200d800013201c0c00c0313076005038800f04042e01600701030346003e4030380b824002081c515013030341b03030380900b1051108003e4003540982c0302c8020318040580341004a80c1c044070f0b20000703040c009840d000507001490311803060300100c4041c07402c0f01071507420b035001c1092031301d01e13014025148114010349010032400c00040000f414800c04640c065140071000c03c4c1000c80e070354000340d0905250303d0141c00044010502c0340c00d00c081064810b46480c85401c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 334929586 1250 334928336 334928381
    0x34050408190b06060c0a050613120c030e0103020d02070602030c070c0b0703052a010509061009091226100509070305040209010605210a06060915120f060b03070804020103 75
    0x280b09140d500144800d01a400124452007401c5080118a0006520030255000b9140c81091040d0088448a00750b814410000304046004d0050844c1c004068241d684d03080c80c50750b200b0041d406075000480040d0103d6003044180c02164a40c809540115030704030940ba520f0140382003098000c0340942140c6031803503082040324b000982004c2200d05015a014502e900b0115002004540400045041d610743d4200320070482190804a0003074410214108141c0e185c40d00c40b1214400c5403803254004280083d81100384003194000c20082c800440d01e00506c9440c0d83c6c1d50442d040328801c040e04c4501943c010b0090038070a1340351072440300781e00c040545420019803500d500001d0055070180300e103100f44400000c40f009481c81891401e030100700000314038040c0381095020400200050b12569000800f00c080114205241e2000b004554840c1d90719031f641805004400c1c03005040003061455055600c05d800a42226000055441540f03a43c80b1180319103440e00001d020b0b64051100d40c125145080c0c1c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 334930836 1250 334929586 334929593
    0x15040b0403060906020904020d05041202210c030c1902101704060f0f140126030307030203060f09011401090b0a09210204060b0a0908153405040819 65
    0x103540840340c2200e030120303000025040800c0244a0b810115800900000d054920b4040c075401c858000c41c0f081c0100e801e80301180400301d80341c03003415002440035101c42a02c607000341200c10280c11210191000d4914100f0790480b1185408240300507100d41242e5441550190700c1c02d000c44115000f0a800c209040380c8441000a00000b002400101155078032240d643c503810280d0312052003951440701c100321443d03c08040e01d900003400d106da0016040742ca1122241e041e030010505501140e000011070454540d040e003500a504000c00c120340100c02e00b800c903803c03680ca495200e4000d000d0084c100c1201ea8aa1000504085c2c1d584c00070005200100013410250394040b00c0302c03080301c03041c0c218105a818803080240790201c0d0346402a42c82420900d01141d519120300050009624a440380c0d0b8802e0b50700d24946464400c0d00700d8186008443da000500003400c4000582c0481400303580c01c6404840030f0481d500107049019090000980125040c80020030412030014120f01c40060b200280000d90f9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 334932086 1250 334930836 334930859
    0x6030b0613031227050306010816030212100903270503070902130e040602040620190302031201090b040b09010f05191203020a03030b180a0c0e0405151504 68
    0x200040020034000203d03a40e0a00c40d45090448400d858070312450111515800c40740080b01d03000f0584240284030000500ca039000031030420180d940c142c1000110319580070003544c4c0c80405008080c600442c040500c004045110711a03025129031154010401c12821003c105140180260744050741490140855500020b41d4411030313101040c0035a40d8114030f80c0ea07010404040d403018000c0d0b502c90050004000d0075802810554501d60f4801c0610380003004503850310b44010081c2030a64000e0700c2d4481201030341180129445010b80112440c052058400d0a040402640030040341c1d65280385108440c6040e003c2c10702c0e041c0c401c44910402e5414000d0054071211207101f03240c0b1819440900c0c48502030100410002052904e038140c65468807424081c4d01c40400d02c3c0704a0021740342086030000d920700800180300c1003e124648108994500103001d00405003034190380184006480b6802d160360380c1d80140c91180c9029030202d03012901d030105100342072540f201c4d10071000364144030038070801d4180b4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 334933336 1250 334932086 334932089
    0x100203070215060d2004090c03060507030c091d0a021207090807080d270302060301090c14030c0706090309151215080604061e0203070815030601080d230307020706030b0613 76
    0x20140c0785d0b2000341d5240000c0080c03042650081c01e100c2c0500002050084a5028521034516600c040c00681c0d1000b00032203640960307004200c1302141e6070281d040540100690580d0181c600e038001031400e118000704907a4501c0c212000c200089a1103018820020306110940083c200f00008001c980f5100b10080c008221001e0946190201020329000030015185507000468001d0103465803940c4420590004e84000342d0080c001c600320070320031200c000c6031004603845401c9800380f507410840e4a544940c040c110300f00c401c0e01040341e40b610101d0741c1c80b849090030482d80103075100d0030380c61900c0f1100001510354507924007980308408c203c01c01282c9030205600768813035446900001c0c441540a18040c250b200c206c400b8030b20520200401c24101e410140c0c860281101a25040107907181001b0160b40c0c940c24020b5803000d070080280b202005024500c00710b003060b140742d01503104241c11110000c1680040310900300503440203030304100d40364141c460030000780c909952461420412034203004420000c0e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 334934586 1250 334933336 334933373
    0x140a0602030c070e19050408031f0302010c020105070204110f04080609030c0604150f0204060903050c152a0f0c0a0909031403090c0916030c0314010b0c100203070215060d 75
    0x1100007030305c083c42c010b24501c00900d040300402007030410b42021032060300f0880d0020f80c10001004081c54220403010414103c95050b902e001c10814035900449054003c1030089800a8540081440300c42260014041011351401c481d6203544c54003130002d103031180280811459400c10071078150402004201d41f40d125810460f0750700345454840510707005100548902c43c503a0304c0858045040f9900c2140c640031280240c00700c43c020f00000f01000b180503d80c01204900c48002c202081d80c07080d20440002c1424440440c02803001c0412907582e04000c0041040302d80f5401c45000a2001c3c5058448040505601c0d0f400700b080b031403613503009010307060741e00e4203056008408000188080e408109a401489024214041c182882000280645211071880000c07034140700035000f40324801d04c10205543c84494004107507910304180140f0540c800000c1440034010701d0144400710b41180019130058650f039004000b010104403100902c0d00010f008584144860380024000c500c107030304030f00d481000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 334935836 1250 334934586 334934609
    0x40b04090f1106190e0108071e0e181003060612080f1602041a121906090c0e010e010801180308070305071b0302010510090c0c15060f140a0602030c07 66
    0x740d07100054200d0042000020f101300c14520304001c01d981c09600b50054100a03210120107488807042902c00b50807192542c00014410030a40059900c1060416003406001d0f00b8048198030b0000d14102d002ca080b2000c802d07060741c09900700100502445820010b007030041c08001340c2c2c001503031a0038040c452040b40503403906000c03904065042170410784602082d4010000c0101090b110b074400780b0035030200035641c420781075218000001880031802d500310380003070a10701ea00c1c0071a41e500c540007010404429241e014200d00d021071015020040310340a0150b20041010561400312030a082d50698107010340d80c1860780c0300c5500041d400c056225042030140c10701107001d03a1485030481b4141504d010b0083c0c48005070898106140d01980240c5c0515411364001c0b02c4940c56608040a483d40c18200400048140b000c24001c2030290a04c50740080d0302601c0401c8417a510841d0f444a46403c0c3c02c00c640c11b0225403207046087c40c00050306130003040c07240091402d14a1900741c81d07444d080e19104070402e418 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 334937086 1250 334935836 334935863
    0x20601060c021504090b0405070201020a230c010e0a05010c021c0809160b0a0305010f050603070804080c1f150b18030705030607080103051516030c020a12020c040b04090f 75
    0x41d241100102d43e2074200340a680c650340d442c0107407406096607028403402645440c000c280d40310b1042c000c54171303808080c2d16601c21044c0e01750a03a11940c0d10203d281e141001e400c0c411208900800e000316075402c51010001c104610303490900340c0c00c5500e42001041558030407a190312410351154000200c0007140c3c204407a00d541c85c3c40b801800c0201251111031491340210001c2042c0790307554081d0080110b01d5508100d142e0b00c1d00b111401042c030fa03004560740036038180001a402031140350303200ea200b48901d02c11760038007001c550042d1502c03a0594101240b00044010380d05a41c0341d52285040329500070862500891a00e00b041d80140b1600310410114814000340300c20f10740302005200014200901152184e140c8804024064082800111464081c890b40505201882031005004500c038042c0040103034540141640140782940070300065000310241800410b183c42104d020610030b035000350056081c403008003c205c0c0c126441c0284110704c0c0840e9480407a10016010200a51040c8201c4416 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 334938336 1250 334937086 334937089
    0x61e150301150605040617040507090216061803080f0708070e0d0b040b0a0b0109080303070305071e09030b220b0628050f041103040633081c020601060c02 68
    0x42c1004110624400381c02c850006005900000400480e00e241e510103004070840205680c2d613805c1030740c0140c682c0c0e2100105200b2208543c1c014800300d00803e050403d11140b40d503850301512424020780c4505500c40e44940181034200d0002c5520602c200f0303c0c0e808514040324080d2404401501c030008014141c030f44e19002e82c0700c8220f0b00018507000585414145007a28110130522801c83e0643c1d901410a03e0120307055004040310070941703d01d4000383d8156916000c0c107e008010003045e400c100010f444042024200c03138908110070390025514200e0a500b14204004044e00107818020840740444510001d101086030b00d0020b01e520100d80c2032140c884030001001c1d0b0010441c18038000e05000c00f40d402240300340c3c5c1c1c01800c4038400c0da490411490090104001c903524100c2903100400c1c20000100040c849500c030100b900070708801c1c410ba070144007480e1444038040703003520703103100c0c00c029804e000321141045540c0c030311000c200d0484e0750742141c000001d4031408188603060520072640c880c2c9085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 334939586 1250 334938336 334938341
    0x7030c0f14030d09060e010207020a0306051504110c070e0c041a0c030c150916030b060d05011a03070b0406210e010f0b0f0a080c0d03030902090a0b03061e150301 71
    0x103030700e4508403511040782c0f03004400145048403044400610348000b14480d04010300a8079079090300108286442881e40e2100c4025080c003c0142000007244a18007441e075880d44903168000c8031390a22681c0352081104081c4c90300500341c0101078403950b410100614070701003c044400751500301c60f200c0801a2000700000d0720340140d42d1141900d000c080350840c141c03000064803502141103010f01450030b0300c0c0d4442441c1c0fa14201040f0b002c051005203c2070011804070350306503401060190010311809600e0b1a240d0071039894020141091442800c1c0041c01d2034104100d0b006050020700062401e858040041d260a60300350000305801c80751134071fa51405415a100a480d6940c440c02801503d650000142c0100a400b008a03ca1802402103940c00d00300750002001b502c2e56280200110a03004007003180c0c201802c1400c8041540b115409001038541842060041d020b2850104124000000b01424031100400c00c48002c0304d43c0c0401c0240d05040704800340c02400798100c0350398680850f80440d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 334940836 1250 334939586 334939613
    0xf0d02070b012403020906090d031101050a1d07050603150a030f05061e090d030e24010303030605060a050d09080403050a0b0f0606040608013305030a0b0607030c0f 72
    0x6040e100800081d83c8031044180c2c940d1107407240e500e0a181026007105800300c0c014418a650050f2051120106a040005c0704000041c0241001c480300141e0740000c0b405e451085848140c141c1e151440ca480641c1b0580c0f818510a0300000501983c6007050b01150301404020840d4220502c01c5880060300d0700c44210000c060342c0c100880c0c000701030481c00d000e5038820055960501f0441741007404459500b150001d0703405a170360100584000f01c2d40d200101e02401000b84540101e0040346441170984840c50800d810140da10855800c95600d142409401c890003a44a0b50280c02c00b0441055181d50040854681c0481543c0c0000c1b0680117080084007402182c0005041d0f12801444406015000286900c41c2e250706601060030340c2e889050140a001d14859600854a0000103026003699a160020003110540f92504020303400003803006a00c0304803c2c020081a0000103124003200c5030f02420003d104181c030118507122203690700801e152100e150240643d09218081d01c10040c10211142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 334942086 1250 334940836 334940843
    0x170708090603090d0810031e1b06090518040f06050903040e070c0b100b0708030603030702190906140607060c120c030b012003090d060216030e0f150f0d0207 69
    0x3500c0f494101e003078580d03440c039080485012034110400038007080e500b4103204044d241e01c07420b2800138013404a034910112034a01c104070380e071700e121044180302c041c0c100d11040010040780d07455010b00340c80c210030f000c443e004410118161556800812000c0307040000c0e84441c0d02d900100002d40395030340e18a4581907008640200c2507610040040c080d64980c0100c2c403040050195041c2202915490754200b10388226114144040b901808444041100c100c00b465200001400303a07403074075a440c0d000503030b4150b00800640303a000c003415050000300300d1481104c000d041d8070501c466207120b80c040040e5450140030401171406440d01da1800c1c80601c14043c2001500000a091080314480c480107000b5189561031180025240202200240c40d181c140144c0c0520031000f0b180752807108000c2c094980c000f803078250703055034080213030402d030204141800080f10f0281d039610864004030410000c0a65a25500501c2624200c01c820340c107001000481d034240c1c1284089550b52502c40300b400010f405a040c024 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 334943336 1250 334942086 334942099
    0xf060e1f0b040b0304050c0406050102061906050d050102040602120903033c04090c031401030f050304030b1024020c012a080306090709060e0f0103020c060a0b011b17070809 76
    0x2c02070440c8004e903000b9445402580e603c6410442808100c03982e03442440d0040c1d000c1000701e00c00d002c6d11400c00c10761000307072100403800382c0c3c450010642c034200320181115183c0d40020300300304095060050004070803008242a00c0c049504000035680d010340319460034080700030100c000780c00251104c01da9805182ca040c50308403c201c4040c1d01400e41081c171902d0422070a0500c041a654809c0c0700b402400880c2c508500417503400c40c0c43d21125140320042c1241c00340701c1040b000c130214190750b5130180704810070441060313118209201e58840750600ba0361034248010028481050b50b80201d442010640b007071a108100c0003030b43c110003040c0b050b40c0381c8543d10302a251100350b06100c98407009612a0740150b0f580103103030320b82e1601100e111480b44960400294117514400051404e8003904482980500d000741c2420030500b20182000c0b403e0b110004215a02c2007801c03001c1d604114120040c828110840900405646520038610341014900e280c0c07110001c0c3c0308c005c10188400391440ca03c8041c100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 334944586 1250 334943336 334943339
    0x3161707090504330306050c040f1205010b060309010b0301110c1c0207050d05010f1a03030403060207060f05091e010c0e060f040f03080d05090712030e0f1509040f060e1f0b04 77
    0x1343c070343d0240f09004c04d0b1403143c1044000780070a0a0001140c044490b4800012003561030058102da02941c2e59804680719505e5a0442c550760b541c0038007a48c0584035103000025442e00c0e0b0001c040c210303405921588d100c04428010702e00c0c00080482e00105802c0314451400c8d42e00c921040482c100314403034110550110702c1074030300700c00c0c00307415481300c40d03205c01e54a0208072801c1180d801406496040788841d600d80d000704800d00c0000d00a4000c0c1c80f41511552010691802090421054840444690110b03510101464013410200c4a844034111003410080248150341c0c01d008003a0410004042d00440d03000036282d021001c41401c560091091200403060700d6283d181c030110651145201041842c104004035016001c08218102220322100801002082e40d9506888842c4802d10096020091440b42c0342182c80c0c0c01c0c020703685401000e200d540d6400804003000105d544c2040003886c914503007101401030b50723a000c448581280b803602c1c05420210040681031460300e8144c00103189290041030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 334945836 1250 334944586 334944671
    0x9150306091b030622030318080706050f060f0d020607020a15091706071b0f0303021b010603230a12180801020c0a03110109060203161707090504 64
    0x40c0740d2022082c154100c1460302d0060101680c4510a9495215803500708420320041000e07040d00f00d64071482403d010a00f070505803d140061064114140c030041c400140d0340c020041d9606c04c060340254601c010112070f041c5640803a0180c1c8883d04414050304905418406560785c150070303901d84a130300420800c00b903074860150401c002148007000300170503911400881c030021045601000074041c00020708855a410200b102c006806c90719402d0010595581d540c04200168400c040240c025280541e441280c00d4440309150481064078170360ba45030a0080c000503203500c2001d080c1c8005480184106c0c0341c8904504e0505000782030044c2440403010210003902d420003408008800320b0b500901c40140e6030580b403800d034400c016001600b60460064000001d000d00c10107a105030703035080009202200c3d991110100d07801551780c0c2144610790448092116404004444443c1d042e00a45140d8180300b800a0440000f42c007540f0b20072500c54490085c0f001c001c0700b040c1c41914020000040103142d411 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 334947086 1250 334945836 334945843
    0x140a0f0612060c0f0203030f0403030f060503010e01090b070e061911030714070f080c01030f06210209010f06050f030618070e0a06021b0105070807060c09080606030d0e0915030609 79
    0x412040801c41c8204d00003180d40c00881070300e104000456811070141c1c4c480d80c08900506c1041800c03100c0301d6560b81c002c201074500740302c0d0b0552000032000010b0744440904094586400050800041180e01c07a00142152211015502180c1021102d8445490b5018054581c2e50103c01c40507da8403002c01c2d15814080030468560a02c4070b19030a540009884200032000c412140c002c40300c4650210740020041c0d44264071026044528980000d0704036242e003517800b03006101c000c014ae00c1c1d18040b0b080500b50b10302604201c0c01803c0b05c920030880c1d07503c1c20202419900500e02c1c1140c90460100003d10162150349116103180107071810743c0010320704418090b00462040c2c0e9024040d002d07001d030100d026400010341040c011a0540c03151150008000111410351200000b100c20000c140b0281000445c3c03030103014100c20054a4100c201401e0040d480c0c54001300404440c403036409031050300c0c0343d0b94021424a04c1d10030142e038006203c4e5a0f03c2c041040004008001503014851a802c0003495031011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 334948336 1250 334947086 334947101
    0x319051611010c0905100e03030a0207050f0a03030c150609050c0a1d030c0f01020a0c0801020316050a08011a07050a030f02100912050705120c0c0a0504140a0f061206 73
    0x39120007031901d105400c03190803100b00c1c040c1c0781c02140d03101d40d007807040b490400f6000804620b40d00d801c480401001010a0860300304245880140e07000388424070181c03074840d611254001044e40c280100380c0c0b4646000702244482040a40300301e02c0c408104100860542146000d410307401010700c4281490483e114071503120000e2040040c80a031503561190410b802d0302040c3d00d500900502c2c42c00065010449954040d01070681544034405540c0c0009096a00d500c00400c1c2c003c00041c0c481c50031054110340c2803000c14101c1c1c1040410010040b54681050201c0c1c103440742c07071060201603101958a001c80d4400e08070b014007280300d103021b94010154008054001c120040c2d0940700442c842505210541d00800c40c000c0081a084042c401d110313200b08054000c99020b40c0440713003100005010943c86030301501401385160007101d44a001401c2c51084a0000d2200342c03000c02048550403120140c0e050080e004c04a0161134860841d4045141c2c1c000d54041d0002840300c000b10741d00361802000501d001d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 334949586 1250 334948336 334948381
    0x4120209060f0f04020c0f070807030b0609010e0a021608030a1d12091513060908070608090d18150804020f0f0d1e0c09020a030e0c15031905 62
    0x1503600180d414240010440d81c5600040e1010f4015100c400400000c0d403c0504040c1c1d541c0300340c1c3c3d1041301110040110702c005016040103482e4050440c01c02c200f000e0001800280110841c80042107003a8004003040c1c0d1090340d1041c0107031030b9580c141468100e50102035002d0301303001c000700921090f54001c0d803040304406a035031030400170b010081e0700700d6441d0722140d0303a0200003960a05c82c800160a02a59210000c0c0000040720302d460b2569007101c00000c12604950005440000103010348003040107488042e082c1c5d800c290b041e03443c0203c0c04a03660b03061044a00104034522004403805000c0080000c06424024040c07072040ca00200002c1c02008100c905910440180d050000030b81450441001c070b07035001801c210b02200890311014545029042800080300d480e03621400480d184415a40141200c000050381d50318a410005062b0f408004507a00e0980003030221404955980c4501c070019004c1d010300c0c42d1a0758070101f494248126030581008c046007003800f044008010403100c034018072003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 334950836 1250 334949586 334949599
    0x20402031510030b0d110f060c060406290126010b0c192d0b0f0906060406050627100201090201090918140a0f031d0f030a080a090803041202 62
    0x25000b28142c6098a08040e04640c5c41040003010800e40f070070950502001a10b852110100380b00032a003030394803e214150254000740180400c000c07640c090b50000420f400c0105100e400041d051f81034901c0d01580e04c4d0306010740c250000e11544200c400324442c40d41ea5112404c419a52044112825841100125030038080c1c400007803400381d00d05a8403515180c000f030724a079821101d954041c0b9148041d007454180f9440309a8441c0005001040140c428444101d1142a0b8184008030900c1c02d50041d0001340f08a0901500380203584031101501c00340741c24804000c080c1501916a83d05201012032141c2d0000d166061800d0880d405420032a0150704c01e995900d5140da80d40c1d40042240c4038205a0140c0f180c000502c000841c400241c643c40f00303c2480c0980b00c03102031a0381c85841984d0080c0040f40032502510070b0b14841e00c804d00d0302d6450400c0c1580c560305140007a10010380c4460034110014030000c0045105d0907020301c204917841c0903024186c1229a00c5888070f810b240d12000203038003288241b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 334952086 1250 334950836 334950859
    0x8070506070b060906060408030c1f1a0f0d0203161e06020a020105070305120a06301b0803030405030d051803071511121009050705041e030204020315 66
    0x24810222180c60b9000540ba0320103880b07000c1001558a0064001948060140000310300c0100500c018002c440c92000102003051000700e0300441009401d522201d844d02c0c0c28140c00c000c203040c20300c201d480b0034116682c6004000e400001620105d29080181d01403250310b40e203020000440e0000700c1980c2074450324240c0c07100c4600c2001880f0181c3e008100050300880816001075004002512395207119003800c0b03081c00400140003002090441300308070910703141e034410400301904280d44600c18124214964030742c1101e110548080c002c07260001c02c1d038544d419542014592440c0c282c0003a04510050300e80e641041c0c20880d680c0e421200e84452000d1601d070120342e00c03100a1407807101e403c092201850034400582c0300c0040707400c3e000800d5040701d43c68204001045201100404050745142d00d120310314240007404549401240d08a903042c1c0b840c00d014054001c1d046401d035011130b00411010602c0b40702c00317080460045040c0c0d1000350010300220a1004010004c103501440d4003081c0e13030480100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 334953336 1250 334952086 334952089
    0x1e01050906040f030c05070b03150f100c03080c040e130c210311010e030301150e03030406050405120a06020a050406170415020a09150201060312090f05012a03020601080705 76
    0x7200150350007072104040d034201100090203008010310b01ca014006503151070b5510b00c29110151300448000091001440041000e031a004028400c5910251950544500d20001c094040000e000002c0c0070310490742c000a180b40c0082003210007800000000c99091708011918010000802c0c2c0200c0740c152103c1d40220f0710351202e21141c0b0386001c071100a01ca100203680c405032116a8032895484182d500c0721004d10749000d0030401503000349007080271106d4000c01c1110041c804515041481c0c4260801c0204000082d0700a0507201903030801c42d1181a910301c5642d1461500c2c0e9013617030040a0600100d803440e5900d80100143c4121503941e1641c4090301d400f92078054265004580051111101000c001b80003001980509200b54090422001081d190005410701088001030f080050b91640317401c0c0104548580c2881e000c1d8010b050485c21941041c501e1980076a140c0205410030039203a11207601550b0021111060780362141850300e100340542070080d250f81c0c0901484213903104215001480c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 334954586 1250 334953336 334953343
    0x9011101090201050f0309190503090307060e0d0201030b120a061406010f0f031d07182d090204020708122205250302120309190503030711010306081e010509 69
    0x401e54140d440503e000ca850840c600160030140000ca11071040d004801807119110303040410032801140190740310440c040400d481d001c2d00350030101c200445481140c800f9141c6401051001d030b42420f001c41d51464810126515294000c0e8402503842440111010710080e50b10440300300c0c41c510503481c0c4541c0c1340001980d08104426084000500005948100c0c0e88280e204a140c51450100304131a01540c0c20000c0c50302d0400d4000014402d400d030020300700d00c01503100790061098030b03460f0042c01803a031580d2080d01c50b241d54160000103481d054118210340d030b16412a000640e0000c01591509000c0071702e1b00303800303d0490742c0f0310010340c40e104050341800d45070f5078000180313502c00018118180213404255401c400300d0224030304c40303a040d400480103a0703039188034000014082c1d00443e2191a100204801444030b25180e801100901c20107200d03a0320701108403400c158228000074102200b5000480050100da40500d4143c010b000c54030101c04002d200c03000c0b00d664980028040707600d89482c2c0545 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 334955836 1250 334954586 334954601
    0x15011409060315060f100314060a0e0f19050103060903020601081614030a14030c120301060c2a090608010f1104030f0611370522090204080309011101 66
    0x81c56800125403451502ca0051203a5004102030701001c030703a17040040403444c1000941088408a0748450300388000540b8052959408541101c10440d030901d031404510321010080e110740d000c41c40341000074203441480b8105c00307100740388003000704540d6a42e0b080000080c0000401100180601e80000030001000241228509128811240b01a10b45440042074440710a8065018080c90300388201056150760300346410240701000c0c40d51a12141289420601c0505500b5510300c020b000601840d94000780034208a903200d0046405511051980c2c3c114003818591002c07106041e14001c1112103403038001000712850800207008007515841010243e480c1c2d110710720038070403052104102040790450800100d60060340c0000d00b05403079036988552a440181e0480c900c14000c9110000b038041002800b42c0c0301c5214481c251640c42d1807400502a114201041d01ea036400210034504400107410390400900c24204d08645d219070b1034901039207a401c618201c9010862542110042e00d038107008888 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 334957086 1250 334955836 334955839
    0xc170a02061807150207150801050310020315040e0114100612060b0901180b03010320030c101110021801021606120f06030609050a0b0a151202121501140906 69
    0x200d11030412041c03140010b56103214001718800c4040c00101c80e8600740030283e00480710f54601c41198101005d161a2140c0c5a00ea01d0001c2c8c4100204001611402c0d16002e202600311404a40d0248401c0210b0140c1260850f500c8184940800c2c8295006d540703031034000300c444603102c24240c0790076201c8480844025100e081d079510002c00c00480558030440205c081d80c652415607501880e20b03949645c0040e00240c00484000140f030841041d40c402c468500c0805031402c40040640880300300c0490010081e42422805200d038030340d02c40f454400e081c420610030001c4a0000c5443d104140a017480e00c8105054180c050f001ea104211000f081e0307442e03c8001d48090b070b04e42d0400142080800d000a10307070f04c03410041190342d0700008070004105010700f414081c0071340014002e41d40c2c5810b0550780000c0c0549049407480c680307402c0d0300d480f44210001c80200c5203000c0c20046105058008141d00e906490401082c901400c9030b04c8d211540110122410703900b12250600b06603981c001407040070030050b250035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 334958336 1250 334957086 334957093
    0x30801120f0b190b010e1c030320130f0311040905010e030a020304050a0501090e04110d02040216020109060516080c0102090901061706190509070c020301150519030b070503070c170a020618 83
    0x808980301d101c000407c14030038600001c10f940c140301466102d5200400000154000250311101c0000c51118030016001c1d11b100c100c1b00d140707599241e0b914484044040350080351100303041014800294032010720050018150f81e5200140d0100039225402030080911400d003440740410f1175481101e43e136040d40c06100c0306d0241e82d00ca0391140c58080520f2046182d01481d0b580303100006807a180003801a1520310120606e2503841440090620401500003008020052003402c0f10790a0005100e142507402c100403998800d540c0041a02a10a0211541d0801808800090341e181d20109115811038004501a22911001c04001c030b515945e0000f070074440170ba142c084c403440c0342c151070954214038241040409600540d0109003903406041c201034102a890a08002d141403403401c00006840300da0300006034908580d1600e0061002610350f40c10408040300140c6a9070192503008110707038100154142c214142c080124030303980403040386001400b50502241c01c1072080c040a020300d02d03144010303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 334959586 1250 334958336 334958359
    0x111b06090d14071b06030504030f0f020304060e0d1403070302060a1526070f050111210703050c06010b25051209010903080f0408070b0403030801120f0b190b010e 71
    0xc41105420608042c0c91404d030310b20419889402c40c21000c0c004000a031000700c1c1c185031505010384000f80320401601480301c1103c6840c441c2d6070120446040c0c8105042c94800c0300016404a03140c0303084004010943c1000d442d036005480c1c400400740828910136030880c0c10070b69a9002c4c0d0020303200e984503076000c0e0041035a8240201c075000c502180014001410048039142d10b500014604201a40801e000310b804401c140200d50b80800040c0b501c0c2d0b085401000c1000142c5602c1c0d0f8082d151140076290a0804102030701010312400072540c408100744105c030079550f1141f42804183c0d00500c10503000c20005503859010084424004083c0c58020018000d098517200112010790302480e0b0381410071884000c04000100e9103c054020b0b8120310346410340341c505001d1f03036915104040e040703001c0d130031400e2208000090b400f4002d241174841200400e2981d003181d2400440700b1281080c01008404894100080c9140e8400c00c440c03411401c101c14400402a84010f54801c0e05d080d40c1c2d2600700c0c0c87c0c41503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 334960836 1250 334959586 334959617
    0x61608030c07050a1412040b04092a020607030501170604150213030609020a050103020415050d0f0c020a0209060f100507051908040303080a0209061804111b06090d 72
    0x2541d40321101565151500810399107203428000109800c461901d0f0b10003004200e2807080020038192840140340d54130f040d08140c45a0458060303481490300c4580c03501602e03034170561300c018004101c074150001564075406101c4042d46400302210b145001078034000001501028a40554052400c801d01801440d140c0d0784440e46500b5601082d91a499020400c207149901c0580310380c80218001d1100040400341d500c10400c1c0d515095015a0400d8010300090102e0311304204c2e0545a03c01e503003001382d6242541c8030050041c1c544605c50120a0b458079030321104454011900d41600c52017110415044d41e6144200404c40d014165501d41101410001e080d1081c0034100404505000b08111240350080140100c1016400300c4119444003021800308205600440c02540060200301c040d4207103200c00b004038540340100064064412580480140303203848039800b915110351034851f0aa030310f0300080ea4040d22884400310b94080d07032083c80c000400440000c10070220030115691541200c1e0030210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 334962086 1250 334960836 334960853
    0x1923070f020427020108010b090109210204020703030b101107120303022503111c12090b0906060f09060f040b03160e0a05060909060402150408101a0616 67
    0x481240c01a5032070307440010066079460348803d9890403c0e0791031110320040c400100000410b900c01c00c0c2000041c080101141e810640d120142c4006e4100e0b1101d2020040011000c48820000650010320000d10a428035600d81c010700c4001c501642c14039a0102999800ca03002f014003004410280c00800007402615032140030074103464024503003d03041035641e85200c45004d98040006542038041c004410406400880c86801044103030041d103029480c1e10807401c81100840c0c0c45030104858007030303d18007080d01a4804200c0d03903044035100d10700d071800d10401030b504da000740c4905114001128018140345442e05059200301f20242005101c892040c0034030016090380f03d212640350103890750740303c108414420004010000b126506110341070421401003124000350146001d241d61030300700a600030000074515009a81512103401d0540003155503113842c0941c1e002400035029480320307040350154030f401000446903941c000307080c1003029004212941c8103450704003a61362030755050b4402045404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 334963336 1250 334962086 334962113
    0x1050d1b14071718060409020a1b0c14061603080601020c060a2a020d0b040201120204230402041a09030601080f0601170c270601031a091506192307 65
    0x4000404d50800640040e05c83d401503002050815030101d1260502d80d44841c91448104c1c001d040010185140c0d22458500307074440c00381e000a0148a41e080e8005d4490000303c0e02c01d0490000709036500001e80c680108040402d0324580c0c014441c41800e454180b4204007201c020b95010740b22600040c1008002c050401c034026081e0b41d81c2a194004140940c071461040e90486104200300356141c07400c5c3c80050305140d500350400c1c1c44a4410b01c0203108102d0150381100310416061045500302204a000502078803c0717410803c3c046412100780c2403c0c03030000c0d01031316034603030304805550440e030300c6080c81aa1010011001002a370141004104030386541c24000b480c031a650042e140c4007a200c1c00443d91140308a15100c500040011010a0726200700007404d8120340c00f46410b0141100003864601103510301c101c02d500c04d44040022408a20701054006c100b6000075100640b8ac800e00142c0d84100721420031030030046489440f0700408409000d204180e0030001140c1c01d810400d45444401444005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 334964586 1250 334963336 334963357
    0x6061c060b0f09070215010605040f0902090d05011517030309120313051603031b03090512010e0a0f02120109020102030403060f0e0a080c010e0a020d020f01050d1b140717 75
    0x4942c00d942203500d807104510b210303520036001441500705148008061180592000c000c11105000030f01024a15140b07601c211424002d0140c0c4400309000011341d035160b40d00c401095580b80041488002255144d0402116003144022012100300c4481a0322484100c4143c901900201c4490b52040300701c00145810003820080111205030700e40c0c4444c40d00c200014045442c8014130310410400d5481340c81904407103402001c2c0b040c0c0066079500a001030300d081c000c4c81d21980c0c58000c1d414650609503c022030401c0076200315540030b40301e402c01d400000d0b0070840603401490019000015064140544201c09606900940c60705240d44c56135001070004008d1b07802c88070345601c052242c0c11020402c42c810309004401041e039400106483c142111407120048140340c006180440140c2d5a0400541800d0740540d0302958032100000122454454643d460302c040d0720b0a070401c1d100c0444080c80d0307410464161640100b0004401c3d4010140c09403c1000b0061010510718042800402e006861103188 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 334965836 1250 334964586 334964599
    0xb041a3f150909120301031a0106020102070308060603090c2d030f0c04090201090302191503140a0e03041a03041502040308161103190c0f0302130b030718050906061c060b 75
    0x2d01450210917948282d000765140a89445503002820000c50554018a9140000c52809883e517801600c000001054103205000c0880081d03120314003841046002c031b00041221400180001601c40041c5901402030074007119450107000900380002c4a03d81600c0090043c1040303503c43c020030020b1301b01084124100301c94000f0010041e1903603040007440c0401014035015440c100b058a9070b543c1082612030040506200380c0b0408055240003454000c0c030b1a031008030700c1101c0e640c1214990310480c2e020022082c03908001d003a0703282d520405540134502c240c0460081c0801c0214180583c0164003002e0039120f000c0180528001d0020b006640b410b1080b1901d4000d01000c0c000642040010040042c03001c403003c0600b07082110005c0700b080580410145030301c5e01421900462a0241140150281c090342e64112500c0340d5000c12004e0003c1c000c120031000c0c034002004600000e01410759440140d44154008503099203010711080086105041409a0780826525010041d052150040f1707080360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 334967086 1250 334965836 334965853
    0x6010306090318030506060906061806070c0b040e0915070807030221090a0b0a0905071206021e0d0c0c02150d1d07031b0b041a3f150909 60
    0x1d26490f96000b140904007420807487d004007484a0f18000030905445400f0401801d42c1040c0c000d10180040d0006a46041e1220850b1804001c5400c4c07a170003407000750102180005501d218050341501c2402c640e815125103050810581c481070300c041d10058045000040026610307842075000e00903807003000200c203580d04500001c1138070b04041941d501130301e500020030042c14008141200c0b60001041e4008001021707540d256192030322401d0060345100e0708a040810103000464040e200c80424920b06000c4c4074040282102181e80a26030300d950300303824004c2a0f06110f0091003241d2800344c000c0d026035545601d580300002603602141c01030b607a240ea20700040c490710303500404c42c80003014150300030191141942000003843d849120000307003c5403d400180090b090000940302142c541c0d80d0303032414640643c110100b05000e0300e4951600d0300d020301d4041c03101e44c0204588002c1248070f100c110840307a404c00b0b0a00031603101207503a5a51003841003541621070502203512640702c486001500d40b500e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 334968336 1250 334967086 334967117
    0x203010b09070503070905030304080c043303020a1d18030403050105040c08160b1602120a05010c0305060f0f0f01140d02180402190305090c030a080c060105030f060103060903 77
    0x400c00c0ea0700b0000a6404802c00c9482c3e6080b28844000c0e2000720b0042d81003503d4044160360316000442081e0155440c1d04045550140c0001c05002580300b400c2c0e501c41404916036283e174007807554401a031146080c4500024002c8500c40350036225440403884004a503981a44e00e00c0240c6003682500580c4800c11002000ca031080c0304560082d41f21b54511504203160086241c60400c1c40503842480100c400400c20402191208580c1c1042000d082c0664040e21400056800c2c0140a000903090103411150000c00c04194005465100c4c01d0f1030070040d82d168141405804441040e00710b03042140f0b00f120301c01c0c170b00d0105003000d01460140b40c07410740605011103184003600003511011002d500419400c840340000d0500307108080d01078500b10b05084003450400d408042030021002455902c0b00415140c0c2010b02000c03800c07041c003404542c903440861078040c400d6406880d03800454000c00300040b03060300d40800c002c0140c030118801030420b6401c2da10340200908043d4011070500950181c0510070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 334969586 1250 334968336 334968349
    0x8040309080304080109050c04060f06031113060806040606030c14071524080102070c050d020109170708010b03060103081902010906140103030e0d02030303071d031606091d130203010b 81
    0x134021501c00401c49003400c2c40d00711324140300b13840001d1080c1c0c00d05109222081004041c8000c6680794680800c41410424400281d48150002ca000c012031802c0007103011504880f64a01580040d01c041050fa6a901021400c0b00c3c072107480c01c800900c1089881204440e007038007030b00001d4040e41e2484004419007071310344101c41040034101c21480c00010603d81a030482c1d607811008148050084d480c0c88013036503e0f5035443c2c00601500380306106603d019810741e441188840040c0a5002e00d04140c2c05000c0c03a840da9a0a0384e220300c940c1982003800c2499141804038119040300c0d070084004e4101024065403030103660401448104665030392078000b0100b01c50f070080071040101c503075001006504508008003a450f040c08002e0040700e01000d00001603e0000841e80c1c08110351034010074801c0002e07005a5964041018958140311ba070b01d240225418154091040344c01c1600c5180c04150344041216481041c0401c621001c042c4000003501c5040c00c0c0c06001d407443c03000740002144006a40020032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 334970836 1250 334969586 334969589
    0x130b01050c07172a0607050c0d0605060a05060906030c0307110d030f0c050310030201030c020a02040e0c0906010f050a0e181603050601050408030304152a08160c020108040309080304 80
    0x242500352401510f401e2030a01180700c292130003d400c0130b8450346802103800300051a90115015110014590302032103401c2c4900321004000402c850b4207410305003040000b034501520003510074141c4450004480c80c0420462b800c1c02c80140140f42566203c28002019400060880c82800340e030340031008200c0414840070751180e4254800203201b014450624085130020711301202400740400911803401c0d250500d44e41241c5d824600480c6460078500120b0400f001d0043c000c0d00a801c01084030000b8002180640140c0811748428036103030b864400440c3c011103100c4a14010940c10051625001d214050345800600c010704134901c1050a002c4503351100100d0325400e071880e0400c208490f955141c01b0b050303000502443c01d00e0620b400c090703602c0e440c1d00c00508004d00d000ea0882c004001e40f9865000080344020602d002c50350284000030400380e24807a0740d0301b14000307143c4000281d01d0755450503102501e401c0c56690000440b0041d401500e540002a20540510145020004406804000174070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 334972086 1250 334970836 334970849
    0x20607050a0309061704060c030e01060b19170a0f060b0d020c06010e1905150a030305121b180d05100c020f03030c27030106141e130b01050c07 63
    0x514201c8504004001081c280c1001040040200001c080708900301303075168020390407600000d020f18040c3d038150000c000300700c0310b400d86500f0960005001064040a0101c5c1007882a150f2a140f0040c00c007180d40c416082c0114900405000100f0000c10345540a8184000103003800105551549035202164005600315581e1680006a81d90301c1e40741402090300406400c0b041c0081410070604c034240e240c0000c688150120b64481c0050280c00d4900d8007290728020150110b584191a814010003580c800e003d000c0d9581e00c54004280780b02c0d45860b41802c48885111041e0a00f8030340b004030401000450b07591a40000d4500b03017040414030502180038640064040090f003206540302c080e091990f0312508102903081070003048461061442100c0061090051280e080300141e205805120000301c4140d42540c0390110100d064040c496440040500490b4054200c08040c0d56844a0380068005a5005803112130a6000086c82d41c00c41c80c21340c981414080e080041c820402840c003401584904c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 334973336 1250 334972086 334972093
    0x1060915050f03070812070218070c17030c04210212061801020304110909100504060b0f030d1d040b1c030f050c1c0314070809070f0e060607020a0302060705 69
    0x40001d854a1506a54922002c0d0090000d0b6840c11401c2d0f51200d00d82d4030b0303c02d00c0c00c0000442004664507420340303650000310300841400504140100400812000758116210012240a5002c080010040c2c9100e84e81d0315808a10f810305103c1a08015800c1700f0940032918803a01d0303003a00680c1e80001400c0c009441c05c00030411442c0c490b0b40c042002c0340e00740582c0802c0c2d10400134400411500c85050b0250312003560382e040e207074036140f00c903615000300c0780000114240390406010810455800a0340d4105040390022416842a810103444861100c001000302d4990303610302c0d0804156040710005100020700c0080d05030110004694200400d926107003d2144650f014010560815403404040001d0303d400c034140b03040b401815554024011900c48200101c0149154080c442d40101504c1024900c0c4c041c4181000b100161280e00181c5510080303010744200410a107804031940000c43e1001481101d96441d01002e00c401a8071030113090f600034048002c0030002da210b2000070001c2ca803003031004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 334974586 1250 334973336 334973339
    0xf120f0c020706090b0d2a030c030b30031603020c031b0603010b07050309041b0e040e030d05041a040507180c0c020415030b1603150b0703050c01060915 67
    0x24203005264103d0020b010503200140000101030003610254507a595000031303132800c49410204d059000e150000c803500c0c5010392241c00b860349900701076080c03c00e5407010b010f22050201000820081107508011440100085503003580c0d812010020403500b84044d2442e01070081c5d101b0240f01e2000d6026030150340440018282e07810b0801038000d596554030815000d040e90340b0005604c43c030043c0b1a001c04c800f800700701f180901806008440d66035800070010800e0880b0203440c41a02c01707030002d030f480200e08050100c04d4203040c94000c100c00c16036800c026610340119a840c03000180005002500c205415444880e05400501d0696010364041c000a084192602414500001854004090941c140b00001c50f84580200e039030100b02d81d040320701151010381e000c000314000001c2e610107002d01d41003030300780569034111201c8468003454aa4050103a021200a0264600c8051007800301c1d203101000b400c1c010a00c2180503060b8118418008902c00790340340504420b8605101c52200c00300350380c050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 334975836 1250 334974586 334974611
    0x43614070807050f0f0d03091805010608150306011a07050303071e1b03030b0d061a120304050306060f1306080d121803080c12010305010b030f06040b01060f120f 71
    0x40b1401070904507143e8a00701001d6002c600e000d80380b828104d000b088110002404c041c051000b00020384000e0b000110141608100f42c0c010b45400c0c8550008152003802045400d003121b80e0100b0480b2001d40140456480d042032854403196400388003150120502901c00010320a01c0110f00032403c0da030b20207a2800200c15080200d03038907000d000c02489990f80c0090520700b55540300b802c40c0b603003500300040d6250001d0702081c0300c0d0300c48901c028901c3d85003030300c040e100002e01e440b107062492050f2284c0b96508442084a99a44902d025095043e800003000401600d000d041d420909a40601304a0740315030516140c10540d00240c000d01700300c0d04070480c03110440c0e0f4003628603044804850f505000e60310540700e048072100a8254040e0400528000061180302c0d0107044804a09084420031451340c1c0d00d0822500902100a080d1b1183c00748001c8410b543c0f82c001520350085802012001203646400019102081c0307815080060099541c400521303003481d84541c000001f0b1149001c10b11160f11407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 334977086 1250 334975836 334975843
    0xf0b101d040204181212020403061d19020d02130e0a0606030b0601170a0b060c030703080a050112030206071206050a1404060605030c09040f09240b0436140708 70
    0x11490020004401882000314220748150805005c89017071010307250483c1070144000c0c1c46190006005c01d418201403e296900d0452100c00180703c41003540c4400784110070351465000d0014000e58048a1080a00054681710002e030741c14001500c800030f05801c5150756603082840f152020380c0d0480c0d440c427080051051880303000703a005909181000030205900341a80c40808e0182a000300c441d501c142c098040e0700c48204480c0001c041c501103e403101c40d58640104083c0382180c450705c40f070b803d005c00020f035042065042c9149a0340358010300610740d1941e40454020084419001c5110b0311020000754580303551b00350b000600007803803d40080c40262014841519040d5200c03a0410104004200b4034082c140705035020013100b182c011840503020b850082c05860803c0d40900089004803114400c01d00400d542190410300f03200502800c10620b04201c110740001d240c0c40050228800400821981c0950386410f019620703021141d800c031a51511800700b82ca046048140794040c2c0c5041c400000300b00f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 334978336 1250 334977086 334977101
    0xa08100f0506060a11070f290a050901120b0406140906011e0c0204090506070c0201110109020112110c0a050f1908040b0a020708010f06031401090f0b101d040204 71
    0x90001c1c8514240700000c2101840b0b041019410024500c0c183c4c0880d46040c800000240302031840e801249840340c01d070440c40900d04400545840c042201c083e40d80401c003050b20745007021750b100c1c01d080a00900040d03030302400c290130401e40b040d91840c2c5420613544910075240944003007540d9496200c8800c0078413244603c00380900303040c44103800c45207a4400144010b00c0140c4010303e400e00012110b0b20106000d40b807620001049401140300b0050f02641c42840c601d0424000d0360340d4282d43d10103910280c203c0d0103403a806400181020b02244502100d070300421401c0242001240c64115005100e0f410100760403000c6429030084600c03242c40210800a015403040f0360704d5100088103d170380c2c4808840c4281e1240303c59004001c5600c001c098000c1c40560300400d823000081c814001104c00b100010721080c001180e1a08405a5010008105201d0045000c1d440003c00c0c106103515120007482c00001000c0d031892422601010840c1c16014100081680c545c47c1980311500b400e20400c070035150030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 334979586 1250 334978336 334978361
    0xc010f0b09060f04020d0209031b0315040506150a05090906010306050a1401031103070e090703120e012309030d0e030f0111030c0a0201150308070b010b0a120f0603020a0810 76
    0x2140600100350b4441858003040c91084134010794506061100c10302a00a500e12540c0c9401204a00204081283c0c10051145011000d4980c034010014120185032001d4034083c0542d48a440081c01444200035041c150040003025811000c2d5a00006503002004842036401c85c0c0200004108000040c06040d8002542c80d1050281c032151307441c2904005414840940952070f051068403c9803014032100000d0000102007056601d000d008866a03010075110483d90507030f051100f03944452051201044c2200140d40742007080750501118841d8611600365003240d41c0041050380207590f020408241c490034562140003210200d2000c06003090340e50003002100c1e0f41814600c011180605013103035030100307040420640b41c112600c0304a005202140e0040c24405500710084140a003010250000c18443c1e05c500c140f580c0c0b15070b0001c00d00d000354035a413004141032b4445201005110b030069400388805190020f6078503a00c0d00050816170b240d03400f440858100304080d0041909070300511100390b50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 334980836 1250 334979586 334979599
    0xb070e040e011824060e010303182639030a050604020105070c05030303040b06030d031103060d050c031b0102100209060f03130f0b070e0906061812030c010f0b 70
    0x40e060342840a000c41c103c0c0204540c8107030358626001900010381d40d00420380d0a90800c11152504002000c040c801e020550205240e4000030181801c05035002e419a010104241c0c80040081094010310031406041d00c0a80115400400b61541221034034a000180172100f61060589100c81d03110020f41c40c49282c025000030201001140e00010015006a420b28015a171081030703051a91054403542c00039a4580000401c3c0001d02081d50f00f01800f43c81c041b825141000c1c800e04054003115040100c941c101d407010b2000611603d4111804070003036000c0c0040c0e4844031010800a414440100300c50b825800103d11084240d50b41041101801e1040b1030381184bd00307580500044680c05544891040274200100040d201329078040117a4107158000682d06181d00d042c0b41c41207400c01c0132110500010030b004281c0c9140c0c0b500520413802108003070206407500404a000c12010a017000d11182c112041059030384001e90100020058101150000101d0020b160441c50565150510140c400c0c42e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 334982086 1250 334980836 334980851
    0x9040c140a0f060e06190c0308063312010b03071701080712060b03150603010e030418020306010201090b0a020d060e0705090906040f060807050906010c080307080402030a0b070e040e01 81
    0x50391803402c182628240d00305113250307140810002e0f406200e1000058801260110401c0c2650b8100414444281c40317600c1d0040c035680e500c003d0102c0220a6069002c00c1440100950442548840300d0418800182800c034504000c000c0150725100c42a4002850220000f0420580c0741e4010034071142d500411200101d1549010212540c841241c001c0700600001c070340000742004196800f075079103584045d007600d11422100001f030360b401004442070b902950801980d0780d11144080111400e851541203400c4170010442d40d01002900020031840c1550350710410783c000b107814800014480c1c1c25958001d030b2307102001c03980380050300c1e10b41d44070359200440441400102e42d04403080c0d5840b03060560744403601d03949840005002d09440d158a0b50b40620304000441d80c0780000c540a0180e940646454580c5c0d100c3e50011608880041c4000e0003190f42070002c201001c0c4107c2d90300d80c2250000301100e06d00c0761981c0341e90100b80415505603012440e140305c900d13030381e0a06000314403409444070001c02229 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 334983336 1250 334982086 334982099
    0x403111810030809130e0d0e06030601020d0c051207140d0c1205070c05090a0c1b0308010510111005090f0708061501020304090c0c0c0b090a05010f030b09040c140a 72
    0x200950b0000030b03c40792000c6000011034407400c50b00c195001a80703200b4000103507100d01d01034840884042101c002080c0745400c140c2804d22508032401041c06074014240e8036412403046451b8070000e081100c41d405040c1001c291441c088001d400f01600603903040ca038071103610955074500709100e01a14244407040c590080856000f0142803c210b400f42001d5507220080c0c90000c5030458103403c800d9009191000780f00160711194010b500720950707a04e40700c0c00824a0704002e02c0c0d00890b40b07001000110a0001481141046250a07010b07031020f00748100030a0000c89110b0402260503525100b60b41d440c1c0c104a18031004000c401030842d101c00241100070305103000d641e00d4000c0202400c984122180038001c050344204215401004182010012290b100000410804224000b950103640f070050214561140e103003200c940f40c500502c41c1d544603203820010340d841d5038200c5030482416a031b48090721751030300c988034145e208a110b014003403046410481c079107078100031078041b07140540c01c4002c003032011303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 334984586 1250 334983336 334983361
    0x6180601031a07050d05010609080d0509030304030f0f08070b10170d0e0d0b0c04080d08011202040506060d090c0306180c030209040507030804141e010e0d11040204031118 75
    0x2c0000741032460020f651082c00036034091080c0009040311a1a102c000140c83d42c0c0040c00390203442101d4242c882600d49042d040b240c074010a504946d00d904201320400000700c146165900251080802e4100c0740761684840f0f40c150002241aa2085000310400c00d035802c110310b1400203084041c90801c89445e9a1000325030300d9001a0050301440207200c00b5003090382e01c1d1840b410f0a43c0d403000b8a1581c9150011161546811501c140c42c0c061103400140c1e1902801034110b10b05070b50041021400c2e8121a0b0204070151501511054101c2010004611100c545010b401c0041d4082c264811485266103042c0c1c0485c0c081c2c000310640b40101d443da00e800590450b101600310b036011039001406840c1c1341001c83c01c00449500c0142850400100002c440d401d40e01c0407044038004440c1071200010703121890180d0050800d03c94009500c444000300319140003054000c2450090610b802c034a0b8981002ca01282e1043d042550b0446805200280c0340c41e0980d54150602d1300d14109089504040720f04448 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 334985836 1250 334984586 334984613
    0x50f01140711060d0c02030711030106080a0803100b04080c0f0141030f0a06060c0f080c100c11061e010b0f0f0d050919030f0e03070f03050618060103 66
    0x100d8a1006104140e42c1c4803c155544004101810070121980890103035584c1c1c0142070407034044400e004108401c1c03030103104a008803010400035015240d80b1b5039400c0d02692006003000c1d030424580c0740c04545098041e020300f0140c00041c005001450340c4004000d444030708954000d04010701c2c4c10b0340e850651074031103003c918001754030144061100d06461506110108690100b1040004010000342c004c0c02d00c03269019000440c010003805803075090072254209518005003982c8400300220002034039040c000d08981e580d403819640691342c0b054040013a1520300c06c407a00040e008000d1281c184000344102da42100c2e4000301d803a280343c01e616400c20100414414518200300c003050240802d6600b10440b80c205208084080e51001e80240d003000404054515002c0c9200e482c54002000f46c1d140c180d03c408541544601807010141034080305d00701d082030041c54250003000b00c0010643c03040c011303080103035104602920062422808241046900c8108810668450300040000c959110b08820 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 334987086 1250 334985836 334985843
    0x70e010620060108031b01060b0313120c02030606270c0409060e06030d0309081605030d050c1215130501081c1d1e060307030504030e0607021e0307180204050f011407 73
    0x107280f80300141c00c5004188560010508510000c100220441e21400d92f01f040c2d0310039424450700f01001c980c00c44048402d4000250541e001c40082860307460043d000300e071814104010b00a249403000f107101c2d016036082e2a00c100c0403801242c148448030040c02030a000c0c0a00114030f88092808a00280d5a903c0c01c20b0f503034003419602e24210702031080c56000c42c1ca4120004030100c00070004d91a103560384c0d6001586500105140001044e0003081b441e040310001c2d440e094500c001a11501c80f010001503201c00e04a900002498040e00c04004c0760040317034004c10213071000d040040d020702c016181c00b06176140c480302000107400b1495680c1141e000540c107d2041950042e82020913901c12500d541d1684102581c004004010031100713640c50f80001e84604c1c4681d6401e00600d012006001c0180a086002503010132069110101c010842d10001d60382070f0020110342410b5950081c80c002c6034950280707110502e0300050705002d682841c03d00d01c8040802880d1011400c45200c0904140340280c8500a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 334988336 1250 334987086 334987117
    0x18080c0f12011104062321071e030501050315010602060c130314030702031216060203091608071403060115030b040b03061306140f0117070e01062006010803 69
    0x101d0110701c02d5002c050003030700c40340351240e50f5511550094103404500f08400140c043c0b0008156440c1c5480040c1d031000504142d210020b4000341f602d1160321540208503100b0030880502c00c9000d1580c10708c004c5141e010070b490019181d41003605240c105010084085000c03800e11004101540e4005101640700c00d59644440c1ca8800d02c4c54011140c06003940b000c1d00303c02e0141440018074a0100080c00581d100310126441d0a505440004182c041d4100e580ca0301d1407000c2080c0082040d42d00107603806042d6000341c0320701d80003000c8080b01c000c07244d0f00404119030040c20107000c811620a501c51000408a0042c078a66241c56560316560072200c180004042d05c505c002d204a0312a42c10400c1c4249000301622024504400300425841d0341c0401550100e050410000401d1a00440c0c540079400390356010102d40c3c02c08d205c03080e002c01c08207500d45141c420003100051801441059601a21181d031301c10300c03000c1102c404c01d104003c0708003023003000b0340043d03004004c2c1400000803a2656060403192 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 334989586 1250 334988336 334988359
    0x411090112060302030604140f06041101050a050f0408070e090111030a180f0b1009021801080613020f040302120c0d03080901060f0e011a03010311060306040e030a18080c0f 76
    0x1c20280030180d00c000c0d007500c2920140006c00107003040300140d400751202216440540c540f002c40e034401003030380d01428140768051000004d511a00040040010a0810b1460201011039120039035105034440c03620340c1c00c10302c403d015009812000070b0300000c042c0b00070300c003618001c400c00050344006084840096a03c200340c0c6140da880340311500500740c0208980404914500341402c8405080310455110200c40c40e0204807030b6103920a0394280303070500c0301c18081154100c0040d40c1c5148080c10340d07a03102c0c682c8805070703401d0222400140b1845c3c2158010303a4171a840c2d441485640880091700e04c006070404070415031a40c0700c405000051540600c0c05008544942040c980104403980040f9014070811402092071600750380c101d8101c0d11080311300030001c8001090240a0701080c000280074400b400b090540030710300080a503030415401070001508000c1030898900d1f544c80242070102017001c42584041711413107001d80c440140001c0000e0101040000c0000702ea484481e01c0c0244101100002d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 334990836 1250 334989586 334989617
    0xd031b03170f0703050c0a020a0b152d01090e0a240602060405070803040614030c04050901030f0c0906050609040509010e060103050a0b0c0412031d1c1104110901 71
    0x2164504607418100c0e484071800c10780081e03880c0e0a0200d50103000b0030305150118030120119030031244c009943d81e02a050300500d0780e490010956014007901903117159500b100b9000c7d543c1d14407204428034501c7c608414042168540f0004c401d40190244c10311000b18010001c800d02c41c840290f2040340a540040d1401c0d1145840080b00c0158542603400c4943c40b1010560507000a01580aa80a081124080c070b0392074100990340d10441c091400040c038000170b0010444009009503400200085141e8109500d8402182c006a0b090b48207881900d08000030388103010006a100d406400880024071900e801c03c40851250b205048400d80129550000900d94800a50010208049500603030f41c0302d59603814102d580d001e0400301035440042d1140030908241c2440100c4084402d00d41c0d050725141c01e152003e481c03400360044c1222940e000d0310482e081c0350f5100c41c822610107509100c1141400d101d42841c0c507958104510080c02a0f16014104410130803550aa0745504000d00c0d203500080343c160f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 334992086 1250 334990836 334990847
    0x905010906050a02090414160f11030f04260c060f07020d050d08091c121407080109060504020f0409050c13060305041514190b0a0f05040b0d031b03 65
    0x200d02400d120310301000e0156a00c40c5400409030101d040b81c083c4451100c80c00b60700440300d0305503543e039848503050269840c007030f014a1031600d1440311810820405001991050706680c4400c01100600100003414048100b0030260414441b0003000051000d1030180401030355a00b070b039011540301e12004940a159049408204d41c1e5059000d40840c0c4200c049203051603481050000f10307000304074030000040c0049000507114500d100031070b075034862041c100d4200713565440d500d14504295513100c40e0125000c2c8042d88496014540340c0d40c0e40c290941c0b40c4aa00802c5402c540c002505c1103004000c03900c44020a607090b036040e54421a000900d9440346020b082c444c3c8100c00d0001d04140e604c840c0002d40e541c069220b81e100e64052002c20105481880f80d00c0c1c1103035014408028002613200100d4040948040c50114040092130002490f80500300001c070041c08036440072410b011105014821400c0c48e00500400784001e4030b1880341000380b03540207040f46c02000c480094014001d140340d014140700b030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 334993336 1250 334992086 334992101
    0x21e1c18050708060109390e0d0506041103010905070510170703091518030e030f0a210e09010603090302010207020d06050a0b060307020d030203150a0b0301060906020d0c0204090501 80
    0x88201c07098543d032109829103409091040c071038260b00c1d01040146203522a01d03403140e03880d20901f90050808130070510320721004400580b01c0400c02801061085170301e032485000300083c0184000c025500e46440d110581121a40f07480f8080c0e41800000780c00228006070b0603084d94811504101c609400e410308a44464100e0040040c0d14416800d00c007829415a00005545020380c1520b01c0d0121030700e025800341c030302520412001211050f50100868421721021030615002025120002a440c1181b403401c02102016680441010030340c09074030b5165102c0046802203404c0000142403880001503183c0014481e10040c10349074448601018404c7d41114445a801090000b258990b4180580144030441d4008041468884020070710700c0c0c4182580c0c820b03141d90f8018100d40c20441000c90181d003026000d0340665100c1c80103441b1658910004002a11b00c04590f281c50350300d400002406010258000300c255000b00c6a1030710007940c80391009005503015500440c8100c0c00307241071401095603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 334994586 1250 334993336 334993343
    0xd050d18020315010807050402120105040c0c0c080c0415030b0c0309010905060109020c10050108100b04150602161202010516030e09390d0e0a080c01021e1c18 70
    0x741c103540407580c202420f800e07040c1e9a50b0701c1121207041d100c03c01e1108034410740d0402084040341c00c2c0108550325040d00300c250900510315004004081c1c2c0e41c0c0b00c07006482c45400840d650380100a480c40da42c1841c0c801e04000c00101400749a800e0b1842c3c64040c241440079020303188013035000001802e100301c03d4010703400160b4080100d42c1290394a455800c000d412030400c00782d181c06418000e4190701010f0042c24181d400c0e0201900d070042c80058410010612040d1841d049916103080724420148094000c0042081d50041d14803024010700da09000d50880d0010540c0c10404000e50300544da10030242d40c481c1e4400601500c020302e850400b40c1d410030301b84030100e5000d9003900410500d070350b02d50f4511a01811205904c0c40c031212106000c0420040d020111441c0306060041c2c480c160200d40024041040420940e005c2c000380c2d1311400c1090380841c0e8250141c0c0e4002416485015200103d0701d8950000ca070554284001c20348102a800703030b40030341141c903d62107110004610040100078801e4590 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 334995836 1250 334994586 334994593
    0x20f0601030c03020f0315062b0b0604050c03040c26010c170a020a0c0609030507020d0303230103031d15120414030903070303051608030a050609090d050d180203 71
    0xa491408040c0700ba1030f030100328043e20505003141e00700d080c0056420004124052840135954600c003e01000c001c460004040340081416400c20690425100c40707903c601a81e4180c0312450070303005100c10348001405c0c0c4425503004004110100b12505600c400b500c102c2c020706581100800c01403a92520080b852103540c0d441c1101c0030016075000002d180c04080c0800040c006507840600380e40032401a40c030b194000c98180e4042c903000bc3d07503035401340c07081a20a0a0090400c1c0380c980224112161104044003c00d6441408222418031018800280382c1c0a4882503800c0d030555500500035203811230503540302910303044e1408081e940c50160258807804007050030780720b50601000030b80c542030030f490951f0381c14001c28206900034000302c115044007070003800514880b482d42e64100c40381c0d44403c2040380000701c0c0003004030000b41480025070003035903042c1d001304280c01c1900400542c080e002d4284070f84d560001d0b0720195151b8202d41920000885184005810600d1041042c08030540140081d031600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 334997086 1250 334995836 334995839
    0xf02120d110c030a0e040203091b0a0312020601090e0d090e0a0e1902130509060127020703030c021c120f0b120604170309031207030e12040504140114010c03020f0601 73
    0x120000043d201310a011754520341d020041c8400d03c4100c0c4800c0d200c0c4d01c9580c20801e200744c4080407140355041d00d00f001a140d01d1255641e47c49101a1480b0303040038400581024004001580c19401b03882d042c200400e000d003000c9028808050030b4642c02d486820f480c80380c4040081e5100840f03030312903550801401d0640e84207441500551b06144580e80d0201c2c458100440280e018146500c6124804c040e404001c01fa140d00303141c003d050b842503180089101c0c0e14400c0103440c80c80e030340340080d00440748a620089800b0364206c130b020381440000d0b0300c1c801107115003440c25080350b07501441c41101400346840014088030318464610141c88541121078010105c59410300b500c40002640e984664010680003070f8070240d0b804514144e10050303400c0520f960041c0074111400e91000a0b0701e80014503800c001403d80c4100c4541814000c0c00b803001c055000001c1010444da05007400740d15403c8038a200165041e40c1856030200d0380343c608407091410000e0288134082054020800c000003207091400721351482d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 334998336 1250 334997086 334997107
    0x1b0921010501090c170114090405071e0515090a03060f02040b0318010507020303090d0806011b1b050a050a0306020304030905121c030e1915110c060105010f02120d11 73
    0x20400858a00006420b00345d109540740b440002d418103a0389600e41904088100a04210008070302030002d4405001d00c0300001141d13000e000720114a014000680c0d94511300e4401080b4483c500032001041c0b00004111451069440304240d6056a0748080002204080609404001c0c011a00449280d0740700100b4001407005c1c180403590b150b03644170020721180ea21480d08a80703901058a180000750300510405d484640100300306a400441031400342e01c410740101c00c0d12101116401c060b16580c00d504450091800c644501078003824040d40e508030082d00c0e04001c24082456440003400b10369001c0085802c05108510900040c440140f02c840d0b00f1405070314094480d108050150400b002c054200c3e500c2c00d001c1d0240c558001103078000f400e40d044001c40312020200c070941048420000001d00481005079a12502d42840300c00078282d40c881c1c111b60313100d51600d041a0841070511070001000110680c0c00a402580702c3c81880940d9210f100304034030070002d042580c21206201d800880c220301d50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 334999586 1250 334998336 334998341
    0x11b0219080c0d1215030f0602090301140a05070f020c031207150207083c07060f021606050612030406050f0405040911011803050318031e151b092101050109 69
    0x140181121304104215400114942c2c5c1d481520009005401e804480c2c40400c19030790140502940180000c9948000c0350344110782c207041180d085000b643c0d00c009100d0125404410a40b00d16036038002001c214403a140040e95500900f280f901e010b907400a00780c0e0400c0a18803050749600c0210400b992181d04900d80789440d030300408441520f1804600e01212418003106180041111102910140c0c0c8468210019258000c1c001951183d45078444210041c0247c401040403500d14511094402981e00e862815180040c00c0c2511640c0d0754004103006160100440b001c40d00c2900b8199aa0b0a0301050b00b2400c2c01203900540c1c0c084e150203421418810303120303588031741a00240e0f258841c2c40e01151854a00c182c59003c0604036500038408500c000307c46c500c9102041c01c0040c11076143c1c0b0003001a555042c0e040c8100120a90411711000a28840350150142c00c04036440c00030030030061010a40225025450805109a0706281100110354044c2c224604081340b44000740159130b12890440003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 335000836 1250 334999586 334999607
    0x1e09090b03070305031c0608012a030c2003070507321c05120406030207120513060809100504050a111c02010f0903080706061410080a0203100815060102011b0219080c0d 74
    0x40c5000c2e144c2b807100d10b6102c8d03c81c0044045250f00c4584034048480020660700c0480f4a140350301d8442000103001082c0c003000010010681302c600c85856140a0f000303140b412149015035042c8401c0c80804000e1591120000305101414072900310420070b0fa805d015151540d0202402c0249100140100300b81da4590020401c5901810b8802c50a418980c030407a13091003460901c0c014558008cc017803148500c6800c020b6000f0901100b01d6440d40380054440e0300300d40041c0d03006ca905074880c11800c01003140c0211040400381003200c00c0104030503142c01c030342c0700c007008224000e0400500343c004d2040540a15454005107800020040c0c032540d0030f15041004024502551880e40504901c8608616146080f80c4000d49103948a202e15181c650f2150065000508603004040310074030b021481060400100042d0581420028035504044002900711804924030802010001c002c103a8400e40002c1c007042100c11500d4201c42135071103401c104102c5d014000b8507034040d0041141e1440440e0b809000e105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 335002086 1250 335000836 335000891
    0x60705060708012313110a0c021905010c120201020d09080904060e0603120d110c0607080f040206040e0a09050123010e150603071e09090b03070305031c060801 70
    0x2000b03640c84811120702c1c0803500f5103400300311590b8890355100741401101121400070b0780030045009442e0b440c40c1049908012000340000d0000c40b012405c6d881c0648280d0503d0b03a038184030380c04450410300001c0440786c4c4050007034100c10b4096450601d82e4401d41c11100f10b408442e0003080307018190300d00002141c2c8080c0c4680d00c10343c00e00700c0110350f500c01d00e051507000300002030007042e49602040c0010003680081441b8450140d0b52601c844191899a00400c154101c09000c2d00d540d20700302c0d90240c50f20b04064000700080c51800308210040c0c8903581281d041d244100100d42560340d070f0104900107480019002803055007000648038407800c0041400d110244401000001c0d0ba0303c3c0e10300c0d544a14401c50740c4143c50fa800301540449400c3c10001140c10035160314007406020035440c42d03481c1c00e214002d42c2800060b17070010100320030203847c0300b940c1c00c8400480103850541c0c039646030517a50b4000c3c84440e20b4030808100301d0548012069010318010000d06000b8032840790510101e88018001c410240c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 335003336 1250 335002086 335002097
    0x10080607030e060a0903020708060f010e010905191109040e16080c030c0907050d0c020c04270204020901120e07060e01020a120f1709010902010f030b09150a03020607050607 76
    0x690300034001d0182050800d440380003402e840c0d4404841d14041d00e000e1205400b903025108011450f0034083c40203501c142d01e00d51440c4070552400b01200c07071041059000c04240c0d440c210a04c4040c9442920018450440d42e4001c2100e0458403c12039040c4500e004032680070346001030050b950440403031821a0303125a01e040c6888956074a1045845416240031294950400383d52132401340b07491100035810034020324015080a146034030240480d1078008201001d6401884040303c42c1c03425018190340c6d44400400803c80d2039115414030b62548079400021711454010541d14001c0c4d01c60915114050300c1749406011100365000d034903464940030f004207030014400710a030402c0d1f1750000030220030079940041088400686510300725605c03d06141c2d54800c210481d41c03c4140050707082d00ba41c0c090804c4600003c3d070400306100142c0302f80207018100d0300707050806d0b0640d1820790b1840f2802e903101d80000104800c200081002603090030003074000a5000340c0226011060150025400317200e41c502da04d85 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 335004586 1250 335003336 335003341
    0x519090507090b0103140a050c04320105040602030304150f02040b0414010509090114150a110c04050108030a080c0403050a0b070e0406050d0f0203010924110406080705130e100806 79
    0x440030f9a186c00700f440c0c44200741a01090b0320403070640c00b15038000421040d2a05007a01c450900e220150a101c40d8000c0510a112000daa60a00300040003161401d0900c0d600c1e00e4503069007e500d13800b006002500000040d1a00c00055149400400401010000c115941c1c0d844c2d00542089030018000c842000e10041c1d05c05400e940210103d80901100500c20301c56030307290046c92504140040403040c0c00c00341840002801085100180500c00300680740c0400700407050401900d040d1000c0e0406100b01e0400c00104103182011046800701d429910304040c20347c1d40d00851030703020710555000410a10503020400b0070b20a000382620b0090042e607480460352910801000207440183c00f0712a07000410350510000a1515410300200610180010070140c0300758540301c034101e4589280482c26280540f61079519207041c0314140c490f0350512400740c28117040c20001008200000c01003414040c000480c0c001c1c0a01c1446079000405101c0415900d13403900c0e901c07034001c040944c49602803d1280e18007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 335005836 1250 335004586 335004589
    0x60806030f070e0405010f1812030b0105040519170601050102060108070308040506090f09090708151324110a1704030c0816020307140325090519090507090b 69
    0x18403800101e04800180941030502c4800c00e007204010b4401c4441c2d40d81c40c44075840f9000b0341c0c040c00300200c0c05035859000056141c00c06074000451500743d141010700d40410103510b40c0e089800d8401750344050783d01040741e0443e8824500100f08940085400d407a09025541c1c070f1280000e4014141d1303500782d081e42c5c0c159a803200c0e143e03650f40c081d00001b44010824841440345007450380242010b07031401411140ea6600d64004140d5600e01030305d11421642004405008450703041200140d054000090501c80e894601c0181d10010055100100300d0b03403403001005208480c0d00364010303003c000600200240703119440325210035405415140302040b05044480144c0210001c03e621868050711600044101665185504c0c1d010903d442c580c0314910744a040561030030007000020b8444640c4011818850038101854012010100c4c802020912181c06400d4005880001158545800403846466040080305555041c008040f0741a161800b10070078401c0000b2008111740017036400b0001420400d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 335007086 1250 335005836 335005843
    0x914090a08090a121a0105060f0405150c06010609030c09050717041502040b040906050d031b0f020904050303040204060b1305010e0609030a030917030a1b0c0e0a0606080603 76
    0x5462a0580d044004a103001c1203800d03008003000c03040200341c10030040e111060002c40c078001c10020745039070518032000a00030701521503041c00360100300c2d45503041000c0048010aa4802c134006d190080310340c003400b20144088402903400071100c0d00b068609a43c0c503100010071865040c0320696010902c580300180414551207000d004030940d5407001480010313175100c4c0e605241c014008844c1c03001e40ca02c08010000c02480030b44098101501a255540d20f82424281510030070b0301300318802d1000d40c6400c00041e4110b440640300100d400068501e608003801c140341300d01545000079411800d44410070040043c0440110300c1035108880800800d622403455908602807a122161412031400c0c0500281d030058400c0703000058024041480c000310480424200200c0071000c6010950510b0180301a0303009107100742c0c1c600b5080004500b04030744807400501e040d4103452174010b5002c80030110401e110303481180340098150741d000460a4101180401d00921070bc0c86164001075121010503903a10b00403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 335008336 1250 335007086 335007091
    0x5010501061706090714030a1a0f030706080a0906110301030b130b061201022104021008040f080c0f2a040911090c0c0d0e01030e01290121060914 64
    0x9a5010050f07500c58040c0b2042c840e0150480d024003546101d00410015184002c5200d10043c0b071380414101ca40406280e008a6001c0542c0d01c140c1002a143d1070355140010711104560030303444c040b201502c54200d00300c001c002e009400743ca060300b4032031840760f07691003c80214101c1e4420360500c4400c0c0c0d901d5030b0401509210303000040455100101054861034019083d901148a1000052400f03410642102081c03442841d01d030742d5200104100406c0d0b141c0444034100030703405820030100303038501640c820456121100e8000d101900104400011840410425100382200c0c000c031043c00541c80d10364604140e034250b408058003040c6400045a0402e0301a00b00c03403550016030041010707000d04c1000340a5000400803103260b0b80c1803015242c0200f0800048000318000d44030500c41500704400101074510340d0300220101e84c1860758020403001032400d00100d150640d80305000c140e00c95401242c282400311903e855242c8104910011207095901080803100034103800c000c8110303518148007107282e04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 335009586 1250 335008336 335008367
    0x50703060510210314130906080d0c05101503060c02100e0d0c020f0301090b071115070f0c03050d0204180f05070507080a090302090a14070203040807140a030c120501050106 76
    0x1100c10070000780640543d4034000140c5800034181001c00742e10300146c419076804188040e440301030400142c00c0500c03110340c00d0f843c0362074550100d4420340c541542e10450400180c0501d5501c01e180074071110038140b501d002d107034401002c0c080c3c41d51860000755602c1d030184203000024981041549141d500259062064190f519a400b2005642d0200200705000040e116015501d6405070800242c01080e40c5100d94a82e44617a061a443c2c08501ca1a05141210103548000d160060180f101d4015021040c0c520003031400391140100e030b18080300d01d400741c0080420b0380741c0003040205060140071007000d00005812410001e029400c80c030309045d95019500798010410030020440800d1849004100e4207040d420f020780c90300e5907540840e00c184011926210803c2e540d44d404610b0f10410003106810ad500b0b8801541440c0c1803810050312501d661003080c83c202994001e02d4243d4450704c08441c000c640003030204144640e118160b0410742c0740c174a0100c81e0742d41392400203e941801081564110100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 335010836 1250 335009586 335009639
    0x4060b010e1c020918030c100f020901090e10080714040f02070c050904240209090f07050406260406060501180f03060518060c0a020f0601030f0605070c050703060510 73
    0x4603024003203124809401d0312440d425041405c201000d0400c02800388482000c010500d80203802041c85c101d6000340218541c4900420404004d80c2c0d10040307036416601c00403240784070b42c3c840c45103090090f0440d40c46035149000702180051501007641c3c00c3c40c0740c000280d405011345864002c203a8101c0c4030fa01c40c02840b55101642c144040c0c10542c1015500501c07558526194001c03540440102c02c03004031000510b1600090b00c038400f810b00c61080c640041d0f041075040c506050001c0080c100d0302542c001c006c00c00160302c50390501c0c10302031400c840304e454029401c0082c60810f810720b04041c00712401041c2c0807511072507101d41c0c280b90456004084881c14900401034034115581c180c007801c4c1c080c25010f005552080c40e18000d0500f88821030040b040c0d00c404540c1e1312034008010341440d00c1101e02054a0b00076100400205418241c401c26541e07114900240a5640400560b800710901c000901240314164000c0108050b940c0b10f9030090030303510498990113548030040468240201c19400c00d102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 335012086 1250 335010836 335010889
    0xa05010c09090203160516081801300c091e0504060f0b03060d06020c03121012030e060c01111201031104020c2e0213030b090604031e021504060b010e 66
    0x40c804c40c0505000d40d03a07680d40c80f007001003d40320001190400c018007100e6582c1c49270381c505c00b980c00144264414510380c601588400240b04803220941d525100c0050440e01d901014441c1817045c81404007130308460f907105813550361010342011810340074002d0a000754035082c2c0105141d80b48102201c101d86a00e01c80615543c0c81e1000d108441c82101070031035803240c080c482501c6400052000e0000302c0304021000d8000e142440c03a980341e5440c40c2d80090942c0c200920060082588072030018418030042d40d2466540f24844005030040c0804414811544c2d00410800000e540003801d03e030403a401011709404022a50b01000f04a100b410009840b0f68041d40c0c0d0400c55800c070810008144540c1d805440d00c107c4220500d400780c0c2e0010440701003159056a05008000d407543e44241c00c61180002813185103040e035405040c81c50900120720402482c030551140e00c0d8800c00441108410041c0c0c801020308281c6041409840d80100003404610200a284481d061000485111880f004405174a0b403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 335013336 1250 335012086 335012131
    0x6040207020a14010915020105040203011d030702010c0203282d0f0c0b0d0b04050a23181608060f19020a0306030f08030f010b07020607030f0c02030a05010c09090203 73
    0x281c03850068138140081000d001666545c0c1080c039a030702070000c2c0c001090078035061040608450070303c2071055800b007005804041d208800000d881c0010f90a0030585040c0c01d860000900e080c030401c41c0c420052201002e1100c01c43e00007060f00401e503210326500295000003800e140c4071000394146108000780a40000c1d400316481c0c3c203550076028050030a52020644407074140c46c05900c5040c140c034200d9180c004d05403d9003058410503900c50150401004070a0214011480946030b20242001c1276007298080f0310501e440c014242c803800c8001d4100c2c0e02c0315501c03140600c51100584543e803864001e072400500394088241001e441441481c1c4001c100044440b0b80400031341110200744209541da100c0880011541d00c0350300b0034240600c0c0e51f00e8480c07518201442c04180c05070055070100b50f0620041e00140c03540820f503040558581419100a44007070001c4400003100c0c04041e51521501000009009044d03111685100440d42c0d001403144d22546408141e1000342c0d100300d14044a000541c0d0345 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 335014586 1250 335013336 335013359
    0x7032009030303191409071701060e060d02010203040f12021503070804140f07031a060303160b04020f062109010c02030409050405250f060f17071107080102030a0506040207020a 78
    0xd130401c15400040d000d400c1480b446a140040707810b404203900902061003079420680c10001038012280c020300c000f0b805e0000040e2070780c07401303001640030350440180d4204580c002e2040c1e0340940701040100800c3d582d1560151042c50040a041e03006140c07010516002c0e4440f034040320b11612687e00c5400840c2c40e0742c0d03209088224155105440c501030080004403204003402004000e5005e5441e4031450343d10800781054540e00900204d110b45c2c81000002d0b030f000c48810f8100c0070690040406001940d40c0e002090580c010000a264000000103c0e090244400d41903001c441c42113038448000d0381d1740c9415150803203501070300b00c001591050004104e201d0054110386d50041c40340341543c860880b580180725042c50421510440c50150070300038000e0b440c0301241d0400400e454905403620300030900c005050401400031003c0c0300840c1d64001564680104e205011140b071a804580500383d903422940d00079081030720b80e802594280300205603145841d00a0343c1500b5001042050464a0700319120007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 335015836 1250 335014586 335014621
    0xb090c0a0e0406080703030509041a18190207030201020d0501050303041820030f04030e01050702060406030e21070506010e092d2e0e0c130209040507032009030303 72
    0x511940b600300101d03095009014170b4000314881e856031511141e04404010541d03403035040328000505003042852040d550b06d81010210b054480401d000d907124440c0c20014010b02590410341c2030300003d411010954158014840c3d0040c903e000c11207139032584101a220320883c40361444081b040300343c9081d030000d04c2c4c0c000c08008001003002c800500d00c141078200550000c50b511900b02030802c3c104018950040f45903940107800b442d010f460701200342c4c00200c8500440c0504010103641d4030891030390042c02c0cc264406051400c0c80c2c4961030f001c041480c80030b91700c481421582800340500001d90444031081c000d000d1040341002d81580054a403a0020740081e03c0d0501f0244012800c007001140c1d001d025407103140501500009080124691511018030b0060003101d16507d01b04a8101341c80340030035035084405040b22106015003c4080e814081e01031f44203c664030914103018000c03080e40540c0920349020956070120360341080e50a0f144801d01640c11010b800d90070400010300c2c018882c652035403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 335017086 1250 335015836 335015839
    0x31b0509150f04091103060901140f0702010b030f0f010605041802010f02160e010302010305070c03080105150403060501150207080f071a120702010603150e070302060d060e13060b090c0a0e 83
    0x804612034800180130f8416a8100740c42102c51405102c2550900344200b550000300e1070300034400e04501c0c0d26180b44c040d0f0f0051074481403504140100e12014401c0d000716250b40c50090407107400640b8040095161109a42518403641c6800700009850405000d030300c19104400304000d104200310780054039125108805001140191801807609031014084040900f141d44100e2000c0e60541c030003d0122000a0040d40502503000800b13000242d00c0544d4038151041696880e800b200700d80f90500c40740c05160001000036051400100b140303c1c5282007500c0c10b00d100c0d400c840d203c0380d9580e0301d261a8041c44042800680102e00e01780050040001c020842e0000305194510340040c0229540d01014141c1d6003c006035100c5a0810038008a000d103600c40340304e003100812042502000c143d5079000d603403100900542000c40e61a42528141d4440d40040980c0d00032034526142c1410701d00a4401141e4007258a03078a025003083e45c0d8149052618402c518000c10303946082c05028054807150304088440703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 335018336 1250 335017086 335017099
    0x1b0e010e1c11030d05070314070f1709100503090607171f090207050a0203010606090b04030303091a090d110d0503010506070609080d06170309061c02130f031b050915 73
    0x40b040c0703890400c141e51a6034070995507940c45240c2c1d07243c000d101c1c030300c102010008080107103c0d100108488410545010754005103a0081600d41c0d04560600d004000341c880d44180c1c441198602d40340c2040085208044170320907222640d841900982e20b00f131201d4004103220300c00710000b8280b101e88106e184000342c109081c8031001c0c1d82d1000c1d000166400b1400c00c4070550420901c4c0d2045060900481c0050303c16410440501402c01d05271100303502a5200260825417103610400501c50b00780d40c04452080c00c0c8030148551705d40854907955a198076021440095200707080c0e222641c0780400e8022115007a9545c19140d80d107424100881600245819610070355154014000101040000d15944030100340105005140a40c81c90311401d090b00040070b41c0d0003c20050409989a0b0201c6240404da200c0b04580c1d00390411000009005804040f8a04180258046880c00c07060094400f16442010500990003030003450700700c0662544241d540000361308002c604101c84441c0f56844100029121 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 335019586 1250 335018336 335018363
    0x621140402331804050105010f050d09020405040614010e130b04141e070b0f0403060915020301060206190911222408070b0d02090409061b0e010e1c 65
    0x3081d40300c00c80000030361200c0d500096040103414408480516441c3e040390200842e40c58600080c100c0c3c2c40c16071b03591b07040020000386c10002401c3c45e405180b0141c0c003d0000c22040c50f05161840041a403010703001582114400006170403070780401d5141c80744454150000d001c6e400c580d01c00100d00343c040c4c001c036500a600c500301d10340d030401001044660a01d2200380600390314880f9100341480d0311908900950350003007203084a403001200c201d804503580520001800900e83c1003041d190185a848154090700000001943c2680002d216015100140d01c90030050f041c1040d02080718844103005102c4401960008858688010b03060020700e508003249400103480001c4004440d1951034900e0100321a1088400703c6028002000140040074000d0241600b03240700e2206900802c511211150340000b0001456211900442c0c01182d003c0014088202e0b030700281c4407114403007080388000600600c0b030409c181d031244c0780c0f0124014020740344620300182884000c981d90080c6800383c9503961450320 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 335020836 1250 335019586 335019649
    0x60708040e04110d0b18070302011d010309050a05150a090b240303040e15010c0b0115020a0c060522301707030f05120606090109090203010621140402 66
    0x40711303a91305208001e03200781480c0207202e0100c102c0005002d003440b0750102d282440140d0b00300b800210041c40b02d030041190302c0b12440040300648a0480c004069000d02010041004400140444000060b40c4880c2d050342c0d40c0d80280c0c1c1181d95501018205442ca1004941c2140500c141056401565001c40d20040408000700c3d01e540e0180d8010000c4000d070004108520310050b46180c4150300903c1c1510518840f03845d1550080e8044c02800043c401c0010f842c881e05008100310329055900c0b401d206560780d941e0318084c0594120048015251503001c803401803014400c0d071034900340c90012129103c551042000300078030392070990456140d041007441000105a0302d954500d900c00b1100b80c055500c000c1490000c000b0a103401e048810720038280201c4408819083c0410b601c18001c6e40e85a884400c1180125011a02c991000340028400000840e1403540301003082c1c80101000f20840004c0f591701201001c032151424500c9100b45020701080040c0f41900300100c07800342404145985402456 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 335022086 1250 335020836 335020849
    0xe0102101109010e0d050c122b11280f08030406091704031a0a09120201020406141e070c15031406040e060c030901060f18050105060708040e0411 64
    0xd1060107050046590101c0307690250511519010503212550000b0260f81c54a40d074011a804144c490318140c1554a0810000c000c1000340380b959820800511060100b02640640e802c03e80b5000180c3c40210244482170004403868002e607007503c4003810429030440700c8520000d400c011a091800c034130501c004140984044c5008902512000540c9102803038503015040c1e4a00c000703146507100340810000320304158400031081107240320007662903440d150b54034000c055031000201480c03011039002d03501641c1503000c0e0094504507100d13042c0038221103015007447d004128040c8256200b504161162480c41d00180a400e07201e41d8010180b59250303c91800c10607018074082000994078041c040050540c400b42907040030098508015207101044480d8030769400903c84c01c520100040494038913142544074400411081c1d6070380c140e803600c402e6030420f01244040b44410150810300040340a1414504032000f599000320726a1a00c3e00e888124801001c0040c001c0c1e41d0300d88507244c00c0940e0b80b54103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 335023336 1250 335022086 335022101
    0x6060308030702210d0c1101023408030604020c0129040513020f21071d10060504120602120a0506040c05180108091603050d02100209010f0e010210 65
    0x403803055850385003214000380342480c54107442ca2612002c0350ba4120000e6403404a0700141a40c00001c00d501c8010f4600750b5400c445081c6642d0658400518a10300c0c60304410320105020303084a13600c0050f040d1b1420b9403d006840040070300b0314803080002c20b80c00d00e0a54010405070b2021400450042440004000055a0440c50451400100340c0d07100c401c0c0740c14868160f011000001104000100d5008034040e8000b48074080d0003004154050100c00003009200200e8001074022602d016846e040d2460740313108440c02030055945c0c4a00401c020580c620710342c0c7d00361107590ba11241468070b4001c14180c5010041e030b054401c0d907030800c09114040c0356002c0309403050046d12404912414030301e0620080321030360007506007089818030110240e14588800b01c16401001d113080c41c03190711014805810080c200009928004042000204009000c11800341609072a029a069000ea0500d030034103070b2280c2940746002940719000851414050141d0340082203040c8112103c2a01117106c4070f01701c8014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 335024586 1250 335023336 335023343
    0x2001060e0a05060406030f0803040201031407090911120c0a030e0106060e0f09060f0f0a08010207061b080417030405030d1a0f01020102250f062a020a020a090507020307060603 77
    0x2030070800c0111950166640000301500e08003c0c070703031650300e80e507140d40c403a200d000b070014030000041005d580c426000385503214180b20000306241010031000d45140050f00c9819001070070401307060081140c04058440606120000280ea50748001e4134440c1d650004020006046c2d40d541118425a4240b00b5480501900c4d1180e00001410000b00008001c08840091040c42c0d00020010281c46040100c0c1e4180f00a85004160300c1c102d500203807180002da009151550b1000c40c5441c10320409070000c044480c030b12000d8144141501008036600f600c101d43c00b0384410611001d584192080c80c00459001d070140056900b403091f8000c0c001d0a0f1403001030301420f900c40340f20031149c60b4944058180d90b504401d00003103190241d60080062442c58810303040c101469915180310a00c60b41d01c224201084d8840300030040700c0c06850314039100c6c402d03819212900c4050820714011003400084c51125480d0024004070440d481e0030360400c0a4034005164a003180001d000410000703d450083c100510711 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 335025836 1250 335024586 335024609
    0xf011119110a090e0c01080601050c010905150c070c3b040311031204061805030d0204030501060f0b180f12030c0d02032503020c060c01090b0a0203070906200106 71
    0x80141003105900012400e91030b00340e01104c3c070880002c0c1111808020b0a144040e9503550005031102d00440100082a5090503051804c004011a14022494980d008fc25203600c0d080b2200ca114051004002d103448007000e030922501c4d460700c00ea00072440102200c0504072140c4003a1101c0105403e010500c00301c080e10030700c000c140d042007039460b07494401d0000754201503080390541c0c941e500240010780069a07a49500b003004d410480c8004072190000122070740d52010080da03800030742c09072009441d0341d440d009021034003007903000038402110745401d41141080700c000080401031a00c000e03030380e80c0402c81e03c2c1481d42d59100e40c8a120601c156203000f0b55145d809076041d40e410a900030f0510011900200154420030400700c100800045070400c4c11105c490031071506900c0c0001040210390300c41d401003051900d0b49415040040124414010000f058a801501105074001a00c08401042103141c0c02c2c07100c14840c25041c014403a0718410b104100460b207a0b81402c41d2030a4000c42d00041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 335027086 1250 335025836 335025863
    0x3080603010b040b0a06050918070206070f0f090302131b0309061a010c0b04030e0603010b041502010b211906090c060f0909020d021c15060c020f011119 67
    0x40e080c85a0180c00005603030901002203060009410145a4040d82c018824080b40800309500c078030000f48042c0404caa0140100c1c11710a0019540c0c400c100d401d0382c0040e440e1142c0350307030380c0344640003a5150703001c2c9456210100d130440d8204400754124160310f40e0103a66600380100c10300500382407228214406d440c0024012400d0502c40c007541d1010200e210743c4015910300101c40e9038403d81b0f5500c031030b030806074081c1e250712240741c00c9440050b40340038154043c40c084004101ca501034001001101e560707038a049001c2c803506405070700b83c8a070b02203070940c84881e411000c5080210038481404100710780007030b02c0303c846280708111034440220304166031442d41c400700c0b4004c02070b0845054001e81004c0c20710101d01c1d080141d00402c8400f403800303451a40c58003c10b45414190040e019901e1400040c0e410785440000e0b6044a0300820407114000e0f05002002030009003030b40a51302c43c0e5a481e401400c0090030a5811005403544102680b149407a40b040015440540d02c180c28040c940782d1090344e440480342c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 335028336 1250 335027086 335027089
    0xf0604060c1704020604031407080619061e0b1809040b060901060c0510091e050604051b010912030c1b08010b010305090c040902030f07090204080105100303090b03040f0609030806 79
    0x5140412030880b440281414030001d40d85110030741d412240e00c1030484038043c581c02041420b05400b80d200c040c003072140754240700e0300004070000304c110300060700c01c02c0007020790b00c0c8100e56030190018000042800e41050a0100205110041070304c103400008064890640300040b07040b0540480d8260385140081e42030100a1030842c4100d401030000d89040e00318066551030f441c0d201c0b03584480b5501c449544980361002c000320a41c1c480c000140200a540155210b42809521030000f200e0883d401d010755400c41c0c0800c0919080d00101c1081a9141d40100e81000d8a07528100c1c04410158240202029000d001a03c28440d0500120341c4040342600a45040c0380b0310700350b800c4100c42d17906050414041040d880d10000320301c1402e050464010a2a5103940017090802140011244440c0100b1402140f4160306030018412540828020003c40c0d440018486500d4220700000b4000b03070001d50200404c03060080a5a0464001c4842024625280e542e46044800d2880d00701c021400507000c00455 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 335029586 1250 335028336 335028347
    0x1306090302040b0109270b06070b04030206010e01120b090708010501080d080603010606300e010c0809030301031a1005100c0203010f0501050a0522020c0705130606090b07050f0604060c 81
    0x2264001c0c01d0054982d81054556032000762600c42c4202c0c40d1894600c03810409001fa0400104004007403c200e6440c07665091844a05c081110f05802510905000140550b00c400700381c0c0c125010502000c0114a0b29550260b00310406881d5010034440c41001240c100300a1107401d00070281072008004c50302a55002402c000402058584240d25240c0b04102c040d4000c02d114010040140a03000044c01204480820703480c200d04036104940307000400c04021360705601c41000c1c585a610740e150241c0c0d034110784641c1ea1100740001041101500904e02c02e45008071080d580042c484202c01c2100f6444202003807004200102840000340300e080024158142071080c4c2d040344000c400c091000390b05100c003051105003103118007400b07440d0519000c55151680203060907050603501c001c0d176650101a0305280c0d150000d0185501c103440940043c05038900350b01c038046c2114041d840d5084140e182000341025508066802d45440c011004a5108a1018001a8455442400d00281d80080004020030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 335030836 1250 335029586 335029601
    0x150d150317090d030302090402120a0227030a020405060a030b090604030e10090e0a090605010b1201050121050408040302061306020d030603020108040f0f08030106120c0309110f06130609030204 85
    0x21040802c20100055449400341460300755018100542e44009071400300f0000c1c81000c040c031403050340d940148459102250010303c3c444602100c034081101c1100c01d020150032802d10b1065056001401c804014180342e04441c1d40310900501c440d00150340c0e03403100c0e10a80c80407a01e181d450380082080104050f0801c0d54900744550607a0001080301840708041c1140e10103001e210048850500012107100b1140c04c15901a603218405010b5569290414102c0742c11408a080d01004400004a22544605030b89141d0102d1400c4071080420521045c0c0c0043c0ba010f041510052810007003c40076855001c020b000b40d000944180b842c0902c0e0400083c100140d440208003010304100381003000d82c4c0c0c0b00c455140c029820400203006507c41d4940240c0d018104034004141c02004000010f0061b040200810f441240134820701130b81083d03407402c80071a480400000d101d40d031402c6507080507050104c4041100107028204605d002d0b41140c1140003c2c0090b80018002840e940080c011400c09004009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 335032086 1250 335030836 335030873
    0x5030309030c100606020a15180f0b0121080913090b0411030c030337050d0b01050306090103200a0f140301020403030f0c080405101710030809150d1503 67
    0x1c6240e042c00c9009445142c00b14016054852503111242303c0082070384002110032008000384800b0081d460440d203401146041910400c40d90000062500d400e440d021b2860a405014a9030741e801c00e5440c11143c6c1c210042c92504200011a404030b0140180700d07061415001d209100d05519003850072144115a00c0700300c074040e802401c0c251040b920004103a4004841000401e510540640401001c68900911814410705145805107003160404010001802294002c0c0016107201c0015155407000355501c5030003042c2c400040005c54802ca00e0000d500c0c8500342c41c28100744094000686110346a00034011a420310241041906031244a00440c2c0c1c205500075403c00e495078401801c0d040078509003405100711261403a0400005508540180800402e02d1140000f200802015000c82940c40e4001100d818041074050188603501022603501c00c00d4207141c9060127050040c030140c42c442200e1158400c0c000c01c40c211441d4051880c4441da11801040307824607500700b400a02c0c4052609c3c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 335033336 1250 335032086 335032091
    0x160c0512090337020d2102100c05122214010b030615150c010609021b011e0b01050708161e1e02010909020c0708240402040e03040305030309030c10 65
    0xc15044044460000c0301120101d070302e02c010b0807a800440d102d102404170080070080c040640c1c5030000c000c01940c8200d00000d0742111504070748146c2c1041114503c03204031000c600140022004200c0b400d5803203500c90000c0d40c0d4000c0d0000d0005846041c2e8445210440e43c0610380c0c1401e08a55030b003440389c041c008000324002d004906210584045480158a04074081d044507034040500c420300c64100e40c240300908000700310031682c0e92071080c02908908545900d04c1180040c2d46c0d0400700500030b441901c10307a099003a42074000501e07245d00820407a46a141480428000c901c0422000e0004d09104003a60314003201c0585545408803c098002c6c07049034258503440e024002044140b50040b0107403030320121280030000f6600050710156010750211030300500001c0e45181000d404070340201201c5034441101c03200c0c002905200a811100a900c4a51015007800100985000d0300103136400d662075000d40e0b26280e121b88403541960320803503102607643d100003140015134104211080d4000c0011008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 335034586 1250 335033336 335033383
    0x11103040f0e04020303070b09011a010e0303120907050a120c0609030b0a0f1d0d090503120d090602040302040908120c04030803131103160509011409160c05120903 72
    0x21020701c01414010302e0000c04070b07800050b0441d1020011a00080d40040e4010802d2900c1e1a43d90701804149031110040c400500844159500641c8102e20000005001d075060110300d503005903000800502c511349500c54440c002035107840700b0750090b01a280c0340580d0b216910403400e20002d00d4029134000d404214200001700041640301680c0c94000011035400b054400584c1c9502d005001800c01f207803034080303260598504060b400600060520580e03202e10303001944d40c0c005c00d5103e22500c403145080d11402c00601410b0b101c0c941c0900c69283c440c00c001800c140e240d4001c6001c80f100050101c0b0925000507441610124985546a0162180380700c41e00e401e045a460300094000503000d400461003d20480c02003110105540b070f1418806800c03103081b420344031296124030b501e034403c040c0240310010000c603800700d1100d1441d00c10030014180f210580c41d0100c100e8102c60303e240c650001c2100d95030350440090018407040b40c245140d0a42d1030b07210320311501050300f8609540760040301101400003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 335035836 1250 335034586 335034599
    0x2404020609220510050906010806130e0f030a09061413060302070303020712030b10020316080901090b0a031a06030f1b0c100c020106080d0509090a270201110304 71
    0x807141c0101003503074200010b0141142e0a0090600c0c0610020a0340c107100401c000e40201000d01401c641c001c58000082e6183c0307000640d50b82030141c1e411600072000a01d070891010164204a54800c4d141045030603881441da003443c115040794411400003680c82104110340c961006000d5051220340031942c0c03404000544001c8d40b40514441d042c281a000b14070b030010300d8060303230503a9401508600d0b450206810700b00300a0007004d0049140d4480c101e25412080c16a10000907101048110a0726074070180d02a142c06480b1f03004100d1040c1040050400031445010f500c02078008003c080d10b02069203000c01c01690100341289050b01d004010500400c04c0900703040d00c61076040001604040c0015011900c051140c0c4242480c1c0c074a80d20900b40007202d090030b00c0e4803004001d02654020820182c40310b10154541161210a40004009101200c040e151844405401c42081c01b80001c00010700a10806101c1d0040e025070440c2d2803121854040d0750b003000704d00b40700341110009180350508111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 335037086 1250 335035836 335035849
    0x60702060f0901110d0519030b27010603140c092818050702031e0c0703030918020307120b030106170d030501082d0c19030c060311030f09150702240402 67
    0x101007c0c50078211000000c580d402940000001d0b840907224040381d91001c20702c0d5855041c9000741c0e0301c000f0000000001c0031840380c864400f40c207111140c0134442d030700d0750356070031501e50042158030764807048601c40004529640b100701100e070020301c101424900d10300556414003125009c20b08c510f1a003007004105221382d010080710740340b0404200f20199144046400c103c10f004011540406100e42e94000c024160040d8280c1c1c00c8542582c01c107107005c08000b10301c03020b0340000c1c0d0342039005c2841d5030b88003c4204442d400c040740d0b440e00030380000303980f503034502c5100c1041510040381034450704661507100b56075915000e12809080030800510030510f21112451940510307450311401d0207050006566a039a060018003040500184007103000b4080c00e1016200040600c4125a21401c0c0e50700003c8050103400f618940e146044845821681c0e40000c200f50010001d02c82c40c014041d042e446200594501c0425000d020140e0003020b015404140103108103200b0030030340c3d1060b00100e0404c4016903844 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 335038336 1250 335037086 335037097
    0x9120301050904050a0c1e0b0f03010605071a07030207030f0f09060c02130f06060906090f2601050103050102032703300408090405130c0b0306060702060f0901110d05 73
    0x195080c0c2c41d50b0b81c55040c10ba042c480900740c020041045940e0003d4512600c5440401d41c204480c104466075070742e82c0800804c2e01c5000810003104c81d00380010010180908054550a0302071b0304242404006904011440e4100304c5540000c03030b034007050b2103042c5907000040007003880c4207040400e000e0240c00e401a26560305071049408020202e12550210744542c0001410103030581010320040221060384000b40403036008260005040d49000904144261010b50403100f0322100200241d00b0458000c0d01c860509089040000309040d01305000071003482a1030081d0301400005890b4101842c005002200321603201e00d5020170203200c01d142c86c50110803201c400012009802850801064881c00380c000c80011261a6900b00300300401c0c419401e0080042130001c07942002241d50b1410b43d10a10304082401408060816600b80440c40200c1e0003580c1103040204464104400741c3c1c0000c1441d405420f80c2010302d031011031004040d580105144601285e910040c1282e007010510080c02400354 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 335039586 1250 335038336 335038339
    0x80a05071713290d0b03060609010e0708070c0503032e050102060f072007031712040201030b03010b030d030f0c0203031b0304030e090f0711030306010e0d1506120b0912030105 77
    0xc3c112071400c510b03011002102440c8019503032a2103c60460b0381c0b100501000f0700c298028040e0400140c940e00e4030702c400c1d0b41a194444c82907442c64a9102003213804600040c00d00b411721103134a4480010500410186110704820041a12035000200f000c0c1448480300444514a000300790052000760380210b02c440c0e00101d24418281a079589400448245d1164504401c0c131402a030740500048001182041c1a07074064030341d0b14400c80308205150014414000f100340e05016a0b0f0110300158401e800c2604002c80040c004214140c00307200281c140042c518903600480c1d43e86440c0b55404c000c074010200800c4c424006107055140028540440d407003c030a902c80750100010004081500401c5d605112103030103001d81c00035161528601701c1340c0e40141e8100010030030503440d64031020400011244070761010703543c0e8560442001c0903c2140161050203c8403103040004150402c0618403c0e80000c00808a841141e01c0143c00c2c0368403d0100540045400d80000403500300c141001e0381101c0c1103820 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 335040836 1250 335039586 335039609
    0x6060f170613060314060f01050117180607020f0c03060907030f0c090906020703020f0601060909090501021e04050109080c0904080315090c09010f0e0915010507080a05071713 77
    0x407541c0c0007480c01c507010300d03020a00528201011040c0031400d0381e0907294201410407a00640c40d0f0603800403204100340302c1c4500081030001407010a00741c68409541094079800c200f40041c0c000d48070142821001c440c03000040c1e0212142000085040100040741c61080d0090b0041d420805040360302c0d81f0716400040e0035140084440020000c01681070001030000703100c01c000d19840361400c84080c0d48008020b030014441c070b41c4c511400300d0000c160141201c1c559120b06080702d240c80801c9001c0c0103061003e580c9035500340b1200b481c59011008180590600d40007555039030341010009040e045030b98010700282d07801008402150b4448510290700a40c00c00394141c0c49548039095035070540001d009203034000b81290144055600058080d1803450401d88925181100c064001c0724540f000a020652020008001c184a40000461500e200c0c0062510508d404c095441e140c0860b0300403440f540000d40006540c10070321600e50540224100014481440d01c045006000301c10307645809004d02644 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 335042086 1250 335040836 335040841
    0x503011d0403020f010606080609060301020a0e090a06170a0212150402360a0c140304060f0b0901080a0c0f1202100201061703030f06010c050d0309080d14060406060f17 74
    0x6008000d40d404d40d80d0518005e024550b01e44d40c000b0328040741600c48500072205400816032900d410f0003900c10498165880410a04040d010056102d00190030600310300e40d5040080303004d403050500d4201c46090720004000200541c8103202ea40d45040031b20b5451030f08041c040411482c4880045d9030040d0b011a0b400881c004520700403494802140000b101585481c0450044807564a0314030b4456020b18804100c4524040004e580d10034a07100c801e00bc182040002500040075580030740110031081c07800154005140340801d0301c2003000c1e0810f403096407044201c17408008440c403584002d0001c0b40c05030b00d81649020884107d00c1852207000f0311031100d15410b016028401d61000e8010440010340d00c10764240301350035039141d610548888031281503580011b0595401019482c2c006c940c40740003000102e6418104074000c4c4407400044460b244c00b00103a005508a034040c01c59078810046800510342801c000704801c440183d48404240181d8511034056560030041c51210104101d03188141075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 335043336 1250 335042086 335042093
    0x903030f02010615030e070b0307020a06180b1e060307030c091a03100e010501080303100e1b0307120e0d05040b0a140d0e0d03021305040b040b0306070305060a060503011d04 76
    0x180380b02d40002c203246808240203010301da17140d0010101c004a9034150790300070361104000b0f4110300c022610000580e000c409000009103d03a804115030460503040c900102001c0d5850141c000380a6410980c000c1c0c80c0c0c5000f0700c07c42031003c1000c2c0c020108500400016156560304d402c160a1845000881a520b5080c14400300d80b1415129a00ca001020740344050850800c3e6130041081010b01c0c40150b00e44030001c10082000000c03a801000101402d0b60300e103180230301042c1c5655006040308802002c0068070303008d01c010400518000d4106480e101890720f00c0c8600e200450711440d4841d03406034440f4036828065074001080b01c040d220650300e03a0707a03550361401c0140c6481001c10280007800c180000d210308445502e6200340c40d0841c0e860256518031310f010001314180e006503149141d01041040080120303140580c09000704060107080400d00d8615140000d00703111086410601180d11101040b640703203850800754001c1d00c41800c10f58151750405c415018181d02d180300c0409100d004c8c01c00716043c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 335044586 1250 335043336 335043341
    0xf0403120f0f0504030206160305010509011202181e0c180906030114040602070302070b0307021b130e010b0a0b070b0610090803040605040801180807110109090e010605120307030903030f0201 84
    0x40c004202c005000c00e041c1458000c4d580c00342155449224120007120b1120f10b4070901805049030401054141c16034248007681e5200a0544c0040340e0002d0038220400e04142c541e94050f21684414a42460300800440b2000044600034204043c101082194243c80003c000300c3c001900b0059902d0016a51480003007401000507000c3c640e80c60300100c0c100010494580c0041407614403a41c01d69008558403140100705000c10b884400250300b1400306d80d4801d040c0ad24200300d14120003000d803510140783c3c0742c403c01151403008602e0580e94448440b54164100366501c00010068048001d02c0c00784541c8842c6c00c1400041c0140b846a44104481c010041c13007002504090000301d800e403555aa40c600b00501154003a101749042542030088240e0400c1e841500762010a8000321030501d801c1c1b49a4582c92009800351000c3e0621955920108040003644250781d166000d2900001ea101d0a040800480310303007061080b00b0940c4100000000694407008110450b58581003060191a640b0800e902 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 335045836 1250 335044586 335044601
    0x1803070503010204090209040c0f200c0406060f0e0303090f0d050708030a090608071407060e1e031215060901140708070b22050c060901020a140705090f0403120f 71
    0x81c550b00224010908030801e90081c5040fa07002c035001c00c0300d143e0007041541e82d048417884d60004550303404182c0100100c941c102c22281410708054500094000c0001b070216000e50300080001841059085203603504900d0420400108070000d6087c800c2c1c5400240780090441d50113401500006e41000c2000300c200080400f403c90001542c1d00c0c0c44200c000207140c0042031041d10000703510200403c10303840c001c1112100c101c1710301c001d1600e400459102c0c3e601400d0103549840e007500c11740c81d244401e055220560180620740001865640303010201952186d100030380445601d419141105020307541711800c40c1c07021042030030310345a40401100390070070900610ba009862900300142e20b2080201024000744203102d803144d484010a148442c01c0024504020020800d80c0303d0003200e21140f074480c000d4900c513081441125419031195451000112180d035200c0b42c244c0c0248018885807404004d01540440b9007500740700300380380c1070f2001030103d40d50307800310500d1540c1c80b03050708824000381c1c02a12 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 335047086 1250 335045836 335045839
    0x50a0501090b220b151206100f0b191b0609050c04050c0304020307030303053403063201050405031912030b09041112160f0504050c18030705 62
    0x208881c80c100b40c0704111080300c044150801625121030440020804000c0d03058000c1800f00300c0b0781d9401005550404058422680700da0a0074003080481001c0119920030090111310b40b0b600381c6040001c068a4106d5000313090401c0042c85400d0000041c0d0105c04d01032101442c200000c0485d08180c00740c1c20086074800b9149074105000031060080000306900c1d41c6100395810000759842d004880440d0000340c070700a5041d04414420000319100742c00003078020035103c0c00184000c0300070244803600896000e0302e150703001501d8210945250140300d114014605270f1600b815000700940045500c1c828500500340b01080ca0481140760b9103c1e40985010304805004c85003611702d4465102c4085486400840c1c0c0620f45882d03d40d416882400388000d180d2018000600b29160360b555502c2c4d170b0140c12070700c58101d034200c2840c1c5040d0501700210149c9a8100703100542450400001c80e40c66960380d00200c1c015402e0805004003070480d401140d801c59404140f504010398100e00003802e080c038603808103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 335048336 1250 335047086 335047091
    0xa110f03041e050108040b040303021605070f060503130b130213140c0c0c13091208040c0503061918050706030209010306080a021804060b10080604140f070c050a0501 73
    0x200460001006006980c0b0712090b25016007200c00640e2040c000c14050140010300401c04100080c80d205201c0c1e402078801c0c03c02504007050903604074116440741205440d00e0744040002c111682544181e0307405030400e403500342c1c6075280c0883d20000900403840c0040030540e8610001c2c569110005509503620350080c1040303038a070f024201e00f07400b038a901c050030f03c0ca1540361408a0b41c1c14824408550340e00101c00e002d0b24540d00382508100100c100c03070800b400440d40300d501400000e0221251071200c03200540300c188007404c00c0e040881030140190440760103603004205001c503c032141025100c0c20160780401060551840381c03500c0d000c4007198001003c6201d000070201c2d1075501178001c1c1c941d41c4001e07a400c201040c0d030f81030481d940d5001c4000194110140801c1d01d0306d024071050545501034010000402e880d40307114007241c40d0b0301c2d030344510f10000394111043c40600d02d0039000f0111041c403010300320499030901c0d60304124030a81c081c1105080c0b0414076104010040c5c02d028029015800c01c3c001c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 335049586 1250 335048336 335048353
    0x4030c0611030f01031b0807170106050604090608070b03060307030609030203070c06030b040b0f10050919030f120c0327080f060a1b09090f0b0d03120e070302060f0a11 74
    0x42a10003a405e0004030f8918a2507010480d17004a0a0500c4048480c964010148980380400c50480d0115034009520155200c00010031745444003801840148103c400010b4814500706065080a0294100700030750b1400700280b0400ea030300020b00c403090307035042a800910310384985801da107544201480203154031120040054061b415501046900c0070983d001e2000110b21001c0045440020b280c003640403c60b1168012418862005004041d40280081003200d1030440d0030b40c0c44040e542c5c81100c60304015a101410002a16a0307003640800758148841d114410b0b03500134125184c03814003481e50014008080d42d0410080065000900480301500c0d016940100c4084c0c0b11181150200c03000b40c140701c00100c440d215a040c001c100c402d0f5640c0d50007481e01300f10401019044001d0700c2107240b9201c1850f02c22075640c0c0d808000045100ea00c60440081404d00359600307645400e8908603081d00440030400140e22a54107c030fa8043c44900302c0c90385c41e807802c1c00c02d8071604a214244411807060004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 335050836 1250 335049586 335049601
    0x17181c05190e09180f150a11070512030118020301030209040314091201060e13080a030b060d0e010902040f020f0703050d150f0806011e0b0705070b0307030902041404020102030304030c061103 84
    0x8090a4008001c4c2a40c907540c92a02c43d5507a038604541e10311800c1409000080c503410015800309040c881800000c5180003400d4680c94900550016000400140003004006a03048040c5100300740601d01000c3d41035601d907400191342110000c0003e4280400300d001c1000c140c9880044440420b0001c0811014507000e00030b0500034111400f99002421050700400c180081d0728180b0201540c0c08244146090052034080b0050050320000d160480e0051103c1c6902d03042038040c031420f40c0090000011030310340390300400054800e118441c0819a204100c0d00989111100c120361405806042180d603848000100800a18070500d03410380c40f0003400f40200b4042482502c49040300d0303002007260072a0f601c814084091502032515454041c101700d4041000804180140009a010701c081d241c109980c0c0795040a643c0c8211045c1000982d150440c4085140c60b121340b45400340c0c00c17100b15001c0c1c5426070010f90f480c8800341014003440500360801c8100070702500900703020326480c20a1516414403c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 335052086 1250 335050836 335050861
    0x60f070212030f0a0f021c08070e01031a10090b0c071e06020c0909160608060a0b030f04020120120307030c0c020d080a17181c05190e09 60
    0x2004a100701e0010216151420001095650881c10003102d18900384c071220302964901a10102c20040d80034040c0002c3c00381007140403070300303240c0c5150f2180e803824505480000e0035084815001c41c1807601d840c450000082085d0503100c480441550040c2402e15500402d8429202030f512465000c500052014a10600414075008498a40301002002482c07152030b020000568014030300164450040c0c6a0140340105500d50000b0011050369100f061500d0100c810340742035001400403803c2c1d0340030302079030341491600c50000b80840c410306801d505000d030240035500000352001c0d04108002c05108207138280c403107211003907041900884603100c40e040030504060b0811541c02001c00c1c90031056818060141581c2101301e0b038000c0c05022880d80b140e495152b01c2c0c00074002d14041101c102114074080d1400d8005500441c01d001080c03181c107002050391480d050083c901115914404861143c85039041420741d1040c01c6544d00d011070310301c20341000700c03000c4000802c802e0344030280d241030010510420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 335053336 1250 335052086 335052097
    0x2e0603080711010e01140f030408071218060c051b01020115090b0a050a081f0b041d01050901060f0605090103020904020a0309020306060a140402070507080a0b010e070206041a0603010b060f 83
    0xa88400c003003061180010f5074402d030142c505500032803040247d030900c020100c008643c80b610407002030341010b803035031281092101d0304515040442c00861244010b00f0140c03421400a1210b840c00070a0114207940d1941c982d00642c031000745103200481c0840a9030f000790002460100c0c4000c8403810560344404a00142ca210540316000d01180503000c5400d0800e4a0040283ca02060040c411915807529802c1c0c40c581002800036400d5641111071a19621070040524900c00b190003c150841000417031400c40380c001d0300c42d2460380c0c58420100700c4207407084400000c132021070070300d2074654440b00010384c0644258099264070170300c001810040c080d01a40710a24490003581104c04a07610758050008040a6000700c0c084c000780303000c17215403501d40380d001081c0c040e102c0d005642030550351340c841134030b456032083d411541e00c1c4080005200c018426010140c0c000ca00344010b240030b00701a00c81003039614060001d0440300c114803001520b40c1c5c900b500500141c5078050090f1b039859113864071200070307074110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 335054586 1250 335053336 335053339
    0x6040806070203030a0f060f061b02040203090f010b0f090f070201090b010e15030105040c17030706051e15060301030201030e03190201020c070b03100909050a060f0c0801082e0603080711 82
    0x60414500c15640035125403412354562101d140f2130b15007461019900c90000c0c0c0c404004079811400c00c1c40c0141c03100d00145003d502100010a000b60a40c9040c5094903583c1c82050b01449140707042d06400e6484140442c0c02951303600c00d0070a192500c890890242c103103050b000d07041410b450700020365040c0707030010300344140c51910700455600d24500800d4240c60042c1d41c040c08030041c040b401c0c416805103071800028080e081c0e08681c601501907580205950040350740c10140400e0b00d5016502104010b0510352110401100c0320a941031036000030501e001c1800042d0405136105510380d815201042190000421050441000303614083e00038041c2d404404a00302e1070040550001c2c0400181096070702400d8800900965603040c0780f03104004100e40c0d0819905880344800c440041003c41c0b10f03106100d1107007a4042030b51404014080c1082c441030f44a2202c590295400c8a8100010305003160032030020703444844000b01034005140641010b4101500d501800118481044442d0150f108071010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 335055836 1250 335054586 335054591
    0x90c1704050d141801030b03030d050c030a061502030304080f0714060105010909060e01050d030c022e0912110a05181b03010b0a0c0620030906060f1e06040806070203030a 75
    0x107030100443d071a00400018100c4000103810300000e03580250451100380c074010341101e05002100d40e08d54180d52083d01d80b483d035100d000045c0100302c155809040c000d884e4282042d9100000390fa0001c1d50380c440103002030700d0f0781b6000c1012483c00d402c000481c1d1040c0d070468015040c8000021140703840e11428418280480c5c81c1c420f000904502c1070080d8811100c18011104007070380f03000e040c4061b09400c0c400850421200401240c010780e150018080149280b4107920325400c00701520300144004040280d041c8054540e041154072010f450011540da800006002e07a200c0d00b401240c40c2015a404c032035402005150103100351144d00310000d04c218140000c08600016540d140d007801e00c8207002d55213080304c0c100081e4007a10b001d40c030941e002c28425500054044100480c00c0140b8042c1c02100724182c07000414019542400c1106c1500080111100744060015000140e840c0c01d8114811072040c1c55440480480d6480f04141d0b001000c00c10103481c818034115000070744990003250302802451 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 335057086 1250 335055836 335055857
    0x71704030c090c02010c030c020d080903040e130606060201090c03020f04090605070c0c05040504080712020c0306040609140c012001020d0507170c03010f1a0705011e060501030213090c1704050d 85
    0x2841f0b030080304c2100d007060300509100309860b60b045403040e0004018035554030081100060020342d00151038402c1417140110701195542e8a050003d50715141e1240085a040c900300301c1c0401c5500000388103c4e54100c5408544041c01c5020401904820780040c140e14942010012225006540c84c2c544a101d4901446c3e0151148100320803950305507805450a5028068400054204801d021b000c0c00076004845000007424000307440c0030011141142c00b16228101801008229250400b40400840103000d8013940d000000780400c00c17000f100c6072418100c840107045400b0a41c121564250725800a00891402c28006803601207200d02c042070344042c03800066900804101a03c3c16a8000214500600e00d00940b02a0403000c43c1c0305030314403d07000c0091000241d0240b00341c030001c80550002d44d4444007000020b0048a030581d0159040c54010000d00383d079000f80321285000d840c140f010000d844800404111285038440c051400d510401030300703000c1804000120070001c1e4002e80d80e100c02c040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 335058336 1250 335057086 335057111
    0x7110d080901090512100203040231060b190f050f03011205060c0f30090a06050a0e071211060309060121021008090f2b02070803071704030c090c0201 66
    0x801e005e205132603d54100d04001d00c661003098009580041c00204211211480c0388005840795400d0b0010712040c001c40041401c07000305501640c00207100f050f00a41c2002c1640001c03200138291720b807101d0b0402108811046215016030705503140000e40c1001d5503140e43c1c582d40483c0051060440a85031031103400001610111110100c2c2d42d01d0903038809081c104102e80e01c0134520f40c41c518000110030000000301c0d910580b09400c0c29072040d10148018201000c0b60b050803800c07258090f192580c05030800c8000f0341d502000082c520110781780041d40b23103107003150f038207215407450b6090b401158060800001c3c0101c145000407428140d517402000046080450412010f854002802c02504140c1c840c0c0200101801a400d103640020301200360346100f80c095a00c6414000301e20420f1407450074020003207d14289001410191183d180020b02509007042c0751241d49024504000741080000d580342c1c00c07003440d04005c0d1001164001c0030f003041140c441d4200405011a843d00740f00542c079010006080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 335059586 1250 335058336 335058349
    0x111803070305030d0e0c120318040b0d08071b0f0305010501060203120f3408010f0e0c18030706031a010305190c0507080d0b010f0305041707110d0809010905 69
    0x407203070300100840c6003016190b10a4003402c030134a003200c2c040c010000014525100c01c800a00b03912030380c4014503501d1180320030300c11402810004090040c1d243c040071980c10746902c0808c01c40315401c1182c0603140d01c6145040c003031424899021620701c0606920000301a400001c2a00a07171b44144000d120581e2124003c0341e6030300491042124550103100031600d08006441c0c0c0135002a08110f03844030103207040ba40270400487c1e0b00200e094a00307a1000d10300c1c2e401d90000710075025001c480d100045031440d041e1014100880501500d80c21400000e0303c1c0080210707005040b410f0b180103270a55100c03550314400a0014641c00040141c4804403011a04045d807103485040d00c207000f4112045003920546000c070000700045041482400020040702d804244404003400d00c0003955800841c0c0d088200d0001070240d404804240141801e00b07081c400081c0d5180400c1e07840141006003140c0300d40b81070600c241800c1d41044010340082e4035140c7c94040c4141c1c0402011008800e8840c004115914014400c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 335060836 1250 335059586 335059589
    0x61509090a0204240e0132210c0304030507080903060403090807141008180a0b04031b12030b031203010e010f0618050d02130c0207080d05040e01050603041412090117150d1511180307 80
    0x9d440004000240000c0c0c0500047c04c03640307010b1207015007480e005502091401d1004d40b4182c1c0490310400c410851303103004001400c003822140c189803641a402d1008103801d9041c41e0070301d4007801000b45c0011140180310494600010500e02200c507a110301e1308200030030740d2040d00c0a50000b4141da0480c40030f2407003ca810300640741d000b00d0741503c407180301c08210010202507502540c503029650300300304500ea0340c2c2d0146008c1c12180340c000c00300e5494030004840d85101036002c0b000b441800f44608800c0810184420226002518401c0c140c4c0d03030a20000d66a503504603907602e010780ca0b091a00162980c00a41a07050358071444c110741964165050984140c041c1d4032581c0c29510001005000314182100999085486a03006550060685041c075045c40c20000e2002c05083e80411038400c0c1d50390003d0300f0f1864400466140025042c0324a401c000315064001c900c0c02044480184c1007004400e01c5080c4540c0304140e000c21140e6021450340392168000d0304012024051105d41e0300c001d20340401d0440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 335062086 1250 335060836 335060851
    0xa1b02010c0b1009021b070e040309140604030609050309240a14190c03080601030203010b0d0203070e060d200c0303061509090a0204240e013221 64
    0x1110340402e030790b08071a440c0014040350402490100000e5642110f0010f4411200c15002c540010861050181c0c9018160ba10005030600c8420a0002190f080500d2409803242c810001c080c1402840c003040007441144d0000340360754540724105044c0000480505407031b22088131080f40f90344440010398070718490003a240c110142c0c200003d4001d88c0c040c0001ca56241080e4009a040610308020501d2070b0701910010310108000e6194001010750105001da408402420b00718110b50410361280d80c1400340301030f4408a50b13400004100d0203806008200b45c4a0300007001e495684000c10340703000c058014191000440403d20480180794080e420a4400c205043d02c0210700715a2203100b00300c4030402d41341601ca0000801c015064042e1102103d080c85041d0a07203016079160710b010302e00d029800c0d244141c1911030709500c594960841d032000241e02c428109103024959a03c010300d065250303d040d003d2981205043c420603d000740140300142c0280350000480e00c6050b0209090004600c20840e85035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 335063336 1250 335062086 335062097
    0x312030f060a0e070e0409050a0c030507080a1a0408070204050a0b01030b040b1003270317010501050901091a0d090c081509060601181e05100504050f040b0d02030d03020a1b0201 78
    0x34503292003403104c180180300080c404981f0541c0394984508004005a080d10f009403551428401c0c01001c003c2c56000b46841c0b001449003180c5d903100e40100b08103032548141c03407002c0500403400307000d020f20554000c260028010801303400d005d19104010084024080e0200e42002c0741d0051510b01445040e049031006000c119084a50450803802030103050314150a00b0303580003540742442c0c00c1c02083c0b04040d02c33a41312060303501400e48080c007802e40c3c160b002c141023082c20088100cd50741d0012120085424800c0c00007410b030005a8441114000d255000c522945081841c4003484800380340c1204031000310b810340340400010744058a140104498000c403039400840461542d500c508816000381c0b50140040c42501e440e011000075800e4002901d10520311180401e106c00c0c9000403100905180300c5c2001d5250520703200c086480020200c002078412a616095083d103034803010030f450300e00d1754020181d41f41070521aa0240003504402458000220034146121740c006401ea01c400b012038050310782 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 335064586 1250 335063336 335063341
    0x10c02010603050c0a0303120b06040e040f1109010815090708030c01150509010e0112030201090f0302242701110a180b1e07050709060803090414010f030f030507020312030f060a0e 79
    0x1a907009e03000c1c058100b50444001c110000342d2418030145d280c0a0752140d03000811030401818291400d0000ca07804503c1280d1400c010414180002060940c000810070414001d9036440303107460515907030354444c0c050340c04006a44003040700b040d804032100741e000042c01ea00e410b8540041c484864001d00805c25101c00c48401408010340a002c082880c504c03c1c4008141010a59a80c070405c00d40c3c000e0440142e80061030071070074001c424414650900844120b1441ba2801440701003001100c03000c07008124101c005240901c2d9404e4010705440802c0085071556011202c10060505140d04040d003c290310214010400c450180b040312201000070002e40d0a004507440c06610b50380c00050112842d20810b100056115003034060381c001003203024044d5455141120038041590841d51485000030780342030041c01801041c3c9205c0083e01c1e040708803101c4141c014901554035108080d1b029500d0f100300d1555180a4820300001c502c29005036210625036150fa1080c0300007403510703001f10340480420900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 335065836 1250 335064586 335064617
    0x50a030209092a030d030b0306011202030f0703080a0f030908030f0c090306040305090f0103050609130c0f080a030e01030c0c11040209130f0e061003021011010c02010603050c0a0303 80
    0x1060b07401c00b81d00d0701500c96004901100031255683e03915030507040920032041e10314510342800180c01c0090b00b41418000881c00c0740000751100c10502840c1c40864003010881b0075034504001d0350118040010031542c45c59164100401d103034104d9560714000417901d012540e60140310780601401290310100c01801c2d0b0701c0303524000d000700000030302c0301511202c14000614140d408100c01070049000c1c1e15079503030702c600803001e000134540700c05820741c18581000300b4080c150300d0b06042c0e180c1c0b1501c1c1070050b288001c0c007481e0460f040f1401d54800280b55084150109440c42c003c903c2c0d09402c4c3c42612890b095005180054080d1040b03e440f14000c22079500c600404501a103140c51020a030003400146484000700004540c45e01c0481030040c040d54034401d9074206805403144028640321034006166500c1d0405484480c0340003400b0080c01400140c1510b01c00e2401204010030070501900203104110360369000900800036440240e495201c0c00000e42c842d814080c4080d01a281c0560f0f404031140140360 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 335067086 1250 335065836 335065849
    0x1050c070c0918021305010302130216110312040807060207091407030b0a1203091d1012080d1a0321220906030b04200f1002010608030406020a0b10050a0302 69
    0x503d80100000000d10500583d07500b070440e0541c028200d0006070a50540c0103005250b1050401115000c0c4104010903201d164803501320480c640c0a03c5406405903a50b0101e030038010b0141040f206018080b5010900300c40114081d8140c0c1c1440c1d0880e021650740c0c00080f801d607610070304520b22946441020071b0399580300c1d8015890108000c0d18540c03a85640305100c0e0040c075001001600010303080b1401b031010542941c4141082d84102e000f990643c03c2c40d41030b40110035058801e112043c0245032000d42042201c01c192444105000d004102d03c40d954400e40e04003a800d600200d11078000d40030000e1400b4110229001c0346a40c1c8a051818511240e8039170800c4400c421b41b51841c1c04981d04000323428901070181354007961082d640303014582024a4079228203101c482e03c0810303180459100c080070762500000f00a4a000c21103052800031410b040036401400340d074000c00e10038000002c01144641c5c0000b0348030981031040111251942e01d41015600c1c400341802010390010702a4403c102601c1c120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 335068336 1250 335067086 335067101
    0x11802070b0114240a0806150a0804061413050f070f060e03100c0302040312030c080a05060d201201090b0a05041401090c0603240302060c070513020c01050c070c09 72
    0x42c04c0080c815001d103001c2c4900c5044010700d0518188002403011045910200c425003142c416287c0c10a06441107007404240c0c0601c41c14101000302d5040054280007850f00001848885403203c44523030305024080a496000c04401541c051048015060b00c040000885600301c6001c4c0002c03d000d80d0030035030b08072803181d1941d05080d854801d20a040d0700c40305642c405c94010b50180d440040c1ea452075840e00c1044882c0c4001b201c0240740c034104140c2c14a80d00074500c07a500001040c0001941d036525400540b071005940c1018240a25000c0c40280c00c186602440d4401001151042401c510500c8d02c24241c402c6000020100042640800c4140032260042904203119402c68405106030300111800c41708100d0080d03880000000c001c215454161051054190710313614a50024002141703601845101840000d008040004070240740f10750600801c4045c1034010582803017480d80d0302c400c030003a411901c00940c03a07501c1c10001c2442814058216580305e640580c0c1c5400c4d00e440c1415140080540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 335069586 1250 335068336 335068339
    0x70b13020a050f0427170c0607030f090510061e0506070f0609050d02030901080708010602030913020405060f0403020a330c140f011104050315060f18011802070b0114 73
    0x2c0d450000c0c008003480343d42a07100041c85d21100c4c1138840301d05120a4840608107030340358800c1c04000c0d940701803902003542a0f00850341c0c1400304162540b070316424020010b80d0760141107406901411140c0c4000b40e0410002c90f80381158002440c104d8400683c500e103807a119080e8080e1003040b401c400a08108112508035000d0310000619807240d40700c00d4204054000c506005800010b108402903800030300080e08102d40d868240250740c10304030065642e00c01e0300d90040c0300c0c00301d00e40740c020246165012100034250192003e0345a120a25507081183c0290000724400c40c0d0500021a40c98a40400e51444400300074034005032000344003001e180d0a0300b02601034100441d5200d075501192000394502d5451100d04014550407066125581c01c5880201102d14515000c0104110940d0001030295030019030766180c04454a800002030712540e02c040d003083d04008ca000c0f00d19000540301d180c0340d040301d0b00c030031001468240390a5850224816528010407a40315180184000d031943c3c203182403c00c50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 335070836 1250 335069586 335069591
    0x3030403060f06051210180209040816051914030a14030a0e01110903010e0106060e01140c06131e0c1a0702120304170708060403031817070b13020a050f04 68
    0xc494005c251500c0459005100680c002c494420b4442071130b11400c1203100c2c00306900c00f0200343d154001822420301a2002d058443c02140c03044510b64241c0c48205495400011981030054003503081e2200c0d03e9840d41594180340c400607400001c0404012680c004206a82d0a8900c881d8030107840e445070400f408121405a0700c603280c01c4171780f100740714505c07038110114110707509d40b09800100360a45412500d06022a4107041c1c040000c05c1d000b08071030200d14000d0924010210a03550420400e014107040d41000d44111020b200450440340e240c0f080c147c0c0a550608c00701d0400200328514081d02101c010003030203404e401008180d03074580b8400304000e00c8030720b00761500d16250001510600303441040c0003e60000101000030a4210292040102c200130280255524021a15403940b40050025092584424044d8110400115a681082d500a03901291a9001c2c44080301942280c5c000302d0304840300344007081380740300c041000d103000d158010251142c190400b01402a40074021a0164001c0d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 335071942 1106 335070836 335070839
    0x60f0f09070e030c090f0406060609080a1e0b0708090709090b0f041e0c060e060c0a060b0105041805090615061603050706051e0a020903030403060f06 66
    0x80d030754100884100d400d5000310303082164060200b40c0c03282c03c52081203007410303051724628040c40c05004100401604c602e01650901040e0044240b207078410300c04880090392540704541c0d180782100300325005a190b40d0750701c05408406c3d0344034808510100200004c130501000240014600e10605020403040c3e0b4035070704142000030b0712052360307484503100180a1041c903441312031190a042074107441401311420100003480d00c038020b0308000b500181044509141c00000d580f02c00c40030340094a1000001d556000c0140160420941800000e00000030700c0410344485001c0c0c000c41c0c0201141c2480d000c072106003440d1b40102003601c820307054200082a6103401d0306446806068000400d040f0596042c180c5544c01580001800306082c00108941c4c1c0b20ba01e02a0b0f0143d540760010f009543e201d264050050f402040307681d03601507200f440100045913054010a81d240b203000f90016115 = true := by decide +kernel

theorem cover : BRFrame.Cov 334892086 335071942 := by
  have h0 := BRFrame.cov_init 334892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 334892086 ≤ n) (h2 : n < 335071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
