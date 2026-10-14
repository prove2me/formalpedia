-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:10.600686+00:00
-- url     : https://prove2.me/submissions/5b30a7c4-9928-4afb-aab5-d56e6f034fb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 380035971 ≤ n < 380215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 380037221 1250 380035971 380035979
    0x12040305100510090b031203013003090303080711010212061c170703030618020301051203070c0e130b0702070f051509010e130f050618042622 63
    0x100e0110658901c08103141440c0c01c10101801104a5104071090180007095104103103001a0400000030300c550300c0d500002c4004a120000001d12440b14020419042c0ca64042c40014064400c1880c0009000400e4482c062001a210b40842500f01d000b03070030071545095002c0303002426a008500300714803421840c810480c6c54503100c0c0081e6044084c03800481000c0c2c1c0c0d1512083e01d042418001405041c800042b03540030942319500120081407445180c0a01140c520030010180d48280703c0d0500c260400b41c840d0340b100c000401160b4449500c1b1003440860f0f841c12904084102008041c078036040e0342c0d036607554042802c0c82c001d10721542007a4040d28549080091151000110307401441c000d2100b19200000a44160126a0f84030000d00b49081203203608400520742012590380c5803091400d044903201d814016802903801980216204c1c803691546100041d4403200468015100041d0741140070315011051201140071903140070a6403404000c00d9040d00306200c50050f03103a055040c024200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 380038471 1250 380037221 380037223
    0x902180103062103030209010e030a08030405121305010309031b23120d1a0a060201022505210921060a1b0e04020d0504060506030f071206050907030512040305 70
    0x20007a00100d800c00010020f904a00c0e2508800da01c80282030503070000300c02d1620ba00681d5035854614000302110100412450200c200e50005e440440e4940b2a42c0c64a20721a00c139201138a04205964803020085454107004401408070014190148101e100c0500c140700c6024100c10704641c040c0c042c05039402e1940e030000303070401060034200160340c0240302e2000541c81003408880100c03101601c00700302c141440c0d03074040d150040c07a03002300c0e13010440c1040090015010b4000c0c1030011020101c5144d0480504644001c1e56101c04004080750010410300001881e984150a410099580820300b0f01d0041008180d107120750041c0c0d4005085104200c40c600c56040014a41c0300c5182442842009104e0b02d580c2d21412110b4291014414400c02c102c440e07460b194180c41c5101ca00b100d00748240c2c20941000d0f40180320540d8aa4001c5c06050400482600c000075241c0441d500302c0b00348001c2001d140c82d007000800c4054106891409080d40010100700204005075000d641e00d0600caa076140355140c15 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 380039721 1250 380038471 380038481
    0x204080d0f020c060904150803040602060a1a0f04050403090b030903270307120f0b0a0603060f0c05030a0b0a030807050607080a0e060105090403020313031103010b0108060a0b070302070902180103 86
    0x1d40219070021201c0c40d0507403510001c1d1224414103a501040581d180c10b00d45101051396002160b05120100c0c00003080d5500190b40c2c0e01440d0030420800540801654240c0d2400210801c160002c030380c41d07105205800c040d07002c540c0c403a0007480d02d402c0f09a00c0e008608110f61042e0340d501980c1e4808254004111130306513080c008400d03541000c500d070100c50070100c0d40340c009a11482001101d031403220010700901c00d1541300b242d41d0212089086241200c04000148920f000c2690103502c7c3c0525100e1598852066043e1415152103150959580c411600003030018482a89c0d000382c290f070400000a44401c01030444181b1400c00b52100b80350030107009003031550041c03000b021107041c03c0a203012a0b8010a2084c151a01990400c0c40c0355500d0030280d113584903091070b840020b4900c1d0b000006000108400e0540d003001200288031a102ca4001141c3c4804144c4041c0d5204094036001c001040101008048281c8a40180c030561036841d5800c401300d8014180711120a0117800e10101c240d0b900d4070807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 380040971 1250 380039721 380039747
    0x6070e0301091416090e1509190303091502120118020c0a0b06190b0306010f17090c09010602010b030c0f0a05060a0905180405030a0f0e1903050105060301020301030503070816060204080d 82
    0x3c101b00c0c000500c8004c0e942c44203042c44c030300c0c01d00740502c0104900702820304c808601950b40020580b421021441c009000301f4400d0f4059408240810015401540500032038502312410500e0f41c88990034100e4030b40031511940c079940c0c0820f900b000890019481400800d0810340142e400400510342941405030721041000c2d000b40038250002c1c180043d07a030900036282c104e007080c602481030561a25041c1d82c014010240d04040c4d071010000c03c904d94000007000116000203958003611030340d803840180d00740d884540185138141c01a4540d101c2600301000078440300366004200d00c84495403000411207992055141d480050f000c080c060003a030a003140340c81d08600365942900503070310313080d2929600c0740078030b405210800c14007010981e0410b102e008880c41a001c003d0019501940221840d1400020361104a4143d42408001440d501d418070070703281244c0d000000355150019660301c41c00b40b58810280d0710462505541840041821807010708098110100108000f51032250098a10303120681 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 380042221 1250 380040971 380040989
    0x120108030c07060509060904060801020c151006050d0f0c0f030e06060604061803141b0301060e1f18020a180641040f0609050306070e0301091416 64
    0x85001140000080d1100840350076180c11078171040b810b400100e40d44501d05e004c9901900b0103030007190030f100640c010b004000ea9042140c01600044225140070307201201d121200c8219080b04000490180380107160401c90b140340090307950104507c04044070080c2002e60006460300c45031602071170f010320451602d0850440200200e01d000000030b501442075000b14010002c420803030740b01d400c60141200014561020040794081329034a601aa10f041c0110180e400e00002040c164071400d040c4503d2098500c400f5103002d4641e0b8150b0301040b1011510b41e86407080f10032240010314441102611074030321503007440160341d8001c400e500030200240841840d401e2800ca040c2084102e03003010081120f403981d0310801c28803c0c0254030741c0c44160480001c0c4403c1140c01508135496409550081044c0da41a0410151240c0c40e0130044a07080c056010b0150103a000c00003180801d4003600b11752101d800000c0c000b203030b00f50050340c0303005c45810000700500040e0710103561151b00038510401c4a0141032511 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 380043471 1250 380042221 380042227
    0xc0e04031103120c070204090203100b270408070312050c0a0306090c080403030b28030c06090806060603041e05010c141c05090a020604030f0203060601050325111212010803 76
    0xc3c00700c044104080c0910004000c00112541152241c2d000310f060160002c05440302204402c0c1c428003c3c1a01c113000d54864003240342400900d07002d030850300d80042e080181d444066a140c1e40c0e0a28179a00054042d000d0141813560102d200b1514000c2601c40d45201c83c2044d160705485030064140c5600350411390740142003084244040d42c1c4541802d500580501d000b02e04201001c0104500c0164a0641101c085128504141c40404007540c0004c40e48030b60584880303555600b808841c10011400358000c6504071a000c01c4007854101d0286400a0181c80791b02c940c90784003003400080e0044102d0454060751150001030000b130b0000d404030807642030001c220317285c145107408001540c4240c0006029a594038004a1a4001c0030800c1884c510381c007500481d036994070f8bc1410807178010f11800481c403074402c4200185155114a0036a8040e20204a5030003000038410001003180e0f030800140000c105001d0003c1003140003c020b820500c0c1945c0c50f1441c1e507510851445c24441b0016000300481d58010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 380044721 1250 380043471 380043487
    0xb0d050703141b210414010b0310020903030f0301080a02100305190f020405121f06140906010c05120702030c0607080715060816090f050907050114070c0e04031103 72
    0x6900386901010b1030140c60b070b02402c00c400318111400745010b84aa90055841e20715804c03010b030f403d41e0b8002d90155400031841c4495a20150076501100e46168140d0000c84d003580c4e2065140d00a000784d918020142d03400c10350164510b1649401c2684505031a900806134001982407070752101c003003c909071800388501d00c1d10041482c071040d00400051106c0f541e071070a99030f0f000500d40c10348010707210003000080201141c01d0450380d41d4002000d19005207100c254555024038062051800b252158031030001008084800c00814001c0109441d050041c0800c007030000550a10035488c20b050035424203503ca800c180149498170104030800c2d402241c04006900c04151110251001e140d80100d8007100300902030000c0c0040c06041c1d01c002054410410034030140410840d11506035103146c442042541c0d150020b903800d45d40c046d07442e03030380c59001084180415440351440c0284d44007a8143c1c1e038a84160786d034640100400c1a40002510300341503061000305a8403400c2c0381d00705510040110308000c03d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 380045971 1250 380044721 380044751
    0xa050403030e0f060c1b01090305070201080c030105031b0105120a06170c1c0f0f03050a080a090c030809040b0a082404030f0815030f01060905060105130e040f020a0b0d050703 77
    0x28040402e00c2a001c80c140a06c01e41d44181c9811180909000740326031403c514000c2c007103030060b0208070b02040100d1b00060444428900792812960010010161030458109031b0703082c01002ca545504105040100009c0c0c0b40b14508410f0280030a500002030040c80c000070701e01910303d80484444a0380040e1703002985541e03481003401300584440d981d10b02c0c0c079400303160000c01f2850160006288844c000d041009050b0040e0281903480b17015192245a0b61302d040003d412904c0c1c14030001c044002900080c000704011030040e0201e0030001d40002000107000000480c1d503e250303880311a481c3d21403010021801035031054011104c00e8403201c01200d0500f0340e0040d00720f9503400400c0040099440c0000d040f21007055411010074805807c0e50701c0d186102e050700380a400c0d20300a0a240c5400d03e004204154850340807684800764848000c4030490a00b500c40344203e0002e001a82c080c41240e107800b01594901015200401d41c1c0d841d80c0c0e5491845a8100301640e00040030341c01451f140052519001d18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 380047221 1250 380045971 380045983
    0x6021e070915050d0f020f04090302060403080a180c1e0f15050f0a0f021606120510081c02010506010311040e0402150408010b0102061008030f130e0a050403030e0f 72
    0xc140390200703003500241a60b910401243d40416400051800d54505003d598000010800d009403800f0b040c8458090174403080d250301403001030059100e400000c0c003080c03142030030b950003041c203483c0804c081869043c4040c41c11034407501a95038100700c0c0c008009a11240b0100e82c001159402008500b516100c501c121510180c03061800c50b1240046040303126204604440f0025601c0d10803a440e1903410500410440008021001610441403210201d1070b005000310100c800c103a8070040404210440c01025000207040b029000f4040749001c40c81450501c00c010445e460242d281104c141034000081c01d6540103491141418503002d40c0d0b0b001204040c08441c10783c5d111180d112001e840c2e52020820f4070140320806248004089004258003906401c40d0030380382000d0f802c03960f054407001c42d2100c40943c2c43c0f01e0305040381e004010b0400d029075907402030680885035aa80c001c82c00c0d59104076200c134003800c8952a4082d50340341c04010825070035100302c488030404040208001a0945100d503075541c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 380048471 1250 380047221 380047229
    0xc192610050315011a1e0f0405100905060306240703170a1505060a0203090405092415150408030309060105041b0c1e0c09020c010507020312060d0218090706021e07 72
    0x300c005001003180000c20740b43c102d1b800c03035142c1035030f6203401e00d0002c3c0c2c0c81c0c1d41080c01290303c101c800b031000041c4180301c0c04600060343c80060840380b8540310030040011035242000c4d0f038030703000c0410b00a400c030142e0b040010303064907802510303102e5687c00e01a0400c1320b0100000c100ca0000f51410b0140740c40c5d00d94980024090310019078103c0c0d40d482a104c4140d00d540205000030340c5c4a8288000c000680901041001d1412942c80c911240d50342e259294001d80d210444904001c44440d075000042490650000b59103520f102c503580e49441e40300ca41d101d04503802102c3d0b2496541c40140108200c0c14640304040c80c408961424107403d01c1c1e10304000b003c0c0358103443c01520302103000589440388807510406418250307202d01406502540c17840340c4400780d00301c90b0481e000f9518040000f00c01034000f2007182c400c2c548101c4031800c0d0355a14000c00c0150304c02c8180c260703080350204619011054021840500510104006102251601000038a010310702c10444641416444800c0010080000c906041d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 380049721 1250 380048471 380048519
    0x1b021c1205070e0303070c05090c070314030709050312070c0e0105010c1103030d09030e2106040f0807080a0c210e0904020d02030111030a050c19261005031501 70
    0x548420b4821107080c000d200308140d150000003000001c0001e440320301c004660342592201d516640e561880c107010f0107010030190200c0c1d5500c080f081c0d110314000040d54061401d0034000d0f4043c1c1c542c00820b01d481c4820301070401500c800260b200501c10030104c1c2100070071940101010647c1000300080044150305401040d020400c1594001aa0188140c90300c029220b142040241c0e258140200815441e4844038041c07030040c05149080d44004403a403262000d080c0003040d0741d48a623038940342e210340d0124069900203c140601000134600d0701c010701d504807565541801e80740907414140503045225822040b402800e007e00d5010320380200030300350160703c01c58546290355030328008100d400c180b04000940c0740d403030322030020440d902d510080c50080c0ca0000082025035107110398182d1912440101410001070400003108451042400140030310303007016078071400c0c000301c1d00c00580344000340c4030200e1001c0b001c1c10510890400300030a10041010b8080d540c0300754542480e80d54811070907000b44c054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 380050971 1250 380049721 380049731
    0x311010612150f0e032715040b1c1409010b030105150f0d0507240c080711120709020408010b0f0a05100203041503090606231e041b021c12 61
    0x10001103502400320f80c1002030030350b55107446e91b03402011185d010300c0c2c50420701c00d62031242900c3ca0038143d942c540080301c424072991400f8203010065889420080c0d4000b00687c18422104000c0b1590281c4180c1d0103921340c043c1c84900b00491054250745980325161300a038580740c10410040c4800c6810841c4042c00c0e1183c00507990b892021580b1588507845c003038184e00c50814000780701e58155071050308010b0044400740721050300362070488030791440c54009400600c0503c1804003041400c680940407c40040900014215011040e030030400c540c0d00584106a010a08000ca8402030051007005801120907074441040e140024512103064000c45008425410f5136183d110f0003003040310b000d829885c5800e010000035003401000f402036600100ca00300d041c5000001c3d0603508040d019400801038840040421486051004500c400005145c2841001a8a5032651503500c1190045007c0c9402a4001080d80c100a440d1406140c0000444602c404c084000c9691001c501d26202d80b21150120f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 380052221 1250 380050971 380050991
    0xd1a1008070e2214010503010c140301030809061902150c091305090a140105061003060308191202040b03040b010f030c03080a03060e07180b0306030c1c080304031101061215 76
    0x529804020340f0340b0000c52800700315204656036140000e040f540105c00a01c1074820307103d422568405040d0141c01284000d000500016a089019010601002d401c05060028441d07944180c41d00071140900560882e00310803410000313890486501618007402c07075140411440100b545910340d45491000c4035540c0c80414120b603070a0000f042100c0d000341900300d00b200c078248481e008007030940b01148920000b8890300c2202d4000e000e040d040b01e4105900a0411007070540304e86804104484070010040d01c00c091160305981c500c01760000d4040600710399164a0030703180607012824180c10039002d0a866050410014000302003e10961398041205902c90011401c240e0242016410200b01da500b140e0800022035803000c0d04072869940c06e031800003156070790080c03c81c841c80182c402607015008080705200700d080c02d0200903561160720450760101100c030b851310091908161821000560306400c545040c1c3c07024000c9001400701106490106c94043e561150044c00176450b030300e0110785600f0f0313100e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 380053471 1250 380052221 380052259
    0x80f030a08130b041b091413030e0613050a090b0a12060b06270405040c052107080703020a08030405090601030e0f07081e0109080405060304080d1a1008070e 69
    0xa0380d07103a4000303803c82d0941480c1c58007801e00d8407440c20f60001503403009000180031480780600319030401e48035030b00d00d01502c4104a031000b81880c100b0680c240008451001c603103898002c0101000d011044540101500b41801c02000c8510b80d880450542d0038400100c04503550305c006007048a06a0550041200051516401030002c6425480e48440c01241c075810512812030301000041d12840b2a407154401481044100c3e1010b0754060105018140b0030f00c024207000070040c0d4816000e0003001c040c46120100c0d1403034030006400a0100740c100000420840c10080040b00c0030f00f81c00c002845c24603040401041080b0001440303a0304040e11089158030000f014425254250280010340c0e203110740741d07100c0135521100c25104100181091040c919406018840d01908650200f039683c601481c100c20402c2940001d041550480b41c2042600c41c0780703910b8403e4180b0046005154007031070700a0010480c29004014200007486002c40c20802c030381d540f1204c1d007104c440080310b408600d480030840c45 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 380054721 1250 380053471 380053501
    0xf07051e0942040b010804150b01050c010f150509010602030a1409091303180e0c0c0106120b01090606030c0804060c090503010c050d050901110304030807020c060d1401080f030a08 79
    0x9030918582192030429105680b0000c81090030040da41844444030002c0111407030401100c02401280050465104040030394001008031801450075908201e184d400550031607110703581c1c1c60400743d61585004810b820300d001810003050704032901003140d0300d030180c0603440384202c91950f4108044880c2620518450000340d83c0062000303418103800d49050101c1918901c40d02c0b40540105e03146180742150043d80901c080f06482e04103401030151f8030307810b04484442c0c0000202920741e540b28100031a4007203c0642a401e0580075159025055151184450445010380c1043e8100b50901880100c09a00310541c0c0e034025912032030024034503815800840d11000d03a90400d5034507509110b00b40714000e5001c4c015100c1d000e4104410421512011821030898000c404031103a605002e03c002400b29004907201540441c0d5401507940d80094540000c2d00c1e5030001c8188006669641c43c0c1002c002081c903441c038050400200280062100300405a81c0d074011140304204000c544800603101031501002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 380055971 1250 380054721 380054791
    0x40f0507030f1112010c0c030e060405030a03020718050f06011b0b0c07051b0d0b100b0304060218030706080a090501060510090515071509140f07051e09 67
    0x3072000b4590340c5151010031140e02c0c0314082d100b100c040c0541d0b0020107041c0304e5140703028503544a200903c6400e0f80c4c15030f01d90401244550313205c0320600c40018141c400340100120140301e50b02800e400b50a08110b683c1035205401086422490141008651300d92050050380150007400c10800f9040d81c002d20040c1200e1000c8000d10344507003002886a819500300203000400c0c407802c180c03a405c8110243c0e4401c1d545403040d11a83c0704110001c400003240350011025007101c2420200d0007055201c114046155000b550200c907465070001d804140c1ea044c04981c009035050071800382041500d1301a00500c58070b409411444002e5a032080310080000940c0301d02d00030303c009082c0a0105089140182803a2581d120b03850241401615000380c2c0300000c0104d580d01035001407102001c3c4445001c490007403203249004c98aa0b010400d01001c0e6890811061000c600b40310000c000d01801c00c028010614080c400f40f00c06452009494a0a540e540c2205a40b107041180050039400d8450708a41d408014070754 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380057221 1250 380055971 380055983
    0xb0a022706160302011b0203070c050f06070c0b090f060c100c03140916240c0602040302031b0f0d0809190b0c0604050634021f050406061d040f050703 66
    0x100c800100f5406400030720071250080700500c83c044842809903280d101f603c1c00100b54000007a010b1200e480c0c000c400d82c07280d54028022070b0a11180c2c0e900d040c8510a603810210f219500231401c1000c0380390403608a04035800c152035043c1002c008045041e905e90b1107550582256880d006012241c0f440303a8815410781c500c50030350b5542420210071950b01d8140909010305c6071041c2000104011107a14544544d034100008940d42e0702000400c1240c1e8005c2c2c000040780c003203070200000800350360200030506484000880c000311034a04141040304141c0010703807884c016190141c800c4c02007682141990007a00041e1000d007180d80441e247c1ca1040441600a207002c1500843c141c04142c00c0016002d01ca00d20a504039401d50725a542d0b03c441401d00071107450103a12041c1440c0b100e240040c15071101c07036405401106c0341540301405455040c65042d40d40c44400e681ea0003040140141c0d805020014040d0340b2051210756502ca10048510300001c0000d0199280c980201c0c08002c000c225240040d038002e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 380058471 1250 380057221 380057257
    0xf0602150a0f09080909131a100b0d0e0c030601050102030409201207030b0301050c0f070309150f080c032a0408060a05011e24030204210b0a022706 65
    0x11519400da038002401c1d0364010703618000060b1031903000465802219810021a04400100d0240d403481c1c50701c0140f00394100d40c02e000b00010f000c90264003911044040bc6030100c0d100300c022500603d001e2000d135100707119510560040142c0e0340c022045506950038000b000c568201501d6908485003c603a44640c01004002800c41c0c4541d80c0000c2c0c18091050f0707a0b4240049610b20302010b0980c0c0c002e0311105030341001000b8180d00c030940c6600600350309100b8202158200d65551039043c0480480c4141000308504e0845505000d40c000c4040760303c140e400c1e94080c1107041c1100041d00b050401b080c504080d9882451540010318217800b510000e01626040700d1079032421107030000c0506000c0c1f06070545202c504441385106a202c0d070b0020203a4007042080d003800420707410307a00020045602200c00341942008045a044140380c4c0c200b0f030071080000e0740407000e0494505258003040060010311810b00c14480fa40a840900c0e150352001407508011004141a1000040c1c0f64842d50350720008080041c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 380059721 1250 380058471 380058473
    0xf050a0e120c0114250212012a0203130311030f0d0e1809060606030a0908030906040b0c040f151b0b01030b0603010e1c020304030804080105100f0602150a0f09 70
    0x146400c441c92080e6a8035003003841d0b9411040a50140304d06074007400e908a45102008005c60303843c1e400403400140f0a4006d000d03407501040c21a4411100c48003c00084503510341c0c0060320010103044c1a04030700c000c41c986101904503212110f241e0100074060070500401d0122540c2c108081001c0329060000c1da00322100c400c1000c6c0040081501072400f40e820a004007135518807290356540304000c0740340980600da450380200300c1241d000500321b420711642c03021890085009000a140b048207100010403003030805040c80300a0150017806202a01000c02003400400c45142ca50340c226030022b80c1c004180b85101200395400e26012031070307140302c4a035140301000707000c150500c0504032400360440400c44c0e105c0006040c00d03940c070360340111043c3d88075400448501c525490402c1d401c04040c8107403030509440c0e50396a040c50f48070754002d1207960345074028884015120b0703075088000c140ea480840012031402d4800b075180c0b1200f10b414a501d500e24000542c000c80b2540010107091940f95080086400d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 380060971 1250 380059721 380059723
    0x2f0106260115080606041d01020f0904050109150315060b0a2012040e131b080f0d0804140c1f090b180d06020c010204120b060904030f050a0e12 63
    0x5603880340300540c20410680010005454180c0584000d203000e40032640c0c030842800042c1001c040c001c2454140c50315482010442172000d010800051080780e503565410904100c25564181c0100b840b40b46060643d0b1500d4000c0442c1004030b03070380401c1d40c018904400200300010000c5501031544950000340040c25141e000c900440c07030301107514025416424a0321a43e980742900007180740765007070030402441000c4040301010380c4074000381c04154000b00c043d600d0b4880b00c40899002d5080440c071110520960030148402c51108482c0e600400d0a2006406c0042000c2e0700a400a00610003020b000c07024194103002d84008440301412031030000c8004455102815418034441c000228070712404140800c02d0803c98014000c02c03490845041044400c00c03400c0104a4400c4a44950030400f003d0141b2080c0080d0005021030040c2c41c0c9503118500b01500c43e69401404640b003400d2030002c00c800240c2000d814160948245005a06c2c1e44110740c0a0b01c81210440342c1560121404015070f100c004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 380062221 1250 380060971 380061029
    0x409060e09011a010210020705190309080d03051608150d05160806060d2901091e020715050718150315030b0610050d020c0105162f0106 60
    0x4004000c0140d240782e48509960700f0340364480c07240140c02902c00f03031502e407002da0060110a8020406c1c1d075410502c0109041d00303030b00100b2040340411086901041804420b0080308440c28040c10103002e1031410b060081030360500c2040c1d01c1c06200403a00801d1090701f0314884100d0b02d00740a03006a111440030304243c0d654940444100c2c090318841c04e800314244c4230115405001e40405000380070103918503540d502d0390420103401c40309500c101200d0040080000020785000305440c210016102c03050342d61400080010321110780c4c805004024041c0010040440344000072040070340000c494440701030850b11101140c41990020007205004903d284003042d43c154013140c0c03601e080042864005106882e103625200282c4131446440000c1c3c05401c00307a0404d8815407003480c0007841c3c01122001d0008a800c4080840560ba65500030000704180385980d9505001c018200030b0010220310040182c2000441d800403c9440c070403c0e0340c0420700c025003040014040d003407060400f005528683e82c100c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 380063471 1250 380062221 380062231
    0x405091e0f0a1505030a06020c151501090504050105010e040c0e1003021207180303180312020c0108070306180b0303070f031806050403030e040c090308030a060e1605120c0409060e 79
    0xe03e400b50044200d0851032000c4215003001d03002d0425512641c07503000007900140700ba03044500507200108005910501418400d1400d2404d0804003002000014465503c40e00018025480d003001840a07030f810507503410358620300304c4004c2201c24006102f11a201c1d40e03000320603003100c01f01001c842015096000b5206074580e000900055a41e541400c0300e0802001d100d0031000b00c039a2000b400481e104003c8405205c050282680303080d50340c1d584840d600182e1003140d2005801543c80300b0420341c0c0c808003094001c0e901e441c1c240007050411407160701030000d00e0340c101c1c07510755100b03484187d41c0c40c1442610100354010645640d55801c1e800c0c0a0000c0840b4411344903022010b000100e1028010000d41e02a0307601a03603024070b030702000d1007440001c05004030a40113002030707601d0000c00100d80000451244011600104045150095100c1c010034007030715020717008031a0207020300c40980c800c6c2a5041c001d005e21098060303032240c080520f030521035030b000021814200740001c80d00601900c4280c0c050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 380064721 1250 380063471 380063491
    0xd08060f010201110d2703080705130b042607030206040501180b1603090e041e030c06061404060506040e0f10080601091b0507020a060e04020f040906091404080405091e0f 75
    0x3150801443d180712400b402e004000c01e0308400030409c014820005001e20866000b40304d00e040b506c070301c101072494219520501d03480c142000c0342c2c6c0c940d4070080440c00000c085040100490b5003140d0000c1c3ca540124004e1a04100d9444e68801501d54016003120082c21460480b03690303000e4140c011b40310f9401012050300451408000002d24102c01060301c0c2c45142c200e00b003180d4902949654200e6a10b90010941c1008000188400400d82c103100d0380300282010a15060880002002e00054441660285128100c21b00042001031542c0040550020352403a903208a5500e032180d8404044407600440b202d40301e00c000201d40c154559110540007498222840b403c11902c160488180c8110300c0300a4200410410420080b8011505070444035802000036003070000011403149250070690200c04a951210380c2040364900e0313489501746020010100f9051454140c43d951030320701c110700c6168041d01e1200e0004d48002d4088110208114031040c0d05403d605103800c413210741482c00e407640080c0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 380065971 1250 380064721 380064761
    0x19030213151211100507060f0b03010c08012105031209250501120e0c09041e0515011a0f0901050702060403060c091710181b06030e0d08060f010201110d 67
    0xc1403604c01040c0c542e500b000d82c5d5440c031740030075659040302401101820342141526101c1c100d10540c0c080c0110700300700702940c0c1c503644c0d50362400c141400100c015001e100804040c01a110021a5000c1300b11180e804903044001c22070389642540a02d0542800207083c0e07020b50040c1000c01d0f0305048040c034022550240e0b10060038100058070281120320740315940d0420740c020083d00710310341030416241d54018003034401071940c180c2122001990004c0c6400440d034540202030000c6110112030282409003c801c00035070000380508201c88014452401c22941070000421f215045a03c14400c030756113030394064001d588540c0d0300d140ca180545051561440032562103800483d018941002446084036500000d00242ca0624449002003090840091070104214a4070f40806d03a151030851803035a00f841842c080a142600003011a42a1002d003481c0e900059622140560710070001c0b90400011110714505d14103042c0140c0c01440b41c0c034840c1c58000e001140002a030700185e840140c08144c86405125 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 380067221 1250 380065971 380066003
    0x16060e01081302010c020109090509070e0114030601030215070503070809130c120b06130b0405120d17090a05010f0605030f01050906130804091109040b190302131512 73
    0x14030040e00311070030700300210b1440d420000344d8811180b540c1c0081c018185000b0381074840c4180c40a031442125a2031059014501c2005008500003501d40101092000c01540140543c002900c40c0b8040c1300292180c44144c1d024800101203400326110540d100084035901d841a1611081a40040c4145407140c01a124481004802409000d81f541101d9803241845601081c0d2800240007024581e034000c00140001c8845801c040c074920090540740318441e131128608020010103403501d07158010940c00030344004000b03540224800d454900000c0b503400c45a070fa0101c00615054004030f0140040d030030404501c004150660106003514030a909840320103203030131803d5081e50016995000d0030351081c00041c00b51111085160680751103203d42c50b14041d030701d0000c4029103000310681c03503c07118002070a031414581131044100303034407090b01c821540c0050320f04e100b428000184000780c001c4d00301c07410400ca0990994086a2814050502c0740b0030192154280d082c40c411406040b01c5000000030680c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 380068471 1250 380067221 380067227
    0x3180607020a30120e070e040605100e06040c05091801060207050307060503130f050a03020303060a1202060910020c3c03030708070204060b03010e0a1d0a0201031a0316060e01 77
    0x81c081110800350304480d25070101c084507401c45440b44103180b40d80e5481c40045d26641800400000c100303030803030f0315031a00301401d01c00c040750030141201d802215802020800301c00b550040c00d2780920101e07030000c0da0041840c400d0b6604d01c41c5080321640704810a0b450303001c01985601c41c034140c49050307084601c03540d11341060640c5c60601e0300840d0003045040c0001180c10745240000030b0745510030b40c1c4180d5243c1541d960b13a85006104041107025800c04010848030b030600e105104000c0c050b00080c42141c0e441ea4010981900c00c4800f900d002d0070a01c1c204500d41c1b8001c216001140101800d546c1c05c14241301c0e418115032000440c1981c0b902118a030600030480d01214400051500030091403800c659079907a11500d5114420803604a510380e64009520340c0083d001c0c500a11106404094926210742881c0c21282e10113601c800200900780320381240e0768001000c2204c0d51342030030001b8820014442c060348000740308000d241d05210307403040002c0e441c4400704110700f1070350701ea152003401484080040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 380069721 1250 380068471 380068523
    0x13140105180307030503120f07031401140d020a0611060604060e0711010e06011401110d140c0f01020a0309050d0206070c060c11070b0a0f030b1503180607020a 70
    0x106000540611042600c0c00001d94030400011008048a00f4141c1d42c0d500c143c00c6401030b82030144104140320402584d1408400314079884002494100400030704034164254070b4906008118942c8040c114001da181c0700c0c1c0700c00d814003540060040c02039640e64040100005440108448103005d8100841e0380360505003d02400d8859444030001c0507901c643c401c40f0700d4a4003000d072011664a90050301180a0240201c0380681101d44100e0008644500050074004614aa00405521251808026560007102010380340f54102c012551180e0306040180703400080048002ea95100180d12420b6580650103080c11030700c26406d41b1a21000682c050340c45506c202ea507900811221041c000001305241c0c0149401503290401c0b01c0302e01c520701c0100f8079114094104040d0354400003054242c0c10f4200c0341c0c0dc600103070785107070500c403110700c03240454550250300849800c14107010001c200600700100303a1922140c1c805044400525004900944d01d0105072010750710b1400b00012580300c10115120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 380070971 1250 380069721 380069759
    0x60304050a020418080a0f0e0111070b0a02010609150906080304062f1c080a110d09020604031506091103090c0d021f08041a100306050a0216050313 65
    0x103410321a52980a00002d408984c10307003640b034552640d076040080c201d0b501a020040d07459a8542c400c54080401400e50b50390f0144443c140700d02c01c42c01d146086030008005050b20310004140c2e4607440b2070314013603025000540088100074200441c00344807922404076041103070415502801199621102c80e078407803144d8016000010540b142c1000d01103800440401c20181820854004441c1e50754142d0904141c1122203040482c0108041203161340405000d401070709401e010000d00c1c0c020684074680b88035420210320101d8582c0f5542c1e05556039502601c3c02181c04c00116100030081290300c0e80203203214080c00703505600e05840c84601502c410b06a03441900761200a20b03c6009440030080a00b030364030000c0341d010501d51111b01501c03280c2d411480103400e503500c6c0c003031301400c1c949080341e0071404603000704014801c840300704101e10880000000880350402000281d81c1c54041020340a44a07080406446000c104943d008206002005198200000c41c1d100407090701d40012107208117041c2c0c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 380072221 1250 380070971 380070973
    0x62c010b040605040615051e030106050a1101020a1b0f0b19060602030403171c0e0a03170402030c090411100f08060906150d0f15061106130602181e0a0506030405 71
    0xa0f040c403903034005c500404441d44444202a03010034400234411640c1c0c802d801250014001080800c81d1130b03044007101c43c00440c05c0c402581051490b50340101109046441401651700501041c004d0102c05800c040c00b003600b01c5802c80d250b203000e00c0100c41004081c0701d102c90007890564005001031002c01640c0c140c0c2e600c03048004080c1d542903d4880b083d0014001c0c2d105551031549410031590603445840b60840c0c420014001d04202820003810842d4506175401780c0b01590b00c00c220041c0da000c80da040d00c2034412100900991980d0030509000191000c80d190000c00003241c111003140c0241e1085681c0e103e07903480c400a6a104414441d41d4181a5180d0741c000c40d402d0004000c0c1c01080b0090500000341a60001e24039500e454500e050710300c030000d000b82c2e5000200052184550204c80c0d0255213050100604040c20110510055410b1102e4003904a42c2d01013050500d08804003040700342c0102c000e21070b1851054410b128184000113002262150007248800a032a04040d41079a10860b0010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 380073471 1250 380072221 380072249
    0x717070311190f030b04020906030c03070c0b07080103120f020a02060f0c12040807330c081309050a0b030312040f02090103110108070318062c010b0406050406 70
    0x1110540c080c28803503403a280d140809000090424804541d000316403640e03580c03100e802c010561400b60840351103200042c00781c3e00400c0f030218181c81700d10450750412400c0001c250340c2d9480351030407520802030b0000100030385103070b03024805042d51000005040c2c83c0154422407942e80801815607140c02452501c8000d80c000c40b400c0300c09864080c0103010a00c0c44040e546151411080c12142415140c0e007520300005400328040c0451241009084c0c040e240810680385d0420200101c0d807142030b1000300041c03924800e000708101c41441754440e45001030f0703ca4401d0380c40c0d805004010540701058010303040b046203401c2c00904956604c1c0034140c200d94010f0061031401a900e44a805036a1008006440706082d260110340181c507024203807402503020f04601d03021354050300001009400c02500340001c1600b04900075040892882e0a5170f050390307014000299000056540c4c0e100c0c2410840084021341e1380005c0140001010f420458860750119410000241c5503070412003200d61500030130582c41c081c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 380074721 1250 380073471 380073481
    0x15020a170c13090522030c2d0807050606010207060f031515020304170703031d0f120a050606060a080f0c07050102040b0705061003050627100501030201080717 70
    0x900903841d00480300902051801107542e694218100351503100102080e692020080741100c0040130003501820340f8101c1c580001d0585006201c103500d603801500c40030202007482240501081c6040c00f040c10302d071022220740a50b0820a01c244c00524040c1c035280101e070000f401035840420181c0a4560b103450300c5030502d8000e20700b02e0003440d0015031140d003400b400d01e010428000405140082e0040ca900441e41c0342d080460400500702c0c0340500c2c0006921010701400080d4004c5c100c4401d05403501031002c1d044450000042c44070003c0742c20700d034002101c08000c5000d84000706001e41001e010350200c1f00541c444030180480740c80f80d4048c8600061a2070045061300301c552503800d401401500d100390424078551103107400c9902a901c031075020300c1300150000400c181400170561040441c041c4c8201c0c0c91840c1c42c0c003030721400e000f05a0000140d45609034043c0711108032141200742400c40884800c04613071507205000300020301003640400d2056001032171880c40790b00c05040100c865480c51219880d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 380075971 1250 380074721 380074757
    0x30902091f0b07020111061f090b06040b0a0c120e100822020d0503040e0f18071401031d06100e0c07110a050910060f2303040201030204030803010f0315020a 69
    0x310001300d04005101e800301c2e085000c104107850042c060400b00b41e00601c40601801e0010721a64031070074605003061039101881d513568050320125251032503647c0e992105040110741c03100038100300a200a2410704160365060340f01c0d6402030310060940701800140d540e030405580307109049815440303100c036103828007445003200b541c11790225202510b450b00210042d030316542142c100d5007182c4400c1094408024000210214440d048420b0804214103800c421254580701d04d03a80c040c900c040d08003415014801e034405e0380150040160203603000c42c5070f110401c040da100d0a040d6003000f40350020003408145008400b504601914280200b80d15100b01c581e00c2100190309010360740c0d482500b03200e00017510b864019119100768000d103030350300200c3d04081c006044404002d84000070044800c500716540000300b07203d81c03035243da00c89807903889544a10040340070348919000101166000b000010b000c800540204060303c0c4212401c9034411a0608210201c0c01070003681c3c2c00250702a071100700c036519 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 380077221 1250 380075971 380075977
    0xc1804080c0c100c0302160602032b06030807060605010203040e1603110307031d0601120618020a0f030605013002180702150f0106051209010603020d03030902091f0b 73
    0x1035481d0655803100d54102c0040d4035031200b00b0f0a0b4000c1846480141c04059051126000342898200e43c1c00e021800c05d2802960313809075452400d207880c0117811301808022070410b00200150801c00602c4103038cc492600030080e812088040382c00a081ca0004640c560011060f02e00351212581c0a01003a5548846229281c0a03542c92200703040d90f0f40c030706802103000c071401148540e4543c0c40c0414041a50540444154400f00c00900b060700031100500210b1700350a100d28110b41c11160100e1540040d00031800b012442c024000d6001d06490070000d500d401e061900c0341240d00410080285a0b600e1400381c64018105c204c0c0d0340035107620390070340a81d0300080b00c540070101d002030102807a030304107006d0042c0004001d84a070800340e07204082035010b0b0103d000b0103544c0078280030b80d018519494040007900c1409260a2415031030b15020000d10390b21000d60081c0000d5400900d110303030300d041c681000350040043c078805074040c0001ca80001c0300350702c0c101a03941e0382c2100c910028030380901d8000035801e01c2d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 380078471 1250 380077221 380077237
    0x2090906100908010501091e0b100507021903060501081b010f0c03180b09040b011407060b060d0218040e03130506030a020f0c0f010510060e01050a2f0c180408 70
    0x2c40901c011500d090244240c6018284000c80020b80000110101240c1d44001782c401c0c0340c0d1030500103404205d40354021220030014040c2040b5840d4841480044c59000485c202d601d04515521800424010705c0e0300842d040318804005d075a40078940d42d0701d0246200710041d42c24040b5085140c10340c00300e032066040305103403406481c04007082407848080028948c280d41c00b4441d2101d000c215545245072900ca10303101c215090902c0c0c050311503184014400d0703008034003015014558075000c0c16003540300c645c1103620b02c5060603021555031400d08a6007440c44404038489000d1494102c0031018401c0000c2140e038840e500b17800b281c4000340380604015466000802121401e5021310017000300e04140030117429a08104000b4041c40d00e00142841d0840e48018149418812400b008200b1a0b4002d00c01c122408000c1c03904941d00c821100045e5807040d4020004400085000c01500004503410340c54881d00c4c154105a0384515403a0081044078554200a1402c86200381d01107000110100c000740244 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 380079721 1250 380078471 380078477
    0x9061839220e0a090203010c050a0903020405060105190504080706141909080a050a050d0509061b0c0d05010912030507050f0d0e1203040b010801060f03020405180f07050111010209090610 82
    0x86445900c1191181e0b0305440c100980c684034220502145028007d1120b00b80b00e45c545030b820300654506c020024401d5210103405030b5500c4000c0b0709182d00c9001250413200311001080030032202c12400070b0481d031240c81041101d02803018041b44840c46016650854440300359401d05104c41d280407c88080c0001400074188041d42c84001101c0c1000d03c0314075446130144000e043c020415040a81c18440035040709410450100044a02c9640b0030003950b82c507507007802140c09440c0c07100ca0f1f25483c0c030142e41011035000c0398840518007004415000340514500c07ca41c403035090a0404010750990340306031546070115005100c5201901001ca018004c01d10307031918042409540901c92605101500d048105894000010082840444031005006201c0e03200204030542ca050684441c0b080a800000c0c03150303450307074041014420701c4900d41d844520048240c3d05000d1f20b020005544e40514411980401c20022003000001018820b852100d4000381030946140d80b503c0801c800701070081085000c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 380080971 1250 380079721 380079787
    0xa020907110109120914120d0c0f060f0204061e200c100201021207020a081804090b070905011d0f0906211f0c0c0209061839 55
    0x401c1410030382010f0306130b094440416680c20a0155401c0e041d262900b035018609041c0c081d08000c50001d881201800a4070b8002c4060420349000385500e403401b08054a01414901365260310340e680d5004008440007504d400182e10702e00154980390412089010300802c604482800c01050000710003400710141e8015902400d407203500007002d40846402c1000145e5004c02c9030000f040403914081e42211050005007440301043e03840600718400e5000d03480c81140d020003010031641b9540c003c200e0f802e81c4080121500e182c89000149110141d104560000d5440c41800c4c04102e105507000c1e0050b00050b1441c030414100c1c10038409241000b4000d2500544010201240340f4111074180c07200c941480c000d00401c56910803007000a6600070300109002e0f02d460104091385401c107031014441c65054620301c5440c1d036020f00240c1442c00c4082500c01c00300c0030700d0030003840582174020400d64581a107590b04010444100e205406660118140041a410042c5100682d4003042c40e07402c00f0419800100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 380082221 1250 380080971 380080973
    0x71211091306031a04080f0f04091811010e03071401050c060403260903120402030304080712140d090605030903040906170105090d091a0f03010b070507080a020907110109 75
    0x15a04404075840541c0507075801040c0f04100081c01c414a0080c3c44054181d5036050546a4800c20f1044501c1d00b0b0002c0d00004852003c5821541524010140b203c0100b201c014415422504c502d80d2400c01c80c0c035844449403200f4a07600860b2a44078000000d0700418066081804070003049044e0035040d070501c081031051007108041045541d1082d0700c00c0e0390761901c01c80a646d00310850402ea0f4810301c00e6014440810001000c0000ac2d240000700706070507000161141c1c00400d040d071041303420408050289510101d0190141111100110722039548040024804007480d40c076426102c50510015424030000c002080c0302d07201031600403036401c00341e071b180c141d8074403502c0210344c00780e40805030400700b089805a10030030078420140d1142c03075100a00404030300d05000408128042c0104e1009031030580600c10f4900540c0e0940f501031803440071403552545c582c68580b1450700121001c486500c2400341c00f0071494408a0154601031380501a260180c8171035006499806500400100540da0768190300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 380083471 1250 380082221 380082229
    0x1050f130305030a0f0203030c09100c0203030301170c040204050a0b0304030e041409160501021e0708060106050c0d0f17130f080d1503112110020d0b01020607121109 73
    0x110301c54001161341c0c4400f100c014003d070304169840703000d40d0018001c0007800809502207500e444c1080322a489409400381054548030040b4801035054440403002103122060b408140342c1018010084070301c84201c00003000300340d00c114020140c01c00d0b45017504028181108000d960018440d00744842504546404a42250710304c80c401403d0101c103d05100d1490014040000e091404112840d049418840041d694050b400050902000200e4946920300002d102c6540580016029114035507901c1c400142640c000c078050f1800d90203005d40450105001e420007949a89007900c074002d6210b4109041070301080014030004540e0400350000e4006000508903400d0248610795554440d4121151101102d0101c4484000145650310610114a1403500c0320074807002100c01c1141c007030407064405119840c00003400454821144004005000e42c0c015026400511008000900c455001207a9601c02a5400008519145c111904030b000581041411b500e000c4605881c020149000c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 380084721 1250 380083471 380083507
    0x12301050d02160b060925030902120705010f2102070c03050d020105220305030a0e030403020904050c01030c1e0f0207080a06020304020316060f05090114120a0b0a060c0201050f 78
    0x83d4800340600d00c9410204002c220240b6008a010b03503003050325150040540d40c040e81040000f8402c04107160b51200c08601c00c1d04450a40c07940501056658101c07081d20710765410071801040e02041038041c0c0d5840e01489070110041003400742c124a54501d01d0510a4002076000910503a40b1a0440348003202182d01044110b00f101030580c00000c440c41c2c403401401e40c491034070b10280b8a0144022231500030a07407180540c0d8202822003000505000180c900300e00e10302c1a41e000940043d041c400f000180400405c004446000070b880a2140f0700c00360504443d000c0b9240c041c8a500083c40c46424101c500c0340c11440c0300141c09004440d282d64070b802581e07107054080401243c00b0354000007000114241031100400d03507203111090241d407605040e80500340b020481307600303810001c02040c91075030360b07103d1107080b800c0c156000d200e941c0c5e41c2c0180e200d40211680460700c10b0710721800e20003130203a00e04140c200d031000c4851b160b444040300c007025401140d00754061303461281440c4003805100b000c28491418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 380085971 1250 380084721 380084737
    0x5060108071404092406020d050702011404050d03080405370510020d09060630050a1e02010813020a090f020f220803130302040207060f0e0c040e0303012301050d02 72
    0x61007405820a480c04012441c1c00c00703400c41d0000712300d55096580001c2543c508990900b041d26804450094031900360080e68811a032040042d400402030503017003080d00340214050b03415030349403100c14100c048041e1003189050b181c100900c00c40170159030300310383e409050a100d01c00391800000e1160098060343c00c2407000f0341c1ea09640390802401c1050710303c1080010059103c1040310300480b1f410000c6003d020400c03000b05200d10000c04420000140725410942d030344500045042c0c854042481c10900491100324007241c03500c004a512202d00f080c030141050f6000b042580032a060a06102c0031b00711485a071500c1c69020300c5264040f80100c405010000d00c5810a14590107000e048810002290f90003605d180d00200a4891290038001d9580d040c2e076015200581d03591030b54580b96004100c05c111100405207042c1001406c41c0740451901058003081724140542901c5c05001c0313840707210a10500309030710a40022500b0101c06207070011001003050420504150203c4041000d07a40071010b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 380087221 1250 380085971 380086001
    0x51905010b03070608090c010e2d040f0203040b0106050c070e09061b0301080a12051c05090c04061d070e0a060512013215070516090506010807140409 66
    0xc10081da08003000300400609240c41c1a1607981014040f05807942c842003000e078108060210152202c2d02d1362025800d4109595030310220036030050300c4030000d4292811304a0b01c03442c01c0000e042d82003a224000d880c000c03a040228024240d1034140255491b501000700801107006642c0002036406445502511404404010300554a000403801542200d06403510ba000d00040c030060102080000d054046280e21480540900b07080c3c034410359160090021494100c2e00131001d01301e034148a41c0040d4021401141198840c0020808010071303280980540c0b4402010301880014414514841e150080210304101404c21100c20219500d0100340d00301c4408101c000981e00c0126050040990040008030a540001e200c141494120040c1c4502a030712140f40c0025100820344e074012251514046000c0102d07035031421881c00f0703030700c0700b007507031510050070504500000709075801d40035562040b40140c3d41e654241d41d03000e40941c1c1e0840000220420810284000301c0c1e40707070701486080440c00e040b00e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 380088471 1250 380087221 380087231
    0x30a0905191a0702130203162c010509040f0c02032805040e0403090819021207060e19030204020a030605090618070e030f0a060221060a050d05190501 66
    0x8014058020000242462000c08484040096040071140b003001640d4180d100780c1c0ea15920b00004924460701421a00418800420b2081600a200c2072080076102912820305604956103080121900340380309951385003d0030443c500301d621500080041600080002414040c0c54203490300b21190340d6903280241e4000229107101d0181e51004400314400410010aa02100c0340000c0140c0502d2040c03c5a80010601041c10103026018602c0540380e110100d42c20f840c9001203d10402c0302074030b41640070300c0d07862001030218600880c00500ba5080c0341c4a4a40e00d2044500b4480040d07409403038240c0300c0703c508034040f00590780c1f80000d207601c0140740c2d40441c0e01c41c200700800004440207040d0390b108004042800b036110f8514a01560300c49042c1c10301642404045021034100f1029090383c00482c003401a241040142942c090039180c3d108004c0c00d80d48440801d00304080c504203031480340e808010b101c0208001c0c0740403400480b80610400a440782d6404030340c1c0b5042c805c0d0326032004560b140d44403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 380089721 1250 380088471 380088479
    0x50a0302071b030c0e01050d03050d0b19152d1b030507020a060507020d020f0103200a090501021911210703020907051303060506010203160303020a0f03020a120c0908030a09 76
    0x54000c41002c0c002417070001c40396500d8100001c2c0c264403110f41c010180301c008a03c2090301701c903030b0b8803449603040040c040809081d110790818541d038169000e44500e031900703c04107001c1d05100d000e2002c80b0341e400c445500c43c0011483c1901c00750700f207940b0301241000802c0c0c240030101c465071010f043d43e0502ca41c5459480b610148101305812900b6007002e02046814072420000d80c0e10403020f500171079010f9564030300c2110a000101d0142014035010011003810404900c0803000d800c0050000d00110740d40c1c507041c1a02c0b4030049854101c04078010313100b20b49440d03207480412814401154010320043c0310380c00312040c0204d0883c218016035008603160b009103400b0020760074040103040d4401107070311344280b40185162198103090702501018189954800014456034000c0044810f035121903044884200e402d850001c02075449100c102d00015001007054044074000d000343c07218140c241d00c031a0b0500300610001b100505408107840200300d0b00c50b5001074000b20500003420a51266a1011030241c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 380090971 1250 380089721 380089733
    0xf0d0e01020c0f061204261809010305100f020405040e010f0c051303080313020d1b080303010e04111f0e15120117010e01051005030d0309030f050a0302071b03 70
    0x15401841c003440d10741c483c0b5030300780c1d850030101c4914008144151000e0b88440c2080c004040004c03038241c51091041d404415800c0055000d00b1202a4000c039030030501c2004000d21103507040a1100510303680c4105c002c01c3d5117041603003040203e103015103001410290394000090940d0500ca15404850355142102555000e0a014500613086170f410702601d00b80c0307002007600b504401c9101c007a1030b0f0080440411000303070306075403400c25554004000803812140d070708150b103039042c042a2200c0d211920500000350140084140d904840784410240f0325a130700e83d01c40035114010300700d500c0d500083d94150546981c01030a207018000d01959140000ea007008418040f40e2550700340c0c0c3c0d0f11034a2040c4a01601c0442c6102060706450701621840070100b00142d145000d0f028540f0720301625400d03c810461003240441d007400c1225800c0307080368500d0080d51001d030125000d8101c0500043c0071921084000b500840082c070445859281c0180b400d206500c2d640c90803070302241c3c815180070310400d0400911007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 380092221 1250 380090971 380090983
    0x5070903142d0312270f1b01021c09140913080a050715050402100c03080103021009030b0f011e1d0a0f020a0c050d030c0207050f030f0d0e0102 63
    0x49008010314000101c584a001801108114001c41d6202c842842c14892410f000352191018016200f100e18280040041ca401c8014183c0c0c41c83c24076404450b41c10b0400000c2d00c0f68904540102501035000d00c1c1a01d40240607204c100c0a06603c2441440d00800440804007007502c2e101d6511350a0f01800d280701d40c2034240c05142014860302c01c4400f4094040010130400c100d00f60b01c0003c26945604103082620a40103004001e44203c606482c450305000a581040c0d00c0b462003142e0801c0e540000c0c400c2a161024003800c091b000406c100010300040c1004c0340d20020809050418001c03456690781c500d101d40d4000c03191a2804850f00004000715102c40d10810184000c841d1010342039400c054401000300c55400d46000e142500328042100400a0303402050001c6040708103540d50650900301824110b01c00c88110f443d40b03e07c0150a170701d1031007441402080f0080740c4c06040030514040401007580d0390000d01035454014483e011000b00380410060f0b5074000c260b216880f0301150840064103000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 380093471 1250 380092221 380092253
    0xf070f020a050c2107090b040b100c0213020d230c03070206040b100909030c03021b030703140114040c0f0602013b0318040f020c060402012105070903 66
    0x3600c000104400588081410f070078140c1c05031044189a5801842e4020050b06002c018804d400f4038403021a42805039000303000c1c0c19800b520140250b18512061044441c1d505d80e400700041c20510313108005182141200100c240d801f0b030007600740809100b060084840d96001000da00031120b984040c1d000215910a5000e200b4000d12030035032a00ea840a9203660303000780018044002100029490200c4000325005403a01000801240400389400780c9a01c0c0c4e8218164090300ca4000c110002285001d20f41d106c84501501420303078145560b807089402e01c0349881c0141e1554039403821004800b8110702561146026031a0340380610f140c81c00e401040002504900110790602c40811004540308005440d40312026081005c940d2440100018508203250101894040006d008002d044888002088180220f070204110034542000030704a2044000f0b5413042d400c00360000b009980100030724012102a0f901c900808004900c1840c03c0300d0f41160000d01048032000c007071050140594081d4041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 380094721 1250 380093471 380093473
    0x503010204030f3f020c0306070207060e060403020402032d06060403031d09070305060a0f080613021504030501020a0f020309030a15090501021209510f070f02 70
    0x182075450342d40d4421846400549040151070146101d0989070480f04001c008088a030b2243c01c0d620135030320440f4620210404014810300d2280d4200340b40114600340504510b4006010103840c240c0c040d079030f418050b002194065024003001001d40c441c0d000452042040d01d0107011181c0503404800d1942070411200c058803d40c000402003075403100d0b001c69007601d8042c14241c20494003400c46400084502603019003240b031141c00e20100b0740d010340069014400c1111090300c1d598846002040a844601c074560b031130f91004010039100864031215005980c0040d1404009824440700c070301c05c07070f8090340c0200c07400d030740c00104200310300d40c011050514440c003407000e14a46100d40000aa0326a072022002d030a2403512003158580c040325911400506030b21400964541404c8810414030120464078031640780a1000101c0c0c003514201121070b80701540783d5480084024125140488568031101ea00d111030240d008940c104514900040c030611040851b4040b42c40d04110082050910100170815 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 380095971 1250 380094721 380094727
    0x3070b0703050738010801180807110402091c03020607090510030e0319091e06051804020403140a031101020406090e151c061b08010302062101140a05030102 69
    0x1941c010216490035801031400408441d1014031806050600d00945460004c4603500001101c202c9100707074100d501d82c030020001c0c00d860314500900000b100f24024a0005c0030041d050004040401b000640c400103400107003807145050126001c1c0c0d00d2841c800325814003489182d0101941040360a500030110314190b29100d00c2d210104020002d4442100241902c0d20070030300f400c0030104140c03020403026180000007981d01c480041e0042d4001d000d180810300b489035450640242215000044880a0390381ca0710700700107414002101240400f80d5a8015020040040400c10740140c106100030010003801d030000c00380c45c2c0503041c0350300030f1003010b6581d0040c0303c01c000d60764110710110200c032044640340c00c80b603541c0c001103072034482c004030501d0b400400800007586251003907403c503040707070b110701401c225a140205000c2c00081e034411650000130b01c0b1000510050814201810203a8118001715012030580c860400d03080c44240c00102c041e2162524402840c44e005940000a1005030001c41c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 380097221 1250 380095971 380095973
    0x150a0c140409020304050a020630040b0708092a090702010e060a09021219030807030e0604020d14060f150a0503060a020306060f0c160503011b360503070b07 69
    0x491030080b0321800c40015404000202032001c00d0100c0184981e0040c40c1540d540c04203003010b500900d8803552a2800305040300c00c0c000c01c800145019002e241c1040f1440c555075209003003100d00000040c454030b1b0380e004d4014a4410b916001c1c0d11031000e40c002240c0403c101040c20240142c2103001003540045a040c52001c0d00e8200001c01c1072600400200b1021402c90081d002051b0800b0034500b003004144500011840082e01d65030380518002d119a440a0b0303240c60f4100c080b0242d4400c20409042a003022011030018a05080c01c590f54a00c00c2c00301503803036240040d101c0d0510508a0307804131040c4500b800c0103418088000c4200c9060b0040f15940002e43c1070001207a61a00014620290380d5400800310b5180d036109010b031104900c1004520b9501c1500e20141a200c0200100c6c3d8461403039600004111454107004a9a6202d00000030310f54240341810f00301e41001e21250140740039030260304000d014080785038086080c0d40d40c540546c42c031035142c03c080c540b4010243d80120b050030790521403c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 380098471 1250 380097221 380097257
    0x50f03091c030c261b070617150d0f1109130503160305040b0301030f110402030603060402090601030608070303020f06010803030c0711150403061b0e0105090918150a0c 74
    0x10045a401903120340043e0101d03004101d84e003d10100e00303031450782d0100700d07942c508240c00c000a0f20000000e003581e40055541e9400e45201d440b965200c0401c1c080480019480384403035010180c1590000c0c081c07202449161126903421440c9803047c0c40c804141c400001440c2480b65049802c42000b08148140003000d80360b154507802404900e910105820f0504024076100704140e402800380c000d0306070354a503076a20742401240715551088800115070030390003040d86403503c243d130320418020300980010b5540342d08010300508010070340c6040c180e0b6183c0c0400da4032810020030009c1c42c42038008149038140610801d280080503480030001d40c1c0100104907025404105840d0650703400080c010302042c05200003010231307900d800d0070410010b011900205101c1c0c190000900440458124841c20069400460b229401440d90602044041008071928207111040ca98820200c0c00b40d050040b000e421001e051410405070803101e00190020320800400d10700c21529130280034200785036910f0944c13440c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 380099721 1250 380098471 380098487
    0x10e0603030a0806150406111915180803101a030402030d051e031303031a10050c19052b12020f0d060b0a11030304080706050403020307050f03091c03 66
    0x80070801000e880840c0c1380e9241d41d02d0702110340b20801141a100c603201c020080c0400900d541c00f400d580b06462542402c07441078850701c801240c001a0f103130001c66404581001034450090350207065410300300c1c000d01040d000000303140280700300503409200901d003621008116a0720399503840c10b22410010f001c016500010743c8010700c031581c00c020352120081026000300d940400103160385100008108040411400d0010142610031f480030010b08844180c0410f44000003801c568002d0a07400e82001028000d0000c0d11503d040a012110b1205400c0720b600e21904404c07c04a80b241d0044c6501d01c281c80388070690040284000d001c07a141582180e100416030011548051001940090360700e00d80b40301c08080b201e9506030020240480caa0f2000c0c0100c00340d211010b05800145414041c070000100801148d004642244a050900070703152100e4009002c050400c0b81544020040207001500a010900c3d88040348005503885543c940140302c5448440802c03043c0507800e4900440c0000d4008a02c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 380100971 1250 380099721 380099737
    0x506030606030f13060f0b01090b180405090102130e010e010503190b070c021905040c0302090607080901030902030d0305190b010804030e042d15030c0b0702030a06180506010e060303 80
    0x44040d84628202130103048100602600c0d15003400c22140741d03448250032075104210280e81d681c001a47e5808103203d2401018001d851150f0048081185850303c1e401040e0401a01400149003c5078500c03440107900c41d603880b0316150601103004003c00d400300039206006060942c050b241102032007100242a1544400c010001205170700071908480c410441103000d581d020344a0010711a46515a191105891003070b54815802c103000d42032114803034001e5995a550103020703e17051224a036039030403d40c0c00c44076000e4101542c641b10304015039010815820b0070045a20b0004550402c003003d1825040721300e0880742c2c0c01d41005101c03546a680300c01360507441605458500070030503c0c4000074001c1d204401c1900c030168000224401004407042d01c2039206e00c008042080110000c0f02c8114091006200180ca112040c110420028400100801103d4030080584084130425581d0200700c4908101400b000c3e50310342500310801c5400c204590140150a20291046c83e04100080c0e8074403803088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 380102221 1250 380100971 380100991
    0xb180406021c09060b12010b010f050c10020301060f030c23030613020d020a0801081c0f110a060605090601030b0616080d1d0d090302010512060d14030c07050603060603 74
    0x1030180c160418402c0902d0050008080c140102c044904107070016056090341745100c2c1010b120741030346002d01482114160f41040c0c64455444150b4081540c0c1a0031900d81d61440340207080d0030301800001480114040c0095494544039400050802804c40742c0078504801030090b040348203a020041455812078050380540e13251741e0f0303039503274404110b03031400c3c5036105101180085031342c0c4041c1400350050600c2610555402d000d42e80e1b40c0400a640d0802c50007603080d070105411044103581d125040d484e20122060030500345148260b0407142c54907102c0c903070580d0890b40d181002d00c6940b4205030500d070450b1003480d051050100d218001041c0f84521101070800106802d4039808000001e015510441c4005104016524886882c0e00032152403100c03210050144203510840c40d07006210810950b50180c0d0380d01d08280c028241144441c60240c901c0340e1028020b1140c40c00900360100c80b090a14082000c0c54881c0301c0c00c0f041614140da00d41000d403180b1418020064240c0310241501d9001c807040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 380103471 1250 380102221 380102227
    0x10903020d090e01121b030302071a04150c0c0e01150915020c040f0b040f020403170309100c17070c0b0601050c0c090604020906040902090a1d0a09020f040f0506040b18040602 77
    0x1186c40742c0702c2c0404a003152404841810000b0906030042040d1003140c00078112416101219001da8210780f046014079207480c10100c04902042e4828031800140358070505c00c69454541b11109010000400d0b804881c4500c03c0b00b19502d00150f100e04004000c01000740014002c0900c01406900c40011007200c5000d01c0c2c0d02d0780c58400e40030342908040480400500304100041002c454040690301a02090b44d10f0b0301980f640c150302d0400c0400726441400304001901d0090070880700c51002c0c0000031540800c10880c003109030030744d10896804500603d180d0b140d4500201d280d1a0810481c2c10041c10300b8103000c010f01c01502d1412001c650210003070411212b0301da5a90ba0000060000d00481c20400d8000d0004038002c64900070590080001c21b07003c40d81c44d00c446584860441801d840316080415170303581c001c0424500913441d0011800360b4401840c10300240e0110000c50704a4901a6043c0103240d102c5003405040d0901d1310900003a608190780c3e00e4416019101040c50a090203040209425400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 380104721 1250 380103471 380103473
    0xf250b0f1b0d020910050304052109100302072a06050c01060801020301080d110c180604110d0906051621060510030f0c1d010f0309020909010903020d090e0112 70
    0x12848149580644192541d02c8001d421070b028000d4006812440c000c9201180120791103000d24103482c811648130000341481152081e18070501e030808420240240c4040c400d00c0348954030401c03041c044841c640d800680303804a03410000902d85041060001c0030480d100342800780e0000500520540c0c1d0181080b99032583c0d0071008034014455503200f41c203a0751000c00040f0b418500401e903010f15007a0360350303641840100003c02c16215002030240c9540b00d560b05070101601d00030348200301d500800c0100001940202c041000446a02c030680341c02c00244d031194220108505031042ca03802c10095184100d500000740c07005400084808401c200d064681420710519460a4200318090240030b0184122190728182c098003030411a2114a8a10709081d00c94031503a111380455010701e0003030a0300550010351180191500811507402c102010340f10f0421001503224032501d203008004040000601c1d452604000b8208030020301620f041211080d0700b080700c10b4240d11442d05440714113030a58003014803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 380105971 1250 380104721 380104741
    0x40b0a06030902060904180210050c07050d0f020a170d02060c181c0609171c0b041404080315011701030303150504050f0108070b1318110f250b0f 64
    0xc80074060361160030060291040e00f10054603040042c03094270824407026a514054800c4c0c011443c0d000300c50740c080c010410281c41c02c1a511005a8050484890056919004240d030103209810400762151180401e20000908102c1259940d8041c4090715903820040502d0074a442150214441a11000003860b060b5450048000c0741c210340c020109940c05c40b07850440007404130b402d02500d0b25401e0044440d814003c3d13104566a1004804402004225416400000781220034440f90056904d0011451780c1d594051078500540c011110b064980c5081c3c841e03500425603006090b410040380031941c10014845c11141411343c1e516040200e400c002022a00e060003103103511480d84541000c00380021000602505410707962914203a6030320700c1c1c40e5050800f41e8400e02c4000f029861000b030741000030034180303003122502d0380c28048041542100200700500d250014401500380180001c0c003020286414007107889030300f5044030398860a05d003945070b500600100500c070200301080741000403d0151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 380107221 1250 380105971 380105977
    0x90102090d061b0905090403030e0c15040806010501090b0418021207080601030c080c120c091017060d170702030f011d07050927120406030f0506040b0a0603090206 72
    0x403000d400ca14040da01c0d0708080024000e01a1075040e040d82a20100814a00c42d109000c10b0b10340203428051203481d00d50b8210000c0c0000b07040c0500d98050522511050b0707850341d5098404241420a07503031a02d00346806c480c203028040c1d104605000108038108804d0b40e2107001c1e60102c900e4542c2c040381121600d035040b000b0b84203020310015800d060908108500340c1001050b40118400c0c0c0c0d0400030340c001044141d0740f00300c06031010500100c003404010988500c0e039941590047c40c4416450822610001180340747c01c643c0340100124401c01d5600e40030000c1100401d51048040702e0703000b400003075902c0300500c044020040e00b05c07002d03000803000f0554034100403168540380340314000c101048424580504488202003440c01c0b0703014907400058a4a031403c001402615174800c2c81e00031001c51110340c0e0b8200c00b410640d0139180200040c000300c000005000c0c20041029413400b017051008083e0803c02c0350b000406c0c041c450381c500050407241e41c8403940380105075041800c001490740c01c1d500010306180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 380108471 1250 380107221 380107237
    0x1725180513050108370501060302060307020d022a10051308060105040b03120a110a08041e05060c0c09070507020d050106031b0e060d0602040e1611070503030909090102 74
    0x38442100d40c80180c40c542c0c0580c2c103d490320030a40341801000400100100404461020a103d81e900b0b00c0100441c00340641d1720782c3c0d1261000152240d66640400c21a4000300c81e113801581100d2140c01c01e494051082c41722207406080502e44a10708002031003030002c40a58030302d01941e51220300002c03250080040b0361410800b82098011a0303500e00280e643d41c2024041c0b40c1c01241026140c60721390800040190903034882d00d001034240000074030100d401c2e8807003802414035403254843c01d001140320940204050500826006590f00f0b0850300d80c03071540307010750042d070003000c02308032000d45103030f003c543c007442e0039401c940c1401030b80c544030005c460380e0140d01800781d40b007011030441d007080000c15408401100d200c0c124401d00e007000100c1c121003079080c81c0720381008140b0b020000340701ca10305814514040b034070401005080070b4851401503484442240c1440e8100d028002c802c20994220241d001a06140300c010107480b410440480d44902910740c4650080c01404081342405030b081d01070303c9010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 380109721 1250 380108471 380108479
    0xb09190507200c19140402030403020c13060e060607030519051b0a050c0d080304060b030109060504032d0e0105030604020d1803081003080a08040312060617251805 72
    0x19645115201d0b04490f01c4140304403c120000c5003141c85450110381114069006008160401420300010354070003001141180151001504036580d04c1e1245c1041c14501c1d4000107555003004400000804041c141912402c0140101d00002e60300104442c029020b9154880c03c08641c0d8809541d80d008804290310301d900100c0076030034000800550454224060022035600500f1107060105482c400d417006030003c03004100160216034a038104901c520f5000d400000c0b00ca50a48604040f00e0056034210000380081082c040320310440351076240c8040070087d00000c1010042c1c4042d000e10001309100e03040c002e000c40085c500b60394984c141d4802910000e01840082c0d401400300c002e480883e04201c01045401c404519112010484101501e60102e00340b032a1850744132041c4e6010f94000d1003241004480149840650800d00544004003031a45940344210541c011400382c528004160750515001152441c80d40c1526590050340c0c107040e03040c10480b9a40340c00b0007002d00c2c00240c02813500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 380110971 1250 380109721 380109767
    0x20c0703080c03070b130f0f03091d040b070201151401050f0a0e090c04060c030e27010501030f020909130309091b0e0409020a06110f0717010b09190507 67
    0x444000f0000300002c07441000c0d110010f030f4445040004012002d080079001c050041203100010780180d80640722103000382030000c0515502c2c100d48031100b61070520100c00c00405800d000401c80031a007607a4001040c0d000034848015850020380c4801168890008103255408900305075134055070854500194405a20380c2c1d40403010805841c000c80c0b900c50600682000c070018080e420440300381da0503a1050355944050304416101120440f6090305020f0b8820340007844100118448548204001c0f00684400f05942c0b5090000d000c5601300701101010744d004003c0341d4920340c0c480204542c000501600c0c02103418150070101d0300f000140c0c029403905450052400b241e41000515005500001e54550100c01824018803042d00d2003800c00070f4116480c031030300707104060040c0b130300b080da10541d6422918501c00d400140d510301074a03079000d160300e010500c4214903040130030301035031800d040140c54543c850f0403d07840e040c8034a0103800110307000c99502d60104103c0c0e0300c50043d14040c52211401c0b418 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 380112221 1250 380110971 380110987
    0x30c010b18091b0402160501050a0c0302040311281d0109021c0b0f0604090f1b020d0807120c02060f01060915110f07030b01150e0d06020c070308 64
    0x402845092211880354500001895181081e01d4500d4070400340480038188580d29004000160003152401c0d903030182d028000391610b015041210400e85c0e01039000031a480c1840c0c9086011211049003a000b014010401030010940481c008204210192140c10704c60f060080301c0380c4d00202c40c80c0d1400e203180307400000140b60082c00e04031521040c10302e24200603e03662490300c04102c0c441d0086d00000c01c00100c24045407400d0a910440c5001c0010740311001c030748044800a07915611541001e21107c0d5195909010001c07640b0504c910000d00b441806905e42c00804045c1d90bd071030071209a0104440c41000440c818030402e00121650300d00c03803003448140340c1501c01945480c42100d205607002c0ea480000aa032a21500a000498052002c86d50344001da40c1d404540544803007034164480e01c01d904c4102c4c41c0c031a040207800011801500701e12030950402c1403510440340d010a10390100000f51010b00c2c407542c0c812448001c550740c425001a61551114851401d00366960b10190641d00302041000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 380113471 1250 380112221 380112223
    0xa050414040c05030d080601031a0301050a0f1505180421050c1c08010b0f1b030a02150618041e0b06040c02073807110f010e09040803070306030203030c 67
    0x250103248502c1103440b48544580626543c1e684103424100040c6503000480c869500961204140c0c0e022115040d2007001c0c850046800d56006481501c40240c0d1051b101101e10034a209420034441c2851450200c0c51509000480e1036600000c0c4400d0b10301c440011804002e6212044064030403082e10b0518440252880903043e0741141c1d1400f2900d01486464001c03046816544251005c4544c8407401c00e03900317202d0070003500c0e08000f0015a00c4081000900c4001c05100b004200081440c00110b564540e2024028140b00e100701d011282c0891000600c08181d4564542c201c6481704000c003050039640703038288130b680142074080081044040c15030b43d8090010b5422010b04c04c0340269028400100000e41c00c0307a4513552845450f4040307800300c00403115181558162020071a0400c0140328040002c105102c155120320300460340c44840d12a108114185a00030320707071701e072400d007442a0401c2c0808041507401c0030080000f40340070400800910711a0082e4802005503401400310b035220300d2140105 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 380114721 1250 380113471 380113511
    0xa110109030f05031e090d1410060915050307140103051005101d0d0b0a0c09230102070b0306010c121809050103020405060607021c0c030206030c07170a02070b0304020a0504 76
    0x54a00c040703a000d0303039a41700c0d602e00101d402414001c0c00c090b070100d00390b45841041c8268410b000701103005800040e40504807901480340036091700d0304000faa10181410110000e010355222074000d0b00049810080712004c2444201c1e02c490a0070701081d244d0319103111224428082c0c021a501c0f071074801c5101c0e0703495800140c00c00c4035a51201004812400c542c00c000b807040307a41a004024031001030002d00e44900035000390240000c02d04182d241c098607018080340306080c0000042c3d0480e0aa00c1c0c4040325a4100499802400c015003c0c03855800e042000800c41c2c00ca840b03002c1e202c50852018050a1071041d151704901441c69851004842d80701ca8608014000070320003179100b40e05120104000b85040412140101d5005100741030500c40f08265061050404100351103400403144000056119240158030600e14000c4288e0b54007614034046c40d9103000c094a4906600d02401030000064002840c401542c200e100d0b002c0e100d60f03d92000070026802904440d03041400c10f08058400c03c40c01700351f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 380115971 1250 380114721 380114737
    0x19020c12010e071202040906020f0d0b0d42061a0408030714010906050f040501050f0402030c060d0b100509010210050705030604021b0f070501200a110109030f0503 72
    0x4400100c0011030006820381d81c54890400c801d0300005001c0154940211104004520282c030100d500781c09a1500800ca8200b07210038442d40030002110200005503100b60351022234119840d072801c2959490701c003408000700103800760024808503188203085424010f100719108010b0140301c2005200700050280c000c0c0d110349a411003900108154500e000001e5500303131600a002181003911684076440c62000340c0c0a64041ea568403810360000c02c08030700075288911940440e102203802c1030300d0200d01b101c40040284500c40003180a01005030f60104402603e817800f1168941c44402500380200104454910b480e80024480390110046030040050405032030300360240ea0803174408940388800d59404032001400a0020800102540b900758040c21808134810f11000c019114844024a01440c0d4100c40d025a804003070100401d41c0c0c0030010000c2c0c140d00000c0043c041185144880ea20800100d001300b10421030004100700303034821600000210b802c42c601000c41122420320a0300e0fa804070103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 380117221 1250 380115971 380115979
    0x112090210031d0a1101051b010606020114090307030f05030c13031202061608060112020c1902090903072315190c030b030c0d020f0618090a0b0102060406050c19020c 73
    0x3000b5034540740c000c250b115446400c1302030a042540305e02d0045501d80c1c00100660140c6100700d943d002c8480091040e0409001c1d19000055601c8000d56401c40028008001644a41c410018080020780c809410941c0d80c059081503a260b032a40c6c032035995203000d0744080100b1809803000000a115060514010f12a4541c0941e00c841c1c0b90074000c55003080c0a0f110a80c081140e8401143c02c0d944504651090070740654001800e080084280508210701150510013600603c03100809501d4940e2007550400e40b4079004602c1c2200e50780c0c84807890107002e180003200041240e00c100f6803500601c044074500b00720840396901780c98040c00941080741c5800a40ca822841c04011900d4180039208000d03400e040100141041140441080030b24096000200d0b000350001c1c080d81100d071a400c002e0060740303c040329090310f80f0300b4a10a20245000091540c08030038144091f900c1c20340d801280315600190030120100d260368410b0303d1030400f8898100342c4420600800001034034a9804070740c4131040d1808a0f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 380118471 1250 380117221 380117261
    0xd020a050909130201140708120112021206100603150b03070206090f060105310203070c02030105092b090515040503010c090807090e010b12060103020a170c011209021003 75
    0x1000c40326510f0b41901c0b009001c5482c003804d5281c502a20400ba0143c5440b642d1058689030070300348907003a130340d60aa01116604180040700300031403500504010052546100400c01460503040001d4407461071300c140302c2031503514044608038845002d00301d005454421441a981e0401d00d800a581c0c680869040200f4014020380d00d1b20740c0404251907040714401414911040b030212007580120341c400c0d10000c903280280100c02841e00241c0082c500c205c0854541165501e80c80c0141801d49100400c0d8002035088401d502c3d0301c3d113186c05500b04000f520b8001d012006041144241d41140f0300340c0081ea44104171030449048008400e000f130083d10000e40081c060350494003401c1d80c1100c4140103a4180303030884101442500c5469101501020000001007849100340300420098148403040340c01d10f070080401481542400202b00009120314044061705180400503036031941008072a2904001c0d108450700f0314286681c01000030b26800501c9200c01201c0f101028000b042001c40001e9032110030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 380119721 1250 380118471 380118481
    0x3010f0b0403050c12010f0501081c020114010b0f07080301030807060b0108060102060c0a020a17031b030c090616060f09030905040b010e0d020d080a120b0a0605090907050d020a050909 81
    0x950a641c11658088020a09462000d007003100309811805e1540e21996152140d98082c400c6004890081c14940043c056215110706e07030030503410440e500341065a0400160702c4185444a0b500c41c111044506959110650710120046601c0b44040240c04400b0120000c801d0200a1000b4480343d4441d900030888407100e00c0044d20560400c50714103025800c0400050301040801c0000e044080785441901c10402080c2d903041c0c0d02c281c07503100d8401c1a100101c10860340c014210500400c0c80c1c02010181d0640ca0455030601007441001ca105016042c0412511900b102e1200c481207220b90001e07003401107050617000fa000405402f28144c2c001741c000b201c00600b0b800c0c9880344004d400c0041c0d5a00390418000c4040c08950080b5100481e00205024044030204206101610340148a903654061a01d86034205000b510012600240700d0081d180c02003181c180c000086441007031007607030b0100c6180d89188055810340503081c0c0905d043d0380002240c0c2402c55003d0010042c20f0700c2100c860b0991303198 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 380120971 1250 380119721 380119739
    0x6081816170d08060607060b06040b04060e1206191e09050c010306050108010f0b0304110627060f0301090b0d020613030c09050c0720130b01020f0a051f060302040207050303010f 78
    0x2644c9603034001004114420108115030820f084058001c0e0066150950f103004030901a40320b60302c2140084d43e042c00014552408802080000411600a014901b402080540c0d1042d0007500080016a40d50681c0e1840c0f500c1902c440c140d140403041000061b280f401c14a4a0346010f5035007c2c0080d1400002048a601420702c0c503050341c400503403132085a8244410718520f940007420540311140d00b0f000b021810307540e60004150109088510200014401c1c0e40f008580f041d5220310743c40b840c0c0c28007409140c1e0f882070007a01d0465814440104600b8a0000410903408110b240070f0b42154001403050342e2805507010680849104581d0f59500d6036075440304008440b01036644a03a00241080680085503581540b441070001d540608001c00000c2700000d08402032140c1000c8001d52524420b00d81c0b50303010700c5913146002000c00030b010101459a43c4903114260b00038102c0c03a03071941d00c0d20040004a25400705024550150046641d02e0050400f030b5603e4000744289601c40d4000c502c08246465 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 380122221 1250 380120971 380120987
    0x30803190509030a050f0403020a060509030f0304030302030d02180a0e010609060503090705010e060f030f040c060c030906030e0307080309150714030f0a0f050403030902010806010906081816170d 86
    0x2942102644c20100010b00450782c55101260b03051480c03c0900020003da507600c49503200400290f1035055a6100c0d50090508010f016990038150f50402d002c108042600441296486081c1000050b0b8810104480c0c6440000309800344e90040303002d1001054800c00a80b016058440c95150648115a1178038200c500344400c03620322a00c0c2d08242c0b07080020f54065501c01d00b413801c00800c0700d800c040c1701641109d09500100c440c40da110303000d034090000b030110040c81c003409080a8074147d8a20b07081c80e01c002c0c100c184244120000c0507074070b041481841c817041c0184d400455108a00c0b665a0900c4000036542d8503a84c12201e0008400e400072580d40c42c001d002c14030402d1201c50351503003595a42c1e202d001c454100106440d0300c1d2601c461100380c01c880a4444d89200364440d0720b00061510f800d0000400b01e00c00145100d050000c120030602000350040f40d441ea214107400002c0d020f00e880c400b0040e00b4110581951070200c10080000300c1e10300c0700c0b00d8401d2507000c1c2c1c07401120000f00e040781044803080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 380123471 1250 380122221 380122231
    0x80c0603102c06041a060c011107151b2708030706150609150807030b120a0b0f091509030706050103051507050711060a020a051f140609010b0318070308031905 70
    0x41010b5400340f109061400141074104c020000006551049c0c131000d034a1a0b000c50811140302d6008080b00c2c006003028880e119400d0b400d01e80f1051406c17895036001c0c211401c0107514007108034403c001c00c000000107168000181c1811400c0e281c55210602c1d005019190010104584602c00d42c0d0101c0c0c0c042c4500590012140380781802c200c0320010032001d488070000904004200342d21180002c1054031001200075411520100500380c00503141091500510060f01c12021100c5030000d00404480c00122810002074000c1036020300e0700d44000252852140350802400386041c031000109001c0007081050340382e184400306422503541d06c1e408075032500c07034003000401c41110503168100c5401c044005c0d040610040c0119114000692103045c54001a8451101c21400c0701d2031404002d1803600400045440b00541103520303003408000182d0540050003994240500032000410a4034103020002c2c1110601d425a00311680742c0c00d24240f144d1080324030411281501100984408052003003034824 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 380124721 1250 380123471 380123501
    0x30c0f030b34030b09040309090b030609100c0c0f060c080c070f11030f0708070f06020a150b060d090506040303051e161101020c010504020f0307080c0603102c0604 72
    0x2e404816440b40c80008000791010805546020711481c9407105841d4038001c9020740c42d1241401e18000305c2c5c005880200104a010350804424482d2403200043c448805006554021980318240d10b8101c4108046107000381510081d020a0014000650f20513940300031a987c9030b41c907990360350364484110710400d9002040c0800c0c40c0016808a40400a00c80c141540103003910051001c0c041d040b85822000d41000135a50018902007213007511400900c1e00400240c000b60480007029200c0c031600840310540c071501305440c3c1c0e400e143c4907603852040303c4141c01c400400700300b021880d0500f2503540c032044400702d0210303140201188142c0291520203a08901d84640004281c1d1280c046a03228a490044c50040c40991410721a9154003130000c0c1465100703443c0005030900c2c1900411a01c4d418450100b4001d420800d0700b07004000b00400e0b00402041c0503036600d42e0300c3e110440e40c80940500c41d402881c241400c0c83d85039000c800c0b8a04440c0c40442c200700f9140542d20b95000308402c0b00c40140700080d41c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 380125971 1250 380124721 380124781
    0x4061e090f0b10030c0912020a0b03070c240c0507150e030d061409060111071205150a140109050c22030f0503040806010816030201030b0a030c0f030b 66
    0x91410640c10480015501c40400305448140300046a215645600c001000c00d0301c0790115030b102d1b0362040c451002000c00b220b03820f21083c000d0f00440c0a01c0c0d0607014041d88008000000b0b042c2d14020302038a5005030b03005103072840c2d038003900409002d40080c14440c411100c3c10142d8818526102d0000e0314281034001c1001c042c4007181d00f1030300000b0484808507005034002403141d901449801c0c0304100003005800011400c400340306041041d40e4400420380307410b0110390310311221102000201070081d1050400c0141c00480c00341455490001c01c00380c0c10101140781000c22844c025203411030b07031503100344402c0b04400d640c0355a10101a17441c102e5a030151050140068203011288075150484046010507092056441e0b407100f40d04070003658030a4800e9800050b040000c14003c111700b03030040403814082e0004d0354861075080d54030291f030310020f41055103400f41154107a540c03011200080d03a1140c0015a00c60b0344500b0041c150302c082c0300c01d41d40c02c1140c1000490601c024803400c0f481020001101074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 380127221 1250 380125971 380125979
    0x30f02060114120c0a0b0405010e04020f0a08040f06110901020c0a0305030f0a0311040611060a09030e090a0e010e1c0c0c170f06070327030801030b07140f0904061e 72
    0x2e9808861000f202841100e0004200d511160071000140400d551040d0755503082000250205580800182c040c0b481000080340703981034181030f500d050301c0d5450300fa1215126030800510300d60040c107001c0c1038213142180410f0004c40800080200c0c030001c1c6c080c3d905120b030080400041e080540b1010b040d5420400c4401c0201c0100303070040400c3c0c0010b00f00041d951031202d80c2ca40640d0025001a804100500305441e94450100940c0d584159111004e101407850f65500030071030043c20030131b28000c00e40440425403000081d004540e0301901003008001e007003d12610b9a0b519801d0b140140a04165460b007030141c58402c03005100081d070042c65802e04945400c0001d020728540c05500c0006000340409142c50034000d12459010b182940c1d408285101001070309000c078036060303407000f0110742071141010000380c0200103d411a600800c2c183c40f907983c1e41c0c40603200405a81ca04035012180016803500400c0d000f40034000f08a4195010054507071510f41980344048041920014a90b460754100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 380128471 1250 380127221 380127229
    0xa081501030602220b0901021e070612021c0c080105032d070e0a02030105010e0607120e040e0106030302070801060e192406120b0a051003020903010b1903030f02060114 74
    0x101c1d84184030013018240a084501c1000b40d12540c000000790500080c002e0f0940d81c2c1041801403021641925410030034102c0b180079500c010b10300c00c00050050031030410301112055410b41e0030072840c9480c5134908500920280008240140c182c40228071680008140e0782000900014520389100c0c681c008416032034910302c9a0000244141d0390392044030300110f40035100c0880c141c0203140406025031654140000906900760300c2d100940034880a00040300486c004006485402d075a50914404007012840414060440b5440a80440d801c1800010806900103191000c80344c0d540000c12046031070300e07048095100103440668001d0242038210308400855884054030214124062500321800c41034000e1b140c80c643d008070082042c00d40d18000410282c050301d4640041100e0069a01c0c0c18a0700107075444020700b508208140d80840c500350151401d40c0b005071035a030002c0c0031035120a075910500e0800030a44c00200c0c000391724140a490000d00000390207042e244941e40070ac11840e0010280 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 380129721 1250 380128471 380128477
    0xc0f0906180305011d06010b09060909040c030b09030426060105100302070c0b030a0b03010c1d120f01270302030405151c022d030414030c010f020304020a081501030602 74
    0x1101c00d4010720040000001d070709204007102400c50840c5085801e00c14415075003400e905034880c0d840444100703d0161543e07a500b0488104980c00c680781304180d116410b0041401c5407540004103004581002d00403590343c000058021035039403142102c940e10b06004011041200b090815880340d10034001840139160078840d01c3c024031160f24006003000313500d48510540850a41c491542c851000062007040303640c3c0d001d03c600061080e002031046241e2030b13030001c004e0301c00c0511070041c51610004c080c01d590b81c0ea014840301205900c0484001900a1a8681c024160415580d02e45810215094294568158580803258064001e14141450101440400030b0389095058006d0f0301001405c0b200c03107a45201094440350b2090043c0ca0b4200c2804020f451404e80c008600703204041d0420100d100755030411640d10a0780032001001e0303c041003104d00d145005001d54074450f035003082d100d942801c100780e02561095000f26004910260b942d00707945d440c1c029550600107500040300060011400f19001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 380130971 1250 380129721 380129747
    0xf0b06040905061201020a081e070207050108090a050714040e060405030d0b0607020d031e020c031b030a0c060c05060f1909051e0f01110307120f1514040c0f0906 71
    0x41080c00c41300b6994690899100405003804201c5034024402c01e9662491508070380a82c1c050380c410103007000f090280d6111031610a81e8104840762001030007102080c8643c154443d03000080b0741e90340d5110403417a035003c1d1790300000e54002d0703191015450190b10f000540c10b004580001c05540782503e04088240500721404005401c0f420402c004001a2280450704030201e0181e03a4842c459040c14855041c0050742e01078034070843d40521118191960041000496a241258105104234217480400d040060125029050403500c4400003121038100710302d1307070383c0b14400c400761b58496880c951000d141d08030654940481c210f012b950b41c40d038000175600c032115190040c411200714500b071400081401e042e050100c44580c00440314030851141c24021800703242821750f8054114035005000400b00c1c5e10b0b00c08200a890b03101e61141c001c4070441e500c400000390100000f00c010340e03212804038040c034000843c05400b503032400007031061052280c0d0f600d103480e0141e0303503803003948614100c401c490320805441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 380132221 1250 380130971 380130979
    0x209180a1d0102030402041406280308040b070c0510080f040f0210030b0906030f0a1712070c021206100909110402031006112b02030d06060203030a0f0b0604090506 72
    0x5003241041005072111007100800140c1e40b86001d2042c4001c0d1410340006041c07040620080c000160354420200601c0ba8409403000840018042014200741013640050711443d80003c000c10101007500003008214020006419500d40d14020300111030764103502c0c54000340d1002e000c603141d00c1403044400d4002c1e020b0862055007418036000940300c014980d1408010940e950076110341802d01205155000400328081d0090340c03e07159050b5120f0114045c0201011005201e0040000c15142640e501000c400d034106058500310703102601c4448003c8059200d144039042080345203100040c428855507a61410b0911946000a001d002d403d0712041200e0035803001001c2c000d01d840754405540701c0c0d00d98109403100d41e843c2850142c81c0104201a08456410540c00c14a841010b01e00c8505000d82420805143c0e81101e40203d0460050825052015003403d0002030400e078000301941c01810310035401c01a500f203460f00c407021038001a1290760400e50074003041100620940c809a030280020b8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 380133471 1250 380132221 380132231
    0x60e0102030d0509010c120b0f010513090608030319021e0d0603060f02090a0f06020d0507060902030607020f0c0604051822120905010302120a092a1401030209180a 72
    0x10030b21409444045441d160140e548140144135141c0c04280302030042e03201ca008101810a4038040345000c03240c0541d0310f042c000d000481a88080b4880c1e0302d20014105458200a5180c4600300585c0342c0d80256240400c03141084040e01042002d03100311240c00c0d10412400014004006280d01d85401848075440020b9659000101223a0203002e1030701d044502e020700503071340c184110800c4001c9800b0380202c1c01d140700c408030074066140c001640155880c054201203072281c030f80d4603100000e840c0b0007100940501544003407120954002074584621340d00c030815941c9102c1c85000744500303400340b80f142ca07501685e23120f0715504580e44050b1403a0407182c22165402215580c801e6000f1381d94039010300b111407029064a055420354041c0303504000d440c09207029458451000303000c40b01d41c0c0015194043c8241d54800c05002c0007020100f491040104900c040d2114843c05401d040c00c0182d4851825103c0214103a0f0986600c82c0c400c55805007001400c1000000b4200c08502c0c101070000c188074a60396480d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 380134721 1250 380133471 380133487
    0xf060108060f0f130e0c15040e010308070c0f0e0609060330090a030819030203040b241005070b060d03140c0115170c18070f140c0703260301060e010203 67
    0xa018008500442400400d180c1110000380a1000c00b17007069181245000e010034400f4007271701d404c8a41141d070410304643c0c0701c242d541030034400104164005500d10815800005611401c101510b00c1003404030344080700ea40e24601071580340e03406c2c10380644e4084264152194000641207400108502d0b111181d03041c00841c10214540601a4200751a000340214150080440d01ca003000c0041085150a600310f060941d1840324110000e0480c2c092500c8440c01c110710b008080741c0d00c1c01001c80041c0092114541c0b0344002d019139000704003d54150502d08001902414009107261050380d1540c1d550f101c24484500c0f081250b00484a025980d5480301c0441010407a100c2c88080645005164480120300040300c00b0728000880e200c56010320700700b10492520390b082200e05984244581452a048903d10307604842c280c07140903d44d0300510000c2150f02c4092800903011096a1144041d0524603904006066420941101b66030481d44100014810984904641c5110b42c6041c01100c0c10042c0c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 380135971 1250 380134721 380134759
    0x30d020a023a17060f12010908090a2301030e07032f03010b1318020a0305010504050f0613020d080409050a0b0102070506090a05040902011e05030f060108060f0f 71
    0x1040003111004081c2c00e090420800482550b45001007824007011400204040780c080040043c51103120f4015660003007030300d8407010b0410020040c4180204184a81442c1403002034001e520340e0f5000c0d42510002154410084440809145034605c401280900550044015113204101800140100703040000000c404c0c0001034419074418205515818012413440340803105c2e410340611a03070514031000040c4d1901151a41c42001d180408190301d5020b4651002d0601003603402900006c02e04000024800306511140c065845201540c20fa83c0c040d4281c00d2391100700341d5402c04101c400c04030400040c40c0001240c17206034416078455041c155202003075000c6950840d844440300e600e41d011041036603418080100580421904981000100304c0894620201805401d0080b030750366400e20156801110451802d44402424803c00b19650070001e159400c261440d09042c82440080350141d802108260310500000d0300e481788001320f140c20401c1c241d507a9460640c1000c4801e180d0085050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 380137221 1250 380135971 380136013
    0x300e0114010602150f06210304050d0305040e0702120f0d0609090501090c27050612030f040306150506030c071b06020c0f04140601050c0c040f050a0b030f030d020a02 73
    0x8410780292076060301904200003503440082081a41d614041d0421044c2c0d030f42c01f1075503112041d5050010304030540b0004424507500c5140c208681c81000941a5420941e000c1d00400584184100b52501c64448410a80e51051031150100c4400004d00c080e029116142d006417031007420a80303000c1680c0395074580407403c82d000c1a02c2660103035155060741041c00000d1600308003c01c1e00f0050f41951200320402c0d510110702d8120498606a2114040340c000d60390b446052196900510503a681c0e0044030340c02c80400e600a1008441c21414011194820134810301c1400031990040c00d81ca01d1359881081c00d0b440380d0322004048824148520058440081e0801d40038064080c41c0c000304028006a010000000c02e00c100d6940b0813030500f001300c85044c944600d10f40c1c000d4000c0c24915101d46429000034204a0300c0d2500c0b070340051a003083d8580042e80c1c1c0c4c0009010340c0b4007101c10086186048289610b8403014511285940e00800c003000c0c078008640e00800c0322060724419541ea41c40c0346000030704002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 380138471 1250 380137221 380137229
    0x1a10030f020a03060815040201020615011e03050103150b0a0e070c06060e010503070902070c120812040b0708060402180121020d090302120a0903110111031207300e011401 75
    0xa51303110f500b40804002009580309041d4200040b803102d103880e43c0000c0d501c1c60002c0100c0c0b505140c42c000781d04540d001d05410b000d2140000b16070140b407041c001f0002d0080100b4402528503004040c0d15185040a41c0301e0300308649800b0301001c503440e003050307a99041e04801030324050400c81e48138400804643c1d00d11502014101e0f0003201015035160504051622000381c00214050744100480400070f104130705920222940105004101d01e031358140045c0901032600b4207450510054100001c02c41c1028200d481044951102c8100c1e40720181440200c1c01060620384407840c001510700c0c56507010f00401800090015070103c01d4101180c4c6400c2640c008501100d207940c0c8540201c020103806002c440c03030003030880c1c442d1410260a2a0020b1943ea503502c40034210501c1c03540c2030311003648569401202e00e20701d0401c90350f86040e0041d0a1741a00011242c0b0340002d40c480101003a410507805e9901c2d000280f208500808800c0051a40c008100100d4001d84965a81c4001440c1504203106207000f4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 380139721 1250 380138471 380138477
    0x170405041514031207060b01110d0c03031506050a140d18110909060106050f1207020a0c0b0301150503090106030506040308190b0a122607060608011a10030f020a 71
    0x591030030088140040e007500303081d8420380241213201240b0b200780b410350340895042034000c5410b102103401610704d55a0341c183d07007006010b943c0404458680040c00f00001e02d00c00c5c1c0d410002506800ca841c001c03021640901c00010b40200100c2c000640f1950024080c030048101452903e40c0031030000701110204582c032401c4260000c8a401841613020707210b0381512080e20002075500d0607961154488105009032002d0190109181d035080d6500d80036540c030782c1c121541403034081c2408200656a0b84051508851000000c2c10200e241d190740c4050382d040b00c80750080302d10310045118081d282a08000d11080b040d42d44c82c840040890301c10444213000314083d4841010608141000c000740d4013a0796030080704981442301c0b901d8691980ba4100c2d00f140d00c591011425400285000005000d5040340070004400442843c0c20b2410f44000030465a4400c080030840503139904034143c2a20389495040001b04103000305a511400c18051081c00c0100611700003454541d40c0d80d035071080381c016030092400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 380140971 1250 380139721 380139761
    0xf0a08030c071e060507141501030807120f080115020c0a030305220f0b0315100519170f06011806080402270604020f0405040e0c030106050a0602030717040504 70
    0x70000d00c0c409000d411039078a1200c415141c2c10004c003c0c05d180320b00e00c401009074940c01e1494a10010034040507002d840300c0c503008001d0b542e6a09240341e4a40110b402501c080c034025901018450041d814022540700d96200c0d094075a2a0000f0a1394410143c1c0c190020b600500c001a109940c41c43d0076031000c1d51181e101c00e40c650400454940c503480244140d80c640b110002401e001603114014103404441800d0036055807560384c5481e210a6684555546401c09448a610350300c0d0b07a00076000d00244036281c0a030f2010400317142400c4074040200854107000c44418804210030761028070403607502210605118605215190b46139200c54503c0d031101e000102140c05000441c945500c641c241c0030050940040001300d50481138003c1c0b00081c0000c1e126903400511440341005000683c3c00610300180108103420920480c541c0303c1c420008820b200354a0b015000c036151401d10200c0301521541c0e4000d43c2000d6050740c0e600740904080c00c1410710000300703000c000340315070703079806080ca03c900e040030751685c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 380142221 1250 380140971 380140979
    0x409050105030f07091e02070c08010b1e131401030b1b071203050a0b060f030f09030415030509070f080a05120a0210020d0605090c13140603060f0a08030c07 69
    0x4215841a00102e20940080d00f030714140b614005410415a442803000060142c040c151007116000c4500c01c0140c00f50011554100340300405000c4e100b101c410720001d01517400b011040000d00303003111841c85e00c0440e00312a01d02030313800c00c1e4036680c107000400403000401810580b1200c0c400c2000764800c0364141d089004205142c501402c030040002d60a8008904065040d5aa090071900c40010002003590b6a000146060341c1900440c62011000c2c0c5880d58031032048c03005d552180e00803602ca0300c1e4041c00301c001c42d200c140000119001c13104111140b126003a00da0304200e02802000e480407800d8031507080c01240741c03103001c011100140712100040550f180075103805800d001456154050b80d810178031112078440d0700424800c231003007128080181c0c1c951f030028160b401820aa0040354004601508120580d0404002040e00748101c01c4001c61161341c89000e0a407105500440039085a0103001146050502c0400740700c6500300108000c5031903403601c1c108e0346160440740d000001c5610400c4100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 380143471 1250 380142221 380142239
    0x309101506030b090f0a05060102100e1005061912030302090402040e0a15050109170a1203061e080c090c16050c0a06020f0a0b180d210903081504060302060f04 70
    0x145400f01078400a0040c075000707140c40840c800040c15102c5042c0c44100003201c5030700c20302107450b00c0001f05808000c4d07074540e00807281e610032641034860380d40c1e4a000086400c0d8684016650f0b8140880281c808070b19050105411800c4082c2600700d05260302804460001d980314000340003d05580043c0a146180504442c014345022001840030200c507550103001d5a41d124402106941c410b101c03000b4040701c0180d1891500e1030605015000d4000607411111155250308011704a4406266140c1d05044d0200c07410141c900d1481568039551218400820318240030f038600d580000710210141c1003800c0490328855130f10040c001110309402054204080d8034100d401280501594802440c01030120342540795a108a60b42c0034008480c0030000805159904522260036003e140c20746521503075440000e03180240c44400c0e050903010350704005a20b504640315003841243c0642d40e9800d251544113010990303000d480529500503840303c0d00840940c5500008041e0b400920f400c6680e140d01c0c104001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 380144721 1250 380143471 380143481
    0x421030e01030902030a0201031e1a090610021504030509090f010504050a06180504080721091a071401270b1602030f0904060e010801020717030912030910150603 71
    0xe81410b1411001d840583c0b800515410015820f0800081040000c42080c1840c082600806080c44c00d05000c0d4a81c41020710503e0440c117810750346089a0744401c070401c40d2500c08a482c18005a200d001c8030744000366051440740d003050090400f40c0ca045400402718041e110211100c83d12150180c00400881c01c3c14411300b5031040f0710003000c010160410800f4404044510798a500d019190001b01d07051002d00350482e80301070f0b03010307000d801251410701c40410f9014802d01c6100100300c0c180d0700050400840041c03200c10182d074051141c9084220341d00d028802100d5030800a0719940c0702210381c6848a10400000038000460100e400d8800c02e190000c6010300061820400c0150410300b125203e400100380c0d0708010b51490825114988040071400410550740700c010380800401c000500750302d06600522107240144600200c07084190706116003031000303580084040c1e10400d41d902c2204100b81c09960002d0008050702d6200d0b90010081c3c0554a24201d110000c840348503040000c99014403c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 380145971 1250 380144721 380144747
    0xc030705100212090609090f040b0906040314071407060903020a0803040303021f09020a0e06010201050a060b030106050a0513090b132306010e10030e0f0a08040603020f042103 77
    0x7140040c80900240291640090f907502e0403032000100d4488200c0d41c6203403e55a03119806403002c4d40034502811000c0c080082927038141d03045c00c0c0c00c0022500c402008030345a4455500354035a0482002c507802039000d15400004155014030001d401d030070855400388091b100501c850b9a4a01069066004004031401140c0c803201041e40100b004200090b000704104450f00c003440c0c511078a442581d05124043c040c46040254400840300021401c50900c40c1d00314001c01702a4001c014075514150018100c800c280102180380d641030004008203886940105003011091070031350705004808040e1448011160070913081c0f203132942403c1406042c80841000d905181000c10b0101541d680342442e41a05104400d121088084000866503409a41907010241028044841051174854002c00500a10500f00300c103000e201c5c425800500d0008900b04059040701c0e09502c0c1c2482c056041d0021b42c050140301d960000184000901e2040f03583d549100320380359100da0192102149801454002c000726 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 380147221 1250 380145971 380145979
    0x1080708072c040f0f080304140c0108060f120105040b01050103151a071a0f0103060c030209090a09021507030201050a2901030b03070519031a0c18011b03020c030705 73
    0x1000650340242c040414440050000c018a6562214240000b8440b000080078100d88850400042005041002140303e1809400707404054100d500f1001e0311158466400c5001640d10004644d1510700f070307100ba440840340108070b61b0350600c0861f01d207400d46900701c40c00d803542c03072803540104903658042c09101e018404d940071000e001814812240c240010f84141c00c200064080340420800a403564043c1511442c1180b01e0542e152008840000036001d00086550b40d040001070107a8030b010f802902e024500061680d4102e6813101c0c0620020010070009980c000360410100f040c15204100800c1d009020f58008181440c00314031800580d440400110a102500320401541040401c500d040c501e03000d20b000700c2e000d080c0100281c6084010f4001d1a44250600c2981140900b40340c245820ac1c1d05c21080c01002d0039a205980e10340ba00c04503800111604108412001c200404107082240d0805040888150f041c0d020780d8900d520301c1280c02c4001d0381c443d1020b0b64482c40c3c2045514002c0004071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 380148471 1250 380147221 380147249
    0x51f060c0b06030102030106142a010c020106050111030703030b04060f0605070b070903020f092502150a0c200f34030302030a1803050d0201200c03030c03040201170108070807 77
    0x2301d80140304c20000c2c074002e00706103000720310700a20394014844498540c00784200d0a41c0a500c0703a1080380200b80f0203c2c00c001540c0f074158000340d15405940b0b22550300810f24055401e021040d2070540140001a8446030b01554440012803120000c450a4001e00500e56031161541007a00e01602d41e0308003e442c03602030180701542080181daa154075001e844030240c80f821003c2c0c8600c9560074200e02103000042c0301d8080704140c11039041d030001da40045c40d110a0403000701501c9101e01d00007162254030500b000501c801c507014100007078011141c5002130000c0200c13500764056640e0070b410000010040e90341c03062412508402c46080b9580b0b114900c07903481c40482c425203140c0d400303990303440f0380038001050041250000300d42c1e05022544074015038218094607411880b580b130090091585020b9021440061800c0d01403282011080e200c200304010000c41c42c54890034441d01464000410490401c8a401070118a280708516081c0c020803c50b4001c22040e810320310658100300503070f0010b900082c460 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 380149721 1250 380148471 380148479
    0x2010908031303080a113c1207020a090533010f0807030b090109020a080c0406090306020724060305192303090a0b090907140d051f060c0b060301020301 67
    0x15100001207a50013540f803680d03045031402c00d4560b8541800390300d4a50043c00c3c000391100c0b4034601e11070305aa103d4003a16100001910000b96850740c1030300314290035072002c100390713100701050301c0189051400200100d1401e682e40d80004240c0720112141d080c140e0b09e5501940b01e40c08042e01e501d0503040101c200c42800c2d801407000801c4640000d07110ba042088150100c1c040034026407008511020140c030700021503850f1044d000107540a81c04110008107000c001440700703802c0d03205490654500d42e039200380881c03071a110140070b900008416160b400d4420103148482e0304682c8814500b100360340010039402c0c907609040342050024031003031045101c1d80305110001022502c1c0b0302c42031001d24002e101c4400304426183c2c5540070300c00016411205176800480c1d0500d910004d00b001183c11640012141d880c028101d42c1072400c06010100d105003030141c001c0440d0140c0003030b5030000c0725202c00b4107901d1107d408400c000780c0a5000c01e003c2002407510205200c4441c07003d5a101e803054000394a59458 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 380150971 1250 380149721 380149747
    0x180c0402090f22020a0c200603010905040c090c0c0303050606040b161106120a0c05130620070f0e0a02070b0f0702030d020d050609090f070b0903100207050a0201090803 74
    0x1c0411118400c40c104a41d10aa42c0d400315840000d01d03104100841d245c01504001509540c0c16100940d035440b180b120070504640000108101642c01030f089034210703481c040038079028110140040381c2c26059003001007107898451050039000846a03903901980583d6040280850390080e0016004900802043c04154814422503044c080da0200360750080050342030034016500c202c0201640040002502c40981c03d8070340319640105030f035a03400c0046c580f64003005d4680380f040a14060030819010b070108400e40c022406854150303411500140341c0600d2440440c10300650b900110702e8082024802d20090070035124003a403100825408501e000002d48890803245401007404001016030b60005141c02c0c424826203003051141c120a41d159010a0840005058100c0b0341d54041e204000005000420025080300b0b6040c402018120050900b40c0d010540c5d80050340254140c49150041071104085100030700d092401100640f10a491a100050440e11160b00500c081c0d0710034000c214011103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 380152221 1250 380150971 380150989
    0x9030306010e06120c120f01140108040203150a0501060f030e1e10060f1403011a09060d0506090c1005071101080a1b03050a050c0c15040f0b180c040209 67
    0xd090925001c1e00d036481e0700041251281c450404840000b5100303001c448a00030700905006000d610070403520750f680505182d071100d024402c48a50001c100c00038000765001382902d0b904103001038280d5100e0ba60341c10007520006015561a009a0341e1000100100c0e07500c2540401030704000d24003400f1107c600c1a00a0792450b5042e0034071a0f220107070211042c3c40d2010040f25105210911081c09010343e500545884104da6108070170481c010640c000c90103150620903103010907641e049581c120a5124240201c40308010140fa40290700c18001e0804101c00708295485149041c0c020019480a034084c4550541000c0004061010034850300000505400030800c03800020310308021240d9070750740c81c480034089511031942e032481100d12003084246d15070807040c80340408620600c0151108129291a880b40350914001c43c1c019040300341500510f900c002e41c11901401c3d14000100054695000e03140055403012016004218112005002400b400010040484003182060f65000c08a00d02032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 380153471 1250 380152221 380152231
    0x9050f060d0b19050406050a0b120702010209030a05010b0a05092a04050a0e070206100b040303080a110307170906071d1906020a021201050c0f0a1b08030f0708090303 73
    0x2100441d030340001c014190b02c402c001000c01001c1c20b5095101035503181c8421a5401254000c0742402c0003c14a801d184480d60100c9169400080c0f41c000ca0b00c602d440311003006417a000455400f001100015541009130140c140e0180000182110b0701000300041406583d02c110b0182000d00100400855042050346941d58030300200d41c0707882d04004070915240708642209500681580d07011581141010350b60b8440c10083d02211420344543c07590780c036540401d11851088003410031042c0b0010b8030803202c903608140c4414000c900c00341c0f00c46440d1001c1c0c20490769800050031450010700555800c002c6c803030b004407403500604450f091805005045590850600440d80c0c85200509078544a400c0724510b584001540510b0389512003030025120b000c141c7d0300f43c0c442c002101c01c6200b00c42d41072080c5030088280213031886c5844802e00310003050350000d801d1001400703d210201d0802001003907040003c2480303002e4045c0e581c07038440c14a014104024140500f00310156040100c40b801c00170807281c101d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 380154721 1250 380153471 380153479
    0x705031618061d090a050a030f081008031c060314060601090905040308012102030a080a031104080a060c181202091f03030e03071701020d180f020108130b090c01020105010609050f 79
    0x15a41d8500700c18a01712200c0c1c0020400d200ea548444145030b88410b69244012aa9035000519110389200c900d0000c2e850041040c541c00c00c0243e40c400003100c19a400c940060001e012a10b19665240d0070100704040c100702d141d9030072a1003048129030b0721200c0c1502070010380c00100400d05080d140104140d00500442441300d2200c60341380f443e85441240401e0b09a401421100754080e940b40c040401d802c40340040c3c001c2410316801199401c9104c041d202981c00d1b4400030718a019207901d4045c00f514203219100240080181903418001c1e46103c0e0501078500d60143e00ba01c00524818021398607070040000b2100040000d441d0140c049840342002203a4041c40c192480716011030000303080c20501d0380590b00041700041c01c02101441900a00300b0290101404c00800005a412100c1e03480c001000a08424031080e1090056000e2004240c06c4440d1041030b6884140c2039940c01d0807000140c85400c09a0322070403100800e50707030900856000d4140e5150081c2000d1401d004680d08056954586206d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 380155971 1250 380154721 380154779
    0xc0b0402010c14070e01060504121b0513050103020f2d0303160f15201c05013302070902030a02090301061221050906070302070503161806 61
    0x55a118a48001d80740341c003c0301c62900c1c001c040c41426134400240c8030304013164500400000784a1702070340c00c2e02e04030344c54a0354010741c0e001641d44070081e413004580c01e26000e903003103480498071b0780321a000003002c418034100009155048d0300400290b000c030354104034403520400744218401040d048500105458504174242800d0780800068190b0051000160051710904000c20a02200c00b0300c2c119460b01039801040780d510300903225000d644003007500c0a8512111803401d0080d0903958001e0044800e08404a0b0a43c203205058a0507a88284d106400d07001c020002d185150654510000d940c4805020f10f0580c500d150308041d4032018039201f02c6203082d6012001411141c11501180c100100090007000000d4440c1041011411031007001e0700d5601e60081c2852401100c0359510741e4070039994a8160030907001e4803c220890f07001440481c03c42c0240680010701c3d071000c00521040c0405104843c40b40340c00c08849030060105000600c003018102103003003008141c03510310699000d10312450540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 380157221 1250 380155971 380155973
    0x724030f1d010b1c020604061d090709080c101202091503090a0b0703141302041e020d0c021207020904080c0f060609010509190f0b03071d090703030c0b04 68
    0x402498500e04078600c080006040450000d030640c000b80c0801c1045410404440d04904154441510f08200940101e000c010a00402d4066140d401d0b0031800003c1442c50003403041d010410804c0c0542e40c5101080854030184034140050007001d010110940310040703c004501401009022042a601d81042c1d0014034800c440c1c465080004080220440481da207090a00106d665100c3d030b400700b07803000008000422241c034800c0c0102d00c0c085d60004201f0f40980c585046e40c80e060006020120ba00075607441c110604100258030705080fa40b210400181c0b254200c0200c541580d450301049030854101d0111045548606003d51308583d405540800250340d40b8a01185188144035240c5103608c61201c0c1080c1400c0001150340c400d0030103032080e65559030b8402c04d1180c00d010644400441100d04040e02521002907481000d00d5540c1483c0030841e5148600400d040441a41000d81c404403e40f00c2d0302201c1c401d100e43e181d0400404002810101c0c0340d61402007000c500600000c2000e07a00c2c0002c68 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 380158471 1250 380157221 380157251
    0x31205072f06120109050106080f070f2a0c0501030603170f040e0115090b0903100c02010b0a0b040f06020d1d0a091107140303090c190e01080a05072403 67
    0x1c40504805051540d80b08000c66600304140024400c0d401002e003040e0012820900c50308115010301d000502e04415515500001d46541401034120b0301040300c410301018aa81901c10101001c040da07030790b10300c0070380b003541000e030502e5059400c00390600d030409408100140c0c03400c5018502c08111480e268540b484000840654400c0b07038003482c00c3c02004000881c000c0400e00001038880b0a50707e500c0c1c000c96846019030024000e0740301c0075525400081104031040c10a4000302c1c4031201510002400c0f10742c0c1c000107076100303007290080500743d5000305081c4400102046510090301075030004201c80342c1d10410040c50b01484401c02d00d400030b01c00440c0f45403525030030701d05c40c0580580070f0180303d0b0742e150b13a950280d6a08943c406443c003d070f800b5000118600040300300e030b000d10040c2c40a032000d2039440040c0080c0310348141309620b1220004a00048d29030708403810724060020100036250f40c440500340b00f031504085400070154401249003180b8900b90803e040034500341c00e41404a074107000d1021003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 380159721 1250 380158471 380158553
    0x7020d11030f04030c0906081911041b0e03011d0a03110709050f15010e010e040e2a130e030405040c170405030a091a03010506090604120b0103120507 66
    0x100300c4948007041c0401000140e407580d0095400d400346c200a4180d5982045a5403d02c00580e11300351005901000042040540c0c812506400600041400d000c011310884421005042c0c4500044030f100d4061154a404c0c020402c00e0b0000170306d2403078035880d0840100e4459100550050510402401840c840d903c00d1000100414400a00300f00034900036038144003080b001c84420f0b0b140e101060411001798040c200043c00c051060f910581e14110340c0382888004c00e050421004a407103070402141c405075500c906001c0c0701f002642460f0303c088142c0144210703841d0000480760304609000e1840310402c000001d540131103108803400310340d08401d600261640c10034550704a20401d0048100424810008004c02c1071240d165517003d010383d0b80f0101407252400c404140c1018110400042080c1e1801c0e1001d800c195100800e06840d050765204143d50661141b00101c81420982004000340140910003030110724a500b440751078a4015611300000384040c40c207541a07400404d180d4000d1b040c0007419 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 380160971 1250 380159721 380159737
    0x9030f060f0103031e02061503070b0d020918090606040c120c090612020a0203040b0c0102090307060c02030d0318031d030d0c050c011e050306031204030b04050c0907020d1103 77
    0x380e40403401d01c440c410051030300901040e008181440354101094443c400b04466104242d4041c0c0700302d444003050070803400e81e82e44030741d0b40c14441c144c0b000ca28101d00c04010710049554400060f6254400c106202156010421010550000904200b6103040104846a00501c11034001800001890003980c085e00b001449030421881e0030300e034a940682011000068540e2900c40c4042910748141c03140c20b9200d0740d03002a0040e0400e201c20054a1281c001410744000e031030001500709444680800d28001981d031026001940c0103c0940650500303000410010402d40760a1008c004030340c61142c820300f4500c50090800001605460300c2e121912103083c0c41040050035620324640d4207a0080c80e5035041c1320141c0319070241d40d04441c6150300410742c580b030b000c441d007014014060103001c0543d03050700700070101a00341c0a00800340c1001c0c055000203201130740c41110030140c076050906000d440d00c1d40c900c207071314000c841220601c44115000150f0400c11600f91401840203c40b95050346e045018601c2c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 380162221 1250 380160971 380160973
    0xf1518091103390705030705030a020607031404021e0315070e09090d171b0d061502010501060905123c2406010509031506010306140f01030209030f 65
    0x7901034a0107010000840c0242ca000028107064849604000c0b8079182507081142c2d59015000b0b00700003000072a01410704076014600792801c0c910036480780381c2903611008207680107030003550802c003003160984504021246035a5507056103150030360114a554012031404c50400b003607100140d1103543c0401211184080070100e60485080c6003d014100e5000011301c0c0307110b213a0030400102c000703500048254144596a03940d00d0306862a4489980c000e4001d81055a044139401d1354450702201c0e2002002248984e0b000040c295181041c0c1e0030b20381d4941e02c3c0207021641410010021554004182c02c241c0b0070441e812a0116645964149041da004210840100c001820036000804041c0c1d84170000c83c0440c540395071845840d00b8076403107004032413064075940d80300c24001c101039000410855115a0605100b0b103000d500d00006032030000c0072004494002c10500400c090b40d603150003403000410501d46403020242c803440002d099480d40500841c100350340890081440d0741c04008082148003410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 380163471 1250 380162221 380162231
    0x608030406361a07021f18030b0a0615141b0109081305030303161805031f0b010509060403080c07031b091107020d02040c05041502010203010f0f151809 67
    0x6450300c6052a2611900f2401141000b880e40c1184075201200e4100b980140031030061501c9911040c0c0c661070b5012803004106805207100c1005084010070000785008032000d04c46450a111110103491250308210000300c46a40c2d40c0c8240c0c0c2d000202d044c4807060300104251104e0752200890046459900e09d600d40350b017030a560703000b07100e50710340105501c20742081004900ba446130140b41d668031080d941d06e800440500f40050441c0d1250300168043c5900310a84404c13569100d000900d400744242d0100c500e110086510100e4000503c03c07850040000e0070003a013880d09240005480740650300c8040c100e06000261040c20501c18803165024550040c0c90b80c50801d03500d0f05135050b1840b540141e50003540341c01c2000398443c0c00d0318156aa2079034014101042c440956081c000605140c107240018460180004078865580004526a0300450b80c0010f031a03624000c80c8654003011b56000510050503500c0611a014403506c03180d010104c81e041c080741c031490311007401e420001207a0000c1c144a00d0b00f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 380164721 1250 380163471 380163557
    0x4060b03060c0c0606010507031b170412060608010b0d03110c04050702030d1a01050720060f220e060d0312020f070515090604080315060a090623160f15090b0a0608030406 75
    0x10f80e1079030701600ed181d0401115031a0340c0310303e013210054500f0f10b5120086500300000640710700c038a211030725003507001d03580e084841e40045820b507001690701001580011841c044001505c0c400c1070500f602100380d045440701203400103400b503c0303a000c0140c00d08480c80700c1c1d00070b186802c9003100c1c241140500390580e12100d400404803950440c7c103540e1000000d00c1080e00c441e49001415000703585180d1030140b501d0312102c08008500d008008100e05101c4940d2034501c0c040001e10250032002c10201c030241d07540c0c0940c5003440c10b0034640e010848064800505001044200158a81c0d00543c881e01c00703a5282c545501e046200601e030306469030701400c0003515440c840d5200c1e001c8001c0703c1158a6001c001c16003130501095201d011381d1851201941400050310880d22268480803141c02119002c044124503220000300c44031104480041d03e032035610070f0b81001002c00c45150700400380c078010024541440034403600e03481030341705140030080c1d00c0ca04007003031101d240f00700d00c40144100408c4a6000d04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 380165971 1250 380164721 380164739
    0x207030b01080d020625050a0e09010905010f0b030f0a09020111030301030c0e15010f18030602030c0703090602030f04091505030a060b0a06021b060304060b03060c0c0606010507031b1704 82
    0x4000080f40103005640101e2030300d08904040c050482107006042c0e41071801c8100c205c500d07030418000c0404000030105a907a264580406890181042150106043d810010100d84050300c99000c10003907401003041000005504004581218500101191741ca0300c0703000403280c032685403d19580034080000000100408181048100c61041912250541e02c2c988110600903411440301c2c040b0341080da0303101c03805125034080c0b00710141841d44100916101e4076004201d810171140c00c404ea03407000406005054100c1d1710b0000410f801c1c402140f07000568100d25129005d14414010a183c0700c9242908604a0400c2034010f09400f800b00d0b40c2203521070070204094401d01c050923018025004020808070710108005091100c5140d0300000441808107100701c640c4010815a00c00c0d666800a15160340c00b40a00c07800780c0700800c1111380740c6010340c480c1400d10f10040c1401c1e05009040000c4000241c000b003170f40a801d01c40500d800007946050402c204052084000e4078802e039000200032442c064 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 380167221 1250 380165971 380165983
    0x4051f090203090d090302060706050703020408030a12110a141c1a0103050f06010f1b0c06090305010c0c150b010c0c260102030f13050a1205030105090a0605060a0f0207030b0108 78
    0x700884040c5096000152034401742ca000281d0824401c03c000b84c08502180c00c850307001460ba190052500e90f95440d04c030b0842d001181d0600018025054400d10072000c1d010707100700f8003c48103420349404d02c4c920700a0a40891034038150b0302c40502050003100c0c0100c040380c0d03183c0402050400d01006100301103042d1010083d03040603001c00c0c94030003c10207101010321454491201a1203200f0840c044103000c1e0b0312550310300a41464034262000c0b4400107541c2c044034000074034030303902c80c45e07802402c500e030103800e5032181110f48041009001c012804039000b14404000c1040240c00014100540c500413510081001f030050f0803c0c5c002c85d000528000b5102d07803904c00382d40c031420310f1034440c45a034900d6081c2e100a603841148070b00b440001c80c90000d04050102035603482201101c84004245c0e8503491030302407a405107404030310040010042030824104059000c2c070504000c01000b82030400088480c00741089607800c200c0000e40c20040c041c000c0120034050f54225025001c50342c1d442e805140c2c2c480c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 380168471 1250 380167221 380167231
    0x340b07080618090d180f0e180307020a050d2306010602010c0806132304060f0507111b1306091b02070807060807031418120a0e04051f090203 62
    0x540b4062800302071115060042d018100e110050400b0310044502180c0c64aa0314042c0010201340090002d020b007089503440d001040c81400301c4000e031400314901000702400c1402c0c091190001c008940050756038144600035108101d94442103c0400c1c00c10412201100980302c2402d01e1650a60981c007900190076170407190a64021310280390b04590481d20076001323030350340b54110001c4854000f00d4035107900500c41000d01d9144208000c401941040001c1405440c00d466040d500c0a4115010b0102d0145651040c170f241007c070328940122560070355800703a070011b20503100c0c007503a1504050fa5a02c0d403581d043d50641d010034041c0350b40320f04000303000f4503007a0580c4004840c41202c0b0100e0030f00106080049465100c0608150391606078103480c0200020b00c00070030107943e290841d620744400e8a0309402044400d000c1245035242e101c500340307045908803081c12a148203100d0903980942c01034551500b5502900c02182c1d070344030368101c1041c14840d084104080c00c2280404220010701d0340c040d41c411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 380169721 1250 380168471 380168479
    0x513050d050702060301051302071e03180e0406050c09130e1b09010b03040302030712030e0d0203040f120204090506010806100b040f03081c180c0b340b070806 70
    0x1030034900d441900e8510448400079000102400100040d01d04a2050803018844000151900c0c90aa4407514011071541d801e50f610100103208100b8981d21018402c1e04e1030349005454000c7c3d040c210704d628a07420043c0014656a1100001040007207442d09541a05030054030150314003245e000b5103009030004665a11961148200758040c0c0034880d105462800e8001d085a4511f909012a28406a0004100f50154401000b4000c00151169003040000826642c0007603c00314144d50b042c10711b0700e5031600350110362050106000d0301d00d2460302e400844008001c0184c100c1c19510100b00509030004001c0c20038003483c4000100c1c0c0e0404035120f44940000c1d0780004801d43c035101d400c2801c0c06140280f1285004c506000c0c80003034010f0b8018110410790214001c8150f13000062601580c90711300040c9800061030100d03504105c42140660003501010781a1400d01103c88210000300c4081403d03070425060000401042099030a04482d0468100c2e044010b030340f80c0408003400440041e02c0e143d0007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 380170971 1250 380169721 380169733
    0xf0106061409011403041e06061503050c0d0c0912110907020d02070e0c09150414031504030f0923360612100b242209051305 55
    0x1101c0c0c4078034100d82034140142c45a2900e85403030ba07420401500010400c071a035400e86c9108480c556190f10381c40e00710754410800429140d0600810050300c070316101c000001d042c103140034850b80300c00031015214050003542c0d000903203660400d01120495196031014004000400c1090181f02040740c10741503e1070151030780081e03a141c03007000301e80e0703500309221520047e003144c08180711a903180c01f0311b55042500841e00e20f0801d003c031000609402e0809030001c110600000b41001508841c1c0c06c180140c4808501409901c03403d0036644881600080c03008003004195001c4600080c05101a00050808c414111456a42102c0040752800c10180650b1141591614034026080303420384000b408907180354003428442110000b4601c000c40540307006e81c0102c2142d40c4040d010000c200d0700c09d0141517000046160500072040c8008604a01c43e481051030845046801c640908000c4410140510320990917204200ea030086030b51005801031a202402d04c0140803202c0300c2c01d070030001150b02030b1058402c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 380172221 1250 380170971 380170997
    0x90b032e03020d0f03092715080319030507030e0309040f02070b0405061909050d0c030908010e01050f0c070c0e0901090b040308040209070e0f06070503070209250504180506030f0f010606 82
    0x1080c0c000665600d000140d10508184055404d0308940458404048c1680c80141c441c1d800508580140800015188050a0061100e03071325000c0d094014045080801a00b802113080e1602d900c1070520660141c2e0f01d88940401c0c4500990454072625046809544182070601d809501d810040d5891108007003030f4001c00315580124416018641d034020018004810004010745000385410b80560510020440001c0c0300d0800f80280d0100010603400000c46207410358a00320590070140110744400002c4c00b4070b4000940c401c84600503203c01c8074881c841562131410043c00b4181c60f000c02003c4001420034807040540059901740218421120010309680d4500d04544c0e249401b52072641c894510b65040409080440003400c4190080040da803918090743c010600071041038030000105000b0003102c26080441c1d40c11b10b200c9540c0da1408500c1c09141c007410f030003600b2290001c066980c0d07450340402e4440d5800c005044005d1a5102620724881c06030101320b00900d85c9208840c00720798400c110078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 380173471 1250 380172221 380172239
    0x8030d050a0c0c061a1207081b09013b07120c080601050d060b040b0306100c0201021005060f0a15090801110403230609010903090b032e03020d0f0309 66
    0x5030000140e41c1c80c0300392002c3d241c80340006800b006120310460f142d4654840415203400d15504040c48210300280071242c03401190b0762411208040b0782080722a0011044d01c165600070410b411615401b20f124694210468140b51008003450350402e80d0b00d9540c40c441c0d28440d1102e10512440594070303004411010b071010a0246d4544800340d50015170344070000b9216600840141840102103180001d485443e400d89044c0355009800c91500030b03001008005d20703803401e80301285003810540b1301a0b000e160b142e40040d656907040c26050050a07211000035060391036080d429511020010310704880c50344d80304040c0400c0c0601d65241030000b00000d002281d118014094040181c00040e04546080c0c40c40c4c40b5400c042c2c15120b00d500c0320340a030081c2001c0318102041460301518801d000010303595280d2401504400082d8443c0018010900800c160340d01c1c25000c0803c3d895000d40301103a010302c110b03014070070096140c200a6000d500f0104c8081800040200c00b03010074813944901b8292612000c942c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 380174721 1250 380173471 380173481
    0x110a0501110a030f050f1602030606010c03050306040b043c090f0f03050405150301261c1e03050a0e060408030a020c1608030c0606150a0e1908030d050a 67
    0x509500040740e150009104d80d4070000814040d241082c00e050002a02d140150700444400c1d02420030242d40409515003407115070341202003402c01c04103051780d40e640074209004c0284a10300c0b40380d641c90400c0365038070b03035802c180445002228054405400000540382e01d2000010380015144001c0074220110814464140e426800c40c0307201005040342c5d51108000074030024100d04001c03083c0800201a150000d0080f0340c980c0b00c0c141207031298180343d000c09a440c800311280608a180c0f0310380e1100c501000c900e135061500d50114080e00f11400c1002680e1501d1281e140e48081510000c00c039034a541c0c5070788420302034990040c051101d108201c922980e030354010b41b00509008000c0000c41c00c2c140b40380c0c3c001d16002c885402500c07074004051943c450700c181d00b5032000d08a5040021610030383c401c14004154850012078000715601e0b5099140405030040e081c82d0005d1049a1500d80d1055450117150001d0546408006100c1502d640c102605c0b60002c00d00e4442c603d0800c400b08903040034074090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 380175971 1250 380174721 380174747
    0x220506030c1305040602070f0b1503070f060804060e19020f03030a020312100305010203010e15030d12090501020408100c0212070812060f0909010c020f0609072709110a0501 76
    0x4005066402c02e5504401410090001c880e13103a420420b480024107012552465640203203180c841034980f2a401010410344020602d11a821010041c4a101c0b4032007100780c2680c289243c000c001ea511031815000a1907242010607191140303000003101c8000c05152807000c5442695541c1820030840189581ca0045c1c041e8240503800034451040004d65140c0070710342c080810320001c540555240c94a0782268401e13044070303090074000010030400000c2c072942903409035420350060200740801d40004295249130f02d011902991503000900602800350142c801405070101075a174228115101480101040004003016006040c0203110b8244181d00f0f442c901508505110700d080071815030300b441e080c00140505e42c044c4001603803030315640310308500350710a00304140002071444100401900c0c0104203d4000b015601080420415800c003241c21030480d02d003003c01d9001c2d40381ea51401e80c0c24040025900fa0420300c2d026641003403200da003015040c0c404054501058442e11800112092003050345 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 380177221 1250 380175971 380175979
    0x18010603110103020c070e0405010b120a0b0a021c0e0a020a15052506090f11030a03050d0b180405071401050705150705040506040b31170c220506030c 66
    0x1809000b9402a001002c2c490030b140150fa14040d1581140c420f107240540d42a5410f139586c8440298a00b4202d4000c1c08031841c0c01c000f804511000d545010503080020040c600c00ea80200344049540c41402c0400c44a07906003038140101c034000c110300c0340d5542990100341c0c4294810400002c805d8840d0690303034501401e40d9560b40c9041c2948070b40c80b4000030004e585c0d000c000b102c0b02c041070105031039108040f54144035140d864144146420000100c003040c41302c8511030f40240d064100080c0d0441d0450b01000030102e404119200902e00050319120700c203551100d03100c0c000c02000704004021503240c060b42c15080c0c410418420f8a401150711303004d0840000c0c0309911002c1c02a0b08a004c002e401c0c1d501c00240d14002d4a0035880b0404501680c0143d4440c14003100082807800b003207201080700b400c2c0304501003420094024081074800c2d1a109911032560404080c0200c0b1030361060501000c14004006048a0070f100150050000e145494203100d8810b1450301001c0b030700b1407801040c0042d010200070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 380178471 1250 380177221 380177243
    0x1c140103020904081309020a1e05092808030712081b04171002161509030e0d061803080402211c050d060f0f140d06090809040603050618010603 63
    0x3603a03890156100103008070f400360045c1c1300040c25a070180010240d090250356020a110b0808403e0203c203032104880105006003071022613141e440307421905944102c6040040c40395070383c03005000100520764100e41c00320300000038158103000d0301d050200c15032649651000c041d0751350200340f0b90b4016107404082800c04010003003001310138001c000480301c2d8210441580c85407d803d40c0303180202e0340000c5c2c0c0c5010060214945005121008844051004a8203000d1055040f00da5008090412180620740300340d507110f04140c20300c0103e9216568911120b80c11400020103410042d20311401114100c0c4650390103155080002111a20200b45055035002060b2402507a24580701c9110301109040c200b040074410465038041b140288001454844603010041d41090902c0b000810b07140c01401c0782d04108003004603540c41c3c00c1c0064164540000c0c00207943c2032540b410406620440f03402c6644141824000300c02d001c0d0102c3e8060040c0215004105a292043d07102c41c20303a003d80c80003a043e90460 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 380179721 1250 380178471 380178473
    0xf030c0703120c08090d030b0a0302101803030e100e030c010818030f12010602070605070f061d010507120c120b0d171206060f071113021c140103020904 67
    0x1140a09101807090906002c115001d80c0840e0840342403100020019401c4001d02640700c0091250304800c484528050003414045030200e6541c2c1d016100c02801201c49820012030707148240c41043c0359030200d8181c618110342d242002090045041c1040e8410301518000d601110b024280740c030000da40c00340207060344102d40b40065680080050440d03506100500020440c03107030502c0100780e152400c2104a403a040ca2a40100c03640c80141c10480940d407045000b840225002070030365811542c049003c0c500740b9203928114000d08490f07a50004404425800c1210120781034115512a41e820b5544a0301030a4485441c0b0030360751062510408a08040b160560500e4a074108021118026040a001c4e4800340c3e6241040d1003420b40303031503000c01c01080080381600316400c42600080100e510a0800152044030300346c074410703c03100070304440d150150b511a94a8094402d000d8210001301192501d8001e070002c8030b00b88603200b41d4084540b800a16151681e403078a070700c41c181c94014101142030780d21 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 380180971 1250 380179721 380179741
    0x6050a0302090f0415060303020a0b01080a05031b15040f03020c27041a0f040605060a05090a020a020f0706020c010210060e01170f10090203100509060c13090203040b010e0a020f03 79
    0x2028009603600c1203840d50f1820500001d019040047d4401ea0041140500300c0c10b10000d0804184c00c041516001804010302007403002046d00d80341084000140d0120001c10031140c502050700602d480080000002c02c4180143e4620140855000341c0940b01226002c13810498150425124041d03440049148200d0300c20715410081d900910400d100107580d08100c2c0c041c2c401c4001200d060711524034410030801045060b0083c150400c8042d05c8503494141050b00050204c000103000d01e0300687c3c041050390400b48200945031080743c404041d107540340c1d22420020344a0f0600754165016114030000d10303123103000d43d100d0320702152007e03442c00800f64200200541da0980031009803c01d480340c06110a036a030014014244002c0700318100241820161052600f4200c0a200c583d105c14606010840010300c0421103a6120018066090b651882c60548811201d12900941582403002c410071041101038005641618070700d440c0200186c2c1c0d6290540c0c141e2050020445d0099401d1010804d0802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 380182221 1250 380180971 380181001
    0x6120c12180501020706020702150c060703020c0a020a030c1e0b040b0703090b030f0109050a0b1003051003050319081324020f03040b0604150503120f0c0712020406050a030209 77
    0x194010030300000001d15203541e401e907041032006960055001030740e03e04500d0842640465120b4640da52403e0000650a55403031f0755004080e003042c10307000150015006002e001e20382c0300a900500e1401200c1d12820a070303440041c2400340c41212641c0000d003182d252100c0115404481d1100c900710716003814410504503c3d000300c8404c80078000502400301d0f546d10306001071072003801d4002e0b000e40c40d9803411a050050320000340140c01c503646402c000c4452500d40c10a1402d004419027800309040e01c80a411245145080c1d02c041c00c580070108a00c2c005240822010899901745d5443d800551241050f68044e01d180120082040c44042c0041e1689010100304400d001c0c4d08643c01810074043e00e25558059004413400c5038241664001c0003100d01d0039104070300c509400d80303d00c00585420500429501d0507030704d0b54642d404c2008541142c44405400484142030031034020798091617504c160084118034642c0003203104906082001c907543c11b00d10781050441c1c3c0c0080074461a51248100804021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 380183471 1250 380182221 380182241
    0x30213020f0c1e060a050c03040f020109050301020a081b030907142403060a0608091f1805060405060112030e060901090905090703111e120c0a0f06120c12 68
    0x20030180a20b9103000c106002c400003100014500501c0b01000240040c105003004001c0e54101d0700d41014440380034011415070b45e220b0b900c03010400300c40c8a00d00044e10300b0195540010ba1541c000a4460219035100c1180350040212011100c1440c030f01c4042280d05020444070741a06e5071182a08214501c401684a000b541c00a01032091880d03014107802200b150201d8840c0d404000002440000e0401016090040c10710b440c0000042c1400b140640c0c9920748808501e1050340d2101e40826605060b0b13101c21a01b10a06031082d40031542d524215031524003c41e02941c00d4060540009040a07000d410061007580c0340e0b84001c21660f0280403c2015000aa292810480094000320301d01040f4860907002d54122402400d107103180d4a00484907060340840580284614003004004034648081082000030441d402d00e10088960b0800d85088004103640d5401a2071000020707240c85265040c20980344107546141c181e201c8003804009031152020314800040a203022005849642e501c40b400324 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 380184721 1250 380183471 380183497
    0x9010804020d1407030614060405100501120209120a0b07052505031603030e12090604140d08030c0d0b030f0a1104060e09031803070608072102070516090603021302 72
    0x3c900e000050030301c1c014858000f141d0300c0c0c1d542c000b00d40e050006801f015500c0241120148242e2030041900321f0030507090b101d503030f05201d9516000352104050390143c076030141004d4030482441c95181030703451342c4000d84a401c1d00c0d40920031020032010340c07042c422500f29020840101c0c0d801d820500c1e40e041c1000c03001405440c540024003003c0c41c031340510f400400ba5140269008140344141a240505000300000c041100f0704040040d4401610342500344d5049030115240e201418850502041d18804005401800300d4000000c1041d91481f00d009441d2040d02010204104034040f414165142419241c0c4001c0d6805009004005001500d1000e010328000e07001041079941c0701900850104252403541c40c0c0d070004611291541540b50308103900c11401ca0040001c50b1500c0da0143c5803440242c0b5181c2008002611880844a580040200078050b00c10443d41d445160415545400d0613007140e134858a2040780002e0080210b00402041c0c0f90024a00030790b0400d4000d00717400071360140341c003c456 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 380185971 1250 380184721 380184743
    0xf0305040b030a050405071d15040e0d0201060e0c030c090907110a06061805070801140402090612060111030901020705040e0c1f02010c020d09050118050910051509010804020d 77
    0x702088020155004190f0808013240c3c50030140f0b00581404040d0704418040308444d10400400240d40c030100350400241000c91a040c88070b9400b0601515229445140d944030300d0342c2803411184c3c150302c000200c5003031058580568440250591451000751070050001005004e615554500115001d81006aa00300080320060b11300c4201d04080008a068a9041c3c0d00d403805c004400c3d106003d5503800040304020041c07460510303005080c0400c10301882080ba14102c0e02d1401c2500c46504585960130010910350b140d0b400702420380c0c407400085420a000840290700b00c0610800007058039003006d016000f0b003600310304180030300009010442c2c001055209240550400347c031442c21010001c5e6000202c00384501141d040a8250745e0560041e0003158002d20204483c80e51000102050350024a44405803481d50120959000440e07048160700108a000b070107500c80c841c0e004503044640580c1c580c07402c450300301c040d2005401220780c9207000c2100c1c1c0000400525001411202e514419041102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 380187221 1250 380185971 380185979
    0xe031c030f060e1e0c0304021c030224060111011a0121020706021918030f03050c1e0106050307030803011a0d02220e2a0405060d09060e15040f030504 66
    0x1101d07103000d84c4d10401c07103682540100c0c04c3e0b1000780d00d00313580071041e20039aa141d400c0941c081403468607100028040824800790100425100380810100b08408550000d2000b051075000000c901003a04c5c42804a80402100303000301506005084171079240c403060240c1400d64000668031308400d0120540c101f5100d0310201185c08048c4007401d44207000e80c07401604d800d0b40e0b070300d140f0880002d520380600340305807080303029000c0207008203800036640d01101800302080189810346480c0920400010030f4001c80242d1481004000d409140318621000203000c110380d9042072540702d045601014044510030030040c800d01da120400c3c6c091b0018011100c42c5413003204d0b59100f08a8000d0301400828040c0c2c8000d80b03504030103403039004010300f80120303002040303083c030381d4001c42481000b951410070903c041103900c280c04d071410180c030b0040001070241d0b603031079181d8503201000300705800c011190320f45007080d0000c5002c00080c0056018031001c0c4900d125440c1e580300c100b11030b8074604046040220400002c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 380188471 1250 380187221 380187239
    0x2102010e030f0d05010e04050706140c06280207110904050708071401030510060813031209030203040e0a020c030304080c01060b0714100b060904050a0603210e031c030f06 75
    0x101000c0b2000140540b00c004005080d800c0c0d90040c2d103d4482c204d0950700f40804200085461000c0741c503d42800b8170001040d83c282c00607409100c000800f01e005a40800140994011244050381c0340321203e00400820142c07194201d00903001c028113038806040c03008901c1d0030142410764005d801102260b4140341e03a41442860540303140c01091010008c482c1242e81941c05015032604440c90b442c05011990034a900140050001018079480d484415190001e00d4003529541d2440d10b01403400703000380d00709424003070b60744c0d400352080021400c00c50000030126880c5101359816802030201035413854585440c1d070032641d0444106110070b9540da041c009602042480148022845120440c5200500c0040182440d850480b68900c40742410344402c00c9541c2d0504a07450103000315000543d60f10b501c0c10000040a003600024400c140d030b18518180c020015240840705030a554802140941410a00d41c89591440075030318100d01134070170000b07228002d170012810800080d60005005da559540c1c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 380189721 1250 380188471 380188477
    0x20315011e080c130207031403092506020606012001140910090c050d0503070507031a010f05010c060905011b23070209040f050a060c050405040c0206042102010e03 72
    0x140308588115005980061109020a00501d048000341100b0f00e820404104001c5003c44081e40a071341c000f4400003018002c2ca4240d01e0800e40300034150f141d00c9d04100c03156403034141250304004049030b0310f5408040700701ca5132103100f41c506581c0a413105803114401590410280d08005005000d05a40c00e84044800d214231404090768110042080c01c2c14101c540c1006100c9010390034243c20118004003145c0d9800c1001304449054400000ca4007650500c1030950060b40c2c801402c50283c01000070901a441c0a00801014091400400359030b80d503854a44a0140d8420280818510049103012075140c0d44260a01401341e1b001161308002c680c417038000800b00e0f01807480881d843c0c051412030780b82030540c0001410500200f0500e002c03510f40001e11000d00044c00140141c5c1744038034030020003009124001201f6409a410300850080708805045030b0003900440e03024524002184098900c0001c0c003901858000c0c08041c01508042c0500344800d01c080428000c3d0341d00c8180b0940b48010800c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 380190971 1250 380189721 380189729
    0x80c060f250c091a0f12060a14012111010915020708011a061602030a050a0b0a14060d02040507090b040605071101050f0d09030c080f090f060c0c010c02031501 70
    0x10300d681d01610b4502040600141d800030040e680c505492400c080054401d0a14060001c4074100004081d0800181d038038404401145d07001e0080340144180d2103415040200d01040d2290b080c201603803154400da415060391303103481c00c000c580c0c40d8400c804030f92044480b1454100614001001c0b546070000c45900e00448040840140c1c00a03004110081003031103a0b12145815621505ca00d110b0b120000e1500e000d0442100231468400700188119a0300300444080154000207641111031035081c43e01121600300d582403c45400c0513800400c00341400340483c89254020800844a445a02400000d2a00910310824040707461004076640032001d0150000301041c3e680c8a554000610302440d240c182d000c0d40390305221080c081c408800000409444215501540003d0710042c18102122a0045e070400604030305400a16a02442e040c000103040c600b03c25580c5c2405290441c0c240121846031a10b9069a03410504542c2203641c404c1c10a04c0c80c0714001000c44504454010303060f26000d07402e1344 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 380192221 1250 380190971 380191027
    0xa05070b0414100204080a08094c080c0d14010b0703020c090c19020c1c020414271e060106080c03060d0b06042a0216080c060f 56
    0x250030320500a040204542403c03d602040d410030f4509989580d40d400c072520020010000440c0c040c0c011f84404c40c1403030394640349241c0380b02c490408591400d48000c0881950744004101d0740003020400600c813000f0104030316030340c4119041e80c8403030301c0306055001061010000343e00c42095942c407403072000c58940a482c51034245a0b85452070720300a840d040500c00218010321000c001c0000c030700c0c0c003403055030303c01d83c1040e41804449291000490900c0302550616600050300c251006940c088901d01000313180c800da908028500100c68942619102110b0119885146c0c51140c003030000080143c0c00401003003000c0307503007190307184400c02c1e210b0030090441d04040e440f460041168550010540d504070960507866403950800101185040da45000c004d40249038030804100161030341e030712a0450310400060650421406004c10300c94400451201d4010320500c07040034a0040d9000c825401c45000f00000d00007031298400b48841608021061340903582d003031040040d000c140c1341241600070000c107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 380193471 1250 380192221 380192243
    0x5040c06031d0a030804031701120201260c090402070605010902031b21040c08031201030b0106020c0a0306050c040b0403051501140303070b040203030c07030b0a0b010c08030c0a05070b04 82
    0x2600404449821040c0d070b8140d1450103000140400100e81c4942054052600e00307030b29643e40c1401c0c1c901070030310790041043d03201040001581080600306c3e00007145c0300741c2c0c80400511a0704c4d00c90042070141500b07190824460004501c0c00103021000f482202e101034405401c2018944420045407000d03800381c000780f034000041003950391b03102c0e12500294280035192410718a000c440d00d640703d0402c41c0d1209400902c40c000c81e0500818070200001042d01804584d038038145540e020b6011380d000e102c100c030510100000807030f4050002c80d0980e400c800107080c03644248c1c42e50301c45801515000d048501c00e21420040071940c104010005c1018502600051011350301001c1c000c182000168040700c480001c0c40e80612840d81c0c040100d46105030045001581900e031800000d0441c0f2443c0c01c050300d80d20464a00104101e6030b03501403846100c12500c10044c0e281401e006403440300d1012001000300b80100005401e910800000e0001802030b45040d40c00d00311075a55540e003408090701c007624158402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 380194721 1250 380193471 380193479
    0xd2a052409070f0b120a090c12050d0e300106030c080613020d0b07030605030d030c02061509160905040f0e010515031c030209060435030415050c0105040c 68
    0x208004030003403c080b100c9400c110302d0320300c809485000c1d042c0c03006545076400c0045980d010313403a048288500d4201540001d5599075001d406e051040d6140203c91602902ea20301c401c8ea03005040006411502030300090010303035140032907446591180911480c1890280b001f0342901d00900c5098040e5104094004095003051030003072508074002c0c0703007520216141401e2001a100c02e98011141c95002d510f61a15484c1e0940580c00340c90300f9044190184502c226688401d07501d5000600034008580a41380d19803210031b141c00c0c10200d50b054594000708110b0100e11a041d80721403100c2c8100325864486070403521040014107032520300311440c9607287c03141341e4200007a900f8424180c0014208442120002c0303031801181d100c0e1030080380d910300c0c221130f60200000c580c000e404940e40494000c102581e03c3c1e485114085c4c1c45d100044201c540e500d00c0c1e00084c105070742849a00840c49003c2c034000c504062170406100424000100c101003008000e11180901000034005e40380550304c02d01c070b141d1905d424 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 380195971 1250 380194721 380194723
    0x30b01170f2a0a030e0307020d0c0f09051b070c0b030405100e060601090b1e030907031a04030503010504050403140a030614010906050301150c020307030501020a020d2a052409 77
    0x100480820b61020721103010858510114200d030800042801d002c01d038562440d07036050550190020180d040b2507042590f0307003005403819107031050b82d90000140008503202c1807444220b880840f014080300d503444241410311a6148040c01d10705100d2410101120340312940034aa5400544040f199607105580c01d000d541d1090040d440300e551807000902c05460a40c0008201400d148036200c989500050f003000d480084201d608840412840219500d04204c2d000a46d55400e9101c1511800e0b608440e0700009190a80624019905030781c0301c5043d6401c00d0200801020050400c40500800f01034810703443d2202000345c81540c81035200081c8061400b14101c0300103046000f254100440c44e40b0500400f5000016203044d1418251041803c21a040d0f0543c1d401401c00d00107907140c0b00b02c40000041090540090041010b140d00361804803500d8003080e00c040503d91103400443c02c10445d68401c8000b04d4200210342e50103802114000b4407620404a220801c8180c040c01361440107040254801c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 380197221 1250 380195971 380196001
    0x40312021009110d030516050f07120b150301020405040e0102070317361f0605040204050d0201080613020327030c060105011101021c06180e0d030b01170f 68
    0x10180001d100307a004542c2c8030003c086000d4031070361044210b0140b0344240340c070483c26102c10340e90b00d00010f8000b524070f003401a6641806d525480e040e10801034081400e000601c000c082507540170840100646907030a2036207601201c5d207082034040d9401d000009690707485000340660a0603120006a591030542001440d0300301c440c91101c0040102024418207480d1070202500469080501c40e0405154060b4641080205412880144500682041d06000d10000c0200b40c0e4040f0000700000d5541d0001e10081e801a44102d950040e510451a000355001e4100b02e40d01540040180500180300c4400e070341240c005890495400b50400074541040e01805002c040700d030301c2180154108403164940c10351f288414046c0c58100700386440c280c44101003d4050300c045c0130038190003200c0c00b40c240c160400203048502c01c6103c060084140e002d41908103110342c0307428088a801030600d0008400c0d0550151000108107410842d4003000e42074041f442542e0140591000310503032180b070912540c8603103114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 380198471 1250 380197221 380197243
    0x322050405060307081002180d140601090c02100b041509150806090604030f050d020a050d1a010e1905030102041418090a02210f0d0306090b0102060402150f04031202 73
    0x360104d04140714040d00080ea100200a208501599458012280d0740002c0900c822080c0c020981c036503448100400007001c002411510701c00c540c11603a9a0b21924192074800b01c1400258202520941241960341c200011107800500046030350b500703031101c152111000f40e015a040350b903642c0c2c40020081c40841d00c08014618074000700b41900b011180c203621084080e1000303060181d92a074003203009008006407010050302da0301c11500d40e142440702a1003071b4442c0f218041c6072807404172016803400141e80e055150700810795903420b00034407100600096100710b82894001c80c0d0210741c00222039409000410142580741c088640c000d03c44410310203d5040c2c2d4007070014881c001420010041c000091211038150120b5051420000c000e16108c03480e103803400c1551050007560601040039000042d8036500711480d50302002034540c0c03606c51008440880100e540160040008100036282550b040c0c1d08550700038039110300d016040d03201d24283d64043d62080b9282d900c440d80028499805008816141d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 380199721 1250 380198471 380198473
    0xc08010602120f1614062205250f090609140105150f09060313030215191a060705100b0603010513050a060512030d110a1b030203220504050603 63
    0x1608600d0701c0d002d601d00030415a4007034a54041a40034106094203021a011500324500f08842d0f00c003456401d4440500f2103041b0020403566402010000002205100558000c0003605400801720310441c1e00c4c02105c038a031050050909000304104a4500640c80241410040011020720713120010782a50200000a1107901f8044010042512051503000c101610203c00c144c1c1c0e4800e00050032618040c00038000e4000601004100000c0005400309882ca8029001c44115500b900a100c40e055011070304881415030903403c99103280752540003055040d501c0b00c002c600d503041001c00f00306c071500030f400180c5d22540300c282d1000d06007401d4400c003040d25a040e680a0b1542d810b02010032640f03104035104001c43c6948000140140d07070580e00240160000915401007003d0810905030b803030b0800c2d00b0270325600e45451050282c44003420111081184281c0780d99015800b40380c86000d404a040c00180d0950000308a03006141e40711424404044a10304901e05003a41080140411a10000c0c0081d020b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 380200971 1250 380199721 380199733
    0x2010b060a0c15110d0b120f0d030917030903190207030206091509090c0a0e03010213050d050a0c0e07090803031302042c010b010305060d0f0b10180c08010602 70
    0x601e9801600144a950490824800c00c0c00342c1081c0740040040310460700002002080c3e031080040541c104204c10401220140701a801941480d034a1301035480820040d40d000c4114600c00398001d40108480324014100283d00c425586d00340c0da181d0b4800c60317180000f60800904640880e0214180b40844402031005140e02030469000c12194403800480d0352203002030050b100d804540c0b01c400c66801890240c04281141040c0409071802c1d0070000350032000c0f55402b81c03080c0c40e608051007551001040100303888031035840c041c140800d61071101030660b81401002e400d040400c84402200c40201981041c5a240b89414000107048070700ca50001d2290ba00f00700706010310703d04140300c6c1c4601c1a40464000500c12001c0d40d80b00c00342d50034803464040b042c00a240d15a2528019408015a00e4080c6c8003440f0680e120400c010300342c03280407401094461034080140c00310709400c0d021a070028110001c00e11454032005007070342000c400031031b003184140c0310155102440d50140e24240104600d00007407807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 380202221 1250 380200971 380200987
    0xf061d0916180b0f13091104090503070f050a02090906060a05040911010e01030e0f2b051801050d110306030d0806280b1c05070203310312020a0302010b06 68
    0x201490114034820b8142c1c46100c54101c0307551301842e01e6490000180140c01e0700303a080710341d04050304000038252082d480c100c070b603034107a400c1074000c840305130703a010002d10324060b0143d90714036281210070400d64407445004032843c01a191541c00c0360203048190024040351030b1800c100000b481d1550807007402103043c00110800030360540110100d100302424480381f40301540c0e004030014180c2000400051203428450800600f0100307a000180c08503180913520364403082022507131484052405800241304011144c400a1a05480500020145030843c40c100c441d00010082d00d0400c80e440c1c80c03561000007480070501e41004441d5080d48181802002c0d490b00400050618186002e442c40d8002042e149410440e10b032004800640041315000d0b41342c084200b2441400d1450b44070728946c061901700802c130442d0000090710607071503503c210702d101ca0190500051103083ca02103000001c1840d84000300009012803001e213641c030b50f15030041501c40844d0900a0a44200700b806900541d03007001182 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 380203471 1250 380202221 380202239
    0x7060b040218010e0d05160806060f01020601060c14060f09010c0206070e010c0f0615030311030301150c210509030d0903020a090e030d05132a05040f061d0916 70
    0x19100b41d4003420300084000d454008030b9000d0310a0b0000921034010304440f103400320241c102150075105040100c40b142d558050a0000f054412030f202c0303000d641703c0c030010041a0f12480c840c0080ca407041440c40d410300202d0a00e0351400d641a0b0b100c01014010000b00640240d003442010b40880d2540f006290718280041c01034030b40031070b101c020780c1004071000301a014481071003a618540340c0e00080810480c8030750340c00c2192007256800124002032414890f104a1400002542c2c10b958010302e400051101050054440c1001c3c003400f21180c1c0d5401c101c2003508610b0b9194a50f0500d0b4603150380ba03640e074411003010f04203200c0800072010700c001035a0600c096181d04110f0001d440141c5000100624908112450742c003901c2c6104543c2420001084601d03409911484030f5184a85480071154900300001c0c0e0a0031114130344402a14440e0004003c14540744d0407001c0b20b2135082c10f00143c1c0c0b1783c4035044280250b20300070328a046c10025209020144404200d5444e58000888403040001d040207207070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 380204721 1250 380203471 380203507
    0x24090402090603122205090106021c0c02040c0c0204060807031a09010612050d030c0302040b0904110c1209090601080402030a080d1b110114010b091c1707060b0402 72
    0x20340038206200c00961140c4080080b04625a94101c511303442e85c0455aa050590b55002d48107656840d1150001600342030401c0514148d03009600509101100c0080d6070b0781c0300100c101c1410400c10400110310240c0c070345203e4441d0412240d91401c0c500d05a80c01032000340c945c1e95111080c10782c05094100042074040b0b04072085500c817070848081a0f03d91115850141007650046940850020840400c1000c0000d0b041ca420000b44c90500032009031840c00c1c1c049000e03520544041200070012034605d490f1540c04030f00740e5507400118508001c409a000c42c90300498004d2955101c40c0041c0300b141c2d5250810081c0c4d8440d200b446c02c0c032240d20700341d03020030380350401002c008158800c04101c403170315504507410900300c1a500140e0004a282c85400082c41d4460803035841156510380031040303002d81040080103040e6600d1481c80d0349020005c009224030066800020240045800360000008411101d0b101681080c052016180c0d8610f0600038111898544641d00c01c610400654400d601d21101e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 380205971 1250 380204721 380204723
    0x5030f090d0f0810050a1805060307030c0303050703090e0703020405031b030c06070c120f140f0309152503080a060e06060304050c09070503100f0e0f060d08070b240904 74
    0xc200f249448503211000b151074141c03c0241e1208009070042a020703592514440c01c03060440b000d121350303100c4400b816294034050002401c2c4044050007840840d001e40002d0100c1846454042c1955588650012110708280c80035030000ba0006020415031030100321800000b400e51490f80e050f10b0507840083e0356400075102d2030340505804076400040c00490400b1b43c00411040401c0300041d00245401c50301c1c070454403003c6405a2310005051400305001942441c552004402917250140c01410001a41c070a01c00b100340840080040c243c1c1001041500c600c0c654ac024401440e00c800c5143c00f80a60f000108441602482c141c0d00b0814004100c03021030300207000391045941d0f40c5440c10405d0a0031030717101e041600841c440052200007075124009600c42d026007104846071580b101f0014081e904c4500c15840003042c80d0012503006200500c0d5a03801a000074a004c0c00782c00d032035071000c01d83e8100c1c03841070324060401ca04004031810304000b66403c0d4001071456001c850034240000baa44040030380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 380207221 1250 380205971 380205977
    0x260705011107030812010f170d0806030109050703150c080f0a09030e060315040c050703120506031513120f122f0c150708070c030c06060605030f090d0f 67
    0x21800310801d41c184000009507400c08245607550b4003820f42264120340a103d0b04040001200000691075500d07925841c1d100d4405c00607010907017900208230b918020151510b07a05559450320b100001d0404c104000082d8030071800c075008154031001e0380d01241d002a007003402344444003040081d403c60403201603600501e1020005440300b0f5900b01101c1034a029500c0d603810003c00000d00c0800510990036126000c4225403d005402c11740600310350602540400501043e15001d00603106103d0b5040701c1c0d4860005011070f84449420742100024030015200c42c5100c801d00300a9000b404100e0340490303107082c2c4509104110700440d4900030001507140203400c2c2032565440c41008000c0b40d0a03e01100c00305044000082c0360280301008155601180300800240301e540fa40f034407036100d103010441c031514443d2150380030340d5190142030701d40b550100b1045082001c10805c0000161251090402401450703642d20784ce481c111039000c42e0050050030740d4146502c00404450403603440b504410601a00e85 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 380208471 1250 380207221 380207237
    0x23010206070807020109120201050a0606030b060a080901090c06050d05060f0d02041e0c091701060605090d0303022503200d20120304021302040312050a050903010c02010626070501 79
    0x503c04030b00400c000d2034000c205245440050384010781c150403990007090310700320400000780c2d91407042d8100d0b80904c1606030000000d0101004003401805041c1c1d200c018140041941040c82d580d00241000c04d41200e008a2008101601c810129114580c2d01147c03c0e5400446041342c41c2c0012000078090000034800c46d1034a84490408258602c1d901d0070043e844418401d40301c024501404094482c05202280543c0c285208503130340b414042d4104031034180c0c13280c5240038500f0003070007401600d100003981816001c125848001c1c44400300d03203803c080b80c20740b2000069140d01c3e00901c0c441c045002d072007030b03482060020a1082c4000c03c401ca07a914080c1014090f41100780c14800501002204008140c081c003200c0c1c2c25020402d00065200b5031081f01c0e19007541d41341d80001da00324040d90101510485030320101c40541c2d8010350003801415030a04107142041e100300000b900b0f40d030048041d040180d448440030071000644071820010f6154400701055240310a0160b503580d00c102d880b43d036040150701 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 380209721 1250 380208471 380208481
    0x140d02030f0f1f020f0f0906040f031a0f091e0a0b01030506010303020111190507021305090a33050c1b0304060207140913080f0a0207230102060708 65
    0x400c040700820921409440c00d800121100d03584610000c2c55a04912400036800032101105200b2180e210000400b81405d04d034003c05402000c3d006021000c1d00041c0030840460b6025074000c811006610a003000d9014100d400320041c0681c1000d06082041e9244c0828495103c03404a03c4e40009009504100040c10440902a1400c1445074028180380b001000120031306c80c0c04940d10781a00c0c041c0d0001e0285928607900305c10184a0700d020f00c0c0b42c543c060212901c01d1449607000349083c1c2d000800320307c0000c034428003d404850041c1c400a0280d40300200d550100a0f8641c12a003040c0c1e5214070b8071400340240c00007008000340d82035074011526610000a81e404403602c2c00d5030800f42e00006e04400441540c40125541d61040c024800503105810002500100305541a00c0f0300d000507080124546800d07041d500f611001c3c0310101e41810040c41020003c4a001c0094007014a5950091107920300d4410a400301400d410b640701d001d4142070041e4100d40c3d80014017103030054600d00d0503a24582e60 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 380210971 1250 380209721 380209723
    0x902060904240f06080403120b100c02040b010813020f0d0f081809061f1116060e180c0c030f072d05070603020a09090c02060f01080601140d0203 64
    0x10030214507031240c5010400400b00c0c0d01d814004a401c1060b86841c2c0303169803202d0802d007008400340702d01e0000511040000c0c0c0022301c510003220000c0c07005c04008c0360801c41040041c03007074240400c4d8940040c000c0d5a41c00c06500d842c0c0a0006002d00030b082072489411b1948180030560444840a4050340840850130070580302c28121f2069250007140d42d502d074014a02c0c00c001c0c0d0341d00c9020a10386a03413407480405214507210b04442d0182800400d038410071040c6000141040c0045076140c1e090280b01002240102404d01003100d82c860030400c016441420020040c0c030080245031011300407191400d09400c5400354080c2685c12035140b401c45920781c410b0025080c914410300c0b4522810001c08962481044412808041002042103407049600054045011044c2908001070320341da209030b40800085000c0d42c0100783d1240d0a00d000416191100c14040c25211031200000059100508100220300b00036041ca02602c2007102600c525490301c14031005200700340b90294407461440f0805011036034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 380212221 1250 380210971 380210977
    0xf070507090b03062508090a140f0106060915050c0a06020d05160201020c1506010908070f0f050303041d070302070b0f0106020609030705120c072706050105030c0a03090206 76
    0x5806400c580040c0d44074421880500407994101d4003a115600115402910b8140203854860000310b4007000c4c004005012160114040c1c0819154042d100c01c20003c194500c6c48102038141545c000e2140801240c0c2c61800c5031843d40c40001004100001440b6840ba00401d8405a4200d880c040c0d4079401091819810301254000090074588000f0711101281100c2e009640720300c40001d1031000c41c41ca0f80300203034282c3c402c403400749120341c121450302550b45660a6500303401800614015541e1600e80d9501e03490002c81c0e0700006800030401408025901d100302d2000b0213000107a010394205441d201c0c11502070184400c0c0ca801070500040011703d030070301c258113680b003051700300714040c0e81d506142d071610410100a00840c0c005004280000c0e10b103901c00401c41f80d1550740305005100041308481150b902c3d401042900c18103024441000901c44c24400e940a02c040c0d01009140280d007842c64032104407100341c1e11290602c402030040024030343c80f000545404418504010964101920000b44c080c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 380213471 1250 380212221 380212223
    0x5030c0f09072f07060806131a03030706020421080a030209010c02102115060302070f020301140708070c1e0203010f0507020a0303060f03020603160221070b0a0b090703020f07 77
    0x49000c0b80c0f14081c0b0000012240d12680c548070503140e07990344031303081140d03916011560540c1001c0704200c019140700c0c0e1135001d001c00303200049400000310f820300d002030305550103044107403000b5801003020f00c00c1410222240441c0c01043c854106a0449a5503008850048601d101d081c55070224464101d079024180034014103500030000300340d0070180907000e0300e811600902850880c9803159211840f0285c1d00c03134480704040107910410710030300e00301d0110080c0d07000c808226000065903016a005031001d00600c100012a200c030f00a0918140c5802440c0000052058041100c90441c40000c10441c03159841000c14840b811203000b042400801d0151004082e0201554a49010055620750110710b0360803142c480c0c0d6050100c980d0f102e02e410703000784ca0b5020181d80b001007040401c0c0c14050101c0c0b08410102c503801694900382440002d018036800c403512810011100007000c20030011500d42040d80954141300030044d032400000802e14800008116506140e030008010300d02070f908a040d10707115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 380214721 1250 380213471 380213507
    0xf160c0f0b07030b041a04020d060b030c0c100b0906040e0a052a010302090906010c0218010306061805070801060e0105121302030f031204060911041802010905030c0f0907 75
    0x1445910708a0801c8100710361003000039142100f00c0019117490300076084c400182d0510f400200d0084400c00000394080103480b24403a5a41d0400100e01101d04040d501c00c400c0740c0d01c3d40744c03107030340da801484d08000038002e200d170500380f5110f1800341c580d0710649100d80000060301c00090a08001c41000c0c82d2054003800540180f04030300c0305010410520284900302261a600c2c5040c00d4000c00064043e4000e50384c0c850b9120083c0400105294803501801c0d44450004142c2c3c01c5001060301825040304081e003080e603641e51110410310003441052016503080c0d04819042041e4078285000808084041c050542080602807055200d03a1103a01656103515030b00750b0302c0d00e07641030400022400c819030f108224024000c0fa05520310000703005c0151001c21110002400380c1d590399903a11001031141c2c5c0d0080340ca1510b414481d1034261a14440d981601e1034160b089403001c001800058003848055009511a40c40035642007041d4584402803803008200341c900b64103d886000c07069400001c419078503015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 380215827 1106 380214721 380214743
    0xe030f1c140a030501050a050a0b0714010e0304060206090708062403010f06030b0f0a0e190c12080a0f021506120109080301060e040f050f160c 63
    0x40300918103030741c0660846034841c10350b4010109500000759200014000c2e41400d00b6040c1c00b07424201c61452400d4a4070a207000e292082d181c7c0208007102d10b03521200d19905c25009800c9420541c810749403241e440b03010003566184100c48a41e9079118489000800384004505103005170900300001400300c120681e03040c2c08101484142d40c0541da0f50004016501c018843c0f28095486840344035802e01301070b10000ca00e418040c103c0c1340c003145080c1c010051824002440050000c0300e08054111104c10704000c0a140795642c810081d0841601742c1c0c0e820008400020401c00140d6244c0301051a403545049982d032040f00500b014000c0380f2004030340540780000c507556049410301d0010079041d905550380701c181e0f0003c2c0d0040b000304d400708989010f07601c0cac03034090345400c5059001c040009103440310360482c0060000d03015180d5025200c200d1040131b44904940c1c1c500710740100d00040 = true := by decide +kernel

theorem cover : BRFrame.Cov 380035971 380215827 := by
  have h0 := BRFrame.cov_init 380035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 380035971 ≤ n) (h2 : n < 380215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
