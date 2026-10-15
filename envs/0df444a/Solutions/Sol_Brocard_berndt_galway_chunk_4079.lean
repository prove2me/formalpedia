-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:28.579351+00:00
-- url     : https://prove2.me/submissions/cdc3ca1a-94ab-4415-82fd-adb550c26da1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 733453237 ≤ n < 733633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 733454487 1250 733453237 733453247
    0x90d0f0210020315031204032f061206040c0e2b080307082410140c03120f18120f090d03050c0c0f0a031407051c0b010506040510050a 59
    0x4240991840d101000300814880314000c00d213030142048081c1c2c2e11005070840c0d0003c003401140809003100541d0440d081042d43c0120700c0d001c1c089103080700c0d40014030b00180010899404903800c00c4101040304d003408880d0030140900000c0f4800d50410070501d88030000420035040700785e561100d840c401d40080e515150340070324030000711941085002d9505d10700180302070507400c3d06031010748207000900441c41031410900e00200350040f006000c1100c0c8085203800300c0f251403510342150f421880410135034103014800c00042884c410143c0c5500302502d040310403041003c900400031302d0700104156801340b5003500400e09004442c001602552100c0065840369030a02488040c150812001045001850307001405010760305800c8049907080003801083c40000d180c880402030b0000f201e158241700041070340101d4174103007010004a8402d0303582d550018215601c1503441c0007002802c251810240240c46007824050078068800394981450040810500031820801204101c00454005402d074070035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 733455737 1250 733454487 733454503
    0x82b0e0c15070b16082406030403140c0c090906040201050901050f122e0b0d09021201090305030402120307080d180203070b0d24030b070215010806040b0708090d0f02 73
    0x100a03c50001c3c64610141074256803030224600204100710005021498030750380840c08460ba0301442a08102c10405000c00b50708081d00031028000c040300140940043d80025042076441c0ca0300034080c3c14070701e0045c082038080140001d640b40d04002c04000150340c10000b1640045002c0c030f4082e54609074413021500a008500e203c000178406801441001845401c586461040b1074030302c1d0340e4001c00a80228101030a500c504a081c0c00148001031944625500002000d8005044201c01e60103044080d4219442104201c000c908040140429402d0411100790161443d00c02586040220f884403d001d0181d05407040050361100b154610300e043c030807440c05a642d4058100c0b42200d844180d403100c0c80d00202c0c0d60f0054030703240c040d108100103030800311100c4000200d400780300c070a821078441d10725402e0024002001e44c0711386020a0b0369410140c0c90b0724001c10404028200301e0410307107002e00c480071000e0040d10030040c2d038505016220728003140c03007866032009007081d4000c1d58864109a0400b045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 733456987 1250 733455737 733455743
    0x3190e1207020d08042601181b031e11090f0109020702180a14100b1603031d0706030c030c05181c030206160c050a08030a09082b0e0c1507 61
    0x200e0001b50034142e40c0c14081d9150f02204214840c1b8259200440c02c032241d078009100c0e2000780540c4c1c440451101c0b0840101040480602c0c0c840c60f03100e494017a01c0f8001400c25840050703003104014203104031403031000800007080b0703001541c0b410904403074042c80c10107015000c040380d0300282a031b0840d0340310542c0451001c42a5449229850001026402010f201d400d00042c9421000010745a4180400303450507121440c402da400c101600e1701840000c00702440c21824155101c4140c2100d4800003038214040c1007141c000e01c0054104040181130303600b10b06e0720710309060074203080c0c880042d00141039a000b040034421824980d140c18000421350500820b00050040a544882052542c042a84c5100d076012580310046900d460108449031540001d01a00c2600314103001400100c001c0010360b0008007598001ca40070807135403a000b841c2c0e4850111001440010000146101d4540c9080d020b010b034190810450841e540001c0c3d911136248c8458a4803405022200c0003400d4106001e40e4017113a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 733458237 1250 733456987 733457003
    0xa0f1202040e090a0614060a060302030603071212030c030204140d0203072d050307050d081e0a0c050c03210705010906090503040f150912020315090303190e1207020d 73
    0x10880301c3c0c19100d601d14401a00e0359400d020581c0d1171541b40c1103080380280360141c210039149160030b038214003d410150805c4d40c180174035200003032120b201c01c42240006000358101d43e1000d1520501808456281c40888141401032004100c0040e0740440c100e0042000d607605070500c501c0f0b10000c0e003881c40c140c01580c0b90030340760780f81c070a05002c40b904900084001c816010000315111400c0641d520000c1c400c1c83e82c4202e030541f4140000d92035030701411818040e8800c03034080c4000002241c0464119100754000140c107804030b013003030202c100304c82c26215109038050900703107031005140308600c0303562071180b098a440014101c0402009501105607d6003011041041d10f0701c9190054580d4014800e12842c1038020101043c90f002041382a01070f100c0e652101c03451f1070b2510700744121003900d000b4280c3e403500805a168204802d00c1b00494031034910980919641d2400c00040d1210000b092804400b1030302d480301441d46204000f50b0030348006c50030a030783d640b2598144009003d02c900c810000f0700d140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 733459487 1250 733458237 733458241
    0x50105090304060905030a0b060d0f0c0311010f0309151a0a080706080618040210030b03100606030c0e18100312080105010e011704020d02060904090f02150a0f1202040e 74
    0x42000300160043c1d560341d980f0b8004a565840800d590744812000c09002212404041840e07450310030101c00c0c4c6c29101e20410b8040c07042940b03503d0f00c200e22540c001e807801c0c0c19407030408d102ca60340180000029121400e08000704080c0e500ca400c0700352a00e00300703e48116501e4040000c4400f08028a4a052000030600c1c50440e448045890706c8030750511540c408207241c0030100d4813a1400b4070308000a50700c0d03080305808940c0c5c1c81c0c08101c051040210280e081c1a40c4045e00c400a49040c8001d42c074100c05040081007282c81c00c94020100e601e031041c50010401a0000314480f540c030010890a620002c000085840e01e07580741c00103107140c1079800207002c090040340d600907107034004017014121107090f00e402d0b512441c041d0056499601c102c141c030380501a02da000a0052810030f004041e214009019981411881c0d80071400719000454190789000541300c41c001149000342074031a45501d28880c3d207003040b90341c5501800105028900c0d8040c400c13450301e103209071516a81034800038402c07104045014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 733460737 1250 733459487 733459501
    0x6061908070b210f07032a0314180a080903070f0e01061101050c0d0504031403151f080106110c03011e0507030603020f100c0c06020f1009111309050105 67
    0x50703001c02e900c24002d81d81d05032045503038a10060711070322840012001031301c503541e9070900310014010009155a4480c441a0f50a0b403420320a5602c8000c090944000420340054040703c10441d2009001d10400c1039034041b40010300030302182031016698018410790f102c0803044000b0342000201d4114135422071981000150104480030f60703034101d034100e4440e400301206000105080c0c2c0c00071500e03184c292000b00304084022000b54801d5074000c1c040c1c54451251440800c003144c103644160340802c100b08000324002283d250008088115415400c038030442d200200384040c028100500c038003818800c24110020341044180100729015200400030041100c03501742110124800100e03990361649004d00180480340240f00d04411380e50010403000c4885110030801034851200c4441d0f40400c401c91468400040c40480c008003e004580c0191081a010b00181881d1100019415181c00e080181d07080201d003001c200e004180e64203032900400180c0c80903404001d0b240d0102c00505940ca4541003000f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 733461987 1250 733460737 733460759
    0x7030f1109040e061b09120f010902270c0309010212040c0f0e040209040f140604120f0f09030b0a0b030f1c05041508040602190804030801080304030c0e071103071a180606190807 78
    0x101510031202c0c80c2c00603509330740010740c90442c0401540301c1c4880c4404100000c0480c009141d00000782d10001d40350105800d0303007407d001c0003660100c51201c02040c05121100250340e1036000f818036030207140003d18040d00004c8440c2c4002d00007400410300360003c40b05015240891240c1c1891030301c00c442280c00c2c2807030300900c0740b1303841c46900000580c1c1003c0051007074442c1608402c4244699100700d030076400c580702e07901c9031100607011800312583d42c020f403040d6860510003015440302c44805010503000054120208500c040312030000c0290400c024003c0146405040700302843e0b500d0191a183c0c0c46160101c024842c81643d000070300d009445280381181c0c0942040c0c4074034800e41d11710b120b50f40d80c1c070388481d600d01450100a00007070540c4c00600035060043c022a81c800703501d02d0244500329000e41228290f0744025016a05a03410782d07041603104840822042e0498200d00d00c0c1030000300311600580e2241000f0b003465206284030341d00018019040282140a400d203402911078452b60f5802c42a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 733463237 1250 733461987 733462001
    0x170909060604050609040b1f02011e0605150a092102180c07060b0f0a0e01290316171006120204061707030f1109040e061b09120f01 58
    0x1104210800005450341000c40545040b5040603054a091012030380030032005c1c14808034003603000440c5032800e0b000c0c00b2000488111a05494000007001a04054070300384c01c00100100802c4581803190401444d11002a450413203101800c2e003a4030390811400844d12010703540d00550b03c403450510350011500c3d01d5440c41d01040e00c00ca9142d00341301440d144200c01c078a400c035441c0301c40c08dd0520800c004140d4039088089408801000c90110405d01c5000803c0144290003001011103020300501002141d608200303804801060b010400031603202c0b4511461100170094450100021a0301614a010300100c450218060083c0c40c45441c195a2080d80c86e0414031901c800a07011140c0980041c50a20031207050b20903555554694250140d50346445c150301070202e1040564441c1031449031201c80c41240c14584403442d2940d41d540e0200200010f0315038214800403035030000030a204030310383da5410020340c46800180b1551518216400aa25500e6105a507401d9018031a0302c1e0902c00b2040d84440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 733464487 1250 733463237 733463239
    0x40c03020912060f130305040e0f18120a0e1f03020a230d05060d0c0e2d15030a0501050108010b0a120803010506030a0b1008010e0703020a020a1e1709 66
    0x300400c4002c4502c994401041d80c00b03080400d40b0b40089480f0501c2c0444500360385029090581c41d05507100d808500090080b01c0c0b40c02804281000e000c2e069240141f0380c000d928418000b050701c2402030300c0800b0188612305140081c050780d020150f440c1c0c0c48100441ca8001540c0c03211007042c0c070b503003840034010798802210b081c002098603550f903c0710180caa940c5400840640c0840e81003088100b5610014140a04100e80c080c803000000320005080302c2962018090204060006040107403c9900400b07183c200c0041c0c80360030031401c00d00e002c070100145600c03140c40b80c0d03954005114032000c2820b00c400140c0140103942070500108504405420603200903c0030b64181d8030540d9500c80034550000d6200008010090810040140d0314090000e0354000c80d1502c000522440300c640007418007000340e04420080745040004100442204010942c00803403410194507050640304001c0d1100c680705c40081c07110b4602c90142e0802c0441031000b201c060b40c41b21107c011840040000003a5801c003030b00329 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 733465737 1250 733464487 733464499
    0x12070503120a0b1011120c070504180b0103050703031205160309170711091308162d05010506030c01140d0f2a050403030e130f0216060b0a050105070b070e040c030209 73
    0x1b81c601512148100c030884444003005c4d0203a01e04040421001d884001c124415010340f119141000c216407181d6280250301c21002010858954a4043c080c07440000c2c00300883c502d80f80401140d0200c3c41c40b000343d01e40f028a40010b40b01050b00d4003d50000b21f440540c030042d070000c01d802003000015281c0b0b0800e21021601c10001380d403040d00050b10f9441c2d2401c01070611006002c6050b0300c42995207122034080c41004080c4030400c1003102e80c020441101a41500c010b248014182884070030300ca00c507042001a00a8010b41a80c000083d014000140380c003c01e008002805410302d0105070301a0401200801003840040c009030202d02ca508081030203c07001e240184181c1e08242e024100711011a640740c1c480000b4400507004001c0804071040800c0750b03094440b4030707410007542603100428040f504040074501c041d9407410118202e4085001c031038007407140c0d403009103c103030780001c02d841800303602c412900215034503114100d9001909805aa8200b03040802c02c160740c940580251002c5003041e903807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 733466987 1250 733465737 733465753
    0xb0612011a120304030c1502070b160201030b1e0f0103020708120711012003090102070209090d030612050a0f14060906011d1b0c03040305030d060812070503120a0b1011 74
    0x100e0f100c0c4100d1000405030b00541004100b0505000040080301216006450f0742903940c580e8070560354046a40780350748981c010202c01c00c40d0780611030aa2882c0381511903030b021130982131903c054071078000f03501807240010201c100400c0c1c0c401e40445035143e078000da07801c0d142d89403908681d20b0b1410688800010a210b00302d032080c0014148560a00038210324040c00791102230703805520681e40082c051a40c0c0755000c22100002d81c0798010381c0d9005205010092614070280c802c01400c48010760010a2205102d5044901181e000100c2d1203102e900400183d400c03410030f00d48500804400e070303800c0c8068020394040101c00386011406034105c4041c40c0c52485610b6142180788620282240d01c604c0e21003081d0100c00c0840d078040d010303040d0980084110307440d050b2030342c403490300c1c5401c4030000c584d0780d64a0300803d0040c028140144e2a00e1102c00400074180010341e41d4941c1c480c010807002c2a1004048000541078528981040c010400c0140c4a0b01a0600324400280418060895500d4620a00360 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 733468237 1250 733466987 733467019
    0xf0d021312080702010309020a0305010c09150504080c0f0f120303060118031a2706100501050703050f030c121e090705060405040906021e0409060608070c0b0612011a 73
    0x620070905503401103816290107030ba64015002003880190998010340100d6001c0f000030824072920b1a05c00064031040e8005180040c2080011500d001e0070081110501c010440c500c5d000400000c081ea0440710a907d441040020911607201d10140a920144070724034050a008080025405520f00ba81c0d0002d04240506400c3c41c0c03040c42e41300c000c15040f00301c4429410102d4403011113400c01b0300c280c4000703005c02030401d4038015501c1a015400140e080300007444a03200320100309400900c0f0a0030041e04042d076646000d81140120f8408100d03401c00040001c10b0301402008403880e0028200da880702c5130504103049030141070404e00700203441d6180e03c0441d043c41400140f0310101d81c4028400c0c1c0c9010304000520010300b01030341c01164440c4d000e002c0180c3d4204400c1d00250319000404d070081d2030301d1400554506039525588103c09210b03000081c807886030fa10030340148849800c070440e80e40545640c4042200001e19004060595180900410a11591354010f40c00750700c0c02c0306c9204003110001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 733469487 1250 733468237 733468259
    0x90d05010c1e1b140f060a1a270c1201030f03031422020301020c070815070e090406020a050d0908040807080105090a06050603070e010303090603141006140f0d0213 72
    0x20307007040d990070010395400c00107103034022041413402c070940c1601c00d05110096240d01c0e1a1050780c00300100342e110300740f14400900b00900400030520441c0e001503415118010440400c1e0402c00200820440500186400390240e08545501c0c07000c03104940d6640c1c1d00c2c01d080c007a07135884900860001e810305100192038190741c0d41e4240150890050050001c046945984d031481441208a805540a0010910606051210300024003030b840241054540416903031980d12401040c03003051040054900c81692540301040b0f0380700b980110b005075a41c0b10f02000350341502030215058203990505044a00300051003014000700c80100088607030980d2203002c080d0a83c0c508440c075451a90115000c4008035a0940000d80c05c200e002d816a4912500c4200112240301e0980050700400d001d4034040142c241e161003440440c0b2480400900319052183c08038010407143d2042500304005070b5018081514448125040e601925491644d40c0702180d0f0b00e100030f90072042d8602c030008607155000a90021039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 733470737 1250 733469487 733469507
    0x6130b100f0c050709060611070e04080306040f050a0b01140a08190b0303030a0e0712121103040f14030c0d0209281103040b06060c030708090d05010c1e 67
    0x209150310900000c00d08580c07080009040350100044001520003084041c400c69020786050940403038003900f00040078000c0041817030521000d90014904010b80003031104020303045a8055441692034446c400020701509098038005440b0703150074184403000f0b54a500ca07002c851020b80341e401213030a501c2e580070381c80d026124206000c80d5030b58000412a11040d038040010143c11180060042e40f0900468603541084400880560f43e1320055070301c5210804c5804000d1030101c09215005040d59504060400d00d00c41140a00c400d07a2409002d521051042d00c01400308890440300c03403540c450029912043c4000c506009001f00014100380c0d003401e983d207071403d50700a05910000d4a03040890054034145001460009600302c1144030060003a00a801c940b0400441e26600c07406d00d814050301041c40035180d140303d0725003001211207581000c001d84405070f4100c003500ea1a07a10031741c0072443e242074204d0014002d5181044000509410010b889a0841c19601c0906184a03039039040c0e80300b1480c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 733471987 1250 733470737 733470739
    0x108041e02062104172b0e060408030a1a061b0f0d0e042a050705030c07030f120309050d05090d021207080f121b031b0c0111190605091f0506130b 64
    0x4044000707181c0419079001a0202030344d12400040007d0b00e0b2506609000058808032607500300041446a030781018024201c3d0116030224503840b110382040020385ca031054200000c2c01070148803122040c0c9038180030b9a80b40348218010341d81c0160750200002c1c03602d200156024410740c0740c150061400300c4440402c082a85410780740c0b0b041110010740581d055004544200e4261004024000940c402402054010751165034a280820308074070708a00380d0307000c036070090080518100007800030800016104800b0752031130402c5a540d13080728002c241c0740c000c0010080d4001d1400f81e0400e00c22080000c52000321248007007544c81130507030600c21a0f2213201088810000800c01d0000080b0721100d50324240d2028024000c407460042c408000c1c00d041d0a101c140081c1c20b4201a04038a071550308084100801c00c2c01381c014003201001e04850108000207544041c00980e034a0b00004c142650820100e8440303031000311012100700d50006110068041200c0c000d01031240c0c4515a00e164005001d0b820020714 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 733473237 1250 733471987 733472017
    0x1d04050a0201051303210e10091802070609050c010e190b0f040e0a09060e210f0903030d1a1c111c110f0108041e0206210417 55
    0xd5001110303140c2118000c6418000744140000000741c1c40d07880309001448a9401d009800e03120040500702c240f03002c0c81c00b8040c4091446689030075034030110407000d48030a2900c803640d40c130443c4003110003401422001009a07141200d503000780000001c1c0c00f0281e040990f0790813000103605d4148072103860030f00e10120b005d48040505119443d082ca0103445000c41c158101818503503142c0611991507429629031150360356502d40c81c020f10040c0e000b54030441c540321006004d80c4181071001100120901c45001e81c4440c08591303010040c40807012202c40001c0101129220107200f4408030013081c103980720141818258050032040c0c101400200841d1080040d01c11b10754400c0e4031103102c00b1002440d0181c0c0704909405c00c03012003a00c0c0d05140300c0d035401820001111040381d4280020010303d00141c5061226160400c000150719000580240d02d44401025440c0b60310f00c0880c1850040c200d0420b40038a0416071140611011961980b060340540206480701302c1c0395007000980e11500c500c103500d141c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 733474487 1250 733473237 733473253
    0x9050d03090501140f061306060e060c0c040203100e090a080a27080a150b030c100c06062408090706260129040e060108060409050a050105011d0405 65
    0x10380668048000d03107000d40c0c00856404e82c0c0c081c44d5080100c00700c0b5140e0203055508148003040c01d141040034480d845054041283d0342c10540040d01a51004103194411040080c0c03020001d07070f0610108409034400341096445c3d00b4860b120f103001d00d43c540201c800200300340c000210032180002d02c5039041030300304081d107252035858402101d000100c0002d0440074042e40000143c1603071030025800c0109504000352182204601d41030300114541080051503a003006400800c50703401240083d0a07100444152010449110701910311001c0c0c1c48001d0700c4c0b245000000200d180040301c00b0040188000300c10f07036100030340c1e4400761042c480c2a40c880c001e81d4048401400940e014030340e00031000e0000212096045000301400600007001d800004094ac1121080d04001402d89000c4081441410f03440e0f04060401180c149141c41c020645410040e82c0c0000c01c03950b40322588903014040d0050103031501b284280c241940030f030a080c4505c0d200c007401e0098002000d44440d81c80390043e40d110026103104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 733475737 1250 733474487 733474513
    0x7180e1c1b0602090306040305030a141e07120c03140c030f04020609060706090f030305060d08030a2a030515011103121b030106020a0c3c0f0803120105040905 70
    0x694030000c00c0750103c0c0d08202604031943e003040070500c91032182d80c41306d84e40c0c54003e05c801e054501c180c3d480f410407003481061080b5000114a5a50420b4100101a80039a6440011104505225041e0728482d00c0d280140580542c1900500300101100803894043e4071042800060f9110440d001502034803104040780062400800a0599400003001c40f0b003031502c0c50b181e0000304c030200035048518005070382d0a003080680501034541d00000c1260300442c0c003621512030680743d104c0282044089a51181c030b41110300c02e490010181c840000202400303c000000d8087c00501c4280c0301c00400e012420110f025a41c0310b8460f00c440d03400c0f0031010b14100b030058818541c2c0c11401400d400b000900d400e005219900208010718000d009a9004010019260400740610003664102e80c1140c0f070581c603404d031401c242243e0445101d141d100c003c55416016010b5400c004295001166210b015500024a6010000181c00c5041d000344803841d00c0d0f6a140b04110445660040080c00c1d80c000141034002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 733476987 1250 733475737 733475777
    0x9110f160302072d09050601080703090201020a12050a020606090613050405070306091b08010b0603060d02031609020a0207080f0712080c030d0e0f010902090c090307180e1c 76
    0x4068441e00445621a480761342000d51284034980101104120501c58140d440626061500800020004201604040c1d000074050344d8002c00c580107068a44800f1002c59108001e004005a0031490184400c0c881a400500710741c0000100b500503c500b0300850b9107440c00005050160100411a00b4424109038045001d05401001554980034032040040070071001d002d01c1d9000c0c0d2080049952450b122002c00a16014641040b241ca17850b011300568280c03501011650010300803605040021101d10010380741002c84410385007c0c2c55404800240c44190f40c024000c0f4403155000d564803981c5854800399a60030032400120350307502030742d810880040d0300355008501d80d00609645240c920f004500030300d1544580c05484c07117255105a80362401000f1f01c802d075026501c810082c008007241e5000903640c000302034000c00e100c250000e400356459070b017003200c48010140f2001e5085c0c1507000b284031300002d00c00800e984a0500441441c03500c00e01850306404001c024944500d20581007101280032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 733478237 1250 733476987 733477027
    0x20108061f2f0102040f060c1a13140609190c03080c16081c05070b010303081503010504051c09180c120e16050a2d0e0106050409110f 59
    0x103010891500e00c14051402d201000310072049000016a4541c600b445905080c0c6482e8091400c000000c140100010040c030300c06003840c2040043c480d900c1d26803c0030261400c4800c20000c0040e0381c801000021480b02098081c81101c0c00000d4404020b07485045001050a4a200424001c02400d0500000d4000400303401e240d207402088403c1c18120340a4000001002d4000c61841d80c40304894104514821301040740748140d5251680c1440c803039907660512050306000041c203201c0b41c0c1000030311012150030110f1072248010003c2c0103500380b60401035101c840c003d01280e05080241051082140503034086002c072551340140104541d000b861641c0100446580a401c01240c0850300038122644c0c041c140a15283c00098200f9a000174221701000d1020b51000c1e000f001810000c00c01440c1070004180d0020341c2ca117a02d140c41c56004580403682031150441c0740c4240442c40042500c0394400090001e4902a000400640c20382c09000c03002409443c001220840081010700a0703a40d140c0941e01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 733479487 1250 733478237 733478267
    0x1b060314040807050114100e010b0c0c0909030f0403061505030a020d2a0305030306040605040618050c07080f0316031526060106031a0a0308120c1312020108061f 71
    0x941c0c8406c5120184c00c80d0410b0381d0300d0030f09102d65141880000540340c811401031503074071141d0f4540103e44600c0d41c1c50309840042544074988440008000d494180704a07001403201c00c0c4000c0c1ea81c0d40340d1034001c004101400c0044000340812901003032506000034100754498009108881e016001c0c5d4910441042401094145500714440740d201014008210400396203d5005540c6901e0f240c01848201c420f1540000e00c920b0411404210982d6041003c8200194580021529a98424040c2540e10030349074002c000040020303d48103208100c0003e14019010b01042c40d1945404c04421402e80310110483c1140e00010101000400f2980f010801600d18001c43c0103c0706600503030041c00d04600340d01800110b6161841c0b40b5007515441840c0d501e0510072244111a1400c5480320b8100307000d81245616085200d1010400000303842003520803403044020180010b030389078150746902d50341c1c4032412400f080c50300b4081421032421400843c00c80d00c81c1c60550000070304d042421142c10201038420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 733480737 1250 733479487 733479491
    0x20071d011d040602071703070815060307200a0b01030201170405100e010b190609050111030a08100b030702070f0b1905030c04050a030c030b31030314041b0603140408070501 76
    0x1002410075050225003035581a4a00e440c8e10b4802c0340503104000082c029141c81e4800d0201c03a4030740d6030b8101642d801a81d90715144121003015400d080d6072a0800180d59a28842e0415030001c2211108026042e24400e036518040c0e03048810f01c0400c0d450080d41d00800c82d401281001d01104070f1075200010b90310055001003180c40110001c00c91034800308040700c0c604070309110b062010ba034000b550000141804e00c3d1004210b030300c10144030740380c0c016046440c00f00603001001c60801d40b181306444000e809140046541c03400d0208003e91380c0c000e54480d825000c02040c400040740304a2101b500c03030158465a501d20320f0f40402c2000c41d5280d20041c43d4407030034041480085001d03220580d10001452090112301000e80c00c500342066014401849000c45a0349205040070520340c11840c100194194400e1842001082c5016005050f02c0600306180c0030b0488200424425403081c8158000040d0051902c80d503100e03201102034070400f00c490800307600380382c0c0401c000556200042003118060000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 733481987 1250 733480737 733480747
    0x10c0503040503092b0b25080612071a18100807141b030301051905100c03120c0e0a0e0105030d12060e0412080105040b01090504050720071d011d040602 67
    0x1141030021660700f001e0b2040f006880410412071034901501043ca02c44d481003103696151907c5c003c1c08080c00800c0c036800b4004c0c000404800140802449014280315010700e000c03a900e800d4811745a4101d1440d03840504096230364986c07541800c40d521082c8141c19981c00300b099450704001d9a04103c0014a00c0c12041c04110b850f90169520308545604045000a950f82e54500800c03c140301c0c1a101d0003088000030140708020550f602103200c80300d10102c0c20300c0c2c42101d5550806a91880b0117401d00b0304958180303440d880c0603a034003a007003082c0f0b42002c50780d0924850301c3d0846280810400d000381c5400d58082540d2404482c00780045485204c400c1c00d01141c03540d01c50300e240c41c802d04d096804482c00344144041d41d50341071b003101700c2a0141a05a80030000c500108000030b012105500c1242d008903a2103021078401d510503410001d20000500b860800102400c000690713608103407040410036000d0050a05198003075445990403a190341208520305428100302950340840a001152111b0707003040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 733483237 1250 733481987 733482049
    0x303050c0c190e010b03060906010c0501090803010608040b0907182d0504020117041203020a0c05060903031929010909090f0b09010c0206040809280305010c050304050309 75
    0xc800c45180d0b19030100504614a002445200d40d40306801521041400740104800d0740c507a4802c0c01d50200b424a00400a400c00b8100303c2e00504030070038080e110b90b00010011441540000042d40140d01c601411000c03640c1d28856030351070f0581405450002d00c5a070080c1c0408101c1358200e01c0d450341d80a0307640035092412060740a60320200203003400e030345034580040100f9503030003402da1075450080c0f090781c031451b14141d66071407000040080f4040c00e04d580824641b208034803941180e02da10717030700c082110030398105610542d40d26007044070003002c881c140c0440ca0301c07003030281d0056008a2600d00060500322141e010400c050481a040c5181002f01140700015035074041d00400020a005290324807125581d41407a6485948c014042416607061010701000264009009a0f100350080f018585a9031132000040c03440655100e80356251242864240b421075a00800d0400c0304e2141c4020440d0018400040d5814007003140c1c060015081402000d0490030a100c0c100045002c90b40014040c1600507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 733484487 1250 733483237 733483249
    0x50702340306150803070803010501051c05270c011b03050f130f090b0d06091113021b070302011205070302160f030e04051506070206190203071a0c040303050c0c 71
    0x540309450840d202e503460648040280c0c0383d10080c1c0603c6005d94900780c0d0300d0b241d240300d40c401841400d0401c100010319060110040c160311401d101100c2c000c1c013403814210050a500c145001c1143d2034044103115403041e1060004800300540e4040e1039440414421500401c411042c80c40d040e82801020000c2c203180d034180a0040000501091240304210b00f4698186400005a04400c00092400c00c030501240d80e0250720220059000f0303400300c2c031048585080300c1d400342d1200c1d0003030300200b0009800c100c00c150382d00036122590421501e50903c00140a20954908071307440003038080380c1d03024420036041049802c40d0368060304906025251100ca24401070303409085a10039503880d440303040e403031041690005181502c08021a000d0000d401c2c203506034141e5003084121a441079100060280454903070805507144070b0000103840b03104c04505d00c40a0b440341d0004c00c04646101d200e01030581c00c0901c030002a0f0182e13009a00f61230400c7e003903a4007070341c42c1c2d070003084c10283c103100e034080d22038a0340d0340e40b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 733485737 1250 733484487 733484489
    0x509091c020d021606090b031f06050414040b010503074e050609060d0224071208010b0909041e06061e052b0f1a01080105070234 57
    0x5a801086102d8006000070b0518680d0b482a10301c045004200300011030b0301c201c1003c140c5103001c01c0d03103175a41c80c1c03a0111181e08561803a031002c40140903000094440e0001e005c3c10403518000d0700c00c0c0d074011100c801c0008440e00181c2d03203070100d041480441c3c9500d218050324070700c11048607010410000b2000404100c400c0204940226581e4603240c400c010701300500114070411020010701403410104002001103d000b40424015665602e000056503504120108044d980303810401c000e02000100c0d060075840040f0603103014621703424117511144102e03080c43c122107005404904000d140b004202da0040064019640301c011081c0d880c0c40c0039011201c01d0b00c1c16100c5c0d0ec0000c0d8991401410415071004c11034400742c1240000c00821050f150100c12411011881d190f0903100030004c1c0300b0070300c04688004003504c03000c1d100c0108000c1100e03001207415041035035000c0386200e030303602c460250981d03000320754680068012290402c011f505e105101c0c405250050000e502040901c240901ba900031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 733486987 1250 733485737 733485793
    0x6180903040303030f0b09010e1e09010b01090602030c0a06050c040302041e060501020c01053103050708120711090624090a0f03020a030312020714060405010b010315050909 76
    0x400b0010142c16110f0700007881180042849040320306800112100c00500c14171400e10400b2000850740e80001903c140e01c003504041c410018185020010b0080528003a46408500c00304008503c4038000800d407000d04550074010507103501b4903522080a03000182c6012200342040c0000310040e80c03140580480007982c802d825810903490390390300d010740302140e02c5281550401103101c120790340d201c400c44802c114880200300c040c1000411094640100940402031072950076070200411401041c020f048401e00304c1210703568a4521250040c13441030b0100140429081075000c0e401d41000d0889980c4000000c00c18a68031050089208215950300c07802140200300240c010042d1400703003041e0f0080e2980c0d00300109214250350208106a40038000942484545031000d22100c100d5012034040b1381d44140242c80819203131184030b60781d400540c1c0844465007400c1e100b4120307520a00c00d55403154a4020229441c0d4603206c10301402110180402038203004012200c190210030039964454004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 733488237 1250 733486987 733486993
    0x93f070f02040f0209010e0d0c031a0a0c021605130f150f0801020403080901120e07121401050c0d1806180311030304030203040905090c040c020c03071d010e061809 72
    0x349881080100c071416140300d031540d031060084000c1a41d1114055182c250305441d00780c4202014108901c03c00b00036030004140004010f600d0583d40840392203035004100c0b6001c1848807040c00c0f00181e0f2210780b0340d15103591740001d20074200300c0380c17400103680c64054034050b01c0081d9803040c0e03500310001d44000308801c0941ea080c20030304100207174100380c8100080034804001c5007000d05658a40b0605e22130343d030303200c1e0400a600c50240c140d84429405002c00c24818421142e000d656502c800d4100b0801c481c050352524440200045841d4042c02000d20819241c1e090902e0200d07541c40400080c100d18030700e2416409944d04120000e02e1314480e01064807070410003203ea8024503c0e00900d291408c440606443e0018428800060340000c01d80f0305884100a02040d59941c102d10f261030120350602c0305a0250428030400e0501c0d40100c1e42c0700700c850341901a05c845030f4441c2400405106140551711040c038003d001084000301c14804a85c202000070300e8070041d4107a0542d07c000411080d905540150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 733489487 1250 733488237 733488263
    0x20d03180830030403110f01050703050402040f090b06131103090c030d0f080604330e090a0f0b090a0213020408061024050903010903090e093f07 64
    0x5410400790020b500d01c2110390080708880c1403030303401c090201500003018860240429000d100c01807107800c881c0358840c0020403462800c502c004000d40410381702640907074500401d001a41344035000e103100e5650048040d10030354890505218400c142c155006200b00e542d0300e100248488000011400b8909800040c000a603544041504222800034103109001701c40150b08800703a00203c1c4283e001c0704c120780000d04100030303040b5a5009008001801454407080d0032080030b9040b00b00154003555a4203003403102c15611903500d03039500e00c603102000c1d166109880b9100005052402815408107429040d038508203061b41c0403540000140140711b8400f600450b060011030f608100590b8008103029101040301c0c80c1082e80502000a044081e0003c2448000f5815160041d02181c1c64800054003c04c0b108140e030500a0406081d4000c0e19502204100410092000001c01801800486404101c6950071840152040b4010004146a60f400c0c070070644007070b0450340280400c00c2c040c182d104c0c980 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 733490737 1250 733489487 733489513
    0x31902090108010e0a15020405060a03090b160516110d031106091605090402300106080309031c0908060a06060e18060f060c01090302070320010c020d031808 69
    0x20030142c01c1100c1c960300d8154130105072180082c0e84c04c42250050951448048942c0c00398020340f085402454000e980059801202940342d4490301c10640203403540c1401ea16266030380190900d059130a0400650140107144a03410010707010383c5040d124001000d040c00c0103a012030011000c01700140c002c00d0201d9000201408107000090b44981c070403002d030880c20510943e450300f181c2c0902946004500310b40000d800c544070a02008881007124110805036107018450340315010307409210190315420800d00107086600001a280c10a200401928818181341040500300309070180002c10840e000d0030015880c01e00348402405914680404110f1604084028150706801c3d89802d01030140d180c0d40f5100c0c04417130b8000e5078015008881c40e070341c604c6940d80058007038012514506600d51074a52184109030700080d0781004c4a02c0b941c4004100e4010341d011645c9030f100426601d0100d2800041440140742c1101b05d2030519220b4100b21100d051421000d121054583d04901140c0d4002c00c050700c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 733491987 1250 733490737 733490749
    0x6050702070602150c0307020c0a0b09030706090308090d0309151d0f24040302040617070506032802070b0406090b1807140102010b060313061109010e0909010209031902 74
    0x2c1c110b1030005054101603030710140319001c0002c05541d401600030010849640c0309000c0f8100c82d000080c80740098a440d00313500811a80040c00044c8240304160000a001d401044030608403908001013070304254004060000001a8440c100c00300800000c000c01c04041428030300000314529079440b01942c200d864522544400b00c6500d03032160541000c1c2070100e40d40d0044108000302160000040c01292001455081c01030b9080254801d06018011138155013490f07540c11510031800444c2d0f580303130f500e030240289440f042d1407116104140d60100800070302c10000b12400201400c5c80149070041c1e07512541a403031030598044610303584400b403010501112800c02908000304c0d040448030f012141100342c1d0341d8002d9201e50104005044480d42e003d038000e6221020103800600819a03074a040d0005040a00c01980704855503450039100c942c0303281e0100c0c107840c10b80c10103031038410b81121064200204900b0041102d0110342d000c0115142d6070f2401d00205041c0058101c0e18205003413240304001f1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 733493237 1250 733491987 733491989
    0xc1b030c090207150b0103180b040605060d0305040b09030a020a0e06120c010215060a0b031801060609050109060522090e060f040302190c0e010e061c020a051513030605070207 77
    0xc1c500780140a00c81c0407460324101d80300ba03411500030004865103001d0050b00230b0a92442c042c100c0c1282c8000d02c00600855548161145110b010b007000301781e450000700101d510300078074007070b002942c244070500000190f4001000004401002c03200003407a16400a510039007143c10682c1c1010702e01c410b02c103c0341444510420740c10f000c40c0c0580000741e05040000d50320490001000d9140d4410808941591034400303400d4090a10100307036a54030300c1d14000100020204000d0071001d98a8142c000070480d101c0d54403101505c805944042802c1c0c6410802c0700c3d103400806000c90040e080301d903100c03000c040f080d041d180140010003000c640602000700e65410b00d10f006083c6a0355a1541c010800001d5020941080036410040440c07008006401c000d0560546604624207002c20341c1c00101c1d0405420200718807450080f81d10b451108103440d8500102c3e070352500025003022400c04244480e1404050300b8448446000029092180084068610380e80e00d0340b040d00c03815518424419032650510240c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 733494487 1250 733493237 733493249
    0x1202040b1603080a11340b061009031a071b140106140d060518070609050f040213090b010311120a0608070803090108150910060207080c0306010311010c1b030c 70
    0x71543c20704255030b000b207228000032038185880992006040700d0b0346c11005032800050031400e651718040361405d0410724005032003842c4070314004882032200b40c1c8030b1001207082c0c9501003101e40d1014081c0c0340c80005144040c00c2003082c071404007402103000b411645200d82d08c0340603010380d00103594410700e00d40c2180e410350001c00d0142440344114003180c599075035044100b90300000c00540c3e0340d110510442418140d4441d60050b004484002840c01d91006400d025240c040f500810309403002c6080204a110307403041e07070380342030290070007000307405419404602202c1c810304005c21950301c0c00d00703814415400450300c00040d5041009000b1411300380d00c180c4000e002040e00500034a41001c581690368020020350b03d0420440c6400214215410a4042c0f20400e000d4003520f4070381024a2400781d018924000d04d00188120200000e290340d0001d80d44450b020090301a00c1c0c16400c2d5240e0348007800d908000e0a041c03041160101e0001050a9010885245030700304404220b429843c16203a000c0440d4850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 733495737 1250 733494487 733494491
    0x4090b040b01150f2102040e0c0c07330905030109050312010b0c1009081b0d030b090105012120070c0b03060603060105031305030f07020909150402011202040b1603080a 74
    0x503180c4c0b07500224603044441c440e01000d1144425501c958000e4030031074102200304110642803010780310409026180e00e40504061790740054640c0d22410540d008843c1d41411204010030040c00d909400304020980c0d51203190550314240c5940202e402d4400540046800e94030000340340601d54560b10f00f5a016001d040781e180d1030900351081c950399881c040030003000303420707980c88640342046550710803600e4908244040d84100c600d0128240c3e00c031400c8815003004207080221882507843c040e14241c2c107840c0d0503140e4540c0b04a02400300041e000d402c1d41900103490707540c0350005a108c600e04007030002513615a00b0560703552036464101c8400383d540d40909800c65051084c8003699850f00d041d6a4072031028a07000c0d403079540e00c030b400301040e060003000a4024000002d4800e503445816000780009402030f1006003203510fa031040c00b07540e182880421040d00d8902008100158403681d51510302d0a0440d002504098941000c1d0300b10f035004d1494a0700f0240c0d1040840109508150310a1340f081d504e001c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 733496987 1250 733495737 733495757
    0x30201060b210606090a031202100c050406020606040b0a0603020702010509060d09170403052e090b0612030903030d1e0c020a021203120a0b01050f030c090913050a060b04090b040b0115 81
    0x108240d81c20a010081211042123955128a07108020030b51440390711007814080070104c0d440181c410b40c045e009850040c0600c0e4006042030038035018031405818054501c0034000c0ca0001c04070003c1d00048022030420200b00200c0d4501d40d5400040d0a2081c041100087d14070302034a080c4044c2102107840c640008014002080071920104110024002552403011900c8144a420038004904062441041e2a00c44800184039400103154410042650801c051000465402e83d5074001e00c030300d0682c10b43c8200301d04500e0154982041800b01d141241030007410b030314030034100282c584014581006030f1180203584203510307058140c01c2c100e007080c2019500d08480c010000c0e0402030b00404045141d5240d0305e810042e80d105204692801020703911030707034503070415640c580c086a100a0142c4c0c8159042e40c040340030b118810359004a6203034010000c0400c0400ea079640340c05091204510b41d4016a00c0d100701d0041b510036620a4130030381c840c0e1741c115159070414441e0071840d0100c010b030000304552525 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 733498237 1250 733496987 733496989
    0x150903040905093705030a1710030c09110903100c020c0d0b0601303611030c1008070f020c0102100e210c06010603020f0d0504030201060b21060609 65
    0x10b01c20809504022000390894a00d860b14a40c0c13042c0458010443c0c440029403400d203076840b081b040700d00d50a0103d890003039110302100c0321018042c4c0c0005004d0f0303078000c1402c01035410294040c2c1000a83e1198060402700700100081c14204000c0d541200d03a41c540910800681d410310260704050401c892003086800c0c0f07501d03865100300c0c00a081c941030002c1c5031299551054000500f01d40001f03814036102013040c1800c64a00542141c1c0350140110113214185074070030205180c90400c208074100b0301441e42c54523881d405141617000c0c06080c1c040c065840b000b46641c0b5203441c0740705c84001607101d0303a400f41040c0078002e11014200172020304540103403c10b03044687c0d001c6510905680c8010003c2a0000702d0502d69040441c07a49907a00300482d4030b2484101d290000c0090a10f420340101501d170380781e036260300643c10784c400c1502040d8850340401424040800d141d00158009000384000110f25441d000f0102c400d52103011668000c0700e00c034588007048610145010f0348120142c070b046041c403601d40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 733499487 1250 733498237 733498273
    0x522032604080f0913062705010e0c07080702040626070608190e0a1209090506010e1302160c05032e050403020a08130905012405090315090304090509 66
    0x83d0036103842800041c4210302551a074554100c074007200d0004125017562454814641490104d1880c1c4444c500e80c254045e4081074403503141200d0008038210301c00e0340d078003d8401d010b900410f402c440080051160310056102d81c0b01c2c01c400383c46003070007104500071046650007500042040e040307004d41c8280c900b1701100764840380d45134115210b076200030700c6203001d908500043c10a40911101d14450b2050f00700500100326030503420000581c882c01945074a8000301420f440c021101140400e007013032115552820b140640c80602a860b080041c02c0075020010100d40a10321402591401040401406289011300078905402030341c04800c080c02c1d0140e60800f92103410101c440101656170400101410f000b404441041c0381c0c0640f04583da9003081c0c4450303003100800d014444010f840d040c008102d40c00c44051403003d040c0140c0b0940c4405e10360000032105a801901816050701580b000341541c03c483c07031900e03401244c011002d551500d00b000960030403110000c24002e0140c0c030019880380101c41c1d032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 733500737 1250 733499487 733499497
    0xc050109060b0405090d140307050903190b090d0c1101050d0e070302030c240d0b12010509060f1e0c1b010204030203010507020706051815190f051309052203260408 72
    0x245814544279503580c8010b644e0390003000c02d00c541500030880c454640c69040c2001c15941481560500d105849003101c0e0b0b075072181c00d01c00b8107003c141e54050032400319402401d0400c019405243c000d140040d13810340c0e20161220942079418a900194061086290600005a28a01c281da070b001c0c01e845801c1e05aaa081499031060850a900203125500148144c100c0e221500010300b00ca4200402d6050a60003403e00301e0704040705008010102d410924000512402401004034010f00010009181307403040740040c0404000741010040d00c49484228564986110100c400040e00e03580b40d40141030940c0c20082440d000c641108006001141d0807906640310080303480c41c104800b0381341c100403500082c004041a08003507008500019140031100b500c26070ba07102640d41098000c5461001e031802e01034813801000c2100c1144040c0b03c41090f503809180d0185020304c6084200c040802981d002c425000c00540c001044003070050702070b140c41a4001e800030401204101d003440e29840c0c2d058a07000e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 733501987 1250 733500737 733500767
    0x6061c0209120609061f03111207030c1203020124060f090e0a0605040b0a1404150b0c0a0b0c0309190602071a071205040b040b06010c050109060b0405090d 68
    0x3010800d9003450300c0784050180c10084a000f01c8010303007020340c502c581e5407500f02d45440c50840c803d1340000c0c491a1000d04017003201d501c9030a00c1c034201c00c40410014806000039540d00c0a1046420010206904560510003016008801c401d800154200282543d000c0690240403003015459461440001c4039090200d804a141c400c9200ca8001d42c110b8001d0050341c40520440905801d02402d030303c0980c020f50488004070303001c1002046200074801e41c50994441c0010f41300b010030100410f418240c00484a04504480070180140c82e0045603010780c101d03102110455014011103010002d40030189a00720051201460561030019040c955035203c1c5503d000d50f10f80c80d40c994004121454060b10045580b15107080c04c0130040c02d90448400d1000c4503008001500b03070700101c040740720034440e25015039041400f690040d50786d500d0700c2c620128007a103c00c0c1005010481036022480270b00c05c41c0c0f4524070400c004140031604100704410780c0d1001d0b1190340260002c0c0ba181c000d90742c02644032440748003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 733503237 1250 733501987 733501991
    0x151906050310080601060f0e09070c030305060607020405010b03161803060c050906030405330f060315070e030c0907021506041107030504030515220510022106061c 72
    0x5101250035040c2c0c105a440040c042c402c010001ca44950085402401c1d10540e694440d07540031940100301c4600030640c1c10002080300c1c0d500c00008248640c011981c0300002400c4145410b40b6076022800b2558240c0c44034032810ba010040c06001110380800a0400d00c0c28603142250b4460b0341c1d15040000140d03c001801c00d40d40c3d94130019021b0160082d2110110003c143d59200d140c24141720392182d401050314080c113022000e0300fa21940704203642c007415869008680c0d046da0f41d00002d1b8015a54041d060903458812490006030004800c1000c610a603140d0b5074513a0860912410702d4a42004004210b1003170f66060100a841c65000690301022254442c1c207403070310f44405e400f050080c0855618440c6031035001441009040c0c001e0010400c0b24070a4041320b021500d0030070f0342132444209480080c6401c107070144c400038407114203840c440c04a0241094a04485c001c40d1103400300c0c1c1c4170a6450000c440030201c044029859040306503030100f0162901031400c0081040c200300750f03602500540ca12a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 733504487 1250 733503237 733503241
    0x6060914041205090117041b0e16031e0603030507061118100e1302070b0108120703050a0e191715070f0512070e0907021209040b18010902031519060503 67
    0x42e1141a030110b400ea0303600e03086c04a43c01d050600340500c201509000c20348101e05940003501d503400301d005c280320f80200c0080d06503007c06040202c01070710b911104240f40c40d060b102c4002c0d004d0306900c58400150300c69210555243c0040c90894242c0300301c1699080050b00c103014030a03c1c84100c13040140c50080895010000a0380b1403016244408030644280d044404180d44201080141e4010b00015000d125103c140d6070ba170311500d81c0e483d84100d814110501c0c0170700502d0002401500500b45200640c108200402c1d2034201003200304116101d40d038103946c03940904000312040d06140c03a0b15213041074040c04400c0300b240c0341c5410021001e4292410001100b4820314410300c10030a50780c9a072034014100c02641400640206081800c0308101e01c00c148a41c0451080ca00000300c61072194959400c0b5400c003015242044000e0a030030300900e401121462803d0f001d1041240c1c0c0d940a0000b4800051300da0600240d549030605030400110300801121443c0780201e41c1365600641155010300c0c1c40d80d9a6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 733505737 1250 733504487 733504489
    0xf1306080106080f0a1106031e010602161703070b0c120c0405010f0e490501060e040308270a0b010602011805030316050f0a020705030d05040e0a0f06080a0606091404120509 76
    0x9d1041d5403021a004010341d80049440e03680031554217481d145c500044800151074105441502040135103040e40342d0300c10406900043e4880c40e0003544928a001c0381d50803c1350b144940910308900b25a00c44040702d00140a104542c0c001c0616850508603141030a03848044801141d20b1010f0340d004400c840c1708151500001350919921301006a03a041c07d01810007010310040055010a43e00481d5194205100410443e40402d9039501c6150140d5402e250b503102c0000418203c849040e5036110703c1ca21600c01c1c0c120036010411058802c1c4541d001c1222585020002801c5480b507507281c1c00ea0070031200481e400b00b0300c004103998207c45489450b000104140c075069075288601944040d05080c04a001c90b41f250b00820001d007205c50980959661a186400840d0103200307501506070701d020540b0201e03010100c5a0b10251700c1d200180301c005074590300e400d2140e18055082c50215041c0361103507418010075007140075984100748140562111400e00e50b841e101c0c5e001e0b8401d5004c0401001207501c3c1c4031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 733506987 1250 733505737 733505761
    0x21042601020904020d02040e0a0e120c1e0d110c0d170904061d0a182a0801020d06080a11060711040203010608160216050f1306080106080f0a110603 65
    0x2e4600001c204540e01c90000700707100043e411500c140d00180d0b408100003214042c49006641e41409004040c0441e14010626940b09d600070880b18541d0388100d44240440c005c1c8003070156405200340c401080042c002d080c00524294082c09a000d203030300b141107626805d440d19024103001582c06030502c01d017079404001440841c040c2c0f2020703e601904115002171740c00080000f48d01d69154071000c1074050342d11400d2640c00d44a0b0100c02e060505220349540700410204031036110f99801280f806c0c0038911440c4c04020201846810079001d0340d50028003244400c03890310840d4014202d00014042c3d51101d80c9500c3c8070034403440300150040c0c00025030002002035011414030942c400600840d10303540c44920042034503a04030382c1d4054850000a41c014030714000250512555034980809501a041900f80000325811001c07980e0442c000d0b0019100191490140d80058608400009142d81c0b410744014a043c1740c00c8502415900411040c1d4080f6841c1000704d00301580c01c1d24030710742d00c4d08c5844203006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 733508237 1250 733506987 733506997
    0x14011701110307030e07090911090c0723010c0e030d05030615040305010f1d0607050a0c0f0b072303070302031003061a1201110d18020d052104260102 66
    0x121500780081005400782d003560209000c00242c0d400c483c08103403116203100072120305030400b4144038680d14540d40c403482d0407030b4a04d510151540348103060058030b658034680c40c00b0040083c41104030540d10012114400d2040f01c1d00d040303903417034078541100070607003c81d40381c808250b00300c2c0400c04000b0008000f515841e05440b0758000c8580401d03500c0395a814054001d00b15582c20038051820008000c400c24040c0001075100d014000151000343c41d08007060f19541e03c8200c0710703400d000d5584090f0020503582e40d0321005650165221040b50300e4a0f40c4020481c2180c10481091204100142ca00c0d1684400a072540821942401030703480e11030040034000b8006a9000030701890800a208443e00101d26007000c1012007917402055842055410320b00b80c070f01c800c030203558101041c41180f4940b22190800c065680f9403484e0301342e64900540200340103480441d400e441d668081014049040c0c9900d603202409510845c20a042c6820242120030000000030182040d0344105c3c0f60325505582075048034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 733509487 1250 733508237 733508261
    0x3031c0f0e030309060907050a08101e1514040e0a0b0402010c06020301081f06080c19050307081b0102030a08010311041e230f1b0f0a0302091314011701 67
    0xb9480f460303c0031034940e4038001121840b8290060700c00019150500000c10780645648001421050a1104105000740486018000c03411403980c2c000843c440180b180c190141c2d0100d484100c02030501c466200c00122800e00fa42c005c610b002d1601024030300100f442500250b0015100c101c03074540b4001240c40f5111480301500b075601c00400090100000100091188414041c030100100900e8002d001c90312a44140030307107600a00301039082e030728114001c9520b2815131b1209602ca25144c2003c646416103a82210540d944408498007a03000c10840184201409100844c502020300c20700414082c07061100070000e105407104080199104d400005400c840100000c4640034400300c0c2101802c1c0d00303030040d02e01445811644201030402e0f1034562242c070901c1e0007544580c4a040f10181d0203829008440600039040c021031102025a000410100748259000743e200e600b07050401015001201d42120380a242c04081d0f100da52006100504440c0e800003229504404101400d02600700180f80e8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 733510737 1250 733509487 733509493
    0x70f05100c02010b0306010803031506040b12062d09090307060c09050f040504080a21050a020702091f050f131509050921090d240b03031c0f0e 63
    0x111144500c0e41e40040680306440d4001d01c6025030040030705403184420300945416410400c00038012a00311050501da1113000780c50356141c50b5403255040f00315041056144410302400b014450b15251030408003100c00720b50700f5290601d1204045052140b0300e0b0101090007808a8030002d81c00c18400d106548100c4e401000c14080c003401c07004024941c200320f0203564030a80520310151501e0409105241c40340d40c1c8070031680c1c5054241d040c2a595442542c0022031540041e0361000500c50060081c1c1e401b0340c0e601100913840b4076840c410002d403054020138404005000c81c00f2000104500d00f47e800407100c09507000074032402d02c4030214845400d84800743c0c4107142015004200620f540d9100812110758440401c0540c44110b10a40c5a441c4401c82150203480aa408066070900c0f000602d0124070082c000442c0d4440f40da1400b40d01103400c0c2c0610388400e0003844030802942039005a050120b011400744d490310740c0b044005e1004840604c50244110f039503950b148024113a50707000c00035501842c021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 733511987 1250 733510737 733510753
    0x40f02040509010e060a0c050301031e02030a052b08160e032b050738070201090507082d1006152606040903270f12030c0206070f05 58
    0x1540e004e0041c210306a22248542400074103402c0c0c0500c200200c1180590b03c07149035910715200d001c000d030b0a000c0c1501d84450000080d1005a40c00c102a04499119801406205107251814000000808048591090036144a4424075808046250b01c14004040c900c580c2414920490b07910380c0c25000240c01d4401c6d42054611140b01c80c0c0c00514140880440c114000e0410004445901030f24000a1a03601d000c04450000801c0e4403008804400d0f5102d0903008400080715800503040075501080541d640c1c06030320007441020701c400c5010307000d400300821080c0403550421a0340d1109400100400c4007242e8580041c0380140080481c0003503203041840742d50b4940444100c60210341e1107440104941c0300311207004224003070380d000c140520884880038030b6a400c4240401f9140300c0104901b04101c10100540b00d10003071180302d0030030500101d003400c0c0b2810040c00034004103098224441d0003005410120000c0c3d44510803010080c2c0c103989050300d0710b03000d2918107980062610300030300074050b480c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 733513237 1250 733511987 733512001
    0x120312110d090b011e03080a030e060f0402010216060504150e0315060108010e07121107020a1503060f180e0f1002030a0b0f01120b0a0503060406020c06011a12040f020405 75
    0x10041c0003902400090003143d17a50b503e80484544c6103807008500e581c400c0010004207002d2405410024030700c2c01d021405506054600d0b0500e002200d084100301c40380305c10700c402e65904010054403c943c8401c1d80010505001c07019006000d507201d030030460204030880c0e100b07551060940c825101800b5080383c48501c2143d4912354110300444255000404400c0000780c981071150056005941c6922060130f1200c61f44018406031000900e940e0101d0010002840185c0310521440014101041c407a2140c40410700020143c50741d5500c1801a1002c1c098180510811440c210f1600341a411300001c4d8a1040d0410324144140071049003080d005100700305038901c0da10380043d407240c11002810008840120200050480040b038030f00c0c0011f611040c20742c0c0d44415035000d500c01510050041c2d210b160f4402c00a07203485801c0700c003110000d8000c41c40f80f418407002c05c1100d000d040408080045c4080410b8041150f00520004501e6010124045001e00c50802c0f2000074154005e40103004600e00341d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 733514487 1250 733513237 733513241
    0x1020405040513030c110105190903020f06070c0e2d0901110f1206061603030905061605030408030703110301170601050604120b0901020c0a050d031401120312110d 72
    0x8480d1600560800b8006a80ca511420000c0b8540358181c907481c084030303010f8545040210f81a40c0140c14498204070098108100011a425250301a40d51a4100307003940706100c0300c4031082030030b180590410300980c000506106d0300c000c00c3d5071000d0342404142c0d6402c0100d15043c16852040314010703240a211030001800d600c910b501c54001c2000a01020410071040c080c00c2c1700781c481031095001c05104c000c2010b041010441e4001078020301341420240c1146014540003111402180860381d14059801086002e00460790700c00441210203617011010301002d001d61100400007820070b4000800501c8850080c0e00046003940741e070449503183c0d0784402c148151a01c070455407490178414000001840d180201c1190140c0742004814080769800d90b580d400107190140c00c034502c41d50227006508031503c0400c02004014081d10040c850582781c90b4000c0d049072101152031036400c0054006004d80c030741e80641c185495038141340c8419035080c64041d0800804e6051500c1010309400641c580d4890142e07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 733515737 1250 733514487 733514489
    0x80c071103240f01120c09020c0106211b050901030b0a0e0703032c0102191406071e0e0f091807060504090605031606050304081c060e01090b0906090907080f010204 72
    0x154510f0b28541e62200d891030360401004000400c181492842849806c10903006005241040c2001240281e00c858000b80010300798020035210749889003400c1c0c1401600c074026400192401c0c640300745a801e0074003042030080d0502000e003112401d08045200110941d0215020b1240c00c410350300c0c03254492030010f0020034100ca0a09028005040303041c0e084840b981d45111a00058000308442075482c0728441c12464504403d59844a910034000d5410b0740c1408218403603421ba89e5040c2500714032031080f1004080041000703080000c80740340182d1a80f0380e100342c515922800c85031200ca80e81c0c0e8011002c1e8031040300109030441e0090f07540008410350004081c00940722001c0c4180715a07504d0303105141da2041c14607841d848003441c0b4401001b100740558029600140100c0c04103207050604240c0303080c1005d4071448255202c0e42d622042140c07020748009203000d8141100184490f036907400004005100180c81c10b0300c80d81440000c80c007800410020040240f8800f01620031441c109a5214001c2d082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 733516987 1250 733515737 733515751
    0xb0307020d030c020328120617011b02060f04020a210201110c180c13141e0f120708010e03090406050d02090a020904060f0b03090706080c07110324 65
    0x1841040f010090010060b5042203c403403000a640d00c000341c0f800c075041c009810a1600b448201e20380c01220031050b0003158060407201010080d410003c03c00c2d00d003101c21b50341d4070704189048030150894260740854441e400c60288403400f400c0c1d0b00c513400080c4106440d50711001c2008030340456107954204019420042e54000d03214030080d001071145150b141e100a42002d680b29441c5000e54a54050a046d4180c010785480030050805919800300e030f00c00312007504110100e01401488031024034141c040c80d483c004401a041454a180c070021500e1450200d404070311500040c0c10300190b100c1c04015280052840c40000e004d030284101e1940d4899101e200d409000e83c0c20607001041034208107141428069002e01b456070303940d403244a2000250099502c943d8000d44600c000290700110415640190000424442d624189054901e19201c180c0d0b0041d02405561010031140d4110302081c0d03000d8903004140c40005551817000241401d81e81d4404101101c18503039245c4801651503d954490f400e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 733518237 1250 733516987 733516991
    0x203090d06090212010c0c02150705011107060c020706141b0105011701140708061207050a1508060d0233040e04020a30050c0405070503100504020403020312070c0b0307020d03 77
    0x4c41482079a082e2011100c0e0b26010a1074006141c0050608450394040c54908850107400c1602540c0c0300c2d82500d891080304500d2109c0815488140091407090189507a400c0c0010704c400c6190050140204103000441031078400040381000d00c070002d8400f460481c0d07030001d00800656840d0b049841001c1e080b04418011507182c01d0b207205640740704010b09406403c40c0d444200d41a982c2904100c0040440007610744a40100100000d4940342c0c159030501410544006803401d0803810310040c103000300141280e101708890720b0b100015861706a8688030407a00781d02c1c483c1a9001126060785001c0c41044c5803002020002400103150040c4440f580c00f640c030031169007a2080d52541d9100c08940315155040c070030395616a07100e20b41d10790300b007581d001c0c01e10a60a580d14000d4000009081740c9040341d51f903010950002c20000d080140c002510050a400c6400f142000c0c02c54003c00c0c1d44030104201e402c0c2d0a1400228681403081f0010880c00801031060502e50703074a00803100940341c03140303000c02102180c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 733519487 1250 733518237 733518259
    0x20109051c0311070c030b0c0c0a0308150f090c0d0605060c0115060807080a0b011e0c021507030c0602130b04091b090b070b070e04141005090f160203090d060902 71
    0x42901c03021604c81d19003280d074140b40e003401c584842c000d1400240c00e080c10510104450502c0000c02d1001000b110b02986030181c0500e402c5480320301b01005458120b105034a01d60440c659640d03107a825940151240b030085da201c0616a581100404e059004030b6409030b4041241c41110380d0542101450700392000c02222719580d2440295104501903502d600402c01032030008900030300e55880180c01c90414074000e01e066181405a080e00c001030407003400010020010740c4e095060941503404030100040c08586848840d80740140341c1c1c61081002410305400240b0890441e9402240c40040c10092040b1540c03680d59003030030781c014440c0b81000110101107000126025000b40d8000c002c681c04245200d14100c5a0703503038480c64540c0203100700280b25a00d002c900c0301d0f032a40e11070144400d007800311030354032414a0b000b407203d00a05944500c1c41520701034104080440c150407800d03000020b10801160009056109034194010051450341022560703100305d09000150f0010041d850003074803030b51070300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 733520737 1250 733519487 733519511
    0x309030d030209150a030f1d0d0203030702190c150c060b09070e0d030311031f05060906040e040c0503010525030c0e060d1104030c06080c040e1501020109051c03 71
    0x40d01400b0b01d841d5005413103012104c1650760a2004007025011850006000c80e203a40f1240b08603030b0b400051401e0030b510894107040d010810003201e03016101d076000a500b186001c5000030b5590728044103211540c913007800231804006000032502c0150a59a01c0c80300005081d49000741802e8860000b52001d606001e148102d60500a0b81d40b40600004c0e80e07820b090901c4503091115aa59452044040517920031240c0f45070280c03040a9400307811600141c00c900119028103071131448540e04041c2c400c01c0100070b9a1150751304c80c000c80d0200d0303440d40c120240315a03881c1084c3c0002c04965000f60b4240d400d03c010008920001c0d0500c0b0080c240d038600600700d103c0c0c5a00300320210b8070304c1d03a45140414800d50041c80a8940100070300740181a605000c100c8012544c0343c8415a049135100719241d0841c01401d0040641040701a0741c00001004524102440d041e02d18040c400c0140c11090343e0301c00b4064101041e4404e4000383c42041d00070044480c00040382001003441d003604003041000078501072400d805 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 733521987 1250 733520737 733520741
    0x102092107031416090606140426120708120c130e060a1d091203090a061e09030c03080601030c140306011b030207030c050f0108040b180f0309030d03 66
    0x1890340180014070005040d55144450480d5146607070400d4820b18480074803034800d51019402501001c00d0100301c4c03e20300900500700541d44810f5070b09a4000380310503c114012840341a82600306404005000d042034100c1b0b9080c6035209583c041981c000203589001d000d41d0400602400d5011191440555191007600c060750041e9401c1c0c01c40112240303400c1140e08402c400990300080d006003c2c810042d40c0341014a81c28201c040c04d42c210300000010001c02840034046030740701c0c00302c00380400c3ca0761522000e07064880355006c600070400703a5036205c8442945285008540c0c44510441c0421084000d401c001c3c01407102c00c0070442c001661540051065481383c01440c600490390740781c00300b800c1003036084580541c1000304414100300c400c08124013036070001110051018001d4020345600750440c1451001c81d03a25800c5180108400607102c07010742d81c40300400d030f0700c950001d0303880e59942c07660342e911b000b1009900c08800580c8030b480748516081d03101000408400e00214210b0341c0d601c882c8101502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 733523237 1250 733521987 733522039
    0x1201051005030a0902032503050705040c0c0605070212031f170703020d0807020907120605060405100c11060a030b0102102f04030c0e04111f050c0717010209 69
    0x10000300305002182c031814007034200078240785c0f004044e61510780c07480c40b803102d81d00d17a01c00700302040341e10072802002400404d101d05801717003000307441c01e01c40c00103408800f030407800b603201008240c0c690340d4000a100070320a001400101441100d41503581c00c26032030b0004164140020301d03140e842541d00010b814042070031090441c04803900508001c614580800c11a039131903040035504e0700410080000185d9800160078441c05194544044a5032040919011202560002c50055104010078041a510907001d940e540240b490f04800d0840c2c01d01e00f591141681c00d1086811107030100e8600c004035095005054211020f0f800c0b10090348408903040150b44981e60b0038211154110b0140ca00b10051284203040440c14496451402d681c980d5016041c04180d488007130510001d000b84001c0000f410405115458104c4124030340c40e4405032202c03609121015010140000041c1003811181c05120810040100c40a01c1554032001c030b450302d02030b520074203c49214590f218000240030b440070304114 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 733524487 1250 733523237 733523269
    0x70e0109090209030312090a170c10020a120608010f11030c070f0f0c3314090a080604060203010f080f0c04020f0d0903211419110d02120105 62
    0x303050540750569201c02540b003605041d0305400104008801c5c0390341840017038065016203004101140960a00d000540042141c001d650380041050050200e000140300c000c00c145074000595516001c2001d41d004941301c180b007660a41008400201c00e0b6040d8461118000d80703030360600040c4459840009584812610405090000d00814010032403c4103c03005691054040c55120710302030f1959030000301b01e54070280f00026007d800c16801c4001c502d5144000c0042c034403000341401d4078180500120582991041001c0c004a00c81089075a403450342401458000d0075981c3c40e003020f0030807402942c800d0240c4219044107000008800c1c1c80024561a0350300310074007600e80f905040c0c0c00c00c0041c0d032085031102d000000500c014224880903102d0015454400c0d2030b01780c0041451400c0380c02000140481d460300a00d025480c103049100c920034280d000c81503a0300c68050801c040c003104018644903110074240701010680140c4a50f465004095244075003200400c20b070382e65400c0211030103c0b00d0f221 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 733525737 1250 733524487 733524497
    0xa0c1808030d0e03090a0801050403090501052106190902030105031c090b09043c06060c170424030e011811030a0213022703070303121103010f0608070e01 68
    0x8802c00c81076001c01401c88951081d03e1801780c10307a000030701c1c0d4901504410785030396503001070008064001458600515003801c0040c00c20010f043e2100d0f4008031401020203594590001a500e580c6917404004005490180042020f85580781034000707410034002c80380039106000912501c5106c1035100e2560a07040d694000032a810039014040d113400080009400c1610303040c402c0b090511018000c510f094205040004a82050081d81058102500511101c51a060003030168a0380142805070298012031543d002002c0da404c4d88107144920b0780141c0c500c081a045a400d10304400394108190394040c1d90034050419261020f9089801d18140c00e28920354180403500011070800071900301d408003e0640364240510f0b000319403500002424003032070a600017001c84640940f21602085030360a11482200305000c500425521a0180005020300c90600480070a0403065040280d032800c00305421038803035944900d001000c4095000d00800726041b14002082d50b0f21030038000410440580d10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 733526987 1250 733525737 733525747
    0x3030f04140109050712110415050d080910020a0308071106070309051c03020322050d0c2a09140f041407030203030313050708030a0e130608060a0c180803 68
    0x65441d801c15000e4000c201e5529107800c880411000c1c040c0d10010184d0000c038102c513142d1841e11b02c0030200030340c1038284240d02d002c040c2c02c9000c00c070955040c1550001e4031220205070083c00d100200c0d005007030180360310225843c50100620740c049200b0028ad407094032081180d0300c41fa40207840b441e00701584080300e940700c1030024400c0c80c0f1913040088914042e00c2500c00c18500400c291340132031009444180425000020302c18000424180c03018080118241c10403034510b10740da0315031143c00843c2c2c040c00700000841789505110b07002404084619201961007186881981c8100781440c0b80d00c20000307801d24112840640c3c1e40120b4041e031007001203001d280056500e940c0c802e00002e810101403091403040450120040c0c404200440c09010102100c202c0e010300b61078450b140030244e8110744c9140d001403094081d41c07500302c0c1500c2c054000483d01441e034881c16000c102c0017081281e20159080c440c0c23805005186800783c0c01107000354a50703664241c24111840304072032065400d22501c00c00da401008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 733528237 1250 733526987 733526993
    0x612080901201006080f010c020705040b121005091606020a1b0803040e250206070c0f0b0a02030604050703050c070807060605060a11150606030112061b0210050903030f04 75
    0x1e90740c1c40012902c034604403010b000080061403c40e080b51043e06943d5289010301142004100d000d01c0000174800a011024000400a490320098400c080c09503807513060244855031100c050701002a400d50884a00d10031000c1c0041c082d04c410395801c17a031401228054000c20280c07607406070588a0360b400a00c00603401c0d030b03580c800035440800e80c2c40200715141c1d0041104042800104002d02901c6101407084c10710649610503030924a5007107440513915250070300c199030045845503000425040000320003449050070742c034000d01c40c0d41c0240050ba40208001061082c7d0b40518024881520100a950b032034400540c11100c003134901c40c1041c0e400384000030008821314010401c091003507402140e0503a0360408501107801c036004820100d0010a045248007000300000c14800c4d2201c10340c4006802d0100c0410224070060040d803990380b85c01c10010043c40b00e650000901904103250034142c1088504009440d205000807050483d8148004140000c00c008103032070140036641450001e070b841d2a0303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 733529487 1250 733528237 733528247
    0xd12081308040623041517013501020304031d0f030c06090310060303170c03010b030103021e0a030b0901060e09120a021f1b0813060b030a020402030405100612080901 73
    0x120744e028104001030548910a00c014003402c01464100032540102e41c03440405030002010202407001c03040201c00401070440d541201c502d401c440700e10b006551420740c0b044c0d00780a144004c59403060758000024002050351154000364400c0000d0744c40054540100d080100c8075000020055250b030244003860b0451626000400310608020100d504861250500c0c00c00c2c0c030400e500607008500f10703215025040b044920900d500401481e00c039481c66060400e0282a0b0006020180c06807940607024030809000d0085462500f40061a2500b811380d03c1c85d20501d07a007021521180e43d5400c02ca0001042588031020601a2110102a1899030108042010b05401460020b401c6200d900d406602c000c044042e08407400001e0100801c0405044203890028110301b03200600f0000c0304001c00034036030715294400e2060780d40008080303000180c800001c0e1070724901c4c1d0030203944107100205000030040009851031003007001e40024040c0e15642d4060185945d13540c4130180c49a0300400200080758826 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 733530737 1250 733529487 733529507
    0x705040c0306081204060e0a0e071b06021317150c090f1201090309060c081603050c100b120303010f03083403020105100602030d02030c07020d120813080406 69
    0x91a00244450f42c6800e61807500120444403240440001403c0c440c4030340c01200c812a20300e041c1c03402c41041d407611800460400303000f0100d00420100c03070b250010b00100c001d41c00040641101048d91501c6181000c00a68032640c801c00440c0c82414201c003544040200300d0b00007800141c0c0c08200aa50f0350311102d080c0750300c080d941982c041841c5c00c070000c440c2d6800594000c1e100d050300001802541d285000342c040b2015070002c0080c84400300784200051403180403101c00d804190141310248905207000d070b403907010740404494140144440c560700c0f0700c140d0b841101109001c5035586ea02001c1d00c5400d40e120b01c403e00440000390791808061008c038040400a000300741600e40a1410300078004091140611a22002035030207040c50000c50605038240078007a007220500707039000040361038600c010790382e4410140962281600440081c03145400c02c0c042e144499006040340c241000301c2e24058089811402005c00400c8081d0045840280030041820a555005240c6031400782014400d0b20100d42c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 733531987 1250 733530737 733530761
    0xb181b04020d061a03042907030f0917091f0509150c01181208071b14071508010801020702030a0308060418050c0301110705030306090402130218010906030c02070504 73
    0x1941c400041c420300c0780c080c800d03500c0910203413184c4034109890300208040c02500d004100002c0312422241100060f2021034000c6080c2c100055001076074101d410140c0b0881c86c0141c0721b0b00071102001c5895901c940201040b110484d6500c049106101e030310072142200e5656940042c2c0c0a108560060402440040b0000381448002d4203180380d191043e03094031241c250550b00303d440d441c001001c200700c6c01a15102207000e03003401081854200b100620215081001540c00040c1450550174400000344081850a0100a44a40a440c4c20038556207601c00d81090340042c00903400080e1b89403040c800c0d6210540c0c024082d001c0c4e102a03031021220140e002d01055401680c1d001c1c0800c0c50183d04c40000c135194450009001e004442c4400c050840301d07421000d6002281c00c21503440050720100c00c0b2580135008031a016400d840718004580c0841c00700c007401c014144001500c2803100b040300300b02d2210440903610b04146030313141c4030708800b622549200b501c0564001c0009100f9440d15420450380000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 733533237 1250 733531987 733531991
    0x7030c090c170411030d3608160510030c0e1309050712030e030708121b0d031515081602010e03030408030f100302012003192106150f021501030b181b04020d 69
    0x20715000c040341004249c1a80341810810003404000034102143d03241610200e50904124191800c1000381003480e410314685d1041201504a4481c8681644a81d500580020071160390a440d072241c084000c031420000ea000c114625030018462900081100c01c0c0d801c904040c01100c2c0c403c1145810582090440030320b0800070f20840301e4118410803181285d01d40c1643d0105840203000001c0c00d0040c4241c0106084410100c8001c2c200c603040080c2c96000301032103c4110251000002c224010240e002581c441804000240000c2c00a5400035501640d07455061030403d0725410a003101015140c032009020506181580100144850549a6482000c1c2c1941e05e0542c10032030391000f0032036451050002c105003000a564101200401c0701d8840c0c4002400c11800341466400003855441d20030400812040342020a0b4451090006128109011585c50301da56100d24103440c608100312100c95584208454070304d5050000558000d80007806442c44c00c0f40e180020a01c0081e51000101d0200d5507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 733534487 1250 733533237 733533239
    0x2b4e03140c0901030606030c0e010c08090402070f0c0905011406070f0b0c18120a12050715060305010e0c0f190509040606150207030c090c170411030d36 67
    0xd5a039918281c400c0342000300e515950b03100e5030005400c0f5001500304108041c07401a40c0300e1195040b0441240030b1109003440040702c0d80502e0030940c9440b41c03951060700a8004a00c0400304805c44002083c40380c030030103146840030384800c0e90000300d035800d10a541010347d1880d4001201d051203c018510940120480890980e0a440c3d42007880001d441001e215940002e002c0401600c0400380d4094401c11140c400d101c1d140342c0d02d81952110811000340403038004540d41c14003280601d00b01e6240c0355014624100396000d1074021401010301d0312094655500740f10600603c82808200d110850700c00800850041e101c4006104100007801511400d801d402c003030109156441c016420300c140d20407034000c116941080c03800140d0702010701c040015907021410900002c0c5618840b8425a08030381000900d04007100760858000700d00210011000e50060103100a2046135042c040d404030054044a0480200e490200d03026155940c001406d0407414039141e0110b0000350071500310000d8482041202 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 733535737 1250 733534487 733534511
    0x20a150b19030803061201061a21070e010e0418110102012003041103060f01140a05040c171e18010b1918060803092b4e03 54
    0xa180d079500151940381d0040304102c5540f80190344540c2c441c010038001c1c40035502d4054680c07030200300f0039040c00b2110f4002c031b6401c880740310080ca001010f0b40752407150b103190309150f0000383c4450420704200380080d0002d51405540e09042c0900e90706180d4034150782c00359030441e0316401412659005c005046540b50480e050016043c04180080c9038903980546a5906140ca803001081c641400c0c41c030301a4005004010300303a404003440d2811a201c1c110040e02103001400001c1c600780c103035000964481e1800120050990740440e00c0350010789040c440300d98a40f200c09980801112028645a40c1024000024007181008144412072100c400011a901c41202d0028950a10218025420514244080007040058103000300880c03103480c0b080140c0e41c01c08503602e8403403003842144d500418921042c1704200056a420807085070b0141c0b40507181640501c0d20b50b400c1100c40e040000009013417150102e002a03205224850500c4058803500c8501e503a42211010040c0c040060090650380d914900722 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 733536987 1250 733535737 733535779
    0x7030b0307080d050d051005150901021c020d021b0a0b090402070807080706050a05220507170f1b091b130b040302091510051c060602010507020d020a150b 68
    0x150711215150581c41c5c01c0f41d40034003401c032200100703801c4500651a83c100b2481c0c540c03400e181096140e0711102c0342e50341d02010042c3d20385803a103403c1ca110b190011034500d0307829901280c03000c2c15103555800e5842d419034006100b002a84004130140d489107400604101800094000703180b4080060405400c0030305c0ca465407015500403038802e598582000682c08208205440381c035600020040040110b420400780f400c0820b00010f105040c07980c010309040e020300408000400041c0002c40060000d095070100d003035243c0401c0c030110b0034a13200b4081c50b880c42021000d0510700c940409000d00341a0758900744200e40c01192907084102c0b0100070043c8071442107100911802a0041e104c02c2580e480c07440c8103014020200900d441d00e1009502d24901c50b6603903142c02848001150700e4960703100d0304203952600307150000c480e035000300358a44030b0000340f0765406400c000c3c072490306ca4090b5050005800d0040e6103d0b1751420300100031103413a2042005803040c17039002080420001d401d6034103180c041c1c101109 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 733538237 1250 733536987 733537003
    0x8040b061e0409231207080f16110f06030103080d150803040e161b020f0102010b040e1b010c110103021c0f050123010e131b0908100509030307030b030708 68
    0xd0841082480b801c2660210b44c540c1c02c19800e803000034102d9111203002d01c22580100d88009008010000e0040641604641503a0f40c074000642c800348c0c50201441c0c040e001c114131040d6980a03141d1041052502e10706101601c0c1282e412460b030703618040003100300300d00070040807040b034001e00d07420240843c01d050700b08040c1c0040c08070b1044d030320304500304844641c0b071005480c11030340308001380110f0310b40c0940708030b25140401d00e9043d038112811411280040c2c0c05443c010394020307041880e00c0c0b5190302054000a031050000428071140005501460044401400540020f42410906104805294880d900420740030b8502c4c100380000c1011000f1900a4a0030b20750218071658580340140210060f019100d450244141340c2c01d07400784c9102d0000703800c1c5049108114490304100002e14440c1c4220f811801c00000814425a04c06030448005000c94505001d40d0102e4801d00c22540d81541c1a032180c03030b000d125001c00442c01c40e660800c04a002c1c0040b0103071690503016441c0002507400e42003001d04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 733539487 1250 733538237 733538243
    0x90d05180d0c080a060605090103030e121f1a0102060705030708060a050a03050102090901060203090f1c060207030206070e09070c30260402090403050d150b0c0d08040b061e0409 78
    0x30102e0004d03802e1910aa03802c0e80c000364030aa01c1d01004000003500110b51400241c020b8070040d1501d0120004076040c149615003480300f04010304800501094140d100007000084003031005030140609004981d80c000c11100c2d903010810401c08100d405005065042d4080c00027042400b56a45480100d24940c2540e0b0007111980c0d004604044a4a0705111301e0b809440079200650611041100113804142401003987c024080d4800b080c49141551070303102c5030035030407020031b640d2010980b50096072280200e0785c8800241d40d6040340141131801c88071045c00341c99287e80c0d41100740340c5a100c6121521816103034220914028855445607065280003050301070040d250039808560106451485a40e00c88004205008000410006a0b03442c00c9140e003141d0945411030322084819206030040c81c07022102d910400100c0c6e030004443e400e443c002c108100b132400c2a17134000b8000390310a441d50f1500b520000d01e00d4421000051046c2490310700c04103400141c0c55206070904e4040c020400b1913140140503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 733540737 1250 733539487 733539493
    0x1b260a050327241606021809070e0a23090103061a0415090e03040e0f060a0e1506210103050606030f0d08010603020703050909130b090d05180d0c08 65
    0xa00200907a0350002100080291204550140c0480f1446400400e038821441401d00c0842d06024a00c801201c1c2c414684e80000c0c00c5546102085038a0408640c01d54014420003004000840c045d00c0307146840b5846070060940700e01541800d0714001804009200110350111910100303060780c0d999212240207502a66002a510f00e004002030346804804084c0c0d4061030400d0712402ca802101c41001040700c2d0100c0001800c07100c00c1c12440d065119582c0840c1c0c01801c000b00f40201c540c1d1200c83c0c0e0f0301510b421180c0180555417100312484d034820403110b2800c07204450085c1800d505102008144041081c00b01c007502003407041602400300300a03042550309a02000400c821410200144944080c02000070b001c0c1c58aa040018980441406038508242d0046101e0742018003070002c0e82c1d850503004091801502c0e14081820161503070300c0e4147d480d2140000411f010180c04500030001c8000e41d80e44030300c1d021500d0402600c50032803813047c1d90400303400c09154020035510350032080036001100107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 733541987 1250 733540737 733540777
    0x4060516020616150c02010c27080a0303050a15060c0b04020109050a061115060a180f0507080403031401180e0703050102070b0f0601030c050306010f0215070504031b260a0503 77
    0x20f00800ca41501c00d1700000d581c9440024000da640014520224170101d181c00386c030030007003481d0290100b0310b55440f84000d031040303182440825415402c03c610503058400100300016084864522071802c074860b900224449941010104507800040c962090040c141040000d03502c40114016524a034007078400100c1c0b800c40d00580540500c041c840b0001f000b290030131030b403d1510010b0030754181d51140410102c0441100401c180fa41c2d0003140480c0d103151010030461808070702c083c1c900141114110000783c03070560700c05140c41c04916658181c1d00a00001000710340e554034000e000b000c0d4030610f2074852080c0d007400000039500340000e2851900c2001803030107600345000c80030090300d00a0815814141400d05c80040c40d030340321050701da000a091070180e81813407409a00782d00744005860030041c4049041c040100b01c40d04900104122482040c0324001c1e86110740240d030311801903004640d460b10081450b150f41c400b03180042d02030204200b050750f2800940341d070b48901e1648401c6030820480c8a03003203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 733543237 1250 733541987 733542023
    0x14010e030f25050a05090405120a27150c03110d02030405120604081204060b0d05030c0d051608090315070e10030b0f04020c1e2104060516020616 64
    0x2c04001100006500540100c0c24180000d40c40c40b241d0181d1805502000001410b00c00100114514400341c0c0e1110740c2c2e00d0310341800040c5459803654080c0c013207040000d11002805071000e00c3d88122040f86050700401c07001d402045500c0540d10078143c0421243d250710341c003c1e00c4203110504480f90780e50002c4d0380c1c0f00d1500003409a10072032540005500d4120000300004103217480304403810490380340c0c0c4e07406c42c940c0d4503e8a00010084400d2198000034003c0d00c040c2044000801840020051400c80d8000491040110342ca4803d00b80c0c1c0c441000400608900010301d1140036203080071004003650018218824a007001427811101c440009001810000706405d00e00c2000b442212503103402d010700400b10000c104552400d0600501890740022940c0c2921380a0080b90f11001c08844080702c103044040b100c555400290700c2038001003a000f400300d09002d403500101c604949941c1c4616041404000d610035040140382c0c001e0743c00c200e080007880168107251445e80007043c0310344200940410404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 733544487 1250 733543237 733543273
    0x9030909012c0c030129030403080c1b0f0105060301020408070312210f0c030c0804151116150c09060807230c0f0115120501140c0d050708010f14010e030f 68
    0x10015100b081d046c8405440c100c01c2d0100320399005415003840c0181d601c0300c0c0c11643d124842c68000307030660f14280d503031750803a8580481c5007990058500000d1105844080c01c0500300d00c140d02c40d40d201c0c1c1d44080e904100042d0510040c100fa0384150030250404094613040080e0b607100b19010041940d681d0860124100a500ca051500001d0303213002c1003c6080d851028098010107030005d021520400c600d040c1c50001c0d9082442d01c0c02150f0325042e11503884202109510344002c008480c2c3d82c50354a841004402a4410359000491641e142c0d2515880c20300c007a242403401401200820024460400e00964602c00c0400024100c84c210307643c80e030f14902c0e040c1c00c1c41408460203203144d0400c641d030410483c26025a4003034426011303840380180d56a1a00350b00400d41d001642c62012000d5042100c2c03030034108040d0030899080b80d0103200942e00c2940840e2284801d02551101c0c1c54255814000504000170312100041d044c1000307071031400341c80000f9240c16070720000381402d81c0c015504856598002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 733545737 1250 733544487 733544519
    0x304060c0506070c03090b1308010f230f01170715050703030c030e0303060618030a0c05030d030603020603070c14070f080f01021606020903070b04030602040e09030909012c0c0301 79
    0x9413800b0400500030365001001c0e0180c41c428a84c5944003c01d40d900c0050748110114020b000c40c0000300220303400e10000c9006405000c242c0052000304201111500e40c503911610700c81e02182d110b00b44144e00b84a00c0304aa905a0503240c05e282c400c20002043c02c000840520030000003948800e038492605240040c161040f9175025410181400000244048000141e076000b100c2250390355194aa850804e0400007800d400e000d606219a4100034203000b001c10342d0f94103588058007030300c12002d515101170f003da86031032000a401038000c100003819148210310714107001d0311903070b201e4821203030f000d814910b07008050b0009803d420380c2103410001302c0c804002c00340400c949007009509000349654600007940300d40102510a60b00001c02107581e540030702072600500012603000c2d455a8880c18210029081400344a003558248400719411400001c1034032811070300200f40d41d8440c0c0c2881d09400e105c0e0040c40d003003102e0172848066040084101920103103c1d2841510641c1c8a41c50a41080c03454502 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 733546987 1250 733545737 733545751
    0xc060723010b150c060f0a290a12120813080a030b0102010c020f0a29010f0905071b020d17070807020a0b040e01030b090304030f030c0b010f0f09110c0304060c0506 72
    0x804c00080340c203040045151540b105000042d0840d583d641c5d51504c019090a0b081c840c91014400c806014140440f100c19000d003000740e40070301496840c1c40510a540309108800341040b0742e01040d032084c242c81144ac40c2e50040320700b05601002c144640d0b803070740700fa00314013000c1c80400e031500d400300410b50382403240c0002d00b49070b44000c18020111070095515513007a141c002d45200342841c40d5008600c0d41003550b95121051050907402907135240500e01a0011078094409043d04290205440b1481a40a02103030000417424110071116542000700002911008484600865038000490b00242000d0944140103840030b5aa4440520403c18061340c0741d01700b030403009001e00c4140128140c00c000340341941c1c4c0c844401ca0490300c0310182503185020b03d0740018061300108070b0032401c06038803503012010f141c40764011007031503625848040c59a11040c02020103802d05200e040140c01c0e0030350000c0040405100241d49000c1c810f030180ca066500a4010340041004000c0b881c2c01c000741005001e43c4200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 733548237 1250 733546987 733547029
    0x819021c12032f0c030405120d09081204050d03090504021b070801090f150603050a08040602010b030d050d0902210610120b0114120604030815040b030c060723010b 72
    0x41c04042040070303e0b0810b0703140a00b0100109600008a20400448000e428000c1c505106800f100001a990308560301c1032000162110100103120308000692450720b80d0355940141c2401e040074180681c0e1080c0090640400c0104c910005464807948000c250035000d003a40384003044441170089262090a0b4064101a0301d841d001e480032034450458a280e0751383c0700c09001d0600c1c082960030000703070a65800103420390040380001810080c2c003600030030440701aa0000d0101408103410140c50742c4810186a010881c1003061070f03074110150b400710134560700c0200b652100c510034050610b11200511000542c591082e03003441882c000c0120314100030841c0c252004c803143c0403640c40180b201c1040c0301d05540610f000e030403011740e1b0740d5401a24880440c1c0108a4000346440d00b0000c0040c0d40646607019102d072030300900004c9003072a0042588449000c0e0041c1032103100c0340c042c037070707681d10410080c0e55003a40030210b9008654018a110401c11161001007a0758440408000001c1d005031342c1507030a86 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 733549487 1250 733548237 733548281
    0x130c09151703030402040203060312030901151707030b1017010605091b091903061404020906180103350301090c05031611030904060e1f0819021c1203 66
    0x1201c008100c9900503410394001d40c42e5128003000c80d107040901044c1c465589004820840103206c15402004c41040c54000d00c20600c2d40c410030004000e03280c4c46a9003140d0811901030000c15022280d0a420100c0b1240341c1154940e12405094090b0740002040d002d651192000c00040c5043d5519035084000414150300005600028160621481d103a00b80141c100811100c0031441d030003c2d8500542d0414000d00009188100008898204407822407090000e44082885410701c8001103400e0341e01a61040d03044d90035502c4188124541410740c5a0006500003144075180d80d085003180e80422720907441e03842e941010360800580d80e0302c5a4a004200042c001c01c081c00c503000c20000507202d19030a2081900e41215062821881000c411b580c10a040020008001102c06035080c403984802c031114001d00c0f13250682e10000185c40c495941c0ca07600003418020010b651207160f80b1014030040c400b900d10640301c0040b40c0c02c0c00040505480c4100d1811981000c075070140910a5540602d0307280c40d400c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 733550737 1250 733549487 733549529
    0xc0306110405010225120308091b0f01051605070b0d0b0907050a0806011215060801050301050906041b0806250f0207140d060501090c11011a09130c0915 67
    0x200e02020318211707520307042120200b0404403960024040c00280c00b600341c10034114140580f03095825140b6006500c500029111440511404003070540c400926120700354a442d4011a1541c2140410947c00714103120038100041041219800a14041040c5500c3e080c00011030b0080f03a44a600381c900804044003001140c40c0e10004490003508282044540d584a03c40102d50442561182d85541032030116640040c0d0307903020540c0d04032172465503100303203684e2a141032609958003510b040905600c8880418005100c0c0c030509805000c450380303032140140d95080440d00d440015a0040c00c04c20300981d802e2840306e460140c140145020341020310340c3c0040450000d580719043c0c41000460703d6506902c900340d9440521036030000d0f0300020140300a5841e614900010142744003044040b4080c070034a02503095041c0035040c040020440342e20a43d8010006001101c800200071402e0b240c401604a00016407a14202000d451100000540300503505410340c9050502d4001c0c4070000d0310103014a0507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 733551987 1250 733550737 733550743
    0xc1912032a030b040f02091201200f071e030908161505040302030a05060703050f16081504090606050102070902040803040b0d0b0607121d100f020313030c03061104050102 75
    0x1038451201c95184980d01001c048005102d0b410000c0d0780a0700301101c40b2102c01d8203402400c200380c81214210190094800b819080315601d03400056940c14001002c0801105c2e28054002c00008821280c03a0010f155501c80c8140310724181c81d05044054407080041c1940305030300303101605405000300b9110035890381c2c1c51009803031440b511514400713a4001c000918445c1c401d0744d00031503020b011030720044400d01d0485e446400450707403140001d18120009419490062606005d009201b5003015180c034030101c00c9074005001004004c0507071300d040c00341e151a165441609a840d004200000d0224200303400203040400d10f61000f503440f030042c40b007440044008000c4904940103090000d95442d4000121b0014100002d0603650001002c07400c0401d00012a24400c412002c0e5580c914904d000d400d18050354a65100025401c100d0910090056030700a1018002e44405401224103011014842c00303150100f54000301c48142600000f001040020f00416103c00c00070400306060034240710001359 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 733553237 1250 733551987 733552031
    0x5012d23060f1c0308150a03230307140f101a04090f0507030305030912130e0402010306031e0614061507080d0203070503190b060306150c191203 64
    0x80301e8419120b440310150380f50304a4541c03034000d110018040000b1400c0c054400c1c0021500b03034280704201039121186203031000102d402e8941c040c440020180b0103000701500d132180103080c5e074202d01c010403604000c01c4812414211024944004003020012a0070b801e05084500d0000300519007001d220399011034840407034120103582a10006110a01c43c107241c2d105002c3e030300b005850b6010340c01c3c0120500d80d02c640250302c2280001c045446001090100414611464200044140c183da9041c0031840c040120303250010b005240c040f508035180e46540900302140906d07600f003031250114200c100002c5010f0032030500e00740c00c1c0c14059480c0c10710124041c049a5500f90b940c02030000307035843c00c21152800f035454402d10703040115182d181c41c02024000c1e034810348128803042203903560103d4280c0140074203224003001400305810368951006110300708241c0303c04002000c0b01030000d0030744942c040254000400503c00040e2400506041400071203117251503107010141800c102c00041c0c1d070340005000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 733554487 1250 733553237 733553239
    0x60c09060a120c0c02010215091b03011e020c070b1e0922090c05220b03011107320a0206160f050a12020d0e060705012d2306 55
    0x25594080224044071011164868004443c1c50280c0200c01c069000c000c0304445032007130302110080854400300c40540c0008803555220703a40044400400d9490b2031144071016000600003003111251500720603007550400504c1c52a2aa02145030050080f04001c0c05001b404407140c2c0900d014040140010641c01c101d0307400303010100008801d0465114184540c400224a0302c0c1e80c0b1501d01803a04c000c000e03060325403040e01e2044440b00046003e1a0508488003074040280042000c43da68030742c1c500203058010f0000364155640c0c80c1c8645050640d8004000452180001c212400c45d10081000c11401d0070007101005954000d0f0140401c2000503910011501103481c103440f00000c0180901d5403544000c01401e40ca40d98015a08010000a0030f181052081108041040d4403081c226035500f09002d000d00050320b58100c00c070a604194006003841d50240c4008505040c91030012240302504a20101c1a0105c5820441c1c1c20038030b07480f8a4a2400080701c0301d000e052a0004100c000381005400300d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 733555737 1250 733554487 733554499
    0xf0c020616080912030705010515060a030b0109080f060a0606020a171c0c020d020f010b100e12161703090a030201080916080c0f0301050f010b0703030b2e02060c09 72
    0x10b111002d4151480b021000b0004030381d00c0303400b10101c0d8590704015003c484035801c000110b01410561007119002500160a481c1007045055045010740f01c0300901a050102c414008101c017441402045440e0020b03000510aa06040303685804465150b40900110340200c2c00b80300000d00425040c14150927281250745d19954100f24140c4e140d200040c1040c4000d01c0c00254003082a00440c00da00c0712022902a120311004034010300d07090350b2056920b1540b1070540aa203080f824001c002603940400081c11300c00e894140001c0f1035242094050f100b10b01c24081c4a003c01004c8805000c00c8662007594000c0c605212218000c61244500d03400000e040c00b07080300c0000c0c40072804124601f400e0307011404041615a40345141078460480142ca80c0c00351000c04440880d0341814010180a5018080210a40c1e8a094030307106094111140441c1007617200c5288130050380d07070280069102900c4070310345055205600311410316000c2c4000301d1410340d00544c081085c080b00d00303c1a0f800d501402d45003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 733556987 1250 733555737 733555777
    0x13020d080f0f0703080712090b0a0f0207052b17010603020a12050103060213050a050a14010c06090813090b01020c010e030f060109020304051915090c0e160f0c0206 72
    0x1031000c190082103002010b030500420101e0070305038010f0825008500d80d86170410a4072603080581c050301c0c03400070090545a008000b190040c2159840748004840018006040401d01c0d030303840c1c3c00e00c0d4401c652004400c0021401000856040d000386111407000c1c180104010f40f840c03641a41c10ba0148959000c2c903501107854072400e8042e44000f00f10b4210b03980100708544e128940342c0c2c0250030181c1060700704840401d021400e03003480c240350429514001d00c240c801c6843c010b650810804d8100d8000e042006c00c2c081e040001d070483c0a9000d00383c0c8a03c441c5034071681001640e0000b0341c0c256020b1400c0074185680d001d5140d80101c1c80600000e001c2c6440c100d5080e803100030a140041007041c4501e944a103600016a20203640d019501643c8a01c094407985864851141c0080c01966070250404030300c80c1c580900d41c0317080e0f440f030342641e0b1141d00e0000d501c66549010005400d0100c40c1c042e1213241241e490300b0f0701903200403030340d60f052140d050112010510360041261400f45888d03c515030210022 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 733558237 1250 733556987 733557007
    0xf0a06110f07061a06130b0a180609031b140907030204080313081606211e09060b150d020d060503030a0c0303063c030210020106050913020d08 63
    0x10498564000041006a8882d000d18120700140b01009407485862013000010b4802c1c41c04038100c0e03180d00c005500340c202090030820b901e01140e000d44001000e01015508511211030700d80340039002004181c40301c80f0380a1860420700c841c46507801c05400703038854107042441100100e1101d4244a0740c26070300c3c1e038103d0355045020707030003441190072400c01c83c400401c900a00a8011004505a840c40c2040c0ca1415469503542c05080c81c45000d8040030845400040d140c0903400954a417000301505e2000c00c01d400d030170060802103580761403600d094039194455070052000a005502003c2000d84803041d24810b0340f0342064043c002c11030388602440d00026118640e10303550300a14080d0100030309403030343c80300400006480c00c075020004401003420000000307206170740c4404034030961540000c25030600040062070310024001440300c101501c0e4104010016880c0c882c1c0328511418141c00004a032400c003401c00007072120080101500d103030020000c0c80107890794141403a40d954030944d081c1d00c82031025 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 733559487 1250 733558237 733558271
    0x30114130501080a0c0b040e0f041703040305040e061e040e0f07140907020105100504091505070518031c08070219030903120e030a1e1b030605090f0a06 67
    0x103001080000c0c00e141c0041102540450402c1e00e80c0e00c40c0d603407070038074590796250069a13010342d00c0307542e00c1079180340009a803902c08182c80a9000d07200b40059142c3c4d01480d085805590020b5030305400080003c0b8091100c2c00201c81d02e070382c004104440000c00030140d6a00e02d020440f0044249000d0f9440b10310020118108100902005042d2002c1d544010b8031026600301e4182002c80e220b102d0b001d04004210018010700c29a03001e5110030f02401038903030510041c000605000c0d002211401c41c0801d40300b0324400548134450140d082d07903554a503190643d200000c100300c4941e110320b100340c00840300f0015130300c407014601c1e881e103509050100c40c0f50303141c1c003050342130035200010310f00c500d8440003507142099440b214400560348141030210002404039012240460394280d010f404d40e00c000c0702c100100b0f410074411260800070000071003150b01c50340c1d18441010040c041002c00c04a01010030302c10080316001d0550f000f44141c1c010403d0195129400e9070321040c03808003410540d502c0500c01c441700101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 733560737 1250 733559487 733559509
    0x51f09021b010e060603012a0806220c03060807081e030c10050f10051012060807081501090902060316050702060a0e0a140117060d0203010e030c07050f06030114 71
    0x2840c02040143c0c0904600c070340713681c42201c03100d109504c0c0c40d4440491000c40d4040101c2e0040c141001403100700720307503400d5410700405440d680d4099512842c2c00e0522035600c0c18212001070110002c510242004405001d484040d00540b585070031a1409101c205400500d5010174001c44080c0c0d00010b450444150461007042c2c040f034114007038110b4121500a803508014014195030320844002d507500c4241c0300c82e802c80b0b40140c039842101000090450340c03040d5200e042140002d0f40014070255903000181c605852640300340050380044005240c0703480090096401460007803824008076a2a50006425100051a0b02000d103041e2030229080d5102d281910700b159805003040d80d030348030038100180c00305608441e01c82c4906070b0b000d0007251200c0c10304103400c440001a11180f580010a041c24020b902d0007c01c8030341c1000f07040d050040540e03002d010b1000d11030310310806142e07180c5994140906000c025080180030780700442c03004c16181c0b1031400f00c90459460154011900f48600002003103a024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 733561987 1250 733560737 733560787
    0x1c14040302041104030c0503010c09090221130303140609040f05011116050c01090b09010f030e072c0910050405250609050f09011403120703080a051f0902 68
    0x40c000c0991150b82d060001041940c0c05800000301b45035803034041500340c4940c5551100080d212000401c40c0d03446540107891485121011090700307000d182c1d914030030403404842a4002c1c1d8001849101450f4052003041a521807481c4980c81c0b9242881c0480e44c029005070000b41601d086030075107424444d0a61000100198103a201e540d075801d10704254007101280c502c01d40b050b00403081210b20030340c0120440402c1b644d29080c0a401d1500d07000040d00c0b40ca00e075640240a0540f148080300314904144900340107040300454a0315005032004121002d034040c40c1ca2403046502510a0084400c400103a0402d580c90045012902741c0d1f4924001b81003d100703a406010400e0100d0160004100480700041590040d0340d480d043e15644000304080e030708010380c1c00340c1c110180c3d2005100b03a0300c40010801c54071101604440c295805540c0750380d90750b4000e072002da0009601c5000c1c07164104190140913080240c1d40b40000700b00d0580ca00070241030819109904400e0342c00104060040202103007040d2040e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 733563237 1250 733561987 733561991
    0x1050708070f0806090105060d1e021305010c051f27020906040b01050306060a030608030d0207030807090b030a0b040b10050d0b0d120c02011b03110d021c1404030204 73
    0x204048050a20101920035001194860300202507051180c0441c3d4802e00c401030941c0c0c1c00d6440e00f418000349a1110740b0340841c540d1a00082d03040815185980c024800d0b5000b001a500d0058010642e07010456410035130400025517a80000320f007000600407895110b1900d029042e0000007011760080403071542e41440605241001c0d2200711240805540c0c4900a031b881d0007465903040c040004403810000c140d40410402d10226125080c0000a40008201c0341000110507480b0380b03629203160032040215052a400003061820103500596442c0c2068240c2008000c4c036092100c40ac07400e00005040c101c8290713070741c0d107228001c0c0d440f0740100c0c0042c000501183c0300c000c4a5403009040341c0c0f00306a0300034840d00b0075880d1007890911409800c1003540080b402181d106800d0030803a402100700300140c0c10071401c80008242102c0030403076810303d20301c00c1d101e46c400c04045190940c1031800c640c22000554008000c3c2c1d41c402103a80000c4080e042607031400d480000c9044040e9001d501854001070b412074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 733564487 1250 733563237 733563241
    0x6150a030b0c090a1d04020102010c033b011e0e01020f0702040e010b12030417030c03070b070302130b0403020315162006041a01120206040504051312081b030f06210105 74
    0x10300c0c00103178038040d50013a8000d100035005064181d00780c82c0003505402c2c599281d5610400707500d07107142e170310307640d85217040c0502a2030507640c5002404d41f61346550108034562880442c011030308861155648182d51003009504007507c07600402c0c014001d014010740541c0d21034200a02042c829030007120403840c0101600180000320300102d540380c110f0f004401c622070504c14040c58100d000019201d0f0888018019803920000d5941d02d8401c10000d020002896000d10003540c1405813107002402414142d2619a112132a500401d840c0900300900400b100c8040340500586801011300348400c1d0090b41000b00c0c3c40e46051400901819441d0100c46c624081c4009000411080c1c20b102076403551008407a00150b40c07035079254104045540f07402507001c881002700f0030090800b50003066001a44a20084801c1240d88661403d400000e10880001d168002008100c03142da0110802a01d06c1c01d8029045291045049005110103841c2d507100d1b05c1c40c071410b00308842c003e070610001c42c88a40000d0000d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 733565737 1250 733564487 733564529
    0x3030907150930030206090f0f0c12030d0204230907200c0d0b0403030b060f0307230a0c0507060c0c030204020306040e030c1c0c1505070e1206150a030b0c090a 70
    0x6d010142d5411410303000b8407180f00005100054204030030040040030305402080b4200f00200c44c446804415541d00060011001c101128400750008292001c0c18003401c10041180b80541072a00390010b00c00c0c3c1041091202c030b01d9100003461382001a0704000c0b032400d40c0840c80c042c6031000c00204281d0110a1002d2242003003c0b94022602a034071948092013107050000401c8907a000e02801800c51400510004440c01c0c820740e110711400094020701c40c1c100095a00312806035002c4411400802ca038220325604000082240800401ca00d2809603040c04642d0b8407040c1e090064407010744250303004008110325690b41e50000b440d0060840813203030b40e40c4014442645400703030305c1d601c60107880b40001f4044581d405001c1985c44642d01c00b14803441c2d65600100c00d0020400030744424104141900902c2d55611a80c0e1068146079040740241403074035200320301103400003034044042d01401c207443d002c0000942500455400c0300b540b9511075100c03051100410401d40e003e40c45078803480ea08240006d11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 733566987 1250 733565737 733565743
    0x51204030809090702010c020a0b0a14010e07120b0303070b150904050d09061e270807080c03010b0105070201050f070c090204030b1609060c0503070b0108030309071509300302 77
    0x16508050b20143c03c2580da59009a00f25407200c24031002581080c2c914a00060183e100503600805d44203000403041012804c009014802f60409119542d14000348800640c1141958404507a1003034103205101081c40071940742d024088008281509400100300c510315800088200c190010381103868901d011304005545d0707400f5942250104000c9000481e805104103c031203001c0072031202da44031204100c2011141c0c40c00c0c1c0820f5000800c1e4100351010600f8200c0030303c00c01486e100c401403d01e0307402e00155606082103907199510270382c07400c200000103980100c141c910b1f0b80e4090800b640c91351040101c90300e0300e101d8520020071000c4a2030002c9001030a039400350040d28001d000311640c0343d4445201000e0041c5c51402c88000c41c4103003d0421803188103070000d04025201c0e40981e81085055900d00700052800c0e00170711110f4001004000000f0010008100100f02e41110102c0103030070700c440030b00685120300590411800c00c0030f640d506c040703e204080745000500181d40d02c1007081e6040c020741b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 733568237 1250 733566987 733566997
    0x30320030d18150603110f130e0304140105190302090105040801090f03080a090b01090f14010906061e0e040203270109210e0f0a0e09060f10080c0103090512040308 72
    0x45185040c0b000f101415124428441500d17030040e0b25009030907084082100c0107800f1800c80354450038460340405000300d0341c0510368110301004025038841d81480a0f80440c2480c1048450402006000c0041c2020b4440e000442000e504d0600694500c14540102c3d80742c45190056242503080c1171140e0104055507100100050007640c1d202c400d5200d440d540402d07581c03c19809858200c8200c014040440568400400220655000203e24800c46c1c0140c103950f01c00da010750955541d99000b0410703980c01640d480b160742044841c0d03078000e081c0c0d41405009400030140e9140030b03e07404400030300c444000c010b034846800400b09080481d0901c024865010f84803c11040b1240d55210b0b51144070325030989200c01c040c40c000d4032291603c0303052405000b813160401d00340941c001d444260019480c044010454042d4072003401401440c540850b00581c008070150000600c0d5941b41010400d010004c60303840c1c0003810920340819101c15505009240406429529055010014001041140d4100186 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 733569487 1250 733568237 733568243
    0x705070803041203022a130204050d061b080603030d0902030a020d1203060504020a0215040615080a120f0801180905010c050a0e0f0f06031e07050a030e07030320030d18 74
    0x244424401103607004c100241d0219a0b102c00e60000f651b4202c0d031901402801d5039205030307500141441d680e480042c0303c00c5540030043d60481e0380c666181d5511080203600c2043e044140c100381e041c0342891004260303a8800d00002c540d59565442c5903004640d400e0140a50702600100941110046800c015100301006c51aa00120f480d21200041c5810030f8000d0342e9403209503402a0000003613050300c210031448002e004585541d030300c6081101d44948100c0420240c2071800c000c00b4188a58986541900c5031145d1110920040140c0c40e40074a90090900b41543d8002804640d9001400c000001514440800420365401c1172242080103511002a01c40c4032a150703101a862211039050103a164040034a40d6042000703070402c1c0b04141484230096403c0804444113000c100086d40485203080000c0d00c884002400c001004481c0b240c0c10b020381400345403140c0140a00c0ba103159000340c84251340d15400703003003d50f2160b042445600c0500c1540c00314444400c041c0300c40342e40364507007030b2020545203021 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 733570737 1250 733569487 733569493
    0xc07050318040c08010b0d0c050903030409050f1506040b07141b030c0a24050d060e0103060b06130608070903050105040506041b140411040506132612070507080304120302 75
    0x100d0140c0e02c5504c01074120b03118507000601c0c21002d0305925002c0c0c01c121f2840c42c1885401c0144d0221078030f00300020401401d03a49400216800d0140c070780308068501a003c00c44408400c0c2004a0035a6190200da08a42a001300c1e1aa509882e1030414120311002080c0302d42c0c0e0064900f6482c0c000d816050303081d050501142078501c0c0d14030001c200011520b65014003407645c030151070711055400913107006c2002c904280c100b803428505e4601c0e540c1e00f0b48401f50003c1c61000241401001000b000c0d0180c0b00c06140212030590418026a07600080b030416842800c0400c9009030100380e040380030300e040c203000d107400c24000e009900c1d0a08000c0d80d01d4205542c1250300d050741d40c5440f400d1100e203840100c107403a09480b51a0485268401f04405460030140c102c4126031300b000009056075404000340309100203031800c05503580c40c28421204040110f145840c500010601d590890900803444500d0690215516038480b861030402d10b252224541002005100c00900450800000061840c40c14132079421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 733571987 1250 733570737 733570751
    0x70c060908190f02120f010b01090f03080a0e010306080a301403071814010e04050c27060a020f06060a05090f0916060507020310110702090c0705031804 67
    0x300c1a903560395540307459200e02e04410080000381d0750514480f01180000c0c160740003554601001400d2813040d50044080e82e640b0100d03d003031960040f07054001803c013500304d255454a1b607101c6410318803511040e4010410501707802146d50b07001e83d200c0750203440e0240840d0000144ca1408010020720200300001e052041d1800d0f007028203805a00d02d440d003070303141c0d220518549645054080e0b500050b0020003441b01d43c4003400c020aa441001d00c0051404414003454107204a002400d03505640361071600560a00081102000220003220b040d1046000034040320010740004590302101107202551000c0001042002c01768005010b41403540c40200f969515110b42c0100202c4a00b10b1042c55080350140c00080c0d0700503104508070f6840320180b0103495040c5c6010300042030090658011001140340841e0240541c00d041003628804d2090843c00c11800310302ca40142035a0082100003846000e01e00c3c000b07500a0000410340784950b03440002ca81d100d221442104500c00041840700d80110300d001c5c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 733573237 1250 733571987 733571999
    0x1050307180b280519050d14120d050118111e04080d05091201020304050c04050a0b0d030915020102030603060a0b010c050706120506010e010c060c0903080301030b15060309071e0b070c0609 83
    0x101c1d41d021284021f080c10034410050391500c0b4540c9051903070211a0060b6508007002d00c02c00300041c02d04030301d08000007035158144030b9a01886030001c051200c02900d003220174000c1240341002c44400c01d01d00740041c00d08507036030300380340580b80704903000350240b03001d45055000f881d0707007003000341800e4107088030804a000700c5030076002c2c00c0b400100c0c0c01501a610640703401000b802c00754011a00085001e602007001084800400d2400840c160120005100c041080140d500081031b201d2280805100035890f40c100b200c00280d40c0c0101600b01c009080d5217002c241800d84c09401e01e18011507011058844103503441201820100410110103001403e0200240035584650f0410681c2c07403058507072640d640d055880d0700c2c0003000301001007000d104804d040030001c111640c0c00343d4000e500c6203101d0015490805800c603140e0010b05070300ca004100c00d100744400c1d40000308008050314445c2c044040888a1420519151440c5501c02000283c00090080c01d014080f00c000c8180c0d6120386034130034003d036110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 733574487 1250 733573237 733573279
    0x2043b0c12030d020f070203010203091f23060102030403150c1b081206040b041a030f0a24060506071103160b0d0f020c010213080601050307180b2805 66
    0x84151910b41c00030040b450105036207601a09242000500450a0901940c046402c90b441501c10401e680d10041400c5098a1501c0f040f181d282d052803000c0c44012412032480c40c0f00c0074038080b84010080d4410010300540d10030019030b001542c000180102065038080d0400041400259900c0062030340c050140d0074480a03042c01600c01e45c4420001d140015400c0c601d10b06d24401380601d03500036120113400342e00d9130f038038000d0b4105803200003079110721940300d5410035103020080c01440e2425081182c015001c6000185048138002c449106540343c0281800c0350401403c0703a030005a030165000c60440c0601c1f003081c1d285101400141c086a603019251180300000034094411140070070360070070107a007001c0c0d140e8000484661007240c0250520070403071405800d82c0c000c0e00703c294484101c04400c11501e00104442401840c0a070060100c0328100076400103010060340802c0365054581030710205035121082406c00310254842a103103400c0820941d04e03040241ca108080c42800080b0800301941002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 733575737 1250 733574487 733574509
    0x3020a0905011809020d0b1207060215090309090705071416060c03050c031b06010617040201031821030c03150306050408070b04230a02030a02043b0c 66
    0x903100d092250385010011110b1940b40c4026902c009902100000c1000c070500150603407404100e004564510b200d010701c11350040e0322001c1c08466110500400c8540e4003c11075552035403081d4011001070303807031110091451207000d6040e900000e07414200107003e54450040c02c07510788102c440c21100b040060900d552403141000303c201110000004000701c900035070400384454400e050890070404609080c0342075802c01c91134030f02400f0054088030201c50040c02002d01605032420600c00c04003101072101a140b074002c01c000e0601d56102d40d1800035414619043c2c0325140e21403092030540440540d9650910340d1a000140030034107041c039203c0028061b0280c809200400760302201c170079145440b88000f92101810a403070300d540410100000c5841e0b8182c45229070301a5403200070880c3c40da05071000241c014520600ca507004141c0400041c2c0c0c02040c6050150380488001c100c5080081c1000c5078014280b11800700080c80c10300c03484040d010300c03180900c543d40c0c64003511000c501c0e40c414400f0500d0f03a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 733576987 1250 733575737 733575757
    0xb0105070203120c01061e0603060501111009020d050319030515091b0c061015081e040201140a0909051503031b0c10031a15070b0a021201240302 64
    0x2118a03c0100340c600d00000d801c01c590342c01c00100c0c62076a610301d0350f804590b0303d51800061703815042083c1310b4941c160250500416080c81c7c00702800c034180d40c28680b030300078a0440c81c021944030605541507603100d076580d10343c10f90480b040d26036070304c40f40c0d03200b0001072010040000800c0c10308002440000c0e0381d004d084121400688102800e69921448500c4000c2c1004c81100001090010b030603500c0c0300304030a91194040c50050464942071054480e14a80354001c03000411083c03104002803820444543c000d0380d21005600c4200784c4482c40140d685000702c045030040303c2400701740500c500d58054600c000312034001d5001c010503240c0544500810403035024107034150307004000d881c052100d0707410010000c80203201505d2202203200700149006142c012440006519079060006100c0d4900b02d50250200c02c4810382c02c01c3c43d0300001d80210303000d500800703049410070310000740240009404441540c0f00807000d01c1d80660310703001c54000150b103d010541d0f0744040301c40d4607114039009208403024025 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 733578237 1250 733576987 733576993
    0x30f3106020f04120302030408060108010c090506090f0913110d02060f0a0e030a0b070201050f1b0d0b040f050702120705033106050d0c031103060d0f050303040f060b0105070203 78
    0x21454503504003a52103142030700d20840040000003032540840c00c00718080303480b95000c5c1d03a403149401107440c54410181c109868591500440c1a0100c1e0041c0406003111400d840594480244c06c3c00281c0984420b40360f203400400480801c02120800c04039160182c0c420541402d03855008414400201c9480034000c0d040502000001503510749000600b2101081d0714055082029a0000c41c0c1840c000c040304803142c21400b020300124980a0189581c4601d513424183d18600c1c01e14030f0004112000818001001c000194442d8031480c650440102c41d4405801401b0181449aa4400801c0c0854000d80107020303101001c00c81c52444c03011a80b5a41d00440294181003c4180300d001e19200300741c1d0202c0081e003503103416500c2180c4000840c000c01880d15183c0d254141e10042c4e106841c250740f13149042614012640200d554500e0641303800080a90b03520070b48080a1412034110303040080040c1c2640700100400080185581400c00b545104103410b00144a44e00015501c1c0d014017940258035030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 733579487 1250 733578237 733578331
    0x606130e070605090a08120702010314130303110c0106030c05030601080601030c090f090506070908060c040b041503110c0d0e01080f3103030b0f150d020d090206030f 73
    0x25120f440a84412900100441400395030b844119150a828804481828802240c1301055680500c00c1c400c41e4240004424041d10700892900e0a030303808a1802403d02d07503241e0bc10f4448100f6081502d004010000c001c004164490801d00e90141c0d8912a181c841e02c612400842c4a8401040da0b904803980050200009410310a0b010080d26100c00d055000641d100c2c4c00e840458000c01225004203229250800064100340180341444001404084039050030041000b850152004440c01c03100c5007064030940103030100c0200c015060503100c2440c414000b03d10442a64000b040708411100301d0b40302e03940e5801c44080155880301c0226031a00e240c0040d5800994074098001000000d1806061607880310b40441040025800325910240c000a0340c402085075641012040c04100e603408031f807107003000c21140c12005000c2c412040400c00301a00851902802840c64204811441d80280555140e10f0111100e08074810119120b104140c035088403008008d005200600c0e4120a4841000d818 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 733580737 1250 733579487 733579499
    0x1a090c0c01020d020703051908091002090301090819030e0703080412032d08010909120f12021207030c170c18030703061407030b0a030b040f140606130e07 68
    0x90304035184402a954080040700880c42140c4010710600380719440301038071032107842e816400b203882c8010b040d4144030310715050014101c4000b60440141c103000300c0141e03840107140b0210f8050040400010080072000c03582c1d40f907031010ba4103a0100d00c0b03a95501005108034240c02942c0d035182c180b0010784013000400c01030040180004020404a000381024000018209011400c0f4403251502f428000040c08603400580e0344202c1c0344c0e00410b01c20605010190594a8180c0b401d4100000c00051015003018900c0d054000c2204000200340f41c403045486007200c07103202c2c2c0a80c100b140d40100191a040082440c00d000f05088250103190340c0070b4002c9a40d03103d01141040c0c2c060145804656040001c80340140e45c1008030078040c0d07100321030100304d1001c509101114034001a11030700904d8104080904262a100c100b0012030750800c8503402140c6480c20f12058000c404000503107210390400a107200304100040490003600141c1b4000c0b10103844021030360896060b541400c8803500545400c000d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 733581987 1250 733580737 733580761
    0x80f130f050309131b05130b1b0f01060509090a030816140708040e0f090a03031d0d020c19141003110c0c0108060901080a0b040309170601091a09 64
    0x5520070030849142075040d000041c400c42d500c4004400c1c00303480d0310a01090004006200c2446412402e049040547c84280354580500e1f80c0174000c0e8070381000c1558100c3c440307412924031928101900ba14515030000c1c141034060040da00030345001e01401d84c0412a003000c00500a0701441e0141d951035081c1d143c80000c8001b400308411403600304040c0b802501c2e49d0750111001072007400c3c490f03c01d81c0d59441c0740c8004000480401801045181c0c0a03c080001c0341d1008a41e15a90300d51525001a0703c8500130254020052030284000c424441e0070800408640c0000716041940c1c3c0403a080d0315110721082007041844614004c044080c81e980b0120700c2d240c102444180c94680c80ca060110320f90520094000c41030300804190b01c0140d000d45440c10b810750300a6240e41d003041c001d403441082507041c200740f10f942da642144010704004643c000201810311170001170010704445025200c0307000c00f520001e0354401c0c0038048c1808003464004210405a1002c140142c1480c0140c10030344150b59103102590 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 733583237 1250 733581987 733582013
    0x50a140307060504120b070e13090b01060c02011202130b070807020a080d0e010309021302120711030403020a0315110307030e010506031504080c0f0706030c120501080c040b060d0509010507080f13 86
    0x40c4500c2004810850f40c2d0041902c500b10927a00c800201004682400540348034180d00090174412070036001e80160b603000b1084071504080e5500565611801940407200c41d0b000d90004030404000300b100c0041017040e00040c030100713000b201e44142e09a26402202d8642100c01004004078582c2c40c524900b41d4001d4100100d0903000030a03040c0446206000e00050740c2c4018844500e509425081241898008484040000079840103506240c01c540c03700c0c041c1c151a000c0588001c2841079040754101107a04241111400d0300350464884c18841700280180401c03d45000079542000002459800d002444040a14103000b25076400d03101c40c0c5450f000c1d070340100000882030040c207104001c0c010b010401b0310000c0c8019500080d110b546090700401c2324004803001c00ea410f040800420a0300400241d45503020002c07140007503074540080016409218a0b840c0343c54103801c08003000347c03416040d80010320071580c41e1104502581d03039030a6a22200c404892480140103e0a0010049004102d41c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 733584487 1250 733583237 733583251
    0x1202060708030c0301051e1008182509140403030914010911150a020d032c0d03140106080403081e28021e0a0207050a140307060504120b 60
    0x140c40c00040d80c4802507168000c0781c80300929800000108039078105084000c10110b03071030100c11018002032000400c208400d20400c0e040101c600c0207e20007601401c0040401d111100441d9442580c0c05218100350110a011102520540400080c03455190080740e0054182c0c03000c1170850b50301c0f85d41c16402490280016203001c20407554102c0320140902c11141158043c0c8081c07945180000204090311010290b03a5011140500402c080c0c1500001c030030100c4074141c200464082c00c104c4038440a500d1203860264400d071100c8810000110210300007000746410741e01801049402c0905941ca12420322803070000524000020340070a100d80c10064216078042118050700d00750034903c800701041641d002d00c241c1c280a9480c21140101d00843d42c85e840c05040030b50506400365901609840d000310018032503680005d80c000707524424451800604401403969030215150142c4151021030606031a019104c3c030a404211540140107070303001c442e2058030803501c500c01651410100d583c00b600ca2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 733585737 1250 733584487 733584499
    0x20c070924080c03060c0c030a23070303020c0708030c070308090109030602072306090a020d050f161d04080706200408030c010f06050307051009050a09020c1005010f1202 75
    0x60340310104000381220003420320b8402080300031011000c141c10b2081c043e100d030990f000304010301042504040107a6004807424202481101c4801824070f030010314151219110743c00000e0708104041d019809008101c03594011a030a840c0c079125115502e00c5080910000c9078881d0900700005524040217025080b0189000d00e1a243c2e81d559a00598000000444810400318210b650200e03291502c041d10188000040410741001890a81c840e8851003003e0b000b000000780030b1040c442d041112083d00c0c00343c0700464084072041462100c050410f80114401001c1400d008404091400040fa000d10b40140d05546030082d940d503803a00902110b100e0f0040407517481e0361010410007a002800c001d021010156658034a0582138508580c0c0c80a42c0140c00c03854400e0070301898078005506e4050720800d403000f00440c1400c032425251200c940c1d000baa0700c40c0046101180149031900a0680c0c00b15a0b0115101c01e101154a01d0507103200f40500340b110307604444100000d2001d04010100340c0e00252803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 733586987 1250 733585737 733585781
    0x810030c17010e030a0f12050f01090b060705030c07030b1b120a0b180114091005090c040f080309011715010f0512040b0105030f0303130f0c080d170604020c0709 71
    0x20f030b44e00390307002010700f5000704a603041450f2a15400807007030042c0070401c107000c01c40c81c60001c1c031100301d500d0706002d4140c1003070765121070355000d8450720101c45a41da00441100d4484401e58402caa54030103d00003280c241019401203203000021409581c554007081418500b0701c030305120b0240400d000142150492a199880c050203900d4900210325200c2d03a03000d11440319030408804400f5183c0d032003070403030052501300108030003858060000e0701500c5080ba50b0616507103450790520604d0040790030121401c46100e600260300003000000348002802238035013807140d403001130000d045071104880c01c1f030303025002c1c071480700d49907100c0c180851800c201c0341016400c00d6400c0120000d00c030000c550855080d04007400500061070b04005c1d842c130710882c0074010b525502c0c0030091261803c070b2110004001e0800c40c1c1c0c40d502004401d1b401107001d8078007241169440800240000d00e2500e80103d100402507500012444c50700b043c0c000c0f1421000c3c0d090051071001d160200382d8006060011001c4451520200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 733588237 1250 733586987 733587011
    0x2120703050720060a080a0e0c0a03060207020f03030d020d18020306060919060f0f0b0307120b0a05120c010305090d050a141207110f031305040b010905040c020304060810030c1701 79
    0x10103400c120071580e644041c1443c101c8812001ca8001e504c0300448c50f8010002c4040c1590358400c2c0d00c0503241e11001c0075031900141d201050300c0380340c80012503038140000300c0c0b14410151194050042600c00f000700f4010055003a680f50030000390180065010b80008000959030b0034846010394001000301320b218090721500c0700000860f40c03641c11049148003010340c00c20292603074226150107042004003242c5142000c18014140f0f040d02c1d0701c0d68110b15190111104e07503580d9464070030010100500044e070f860041442c25600c40011400950200e440e002c08102c00960010f511080304519032980761500007965010345000c940c44003c003c800350300f0000c14404103034030840c1c58081e100030307210880002c406a941500300301d0f4000e0310003680d03070060015004410f184103214003100c0d81520005080702007100120b03451820b81d00b240e50854182a030390035206500100034001c44089903185241c036243d15031000003035542440080c0001c02d00017014404040e051080e400310240d000d000150f0f25000103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 733589487 1250 733588237 733588249
    0x603090a14010617060106080f190603231209010e0a232d04020c16031b0e06130222060302030f0a020a0f03020a020c15030702120703050720 62
    0x48800708060351141e000b088084040000018855016400745c0103560500000800b0400010700c0895103100720710100da8120030000b8050020203a4140c06d0041544074145010940c0c003081441d9034a0061840070342c0420004140f15038842030000040c0d107091a518011600c0041d48800b1541c00074180790300140ba810904001081001c488045508030480e10040261921002c2c200f00c3c180344041050304100401e4a080018841d81281c0041e206d005540040c3e20308000126407111715890703d00040305021002800e0000343c0203140d00310f1100d507101d0510b0100c0311000e0f1030079a0096401d4207250301c05110b1781c0203400460300080145c960544440e0000703151b03035074130360000c1c011940c0003080c0b0490f080c4400391540d0010480c0700c1540780408280e00142641c0ba56040001019800b099658500d0f00c240000150303040010a5a590100c1d5207400907400e601c2510028090b220f4100100032034a565003e440c07500d0b0301511864100400760312858189081c651005071420380c40c002007641ea540780 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 733590737 1250 733589487 733589513
    0xe0906120a0f0605100e011802040305030d0b0f12030d1802060d050603010605010e030a1203061e090c020a03051b0c100810080f0703031b060c0c151401050603090a 72
    0x954100c102c429450500c0c20403150017800300c4800c506041018402d68203030904441c11610103001090450b0b07100b040c030074020b01032500010401d000000b4400c4442c0c00c00c2d08a02c040e010120741d08403100000340d003046070140c84030074100607d81040c007032140c100355113500c196210008104620607402c07582d40003035580e90125071803005082c2e40740e06002c00ca04003445010b000e03103002c0c00c0005140c00d120001940d2a407140700000c1008074842008260203109402010040107200080c1c80304090841040c01400d00c40d000b01c0c1c00076480c1c4402103107031901c0010039403442a09619520f1a01c000a1038580b00c09a0800440059205031b02685d04961940305c88000b03040c0003941c030000d40c2d05104c2200720211015501c915000d40c00082c0004c40601d001c01d0440460394941022440005461207480036111a0340c0d000c0c24144ca0500e0000c1840d070000c40401d80365120741e52100303110300e5030343c071030422684580c0c00e10000c0140300c0b005001900b0490020f503042001002207840d10b00d07040e958202c1250700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 733591987 1250 733590737 733590743
    0x21051e28030c0b06010309060c11060937080301180b030a030210021602150c0613030c031115010906050a0602192a24030b010e0906120a 60
    0x8401419114008a1400240459000580c4400a41054900512aa2003904050021550b00c00414010f1303010364400f2004651280d000e2000b9651000c026040042c0142c2c400d100e401a0400104408408203e071501b000810410144020b0010000150a004145d0f0401c441d9411715420010444140c040c40c001e0403518290f07a480300d244489a020713a411302c4980ca01036884a0482000280c000c00c59641301e5805610050b10790855072500d0094206c4c80002940140b00d0a000308a1184400e006145044074401121a40d4843d2202c98211300800c0d030000e00003e4803a0001800240701e2500802840c0d0706104450341052101110040c107102030b401000c80076510b5608000380e0070052580303801010a070000d400d03032b4014054404038814046200824003003502c64004540000151b140c48180c2450380e070285010f0b240d040440c00481d00e0313100890804d40309915005858800d01440761031040c182d54034040343c1482c00510000d440043c1101e90b200d44104000c2410307650801c42000c0640c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 733593237 1250 733591987 733591993
    0xa21050f06010f140d02060306031f0203090c090702151806070e040c0c0b0606030603011b2d120c051e092e0c020d14160f21051e 57
    0x11401c1d2400400c2c41072540134240140750810030b502d1940c0c503000f1a034451501038884594984d1103c00003414002c0385600034003000c0040d0b0701e0b440052015800b561242080604403560028298100200028100c42c150300691100c203140840100c0f60442e10b0300407002415042c1505100006941070a40c1100c0d080c00081c61011002800d01c0c00b8080d41510b6a99810805801d00054440c0c0450319801070207580542e00000101d802c5807000d602c40303030703041600d400c3d02001800d101d04002d0404500380c1c032000302041ca4031081d45e4529824034440468640e0794440118644001034200c1c0502042c01607501400014806054401d41c1d140885d01540d56410034250340d56482020001c0300388800f0304641d0541e00003446684040c600b914038280035406030405001007061840020010020542d0003041c111742c424941861540024045d00280612420414240c0d11056a0390aa01480c40742000c4109030000644801216002c8011810300500c00d035120326894803882d40003199103800c02d01660b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 733594487 1250 733593237 733593239
    0x6061605030415210b06041e0302091008010b04050c070f0c03080d15090203090a03120213090b090901151403030d0207141e0a03050d0b04050109050a0c0c020a21050f0601 75
    0x9408907003008004d000e03114100030103034440c00803455a0042d0701904000d244040c40c40e040508209042800540e030003844418244ad05500381c2460300800d11401c90307250b08155480c0c0c014500340c016144500e100c0c005c424107041c66501c0300d40440a07c0740c0283d8080c000c4442c0400811762141c01031010070740844000c26522032080a41d0300d0a400b035441002103a00c10704c01e000c600c000109000d80c0050301484c04031858020b10310316400074845c0354421882c1d13503451580091803d120703422074480c03621b04a40724800340e0ba4080e040c5007a2821410203080900140f01b09024110141d4001e0820038005001c6a0420368400080b400700d9120040a541c144500d40303101702041010801d901c1c035201340350700c24040300c1c20010300291355507482c1c0c034024180074012030410400d4489501c0f0781c002c110001c0003071080d5650380b10005c0c001c0c0f0044e140c10307443c2c83c14460348040090282044000c201ea014020312a601d140000300d20000d0069803100f5911142070403154007240e402c000740d40e6403000d0600641995 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 733595737 1250 733594487 733594517
    0x606070b0403020f1509060109050711030327030a17100302090c1201050a1206050a0e0102180307060302071509080f0301151709060a0b04180602120105060306061605030415 76
    0x141c80084204000d6280170100724848102103001411101c4c03400021a043d224868155802c0c003c0c20100502844080104a00d560140e6070540f00f40c00d00d0454041c952000d00c81180c1c0b80d111344108400424094004039080000c0754900c40c0d0f010004c1120850840c0d100d50000f088084140c07811404510085880c2c507400c04102da0113401040700701c0e82064440d1800320085020b003200080606003594500014003055015000125240c201400031941c1d0452825580c0403070522104280c080c4c45610030200b21507000f882110070441d0020251800c00c0e02c040100009814044c40403141000b05104540c00704044c8400741d4003800d4060143e03c102004000c000700019080b04e40c1100e10640b8030f0030b0010202012410700d4101c950b840c00421000544004140500a0480441030a000c15846c60041c811254007411890b03111050b0028184d9a800070003146010031346142d640002c007004004840040150b060700c841c0d202e00252820310b0742da410300c16056180c1c81d10b8400495102c0030000c1c03076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 733596987 1250 733595737 733595743
    0x2307060218060301150c020d0c1d060901050d06020d090c030c06260121050d0302040501030509070608070503040c090f0b011e0e12010e070807170f12030606070b0403020f 75
    0x810742511580d040d9171410044021030440501500180001c01950700300390b4442240b0856886d81000004410560710000341041e4804c60161500c1d0038050800319a03940383c140702c002e041300c00c0104040061041e0b078403010001d5200c2d01d190300180755244507003000106514080d20040d401400e40c400303039914001d005418600d0754900310f60080100131080c0f000c2e40316401c0d440c3c19074110103e411a0001201c0500d0400e0419110242c0700b44101803401000f83e9043d001041030f1903080c0e078103100688925901d01e070740d00700500900010424540005540c2031140000e194440d00440f0540461039035030902104551175250101c1c2d4658496040c0445560040303a81c031a4a280034021010744002018010007011a03042d81c0c0c0d00c00c5004030403a410302c20302500058060080038095507200c69a669802d036958020307204030345002083c01c1a05010b18008100440600034007005450a4851015038010580c401000141d2001050044d03001003007240000c0b0b407042c0d1207600140a00c0f1203104145107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 733598237 1250 733596987 733597027
    0x301060b0702180c0d0e0c13050901060e0903182403060406170a03050a020109080c070515030c03010e060a320607081911150105010909020408030a23070602 69
    0x30a01c43d5030500c010000d5032000c030b6900c8280001c00160f0f12008121241c1002018220960b110b0519000d50f00c011106a1090f8004d00026008100700c40c3d481c800501682c20441d1146410703003040c4007003002420b80e4007440e8142c0c003000f8040c50b01c040003418204441d94554030300d014010004402c1004608291081002415400c00141400252540250380d1250541401410400040b4101804074004d400c0500010b41c40301c611610f811101084a13030723a4240c4d10449100b5618410316042d006011700444c3d0090442426091840e800d103110701410550147c0b005411a080c9100011078a410003a07900b03c980d103d0503906d68a00c0c0700c1e00382e2b0f450500541d061a1042608112560020300039004945054400711001400c0440c194019640e07411270140b101824010b0661a0082c6685401c505050340c0098954101c41c90312080c0410490086019103203007940200b2410b10b545000d00510118110585000e10007240034280609841c3c21079003049420030380100710a1409000e405d0000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 733599487 1250 733598237 733598269
    0x3140f0405100905100b03030405150702180f130201050409020408060708010803040f0e060f040c11011a010c3306060e090408120903041a0309060a060b0d11090301060b0702 76
    0x4040c050743c6843d20b03925650607035164040166546003420890302c042c802d40c6d00404000b083c10104545c15502c403c12607020180480c8208004a450f929a40c94040340d18091180f00310045001e5481c281e500c0c80288400b0030982c113100302800000ba42000b81d000802c060f018050240c00c40b41000034000d402060f040e004001c060700700384400e103c11b045001e80340c41241d503405030041c1142c4584011032140360744003101c1604030b0b00f016049101250440403510031000c89800800059995038007660410016005050006481001d5140850350324500c0940640c1d4803c00a440038075405042c4241c1d140f100c40070f00e14907031299000c10503d90407190039060b420b800d45100085143c607540d0b40e01d45218016940344c002072240c011464283c4200181c401804801d80304020704a0405842005600200c460300301d9445013500107000490240112812103001e109580e00b0041c42001a101400c0111481c1b0a07205007484070007141d0f50301340540340081c8924203807250340344100d0041c03101403070141da088 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 733600737 1250 733599487 733599491
    0x18040b01111f020405060406030e0d0504050f280e070908070b04090e070b2a0d0e1e0d08030f0702030315011206052701090b0607021003140f040510 65
    0x18030512800810000150200035241c6409501e02c4101000240182d40009030048000324010400c50f4050744a42a90703041107046990000102c82e04480501c031f85e024254110441c03048281582c10600881c5401c0191031101650300c50152050010242c403990051222003080030910501c590081d00b1303003002e01441d0020341038140c01c007158012940304503c2440362155403840c090310000f60178092507000e02840940581d8405241c443c1982d42100c040070340000e1100b00707202003e6440002400031010ba003a0300c9400c1d040c2004020042903050005a0600d002d201a801001907030b141805160554400e498039502e0b801e01e510b034403900800040c00c51055500400502003082c04140d035000401c2c40901e0121100750124030b444026200390380c0720580080c0c0824041c908a08003600c1117032140d90700e160082e05aa41d4440181c01c2c0c0e00c80010894000c04104070304400340c1404071500d820007045050225204140350f00c60a00918216813103258102544180010420306020144075040d1003d41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 733601987 1250 733600737 733600757
    0x907050f07021009050a03060218310204090e06150604230310110c010b0f131112070f030c0207060801152a030305010509040b13031418040b01 63
    0x1003440240305082010b40b0404810b07515001540c030410081d009800301070460810182d480c5440f90294012241e103040c0d4100882c54980c1604180406201441c442002c8180e1110404140310304d00500035100b078940380d02000301103002c80d0103005042d41001114000d240b03078945820785907550168111301c240b04a80070031081040d04006041c0624000040c540729842d02c0318500001c0c50103d9904c1c81340c9240b414601e07642c02901c407000142c042c04a07524000e000c4108007a04010303a0000d680100b0b50f20510301244102c096841e944005080032545444610345260180c2400d0304807401c8400038001100303106400e00c0d55506000e22240340d00c503030009026031414900040c20040c014010703503000e400c00025451030140724988022910000402083d0389400002c0780d20110b9000000039401310342850000906030a0410a06103d542c101c101c82da01511628440e44951a02034000c0c1c4c100030044900130034450384000100000c880e00300e8650404040c010030703c42076030004004ea0b03050102c0854 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 733603237 1250 733601987 733602007
    0x61a09010b070209042d141618021b2e0b180415090c0504151a0703020f240702030328060b0d0204081615080c04091406090705 56
    0x1001d6800c250304c115101e0020220240340d9090301c0c02d6040449015407010001c0040c00080c4026a00c520547c8054071256803156058400d20300c000c0c4200a010368410b03800c61109207403680900f0100350300303541c140c0094118003035603407410981643ca1080e8100e40014800801c103031405200050780d000c0002e1200700120800162400c04040e81100014100e40001e8204001c00c80c441c100200c5c038039400c000141c1141400b0444208078003469020b1031801801d841d010040900d02e20884450f2102200c0701c3e900c60b2407a02068002480841c01d6205140003480f00c10000e01080e00c101c0c444880da4003202001000180300240043c200e00250341081082c480f40030341103d81c144440c00000904000402c03291441c04c010840c9501000c1995030109410317404a86e1078006004036400e9600b1629035881c40e07000500110360318820004103184031280c02610a0003a03510680c880c0e8074800c3c0606143e584c00b54503080d1076071100e154480f600d03a10200700b4a4a002c1d0981504407009180240c01d000e1160 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 733604487 1250 733603237 733603249
    0x108060601021b0d0f0f0f12110a080c070f0608100e040f061a060d021803150103061a0d030c05010501150504030b0928050c0102150a020306030703061a09010b0702 72
    0x4060343c0142d00c030781201800d0041400d81114800d41c02003480d161b0b2005402c055000300a180021603001d401d0710801d0800c58424146003030004120809800061107954442e0880e03400b521b4040c2590041c00800150b25841341c0920005001d192600e006600d0144480c3c450745485410198162124400303000c0400e402c0e051aa40540d8410740010346400c1c03052589100c00c1444490b50f6002c440055400e8403010726030050500900019084440c0c02604070825071605c20100001808042c0d2100400104105420a90764480c0e501c8000200d03100740760100e0a00c00310700c0401c5d00414020132910003004000d1240070700510710404031656801001c80004c3c001c3c4241d12024140382c112002140c1214400d02045503040340c0c02c8189240380c0c1d01c048100038882c1605200f96014003401a05001d29400421600048030400d5010380d42545c91007581d400030341000d01003d41500c500b07200400091841e100b01d40840388118011281c104151040005100058020701d0b5010024481400161102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 733605737 1250 733604487 733604533
    0x103050714161212140105010e06070609211e020d050705070b0406110d0f020a0605090a14250302130b010512010b040302011116030605070c0f0605010806060102 71
    0x45410180d442c0791041402c0c6480c51518405024100c80600b680c4906802c001c1e01c0344503543c802c1c01844450040503030140b6030035092180c1404a02c01c43d140c0340f11454480020700e0360134030440c0c0008242d000703900d900328000d4000c1d0b554900c0c40182e40e46603105c181c02c50052056000d001d0b6400184212207034000f03403034040042c0c9501c00c2c0000407030a441041000d02c038440142c00c071100e040362a240d07103240050074080c1083c0d10b92510b003d51503407105030901c41c1ea9180ca0303046040e00244804001c607940e006c0240f030014200141802000034400c0000d00500080c98261720342401043c034608040f02400012018449101d1190180802080142c46201400a80961100c8005580f202100060312248200707900e0015854100c80042100038880000e4400d59000380da500182115110103075030355540000301c4040d03990b01074000308000342c01500411350001551600040f0b040060b6200c000220a5102c112150740d1120018030480d078003000910781c442e100344014404280660f500c101c05c9181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 733606987 1250 733605737 733605767
    0x9120a08041d150f0303041701020711030f0d080604020d020c0c10020a020a090c02010605060301030804031203050f1503010e10060915050d0809030c1305040303050714091e04020309160501030507 86
    0x180340307403026580e501b8010b403001841c0c0c12801010055504210314002c3d0301035242200d8200300c80c20308072030034140025200001500b120040c052081e401100750740700f100040c481d940c02174007000f0f0300784401600c3c0043c18407110750900406180c5607034403c004100e10201c45900071075000185103070251f682e0341040e0382143c0d41003400140c1d642c2e4080c0704070b000d446541c003c96013080d070000000040201d50401481124041d10b814150b6030644501102900c9040d640e008100350a800130a8902400c244100316400c002000020800c1c20046410f040052025000f1240d6030760711b40c00c01ca84030040c0101c1000d0741c1c00520031200755003000c000908400c0111805403a007000030170710000d251801c000c00b8040d40c50080000001c0e4103a0034859029202c115000c500103414030000c100c42c40c2c052091050610310010005040044003002d200854280004032006046038100c0100d041d115440210300543d94000a00900030b941114800680307016070246040528110070810b07425403013900560031081c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 733608237 1250 733606987 733606999
    0x1e131e0303060504150323060103050609012901050903073501050912070c0506030a240302100507030c060f0212150603061c050d050c0d03090b04060209120a08041d15 73
    0x4803907031f140e15503c0d00300000105d5a1040030004024010005009032166038150009d0012035083c0380e01ea42d4449034004400c0306000f82c501c590101c1d41c058806407001c604060100c55141d9954540501265410b100b00000d000c0045407005000484100458501c00900000c0c844c42c00c080c0b0440340e031102e030105a4201101c010400d08100201a07060100a03c0000d00300c54803400c01c1141c03d0020030341d8043e403540507480619448205071250340c5080403a500105681406c06d0981d50688542d40144022010403c0071302c020390014185200308021011034840c01030701c1d100a43c0c08214881d0001c0e00342280c0b0012500d00d000590380c0c400880e640444165044d150b280411500340c51a040c0345c20300100305004400341c5022241d8014060604101404110784810b07005030b405038101c80d081072003d03101e41865800180401c00c560014620284064003000788026003400040c100000c861080311101800074041103080c00910070550345074100e14424596041401140c982080980c0056004070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 733609487 1250 733608237 733608263
    0xc0d1106030402060c0706021615020705090c0c1e0f19061e050a09061128110d02150c1614030f131703031e131e03030605041503 57
    0x9103460041e10041405a011900407e0322001702035141d1500a0080c05105214000000d699400091110b00c001440e00507200349400d00041c001040802403c1850340001044101c0c0da000e030401504c03401c400c001c01d0004070310130520005400d20400501400403944840b00308440040c10031035821010750320501c00034074207403400290400000c1c0029656280740c604020480d800b00c90f0380003002c200f88281d40400c43c0e803030800c1070702a250082e110702d44090300e40703d10380d0310710340d01d10f10700c40c22480d6010700b400000b41d013003272031505d10f42441c000350000140c000c9480d100e81c0c1080c5095130ba803c200c010004504225103010913440d2a1000340c00500804841c941e6040e818a0510454040a08207055180d8546038880c00c1861804103120b8400c20480091400c501040701205a80c0140c64101240581e01441c81d400000c1100c05880807402c901d50341c103c2000204d04e11800e80d85d6445081e82c01045070080d0501804540c215444503025500b0f00c0c3e000c0301103000a1001100b500c0e03000c00400802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 733610737 1250 733609487 733609489
    0x6090715030b0f0925020304060509040513020901120615050d080306150313030207050d0b0609091f0b091f120606030605040c0e1005031507170f090c0d1106030402 72
    0x15490fa45281350410703440c10038003803058807280c4407401c0414401d0b8031000d103082404040ba45d034869849200c00041d000e101c40b005030b00e419041250880060f41c8030844903841500001c0c82e030700e021703404288a00101c040c0e11080043d1f41c0514226040145242d14510f841c0c80089100c041011f0801805490b0000014074281d944400c990107002c10118020788030718103ea5142660a08854160f001d8895040005058074195900e2401c4070748c0b001c1030110545402003170140b03028002c2c0c0500d225000c2c0d1910802030028030f001d0700b56000401b0034080340d020011410f1028100010300840543c40164044180f03031000d95001c001207601d003d0740c4c0c2d14460100d003440801442c460300014016402d0500303110134828040f1441c1e09035074040800f000c00d511401300c64009951140b0916815801040e40310451400704054283c0c000201e0414040060304000321a061020846000700e0200b0b8200911440940421410050900aa81300034503c02c043c0c449032140051003610600c039420000010b811 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 733611987 1250 733610737 733610749
    0x10e06091507030221190f05241807021c1b080307181205010c05040f06121404050a03080601020a0b010510020115031101140304030f030b0609031e06090715030b 71
    0x654400c0005c503609050003900e500c005805d1010100b07800d0300340060590b40061a00c0b4803400390950112590b08501d00c00c1d0b41c0380513421030b040312582c000111880d031103200406640907072242c0c85540c0548154485103508040d43d50210504004100f194071040480d850b0a4014030621134102400c55100e6541c46011100f84803035000465500700c409034001010310390194820f0f0300c284207c0082c400c01e107100350100da0710b01070b6118840d03080003403030740401100380141213500c11003489140218800c10b00089190700c800c02130b901110554004a0b50701c0901d9440805550015000d201170164050961107180c0c600c5418010306108041242441d0b0401307000358400b8500000b0009040c0380142e80b030501d081030b00c0e42030741e010340462074520200d41140c0810341280e10650745900d681207851464030b4100c0007460561101c58028030204800c00c840e5070700708250450070011490144010360900081c070309104c0041c11500b0142c0c4146814000807100c140703144001001761800140e2244081c000501d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 733613237 1250 733611987 733612027
    0xb1b0c030306011107120f0c08010b01020709020a03110c030d1b09091814030d05100b0d1d030c0304170615010c05070b0d0c18061d030c06030702010e060915070302 72
    0x180042c0301c40420b00400090b5941e100301d46001e003006416250b49c1711002420380e00780c08030080c010382005505200c1c20100d54042c000c12210b51900142540281103007454036800004107517400e90000c60101d00d06480f6000c2c0c2650b0507a81006401c080f240707040c010305400058055511280d84800c80d0540d103079111080880c1c440d4101d500f82441101145195880e82e00440c0004c0c60703e4100301c0054111214000c4100442e0340000c0040e180c0401e460015008082903003d140c201d0307540c49420031425800f080078080c00007103032006c2c41d80c46181c00c0c905003030380341c18010b241c45503040740c0200410b03441d44461a450400003030a0020280c1680d18240307003440c10a800a029407030011400207840c2005601c0003d1b80340706600c0342d040500050048581c80d13000740c46402c00007159000c080401c160110403401c01d006019045441001919000401c1c941044030707688010703903441c0b00c8070307d107917004201c03040d04240d00f10040d0071000c4640d422201031082c0188004103158000031003c8041142901c050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 733614487 1250 733613237 733613249
    0x906043b0115032c1608061618080105010503010c09050f0d0213020703020c0f0d0b160306180209180c070605070c0506070210110f09040c0e030a0b1b0c030306011107 73
    0x404c5107a12298403442c110000d28400c6003d1040f01c4503141040c080d070b014082034622410050005964414000e00e0075400c040c0c48108015443e003022889071408185000a00090b0001088942c103107004d260031611620158810042c601008008c56100c90110b0f19540a05844a85d9070722541d0021400c002c0d1032072583d4075014030000d0314074141070780401c1c424010241281d24100307095450040004000e500308000d440000fa00c008201c00d0031950201e014560307190b0402040051340d03440004460504025903118441d00000c110b9594038040340680e812040d0a0101049030800e203850003014010200024020f6588001180500e0701030140d0021144e030200c02c854080c07a00035002501c5100540c4401081403e00b007421f0410040041aa410320200b02c040350304040080741004081c0052500030824040341800c9800c5644041c0014030115000307203c0c26000d81040000c5400240105000c0c04c070a200c240300001c44114044212a040707482464403920101d10180d2490800e0b01552000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 733615737 1250 733614487 733614521
    0x20402040e0f0109060b0711010806150d0e01150b0a0f0c0b07030e0105061f051b1204030507060f0504030204051008010608010902091f0e0405030906043b011503 71
    0x2400400302e011541030b9210360109000060380c0b035039102013034017800790b000b00f01401540c0b0402503035204414841e4131980081c1076090304101404201c9540d40720084915507182c6075441768a02140900860b0700160940d0400c00980b4500501d001590160200050400c45040d0422170018800e0b80b0200c0542d8011001c0d640e9800c6c947c43c00f8000f02040c0b2a00c444039400d140001c0d0710740c505007072000c2886210b8402041a90121b00086445502549441d440046c0654001013041c00402c22908014600c41d02181e4840c114107141c0d00c1c021090740002c1c1009600c1104843c41c9034030a00740d504403541601c000c106a107501e8062040882c00d5041a88035601e029000510701c030054000c49d01c054000d03114465242c540c91a04100203002007030341e0065030307482c010410040b00c200d402d145e4403c0c01441600d081c0a02d48001611661291b44604410100a80c5070b0394050f0401a0b07410041110343c3d2203014840000d03c0c4141700803014441d1450f501405000034210b103000350025800380c5555242 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 733616987 1250 733615737 733615741
    0xb07090b180103050a110301060e191203090807031502030703020d1a1804020901050909070801060e010f0b030610140408012c0a0f061a100906030531020402040e 71
    0x3034451414400181c10300080c104800300c0c0d00d04c40c01c1e00c51110040e0401040c1c0b45980e09212050712650350b080146600280d90070b085040110041040c003014051201c590404180c180c2030090503281d49c1d80140007580c0080b0010000540340500e49038070b0011959025846e03a94000301500203010301071808203100d0410508403080000402c42059003001107840303007410031880340d041c1c40d00b110445d0004c2d08080c0920050003180b038100c030b06c0b680c03010806040310740d44c644540b0745c503096600d01d90120300701c0c02c0c001c0014001d040c00b5003031507030240200c06529420340c5003c40c0060b504184900c161010701072400615a0040c3c0d0600031940034040c42e00c000e000d40d100700c1e04580501c00100344040c200c45440f040601100b90003058000e5890b8000d00c1c01c0c81c68542d103442d404024500003010402d03401c1c00c40b03291001a15010300c1e5004e94503240e12070b00405803400b0300c06030a032600100800500c00001e41707000305294524101c1411410101d1000342c13918103c1c40403400a10482e0003640c0c4201140003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 733618237 1250 733616987 733617007
    0x21030c01150f031a0c07080a020615371d0a0b0301050105130e03090a06020d030c140f0d0213080f190809060a020106030b131712040b07090b 62
    0x4000704505000c94440d403019510001e0070b904032a1400f0082c98a002500900081201c0102c1250080d40005909161000d20f94600306250711283d0540d01581200d4104090b407442d80702400090b110596400504608061000c120003004044402c10480030016118411140b1000030028040003c7e824500c81101117085822030801c4a5111255081070141d0150703003410302401c1e0480700050b081d054100301c1e26141d4000341400da001950584000c0c40449210f81da241c1c00b8a00400aa03009007015201c16000141503032422940d401c2031046001440528010320000c590786203031440032075a00e0301c038072550080282c829a07281000c07942e085032010403180c002080703040a01070755100701c1300320030101c0b050b4003142404000040c210a01c2484450641e00302800100400b65951000060154036940d4903404480103039030241062508001d08400c0000246030303529040b88100480d41030203124440d80f40d17801d05c000c10003003a0f040c4280c0402d100e2809030405802400c00d880c40c0c035444015000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 733619487 1250 733618237 733618241
    0xb191a10020a051e0c0a0e01050d051c030f0e070308040b0a050d15051f020307080f0702030d110c0411071112070612051311010f211b1d21030c01 64
    0x4e811043c00b0344480521503181203190001140c0c100070901d64035a1074081003060140304241c058032240680d0070381d0312a2500303101034100c02030416103000a50704290064102120140c01c034051407a4043c400074400f28820788242c03411074400003501552100c560b4012100e0703000e408045a0000d00700f121040c07011a00c1c6c0b403404150381040e2400c030160044100310b01940801d03e0150340c05604100301c90804a0b46043c020840556038001721807800b4004e5010034507000c6138070034403400207152003012a4000340a2002030402c640446013400381c3c8007140301400352480794000c0101518072200c2421f030b054aa5103a120035410360341c0240c1c1d60303459940c407029001020752000c104030709103090002040106904101d407819030b002143c0c0c52020310140c0066075114022003620b024031401d0790403901030140c00c1500320b4009910850200d000703260f07038800c10b41049030840d900b824425010614903021841c00c0d401e83c040701048403000c408249442c074800c003070b903078034041c08a49010000759200303c1d003c15 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 733620737 1250 733619487 733619533
    0x16051308061f0e010308091f02010605010224130507030b07110115030f1209150e0a050a211104050f070816140d020906070b191a10020a05 61
    0x52a0162103003070819000b04040300090142900540303403880188041080c0d1006000000c1c0040c080c02e64554040f014a0b0010038801e008a0050791154801e100b80c0d40d06120f500024400315210203480480319011100110004000c15504c030109428001440300c00c02c0300c880159008046500d5904040800400350089910701554543c01d04218400802d0b5030503000d41103d410840300c4140101d0795851301c100311a450301040401c0144a03002c034444040101e06d826040d240c2e03c1e842000b2f01d142c4203014079480300d81e22003803041c80d280d5001c01c12400301c90340c10f2104102040100d07080b2601352421200c00c4003d280c0381d68219103031008205e40c1c6003849407168025292038170341078110796540c010b5020700d40290000a0014141140c905d102d014100c1c00303000204022000581000c40d0103000c00c0040e00041425075a1025000600c9401041032146050030190060706001c006244021542502c1c20718800c5805001102c80a03020039100f4000403800310b62080583e00c0748010941010404845 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 733621987 1250 733620737 733620751
    0xc02030c100507060b0306071d1201050709090609060f0605130b041424090d0f02090c19020309031e15040b070f0e100806130c170109141605130806 65
    0x17501448030503500e000a8018800c40c03044e40d4000d601600d0b0490b4140b2040c00795083c1d60004c0a02c094921644030070f02a05100d191240d545400d4245404c01203020385001d50b114075101883c0450500059880704107003001d99241c0d04085940e0801717600c40c0e918408480c1e10007040c0e000d010401090100c2c0e4001144890740080307400706044085045406000700000d180c2200c1d010041002200ca818500300d003e52690041000f0704012000d0740105190312021103584c000401c0c000361210880a26181c1d400c84550300784000c50404148801182e5201a0315140821450203000e6280c01e0a03c108010495240b080c030005001d405e0500e4040034804090f5204000b103010400441391407441442c04082c144c10040040d8a003200e507031403d880784080078100b141c0041c0442e02c2e0200150080c011400d0300030745540ca035210050403500c01c501c6410181c1040200b01d0a00c8601d40305092040c100d00e030008042400780b100c001c01000156101d100c2d504450304449040c1c4c00000700e000000c44c000b84200d60f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 733623237 1250 733621987 733621991
    0x10e060d1a150306012a08040806040b1b040e25020c010806041418031b0a0314030708070305072a02040606030902130b0310180309050a06050a0c02030c10050706 71
    0x701104103501e030b42c0002c0315428001180c00140005014200d4003001a90398052015507a020083d21020401d0b4017540206500c0c1c1d11003400d12013004050b54041c3d6003d4024070a45508c0b40120803c2c070702d64451032180345400d06d603132004200c030b28510201e001d2500e40c02c06400b1158940312200a5146d03143d81041c00c0c0813030025000a401130030b00e03010b018040d621550420180740d071401014808c64020800150807807206025484410581f01c03039007212140c44400030900d140a5240c0103004080c0300e041c2b442514001d000b80124240c00241450300003415040210f86030362103d000301c8888148102d01d61003020034a041c002d50704604542c0440c00c90082e1001e000389507c410095069400c161030003900441800084c0a5401036944180c00b10710005080c1c2d0424a00313509008152681d0603207840c44c10b480361044800300f50b000602e5900a103016607151860515041c80900103020741c1302d00006215000300c2d480110754003444510a910401404c0300c198000c0d214006140350056a0200c61080c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 733624487 1250 733623237 733623259
    0x409052224051302150d05040311060c070210080601020c131e020a0504060507030e0901031202060a09050615060405060c07210b011208070b09060a0c090311010e060d1a 74
    0x1800c1c60241a214082101c401c01640c0b50035803d001c480302041e500c80122010910840d1141c0e01140a114000d0b4000c4d903d65443d10b202144280c00d042c000f81c079604114104200380030050711400415184002e05040c000580c1e80c5980060742004020400980e0103e54400401307c5a6440d501031903011503d00414443c804070701c42c3d110103e22401c9500381c04200c00b40400c10042c2d2007031000b010386502c6440c04811660540307002c5030800c0c01c207800890781ca200041000c890316030304001007540150a41402d10814026496994490703801800c060f030b04440400d2044616241c1d1011140203010141c1960303a1102601509525031199004004e0300c0c10b40520010000d1100604607590a83c000078490116440c11039a845034407180d0b0400c50f2000001c1c403c89021941c0007034000e1040c01e1001c050302e091f24181035198122502d40403a5814080c2d030203000e002048200140205545080c00d200c0f581c140c80c1400240f41f8000d90031145c0b00e2504001e14801c15140e03224008502140980d07001d9101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 733625737 1250 733624487 733624553
    0x1e0203031e0d1508030706050910050109090b130f060e0c0603100801230f060a0801020d090201090501140313030c1407080c010302070816020415270c0504090522 71
    0x1140d10801301c59620900021000c143e451740119080904c5008941181020a00700000e07103609900040324942c0e20001c4030144034183c01d034241c1c0800d02225003981e0442944d02c04001c01025080901080e903a462450b01c01074003000686822a4000c103d1a100c1c139140c0011020b182c450300907402954280005103030140140c5603100d02000300104c2003402d986d00c240c2c83d440004c0d002081184e002c3e0107008002219203086c03000700340c41d04130701d0008a070302d001900014040d420160f002a042101103507120007421032540a4a0b0480400c00000c0360785021810115114640d5000144c070313031046980948a8005e0004100c000c40da9002d05885082c2c00307601c015812070040d00c1e030103000c0140030000d0717440045446254845c0688001d0000403d5900a40d001c40d22014941204988104a0880d80c56051030908110189030b04013905100030241c0c808010064080c6226441d14251a400810b8282002a00410051911216141a00c1d1041c2044100700c0c07200b40580c000b030391035145040c500b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 733626987 1250 733625737 733625771
    0x418240b06160c08190519050a06090f0b270d020a021201020717030114010e01050a03050403020f0d020709050c160308070c0602030c0433052a011d06041e0203031e0d 73
    0x507c542240281c45810180d40301ea030094a0104401c441001d018110580058001d601081c05400c0c089034803071246038605c0030014483c100c1c0e41070703c0d40c0303500c40710548158603030008041c2812030381030710b01d00d480e1440441c50601a0081030401003d020096024001c0401c0c8040510b0490300c40781007800e44080407c0054802241c1562a00e002070002c008011030756000350041c82d00144a031045136054490501c409081c6400301c04000010307004000e0400031290540106a0031000030301c0d0319071415085e5030940001580c150801000d2003100c00c00030365000d000d80402e0b034000385c0007039041d9a01d2518005404080c0c0c800e002d0b114005a103d4040e03040d40ba400c107030000083d031140454402001107414140d465411528040d0041c00c01c030009080aa8400703207100801c0c0e00c52900200380c1084d126000001590400070040b15580328008000108600c0c183e0080e900c1011071080340c0c00011800800d0862041029200401c0c5202510158683c80040201140a0f00c54000c0040c1140b948200f85 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 733628237 1250 733626987 733627033
    0x20715063c0312170a05090f0f061f2c0c16080d0e01060e06090108030717090d05030315090924060418240b06160c081905 54
    0x301c0100303095002e01c00034420202c529111009800c1003040900c404018042d003400854001752551748800500610100c00c200200301d0500c0078000d890305109050200d651400020032090a2126581ca0019841e03112120080581a0501d4501040c8900450840390b882c03a1102d04074120794807800070701d05100074003c0d03c405041400b10300060350f042e42c450404a80240031812965582c982c4a50460310003441040f0040c00705103c685501e141500c200b00c01d0f901c0503404a05590420008100000c80000300381811001303807904592149401c1010916280c9400c400502d030748000024020040c254185480514500320b0b4a0003441d59840102500d031000402c0700380e2104d40d10480c10000d0644031240070350010010304005600c803044c0c0e4420f404040003101c00e907592000f415000ca03904680c44050003004003010004e10144811101061103403040e440300158190160880c0b0003044400441d007402000c082c0f08980501d40c13428200c0300001003092003111640b0401d00c6c1c0c103001c04151000a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 733629487 1250 733628237 733628339
    0x40b0d300804050c0418170405270601050703020a0b070512270309010c0f11150307140301030c060c0303060f0b0c071205191e0303020901020f07050a050402071506 72
    0x80400031032540d407414401d0041402d20380b105801e100109d019202c2d074880b00703030442d90360710400c400d410008900921018064a150f04024003000a01c021036000200b202001e6030ac401c0301e00c0503a44890341207500380280f03401031418460304424001400014900d020019005d11080c50484260040095807031041205040c04603904005a102040744038140c0c0c2002c50182d08500840404039000462a001034141307029210004024851416406012595485814400e4503e50350440c2c5492801900622400003004424030390321f403c0505c01d8101034020701d284c8031070188260b1174030380c02c0040c1d81000030f0070092446440c000145014001c803640d00704907001400382c200030314207071030b580444009903001756407541c807401c800c4580e10859406c0895141c040d0703800603203070010080028140120a07010030507a07400003038144100d540340c03d80141140e42c111401030380c500c103610300005288a607120451546140020002d12845400307039000034005071500181004032140752000501000c6910130b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 733630737 1250 733629487 733629521
    0x2360a030309061b050a0b071209080d1a120105011a12010501030b210a0b0f06031e070504140708091912050c03071b05040b0d300804050c04 62
    0x1086000d000d0f01e4046010f040e500100128200180c46003894003006c00f81c11250360300103100b0040350a41c01800d54501100c144410b1002031040d484c2d410741c0c0c0c000d21005018055660814400354241c44030090208900684509030107400c83e5a010f000344803d208001404002013955440c001c40325044900394400103c544a6a0742004011001004550440b64100e0b4111060b03404400750000b102d24490651001019040b20b185002410f2020103005604400c071440d0500c000c1e42e4004c40e482440c4440c00f103c40d5282c0e000229654038002841d408a0740040c03509002d6066071000424441c428950368031005c55645441d45843c0e030740c215840315520380c100003800403800250440300b580700c0c2e0065803818606022850f0422400c41d408440c00f00c3e10319040ea0008020440d102c2007080040c84115003c21a00c02e103500454812901050000c0810312004202e0803001c10200c00399400c19100100502e0444030110f014011400980b015a650710580161301294946406050b100340c00c02d102d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 733631987 1250 733630737 733630739
    0x2904060c1e1b11060403080903010c0e0105120a110a03060302100e03061305121b0c0f01120207020607060501080d08090c01090b0a0306170c180615070602360a030309 73
    0x4240038002d00c0401210303882c0052001d007070190742e41405440694059020660384100341000c040c01c65400c000e601007400508401142182c1c1c001054900c020380c9140e003c43c9035658003500c41e00a00400d012050f141002080345217240ba8983d10810680740b00b91010303481d051342800c007503460b110f85009030341c0e0680c080000a8462007203403951210480c07045045130b014085030360740c03014207400001000312010444000c0f0b080410041140194440c1d00761400c482072100c250000300040c015200140c0ca80b900090000704640300d8100f10340c131072750700f1140c10089540c4408005441c0ca2003070301814000b4400d0030128114002c00b061b02e030010007058540000301707440d1035894149500050201380a0668450000400c40084101c0901c0480e049018044c0d20800740c082100c2c0f0400c400d003034104003004808210700c54448410955852140c1440d5944071086445d21002901c01c01c11103190b00060156184600480020900102940c00c04a159015600030610020907094800a00080d10441d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 733633093 1106 733631987 733632017
    0x314090a1203021e030f070f05060a021e040501020c0103050702340f051c1b09060e06033412140118050304032904060c1e 54
    0x1454040e03d800d10744039603503203000d0385038a082c6c10900010414248114410b03548500e80d405802c40b42d80340351884591001e500725001580030320610400300e0032080407220654050354010790007040284112070044001d440041d0560b03040d40517800108070054019503500c144a07201d0081542d210100d1640302d160501a41d114088608826000380070940e5a00c8660b0f40004500450080076207290030a11000f13601c1c0e45800144030040700001502c0c40158001c0c00865141801c2c641241d55505c00740358840c1011544400c4188003d50780b110f9000c1c20a62081a00440000d082c602c03e80703400d010400006900401d582c80707401d40d605ca000041090240315210030a40e459000012a41c1c0c6e1801c1e42d030700442c00010403d400b2011408041c810414000c0000c410044000082d41094241040141a00000c0c0c000003030b1400459010707002c020014211410796903803801001c8800b11 = true := by decide +kernel

theorem cover : BRFrame.Cov 733453237 733633093 := by
  have h0 := BRFrame.cov_init 733453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 733453237 ≤ n) (h2 : n < 733633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
