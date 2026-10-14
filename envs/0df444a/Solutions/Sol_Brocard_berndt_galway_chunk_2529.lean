-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2529
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:58:36.515647+00:00
-- url     : https://prove2.me/submissions/572f72c3-ecc0-46ce-8f87-e885de8bf37f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 454676258 ≤ n < 454856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 454677508 1250 454676258 454676267
    0x60105070825060e0a050d211109100c08030f04021804031e021603030503070513030c0f0801090f06050603070503011e050906010803071209090c03150b07020d02040b010e030a0507030201 82
    0xf40242c0c144050005d1034a03d44816640325040c0810308200590f420818110780c881c1c500040340e4501c9070a050005404150402406801c000d1800344200200b081c1c400019000300242c1e00b01d50b500040c5a4216514480350381d07003000f8020000e03600080d101e0f4084002c480445034082c0b0881c400d80f900d10742c25005014036100400b070060f1500a40d4040c640c02001d9089030b11048040301d40c036181480e40c1b82d0703c840c411503d500cc1c07004d081e1100380d9840c5001c41001a00d1001800356800c030345480840c0c0c1d031382d03016880c2a10341c00c8001400381c090f030303841110114003c2c0e0042c0b54000405000c0302c054541d5000880d0840d04810300840802890b40000070a41030389004068001007400000c2c2829410002540d4484c0b1900c84020b040300c0d000e1035020b0995004014881c01480d01510400c28448840000381c040c10251031044038030181810080341890300c09040c3c510713080d0050141414104c140d802d00008003014a1414184803030b104101c0e205030b40400981c0c2000b845003001d840c00300c0c550300c005030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 454678758 1250 454677508 454677521
    0x6090b0406060f0503030306120309090c0a03110f1b01151413060509130609080409020a0e06030702100e010209090c121308030a051f0f051509010806010507082506 72
    0x30f44402101d4041016940001c10b8076005002141c031000780e0301a148400d4074501c80d40d11b42d5074001402408100402d0160713005002000f10a07181804151581e45038050a1322039440e00b881401000d1080b03000d4054603815400e070a00145e400021900200440e00800485036441000d1185517510200c5041c1840044401d03074400054051004c0c0c2d05210000fa0b004200806124100001450305000d226598004402e0540c000c1e622560321901d40f082e04029511070b61544000c6444050381d4841741c02c0c064101d80c0704661507409040350112030724900000e02054601c5865030b41d002e0104d06002da0b6400141da00810060700f10a40d1441c000c0903006250310000d00000b8180034500313410303001c40c0c20340003200d510070120580000c02d40d90b841c3c0405c0054807011202c0c029002c0034000461400b1031041102d0503500200d0742140d44000c4864848031a10440c0040360008080101156103540100041c0201c00d109400150802002c500720303004004070703c80010700c0100380d4000001800018400c0c1d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 454680008 1250 454678758 454678769
    0x161103100203150102011811090406111c0e07050906041505060c0106150f0e09040503070f030e01180f030303110d0e011e141501170a0e071d06040c0c06090b040606 72
    0x8a05a1f010b4846c0395031520304800850003100d40310001010003080350b0046c44078070300800119440d0380d4180402000501180d28003126075180120f02001420300207119000c5407c014030440c9107a40303000a100243c4082400307101d60103076801000c81e0320354a54010341680c400d443c0000914030b18104403a00120b808042000a11120886200003240d10204030304c0c180700141c5c1c0701c83c0380c1d849a04d001440c5100700c010182c8051000c42149040603846110100b90a10036a214094a60301d6000d19036002250f00c24807001e1402d2550030800280240c019141003010b0f0745d945414000082c64040646100b00140e2080f80d41d10b941203076000c0c00d605100780d520a41401d0400840d00d42e1880c078816200007901040e0f00381e00c0e0784201c04480c2e02c9880d00a000c0d078a0f003c10f804450500c0d12180c800b80000d4409090b06000e2604d0210748904840c00541c5054002c0e2030307100c22a01d841091100030045180390300c00304140092400301141c2c050040d541224411a00c000d0545070509045045070f4068019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 454681258 1250 454680008 454680041
    0x71715010f0b0d02092206170316110d0f03020a06050a0b030a110a051c05010e030307080112050a0c06110105070f020d030225030809010b030316110310020315010201 73
    0x14001c0c02e0001040c2d420036110482c0042c1d480891200086c042c1035490010703074144070030b142c1040300c07601035411000c12100d41e18440c030017441e90145901e86901445c40c910038500700e4801410b001c00c405581800344141e0250400c40f061549844102604030002c100354003507400810110304008142c400c59a000c4c40c800c504001c0403103031000080d01c4490039030029000041d440014865591407582c04401860024000c5042001280d074501d040c84a01c0c2d02550554039010020000324004003c43e4400d1078980d8a40140340c0c2018030300c0122054200c1c0641d990310850f03c0c4800010210a0944060f0241c1d032614442608241042d500307480009024000f04207000014490091300000c040034601183c1c00d0140c1c541424580410825482680800c0c080d101c00c400b00c0f09141e0021546d074000d1460600a1000c000300381c0030701d9079900c2010071540e001142402d038200030420a41d514401403100a080d00c407030300440b44160b02a60015288290b1a080e0b407034020050b0342c5c0905c40e80c110384a10052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 454682508 1250 454681258 454681289
    0xe040b0703150b030a0b04051f090606090b07060f02030a1d0a12050c1c03090b15030a020906040906050103060b0a120b1605041502160509090d050c07171501 69
    0x101030b01000492050300304120020000c40d81c1040b403600509400f500c040c004002c0c034070300741324108001d103003101803040025001c200108000c0d031140070b0b085c141d580039140c840e000351600d10211981d51200c8013344046030764038262440648103000560080c003404101054035041c842d13107040c40c1940c201c07030098076601400c011000a4554810104903014900301203880c0c140b20f020140c107060034034a100071002c2c3c0c0c0765220303200d00d50903902840310300b405200300842d5540c400201c4800096140c41141e45513001e6a802c40052420044c0700e644400003902c04600308440740e89640941c4c10a0f041191a55102c40036920542065840280207003200b80107940103422a444400c40d102d405400001002c042c51b00c68013800740100221002054aa0601002d180d5180340003526182241d10819141c0414000000c6524040040307502030340c0503070064143c0c1628084240c46540c401070385088507025a4100159042540d02400b80c1252548080c0915181c2079040080d0807a0580048240100c1d05a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 454683758 1250 454682508 454682531
    0x60408060106120533010e061b0706181a0f03040b04030318081207050702100801090513080d1a10020102032719020607080a02010903031505030a0201080606040801060e040b0703 78
    0x201081a520124171a8075000003007001210302081034011980c00070000900a04441510030f0110711140c03015054807403640e00ca0b9800c0b0b920500d51200d40080060000c0180040c402020a214a903000b1319a100e14024200280a40640041700c0070b44100610f042004207068145c0940c01f1000c3c05c84903203403202ca8080c1e0f075400240c007450f0140350503a98144006204bc60041080f504800d40051100070500f080f500020143c080074002d00380b00c1428040401c0c800d500f00541441c00075070100c20503003040480c51a090051021001c0048191584030041c04075440d07004500b01d400d0075550000d0303502d103403042d0780d03000b2aa801000703200c3c81e140d1650801c46030580410020a0640840588a81c5002c01d00010b0301d00c0c0a07900000e4852107002840c0c100a40c1c0540c04680310500c41c3d1803e0040050114a10220340d00717038400ca03038040d007141c184140151700c0790080700e03400b00c0c00412280c00c1c00e444000060031250160003600c030300c100b144184000c0c0402e81164540c031501500d401d0081031a101d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 454685008 1250 454683758 454683811
    0x11010506010503240307030803043f050a0c1506080610050303040e150603070903030807111f020403050d020a1505010f260d09050a0b0f030c090604080601061205 71
    0xa807840c0813491071032105260b40900c0f07100021900b2071a843d842c1d04150030a6007011004480d0b0840d482414541c110b00f120b0902c0c945141e1881900980e10212801c5400b0f441c140c3c040001c5034204101000101c00044c02c243c000020000040d0b00064428100308041e0f107403441c09000700d407415204081c100f10039500081100d083d2009410309000359141e0509941480080140315944484081308100040d40d11003034040440e0302035520600d1a484042043d51011603014100c2415086045081f8015050381f101c1034884402d0440103182944d65101c1a0400000a902c81c0050300621040ac0c2440701d6100c004040c074040c25070403c480e500d00038a800c1030100500c1182c1c20054281c141c85141800884114991208003060743d1095020000040003409a80510340c414621050081040443c0d2029111082d40003040540380d2b44600300120016005031380702e540d1240c1c00b00804118900d0030712080b4000c106984600410720320f810701003015600000c081c0c844540e481c40b00c520140000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 454686258 1250 454685008 454685041
    0x1201052a19210b1003140f060f2106101d07051b0c1c0b180106031e0519050a150e011d19170c100501030311010506010503 54
    0x5018401e10007100090040d15910300e0042d014544660744241c0102042e065042215001811207210210a84100007542256089000604105682c80c00248017080d8103503d26003152000740980420f0b15001e002940c501601d4864811170003040d44280300180081140c03a8001240c101d80504c803900303101c051104203140380e501d0061411403034081018503000d0070441b49200500040c02c1c8c1a00e01010f20305a030b401c42400501e0081054003010130154590620418140c0c0c2d004101c6040781d29254984440c01c0781e8004100e07159540e911000000911056070100358505660580c80d01c890103003881400c0169444c602488820140a188000f0354041549220710398007466801149441d901024000e00000d920b1900c0d0398a4000140ba50352599444044849008400c07600c1d055201107040040141d4440d00521900c812400302c60041100c00c042c0418081c0b600c21960902d84240d01881595020707801500800d20821603140320300020300400c0d030301150a081480c594241640d54010ba80c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 454687508 1250 454686258 454686277
    0x70b0411040902040c031407110d0503040809040e0a0302070b030f010909030e12070509010b070f03080c0c070f06180e07050a110a0c081908030c07111201052a 70
    0x8001500400e199a5980407000040c1c02601c208550f145140000d030003000350700c10184000407407800051300a40f0a801074282d903803400e000f4081e6501e282c507050320940c0015104075010b100501c06001591a50b2041c0c03190361103100000c0646c16a00d05010b41861100c2e00603032400d5104104114404e4400c0c01c2541c11540544000501107043c1e0908442c0c20a07500c01030b9600c00c44c03044003554085000036002041e240103c0b0b000d00c050342c0c0d81e0194203180c07240410080004201e25508404203010343e00c05980109140c04141c50131880f501c3c03241c200515600514034045880c542030040a910181d0211901c910040c1c4c10702c8542400100152410300502a00410800055a440d20f6105448000d0014140001c44166240314a464107201840e4010301d051b41c4150070b81240544801c0c0820020760b40c105228a203591140104002c50307600c5010140c0380c101c4254000640ca40b030340c0c2e1500c241c07249490b00004182c280610a00990412400b00d2503180b58003204485a171500c000c00c4840228 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 454688758 1250 454687508 454687523
    0x5010f0507020901170d170a02090a03080415030c020a020d1103030f03090a12020d0f08040f080c010e0d0e0603010b030702160303090603060501051c150b0a030b04060b070b04 77
    0x506180003118588994180250044a228000145020140c54680d0003c454005454882c0300d2881c08940410a401032000c1c090780450108042d04019802094000d00c06400d94400302d4603501c4200b0342d41c1c042e80c04001c112665806003c10706030726228901180525101410080e1400d8000680e040000a8054603034a07070804062001d07601001250144c0728500b0800c0e440c0d01c0d003200000d44a42240c4810784400c0c4804120800e20b510114109507414095110258000e074000b0048500aa00520032910040a944050701140100d000340c02010701c5100041005540c2d040303583d007030412190040e0700b4840a000940520303600e1405980c1520182100c8680303954444108031300d00300c3c03400390600e944c0ca070080d404024140e10001c00800d440c041d44090000e20381d2400110703014845c9080040c1058036400d100c4150402c99007152050540d40c030050f04d4826191401211a503010651410219907600d110402c682840d00680c001030589507906c0d41003081a480765020031800510081040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 454690008 1250 454688758 454688777
    0x103120e060d0b060d091b06020109080d110d060305061e01050d0b10030b040503071703010f15090510120f0501050607120c2f03070b0f070804090212100e100501 71
    0x980315071041d18070003034400360148900c580c1402c00147c400c0203411480d010041c102800b01d020750050040b5040340750b120a40601d0508100e6440b001018503541c070703045184040050401440103070042401541c022000380640381807000c1c858030005040800440400342c0c1100403c0b465a030030704891030484e004180c7c1c41c07540d40d075000c082545040c5900001d1200407800c0500c41407203000001351142a11890043c141e00c8800000112140400d00c90201c61018182c028002819940540f05183c001e504003d82c00c16260000288001003040035000040c3c92180d49054030f0405008a011141758100100200d505120214507140724030400540160319008003200e005d40300b034841c2009940c2201c000c11042840a002290821400719070340711020102c2486551482c011078190100c8242d0201645044075101007840f036900580010b0b01e50941c140000100443c00307000030881c10303200417200300b03643c904001e0019125905800100341c40280a00f0400c0706135039140524140e681c01d0030601d000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 454691258 1250 454690008 454690031
    0x90b0a0c0203070e0906090a0c12060f1e0606050913021b06010e0618060a030312020f0c01141006051602041b0c1e0308041b1205060103120e060d 64
    0x40e0140c010000390180708415000501845841c03d00d402929040c0540e449600c0780801c00350b50310744a9074040c0540e01c07c106c041160b07880f01040364250f14865980411a2460458024100c1d07405c10b4509000400035002d60f940c00c00e19204000152101d810040d06003c0e007640402e02c204401c484809500f64009440f01c04901c9100214290813840e0040f590303a983c4030400084260801d0390f019000319211018640191a100c2000c0d20855020340109a42491074600700e500c00910301c41184075940c20445403680c50710000041005100e1240042a03030084100c3d041c6511a00602079820300d1050101404419030040c100c1e1304034101110380300e41ca0f038050b0001074018001d00000e07112020745859850070903a00110b08410880c011200c81200e208810004002e00590f1040140003904110000d00010248642d101807aa40f0b040320700313100380c0c0f1214246550001c050040d40d082d030001e0700400c20411180340d140d00c0590149040014140c244010882500440b40307407100ca1521406904030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 454692508 1250 454691258 454691267
    0x130204020f0a020102071709030c010309060b0a120212060105090c0d060506030f15060301081213030b130b010605040311040c12110c01050619171009080d0506010f090b0a 75
    0x1e24108040740c0c555400c404140039000754040c4104031095250910030b43c0c100c4072020151007980801402038001030320540011001402c1003c1c1c212403081c0c0e078013821401c944031104400d01800c01c0c003210b808101140d0042095440703c0000349142d552040b801401191141d6403019042040c900b03205442e50364907400172016008a412454000345c0c0442003001c43c10700d8003000d034000d0404000d030b5004000c45006008680c8400d000b20300d2aa88618481100c0c404982d00404072812000baa000001b80c0ba40d4402100c85030640301824881c0d503108003007041c4922034101b44c1c010400b80c2029441d0605e1030b070b034008107030341c91002e003078422035542c415585564050049205049140f110821011520144c440303201d4000c41e0b440381c51503203014005850307814400b13180d011b0310814030300c8241000c0c6400d070204244101e24a40d50305500a0441072440d03104280581c0401c03901c0780e1002034903101210038410446400900150421241184581e541a0000c15203c1038a9104030115981c9045810540c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 454693758 1250 454692508 454692517
    0x60906070215070c0b0a0203060f030109030f05130f0602010902100903211206081b010306050f092203020c0f18070807050702031b0315041208060409050109050f06100e13020402 78
    0x141100070240801c801c6d42c1896000b107101d40d000311960071008070150140f5003200c450840043c08a80a0700d02107101c07900070009800000c951340c004039042c075210b103d0418060500c1c0e0090340544c0d144d401d08000c5281401b24040c04441902d0504020380c555243c003084084092510f02090b00e03400340407100c1c60721401d044e00c2940442081441095a1340c05403564a40a01d10014a015051060040158820b000d85812100014400c0828018400421000810140860750b4055104440400030041d4000b0324001c103000e80c01604409000b90180100d607000c4c1c80c0003e1085440c0e00c0d0703c1d444003584c5103400390402c0c051f280402d142c0e80c07444402c5d1030500c524240a541403040050000c0124056181d00c18000011707001e40d198200301d05000c1d48546402d4900804110f90548030408403441a01345550004008002040740803803501c80600f1a403100c482a40d03039802096450a001c0300401025800c42014114001e0240c0340c00d0180c006400050014000705011040704002d44d074464043d03e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 454695008 1250 454693758 454693763
    0x3070309020f120a0203010c02010b130c0e0307060804050601121a18030d02071209150e03010605040e0109110f1020011d070b0708031f0306060611060906070215070c 73
    0x2102090000e000c4030f41d4685113500304910960800c1c020000f51807042c01b803900080d10141a2140c82500100f00b034000e0800810180e04000c10410740c00c4480e501004400000d14054694080038106030901a060100581044841500441e000e4000074402190000640e60a000b048c4036900c0390f100785e004925074210402e10a110100701169607200c16070080c01b08074820041101c003114040300903140ca000501c20091040105c00d800c1c20414001c0d54038404c1d514004000081d040c0d20303903002504071074085004a030540c0d5114440c90401c002d40c000740c000c3d0b0004498403003000765000c00169800c4a9010403804000012408410a041c0000c110040f0034844000b030003030807881024140c0030401c45185801500c507a40300064452078540c21100c443c0c2e08003e1040ca0742c0d0714403401c000303075142190030070502514442c0008089002445410042d00700740d40d8042c0c03680424105c8030310301076000c4c00384085900b025040c80b054640001e154120180c00e0040d14071035603245078060720b02508000e0027 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 454696258 1250 454695008 454695019
    0x140906130b0a061107090b180a0605060703030b1c0b0a0e19050f1c02061b070f0b01150e0906040b010c0c061e050a0225090e030a03060806040803070309020f 69
    0x450284d0b0020b00c5416881e4a080c2216101d0b40c0d40c0d0041815501034030314198100f404110407800040d201292281d100a03141004181c0c1076581340800d50582c003542050780000d541d180711455514280b12111210301c5070052001024605481d00a405800504448092951001e8001c1410300500c103844580e01c2c07103040c0000301c8105080c0345880340c01d50003152842d8040c10b2103031b0b084409802d5046803041d5080d03000b850f9035580c9860156800c0cad00294040c02050302400040c001420762a602c4d2100e034030441c44280c80f940b51550346810310301c00508110070b02141d00c2c180c041d6515003241c065404001218042a8044540c00603901c0d4203030007401501403819038002181282c1c2110141c04a12512503c42c864044c00c00412190750184c03d00c4c640040c0c020712040e0324601100120409041c0248440551303480d540c4c064a022103032407000e2280c5540020800d141450b4044c461341000b02001009054149800e41d02c0da404c910004052005050740d4034113001c15034070391612050408402601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 454697508 1250 454696258 454696279
    0x70f090506040315200306010e0127080d0e01020a060207020612010902040f061d091909030206010806060a030f06050703020d060303080a05060f030705010c05030f0a05040f140906130b 81
    0xd000100300407007940f0305032603410442c843d60201c0c3c0c10354141304505e0b200740c1c00c0c50840d1902c1c001100d1414480144070704211200303848481c009840e0060082401c0304105a406552030010600c1c01d0911000741c0b2014818464107039502641c02041403144503520041c0103a80f0b0f00284000f4045018081e103201400301c10034008201d00d00180d00402c10354480000303040800355210b004561025075900400f00041080da4161540d0601ea1a4250440072981614403c284c0f46600c2408440403007038180c00507409903004010b94681070098a80019064841400090441e190b2914106007150011700081d520703030019205a10a906540d0341a4000c1c0c8140551035486c02c0060183d50151604206c45141030040350081c41d143c03c401d98840390240290410701c0c900401500e00c5c40503140f050324140404c0200031250f0448a000f44541c00c1c03603840d055141e6080a8000038142c800b40c100d141001c0c40f403d207404566550381650384e03000c1421104503400810b4210f088001e040007183d0140c01c03141c03500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 454698758 1250 454697508 454697513
    0x10f0c15111201080601050d080306030a02040219110f0303011502030405032b2d0e040c030618061404051504050103030e150412110612010602060604050a0212070f0905060403 77
    0x700801c4684802c01080219980b1900304a440e031800b0300c00d5540c06420b04420100040680d40a994058001400e850090f156500443c060b80d01c4800100c20301701c5c1c8000700c0340c002500810f10420355042070000340380354031a401815070740344010b009a50602c0c14003070224062610030400c8030040c000140a0b50010705820544406010700b40b59808840840301d5641806680704055061f00c3da001034044a10101026114151249440f0aa40304104410100080980303841c01280c84107079840c0c1e4002903142c90200c3c141e0000d0010369031629400d003481e0381000540300300818800c90210440d0006900d03240c60f481038290f0119100096007190900b4000024075800070142503d0300420f40c0d000341d1024083c45501802c1c801c078002c0c3d2180f01c0710300b054000800e603848076403861300c17801500c002d103820255010001d1941d004da016500690207082000414181030141ea50010308041013035081c1061002c01202e1b00200400c00d01c2003086042c0083c003c1445111120000c02002c0c1030036a6803074403030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 454700008 1250 454698758 454698791
    0x1008030a081e040201020a030f0306030b0103150e151f0503100506040c0c020114070813120528110a090e0c0411090603041b0b0d021215010f0c15 64
    0x220760452264801c107001e03402c2541c208095920950b416405400240c4a503079003610442c030760040d0003003096920076010001507501603815001e07600a4140c01021101c11011800356a4035640425441d000101c01400070082c1c800d5041d0404404000100c03c4d8803124010302d501b154a9110316070611583c14004c2c0401100da11050150303109440521000a00075002e40b000030003500001d001690051300d18007011480c07406800d00368400c00c0310030716003964460160008801600b02d030b6105a007280d409400c1000c10446a5800d4000311950002c00200d10501c21100320102009007801002c40c1c003500321070b9030307100400c0d001d005060800c0091003119444035540b014003084c1caa02441c60001e03000e0212240b80241c1c2d840c1070001b0711640c615682c42d40c1da0005903075140c900020030f50144602040c004080c0300501291208010010303246e11303040402d4882158040c020030045803620a2528559a00c0840d44070381d4007c0d42492103030146c803894600003c00080c0e010b1140d180c90140e9901917120308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 454701258 1250 454700008 454700011
    0x708150a050d061503081308060f011d09160f380d090204140f1008031905040e040f1406011202040b01020a0203070b0c01150e0604051008030a08 64
    0x5414042202408210500c10350200c01e0180c16400a00a9141c000068468010801001c00c501c01c50750000ea403541c4081d11758010100c00c4000c40000c19040c07059081c01c00900d6071000729400d0a40031035141001035004000d5108520403490496400242d030098104060040010342c1824a8065580e901140100310024080c0ea9540003800d12075000032299403010308441c03420445181c05041c516120a8419400001c50051688e2205851400350350b59220700182200e044035400d006103889181c0c003c06120003000046000550102440f070480300000b40c4588203807544103c1d40540320301c0c0b81603c0b80d004030303400401c90b14800401c21042014081700f28810a2044202c06000000d0007142c0e52120403d000c2d528000b0101d000c01400f604d440d40000e00350315010700645168005a030007090410380250027115a075500024560341083d024801c00c444480c2c0c611114000380d0408903030848002c0c010b00007900c81c1742c07510003181e034003160445400000c1c201101140d40d2103c0300340e0301502e0b4480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 454702508 1250 454701258 454701271
    0x19080a20031c0b030c0108060d0b04030201321512010e070303020d0503090607052a010c0e01021603021215161e050a0807090b0418150e010b030901090204050708 71
    0xc08101d0140001c54015160440c000074042c01040285d0001101c2100740284001c0d4424220848440424254010310340124002d50001c1856400703400d20348030b01504520f00041004044007880e900000c030184054000e010006503010900c0000005004410940c2403090039520702145e00f032100da800507a09003109c0c442c2c2c0030341d81d0031600b16509480c2e9000c201d5480c105074000e1030008020342d1051009010002612000000e10503040c0040140000c01c00c002d21101d81d541d00c1e41c0c841040c0c05c071914a60b440000d100400003007024a0b18407410007400d00c0300031f009002600010000a40c24450104141c0c18605e0000043c50510143c980314958500c10a000c04c07407021148201c500442c62003194000240c503810303d00b40300c16a084800520040c41241042038000001c250103a412005000404425400ca66100605c6d5081002c444000d6140d4503105501c401c100312080311031804c581183c0915900f56184d035a030322012030161684d4100254014070301020401c3c6581c000c80c45034060358 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 454703758 1250 454702508 454702537
    0xb0103020f12040209060d17030406090f030e0307090204060e0d0c080604030f0e0a032a030b0705090301110c07171005040f052118041805030703080919080a2003 71
    0x40f030304018401c0b0760802560140c1000d0b091030446901c0508d61b401180c0251044034000795411490b100d20902422614003200041e60403035400d213403864104546005440c64460440c5070a00c0c1003005007500015800c0c1e03d02603810301e41c2c03070b00920041c846d95100030030100301030350041c0c41c003464001c00b1a90f4002d030040108404284600307684c10000c0000c42901e41c080c160308103c00b50502640c03891085402a03040c03c1002040c084009500078102900a1401c0c4e155541c566824100b01401d6403008214960800818031019a50000001d2160101d444840031264003000e0750302110304054804440c42d9140f824002844100610b6003c1c415609004609540c0002419400b8011802440002c8084c41405011140c20550507941c100c8007010001c0000940440080010340380a55410054856400c0403603400305050300030103100e90118044000c0c2448000c2c2c0d080031000c0c0d0803011009014010041200d81202d402030304030364941d075402c81c0155100d58402d142e2a81d668880841c2d0704094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 454705008 1250 454703758 454703761
    0x150906080c04060219060b10020c15090a140109150206040201030e0d080103020108100815040317041a1509160e030102040513180f0305040806010e0603060a0b0103020f12040209 78
    0x1c10610050b20182c1c0c90950113028140c075499400b11503000300101c2905d205554031070400c0c60382d407880b25103a51801503030080c00c1000070040c00c0001945a88004076081c103410080055103555203810102503689020004102d0300e02400100c071014103d410040075441c0b1800c1c08103c494002507151f2003241300366000c0c4000b90880207210b403104400102c4501190700702005000540c002e2090603409112000f249004550390480c05107004040304c0310902c0603a54074240810b06078003800422041000442e5403049007004d58422200700e0030043c402d1628000280801d07040c0d45030322070b681900e9000804080d99030034403401e00c880203d92040c0550110b1609030040102e030030107000380c90443e600101000348107040d04013520098413130404402420200d10106100203034801c1d6480d04024080e50b0340686840c20140d44038a0180c1c1a00a64802800300d02003091079540020640d07031000c2509008100c0713240b40c10041c2c01034020119800800b003400308003004020100d031442845a8002c49080015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 454706258 1250 454705008 454705021
    0xe1f0501050f132d05100f0b16031809091b051003050402061902031309060b0703030b0d0203060c040f0b0906030406180b01090e12130e070e19030b06102715090608 72
    0x485108e402c5100c4000d11584084010002d82d400c80580a4140714004060316000c0c142c010b034550700205001d83c0d41d20521010b000380044a40346078198100529140c504080002d0038201c10482d5802c101a2150300140c21034840c042560b80e0101303001e100e00e0b10540c43c3c3c00082e440b90440740c01c03500c01e01d0b002000040d140a2030302a80c4116592010094504062501d00714041c240300020540c0083c2800a1000181ca0401519208442c0c40c6142c2e1b8645040407081e2044218580c400c4218010078042e400880d40d43d00104c13a08a607010758001400c90500368402c5640400c41d04c00b03881c010402c00005048495034001061001e010800d44a06c64140e4544a010340a040d0101c1c0a41032049070a000100034051402d4100d4040e00f09010408c442100288103142001c050140c59010401c00b002080b80d6118101d4210000302e542804107003500d4402411100c1008600686000e1048480c0f4843e0480310007401600104000040e450054140544840c1c4540300f600002a20a00040c20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 454707508 1250 454706258 454706279
    0xa0906020d0935060f19050f0703090f0b070e0a0807030b010302100216080d080108010902010e0609010c0204020f0318060f0a020307030e1f0501050f132d0510 70
    0x15a00d031000f000e8401c010300e00070420060002e042090200c1200c04103401c56100c1000820f12a00c200d0f50082401d242c44e030100c003103284092070900d401c1800c0c4018026051081ca00c60b95021840d851f00088480090500c820701b83c49140e00504110b04030307018010002d610000f050361909040e00c46460150341c80003d84d548030038a20020301a140c0090041c801441e000c0c0501d0640c2446104a91129000c201c5051501011b540410040c0c0c2c0300b102c2d13170783c451a000a407842c01003981b0002008a2056900007070701280c01c110703003544142e50008110784a43c0c05444074140842e0054030440d00c5c0c075001c404103265a0704c1a40d29030442105056100407c800020f900303846040d401040712640d842d40789002000c0c0d00080c20342e1042c0350322000c031070702240c0c0200108280c9001d24a1034107021072407810740c9802c5800607040140900482e0540b242d403520b4808074294980240c540c00141140c1c059410400a1050b5404400c080c00045030341e4244682500454003681701e102c84900c01070380e140c5a802 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 454708758 1250 454707508 454707527
    0x910121521021807110718110a0c170d02040902030901060b0316080403090b1c0c020f03040b0c070302120706021203040b010e040f0606062705010e1c080a0906020d 72
    0x35400032101c80d108540003002c0a116800050508200c17048101c0c521407a0b080c400250403007009441d00440c0c000e2101c1490280031040304600000038581400f0310030051498025400142c8856113200d00100700c140e48a00315070a02c00600400c6484d1900e4410701c070041d51007600d408071130350309088002c0386000122045901411003c11294881b0310046020fa809000041054090000e10800080c0c400e507010000d0004080003410f10524548156450303084414140303019007150700c049840618000e001044030291000c0c18907441d120500d5140451a000241d04006d4000140c190100c03011307a0000f40d102e0680e002c603000d44440d03400c12a2000507038041214003500c01184074004100340c2008141894015010f54000c07003608016448040a80f03c2a078044000680303451681e42218a00b20300b60190105503ca109140030702d4200003c0003464442c44d00c42c0302c0c0c0c0030440c001d2540040c100c02c05101039800040139885441854014010f044907200e80301c00350140e60144450b13103102740c6005c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 454710008 1250 454708758 454708763
    0x51309020c15040809060f0d0509010b0609121f0603140303060a09180f0c0f0605040806180a060c020705041d0a080901020a02060d0b1002120910121521 67
    0x288030030140c2da040c203242460050700a90b0621010440d5142e192a07103c024100c0c0800c03400c10541d1006004000c20032030708010100c10700c60b40350583c040c0d542d56815080703030740b1740364200c68180585881016003814040f4010710100304102103100310f0945d005030781004044030700804142400710005640c0503140d200c1100c00c0741d40204101028840381d4101d0384070005021888884208600700e564845040310b804000c2551610001d64003040203841d0038541c1070142c0340c240b030000d041030306e0b111748a603a5680150803154007008010701c1050302c1c1001c101c0c4c840202d82181060001405280c000381d254959402400d0060b803d02592001008000c40756520078900c181c000c1200c00496103888c04540c03c11581141103028514500016941e0480038104c502d426000c00644401c8400400012914070650002950040000c000c031341207602c03081d100c0d42013094843c08100540f070031080701d28500709035200901c9450b1800301d0300e800340c40341c0c0d030300094400f14003804400c14103046c440c0c980d07500b012400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 454711258 1250 454710008 454710013
    0x607180303050f0c030d0603023a17040b04080c040902010c0308220c0f0603050f070c03021f0c0f03200906040e04031211030402300706051309020c 65
    0x800000b84990002e000c0da50f1240000760406004010142c15640f0080c4901c0340c0c0b640b1000140305501d010380b0710307081e094807038005c94483c1401e040c14040e20f84104840a904222442045024030000a0203100c0345044090341d16521500c402c203008040d042402415150710950201e42000c0c2042c1c0301d04209640c05842d42001a1050f0b0f40c100c2d4421001001c0ca100314242092a1180d40302418008c0b09d564801e49843e40302d142040c0e9030380051921079003c441018246414421465589500c2c0c4d5000310316440c201d045000f06080a0b40307060388800c2c4200610785c84485025440805074880000d10001c5c2c3d03100a05515030140440550302180982c2c00113660350344044065111490062180942c0a40000e0400742d844602280314003044230258003140c0144500b216a01c140c2c418040c3c500c07285c0d0400d5085080c142c0115030100400c1d051162030484262000d0740060301c601d640c458000115040f034221075291400104a6000340c030002903c0c0d81c0c10700021416030701c1c038025640301003000c000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 454712508 1250 454711258 454711307
    0x3120f0f060906090c0c10110c01113c030f090c0906090a02090d02031207020a1a04181b180602030f1218070303030204061d010801140a0e1303020607 66
    0x18a2001e6902600c15181b06100b45402203619140c14000e100a840d80862229254011600101e096504611180075000c030f0030070020a040343d803555031a04803a40851646141203104c861060f82046030b0b0841004548007100b0460203085081d11140704000f1481602c5558107a1002d1041d00c0405a440395444400140011920f07051903001d401d0707110006010700301c0d0314000e0700801d0a000100c44d40111501000603003006504021443d840245401a101ea0401d076140b0004005c0b800b0785e008015040c402d203601ca030300c07036a0550045221412040d001140d10408500041c000712561003040d1f5000c50b000c5000103c0c00e00101c196001c1c00008101a0b14041150b0080940c20728010f00759100304900c80b803e12050442045030300c0c051442900c2c01a691403d2110140241d010180c8201c82180c000b0310700350860b40d001c0451411150420b985020712009140000d95001041d001110f98034038140c1000145410b142004101d01c0c029026106544c540510032207403114403d03a91680281d0510 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 454713758 1250 454712508 454712521
    0xc0906060c0b06120120030412020f0307030318140a03030501120f1205070c082505011e0e040e0102031504090c03110303040308160203010f060f0605030903120f0f06090609 76
    0x13000f0314605800b0000020070400b200c1000c8000d00e01c0303109074029032001000f00005c01002903210182d80d43c40c1d00082c5080401403e08590780c1c030a00400808240c0c54280494024000b0402900c084d540586071001c0003030048100c035500c05e00984181d0000307060034000134485041d4088112610340000806800042a4a900c0b0700a0401021030040000411120010074869500e0364040d255810207090b10782a281d0800b445001642e075800105500207034100003d0303820100e5031a925150220408181042c5041602d103080d03002d0220345c1050900c03080c01304540040d0700451044100010090a100740b180c20b01045403994a001405602082d40c1400442d01007541d1032840640281103e10340343d243d954001654000c0502004d249a0714121141146800e01403140f42e04108801000f1a83c0742101060310801d40b44034020074040000081042a001072080f2500300c0300010341643c4a0524400d0b4910504080b039030105581070a03004034209290001119000d40401401c08036691601d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 454715008 1250 454713758 454713769
    0xc0f07060b061b060a0606021219090f09020406180f06050c0a021305010509070c1101030216120807110109020a060f030b0306091c0525080f0301030c0906060c0b06 72
    0x24800700d07a12107402c0c00800c902e20310810001442c4003840000d0308441c00e000780d420040c1c80407030700003400355080b001e0129841290790054030b030032503c54400440c00c0307090884151040070603a0007041e51981c1040000c583c00c0e1aa030002e20481d002607890300c1d80c10100030716080c0100f1070790080703076003100903500700300070041c400d0000d0700c819150101900c004002903400101d900d50b60010040846440f080104a03a182ca000d499901040c0c0e0b0400c416009640d036900c140a1824000c845e05055000c901c0c4e000341c0980500000c0195448404241d5032a90303c08050710f0074504542c0c3e08002803005c0000a94014107006d031042d81d80c2e0103404c04000d54200101a2078281541c0300180800d551402c504074960f82c10426940039080480280035a500e9402c20006111441981d500503c0801c1040d41d08001c038845010008840c08103240124002a1400340d00074414101c0700e490351a40440080140f0800740d85d508102d0f20040c00820080741c1e1307214165181007010101406602c503103030001e00035003000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 454716258 1250 454715008 454715021
    0xe0a05030a1407180902040b03010c02070302010815090f0604110f09060915031618030209040b13051204050a090b1c051903110c03061308071506060c0201080c0f0706 73
    0x10001903e5070f00d6110407030051840003d40c51043c00e01e455a108805500b07062003000d0092005030300034400b407080c0c3d0001079910801440028100322110000031003801031400203c948403c0245101081d0414002042c18074009998003841540350031024005402048100c8004120000c007090901d80701c007082003096000b01400760b4012042e04801c0400303500001c011031040c0341c04400348245e4850340c0801480305a4a0794210f1441c890808140090781d500040d00e50701c168071408240207642c500301002000c05800a000b41941300705940e02402c100b201e409031080d29000c0d1080f55000e941c0b098031070250784840142e56042200b1100c0791120b881030441d020880c9005a044070758040040002641d0102c80c0c0c101075002400380c0405240303841c01803100c41103942003107004107054208401007150b03224043c0401010090700140ba1810000ca00800303010055088000b0800c4a640e600050a01c000100089000400501c0015500104802925408919103005a0406816589510081c441e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 454717508 1250 454716258 454716293
    0xb031b040b030d39080a030b0103060b0f030406020c0303072129040617100b030622051525020601060e0f0303190c0506070503010305030a0c062a0e0a05030a 69
    0x803404c6250800140e89442d42e103441c445e0b1410390355071105402c024111801d55400d80d04041c203001040240d4441c21f4161200c04500b940040d940b034071f484c42c0c500024881d0007d481074500010042003207081d001070301007007441e018007000130340d000389d14aa103001c4416440009100d8030a5000c05c040b201c44407450321070004409003000584946a0142d10480440240c25a07101d91122076644440c0707005004000303428400740e004103614102001c4003000100c20780203038258001603140c0d107410710504108103080e5640700c540304107481c1884101110182032050301e40c0700034900322039451a080d02c00a0414103d41040d41c0c1c031030807010306504001d010845203c440d07515100611841a00740c0c103694134011401845c5d11142c5039281140f42c56800c0807401000e5400f4401d0900c010800310b500441181c00c07003a5075240c50115142e071864804001d1803440100307902e5510302d0344a0308010818001c9a1780c40f8000d5207070120032048a20402c44459207a0091a4050b0040c0c04010001030b04104114110794 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 454718758 1250 454717508 454717577
    0x40b04080c070f06020d1409010302072d031e080114010216090207030f090f0504090c08030a020105040b06040e0309060706062304060f0b1c0b031b040b030d 69
    0x45585020351910305180c124001030f03040e21004004058041052035001c4e83c150400e034501c02c0a00c01c120f02180240c141c2e00d41030540009202c400c1002c000308451030f2400062034005c0107001d003080a00710f450300d400c044001c00d010301070044034a1540190409000d11340d0340e9401035a802e20400300b560500405819040d48181c2014407040c00c0f0000401025109492006803201c0c3e82d4100103205040684040f010701007100c5091003c091080c85000c1036804c01d442c0440c44018034542a440918194840e803034500010815404040e4107411087c02180540c000501907104c940410044441e00f0301e115038154020884560704d030600001a00055021300360000b10555100d43c4040034400d0b46207450151f5024900c211010324182c812000a090411951001d9905003520900140714011118100340c00300c40d00c2c8400624550042600c10f0b4001d020307a480b40c8850f0050810b42c43c030203100e040c4668200741e400055410005040e00720a0b6695903081000d00e40e242a001d43d4002d0506594001d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 454720008 1250 454718758 454718767
    0x140903060601030b010e1e0f01080709060c0507150f0806030c03070302040b03010f110a090801020307200c040c0302090f1f0c030e0604170f06010501052b0908091f08040b0408 77
    0x140c0d100803c4071403034000500c05c0301c1404447c104100d10075040d084190b050040c5603041c0030510fa0311168a4082c0c40030ba080c040c52101c25810143c0c6809030039445122021b0885408050041d0700421101c014030003500d80b1411500ca010400d0744850707a12140c80d825a110310301c200003510301a0029001e042c0068000500540d40c00e4050060300c1190b10200c50307290000816000c966032284090009140c03480086040d0b0400141c02481402d00005a10200184480410040780140801c1c003004500410401c60054205006800380d004001100d01c5084004042145820300c41c08118a030044140b40581051095005480354400c40c0c0e0150208034200d0f44206480e15501c000700003500000181e11420140c01c05918500b6080341007540b0140c0080004001d180d8008065aa00c0c00c00e03826140c003034120b00840728000101401116006c141084400b20500840c20010a0101019645100c0404112800c0040e0540005c803120000c0d00000006000c40e41840c1c2c0150001d2184941c607140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 454721258 1250 454720008 454720037
    0x705100f090b0c0c130e0a0807063c0e0606091806090616021c051b0106121205030705040b0a0504030605090106080714061b010b0d060903140903060601030b01 70
    0x41c0e003045640203081e6000c020207a81c21305d40f401064481c2140000e0600106210f200783d80d031502c1d00303a500204500e0001c1108401c103e1290005800380d07030301c02800f0762489002d4920303c102c1c500907054482d043c1000d030308180c4000c000d40a11300e10490754034020101502e54001b8888405001000d00d050001c0006058080c140c06221040c091040d02c801014941800c41c0320b22095240e100902007990300c40300f80b40d01085070440d141a01040d050401303030b44802002c40d007450f4610a500305c5404551030180042020140452604000c83c0290066404003441c0c000941d018401035803d0000714409200800100d22000c000303007520175407403070218245944c1e5070ba110706580081e920305042d40d45804050100e8501041100001c02007601c018000c07030303948408a0082c1c03140c000d0502c002400c100a0308000e407000d41003440f200002a00e48880000f0304e00300780300180120501180010b00c8040c051141134403200580d20803005c004e01070310054a4030300c0150b00600d044070619041c803001c00d04c903411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 454722508 1250 454721258 454721279
    0xa320103021b010603020405061215180703081e0406050f18060a03020304020f011b030806040905060115110106031e02222031081f0507020705100f09 66
    0x312150302800400e41300e0651040000352400105802d00400507568402c6003038000141015410112592886894480c402004404c80303210b507480600d80701e184800010000c0100082070174061000442e2340c0c050640513035111610483c440c003000030b1014004a00d01c1201c40c0010840e11410003440403142c80100d0110b2031300e4014420b10350210741d0110410007507082c00f8004400701c3c10309180c000070001c001e40440350304a105881c05010001d4244c00559151103542c07003241559005000c560a640e0340d2000c602d800310002da801400034818641441c8000c00501480c0c060782d5000042249121a0040d081a10031280400366440000211403d5440c0044581d0f42000043d0400205601c41504590b800030001c02c540724003080c604111414240007102502002c400180076050390090500da40c6101c40961508002c61a00500d80c00c1c6268050091419070b007284904010b0110741e480d490b080e030301e52000340301d40f80c1c104655214007408070344034014005400460b0b081c0001101e031202d06244 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 454723758 1250 454722508 454722547
    0x5010c02010f030207061b020c041e0902040204120629010210020d0209130b010e2b02030a05060f1b070c09112101081207050703021e030a050105060a32010302 70
    0x820400d4001004800d48da0600411200c543d054a040c083d00c0c0449108081010140140b081d50941d94180d090440d900c40d01100c0080441c4040d400e044100d07401c09400030221800036000c10340e1a0444540c182741328560080020324141c01806280b20401c00090181d44868020300c2600c0e800c07c489003240d0381d440e44034031410b94403035000600b03031540b80005001d00385079049e0760348a05440754800011905ca02c1d804444000009802c03031040c0703680e1010916225000600509134007404007004170402000c050140f09110b041a001d102510750303540082c192040d120040c0c104550360805101c224030540200b41c016580501e43d600d0b02034140043c10001c1d0600000300142c48414004000301c0d001000080c1003030b18007188041c0341640c2070b03407001c0e665503007480002e0099154042808042040e42c0415008002c0941030741c100c10054035240b8002d20b0101c8890f48690b4034248045407030310038441d0085001c040d034009460106d04850031640c4410340b010403141015020060b04480050b407000e0359 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 454725008 1250 454723758 454723781
    0x2030712051e24060d11040b1207050301030305070210090b070b1801050c04060c030c06090b0a0c020c030318030f120d0e0d0e130905010e0706021605010c02010f03020706 75
    0x401c40c02e585500c5090380c100584100c020715080281d4010300d40307401c4031900c0010812515141d8449682200e00040c0c12420062002c20001080c0080c1c0c0c0006071008103030a0440500d03000b90b5a5070a00140c81c240001e0001900141040c00080700504042d20011392004075400d105408594400d83d100c29580400402c07038591610000b4044014125140e501c060b62181c0000c1c452850041c0d14200d081c0164820351080001142c0a0070030305001c0e0f55210255038100343c0074071412520b800c0c100007400d4103035040540303d031511072001c004030300c0420340d680300001c01806145070103600c00e8808a04407000415562500401c4ea406000100820100d51981e451640c1151510001d0003c0402c031b640307030030703118402d500240f40c1211041d90008100314003020889a80c100b1f2050313030b04000f004104840c802030880d0300e00381c4615500c2d00300041240c212100740d8200e41c0a01044140c07002107421500c0740c64007080e003524040f0019030207411644001042403a0060510100d510f518042e2b48100c61123 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 454726258 1250 454725008 454725031
    0xf12010c0509030106050d0b160e030d09030510091e141e06130b07110a1208061009180e15040609020a050301050412030b01030608030f040f051c060203071205 70
    0x200c0540f07003820b025031801010201d40c5950751040300d0702e4600091400810107a0b071040c3c88a1100c01c0640141c5011440c114060f00b1158013500900c0090552041c0380019a990302c9100f13121280310400d4003030141c4042d88104140b400b2407043e81402855411a0341c110703505c0c5d0600011074051401002068840e80d560340d850320f82403804503416414501c02810048503d0300d0700413410f002c650210481c60f000142468107050170085403440600f440c02809000307204841a10043c0803007540010304a0242e00304444003141c0004400f0f090300d03501c00b5449001c80050541c09100c1c420300040c0d0191585090031002d540d204022a2200c042d007150440b42150b03100e030b6420402055042802521020707240540082080b070400f901c49103140d4040076104030402d600c442c10000c0340e07403107500201c00810148040b251598807038061500b45402c14042c039440b03055105000101854145080d882020142108100d01c001c19140c58000e540010941d07407c0c403c0300c14040c900200135100c4d10f480f900e5000b82c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 454727508 1250 454726258 454726267
    0x100b150d0f0c080919020f06030708010e07050c10021303080c0d020c090708150a050307030303050f07030207020a0612110d02030601030c090f2c010f09290f12010c05 73
    0x821008441003035000b40c040250010400c82c504e00c0005003a6070000e0b2030408116026001c1c40018075008001400c01d0304241c3c08420310508035082200320313058458041e041016666003080403035043c000e0300320b20543e6a128014000e9503640c55801420188600c0e04101d00703c1c0e481f902d400070780e640203100019495011914080345164184440e0090348412079082d01e05041001004060500240c414500540a04c03640c2846503603860945005100c080c0580f9643c0703681c0d041c090300503c01110001041004140001d40781d40c820b00c03c4415281c0d00400d258621030904d41c1c110766940cad00a8591560664030350900c0c001c41d9012014201d0541c40b200003503a20302d089000181544c428000e000c05000540e2414403000392494894002d5403008180b294a28541c1282140c0384008410340d82540700c03007a0b00114410000e081402d01391000703080c1c14001d07210a045050499000c000007440442200b05840685103007a0901c1902c20f00020000350b480c86c0d07010085404c494045603050040780c40003c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 454728758 1250 454727508 454727531
    0x4030c050d0503010f0b09210c04150b0403030807021006090f1404020307050f0d060615021c05030f070309060e072112210603080403020a08010b03100b150d 69
    0x5514462990b2070501d046514050f480005030001d03000c1c1104502e80400c9009088d12a054411b100311001c40c030b0030020076040601c042d11140c1c42d1020500035420041d000c00d04801c4009074208076854451003620302859038808951156001c0c0209045002d4040d2071030a0301c41c54001ca001601251000081400d00340308050b044a03004ca03440080c070700c0c114080101580d8041051404c0f2042903a020340707840150380020301010303007424006154902c2c040001c104107201507204004480c2940807580c0c0619070503140020b510300c40401c10002941040019100c444422201703410268504000c1207a040583ea500e082e81c05549a4500517446608100328800059400e5140c2d0b442c682e5030120462000c0c0c490b45d011140c0c0f080400c00303201c503400140150707081b0000103201401c0c1c810b02c10006240c50b45041c4040381e00520090348501c42d00580851041010700c1080c54014000340107000703946280700b1481c05090a4100da6501020180d8100200c041d6800100b20186400c50001428a1800c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 454730008 1250 454728758 454728763
    0x81b0c030a0905010c020a031403070b0c0403020307081c0c1e03021c1b0807030c0c0b03011a0c0a0f08130f0510020703080a0813080a0203090a051f050f1204030c05 72
    0x180c3c020b0381000080c08001015840c4c0b010b60304207494004202e20a20034100c00403d1843c030131402d009220b02c0307641c004c10076a064058050004c2d01e00c02c509443c1c400d55101201ca41d503040340340124180340580201040554003a4845071400c0e4860484100705200306900100c5c50041c0302ca095015800010031451b0320250044142c16101150a0503d9002d44210381a01c0c225001c0000620000c000101d5409060083c4400500c055100d80301111007500c4d01c6500c0c0d403980003031289154214811015404651f011000c0d55402e4001500910304002552528081003010b0002550780d0042000b4a412081400304e468020341502442c002ca510318200a200301140755802407000c64100e02c0c41030002401240c100c4040d103900d85880640e0b40c4808440e00c03034a04141100804185000542021054010000d0005c18508803a00d0000590390428007030188404030000c81c1d452072446a83c142c01e03005601401c540084003e4080c2000d91018428400034002c3d28181c000c40c0401d1000410400c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 454731258 1250 454730008 454730027
    0x70c05031c1b0204020c21040b0316030e1c020c09251202072316120507120f050616050301141201060605090f010c080703081b0c030a 59
    0x3a001024a05814240d4000d48900a9952410003038080c01100601110a4150700705540082c4115550000103901e590385211f201c07a44100481c601ca43d80745141038500030384044400c044803c03807071507031020500003290036480030101c00d0541d1400103100c014000c00040083c0c5040822120258040d504040e140c00c45820070940304680f104100941c0c944142d920304c44540c030325134245920981c00314080c2c0300725490000800750341e0702c0814047c00340600791250003107009080204070004070540d60160340324081d00b40b454404a43c0e1403020400c4c44010a10140040c0c0204184e400395500c0d42da0380c03582d02c0e54a842c03e0b1242440201c2440520806102064100f10043d0703195403a45803588014040340414441e80d41c00c078102c2195001c0c280c54050341e4190000040c802040707407a44580b000703031440e005403010b50b001d11213500341200340394003d1000021140c0c0180b643c40c2025070f203035400c60340880700900c00c5d10354501007030710403d1903004400607141c4000c4c1c050240d501c0740020a0f0050030640c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 454732508 1250 454731258 454731269
    0x618090d0e0f0604151704051c0509010806060f07170408160806130c032a0f030503030415090503040305030a12050717070201020c1614060a1b020312030a02070c 71
    0x12001140856919442110100c1d0002c000505030020402e05c1900c1801400401380c00080d003110403c41008008112800c0a07820f0903103028540149180848480c000d00b014180418040381c00705200e445c20b4405807010b00d40d84222949010304543c1c801091309418107280c0101207001c2028460400b00348062011721414041e09030182e0b24000d00c245d07495602418400c007410a44079040180300347d20440700061500b100f030f292040100f28a0100c1c0d00701a10614019103080d0260102d42d0f401441d1225040301d030006c00941c2152250340b100c034030301d80600180411b4140e882991000103102400607000442c024000317152510321460340a02a00007484515984514007030407c11410380090182c0c424842a0391203e001e036854500030303030081c13080200e00d6145100b503188800e42d504d1800128000d40d440b070740100324051600428003000b030185040f00030102e0b1340721340d10b00701044035000703819135140c0020200e559502d00c1244c0c40a041d4010b891481104d5000110941884110080b84000300b9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 454733758 1250 454732508 454732519
    0x10506010507021e0315010e040b01080706090506210705120c190c05010b150403140d141303020915040c0f0807180b0a03140702010605060f030618090d0e 68
    0x80c2c82d0381c0083d02e9960203e12450a0040c0602402d2058808000c00702c1c100c070612180e80300d039503103d400034086030350704690071101440c1650011414000200341c5204030f4104da1110349007a8100010071000e60072025500001e000760701e054003110040214882c2c01007505890705540c030700c00c12840d4801c0d280e00500524042d1400c0112402c011000b203560024120b0528140f65401d00030b160680c054515a00c91a61002100b064141201c009400030001c0701d00c40c14803c0c5140380f2555116458410701070b045d00218400c0d581c0b01d142280c009000703103002c2c41200e0700143c0c500d459500084400303800382e59007464540b004c19510103600342407040948000341410068060b60701c2c28801001c110004001c041040303440f80075044801d599001072805481000d03551500c401052200a00a10ba0000c1c2218400303520170225490a00603c07404054610141c24203180c84d1140034440303440d03440a049150064083d0003544621290301002c54060307a0100d02038040310000e20b0004210010b00f081c082c2c8241e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 454735008 1250 454733758 454733767
    0x6040f236c0604060b0402090a030c06260601050a0504150818030309070314030904090503030601090501090f0b0f0c0f010b01080924090c0d0f0c151d03101d0105060105 74
    0x3140005642c0d0350040d07011a0100e0400c6072500401c001c2c0c050819015080340d1071403004001c2007180d480c0703042aa8a140c0c0d45d642469050707042804260948050301400812403004241994030500080410304000d04000349003545e2640e103403c22440800490740080c0f02d8100b800900140d0390a0400d4215041c0011030a60a0082c001c40c2c40301d8081c800140039500312520268902c03428000d4a590754030081c0100140d04d0182406501d9a0040301c0050001c0c251800200c0c0780d6015802110075214040c0340070050a0400c2100003d83d0300a94442c051004144a4200038030700420a1000b0200020004a880060b5038000350580601802c4c140940e000030b2a1880d1000d0b003501800c40320b401e580343c1c20301d07039480f44800ca5007014014040103400000320321352079052120358030700c1400c500d100307615400c18165604032000100120b42000400140300e1901c00e0035454540312840a8030100409454400c810741c030350f000844941c142440b41c121425200c200812400f0300c1056400b52080c01c095117030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 454736258 1250 454735008 454735219
    0x6040326040803030a0e0708010c020106030c08190303050a09120e0901060806130f020c01061d0c0702180403142b05040c030b070c0206040f23 63
    0xf24040180340400196807020004403a0b80b042102d80024600e203002082907240341c3e50021702a12103400169102c0000703040c00640c0200000786004032128030f1000e0a4040b00c60f540450140034050030a0895580f034914000c046841c51000e4402d20191f920342d0000c0f01c0071007091000000059101100f40600d910130010503413142400100d80401290300000c19214440502c802409000d0541c0300175807a0000c040b48a00c80c03103a845010b04180700580c032983c1d807a81e0b0703003024074410b1450080d0071054070b00c44a49a909440d0400350032600c01d0420b44040c180801e050117061300010468016a8031018200c6400908030401140c5201084428800d610f89512180418440e174800204008520b00010b04018032501c1050344066000788130640e620717034921800307804041074051902c0e94807120803034498104a40384448100d100140400160308884081d00280304056401224444550345034111101110b081c80c41440902c003003040315204218802541448140c010501008602d1400d009e2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 454737508 1250 454736258 454736263
    0x170f04121202071a01030201021504080403080304053a023d05070906120c14030c07050115091b020312070c05011a01020c01050f040e060f060403260408 67
    0xd14045420900107610986001400920034000b01801900d0740e08044484108021103c42c12a03000f40e0850f0004c05a0341a01000a441070300c00621080d070402c020400555014095940719004000382d58101d031810b4441010440300d021442c1d14100102d00842d200d40101c2001742403260144024020841c035409080320702d4208100c038460045c00d10514000701c1c80d44904018100403408020b01403030a2080b00600075030313480d00130704010840a00c0181084001440707140c060280542da00014200210220452640094a01f10401c1d10821100001ca2401d00a10080c9120002da84000382e16001000c802c0711500ba0405441c041e501e401e00022540c008260381c100741d652050f090281c0c60700403042d14140c105010003800c0c0d50810f9810940d0454902d1510358800082e0203581d1503081c5c1100440e0749104190102c3c0c444e030b5050100b8891140c00d018030303d03401034000d06002419543c100000d01945c110b5401203442c0740c0185100381c8051440d540c61030324083c00c480b1845c01c1604007148185c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 454738758 1250 454737508 454737533
    0x1200708090409140a0b010305100b010c0f08040914040c06020f06182d01061505070b0c04050d050a03020705040504020d0b090717010b0a051f23030106170f04 70
    0x61240380c607100c84900b0f00c02e45028584c1c100c0c0307900c42200c8a0b04140d14040b4240402440151b03807034041d0044500720040c8034042c01d00d150311705940d110f41000f49030795400e203a2030130418161800300091101141c00080c0b8414807070700511000d55018103242c02d1130001c04142d610340007042190000407455150f1900000c0b55608030700590894140386a200182c9403400018001d0941c40010484c9188010a90180c075421302c0281030b03000744005602d40007811031098a01407858000b52041208034041042000050b40045050100a18240c0d4980001d81030840c01302c015103098006a4100e000c00d0340400142e4000c04040e9014801d901c0c00340c0000b02c905a0b0385201400c50104100001d901c0c403c20700c8000c019003004c404000360140001c0c4054000c017a80707002e860180500c4000450130780381112040030301100c0700c40b01e08e1a24015070390855480051030722082e051a8488629001c1c254810b01642c007814039a51601d60fa49640009003051480280c0348280d084003580500011400380700c0f030007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 454740008 1250 454738758 454738777
    0x10b1203212a07060f0908030a0c110304060906170f0604020304060b040f1a010804020310020a0c080d0507121811030a0503030f060f0303032a04051201200708 70
    0x700c030642d112003042c8400c546a01c2081c024900c680000c0006007101ca0140c0500c50146070100080c03282c0641c00005c8407055500580706042c2400081d0100205400080009195103400e420034140d240d0198130310341060b0440d0300880d1200741e05000041d40114040414105000d9003c0341d81400c80c14403440c0100030307103c28001d0b900080040c0070302c051a0040b15460001800030000240150b030404002d04505824081d1a203d1030b110919540c4140d5071580030b07980042c090050a402c500d40f580096028603207076000c0c084008121804540c0031405008540032281e400f141c103290480008250240004204901d14900658000e100c40f80115012081f60f204103a10381001d0000c0c002454465100c0c00100144000070810104a01d00302405000700015503000207840b4030001056243d0004582001000540d010880c51040c0e141d44500d020f0f004031407041c0d10b0300e0f4640c404680100c54184880d200f582d151100002c00c0412000e40740f081400c8036150318204085995241014410512031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 454741258 1250 454740008 454740067
    0xf0d2a030309021f09140d051903090509191812210f06030506090c0d03141c0506150a09032604060206090105090304060801030201110a050708010b1203 67
    0x104119200d461800f10080c1c0709510a4180c1e042445000380343c00001e0007245000c44d40103c1c0302d28941800e504034981e85901c440038207007480d1444a2791507049501031081d010041412000101520750122050140c1040c1c484140c40e003e1440000c0305850002140d0800502c0180190011800400c0c0398054449585881c01c0d51031048085e000720a44d41c16402d011861816503e031600324080e504c204103c03403181c025120275960311041152a46000401c1a0f0045407140005002070300c1031b0307100c003c1889000416070270204c21410010644000484003030340d00b9074440501c120740c80c2c1082645841060f0600e1149407000d41c00c6e0042c48400b4620008002d840e40625204803035100141c0800c005030b00d8010315454a94804c002952003030143d07102c2c0035551a02c0081142c400c4003204a078240d03041074a0703001300390340385600450318014840300c1040300c0c0c0241100392001a10500404004008402c0081014140350003040412110384154942c107500c2002103607403407015160410441c0710450300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 454742508 1250 454741258 454741271
    0x305030610090905180f070f0e040503190e2e1409040f0b1e0603010317090301061e06090f0504051b0705030d0506190902030a0209030f0d2a0303 64
    0x41901c1007076181e0042580f5909081c10800100c840c43c20807400c1c000034804440d02c07002d800282c9620340c5180c2c020501258801c1400303004614a480041d6041882007040703a140403607a0403415140c04440801c5000900e9600c1003c46604e080c41e03218281c0700c04044625004030840a103094034042755802e1005000c2c40280b1103040440803030030b440c0c4120000d001800420400309207000180b101d07002440c81340301c0390703c2d40c43c0c411031070315040b0340681c180900001d26690950700c0d140201c003c0c2a402e106c980408001e103a006480a0141100400340326040b04003080501c00c420228a00c0c64000e482003047c1940204906440c00c40010101c0e00300740c03030005441e01e03070305241c402d202c601070040034a1100005080e000c01c41c000004180c032004008041120ba240d14081228065401c01b0740c0451301e8512006104540d0194002c641140082000520300703804c20307000c2410300c4413002030000150083c51a240d01c980d002030380b40502d000407000054481c1d2400002c0061070a00c0c560280401d6518074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 454743758 1250 454742508 454742539
    0xa0c02151e010b0a0f1812080d140906070e0109051002070b0f0406080a0e061f0f06020c1519050a03060911031008010e0a02060d060f0308070605011203050306 70
    0x1480030007180111003006007a90303166040a04581e0040c10404006074034101c80d058507910404ca1303002c0151031650414965482e02c900d41030b0001107840241c07102c07001000007140601c1c482c801c031900f43d1160b203010800c07845d04d28441070400b040100301c503051000400342c42016a034060070f50010740308200ca80440400030310500f00e162030741a8004603041000099a07105031848040a1f1044420380d986440060f5902c42c2c0304004d5501e134000000301d42c1c1c4001c0105000045084500245203074407400b1007a00c43d0703200320341140d80e50700c2ea00c00310160708001c458108a04121910760500340800e41c6162510856507842036101180c3c01080040220106a07400e40512942041e0020920b40200784584520900182c00741c0d40160b811203801404d110000403940b006006010b036a4510b0006801000d00725001c1c0482d0f0f03480040d2101001d95980c1020034150f6002c14000055801100120b840d403050f840c007102110410303041184a2000448004000b03540310080300c1e40548140c0d00c168600c4d0506 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 454745008 1250 454743758 454743781
    0x105150c03160c17150f06040e1006030611090a031214030103030f110a1101050a03020f0a05071a010510050711090106021f11070201110a12050706050a0c0215 70
    0x502c007040d0007820340d140c002400342c810b51000c180d41010f0706000d410081840c4032690386508000242d21005c044000549040115a00c0f03540204e0141c004510350f41b5506609040040c21440d142c0e003540d4481c2c051003800298801d81c502001240681c034580120580090016199480014146146c0f058050807051040c84510104603611040302e17140e50b10307807030081c144100201103500010910410301000b00000100c0510b2190040003025031000c00d40c0044420368450a21031041c11b8080141074256040f410060404001d5555856141c0100d40f0300034030310710300d5240030f00440900c440040c0220340d140c1401654464190400d1a035440302c9182850007206508055588960010b000003041d0380c000c0b403000c0c40f09082940c0340010350303000c202210898061203c500c500c05c0050100d01c0055000e03010001600003904101c8102e0881d66885812480590300d85c83c0008201040003410081c41d0b020b4903400042040c02400f80114140e070088d030354104840d000403180d144202183c00f58426 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 454746258 1250 454745008 454745017
    0x210c0c0f012a12020303042001090305060a0203010f0501090803040b280c02040507020328020f030301080102040302100801030f0320030f03190b13150b0313020a050301050105150c03 80
    0x564030440e140c9000b900d0b81c2107401c410540654001180b103000c40c1c0810320100440b0b2281c0d500003d00500380c00005e108440e40030f00d82c014241400645000440450000c1120380c2c0718614039000540d80358107007070242d11061141d91255050081d1054140103500010040e5425200c00c0160262510400710b99589140101a6650401c0700c8442c404600350b42e00c84210341d45240255010300513511030b008200d03503e01c02c8888404e0354054407182003040d40c526034000d0180040c248101c1e4003030040004494155802070b4080e041c50380d4001010800c500b080c0c289011202018101402c16602d5500c5000c20038001401c02000c11022244a804280040100a0080042c80101c3e43c23030795071558000103160700980300001880c6900d51107408240681c0228102c03428040d205806070b030030040e00360016100034041c510444c5800b03813020810401003c003540c0301c1c4840000400f81c0c03501600502040c60700301d410030390090341030900610040d01c43d041000405e090707404055960790514002941903004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 454747508 1250 454746258 454746287
    0x109020306040b0a0603051506040807030602030c09031c14040f09150314010c080a150b0d02040e1302091807060c080d09030e090106050421020d0b010305210c0c0f01 73
    0x4c02c1d074008640d02c1c2c0d056100e18410480da10804002404000400c4518003c910a500250340030302030510000300709401441c0c000010591950500c00007800007401c02c44c61410306d008070a10071200031483c0c2c0d40a0170703082d192540c0c1e0780c002c0d00d03003414584108a413600700e000d00f600d0b00e44c5030014240308030b91050540c0001c5402c01d51a181d00003108506501a242d800c01200c00074840700c0110304012502e1052082251580e4042c0c1001e0f07141a11400d40d64000e00e0440c0800c513400d0100003160121030301038a104045044400145425502c10840c111001030000c80f01d0000f2031100e1405080002105e40588d40320f4141402144807034500392400e0b10402c0003020f07085090484bc40101034000c020b40f010b14408a5105400382e8030741c03200301ca1601a0b44112001d9200006154103000d0248042108960000d440b90f42d0055081e1201500c80c0c0007070b4001c8415611000d11500800c0581c44e0f00c0c0541c3c0c040d08046071500105228107590303407c0f501400352050b41404080e404507802001030060003003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 454748758 1250 454747508 454747519
    0x90c0512071e09090b01020c0d030f1701031505070503160809010e07080601060f050a05070b040f060504030e100201061409090c0d06090c0506090108040b040215070b0921030109020306040b 83
    0x2c121601c02000781006100d01c000032410101e8901c102d600101c0c0240500710051300d021050030041d1005c43ea10b4120380d00700c00912010a50444500d070640004601850041c034918100d2403a985940742210001460201000780c04e0081c4901a034407005e9080c40050103103480190ba44408050f0b6005104030b240c2080070784511100000c19401c0461894100c0e075842d1120040c290344600269414850048141c000440c10445400002c01142070f01d500036000d40d0803016004110796800049070400d94080d07020494003198481513150001c030341d100349003071803000340f0002d85840750000f0394014224110340b045c2c1c3c02100113008500200440404520300502003820441e0a050010040841d0101660700c055001c00c0400d041c00e1000455160b9001a55901000d56544d250710768a694003030412640141c10000c01d08900c01084007611f56a030050250080c64105600c28900c1c0c00785200503c414580544e205000c02104401603030304480d50f0b4130340944c0c2c03a0f80300c00c000740040004e11202a40031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 454750008 1250 454748758 454748807
    0xb070201110f030406030b1801060212180a0801020d050604020f0d18021f0f1805040e0109080417060109091e0611030a050406050a0506060d0b0f060c030a09090c051207 74
    0x41d9455005000c080fa016181e03171020701504a050790232910700b4011100542e100c802c080f070755056401c00600150f180c448205098404d0b4100081e0002101c1c2d0204001d42e40104070000341d101503101e8903030040b02c102c80c11450900d0001220566005c0c03603500c412180c0da030300c498201c4804000c040401c0302e640140b2505280444050a24640344081c0146000504804118090902943c01701000200100c4810061460207080002801e174901800d8069503c482d405030004e200074004e800948042c40300781c0100340300302e1724551800c00140d000402950520501802103240301e030032001302900400f402e0034010b03441d080403405800841c807074110711280001082205046a07000d0350185104160900040d00e03200801e00c01d651040c1e6544e40e0009003003003a04919001640510040385015103609540340e00c03030740060b0458102c1d00306d42405070000140881180c0d0f10210110103440314540c01c202d00b003e2108000e14074040d0030310f500302c07850b100400324104501034885d05c07540c030000a503941b051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 454751258 1250 454750008 454750019
    0x2070803070503010e0c160807050a060609050a0b06030f01330f0e1906050d060e090102040303030501060c0b01150309060216030807091d2701090c09060b070201110f0304 75
    0x20b54024412910070280717180100f4050504a8111649a5108841916103802a071548600c035800700108603035601c00c42421900003002070181100410340303500005940d2920540403800d5441e0307401d50b00d205500401c208070b800800300c2c2c030700e0703064900542c4402c482c0c40c0e8040280b2004250043c00240800c0941c0012011036400400c56090004130350b00d03071a418541c14140028811a0060300901c05111401480f03841e20450140a51120580002c00d0b40782c0e4900e0841944c540954110a2603500000c040c014580c00d8012180100420b18103180c3c7c0703002644510051840600501c0403040548030f151644a129402540c07485800680865994040a00c800717030f00000501e0440125858a0018036003e00074604102281c0070114144408100c0c66208103003504000e107010f555004982240300d25199825540002c5900d82d00002807140702e82c10003504007403250303000143c034905080051000c0c4d80f21200307440c519642802d119840309420700b413942c10002e000071107220500c40820005007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 454752508 1250 454751258 454751267
    0x1110091a04410603043c050d020c0307140a03080d020c12310308030907030606090c05070b070c0b10050117092512060f0b1807030b040207080307 64
    0x1808044415a400c155a5001c442d29103912401011a4850030620010300418108080080803224040035481e078402c0b1640c1c9203d0b001801901d010032002100030001c02c121301000840040c6030309000078020342480000107565103081d1f0041100340b841011452140d0340312042c0714800745602c21482a01c0305500da4584000350040b10b80ca010383d20132404030805070308040e81155004d44850b0101e130300e000061034410f1661941a07441c1d000764040c4510000110341140e0140d4050707040e08010b0031034149941094010b403009508000b680a1410400682d40c5e504141150400c55011903605030513500e110003561402244030b0040c00c011440c4080040c1001441d000000b51502602c4d003005031220301c1b003448804081120038507000c0c1e001c0381c010001082d400040d00d081000700e042c0309203202c0d10351207840a6954035000403660b058540d2850942031a440c000c120300410169100c600001101c82d42c51943d04001c2d1101083c540e903060b18029603140e98040320003103900013031001c0c1d603420842070040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 454753758 1250 454752508 454752569
    0x1803080301140f040608030a030b0607020d0602030717060a060c1a0c0d181e0f05030a090303030c02060601210f020715060b19080a0209030115031110091a04 69
    0x2880350140054a1201340fa03e44140c409450111000710b05000c0310090030350061201c0a01c036a4881001c1c848240180e9a407044460031901c2610003585a00745800b01500d1482d2800712804460a00000c0020341d48030599040c1c1214004d1502c4110740e031460500e00c052425100f00c0d501c1101500041104000903d0002e00404480c4d900800881c66907010341400d081150b100140724502900742e81c00340040708017081c07413014061040b19183d500c1d966074991540e4468100b00000c04e400720410414150588a810032454140c00980300798030309400000d05580300c2140c1891400803038071520200d400c0c150b01c500b88032003282e001195900224140218501d250381c6445103814145040420080031950542e046010030a400005e070040c4900300b5101400b0061041c0d001e1a8280003070545aa024007504030781d21610038845080c03606504007400244a20f034041406020348004440720250301024950440314015550380c1e10401000d402507952103194071034420424042c042d004004801034925 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 454755008 1250 454753758 454753799
    0xc3906060108090f060c0a11031303020301050f06010507061a030f03041e031709130614090a020a0e0409050a02041e0c0906170703090c0605040501080a09050d1803080301 75
    0x412241c3d03500c00c41c031a40c40750851303804030360b542014001c1100b0800b00c03005400d00e4200c60803c4001d40403000c0080340340d6003090041107030704083d2400400641c20203210702500300c034141400c0469440e200d8000703441845030f500d004144950358400d103000c3ca4950007010301d10b00001816a0240c040d20040650360b42c0280c0145548000c10b0740c0701305040030201070781d03104481d8000071a030070b4000344440500040e040381d204541c000080d481d00a80303004191040401610b105040c082100b480201030081804005201d40c56062040100e0b5000310b030408519620403038100d82c04142c20b04a4a010350404080781c90094009007003210101510b07a03290341c8105540c00100c002c011103003080300c0c121011221445044089481142c203400355005c0342c2c0c110740d8064500d040c04a1a144560395202d031051a40c0e0100001a00119090103039680c0f004091350008081c640610580c43c0544400e51500340b8070310b8040521100c40a0b62003400140c802001c02190014141030f101d6079a07100080c030b14803480c260b1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 454756258 1250 454755008 454755017
    0x301080a0c0f050f010521011205010f1418070506030a02030106080f0c0406201e12130b072306061c050c01030f0f060306150503060c39060601 63
    0x800e0321182d107600071007100e000a0907160640c0500c0015a401d40c0203076440c48500d0342e8032000e03001d980080c51196000f0301d41902101205402403e00d20b08540c1741c0d0340c6400b02c490070034540c00b4041d0903080201e40c1010f0800c50014001e81041c0c0114681801d0707621094001d8400b20030030101e0402540610b04030b44590b2201c643c103070f4418440c420504400c98006500040502051020038072601c100010104071028240d00c07601c5c0b0810040c0f801203d8004030800e1785c485030045648060074800d9a0200320928021410800d80f24584000c802041c006d450a8600110340c03401030120030141c500e29485070b11020003542c2040380031507803507440440361580204506040e220005040241e05007001e0380000140003050345100c0114058849041e102e0241c80c0c0783c5020346130401003031190070000c40c07056100161400c86002c00850404183c0d01c0207129410420030000203c1c407290450380c000d02c0214003c80c0460702280c4902280818910031900341200c08692800030a00060741801204240c95 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 454757508 1250 454756258 454756283
    0x1060902040e0105150d050a060b0324040204080c0d05070302130204080106171c02120c06090d020a030804080a14040303030504050c06131809120206070f030507050306060c010906020301080a 84
    0x2440400d134103420035005d503030a00700075a41403404141d03c4580c120740c1c1180c1c0410baa660342c1c0c2207110701c0e800a40d10b0980140d84a501403c09031503842900c14041f40540e400e50808d860b0001d802e4964407040502805080140811810040103108043c0916801001c540030720b00c01c041008000d4001d8016000198171341200801c2d02040030f440d5201d403c0c5c03950020002c0540b50640e448626100ca1517010640c4038403001440841d1108000d015030450042c01070421703291800074103203003850000740801550031040b60003000c070381d0044030540e019410401d503076030301c00e401081142c0b200c100c101c0d94401c0140114000c010154907402c840c0c05540150221000d10b9810001c2010611032035111a0a480800710104146030820601c002038503580705001400c0c0f005e82c1c40d2483d1440b001d070540d10058000b94100202c03107812000340611140715203010001440c01000c050054440500018818800865032280c01c1000f50003001c5040d03400b00e815034070395a4070b00400d5901d025100003120907250380c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 454758758 1250 454757508 454757519
    0x30a0f030e19090c09090203090c0118030f0b0702030904060902040e060a0b042d060806010206090105010b041703070f0b0105012a020904150c0507210f0e0402070501060902040e01 79
    0x107140b041d14000d54001e040349503c0c0a4003000145083c0350760b00148401c000e00003d039a5214070245200d020900b000d40080c1c18010300040c10861049072080c50010320788030620210362001d061034021544922100b0864840c20800d9155010318140550b103d82450008a542c1e6100e030060012031310450210005e645a6030108540c42c4214026a012810280400c200c0415020921500401406241e0f901d12003640c41407402c08001345c00c8070021801c6003091200550b810030401c2d41c44003400e0020095541000c56280151183d44108241103000f507085091030300d01031040340c000b035a00000c0c00c1d6241c0003038039242d6244242485101e012410600012446070704d101c50000b000160b004052540c02041d030300b0444449006807042d101c054141401e40c0c005440b88c4030f0441880c641da121545c0b9210249800702e0400c4e8640314008140300040c0141e120240c10907002a0090300500349038100038024400718000b07000700c07131001c0d00360740c03e0003000101d011540e80140251501001008456a2588c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 454760008 1250 454758758 454758769
    0x81e1f060509101206050402071109280c050c01020a12050705040e160302191d010e21030c070f0305070b03090d0c0f0b010339090e0c030a0f030e 64
    0xb91109811505210501086501c11309588440d07180300c660000e03429440d4804181207070030004040b10f910801401042080c40c00e10140c980c0000d903c9200c0c0c08074801050352110754500c00c400a6051502c81038110311070380c0103c054407610000c29008540360413851100811009988070010300861408000c905031b184540e044a081e2400e03c030701d8042984030501d14840071450030000008142e8203002641003a0b031605842c0c40c01044558171910320000c820010142c01a40b6402d01c0d041c0081b40c80e40030803944403911150f00703003400740854400f00d1003118007070740c02c51190001511039401107607004501c0340c1485080c08240ca0207402180c10f0039481c0c1000101a00c02641c24000300c0e80161130010b4600e10908514461074414452002134000959924000560a0300700711031800b54480606001140007101203199460404840b161400304111101483d00900642c490640c403401e00c101440010020340005502c0542202c00301403482c00d1074414102c035564224005523071140c101d1024a0107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 454761258 1250 454760008 454760017
    0x102091002210f041a31050a12030309020118080a0b060d03020c0607050c190e0a06060f050a02070e0106080f0702010c02031c090b0109150b040b030601081e1f0605 72
    0x90042c5624240c1000c0d5403082c010034540b080e03800309604006d207001a104404030700401191020b4032502a92110b10b03c51503540c2507410079401030701c0d01a002c0065405040e03641a095406050010f86900d45000484001074000328141228404a0380040c4000c000503074103040b240190400002a02c56000f0060504c60384030780600181e124400d4451185858001030182a100d1005c41c0d0000d074061010826580014407490180000c0b0302c010084c01224504c542c1e0b0251007910104035160510102901d55810aa00e500c104030001c618002c1c064000c210842c040c02006602400640e91190010090582211101584142c84012440c801c1c014001c8000b5102103801442c00c0504000b5441d1850070500d8401c00c1c0180c0341c106060101d0904c503881da01170074081b0404298146114072100103c00203500441c820031080104200e015900c0701903030b40110342440c00e0505922800d0469241c1e04d41075240076410382140003030100020900b41e01011544001100c1540075a4807141600c0d580903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 454762508 1250 454761258 454761277
    0x90c0e280e0903191106011d01060f0207060503060103020c0a05100b0108040b07140d020a090302010207081501170109120c020321121f030501020403021813080c010209100221 77
    0xb0510803909241084d80c0456903d4a20b031a180b10340d00815000e492508000f81c1c0480d6a0703c681c0c958803140c41000982e20f5024001c0c42c00e1034130703c500c49a5002596000c0a1194004008010000c2196688681c0449080100344012280c551416040ca503483d03850400f800a1300c40e24095031100d941d40500300c142e109940166130480140e54281c001d45280001c0481a40c83d2102080400b401012503c090400c40300940c0d03a10f18280d04500c006403078074030141c00c00c10155103d80844000c0900003100c4a0640d0b01d10388804503031143ca400800d000d0011400002c0100c094108140d000540c0100c181c0d50484c0201d086034040702c4020f100f12002080788a01c81c901d9003080245401250601101b140c224200d050414039100c01c2e0803007030180d250349400c101c0703841e50009010415440d002015280c54101890020301509081d11b21011480c02c1c80b600400d806004150500340390400e6040d6041c03010050504111800703c2c99009407144e143d1456144900c00051031700b90705481e52420340f440d414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 454763758 1250 454762508 454762513
    0x501031a0702150103050c03060f151207080f21090a030f050c041e150f17030f0f0702090a05040803060609040b060714071707090c0e280e09 62
    0x414201008662000c0245a10254031481d020088001225040140210b004001a142941c42c0a04140c203046026000070300e498504001e00503031164060b145452850100d03002d01d000411000950706001d5264000d105501420300b0f2020013850101d0004141042d1486840c60181c506c500c0324001c1c014620707403d27042031b46003c0c2803000600e011200148640a4421110900065030000d000e50300c00851400c241c030000615084c0d040307000c2c0a001d440204020950a4050525400700841c40e40d6203d8445803642e40040040021003d0007111440d403c0c031074019685d103026800001c0c0d40e920255049000d62000c50015030751140c40e1007054015580006036138515103074070080042030303003200b059694000d0380c0d00c0e0300f640241e0380d0b4070042180c58030800140c00300c1d00c803000405003011516032111003060b001d20205506c0c0040403440400b42e0725400c10005181441c030b541182e4440d8000b00b020b4104c2da44040110f91401124855249850f041100c0b01c100d640ba0740f0322000400381078031001c1030755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 454765008 1250 454763758 454763783
    0x503060324190f051503190b0f0601050d0c03091416051e09041103010b1008040204020304080409090c080f070f0b07170d0e0c100816030612050f0d03050103 69
    0xe0300042041004000342c0321001c03402544441488040355002d0341c030100c900300344c000f01c13440c0e0703080030b1103c82641c04151901d10600d0b40300351218880c0aa004000c100428034034000111583e0080013669800441c04108014494150f44040d00410404030300769200f40e0b298040c06200c910005a2031506010901c907100301c28640302c240041a101400c5481d03140224100b10030042e103404d000c50340310758000e40c0003101e001c0c10b010505084858440e40c039400b8540246005171000d4000c08003540140d0b055800694940e100d08110400e80201d40042d480c0501700040803042c4000d0742464415507888800b911407001950410954480c4280700b4900d900405c0101001011020805018103a000744044900501d841c0d544003400d82c0606100e400d0141d44001c02000428100007404200c841594518522048a100501061130061620b03000601c407001100f0850f00c250401e000510801042c00a061b81d90302e0702030b40712004294100800e03c644980001c50910034003c4c607048a800050204c400b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 454766258 1250 454765008 454765021
    0x60c0d030b0f10020109060506030c0109060f0c02102007050a06030b0a0b040f08070806070e090403110f0a031403010501050901050a02070b044e02030a060c0503060324 74
    0x14029070416103500251040b003540d181d454a4940c440c254020340d00001d00c003900b5240403000c0300c4d005032006000e07a100902156081c0d0300300e0029410b41d0020305000c21045c0724050111003910914400941007805c107460610000c0c0c1250351041844103d03080d0b41d280e40305140416558003c584a1964800c1c070502381080344a000c4c0d442030140e03a4000c0e242d10062503d64040c0609a401613000751410f4074188010132190368140050300c05490504060581030a050302e00928014a9101c50f0784160000000b09040500450640207041c04c000107666952422010039030f03c1c1c00d2903a2065000c25500701300d009018a406e003c990507078805860700c9041c0038809004640d1600070650740d005501c10580041071480c0180013420061075011144800c000e2002c0160b43c801410f81c180c142e120444180c54001c00740c00c80b0a01c0d1514461000140d141038090001914040b480080034001070b07d8440ca050026074004029445044c041c0c0c120794400480944c45801c01078414461050700100074085881d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 454767508 1250 454766258 454766261
    0x702061b07060e010c1e0206040c05040f0207170c10061203030507120603080d1404020a05131d010203010e0c030c030109110c0d030e011a090f09030c101a060c0d03 72
    0x303181c042da90002d0507818181c0030a0846804440d400089101c40c81402203030000e040140d070203032911784060086828690368901c280b1409029162285450340c0030064425170550503104085d03081048290000356526240c000d0350310611405040c0e005800116034004414000d010880321100005004c0e0704407510118001d01006c0c0001c2c0c10040c2c214034440c0e00020902540d0065406252003030340e540aa13189407401c581c1e80700701c80030300711001c4810400503039a1011a4400c039082174030340d035550000044404006112a05000c400002e607100c3c4944916015409103050344d406400b06030b034948592042c00d04a0004559a02d5044800c0005000c0301c0039a40145407a507010342c8195080c50b9801c40c00e542440c00e205c2c4050002a43c4030340500b0140024090080c64440443c4da4587d040c00b41d1000c030389020401420502070f14a0b40c40410000202001119000303200b42c0191040d103e12422440090620203881c100324020f425480842031401c0070459210301c2400c402030a0540b4815010340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 454768758 1250 454767508 454767517
    0x5100f050d02120d020606130c120b04180b160309021e030a1703040302060708010503030d1107081209010b060306010503060f0d12050a09090207030e0d060e01090b040204050702061b 80
    0x980141c00020311040344a0b0400c0130b02400e02103a0054111440c014081c4040d40301d40b000803c105504001c00a00e210b50040c0c1d00d0b0151a200c0707140407424402c0440405c01412010041d030310045a6041c4100600030380c1281c840c0281c02024044c482000c490f034046054401d860006540000f00100c00e108510b02458180322050024050352404005610b501d050b820458102020b941e03000400c00c0100340d4144162540035001e428500c021394113042c003090362805081401060280c3d11030350041131094030700030f40f112180d0200086582d18000804c26850910540d031409041d800c22200e1402490964113aa1081106a59260441c5c0c1e0b001d007000004510120159080419100c5900c0454400390000800c11220b031509945c40c040700c0d400400c00070541d4828424188140802e20000303500412900040a0440e0b51405000c65802d0174401051640c4400c1222341c0380c101da01c0b003040381e1300c140d091155000710f80c01c0081d940c681c28107a0b2030b0801282c541e01d0074070350740c2c240d5001d0440c1c9a0152 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 454770008 1250 454768758 454768763
    0x90614060f0d0c050907030c0809060106120f060807060c0302101118120a06020a09060e0607080f13141c02030d0807021e0106142b0f0602190305100f050d 68
    0x3000700356551011405c034460913034180300000c4d111080300d4615070b0440100c2c0d400c000300c00300070180ca62401d0401801c400c41d1103000c080d4a62101550090303404143c120307030040c150607015142102c0d583d55010380302c182d03d08403c4000d4011081c0400760000f19110f442c0400c000e00c4030603844c129106c681f504a554115003441c0d44011011801c4119000c10410070740b0303c611a0000684c0c51120107409003910003554060030030072400143c4011b480e2101d0041d15102640800c0f0709031200064070603281580a40c1524100540f02c4140c0000e000e890320345000604403094440b542040c0059064031886840303144069050b50245040d40075940c8110001640202ca038030503594010f0404030013014403041c890b000c03a00b681d150f4100b0311410051500402c0f640b402222040e41c02543c06c5151082c056102c1c3c0c2034040c50107240b02d042c050006100468426561003901190340d14154070b200303e4032088038001100040e14050014001f40d0b42a12400c041e030301024802241249001c00300005801040002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454771258 1250 454770008 454770023
    0x27030c0213051509011202030a061a09090d0e060403110d0309090908120603030c190213060b130803130504021806040e010611030a08060d0303140a090614060f0d 71
    0xc0310091040340300301c5024000300d04100d4104600201004201c84d41130304001c42c030b0749031800d0000040c3d40000d500c0311a6503205002103950050402c080300d06c105c0d0050025040060360040003000c100102d55200101c1c4249c548010902c481002d01c41301e40100d000061101890403505206441c05000c007003003040c0309241106180f9255243c203010348a688004070781d049070215401000304202c1559070b03030000045d00151700384031050001c0c9030b4441101c9000c90250940448200a54513a5076020701010315840d010703c90a03981e4100103130030382d102c4010480ca8801c003c030701017040d020110843d40001101d1850700c000c0d90405041000135030000c1054844e886865803a02c1c91a11201c014100a240c0ca20503503115614022000e000d80700000c101c1101604200304042c041c6801c12004e0307400c15010303035051400008500d020740040001c1c801d510800e04c1c01904011100001342c12110510b0b11452046c0700003003441240d09140441a24035560120a6440a600c00d042c0042500c1016024410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 454772508 1250 454771258 454771279
    0x140718021e160308060d08120705070b040c1d04020303040605131737080a02010e1005060118030c0b030403140f030a11070c14040b2227030c02 63
    0x400c00951192400c41a0300b5400a0014145078203e0449540200191440360010b81c050344c0e030600e180b140c101e030825009041c20100701224410400c0d5401c07240e1100c0440198200340c00e02c0d0404212500c03074800007041c2102e403140c00c159110a440d000b40d03800b41c010f50805040c00410742c2c1c580c0004058050741424000000755010369000171015001c6004090b00c081d115100880054440c1d608105e2214441a035903040002c8640d00c8264400c0d0b0040c54854035030782441c100700e01505004a00c06058401d48051b585203502c954405d5010300d1091700c0b10040b0351902c03180120001a01c1c80050f20441a1500810084902c003004591051080c0703844d414088241d83d10303c40640061074540d0018001000700321301031140707100d16020144490209404d1207a1941d078881028801e020301d01c0c1080c081280105141c440c1e03002031050740d20081605403503207002c038010f85070a160350740500c0c075036030415540b02e4107400140107002e0020350310481070b02030038515242915051440030040760400030444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 454773758 1250 454772508 454772557
    0x180c060d0c02010c0c081207030b190608060f0d0b0403020309030a050105190b10031505061c0c110a1b0b12061005040807060c060207060e030714071802 67
    0x1006000c0600104000a0800c244840003801c44040e42c2030030381840b00801c08200410b5140069901b11000c014891901e540c48510440180440440031508000000178800c0c0010903c4e060000b503a061b592a1007099495000f00300e4100401743c3e00d1078000c80c1100c0740a0115004103003440d4411700074011289040f0083d000309240c0140100d054840303035516028800780c0409200300d6207a90000f000184460445400040c0449060b110110181540e5000382c034444903014040c44c00030640140110384501c0103036076207185410a5242d03850207500d807846a0388000c0c00b41c50b100408606c2e0800800404c0c3e495a500300f8121040f03070414010402440e030004005207903100401202e0b08071728035072140e070510f0801c2c03003515001264160244241032100341311543d000a00002203a00d286003804284449080c143c5c02846002c0f00505010309000c0c0b10004d8120004c001c082a5111f5102c1036080c041d40405203855009900552030681e0040d0400c51842d9010b8000d041084428244050341c0000701c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 454775008 1250 454773758 454773769
    0x414150703050318060103021e0f1002150612031603030921021e030f1806120103020a15050f0c0c0a240518040e15010f0e060f0108180c 60
    0x440d000c80001d0000010041e05001051000c5408a13003800105519415980001c0c029001d09828a001075090304590b203007641c4042d0104441c1c580a40500300300144488001d4030382c1800340d1580382000c100800300780385040c401c016200010b03000b00618101a50003038205e11003440d0b40020350805407901c510b2004100d400003074401003040032040c40b2034643c160a000e81081d40d1941640c000403911030780010800f00106c111800d42c40602c110503500e24800180c06100040c0b54071380c54011a0220b590444c0090030381500e0b041e0380c02290b402c0c070300a5403036469035440c0d0365105209001640c01d200f025607000d4080045e008407908081a210a0720b0308102041c1e01d6003250703004880d000d00707140c1307001443c0902a150110100da18905a880c0c0b108000f00d06800f0103400c0f24440c0642d40c1c4040d60702c01c0b00070511080c104044240e003a02000d50f590055030510515a0084000c001c68204c0414400d161801d41d0f24660030301030311100e8050761082c0382d408164402c0022400d690050701c10741d80003076a50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 454776258 1250 454775008 454775017
    0x2030702100f0501090e03120f180307050c01030b0a0f050f010c121d0d020d08030901090b07050a09120f06110d09082703060a050a0f090602070b1506041415 69
    0x12040c00a0701390f03d0440b00209a031003045e2401c1a43c0c00410007900d965010449661744a100300c01c940d0b032035840704002c40d540108561004005c500010511104100000c40c01240190003641e0a110b00311950081021410061127240000c00e8000d00c10892401d03d500c44017002c0d0310504060882015680f244841c000f5001c10300400182c1c42e4540d0f000d1500705c000710704145c00c1c054a05c1c00c070190081d40800c0c0b2030360f03c030380000c0c00b044e60100c0015400d207003d400504120f03600200a0805045c040c4001c0c00a400030742380c4c4400324540940100c0e6500c0301752440031041b600070345404c0f000002c94480ca0001c28020b0204130f080d0704104044800b5041038041c0201440c85074046035038954103180041c44002c0c010712840301c51800006074509035600060a5a04807550050019058886d811590002c103608804c01c00c0c82402c00c1c1035003040c841aa0301800c00340c4d0003100180c207181d03155400c20a4007440000704c60f900c582e060106201000035030f2009598650003500325041078508c8606005140c11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 454777508 1250 454776258 454776281
    0x712020702040e0a061508150a0902061207080a051504090303060906080d180605072018090f0127030e03070f05240708180904030305090d0206060d060203070210 71
    0x1c4c0e1005810020148a40350503011032840c405c401c50300b007807100341e10b48041c0300c28040c0c80104140810440703030321030f8400d01d10b1942c003d10690b40ea803804801c941400070121040c90200d58840f00040c00c800850003024801c108140d400540750940004000040c14003c80c107808044d42e0b0071703011880101d01e02c42d44001d000c08400510300c080040344010030707100d2403d030542c81a8158410420402c2e4104d0203849a0740d81c00145210000e0000e4074031250b441c0710b00803080e800011b412070702001101f1045640c3c02a80d5800c00d07180c004224039800343c243c440b500d00002c4101c4070714004099003007420004801c0c90b4404c0c030300959101c405500181c600a5140c20000381a040c50004000c140f034041031008400003c0d00d00820b04441e140b11b800941d019410001c0c0c40e052000402d502e81c0208203082040790500140a10b509041134140140280401c4901607013620590755180700040c00020304a10820307005016100d80c00311982c4080c040d400281102040d442003042501070700001d40202181c246 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 454778758 1250 454777508 454777513
    0x3141201090b040c180e04140703032a030f0e0109090e010209040c02070b040b03060d020306130302250b070c0e04031106010905010e0406110d020708131502060712020702040e 77
    0x1c0000801c0b00312003e900031030003070000403520844a8501912018119044007856015942d25070800142032000c102c810180727400341d502c001c0101500240b0a002c00d031402c40f0140c0d040036141c4140700070302d20004009004100408000310060788a61068258542d0626191444580c4c1d605041c055841121410303810b80d4001c610103843d420107201d122a03000c82d40c8010250300c0d01d8074040701090300caa4010801c06190000008005482e40120081d1155003d021501c0614044e44901c82c02e440d961802c0300103005484003a10001a03000302031800a040842c000c00e4540b800009e10090b034059581181c1100d020540000c509100310b10151140c0c1c06a242e98040200181446041001c1604540500b030318010043c0455041c2c402019481540b003440000c0c2080da00c0340900a40c001c42c12545030b040c1c00080d540c0c00b00403140002c1c185404000400c03000160700c8840300c0441d440407244810069100c0f00c00240924420302240151480f50b280052a00b030254011400341c400f1110500005d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 454780008 1250 454778758 454778771
    0x1b0705031203010e0c0703210203330409061808030a0501060302030114190305120408010f0b0904020d0615030b091b010917070e0a060e010806090a0314120109 70
    0x28101031182603601c4000d079084510350b604101d030701e00d51150050803011050401043d1001054010144e85541c280480c41d03040c4030403080790319100a0f61040307400c8a0190440c11509681401200801c481c00c40c42080a90b100400842808010701a07404141c50945d1600b4601d501110216404080705005621580e134078501628442c0c142d42069104004152041004000f02c2e020480f0700d00b259a0210342030800003203880c82071100c1c01c2180c1c0028159014107100202c08a444e08014022140400000e020710b22140079240c04440d02d685000b0f4004038450001001480c100800c0a10548a2000043c03101440c5000040001b240d400407201c0342440b00520207060020003400d002c481030060800405004000002c2c801d4441e8410303402c1c0d4080d181d400142004051241c03202510a80404210500d01078600314051305442c03003000260a0707007100104d410500030400512503100080207101d08002980c0440b0fa41984644143d080300c0107004d1109030034888510365000f0300c800040410103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 454781258 1250 454780008 454780019
    0x20603070f1701080703141c1215061101060f05030604060b0303040905070203030609180a02130e010221060a1d060a03050a0302011406060901021b011103040308030103030e09091c051b07 82
    0x42c680f070b0247c00c40165005402d800182c4000201100e44840545011501140d0365503400e0b000c2c094004483d060710a82a401103455540010b1012411480c41c000303001550380da842160303400704240513864154105000080208041d500000307800100941202e14203640d81080004444080d906400140c2000041c008146051003215400000c0310761680c205034080d03250701c0e58a80031142d0081c010002072406005c940282d900c0081c86c0c031080350007075542d0210040458140c001a04018046003030b1000810351078140040540f055908203445007500c00750040c500141750380c000303026a0303100000030710200c00540e05000300455a44a90008100804030164403007803103c0041c0317035500407101484500d0b9a0b80e030014400d4908009a01c0000030543c8880c0122005843c040114055100c001000410400800011030403680682d90309110705486004012145500741c50b8401c41da4440140021103080010f2054280311190030a2807501a00c11407405041180d03039000d50f590340150804000d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 454782508 1250 454781258 454781273
    0x1f06080601091d061002031605060108010606140d020706181505420913050c09040c053307110907020d1b08040b0405120a020603070f1701080703 64
    0xa04180300180710884034005151482003c024405880b07a17440d0342070321103480c1c004d004032100d56920201c040902c1c03d040c1050381e42c8400038402c140c0300d0343c40c2c00000030b010391050003041524611002c0c9245030884030200040079400c2980c040d51940e03918030309452181009080c0362442c0e44640d4411140810020300c101c12110300401c1c8050300503107000c0c2c00220210540302d100c0078846507502c0030b014900600300009280031050300990420140d40c240709030080725040c1f0050540c4200200c0350000d0012043c481c6504041d5001000140104404e00ca94940340c0d11408001d030780030000d003290000b000c410704124005090122800c403000503140061103019a040c0000000903240b0a085043c0380360025520110082c00004202c50006c010428401c055021200680c100b0390141d20b4a45822458000750701910a4503c980b03050f803c0064100301c0030031500300080d0000d21305411542e800c4019a50080111840010042d2031a180f8400c8802c1a030300078040d11503074000740b2600b0f003146003080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 454783758 1250 454782508 454782527
    0xc1401020a030903020d032c0312130203060114010819021314030c0a0e06040528021b150403050a050c1e1603050712021503130b130302060604051f06080601 69
    0x10109410207004800030415510b802e108044c0840748230011103104455103085000316212860900c1c122000d002101c18102041000c02e4001c400340d441a0760303219040044680f0b000d100d607001c40c0004001507484a2945103114001002c1c20026140070b65100c203c0c990241340703802c881c12881700c0d0b000204441c1020480022458401d44001000608040240f40b0502006090307911960321000061045c2119043ca14120040c4005540450000c011400003940150701c8411034181011300b47e001c020000102004080c8186c107003196540c61b41e440c22680d583c4180c2c55081071020030401446000004c00205801091340940181388448094006080001204985c802035040303500074004240c0c0815001c0440e03e60500605001049201003203480207540c1c2460243c603004010402030403000320003046110b1141c4550b4a0583d41c030000821444890000075005900500000d8020b081c50b81c891600208843c40c1200c46914019080040c41d080da0050130004e10441c1c1030005a5030060240c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 454785008 1250 454783758 454783783
    0x3c0f010e01060f02030f090315010b0712030c050a0f020c030f030c07050a080d03051003020d140111031e060f0301050106050d05010f0b07030503040c050907020d020c0f100c1401020a03090302 84
    0x6100ca41c2c0c2c000402541da002c0d00071440700f11140003954076a48d940802c00d9541d20b42540050040e150380d544c5c04031034950071090007a43c00101c031041c0301608500c24440d0f086118100d032113107410541591412116178a118801030107610030403129501c959420880e10480041ca10003e50307a99010f6450359046c00502d5000701d0050000e41e00601c400e0802190034a0000c2c49880c0020740c81c0d6500c1d006914000c0307d5403000e5040156600050140100c041c1c003241c2c4980b861000380140e900344a0403216521080700d00e42c01c41500502d02c0001d41a003101c0c030340d80299000b410298094400e00001c4d00316a4281d0144020038000201c81c568a980d90003024010202001e10035039451405844030450320500c40020100040040090100480428007101500340640100000e2074400e80196840045068000c00341c420b42da11200700e8507040c0030b1003807600005400b50f50307030003009407040c2c84980c40310300202d45800c9018001c0c000c581092025002505240d5000300da188600c0c24080d040c101c103921003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 454786258 1250 454785008 454785017
    0x30605040903020304060f170705090906011d060c011d0a02090114010c0308090f010f060f0b07020303181c03020109150207050c06031518010906050303033c0f010e0106 74
    0xc51020036008405e0703900329003080c180f041030401c0c1d1340401c031420456444a49032034191502807100c0c1c1d83c0c0c0710018004c600000d44102d8250f8446500555140640d548155101040700d802c01c04542003c401410012001c440042105154198241c003140325400e030000d600d9101861401c25440c1400800c1e004201840c130f01c85019200a0000f01510300c0040c001c0c051021341e1b4041002800c04100d200242038139080200803018190180500ac0c3c4482d2103500c0c111221020085505130001040300c504680c01001589000d50003012002c8440302000d010340d00030412070341c0c111050a44020200300611a0780001401c000e10700d40740d05541e07984200c0c00d00651050001e500058000140c0a41c41407040b5601922503a070142c005030107400c94080903412004403451b544207400042a0b65050b2020361b1021f1101c5611b9505140e500d000840b14030003000740148028040d60100201c1030301c0c41f0301e050b2030f484140c0c122100702c50301c0d0f403001c0e9071050700a0b100c1c0d030041000710840103506000d030281c0d180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 454787508 1250 454786258 454786271
    0x5010b030c0d02090d05031c06061b1419060b1809150912070b0603010b0619050a0315080d020c0108090a080f131815210f02061903060504 61
    0x14852103a000c1e606080a0443e0700150a4000395103c100c0b04580d2503020017201c0e134800200c04c04116214829180f1081542403034404655240100d58002400c104e040e00c1c83c0f9444424bc85409100003d035144242070f00070383c00441c100e00c901030804140c281c0a640f000c54007410050510848490124914031a40e0442050250703644000c1200d2a030480400050f11060701e500c50301604003041c1318202d0000380710000c0e52900700681c4514103480380780110020081c00e15000140061403154004410001d1100409000c50074050740c0a08004481441d0000707031841e8441d540c1e0088207081d00038545c01d92012035400740842d03042101d041085030a01c0e2081d9242003d92050350345800041d4000c02e8080e011455218020750a02601d40813007806074aa0022a640c003024650100301d80b4024081c581010044940741c0094410a012250640144001002700c9101407980d00850b800481d90482099400009079540728080c1602c07404040d2404802d131015803000c0e04035103440c1c1c01507000c1d909051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 454788758 1250 454787508 454787521
    0x207060e060f1209070b0307090f1703070816051b091e0a02090411160b090607021b12010e03130e01051003180b040c05011d0d03031805060f090105010b03 68
    0x4040e02c400c00f59a0300000e540b5181d0a503001c1c1014a01d41201d60030f40400b0042108040e84907038410200c2340464a9114500c1d110402e582c400d996107510407071f4a520800c1303004002011000104000070018a4205101d01107644141c18045000004074420200d9130100400b0f240c24960a0303004541080311815008111036403500b2501c009000042042d4045808001502c480c0c000d00204c600002086540700502c07140395406040c1410161501a044400a4101d032800545140a04100d40040507030082c0b032030303039900400099958113400411a204034ad480003c24019a142060298055525220903000d080745060a075402180300442c3c2600404c80c5071241c600c0d16002d1801817030f01040030002d0b211030440062180d80002d100194880c02c100c1070150740000030040e15003d9031001603494441d05c2d0b61030000030907a10581d000c4c01e80c0d024040001c2c0254480d030900381d402020308600c0030782521800d04050040340c0c80507413003d40c035041004c520000e200d490f000d01411040941141000d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 454790008 1250 454788758 454788787
    0x6010e0708090313300b01031101020313290c010e0d021b0f01030b15030a0506010825110304091b020a1208040203070902030702030d060609080c130b100207060e06 72
    0x28800d10102080114051134290090402c6005c40d0034000f00098070480c45141100c9007802c24031068500480e80440b51843d507202104403025858444aa011080d0424030a4080c00139501d900c10015245150342d01d55001092025004d00340780300c3c00024400210011407410140c0501d581c9045420003010b018025003d60455000d88000741d8000f50101c0d0501c005030003c00c0c103056120761107625500106140e01c1807500551043c1c92103001448541c44010054904a00c240d88080c0f40c1040d41c120320b54072a03a12074030300c5400311061500c51101c141a1602c41e0841e4041e4000c40b03465501d40940c1240f1103403419210311600c07410320040c6a00282910385100d6411010150b508004004010800355030f410001c2c10050300b40c11b00c1c115920b040882c0c010b5500d51040c410880300c0340c1402c80c0010300c540100114411100b014010700f04407100041008800f030581140c46846541d10b428031a4181c4900c82d0744520500b5030b030018100d803800c100c00900210540504c0a01c00e000c10009260100b140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 454791258 1250 454790008 454790047
    0x1020a1706010f120b0a0f08010c030213030b280c0806060403030e22062309041203020d0212010b041d070e0d0201110a1b0803040803180a030506010e07080903 70
    0x10fa1400c200050100b11360a000703042c2c0180c9650b44900c85150100c0c1550303400320034000311034519000708140784107801c05809074003440c2d08030040400084004c2002c035a11401c41c42d446071b00c4040082040d40c80000c80890135092101e0207074900c0e43c070000d042c1c3c3c00d0f4006054a401000444059040c940b640e64000c1101c407030b0152a500070301180d8003101d41c0642d20343c2040c500000d055402e0002030b0b1611fa002c0811405900c6440742070503045000ca030103050802c40c603401182c11081c242020440003c0c29000780d44a8060184603983c01c000d1030030030714018040b060280551182c251f5403245403804d1520860091103901000c801003005200c0c4081d000881c24644103030a84842803100070758001a109600602c2c3c03089600d02641010a081112036519007810414286945824039100c0c480d1690700c1c016401101025401008100308040011603a00c00b281001044400819121340d2003500b4103200f0781c00904140010303018403d009410452040d0720894070b0340103600300640c1254031508010b2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 454792508 1250 454791258 454791287
    0x5010809210c01020c100c030b01020705090c04080106170d08071b060f15180209060403080702040b1c050c150a11032502041104050604180603060e01020a170601 71
    0x1c10300c0c04001110180191805034850780700071074580302c001040c2a11a00e09038a840446071905840903041402807150703030b14078541a1700130310304941004188028104007512120400105200003d1484800d007e1840a81200c0d99019240761401042920b0035000000c8401401201010480034a03440549211180580202405a4061802e04c47d000b0400711460340c0c409828010f00006109094a03c0400c84002e403401000c00d05081070640100d0107074440307556208070200010004204036001401e0703800c1c0028000141c101c0c3c25000140a29a0400401c01401c03100c100101404400c3c00032064018003038400414074402d0b41046c64045c0700c3c018403d810b0180c194101a150b42d820403d68502c0c014040090640449124a03d20703043c401c84422032096041403143c0810b004e0704000e4500701c4002914a030b050908104002240b282d00c030401c10b098590340d21000010817403a000d191000e100000005a03540150f220080c244207110b80c00c114100e2005042c8901640e104c480c0340300380c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 454793758 1250 454792508 454792543
    0x1232a1207080d0507030b010e0102010507020304050111010b0a0e010f050607020607151b020c090a0b030a0210050c01020307110c04050108030d090c1a04081005010305030405090619091505010809 86
    0x1040d80340c9900b90340603c1c440c0380d5a4a1500d03041000c41c03501540170542c9100300341c0f1882c61038011040120700341c800c202c542d02d0040c3c00034402000741d94050300a9144800c8070b40300100318114a9804a013450a1079807103a40104110300040207181c4e802022f00c40a030009482051410459402280c914803419000400100310000c02c0f007804691540451040001c10f0410080300b4903161000750307100000c0340c0c52489a003144d00800c01c100306030b104108000390007402600c0c10b9401ca80030032160807480e01403030041c0101000780441d003241c01c3c03008600c00d0003503407262031040349044500c5241040000b00300707004038601030052085041c004203035140089240004583c154092800b2b820a486903840108401020180d0308041070095004e44181c400210845103100c003c4120501030b90000e200c041d045801c02c020500503400d1204441e0340c0704401900705031420307086510810201c24140d010f00304055441d180f0282001c40d81190b80010306e424608a01c283c00c04010658451812000410300709 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 454795008 1250 454793758 454793767
    0x11103011512090c06110304050a171f0618050f1902040305061e10060c0201080c1b0106091139191b12060b01232a12 52
    0x40c80b034116407644162964050218402d0f070320b070030380105509001c2d84012445003090f000051030004156001c44000800d0704901d5894003c04a41c10449004501014007540e89903c138401100c00c51504401e0501d100051118903240a102e8040d0094480e981d90509080520181100e0001a15040407008103200030004458110f40002d00c6103900080407402103004010840b800401c82142001840c44001c40c0b40d070307801d10f4001e40300000d80205000f0906200c051001b55104100720740d8007203c880c0321180b401d51405208082d6950505d105903142c0e44445043c050301e00940100b03149070085080442c14820036402c2c1841c601c41d0134882c1562580c0c840304410401010500c0566000c07814020b8440c00044820308181545280c031083d101110410700d030900c0900001c03508412283c903812a0b0414000c5030b528a00904140d441c180d04006c00c20100d0810b002050384115684425007403101da4030804481051150a90094124034400c000103468400601c00f0030b099800030f1320300b00d0241e41c0b17 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 454796258 1250 454795008 454795049
    0x80f06040b0d05030d060807080304120305090d0b0a06240c06140414060c04060c0312060317070c0f0f05060a0c080d0e0c030105040309051005070f0602130801110301 73
    0x18000105050303071207142d200562080c018084018035043c0c800304020300042c1d44801c03100d55100d90703c0c85040b01c03d07441040100103c000d10700c966189103219103800c40c030f8685043c0c00039000d07445421003914103981c29070034042c8040701807103000020040035240c0c0345403880e20003042d0010300744850700101b0702050051301d804000c2c0640c48409556080b00903803010b8141800c140d03c0c01c030321545026005201d00004580c0c0e1600c01ca0943d802c5403071035902c3e203071f600c0303c5664202c4d200200030244c2454240c40340000300000b0742c08004d1810120071100312986171051802c02074980c9a0603408040060703000b10741480720f11002441c840035120140c440d507580d000942811981d106006001511907400803400ca104001c07a6004a00c1c210142030450b1081d960f040201401c85509a400070f000c00c840c140100441c0c281900c0d40004110a400d02070300b00718040d1078503000687c4072101100d04507400074000094403603414541d005060040020446440003c00400c503522042c040c000c00200400b92101c01c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 454797508 1250 454796258 454796261
    0x1a0915090721060b09011112030c0708090904030203031e010b0a2601180608011a040b03010908030901020712020d02070b03151e2407110409081b1903080f0604 70
    0x80b0340e02814100202d564641e00654103412400c2c2090014041c1c401c40303800c3c028001402d0740c1004078152807510319281c0c503013042d0065109001c1101e07014814050042b09540d40e11500d8441c60094001c0c40e520b00e0030040580c020740d688034400d890008550014000121544c00341e50158025041c03000d035244111550680280300800c0c02e1941d880c840001080e1009100e05203078076411040802e01181e51100810740c00c3c0d07546810203190884410004610518264000d030360305101c00b43c00010100c4403501c56560b00d62045a030a40c5580d0009400350400c005140500801045032002e402c0121107107100944a4405100b03c00010401202184150340010034840f20500001c0c0780030440200900b031142c100380000c03101ca20804251140160200c140c01c0020326440f01030308003030b140000c0381da220001e000b010551650400d5441c0400700011b501c1400030401e4000d10500100b41010300290305103005121746040380c4504200c400c480019400029460f0030014540704511241d986002150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 454798758 1250 454797508 454797557
    0x303160219080609030c060109050f07030b01110717150112030320040e18031801080405070504050c0c010e030f1206150a1718070302130e011a09150907 67
    0x9443c001c0d40d06202e0008030000080000c1c00b602002d41e48140e0b6a54400c0e003c6030000c8820a01c0b992000b800110400d209a001071603000b41410226100031421001c240340c00059040442080740303c8209546491040250300a03100440100c1d495a605011940810400c820300003010715454552548506040e408a085501c60a030362a640300ca42d42d40e60003054240968100f009907007060a0803242c0b1001000701d420311500050044040f504a500440d40707080010016034031030040c0c03030000c03c85a4036801454026580040000c0e103880709110ba0500315903915003000381907441000b0f0401c0380e0402c24141c7d0f11442000d42c05402a540c0d050204402d20300b00d0074102000080080d4401440350405142c070b0310800e50000d00308403540c4281804a07034110040c2d90440d40c0d03200e40c02c01c000510b00511484200c24980320040340018001003110300317681d41420b12292a070003c0000003020300700303031400690000784000644903c4030007002240000350050012000c010300100c1e4440e199031402c4800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 454800008 1250 454798758 454798769
    0x3080f040305151f06080c0705010b12030702030d0302130902091f0f0311030603060c0f0403050304081b010e180601020c091609060801060f0320130608060303160219 73
    0x15003d00b03010300d070802c1e0030020445900e010301074400c2683c40450038034000107081e40c110392280c2c00360b900d425440d10708076006080222043d40d26040f014031311703441e10f480d91841c22041800443c2c940c0443d104141c100324407848031404061041c0450100f404040103100100ca414640050351003440ea40421100192613804540004640e5115507580358040200801d105050740c08100060300303403106420510003964101c0c0d0651000300858101c50144005100e4101aa9021807400b80d0f02d94070323641150050f602103252500010b4680554032001080f070400008246414907002440034001401019001c503106403003004180000c44a074000c000d604c0741c042c801808c8900707515000700006150b04020001000040d20008009002c40c0101391481c1039503045c0e21050f142d5110b00500f140107204c002840c800304a50030300c003580c03d42e0307819000f000d000311903480000040d402d00d5000345c0a943c025003614040c1d4420445030f4074840c1107101140d40b041d411641024020340a069441c1051740340d8020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 454801258 1250 454800008 454800013
    0x2071a130506011208090918070b040306050f1e0702070f0b19020d051638010609080a1e0804080a0b072d180602070f120201050403080f040305 63
    0x1400125122030041142151044045542503078840007810b80c00002d665000b000f00600784030340d02d9107190021001d80c2c84102d00c00d100c00041aa1040c40345070544650210207002000a410300c1407000030301170700b40c1c40301280002510504009200402e00301d07609000003d504011000300300090304c01d01c00e00c0001c0c04d40c01c0c060b454040c3c540c41c41c4802c0340d012414103423440d8803000130a49200e0000c03810118400c1a5210710f030030000c10003118080d491a010080702e21125940d001d820301207050307840d40441c1c00340000c403a95403605000005140308040e000715003030140c10f010410000400141c0008a030b54030482c500e141d84c80101d402207000c4440d0a00621103100824045403803000051a01c8216000300c2c00300c0040d45420384252488007040c0102c0c42c80300c800000b00901c99080700e103051a0400c80d803900000b01ca14180001c1a4182075810850040e0000c15040244e00070012052010b440070301d030800c514410583c00640903105622000b00a40408120709202011090a460080d50840d06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 454802508 1250 454801258 454801261
    0x60b0301020f210709180204050d0b15010c150f021c0b10030209060a1124090c0301270503070609030f031a030a060509250f0e070c0602071a 62
    0x880d0b110581141121403803590240b8a001480c0c00302c90b902c01c1c0511001e4072001107040c04e14952a01e400c00380c6403100300d56a001c000c00a01c40d290041c81a034098022144460076080085002096500b030800060400451040e2007000c5810008107201c0387e01030034000508821400101c02c064014800041041c0c1c207211513041410030140c0100907442e5080751484030107084040180d0480c0210420583c1041003030144104007401042c4084d44403034030f07100b102c11040841038490242c112006103640031304a402d090091180d410010090b03000c00c110024081c1c0c40c641c03000880002400b2400740c052042c960380d04414420140200d454180d00540b0601c800451428050b008805445403138001906e0021003865407070305009502d0860700c005000c1c03c440d50341c1c1e1f00c6420103030034098420350440c0951780c5c0001111000426003801a0b04203401c0b0300c3c1d054584401800d0341a10b41e4420340300030030808100514664400c0c030304070115520010040c0c0300e225504041c210790400c42040c8030f01104800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 454803758 1250 454802508 454802527
    0x307050102070605060a060207090b131b030c0c02010539010506030c01030c08041101050c150402030f0d08130f060203090307110f0d0204020c2113050103110d09060b030102 76
    0x4000742019070144005000b2611010144007080c0c860b1f1003600016040309005010220651304480300340c0c03000030440000401000703007100c100c5036085160102d00c020007180c806050303014024207280c54103900b07000c000d11009800103003581c4140d110049022000001000c00c084001014980c3d07141400505a00d92a1410006000b0324081d00d00510034840c0304a40038496200713006421040480c0da4800355541c0f1169a0050156940010075051120a02414285120421078a002550f00481c4010705041c1401890f0500c803481c0700e004d04a82090244000584c0c0000d00140c00a0f11440c8015942240f820b00c4269402c03141e8006014030300001c10720000f4000040909289402104041c0b911000340d0100080240341d010010340020f02120b0391400340c94141e015140c410038200503165950542c01d111101ca200c19000308000120200b12100d0518400700e047c40500070a003420484080b19002c0c440d4540105041c00e01c400ba254880a0100245504a08410140540250340780c05818 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 454805008 1250 454803758 454803761
    0x20a050301030615180b04240914010e0601050309010b0307030b0114030105010f140d050703030c0312020f0702040915060e07020d0905060f0903210310091e050601020c0303070501 79
    0xe21058810604005141d0200c00083d65030700c080380c1701902c40455041e03070340046901070700d002890103030300c29516805804400100c03180341090742d00700240103a0242c20000c0c0002201c0e69903045048003000000144031072920910303800e412940c24207000f502da0303660341d444601410791800442d4140c001c2d071100004001416240b203050f55603075440900031900d000241401c81d9824441c807003c0540c035241c20071003019a001848550344000c4c04004c0483c0700c0e500d4542c60910164800c60010315108011030515a001c000300c008020051805d514100d507541c0030480d90300829601034480d0f980d60940b541005000415200c11090100c018094145e40b0301c071400d41d0000480300b59002d80507491003061094070960f8441d054540080c11380e030601d07c80281c8038002d41c1280c200b00d07402d482194800307060101c800f00740f041a094004400d55076890000041c4000c1261540000e400351300b044681d0f02008281c071030700424000042c50008050f0380e0200101c3c90300e03040540d40764240c000010079400b4010306 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 454806258 1250 454805008 454805011
    0x5190614130228031719020a12030510050306090a031107030b0f04050312090703030905060a0807030905160e06040509150f070504050a06050702130b1c050f01020a0503 74
    0x200c54810400d5594010215401c844940000f90302075914a0002640d48641000e2041c2c12021070028818684035510441925000b4443e181100300109404840a41c2081504120240c610141604d04507543d610310689008080c0e000506456000141c0c21800405030078006050060440d06681841e054450310780380c1d0b05e00141c1c005080070003140311104001403c001180ea0008450340d4661700c640c1c1c0c1d0302e0002c0b0042c00440d51404100311090305400f8144015004220007000f44c160b01c1c0c511720b00582128140c0c1d115a02869050040300ca2550700110380035448403490502050720f81d20f40c41c055003020040c513400318106d0a802004030b08001d951407060705c1004152002c1040b40c0320340240030b41d2104002034424441c2c1e900c000113044920003a0010f908440c440c00e0990400c1d480300001640f000c1d403504200005240440c2200651a0039007081005000e501ca080111002140104e03403007400191003001280042400030007081010802c0200003840e2000031511010801302c0101160310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 454807508 1250 454806258 454806281
    0xf0a05160f230a02120a02040204170709152115021201090203060a2d181514040b010525120302360904150e0303090a020d051906 57
    0x25110000c02444040c2022150410300440050448200950070804000700060000000f8011b00340c8640c0103868500140014100c100c030030700780721601c0b100c009142420682c450140c150801040c0414034640c105100c0584803a03c461a05415481d106001c00443e0303444018000324445507051210320344c03917000e01521540e00348e40c6a0344d03982c0d642184003680000d0320210340c8100d00040821041c0d2a8944000c150b06148800080c141c1845400c601044a50f600050f0300009840100b0a4944035114032140040720420f841841410b290840f101c035041da480c2c4900032540c0380403000c2c07103a01400c15230b407c1c82055081e1001201018141503824401c00400701c544010244251090b64064003d841a90030f4500900700261525038006041e8201c1c49890002e08900b88507a12558668052191003079002e0302e10b89034400726000b0003004682920104c10107070b40060060010f24a00401c0e44100e00390116207001030321426080031803c20882403543d0300164140d41c2808100121600545015007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 454808758 1250 454807508 454807523
    0x1005120118062c061c03030906240e07050c03030108010605011b0b0c03040606030609050a0c060216030605091905010b10031a190b22060509060f0a05160f 68
    0x7550b441d1000440302c41c2c0314800e141c098142c07040c01c41d000050349609031304c1040180104030294496103c3d41203480d03080c105500107511403a80205000860203661004488030700e010151900c98032820020041c180911081c0001680220300814400c2041c2c9045442e54810703030f9540d5a543c41118000e0001f803240038085080c02c4800d8900300000c04020415540040048a040c4d903481c002c4c3c0d030107a1009000f11085550343d64040045003d501c81d43e00380500c2440188084d0426007080442e400340c80e80039070304642c4021400410464840070320710440c1e40c050b4000c5071300c2e1526030070181410075410030311020031650100b08090081c150001801800c0945180c40c2c4007480090407001d40d02001100c242d00c200d07406080c0d0440c10075100e1001000e80421600c509240c403410b40408560048039103d5802040040e07044040400c02c241c1d00091407141022454410740070f0104c0d0030350154000d070ba24103c4000c140f2000e4180134500310748080c080d2030f94030f49240030b003891305010300f800422041d143d04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 454810008 1250 454808758 454808771
    0xe0307080a0c05090103030f030506030a06020d05060906040501050a050103090f1b1d0c03070e0117070302040f1212360801051807090e0c060c010e100b010507021005120118 76
    0x1400c013800c5141c1600d4240d07840d00302c0c085e407015050b80640005000307160984a010b50300801b00c0d1407440a0030000503110b801207a541020400c1098940b40504030501c41c45c6408010005c0703949e0756425204581082c00c010a50020030300780400c4030002480c01901c1039032443d5035a040c0c0c400703150a0105944240d198006908031024254000d40c4049486803220403040003c03440c1c6030301a29010070120720502d0080c2c01444030260140e00110203440d20404a40c02103070a001e483c001030b100001510510040d10586551900c03128520310070b15040c441407020702d0a504c0165551004085902100d40c1c04000c60202c0000c407010107200ca80c80303400c4d6294a00b2001c2010424042480d040d2920340c00000c2601500b4001c0d4100107142800010301103104818a4900a8035104080c0120000c0f20300000745090380e100c00c2d07a0a1095801980c15000d182040c01d840d40c0c0e8205054030161a0107844100e03000c0040b60090b07034984140b880203424012081e00000316495074900c000c082442d040c0007030100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 454811258 1250 454810008 454810019
    0x1e041116080a02160e01031e051c0207090506090c130b12060a05090f04021203040801060f060f02030a090e0a09020915030d0c0305120709030807080901091211100e0307080a0c 77
    0x301604d5000c0c50043c20a401c2c0100301040d0882c0c0c000c610035280300c141c20080485a607515240007414500300c0a4084062192104283c05101d0318004004820043c021032a000c4000340381584020f01854010b40c0104036035484000824003400585480e07824039545800603c0d00300390700b11040ba902849082d00d244040b409003800303040c160088800540004c4245c886030308101c100d40e00740801e2082c500c0240700001e8a02d0090160310007c21b02c100e1040c03005410610010316074140c02c02803400b0345d4403c00611a01035481449601195102c00104c0c0c1c09850340350a50340a8902c1140c007075482b0ba0020f061200c0e1034105160010403020031411070307510ba0311001095900c1000d804000c4e000c548107020000010032160714007a4410b0140c5000c0001c0f94503542c17528401d4103c444156101440400c01714115600301150340701800480484402946c1075654022404200041c8a800341d0310540d008c40ca954040c2340030501c0d2400c024180d5a41e06d444d02c1c680e5980b050000c2040e0350b50640e51000003403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 454812508 1250 454811258 454811293
    0xb01090b0d08091e03072c0603030a0e3105100501020d0302160c030b10140609040905100e0309010206011203021e07091401060e1e041116080a02 64
    0xc0c0710782e006800c542040307800300070400740c445904203000c8482c035200c050800c00d960500c00b007405030180da6100400312414010500d0b1881c03150340b005402c0e40c040e406000c02a640001507448501036858031030190400c0001251a4510610010074511600070171040710b55040c0f01083d002441d40002049aa510020010b041ca282441540d0143e0414407051246610a4004080717031400c840e081c0c2044609030351a08001d29440d8030a075041031a100600207030f60070111490000301704801102e490b040c50000010200e00c261545284190354552202040140521a0015421003c4810090340d0070410b20701c2d45a50019a00c1c3c2c0c0180104400469648004000f01c010217405030700030204603540c4610822036200b64190420180f0030000300143d12407490040c2d02d01645012a00c0e240c9500d00880030b0711907196170441901c01d4001078032060f2201d240f402500c610321411100400c07440005040d5048a2040002035070320543c2144a041c2442003900091500030321547c00c4942d0790200015600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 454813758 1250 454812508 454812529
    0x20708180118050604170102070203060c1207020c0f01110c1e010306080a0b0a02070c030b100e010b09100305060a0b1b0c01090308030a0c030222030b0a0c05040e0709030206070b01090b 81
    0x144d0165042c0002c0c802d180380940805a8000e480d4001481c065940c0c0000b49403902c1100ca0241d810000900d940c1810400b104964001c4201d0009060011101d0b00003021020880950740c100481041c0500107440204402c80080e02d018254540700b0310000080d0320b101c00d0114845004c2800d0800000e00101c0000e00d000440d41c1084046e17000f0707216440b0a0021390f00400301640c92000d80e500110220700c0c10107019004100300b00c54061010f251013000151002c050344034102911041c481803416445d18081d5207951081840c000820766101d00c0000c458a01c1a0881210701a0209010301c4904401d1840019410b068045942070520301c0300456050b801c0f4000289000c1050001c0b510902044d0070100380d8451504003d414140c080b4414020100c0d60703038460199030341800c8100b0a209411010580200c04400c05015681d188080074000303201d11b100b2859010510390000d106140f0500080014503802011940ea61081e030400144110313080c09403d44441c504140384001e45030206042c3d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 454815008 1250 454813758 454813769
    0x30f0305100b0717130e250f0e150a0207030c170a0b040303020706021813020f070b0c0c0303040b10060e010806090415061d061e090a020708180118 65
    0x483c60000036580703501301c12044258045000e10305011220408516001d040090013400004480a150911091059080c218080e18114020350b40407142142d0200307200f580c08045061012152142201140306422014104281c04601240d0805a00d5011550304201d034041d03080002c44a1b1a0700f00003d500c2002c1200b00100c2d44410001da0004030205c804640c400d00a0400504042c04c0d5250101641d20100100e00c0b50040403500c8005803030f080042c0441183d0300c400460030000403c4046005100d03102001e4940d08100000494103443c0c4800c603403003074500350203481c0c90341002e29115210000c10746440303c043c084c14802255540c4210000c8558030342c140e541ca01076807110014460f405601520903100d04c3c00080c007a1450080901618008103408a07c6602d11000404000401900982994450403030102840151114004a403011500172906d03440940c0b80c00070f130840244640300c1c0003407840b00c1c0850003a0700c8041c019032100c0999800e803a4105c210309000302204030859640581d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 454816258 1250 454815008 454815029
    0xe0a05030609010e0124150e09011d0f060a1403011e0501050111061311030118050c030c010507050706050a05190206060a05061e03281a0d030f031a0409030f030510 72
    0x7c00460a4560304040d0054250611170442d0078402c01080203141c007600f05410b120540c000442020b0120000784d503124650440b892010708000f00011040800c500c100980500b250000810365a030a500107403010b040d41d0300750081300141003050341c0508004d00c0b43c5800b09000d2000207800d00c201140300b512a49102d8030136080c2010941c0c40f0151007100d20103043c3c0540d40c0320030120180300010500303a101400b4400400b9046120b004141c030f44480b8580c154100001800380700005000001c690099903007a05146880c5d00103900100d956001d06c445520500c05140c05242ca100e4020854501440c0217a505c400050703114420f102d0380348a10116841400000f001c0f162443e44107001031034000402100c0d0003422000c50b505000f4a98000d044011415654140498801e58451181036a4081a1460841a00e070354401601401003001a002030685501e41d4025003030103000c404108040c0208100941c450b581030003012100500c50400120f8600004916400b000024007400ca030032031b108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 454817508 1250 454816258 454816331
    0x141e090f1e0f0109080a022416060f020403020a09090503130e04230604060518011a040605040605060a1b080a02030304050f060919060207060c0c120804020d030e0a05030609010e01 79
    0xc0c01030342450158500600120840400742e55148d5100812070f0701171642050034260b8031030900000710b88241625140c0d080c810070042005803121860141119401c0f4800107102701d8030b081160440c460711101c06100e00c0c40781d80200baa43d100c000514015030188031000425811801c0c241c0d1030f21036600d400302055001d031000a001400b190001c503840800b0310400c0e054003102080031404c0d01d15070050b0140d0648841038001590a203403040400404003110705215a45c40d0a002c42c02c40d1240340301450810500211008102c013030b207915405c1465001014a0360380060b001c009440c1d81054a048440c1c0c010810340b842440400078049010b00880000b0f44603c0400044002e00b810400e89c044a0003a000d01484011542511914500b510346803103020807540189070203500584a40c04480030300100c0402d00001d0303110202c3c00702c082981130170002e514010b9100042c55140c2180e0243d40e06200300c908205582006402a42d036400300d00c0000c0c41a07084031050001c40d99040740001004000c4ea10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 454818758 1250 454817508 454817513
    0xf06010801020418020c0c1509040b030a2415090603120c0b0601030c0c0503040e0106111204050103050406330e0c03060103020703050c1c141e090f1e0f0109080a 71
    0x103004210146e410001c5452030000040031540750071a07040c018103040008035000c4600e050034010b0313000030042200606001c11450740d034000940024154948114101120810a80c1040c0d020401c0f0b18090a44090384580c0e5000c0600680120f00049404224000c0d900c0c00240c00340c00d07070328040342e400942c043c080d5070b40900450040415aa41d4000c00c414000e0308400310b041880200090210300581160540c140761000c1e06c0300007100c24200c3c0c194010b004548041c001d031426507040e1002440d02207500e4031107007040380c05042d0b2420803013514a2040039903480c0d0410307014545132000001d040c14002558a4044052007201150015038a007410800918958400c0d801000c121f84207050150404800c4d20700320740382100c4142020b2486221b1142c12891942103000c941400d903051002c2c500d085554460080040780900b0103882c1000302103490950b640e0b80b822165500000031f0000c1880d8801c0c0c01040580c44400c0051500511500c0d4040d42e143d4402d03100c002c1900c00d20001040d2000e19076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 454820008 1250 454818758 454818761
    0xc03020105090f090103050c0127090510030210020726070506071a04150f2901051909090c1b0b0402060f0f030604060e0112171b0f06010801020418 65
    0xb5011554050141c0e840307228983d842410b1139002e940614003d1031015140000500045000d081c5565511014051070306128030040c40e40c01590707206480410940c48103081c01158010503040254050540e0706c001e050140c1c006080700071501c0001078665a0b40744442c2c0e180001c2c0a1703c24620954200c0ca1003400f86040100043c10031030b21804c51011304001e02b4003101d17403045054034200c68a42c0303185140c06002020340115100c3d2070751842d0400581d103240200d80811300d100c800c02c0014462040e60b200484e0f0040040d41e021040c00808000194400b420091141c8428051900010714119004c0708042c030600309145d807440e80d4644941c0061340350b25128007890004000700d900140400400e03c060740f100026001c49005122030b10b40300d00b04042003000f962040d4111101451610004202501280104035040d50b042300c1c0d240c040b000a03081030811031107200c41060024000d1404100f0b00d200001d0000c1003416440140da50070f0344c845080c282030b4032039486411000115582014003941c0117 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 454821258 1250 454820008 454820017
    0x806030a140c030a080d061e090c0c05010c09080f0d05090d1506030f06050901050f070e040b0a0f0e0c04050f010e0f040c031e050415050714070b040614040c03020105 73
    0x2401120480c0000c1c02c0000c0c0344c4894132208444084002c41e401d0202003d6018610103130a0308503080807120481c4110075401805171003030340141034507040001022402400c40102540e0408000e00401c0703014400a070000320503200d014102c1c072070050307003010407003011600c01c0040c0b51941d01c00b460301004004109080102650031740c1c000c1745101000c104400c5601c150b0b00158403c032080d003040d090f2828564100c1d2801050382e40c980e41090708011240441445286d17102c0c0d0b131418501340840a440110b0000d080302440b03a6003201c0c0c60314020030a80180f018500c11a61204480c1880f03680303203070844225001d02c0c4101d07a0800101820b5010035802843ca80b22201d00281540402081810000b401d4402850750360b400300741e8483c0812076658031903214001e08100d080c424031090605950710901b200c40072500c240e10960714404521058824030300032a05901d00c0003001e860f000e003810043d0031030f030045e107044030054034099840c1c0c0d451096110491007250010807048401c0d10310b40066515500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 454822508 1250 454821258 454821293
    0x305060105040b121603020a09031b05041d0d0504030506070e0607120f02160e0606090315150f0d08030406050c04090606020109020405060604030b013605070f0806030a 74
    0x40601c004944118081e004e020580d0f0382d0700a00d603480c1000011101c1c244c401d07410b0b5404050041000020703242c0c005483c4001c0b01c3d4009242c00c81020850b001c0080c41c0340c01d41000341d0260905000c03000d0701215812060b030b810401e0301980c080c0342c000113080d00d0346c0c4a14840100035401440000340914040c0d00c0306600b810703000c0c3c10546404d060350f483c031044014032140c0b8400b2802c40e82c09450300d540d0410620500c0c0d40c100000902082c00d00c2891031005400800b030900c640380000e00e15111351814002e03c0750f65041c5c03105440d018185040d40128110044002b00c0c0240c3c1030340e0910b040c914200c856546001d402030b00192035030301d4a0f1116800780100900c043c4031002c0402c8001141109440f0f49002020641d0000a103420188100010341e0700240c0400e110708030901c828400308400160090441da09002c40b080000c44401d1100c0041550405940000c4042c5118003020584c3d03400952007003001d6a41c0ca50f540340d220106480403101618503a805a10550741c410000300103a446c240f2014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 454823758 1250 454822508 454822517
    0x90607110c04020c0109050c09010f1a0c070f2301050415020703050d020d08161e03090609030e030d0c1e02030c0901150206090606010c060c180306020306010e06031603050601 77
    0x4441401207000d9078000c4504c018180c2d035451005050103000e00065000190840d481c080a5244c1100d4035108056030140d000c00811041c40518408852000c5407100c904500959540c00d80c6e40c1911103c0040a1007181c0b03064000841080e24507a4108a101c004041611818200341c1442d440d60078582c03000e0281380030761080c043d0110202c0c1c000c005881180c00e4540c014490a00410002002d18030058144d20245502108110643c0e8001d84601030b28030150702c01511940214000310040c014001c0d0160010b0300d00a2100c007071540c80000c140030403005404a41000740b01c0c140032180540700c60030290900c90111201322a042400c00c940c0e4a060000303048441030002ca030300040411000382d1140381d02901c241100380c0303e16014080c4651005110025022510b002d0b00041e00148408000800c10790790740080306400782c041d40e42e000084040c0f82c107103000b6079100d01c0c0200c002e46c03042d10034a000c0340722074400d403400e443d02d0802c4030320940b455224604803240c81c0c00300368003605c80940441d0502 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 454825008 1250 454823758 454823773
    0x60a06121101180e0703150e07050702130e100b01110718020904050a021908040510020a0318030e0114090105070f080c1006060f0c0206031501090510020f0d0809060711 74
    0x1640f4098003805003505504040d400d0030034410141c1241c29071078450369542d0b00b1368010441d0410200765250300c0f03500c40c281255622500d10004442d80d203070000007040390f03103001805d0380c299130001184c8110403e5500c00308912071a5500541e1010140301e003110302d030350000c1d6052041c2c0703801c880100e1458a03003035400b504005a070700003d401c2c0d80007200c1c8040f0007a4003003020a1908511480250f4804090800d131030181400d407a620f4a910391207034404022030300081d03203032803803032095202c905180403100180302410018600100102c0b0300c0418580000d40c079620b11040c14800404035003260805840785490005213903110b00d05c909507220151540142444012000740c8144095420828030721000100075060550140c4001c41c511a08001c1100c942c0b01c002c01078442c0b60449400c020741c1c401c0b084035105241d004a50888081c0c008540024000d031024040340d400082c41ca401c401000c050310b090141881c02210241002c5078449a5030b4440381c041141d11b07024502000141c09090141c8584 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 454826258 1250 454825008 454825037
    0x2030f01020c160f0b121302120c0a081c030e0a062c030901080a0216020a170601090b010f140d05040c0509130b1807030f030908060a06121101 63
    0x8a8000001d00b0815400c102150800d41e40f8141194002e440300d440800825800c140080c8407034040d002080c0a180d1a000201e1400d140b0b0f44208040503500030101d030502e2240380d0302e042d115003a900b8000e00550340d4000108143c1008561242c000d69181020002c1d007072a030000300d010344510551500c2502a20184038040741c03841c001c00740c0d03200300ca0a94031f8580c2d40c1000c2514011545482c80465500148000313041d40c0c2c3d002c5000e03904003820040c0980c071007070f09044240090072422402584804138640008d401174281511101c405201c100380d4020745c0c1e075141e9010949d2524051940040c1d00844460074243c002c00d403580035840640c04040c248004140303203000300c2c0c0e82610261007403c00c0100422103890408002d950040e54510b8000250091340c3e10760710310b10030240c442e0b07004411f400170240d4003103000c0205000a60304030346004180d4516040c05864004c02c2c0c081c1c1040ea016100c0003540d0303420b20340200000c84008080e0340c40e188180c0e40761286100c01c042205410814241d00c0760b4807 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 454827508 1250 454826258 454826261
    0x1e110607060f0c050c120903100e1f15050406080a0605041b0b090901080c011e050c19020102011407050f0a0e10030c0e040b0d0623070306030201140403050c0d02030f01 74
    0x26603c00e407106956048510900e6203006040348043d84002000c101c8240151408a015020507541c2680451031400c05e43e1218123203080d50948402054072185841e0b59800f05400c04800040420a1103840580312028403050300c007a8040d104042d8014210a030028449074012607101d0701620720300b01d200645900c03208420302d2640c4002014000855404218a04507a1090040420400414204081d600081d19034a810030700320b02c0c101b034140d0380d2031a913034020011501080103040944040000f590307071038000c00e07500c2c44060740150310301001105808801c1c54400c1c000d00203a15124141b200401c130101d04e036070042c001a801c0100720707101c0b150b8507200c1030007603c10050325131804602901c03000b00041c440e03580b03109068132075800e08642500b19196205187c00c00d5030020f00100e1405100d245080c8186212401e040e00603044e50100b00304281e1662106080d01d200360b8449400300c00000b42483d03503018902000d8826003055820401910388031002c001068400340a0314900c030700305002c850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 454828758 1250 454827508 454827521
    0x30f0b09070e070c15020307081602030d1e0e210306031f050403020105061525080c030307030c050a0504120f050102030108030d110408030708030a0603020405040804031e110607060f 80
    0x740132844116158080000340926599034183c0c400046056107018000245400c2c80038001c031012140007a8000c80c15072082c0100d50701c0340c200300d0080c0100050b81c003621340490504a54150007620f411408014681c000c0754080c6810034080641c18000c3d01241044515400034000aa1522a0403d44522002c108a90880d0100c9a1200049914041c20302070700f550340003444d6070b119000f881742d0701c00505c42100c2a030f0f18a524184a468840140c00ba485401071030a401c0900301d0f09010942061308100080158490f1900daa0f090100d0650300d041a1401e000c2c0010704c402207030090200303100804209440b80041400340c402c504d90320145031a054220b92083e0010000c3ea007000a01e10f040140b98021400d43c50b40d05507095182034500585191030303004500e00209004000800714030840c0c02034014401071500100100540d02305481e14403510303030003484100d49a282e01c1846100c07405825420240c0d4075005510005c1c1e40c041c200c20810164000c8404031034291791040c0c001c0d11050180f0850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 454830008 1250 454828758 454828771
    0xd060308090102063103140c0c010908010902010905151902100c080c03040b091608070306050a0513020402030c070b090d080c04080d03050604140f040219030f0b09070e 74
    0x403681c0d0302511000a0405800400c1501c0300d070750220f120300480e00422802c040c00c00d807443c0500c01501312442c2c203c0b841000d210444403007036004200c0040c02e040200320441021801d0f220802241e699100c01402d032071030090068003241d1001c604109500301308420700c09460b14021103602c1c003200244110345110346004070000580c0942c51643c0a400386116844210304542040707403461610480e09403461000900c003c1c00c503000301002c244046d404001f0400c03503505a02080103a603032200c80096030380840c0c2c0310541d2882c7c00d00001c80c502c21014801c40c2e00035400c016082c030004038a60280400f82d400540741b64451101000140d0103d041000e07485d000f01102d0000d040760551680c0010480340002e816081541810001001003002c0040c3d0800011401d007400310b0381d83d4036640000d006003410917500001610481c108414002c0e00e40d2000d1055100712060002c05d2101c5819192001803404010041d042e00f00750800031440040342c441d8018480000c039040c1c6c1e0707158009004041c2c41616903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 454831258 1250 454830008 454830023
    0xf0d1e140d05060f0109030b1303020a15020d0501240c050c0d0b040b090610030f021c031106011502070b0702060c0703210804020f09040507230102010f020c1f020d0603 74
    0xa10803145046144181c4d0810b091a008000702d0442e1a4010070400c040e02c3c804000c1c800710200000c040c0203108078031505401c1001c00f200c9605030b012000c042e503c0303000458101407400b8008552021901ca014030220800344951403c400100380c141d45247e0300340400d079070a114454190702d4590350750344400310080c861700c880802c501b0140340180302440d024114208540090042187e218220f1451300110f80e0000702013104070141c1d0010a02030f61035000401c080d50507094001c000e042d00198000810f1205108403001a83e03103440c031507504810350521400503004120308000d070a07200009010541d0000340854a8054824029403802005a00485d40203c0b0800c5085440803800b02126000d2100d003000c86081c5000e50014504003a1000031b20711417500c443c0440c080c001c040111101510800159101586910200345882404289000d00540c00c1c5800003001d030b0312034025200d003001ea560042003425805186003444040070b10a20400d268244981d01340c6050038010000114000c840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 454832508 1250 454831258 454831261
    0x16050310060b07020910080118020f09010f140a0506040e0f0f060306070c03020109060e06160201140f06010c05030d3e0310031a090f0d1e140d05 64
    0x1414141210308164041a62402204000240041d01228005541100c0c031101540d52a94000519043c0d070b004489290304e8407000514a036406140084464000c80e140710b12600020304110728442c017406040ca5034542d866040001c18204010207080280040c610000151203201043d05030b0015400441ca2198580c00d1207200076402403000d0700600d180c80b0034a007614142010958030200506a00c0400110181000038107200398025814140c0c4500148010028100e00d00d81e94401501c030a4083c441641d000e05400b4014490038050600d0101c624245135641404888081001000d07603042c4a82558000001881440100680c040e885000101030024644003850010100801000360240e01e0750040d4450010100041444c00c040140e60b4a640d41d000c41c0e80b05c6d07151607000501001c40072103461108441d6428151150b0340c2407048444c0a001941d5456503002801c1303044001c11100609040c81814180d040e05240320a03041000410142d100244420f41c040d800200306245d0320070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 454833758 1250 454832508 454832519
    0x1211030a270804060c110405150f10020606040e030f03040602040f0909112e0914010206042d12030915061d1e010b28080c0a1116 57
    0x1000c201418407855a40340942603038a100c814401c1e40240001e001d2281c40b01d008004040c08600d0b86032001900c00c0c8030501307000c062a80d10025411085100b004d165142c1e45035418440754041030071800d0ba0060000f501c414040c48010100070700501d1441c0004c02c1003810b0a0500d400840c0541d11602006986038a4945c40d100e1144031030f0420000d0f10f040507604030100711300700904021540d040ba03400311880c880da619444610514040340d2228181000c04940164002c82d003201212100c81d40212060038074801240c580c841110300400c007445245282409010051000e003500d0403031501c0380f080d20307243e88403488200c2605002800081d10340c41520200041c89907070118414035a0001c0c0400d506014820480c1c1c10340540001640b01d8007000118102d80c058600d85c10480e0070048446296100e514040003544001c41580c482c840d0012806000c181e40e8121103511001c0c1e90300c1c10107a844100c480080e5621000c880c4081010404605040b1035050044510942d02d21502041d02407424 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 454835008 1250 454833758 454833791
    0x30f1b0705030d05120601023906073210061503090803070c1109040303020901200c060723070f06030209102604110a08030304030c031211030a 63
    0x1038201c28066040320000c040120f030840306480c400110b014650420390342c0c2c680101e00d00340004c8549c0d40d49012850561103003403409181d40392012580c0c442c018594840742d0a11215102c1c03980010458840489101005e4190b940481404880b00030202c0f645080300f1500c916080034004414609a42d4080402a80480d2164600030788a982000c1c840c80100361101c0490380802400c00e0240003011a40000700407211203200c0c3c124000518000d41401d180c28024001c4d0090001c443c041480100e0030140030451089454009130f080c8000c145c3c1018600c28000e070340e00b14800884115444448155152030b401400c140b00180340c100821007140350001700500c0b070b140c82e03100000b85803041010320b0b041e0f02d034a4841580090781d1b01b42450316030001518034850906400400135501d10150611013040002204038841100880f03a068400d62200c07003103a02e0380700903200100861001030307901c40000c0c0100304050108000c9440000d080c00400e02e80c00710b50740101c5003510119075a5200b5031030360340131 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 454836258 1250 454835008 454835023
    0x720040c020a0506070e0d0b01030506092806020d18051b0f0307150c05060906010513051e09010f140f0106030501030209010e0a0b10030e0d0302090f04020c030f1b 72
    0x500c0100b00d103401d680c0314143c60b000b01414110802620244140294a8440d01280d002c1e51104048020b507035a030614a455044c29542c40d00a0b000e07081c0811441c0e0010b12414100f100c99151b15910801c8a903900c000035480402c40c04103580c0c07540070902182c203180d4210b04030540078038058501111760780c2c0010030900220f01c040e0f1191105c1140b44489807400251103041d11032000009610186d0580140c41340035200304010302d039204580401a8903000800c0160403501c2c181c9912800400c502080400c3d50401c443e00c0c03103881c58005040b02c4001c0364114080d0010a00360002881d400d64070f200b501a94a40d01f40b41c9201e00c140c40610107042c50b008100360040c601450200090b50555000468200b810300c40e0f101a0310200c008129060010f50201800c130a00034004803426428542c0540030b44409000d0032118003c0380c008030b00c998040e008440210f0001041d030070368071482d802044001d41180701d02d0996131000780f00940002d081c3d032000f07002e403018596001d2080e014103e0000d28020303c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 454837508 1250 454836258 454836281
    0x90c09020c07030204110f04061d030615060d150603060302090606040515031e0f06030f010c0f050a230903070f08060c0a020c09010303030501090b04110f0f072004 72
    0x8100440040e800000c0b8106050740d81c121404260002070014003100d500a907200c1205500700082c0010700180c100c18500c0c1d481c0c0410140d050445502e60406498040441720100100907818031007a545c54240014205a1a8114000754210328401030403c821090740140000c207944003070520335440d003400f450740c0c0407030704503135080ca000c1c20540810f05542100c07403441003440010000c1211480c2c03841c14010824440d1804450b1858010450400030006076a1140617004103a5441010541030081500e0040141c4a05002104004003120300781d0103545c602c01008240c101d8026071880102d070740c8010354480750310b00d41c07564070341d20401d410100d0903070000f00c629986100c1002128004105594010296001039458040da95000d80c24050002c028580c060f50307420010080641690055042c2c42d51a0740030082d06090600381720440b9403421190405903028807600c2c0c11601104010010b50106400580c02d08000d5510740c240c2e000719921144c40c403a80000c41c001c090600d442072000803203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 454838758 1250 454837508 454837511
    0x230405040b0a290f0f0d0b060a171e0f10120c03080702150c01050403021b03060a2f0703020c04110904110f0a0c1106040b0d15050a0603090c09 63
    0x9103080d900b14600f0340701586403080c0100300c5000040303c1203d8415603985050a0001c83e550310308803500810345034400e83c03003174030700900d8104e440c070719410400d050381e00c2d101c0c141d140e540388160007410301511082c0c010032034192400301d130002c80c001607040c01c4440d0189000f41c51100c210b0400380c4082c2140d00c441e0300405400b40a400c0341c0004604628a0f0308200c9400001e81c642d50030060010644d450401c007010341c014000001d0801d5524415806540716600941c2034400c000c19400207180600351400c10154581d0100001c1002465280d00002140791001d0840c40a082c00c142c40b000b100c00c840030400e0140da00880d0803070038540c05100d0f40c00004401c031010808210001100030340c43c0642000207002c3ca03566403030804c012030703610115011000071001958032142d02d80d02c002c00d04d850208007280c0b4440345040791b0b0160f007070010599090300c4101005605124981180d000188507014080c025071031a0070b000035664a40e01c3d81c0d140500041d42d00413441c0a0b13141003450082c000c66020101c142e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 454840008 1250 454838758 454838779
    0x309230f15040c0e040609060203010803031015020c0f240403051006120809030a060218040f0203010303020622021512090604020a050f010909140402010206160801030b07230405040b 80
    0x4010b00914820f445410007940d1485d162404d06100904540c071004284c20300c00030002c1812130b4000044d43c86500051000b0180300d40b500c0071a10000340c8001e030100540d100030798136020752404940c1103c0310540030700702c0001c04506150a08801042608403508000c00003810300501034140b0500781c003030040341c3c01030045500c0c0c070594688081880c0406881190040361401590380c00340000080b00d0f8103c68255240e10484003411407102030340e02514401c500e0001d400f52481c62500950741240d402d5000303441d442d9107500c03100302c0103100c41d548143c501c980301d11214010380e12944104000c3c40040500703500d41c882d08082c0d0003407043c0075050b0a25036000400700300060340d4000c11401541d000f03a90401c9511019801030b1080b40d00713074005001541c10560000316400010203410302c114000d0b4205c41842e240e880b0700c0c928414410460b8000503032224018800308400d1050160414868078000701801ea80815602c000c13041e240c3d150958401c0000d00b08003c0c44d150140c41e800b01c100b12a2561740303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 454841258 1250 454840008 454840013
    0xc1101020a09181b0507050a0b0f06010219050c191a0901080f06100f030f1d0712030804021014030405060402121207060f0207080406090503160b0a0309230f1504 71
    0x8600e102d200b130400c11800260b25020045d0500500e514503500061426913070614805041402500305c59180c01481b80810701c4040e41072110034046450341100c0035080e075a10100900ca41440441c103201c825010901d0000303114a03558401043c000c000f0701500341c0300ca02d1680010150070340640b00c0707540542c150003800403036901e0b903526031264100fa040c1001a1140628203601502446800b41e29103403038041c9424507500540d03401d030586844c0109650001e80c403884101c20020114401400041104000900600344261b05401190840c180030481490007030b0703440e0982e40100c8044a10307030844030900c021414246200080b4100010280070800004166080c1d18020050050210742e10f4140c000703505082c03036045403100740c2c204d40003982e034944402c0007401c050b540e40b044600902c038280c8031011403040c510707290050724400b0b10041d241608a0800701c0151445841c10f407164404c01c8405074508550959200d0300102d481c0160815044c0350075035500b00b20b100030001c0080c0c0400e2040000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 454842508 1250 454841258 454841291
    0x408060a06121e020f18011a0309030415021207081305030c010203091c0b0c19030b0a03031d19030c09090308042306180f1204090c1101020a0918 64
    0x5401d5a0410f910690014000200d696045804081e0014410240d01b01000303c01a402410307518841240004540100e0ba082003502c0101e4407000d45400911052154416545030301d14010410710488403002094030f8842e09030362000401319000f140003e0081016006007001400038081180500030344910280043d49034814995128410080d0700c110458104071040200400c5401440703030100351900341301100c0564058040c00000010811111965034486e0141640208004c0e01c194881c42c55030703905681101741144120090700350209003806a03180d420040c901c0f100c864400f00c480d5460b504000700c0912082d0041030102d41448560380100c1c0d0402120380d0803036400b02c0c55007002c140f041241c1040840d040d00a90721402400d007840030030b10b4440801012089048180e80c0f81c44c60700900399075100000d41034015000401d000410903400c851b03000c603400314038909004000d170011300507450880e0b20880707054011540403841401541c560461104d401d410140040010f41d008401810 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 454843758 1250 454842508 454842533
    0xa060f0302070213050a0207020910050f011412150f0402070c03110307090c0305010e0105191703040f030c0801242603030a06050306091219020c060408060a0612 71
    0x24145a00000c4400440d180c035001d0a0f881034012400700001c1c185901c61202a501a0030260b11071901c010100742c41007940c014140c106c43c1c0041c20364800540b040b00644104103581100b054024042c8060000c000180f8503007440794242c6040d80301c9841b0194104501d2148100410b030203a0310500c100000100358117451410750740c212066a00003070800300000e141101541203c01058144100d9a0380b841c0c140e0002e605982d0300c2030301045103a0320755090009440f82c0060054020101c010200000400c21707030035209500d003160079245029221003016804c0c0840342d1007166074010307450040040140a21841d0400741004442680b00c5c1510301e501c410500d05400781e900c0c0b608007070a2640001181404262801240038252622483c3c00354800004014500c21035010b8020800022a90f0703102003050041c4140c0510118144521011400410018882c0303840551060b40100c041715a920005000100607031002802c4c0c03483d01030307044400d5032040e5100c000088491015400001c29402404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 454845008 1250 454843758 454843787
    0xc1306080703061d1b040b01030e0a060903020106050d0309090c050a0c080c19060b0306010503030c03180604050405181218060a12050a09170301031208070c05070b180a06 75
    0xb081148107030605048422980c01c144c5080e00c12025001901200302c500a0f00481d0b00710341c10402411041700560603600c0321f0038a21000d400a414446c005001c540c081802c16000e440001400340d1180c020a403010035412080e030210f0404902013041c4611405a101550400c0c6022400d03d01d00301006001403116490040408401050744101020100f00042c87d000341d1051010000c03c05003041c500801c50b9600b10303406401072070000f051a00340041110545204030006524080851300002c0c8003120220000f9885202044002140d54541c02076501034009a4000c42d801c1c0c460b142901d01e0f00b0b100c0034503002c58090500601c0107200d4648091010b21034107803441903581c10740320382c200d03003045030000d408942500d000c081c0034240e070950f0f01c4590720310310402518010104198203078111f0b001c24840140f082d04020502c421140c45288410781050321401e2000648401c0d96626040c460b01c5c0c2c1001070f106101061106a040d46403400001226040d107481080e0b07030910500404114142d03829 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 454846258 1250 454845008 454845011
    0x12170a030b040609020d0e0a020a18020403050f0105060a060f0519110111041a120c1b03031e07080f0114060c070e07140a1b030509030d020c130608070306 68
    0x14100528000d420031220107a000300204541034581407050029007040509104143c038124480040c5200090911000307500148107501030b40c50001d503813180210340c11107060401c1d002e02c80000080c81c10010305103d070903420000304507481d0080c00c0c0702140702079520038000c11005591290550740c10008450a081500e0300142c023035140c0204c1036a420424001010b541e620f0b0074014580346c400c050203002131300c1111036011400b100c0d00e5030b1001d0ba40541c0299a25400022000c10005130041005052081c40341d0700c680740750300300310081c241150400c549044030203007031544ad140140c0d6003030121507218440e0b00348249242002c0d040000c17000014020710190750112001031a942c2d55000907110dd090b40312046580440e242ca481341c2840c0c2c804e0366041c1c04907048042c8110200c00c00303400d0b107040d440555158a00c00d44503c400100d01034078040d0540070b0001c1040041d03078544050200f0072003921550020848050f2000500c0304880c1d4030450982240e01d8070f002407140c40c4001c504842141d070030460 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 454847508 1250 454846258 454846267
    0xe06090c03040b18030a0207091107110904031b05010f0c0f020a030309020a090f0605030c01020106030b1609090216051c09030f02061306020f0d0534050321011217 72
    0x4400c880c646148420303138103512001c2928008242d0004400702640c13810f84040c45106c01610105545001e0450001d05c0541c000c4640b04460900c580c4190f40140245451303440700880b181c0320a0405106101980d040c2d440d10070022961885004500c4c1e1007000345000c040d0342e08034420003500c034607001200030100743c1c840c1c1d40e210a65955042d8503001e09142042000500071901d5400c00400c020710807640a40206030204030a58012f01c00c45048035005a6611101d1f81e43c0f0580a0071070f4000101308052000b980d4011810500520151000140c0d424542082c5481d0382045e61030042211240820480f03440a05c2000551140107142100e40c80b4220154003100ba100003031a0340034055072004250320f0f01c0b6000410301d03030000d01c0b01030805140c002d40342d0380d400001c011a8244195094000510014400015016904503d000c001c05580040030400486640c40c1401c590154031640740014035141c22144143c0c200e583e0b43d00420790329a0700304190915070707075400c0004811640c94000420209 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 454848758 1250 454847508 454847521
    0x70b070c02100306030b0916030b09100207030908061b0a030e0a0807051c0305040c06212f090d11010219030c031e09180908030f010e06090c03040b 65
    0x103404480c03841d4002d00301c18a0900562008006044900c000d4440c1181c40f00450403500780800c05c6001040960294410142551140c0340c0500c3c02030001549803003061f100c0102044c192018140c418400e43d07035000c4107440c201034103260010150140720003c05003080d0490603038802080b0385d480343d02828007084040a0709002814848192070252240200160038010070202080c4642c1d124814400007807203841c2c580c011000c480048400902c0c030102c0d0107041c00300340d00074802900d0605519029450741c500c0519010280c0700d1080c109801d00a03144650034003d442e0b0203403a030700f900e40724101c5801c00c054a030000720311112450000e0003a4070f1240e00c100c80c42e40700740807510800340b1112403070501400c240b5000384135000d10303501600090081c4560403a502c4e04400c43ca1092081551006121810000c1a40301240c520800c8d114040e907417140e8400062500c00954070a002030b019001c010362600d18030f80c041120007040035104000d18020001814104820340790000c0c2c10049a04150b6200d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 454850008 1250 454848758 454848767
    0x50405090118050702120304020d140d02061503030717090a031e020102010c080402010e1519080a1505130e070b040b030601030c0318021201060b0301080d0e01080705070b07 76
    0x150401608900424008030781960a5810350241800603031040005a5030701304100c0e160b2100c0b540322581100c0810105016103014182114414020b600c03120204c07a890708054540051030749603102681241e010091356407580c41c00c001c0c0b221400c5d03000e1072401000d40d0341e1b05c200f40800c808113031414102090380c26103501c9069200018692001030841140500c1c50800d2011095160403401076003004100f881c801d00c5192098011070b03068503400602800c810070040310b1456400c4520318900305200d4901c1e9184038500a41000c0d400d40c440018500f04100104190741100d0307025540a1048001005143c0b203860a8135641200c5103070004001001401d002d04100352a8456503469a011a02041c0c049040000714000c400988007044004405441541900c00074118900303070800745100c02c0e002d810014440030492401b140001610b640b501010301d1160802e8205108550052684005503904010000d004007c01d0071309002d0303482c11400044c0103100310341c4002e0854484102040d00103014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 454851258 1250 454850008 454850017
    0x13050a15030803010e010b12040b04050c0303130503060115021c020c03060c030106030e010e060c090a05040e06010e090114010b0a03021207031506080f04032712061109031c05 77
    0x390100300c04040d603a4140401c0030b03042030141e0b00d062110708000143c01d0b80010b040f140c211141189040d840d60382d40e04c4400c1c481d040204151402d00a200000721142d60a0009050b9a5104c1c00c42080f5141030805062070810305811502c483d00c007100408241e01d40004401107600c201043c0c0c500c208160400c12414140c42074003031a05481040b0501240d102c08401960681e0000c2da001c000a05005001900f0b0b105040d40202c0d0a41043c004140b098030018001d00710914094055010640d031000460100c5001c0c80401100340c1188005218094140c190142c000a03400024448520342503c0903000318418802e11844000009a140800780240c0584002a00d42c0c03000e00d0445c580b010002c3c000d4642c00041143c1c00050709400b142140c01060342c0c1d401800c2884003101290380d15035041c1c60f407048003410074145451a900c1e03c400204140c011102900b03480c0e01c441c0c0341e00388515121301550907080360041449000d000c0080c06407000540f03001030103030000c5103e0040241c0301c1e0941d100e01c503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 454852508 1250 454851258 454851281
    0x20f0105070c0b03010e0703090c03060b0f09090106050103051f2108031f0503030f0301090f0204150e03010b040b09071d10050c06010b04061e05210405010e03030613050a 75
    0x8240382c002071200c0c1d0500c003441c101c444148800f103403941c4442c011001c4036110315000389030900c03400050000c04e00ba5030005104078000341c40c40c0203441503400060302040044890300b51310b03074442030b0502c0256458054135410a1080030000c0c0b07081d08160500c15003035500d014075001d0304241c10301e0340c0c03030b03802c880744070400c440d41100603030359a410210302d000555402841c0032045004403240024043c10000103c5110132184000281141d00300351145000e045d0039071500c0c00080d000d000100c0d581ea00702c03405c800103031915124015260440001d140c00c3d14581c09d03401d4462480c000d01c41d1500c2d102c4281a03980400c2c3e51038903d6407100c41000248020001c007103031640001d1115241202a6041001007040d000d241e4200d80d203d0b0303a500104d945920441c001c00c0001843d02254003120701030341e020340496240505000d800d00701001d0030001c000500724103d45034040502d0030304c400e01c402803048449040d401d8025504d10f281c00000706032240c0e000c00c4042c0080350399100160001d0995840a030f00404c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 454853758 1250 454852508 454852523
    0x902060706090b0f0c0a080901110a02100501140d030e19060509150306010504051c0f031d030703021018080f1501240309060f050907150302030c07020f010507 70
    0x19250610100805626904507410f11001001c6a13401c901304080a20910b5820072003440e12681103000c541c405005400d140c415900e4480e00007220307003003101400127031003141c0c000c002c140d01c0c40b41e100040e1070303040e0312102c60044001641c101c2611501031321813056400d4185a01c2c01c06003040030500c41e02c00c9103640118005020800320303242e41d00100401d0035100c100d03490001c4444003803e00d40a0300c01540c015001c0b0798100300802c184e0134516aa0650303d44d682100e0243c0520783d841d10042142000c00c2240000ca0cc140961803038881c0b24a0480c20603410741c01449182d007180d01041c141d010200c001c81c00e100800ca0710100c26496007041c4000340081100f59114200303810f803896550300c0b03844c490719a1104600e00106603000c8421109080031103040300b12014070300400041d00100310341601a180552510341d03c011508250240c01c0c00ba0740c2c20b0004060691034110803503110002244a50704040c01001444154aa0742c4103640c0000e404a4055582450710401602d044c420440010700d0b18 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 454855008 1250 454853758 454853767
    0x14040b011e05270315091e03030406060e0709030303020903031b0a05011b080a27030c120318321501170d0f05040911031f05090a0b04090206 62
    0x1580c042c01400c100c151804495050201d403009520740076819104640d0154407400207013080c0091407825a80105451060b20940e4042c03941d071940c08550907009245940c000418041004020b104042c0149881d2a842005050004000780281c0c043c1c80042c042540210707503022941d5042c03046601d01054400003b544022444200d625010300400075a07140d46007189901d0240018603001c1860716a90b82d40255658540c50090000d00d113410810303100b503070356054440b1010150440402e02d03e0090b00c0e01d4418001d9407070000c0c0710341340c2d0204c00e01c20035041102200c42c103034816014500e2140d000641c82030801c0481d0079000085071000c100c905100a07000103d0501802013401a5400b0403400c1e100344a80e2201d0100080d039040c0883c100070740e4080107111918502c10300000c8006991031a04070300e82030382e0b0643c0c0e806842c6503590800312035900105005407049244101000c1468042000a40340d280c0000141d0780c3d0001404004400c0d250020000710350740e039500c100b0311140d0092800381c84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 454856115 1107 454855008 454855067
    0xc04050d060f0f050108150702030414120c03010213080d020705060f0714030a03061d010b120907030b0f19050c090f0102030c15190614040b01 63
    0x2c9030b940341071050000f90705010f86802000705000030400311382003c014031107802024000105550041000300210444222a00400f03402114204218441a480c0a0a00c0f41603100c15a02d54800101c141c00c06080050403410386194104a40e0a4103400c04140da40d00c0c2c04d0300986a0000c010b114400c0c40c040250000c00103030344108182440b000c45024518034541100710300300040381e2282c80a004040d00581c031502810003440d02400c80e035245c81e510b0001480f4500b04010014450340000c0d0400a0401045004691100741c01c030641c0780101040402c0c680541e82000c0314103015003501c807040604d0090a01410300c41905603d000803c05c104170f0500000d07003005055000c14861890390500500c1b0038915000412448035481c40d090200d02e4800c4100c0360b42c2000d0501d041420f0114039040c4c1040300c4283c3d410385000496036070f400700580340112000365201c482140d00750368464 = true := by decide +kernel

theorem cover : BRFrame.Cov 454676258 454856115 := by
  have h0 := BRFrame.cov_init 454676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 454676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 454676258 ≤ n) (h2 : n < 454856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
