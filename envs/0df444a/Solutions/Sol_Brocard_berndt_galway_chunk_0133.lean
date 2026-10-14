-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:02:11.270744+00:00
-- url     : https://prove2.me/submissions/6cf84e07-4ca0-40d8-b435-4309bc462c55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 23741013 ≤ n < 23920869 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 23742263 1250 23741013 23741033
    0x2010e03030a0c0506010602010504020303040302040b03011401170c0f0f010e060d0509010b0406081504030f1709030304050c0603040f02060f0f120108010c031a0d020307050a06030e150103120c 85
    0x6080101507985511101c10020b002d6006007000795184d1103414000107a107401886502d0082d40c014000d54039003411a0203210140c01c0740c0c0c14040e09590780e40d0900740d1850380814050301030000040182166900c4d403c0c030030b02d00a0030b500348030b03c581105440150107a0350007200c10040d4100b03007042081000c4170400503510b4065141403810940c100020401143c60650164076100c10455040040326226283d4559030641c190103110715810300004035000ca0300400014800300d20a14011100380d6040c0024048690f0990300200d89501c04001d000c10440306100d1040c005000382d65090651030161541500345041c080060b010303070780c00a0340c103124036585400c580c02580d4100f8096a40c08000106044c0a0001d200e4028194a071940e020b12440c481d00440c0001e040c150510000c90b20020200904070400b5882241d05200d103500009264942c05141401001191800a0922a0b2060503070501881560070800740160f04014400140040c1803c03402c845a0300d42003980d4045460103c0b403103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 23743513 1250 23742263 23742287
    0x914040f020414070c051603030f080c090402070f020306060402030f0403050d1116173a0516030f09120e0f1903032607050f04050406120204050708220201 68
    0xf0f80402000510f07500185119440d0748140100d40c0c0c0602c028983d010075401e140001400174641801c1000d020344610040c94204032485121440c10041d00e00144c100d920881c03003140c00038130803c40c10013545014000c0c19400b44040e01c06611354605032031000c410010040c00101401408107110079808842e60015600e40e07044039450750f0303d501e0b0170398030070344c800d4008000c40d10b118107108040c4010031a001582c10100001203507600c040381c1c2581c892584040401e42034840c104c6078243c13000551090180e03c1c00794441e410617400d0700350002d00003400d41c0c0c0c2c00d6205419080c00e01c10020009031034081c00030500700861915646442c501d900180c400800e50030100d501426980604544000b04800e00d01103e03c01e84803000070440c1d400e40170400e443d900841010140c0040c000440083c0030320000c1042000058201303180607246c1002904560540d04116240b2511402500442c00d00f4884d203034100c54281131010492828464082040d4099004419400b211515440031a4000c6800d0700324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 23744763 1250 23743513 23743541
    0x403020618090f060907030c0509010c05030712030501060207080c03120306010302070f03030e1006051c0f150204091d12090303070602030103080c01150b0f03040c080307110108010914040f0204 85
    0xa6801c1000d1454910f03001a91250311074590309000c10681c500030300c21f6070b4813a0b00580318241407014420042d1402c48080c0811349060108200442c0018820f240301d08096800d40c40014035541008002403402402d070b00421803c3d401104207a00a41d00081e0b00c03d070510000440a680c1d03580c0e100100c010380112040149210040b100d820109a01a00f01145165254080f15001e56901c0101c0301555401c3c0704181d000441d9140800f8000c034015500d6082c02d020f04480388040030b0f1941d0300c40800b40314a49100c1c162358082400c7c0032110540c000c1d6a80640c200108107100c1803401100b94a41840c866004510503002603903943c9030301d090040e162280d0b0811000c6444c4d40c3e407400e18003c254000b0003c0c10403546000d003588a682c243c506040203840ca0440c0d401c2c14000a100c043c0c40c2d170340c0050010f50f01c550003014006111542017004040305449101091110300098001509810040e0442c110b980c4c00e0100071007884440100352503005401287e0020110b0807800840e00600303d02e842991 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 23746013 1250 23744763 23744779
    0x6020310080a0c150302160b040203011404030c03120e06060907030605060a030605040608010509070b03060303040906060210141501050f0f0301030311120301060507020607030e0a06170a110403020618 88
    0x61080300c0c50364500b04e80c0d5503440381ca00743c03041c2c0c0011804c910405005044c00d5102804c170f040480d010665540d03000f4401703030002500800044d4503501c0c00c1c4e401c480c12000200f210841100709980480341d0819145158410701100000300c00c030783e45426000340040e016070b007540c00241102e403182c0c203d1002044068810382d511300003420000c010f00709078021103010344c1c00c1650003d2900014850180300e240390300080c024440c00c0040c49081640040d0281c0d905102c04d200100f60307061a4400d0000820b0250014007403031071102014410703a1003050040b0920b492240410403051440c841d03000c142c2e4000d2901e50340d1013460b840e0000b11401509145980c1c2100800007204241d0170250719150000800304036080920440e8080500740f009005400c0059001d00003c0014180f08020f040428480c1c10461221104400803429400e4146c0c043c100180192018a46005060400031f07040b07480082c040c494816451411130079846107100080c01000c00088402c481d000d609441c1c0521b420041c88e5030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 23747263 1250 23746013 23746033
    0x1101170901021e040302061606020405031603140d02060601050a050d020c07030c0801060b090111010207020d08182b08040e0106050a080604050f04061503020d0b0106080c0c03070602031008 83
    0x28000d401100c40000503180700e00342c01e06103051480613102101d50003071200389410342143c90700080c0c990100040b03c0340b0303809002c00f0609990502400281040483d86220f0315469410a000c0d4102d080014000c0c03500180c006403c0c056020421f2a03101800f03083c01682e901410750221103034420082c245421a20220705da000084010075004100d034000d640804c400c0d9190000942200c0c402e01c01c08504601c100704d002c03c0c5500a40451200382c41c040300041c14020b5039004500802e80c0c1e91800c40380c0040001c2c5060942c0c0c1c9001d6103d040030029106109444c03107419001d8ad0485003040c0b0700e02d120039140d042e04100075400084a0141c01ca406100381d0300e50f92944081c0c050b40006944001280441000400e6400d0502c24280310b09075104034140e1070340f0745891300e00042000d400c049540002d4001d010000da01d650141400d524403488141c1070b650300d030860081424170051b10340541e400003003005110f10030000066452190700070800503500d17100c400b10801c0042c0594000062070084040300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 23748513 1250 23747263 23747281
    0x10c020d05010c090806070807080601090806040309090f0606080f0405011b0203031605161203020c030f03041202070305100b0a1205060f06010912060b0303070204020f0307090b0306010c110117 85
    0x840c0f0f505003a40326040b8840d203400500d07403101c40840340314000036240743c0014100b0b413041103103980200c0181002001c0b00d4680d40e8460801c1c4080b1020350114031840303000c015409803842260200b074003583c3c0800031742d418400006c0040002404400311540320740081014032030298070020340000b410b1400580303840c0c2c401020392a82c1088074a032642c4002e10307815018032405507003202c40302e40510300c1045030104240c1d03441c8561601c40100c8410940c0c00d00c000700034640204000d0000711460faa902340c6a240c07900e880c1c10001510345140046422440d010070004070700068040801e0003841d0003180482715040454013501d0285c1c05180e01c1501103880ca8280a0301055082c0a04072954081902e030780c40300c0054a012070700744105ca6000c0408038201c1c0c04220b00d90300050000b180181a00e1400c0920f80000c2c069801c2480000214180002030000d0b15400c00e12030401040000d0f500350851800e1000a0030000c007072000a02800c803202c00f0303060b5030b0384550781001c81d0a1010202900134140035001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 23749763 1250 23748513 23748521
    0x123070c06180510050c151008100204080303011a0f12040605070e09060d0c09020301060918180f02060c1e0106050a08120a020f010c0201050a0506060702090103030e010c020d0501 79
    0x25401c041902040211a12020b41c9959010380c1c601900349050241c54500840d034581c8038484407080b5000e081440e001514490207141d0040d000f5603121480c10307040050b454100181c81801c128050303c1000100082c44000c020303a41191543c005000c0303241c45c1e0307940d0351410b8400c24526280140c0d0005c0d1400601316134145441c0124042c120400290f59880c00640d0030aa8560806501c0500b40c0700081c0e2503c0c008034030b41550380c403880644075001d540d0740950013a40c00c20b8000402040900c4002c1c49510300c907884401d9001c01500d4103000180504203040780700d04080c60064203190002604409548407c0100c41000160710201c4813541442100030b0081011000111030f20b50a041d000170762850060701400980b0b10420103003c1c454010b641b4808994800c0d44a441035003e04410040803000078480e8006140d8140c00101e400e1601c0c404c11000c0310001003c80c0d1150200703002420258440d40711890560741c1c141800d207985050700005858080507580300950091f0b581c12500108101900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 23751013 1250 23749763 23749769
    0x13060f09080f100e030903070b0d1d060402042004050f0105040e0a0b030708010605012106080d050c010f020f0703030b01030f0e0c0f1012090807080409020c0606040e0c0123070c 78
    0x3c00300704c6140003c000c01e40303034400d45c0c00c1d060f8107074040f0009126203412003000b4080008107220000c1c1c14901d42c02940c10380d080d080c1011019411540c00c0100350308250141e001d403413030701e807a4080b00003001c214000000c2c020760280303d003e08902004000305900070300441d4081c21902441c805543b40ca20004805070603c012158080d00500b000043d12001c14000d940c01e644050b103d03001380c00407605121400d290000030408229443d10b8000850800600c07400f050a0030a569807581c40c03281c07102c82c50039a40c1018260020070b02c1080303140120219072050321a010791610300030076034010010040b40a44981b1010600152074200c0c26003280750000342c003440319041560360b4070314405044100001d85032140080c0004c513040d0682c05d02c0c4800503500080c101c0703100300001c606000711070b100c200c0f20b50081e412010a0030741c001283d400041080048030303400070007101c4c01e01803908920411602c1745141d039089070500801d2018014582e10300c0a50000700c2141c0c034a40c5840d0415800c00310f00d81c80041c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 23752263 1250 23751013 23751043
    0x1b01140c010507091505180a03081902060f01060801060f09082a0301181401020415030606030e070302152b0203010302090703050103170a0203090a03030e031213060f09080f 76
    0x2000610781c04020000e0b101c0c217007582c441038180340000c100c41d1107120b6a048840d0344091701d500c0120010315400c0241c03804488454141e40d1450030040b01915007580608895415550740c8010004242c6c882c14160640d6043d103001d208040c00d43c0402d50303604146801a1f44540955288000420700e0341e4681850504020030a05801003a04181401c030391300450100b2080e45828080408500941c800141e0b21900c01300041c9426614070a20b1502192141d1003c00aa211081040015410f01a55900720616400780400e80c0c079503070000304000103002110780c0b25200412824102c3e2185440c400c00044411200e014103861207940d100203520902049221f130b1140d00101303030070620910409050340d0340405030b00c01002c65482480780f66000101d10004501c000c202d480c1194940400b01001148251607041031040c00e0f02c20142400c51503d440030810070280031142342140004ea05404948050500840301300303000104407403030070940c1c115030703824894100e001c100104002107101c0050004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 23753513 1250 23752263 23752277
    0x1707050c10050d110f09040c020708100f1a0f09070c020d0501060305010c05160b04022205010f080102130509070203090603010f061209030c061508070e0f07020f1b01140c010507 78
    0x13045480c0c9484c02543c107a03e91046043c480d81703406013856801030b0320301e00d800d004841c16582d45400c56443e069001400c5250107072603540010b061070003400360308040c14581580b0003040c21404041101c0e481404a40fa02c41c4c1030260106100380e028900441c140c50b00900b101c09500500e042c058084c0c45d00388804c44240d0300e0031541c2d5106500c40c90640d4400c103945408000c02458584820107140c00c040c6c0180da100655128140f5840f414040381c48400d00d001102203515032400c0e03012125244294458100b0f81d004211a42d402c1c00c00400c00e00907030b00200d48440ca1601c40c00000ca165000e00008580c210b54000000725465403110320302401c443c0c01d43c3d941d0242e00d40102e10340303040c0d41e0452401004201d9209200c400154140c00041d07140b60120401c440f5a50b50b02e005030f15100c2135510800200403400144400c10145944407544907400d03000410400c0c0c0e1083c0e52564840508a41c03e0780702d89442110280d90303105440c00102d4150a24060740c03139040c000d4150f402060192003d101040c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 23754763 1250 23753513 23753531
    0x30f01090509030301030303050702100509011b030b010e06160203060c03090d050702060301090519020a0302070c0e15010503040609050303010f1715150f06030103061d03071707050c10050d 83
    0x454019188a10b6280001c0c60a591846d40c0580261001502c441e00758010041060f0980d5101d20507140b080b0071040000c1905e00d03040041c2c0c29018002040e510415091000985607030b41c000c00c2d07003151000305440b1199243d2122080b03141160003004029810f0082c40140800c403030041c0302843c007504029090760503581c09000c00742e03041d10454100079081403080c0010000c0b4200340d03100310383c0005180c02c80c9540c00003444420741280d1104189101180c0e010030104144100d9036801006400c0d40140607000781030480103801401e1040918904104001000034100000c5400014030039a01c40100e07612540c40e5800c0002d100300764065448070009210f221a1360202c009008610100c110803034100d140c0b01d5400d110030380c0143d0402c650300900802454030840e15032070010742c02035014100000b0b40c0b008414103810b0140368014045100da20600c900c101013a00002c1e11000034219481c983d0751030304a403030414240b1003194001c40d840020041404012034001004000c0d48003030440c10409198 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 23756013 1250 23754763 23754779
    0x3070504180209070e03120d090b0f01060909020403020d0204020903030412060609050603030a0e0103050c13030602040504050c0a0f05090f060a030c020105061207170319050a0e010f02030304020d11060703020102030f01 96
    0x58002e4071702d585948900c801140f643c500700024004034101c0000072540114649403030010700002d40d070902810a8000041205d103900c410070300040c10100c81e096240500d1900007403490304080700042e1249500080c02c64090f03400300100c5000b40484447d006401c4c006003805c038000c0c4050b10400190600300740000d04240780110855424174042d80307406504407101001140240401080340302c201c0c404000e800d090402d100e01007001507115540243e0b58500b17003000e02098800c0900080a0b8010901014000641100000c034400d1140d2800c40d4480c5120800150f0300754030700c11080e03040100090751001860b0b00d03410800d8a002190000c7c459500d403001485802070041d60503429a03000400103000c41454884003607503220501c812281050b80b0081c4c180c00400d200300d81135003c40c2c40011503007222908004000224202428500e10780c0138204000f079201d03c4020402440b8003155032108081161850a0034981c50700580314640b03441840c0b501034001c1d44203490500761082c140c000015004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 23757263 1250 23756013 23756027
    0x70215130c050a0605030a11040b0c01020d0606021504030e03030d02270111030a080c09040203010f060f05040b030a020a0c1b03060b15070b04050a170702120601061b020307050418020907 82
    0x20515910036155585601c7d0000040005d0507106d50030b46820480002d2256540c4050503c03001c0100c00140d0f40d41c02c04030200115a2035600c20401c0d0741009110100348910460368661003034050600700c4001001000003030951055003c0301c050b00348049461290261050300d5030034a5600d04a20809030750100300107451190b1222000403032540100f01441038144200d005075005100a02c44c14240f024140020b4103076042600306030102d800d06c05c02080400e611203601d2000d12001d0034040c0c50715042118034000ba01c070003880302501e590000340307100c0c1c803602c1100b0504005810110110702108580c52900e1900c5103840b00b0360f40c1900f45145c4040500d09480718804401d149003481c0e1415820f07a85035504640014070644850240444a10100318000a440e1f8907001d0300300c10503a102d0041c0704004102502c0c410114180d801031006100c0f03280c100744103044200c01c1504001c4403401a1001903d04807480e00801d0304142004030103070389010203c0881d03440f01c3c0b086a00f484240d5491300304841e00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 23758513 1250 23757263 23757269
    0x307030507090c09030204233411010504110102070b0c0303010303080402130507030c030e0f0c090a020c03040909140a030203031306110a020a02040c0207120605070215130c050a 78
    0x198000340c03410404000c903030b0f0104107248a6030404080865490300064110740c110080524004643c000150a000003d0b07501075001e04103001400003450300700c2032a5065250003403810500700507402c00c1c00c40d41b801180c238500c01e40d038410000d001510b00751521215101004400e24054070541401044405041302500d4007040940300a5045030f107184c40868400380003510070380c0c004054140358480354200b406603600c2009a0784004c182e6a010b144000e04544a0340030700d0415801c00f00c0e035a0054180031a6045c01c214003180c0e005200d49465450000034450403038040420701c400200010528000e40042408600522a144003000c0300310145403200c4401e000200180c204000007251403030351007100521140241c200040c41d04038020301d0b0016502100c000000740c2d00c01d101110461925000d004c0d40350b05984007401c01c3c1c614025103c00f003500e003564014034a40d150782c002400725100300082440303042c44010401c04c43c10308010120b010782e841481591503842c0108080f82c42c0c18542041d00031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 23759763 1250 23758513 23758523
    0x7060504060507121e0905010e010e030606011101180308010806060d031209050703060f0b04050105060f0a051b0706080103060e0102090d080d29030105090a030206040813080703080304030806030703 87
    0x151008a95903c1c0d01d1018003032245042c040180c8a000c1900e03103805d044c400c00440742d00c464814906010000d04400558410681000a88820807500c0d490103e1010f0f0040c0c0d080c2000c5408400341c980a502400c0d10714102d4141da03c42c1401c0700181940080614101d4140800351292034403443c00f4080000020a0060f002c04d001ca0810002101540e100c0f2842600407410360321010348030303078405055400304172070300c4d0409481d0000c40c070203454144a240d00400044510510341000c00c054030505004070b80607030050000c041907007404441c0385e200b00354810501d0000e50b68107944410005c0c0c01480c0a0106507505840d15040f00030740c42d03051088402c0c6000061000035111041e94030302da01e56009000c3c00049541340e018400e01e800080440708803185c2c05109010111680005060842d02e000b041180158094111100442d07000300c1c0c0d041e006030300440c8056441e91030842441741f03001e1691000c1500c0c0324003980001409640320165016901c80c4d6542100343d1200b03401c06985012500000e00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 23761013 1250 23759763 23759767
    0x40305030718050a030b270d03150302040c0309030818150402060c06070302030108010b01020c090103021203040b0301060c20090f090c0904060f060605120f0406020c01090f0203070605040605 84
    0x282250182c8840444202e4201218a031542c0700c90200d07454113060360045078411400014401d40407600001c01c08000640002440e500d51401c0200707030307628503504001b82070660b600306951038010481803100c003075a005803052100141400c030060050041c800264000f031040c001150300c21002059800003402010014800400c40d00c01c81e000340100a4001c0707910600c02c03c00121340c54010701081d4820300c40c0e03840c01078696140028076801c0d220060540c0781150030440100084d952000c0700340d41507a80540300d03041251464030a444c614401c9402a51400c0800700000071010f80c0848000c107221722500d403807001c910b09181d60006107003100002c198002101000600c240b20350500055100c2004412100101001d40210303401c0302c400e50301036403216140c5401c4648401d00f0f0191800420845c41c0203494888030b20211410204064440402da001840101e014000d058068843c9840a0310003040045020f03d060341c8404540d2404038001e000d40e0100050382c50107541590110340c201d0b202c1d00c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 23762263 1250 23761013 23761021
    0xc130501050a1b0605070207091e02071a0406021e0408031204020f150d05090609030a0f020a020907050715050903070236070e04060513050405100e0304090f020304030503 75
    0x556660041e540311020003c0300702c54655044582c1c021408030302c0c001e1200285504100000034140400358200300c410701d06100303c480701c0705040e1144421180d0784400060f03d0b03503039901d012114103050500c48240c05042d202400103001c5203038000e0003000a0440240c550441500403609580910322036440c49400174040f03c00b10a0b0560391a41e44184000d002e0a0f8504140340050b241690007c0c18540d0f51001050390340d84001c0e544a52604051600b004000c1c500c0d11522031580d0b0310402201d101006141523488c0700541c002c1108804540c1c1c014500c501c02d142c81c00c0014090b800412054902c1c01000381250aa40c40c2803003010b00031006c0344099880c040709602400140000150041741c1d403200d00c0245c0101e10000c1d50300c40c0140e62080200000c0303007042d15000385895041d0130068412403038200d003084140d80f1910700d500e4242c1d441c000400c2d144d40b03d00701903040c1804001172502480c01d00c110040030540100003001522120102004141c00825103002240811580107000c200204082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 23763513 1250 23762263 23762267
    0xb090c180103081308010f020403020102010b030a02100c080d050f07020c10091202120708010504021822080d06030305130b040308040905060a030515010e070509130f02090d12080c130501 82
    0x800080c0c0142100740c5036645d0300c00040d8211060007201d000080e0340402d05100b10341c1d0a014800124008500070700c60340c803031900004ca04800d0071940070207004a001c076040c1000780000540c1c01d190b5099604206030b1030036a2200f24220342c102c5010f030042c000c80c01903042c03c0c60003d0205e0300c00030041e92070122842c106406005109030608080e40e10520b01240c2d03807189541040414080c100c6000042460f00f0280b040c0304280c1032822100402048050401007580c0c2001401a0910b12210600b1000c403441d0816040758032400a0f0044820308041020040c03541000003080082d1001e070440d03200566901c422041801140401045d048040004010a95160704540c0d04603000419920300b0170f660343d9030185800c108019882038400c8250040110040ca920081ea026110b030070710a10340303449000010150301850240398080c070364440c00c403103a05a50b03505032840c102c005400a4100d44035410120180c42c008444640000c50032400100540c885c0c2c402e43d0220654240b00b5038000e8105401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23764763 1250 23763513 23763517
    0x41502030c0405040510030308090a0506040602030403030204030237180207050c0907030e010f020c030d0e0715020106030611040807060305040201120501030f0201020706080705040e0916030b090c18010308 90
    0x2000705010500003c1101d50310b038854540214413201036100318500e03625000c2e00d03455004003502c440d034008940c0500401c03004140c203940164840300050740c84c3d86a16068009000b0703900042c0d04000c0d22042610740b80010303c1c0c1420203400d81903003017611852800f0802418083c1d409041068002205030055800c0c242e009031820f02d10500545540048003c046140a07800301c0b44580065250304441410718030a1080803091280d0441c150300c0c20011701000c1d0303541c5c07182401c4418003580d142c80c485009030742440400050460811004400500044024064001da00082d03400358a0003070504c0043e102c0d2000c55003140e00030781c0a4032550389003030b80503001010018801d9050198003604003a130760146104241c0030b075109028030310790340300e01c0e0000901d0130f841a0402d009001101c1c06120785150441d09680403a5000d1014503ca075660600c0b10742010241208140d40050aa2011041110030014584241c02c07000c1280d02071044101001a1030540101d03221500c8466401440400d444e000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 23766013 1250 23764763 23764771
    0x50102150405010609020a0f090501020d0503060130020703080604050106020604141504030309110108040b060d02150309010204051912030e0d021e030c1e0603041a0406061401020604150203 83
    0x20000850b40da40d6450f85050780d0100c0041f00003d011042c4003080c41d074001450798043c1c4030070b2006040c074903240301001c0c10910018200303d0510403001212010319a001c0101d8088a0b000011810250303001c4002001a40000c0c004402090584000460074101442020304a80196008203429119501ca01009600c02542d00945000380081d00401d014100d0311140141d10030307980054600a142049103004d00035034a801d04000c0f080d010b21000c526465070898010008403070043d443c0003d480002c501d041d41c6104810001004810401c0111066000d01704407002500c0801c48410850400301d164080e03401021700703500c6141c220f1000b2178490f507551400e604018102441951407600082c8100340640c08480c0107242000c0420130b14101070110701e8009005507582d00c0480540c3c5941050750743c0200d02c1c1805444040001030500903040849520b41c000303640e114a1500301810900041c20a9001c4c6080c07040310109028000d500c000b03079261089030484003707074400d1980d103140c0700a540058 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 23767263 1250 23766013 23766023
    0x606030714012006190510050402090f030a06020304050601080a120f030e06040b04030201060f1406030702010b120303041719030e031b1506010f09060807050d06080c030f070501021504 81
    0x200c140011028603210039410311800d400101a10701e005c0141c440054071201c103040902d03090000b0320207810304070003907001a108100c81c0940c443c10590f020035444045070340203d40c940b080d813a40c0428043c4a40c011405030740100c068480d175070381307810103181c4d02d00741c02c040141400c0761307600e00d40512071007100d64041040721440c000c07544024681056140900a03170b015200840081c051104250702445044004c04403031080450491420820f40c42040040316654040c050000c00074403614400e40c400314400c4030080514402c8082001d07920360700e4008803007c0354500380440c05c0c50703680401c92040c1d0780d0031140c07000e100d039490b034046030201c014290882d214401d5110501100b000551b850f0002c244080d0b60400800080c90600081c040748000036042c18180001501d43c1c4500651101030b840c19512103050040d056154000115040d00c24000588006441e080000c91041c002065052401d41c040742164004100d24182c641c50301203d1143d240581d120580d0f0315000c0702010030701c0f54414010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 23768513 1250 23767263 23767277
    0x30f06020403060507030e010b09060f061c020c03040303090e01050f0402070204090203030c031809070f051b0d09060e09010f05150c0d0806150309060c0702040e010c0f030e060603071401 82
    0x680e0b43e240030ba03001551940080713600c85142c01000c8000f4422604468000ca82020346824050040703004003110344111030250a0000c3c6158111a03120542d00a0700207602c002c42d178a00d41041c0440e10b0790003a0000304e00151070400001444558492418140d881c0201500007a089180c1080000d620101e4200c1e0030a440b240818050381d02032026040128905001c4c44c0c3e81c0d0744629400c5525448411443e100300350070028084581c0e804500ca009232500da01308030340c0d2960324501442a0b00144d101001041c400c1040c84019107611488490891798591540c03a04800c2c22820400020824000d0140000d040722003045245411031620958840c4106034502c2c1161041c01ca60810407440c0d807030b0300070820010a001160400440d0803030f00040700d50800b4110b04001004546a12010b400c01c0e141c03605c0840e4800c15980da6a00c011079044100000b0080040140b80c013516952341400050046850300840d00c1d0220008242148143c00080150158605001f10064901803010304d00d8100203003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 23769763 1250 23768513 23768519
    0x105070e0d030c12030203150603010e0c1303080a050d05061e01030f060306020f07020a060c05101e020c0606030d03090807120c02030a0303050603060c07051b01022805120310030f060204 82
    0x303413003254034441c4903503800350b600d161200b4102d80072281800d2141c040d910800041101000d8150003580004035202d01a03554042001c48403055000d0750400f07000c41c0c000113038041509401900070074401c0d110003c140021742e41d400410070001142c00e1103c8484080000500507584240e0004030011103003100041d61549944500080b6040102010302405c1c0c00500c050562500d040c1c041c0082c04185010b824040b030603621542c9820316000380c0003019807104038185407103081c0d4842080786e03020706070210340314100c01c902c15a42d128240c803940d00a0240340b04040b122442406a80341d600c0d080301e4550725001184c0c1d074019524040d80044000c01c070034000701d03000680d41400385007003603030003544c000c103040c1000010503080080c0505181b50f540c00820076600000d002091003880c0502840d1201c1c203a07040c0400503800c2242404228024140021000400c005a80120194580200c0c210340000d2110390792003810b44010355003080100d01e501010000204207203808030041c0d110340c2000d400c040d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 23771013 1250 23769763 23769773
    0x904060e0f070305030705070801020f041202060702221b14030a11041d06060403020a12060b09010603140105191a09030102070c1806050105090f030102040f0f05030f0105070e0d030c 80
    0x300e80c3c208903025080050070f5014820100700e200c01602041c002145000512440480b8601c80c0e0700c03130030030f040f000c4068074400d40d034684007034400203070b00580941c2c045008610681507040c01009c074910302c4c0b841d0403603d83d030b400d88680d2007164100d080c0d15036000c90308290b00000d0b003d40009016201e43d544401c2c1c03200180110b440600010140e007501c0b615408054281d1002c1100000c0120f070050a007840300f003000d03036150700d100070840b40d994210141007402d13400c1002c054441068001e0700540b00c0e80001803225850b83c090404c082180c125500d07581d132520208040e138110380001404611005100b48440100d00c0d00e403104d001c6161488624050700d40c0c001c6826600800000e898000080000300301da13440803103407148021068501041854184000a8800c0c0074408560b80202c000e0b012003034460b20300354100c0303000d004840c0f0800e5005598004c0b00d420800c4500415009010f00b011b40c800d0300005000340343c000c05040c1c645c142c2c81802d58060080360540e8110503030412500c0000000861 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 23772263 1250 23771013 23771023
    0x19090807050307030908011a040b041d0708010f0219030c09120b070801120302060a0b0f040e010b0f060a080615040312180b04180b0a080d0302030702010b0d020904060e0f 75
    0x1d1103140510f4441a103420701404007045030740700300b1407641090503100301c0e84a070f0440246800380403140041c2c0d08038180007150040415020311000e090709e21f01000c940520020ba44411030b64a500240103d6081c60400416809000b50700340000507246010340c0428000c1c0c1051800b4800f070315051030419940d07681c00004a111400649448907014144041150701034101c0d809803113600da54481d800c1c0d259030001e50701c81c40203240010b550307035512580301180d03510050802207500003007052159040380030390180200385407600c0c00d205030442c0391400c0c500d00304001a58440c071500d403200c1009655407014031010941c0800c081c600352004000200010324000c07040544462165141080383c03441c610585641e03210784e0040b01101d10148010001c09440321345800404e501d1281c0401c0301030284010070105003c42c1c11119503402003aa00c0c4400540c9940514410b4116900a0021407040d401744003203c0803001c00650004420000075000c10115040680c0b0304000c0001c5400040d0360100590400d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 23773513 1250 23772263 23772277
    0x5070f03050306090c07050a2301060803030f0703050108060f0c071406070f02071a0d090b040308040b0604060501120e0f070f030203061503030306010f030204050406060816021203190908 82
    0x420300101c280401130511020941c5c0c041c01d0800168904805e50300d88554a003c4400f0041140300034000b1201c010030801070450460a80000074040280c944803042d8032500100c2e00c040305052a0000580d15504c00d01035141204c0d044009400b0304c3d29001043d0b03010b04001000031203410703410080000020848030340c8000ba2144040549820306201c1401064001101d22240c00c540c400d500a022a817000c2c5032040b0002313011b160160b6185402a0b25401030183e07040d014100c021000c041005042c1c201600342e203c0c41c40752040e00349982c0c55030b0401044400e54080d01d070000749034000c00026140144d2142c603407040b5007402c0b0b0f0117803166919900d15024094102410035401c80390200110704040091035000442d5107402061821b1400100f580c0340001007150341004a02002c0080c080c1c002d90455020300300140c804d101403921508090102031042c2e8000491010380039415054503c041891f0f803489040d41308692564503042c03000a00060640045600c456483c182d00e000607003044020300807 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 23774763 1250 23773513 23773517
    0x40e0406020406030c080c1b0c040906020406081602030a030b010c020904060b01030c0206060907081008030301060c1104020306030a03271509060807080610030b030f0703020a0506070f06090305070f03 88
    0x24680c1041e00c0203050702c11261400090003140c4007404400e0404d0b1f41030b40e5405001940081890001d080c0175442c4c000c422050302d40062420001000380706090300200251101d03901c44070240d07220800304031003500d001090100103810a00c00206080d100f9001b0b03001c00601498200d081c0300141d00020314010040d0340807150603503904494003280d40c145c0501c00002480e80003401480c50300c1c82c081900d00e40001e0200041040000014142050070520315000d40322070f0701103a45a685485025103901807203641a200d4039608107a203081843d19008a920880b4042c0144ca0424440d54041d280c142060200c40c00c1644001d0000d0f0700c41c20f0089540c2d00601c01079a00c107a242c115981c01400d0700506400240410a0460400c0001034105051030740204064500700b0b041c80c10303000224000c28025012950500600108041072000001d10205490080354030081165a035802c110040c03164081c01030001c0c0c07802402d140807850300d40c451000d0502030b0411501d001c009568001c1408504801240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 23776013 1250 23774763 23774767
    0x605070b13051e10020705070b030601021603050a0c050607110d0606051513050f0102060c0d0216080703090603021e070c05030105101e1214070506160501050604020315090c040e040602 81
    0x3d0100410030802c0c074802c03050441103281c0102d50711125100d01d070700d014200c10064004045842079100b0040f100e104801120b4010b28582c072440c2c8542c540d41c03e50015039042c25850004915031902e5400c85c1c02d1179a00017200148208604240041301c08110001c3c0ca00079500c030000201521500010800c80c00326407040b5540d118090400b1880c94080e0300103c3c0903c4480c84045501d0740c0001e2415001143c0402c29500c401c10000210084c1c07146250282c072102050003420100914103000c1c200c0c092298540319500750301c03500f04a04038041c00e2a4041d6840c1c121210f07003203802c01d842c01000400d0181075080c270016103a50119082d03410a43d21100924034811b000c0080c14a6901064411020150710702e0580e442d103410f01300400c00c4014050115401110010400384d010061000100b001410342a2100100010355411404251054601d5424000012403c0c50540700300c2e07104401c5c035003402c2c15400e0060700340301d41500000c006000043d0104408548564080700f035521907482800096 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 23777263 1250 23776013 23776063
    0x1020a0b0a0c1d01050f0d02070606060906022b0c03090e01080601031b030804090203060609040e0606030c0a03020607030503070504090509030a0e0904150e03040314160f0605070b1305 81
    0x1094a42c002842c103c0c2c01000300e0b000141607901c1012103810404030f0307000399110559030260078001d1080c9040140120310b00300c400183c090300082e44000b115040d801707607810b006400607900c404201aa0388030301515040c01c002c00c0302d9401001d1100b0300d075001c0c0c90079803200c94695a105c2c030072140a80007d00640c1c8010010010020045902c0c0c4440c900040720042c007600c0e55451071340364010b50003044a125000b00018600c0d0f151581a500810001803050000c0c0004c0007189407921000e4910394000d000d030444d10810f50401c1c011060490b40d019010600d030031240c0c1c908480039040a811034003001010000080c6204240c0100e0303014002000185607a91140c03200541940c408a03003480c010708a890410002c01c603d4440385103401c510000101d0f2150700d0703541c0303030303040d441507800c01420510a8140c1c082108070001d0700722028001c44980400e1992a110540c000200511400c2c00180e0f00b00625000101c080c40080e4200d0301d085184920702c40c0e540d132980e00b04080036264484c0c0062000c201c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 23778513 1250 23777263 23777267
    0xf0b030303090a11010906120b010e0310090b09010902130506010302090d0302070602060f01150c0602040506070609050105130f290109050a0621031d0a08070801050105060316030b01020a0b0a0c 85
    0x1843d034440c806d08240c2d03103407494160701910000c1c9406c4030402c1d0682d240b0007425164000c20340c0001c20b0000906480320607100036021401083d02070025560705c1c01c0d290000c0d503100300c140f15a40010f60010501d404030049030002c1000b8103001005541019003d0041c0641510341310041d001c05407080d000f03001c101d41011002850306c80000c280550000b8007100400075038030040341056600b801c42c5801100c010480c18028080e2289038046030300300d1000134010041c070a076540000b000e01e210307100a0000c0e0b202e81c2c5e16800d4000140c034018203040706102c1d005002650341004403402015071300030340c1a101f02801b50301d07054560903402000c62546440030080d15000c24490500541030b144140d049507440c001d00251881404c40e1b0060a10020040507000d40c214034071401c1035480020001c012054842407610f4407000f0301d1060ad15950300f030400114540c0380110030b8034860001c07402c2d03404003801a218210040c0020718810350550161860542c04104490300b00c40c4162820364001c0390b0f6052400300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 23779763 1250 23778513 23778533
    0x3030c071203050402010905061308030d0b120703020a0b03040f05010603030c0302011506080c0a0e0301020403030903030215070e1e03060403020c030d050f0703180902070b04020a0e0f010302040f0b030303090a 92
    0x1501e010107260000b000010f0703800c59802001d40d28140e0b9090f884c4d4680e0700351103403d603015800c04002c82c032011800f110012015008400707100340a99000481c034640e00f17880c503075031182800300030f50040b00088180080403005010356071040c0103c0210390000c440b903e80c5401c540c2d481c0c00540000d404051200c06041d024002c1209403c6481d00440102d8030f858801000d00d00c0103401000e420300005003601100d0301c28000215102c1c00100215600d40d40e0b85405040103525102c210054052552403584070410868082e20515003504d0388030806400d00100402d03d55080d0781180099031700980d181c40c80c1c03801c011280c0310364825002800d0f1307160844100b5142c0035002a041c01000401c000c0400b107021100300f9071307200c280d040c180426040384005584c60802001d400101d51144042803030020300102400300d0f40128020f561814285850300c4c5000300240c402c440b4101c0c10b040c030030010001400d29510000c40030720707950340000f0728a040c0390000c0d045520546a640ba26800340001c2c0c2c090203841c00d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 23781013 1250 23779763 23779793
    0x510050a05060703081504020d060e0a050f07051e0d0c030b1507030e0d030c02030a0506240102030a080406060f090510090b0a170a15020a0f09050f06090604030503030c07 75
    0xe450b07030408906960040c03515200511045003040e0401d1021001d40359031301560219065048203002c0d00d074480880c0505900c08981901030300f0304000c0420074151554161600804007070b607900f440d1070720500b19001c0034251075405001101041041d640e030120b03548200030041003c0d940200d01e40410504001084400d01c49002d405002000b07032a00081d04840003c5901005499540d5070030120309060b10000c030800002780d014081c200040c03042200100b0114412032020081c800c02c202c00d180c100c9070ba003000c2100c40b80940d0040055040d4240030326507443c0d00030b208100100c2c0e4281c5035601812162490b40c002c800c039944980500c440c20a80e0004480980450300703041100c00540341c0040c600700c0040c8624401644a0864411030500a2221808039500300c001d80c910b03030301843c60038002548400840c03070020b0400c070601107030302c3d12a0802004884004180090b800300e40010481294880326209601260030000000014000e0010f1440b0b0140010015151a154240039441c40c5a6007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 23782263 1250 23781013 23781019
    0x1030203060d030c06091218080105010b1b010b060c1e0307020603010510050904020a0509100807021e0106030c03050c01020d0c0b040809040905071707050102010911040504020604090510050a05 85
    0x4000c01c54161650350a20b8900c0d90180307020100e825150070a00300802101c800508010203260200700d25680140c24903901d81400002d810740aa528403d0078200c900a0107411020b4404020034645044295410000c4030112800040c0c00485c1c480081c0c5641e000f028a00e082e5048403100d00d010340e05280c030070203c498006002e149800c46950024405120500401d40f084030b60707200d0030854038401c1083d1403108030701510855507205110720281c0345806c94030509108445807950702070400c0c0302c0c4103d680900d00503001420100225071024090b04003a1042c000d40d50342c0d4090002c0807400c48100c400c0118064000780c104200810300090810200301d20401c18041403003102c03070005600c8003440303034843d401440441c4c8a403010000140a8110001c01811612540002050175101c3c0000c2584501d00c02c0c040ba9501a03640c401607081e0b9042200142036003140300b42260150034560442c50740030344020038151400d6194600081101c50a44120824041910061209082c42590000944411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 23783513 1250 23782263 23782267
    0x51003060e040f030c0503040b03061f1205090a020a1701151a0a120509010b010f0e010206160c08040303020705131e090c05030a08090f0d02011403190f020306010905010302 76
    0x200000c20207800242c00242000103641c690414544110001005c1d03030340c00320580341e0740c81c0d841100c204070303400079101280708001207200c03a20807503040c0c030b10b14070780b20b04a440d0300d021641015044401020020002c0700c039401040310303080042c0d40714650080541602004103030500f0b07440181d17508603000040c0306e03c440c580e020414480b50148405040c0c1038070030184165034481c42c400045400704c2c805880401c0081c1801c0c28031003800c4064000d15100002071366400070040c45003c0c121108803050301c0280c09604240c0200d20310b0011006201d00b44c000b503041069900d4080e66602010b07a1080d0702c01e60040c0c0251070140f0603480e1010769800f0a0381041c00500c01c00d41c004000d4103059900c40c80141e6000d90b80c422791020018820b02840007071400405482030f10039641404038141d0b02101c1400c0c03040301213000c821a58a851949003c4054040e507a89540c14558607448001d903001404a104041d401858421024a2401a0350b004107106001603203d0400c00b00140114000b500514181401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 23784763 1250 23783513 23783519
    0x1061e09060f03060e01020d0513020102060601021605040b0d0f0804030506100e0703150503010204090222080703140a06090606030b06010306080d0302092e080907030206040b0c0f01060f05100306 86
    0x1901d8402c9058a030001c20008591020088260086c4200d0006403003070b07820907080000d106440b400c070028035030003a0285caa132503541d07030012616924403443c800700c0c9a980002c1031280d82403e030302c844413202010341440c1c81e51160740c4440306801c1c00c18030120340641c00000d041c010480d050100c0c0360044102d01c0081e40950412460422840d001030a0a081641d60520390046a1300b0b22005001480701900031551291a21500d10180d07006865181072614100e03560a03441e01e144503c40704a0f40f10501400d0740768150750b250b010a1901c154a8801486401142800300b1600c3c8035207000da0b8440c440005401d41303503140a0342c407034400a201038181850440104060400480c076414091014900140e85090820004074402c48000a9460745c0c07001d8441141540115200d0000d20b040a0b143d0712040d50301c020071155100264000250005028030003004411010006415122100c40554031030b480300c2032119013110b19a500594400171140170070809410036600b004411000c030b140030b11005003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 23786013 1250 23784763 23784779
    0x130f0b0f0306041401151106090a020d02010507060e060106110303040210230f0d110f04061209080d09030e04140415060308031006020d03020c0a0201110304050301061e0906 76
    0x3404203551800000100040c16603450742c0c4002454400340e01e01000c00d5031503031240b8544504a0b4000404591400e8044a4603000040c485100b40e2240340180b040801c55402d0240d903a0b113046089050040c00c0c010400003030075501030208001c110500030420307517140c80d0b002031000e0600c0e240c025403504100140b002589414081805d980000d0824684803400d44070401c0003a185030a04045840020403241600000315005001401c109402842101103500310200340d0f110395084442e045808101c100841c0c0c0c0903158004108400c1c1000189440380c1c0d803210452580134800d00035035180d07200840300030150818880500c07048203039420803040d003404506e20000103010b04003134080682c41751218502e110359005400915480b007041a1079040c11204250031010501650340940a41044a200305100703209640318903001000400a200f40390300150303a01c500c0e880c000c00c0c03103010030040070a05032002d01410008140c0200741031005101e0b199121713080565604080b14060501d0b0040140d50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 23787263 1250 23786013 23786017
    0x702040b180f090f010f02030411092505131e06080c07031202090a0e160f050901110a0602030108030a030b030d020721020a030f020103150e011701020903010203010308130f0b 77
    0x451030311011125444022486250800c1d130420300d8480d40c00c090051400d20103603005180524407c01d10401c001004004202102c10304568013288242d0b1003548101542c801c010800e075036041414050300e003903803403003112107401c0b9603800481452641c1e094003201540c8011a0b0b2000345010315010410342003560b80b08550307106051300036003008000c0d10032003c825000d9040702e00021005014804544c0d64020b903810402040300c0d595010300e90b80d5440038189018900000541030075950301843c012000005480300d82d000c43c080d110381e12036890b0a0b00003580603c02076002e006100020360700c960401d80024150f0320100101d50003a0040145541d505400013114400c0e181c41000d0901c54207000c0c0d5030701c90101d40e07061000e9405038826500100f8002c8504070340003003a0007070382c06002404280c000e183c85001d1500c294110b003481704004002046c7c00c0c040c025818002d4000240c542540c44c0c00103070aa070030030380094420a00024600504101e04a564001491000e89a42049140110743c180f24 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 23788513 1250 23787263 23787271
    0x613080904020d0f05040b010303020f03130501030e03130303020105011707081519020304030305040b060913080a030f0204080706030e07080303040b060604031202011b021902040e03090d06020702040b18 89
    0x19540103d000500003030181c00c40008040010410021460b00c3c1c145440c8400003031200350f02601480b0a030300380002e00803084441c0070080a40030442c86103400c1c0114014000104650200e010501200f841c503001410444000c50180d170010034107504120242101e840440000fa080c0d51000004000c45400031030100b1102070307026480007441d50f819a0000b02060301c0307000c1da42038510020402c01010b405902c414013560140c03003901120b82c0d9400034009210000d13141c9c11603c078005000704001034078450040042c4080e034500400c2c0c400d5041c0c842001d0342c20a410041d01134000072028070107181e05101341441c01d00d0000061040c02e2404001c5a102c1c80302030805003102e40c2d4031000410a854802c102c80003184d10040240c60f001c66404028028407020340c01e424250f020042d100c1d142031000451002032604982c6000c1039580c80c0e030800000f485103208401c2c45000034031621580c3c0d0707a101c1c8030504140c0102d10143c0e032888148101f008030f0300a43c03503483c07041000c0304e0284a02c904010100e07030302c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 23789763 1250 23788513 23788519
    0x30b0a05090a050718030803041b03050606040c030b0627030102040e13030e060a0c06061728060e0619050f011503060b030c04030b010806010501020d2016060206130809 74
    0xaa89400c1d00c202c4810302c8170813400066400e081d00001c2000300702001144105d000303ca983d0300e4400c10380803400300e07452140310140c510384c022804030761030f0300e499031055001c20380360700b800100d8001d10800714505401c2000c3d00c41e403289043c195101d004400c0e4104030302140c401c400851030b090401c400820155000350106124094035580301d8201401003010004000f8000c04040d240d82c8001c2c0b00610840000c036044942c1401c1040c006520109a03032400700e07810b40280030300100f0520350b1002d402c0508607049804101f07298a154030209280c2d200304580c00000f4000f6202138502800508031408003a544040c805140c00c0c01c100c80704403c0300c03005054824207204031032940c00581044018000350740000741300318800014820608101e0380108101c0340300d08110324084e03030303520003540e16034400748126400f5810613500900201e1003503a401800c0c080000007242c500741d02c1580546400406003504241420b251070034082950100329090380700f0140055030720501c40c199594400d81c0204039903140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 23791013 1250 23789763 23789771
    0x6021e0303131506032103090206030118110706090201020f06070c030e030307060519061706010b130801141819020907110f010902010f0c03050f090d050a050a0201030b0a05090a 78
    0x200302c0c0459801c44402c3d41a4000c0c4859500d904107815010364a440c3d00200244e51000502014028041e10040c0d5030020030079030440e86020301c071078034841c42001803004e419507030104e210f10030801601901c0c2c4035000300c800288810715071002a2030481604410a00c5502880130400d40329481500ea2101941c50725201c00d111342440046407039802505801007600d8109410050084801f00d004044172605174424400300d0340e40c841c04181c2c42101d92420030244c1005006008900031030004220742030400740c00f40101d668a8603041c1c00c40700c0318850500c41076000c40034804100010380740c0190495915014140b1034428610341003440c124040028021030a190004840a004070308820800c00004141c0f0021880f03d40307480e0080c440d145080340440c013800300c2000329520030500c0303a0105a040d03c03424545150051781440300e030801100c05502044034992070001840501c00700411500c81c00040c8801c1c000392001405449445000c54060000f404082102c1ea036040406500301c409030b00005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 23792263 1250 23791013 23791051
    0x40b03010909060b060a02060402031c02060a0b011407080a03050f060607020409060204210b010b0405030a110607020a0b0c06010506090d030e030c180118020f0d020a090e090706021e0303 82
    0x8004e00220341c00241d0004000c1390360200c0039008200c152040f4400c0f82560349091a00845022881d4800e41c0c110042e0701140020b06210300316402042d854105042c0f41590800094144542b6480040119803580c8040ba04143c91600f5004441d000f070822070f105007861501d44041070845c001d40318007900c156191000c4400344403041e4101d401800000f01c1c0030240ba60034400180034900c7d61a030484128111800000b4290300b4201600d00b0385800030040c208481d815140c8210185443d81c6899004404002d8040142e96101c03110001304030b0541080e0f2580c62010103d410000164049070180104004002213a5510b0b504010a150300d801d004010741c41032004240b60015010380380741c00c0681401c0c86203840c01c0d0054114100c428805216003144542c3c1354030b00980c00383d03100b20000450140088503a412040c0c010b880d4141d0185050031280d640c41c0d05a503031154080d164144644c02019050080d2903060000c15130391a008106000401018040b580c0e0381d210040000c0701c070411b65800c030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 23793513 1250 23792263 23792273
    0xc02090406090b070e011103030103051e1015080c01030501030203030f0d0207060603060506130c021e0c0405010603020d0c0305010b070b07020307060207110907020a0b04080c010209220b06040b03010909 89
    0x8180705401009803c0140741c00e40c1302400a04003501190f003c1000b40480c00a85035000048905aa50110107024000c05d6000703217a001c07001c201c406030441d0240c00541400800f072441015040c109205080030502d14040009050100b41c05003241014107010050000d40c03070020849554a00e100b01441e0b03200d94003a01d0340c00078000c0c0c0c075008150034108800001402003640005000c0d9204440c1c2d5000c0940c44858442201c0c2551031400141c0c20aa8500c82c0d1700410011001604803108141c500c50203412000404582c2e090b003010001c03039030204042029200c90301c607030141042c80342003c1040754142450500640030f007010044c845038101c00000c10040c8240141c134401c0c1d610040035500c038241e030710380b2020314030003094440d01071034402000950700c602c0001c503c801d203600036601103540d031140e8451014552041004015540d000c000c42000307920b41c8502c40d00280c40f011882a85a900550754909440350000010300c038220512091000c51501c3d0103d0341110412040010303034252510b45 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 23794763 1250 23793513 23793521
    0x1080f121b0a0503031b0c0d0c02131b030606091a090a0e01060c0b0604062103020c0d0615050103020702100302031b07150c081005090402180405100509010c0c02090406 74
    0xca000703140222072403003040110010240d0b00401c0001c086c0240601d1456409038607003d001031070718980e480321400c5080c440c040e4205100507400589050344128030a20b1542c01d480d8181e1200001f868030400001141c1d80c0741c800d1340040c0072103140442d03185241c2980c51406505034034442d0280e43d0005445040d039925441d81000510b00d20354101070660f034502000e0038014002c1403d40c0c68140501c00200d1500d130074860402139998028110031011441034402d103d50000d040c1c201c0c194495002d00b0050340d51180c511480c2c40740b25403808211004858642c03085000c10794416418580148140c0e80180e480281504442070240b0b40140c0341c0c1d407581d003c160024000580d95030480c030005540000d0100c01e0610f1000c2001d048000d20401c000004112000a021944030848170209a030034026490003148094206000522301007c28051b1865050422020b032411074640d8000082940d4000300b0b4001c03260301c420b061000f040340304400300300608504c00c5520b0013881500b0600c002001c1000942c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 23796013 1250 23794763 23794807
    0xb09030109140a03030b010918021b030313150e0606060a0e060a030c0305060904020a09090201030b040f020a02070e0103030c0308060d060c0201021305040501050f0f01050c0a0c0302010801080f12 86
    0x2e85100c80315036485400d61510306103001500002d0800e4200c0702154064a000340481d16a56072441d03140c0c2d8940d100000035044410b143e03040100200a61088031810070256004102d0100c604d0b80340b0501e032400610341801c1314507614a032410002040d0082d2004515030358020005c0e10307000c0da1003407040340c200c901d014500300480d40041d01054203841994142d204a02158417038804000e907407a1a802c00803ea001110000d40c0959683c6091156440740e80060490b42c2c4181008038900e101c1000241c15110904800740d10140d0125410304c0c110303810801d0100901491140c0011941503860007070038480fa10f4005024001e050010500e03070344502086445543c1c000300c2c1005181c054410080c040e61100e0042d07040c59107000c41c089405e1420f44116030403184002c100d407030041240d40500c0980d45821102e41e05014052040120080d418440628140d2040384001041400c41c4000350075800103802040003940704c50340c0c0e05500100050003003641801d4501e81600c40320b42c10810703444001800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 23797263 1250 23796013 23796023
    0x60910091a090906090c06090a120b15010c050d080709030f031809020406050702040b01030204031506030b1b180a0f060503091c090608040305160803180105010503070b09030109 78
    0x14901540340028000100501801103030b10100e6030300c510b540c0e0b560700e50040e00c000d40c20780c102411495491800c0d03c020030b0700f24070183c02c8500d12980c031803102000070140d800603a600740300282001a50400280c000101c81000d0800303020b00501502c50950390000502032805004c034520200700810b010325460310095622008003080ca2840f072030001d02600e1400c5040c4500c50240e640404c2c500d56034001c1e00d06942ea10f6592608103e915001c10011304a1906c100d410b0640c08c05c800301c04030302204180800407a081c400414401d29500d440d9400c004001c00703a1054600d542c5c2a1001101202d045900b0651028210b5920000c1e0000094080c040d50f800200c00306c030040070000d501c80d00400614410109541503a80e042680e00b84080749070303d41694100002c411000500c000c5001c1d50099030030500a251450808003001809108041040016250404088200085400f42030750740c0701c0041c2803c0080c001945400d010035078804003400b40e1320642002080d1159513132425405030184075000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 23798513 1250 23797263 23797271
    0x7110703140d08060102011e0518010905030703020d0c030e0607050c060307020c120a0308010303051e180f01030e0d20160513020a090e04140607080106030f0603080306091009 77
    0x102000c81d038840342c1001c2a40030075100400a466580103102e506100e03a403c8a1100c0a04092803805000b0300c0300918004400c07400034662a02d06409101c1d9410162180c402142c0e10140b0341800391800c403172410940c04001101096000003541710344200700f00c000998800f5202c0c505803501b50b082c20034102182c1d804c0309005c000c000c0d405500007503000c1407050070307980d4403100c190680e002500c0d00841400a4081500744004000281c0f00700300601c0250f204200361a654481d83c0080b01c03655004480f40144080c1c008034041c1740d45041d1401015120342400e041201c030407040c00c0903072580002151481030040e00d030024102130001c1c041070002401a44141d40c22500800e01c00824100300b805180d006603800c041140f071212807813003218400c0d072840d10b604148526022100e040d000c8024402c9818407901640c20300900010490940108a55260449258100b1b50000c045444000c8004d241c182000301c204041102d01c0210f0342c100b201074031078210950f0390150702c0d4501c0c00c4a91004981c503241c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 23799763 1250 23798513 23798543
    0x503031801050d09150f18020603072d030e0606031e03070807060501061b030507060b0a0905040b010501030f06050609040b0604080607030c02011404390801020309150403050307110703 81
    0x1417850b05050079a66104009880c126a1058100c40c0c440780c400c628140d00c060101c000d0729111000c4c56001d041403034608c8000104072001d4207000d449040f00c0d110b810082c100a140c0613090700030840c1c0c24092000a00705440c0c9540005c0d0b4580c5044090010008080d10104960005008981c00260041c403129900c0040e4509400145424802c460024160545a80e01c0b00004400b0210540c0c25030354450806015844080042c09a014035035480900ca020004000c5124062180310300c0c0503903001c003040d6140c540007405807042015a40480d5280c400103110a641d80e40549408000540c0e0000350074a08002007895880b50350003030342c0b0302d11500003000b0050b58035401c2002d116005500a1254403540d0000c0e0000c24000c0d50002e10301c10704c0c0142048080e04100e00c8900c40f101c4500c023a984e81000014184010080782c2001490b6500041080342c065000c02100c0c0d1103551081440f4443d1406031001043c0c0d000c06401030003000380014218001140070441000134641101c0e0804030495 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 23801013 1250 23799763 23799773
    0x22404080c0a1d0c03070903020d080d110301060c08090a0302030a050d1b0809010c050a0b10060206010b0307020309010804060204031a010504140105090a020a031d0601030c09060503031801050d09 86
    0x6080000c09218101e403240225040102c0c0070003e503c940d224004039001e07161300008821315080244000c041020101c00000541c0e1002d03003955016000300c0d0aa6a160048900c034816901c1c45032004042407000c00040010315803042151100540000f502600c58203120000307101d909042d403010394035105088400303091100104052230320318465180c0d121113440040c102044507103031200280c0380c607806101118165001c0c00704040e00f02e00ca074040d030300d145100342d9030203144420079134421490410070740062000ea0340401c55280505030640b039003030641ca840000250703284200c075005810806600045020000c854040d28055680b00d1180458480d00354240340003072600348142481141420300c0140c10400245810f41a0fa03c090640906546c540603040040d610024070801010744d180c10301c01150310010a4010300c90a0384c0302070803040d450350400140706c48943c0c120214091511804000680d400000c40c0d000f41c121a000044108008006a9480c0501c0300030850035410306e002e5404110f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 23802263 1250 23801013 23801023
    0x902030a03080f09070605090d110406030b060109050303030f130503070f050102191803060b210303010501030c050c0606100309050d0f1803080706111e07020301050a051302240408 79
    0x240e8101c252210b103503604c030034060b544c803803c1c4501c00c0894001c2001c00d1180c1013050000030070b20b002c1c4070070704c03031f95030b400c1e80860116141a0b0054840c0000c10040c014250307801a50307070005120440040d400c6007800c80600d240c12802401341e48560403809441c1041000901c1942d444903001108203c0300b41003401d00a02175804100030b02d00401440202c2c20b10140070752400500148105030f510000341c21940c03110300800f08900c8055000b910880405044403465022506080000e0091910ba5150031300140a886d1052401c7c814000709000c12210030704009a00b65208000701c070f40701107071079410905900511202801030070a000b4007142d05100c0342c1220480c2440310250717842e0341815898100100d06403440f03020042406000b08174003030118a0603001070f441c0954602500746003100141242582c43c80401402003020307004103c0e00294074007840340d640e204000c1c803809c0c401c91030310800b0f08071035a0040700001d00c12481071850003461140405002101c5216190b59542c039030310742d0314944e964 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 23803513 1250 23802263 23802271
    0x90109020a03091205120f04050a060b01050c01020d0f0b061204060908070803070f09050603010819020f030604051609050c030c03041104060f030b0a0615050703021510210b06040f0902030a0308 85
    0x3d104101c0811f00980300802c42d41d1055420202a1000351210341e07480c030107001020815410020280400001c2c4e980030300c0289071400d194000000c101c00c3d500040c0b01603a81d003048481c400d80d814001206100d43d2141c51ba9071065100ba00080e512241e441d000d462400780d2040a4005003000c800c100c1c1e403540156600803400c91a881e80ca50041d592400c0141510090103030005e03581140c0324110031172856901850700c507840200340c2d944241c1500e000c6854404110380c16506940004001400404800c85540c007500c000001440245000488407040d41702c090f01c030520f14100000024107220543d02d05440c41a402082400740981e1554860b24849442c001611100410800b2800c641c04034424102103c2c080034196800d10165041504c141d04100825010b50080703662403842002c40500d2284101c240c503a5404100c0c3c1414001c00d80c0304145409205860100701d030840c081082100c2031548200c0498000c503290851101100151200356002901840b0700c030186010180c025142d40d201d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 23804763 1250 23803513 23803537
    0xb03011701050f0705041412100c080901060f0e040204090c090218030703020a05060901140406020703030e010509150c070e040b07030b010c1e1a040f020405010b09090109020a03091205 81
    0x1640c854201c0f48030940c40682c0e624001c14400c0108100014950060040600f4010800685003800c01d816a003000580c2034a28401c966407020030900300d0b0801c142d0741e000000c2800802c0300604003050300e0302c0489240228130107440c0c450b00080c2151b846401000c940b0360310405015800d5640c0c001100a0b4014800740500e4009000d0880343d40e0800280000c1101e4000b040e0740d807514580018030113a030740411940d60401c40c12059031612031003c0c400130720040c085039004026051844c1070060141ca014840076041040402c5440c4e010b580e4030b4000c60b6500000c00f020b030354a045082181e0300e4590f45038007424021003100c08110074003d02e01c5800c0d101301a1520248030f801e25170300044594030a40d40c0010102000c0344150b01040706032400d0030032624442e0020021280328941c801c40c0d514012075045540484039010041181801d0241600414110341c50a050540100003d241150305029100d01154040781d200c14091003500100310554028001290f03481c1701c0d0780c005040758020f80603112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 23806013 1250 23804763 23804771
    0x503280507090512070905090a020303040303020a0312020f0d110c0106061706030303040507060302030903090d110315130f0611040b0301030b06030d050304030e03070b040602151305070e0a060b03011701 89
    0x50a04026914054013011000585034140c20880f5000003040007030540c45013849500c0e14030005860420042010307500940080841e111140f0b401040525401044044a401848000100c0c040321069030701142600710f01040d00d402c1b0102074001e030300038083d51028940c00c05100003000d0790001071290907185d2801c0407070190b5840030241941ca1000f40c40003070030380d80002c200f000214440c0e4082d6801104000c182c0b46800114000607194010460082d90700d503202d1490f090380e91408200d00e610702d05160500e401145041c12480c0000100444003410102100c00da0400304090f5a0100b03450811b001540c81d110364441c0da84001c81d0b0024001100c030f084880012a140b4940000d140e80704804999034140703141c0d2281e030210741080ca4881c6003501440f840c50041780541c22000944040c1c04158000c02d458401c10300b140f0084c000280c400c4400e14a60200140419004140c060a540b0051100400e46d1224858040140750940c060100c1060110000c20001c44581e0304075500305601000348 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 23807263 1250 23806013 23806019
    0x6060801050a0b0406050f0403050303160215040308180106090213051002010207020f01030209060c010c1e090e010b070309170c011103090109180204090504060504060c1b03050328050709 82
    0x2c0c0202c10340c000c1d0385003020309200030403126108000030f01540c0d000745030083c1055600d41da56460754100369400e2004107101c4c840040308030340c104644440151844c10400c02400d007901c024148040280c090901c00840315001c103d01c5009401130802811400411565401c074106043c2581080f409258414a10701d900d0000c510700c14000d4512240d0010a21000079100400541c0251f20221803590440410701241180c1c0d0401e224540e1044000c0c5c40ea042d0078031000a0340c025040f4141000b605026004a080c00b80010344950681598410000701780e44a5450505a0b043e250907401003082c921104c0b1090450440816103418007030382a2103052f41403a0301050035844c4d0143d100ca5034000764000800300644400c9150000611030640c1c001490951034940c03600c15a0001c60f829105251180240820004c0740d00c503107001c070441c9191202100940411f6035001c003540c2c84000c0c0030440040003050001c000c484405000070f030760b00c1d8264151008903000c000070f007a00b1600c4030041001d1600c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 23808513 1250 23807263 23807269
    0x607170106080c03070905060a031a1509040f06050306150a0b04080309012a0809090c03071202070320060a0b0324040602070204021c0b01050a1707021006090606080105 74
    0x503060300c0c1c141c2c072006041e0703582900020725500002e20712810480c2c080800034603500d5500080140703440503500800e10010700e040c003407aa5105003105900980d05a4041d400c00d080c0401900c2d04000304840104041181107004006080241c2055074035002d81d0080c49419100700440a0101d2415524034032a90b580d0607122409019600c0303040d1003a0820083c01100d5881801c3c9541e1820004244614140640d5083c1e04110f0700a6400c56440400003003609262a040d0400d0b940718240790125851403410540041c5006101140401847c0d00418100c007007601640210100d40071007a0041c01d01c40000c0300090742c5100030786107510700b01d18042c0301c50802d0070040354048074000e290f003244941c10038030181d0002c013450007082a40c0a0754203114840050b6154002003000610aa80c0300084644042c501e508450400a80c030341801780070065400c9040e002131450640301035a80001c0a43d0750784007000c1c3e0800c0300f08402800072919000022403500c80a80c4010280d0f0740540e2100380c0740ea2030b0414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 23809763 1250 23808513 23808557
    0x50103030905090601180909170405100809030c0303070e12010504020f1905061305031501030f060c021507020102030106020d0507081b03070609050c1e0f040c050c0703050607 77
    0x80a40020990712090080e420401d003255000503042c500700c0300c034030240c548010303401c13025400803200309880d04210b605104080c25410000d4007040350583c0b4152a150000c0c003405c0700c13440c1e201d0500c007143c8000f60681c0820f100b40d409640b104026a40d036850041c10043c01c0707040310034030148201e4010703201500c0d600d0705204040c8074560240003034401404003030400c000c45080c1d00321250000c2c08010b000c115501d420b005030840c980203000120030281403004040c20314403404a412041005d4800403c0828442e811600f40c031900b0000000b1a0000002c00b24201402581c00840060100c401d00002550540c0110704854480d802c0e140c01c81070300001142c9a1241c040054107030502400141b009414a0700c0d01020040000c08503032071b021300750381c40000f51010504161415001402e040445042c40030b01ea402001ca2030314040c26000042000070040c2012204950085a541000030000c0340504111a24103540d03200302c0701810390380e25115070356038402c071031610004800f071461654401d0403010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 23811013 1250 23809763 23809769
    0x30c0b130f06020d180503042603090f011412010306060b0406081518091b01030608030a0c030201020409090f02101701060e0d0b07080612030a02070501030209180711010f0501 77
    0x2801d00301c28540c0c1d281d500c0603401a0486003003040d52070342440a420100203244881c0c0344554091611145031071084419008000003140215121442070a1000d1000c022030300c280808807045403140d10307680c00499181403d19010014007500090b0303146040703400785490741200d1244005100b5580c40c0d5039640c1c0d10340a1807045801140c809001b16044403c1c40c6102404060081c1403921185507600b0400c0b00c03202c0c107882d280882e41008425803000109002c01c140f003481d00307003000e0060070300d0308284658a00c81c68032200d00300240c150034002011700c00e404030707070050454801c00d110f054580c0c20000a56150380c0812881500c130340081178446400b8032540341004542481190b40d503840d040703007901e01080400e801c2c0d600440e05181c0354005118034040c1400ba440039500d56082d4600b04040c028190b664681c1511503520910030300560b958001071141c180c070310a213005030b151066500840c4501b907894000c00c0c0010170490400181580c410f4148040d1001c090003402004803403158031089130003c0c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 23812263 1250 23811013 23811023
    0x110309010e030405030a0602030c0c030a0c0c050103060b0403030f09080102030a0b03010b150912010e0d050306010201050708040b010b1b0706030506180f01120f05070f060e0312030f04080f07030c0b13 88
    0x3606d039001086082d030140d94015a0a00c80c1450250000075480c01c6500c41070b0034402048000b02244240b04900d50307840e018100c2130034200407043c1803c850036201d02840c80001c04005107114410803651042080000a1084500a6460303041141115020f0148542600c1c040c3d0f2a0501d411028901500e0400054400001c0c19140c030041509010300078118a000700255903c40802d11301c03c820400c24032050301c0059a030151681007900c002402e55102902c42d000b000340303c40038040890110504141117a024010301543e07096102e038214a002c030318400c030707440c01c1c0910003000a1035601a00010311450049420340c01140c140215240c01000569119265404000040c01500c41c0c3c07662019105020715801b0f03454803c10356520f031800070342d50440d43c1101d0380b01d01c0c10841c442d00403159851521080b401b81513801440c0030503016a020050042101c0c09001c0040303428080790108565804144000300340c0e03134140c0b42c2405001280d803040c1c12289581007400061070000c1811210800b19800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 23813513 1250 23812263 23812273
    0xc0305060604211502030a06091b050a030e030310080c030601080a06050a0209040207050708010e0a08120c07151a0d1a0712060f140d02030a080319110309010e03040503 74
    0x490400061103e1043c0d8102001240d0f00e040d80c08949241d903050001035080c031000d0707601d183c8011400180c50555001c00c1005080c80c0305c060082c0d1080c14070f41080c01d901d203826074648480e100c0480250043c81c0f252207403400008140103414880e9a0040182c0f82c10401300d41c40040020245983ca180902c1801d690b504650f000038000b0300366401c0700d5080441c0310303405402c2c181d403200040c08992180340c0c11240c5a0103200f0030000310501b0b02506003001407031009041c080407552941c010a10450042e46d000290880018074080544815900302507000784000f00c0500d03c000c85840100408000d9281c01f01c08c644220307003035291400d07901c550907600041100140c514028402070f042d02c0604000306203d858144144844103622506000b442544020102645401070740d20300d0741d40403101c2034040c80544039240096100000c02004030b030341c01203480c2e0740c3cee523201185014108040c00402e0146c0d41042c10f040012845a0061405031142c40000c000440300c40c92070307070b0780d81c8100e101c0c00382c0603040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 23814763 1250 23813513 23813519
    0x82104050d0c03200a06050a06050609040e070801090c0f050f01121e0e0102071e0804030209090f030304060501031a04050c010e04060503030a030c09080102030705070f03050702030a150c0305060604 87
    0x4070301d02d040703510340c8a42400804004142014159144510380c03104042d03100d01240e03014401580507064100e600000104549420640862618818001c82d1801035131070342c0b50065142d8007000244020040f100c000c20003110545840703040c8404034031a05400300340d110350104007485c0220482856183c1611410500040388031207a02410680384200200c0030414803800c075a00b018002c48052601000c00141c0c0c0c1d070100e1420344894810720070100c42d2242c0340c103d01e0b00020780759130458003580c0c0c048034a44056959080041d103802d601c0c00880c043e0380004020301c8100031150308014166840384200e8202c40d0744148006000d00804c0381c02410700c2d408004517444650086030b15600e0310748080c0c800301c1c0320b503240d4000c20300d50342c0000804400659a03d00d405a82c55015040303101030a846002075246040c2080b00405900441c4400b40c82c241c0c1d4149a0400c06005a044a041540c083c00b5140750174450705000700d0720000700091404c407900708882c5105041c400e229807445040000c040c9030820741 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 23816013 1250 23814763 23814767
    0x5060306040f06090b160906050702060906091c2d02010c02090603030705070305060108280201050307171005010f0314010e090f06010905070e09011404090c0f03082104050d 76
    0x40704140503034025a440751044040b40da0281d0f4644150310000d41d806d00c1d904c0340c0d04000c006a44a600c40e804210080c00a0030059684004491901400b100d4050700da500e61400100d03c12060620b115100e0403180140c0100500665804060024031a4103d40f545071070b084502e00a9851800030f0004140707111410042ca0555001034100c00064105da0a201440c0d0b2590714100040d00280c445a00c030000400040c84200801042e6040741050041d4001e90016071204185d0444002070510101000041b9103d10500d42007900e00b82c88605003400341043d01540104028078000d0a001521401610450750f010b8000c4a09424022200d6101a860030800c202000e00c09011b01d00180105060150702c02e10801c00c0c1d41c00707804044000103840c02d00e0b03200600320080d030b08090b600849040b00104501000c21403184031000d4203850108003401d0a140c0800d16464035003043d000440c80349400f0041c00407002c0a4500ea035890b0b102d03a00850600b804140c2d8218040318001c11030380c0180c0000700c07814 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 23817263 1250 23816013 23816033
    0x204120b0a0605030d03090b09121803010209060703050304050106050a12080d0e0a0c0e0105190b0d0902040501080a03080604020f041a130b07060c1809020711040f0203090d030506030604 82
    0x21075400070000c1d00d251114000307801e12051203031100020341c55030b6083d82400000c0c080315800c000c046000380702c0b0300a031142ca4a0707180220030b6884600c1a010040d82c256450a404844604400130682a41c9208524001c1d01541003034405031020361a110bc00308982c1403000307200b02610070130045462415129559885150710001c01407066648806d400d1039103000c20003802040c148909030700d82b0124103015078404080e90503807000d2711401240f403c1400c00740181004100740c8100c1801c061f95404035404030750151411000080d0060320304400090030a070042880f81d0160320941d079501d0701e900c9080400090740900410701510040c208010070940000b46500100000032400c40703403c001d9030350008422039296900881c0e144c9030003d000020005144146099042d090038500007890904181010f04c2c031540c09071040050b80000c44106105a05941c1a4171110040c4240058451911100040d400035075400e21a44102c8401e0700d0103d02900416204080140007400746036079680303c3c00411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 23818513 1250 23817263 23817271
    0x714070609020405090106080d020109020a05090903091011010e010902100509120a050c0906011b140703050304090204030302070b040605030a050c090d0b100f080c060f040e01030501090c090204120b 87
    0x141d6500c0d03801005848a018191280f020750000240c0c40749010f946508060000418008591411240070700596a518004003a9042600c0083e4250340e07a00d8024518861411010350008008047c43c00080e4440e01018110b90107000a0080c4c802d800300f40c509030307a000c0c680258004074040200702c20620610240c007207407100230300041c0c940d1150315620b404c1003600c40341601d460f04607407030700b00c0c5c141844000d454020401f883d10305081103103510300103445045541b00410300504282e01e88003c010030815030000d10b8001041d02d0742c2e259210301c80c42c001e62180c401103025000c0c02e1000110402c0d010b00b03480840d2020380f0391030b1440d41c44100300e500600000f03100c5146101c2c01e00030a1a151282c800740c0c01c60901ca0451074005003400100306d0740e0303200716500080307528840c65401c5c08214070110b0a02040c0e9070540728140c84070200b203a01c04650145402800100c98460000828448150840700003580140c020450f801d4499038040c5c280d101e18081c171300380e50003071035140c400056584180c250704c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 23819763 1250 23818513 23818523
    0x60c0703121b0507080c090402030312041b080615010302040807140604030602040e04020108060909030403081605010c0503010905010e070f200d030e070902070b0c0706090b040b040317071407 84
    0x10b1803607103003011102c14241c00382c0f4a580210b1062090304401c1015001500303044034105000d240c283c0c0002e40c1c07407090303209218039681d041e404a070400122110110201c070741000054080c5442c2c1d02072680e21402160300c0c0b03503000c1c141c502d4010194087d10880f01a510040040d24455040401880c0d11494600d01e8a070440d60401c03001011403242d03c042c0c0042e0a2180710403182d070a1900004007421800382c6114899112032091110b0410000125401c40754851019625681440c08a150042c1f52007030140c07681d42403030051700794594080000c5050b0385220004201c01c1e6201c4140c011180000c42c2c099011442085881c10302d58000c07601c3c60310807048211a501c50300f01c890f0134907040c641c02151000c0841e4885108427281c00082c019200a00500e54045080148644440e00e1008011703041c20440200080c807801406155004921200d8200c454001c1d0380c100b41c03406016000044805400044151280105803a071000d0502d0145601c0e40e591500c42c04000c242c000c45502074070301150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 23821013 1250 23819763 23819777
    0x1002030403060f020c01051806070c0303020909130510020a0207140409150608010c030207020a0b0309070b0c100608060402010e1e03070801020702030c150f090a030212060114060c070312 82
    0x407228061883c18200101000d61103282084c543e5003910009005145039050341c21320300c1d64200300042c3c0954041c1f850325000d500c61451f820290002c4c481c5600c2242c2040c1c1e034030208018032180c440c00041c0207110714121150400d0b510984801c0b402602000380042c0c0100504008200c602e8512005040000b040055500031560340d460312594083e1a118803551202c0b400c1004080a104201060249040035440c003e0103500091701304c0320314010403d4608012000c10f40400c0204241c6014280003a050360f61031141050280c3c0e510761021307200c00c80c14100200403c0300070340400c00341e0084d0b5060f110303041c00442d04030401035040c2803e1060545440e00005402c00e5540c204840001010900c000607910001c900605081090f00e80c1001e01074429000844103d11441085410101ca44a51291030743c481000040654503a940043d50200d4280900c440c0c440000c21044d04072100ba40107124010030440520455011742c0401c401c0541040c0410404100010180000e003610361800039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 23822263 1250 23821013 23821019
    0x290702011205151201140610050c0303070206040c0f06020606010c05030c0a0305040f1a180f0a09020d0501170307020105071b060207060207060201060b040303030f0f050a020a0e040506060910020304 87
    0x340440300c08440503003410105420280e0142060010301c58584c1030356000780040d070125108a208600d02030f05850040d07425030540702900c0d108005072a26141c50000f62640c070704084100075500d14054505840d108440c3d00c1c005400e28800c1480c504807400794000d00b8040d681d1030010740b5810b80c0d060086d249400f00304a0010181d0050041410a031b110707841c2e2070f8945042031103c0c400b8042c0c81c3c21801140440c08201401c09c400c2e0005c0e5908c9030f001c0d45d15051804c41e40d00100c0da6110158000c160012404400880d5040154000d031042203c00c0c030003008183c0e030b00c1800410384d540c0c608507080c00b60010041d460241d48504005c0000c54042c10b5220f244402d4904240c15511041c4d001d1001608182002c0c8403044d41440403400070320440c4024450f160425614290903c210b00c401000c0c55580c0d00c3c0b58a80110315040701c030903050520000c12080c5490700b801000b0354031901c800e02c0092950240c0d24402e00c0c140c03244a0185001520107400d042010303040c05054580300c0c40100075444180000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 23823513 1250 23822263 23822297
    0x9020a02030406020c060c0c090403020a0c060c0219030210050c1c020604020102101a060d1805010b010906080f04060207081209010605040c08090d03020d0902130203060a29070201 79
    0x50044416650045a4480c54081d0080c00d081c4040d02e5203108603002c100c2c601080c0320001701c41081000842d840315079a01d45240a1b86044001e002c024030f00d895401c40020000d0300610340c240d1881c000c2d50140242624007810320008502400000e5100c11260400400340f440344e400703450f40f228500c1c11103c03080000c41c2030800f900e00020b0100016032110003003100b107581c10306c0580003c3c006010213000807155003442a010f0580141c4a500851011460340c8400707080e504039140310b0103006e000c0d024004007800d01e00d029041d0a01104e02007504a00001003c0380302e82505071151083c8521130290340c456030307208406503202c0101503442290a00c800b60a80d101d1019050107031214100005109103000c05102c26180c20210110510880d2003c100701c02402052000761551503203801a5194080c032001401005c14000c00307508292a0b03060390411100d258000c6005e440210750201c0c40c15a25000b5400701c013403224407411281005942c010f651644000507040e47d8ac4141001d00654889420b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 23824763 1250 23823513 23823517
    0x30f011e080f010902150301080309010e01030b040905070504050c09060706020d090b19050f06010807030507030e0304030803041103070501020a03030203040c05040905030307090501050a02070e041a040308090c040204051309020a0902 102
    0x510b410a03503480c20804114070f8000d035044100c08414011505661511125680300d0048034145410300c456140712071120307842503000c10b0540748002c104008000841c03c01c01c0d91411907002d0280101e150070041816815000151501e0100040c01c4030700c1d03c881d41d560940030350403003d102403c0703503100c0c65118000703110001c8503889800b0381107000c0b61454440e41c000081c2d401c060405d4208551315418440c0030b907480740c0c103550701504a0501240603100c0301c0c0100e0041c90312180541b22404003040200410204000850107503008a40c2c04001c501c01e8001c2603110070b000c0c4101400340c0d22455050340003034000e4002d1544140074080029000b5911008141134401540c011901c81d000042007100054100c01c54102410003807071f18905050844d02e0180d511000380c01441080072200c80080d0070001c0c2c0d03da4144c4956600804c010039828a46009460b955059036008100d003e000119212230405100b039404540c4020a20352503140b030400c2c01001007010070000c4c2c1c0c1001000c040403405601e5400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 23826013 1250 23824763 23824783
    0x100614040e1f0902030408091c02030105130302070f05032e050103060615090302090606160206070b1008030c100f020d060803040f060c0b04062c0a0c050303030f011e08 74
    0x40c0103502041e05103000b030241294014441d80303803052050001150815095074072900c8107039001d03050032074103650700c040044100380c0095040d070918080001e0250b005807100c00540c03194080700d030300c1911401c1000c00b00f6070f00e003c0c0540550003031300c40c400c1441812449100c0c9801d0120302c21a840074050040090791004d800030354040d605d4140810803d481c1505180803203545240c0f15405034216800501c002c00c000d8280c0b0312482000c250101e02540f1707104000b0031994000d00859884800e4608020340708d5048908040c0440011000281c0306400300403501220b48a00c040d00c01101441c03000001064990b60010985900344030845d84c00020344241d10292010307100443d02c5501c0c08142024114054008000300092010749600041e10001041e81040c3d201ca030114000e400c4241c040401c110144440410400c0d10004481c00400410b94569407401818481000d079120f509156480c1b00a4403104200300000004004d0081c0c00c1844001c10f01c10f10b02403500d10f50b9205103241c600000c00d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 23827263 1250 23826013 23826031
    0xd1113090f0201080a0216060b030c0613030203120f090d11032407021f05040f02131506030e060402010f020f01060e090d09031208040602130305010509010b01030203100614040e 78
    0x80030075415503030011801940010745920031b520f04000d4515010500040c620014000e684584042180b540c0034800c148400f08040e242c55200c2203001c000b03c40303888051106034001d02441c01c0e080480c1e68100211070114000442c505d00e4408400240b04003500310304000d49030f42440664480342c03940c0030b02889000304400403805900c0702d190340d1b08092811000e4502015944142a405e511103503280c10361141c87e000e40c9002038599518200791100d4100d0040082d4000d00142c2d0911500f03000b82d00003900c0103800610714600e9512a5001e8040300e01e01d09502071954040f43c001401513101d0303030030094808a107105a803061800c0030a11801e40b206e5401c00b2990140010400180d418100301500346172640d031800440380c52842d15480d0030a40d170074640c9402c204005000805121058040744c040000710f8091501941c0d5a0a10342e00800f019101c2c000c2c07031b5091640b046010743c031034001d590003901e02c180c90703444140c581441030707400395a240200010401d05010028184035400c610502c680c03411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 23828513 1250 23827263 23827283
    0x7180b09070c140c0102100e120a09060305090601120b09070905070207081506010915090b1902060a050c0a03021e16021f120207061805070609080703020d111309 71
    0x92510f803102c3c140026941d8010f0303101d041840043d0303a0000d00d1210009003414001a008031451105040c08aa00510840e903a800180c00100d564010290402c031000e0782d40400464859101c2d050701c8604c20f20402101364500003a10002c69031201050342c000242e5011a50fa441c4d8500c031100690740220781d64805600040c90411a480081c011201040c901e50100c0300c8520702400060f21740056401440106070b030601001b5850340c01410b071400603040240340c0c141c071451315100c0100d440482c00f0000e0014041c00010400a08941c00780342c1c0929010001c490600526400840082d00aa1484d074140204100e0184210308400000d001090a02038001c22040c1d2600510031841d030b49031301c100c0f01103440141c1901d005070301c1080003404024032000565105031a05020015080d0301c10038200890441c80040308100000810000700c4400b502d0720703840d003503845238181d4a91002d1700c4040d41001a0452100c001a140d035010781080c800107000d200c850b01007511440880e010610122196285 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 23829763 1250 23828513 23828537
    0x1a1e040f1b05092b0b0405010203160e01020c060c07050a08030904050603031602040b0109090f1b02070e1306090b0403080601031103040f020f03030c030f03040606090603030207180b0907 82
    0xc15001041400d4160911518108a102c04140c04d41e800484000c10045514902c41c02a48048090042d41e40c1004858140e81001e052650007584151800c6410501c0300f60b140761040d0085103450000a03050300030386920382032030007800b0300c0e41c1c4007014080d41c6015900300424207503500c00700b240141100d1002503444882d410300f404119000079150a1190348148108481c0c030400c12102c280d0f50307906541c0841e180c1790040c0161207841441c0c2100c202a030030011103200c1044661f10401ca40c0640b0a210070701100f400c00d0030381e01e400c1076009500400c806000000d0382a0481e203408013003980b0030003001a045186480d0f40700e0381c40c01501c1c11000140254280300483d030345401035221940c2c611002c80c2ca1801c29035907a18030f040200800a01607140c201c408602960103009848003401c1c03102c16a070307403803180d03000201c03140c3e06c00c5500702ca4091405102081440d501d100c1c031425640d064004000040c01c001d0252925045451601c0c445a1a524034003032540302d025540e1301a40035900c0d90110000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 23831013 1250 23829763 23829791
    0x81204080705030c0d0f0812040501050402040b0f0105180d08040e0106080a180209070e1c030210060f0b070507050a060302090103050a2a02030706090803010f091a1e040f 75
    0x99aa4480c500c44d9003c0310320600305903600c0098489003030380102500540c05003890640064001c0c105000c2180c82d54030208800e001040d0409881284201c03400c200c003280900c1040b110400c41c0d02c503503001036011700c884000061400070f89604041c2c02044500000390700da8070b115150380603411180d0400e501400400075560000722407034105080703038810b0000c2c02c40c54003035041e001065200039205070440d0000c146100e000707090005410385c01800317220044845103a88005594441d00c114014820480321003844101403007601d050700d402c49658090245403240c55055500054402d40b40c5024a480010b0f0b550341c3d210407032006088648003d03032036210080c0003500300c2e48001c10414425003020004186a4682501d50014a071000c6043c0ca850940441c1286180105000180303401d241400740c6040c0144640510b048403810959000b6461329110080140d80c100c0e02800c081d030380200c51040c2945480401041c00301a2161820f00707058dc0c800000d0305a41800e000d03094955640e18140014070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 23832263 1250 23831013 23831023
    0x15060f03190c15020d0c030507080706050c13080f030306010305090f010504051006060e03060a0c09090e15090d080f0a022101170a0b01090f02040510050903010c030507020a0b09030408120408 84
    0x2a1500207010540d90289000c6d0060f60380d81c030010108180000c3c1482080f401c1c606440c055500f00c40e0421691034905141800d0354032585c0146600d0700c4404001418001c0028100901040d6401450864581400644c05407a01601d11031840c00713211843c1403482c3c802d00c9010322a03801780001384500c44003400e0392011180c094001d4004c2062005854429481c00a5500e42084000000284103032040700d0880310700c141600005403480c02d1403c1810b80000015507a10000309080241c41141c07150305081e40e880643c075640744007103115080080d44c080c030442141c2e82e01290191016140003c10841111001200d1803d0042d0780e0043d80181305416041040040d0303407000d00c0050064040645038042030ac08144281d00c1c0d0680c4440d591b01c3c004615030107407030080c200039001d04c002f281000d8000d803c179002201848c1c043c1d03180c6643c101c41e041c4240201e0380071384529005000c0203940c548a00482110051103080c3c64801000005440181040390070340a03242c0d2040c5a480f1404e00c160b4600708 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 23833513 1250 23832263 23832299
    0x607080115051c15030c05090a0204030f031b02041d060a0e12090a12080703030b061602060d0608070803090a0f060918060b07140f15060f03190c 64
    0x450410611044080c2c00c0340c100c580341c0c807895424220255440460a001d8003040c10324a1030404450000000c21071a84480380548000700c03261409a500c4c0b103092012402144400380c9058107036040e64010070b0145840c40100040140682ca0340052a000f16080d80c1803041440015001c0d000184d21100c8240989074026800450a1005c148040d07440c46d9900b4090495030700720113001070012903964550450b00010301741004c0e012105003003420211482d4010080a401090034a2421b0b01c0900d0301c00c0407550302c02c00440384404110041e40034041950004002611600c3c0d0301c900102c2c51540410400000744208002160b407082c404040c44200070480d0f0102001c040107807401d024458200c044c000c1900c5201a254807400840d00d2035001400e21580040c2005c00c001680009214114440e060080c4000c2c045502c4409032003500f9654011524240d1010760000001c5540380c84c1c00061515558001001c50702c903814402c8084c0b5922144e03000484400071074180402440c4d14850b20b00c5aa = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 23834763 1250 23833513 23833529
    0x12040b040b060f060a0311130306020307080903120703020703120e0106140301060f060c05070906120c06051201050f0a092306011103040605030c04090203040302011409032718040506070801 83
    0x20307403101a4003144c0540541800f12090644500c04135000e441c2c0c0b68191408200c0c0aa21150710556038149040294000c0c5c800900148010380094240e2000101700d88103500c0c5400c55030059550181c04400a402280084041203000c103425504a60365000c0c0c100380c4070b110300c00010064640f80460b444298107000650190341860020043c10403080c180c201220040c0c00c141c510f15100f8607201e802c005980d041110003a14042e00860349206c0740c1c0300100c1092140d604030a010f42c0310781d41980d050064201c680c0034a03c01030f005200c14200316480b100d001202a061a10f00c40d1151881003c1c1d6980e00d0301644a50300c429600a414052952903681218081c2020660364a000344078540b13a11030f600900c41030007000404189d103c0080d10880e001002c00400464032820300740790080c06000c00c0348103030802035168800705951364000b01c01c8403a807540c2c01d00380411809018040602c2c5c4500c0c17040b200c2d400710b003101098074104000e2501e20712940c4201c000e415245807603a00944103840c1a082420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 23836013 1250 23834763 23834779
    0x1182a180506030a0209030f06042105040e0a0b061921050f04110102030403060c11010c02010614040e070b0f0c0106090c0c0b04240903110a02030a0201050c010212040b040b06 77
    0x1c0c03501c603841103d8005180010242ea1040d280001c2031a0600380c03001e1941c0c80c8a014100300502414044262002040c0a124030440c407100c18211540c0c01640601c190100c5aa40030410140c542c0d403041d0442200030307204c42d0820301d18800e031914800241c030354080420103001e82d01281841c95001041d2891301c000040260f8180480da280e030882000308001c04c1420960121155a8020030a80e8011540700106100004083c0401406a1840200c000700c40d03080803041c902403801070050b44140c4018a21054420412104210161120309240c0c48580500b90001c0f9168683c540105440000748031207550740c00110000908407043e550104c00501c0ca44581c00700c070b803980300034a40700258100c4003030061500c49040030600e410850f661240c5200a5494010000074103400c80d42e0724500075200c446407425100c00d419108c00350890000c1d895004905624015070060015107283c1181800060605096424921145909031000e4230000f500748100010400c0e0800001e51006042d14800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 23837263 1250 23836013 23836019
    0x50307080312070c08031003020f010c03020c010e2206031b06050306090c0d05010303030b04060e0c0f1c0606030f0e19110f0402070605180f030301182a18 68
    0x3076164018500030180b500c0c2000b01151069215294040e0700580000007956070707080010310161054400c2c4412802108981010b1f5529030280d00c16415040c2c1540151071040c0800c001158400640303d03500d584034203241c0e40e20f0002c000341b004100d00c1d5a0b0015000805c01d0850400c20003184600086001c2115244401e22001d68000252900050280c4803103940341c0710030083c003540e0300842c00b4110016241c84000010301d80e06810900c0744440a807010000c07162280382c030b092010011260310f00086410031514040c800004c004200a080750a458804081c40402d50001c0e54100c0c0d104200282e02d07100301d0040c0c1c00c1d0600c26404d4846000d8010702e03040062241a52420340070000103002d40c1480718240125440d500300e00c2c0240000184110b42d60301d5103141500061a0645010300b1042c6d0007048403110080004801805c10141401541107a18108620f95840185098850111340390300549854102500d21103542c0341583c034920382d000340e00340401410308084884006c008e81401c0820 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 23838513 1250 23837263 23837279
    0x60e1807060f0504050402030a0501090609020a0203040b03040c150c0204050c040608060d02030c0a060323010302060706020c07050d060f0b060313020d08120423010b100c0c0b03010f080106050307 86
    0x8120303007503401c0101d00259102c1c029101d5000702d501c0715030801d00000070000d24445a6211a0680740181c20421610362160001c01c00c90143c0302400d009a801007000b402641c0001000d56841441552480354a0341c645969581e0068150954008620301000070802c500d42805860b502c0040042030341c0c20b040c64040b00405504000c0e00e01405480000f480d82c056403800d00c20f9841071400505412a001d03030700c103401801040782c240e00c80c0c50200903d5680c0030051426196a04030303500140308904180b10303612035800a41c40588202d0f03d91068802c002904c1d103a810017940c2d042d000b40f00004405001103201c1c0159010800324612441082080008803038215805500094040c0c1303500031880030510713005200d0302c1171009828075109200c003000200034800f81c645005101016400f001c4421032044682a1807903031b114941c1c00313030a40c48100800da01c140b4106403694058524413042c680c2e1414030708442c2e4000c1e00f040610a200d040d082c04008400d005a05c0140301c19401071505510707241c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 23839763 1250 23838513 23838523
    0x7020634120c0215070609080a090503070b0306062a070b09090f010303120c0201060e0c07050d03050c030a050403120e030a02010e0f061602030408030406030b010e0405100308031305060901060e18 86
    0xc14286040d01150170740a20249500406243c0d40c0000781d1a51400b4941001d00000e40034421a0722a1140400100300185c6410540780140b0014000f1818203090980f105001204031450a90541550800078000703481000050000d0522224460350341485c40280180c051f070082c1031003020a401001080025440b00e40e03003c44100e082000110103082c42c00c202d01500240c4c1c440482c1080c80414001d00700d452070020302400b40b10ba03080b120142801031741a001c0c0c0f40101c0304102c80320018400905800842d81160b5405842440c00c14510b0300410720540c12202405403004a550000c15a2183d0a07024030565001003840d1006001c8491010040d03903541c03c0007000140448869102010303100c1c02001510042c0018400b80d90322540c982c00024020400200000e00240180015070b040381400e02c1484c0c00b0710241e01c0b503040441d0840c1c94100c80c5a0019000402070140d0a842c1008190309010f09801111903a001069140c90b02e42406000d0344003030100b404090156002e98001140060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 23841013 1250 23839763 23839789
    0x80403030506040204050901030503030105100908030418060b03070c0c060309020f061e0307030f05060607031209030212070b010e010b0a050a11070302060309030a030c030b01020307020634120c02 86
    0x900440e0703903a200000f00f0068001d0742d214542000c91600084100a004409103050301c400380e480529001c03411078101c64410251080f050039800c208014001082c076440c0341d110032030b036030140401e04c107955085a00c800d5004503005000543e0703c1c43d500d8100204070b41d0070350042403280350034003d00d042c9030000348034a0440740d401c51241d03a0005402803040d40040c1c1d51032011800440e140e03100c0c50503640203806403100c243c503184035a10704000030394140307446c07001d03280441e030950b9601c0303002244500301800916281c4415819803291322009031402d001c83e00205242485000b018002d5450311440510240040c1c01c1011501400c0c0500400327194480150b40740101d96182440c9050800f84049050105680000e07402100010400009400020081c100e10b120780d0340400140c05000400c80c00c80b9205181da07030060308104605009444c003000a04400818500c0101009174040b440032105d448a02034144180d112400103000c0c84452a1041400400d83c00c04460100b460380c0044d500c0c0b05844 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 23842263 1250 23841013 23841017
    0x150a021b04060305061303080108060c040e0421030212010807031119080109060e0d080709090f0b060a0306061b02060901110102070203071e0603060e060105070201111209010816080403 81
    0x414400365990741e402510040d40c2080543c1c00500300741541c0401d1240301a03094002c00c0481000290458002903918440d00f00c1880340c1c0e04203410098103214910000d4010750310751a0050014440804c00f1484080010560b140140c0da604090301504070410141d0004026400135541000460745900c007600c075030007040341c1010a18402440c810800c1c1702da5040310b41250310b4030802600300201507000c6400451050121450405007850844001c07804840c03403000568408820048069150800c1d10400200c0802080186140f00420200c0d004102c1da1300c0000e49a05081240c540c102c2c11803541c244003148000c0182d00b8079004074445111b40700380380e41009804508429142403c1d41a6550319900800303032880c8030346c0d42d4026901e040080100500d01c0c4510740300020814064800c481c104c60040110640c2681c9603001951250030455069062090f180e080e0401404180b14030070740035141d1040c16450364480000100510002048162032000014240304025000485141d101b075042c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 23843513 1250 23842263 23842303
    0x7050a0b0a090306021215062827031205040305030a0c0807140a030318020307050d0302070510030501080111070b06040510050d060506090705120f04060908040b09150a02 75
    0x1c90854506116074005800c00b480450603220840b000c0d81c059005072031802c2070712030801440f42040343c1e5109420094060f41070884040e01042c1403074203403140f601c005042c8102c2991003d0300003d1807101a800e9030f0150074040d0410710070003500b03040718810b06480b46015401c04d4210b558a83d5a4401c1d045241c044c841c04519803c10086000d0886d60401d5028003c40c07504034400b8400c56440c4022034007107011a00b040e1108080c01c075030140c11105642c000b00100141440c04040c072060203098071007036085000e030380c40100b50364035604a0031210310740329078000034250324082600342100e101c400d040004810401030361001c6031050f0605c60300314104540c00146500c4403444c07040c11802a922841e08548401c58240900034242d214500c500c1302560706200603a541901140c15229408000411101500c0440c500d0004041001d922900c20200000c400b061500e440c00c558001c1d50141c1c20548000642501c01d040500d40c0d06034034801034141c94106090b0201c0039481d0200000f4414201c0c200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 23844763 1250 23843513 23843527
    0x5070206131b06030b04290618060304151506120209041b030603230304030b070201020705030414030c12030301090903020a0b0c03100b0708070b061206010b0a03060807050a0b 77
    0x1400c1e108466201c0c4060128200c50f52030340081c0141c641d1030100c91003185840c0b03900c0c0c100f11250121600005250513040000c81501041002a81042c3d5101b8642560300c100c0d00c0c200d8070740c2401103000c0c2b4018000144504428a05842074840d580e00c0b607019900c60400400000c0c3e00300e50707486810480010701507119903414010030014120310001001c04403901c0b085e030120b690998840308c01d5038003d03043c10070280798000505100500c0900b80b444646d204010800c08540807805203500044544000751410800761981880d54100c0d40002c1c440c2e00c400024003545180401c6a1b03e02075600381c03034144511491041d00c1c2d880f07000502c5625031140d00c621000c410140300740020365020307900000441160503d0000c524541d0005c4807005207509411030302141c181310000c00d40d04072903072182d4180d25210300c6075500c0340d0008018050540005585180e004840014007140740a4141038100d25241c14042c0300080c02d0b20b000d58082409a0403242003071095441ea0307024042501c03014403c1682d034400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 23846013 1250 23844763 23844773
    0x111071401090507030804080c0105031b0304020607150621030215131b1e0308190302090303030a0c030507090f0e0601170c030403090504050708061909020409050405010606030507020613 82
    0x50b02d04002000360140140c0441004281d03070140c0140c40c0d808044a000506102c01901c2e240300c15103661490035035484010081100710f2005503030240c40503001500b080400d55034040381c00803052110f095262280e8050240841002d19554441c010180d0700040007160781340a03441d800360141400d068401c0342c000401140b04089942030081d17019823410800c0c038035003441c055440401d018451500c40198404c54007448600c2191050700d812103080351a10101400584000074061419028141c003030090180340d55040c80034610548051901003900c3c2851a8001c1c11103c2c0201540240080d95905000b00402e92142c502900d0041020114980b00e080040c2c60052108400401c50390390082003144458200d00550f0040380710307445215030719803140100001e0760011206540010100710000d002403910102100b08014001c200c00301154a454040c3c081e030740160804070b03080e601c0d80c0500040000c03d209050003824189420402030802000080d101d0340702a009841d10001e8040c0041405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 23847263 1250 23846013 23846021
    0xa0303090e0f1311120d030219020706050f16020d030201020703090b1305040e030d06081507020604120509040905010e070e0c030103020901030f03030b03060f0405010f0e060a090c030b13050d020111071401 90
    0x152217481100c8280d600000000c02a5004550840b0041e0312100c451004500000e002c80c10346800c1d03118103052086c248070280c1540c000e0f050448002c0d003500c6202d009030300c902240009050080e4000360f548d0b8001e0502030301440483c5d00a204040017008032030394401000e0507000c10398000b25800710b10031001c10510751850254200b80001a440c1c050001448d4800080301c0300580b440440107171103903848003400d0741c07645030444001c0c021003a41c00c040b5a050b4490001099201d1004000280c0c40f0362135200c180c21221040c080c55466845100705000610346020032a501c4141000384601d1507041d98089074510106103c001c15681542c16844200341c041e81000c4038001000c0c0840b17206240900e4280d110740c0050398190ba580d480d082e0303076100d418001e028043c0741072250340050100b900c0e603410400c0200400142900c6000c50000d02100040302c0385200c0340a41860303480a40d078645542025030402d2500d40c100015607251101407240d038000c0d9803d90f802c0c203412071a000e20a5061682042c050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 23848513 1250 23847263 23847289
    0x1051006051c0b061b0d030c0c0f0201020f06100602191106130308030412030b0303090d0209060d060f05041119090f0216150522020d0606050a0303090e0f1311 70
    0xc1301080712120b800c10805200c000e010054201d0b500980c0029041c1c04442000003c00002442e40c0c0b40d10780800c68409014442510610485032840c1d8658020390400409490107a805010b9400070841c0c0356041000c411404451444602d042d9401d07502d1000088c04020010f0080304081280031030704220b4a640070095420038034032a941d203480e00d0403a00d11008202800c000c00d1608200c0a22403d001040c0e034903804000e001604080d100c0c1d020042d0741c8000500d02944034900751040c0d000a91070740101c00c030241141c400400c0300c3c14549404600e80c1d400e2501d00e0300810b110008405038001201c03980c011500700000c0040c003c000e8070034540191080d50942000211405210300c20018641225207040c91a801c0403c1507440f20b04032084480794001c0c209201c031441c0b000792030241c90801106542c1c14230540d000105155102c010442a11640e0f0065001c242d800c501040440410315260b64030240d910443d80c498640105400015454100d000c0c0c441c00800c031400007651540407000c480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 23849763 1250 23848513 23848519
    0x40f091107080c03130f081902040b1003140603010e070e09011b0f090e090307020603060f0306011503050708221106040b07020f030312370e01051006051c0b 69
    0xd10140100d6080c0e4130b90205c9051160003000200015801005010300c4054a680c4005405a00001110581c00001d42d082c180e0b80320359201c3d0350055550f98801c00700c0c2c1d0403c15482c08aa03604104040d04001d4030020480ca00913410508007805070300300411aa4192000300103462500d07101c42c000c803801881c50003039025818180c4003040b109550001c450317911102c0c00e980e0342107019403103224844484400f5245041d00d03038001d004d454014a040d401440e840344020300b606070400704200000f0b181031001c2c0d105c80080c0480b080245419903150003542d90050260814900034201048100c990044100c5c40d4801a0815080316081180c920b0580a074150300801c0e240e16640c0b606800001940310030012072180c0c2e1011000407480c00c0c041305884c451080141c088549680e8610140030384c49142c01c401c12111004025001506100180700c140c14454603800241e5060340c0d076101e400c6400142080c44038020441080020a500c901180c6407400014a1840b1003074640100320b019103044150154 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 23851013 1250 23849763 23849767
    0x190c1b0311030609010603030504060f110109060203061f0c0b0a02070c06030e070905040b06040e0304030501061d0601020a02030d0f0318061a10080109090c05040507091a040f09110708 81
    0x188012251018803054040301030310b0054a13034061040c00ca8041c1e00c8010003007001400708201090003200c2c0b0682c00c1c45541010401c0070b500c056800d00b1101030101c11036010743e0100610810b400c02d0800e0507078003134004903010401c001c0309001a2011812035401844054520700085103450190107542486600009140741c0300d44404000d0042c0950403d0083d2500c104100002c100015000344c90049030440d55241c0f458407404184405030020070444092403004000020000b84c00341300c1c0b0001000050a925100c414003c41c01382e510f40c01801050442d40204045070140c1d8000c601c03985190100d050140740742c3d0441c00306401030030281030707600e0042203403002e00020b01406070000310700301031400c20101b5040c0e2030303108112072440c2c000c4c4a0000107400704c0042c03107001c04070307030020501a001d582c0110069685030009001e03550115040300000b510114104500e00f11103501101c040d00102c2d589040606001c40000003006910031643d503a5154020010040a400211100603801409481e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 23852263 1250 23851013 23851019
    0x90b120a050a0b06060a050d021b0a050307060f020301080303070e01020c12070312031b0e030307060216050601050102030a21180804080d030501031a0709180902090c190c1b 76
    0x1a40b1035100c2c01040da00442194001180f07464190704483d03618185455490600d002c00b07420100079008050740c0d401084841d800f2074040c4204121040401d0f11400045944460030b2401c00c060307903640c403034010340c0900510050062140110a81e80c2c841341ca450300080401880d0b004030306e0500941b03145034101907400e20350b00011001084d00b40a4a005001c0303041081a4518104d0445440c2d0700c000074490106083d940c0c29074800c01216011000c010116030605280c0c3d15044c0807039004c607103c2452441d0540400040050610145004260900103181800c070000d6029100722070112040001000561401a802c030081e40120454201101003050310115498070313440e294000d000b40d03207d41c801d8110001403e84207001310303410703683e1020540c209025096207030390190300058681400d0281009000c42c6042e0f10710407560f072611640300041968046c1d030042c4491584098804802e009040000d40e400901c5589000300d01c4096290481c00c03442542007808600150034000703650807114a03000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 23853513 1250 23852263 23852273
    0xd080a0507060b030a0b1303090806070507060b0306090309060c0a050d050901090e061008090c09040302070906050d2307090c090906060509030d0503070905030106030507090b0a030c090b120a 84
    0x1070701c1c08078494941004080080f8003010380c1c450020031300034141d0031040000782c000c00c0a998941500ca110342420307110030380c42d007003d9428000100c601d01e0020780e02150003014008240140d58903c00103801400482c01d0070888244c8a01c141c082450003808009801840d003442003202d00d202a8025050391400032550100800c141d22182040d4002a605034000c258004408605030085030028440340701d492507084181c0e10b100c00140808040c1c000d860000c2040e03151244424455031190340545160b03400c11440300704a91182d0032240c016010140c000001170401200806a0b090b012148800c0b81d0010f0900c51900d2201c0e00201c410f070307080001203a503c0b034112110500b61510300000f84100c0f030316100c00303c0c1da03030150313400d1658035510004d25500089d0290780110f410540c146420020151140c0100e400e403525503008a88a9000039020031095030a4421011703038004c00c5400c440030903d1a290024803410f180600c4070440d40c0c855034a1081d45d122880582458030340300940700307021900d0400e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 23854763 1250 23853513 23853517
    0xb06041d010203010b040e010e090a0f080405040504050c100203090108060d14030f070204050604110d0b0a1208030411030a0c09022215020f0c031e0a0b0412030b030c010504140d080a05 81
    0x31fa044010041000490a554145100d6100b5080200180560440303500d810302c0c800011031040d11614420880407821b921280034507480307075004d40001c00b1409070b05403d002009071101c043c107003113400030700c46145039070307884a03d031a000744007100c00d45444100350600d10209100002d80c5105480000f0300a6625400c0d0700180c040341d402150301b00714690f81d8009010685900c213102002d0301e1010800c03c4c21180e01d5511406030568041c0500f62580d45844908030f16200c04c44050703e904401008000402c400e4801032040120140c01819041c179140d0340788501071003603000b1486095000b00b060003401c07005c0b00c5190344440b214082d101000b551051101c052405421207080140a41c0040140e0003000103203000d04520040c00400510007000221410300040500f00061801114110f002141c0b110310824040c50003900600118005004007034122409503a80314029045a0f0744694180e0b0890240c80071101c5022204461200c580c1c0040c110407650314004280200110b955008035902c080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 23856013 1250 23854763 23854769
    0x8070602060117070518151c1b05010504150201020c010c09080105071404120302030c0109080306031608060711010921020d09050901170a0605010312080a090b06041d010203010b04 79
    0x5204074108400301c00396130311030711180142504280c542c805203032450351082400d980041710718041070a0070403100002d600203901c2c0380880c1e1085001e03030140e0705002c403e02c9091103249400508060040c6080c00203065802140b24145400540d1208180814001e4045824039102e040081101c51200140900007130317418042c2c05690743c0b80000040429010340d0700388024441403080303542042c1c40c3c200e80d01060b40c0052400c90440c0003e0118900c165030900585201c075204c2e580242c1c4a203000d1042c1450320261680041d8244904201040102c4002c104070f5041005490114045985468406d0241c12101ca00600440905400a07038803425a1080304000c0c5095080e00c54404003203c4c2110505154050254082d178140c004001c501c1c1e6024280001d00c8649090ba021405130340c60b80360447c0c0090f40f00381d0345076441c0d00720000c04550110141d0307480100c1410030054a8402c1d02c46010f8110b00074451406180c0e9601d01c031525060b1258081007910b1110b000f075640750386400250983e900644 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 23857263 1250 23856013 23856029
    0x201030207080c070b1b1506130b03030d0203010e07020a080a08040309050904050106030506010506040f0e0402010903080f04030b0a0c0c0311070b18030c0102030a050f2209020703080601020304061b0507080706020601 95
    0x80d1800c042c80c8045505282607081201034801074503440104076540003109c000b500c150741d0b1010784180c036440a002415540c109800010784940c5891030003541c400e07008148008540224000c103002580311000d450030400c41c0d2a1038055aa648e00e4207455481d5250006540440e55200300701c100030054200400b5244900d080c2c0320780303913660400d01000c0d0041d400b42d001100c844603405d10a5566503089598082c0c014034042500755660348505850b179000c807400c1d81035803c1c0010242306110440c41c0460700041d90740700c00c001d90050f024009003441c0054000400b005001d45048461180030804200030b040f220a4550751403101c0d5042c035100c900b105148034003034001c0010b5155190b00200c00c2e00c00002c600c0d114580340ca14041648403060788a0165141c41c0d903082c0c080c2820441e510071112000e001c1302c010041c0e0354005420702a1216000a00032411584200700030300c002d9502280c0402070140303201c09194400020300e043c0d810138140b40c00900c41d504c210800040c1851b0f000814604883c0e001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 23858513 1250 23857263 23857297
    0x15040e041b0f0509040804121a061e0616050105270706050712090306020703030e1504051b040e010203070201090c0603050c03061e04090b01090f0e0a0201030207080c070b 75
    0x30a602110760300c50300c5100119960441d003040241000396019901a214460041c5410b07126400d10304034101110302a10300c402c0b00b046440a5080051034035070000310848813444100d01000320341e11401003908409001c0d0301d02003005440084844113420784e40b54030000910080c60000c80e18003400108030a40e0740d0240d00c01100e0382414401143c10302c165042603940f54039042441c0c0b20707c800c2085082d404001c100d4845400000f2640700c0c80540492482551302107100065244054541020b02d006400070f49220028400041c2c00002d104106d6401142000c1580b0f0300f031000a0002e040c401c0840c5402c1d4000000c00800e26810b5004445051040c58030701c11080c0c444000310110344088034441881c07207041003c5603091030410200d0005d44059140d190750420a800400d0503141e140c5412958004900010300100707809008401c160910303e4420001e0b1034520301c0c001c0c0e8800b801c0f10040d0500d40e001800e401804a1403080b078040c00c56039812650495501c03810b000042c0e12010302c0480710010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 23859763 1250 23858513 23858543
    0x3010f0509210d020702030f03030108030a0e011115070201091403040504180c0303080612160608010611060a020901110601140306060409050a11060d0f0b03070501020a0209010b0915040e04 83
    0x140d0315010b100400d00c10002e0401d08441c420f000294000d40059a140c0700300260300741c070410200000e5001e030041d00003443e251801d00f480a0a41010002c14605000360030301900d03415900040d9208890300c41c0c200302160380e2a15402a40108000c400292100004200220008070b0000c001e00464008dd1020001c04040c20f8040f16005603030b000090640c0c2c0301c1e14040012900c1452003d412400003030146003060400c2c0c0c940392514229524258903200b5440e41040a940c100712501e0040943d803c2880c1c1c04660404603070385880c0010403d05543c4e901103410b401c0c2e80d20500801c00c084500e40b0403540355503100d1303098000442d90b240070148203100c0c0c3d000280d03150415004080d14554030000602c21f00b03030141e41307003000c601821140715040f02044c41009942c501c18092801070b40b0848400103046003028060609014040e000b550655120a103a1401601e860060030b04407100c1009040d240e05250001400801c0c05524030552140c02207004142c650510b0b54240c0500d01c940643c10500c07007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 23861013 1250 23859763 23859793
    0x20f01030908030415020409020c061e010f1a0d0e1501050a0311090a0f020a03060e0c0705030a0525032601051323150a090510030305090f03010f0509 66
    0x4034070401040c2d5241880410009494015199815580c9500c0581001d444811150807a0000d024602d459407010042c043c0d0011142240a00710600b1a0125040e604150003145143c0781c5125a2a00030003100d5100c0304604494241c9402d1150039800340001e0f411125040c2d90745c0b01d901c000381950040c0000000ba00c1c0b4240030a402200d502040d820b1482c400401001102c42000344208031a60f12183c2c0704c1c011014038402030a1190740d40c1c80c00075046040c20001e040c0c000005003039000c80002080542d000c031303100108cd03540801251034001d0340e40030302e03286e1941e880c020b00c45050040c20a0000d94000c147d044050320015040b008481d0720706000090040310a007100f031052507000000d08a0f04905010715400034051800681d40340a86564000703600d841b95001220b8000d440202d03271f820600645051402c140c02010340000501140c104850240180045484010301303100e0002601001902c554010403403d0b0030040c0200a0074046e0000403000d800304450300d00b4907003d801c076400c4c3e03611 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 23862263 1250 23861013 23861021
    0xd020406110c010f0302030604090f060c02070801050c070605040201090909030302030f060607030f030f020c1c0206070504080d0c020103090501020a0c060e0109030801050607080702060c0c0a0f0302030303070f0504050418020f0103 101
    0x40595a0001340056080107400a50020702080d4009071035002c0c0d007003c1401d000c00d01e560f051041100046031034a101e0001d0501c6400d4000c440d6590400b005e0001d01015001a03402158001d44001952b450b50310050f100d0040c142e005441c26401c10350101300307054069014511801c01501c010380c0f550f5840c000c00c8180e100d042d83c010301080005416038903081c480e0348511440303051440c0061808106280d228580100864903081e000d02e0302418071102c0e641405500e41164250900604160404801580f154901d148003010000103607428003c0d68800d401c0407030380c10b4100000b15552120510000d000400d404e0003a60824101002c0841a041c14411611650740660358a501d50f402e0508001d200d6000403000e403040c50301031003101c0142c0d0310f24008210800d95440103002440d816010701c840c20b241e55100e190070500801c410030140c7c80200880c0d40c0550146000710f0512038219090380c10b801660003154105140082d01005a0303282e500e0302c192341d802200e400c201901d02c200114252 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 23863513 1250 23862263 23862283
    0x1c030612020303031f051302090f040203011a09030c060d0903080603060910020313080c071a040506040303050723030903151b0a09030b0a050117060411120109080d02040611 76
    0x150f4000c00014444170000380300c0c00081c0c001c1184240c4220b98a000040e088100c1d051a0203596900190a441511300f820507500749240c01d460940c04c640c501f0581c2c544512800c011510580c6000504030324640d024048400c44030f400070f000a80300c1d210105008010704001d0400c1300403805120101d0241e24001413542e1140107401e00504901b074415161502075000034020120071324400300b00000003607100d4058644020b02c2002429180d144c02c0c0103aa00b050820a92291000108070038002034854108940c1980c1e0181011503544c0700500d4040c0c00c08084a4250810380c0300052000f40c11100800101401e410840844204060041540d00c49483c00d5a140740341840344000d02900f03195203000b8100c0a515030501940d07280d52600da00e42d00041c00c40e000380301155180014007440c40b20900e042008450f0000800c0586407d96502818600714842c0611079941e4000c01c040c40316003500107492083c0d11445070703a00d414540f40c1b403074069041402031002088003031822081c50300e0300252104130 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 23864763 1250 23863513 23863519
    0xd020a050c0d030507020306070206060306011203021b010c05150a0c090f0311030f060f0103030f08070c0201030b040905100b0103060e090c090411040903020d020606010302090603040809030307051c03061202 91
    0x520140401041142d4459203000c07028840300344600005607a0501c11b140c072880c1075401404c0985450001c16090042c140c2100c00460000180b401c082680042d540040c6244911400001c180c800010303150b008101c3e02c0100b86104036007502541c2c100d040c0350140a24003c038000e2021103140e08041d5040b20b03880c09601c1c19890440c1080010641140c8003400000003d426076010142e904406410f103081240c0404801d01001c0040003050350010540c07110100514180314103040008004007064400314002e410140c0f1040203995540d00c9601642d9100d9128084441d003241401c00c0c2d03005841c2c0351080d5130120b46480e00018054a0000005105c4c1e100e4078060410001440100100a00c010700141c1d0369201100d84014030351214401c1e1403030107000b0b4004000d52080c803c4028a0101c005048504041c011310801d8000e44425044d06c0c3c10541c402150f54494601c4008646140a11000030300148a0308000f030003162030f0a042c5801d40801c5580a02c0415100d21109008039280030300250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 23866013 1250 23864763 23864773
    0xf11040509040b2d0103110a060f0806040608070f1d04080406120219021005071b03050705010e030406090e0a06140108060103060807060f030b151c0207020402030c040303020d020a05 80
    0x6a00c1c158281c0c0d00901c030628600e02002007000040307085000141204c84015100300510a0201d0a401e42e5000141254120050f90170250700900d220301c20780700d040c10b0008401c04030f8035560b40c036000b01000c0c040c00c504880c010f03580c3d101602480c00c414030500168000d109040e9010311001c081082c4110340098003586021316000302101e42041e0540750148440d400e109001e2010f04845180c840071415a000b80009803042d8031820032910090482000d00104038441c00c3c0c0f20030b010051010168040c1401600c9540f90304003075001d490b64902590b03042c00300140c080740803a0000202c00640705160380c07504081c1c0e140007043c01215124000c00d07261003040c240c2120720798810401d195003d04103150200b43c2d150303a0400d0500c0c160054010801003a0608403510308243d052048003a1404216445e007013101c00750380440c05601c101061680c0000c42448401c03100c0381e5680444840c182d0141c82150341c0c2c5010505003000d6049408128010300904a00d44241840002d401d02e04a411402400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 23867263 1250 23866013 23866021
    0x80c0405091b0f03070c02031b03120a050d050c03040311030a0203070f060f0507110d170106032c01020403020a0902180603060109090207060501080601050102070b0d020310031202010f11040509 85
    0x8450710b00c80d5141100c10340402c0054442c0c0c02c00920240d40130794102d4540c2c5a03083d03100d10406080160b054415a055040411006402d42c1c00041c0c01004000d00b02c619a035448003030314101e4240c03040707508038600542800d0500181e8001c44005500c12170103540c6210f6500c039140302c80b50b201e20a500f8440c005a2041c0860404104101c1c0051800d0b803043c1000120300c180204008203075441103070b486000c500d042481b141e5150301800502442031447c0341600548062a000410071201030141008044d03403070901e82e1003a600c07110b1112030907528a010000040d44090514044d40c854001280030b901000000110703a01107000b55500000c80208440d01c1e80304400611210350002801141000b12100001819440e14401003895a028842c00b150640c1815103907850620181e11260440d030007400204403202c50102035440b800d602010150762900c3e010000c1d08000e0241c4c00182a02c0c001c90360107141e45030154844510052003240038059042c5403040c00c6450b004034420380740c20095000000f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 23868513 1250 23867263 23867281
    0x90402030a0e0604152012100e0c0301080d05040e1303050d09060902040605030303010e0a020a140f0a02011a06070209040206070f05060709081f0b120d0e01080c040509 74
    0x60340d40001484000169109000719540c03410a00f60f44c2910080d011202891203c8024018000300c0802c800c44251010050024210300d8401c018240e9500c0101c6c2d804a1245071514400da002000c20841c00c04181c246400c141e2041e0b4028820098140f140e42e414090280c05402540c0450324100f48003501c039514800c2300310001014040840400c001000000e461110501c80d100ea244e004000009140c41c0e2441480221412604440d20950041c0010052500700207000e6500c844140c03405621600d0841c0107550402001003140d0358188003242180c4100b980201800d01c541050f0b0007030000604070b045040e11080c1c0c61380110b4010104000b501d001d401c0c80c16915820030700c0034181601d020344a803125181034040d064121402d400c0740313090000c481c0c1d12044034409000d06001504070841004c08000c041c26a114401459030b881d041e00403501c1e981c5a480107140c005d0403042d1420310380103000091510a1004007603003c607aa0710003040d4020f5501c010b8800703540002e0b200c050144c89a1001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 23869763 1250 23868513 23868517
    0x30c0f0507030510090219050a05010c05010212040f020108070e0303091002030c0f01090317010513050601021e060a3206060720150c0a0210030e01050f0603070e040305090402 77
    0x105036100e10030311800000150041000b51040f03038000070005404409441000294022003000020010500c0828006591000c2c5c98904a80090034203a580400a140050290060558492107054101c08000c10711100f50a0aa0024800da07503a0304c05644204090303500758801803c2d503805500611103124a400d00ae450203010300c0303041c01280d081040c030018152402410280300354103a5190409070b8101078101000d2151000307103080b802850340c10f00001c90001c1d0b00c0f010303164503170580b91004904107900a02c5504608055a44464401c01500c2005030783d480055a041c80300d14540541e25904120405014905410480c80003e0280700c0300021005000b01810081c1c0c850303400c0120000049888840d041c00a2110b0000c0c0756604208082200000400414038100502081624800100842d110321800e42c12280e20003241c9140034214001e0881d50000c0000f98600300a200b5912011201d4a100e10340c100d0440d0f401c42d80b102000444aa804d42d001000f091040c0890741240c030341a00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 23871013 1250 23869763 23869793
    0x40e010216080906040305070305070503010e07081c0302040806040c0e0a0209031506010315060305010602060a090203100c020102040f0308070b070203120f0601020a02091806100b0702011202090301021207021009030c 95
    0x4080c4d4200740e1640c5a582c140015a4800c90752a072010104120b2400c0070b000c0ca44804800801400383c06203403544a41d00c1e0100346074202c9200c0b0442100131917150195041c2d502614101c012a0380758600352030407030316040ea0360250849036030761040043c044110500844030518800b03000343c8a0141c2080d142640490080d044c18149a15440030b1804602404402001440b456501007400d515048029013030480181c0501c44050400c00e20401584001485003580c00440c9030010760649a207004074028015504100c0b200840c492002083c00006400b40203028003032000c0650a07142e1400c00c1e80d9900c5140c1015528100b0b250001d90503810380410382d58401c2d03042c015650030814940c0018000038040300c080032644e80d400000c2c00400c0c420800b0300c0d0702c000c17a81c4500d5242801c2c05c580c1c04a60180740c2d4000d04110003055a402414503039010384e500c8410240083d034603100c0042400c004240c0c1212000d0051207400140354145141d40202c2080380d0309603c64111076003003611b41d1080d00c00c0d0342c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 23872263 1250 23871013 23871019
    0x9011409030f030304120906020c09010b030a0b06040f080111251401050c03010915081b04020c070f030b070302090d02040e0a12020f0c0109080705100c0b04030509040e0102160809 79
    0x5079a000d500c0c82c188000e502c910300c2104104092142000c000e40f10b508650030030404c640c044120001385490f040345c0e95055039200c8420a880341e95148002001d000b0f9001100d80061000c00c000840c100707104035071406d4500034402400b025080710402400b43c01030341c036031311a114401011048540c0d0300d42d5503100b134a0b0040b40e0310205616210f801a003559070070750360580d0294000004002102c1c40c3d04c5940307403170310341c1c1440000141d1409414598412401000514104c4008081d01080d9604da0441b11400082d1042c0d800352076803860b03c4954060a407206171815420000004e4040e4440e1007180d044420052442103801c5182d02800000c05a070303a02d2005d640701b2940c8442c0416240202038001c0d0b4078a500130542d0070465204141881c0f10640103d043c00300d010800c0c0503020740826910280ca0b400d0780d401000c514502c0c0120ba00d01080305000d030103503001e4814041816844001414501d0094a040c04862580d00c0480d0803446040360a00811807440c40007c0012031140080c882d0b03035401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 23873513 1250 23872263 23872273
    0xe1317070c060801030b010509040515070216030602040306050c03010b071b091d0c0103141602030f0d0e07061103090108060f180406050f040201140306011202030a0c02010f020901140903 82
    0x7540d07040412805034000340042040140100304008240c200346000d800160340e00d1483c0e050075035a5a60720b408500d034411852035800c001a404a100708001841a2080450907040301e660b414070400950045c00240c62144c1060001181d07103920074101c03030407580013a0010749410181d440388241411070003400c400740e01e910700c00007500529501031341d1039042512140d40c4010000e166858500405c03000f4840c1410305015080c0c94401c0c0500c4101c1d80f01e000b1540480e140f03002180200d00314031455007003c05444002c2048400c800c6190701161420210b0002c1361805900c4200542d08213928864074290390307004010460711948503000483e0003074400781007400b42100c49000100ca43d4800300d5409a40c40300304040009010007405080d401c400d180b04000c01506098000a20b2901c500100d440c07807042c00004a030321a44a10300d000c01034881e07013400310b4990910003600e401070709982529038019824060780f868211501e1085481001050310303442240340000c2c000074602c1e008186062340c58010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 23874763 1250 23873513 23873527
    0x90705032d01110f0c15060a030b04060b0301020304050d02010606170a020a02070f080c040f1505011b050a0609020f0a0b0d0b04060503010c05030f1513050604090f03020c0a0e1317 79
    0x1040b020b0441c1e00800756120b503c0e5070038181c030f00340303040c86d1301e4003e040c1c5100c6030040c0002c1c0c2e114140c0041c181d9400200c0b42e845070b0340d2800e005015080d81a015a0590320000401040c4030b004940e0482120442d40240105036441004650000d07186c182c0c02000090f09001c5041141c170b5a004001c8030965006445900b0755403070a25244040580c80848a9000b00c40c0080e1203160512400819108000b0100721290003041c0c80c0940c80d60500502d8103001004007800540d1142004464510394000c0072140820081d103040c10241101502c101d000700903030003a0000d94a0300504d0301054500540d082414201400222006822907600b6030f41c01036641c02c1e0104240c0c5083c0510f003500b000c99280e1a641e070800091030403511500400485a205030313007080b050641c1d1034040700304002401080101c2c40341c84400004005013000c4100401c0220041510001c140c0c001c525012084011102a0f4140345d030740304402440e10302140c4078031f41415502d01100001d0100710502605450000000b810a20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 23876013 1250 23874763 23874791
    0x10e0f0a2307030204080d03110412020102070b21010902030402090610050c01050f01080f03040b0f0307050405040c0801080c0f090408221202040612030f030b0310020f03090705032d01 81
    0x402690b00c40300281c0c000405100c0d02100308000c06100846103000c0100700c50100c030101d507600503800b0781807003281c12184c40019680f082040501400340402c203580d44202c0440040c0c10251044c0411603901091000011420094404c1d41d1146401800c18403040e680d1000304440c00701502007d03401d1000038003d4020130402482018803a0380b540e00c16460130350600c02114a0440009503100b0160320401051002c40d5485041d1004040071000081e140e4854103030035116030107140c01c00d0ba0814a00100072606581c07001c0784c641222085800c0d50039403041c10052011401c592240c5036048007402e40841d0020ba80d05c1c0052030b4a050300160b150710140c1503d80305417001ea4550001c05102c221581c07100540c0780c42d2185200420600109407245511590042d00c1c0301c0603c04002c09060796161400b00c940c805000301d286003e4030040c115034400786071800d01141d4200340d0700034544c0c2c429410003041c90b0800140040d00d407e1260031485c01e8404c10007001c5080d844c003484500d1155203402940d90300031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 23877263 1250 23876013 23876081
    0x61201020f0706091406160e0307090e0a02010801240e0d020d0b04030e0d200307030c0602100e031602100302040f0e04050f1f020903010207020306040614010e0f0a 72
    0x107407080901103080082410841040042032001c40b05542294040c010021038005804481120300d007044920026460300007030412b00725030b0080c0c500c035003400448a11408045804031030280300342c8580d400d070390321845043c403540c1d0a00c05032000703d042020342480450241c00380360b1802ea0014950b9100d24a558040b4110003403000003103c202c60200d00340000c0540240110400b80d0042c0c82c0c1d0b1030840e140d41c940c4181c855020211510b4900402c045090350b86040c0032030400f039608070700d07005609a80c03074500a64503400c80000410b2a407030501c880c40f000f0317004012205985207104800a084013603808104030486105080720600d075003003000107240848000c4800c0280b4000c10040400d280608209003040c000c146940030756004421f41c007103121440060350216405d2040c006880c2c01c0350001090080c49002d002960520034102000304102d5070f0f070040e0241010480e0183c0c02c07a6604e242c1c2800c00701c0c05458441c41d0720003407800146041c0050784000d0554490050350540c1d250304070ba00550704 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 23878513 1250 23877263 23877277
    0x906070f06060e010305060108010c0207030b130b04080306040608070803190504080a1115160308070309080c060402030f0a080d02030a02090d0f0605060f0105040e1e090a030801060c0308061201020f 87
    0xf807402c00410034800140145401000740340028080f0140c9542d00070b49800103400024980d00c0114046400d84440b40690009260f000c0b02c81c0081e400c1c1410661080e800c2151110300c280d00f014000b203411800845c42c503044888800040d82401c00c100c1444160200c4004c42d0030800000340000241305504025001100e4040c1c6140741070f04c803138413080c000d03000381e0805410615401086203c124030b1180700b20822064061070f110215440700e8104901429a20fa0301a040d500c5c042111340d41000c000c00c1c06801144200c0859039410301c0c00c40c1e0f8644035031120502420000341030210b0006400d1035002103900540c02ca10062070031a850000130160704c41000d040d07035890803140d94441005002d00c0303456000a01102c0c400b0442c42d131080001c04a1159000d9914040010000f1500c048881154a1001094a9080030b00d0f8507041300b2a65a40040300b005800042d082000002c0c1a4011005410b1042d0990b0342d01455076a01c1d000d200025001d100111a2503500300708070501c40c030b00b0001030450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 23879763 1250 23878513 23878529
    0x13021801090f05040809040b060d1401050a0f08060c0c010b060c01020a0e0603011404090602040f120512040509011509031e02030f07080307020d050c0303030a09030809010903050906070f0606 84
    0x4554100441c400c200c4141244040703080340f4090030302c000324900d1003d44155601c202e8011401c2c016070404100c49000b81042500014200343c80321040c0c11550b42081c3c10f0740c01c00d440304007030710383d85244c00c0c0010800e81c80b132803c2a801580c0810600c4450200401c8038100b00d40000c120840403201040981c1d0080ca504400d03658041050400c0c1c5a100d00080380b61030003200c5450565052003481c0d09402d40902119100c0c0e0360f109120400c002640d01914018550809d4004403150f8440090300d0508401a040b100350190301b009414207800714041c2e9040c1d40001e000e80b110b682c241b841c1d0145110f50148182d06001d4500000000900d6004508501c1e083e400c000180c0b5004d20700c14545082150941c04003c0d030032900045c001c81e070340001601da501344c04941f00500c840d01c0782000c509080104410b03940502000041124a601e26040540101c1c800d540e408025a00c00f4136280c00c03104401030050000c0d03005c1029110614010025046143c020034a0349040c104c6507030f50000300c90b00c2d0342c01014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 23881013 1250 23879763 23879809
    0x15060a03031d090a02370e130606020102041d1e040204021b0106080d02010207080a0516060501032f010206040312020409021903060f030b0a1104030609050705030c030c0105030f1302 80
    0x104291904554011b0a90008200948850100703000140200710304908410400700b00c0d00c5151964a850309100c110340c00800406c000d03520b4000c024003075807282c068408403003060403403064590b916409152040d891040360390804001468008060540580f00780d038030036004c2c4064122445d0907520300754440c03040b800006041d45010b0145003042e10300300c1300d030085da4414410030b000f1581810444203c0611032804642c1c6103a200e01e60403450800110141c00c40d032a210001c4104994032012500741e10078802c5507a030004284401c0d4913080590208680181c001c44041000607000d41c0ca00000003030607400c0541420f890303013845412030f00945450801801031f080c0c503482e1b60350075219100144c810f82c008040e401c1c0c00e544070300d0051f110103844080896620860240605128003d40b8061680110103001110090400513076842d9a03014a6200b802100400c0c040b52070300069114500c40306854040c2180d0f038800034600815030090a609284684000300b0300180e4506920001480c46412121 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 23882263 1250 23881013 23881027
    0x1d100b1002010e190201170a02120606031311030f01090c05090705090303071704050a061d0301050105010c0f0609051f060501050304020105070204020d06030b010b090315060a03031d090a02 83
    0x200800d00c0501541964500f8840c2c00c50901c0c040380e0724504414001c540c00c3c82c2040381c40125100c50384001700009242d1000e040c008012171940040c100030071020304112968031046d0070804580300a0359140030361406540d15400103001001e104a0003103004050f12541d445001c09107094541d44d0340110b8001d00c00c10030500403403800c2141e15403c400310349001c40c1840e66080c042070392481040805000340d08c039003200d0340c5640911070454000d854080e04160999036030380005000110500d200e001c0c60307071451824a089050500c0765504030303201695400541e00050306d615950f010044801d40b4231580f034088003008100e007003001801d01c0031155014050180f80d10b1031102140c07840d4100d2070401104206102c00750b079101d000d0710a0550111001656070f43d0001d107042c000d02071079000800e00041c1c940000b401c2e04583e00a450310381002d0b41039034060380b50080c51018503141220240e5000070021002c0c0040f80c07155403501500c8003080c400043e0540c1c0100003411120b02100c6c0100303a01e400007040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 23883513 1250 23882263 23882269
    0x315030c2d0501090506030a0e01021305030d03050403020d0309080403050d050307080a060303140a020f060117010f05010e0a09022803060c08040209011a0706060b0316090311041d100b 81
    0x11440c1540190a41607420b081c0b01c0003d02d01d01c8184103c0d8401e03800400810360404032540326200d00040030000315a1908404280b068040c210b01c10207209008440024284500a0040501c00e0380c2c07642c05440300c0018440e05400400e0140b905545240c001e000c0800002e80422600c00d4a00b01c6031070309901e0340b904010043c10020000d050404032400c00c601000001d41044d40c4100301e020300464140c0300c060300241245010240d44180403144a45c0d0000a60035540c1c000d284110442c4000a00207a0342082450301511000c0c41070062403242c1c540081c82d45090391340620701030b510044c81d00d100d0b0000180c03800301c9010780a22104554020301c2003003080000c1840303002004a40303070a0a441500c2c10342c0028511800500c54a60034140640c0e00c01000000a012110744507405030080081c0d03502c0d41d07182905a0801c442132000b029640d04002031f100d00802540040340e034041020300302c0012030740c00e000241290520160444503171545031000d1b1182400f030906814591800054880e08110030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 23884763 1250 23883513 23883569
    0xe010b03010f050a0f050f0f030105100306050108030405010c110102010e030301030b060f041109040c02160305210301030f06020c03090a032f010c060b0f060a0207060801050103020a05040302010315030c 89
    0x10f54825840520b0411008035074000244c1151021600c1c0301c90400f000e004030341031503640e410b07040d803552900041120b000428a5060160790150030f00f04850781e02c40000d00d54901c9071f4014507010070141042c000c0000c9c80d520140135500d8040c8008640408482103142c40d6070000e80044030341854050401055007860420101506022a0244004455031850100b14424007002070302035500c0340000d100d00d9000304040b090004800003450605075072130800540f50880151541c90720381d8000840300b18000b080341903d042e81c0e0072001c2101001c4499482c1c03402540001015006804180032640b91540c44503103c0d002140900030000c00000101c00c44540303440769102001c0c01c501c203400142126680b060401550780c0c3d21400002e0b40303952100002c3c004030051614164480400504400a00d902103055002c0b603034030b85c54901c01d86c1d80310307001034080e0b0244540782030014100f4001080558441d4200070321031700245104031305990b03c94580074400c13421500708000c06940101e14408265803090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 23886013 1250 23884763 23884769
    0x91b020d020304030b0a021b0f010b0f090103050d0c050705090a06060e0d081611041104030308010e01030b070305070507170a0207050405090d141207030504030e03010e060a050705040e010b03010f 86
    0x1c003940c0382c14115582c852000c1d202401000000f0760118001c51041014403402e248140040116005268020840350180c421501040c0c0540945807400b0240c0c00c041350820b040c1c1ea030000c05440d40305034400040350211a5648180d13624071940b01c001401d41c850b5240180200003082021500506100340036140c81c6d10072822501991010400d41c0c00b15a1203020344041c0c0211181c103040300803860410101c1e81c200703444d00580c810f203804210350003174051600070021a480b980f980781560fa650000078008400034403004e4003c6610b00700041846210b5400f06910007568204036080c42e0f01500ca80903a65454021199051400246a01295010004407006000c116410701c180d00d869446aa21481400c440100b484252542c417001c1c1140c54080d80c515000a0000d10184e01d8032240090180c81c0507902a004a0f44940d01681e03182018051080442452802006591240b10561000300701c000d20200401009120114079074510030043c40c000c000400340a40c8a50402c10040c0710080564 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 23887263 1250 23886013 23886017
    0x424150905090f0d0f05120a02040311010c03080c03100314070305010605060408071505090603041a15010e220e010b030d0201020a0813060f02030a0f0b04020c1207050106091b020d 79
    0x802e6000f0900c0000f8003141321807014a40b1540702c4103110b0007a201806100c1048807091416001c000300c148a030b81c040c00459004103034681e2074050364001900c0030154006c0140000d2800000620715446480c011500420407440101c8101d0f66500d40b0948080700c42c042100c2d94004150800a2041c240a91005080d007224000d282a15000b081503841500d4840c540c00b500c99404000900c50181e42070352201070018108176901e29203498030030042070901d40104903c1010801086409640803030a180090040c1c5076086007051007410044016001501c103c501e1200980c030401251031400f440e400c078060030002040042903003080604200442d50303030300304683c0305010100240d075001803a00c0d04941c885001d80305a107402d08091b0b024090403000341c1441c500000601481403802da01c20581000340c184108002c007440d0080200b41d210348150210258025030150160340184401404500e1123000001800c0d0360758202441a105c0d003501500006040da036200800540511040c1144510b034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 23888513 1250 23887263 23887273
    0x30708090d020f030703080901020c010606090806090303010302010e090603010f0f02070507050f0d08030c0903030f0307022a040c1e030501030507060302120c0304050307051b13090b042415090509 86
    0xf01c0341d0300e03584e0300410101908100101011410300d46082d411074618070410002880581e0722448051701920040c41a002d0710b218030740008410060100940741070341e6050f5112289140c5140400075011b00140000741e06550320700c0d203d03100d400d80d8451003a0300c0000710000b60700e0399001c0c24094140403044d404103005a44040050080b540c440920007e02c40d88101a5922511904642c40c3e8a01894881540500c400603001001c000c1c0038001e14841e41a5030300301c802e43c1c041d140034411654a82e60648607400d250ba500382c40b440c5410303007210410381d4240c40c084103604004000505281808000800802d80c1e03040144184501070120f800903101600b000d502c5d00132103102014080f400107190401d030a0012010400b040401d00446201680200440f1b202010104c040f1f503143d50811050341c4201c01c000e4000c0415040342c040c84010303981005c880e01d05a035540d210040107580110b60079050440b480b8012000780ca4500c5200c0c06000c03400e0540c0c1c48142404201400c88001400e0a500c507849 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 23889763 1250 23888513 23888533
    0x1002030c0c0103090507030503040803040e0a020a0e010f050d060f0905070206090601060f09051807020106080f06010510090510080403020105060d020904021003021309020d150b12060604030206030708090d02 91
    0x200003607281001d01c082c6000a11350031942800c5040c401c65801c018014040006d00181505001002d4810b82e82161801d540d6a140c0c060404120700c1299a0324001c02c0390440c81324600d40c0141c840c016004240d0130694030702400c946101d0200d9800ea000380080458025083c07041d01e8842c410940d220405000600140c14083e42207a52000305211305020441a02400941607210f070140100410001c0c28501e40320400d4400c0d0042c0200444d00c0750015840c2007000a41d559000402001c1191407002a00c601d07400e0600f4846205180c0441b03900340010304d071001849481d04511308040820035510000c1320700342032900134207507000a040140f19810244e0a0405039440460484d0400d40c121421155031018110070380190103082140c031070700c0d001180e001580d0700d142c3e0021300586510310020400005115403001e40c035401d42c068005140014881c002c0f54282d11043d00e80c110f0001410f03541080c3e42c907400070b0060340c001c444a00c002040c0d403051044840c420425400a10045d0000d803010080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 23891013 1250 23889763 23889787
    0x32106030201091a04050405070e0102010b060406050a050c12120403020709050c030f0612030309010b031501060206061e030304030c0e1b161a01080c0907030513081b070e06100203 79
    0x2940f4010840132200c0002104500100c000403103004280c0600180700c18540008060030080d90038061320301550904420f000c4501e040012101038030026100c180c10440a8841202c1a030031040e030340011352040034442030a00c5441406000d44101c4031442480c05e19091600a05028850b4000c080f00b030308107800d01009080b8842900e5000b200c80c555110b6541c1e4600003e00240c244225454150000100384180b40c0c02c10340000b040d02c0d0040e42203c0c200700d0300a090785e00803c403d216030001a000071021441a25090781c0095038203401c0000028000ca06c400040d040d94010b9008135401c0c44040030810848030702c0300d1061350041d2040c50826145241c0440308600d0300c60008030241c005150160300c000c02c0002940900003010044d9000302e5583c403003141998800d06a81580e04c034821410004031454800e020711071140a84c1c1d031b500520780c142e80c0d0350b07012030743c020495040c070184004106480303601c42080410300502c40c480c0c00f0303c41800c00000740504201415408803c6410403c4184c0fa652 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 23892263 1250 23891013 23891027
    0xc071d07120e010b0a0905010f1707171c0503010609060e010f0302030a0f02030411090609070906121b020d0306091107081b030c0309040606031a01031109040603032106030201 77
    0xa0102a40420040041e1034283e00400310314000a038001019003000c07030450020b6001034141d82144e008a0b03a41c40c0c840c07140c4100c9070700c0b00e0b13640341c3d050340015828409140112040d00566490704101c031203d00e10b07903611a44840d405120034001071404801000440da02100f480000c050900f0b01541c8140e50800080c90381c1d600b910f5150074184c00001003100040954803000a50341c80340002c54907070405242c40e51014006d01d05091103107007010007194080c5064400703a0b0050119444038524686420010f40700410a06103401c0495660480b45484a600b1400000c03050526805440b40c8610681c000e0111031458010100c40d6145c01000d04175081d4980844d00380344d82156a141d11503000b40c12081004000f140425858080840d1b00182c3d5200003000d499825801c450510415403a100304030221403404c9070fa882c1d070012001840040394003d602003180c6031001031100c0d2802042e80c0119083d5403190740105c0c00103101034281e141540c480103103401c03a8400e541d0706114552450700020109 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 23893513 1250 23892263 23892287
    0x5070503070b060118030309031205030c0301060f0c0c03032006011a0f07020406150e0d020d030e030c0a080a031103031302010f030906090804140406030819140c071d07 74
    0x14250302c00100e1601c2c2c2c015620900880b21380102210f015840340750050a010b19031201312581a8282078800040b4000d50030b5038854030013186503904603072908200303c40075003d540300c09080c404000022804504600c3c00c00307010358000e889404d030f40c0b07050030306c12460a255a862000d9a07002100180488081e0740c000152443d181c640d8107446002c4150301114500c0341a800030b500c145400c10010381c030721300d9600c5c1c9200245651540e40240b050348085c0010000c1c0054000d41c02103420912600103400b86104009500014040313802800298000c143c04004507004034410764410340901e010160f10402110441417800051400c46c181203468600490030400024140302c440100260080e00c0f0740d00903a4000e801c4402401100d041c0e00341001300754887d004003200b404040c03500580c00e0405000c0c59088a0740401034174503101010059000c00103603a40480c0c20812400083d09205050034042c1140140180242110a280000c60141501c0f07035828548450600782c10803442680085c05075481c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 23894763 1250 23893513 23893523
    0x12030105010e0109050a062c1804150c020c10050403020d020f0d0506010b0304030906030902180907080708010b03060f07090306020310090c030606080907030c03020f040e12070c05010507050307 85
    0xc00300c204401030b00c0c004185c0e00401d400842083d40090b080340d00c08411a034030510440300c8a01010702c6d2500e0701c0200d01401640707800441c9141c40b03444040c3c40165482c0e0007405201d400c81c0c50003454203920107413013030710002c5401a480040d81d40a5032410200d49803c0f0041c50030102c4c1b03003d15640c00301d00b64041402c00607100d0203c80c0c04101030794540c03504100380d0950000a9078019a140c0740c15520b90f41040d1030503400500020008115507000780701740e500b09a0000c1c40c1000d140d68040040c941280000c00c00b40250041e113100281103682000300ba0060f12852001040c83c078402401c2c14a00300004201d1444500799205004d240e6401003032650989030488030240c2c0e03d42d43c13100207280003006584400b004500c0c010714903030600c0d455400381065855075034505249803100302c203280d9107844500001e010b42092410400042c64810380d40740341c154002e0400300d034510802401350308015913603c070401c0001d03000030200c082144400714240a0b00d07003420105e041404d55101c5503682d008550340140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 23896013 1250 23894763 23894777
    0x402190801050121020a030b190f0501090b1602041113050f06121302010201090b0f040506011e120203010f02040f090608060103030806010503070e060a05070b06060304021c03120213171203010501 86
    0x650714448c0d0840404528081c24613003803500008000b040b62000c6109501c9881d5035403d01003042d600c106041d6003110b03c80540542004600840307c1200000134400326880756940c2d03c442050030092015141c140700110304511440d02d0201030144000810070710302d100303690801403030200140e6402c2c0340b90404605560780c9480d008510040c4d004006d502c07400b50841564408100d10321a0704400144a03911450550301c06990b61800c03c0c4078400c05444000546042d45424483c100380c0004050005000070b0001c00c0c410185503280d0100da0158101c409202006d000612101c540d601441c40108220f200405196155890040c10600302520302c90400c04000041a80a48548020f40303503000003c2c10342c1e560300d025550140c016484950100c0343c1f41c40f079000084281c1390840642e0720940c7c01901035509100107203410714a06130402411010710403810340014000d8681d1000e0035004109000780350410782403103a4801c903201e0082c111401c070340c41815202190001e40058a0440b103084c00c0071a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 23897263 1250 23896013 23896027
    0xf0c02120d0b03060a050a0b010306050a05190312020601150c0201050d02030915150406080a0807080307090e130c0b090a050f01090306020c07031e030203070b07050405040219080105012102 83
    0x81e004250242d541441140140a00b2400e203500c114010f03d9400c0381003240083c00e03c019010b40e0f40c42e20615a004a940d14100001e0a1100072010000d80e0118500886134681d5038009603410080200001a03000c000140140004401c1e030300f81e10481410000791440c86030340001c1603131103071274043d8107126004408644c0e03c080800aaa00d9004800303011b4080d49823020044c201401c400c20307914811805d0200000e43c0c500d0118030300328401d4010340ca891074a0015205c8081c00d92002d0040d408008011200103004841e1901700d0303000d14890080c8181b00c075440d041012800425801100800e0010080f4800f90340d2000d200d40d00300d400940e54040403007904401a18400380300da1010300114000a1107880400e40800d1500c1580c1c03151100013281c0d02c00101102c4c4440d5100c1000300568070411078640820614468603521000c1490a903141c04d4071000490183c1e0031100210a003c000c84100c01c00080d0850302c8103000d844280b91900800004000540c0d1502520095041007a4000717029 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 23898513 1250 23897263 23897287
    0x20d0e0a0c0303390804090c0f080a0c0206040605060a03020a080d02011a010503060d0c2102040e0307080a030209150a02010504050d030e0c0d020a0905010315050601030b060703030c1e050901030f0c0212 89
    0xa1b6004001071201042450b082402c0500080440004031000500c03181c0001c94020103840b40c1600c50303c260380140103503500e690380c0c40300410b405040144c0c810b01e0400c0000041e507401c0c00c00b10150942c8005401b00e484a00b00c068251108202040da0000c00411015201e9900c8425294040c02c105e4002c0300c25886400c0c452808003154200001c5c581002c0e601380300034134035001003000140c0f09540401c41d05906106ca9600d074003910318000d0520740c00300441480c03d403007a0050003404d03000410240c00c1039106d100c102c0c02503000b8095000541d4442c41040140321051210030115400c504044c07040038400c2d94025112070025400310712802503492190f09544691900102400310710400f000750356120b0901d803148a040d41d031a4000a800c4c0300000740c01e5403007070080e039251070b00141c5890b090400f5a036065003d4100030300264200035401c1c01d00c1b050001041103881c0c03552055100c06582d50644400102651010505ca1440703500f4124808171741980003c0a140c90800319011641311a104190 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 23899763 1250 23898513 23898517
    0xc11040e030a02010b011403010e0105120106090c0c0b0609070207090e0c0a090605031c1202070311010f060503010606020c210f070306020a090e040f06020d0e0a0c03033908 76
    0xd1044280310114141d940140c0560000001100988841002c180d019901d076605110900031415602e030000d00401050501440d031891094811001144c0a42c9a8080008607160207600c40001980050f102c0180481e40c6866034001405450340401890300100282d0386010324402e1071400c43d5519601c0e44084405d1014114829000300a110740950b59010403000e02171038003480303100e4010313007860403048007154081d0f844540c9651a5900980e60303041e0081c0094000c081c00350144104102c03241d1000c0800e115100945109c204002034060030f250905084541c10b030030005c25540050340c5c5038010340e074014440720a07181d4400c0840450740110313880d0741004403151460302540301b03445010040003500c0d005001c03020179643c0c0741d100c4e941d03540035100074103c1d0594000e4038600e5001810400b00785035070001e00c5a0207070480c02054880401d1132807498808a41410740d40c0b0301c80c114003407040581c030004082038a10803000506103101880b01002162142310041000322000581241c20001c140003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 23901013 1250 23899763 23899781
    0xc010207060e060a06080f1f110a03090b090d051206010e0a080a0501140105060a111e06040203060f190509070b070819020706020c01120e0105070906020d0504060c1104 74
    0x16081c00342040b05042c45940303a42c1a0365240c004d50820001107031440d00000c40150070005c01c13009120901030b0100b10700885100e0541560b8140c0c41d800807580034204103008100c211310701e540001d19135500742880c0c0c040300d1010b014103a143c0c00454811089035409015582d400c0304002c2c800656031605070040c0e03400740000040c0ea40140c0b0354907000134009404120110403d00440c001c1c080c403a030068008070455003d010342039004005010318800948a2170803805980111011a04e4522085204441e1640c0c24035603141c071035000b0020031085040c1030004c250008848940f0403040d041c03400c09100058030550034180c1d0f4950b40c1c40014006103042010000404807002883e0b41c50209003030049140e4041200c0d90003011511008012141c400190a801c07100654058421b40c1c6003600111682c1841c2e44c0703815007107901d8009034030181000388a018000d869940710b0841e054503011019080c0081911044203000081c00104021a005100a006140d02c222008031070070640300014020541d83c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 23902263 1250 23901013 23901023
    0xf090b06120c0307030f060302100c030e03100b01030f06060c02090903070f0303020a020c030a02010503010b0d0609020c01020c060c070c03030e04090f030807091e060c1a0c070b0f090a02060c010207 87
    0x810b0081c1c1c49030361001180251301c180e40078481d10709240e4a8400707654003444000d400c0002d106a0041152084a24024140c0b09280c030903550043c0100081ca0000e149654041d110f55449924066603054420b0700169100d054045c44031600d0200060494001124040c1c01b403c408000280c18200c1807003214841a80103460191003003042c10001c00a4000c00015009446125480d140a1074001400300582e54142e407124170750b078200716400c0c0541e040140f907105216110007021404a142d400075000c621b00318400162551140004103103404009064800031007030420441c40400d402c100010162501402c2256080c0304110204004251000c1c02030444002c100c2d441007010303030000d00f84e8083d1b129642c9503810b80740c4841c3c0e2743c03010400300341d01100f07081078480d01086203070701450288801c6030040c14500c80740704520100c0700c2ca00504548810403010001791352803c0083d401c85a9411400640042146280590307030243e0703691000700081d00c00d1001048081008109404417100c1076403203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 23903513 1250 23902263 23902297
    0x903080a0801090c0305190f090203030c100b0a08070306020708040e0a06050109080102130909020604030203030414090a020a021906020f0f0306031507020a0305030c130e040215040f090b06 83
    0x6040d00400c1650280a0018044e040c11100d008251081c0159805448030000c406956100c80404c0c40c0188070f590044a4a40d8484446d08007607a4140301801c00012400e01501c0741460319840e44007115908000e03144180540300c01030100c64030010302a010b4075840400141e981e030781814041c0103070180b40d0128981c91004810020711915039001541264004e881d41c1802c0c54640d0942406e0303004203c01211105400482000301c26800e07041030304914000781c030341840e158070703500480d003158007941240004010b4813050017401d090900c1103907489020300c1800c50810103a010b00a440310b2403012032256180100c81000c0078441a40c0c1200c2c3c00983c1d05541540d280160a0f9a40980c1c100b140c180c1d109010305c9403170492000c601100a44100f0050780600503c002654040e80d10360800b5201400c1020240075102c8075041c01020305001e0104c0300708024a5242c60710401808240308610a00c486c8002d000c1000100291654481515041100494142c40b504045110750080301c1e1544081207003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 23904763 1250 23903513 23903527
    0xd060311040c0503070e060f09060703110601120201091401021218030c040212011206020f03040c080d020a0302030301120302030c0307030c1703091218091006090f0b0702060a090308 80
    0x40c030100c00c030300c40c28203035001d100740403031004141c90f1800111840c10100f00b51104488040c0351000003443d119220074403603410700c61400c0200300f09400c1000c080300440d81441d1b0a80c40140d04020f07807401010007203020042240d403540004c02d0b42d0054410984049050300707000020703078001d10006400f2440410b00d1030712928002c110382c103880c0000d0b0015000c1c1c050758590b90072605050084400c2801020510445c503407a00c80c110801001e801010385003207909000714611417105070011030041d1700a01250700403904280d144e40c1003c0903151050305543c403149140c00081d80102c20340741103508a4210200c3c1c0d0b41c1500b42a07045100300924071405020008068040540188010b0005d501030b0100d80d99060034500c9640f00c91006444078507082d40000104c602030305e9080300800010111000000f0b070304403814042a210102030301d103641c4c01c00144c441403007440c0d408903e1100900b00010030044061824002d503c0922425001178026100050303a80f051f43e010380d1051008503030240720f81d031390740d58 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 23906013 1250 23904763 23904773
    0x1080421051809011a0306010c0602270d02010f030b0a0909060e011808040e070e030a0b01140301020a09030b04050114010806060109050a031a06130e0a02030709090b07080403050d0603 81
    0x3110401d0808000205500b810440c1014200035040c2e4080441030749140c80c3c07003458500d8540000342200d040045507045000002d26038006004485900101040824415400f540f00d4101d84940580150844007031040580e901c280c0403e1100c1e1642800155102c203a808262150142d400030074a850a0207803903410824551320102c0d095007650020000d4440c4410120200c0c850018090726030300b028801030050000c03d08070141c1110460809440c0e9880b5100442c0c00c1c03400325041132352600310b22401089080742070b00c000c002894048000f185801c0e80c0540241090b0706c0d9001c00b402c1d072032100c0c0c0080c0403c02c0c25840381c0000030310800701400319a55004e4582d56000c048072035a001807101c0300e0000b11410210700f40000d880d0b01550380c0e040c1049130176011010602c0144095840070382d0041c10503900c0130034400e500d07405903840080d11a281460044c1894441203500c901e56039458a202c1ca070100f0070300021583c10503164640240d440d141d1b420100c3c0e43d0b00030040d0190101d864840300008000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 23907263 1250 23906013 23906017
    0x20c030c060f010e04030c031107030606120c0e1006030b03030c010e06090c03060103170d0f02030901020403060e0f1504030302070203060f01030203060a05060105030c0c010204080307060212010f140108042105 92
    0x902020400c042c10303038071400405103a00b410b0301d0090208002e0b61300e480c0080d00540d80c100c020101442280c3c3c3d001c1d41c1e03071161401d030f40d001d42c03050a081c140940d0510a200c08a0305600c017510610741460054206141e405032058028820402003507075946486007030b540c09008854a1050102c000c0c80340c0100b144000e52030b5001941c110b0001e00c2040c800300900d00740819140d04076031700501070082400500038601115440f02e40383c44200f5070f60f22800010701c4401c0c40918012001000016216415454400e0854075001d0b0070410301e81c08070102803400940003d080c0b051801400c140346c0d00ba1a146002d4019000d1241c000390305000d8481000304858500e68518102c038002c50417201c503500d8040c60001150010f9036070b00d0006000300006030b00800000000d1105840540005140c155140410b13030a5030060310040f00d40940018420900c1c80c140d4102501401d0054148ea41d070303901c2c00061204020340c0b06000e40c18440c0d540005410f0286d1100d500160f042e2000601d40e041c0b2032303180002c16079 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 23908513 1250 23907263 23907271
    0x30903040503060702160905070c020406030507150306050303030105010309141c03110c070e0613020f090a06050307051206130905010f0606030b0a0902070c0b040b0703080717060904030201020c030c06 88
    0x3e1040c0e40000f0304261002500c400710054521b49009441d0510030365001402d07000f880f1005002c1e21045480050316644104001103014101421b00c582c1848010804461400001001c15007009403d00c5540c2d40801224111942400c0002e00700015103090303006015002e413840910b001e00d080621300480d1503c400d40109040340d5040010343c0072049410280c1c02104000f41650b88840402d102c140c1c92092901d400000041c1852414018410480140c1e0702000c1e0191080202007007804150920111030302c00b40c00141070140c00d61603c2d04004209004040345404464444c00100d0800d4580c2140307000c0594113100c091000c00b480d41001400790100c0c11103590518a400c0d80054070a109100342404401c008100c0340d00c0740c4c60001c03400040e400000d4207840c014512180000e44d01802001040140f1034009441c0e00d40d4168100501003000080c601c40a1007402c02880348943c4062140c41c1d44100100c0e442c95191f1200c0c103040740240244c411007071091100054560b40d03c48001242881 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 23909763 1250 23908513 23908519
    0x121602010915020301050114040b09040e1903090503060105010809190204090606030302061b040609050103090501180302161a040902210c0913140c03090a0f060603030201050a0e0706050a0201020403080309030405 93
    0x2c20104107030203d00a1027248641e002c00d00f070510035403080b403500703400101802c1042e00444440c8080c10021820303035580da80c811800f01d102c0070030030095401d060246a0040c002420013190034504680c4058a451308803035000500c140d907091103c00c543e140c1d40458821600600d040104540741d14020799102815100320b0354400c62003040c485400046411501038826940e02c80140300e14160041d405071146030011034982d521161070385d504030003100a01079182d0096009201444c152555000305c1e20b0b290308052840c000f80d0401c3c0d00840052001c9504540c42600300596036030f1140140080501c400301c4c600c411010b90350501c0358010210300500007900c4101c9020001a10485010040311020b505c483e080c20304840000d003880000001641d030082d01c00c429102036001c540e44140e0745c3c50f01c000003200c645a94038424400e143d03092082d598882401c6c0300c20421500c0310a001030f5169101e118a03410841d000803001d2405200f0f4041da002558010340041c2c903030920100d41512600303d40240b40c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 23911013 1250 23909763 23909777
    0xc060705040801180201020d0302070804120c0e090601030302060403050a0315060503070e04090c0303030b0a080f010c03060801051005040c14030a091b0b0d0b01050c0a03020a0b0106051216020109150203010501 92
    0xc5084450700c1a0b2140d00d60580041c07080100380223068010790042202559200814130000a8903042c03820100d120303d22500b00002d0282c01e1507000e4010702406031440c0700300d42c081801400020b070005080e68006805080041e140c1c190788800314050420b0410502822205103000600e968119020758040d01b803507294440701c168000300380b1049844410b0090030100070f20741c042002ca8080e6000301000000a81207040162b1622101860302c0101d4450704616907581010600039a071511428018000c200c0003400141032200740003c0000203401020311465031248107444040c0106a040013104000602a803241b0700500300c0c0c401042c00150541d07070f0890300041000482e9420b00ca0300162107041c807035141880d90b0b0607001d5008000c000301230f5050002c1040030001c1d22404001030322503a0705c680c1c02032410703070000e10705030008405c10703031141c01400f106115001218910600e01a4415000c0c0170b1510741c000040d8040380500403060740640184420003c50a010056400547c10b84d50280c031010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 23912263 1250 23911013 23911031
    0x9060c020d0c0b0a02090102150405030a08060904020d060509160807030c0902160303021c02070605160f021b030a08161703040c1404090c080309010e040c091502030c060705040801 79
    0x20b03805107240031000b040201520b00003a03034285282e0151066850600c11203a000c0c07203401030040b010340143c03426155030388046500f4918a40c003214081e0b0112050780c3c03010580c10283e02007801c1c4001008000c00c1130340c0b10350004050000c208440741d104c1c0100d043c2206010750392042c950b282d0101c2d00055617283c0d031400d030105d101c480034021111010100c14001e00c80024584085009401c006103110087d81c6022101c0f82d0103070140042c080d030f2401120b0000315070500b040100221081001c007003050241c10b2903082507207a0041030280040b884c00c8452243c039020400000c5c20200c1e42071008000c2ca20100d02d4800c008075000c0440300580c4104e11049802c0410090840e86010850703000b40740d84020402800045603407200305500b00340c084d002150280d0306640703201d80c586c09600f040c4016800442e8555883d030780700507039403001c85080d1020014902c00517001012a00036000e85940c6609a805800600d4030070030840e54804150000d407410360424043c020300d903030f209100b41e0720550b00b014004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 23913513 1250 23912263 23912267
    0x3010f06120507080103020904080f0a0807030c0f020706050c1203010602031b060f06040f0f050108010b01020c0406050607060b01051608070204050c1314010e0d05060906070912030305150409060c020d 88
    0x500460f1140c07903081d8183e2a5508120035a44001d100300d82100707003440105800b1000d18050302c1b458030343d41c031072142e01d00d07200c2070040c04c68041031070100400249000d080ca0341c0d90046502c0003aa2024600389542e800c452002510b1310070103181c02c101c850800400043d07199800700250035090884640b00b800300003011513040c1d07210800d98007854650942404116039160980c01142c00d69071611021a1010041c00b180c421100242c1c00010703240d46640c0403003a00d60703041c0281120031800b1201005070508240120f45140941d0a0040501c1c1e592801c41540c1d1307001c1e4003074800608020542c162290210f00d400080d94200c40f104900803401c00c000b0030013a500784400d4a8048005040146200f03140a0803c03100500c4c2d0401c050600c40d1400e6000700c203445404401c00940c2c0100d008204508104140d40d1900200408030020801482d00900130a1b0540c1c004d4140c2681502e00450180c03528055054900c40325142c0c10ba00038580080101048072a8000303000080c2c45400380d440382c7c1020302d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 23914763 1250 23913513 23913521
    0x806070207050409030e0909100c020118080a0c0203060c04210201020d0e0103060f0803030f060301020703020d03050a0605040e0105040b0604021801031104030b0106090f0506120103111503010f0612 87
    0x15200560486401805203061540c4445802c40c024035019044c3c0c3d03c05404669141015900400b494201203880b22107a010740c000c0102c0720904d88000c0040f4900ca081d0550b45000c090b00080c0010350015003280444c4c4940c92038451141c006040d40d0b814107000c40c94601031f5100b842000e8610500403c0c00100981c1c18200d10b01250f01030f00603156100b82520201d42d40054500518140340d9164000303d00b05c0300e86140c400150506a00441c1d803401d2444100204010052950380300e070f8010088200065404601410030582c0360034042a20380b2090702c024058103454011070b8201e8a001c1c0c070048050300542000c0c0c003460046410701c005840d240b0510040c2c0c460108081c1010141400b8404154803070390050020400c1100d04500301902c981d9131451000c03080c0d01c80740000b06480003d008121ba5081203a00425040310050720341802c0340011030b83d903d0140b00c00341000310000b10442c810785891a40d010071f0b4610490b810790325038407110b00b490080c10b10301440000440e040d40e91400e005003403103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 23916013 1250 23914763 23914771
    0x510060e03060c040302060304020a090c05070302010f150501080a060803030a1b09062010090b040c060c020a090c02010207020312030a0609050402030c0d051203040b0712090c2c09160806 82
    0x103183d5213018256000d010455201034000c83c1c010024040006500000c0e1268881d43d10341960303007607134810107828000e013503c081c0740d0f4a80364070f49000c0145040e00d9018002c141156020700741348a044e80c680c10702c44018007095210320b90f1804000208503a5002c41e5010950010746003910010341d07510301804580ca448c0a00803980458401c0c044543c0f040c0160500c0100d40700d19070112015101c60340001d109852810900310f4244a028003440200152007000704050080b0307180074101c082681d00000c140b10420320508186a036608003e180d614801c1d0119105180c000e01112149021032056244a6100300c9200c400344c0d2506d00d01044041c120700406c1e01442d0000c00410003e4410000c20214880700e44003144c00b441007141151040c010f10028500c101e0090405505600d45041c0140581d0710400c0b24160942c5004403607000516401110f405a03814101520080b03043c00f145035280034548030181610080d200c0800142990008109229058850145108564904805aaa0206032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 23917263 1250 23916013 23916031
    0x504180b010c031d030304031127190902180108160501120f02090d0507030201080f07080403080903091206010512010b0a03080a0318030201051b16170408010510060e0306 75
    0x30712100e02003482100030581c08900383c00c00d90000c1d0703521300020307113540c1c01540200c84100c3c541c0a581542d1400f805812012400300588d407001408c0035852003810750000303004800d6944804494038100c415588035210059001d0800384d0f00711b0b00c06c51242030180092261600714441c841c1a080b0400f5126810341c03c031075040e1508022808060050001ba1082034a1310103119428092001c00d40ea54000c000d107141d010f080a82030040c214000117204d548024203204444a60905001e035869002d0b401350384c41600b510704410540c0345c4600f00350552080c40c070141d80c070400a0500c515003400c007041c507a04a0702c040b0b80318004007105020311400c0e034164541050740b20200c600e0401c040341c078100041000314501c0c500001c84048c01d030800348404040308801e60043c0e54a008016031130020268a8a4401c00c1075070345800d08030890207140c1c0321030400d00010903e140403480c003c0b25a1403202504c0c0a400810000d100304e2500301480d0840c1c3b0201d00c00d0400140c11462501c409040208110307000300121 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 23918513 1250 23917263 23917277
    0x10090302040f020f03011203090e0411060d0e0318032103070807020109020d0602030415050606040b07110301180b13030504090902060702040f020405121c03180b070504180b01 77
    0x550200070081010400c002d0b040c42d001c010742c00043d080040114042d014040e05a10342c12018140100400c00e00e030090308042c0c0a039014480031443d02120107403849802c440a564950110806001078040c50940380d03406d110104070045c0b1079480c03440000e40c500c03040d401c503400384040d40d0f141e14150801d12000510501c0030004a41190701c11304030954414900e00011400400d00d90100f1058054a80144c0d90140d0110a00041000303980004c0d000552106e011b200320708190002954510039889a0240e4aa001500c50304204c0d840c0380039a1080801402045042c600f442d1444e045c050f000c0f0101c49000c03081c5c0020302c440c609014010f036441d07096915541003a04000a107070040c40182c0d01070384c0c011818001400143e640d0f004075215851002d02c00350b07e407403800040c458401707001908000c075600050f40585450210b003902c4408000c82e880d0100c0e400c0d103040c1d014088610080f40180c0202c081d00208450241c010b8010021141804014441400800010021103005d1101c0c94002482 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 23919763 1250 23918513 23918519
    0x303050913112203120203030114011d01270305060109060b12060f0a03050a03180906050102060402060f070210030204140f1c14010c030b030106080703050d120f0507020312061009 79
    0x82038150114a00f0306081d4424035503c07611040743c010380941003080184c1c000001409041010b80202c81c41450a003400c07904190301550307482c1c88800740c07441c5038104006040052030420392201c41d007c0c002a140804c10700181c890408680b900c42c240205e00c402400e01034000b6a540211045032140c0303450064001c01a00c80908008140303403000001948400340300d05c0130000c200140f002c0142148682c40d51301801c0702400000c10441290b500c05001c00b4a0700d0400c00890b43c003c200300d80c0c41617040300d4144d6181031640c0019103070700414001075040603001100c0000309400d0781c010400d64503140c0c03071541c40c40129000c220408500f0341c003040c3c200800c5010403404040c480c00032036049104101c1240d280180540140c05c45080307500110000303840740da00c00e65a043c00c0c0b01e442d026040400240c0030450079034841070303a6030300c0c20007101d000c1003508040c2c42100e541c00c0d8410f00d12200084400d0000d4101b481c0000e6881d0000c5104d8000c030404500422444c1c903288040241000340c80c1c44820050349 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 23920869 1106 23919763 23919787
    0xf03130602180907210213030f0b041104091208040f0b130b06030a05120307090803040f050118060206010605070501020d140103031e140a1107030305091311 69
    0x841d0315010000c0300305010f605c00c0c06049510015a07100d591100450940b022071b40041c0030207e1420b4804100704c1e0003040b00f13006030f0040c0d0489104507202c804001c125482002d0050180f00341507080038030940604940c0d0350040c016604410520144d0b02da03038120344000c40b507216642900c1c54104081004198180345c01000a03001086150070308d03541c41c1d50380c890200c0c8001d400440800011031480c031880f0018060680041669210359403030301041240d07001c9000301c50105803e0581081d0885d09110f2010031281d407680208174603440c0480c113031015440400240c41c00d5400304400341c44d00ca0f803401400807035240b009040005c1c2d032542c1030040ca400304188081c041e411012284004103a8824084040e04154804090780c40700d07654026105460501c0400d8443d0107100d50010070715421902401034070720151081c40000412410f94011203a6402515602d80e00038040714030400e07 = true := by decide +kernel

theorem cover : BRFrame.Cov 23741013 23920869 := by
  have h0 := BRFrame.cov_init 23741013
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23741013 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 23741013 ≤ n) (h2 : n < 23920869) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
