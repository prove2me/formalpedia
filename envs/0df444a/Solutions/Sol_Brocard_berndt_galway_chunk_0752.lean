-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0752
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:35:30.212895+00:00
-- url     : https://prove2.me/submissions/ae2fcae8-11ef-4d27-ae5a-4ed631b07b55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 135071942 ≤ n < 135251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 135073192 1250 135071942 135071947
    0xc03042105030402100201200705010609150e0405010204080102070309090c0809060c0903120711011b0b0115030b0901060f02070e090304060507021f020109020909030a090b0d0b040e0c03060f0705 86
    0x213808101000c0c541c1e80e0064215900c03078074100321039501c0e0100400c4c40c0e120080c1c40d5403075072031500d00300742550030b1f9400a540342450000740e03248201d82c201d04501184c0e200c0c00000b11540707590808901a210359048403005600004180c010503901400c1d600031035115103000c12000c501201c0450700000240e824140036404000807a0382004884028804242c0081c01c80d04401c81c4489550126044240d00355004d20300083e5042c09545c201c8690440c44c0160941000070100c2c03556507041c140c0c0180180d16a1300c2c0d2102051580c18060f0340121651000180343c0c5005682d1504001c0002070f401c0e00070030050003010340009220b0f0344002200c2c02142c4800295040a04008040303489810030202642d00000380310035191940c00d10f00c0c44c2d07100c4000550006c102c00c80c1358018004134610280c21916582d100b08a01e1500c10ba01c000003c0595084000e120354800389210080c3c042c0c1060000340382c1c014138201001076200f9000811f40075030001542034403103130b6892000c20400c650048900c0c0c0d000c10002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 135074442 1250 135073192 135073201
    0xc0e01060809061602010b0925020d0c03050306040603020d0f0519030806090c04030c090e0d050408251d0108100204080d0809160b1e09010207061404050303030c0304210503 76
    0x81c48860388004c1c035600c000182100303400c00050010b18140ca010405007031015241c40d0030642510042d0781c11205000034a10700c42c40c414002c00c070844050002e800c006004c00442c100c2c3e502d0b03800a0008540041c510b440340e000a090828003c2042d11044030281300c0c3c11191070300385099105c040391041d0552201c2c0324951b1600140038001e030008003800d030364400030880400041e841200141c0035001c0068002161509602400e00e40b9003086d00310300c1446800d02c01005285070009000c40c105d000900c1c000d1504954050400495071182c000803007844030342280d441400810307444c460485450100b200c030344100018556049108500942c0196007002030102d0003603005482da282c2001d154012694032824929040318409481d8103e010382010024070640d848441d80014100f040e45072242c0c80c9000019030020359108664464003003445842003503003c241142d8025500101405001d880e075a282c001d031040b00c1584100e83c00c8a41028031100044400d00c0000b400b10300d540f094690300d00d1500c9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 135075692 1250 135074442 135074461
    0xf0801050109030221060f040606080c09070509040f0c020a0201033b030705070e0f0601081504110702090106020312010b040b450a08010e071a0708070c0e0106080906 73
    0x17880f07070b5503c44012081c4002040c41c17200b04042481501414440f940302d091519007034040c0c0c0c04a038416610b0b0f41c01403659110640e00c08944540101079410a20b40d1a408040818043c0c04500f0b00c1e240c1f0141342140c0e91443c070741c0124070401290700c00d990410445042c00240103c0c0c060340a00103e5040411088034942403989010440320090101286e05184050791640c0c54400c480d080f1004001c41c46040c0010f6049048003207801102c03d003441c0d1500d150540110104602007101e01e442107403076100b840131041c0100100e821031500a01b050309290784541020f075595001ca0503101794a9824000000d190a60b8001d41d0240c03540c5491a902e000e240c2003100413a0301e040a02c0360302e00c007034640313045501403580240c40d454280c0030b4144050072440c0c001004804056a40042b000e64146034940210070800f055000a5628085070280500a8459482818000d44100070004035000403210706200c030700c415543c102e40b29000700b05800e0303884d41d8088441c41c0e800d550150496005a0200d2540324 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 135076942 1250 135075692 135075709
    0x30c0d020f0f0c100c030c0c0b060f04020c011401051801050d1e0c0816061704170c01050a060b070503030402040e010e0d030f05151003020a050d02030406020a0f08010501090302 78
    0x1052580d0305014403003008100aa00c00d2065a03180d5010194140e1146207070f0117107400d491101e01b020410b6041890001d0070a501c2607100504611a200c0001d04c1c0b0303912030070b04e207404c2e00c40604219114036092491500034841d680d428492401f800d00000707000d01c0e011001c541c00308544e07103030a0016440c040c28080a03107102c4404940c05100d00b5041c801403d800c50714031420a000e40c07000c04080303146c219100e06108444180d2812410904011b0040980000840c010300b00c0c0c50320b072801907030344034142400c5120038040d16104c590000901c8406924054100500800d10004104611b543d54000902284038114000f02540c0050000030301600d01540602d401116803400030071000c0c0500c5c919810120b21140c25000320b0b9882c01040340086d428410795a02c055000a00c2c9000482d000016030881080003511080680020b101906144144256540c0252070a030a40d100e023450710340310380a900aa050100052000d00f980d1039041c0c0326440843c101c0740c2c10703102c3c050a00c0c00c640030b0002c0c07507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 135078192 1250 135076942 135076957
    0xf1a032b020a120302070b0708090d0c02031c110f0a12050307020708010c0f030b241b0d050a2d11120307180e010503030904020706180804140105030c0d02 68
    0x40c0148081c60340814050700f15040c07400da2a64005945207820f01d0145080c1c00d01405c1c00741046041004c02c03101980000e0001d00c2902c4604008604190b2440002c0c60803034400b610304202943c003104410081d8120000c1c2c050010b0f24003e640d9600000c05002d42d83c1d458402c0041d00155003c4803950b1440d004000030b40d040030040c41501e5400d5140d56040d800e49a011120000041401c50640c0c080740c1c0c144281d1140c504c8c1201d000c4a826504034084405c18203114200d00c604a0004801000f1040940c9154024403e070040c2c800e04ca606400103441a000741942002240c08401c0442140c00b000501c50070a007072200c0c541c05480080d0104550240020b00041001c0c41004040c4040040e44805140f01c0e001a9076801d16955024504106a0f103581e03000e0b0601605a100501c21a076011003901d0320217005031401a152116070402c4805407145480003c500d01002da25502400344800040c81039400041d40f1a021035920340044503580301c100c1c0d03c8808150240030140341d024181e00281403c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 135079442 1250 135078192 135078197
    0x70909080c060906070f0c02090106031d06010905061c020d03120e01062d080a02150d0f05060f120604020603042402090a060507020607060c02010e010f1a032b 70
    0x708594924000d25080042d100c1c010290300410070064099880564401242d0492078030119580003903002c0742e02a2018003503001419191001ca686018204580c10032a150b4102280c1c41942d64000f0700000b46019a09140503007501e102e514425038560380d400220550180c2010855841030310100c403019032008000c41c4098072043c0808592809001b10350142924945500d02d803680d05107408003003039041084891403501541e041008440106481115a4050b5040c042c5c00310640e10b9801284900180103000030714280306038261a205a002a12511041d1030480c00265420100030320450481400022507211074001001030410784040c40e0400c0c0b2071103291949079400400080602d014081c0308052a5002c18440310518000961000400c200d0800324541642c94000c2062881145006004113446001d011403151003588074620a514082c000c012100e03282c4c09940c007270901e510031044d08803103611043c803651130089010208041501555004031108444100101482003030102c203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 135080692 1250 135079442 135079447
    0xf011101060e1e0907060c080405090f100503062703040e18120f0403060b03070509181b010c030f17010324110a0302070507030206040b0703020d0509010207090908 72
    0x11a000d0040700c000e00000d50036841d06280c1448a004418040c0e000140150000c0d018403003a20f00c0030400000350713074413454684808841070600280c28810b0764803254100d401c0004000c60101003040f05405000f82443e041c01d0b896503074040580e640c000361107401501d400c205c46002e03080710541070703111903049000989040941c1c03400c500031450402c0310f003240301c1c1c094000050740c281401c2c003a03056111512420300e0b0800c50b4040034031042c1d008074000140030319950003e202c002c0c1da0401890004000040030400545007200c400d5039040d682d4041100f55102385001d102141d06c00f11140c203101041a0342c0c40c99012407070f1700c0032120192611405002d00c8285082495071402e10140d00d07002c1c0d8001c038900604100400492032001c0303d40c40c24040160310340510b104074604004121012910300e440c016840744450300b0b1882c100b40c0e8561009600620010340000c01c0b031041d4006d0030200f4044c0e001d40305003d1403032000b542c42d07106106007140180c211032002c0c00300e000c9541c40a05501e010700d40050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 135081942 1250 135080692 135080717
    0x7180b090d050307140f0105070207030b0601020f0607020f010b01030509031602190e16020c030a0201050c100509010f060e010e1306090b04030801051f2a08070b010f0509040b060f01 80
    0x43c1194052407040d9000c007456401303000303080402c0080407000c40b2860001c1101c0d00e07000400944560721408003d1801d408900440c0c581e030700c20050000100e5640050341c109051101c0c008c2d68514280e40c1034030b50b81d424080c084400758064400d0718420382091340954a000c010310b461080185603000d0490348810360241c1030385a01410f801510280c81071040b030000d1802d14000c070f02c2141350514803d1007158002d04121006850205030b0401007036080c2805601c4070490f1041c00d04000c124510401e5030780c80c010800071643c00540120303101c0601c0c0c100410443d916007078001d400003801d01500b281054080c0109404004000b9440445801440002100201503a03000540798059605070001007441c00103000d9403508501000700c28581044c08030b51100e40c01e0000c2d000781c40e5204280e00c540c40285031484d403980c4c440c48100c8401d6202540310f5982101e440c12444010081c060f030300b0307400696013000c9500d082c00051780d801607410000380c5250340c0e90901003003041d1541c2e5504a040003100342021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 135083192 1250 135081942 135081953
    0x209060c03031501140403030e13020405120a12090807060f050904061404050108012705120a0f0e030a0c03020409110405090a050f010903050a14070f031707180b090d 73
    0xb5800342d240d51600640300c20f40f0700c000405501401c85401c1080d08100710410000b60407034821108020203680084c1000c0303101302120700a001e9580401d40206c10700700c4400c24080081224156548202001c01c62507101503022580141940a41400303503009030001e0060314060407014035000720751300d4113501c0c003071700400482e040d00c043d54000c1c091100e100024450320316240c06902e01401c083e400801034040c000c0403485000c1c0303ca0f20040340007885080c0090501606010305102101c00b6103d43d991210303d50310050481d181e22009000045003c0d00941061602007012114190880360028000303065408000051400d40300c01c4910241000c11420582c65601441e44120b0180380078240a00c00b600307043d81042041000740c0c0c03030b40e450301245e0380009400c04103480107441207191100008a001c1103e405d2403003002c00c0134100c0383e4518448400c059119402c610f086254900310302081c0c5500d43e086c1c581c100500381441e01d540c401c080130b001f00c003080b902511071400000c000010010703458880f03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 135084442 1250 135083192 135083197
    0x30a1b0801030501140c0d0905030708040e040b090706021f02090405070f020c1c0b06010c0b0a0606110303040f060506010e0a15180b04090b010521070e0409030504090209060c03 78
    0x418000c00d2000c40100244002882818050300001d54542c05918000c01e01d01240e110b00380c2d0911032295207002c42024404100300342da40303a03988003100c244e031070742c807000c6020800b10300301c0341268a03081420001e0071012011071a801152034a800a100358030280072100140c801000c0d814480c15402d10020308184d5840c01400e00030b2f07046440b00b20b07200191081c02418545071111042c042c98020000005c0c83d40d000103040d09403500011100480e448400040f2141d400070030015040720050400e00070281e610307078011002c907900e40d1111824692440c0c1d0040c0c0703a0004403805408410020a4100401d0103074100340d9000105151210020700003800055820000c2c0c3c028016001011050b50b4843c0c3d088415003c40f030240414141000e403800c0d42252091043e07000f884861500c44040c0304040c2d0080c8140e40300c0034416a101d091007800c12a00c00014802207901c40006000c580c02e46665041610803100c5d116016610503250504040b0008080d41c010301030542c10207001c00007000308180c00d001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 135085692 1250 135084442 135084491
    0xf1e020d0f02010f0504060206010312020114070503091b06070201120b12030c0d031503030f02100509060901061e140d0606060f0815010e1e0604060201020a181a030a 73
    0x201c40c048515400010303c905166180e680610904000600243d600029111f045036402071100303000046c142030481c0588186556070002035203220520110f90381003005503114007900d5040320422290040e80c0c004100744007a4540e04010304000c0c8102551103004d0100000c40c0e82100482c40f04201c6e00400d5412090440c00960ba41000c10041c02c00b541c00e202e01030f862501813805000141031310a4043c2400105d1100505008110350350420660080c80f500b1007007004024100960700d030000d05241c40c2e4000f111820044d51030400082002e03400b9070081c0710304400c00391102c140da90a010030b0320389054003403020581c040300c00340e14240082c01c180200c1010f40219550480c060640f60005000e000020b0444d000d0303a084040d0186469034003912500000d101220040003007184084007803c2c0c2d0040140c603903005040003c002c2410744e0150001d101303c020641d03542c00d60104c00100703000d9441c00c600541c86482c910a148518018034031001d52381103604903c0000301030310100c000d202e03007440392039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 135086942 1250 135085692 135085703
    0x504050c1e0103050a05040c0512120f040303030c0305100b180607050309030706020c10050d02091005040503280b0603030d0c080103120c050706080c16060204031e0f1e020d 76
    0x141d01c55020750b0b15010300307078000c11890000c0c056402c007680c544500010328000c5500420a043c03440081980c10800d03000b5190141051a0780c84624201c803075000d0740140420b401103400e0140c0030604c00d2203885510f20072a15503d11300c10090410ba40d21185034803003442404c02c4607481c100925141e94500080511038031a800550b51401240149801d0041c160721400075074201002c65003082e03c4d076400c52200901c43d85000d40d51500c00580c81002406941e080a4100308840444c0000700d03004401442a01c1c030417422140344071605000252504102c80c2d0286200c0b42001d1100009070691a045030402002800e807410301c2b060340d00e42000c0300c4203252807000007010000100180594400400c407417180034646103071542441d032a0306a0320f5059101c0c04040084803400a0840445841603845400d07203002c42b0103174000f03942032001c0a900203020550340b00d00b00030724030340c3c009010b4001401031540c44906400c1e44601078540f80060075010a0500300d0079501140790700160355142224210911a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 135088192 1250 135086942 135086989
    0xa0305060a090204150614211806150d02040b01050403150506040606050f030402101115150303130e070504031406071101060f030b0604020c030c0a12140a030504050c 73
    0x340108429140b048018036108000c28a05104031b030f5114018509194030441029659151411a0714949032000500075034480f6160510085542e0102071000d4481c1240446000e502d5284001207003800480c00701d40d00410700841e0100506164102d900c2c409414103003107041964030303115030300701b840b2502005114a80c3c910030003840d4a0103200740406004507151040c02c005102d40004030a2201510280c81640c01c0520310700304512840d118001098407405488500c0200e481d81400e00000344c51200001b1040380202d01503080000550f0012158100003940c0b0a2420036410b0300c01070b018026004004c0200408004078000410a00c5180141002840c0380c1c9403414006042c081604207944150341030400c104032049081000300196500301d901c02c3d5054940381d00007002881810344a0000d8000480c03100980c880224128421074002c0246e07503001d800c8540200d0b010a989200d2515102050000c078900340d10030343c011580544110f0807a069002d4101c0020352511141c6549181a580c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 135089442 1250 135088192 135088211
    0x50c0408060c040303050412020a1e0302120d0507120309080714100506151606050106091d09030d0e01020d09080301090609090b040b07230307030c11060a0b0a0305060a 74
    0x2040040d600021407502c0350704260450350010f28510641c852a112008284d0500c1c09552b928016440105100c101d5840c41e40d03002d9120001100c82c3d40b100381d2044640c682300b0728004e50003086074003c8060aa40350341c504841c9942d40740001c41c8403038030b010406544400d5503002460039002011051b0044105410188041c08101c2ca4241d041400580141c241300174044030740c0713452210084c0303092400d40c0107494150640603c0040c001e01c140c00307002c482c245400000c130550042141015142d8100405461907810741d40d80d85e10650589440445500c100b1106000080e1984250307481e514080026140c05130b140310040036070300f004500752051440003004208a1205102e440001c00030440240301300b00058407070198038800140054101c0d03a050300040c503014490b581021120b008207209124022542c5240c0c41650012542e4a010901d04007400d003155010700d12040303095a42da002071016540c1c40c1c03054005000a41c0ca6240c2040407580040009101844418070809421000041c0d4201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 135090692 1250 135089442 135089459
    0xc0f0e010b1e030a140406090215070503090409020a0e0703050906060d020609040c0e0a03030512061206060d082715030103120810050604080a05011407020307060915050c04 76
    0x1a030084501e40300820000c2500d18580d40300a00e4102c01c020801c0d203940c1d4450140000d0700002402e02a800c1c45003041004019040c2c3c0440c0c1200d0003914002411146090081c200d071294180c040c0851b81300b03000a0740b85152503041800c200d40f0203030001440a503200d803410b071034120554440d400b0903103c20400041c2c060420555612007000c894420031041d00341c0100d0014400ca150385400380d40c42d0b00302020041c0c000c54510030f040703102070280e64845559090080180c0c0143c00c1d0700c1d8540c0420004074509103030000b894002142d400b4080c0c200c40e1510b1040150b014107500c0120348000050100318a018039862101424031070006403103401410107420850718900321401170105c000107100600100303040402d4045280c8040c00c2c0101eaa40b1184464405034a0341d500056210100140100320004041000080140702d10002d004080707403105490540502100e000c001079100340491404a804c039006a408036000303900307000d89000c8060803001503820480d8991202000000e0030000c100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 135091942 1250 135090692 135090719
    0x90619170901050f09030a0c1e0816061103011401030e100612050f010207120503150d1118010b0904150503070602030a0801090506030c0d06022a0c0105030906220c0f 73
    0xc8400010b1847d100a1385006451010401800b501c008111040c84080300c40d04c84144c6500ca4120518503101c0300ca645000c40741a510442c22204030741000000c200d1810348a017500d041c2c45c0888058184940200d00450083c80e0b506a20001c61140345120350711600c1c2882180064a6070b007407041c00d011100d0400310b1400075120804c00d801d0388100308102c00300f000032014020440c007c0c60b1655491b2100356070305c0714203000c0f1100107600090340c045003000c0040080b500000d12130281c400d08842d10303281c20010701000f000d208001488104100c540032919155100c091504a140301d42c01c3c0c4030b0b490b400800d1410f1101d0300702e000580d000091800c1c88542010700240104059003080c0214030b021004203865082018199000e41e036481008002c0014540503100c164400f44180d00000c044000b0b05c0003906040c460001550080c20446003240d4400c1044038800c859840040000342c4441e042407484189000701d6440c076250105a801c0010a0038015100070010340d48031820300d40c1010628854003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 135093192 1250 135091942 135091951
    0x31e0c0e0316210b0907050906190501140403061d0c1914040608030d05180f0c130608030714010c0e031908040503010c030608060c090619170901050f 66
    0x303074010080b28140030700c0e141150082e250003910301d007010030300e002e440540c3d40c0310000020412078046041000180b000265042122000c0380d400d032050704d882c824098661184110f01e1654012210240900d50060b01c600c5242c040528555190640d41d85074602100c5214004c440da146454400074410a010003040f80401c42c22103502c9441c007104908154030b00818070425103e8024890282046da0f5541d2011004118406c10383e035840c03d41001d007100401d401c88122008006881200c222640c0010310001c2e0b00d032000009044140c448410015840d001d030700020300ca15200c0c40c000c611f05400784040e0440e24440d001207c101003080c2c1e0359900b9103031a01d026004001180c0700c2003015030340004103201000c03081224010986994203141c96103101e1a08615015820136988803000d07545648190122194807041e0307007554885801003840ca124a43c0b04540c4003070140001d00398004180c1820100d4551030405242041c000711200803425011a000c080d00d9568804000301c40c004521601c2d0312 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 135094442 1250 135093192 135093199
    0x7060506060c0303010603050a0b04060603240b0d0e0a080a0c0b0a11041202030703050706090503010e01020903070b1305030106120515041707020409020a03080a02070807050a030f03031e0c0e 84
    0x30041002d040c41c1e50307400305129100405071a000821f819403c1644a2140312001178401d01031540c07940e0003d800340c03444081e546520a43e03046080c0c000c003111041c04040d6001200302034944490080001d0203041c0810342d02074103014480319000000c02441c01001e0025842c1c1315200030b901d450401208141c401001c4a000d1030520004640040383c40d400c941c02d9406130f440c008440d0020b4000300c0c0c40c000301030f080103040784602d0202040345900070200b0710032a14118000d02004400c911040e09030301801a0441e0950f1095009000701e20242c0b010f00011040648800c410550b12000642035543d281e10400080000c0c510b180705000d01444603900c18090042c0b13560044c10282e40d001810107400300300942449021a42604640d2141c02288000e40c000345107250254907800d1480382c0d5030205c40a02c0c050301c074903500040d442e1804100401102c6005040c400118550744a440381040c1e1401c085041640c0c441300c012104640d00403401440c62600e40002d448868003201074050844507007032510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 135095692 1250 135094442 135094447
    0x70c050306010807051503070c0203011a100c1a041514150d030e0402030c04080a0b090d020706050a050d110310090b0a05091305011b0206040c0e0601021c02031b030706050606 77
    0xd11b881d0b02104c40c51400c900100316580e940c504001f01e9010b0b0502d040254036509100c1801802652100076010301c0e0800c0328100030205400405407000b0170202002405008105810000100f245c0d42d81c40d8003500842d40e680c0c903031101e024407404413032188540069100d40360041c0b002031903400d0b0f11814114000c0d11303048555001a200980140080202e0611854001000a030ba40c074140f01030300c0043c100b02c411034110140c1458003445501e0101c85042d400d108c0c8429000440c2e2001800740e04680705a1a210b1420015a004848a030b1054510300c610b591246074007804e00c00010011840b4822582c424a000c40c01e056000c01038444000801e0302c00c6075039140c02c0c490749da0380c40c1411317410141e10710741c0e804c0351006858071a02500c45a40d1706810242d10214240d9041c2e00881c0c0c030f510691080c0e5100300b55588500d0201009a019904140164441e002c0c403840c402c614002034035445c0603401128206800b055101c02140003030b4030703010b40135040411a4000c002c02402920341142c000c0b02da150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 135096942 1250 135095692 135095699
    0xa0506090705060f0913150303020a0b1b0304060b1f080a153605070503010311010f050304060b0114030711070f031101120f14010509060904030815060c03070c050306010807 76
    0x2500480e0709546c03280c4c06041400e840d01010707601161701d6558045054440320b80d2810301940320020544141d6000c2c0c2590b0004a0385154001c028840080c00b80d11141940c50743e407101001802a55441c5400a0b6901c052410701c403040c042041107500250f4850940e4945044400243caa6010020240081004042c403e00200c003480c100f64102c142c07e0317040584440c0c520002d600500d4035010301c4581c507100038008005d50140083d03050724000c0070f02c902405c0c40140110380d01b040341c080e0f89000403c2480450001040c60b0003083c103c0030145440490310b92510401005584141c0d00c080106030002c06240c0400000c0c41000c2c020f080100c1400f050070700d15281d0700d16200041c1001e43c100704d01c2118258803940c640d404909600304404080001d05403000304109182c0f428044d89201d0006440052540c0c6000c0b0070752807045500d80e4030b454440d01c41c07480781d811001d189200554482d80c02c0c050a0304814040029001700b5000350511400c0c0d51600c014181461010b030403d91103138000c1982803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 135098192 1250 135096942 135096967
    0x2190309030e010f1e030203061009031703090102120a02090f030c0a060807090b03010f030b0f060a0306020306040e1507090b0c0a0803100503100c201002031302030a050609070506 79
    0x205800c920071300b00240200c10307402007110440e2100700c070480789100c07003a0391806241c0d155000d94401d031030079105078400541c410415075410781188001070120742d91004101c034807207203a03014640201d01c1d00009820580c00000724403207c0000c41d80d42c000340fa40440c03035840030f250542e50052003500543c05030072401c44c54030102d00583c035540200f00603c00c1c0000851900d074030486d610307001080f819070604e440303507100c4560b5944504984000d07151100f280011400807003a00e08000d005440050040d035200340740da0395040c040c0d04010f0220741e0055549030f000d40110014441d0000e01840302560310b66038079190f5006411440f0070b4100c01c150020a20504c4144034000900d0590f03990082106908c0e40c2d18020380e5030812465401c07594242c0241e4002401c5c8a500c1d801440d01e203051a00d55005140900c0301d41540c171910030f008050142e000e06241c2c1e1105000c0d13401560801c1e20700500d05071440d0381d07801007458105113100c100c409a100000b004002e010030720580c030241c00120b440394600454440903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 135099442 1250 135098192 135098207
    0x2060a0c050c0601030308060915010f11070f030609020913020310150314010e01060812090d050102070602070b010e06030d2007031b0603050a02070209130309030203030d0219030903 80
    0x5000440e5104200300046014000ba2024524520200c1e0529038480c81d0050546405640c09405844000c010504100340760030015040b05040c0c0d92156181e040c000c04580d8960746a50095590080c40408240760761075039940030185014202c00301e0241040d10501c902e40c0b100a2409448901994617032005a030041507285544020325800301d44d0b4a0b0b41141da1001c40c2c3c00750b000825030f49400990041c1078206402c5802524000c0000304095592442c000d5102e4264040c0050b2a8608001540d43c1d494025503010b40355001c0c8000606102d02e55452104036400b02c001695400000d8004006070020340c05440c1e80014154094004556a00f4024000c2d8100009460302c3c111920142820403e00704a284000c503080604020b10303134010110b0208014a41c00b82c0c1c40007900b03043c00a440844140215441941e021f491290650b0310faa400b04014245820228100701402c00004003503a01000605440c01029070016900c003051a244144c0c2c1c10107900490034103007002d1440f80820f801252 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 135100692 1250 135099442 135099451
    0x3070b030405100221060d02010e0402070c080307030e0306090106180504050c030132040203060127090317010618030b1b030906072c0105070204020c0609060f0105100206 75
    0x10220349a898074070705542000c07003070010011180d2000c00c0540070401d122403031082e880e104901014481d260700c418002044003100019001c560740401c0d05030a800c0c00c0c4c0c0204640c0d8040c1110122054440e048182558028801500081c1c0da00303010316070a00d0203110035508101e460008105480c075008820598051210700c44d15035a9a840c0010144401070003d0102d451006000700004031b044010f02c07a1072611101c01c8414000300f0100e40880400f41d650b0a0301854000b4024005a80783c5140500c0024802c00048400c1d12701d842d05c000a0380301c0e805000d080d18400d448000c860801d8102c103103403c0d68143e115a0411130f1b050b16403010a07000c04000419640c10031032107021365450420711090001311401d01041c160b4004100305c514080491050700801441d55000e4a02d40403020404c00e0702001e402150541e81c41d82d003480025801000100002480648050700f40a03002e411642062012030340300d246c64110800708041016144200e40c05440111044280c4911401009586410081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 135101942 1250 135100692 135100709
    0x3200601030f03090806070c050c04060501200a08031008010b0603040f03030506040621110102060702030d1a0907030c0f050f07020105032a19030b0d0b3102031204050307 75
    0x490b441858071441c001009003260508a0704107051000008081e4402c4141c19540790081d961983c5441c0703040d02484044440596500315482400442c82d0000d035a0300d4080d000e948249000d034030005410f48040d500c540c60750400100300601d4000d4142c25940c40400c1d80e4811603041007004001a140480000025007510b0300144541c1d40c140410000c0269070003242c04a14034540c07002402010442510307130588070304598078103100b078031005990b1074034142e90301c07805a04180180700082e0007039806a0854520b144181d116005070320045001224191500300000342c40301c00c0001001d80007018810720701070501d07103280351141ca09450001400b540400904005001010a801859144282c5a150410020007903100160143c007161a44550b01d4400146241c000f0300035a2070281c800c503c0205005000e80a010440d0b07540c00010b654010584a0600031407856116000070041102000071007120107900c01d070348a401018600f944840d86111080d0301000f05200ca910003044074400c644000c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 135103192 1250 135101942 135101963
    0xa1a03150d0807080a0210020c01090213020a050403140c040504080405040e0601060206011502010e0d030203040213060b030105090a09050607080601090506040b09010503180d0203070b010510170c041a070320060103 94
    0x4145c12801c101070078000c2800e0b1030000c115105018010b41c400c12103144215040f05e1010505800c02003a40100103040010a5050008102040320403004400c100c011000359016216980002400c4580c00d03901680d04000100e002d022504062168041c1c0c2403c101c01010950316051000b5598070b0140290034082040f114045e460038000d41203184001d000d81d0076901140707140703d4018020741040301c090740b00b10707518a9200302c002081c2c4500015035030780700354047ca0f580c20311051181c000307006400504034507518981c80c4045101401041d0264030356545920a500b401800182809100e820192080c441000304000031b003421411103081030750a00f0003e881b6907900700109070741c1190388001c0281e0300648140400d569400701c001c0030858850318036450981d0700d072814018018100d84a00000c5030454039500c5803170410303c80966005040b140ba0504d001d844110001c1052054860500b19210200d80c0c0c0c001c0540040140c00b4071980b0407132800420b484850660754030301d010f10002d000300404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 135104442 1250 135103192 135103207
    0x9062903161d0603040b04030801120330050412110c010c0212120d060f0603090807020118050a03030203090306070219080306040204030605091e0705010504090203060a1a03150d080708 81
    0x2501521400602c001c00300c5071289044e007440c125001044a0860000b03041c0000850130302d004092420459405598260502000e9200c1440900f0b0b43d01031039240e0020300c90000c19080307107030280c0c0c0d1080388a00c6100d034120040d20030180c90300c40f0101c141030045d0040608a85640d92120501c00c13002e03011121204500d4041741c7c2c8500f00300d6461401a0309000c00107104c0e181d5503064002d141101e031560b00d000300503691800b084086941d000c500810003c801c02061003d9031040c9a8070215600f00c81e926101e0690310400180a217a030342e48100c015130000b15148965140620885a0100d0300340081d0800b0840b0900c1003900e01a0307100c004002d650301102044541d02d172507040d9000342da0f001c0c00401c0941440205581d0382e111100d00110607040a48002c0801c0801250703980071228183c44075403c01e400d086555000e500000c02483d04400400e100041d0025400d054001e070b41200c0c00640c0e035030304006405625100350004141e0292a518990400059920003101d4102e40c0105025489404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 135105692 1250 135104442 135104477
    0x405060906090a0806040c031a0606040b0901091806031a04050303060114090d031d0a180b040e120909150306010308070501020c0601060e1003050906060409020102070906290316 78
    0x141d44d0098001031003038804020401010b21810000c1c0c0c0d01a0f40d0860527146110608116240308070b80c020381000080c00100440e040300703000340175150710504088030341f82d03183c035410040184041001d869094440404205000c0440407001410400b2010031002c0c1c03409494281d580c1c40b02502c12410810301d101001c1d0b035901020242c0300c161100400f003001d2400c003400c00400480c0c41c1b4090707880c1003038803140c40da02c940b0b40500550105c0d20f01c3e9000058050712074000100406c0c1901005820a441e1406030f448404103003e4601d04070780d09580d164840c81007400340410304070010300a000401000c0c02c40c00c00c9542c0003c000341102c0d4422100703a960441031602c10301a0003000050407a134071030360001040e241d0300a030050007001e0003950070050194804100b00d060311000d40303d81c00d06410142c08200c0310308042c3c0241c80f15500600460303150755520705075001100c80551005002c06070200d5501707410302d0810f5000c0542c03040702c0129800d40c182000034408000e8150108000d01900000784000c009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 135106942 1250 135105692 135105709
    0x30a0224120103060603030807020609060106080601020c13200a05030606071406090c03060702011812090b030c0c07050109050105030a051f091506170c0703020c04111c02040506090609 81
    0x30110300588016503034a04d0716030042c15003800100c0c0403a0040001902d25840014441d104120601c000c01c0581d1078494147d031402406040241140226600684642c0310803180c0d84590080c1c24000900000d00401080840d11811a4a080c0f0394100f100703e8000b81e11000b925001507007120400c3e03480c1706503c1d00100075401d00c109020305002da5404c01a00e120045400a44150300f5800d80e0526074419400b00d00301c4414031107003540d1400d08124000400d0101004400c502c0481c107242a2940c0c0b42c105040351a0130854088040800001d000710380c5010501c41c07200103100070300b803030b030b12441c14040040c1a030f000061407020285d56820000d4580145c1c06c00700086400d200c0b010003a120b44616401c805031078000322005510242c1c00c0001512849408410260491803080c81080c0d03c400c007140304640c2c071800301501140709490095a581d81d540c4500382c0c8443c21a100315035100300989800c0d491400c010380e43c0c034001d84140030400007603c800f0100c41003040101d482554401801002402d8030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 135108192 1250 135106942 135106957
    0x1b07060c02031303080705070515040605070204152306070b0f060d0204050c0405091b04030209090c04150303020f01140a020c030403060606210c140705010b10031a030a0224 76
    0x5255100002051145e9030b0300400302240100305499416450b00c080c070081c0e28080b051001c1c01c3d241040100251072094014200c0e43d0720040010407101303203625040444002c0ea801184160b06011204500f41c4000550180c15190039250b26080114584681142c04801002c40062440300d00c0013561a54401c2c05170364401340d004004001e1070400810075241c41d00140107041c0964510b10201e800301d9070781814441070b0006584403524103400c3d07600388012688050650341981c890840c0840c0960fa480c0147d0303141c5069142c5d605003551550500030714001c1e160310802070903450801c143d03003520300c11814150311121b00540540e5400404480c5455441643d0000d00404e1030900041501d80c4d11900503c015807510b9920481002078803010003c449003403805401051404184c03400c540c0100c000b41c0001c50003007000040e098104d00203e140d100d0080c40c0720b00020b54509945c0c3d4046c2c585801500c14800980003001d20600742d41c042a00071070001804140f0341000c03400e44400e140c1050403070320300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 135109442 1250 135108192 135108217
    0x6070309031b031d06071502071e060504030e04050f0103260d050a060506030108191e03080405060106020f0c04023f0a021c0b0103180311061b07060c0203 68
    0x1080320382d05008040c8208030104100081c4410018003282c50080156080d05801030f03101d07c040400b03c45403c000f0b510101d01181e010114603142c41c11002e0240303003021007a00910001c42d251a091400420318040410b601d480382c0d00e81070030b210315080c8080781c80381900d62164451000780d080140007081065036100380c070090640002d0749207082d00c09410540c0181a022400e0007029140d6080014500007402004d100e0b60108050782c84404a00003107685c0980500181000c03045180c0c0413416020461b81c041e40859400820300080050804c2a180185201d2020b00315510382081e82e503880b00480d12219100c2c2c0d4010680b001c8049000c0450600d10b80d2110710542e0003a01c4403107000c140d281120044040c44030290000b0520100740c002c80d8002d544044011060722151031514006103404940c66040651b00c10707240c51052414190844801e02079252640000c404400703c5107030150013406580505d031407003400809034241000342e42d05079601020200740c0e50550b10080b49980129200e0004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 135110692 1250 135109442 135109487
    0x402031006032d050622080304080a1805100e0316120b010e0f0a021c060612050907080309131107140c040908090f011b050c031e0607030903 62
    0x20400d00304915908141056040a50403142c4980c01503400b26861004d861074005000144a00c80400c500c4041c142d1407211943d40710b03400351941d45441e00112011500420001040c0008541109130007034009100b545500c1e5085c20310020400002e0f0081c5008280104140341041540e800d0081507803c05044001a840d940e031407843e062206451103003a21071020881c0045400604642c21500c2505070f004048099121800c0c03c100035840480329546680901e0449800000139010309002400560f44010101c1c10b0100600c048800240c18500e00e07030f0042c54100700700b80780801961842c600c101d80e40c00441c8544800840030703001c1410300300c41c10180050070b2000c0103840e840311207e07040010112040300c20541e0901003140c85099011300b42050900c104480c92401c0940c0d4014031b401031420004188003001c03444919030b1202d20407a6541c01803a10304003641400c204154a205990f242c03003a0001d0744100c4162600704c0500104101501c0b401001e003494040c011071410400c1ca119000b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 135111942 1250 135110692 135110699
    0x30c010f0f140d06061407050a08030403120614030706020a02030a02040203090708060406090b0114030636030c010b100e040218030313050102190c0b09190801020910091404050402031006 82
    0xd00410240c05404089400980402c0c806c14444040e151120b80c0f0400030110040140c55000b103a42005004400304800200290582c3d00039008042c02030089034114a0640d00720420035040042c1600480e00b19032062408901503680051818500c0da01070b00c0059a90700c42c040640d0800c00c20b50050324841c4103401c1400200070716640560f0885006d1040d51041342d80b80c910301c04808400e024210782c1030303000e6404114030b4003d620113101e0700701101b000700601075411590508184c01c1c02a00c03402580000ca2200c058a001380142c20f030301d1404031403501550301c600030084c202042441c549400390341c0c0883c405600018140690400800c000c2c2200d89441d180000312203000f000c1d000305401405800c040d4090644080448180c00f58000a0440a281848510410ba410040000d0350000d100c2d042c07030141c13034428595000585281c07000541c3c0c1d0b60a0000b03000441e81d10301d608008101240e4420000440c608a60311817079402114041680e4407030f07000192501008140744040c0c1c41ca40003001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 135113192 1250 135111942 135111967
    0x40308040f05010e090105030c190510020601081e101808040b0304020f040c02030f07111009080d08060a050904020a030615080106080c211002030c0405010806030c010f0f14 76
    0x24421a02c090361070030700c000c1d144401d201c3c5100c400c0c071885415600c01c0311804d41030f20f0802c2001c2094007229203031841e011365540c00200e1180d440c80300382e00503800c5580140f246040c01c0c41340c1c2d4030003a1460500c07107a0300c40721117010380d68000c94061400c40550300d8650081010140e1684804c654204c502c003525641c07600c04001d0799030b0058034224491500d1400c408402e00b4280207460290b4915006142800813880c08884194000395045541200400780c4040f5030380c0300c6904030b800031119a03071154003a08001d107a920b04103056800d002441541e9017002519543c01c00a0000c0e204195000d81c265140c030f03c04100d46580e1500024440743c1070611041c445400c0070b01000c215150400240003507a0342d259030a48403404040c2864008610707018041071804060320621400223880c08854005100b100f02004a03001038451003441d0000203400c00040d80c0c0003507501e40020045014022644600002801325650004020280850500c076641e0782c60140c1742e0300704114a83e1450315941d40e000e0070380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 135114442 1250 135113192 135113219
    0x11212050c0724090806150d060507030203070f090503100f150b1c0501120b13050a05030306101b060c02010608010e0715090305030702010e0d02100206040309050607050613060204030804 82
    0x48801d8400c5a00e016a110f6100c3d42405080b144200081d20458942c0d54031a881c1c4d9280515aa4005112420141c0090b10611406120380780c181e0700140c681c20300100c0108413002035000e450402c5400750090040d40d0300411a500106400382000036001102040000900170000c0b40c910f16900f00304000806070104001071807841c2100c003d80482c090f1000000003120001e01500c030300304117108140c2d00042c0c95101d055800410790100c801030303000c89035151813400514a500300c80540002c010721100c1d0034000511500382680742001503032552129014071910a2040000c0c0c0b91b80c1d192070b15054010300079402440588a504000c0c0045035010000d10742d50301251140c0b81a039030103040c020780f28070b102da0080401d9981c86405146000480c0c0c00443c0d942d18030b420080d0307006961642d11401651030140c00710300300c41150050b052034501810050181c48080e400300380220703810808500050008a2450307440700e0110300f202801100c0c0c0c244030000340a42d070002082503000103800b04810223210302 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 135115692 1250 135114442 135114479
    0xf2b0302010c02031e071703010906030c06050c06070c2103090c080a0201120905010605040501080f06070503090d0809030c010207080414100c23031606050a05011212050c07 76
    0x81c4940d42d0141d008a81c0d174450b0f03243c8080348119481303482a0007031074240144241c1d80a0050061600381061410791294002c1c1d001104103562002c0800800007060f040c0001030555051860926082d0400d054076100d0040c6174104105103400b03040100000b288004118562402c0b800c0260240c06101500070a880c510a5420040c0e405000440140c001400f115156040e5218003401407480000341c05040c244504031030035502c2e50350101d1241c449100b040d00070141240200035480303111481c2030502402500c1f1404103c01081007001886000070210038a16203444d02501590b50110003d0450041111081095000140c4602800f50640103003055035420400c040b55017034182c04000c6072a84081403e4042580c1e8143d21000c14461186920501c5007119110804224460300a01b1580203500d100074500700d803a4400b040c4a0f03180b04599010314240307001c1045506084025140214201d40145020100c0da426040c0d01d1069060700d50300030b880811103807c0c60b00c0d40c0503292003030041c09 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 135116942 1250 135115692 135115697
    0xb071a071d040e15041707080d0b0108070e15070f030807080f04030c110103020d150f060e03120903120a020105011809030905190503100b010e060708090f2b03 70
    0x40072210145007910506203400c0c1070600400c5041c0016030701074200c01c00100306aa006140469400b40c04200383e000b00b00051050182c199664610070822003150a54000203040101500c20400403581018103540600b104503041941602c106a9002181c45901401411124008401d104143d00051204e000316500c2d150500c0c40e0361282e0208400c0e5000b110083c0c0091058009800030a0f550015803200300d2040c5000f41ca448041d99659042d106103030040031040d83c44150404c81044050400c00191055107005a4403550003800642e842511401000407000000b6203042e9664080154851403103018812903190411a0b002900801c824032a541f0410032142104482c0c280a11401445941c5602d82c000554100f40030f102980c440790200c80640301030742c40701060a58041011204010800c18003050704c09280d030005060480c4030480901900b03080c48108000359503103055a515450507100341000410b400c00280711480c610000d00c0740400d00350002c0c0c2d56550030710940e0141e40d01a4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 135118192 1250 135116942 135116987
    0x10302180f0403030b01090e090a110307030309171608161205030d0b01090803040e150d08070602220602011a010504050117060310050c0a030608010b01090b071a07 72
    0x91001010504048400c035003400040310000380004d01a500140d080b01061510035026903c4000c81d07281003074260340b205256817050070017408100c0c18201e441070200341503028050103465650701030182c500c680076102686e07010326981c0020040c200001d40d407809d030710304002d20001d41d40e01e111512021a01c0010845402c804008a040481000c1107044141c0c0117004602c6c01700c540c20b801008040c0e84040c03904004414800284150040010b0400751985914454031410b04581449160500381e2400b40112000d0340c1d0127001c145440e00740c4e8084c5420031400750f91404890111524100342a0180a45030911030f0082030142c0d0551044000803240512400c440600300015100c0317005034400d0394006103a549401c0f800e04520612035400401c00340031501c600207411402c2042d200110340410400c000828191351441d410b00581d8010b007204070081062844010000308951135902506602c1078000461000f00407003002c10702c2400081240f9007046050082c0001c4c030960030f403044000d524065 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 135119442 1250 135118192 135118219
    0x4150203101701060f1203020a020909010c080108060c03160903020a0e01030201081f09020c0a0602030a0b1c030e0907051b071a03010f090c180303050310090b09150406030602040905010302 83
    0x144180c9058868050004d0b01d0b1710318050642c0103100c2d000d0320840441c0a032035003403401a140d03070f04624015140c00c40049506d20000c28000c6c00080e05074800e038011382c0b103072003484665440d4208407a000341c140e43e0244000340d03054a041d10001d45075070000b50003440000c2c00052409030103c070641624030176a120361246d12030801499032008100711f105075403010040304000900d000c1d07004006e046502402e607034242d0a140c81c0c040032a0004c0351703641015925079498070300038a000b01505441400d501043c2d520010a0345000300102980b50308640a81c0140000c0f62050340641b082c0c038250030881d860041c1e4100c071000100c0c3c542c4c04500c20341102d105520f016040079224001500e0681d07607110b502600c013030724041c51103002e002c040303aa400a02c0b0103100300707a400c1c0c000d168000740a14000d84405543e4103040440070801000c943c07116441c249804410041559600c00941d040003004d0781c90401002c840002034002c0c41290310040c80e42780f0010300042c3c4041aa08054101c900849200c9005030300c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 135120692 1250 135119442 135119489
    0x20a080f1b030a091502010906060803090a05030a0506150616061b020c06120c0f030103030c020906040603020306071101020c0f060a0b061903180218090115050a0e0415020310 77
    0x160303c51400481c03429601804101d02a03101001841c07124030020482010a84600f011211541c0002c059500005010809410120300c117400a15090703000300f0403240e1684500c5c1d2141c4c0040d0113910005181d4440090740d0399418281e0300804000c600081560503540f0300000106400c6081c20b4110901e9100c1104e0a40042003c40c00b501e005080189811102034030041c940c1d400510b035003e070748414000000700544150103940a14880c1d210040c3d003808500410000480042069206504180c001c0c001610041030054001295082060032440035450490181c0103600134900107100d041202030111000041e058054003001108014240d43d00e0103002182c883c3d0040b40c0c11410300b080c0c0140f4071512940c4150264070401c20318100390304855001520240400554882420a00085c002158003c0c403901c2144014003c400c0a201d18010116664121a05c50031078120740e0316000405001901071064060580b600c2c00b150760f85424009001c0b100c9031030042e10b40586c510b081d001c11a10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 135121942 1250 135120692 135120697
    0x31503071a04060e0d05011103010f0b160209190e15060301050c0307080a0605060a1d030c100509040f05070c050f190807260904151206050403020a080f1b03 69
    0xc51101d04180b60074108902503c01c0c0340308508090300000790505400105070b00784110f03c401004801000e03981c1d450f0641104250140c1c6c0c004035092a002c001305800300c0c0320303114008035103981622070003110b07910ba0010301c61b1810301c1c0113010190f038240070402c01c48000c0481c1120401140324142070317803901e4250030705089550803114000ba068040010598441c01905165801602c640d00418410784460208446810554164011030b800d0001e110380180c40c3d840ca03d0f038490b0194020121070050100091225541121000c01e00000003503000190310703190400010190442000d00242c00d06001c001e203100003401d02a00c4901030100d5022340303040b01040c0c900380c0c00f96004e0701c2c40000c102a2110301440d84183d80c100c03400702c0098217404054040640c4c030901c0fa101002c030301d80c031384c0c928009000c00c1d1000c039440418001603800040c840d9000e2114040310035604141d0010340743c2d41c0c61609074030300428100044c1551402152103440b051000c0010034000c0a00f954140d02c00440305a42aa00d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 135123192 1250 135121942 135121979
    0x6240302161103070b12100803180603061503010b0a020c011106040b07031d100c030b03060103081806030a0f140402030c19050a060201060e0105090f130204020f03150307 75
    0x1c100d0078110000b09800c118102c40d00c0000809403400d060740e801c800142c6a0140a030922140312480401c5450030b180d040580c01804c0c00f0b805107145c0000c015003210840503032107000f40714050102c0810840c0e25101501c40b14041e107110030b41e980e540c40300c90010300d940100750040014401c9068821070395218480c803c0c0c16042e9080100510740780c944e01da00113001c4c010700c8a07007099550750a51a030341002507080c41c0304080714400351070211444101c0105650b82110b407002810f050050309107084d10300152050450742c0201507591110040151034003d8500300307584907405200882440340c0e46d800c1c0e610240d1a0a800c150400c0140c000c0407a00e03540110440e00654507401c103034034000d07090401c2d000804803152f2051441d90025203d100082c02c02d00b668010200503991118180a0300080e122004d0140074110740921076454508400c00604800030048401e03107a50146140440d01c6580580d0171050201464a4992814245046c4c24115a6218502c6841041d00004003c0c05400c0e400c001e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 135124442 1250 135123192 135123217
    0x5040e01090209041404123e07080d050a080a0b0a09020d06080f0307060608120a0522030f061d0316170403061d030c0318030a020406240302 62
    0x256864606400000d40010074616040342c2c07594a00200c403082807200c0c134032440c030511181c0d0401c4840e0b60021314100b00c44010b840e018104502185841c2d44d00c3c981c1400c0c080c1c170004000102c00300d0a80160800312554064800c6200b00742c5089040c5410001030034819007107a0b00e5034110707601d00038a5000c0d80d68451102c0c4d04414808000d000111035500181111003d02030b000c1022566035004a1900c1c00e403c1d8070f01b071517410114440081006a002d20b40060507000010441c0341740d0b03107560950b03e11070782d600c181c144000000c070001d240d408803812880c01c12804407003110b400d03035a081201d81c41c000b806048803140c1c6032900d1058442d5443d0302481541148200643c2444110310003d251a411004241c0d01d54400941c031070304040c81c40c00140095481102d01107a81e4800c42c04550007889080e4130b52035150024040780d410080e001080e00d5033303143d184c0c404e42441c041d0311000ca400c204500e18081d40250412801059002240164107480c8030f00c3c03000326244149150703040f0101c1c041e402c1400803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 135125692 1250 135124442 135124469
    0x10150903020d020103020306010507050a05070504110405100507021f02030a090602031603080903160807110306011d0a180317010501030902060909070207150c0b070f0203031b1306051201060504 85
    0x554446d6010f1580000b0604180e840c0c40c601d619124608445004115074640c880242842203003098040d900d00403909124650405040c14000340d00d01c0703500005101084004140d24003903541f08544502c9100e5211154a0240003c1600a460358000d4160801182e035403000016400e2002040300da00f58100140420454201d5804075640900641a20540d00c402c0c480b1180d040102810002c6240c8506002c40c1d492005250100c2040780c1070008a1090700000010400d5403914029440b4030703418584038085036514200400c004041c139070074240407019070003031081c00c040c1c004043c022140010580702560360303a10f9004505444100000135009181840300c0c11890420220f15504409103005a80f0095210040608191005d0301380c0000241200c50582c1402902690300b44c20801d5403070451007011082201079964400500541d09020a10001e20704041244080d0390014040344900840603a031820018826044a402e00d00e182e80e080c070000038403500031401c460131036901c442c0412 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 135126942 1250 135125692 135125719
    0x2a05090f03030c030c011d030307080a0b131b0801090b0a060c1109040f120305011215090c080123091c0302070b040c0e18210c01051015090302 63
    0x188098554030550148000c2c00782d45548507003480a0450782842c1c400000f00c500c2c0c085640300312000d0b642890740302c4c3d800420610086039440312802d40e00a4919a02081c00d4480c0700101d8420310102c0003424582e032030314003081707002e0000007072050071403141340d858007800d0743c036010b007142114681c0304d015500c002c9180040010602a100020015008a594210380c03003810000c1008004c0c101c3d0708840c00c502c038000800811031381c042d000360199050315081203070798104625650740400d6540c02500003000128001e410540310340042c030b030803507120b8000c4070055541d500682c06000c60019041d82000c0c803684a400d1142981900c43c030030540540105240001c2c0c01c0c0c002400114030b004582015004c20102d8049030641c0c6619020314071852700c42184510b0540d21941801002e8403a05000e50002d0601010050006020540c000e459000c00c0038603591584508542c03007801c0c00c10010303508000400180385d198000e0070088819118580c0030901166400300c0c0c0720481408002d501491141760740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 135128192 1250 135126942 135126949
    0xc041514010504030503041202180601050703030e0f01092906030c01230301180f18170d0e0601051212030a0513020418050d050f0d090303020f04092a0509 68
    0x1141030418100580390684a07205d490039588103800849048880104200443c02c0014800760903048c00c441100290410900082c458460070300058109030702e440d03416814800a102c54901110008002c100d103600303910b019012a0381c61041d01c0310510200a0130201d100d00105000e216090080140400710102030040d1841d080d040103050b508a00510842c0c110a2404011406021381e00481841c203440ea001103410b407810040d0041000b400c01944203004c2400b0884114155805503500b144103c5106155001d03002e000c0b40d070070945081c0940750444d104080b071120f050320010b07240400032a441003c080ea81d84046280b410100d50100005040d0143c00d034089900040942c4500780350300440c2d00001e080d210781c5e214420b0500c54101c0700300f007086010403042010000900b0100c0c244464603030f8400035801b034a010aa511034856900d00200f500c241d0494181d02c2c2089440750b00e5a881c2e03e5040010419070034150400a10381c0410040c4c0044141ca01070806682d0740c0700c918040707000050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 135129442 1250 135128192 135128219
    0x503071502150702030403051209100f030b0a0308040503010e1513050703080a111c090b1c110715051005120a080c0309010206060409030e010807090e01090504050c0415 74
    0x490308500680c4254450b110196141034011089980203513240d50840c1841400c00c80c00050306280d41c9400c1180c60305a44070288800c112920700c2c2000148404181000e5000c0d10010f40c08950249101c0c1001c4104840f40c0c0c003a006540701a002040218400007241d9550102e003481c07070042000e031200007911031036026410880d40b81310340305544200c2c0e660350380d180b07854018011040100e8102c61103213030008420410f100910b00c80750b1269205040e9210042d1031081039010b400e04503100043c80003074218202e103420400621000b4100580044074234180e01c07036004170804490507040d2000440c030310801809124041c45101204c4140e0303618180400c0854100c10010341c059005a40c49031010480c09400b801e2182e9a01000c4c65482260740b00080c24404c0c02001e2900c19482c1c2044000800e600111904424ad42030078408802e80344c042d01910499501d9009a40d0884c0020001c5403503203198200c40c1c01345100c2d10481e180303841c480042109030345034100a600e030059144000c001d5590464130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 135130692 1250 135129442 135129479
    0x40303020606120f01050115030b010201140a020a020102040e07050a020f070e01050d02010e180115080126070b07050709060501080f150d0f050c1f0914040f0504230304050307 77
    0x460303441c2c2050b002030074251b4500340c5c03107645419503c0d007074514030f1a00740c001c2d202c0d1248244000c0081020145a103418a1405030010910030f60100c3d80d41001d078000d60456010304032800ba22000327480c000e08020511351096258500602a50100b0181e8030300001d9501c09071031007140505c542d607003020700303001034403004c0e1206174100f0050a0010034240c8441000c0d40c2d00301ca072646010b00541c101201258201d101210f14400c0020940040082440d0750000352002151003e00038211001c481d00c1510f841d1090700000d6416400240c0300d01000400285201216003802050080301d503904010745244808580800710350302d08000042c848d1540c00944643d90000401110030038026850301030791400f17640e02c01c80c0c2650011319003509502c0c00d2000c6600e074008000314214804a0800d000345000260300c103264110380199000782d03640d0b40e245c1081882c100a8041001a40780904011071020314185050b40c4650fa6004040785440010085400340c960240c001c2450a140c8240c9203000b400ea400d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 135131942 1250 135130692 135130729
    0x10207150e040b040f051003020a060c0809090a06030c092003160e010909020705010212130503040608130f1209060e150904020403020909061f1a0d3806040303020606 73
    0x325a00da000261b4440d85c2d0040c0d00d6140307001c1c81d060940c03040c0540b80d4510341001040c41281d418400002d2403e4084607075800045c5c1d07202070f803500d0705e0500c1070140c5095000105550000e8101180904c990791000704007001003c41c03221005254214810307a071001781c1e000f0a00c480d0340d11010160782e004000004840f5010314005551647c3ea18100080b03801000c81100c02c1e94002070015224940c5e00182a00300910a4aa846041032030380da26540e132080b8402d50041c0710300540054903036580506c5e498003c58000818040441c0c01e4905103403071455041500c40498800c2c107021078414419072071016070900241420007068800b03034501d541ca40001d241c159215030208004801030300d540000500440c072507802008241440300140c0812202c3c44050f50b102100b20008019034412603d602c82d04507140344840b0b907100c1080a85c50003400015902e0130301b40500190041c2134010440c010800c6100c55102d00d0854000042080755603c981d00c0043c2c0107030700202c00310300d651030400d404008401085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 135133192 1250 135131942 135131951
    0x30403110706030f0f0213030b18030d0609051e01090b04020705030408280807080a1b0507080f0714060a0c06050c0a0e1008010e0903040e0f0105010207150e040b04 72
    0x1946881c481d500041c00094403990341d013200c5505405603001c420000d200560401f104d00a95803031b000002e1001a1040300103801140f50511409400102200c0038030070f0301d540d1440460f908000c0c1c020303071040d08451440d0200081c81078003035400c0c4420805461030011000e91824035204003030f2010103100b603841a800c01c4041d0010307004000400007894014086d14824461203040184072444803020100320007281214000a207600d0101c550017544404882d03110008030008494078103402e500304813101d40301d10303c2d14240040010170104640044c011039103109003401c1c020352514441d1040d01c2030405041408480c3e49400806404003180d98a40020240c10325110f82e03042e034100303541050801900056450f0b02960049202c03451002c265804050082c12090043c49400e05200e000040d421407000f06100315410300c1141c0c005d1591003000c1241d0b082040405054400038070520340584a4240d0000318064201c3c003065070760344251144201c07100381d6024807025003c074000c020740c4140e55 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 135134442 1250 135133192 135133217
    0x302120a1a060301080d020106060516060f020f0c06100501020c01053f01080d030204030b0f040c050d0302060603100e07030311030f0406030902011710030303020d0b060a120c140906030403 83
    0x200000365000302030050042080b41b0032034074081d00b160002c0d005034080003070030401403100c05250050f2801055006800180110000b6880e200074000c09000ba10801400917503450458000607025008900000410415960307910041e69543c480142240c0400c909114942040188180340b00094504015800c0c0401d81d501401100340c5202c810714400502060052265940400c510f240c1d5400c1e505086280a00b1921081152040188041d40742540c040c002030400c01c0c40c522a4000302400713414a140702c00a464040e45a440480e41c06000344070340d000031128070700140903000e008081980541241810350b10102c03403400c400540110184403c104001c1580502401070005104554000a050f2030074800180341c086000600024911308800340691840c050140740e040380d600d4200169a00300340040e170b030082c04000c99019800040803d107540d8450b004955580301c4c0d24031400030811046244003c0d141a0b421034540c20181c00240701c0d041103410b05000031900709020b400d007200401c29 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 135135692 1250 135134442 135134449
    0x2090613020c0a05010c090302060301090b030109060e0a02091506032d040609021c031b1106030c0406260609041401050414010c02010506032d0a03030204050a05010302120a1a 77
    0x44106041640d03c60007465051003c28031582c039002150345400c2c1181855600028243d010600400c0900c60742d80f0000412030303409601907445950700840c24095150554034040c0c8640c040d4405a008098000002d54401d601d0301800d0040c510040085040d6254040341c05240440c110084801140741d030a244203050116151780d129038072558012401c602684140b0032000200c00000d443e02000d505c0d450002908014100c503d5508080f2103d61000b0900b00b1018503503d981c00590030800003c14048115511802401500e078a5210911071100b206071030714080e00064011824814500041506c5180c02542c890704903004428010481c0401e03420142165015034007200d0f1400f80c1e4409400164082c080d074500c040c1680000c1205285c12000710351204010f5400784005c4851485d281c44008140080e0394402e2a10002c941c0c560449140185c001c2d401401500d2180048802c0028158802e00846000b1851425a6103407911401c13120300280401c1d04002c0e10f607070380712030a80e6020344 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 135136942 1250 135135692 135135697
    0x30c020f0c18060d1a010614180907140301030b010807060f12020901090915051203090d140a05100b010e0f1c0213020c0a1e03020d050a021c0309110303160209061302 73
    0xb821383c85e400e81d103514002000d04000303001d08084a00120070f00c503440259000010a00350840300b901c0511041c1d80e40e1100719013402e84503d40040c0c07040c0120012080c13103a4030f1080350680f07400c5000c8484091715054255207141248150000003000d00d00e5003490b00020350090140c074041810f100344210f031a0b540100541d50382c000103410000842000300322a1070101c0700190898140c0024515010b48040440d0025100c400042c00c0a0342c0061480d0190004004006001d5003040680f80085948580c81307010f05800d100c0c0701d00040c0c1c0e851303c5541c18501032402d48084000200394800603650503101854180c8118016070748100c040c00e1150091210340020b00d4030b0010500a4801c4190038503011200c4a20080d40b800440610700c0da20f000640c0010b43c010164aa50400303548820140c4006c900d05a100d58200728000d8407004803044554041d0004100340d0300c02c2c0e00c8200c480c01c0440c1031583e240200c0c09024124051080c144026040135951590000c60240c0340f90030030174041c50007400b80e0b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 135138192 1250 135136942 135136973
    0x90206040603023703050c160308180303010b030f0402030f03030a0b090108030a0e1201091a0708071103030604110c1516050705030a0305070c020a06030c020f0c18060d 74
    0x30743c0006021441c00d0030b0641060b00d0749080e1080309803042099200d401030514501920052550710408550072000b014203803120030000c48040714405000e858000d00d00d61046c0d071444012030380704a140e4407000002c0309507030607156410b0783c0ca0300710ba850b0081c1000c904000b400a0341c0502400e6034084040c0300a00c021032140c080604041003030030840c0288080315005074810f81041d002400300300c4485030b004190f400444822a4540892101204080d004184a0200400041d4844407054007405580103103482650a5100e0a1203540c48502c282c804900c2140d003031000c3c1c1c104000007481031070141d210314043e10340b101905080088002c0541c1c0742500340030a00b01180074860401800c043da0316101200b1541034940b0509107da10b50b111940c03402801d840b90b050589460024030305510428550504076001070050415903610312001d80148003000751000140a1941486100440001e2584c1440805000e51045040ca1000d503e44810090a659444410050341c140441c0032a058110380f0f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 135139442 1250 135138192 135138197
    0x6010c020d12020d0e10050f040f030b06040c2d09170105150d030203031909021315060f05030a0f0e0a0302010b011d09130606081504060b0307030c09020d0902060406 73
    0x542d040008040c1c5048050342407002003000d9840180080d841c2c00034203000c04089030400d90340399802c420f0112001c1c050f5400c040350a402d06040001440720303480c2034034000d00d001c1d2420031820940c0312041794201188a80d9403011002c0c0d000c480050820340060701d4a900300d61a100d07005903280c507020b5505403d00c3c0034035540e07a03448005000e40c100310b05160140c2c094003103585d102c4001155801030740320702000b003c03800805001c800303e8078030502c19000b40e1212036004100d11000420309038180c0c01004106e080c52014120200c001c5422030103085181c680100d9526174074250743e070b0348050401070142850028009031700c8210640c41e0131410080500c01c24441e400101c1c1c0c080904000401c641c0d011608800083d1003092042180e449494549030030001d030010780c003000442414194081c1065511407a01d610800301e03541c4607004002c1c4e0309806148200310511450b0311540c201603441c1101c0c007001c0c0c040e07030965170104000d4400340c0c0204000c079500b500101c1d030400aa0001102170f0080d81c132036000b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 135140692 1250 135139442 135139463
    0x4060c0b01060215220c0e0f060405090a060515040507050319050105011b03020c031204030c080d080601051b1204081c05180a0302120109030f0503160806010c020d 72
    0x304034250032041c0c00b5111510041a6002c840440c9071000346019112949103000011480451071072011001011360700041a111400d54504410000308800c0303552004a04e07902000c20450b2400e4018a4051000300300102014805a1141e1008000282200d4505042072001400350b8031a4081e05200b0686034803141c0d05d900d01813501c01254010400132840c0d032850200184141c2e0f810400c1c801c00c1c2c105400182030782041616060340b50540d00e81c60540d1600c20514010340c000c129400400a1300c2c445e2403045085070790760020715680d60044c040c803000301c0e03013400004e03245503c11009003592a06d0703094000785c0100f20422442c1009002a40c0c04684e0f100094107000390007003000311025074080d9100169084e180b0700001000c9024001602d40c4150b9995003e440c60342d84c01580901035600102001d52005000110340e0090241d0350040300072405c44001100924095030990b803103450049001c0c03c8030318045208032000e030740081a8070f041c44038252000002d41c4451154a85541c4120b14050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 135141942 1250 135140692 135140717
    0xf0b0603070525050c10090602150a020c12030604060504021c11070606030302060402041409060402100302090a1503050106020316020d0303060305030c070f1a0415030603080f030a0b040504240e01020406 89
    0xc10020404004c8141f101d001d0042010660001e1880c4100f145c40280020079241e081000001c1d1003541003140c401c1c883d20b000c3c10240000c030b5000b9070080104907401c0054580e503005005c245e018500c00d051842c00c011207440c440140c0707030b04140340d03910000003002d180482c40e590b400c0c104d03441e54200354010381c4450301700021400c242c1704200b010031740d00c0c075034a1440c9007036100160b455a0040c00280034024410343c0500c491f020f0b4056442c443d9004041c0e001c800d0b1a00d00c1c1820010790601c1080000b42800000144c2c02d00100c21640340a004405000c0e031481d01e40c09000c082d907081d02c2c08904245c0c0d01c13000000070a80034400b800340c481500000d06510783c80c000c134940c00303041c841c0c2103048244070201c0c01e1f031041c0e1491011201221032210051001d83d0344244290004c0c60302d580b01801d04640080e0040c40300021100651003602c440c5400c100522141082c00112401194010051014100303081120401181000c0703240c43c03289004514a000300d00b001d42a270300698083c0000c540100c00d540c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 135143192 1250 135141942 135141949
    0x1202010212100e06011d03012d0b15071b0b1201210b0a150803040608100f06030509070f0803180609060910090b03190f0b0603070525050c 61
    0x940c201c140ca41c05451103c1c00d0031034181000307101401840c180641e41c811001c820858401c4891405c100500030800d20009566030105001e04582c0741c0c45d1031100144c101802c850600c190b142400010b001003051140001d0f8400d1568440b403c00e9a000b03218288c906080c49100d0003a4014281030b40e01c2d20b84482c544403000801000c1a0402d004c04401d003205034900c400c00ca880c0030740c00354100002e40c4154980e050000018022a40c1c030f414100d50080004c2041c01c07000005100300c031801e41d00c0078810b0b541c4200081188443e40520807104507800f43c2002440e110f9000300c0d1b08200d65a0a44002c2583c0b04400e91540700642d0010070103410100c1c0e513001665150a071901c02080a65080b40780c42001030003d001d6124085003e44608844109100814401d005ea28003602d4400c088656a08100c00c0701c420083d500036000c04801d09050010030220641e00545914000281c1040e08689808100791513030b404c41d0400c208820f144034203031690700003104c00243d9150f001e4070150881d00481d4061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 135144442 1250 135143192 135143227
    0x14030d1a03071a0906090a0603020a023007050316050d030b0d0b1303140a0804020f030c013f0606081e04060515060c060117010908090405090a12020102 67
    0x10315100390031088041202d0691500241d20764a56801c640340d4802c4480c00143e9180160b500f0704d600401490008500c0540543c01400c0c1212140c00f103d540b076401c0e010082f81b030b10101c01509541c0d510050540006181078000c2c1c101b03144140c00780c074107000c40071400c40354480e007201c42a9529031000e0b8041c07106d01c6c0c044c42003043c10641929010003a405da9195044409030281002a88030000285c000916200f0740c401c00304403d4803031038260703108007508005182c80b60a55003644654284602e20a05240000b0007200428068586000c0b001940e508400c807421400c54503c1480d9802c403101148029985408051080c0e2200000781e1500b880c10040500000a066541240300b0300840c01c64806c0400f51154040d90004001ca45a680c0040c0c001c1a11000b8800c242c101901264402c083c4201150a50598092900d01c0401c4056040c08038241c03105445c4c040c00e440e00400c62180c0030704090700b106038441023610440d03002c003c8a55500001c00d147c50581da0041c3d40c041219080040501d14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 135145692 1250 135144442 135144491
    0x2202121632100c051b040c0f0804021e1203030108010c020d02030d020a0e090108030304200f1c0f080a0807090e130c09050c0c06060d1e14030d 63
    0x408076002141141801d505600803084a10030302d01000c10b0b050350362103180c01d014040e40c8101a031703020340c2c614280403000d20090210341b8800e0303080c00c110480061240c40c40d4020700c440343c0e4a080d40c68842d6000d120303e039442030040c0281c0807824480503100340c88108200350041e800e10300035642c0f0740c0350074085801c40f503e02c858141190401070348900c4040e400810760b104181c0e04071b40180e40e4082014162031800c03500300240c4c1c0014080c800010500e0707010001c0d5104900491041e203010010300c048405503010f000d1032650040c0d0300941402d140c02c0c142d840c0301d0040d50740148000191060f45800c0036101203000110b44402d80014450510342c3d120020582101140c14803040e02814080c840c050752600925030003a410707a12102c0c0e02031000c1d2159010041040200810041c20440349401341c951101d074050a00d8844c0d06c001c90071074108601d48c2c01e80340e508986504045001e0501d80d40d100140c8460a60310b01003810200030304d840303080c0001c1003030100d1010009030495403850008103a081c00c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 135146942 1250 135145692 135145739
    0xa080f060604060809030409060308041508071e0203090d110118060903031b0c06030608070f180209060c06010f0501110105040302120a020111070b01030b0f22021216 73
    0x14203006280d2101420340d42075642500f01518240e80360b924a0f4a0750290f130744200009818a00c00100380882c0400400c299102d2000b80d0114410b441c40550f110203041c0da2200024008a040305510301151000c020140c0162041d42c0c80d02008000094500d00c884209848800c81e4403402505580c11007254042980b92a6a1285071407400e940580400c10600c40941405040c0150305105081c0b001e0801241d540400401e00c3c5980f200001002000640554019880741001c045941019880e0020840300031a00c076a100300740500100c4040e400c4050f566410078014848035102c45030a100941c06015064401c03aa6585442d00050a0006030b4000c03c24a034035103004d0002080e03002c904420007644456241c1c2d80c0d8141030108070300505480c00d43d880c841901140e034604004090401504890288210300019201c4c1d521400c0c00340780954104580d4a17000087c24011454541049051400200785040100340401c6007030808240840701c4184100315032091141d00da030341c000d8400c903e1294 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 135148192 1250 135146942 135146971
    0x150f01050102070617100e100609050609030703020f03070e04060e06010b0306031b060c07060908010614010801030f06020f04032303041a091324060e0904150f050c0a08 74
    0x44c041c0c031003aa04201c1142030114800052504216884282c005182a907103810703d03480c002d0008031121013a030055100140b10703031400041601c0e1003015100e240c440103001d810418915403c0000380f9040e5452290075004d5140005103010b00e010590b807003a03000d140085001d0301030308085810001d05800200c022201030040c0b0100340c400151801e00b0a6106c00155074100c00000092614003070030801e41f00f144a001070108000e035101d0b810004070340e160b5001340b0095884048410700e00c910510200d00003400c440041004c80c80c1d4081c0841e429020f0040103142c071003c88003039050341d405078005445000415001041842c1207040740601201d2040155042900b48032941c05080603c440d82c25001384045080003441d0b82c0d50001d001112a0050700f00070b41d511241c1c0a81d480000c042c041a1886180d050000c0d1303807409405001c1102c403005048441c01e030b4450340d8081440356040c4035005281d0303843c0d415203401561f41c0315113802045c0c040040f0303845150845004120903002400d20011a244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 135149442 1250 135148192 135148199
    0x50a060c050a210902040e01020a0201060f0815070c05032b0501050913030e090403080103020102070b07050606270903031008030405030c0607050a06150513050712110c150f0105010207 81
    0x100340c2030b4500c200807640d02c5003c10000c168480143c00540d6001e54040d152648011040e4015802003040b10720300e40082c4042d6179075034070400310800a4403030b2181c3c0b500010490708030840840041c0750310100a0410001e47c08541d160207240d5000004040c2504a40071401064006e404800c1c0c1e2450300c2c401d10034050b540c18030b40854103528000d8a031036041c118a040c6402014010810300c0fa1b0150040c00718099860303d800c0041c0000400e1000781c2c09401a04008200c0c150030004a4049a03000b1008140b641c07106410300a0000480c00d003608410201c049070010410220501c2d0301034010100110340703c0c1089465030842d041b0345c0d4094102d943c0204001c06c01038030b01080c100400c003021a50141c9848140c00c100741446440c1d40003e003607a00e410b00c0b1a0b040180c0c27105000c1542c405450302c01c4905510340301c10b03003154026624007020841500e0f10510303481c40c540020310300b0792240c051542400b08010800d442c1c07000c50602c844007500c5079001c0110707481070780560074010300e0b00748014100c3c2c40c42d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 135150692 1250 135149442 135149447
    0x2e060b03040312050601030902040f0f141e040f02030d0e03010518060a1802030d050a030b010e031504080f040e1803040605030403080c120a0207020306100f06180503030403050a060c050a 82
    0x2610109090f040d91120001076490b03003c1e0b488041b0351500034100340012008040f00500078120000f0000071b0520b041100c03140c2003103d00d9100d00c2480003098441130313860040582044501c0080007240c64003540d066400058805000d002c203400c080e41c480d0080020218101801d40d440109641e000d048074501004400c0c0d40010540e400415140000401c01201c060b07c071120090010080d4040c4103480380c50341083d901000a00210b83c036980e04000001c5220011220384100c1e440389940b65001003c01c008050101c4280b640191140054a15101018000b200c040c0c2090740000f042410080401038461b102d1503040b410203414602441c605420100040d0071400f0142000e002c0001c420002070301c0c5600740046a44203c000411250903251140040c0060750150400320b00a00030a800705101c0500004078106450349074035024407041c14000c08843c070380a8120a0388115055060005064509000400186000760080c00d600460f50404100f500c07030381750804007044000c0080345801c5a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 135151942 1250 135150692 135150707
    0x8040605042f090c0903031e042601050604020f030a0f09020909010b1816180807140f0a060203030a0906020732120306040906020d0f1b0203030402030a060207052e060b030403 77
    0x841c4541d142048d1002019007114038022034201160310b5020114070349040e920b9081e040c07101010344d4003d0050342e6807031061005174003510102d042e00080500114640f2031990700503100800d50307400c00190760030780d40c0c001907020401650703a900d59954608050140d81049162070546034a2696442090700744004500e0505c00c0760b01400e0108903c401000900c4951184500010f0070300f030341192402c07600c031000e0303600c010165039030a072088110701d400c14410704240701c03d40115010368010b5401c603502d200b00311003d00f400b4102120142d0b404c110751400241c0000c00c0000402280c3c004454450320401411030340c42c4001c03035106007680548000d900a5905d0b101300d0364060b20a680110348800c084c500346000c3c1c012010360480385411301410040c40b24140d400002034040505025580110b06031050f80c0300c0c0b0054501940542201c4c20f03060125003a82c004102840c803032011134904043d640039040700c05050100941a9840310380d803000110503e8003503140509041c8600c00c1c41c50400307036005481130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 135153192 1250 135151942 135151957
    0x7170d030506030a0f060f0c1106071d090406020a030c11060402060a1115060f0109030f06200d1506032a030b0303181008010608040605042f090c090303 67
    0x584610000b900303501c0600c030009400f80d0182d110302d00d405252815034041d0900c0c00c2c0100300c0d58078044a410413503208024802903521580050b007280d13114031100326200c545440180c0c642c4481030420b0901c07900c03544041031043c2c0c01250010789429000074010706a030307501a0b07040c3c200407000c06094082c100214000340c100b0750413103e0640d0384442800980c1e07001101d40c17903850b080c010400d11a0021800c980114405c03402200c4402d9030440100040d6001c45140c0001740c04a041c40903860300207115580124540035804200042d00e0b0740c59940980b00d5031003411444013550b2034100e0301705000f40d043c0644010f4200e504080c046c00e90700000f025004004140145040c80110b030181140b14000d502c040038490016042e0f0341d880341c140d0b0500d140100c10107012409803a1510030201071031300c40d640c1c242c148da116075104400c5031a19141c0750040c1c071003d001030b150b0400c001c20848a45010709a00c501c9203446030300050107102c5003000c00400100050240c5d042d10020041202e5a03500802160b100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 135154442 1250 135153192 135153197
    0x20408120c1504051c18091107080a02070603050a0c0c020121060b090325051216030b090c010807022a06070b1609030203071406161407170d 62
    0x81c1d1032942140e924041d2514010b0850314a15001d000130f019012603180300d0309601002e4a40c0001409078221601080c591070300b400306c0c901c107409000f03441040d0400c041c0e60286907903060a01c403003500c8482e0682d01c02c11124000d03034042c0700304102d103540601900740c0c480300c030010412000140700400341c030b0150141802070401030301c3c039070700c1d040c5030703d403541e120080c1000e82e108100c42c0c3d44400e0348102c4c03680030319a028420300c550b400000500c0c90400c00030517904e0000c11444501494881401100f5440d404d1900013030141c001c0e4156981d030b901c03031a03100035805a01424118146450aa810b0200c0308034000d04200c0501c7c00c01508070380008981140c41c0d0b10078460421490b260198000d030116884030298024000601c0c0824091040ca90032302508400045000c0c2041c603100584070441a84002900754101c0b0070100480e000124416070310881c00340c400ca05e4804d10003060800b03021405002c880a03a401d411201c400c0c0000c02c90000500345501d01c81110700042041140d80751019001c81e003c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 135155692 1250 135154442 135154447
    0x3030906090501050406061d04050a02060901120f0516030e0705010e030f0a140609061302042304030306030c080106180f0e03030907050306070f050d0522060203160302040812 77
    0x10402030358016184590820020803c2d82002c1c035003540904490b00c2030403810b21900040030f14100414160320301480d4401c00410130b01c1010341c240002600302d990100c2c14051841c0310301c0c4182c0340901030300a41020300710b00061145040011803509028120381e850406142c031411103071014000414034103a034024203200080001c09030001e441c201140b000c140007402030607500000c11483c60780c204014441da10640d04d00303507110685250303109412030340e403810300c86907280203405810190700080718490b0fa188407042c403085400d0180c2078404d0a0307400718002aa0b8400420601c40c3c030f0582c0300e001e00047c2000740141844c10344450441c0c040307100b02c13000f105d40d50300b01201885e611368007842116040e1001da9032a0f103058406107841c0c401c81e201d400d0080c020240020f825074451004502c903004103886027824140fa403200c0400805000345121380380200c3c3c0c0c0362808000541406082d040340326550150b82c038034100350804800201d92840700103150040c0300510205c070000c01c240c0e003003e030001c0c0300b9038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 135156942 1250 135155692 135155711
    0x120106020a02032a0103051923130b0106080402010512070203030a1407021209040f090305120a0603120503040201020c13290607080a120609050603010e06060102060714090406080304180e0a0303 85
    0x907604131005600e01c107141007080f00309a852554484510451880001166a00cad0440400302860702c10008100d55440c01c01444594090615550030030300600d0228205144030346080d590600a6036a0b202682c0007001f006010341082c002c00c0c608000c01350080c0c00710b0401c0030000c3e41d98040d203111605190401b0903000c0b41902c07558400c0c00b0311050364a042c0143c5850b414050401d522070141e00d040c1d07140740c40004088d00107500600084950008041c0e5034582000001c40715500040c0040b411409419541440c5569058030084448081e070030014032600c01a40180910741c011401804c91204d0052149440c2d8071902a500d140e6001014183e03600e0700b48004407000c0c8041848000d4040c0b070300d030004c00c41c035407581d2245101e172800764000c0200079400d846860303a03040210340b01070069014400082030b541c07180d902c040d01d502900c0d50350340c2003c28000010302038032000c1c0c00198080d80046420840c0300540a034210450300d80220405c405440341100a03180d2400e40d0000d828580c481c03c910 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 135158192 1250 135156942 135156961
    0x62b1a0f060c10050117010612020108060f10081501090f05010c050f03030c0d05010b13090e030c030d05220c0905060f030d030c030c0e0a030f0206120106020a02032a010305 76
    0x11003082e2604000c0c1e843c03500040a2200080c20207006058130700c810344105e89540c4d881445a50b05880100000c2c500da503105500449a540c00106a00d4000358910103244440d201e08407490b50000e016101d411440c0340610b82013154846c0f41c00320b2410000c500030104003005503601ca81c01984e9003032a05000007284c50901916020a40304050f413940b10000810142c0c00007100584903070000400c091100d6685c0b4061007440d80124010b032581d8080500b810403540403140e02c1041003001c6a42600d082c141e040710355134250341040040c044920b4440e4104244040c40d4020505503411a000448030700e200b03509d50701d41c6010030b0700a42d040580c0e1180403800c65565403c400000c032100600311403244441c4034005015202103480e4102107801c05414514260040110b014801009404e45041e1407840d190b581005020b1041640c10520402044a500c0a40c04d0b4041c060b082640040018440500c14946808003a440c0c003031080940d9181040d1328403228007141d00d0700009180c0801d081d141c0800c072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 135159442 1250 135158192 135158197
    0x1b17070201020705070f050102060a0c020c1207051810081c03180804080a05060109020c0d12091b060e03030306060a0c02010e0907030c0909140408030a0b062b1a0f06 73
    0x5001340c070944000090403a107144c024425642c0c2039080e02c0164488541d07c3d0700795084a1400000358200e441040c000741080a041c2024101d0507040302c00455842010502e800e02440c0c003200303030744100b40402495a04001c2c851000b4104880100850a4000380242110070540c0b8000200754032843c0308140360519110840b0b540c0e0300885107640da01e9944100c107644403480542264207024140c00003ca00708a031003520780082840002d01102031003180200c640c1900581c0e00c06986603038403d0040484e003c4074140c02d40b224100320850880d0300700070002e04666681c0a02c0381c1302c0c0e4020020031070070b0340b034560030b44404154505103c1110703d118070040e44c44e02d0707500d821680c0081d0024200700c101541504440303500d80c91520b0f8500815124241c1c0c8041d035441601007844c0388415004580040e90301c10046502c083d07070100008103104220000782c2140d10004040d50040011011051007004407090201300c0440b00404101502c86c440e16021400318000815101e40101130704848141c494404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 135160692 1250 135159442 135159457
    0x90c07060603080f0c01051311060c160602010c18120204180b070e0f0105040302060301031112010207030203040501090b03090c0f0f18041101080c0d0c031e0f1b1707020102 76
    0x149a00c2d4582101300c0307070903a080f142505006600b06404a525401c1b5045925035007504038524101c0c02c00380c7c0007404250781c84040c40722510f00c50072140d244501991951600502415030011910782c0311244014000d104076401c0612070240d241d001c22600e2107208031800b0040c2d05490208950040003404078811501e01d071b019011200b000d0420240940c0000200d008040c203c0c2d40041d03040c01d001c01100c7ca4001d07404000d40203201080180040380307030704140b10110300c8014072060300400034680c4039003642c002a00c1200075a0011170b081c0115a000081180900f8009003502c5c2149000341c0d116a6416011130481d01840b0700040c940744946410004909482c00548217200050940003240c00c041000c0350140c0e64180d0030b4010400e60b40c4110380c0340b0b0240003005440d60030608100440401400042c1814040c541e0310049600701e40143c40c00091401402800060842000c4641e078068404107107580b5000000751a066001c107030020040000481211004910340d0344881c030507402845240c2c3e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 135161942 1250 135160692 135160703
    0x1703070314071203050405060106111203090718060815070c060f0b040216021c0510050705130801020c0106050303040f090b0609030312090d05160807020d0b07020a0201021506090c07060603 83
    0x1d80703100ca003601500542c6c0250310450840b94907a80e00c05080754100703400c60040701e01d45c01010052102400240c040d48d002042035040e25040b9541e42403811000038400c50860071540c441008000c04002840030501c020780105071005141b400080040c0303000c4408200419403130b03650446589407441540805400313203002c0c004650350003240c084604c00c82c0c24020100d1141c01c41c2070304100c14441804a141c10036a00c08004d20454031381603102000b80c000101a502042824080100c10700801c038001c200401d0440300041c1e60b0511051020b003920140c1d00241e0003540104010000039440308201c1c0100c500002c000180058150000361045c45400704040d85440081a6a03080f500740c10021806a103520040b41d8108046080c241d4150060303907800a0f500c101400040085440400100f884030700c010185100301c00b0300c0e0394007440620190761410040c1d0200346210110751b010004103840c0402c401c07040001b8a0b142e00051074103e8024881100b104d004203030207007080000d411074001746a000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 135163192 1250 135161942 135161963
    0x412031106190f0b151b0607091d1902220b04060912020307120303020d1401180504120c05070b07050a020406140904080f070605010f0e01170307031407 67
    0x21407000081070010700c02d1482036240048404144201d4031801380008005880100d86068240c104009504090607071180b400140900042401052200610820044c1c486c000c7c03d506009882c42c448400e001200002e44c1d5607824810601461071800c200140003140c0903030303106100c680030310380c1d061080920741100002603401b007000340c0001e01800980d0819520382100641e501c04013400240300001c06901600036440900403055400c182c02449130080c18058540404c07004200f0888505801401c0c0382e40350000140039090034000020003640070110103100d14141358aa2482d102440c205410622620b1700141081203801c2c0483c90051003105020350305d981c864149141c442c1c1480108a1141c0d1805a000c44d0102000d100100f031004040c00400066407141c2e03520750703a030340510040448180144240400074078980a450301826442e6210351900b80340000b03905032280103030485201303400380040d48004050b000054654854041c078003101c88a10050f042a8a885826005800002032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 135164442 1250 135163192 135163201
    0x30507031203050c04060e0409062c0120030109050912040e091603110f011202040f080622030e061306030b10031a120106090e0d0f020c060412031106 66
    0x1401c444006221603880074010360343d82d00101c21a6100d107000b44008660071a00304010303400c0541c01110b100788101c000059041e13454840c0400c00c0c074040310342d00040c0601c403040c0e02c1280e000e0081c400c014000c0b11002c10440c50311110b144060105008400c081a610340003e40307107140c10010700d0580e200101015640d03075150000300b040f8110440e00c9041c18860a24061003c090046400c2e08076600a9016803e0b10900020050071180380180c00c0d041003140003071002030404505c001c000500703078032040b424107918014200d418a080140000710f5289036111400c1244000f003e40383c00d160b498a003103d07e200e80b00000a01d28062224001a034004500e004038015806034082410841b0807a00741c0d9262000260440c103030744c0c68402e030480d00700d00c2020180041c20700740424103061008000120311991a4203070b29040382d80008455280f9400400c0c0d03504c1480e000038541880448501c09841d20381203e2000c00c2e1540700c1c43c82440d01400c43c440e18802814800d90030004c1251a84007030329001c2c00d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 135165692 1250 135164442 135164453
    0x60c0a02120a0606150c030f020a0804060c0605150913030c1505010806060a0807060e03030405030d2003090d0f030e090405030903010f02040e1305121611180f070903050703 76
    0x11540c00884003113240c001e010035080c40000142d4031015042d95850354004031035404a86a10b84010700303409501c2407104040c001004807010340b010b012195030314034503000181421003d5030800303031800b6000c00300c1564024241c1c890006803a8003c91203550620308510500c2c088030262050f0350050076500d072030700314072581101c150000e40c121a82201100c041b40c8400d410080211100e00c102903603070b44100010840c0d1703401100502500e240c014280ca040c903075248042824059441040000968614030100301c111801000c1400185c4035401141000d04000105000054003500078042280f003440000415110300c0c0381c1038a0a07005803a44000e401c0502e003081e901d0308200b61852007942004c0d10060340e58902d100765011101c00038000074044c4c480411520070411081c5003601d09004628081c5c201c0b2801d07100400250191a01201c0b2141c468280010615108100140b162a030022281c00c4c460f00011400c2c0c20980d0402141059110041e0a44e05600300368001409801070b0b00001040c0607 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 135166942 1250 135165692 135165703
    0x702150915010503060f04110a0306020408010608160b090d06020f07030804030e010e180a02040308030903091009230f0a06030e010606020106050303270409141515060c0a0212 77
    0xc0914540a120b980340c00806840316000c49411031b01090800029020030148a080b091090340641385141d2582c603501d503002640c1c0240c01c0100d250f0f456060030000c0f20820049c203801ca117183c05d00d0381c40c09810306001c94030078032036060303600c1c401c8a100c803100302403000940c12a544541071468860741c0358100d180141101d10f04072000c2d00880c1400b00c56200ba5401580b8109a101004005405410700840d103d003031a44090105014150309010110009036203400543c016039400700259200d0fa134160800c080b8036600c11451b001c000b0900302c06c1200304403200e00700c402d0b27640140b07070100640e51000100f0907400c41c4c2c0c401e141c0d000781d6182000400341d4055200c000c0e4482014000e00105407030700300603400d80705c1030b01c9101e415500410001e420000c00854a803041510151140d0391b0301d1048002038156180101d0984201030b82882e0840e8840c0200710b900640301611036104c1c7c00f49407007160295803101800b03c0e00d00448000a07126a0181d042c41110071032a8010614400500001c08947d941c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 135168192 1250 135166942 135166963
    0x1404060b04020c070b070f1b0e060607080a0c0515010b0723030301050105030a091211060a0c0f210f0501180b091518070f020706030203060d080307021509 68
    0x492500c04484003904041c021503a048204100412803035141564000d0160301006056074031002d209601000107580d121a13503a000300007103950300150f09041c83c039680707150081c7c6503d00c2100c0421540d1300254450007660300e1980070342007400b80c00300c0074100b403828070700401d149000d40e101c0c400000c59884541d60181852034010f00c03440b090051600b241036085050151b90480950080c40100465886000250b070300c40c0001c1c00100d88806165211110800740750320f9400401c804107944031241800304906a0f105160719030500c140d0617a4071000e40b86200c50700d02c0104103d000c0081c0c892203a44c07903040c0c2c03107c1800038000f00003105510300700b203000300020f00a45000d411b0180c051120002980503405110400400303044080d2109c9241c0013100031640c072540c0d0840c141c1401c0311075030916100c0c1244126040d84500140b0458488020304208160f04610103061040c42400311320f46a00142c03202556100c0c5010340d5070340790704c04160b00e401e0808520340700018555082000403240800d0040300c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 135169442 1250 135168192 135168203
    0x20a0914120d110f1f1808030103060204060305061f05090102010e1c02011b0212030a380a0f17010e0a03020304060212070b1308160b010512030304030903030809010f1404 75
    0x403041980c01c51611411950b080400324000d0000d045010750751640030041c61b18080b02d0240c03c190050703880d0f1899400c241d0040e100658042000c001094040c013510b64014000c079a40411440712144480ba02074859a80c00304214001c02c910100d07074004d501801644080b0700c00c0350110909084120040407000c02144010750a05c140203201300c00e40050084c42c2482e54010703240b5203411003008401500f0013040104115224904010040e02901091458295074954004403c08a50300700007000c0b1000320345409901507003000c0004108011685064641078141c485420109034051409031a40741640f030340501400081c0010150000003c104075032894094403005604106005442d01030034101404101c030f4600014040400c0b682d0118403940b1507503a040c109101300344120a208442403048800b0f1141c1801030083e4982401111814402e5000039840c1d0300d41030380d0080008889110050500100344003040403e807080d0050180c4c9624214100050210310313941c10084c84041d20705640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 135170692 1250 135169442 135169453
    0x3050c13050412080402130e01150e090c1905031509071d0601030c02070f06120608010501080c1207031707110108010b19090f08010618020a0914120d11 67
    0x18103205802200c0c480c0e0380040306205200b81d032103415943c0c208000c1040741c0c050030000491125002078030510050140e0000000740c01d9580185840400d031480d046014001d0100041100c45000040c842d000c44100b52131603228013002d0031180c01d11400ca60841c1d9498003450030001d009031104501c11388281aa1000c40b03002d1035031346070301d013940c40000c50b0612a030100b1000040c00d1540a034000302d2500055204650406591700c81a9054020f15002400000c080310b080c4004001c83d0f000f801c016020316402000300354500701140740d40d0030800701c4481c001c0302c8c034650400c44e1100c240710b04001180c00c20f6502198800d00180105241c0c013100d07049401d80c4a207001c0c6800c5522034031610b4103032450001824034125402d14581c105070005e540400402a06100200d4441c10b81e51180000303280000001c1540d82c10400704030044070f6028401c1211307501c1804102e03c0c0baa4001003840840d103043c004854121150004100c800c10340080600306031044207400d091b5a5403101c0704501c840d00c108203950 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 135171942 1250 135170692 135170719
    0x301080c090a0216080a020f0114010510081003022107080d0813050601060503190e01022511040f0603120806090105101e030e0a0605040506070e06030403110f030403050c 75
    0x1080340500281c0d00403241600143c4d02c009110380d80100316040d400d004a5240c000e0000a881c255040307a1802d2115400880c010045030608100300c0070300e01001d00f851001071800c03d400780786601003031001902c42c10003041075000208100c100d00048150746000d89031915140c07405c2035075510300503007804000f540c0c150010b40c00e00e2110f6111003020364407102606141e40717410001c55081c0c102034000341554001003403200340144039118058400381040300250300c80710100381c15030350751000a0240c01962210841c00c00014103004210584240440f000034541022941c520010040c0740c0000f0002d248421b52070440c10342000105110b083c0445854034240c0c0c82d0303404d10603029032220080010940d03044da40384501c0948604000980d041e4500065488200a1041d1030144100010b46d5130613a16810310003403080c01c1c44400e600c40c816081c10b0140481c064082102031000810150030800d0102c8030410040d400c1c8200e54400e1800c0c0100c07030b1203503142c0c10500d071602411000030f84615403040c4140d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 135173192 1250 135171942 135171961
    0x9030503030a02031b090105120c1908100609080307120309120509040b1c03120e031201080114100504050601020a0222061203090509091006060906030510080607051b030301080c09 79
    0x80d044010182e68881c14949c0314180f403428904050040c21407e1020300030040c03102842800c0c21380040c402d5071070030030600300860b40401c007401a412000810030500000d00a00e90004101e07891561f12040001e680100248100c000740a480e10003003081d02c00c4074000410b50f80c0b0501410701d20b40308840810054850300b04100a0700e0f4014208810910b03058607902c0400d01505504c07002d82c21681001c50164010f400480c2180e200c04580c1200c074052200512425109109441088410001030314003070500d910103201e000c241c0e00c6482d120395192000518203902c00d004409050741d01910031401c0d00801c4444089403514901e441e0300b0309182003000240f120303800f0441c40b072a036007503103511440d80e00384824816018001802d0302c1491051102a640c0c00d9464841c04000300190341e11690342d18144100103080c0e035806480442c110380b000200f41302d0081c001c14074940000440c01d1907665580800e81540054101d860035074540e01011000140ba59804950003203400421a80004240c0d01da4402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 135174442 1250 135173192 135173197
    0x11120301031b0e1f080a050105071b0f0b09160b0a02010c0e0d0f0c03080c07060f05070c06120f09350706020a03020702060705010c080907140d0309030503030a02031b 73
    0xc0d0105098900042010003413040c0803c1880e015040c00d20340390f5902c2d00001e900c0d14603046000c80e140da550303504204945030310105c800b14070b20303d5120340c240e013540039103500c03419109060014006400050114221130340811008031901401188820501c0c1e451005007000d400c0540c80384059400c0040c010280ba100e481c0444e010100204910381281c4142c44240c1c0e0f941950008913900210f112000c0040340112000d800f0000d1248000c000c441d08240c00100066100302c211818820300b403105c1c2000503040d0100e141590198071701f80103121001607400010b0151402880300d46031424080c002484030010008240c40050b108442440040a040c1d1264400401100010003014880c0000050389900280324141c2c0900d8054200020343e00011030301d82c080241137a59a540e9107100c64030f290812140c03940300071080003034450301e458240190394100820090910a07611896118105030013040c8210103543c0000072a6124641014010000d40c415502c0c1071400b083e0400030f205440741c0408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 135175692 1250 135174442 135174449
    0x1050115080c0726071505012402011509021207180e13060e06070e060f0d05060a090207080307020c03030412061523011d01080402010f11120301031b 66
    0x250464156299168a02d1503000030303c04640c0c000c03060000c20a81301c406241e00b54014200045140d440b000c915000342003410044daa6040c19040c41c004204991468550854500c0c0c11050a03801c455043da049004042c450101907024010040100e4507214550113003095140b40450090307641c403540c1040d201008018131080c2e840300d02400a03c103000c0f0111905401c2400c0170f03080312203181c00b99115004e560320b00101d60030943c008410009561360040c07079500541004e40d1000d203400c0620650440500c04c0084000c040354440c804514a51141401c41001b800c0700d10b4110745402c02490322610b55801950303840d00610991500c0b12192030b0110445080b04c00025407020b4840c0c013607464030081d011007030500c402e900000c5000241a500d20b03075070011010141751010300c94078040001400b4803080081036030203400b4032150365a00383d810948054100d41c0909000200007400c200c102c84203c002005041c442c0031b60001304980071445030146058034400c07491710400540702100e00d00300316880d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 135176942 1250 135175692 135175697
    0x308151302160c17190c0b160308070c0b0a0902240c1203190e010b03120c01060603060e07030209030a051506090702160611070308030c03100b0316180509150301050115 74
    0x81003e030140301c6458445c003038580b04462101c80389541703101c079010780e4000200c0e009032001c20705400010103038000300c000d031300c060541815054155551540e845044005203224030159803406182c2c155a41c2d080c5411040c1d841c802e44e0300f098030205040001d40d0308410a07040062007040e072160307020398003d02503e02c40c40011148186500c4108050350261145152558055694030200c5000d901e045c04411004000020f1250707546100907801c5007101c00759030040301050f02e0040b05000e03110710044610382040e000e01e00541c843d080140028103208801c00c0040c203502c50020010f5075555191070b400d1040908a94030080f9a5540c0001d0340c03540410201551000000b5006000c528001d0b15001851401c140456440d02c0d100d80d07400700b040d401521055034080011040161800100f15008054a682c1c05110700b503040c8007800308090210440d002080c13101c03c0c00380c0800562002c0c0364034010f04000704001801e00380b10751410841d10f212040140607500b0003001088516501c0e00100307040d444c0b503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 135178192 1250 135176942 135176953
    0xa082b061d010803031504110c010501140f010210020a03020f030a050703050c0a201617070605041d0705130909061b020c120708030301080607020106050a030308151302160c17 77
    0xd411108046d0320703550b6000c0e0b101c0d680e40b01440e1122895006410495420000001c580d414100544900b0300081030310340c8035800317601641d02c0e02d0f680400d000d040841035810141e21a01c1ba50f000368040c1c0110001d61881e40030201c2080300200ba50b0300440c1c00742400341c804100075214686505050f01c14003403c0404116455000c000c0c081c21454120b0b0303008800001d4440003500712685401540f401d031700088800001c0a68408400e9092011000601c50f03420710500d002c2c07810740d24800740d01c50000d982c444403007008001901180100c04403410101c04410b032a1a6a4592868100500d00c0311800e841c2f46151081c541058501032018414a0032550010305610650350100110029800d84440c40c82c01075603400603007080d00300302840c0a0704100015000504e403101d002401c46005500892007004100010030100b90042040c9400041c0700c503682d02101003a401040035140f00c1044d44c1c20356840010494031131891071a003058514810600074101c181e4442d0007031203110b8482126000368105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 135179442 1250 135178192 135178201
    0x7020f09040c08060c040303030b0a05031f020d060909151e020c030903030c070e0708070509090405031204200324061c050c01030c020f0a082b061d01080303 69
    0x200c48403030340c0035100308184012681c44030300041c20018162085c02d401000401d0078010540c250044d030921a200303944040c0011300d4807000a070b40b120070101d241100320451094110780c50303c070313012214400884c282c00d001182c1c0d642c25201c0104600e4900781da4558078030842000c020650701a1498000246210800c4040810740c80802540119450841440100013050701c546003400a0203407800183d01034406e01c1d1130884a204400e00007001c1c1ca04000102041144980d0040b0688501c900f0545089001d50b86525016241d0702c500d0303d6420309030755031404110800c0b89001c08480d40440c04658400d80c44a1070050555411400c0d4072000b060342c1c4035181542c10480d03071480380d41c041c0300100380200080601c201d0b1240c40302060b2003903400e0703004a40382c003041e542c00d809810214407a038030091289840010341607441700d10140c401414a200011204890352950300c40307604071001d541ca00d01d00007e0789800f041c002d20300c1d8802c030340518140c0d180100d004004c0c0c3c0b90082c100c520000c0514a9984c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 135180692 1250 135179442 135179449
    0x501050c0d0e030304091a0a0e04080423060d05070e0303070c030210050f1303020103110909070f141303020a0510050d2301030302010e06180d050f040801050c07060e0307020f 77
    0x24282c0c0c0c030036058070083c400000c051046024080c0c14190340030712440548104410301440030200d8009440c2d4500c07003428000000e240070125401c50b0520071480005222141c0c0d8207411503420074410b60b22a038045400004d01c0601d6021038000e40240c1c0b10b01d1030948045c010b0581b03a00586801400030021482d04001504100c009841022000d04c0c10134648921078008500541250480c1800b80e20751140a00842d601031251740052100d42c40740030f0402030b60400251014000410000070044940007189401c0c3c01560382c00c40d10107001f20301c03c0d166514402d40300c8410416110507842801c00c81400110390611441600042640c0d61b034517481e040c821407852002e041d046951401c007a6400311580401e2904400c4a400b0714425400400c9858950315041c6c5040b070301810141440101002c5515840f000040c43d82d407080180c10300300d031500943c8800f00182d004075400f821040d404c0204100c0308005a10003005e00f240308240c1080000007111540d50b1300e018800000f0b4005901c103403211103925 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 135181942 1250 135180692 135180707
    0x10050a05030603071d100e1510140a02012414060a0c02040507092303060114030703050105070215010e01060903020d0f02040f021e030c0f0a1403040308070305010501050c0d 76
    0x242c000d0121401c560307039030b14180300c01880701011054007400003003485800c0c0c0264402e40b00600d80e12018100a09000c990440f1404490031107a00c1007650302500d011041c01203038001d09060303001090340d84810100d04081e0103085080c51200c0c00c58020440000d00e2000000041c2c05d603042001e1060441d2500302c20301007594410540d45080c4608050300c8401a900d50094034400d000e070383c2d6a454514942000f915910480d000c0d00c080a0b040c420b50424641c40000e02c0504551410301c455821940ba0b20100e07050009076000a000c6500300410070190300d40006607010001050009100c1c203070f070b07902801103080100303000d035400050005004101602c3d2118010081a0003004910040f070a20b50011b130403690ba0b86022300aa0340c02007020758014008401001c03c0c60301480f0000c2c82d51901c3c0140e2505441021903244d45030b039021800c807041c2e43c8604000240800110000e540d203081509018141460840f040000241090004100c1e544282d00b50380b0b5860511000b044005c05000301a1001c0c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 135183192 1250 135181942 135181951
    0x503090909030d050a0c1d010c0b0601050c030c0606010806090f011a1b0d110d0c150b0a03050c0406090c120c02190606030209070801050922020411030a0b10050a0503 73
    0x501c03081c006030409a41e64418103000311141700f40007900d08600c0341c024001d15040c4900c45203071002c2010b00000d5980080c84080e41c150300604095096a81800507180c81c0114044c150541c07001140f440508140015101d000701000d884848645d940c5004100c90350310304030741c3c200c202100e80d0b00410004940ba00c0c1101c10b1300c84880024200f260528941402c0909202e00445036880b0074011134020b074000700d4950403410050050012048905009400000c022a00401c81207100340041135440c03481c8e025541d03111008101e170305d200f9034030b0030001d96594a202e2400d20072860030100148800300361182c0f28038000e00d138489142c207504502d0444024002d000400c02036010708101c4846a215010981c480144103210004500d815401446085180104144c092181600040c40995164503680b039001c0941205843d00010f45150b440c40045d8601000350458200700e148000041094065403080d1403901c800c00ca5601c00c8400c000805d2204410900421010404104000d21400086601 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 135184442 1250 135183192 135183211
    0x22202070206070b0f0a0204140d0203030405150301090b03061b07020a0f1701270f03050c0607090503010b01140a030903031803020706140310090b030a150506031905030909 76
    0x2400101d4011641030703889007a00300e0344003140c90100614290307a090b0003600007145000450a1600300f41d1501ea1054150310003c1c4240380c0742004400b150380c20412140681000381c124200c210b5107600d5a10540c000303009044499050203500451411700060303e0b485a441c082c41c101d001c44812400b400c0d00d83c0300d098141d07001642c5850100b2003050754075081c0000c010003080c180302e000c08002c1c4542107400c8503408070790b921800104031089810018580100e6038026000658800c0240b606549070312441a890669004541c08c1042c400d4104500380c08550069000f80119041c0c03800460380d41c0c159040e081044101072011140140c400d51000084038821f01f00002d4910300410150000d41d4824000c80c0107a000c4481809840d40c0078581b4035246017040e0b603403415070034581d0005841c00f40c60f010709012156103101d140c00c160307420400d284003d500000c1c20041013000d0f03052100505030407101c25011744a442008054039003031124256003d90000003440c10400f0385800c2140140020340a00c62 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 135185692 1250 135184442 135184447
    0x507081204020d0209090303150103090c050f060705070906180b01091404020c010504060906061505040509040c05040507111614060a0e1507030e09010e0a0f060f0b0913020403022202 80
    0x16291074445a0050001031b0017551240b4000122084070f24000161504141c24002c030900015000c05d000700c2a16421500003094006d490040344050068500290091040003000101403109520150607140d002200300c0841c058400c800c010b0f1035400c4030302ca00044a0107001c001010a80c6113804626500038000342c40c08032600e1105007901c8044c0c80544604c1c0d503c50130f40081184e00d1140800170080301148154800c8080b81c0502580240e110b000d00a503000b400090401511207001c60207001e0081041005040a8070003c2041c0c600c0a0000c45a110750b404944840906900d820104d9140301d218004c003180300001d10001d508804460428895050006e01242c0d0302c0003203046c5190031056100f0b40b14096414002c1080c20b48000890154086c800180700c44a129207100d41d000c40c07900d4000c100c5011400c60b1000404d05507024007840b0b428808003280140d0764074020501c002e03049401c2e00074005504e4901c07089218a100003940031700f480b11410500c50080000c40c000f140d01410060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 135186942 1250 135185692 135185719
    0x3010204051002240912070606030209040807020307080606030304060e1305010e100e071e30060e011d070c08041805090109080d180204060b0a0f050708120402 70
    0x258800c00002611016070030080c0004800e801302c25140324030b40503404000106040c4100503507140d05191000b42c80300c400000b08030b02131050903004a4002c581c040d01c070304050f1400b07040580250300800003c922900600c3d000060b2510300280b001c0c080c5200501a5290916019041e1442000119040d412031500900588500307501d104143c001c0044115198103032420f44920002c5450b40e400141b424812241030250a03a440002c0c2c10000c2c400b4141d03007403c401f0000c0140e41e01e613030102e00f005851074103204900400c00103140c1548a03095440050010548585100305542c0003405a142410300c44000f8502c900c0e09981310580001850a0001c0c1d91881030721405003642c8160820b1200c002490441920f40314071f8410316038044082c0c0000c00110701c0d03aa803240481d21403105e43e4910240c80b021112012100e01003c01440b40d4002d00812009540e11446417060b008401d6000214041c8080c0400c0c26000310102c1c0c0b0404ea20035561071400030815265605204045c2091ba0000309140701d00c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 135188192 1250 135186942 135186949
    0x816170703020304140a05070905041b06021e0a05030d02071a010b0a11061014060909090f010501080f0304030b0a02160b0a0b0114090603041b1d06100f0804020301020405 75
    0x490040946035400b6a4130720b46801e01180c0b08919510182c0c1590041c20381202103000400e50200351160090086000d80702c5080c0085010340c0042100e50100151400141c42ca03000640000c164103400c05041c100314420103425103c0e040c0800160950308104880d455a030a40d600903d03280d440f80640920050307004403035032a0540260040c2512290020b8004200398004040f0842c40e1000d200034501c1c0e1400300d80030a114103080c400d00041100800d0b540750103584240c26241c040c2c2028140300c04524246043d50741da40c15003032518003154078160010842c09008540e070350a1344c0b4203400840ca0306183d03946404d81c2d550700401000c07019030300f807202104001c43e1807440d2075070343d0250030761607078a060030304090048502104541d814803904202c0211010709030010fa500b8174600b100e2464980e501c0d41420315848440c601d0b10250440740f5030000c10f0705001c1132480380342c1d400034850307201c11940c841041c0101464105003800100d5144420001072a00c078421650f485440070340090b0910350341e000030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 135189442 1250 135188192 135188237
    0x102070f080607030516120f021e041e0302090403080703060f09020c0705100c030302031b071a0a0c05070f1a091e0304060c0f0303060b0703051908070816 68
    0x1c0c122a80200c0c0030b002e030966250207a96000121128400741d4030007141c42c0503094104880c480031040d901d40d280800c1400f8142d054400c0c9015013801d1500820040354041c65a9200340503113115445420403a501c0700c00d444042100b88c030303405800900b00d52202d480a4455001c010503010030191036002c0401d42d511072042100040118200168881c4907810200b0f041031615003000d402031820b15a10010141e1203661410b9003a00343c100143d81c2c0e1200c400d404120141c0200400790300000155500c03c11070980480c40c001e856201c107843c0e0f2601c0d002800c00c1030b2407100038003c00058081c05040c000c1140c420780c074500d9611410040030345400803140340901034022144180c840c1c024007803004208400010f10f8020769958005945010f05150020b0040841d000c00504030804003034444007007500070f80c046000b1f0107200001a032251610b10340100075030300c80b0740004400c180015a66030f00b24001d503a000e02540c0320743c5030b42c1483d5407058500001034826144000c1048650a03000c45802d890405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 135190692 1250 135189442 135189449
    0x100c0602090303040605180301141b09030303010f030209160824030607030b0a0b0c07060e2403040309052d01020c0d0b01050901050907140d060314061803041802090102070f 76
    0x206c0355110201d030742c0010050101b44c03849038002d03410301c0b0421013200c1c001c107402d0780d1104400301d00b601c1e0000c855030101100d0040000180c0c15210000000c620b00600704000c8040700e2007201e0754125030341c03203d40f40b00d82d140c503040042c3c01040721103000c030b1014100b0b0340c0410000452000d18840091900c2c00280c03820009982550100360b49042e4081c1c01d042c4000b01e44040c00141e03c00c01d04e40300c00880e00a03646c80b000c2c41510100180340d200c0305541d0381c0b0364405415680311011100d012084000020340258801d42d8220042250840005001d040074a0742440b00b00c240b040400c03a54600681c40030301130400b00041411800713081e017001c81d02d80e036000d003105407039000304a000d95540c100b030180320507508187c00480c400c01105e401c111046901202e12554580480074841d2200e03100b54444c405040305401c024071840c00428003c134407000c002500c91080507010b6010382c424840300c04054480c070481c007c2e25040e40240e2208803120116400400481d101841142c002c1503076a10480b8500c001d0b40c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 135191942 1250 135190692 135190697
    0x10c050105041b090204060804080a0e03030301150e0d05102004030b0415020705032b020d0b04051008070501030b060702120303070f03020414010f120f020a020f0606100c06020903030406 82
    0x1441d0b008a0240322508401500e56100110314013400d1502c0503000203402270008152140000755460b120313206041e41c40c03ea58002d01100d45950b1983c102041603005c10802c2400900e580580c0340e2949081061121265044009080e00309103405406000e03100807070b2818401c0110000d0300812240300002000110f02800e400003190902c2d00d00301074030030001101451600e005201c0700003c140c4c08822192909461516641500400040d092140112010340700d0901d10100d440b03c42c164a0f60807490000c1000c8a0410555a80003001c4030103240368007414000e58803840e01400254001d911590390140c00510b05414000903500280806803007208842d01e541011090040f56034016070b003144c5000e0715040541c00c150910f4071000e601110891540e041094600b482514217015001032a609800702c02e0611000080c010550041d60012040600500c0351021030b064103900031844600626004000003d00c2aa121046803001000b80e000c6c2c6401d60300300034204c1d1590741040144014111074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 135193192 1250 135191942 135191963
    0x103083106090603180b13030903020310020307030c0212030a2d0209030d0c080a0e06070c030308180601140904030203040b0a0305010509011e0b0c0102130f08060106050f0711010c05010504 83
    0x50005094800108034201c490100e8170082e40041c00041d40fa03980405030f002e0012482c99642011550700c911030740080c1d05070040c0054008012655001580300b00c0103a1028000d030b81404c00104e0762800c0302141104040c0341440481d4130f0183e550030001350705080500d08211403001e40704213034207982e070b2540031461103900003200c00503824244054111103046040000c80c014a948030b8400600c1000307200710410040000454450743d07840182d820a0b5003000503154050345034034001c0c1c0f84c95010340d4440c820403010744403e102f400c400a91141650f01f52001300f5104c5502006000b55850084d0085042d40030910001c80c5104041c0301908005400b95000b04d085d514240c2031052522040e00100b04c80000402d40c0d181d0614000129411580710180d119501e007022507400d8024040e00b00072103400d40c40144005006070001190b0780a89000c5030548049136a900d006450b24441c60002440c0302e502401007401041c0200848443c0340ca041c1001c003841440c540d1050300311003084408071402d480d034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 135194442 1250 135193192 135193199
    0x1110c06041704150302030403090e040c0e0105121b0a08030a0207152c0103060f2705070c0b0603010f02040801020706110306011706120d11010e06010308310609 71
    0x12120149002044a40d20345411300c1c0c420340300000d0030b20b040002d1580020101d01090710a400c402c00074180c403030134640c1d28100b03894084032003001841103802d0707001140b00201d40d901d000030125044403c2180103054241100c5003602901c19a00400d0ba0301505080000031007140a0004046009031507000c1d10b809170510380c000342c0e403031b000c0c5001c0c2c800c0100c2c0c0c29174a8a40c4281d5081c0c0043c0e00d440e03d44a00064028800403000380c26582c010040d010070a000008014801501000d0f4041043e180c514007124151501011500c01300d4090000034041400d52010810005659410200240c000309403c0f0f1201c500780240e03401540100156940018008240302444c0700c0c1400c4100001c4041d1320b14201400003d101210641400c10385d15584004900700d0b540348024000003181102c2641c815145a2102520301107111030f500300f965080080308450380320085445816a07a0088548d4100200c280d02c0591013a401c64103440034401d05a04004a42007a298040042c200350351622449404c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 135195692 1250 135194442 135194453
    0x50a170c030616110607140306210c0102191a0411040612030e010908030306100c0c0b070c0e04080a0c06021201082d06011403030d0c1205060d0b0703050901110c0604 73
    0x4d0421010303003d403c004d051118103030740041c01c001d50b40a010b14558032602c81c1030000d415098611a14180c0010040041418a0000c40c1101110000741c0a90788098003207440e9035843c0385804001845a515060640142c03010b04004036049800b0b18000820000e41501050803907840381c2007101004030384200c0ca402c01d80d2200080407003207003c1c80c008040c2440d00328107503030320300000e04814420303000e8001039908140701b13601c44503031f0030b412450b2281d0440d034071403040b442c0794032000f000d9600140d5600007190f40310001d2051405284c0c482c0210789040d040c404100c46001316400122451034003001014100c1d0081e0b54403034041d00600b40500084400004528400c10064080d51400402d20307a080c444980c012919504685180919065203011100000c0c194400c0800700e040140c0340480c5035103070660040030920340903000b400402140d00c40400300102c00b542180b008001c5a0354800042ca5607201303801107a003000c00b1740004240c4500c101030798502c0d03070003001c00f08070142e2243e0b040009111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 135196942 1250 135195692 135195707
    0x40212010b090601030b0d05100510060f12110c0d020d030c09030b010b0f0f0a03020405041a031f020c0d110c041404030302030403090b0c0c040f020301050a170c030616 74
    0x850040081040c400d49401044100304014000f60515540d184c6520003600d030410521007240e80309050301c0212040640d0840100000c1c2c0b0045d0901d01e00c03450200b101c5014012400c9401c12a032074810841c41150201c9010301184100100500801d21800501850070000d071440700303560350043c1c40e0281d00070700001c0407100c03103540e0b02d81080180003042012030743c5000911705444624507000d640d840d10300200d02c00b9119010030b0311840500025a090190b078590301410641d64126800c2c0007031001e8402040c0888984070303516a250700480c0c03503841a904a0004400c0940a20001506001d0050301083c20112141500b00200d50f10845d50b20051a0900171840d1100b81103c0c2000f4051903103d030700d1203a40f8010002024150f00102160516014084090080442040d5a595400703581c501075196400b542c0000d008a080c1510006900300c82c1c02a00d05840c0064005c407410307480c04880034400c8070740c074408144a000d101a9011152401d21050344112000d903100b00e80308807035181c0209000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 135198192 1250 135196942 135196969
    0x9020f0f0f0d0b060306100809010209060a18051f08100b0a030204050f090903040e040309030b070e04201c09060203040b18030a0c23060a050106030c0905030a0b0405190b0402 77
    0x4c400400401680d0754890360011304000b00c0340b40003850742c0c4e204502180280300c2d4007102c0d98000d1003c584450123644c80f040c20003407800181580200d05607680107102c0103501d508091861201c0081c074800046100361041d0340e01000075001e4a04899543c07041c40d01c191b110090400c0000d400180500c00c9041040c0401b94828003940c0c2c0382e45915151040d5070702e902440c020355090f050780c0390109007450702c43c452a2004d95003100b01c108050400b41d2000e00390754659540c2c6c43c01203043c4200c00c3c40c810300d640381c01d043c84190080c40c246405d4065020001d005e44203001901d010b50717643c640801051442c0701540c469441060302090381c1c1801d160759074004090f00503c04440c0e20801c041d02c0c2d603982c45035104030259400401c40000072001d041c2c0715400d060545a25a09101d02410032080d10855040f06040343c1150f1001c0011640c60a0122261982030003000d40652100f00d00380c00284032070440544c02400307072050f40c0d1501189103502d401959040c80640ba03040d4000240720039842c01c0e03211034008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 135199442 1250 135198192 135198199
    0x503090301180206070201030207080c01050901020301170a0c180f110901020708030301031505040c090911010e01030903140c2815140f06010210150e09031309020f0f0f0d0b 76
    0x10061941c00a1131501c81c0b100000c1c1015008500e69042004050503203105050002c020b003d41d14202c10214005d410902c41c0240c00302c031103030305e11542d01404608844410f0304840035000140c01c16050b1000c03c0d007944450400e8990301e0310681c4c1504080d125904000070b5039109140e6403a00d00d00020700c3c088190700510b80e180c104000400020310105880c9404501c03080707006c545592242040c4140041d150b03c51000c450a24080f82c0801203943e86503851114244c239940c84190310b40d030045084401c151001408600d2440b0314580f844604c10107404c1e40808281100c04103801e50450b950041c046005507921082054400401c002c01c80120852410451004000d0300105481c00c44ca04a0090f02c01005442684003069845c1d1003070003041d10091800c4014465460426002208120b076845a06210583c000100342090000300440d0651075102c5d044440c07032418280c01c903000798000303076105507503110800203107020407504006072050840003500a42c60716110200c070b900b525520b0016910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 135200692 1250 135199442 135199481
    0xf0a020324130206071208060103240b03060a090c0f0306081b060903250503060c04031a1509070302030708100303090b0a1205100f080c0a050d1a040503090301 70
    0x500c03101107841141d0110140c508110780031014000720700d40e44103454026042c107801c0035440000c140c20502c194054482a40c003002521500200e030241802001c0345041d0041c0002410011000c92801564008900800849840d56607803040011184c044020801140800003009105034042c840c0300010074441d0040c15070482d1001c441c0c20b40e03017aa40c004e580300d1000480c240381030b40c5003044030b1281d0001e071f8809000c2c0d1044000d0f0450000101d4030840f0701c24401e160010324646100000d13141140d502058074800201419214058040300608203103c0307025001000b615039031180c8605015000946005a0b039041181c0010310100f0010302c81c030640f00360101c0410000794403406500c100d42034045041c1e1280c0c1c80c20b40440c0c10542c03c0180a0000b411b141c03d0005410002c50f011013120000f111350548103541d00c0c006900c42000798202c0ea400304000c1d0f02080942022010038241c030b4481c00152040182d50701c0c0e482c0900400352000e499950001c60208840c3c2403d10409400000b272a000c81d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 135201942 1250 135200692 135200743
    0x6040e040b1e0615190207170f0303010501110316320c061b011a0f01020d05040e10030b0a0603050609030721020a02130902030d030509030702040504050f0f0a0203 72
    0x1100b000c0003400c003a025000c40b03041c1c0c0841080c502c095035a06000802c02e6050b642815400030341d2900c60740201b090782946003282c0c3e04c00880006689101c110800007640c2036070f280000540f0b002d0100c0e009404140400c0001c3c994801522560601c142e11421044251002400c1d400b9820f060411031100a01c1c42c40c041d030008880c000800003140c43d8222100b5650790309200400d4010407140d0860481582855503102c1007880f0180108c0c04a01300b60784000109482100480c1e0341d68280c064200842c80030803041c400340401510b600e911901454140c0d4030740743c0c0ea64880c2107105040301c401001d141d50b0070051040107424807071950000c0f41b150085007840b0045e2500e81c1e03101418800194003079a814a01d040450003413108481098004014598a80c80c40a01c003010300b034a00d404170300c0f038050350f642414401c0c040d1007110300840803640150700300780b201e0303003404020400034100350798038840c1100c00c03117201400700621405041660050082c0c0390192051629254442010030801000ca500c01c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 135203192 1250 135201942 135201991
    0x9080c15151c0204060812030f0a0605090a0f0603320f0c011107030507080d0e010212041401032a0e030307020f0d1103060c030609132f06040e040b 65
    0x5001800454285925442d07a200250007407442d03030300580d2907000f04000d0041414000018502ca03d074100710b0400d0b15560380e00c0d0b1108607215401140e502c0070718180850207c21482c4c0c080038180074138010006900740c8a4607407001e0841640100b11102452000c1c0044c0c580c06014a50200f54194006080701c4110700856a107503c418500b180c1089501c14030601070b000d00700324140085070003100799403689031141c0d4819154170044501e0008030380c111100076055480045e280c0004000700e210f40e0704241c102490600c03418113900c03400d81056251000f44040a1240b03031070004540103481c0d40c005048040c0d2000d00031104418609104c4c1e00244001c401503210405000f840340811940c5692003211454001e82080c00d440089405100340410802c02c28100c10046010318012100c003502942e40c0420940384220004008082c02c0c00200303605a410f0701e115034000840180300002e5508010640899225000396020424810340407050109204800302c0341d9401a120341c100e8040150140381c030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 135204442 1250 135203192 135203209
    0x5010503031b0304120803070807020a020108060402030702030c10020901180b040e130f0f03110a050a03030b06041206020403030f110a020904020d060c030e1c08010b09010309080c1515 81
    0x1030744405001d000c00b070011040180708403030140000510044540000b41801500d81c3c03c201e03219804141c0780c0c03020902e610700008000100da54140e603400718590360802400060b40000d801a004d51105000021001d541400070f00c403142460400181c82d183d010340010003642200c400640050000d078803e01c101b001a500b114280c030030641c0c00544984070030140c0c0d03201e852051405001003519018000800ca040c4e5803221290b8000d60b1034070060f60842261549030f520346400200310394403c5000400080c025004558250001407940f42010741d58903581440c810003410455855a000600380105034001802003107400366480c014008214110102d80d840040c1c04000e88514146c0700060119540c51443d51101c60f80050306105030102e03400302901400e105c0c0402c3c5107a000d58118200d2844001003408400c1003195100c80c0c00b0b1b480c006400302d00c1d61141e0402810551206403030804204a100101515840a0000d2550220300058480c881501130000002c41c00e001c0d0520060355107181c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 135205692 1250 135204442 135204457
    0x10f02041a07020a030b011e090605130c030b12060a05090c1c05120c010507171509061513090c0201060b030a02090109080607020c18060a18150f0302010f030501050303 74
    0xc1c5981d05a2400020300102141c0d0004206041060000c41c0051200014a072012038034403070300160503203a030b4101b4161a0302e40510b03908807282c4441c1c01c1c80d100030784d000782c00700380c6a5041c0014281900d102088100321074080e5024941c0c03010060040700c22491041d60380c0034482c40060001c1c10004e4000800a540f40b469610100e16402600030500c0002e210426210b40c0d021070899440e002680d1460103404102d81c0d10380130a201d18010560410051040b51048181e0030030203078404546402c0106880c00901015041100c3d0041041460b110600801543e4520202c00c0e00c000c2c60004410141d4a480020f84216414100c0811415280c1400c0c0c03a0404511803001d6111318403400100c0d260301c01c662040b00140720320014003140302d80200b40c927001c42000342c4030740062044a8900c20104007094070b0094000c10b0f850010817410064100d1002007001500001c01c1203001598030003005001c1344c10807000d1700310700c0900b00f0443d81c00620038141e4183c01d0609108070762400000a8a9010310354 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135206942 1250 135205692 135205739
    0x90908040506031b030a0608100603080d090501060b0c0a020901060507020102031209011803080115110604032304061709011505091302061206040e0a080a0c03030f0c0e03010f0204 79
    0xc081902415820504804c5140703074810683c9900e000e4107010081c0629204584003801283c4031224091032502400d800e03650022400c0e46003418400403140100041c03181552695a41e02010600400c044014412002910002c0c544250701e40104010410180e001d6400d00c00200708000050344c010007900c540c1720b02e03112641c00965441e00998054487d24518121450184042e202095000b10710781d81a283c4080750503500358860b14082d1104944400207540981c008c00c00500024802c107808001919082c0c481030410301c44020151542d00213802000100320050180c886002103c001150320038007400083c00203040300321803040400700d28040c541c01000350303000081007110014040e42480e68041e01c1c8035501d0070030702280d580f019400c1d620a403040e4146082190380c1140020f070b0001c0c81c1c1d04131600e2844c084070b15500352284085078a0441c1810f40b109200507101ca500d11403420704603100e844401740301001c0c404050844648040101c04503206110030321030301c0351522101800c3c40c200c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 135208192 1250 135206942 135206947
    0x9010e040f030c062406030c0516060506030712080304110627060f0a02010506040b04020702011409010903060c020d1701080703030e030f01110403030e0102010621060f050c1201090908040506 84
    0x20f0800002030802480c040caa6010380328907420b42c516000225104031565680c02300b10302c071306555041740c05c0d20a41d101170002c1a4821044800300308158082c3d50460702c000c0454400c1a0785614030110640707480070030348014001108001c180103020703c04050503142155003500d00400864103400d130000041c0041c60709030340040b006402380c8038441201c21242c0b00e500c6031604d07880c25040c024003810046944500403410f002d200340d02401e10703009444050fa4140c40d0140c0403903c40a141050b6082204080d040000000002010030000d01c0740b510341c0b2866a002e484910004000944200c01c039007100e2480c0b0f625100100300c02140802d1500030340394140f42c140200e52101c00064540b080884c80221a54038001da100780c294210070041c82100c0c8030f40c403010210303031055005900302c803446e21032403075155103003e5644455103e45454204c1d1030b126500010700f101174511020201c64080f902120041000a5060a504801d42407140107010b5000d00340403624040e510000c00303005912947c0d004002c007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 135209442 1250 135208192 135208217
    0x15030506062209051306110304080f0f090a0306020d0506010915050702030312070807120c050301050108040204140a05011a04030804090b01110607020307060c030c08010b090307050a0e010509010e040f03 89
    0x42800c01000f4455041c0720900b0b0500c2181020503414800b100c6e002d287c0030f45001941e0410054900c259088411a4286411040c80000680c0030918230000654200701e903412035030741d103030382c0c03202541c0540401a01d620124000c5022520040d003c01d050011803036003084134a0019000c5180b281b010b10f800c03038941b030203440464903500079080d0b1448010000340802c07020503448990144514419980c00e6400c110b50520700085a0714664200c00048080006103c030707500a0001d16000fa00c040c200203408400411401310201c001e40e0700b82001501e540c0100000d41111450fa5401c140c507104d41461305203141c2c0c402555200d28418801055120000c02c40968014414440d0b11a401400da550900d04150025100da02003c012680c003803804c0100100f00e4820b21a4403400c60303854031001c0aa034208001401c041d0410910a81c0c03610030900d0124140c1c480c00412401010a4030310361805505040c100285c441058100790310b0910594108008a40c4242d101c41c103e0380c150500c00ea0758102c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 135210692 1250 135209442 135209497
    0x50c060c0115090e01051b032805090105010509060102010c080105040c03060512030d050a0212040219231c0b04030804020a05100804060506030d0905191502071503050606 75
    0x91481181c42240c080020020700442250001d0303581140d100020017040e6104c103114454160011a1403001c04010f000107225100c03054009920016250007030101d026481c2149d005a850440d64000c42e80d4480004000f01d080c1000d00c10b4121009000070302c00c80c02901f00c010700640d0144a50b41c451604c4e1440c640c4407502a61040f8090300c0007501c080c518401e481021581d90f1b100150200c041880c03c000641d000500f48291540459510150f00550710740390204207807190603a4800c00309200c603200002e00e585417015495074484c1010f80ba101c0344486802000712140b080c0c006003903100b612500650000d101328a81c0e030340c0b260b4035083c1010f031603ca0f4004900d00a00382d4100e1500a40ca40c40c0150003540c0101d65070388114801c0c04284102ea40d0b9105154803480001050030210b02d00e008140414501405184da81000041a02310302c0c523552071b0351241030b801d880c010a0250f0408001404a66256480b2100820903810144402d04244021400c02d200d0789401140c1092a100006980b61 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 135211942 1250 135210692 135210701
    0x60d0605150a031202070506090a030201050903100f0b0a08010207030f050f0409021204212a020414011a04050108011203020a0f11030106051f05250501140601020a050c060c01 77
    0x25224416803503c07460f24416400d07030b00d480c1e000075104e00f8400240518190040f034134468405081407031014035544c0195103940044c040c441e414000c0a40c030301900c0f1020720030504052020038011800040200620020200c96040951181d004000f08404640c200450340d80c2c0481900e04140d4540c0c91161118003406290014002c150001a00e003008480243c804e9011b1805611138544032141c3c481540f0001101d8402d51000ca4081c85010b100c9408140500411090141039040c407025580d00050484004000d504007250303000b40107010405c900240c5a40e0201c450202c42c0c85c00d8100000a4007601c01485444041004035418008140c400e00168116030391080381450070007140d02e440800c203542e0f0107010380a0340c80c0c582d0018161900f4001c022444a0720300280181042c41c40c400c030f881e41e0010040e402c03512034520150302801c5010388a401060f010f0f0000003400381e8103030340c0100810006414a411036005404400104401041c2800d40031011550240d40c3d40640000302d0241 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 135213192 1250 135211942 135211981
    0x1d061b0f04030209040c080a210e010e060f09040203011502011104060813061d210703080a02070c08060f040b01050a030302060a2007060b0405060303120f060a030b0c18010206060d0605 81
    0x2303004280003a0100705416002c21030002c1406010303550786000304c500b140c0c14800407524070700103082e04070b1000440c10850001c01802086401c0a485d009129000c902a43d10a82c041031188414440500c0d100f5420310039098904800700540f4905858080010014a00501408030790303402c40350b2201c01c01480703a000b028000c5406c20740700c7c0e408641511301505c2300078030b0800c05103903e035000000c0701e001017903c1210780056064960070501c1e00e034540700314000d400c2044100c3d0744e910201e901051646003000700502c44c4030300500c410720070f03d40703450050340c040010391040740030703041d044000c1c0002034020030082c1d4041100346c000241000c0c4801200320781180120140204800040d030720082c03099540003c90240c00545060000380c88030f5003859503e218180e0543da80181d41030114a20185040241c4d401480c01008002500e0302da0700c0d42d125801c42500d1144503200000307450000044005000e028410003400944010300c1d101c8045120ba04104400400242e59000019641b410010100041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 135214442 1250 135213192 135213209
    0x30e030d0c17070201020c070618050607080319020702100e04061a130f05030303042405070e042910020a0b07090f08010e0706121d061b0f04030209040c 67
    0x10a0740008064034424090b14240700d15114280002c580314014000c544c10600c0110080031b92614204007180d08440c00f4800481c94246202d0000e840d650380743c040c00440d4041d00d42183d80b418201e0100503681440100b0030100ca0043c04208090b9641000010060340d090510400c001e48000000c2d004025603002013082034503521004083c04140000780000110780315400c0195511400d00703001580b200d01ca4164194010000140014294046005503050110b200981c0d54840280641903c0040340d45200150070310710b18882e075103094007403818a03861030400b0085946501010780c280d0760841e4035090003204a00e047e1410745208000c50300119810101a96103800c0c40d190080c0074018601c5840e03c8100c0f8400c000c0303004031040c8280d054074001d40d0000c2c60001d140000a54201408001803400d6940c0c81e411800446041c241c581041451040604014580304580b5a4448600120500d0958062009040c0f01c0007410484046e00e0301190315200a43e04c42c5020007840c00141c118404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 135215692 1250 135214442 135214451
    0xf080c2e0b120f01021902010209030a03050703090b0406120f0207020d02040b06040305060a0b01031d07090c050c1902100507020a0302040e0c060d09050606220506041128050309030a030e030d 84
    0x9543c2c19030142c2043e0074601d0f00400c2072101000102d00341c1c041e2480c03969140e0080f484090000340030718002d1400b18842e041140f481c564401407074039141c20640c042c0c0089242024000c1002015108030000340881c0300c0110304210803500460306003990007200074081c680e1418a071409995510545000750740c800110b9184c1d2801d40340c02c50103400f580b441c0502190400d24800f14521a0308400802031055a000340305007031a00c0100c0f0080d001002c22507041c007104100c0d2541007141884041403047d110310050b81c030641c85105021105821444090130010140300b00001a0707601d10039401101e40440303003c43c004184002d0346062101d04031b1001d900c000001903001410005030401c0121500035002c0d10300325510102400f005c61120346a848190103241503804540c0c80e540d01c2a50065030162000a00a0030103052010369400b007113000301e0204621104844c100054030501120030081d141842c114140b80b604103030782c0c0c014039030000d090544a19851805200410a40f03070010301e841740502 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 135216942 1250 135215692 135215713
    0x10c0c09061211030f03032409040f020a0608150111070f060804050105060a0605070f051609021e0c19171614010e0d0315030f080c2e0b12 61
    0x581c6502c03150011202c26200b480c40c40318503d03012031582100b144510140d4610f1755003200405080e50700020455145145101280f503e8540040041c0319078070511680380450707076500400a02280c140d105c00e041210b840704104203141c8070391002084203000e0230180010442e22116900b4491036801220340c07102040310000d0707411b41c0700649500481c0110000c10881e141c0740117125005045004e0000170601c200400e40000f024103c0600140340200d0584002800000c194110300c403041d0b0040c1c4a10b40c0200d84502030400134401c0d9001800f90007600e07490035107010821601c0c0d10400420621401c0014000340600c15001250546049103034281c0d6038420074241c00410b201d0742c25006035040d0b4000d9116455030481449840e00902206c002400740303501c040d0045000d40007071101200c03c690003400000008856201c2d2071417482c4141205170315003540d50130310f6190a041e402040092810340c3c14860840000780e07011284d144000101040545050012545120a500064409104008448 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 135218192 1250 135216942 135216959
    0x50319052a1909030212010203090d0809030705012d0b0d060510090608070306050106050717030c040305030d050f0f0c07080d020403120e040b01090f0b0703020f0a05240106020606010c0c0906 84
    0x21420340384201c1b12048040d11101400d4202e0001f19005072039544485000034083d401200b40c1d6134070010850480740303860610b542e40340c00e42e000c4040800c409201400302c404e407920100f040403d8240940b10070000ca1003501c00081c0c0c2003032080c13005800340d6603030b002061403d001c848912010706080c03003043c05501d9540c241e480c0e07070310f216110607182c0c0c0b8902000850071510a04c1104e00490f04403102240c002610318400c0c0c506e5001410100403090200800800a08240060050507803c000002a01d240514000c50014401054000b41a0310141001180d038440c4040d200388903040310041d03807070b0040d5441e88802072080f604003070900c171422070380081c1701e540c40a0368a100b002d0940b070901c019000702c3d006542c0c0000600601c4000c804015003800240088c80150605c42e000b413046540044203003141900b032200380b040c1a1769075041858204080807029074050341c0140d0600181009614040c4000c0d212100a0211410070a80851005c103020300c2100d60405030404000812440e541d40c01c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 135219442 1250 135218192 135218207
    0x3021504050a09021c0b040e010906060503061b180f12060709050301180206030603031e07051207020109090515040c020c040608161a07060606050319052a19 69
    0xc007403141e0041c0340701260f15001030094600d1520301c0c009030b20040c0b505908100140a100c3c454030b412594840f25000030745402d001d0402e95900506001034601d08107400d05081c00801413602c01032410094104010018100489840131898a1041051000180007810040310307003600941c40400c910000c1c00803107000c20b80c54011a295282c099406070f90300d003410f080e107000801600f00800703400500d001604091004691048009050743d00d001145442581400a0160980a0944081900f8040007810041070555070b00300b8400d14144030315075000a01d0b002a42c01481f5042d91034001142a601c5010101d15110f24005c2043c8028000d50200035034824000c03021a1003581800000179008102162418120240c0c82013828030b1400d03c00d0b060104c4419140c0c01803054810403441020601c40c0c41500058102507031131950b07908102040412250360b610002e407903185400144900c0c02c21030055038040000640c900b80714030000b002040e815004a01218898032510200090442da12104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 135220692 1250 135219442 135219449
    0x20414011b05010c0f23190210020313050f1603080702010c020d0503130501090e0106050a050705010c1205250e03030c100c180e0601051e0a0206010f120503121003021504 75
    0x40d00351060301500c40c1000d00a00d058100c41e0100340030443c21103100350b000303400a007d100a0048425501d0b14a21603012607008036800314140c45107442c81400c003c1e040c07050322148500d400080039000007440040104918500c80200030050028417041164001d4500c048a5078000b00111001c00780c504040e034076580044902e04242c030b0b03011390216141d8042c0321328409541c0a5a8469181d82c2041e40030340d070940c0201c1820051081c140075060003d4002d009699202509640b0707280f902000c003e2042c107442002d40310b07031074160303070780d0925440f11100354200f840c21005441d0840144181d900030a003580701d40c101141c081d01642c140b840143e0f2040d00710703030520380055844ea01200c80d02d01480c000d40c070082c01443c4400c0522404140158030034005480070326940c14150210350050800291903900030076041000d0382028004104001d4103011590082c43c0d0820b5800b0141c01c40e6680544900c641101540f03068050804074047c040010101006182d000d04072817407021800da400d4016802520 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 135221942 1250 135220692 135220697
    0x5071a070c02030105160c020f011e03020406030b060f1602060d0f0603020306090109080703031e05040501051602010b0607061d0a031d01020a0f1e06151404020414011b05010c0f 78
    0x40c0400d00414042c0c2c40360100c85a243d40d4240d41c21299800c00200444512745903040014028840003000c030721000003544408951001684d4510300078000d0150350750707040418400d01c0c083c80700040302d02403e02194911185040d020f007603c2001e10010b8668000c0804804445207070081c00d885500d007650100f42030328001ca0440c2d00b644d03200a2414240d900c8154010660700041c0901e1000038042e0b003020003038068050316940e005620401ca2000c40d20304650545060391644180035150752940301d03404030001e691009102840711600440d40030b12a074030380245032641e140405040100209403c400d1400701c102030301e0408103e402c008090010300d1084408856412020455542c00041c030b0380503403030340090014400e103403a40780d4000603040c1c85000000c2d030300380c20040c800003030320362045271005e11b4040c3c0d007550010b0400d9001840000d80c20010b030b0243e032040009000d60480003c0c185003031032007440e001c20010000d034400c821003950610300503e19030030007003824000d5801c07581d101110744159 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 135223192 1250 135221942 135221951
    0x6032c0d0e060702012708010c08162c0103020906070c0810050f010b0309010207050d11070b03040b0a091407151b030f080c1b0627070605071a070c020301 68
    0x442080b0702031003010f40090204070a207201c24146c8401c500401095040150700d0010b16984031142c88c296100000700070009810389040280344010040944a01c40080c0f900b0111881c00c41601d03141440c1c0c0d9142003010300844080d80b41980e1080e011207250a4010f0040340d1900501d19250358007544900900900d030244040002c5940c1c22442044c1c40341c50320f0758941e08164038000c0e40d28041e40c000380156601d55000c015520108804001c060801d140340e80da000f2a65051100060a102c5c00d0f4008543d078031020402c2c400828950352a250700003e680b54005000083c0b460310700c030610400c484000b16801000e034005030304a08041c075407640034143c2c2c035800041d845005805000240400d80100440c144003000581e083c0f02d4a170141d445180741e0340880c601840030b280b001c45c100310a00c2036002d551142c2c08000b1030030f002e0700781911035100d64640804e0052700324030f00035200c01e103034000c1c60101f1801081c4441032084810b4104a8040c07a4903014007281458200100f1291404071f069000b582803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 135224442 1250 135223192 135223217
    0x1021e2e050f220c05040213060306060e0a0509091903030c0909090312110c010e06150603040507060f03060b03010b0a0914031207080d02041511010501030c06032c0d 73
    0x221000d0a219800d41109181c1da4000d103990040100340c1d02e5802d40b0300d403810440102e5151624401000d6048d140920244060715245005054035030b079030829802c2040320b03035400c160b0752a98440c000648000311540b5071a640c840c41210719009a07460240481c12544c2003c000741501540003210040041d13403070940003074682c090b403016625816802000603246940705410080d050380020306d40340c030f202115440c200e4424401400c0d00d610082d691041d4000034240b012082000883c0d000c4a0010780e289825441c146c0c44098541825100d030200f4010076094042d0060b210740d00c010302408000100c00d88035611841e0401040d041a40b0303a17004280407000200e0810a218030285034004001e0041c10744c80340036030030300c0300d181c0107a07204861503a000d006007041c1c130400d800500007516582904500e1110031240080c070700b42c407414100c2500d07494140184082264002510250fa0307031403c0211325032031000010281d09100700c4901c00d60130030300e00301002100c0020130346500026107941c444040444 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 135225692 1250 135224442 135224461
    0x1805010503101401030b060409020903150103080406110a08070f021002060c030a0903120501120317060306040209150a03030503071103091f0210151d040201021e2e05 73
    0x1651030b48500c0010350300030000c0e5281c0000100c007111042c50013003194460040400d0240e0070581000c1c82c01a008140071619041c10416140b9011400351829a03951441d1640032223845a400340008101410b03925082140c41004140e540316842003031541e49031a40c0c108844a2054545c040784240d2490910461492000408a004100030107805103140c1364892508000d0807409821014400701090b83e0342080c14510034280245038900c0c807104c40c0c1841d440d00500200b0981000c80210352410103000c0c05440c0006e19607032203503066842040d2500d40e24002e801441e514020389501200b00c401c040100342c0e00801541c0654000c3d10707554025112040016100e00507541d0107504038107202441610003107003206c944101079690060f98006400400c0c1d99003031329500c00d02031912400000c03003048101c0380341e180000c0c40059030047e040d09080540c0003e4860810782100011060902c0600d00d00d64000d000b07a4556141c1d103008104808100d000c503c5a0071404020b82202600d400e000840424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 135226942 1250 135225692 135225697
    0x1801020901120c09090510080606030d0206010519090504030c0203010b010309020f0906041d0c0a0e010819050c03030a110c010816140f031e15151c090318050105 71
    0x16100e26242610954401d0000e09000c0020010400241400500503c8034800d0900942c4500c2e40f200c01f007410000c1d101e107080809400c1c18041d5124220703105569902041031410b640302241c649100742d0303801c0700c2182c6007280d58200c07080540c9404188420546c02074180801c50344240e0090101100303d40065040329130041020350400034011a0160038504080f000364081e90013407000640c0019601303071206420200c120b441c803a81c00502104a146402a4400001c01904065600660500c80000c1c0c941071403030600800d003c1007960170707001c00c5000d00514015200c007804481d11a60300c507600400a440d03490403803426000d074018292155100720600c40c82002000c0b245242e014005804862a600d41042c40008402c14000365503030210035030086000d14459008008008042c48844c1c103000000380040f01603040103404408a511400d02904803040088900c5403203441c11b10403a0300000c0c0710001d6925641c030f06081141015046070350018041859910f404000c0e440e600150390a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 135228192 1250 135226942 135226957
    0x14061009051b1b03160b0a09030926030a0e04050901050c0a051b07030311010f0b1309080903060c041e0b090405181204090e0c060a08040804030b01030803180102 71
    0x110181107100c0c940341060000f08400a44400030b036840c1d100034119a403d54001e0102c022403048070616003428800001a810340011100408025810703032540c0162070812503100f020346501303840701d0b1030039926008003462152030311500641e0382d144062640244103050005105103d0703840c040105100c142c051003070500c2040d040e1602440c0040a501c00d6078107402080b250205c80c041045110b4044d01c003403060100444c8a51204805c903c030b11301c0f6040c00c5d20f111040e41c0c0c0c40140380c030035040d40c13075513480c2c3c1f5140102d00d41030000115511b0700e003060440d070b12078840728980603c5154244031314041c02078010000c88840f005140104442000002c604280300d12900b20a0801030140e0b803c2c610781130340840e801c028a07483c3d52040d8840c0023907482c109000ba03c040f20f410342d4040740c1045141003500500d440e8042d110003070416404180d000800502800640c0703000c0088070000942007182420403100030b15008040c0d10000d603981d240015aa90003204c041081910100395645401c40500a6a090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 135229442 1250 135228192 135228211
    0x51504031703060a120b0103060e060907060e0105070501020301080d0201060e010b0403030813060f090212210310170304090f0c0e04090503210901110a0203040308090103091406100905 81
    0x148194521460034503040030f018076520001c2d00700002520043c180300020f54501c15000d0807a0780d891410800203c0c2d03c1c14441600c0b580100382004011170020500c0310641d041802c001c0030300420040121124040c0c880014025880000041a06880001c0c080c0c40c40c1d4607a80203001407519503141d01507111003845106107000003880244000ba002d550142c1d0f10009003040500038a0440c3c42d03034001da0302507464180303516503659031031741c15030070034121020105101000409003807000d030001001540c10b44560412219000c00400c2c210007030202d0040007004003181c0c0003d42c0c4e03110b0065617100d511600c25401d103513190031080c44d00707081c241c010982c06544644031403410320400014440036289610b800c07601c6000c10810a100d00400b48540100034a001c1944106442c10110031402c55440d28109182d0304d409008882c8110707400030032103007900d90042c9000e40f100c6030307500140c015041681005103a022151110030f042580010517510032500c08506100c0c690f540c1c800035007202c0c42a5241c130314 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 135230692 1250 135229442 135229463
    0xa02061005121002090f041e0501050603090d121b09061805060304060f0b0303030c0405030c0d12050706060f09020c060f060102100b0105090603010f18020310060804020d0203010609050105150403 86
    0x24590b0f03081e8098500c00c0006002480101a0f480000d4100c0c0d080c2c0c020a40c18002207400d038214000c1034802c5901611050b180070b8958105001c100740d840310355029000400c061140cac076002501c0150040e8441500902281403019181c2c8406401040e0601550000030721010022100d403040c41080e10031900c0141032070786034ce00e6985807180600740d04e10a890045803a81400302e041d40302000103500c5440307a0b544090300c49003414101420080079a80040c450144408441c010501f516010391003e4068103143da600c86e000d151007000303400c3c0c9a21000c0c802d041902d0010700d42056800408000541030140c0b102581e403404d142c203a07003105070303085801a031088600c0c508102c4217901c119401d142c141405030030644800001065503009800c6600c418440d51380c208401d031070002c9810303403400441000b5803e51420714401418030119104607001c00480801080a5488a1324114801c1d45c01400a128603502c0b441c4034400b42c942885820b018000b8240041148020081505c0599910002c09803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 135231942 1250 135230692 135230713
    0x2090a0b01080f090313270905062e0b1804090b01180209030a0c0503010e0a170a1b0b060a08070e0a020a03020912010b031002090609091b0a0206100512 67
    0x103d01c850010310484191000300000c43d901c00205060f9401444044005040e0b81164482c64a4100c00282200c2c070150901580c000000d2010500c01c0d07004c5500c2c10b225580c40b202c3d240080740d142c0c880d003d054a5012103200032460300027510003030001d01060005100c200701c900c0107200c102c85c14100c000c0d00220900c401030050720001c91010306c0540d00220050309003800c0383d00007410000c4141044a81100e80380d8100403a081c28040c04000403102e801401a05940e03441e00d9403001742207150311610030310000305009014002c60304190a0903e09100d031104e9440391a09814452050703e8261061380b2446001641180c0000c485081d5603a041c004c00c06601d91422900194104041c12005c0c90b40902880d16641ca4030040381404030404400031441b038580e00185400c1c1050000c403000b0143c01040954400d407140303000c417508204155100a155030750510301c0c428190090740070b0402070034000744c02031500350300051107806010b001954140303241ea103a04014820380080901891508911460b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 135233192 1250 135231942 135231961
    0x1606090203010204090c05040801200406140409021803010605093c07090608010905041713170d03060b07030801050d0c150f1101090302061b040b03011202090a0b0108 73
    0x2000054409000541855140c91000040ea420305011300002900420300b003007074080902031120082c5401e0762003212505849042c00c822b220314050300c000d1011046d08610400111070884001f01001c8a0031500e1705104540b40c10f46034050500c4d07a110f50300f0711001258030700d400940c190003501c086410520b0002004800c80c19001480c00c0d110903040301e110422083d9074124201d0b441030915540e56080c4034102403014200c3c0e40107803c003044042c039140030800000d80402920449884045515888040b5091480c004c1c0d8a280c0002082c900280c1139204004400602041003602644091001503160724030510180100c0341c02500043c043c4004000a041035580105902d018074002598a0f81325021a120003001018520009101c0024000300c03541c0007021200c0d681c1c5080082c890152070751402560b41c000985084180d640c41d0700204440c0c10064111b070018094031883e5505c0790396034240c050345084146000d80c000c58041000030170404c089c0c841c1002062058413610141c0d1111002c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 135234442 1250 135233192 135233201
    0x1090207060b10091a070212030310060c03120914120d0605030c091503030d020a17150d0308090a1b081603050703030c03050d0509070f0906061202090102010b0d0c06141606 76
    0x10070031700140801400000d0b80325400121030300c04100c0000d507a00c0c1040101501e00400d258080d00410010509101c0003983c0700c3d50114203440c0503070b40456040f00b90f06189a00149004403204188501d030202031404440c400a0080c419105608100b00d560350007e060b220310014185581c0440d44000140c8010b01d403065280c041c0300050116130400c802c10342d69230201c0e032109659002181c01407001c038800c1c406022159071f01c1961101c54800c00070041c0702241590454040090500000c50700003600340008011550764207800c00c101c0119a003000303c40b615030480c18024082c1034094103440b04080a10350900d0341c120b95100e0000e055141c0380d9101203440c042102d108a00300501003080c240c0c11421401064040c045003c00303000f4044c641041000904400e40c460600d040c140202040f01581000036017582544049015940f002445c00403401000c5d0390400540c054929458882485407100490058400a444054140000281d20707001c6010b0394081c1c261700407102c101c0c7c10005450307402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 135235692 1250 135234442 135234479
    0xe160b0c010b09040308091b030a020405220303060f15050703110c0409061b030c200c0a030503030708090316031d10020109030e0405010303300501090207060b1009 72
    0x10340c000d10b40d000601c0c180c0041e10b040c3c002407014030a00100100511080c0100b20b002c400309200e919000012039100e034080b6034040d1140d69070b1030000f44820030f001c1254071a05040c698007a400b045502c0d0107401860680030304058041980700100f04115041c004441001585d114581006075a540c101c0d042d16015070046418000c81a40a041d80c54078021501035901c141008070303d000641a00d20543c0455440482c201814034101c4d500581d00850711414101031042803040031003c1c0000c80d803411202401070f94000441c40700003c1071020210145000d0034465a5804036522881c5042e0b030369006050f10740c0c4001ca0803000040000e03000d120300d0180c9003c1c40b107002d441c181d51200003c4c003040b4400c0c2a400942d443d13107008000c00d688248a02049401120204059411610020400701100414035844400a0a0440b10480380000c80040a8217000180400c1d070b15607803ca0b0203034006c00300c126491410700d448503031540303004000c3c1c40b41e80350180e5515a0b55481d02d00c010145410180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 135236942 1250 135235692 135235717
    0x9010b04230d0609021206060f0f01020703050303040c0509010b070507090e160b03061005030f180a050304152c0609010e0a0e04021203040b030c130504050405100e160b 74
    0x540740441e80c03100d810400c00c0d280218000100781d130203401400b101c01140e00c5c1a0509401c60002c00c207031640c0700140020310042c16074054a2400400c0010b0b8900b22050300060704902c004002c0000f0080500342d10750641c4d0080e2503001d4075036a10700708074209014500000705243c200d02c90a00500d43c0c564001c0c080402204e04542c40075181c100240010f43e02c51b0413000d0790010000401019080034010b000c0031004910b800c0d40703075240104450030000c2e07003e42105044e4008549a5001410400c0301c21040c5401c82e003600c0d81d442da04c9002c624204040c441980c08603080c0312515003070812080b1400f0004040c20480e4100392056403c006066110b010300c1414000c00c803810b841c1031b1300e40c5a109405400c06c600003404505180c01000310741c849600d10910503900800003440754040c0749051300c3e0032040a0800c0d40e201c0008800d0302c03159481c640c1010390854946000c020030b00100003113903440f01c420307140300f00b0003a400020200d4841c6d036092441054000f0500e010480f0780624070050181c4051710 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 135238192 1250 135236942 135236999
    0x30706080402091b072001050f1207030605090c09180601170601050d020720030d05040b0a030605040e0102031f0501090311120f0717030301030c031b030c080f01060509010b04 77
    0xa8403e09181c01817901942e05c3c42601030071081c02072040c641c540034080d09080041c10544c54004035542c034403604054072095400003002c90780700c50190300120042d0100612015107850402080c45c2c0c2e42d0414525a84101c2e14000072050620650f4000c0340914010ba4a2400082c1400e140036006a0090040b5042001c100920340b000b0f021803010b070810f28820000000c44003808a0340121a100c0f010b20b1074800c0e00001101e10b005078001d402c490403038180c4d00c04943c88001d054803c0d0000c0080f54444e98001e81018001e800c001411350096200c0c000d541040c43c82c1e504241e094500b2450304c0c0c091103010849030b050503c080740f25140610080113005080c0b41c00b800c1d19035062130078900c0007080321600303a01c54002031007031209040c1d002c4094002800110b085602d1510b50050703540e01c0e480701810152612000345650850000100043c45e040910500e010b40d41d0920f241c4d460642101c3c010181d440c00e5008a81361510f01d40081c1200d110800d000e0400e410882d05140500541c4805048800078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 135239442 1250 135238192 135238231
    0xf0903091e0e130605090303010b1209010b0d0c0302030d030905071716031101020f010c0f0c060b03060c1e030402090408030903040305010c05190302090d1103010e120d0b03070608040209 82
    0x941c40703298407402d8490b80f040540c164600d000d0055840140201100e90000e100500112030008161107076016a1500180c841c0c88060b0000d0041100402440c0c00160301200e0006210000e44035104880c4280c04079580f128040800300d00315421804024a6500700e1001008100e10b83d07040b000c2510304000944125640e4040a4861b00c3d246a000b00c80d820066280c080f020340e01440b1911500c0d480b40001c0c01701401041006160390b14018014041c0280e07041c0803c00e21a0581c003003112103501901701e0b107003803c1c00c0300c081d1081c0c0c101207070800441026148880c1100d1507001664083c40c1c0c05807030764107030780c80b84c0d902c90361103402c02413621016210030b02002010500c00d01405211800d2078550713954030307440f40d6064140c94000f84100024507004000c3d400c001e0b212514010100b64210891a0184c4c0d12880042e01600700c03480000c0c1540305103609014000c4c0601e00400b80844011130800124103c9424144c64100e41d1082c1c1001c80e002c0c0001401500f01150380c02d1380403040d5440403000704078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 135240692 1250 135239442 135239459
    0x9080c03120c101d070b12130f050f060901051501020303010311010c080f0306040b04020a1710090f0204080f0609120705120307020109030e0a050607020d0c05060a0c060f0903091e 79
    0x2070080704c089003100705088150301440c0c203220b402c001d8031701c86e00124135000520360040c5290001500b2001c00020030800c1e4000e10a80003e824001903000c400d07a580310254054941e1784a1050344e400f0340039440c103804511641c6040c1c0f850590100183c01235404e44e8a107072140e503003050499000c6070500100d90f5684002800400050400d129005003540d2241003c40502c0102c400c6a04103074002c80c0304006190100d034124030980c0c1808403020b0000880e955007410003072a44002d130f0000054505207881c3e500f2600403500500b060341d44103002c4401e0b902c50542d055954000c240ea01001c80d401145113452035040101c002c00025000c4c00441d200610349108a6840c0e030700c129109070040c1d41d1100c105007016400306010142c014200d07a1724161500b800000b800c20710441c0002846000c551049900300545510b41d80001d02c1c0080c0610b403503054a69018100741d440b0101200c4107844c0084050f00c0500501c19292907076099a903c0d1042c0d420020815521000c1f40100c0c925079040c2c080c00203c800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 135241942 1250 135240692 135240701
    0x4090507060c0b0f040f0b1e1005030c030a110904050307050a030503250f11240103140102040e010b09030114101508010e040f0f050607090609080c03120c10 69
    0x211607580c0340e4a201c02c5090074807201501800c0913840c031038014144130110382c41d250741d20701440d00b182c5000350a0315042c41c150951103050700c41040750301c6d07500c1c2004801250714403040b040b6802078040e5001000407104041d02c802c20040020034105e680541c0e02d4540c144185501e50281c4200100c0b0300c3e100494440ea85040d840a0301240060000020042880c00110010b01c071076080c0002e01a4040321080041d00720708203074207141d04000500091f000d000d6170401c031005480d544a1840410144007000d40241c80b08240000e44d0b02e0f204032000300060501c14421541214000c0403140020303420401c41001da940b14880465040d03481c1c0c02500d4503155045c41d094000c44006c1a4108068071380860038101c10340381c1a01d14140213075000108001c0b005100d45507402988000c0002e800d480302c3c50100880d0a030000007074401d21590b0100f00d0540e801408a030141c03280c50300d500328141e6603803100e140d0f03944d500c130501c6070503800031041e80165404800141400c44e102c041500d0207541040c00210403203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 135243192 1250 135241942 135241949
    0x40f030c170708130501030c0806012a05010207050114070c2910050f10080103060e03040807080102090910030206090904060b060a0306090506090c04150306030b07050a0f0216030b0604090507 84
    0x144009000c013400f00440d441c50f00108001c1c201071004840b503242c0070f007801d04003d003004d05200100e0700c1e50160082c01c620140502c82100e0002000b590703c1e0401134000d4020030b40132582d5618105074105140d84980304188581d071207685800b804400ba0703072200e0402d100d20a88a010000c54802e00401c003141043c124172840e0081818960f07146450100101000140c5202d4004c0c000504070112240c0d02c0364104d41529000400410000c154104481c41c600c01c0d5446280382d806020404150b400c010340007404240c00855580e151600c2e1143c860320800424480203522110401ca104100e040608116903c107006650001300300c82070307030046462031703010340068800a40d688000780041d820611690341c10510903900071302c0d98a0a44101e648038400c034060401c1c0304403240140d51a05129030003c101860b80a07010380c0c0d041c14550000303021a00309000c0800030030722080c05607100501c001a022070384040d20068a80c4240303103031260070f40782c5400b902894005407104e0481d80440e43c00c01420005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 135244442 1250 135243192 135243203
    0x103030f020102161a010b0f040e090319050406080603030a08070806010905031f0e032a120403080912010515040905190b040b0906060a0311060d060801020408011103040f030c1707 79
    0x12900d0018035002c05c04050300210140c00090001d22294003410050b102510f030890f00900468443c032401520354024015101348180d00488080c00e242d03030020152003210169100c4404a1700ca000802d0b881c1d0042c6500b2400040340000082c0300310388915000d0384c00482c103060514001c0d13155404070f41407410124640007034425042495400c841144114040210341034040c0d030070243c501d0212072280044100c0d103a03042c0c0480420b03200da080140700709141c00000305001581e8696900d0089419041078648a1040d03034212028001c001040c060036118290302100d4002c00002c0d80100001420f02200c152268855100d150381d509603a405420359940c000c82c50715030545440e18041c00f21000c010404000b44e00000144401c80d180c6c150740c5d01c140c0741c1c025800c040c17607040c80d0049500c80c080c1b600c004a00e03c0c01c189001900400c1980208181e4040a0092080201401d03a5000520013518010a64144400e80f14042407044415107420f5108a5244020022a0180351100d0700041400e40f0b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 135245692 1250 135244442 135244463
    0x190f0303052d0610030603050a020d050f0d0c1208090c09370c020a03091505090d1b0b07030e0402091c051b100c060b01030b12060103050d14030103030f02010216 71
    0x40915101240c044c20b540a4a4180300c80c030b09603500c003506c032a54900024020040500c4040400c0000d220603010240100c040b1541d17401d68540091429200c004103684250150001d850343e2841500950320809030380000b01040c01c1c5c02d00901282c01360003801e11040085c0750006500c055106140703904e0820180e542c40003941031403400c40045420204c1100255440315031000d00290700300800008481c0c3c500e05110380180c244001791003510450080c076a0124070f020440f0304125400c401d0103107030b40d0303504442c101e03658884102841c10b100e0403801030301069040300382c90102d1a25800400c1d107481c01820b4030424944014103500250038900e001c441c1508020310321081d680360541d609850364021200e0303d6910203c2400540b064952040141c038241c4c9a0071100c40a90103500261618030307000d020124980000d8184988a66080c00304503034a009107200f09080714800e82d5818118401101c03007610710b074690381c1c01351030750003400c2800700955409020f801461907140f41c00a421034010445c400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 135246942 1250 135245692 135245701
    0x60f1f03060b04060503030a09140609120a1b0b0d020c1c09080d1409370303030605040e0309060d09080f03190e0706030c170117190f0303052d 63
    0xf05880c100c0e004507010b0390080c0402d07000359501c80c080030101d0b40e1952540301c0f0702a881c004143c40c0e00c9503090140d041000c1d400f042c2c1c000100012901d200070302800000c4e0900d2a814001c1040c40101d2003100c83d4400e003441409401c00700d40d40108038001d50602103500c8070740144507445514600c02024008140c0001040100040500000304020001c3c9415400040e984661413041d0050507106401001044d44e484400c01240d030005902e5010751a400da5400010403003082c1106003800200c00003400e26000080906090143e845107801c00000b45007000840400e002c82d54000c1407419012503251400180030a0090004000580c4d07101101d5903a458000312129055002900c3c030803055203040801861a030340401d10034161546032602044440750413800300c4541e40012081110b032001c0100000d900305003a12000d0f04800c9000a8441000c00c200d80c43d030442c1407408002d0080d0411002c4000003920960140e0b60269480103e58039411540002d911000017401004007404081c00610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 135248192 1250 135246942 135246949
    0xe0106020f010606091809021503090705123a02070906050f0a03120201021c060302010311032e031a040c230f03010b0904051c090305060f1f03060b 65
    0x1014180348040c003d004451412030020700707160003413203071041c0907204180c920948001034200554545d0001c0c41560340c1c40d440795502072582e000781e0300210544159200018281007020029800d40c212102604807980d140034100159040016000c400d0b0900b9400507015845141203503c03c0c1e915a401402a103050030911400c03104181c1205214045007010303150795590b0700054000b943c0d4440c80d4001103000b40c48041c0d02a00a2204039400500c0c203070305400882c05540d005a084234000d90b03081c805406070f552182d41500c000c0d02c0784c290f003108030002901c142038000340d060007040e84202e6450034144d41c5e498202c05081d1010520800c185050184020311142e031030f4020240c50a04441000050403070040195406088413440c0604003802003901655401c0d40b01c0d450609001d0215006450035142c002d8131440a41c1068903528038410440c540d191203002c0c1d1509907030b4003100419450f143e10303c0c081d1000710010700d80d80610040b550044109034690358480000c510442001c1600484030040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 135249442 1250 135248192 135248203
    0x90306010905011827060b030105070822050a020a0305030c0c03030a1d040908030c2d12090705060f040801050606071208041502070c050f090103020f060c01060801060e010602 77
    0x16011a42000010b0007501103142207210140d440302000900d04d0750b9208003079403000ea07108520f17914500864a100034028160801c0e003028400b20020170665032820300959010206648041d02112008580c480b000c8180103155001c0e80501c0171102d0005003540011401c120681003140c1c0e82c2c00100710340e0035000302000405942d4904901850500f00c2c00036006011503250001c0481100da040171010441c1c80315404403682ca07401424540c5c2c0d918011844040342c0e4004940410000898200002110403880e2303044641c0600030589440c00002950204604030040c220391018014104000360341d6441d98014003242c41e1051003291501d2504c40c0c0c803401c40f0f40080026020300300411500f80040c2c0209405103d480313030750820801c1611a03050141c428580c600c0541d150314800034252061006103450801101c0c1c040360344a40100000c018851400803c4c0b04c0203400061049685c2d0740c5141102c0034102ca040d00400002d1416604d5200b10300391982c95100400e110500c03030040c0500c1c0e5040c40f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 135250692 1250 135249442 135249449
    0xc0606010f020d120e010203010305070e010e010e010e0601020316050606010e091e07050714070905060607390f03050c030706080703050604110d0c1b0b16051e09030601 74
    0x70503100400701c480303000c0c2d11030034040c160504200c0404000c00e00c40b500341d8003003840c103039204008540b40c2d03850b480c010303540392445c0c0200003070030901500008180380e20300895816505000005185a40380c41044000d082004d09080d055000c1881030b0100b6000c1c42c281c0b480400c0c020f0f4001c040c58100003001400742001c070403180f8010070100041004a4106a1204070301004400d4410f010f1755491351304540c180101c01008207031900c5108409011344000a0000035901401005c1206844400402a051007803407001821200c0301c500c04595120806400602e0994124500382c0070b94030101e5030764202c051604541c1c040c46001405200b4084100460950728000743d005188180c100744015007000c0006003c802016103a000041c03ca07282c6801001d680001441581c0d00c0d0380042000da80545024040c290008039202086e200413100c44103519050364000409060980f03441c071192070862100c46403802405000c008862205291315509481c14a141c41610f031500c0014040604210041c4d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 135251798 1106 135250692 135250697
    0x28020307081b040b010c02040c03060512011401080a02090103110a0905010303031407031104061805060309060f07020a020f0d0201020a06050114010e1c0b0c0c0303010303050c060601 80
    0x5150421115030908200b0940c810000c0c0012035403030400700c500040d4003001c0340c800340c105035000c00c10300e04007031401040044d11440402c81d6411b4064401700320b42e40d01c803492007150b002c4200443c050420b050103041116070640005001d03003018000600f031a158119605207039600d81e5840c0c4024003090605001c00d681d2412b02400400c40186100540d8030984002840c40d4400d00c10410181600700c41e650404e03042840131a4100c100f41104d04840d44076050115182d512280610700c5460301c0780041409103000c0e1030520320716002900c403400395886800d0709801662012580e5070700c118155850031502e0705a000407442c0c5040280050203071490000086030a118a044030300c0045420388a90744101c0320182800040085200c0042012a043c904d14000a9840c107038035400c61540a030f01800c056001c111141075500a0340100c4c0454400203000340007103810301060354400303001d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 135071942 135251798 := by
  have h0 := BRFrame.cov_init 135071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 135071942 ≤ n) (h2 : n < 135251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
