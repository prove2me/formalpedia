-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2499
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:45.861718+00:00
-- url     : https://prove2.me/submissions/bb8f0ff2-25bc-410f-9705-2e95993f0efb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 449280575 ≤ n < 449460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 449281200 625 449280575 449280581
    0xd020d020c0d0e010206040303050a09050a03091508040503160f0602040f05090a05102304 41
    0x1014210000400380d0000d0a941c07085110710b01d61107481600a120380300554006034001d003001d80d5036460480c05484040c1800d60200e641d034400d00003140c0705200001c0c440d4002d4448059036031408068100003948020103608107d10f0006100020720040308035200b1800404000001002c9414010032960366010000c02c1c56100080000d040d88035003a480003111000c540d65202c40d0b48620180050b03440071039403a040308040d41d0081c001d81008d1841c100b0f100d0904402040303007030740102c081811 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 449281825 625 449281200 449281207
    0x12020906040e18011401142d0910080d1b0605191a0306010504020f0d02 33
    0xd04400a100c090603d06440c0150b00d00c20300d240300c03000580c180310821034024142000a070549040d5100547e05001c2d1401040000151145001c0013074132091108406122440c2c00700d02c041d008495252040c6c42e182400701480e4002d0040c0f0301c0c2da802008a2000707030350142081344002a14224068051036054032a00c046440c1100c3c0200321a41041150202502c0c42c03080c00390326551030a108030a0a02c83d00441d1b0b8034030381402003034011a80000c40500e81e4032080203aa40b84446000e06558 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 449282450 625 449281825 449281829
    0x30f080405091003020a05060a0e130b040212040210020307020108070f0c230c09060a05011202090604 46
    0x50f58100d2440d003182c1c029501501126202c40c00d114103403069070464004103e0303c804400c141d050004182c01c0b59039501c03900094000e1640000350680e03000e90b61b402034540c105010b0205600e00342c0030510440803180000c61504615034006802c2c10340051008081c0031010340c613519841d00a412411842e640100c0502c0b020103414802104000700c1c60300d400c980c0c443e0411000d000c0c00c04010303c501545005000c204194a040011960540d8800307208252680900a038032103902c60101900c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 449283075 625 449282450 449282461
    0xb090918030a03061a0c0d0e01090902030a0b01030b0a080a0f1e061a1009030f08040509 40
    0xf135116502400800c6007440c422682840340303003117107160000003852207840e15103c80b200300070012071010010044e03110300030310406000303400340c00c541e281005000789004180e105509804207007823444008040c68210401c0c0300315010000507115146841d910315070b05030f00101044a42141c40c41106641c3d04440c8140f0406c00d01c1074000240c2c500c000030b0a030038540180c4500341c1c41052541014080168004006001c580d44080302c1036101d00140340c281d00c180103c2d042550414650801c001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 449283700 625 449283075 449283077
    0x30f03180d030908120a0e121b040b060309030702011202070c030f081201090203011e0b090918030a 45
    0x5d00e540120309120010381c1c0d0240e44141840d01d80c8451458142c41c00c018207070740407a0350280c16141e0769440d1103540b05903149001c2e08076481d110080c610511021010b191146018000948000714002d04c0c469018410040100050440c894850940b0782260b01409400c02605d44810305101d000440c10f6420740d070200000300058542c00841c182c914001c2e05100d0240116100702c1c00148502912940b440180502030f42410611000e6a00117506090003044001ca141000c3c25036101d004404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 449284325 625 449283700 449283733
    0x10608060607060f05100e1b09030109020405090d182d051c02030f03180d030908 37
    0x5d110b0034041745d0745260702e0440d00004200c0c4510f10501003000c15010b03d02d6840b814000200b0b4551405100003030040010307500c041d4006003003100f0800710b00740105100c20034110759180d0b0034104540003412006070215018540203400011820b0010901c00d200100388a04044601c64002e500c0d10041041c108904210595000e90000b80704114a004c3c8102500c00d42450000c505000358a40001012905075121a0007151414019004d01d40b02d49200c0025004040455000088040c150b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 449284950 625 449284325 449284331
    0xc031009050a0b0102010e070302010c080306061c061d0f07030e0c0414100605070803010608060607060f 47
    0xc204800760002c0104584014085423188018800a404a1b1645e5940d00c00b00308040c00a6501c510001c10300703454820780d00c002e042c074080c01c04400071080d0b565040c1800081190350f8400700145100c4003041c11460070020080c82c20340d008004004158480c2d10309040030b80200030103640c2d040300510070701c100c010503210103001500c1121003115083c9004000220b07240038000f150310190b0006400d910316824030800317a4070400080c001d19040f00c001c00c00345000c154240f0600702d014400f680c0c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 449285575 625 449284950 449284961
    0xf0f071a07080304020603091207080d0c02060f16050c160504150e0c031009050a 37
    0x2200340150800d0110600000020318205242c2d075618454400200700034800c0e81302001280700c00200300070300c5600d03004a0b40f68070754840a60528a030181c001c0d02026451500708258002c1c49031020807401d000340c920300038075900380d1604045030056084010540781000428001c0700f107241d00c01c201411740041010441c01e031841c1031809110558890100c015100303080660104600c0c115216420b6128008a94040c0c0f04e848150610003030019070307030000e1030607405c03e402d0162a03481684071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 449286200 625 449285575 449285579
    0x9071a0a020106031e0b0a2c0c030a0605010e060102070f05190b0a020309030f060f01060507050f0f07 46
    0x1116401c81e00000140721f000c142c841c6811907100b46c400f01e084816442d041514a55602d030150801c0c1c03107500402d00042d50100559021031f4410a401305071545000c60180c60200098441419504141c10500c0f00391400400b0360120f40045510700c00d1103400c0342e0020543c4d91a5040f0303a01c000c42c005901d2448540001c0101080ea0084e41210080c22184448940fa84800e603041d4030064a0800104a468031410151031520700403410307661200d05030f0b202240351000790303803070031095800030001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 449286825 625 449286200 449286203
    0x9030509040c18141c1e15050703050c090f2b0b09071a0a020106031e 32
    0x21800822513802000d5034000032406810310390354660202103040c1129080d0f01c0c02050030710301091070b11005805002140800f0390f1203404c01031003682c1200492046801000707203944485d01242035a00a072000030903084100a9072600d070a02c4034031841101805400007003641840100c1c480841c80d041144906000c14004040410170780c8401e00e5000b506110007002d106081400c94819034042d08032000302100001189005103000390402001103401080034030345410701c100c045074556102e000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 449287450 625 449286825 449286857
    0xe031303051204030506060108250801050a081506100509030a05162709030509040c 38
    0x2203401d980202c5000841c82d100707900000f40240c000001081c0b042d401420300c1c913003000519142e00740c84400c400e2248800402121541c0007e16428010022030034036062030009030141402424203000e03145200c50403610054041402040706411b40d0040380d02c280c064800600c4001d041d41c030482c0c0c05083c2aaa69000680180040b2070400000568020b0403490b2103070030101c0d0501a03203421400c105002c000d0101c0607042d41805010021960b5690f513500c18803c80c00440d440300d5902c8695412 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 449288075 625 449287450 449287453
    0x21c0f14040b0409050919050316060b030d030e0106060201060317070c03050d0f0807170406020d0e03130305 49
    0x100c4080c0038000040a07d200e250f59100c0b5100c0c010b0b03100b501c13004500c0141701028406c040d0007881070480c1c0035003601c4210500e0b0704010b0107007000d144205510360030b20320001542d038070500c115401c6982000700070300c840110300c05e5031406520014040e64959000031010001c20b409101c0c41c0000c4456444100800074034500140408a0051108040c80001c0c0074420700804130f440c0c1075034000c1c3d004000580c0c4550005c1d80d0303401030201802c1c20059200c080754034212418001804c0d03040d0780c051710 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 449288700 625 449288075 449288083
    0x60f161a010e180a0f060924091118010e1801050a020a021c0f14040b04090509 36
    0xc10010b20b690004090241d16003285c10161100b0403600da41c8024914620141c600d02c0d002d443d4000d64410410107201d0382184804001b42d001140e0400b0303940c1074111b0f0500b500c81c403058a1b02d072040f45142d40390241941c4041c41030036007c0d10381c00c054051078040144004119402c000c10069206456406821040069026981240030704541d51000c69401d01c0450041022401d00c050b695125681c0001e0100404610910341134640c50400c1942d00b0691103403030040d4981d010801c40003803c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 449289325 625 449288700 449288731
    0x8060105090121020102011b030e07080102160f051002180f060f161a010e 34
    0x200c090701880d2140010322180f0800c503202d14003610005200c8a00880701d20040b0700500e240302440d00307038071541d202011506616070070282c40429000f00311201c054981175518201d2052610020542c9140d100350b00000f40e010b240d10340c8a50048007074408007000c3e010108160f81c04440d4903860802c055085c035206140c00580425a0b40d4150390741402d0101c4080003211324400c1c4aa0701e1818020f1000c00c0f01000790310a203141d401170381c490841509503520110168007180603aa80302e00002d055 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 449289950 625 449289325 449289329
    0x15141f21050933070516080409050a0e120405010507020406120f0203070f0b161a0c0301080601 43
    0x31030001079010401c83d086004510001003983d44598003601604a02e08010b030b07144240d50710390344650b03006604002801070781d4109001c8403100c10320819100c1c00c2d02d84c01800100c01405e00c03c800c0c0c0c1c05141704c0d00d8140702d000144d01c401c545e034990003400074000303c0600c2d18420f4040e05101c19003000c0e446c4107e00a00c641c00020851060704450041180e0710b41c024140303445000392a20701c08c69180e03e001ca4005200b0701a0040031a1501c014034403600518180c0e41d100c3d17160800d103e240400c11303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 449290575 625 449289950 449290003
    0x616110304230111010504170903010608030d09050d050309150a0f15141f210509 37
    0x5000b0006c0d82400d0380c0e00c02e08000c0360450740e045031101003610a459070b030030340c4440028201e00e001c403a943c5404620410180c501c181040d0f55074062440442d858602860403684546161800b0300118410490380c1c00042d20701030328100c00a07585611b070070381201302d91140b2164403912042e10070242c2e19042200030208a0101841d004072440680791240d013030b00d91001140e0190a0905144102c000f0149245410f207401c1040d03882401c14042c000110404180030b0004e0180300d41c860003800a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 449291200 625 449290575 449290607
    0xe0d1203050c03060a05062808100e0610030504111e0a0806161103042301 34
    0x802c1900e002d460020029a0b42626110401009602030620786c032200212905918a0152400d80307002100e0b00360721002c0b110310300107401001c0c100040e001301d01009140800e1000301c0c2c0315050491144001c0e800c000810392160700b000c40c4003071032402e0402d85c04414040d602240126507084800c0c80c9600b55010710341030b178a40c448161509030403110058420710781c401c1519800d00c1141e003188031400340401e80b8603003611030510442d0100300c0302030a402580c3c03072030190001b541c0c0000391804020304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 449291825 625 449291200 449291221
    0x51e071208120a14130b01060c0201021504110d140d030902010207150e0d120305 37
    0x2103403a00c0001110341041c0c0c0c11500450440448aa442c86034030000f5003054501c0d00358000c0040d041004a10b0b10700c90312004d0701e008800c2c24107107030f0b256041aa408002407501a0150748001000c2400041082005a1141c071469403590560f80860105684060360142121680550700d5400c002c45d60410034800b1134092031405115401c0076400203519444039008050685121041070800e0502540a6a1240d040505405600d81240c145000e44890740d034007a00000341003c02007841001d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 449292450 625 449291825 449291849
    0x30302011a040e060402040207080c0703050a0b09150105040b03010f02070606141806130603051e07 45
    0xc035a40d035030f40350300001c0000300145080e074010300800e072088602d1070501c0c1030341c030b141c41ca4607075180c10498060344003048072018050300703140181e4005c500d00300616021140140c50803a1100c180701e03aa010f1619022003403801cae41d082d080b03001040e0004204549400c068100400a00014402c5480c0390b6507000d03811240b81031090100c80075240805461255841e00310034090006019201c503005941c0e503800c04000a030050040d00c907000700821548040b403800d04078003410080654442c0d86031440c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 449293075 625 449292450 449292461
    0x92506020c0a0620010b0d0303050403021501030c0b2b050f01080604120c030513030302011a04 43
    0x3015405010710324601c3d00003001e400341d03205240040b90254411820300c41c004110464400c10303072078001c010300811030781200107000e458004081d000c9072202e034030b040c0d9030710074041d80b10982032800000850304585122002f8032813ca26107a2021003417000340074000e4100300e01041c82c1c58a040c03174006410307040e0301c0024294880c108000c013040d242c000c458a80c00c054034080001041d41d003030440752405240d804c90700259000300b0000400d501503211100200510440b241e5034440807040200b103c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 449293700 625 449293075 449293079
    0x3130f090203010b030c0d0f02030c0c0d0801050d1401020c0613050c0402030c0909092506020c0a 44
    0x1c2130003018650b403100fa04d85412a084001300341c00c503546a0710344000718100742c000395015100d84900192102108210f01c0c0c20912070321100803c120402004000c559680e030b0f0810308954006001c0b01880401c041000e001e4450b50744001200e126140500041c1d05684802c4403015001c0c005a07103071030030380c4d00030001a44001d495003d81c040d02400720301c0192402000c07035a04a80b00d44126644000f88004d5010800200300c1240c201d02c1e12807100700041a0140400d042c0e824080b1103100c4e2041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 449294325 625 449293700 449293709
    0xb0907050306010b18090c0903010f0b040b041406150f1201030b06090106210e03130f09020301 43
    0x1725034409400c0c05031090718140c1c0c8a4440c070310440e0702070042c030128641c154280184034146940c103521582542c48110b4007406803c84803c14002101c0304c200305020050303056130000e4110709000d14110b07403010020504501d89040300c2ca2324031040c1c1014128541183c443c02c01001480b074401d040b281c2007141212030212a524082000d050005180c002901000042c1c102880c0c01000d94002d0742406120000d0b00c0c5e0768040351141d00002c01070350184104440f00d01130040740c1c00807184256810b0f0b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 449294950 625 449294325 449294347
    0x150c0307080709081c030b04140a0c02070305060a05060a0e090706091707050105030a06030b0907050306010b 49
    0x3406800b8050442c0b8450307642c0200d0604600d40007584c001c009001406942140103d0b4509d04900000c1c00b0161032140144a420744040c00240a81459661029a00c0c1402010b4031001c40d51344020801d40d549d0440d581d00201428000c020301418040c22854507250148174100c0400c40d44400001c400c401e4104a02402d5000c0024040503481c0c50010741d55a03000501ca40200343d40d402002c4001441c444000c0d004554400092501c41d0400c01418686807040e00050300040c800d0100600070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 449295575 625 449294950 449294953
    0x9060f042d05010819060609182304060f020403061418030d020705150c030708070908 39
    0x8440b44503070390400003180c021400b212600c4801c5202c0344408401030003283d0f104c00000c2c10303281081c400c07003a14011409482500000f1413140c14805030000c500500107243c0c58480864036400a007054406030b54a403034414560a5038402807000303500c50300010440840804050a05c00310081040d0080203010100c6201c0304408000c450220081600040c3c0f11601e034280f1600c2d281090500c4a404c1a002050140482e10200a11702c5503034255900d01a50f5505c4500b203a0f03d00c828410000c19 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 449296200 625 449295575 449295659
    0xc08010f0510111f060801110403172a0309041a0a06031109060f04 31
    0x301c42c800b00c115800300c6802c1c40c0f080c80c0e00c102c00144c1840e01d01c51542c0940716410400c00101c0d9401c120007142580c140d8280c0025484040c803080c80802e103820240e0b0480080d4010071a03440c600390f00c840b210b0910380c0302c5181d400400d06180c0ca000d5800800100540c41e411203081100404494000b01400320700ea040a4104402903014044c16010343d01403041e1218550fa0a400c160445002640da94000c030013401007480042803c010301d0700a450480c0d40c10004030500f191220320b0765015024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 449296825 625 449296200 449296219
    0x3010207171605010f0209040b06070c03110103020c0d09080c0117151801090c08010f05 40
    0x40c0031000c15038070030b450700c00e052140020315001080d9500b045002e417104603007070b000707840c1411084804001c0c880301c91041003a2032080450085c0180c010100810200e41500c01c4d00050390b8060601601e040c3d061141c848c1400c80003d08280861141201480030500c1045241d02400013070810300240000e014241560305402048001c48440c10001d820340350b101c85080d1218130f50480811001943c580d1203410107481c210400600086203500006119010565407004494018008010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 449297450 625 449296825 449296853
    0x80108061602070e0c07050d140d050604021e040f0b13030f020a08060f070e03010207 39
    0x200a5514a05011154a84100c925164a6211440310780d03005070780300007400d01700080100802c04280030703903120300890341008011540780c10040201845403840350150a2350b038400189031550745505503410a1510b40c002c0c81296854410480c2079445805842d0118050b03982c0040d0106059040300e00194010b01a201c04501c0d60b0390314060340f900071b00b0480c0d00000344400030032100c50400c01c20740719000c14101800c89081006010701122090351100307009034010001000401c00040191f09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 449298075 625 449297450 449297461
    0x61d0d090e0c070c080a0611070b040305030709030b010b0405121506060d0902031e0d08010806 43
    0x10071081070081071800b202c04085818842d840036219400e2651200826128080d07034105403803a07810f000c0ca1000c2d00b2011b104540c651030f44030740c1601180c1c03103d44048406410003030621003804100b40011000c1860020200c1c004d00c0170042059840341000d0612018101c1b50040c164250301c40c20318031003011040e0020f83d0b400003040d1a4151114490103011005e48100000a5054002c81d1010600407025001d01c6158134504070486000c00f41c0a04111103040c000d00c00c02c2640d8000401144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 449298700 625 449298075 449298089
    0x5100303050711031e0706030606110a2411030603010c030e10180f061d0d09 35
    0x484144150b0260752502804415a0152085c000d5031a101c6100601030040141442c0000e41141c1e11a0004e004009615030000c0a001c0002800c018854001c840b00010507001c0004c1d25180301d94548a4000d54105945030003a4101c40c000fa6009080c00c4000384406840c00c5400c0307040351000c2d0242000e503442096003a0420b000703640300d580c00d4013403000705e544880215202c0c0314100340c07150002c441b415618009500801146100508803c0400019001d6a10207103c014150380361401228 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 449299325 625 449298700 449298713
    0xf021b090c0d0203090106090e0a05250e0a05060f031b010f210609051003030507 37
    0x422a03541c8040d15216100d00390162a85a2000c801c1c020002015840b000a94510110070411009601e1001755a24010301c0001c0c03496000035000003031014800145000d483c00f42114079422030f103d001d9259039040803644a404242e0320700800105180403000b480c0041d81c103038040c1030480d0241d20418007400322000094184400d010000c0b480500c00e812050400ba01c80b4005078010961080d104094507441c0309510030ba42c200804120000980c0480310304803640340e16414608103a0b6600e42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 449299950 625 449299325 449299339
    0xa060b1e010815090c1c050c09040b0d0510021c0c09030605061804050304060f021b 38
    0xe42048440f6554401c1029070000304030f03200d10a82c2c12101019001c40e40c00109030556045490f80058440c041c0b1017030078400403a80c40760240010452145895804040030f03615038004420391150040c00f150380721009400c1c407200139841031407800950507220540c94190800340c0502c4118840b2582c440990601e140c8401c2c0090901409480d800104501d140321200e001100407401140200042d50352203103004009089480384410040548d0800c00d028001403045110301a81860190750030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 449300575 625 449299950 449299967
    0xa020a050609152505060610020d0e0d0204060e190c0305070e040213170a060b1e01 38
    0x40041310203034104121013510494030b50304002003031404030703203801055907254003414200c50b0350206c42e40042000c07002907032160341d4500140000010004507010350794099030010360b5404081760015004070351500c2040401c0c5600071034400f403136100045a9000070a5400c051803c2d050210703403944032400e420304103000c075005601c0c0c070460401000c2c080c0031503124041c01100301000c459101c3e004a030195049016403002c00161844030180800c48016041c13441c0440c0c80d0b401e80c0c00540d8001c1146 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 449301200 625 449300575 449300587
    0x1006140d0605060a02011b03092315040c08061b1602030708030c0a020a05060915 37
    0x1542000c1c0c80388800285a2034100141501e1a85138002240c07a80c10800c160326100c0709086000304140c01c1150705000f1400c0554000010b10804d114120b980c42d0f544401840e280040300986903c80b00107003008240300054801200b0350f02d03170303034141e07507031130321644070a8480d0079103140c011680380801c01800c007038081e4044580740150302c05015100f0301c0d41e80707281460454200500b44801600908640300840c5841034910b4090542211481c0c208221235011810300a40c1805841c9110000510317 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 449301825 625 449301200 449301217
    0x30906050a3906050709050405060f190806040807170a08040204020306010201181109100614 42
    0x1500c410703511035402c003035101201c0c010503003400001d8018074041e005540f190030b050340d10341c014001030740e4040302c1c3c0682003c40b40041c41d01904004d210200d0315501440204c462a86036070b0b1003401e0070001e036425550400045121014004011404808503134201010340c500034494030301070001503005001a00c296400b02c0018403e9000b0f4000d1250120611b0f103418072082ca6152005c09003c03200882806041c47c90700007810207010440d900c00342d98168550340300d0240915002000d0391b002c642c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 449302450 625 449301825 449301887
    0x16080601020c0604060518040e030a080709030203030d0b03100501030b06062a0307030906050a 43
    0x1100c408882e0038012881e5940a034100000080f000601d86600c501d28480175607440b0b40550b4208000c21007260a2601c9000c2e0041c0c00f800c214100020074415489805240040e680043c203a9070386045205411008000500d401d038040d004040ac540c14514051045604990304100198125030300d8008001c015441050701c1d00c10b98050703031010000140c48400541380950b80c3c4c0001c40c2d643d4080d05002d0105503d03540180104001080b8404c0c44503484000000800c01b00c5080510304455114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 449303075 625 449302450 449302453
    0x1060807110718020309010f020708072603270d051819030b16081608060102 35
    0x40300c0d000d00f0340c10704562803098040300003000039071040301d4840542d40381011160358000c0ca07008440f81680c1044100d400d2001c981c58008080c0001585800314903503000c0140f21465620020758420045491503806000702c0d00c80344102007000c00b440c82d00640121142001c056002000d44a014508045050030030360900d022a1320300040840d20398419415034000410051808003003842a140700d8004012156810400d540034102624020012140b5490f41c140c0380c0d100300e101c03030760040c0c0510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 449303700 625 449303075 449303083
    0x708151e060a26190c0f06020d12090203010e0a060605030d0c151b0203071a0106080711 40
    0x208110b91003000d10000f61040f50313a0388110310400d01414007121185c015004503018681424041100c84e4000030645041441385c2001d0b540106800e007040020700303400310080d406509140b010980c5040c04980c1e020340d01e114400030091280c0b6070041c59590480112018042010749403080c0201d88106001c07044040030540c0411072442440c43c8094020b501d022a44c0540e00c0401d02800700000b14030711050440c00034155480350340c90a14010100000901820148003041007807060580e0248 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 449304325 625 449303700 449303759
    0xa020d0605032b0f050f0304030309241812080601020708151e060a 31
    0x80090360603c6641141080c0e90124000898030304001103028481c9468160b0a442c800c9030000d04001041c814020304980001c0c160046030300a00c40e2500040c600040c0c2d4904001041e1810318580c0780c40c0d03036a41d10b10940e45600c90340c41195490248141440e2036a501c11220580e501d84650400c041540440d150703900821a00015000324015110010102403082c20001c3e0221040089860700c460090701c00d400300c0c9000c9000d41c8003d8422010242815803018450020900303509400c0b1404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 449304950 625 449304325 449304329
    0x140319110301061d1e01020708070b04030303180c1e081209041a03060a020d06 36
    0x414004036244040811551a0080010003900b03030068001400d0603000070440d010124401c00040040c82041094109582c170f107602c1c000300d64402c20100e00030740001e10440b1412511048413140c140c105120071030004e03050802c0c107004100c1d110700152131030794080540440c90b400c02810000e0903441c1d81002d900f5482a900c001000c00007002821241c915000035036079030f841c8107410301c01607a002c804001d621251031504c440036a00e000800c5139118140480041c1ca50500d40001c1d8060702545d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 449305575 625 449304950 449304991
    0x20c061902120c0a050606010e031506010504090e0a1202010c021504030e100203120c09011403 43
    0x841c2e00c81d10340307041c046041c0d112003541c9002c480300d005613800900c040d03008581001c0814400b07802003013080721580008072a4440540202e060002c107110008030303203a050145584031042000a44005144d91404801c03100b1800d028105590411421603c1c1c44e5000504842e56800091862980d88450a040e1a9041d440d40000d0700f1110302041015050307000401804119a40340c0d8101d01d543c0e4180300038200d0301800600900081030b0303007490300e8000b54903006941c000303070b8091580f40d078030040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 449306200 625 449305575 449305603
    0x1020f010501060e0906180a0e071e080d0801061209030339020c061902 33
    0x380326032400f03040c964503902c4900d800c85003801400d20008140c01d0140364032091078a80c2d1200004c260390300c82c01946c00030404a0601e07407083d04100740c50380400004500081d00d062029041c82d480d03030503203041c00122681c1075090602203401400a10442c80402c4048042e00c00210b25038026020707150103410041200b140d44c41da0360740101e00d521446e0a01e18250802a600b056070600d40302c1291003a440280381a91100700080e0861040e40c00a01c0302c00c02c000d000c0005035009001c403400c0344c1a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 449306825 625 449306200 449306203
    0x90a0603120e0f0102060702060c220608010312080f0708041b09060f05010c050d050901020f 42
    0xd01426020550031102c035020070740b802c441c18000c03000a07100480e50307424101c079440012380011012410f05aa41006031000036540003031001c2c038000103560b16440e00b1456201d0340010307170748500400c01c4c40213041d9842c01c40580c9142640c01e40c6040f050071000041d0240a0070100041400000d0030b11540e81210101c000d201c00100102c0c5507680310100262509000348418941c625900082d15800340c1c4c030124840d0340c0000901600d031320685c410703280c9400154403941540146000c20004140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 449307450 625 449306825 449306843
    0xa0813061515020c010203090a33120c0c0f03030e15151804020d02090a0603 35
    0x1c0368440d0705001c00900e24072401c10b5051004148452080c00210f081c004d070340000035030f0001c860150b00301a13503002414040000e140d1042c09440c40c0c010076000540c1c0ca503444001c10610205c1400b01c0c1003410020780800140c49911f80c3c4400c250484000320218411350703012400340c900524008628400c4c0c1440c0ba600c401014041802618160712600080101c0c00038450703100000548000c01e6043c80040202603254002c003014101e07412907805640340c0d40c0130402c0005044c40c0d0000703440c41031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 449308075 625 449307450 449307491
    0x15010906080327040b04050a0f0b01021f0e1606020f0c0411180609030a0c18020a081306 40
    0x1401c8c0c680c060520500e02c54102c50400d02c0340c05095100045041c1107101e03000e205410b86070050f1480c0010111400d07a1a071a004005030b407183e0038040e4251100a1100d50300a201c4140700415640c20280d07041c1d074080c49581001000150340c5c01c10f009440f0015040780c03810380b00703040540010300d080c030404002c2c80c0c160060003407040078402005118002c0302d40011000301c101441e00c1d4200308a1040068440c085808807010454440f001c001c40c0112500c02c0500142c410b200480000040c078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 449308700 625 449308075 449308081
    0x2011107050310112a151605090109090f060e06040902030a060f0e15010906080327040b0405 42
    0x113001c0d142070850305485848030f18200d01006e503032089078030700810310840c003c1000b031440000c40c550805170703035800e10078004840340081c40c0d004500340d91405440c1c0129031120742000040b80c090020749261070311184108000c58240000080d490381c0000460400201c0580104420b078180c02c000103880b618418003a41046000d40c80c440c5c1e200c00510042c0004141c911401d400b90002c0e100840c1490070401a500e4100c10350480700f5508000001c15031100e54881c1c001c83c0d48280003030028880b5013 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 449309325 625 449308700 449308747
    0x9050711071d0f040c030b070e06070b0603160324060506030c0301030201110705031011 40
    0xc080504141e4203040c4503002e1943d10340c1e0f00603c01840075078005160180e81c16040000c21616042190000981e1401104282c000ca00044003904010421b46182010509102183c80c040050009408003500f40c501a1803454840c21809903c0c42025407a0792003e141c0040c0c001d21690102000d054010109070726410101d98042d2541c0090104a010404030384e0301c40c513003410000301c0104940d0300400034a0407007610a080800340c00c000b818248203100501144000701240e449842010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 449309950 625 449309325 449309339
    0xf0804020402370c0302060106031e0e0d090501020d09031b09050c03090c0105070c0905071107 43
    0x200f0004511a424003c0103002414078586000240304d9441ea030020f4446006105803010591141004c80c803600a4502d9007004201c1d58804024070240340c1107164072826006d2440011a5030317a00d00040039400842c088158481640e0b41d80c20050941c3c0e20202012900c5521b00a981040c03040420740300c0481c401c4602800c87c038004680c0781c7c0303041e9202c90700e443c1214040504004003809440f0014501e100d840041e580404004900c46d40d03005401c44c0e83d150b00c510f80001070310500c440080c1130 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 449310575 625 449309950 449310007
    0x60a11160b0f060303070f02100903050a03030515060423210105011805070f0804020402 40
    0x26040e20440d4558039101d01040c528074000054a08250300494001180c0056a080281415049c0201c2d41070001a60001011640c00e204e06100b150181d1008100c510300a1400b45030000c0c90400f89100f1802404103010410722001103190f40c4100014150300d102c00200000e4450340302d505200c1c21203d140c09400160203040d04011f040761452901100318020389241d00c025104100c4000000546007a042c22159105400441d0480e001420040c90106940340d117200c68843e04004078804d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 449311200 625 449310575 449310593
    0x10e010314010209090412020109051203010602070603020f04050603060310060e0601030501051002060a1116 49
    0x25415414400e5195030081411200740e8410051001d03d07807603c141c030507445900683d145049601d1048242c1c00340c551100010058028060a80703000c41d41040a581a10990303421912882e0701d40c2c3d403c1d0128403910764060011242840100218a0148000c60b801b607005815550002c40c1c030700106055940340d0300901c040340c0f8040208003040d6410702c10340303004100860b088185894081c6019490741d1014265107840c82d2907416001c2000000821a03007000701070415a0102d032500e0070320000d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 449311825 625 449311200 449311229
    0x70b0a05010902191b062d02030c09091b0a02030a17010b1e130f0303020f01062105010e030301 43
    0x1054940c1f00e03c0f5800807800444070403400110f44440c1075000800058016290901240d030703000103241004416802903011440045c0c001504050243c2c0c00080c030740704ea2640080d9090b0b528a0244403240c05581070401c4812103001d09806e04142c0080400a00108104103081d281c5442007a001c650105681c0e0030000d2095419100c15000360048d00c0f40012244010700429080e2104040b9145094194680d8189540c0141000b548c0d0340d580c0d50b2180c09860014070080d03000300b1650424040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 449312450 625 449311825 449311871
    0x1209041a0d2f01051606180c09050708010302030d05090a0b070b0a05010902191b06 38
    0x1c2245105942c07861031100b101c001c1e501c045140c006005800f406001040804101a0040400090340d0101d48401c16a080c0031000703150130300d820358500e202405480c10160500001c140c02c140222000e6040c0d0707900030003502c09101545000c172115003082580310f174020765800001611344a2500103100321030044503610300d5031030603082540541e8010307445000064810400c80c401e0b1190050800b07003c5100d0314111942c81b00da550724240108801201904c294642a1740c1600c2001006452007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 449313075 625 449312450 449312483
    0xb0307140a050909070c02030c13060b130504060f030f030c0f06020307020a060e1209041a0d 42
    0x101d0f074440e00101744103611600d8407441007075000d4010100c45400e03000300101960320352903101c0e000b0b88481001c80d5a02c1140040d01c0b946e80201e900ca010702d404c203820070094440c0c0c1d4002d2404008200000c0020490b614100b90b0302d0354160602c014068005e050940c5140800e21010f0006800081030180007a800606400894050041041041c400c4901617445030030b10b101040c41c0715024403156455142c030b070780244a200b50100d10141c06003c3d200120f144003419600c1a80c05d4048501841d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 449313700 625 449313075 449313079
    0x50310180e0d2a02031f0902130b0d060c0c0b090304140d0c0b0307140a0509 35
    0x2820300000e003258288103299540280140030340d015003a20700a01e108000c4002441c4c404240781011844400400d003444905100c3e00b04104e60210303d10900840718400c0c030740815214001107803183c4d400030750004100516200840c41c1a00103480c042d66030318005101000ea91110701221005584c02e1100e0340000404119000c1e0300003440c0d40b081030445102444094540c0d44013103c0d0240c0c8192400080b02100145806000e01041c4e01d038000c1242100756150706a1500030803990200794198 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 449314325 625 449313700 449313703
    0x70504020c16050913031b0c12150b0109060507171c060f08030703050310180e 36
    0x269100c00500004d00c0041c1c0b0194400540e0700805800030340944114044201c10401c00c54184600d51501c0c80c07000080d0380030307181d40d07000d154600082c0943e0322880c260a5405034400d0107001681c000003030807450140f082c03030100300e07020420300d00300980040d4000010050f2000b2a84500c5141c1642c0e0400949075600d081c2c807460050300003156000f5007455021110300c800694240850741e04d054a10f907000529010040702c1120b0f010a400d000c806900b111080b10f8100010150380e0105c015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 449314950 625 449314325 449314363
    0x21050f03070e010f09180c02010902060a090509011403030a2d03051816060c05070504020c 41
    0x540e2079260b08045d210f160410480318207a12075459180c070038503140c13125501600d00030750008202c15005400b460307035a01c0f22a006802a6818818a0300070841034000068019440c08003140540c0018081c0d403902e140203900300d41c007481311060180b080c00220320300104121110700b10f05040180b62400300703e40c5440c0b54000c50042c02801e0b5200d00c0c0c0c00c03081180c8010700b05500c048090310580c3c00d120f0301c50030700c0b410007518125064011a40044c400185504140c000080e040c0c0c0d8031483e44465 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 449315575 625 449314950 449314967
    0x12010e061002060c0d021b0d050706050105031c1101020d021c140421050f03070e01 38
    0x1ca0190300c005903403409210481c0385640b170064000c203240041d41c005000d12214001061010364204000c10070200103410503a0b400741c903000c113441c02c44181c0c0c40690045109a011014480a581c1c03030661414060215081c00124418250245806401001c40d085941030bc0400d140360050302c00d18900c4c0c0310380f2101100700001c1d08594068003103000d0954000c0c04250240c10b40028145800c0c07141c5800000504025051030b032a1a01540c170766000f15480400503403680a080c140d035030803c2c4070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 449316200 625 449315575 449315599
    0x30b1605070c06120b0604090b131103010e04030c061109030c0a0605030604020f0c0d350c030601030212010e06 50
    0x180035032810990019000c02100740cc03607046404a504100050707859090480d035800d80140000c21542c10540c00100e00002c01001c2d11013044200c080e50394a9480e2030810034410345512651010803070510000e040c1e4909a40030f4086000d40005039482c1104066000d0305040c0c044100c0300100b007070007140301010521407800c00d4a03010108a030240c000020f0f010030851010040c0b1003a24003030000f0007e60b1076403298041e200b1200f141c00c04100301d540c540c64800a400d0048616601072000c010360 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 449316825 625 449316200 449316229
    0x70e01080708070803071b05040c0c0b01090c0203090103021e0301030b1605070c06120b0604090b 44
    0x2041d540c0c4044e00c0340c01c0c0545c00901c4440b0008440003101900c10282c10b905103c01070320307900003c0c21269100e081074080b0704840060704c1040455902180188404030003003000340d5a5600203501e80c070409960b1030405a000949540121109201c8182c01140d0b08002e82c1300c1d83c4034607202d101014241e900c40da00480344171524480e244203408680701d00380d00070800b42e8040e00c0c105c000d030352420a6007050b0030308507241d05410321181c4400000d400103080c200c0000c1800d0000b0818400501c2d1000e60 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 449317450 625 449316825 449316839
    0x1103011509230105160506060f010201111e04050d0b010608010b07110f010908070e010807 41
    0x200e550301e49003160221507642d015810048000007000d0100d00e9030700610840f510104070340d0f82e03c51a50300c5401e2890b1105001c540c05402400211010103882d0301c18850b10002401d101c0078182000c1c142d0024428003403000142c484101c0f4200408191540c03190700303105115104680d2041d0035814604001c08518069100000da907100340500c500003803d045800044240c00d9030340706102212400100d075890f0031644040180d015100001c6035451401c01c5441c10f980c2c0580031519030f1070f52822 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 449318075 625 449317450 449317457
    0x15080a0515040908090409050d030c020703110907050705030a03050a0b030d12020c0a02030111030115 46
    0x31140a104032807666858140d0a2051001900020100761942042440038842c96266405880030b030038402e501410081c41c0000703000d42100c5c070941d10710085500c030391014000105842c0741c03c00075407022261618240d1f83ca4408403094403950307400914900010841c82c0038103406412241c00f07240c480105003c050000d4003850355841d01d0648100010f04c540c00e0010603180c07a54010003016090f0b40c15200b03003264a8020038203540940075044c83c2c20300c002004100490031040000e403051407a24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 449318700 625 449318075 449318081
    0xc031c1a010806150316020f1c052b060302040b030a0c0b0c0f060115080a 34
    0x640055100344203000d00d115490070309000d8425a240d50008000b4020182c1c140e8506001005201c202e030309111035070140c00c04079000c480b01c05a0084001d640c84a85030f01c1c140100c25a841040e100a22030030140c13000501c21841e41c020054200f44848400d045a0316510340580d95250400541c0740c82d01510300350710000e4019008003c0540c031448070700840c03406800d030144d10020785502941400c2042d0789040751043c0994145513141d50f849020a40e200b07003d04002080000420005c0101348 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 449319325 625 449318700 449318711
    0x15031a070807020a020d050f030f03040c0501080108030a030c0c1401020703090b250809060c031c 44
    0x500070b0060f08402c0b003450052410003811162240207104a40c543c0c55802c5440385594440c0904a00c03091010041108110350207a160002d02070a2910b01c509500d03112150380c1c2e0f4040c544403a4285070b1641030300300030140f0400c4030001540e04040310011840407d45840e000707501501055000401040d4081000b65000045071040c0c0c011180c410301c0801500c04890361204440021200d0100800107204580e686102515100d017050000e9942ca842125040d0303214203030b02070142c100c1800c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 449319950 625 449319325 449319331
    0xc0901060f080c031806040809152d04030605090a051204050901090e0115031a0708 38
    0x400050500c2d200800201070b4010010100340c64074004800070302051680e408848480c50513180201e40347d00005800c900519041280420069001040d148008019020801081000030b213411b2044104241003054040410021000c14074501565114003485401404104807034030b0030900e081030310108100909400d020602c025a10811040e044400e40440802d4060a820301c06005180040700100a00001c010000822840c103422400c10130403005008a0b41e9030700700c0305840c40c203811 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 449320575 625 449319950 449319977
    0x7210612051011030c0c1207030807090e0c0406030f022721030d02070f050f0c090106 39
    0x1000f8907007507035156076808082d540100d4441d45039018988801003c85440300140000e14443d46400d00c81d850183c40c01003070441c1d5503000e40004a141c40a124841440314112019140c080c50080ba40100040b1220080c0c031980c00d000c0014000070300b0580f104202c4d100b00070031440040741d0011082c007070350311052201c09502801c030f80a80c2040000c082c1d80350a5034003c000310781c81142850182c05080c2c950301d04080c0907011b102019048610014958a8940c0b1602d014100d1030500044580d000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 449321200 625 449320575 449320601
    0x13050c0a0806090112020f03030f0a02100f0207031407140d0314061503072106120510 39
    0xc01c002050a80c19125401c7e40049900064210300034280701000001000c0380785a1941c0c2c1c0017070007a120b40c24041c406c12242d0070300755001c000e911a00b43c018011403a066041400b0f0001000203001031400384a030390456078011910281483c0c04e02c10054002500c41980c01c2482501790701103508043d00300c0c0c01ca400020442c4c0d120109000c01001038080c000c1032010300920220340e400310502050940402c1040c2e40d100ca0203042c248e03817101020788652040c0004030341045868031a14000d0040c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 449321825 625 449321200 449321219
    0x61e060f060d020904060e0a020403020103140c190e06180306160807080613050c0a08060901 42
    0x280602c0d2a0106168083c140c901001400400c242c0d42d600d21300103684c81c040c0d40132514181c00023020300a550301802290b50140750200007911929201c0c480b14001d0140c181c4d001c801c40c400303a02801404e441022080b82c440802040c55580c0d00300034140028010035003944a0103030180380c00044108004982d1012a031400351038030443c6554054045071004802015994820091041c02c060152030748102c0b8415004d4404050740c8800e48403000c0c0c03205000504040c0314425582c01402402d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 449322450 625 449321825 449321827
    0xf0c02120102210f010519090504080304060e010e0a060c05070203010614030111030c0d0b010c0203061e060f06 50
    0x10301c1a02d02902180c400300744420603002e0400003812300805c06008500303141c9411a840d038000ca030183c5d0100d18003003204003408010b000b101a60700600005080c0300e15a91509070050080000180138098200008801602d082c00340d6001050082083d1000c04030181c280350a4409905040f203800c4001c1040010140c2c0503c19104155100800002d00d07040c0800180c407000c40901d0b0180d80761244504109845003205d80701525881c21075150700035620744c4014490340000f0303005030a502504c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 449323075 625 449322450 449322481
    0x1103060c0a1e0203310308090301150305031606090501020c0c1c0302030a0f0c0212010221 41
    0x9040c02d02040c01d003204000303a04210003d85180c0a17900000950042c501c190903155503078089070101800d5510456035048100d9501008100103500041101c441c4000801008248003060800000420b20510098919400041e40111346000850214007510084038040008064501e100c2c640507800300004000da4010008000560b009a07490286080c5514050715600342d60707804201b400d449003400f50000d030b4003c200007440c4949841103e0781150614118101850070402e10004500d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 449323700 625 449323075 449323087
    0x1050304080a0c0203190b07181d100b071208010506130905041103060c0a1e0203 37
    0x603e1419035a180d03090720020341000c584569a01286061824440600c40b2842040340034031116203410071a400f9a80003074224480c244250385c41020000d003a01400007050581d240d100c4c40c05203180310208e072a592281416001b012080d10300142c241501c0000d5a04021030754090320040b00c00f54201208020348034003c400f6030060802542d01c4a000c0307010003240310703880fa440460089c16241c545c0b401c0b0011400d16000a1000c2c40040d420140c40b40c4522135210305902c01e411700b039024500e001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 449324325 625 449323700 449323717
    0x3031803070b152706040f0b010206010302040c18080303011e05211c03090507050105030408 42
    0x650850282c9001030020280a4481510a561244d00741e43d4000801c00c6090001045414605071103501c0c441c240c0e502c4248a8031445900013034540300b0500001b40700b01e0b51140c10002003031042d070300584a84503101c00c217008140c039002001d030b03641c10912a1081218240c50a040000d2000380c109080f1000680120681c801211042c0c0010f003640301000510b00c074103102c540712520b095200e02206413460310006900740583c204641000d509800441c103002041090200003a8403100719140030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 449324950 625 449324325 449324341
    0x61404051c0813030b150402070b0f041407030305040f0905130210020c1203031803070b 40
    0x409000078000c0184581c107a0307051030050796001442076034034105140c2d981030403101c0000140316516107001e20b20301882580e000b160803001908c42c40d83c0c1c01780907a44800b4050000c0e00c140c1c0355078070344500c10201041040c1c0510320aa41d050303140c81c680035a01c82551000e030040a41ea900308400c104400031a202000e100a804444502c01d0a8100740240d040242b138400040e00f290010b0b0740d0300054003000000314003c002000320703001c11034003107540a6103901072030a0044c10b090780840452044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449325575 625 449324950 449324989
    0xf1305041b12142809110d03111203010608060405061e01091e06140405 33
    0x408070407001e038415849021021041c5200c403e414821011608040300741d07003480031250000041a010040071a20309182807010840038450008526000ca03a00003412155142c101c070500c811040e022224400c1c0b0300302c01c0d00c0e4180c02020798183c40317659840c180a0f0380c0b804200801d450302510100d4010302400320064160314403125840d058141070600307101c902c0d9981851010929012010040c069440809008407a0f1140d0705c0038042c4d1255031480c1c20203090100084506a8102e2481d400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 449326200 625 449325575 449325587
    0x3030702011d040227090705030a050c04090c0816020c03120c030c030f1305041b 37
    0x440c9a0302c0c009007400124107105070454404680e0510094115170f240c0c0c05c8030f4a10f1500407000303141c03c04000111400303c81d9a00001d000303001007000d001003a005260130070354202e2403078281900e9804140c11284c0614103070002503284000d104089940403210103140e8118400f8110b01141c1030007007555040c0412320500504000210306c0c2c261170041c07065034074081050096966410b20103048001f56086a90032047c0c06078801780000346441c2c1845005102c1810003442800800d20490039100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 449326825 625 449326200 449326217
    0x19060b090a09110f150f07032d0c1a07020a02010e0a0605030408070807051207020418020303070201 45
    0x155401780c01c501c13104078254149000d0781c12070701c0c0d900512200000e142c0c04042c0e02201e136542841c41042003801c60b400000c46500300801004c82c01003004000d018036014482c100c1040f1035025544041d800c540d0034a000300940b80c1c0b103405000d031301144802a40504504111240c0c4085a15503659607040d81c41d99620380b002513000305001c2c1e4198209100702404944140603c3c0e0483d10035105051703441d080c610602040c1c81c0c41c034100920f011039002d41280941c401204649070b113582464101d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 449327450 625 449326825 449326849
    0x705070501140a3c0b030a060f2304020901051219060b090a0911 30
    0x1040400d40100d100321030603814001040c1018030360240584581002d2031142c1320420311140018490703c41c805860550018005050280848418024022801e09179014020712044e0000328483d40903441c00a2240720b00003130619002070400e0070050703921008440b151600018400903035100c42507641542d00448407960f907081c0d0039540529040003041102c044a031241d030b88200b031001d40c2e404500d10320400c0d103403101a0340d101400c18086a186507c01132112110360000540b50800d00082c900d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 449328075 625 449327450 449327453
    0x30409111c050415242702181c030810030803060f030114070509090c0415051b030d09140d0206070507 46
    0x70502301c80c03503401c40c940c1c4140c0054020603245580c0c00d14580941001841a5030107441001c250001c200305201240500701160391155081d40c840200b00d6404005c40d0060106912004801c407032107080c04039240c0d00c00c1c000d104034a0304548107080c944850b85101000d1045110305010480c1071800440740c14024005407a40008200000e14105404e007051421035100c016905c10300c55450440c0410004160100c0585485880060500c150f50040195640c4000b0f04150240100442c4000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 449328700 625 449328075 449328097
    0x6050109090209120a080c0c0d0f060b04020c0a05030409111c050415242702 35
    0x3007441c13200441c111031180040340000d2005a20042401540f05010b0304c42104462051181d81031035510300501a49a6420311000300d8415444242505001000075260500055115240068003a02a1440c3c0c00003e01045803e03010f104400900b0301c5016001e04100005022103882c00460700070902140d00c1c1c0d40041e00300038a0301280362412031903440811040d40714000204201040190f101401d1180401c00305610158021450803100713203040c5000b010740717807038000c1020390444040782d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 449329325 625 449328700 449328709
    0x150e01020a06021602040606020f060a1d0304080f0c0306040c030206070c150c051006050109090209 45
    0x1251074101d8980809aa1207440c0c0c0700c00e071446503020401181050311603040145080d00c082d2100c040107200c1c55403105d0000e003201c12074039200c00c06c81c40c015000703154850512040c2c004030baa540d60354006164031442140314114503401020301200507800d01007451340c816036001c940558440e00b0766007000700e503800110003a10090000980420340d0950f0502c0d49806440e03540328a5034103456858081d1500c0486507851490302d042040070000fa98000d5013050580d1041e40c001b40e01c8140040118 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 449329950 625 449329325 449329333
    0x8010e011817040306050c0304121d0f01021509010213090e030405010c0f02030a141204150e0102 44
    0x600459100b170082000303103004002802d49400c00c1c0d4080b649440c80a4a03030b0813035449181ea840030311031034103130080308a0341034010019459080c41080303055000b4402e1801d03000c064042c80354800d04080c0009039840032004064001408103801107561980307804411391803807400000351002c0c0e610038213011012271010b0610000444c1791110096061095403080700c04c102c440341d428044150b130752007103468120720300c501c03800c66004900880e011210342d5070841c00031500c2045544400300041c010b035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 449330575 625 449329950 449329957
    0x903020405090a0b0a0204060c2a030c090614062a1608010e011817 31
    0x11005a9980c000e5902a0207503100401929019007000c18072620003071300942c04035204100030002c0a402c11b01ca030190a8102401961010700c000302e4011401140340c0201b855085000b002c41004401d40c20070007602c1442030304002c82a2105080c24018039a45001a0710075014040c92140425002108842283c0703041c18060702051045841e140540009001480141214040c0725001007445442c1d600e10060009020041b82c2d1a002d000c01080c1f031001500c0c0d42d0261021007500749400045 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 449331200 625 449330575 449330579
    0x1e0406090f1a030706020303160c1203060e01090e03030f041109010f03020a050402032a040807090501180b091609 51
    0xc1d01c41104402c03040c1e15150335600c1401159808a00341c80b40ea0791700c15002c41120a400d0940070305400400004000c0c003594041251f0151007410f01804641030480861034091098100084250782d0078000e00a61038081d024000804049400f5890343c5080a01c603010040000098880102840c4149250015038019100035150020846024035991161540601820310403400e03803800d4060309003041c1c0568042d02c5850480680b000c207682c4c44000301c54a0002507002c180003001440180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 449331825 625 449331200 449331203
    0x904020c030c0a050606010e180406050405031605010605011202091e0406090f1a030706020303160c 45
    0x209040400d221004d0381c841d000581040070958000008800c1b00e0f00450f420680004080388405072941d01070700203001240e6440010303040103030400407142c181100f00c101c0400c0800303030310b000c0d0f01804c40350103802c3c0001e408091010702d081d0309000b1354201101c001d1030a4a960001b0180c0c0c4890600411010383c050388490700042d001c09907119644840c10040380120301c8100d0b404001d6640c0d2402140030740aa403000d8010401d00d40c0c0801503a402201c050f88005c5041c140b0130301200c074103000380e40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 449332450 625 449331825 449331847
    0x15010b031003021905100509010912030c0b071403010909031806020706050f0708040905070210020702060904020c03 52
    0x11007860100c61b82000b070440c0c0c4009186400305e4841503000c9921194180c01a80d880c2e416190204010919210b005001000518101c100310401d00c4a43d940384951000c0c44c004c00d03165170041100b600514002e040210f100301c40700006500c4500401100b80e0000c4c0b80700c1152028213001e541e908280d5100140740c852580084d0141c2d200182c000b071000d1455000d24441c010581c20345464030b006148560a0b8894024069030000b01404400300c21b140c198014000f5030700c4901268601030f01002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 449333075 625 449332450 449332459
    0x30f0b0f10210b03070605070209180a1502070c080c28031415010b031003021905 37
    0x1040b0300641c58410004641544409151510400e60082c009001040c01480010303943d4012060f400701501900c010181c130f075122501c0c9410015540102040c0303250b4003540b024100da50181c4122406070391410001a5922001c40c0c03240001800c00741c000c10650301010507140c58007150888a452002e07502085544c0703071500c1e035121440c0400d08a458000f11042c0d0b28001090400c240507205d0031024a24604040d400c0850f604030034400240035061081d5842503140c6040a4940280400390 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 449333700 625 449333075 449333117
    0xf0721060e0106090f150810051e1302040501020a0609030c050f0a03030f0b0f10 37
    0x302060001d060000541215515565214202c1d203605410220030744a00c6512000407180e010305817254001e100e0320703034001801c04980c100360756500006528010061200381400300d4811810030142403a00078000c2481c000c44041d4501458400000d50700c482000015000c02d80e55070f450340805120b0691110102c2c0c2003003c40c0c800d21440002c81e62191740801d81140840d14141e03a030348031303c800c4d4050201c45080040510f14445800b00502496140c12410007041050124a42407a8100c01c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 449334325 625 449333700 449333711
    0x50a0210020408071a16140c300a050307240c03020403030906080f0721 33
    0x2210030f403a000714400304146024a00140030103101000d480d81003440151940768011824140076005d030550402450150f441401041541c4802800740c1100c1c80410200940041e078021401000c4400c040c04007160a00124412912a9208000e03514280c0552600305500da440c141c03c40c15021020442845c40589100b01c5098180c0e9860140e00c917031841c28043c00a0409601200038442c016003000f100c810481c0b411a0712840500b8890380c0411803c05410102441d00c0a2084031890030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 449334950 625 449334325 449334329
    0x30c06050a02010b03011b0e0102070b030a0207031106010305060c07060b04020706140a0608060106050a02100204 51
    0x14003500075085005000015860140c000440307140502445e0300030300f40e90340442041c91000c44201e40007607800c1c040c84e055218110001441c0c60761940114400e0668480c01a1114424600100b1180241490003000d0344400c00500218502049075504140c161006960b58685850076001800014000a40c82840400c542e02403011581225101c4195082c244015541e240b0b041012a078440c0540c0203154000401441214082c800504100a06004541c0c1c600000302e00c60081c1c0c2d000d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 449335575 625 449334950 449334959
    0xb031501060e0d2f042a020109080a2d03020a0f020c030d0503040c030c 33
    0x6848294954500440070701242c9008000030700420b401903829000c96107041018a00c01d0782100c110706041c000c0c84407110742c4001d1200310755115081c00306141000246004408151304448a441143c01c914079041e400c0380d45018000303000c80414807c2d41325250003262070807201590108008403044944440000308080d0240810120344e0100c0c4400d00f2603840300000c0540301c41800181907042c00c017000a40e4440188041d00100700c00000020100461880904001d540c0008049095030310b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 449336200 625 449335575 449335603
    0x305060a0807060201091703100504020306030102042409170d03020f09040c030b030f0a0f060b01030b03 47
    0x11b402c401e114a001c4c41e0002c0800c3c0c043c02900c0c03403511044982c0aa4614204400d103c1071501e50000c6410030360080001d4241a25600b200c1480b4901a050176811624281020200e54200300c64000810700002d081003030307500581413261a0044481a00d0030107500160240c00b80a0b807000b500c101e100042c10400c0750700c5209101500504550300c4003446441900c10462094200068103480c040c2c0c84030343c011950440da41d400025080704500c02d41070646500300501641c8017042110303016110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 449336825 625 449336200 449336203
    0xd031b032a06051e1b0c01090f05060a02030f0a110c0d110c120303070305060a08070602 40
    0x19011410302c4050301c03500380c0048444107021150358070040642c100c09400b901407520184d212081030b01c0004d0900490f40c034130b40e10700001e10000ea164180014001100c21040d250f030301500c00002c0ca6070b40c140c400c0345d00c2241da00080124544860300001c00030006a00f080b01200b104100c40f1810784020045180c954035207a403014405002902d900e0f040c10390b0145601c0c020102546410961100441540c0d0700002c1e80c81c3c001125507903a000201003080507444045140112031000c216a81e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 449337450 625 449336825 449336897
    0xa031d01020d060e100b0705030403050a03051201060e011b1103010e1b0d031b03 37
    0x1a080b0101224180b202c0030903a1541941100d00403207000c0d03204100355250410307071082c90300050401d031043d0009010000200704184190307444d16110369280b82c0d94904c9100040c407400810b0300071404101001c0b08007845039800c100d4000c0300c3e014001c014000e000091078401c40d840c0c88600ca0613015420721320b984000100002d0801c01c000c0d07201d18001c040004407000e12110f0b00080801034001640301d038144000070b0420301c0d4105501e01910f0140d060b822102000b60100410901c00c440b1001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 449338075 625 449337450 449337457
    0x304090507120207240b0105041e1802030708150907081b0a050c0f07050d080a031d0102 40
    0x410040d908000c102528030b0417841e03080c840c1465060780c01009542c1258150581180c4010000b07101011404542c0c1001c05e000e45480e0f80c0d142010710313640c040d5208401d036031140740703460712203000060f03004490403141940150711070300140d01544900345903038100c1e03d54900740001072140c000c0340b10103410072420040000d0002c208101d0541081090341c8000b802403001d049202c0c14240441c0c801410303004080c011200c00100250454441e6000d1400741a43c8404c0400d50403008003214040d61 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 449338700 625 449338075 449338103
    0x6060206060111060f07181208031602032704090f05031b0a050304090507120207 37
    0x202602c52950f45008100556140e8408403844080091000c002520840c002c98900e080310070b01030f000c02c0105440c1d001c2c0098042018005035290280401002420322070300312450701d0b400d100c2c40914240a1611074038031103207041c200c0030440da28100301c40142a03122684a41d13402600310041561254041c14116202e81c056a1101c00c40d506405484000e98400a642e80040d54000c0042d0300c4c081c0342189120003020054150002c2000c0021900405429400035000c0c0314003034030312031003d1a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 449339325 625 449338700 449338711
    0x503030319023a1802030703021c050106031a09070e0610050702100c1406010b0904090f020406060206 46
    0x3d0b071003442c44c034143c101540309940e69581c010aa8407403007400000d00a10721402c036003601d03030740c00800b042c11141e0040007030210503241d01d001541e014480c54001d000710002e80204040325000f00300001914400c842802080e5101000c0003c140304208000d0140a030400014000d600c90f400320010707040040e2507a8501e212a0700e0f1a05a070703900410140415003080005101c51007560f0b040300d40303c0000f01c030082103c0400e400d100500c07070340010001b07601518002c00051031580100c1c100d803148 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 449339950 625 449339325 449339437
    0x20405031b190b2205150f120103060b03010e010b01050d1d0d0f0801050303031902 38
    0x3d004020741d41c005244008110603510010031b10800002c07801c0c17650b1070580c4501070f0350700700050a201382c4015000400041e80a54032404002c01c15540c00d0f0300781030031102c0c00130031030220303a0608071807450b41e90f0440c0c1120040714540303601190181560b10340034810000c00310342042d01e1055052000342d10b40c0c4134468590001c200e039a840007a0340d0798805c050b40e900043c0c82d00449400e9924200c109040c0950003032550501c05600844003168600800005078402d05034461180781014034100c4035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 449340575 625 449339950 449339977
    0x5150609090a0302030301090903030e0303160f030e06040b131407090c03020405031b190b 41
    0x41125001c0e40c040082c00c00000d5011068034119998401b0106a02e40946403d401030803085c005100715100100410115605000324000d500219841c0c00002200d191803c80c26104600c5041e403d551045010500251411360203a42c8000101e001c003003841c00a0b80c0700000301f020501602d20a138400f907030903c4044021301c41e240000c12a030504528040c40c200200380c40e40c54a508040308000c800421040c0c5440c0e104800307000126203c554002c00d0b455855124241e00404201d8019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 449341200 625 449340575 449340589
    0x3031503032604030e04021821070501050310060302030405251a190f0507051506 37
    0x4100b050b809030050f54001e022640710000e4003d141081c0d4050304503207407082100c071004192a0086810400c281c20403020224000e150003d88040401c0540006d00003841c000d451071510350b1601d140d0780e2840c0622400c1603000000310301805020020040064030040078114001d4003c05c1444d0f02103501d100d10a40c10300d070f20035060074281c407500554242e5200f01c025814102000001103d05c410700990302400d01000b80841000304c0c10803c0400340340314442203154018180b2004005c02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 449341825 625 449341200 449341247
    0x315040309080f24061305090304031104060b12090f0111040503060a15120303150303 39
    0x43c0c11003006006003490701c1900d00351201c24801d05818040480d010070600d864101c44203e9500c0c210006002508210940c070359250b00610040c1c92200b4003005840d010724180c000e650455000d20070060030310703111466030a5045009041d05895102c1e1039480c40c0591820301400034012450505107482c1d610b0401894142080103212104441c50f15007100d0a080d90101e50000362030b0660540048036419160642c0201800403078001890b070f144100004259100318040381101407207440d2402c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 449342450 625 449341825 449341843
    0x3090102060c0703170705041806030b060a03050706081b0d09020f01090b090f031504030908 42
    0x82e8488400c82e40b0890301a61403442415034080392880f181c801070b0403e01080410080003c030b9200180c807840001a540c04080345040c550305224030900005000e0030301c80d541100c0200005400082d0b010201d40403802c0c844076030b80e20f102100c290780407000203d0002d040d001074002800031695100c0b60030795208507010068140c3d440c0c01110005200d01400141c510308111030020380c038000301d40602c0d0075001001c481c4d18401c24040c010036440143d60880c08508080c500380504ca50501240070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 449343075 625 449342450 449342461
    0x50c0d030b18040303061d1e07031103010902041401020a050c01030908191101180b04060c050405060c0309010206 51
    0x905050b84280b00c92200f042012304640d1000324031420044e101c44030304802514103200142800c440110000c111030841e9401401125040e00c0c080f04142e0090006a0312454841303000303000ca81048000717220950103038100814081c81003407401d1500c0c0002003031865503480c10346c03000001061003072010754030a0244612400740d100c80d0b0b0340c1d10108045030f541c01801100200000c00306900d0341302c104d6103940142c0544000d0103004002d141c482c407440e6030450740d076003180708124010b204200c04a203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 449343700 625 449343075 449343119
    0x60703020703110610050d0203070504060909052107030c050a0506070207050a06050c0d030b1804030306 47
    0x200d90000766034150154861402c01c000d1b0f460000001918140000e064403030282d0b50308009801c5540541c0400351035622031070038074140031007400b160303003500c000c248200f038519440b0081154030304c1001001001d01c140c0c241c1ea030003400400c01ca0b0a005603070110445036181001140603544000341e2046511403504110080307440751282c0180d0300c00380440d0006080c03500801c0020b40241c0040703d20303560020f160b10a080a00003001e00c241d0f00031030103503d000480c0c500f8000401a10800c68110754 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 449344325 625 449343700 449343703
    0xb120f06030c0d1112061e1f03081e031e09150601080709030506070302070311 36
    0x98035880d48000609801142c18006000198041c107249017610340f1090b2041c00718400090311800d151010b80c8514500b051078500c0c1c5003894460024816200e00d1900d900b0b03602c0c034000416000c1d420355036003500a52115010148022103100c94030348080070100210710070020662030703451020103c040c0380b102000282501609802034003254a0710b9840c5991160700110034030f0f0164954843c2a410781300d8690030340001d0064003540c400c010706a40c241c0c00a046580c880d5440c01400800d81e1000c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 449344950 625 449344325 449344333
    0x305060306100509180f0d0f030c1407200a140307050d0302060a02130b120f0603 37
    0xc045550242182d1200e54030080217442101e85290b0020990289003840410a07106000d040c030003001507100c03010076144020000b02100d00300001c290901c10300181c03404407000d5600640f10400d901c00c0c1c6001d581010900b400b294100310844698100342c00f00000f02c6c51038180301c2c3d00c00b21030100b0780840301066651010003500740c01e4081c0c080c000d60420f80101c0c03420100d03a0010300e9200c0150500c507914070b070390f607080d4099540665681218003007003000780701c02d10b1804002c040d04010120020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 449345575 625 449344950 449344981
    0x14070602010c0e030a0615080307030536220203010807030204050105061303020603070e060a0305060306 47
    0x40d111351400302e0201c0b01e6031b81c00203000a40300515154160380011540050843c2d21010500c142016002801404160458001220f128251000f0082c12580c80c8580072249505480e8143c11420000564080041a60720724140c01c65030000981c103d8000361f01c030105c0c9612a0b01c0400c00c0d42000e02c2046d01408060b04d2061801c0074000c04400010541d1000a00581001000466a9108010142118800806041e9138481c0240020b001e00b030151000f03446801140c006c01d44142006100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 449346200 625 449345575 449345597
    0x11030604030e091012030906020118030206070c020109090e030c060f04030c08090d14070602010c 44
    0x7000305150b205600c070581460040541d004180d007503000c0704c050b01c4c0c1d200862107080c5503600300c0c00507000322018400140e0a028001c50ba0040000d0b60303400340c074070b43e401944521000b00440f003086116403080041d607129050200081803075202c10080580300c1c9660648a0f801202c0446103407040c9008a000304824000781071096130140e4460494030541e076103000e01503020688030341d40710001003500804034814a03110104d0394100380050046c140380840c0642550b900c2c000314400d00c070b443e21078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 449346825 625 449346200 449346203
    0xc0b0411031b040e060c0703050c070905280606020c012d0c03080c07031713170711030604 41
    0x11b051038400d203000501440030110b1150000f00040000d070010704070081040c041420700701950107034414040c1c42d200a42c48001101c07080140e49219203030464002d5801003080c0d40c0d501005488a0f400c040314108d026808216050700303010002c2e2000d50b06046940c81c0340c19103169090090400c0005002068050b008111130008aa44000d1003011110a00b100ba03865460b070340703030320300b0810000c0780d000f8152017081c0101c00d074007222500a0040c881c02945100c80125800341099141c0604540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 449347450 625 449346825 449346841
    0x608030309060c030c04030204091110020a1403072006070f050718020a0c0b0411031b040e06 42
    0x140380c50300d41140e080c0402b4241d81b51080b07460001c03040d4007800b103a80f0180503060108040d07004000814032810084815288580504c64542007000007401003a4408820603168000400040e55094031001082040c4500b1070041c10032a56001004c04006000c01c1940890300d40d085034120610241c10b1900491042020782408140c000383c41e4000100011300c0c19a0040c0078a94021016080c000420708282c500c48029140e00c448940f0403006141510030385d8085810030000f06614609000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 449348075 625 449347450 449347471
    0x3060303140307111608010b0402270a091a0a120308150102010207060608030309060c03 40
    0xc1c1c5100200900c660780c40b075540d4001100c802064240007240c42c4110b03096401e50030240d070110010344022000a020004d1300d401404246d100e030ba90400030300703152504000c00c11100050681c01120009001c03880c0559220b00716019903400d071000030100340008411841d9840c00071412402031001c417020300c000400c60b4a0140c09994014174440c6c0400004510490f103a01c00c0d41140c01d1160712040810034036032100d4a06a40303800072508085548100d00104021003c2d08040e2407080710b0380c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 449348700 625 449348075 449348087
    0x50601230f040f08010f330e101a04030c170709020f0a020d03050411150c01090809010f03060303 44
    0x4003100880155180c00360380c7d0340700c240c081c0c0c1d00e91200011084c030001100c80c5940f2480400781000601e02e00039440c241c03064002d00b00d6081c142140d8901084406510441041009400034003d1081c424065540180304152085543d0024000001c1c2c55030400c031521400760040c10741c7c01c44440d00038003803d481150b104d0200c00000004c801002420300303803200c103030305091002d1110400354182481400c144600178542c1e103441c2e82040f400100303081089820300b020903081280c20400203400136 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 449349325 625 449348700 449348741
    0x5210a020d021c050703050105010504023a020724050601230f040f08010f 34
    0x1601074000c90051109a041d5103d102014920450806001900d1441800c100d500e484990100311340c40d5080038000107107407409000303030340d008060b58500c0040d1000c0e261b2070400340400c5049205654a01c3d10446200f40c1c0c507071020b00302a0303004001070000c40410900284c102d8525151440301c1c00d14110901140da640060402c0341014620b001a602031059003507206640981d250109803a08001400b00b41700c2e00c0b0040d10720480c1d02500007070005080941d142e0b8161000903140404a10621 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 449349950 625 449349325 449349343
    0x140705120c0a0203070c080a1704060f05030a0e0114070908120d0b0a15090521 36
    0x300044050b91181840030b0441c0010f108200006400881e45001040d41c030004051101140c10f20204441202c15204002c0d00e003000108410390304010207520199050902035225a64101e1002c050316100711141c0c41940f030603109540b80f030240b58015000305001d9450169140d140d42d150b035901c92042c500124100e41c10b0010b5003003c0e29a820a01145802500250215603103a5a10380e202c10140500030204451840a204070305200300780000c01d07480c544142c200702480c00c0c003298a581840c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 449350575 625 449349950 449349961
    0x60601170a0e1203100f06050307021542060702150309030d05090114070512 35
    0x380031840015007602d49280c01040340c0902c650603800424403000d0002080660125110510801902591850103660301c2c0800c0f100324000d41c00011500c0c2c64030307403141d01c02070388040d200c800c8004521b01c040316108444501d010030320641d100d28541c2e40c0652248001100c80c0e440c101c4106141c0b0f4201e80c0031590302460a80d01d000c03114000b2000c00c01030729081c4155445200700a004001624107024528060711a41007080c10029031a400310741c00c0b0f40706004031103030b40c402450341d40c2854641 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 449351200 625 449350575 449350591
    0x207030f051018120206040f140f030d0207030201050a0902060906211806060117 37
    0x32036540440c6108408940056456402e52001c3ea020000041da601510350140c505100c08514040da40e1410b520240590f441c280d039840201030074000e40901800c0b5016008403400008000c1800d140340c450044903158070a030340c40708000e5030002004400550800e400b045158041c3d00400d130344c0b070b94010f05150900d00c000f001d000e0309812560031640769105403500703184204400c0b583d240c040d0100300c0c0040b136410340d1f0281603440c043d4040d1142d8100412703540707260854032400b946a9001604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 449351825 625 449351200 449351213
    0x406030215070305070209040b0a061401080612030409020c0f100b0d150f0524030d020703 41
    0x11508406040c000c6082c3c0c5e01460700a02504040d142c2031811459003e02164203015951a04201180c00c2d401603119000892060f1118907980d11104200101076401c641d000e40d441c03008000101d011003031030001c0e044e401b5210004252140e0003404042c100091030300c0151042d417510000c802c01c3ea40758254003504542044c204258902407503101c00c044c2c0401800c00c0d660030700308014005092a581d00c4014084808c91001c0079101911080507216682514460300603071203a10b052000c42d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 449352450 625 449351825 449351827
    0x18090304090e1c02101407080105060d091a0906010e010b030f060109080f01090308060406030215 44
    0x112082e950560048884000e010004102801407607401a4010b00344401e000000c40c00300c401240b134943c00c03400218204054030394440d0f0b1982c15034000760350441e1281186030304030f03014029640b40141005000070b420f14800d603203c6801440398292000320344141e640e56804c10030403002070080304081c0340104001800e500422107020f40042c2c041c5000c0100703e944101040c204040079070364004594440145000b8558050103031500f04004603401c018075855640084e400c0510140c24002c1c483e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 449353075 625 449352450 449352461
    0x1c0b15071e0210080603011805070b0d090b0112020306130302031803100f0204051809030409 42
    0x44107004241008510800a41024100d40ca00c200c42e80c10100c098400d070411802070240c004640105074940442000081007603100c15414451200864050041c010303039003030001020100c64403003c1c0d821800381d204003401c1c004040d500c025414140700e030b01c0c1e0000250341d11840c06102550007d54034403860b850940e548400b000801410303601445589000036901c201440002601841080258085d00c6803610508460340804400d001040180e8841e0b01e17201c0c061810185440d0414000c1c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 449353700 625 449353075 449353103
    0x121806051306081b0c10140601021c02070521030c070f0f0f050d0212031c0b1507 37
    0x31807040303c00000c6e0003807169054461403180c03040084409130602c80700d9601000000d445a8034219a03030750700709109800a55401452048921030044c19151404c01c425082c0714040440c2070b80156030f5180cad2045034096482d1458814484400406000001c800341004c604a041d110600710840a40785070008010340b03141c0002060368030641c0c1220844e04120100010194409444002801490040000821140c40c0249580204484a590005401208100c44280b544036110040c20f030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 449354325 625 449353700 449353717
    0xc14032205030a0905040509070b0706050601030204030f0b0402010f1704121806051306081b 42
    0x86040800310000e03408811251103812040003d4030b01410360240c0c0d8000c51600001031008100040c2090480d141101094540300051300c0386400b0b007038014680d5061503020003001001030408581c030100d040c060203440850742040e10004002080141c441d504000c0b0004104401408101e00c146c1c0250303000a504801c21612038082d02c054a8508001741d085601e0140043e04640190013480100d2440382824016030311380a06031111142541c0d42d140e060036401140203a074103c0300091511a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 449354950 625 449354325 449354371
    0xe150112091109011e05040605100c03021e06160e01020a0212010f050a0207060c1403 39
    0x30121007505907a0703d9004403640201041200c1d00d451445242d12946001c05c950441c41c0500e040c03800030b20954840c02200002d081480c070388140c41e10400e08080341002c20700c450300382c620662281c03003050300000012600d0090a5400c2c202d9455403034080b007500c82180880740e40d8056002848408090301c3d01c00321a4207117100240010405034002c00004080300c404595001c02c566020600c5014840c1520a080c1404403d06103490301c08500c100e858128040205103140703068a003c8007003030030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 449355575 625 449354950 449354963
    0xf07090b06092814010e0603070206060d1a0106030c030b0405061003111902070e15011209 41
    0x3d603400780440f503400440380e8080b1380c0d1101c4d00c0401c0340143c400e896020300300c1060424024240310480b80324006030002c202042d01da16244d400b14000b1806012036403030f0480b00c0c0c207080045284c01e030310400101e0746d10481031140c40c0e0180a04c03803403110112820413003840d113a40840c94540000d11101d081546e14400b268240c005041925000d0544e204459000707041c1410103580c4104038000d14603524980b1000509002024003061602d03401a501d210308050f0b0b2030380d407501a100c000c500b1203c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 449356200 625 449355575 449355619
    0xf090a062d110304030609050f240709091a040c050a12020c0705030d020f07090b0609 39
    0x45001180b80745582d00503801140d0380f40c1c4e505205c0d0300f800300501280f0010b84025000c0c1a020076104c42032010602141c0f484200700c051007012455541c0504580c600810000c80c0c00c2c01842e0000d05000d045d02c3d03080c116a4026030404e20030701e07800ea11030012180d000c3c0e59512030b01e01c4901e20b04070f608029040001030740c3c0d407481081008100381d6410044200c0155541e0b00922046840009403414524640e0104644a007010503014059039040192a98520151108218103003c0440c017441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 449356825 625 449356200 449356217
    0x20d03050a0311070f1b030317040804081b01120c0207140609060f090a062d 35
    0xd054035a2243c0c0d00c0d0900741c646041c22041c0301d00d040e81c01500a0120460418503070041000301e03a45902c428103052480031181d505038400501c241c07144042803000141d89403041c000d03e503e80c01d1700c594510b114141e000000d8102d0036110300a14070589403010080d80650000303104d0b0240e032820b003c40103103050700c500011441d104854400d90091030103e800c41d81e604205015003c85141141c00b100b0039621070308120390125920411300341d4101c4203069060300c41800d071007080701c581540c0f820551 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 449357450 625 449356825 449356841
    0x10030c0c05030706200f070209091014061002030309060a0e0a1403030a050a09020d03050a03 42
    0x1c20020405080410300525001814482d9031004010459549240b891049400e001000e2200300400035a07240d103070103898a002c20350740e081c5141e041441031100c1c00000d52030803000f103124500c260030f100d00c10001640c12140381c00041406a0750b80c00121f940040b250700c11740005410350785941055103045840d8084600c80101c6544a5001075035090342d0711101c0d8808820803204034454018139801c104141420000c40c50305801054841c0034843d405401e1000020752050018841e07442141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 449358075 625 449357450 449357453
    0x1706060d0903120f02030402150d0e0f160e06030307030f030e0a11030c0f10030c0c 38
    0x36500d0300348440201034008036008505026000108100780600c02c0142c00d911048074000d500c5900200c982d2844100341d8060705001764202e400041c1c07020505642860045460401140350b44000c141d4100301e08000d480038084e203002c5084a4050030103c002c6641c0380900c490003001c0c07240c400780c5401d550348a035006101c80303114082140c220340d10906000c482840c40d42c40542c0a4040c030601c40d0f400341062000126034450240809a4503040204118000c00f0700b280d907a820005501d29150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 449358700 625 449358075 449358097
    0x5070c05130b1c0614191a04020d090b100807030f03030906051f080607170606 36
    0xc1680b0000c0c0c12081c3da03600724000c0104151032003071070082e8444c4018103c0c507080024500403554501e581c44080241c1d03501d240e80d22000032426050035814020802e544c0e40500e40c060a0281904180c00c8406030105801f0450220600034890f0503196081d005003001407540e1203000c00320040c100140c040c1540c81c914240814034030b0046504ca40c42010980640302000d01005401f20180d510000b010b070842001c1c4079040e94001c03103600da0301907001d028030841c1c1ca5190009442e48a80700c2002c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 449359325 625 449358700 449358709
    0xf09011a07080409020d0c18061b02090108150f0708010302040c030e0d0315050105070c05130b 43
    0x2035584e84034010240250800c0080c0c601003482c0c07442840109000d02d1941d44640c0284200e80c1030345103400c908a44442541c00200e0000240b4090000107840d90106140640700030301c05000d026815000800314550001c107501c80040d80321003031007520f5402007078a60659030150740100e843e0f0114001070340600406099041075100b60140c1d0000140d040c3d101129a0500701c160198040d50340300119000d00079000060808001101d04224501d01040e10405070f6880d0311000c502c020032240002e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 449359950 625 449359325 449359327
    0xf0301030b1519050f130e0d0801060c030903081b1501140f09011a0708 33
    0x14040d40c803456080426003400210b440c01040c010807403070310440a01c440340070b80349128003c000403200c06440a03002003521340300040180407403080d030154584c946050340b440f000001a080d000c01d00e05031106055079898100440345035001100c00b43c0402c900c0c1404000154031107004210480300c1302d5208291102d4010000d0072310b500d003000d01c56a81d907003100500035021a00e160354840300041721141c50b00440e40d404201c403414140320f2070b0802000314180401c102c119600311145035502034242 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 449360575 625 449359950 449359957
    0x7020d0302152a090a0915080c01020a03080406150302100f0201050903030103080a0c080f 41
    0x6040690000c0c0c588001e203400010320400d070701e0b072000b00c1d241e01d141e0030032000340d0309039502c1840030945a020161400340c0d0020501c042260380c030780e0010215000c8030000081605550002d2280080c00c10801008071800c4c07004011141c4603440003401000060001000691a40b49000744150504004000f9580050500000c000140c801801c0200681d003108055420500090482d00c0301105590490780c212401034030708001c80a04a070405005e1604803611312007402808110100040034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 449361200 625 449360575 449360599
    0x140103060b120403090b09090a020702030f07030c140a1d071404030305180a03020a090b0102030702 45
    0x25800a0142043c841003603013241d0624058541d03541020b080c540014005029200042d1071800659400035060055440601074828a10600c1045412455480c901404030351118410f2103804681c1301121140b620f4500001011540c00000441107955a5010700e50b01e44d1010317004e142404111400602c0301c0d12140d020b040203501030745032941c84c0c24035000868107860001401c0c0b03100c1c5d001e00100703100682e02c00c24a24141e440072500002c40d079039558010b03031540c4941c00002c4c3d8812500618 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 449361825 625 449361200 449361217
    0x20c060c010902041b18030b040f0c1518080120090d020d080d2301140103060b 36
    0x1064410780340a07803034002483e001840845450502c0d80181034076000203020703145603036644a510ac4916061021202c1c0107540000003200d0500380c80341d44140545640c3d045402c030418580c80403400301a0007214459150443d00c442c40000f408501d480b42c00381c41e13061a00e80d039440300081d80591034480041c0d000740307001201004001c14040102801c0c3c40d48581000001899000d41d010007a803080244044000301c0010701c143d0200d01d01d00c1c840ea001c14034010441c2c54580301d40039015003000a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 449362450 625 449361825 449361851
    0x71206061101060f08060c0a0306091802032b21060905070f0c03020c060c01090204 38
    0x3140301d0a070011400c2425030740150414108001c2900c41000404400a503ea50015040c02c1c2d483c0c444618400c00c5019203055800b500e174290a01c2c4d0040c0c20520310140c241b04840c801c5040710a05090500c410203644c90090b41c028a410500c07201300c1c130903030042001c00c0120150128910705100208508004c561840e000181110750350010040c140e508860303200700100d000d0600c82c1c0d400c850783d5802540d84943c125164010320b00414070721010b1009400000c10264001c000b80a1304084003c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 449363075 625 449362450 449362457
    0xc060209150405150f1b010b060403080a031a0f09041109090f010f05060d02040507120606 41
    0x100200c500944d008050703105044110015401680d4110000180811151224403410400392030b8060412000145103141607000440950040c2d104440e10310000ca000a2019054071074a5100c020017400129440c0c0e002001416812400d50001d101d101030030041000d00007849a110312424000d4614446820100c00040e0b41d1540c00c086a0308660030a50009014441409080d0191030040c04030f240e680c07065401c11000d0034000b0086030801c84162860320720800c050042d9002401181c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 449363700 625 449363075 449363077
    0xa0f150501111e010b12072d320402070201140f04030b1003020316050d030c06020915 39
    0x19581d1092403c60384464822800358000d01403a0305020320404208100310703909410790184c0c0400920700b007075614008c00401c0503074140964404620410303280c1e000504504060b1110b41801c0f080030f440e182c4256940317640c041c3d458400c004503140c11015154024009852400030900000001400d0070a40c641301d01d01c02e100143c8520b00e03601c18103251a1b91100c5100c900c510010703082c440398a075148400701050300b514050308540d4141c00c1c014020300c11080299040a1220701400c41549010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 449364325 625 449363700 449363711
    0x71e0f0605070c0b09010e040207030c06050403030507020f03070804090213080102040e0a0f150501111e01 48
    0xe540d8142090b40c00103503510413004440302520180c44084e01203050500f084000e4000308400d4052004904189001510f103204a604c035034400e0718005560301345250024a003141610a030011940100040b030b02103000c0e04161800c442d0800c1015030740f07a0300080c45c04e07009405548440c10560011401040c0c00302a0141107104001d890004c2000e490308003a000192252500b0f2155110300380b185c00d002c01d512035800341c50a50301d12002c8900c5121408500e80e500914083c84515903556039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 449364950 625 449364325 449364337
    0x4080307050f10292b03020f0607080726010312020f0f071e0f0605 31
    0x100741c14180f403030550350036406a10701900b02e840102401402d100a60340540ca60401d02c03030306000142030b011940904000240035040c60b40300070710b0740390503403a07064029000c803003020100c44d20255036400b08075034035400170380e6000104030300c90302400f0460307980c0c007001d90400c9201c40041300c00602e81c1ca09a00c29900c426940841c0c0c800d01d17406001c030152111034400544490241e07041d103181d6410840c4903042064092010a616009050000c240a48880018040c2c00350361010000c10a030055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 449365575 625 449364950 449364973
    0x303030a05070f030203070e010e22021804050603061501120c0e010e031614060408030705 41
    0x40c4a6180440650f0700031403c1348400c90b4420041298654004010b5208400c0c02040340406010300081ea4400070300c02c0e0100c109080a145115000a0b403c401c5081800070b1362004401038030280030314100840041d0311210300900c0700881c90f0074448040e1301c40e803080b420903034034030340380f05d0100064031002000034106081007690034045810007807010044d050014812000c001c2da01e0310026040e080101404800403c0850154020414032000c03030807903000c0c0000c00071944554010035110006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 449366200 625 449365575 449365577
    0x31008010216021806030a120c02040905070303020f03032e050301051003120f1409030c0303030a0507 46
    0x8240e8030111803050300c0324400c070720b06500441e554411420010b0031400303078100c1c03056015100c1c4089e00d10f065400340041c44942c00c503142c8140d03581e001c2e0004a002d03001d506601141c4000c0042030303900c1a8003842c8518000074409890980785500004003030382c1030b40348950108568a00340180b038081c0e10815009031030031785503041018107a4014100e02007000001c2d8400031040ea84420030700315803070710344c180c3c02e61b1401d0781e2001a190040c0c00b142c0d00d400d0b01000c01004080a62903000070300c45c61391 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 449366825 625 449366200 449366209
    0x80c0f37051c12050a03020d020a03090c120209040201030c020319030c02102003100801021602 43
    0x5590b200140c00014500180107511030034503ca5001d90000c1150a608000040e401340758003404803540010aa00141290020307036580001c121390740d8200030003010b1103503000d02140302c864046640581c0706c09a00a500c150207003804501030302c00c480120b20b1482180c102c0b84d44000a0041c95002036850f40205030b05503156801c540c840c42949030500708694911408103298100051104c40041da0100034541c030062500c039008074150b58440c6542a640120144a201d50618a212007141b40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 449367450 625 449366825 449366839
    0x1020d03020c0d0302090315010b0706050906040f0311010f020f13080c0f3705 36
    0xa0540090400d801440b29803203402c000554035444114030300380942c0701c0d15a080030916124005100301c83c040314035000024040861001044118000d4405001036541c04002c11341c0c800701030f20003d209200c801c00140102c0e00c1412030100002c0341c0d0740041440d4000d0407d400580c0c002031400902c003540014409030848004015800411245000c1d0039400182c000140017103202040300c40c0200b10701103060031442c04218a0b04901000048081002000c0ea180344400c94030b14003c2901401e5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 449368075 625 449367450 449367463
    0x41101020f1b0405061513052115040809120a11040c140f0d06140102 32
    0xe03120301c40b510759626003181400c2d100029082441c51406810042c1c0000f0090255003a807058050b002c003091b403020841c2080111648403c2101c2d0405d081c81c0f40ca8040741441828094180d018816154400c400045000c070001c00081028070004d44102c075090f4800800820503002101d02042d1100d060050950700040708055402581c00d2600030398031040c00a61700c80c154420b50400000305134014444080c01c805040c010b024a078082c51003407030040e103100d0780c00320010004c16000916000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 449368700 625 449368075 449368093
    0x1b05010504080918010b1905070606060512010504020306030a290f0412081b0307090b0304110102 44
    0x100d0b8444c3d0803080d45000b01d003e400d031003101402c068840b00c5603c01c400d25805902160f6400d98030260070000307146e403010001e00c15002508800e84040300400006003500d024000d5a003c0c2e44024041c0001303c0d0350340d5810200001d40700140c1006607043c60030303600070310101c1c04240c41000071a12034209031801d0720748840a9000000004181b00344c00e014460390800d070601c0c030030000048103021503a86d1031b10103082c1d40e029480d5001c080130000c00010801001180c1e408500030130780a80803181019 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 449369325 625 449368700 449368729
    0x604180b0613030201080c190f020102070f0b0f18060a0b1201022214030703031b050105040809 43
    0x61f10f501103070903451820155a1134425890003c40b10341c010654000115582800039400142d060030440751440c2c01159010308a013000c500c0c2d41d850640103400d08d401d0400c404484000d80001107211644042111070004041901a0200d14440d046500310401035100060108040401844001280d215029a40003058072402801c20700c502c03462001d541948540c40820000b8400c0c0400000da602d1010908010f0311141d0351242540c100741c0f402c0b0740d070300310100790ba45042c180f22507582100d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 449369950 625 449369325 449369341
    0x31d010603060e16210c0e07020102130609180504020f122a0604180b061303020108 38
    0x2220b40d4801c1041e100c0800061100e04c0c410000501c1005d41800c0020805105401004001d40e0000a200c40186c0542c004c19074064008600c00c4000d0759094281d0302d0100c0d9110310741c0b50f09401d001c3e00c40c5400a0344d208a0380716100410301c4141030100b00c0401c1000b02880c0421a1903444100e80001640d840c080b240e06220014a098100d0210980071502074001c0303114200359540600c8001d26800c019400105038003401500c0d958454100c04c0007a65a41c1d01c903c800c0e404540d0b4003000c6044a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 449370575 625 449369950 449369983
    0x10503070b1806160302070806101a0f04030b0108010e0c120d031d010603060e 36
    0x151080070708040080c0300e64401c9005900303500c858840300901c540e00c1d00881d0200c060303407140301d01819005a08483c9040045400500145a01c00f4420341803105040c1020310703920319040382000401e5407400100700b035000240103a00312006542c00ca90a0700e465a0358030354140c082c01410301c403001a4003c404d44202c80e07007042000300c00041d0680d0041c10003100362400480c0101140c41c403c02940c1e1003030100c04182d286c00e100d550003650268001240c1680360300803181c90700d000e0003140c2082 = true := by decide +kernel

theorem S144 : BRFrame.sub P3 P4 TB 1680 MM 255 449371200 625 449370575 449370583
    0xf0609140c0a0518030109141c0306080316051e0102040608060315010306051902041805010503 43
    0x4505402c082d0592081120040300045000c00b003a1041c0d90a42c03040500700c1e001b880c03600c90003080c8140c850310f401c0411740e0540c6d140480340b0100b03950b85c461b11580084d166031000035454400c10046034100c01c4603a8604807014400c820700d000f200f00400c41c06250303000c0c0c07180c00503031180c0c00e118000e04044001084540258002040f076580024919240e90460b60007081c00112a240d8059068a429021840580b0b0500018002440c141c0d02d2040805140c2c020344208126600da004161f22 = true := by decide +kernel

theorem S145 : BRFrame.sub P3 P4 TB 1680 MM 255 449371825 625 449371200 449371207
    0x12040b04051903050d0b010e1f03110a0e0915040c09051206011412010f0609140c 37
    0x80e0300340c0c8030b0368205000021102c0140040360341b0281080407030807130300400d950751160460310b810030194025901c0c84000805021a08421a4003101d29400e00c50070b0291a405491309040b5042524655510303181c03112000101c010070340421758032a06014000c404583d0100e1803a0458000b100c40c1d07951081c03108040b03500d4040c00c1c081c06020750000e141403000c03030405041c0c42d180c1c007101d000005080f201801e000d4003200c1041d00041d80207a110030200342c44038140b050b290b4200303416103000362a = true := by decide +kernel

theorem S146 : BRFrame.sub P3 P4 TB 1680 MM 255 449372450 625 449371825 449371873
    0x180604060f020c181302010201061509080105090c030d030b061c0b03070e010b041403010212040b0405 46
    0x510301e1010f01198400e0144201782850500e500040b03005017965048174060200328100201d2460b080020042203400c61802400741c2c0c0d41300300d5490b40718404442102d41580c484044020f01380e001e42c00075040204060b00d618100510520f08020004003480664005a5514a80f201c07608040c421075025110480b420b52095140034072980b000e119901c940c1f40e080503c1d00142d140742c5e800307404566801c00e24110000d42402c1906066401802c142c40444580c42983d2260001100c1000081c032 = true := by decide +kernel

theorem S147 : BRFrame.sub P3 P4 TB 1680 MM 255 449373075 625 449372450 449372479
    0x506070f0f1e05041d01060e0a061d04020d05040b040303050a0c0203030408180604060f020c 42
    0x740c1e10a8846800e8a052400b0301124210381006820a1743e24100c10140c1d44403080c032201141c90000040000e143c01c030b004000d40c00812140e1071400d030700705180144010300b11520184c403000740300360101c0a070b142c6504407043c44464a105215030f2a080c1130000441c8800d0780c044001a1402c0e001500840702c91050700d82880c02eaa010b140385494130f031903020701a0810109e8412840140240d007405a85940041008281503101c110001101c098080d017030804500407640650a01c018004 = true := by decide +kernel

theorem S148 : BRFrame.sub P3 P4 TB 1680 MM 255 449373700 625 449373075 449373077
    0x60b1305151909020c1510060f0f020705090711010509030a0906030e03040b09060d090506070f0f 44
    0x8202c4081c0c426003812a400142c0310b0700700601881401004161044050482d00784141c008240c0082070141d54000340c500c00b4103a001e913204441403101822180c018200081c00d04040c000ba0400082c4203c042c4104101d0509904200b403150f14400c00354034016503110030721408000d01450b40c680c891401c1608010109004410200484080300d4001622507510302100780810442c2c01020700c5418168034110411084c41008a403103846026150781301e0440184950f0262a0804c109030250 = true := by decide +kernel

theorem S149 : BRFrame.sub P3 P4 TB 1680 MM 255 449374325 625 449373700 449373739
    0x5090a0201110d0f0e0a090501030f05010e010c050706020d060803030a060512010b1804060b130515 45
    0x40c0c00001c007400781e1300800ba15100c558442281b40b008220360889204080c004c500030015400000203504080782120141c2806014503410304000684180e00300c01100c4e2070f240d00c4ce000595486100c00100000d00030b80d000f030726440c00b001040c008050f0043d0000c0b000ea44085a0307003507280c142d40000310b00b2580420411504880c00c0000c403540c2c1d801d80c041141d8018010800820290b000c00001102240c542d01060000fa44d0380c003c0c004800072000340004615819104040710700766000404 = true := by decide +kernel

theorem S150 : BRFrame.sub P3 P4 TB 1680 MM 255 449374950 625 449374325 449374337
    0xd0506040b22051f0b0c0709110a03050403020c0a090b03061006080a0507090905090a0201110d 43
    0x42d440402c00800140b81e651907210448800d5800380d1640b104603880000b06142c00c25000a1400150503412a24080c3d80c030f0034101d04907038040c01340130000c070414003258084071301c250025500706003e807044030a01650000000d1114030f4550000b80341d1a41c86070b00144908090142c42e034043c6031a075981400c10710740380c0c000d00058401052030107040c0d03a0b48001079a840c09080c0d450090005030340308100d54030344802e01039601c101a4400781c0c04220b5041c0788000170b00c0300007100020000d03a540c81c6 = true := by decide +kernel

theorem S151 : BRFrame.sub P3 P4 TB 1680 MM 255 449375575 625 449374950 449374999
    0x303100303050c03160f0b01050f0f1504120807021c081c110d0506040b 33
    0x102090191005000b00980d00041d81d2400e000c000e003039aa107240f40316040300c002c0c6c42031082030180003501e80e6450241204070780d076084803210701001030400d11100125601c03504141c44003d0704103030b00300c084800604500c9080c00800142c0e003080605600071000c00e0303020b04915549502e2400500e4800c8141c1d5130f03c107548900307104540d040d4000c42c80030000c0354041c1c1c5a8503692610381c2d401100240c200c0108a000100d03503490210300784000c0d525000c09441c055040e803140100f103013101e54000c = true := by decide +kernel

theorem S152 : BRFrame.sub P3 P4 TB 1680 MM 255 449376200 625 449375575 449375579
    0x1080a0b0a060c080f12071b0503041e090e0a150e0d0e18190b03030310 33
    0x10b0140b16641490004011483c0c2c115902141d000001c1030f110340802c51604808102500c0fa4030000d80c1c000038201d18030101d12051011154060001c516140c40c0516960401c8030240c42d001d8496048180050180681d000707070003001c0080c0014001022181c58565800d003811001d01044514004021001c0100003a602c1081600e6040041d11014240009132200c3d044c0003180004d002070405001801d0b14a2118160000b0703048414040b03074031000309041e030301e000498030261507c10314001 = true := by decide +kernel

theorem S153 : BRFrame.sub P3 P4 TB 1680 MM 255 449376825 625 449376200 449376209
    0xc02060f0c0a0c080414101412090a0f0803070305090705100c02151801080a0b0a 37
    0x840d1954001620410811034800c0c2900c012507030720000b40c8086d0041c8840707001418410001c000d128002140c0250500c5000c031090704003d0058001d40d40201e40b0305051600680e95030712120b0a0072015a03006140081d40407030b4806125441c070180d03104e80720544081225480380d42c0380d10755580691051540c00005034004c028241e209000f1024404e101500c82c0d4008000c8079100c0070303d600004039200d08101100480c0c07680307690012425811a252403c02c201454000c0d0100300801e515020303 = true := by decide +kernel

theorem S154 : BRFrame.sub P3 P4 TB 1680 MM 255 449377450 625 449376825 449376841
    0x71d01080c060304060e0d0216050105070314030a0e06040b010509160215090c120f010c02060f 43
    0x151030b107079116824071780010210085100c0103807080e13512855507140c01103620710f401c041c001548403c050340c40d0015034291050200040c0000d0014402d10320480180d00170b10340108080c000021029007001c1c0844c5800d1050700c2c25980c0003001c8004200c640313041815254003d52800b4050761030b82c483d4801940e503e01815410404400d042d0001d40054020882201404001046400d00306901103100784c40b02d0100c4400f4006508120a40510078000100c09008003240014880d140d07a690071 = true := by decide +kernel

theorem S155 : BRFrame.sub P3 P4 TB 1680 MM 255 449378075 625 449377450 449377459
    0xa0507081c0f0e030715032f03062110060602030918061201020c071d01080c 35
    0x615400e4000b5400c2004401000900003070500d40241e000d6440001c6140754031000c41e51610401c030108800ea200c01c10543c02c0c01603d804410704e500b444000c1e2020000209540c1d5442c025072a5680020300d50301e026020124018548030ba10302000c0f07008190a0480114080d40040f06071801c228016240d8448201c00c07108208040601604442d004241100a503200e01800c0c0002d00c42c14500c0c4004040b07003481e0144112449402e120411090340c08103005210502c1c000c030b024003441c4011203 = true := by decide +kernel

theorem S156 : BRFrame.sub P3 P4 TB 1680 MM 255 449378700 625 449378075 449378087
    0x20d0209250e0f0f1f030f0f0218090c09010c020609040c020a0507081c 33
    0x312036456038008100da91001600d0300030801a074520150000314103541203402480800034820890802030140c001901c0c0080c85100036001c20326160115102c132507001c82c00c241e01c2e91200c18101d141c41c06281d10039406a4000750b180e10404484606003822030000324480c40c410400d00c10081c04200c11202c042e0821300e82440b0421050002c11725a00c070b074442481d0024540001c01d02e201d5400300300d8912040c810025500442d64601003141c1e12007022262029505c5100008076a0a01a50b = true := by decide +kernel

theorem S157 : BRFrame.sub P3 P4 TB 1680 MM 255 449379325 625 449378700 449378719
    0x501050f07200a030c0e0c09100c02011719050f220512031f05010c020d02 34
    0x490208000b9030140d442080d42c45085201000c0c41c4901003001485080c01071070014400c00900e2040c0e20700742003201a0780f07900c94490b055203001e00c509164a250004d4030042c0c0e07105406a0041c0c0c0d03440221030800200580f01c80b23405092002c0340364200015140c030400e0b0300300042d01315600200204803031a030700f05000111070000c086070b000720305032000c0709160346c4030034200c0c2d02c2924a070f0300420407440001050319031441008020602400c20f40c20300800b50340400c50950f046000a0310458404 = true := by decide +kernel

theorem S158 : BRFrame.sub P3 P4 TB 1680 MM 255 449379950 625 449379325 449379353
    0x80f0411090a0e070905070e03070e0619050907180602161404060b0d090c0501050f07 39
    0x860350b40c0281440d1034010054442c0c11000115000e461300702c6d0f840740c3c42c1a070714106041c1842c428035940781c1c258000d0310944860000000c400d401c0c00c01540c28820701d60100e541126a4440100703001000036120040010840c0e10744522807190042a04010319862000707020303204400300720961954550040d00300301c417922680c4009590302c0750081c102034606903001c0e9a8402d6030002c044002e2003440e000700c03891552142d00007444d6003e00e0903180c540d4107929903030303141401558902d1801607804c = true := by decide +kernel

theorem S159 : BRFrame.sub P3 P4 TB 1680 MM 255 449380575 625 449379950 449379961
    0xc050405042301360503071a010b0309100b01050c0106060503010602100207021f120509060403080f041109 48
    0x780e5103001d04c01c695074950b81140c0110808603003400b04108803204203100c59404c02c0c0034003001c5d01514110310f000000340342c0e40e0081401c9145225503501c90034045901c80c00444402e02e08002c000d002c0d41d03640d440c00500b103910900c6208014003d8030120018402c4500807170740200c1d0010000c030320030010040e890460044c440300284c240004128a5900c501c00c0d4001e43d403041c48101c0c040c2031185402e0801820781c0c54010a0000302100000400001034414017080130800b000707580201c3c10381d451 = true := by decide +kernel

theorem S160 : BRFrame.sub P3 P4 TB 1680 MM 255 449381200 625 449380575 449380661
    0xa0207140d0b0f040c120206030105300102130e10120c050405042301 32
    0x1414030300c1c005501504404032407829240d40c3e490b01408480540b00e003010740c0030000c0c80c08a42d020515000c0d4020703221515680c00d020a11203591525040d41d02c5001030241c1281041840f00038440d40081680005a6500000400f01c1c4a148041d080001003800b07110030f01046801c1003000794211000c0000d041003021807402e0034003160a045d0f010940003428036003003000300542006c0100900c01485070b10030586601506c814200c95907076500124240120b00c165451040d403c0b8146249446 = true := by decide +kernel

theorem S161 : BRFrame.sub P3 P4 TB 1680 MM 255 449381825 625 449381200 449381209
    0x70204050a09290106110d0e0f0d0501020d1a0a0e15061204060c050a020714 35
    0x116000c4021640d6183c2d9000703100310030a401000030182141440c0c0218050b0020310500c090a4a04076413800c0000f20400f1807c1c8610304205144860310005100990101c465940807208003600024402d041d401070180085180341008a100003260f6114070080b881c440542c08503000f44100310084800c0e411580c400d07002007a1600c40003034400060025009a106203c08007017220030041000002d10580413080ba080c1446403d121042c00700a503241e42500030300030b0206501241407100d466 = true := by decide +kernel

theorem S162 : BRFrame.sub P3 P4 TB 1680 MM 255 449382450 625 449381825 449381831
    0xb07030b120c060915070b0f0a0f1506050903030d090c0806010803071101050901111603030320070204050a 48
    0x7584006804c00e021002009038030b022650010380a90006c4000b000048ae50b24041c1003260f01007a404842c1c250420b0703003042414030480c0030b009004c8001b810740b45080ca510740124102c3d616000c045404d10300403c4100040c41c000d00089006043c400007031440c2034815501c038000340c2a44208941071060102e150041070f4031405911409403401c4080f903d0003424143c1403100000740e840f08800003402c24400520300c22060303403d80e06486034190781505141ca2907080202034100180210311050f9 = true := by decide +kernel

theorem S163 : BRFrame.sub P3 P4 TB 1680 MM 255 449383075 625 449382450 449382457
    0x807050901032409080d0b10030e070b07050a140a0213020c060a0c0c0b07030b120c060915 41
    0x20780c1e981c41d005c6074010514885816918910b1121034903081410361303031080051500340203c0d8052203185403110b4040c441c0350001e80000500034100320081c041c0d1502a50807e6070b0205034407814141139292071606000700c0c81601c5c4105030001c00300c000d10a8940040e180d1004040603550980810001c08800107c04203100401c03010800103280380c100b86d4801d00d800d5801203440100070040c04102036030226040030b180c00401081c0c1541e2030348415610340c03d0b422200c00004c0464007441040300e21 = true := by decide +kernel

theorem S164 : BRFrame.sub P3 P4 TB 1680 MM 255 449383700 625 449383075 449383091
    0x4080702041a0a05011409130e01060b0415020a080f1303081308070509010324 36
    0x9006000b409545a600e0220405403800c0c0c0480780b15164003040058558003c103124101e00c24000b1491781004042c00421036800c50b1000085081e03610b0f80d045042044007842410043e113075000c4481d80f00d50501c001c40003580c21198958040d58003004541010810100545001c0750941610690f034110300341441d41c1a00c03903a0700082c007031b40c4081010f12010003041d22540c05e99400c0c1e800c0f070780348550b01c0082241c1c070402032102402802c1c1da0440d2044041c8001403189a60740060700c0401c1c08a = true := by decide +kernel

theorem S165 : BRFrame.sub P3 P4 TB 1680 MM 255 449384325 625 449383700 449383703
    0x6090709091e2a140f0a111e0607050c0a0209060a090213050f01030c050d05040807 38
    0xb002d100b804001207003511082410758515025008910150701e1810034040444404080b0003a0203040f070709590781703003010300380d031001401340035284100300d03413082d0360f141c450051020b68098500b10000450708000c002c40d5269a6440d01c00c440c80c0c41101c0b0362540302d4114000404c010308081140e40c0c2c00800c000c000c24445a154074002c0b04a821050b04000000300c001c00400c201d0400c0d4903d90300c000c0b400c1c601808184854000a01144100060203407403642e44c0b0006010b0103541000d075002036 = true := by decide +kernel

theorem S166 : BRFrame.sub P3 P4 TB 1680 MM 255 449384950 625 449384325 449384381
    0x801050d0204020d06061119020907270605070308012408090703020d08030f0609070909 40
    0x2d00b01721000501e00e0300b064500175101d0000085e00c245400840c0000051414880001e6100ca503020104003ca44182038040c0d40750034510400e4035408060952602c00300555100c0310000b18000341510402d5070048031140100b0a117a46020b01e481218003482e108420400080c040084000002d04481c4042090000458001c0c150344548500342c10541c51660044580c902c1e4040000082540d0b41040021180b0440b6140c2d201d8114504124049001d041e4200a031001d503051108414001 = true := by decide +kernel

theorem S167 : BRFrame.sub P3 P4 TB 1680 MM 255 449385575 625 449384950 449384977
    0x109020907020714040c080105060c010f0c09090b0d031b08210403020d0f0801050d020402 41
    0x114210742400058200030350078005140c0c036100800540c941901c041000c860361a40140c000c20040c02260300c141c01c0454407400d180801d4000802008050000703000b540b040d080054409407071405441d01d040c1c01c0203054000c6040560351100410b4055842c442c410900300c1c61003044841e9080d040e0303402c060421140410701d040140c24140102855046400740c034040c2402401e0420002410f82080f001080102001794410b0b01c080c1900c00444412540b42c01510010b4004c2c411052001600c = true := by decide +kernel

theorem S168 : BRFrame.sub P3 P4 TB 1680 MM 255 449386200 625 449385575 449385589
    0x10e011b1202071716120309090b1f080f0601090b18031e10050c180d05010902 36
    0xc8180074a1300382e031500345034019900c0c00041580070682e540c2d0b441341c5440007503040c3e0701c0d0741d9401d003005107541c0500302501d01960400c1050081a08201082c1c035402184403080d81c542001c0e180238080011000c001030324540c18801d5810051280b5284101156407000010205050261203d8042480c03d8066000d1819581100c1000210a400441d0a03d60700a243c0800d2000d07848500100e582c03842000d5465100d001c02e0b83d801d00d80b505042030a2080079000764000a1024044e4001c201d02c = true := by decide +kernel

theorem S169 : BRFrame.sub P3 P4 TB 1680 MM 255 449386825 625 449386200 449386229
    0x10b160c0e0a05133f1d120a0f02190305030702010e011b120207 30
    0x150841540841261400b0200c507030990343d0003800c100480181202c007100182e881c4d448001040043d0300f24400c2c2c0c10b84510703c40640c10301d1600c50070b100c0900d03c0880070603542101007003a550444145280007540c0300c80c20700c05000140300c00944907501a025840c04142c69806440b801c910084c881e08420403103060704102482a40c1042d41c071500300065110031580c001020502150b803c4c28580c0d09a4864540c41d001c8050034600648900c00395032a0f5201b0b54400d00030400a400c1e0303484003801 = true := by decide +kernel

theorem S170 : BRFrame.sub P3 P4 TB 1680 MM 255 449387450 625 449386825 449386829
    0x30a020711090a050405070602010b010207210609210c050a02040e162301020114010b160c 41
    0x1110f22500030600440c031440856a2007038a0309000d1b4280c1740900100b6006a00005040000d2204500c1c40ca84840da2282440032080b6680c4505003901e000c99000e40d60182e1422007540f62a4065132039030074455451800204c02c00c41e503aa840c0e21140d840340013900c5151a0350050411040030301015480302601640c488203155103901615000e03041c030b5400c80000790f010320110329650040c003034110038500c0f2800007955607003000e5285800360444a84000c0020480741584000703603e035080900 = true := by decide +kernel

theorem S171 : BRFrame.sub P3 P4 TB 1680 MM 255 449388075 625 449387450 449387461
    0x5060307081e0103030c0204091103010501080f0106081c0f091203030f0b0a0308030a02071109 43
    0x10403030780e0003001a030400204085030b210164030481615940340d503d01034509100c420010b806151281d4003070b0203108007ca03c8200005014008001c1c0390b940e2500d1546441c684100c00f4215400d00200040c5061700240f8620715602109030a110b0f04014402910b8044141c0d030301c18148000d4050010b110304513003025a048034001c1d2000b0404488040d2104221010656100d21804080e0010710108080c64243c070351081070007a0040e510455410100140d2404000d22940515103030704006 = true := by decide +kernel

theorem S172 : BRFrame.sub P3 P4 TB 1680 MM 255 449388700 625 449388075 449388077
    0x6141215040c0602012d11041d101e060e031507110f0111120a020405060307 35
    0x460902e03840b82c00e0155180034000307810300902003084d01710900714003103003c1c0c42d8000c01d0015008000b4448181d503180300c144004900c8202d050002c0d0421880500702c1c13205810908100f031400b000c194410721004519241e117100700000340c5070300c100b2640d85040062070075030348034003081c18100740c1900303040c14031160010044040d4001c01e0341900e900d441c0d02204c101499040341c0500b03e0301c644010320740c1c1071030600c0280c84a40b9140c40c019404805000e000d400e165454002c03440c2a001914a24 = true := by decide +kernel

theorem S173 : BRFrame.sub P3 P4 TB 1680 MM 255 449389325 625 449388700 449388713
    0x1b03070201090c0b1801030509160803090a080d0e060a03020d0207060e0f010614121504 40
    0x103842d042c0381c00c00c030304443c1c0303160b01100005030200880b012900903014480c2464100f4680803446440c6c010140303203030180561500d0003800c20b81400140b40e045c0000180f03040301c0d041d078510030b4017039454200a840b00500505140803030120544402c261034084000c040124050500504181200c003000c0d040382c1004008031082039031240300c4800c40e0750403c0520380300955107000b44003003428482e0800380c8000060700e0901484460f08800c1c504032040c002c0320261081d8113040040c2c0c0ca82410500d = true := by decide +kernel

theorem S174 : BRFrame.sub P3 P4 TB 1680 MM 255 449389950 625 449389325 449389331
    0x909030f071a07020c28050a090c0206070c0c091d0709060504150812031b03070201 38
    0x40c02c2d40050084a00c2e20f450f9244126214411240419400340305900130200300324002c1c0c00103040c0d2000894080020359500c0c0412090009a44038042c495682d4884d014025010b2000c958002601d213045440c6032074a58405001e80030038011402016680d12040c2142100d03804d10320140c0b01d410f42142d4038299a060f1410140a450144601507030501402d0008512882500025214a0300160040100750415580035400003040c0242d44800141c0d088041d421010045001d140ca0368004 = true := by decide +kernel

theorem S175 : BRFrame.sub P3 P4 TB 1680 MM 255 449390575 625 449389950 449389973
    0x7060510031a0a1d0307060e010615081504020a0c03080406060314070815090c0909030f07 41
    0xb00c00c82003280260b402420018120b03c4d107003942c0e16000d60b500d100e500002070500343c480c602c8040801003035000f040200103049108080b6411003034001e20700c0a0894030b660103962140527802441c1014400d0b0780c5080095203520702603058a80702540e01c64801401280c00945580e4080000b521000e1004000807040e0001c04d0820f040400003400c100ca440e141d09100d01102042104100000a0700c460b180c0055412204548480c1801421352040e402001032407880010b260081080f900c546 = true := by decide +kernel

theorem S176 : BRFrame.sub P3 P4 TB 1680 MM 255 449391200 625 449390575 449390581
    0x8030c0c04060609030f02040f0b0a0f06090509040312050711070803070b06030106030807060510031a 46
    0x40e8499803808200084160040446400b1a5042681e03c00001001e4003400b02509035074101c58034290352148050f107241c0e01c0740c003501c0250842d124032881d201e0410b50044c0c80c4460350303041541714290803010000080c4c2d0000814400103011840071501d0785035464250f44403c16101d51004600072031101044004000016250749401400f89100c03549a05061500303e0b03049000c0980030304c1040003601e0101d9042d80000c1c2d040300f403110300c0f410100e54030303240d116082640f2903102420313a2041043c = true := by decide +kernel

theorem S177 : BRFrame.sub P3 P4 TB 1680 MM 255 449391825 625 449391200 449391223
    0x40f0b030a0f1b1b050309060a020709090503120f071e09030f290103030f0e040608030c 40
    0xa465130411241c0400b4104030a0f980c00c00041c0017208070356031000c0464807107484860390f14080345800318540144501c2c619210707000c01070003800000307010040580308000c000340e030390388180303111011041c2e07501404240168004251289914040307420040189404001a81d0f0b949907203603400f0301510160b640401075091a0002e9103580140c02259101260123820b40d4074507034000b070441c1280b2143d07108000c00810641c807640d4558001100601003002101d132102c581d0200c060319011102e44 = true := by decide +kernel

theorem S178 : BRFrame.sub P3 P4 TB 1680 MM 255 449392450 625 449391825 449391827
    0x60c030d150803040b0f09030106030303050a1b08060d08131509080102040f0b030a0f1b 40
    0x200240c000306031416002801e40d00808180c2c0d07006010501c0f07081032050052a80700005c4243c030b810020040002070955a840d002240020f80302d00900c0a441100c1c024299041d285240d650b0160f5038411000b803c51000030149481003006003021020301190b0421201d011100d100c1e11802c442c0c54440c02c4003510b10b0000e1007000200c0c510300008075007030b040c4290b5095a4414110440b800d2070007030b40641c00c3e00054070003030f0019510401c02c20982c4a501c00c0301c01002d0b1815011605007003420f0 = true := by decide +kernel

theorem S179 : BRFrame.sub P3 P4 TB 1680 MM 255 449393075 625 449392450 449392477
    0xf0c08100e0915071e110c0a05030c0d05030f030408031e060a1401020c060c03 36
    0x320001820600d000320245003055001165a4618540500d2145180c9030024003480d00c1000311130200751542c01d0400300e8410b40000070b4080921002d0390f203d54403c108010b2190300d00044124101d4002902074500f1861b86010f000d4000c0034581d05070390030700c410421a0040845503000f14400c5002d142c041e80c40f4200030106481d1440384103046903110501b40203001443e070310f040b134640880d081c0d07c6a1145040b07040e00180d0400006007071550340918041090703100d0b42404070090022940220 = true := by decide +kernel

theorem S180 : BRFrame.sub P3 P4 TB 1680 MM 255 449393700 625 449393075 449393101
    0x110f090a1d030301080c0114090603150f040605090c130e1315021812010f0c08 36
    0x82410140c0d50010449058407851780142805007035880055820544075403501154071400d002001d500d40b1440d0195200307042a09102101d401107409021540c50344411050042d4201802806039485943c40160418440c0021550f80c1c4585c50414120080c107801503050160038234140311840180111708005180100031000400c200c0628078401c174868440d510019624a0f16070910398035001d06078841c0c5181c2440003040490b402c150f10750071a200f00f6041004501580305104c28121050703 = true := by decide +kernel

theorem S181 : BRFrame.sub P3 P4 TB 1680 MM 255 449394325 625 449393700 449393741
    0x21306110f06010308120601021005040503090f030a0f080c0a120c030e0d050a110f090a 40
    0x903418001d03502c01001400003404076419182002a0aa01d40d1856541d17900100d20307001080c100c6410b400d1502041c042845008002801c0180301603400740b41c5810001d00b0302d5612444a480545040034016683c03002508000003080c48400040c11601c00d40300c02c0c0c54451208191404d81004100c2c0b900102d41003640184030340e1a01c410481d041089200142c03034103915001c849000911440c6041c4a1407882c0c4e895068601c00018003078100354107071400c100320100400d160001c0c2d420035411070 = true := by decide +kernel

theorem S182 : BRFrame.sub P3 P4 TB 1680 MM 255 449394950 625 449394325 449394343
    0x702040207211b0f030c0506070c2003030313060e0102190e04110a050a0302130611 38
    0x2e00071120300c070001d442603901000c0b0842d840c01066580c980030f800c1070b000c3e2400c1c10348a42c032502c40500c2c0640580c2d50b180000e00f00c8002c0000c4c0003030211203190b00e075400d050076203002d184140040e590b40809400d81010f20341c0c100c54581000782c664000030003481d03644000d41d03c411030490107514000749000030f40c010600000b80c11100386842e102e40c00d501c1440b10340c42c5003031004104046442c0e4121900e8502415401c200b10205540c01c1a03081c4000c010715030795203080c80603596050b400c080e484 = true := by decide +kernel

theorem S183 : BRFrame.sub P3 P4 TB 1680 MM 255 449395575 625 449394950 449395013
    0x70203130605090d170f04030605010806010801110417031c0f1a0f0f04020702040207 39
    0x20600b01c0c41e0039810303004140b060203a118007904910703600c0302166a078100360045600e1607071410b48054079240c0fa0310b4038101910081c480e8800302d104200000c0750260061089200351030503034028515080c03030511400750b07400940ea04040c1602040c400b03800c18000c1c0340703140e422440010800189030350036040c0a4003191601d000325541640d04500c640345c2c984400010b10055036048529031000380c0400001400380c8030361a80207400c64004240d0f6002c004a4501c000030000014003200d11a8402 = true := by decide +kernel

theorem S184 : BRFrame.sub P3 P4 TB 1680 MM 255 449396200 625 449395575 449395577
    0x10f050613090f0803191b020d050c060a09022b0209070908060612070e0702031306 38
    0x38056845410b512002c1c00c3c0e00780716540c85041c005c1e00701401c0b00c20f10b05008020100d203025a401452080300001d4042d00ea03071102502c0103403800701f08103414410302c5401d010188100e14040351003903001140c0d085c04100c040c16440003800c1d0340300c101c80f6410380066602d10700b00340d1401d400f040741402c3d00c29644419141c440c04811f0f26007a40d148500400396101b940090704070b082000710801c01c042d00c0c008491199848012500c005182252080d0044c0d001040b5846c00e42c2c0c910b20144000d1000d = true := by decide +kernel

theorem S185 : BRFrame.sub P3 P4 TB 1680 MM 255 449396825 625 449396200 449396239
    0x1b030702180121020127080a1113020702060a0804020609030114090c090f07031d010f0506 41
    0x300f03503800141c6e402441158200d80e08103d900c1c014a42c03000c41d0042031001c0d070200c0500c2c8078420154003041109034641081401c11a01d1800841071501d03403205904c502d000095018404002100c0e90500650b09540c01500140c00607040c000104003007401c644c2e2003412410011084c00400c04e41d04010032580038100c0d4156038440c0e160801e031070161400070020304400203064031168079010440300c50b468401c9003c580c1c0000e1041280302000c0100070070f0300740c40c0c0d140a0301c807110410914505 = true := by decide +kernel

theorem S186 : BRFrame.sub P3 P4 TB 1680 MM 255 449397450 625 449396825 449396879
    0x8090c03010b0a030f050c060307020a0302010b09041109180d050406090b0405061b0307021801 43
    0x2100d000b503000620300f1040000406a40c15944514412000e4481100d101000502d050300212403010150700080f2030b0a08055083c400c0d0b114170901260f10780424202915814840c132441703e41540030340464004140c030315629030342e1072080f16076000459413aa80100b00003006600b00c1c0c41a00042644541c01040022603481030750203849000d41a1401d00c902c4140e128001d803c82c034003a41c842d010402c41d0b840540c4420b03003440713200304980709903030520f524100000e40301085005042c14010f034 = true := by decide +kernel

theorem S187 : BRFrame.sub P3 P4 TB 1680 MM 255 449398075 625 449397450 449397461
    0x160c0503010218092d010905060103060305030901080a0e0f0601090c02060709030314120708090c0301 46
    0x800382030f0745502107800c3d110510920801d00050346140301c0d41c902c00c20070701181e2001d1482c1e162201c489891030b14280a4140781a180070002a090b500900ca00f1040c0d81c1c00070010750901007202c00440b400c8030700400300040c180d281c407184105001c0030002402d112541030003410056041c8a07040040740e85907a0710004640c000f00900c070006030003c5c405402e0f20341500c1e066000c041410507810320382c81044044c90681c440c1804220146900003c1540204000d07001c0e90f85001e030280800d03007030701d4 = true := by decide +kernel

theorem S188 : BRFrame.sub P3 P4 TB 1680 MM 255 449398700 625 449398075 449398087
    0x20309031002030c09010c020d06020a030b1c110915060418050714120c040b160c05030102 41
    0x440120141ca0211170800440300c4401c401012603012980800c0000810285d10240c0840f00141d00d002910500303200c1080132001c5500d003120030300030303c142d18080040e46d16918842040001c1d249140a61501411110300b039070900d03151a00604085400070703440140011061442039205001c0003e500c83d89400c07107600885c2409190040360400c6000000421650860361000a88074101e041079100c002501c030690003c0e04004441010740c2ca500280807100410b0001080110000c5280113 = true := by decide +kernel

theorem S189 : BRFrame.sub P3 P4 TB 1680 MM 255 449399325 625 449398700 449398711
    0xc0c0219050603040818060304140f07063c0e01080f0106020309060309160602030903100203 42
    0x82ca0005807504660804a125184c00404801070650802c08a009a005c03030040304000c10040d002d1a0300c00b51150600a5482c004407201590b03036680311900600700030640403066030001820b00034240c2054403034241a0384610b041c41c110136440403c1d40003080001a4101440d104951b0400300864002c2c0358051000b62540c50000000e40b01d000c1c1000c8644035402c00408140413040402c0314100f140110300602403070035030b10a4045c2d80c1e640008070942c004c0c011494480201c24162003603a1180 = true := by decide +kernel

theorem S190 : BRFrame.sub P3 P4 TB 1680 MM 255 449399950 625 449399325 449399329
    0x30a031d0312040b070e1c030e040603060902010801094a06040308091207060e07090c0c021905 43
    0x125481d005061451f01a81740400e121b0300d0040750040c4c0c000e000c01c080d51403582c4110f55450301e51550204541e0440e104078003515460404000820880c021807808015028800e20603040c1c040c0080c0707009040141d02039240c0904010b07503038601011210280c0c1c0d03290868040e00000d9054011410740c030030201d1082d043c02e40c0c85031280c1c1030480c0e60303e40400030031b40010300450920801000050b086618018803000c4071490302e8481e4030540c01d0042c03040007070034801d4a449818003600107204503 = true := by decide +kernel

theorem S191 : BRFrame.sub P3 P4 TB 1680 MM 255 449400575 625 449399950 449399959
    0x2010b06040b030a0b06040518180a020915031c1d0f0102030a031d0312040b070e 37
    0x11000810801d84c00e5252001c5500585400c000e6402403d0000c209081402c080c002040c2155000c658172200d16154900134130080002089902001d41c000c1c0803801c080d0754250391900141019800c0320382500c14070007014441292600805080f0707525031f907081c8911100000d81480320101c513088500c034030806080d61125a0b000011500742078094103002c10003517140181350000c6180d95181c00101d0000040203107280301d104424910480c49051500c10b00d071a0f141041303400484603050107412 = true := by decide +kernel

theorem S192 : BRFrame.sub P3 P4 TB 1680 MM 255 449401200 625 449400575 449400577
    0x330501050f10170c1306030204050303070f02061b010b0103140f04110a0911090102010b06040b 43
    0x110603204102402c0340c90005001002009184514003503e50010140108045051540e5501c100c0c140280c2044954008800307141c0100410000c46d00e00000321003525401002c2d48905024a10010311540710301e8a15452a8000d030303d61080488065000c401921001d0702d08020300341c2c3c05009200301c508111038005d110b026000000b4085642c80865410020000f0309046040b500c40762a001104d8901a0a02c91648041000c9159580910490486e040304483c8642040c3ca00340c816030701 = true := by decide +kernel

theorem S193 : BRFrame.sub P3 P4 TB 1680 MM 255 449401825 625 449401200 449401219
    0x90a0c12170a120f0b060d0603141b0d05010b031209041d2833050105 32
    0x401c14a84002c00c03885242491900105040c1d400c0d035400030000a0750480e89251074112304100c80c4502c211815400551a0041e00d441407814040c4c6080e07002c201c45001c610317200741e40605450003440000384003484840024a00110341010600440b07010510140d140742c148100b1201424030380714039400f002c1d00c1101640319152070710980108540303250043c03413100c4c54030303210710f40b403980a004c4c90812001040c110000112100c0865a210401440d80041d20b00a00031349040f18809481c03401c0 = true := by decide +kernel

theorem S194 : BRFrame.sub P3 P4 TB 1680 MM 255 449402450 625 449401825 449401847
    0x4060506090405060301060b070809210601180b10031b05040815090a0c12170a 36
    0x50820b43c001e103611000245c00451000d6580d031020045910004080d20002c1780490035003103e1500701040c51a902d000c520502440e0b0f84203100c5521480b042c407506034600c010082c00b07820b8840d90740001d411842e00801d2222010348100014018240c00114103100842070b6201d680c0480c0a10b05a0302a1241007004007002d044002e0a006448005403c1041174410000002c0008040181280c0038048041a010071895070707107010448100031000c0b030407402c4018040e407040c0503440181c080c4 = true := by decide +kernel

theorem S195 : BRFrame.sub P3 P4 TB 1680 MM 255 449403075 625 449402450 449402467
    0x100c0503160818100207060b0d08070215070b0a0e0c0f0a09050a0e10060501090504060506 41
    0x1c009002c400514404601000c0e03e062081820540e00740c0344243c0000c0003e504016402d4070040d241c8140481c075407403c50b0100600e194401152414105680c0030400c00c090070108024030101c0130040000000c42128445d4445d20522800140090100218a24000c0d43e80c40c02c500401300081300c5405031380d90100c81011180e983d1703004a0f46130307100160a8081c00c0c91181190a52240005844200d049a001442aa4800c1e640c000e44c0315540c008100075160180300c0e05420400400c407000 = true := by decide +kernel

theorem S196 : BRFrame.sub P3 P4 TB 1680 MM 255 449403700 625 449403075 449403077
    0x90309090209010302300702030901080f04020112051f0504060302090114150c100c050316 41
    0x1942c80180d107581050340a00104060b5034040b0600c0c401001c103200400040074060b4259414204000e00030b80c2990001d1218003003030b1344c01c01c9016910942804203036040307070f880f8801a16500480e04901141c0c51815040144000e08800d000452803d03a0416004096640782000203648103404001d422401d058010803510340c0c01c070b0384001444001491070411040b001d403001042c1d0441802a07882d0307803003c80060290440c40c8075114030401145003061031840e1000004d0880e04000507080 = true := by decide +kernel

theorem S197 : BRFrame.sub P3 P4 TB 1680 MM 255 449404325 625 449403700 449403719
    0x506040b01380408330c04120c03020a06030b15090f130902031507030f090309 36
    0x4009119403510801d5071246500c950f10b140a16840d46a00b54480846941030185851400c02c0d41c64000325903405c3c10004480038a0540c0d0140404e00000300c69541604c465031240b5080c020b041e45035000903aa4564591001c3d00090320761000d01001e0034141400303d482030402c8400d50810b41c1d1140050040f54080210b980030381c903480c6c6140c1c0b1943e000e8100d100340300e401900f0307198030380340c01002070301c0031071045a414010070b0415142440d16082e0344038490030f058141d52028030460801c207441 = true := by decide +kernel

theorem S198 : BRFrame.sub P3 P4 TB 1680 MM 255 449404950 625 449404325 449404409
    0x614150c030c0321060103140414100c0c05060601020303090714010215040506040b01 39
    0x80296842030302e09012201000c642140e010380302051060319803c01c14001c0c0095000510b410580070700c0c08000380700c3c16081101010b1800740c2701400080c0700d518100c0031943c08204005002c1d0442c4c0c401e01c0103030300340d14024080000700300b8112080e024480c00120154070002c1602d1040c030b0007200604001e40341190031403000c2ea440e6103950440c06100e40e1401c9690b001c0c402680a82d10403c000e02c414a42802c0100100006800486506442c040e000340491b0b5041c02407800d40500350402 = true := by decide +kernel

theorem S199 : BRFrame.sub P3 P4 TB 1680 MM 255 449405575 625 449404950 449404957
    0x70e0708060a180507030b10020a0b15090c07021c0309120c12120201061415 35
    0x7a100d603102c1a400002e8007040703c2480d0880c0401c072001008100480307190000c01e00d0410309075507900e000f12229400d901c0c030307500910b44018165144400d040c1c020f4052001c0c0403110259096981e2005011841103032000c07440354031118079004000d42c55029980d2505001c21000401d4082a440980354050301c00b4800e0388a406113040c98105503075000d6900c03002c03070200c0d0807410708108802c80204410019880e4028807031207807241d140021003520ad80800f5030000c0002c9003410f1682c5540041e = true := by decide +kernel

theorem S200 : BRFrame.sub P3 P4 TB 1680 MM 255 449406200 625 449405575 449405581
    0x909110907050403230d1e0f180303020601050907031401063204060908070e0708 37
    0x5000b000400d100203c00260119801e000913486089035440301c64400c000c061a1881c200110010040801342c1c021301c0e0494200c1200000100381001c03980b24043ca0011504049202000c0d034007540c0c480b800100b410340128029060b11015604441c05940b61035003a0107880c41c0144070b982800c00c7d0001084568462a542500132030064002104420707000305c4d400301e11242d04440d43c481e8400041c01c0000303582008241008000742005000b140d880c01c8458101c00f1002000c030b10602c0030304000 = true := by decide +kernel

theorem S201 : BRFrame.sub P3 P4 TB 1680 MM 255 449406825 625 449406200 449406211
    0xf0d02031c14070f1e12110f1821060108010c020d140711060d1509091109 34
    0x19502401c010909045d22442455441c04150340004055441100f4402c18406280c0b10301c10b000d102e0003400c0c80c0c0350b0145024800400341d4014040300030b014040140460040c2800c03c50105003010710744840c039025a1005004014400c0d007445910030005040c806000c0404010341e0040108100c114104155203010843d4824090340900c42504818004c1c542d5958003046140c85010309001007022a9144c0f1500303000907040e19a018028805600030848a49100c01608220315000082c01 = true := by decide +kernel

theorem S202 : BRFrame.sub P3 P4 TB 1680 MM 255 449407450 625 449406825 449406827
    0xb04020f03070f090501140f0d0209030f010c0801120b130201020f0d02031c14070f 38
    0x5420104092114002a0000c2d201800429010415075907100ea00c0064100104003d02c0d09244200f100381c0310b646a8454850350f1807403030b8000a852032580c4407980481d25204405012203002e64107000c3c185008007485000c04000403100d8000266103842c603c4190b050395000a10010641c0720880304003443c04103030008034154025118000500389080c0b084250458098001c0d565413854400103243d080345104121140500c1d04034041e102c82c00c400e2255521400c02c0c00c0c030b400042c0c0411303c = true := by decide +kernel

theorem S203 : BRFrame.sub P3 P4 TB 1680 MM 255 449408075 625 449407450 449407459
    0x80301060305150301091101030e0703020f0405070219150501080c010f14160f1e08030a0b 41
    0x400207030083c0075000f0081c1c0d00c000d040000a48074940c840720302003481c2c00d01e24030b80d040c40424140203481d009407a0304110004442403000030b16000748007a045005003007102c4400e032070704191100b00070b024185d0080802001a41001100d0042c0d000c04a603501c0704016070641c2e40c10140d1b1003100740b400d05107003410305e00c008580da40a105014601e0b91a08000e6030540803c182c40d05213200441c0185950240c0f81e120400e000040c01c0583c1c4042d080400a000050780c00074507420228802c9405003 = true := by decide +kernel

theorem S204 : BRFrame.sub P3 P4 TB 1680 MM 255 449408700 625 449408075 449408101
    0xe0901181b050a1206031a07050c070f0518070210020d0e1207120804080301060305 38
    0x301c507501100750403403001c40d1501c0c1e61450f075500d0340d11a01400e00701c1e40039010340529180000401c00704030461100680741464450300c05140d05d450703c0031640c50280c082d0116180c06441e000103440030448034180b040328810f542c412000607000c450080c0d210300031500a40541c0004072101844001a030080139040d25607240000d104000190451038808580004444040001400814800303030360080003801800d8605003030035291580d680b400c1400180708031404d140d1188040fa54140180e1 = true := by decide +kernel

theorem S205 : BRFrame.sub P3 P4 TB 1680 MM 255 449409325 625 449408700 449408711
    0x9011704021c0501021e0405060f0307090e04050c01030b06091e060f130f060e090118 39
    0x8111a0360341101180b00d04002d01580204084c03c0740b00000c0c011201e00364003240d45440389100d51a4000c0c414042500d08015000c021904100c003411b000c121656110b03c26806404100c0b41507845400440114501e56018041d6164201044501c546410b4628001510307010340100e8403d000d80b928410f0b003020383c0f241000c49920b01c0c0901517079500c410014110f210b030241c650141904c0c58800384800102d26001d0555007581c8040142450016800c04d13012080901c403480c40a4001034494 = true := by decide +kernel

theorem S206 : BRFrame.sub P3 P4 TB 1680 MM 255 449409950 625 449409325 449409349
    0x5220302150c04170606010809030c0709270b0115110a0206071e260901170402 36
    0x4c642060700f041d0926143d041c0d00903c1c10b100a66030300c00d0100e50410300c1140550700c0c10401d42100c5594403818410091405d4807048030201a50341084610240400101c002c410103c4c18540b91218803030074050700c4442c040d5011407441c51446551881a07017800310b0014140c00069408000c0e244e0003d41d001c4030031500076040400748c50058000c2902152045079000c00940315001c0c1c035448941150f84080301214180714181311a81d0001091002c807040c0d041107101600c0307600205141d0b55182c = true := by decide +kernel

theorem S207 : BRFrame.sub P3 P4 TB 1680 MM 255 449410575 625 449409950 449409959
    0x1409061c0215030c090111070b0706020d2004050a23060c0a0b07020105220302150c04 39
    0x31800c59203030b0030a010030300f80c15071110310451b0100d5041141041c603518085080700880351032901550070302c1c8003519400c010750700184070f15144036070710080c036040e1440c1c001d4040080642c0362800350710340c4e00b8101446a184002c1d08801a5104543c41c4054280080441001058010340c5d0044d101c046030000a450426240c0b4000d1413901c20324100085958154419880b494409403804683d8004440c014840382000b81c0181c016001000e0070501000e1035070507540c1101c05015441d142c646c0c0c9 = true := by decide +kernel

theorem S208 : BRFrame.sub P3 P4 TB 1680 MM 255 449411200 625 449410575 449410609
    0xa030f021203130f050103140f090a0503040b071109100b0a030b191409061c02 36
    0xc00c01804004110129101d03c503207000d16210300400f890740024141424010a0959240388e030398071030b6015800002281d041d8a44407006481c20840010041403484009400304029034070001411402d4424580c0704a000c80041c14842e800e00c00780d85a00d41cbc109841401d02c01d40d5001409808580254900029190a0403001580f1070741c00909800c40c0f44482101803003c0340c2d40940c905c8007100180c5803075600d42858000b0410044098680d00c078160740c035590481c115542c00d401200d042c900 = true := by decide +kernel

theorem S209 : BRFrame.sub P3 P4 TB 1680 MM 255 449411825 625 449411200 449411203
    0x709030f060f14160206010603020f090f0a0503010e03030a2301060c0f1e0308090c0a030f0212 43
    0x1440c2001213120002c10840b011040076403d403a502d07a01c429007503080303018580010310010014003c802c051700f45003a000610340f50040c50140717000c0e95034000031301792900e40c0b580744001d800110a1003908032550080c03201d5044824000000341e130340c0e81c0c6030200c51034051043c10701304689903482100303100c0d0921404a1300340d01b00c0e840450300b1500d5807508464038450f0f0021400540341400140c00e081000c0303500350140000900c100c039850301c0d5488588040043c2d010a07030b030068200704292043c100 = true := by decide +kernel

theorem S210 : BRFrame.sub P3 P4 TB 1680 MM 255 449412450 625 449411825 449411861
    0x21020c0a24050c0d06091a010f17241203030c0a260a050709030f060f 32
    0x4440c02c01408030702113840e0645000c940300d403001034030030f0700020000b078184a6482e0794010544030b00c1038100011024680707040c901c606050041d40b4001200814a42080481c03283d580326442d001c5441605200d043d0b42c280e00d880e2802a103540c400001840c61500d070a030102c9095800a0014003c0c85803203024440e080024200d1140e0b0403072000c410303960750f05001d1001c3c401d980000c0c22080400415034014000b1981d40341c1050052130f445907000600d40c11040c1e0300805401302208818040c0c2da = true := by decide +kernel

theorem S211 : BRFrame.sub P3 P4 TB 1680 MM 255 449413075 625 449412450 449412461
    0x80f040305070b030108060703110904111903060f0b0408070e190c21020c0a24 36
    0x20b07140c064603d81c0c400c1c0101030503403142c0c0c2c0c009001c1500c00d0161650b0300400f900d0441c10242010b051002400f224000d01d00c14410a004480c11910900c0c82c0342074070700311940d000c9100d034a007640d581300f00e90035038005101c100000c0009010b540343c00a1174100f26180b4040e9034540d5079070416104030092400480c00c0445003011400d021465204080e004040d480241c045000c0401c190001e040744100d05c00340c0c01a4120341d0030003000c1590348a0000140320515800708001c3d4486001004850 = true := by decide +kernel

theorem S212 : BRFrame.sub P3 P4 TB 1680 MM 255 449413700 625 449413075 449413079
    0x30103030315031e060e1b042a09031b0f05060313060c0513050d0f080f04030507 37
    0x512440c4d0703c1c20600910300030041c0c1d19440e5561400d58010705903107034a018210000d14242e4010307100000c13146008121900b554010740c1e035000d00d900c034040103103044079400311102c01540c0c020017400c0f040c040221140346500126100e40154480750342c4051020349080300085801070070028100f4040c1060362298421104900901800b1402c00609d032120f00d00d03200c004800502e4109c03604d10070071626480d00400c40c07020300401402c00701c0014000c141c1280340c50944019580190450309155 = true := by decide +kernel

theorem S213 : BRFrame.sub P3 P4 TB 1680 MM 255 449414325 625 449413700 449413733
    0x50c0d080d05090c010201050907120f03110a060207060f061409072006090c01090b03010303031503 45
    0x1000003000319035803101b41c000380415503544030455540c24240c82142071282d10758820b00040740030013410f40c800500a24014401000e03c1c080c091605201140c100c500c25400034200c414486584240071104c842540b0600940d4a03194614056040c0006440c3c0320342108008545807034020003060049a1500001c8909400c0c80500e1540b143c000301c55040b40c42c090211042030645c4a000340001703030740388040c0041c00d40c1d09680b021001040d82c0c3d0170b2200c004c40b00d42000b10200d5001441a00c0d2071 = true := by decide +kernel

theorem S214 : BRFrame.sub P3 P4 TB 1680 MM 255 449414950 625 449414325 449414341
    0x70b090d060f14010b1c060e071b0c08060403080604290d02130f0e0604050c0d080d05 39
    0x8004294070303200c41d291140e5581000c00c6ca40c410031625041108020b50814001c0c08081840100c200c602400582c10240444141c0c005100c1c001807501c03207926644544c000c0d14190000b5a1040103e01e5510707240c41250109810700d580c250110039050b0482a0348103035401d00755401145030100d04056140c1300c285000c02c60300a000041d40e0813001c0c402c08220b41a8800382842980b0a0040200040c0000b880c51960442180e03020540e088928180e01580f10301c000d01a40241000140300c029 = true := by decide +kernel

theorem S215 : BRFrame.sub P3 P4 TB 1680 MM 255 449415575 625 449414950 449414969
    0x140f040f0914160b03040308072304090204060e04140a0f0b0405040309050102070b090d060f1401 44
    0x100f20f03c4103410161000c4400841c072003481108880c00340e0b074155591b00c0141e40d0000b00b00e500300c00803036051190080640c44101921240d40151001d42510100145d0380d40c0b0386030010384106001c203003180c051401d040d41c007090301600d0480d1a9000303451800101e00c50110b141160001e011040d660b1390700c0380c038180500040c5640b0851642c03d5410070380846103400e899650720780c410702a4005040c0d100703101c45210000546034ac0c12209001c2c106010118108135a568180e0dc07408098002c04c116 = true := by decide +kernel

theorem S216 : BRFrame.sub P3 P4 TB 1680 MM 255 449416200 625 449415575 449415583
    0x50705100c05120a050f030406021c0c02011407050d0f0e0708030310140f040f0914 38
    0x654003850043e1030f02503c1000e0302c0c0a034000340511180e49900c0011500b040181d1401c00307460743c680b410054020310500040002c2100e040c1c020001501954120ba0101c0c00d59030002c1118090b802c04c010007542d0129860f00008034100316008004290342e100c0b4110f00c052200c001440040110b000c1c1c6040e60b590050925540040108040640d00e12003400c060002042e94000c00448480401d50300c91411004034421a02d6005409003201c0c15407118151940001c0b6021080700744594032621 = true := by decide +kernel

theorem S217 : BRFrame.sub P3 P4 TB 1680 MM 255 449416825 625 449416200 449416217
    0xa060b01030f14060102060907150e1302181e0105040317040e0a0f0f050708040f05070510 41
    0x130310002d07403e031000d944411405c50307070ba240d40380244202491242c801420340c80c09400301000c0f0150180c04205003000011658040380c00c601c5980c10742002080c040961890155064040e115081c0c180684101a502c0001c005004502005151f8100c1006058880801600355002415841d844a94502d00040184080c00425070003007030081c148a0400c04600503406403030311401d01503881401e1565070b0380703959800c1d8000e401c0a0755980140705000c501a01c4001c48080c1102003600c42030030 = true := by decide +kernel

theorem S218 : BRFrame.sub P3 P4 TB 1680 MM 255 449417450 625 449416825 449416831
    0xc0609030516080d0302090d02180702010f02030f22080307120501090c020a060b01030f14 41
    0x5005050280031452507104039500910b40c034103074080d5103842081204c0d106141e80400d1007489510703001d010200d0301d54018412903445c03210035003600502500391980d000540c40c00c4169540e01601c1e10869004801d2040f90040540d00e5804001040d888803070500c03500c00c03c10103c2d40006140902031405422035891303025030190700c1c8101101300c0b40141d0044041504003003030036141030b40101d41c00000b51b420040c08948411800b0058010b001a000c8540070240303024405251807e5003402940 = true := by decide +kernel

theorem S219 : BRFrame.sub P3 P4 TB 1680 MM 255 449418075 625 449417450 449417453
    0x7060b04021c06080102180405070e121e19020d0302121605061003021c03020a0c060903 40
    0x811410070f030380062603e8040c0709039009045c0500e464140d03440b5000c2000b000340001404441441050104106151110044180c0126124004000000c0c0700022500c4901c0c0c1c5210742a03580e404500011400640110f0880d01240c0c10364019020066a01e006e07030409114001d0811039041c00304151995032680000341000e20f02600c2a21065102c000700342428000d98000130790030982510080300d800c00d6559140c03050034007a20607102c021100380e68840285c031040e070040000a010402c140b0 = true := by decide +kernel

theorem S220 : BRFrame.sub P3 P4 TB 1680 MM 255 449418700 625 449418075 449418127
    0x7030c030f110d0c051509060a080a021c06030c091e0917030f0906010501110d0507060b0402 42
    0x49010b05074880340030401d02000800c0032540c03024142e03840040c09250114082d50b4000d0bd050080c4241000c000780306604045085003c00e281d002700c0c050300d00ca42460341c41c0036074501c040c20682d00b406001801e40c090b50080c00801900c0b96203e80310740c0f800b50303002c0341d50140080c2c8040c03110f52064409110009421080000d600d1040141c1c9004004c01c1ca003203101110400b030480d0715510381c680104100308000540d0740502c203107908082c242c0540280b00319919030030129207980031281700584072 = true := by decide +kernel

theorem S221 : BRFrame.sub P3 P4 TB 1680 MM 255 449419325 625 449418700 449418709
    0xf06090c0a0503010207110114090a24090303080403030c030f0509010f050907030c030f110d0c05 44
    0x1d038980c68405140c200d0244200c02040c408a480c000c004560050340c103803400d04014042246072604e907501080d5079481a5201c40b0780c880c040703882810400c5102d444941200454603040f45d10601e5602c000f40707882d5014001809150780d4080191a8600ca900004c8124800040500150030030868241c0200042610f0040140ca0040441c0700a000131490204507504003c4441000f41962502d0004000303010048030b0030840e0620400c41a201d0f03c0c00422954010b19514441525190600 = true := by decide +kernel

theorem S222 : BRFrame.sub P3 P4 TB 1680 MM 255 449419950 625 449419325 449419339
    0x40f05010e0f0903030121060e061609080c060715060605092e0507050f06090c 36
    0x40c1c011180450044851030b00759100f6903070344414050010429209890500440c1801502c960b809501c44400c0c0701c421103440d2125502d80b011544185503009040c202d101ca98007940000e01614007400160030940034a405100f40790b40704040407035201c84a8185160403001d1b61003070b20042c00175a50741540e90181d410400545a00385580e0304640301c000c4456980c182100101c1c0368a61005041c030703549070200e909100e41007040c0003414420394003070f000c10400d5031100440c1c0000d10070340c122502c1d = true := by decide +kernel

theorem S223 : BRFrame.sub P3 P4 TB 1680 MM 255 449420575 625 449419950 449419979
    0x60b0d2301050a0b060403110303040e010e090708010902061b010b030f01020d0b190e1302040f0501 45
    0x4000d01d0310703402a0f90140101405c4603003006d0841d41c0f9607012640218045405220500000503c0704603201c2c030341e0082600d8400d01a1900340242000e04115868201c40f81980c10250741800507250070381200e1115500241480713460f190641264003400710907608aa140c0b00e2407003000c0b03403001d040d03009100081098400304001c0901c0018010310007210059010112441e503010080d20101c0c0d99903a134414420460260860b00540c006011a02c00e164940c0c84103035220300600400b240d49101 = true := by decide +kernel

theorem S224 : BRFrame.sub P3 P4 TB 1680 MM 255 449421200 625 449420575 449420581
    0x1503050601260f01050f06090f030a05030a08010f0611030313080c3009010c060b0d230105 41
    0x80c8101b858840042803a21400180d4000800031601800740c65088404039003869138503078014155000c0018200c0e0300c1c035007100407203040743c0c1496810002d0341c1d0b0320203048070400e010b080c0c88003103a0400c2020a86014141020341e440c140200c45030351030316a44198162074422a20094494600c01d41d5540031a0100e14040709404416805030903d08426500000d140c1c030301c0c403000204059035607183c0204507143c0700c0591103c40d5210824109100b49061034080c0501046221038041d0700304400 = true := by decide +kernel

theorem S225 : BRFrame.sub P3 P4 TB 1680 MM 255 449421825 625 449421200 449421209
    0x90901090516020a0b0109050705040905040c150507110f01022107030f091503050601260f01 42
    0xc076a24058130f1030180607403070300200501c41a405600b00741d90003074950030264505581d0381c206c54101d4070222001c0c0c0320022001d00034000781040c03154042e03a14490349801c030b0401c4516210032200c0f040069045200f0004060309000c56402407155519084503002020340c2c0d030365105070081d010790040c07004600240c0504d201031080750150104506950a044080c2c4140c114003800f9070050401030003a60600c0503250280d4030301c04020075201c0e10414145581225800d0000307407131151a0040c0c01 = true := by decide +kernel

theorem S226 : BRFrame.sub P3 P4 TB 1680 MM 255 449422450 625 449421825 449421827
    0xd1d01060305030a1805060d0203091009120f021213180c021011090901090516 36
    0xc0c4485419615407980d248603203400701080000300c503010b6158003c0c03004048060040104820f56500f8441b004601a400950700c409141c051800f00b161415821f11034540041d03444a82c00c0014507001c082641c0c2d0315044a420f10039401240f0a40441820403001001c0c051008141a1111401e00c64169101c0030349002c0103410900c0c0004031a150b6800040b203c08410350494041038900f4401d6040409003d04a40c82c0e0b040844080086044e502c0f82d0012031240380c003e0209200920307103500c = true := by decide +kernel

theorem S227 : BRFrame.sub P3 P4 TB 1680 MM 255 449423075 625 449422450 449422453
    0x270a0b07030507292a030903211306090c0308040f170a0b0103110a0b0d1d 34
    0x15103000300c0141d8401d9000c1d841c1d17948025017142440c1c11076030780d02d9191004090002030240044d8090742c1d100000396580c4480d6882584c5032018202113105810307942d010025003d01c28124812020b83c0102c001030704050078a014802d42c0055040076045078004030f000318004d414010340e0801d4400c440481d80800b59558002075658900180042c017061000c0700420001d0400320840c450101c0081958500c05c3d00c41014181d1600004580d2001c2a1a21503004000340108100e1005100c20380 = true := by decide +kernel

theorem S228 : BRFrame.sub P3 P4 TB 1680 MM 255 449423700 625 449423075 449423123
    0xf0417040305060a050403090e090124031112160314060a02270a0b07030507 35
    0x1007000802c02c00199550000701407440060107031524a81035410a82c00c1e0300509200002c1420099080010f60111455818585210f140e0840302401c603489004140001820030074a1580c2c4c403032908200888000c0e0054003001c032104820480000c5180000035441101c40c04007242048a0003201480304c55080703044680254102511200d01080c820b01c080b252481124040095041c95691302a02c0b10007803640c0041140c0d140c08606008220ba40f01440589540100765400201800b50030 = true := by decide +kernel

theorem S229 : BRFrame.sub P3 P4 TB 1680 MM 255 449424325 625 449423700 449423707
    0xe28051009021c061d012903030307050f07050706020307021305040203070b18030102030f0417 43
    0x10300035406000200d060381052003003502c611003c0e0040c880080d1280009420000d1815084001c1225942d50180c0194210107240381551007501203185080e0f80e403003000071031b1b0b0341d00c4064950030074000003144410407075242c2c104071840c0310f90000603119101c0d030310800a5075036040880203d01c6545081445402a0720911801d48034640040040a0a901c0d04080d820140d114030511507c480b41c2c604800d403162001d0000f14000d0203500071140032454170b400c19aa003004001c0c00850f80f80c5040 = true := by decide +kernel

theorem S230 : BRFrame.sub P3 P4 TB 1680 MM 255 449424950 625 449424325 449424341
    0x31103060417030421020705010201060f060e060c2b031d07090e280510 33
    0x8540c0d120003045014000314a41c0000300244c04c1180b00c0000d4020581048090480300c140760500a6480d00d19004150256180075408145443c0071015801120040e540b0903c0e4403180505100c640c0c0c105200980301807080a02c0f601c80c0044d08026180c500d800000c01c44412416910020143c90742002d40511021100d0419006c0080114400c4266602802d012803c5c0201c0c040083c41c140b03400401c69111000540c0c0002402c0c119800300311480e000d03600721843d100d0f1549102c0304450b449 = true := by decide +kernel

theorem S231 : BRFrame.sub P3 P4 TB 1680 MM 255 449425575 625 449424950 449424953
    0x110a05130608160c02010e19030203120a02030712300b3f07030503040311030604 37
    0x4441c000703082c54102070913900c41481c4d05040c0d040060000100505132108400c503003401c40c1c00301d50980300d02c0c5540f04040c64810304240000c80c000060200009042d000001c0d00d25207544250200d401c60902c3c00c080ba186035050903116000c22000d800135004940c80c401038940e010b00000b05008000b08081840b05800130074800744006641c40f6a0300621803064800d0014419413940959244406140054540096a0026079450f00005420030811000340480c61000e03005902401c0c0741d1515 = true := by decide +kernel

theorem S232 : BRFrame.sub P3 P4 TB 1680 MM 255 449426200 625 449425575 449425591
    0x615030708150f030f060f07140a0f030207051006030501180809040906110a05130608 39
    0x1000656114060802901080201000254401041d41c00f859414030a40c60088100900828164060740e61002d03601d03e95101d00500317503003001842c03101c40824007060240f9012244901d4800703240c2e40980c18010324020007511240e00b40020724800843c80c0e80c86100800404c003091041c20191003c8103038049004000c1d9030381020900c201c61480c0d104c0c030b40350000c0c4424048180d00c450074140c10910000d5480c1c2c80b0110107000d6400c44c1e070b040b252000c10500d00017055030140f03040c14400c00368 = true := by decide +kernel

theorem S233 : BRFrame.sub P3 P4 TB 1680 MM 255 449426825 625 449426200 449426207
    0x507081006230c0f071d040b010b0c030c0f0c10020105190e0307061406150307 36
    0x4454003105402c181a00700c1e20700300c2000c00c1d86003006400d4469501d040301e0641d02d6a444c1e00000300074040c40c0312205400000c400c04001112181c00e241e180c0101076007043c0030303001e1100c1000903208122441007045070f455861500c2121010003403000d54549500c2d60405041c494262014000c0f00c03144140510342c001e641d2512603078036140a401d6170074018103004018684c180411f04c0f0140c0403551500c00d04208044146c080c4006145c4101009200c005282c1201280d690034001d00958660 = true := by decide +kernel

theorem S234 : BRFrame.sub P3 P4 TB 1680 MM 255 449427450 625 449426825 449426837
    0x12070c05071401050a050c0106050d0b090c0d02060306060304170315190605041502011e0507081006 45
    0x17030300c02081c24448082000d20000c5001e402c081d01412019003400318a40c2030313003010f01d440c0005507400a0903000e281d00c004035506103400103101154018007070030324586951040c07050f550720080007030345e4400c1c20248084500c20401d00842c06103a201c03509140349120034040210308404128507002682d0550810410250848190b074219030024420202c842e2001000340d014184801c05640d040d03081d4400300b94040890380c0014041c0c9513075542c0ca07040d595000d844524882144c0501004564 = true := by decide +kernel

theorem S235 : BRFrame.sub P3 P4 TB 1680 MM 255 449428075 625 449427450 449427457
    0xc0e1810080109030203250f05010e16080c040b210a120c2612070c0507140105 36
    0xb0010002a0030159440685005c0441141d1a01040948484001c9527001d40004210703000341861603403410039a92181003007040c2c1030008010702100801c0b1030102290480b008100f8810b1103000540c100ca1404102d03042010159004100d03082c001504002544500d00d5820074540030b80080c3c55031140500c000d421840c0e0880c035400c401c0c2c1007000d066030003408502903e007840120074040c0c05204007114204007040e040d040c000280300081041d20010443c1814a291007103201c0b0000b0010302 = true := by decide +kernel

theorem S236 : BRFrame.sub P3 P4 TB 1680 MM 255 449428700 625 449428075 449428087
    0x90806011a071707060f060503060633070606090e0a0c05040c0e1810080109030203 38
    0x400e440c0c0d640e80d035116801d2001c0d680f4000060140880400220f440c1003118a07805401c600c1c0c00048100f1001e41ca40081680314141074a541d507208015011003030760000e9010011082c0c81c00e092101c680c0d040f90b50800c1585402010381500d04607501c840c01c1082d0412801768500c09030082001d07021940050340c0701010320f8118041c46000d81e80d05c005200c00359008112650300f611000300f98060021540c1c21039180030500716048060b000342910b000610000501403000500d1303068000c0d609101c = true := by decide +kernel

theorem S237 : BRFrame.sub P3 P4 TB 1680 MM 255 449429325 625 449428700 449428739
    0x509060312030702011803110c090910020d06030516051e010c110102190c0609080601 39
    0x31007100210741010051000041c41d240c102414031102800600403000106240f803001440502000600c0c541c243c2295180a603081c0300005030303030701d122a01c3c1c00382210750040303541c5504100c16032260005503005410303118030040c030a00d9504280000d000d0741d44294152000786146522903000d42e40c2c8100180c442881610660320345c02c83c00600540c1d454110b101c3c0c02886e810302851858502001440751040b4200b26061403006414511507030080e000035401440100314007150f144105c040358 = true := by decide +kernel

theorem S238 : BRFrame.sub P3 P4 TB 1680 MM 255 449429950 625 449429325 449429353
    0x4050c091b031e0103050d030e0c0f060904020f190201150501080a0b0a090216020a05090603 42
    0x110080082019085003400400d01c5202d10207403c0d41c1940c50341846078458604050001c04645000740c91400c00700d0100b240c4681c114002c18003160160b800c0c3c00d100483c1e00880301c4030350003075082000d02e490510040160005030781506505101c0d640c1c2e240f000c2e017141e072039010038040412031005c20070090ba4440041c543c031010305003000ca205201d4001007240144103400007000b00b030000c190031014160004081781c2640c000c50b040e1040a40c0d0707400748540700c2c2c01a40e0080e0150000c43d1412001c0c = true := by decide +kernel

theorem S239 : BRFrame.sub P3 P4 TB 1680 MM 255 449430575 625 449429950 449430001
    0x702010503040f051b0301050901270602190801050102010f0e030901181d04050c09 38
    0x2400240080c3d5a480b4549080c10026600308400c941031961488036444a005e648101421540000c0c0040c59a90504102e50004000e06803113060340664040001c83c40007290511000a002d21440d1000c48800c550b0302c2000303507400c203110f18100d030026030092215080c207140e810140c5d00884500c031502d07070062103254090740c010000382100c603060114220b44070b941d0b2842c8024149002e140603070701106890070700051041c180003074880c051013620398060500309a089684d40120542101c2c000 = true := by decide +kernel

theorem S240 : BRFrame.sub P3 P4 TB 1680 MM 255 449431200 625 449430575 449430577
    0x9130f021c0f0501020a020c1c0f031709072d150c08030a0605100c050307020105 37
    0xe0600c01c15400d14628400140c011680e07410031109225040d0020941501b4550981d40c1826460080000d901f035100624940c140d000040707a400100701111039517100c2d0185c00e1525102d8081ca50b40c0c110701100700c0d84250241c00c00c0c04204060519a07183c0d0183e2214580740c0b5010500402e88555100114800c1c80f460150702454008014015034500c445a9005200e441c3d0303030b28040c00c408016028511945001c3ca00443c0420a410710800c00021421740c030034081c6142ca81203800454503 = true := by decide +kernel

theorem S241 : BRFrame.sub P3 P4 TB 1680 MM 255 449431825 625 449431200 449431219
    0x1203050d02072a090b03032d1201060e031c0801092d02040509130f02 32
    0x514000c91800f1007124100c0210482188a90074026540401c1034003480860200d10030321082c0e58045c1c0041d464241c1d0001d440c40710341944003e0038081c2041e0180040c00d41c040c42e05031401d00030011403542d5156190706000e42000305011100d4020701c0341614041c0001d40d84003c980043d10705480b035414617428152014082e03c03460348845010300510408207610b46c0a05101048882480801600c0c4c0741400d0801c80c07425005080035100d0740d030728a0310b80089030352021041c03d8254111480b10700d = true := by decide +kernel

theorem S242 : BRFrame.sub P3 P4 TB 1680 MM 255 449432450 625 449431825 449431837
    0x18050610050304170405031005010f050a1503020c070b0703030506030d080613180204050403181203050d02 48
    0x144e10301c480565001c1c01018085501240114111070005d040030700503c0321003d544a0005020718040914405449c40030900b540c5002c0c0080c0d050b0080d400c03000c02212140191480800c0380d40c1c085000c0e10045011342d42c00b0a080c2400c41c18503080000c0000c43e43d081180040400c004c507241c6018421001088040000341910728400359007200c01007500c002d6105081c0345c113110074560310150041c03c0f58250a15412466078410100c1c134610007907800200895010f0140240104166000e001 = true := by decide +kernel

theorem S243 : BRFrame.sub P3 P4 TB 1680 MM 255 449433075 625 449432450 449432483
    0x302030f04020906150c07050f03120405060711060711043207050f0418050610050304 39
    0x4210348521003103030030f002c00014109035041b450060004500f46001c1c002c144e80014000d03806603000c0030442410403c81001c1d102036441c01c1d2001629045a4107024010b4940d00c03071201e421010004000050102c00c00071203043e9001900c061003050213401100700204050500c0c0030702201c0594503800d00b0a505074945400900500d0024102a40c50f00280002e07841980100700c00940308050907030131140740c003d40d9800310040340d1040040300041c0d40500b40b440018801003031091140706882 = true := by decide +kernel

theorem S244 : BRFrame.sub P3 P4 TB 1680 MM 255 449433700 625 449433075 449433079
    0x105190210020301030506040b0c07120f020a062408010e0a0f0f080313120302030f04020906 42
    0x9070001015072240070a00210000041010004081e4022880b504d0f0012056565408000e030a000704070025000300300551220b00010b020303030301c404d90490851040d988030440c00d848035000d90b0030b5041070301841051881e0310144d1a0701400c81801a00242c0004e1018503001c914065a03103400307100151040710a17820880401068010302c54865a00c00412510780c646000002d1032101c0ea000c090b20300d10300a0b901d980c007030b038403e100f2244100d11124000d00c0380e880b0740d002e0050442d0000e05030780d = true := by decide +kernel

theorem S245 : BRFrame.sub P3 P4 TB 1680 MM 255 449434325 625 449433700 449433703
    0x2503020906040510080906010e160e03100c0e0a0b040812210412030f0501030201051902 40
    0x204054807000007404c481003e1031000000303580c0c0320401031500c1d01000070a004104c1080b1400c402d0915820300310746c02c000c10180ea0140710064100700b2103900c0800494229608072101088018441c1e04000c00c0320850721600d070310800bc604400305107405803401702c034100d448a0004000f00c02d03000200039402d41000c00100014a4107403000c1d104440f9140c041032103076103c0d2041081f03401d65144058201c0764016440c0c0380e07a516100050006036004411140310f0001841c08620840140004a = true := by decide +kernel

theorem S246 : BRFrame.sub P3 P4 TB 1680 MM 255 449434950 625 449434325 449434327
    0x6020d0908100f09150911043b0f0106030c09060f090209030321040b2503020906 37
    0x404881d00500e1500b840500405c0c1c6000510012405a807070b4009a40b00c4003e50801c0c4c01140306181c1c003603001c40e1a070748040304039900240e1410b5411801440148204055a0040002c10300100d400f500000300180b1f1494041d0403100d1940c00800143c1c01c200081083c8100c1840107801c6800002000d41e82d8800000001e095118a14011074440101004050448061100548541e01c1941c82240039110145552144035400b0920078003805444411103026100b6000740c145240080e22107 = true := by decide +kernel

theorem S247 : BRFrame.sub P3 P4 TB 1680 MM 255 449435575 625 449434950 449434961
    0xe06061203130e190606120f0c0c080318070305010b0108070f08011a040504051006020d0908100f 44
    0x2484c254002e0040c640601031075191041e014001e5821030f4116030040001c0d40350b0780d1401031001d62580c0c2c0440918142078100720f1054480d140c281c2d24070303007001d01204605210320460800004100040d004281809400d0f22818815036a46105a4001001c14400000184890014844464244a042c0f500070341c5c09415802e0a40302d40c0072400300e40c8243c984c5c0e21011101c10007001901d81c10440344028114900d0700e6910180313003150f820b50703e01366a00d0a200c002d032500144504501c0b158002e = true := by decide +kernel

theorem S248 : BRFrame.sub P3 P4 TB 1680 MM 255 449436200 625 449435575 449435611
    0xe0f06010611070b0a0306081b03060a0f06030c090c0f0903030f08090f010e06061203130e 41
    0x10030044070009585c82c490741d40b590096080d20010f10580f00040e08c42d05401c0e2822400003c415071503003000000c114802d0741c6500240750314640c034402141741e607a6074652031045031455122101c16900c414140d003c07268030540c904803031021420180306080c29518000c021074044010f903010300001c2004203840200c100480079280e03035080000d00450700480700c00c030344524080d034010703005485c0c42e00b080c0351240300401614564400c16015041080c906100c8410f02200035100d4049031581c1019 = true := by decide +kernel

theorem S249 : BRFrame.sub P3 P4 TB 1680 MM 255 449436825 625 449436200 449436209
    0x3060906020712051308030c0c01030b031c0906020c030309100c050c04020f0d0e0f0601061107 43
    0x1051002e03ca4502000020310045202050602000101c200a0510400443c5000000014641c64014900005060603a07407401c04140e0340701800842424812082e01241c5e054100744042d12111b00d038043d0b040180b2800b104140d26080000482e660300c031004048400d11040c1c25001c031400d1030102400c441501503810484615103950010789030040001030302035140c100902049080360a201610040c0342d10840301003148207800b00d01541502c030342d458440041600d0080003072508171140d00 = true := by decide +kernel

theorem S250 : BRFrame.sub P3 P4 TB 1680 MM 255 449437450 625 449436825 449436833
    0x15060d02090904050f0c041116030309020d08090f060a050703030f0608012307090b04030609060207 45
    0x502c0e610382014a0719607914028141040ca40d8064081c0043c0285802c2c41494050415400c046241461411141242d54440107084040c1951096500c1c09a1640310818031050300c50744180e596001200c0c00c010041c0c68454a1510842040000b1509698400140c500140e418100415683d1490140d070000e8942500103000b550700c0d2001d0340c04101c504084140c02008005180e82c0325480395042181d05409034000c1d201060b0080004000044640e0700103015503001d0000107007407c1780c40e50703 = true := by decide +kernel

theorem S251 : BRFrame.sub P3 P4 TB 1680 MM 255 449438075 625 449437450 449437459
    0x30304080c0f010501030602090f27060607080d0b0907110d0806030a020607140c0915060d0209 43
    0x204c80c021402074a0050f11450384005020207216910361561150780b000e2420b1a5a40d0942a41c24010840002c1d0b90225514103010072224403880001810610340820700900c00700b01e03a0400c42c007000099030040419162600190b82c0300c55101400542500802016a66148903a80c00f9900c800d005048031541c40c101c4d000300d2078a5000b004180c1e03040c0d100038002481c69104111140c42e00701e003524652280e141c44145034248030480000c1300d10035080092545441280e075010340303800900040 = true := by decide +kernel

theorem S252 : BRFrame.sub P3 P4 TB 1680 MM 255 449438700 625 449438075 449438081
    0xb090105070c0e0c041a13031401110406050703030c03060501020c0f0a0e04060c08010611030304080c0f01 48
    0x3000000360455004205513910340d4402e105106d090142c4880901605460078628064042c06101140b044061428000007460010502c103801d428088241d40150b88050086103000c90b083c410180c2501442c1d11103542445c042000b1881d1000017541d50100c2500c4e00d00070f42d0322416550300360f219254400d0190500034540714880c00e01e480c24200500c0c0307441110340003490303440001c144c151091180c95844002d010045007181c03155202c1c2c4980380c2c8011590101d920500c201e500c5031f41400c0c0 = true := by decide +kernel

theorem S253 : BRFrame.sub P3 P4 TB 1680 MM 255 449439325 625 449438700 449438729
    0x91d0601030b36090a141002040801140f060a051c050708070609080102040b090105070c 40
    0x2145128085100c0d4500c0020118072020080120700d8190740003c0f40380c6080411340d81c07101194010800003600c180200400400c02040b5210107031a5402d54403603484030b41c81c0f4000c00050810f6103800403100d02103521254102e04090044502409490100f4204001c1c04400400d0005145901d244030075144d005c030b50240b0510029004030400740c65441c0c64100000c0510386180c10028030380e44104030400070380e80d814007100c40740a030a0034800e0311107000f0b0402403201651030703101c0c400120004 = true := by decide +kernel

theorem S254 : BRFrame.sub P3 P4 TB 1680 MM 255 449439950 625 449439325 449439349
    0x31f0c09030605100e010b1c020f07050f0601090501060201020906030c0c0a05070e0a0b01091d0601030b 47
    0x94644c41075000c3c4150b03a20314521038000700f2060454420745000080c0010b4804ca640c601c200d09001039009859404c0e418441801450b0108504000b0002c20741c1d4180c0261000754100403844041d00e42c140c000c1c80a5a0042155880d95124141200c1c0e000c010700c62025204c03160340a2441c14455034840c0a005403046850106540100004850003091291010008920f5036401500c0c0c0e07414901c01c014000400142e894100c4d80079401c01980420149030002d80b9048140008080c400e2107 = true := by decide +kernel

theorem S255 : BRFrame.sub P3 P4 TB 1680 MM 255 449440575 625 449439950 449439961
    0x20f06070f02130b09010e0126030c010e061b070206030117030c0d0305040c05031f0c09030605 43
    0xe10046120b2801310188914040e046e0420381200d0707511030041c00000307500e400028030076040126101e102c0c4044400c3c0c90852282480c040490b508020758040211000504140614180c604051003000b0070540466140103900000313520100800040100b8141c0445d084a148840c1d01a41d1400e0480102c0078a86400d40246030302007903c450400081c4000140e104000b00b80a4000d03250300703412402401d07410059aa00b100030700d41e888003100c64251060b9000d02c0a50b910200c1000281003c = true := by decide +kernel

theorem S256 : BRFrame.sub P3 P4 TB 1680 MM 255 449441200 625 449440575 449440609
    0xc01050d1119181202060904060902040b07411204061e0903020f06070f02 34
    0x40e0164604070040d9229261802c2a1030250100fa01c1e9120b408540505000d502001d410140c004144000d80a000400e0316640c8540d203030120703405548050107500011036031808206103d0005001100107510b0744020051382403c0f140d44a02001e140d400d00b5501000001d80750f4018044004410740001d2465241e907a1003602425032422800b00401e01c8103131200441c422030103080c6900c15070760050241140041108240301040d48414001d5032201c801140f0600103030740e0081131101d22546 = true := by decide +kernel

theorem S257 : BRFrame.sub P3 P4 TB 1680 MM 255 449441825 625 449441200 449441227
    0x616060b010206130305032413050a0506060705070e070c0f12030c110c01050d11 37
    0x28006440c800e5806000d269000030f544030954607004503d840140141c8400303080d50f0900200a00d04030410488034034001c11021005010300f40512035041c00001515040d511f0040d00c0d840c04000c0785642c50644119074280c2d9020000c0d1941c44e00d0b1403003850b0b03031000041035002440002c6d050940014140082c0084181c4125030071290040d408900408481494034000c0c140296000c3d0141d000200180c450040842443c0240e9160b1181e0441030252840e0b00c1407202c155004120b00600001 = true := by decide +kernel

theorem S258 : BRFrame.sub P3 P4 TB 1680 MM 255 449442450 625 449441825 449441831
    0x9100c120c03080f090606121504150b0102070803070305030604061203021e0d020a06020306061606 45
    0x3001c400303502140c0c0b02d4001c6650910204501c611400c003c80c05054181c8440c810410b901920380c0100690b071141980011204005004450140d03200384035100e1100c25040080027591a400403190542d000884100800c11012040310105c07541860816560380d141400900240b04c0303904100c9503502601b441608050300018507039030110802d10351220400b18016440d079500002c1c184034005030401200da03400940e26401840d0441c800405042c10b1107a440280a40607408690541714180c07 = true := by decide +kernel

theorem S259 : BRFrame.sub P3 P4 TB 1680 MM 255 449443075 625 449442450 449442467
    0x20a0b10030507230a031110030f0c020109350c010212040c09060e010b09100c12 37
    0x3141030349038121002c3c5031428801d0b1101c1740c040010401c407040c0c28114110031a00445460650703042070b030040650786c264a1100341007682400c2800d4040d4440d0501c240945400d190b01008400f031144080e958400d21b82c0b44484825241c3d60007a134040261550740021000145000518540002072071411282128180c0100c00c081c400d40409009030001040401309284840d410a11070007554062001024041e03048201212521403003122103c0b2980c0c2c0002411050000c9054018a0801c = true := by decide +kernel

theorem S260 : BRFrame.sub P3 P4 TB 1680 MM 255 449443700 625 449443075 449443109
    0x9030307081e0916091a06031008060408070b07081e0403110d09050f090601020a0b10030507 42
    0x3c180c03500c0450303075100c0c8410411100b102c0201c00741c0c0c5a00a4031b00a0380c5c1050405550b01c040c480310b04010090341c0d880c00c0d50030101c2c01c44080310200c00c001032820400c00580c5850b0b8020685190003000c0e850a00d03400315132a00007506803078100d2164030000f81013612424040540a07004c805441e40038014400262044070140241c0f407203040c4020000c9164202480e40701d201d802c059008010319421a10b87c603001400107000c95559400c18040440401c0b070030000c81004080709100c11070000 = true := by decide +kernel

theorem S261 : BRFrame.sub P3 P4 TB 1680 MM 255 449444325 625 449443700 449443723
    0x1d031305010212070201051e090a0e420109080d090f09020309030307081e09 35
    0xe0100040143c58503070404850a1a201c0c2c0c00281c5140902c3e0b41c254000c0c600e41001c00494040030b01260000c8034002c2000103c1ca484804001d0100000c403100c803080440011122030500d9444000c012084000305452000305a00c0d546a031100060060716040c031482c12008944100b06003c4201881c0da1503682d0380285180c25a0011a481590b0200c000e192042090045204010007240c0c0d0100c60b90070100050703250780e40040c040d00c84a08240a88582000a0041e2048040b41c119a6030 = true := by decide +kernel

theorem S262 : BRFrame.sub P3 P4 TB 1680 MM 255 449444950 625 449444325 449444327
    0x50f0325090608010b0d261c0f05060a030b06040b0a030b0103060c05070c06031d03130501 41
    0x2e2400c40001480c9106008490440d1801084d04120111581d10000c1a51158000f1100c00e096942d00c1203418003100010042400c0f4150304103014506201404140c443c124880e144403070600c8240442d5449281e01c0390142c0760b010440b542035550341001701e0700410064080e10340c400007010000090004018120341030380d001300e80501140f502c0c0131054400e4030074400d00070000c10380135200b000303803901c290b005c802c0035101510703040071603042405035a00d1030704100c091001a1603da202000b042d = true := by decide +kernel

theorem S263 : BRFrame.sub P3 P4 TB 1680 MM 255 449445575 625 449444950 449444969
    0xc0308011505030c0a021204030b0105121b011b17030412030c050301050f0325 36
    0x141c12580759040100304070092254031a060b030794042400440305035541d500303010503864120142c0144003803000006010081000740c2000d1341c125207096500c0d480048030300f10300e25160010001d80e0106815200e103d00038a41c03045010021031030b0900129894109030b03031100c07801c10407075036001080800004140803c201e560802e20110f040700d858104044801810014124801841102e105020112491900c2c0da014807900b0400f0340007400c0d0300c05020140045003149010743c07243c40b201 = true := by decide +kernel

theorem S264 : BRFrame.sub P3 P4 TB 1680 MM 255 449446200 625 449445575 449445587
    0x140c04110408070e01060912170a05090906120703080f0c0f0601080c0105030c03060418080a0c03 44
    0x210b0300c070014131407600c3c1c081c024000464502c2404210440034a00c003030110500c1281d21403002c121038644030390f40c0e070400e100c1200071032404510103c1a05058005035030142c012203108100d200ca0154182d140c405900002d0300b41c0e40300080380060301c83d1607400c80b540c218004003128010902c14110a480d40c1080c0256841c0d4000c0b101c951003d0361145c0300752030081405411291440d10f8680030000209043e810082c19501d0000d8a440070500313560181110300119120008044400d01d4021b1030 = true := by decide +kernel

theorem S265 : BRFrame.sub P3 P4 TB 1680 MM 255 449446825 625 449446200 449446213
    0x2070b010e0708091501030305031008060a1a0f0a090e0309100309060b1c140c04110408 40
    0x1e02d40360014081062000c8000210000c11f110003001d024001c8045002e14044c4407448020304405030844440b881d242d21a20083e003c02c42d0000b5920005141880050a2101100400ba10302900001d14039241040b13072070003414104043c070214001403201c1107140d03131025200d00701c52166a5004c03c604806040043c225060864014850001a2068036005c8118186620515084072414103070b02110740055042c016101c0c0c2240d800781c900400b01c4850440b03140600250b4200c0e80c1201c0300b = true := by decide +kernel

theorem S266 : BRFrame.sub P3 P4 TB 1680 MM 255 449447450 625 449446825 449446831
    0x10b0a0801091a0f0409060504050102033102040b030a080a03060f080c1e0402070b010e0708 42
    0x1c0c4800c0c06000384404010781d120818030083c03014407941c84482e0100b80c2c1d1094131840200c001c01c11a10900b40150b0140e00013503502d00d0400c07001645c40d40b614140d110a0f10000c500352041a002003450000580c0c1103c2c0452541c03034880c00645840011000609911800150940040c1d050380c4900226020540c03100d1040d035039003180300e813244406440caa8100a544400e218643c070f025542452000c0c00800050500c5942c3e201c200024500360402c4600c41040818011041c2c2c02c41d031401c0e8 = true := by decide +kernel

theorem S267 : BRFrame.sub P3 P4 TB 1680 MM 255 449448075 625 449447450 449447459
    0x31b0f0f1909080a0c0b031510020a05010f0c021903020304030206180405062d030f06010b0a0801 44
    0x1258012507440003c149240c5c0c0c500d084440e1050b14550f20745030390900c0d4a1400058110321b800c42d010307144440f5231960004041407000c4c0103c0c000c103d01020141c80800fa034071405a80c000680c00307400108a6800c014203c00202482401103030700d82540c9a012842c19001035081e030180c401e1030920aa0a41854061f46901040031201082c0d011180401c00000b08400040108251810180d80041d610200001a481010b0500722007541d070b5596001a5690301c40c541c140001181d02d400041d = true := by decide +kernel

theorem S268 : BRFrame.sub P3 P4 TB 1680 MM 255 449448700 625 449448075 449448089
    0x60e0105010e0904031218240905070e040f08071115031b0f0f1909 31
    0x1142880740d84030b15044000c000002d40402e011319a0074440041c000000215210409060048203c40c110102d42c1448100b03184d05411080074072014084050030b50401c1320380c0c2d090762210307940c1103103100c0e107000c14800300c0c0003805010319460341407034103600b1403242a95070b5907518014802140751542c0510444101e4401d503070880b00da5040c1d900c11200d01440008594048685c0002c2d50803071044d0249010007008034103007000040000d440036640d0240d080f1040c000d01c0d08043c4c00083c0c00d4000781 = true := by decide +kernel

theorem S269 : BRFrame.sub P3 P4 TB 1680 MM 255 449449325 625 449448700 449448707
    0x50c0715031a0102070308130302060d0510060f05070213060905151f080114031e01060e010501 43
    0x91407004402c0001c0d501d800f00e01c07019001d00e50204d03001c0e035054901c00f40600210b400420710303610780320b070304240e2402880240d40710481807001c8030002a00a020b2111004895240d803216800c0c49295028030078220540c000141c1c02c1c1c1c1d541c0c540030030076903c01d1094600074001085085243c03011441801408410f01c40900b5009540e007236406420f40e44400c1e000e041d650000d02c4070380c0202600e40441e140244030b40072460034190400382c01038051015400f1004540c2141010012640d0342d00054 = true := by decide +kernel

theorem S270 : BRFrame.sub P3 P4 TB 1680 MM 255 449449950 625 449449325 449449361
    0x230405090a050d031a1e130b01080f150d0b01080d0804051c050c071503 33
    0xd981c141e02c84040d00980700401c004802600c040281424a49805002201582d0303e05001d60964a907090b2000b00380c2203210308100c4113050152020042509114200f0303030f980e80c04000c440c3c0c03202e03000e0104d254545a283ca0103070340300c100c41d03151078200c810200704c001031205691190381201d088008962504020950850700c42d0401d54004003150310086018503841c900d071028203840640c0d85041801d214001501070f2504000d5400407800b10001d4000c0070803241d15004240220400c40d90b56 = true := by decide +kernel

theorem S271 : BRFrame.sub P3 P4 TB 1680 MM 255 449450575 625 449449950 449449963
    0x1c11100507020103060f18020c07030506070c0c0608040b0a020c070f090e0f010525020723040509 44
    0x400321b0724460440008410a4147c016030fa40e40c868884e50920714141e0001c0c102d40203200401c81ca60350006a8500d1543c4100101e00c4459207074078080e00c0020381a42e025140002690014014205607402003104070000e0741200c81160f40c3c2c68403080e048049420802409480f8030150304071900c1003152046841c0002c00911291070000307020900c20b8940c10031040380c136100c0c5201c46142c500038040e102c094404c00800c4400750501d02240301c003e910101a050180d4a443c0c00118101c90120f8034 = true := by decide +kernel

theorem S272 : BRFrame.sub P3 P4 TB 1680 MM 255 449451200 625 449450575 449450579
    0x4320d050718020f0d0f0e0303130b0711031602061b0102130509061c11100507020103060f 41
    0xf1301c040505002c0c20055a1007a880941544a00c450200c0c0c4000b0600009003180e00c100c580000e40d214020311031050240c10509103911401c0c2b800c00a2024145011181d0b981c0140240381c03000134900c007a01c1c8219158041510204c00c02c60012010107996081800c0c040e400804210502c458440f400003000d281007101c1a008401c084c0c0780240d00304550300d00c00d07007022030a1030079140c60701c085004a0141d100c00300881c074821041d680301038485803503200040668038a40d010f504100030103d42 = true := by decide +kernel

theorem S273 : BRFrame.sub P3 P4 TB 1680 MM 255 449451825 625 449451200 449451217
    0xf020f010905060a02220b07022d090a18050f0601080304320d05071802 33
    0x2c1e01ea040042c00e20010650004e01d80400c16070000409106001b107000d0241d4907620b1702d03984a60780d84104403d9108095040e60001050351600c5814003029101c05a403410701a45000d101010703030041e1007183d08640364001c10007a000d00582e81d444281c00359008020342103800340601d080c0b038010380100c48141c2040000303203c0304840c11000d40e805181e0700028910f2400200610060b611707540d07051540104452110000d20000041103002d07101c448034150707810703200c10142c030040b071080009 = true := by decide +kernel

theorem S274 : BRFrame.sub P3 P4 TB 1680 MM 255 449452450 625 449451825 449451833
    0x60906060e040c05270d080903010b04050402090601050a02010e300309070b07021309030f020f0109 45
    0x529090041c010481080304845c0c0800f0703551000032594400982d5200401280d07101d1003100540d03600c0740074006050a481408100f980914100310234003005030b49504905501283c01e203400e6482e803102c0343e4200d001d800403c10a8080d4040c4460203c01c8000d08440340504612080c2e640d665805418003040841c40102c0b000d003003c1c1c014250603c42c519040004118150009080d6002d050000c0010401c982210350103c02142c0c01001a0a4068040c0848001a40040003c000924031519 = true := by decide +kernel

theorem S275 : BRFrame.sub P3 P4 TB 1680 MM 255 449453075 625 449452450 449452457
    0x1090318050108011a0a0c0b012705191104090905060114030a11040b01020a06060906060e040c 43
    0x50520483d004005c40e00c030744e03852800316042c00400000074501d03a08030700000799011920000580a40c4034002014000341070048181c202e54049440603040c504041120f1041e800c3c0d0b500c00482d80540803401807a0a40b151030b041c0540300080d00c2155540d01c154010042800c0e04904003200030b600314050301e00082c194440101035115070090500c515135a000040071a1b00030054644050780c0b0030801e2005580d07900107080200168850080441d81210030501c4038902486505112401d589 = true := by decide +kernel

theorem S276 : BRFrame.sub P3 P4 TB 1680 MM 255 449453700 625 449453075 449453099
    0xc0c0a0f031b0f0b0702010302221e0501090e0405010e07270506130b01110109031805010801 42
    0x10611613504154040e14295206050150070489240c0b80b61040402428420450078403810b01000140b00b4210f5142c1c0d05400c451f00910458108000202080f506026042501ca001c001150130454250702c421501e8034603005440b1000c4d21080548008202c6003501120006a10818507840580d4801c56014940040c0710042c85101400c1800c09807400c460114140154000001c034010030078050848218403940c0c0b0800b401c0900d045102c0f811116400031410012140c00500004113425 = true := by decide +kernel

theorem S277 : BRFrame.sub P3 P4 TB 1680 MM 255 449454325 625 449453700 449453729
    0x120c07121704120c06110d0b010207150522090f0605010c050706050c0c0a0f031b 37
    0x100f407201c0c240c004409592040d4402c543d00c940245042c0b2107280f071003240c078481c0e5110843d500c51850031b1510500d01035000051800840c7c0c640b8a20440c000303c880300484040d00041000c0407040003928410b50301e1800d00b001c5001401d10b4180000714020751000c1e0f1011a10903501090500241c0004100420790106089c0121440b50410781d03521400c10644134200380d00c4100480d8024a8076901060a0031800c0380c0d0300659100d0007440e0b510032101510320040f0700403441014050f50010 = true := by decide +kernel

theorem S278 : BRFrame.sub P3 P4 TB 1680 MM 255 449454950 625 449454325 449454331
    0x3121b0d1b060e07080705040e0a02030c0111030403020a170c120309100302120c071217 40
    0x141d42800d01c0c954540d0940b25550f54001820041c0c00903c101d00140c00c00c00700504c012407410052204980071000c01312700d907400c240039520060b0340205d10400c1c040d200b4a4503409407207407030700e1540c150722469000941c80241170b6000900c030007140740c4050b1560107d00035036848001210030b20240030100401104260400c1203450494901002500030020162a0050910000c1c142c00e8034052000c0c4c462203201c003004165882004216241141d0340382c1c0c14507200850709803880c1a42c002d50005 = true := by decide +kernel

theorem S279 : BRFrame.sub P3 P4 TB 1680 MM 255 449455575 625 449454950 449454977
    0x9010b0d1b3201120603050102030f0a090f0f02010e060c012405010219080903121b0d 39
    0x1000403071500d0030420060312501d03000030410b10900d05e010000400e00c881035010314000e0f4045204d1601a445142d542e41c02c0d28a016000381050303500c1130111740013801a2402c00051841814000f001841c0180068002e40102d101100f441c0d45510325002c0d030680c120340d102c0c0d2400002005046807400c060000390f0f030f0f00d03a130b078640032085c00101d11240c1400030560903070f042c00200404a0b100511800492000303038004542014401c03036410115500d9001c041181c540242c1e0682d21804640740c43c = true := by decide +kernel

theorem S280 : BRFrame.sub P3 P4 TB 1680 MM 255 449456200 625 449455575 449455649
    0x9030e0f1009031203151202240708090607080703030906060f0506030f09010b0d1b 38
    0x1800d810104c000c2468001a042c150214070f40a03658198090440e0503032000e500c109500c2e02003400304000f00001000f003d4401b02d08211070050080100140400300c0206494a80d03441c0d500440e200f05620680302d44c0d4a6a0503d8054000d06030941c068888900d000c0f03000c1023400703070169120140c0704001e00103425659070344648440e519004002d0329040d507d074030f20400591200020000c40ca849011810602c1400107844030030318019610130351008007416811380d000c0c3c7c0f0f080f02c121003c0b811 = true := by decide +kernel

theorem S281 : BRFrame.sub P3 P4 TB 1680 MM 255 449456825 625 449456200 449456213
    0x319020f060f0a0b0d0f06060e01060306181e06030b1605070b0a02071509030e0f100903 40
    0x6090507040c16580c007010b698201d40c02a00e1107000d000949045070080039980302d009c82c554961000010864000d11501c8101c0da11031080280c4e0350304000851009102554100e412042d4a0000c102003010070720680e000342d440341c60030030898144040c02c1c000d9041c09046900821100f008158001060030480c1c0d90419114000907803541d4591a0000c100c0c401c110034074904030714000b0003000f4503074800300b440700f4031030140c880821000421082c041034440403070120b00890100320003040000d00 = true := by decide +kernel

theorem S282 : BRFrame.sub P3 P4 TB 1680 MM 255 449457450 625 449456825 449456831
    0x21e0c040b03010209030303070816030513080c150c070b0c030708010b1b0319020f060f0a 41
    0x452052541590b0800c1080c1e100d4601f0b102640c4942460b03200c02020b40780440300304503000d07800c0100c00c0c10181341c042000400c00c01c103004201040d400540880d01da440b132000700f030b1501d90200e140107040140c2034200008599504001c20031603216110741d645030740750004101c1d0607000c00e480403000706002200500106840402a0040a0740100c00e50303031292500c00c0481c2140c0c4046d0000c4180581000c60b40400b03601040080d80154607400100b4941ca401d4410070000040501020b031141d071 = true := by decide +kernel

theorem S283 : BRFrame.sub P3 P4 TB 1680 MM 255 449458075 625 449457450 449457461
    0x6010515041e08030309030d0c050720010e03030705070302030c03030301050d1214041203021e0c04 45
    0x2030b0501e0446040c4490740312042900000007080342502002c001004031b00d807401800c10001c0a05181115140250400200003410a2400c580c41144911940404050515190480c00221000310381140c20200d8215403d41c0100c1c0c2c01c4c801c610f0b080c4007542e8101400d40045081d0f40c075010001d05c1000c8100d001070034407102c1c0e1a40c190418880da0502c1e4601004901c025501c0d903858a2010b10540b0154050300103005000c0c1041c142c04910140c5250600c418009200520407903003000020174 = true := by decide +kernel

theorem S284 : BRFrame.sub P3 P4 TB 1680 MM 255 449458700 625 449458075 449458109
    0x15120f0f11030106170610110a0b040b06040c0e1f030e030c030406090f080a110402040306020c0604050601051504 51
    0x7054001e840d12040162b0341c005040d0700a030fa041c0c49281c400340811007141080d1040085840c02428100c80740640840007542e0504055403024110203d0a18103140501035005918107540490949403100e4901d025150340f43c005200d10310001d02007481c006000e0400c1481c3e5016a51140302406e4204c913180c95008900d108607010942040d0308001c0003000c9070381440540500701840d0040e00140c20507062151901c4010381000d407180e017428940c10806000320003220204c9082031003419a406c = true := by decide +kernel

theorem S285 : BRFrame.sub P3 P4 TB 1680 MM 255 449459325 625 449458700 449458727
    0x4150801140a2f0708030106080708071715030a0b0702031315120f0f11030106170610 39
    0x1060f00240d40c2d1103948800340542d03e5848902c044c6c2201710888010b80040c3d003910003d20464860800d400d881c007905019040f0315210b40fa180b2a80182d104001a098031945840701c001c030b058418441c0c003440c0c840d0042d6680d40784c1104111105480781d040900c18260700c5082e00d64059024241000480d0607250001e005080c42c03520b80050030302480e0780c0c0c1d03040d41411200c0c02e800030524000c40c122541074440b141c413142c5c158901542c0c444200c48581d031010001841c01d65590207031002c4054003 = true := by decide +kernel

theorem S286 : BRFrame.sub P3 P4 TB 1680 MM 255 449459950 625 449459325 449459411
    0x10e09070c110a06050a0f020c010903061503060219080115050409050604150801140a 39
    0x31059282c1014a598148070000078064903581e003138691610440203070a112910400c1c0d000d641107005210050b0340e010617080d0440c1e80042f40801d10b900e0f10300d804a03101107a074001522083c000107440c40c40500c9180d00c1c551801c920303540c1e5403981e030380d9030b682e484200c0e8007070342d00000034008100400c401c1e00b89070089c980288000300b00140c0d40e15541c103800c04070a02c2d548150203a94403480380320b0f150320b4a140311a07407004600780305000b0581003428030b144920504241211411400c45444c00d44 = true := by decide +kernel

theorem S287 : BRFrame.sub P3 P4 TB 1680 MM 255 449460431 481 449459950 449459963
    0xa0e09092103270f01110f0d0b06040801090602090f010e09070c 30
    0x10582070601160180410021a800f0060101d0041d100c14080f000340301000c02c0001c880c616800c0310515111400d02030048190b0007001c00c200c05d05080d0b4005020301b6620600940d900026070b6070682605580b2a0800c2d00c00401c2c00744020041c803047c0e424120040c0d441000528456170744840ea03440d1940c01036511405a100203012080ea9a4076480b0170f580105040d4000d0380c24 = true := by decide +kernel

theorem cover : BRFrame.Cov 449280575 449460431 := by
  have h0 := BRFrame.cov_init 449280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  have h145 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S144 h144
  have h146 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S145 h145
  have h147 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S146 h146
  have h148 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S147 h147
  have h149 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S148 h148
  have h150 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S149 h149
  have h151 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S150 h150
  have h152 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S151 h151
  have h153 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S152 h152
  have h154 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S153 h153
  have h155 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S154 h154
  have h156 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S155 h155
  have h157 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S156 h156
  have h158 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S157 h157
  have h159 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S158 h158
  have h160 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S159 h159
  have h161 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S160 h160
  have h162 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S161 h161
  have h163 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S162 h162
  have h164 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S163 h163
  have h165 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S164 h164
  have h166 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S165 h165
  have h167 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S166 h166
  have h168 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S167 h167
  have h169 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S168 h168
  have h170 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S169 h169
  have h171 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S170 h170
  have h172 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S171 h171
  have h173 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S172 h172
  have h174 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S173 h173
  have h175 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S174 h174
  have h176 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S175 h175
  have h177 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S176 h176
  have h178 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S177 h177
  have h179 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S178 h178
  have h180 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S179 h179
  have h181 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S180 h180
  have h182 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S181 h181
  have h183 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S182 h182
  have h184 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S183 h183
  have h185 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S184 h184
  have h186 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S185 h185
  have h187 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S186 h186
  have h188 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S187 h187
  have h189 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S188 h188
  have h190 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S189 h189
  have h191 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S190 h190
  have h192 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S191 h191
  have h193 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S192 h192
  have h194 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S193 h193
  have h195 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S194 h194
  have h196 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S195 h195
  have h197 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S196 h196
  have h198 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S197 h197
  have h199 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S198 h198
  have h200 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S199 h199
  have h201 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S200 h200
  have h202 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S201 h201
  have h203 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S202 h202
  have h204 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S203 h203
  have h205 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S204 h204
  have h206 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S205 h205
  have h207 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S206 h206
  have h208 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S207 h207
  have h209 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S208 h208
  have h210 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S209 h209
  have h211 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S210 h210
  have h212 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S211 h211
  have h213 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S212 h212
  have h214 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S213 h213
  have h215 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S214 h214
  have h216 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S215 h215
  have h217 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S216 h216
  have h218 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S217 h217
  have h219 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S218 h218
  have h220 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S219 h219
  have h221 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S220 h220
  have h222 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S221 h221
  have h223 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S222 h222
  have h224 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S223 h223
  have h225 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S224 h224
  have h226 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S225 h225
  have h227 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S226 h226
  have h228 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S227 h227
  have h229 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S228 h228
  have h230 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S229 h229
  have h231 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S230 h230
  have h232 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S231 h231
  have h233 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S232 h232
  have h234 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S233 h233
  have h235 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S234 h234
  have h236 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S235 h235
  have h237 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S236 h236
  have h238 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S237 h237
  have h239 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S238 h238
  have h240 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S239 h239
  have h241 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S240 h240
  have h242 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S241 h241
  have h243 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S242 h242
  have h244 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S243 h243
  have h245 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S244 h244
  have h246 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S245 h245
  have h247 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S246 h246
  have h248 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S247 h247
  have h249 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S248 h248
  have h250 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S249 h249
  have h251 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S250 h250
  have h252 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S251 h251
  have h253 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S252 h252
  have h254 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S253 h253
  have h255 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S254 h254
  have h256 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S255 h255
  have h257 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S256 h256
  have h258 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S257 h257
  have h259 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S258 h258
  have h260 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S259 h259
  have h261 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S260 h260
  have h262 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S261 h261
  have h263 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S262 h262
  have h264 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S263 h263
  have h265 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S264 h264
  have h266 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S265 h265
  have h267 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S266 h266
  have h268 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S267 h267
  have h269 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S268 h268
  have h270 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S269 h269
  have h271 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S270 h270
  have h272 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S271 h271
  have h273 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S272 h272
  have h274 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S273 h273
  have h275 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S274 h274
  have h276 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S275 h275
  have h277 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S276 h276
  have h278 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S277 h277
  have h279 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S278 h278
  have h280 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S279 h279
  have h281 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S280 h280
  have h282 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S281 h281
  have h283 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S282 h282
  have h284 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S283 h283
  have h285 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S284 h284
  have h286 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S285 h285
  have h287 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S286 h286
  have h288 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449280575 _ _ _ _ _ _ P3OK P4OK TAB S287 h287
  exact h288

end BRData

theorem solution (n m : ℕ) (h1 : 449280575 ≤ n) (h2 : n < 449460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
