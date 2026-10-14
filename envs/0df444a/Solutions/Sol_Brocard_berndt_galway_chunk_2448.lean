-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2448
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:48.351703+00:00
-- url     : https://prove2.me/submissions/119358cb-662f-4868-8e04-63c152dbf902

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 440107913 ≤ n < 440287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 440109163 1250 440107913 440107939
    0x106060309021311040902030c120109051b04062708070b0307030608030f0702010e040b041b08010e0f071107090204060804051c0e0f030f0d0908100e07090b010507061505 75
    0x50f51140010b0b0080740f0300001d040505004c1000000e606c0542044c3c420741050040190f00d1b00411b89040c081d012039000440e15040c01601c0742c0f0a682032008071a00c0d08014041030140d0b0341d00080c0200c011514115800ea0700e0800300c0204034141942d0440c1180740105040482c0c2c8001c1e00b002503004000c00c2d40c04002032503642c2351040d202c1c0100f002030300c9004404c01900d000743d841400310010300c8800903c006501241c14000074120b80c840c4002c40c0702c04614502005043d03810102d00b500500880100d0f407510b242601410700c140340018903074018040c134400c210116803410171000c4050b00e0700820071951a51100f4010b483d000084604544521580402c90750300300810140d030b040005c0c240c0b01c42c074159800400b0020303c0d01d000c1c0768041e0584903400c600c6c0740e40141006542d14001c5141c0345d170313910f85040444d40e42c1454584001100750500f0040c450b0070080e40082c8250868005250005031024076000407200c5100b24200604220b00b00851000110000503902e0f04a441c1100c4424040803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 440110413 1250 440109163 440109199
    0x30e0a060201020c03030a1a12010501060e01090f05060309070e0708150d02030a060e0a0602031f0501141c06122001090608060d05071205100c090b0a20010606030902 73
    0x42030810b030b01c02c145c006001244070300001d60000e8402c00304404d056004051041c000c0369801c0640072007068240c2d103c200400400b40c00c00d00e14140c010003841e2144855080c00e0303c0c0030744010144541400b4807000400a031074910305002a801825100b213030b0444508007154000c044003820382c0d4180c4621b0314106840454038094440f4400c4640c0500504032200385510781800030054000c42c00b5003401400c000b10001000f5200851064052080c01c41302703008003a80402180d2081d03044035045c4640c0480d080410111070307040c0da0203440c204010070044400c0c034060101038509680a500c103559030542d8030007001000c00c038030840c811601d400080d00060210044070103111a20440c0c01081041e000300d0303050704105041000142c06002103594550303445003421600360000308180e82980003801c020307188451500841000000318a000c061050030150501c2c11442540148414001d103582c01d84401d0a2582020100607010381c02001859a90032000d009010030702d8040388a079410302c0790420004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 440111663 1250 440110413 440110417
    0x609090a05043e01030219030609060905070c110a05090414060c033c0c03090f01060303050a030911100f030e031e180a03060903021b100e0a12030e0a06020102 70
    0x1e011000c1241c50a00700d03c42100845208030010b030416800f04205051001121580c801408440d98005005454441004121600d0390050b409650500c0103004416500a03403105905400501d00c0c0f006030140705c00100d2210850f0702498201340402c08001c00e0003a0541c082000451000a40d2025079030400780035403e101c21214024001e90003a140b009400f00a41d9150403a1aa2450100c07840e42c10040c0c0b404501301207600f00601500042049850502802903aa400307000304020f0050070700b1030b60090810300960721500c0806a81c0d1050200703014810702185a001e4003d403005c40180096100103140111146003040400c0c04c11985240c80c520000413079100015015251120044050840e511070384000404039603a5400e0b0212011551500701c680b0043d03116481c00182d8000c6490b010341490700c540042103410b001001c80c075459440e2540200781c542124580f02e04240d201200250000b10250001d018019103912210105501702c502c18103203d604a80301600d10343e8480d0300320300b80c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 440112913 1250 440111663 440111723
    0x30501050c210702071511060a0c12060e0c03130209160207050109080d20070f090b01021b0411070512090a08030c070b0a050c010c0306030b01060302090a0e04020609090a0504 77
    0x16171100b2400c1040003c1c0121404a000f800d14040d91488402d201561500700140e951030340850b034a80002c021690000d400c0080054500c2081c031480c4d1400c4071001003103030700500030000c2c000000001401800c040205c2c0704080c1d4020551500d5080a41241041103050351410000d44680700006c1501e42c020403030041210352140c0100a415202d007400c4404001c25001e058500d0b0719401140382801051102c84050010707031148d107040c540b404c038695050700c217501501415034200d404500d606800451340060108000e980100b44000301003201c07141c40c8a1644081d00301d0080032412075080a80c40018041e02c2021205080d1942c0c80c1d810203900c034854040c4540b42580724020412460b07241c0405040b4042072410031500f0004072120190954540b509280c0000c0d41d00c010078001c002d00301e092075014011a02d0f046081144140100d07120b503a46004906400850f600001c0c1107650345412940030074800b030000b0383d0604242d540c3d000a0003080c0e5003100c1d880c80134081d20649200c0350107030000c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 440114163 1250 440112913 440112917
    0x12170706140603011e0c030e07080c030105010609140f0609030d050c0f0c03060f040f02180a0509010e0a0b060d1a040c0e0c07030e0d081b061b03041b030501050c2107 73
    0x100b05170740301280d00146801d8515200745629a48460141c1c0418403148000b00039000c054400030048104241c2100c805030842d40520806200070302494000b211860800d21058611008040074040040d1443c0160740c0300c0d641c54424003080451095000700903000f41142d10084030003c0f03d560010580b9084242e80703240c0c165002c1000541c80310030b00d24226030010300415a154101c51250040741c91400e4207441c1d0303c024080f040c00d1000341c01c20f5114140c1e024881c04001c000c0d03841d040991300e40f100d05a00000c0d1250680e000410226500c1c81220301c400d03640004c1b2880d0715500c04551f803400201c1190103035800c4a04c05070000d9004034007040584904000000a890010a9541661707010303100c02d003540e000340c08941c40d080010031100052013000d040e21100226000f440551920f007070701c020720400c1c0d000c517401c011080b0100c080055a03041030f440301020603206030364030746510b09030346681c00a02198205014000c00c0c180e4040100040e980a00e0503900c080c44070861250030400503940140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 440115413 1250 440114163 440114201
    0x20d0b040e06190204030203100519060b030105060a020f0703060b03070603140a020a05190305090d0513090b010c080403060204050f0603060a061218140c0d03091217070614060301 79
    0x2010b415140f0034407400e0079000d01c00500f0a505c81c0c022910b020316408100c102c543d92001031040f1500c0c0e403c0d00725800700400409001e400d0801e58010124007040c884c440c01080041590750302180240071000005540c9030443d642607a4a00340342c1d000e0601d4600c0380c0d0090094030b0010801c54803034060444920f01920307012406454980d44038009500450580f0300700314060000c0700c4180c1c00c0c2d240c5201404166a008640d900f01000200d00380781c0007001041c10320600300b2021950540290010003200c1d110400002d41070750000058504401d102c0d0014609400098044200206903014106565007600d26071002107110041c00154442500c0c090382c8001040da041005500c14a845035100720710795808a42031403080c0c02002c2d0b51008400c00c0760402e840070311480d28008108990340380f00c13004980001e00325195440161002d2450300a0040d004042c0b00070109200d00c210004180d0240f100c0c1d99541d07201d00c0c0c02d03c0c40003030131401c01401c0b42d001d150300400c000b8907050288118000d80c92480d80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 440116663 1250 440115413 440115421
    0xe060412090825050607240c02120d1d030307020d0504050102151b040e190c2003040b07080a030501090209280b0408030301090e070608070e030f0d0201020d0b040e06 73
    0x840354030f810701e100c5184201e6103030100301d030344a410103005800c0c81001c003040c042d55480f010f90b01040c01d162031548180d240505104a8990008501511000c4100c13419a038100040b000d401401064407641030004108502143d10b40000000358410555503090307a02c00846850111054031030392042500690205002c1d006000000b81d01981202c5048150b15030018641d10164180d0440d602c10701c00625040c040000c201034107004010040d69000040007001d0710321070040c002c14803034182c103900c2402c1954180321145003001205d02821002131400d0725000c091900800562200b50440000380c00d281c000141d0310414000d0b50580f543c014031004002003144100c3d101d0024600d503c03144000751000c0000c8000715800204003a10020014569a40c1015585c005030f910300e982c02c000c03991084008100e142d6116003044c0c0c108541389040b604416811001a1400b080c001e5411554021003003d444204d170154002c0015170f14203101403090384943d408001c02c03210002511101030300114005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 440117913 1250 440116663 440116693
    0xc0e07020a030206011d270d050706060e010e04150207150903031d071502031b061f0b090405090c040c0206071b08030604020903150405030304110d021302030907090e0604120908 78
    0x286003018104252401600205c058107281a006180e08c80209000040c0e00061142c4ca009150182c41e0142180080c1d52615a00900b4800c0081c4082e02d940006124542e510100380c040301c00d240d801c4202280c001c2c4038004200d00034090403108a01007840c028075048454900d0701c00c0029081e40501801795180f820f01d01c4c440c046188120441140000c00c00210800c40d03144400c90090301000003001e06250404603501000104805c0c420300740c0031080100059804102203682c40c620540e8041a141c03507111015180c40903d5210f00e901500300450348955a500084003403040301c050740c0f00304410302034908240c0d52a5a548019180c40002c0002039400d040c5500100752100014003160401c00d01e106081c0000c017000d980481d1150800003c3c0000e1004000b0b00b14000c80c400c9540e4007030180c50b940013407232a6207400f400c1040b150300070000604030401072120784011708148005020899107101c0054403074000711412500303602000103514000d48941841d60649040e40b0080021100c084a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 440119163 1250 440117913 440117941
    0x2070f051605040e01142409180c060414010e0d0b040f02030106050f0d020d08040b130f0b210a020c0d11010c0c0209040f241d030f160c0e07020a030206011d 69
    0x807a00e022000362000e10071f170303144c2a0040d0700c20686d0025001e480b101d02d07080e0034204900442c2d02407140d0300602c01441000070500074041d50800c242403607071413404102d010455209107410060100740c04d0504000a124074030110040047c0700301c0c000c024070354448007002003841c1200e03124ae0b04010b40b03101f55401030a00c45280d10000d805402c40030300302551007901e240c255000072100c00d81605410b40070002c40004094600150034204541420b01400400c045854a00f140c0c041094611a00224001140036812141e00b00140001d8800f019241c50b0080c0c40d101030515640d88c01d40c6407031041c0b000c00e4802c04421465aa0040619080351641d071542c4002407112602681c01248040220a18008070903a41e61a082d00150100d40c8a070b00c90090051006d81585260241d00304220400c0303805414812034a071025800130703518140c0750728140070800049a0f00302d40c5148204505100d2950f400182d003080d03580c460b90031175545a80b1541196203411019021407002000d2501085c00c403185010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 440120413 1250 440119163 440119201
    0x12060e0102070501020f0705061e0f060112020a090f0b03061518090109240305070b1803010603321f020d0c080109061403060a02070f051605040e0114 66
    0x80094240129922442e08981c4075034011200e0f80300024150041281c1408042d6000c0c2d110354200c5058442001c2c0c03208481401810244102c0b103410020700a6809086161034540d40c8020464950465078070203004d4080714004d2413400401c0304070003c0c90a08003400c403403040c2800b0704544c01c013000b010410050b9412805031040d80d02d15a5585000035218000c81d580200750709680428801d00030180c40c0c15440417000305140420108205001080000070302d00d0407108580f00301c41c2e88030707038402558100b80b0701100c1503545942030400010038040b0f4045c111261001c00d03100e02c150b8400c01100c0e0021010031028255031900010010b201030071445102103d500d1900030090310300076081c1150310444041c0310780301c1c001c5003c0074014040c1c28954803844025100c4045000001000a000603039120300007020500403940004d046000c0042c0c40c0100d2014541c400c040301c1003031040d00712048140744c10740204c42c01113250506d0054a07910500445d201d0000300b00a4004940310051800c4107280220703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 440121663 1250 440120413 440120441
    0x150305041a190501050613030b0711010614030c0a03110609010c0503160b0928081308061e010b07060b03120714070f05061902011b020109110a1206 65
    0x8007090405800880c00e4450200c41c0307020a141c034a00380c1c40908595041e000075001d0740044c050b01c0e0806403504071314011340e5000205940c1c0c4c0d5446050171248103400c07003807502d59542400380c00100c07072071020b41080c50002d0071400d4540641d201c0c0113001c5600c03094031000d0082d04250082018600b0080005c1800805c18034281d0036030101c5448035407030340d0300c40c0d00540740d25800080711006020f5400e600d544c02001c054003818084544100500c41c800c80e098100303042510b1440e41c0070400440c0012903080080072280503c6095071070020329103800003147e12036100c040401000e03000802d40030640f81620b24a910355810140280c494800415003541869050b00c944040840b03240313424400b60003002c0c46481001401c100e003810841c20048070f40d10071903000203070710010f22556031200709540030102e4090800d5034101d06800200d014004601d03640410f51016844403841c1c6906400c460403081c0190320104218003c001030000350403041c45080700700c1b08642400310010b0b8070794011b5203000d4200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 440122913 1250 440121663 440121683
    0x60e0a0201080a022d0a0e151b0a0c0807030c05031203150307030b0a0c03060906030c030f050102190e040c090f060302070503040b041e06050f030705090d0b07050406120615030504 79
    0xd04c1c1001003207840d4200c031100100085486c0d40c40c02d40c002c0d00429091000d442c040740110202004152500424511041608030300314030300e1804204002a00c1c805402c600001e84c41da0707498007840d885403080c1c0000c0d607020300c0291021410341400211217104266040c0b041d459903076154150315505500c41482176141c01114400004504500c0e901c602071840d1203030010740e43d03003054005011940507500080507903040c40006c2011403a281e940d40d0441e500004c2242e4080d0f03503440c1042c0288110030309070302c1d6008e20404500203160301c86107041d400a01910b0800c28111481c4d8280c035082e26510800700c012284440c10304c00180300f6005401814480d0f4120b0303042c41d80b1844c00000035009500218801c080c1d41c903d01942c41905030307031140100184e041a03031070201540f00d1512244802000030050020029201c0b6441d2100c01c10044586c0c2c004100c0c4060341040580100a540310348510f0002440d6a694441803110b02c2c03080104035122480000d030b0341c3c0740300401500a0880140192060400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 440124163 1250 440122913 440122957
    0xa0510050c0111040501120623011707031b052d0403060f0b0123041e0e04031d1005070204050c0405060a09050117010506120408160f060e0a0201080a02 67
    0x90040c240050040a82140c54601744400140703403a401c24041c1180c40e0410300704020b54885802600080c49000c6080c40d80d070388401006a400c0c541c0da01071034900c88115000c0100f482d5269212907003100d000e03104040c0920403402d04036401d01802c1c184d030b186140e9150103900352403c0c154422101c071840e07180d440d052503030784c1d2180c00c211541c4d10480b40790280c48100c443e0702c0d0341c5e04c410f000d01c5c440404c0200000348540311041c11745038050381c0251549401c10411482e07501402c0d40440c002004c1c4005000260315040c03800410640074004880c0018038282040d08061518407995800d0145030303035515090000a408100c058070740581160304100c2d00b00400302d82912844001d0071040c00c161101d0301041d1a1900041081c107810301000f07a2160250014015075464a04880c2010050501038510b5184c40c109a1554451110480004000400f411040002c601900c0f172041e0301030002081410039810381a6115840c0c00e40c024006280a000220b400b007182e4081c100901c0ca001224513000c503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 440125413 1250 440124163 440124187
    0x1206070c1509060b0a0602070303050d020c1216021207061b1104090c0e0f0105060415141303140312070c1113060305010516090504021c1404031d0a051005 68
    0x2d500c00082d40c089131200700920250070090401c034000c007001c2c4000d044481c80d40d2001445030040a60341044242c00040c80b20002c0c0d010006a003450b086111190354072403d040e00d4403400e40b0440c13022130250016854a90010002141404c202c81c2c0c1912198009010340d40c8195009001b5101181c0c40c4500080c0e40086846900c12400120300c507500e0204c1c0c3e14100448060b440c0c2c001014841c004201400612040d25410f0949040320f0116003510b80a1302e80740c20598002100003040d0110a402240c1307084040030f10110801140c0c055400340214942050303889c0e03128030941c040b00362080b00c40404948080d106070b0f9004645400740e81401d130010f0b40c181c005034503030304ca003824004540e450b001c0600c14060207214840d082030404001c1400e41c00380c050b0203483d030000c1c0d00c5040d00c15a0301150790984100c2d01c40050303000154109003002000c10b020801e10803050300784d4042c0d00241460440d0401d41005e05070851500c3e00052030254410701d4202008004d03940400320100b040340500c480c00900d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 440126663 1250 440125413 440125421
    0xb13030306030b09061b07030f140c0f1b030708030406210c050a030506030604030e090702032b050603150c0a05040302090a0c2322270b1206070c15 65
    0x1a03103120241400382048200341b80100c600069440141c4010400000001e0b040810410b144007036040c06243e04240d811202d01c5400b428410900a029002a6008a0f500800e0705405c00c0100b183d0006024640d100380f580c0c5440502490345c1d103501c02c010a000e41c50285203012251459501401103502e15812a042038484141103100425004524101255014019954840b4080e4001c103c0740c0350640380140005212034080f40a001a100841c20b01703442402200e01095003490300c0f902d031045102c00c01100c80c0c91380c0809202c051900c80801c100d0719008c103000c001500e030341064405a0700d03003001c110820340c0140c102c0c200b8022700304070000041e03d502090a102d100f40070400200c0801000c3c1c040d03e00742d11a40064102415120751019003d904815106000391500700c0b03441c2000240320040000c001c1340c00a240440d80807800418191560303071150361701811400c0c02e02a4940c21001e20501011901414800741c0005c000200310700d203d1030202c10003034000c1c4008405003014003501c404031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 440127913 1250 440126663 440126671
    0x60f0303090a12150c0203030f061216050a090501050d03030b0109210b0a0b1008100b040f081209060a0c1104020409090b0108030a27050406090507030c0c0b13030306030b 75
    0x1c0081c402c10406104c2c0500a0000d0050480028031242d8101c64000703440340710050105200d01e072843c001c01cac3c075610307142d100869004c1284211b542d40e042c0003051111101c040c1c4180f902c01c01071100041514241802000c0c104c80c00a02150030b807075002e645c1a0082c00740c0840c02030410499a0000807500791101c2010004040d8002c01e050926480c01d1070004110001e061000d0036042002640003501e40240310400710540b80b40007a0552101d00c890040091590710034000281c0209011903c0c00500d8510011110f400c0101c8480415009640d6051b01418100c10740c080010300240006601030744a0304403a40c40303180b14181075205140002d080740c120b0b400c158125a554843c10042298201c801c5000d44680b500540c1030211548009020381c43e220003c01000000382c0e448c0010382d4100068074083d20340280244400c640703411081000300021146000000d0604480c41122030003003080d8500c02e60820b006084c10707601c8200002c80d8000c031010440405a0701d800000214961003511801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 440129163 1250 440127913 440127929
    0x150307030b092a12060402010e13020715020a081302010207091a0307060509040b06130504180609050102070605060603040201080103080307050c1204030203060c031909150f0e06070f08060f0303090a 87
    0x2046804801d00c130a910b00f4800c2a005903000005100250ba04290a11000074046071541c01d18884248820041e0103043ca00610303880608040c2d50410706e26802a0814814950300d481ca04d90340d075a25041c442c801080040d0250308007407002e11002e1619045041c0300d185400301c1905103248032010900d01001c9a0103280050700221310f184d09d07840c0901404003040011140705003070445500201c1d0360300405225151240f503039414a079440c4988101c6c020622a049181004041510b00707106010b903004083c1210380354a8031001032080c0c82c0c180140c1c1e004e06e40696075138000e60b0031960303020780036803025021106201c001d00080c00302600030411142d03110107031226907440394514818146132400107001111000001d10402c101c980010340c000c017907441c00f104042590343c05400c100c07040ea603404405c05181030400200d03560315181c541200822031525821506940d0350704000303d50040c0044031240000f01541c2c00324146280031202c48145810090a0701d181c08107800028218030300c2980003e41d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 440130413 1250 440129163 440129233
    0x816051e09031e01060914060d05160f0504140112030c0321150806040f060b01090315050414010516081e04050607020610210f060203130b150307030b09 67
    0x5007404c1c010381c0b0003055040000d0000c1f012400000700d20324001414a070180b55140030240501804120304103241d0315804090015035280d82e10941100107501801c0d000c0d900300481d0020360308a0426460484000c40f202d40c1070460103503000c94008800350010303010403a03a0400b80b100101c030b55840c880c424152030703400030341c0c80c0180c800034640c0840d5510403112a0403da08100c04100b4020045820550108000440b046e030040180d0b6002820340005e400e05030041c1b02c0c400008001ea103e00d004070300500c0d10180708032119501d1400c1e958100d800d40d130b03c200c10f2103681c2142401603002a81108815034a0040c2c032029941d10703110203c0440303040d0b8255000c181400303480c0d6014010710760416200d00c448940356013082940078000c02403241030300c03101075903119003800e00160401890002d41d014005550380d0030480840d90b52a40004001e842e120a088040786903000501e0b0a000c00e400d015002c1c2400c03d1070340c7c8689400b080c00070300315102c40c0200d01428400c0250a441014030328040b840baa2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 440131663 1250 440130413 440130463
    0x106030c11060115050d060906030606062304090c0903080708040312020c030d050a03090507080c0f0105090f060903030d140f0108060f0c0a0e03030c0604030816051e0903 75
    0x40603025580360381e40711030304640700502010304498101c1c1e10300251820b040c3c1c1d5807250762000700010311541d4080d0383d8503460300c0008800c020158205800301d4180d0fa8407404060301101c545084041584000c08141400b00000c00800110b50001c890080080c10840603141c0c1d6500c8002e00390340121001c49548000260a20810084081c0c6100601952005114035050800407903960044128400148030303000c24030aa00720312980002c01c48690100a0b90071280ea031f005526600c40405120510840c07080c80b24414552041c401e0301c281041c010841c01e000e2030b0820a004c4540e00a001098150000304912408a8240d000d500050201410701c9400d602d400c039409494000e041e00507444d141c2200090009900c40c2144042d0018001c074245544c40f4264402680c25001141e42d0a4041c0408240d2012200001c14154462406501c1e0b110365a5100400540e08485101a200c0403800502082c0c0384d50301c202007444003903800c032000a40703030000c0000004c0c030701600c1c031400c150b036501014080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 440132913 1250 440131663 440131667
    0x131104030c0905101215060810050106030e030901020a0f0501060b0f030f010b0c0c040e070f1706060a050108040b07201b0f0a0302010c08131503060b0f0a031a090106030c 75
    0x180d03407008004c03000c0601e0500300880d020070b400c950311025081c0200380e80c41c030040c01c07460b03441903000300760a504485070380f800e00f2055000f600c800d02c1030401103071501000c084141030105c2100d984e1341050b0b0103454548034554601c1440d034202c0200355050b6580302c1000c221003081c10700801809007580740150300c0785080c903040c40800005821480e81260280140090b901000070455014482280c1c04122941d440a030342d881c1c01d44940c000c60155000000005404105a10884032940c0803815619250350381414455041110302c01d040c00682803100190125121b0680e880e0482c44c5440d0a00c8018520080d0458071803c0121400e15a00090306070041c8501442250f40001001c2c4d40c8020000b0005000a0b2540658480030341808846804481004000300450340400000404242d00c2500c0c3c030000c180c0401407584134408a13140c110042550780002050b40d042401904a003403400840b1541200580002d054807240401c500d081c440c3c840d0388402501d4041c00d82a0340c001000d6142c0140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 440134163 1250 440132913 440132921
    0x203070210050106050703050d1a030d090f08150f1506040e0108010b0109030825020a120215030c03150102010e120d0f0501230604080609060403030c1d131104030c09 73
    0x84ca0602804102860011b078210056500701944103e001071410302c03000c8c10080701c141d09000140d26019690070910000d0b0000481c80503500c14402048402c1d03154019180c0e82d8112190710000030b012900066014880707940b0355607204403908800e000c001d54102c003051494000b030f046080c40c600c44400510440c00240305100c0d15070400d00c0d00d0883c681c40c41d100c4045900c10119108408564141c100310040c501404c0c070035000d640607120f0f00103582d8505040145840e90725040344242c1110340e00d07030140740002c02034034091035414a070680f850b01d50204030f04e0032441e5981c001381595210040300801d04002c0c000a6540e60381000d07080c1d602c00440401c0b404641242140f410b481e4544001402941d032100c10140f00c0210480c400c030303542480800010001d0041d0360200c00c00307110b19000c01903944c0012030004e00440c8039880034840c101000205441c6264040c60350300309590603202c602c103140340c200382460500503081000124581011000b414550142c0c00a80c0c40c140300c0071007084080d109200d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 440135413 1250 440134163 440134169
    0x70303111b1005040e0907090e0f07091a0d0606060807050a0203090603060a12030e090604050f0402010e041d0f0d0302030702060c030a020d0e10051803121902030702100501 76
    0xd4241c480c0d0a4040c404002429205140510085400150840e002e01d0403107011300540c5201101074a8148000740c1e852065024a141480c10140b840038000400540350008034602409040304074200b81c0080010310070003280c4440081d10105c001c20a40301d048001d207009010306401316280e42050006003080c000a801101001010020f105c0d103a070707010040c1d400d050011554550750b0348034040012444241900664490304482030b00c2800c0681080a41c3c10460703040d64400c040d6076480c400c10048903021510000c200b04450002401588074000c1d00d0000e040040c800100308144200340c240111219100c070340c585c2e22410711944107020400c0112280402803078158654646900029101e40e0040e08800c4589008004101d5140403138050701d4807220144802c02595554029142c0d8a100c0e10f0400d1413428940f070041404094641d09403680081010011807500480e2086100300080c001d14040c00c2060320484c0701c1e00c1c070f98103000075400740d001075004004054000e0360b01011544103078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 440136663 1250 440135413 440135447
    0x2070302010b010e130216020303161b0e0f070201150f0f050301050705040e04080403021305060f030f0c060c013e0406120902010c121d090c0d0b0a1205070303 70
    0x5034100b03c3d00d44e0341848445c16162150740150321110707540c0064200c4075451000941c9400b0110300021201c40d4146000d08040c051403190b94003800813001c0c2042c900700c600410f0940b00d0f40700c0004a01030284400590041c129100000750b4540e9548060000c201940069501c1c3c6c4042c0c90401c8401505030703812010b060114001c005509083d040a40144241d104160940813610005024000b100c01503500843e006000c0040c2c211480c007034031000b05400c4681c0c5214030020406e09000d42000280e65035105c0e143c02c000c2061400d4082006040d810003901c0102d650340f03850040d42403a1180002c000150301101c401c041ca50252600211546000c6000200006003480b08204003584030a125042e8001690002003040403800100c40405e01502d0261104011100b144001a401040c10113110000c00b0b0840512115001300301c40c0020a44403d05220428004021015401c2c2d0080d41070343ca00900d2810b2240d41da100e080000208400d0070344698226032030802c240750f0049501a10742460b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 440137913 1250 440136663 440136677
    0xd02030f0301060f1809140112150b0a030212060106020d0f020607050a030204230a15020a02040b030f060a140f090303070f0e120307050c090c1e041203020102070302010b01 76
    0x408480c410341c0014800d00c000c2181048072081e00c10300503100710b9103008000090000243e140c040d250082c00c0600e0b15424000050b400000f01c4401c40c480d58206d00394490075041c4511810b18400000d810000602980914070110000050760703200c10311418001c0b07900203400a0340c0b50600217820080743c5090902444019043c6000840d408900c059001186081841d101c41119004030001d0140380c110b501c200c48034940b0b00c044c07074a900481ca4644e120880e0320341c0e8203d8881d2650705849000303002d9240964443c1c40c2180041ca001d8104880c032810180454102032144190030b4600035003070343c2d2114107669400c0320944a41108c0d030740720342c40a0801c0c060081400d2100e100340c1c4c1c904c001001c05c0c04000c000602032404510903040d6102c0031000a100148002da2008050303241c0c1d00c010400c035100d1240603100281414801000d80c82100740141190402d00f2010307410b240700c61184c0c6403441400d02000007080d03590f5a424150101806a4001601c81d9041c0c0f40107400c44103141d18107412f000b00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 440139163 1250 440137913 440137927
    0x80705041a1008090c0409061406120c1210092609010c060509160f05030f0d02060613090803102903270304030501090b07031109040c05090a0b0c0d0203 67
    0x40c00600108202541c9080d042e25620200301e05d003130640e00c910079607115050075048810300c0582d401c8250324880a040704082d42d128030041042c00c081d506407506413500403480d210303090729213a0701e050f95610252050710b0350000c0c126904001c6403d016022034682d02540c86240c030b4844d190351900c408a4038280240c0c134042c2c0c2400041d11401e0009070080040d52550002030100340d007440100c0800042640b82c3c100281c55603200c2444544500480d802841882c0c040d008041000440c02c641400703030f070041c141d661036420600000c1c205504110b0031154172076050000180fa104001e612410102491966107410801142041c0c0295018115a03500c0101c5407101d9150394021203400c0384082140321650181151440081c2081c50340d0701030540000704001007408019000306070818410b50228055584482c0300760304071081400680c4964401784006101400c00d6844500882c0141c10100c3c1810075403000209004d503160072044040402042106444100300300112078240c95001550404034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 440140413 1250 440139163 440139169
    0xb0a091a0315010812090d02040b010c1208090d0c1a07140a020102041412060c1806071208010e090709051b191220070c0b0c0601050a15020604111504080705041a 71
    0x10287c1c00a48a1661500350f0b460300d038082c0f40d000d01c00e80c0d4041d01c0c1122201e8504005000000c045920300c0e5180911030a4501203440b42d040500e1484e4899282c4402880305003216821190042070700301444851003c070300031080ca02c80505001141036001503581d500308620781d50300e50b080100e00790241007100c0d0b5040903c0004680e607039006c103000017415250100031414406448040c00050342002c0c0000781c401c02c1c09503100d030700c0c040c40c800c40e110700c103a591b41d80c41e8110720703150200c407500d88940040c5800d01140302c07903400040d041043e14602500d03001c0b40c03120100036035020b43c030300002411464038038200e62500070380701d6290710f01d40d8402009031046100601d400b1a0b040c24280540b140c00003a102c00b00f14200c1c0c00400644402d074042500e801d00d65240b01e69074242070284912402c40102c0001c2c43c06280054200c80c84d50035800b5083c01e444960314180000003d00d01c0991045402928942c20001d1307034098002429844001e124140c644000e01003106d445040d40300142c600c0100000c5240c0b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 440141663 1250 440140413 440140429
    0x20124080c270604060b07060501091d03041404140108060402150f07060f0f02130305010f05190e0f032a061605130905010f0311040b0a091a031501081209 68
    0x51410702c1d403001e2603591200090010503a5410640c00d012020840703006200b00d07039108038140d650042040100103020207071422000c6404550020310b03402004140031003902460045100d006c0603102152030500d0345212101c03101c0982180e000d9511130420041546040d0614003901511950000c1c0341604455006089209004010707003c07544800c2602610841c550000c1c030408050f04045444440e480c0750b588001000c1d00c020b660941c207161011460808901c2858040c00101d2080d40640441d00c1e04c0c0f901809200161280c1406802210300035900144000c0500400d4440c1004401158034104081501140e20035005640310404202100304414030708440c2041504010341c40c0c1101490302248100309420101c851420040005061400441020243c030310643c0c0003412100380805001c2200c0d10001802c3d8444185002004008441e62107142400e24000c40c2d039402031071001c00300780340c012a0200e042404489000404c1840c03030600070100c20b000801005494a03030349100040841c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 440142913 1250 440141663 440141719
    0x706020703320a11010509010b0a1401080a050a150b030613110412051c02011a0103020901090522110301030c08030a0801181d1c170406020703020124080c 68
    0x4a0001e043c0a889001d94007007105071a41d14002c0c8824075108031854064050310035541d01034082d005c1c002c940441e141242c00b46880b010394860340690703680c504403005060090900a0b065130744100c188014100e00c4c07005409010416402a0340741480801e004051031008201078019251404e00041c010300101100d0071100206451660840142809401c003a00148840c0d80022560300d821310158040d0810040c0c8a10b0500b141c10700340620006500760320902429900103203511f84140400e01e0202c4600c0b200b58004114080400495402c420444042c1104001c500c0008401002085803819014000d400320f007018509203e22400060020f103818002c0d25000d068240b0303c040044002d501031750907125041c040b040701f000685851621141e680c00800420042e542d500641180662000981d440000b843c002840e692602c2d41c80003904514012801c43d5255051010300c03450b0185020300603001000c0702039000c2d107400f10391440c190b00e811199005610360030910002016100945002c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 440144163 1250 440142913 440143007
    0x182001080c0d020c07151404080c010c0c1203050d05090304080a11010e060a11010e070602030703120b090f07020106060206040201090501030c0c0b0114040e12041503020f0706020703 80
    0x71880d11010100107802006060001391040382c00000d0400a1111228842d032443d44805a90700d49109032049148035a01924505074003148c0d503100c0c10b5200d4441402614019040d94a030365440310281c030a10700016100ba80012008600500e11205a108094019001100440c030781803400080c0d1740c0b61092141d016219000e9060303154400e0b401104001e08100f4024001651190b200ca0054504109618191342e40d600e4480f80c2c030032958000a600c420f5034480d8005504001d5903681c116400c2c086e032107264030042d8560040c0d242c9521205d5041c1d0103008040208150341c640b251000342100c5455003c0030440d80b000c1c09000250740c0086646040d0380082c039002c0b600701001e001c142c1b0907900001d80240902402d0b030001801e89081d15102143c501c045400307202015284039007694480d06004012a81c0908110800c42e0045440400003002d00300c3c14058201068a41c0c50350040d040702c0700c00d540460b00006d500c1c04165100d5404000441c809510201501c1300d10040160046c6070041c1c151 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 440145413 1250 440144163 440144167
    0x11060717041518050607090303091a090a0312080703050601080412031d100b06070c0b1605011e0f0e06010603020d0b04180308130b0a02030705070501182001080c 71
    0x306000d001400d42244840c0142c09020b4400034440340d00b071054595209a40a00a503008514410b03c075450503400c598055448100c0e113030030985007051001003030b01c162407071100c100821071583d221021703171400441c000c02c0005101810f21401030100100202844200b610740b82c00c116090f83c02400c9150070070740000c42100c0b00401000180c00400001100d6110011b80003c0c806525400042c1c0b0240700c00f00302c0d014004c2e032403060240b1407540120b0700d004182656101c01480019600005408800c00c11741402180d04519180c0500719221141c0e0a041a451070f98290301410550180044166803002c0c01c1150f201484144c645510040c001d2034100750300001c060700e20011a820224000300d00410030400d820000c4a0190005040709003240882d80b40d0001552018020f08203c6038290030001d452902e907a000c3e810f100a500091020085c45010321204000c50b10911614100108006020702100d5807420034800400340018144a410080441411540da101e090030350004446110b943e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 440146663 1250 440145413 440145421
    0x160530100621020d050f010503070f03021305060301090b0a02040807150c14011509021b191e0c090b030606030102040b16020a0b0a0504060f020c09060907180f050111060717 76
    0x340c068450601e618036080d09180a0117020a4411b420504030b4504608642000d5514503180c05c1c0e49100340f102940c0300000b4a07040c90b4801d52604402d0740458001c00000304440c40e9914682d01440640d10140e01950108092184102c104450b05c0540000b41d5010040300c201c1100a2404402c034500610307203030b202015108010025040748910303003484401c0d82162511407600310025001514440c10340c0d442081e40d03401d8407030301081711a440720a101e86090040560340751050401d9600300c00d010101c02c0c0c020024003250205a111000d080d00d070343e0114103860500c08040c603240c401f82169100741d2040008004402800c0c04550f40c00858440b00040040d2a00004400c1d4203143d0180610f20800500c0b41004d03503010008209450b040e488030586500703e80030132603a900c11001003c0d006108080462114580143c840e9404500380c43c0640001e0700c00e4541c084a9482640300c5002051f16210900c1291f80004080d80e1584e003150003024035140614005081c9060300c2680101d1083c5d0002107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 440147913 1250 440146663 440146727
    0xb09040212101a1309081b030904020a030c020c0f010f0e010905120d0f0509100806040207060906060807090e070905040f141b06090102061605301006 66
    0x200c0b209000c01c1e2030402c600070200350302e00c800010000245100d500d00d034501800c05000303403155814240c1c0100800313090220311101c03d441b101c11150028141d101c2404140d22796500c0b4002040f100c0301e01e41e800700d95074182d1040a0f1811407110071280c4202c00c045800d158a0b40d004c004034250b41d20340e10b04498089083c10041e12480301a801c444e801171490804801c0c11040000c3c6181200029601c45c1c03912012110204c0307181c06040e9119500072140000c00f0f4a161044903903079002000100010700d8131846599820480706158012182540c44500420151409000c000024000b0301030910041d240b84180030b888030180d00405880030b81c1d8a000c01c003441494907240202651010041c0f1108181ca101da40e038803002c5103039200740340e01c1584468120b418180d0550303a502d07806800070881030321400200c4860a464031410410044107112a03259a040c80a4680b540d880040740d204824400000780c0000080050040389640400c01d800c0042e01d5004490305500111202d104c00301c1d100350441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 440149163 1250 440147913 440147923
    0x190f030603080c01060e100f1206180f0c05011704022b0620090d02100e130b28141302040e0a0c0801060207051207030602040b03070905040b09040212 66
    0x10103002d03100041041c1c2c070121030540c001c00503582080e010800c6a607030140039602d0a10a8083d00d15405884c120801007407029400a194130303480360801103048100300c0c050941d4052030180640b8000c002c051000c0074405032019007800b41400f80382411a400908150003088600980007d00500000401c407054404100804070004104a0b04041c09205030804801810149905410344020350ba540b148807126a411664580c0000c0c00991001c0015020008a5a84c2c40344600c1401345800205d4074564800009104014480d10001250089403090101000900e4403200b01e142032943c030880005021a212001c8401c0707116182c109844100109040781c00c4400b0507042c01c0e00214020508540040c800c0c2d101d101c2c50074041042520580c02201c491320280700307800c0540c0102100340313310309052a1508811004004840080741e50340c0c0c8010807030380503510030101c0c1a808018000115805480300d07005141c2150213101000c1c0d0329000501604014200078406d0080c01a58807101c0e4080c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 440150413 1250 440149163 440149169
    0x60606040b07110319060b030705010c030e01031d0a0308060d050a170c0a0c030b061801061103070c06030b0108092407020a02100206160201060e040215040b130e01080102190f0306 79
    0x45c0c0fa049400054001c00205150108807038080c2042201441420000b81d074400f1140160b550221283c060346056803030380700402c202c43c101030f21451080108009080d10300c0c03521006800400b803070f1145c3e04004200002c0908400c1c494003410441e02c001c6000003d10a0106070000c45207803245041004d1200c0a01c2080d070b401039a8002c410020f01842121003110b8200c82c040c20102c3c0c40c075900c06040040c0d03241d044050f408032000101c0113002c1e40e4031131a01034400304810b4088902d4076415446d82e80c0d0071411940403c0019031152240003240d40d1140c0c01d0f540081d046002050250b41c1c0207003149503454001d040c054040b03503000004400c24803c014907001250040d01b040e402e404000002900c1d03013011101c0b400d500411b001c10b100864170510401c01100e44a205101564465500b040340c005104011400310300c40500000c1009900c580080100004007e504000c0a10b491116060030748140d01000039170f441409420603c00407506003d1424a03035181c60000d0b40c8000d0f200750014603c0c4e070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 440151663 1250 440150413 440150419
    0x6200315010c120315120b010f0b090d03030b0303090402030f0a110c0703030c020d060f0501030308090a1e020103061802130b0c1e030d0f0f060e01061407080415020a020a08060606040b0711 83
    0xca801b01f0301c0f0400c028681070701c20740c011074000c10352142e414006070b21504440507009003034406944040780c440c2d0b003d80400c003c024150b078034107034400e000603040c0c0c0c02c140e032441c0a14043c0d80c18030607450300d035120703581105040c1845d103402d040204a070141c80f014148009070510403149120740840d0b8561200e04816640910100094428145108003c0001340411000308148001140c181c110028240e104640c2c010035222111241d2780250050b1446107000324141a100c800228201003414820b09400c98031620050b00c0d0b03000e40c9980c0b1a80c1d8040c1e445003070328034010000d80480d41c90204441c1050007102e00034608402088a03102d2651040024810a051a01740703844400c40301500140d0241700114018000952210042e000004080c49043c01244212084101001c203c41c060003006014900b20b03400c055036200100b0040d4541401000140c005103400740c21440d00841e0200901310490081c1035514200012643c203114078043c80200c06d0000c108070042140199610700030b80d0001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 440152913 1250 440151663 440151689
    0x405030d240602030705160f18020d0e1b040c05370c06050c0a0c120507060908120a0b010203180d020d031701090509060f0406200315010c120315 64
    0x1030b54000b0344036041644200d84500454040511000c1c0c3c40c450303641610800814048010314203d03508104d04080b080e110a041e401348000000c01400340318400440b4079000c0070740701c891100f0248000c0101c4c0e0014840c400c6241040c40c1c8040350f80102a20403644070035088101c080c2200c0d001c0740e0544a58480b074203600101480d04001658403401022081f842010309003c40c0c1c41c0c03910010801e00403285114002460080c003040440e60340031380c000c4c010441d81805803030490951a01e100740d40d45401f0a03100f200000400404200900502e136510020250040100046a00000b52640710b0814540c80b2040c00030450600c0781e41c0c44020805a95000742600a400c0c0d503481c0281428505100d0b0003002c201c48070000944120074041c0d07a01c00e0704000060107455036505680081c42001400a45449039203084052910510a400c0002034400c208050f40b24034010502c0080c61a403c00514100b2900fa02214001074544680c202a0400c0d801d000c19900c0107150607a04100150b4801402d90f800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 440154163 1250 440152913 440152919
    0x3161107030302010c091403030901050a05040f0b0a0806120706080907081e0c1210020f090907080a0e01140f150a0306020c0c060414040e0f01090507050f090405030d24 74
    0x541c4076007039a8882d0384030001587d94607417452007210150f4a1140d055001040105a81e62280d002070011300740908080c0d060603124180701221241719041150f824030300280200080d500030b0040d039440708088903045000000ca008058850000340314502c240000381c40405c45004091090f42e01805400080354101c092500900c14580650003446400d405800303030003001802e06003c0722035001e00200042031504d045000c100020751007020a109080010b21003800a55205401103020f040036070f03903003030170b9050140c215011150180c0f01085203a161580381c4122114110300c007503012590300070340b0100369a262803826001d000740303200950001c42c200b40482001a50b40c040c0807030100c0700f81112403003642c2d841440316900c200d0040848100840c58003014501e8190002e8880446400507584500c83e0802018203580006100322100d80103504c00344070f1070501455004021a08413003000c090b00f00b0751103854803441000c120004281d21112000d174081c01c00b00e520030707141500540100200350b17 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 440155413 1250 440154163 440154167
    0x213180309031e030207120c0b0a0c0b0121020105180d050d1d010816020708011d011808070b041103030a1707030605060f070c05040911120303070203031611070303 72
    0x3800d000403500c00385503043e6241c4003041a0b40c0e0006031503140e0010010503081503032458000305108021900d00d892905c0210f14012010090f00399410316440780400c11140e440e10411541050708100c400508420314030520040c40004024966020f00340340c0da9401c034000002005000e01301603a80c120164844038010800001054000c0324400d40c0c03400e44008041203508450500001c11600050126020840f610b61607540b160074100180100c9030140c1c2c0e114104c9080d138401c5807401014400b1580ba0703c03400310080c00f030041e810ba094160001c0c02a100d94980b1000d01502c4409003650070020005000c201e0f0400f210050810000c08030382d00d170506058001c0000d4142d0140e0b000300152480030030701050290142030191840145118180603008050039201d070402c100a540b444030081c0c0010321611180311301c0c0241400307181d04107440c050303c4050105005c440e21903180c00d40c0c020410001c0203503010064170382042c01e501c503003044080d40d40421115a40f224001802c680a079201c0002010307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 440156663 1250 440155413 440155427
    0xc0f060105010f020c031b0315151314010e09030d09050307030f0e010804080a0e0a0315060f0317070303240602060c0a0503010b09150703050c010b0402030402060702131803 76
    0x5030240c1c0c42502c0581d03d80022622046405043c94050344095205403c401c5000b4158041010150484d50780c5007040c00565001c40c0e0030396405004411140342c14000c0e0424003211800003401500501c0200e20403c610703c1c62480510030710741c1880303050000c106214010b00442d090b480c0c03056414000d41c941400d1154580d4030051045012813400c4c43c00d1801c0501482400c0fa140b80161111816aa21a1580400e50380807072240b604005419a2020705a6940e500b003a0107540130b4030300740203002c980007a80421a00750b504002c2100c81c2210041002400c42054901400120312032a0303183c42c0a482c054010304400403407a1100282940c56a07580a4001c0d640030031a83e00da070855956849144126140c1c2c411400b440c40041d60400c01440080340348401061011000b500d0608582209181c050064110900440000700005540c1c1e2480c1024080c00c0d110a0b0f085504614500340385e4002000c520414030020300582600704004592416940040c1c41a03903e400100540255454010000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 440157913 1250 440156663 440156669
    0x815130507060203270d031d030f060108010c0e1309110409060e0606010306080c01200d110d09060c200a090617030310030f08131d060d0c0501050a050c0f0601 70
    0xb51000d1140760b18a09814101094172003000d07120303e401d0318294400700c4400c0070891903094458892a4030348a01d4808108110486130403001038096035060144803820350b440181d804040003a211303021b42041c0e80b070b4106048140b00e480000240600c407850b00300c04c0f0100d8900f50039403140c5490503203401d00a1640002400740728140650b00c550740c0c0d490041d02110079902030f8079003550001900c0c554950061042c400e00c445400c4caa83d4003004503c15031458242c89101d0320001546510780404c40c83c3c810005001c40d0146030a11203001030a106000740250202031001e004954180c00c40c100c00008000c810060306070141c11600c6058852144078064052071050008000031601001000540801501d000d20322a2803144e40c020314646172a00040c4450b9010b460f803000c100040004048490200300040c0740a90605040211940314491540741c0100401d01034910000c6038000180100b4135102a210242805a103c5965040444040c010303084201e501307206203000c1c0070740f13400c4c0000c00c0b60407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 440159163 1250 440157913 440157937
    0xb040e0601110a080412020609040603060903110109260d0c02030a12020405060d09020102030f0c010c080105120703150204050616050118051b040207050318090705040815130507060203 81
    0xb00c00400715140e0f9155602c40018003014400c1c030050094000900610325410b00051a00d400d02c000c00f030000301113540719413080340c1c40745d5900c06403010540c02610310721008204500030030110a05498001e0b0240c06aa0b048601422801303000d8206003494041d40c8011f0701c9203d04001d040c03681000a035480c0d11041010303010400c031003880885075115008031002e4590182901c0d0a108500d0303030050140c2800348040b8154081489000300c061054005405c910040710004228004c201102803c0380324181c03c0280690840a4120309404c400100c0740b044a600c02401c0901c6d507c00c04001009004d10b4104681c04640003074400d00100100c6801d90307490f0b00540080004250b180e806e080c0741c3c0000d41d0003e0151304001414104500340c050501c144a1004d0001f501d00441e580e200b50444c0e1042403046020100a02020310303908025048551001103414003502e00740c144101d1a9a40604200303164240c46c1c1000000c48810192017001015503001007244c00782c58582001035202c0d0000011118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 440160413 1250 440159163 440159177
    0x515060102100e0a080f070f150c050a020606191508090c040e0a120207090609090506010603050c0d05060303070f0b0f0a0c0c0201031a030715022a06130b040e0601 72
    0x4065203611032180c00301402c00c000d00711414103a59190300340d0030a0283d11040c01b024084d05011841601000980622590f0ba601300c007601540c22a048035419070410003001820b00c6400e04154002070b545422240c211035040c01080d240d50303050900c4089800c6446041c038a403808050702600003410600074403020082e696040d1901d41072000721011a00d4140080d4441a600c6011507981843ea0002d12180c0c8165456582c0312000c1400751086a401122a1a5900d08803010301400f440013901421480c03409101c0c40c100613000080500079500c0c030203006641e07103001c0756140d1750030011141513a600041c602c590603c203003040803030b0308001c6540c172400405000000c2c80527409071040440800150316030b14085071594004400a020b1440c80000101c100c0407100d00c07545c0c041080d00300802025004a030440380e42c401c02030034001050100e4050f690b008801e030790655500d1141f120b40d90810344465484451007140d02210094907849000c24003000203010036512260000c41e0710411007030326129 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 440161663 1250 440160413 440160433
    0x15080124081504080c030904051006030e0d270e09070302100804080703080a0f0609060612020c0307110112050901140105060a0207140312160611160308060d0515060102 74
    0x541c07642d008004000d2410318000000700081c14800183c00c0307024100088074101001035000c03e04035442030740c0c65142d0080120003000b2443d494000ca1919880c2c080c0544441142c14401600a000c4d000031804e0711166030015003002580003d0f07100c02400444407c03910340c104030b048251a00a940810b1340502e0200d010303c20300601807050703140140e9114400603d400c0710340c1c904491024020f0500c02216441d03020350004800c1500482000c3c021906002425600d012005400c0214a80c00e011000303006101d5060004000300554000c1e0341c010010b442c001e0700341001240e0201c612082e80c00c2c5030346070406100c0c56100c1503108041c030b081813094241107a43c86104008143c010200c1d60001603220741c0b010300c000c0340c2c91000c04400d50005002c8074000d09021590b40301a4010440f607008042c0501c040c2c205104450089420710b00c1d01c151103501e403c115148a152044400c030024040c08409000b20b040f035120302c01d001000980080550381d017105100891120103005480050040c401c2203000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 440162913 1250 440161663 440161679
    0xb0a02010b0915030d020a17030411031e070602010606050d0207030c080301090204080d14090d150c02101a010203030f070e1507150b010917011d06070f08060603040615080124 77
    0xc0d040d554209042c10201c0c4890003c12340306034030041c01195031505200c0c0f42d92154804100049100460071080c5140110380b40c2c0e1070f45070100d164003160440e170600e001049210b401c802200e43c400c10004000da030b1420181020360f04c10124880050043d84000000142e01840780d000d001943c1e4664281c441c1840d554800329050702440f40c140c040700108110341d8103940b800e8098a07003001e109123191001c10680044030380480b684030341000c0260f007010310740c20342e001700380d110b0000300300d0a40752500c02c0030a116000075940d0200030120b0030010915004126040e019826040703200d4002888210545503003d100b45498014103811034100790040000b1030324460f1130041700040d202c1030b502d003500e0704c3c81c0205680880c00500008140355580310301c038000041c1b01e8040da0350304044800081c0741d00c0c28411001010005c07a500d001081041610901031031359104421281c1040e0014000310701c4c0c1c100c0078440480b07601164030965466282c0005c0f2401c180b6a5129144c0c0071200c505051107041d40ca10300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 440164163 1250 440162913 440162923
    0x111e0f060109050402090112170c03210f0403051615061d22081b011d0d050a0f030227130905060109090309032a0b090102070b0a02010b0915030d02 65
    0x254806e43c07186c01802007030080c1d2032800c0d0481c021000804c58081a40010f045940041c1d0072101c0c2c0c1d040020306d042011000c9200904c441100c0c180840589400ca010140300103001d04014100140081d044484000c00000d201120340c000e1600000d103d616450743d801047c4030700c5140c407040100c0c40e01300d5007401900c40c4544540c200107041d9690314814a400c5140103c400012150010705001080c4160020281c07440c0e0521104000500c0300281020110b54640340450007250758032420440300144e0303001c019500042058101000c8003007481c1c1c4140d01a000e0044083c0700041c0300401250844044c20316051018010f5440b042502401070403041503940444001d03049910010041000341c00302d82c0005807140c081d25020707080507240da4608644612400840646415144900e000e103070340d624000000303210341c0104902d0111134000117500c1d00f00b01d00c10704095000104070094103d00030b4201a1003000c00400c907040f03919068200484503644021003c2c000c0c425010081003460000035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 440165413 1250 440164163 440164171
    0x30803100306050a0c1d030307080d0603060b060f041401090302030607020c0f0301020c0a1b0806091b0906012708070906140603010f180609020a0201050a0525111e0f06010905 77
    0x145d285225001051b64880c0c0401242216405200412441000c100800003504c504410004042070061540c288030b01960080304d041031103004204040c400740290b150031203044030300b481c40c0030b8815550800144c900820360313800650503003d0340042144041c2e0200d0350741c221650481e0b161140c1c404d07a1003810308038098000045c05c02c1d4400c666400c0400c062030042d0b5207000c81650f2025842e81c03210002410f00000780c0348610703917034005448103400402440070340f0030039071043c0c500c2110b9141c032500090055659064000c008642d070300c803400d484020a00800b0103003c040080320340503543d6801c0034004051512400144042d00078444000b0b10b0a0000c590480300c042592101b06420289400068000700c3c219001455440100160800f624005040e039640a40c0000a5924200c10307260252440205000c4140b02030103119803070381100c26040c0700c00d1851487e180c03164254000925252680c05402ea00108040510f001261342c0c000076054240c106400a6411690b0798107200f0b801d0755801c0e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 440166663 1250 440165413 440165417
    0x30f060e15100306020f04030206040314060c03040c053a030e04060803040e0c0904050c09010e0d150f06030b040804031a060609060c1f2301051003090507030803100306050a0c 77
    0x30001c1004c20702640190a44086d0782c00d20714500381d50703540041c105500039442154a03220f42c881002415409000140e8405200034000e8514546a80e580e45014218094a8400e850740000a941d4410070b20700380340c00c0d6550000c02c11511005003950700c03801d1400fa401710005030001d02003110b1414540100401c40b0841d10080d401c0508241c0c1180312120000c0075084845004d00006a940d6035501946000b0f50200c10340964403182c60f00010700b1840c2c1c0e0090307030340107408800d81100014040d6030603d202c0b54028000140340d01a01e0854800b40c8100d920180c107580649041c002405081c100030001c0f07901c11010b0380a00602c034540310305840b00403101150310032810f100d03480650a0540c02050560520b2081c0c43d100c08078041d000401004d41840170000954552039181c81d02c00701a40d0382c000b070b030701443c0c1c40302d981d0300d0140051041500500703600f0400d5150074428040010801c422005145d10074940e07a100d00e445801c825840e40c0a210540342076003820f000c15000085446040b07040328060b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 440167913 1250 440166663 440166691
    0x3090c03160e071110020a0306320f0301090501050a14070801050105070201210605010f020307020a12081611011d010c02210f01140105031501140604030f060e15 71
    0x10420750b88460001c018a082c020240d104008001c000d002c0b01640e0030402000503180d8035180d00040403944c00d0741112050103101422a080c428040c0520075030b000c01a20441da00d03d240a011801d45400c0b00102909982020300300b804100064011502c00c114203542084003504a004001e00342d8015203040003c10301035001800b85500c55002070207841e006043c928003405241c1c00103041280d01c0307005140da00341c2e218402c1c8103d40e440780214040ca0a00d200450030301c14281c0006002404a121322a00d01800b1485c5508001500040c0e868040d40305c045220942c92a00341318644041c11812640000d14245d0004600e68414803140298041a540e01e225444668241b005841c50706507280040c0c1c1c1c451f400141c9070b420410032200c4c01c0b10720b0000482c0368030104000315074508042e00708611035040440601c0160102d590824112480351480c0f5400c290f0f01000325142e0310031500302501c40c1013404e00d035101f4000e584d0004510342c1419422101c0c3c043c202c11905032903541c00e441e030700c00c0351401c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 440169163 1250 440167913 440167919
    0x1050109150312140906032401030c050d09110301110414090c040b090102010f060807050a080105060114071e030801050907210906110a08010305070e0103081e090d0803090c0316 78
    0x451552140f1404800d00e180b071a1101c0c400000d00d0783d1f042111804800300d990380201c0c20b812401280d90f90700c01c8003070070240400902501c0180c00b80c003030b0060007410700e030703071600d0341d0080c040451500c0711a504054000c02548500030034640c0580e000e40200c000701004d40550f400c0c207052000340d443c03003070421140e40c0c2d0034107040014000a42d40300c49289811503484040c1403c0900d07540c402d500040c40004001c00c3d25a1425050220056140d80a248182d00d440100a140d98102c003030307180304d8000c01c0c00700340d5140110715018003808682088503010311003c0780502d0405411088060594a0440312208240c0c1c0e01c0701d0403990280c45010324a5002d0322495086200c0819070400001d03103210b260040789514009001c05007580101600400007203020300100140401402900d0140082800f208610b6045403a00c40b0b041c802c01c07030220700002a0b441102c00c541c010350f040d941004002000030740700039040e08100b51642c0081d01d054100c0e00809000e003a0514000030007003e01c0000c0c4040c8000585 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 440170413 1250 440169163 440169167
    0x803030703050618071d010e030a0f1b0602010c1106060f01050d090203030d1b260a0b03060703060f0632071b09232a040801050109150312 61
    0x780c0600300f29000540f080c1c0705442c6110100100b4400c080940e90070052107410822892208221251725060025401c5140510784011034000351803a080902005100340c2c41c03a020640c00540b43c031109102c605000041011541034004c080800201c1d070b164030112440d4240603440e80c205968240d0300c00c500c599440c400d0350154014262010352400b002803140040e40209040d40e002c0055450520790345e000c0c003802d149445400150040320381c505040030706124002042da1001041500d042548082e00081043c84507403c40c0340e50f56005025140313142806040980079218a000b00d00c9203084103500400c02c40d101d200d0000080c42c44100c2140c49050300b12002d144012240140081c0c0d42040081002081400841c485c51001a1800c2c0d0182c500c0c03c4161001c4801003c2001d0000c0718100100d004000400515a003060701443c122004000c410700c8504156800c80300c0d968a00380204000904071019401107040f101c40d18418130103500e00060840500034140001032544501a0718100d180b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 440171663 1250 440170413 440170421
    0xc3a090b0d150506070b010e160210020715060806040b15010504051c02150d050a0212074a1014030a06050d0f0302010f0b060405040b010912050d090f0803030703 71
    0x802e8240c40410544500210300240e110034020382d40c110403817004004580203100050344c0700401c1d040c1881c1c4031041c0030b0001d480c0d400243d0340c00d80140c0c01044440c14000c410716101000720644008101e0250f030f48060741d407134440485007600e03100311607000911105801041d014011105030348641c90b04c0d0a1030200480910080301c0306583d01d45000d486170040e150303900410929107070440d605071240410041002603410081801541354014419060f100d0100c551a68100116040c50313010850f40700d1641a6071000048030b41c85040003040b0444c01c0d808015086d0700355440122607415540019030a12612458500e46070300002c4e4a4031304022071403071100180d6040034104001240d060b94400020700c160410b403100380d4440518401340c0c0c00705602407090044c90740c1c0c1810b081c4002c026041c002917442c011441014000c94a4404101040c0e101d00d0100000c1d04000e810071412807420b007081350fa558954414180401c050704404102d6221520704c0008943e8408001c610b19621254224054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 440172913 1250 440171663 440171681
    0x16030c1b15180801020c0a140c1c0203031e0307090812071407180605130515040209030a14100c080108031903020c0f0606030606010c0b040204020c3a090b0d 69
    0x2811401c80440c0d40a400c1c002480000007080007087c4002c29414828034113101e00c0c82c0309101d07501820111646440d0078241120204000820b424000391a001007821449124010121003c100440242210126024500408882e43c45000590f00c604105a0b5880701f960000c036000014400c5500040a07410303114031103100403042d43c0c00c1a964101701c450726407821084802c400c0e12510144503030305061500c001c8101c3e00300002e109909000168180c550b1410a007a03015640000d01c0c940715403400c0100c00c20340d40d0302a03070106000341103038603403500c80702045004039940d82003004c503400444c80340300030505032494200518604101203403480144c03040e1440c0101415001d015841d100c0000348500b000c0e03070078a00c2c040d001501c0c0010415040c00c07002840300b41031000300e00504000c60202c082480d4040c0e41a43c0c01603949803035045d01d81c0f03424054500070524813920300c0302e01d80c4c44050b850040003203117000f0f040400060700010166440000b0b40541d41d6118014000400b2034061500310140d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 440174163 1250 440172913 440172947
    0x3050a060e010212090d0f0905010c0f030201060b070303020405130504051504061e0c090812090f0409080c0a03120513120c050303070e03070807030c050105030a0216030c1b15 77
    0x1910844019120101c134044815040e650008a03040000315042481100c0503401c40c078080b0209414880080e0900e1200e207405020f00444513040c0c0c04044c000d41c440009000381c160240d4803075903c1e20300100650b1050156501841d842c0300310310b84150b4540151800350354460040c3c114030b1142807103070074406070041c801d60b80d56441d4105040da01c02c4040c4e0013080d58142010204901c00041c40103052a509075100e80000d5220060384104d0051000a0ba20032070b030120b41840c0d5860601001901800b41c14001810081000801c0309500000203090707800b082c0701ea10b8000e69207807600b0400049881c1203030740020a01410498000042c02510140007100140c00c2c500b00c5040b16032250313880d5400032a12100421b05802c203410310b030320701080004003c001040044c24020f05590b6122841165440b8890512101001141c0100c00b1501a584002031400190426500d03e04006010700c0008000ba2034909010849002d61403064140c038050b1400340c0520381c2c12840d845070480c5c0b880501748040074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 440175413 1250 440174163 440174167
    0x2120304170c0c04020d0b0f0909030d0c050f0409021e0403110402030405010f2940090821151c020d0c140105030f0c1c020c0106030303050c0403050a060e0102 70
    0x3c0302d950740303101411603011141800912181e042052044040184020034410b1134100c0030441c04c003a000045820210803c000032039010072041c8152014010201030314903414010a0101c2d042046078050110801d24210059050054244034096407166010207002d80211990414a5003070035001103822510400001400038404a03492046526540c1a00c8903c015000007070500070028101c0d080c43c0d0310031036101c04850f0b1280a00100e002004176006261103041c004811880c04251070a00d07400c5c43c0210612104040e07180c0b15641d940080c4494040c000e40320142d11100a4207403038244030b1400105061413900700c1004104450399103681e0086d010214030910001a1111031403800ba2b030b13214212084c0a50b042010724111060101400c0d03040020500420400580161206400c18400140203540c2c2d07075110f424207103484005d8040b0b01c086000250103204003c0541c4110304881c0241d904010540760140e05031942d2055200180440d8404a00040401d44c9644110303484049100014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 440176663 1250 440175413 440175433
    0x40f05061b060f04230c100306032406060309050a060e010f020c0307110607210e1f12060513050c040e0c0714010b09010308031003080d0c02120304170c 67
    0x142c0761140403515880415000010304c810000e141c1c65030b24005030b41d00f440c8040c514500a041d41d44807001d050081c030920071003081086c118007a07440780b405150001c1d9945124035500307251154201420a004406074500b040c0064101e1191090049007680000a411040d010380c0350500a4480c180c140190740d583d8030100381e22003c2501c0207201101c030800107136840d01560300b46174200d4400c4e081c106008100800103000052100034101d2580c410002540461081c101802c50340e110181aa9035007103000342c03081905181e41c0d8049014803490f04d55503505518a80001002a624103104094201c800420710f101c2074411904820351202d91034086078203255803181c202c0010310302034580f940d80d5900060090306000350080b41d40c0001d007050000340000424100401c4400c03a05110160001d0004000306040705007038002240195000003031181c44462031070401001381844114036015200d00d800e031444121040098902c11904880c9400c80403071b0340c078021021540802c2c1c0681c45800344521034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 440177913 1250 440176663 440176717
    0x1b070e040201030207060b4207020603130812060f030d1e05090402040b03010807211101030e0a0308011805041a070c050a030c0614040506150f1f0212040f0506 70
    0x1101040c00404c2c1c161603101d0649110201c80030308008e03030100440701000c4c0011002d600d2022100761550541740640e40ba03540c80d42500900c802c00138020500039001400103111618803d81da030280504031000c00c5000c2e9440c040654030b01d00c06c10600302095080e040144460107603400c1c070300005031a00b80741d80303000450300001c1c081382c1c0290085154040080b0051003403172802c11000d00036100c03510282c0d07100350740303030900d19105104600300401c100500e20310310845900c00e0b0031900d030240c0c1900c100c1d10940110f11340903100800c01d000d110300707000b5500d2132040c2c40001401031b2405035405c07061404122108c0b403c0c200f22203100400410500c00300d5a824000141c3c1040307000b00060082d41c900d6903070a224a0800103842e04604218089401c0205100104001140d204d4004582e07504141001400a0208812203003908840f0b61200c41480041210181c540307130010381520030390a94100085102449015000e103004900c92a809828203000030b0410070010b003041c90642c00201119280340030300f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 440179163 1250 440177913 440177929
    0x30c030b061612050f0f0306040b04140f33031911040501120218040201030f0e0705030c040c08040321182102151f0303051b070e040201030207060b 65
    0x141e00302407041d58280b1014440c10381c4035210030b24002c0ca08107103069899000203201e80034020041c40200070020214045589039402006050400b41090064101c21f0031840242c2c80300710b40c0b021002d505400041c13440444c03c1542c455170350b24aa12180494418200140550081c003039541d0544144101d81070403d10400901d4162885030b048500c00141d01014082078410691080c0980c480f800e40c541d0050755002021484906044100081c9a8a500040300075014607480f8200f43c0740741200c00c0c0b40340500480e00d54192181a82102c2400040c00f0500003118080c41d40f2100040d0114040307030010b4810341a1028aa40c0c10603014801c001954401d0201d41c0b6001e41840307a00c841113507040422039030003401c4035015010784011070440c0e9108070103034031100480c00000040c1502c03400144408500b03c00c0310342c0d403501c00d20582034a58880c5000f070300b6075100c076450910840c2c03007891640c001d00380055500203490840c1580b14103912141c4c019806508642e5003103908070745036004025540ca903804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 440180413 1250 440179163 440179177
    0x20a0504050903041a0a090e0901060308040f080105010b07050a0f1415070e180a110409060e040b0c0f040e1306092604080a02100216031b09050610030c030b06 70
    0x1000e5030b034136480d005c03482e021101c10418021790440d050143d412000e81200280d02150356400062025a880c2d08400303004242c40c0e0801001d100c40880c001c1340d08040c28003004140d4080d100200b080d49d80300c440350b07507081c010b2031001042079100c43ca40c00001010b00301c13205d4100f4441c44140901000c0b0300401410441d202c441005294001c40401000c1980038480996640c41a62201d900c20503842c004c05080400405004069071201030020300c40d126079007220014800d203041084541e48581703c202c0301b0b60080e20141d425443c40000314000000c4c04044515060000c80703400d191501c2c1c21174490042400618107400d8004104540c0046500c0c0e008400b0003a208540044091a24048805a03001812070311104010184414030a0328000104c107101d440d0101e51f0142116034400c4220300d80302200801401d072509010000041120a0010024045481c012105015140c1c5810400c0b42c0d401ca811941c001d0403485441d015a02960010380441d80b9480c0102d05018800702050103a40000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 440181663 1250 440180413 440180431
    0x218280902121e07080603070506030103080a080105011e0f03110703031b0c0507171f0504020f0d1a06031006061205070804171305330421020a050405 66
    0x901041c14850700a00143d0000d1150941e8600440e00c541400b100c0500502c084180301c2c0d00c0c0c0c0130800319542008010010b05006240c541d1701d60312440c00100d66000001c1e04000f082161002280030360240c084c95880c0c0700c02400c0304a4105040380d003207890b125110283c10500d40e0381c440c0f60070300000c040700401ca0b89000c4c0d140416000704c403104080395000e200102c2020080c0350002d2400040c00480c403001268403a040d03d4440d54940364816080c403070000c0074115603400d80206049070100d15080b052203a40200c2d03102c0220000300d81448150156400001c2c003d85903420300102c409003408903940c11482c003504480003000c01000c01c008a41c80c6400400c00b2030145c1c0701d441040c48a43c050382da80440c40d03140c00e00c07090505070f8500f4007042e00640040029617011854a80403084000424014400180440d0708140c4101e403c00b8591313009c0c0d0300c42049481100c110002800e8480481d4200e46610b183c0310003840c00c080c0503040b40b440142080340d115908400c001030607a6036001d214002ca000d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 440182913 1250 440181663 440181667
    0x609020706020c1204080706030506030f151e070f08040609120309020a08121b0f12040509090610090c0c020d110a080106050d02090403110d02060702010c02010218280902 75
    0x844200784c0382803142c0003a100c2c082402c000601190b0400700b010b404030303000d40c1008180c0c1c3d159000024100303103a41c084030926106803a1008044172102d0305442c001d040140503800c5402143ca060350303e500e012502c403c08101d0102c1490042d0b03100f121150b50240c0101000070740c1071440e0b40e803c030846240901c0440000d03203682a940c15460940c44400c01044680c0041030310307048841c2414014050303d1243d01c022052682103c00d00f45060108100008946040e81c1186010003840080c90704503006840c020150140010341d5000d0028106020392100c0d003070981075074500f90350500542400d80b4404104a014030b8100c0060701d4000d244094148189299100c0c2710312101844040038140e4444041603040c034008114a4481c8480380c80125015204007400d0750700c1e820160b50080540d54980e4040c403688100c0520640d010503218007d0800368020302c905079400c80e049080c1d000d10a4064623084003100300904915100808881c2c2c9031441d01c0b0030340c05002050b42d002c05d802407507002025003500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 440184163 1250 440182913 440182927
    0x31602031e0c0a0f0810020307141309110c060129040b030103140601061d061b060403030b0f06030c0a1416050106060503040f0b060109150c021801032004060902070602 74
    0x3d405000081d16442d9160820b0b5443c080d03286075604d9001c0814883d182c7d0000208040c584a51107c00720320300444c0034580c1d103001030714015041102e20320a40b50b038103160850400a24007101c04440b0312680400050002b0307403d048030f005900101110300080c01d10b04550300004180d201025100401150354241c0e125807450500c1010000202c11150061300b0400041c0300164012074402c003000c03200c0e900088282085d00100e84e00703110780070a104c8440c000100c0160354110029a1a1285100307079418003034201c0344018011035040b9a0026580010284001201440c01d240503004030291803821110400d0702c1c201545560f4410001c0c484030840e0810002e05000090081600510b000e01d4001e1540c43c1ca0740307071181103140764440200100e081802060840c1e00c40d00070b082c0980b0a8810800f000710500f0700160050002e40000c9010700100650b01d1144000e002105040340d4002070100800c00e240b0707028100c4200e0140816030b12690700d00011411440364070140030b60768412580180e40381d00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 440185413 1250 440184163 440184169
    0x924091204030506011a13090902120c010203091201090209070c0501050709050901090c02070305030a03092108040f170310081006050f040f0f110316030b0102031602031e0c 76
    0x625440c030349401403001c00007000028000144581110500000100c440d144062504841d100310600b030754041800c0c500206241855600c1316094510031605652105100780030345413910280c3c042c0c20f025030014804811141003055034500e01c082075000002d45184a580001c803080804c0e00c00e400000d00704004541040002d2160707540002c46401d0070650145040002160185c050240951058031010440c0381d080c000c0251601440c3e100d0141c03915032100c018001c004001e201000d40c0c02c07849280414000e9041c1140500300f81c0229036510003542d41302d856110002180307280807185c41400024240015031140d000c0d5000e05820030142c1640b40c50159007030310744a580d00250383d4580c5840d404202551b581024078464071026a404210000c40c00412001004440c1e0840019424a21703c94140c0700c2c0c950045120340c0c15484103d0790780160400031400c441604503040d01581c02001000f0406c0740701260441001c1c4000c045174010742c0b0040700c02440c80c02c1d2080007500c82c0d00c0004102040d103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 440186663 1250 440185413 440185423
    0x702010210090c0308070f05121309060510140705030c0c090708090d031a06070f060e06281b020a0209060f1503070c14060703060509060f09092409 65
    0x898100300b44075981080d1141e04040106100040048130300050010404c001000c82d12241c0b0b03040320035034481540782101c0040a9004900b030744e60780c5104070400b041c91031191168500790b4030082e05c06019030002c9181611170706c0d505440090181c10501c6281c002074010001080d0700b68550001d016040710701018024210800f038160070138408282d04010590900082d100c402011030701c0e0101d03200d003050000d58084103021b02d9003904131600140400511202d05000e1004900c00c6004000e86020240413503242c43c404c2d0b550024455039610400440b40d1020f0401405014a0b00b0001e030041c0b095042d9401d01c4e02c01c0400e140940c024054035030a501c8c081c2c1380c00d940500306075001503110242800013009082c0754009021058000300120310168400c003141803d07144c0c840202c1d0001440202c0960340c0342130031514080042d080c400045082c0c24800042401140c024024108100e0041d0070005010070040150303c0c144204040c042071204c40c454402c40d5054104907501e818101400054145 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 440187913 1250 440186663 440186683
    0x3061e0d051f050103210e031e0601060203090102070b070222050912030603030a1206080d0c140d05090103021e0f0a17040305090d11040f0e16050102060a0f0204030212010207020102 80
    0x140c2d18003030040000c541111200100340c00359806c55402c000c80c100f000d070740000d4103039041501031040d0140d045100303202025903c0388d610382c8021541036aa0b81d06040b642c9110b0000340c6401604558401c110032200c210140c0740b00d03480101800c0c220080e002c842c0340034440c20305090490325103c00070712a50100501c05810180f070307081e840500e5803030503030b020a13501d02c2403026960811200c05a052400501940043c010b480d030981503801800b8004001441c442100000343c458030400020f0651a00001600600110703942d19810700380518400150002d4101d044411008103a611400445000c101c009041c2c00001c00081c5444120f074080050440d1000b19014001c2a003c8041c8000b198210041c3e40001104131222002c10881c0d10341f00101c0802210080c1e002070824008001001c803d4000f0400c0021500841e444500e1100c1d881d0318000c4540308560240e0040000b060001c4001d4008a1005d00308042c058a4683e5130340c0070814114410700c1c504050307503010410748210340c0d041c0410b54070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440189163 1250 440187913 440187973
    0x120041e03170d11070f1209030c0302060f0904050a0f0e0705061209030706050a0605100f08070305070c0f0b0105010206011e06030902011106040b010305160b03061e0d05 75
    0x35908507a900c0c80b4590340c20550201500001c2105584000c140e085501c000400b0400291219034074505082d060203400790840d004080080079141252141e261003003102d400194441100740f9503000d0026690114603a4801c9010800400b01da9840c0d80c0600780c061021020000b9440302110b006100700c0d0002100a5407030340141c2c00400c203d40c5d801056903030303425070300211101503111014041e00d50310518a0080016082400b0000c00107003da02100840d0400d0311018162014140e0440c1e0350510000200007007003c01d0701054010344a50700c00b542c410030600b0048503420b142d84035017908602140c01203d800c042d001c0140020f5a0501c002801411060143c04040c0b40d03103140b0018504a5005980400d65200d40140a680c802c040079100c1c192100c0c2680c81500707180c140042540024001502c0e6071041c1e0790507000184400d00b44100b1540340d84841403c40d02c9500403c111203000b401c80086140050030780441e180e68075103207907460b18400d02c001e000c028080d40342c41005400c28089042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 440190413 1250 440189163 440189219
    0xf070302090105071b03020306040f02090114030d200a0c0306062715030c1502010507110714030304050315070201051303050703050717040b0703020c0603010f1205012004 75
    0xe5a0343c000c01500d200b84d6001800100421040c4000f01e6036a00e5644082c2d80b5220310030a105c00d0000d10040d09190500a80b4480321a0380c8850f0541c101c0c0061107070107078240c0c0c0580460101103110303072a05144199030204841c0f41c6880c0b51f080070700c0c080344407070262480042c03000104104007092042c10020a0a0704ca00f02541207417030316071310020b00d03c1036440700820307150100d922852803030103000400303150322503a4044110344800200054014018610000d5031030000030840d454003407444e00c0345090504e00141001d50506181050030840041443d415200c10702c404241940e081c0700b10703a892800703200e0030701540c40d01540007400e584000d00001c045290034201e03000400d50150484407002e406040050352041c40f4a0806043d420750000c140c50040046404101505848014094540aa400c03a0403101d405c04c104201403000384208591011220ba0030000d41c083c00c100c600f4007500030000082d0042080d50482c00418085410034060342c0700003010f0025402c1001c80100d140300c80e0702400c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 440191663 1250 440190413 440190427
    0x60f0909060405040507060f022b02010e0105010f050607050106050d12021b030a1e061a041103090715180e060a0801091a131a0609060306130615031a0f070302 70
    0x6501d40e1b14500514041281072200490700c00e008101c4403100111a00c66540c0024203001507030301806801e0380c2c010041d400c0402e42030b4205070500070141a03510402d4240e184600e010108203071644200c00c1220b1a549525000804c2d542c0c842803044000c0c040c03985201c0c0d40b1a01100241401d00c80c005400a461403101c118005d9140040c804c8004d42c4c2c84401071714007428942d482c0c03200550350740004055a0a05154103158030484000e00380b1810700b51002d20990103a146008410301085483d040316501c071035010006e826800d50316590010301401e24105920b020001c07100402d440b90030107901500030701d060240d05e00b0a0b01041c0c0081c184031000b0441080246c0d107401c1c0300c140c81004600049206408188011032205998030800d40c841174280e98140701d18001c3c0c07070f01d440898625100300e0102d400030342d0a00380072400520907a40c0c040d00401010a07039a44200a01c1e44400b04601164060000b0000a000c0b02c1080e8518090b810002c0c41d51410341c90072038103600010a14001c06006105e11 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 440192913 1250 440191663 440191673
    0x12402030414040b120f01140115120b0a0f030803100b0f0304030309030207080a050f0607030902010906080c07060207050a0512090a0314030f12090706090501140315060f090906040504 81
    0x7189992500300c40204460b0f003440002490105c074a50300000740d00915000401d1054154480d04946511800114250b0b9031100307250010700b051329603c030100d1b81c1504d5019a00741d00380d104000c0200004c0030324038000d440c0c80180030303a0b00c0c8580048680002c000240060344041856190090804009440c41c0240d1811041e2150002500080916480d1144e4004040c004d004600c0034117138000889920090340e0402c04e07543e428600c8103e029007e0800401e608510070b0145c1440d20343c0617180e4020030b91902c50100c403426001820420340490030302c002e80000f04640024184240200010103011065050080c245078600c0740c81c8601302c100b080544542d131107030488501181d030054250110103c0d20041c5c14103511407000c10611491000030221000d03003404c41c290340680c0d1980d084600c2240ca90030292104540c601410b0301086021401c801c0c56400e8500441e400300010020b60410b0588001141598204000450100d100802c040c00981042101d01d503001008490520050510752030f5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 440194163 1250 440192913 440192939
    0x1091a0112110d02041b0f110c010207061416060911041a041814330f04020d0c060207051503151908060c1b2e0e060124020304 56
    0x64500030380602920740d056594039440b00201606c5081408940807109100a00102e54904800003150101c005807489050010300149007503810b80090040c10306001056074101c022142c18200c405d42005521441c84401c19500c244900c02e02010801c0101494484000c01a10603100e001d20310388400c1205c200047c07601d42e41100d20640c0c00080394500c03000d6a8040d0604030401802c510a1440141c1c4048000544140503c2052781e814840c0c41849041c5c01e8000d8038048a5170642040d1404211040041c00c50f031604948000c0c040410140280d82740c281e203002c164012005030300402c00400841c2805460056802200360102d0328524081f0f01a504076600b00341054001c01c450004005031920031783c141009407943c00c1c2241c81038a820341225009a00080301001da600300032042c3c0519000000d4214015080202100e00c01201a089002c41d01d00b0035000f10012078440340040034400d000d100c0310740a405940c0a1164240c003034021a06280303103501403041107500802c01002160320320f0326 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 440195413 1250 440194163 440194193
    0x108190204020a020c0904080702100809031215040e1c0908060c0901090b0301150315081504150c08060f0d080307080408040902030f160212090108041401091a0112 72
    0x107030040c0c4038024800101d14110510240e01e070807140d05c0050100b4010041c0150440e42d208441404900c00b01d00700403100d0b603000b5100c40d14154414000d4811403078409017031940c40b0140080c044074151280000a040d54511300c54404a50040356082c0840b05a030a1410401886820a10542c5190071a15036880c0d90040800400e400007007440c00c402e0b031046d420340c0010004810400d4481d611840039091940035003110b0700210b450034104001030820400d4080481d442c04024195080d000c200442101200501c00c40f1320b418141c480e45200c5619204840300c452941da40c4100c0e1b1b1500c902407182240d00030728028440d0101000410000d102101281d9120314246000c020680751450004814022a00890401400031081240c0c2e09081c14002d0f1082c024005010100d07802c4071f01c243e071079103a001c010501500c4c04200b1410154004ea80d0550814400c28442c008010250416400c440031101e044880c0c15124004070201901d04503d940980305100d0303240a0414241d88080e1a560440c0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 440196663 1250 440195413 440195419
    0x8090c100f1404050303040303050315011e110a021f08011e05120f150613061a0c0c0a060f080f070207060c110a06112107031107030f1a01081902 64
    0x700002e070482c0142e007600c0080401804890f140d640343d20340030b0005e80040302c4883d800c0d5190030001625603c07610840c0c405200806401c0701001c490320f404c4612070340c4884141030900c21414107000503140c10069480402441c070a03e05101000c40c00104030038010380c449007601c480a102c02103103401045030001126802c44a0404100725480811306140b4110040c40481c0101701c0741e01111200c030805503104520890368450504982c1a5402c102c8070382d4080d18211030040b282001115031440010b000c0d90341d1035022111010b2289000801d003100a4000c0800a05245492000c5a402c1401141c00400e0307962243c0f82442d00b4180256500042d10072030080103030302c0c50040300341b1602845920f010103007d08200b482c5a02c03000080c041c501d0b85c00704200144100c940e484008440b801c174540e904240b018219240c4140c03601d007280d030280140c0700c5250b507019005000001548a108951003603218850181111506420340e18409105030301c144d4841e04251400303001c001c19401c8403090750f9030407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 440197913 1250 440196663 440196677
    0x1008090c09040c052707110a1b05090604150510030b031002040e0906040b040b07050d020c0a03020c030f03040b0d110a02010e011a1f14040f080c040b011e0507060c08090c100f 77
    0x9041f10324a01803441c100074090321801030414114040701040d40d42039800940352640103450314024070048907414160581e5140903000300340b28602c0c6c2101401d4003840c2904e0007061504241000038100b0b054060403071201540068108400c15000c45042d80c80311143c0050316181c603040e2105002c139000204000d00003400310300001c0110f4003417026150b04900c1c80305d045440c1d881c00903400d540ca0b0111001074000d403086801190003850001020031219081070003940c2814030300120100150003ca1107021016280c0d2400c0e0b4a40380500054250070000790b00124603613902c054a5030854405c2ca50f9138048400c1b06510300c4090311803d482c810a10041034132104c1d070081a0600311a440304a0f1000544003500140004003c10035501c01c105a407804000d40f25102c0b42e41d02004201c40c4001459404580c81ba01c8184068004500100142c143d40c20708a14000c030325a103074811204080d9000011500b400d040c0b040f040410440010310308410703074040c030030b060300d00101504550646203170360104545 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 440199163 1250 440197913 440197937
    0x70308030a420609060e040e010e03030a060b181e030105150316050904080a0908030d0524060f0702241b07051008090c09040c052707 59
    0x16601c01000c0c45018800c1d46481d004009060724140303a029544010802c58415003440036400d01640c030101c400d43c0d10707481d4074070786040400d07101c041260203115881540c508410310029020b0280340c6502603010051503aa01e0502000b000300c64207900120000031003800a5641e0303001100740401c004004988d80000754150030804016a08800311007505542403000b4410001c41d462403030584203c044060b00c0443ca200441002e6000e00c0c0c1c490543d0001e144030100740407950381002844081032a15155044548540c015865944040c0b440b01c0300d42d45c1e880c100f10490346042c1c0903000c8003050818945020002c3c5000031200d0190a501c13907018507000a00008643d00d0700704994062051141112001c862002c2c07200741500140c001603040403c040060701030000200320101038800050005103145609001100c01e13140040900800740f10701298042142d0f900200c56102d18450a1550411400d00d401d02514a01a0117110b039840003c020016803c542031842551005252804030f03034081c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 440200413 1250 440199163 440199181
    0x90506040b031e0d030203090c0f06040e01120335190608010507090f060c03050310080109060e0c181501050909070e09061f0e0402041d04050118020307030803 70
    0x31032004400e9040c80f500c1541d0203001d09030050015580061000c0c2d4200e00c42c11003040e003c0c0d220032100004950081c40c000d9100e0728084411500e4802d02804550074103403034003441d18941c2000e0300011003071050140c030541003507800400f10609400305810307251810b9410104542d80b6541220719140e10741d101c1c0000e43d80301201c110181482d0801c400500015075140c20441c000e183c03e8401000240b1101b5020071381c16000114034007182c1081e501d098401d400c945084405400c060f00e00e0a40c0c9525500c0040c45d901300740148087e0360300a15000410009450489250000b0300c1441805140420b40500c0001c40c12643c165201c82200040c4c4540f49105004030303468820500d83c0b660000a032000d002c40142d205032100d01d403901c20740750f82c4415224042002404840c0340481000b046c0c08140d0707041341e14070908a04107048000b4001509294540e0264040e0f900c0c20700b00c45103650140002c0105202003402000070030f1a0b8442d145008440c0c680220b91101e11034003019100d4140080403516501c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 440201663 1250 440200413 440200421
    0x9150c0102041e170a0303020d060f180501060f09140406080303010b0d05010e061e010c08030a0c020c04090f0b090a021507120e0102031b030403050d0e0a08010b090109050604 77
    0x505018001c5503190388814a03e802140141c0089204803c02400400c600c40d0030580300c44405061001410708031400e90701200070f90710006071060740f5034444900041904004001d42c01901001019550040b08038191504072941684444200560b10b44c0011a10307410141c0802030f41d2443e80740b6240c100080010402400160740200210320000000203040f01c01c03e000380000801c0701c4000d00c040e9990f44440d0900032000c2d0f62032a44004c444090400c90620581d0600c00102c041c1411000c140064480006540040f122040b195803500100034580b44c1c1440031640200c02200e081041c00c0040c1c1f80c1c810310044400f401485001300c40b000c28507c500820501410940c0104942c0f20155040c2003045150010300b81180d2102c441d04000442c2d5020369a0141c42020681c0158109141c0c0300c10446240740c0101215200e0100b008040080b03441405010030102c059182d084064010400b07100c0246402c0c0c0c00f0a07500c0c0d143c00301500069691003507090445003450b602046c151924800a4018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 440202913 1250 440201663 440201677
    0xf1e09020906120a0c090203040210050408030d0203180708010e0c0d1101051c0c020a02100305070c15021209010204060f0f020703110418060507030f020403110d0f08070506060f150915 81
    0x1c1d00d0340d17000400c403400350001c42c4514802d603081c03129007010b0b00d41500c90b0300417401548100d800c144110500380100354091076120540c44c80410b1035142160034241040c0913030300090319903511001000301401040000d442c1e00038080e6403210a036032061f00d0707110040005c083c080b41013280020340c281c2c0c07507003400da00c1c0c80b18a40100800c1020760315029010b584d919901d0405c90080c062a25035040160081c03241a2140100342c8602c4140c2c00c02d90390703250140d003c03c086020000d80c244011110f800300c000c0b489205203da00001603580b41000006048003400b400c00008101420810b0907400e03601080000460340e11840d60400d000c403510000d03010340004902c0c65064200c52090300148101500070078040c075a5074904001c400d4601000b002680b00d280005007880c007500c00070550500b4550080301207940a61526100310826540d0807034240d0003080141c07140c1c0d0203241800501c0c0b03050012107610440171203840e09138003100170107059517001c0c50805c02d1240020003040800e13008075030308640803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 440204163 1250 440202913 440202923
    0xb0d05041a0108061902033d14041103010810200304030815010e0a03030c0206070c15110312070c02150d0204080106050d170703120f1e09020906120a 66
    0xb50b03100c4070200e50304e10086a140c2c420340c01210b03005020022034400c99018801c00320f60a000040d801c03044042054101000d02014410075501c1610ba0a01182e10300141006664450741d4a04820410040d0740c0c880003e80034210003000100b000000000781011818203031000820b0071110f10888100c5004c07140403a0b002c1e05030010410042540c0040d07003030721650701d041007010800d890000444030070f042d2040c00740e0000044502400800d0051581189507440140704a18100c0c00d55107580c000031a80c0c1c801d01814044504605c44141c006c030f120181125030390002c0d410501039000e10700e0303044000780c151400e121030245914150745950803152816220322000c0c90307940a40004520095003d84102000381d482c242e800b1406241070840c0002c01c80c2c00c08281d005e02c0da41c500c800480d96101a00880502c650285411184105801210b00020f84102d0004000094a201004001400502d12056842d01c0f4a0307500580d11038403c030750000016922259942c180440d401d10746911100c0282c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 440205413 1250 440204163 440204213
    0x3071505092701060e03010c0c0c0501110c03161502010c0e040209010e0405040c06030e12030a022803050403090b09031e01020909040506011523030403090b07060605190b0d0504 78
    0x241e000d0700104001c41480e8203030300030820008c050b141150410551480200f10b1900302e40204072540c172540c119220b02d00031074281c404481480300001d140079001580400078061b50081004031482c04526200031502500003400300310130070903000704010020b00d81c45d403103140c4c04141d0103d40c1c1d00c110b00450300501d002e00300300018202424150070040f02c130b2081070002400c0c010095180b0138003145002107142c41c0c1c1440c9065443e690035240107500003050031089403400b011580d200d4040b803080e106011281da02c001884e4100307030a005104d555540c003e035050031400c0100c0c0c0c0d40e0340c4000a071111142c0e100b0300d0314a05107064002e4180a44960784480d82d0100c1401e0601060100104005040300c2a800c002d0a09184403617050f2507404a40d030ac820092a042c401044c070b40c1102e00e00a5901c90300c00d260050b101c03501c450040c03410b0707005507a09a40c0d50350385000078401410f00110700c1d0030510041141c100b1140c900b01c800c0303040d880341c0d0314441e204640750004203040004455254880401c0d1700c000d84 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 440206663 1250 440205413 440205419
    0x1509090929090d0302040501050708031f120c0909050a02010e04020409020403110a1d0f04020616060212060a05030d120608070b1213020f0d020d0602040b0903071505092701 76
    0x4030302041c192220459401500510700202d4082d10807078045131810b858480c20010241c807010b60640009003070b690402110651800510740a01c0c681c00a051100c603008807094039070424821190301d580000d2800340c60b20706440702080b000110a0200d83d42440c00c07a90300c03c0e10a0108010307001d150301c00801c00c1d001040100803c1300500001440041c159030303031001c656a40c064640c0600a1030507503440f00303000c0b40120300b0140300c0143c07250b80180090803080c82c1880010401e400352032090b40503a001071b808502e8138a00b00c00c1d1454541c1184045903c109405c3c01c0400003900c2d01201801e50003404030140d10980c2071116904107100070410300050b2000150717a142100c00c83d070301205100540d40440000103a9283c054046400465005030030181e0394481d41c0148042c2e031591060036a8422040240000001d40c0c41c001400036213400d41050b0b45030045c0105040ca0085140c0080b05031041041c40d90000645c40b4003a14085031080700c041880401c554050004007101d61203c040702e400c014008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 440207913 1250 440206663 440206733
    0x8071e081218030f0a030b03150112030203070b042d03021e0c1005070b010f0305030418241508090d0f050c030a03020406120506010e06090f0a12020a15090909 70
    0x1810117001e86032000e00c11800780608041c0c40d09d0354011f450459165a00c0148100c070300040030a44294401e004691801406849800300c148040b10f08850741c120180e074150b007072100003c0b00b00720085083c4809200300703207603640a915420781000c018003160082101001c2c002040128100405010303064101c2940801801040c540c4996015039028142d440001011008510084200c0341c1003000b860800e41804d01d00d40d0301154010002c803100d61144258400502640d04ca0032000d0320030680f06a002e840c0001c01452613412810b4a82804215000c0068400000c02d54620204162a0030014181c00e400240d41e207001d031203114043d612001c166a80c02a07050341c010310a46a10b0b4032521084000070000341c0c152401140c4060004842d4850803102d402c08002621a808004210340550410790010078454031442d0b03c60403081c080c42001d0f030154100031250501600c2d0503c2898007031a4002320140420015100d5105c0070f51781e03502110b0034480850301d01194050700c0302c0300b080d03203045e01c44003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 440209163 1250 440207913 440207917
    0xf06050f0c03010f0b09210a02100e010806190b0c2107150911190519120305161a0a06060807090501080603011808071e081218030f 58
    0x3040c4818040d201103804503280d41d0a4034100c0e1040b0803210034850408101d19000d8010041c3c090f003040b213113840e40d00e030a50210f40c1c00c900c40608000411070000e0600400c50000c001e040340405000d41e482c20601142d81c03105000c0e03444641900c1d400c6a401e1081d0701311800d03844984c00440030090105051011200100d805c1c40b118600c0313460594191000141c103d06d5110f40c0030002e0001c0c80010700018a03030b0840d0040c400041c02040c2c00c0c01d81000a4000c81c1e40c61602801c00c90796150390741c03000c0c000343c03a00040802c54900364038101d403c13150400f915a100c54240b1400a0184000800c1c82851295905044013982e5803000300740300c402e51200d8403818001016122821080d042a502081d070f02e01c201540f83c03068407941c2d2a000740303601d0480151160b100240015415540b04d50086081a10308640e1100b801e1003281d2a507a5610319040980c0d40d14140c0d1a1851030701640080c440110708002c0c1aa03240324400344050203980c40701e82c41c072800744012902c02c1c9482d0001003070301d0000001c8040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 440210413 1250 440209163 440209171
    0x910080a051e03120403180f080109050610082a0402160b061e040e010e0d0503040b010e09030307050a05090907051c060e040602090a030605040615060503150105090d0f0605 76
    0x844007514070411101c268481c054248444c5500e0107060000e00860b200d00e00d018104195001c110a40580301c00300d08214043c10780040500d40c0d1142c0c80d110400c1800c2101c640c0c4201000d000104c0ea9003001740c0c203600da8600f034911891840840c90303600d103d50307107171015010101401441155038100b1b05155490054036658241d82d002c0941001035503d06221002440050f0004140040c10240008100040040402001140d0b50382c0d00d0700e0700c0c402130400190003001c0326074a40302d840f85400d01d0a203418070741c1604840340660070360041c090700100000c107480d0441c4541c02e20303540b900f913410380403110341c09a1f10040c0d9010450200f80702e58160000700600d0043d00612690b0f04070745001c1900001c0d194035100340810241804d00007400308106034090600140d00a0560109503070f80d0312100180c50066070181c5005945900c80e40f48686001c80440003081203040481c218a00706070719205031420141c4850512400017500f0015664540514184a07840505640a0381031401c0101c01084122 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 440211663 1250 440210413 440210443
    0xd0906050a0b01110616020c040f200a1d011b03030903030b0612040803060402120708070306090c211808091216120816030509090a11090910080a05 65
    0x180600e82c6944605005060b401c500d00003403009803034040c100b418803c95081114218012100c000f002a80c8034000c90310300101c9403002160b10960189542d00c9180070124010600d0010048580502e4100c00c007407038000c00d40446140844812030042c3d90f580030300d07881941e414070400840402c264059000090311406940c08000016065050158a1180e040b500e400d600c035403000900001d16150046a010030301600144c140303a40745440d4032b103900d020f0300e260020540c03120811000c030b50b051180c80028008001f0a204900b140c54000d400c901600d0020302c0c0000d00f481d0705c044503a405800c0b1481c8a03280e5072510300300022905161010303030030243c80140f1030540120070a400b003c002480040d0144281483e44d0b50301d242c182040600401013004441d0040144800c03000c50f158020746680b614060b485003584e962074102007050001d002400c41059070b1614400100900b08841500c5940b40280d5900c0240d4450954040c004201c1d039000e81040c1c42110000010010041a0120003411203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 440212913 1250 440211663 440211671
    0x6090c0215010518091c170609040804260715180509060d03030e010504031101050a0e0c010c0201090902210a0204060c0f141507020f061006030504080d0906050a 71
    0x955440040784284145039002c0f000081001d032440c00752440b00e030000d01c0c1c081114510003004500825042c0d080c841c0b4400702d600260404002502c1120045e441803040358a40f100d0719055072030f24000d005d980600c00740d080710400402480345051050984020b0f8040490b00c0c0c0075a90025210301c40540110040001c92082200411280c208001c5c02603030401030124207513550b01410300288244184c000c3d400c05460322801802d6400038402d01d030240f0701079500d07100001c0402020909481c1c01825280b60185070219245080c50f010400d00c0c200070091a001c085c01950717000480755903071035800c07021070544000741402c41c101c69808440b110f0503c490100d0200e0380c0f0064007000701d001c2c41c41501c000c85c5486210300001000c44103160203031403040daa00c02c030700304102281e54030b0006170200d4117030001c2011080c0254582c04000e4440407000e468002d201a2500c1c4000d940018002d03c6064241505d5101041c10010004140c078002c03048000104240c1029082c010301070441603944600803450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 440214163 1250 440212913 440212933
    0x1219110303090d110f04140105010c0305131223073b070e06070b040305090d081207091202180903041a071505042609030a05031905190503060f0406090c02 68
    0x14001c051802441f0b0100d58503d07842c28005680d4060b81c072400301d0803c00100710303880124208503440d07001740189042c44800301c5018074280c0d410001002140541c018842102c9141d0500016180306441443d07034101860260881c8480c00c08860404001140c2c1d00e5510b070358000741100c4201c6104001955902c18031031030075402c0c049540710b045005000c00500500003800300b80a0002046071a41c0030740b12480c03031900354595501c1500300c8001c0c100c400c00400240841e071503121071a035000e0054a5505400700d001a400070f0200078515400a004030311040c00500c2c0f0782c1050090350014400e00c505030b02d0a840c1400ba1551f01c1c1d2006070125240800e034141c12158104502c01e15210f250301c00201d10b01040341c103914201010715050240703900641049140943d44091024030b0100c0c2c4600f00442c0c55806505501c2c275042007581401003000020310900316080c0364042480031480303581c04c0075943c80d220140820046e006040b00c040c0c0050810b0800244103055a0020510009039426201c04c404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 440215413 1250 440214163 440214169
    0x30c072304020a120b0117070c020109051504031b03061d010c03140103030e0a081009020306090a080906030a09170307030c080106050a18231219110303090d110f 71
    0x2803c0360f00c1000500f5603000d1180d000c4144d004125003a814104540b2a00755412200c1c20480111002000942e65007518021941c0015415010744400c441c5031080c5001d208075100d00c0d014502c00a000c2c5e40384801c007008171000b003082e214051b6401c040c050003082d080904881c000b00440c80d00b980150310700070610b04902d20a11900c0143c0021a079490540d034a5920100c1d1440b0030008469840414100d000071501010400642e640e124a5000704519995004040c2052030081100440760801040307480007855200c00ca41c1d030b41e4000c0b02c1c481e46a03151403d021000f81030000004180317560310f46002a00c4400940610311504542d0741c1400307465402942140d001000707101d00c2020900c2480541207003070044c81c16004020302d00400011443c2d0799100c104661490780e61140c6081d20100840c021420407002c2c05035060010310051030013030505505110110301c420405001090082d2940c2e41a6070184112080000022710001c50790a031800c10256540141d51203a01c11141c2041d061000c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 440216663 1250 440215413 440215417
    0x10522050a0b0c0c060702161406090d0507090509100c030c170a0f020313261c020d020712030501060207050102060a0b0102030705071202011b120f02030c07230402 72
    0x2990290203415140030a41ea51900c0580141c005081c2400901c00349800080801c060f601c9001141e000b00916058541a01c00c3c8000d6900722120140000c40c4000e0b1030b071160400c0329800d102c190b0f14005034055508146d402d0180d10b8000c6c800c020b060509000c11000b002440d07194402103000f00308100c5c068811b041e0102c8011501200c081403001c5600c0b868030002c03203030a43c2e00c0703504d080d07010503070b1110452414102e030302c1100c507045254100d070080814000a82c5d6052400301c1041004405050051307803801107405031000f48500d48034800c1210002d0700b5541c058a1039803035200030a644414843c030384541645144408040042e15202c000200316100003100c0d001c4a4041c0c000d859980c4a4001c0000542040d82c20300c1d05501c0b0070003c440000340c0401c034000040c01401c51150950002c4d1000510708038845070500402080355030310801040c4500546508407180b030030110400008641c00f40d0850188551152032402004030020b28030050740d2190141c94860b034955204110500c0c1040101c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 440217913 1250 440216663 440216731
    0x302030405270f0c1308210324030a060204120204200708160c030f060c020a08091207090f060503010501330912060e06091c0309060603020306090105 66
    0x10140c0000c1400380e02c840d00d6454100103900440c51500d45c0c07200901d525602d69500250b00e6034015207031315081ca41c004400c000254a10310740103117035050850f82581d8118101200070f00110b6540b118603030395902040201c0c200f580c80a03080d5211a962030b80d4058030f00b8012000c3e4081c03410012140c1007421101500c422482d0140242824030700f45880c0d5124540002c2081090f020409124101141d09204c803240118420b80c0c2c0b070004041c00f0f103080d01c1a42c0f5001c00c15410766000f2152200000c04444c182c550000307083d18600401200142814a401c1c91548182ea0132858800a0301030480307280c202405941d400d0b0005d02c4566a034032a03024501064400910403000c04404008004040e4041e51441d8107541c503064008589035501e8068000c003250b030840d0f11954415502550220501200d0307413000e0441d024010213441641e8144260110000700703020540d450701040b040010326409400a560007404036851351070000c0d125802440b05a40d1100d90350502c1041d50b08030180d01e9100e8401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 440219163 1250 440217913 440217979
    0x20d1a040f05040803130807021206090d0318030804080d09140c0121020a05040819120f0c14010e070311090606030405030403030c14010f06060807050f30040302030405 74
    0x3440d80c0700150440818100e0001f10ba1881c02001403e02581d40c84404114020b4001c0180003942413004a10303103071103002e1408400f85428259036a5007812401001c0d8040c036010b0900380620350300c41c030300b080d050720404a41c1c03080301e46044017030428828494a01e1100c0210b5808603608115100e005540f004185420b21101014a80389a58151020703006020003102a04110303040540700e400c07190900012880340005d02c0c285e840c4120074007100b00b00c866612255410a400f0303071a6019401456900d6440024081400c000f10304200c52900754001d20a40c41c018080e140b03c3c1e520303880c05418500308425107500c00e9003147c2c0407031102d2424a04480c01164040c0c01140742902d940ea00365240d03281c041058070000d541d48580f4803200028001c00a10003443c1c01c001400300d0502c040074010081c040d0190082100520a000f00d02e030500c0700325030b00c1c203036000806020140c40603410712080605403040e243c01c0c0910f006000801d5000800341050320000c07103c80703900c2c419201c5c5000f0700c0d180c200d03003a030301c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 440220413 1250 440219163 440219167
    0xa0f05060306120703050a0b04060501060c02031b01020f0d05031b0322050c04020403050606091627030c0b030a0c030908030c03131b0306140114060c01020d1a040f050408 75
    0x80c10785041c041c83c00d10701940700181c504680d540d4136424140892030000360f640798440000c005c01c000e114801c5501600d02d0307080c1180708001c0341c2c0120355a0000e26100340e001d0050060090000ea000300003024500c0394150444056121034030b0020126001515846035003031110a5038040741280c882900c0c030600c05041110840c0071034280c002e4003540c500701c05448034054502d10007685d46850005002841c010070050030309081c541d00740085144e00610101400d2025101400001da0000401310344200080320415a03400310502c00b40b01040d00e60004008000300e8400158507a0500060352140c5a5400c0800401003014420360984e42c00036001040800108001004c1c0e410b1740d005035421800b05855400e00e000541d03101c202010900b074034407a6002000100b042040344034040d000c0504064045c4520710b524021440b2542c2200a241a104401c045004009848254161000051400d10030301840c280b01d11059551090800c000d0b0195042102a00b4001400d000d0940910f500c112064 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 440221663 1250 440220413 440220421
    0x9010603020d0b04031e0306050108072102090112140702060112030816051c0204080c011b0809030f07030c0e09010e070501110a08040b0d0605030f030304150912020604020a0f050603 80
    0xa8035a083c010030407030901452442c150f0f0030041d031051840b901d0455440008500b03040100140010400402450407c01003041c10111a11200b45241c501c104484000d6290100100181d44161241c2c0b00324004038a8038076203240c010070003010b4601070a4940c09540c0d590342c0b11620204041d10020001d004200120b01041c1d83d01e10010048080d0341705490220305068200b40486c0c0f40c44420540e10f8026070300450300b8004e501c000c2c00040c40da54001d08083d900016100f1610b228401c1e020341c054050b103400300315030301d6a8a007444040d0b0505448010b460300da0f07883c4d240a040108441c020723500440000310020711030444c141f103503201007d005402480101d1400340110750300100101101c0460250274a842e0006400b50050006014030000c45515008e010801c9003c90b045a404188a030303000760410354606402004032904280c1020506100040603180c6602420700000028800390340b20f012051201d501043c5c55018038402c1700c581110940c0c038210b13800c010040b0700846520040403c049 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 440222913 1250 440221663 440221673
    0x515070b0129091c1b050316051207170a1502250203030d14061e06030f130c0b0702030d0305010503070e040f0507080610060813080c122109010603020d 67
    0x180c200e114004200c18261409035800a0031031300038910488001c0c0c800505201c400800007840300c0905829030041213022070101d0713202c4100e100e80c410700e40030b1b041c00d103d41c01c080034007800290060600030f0141c00c00058081e0b0880d503100c10500095034412742d406484034840d191030084485500c041401c0c140074002c1c0004d802c8002540c0f4008076403502c001c00010381041c03960b004d1100725046505c20200300c0d24284d400d2080c4241d888224031240c4610600440b0f090707481e031050300c3d0064088941e8041c5581d0b00c1e02604c5540c0c1c2240b10280c80724091000024542005200910829100783c06903503200d01448003c2d01500c1080c0207480e410707005100280320b011152500701d580f00c2d0141c11814103081132901c803142004c03401d80041c2400d4112004014007481004a00c10007000b2518140510f4502408580d032500340c0080300901c0c0d80c1000450008482c020815518400c400e000025a10003240c516006c220000362081500c41074503030001018010103200e108110303500904811400000e0340e642c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 440224163 1250 440222913 440222917
    0x40918020a0902090d120917060c07080c01020904021308011404170a0c0218010512070305030a0503041a09010209040b040917090111060103030f09140a05010f05040515070b0129 78
    0x50342d0032a41c40c4200704042801d0400b14600301b40300f074031407104090600200d03220301c9840032480740350350b4000d02c02e100d103080c02c400807075502d56040b0303c016444452444007070740a84a1010b000340c0c0603002240148610009074101411240c0040c003c003d0f128496600c0440082d0488028018100c1c410402c015003844800400e8011043d00d09400480281e6000814201518a092808140034401030000d401d0074103650801d41c1400000701021031031903440c969a4800e105201d402c002004c0007007000c1005010803840500c685540c10720301442c20000c200d000350401c3e01680d00c00c506201801e01301d400d291003010045074005040c08440044010b01402c5070340000e40396410004d0340f0001c100e003d0310512581c1d01a500c00d82e41e40000d05010361000b4807013062504900701081d800c202d00c4000d51b0360304081398100c0c0e10a00704121140c3ca000010741340340c004c0b64800c0303402c201200c0e00c00010581070001403400c40c1c480ca01403a02641c0b18078020b88004400610000c1c0c076811a049100c9175289500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 440225413 1250 440224163 440224177
    0x1e09070509150a200120030a020706020711040e122a06040302060f060a060903020f150307020c130b010c0f0201140c010203010f0b03010b0d1a040f02030412030c0c080c01110f040918020a0902 84
    0x2230301519000d00e03942da0401706e0f40301c0d040588464800b42d015540b549464081d0540482101c0010b241c03031074112060249070b1141d08a669100c00307950500603066808002e220300c02440d0072040d104645403504019450349011215070b03501c402000c000901c5450303c0f480070703c10381d41c0c19a80d85054509550034002c1e0313007803e6a04607910080d0903241243c201a408025407064040c1d5006e007903c4d0030002e01784045070758040c940325900d034240501d00810707980c070501000b60f243d000b0948401401300b500050356400c507201c6510f5045100011028255a01500150b04a51489002308100d59031000440f41c00d00080c003940000f042e04020300100300030540c0209480d400d40e541024490b40000d400101101c54000d1082e41050f0040100300c00e0000082001100300d249060501c00d600c485940107100748000d001c0141802c2003c076060a05100951108005136031b4450030380d9640d00d4030f000030042c0b0740041c460a1482801d090b00d1500a240b0300d80d08411484c3d0140014a0042c20038907924080e40200c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 440226663 1250 440225413 440225431
    0x200a030e0715051905040e0402010e1305090a110321280c0303200405010c03030902040504030819060e0126070b04051e09070509150a20012003 63
    0xc0046400e1100e81052080c0d4540d0f40c03035543c2c4d51409503c0c005824030302c105112050100500c010403c120901d100903a10560901c1c1c02400c1d400c90710005842203d1402456003018980010031240000005d50380b011540108208095031060404141d03695040310740c2c5c0e492034041e20b004000020141400f500030b0546c0c1d05510901c0c0b6220003072540c024901481d201000400c1071056400b415014424110003404070880c0c2101c03881070b415551010302c201c0c444d1504111442104806240c4250300204402d64002c20511070381c03c00d802c0c0100044804d652007241c802100b07000b400410040c1c450b18048070bc10301c0b01d02c21039a02c1d280c0d1015400c4d45d80780045172042c2201596240300c403401c0c0300340c00250043c081c00945650500d400d2200709840c803400d90340800749004112000341c0d16440201d43c420010f00d000d60b500c0500d0400300341d1500c401910341520807000702d140314032107421128041e11410204807010904000303204040c00d03100d5031034044104104600262405900290055a2180e081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 440227913 1250 440226663 440226673
    0x1e040c031a06040f09030e06091305270d02190f15061410080a020906040803040602030307082d0709050d030e030f0105101202010e060705010203070201200a030e 71
    0x98856020369001c5128502600d0380700c204021581c58144a0003012001551040080c00119034016000b8082c02c41001e1050f0004100f01d011030782c0c1d6144506102c00c4100046c841c5092070005001c40107810000c5003000038980c1d40c01c070301002000507100ba01001503801030a030554400621040582c08010658030010343d4a0050b0103d14040a03944100c0790301240025083e2601d24504039001029105a10541041e00310140f415030010a050f003090310603000598491402000072a54031583d8812803583c040440e0005002d9008170185200d0040d076100c0706c420350307240354040c02c164200a4035060f6810829141d01204205041c4013944810b01e410a030341c041da2175400181095480c0d001c00c40010318824100c0c0c3c0c05007410300000303141c6280c500003403055040c40b4070030041680301801010301c001513183c0640c0541e07118661100320448040c04080d590000b504003640030f0b60007225040302660034000c0030043d00895034080c070410348610880038241a00880114058103041d20320340640d11403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 440229163 1250 440227913 440227919
    0x10080c040e0a18050a050705031c030f090209011814060616230a06060b030105031e0a0614090c2b0204110a0f0207060302070507060302032d06181e040c 67
    0xd81c0410303d03040b5004000a00c0400024074285142095603003099001c0c0e004004488a00140d100d803000c401c06540c1004a00c2c075150741d4181000b059046006035101110340d00000701030040c2c5401202911905206000300c59200c0584010310400b614040d4100b101041560042144485290500d0b07128510400c2c03140f2804000c81c00c072740c0c05410700f4041d54002c54440000c21015120b000c0082070305452482c210740c90700001a4484c00c00d1189203012258010403124864400d01c180c040f000c0c0d00400c20440700307400e00301d00210590100c03810000d602c03608040da00140b91284042c4050a2180d18240b8802002c1e26510400c9480c0b1004a0f0496255004020f1000c2c0c81d10241603004859500c130001281034885c024600511540304200349841008014007003079000c034055058640718200540e40b52500c1d21203203407008140e045034a0320b0340c07081300034044030031104240d50040b1000c0b260007000300d034030764064404080306136040d075000b107500c04c003410f4440200c0342d155500c01c2c040c40204c042296 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 440230413 1250 440229163 440229191
    0x906180306240603050106020c0109030b131a1006090e1317090d0b1e01080c060a05040b03090f0607050909130311030d020409061a070b060307050d050c10080c040e0a 73
    0x8183c1000d40441d45480051181c60ba0412080744051030034600781010f9861901c52030b801a01c0a003903c0d1380300f20001903000c28000e4040e11040c0e08031002121002610b48019050080c000d2805100c0000300301442c00141f00d103514401034006c0c45120106200d1403981da5990340160300030800491034a00c1404298903a94604014414090044000d92250724065296003043c41d0002020703a44144d0100040c45108000140713038249040a548075607031800d5500050741c1c903000d80d510503a842c074000000c00c410300c10045a62441900031100711000c0b51034000c01500c82e4001c000c4c001c0d412440d031500051092000000d44d0880c3c9000341880d00072a062032421a003503038003070f2034910b44003600080c00308103084140c810031000707240540d01400d040310146041c1060380b00300700d0701404550300c04001c180f25580034801c41c1d008240c0100154030b40d0f0307130f00c0c580b6644641c01600380380e121300308040021000c103001d10149840f602d0803c00c0c5619003030034520441014500a0180341c0c0e81907031502042000304d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 440231663 1250 440230413 440230481
    0x1a0105090f041a31141212090a060507020a0303050115020a020411130303081008060c03040308060f06040909171602091906030c18091e050f0604030f0906180306 71
    0x5802d00e061072a04c681e5801c100d4107840744210b203240103a01061001d806501c0003000d40714101c00c0004100610740f01c03040c801d898044568000780c03210340b03488140548035070009515041c1502c2510f05020b03581c2c0e520b10615940d12280c140d41d0241e003100010900602d0180e011102045102442506200030240d004080a086420440204d5071000501152038071700c1c040d140080004500800080c503207031a00104500010700004c040c401d5480110b40a60340d80003440c0300f2502c0191000c0c0d20b8503525204003001d4040b034070087d921110242d104c6044041000120b60760250b800318104064465071b420710144500050090041840d1a0035800795880b503805841c0085026400d219070503401d210121a1586410072811411880c0c40345903400500b00b80038091081c0b0b540d1740c41403942c4007a810001d05240000700c004815010302000c00042540020382c480c0c03002001e0760350b010311903201d0b4001c2c0c03003100c3c22142003828645401800c1000441603004010741440d00c03500d054401310418003c158030303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 440232913 1250 440231663 440231731
    0x1020a0306061e09180b0d03120c0e030303070c1403030c040314030a09050f1219060506012d1e0804060f140103060c0201091a0105090f041a 62
    0x1c1e2554010403141d580184203821492904080002d04055040c0151000c103d52180844198000d52584031800086e4400b000781c1d100074103800f42100c81c1d4030f002003940c0e070715681100c0f400380f6115446205030b12502c091608400080d000303503c0c0d910f07804010368061200d0042180d6401e54200c02c0f61101780b042c00518000d000e0002c406440b01d04602d000d180540e11001c118009502c1405070501d0305501c41200c20880b00180c8860f001900d40300003069040744c40412509280c411040c641042c8410908445e04040c0240010492a00d905004503507440c1c02c441c061003280786008460038002c420f4203c88280c4d1007079084c41d03d043e090030031100c1504007031540c5a0300402c1d4014100001e014941c01075442d2030600400410121012a00301e0140860600029201d240d952244904060003548500907451b0003600c801d10601601e90141001002400b1b11801080100c0209048400c0d822102c1d0196a00200140d00d042d03411403160211000140070340780700e405030b11403101060006804c040c15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 440234163 1250 440232913 440232917
    0x51309050703080a020d030b010206040f060b030703030e040e15180a02310612030e0a0f23011d12120a0306240503060114040305030d020306040b09060a05190801020a 73
    0x21190085130103410a0b080e41500000e15090a02140a5a0380400d41950040e4041c001940000d11424100001c218409a05816210340744000c405d064100001c940035403411142803005881d8818815114502004100e5000760800085000d5501422803111442035110440c0c0200c0d4032500003407100d05041e181c29480110668110410001c14004e0400d1040105c00174450549020b18184600011580241c100408400358482580d1a950a40700428010042030210303502c1c1d00f0180f09081d030141141035104044114052a540101030203c3d01d11851401106503104170014451594038440c05800d81c1e0140d100f0641c4560036038406444030842580c0c00003411414550020364052000c5003006000c1e0900c3c41c281e0b00300d039126089961106e400c0c0780165404900144000f0140965000288640408607212040003055400743d8414cd0007141d0a12050b40560140040d800042d90a00c0e001803040d1b400f40014204115402c80c03400c001d1406140e405e0b69058144d0032a00301c0700c2c441340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 440235413 1250 440234163 440234167
    0x14070203122805040603091b0306060503150f1506120a020d15051e0a0b0c0d0f0309050d0318021305100b18090402130504060b13140105130905070308 66
    0x190101002070014000c02562544060002c12150050080d01952150104064503402c12804200380c0c01d5401210708144601d80d482c0b030b922854000c0140c8458041c0b28040e00c140140030450351001d005040c0a5130055400964a4540780c84051199050708070450f0041030400440b0064801814618810840c40b4030040e112566940c1c182c042e00c1804c155041089426242409030355600c20b102100b00d00b0902d01c0350404014003000c00c23070451440d80300034200780020031140b0860070007182d000080d41c0943d40d0342154060950707003034048541300c0314094026401500700781415400ba81c0142c5482030580c41501440143e030340018050320010009100c5141c5842c1802803082e107003251180645115101c1600780306003401c045000c2900503503854400c0a4071000f20f4155140c81c42455049400c8080c2400710b85031a00b011006814105e51036801064000707003843c8001d005204004084846082029241c0d10344820004030110302044400d129542c0c804400000c0d40400030070b40158864040e0903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 440236663 1250 440235413 440235427
    0x901140c1f05070e1507060e03070c030c0509160e010917011a0906010206071b170309070807140d080903030a0909050c0901080c0d150906090b18071407020312 70
    0x4000c1e900b0150003070091220011141d08241d4681c010040031006825643d501ca0550303050800c0076180803106112a80000160041801000d031038007030a607809035040b411aa80d444081c000a142c04480f180505111a989a0700d03c61242d03210510082051401c1d01c540b03500e41c0c4100e5001c0740d1a582e405416952a4a0f21a80400c9800c0b1480d41030000c40361b81c0014a040d00010351a070030b00500749010000d80c0d45076448000304001c0a1132010703403c240001d07001540003140c0b01c2c0c40d52064402440602c2134100c009000180014544c0507191000c8640c6001002c01c000e008084800034400c840c840014840841c158034200081c0c00c1c00d42569541803a11460011940110381c00504106485641008000300a9030054081038201070000ca00315070b100c4492100000810b0507480c003041c1c0d03540c40303440002d91400c281c0100d0141c801c400c10070070980e200141044610070034445501000503c420004642c0c074003a072000d030511140c04450529019041d40003a0500c50041c500301c4110340041014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 440237913 1250 440236663 440236723
    0x140f030c030a03110703051204210804050120251218060305040512030405011401060e10050301080c0108061207031a0a05060f0f040905070807090e070b0901140c 71
    0x44480043c104509074a01401744c1c03401003803440345007444403588505101260401c07101ca007445e052007035030207481421107091000084c50844d007550151801e600305036161200c203490038485080980e4216059103400340351018040708041c49900d0804403403c5407590408680895544607044c8543e0703070351032840c1c01810556501401ca50b0800070030145010b0802c400100d00182d0b5114a500340703681c440d126901c40c5400c034050084525021441100030000141581e041204c0651030081202c01c192010007642c030848041c0000d200d010001e40c06030300c01e201154040c00403550050300242c05000e42c0c1140c0c001d110b150192130340c01191851140c01c18104000444803000d0f0300044441c43c140224103004000515440484107554400c1f1140703d280c0b4841d076110340c4100001507201c001ea918103595030b0760b60b0361200207074407881114604101c40070682480219105050303e00d040440d81c03c14143c0301c011038040800304800030307061204000912a480f0708021245420745c02e1514103802440d00810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 440239163 1250 440237913 440237921
    0x20111120d27030906081b0c010509010501090908040306091e05070e0601050c0327130504060c02010603120e040213081b0102060601050711040b0a08030c07140d140f030c030a03 78
    0x414160b80140014030010381d006107000d088a91500d401c11058850031030729440100340c0c0801d0013030100006044c0f4101841900300910864807103008110980e0303544400d809035030071648000e10000c002c100500008849500c20307003646010305218102403516502014401c0d40801c0c007919030380e004400070041c4001003040550300050a107041c1e0b060044272240071340d503030059050858010000c904000d40460800b4486003c90300c2c010b0551103410440500007009010036a41030720f00c0d03814010310a80203401406007004907035200860102142200c001120500c5424103801d030b010350200030181d07500302e05060a8000d03181140143c84100440600c01e11200e015411607810364103c80c0070007c00340c2c1c1140c03c0e600307101d8200d41c80580418203240003800605020480030b9114120f07486c085884000000906224114981128403194548807085103c0d105003001591003a40703001042d00040300044824150032140040700d402e5144204160b065402081c42e0442d50b50010540820341981402 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 440240413 1250 440239163 440239211
    0x60f121b060c020d0c050405090a3011101505090a0209090103080f12011d060a08061302010309050a26070c05060714011b200a0f05101802090f13020111120d 69
    0xd0100d5580c0f40030312f60001c1191004c5404041c02090742d00000390400034009400800d100741020040340300c20b48883c0124240c540035190150b824100040d40c400300e14400c581c1804801040c0040581ca10b80d11154694084119904c00c10028400c4058200740046110301030080d0f03803900342d68030201c00e80000d0840c1c8000c18051092000900411a01c4000b26a107034001c01303000e11807249004a400140d0103403131308603801045485458001401d203e041040004c00d80828161500e00300d46c110b610b038445004038080603010340c804280420080c070303159004080f014032a20110960180712580b80b421295040491038458450b49019119161b0040340d0811121f000c00120000b101000151030351425a0100103201e040150048010701808000d00e259580d011801070001407401a40d00721100d0816400302d00034041c03079020a80c80700c049401c1d584500d01101d41804021400e030011038100300d20300c0303100500780501910031040b0117411009100b0480c10304804508050104084502840804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 440241663 1250 440240413 440240453
    0x20403020f0402090d020906010908060a050a1503080a0815100c050610061409060f0d02180604050f04110f0a020a14070803030712060f121b060c020d0c050405090a 72
    0x10403121580d171181030441d1416010f40e2051007548da13800050701c0d40c03c10341d08183d0151048408002200c052030304510b224544101c030510000344440e1120140701c00d140801007821a05004c0c1043d4070707115a00c119400b904840c01d001710609100c0100d000036015100b898009070300399441c9018468100817050700111301444d0040010700d00407005029081520f512403c584001440c5070030359442c0c41c207031016240781101d03503030381c982040384510300a6014114941c1c040c0038085211803246804002c0e03404840300a00411103951b02030040000800c0c0212086c48420b1042c06042e03082807400c0d0103000c451003550014020303225642045c4c11240558010746d105980034030402d11107200c0100560350004c20f50308008011444008040020300520f410a074900b1981e9200042c2044590310320300000303800350030070000e5800400124240c1685031b000d420701166a02a240300142455a5080d11940c0148150700c611500e8070002401d031001507409181541c445c40207101400908000f07017600007851 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 440242913 1250 440241663 440241667
    0xf07082208010b18090a031d12070303111501050105030601031b02030a0e04020f09060c250501080907140d021f110613110111211305030604050304030b220501020403020f0402 77
    0x5c008150741d01d0384407910040400c100300c00b0703102000420805124550350001d09500e00c42c0f180d88056540e42d00541f10660005d5092105001c12040124000440201c035800304e60b0700381c0c00d0800558055202400305410103544d200303040c419064082408240e240c40d81e0145594120071a00100100000c00ca400e20442c0f04100f010071945000c002c40d1100e80043c1c2e407854507085003810940c00c00b2801c04864020041d40c14a503a20910040108015607100743c80380e40c09602d0310300b180c540d144820b000d6180c42441d41e10800c50140f0b0010100c04109100810442200342240d20540000000e0090341c0c3c007165400036030b00f90014080c40703140e0744241030414804100703c2c940c654010704c2481e10500c50500c06e044405500b00042405505411080c04c070003548e49840305005121039900c12001c110041440c020041307400d01d0003040341c90180d60030100440c101811a215140c021402500c0c220241480207100324182c6c10f4104a056402d01071400103132264558010310100e0118800498840d600c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 440244163 1250 440242913 440242921
    0x30606050408060103111305010b19030c021f020705010f05100506070c090f02040509040312050709051f18080f10090f0f080d020d0209030c01050f07082208010b18 72
    0x10000f02141101d42100d9482030801c21000410510b050122013a080d01c0d09040000c900100e42c4c0c4002d05c80d600c48801c2c17443c4100e045100c2101143c41c421b058500503000b50100c4031018914400090440001c1e407001494503034559070707403070840300050324010441b919002080500c0d24124680b8008201c181c0d04c491400c00282c1d40c1d841014194040d4813401e5a69010000c0c0e6106c040d411744002e0040031308001024102810040c3c94030710090b1130240c05500700f10010701c82c24071440088044407006000b0055445809404111901020407804200400410b000c0e403220200e4019000903e220742c060549075800c6000f5604149241c4032481081c0d080040180014800b0441400102d03000380348031070603654038a4100c1051180c20302d10701801d400030030120b4003165107600401d0441000c81c2100c64181c045070041d500b070f008501540c09003c03001d01c13044001c01c4041c0001c0400c6580b103002d8642c910408040e0004a00450708100382307a81d512540a50306007041404451a6070307041201001d0303850 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 440245413 1250 440244163 440244179
    0x60f070314190b09040302010207170f040b0c030712082e0b0a0c0b07030f050a0501030b060d060b060712300c03060515190305090c12100911010306060504 68
    0x14040c08418048500c01c248103202c890710b034088031000708010302001d0581400d0400030301070341001000783e40d040340480720001c5058061045810107002c0106003403c00d803401c41103e009400a5540f0710650004200c40c5001540101c0441c00d04407039901c54a0040c242070550054014010210307001c9030903c01c003030218100d5aa0720207803c403500c070f0f00140d40d40c00400070111040080600020304c5d001d1888107100c82103400d85c0041e00410085482000039541c0e203800c00701a24002e110152441a0410102d06981410540c0d1501035000d1003001c2400d00704c41011404541c80204140c40051240401d0125580d020300c1c1d541d01c00e510101d1464040c0071300140b0148a4001048000c40f580e90368812090650184c0c0161000b45001003103000031082c000700c4000d2551080c000752200219040154481c10b0091003044d01400071900104a80c20400e000d006040c51910740022441c826100c04851000c0b01703000d0704040501c10b00383e21342040c030054000b4003640d5454024405201c82408140300e021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 440246663 1250 440245413 440245451
    0x230109110d0227090d0914040207051c030c08010801050402010818010f090f031e052704052a121b071a07120209220f020a02060f0703 59
    0x8a003120701010301d607110300c001000d0402d0301c06941c4000100e19a22101107401107000703803103000400103441060310354000490f40f082c52402064090080c0e0010641c60b0b0926a014055151194080f903860012504600041d1904600da8000080c1c6618500d00c01e50f0740032340e9850040c20b80034001e009a0419034000b8001c220300524550300c0f8980c1042407010a003094000c90031600c6284401c104460060170103040e804811346003500801c4800c0d03840c4841341d407105016078805c0007039a00d10f400c00880249107000088814040300341c0c5c120005144440c1e0340e8622540340907038600354080d04090840170308210f00344183d0484148685e014071903011008240d103049075204e00300840580500e10f08404070072243c0903c0602038481c8486200c034814521091025600078000c549902e84e04004002d5010142d11426140a800403481d03000c604003004020240e450740d5810742c4000c2440d0307503048040030403072b04604040c0740164001c0003807003140701d070341207a0700e030000328919052001c4000e24900991355 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 440247913 1250 440246663 440246693
    0x7030b0f0306040f0501020915040e090309010c030c03230c0c06040501171b0f03040b0a09170a020106170714040b09070f0e091503012405040b060702040207230109 72
    0x411080030300708007041700171340c1199200500140007051101940c842040d5a40040c0521035403403450601250030079500109582003010140d6905900c1c072240d540442c1c80130090801101401540d00703055146403400c080281443e50041e45d1507407030b04104400d0707500e411880412240034500411090000340d07841a11401e140d9181c0e1106901c0c2d8035543d41c021039125561603520580311001c2a20f1142c502d000b0029401203000704a040030544130700540b40e08441220000074607000400c04c080815035680e0001c1d103c4101c580c00001000d59a446106d00341c0c110201c0104903580040f002440000208807002d00300707810650303040200500c4400400c65504010300b411007401502c030348502c0c045108111002c1c1c0020090681e10341810000780e41c101070b102203500c2c0d911950800c050702ca08189150310f00804100c00c0790711a224030f0700e410148001054820710158005c0c90801540e4090f072118002468410b1040c400300185903d9050140c1d0190582c05489071a0707410960683c3c0826507000a100d04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 440249163 1250 440247913 440247923
    0x1603030f05090307030b090105181204090507031b1e0302120f100909080a110a0b1f0506040e040c210b0601030b03060a0b0a051210020703020304030507080607030b0f030604 76
    0x580c82c40000040d24000c1c5941c0000d0151061804004000f2010b404c100e0003070384044000d1400c0c2c2c4580c85019242c00b2103000301000701ea4140010807204040e900000d401c0b6000b030500160260014444408098a4141c504007044500c00102c0c01421401140c210f1000189011403d1400c5040c500107440400b90840d0f4a1104090119000200d240c1c003110080102280c02c20241c840c0d45800c0b90250000e038050000f14222240d0034500442c00304102c10415404950001e043e0f5034610150f2041700000d03050031075040750441c00301e05601c034600248043c2c40c2c00b9400b04554507180c039081203205207a030000d1350002043c064940803004010003c001c0264003003500c070026a00e00004034010030002100744d40c5881138401707000210b00b083d444089281c50980e50b0340040703901c03074040c071203044406020340300709601c03012060350004001e0b40074051b12442032041c1c1e842c055803522000c0ca03040042c3c111404e580c1054061200301038040c070034004006001c0ea1080003a0801c040001c1d1513001c000c0c80905 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 440250413 1250 440249163 440249167
    0x1e090f090f062b0609030e1003060e06120c04090c0f03052802010207060809121c0e0c060406231908010515070201030c0c0501050c0403150b0d02011107031203020c1603030f05 77
    0x1708040c041e940010107103002170403102d44101a54401006020f09205070070001a490000c40d1040c1031950903c080c0505075001410300f40000d200340320050a10401c00c0c0d03102ca1203280301040c403a0000004000950040d0002c00101c0181d075001010120242c0044260501c0190b842d001030360042154422940c0c1810441c940d5541c204401b41880c01c00207000820341d1000801700b084050b01c0201e2004814019003c222404100211aa580091440c4141d00c182c080c4405c0000b03c0c4140c1205007801c071210116269042c41945641300c941111740c24181e424003a1030044601580007002d50b005102c1160b40200f4401d5656130304017688a0088040c3c10151a8840d080303419004003440800745610100070890b03071424441030040f6030003902040341c544118511190a00200c0c1c059001400c000800c1c00003100c0080e401500c01c005202640c010500924030000b000c102c040c4451400c0b4440c907107015a0340c60080007220304112086510f040002400e0b842400401e60002d00b910b42c1800e18200030f6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 440251663 1250 440250413 440250431
    0x210090c0e0a060f03230105010501050f0903030f0d02040e1003200402090a2408040203060a0b120a0303090c06110c0111010207050106030503040f0503031e090f090f062b06 76
    0x100280c181908110b980b078403003144c00002c01107010002c281c0300d92030400300303545070708200c0c0c1c4142030f5203007032003418001102403004187d0110844001c00000300000c0c116890043e054041d00c8094100b0a00b4014841d8041020000015200c0d000d50380000030003000902142507541c2c6e000c41c90045c01c101005502c62803009546174840d54115443c07114010b1841c0c0707a07140d46240d06991420030804031400c06900099080005004965050169600030060101c070707030f62040101b00800c04150103a90024002d51820709024051040d03005081c042e90f008110f0f1451420020000d00340c0f0303407004040105410740c0c2141d5050109040002c00024a003030108001d16103000703400ba00440c54040c049510701040041040000402042154000888090031a60316001c05807240144402c141c0c000d045005408240303c0000010301d11484e00418800400c5078a401186590f0342c02c171802170026050b80144490707460540d100b420300d209040c3c08600194a0320400b9072040144040003000103440348120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 440252913 1250 440251663 440251681
    0xa0c0f0b1e07171308030412110f1b27070f0c02030606010f0905040f020c0106050109230a0b1206010201051807050f030f030a020d090501020a0b130f170a0210090c0e 73
    0x704c002e00c5d000000d468032130070142801e034021401d0030340180101c0d5480e4589428000081009403862400310701034440c2c071262884514401200c800041c2d030003583c4d6100500c400041e40118400c42400400c117251324900040c020b0515844001c00d07800744a0250140b0005a50004100c1d51208080c60050030003130342c80d0000d1700c61218540000768058140a03140c019410300da4041c2c46883c034128000c0c000540d50728010355964900d8014600c43d82001c40440070036130242e144030728000c1406440c1e03004c1c0a6035003102c05403a80001744207485084406003070020940e03090180c01d17040350405050740c901000610349140c1d210440d2142c58094180b41108035015603050018048004048044d25612600d90303100030340320800400d581c4040340000001040c2c030f502c000b48580341c1a030710581c00c020300d444d4004520000d0840300011039812202810b54030000392040080424001808500768840031070b07000c00f03410300c586c050011000c1440d1065181c04119400c21000c1140d15160661700c4603103684a103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 440254163 1250 440252913 440252941
    0x1a040b0c1c030b010e0f0612070203070f080a08100b090409081c0501080f0604120503181218090c0a0806010c0f0b0f010b0a020a0201050a0c0f0b1e0717 67
    0x114110419111544180701c54154010030060242642c40007148042030b01000728840450a085d40c000d501889040040300c1103806194000c1d50f02d00403641000b100b541c400400440c0010b0440701c2041c0401c8001013035400c141810380020100462120a13801c2c010404001d0241e015120302c40d036100d600c401c00f4003042c1c40840c1c1d00e44180e4401e103c2c0c9244a03204c6100900310a210340302c22803107905641c10083ea4049061030181d584580e012003074105107041142e01c0d03007000e84001400c022428810607002800c01600702e8000b051003450340c40350720f1a12038420840e4031040c0c00d8010400c0400f04007a029114048031000703015410710f200c80d40c88850040340c8031417041c507000f0160340000c0403002c2484030300307112588200e82c1d580890095a0701c80c2094941030250607451000350388203070021070056001e0000b0b070095000c549001c8594001c962500040e1110f01d14059540c0b1b00c00400707104101c1400201000028201e14039500c403428050401081a40e0030300b141e14850300990040340c041400442 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 440255413 1250 440254163 440254183
    0xc07260d02030a0603030e060f030a090c0803070c1a0f091e0303030103060501030605070e0904112b11010309022803060f0515011d040917040611071a040b0c 69
    0x200c11901d82c40c10440000c01800640025000b00d0100003108900d0b00d8140111041c0059510006041d0748504625901414644200320780e2036100040c0030500340c2c002c002174640b8600030542141035a190500140c41c0c80d0f112825400c0d449010031500e44451100000c4078000700d41640c40754417140d510240d1042c00f49101c1d1096605020000001003400f2040e00510706a9005880820039034450340e800307039017943c00c4541d807075040040d0303800050214404290207400b180300070300106591299503031904608a222854080da0380030f00542c29080c00450002004866400e0038100080040d41d0001400b2846040d02c020b141c074103400448941d130440300014002513031712500601c0350500c0c0003002c1001e8501140d01200c9045020f440540d035622545842d52041c1441e400402c449901c04140806000707544c6042d62003c240c12028030f100d0039850000d00082c01950313556188040000c654a04180c180d90089010b0820303113804074618501c138000c0fa803c0704c0c9021000e95981101413903590410640036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 440256663 1250 440255413 440255437
    0x1207051c0807050a08060d061509050f0412030b0415090914010606090b0307030e031306080f070503130311070f0305070614192c040c08010311090601090b03011503050c0726 76
    0x1c0c1103c5803070300349c800307902003901e400f00c50601c0b4559600c0c0111400300c2088030040e24919040002c048194040c1d030200c1c44001e0050004078400c240c01400e0082403e4541c03000c0760b80f41d9a1460701d4140031704058600307105802c2da4000d02400d40f1b03050000300040c0b02d07405503075410440040850821b601a80c000b80109a5490a41e51540021a11010380c409640b0405010591030000143c101008030b0030244030b00300c9511150304540302d1039603040b5a4000380310100d05111030b42e81c030005140070030880000100480790218500c1c50552810b90f0070b00000764080000c2c40003410080180d541098150341d1442c0c00304410280700043c4400c221801c145070125a9444d9600013036071452603c0310019030000c0c101c140e505026004a001049071404400d22001e080c202409403910340c1d905e00003480300c1d0400340514203040d41544030321100650340e0080c3c4c404514060b07110590120075403d40101350b0700c00040c1060074140324003030712441100e45070300a140d04070584400e4038850620f08401a514000108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 440257913 1250 440256663 440256671
    0x10c050601090b090901180602031e0f06030c01021b0d3f02070302031906021e0a080105011b0228030c05090a06261207051c0807050a08060d06 63
    0x1c842c00c900070304510141500801c440e00c0061003400c01405400799000400364581c203000059103e000083d00050700b11a03d094400d090100380919100d0500e00071034100c4044000360a019040600d403507450810281036406c040300030100c0544000c188ac1500742c0c190b40da00b0000119240245410b0050902c0c0032007000841c1000c58464042016840000901c0c40c1c081d051002c81d40c4140d80d5508103104c000e6166010030400d840001804422505103441001c0240c1411101c81043c80f00300305000d95885042800714840c2d52030383d445254680107040a00b40030001d07014040c00c2d1202d4260016000e80102d036006c00010800c00b10440807031000c4012241c03004466124079056102d030400b441158400c040d00408075407504100d2043c0c404890001800103040c11100c0b540e0104c0e103601440040d682d02400d540000702400e084014000c0510a0307001d021018551120b02c05816811605030382004a600200800c954110046030583c100c0c6040c42e460503500e102c0024039206000100400160070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 440259163 1250 440257913 440257919
    0x15100e130f0b030c2b02060405090f040c09090c0b070f0c080a05070b0f0a1206080105010308121b1b160801020a080109020702030a0b0405011d03040602010609020f0405010806010c050601 82
    0x841d4405250024110b051315080043c0204100c0205d100752030030740c0354404030120665455101c10800702c03101d10103407074181450703610720004605110882c2e0284108107568100070803c0b4507450410080c04d0358031010440c6800e6500c0f41ca0400e4114050081800e50014607481030041900086d08183e03401800f04640c1a01d03000c5c040e03200d002551045442e8410355501103070b030019680c1a80d981d82c5441d0130440c10b1503802c0d00115035451841785441030300c41e507813880824034040030301860303001c0c5000300341c01540d40340d11307440481c1c800e107008052201d004500e80d443c41c401070000d421039409030781c51004404c42141d514003039410008100148000c5102c6408e000824800640144c45910480d480b00050b90fa6a20b0b10101a80b040f808020740c550400790401c000503200d031070995001809107000040f4071004120000c1a00805800b000040d803001c6010440785a09002d000701030700302030b4401e6090032013000303e8520902940c00780c18188045000051490391003000103240442d000030486d24039580d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 440260413 1250 440259163 440259191
    0x40603031116080606060a090806070e150c0a0201050306130501031b170606150c01090507051309020a03081e0a030e06010509070215070905040f02030a0515100e13 72
    0x5050301e1814150300880111030700c2d400c0d80c5526501256280c001800b6281c1c0d07131034100b00c0b095001c0c1d11184140000c004d000b1581040030071240d48518a940c5400421b00c411404001809002d01d600e5074068008000f2101040b9011400e03400c3c243d82820301a0b12501c034000000c0c401140c99558954103481c0c0b10000092016104410514096220712900016120621040d8030407094004109940c80b0130003003580c1c1d081440c2030b0071920300211940307401c0410308810700e8291402c0320ba09407001e41c0320384001c3c0241d280010600303001c0300881c0f00c10410741c5410703400f290440c0c00e548000f400c40280890010710644a801038801d282d00c1c1c90001640d14680300d007000d0010b020b0715111700a94030400001050500b01010f1890250301580c00920414501407500104820300401440410a0451000410741c5a500900d0000c401c0040d01603224075040e215401102d6000345824989516101040040c0e01c0d82600210700b440e09161004080c4d16150100b1104a001e4004180d124905420508110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 440261663 1250 440260413 440260427
    0x30d03060317040803160201031418070f05010f0c0c0e0f0a140f1f08060a0f0b04021801121e091e03080a0b1f03020309070b130302010c0f0204060303 66
    0x82c4251810700504403804078600303443c0914003620909034003c12540c0744603290445102c01e03581c030514000c81c0e1100c800c0562a4407403001e072207075206040d10001e41420310800f8081070019110000c24044e40900d04000205950b88900b01d4205000b200207203041800b00090880024103844240342425051030002d5252035041100d6840c4101e280c451100803c081c006c0d1002d01818240a480d82c0070340301e051f10a007041000910521072000b0752440042c00f031b1014003519201e9140c524001130345c89000241103090358140c4641a01c82e034070405c0391003d07000d1600012030400800307103089522a04461411401404104807a041c0c3d09513a0000d41305c00303400d581000c1e0a1a1142c0d1034050648040c508401d10421180c074020b0100301000d001404107010b03680b00701032004005042948801c0c910641c201002250184100000e40020412500d004104160802001c8039034a40740740030301c06442038a08250a0000034100012407094500b070205507019070b039025800800800286a907490040c000b5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 440262913 1250 440261663 440261669
    0xa02030301080d090302010801060806190e0709140303040b130806150411070215131707060806010c150b060c0f0a0314040f15140301060f091502101a030d0306 70
    0xd115032001001014819441d410481b903040c0c503038071042d90a1170000c2d44c221000510700d07500031070559014105454400c040000403e0002c40310882d9041240008001810541140c0c51602800000140640700081110100c0360a4a41d25884403000d15a452034858240d108400310b00c6458188400851f20070110407241c10101c8041110202c41000d0021500601c0340c081c0d4002901c450f0001c059610400400c2503010360040b0082c45030700c0e880c103000183c0401c011410305500c0f00702c1c1800b42c0da0b00241d90b250001c909080c10101d00d1003607500c05d0400c0c03280700d44c43e00c68283c41d543c0b5860103488002c10f03204034800d41380c03e541004014030561136560601b00c03401e40010702d105000e569402d10358012103050750300582d00c149170242092144400740d020415554208000c1c08281800c2c0e0048001840c0641403079900c3c810103444a250040c84001243c00c2004031101e5040665101c0d17400144140b07515101c6000800c8a440f20442d0a41480c030300c0d503207160540a91406035401e140e2580c8180d0139 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 440264163 1250 440262913 440262929
    0x5030c1c23011a06090f03030d020a090302030c040207080f07030c1217070519082212020607053109020309010209240702010507060e030a12140f1302040608030a02030301 75
    0x6140c105a80803c0c04901072400e034102c807080200785150300345007513a609809006021070b45045040355600e02280e001d01d40d05800590400c000f40110725041c000740d400103804403000e60410300e56840340c030381c02e1007801c4046170004c10004c1c032203003010f029402c400c59407500071001c94124166010060401000603d4000261840c0300008012178015003c1c0c4203a0000d0702c00402d06070314610700603078140078084d14148048903401e0b4000000c0b0340c0343c100b40520900c1103035074414014405002078a0800080c041030103102090145801800b02c040681075940b41b4240d130489448022261041502019084035103403e0001003000700d075000c150010841c000e03040e18032010301c0c201040c904d0042200b0560b4091030f0001000014095031003039002d040c446008400000b00a40018090362a40e4080c0d00d40602107016400c0041c0ca0745207030b119010340c001c0e0841c0f0100d01490841c0d5a55040704000340641324000d041207000040d9211680503001030040d01c01266503030300710904065540d800900ca03c0d88 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 440265413 1250 440264163 440264171
    0x6080a081c14190c090630110403030f090e0c0d02070203010f06140111030a181e0504050c0309060402040c11031b0d020a080a0309061b230405030c1c2301 68
    0x30684603c0900044501c03135a1111203000021100018000caa000f00e14035400440031f444400e4503152080c2e92199100400c5507035a903181d80b60141ca00b40040750035009001601c00d0412092031360000655020a111642e10303a82c6202c1c0114100900840c0c070080d415610b00303907410341c410000707912100c2030714140c40000c1091074400c001101c5011040071041c045400c103000712140746005a140101141c0001000c551068690045014080301c40940c06030300d1541440820044c00c140c4079030350700000706111084c036526002c3c518607643c007030180000740180c1c0e440e038860683d684104a21428002e496059039079418000d454980e80d2604040c60700f0882c02146041411580006a00031000ba80022014104040d001c0e0a50080845038000e07074066450304540c03503c030072607612100e2000d0600d88484454108055074110112205251466426002c100a004540d0000340f0401010012030307160594400401110501c09000d050040c01281121007014550580d5840302c03d8034051440200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 440266663 1250 440265413 440265431
    0xd0e070f0302060f0304060603021003021903112b0e15011e09090807080c0f070605090112091e08030f0f060d020d0c0b0c07050406080a081c1419 64
    0x40e00002840000d5000030200480b030000d6042c0d40c05075a1090003000d001510079640d40102c5d0300705103003401c0d440002e640054083d44d011484060304810007128601082500c8185600010314420791080c0c1d101c40800c078440d00e0440594100f41d181d66100c0c008280329401642030195034526044080c07002841c01c07035001045d40c00080f0b554030718200c5000c2416598624085010300248100f500aa40c104070401003c004224504020201c8100b000c000b01061402120303a181031110542000040000c10081030792544e078400b09100e0403000c1c01e0070016110001e4076112144240788094030124441d180030724001c1c44001d2001c0d5100d90750405d40d607061a44c43c1a4213081c02c1f0000c07118030768000742d4108210b0140c1030181000c8202889210000400d0b80c0f0f0780d40480e1150014040c419582d402180280039030300341b0f80183d00003011480300806002e06c059403030080340d02131501d441c0d00910032441c104200c20555008000701108600074030103d07013171007007012941d41221aa5910140e0516040e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 440267913 1250 440266663 440266679
    0x4090b060901141b01150504051e191503030e0112050417031e01090c1202070c090b0310060906050901050d0b06150d06080a0c0e010b0306061309020d0e07 68
    0x200c1228078141d5a101c044035282c41c00340080d03003004004c050155080281549642c00c00d114080c840d4010100207841180b820342000181c48009104081070540d080c0c41d010305d414000901c50700106c1d80080100120310584414004014002c50f4081412003210300105160b00303c5180d20b01070703100707990701000c940c030301e55500003a5082074400501740c410002208010550341c2003c0c60f000102c0102d104040b40b160450001d40e80420703004400d4103541c0f408924180d42d00403501c440c40128000c030030b5003003a00175224400078800c00c0c883d011030701d41c650400c211265030074021014042000c4504200290300c400c843c00007441a401003a00901c425000411a480c1504d01140e481d40d000c14244a030307a90b16406d00c4044c0c1c0300321107011034110092103017408650035030103140094020304c0001c1014034683d0a080c0a0250954401d2009401c04e00050001001c0c44085a91200041d191181e803541a9900241c4000e500ea00c404240361000c503c500b07604401e44c2010040c440b140c4126582d80341c0390004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 440269163 1250 440267913 440267917
    0x30304060207120804030803281a0f060403051509120c0a170c010603080705010b010f08151503010e04030923040b03010605090c0304030201050a06150305091204060504090b06 77
    0xc2802690019000b00a1807002c03d100e8260307907104014031402d00ba600d54901d0341c035070015294592881e990000d581c403030644001c4140301b010040e07041842030085001399100325014442c1014001c0c45c040d050440c0300d0b150b0310304480080d40d011085076030024851805003000704065400b8241805400c546060762107501c01540c0b00032a41201424000307016540741000c502c00c044070304980d202e0510103055050403c1c41004011401080c1c0c0c2e5503590028904a402c641c1c5840c0b54905000101d040c410820354000389183d880740341c41c11041401034402d40007a40d9070811516100c1000000070010079112034000c509030049109403501503d698070b07044902d103900602001e8109a1075a1a81c1158614158205072406200a00001003050b228008a180c010003100c04000014000062004040e824450700b07030b0040181501b080b545040c200d4480b226461658650101510f070f20225080b45400d00900c22500d03019200c0950b526a901009030680d089031040d00e1105280c610709108604017002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 440270413 1250 440269163 440269169
    0xc060c0712210c02010e071d180a02060c03090316080f010c1d011101020304030203030f011e0302060d020c0628020f0a051303060c08060f0d12030c030b0a0b0301090605030304 77
    0x3842c580303600c0d40035850401450b203045142c2c215900c5500380c6040f01c4082c4a46030113490103c1c6005000c1c1c4000600040aa1001c1d0505803150505003000e440c3e5000410000d50310780d411502c03540d907444000d000030300d140581c15515605000f001c0d0030002002c000200b480888407e02d00340d41c403100c0b5050722603080754650f81119000c104041c0003000e549190041032208200b050504030b0b9841e1409034680c3c00c80e08115000c0300542e000209101c03001007006c01d024014050b401140c11514420481c00382e0846075448024003e4402107801680000580c040d507084408410455816180620340c0b038a100007000b0002c407604215400500f8612154021124001a61042240741c0002144200c40603801101020346800c2c60079004000a20b40d030040e00380702d2302585c1d01c45040b400e00030200516442c86854843c890100508134800103641d405400d010300c01c1d2420005415002110250080c12400500d0741d4400448030002c03826214540245050fa401c10300200308503504c4100345962481240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 440271663 1250 440270413 440270447
    0x1b0d0b01171006080916090f150614031e0709090b06160807030315150915083c04050120040902030406060e13121d09060301020c060c0712 61
    0x14405004040c0a000c1c0c903500014802e040780c901b0a1040514401551a50450080700361201c1a000c4034102901401600c000e09140d0303810903a1400c800600307842c0003080f465180c017030084001006201c90001d07a882c0c1030007150703200a40c0d03d0f0440e002800322800c0d008a041292030010924a0360400300240c1c0d10040c0c00840d11183c084080d203e003101900076030012401c05844801d038030540300012001000401c0f40180030141c5900148000d004007000d40c01820181c1c02c1c1203452424640c0c4100300d10f4010702110b00d006000743c0840c048002e1030100258a1070303e8104141258900f48105103072a00c9180a000200900c4201c60703215140e1302d82c00f40e06072905460a01040c0300740b10803a8010f6400621070f010004240b941d0342c036012650f2204464481c510441c92119a050055040944071b507400c8a18040320100381d8cc000349035a800c03403032402c140102200c200007a0305440941c100c1e80c41d460400100d80365803402c07130420500c075444204100c0d00980307041c0760000114054030041d40a0000301c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 440272913 1250 440271663 440271691
    0x1404121401050c16081602042306100f050717040605041d0c0403024e01050907140102011e06180501080d0332070207050d0c050402031b0d0b0117 64
    0x1c5c0e01c035595560003072814504403000d2400a0070043e0303030320300c104902d12196000465104503030081405807458020180383c083c007400401025910360145203104018814240b481c0c951503e4180051001c020000c807140040d4005800700d0065040405042202d41d01008503034540443c0c00080c04a810660b003640301e0400600080c001803a18000d440c5880c54080a00b01c0307070314503210700040341020b4240f4500e9602080a0484a42444551000030311071070f040003400641411610207a07070342214442e4110090052a004615070b100707422010144d1015420500211000740c141001011a84664480d41034031243c00310f0480e40074000d5070704854030f49000e80b03484000000294040d103244542902c44608045010811580c9c034518910007072502d64524a9071b28004d84040c3c500900d81e004644966400c110307920002d5080400d84003903940030349005da100c0c0c0307500c0c1136084d442e41d2065095070b46060204001e801c80d084e070362001c10b00a909030f9801c0c500452000001c900e5680c00d40d80403150a06c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 440274163 1250 440272913 440272957
    0x10905090109021e0304060c0e010215060f030f060c030a0c0f080106030f020f070302061008070e04200604090e061605030a0504150c030b1504080d1404121401050c 72
    0x1e143d002e050f00d080c2e44407a142861440c03544003615684125000c0381d40990341e800c08442c5541c031812400305044e080c00117000c00031106410b0004c407200140340311301c2882c01c01a0700a49440c144454004000c842c0c003203400509080100c01d00640084a5079024140b4201655803510701c21402d4030070f0b24850341c6500c1545d90030910120007a100b100281d08103036400f00503940c5039a4107100105045800380d8060311240c20500082d5401c030201c0d40c05032045074401441402070080603000b20350060f62100025694041c0c412141c1c07070000490100340e6000d100450300065149068000c1f01070308514070141c6545e1340c0d03a003002903400b4505103003440c0080e8007440090fa41d202d256000c9508136000e038001c0d8880c03024905499003920030b6000700200007074442c160079156050000e000840380080d041501d0403d8107040460b036032a140c0d0074144003003000c1802c08041c000c00c0f910480b0042d2100024004808c10303541001d000300280401c030710071258a00000500c0922007041030f40c1102100415485a0b070b44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 440275413 1250 440274163 440274179
    0xd0e0606091b160c0b1c1b0c11090702031902150115230c120306010f050a03110d09030e010c05190201050918040b1b07022710140109050901 62
    0x34902d00d0f503d200191002004140300d0b035408001411101c5400d44e40308407081c2c8000c5004081e00c2c5404200d4103042c1c0428101000a80b4010707080024900549000028100848401650384540d501312508005001180e079012000300044140851106a010108030342280d44060002d90546160143c600501c1040c041000300da02c40d8005103000101d444082d0802c948110704018001d145400010744034044840c1800101e01c2040c00007001411464500c00180c0310410b4904001304000000038040c4440740a80d01c00228807801d8000f00d07403189604000407001f48031034202500810240440e0280540c0319410350039000741c4c40303800340c00c03402c80b134002c1125001c07403404049040c42018010450640c81d83d80c0c048188034580c00c0036403807900703042c18000b41b0340c00003910410540040750b03004005444031404445910368140c034451028002c000303c01130100c500d0555056a660400140715030b0104c10b100841c00d0324501900280304126040064a911145100e841c0c2c00c854a1001000406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 440276663 1250 440275413 440275417
    0x1a010510050a05071205030a0c0207120b06061e0d1b021c02070e0a090b07090e04020d03050d090b04050c03030903060a0c1407140d05030105180a020c030d0e0606091b 73
    0x401d4606155050840d40e40c0c605d0205194000d8103000030300b0200400c0603407460780c0900306040380745002174043d060402c013000150002005001d440c0d1403a00001c620070762100000c0710b00c1c103206488003040881264404c68110380c0302043d2464403500300003041d02191445880000341201940040c1030b001d081140d40f00540d006521140254080d0042c00034503420341607042d922424558500007180945440c00c0750f00c01c0f401078045d10401030140414030140d1409690542c020350112007440901c1c0c0c00d40703000c88a502c20f41c003410740f403103003031000d03660801103c00030580c007641c4214180d404880560042c9580e90080d00981541640b056001c07500740c030480e03408100c8818592407d03c40580700b200b0b0356103650b408010110383c8130320002c0c040e140101c01800200d08400d06850070074990351400d40040c00d0302c1c54070340101812180060104815000950444046210100940c1d4480d00055007140003000704090300b24090064074001034488c138200784610310600354800c0c0324040e003510080065050b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 440277913 1250 440276663 440276677
    0x282c01092a121e06180f0219050d020708071a01090e030d0906060e0f010f0905010b57030a02030423150d0b0409020a18020d0c0c1a01051005 62
    0x88603070450310142103206004620141405410b185e02000c8032a41e45c4003100c0c0d2440004c2c1525105111102c107005521103c02e4020400346051620307100085403500080c451103200804482001603810100020100d0000039410b01c10061000e9130380c0e401c94001910b117101280c42c42c0e500108661821266141d100800a60144070b002075441d469107040411a0002d54844e901e40c040703e0010807466180d000c0050203000041414401c6500d009000011400760300d6401c00403c1da0090800351600c81c4440e40c515840d03030982c0c0f0b52003011528400802407400c0384100041002c9200c0b4022918000104079038880110f540198a010b1600020300001c07008209a1001e80c01c01d404503420903600c01340039036540003091405d2070380c41030940381078002c450f01500c0e094010742c10a6506005a5582505107080f40d020503803054040158003a040700a01c211071084c00c0c01481d0195880da40f550100218401e00d2240c05071404820001e081128000024410a90b000300d2034041c1d044c2242c07058000c0c00f50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 440279163 1250 440277913 440277941
    0x1701060522020405130509060108010c050a0309140601031101030c0219061d010e03043b090c0a0803030405070b03010f0909020609040e0c282c01092a12 67
    0x603c1c0d1a03d00080700c5510120699582c40e40310000d020310010180a07040c01000004000c002101c0c1a242c040d00034041c5a80a40502d6924005103050107018181510044091000d071011076031a85440d0700d0f1035000511041c0041c1c0b40c800308820984c000601805a800c0c61032116105d100c0590b180c501030a85803000120038030440b110a00c02072030900842c071340018010003448e1218140400f1201080b51a0003001003c41d942042c080320158024043c290390345859840c0c0c0d4148d44032400d151628003603440d01504091040c0001034002008009035000710f2050040e242040d03170b14810b05505001c2801a0140300e0103807002001038650b07a500c07185000b40b02904603400c0a00038000101200c0719481452116000030383c2c280107030f140c42e40a10200600448004400010a40c02400e034202c25020b04080c010625200d5070030100d40c850815a0341c2c500c3d080c8401290384410520000e000c0c40b01c105003419080140110714100c09040b01c00114070140c2e115100d1000c40c0c0128005440324001d6600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 440280413 1250 440279163 440279167
    0x60209010e09070504150e010503070f0e0d03020303010e01060503010302010f111207080a0f0f0504050f0f0a0602031b0705181302060d060e1e0c0a02031909170106052202 75
    0x1c041d19981c41182c031a0006485481c2c449140c019204621000c5640c4403042260380c01208036280c1c0c01c002a03c1d04142245801200e0700d01000080e90444200003009501400c0245010105540000110b05170356036407050440c0ca990340c44042d5000d00080c00000e000c00c800b07a41d0080d00b41d100d034080d500c100c0000c008450600c034039003040c841107a2019009032410000015008031194128610305401001460300020540f06603100901d5405580101e40c4203280d94002010b09075108080c90000b06001411490100c1da5848065a82e0b404914640d558104159000f0700100d0042910421110003400c0c8a00c01c00a84070820b201003801070405500d104000700000150300c80d100075240c0004032080004003130f1704048078000d4602d802000a100d02e0400b240c080148103c0004594019944480098031050a01402d0341980a003021461404200380c8200840d2a400240001140e4499001d1072041000040035401e8812074024207403c40c81042c01d42103004003100071000b001e181c0d00d0b0014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 440281663 1250 440280413 440280437
    0x9190c0f090603021002150604020c210909090c060a03020306040219030e070911090904030c050312010e01060503040c1e0801050103050106240c03080a09060e0d02010c0e090406020901 81
    0x20004030803074116101e280d03500e600c14011401e00b4001e0b5501e03036480340024040c40011881138112880010000f502480d004240c586c3d5046040007100c031030006c8111000b100810484007801c490304a8100075108200c003202103400707480e0204108111600183c19240b418058074401c5c2c019600203085142c01681c01c00200b0300803c60b40581040b24031007a0303800b1414010f05101d861420089811060416140901500d0001010350485004450035036061003242e40f0741c04c1c1030308c40710b18400340500540000111200b89000d000c020034169201e05c59007a200c0c0c0d0301c031002151680421140241010200a41446000c1d0020741d07040035160310642e20b0b80151345502909003980c0c001ea004592aa44980d4103100d24035401c0b40c00d88410011119200074188a4400180070108084000d010b101004010850031162500440345331a000081800309a03140c1072440e0740d50150f07515440040d480c00703980030102c07481a20103000203c401081d50416854607200d40c0e000354400b0b05100c6c14032000c80c08403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 440282913 1250 440281663 440281679
    0x250507170a0b04330e01020903030d0504050111030f0405010f0c0503060409020a0f0b0c0c0303130b070c090203012c0112080d0207230721110f03100902010e0909190c 73
    0x502e60300c8100c507082e135441c0301c1c00d1040302c401e443c0c2080c540300159005012882e0030361400425038140c1c0c81c4400d400b0606884504000b8010140046d0560701250000b007045200072a03060b0443c0110b01c1303103008000402e002d0006000b100c0e1070703144400000e20104042015841c264100c2015280006c02c504100e40d6648a411220310455000300640d200204030b00760405004d0110489034842540598942010022032542041c0c1c01c2c081e21751020310228098040c080300c480c0000207000410011590f03543c4a0010240101208007003000d803c00308070070b44440c6c00312024654101e4000c0214004e542d451603036140f00c035410201c64000607075401c0c42944049200900082d03d40154805901035100b8845100741c14510141c0004218a02e0300d01d00c0f03504c103070000591050300c5030040000014400000001000c0001c060036041d4188a03524031200c00c000e40da0b02004d07455100b62201110f00f0f9082042c04110842203a400301650800454074000a95865205a550744207603881c101c00c81d143c042d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 440284163 1250 440282913 440282963
    0x215061e1210091a0f1b0706060b0408100b03120a0e0301140f01090c0e01080402030102120a0c0e030c031009210c030306080102030907051005250507170a0b04 70
    0x400c002c2d0329100c201030340602088110700d0b1102c140701d039003c0806241c11600001d1251014040d8010040310380c2c1c103401040c105000b9036051650000d414005203540c0c00390812141c1181c01080080d0050100c80040c00d4481e100701c82070305a015029040720400d40c03c0765551600b0801c0e181061140c8d411142d04155001e2092880c01e031104550070390141000150006130303a0058100b0112185402001d1402940042c018540302c2c0091822507200c1d030702d5101080c003a00a5903418494842c040051020351560341c2c0040c0074070307041c940c1c441c0c070000400020599105980508250550841c6280211602413a003120030420300502000e10100320030280b925074940e0461a41000842c4000100c0405915003c0e0b0b400030b091040095096042002c003194994040c0e105052041d040d51603041e02080c01030b0301340ca0b1903002e00301d401c0071f1a000d0340c64071510701391010310f0845403402a400302180074000541110b00307c0800f50014035189025039510420188083c2c0199884011440c5084560460b042 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 440285413 1250 440284163 440284183
    0x924050a020c1c060e0d120911130516050f04030803042942040e0102040f080c150f03060d1410060e07022d0601060f0215061e12 57
    0x40d80700d00201810304c1d204403004076a02c0f200c82d81000c00c8004950358004020110194000da002404441600d01004030700c0601d110150400100700107840862500d500c13052150f040d141c0d00121704d02c4880c41c03c42e402e1007546113460854400340010300124110b0400b640c1d00c54400c0f0006a407403101043c0016511001080380c5991110000c2003013800641b003a10450055420082c401c41110303410000c0350143c2c04500201c1461480c2c0c0b501c00501e0303941c0e400008004140c4030003150f80d183c403002d24007a43c4680f03009802d090b10424076013821a0804101d40e034030720b5004014050904055640c008025840a800c0d00e034003907402600b080c040744203111083c61906c0064000c0240c801d291a0150540e10283e102d03080c9824420200409590007081d20107590644591081d80d0a03050422102400030204101c41c4511660001003080b0703810841c280c0b4441e0450f000c40d1000f522084e0212404032040307440c1d6400030150820b6034402550440c9070000004014002a0300d0041d251605107020700580d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 440286663 1250 440285413 440285449
    0x60e0402041d0a06050406180515042408060705030c0d060815040212010912050f1306051210080d0e011e08011703030609061017010909030924050a020c 67
    0x1010702c840d0080611486004205c10349090141c1440e244403902d04520100c035850300d131a00d07a8005100400e102106504200008004001216412011500602c480d806001d1290602100811000c40000380ca40c81154940cad2400d24541c0e0390510218150020001c0307202e001d45440012070200b005105600034036820480003a00d0303107880e00412201202040c0c0582540e4504000140802d00703140e4207220054090800c1c5d41c1d50408001000403511617040c02c01540407503030b00d0102d40580d001c80141007400c480403040701d00740c40b00e020041c000e2280b8031904105a120481001080c1d001c0c0e05c41c40c1c94068141804070080717480f100070840541c410603804000424030401485284106620700501219041c025400c6140440208124000180c42c981c42200a0010781952920403141e06d0201c0c07a09803901d03880303541d40e11342650240003100411004220b0340301010a600050525014491b80f00c880740320a04285590b05541e42d92081e1044e804501964038031000303d44030020040d044103800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 440287769 1106 440286663 440286719
    0x5031c0b011d0f0a150f091d070302210105011803052503020a06170f0402031015050406080a0b07030b01080109020a030f0c1106010e10060e040204 65
    0xc104040d0700840701500401c84170501d1214000c580700d5520707080e2161030700e0300701960034241d40d020710185610400c101c40080c0e1001002c3c15000f08c80c45c1001440d0004d04000e042d00c0c484164898040c4003065001084956400b000c4020785020f910040c000c490b041d503907120f46850382c8080e00d14000140c4d06509640708001810b240085500810308201c4d25550280078024000c81840c501883c480200021000d104154580780b040d075000b0050900c0c400e006600500408130501c0c0006c4000c0e0002d00440d40d5243e41c8640005090901d000300717641c08052034519260300004004408150400200050700e9070803c16041c15910708070710168440d0880a0304500400c0c0c20300ca841c203202c0c01d00c040c8841058011040c41c141e08041029203c46a80742c201c1422004030941c0c2c3c4071100303101e042c400c20155125503202407200c04001c10151801c2c1c1d90b10b00b0a44403d1240010080ba0188 = true := by decide +kernel

theorem cover : BRFrame.Cov 440107913 440287769 := by
  have h0 := BRFrame.cov_init 440107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 440107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 440107913 ≤ n) (h2 : n < 440287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
