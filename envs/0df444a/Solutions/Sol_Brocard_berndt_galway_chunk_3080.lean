-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:48.93698+00:00
-- url     : https://prove2.me/submissions/74f4d137-6cd4-4e75-b8be-2f9196408c32

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 553776978 ≤ n < 553956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 553778228 1250 553776978 553777027
    0x1508010906020d110c0c0108071115061005071505040c0b0c010501050f0d110402160b01031410142404090804090b030601051c0309030213090c09050624 67
    0x70045615051034203c0d0290780305550030046180e04206031410f4155980c54000052810094074201080d1080d002b0464010018207031401c2c1e641040130141000c14402040d5547c0340201c42c0503192880040c428420b8591459200440750305000d645141140980720281041c0d940350050503000030466001e40003403203014502400402c8540c90700c0100180b11034030408150065003008005000101e09407040c011649049500588500201000c044a0310000c000280868845000070080c4899804541010000c81c4100d410445c0e120342c1c0542600c895080c02110424200042280700e0808245828040c46042c054003003c0d10542c0024103652070010143d491940008003444004403a025092030501c080d4014155945080c01245a882c80940d211003680148c0140f042010310403c0a0740003180c008001c41c40045188030318a00811583d0001c40b0120140c2800152810180c0205882040001d01107603103a03034000c0714422101d011349006011060b0411207202240750b03825084140f0348 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 553779478 1250 553778228 553778231
    0x60f030412121802090c041203110c0102010204030c0e04030c060507210203040206250c151e051c0212010b070308070e0a14010c02040c020c0a0b09060d1508010906 72
    0x101040800b41c0b00d000c440003201c49060502820100b010786101c9851069030b03042d01c1c800c0d610f68030000700700d9150081d504a1440124446101d9080c558400007035904c00c040b04090301c3c90800642c4c016402c074801c91000a000c101460400c101601c440400290300c41d000c4e00384a22085250f80d101d13070403210200c1d100b8010800040c0000d8007910040501710b1207654490007185942404d03000035040780144441421003a0f00d00042c01c4055030030402001c000d982c07142c042c1c4600e41d191022091100b4005007141b0005162050629044000700070420420119454040c545594103583d548190051982071807003d4080000c0c0d5048521061250b00a200801c9015101c02092600401074600a40100100304112503803904c103540d0040d060b0101d81d0891800b81c4142501d90050324144080f440103584645400140c81255030081044000007208407840e0032402d49500c440500360003180c18040d00000c060001184500b01c5a0010400180c0b039a400c1040f0755940382e1b110f0070360346a048100c4409 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 553780728 1250 553779478 553779503
    0x14010915050103021812031204110f030615060a090e01290a08010603020904180f0c0b0c0c0f0d050d110c0609010e040504060b0d060204080c010f0206070e060f0304 72
    0x60100c1000401408007441d055203815107060805540128001d0403e101d241a5110b400d005482041100c21000c41d4256401040c545070a005a00316a09801c0900440070f81001024500e008109113105034041480c0c0400c00070715800b40045904005440024014102000304484004465243c02460521403100451010500b2410300107108220301100c14000c0c082e041440c2c1d000101541910001e1a0040c0c4441828002801403c40c0e05402c508180c440704404042c000d444440c480c02900644030910090b40e5001400000c0c451f014865840350040490702c1c80600d400380c020300a0b000c0041003c2c2d0801901d4803014284000c0c02038100100c1d0600618001d07044e020312044d40302c980c0840d8a036007442030b0500080c014061441170603200d06d564100003810800d50345d00c800b9891002416015107514030b03140c41c000a501038041c81e400e07881125009a203940c4140100b088001e083e0b07000d0203c0d620b9010080c0e80b480035212041d0345c0031205000600082e04190055481580101d0501000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 553781978 1250 553780728 553780751
    0xb09070816050619110a24020a0c17130b0310080c03030906130b0f070c0503060606070b19150f050a0f1208120705030a0e07030819050d0e060105010f09210303140109 73
    0x34581e2607110501064018000509c4094000160000041d000340c0000d9003131000060078100f03441810014040e0044e0140045000e5007408055403190380c44ca21100c042c1a00c841200c1c0d034585c5220b21030b9a05a00400800c803007402c08038080d05070070b410112403003030301501d0b0454079200350007680c02d04070441c5001c11150b09012160039180c004240c1600a00244d0500901043d0644107a007000303012483d449020a000301c20f800e19401078030700000c07810880c141d002c07980c0101004046c40340820403841900040781034540480c01c01d088032014148110458604041d41000c5950950705941080f4140003000841041d540d14912881c10342d034481c0c0c0e46c0d14014072103800300c0e07100300c0c00ca1829034410041440002c0a500c02c481c400f2140c04002c4076000c040c01002c944600c1000b550800380350800000b40d400c05000210340e810382ea8240c8612641184031841101c1c202002c0c46040d0003104201041c80c40212029840f001c994000d18010604030403601e04d000a078178003039228500c080d0b51114007410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 553783228 1250 553781978 553782023
    0x30601090e0f01060309020d020907091a190c020310020703030203010918050606060c07051206011a030933040b0709080c0904060c0c0b09070816050619110a 69
    0x3410803440900c480b41480c21202100e0ba105005030010b041e41c0b00d5010066588075100049125402403101810385800e5000408040052041008865950010f0440386841070240c2d0101c04100c1c14800c4000c007030000071250f000300344005903014082d0f03900314440030002c0d0005080680c0607485c01740c1d482d490131401c242220131500510010b94a0549040005440801d0642e00201d003211100d48900740e800100c2d003088110b038407170340e4460b000060b070140702c0402061450480300035545101d80007251046100f910b01c0119030601454002d9566100e2035141011480d03c03c3c5007080300d4001003800084170300e152341425038096441d100c2079010090055404039651000e0001d4101070a02001d422001c03414000014000400700b070307141c4a49178481441390041201c2240c01c01800041410040e40042d10342580d40602c0c0703a18000c01072000310080c00c0d4004031084940242c2054a428440c07075220b031580c0340c4690301b0700400c20400050410a070081000e803036118020b451248107002640303103111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 553784478 1250 553783228 553783247
    0x6072a0f09060b071b08030c061e06010915020705040221100f0521011104080705060316030c140c0d030605121519090f02030607020f12090103061a030601 68
    0x18026400c040d410f01c0145030782d0b0281e40020343d001014004400c41d10080030801111134000340756500c408603440021010002c0d205014617540c828280301600f1107403404001010482d00540456000101085080208020540790075030503c16908050344a0001070180d07031121000c050090b540300d6002405801c1844015040414602d11988481c603102c000c20300b81f0003074801c0506c902564040040c0309240c5515000c0c0001c10b100003004465082d807601040381d0064002c0d880745109207a004509400e101c82240c5c0a051040325000100c05c1c050421409451009015020000300041000c070780c0c9102d00260840c0c41110000c0c062515440e1002401c0344d220ba40075038459181e4002460341d0500c0070400d1515070b0500b100c45000c41d601c04039800e01c40700610854820141c60480540c0922403001030002a55108400f50380700e90300d58417400c80c1d4504110f2603085645e08154900c003c001e0311840100078a0304103040c045102907942e0441802320107050080405030800200b0010590392002030003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 553785728 1250 553784478 553784489
    0x90305031602061009110c0102040f1802120f060f100819060302060702240c030a09140901091e0f0501080f0d051207031410140303160206072a0f 64
    0x50105103044c806103112004144100701c81180d0b20540d40300d1030f1281004840d07051040c0c00003591307201e644022010352001c0c144101d900c69192007402e02c00c00340003402142c0891000450760a40303034070f81d880c40d01e03102d010180560303600000085c0d1907913198503046112940480d06d900d41503401e1808a089410682402e084003c035135281420904c016074901c015603003440e406903000c1d4032440366a580c000f50a1240b038084003180700c2c00300300c104044c0c10020060a24500d5584e441c414640c0c1c2d00c24007001c07038900c4950a940b00c20f032240142300050896021100d000030b8144d002202d04003014600c001c4400b2240b50320704a03a11480140000c01082081c0f12101c8814002800b04941020f8003c00707074040c0204c071402c2d040d8050045a8141c1c4680c1150250040d100c801a816042000c1d03a41035014481c8034404081007200d600d041c1a01c1d01200f41e6414002d0280d8166034051584d08020b082d90285004681d184529581c030341010000e0b10b91030700c190614684040115080039104d250990103907005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 553786978 1250 553785728 553785733
    0x60601030905030403060c02070b03010b1806070b0630030301031a070503070509040b060f03040210050f041a12161101201309180c0b18130906090305031602 69
    0x41c03400a9000022541203e8010078001070807071003090200d040034559803058200504c0840041060752a410050080c072030004030589801602c1c1046c003c141c0100b0314064a00194400002c00b2820040d441c141c05070b0400808010401c2075160480121030700400e15003c0e0381c00072005008024204c00c80c4000112007017400d400d581703044c0c00700804a04c00207010300c1c01c21002141014081e116600100c408000c002c0c640790b00c0341024440030368150401c580903480340c0c00070074440f032025006a08490482100e10700082c0303000d04042c20340c0c0d0180702805808941500420000071031a000c1e00c601030003840b40c84061001c04040d07100042080c41d2800d8991a40e9140809803a40c618121140d044d0400d200c0c0e800b1a1030311440b80c0b80f061103404543c407400145080036048060701e000032082070f001e00d01c00c0f2030711940592680c02c410b030640100c0301900c0f400710141003c1401e030311340100200041c0001d00800b08401c0455620002aa206010110302184010013804114560300c0030049610100d81300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 553788228 1250 553786978 553786991
    0x3160305060c070302010e07240906140a050403020a080105181c080612010f020306190b0409020f040f143d03090507080d02010c1e050d020c0a120206060103 69
    0x559944401c0040c0120700d410000107112000c1500039048100d48010810540b00016903078042e4454400607007540c01c218081d150740140640b4040c4000006031555079035004082c102d55040c1100a500c03403000c0d00705029062000100581d41c3c052142d002d46090340011400f41032056240d072114640d0707107405c0300c0364005d40407501c02b00030401c0f5142126542450f006469480d0500454074800300d950811005508042d0711030340300609900110300912040d035a4011800600106905c21586406480d00d01c020420080040d1f1035982c001c1c0039180b0200201e80c0ca06584c803144020340700320f9030b480828134501c00401040b41e4501542c54546078161001111000903c14541c140411113100708000100c0080b07403403a100700d1195000e4003066501c201160304540d2134040182d580c07a000d0301d8000040d030030070041c00b1003030340720ba00c981c0c0c2036817106543c40c0300c950840c201c1995580c03c0b040e440740c0c42a50034004030b8150b003001c0050740003a50154412068030711b55030800905040c0001d20050500d1308000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 553789478 1250 553788228 553788233
    0x110d06080a030e0a120b0618040b0121080d050a0b1201050109050c070f0212010b040e0f0d09061b050109060c08040c0f1a030c2a2505010f1715031603 66
    0x841d01c0c10035a000300546c81c15500c00c00024841c18603241d1161559140c03000304010480c0c0d00071000c3c16500e40035007101d81c0c40302c4031540d1b06008000d00d400511440060194490300700d210340090fa0094001a0b000c104000014080b46010b01840c40036107050391107a0040041b0402440341a400c2800c00d00c01618006260712821200d04910500a00442501000c000307400e40a42c00907480c000020410301440040c180001c1d85c0345a030f11103214071801003a5409446500501001c8207c41d56500c0d15103020305d100380c503210400c68500e4151019500e030f441460000d082d5114064403520036840d6404581450f0910300b0010039940c00000c00d0301c40040e02882021608a2458449518090b4541c0e0340d41e1006002c0d64a401090741043c3d48105001d4800030000d113504200700c2d03050307c41c01141c070340c810100401c05030f2140310780842e81d04d0007100c441071045512558803011000781e01c3c10300398094895540500381c000b404403445001911111513500042c5024130011402144d103941d003032032050854 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553790728 1250 553789478 553789499
    0x509360609070e1003060f0b0a1106042a050a0306050106020607020d23070506010308070203060a090b010e09011b111002070803180f0d0203091003090c050103110d06080a030e0a 78
    0x1010024403d240d92110031241c54841c2d00190047d10a408028a8a079a12130144655030001c5080710003090140a013042d1400c00041c8092085810141900302e50451258011034182401462002d480d1a03110204050f10307290101001144182000103442d07240010081c01c0080c06403071641150003547c26000c0b241d6003d40c41004501c49060703c0c20804a4040e2000c0007031241e140020b0003400340100000c18031020b200039001d84c1d40240c003a00c0e80f40c0c1d6060400c104442803514010800180d24005000e0003107200c520302e0340442e100d000000c0174440c0329607111843c40030392841000103c400c0c0c00044c5414003402010111103804e00c0039030600303080d50344524a900000300f036a003e6008030011400c04001c204440c1d004100140162000d110800c0300080d1203030702ca4800180528000207038045030030310130321901444c0c0c1e40010031121b5075410900110b018010794115080440e00502c0440c074203060502c560401003185000611907c0824540039200407034860b4800d02c240c02168040084074150b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 553791978 1250 553790728 553790747
    0xe06070b160302070c030b0a0b0a150305281505060c120f04030c0e01061e0c0605040204020c150f091c121e0e07090507020d050936060907 61
    0x1829441112002401d001c030000e006004003c0e120805106000081c001600010350040b50f1400052052582c07400521603102d50701d00c01c0304107420001040c604028400c1e80110f41003040f05002d407855910703c0000b00001c280d12002000480d41e900760555481d1285103400c40248000d075010740c100022780720640d403144041e0f003408040350030003c0e884422002400413207026547c0b160280d03031304681356a014a05080240101d2000c45c007000c032244501c41201181556482d260354820340d079840560740d10005090080c2c000c980042e001e0100c00c540360000d10041000c413080f20429580d0385484600301a0061010f04049180d402205208501944550030b0003010200c900702410a04070b5903200d140103002a81242011500040c80c181d50103440342c01240c400c8401404480a440d12100000d048800036280c88001d40d00c56000c2d02ca2841c0520301401da2160001c1059518051460606130b14101d010440c10640c00054280c09401075410300e0b03990004011758045015282600c00a0140d608 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 553793228 1250 553791978 553791991
    0x6010f02150907030f050706090515040312030603080309030702010e0a03051e030f040b19031a0d051509010b09010e040201090b0c011b030b0f011b0609020a081603030e06070b 77
    0x10001d0029807000b104010400086500a044800403881414201d844515a005620018417841c00000b50740c9009102c1c070108007451012140780501d540c0e0f58802396101d4002c864240340c0c6500d00040440d031444086c0d441003032410080d550360341550ac00103000300c00b00c419061141e007414005101144c0e000541904001880941d40d1211390300e00d42e80b03859070003502c22158945000290100f042c8400a001d0303c1750354000400e036460902d9a200c1902035a2a91201c1a60000440713001c90301441c1090a600c0c01d24000c1341980d1006d07060000305000c50100f100c0c40125030707445c2c1400c1601070408036509801000d66516000140c10306034002812024248074850f0803200c00b04004d03141410a46c4285800600800b949484079013010014010f072940da4003843c0300741c0e4200300c0d6110b0742d4042c072030b148000104030180541c0c0552998481d4014203a801c0b059800a9141c00042286502040802850520a09034a491600c0e500d0020000242c0e116024062102031250308000340014465540005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 553794478 1250 553793228 553793263
    0x20a090b120a240609051003020309060606090a09090b060a05150a030207030e0d1406010b04050901050d140607080402030606060a1b241a0303030106091202030c0901030b0601030506010f02 83
    0xf2505610200e002c10304000b040f148030000b50000d0f00603000b407000f208962040d2120328a01121040c16800c90008965058403074202c480001c8052405000078800d44070002c3c440c6031401d03250000c120407036480a008848101d030800500c001850840c2440c002414100d503440c2d1012221111043e15000d055850f800b07050b004542201014021f00100ca0040c0c00500440038148171810144030b1804407680c0d001c1c947c01001c0003c100c040103101182e040e42c50140207925181d00c2c200a01062800b822003d5981c6c5c8820649418111410310040d8003c0f40250340e00c4843c0e09260040504110014045500c01c40c010001c901c451900400003111517056403214032000e41050804a07140c0c0720300700150080f4072f941c0c1254440d03424030340e1003515082c4000c10030b61280416901031650360b01c800c0c000c010214521110400c46164001d4042c181e02e4030140980f070b024a0810f002c1068500282c02c1250114901d80402c50b15581c18072600c0e80c0030700240b81045007076100400180d10348141481d0042a413 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 553795728 1250 553794478 553794491
    0xb0a080d0c0b0a06030222150602070e10090203070804290c16051c030b0d0c0b07060209041805010e0604020915120f0105011d06061902010b13020a090b120a 69
    0x100d0f070b80da1269000350340281c4041c0e03440c00546079a400d1b82c10840300d47c00c1040d00e0202490341c10074104444505481580d00100401400c151a4828000c0020302d00749a40260031004501034180780080c5002e407220b134841c4122400c1070714003290300348070700c101c2600c071008422814000c3c440c001410a8012489000c40c40c0d54040040c42100d1464106202400f43e2041c04d81600c0200d219003004c2d0b68801c241c0d0740030000c0600903001c000ca90000c5001c048c0c481115140280800c40340100103000c01c1d0f215a00041c40c01000b100450705845618031340400706010a8501c2c2c1c00e00600303002d82d9952851210152142c0d15003030b40041c1ca00070340500a42c01603445010080502d48402e14010500070700102141c6040c134a208a1034040c080034002c2140d001c006144a030036a1100060b80ca0050350b0003483c41e410481c4444941d034075520350082c6141150340329554600f0507201c25410418400c81c0000143ea0380000080140074843e5503440303004e0001c0c0401441d85d00c3c054551440c5e400c40c0b882007011552 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 553796978 1250 553795728 553795741
    0x100608070203120108030a030b03070506030601030506030a0c14040509010e0715020a0501090f11030a050a03030c140c01050a0506061804020d02070b19110909060d02030f100b0a080d0c0b 82
    0x19801407030f5404000c40804000441c3c6401c0000203032042e010296414058204020f0601d41c84008a2062940001c3c0500101c2c40c1d560083c1c00843c0c0c08a000390803604540916102c03070400c3c40071580710021124049941304001d040c5800358580c03045148000703001e03c5d5170592141d43d85500ba449002c000810318140b581080d8030a010007071031316400c100244035107000d40c14044030011416108440d0801c2d0b0105070782240c140460a000116088400b0f0400c9541a0300c7c00c0c3e02805101554400300b080000940c28004048805466185004000041c10b4a82203554808864000e0002841a40c007804901120b10b00d569000503189000e440140c1c6800c643c1440034080c0c000c41400820b00301401e404c21607091010800645d40a5804900780800c1c0da640843d07070307070f1445030703040d0250449405000209207040001200804610140c202c1d5002007000c50000d0030a4005030904007055220004a102c80c03418444000140500d140078040304000381c10045c018468402000700300004a1000605 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 553798228 1250 553796978 553796983
    0x20910030b30030c07150908070b0309010b091305101104030221010612120804030e04050405100203130212070f0608090a02060403080a1701030c051c0c0801050603151006080702 78
    0xb0420900040b2034840707600c100314644454040c06409840f840760810f0482280c441c3d500300c0211403400014020560074002048015840246103205d65901ca00c00c007680b68540311900c6d1300c1502c5039134800032002440c0c51704600303201c400500100c805080401c0c084450105100f220102c0780e0445004c00760943d410781c405c880e50258001406079520340507000401182d9030801950349803140411000380c8000300d4050307036000c606a901a000410782071104540f4103091317000315000340c0a4003c0303a0440010000a5081c1c4c1c0c002c0f5007803d04441c011007000f0450a0032140b582c103011142024141c840e080c0007418200300d4082c1f06030010800300101203a031f610002c1c00381d40c41e0640c001e440f46949680381c2c18035104e103502440c04071002900c52070841c0e070b030b550301d000c6054182e99100e1000503481d450f060400041021381002003000c001c1c0c8003c41800500aa4800002049002d00104036032800034201400c0c8606128041c100c01c41a004100220110800da00141c0310b55040034002d90301c071303001c0892 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 553799478 1250 553798228 553798309
    0x312060308030711010203010f090b0409020a1806050f030c010f1403040317180d03150e0405060f0606030730020a120e0c1e0402070f06020910030b 65
    0x4010514242000c03003400080d4008501c5180d0755104d0142e64500e10f001c0c40c0c01c0b03200074400c00050076406101400303807085940100139401001000804c108403550002200303500240e004294450b040f06043d82c05030500d01501009100c100c40030f0317402e151090702003500c0705080049981003054200c610003425026200300083c13201e2401c40c10380c49113007502d4041d0112001120b480383c40c0d0000c01c005443c0940451200040020000148c400309080d19000e4010b0840440e04031144110100081528550b42e01000e00c11409031004242380c0c18100c20040300400b000e019280038140800c10004e1311604012090340340d80340c105503091961412415a00c000c461030b1006032141d4000200c0a0315981e00c070103000c0710511065010082c052a403030312540d0325141e01d0100b03078010180c20b44070000044004042c02005c3c0c0094000341c0b0700300ca0340d0340345807050020740812251940d01003040c0d031003410000c0c0004c4c0c4500103410104600c02000c0c2c0040d14200f9120b1001c00c2220400e020142e81c0700f0010305e40f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 553800728 1250 553799478 553799507
    0x7083108161211160305030714101a0f010207030f08030901110a0c0b1005030a080c0109121715090c0a02101503021906210603170a170c0f0703 63
    0x221101402e40100410780e40340300a4a480e0b9200340501e107904590720025980469038040000c5141241c540e036201e018601200c0e02e64194001c001c60f19032840114040c52100c010300e1a03030381040600050400041c0d00c0c9100c407113070442d8010300341400014017030b002100c003403500005150344036034440c512035014000c5491103c00701280811a80100c47e0080c4441c043d5902c240400c0c5166a1400ba0104e42000b080c844c596065100200b0003001c1400540100940014000007060f0741c0095195200f0b04000704031100000350085054408003d000c450807a0420311000c4801c00c240340180010384142000380c4100d100980014940803030b18001c002480040138092014460200f1000341e840304d041513071000b64001d0024184010104481065034000d959050311102c041d032080e031060301500c03ca580801d0508690700d102c00300205510521080d20b500041d05501e940f8078541d0300c0140210f00d00e920907402d14110805000d051a000c03c00d440805650192040e00d404403402c00b103c1542e06081803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 553801978 1250 553800728 553800743
    0x10b0d150b040b09060f0409140307120201150b0306061c0b0f090c12040807080f04090606020118170417030403030f05070b04020f0411030708310816 66
    0x292410800d10216aa010308556501000512542414042a41c9082e110b859100440400203805131610400c0b848041c00301800018500c041d55958004078458204419001d5001160850030800c01e0030f081955400184003e110244000c04d000c03001e02d400b401550382e0681c000c0001351031030312520107513105508401d50f460030030400340481000805c14010521b00605000c40d2070070440c1400c60a4074050840c0c071460b20b150060031203074002d101d40050021070304e805c410002130012440b010702900c400e1058150080d5214903108440d411180b00394440f409590400007103001a48440801d02000da40200e100d03031846a010744500301c14451600504407030000b907402c2000351071001001e401524843d80f0782110504120700240d83d18081c8006c005d10800a10b000030300142050740e100ba0300001e024002145041080811694031342003254200001450380303081220703510840070340c0b54081040c842405410311762008140028903054502a11140c000900140700000d80d02440c1c00716500101e1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 553803228 1250 553801978 553801999
    0x30b030318090112021804050106080d03020d050612031e0405040603030309050c040204030b180c090403110d08150402090f030a0b1816121a0c04030b0a060806011205010b 75
    0x9841d030044445031185010700007820012856494101d001c68410703070000d01510040716504000320a111004004460554a80c0f07000141000100400401c0d0300c07450320003589030550080c0d0141100c60007050a07225220034564aa40e000340841142d110991011070288000840700c00403005d0301c80c60f4803558005191801c00018160705a11058000c0e10a0302541c0c400784004041005a0003607000c007500c60b10200020a6006510400d201e101c1c66164041d15405810440011a902c808980503004211603d004c12035541040c401d071208081c45017004c10103030401110414004403495503460280c0d6000031782c0c1c4010b9441408a03000400006c0403030300e1b4085146440c861300c0009a4404403000c80c0904000010b0078046500c9ea100d00d100012418014589519104514044541920072280c450b02c0503034404000d800d460700c12100010096950351a52424541002e4020241c3c000585000000d1241420214000b4112071161401068242040c2080d40c01443c2c00c0c400250320510001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 553804478 1250 553803228 553803247
    0x32a12020f0609061b03220c060e0d0309051c02030f1509030405030c06031909050f0c0301061409091e06070905040c020604020438030c0d150c030b0303 67
    0x300d01000c445000103481e03a5450704024240e48440a03161088045d40300080801803d40e1040a5548040c2c3c5484a00c1c540b0382400d81c841c1d803401e44d0041626200445103040c052143c10400c203a03004e003400d075100340c012101c0351002404440c8030700800d0f110f03030200b001b100551142d8030340010701507400030700395030501e18031103e510f0341d490000a05107100c944020005a42410103c00c2c1e5048850180141c80003042c41c4080000d50341c0f0040074002041003481c403d014940a40c800c0382c00c045e00c220014074455152081084ca09140401c807944281e0400c4000d0003c5d4030348140c0e01d610058250360b00e003529110706040508046060740305510100010080d100c1c5a0000914240507002e951100c407140d60311107061000b9a5a248031040240c0d000c00081070040c149039100f229040c0207680b80040d0003c03d00c542d1460800e100c03040480c41c00e80440c6510b2541303400e1256015140044600710b10130455aa1000c24024800c1710407070117075584041c40340019010303401c062580b040042c180da80d12807802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 553805728 1250 553804478 553804483
    0xc0302061e30190f1b030b010e0a05030a020904020d0b040c0e0115170a023903091305040812011203090602010b150708120408040e06010c032a1202 65
    0x1c400c0d40280d42c03507140004045250507100d0b405003401c0c0f04a11003d042c8855550040c0c49140c0c00a95180e07504c1504078007802c0c0c070520342d40d074413829664085001c07185500010210038052100900c41c11040170104806c0d07a0000ea104145641620848069502c0d030002030010b210003000035006d070355014108010440d41ea42c03c101559a01000e00e074031640c840081c58a03402d400b140d4000800c041c0e500c1d044854a80d00c005035486203814002500d07200c200e40e88010480303071030040500c0c803007079010017420054860030340a001620504001c40c10900764500151101d024122000e91f035030340d01c0000c10305016102c401c03141200c1403400c424400d541d50741c0c5500380c1a201c000c022b81c0002c0e41d0384008520300784180030341c5030803107801400c103540b40204039100751a5a000c030208841c41c0d0703000c10001072421021004548034030300078480143c07102c0c0740050b1040c60b150002c2100d410481105e5200001a030400103c99499071002d82c003907101c07540e0042000070780c851042c0c00b03441d45800070210181d890b0f00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 553806978 1250 553805728 553805767
    0x101206090803041a07030c0522030204060609080f011103070c0c09020a08040b06100e0f0a1a0910020a080f0d0e12031f24120f0902040c05070c0302061e 67
    0x2a407013207440d550307038102102120752200044002401c20011110310602c40d05520880c4908202c111986070f0b0b80e42d00040840c0c205602a0002c201c3c254030802060405000f40e210345c0c2e480ca802409003007040d0a550744a444018103110034048880c89000a001c0c2508208002d001050011035548811002c05803011030111400c4134142542c0300010700303d06161840d00b0003048a502d448404890010800140300307550175905070404405500080c004801601a03015400d00d0591145d482c007007001800607008042c0c0148042d58400781d5100006000c0c00212425040c002d0b039440e07100c4a40c0c40c00500a05420003801c0d52921819004102c50a01d041c0110f01030715070095200180070558026603403107055840b4240400d0381c66003176003101d0510f49580c10b003640401e24024001803903524464040f2201c01200800aa944105090031800c003442030304040c48282c1065428800305036141303484180a804000d00800c008549641008112aa91050070001c03c941030b454501c6036040d801e02050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 553808228 1250 553806978 553807013
    0xf050d0e01090b061c200901032907090605070f050a05070f0f080a08070f05060405240c031f1d090d050a14131d090705040510120609080304 62
    0x4408041a07140c50483c0c0c45801e4915141c0513508000011380312049100c01118812140080b41b03880300703c41e981d4145035103000c7c610074110300900030941ca0468950b011181001d5803c0d007030b214140516550420741321801c03108240760290f6130303981a01c2c140da480c3d441d40100910910030046410100680407840100381e6000f98100e0707640f10368444010203054840d00c11000c00f81c00060030038003c202000c000300501802240c1406030a420fa0b83c40074a0708804071819038154009001c01c0ca03c1e5402102d009154007680e04d4076004a0810b041c000c140c5200c003900b41c0c105141041d01b03c2c140810704802140c010600040c21000d0341e058100f90980e802d10445d00025680540c500304401c050080c030940c4d46000e032030307980c00007006e010403170f01c4100340c0c804005120152681000050b0116030b00700704003034001d6249902b172414108150520300e8800f0b25040725114a040000300180b200301c04c4eaa24080b240610350745070342c624032818610001d20181d9005420900e00000304405c1c4440704010702c60951 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 553809478 1250 553808228 553808243
    0x60304060212060105090a090906150f1a18120708060703020d060504060305060402060c0708030a05070b06030c0102120a0e090403021c02210a03020c0a030315050102060c07030f050d0e0109 83
    0x3d0781e034801101d0600c5180000f0b07038030003103000f402d02c01c0942c3d5900c05e16040344141030000c0c5102a1940c0c5d8207c07000741d5440400b178021141c60510014481149840c0c806100b06d002c0c81c00c2c17001d4604000400c540c3d4000c014006c10b494200c940300c01000300aa54001d00101c1d040d50560709140900402130340c45050803160260030100002802e041c60721690040320340080241c41d142e11190308000b0617501c44840303886a44035a49010030203110a00041403034003039607211296140c142c2e1404040e84000285801d103e0340094981503482d0b40c011034140c3d15000a40f8942c2d69451039407000355140f40c10301038440d421180203410401059000112204112100d47c40341c0d1003200550806c03039035007100031410100180d490040c03419144201024040319500c904000d810100402581440e065508605800103a00d6007060201100b480c681c1c080541400c0c40030b0f0640c3d00c0c00d624400c0062091800007000c00607903500b0070b44103030b21030804d8a50041c0c040350203100c00c1440716035107406420b0a01c4181e6486 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 553810728 1250 553809478 553809481
    0x90c030601022532210106090902130b030604030806061b030406080f011202060a030b0303032502070b0f1303020a15020709020918070306050d0c0806071b0f11060304060212 76
    0x43c032004c903001003102c00c112100c110a2022070078400c0e0000020300400c045000c0138803641d5030300428010700340030381611840060a0030050042101c0a60b404000700b40c22032409241e03018946000ca209a4010740600380310150303480300f401040651240b6114468249001c0c24564840d10000c8001d100300c9a082d51000b0441e111410030142c4030f070080c41030040c21209540e0440040c180040645060b0450f0b00340010b124400201003815540203e400c80100d01002a01400c01c821490a8401028462000700009400d00b50f036441c0911980c507054405800128100c0290811554000051540a8084407a4070b54402e01016990710042840000d40101c9401042d486618403c2ea6400311005010f21031610813444044601103004c0c00e01810540c035903901085035222010150035a9105119280400d464002441d061403c05030001040050b2000711031050416170b9500250680c200140b0030b024076852808200310883c18088581100e004002c000510a503940a0260708070090310300c032540d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 553811978 1250 553810728 553810769
    0xc090316080c0603070c150f06090207020a0e090d030b131103040501050a15030f06060b041403060a060308070b090a02150a0813030f110a02041104031e02090c0306010225 75
    0x43e40001c441600004200718410320200f9002c101c45100c031460000005001141010804244d483c0740d000868980c0d0002442011401c0116050000704074088104bc8a0b007800e440c040d403907890041e116070405442e00200000340d0b56140c00040741010045041103070012800e4400d241d40c100300c0c0d050340c965181400040760404140030741c07450b1081e10000411684c1c01c59481c64900780c02028141e83d065a20500494411642c400400c060301640c507090360800c000004040c50300b0401001030650604010f02000012840f1040e03914a035406107220106a503104141c52900c0d41c05140031b5071101d50161000c50314542000202902d0703042e45c0e01e098643d038500d020381c202d081e8042d00007000140c0789264800918031500710008210030200a550145c1031680026050300c1c0d04d9120800b80c01c000140401c00c0214070050018218100c1f8024144590341e0b800061070b801c801046405076940000000d6143e03842403207402101d100016481881545569403844645c006002c0c0700e0800000d40e018540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 553813228 1250 553811978 553811989
    0x6010f1b050705130c05070f032c12010b0d170f040b19020f0d030e07180204060225120602040e1302032122030c060f0f030e0a06050c090316080c 64
    0x1401c54170b5480c0d052900c4071960f1100940703404107406404024074807411826003c801c4107400d082d0080086460b01e80050102045245082494401c819030701d002d45440c0c1e291150f40c10344408a8001c201c0e6000010059070901c0b2900c02d406003004080d40000c4c0200310350b40c5aa01501004800c50183c0c0e40c00325001c081640c0c0c443d420241000301c3d0340440f4088600b240709403c030061540c030481c2601c030030342c3c0c4d185d2074182128010840c091485401040074032002d54100103008040c4004040102d040d6010f200790f40b2255018094108040c1d500703240d43c01072100ba40c044600418590000b0405450030180c00c200c03030030b0007481c103d11a00607103480c601e1b980800d154070402c0042448400345010080003200c07543c2400f07802c100501469140000000c0b440b1400303101b005100580311050040c02d20f00d0020b101c90140300024050600d8984659040100042e0869025510600005041c0c6603580d40c512140034880e0320700c0d454801c41c0d411444000b80c0c14144412500100101c0e20103104070010001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 553814478 1250 553813228 553813241
    0xd0f061506320d05100f06031409010b0112020d11070602180103060605090904060905060f0a110a0c1e06020f09090a05131707060207030f1101050c0306010f1b05070513 74
    0x1a8521003c0c414403580c01e089a10040d00038051888442070700d50759010015007240303541d02c400c01081c0d0713841140b0089250b216400d54440c00800c002c010114000001074a040b19421030104880e902150200c04080c2e181d00c142011041c0040ba151a04030900d81000a5841071550b6844001c003214508025402802002e081d0f075120345136581070100e91000e0142c510801081034620301d448410100102d00f01b403000c079002e2a40c41c1c50b4210340303103826010311041d1001c040d092030020ba8200700821859a0114048883e40d9015850403081c50003061415249104050064074040c400246040840080b030000c00085800380ca04c0ea49a654107000c030b60031144125081511800b0007142c183c0050b00c05640d1074802e82003c0d6100c0d060044a844a000300c0c2c01507901100803444210042284a80040c02d031b03400f00c1c2960000340300a01c0e0000d004030082c0005849241400690800b000031103000f0500f658103101c6111841103014003c1c1801c1d5038800b0b40b032050074006c1c00b08079245d8001502c64002c41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 553815728 1250 553814478 553814567
    0xf06060102030406030e1002120f07080112060203180724260c0d0f0b040b031f050705070203031908060604030c030f030e03010c0c06050907050d0f061506 68
    0x20b50034903207008000d401410100407010b1040c050481c1404558440388007800e6002003c8170108003503d09441382d11000080035102c40c0030f00c13000d00010080700d0031035503901c40c01503813141c4056203e417220400104ad0201e40a1404920300800c035021074230900e05064021036a410100c1c01448828010061720110441302803a41404051031003100c4013001c0e1089140c00042d802c440500e880d2113045520704845000d00c4003840641c0341c0e400a905882c01d07002e002580b410407030280141854001c00d4004103190412f50a24958440000484d00e6004209580b4183c2c0c0140540e640d5110312481d407110001003040840204580300d0105606040231815a0140d076844900c3c129440e0840c0c46030540444c41120841c200002090b1100c1f65882c20701030704404180700d0310f0301c40d062200d0f0720780303c02074030380083c010742c01075104c3c01c000c1103290384c0d140400403402e801014440c1400d00905211000c6c000c2c003e660620001d07014070004000e82c0c0603c6540c1d43d10600000341c00c40c2603000061210810015509 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 553816978 1250 553815728 553815733
    0x204180507090203071e020a02030d0e13090512070c05040c081006050f07020a0e040c0504020c0d120b06122d06011b05190c0503030c0d1206030c12050f06060102 71
    0xb40815031140d0b0056030420381c41d05040c24000628580c030a605210200400010b030061034040c4110308041001d200d0014140c02c0428881706002c010a40741811311481181072519440ca01e0306008003030144019070f00701d5004860b51080c07242080905003865110b501c0c010341c941132110328501d105a01c814000e6030700e01070b01c5951507c0c007281240c003604490a07107807403c1710400032440181e85191400f0003d05c0c403000008a03e01d0907061904441d0b2a075400300e17020300d00405c0360713060b0500f003c200718100c1c107101e0408070a0f1030180d40100009200e1140340c1754004400040032030300c82441c0e1050900c11034051040f00c1943c111a8401e0b010038854116001502c94500007090a0f50301409401c01d513200783d8419445103088a0301d46601c0d00380000b21000b06a01102d450409110030414441e000d00001e034029460300f2940644103aa9181c02d00d040000c00404810348600c418554200b6001550418400740680362555104a1f0741d4440e000101c406215950301030710800c07400320f48a8800e0b40140c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 553818228 1250 553816978 553816993
    0x902031005040f03081b03010e0702010b0a03240204170f06310807060f052715060a0902030103050c100c110f04110d1b050f0301030213020f030f0402041805 69
    0xd090701d01e010042e020f59401d06100c28904c07406c0c81c83d28082c5001313142c00d880a0083c1d08004002a08484004c07003114010f81c089941030007c91444030700b0443c2412807010f0000303802d8010320614000d010f180c20481040341c1484180380010f10008180a020f1150700c262071868540c4681b12540c005148e14100c03407140840f03c19040401040382210f04180948240c601d402c9440c0c0d030340c5048076480c01a8440d802d548006201201d0b00c80c20030005400342c1f01c078101c03149034010580c0070707500c001d41c40f655440505000002140c0d900c0b001c404100a04402c5070035034a0756181e280094440800758002405540d404404040161151000415031900200c1c6c11420313060402c14001c00d560080060740d085601c410308400d042c1c040d80001c2034403008054000942c00c3c104000a200b4402019940081140a00814514440d03d0080300c2c1107a50440e528100c60b0083c2c00c10001901461b5442011090040f040210745240c4004140c8501d1080b03404000001c00080080071000b0f42e08000790032a4403620 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 553819478 1250 553818228 553818233
    0x70e0f041101050f0c0601080c060a0206150d0507030b070210020412030f052215080f010e04030e0d03030f200a0509062b0f0c1e1e030902031005040f 66
    0x164030780074600061401a2030310040c02c1040d40540d003d102e904081d0340c0100b00410403070100780162805550111402441c1841ca104002e56804015115400300c49072104ad0b50324594800e40c441d943c00c0d52040a40b00a255030b403c03c025403400449100c0054001c80c02c001180700b885100f21001c2d5040b1014402052205072412142030104400d03a800b440402c0200003d42445045500341e5010140902031813241001d0914003d61070b840e1040e001c1c4800901130040441c0c0604105040d5981c990741c0c400d042c0c0e00e900301110440100c01000350880070005004052584c036400402400b10b0515040c80b1101c800d45009070850540c0c0310580100e1418421000418821b000410840c00b00401e480c1c20580591303048001d201c084a40c0c0314040c442420304481e407240a0080c8071155404110802079000e4050000d04815000c21504005071510a0f10b100d055025070701c02410340ca06440b940c1c11004640001800420307031810242e110744648030380b011075481030340541031299922541c1c07142e900160b90f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 553820728 1250 553819478 553819493
    0x131a0a0314190c140c1006090203160c03022401051e01050a0311070615170307030f0e0301140a02180f06070605060d0f05060709090b0a2306070503090102070e0f04 72
    0x101d1a8400c002c2d01300c4541d610200000d01a000c0b251604024203041d4000c40c40c8401120350542c88040502e0040c0304001c00c030040e221541001d02020b0070900c0044081d460101d0410b564280181107610340b8102c0d2580c80c4559070f43c0079069230401d6a110100c414600c0000a241c0000c0c0c031130a0000300100f111015061090300404002100000c60130b00b000e00b56612507064840d10f43c184200c0141070a4100541703d4024901c0c460358580034099480d24039603480c002e2441300c0c1d4450b03400c140f004840c0014080c2d1401d502030300700703928400241030302030a02040d1070029501c07064881d2480004081c000c0c2103403825102c03900010b50020b122925040ca9507640c40080c00c4010001c0f64048109680240801d8845010103406031280317011f0701403490241c201406070a620b0300700c3d41806e45800c44030304441e2248280d85c1c040d2100c021055000c3c2d00d044100342807294003c1c90058100350042080c1007040400406022840340903000d94450355141c2c80204c0c1e0080c2c0403210400602c014402080110f1f000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 553821978 1250 553820728 553820741
    0x21f02040f12200d05070306021e0f070b060d0b0405070f091103060f04110705010212152d150301090c0e01050304060c05040506040e1009020f07020105131a0a031419 73
    0xa0810366031813980344c5601e400c000d501c0e44140c8849030005501c80481e0900ca010301a02d80f003040c48541090a007000c0f074552400f416100170700c94551040401c0c2c031540c2d00b0036050501a07200015508500e090320b841d6840b07000310700ca541c80d0114608004211005503008560160b41070003074460440d41c80c03404010f4001c0020090350780042e5508040020307004003400400701d1a0240e000980d8400001d842804d561034018444110080b5202e495070f026a034003514021000750748142c2c803440688100076540e840000410340e941c080030003e803102c100d2041d90080d5040743c00d011802c10019000d007009456030210a914240016002c00c006030010311658007000004d08180340c0745050a840c3c402060255020303401c00d6940640c060b082010110b844403c14000e040e52110660604003103010941b854007541000a040c0400880e440042440d5408040002d002440b001100107006a0442d0700640c802426500000c0c00c2030500e0309502c6c01540c600c0d0040107055245480c0310035602c6040000d10700c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 553823228 1250 553821978 553822043
    0x3020c030d1e060602070e09010605091f051e0111030a020601030311120f04140d11040902180112031d0d020603041104060305070612062301021f02040f12 68
    0x20400b440c0e5002c981c0f0902028101c103400824a4605042070f044119030001d100c0c51050703051000c288141e45a10a00c1c2e60040406040000f116a12140c0e0b400c4410180d040145c21a080c01c0880d00c040d05030004565a005007a21620090310f00b40203241e440e803140018101c0568010801000040e126501300c0980c103070380c103007610031181c0e05410008055200c0d000d84a5a5440410103101c401d2001e20160100b20048032200d00c50503890381c0304464858402d1104d0701c2599030710840d806540312108055601242c4403041e000c5582c483c0e0107503010110f0100e041c0c0001c0c141691034640c0344940302c00105c200000402140313003a00d40368200611580028002c444e541c01c041c003070344055101c50054402440c881d0000e02a003a040c044024005070000111035455410030304100b1120084041d04020702e0b5500305507070416080000180e290440c0e005517030002c02c81110007603196441544c040c01c00d07250100307100b503d2070b5640d01c03c4421088c0d911030b01600040300310360a9001d21140c101401c60008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 553824478 1250 553823228 553823261
    0x1f06080601050d020310050103060b0f040c12050c0f030115030b0d030e220c090608070912020d030302040305030304060921051c2310150207030b13171903020c030d 72
    0x545039001d0001c0d60340c289d004491403926102420550b182c008010040c0c90010f45040000d041d8020005061a031510340c2601002e5403000130070718411621044850b00485001351030b0f42c1e941e64510040704980e90707124003000a481c041d03400d56103161183c2c02080c1c20360981e444003506d10700740c41000484425003098044d40207840700021241100740c09100350301c1c0f040d910b0302c42c0748501e085030150501400400703034010002114000e225112070343c200c0c0b1064903019250000c015074a072034290001e114580010380540300100c10003081204541000405500c44c0c8c088081b075640c2042810440258444c01760003240d03052006120100840748008880443c00f103020500c5000300c244a0210000070302001214501c0750200a2180d2250003010010058102500e40101000600079115009400f0080c0b103034103500007191002c1c00c0b001d64100d54a8101c026540c0c6442c10300356000301640801c074040b030741c0003000c0505180036000b4400d40725454140c101651404610f4483d0000800c0c0100c816483c81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 553825728 1250 553824478 553824493
    0x1303060606020d0e2b023001150e06010c05010f0236010f12140a090b06030a24061809050601120302100c120e1f06080601050d0203 58
    0x244103801484001c1038203801808a808489800800004e10a50400c0c05208856041d0201c40140d11425100c1000007141000e1380b02c0502c00500008031a9103e19200c0302d9000c0022803861032040c0340020001004002c02c810755a100350000c2c104c4080c4544800c40c158080020030319405030a40e801600d00c18400010950901015501280c000441c0003001c1c00303007440e28421803d0440074458950b104224180742003440180003d186c0c1541145802c00c00c42c204a040701e44018640000151841c1800041c4503032074040102401045200d90607104034007980081000b40c280820301040302c0e40c00281145942000c41e500c50001d0365007105d5101410740e1050f00040d015407a02c1200b114404030003010610b45824280645003207010b03000410481801c86840000a800284041c8140308002e000319400d200c0032020340d4005240c0b0b80d515811030400b450101c0001020840c140030342d038607040d0400c2021070303402c0c05011a900e50080b00d406521100061210749048052820038130310040c02c0300c042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 553826978 1250 553825728 553825733
    0x8070309060c03020406170f010b160b010305030909010b0307120209060f270909030d09030c230601060c051906021605070e0c0c0c090402011112180a030b010306021303 74
    0x888011500ba40c0002e540403c042c0501640700301c031b0401204207160105035900300750b400a1802d00045c807500842c40e50026011320400010124a00c009412800c0c82002d9070352030902c1130f200c0d401000441d03c10040c0e80c001048000040098a0084403180d48a0506422005402c40203510250f0020350022061112400c1e44da400001086840209200c20a1002c0d441d0150f05071890414400b920401c010001c01c05004000810346500044070000400c90519034241a50351101608001d04101d01242000d015070b0007c144000da049188000c440d482d1382d0341d2038111500107440c10001c0c604d81040f01020b0460302030070544003059004550061828561070119689508401d400301c0c0c09400c40a0100118944001010781c807078a80c0783e0861400e528041c68a840d29600d01c48584612284004501564030401c621000f60710300c40c045800100300381c0e00b60b800341d4200c000c180c1e0440784211841c103c5800d00c200c24000710b0303a01200c0103040d83d0a503900c0314041d40101e00302c0c0050b1403410000201 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 553828228 1250 553826978 553826981
    0x242607020708011a030f06041703101503050702061b090d0c0b03010609080f030a050f0706060b1b07120209040b0714070f02040b0108060a09021e0a021609050103050d0807030906 78
    0xc018a2002c0c044c140081142032504103455104841141d401220421021070b00103011680e07003100d4491450b80d40d0ba2a4501030000c100030781c10448003d15107000c0e2900d8250160700840c0030300345980848000e030717965104030340e040c0000214582c8084014450311800741052581c40700040c0c400c1001568068a4545c0c4448a4100340c0c030007000105910002c0010701000d00408458100240145207443c09440c1d000d0101d12644d0071410302c0340000201300c0148000381e401701c4081c046440c60345d0b0382c03180d00e800106884204407100f000c41f0b0081da240040d039240200b000c0344819501602c80047c5135140d840c0d04203c0c4000038000c2091080b030400800f4424282001000b4840c4a1841aa0246040e005100032142c01900b07060601580740207200c1d0076560300e901d00d02240c00007080540d5405031149507071000442c00705c0d45240b081c00491030032403458010034a009040c40c0e801c0c02d0100280c0d1a140582502c60a210142071600300b6810540054401c1c0003040d0301034800d05001c00c1d400055a178040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 553829478 1250 553828228 553828241
    0x6020c210604050a03090b090915040b100302030a140417070c0e0901050a0c020a17090a031b0303022a0405220309060206060420030411090124260702070801 69
    0x141d1079000018130720201500540c5c0c00c00038241c084411414a81000c021403207d00c000b0b021000e038800600c02e50303e515a034035008905c0c1254003074442d110704130140301d000d030180d04207030761000744542804c1000e40115120030585104135041010681c21851806008003290300c810300030b49403460300034000f2600880f41440140142000f200000d0f103440c102030740b00101e6150004e040304640000c4000004181c030000014409800d043c5000d50300e0294600160f407080042e40002c22240295141c031400c00351701100503088a02076001d44c2e5032900400780c00b01e034898074000441c100e0b00c2d0400b0b10b146c02e4101984a140e01c2071050100d588016941c280b9002d600d904840110000350043c4400d01215a060101e59008041501c09102008002040311041d0105e00300b0301b00d600d0b4001c0f00040901010801412540348042c085500c0fa58503a94054100482400302446170400c00c1c4400c90014840c11600166131120303025114900400d001d51080f05c0000307001cac10110710440c030000c1341c0e9071000c0c070450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 553830728 1250 553829478 553829483
    0x309060406020d030b0a0302240904110c100209060304110d150213080309030703060f02070804120308240105090d02040c172a0a11010204060807081006020c210604 72
    0xd006081c864040101075170017509003d4001d1001440400058a0305100ca4030883c08084908550101c00b0362010424095860019481828681030b200e2998180b0001d01c2d0940300d40059400c0343d00080c911070140d110b04401150031600c20000100410500d420700120b02e10014030b15415140f50380c0f0754844e840582d00d110000d00340c0c00142d203949820800c1154004000420156041912794000281c48405620002e0704068440644800c4250254110381a85a110800701e480d40d80342c9822a500c091401c0c41100800d600501051f405c1c4000003000880c220b0003e090351140104d50300450399904003a0400e9040002c0710201070042e501c0e4083c402050704036603107010004811040d020307010030019000103a040080c14445800ca5101d03000040c027404884106036503034481c40c0040721105090040d00c0c0c910f500c0803c0c04941240d0069405001c0d801c2035641c000c441e224034104951845042c803d51000d41e10002c4521100c3c1808224000f0300c4070080036100031116424101400c01d04101e504 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 553831978 1250 553830728 553830733
    0xb0a0308030901140105090c070302010b0d080c2b050d0f050a0507030f05060a05150c0102030709050a080c220f0905030c0f0303040f0215220f0603151205030906040602 74
    0x1006040b25092040c920303660701e2200705401651502c4c001c00c94803100940f061617408000510482454001d410410300c0d040d024240e0001e010305d42c2080225500040c072a408940203c2c9900d0040361145045182c26908240e0003031154001180d0039240341d0303c0807084041c46500c40011001d0a115489424460301c0d1071342021802e0301d1300c0400203048840080c0210b03400f40c81c020601c03802d82c0b55019103005540090340e107584412090080d0307200c60b002d040402d110560000041040040d404008082166405c0e42c40700b40c900e441d011300c152610035090465801517082d04002006003650881c1c8400d40c0c6100800007821046c0b00060429680000c00c140c1e100d038030010399100350743c0d420442e001102c030f5400b01035419030900790f803404e84004210710044d01c96100c6420901007440d011045a4020212440c40458821030300c0c08041065140c1c0305504482400c0280014100c0c000d01036821508140309500d4421428200000500303080035800303840138401480401d942e0703103610000300042c1c40135400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 553833228 1250 553831978 553831981
    0x3040e071103070c0f0f1406030403020a0807060b01090b0f0703080a0e01020a02010209090a0615050c0c041a0f15090105030408090603071206081c0e13150618081f0b0a030803 77
    0xb61710b4011725407584a03c0701c2c0303078011104201c0080540340040510404640041d81c076140c50a08928003085004003a004010001d005030070040181c1c8841d802c02800e885120700c85136194002c0006000c0c072a0101e22224081022100003032160070440d0748180640000a50b110a40503107a0881c2c22000c5020b000d070307500084511041c07801400d2030f9440140b00c0414004181040c6e80804c901c840e09105400307001011610300a249402d0000050040700030f0001c200a00c1044030030b00410385041c52860060451407140a0641002e2002243c81b03001d1806051a01c007101c00110790301d83c4010400d9883c8035040c03080c5030241e80c5440055008966580e00c505a40040b17441c0d042c202c491540c001030160380f000045d6015030140303040c41c6500030b0345e40c18810013240fa4100070500c00d8800c0e0510310309041c40c082e14815035120001d206401d81e4210350390b40d0030020064281c0315801c0c0395406503600c02c2c0c1c069001038130f085003007075110700c0004c1c1d90140104104030790702c001c01d907c45207980044850140100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 553834478 1250 553833228 553833239
    0x52113062708160204110d1a1e01090323060718050405041a010801020a0e0415030f030207241409010c0201121103040f022103040e071103070c 63
    0x289001c0d6140c41c1c5118106070714511002a44110103140109208000301c1c0a0815860420710a4000b41c0c02910502108050030800d02007a0310410040201c030386000030010510f03143c05190345030030101920000392010b030211031b03c0300783c404c1000ca5410400c0341100400052208130080710302c03130307150130181c06520350b0726840a09010300140408200184560b00e0f41c4039622010b2000c08aa01c05c0d600080d0303a0300e482c28051344808061950b403c001660740b00009180d0015802000030318403690307821100d80850002c0006480c800391300c0c851452059030040c00400c0341c2d40c0c1000ca0252007401211542d42e506c00b802c03070031811034515003080180c03801002d40e0744d035401220585003120100300d1613250440020001c1c20310080000e019040040c1210403180426003980098010030008100b00c2d241e00e4a85411240ca8036190400c84c010076025a10451281582d0080c04405000070065800e00d81848003488120500420007000c2000b9400210b40e2498148002e000b41801050019602805c10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 553835728 1250 553834478 553834481
    0x90a081c0f0810140d081201181a13021621260601030e01020708130504020705100b040f0612050d0e031e070f2304050c030705211306 59
    0x89800d03040c05a40010081400c4140c2c07200c4013a961807071010380c10005074402051448a40c0500100107000010306000340083d8881070134101d5036101101038844580641c0101076a01c0100000e458802c4030401020528003414550141020340000504001c803c140103480d00b4940c44060b0760040c240e00e20748080e2030f0070740108146d9040c1c0f820415070458060071500e460101116603400016690400305040e6807080e002501c07488880d000179501d4180500380400564003c00c0d0701481e4103081c1c5400601800d1a00a88407015013048c05810449800e8000c1006080740c00c407160b500a07075811062846000910502000d04640f00941642d030100e03141c01890414660020010302110030880300c1203942c0010003140c20021100356210141500403e58903104150304410b2001540c2c94010698403111040403c0b01240040404034042d01c04e014072003140c9c03046e112081d4500c010000240c500b80079600400141c030f01c07009400d10750001400070004d5200d0a80d4602104519a1803081c240300c01f9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 553836978 1250 553835728 553835747
    0x3040e0a14040c06090e0606160201170901020d050610210207021c020306060301092006130603094b060c02010e010e0106080a0204150b0705010903080c1608090a081c 73
    0x1b1045800034105100041c242e4040e1419000750800449445d00859104150100035420002042001d50a001001d00c0c042c0d000880c45040c03841c40e06001400c0da10b8100d420700c90071a12a100e003813030314a8240d0760701041684d49207000c2c01107400300000401602d8203098540d0f2100c00284014040c08036104260425001500552080e07060000c0c0001081100c0500c0407c0b203002420201c2a21400b00880e030140251503040c0d848000c0100c002aa840d00b6400c5002034911070903001450504031100e40020701c844441c885044642c45403014050160901403034111900c0d03011410400f901039071380340181c5c0c101803075400060351a07403001601e41a09004440c46151240006d00c03c441c103000d034103030391021071880291180da00c40d02c030b0f074001c1f031001481d0001030015880040e542d01042c2c113000340606042c4001b1000207443c000014500f0883e64141c0360140d69200700c00071046d0042c1c6070700361907030807407045280e02c0040d1410000709060100301d40700980d0a181020720b0004480000603000307101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 553838228 1250 553836978 553836989
    0x60902070b06040506040902130501030209010503120d020a030e0619050901110702040504140609030702030d08010503031c0213090b040501050105030601021e0c0901030f150e03040e0a14040c0609 86
    0x40c014100020050346400d40d012405580016199503401c0004010313028003c00070703411610085450141e2407032608024141c03030013070703420344007990703803903081c1944e0b0395201c4e80f00220103230144074000361030006170010490015940b40c0801c1d40c00511105a003800e00c151403001c01107520303202d40c040005680c06620750046c9003200800500100059100440c441d00740002d2207140d6810005041240a650462004c0c071007108a41345440c4c03201c980f82e9258000700b001d92003032007400d107000b00c428841c200340c5043e0f95001d0051400c000000000c513808122840ca209140c50302448000e40c0c0800e05504e4600518007240d0104556110806000807103006800890400000f007042020603600000d100e50401080d0107030f002c9011144c0122030030903603c021401e504c401c2e248000024012074100c0300e18514060807800803c0480400400101c407200c07a080d0344150014401049001c250200d01070380609010301c04500c180d41058408001001240c00700c80418421109003d01036004480901402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 553839478 1250 553838228 553838231
    0xd050609011401210e012c0610150c06020c010221070807080907080601090b0301050a050103050d050c0c1c031806050f1c05070f0f02060c031b040f0f03060609 70
    0x34042c000204151100030501c6161001e14500710b940e4600c80c0c0c007100c6042c8549000304801e0398120040354691310450300b0b40245022151520500401c007150300743c000c400031003940701420300e0103202e007214100d100300c42c00030300c00349060400c0442c60600050060340b025400044c0d03509a16005414800802011600d01b00484400c00461680002c400c54001c2c11a0400a25907030350010b159240c114541c000141c980101c1000142c210196003201c007118400720000c2c406aa00c01500e401250003d01c80986183e0011691003204e60082000707103214501030303045d241154500030201741ca440d41c1c0801b00e211440040001024142c0c405821503140c0200c00e80040d07014507000009010f07000310421844005000181c0701c01141140c0d50f00f280280302104c00780141c1c90595005007101544901d903030007060701710250500052022070124800d080640c0520b01b140c03504402d512044640040c0384651600401010400c200c00041510090150400c40100e1074110300c2c0100c162401580060000c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 553840728 1250 553839478 553839509
    0x80c090a0f1d0405060c070c0b13030303110a0e19120b010801060e160e04020702030d03060317040e041103120d200a0e0f030304050a1403011b090e0402150d05060901 73
    0x44c501180c0e941e04581121000d40c0c54401e2810808861450b0354040c01705840002207815242c5c0829403c40100ca000b5103041061006400d002081c5100c0c90002400250554000c103a8034a40418001905103c0d40580c6c9602c0c2c1d118110924101001e1700c040d07660030300a02c01041001004d014010207403608071440d03021424807604403030f2030900d40d50f045e40c00e05c600e00e20740074910748541c2d040e01c1180303030014119131140c001540b003e002010300d40010b8840603000c0341c039080d01304031507402c807000c0b10111312285101e0b5072940c44a403a000c402c0c0706250f40c103014400090811001c880050030700c650340740ca4005110a100c148048040f4580014412038190070b1003200110b60b0090780d141120366041d00d090141d80d50f0300001a08620594228540c03180038180b012592103c0d4090940c0e410b13500b03600806c01d0b09545141418443c07441e02c040d01c0000d111800030f10001403001655608144080c02480070038203002c0d07164400760000350990303402d0b590380c034204101b502c1d001250a0042c00c045880c0c0380350 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 553841978 1250 553840728 553840733
    0x1002030403050d080405150f070f0f120e0307051c0809060606041205012d0b03120412150f091101170c180604031b0f0e0106080c090a0f1d04 62
    0x4442ca402e020300c3c240310b030308000681402400e003c0340a030405028075108007032810905404403040151155000103413155000710f001401001e40c00400e548548404d03c1c0001c0e0168200d0140070b6035500119540400d10581c4005101005a2007a20805021401401c6800c4400520480b0003c001100503807104091040340d46030b54040f07509640c008c03080100c1e01c10746420b115024164941d508290341400c0f414850000b07007814803110200800940501148150404141c2d1f00d4041d98402c203c400d104000401182c0481a8200d01e4184104c0ea0380448151801e44c001c100c80044d800040310a8940340507c04000001e00949001c00090900c00360171092008a5600c0980040940712080c0c80010088002c0102e2380c140c1c01d44110040049545030b4403131030820307001214080208048a15594082907d502520300356080c1c40d25403a03246616031803e04102d69948001d084c050f40008108008104d0b44c40d03c8010070081d0445196455000703242c91041c1c24042000150100640b6074030742440700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 553843228 1250 553841978 553841983
    0x2202031c02061e0c040302090a2301151e051b0703030509091315020306030708100e0601300804180b150c0703110a1d0907090b010e101202070f02100203040305 70
    0x91b03a4040c1d558000a9a442e1132940040090494400781c813520803100c00c004400140340c49040c1c8407d002030030104503034548140c1d0051711a400b50701d50301d40c013a02251489031150015101c0c00076140400702c1c1c05100440e00c2420140c19820940008000252032a064140078444642021101036140e800c09000e48810180c4000d440300d000c8241e0700000850a10341d4100040c402800c04802980e945182c40c0d11020300500e81002c242c800c0740500000001c118000200c0300c401132801061040031440100c0002c048900070030750844000c8018040800c00c603a02c0c6641ca56420043d9000181c650804420806560b180f5501d84040390400c026081a041011a040003101e031b010039850500040280040d140180703d07003000071f02c011854966641c80b04425103013070003800c00c103064800d6151503148030401e81e20800030145c0891481c0f40c0c5811706081c44219a50005440d01d000050305032112203000999102c0e60b003d5420040104140c01580b03012150318402c01c26078001145010b246550b2642c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 553844478 1250 553843228 553843237
    0x509070804033509070602010b01090608100b03010312030b1512090f15071404030f030e0d02030f01020403030e091015030e030d140f2202031c02061e0c 67
    0x2001c100344000d41c40c0b10f9181c44400c4000a08003001d02568010300c01415405040c0101d9400101e8410981c00164090062281ca6014601a502d1200d406d0a105007070303a101402170030900c20014403050006030480028043d50180d031103178400c8103000103410f07802800c0d00c4105100314425510703100d110681d07500017401c9138030b0000014409021a0358480c0a5030a001100495545500549080a0040c4904c011240c80341c045501e65070f44445107031038514428000c50000407e0713400840d10140c0401e0040406a407141002880c0000042e01c540c0403c0c00e003040b542e105140b0340c0d0042014000c1540100c4500c0e42e0306000d460000140c60a541d14010750402072043d1400c241c0101c040941031440703071704050b0701109080202c0388d50710000c0003801c00070518040c5114001007030001048900340041a114064949114a1a400e04107211a014402d04840049034503115620128000403140c16410701c00d480f154001c0d000500c1c21440115042e44801646100c0307001410821485d000e00c502600c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 553845728 1250 553844478 553844483
    0x19050f060103050717061e030312060310020903100f0b030d0f030e0127150212070314040b040201141b010501080706110307060b060705190201111504021201110c160509070804 77
    0x3202072410010b01f4068545030082d03815020014050709142c600410060091400380d0481c0c561462a0103240c0480c019440c1082e03040e08107500207034092015402c55441d5040800300080c030f445400c0e0002c1c1c1f130301c01100000d80100d003209000c2040280c05200e80f5415109480003404580c50a4040c601054004a48520305401c454080024004189600d4008100da42000c554511240d121001000421503540000074204200054080301d01c0900b40d0190717a110f0030741c46543d1601c0e401944c103500050181d0f25032600a00986002c940282400c0e4540c02038003000044950402c400d683c24170155800580600c9002c5114480d413002c000104d950a03600000000f4406001c00d0006001d846512070217840392141c480d0100791651008a10043c00c0d10076202c0c20100340445604a841d00822a84140c42c103181600040241c144090795120501c08074000064000a80840c030300c45411803141000e01d540507914407201400d25504101c050401219400a1031901d100c000388904c170000d000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 553846978 1250 553845728 553845739
    0x10603031704030203040509040305120601090b070b28020c1e10020d020f0a020102030609150609040b0d0b040507081002070b06041a060d0c0909140f19050f06010305071706 76
    0x24040c10704c240199070141034010076810160426080c010302641000e00055184221203000c00c2907503002d138045c1012240740d4040103040180a8403458039280c002130a91790b41214000c1c0407403450070003001300c1c114194200c0b801a2180880100a40f034013801c1b07031440c0a2012410f8440000d180001030b6a0b200782d803241405a40d5412980307080d8047e004001465001b0700700415404401034045d00610f105040945441074140c0d00d942d003030a283d01d18180310581045040000d10034070700b01a00010756100c07000d03000c0c1c28103a00541c0c40e50000f0100311343c01e94254001d610705200d04041444008005c5010a07800d605201c0f242e1600c002d4200301070300c050721070303035448207480704184080b0f00340c03900c0000013854a500c5250784c0c01d0000c040d09440c6d00400000d69404030120300c115040c0b055415162042c51400700303959131004560700c0004007511401c00e070103150111782c05a0486000d13151103035403c040354150b030b42082000501540d001401003030070703c80c080b10345a0400e010049620f51000c800c4a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 553848228 1250 553846978 553846981
    0x611040305120f09131803090602060a27020301060b0301030c240806011d030a031206080304080307030c1a070309030f05030915070c061802180c03041b08010207050114090106030317 80
    0x5030070000c0c02288481c0c9904103c0342c81c80424990032048e0041116841d80039641c1075030700c084910085070342c28808524034000011007115807290715288445501c0c406000040c90366103610343c460b0030344c000340e204403140350b59040300380b0030061244140d60681c2050307011840224404400542104002420941041040010301041500d001024240d1850240c241d80c14040b00b81030092521035480142c4440382c1c20100300081c0e5481c0001240e08503001c11000e1410001036503400c6681402100065480202e4003203d48058504942c9060003814540c60010b000215440c02400d1040108034400a000c0d0500400c800355001103100c07035001c1d503039070000607030341d680c001055541080d40380c0007a0100d40f42c11400a0584c1140d048106400e008640ca43d00500f00421120707500001122015102e51050000c0f0300000c440300d118000f40458088080c00917922151300608a800c041c105232031581d15000b44400041c000440c8540201c80007000b4401d180c1113803409007686203c4152020300c402c5410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 553849478 1250 553848228 553848259
    0x1b0d05211306020d0b03060619230a06020706090e010b03162c030c0a08031605010207140d0306050406080a110a1508090d1803020f04090611040305120f09 68
    0x11003205030b64070680854495889941c1e100081c210b09203400d00901c25000800e82e42c0c0790003a41c51400c1b003001901007644504200105020040c3c00c0b03c081c4155919542483daa0f966005017440580071542c002c0043c107150002c01040320fa000d500810501c0da04200602c81403603002c0c1100d03800502c48a1005ea084955602154150038211810902c07481c008542c52518040c10104444400c04404440190b5540810030918095500c106071180e0310803c17684c118400b4210060303086034020070006040107402d4888440c968000750300500e00d50001a824201030741c15202c0c1ca00901340503141001081d0500501c5030780c903950048094600900c900c172001c1c1d81e40c0c40407000f002422000000d02d401c8007050b5405040644107a4a1040f540194441d400d8445e00c1204040741d90442c4441c0702c900c05145400f401500c8501c0e00c81d242c0c04c552522025000710340c490052020300c0000401c0300d69100e01e5420007a007804101d12021440711810420318842031340c280c00342c54040c0412522850302c000c245 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 553850728 1250 553849478 553849501
    0x50a05041a04032a0501140708040f050709090b0a05150105040501050906130303050301030308090f1203070c1a0907060201111b03040305060f0a230a0e01020f1b0d0521 74
    0x201c0184002c5442ca012144528440c101d03010095105000a00070a851030b1f44801841c0e0f41290320000045140001501194042038102c19060241c01980c0b41940c07950310b00e006490042505454540c030000511860180f90b00c070b0729500c891800d503901d10100844000914501c11071040701d040200126074121035036514001c13074407a0490a16400b1440f039580c42c01a00c036030001d00c020380210f50b0a900080c2c0e136500103d51000d5002c003601c098403010fa24070440c1c5000d5003014104108020f04500303840b0026510a0341294161142080b00f1034512f4100580707854a4180d40100c0f00f16410542e015811002000c2034030007200a0801415080f00000942407441c003441e40058190703c1610140700b5000c1d24655030a000d07900f200003e200c0c0e40f445880404202c001084c05595800c960300004000c42030a9000404200d5280c0000d80350079055050328140d600041103810304c1582e4900003402c1d0710020042e4021040590510ba420400d60f0038502d0740c41280381014801c030011a2001602e03110340c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 553851978 1250 553850728 553850747
    0x1406191a0301020d051f0f03020618040504052b051204050c220605060909190f090c051002060606041203020c15031006020318040f0e030f0c01050a05041a0403 70
    0x2500844d250340d4280a04000340c1002d580301c180c0c084408a9020840c0700c2803116005840682c0f02d19000141b6603828421180d00c00e510604400b4099600140741e80d40c2ca002c1e03240030381d0060004025090010395201904411451750400c0c00342c001c10682e40d06508042901c4240307490310a00725080c0d41c1e0742401401c0040c01042e040c1d009000500da51141c141039a244a1a910000c5040225a40301c209000f03191003800d9106d580b1589107130008021a1800c5c02d1005482a210008a803814031900c1c1e00d000e0b1244820101d907100c21401c0207020714102046a035112944500c0200b155040880201e001413089005003004a058182154240342c020001840100d4001c2c0006040f8541c00302c544111790015a03800b08038039080c84d000103140b8400400c1d5544a41c940041c0d40b224400c44007080700524000b080d00080680740c00b20807402245c140041d151000c6000f00c004d645410300c840442c2141c20042400c070b045031400c028000410200340b908001a0a041e84d0416a42c54504095440149 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 553853228 1250 553851978 553852031
    0x7020402070b01090c1b0803100b0406170a0209090f0705040b03010f03030e040501080c13180305070201021603030e0d060b0405010801060512060103350a020703140619 74
    0x111030307080106021525040314050308040013403910703040741160010500c8680507442001c2c00910404151317101e00464000e0412031004040541e240030200e203641103903008a000c00d01354040e000c80640c2da80d98041d030002005500318540b8040000040d8981070181204251007074502c0011121800384088902804030300ea40309840b5a0759602000d1512000c0c00100d000031124810500542414001d15050301e00b1a000b401000000030244800705008070b052801e100e840c0d11240c442220140301d03226006001e56107056880b00d0500000e46400c5d4030ba01e076034a03074802100d01080071a6000314030341903510048800c2180c080041c242023010303210300511240d10074981000000d0146056008004840e403d8640b1890320205e2501213449290911012b0700d000c8560f006011010041014008240c0100d607002c1c034007490034900c0203029000041c0031000360384010030500c1806460b4245d18440307c4800e0042c212440c2541c07490a051503226120032049441e51412707603101e0350fa0012140e0445 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 553854478 1250 553853228 553853231
    0xb0c2509020c12071b05031c0f03180b06210a0609020105040302120d081f0506070602130e150a05061b0111070303020714010b010504230901090b09161211070204 71
    0x100341e405c0909900f20015914030304541026800265802c1c0440c0c641d51880c20030003051180028002c040e01c90b140c0341e0304540e04040c3e4030310004150741ca0a81c4407010b0345005101d2500e26140810600c04503254070a2103c54a03010001d0714070740003100240c0e2561a60b80401c01041f489098401a83d03140241c0d04003d51011002c2d00100c400c400c0040c0180a1980d82d0340c3e001a203440e4513144c0300c0e107031041d0f0000c50081038082e0028800b03814018018a80c07a032190720018505611010000c6414419400c550041ea4900c1e05000880a21401554542c1000c03030785100b10928100020b21035208840034827050400302000501c0e2802c0a620541b804880c000d081982c07082140780003802907002d481c0403159010301c1641030710701c034105205600c00c111041e1680c0d8079050605440b030001c84400c1403c510128075004c0b4028254490985980c000c000e07075680410311180d080100302c00090020080994600d1310410101c40325882504402c41007078030709000460b2060000820300d20b100341e44010350400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 553855728 1250 553854478 553854487
    0x20d0e07030b15011e020d020c1f0c0507090203092103011202010c17040b070209100f0e0c0f07211805130e060c03070807050f0409020f130b0c2509020c12 68
    0x1c0e6001302e035070742865460341d02751447c001e0144104441150044a0144203400742d03844040a507001d44800c1910030b00030000c440c0401c1d52061080180d1b40101c44417003681c1c00c8461450b2a1543d1085116000111111408d00f998100f500b42c203043ea510702000b034100004000340d08280888408030314108200502280c0e95592501a00080c3e5030086208a0050031543e0001c1d00c098900914141030380e03a0350790646034003840c0c200c55048245c005000c00c4c6a502c400c00c943d031010710301e420003010000e101c0e40d03a410b84070861490311081c10108880070750511100401c5010b0041540d04900283c40040710451419641104a100181111041075801c3e08c110024841001c0c0d03a407014510030314080d5141c0d00c03ea43c86040c2191103004014200c1040d00c400e0100340413685854025180c048006c1d40b40c641000c0d8503e1080c02102820347c400302c0c02c0c81001503007100b540c100340f000e610b00080c0c0038002c00c0740960240e100284e550040c80748075002680410140d4032180188911a1602d001c5490140c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 553856978 1250 553855728 553855787
    0xf0c09040f0218150904050c040b121b01111c110c04060315110403050615010e0d03120609090203030f180a230d02061822020d0e07030b1501 62
    0x6084c4c5044840c034580e031406904a00d803005019125070380c403a0241c203007015001c0510014103040c241c1d1580c0021400303c40306a560301000945103009003995050398195104001401c90700c0007104862407500f09680503891100191200c1000c00a2458030002e07032a803200342c1c40c5c2080343c0c802c5200d030f106003800000801d00c022055804c031010a0040204040240442c9043c014412440300402c0d54101000081c000403820142001301070060402e88400d100c450001030b41013803007010440214014004081d21081c05120356005402a00e40c10080f2a000c0c1d00001e07a28003c400044188402c0041c1d051019841c1c4070b42c00002540c050803e612190325418401804855400e11140b085c2880c03005840c2c45c40e006540188464024100ca40382c45080403c0c0303c218041d40c0c61594216003002c8440941040c06c002c0301003800c5102c00d00680300c0c86042050380c10361b03485100503912903010f0074050020034111488a50004025080034038a83c01100050350340c03055810621100b051904e60391040e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 553858228 1250 553856978 553857019
    0x2102040b03010519060801060503130803090102070c0f14040906020903240f04030504030605061f0306140303040308040e0a111b0606010c050c240c0a020a080f0c09040f02 75
    0x42c3c500c02c449200400c00403401a086160b154030408000491600040014600540055030410030850070049d0444060304c13241030382d82c03003500c204400b0780d80050648240940466060007420003000d15420042c50002981111905502c3d8030703215581d40c1401404100030366040b28014207000d0306688404528440e40040787d64140341c81c81245c900800017490555040c900b040c81180d040d2959410a821a1a000b00400e0014803560b04049501d80111482466a130400741b50607080e03402150050608e41c0390340b5150794121249020703074030503c001d20000d082c40c0d065800741e4640746804000760307907001d500c036025281202d444929003400040c9041804040c00790400300056100844090361100300c011114422541c6001d04240c1250000c000320b89000c0000954181243e02d1540584440b1080007115900034041104070780d0241c1005011801c00441c41c100038940c0002400000100400742e41d1540b022481d401e11034030745400041c0410913140ca540300d047d074001c0c0c1200c03d4071800b0080f40c138 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 553859478 1250 553858228 553858231
    0x190e0a14070e010b0307021b0402071703150609030a1209030f030f0f0c050a020f0102010605060f070308010501022b0c0503031e090a03020c04020703050408060f0a05071b032102040b03 81
    0x228070625000801d41c00707154400c81e40201051f9008105460003441c0c03c9540003019800c040e40309070200030210102d44191018082c5480c41078089a89003068140702c0c84600100304107a0190100344811411540e000c40c50000c1c440d00304038a4003541c10342c040111050b0605400050469201c1820790003070590148980402062a8842c031010107406a41a181d04042d890004e025a00145101c07005040022006000050600000c00c00c03d40300c000003409508a101c80c60069200840d1070801d040d4098041070042c102800940000e0050400784c1c0c3d441c0701440c100c0034800308085c1c00700c08070900c140003100c00c0e143c1182c03e03a03440e401d081c00c000051001c055180009011742c500814001c54010420090301356041c3c004114070061078041c000a1f410a910582c14403c0c1400001294030042c0314461052000042d01c41103454030407001001c50380c01401090410000c08510280c01e103510485ca880a905414042041e40c510400034070360000030948020410b00100340011980035400296 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 553860728 1250 553859478 553859489
    0x15070c0b1909081906022a010c03060e0c07051f020309060705040f1707210b0f010e0f1b0c010c09050d1a0408070209040803060414190e0a1407 63
    0x200403458070020490340030300a400b80010541200070401c000c03803811201c1070341e99131142d003015080201c0c41480c1390318010104a488001c1c04441242e00c19501c1c00c0c0724440c8808801e0608002c86803d0074000d11640c0030003812880d25540004012060000420118140219040e42c0c1103095070f034004454042e4005544071000d03449288041450223009100f42d81c195040c113100b0305145440d01c2c88403000703980020360140c11401444804a8042d201004a03060212240b1126a2044103464100880040180090700b0301d400c03d00103100c0e48184103c0290405811564022507841d5114403081619580c00f10f600070200020340184c1500040d0031441a51041d40c64030500242c0d1201402000445520002d01d10154105054420202002201c0c2c206015449090030b0840e2580401d0f908042914150350307003c5c02000300082450203014420071024200e07030080c49401d16014003060f080f044150504403985a180fa000d03c5001001914011608107040140310002002800d888007640d014a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 553861978 1250 553860728 553860757
    0x807060204080d02010b06090402090f0a080a0302150610050f0d06081b040216170c011e0605040228050903240606040e010509042916180515070c0b 65
    0x3901034018440c40010000281c070041c230f0a400c58041000035400441d030f840c0d00008d462506411034907413400300030107444090f0040201030303520309000e40b4084040083e4850350b4041c200300003440c0c5403001060a40b4600381840e513290000c00002c0030850141d840780035400d504d0444000b400c6880001c41100580c030030f000c0c0081d08201c071014802640b1031204030b2040000c0290100300003440d110880704840486c6070001d030034045942d041e1070070740e81c4480312456103200e02850700c1499603042c4660401007100712411803400301e0460118800300c0c0c5680107008062188020468007078062001c9505e5044010103560420500c00742d52294449038040203d40b1070680000100c89041960842e001c2c0e43e00c003a18809140e10300030802c07200c0c07000108216405001448090300c03401e4000004015200b1040742d0390b94030700d46400d0384642d00c50043c1d440c03000c010b44520041e10306401c07150b5660698200340c6681450a20000070081a072099a0006082d800c0d06000064a0118a0003030b14040480000c2c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 553863228 1250 553861978 553861993
    0x290907020316020f0402210601030615080a0b04110a03150e010308030a0905031b0d0206100b0405010c1b03030507060b0f01090603050402040605030f1501090212071803080706020408 80
    0x20890303490046041d80003003141c042542e40094070700744401809045000700054909180e100e00d08000b00d082410711200d4030b42c94000e2281541e094020b2001070501308a40c041c1c0403c1c480c5005004400203065203241c41d81da80b10044560b2215008400c18030004000c0305d6540140c480b0080c0180340003450110f1400562401281d815a201c0a030350407250400203c90071500c0b509811002030410407411a158881004800b00c00f00040c4c40150b20b104a883c05001340c0c171300c1c10030040c1c00c020004203100905203908400b0301c0303001101001d40301580e1003071820f803240d4240ea15045c0202c0391a04064200d07400c0e032401c00000c060780300c4e000300034a500c0b491084c08903400e41007c3c060310361440080f8a01042d6a01710511109219600c5039a0041c001000801d078140d4903c0841c1c1841e00c0380c10651441e421607500740081c0c00c01c5c1b81d400c81c01044801001c502c5c1409000910ba1400b03000703001001040341d91031110180740000c100001c0510380040840d0b1b964291440c184000354054851481c49026201 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 553864478 1250 553863228 553863241
    0x9021c060e010e0c011b060f0911030604020127080304032a030f08030403050d060620030c07060503100305120d0c030e07050906150c01271a04062909 66
    0x54014101c0d0f0080c001c21030035815030f00644251540d08841d07211707040301c0e05102c00881c182d0302441071482c2c0450b80001d002c20040c18020107002403c951240298841d405110050340d0220b000c0d40100b038220520032400f98840c008080c415566401080c841c84049400300512402002e004e81da1080640100a211041247c2c4c4241310170b18880a00410804011040400c0e0300b00c0c01581d01c24030903d0030514068030340449004407000c64000000060300d0800c88121082000014015000901c00540c20050f9020160365500514024582008004400300354904a1003140714055035014094031f00681e24101e090720250498207189106a00b441081030029000b40328040c0445a4074000e41912400c15080c44180d20003d40503603041600d190004108280001c003822809800b240003049000e1064404442e5900e440290514048098091400151941010280100c0e4010308004550f038508001004101100c15840807421002001c82024604183c0b02c0b0300000c21980941192240c3c3c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 553865728 1250 553864478 553864481
    0x3c0e0a1a09071d040b04140103021011070504090215030106020a0c0e09211608040302042d090303150305030d05090613080f04030501110315040b1503060409021c060e01 74
    0xe4031010b0108614201c0b82d00d8004080c00202c07100740e00a0800318500ca03800d03020030211421250700c1c0c2140800c042c010301c21071403c0e0114500c2c80c0e4a5280c8844102440440c00307442d81c806206a40c805c40d42c2e103400c0c00031034a555058000e8030203880002501d80da981d002c040e454041d00c0408079100c0b00b0110300412604003151007640950007040040100b004584101380342c0a440701080486c1c6041801341c0340d182d030f000440c2c1c96106d40c45a044a81c64606d9407040c030050740c0c00d04101d10170f10030300a0b00c8805115203039041500681c205c1d15000c41c00314602c1c01d0035070050068440b0070b0342222600c5804000e210000006003c05070045104204550720020225210141036801da0407500c00c008900c0086491400600505031072810581d291035900d640d080c4c00c48104917410200014040100400c40d0394808001882d031005071800e00c090942400015500388000184144075200400403844039110b6500895060381c1c040c001e10341d64135403000f5031494049120403c03140d42e03082210318440484107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 553866978 1250 553865728 553865731
    0x200f0c01060b0a1e020703020306011e080304051804030c05011104030209160801050d03140a020706110604110409151e060f0506030612030c190c3c0e0a1a09 69
    0xa03030b584600741d40c403070007003109056507071413003401144100c007400b0000da6800d00c013450080442d41d244c141a80d0324240c00710a800002e901581d01740d0004d100811290321680051041b91420362031094942c0e8441c5000d56100ca0b22034000b800942c41c15019002c541000c100a04c16603000320f49101c45583e131400c0c2c038201c0c0382c02c04086000080442e00104441d040c8240821003031031080c10708d483d6800c41b5040804458018446060059101075004c0012a030008103000d2501a000003405252505484007444c040840c0200f6024681ea11030103030501407440320402d0508441740c400d10074500c9500d400d0343c408ca03c840300c41740c100e40f61050000d482101c12889104585000d81100d0a50703075a4010410900d43c002c80b94000c50000f00580c07a6034280600c0b041c0c8515035140420700c5028681e09060203e600d55801c408400303402e402c2100c2c4661400790f08800220001c0e0307402503e4014142d440c210b0b8007810750000c2d0452800c0801d03c221400329400803030200701c0b86221010310341104410081031060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 553868228 1250 553866978 553866997
    0x16060209041a22020f070c061e0807080c0c1606090f030302211905030a0c171f15030506030613080a110a0c03030c0302100618200f0c01060b 62
    0x214000d031110780365800c0380307443c07010005100504200d0154288074150f8088141210f103650780880600c42c080c0c103d20050f11800710303001d1520f04d4600c9400c01400034100507021000b030182d42e000040c80c0150080c04c513103000c0136440958802007000310545039881c07001e000310030115011800120b260525141c0c10b404486d0194010030041569000e8500604200c0c96501e041d60b0040000c1d0b016403480210020540141e9502c1039501e1500304000c0c0102e40c2c0703204660080002080080503508409200301d6000700340da003c2140001300049810070403510700c1c0c2c420074850424000b60003110307800d540702502c82c1005405440d001e80e102c080d003440781c0385c449030000c204103010311804807e070f441040e8070725003451030740102c0700f0f2074503952640c4400f00714540c01180010403c0c000c08040560500105000c00e010344000d100d070134100401804290340010748094210380d184900d801103e0402018101f4815461085039100c036607050302c00ea0340c2d010000c208806c0d03080500005082c2038090450b8078000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 553869478 1250 553868228 553868239
    0x509120f030706020d090206070302100e0303040f0b092e060e010b040308071e1110230a02030904380f13021c050a06050909030a050a020316060209041a 67
    0xc00b60380c0d0540250007494032001d44a640f00070100060700c440005280c014041e80003030100303103410181c0b441540da41924540d0180c00900a001c0010a00c000c6100b0a40d40324900803100c1c1c0c0c448030410b203480d0007080815042901265032140c41b00344410300030f00d20b00280205104140e110507000d004a01c0a04c1551000c0f041000100080703031565020b880f010388a103101e802d08149980b5000c000581c81c1805840d5030046600601d0149050692a040c1302000d0401010207541c00303140c001d03600003001c4580391025000588544441c402d00454402c600014170070012242c0b9114100d880c0c1c0d48401015a142c5da6044080e0481f1050074513a4405442c01416480700c00d034454103200a0111000701d00350026001c0c00320080503442803500c00d162501c421400901d0307280035600ca6080c0d60311584000d005203140c00600c02d2594021044a06000c41c0d81045940c5d6030005600f01d1071840303603001403245110002201e070b081211680042c000c100040b10b00340164005030300714420080d82c2c80813165000c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 553870728 1250 553869478 553869487
    0x121809051902030606220f0e04020f12010e1e073837030b030316140708060106090906060e0405040302011e0e070b16031809020a0509120f03 62
    0x400c160b40007540d004002a145d5400c0c808200040d0824140150040780c5820301441d084c00018602280a00203229441440005040c02e0300071504200340c510300300c0c0c000c04420320386405041d025004035a0072045281241d5803060f82840b080b03c0c26030800810003d60140440000d41c0c140b20b074540d4800c40800300005865a115800c0448020a00d002c41140404040c850880079042d00c0000007415070310300002c2c45044503000c0005000d05000c3e0700290515280403031110a586001050340c00121030440b00c0e012131003141c20512014400c00b0b541e41032a12600d64081110480858102c1c100c0e005a284d407107000380c41d080007134269040fa004040c0024010858406c0c94030305908075a401a00900002a0351024400500351605c034140c1d1444446403200d0800001010170401100101255040349040c100c2d12000341080040001002e400c0201210b44107900782041268000101039012086594805a540191403500194182d07880b6010150841e13010440104c0c0350681d0184002c00380d0300c0e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 553871978 1250 553870728 553870771
    0x3023a050304051c020d030b09011a07110d030c030f020c090a021b0d0315120b0103140102120f0604150501140c0304080a0602042105070e06040912180905 68
    0x25007000340b099405100c1c401c010890708110351007060fa00c3c0029400340030062017900c07015040c2d900885001d0301454003071004210101c19000198207842143c40c0c1c0030740c2c0d541c403070400200c2c000c4201c1030680c4c0400c92703104000401d600b213000492a580709441c1c0390000721040e00243d8039903810110007030f00800742c0d00c00220340e0381c1954000e002da403a425110300142162081c100d4500f003034018081d00840e035910603000010806010040040100318840e05036410a9a0340e40a2130a043c48000e0201c0c41400d9401609034003034060300c030b18408442d040c8070700d40b5002c0a15000800140d035440c0c0118a01800c100080c81d102e102c05d41941c4041e100e009403255034000c0e00042d40d200c6504484c140c0001d100c041101d02040c064030018500440002d6103903030411045080410300b503040b82c044202503d1032200001c0c0040b0340ca10850703044441c51801c0f903955101003405407810000c000c0c0640702c4002c8400e00c0540042040300b03040c40b8085d41d080901c0d00c40e985a03080701d500b9240b510228404003180c402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 553873228 1250 553871978 553871987
    0xb18070314010308041703040b0703030908040b070606030b06011704080c0a0503040b13060206011203140405120604050d020328020f03030a0e01050a0908090405060f0a0303023a 78
    0x2005042460002080070314071440645039002a0401c071851400050100a00380c0c004104000d0518004050b610b41860301e581d002040c07050800040c103058450000c541031200f000160760052900800d515581c144a1800c00c00420860000326525101400400c0c6035502c00c00a900d03113001040102d0009171203680740d0309196009802c101030355108401081d80007a01c01c1c0042c000400a92440325128018001c40000310740b902c0e00160704540c0a6001048200901d0a4100440b605810b01180b6480401200300aa00c243d802940c0c010300306a40c0c0155030100020b0881c8254040e005a50040c3c11000c2d00301d860344682e00d103211004003412118040e89148099040020005004031809044440c03206415a00308448408200d540c5200702c5d15954000c0c090554400307022942040310502c1565401c52500421080a010381e43d60342c0002d03144e444d03450700880514801040324400070354034a0000d64414481251442640d10030301c6006003048940f000d40400108c0406403145007200d0003080f88c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 553874478 1250 553873228 553873231
    0x151306030f1407180e071e09050703060504020f07050d02062a071a090c0d121b15090c090506060a0c301803050325050105070315090b18 60
    0x8086004241c00056a05500c4d00410701c007010300d0101140540310050090b040c018941d008010240725a400c3c0c0b03140c2450515100162100c0d44000501d0f03460b4000214010302e01a0041074000d0320001e80d29801003c142c01514560f131041e003c4030704202d0310240c203e032211001e803100700c485059a80000200380034041605c110004400c81c1500301207064948200d40c0006124007800c0b0b045500901c4281801840302e2118500186d500604038010b42d81c2c0c00c0078012a03120387d4800c01ca034244200c00311040006810403450340100d102c04604200b40e24800080c91420011148030220b10030011f0400b03258000d403480f50320b00604050401c04064820340301d180c4204000c45004e023104502540ca4011071504603000980c2c42c0b01d030351651944c5480030f40030301800c28034444502045401080040d400104403000c506c040d82d50007200c202109000759402c0303003130303800101139509103010000816415407120781c000303040b01108145160303a1180d640483e00289400d54002d100e4004241495220480c3c06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 553875728 1250 553874478 553874513
    0x9070e010510030e030406201209091314010204150c0807110312031005040b030c211009060e0601061107030602070206041e150e0d1707050303151306030f 68
    0x120b43c4c80b0b01c254290741141d00640048004c101d42e03211800070b040500301e1416250f50450010075410385084a54400c41c0034070600036110302d42800c00a492040034a04026200350301c03050b840f95440151101034044d4115010b089000c042400c0b44500b03262085014150064001403524034020013a21005801d6409550b0b6a0701485000c801c502c1c1c0d040103200840c8a100c40142020580b4100010401075904900c1c0c4140309900103080700728103a072011404160340a0383d04500f51002c2c001d01d5250700b0b0002c40b5440848e00b5140c1903205c070a122281d00711140c41500c40003555007607038a85805440b259a00e40581281b40c1c070646061000500d668010001d0380e000501c00360070300350ba887c141150f88000c0c050402e54158080c50412100880e14564034198941c0d0801703040c3c1002d43d0012440049445d04080e04c5240b5030303095004c0140040040710180380c0c1190a40e5540d2034440c0d400150f0041d0944400d000c1d52189491a803400a140304900680b87e10000ca07820502598503100310990002c07010703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 553876978 1250 553875728 553875731
    0xf010e040f0e0609030c0d0c110d02040b060a020c09060913110102030f18010f140f03040609050303130c080102040b120a061e240c0b0903071b090509070e01051003 72
    0x1001821040040350b04c20400710009680c1d41880d191681d0821120004030014000885443d40006819480d4034003454415a0000e510304514000140500340f200042c94101d0030000d9801c80540e40412004543e60065a0300c1c2c10540781c00c014441201c00c110f0320b14180c0035407800c0c15000035601c410081003500c1c0c1441200e0420301500320300c01659210b464406002e505006107600070303580040802100d17660030700b40300300c00c040c240804e4140c2d03200c1c00120101a060020009003003010740d80c008403209402104490702c07032810050441d0000032080b801e03200309444501c00100f82105001f00c43c2a52105502c0d1810b21241d80c112100c1c0304400781000f9400ea8480300302042c0154180842054503c40304098100c2c1c80c6000c6000107000c00c4907141c803d00b04440e4a01154540d000943c0c015140d40c0102002c482c0da43e030060171410341c0183c09009141c0104000c2041446050102c0007040d251003500400040c0c684c0f545031a03031041540301d01c181100d210001001301e4507001081e00c90f20031003800c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 553878228 1250 553876978 553876991
    0x130b130f0201120e03030a1407020601030314070515010905041401020c2802030a080a0311070b1b0c0a03090e13110111031e04061b03090911070203030a02060a0b0f010e040f 76
    0x1e50307402c5d038000f00c071524000303550388000f5003410310080315a64014443c0e0014228035411a200141404411550250a400005451010800100078125024116055500d43d55840d6481e200103060280d80a40d800c3c4030156901c92100303010f2088541203460341c0002c0c0030754824441074082805440c0b61240c4607418100d440303005030314140121008940302d101a583d880c01181800341c11901c1c52000d0b107a000005002c4c40740098401c0b141d450300704144041018010040f00005400d42c42040c003082c2140c0241c40203802091740000f42c0c0e8094514079001c52001d5980e40ca01c002d12503004800c042c0c95208400111001540a0b81900018120b0841540e14060180091050f6061a8010301d030b2107a6000808000d81c503401044480c2c413038999141e030305a001d0b0989005010f80000e005240d405a55241e000b1a00500710b4101c0b8400b60b4040c066035100e26210708080d442e104104c4400c0c070030b85d0a01e1150907140c81d01032800b52079010161a40c80f0035440e024240300003009600c1a80110698540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 553879478 1250 553878228 553878251
    0x608010e18010207030e041a090c030a020705030c070602010605060f0d0504020f030d3f021309090609030806060c0d030209180108060405160f05010c1505130b130f020112 75
    0x50801900a45580c0caa01d0000ca0500003115000c107031980e06103c100700c2087c0315a80391030b27a140d0001c00c0103030080e4032038a644030204024450400d0040151000091040409030007003061400c60b501500200402d6541d0b00070303c640c1c2e200b6040302c41604001041801c0520034194040da41042c0080c082019000d44180441e01c0d0100c2d90394070001040215486403480f0b40040b0b00c04920f04040c2c88080c84080f491250b00340ca242c500404040d850382c0104480d5810105c80380c5070300040020f03600034841c00640b030030190010401e1000640c0040e880b0800501704e810810200c4403201c1204000305164040e0000442c003c0d002524800e9010307050380d41607076600d090104480e0107000518040c210a00303080c07a01d0381c600400400c140180003100e000c20012000030310031000440d042820b001001e0001c43c50140746120305040000350f814a800709201580d040c86c010451402c0c070a0142c03d101d62100c8404412502d510301380105002e100405c2c542c0103500c5040d0040b00c590300004041203801c501c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 553880728 1250 553879478 553879481
    0x60c081005100c1b03110f2d060d1a010c080a0c060207060908041d01050312030c2a0d08040c05150f03010b0a1b0c06050c251505040608010e1801 64
    0x203806001007000c4500e814401c1c0010301082a00a4008441d00801c6001c0d10f40404c1da000a446082610316400400d5441c00b849030208540c00c40800501c041d03034ae025900c4040707009000c034256105580f0814880a411540182508000181c101c000c490510100900c02c580c4c2c03149800381195129003d1050200003200c1d8002c01e400c4134403038441c184d02e55092501985040c40d0440080300b050b80c56400400441d00c01013444855020071a100c01d6883d03030b070b03040200202d11801c0c0700300c4074003015006c061090340340981350f00f410072a0103426140c3d00940010222480340703003a02e002d000036007045010040c500d0982d030420380c2e6000300c5501a0904085428685954109a02801018400188080505500c0000410183c503003c0c28003210483c10b44807108405040e00a84040c40030000703401803030b070000f008006030b411194034140c0c2c12075140d0b40d4402c0094686100e100d011100395500640c049005400380c905039042a0746840482c2e1a21092102c5079402a1900301d440544020f1407002100a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 553881978 1250 553880728 553880753
    0x8061e10050a080a02040b0105040e010506160b09010b1002070311090a0e0f0109020f0603010602060a05040602041707080d080906070f030b0d200a1a0c0c0a12060c081005100c 77
    0x40303001340880c030304240107000580f10001c01c481e0421100b08070600240c11580c00c880d040d1207003074600a41316907134070100036035491030003001422800060b0700b0044499015049010004c034143c0c3d00629000010600383d80e100b0036804010809201c01440d0342190400389450355000303000c2040490fa81d58107000650610941c0d00c2c81a200340d449050600035030070002519800c0c16001c1e50310070318640c5040c2c0025105c1101428060b20591150f0105e410f0102c0d44e010382d400782a00c07030b490040e8035501a0344641d42d0700161040b41c4440c010000200c20107802100900e12400900c006840141e17500c80045461081103000d405c24540e032330340c03000c0050b100c800e00038004c144140c68598041818866404030142c0d0945d034035100390b19158003130041c0c0d020640285074030908401403030b0b00c4032074502d83d890500301301400b010f40141001e0b6000861240d1b102c0c1000c8650b00880081000b20801102220005811a250456219000001c1040d42081140a085005503140086942003d50748501a05ca078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 553883228 1250 553881978 553881989
    0x20a170d06030c06090b0406081611010e010204090f1b0507290103061d07141201050a0203040b090a0c03080f120103051c3e0d03140108061e10050a 65
    0xc0c901c00030f200c0d060b0040c040c5d1003e00305043c1d131035081501e4402c2c002e00c02e0342d00034001c0c0c403110701240a400010740184151820703d0201c100038402c03001940c088500039000740c40b031480315078200800c0b099844100d04c41d03220442613000165084140000d002c0d2865071044600b281c0030000800d0252601118505504861804900e1400303154990709000c1c041c4d4030445003030406803c0340040540c0c810000901c6500721840c104411000b9000c09001501400c42102d10944550030f040030483d00302e03603d6000354802c0344070302e00f0747c0343c1031300d0302c0820541e501c1e6017400080800c60b4541c7c0a001003282d41e0007802c0c0182095007840d02c1e142c1e40b1400c004600d40c00303910446680d400203900080d0003641a181011052039403512403500c4200890030b2480b40000e5400e880d82c1075442c0e00c0074071150b000b4a150000d400700c43d01192654074617004000c0080c03039106030101702c0000d0714002013186134000c940c3c41d0060b18100d08124802c504c4403d040b100c0007001d05000c036603000e0b80100242684800389035000030b01c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 553884478 1250 553883228 553883243
    0xb0a210204080a0b010806090c0f0301020f0301081513030f0e04020c0a0f060c0302120a02070201090b03010b0c1b130c0e030d3c03020c1005040f020310050601020a170d0603 76
    0x291400840c1054181c06c1491180c1100c2c0400035401e20000d060780d07030302000329510002248018082402445441d41c0380b583d1400010011803083c50000b101c3c2d44151254403620f0300f1342ea900c2c8598060202042004000035031101c041c00300e65100c0c0e1487c0090b854020401498003001c0e4041070725003844201c003100d07403080e8500c0340401d1111500c0340340c052041600701036180c480680580401c10b580285140300d615404034225055901c51890100500341d400707100c6960356120200c00000750003548076032141d4400c91a0b10031031a01030004400d84014050b000d90980289010301001604c42c0c001900204003d0f00410011a901001020b03600411a20b80c5170303200059000d241c0401d80440c200384c00f08080d50b40309020421700802c004150b40d581d803a0050303c480e00d60207554280000040440d800300e061000344024030403040340750b011940c822000c44112800d24207943c01551400c1b103000d401b6800c4103d6910200b03000028411112a141e40b0240c0780403e4107485808880e00d42d0026500301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 553885728 1250 553884478 553884493
    0x302010b030c092701060f06020f071a0d0506040f06060509090108060103050a1410050406140f0103080913180b041b05090a0218041a030c04060b0a21020408 69
    0x7418103010032800342005490000892400d90328000303c41c09000b01401905550103907a011000003075020710040c100c40d002040ca841e40d40c4200070342da080c07441c0d940722007805889000921100070080501348010310310002c908001a101110008040c0201a190030940b92469190400000c0c8600c00180c8000c0d140e09440b085400144610410140c003d0b0326164007010060003c10400104290a29803242c0140c0d04a400300144504214603ca084083d403410881400200310f00c03030f0040c0003c960303d240641a55070717404012a5411000307100140c030000d410407800c10941010280c0308070003030304100c000c600889048010900c076000c01c0420740d2945d03460010310080024040590411648000b00f80008900348070000380d40c2840903100c03500e036650015014800c5040140406981140240200300c075010345100081e000081901e0940310340202c80120802d842c06100380c1040d07130302880165040c51149074083d5081b401d503d01c000ea610341c11801e00c0440c202d2a0000b0b00140c00700002802c0750 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 553886978 1250 553885728 553885751
    0x207021020162706060e012601031415010306050a0b0307150509011115010f0501050705030403080313150b150f18130603051c020106080d08100e04030201 68
    0x101d4461400411507600122094403900701100c0c645401d07500381d00d2080008208004111500410020b4007000395030400000140442d0403200668018030700ba20b542d05440000070049841c104148842100340d280d49006001080b1f280070901202e5640d80c080744c006022030040002281402da0048a01984400800c62198207030b000f15414800f05500500410703003000041940111205030120030448041981d440b540c0c4242080d80d4130301d104a09545c40300c000810409160a424003869240c1c404003940020a0351150341241c010070b421038055403c3c1802c65882d80d0300f5600140c140100c140e401c7c6030a001084840700000c0515040550000c4d00a50700d90502c40c6411401c50394a009040a000180d050b000817008c0702c9524041300c1640c07104500c000001342d80d16181c0754180154030301d00400402000340000720140d8070075a040792142d810701c143d50102c2c241c80e185e0080040d150403400c10030040c640203200c401c0c0c0107030000e04c0c0c1060040d00c45003040e40340107007200c050380140e4407001718245 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 553888228 1250 553886978 553887017
    0x110d0b010c0206070615030807051e0c030a02060c070b0c030c0c030c180702071a04080106290318010c031b09050a12030c050d0f0206010b070c14030102070210 70
    0x1a9200282003150400030300e600000c640e4029490064803540d2241701c10200e900002c84142c02441d401415551520614207145644a1010f0841c0044410351056003624a2000620000ca600e0040041c070902d03680d03500b44034242c4c0250007001814407030300c400881e044000c40058442000240c00458450070402111840c0034a102055802900105580c01254070b6801c02901c003115404c00c07203c125119a00201c2c034100042d4017170020080c0b8508124100ba081c0401070040b43d2000c0000d004464a4192243c2c1c589440728003003103a112007050045070010004040e5510100d0800241d80c59040d0501c0d140c00e40d11104140c800003a5100161410030f40c11031003907035801e05036261021815080901103803100000380a50800e4640d01900b52040501c03950600301240c0d4402c00b69070b1480b845c508050403440b8401c00d450054003400d0000704900c0010020b643c00d603a00420000c094615240450740840d5010001c3c1d50955000c1000300c6c0961903e83c000c100041003aa1901009002c2440c0e008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 553889478 1250 553888228 553888241
    0x90106020307030801140d03110a060606050c07050102010e0d0807110d08010f0b093a060c080106080c0306010804020a0b0c0c0901150806040f180f1203090b070807050d110d 76
    0x8006d05211014442c0d403640106c1e83c1c0c0390340c0c2c5420a1038070944100280c2c1d1501d55030310b41c010159800e1a402045080e401000f0380b0030030350210200c6aa42c1d40b0703140160700740c404a00c1c580741c0035841009070480c0c1c01d203d0030046030082080d00303049201d043d44007425810902804480f1002c100307140010018451040f0b03d14000b01440026982003000a50014080707281d81d0b0402c001500c08203114062564070300140d21490104001040030a80152a000c0d0107443d400c0460000f050341000006011340c0079000305440358a5800c0d101e8995910781d00195051400a0400c0ea04101584d4000c2107111041004200031040000141318004118003041095941600490600d080d8683d14140180d04900f0881c0c20100854010600e8032108203230b00f0040ca4551000516024204840c81c01c1c001c00d030601e112507070b001314000440c400500c0401c0c0c051368a0080020040020800051141e920880e24145c00c05d10503d00303d0b00d8030314514010001c2e13030740b03101c0143d000c0e600004800c07148815900c65803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 553890728 1250 553889478 553889489
    0x30b1e06040506010c0f031e12060f03031e050417010b090603190809060702030a080705011811010f03112109011505061804090f03030513020a1a0702090106020307030801 75
    0x41c0554a4883e00003018904000b40041c0200e4145a00108041c000d4046200c42c449900301c00d40c5491440710018403e24440d94680255403801a0100310590783e0b6800000792501f41d1952007642080c2c01c4503100103005007028404101c014400807809843c1410036102580c02c800001c110b6200c0c0208014078060702902045c880c0d80180a1503030000c805213411007900d0b800000640d11901ca28001c2001403243d003000950600900c01c881c007c20140e074000d4040e10340120300810a18000c41200441c001486c900070301050b030b11240402003588501394484010340b4915000c00d801c158413400030180d4015184044035030030814242c4600e0000d041c4070942c030148c2500240000074455a0319500c00c0b4481c007450340101400282003800c40c8000d500100100c8000d40100b001841d182800e44003244009402c4001a081c003000c2580304000c4c50100c2d24036500200000701492070000c140c01c04644407942802e50201c1480700c103001d66508145a4004c0503150041c1d607440c403076860000c101c044140c000c2e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 553891978 1250 553890728 553890731
    0x103150c0806031e07030b040302070f08060417070629010e0414390d0c1107090c140f09180f010e0a0e01020a02010608010b06041d060604030b1e0604 66
    0x1c0000b59903000840c4510f624034031031070803c06210700000078141580381d00058a0810351909110805a00003650307001c66135408101408142c403014025120398040e0b83c0501007034007840b40107110a20780401081e841d4412440044c0b8146000c046804400190080c0c40d07000c000030715018400d582208402d1503004045408200300c03140c031049002c1d1090042c2c94800c2ca00e1a02000c4034158983d51005060784400700002c06c0c10145504002d46140e009920070000b40303003850000b5881038091481c500a040c0c0b00b0010f00713036480c103105018008140418407401001586407940b0b04035113544004098200000d0720803550f0b10814014420303d144000d40f65003960724448104111001c2149086044d03a5a0761822989515000071480c003900082c1044a00c55100141c02009280c0540c8400e0484841e00300a21031f01050710100007150207907203d80264400d90301000000d036030b05079100b01e510800c020907180c202031302ca40310011501000c03a0940340415142c51100c500da41814105075001d481201e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 553893228 1250 553891978 553891981
    0x2b140d1a0415230913020607021206060109050d080307081b0a020a1e02030a0f0f021e0901150e04020f0d0c02030406270e040309030605070216090b03030f1c050103150c08 75
    0x2107582075100600c4d08605c003141c0050001103565810072103581e19002421640c400b07090b4480a900d900d42a42c1c490b02051220030b00040074104041c140d02c0e41e6411001e03040c210340e54883c068a5400b4010703c40384400100300c0c4141351030142500078081602541c0d000b803030b01044900d840806482130b10144400c4c000b0410180005a600080b100e0383d1a41c0b05e0142011458685415080c851980b0b000a6201c10700070160810300008018940d2409002c4030703400f040341d0380c0c0c490104c10003050140700800100c0a03940e01c0030900b0030b84c00400c00098a000402e1810001080031300440385203c06007001604000f904000d21039101c050042c0b217003507072044240041182100f490400d252840b4524034a01c0000c00035090500840c5000d0046420240621030b074949240003d4035660140803124800c20107070004640070001d0304c00c880803a18058000c519014600c04a81c42a420180e00840c0314070303100c05481c039040b0507030040f24000c62040c035811900c0d51640c030000050b40d018540788000c0242000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 553894478 1250 553893228 553893299
    0x10b04051507050c0d0f02010813030806041107020a0308030601080702030c0c01030b011101050f07110c0a0b1606060e04060e06100b1b2b140d1a0415 66
    0x510001d0903081800841d95105082e140150410054065160f4002c0c82c0d0301c184420f0107984514120014801d07038500c00c29a03640b540b50b410140b540307400500054100b10005100f42015805100d1b03800341d401740c45050208690000340c0b85141904200c0d070030070000c800e004240d600005641c6d045095070000e03500780821590b00c141e0310304140ea21703941050b072500000d9446034028445510000c91150090110345009100883c100c14182c400c000007134820740c0858424132000c0f92380c013507039440103005d640050702c1c040c4802c0b0703607170419070b80100d4560f81d1440d518005609441600010420140c01014525080c140f4404030703a44d0100b4000c81c0d170032034800c00c440e48152812940c1500c0c68a92115240c0c0014180740310000000301c64417000348034200c0c2c10f80100507240f08050b01603541182407464101c0e10401219001d0441902540b4101c040c0714003406a08541c0040101842900764007031203041d9000042c0c10740e030036050b450070f02400011050004007119406044001c0716615000072006000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 553895728 1250 553894478 553894489
    0x70507120f0605060109081c020d0302090f04020304050c030d090e07050c0c1005040b070f0c0b090303030a020702010c06110a08072c040b03060c040e060405010308070303021b0303011508010b0405 86
    0x507480182155074a8002038860ba00460310100901310035000c5800c2e40210710580d00c6054604071004001d03100c2d5000030100340340f10740219000c424015004059083d21002400040d40000c1c04c101c496009030030410300991002c0011041203807881d599070240d54035001c0c02c0301100b50090180c00410108202c122402e5100180e501d00c4100150350040350a00803420882e5140529000040aa5000103441080c420036003042c2d2150380c005d244050080c1d51710807511710144940d98249401d90000c0c4001020b0280d9130380541b40042c0103041400d40b40c41c50740d454004031000340144041011010400c8011076178404515588940c55040c9410150a9a5441c6140a0801e69100d9040140400da050180c52700d03040344100e01006000c6820130b0a000201500c19000b501030859550305d4040040d04501d86801140d0490350401140d518050b0301d500c085000c0d501100056039011450b03141d0403d003c0342000114020444010440c42c094000100100701100c1070b0b002c0401d80c501803105100c2980c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 553896978 1250 553895728 553895753
    0x3020f090108071716030b041a01120605090c0406020c030c030c060a05190804021804030801030f0f020d140d081501030507110706170c2b0b120307050712 68
    0xd0911407807543e2400c0d01100c8105a0340120000c440015003408140c40c10002501c01c681000d440500c603171510131043c0b104599080d07a074807000d44041c0040d0001075014803182180c031130140c04c0100d035140e103500100701d007034134241e680c003401030b200240800c0240c1d4103100c90300c04c2210440c044c01484c041038000030358a221600c1941d01c1803c0014541ca055030044040f0349101e02010760041c0f40410200300030b0700300070342241c003030f030203050003130302c042c0061403000c0c09244101e50540784c18940e6402d50311040d80400c0800c00840d10041d1064038000560740d1282e0300d011881c030580c000100241c000710514104401d000442c400e0103011400d10180e446850f551040003c820b280001e61030790388100c1200c690b4680036240070a4055504041140e075408841c0b011031482d5003134102c02c1780d11400d00e110140d108480032410030118034010b0442c2c0910220710f60707030b10003138030382d40415040511400600c01c683c910055440990000440d182040018004080108008050009100c0b00c0ea02e031009007004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 553898228 1250 553896978 553896997
    0xc1b0f0d120e0103270c08210304060b061309060504090203061f21030206071d010c05030c070f0e09030c0a0605041707030c0302071a092b08130603020f 67
    0x2250b1003600c181d100e944514082e540300c010038010a090f400d094110b10903480c0c0300341c400d16002040401c940c0340c001420460744e20f4090851400f545036450281c000c0c1c0010f0411074030036483d40c1d04084640d9940c001342840243d001c501034407943c41c2a00c09000c0381e04580c080c500030303401c08845034050b940220346540d000940e48410381240007500c02c008200111900205c0d011a92160002d03108400c0040590489109408861007030711009400c0c0c4002c8502d140303807c5000c4c002d10740c50081d0351080354402d41707a0340300380304880c2004001c03904103040c41c0403030f0420f04c4020280c80c410019400001d500e01d80210351803000e51b02c0c2000d00200591158515640604850b4403080424100282e100d64034132100400d40c0c107076440d4012450f0003441c1c006d01ca0401d400601c034511011603c0c0c01000400c41c1c100e00440702140c50a10240180a48820380080c624145d05041e84460030308440001341010844c440c000c019030307481c0502140100e415043d04180201881400b90440c050440e0048824080307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 553899478 1250 553898228 553898237
    0x16030c0f05070f050d0f0f030504021e0d0606080d03060b090f090c07050d120f0c080a0e0304080615011205041709031e030a090e0f0412050c1b0f0d12 66
    0x11641004412070145500040140c840e480b480c02400f5840040c6140c031602565490b807c5c1d000c3c00200f1426500300380e901941c06685910240b000101c084d206003076040019003500c407001100c0d2070364022070324151b001120a822500c10362850541c03610134500682074000f0f80c5070801590b4400326601e007010b2141d15018030f0b070400114265428480c16683c2c1c095108007101c0c070400d00084002c0c450341c022071940c0791060030440021007240c11801380003000310542c0c2e6181145d649584001028010440c40c603401800100310210b0528002c1c00220320619100c0d00140c940082100010f00d00b002039244401354519100500c00000c403440b01803c95040001402c68845810000080c01c01d495048a4001c0290351940344164020200103002140300a03100c0780116951201e1410042500b180c0c9100340780000c100160000c1d8070248088242916803a01d0750030800c0c025042c0d0329000c50003200c81d07103600d200c6e0382110803840c0541f604a0144c0e41910100031030342c081e82c0d49500004032625200d0074003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 553900728 1250 553899478 553899487
    0x304030b13050304180605040e0d08070e060d061203111506011206090207060f0c02070b0d020c0f06041a07110307060905030d0f02031e040b1503030405060a0816030c0f05 75
    0x107800c106880c042c000c440c4013800c1700102c55480000a00203845420700407424035120300c46001022456800c40031041d103848005540d6032504688107200c0304625a40074a081c803440390105128482c244c098544e039081d000101e1040d0601a040400c0d00c00380e4849a404411680105100484100d400603000c1c2030403418954409046000303400a508840001c070700c04030342c000500c08144c0000c40d26060001c000c00940d0a00c540483c0c5941c024010031100701ea00f00700440291145d41d00908039003540c0d0341514003600628280b01d04004090741c05942003900c0c1d00082d81c0381c0380300c0c240503900449241424020600a00600394407070003120b401a0185980d00c0305403042c4041801101c03140480c0440800034404038040340002900161030b50f500001030241060001c0c089090814003d9411020f004116035441107044203811b4500d64590701030005100000d51515900003030840442d00742c540201c68a00b44162600800e44007420004040c146905190001e80014591140402c00e00d410b81c2e59 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 553901978 1250 553900728 553900733
    0x1a030702071404140c0a030b010207080712050a140a05010f05010513020703140d061809030801170c03010f0b1002070303121a06040e0717010e071b0c0801051005030304030b13 77
    0x70044c0070000c5488031003001c10003036405400700040080541c0743d1410808030510500490359146940180c552030307449070005001c4005d040300d01c601e0b4144030b4401c69520401c1075a5501401c02d100c8040c054035400030701d8003410000300780900391a400f4144010003056240500160300e01007181040c03007900b5800141c44051500c5192883c1403640542052070ba070b400404240b100400d003d05c14001420040383d0740000049440c090351540f960950384104039a4200031101961381c2803110a200700f80300f48654076609840030f004034050780040340400035005200398144150014918070400454100c100e041c0002901b0410ba205c0803007801d03038002603003000c104043c1c12814200500c6030b808000404c00080315100424140c2c4107100565a00c1c135066004011007620724028000c442c20800707141c00140d031140c410f024004a03407041ca402012102d240e515035141c4d50040b90040e04559441d0400c00c0b491f9080c0300200b40041600b540190700d014a1506e8040e07450300050448458130500d03003641c1e800e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 553903228 1250 553901978 553901981
    0x60102031e0c0d0f110303060312250602030f0f1b09010306050a180605030d23120f010e0c0c0c040905030c0708061510020d140c01060902041a030702071404 69
    0x140710320004100e4950103c512405441e400c200d610240018854200d20301136000b0100c03d03680118005401040041c152500710031103900701d400e1030300d503041b050000345103030042e000403058001c1c0c080c901c0181d8a041410603210282c0f4020304c0311018050f40c0c41480340c034800c010401401001314203440c644a40000700101e000c4e0100b0f0b0700413a40100d203945c012841d0001248111040691410208031a6640d40c00b03160300c80041e080d0f48400f1940c80400e2107034409465026070004a000e0901d00d1420144260307a01e0002400e4405208604c44880184510305031040780c80e8020b5441800c1c0d5007025004484603594094445031140590349440040040007000c00540e4a0f0303a6803c0207503510240c80b5044a80d60f82002c0b185040e01c0100c0e0b140307104046c01e0514010f480c840103030340035050444090301d040e241c000190f20103c04942d0308215400244200f0f120300800762403642c2d009a5100c0c03904441160b0112450304a00e0310790020010310282c250000340503421100c42900512042d91003100060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 553904478 1250 553903228 553903237
    0x240420090f151e03010b041103040807050705040903030e0d05040f090e030d050420060304200f040e1b150702011209081218010c09051207030503070f0b010e060102031e 74
    0x41d00103041500c6554140c00140d0b648034180f070700390020001e40c015403082200b510002405c210240700100041400300e8914001059954051002c880d156a80e4101040c2210040e40d01034000940d52100900804001c4c000042004000e140c80380c1010300b481e0b020418108144140b4140603550f052589000c481803059942c04e02100e40100024a05800d010190084651010b02040320051400d8045d250182c181c070f000f2500b20000000001c40f1a01840002c0c03643d10540354070440e1079800b004155210300469800c3c200c00c0300680f150000a00c24600c00c080c60900300d6205e131042440d90590070710305005540301c4940901e40380c100c100e481c40d504402405480c00181094400007030030800301e06400303040e038094107080f480d042d0400e118070545801c9030b804a0b0144006141c1c0e120402151402c03800201003005c10030241d6001582d40d0b42d5281c959132223090126019100c00c04c94805116180034058010100c0ca11001207500e04240000c0d03d80c454103084160a560f0405480380c0ca5209800f680d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 553905728 1250 553904478 553904521
    0x8070513030501050c0c0d03050f0402011d030d0f0e090415090c0332011b0e0105120f0703060b0f04090c110a110306151503040203240420090f 63
    0x2001503080443c80b600295011304807513146c4e4812034010240b403e00c41d1040c944a000f241043d00c0c440d0720b8950045900040c50035841018030036400019400e9a01030083d207465105541b00e100c40722160041c05400b07103e02c04a500e1040c04850100800b003a112002103140d411034410014825289142c00303a0280700e5074001414010070070303006c0080d4242c0c100d921044501580c0076141c1a000d0190310600f03841d1412001164407011440d001884ea00070314210542c1d42c0c050600a081001d90606002d13201c004485014528460006100116401d0b100f49009001082c58162030112240c81078480d512079031107480365090341c80780108d9000740705203118a01200c41d50b05982c504e014034244440803458000b03880e8400d0051002140c030705c08004010010450707003e0040003c0c001039000404c00360b040248207a8050240c0f000320480e175035026082206000300c5408140c058203040c1481a403001080d040109500e90000c0c41c50425030b074543c1c0565101d440610301e10007a83c0ca684405060080349480c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 553906978 1250 553905728 553905731
    0x705090a0612031713110d1113021306180b280815060301081b06220f0909030503010905040f080c030702091005060f030a020408061e090d08070513030501 68
    0x250010903501036465403c01d1144a0b407016240c86010081c0440300c40440010120f14040c1e515515504000e07c10704845405859035424118090000c103e41e0000440b510010550019044415000d43d016840c041e1080d850b1540f40304070140c0e40d0500c1d40c02c1900070240c02400103e91b119100041c0c0e24085a03243c1450314161444552003000b0b842810306468030600fa040d452000c640e07508202d01540c2c1280c0d4003000034220a1000380341e414040124a08903070304440304001812008005500180341241d011000d4140640352824280c0d00c401940c00540e02c16080801e9000807aa10006a80c15102c0c0d5000000c1c1c0303900d4030320340043c1140015500408410001c1100302030000c8c0840500760250080d01c4080c115910310b405d42c5030f0000702e400368580c00982071100b02c00e45482e8402031a80704030724000041c80d0079180e89190b45802000c032078010a610f40e960b00b8900c0d03d1641d403070003508084211f0092075481038500015052010041002d002c010f070100310002c1d2110780313400c51002540c12800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 553908228 1250 553906978 553907009
    0x12010501061b051606080405011b120f0b180403110a11151315020d090e070807110f0307060c050a0f12110c03090a15140d02070b07111603050705090a06 67
    0x5010300506d004540076140c552910000103160315030410b06008444c0309558217104000381c0800000141002070894000d40e0741c1d45c455446a40b5600145061840c9910201d4a107181916000780310301d4030703800214400e41100940d40300141003030713401015040c0c046036000c00d4000d40800f001001d004040d000c103407140d658140054401908601d04500858990994007103170146041525078051921450f6294840c44002590300351056103080e07005409480e194502d03103c800440c0d46041b585071844203490300001840010001148503841d140e03903180c10040d0401c007031114081c001d0340201055800f80921017101012140b00761b0f00085e40c0a2840ca00c5549035081c1e900760603501d40104051a002d4549100d01142c90000d805601d404919107075100c4140e65000605443e0382e0300f00c018020702c015002d101146c00030300d00840640c0300e6a160368568215440c182d07801d514051101130f40000c82405c0e840c040c800b141000c2000029106c064070310707c80c1c64507506039860051040382d0024440d4240084e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 553909478 1250 553908228 553908239
    0x90605060a0609060504210c0f060206011403060f0a0b060a0c110103020304080d090302011401150e0a08070e060d21090603050f06040f09080d02040512010501061b0516 74
    0x502403401100c05580200e5010b4039928181e4150046025500c04554148810411707a0400707514022030b41c06a1300383e044686180d0341e45141e121090f81140710015120368007403200e17035070400074540140344003032200165595500229803625000780c15481000a580000f03070030f825440d00324000c1040040e2645607207803c140ca004090180303e41044a243d03402c4000d2140d690321034000d490295802034520341c50070005500c503034010219010100c0555403079403403c040349401880414000c06408403a8012100c4900c0f001700f100c140340013010310496042000703000700c501c00140307032059500c020840354480d00e0328400120041c44a02008000c0641da0081058074113002100c3c01070740342e15848007000251030300b0041e8142c40f0210360f640c60001020740081c1039860250004040880d90300b40000d0f08030b600d6164a0034035485440c0490807603400160401460600e140103a078102c1205000300482e505040c0c1c01011020842440300b4130305e041c0040301c0240442845071000c045410031961800d944d642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 553910728 1250 553909478 553909481
    0x1060308030a090203070e0709121a190b0420180901031101141227060711071d060405100e0103051614090a02030702010e07080c03010501051804061e0906 68
    0xf4401c90007400341c1040010034200c2040b0f4036008035166191000500e091000c111145411441c05490b18440d8200c00241d00c000d0050700c6010740340c549080c407000c412a82c087c50941e60081c5485000e1403400303e0841d9900b40c4810b004078590825219259101e000c9a49114110b03030b844030f841e07400201a030000007004099021100140400c0e01c0e07904040120f07800d002c0080c010280d0111102110400049095005070004423203611001d081090800760002c01516100003155880049401070403d59030300b40b0308101c0b0b00d00500002110071200e210a00000c0f40700ca2000d007599002c1c0c0d440f08040b81840340c2400c440740c0500400c40e07881c0ca507982d5a00b0802d944155841d9440407480ba40c11010034540041c8083c8440d040000d013951801d5103c2c0c4c00000020341c8010407020841d540c5082c003442c1088144464001411071200815191107060f00b05401c44070b042c1c1c0524840d810f40407844119098809c0c50a038402d4000c8800920200000620081241103056114000d49494400310030003a06 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 553911978 1250 553910728 553910741
    0x6040e04051509030a0c210c1403180402030a1803020c040f11030f0702010b100908060c03221506060507350705010b060f1b011503080a0201060308030a 67
    0x1c0c00403149201082070301e0304140d140540b4415065002003142011050182c400ca4041e03d12a1500c2c03148001c022400d60120701004d40c5140004941e1103996052044502114881001e0707507000d14501034a5250003441001520320040c042e80d004000203800c040b8540c81003c04120881c0c1e0008072514924009442d4030504903618072580c41c02185002003403241c860300550340c40719500c0600c0c41e11007451824154a005007075908641d200c40c1040d04986600d0f0609241402588408040d6420300451900f4a1801030603010082c0e4140100840e44220450b4909030f40e03804195004a032455041108520b848047c52821460414000007041a8080020040c141c042c05c0d61100e15a08802c024010000c4003c1c4025180840b42d44074082c02c06007402003800ca40f280c030001031081021000300f40c040d00583d07981640034501091001d882c10f01c28411185480815008000000040103640662a1103000141c441d540100f07500007024000d512502c003942d00301e80d61503100c1c68103c45040c041e040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 553913228 1250 553911978 553911983
    0x40c08031908070203070f060f090c14180f061302070c0b27030601052115040c0608010810020705101a131503080c0712030306090b1c1b030206040e04 66
    0x15490002980f051010064501032580050b03100c14101d0700352107882c0a0248810351070a8107965944c030034001920101154010030905d0201801032a083c002c00182d443d08800266421101004000c0c0c0702e900071001d00d0303024008842c06c03403585c2c8100e000e020003030250000c002c200443e030500225000894801130207148249031820035a0404054007410700c0d855855025030190300031f034010300c864540100d18213589912401c040002410300b40d0303401e1526444d903002c203d12010b04410300c000d122000541c0400b405490070010070f5035151154103952488203130401d40b501940414004d0402c0003e000c1c6100c1095114014459900340c230461a11110040c2c010500ca2107400842070f05400050081d06090b01c504400224100c0c41d40c5c89210155100b41d10403a058042d244000c208509402c0e49070145034040d036400200c42d8100032100b8110345050303250718811050340c803102c1200180c44800c01205a8059403a0070710310b4501c02001c80e21a519000290301140204002c0703001155030744490321660 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 553914478 1250 553913228 553913237
    0x7050a06052805014104021608041706040c0603110403021809100b0d11062b05180c190807230103020702060f0307050f1909090209030d08040c080319 66
    0x6001080021450282980400b0f100100004200f15012100740b02442d031800500003501d8280c100400082c10b2181070700c00c132004030012030203001d9100e400d010b942cbc40100c1e10004040364141070311380c50301c44100340c1b04490806031203112690a08417010150380040d40d01600c0c1c0020345402442c00203a11754102e6410645126684441026400d507001c1c0307443d40074014006110001458680f8074004811641c1590040030800a480c100351222410340602c6189072f1b00d902c0466130240c030300c00035140003800704040411003001c0c41003c001d0120f010720700700004036840740301182c00c03103034480522849610001c03a030b0040c868001490001840c5124a58103488440000c580e00c0340c0c019003c034014500040e41203502809032169441c2124025030f040b0081d42800d030300303001c4100001c14895000440c0d044150380085c420941090300880034070040c010a0805500342088100440d039100d101030001d408118128010a09100800d007403407000e013000c00e058995030701003020103a010302d520102d1500080d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 553915728 1250 553914478 553914509
    0x4030c080604111023220f050301050601091404140702010e0c100f080915070f08090601032a1a031611060a05062815030207050a0605280501 62
    0x2841c0689141100013099150688501c420700c1c00906500b650b40e050301480c800c10000c1c00c92031458030060040304414824200d80e12400c00503500c0c0700a03800c2d80070074083c0e8180818400540c0c0c008580e2070980d4030300840f1921880500300000d02900c890b180c03140340b0501120074040505d6041d0440900704210742c0481f400c007040801480701400e004001c0d02d0029400c41c6104004510603d40c2d1900503030b0700d4040700c03082004500b44035901e800c152041030204414408031004142c2140b080c65100c00b0f1407015000940c59619000303111400052001394042032100120704200064103120b002e0282603000d04180801d5012404850303100f0759111091058210000681c0c501c5281d0140510700f041002d803209456900546018100c05005694003010040682c0c609881010154144500b20907001a4042c40e1460914000840402d00c8040500403c4400041030300001d0054441c1e500c04400905a5030300031002150311032000c090345140c01c2e0400f4040d410f4a1540249050b075803031014070300c0c0c1d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 553916978 1250 553915728 553915763
    0xf050a23010b0d052d01090c03021206010509040906150509010e090d1d1c0b060103020c0309090a02120a0b0f1e040c0207080d032009010c0b06040204030c080604 71
    0x1040c0c400d10030b01a002d84100403038010000e20350402900010382d4001c299403a0110301e1800100307401013141c42d44c00340c8400d004111a52180c020404402134a050851500c01061b10090781710f100149164180000001e00380300a0300c85900201145411020800610500b4541001140854032a0074170803c071210011800c01085101d1a000340c201d0390080c810030410020036103190000c103039201c0c4039401100c4405015120245508030413004084900b2100d031a40c07078030b0a810f0001170881c604062041c840d405c481310303000003201e1006000b00c52440d41d680d120040c4a020348520500351007103506031800d1040c1511241c01c480c250107002c0f500006075545c10b6082c000480c01004104e03003030814802035000702c0e040c1540120201d104a1054400b199200e403885807070302c45481200000255109400301038480c0306020151080c01e141200c0e0700d0b25008200003441c58014210280100d04140b0103e40300d50fa40e40c1c120b0b030003158000c4144900d1943d5100301b6448480490f03080c0c0c0c00f8488030a42a41 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 553918228 1250 553916978 553917041
    0x10c05180303090607060f06050402040603050a0f1109060309070f0f030b01120309051e09090a050c0906090106081f0e06010f0306080721080d091e150f0f050a 70
    0x82c40f82c0041d084034100129500c1d814040d200a0340710a80803075580c2d4011480d9192800100b001c1c0016841c0415941809000e003070407a0100318200c0c440710320384a201d0500c070404208440080030111050f686a442d4150881d05010b034940c00003503140f080a80c00034080d03001c4594002200d001e03202004040c0c0e1307030702048102c0034104c50380140050040355061040386404500007104403029401c0390b40d16400d44c00403c1107100d098604040c5070b440b0690078000c2040802128401410669a091007800c0c602c0c0440c078180810300501090140e0480000c1d15111030451002010300c17001546018655130b0000e9440010055070218006042205401c4540f07010f4050601101c222000610042d480c0c06040008803500040b0b00346052401242038001c16140b40160101001082000509202c1841e242030710480704401c0c600c80b04400308540c400b00c1c0300e5805100030041001400704200c440c12104900400181c400141d80d6850b02041c8985031320b0540c4404c6201982c120300705d07903100f4008003484 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 553919478 1250 553918228 553918237
    0x1020f030903120a021911040c051602040903020f0a120e0d0f0605060102030904020f030f0915160e040227030c0a1202010912140610030b061011010c05180303 70
    0x140c0640c050b1800c0840b035121200240410312451058911011b0300f059044041d4203064826610035609180f42c10451400707124202c00310321542002460b22241c0340c82c00480248010000e44030700c0d5502c070480305042c000e0000342c4980c0c01e0074080c0c0355440445d16101102c0d188461924001aa044541012038205080e40c00d80403904070201015006c240c0e030340e503005450700510f014114042480042181c1e240c900151184540340010310751285000c2642c0c28a00f48000e089c200d595000ca00c40300d0601c10166007594001e455103151302d06207000076174195643c4166407841500305200260064001031030111400d0411005c000c0b401c010240013042513501ca0900004d0395000110040c1000b103400c01ca18441491032040c14a0315000d0340d00c410002c407601050000b40c5400100a0600040380002d02503282d12410124840c25800e085403600051640018140360051381305416001129015072800101403e80030300900070440314400c02040d98014442e01c2c0d120254090320510146004030940303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 553920728 1250 553919478 553919497
    0xa0206100f03020603130606080f0a02030c03010b13110412050a060605121e1e0a0b061c02040c02011401230a081c05040302090429011406090307091a01020f03 70
    0x1900f19152001c541c0108804111b08891080d62400c0006842c2014400c4008074001c51307000d00200441c6e401072605011380c003000d20b0320907403400001403800c0d03440c0d9451400b0002c5240000801e83c0ca8521202c20f248100d07000381d00307100104007008041002c0050341031100c0c0c1c0b051905100e41c070f42c2e4000303100c40b00101d203c0c101c0b0250850300e0803088200207000c601c07264160441c202c800e8030800c2c400010140c2031040d2a01c140d904203184038400d00000d198416080241a07c40c2203141028039000100c801220780c00030312998503a04511081c45c400d4001c103291215148041c5200d581d24008201401400c103010030101842990345200e03441c10b154000b007201c040b080680f41c1c0840700c10011140b41218007025007800b0051001001589038100300c540310301e104d030741d1900c5a405090103480300144440c140d511a4071030792005110003001c400c942c41c031107031040c2d51058544030b04c0070000b41440c00940195100c00d01e40800c6a90713404906c50440201a405c0c1c095410030040700003040e40b82d21450645 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 553921978 1250 553920728 553920739
    0x803181309120e180112030f050a2a020405150a0b0f0714120c01020a110c030a0b1009090609060b0105041202010c02011e020c2b15110a0206100f0302 66
    0x1040041c0e0050115484030003000304140902c04c149119441c09240c00e8001e1010039011248810800d03411182c01c0b8105040ca003081d9080802e0b012000f44000303400c2c2e145902c42001520306101c0c690003006040d00c80ca500400502146c43c0c02060f901c60541a04a0280308500190002500b04203100481d00044c035040a000d142c2200e40d1640e0b501030040908032000e500c41e1010201d00c0c802c0c404003a000341c240303200001d66913419402d8000c0c2481907188494110750405544080e10756400541110b5850b4441d5a004155540c407091140303101840d401001440d0070322003e242004110390120320540e2103003e04000f41d4411500444942c007490040381f500030703902030f000b2000d0740c0500f69013009684149450134950041400740d880e0700014101c22070150384401158205880c010b42581c0721750000402d2241200e4174051040e4542020240240c41d003074410940225001064201910b80e850b08481306540b038440c071100a40e220802c0303942c02d41e800d85c0240c02161010304581e488086030b800801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 553923228 1250 553921978 553922003
    0x10606081521031c0510210c0308071a01060807080f060616030e0a1d0c030a0b1f0f032304170304031808031606020a110f030c010f05100317040803181309 68
    0xf4001e510050400305841038150381c42300000044032980103116461090000c0032004190040e403200d04c680680011080c00001002c109820743d008920685c802d0340c1080148580d2200004181e15110f81044220a15440c0009100741600300040d031300034074000d5460b0001165039018119135422503888003aa10414040401c00c01c071700003800340d5049a680f03070001136111042000500380c20311503c0e00300413130603103d6450b101c0f450300700d00741c080b6500c414201400f000da042443c0c1d21825404604c3c5056001702080410705216454000c050f008101c0c2c21207903680d04190601800f8056410413144210301c4404011030071010100c160b54601c1681c40c6510981c440e20b07564400650400786e00c42007004074002e26144000000c00290035224440006141c0d595402c030210340c252030311801c0000720582001c090180f610021072607201100e40120362580002c120500542c9030f445903502503910361201081c41a0390340d0520300c5045480c88100c0309144096000c5c140441950b1000304060201c008407403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 553924478 1250 553923228 553923269
    0x3050d020f0f07060e1026060916020c1009090e0303060a08070b0a080a14070908150f27030d23060f010e06040807090c02010606081521031c0510 64
    0x3070701048480c9050610303194074004e06251116203400347c00500c80380750340641444480e06006c48056000010312500c00c03958030201c003020f03680e42c424080b01e0780110958100f124440c0d01c101800006050204424051500e2520859540e41c1064448521650382400300240c0100700194110480351941c030f00c2400e00e0b0004e0720540302c0320002480d486046854141c0c0103c2080c0059115225040c1a2241c24419042c0026035113007010520340105940c1c2c80001388004004a064500e600c50880c01da00748001c0e000a90014441b52200714143d1207100201c1d407030140d1a10341c0c0064101c2201550341171a40d4041040520715100709880e00c68114a0481e80622a544070700c1d0403c64280001e48014a041da559980603c1c0109076403080200780e654540c1c0c00d0140d90f080c01380300e0040409140141007810080c114003000c507181c0c90341c81d2040107080001c8500c05409410f480c2a0601d0768141c0362a68905604080d0350158460304240d502c0c0340a0002e078030915000d80e0f50381034a1074450310411285506 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 553925728 1250 553924478 553924489
    0x60406170601050d0905011509092f0901060206040b06060403080d0b150c03070c050a15030b21031b061003080c01020f03040f060b0901180f0603050d020f0f07060e 72
    0x30700740504000c001c01407070418440d14022600d50500c101c0001929030602c1d0034055021400e03030408484513090407d05c1020684c0e40c0480d014901c01404400c4072114407250201c04400c41c3d000c103035080b00c1e81c50000640d441e00492080c1c0301d40d01172003140c0c94580d10101001030074826070000500e00300090210391502c10807030788100321603200644000fa07803200700070400d00d86070411943c0100903030001540f2030420038014210401000e00f0b4400c0450207043c044070420308802c0100643c10560307140300c00440c6a841d140034100d00344070b0300301c2081800240c1141039103c0e40482d58944015240b40035119001100041072846214112424a601800c1d81c0d034610340d9a0150380c01d541c3c159000e0040c3c41103225040f00030760180b8401c0320701320694112450032030242c8008058031132140c4021001001085400e0320702c2008041a030000040004002440000600084d08050040e20070b0319504611031f500002d1000c40c006101c011901120090034400d966031495000700c8001480b52480c0c4130550611 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 553926978 1250 553925728 553925731
    0xb0f06070609050a05100606030e07052209080406050408011a0306011707031401151203020c010c05010f1b020c09040c0b03071101020703090609060e210a02040504081806040617 78
    0x290040e14007040c003070348178280b800400d4414180b81995a440811065405114021035030b0344c9403024100151034680011b4912482210304400c6400c5074581c1c0d065411103034018481c1d02e6110000d26142c603100d0100424039041030113a55415803030031015007591082890408840c40c801001401c0300d0707081c1400d01181050000c0c4058851060a1010000944010031081340c11440c8000023601c0605100742e0014090a0b801030b0000010507501034042580451080d24400b004c0c20110740c1010985005c0303005002c0c4c41190a285490024400c02c45032503280e0411803102c01e907080f1620480c4040810184000646008000760460f600811051039444040c690000c102e050040c10380407400c81c218260f07400200e04070005084018288041c0c1d8010a010010342400e2134899a240002e0b00461001141400c0e075200942c4101c00200d4401001c02080200640c040c0040c0864285403400040c0e07a0090341c03003114509a0005460414248001501c081354010b540d600351403078542589400c508030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 553928228 1250 553926978 553926983
    0x4050a020f04020d05090f0607111b010c0503030f042306010915050907080106140405060306040905011104030305042402030f070507052d06130506130e13060b0f06070609 75
    0x1c091044c980300b04654454184140f00c0c3d400500044500c0e281018204000100f03090305014000080301e1010a0009103004400c404002101141482d100107030303804040520010101d1200104200640400301c20084c00b40740303d00007040e81c405030f0650006000441083e0460241e100314010404002e4a800c0442f8000d4140403000801d51038001003916110122015004140004c0c01040410751108003402c0c060144440207051608260000e480c0b44070280c0410300c0303180ca9420440c03c0c024294000140702c5251071000f9950381c0c0d607103800313401ca80281c81151403101c581c0c011407101d184000f032a81d41040c0c0031ba010310b1510f211003400b401660405141071310709114400010459460703250240307e01ca4501c01004041e01022028241011180c2040e103000f84020301c0300b0904011900420803d03181c04540840d04e60380609107049105c00603920620010140c0d0007070100a101c909282440035010b07250074040d5000360002e105450410080441d00706000f0403011000c034809501c00341a003071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 553929478 1250 553928228 553928231
    0x18011b02030d050711062b06090609060501030609020304030c0b0c0c0d03050610030c0206011a0f13030201021b06071205121533030712090f0b0a0504050a020f04 71
    0x6186030042840c24501030001c6020034000910101808581d5444191000086482d1443d000f8082404198843d4078948139103000d502950a0101118541005003d00041002000215030f00d10703c40e0098000762140328003080c504080411001d0060089a100e01e4141e01d6107200010559105010080001d0441e03003034241c00d0002e03c0d0769407410300008052188565012078241040030411220707a0000301032405251401d4041b1482030b4000c00c80c0d504450302c00710b414001e10104170014041c1d10680e089618410800100c8103001c0034088203810989000f80c0c01c5540d00300344900344d8040720042c51642940508140100c400241c040240d641006449190642c2025800c01c006660914280c031203a800840300c1c207426910f401c01003440c1407003107805101880004251a01c1c41101140e80408956810703000000803c042c1c0640307044040440000b108020600d05400c040761840c0014108983d594441c1d0b0101d0b660302401d00074140a26040070140842900300e82c20000c1c10f01c03012030410b400a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 553930728 1250 553929478 553929527
    0x140102030409020427021204030e030705031507030e030f030109360203010f020a050708031803040e10170d1d04020d020405040f29010e150903010507051801 69
    0x40b6002d001401c01805181c0c1c60b41c44c8240e40c06116904000a6216040c0300b82c0305000380782000300d2419041d074005805040580003084e000011034240140c1c3d030003590301449009101480c60715105a11762080300650b80411103032141420380c0784c5a200c0e98200183e02c0b001400103100248140d404014600051100c1e038804103429043c031010201c4140311010036411008183d01981000c0c0510300196504990440c0350000d40403010b840c2c0d0041d0b44020b05050030120006504008017541c8125403500c14040300c1d12103130384010040c4d041d83c0840d11f0111781c001c04180000c00c61880c0c84107040034600311010b082500a5100200c1d810400d08082c009000d1030040d40050f99220380c4010101803809860159a450401c8148415244c002440c0603030720380b0b824816002c960761889200c181e81c0368940141c2c084800c1100489142c07107081021644400314843d54603072038a1070b000034508003074182c00030300240d500c8800580b210b0045940c4511189000e5102c0f284941c4103c190b000b1174014802071010382d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 553931978 1250 553930728 553930739
    0xf0409050109051f0f3b07020115051804030210020d0902120c010905100e0603070903030f08042109030c030c0303090906081506120a0507051801030b011401020304 72
    0x40e80c40c00c2e8815650746681c1c0d018000a40d4401425018451510b10740305107552822070194968010f922403081100b484507008010b0300101e02e0041c81e020000c8104800d00d0b161141c8040349000250f480101640c40c0500c20b41068007048910300440760002e00040390000d90113881030310603030010012011401011006000022107102820380900307030f04800104800785105201d9461050000f0300100d41c4549824800350780d11101860540e94190b03810646120001410340c0d0f4606110310f22a03020002008101c8140d5020b003c1e10120b038007958410420f4400c0e00010390b0703182420b42d005082c41c1a41e00c40140d100c1d6844091000c0e00c0780b68030f400900c0640d01d8540301d100d4526a04100d07102200302d4020428594000b40e0980a0540c49204200180c0342ca0103241c0e0b44c10052a00040781ca4255000945036560f9007036006d500d540407010340707503c04500d1901e0b5464480d01e0007094840d00c80c40307404d40c000400c41d511840c142c9900c60006951a4201550004070f00c42040c00c150442c1b0040002181 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 553933228 1250 553931978 553931981
    0x5010e01050325020309031b0f2b03051206040218040e0f100507021204180b06071a040210020a03270f0b030106030c0507030f0f1112091008070c03050f0409 69
    0x3e00c00c80c00d070302443d11640c1010400d8184044001941d24062030548011743d241c0d1002e040c0c1e601d10780207c501c860401170700001300c0d194001e028406d40301542d1a18000c0180342d0041700070001c0c2448048000047c0e501d000803c4100e02030303c145d1580a00c07500184082c142000e0380f007481c14015031011a01040040005946840020082c8061039920385003404804e64041140c41f1140203a01c01d0241841d013008c49042c01452070445103080c00b034550209000c00c2d2100001c55101c640c200c8140c901d01c40c1889641c805800056404078050141590300301250340c408034003580d2890307056407037005010031806440340c1c0600c42d2128008100c60400009004003003403010304010207000041c40d4403036140001c040d040b42c0a500107801489400c014004c00030380d00a440180d484114100416401100d690448994104428400307031849024000d1144241c00b5020701a407003002c9800c0c40d00040c0003103003102c0240050300c000001c51501030500340041d004074040d292049070318003c03500b030903640c094500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 553934478 1250 553933228 553933291
    0x40507050a1d060d050d050f13120b010503010b0105160c0504150915050904081c0f0f0b060918220f12020d050406050c010902030a0320010605010e010503 68
    0x1001c070203075008101003404800b0421940003034103e645015440c0581c0704c1035101c88040459404200e00062601240e504c49025110000d6001e40d401c009a9103408140640c0c4900e15410340700600020000034152a0501a5002d8002e06940b0b8a06080b400e1121000c1e503080f083c0200c84002c040742000c10700780c4503807084204022003c000038002c00d103486103500880f1182c64080e0fa403d201000180229100d40140d40e820551040455944035180c041603541d90843c00440c0d0100342c00c2070420f40c61200d180e0003032000300c121840c0070030008407190b0401510b0f115180901d60801043c89202d5411a61004195400502c02e00c5074002641c41c03141118042c2c6001c07508a1760a00b810100702e0030302a41c0560031a1445ca1800100340f508080c1f640074196010300e00c601d2042017800141e107212100c1c01c0d003181844981c060300b03c03691540c0a10300030340082109120064810f030701420021301000305018070b9003240d4041c1c55110f01d40c9038403001125070342d2008200c0103006608803181c40300c052800c904207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 553935728 1250 553934478 553934489
    0x100213080a06090b01060e030a020d030c05060903032e0905100308070c06080f0402030727050c0a0e01051305040f0207020310060519030b39041a03040b040b040507050a 74
    0x1040c000f641392800c0c0124041c2c0209041200c1002c60038030366140001c03250308480d011030310b44c7c6018006180894420780311000003081401040e080c41400e040000155015030b8042d1021708465410740308940d0301d0b0707800c0580c401c03040d00b003008104810740e0954045900121050100c03131320309407030f41c903a09071030307801908102c07a01c145548040104d10740c0079800b99009844142101c11604103500003070790b5482140146c5c818044c0c4004178840c0841d04d000c1801610841c40c0c1c3c1880140b030004400c040c190010314240340441c0c000c803004d950640c490000c44a204c030464485d600d0950502050000502000c1c0240406650030450710026035010010518100303030007800420402e00740310a2003140c01d000c191461140900e404180300007040101d400350722108040e11039140d0001d91046507034440380200c001004022082000400354240001001520780916462040500030b0203684854801203034007400142035036000c43c0001c1d40119600d03422601520460f00b0060311440080e404420340e5018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 553936978 1250 553935728 553935731
    0xc020d141b0906040b0d1202010b150405040c09050315091f05041b1203030207050102250b071821150902130203090a020919051e090c0102100213080a06 67
    0x42940515012442c140d20010039941400080c2080003c20b10381003800e03d000700b01030b030400408070109100b5031000740d80180c002c140d01c1e1048464003140c0c410b94494020340e401241005010745405000e10320350421070308090014091868101040c44a00101a240124034008d5440c44071500081840300c510510a1120005280c101460448540d0320000c05d5001201d41104041200071030040152844c5509420090fa442160b40303032042c02445103420741c860409814210814880c034281c900d00d41c06203d008150580c0e20b90400941d5900740707941403640688240b100c140f14203068107441074002d0f0710400900d0314905d4190784065400e501804c196008950710f281c868294a1300340c2024031805a00e180442c55030514080e9562038411100000c1c0c021300740d003400b040d86181014840e00e040702d030344002044070b800c00c2460103409076904880ca1203080154230110b1280d00000c00e4901c02068146c0042c182500c000c1072035006500078045188144443d04000030b0840402d01040307581903c500b80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 553938228 1250 553936978 553937023
    0x604030b0a18080d020f0f070f0c060206060a050f01020a0605010b0a0e040603050c2b0501090308060303091e0303071e0c080607210209120c120a030c020d14 69
    0x8100c0115445150302c2c0700d21185a081480205070754408039119007582200242e510050581405000e214400111861142c0024400d00340014589024003880c41801c0203001641c4d5800202d80e19882965110307404160010204801e14045418007850a41030041c0d41e910582c545072036044810982c1f003c01184c0b000184051103d503c82c141c0018001e0844c1d040100c5070464481039600c0800207e114052a0b5040080e5504492000c0d006d20744e1008400300b0a0095040c81c049000e0007000d030045022441140100b070381e81c40c001c01035540780100030f06450014a20420343c000c81110880840c1d415000c100f10300000314400003100004050350130000f201c5001685400f41d0404415030002c18141c01c244103002175207500400e00036110403405101441d0141003c0c080c030080c800d401c0c0c2243e012504038620208180c020070b49540c2e09030111a64107444d00204035035134a4903125580100000c4003100d461005103090703ca28212540580c10040e41e5408002d80d55162401c0321001c0c5411000150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 553939478 1250 553938228 553938241
    0x606030311160e070c050f010903021006080309010804140a0b0f0f070527100e0a0b0301050a1e050301060308070506070201360b1f0902121906050604030b 68
    0x12502950485004010a069400c6102c00800c211081c0180d00741880c0c20804070f401c840c402c1d020040915000702c00d803508010b107c02c40c80e0080000101c2103001d4010080c615000411a10070103080340d9101015520b030202e1130b4011221014000c004881140d090410000b002600b04a0360300c58511a050802c4203040c10b0740340124010004115409641052040184d11a40182031322800741043c41007100c0c0e503401c84011074030200a0050329401920030b91005031001d90007030b00d4941080741030303800b0640292611180b228910090050136000103003840c0400c50503a20000e92840001119080d8180740e495000003030030b6038400d81c0280c2d01c00d000441c841c400d2000502c042600540c40740001c00000e40408204c0789004000c20041c044c005000c00345c041019851207210b10040e610450141440c0b621701d414441038410b41800c400c0802121402194041440c4200d540c1250048240c006603500c405400c1c010b4075201c20b2002000d0780358600005d442d00c07400041d10186200d030385110540e24220 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 553940728 1250 553939478 553939487
    0x10f0c240e010b06030606090904050a060c082401020d0e0103020f03010305030c0f1b0603041401050901020d0b0406120b090a0c15030c020607090e07170112120216090b040f050406060303 82
    0xb140c000d8030504c02001440700503036942d812036403081d8040d0b071720300707000e548500300b003402e12003005805001c49040042d00103a1981c4400064410311006050b184142c00c25a00a10403e09620740140568841d513941c48a107409200b00c41c18400741490701501c1c2c0009404042072640003a442100c866002080c011035000c418441c05030300840200051880d140c03201c1da01444452381c480054001c100020200e8180040c0708140c9240c240c0060003131200d4204002450b00070360001031106c03600c03841c0405aa486152078041e0354116090f02c001c9100484058440240c0c0710b10107009800c051040359101000207081c1e010440062031000c2020402c14044500641507904000d030160441d0441e030708000000380c000c203203c0300303031100c480c90003403150380d010302c04c0d07842c0040341c0030000c0c041c0029000042d04541881032200d840d0310481358282e10703003d0528183d80c0c46894031446004103014150501c1918001c0e8041800c400000380701085503113814440c04101c500c16241510708940b503800c01d10505820 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 553941978 1250 553940728 553940741
    0xc090b120304120c0e0c0f030a0e06090a1104020f180109170d03060f062c121c051c0b0a0306050a090203070806060d020d02040b1c0b06010905010f0c240e01 69
    0x1505a04521b1034040f90301481c502c1008503180c103070940440418802c00c250780c803203101c6078010302c211451418807140300366640f600d04500b101c038031500091883c1107003040d000b56801410301003821420b008146500700c0c0700c1001c040d601c0741004071051000071100300e82d4106500b581d02140203400400300100000303090300d503d40c21130300d001c10350b0f071408119443c4c0c40103101981c480c1c091340240c8a0080f1440046802c520b800685070b002c81000d201c411001c601082c0c582d404840020031800071644410155501d005030100312810450031306851250308501e411008035503200030a480581030303c03039803514200d801c207540c2403a0840d61200550114281084040f0161007000000c048074504540090903008210304002d010f6414100c1010031925107400c00c40c10342600401c04200744440c40810781c900da40040c0141c43c1690316501251907035004500040c140c505c10b07920103401d146100310642e03000d00f504408403850b164841400a034078001c81d60418041c3c40c00d0340082a01c0794244602c9083d00e10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 553943228 1250 553941978 553941989
    0x1b02010c090f030209060406170d030b0a06080402060309070f09020c0d03141513061205070609030209070309140f0304090e1b0d05070e0a1b020a0c090b120304120c 72
    0x9101802107100500c0c8090072258116541c85d010381d149000300d40504015881080d120694a81c41b0b58001d001045a40d0210920782e07041102c150080c08001d0901454032600020403031450110f00541051801103078003403100800c07102c00903a6001c0d00c3c2151503e541c80032900c1d035400305078182c820409101c141c0741ca00d0503140070320400300703085c1105c501210044c0500302120a032010b03001d41512007984186142c03c14180030491f40780d48611842c1c2108142c1000c4031503008485e004145680644005415a43c016201011680d030b1107400758000c0005040549074811a4040c1c405030301420454031843c0541c2001030750b2a50b151031032100584d5401850071403150440020220442201c5d4007040100d8002c4407c60801d50160070b09505066094110010559080040007900e4019400c270a401903540c4c890342c004285443c408903142c201014005110621501040101250641000740d0300700c0014141c4030400d404800c0c0614561099120003a00320481440c8000e01108400b036100030304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 553944478 1250 553943228 553943237
    0x2120c010b120d021513240b091b03100806070903060501060e1f0302120f041a06181b04030b01030c08060601050a080403020a0818030706051c0e0f011b02010c 70
    0xf4540300040d403030320600c010042070303d44400002040c86c1481c2c801c610301540c00c2181c042002c29546501030100940304400495182007048084040c202203103030600c940c80c0d102c8945260100c2c203003a100c107507001804202c10214070311008990154140188c5000c1c0345552100c100740c038a9880e0010a9a005038402003e1046004590049440e1200020085c8902051f2002c0b80400d082094001740a04000219490266000c100c0320340040c0c0c4c210750041d4025074801e55088a569079a280c400c0e411180a60418074540302d019015000491103a04a2640811010140c995184030f52654019910075160005988010810f001815207a4005440c080703014000350701d000400a0060b2250035504070030005990001014940b00707000d1311400e960302c10446a42c83d2000d1180140c1c50600b000c0030f41c403900030030100240042c01402200c0380809100c0640581d1400b4401420042003240b600003c0d900405250040b140420300c103448018100545014142c1d41400c4000d00310746c01c0710704600900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 553945728 1250 553944478 553944493
    0x40e070212180607020d051c030e06010f06050315030d0c14060c030402190b030423010501030b0a09020303070503160b01080307030207090e010b150a030b0607080304030f02120c010b12 81
    0x2c04000001d8420401c1501c0326980c07004184045909081020009881c0d40079840b029a41500051013071240070445540c00c2c03000b4088202c0d05502c40da0207101301d0400d02c1c06003504014083c0031b035024582c014448100725541c1200c0c6001b2900f82802d1020003000654a003440400b0040d1000d0015480741640b00106094a000a03c01c90b40307100207803008c0e214083d400c4035460343e000050100d9014094604846031207081c103290000d00d04081d10840e0104820527100c04c05141414401c950490341c100425043e90b4032200c0b030600c004c00c422001683c06000812020010400810041002e0300f00040308820b40009400c040c0403001c8180c1144480b0741080024402203076000420078103607824040001604110700c1c1d005d80c01404402079080c1c015411111648099180f500604581a183d40381844a0b5560314101b1005124164001b40000c400784082000700744551003001c110f10160040303507031520444800c0c01554010b488108070a0b9111a0000a6402c0c80e107075492518034035400400d41c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 553946978 1250 553945728 553945747
    0x110f070515040e010519030f080910031802150904021605011b020a0308070c212a0f06061e090f0c020a0b10050d032007051513030602040e070212 64
    0x1805411702c41c15102c0e4010590180c0000c00800c8004015a48103201d241c3c01c0502d40750a8400d90820708821b440341c09281d40743d0a206000e405500400740e009980ba121150303280d400c09c04c0794500a000c020800b0700901010100f5116032004150410110601e0b101444841c60903900390307207e040701880c0c0d0994034003d44510035000918203140c0780e45810420195518001c046030103056162000d08100d01040b0120f4140c10f05508140d29607985076659104d0034220013080c1450b2031000000c400048a01c3c01c400301280c0c001440200d04d611428001c19072a603030781d0390450b051340c02480319000703500c85000030018086140302e5031a9002c080c5109209400c800d0300003a4031041c041c000503107a0300b83d03140002c00b1001d4421004010f0f0900400340210b2031500e08004000b4503000a01d441d41e00058500718070f4040c00001e1000440f5002040201c5020301c008070814150000c003041032007003594100220014813280041c1002d041c0e40700c2408072038588590001d00d0860440e004c034800300030401a580d01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 553948228 1250 553946978 553946999
    0x604060c030216200a03060209030c011b060f1407110d14031501110d0909050f0408041a041505090f010806091501020a0209040b04020112060609120201110f07051504 73
    0x40c080d000484c2618000b0030103c9848046a106040341e030180c0d1400d0003200b045520341c080e18500505038101c40c03100b040e410054407404002a44c8954212040d0303d00c3c000500550800e840d0480d2801d40459aa0001c4803201c09014040d556031012814480350741108010401a00304426000e240220000744d603160018000e210140444420105089201440e64000d40e501c07025500b0320300c11541600394a8000402696250140020080c10100411895078400480da0301542d000184645021324024071545400e00d804038150b0300420a100024032050038900c4c120760300c0101d03201e840d40c4050b9501003000b0155145e00c2c1d141444410b00c18000251259903070240e006681d100345981039600b510042c4d2401c025960000e50000d10501040100901c8910441c0182d02c00e81382c608243d010620b81905840365030140d18001403034040300700162850a451182090f0040c1000c0000d96103c01c90241030102011110f0700b1644108000c1006e8204450100e8101002c80045070400e410700d00b030040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 553949478 1250 553948228 553948267
    0x130c080c070615030803060a06030902031504021c0c0303090501031a04050a020f040803120f22390803040308070f020114040e01080616020a0b0709170604060c0302 72
    0x1040da10001c2512810012154004002000d00014000c8615500d1500751241c1e8401c450150140b00600e000041c0607010b4001e9800b59a4020080c2c00e003910f00300145001c3c004c1c000c00c00e81e40074105081c2d524118001101404900b40640140d40209e0b04600f40681020312560001c3d040500e40189640c002c01500c4440040410403900441c85440b504610300281c01070209014400c0000100040d603014000000e218a880b11441c004035a0388290613844859030072198490814034082607040f0740310300440f00c4110f080c815081503030709101001d00035a400c000368441c02d0303800c1943c00040b448aa5110000b000030304655006514090440c3e898680c01d00440c9801440d240102e10322004580c060600b0100c00040041c4803610303199240d42d01030340d00000b84034550302800303000702040700690041e1081e00c29003801e070014040c90411303507035a0011442c01000d04041210241000c00c00c08a02038840d40c0d0054668002c000e182003074200324041710381c4081400145032040102d80d40a070050403800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 553950728 1250 553949478 553949491
    0x518060103200f040924030f030507060c02032106131505060a0c0c09021303020108060d0605011401090f060206070507060e10050a0b040c020601170129130c08 70
    0x114541c080300c0c5158112101d1282c40001d0480b01041003200108940040c1c422144201d83c1031180100c014480c1d0b2800c4a2a42005d66400080340b00344081043c0f0158450058071920340035240003110f03102c580843d0140c090f802c0c016080044c1100c82840048400e8030311140c4c4155011050a14030001020082108019602540c40d0b1265280184c00003407070500426003c3e060592324040032200400052003400c0444d010448090041a05002071003550380004001b048120008d085d9001520000710003425150300102540071440000d04078000d460092000020304580030f09400005442590705403c020000f10740102e041041d294001101600a085400c0c1a0795030f480740c0c100303200584121440d4000074841c00b4003802800e11a54407007442080840010040d1840303480c100800d4800c002c043e40c00581c481c40061000105440300840110086030000071500c44503c03401c1c015000502031101c5000e40c80070220f085042c0072070000a0a09400010000011602405006414007030b040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 553951978 1250 553950728 553950731
    0x110c01022b020114070908250504020f16051b01020c03032d12060f01020c090406050a0e060a05061005071e02210c03010b1e0906030c1203130518060103 67
    0x154400503000794000384c850a00b4040032100c91420000150207003005c1d100e0784605104144104104919058500818806184254051618100c01c00010750000945803600210400c8401080300810000780800c40c40f40000c0c00200c4c42d185014515501404003460654004040700b05c031a44d070110854000c20341c290340c50000304c3e0011952100400c04403011a10b180400160400d018015a1055104a00883c3c0c80038803031101c0001262554002082d890300002030b18082000520181c01496110801c1040094040080780d001450040140c44a110b0b180d40d440c103114450402c072510300c4190402c0e00300a13141941c42c5e543d00601c803104032180603418244510000031941d45880d11030141d130b0380b120300c0c030407101d180880f03980c0340c0d100d84126502ca503213400b1800085040025014072a01c0900c19031200c1700f84402d0074004510f01c000c24155040c0030343c000204060391600d441c89034000a03480291f44880744034100c07072044402070b0421803082e03a80c2144414003541c0c40000d15440342080c44c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 553953228 1250 553951978 553952053
    0x1a030c0411030a050a0905060a0f0c1412330f010302031b0a0302160b090d021b011b0203070e0a0e01090b07030902031005090a0b0c040f03030f020319110c0102 70
    0x24017030003e0112540c0240240204024440511100c1e0002c8400c0b0392104010007001442c0e40c42524412540e0305520303d02d80d000c0c8500345e1303500448800e440d804200503801c15031b8a100101014450120701e03044581862001040140c682030001140311544c00a00303045155007411075141400580505000f2098038000070700082c02c61094042d108400000700c420010705469150003030035640201d40c600c480c1e1141c1000041d803a03100041c1c600350600007100401c0c0f4a00214011650f02c094149151284002d2481050050324100b002c00e0040c5021041400b8a00300b9541c11000d99803a80203101040c0c0c10704000a0200d00305a050581143c00382c100040c0041700d503c04a410020740002d5114090b00d0710003000300600d400700c0e504810304c1c840d52407070307409a64030350607054107005501070010303444e401620a0001034010300c81d0b00c0b0100c040f40100c80c2000305582659180c0410541105d0000320f81d81b00354010f80004004504544e01e0034006840303820039240d150000d1821411041c0507000b290341c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 553954478 1250 553953228 553953241
    0x12030415020d0509010506150910021f020909011e121505010f05040e01200906071b05040e0309150f0d060905070f0f0507020d11041a030c0411030a05 66
    0x161003440103031035650195228203032500402c000305000c541c4a06503508010010710749141c00d22a0468030071005406909110000c1d09103c1d40c6010174103904194414030000d51003211200b01100902030061602690b20360020b424000c1d140010382c0040741e4440c0300c1c00d0704030401e154001000c054071102000042c0401c0c4a0600c40780c20b000150030584000d140600101e080e4a0030f00d581c00980344d055a041c07202c00000e07d9254201d80745042c1e40300d0a51084000c14005140007001071030380c0a00100a2820011640c4440414154940c44110ba1511183c0204a141014003070013840504200c061814460420b002c240d0341600c040c000901c000d0005868070000240000391000c2c02e40c20081000300d9901c5040d00d4009040680754030010400440d14031546034850454000880401d54556080210540c24014800c07402401100c0d0b042994001c016944c50714412400020980c244803500321100b103081c90306206074134482c58000c0703003020b41003505104414103e9410642004000400c0d0f85c40d41c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 553955728 1250 553954478 553954493
    0x30f0507060c020607080c090d120c14010608101a0d05120d151707030308060d0f030c021302030709120611040b0d0605090105011709010b130204031b0305120304 71
    0xa034005010724900342000c002260f00042c1c181c4070350302546540589413980840121580641c242c920f500c405040c80100c00240c400a4003041c2c0005410400b04507105540c40c054200c640700001c0b851690350b40c0c4100b00c03901c0108003a5410800980003082040030390028000701c4512003020703a02440810192004201040228025030301c41c401d00d440d22608401c00c40401762052501c15654403c0321540480c000b20f8510742d810005511700000c01c0340d540355070340c02d48840000500c601d034460025250040811000358001503014445c1d96840301c907485620402000307400080d030301d141307551040c01000666038000703407200282c540711b800c1503443c251a031900c1c00203000e40413128100368501050004400002101a213501d400300036061204c5610f4809100c2003000c240314035030000304042010365000b921030f00c00c00c1d08140010008180440581c011404580800c01b040347d040d50300060400902c00680304000032038103d154124074003891900e941d56604d14008892800c40303c000040780400404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 553956834 1106 553955728 553955737
    0x31506210e0705042a0f0512040605010501110610180f0606050a02100b011b021c0b150a0b0f0f0415020703110402070312020d140406051b0a0903030f05 67
    0x5c0c0c2012980c3c00b054134100000c3c49401c100b82d403070104914081034405d50186101052035490030000624039003c031108a40641c204409001d04205040c1044080b030307103003c425903025242007003958002e1094a0300313142a0b614000000074903e03000406080da4520540903981a081428181029600000e2049001070303000c0c06e40d9441240c3e8503001c1c050482c0050480500f03013583e101d401628800141c8143c44448525007000352407440b4401179a200343d400d40e0354483d00da00d8402c4c10b060740d0141000d9443d02d0200882c00c402c15400c0101510700420310b6200c840c03c000030036280a034884900d400b040d105568186400001c900300b40c021500c0442e4195118260800c0085070680207400441851200d240c4910002d0034241d448010795003d140905230000e881d00340003501d22041c00800305e03540694403003031225021282d0401d0314030044030340604185900789c1c9410070466440c400d = true := by decide +kernel

theorem cover : BRFrame.Cov 553776978 553956834 := by
  have h0 := BRFrame.cov_init 553776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 553776978 ≤ n) (h2 : n < 553956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
