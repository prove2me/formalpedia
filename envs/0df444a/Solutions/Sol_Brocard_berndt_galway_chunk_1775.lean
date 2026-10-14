-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1775
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:37:55.325981+00:00
-- url     : https://prove2.me/submissions/d9860487-145f-4afe-aa10-a5b00731d8c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 319064748 ≤ n < 319244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 319065998 1250 319064748 319064771
    0xc0709060f0b0c060406181403040302030d0504150c0215030a05060f0102010209130e070807080a0b0601091503090312140108060f061e01050403080d0219031b051b0303010303050706 80
    0x101520003061907500075046996803580e40070020400040b10103061810740b0347c85404161189040c105a551200045a54900314010507180c140301043e0750b001c005040206002c03001c1e055005806803c145e003040f0041505901c00500e40340846100c2000006012007042251a015001140580c4040c0d074070440301070141c00124244d12602c50307078a4012510008202d00f403800c40d8414941502c1200582c1d01e12134680b070076241841090f5000c4656980089192402d0100c0004007942028003402c061101c0c502d000c2004034003c4010990100745a0388051020505008109030840c001d5001000c0194081d50189202c012100380600c0e640b500c00c1100044a50600d641c403030740260300080100140c1e982114a010304001c0c0d00003060304108083c440000020700205c081c0c1040c0001c0080583c441301550003019109106a800404240c140300115070f0701d080e5880300c519100490329180d9540c0154031818014807551524070461407100100010078550f1103000340c14030341d110705403e10001c134005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 319067248 1250 319065998 319066019
    0x7030b030c150304020607050a08070501050a050f07030c0e09070c1e0209040b07090e040c0501170712020d02210f150a0605070204090c170c151b030c0709060f 70
    0xa60780c12440018a25045058038000f450b400b610081400f46025020380c0c5550030f01340d89020444103084089003110400200b030040039801b61440804001a00e45100110394840740944094103050f41c40107040c06c110300c9040d151010400190800d1000d0502c0e500040503090800720542e4442103208210300340000071060710f4040e54005019240e26210390300d6030307880c0700c402408000c18004580303000034030f0b40744050041d40320382e0003620004170481c0341900160006041034044002c0030388407410404030b103800034081603075060101001a2141d4104d070070300c0000c2c0715000e0012942640c80402d489944c40300fa20040c803c42d0100030300310311307915001001300d00d503030081034010390040741e01c001800038038401c0300903050a170300043c0007003000c41d9141c0345c03000d0300440c41e002034404145d5454418100700d01085201014030080d14800120359803410b0314402801004101c00554540502000681074104180c0300c43d68201c0301a102c290ba902d03d0303000300503d15803141c030390001300d640d500040c2294030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 319068498 1250 319067248 319067263
    0x90a0f1d01140f0720070b030a0506010203160605070e0607060e15070207050d060603080705070303030b0d0803040b06060423190b070f080c120414040b0a0e0a09120807030b03 77
    0x403815048a180c81c2e086094a501e020080e0050b02c40201d1000340190344420000341d001007d4801070256a410503030111802e580c4020a12415940b00f00440ca0083e40c0001501c2e00f0349800410010b5140c0320a102260300d0380800d9030850344408080303000814800160b0003d02a082c00d1001c0b2080d007010840003820701c1c40100e4695000d604560390400060a1010000d444c05204000c0000d951fa00c943da000000d0304044000c1d513580d031082e2402e004154042c450804c150030121484600d02a0755a6400d21620000380010281038255010540c145c440c14140d801a00100740418800c2200804221500c200421050300c54508031240004c141e0341010040d0998415800c1c0b2440c00302c00381c0b550f51803c0140c0d8812144948100295040040c0030f0010404d07096540c0711035540c4500d000746940094490703030800c6104a151410440482c0d860b0f022000403204240c2c0c0d1a1031960303410b5840c074001c00600e8005000d10800403000d08460f41d024402e58450102d0340c80c1001111a00f2003450307501c0c1d20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 319069748 1250 319068498 319068511
    0x3060c0301090c03151503050609010f171507110c091003110307051005091908030712032403030206130804120212070b0301031718090a0f1d0114 64
    0x808100600404400c3d8228007481c010074140420b5044a042c3e02e6100300285903c65508119a0750760004ea481d45030044a820603400c554650541d410500c210100d920184100301040c64800f540b481c40a00500003c04141c4412f1840c49071468034075005025011514220306140c040e21100810341d00d80381c1801805142c0b001003d4020500755600d161a200040824940c144280000040c1c546c1c0c81c42402d0441c1c049030b640702c689902600040c003e907007041c0f1322032140c02410102c2c207000d04600042a0b074040340c5c108450107103e5454000c10b40090444901d03001e4410045001003d0080ca03a44005044a00c00d030708443c190780e5203034549440e8200304031009000d140d0401c802c10140002400001015000904090588020705110351920425910105507550040010800c2c0400040402528512003010518004032072030b121280c801780980351481810b402c0e010a262110700d510490004000e80310402c00f281400100102d280c4811401c0e50443d07003000d00c0c405885804075241405000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 319070998 1250 319069748 319069771
    0x708010603110f010e13020a110a11040209060d11040e07020c0a170f0601091b0c0c0e181905010510050d02100201020c06010b0a0e060903060a0e030c010905011a0306 73
    0x6040c008003c1c2545600b001981041311000d107580c440d50720071507015901c0c68000f00c0141e039004103840141070781d03003212181c140070b800207242080802d2801482c0d51528204440041e07a440340007000030741034012400e091030311501d000752400c0c3c2c80c41e0b031000900560740308440c1c0801d9641c50400c03c076a101140c091454100302652420000c2100c44c800020700c00c81c5110a85072207403549040307585270030002d900ca1070715142c8410018880303076210240c5451030702e024502180d0514003600c5100c1000d51074410014010a04400240000c207000652517103201618140c900ba140a0400f17515081c0200f030095038903500c2c00d4003140e41c1d22b10340c030328a804440f40039200d504000f98030740800001340b07820380f00d01080d55002c1103c5c4001d08002c1c04481d018000c818076090700c0b014001d10080c00702e080224510b003c0c10040040400d80e65002508690000002c0c1c00030130280501c80c003113070850140f012400740540c24455410100310042d0090115465044841d945494014040507a181c0d029503c448004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 319072248 1250 319070998 319071023
    0xc050a120f050309030f0c04060b03090604152a1818050a02070c060801060f0f090504090507051005270d1211061e0f060604060513050a06110708010603 67
    0x21401c105a10040d4040c1080d2030400f007448011030f0400c0500c0c421241c56801c995000341c141e260910440b0090040003e1881c00c61500150256885401420242151128802d100f031280d4013034204500c4512012942d42810308100c400309001e1540341c01860102d544404150440300b00c440c600f0f000c030b6000c1000c2c20b0615560003840c1c0014400945143c0c0e04603002c014250101e21502c40090082c101542c1d4100705624002c402080b51030600c0c1007404100310401c119a186070303c04c2d001c405550080310b001450300303010b00c0c02900c0d01880f58081c42d00511019443c650940e00400508080750181c00b41c13001e101140400180d078842c0698484d0b90207402c009040b07002c11400800740741341c03d1060400010502990400500d001000ca030850a001c03040802c050902d0f40c56050315070403c2c0c690b081210203040041c00203046004074000c1104002000c10403841444210910700001c0101510900615444031001054100c000041c1e0307405108000002031500d80500c40c8004807030f00514503106030b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 319073498 1250 319072248 319072253
    0x15120610120c18030b040302100b060405210d021015080613022206060e060a02061f0b0d0b040b010504060509060d0f0507020c03100b0102070515120a02070c050a12 72
    0x2c1040090b44002c00ca044a80d900f6440403101610015500400350b0001614061500030302d465400d240100e6058280320b1a00610780300ca8050742c0680d00d04440301c250042000014a0b26201201016401403261210301800190007250180f40000d10b00d40038001e803140c1c6c0401091382461407098101513408180001c44188820f0095005184014009985401079841210552045052141710541e03546000c01140340c20004038900010285e401500b071040c80600070391540700c0100001c038501446000b06500c050706440100280c000c58000d00d80351310340b021115008000e8030714111f029619010458055600030000c0c0d9040321020f0760396074a08140c00083c001c0603041201c2c444404c5460782408010200c4500030b03c1d1142d149a03005010b281745800800d450262381148000c0764518009050016907404608842030b41c00030303101001600352465104101d886030395110400d2095402c140034550f5010b8008011031030046180160700c43e00c0d00d04101183d2402e208042c42c0700702c0b05000200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 319074748 1250 319073498 319073501
    0x10f141e040b0a0306090b0d03080a0b13050105030c030f03040b07030306090e031e03060604060e06040f030309060801080607080403120b060d0b0406090603050c09090c1512061012 79
    0x1150588508000c8a00319a5490400c5400a4114160b50714001c154040301c20b51502c81c0e0001081001000e201441c0d1100115002030101c000c082c1c10044000d000803103003121034114000001000e0800c0000c1c44e20300c0780c2040217000078054507100b0f004030f905d030100030b20300011035800944015000c2c601e007500c0e10900c3c840706e500203102242031540b80c0c1c8000680c483d10f403140d400c1002c0c66601441d07444025080a0710f06486422007481048014814465291104010b80307003a900070741040828611104001000703806280d200c5400303011070220100c00c0603882008081100d4840d01c1d02501070340c90301c40e01901c559044408000040e034000024000c04d2050030560758400c0b640600250040c00e06011500c00d0380140b0300c26981c2c80d00c4014101003402c15119560040c16000030802c402400c6030703074079030f210600c455256100d802a17101180703240000740708844803030400916000000010020780005900683c4440307100c240400005140c0781803d810503041069103a49016001800390075107030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 319075998 1250 319074748 319074757
    0x30c1002061807030602120f0a0e19021507050705011403070c240c110c0402040e010308031905010905041e05070e0c0c06040f020f1c020607060e060a09060506010f14 73
    0x15202d03c0760000000c04241c5d54070040550044245d03c8020514250150f847c1c2c00304e015007d007460a00e00074048665001c00b01d848402a44080b40c44468842c05000140040000d110607051035940050b058080010018011040720401c3c0c90b00c5400d021501700c1c01210740030466081d0089000b0b00880e8001a00440c02d0307078045910f0141141c10702d07103400d942100b21503500c24200c020804562441600d41c0b020002110501c80c1114254a01802d013510030181c07200600c8010030300040403011a881400c92007051038030f000a82030070401c075a900c9079040e0280000b80e41c00c0e595100c440c441c1034002c0300f01014084160741c1240c003c0c0756084c50f0a03210107501b10020004d41c81d100d800d21107094104401d0008034002d03802922001a444441d00401c0b0b949401444014071903c1d003101c844000c00038601031402681e804440e0b85ea220126410048081c22030124494000c0c05443c04215045d9070b00e03404070b4141070003003a01b04070950701c03c0e006444c60040c603415039021980d8014034452046590300240b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 319077248 1250 319075998 319076041
    0x601290304171201061e170a0902150403060b151e09030a030908060106110a140705042a030605010c060f060509090a030212180909120301090605030c100206 69
    0x86250b404549165120307000101c0c2e4946401c000300040005590150400101c444603148903030101c95100005030005541070340054680c4499030004401c04099405403441580103000c2d07114808038844008013a910030301080354561700e1316101380310900740707202143c400c1c07411b2001880c500041035442000040180c060711021440800480720281c03805c1c0042d851a600c60707160344d2400c1d82020701e4142840b2058000400f04440303401d050b1140a00016000844c030782107040c080003254507080d81800e041caa604269005410419013164590090303003d41c10264000c01c80301d0313100d86611021420780b81180b15150010b84a05e4403580468030980c4011420414038600081c126580d9003c0b5030000003c40b218107180e0805000e020038950140802c0c00540d1800403440d00d40740c030701c40c00b1011245a404d0321500554625001031942541007151042c5802c84408043d160b60392031402102404403801a01d010f8014013954105070304124040007043c40803900a0230003669180000503c00070700c007068 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 319078498 1250 319077248 319077263
    0x602061501141c0e0a02010e1002071509080d0c060e010501060914120a081213050d050304050118060b0f061c0b1809010609050f07090303030e0106081e0601290304 72
    0x11200040d020348211034100800001411800d9446e00000d0074034803014200901807212800c0c1f40400d6035001c43d519003554042560405d08002d0500c04440c01d0605030007650440c8180c0d520305400c981c00c00d4224103d04c0c89044140204241c2d038620500f83d403020f10600000c07a68a0384180f002d0650207082191560703010300040140b1030404a41481e00010010075100c0c80302c0003c03a95601c5203d4034029900c089008902032507c0b01030359034180e4600161102d0410424080301140411501b0b4102840050541030854040c500310f0811030010714481102074071070300002990584500b413070000d0b074418441100185515800c0600ca4034050300c104103400c1e5008001c070880c1100f0101078485240030700040c0000180460030001400215407002c0d00d4a150040300008000341030740c1c0010300b0400d4a40c140b50104903d2409084203000d0f0020303400c200058022401e03d030300e003500c55480c21140c60390444126511030740c1c0d0b03407000b920b9907509601c00b2410790124000a01904000c400a60308907114082 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 319079748 1250 319078498 319078537
    0x4020a1101050c1809070c06020307090914160e03060c09030a05030d0e1b0603070f0e0d06051b03070909020a180801090c050301020309370b01060206150114 69
    0xd00c107007115411143c10086002c041244a44094a114a00d6034800e00381c403401d501d0f040024024144c45051940100050303000000510590b100c1d139504001010130f590140840117134000500e043c00011a10300c01d042d6114088113121070311a402d000b0792604054003400399078440b11901a01e540c80111059058841c118014000270000c1000b00901d0070b040c08009040c0480010391814014007001082c20801442c3e50302c50f06a440e01c0850f9001456814000d9141c0b0100c402611040010381450b075015007880710840a02200360080c0380329a05849000589407904160190940800e4075100e0025100480c244201005030f0700404400c40a420b000601c01a03056141d40310004503040000965103c106102c20840d11384200805407200300c000350300718909014125543c1c0b0404d003803d401407088415016114180841040c6a100c500d48960b070440110b003403c1c04001403c0c420382d00148521070000f03040100c1d8002128003500305955429074460320308407001b501c2d00b1010b150142e903d18141d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 319080998 1250 319079748 319079777
    0x702010b03101b391502070c12140d0c020f190315110307090504140c0d0c09050d030903120207060c06020f210a1d0309091308030708061011070504020a 67
    0x15054806000904d40b00403004030149042031211501c0c40c3c00e0040ca038010700c501000a0209121042030b100c645031a41c2d0b140c9042e00304a00d04004200d4084264060b0100c1c9491072a404040d000c10b140c001d03a003405a0300b0081701807240f410044811040c000c0e401070010303c0004c8100d0f41041c4008409000422091450410001141d0003680d85001040745424200101d04050003031004000c2c0c248042503071881d0804d4980d0b030620030103452070700d0165100c0d91a030500d402001070300043e240241c102480170f1480d00d4051b008000500058400c40a20361050701c20505c0001e6400030344401c1c1c0c0d1007544902099440700c0180d0000c1c00440949482441040c580c0d590080d0151a003812403041c2c19414117041c150710007107442c3c0642044001e007000e491442a4540001101d0382c00800703480d8483d00346d5030682c4407011128001c80c020810b000c00000c6c006507039400440d00c0e004803c1160030741d1584807401010b0380d0f00c414500640c0c01070b820002040107185083d40c05498502a14145101e0010680 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 319082248 1250 319080998 319081067
    0x250503161505010b0310080105060f041503051005010f150f050d0605060a170106020a0309030209060301020f030a15052704050c130608060606040b031501170702010b03101b 76
    0x7600000d00811005c070803c21001600d01d11a80208000e2000300a141811008a841101803074192030149446605280c040301c03c1401c1540210341000a544407104140d201c00c02428080c410301c5055131a103003011030155071071450350011100d5503c070740741503400c0b69030280c8850300148014048140c0d41c03980000c103510760038010510340405954040400d4084042c681e4520f006810072002c40d408006101f0019400c00c50103000d07a0340455810000350344100000380a403050040801002d6004014810040d6250b081440f40c40700e040d00c008912621001400750b1043c0000030510713080924440c90b030795240c42415240c1c0090284080d034a403644048080b5140c010700b40c03540d00c01c0642d901e608201c02c0e0f20078007036140c1280e800c4030100d1905290842408083c04090302030904c0c90074104084506070300403808640c150446c17501c00511880c00b400041c0c001c0043e024407502038014000d000704650401c0c4103c44c202042070b00507184100c042c12044590482c840c40390401d800342140803d5140d00036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 319083498 1250 319082248 319082251
    0x609030605090a140c01020d0e0a06051b01020a1805090f01031212020a11011a01020303180c0406030c0603050f0c04120f050106080109021203030c09042d02250503161505 75
    0x204000c00032201c034500024039080000c0f2300d031010031113650300e801c131255240f290301c01c01c4500e0381c507149460380325084400311000c4c103015403041c0540c80050417250164100f450b81007500d021a0381841000d50307903024040401422070340c1c010030740c0754040140002181c680902e54014501d16180211211141d80d240c00c0703a000740510b81c0070031885800c4083c1c584090007803031039100c42d000d1030200007064400040d55038000501056074801a0081c4924103602c108402c05550100601c02c3c4640ba40d04e08254032203c0003401544006170822000031040030300040300a01aa0468941901c4c0c02d10700040c21004a0b6a01400c4900c18001044240450310901916020740781040000451040c24810001154040b00844540d07810a01c2003280114008003a81e01244003510081600122600f0401214490440000d0304069840781c10890301006d5016044106124031380c118481046100c3c207810701c0c50308500421542c800c000c00c0c60004a0502414002e030301c0303202c140e221910144952401d4680 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 319084748 1250 319083498 319083533
    0x30f050a0c2303030f12070c120c06051302150c160f0906080f06060919090c1a12150409050d020102030603060a022701050408070602031908010609030605090a 70
    0x140d407902030b031610031502d07000d05802c0c81240103501d040b02600301c10085000710390901e0652048000000d000718002c03d4a056000d60040307950b105443c841074098101c070650b090940e0460319180000c0c04c000f0407546082109a0001c00b0580210280010301041c4e600456030034005014074203d18041e03180442e45d03c4080d28182d4280100360f402c00b149001151110340c0805083d5124851080d14801c0208000381c1001055690303100c603603100b11140500c070441e801031100e404e20f480000e0f000c0c01602040c400a48840340200c85005859102e03ca03070b10302540c6007500844840c180402c1021070030601e69484950003610100e03110b00c0700d80fa01404c012407900c1200c0586d400004011092509201041d80b118088104501300002100810300a00200c00c4201c9100c545049110352680074100b074030028a559070031604070075220b15000b0b4480e0001c1c08061002c503122041c482111b070168111a058840380d545030540c0b82d1031074442e04081c0c800503052100d40c3c010054120040b54085400040e0b148 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 319085998 1250 319084748 319084769
    0x50316031e1b0305040b013305070605060f061b0a060603050d0f0c0c2d120302150108031204081c02030f060306010311121501030309050111010c02030301030f050a0c 73
    0x1003a1007100e9040c60080c0d0b000010580742104000001d4072440040d41558100d0b80c401400381100300c100080c0c14680c0104440c010403089042c0340341a071000045c82a41d12440090001c0e85922007444010090340b00010742c86003080c407543e21a071441c1030307004843c00000c034200c81c0c030414142c6445048880c2d940058176181c01200180e454141c0103034500b01c00c81420715080184442640342e0b0a11800c01e070003111a0065090a40440c101c4080da82c1080c80a2215016221594a098a221b980180603044026000f10000104c0705810041514100c440c01c402451034100b2a50305594007200c000c1003100e0702201441356101e04080a117244010950f040b10040e92414030700842a07402c00f008001030b119601450041c4002020b64031800c80200050320884d19405002401c107041c00b01790580c50541040a6000105155101000400721002a00c4075041610301a002c5400d1b6010703000308a0150307104200400c002101103905c1f003040c0d0300840070f886400032540e60b884800000c6030300841081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 319087248 1250 319085998 319086011
    0x5160b01170609030703120b180108030901020f1204050411040801020f0301050f0d1203050c070203011119080f041b0306021201060207080f15100509010e190507050316031e 76
    0x141c08015550b000200d01d0015814520150740041c80c80030040440a43d0f0b42d1541440b00326520360312800b2402560a07900a1010345c0c4540c40c0668a8000e64001070040c130800744081440c0c0300218100500743c1e6101ca031545083d05000900c005001313045503000701290308000000b07a03c0c60030b20262090510702210582d0300d5140100b00040c191f08802c2c2c0318828600e040341c0d03d0004883e001c1c0c0215240850802046c83d40c0d48007400700c1d9034014414003941650078510851842034028000300303810b614014040c2c2d0402c0744410304469210086840c1046825040003240128100352201c1034580f4125260480b10750304c0380d480c5416078000300d910710f01c0c1000302801440500d4041c0204005040400c0042c42d07a04088040581e840811142803250300810101080c07041040085020186c42d0181c00d0021550303503100c3c240402403040b00c1c4006843c1d2420544035031513070726001d1180210200d075501400c54030303000c1c1139405040111404c001810381c0c0d02095081c000e0040902d03404a0141180003540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 319088498 1250 319087248 319087289
    0x6090a050d0e090a2d06090c0c08030109020903030918060114031006081e0c071a070c030516050706020709140c1603030e07090f0b040603050d05160b01 67
    0x188040807a000040c80280500401192140500c260344a0708107003001c2100f0300c400c4681308080b84942101e140d001c150380111a07052140e9040081100c00301c0d0000c0241c4800d181c01220400f0610000130400d000800040206001e0f98000e080300001c020256803500300c0c0d800015888040300b420001c0c4c01081c41d001c012040d0380050f20303040318440b9884458034611b4444d0000040100038010182400350110100381000150980c00d0389500e01d00c03031000304a09003090b0301c120ba0b401c02c86003101c3c44450600070001d0301c140302424070b008091035211050300c2c0c00f1076a41691244c0140292401090b408814000800d0040298000805454014101c4c840c00c0405910a44000305070060420500109202002c00e87c00d00700c2e000c030340341e180780d80c078155819190840250107013101d15441c922504a020548020940c020200e1480341c000802c21071045400340025101203200c0580780750040b104180301c2c0c6000d80b0040c509000107401ca014038400320341e5860490642a0420009048006209080e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 319089748 1250 319088498 319088503
    0xc0603010312121505100507050615100908030307080c07050d050309010c0203041401050903070f090f180201140d200a0206012421090f0c05060f0717090306090a05 72
    0x22002041482407000c5418042c4c3c14404407000d02c103c81c042e442c01c0a0701c03c070041c8500243d540743d590020645585040c148007140c01d42c4c0140c3d440328450301e004400c1895081c003896242045450b9800030314156070311071206881c0440010300b500070800e010402c0d40000f6400307001e040091445a2a101c0d201d09220603114212460412287c0c159402040140700e20400000603001c0c2280928185564803001c40c0881e0030b050f55036100281d0740030321080200e90340e002a0000704249640708000c0004800040152848964211010740030401c0c1543c4654103501e028020265149210004214102c0c1507003141045a0030945880c1395240104003000d00640c1030205070b00410100300c03040a80b580b460010a00040380440701000e000f850740c022940b0903001200d0300708502c3c46000400402e61181048401080304100c11a00010b2030382c004945868210152214602c1801016045c4012540c40311942c07004e2544840401005001500d0540d80400900d840341c80400068008804546007030307407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 319090998 1250 319089748 319089767
    0xc050c0f0f06061210090305090a0311030c01050f0a080a0b19051e0108010e0901090c030f031e090902090d062315011d0a0b03010b04060914010e120c0603010312 71
    0x911803445210340080c40003000490611094031450002040c984514060362300b80704403d0903940100c0b11043c00420702211031145030008200742d082d5001c00c481a07004544031f208012140340c035510180038031401c140c800d01c003159024500303079800142d003000b940004444126181034202c905004580070701980c185880186016040809082c0e6410300903000a1309111050242c00380001c0040002011603a09400200c1803d822007038101400b5181e0400004a2a015400b5800b062074089041c80c040da100b00030b040040035a43d01c8031402d0f030604034000065448542019400059081144082000e510500f80e0760716500b200107140e0180a20416030110004081549800010958a000fa40c1007441c0c40315500040c601000100c44810014121020710781146000f0703440400080f402e01800380040040d1001c50712038130f045070395807025415045101036071140040c404c1e100d204002d0a1480300c100f907195810041c0c46480c2191408164160426030080d02c2c540c2c0c4a400036402290480940c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 319092248 1250 319090998 319091011
    0x1020c1e0a0b0403180b07210806031f11030a200705030d0b1804080901030b0d02030a02060705030d020c070608060d030c11010c021e1513090c050c0f0f06 68
    0x103008000890300c2d4503001c690010b001a09100341504640d000d1202d0f41c02a1010b82103000b00140c5518207800d107444402160b62415400c1c541c4440211440c602030101d440c442d5900900901050407114a030540110203848541890398948406200b042201340156100c1d03410050b00158903c17035004103101d002c1c2c034114107000c400c1080041d200070a03804000c42d01400090240800c0c10000300c0d010600880c2c000e07050041c00c0440209000410600c0002048400750984e8240304500040c400c200e601e108018000798164088100c450040c20404042c0c034599001e0000d8904001041c3c0461f0142c1c0e0000c080303c04981c2141c0c400b4013005820040c42500f081e0159110642c550083d034019000c0803206c64080c0180c5100710140c001d980c80344a2030040554041e0504403603030210340d40101ca001c0c0c3c100c6128440e01d4407030a0b140740c070080101502c039400450b5810005540c5003801c6607005120280242d0b00f0403c00700030307008000200304400c00c0440128002070844040a003145818014044c019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 319093498 1250 319092248 319092253
    0xc0b091510060509010c140609010b09090102040f031e02030d0c0c3c0b040e100e1b03040317010305031c0b0a030201030e01060519090c0c020109091d01020c1e 70
    0xc2c0940c0750f0160581303034410005c2c240307000403004038100880108a50000300005203c0c00c000c002d804541900070412458003134803401056114090594281e0007140915405c500c00b9000810201f40c80a004030100e40715506a24450034032500481c1c10801811742e4100880c4444101e00c040054288001c401040c030040d041d00c00011900380d1500c01450b030b1a18403261a048080004404200f0798100020309503002e01c0c03940c0d15602c01c10010407030000c480d082108000100000703118200c4100c0e1a201e050402c0b80c0d181d90307210070248102c060700084d00c150104850502c0128002c140141900e002c2d501450096444214180140030318214441204000c241410400e40c0d031a101d001c40740c001e8a41c242404100769141028503070041920354021688400c00e044296158901c1c10031410640c1c22124081c400c210003103800351844042c00f04000c0c0003544c9840d04111101d9558040c80c81400ca0788003e50480c20001826426600141404046c94000002c0c0c1402403151640903400080004003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 319094748 1250 319093498 319093531
    0x21911100521070e0d2d05152703090a0b0d05241e0a0b070c06050901050306090a140a0c09060819111e090a0506070b160c0b0915 57
    0x40050032a010412018000c200741002c0314100a06d00c45083d14468400741c43c2c60002e030343c403c240d18112090040a452078001c00040d00d00c04a00680b01503c03034405041d500c5c95a0200340b2108002140f10580f543c824001400706840070341e1a0f00900f00103041c40a40345450310841e001d10350494502400c0518441c4154180b80c0010340c142e05101702c0282c0131603901950a0039203080540c01c0140820640c0d100070314103000708404005502030b00c08a402004d5407480c0f83c0d21910262030900c140308a542c04582c09000040311864034000950f4062444003020440041c1040d15010f000d20580b525583c59499424584c14684d00210382c0000340603d1510059138145859510008450070002643c0310f510303a4456060691030204a6440680305200c1007090803600c84500b10541002408510404940d440080c051602406503650f41d50801140e140070f0311400d00350b0300c40100c403005040612910520301d80c08501003851280c400c0b01240b02138000d414102024005071840140042c80c0d111040c00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 319095998 1250 319094748 319094761
    0x1204170303090a020f240c010606080907090209040204030b04030e1906051c06030c0807150302030610030b010212040f150206070f0e030312070201020c010605060a021911100521 78
    0x506031049940582c2c5c3c00d51440103043c08110100941c0c008088000c03241c0500c24619002000203003d08680f10f03000300071560726118200d03407092003910904210b500c00c82d0103102040040d0300070041780c84014001071601e0364a6492240843d821a03064011078510302d500b00260505c050306241082c0301c1c040d80442d5609003400a011801210450f0740506050b4902e105401d010380d0041003c2c1d90410110800d00355280801a5140380602800c2030301d40c00c100198407590f010f4000e132401040d00600005129142c02002c400400300740b10030354114071811a075207a188101100500c017401c80c105844404604110b018280e0385d4151134a0411580050108020154401c000000304161460030790312040c4e400000925600a005140440342d0700f4809001c51a901503000748100c00c81080288010b40d502c204001440c010040c01e200960002c0780c144180f04810104684038611801c141101e040b1110003140d40105110000c40c081400010b1340000d00540201340d40701040c2c40100d10000e0714010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 319097248 1250 319095998 319096003
    0x10b011b0602090307030c08061008060f040803040309050a09091a01060c0209191404050c030a0201090618031a0106120203041e140a0c0f08071421120417030309 71
    0x988058840d40c2d010841200f2960240980300081d500980f0381010380b03468180460312502c09448280d08040d020600007400100412010b01c90b918170000d03400c081e81c907078a0f0301106d40d1005000f00e04211000030042407540c3d0b40c80c1000d010b4040c1c02800500a01d040c94032480f8841000a6641c800d124003004201e995445414a005a03506403007504080c0c4400050306002450450f90318141c42c2070141a1403a00130100500f845a0b016104079000360381444103160f141d221610700a4005464480280001c0340a110400c901580660b20074903142c1c3e890312400c08000c22110b40c443c900846038010862658042451071540c102c01d10f04600e51305142c1d03910b816000c0c00c4004040400c03e051454030a000d803ca6600000200131801d80e09105004d103008a0b0b140114025511060299a4003090b03404001a144060303032512004c1e42601c2d00348004010010a9500c1c0d0b422021284401c4500d07035490070b0045618410400c03003401c3e1100d0a005e00300c0c801140c100c40b90070141e07206104210300780200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 319098498 1250 319097248 319097297
    0x60f05030c06070f0f060504020a05040c140c0c1201090b0c163c021309030c020d050a02100e010e010c0b0a0c1202070506040b0f0603070e09160b070203010b01 70
    0x12184241da42081d4134025820f942144000f03400d180d4200c840307905002098001c14491803003120b070105095190303c108011a0b0b41c0744000f000141c40c2801104803802c04031300406820840714100c0da8030042c1c15001031403011381d4002c40c1b6004d0351603034030040400c40e000391855081140f1200c06070070b009203030006040c1144503c50107001c01403418400c10350420300c0311040301c0c0c0300f0084807169024142c4031110209170020000803402514070080e400d081144510510002c1903041c0d86800f80d2007025020000304900001e0203581e03a00800b0380c81c0005a1783d001f00100d450b41c00d81c0b500483c200c9980c00140c4846102501d40341400861004c0c4000580408920359201a003644001654104100100c07041c022016448010a00c0041c2207030506c00700069040c03166100e003942d080035655550003414010016a140c507007503400903405011444140d4413450b1322070404002c4810f00000e90007159440d51859000624929000030600e06500b03080c01070303010600702820161102d1041140b11002e00f480e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 319099748 1250 319098498 319098523
    0x70204061a0a051c0c0c0309050109060e12010e0307051501350703060c051804060806010605031e07030504110301050910020c01020c010f02040501110c100509010e030109080301060201060f0503 85
    0x285a841ca040509090f0b0144139025800c2090004041c07000c0c2c018480d000c0f0039404a940500b0011b5590b101c1c160182c1901d1140da29030058441c81d030f05020400c0c0d00b480b0421243c0d501c643d60b680480c08104041c1034164001c2d4020a00d031045040b00c10016030043e00103030700050983d040304030011041c005280e00b02400065121085500582d29070804107540c00c004c0a071420210007900d6a64401c000d000c00c0b01e49032106c914000001c504102c109c88030707440b426170141c0120004000c0b580c000c10103903602c004602040d4105254914000c039410104a41e4000400d0380c070302c01e100a12580200740c41c2d051100754000c000509008c401e680d5250a6084403071115500007500315440b032000e4040d1000c0d03100315402400001520049900a03410900074070b070004003001c4041203640310005011500c0304d400340c0b82c85260a1605800c1741d40e80e0080d05100e0501840310a644110b480c244202c041035402020002c0c0c0f20350604e0002400e40f21954401c25a00c0381581d41030003240c4e8081400b121001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 319100998 1250 319099748 319099757
    0x60f05062103070f050c12031c060f050f01181e0608092a0603090105060301180803040b0403140c0a11030c0102062d1008120a020604020d020a0812070204061a0a 71
    0x18003480d0583c98242094040c87d0451801c502d03d0f181280c000000d440201c2c40708000c0ca246150083c09c82c01124001d1181c8401140305003001c00c002e040c01701e1459202101032425a5106c15503034841d00c0c80141503403100c1c0030807440a401c0410f41144e2a4107030040d00482c0707020021404c03d041d42c01d40d928035842000c40c142c403100c5c04240071020001155031f010400030340f00c1500d9240c0301d5070342c3c0c2c004d01d0212080c0d0300130750819038003110300300620f41c007401c10540c08034443c2e065840305d4590104040300144110180107100069244130b00319003000e0692080380744014449020b4034a880b601c45100d4001c0755000b513003e003c150006e40c1c0c02081240d0308c0324480303c04c1482c68280d07c500322110b0170031644200c000003144c3c0c10f0003100b06450120400340c40090040303030300e1001e81c00d40040161040104120068100902040052400a0161040d2400100202c1d4815221140e490030500c40008054441c0f500040300130842c1010302400e0000c00350030000c90302890088503030b0211886100c280c00c0401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 319102248 1250 319100998 319101023
    0xf09090309030a0809120a02210c0a080a031701050d02010c02040902100c11061213030e03160608090303010f030201050f041203050d051014010e0a03060f0506210307 73
    0xa4408109a60000e80300400300c034a181e01504205141d540007000c0c4a0140a0700364003060302910010741d100d40240d003d031050700021503004120039941c0c0c150405003101c0c000d00c1d42c0240103175249c0d40700002426820021782900c0310a8034015080c5188480d40002607108000100b001d5a00c041c2207031121602800c0441206129100050060551600083d40030302c0f80942c40c044a94049004c0d952035114252207141d40d44004204040c031f000384100704440301150303000266030b200030011002101d842400c2807248401300c080082d003030240f090669130f07034ac6103028010480158007400541d040440c0350081c0d880c550402c031251002c40c0325400064107000300002c1041c0000840c0e811036000f0315030f07a55841407001951400030041e522040b212140319040c60007140054142c02c450004541c028140380e441001200019100302c040d0300740302c82d80314041c4080000480d000d13001d15840c281e0001ea002500341b601c007041000040010642c03d1000a00c2c0170b8074100284000111034006801c05000c4125 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 319103498 1250 319102248 319102261
    0x12110708070605060108280c18061107141008070c14010501051206060d02121501080321070c0602070c05030d020c01030e0d020a06020d0b150d0b010302090f09 70
    0x510914800511000c000079050303050102030341c0901e015800990710020184c030b03410044e82510001e0002040d850284071031841c4041c110303a01c0710f0b03000d40507802c11454038524020010104055940850701041103c29181001030040c05014090066003204c3c410240104000c11580c04204240b01c003844440c1c004030340001d0007841d503507051030b40c44205040688645500c2c0d501030306080c4030b03c500074501c0c8080010103800118020340300707290140007081e2040031070b020408204041e2500740c034140038190120780c0e0380c1420b801082c040c00740d6200460750341c5000c1d03024000d0508645101c0b0820940c4205001b12280e10800c6c80a0031b5800c40000361300c44402c1e0900b0350b98610b0b07981c0072503814824150303020303119500400c000510007403d0700c080201003460f02016403540742c0280c059006807c221300034000200346502404e600c081d0f50000054003958800403403245c1d2000d00950600047c080f90001e000c94050048405180c800e290550620300c21030041413180c0b00e0901511320031140b81000602 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 319104748 1250 319103498 319103531
    0xf0307050c030a0302180405060f09071b030c021309120f090509010810050c0c0304180b120a0c0b040f030f1106160203120a1e03090c270c12 62
    0x5070345466064940e110450030010300254020050000480719040403520285810710481e4030500001d05100d101d004104e0411907032800c01021101440503000a501075515102071044502c2c1c4a9104e4041241e42c6004001d0310002c2014002246400c0203004030020b074030f080428000950f50704041c0e041404142055a40c5502c581103103070440b40c0d0000014030743c0b900040e060710841003144100003907103c0701c000700c0042c8070f0070284420503402000104001044d0048103487e086e100b020004002003d80006240010f90503a1701c80744c1c1c0c2c4811002d40612448904d00c90003840442c08007441c0030f00d02440a14040c0c010300c005800780c405000400c06209165010021403c001012103070380d00c444402a0381881c00e1004244d00912940c400102e4004810007101d6042c8c00030386034544541c41c1e00008480108409071030208050700c6200c50070004900c1010500a00100d0745135100034400c040000e201d401c8511a04400f460030b00700b00d04c45140c0c01080301980e84030322000100741c1080f060122103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 319105998 1250 319104748 319104757
    0xa110613032607061b02010903090b090a0807091d03030105030a1104020c0d0306060314151513030807020127030602031e160806370e2e0b0f030705 65
    0x24500d480001d9680200401503110311780742c0100046100030076651100403422540030440c004c02080407090288024141c00c0082c2c07850a800508100740c80780c65042c00c0d400c1080941c80481050f444188040800001e11904600d120304480198110340c50320000030f40d80c800d1000050300304c082c07100391800151290b0f0101c60f0f1510200040f60007209600c00d000b402005a842140d00092600100c071840060414529014900c2d902e10103ca90050b90708003c0711a10188007113040080420180c0c0648201d0161100210b004136041d5496000500001d0060342c81134208200001120b185044c855156050540030b907504141c0041e00d0b82d60340d5007800070f041030590303604c07065a03c46010080044071081945404001503070344e52207207480f520305214815018801d00c0c2c0503601d801500360704070f221641074000c45ca40000d00340f042103990380e40403c03d20003066408060340001700c0350240541c0c034041017011031345950403560040246050401c01041c062154543c40c0e2090001c0401c081910610548 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 319107248 1250 319105998 319106063
    0x1031802090412020606040c02150702190506040c050f010f03112b0c05091f030219080406061403030d0b03011515020115150c0609140a11061303 64
    0x254242c01c150404004080c5421215401441031000003150307030409014410303400c4125002801c460304400c078040d402600040c0218210301c41d5a1b40c0168021a19020743d40e0603001d00701800032410203042450b0050b50300c3e04107500a420807029098507990001e440782a00841d4900020044040c001240842c41070030381d040c0c4400a444088684c4501148441c51500382c001020040a54808000da42c0c602841010651289450240441150b80e0301031001b07039802c26250043c41c0080405074500810340c02900d00c0d0000d24581c04100421440b449503002814007911840350b03120360400043d6507446007042c050341c99512a00c2e28445624250401c0003070716404080909400c0d1510030b00c07134036410388400002c0150700b02043c40708840c0c011640302d01650304050480400c1041c849050b50303043c0711a0300c101c0d07482c1c1c0d403041c036075021a01ca010212694851140a041100c21070305015200040e14521648500780401005094101800251007160740c003c010304410541c92445c1711440c0c0c41030359130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 319108498 1250 319107248 319107259
    0x360e13030e0613180b090603010b03061f09020f0307020c01020a02030c0609030c060d021c05010602070510020f010c020708160e0411210d0306060e0a1e0b04080f07121101031802 78
    0x5020400d5400006900501b61032141941d0380f00c00070036003070b9801d1184141e09500840c01240d0380d01c0d88100203842441401d03e01c40d003c641d07900300394801c0383d0240c5c000c1b042c0b844021091200d01e95046c4100301b240f00c402d200400107410107800007911041e01072401c41c803a200c00240841c507514144900c3d5104c40c401041c440e1103409501d540d00195002d1300c07500c10039507401c1c08003c400d2445440f803e410380701e4a034014602c0b941400184244080424940c2055124107000151080001d00401d545120f040d400340807544e02d0158110300d000090748405011030381c604014008c4043c1ca103800d42e07026420114262102c00c10f42d01007004240780001d032480b0003980c540304183c40000011b007841d810f58a0f40e0708000c03c503034603001180c4000301d0b02e180560140d8402003c0042c80146001510051588002d09680e0750341c03040e8400c40c0e40d10503446510b4a820070300309600c1461043c03101000904810200d0981101d45641702c3c481d414039500c0e07540c1419500e000c0102036031520840c1c0340700d07282d001c1e19 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 319109748 1250 319108498 319108529
    0x506211008100906200301150e0405130b070207140d0305190e0a210f03200f010b09061f030f09060b120d090501360e13030e0613 57
    0x802c0c000741864800580725541070070b500314552400207440c29050941c3d124000d05590030100140416840086054204030540c00350f03032905e990b54481e441c0039440051888080c1c41461130704143d0218010507420035504102010001d0300c45c2e8041424290754215201104010035242c00e6401d8001c2d482030807080642240d03210350060304030402c0941010111442d044850f41c0c0d020780c0c1d081c8650400c0c03000307202030f0000000c000664900e40001406100b801d201d00d5008000d0100412070401a2102000b68032500604550400038411058181c0c0143d4461130300d8a0403001040a50f42e0b2103240b9407c0d50308010948001a10a9200c0c541545607030b00184400d04280c203020010b0202e500007148a03104072021410030600004400d0204400b90f110a239103281303008010365481c50807041c0500b07508154056546c10b509440c0e00d404c4120f907144001c00286050049003524041e0040000312007000300520000440e070015400300242d84201c5006941e10071041c1c90650301e40c415030110150018448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 319110998 1250 319109748 319109773
    0x12081b0706112a0d05010615021b030109020906010c06020903071d0906061c0f1a0906010609030203100c0309121101230601050c0f0307030c0308010506211008 70
    0x840480380c2c0d454201c119441d000d0215600007008070302845441100c0ea044181c2820742c201561590310380c0e4000c0f80001401d90340c94030001b0801d001410001c0050300912075100c5648031100740b066099006034004c00c841d000d681c1c082403821001501142c1440010304038a03041203c0e075011030703020f500b01030203584400b03079900c8034250090a224010100b50644d100060380601c00007903100e1051000801c482d568401d40c004841034280e1406058500c3d00c407050122012078444d010f801271810b0122000b040c5845c0c4481400c3c1412010f802050400c2818541000565000a6004021740d031460b0005403443c2040800d07030041280400050110046400e62560075800034a0f0380896030112000380400107001190000e121900001c000040c84440b011a001c1e51040020b001c2d44040c2108540b124034104881a03e190000302c412400110403a4440003095402002c0b0b600519041e01c920781000c0c0c000e80124a445d1700c08400c0c1c6e039943c0c4400e000894000900c0c800c54004d03c05402901e81980368035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 319112248 1250 319110998 319111007
    0x30a060c020d0f020d12240e06031c020d030203061f0807180803040905090a1407080c0105090f09090309041508060709050306070c1a01140301050f0112081b0706 71
    0x1c002a010a14106100f64881d00200d00311500c0360b00c03940e40d03000c0303541d60b035454100410103420060901c819088280340c8100720301c044003010b01240540c1d0304c3d03607150203c105031809444003c0d12050000082054450680010742404c101c2014100584c40742e84100c0840c400b9001108081d41c8070058085000d6003a402c5008680940041d50b070314005101801204040100680704d42c60041c0d00070001005904500e070321554001100000343c41450b54140c4403c1c502920100c0818216004182c040000c00300401807200c507170360282410f81c140704c001d000098031010000c3c03000c0d00407041c010000780d0f4907a041c012103104032b0700200100300c0c0c1c034601240d441c1020100d01070f6240520404020907c014090b82c1c2200441d40014028081036a540c0f2046500c910001c2d0215101404641e4210100d814115800c3c0a000a034100c000f9030f1061074100742c01c3d01d03000341800300461444001400318a540c110045400c03504502455510725000601d90302c04c06843c24842c2071409910008110075510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 319113498 1250 319112248 319112263
    0x806180a0b010306080105070f0c080c0604051b040902060313031e09030b0906010321030b06040314060f1b0a02030903030c0105010305070906150f0e04090b0a29060702030a060c02 79
    0x3e99041141c2c94480c200c5034200c070000e49040001c51140c41d16821564803c40c0d060305858490302c030b00c2e800c20807007000451801c01c0c00e4804031220f403c01507132040303480428000700a10a80440b42406040b25a0300412428800a080004003040c8010f02400341030140102210301c005000d9039451042c80b54400502c0003000d4001182c9100408022a03150704d03000130030a0690f034000031700034181a000e0100003224003070384d1014070505850303100c04012540c03540c2c0900000d50080000041000602d283c0c80c0c10f01500600c0603114000314010311828188841c16803291950480010369600d000300400e0303155004120141e64984400605800080010f40216040724864001c455540352601a4002a03904d51301415150550340211418840e106440a10504040d81441036060151002150591b03554030030a27601605010140088094184226007800c030019050b04140075940c000c1e074450010701e038400c1d4803e0b80c0200d0b44809554082c00441e4070300d17601070b030704021032961120043d494100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 319114748 1250 319113498 319113521
    0x31b0519020105060306064e030703020c01080702072706120537060510060302130b070c0506121b0405011704241b050f04060806180a 59
    0x104540d004550050103014011000200a803032140c1d9001c083c44840e9803110380c0f401d904815107040304684e503d80c03040007404441541d20305a90f80113030740805a400c08400c02d4560f10360300400c02800820360204104814020900e404141c1c0c0d120360b48101d02d406560380142d4904003c039a070401025040b451408a40d000c015004e0008503600c1e003c640d00041242c6024106811032a10109100104500780320740b288213448484620480c140140046030344088121000e55643c424090780383c1250415200a28107490b05505e440d045141d440740f2840107110f004d000309000b29010040182154024010300030180200c0d445003041a09200888026500300101003011480ca04104541100b1141621410384403100c010f843d9813000380d4810380c0103200341c80e18442c49140c1443c60007030303503141203090385455000f203034125441140c201c40110312a000f6003440f504000c52108000c03600151021076106e410076900c10741e1005c000c100840380e00f4100b4640001400100710220815a012a14081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 319115998 1250 319114748 319114777
    0xb09030d030216080a09030f060c1d0d0605130813031b03020f220e011a1009050616020301050103060501030b06101e0909091415071e031b05 62
    0xa0000310181d0807031088640910381c425112481d9800b0400180042c0500c1445142c080b0006550f40c07503c1140c2c0307403254400c40b20035458584120310594092500d031048a800426202070030300034000a400390030240401804961036400060360611031948020003585c1240c4c103640c5e1907094030040f006202c0c01d8041200c480b203001c2c5070081d800f0385000c0c2000540b0f601406002c3c5c41c101100c1002507d50301c3c6016130030421012011000d0710b80d541d00a0602d540e1080c40007060760b2a0300400d0245000ca55961240101c0000b4503000301e50754040e01e44012201d0545041342d44010a01103154981d0348404069015030034880008100283c3c2c2d80124100da008040d58429a282d080c200090b0603900101c01c000a0031000103100f0307440001c0e0200200078898182050515952000141030300c900761030076a4216600750f04042201e40134080380311000c891036802025482d000318050300d2032036034003c1c13280e40c43d0360907900d0400c0d1030080c0d0000d40001c0d480001680708016480000327103280e000c18a080800f1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 319117248 1250 319115998 319116013
    0x305100e0312040516080706170f0f091915062108090d0c2306070c0b030a110c060603011107110402030a09080a030203070206060a03021c17040b0903 66
    0x145205030a001000a0003441c6030028459829261000c0900181e0b00d5006041003600908100000d440040002c8805012018038180014044d504004150504003005408201d120545c503034801c0c3d8840304200500407e03490320102c2e0344c50401040c149011000704247c2c91000d1010910f0780007076800941e4818449241c0381c4491040000c0f42c070b40401d51619481c1c15600000c6d001c0b8020700b5a002c0b02804003000700d0181c1e2a211091249680200088007000110b222001000810150070060551f1041e2414403581e4030b8000391703040c42c8a540440c500110101b0400b01c103d4004041c02d059a04030310b03894a1003030b01740c3c6032101c5041c1d174603610961030421140316007980a002d95641940042615856024241c14440039510044c041e858040d078640c01600014140c0000c0c101200842c0d50050b180d1801501c068544600a4541880f501850404000681d070b90364501c000c0344680c5440700305110642c50285409482003038074a003080408070b0040b90070032046026000c91101181180c030308 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 319118498 1250 319117248 319117273
    0x2303131a090102030a0e030f070e0916030819032318060709050105030901020c12070308060402030c03070e0414150a174204060c020c030d0f03060305030a020102040305 74
    0xd5208441403540036800501603a0f282601944181248120150541d118050242d0304a0b041560b2074001c09440400d58051100b0000100120919000404000e800d018115114000540500c030884100305000c008c40780c040c18400d03003000c1d001c070030b00011060459a164440b00301c40c48040b6240e21342c0c141e0350146595000400184a8096070141d1904103105043c0340c01182d01d640000c00c8164070b99020800d00071969010058660000b070a40d4185855407421303c2c0041410101412a9208a006000344151281030508803500711000c1c0c20030319910942d1102080141c1803091128460b85d103c0d1040108140c148000501e101d5001c40b40541140d465082c41801c01158508003452a44481380d05240c00341c08400b02200000d0041060440b08200420840040c082d240c1030070010401c40c05010030094103001d8462004030b02c3c000b0f4111112104086580c1e1280c2810341c1023004425000504040e02a03800301018513003000659613500b0480f14007034040d5005210898051041e900140f50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 319119748 1250 319118498 319118549
    0x2070b130201081618030b0106090b0733060602010608010b0102071422060f06110d0c06051e04080702011b083004060b0901090b010c230313 62
    0x264140d05868200c00c584918440c42c404018044c1c0340000d02001c564801e5408924509a01c015403017500c00502541c1481d400900280c01580401d2008206102603030000c1c8001808841c185181c2c40304051000c4004190700b004690300341c2c404a020310b418404500e5581c19000141039070740703150080c84119841801240c1d540c01500c510080c1c01703041e1001c80303001d01d0311314611074213008180c8520b4844843c04a0000441d01c0c50342c03082c03454802c0c16008120b4190490324494410407458041d010740c2004003000340104020301c40060100f50760341d000480d0482050301c0d8449902010003040e2442c03400f40381c4441d9640c00354a0681c0495900c8917007602241040202c1c0801c41e511441c40c9050003418861102118141050648603c000280281380140b00f914020b11460050a0118105604006000841743d0603001070751078a08000181000345d0300041c248242030743c0011400300950000980d8008404120140d501901000030007200c0302c0c0b841c00d55a416500005001402e61090034071041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 319120998 1250 319119748 319119781
    0x41221141f0803090409020f1305040213111b010f06090902210d050901020c120d080c0306060a0507080708071a0106081608090c060c03040303030b0901050a1203020a0b0a02070b 78
    0x110b450348200304107039482c10b0a41040c084280302600b030b00400342d116400030b034410844c0050351440d0b41c1c3d10810031003036181691095061a03000902040318206c4000824507512652013446901013840e50003244c0e901007584180c440003042e480c06c00085859a00503005446040c4c42039100d1841038a845a080314612003929803164004001c103040712502409407040e4004551203070640c080c1c2c032035416042e00c0d10101d19400024180c0680101186903001502c1101c0140c8140e084174024020440c032a19900101c078061205410501e4841025140104091040c441700612501022603040d0800003020918082c800046400b09030b940c2c1c9403c1b0848546600700d421000b000c40c50000044800d002c1d1000a0304240700000380e0b84c00710303040c00110b845640000400c069a500c001400c10505506100788041440c00f1105002e80e54506800a141c02d00640240c0b0750440401c40070b803003090f0081052600d4a13074080c881d84900e207001071002c4000d4010340415a0400790800001d160b43e02089101c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 319122248 1250 319120998 319121009
    0x308042406140a05180406020705070b0919031205091201060e07020d0201110906090f1f0905030c03060f0705190207030209010e06280305120403030314041221141f 72
    0x200c02c0061005c4d513880361140150080c3c580300c0d0300b00114000b1500a110403405081e60303209260355001040180600007101640c00ca03110b43da000001d00c0010040201144070700300500d0840d4071100c4500c0081d0040d15480b164590641c40d04d000000c28460703031400588160340305d40a0b1400880601d906074240e40d5070010b1002440c0003049038445519004014015401010f08001050b6019402155940c0903221034100224a0181c02c1000e60f03a21101c410040c01080d030141c11030040e4a0042607403180c0281504a80d00a002c2c0000c41c150320030f8095411030241031040134400c40b0026006925145a80030590140c14558000b084481241050070301410b8054210062042503408040154540030004000410380c61400000309004210791101c10011a000c2940ca0b8a5442d01404031110010000a1601e1010410010032003000ca0854454558100545202c80b40840300b203080407200d402c07003007203403410302d590749076554441180d0302c04d074a08a200c5800001c003582c02c0c2803101e642d01c41c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 319123498 1250 319122248 319122259
    0x40c05090a090204020a090905010f03170c0102130b120f070203070f030207080a230d020a030507170a1808010216030e060f3f01030308042406140a05 66
    0x200018140040400e6008802110004110341181d0001e016640540103000004135007841c1489014524803595005000a01c6070703552440c9560b440c90b80d00087c0251251070a1008540c40c501d104080d01100c10b00025440303000c00d202d40756101e014042c2c0080c0040c3c0c0c1551010070002d0010455030070311a01816040d0001d50400d1030310f03a282d950321001c008003201180908180040d00000411450b4940c2c1e1254000101c1040034a05040d0b0071480602c00722802e07030010100750700090700410100e203901e408d442e21654543c0b0714200401c030145a00900f024241001130300c034699030b9000c0d0890725020404038420030100e54a000031030030303405508600c0d0840401c00301010f0010b40034503007106400320301900c05070500c030050940610316046400078270400036076829540c80b200501a20a8511071805004007547c5140342000c803900c4d101400003e0501003071101080038055056401d2030551960300c814404109607030781c4100544411311483c12210080c010340f9a461a1800e80d443c15070708042c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 319124748 1250 319123498 319123523
    0xa0807091202060a090f091a0a031a0912030a0b040c0e090601270914010f0e010b07020d02090a0b01020d02030913050712020a0306030213091101050c1e2404 69
    0x3005415030240813080c050085401c2c000034007510241407403004012842d0b00007071030702c0d280391050310881d04806501d12035214030000b4000104640ba00c0d0314201017041100300242d0381d4083c018030305140c041d4081c01d000004800c210310380000d07421464013440c05441c244541044810161034400c0c640c15855031004403200012155446000c4041c0c9000958088542e840c8059614984548250f041080ca02d5103400140b0070b80300441072810300400885c10080c95030713890150110400c9206018111031444002111029599442d024620144c0c0040c0102c2c4641003140300c03600181203e40130700740507000d0703034641f0404107001005442c0d4400003e02156006500c6950703070802414000d18100c28800510130501c0144902c0c0301815048640e503c00280319030550041103003c494012840d64030504000305040042c1e00100d6a066840003800c00b9038440d0b0701c00141a00388420f40c501500a43d00750044107062880000c4c010244001400b407942404001411914035000d049401915000c1c4054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 319125998 1250 319124748 319124753
    0x170609060f0135010e090a030e1f03060f060201020c06040b0703090f0501020d060f0b090904060216060615020c0a0e0903040e01080d0207080d1403040213060305030a08070912 77
    0x2010500c08505241c0702580411032203d4110120240c48440d01000000d000f82c0c665000c4041118090901c0d40b1441105182c0480640e03592001e80c90b0042c01c102502c01d40c682e19489407141e002480a20b201c40725403482e454080140140924807505008440c80d820000e9100d0040c421116200700d001d01070142e40c0e031662500b007018900503040c1810180d4841405c0042100d5241a0b85040c0c401e50002d680c81440900c10420740d006a003010b0394088481c1810005512980125080c00c01c0c1629914031030740c0d4034180703440240142450120507038403101c8008200b090562205064800c0b107442c0c002e44000450742280d41e0000064416044503c00e4024000c1322072210f50301c8d60003d004400c40b840c203502e47e698090030702d2082e0301400c070b2a40011845411a80c040c8001e03006003004c24000d2401005081005114003100b000203001803030004007040030b54a44031101614151041c0d01401225528540f4503626804110240000741e550310105207102d201d009101300b2550270f00251001c82d107554 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 319127248 1250 319125998 319126009
    0x13060c020a0902030106120b100816140316080c0301030201050702061e070f0624090b06090a030f05060a02030408070602090303070f061d0a05100506120a1217060906 73
    0x980003030780d119011080006141140780015800b0306865a2003ea4404019089006844940b0802072248030850920f4956903031100c10180e2090b03035400203140c04105a4016502c068070305035034042007600002002015080b00c1e01c1c1d0503c1c03507419611285583d80e080b40300c140e01c0c0000e02000b400603a0412a200140c54108040c060354407a11001c0d604d0001c1c01c4800d0007056020907802c490ce00e840301c4a68082c01040d100e007a401142102d00e41c140c0360200044086040300714026100142d558212100c01500c4040645503095000b408020079903031207082004000350010800c446600c02c21b07000814510450090328046c0381d002c00c9250606901c0d59505000c1c1d04017450840d0144024008078012900003c400b4958038042c0000058511421301c041d05030a1803103501e00800d6005c80c079050f00003a00064650603000c0902000075658980c0c0c00040c1c00343c91040c8050826100340c40502090008003001d10b1105591358807036580c0c0b601090f4003800e00e00c208442e80c1340d116000600140450905 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 319128498 1250 319127248 319127267
    0xc15040510050a05120a0f0f0e060402060d0603140a0606120c031205091309110303090f0f030c06071401050a0c1e0302190804060c050c06040f020312040e09010c051306 74
    0x5003810b80c10000c0071742c0ca51031201012900f1015642e110700c0103540300c060501c2074520245000e00241301d4070303011500f019500c440240000740250700000b14883c0b00f104a900040c0910361044800b84248c80d042c9805586a0184100b507c0c4646070000000b012007004641003c51079020403000589803550f20b800940301075a42c208018000200040d0007259503803947d0805101551100080d00c5e49141000c03445100211000c1d07010b980200809101030780d840c0340344211410211910500c0007044000300b802d00341c199401a4101c1404102d40701000078140701440d254100200811095071520100c80690344092015004603118044490134190341903404c11102250b400c002d032070b082000b40200340c1c03081c1c2e401080380001c00100c14417007003140351b0103001104c203503c0c0b42c01414044500b6403a5107410010700b00a02071002104500d0841d1800d1001c4000d10141a0303009849a90380c203a0200700140c100d0301485554a401c0d21861044c2c028010b0b14003080841640d904c0450400000360b0700d8008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 319129748 1250 319128498 319128517
    0x30a03120e0120070b0a060b070209150627090105090406020307020a05121c09080a0503180102030f0402190308031b0708071119030b0c070813080c1504051005 70
    0x101c5101400945803c0e4800d014110081103c0664452079800e1500007500701400d080c200e030b41803003010008041c1c03150a440390990110b40d1f40826484441405000019100c107142c1c008401082c8405d1901c01c01c2c4100092100c1040310301e001014000403c4801142405159441042c0c100407030041015036020315800403150044501e007030710039200e00d0b2a1407591203d03a030317101c040020715034001600c03421410295540c5090174480c8482c0340d0344651860240c0d0162108012010000545a6407085650002178010078002c55413402c2a044035800c4c040100c4050f8069000303080d12162844000754540c0c1184c0d0011640c50650700c0380d546140c2d08840c0300d9014a0360328810700081010682620081070960310410320049101d0600c000d002007528030b80790032030030f62030386400c204041f481d0050141d52040b006002559a80d00a02d03206c00b03140100d0300c041d03056000e89a80031841c01170004404140c100102ea00b01103400c080e111040451045000701508608129180c1c00024082c40281421a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 319130998 1250 319129748 319129751
    0x1050901080613061a09010b130504021c090c0f03120801080a0b0103030e010c0c09150f030b07030903031e140c1e030702031b1f0b090f04080d090f11030a03120e01 72
    0x4080d05c00191317a45820381000640c08400581003a00082c1d00a01000818040d202503040c400c021503000820740d4040c01462145803698000e504000d40c1030494001b91030700300050f0040310344a052428880000c601c05401188100001045c45d101c0014158616a80103c15114a03802c580c2c0841d00c090100783c103903040c000603008010010705000c4240000d40462880010f0021181c01d00b00c001c204c0c03581c860f0108440b2440184049102144c60660040817805d01041403107452078200c0c003c1c40400d000c02d410b822000c00c1080d003a000d83c0c2100c52440c07111440c0c030703106844030200518244510340c09201180c41c20340c1103420300f1208a0185622400310b00503281042c404034000003e807555038055018540000130f83c003003001328052829245000050081002440c140045416501e000c1d05490b00004054001810800340ea130858201080000c2c060081c2d003180d140260042c8600c00d07045854003c058481c40c01c500b07000680a20491701903948101d00b0000d01000d9004007280b00079480c0d00e5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 319132248 1250 319130998 319131041
    0x31a190e030f0a050c0105010f0b0a05030c04030606030819110729120f071d01030e10180b0108010504050309090903091e10030b090c0a0201180b0105090108061306 72
    0x202c44034030203850402c0302512103503a00c90000402c03500b1244145c000b0f1907070008003282841190f001c102610144003181c14002d64a8035884245c056038019a40000e1500f814210080100300a1601030002c40410b2480d02c104404a454261402002c911168034141c1c0160002c108c5014640c8001c001400301c1300d800c400100500e403000a4940c0410b87c00a2540c00c0c003c00d10581e000360541f60365015056250010b0b40080c0d592414202c042142c7c1d00904060f00e07880b542c0d0b1201030510141090306841a020002c24000040031001002703441800e84802d10b2a07000090241740600a052149601101551500312000200b1641d200c0260001c44a4841880800c0060301c4081c2c0b90104007111101b900d0030415040300300320540c0c038040c41070020036003400000c0b081ea407078030900c03a900402001340c02e40d212031840c4012401420b82580011210800000c0309c41400402450789050320070030f860540260381c0704d1480507500e030026104120a000506490313030104042d070b0311100400c546500009400e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 319133498 1250 319132248 319132267
    0xc060b040908070312090201020c04051e0106110f0c03120f040803030a06090506040b0108040201080a0207060f020d0c0c030f0c020d060e10061202280b040f031a190e03 74
    0x44030340d0107400700d5106400054000505400940802501c40c044030244002c00480c6d0000f5117406031100160701841d1100042031003480729071520071001c251600341c00340541c1e48900090494440788440301c0d50b030054081c85135165a01281000800b9030140c0149010004243d0a2009500010f4106040c2000344000325800006000440c056003015401040d20340c00d040e10601210409040144114945000500c0590700103140992054090804100a5039801c401402a100704600206010300d03003c030710340b034140c10707a4060030300d01d0901e2004100c4526846000d680c1c800204c0c1004c1c002c100f440b25000003580c07246000e00d110603c083e01c000c16148987c1d4604003910004d05900c29607030015290740240d0016846080d0090400a159290002154002c100740d04010a00c1c8000815000c829074810004100180020316201100341e40e502d9035242c20200d038515901048503041030001c40542041e1a4142d414060050004ad00b017100d425645100001c0081d03403040342c414081444040071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 319134748 1250 319133498 319133501
    0xa14011e0b0c3904022503050d020d1d0706120209030c040603080304060b06190509030307050a030503041a070503130309080d09050a05030f0c0d240204060305060a060f0c060b04 78
    0x3200c60504001c140d10f000700d901d4514550103014031290049105000b07000b2003019070f24580707454205207040500346d210320b13060881c0c03540309260a0b0180c00b40001a0703507002e00c6069000c1a0400071440b01d04417842501002d15403910428440c00740000d15403412041c0d1105d11303500528a00301e006040390310082c01c0c0380114003926030f5940f050711108000303c200402c1c082e85015041d02394104036001072030404803030903410398441400105002c0180c042100206510100b081b030300703665046070803034462207118500104654000c841c1180d48003d8010f107401c14869889029000d0440b03615002d0a40e91100d04401482c0403442069081159514000404030028480d00300449581d5558411942c00c01091008196240e84801d01941c0000820f02c02181301203008003e140e0102c82112210040d800d0000e01d43d036880902c400300d003090fa1a04503010006a00500c11658142c0f41402641c0d2a80b040014800c0c3e24400c00c0045040e80b1000301440348030380c0481da089403180d1000244005810040390 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 319135998 1250 319134748 319134793
    0x31e0204050a0e010b01030605030d0507030909050c07031403010608070e21030306150f07060207080408030a030212060d03090303030e0f012c060103080d09020f0303030a14011e0b0c 80
    0x100300b83d901d40c002060034000f8012400414804e00381440410315100100342e03154407055404007046804200c900403d40f00d00c2c2c2d20002401d0302e00c3d061015091010145a0072703800141c040b00498524038014003a84810000c0d24101c41d40e85d00e5140059807110301c103407440308402500c55882031451040c0c51043c4900001d0301d80300040003000f56140e00d0400706100007819444020b813010300003480848a0343c50304200711a21281c5c040c0002d600d0b5201072030162404c0c060b0360010f0755075002c081180c5800552560143c0b504d4030300c00003400101c2c3c0b034170410300141508041e405070001e200c1d10402d1011034029003000f611040c1140480b03a000382d1a003a0305086410317080c0e603807040f2446030308458580107031400c00070074000074800600440d51650352800510712680342c0c01100551546c49040070356484140343c1034944000350075680c0c4c910706480d05100910841c440c40741d030101c2c0c0e0780c0003140010729a1080560700d00d050540d01d09641c2499001d400b2900240f0101230980b2440b2480c1c4092200d040f07802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 319137248 1250 319135998 319136011
    0x11508041e060e2a060904061d33040b03190803040b07090e07110109020a09090611040b220803071a0f0705040b070204091707050c19031e020405 64
    0x3d1101001d030515082100c8141c0141c50002e2400d11100d4542c29911a2040c02908441c01c503034880c800d00100d40075008940c8110030900451101d17603040080c20090034829084e440c4410407241c09c00c0e4003051201c103041c2c600c416240032140680c0032410305500401c132032040101141e48043e00c80c0411100c0c13581e0800e04561104000c82400200030f02070404a40150f05414898001410081014200d600040101c030400c18a500070340545002903110703802894004d0102004203440b00b0310b0310080d041104003220181e141c0092400ca802e050020345041d0b410303200d4031030720f81070030f42c2e151115040134114101c41e103044009000803032003c1040100701c1680b28240112107190404825a8102001001d51160126a400300071010b64080300f140c05680d074001c000c03a120142400890000c10003c00e00412141c80098030750000102c4401520105215800f02c1c0c60403c10382d814402c032402d0b900300160621480c1101400080e80c91140804084400044040c1c81d82d82500000c0c01d54a055449 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 319138498 1250 319137248 319137251
    0x4050711060a0e060f07030e03030f06010e040920040b09010608040507080a02060712030f06081c0e0d06380108010b19081503010e0304060e09011508041e06 69
    0x204010030502066901c6001040b00b081a004440c000c6500c544008040050310036101c000103c119010380e00c43c640f401d00200c1200d440e460300859200381c0e00d1043e01c8550106950b0703003440a00e171030a8050101da081c0d125003a101d1182c1004030309003411103542c0002c0c0d4000e4a0390307103140c031a03200c80d58424001c0005949a00c0681002d0402600b410b45a030002141c58102d4032103039000da00d40404840b8004d6100301582188811403e0480c0280113a0220700031050034520006480d0200094000c4521500744028009003e0f080041c3ca807448503410050b000408072200b6404608030380d000030001f00400d00d40400c1d00d0810054106915a1041c189a40c0c1000d031035036412950b48045a035024004945860b8034150400f502229900d154155040c00c0064010004206c6040ca81e90a400144050000c4c07065a2036184c04c0c40d00d07500310b40118000605180d04500b214544038800504031251650149244045030070201c4082070014401d403013001b17094084040c2e4030341940610890b0344c0108070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 319139748 1250 319138498 319138517
    0x112d19080702012304030b04061407020601170708100f021306050d060501080402010c020d1b12061802100c05070521120903072312030408071a0910030b040507 70
    0x50321004500081301076200101541c90034201d52402240c05581c0c00c2917410906a0700d510307040015003106211800100b2178541813150380c0c0c0e00000d0f400c0c1a2603a400c40d0034440380d0301c00155641c0304d0151140e462254402e80a6640c1e10006038030042010740a00b80143c42e00c049910b1b004400769032903220900040300040d01002e440218422100546400d10f003c034000c0c00c0a030002880d4000444010348a91035180002041040503548481c1c1c040e400b0040c400107507920a44031008480029060701e07101e040c0354030090030a502d018801c1040e030380100498408a072010341120703400d0a00c07a003100c8520404402183c070361380f0007059540d01c800e5580d680310309000f060002420106884024050800f0620001d2940d981c0032070982c041d03030f0590000d404110745944100003e25a013440d0940c00046426126071024008801081a12000012a0042c03550b900101000c2d101c2c816400c10600303800e100c043c6203407800420080c100101c520300460300d05207182c0003074100d400c19242c14021031003011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 319140998 1250 319139748 319139753
    0xf0f030507050114090910030c09140f22080f27010311041404020f0703020d0f23030603010e010617210a0804021816112d190807 57
    0x88101e020308420b00c0c03c0132201201413041801c601031241010302c200c04020004100c1c2d480450030000645d007000303403800807d554880ca0001801002c02d8000903040b03190005000b11284049180100100b5a10000a51013044036801107500e03407400b181e01d410b01f0441410a800e0301d4000d070248015540081d0140860491168110800900d10724140340c1404044130700e0860000a8030100c0f4005407100702d01d4507083c00090024820251904a08040850307480241a40082e2000d9082d841d500c8280aa05c6294025259801605030500c1d181007c0042000083c0260000d5500a1005000813500e484040256070954036149c1211208443c9554503001c0b5810030002e8602c1818548100381003500600f105044510544003401d0521080d00003050441d102d40c62030b402e018042500351070050030074103403e007141c1018140302c00020f0000b00d0346001003200420006450448003050b4120070203060b03060345400400035003031449400f07410304040c240600443c5d01d4003103510801314507503650b9091 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 319142248 1250 319140998 319141003
    0x405040213050f0a23011512090f020301060b03010e070c020a080a0506070e010c0201050f0315090a06081506030d08041104020705060115050a3c0e030c1e0108040203070f0f0305 78
    0x4600902c030105e41d5500302a15079415034901410740d400080403848801c4451802d079141107244984c3d026061801858a0501c03881114907c40346208030000d0024035527a48400c1c0c1280028002c403610b0450b0340b404103200e07502a03404600d40b184040c0811080d1952100329508000c2d9500f016601c4d50000400c00c5505548001c40d21080b8a003400c04445018203a00000c0044c001c080c035440c404107000001c201c100c1010010a100801c0c010b020f01c0c0c9502c5c10412003005000e862003564070a10071000030004032028440d40d203104200203030080541c480940811504034001500544920b030705104002c0c3c85403500c0c00144081802440104013551609100010400c84098001d04000c4240710006d000ca5000e900b100c07050049070481035805031a150a6415024030201c103240810420101c2c59030320b034100e80c00c001c601d60118151804081064140a243c1403204200704000802200d02d01481d07014105041d04503001404885640b0349584071a41c6210321608031900e141c210355410020007108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 319143498 1250 319142248 319142261
    0x403020c1002070b16140a050d020d0206010501170402040f1b021203010b03010611070f060e01030b150306010c05151e011e0501030b0d052d01020c0703020405040213050f0a 76
    0x4510041100c0c42c50720301030242d64020300740810030b0b1201000268003481b03401d0354888401036000003902c001914903d0981e40c2c031207010101c2001344c0142900041050b0010031118102d40060b12045034001c0c046070302005001c0020000ca030b00c683d0781c80d00540f00140b43e114082c41c01c81c502001180514582c00003a10380910694504501182000107001207502c4000b07490464001d820305841419143c2c249a060100c590025a050030f01858000703441a44016903080215080c1c804001420405040c07205d80d0804800081c50740c0c0d020000308007a54865000003410602540a861004000110700981040f050758405652011900c0c0c0700c40032102501c1940c010032020700100103038001d07040b40100004080c42a28180b41e80ca04158281d610b60030f00a402ca02d40c0b0109444140c0b0394a04180325032060b000b20030382da0540d240e031000381d00700c0d05108582a1801050041c48561318550801c000f810b0001c0040360081c41c1503000c812071610a00629008113002e003c400c00e03074a007900518085401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 319144748 1250 319143498 319143529
    0x50306040b1e0f030a05030d06090506030118030807050409090b04051207050721080307080108060705130302090a0204030b09010207030e010827011b05031005040902091f030b0403020c 81
    0x251a810814092032501110440308043c2c42c800f00000941000030708101605c0300c064028040020b0741e00307103066664800c00c2902e8545508111a885800c203240c02c03030303000c80e041000c101d070034803400c1c0c0c0828011190980d00c03400928115140549541408060341e6103450300700e6010750030800384000c01000b030102240074400030854904000380c03030b15200e94600c51840f07055000c111440300c0c04602c092071190450301c9900091059a2800c01d913800412914013441220518015040402c0c40380e44180200c8400d0f40440c92000b0405085808004e20307407030003400380c0814079420030001000a00d2451143c0c4503440c05030005844400324103018204125400106040184250400c000c000c0c6200501400072580c0c00081b60034145400f8030345c010920580101b001c2551810040016548100150b1190000901c0030020315543c070140005d60b002c1c070500a42c030000b290009084005030204060a0040d1450b0b100704040c1e403610746207224a0b044d82c090f00107070030041070410340d402c3c40c4005060651 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 319145998 1250 319144748 319144759
    0xe07090f020d110a091a0415020f0708060112060b0d0c0303050a081f1203030b0618010905040504080a05030a15030303050717060303092205150a080d02060a0b031c050306040b 77
    0x2403004c14001c2c0f04030060700501c2040121031041084041080c4107550142080c20700c2c204690642c520060b59881400c0084021442170002c0800c1d004400719846040b1680c5400e608401011644c3c1e03403001e001c0b036240c400d420a09240341e0201145401c0c5000c00250702030380707502c1c0e84d400418500801e20303440140154005220741d0940d001d0147e400003014121240124880300c000032910702100900f448542c169440800450310503000c1224009180100e03000742c0b5010340441e9903800388410b4038812070380540700c40410b000030610580600000c50307004164017800100340304a011404140006504184c0001e0f659900f00040150801d692094121090b0801086450900d00095880c81a41e10040c0280d030400c1d0308000320150480320001d444084c100601080c1b52000301c10100e4203083c0140340c802c52500d02e001a8001300428200e9246038540d0181c03003139690310341c03940b005070640741e1880360184202c6580081964140c0a0051442116a245556420604100015281100100e034070030f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 319147248 1250 319145998 319146007
    0xf0d080a091503060f05010e0f040f0b030d0c020d350a120905060606130803030406020d2405100c060515121209090406060803040b071e050309040e07090f020d11 71
    0x6a5043c5d050413181d09103040140e8000c00c6002c24901400078000e55006401e0101c4c007241401d06820001d04d0600503402c40381c25650008007220a88801c41c40a5000280010a940406c40b052071400c2100d01c01c2d0b110a05203c0c41071340c40c180843c81c64120b000c0c0c40201281070440140d0040e0900c1e000c0050340c0e014011421983c8a0f143c0300d041c090599480f0300c3c0f0010301c0c400b40d00c00490886006144d510180e98403880e050401202a6200c81d0711003240b240342030000c810810300910780342580d000c683c01445102e42800103101c65a91250f0001e014040109800c3d4000b59590040e00d01c0f03109201c1407168074084000c20300080615400d19034072550480054507840d44d0301d01c4180e45209000f10f172504600e456905014005003015000000c580c0400580401c2007443c0c44001e0400d87d101380311444296100800c080b29880c92400018429081003142c82c0e01441c154102c0d2441e10b0710b0b030040d00d10103036940c14810201c441095100c4081c54010400c0780d4610054420307510000c02249006240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 319148498 1250 319147248 319147259
    0x120b1f0303170714040801050f060405041a040201030b0429030607022503020406080604110f01080a051e16032307110106030b040c0509070903110f0d080a09150306 72
    0xd00c0718a0100d851000e00001c003044d108050402e009214a00c507581da03030f611001068040c00003240c1c1d5407000301c010780110300e90b820680b10701841544c20110b500c1d00300305201e4403072051a90282c426410075441301121040c1d40e82d1441035040200d00005411080900c0c200100c0a04100300c1102d48a504a401002080794000c58900b55044041c00c180031039003460440c40407050180c2e00040d41143c0740903404200038400145d080e0180c0e0050b01200341e1210b0f110b080081188207100b0b0540090001004589210355135000b8541182d02041080a422415101403820680844030205030941c1141075440c0950188200701b408902d94603a0020340c1a4002d810300c07101c1000c0d001904000d8a0700071055204800e6000c040507551002ca60009030030103050542a100503405004e00c00c1039070502094440d8040ca03841812a40c0c00000c02048185240410110140f2003020710340000c50003a50100061202c001442c0c605050340b5202c0c605420b05089400f641c680d24120000c0c1442c04205014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 319149748 1250 319148498 319148507
    0xa020306090a0b0f011803060608010e1009020f041109090a060617040c050603040305191d0303120a05060411041233150905070c03030c0207031e0606120b1f0303 71
    0xd010070282801e00260380c0c546c2c3c0180d40c199890f400034062a2502a0110340c2600641081908805030000c41d50110800c00081007203400b1448020b40c0034140c220150014100303a003000f0750044001a1090a00d045d020114200110403203005840c0c99a503541070003103e81000100c1d43c240012a22103d041c035040d642d941c0c1c1c428050040c90321131007003c000a070806d8800e00868007030301d01c00803201103015001d110240c00d5040500c00c00561140c02150020142800801d07100c02a0034101d880f0580d440d044080d100900e8040c0086400a03124000d080c1401c04410007040207001d00c1130004512101401d080b072040c0c40119150441d041a0505840c940300100720423210003002d440e000030b400440500045030315031030398486050036041000700420540c12108840c8444e029850074000f5a060010480e1a40f0070b0703020040c030307031b400500c428054610807a842d111030a100364400982c468580c482d1080c071101100c8211b48224100c000c002e803040514007260f031480c1170714807017180071400d50340c1c040e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 319150998 1250 319149748 319149769
    0x130e1005060d02030c070206070b060f090408220807061701090203040c18090c1401030c030612061104030203031204051614010831050c0a03170a05070b0a020306090a0b 74
    0x21000f038000c07010a400d000900700f102d039019030003062660b5644451a040790095000c4078503500c40c01e90141824140e0404081241c810796100c03c1c84c514140b2a80920100742543c41d44224074030102c1100400c1c612410001d040181c00207072541d0704402200c00000f020400141c101c056500d0060040c400021509032980003659036034071155109840b04001c160007012440c00c0a0b010081c0c5040005022032883c6c034040c0029401e98043c00010b0100c001601500d0a51003002c6164000c0e044241c003050760355001c204042c0b0444003003450681da903000246513030000754528040780313001c1003271100f00b05080003c009900700000056200391b02d40040300e48405d00c402c0380e281c10300105900003403c02c447c4070198001541e015041c41540356101d17000038061018010708690901ca4100310311154680703100c02404499103c05111210100d40904091540000c54240140300040c0700b6480091010b4040610a030500c900041e128540f000400603c0000a007100710075600e404244295525100c0c0c2d001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 319152248 1250 319150998 319151017
    0x207050a08180301020f0c0f0703232a1207050105070f060b030d050a02010c090f0501140d0e1f09020a03080c0304030f080a0f02070e1504020d02130e100506 69
    0x75a1038914a158116845450100b41036155200140d034031841c0b20035001810600c040f240848400940358000640d5544013400044e00142940c9003c044900041e09400042c3c0c1c841744c20b07550f21b440d4018004050007440a10b04854410404503042a81070801040e10740401c1d28000f082000d00e040d001800c1c41c4a090302c00b40c450302e0011440b10600c400303070b040703001c1484010381103911503105040700400541108100301d0041d400e05519103c804c0c031654541094038155850300c0c0d00c89240100546443c002c0450601d0001c006005148513071906125101810644030090845038802985500c0041800102e402102e441d250045000d6224032200c0c4060302d0b80009420b541c3d078000f100c068035502595200414428448882c9401c00100c10098000d80354a6240c10302c600900790700a0745c541d02e8174003440940e940d03800700103100e031070800006503000c4801070801450308009245840c00da030b01c800415980c2480c0d04504212b500c401820300d0f607210300450b98246480e401c15002941138400c20600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 319153498 1250 319152248 319152263
    0x20d0203030c03060d02040b061801031112010b0706090210020619050903031602030426010507030605030303040f0609120c031215030314090a0e04060c030b0f0103050702160609050906040207050a 86
    0x210b07000c6441d607030712407060200e00030074840e0ac40c40c4103031440b0305e4864941d401c280060300703041c0c0b040c0c0815030003c181c5850721000e9542c1091a030800c0e074191036036045072a05842490312285c03406c0160301e6022400c1118a0340e42d014003420b10f880000c50005000e04445003039105d00d004200000c180c004001d894010803810f035118600039aa141c02c0740307103000380c2d003040c1014501c1c100010031400c071a6409404c8440c1c420024005540c810405a044500c1849003a0b0103400400c006000034901c0b400c80703141d481c42800c001880400a8030b43e844041034064040000ca0000246801415005041c0e0440f0b110342c424140019100c04585610001c1039200c014180030150f0412070780b0314020400d40e248088050b0a42c13800310313034481c00039068000a0b5030681e800c52070300f01408401c0b0b100c0d00500d40c80b440040c01c44c14020a031100114000c01e4010b21040850213038240c11030a07007082c01075075001820995251205c240c1010104a11a0406040c0c0c611984c81008120001040484d1200623a03401250 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 319154748 1250 319153498 319153519
    0x3030f090703021e01021c05040311090411090c2b14060105161e0c0501080c070305160302211902060103150b01091d19140a0f0905030c0c01020d0203030c0306 70
    0x507490801703007c40c4900490750302025844420781c41406001100e0040c40881c05440401c001d000404100352006010911605100c000714103081c405c0d00c1d000b162400080e4500b40904448180700754a04180040085d007400051803248510700828092003240c1201c100e00d0301781000060100d00c02e03420581c0d14005034914444c01d00c01240358003160385213a884c1c2003520700c860346071101c0e42140d640100c0c1e004c1441800440d11140d0f40d00280c85109925032601c91421642102c401401e002c150001c40452251001c0b109105c0120055401c2d840204c4074016150300003010308440f4050200300c0c003c110744c081030040011072514190b981c0ca140980d800086c49200100c01290a079201d600141080740004240c00402c24000c2c1b1035501c035866242d86134151210080c0a0b00544004034100303000040c1d9480803d12080003540700700c400c0c18503d0000a0b4480c1c1c2d5a0303030136040d03810000d50601290070a00d9100f000303580500c4006401c54640c03000d5890b628203005401c0f5a40000f400e40c4e07014045405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 319155998 1250 319154748 319154809
    0xf0702030c071205011d0c191509030507120201080c0a17010326160b090705040e0606040f020a1b0c120b180c0d081e04030503030f09070302 62
    0x100300c07481d600408040e01c500580354607040c4140c0300080412581d075071074281a010340d0304a01403075500c5031042c0350152004018840c10001004006c1100c030a41c406600d00026007a5001d21070460b00341c441d0f880d140c81c60b42c5903040060419078507620020300b5010302020100146e07803040260340e101c401e00f0813181d260241002d00300c426603130b2601c422a00c01c2201e00048180042d001041da000d041c8080350982c54501c0e000c82c0401c9010305070301030b00000002c04d86030001500c00c84420754030000100c12260100e50741c1001030f083c1c1d100d142600c212600800141b181e40d00b0140207036591140401d07002c0d441c1008040008100154866440040c02c903000012010000d00f005001c004080030900211161400e00300703242c0140341500e15120042d0108c030802828031011a40000c0310300002d05c49100d0350b00c5901c4105040d8042020303e145117440044440545030000060710243d40500c004580304d00c1d01039414219038070060103004030750713000010030401650303440444124440342110b80311001d800306 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 319157248 1250 319155998 319156003
    0x5030309040e010b12060a06081f0c0e06040b0706200f0a0c080a051b0f07140f04090804080d051903020d0f0516020d080c0a03020309070e0106020601030303050f0f0f0702 75
    0x110742440d4480c2c102d00341714001040c0050300034000d50214100300485683c88074426510880f41031000300c0c40a403590000c0b952062a030100c0404900c5080905406050350300042180d0f000780c0140c042000e01081480c01d000396842040b0b01101307940f04580f0654281d0b01c030750805015192000501c020000744c40c071045032003860700100701540000c5140d01c8540600380036055401801e28007407016000320303c454504400040c1c0718000c001880141c88d905040442e0310544411141c5410340041200d5003507880c3da1541d20883c42214083c51882e5203c2d82415900c3e4104903d044000c010060b06000c0a8030720007500c04801c2103404503060051766080c2d1940d0120141a00741c451500341481c0004001c000d1000d0b110044100d03031150f007503600c0408000e10550303403580b013504e262403524424000208024040d034000e68015921808030342c4481d0b9200d46107040c140b400d030407100050700184010401c00d501402a02d0708000400c2d5080320a103408001c099840c07400500d031903a0340043d880840c0c0494001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 319158498 1250 319157248 319157261
    0x9010305030a030c02151f0e01060806120307030c0b131a04050d0c0302100b01030f090b0a060b0a05091c020604090b01080a0218011211040801140604140114150d1e0605030309040e01 80
    0x2301d0381074405941e55181e018003000c5040f2481d50003044a042c2c0303200080e001004407071002d5131540b16200500040e886114200b00000c14000c9810b04030b1100c140421030340c0720382282e40704c1451006442c520301407820b1400c1600081c110b44c113102040407104006074001c03ca034400c002504100180003003804004030064410040c400581d1403500304900305104a41e13091611807250ba0005000c025031701c3e0b051440520684144d50005141400071301418580305020350b0a881c02c04400ca9a00480b80d0006101035200354000e52501e81d555034290403558000c0b464641c0036000d42d50840c1010403118000760248014042c03907042041045598900510342c1d40300058841c4c1d0741081c1500e07261100300c8103000704082c1140d4041030300d13203000040c0c051405010350700350040c081c40003002a03460603120003031035183c40100680c0310399a2600d401d5005424406410040007007500801d618000700038100c0101240000e4502090401e402071000f0740b0008119007510109440002c1c80500c0c41c008140140013 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 319159748 1250 319158498 319158509
    0x5030109020c011b0e040c0f0c0b06060d0c05040602210711011e1d061810050f03070806092505071410140c0c0a0204091109010305030a030c02151f 65
    0x101c0d09054131640248804000b1100741e80030002c0d100a5601a522441090000030020f000741c003420300001e8203101c1c11500310b080500b500703051840c652048429100d05d407814500091002c2010000240d0411207480c1001c00e40000c16020b80c0040c0000200c2d1083c902d010b8442c4800e0014245627921904c0b0340000400b2a03050b400080c014034200510f10385c0f0705199813846081103800418149406400c80c1d25219101111440b01a000414403100403040030224050050910808800485942c0214071905e905c2e6114000d0380707818000c00c6040c4c0700107480302c81c540d161800c05e10981d854005081840e14064180103444113038a01d000843c00c2da80822100311402a0074112442c50115004a41030b074120034a0240d42d65101d00110f1441c0c00f442d071004030258408403404c405810550b02c29403500c0d004a0021545000c0c20011910114007030340202c819500000b41c2403822507061241c54451003540c0f025182004506001342d4290b24090301040303407400e034540c105615008586050b401010b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 319160998 1250 319159748 319159781
    0xd110d021306061106160c1506030b0a0e1b011112040e06210706200f07090c09030c0311010201020417060a0b0916030b130e010914010c05030109020c01 67
    0x5801014140207082c09203d01d102080c10100020040b81012a003144121101d05012039410206042140c000b2000041642c030510300b84103801c440b421070b020f40d1010718026062013160f030a00c03468410495100f241b507031085030040c181c4920050030b0031130360560660f02481d08080e1001d05074166401e103c100e04a9022403080000d000400340040c1206503c40c0000700c6d035a501044001007079070301c078003c4440c250090303801c03140041c0240d80c0141070b800c4014006070948007941c26240303025031410b451400e2210603503000a2082000103100d001c0e02c00111440d20348040f206142d0340e520b003a40c507010700005240c03081300015148541d1007541034400038000d503a8511520040542d03201d031241010341d0703041d2150b0f0030403a000d14141040b0080d640030f019210340e0501c401241e54011401009200720140c0e04c41480d29101c0c518485030b015000d8800e0001c00001078a03001841d20b4181543d1441c0d440c4c1481e4103084250011a4200e400c0e41e0440342c02010150342e80d42e603990444d0040460300200d03004031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 319162248 1250 319160998 319161019
    0x303121a190305060c040501140d02090d0503030411060405130f0f051f080706080c0c1f060f0906030b0609150405070e012c0607030207051005030402031002090d110d02 74
    0x786000d1008000712409841512129101c010b21506603200f1800380b2804104000301009425070000300801541d020824014103144c02c0100103a4952907181080e6402d5001106100034003106000308210110304481103854140303000089081c1106401c582d00f0542d0f40e50608800001c020340028034001030400d410003440c41e100c003a0800703203000300702c482d980740c0710950740815604400280c40c0140e804d03903291400550f8840d0a60301a990018926480c14090107291444444484031220358030004241c3c00b151543c10501c108031004050b60001c0040b82c03c0c03010800205039030240d400d401c1481580c000302d03e595841840c0810503a6442c416810501c1c1c07604006e00070340d220b0000b010b4800245da440003c14400aa403902ea400441c0c903110f00a00411a80440ca152000c02416071030b220740140c41c522039490001803409041050b0304008a8000010841149410700000394066090f1604600785020358001c51210400c5040080c0042c41215980800760b440444110300c0325401002804003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 319163498 1250 319162248 319162279
    0xa21080f0a090b030f010e04051e0705010f1d010305060d08070c03060c030e120a180b2206020601180b03010207050d30050403050c0a030915090303121a 67
    0x99408001d001c000102c41c0c1c0d030041460016101201e00854400c06210001d90030000c92058543d00070740201c03090b2150203136100f041c040d03501100701c4100c10f800182040070324140015207544014039000c41041907000440113900400b14890011001c28600090969603d01c04108012041c541c040d0400341c020501c0350804c00ba00d0101c60689114010a00507141d80400540540321100b000b0364444e00003800011000340200c01400e001c1d54070b854900004008080310b80100c1c04150481014a00001804c0981d4600481d408920720b80c109100c10036180741200080d10b0300c0d418050030701a56034044803503181001941141d018070b00f000300215580c010707601c5c0c102e035a07156061905011551031010300349180340040703c0c4061030311101c4115000c0e65000c0146070042400400441c10302c44140002110741204108054481c0c1c4a5210810f03110304008014050201d182980d000b00961030743d081c8006035001c140c070710443c040c03000e012944554110150036030200c03190031a034010020010785400d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 319164748 1250 319163498 319163527
    0x2c150d050c0f120c130f090311070b07031202030903040b270405061e04060305190606080712060902030703020301181506080c011b02030a060e0105150a2108 69
    0x240c0d41085a0303641d961080081844410041080f01c2d4042e82c00815500c10036052070403400f40369584079500094901c4680b44420701316420500c0a0300000d000001c0500c49035010060f04002d0822050b6882c05c00220ba134000b400d441c0ea041c0100c0140c1c0c2c000c00403079034988040003590082c1c6514895140c8446072002c104201554541504850100461615900b8281440707418052517029124180c003000b94091003800c000310b21078464106589020000c0881c10a100000c1070340550f0601a00811482c2003013016550150420745050b080040100a205034100124031101d078880c034082490050380c00003e04294150f88040d4065081c02012042e50021101110b45c40b88511a20b0302c980d0311034003100741250003a019000c0640c1c0100d03d6169035600942c0485a55865615404001c00309a8007080c10305002c00d034200c403002e86482c500d0901680c00e001e96540002d82524848400c0088400544880c04900c152f09400c01040b2401c0710059048980f0002150400388890343c400244104a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 319165998 1250 319164748 319164763
    0x14090105100608161e0905030f0c0102060403140d110d0608030f1b03070c030b04021201050f0f100f0b07021503131709120f0105012c150d05 62
    0x1005546004000703001514034000c030409958440d5075043d6560b032908a0741440398540401541801010201031031281140600000f42c82801ea403038642c00c2e8900401d05146c548004090345a507084901d001c44542d038005462603100d501032030310341e900e00e10001a10710b041c031480c50004030a904003443c4080c41e8605000801098a4580f42041416030310a40e40b44c690241c03031102c111140f02000410314548421810340d5aa81014003501e1414006640e0300103d208180c0c4101c82482040e0108004d52401d2440f540c50300043c0d000074042850554407281c0a85401000d40c407281c1922000b00748540c00c11050a409040e2040d0007121854a90981045542101204034480e0748600c0755a0692102d0b00c00b900e02440300880c3d03101e41e4040c141c2d42d90000f07030404444034089041c18411001c1650702c3c2e2000c001c0459484000d0701c0080c01c5611030700e0a5502c141c00000450720120303428140442014000e036000e82c10342c152034010f80c80328244602064810007200b81d104031000f41403402c1c040042000b2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 319167248 1250 319165998 319166011
    0x150e0601050a08100b031c03061e060519091502060103020a1e12170f070b09030333060a120507020d0c030507020d020a0b04050901050f0906150d14 65
    0x49806a98500c02c21141101c64010080280c0090503102e144d034001d03030410a20810000c00350f60f5519445407160448039662aa440000f989401c0c00300500703e4038482c80e815001181c282c620045040c000040c00c00d00c11804100056104451388852040c8101300303800143c840d14140c41800c00606400079502c80c0c0c00e0106a00c42e40100100081c00720020400346100c0400303000342c0c0c4480b0302c0d00f03103003004860000805072000d282c02c4c4039045018420500411a4a03918242151988200d00780403d440d00d00400410300c95000300148200c0f1001080c140d42c0e06000020140300b04020200740c0fa4040740c0000c0305940083d00455030003945c1c0d400003140303010071940180400c55550f03066012030b81e541c07a102c80304d0082000c680340ea00100e8468401001c1441c006001409110b00c1d0340e011880003100c690080c6030308240414240200d00d01030f030309280181412034064080c1c19045c00021072862000e482c6c24800e942d0450300e0f03100d1a200a00750f41082d10005400c00c2070507880d1280843c591402c8444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 319168498 1250 319167248 319167253
    0x11101020309030c1903090308030907030506010e07030e01050108030f18060301031217010b0301151106040318052b0512030907050406120f06020a031104121205040b090d020d150e 79
    0x20b158036400300030345c60740498156680e200c0c0c0074510341703a03294658000340c6020303501d003c2c891011000c01d00030840079000301040d1008001505e00303030600800712003413140701071103603410a00108440308002040c2d0304092085150b403507580700340702144204074912142c0d55400030808800002846a1381e101d030301c90148a500c2c0c4a1030000d81445d0300c1d10150090117500c200d0705042c801804951011f03040b0b0041c10320f09040c800c17100d03201115030030301d442021107040300010001c0213101c200031103a84084005000c01d588405980f80d104044140c000303003d0707081c14982424400c3c40000e02104008400b011039250f0301e029030340d0a120407516207940c0c441c0186400350b07060240000c0e1180c912055800c14640041005e107a070541c40d51101c01039441440305c0010141c64030b2520134100c5203070300104020644e80110003140500e0b4030b8090384840c0c5c14004030041c00000d02c000c0081a110f00300300d5840f00c4080b1410007032440741d4400912048142440901003040c10201008900240d80c07241a9038002c0b03008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 319169748 1250 319168498 319168513
    0x3020f090310051e160305040804081c12060f030f020d1b14010e0f0103240b0c0705040b150a02070306050c0304050f0606030a020d050c100207090f020403030503010e06011101020309030c 82
    0xd130003141c0101035800703c0c44000501e810498a911035841183c02c01e1060021501d40703603450072050315115007c04a40c4101c030b1003403004e50100e604001120040c1d92031400c01d103d03192520301009002070940c40060301c001c01610500381159141d0b0f03405040194030400c800c05100040c00c002102d10f001e4003807401ca100050031007541a41c020002007550a5008200c1c030301c80c0b203402d80110058918180718100c0c140702c9540e0403060200034041c880160800b5402c075038490120340c642600d4100709500603400307140740030802012a02d0382803040c40860308000710f0542e6500a8401213160250079400604418500740c00d11085103c2180214041c134040e50807644043c002e0800180c5036242941d4642c3d0640c45602510018180002e2240c0716a00a2060781d4907840c1d038501141404100004210050b0000b51003400400c40c6403040160382441004e04505207410356070013034814030040c000d00804c00d003105d0000f4202ea2041c410000e150360382d440290f489080c403400c41c03603807034100c0f5002c407501c1d01510a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 319170998 1250 319169748 319169791
    0x240a0807020f030906072301050a0b0a05040612021203040e040c0509070e1c03050412030903021011031803033114060406032304050c090708100603020f09031005 71
    0x2050361013815000346018030301030b0280c3c0c500029a00d04d60840800314070006804080d030600b07201e103d208055601d80800ca810b498401c002d40307650759400007032107545408020301943c0040d941c41194aa4140c0762100c01e100a00707030f008d245000780e80c4001640b4200d20b04120030444d400c0740c1c420481e8800c0d145d840803074550b80c1040c0d031010060106140c10405d40225000084008040c88000c64003a05090b403070a070301c4001036420001c0e5010180c0105220300e904004500b0401000000e01215140084080c820100409e859111b000c140854940c2c4013800d103451079509008544c444501e140e00120402101544400c0701900c40c90341c0d800030407814500180020b0020704004041c18001d0071145000e09048040d002484d550380205003840000c015480c650160380d8425000d036006400610040c8464020800840e90060283d010003840106000010345001704034816100c01e8200940c5944500020211030b0003064a901e5152081c92040c98140380c0310f610940c00786102c580744a11078041c25 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 319172248 1250 319170998 319171003
    0xb0a0506030a1e020301020318060907030b13020a080a0308090705010e03100906230405100c0e040c02030c031315050405031506040f061410180302240a0807020f 71
    0x3218250703050740164401d1400980c0041100203161511050b20b245840d00e5004a42260011214241a04c040d07410100980e14104565640103c1c0c4e00b0090043c0c504564401e5040c3d500a0050f41403803c49202d40d00841d62150092400b406210301120746060305428010305c00102a5480040d46c01403002c0851194402d54021806a0014005141d012402a0188010314041708140d400564034480d42c41103540f00c2d0f2404103112001c090401040c00d05062580c180007610b80c55603022864004041c401c00e800c041c0820a181d012100000c0354000300310140e0a41c03281c5295085207020025408840424210306603058481d030039078403456254026410381d0140b2580c01159407550081c06203026142d284c48080b40c0c00040a04080f07504070180e16400c0c1526540e0300000441c483c5207065802a00307002840340c0500c0e0241c03030042c40340340b402c842c05882d0b03c1c02400041c0c0159210114038040003140b00c0001d6607140c0d13070360129940b0748483d10014080c580035204100180a400090803403181c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 319173498 1250 319172248 319172251
    0xc0e1e060f031f0f0606020a0605061801090c02010617010617060f0412021609020304060c0305010e1305160f0f0b0c06070807020f0a03020c0f15040b1c180b0a05 71
    0x60000c2c000b0b070740403d200002903603000301c840d0522520380d02520b04550482c0070b070000400c07164000340b03210031a41c502582590700c010700700f0303010302c1011114400c0443c1d941d174018110341460b2800070301140001d40480c0508040d81112a0300880031880c2005a041580312034101c480f4008070303002e46d1111608503a19201c0a0700c4690034003e401001c50041a580d240c0b415000c039150045450725149207402f0008141d10364030010308a03a010040200f4895180201040c00d04185010040366040000003514140e01511260b02e0501049a000403c1010805480d01d07000135114101c0042e034403c00009401e510b800337804501c4c1041c07000003892100a4080e00e411008070806440c0c0e0342d40f500401c03600b0307000c0141000114850070f8034181f6203041c10300c100c52140d4026405400c00401c64028861501080c1c050140078060304100d9038140080c0030151001c0e41c00c4d582e03a0315a2104808031400e044882e10540119091600c164140240001009003041901c5801c0800440e40c40c410381c00300b00e490 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 319174748 1250 319173498 319173529
    0xa0e0109180230060907140402361305010f270c05070b090c01090803041809020607150b01020c09071709070b040b09031002030601020d0c0c0e1e06 65
    0x4180c914120403050070010900e0000c0c0507400c02d50316000300040c203844c0800950b0b400700c607904030700b01c14040c90b000c203c013041e0ba42000361415458410f1407009050301d4038104039030001d07031840c00207009004402d40203580045403004248201e10720140c40b030000105420f102d4543d5030071a0320300019415800120814074003804102d88211600604550b40280c0700b2800e40300100902000070200082d8411140c6004403000310091000f502d02c1e000140c0052030541013041103a200f48000c10113003181d6100710402c2c1003442d8022948841c5880494181e0048000c01800f8010300c1d00003245001d1141e11080561400b40c0c00c8031182d0f904a030034007959000a803040390000d00503022490f09486100301c440d41040c1701d81e0071120115a142c015000c250040c0c5c1110b207190800007410810340ca004c0010789141c41402c1000c610398141140040e40e90300328440c030041486a810400d900b400980c808181c000d200d4800205164504010308884a24510710341520017400d01010618070304004405407d0110b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 319175998 1250 319174748 319174759
    0xe070f1d0622090203100f0f0c0e2b0212060a05010909020d020105030910021b12030c0909040311010618180506010501030905032712010b150c0c0a0e01091802 70
    0x342001c1c44000a0f19001c0c0f42640c240c0b02c0c0108114003811148500d548141c558036002401e10b60f00c003900c400387c0c0d403078010010800c108007044150594a140100c1305a501040d16802c0e410b070701708594103580d41e02c1d00b800b952140840c3c103000c0304401d003c1840c9214844002003084560303201c040040885250715006500b00041b50061001035008900458005845408450340795200841603006e90b8410b00c000d101c06010b603403243c92440001c12030b0320408810031200c1400d500e019102c0061501881040c40c4c85066044081000d050040b480813425002c1d40b002030014640b609148840c031900036241e8000c0d286401c6c0d4034074a910b51400d0020f071a81d03208000d0090b5918080044026014180050300d16020802c48d40003010f0f0114070800e0011920299464006806410820422210030301741c0d00396418003190b01c2d08d9a50b00713200304904001e91010709807905880220103191600c46c1c1030031744e00302c07161840115141040e40c010364102c51018070184071710380c00000c6000f2601d400c40380094100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 319177248 1250 319175998 319176049
    0x90b03040c0902181e0a05030a21050c0304060518031b0f0103060b0c010c0e03060906070804030c1b080c06040303050f0c161202040510080c040e070f1d06 68
    0xa80b000d800406a00c01640c12101c4078a0306000082e00c203800d048072414802d84c041c40d80980c0c2d8240b00c40840c1c01008100e01500107510300c0c2e11101d00c01000045a040200160740c11400103a006006035400341945100700c03034485031a5100580150f21120302c03212a0420441c05149038903001070681c2801c41c028441c43c0c1031041c0d05061050003010000103d0625880300004680300750a5405000c0c0801480008501348807614006412401140c0240b800381c1c0286007040041c01d00041c43c00d400c0400c61404603000e54850400f1107a40e40c83c14401460010203c5666010234003540110080c0e0f00400160b602c2c00c8291000c028032889180710060100d2000d10410009180706406001160000c600303840c0261184001c0454540e031541004c05545203680041c1d003503007400e20485a11048101d8103000031030034801010398030354410031258031450f00c8a40407101d5030390a000c3c1800829540200364000398850700c2101c10b00c800e0000f98170100c120000064104c1c1740614003480001000710030381c2440d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 319178498 1250 319177248 319177259
    0x5030a0810081915020310031709090f0403020606120d0c0c03121d0406030c0b0304050109060e0c01120203070906050c0106080303040f021e0919110307080403090b03040c 75
    0x10000c01448490030034111440050082c000340900d946002030b28042c800840c005180c44c21800c52440e0420068620510410410107803040455055a40010115202c1082d030031030900c003031080190711504025280e06000001003210349140c0998443d80984040c1c2d66180c0c2070103c1480494090b040340e078800c44a91980d02d010305441496103014001c0e041c0c0968a036191500040c0d07410140500054074404503074209901004000076507601182d040c03044c0703459a10760305401e000794007800d1034824000001c58100300c02548503851440c3d100100303014098401c1501521084184103442c00324081702080b81618140380300b1240721782195150004028105002261150441d00d41c5d244d5666076014081644030007040a14800c9103c0e2203280b5100e0760510521101c41000490501503162103501001d46035501d00241c0e6225100c414064000d9107007a0300e14000d440300300341d001c41241f000014800301c00c4c1c4c414801442580252100400e42d6606c10010526101c222009401820640d406000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 319179748 1250 319178498 319178507
    0x2010f1103070e1201020304050609062d0a1803080a141e060a0b0c0309011d03070b03060d17030f070f080a050403120203100612020f04050d0602160c030501061205030a 74
    0x90380e1004c1c0070405508011044642240d0042d6002e40d01944100300700051002c04100d07282c0e01061080780c1003030754841d40c088052081050300d03103600006a40ea00081c03101c45194000480611181466a0040e5403401c020b01882000e0303e04034800c40c201480901c0062544001c80c0c01180c5101e10041ea5005401021031703111030103032450380c2c0964295400101c0b480000090100c00fa902800707140c1d40c200308800036013014407096549114860f80d080106d5141e03000f04087c001c48200d907200560700d9460400003070041ca81c040c40200000c0b142440d80312002c1400b0701551256000d0029844152a810302c00d5030004400307008800050442d1001a182000a401c4980c20a10034140f600700c035074107980304801382d800407605181401044001000096404403a92908480c4039908600e003804a101c0190703207100f076015140c05042841c20361420460386a04940030424015000314200c442c502d80340080c810140f0040d03c1c150b080040101d180103401030b83c0b0706042c0e445001503180841c03141e000e94 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 319180998 1250 319179748 319179767
    0x2070f02060f09030d090f050411120406061503020301031a090d050c0a02150903011103070c060b0a150c0b4b010b120916060c06091b03020102010f110307 68
    0x282250b20501c0754110325241007040351411249034860401490a0500c0ea01d0ba0b540300e075106a100f10308094170301c0451805041204c01c4040c0103039040e42e031aa22800c040000d8030071a030154058254840d02c505125600d82d0285059910031190491030f0081d900320213203001c509450614903508030312030082041c1d00401c002e20400c000101564601da04540018040c2c008298885c4200384d000100403841e441c0a2003462a00c9103040703003950540c20009001040e40c4509040109115134a410000280d541d0036491001051301d100c94501480c00d0010050450442140480b60607060501240604440d201110070580c0046212040c88049080700c047c1403078441703000d000d045051600841c08140307000c000c0e170280c0f00034034419550300c0c220702c039254091200508848440d04151084680307481d0b080340c035004845103031070040c000d19211308019004040f0070380001d2001600e2000001010000703050740c1d044034000d80003005090144c401e0802503078904074408400e01c1c803c1000070445401210209d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 319182248 1250 319180998 319181017
    0x12010506071401050f43020f011a0a060e220207120201021c0b03060a110c0102031e090303040c05040c030e01020f04030c06050f040317161208070302070f0206 70
    0x50399020b14012495084501c04d0f984d1804d180010403c000c00c82c892104088400308040e40303513030f00031080b5850b499a8001d110490b19a40e0040c2d5683d001c0b481e20801001d80c401d49064020410f0501d1880c1d0507074410b22500c0740e18080c20100200007501070055111003270108010300740f441c100ca01681d40001140ca038010240c5040da00f0b0264401007508003a1200180c0d03c141c00050340d51034045c0000c802856000608520241400c50703014050318081a8185c00119403003010920781405090f80e9030500030003a4020041d803001c010807a0000b22641d6240d0785800308007807541d032511550349280c0c81e813208071000341820058013800c0105040c103901034800d5501ca40740018089111030380003801e81c4d00400b66a01000e10104041c02070140d40c00e11030307000f804141891894902c52140f071212500661001410305640c0405001c0295941c90440300324201c61141c40f00c0c00c0d2040d15008a000c807404017602c000074500c800281c003841c00b910850704207640145c0390707040d452100c0d4204600c0303030b03c0917486 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 319183498 1250 319182248 319182263
    0x206070c020d081602120708120f0462070504090809041b020a030305150d050303090f01180206180402030c03070f02010902010503010e07140a020309040e031201050607 74
    0x682c070220f8000d001034441e03e1401003803410036640c035004000c600b0b400803502a06542041c0e00c1000303e040001003420b08403a8110b8601c0d12000c1c1c504d1104654047ca80c003003042d84024010403004084a450440d94080742141d555860070903900c445c0d042080403120718414072002d49120b00e600555040b500e8809421281142c64031034685020500b40c4414420450b000d40000c1486203480c50107000300c801c9811306821810301d80d44001c031b00075950030740700c20082c0a165880000c900280080400c04c400b01070090000440c0d06e00c981b812599a27071040741c9111490103071280d010036240042c05880c44034035202a50101c4580701d80c08110300c42c0e000c03903407560140c54040c6509011344c031640041c41c13188a0010b4032984900d0712060290902c50304010301403c5907d4101001c0060383c100041d40e045d0b42070714030001d2159a4464040d03821a04c0c21a1084c1c0040303000c151100d005900000900049209682c1400044000445c0b181d403806410300599101c5031b550f0040c007031402d1a901500340903005088 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 319184748 1250 319183498 319183519
    0x180c12090c01080408090d081306021e07060c060b09070c060e0601030819030f06090606270b03090a050f01060f08031606022a010606030b090f0103030503090c0909011a01050301060206070c02 84
    0x100c1d80125446051b500300e130742741150742c01c21529406202c5600d5070003020340710406040001601c16140d0b202800707802e062050382e6004c101440043e60000451400c0a8200080360600c8400600b01b580d91400444015091069a40010700c0124403d4101c0390710506190a2260443e1040d44480c1c05440541c10140d503880c06580000460042c0c1004103a6400001142824018000d0405488901c10b40707900d1a0240d0a640c042100242170040b0396550f2010781d01c98660500450501c15175000c05403c81c400c0c854402403c042c10750002007111300710070610ba202c55807121003580f03e00a80221007091041440b0000100c0c00c3c50b00101244242080d890307086844811315040c0e10440401e030091980e541e10824031445825108501070340f0f60403611800c0d00d25141c001981d014005010013420040048081074220400b04203d681c2400000c10080c1c6615003440c1560003400d0700300908060b0052802078601a5001740c084034140c502640c0034014903039554009403005611490101e0300000c0560 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 319185998 1250 319184748 319184753
    0x1e0a0c2c0a030f0623011a040503030a0905090a0b1c020325060e010c0f021e130911061204120516150605060415030b180c12090c01080408090d 63
    0x1403415001d1403080c5850058a43e0a08200044900d104c40d148146860300345407420600d45010014111001540103445c00f49100740701c4c4100f40110b9010070707054440480d50841407500126084241c4400755811000c0399280c0030117000340d400c0020402e40045050091000da9500512090b420360700140844512600c3d000b4540c030a800000c0c0c030408242d072400782c24081280d20006589004909103004072170302d8000e480b0f80ca82c4041e2180001d01c10b6401d5549112003101c0c440300704003011002050642c040002c55401005400e04c40e03c200d8403e5041c0400408600c0d01034107441c0c880c4c4412071414002d03503403541d0300e030344401003a1155414070034180f050f4212440507044140000d480355401c1903034061003400080c256035060300001e03c00d560034401400321803001c2c09800c400602c1841d002c1081ca20020100703c2d040030300c103512410700380803804000024840400130582104940c0d00350f00e0640e01c20541d0f075142c0c080b18482c03e000411103000b0402061126001e00102c80b402002412100c0e102d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 319187248 1250 319185998 319186009
    0x90c05120f0d0903110103090c05040606050c0c10230408100903020c0a15030c0306050406142d040218041508150103050d180e1e0a0c2c 60
    0x100a5440c032640900800a141e04050188015000041c02e000b40454256603c40d841d07035034000c0581c1c0c10165262144414032080e030030700d00000c1901600c2000a1911260001c20076403001d40c0062052044a203011502e01f89445040c0e2824207550702c13069800e03c124042c081c48a650074000c421003c0901011408400038030100b82241c4100c040018440040d1a010741041ea401041c64410201d19000300130103450988c04220078050740c54001111940e00c5803d80081816411040c0c010307181a01c086015420303002c0c20609420201c0e04500860059500c0081c0329901140200111484001c502e0319410302d03802518020507054002c00f25144400045011508000c01050000c03910341030820020005018040e401c0f00d0504050729550305544a00e6039a600c0d1034030030303410490084032500300030388022410400742444585414090074064001c4c01c942c072a00382042c9600018a000c282c00000c40d110380307204541c1d203807100e20300b01702c0c020340340d444094003240a00c040c034413140c90912103959107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 319188498 1250 319187248 319187269
    0xb0a0c080301060c12052701180e07020606030d050a1404270605010e030a021002031318111215040e0f030c010f0b1c020303040308040608071211040504090c05 70
    0x259030341c1080b181e81401c145030b17190f50700502e85090010800c01141220107584521002124003a428403640c0e04160040354680c14405285091480d0104041400385080e240c4500443c103943c04c40d180c83d1143c0c4201501c5003140203006001c200b00f044181b507182c2c0108511148a06445000c0e42850f554041030104006c01546e580c1000ba105280d4521044e6030348620f101414007841e02d010017501c3c0d0804a80c0c0d50360751030806480b400c040a0b40d001800d100b007040f1245503e24051940c642580c0781280c900e0196011a211265410512204d43c944252800e80e6514641041c03c038026031178000e01c9003e243d4500340d00e10381081c1c40e018500b60205040000b000300c421604020350741c0710300320341c0b84a0848184111422000741800100c09071591b902d054080c11029111012010a590b403001034514403c40e40020b02402d008240010f003943c12100712441541c0030317100c0c81c69000440002004a542141107c0c5c0103450a0101303105504260b0b004100785071254088503e460b85510009810242 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 319189748 1250 319188498 319188509
    0x3150f091208010e0606040b03040807020d0503070c060203030f0708070e060f120105090103020916030902030a0b070f0201060e191d0105070908010504021809030909040b0115180b0a0c080301 84
    0x1a5510010301d80c42c0c0c0141041d00603c618420b04000e800e180b40015040c0c0b08601c03541c80c0098011000c02c003402460070481700304560092603095184400d181217a1260840141a10034021100d00000e01c1c40c0040104e83c41100c14107503107d4640c0d10040c040c4d40c002005840d8104211030080303e40c5003501da81e03000340040740610803a580c40d25000c05540c00c0002050b003000b07009407141801040103889087c43c4540100c0d04c0c00c01c810070700490001c100c004002c01034004c0c2d41807103009800e00030300091100ea5401401c441c0c0d540d4490019180d02070707081c0e90307062040507a904040c42c00200000308040500081800b0a040880c4282000d211a0300300340381030000040b00d07550b68003404a01e5030042c00010041c02000002c0c042450705800103104900d6050407009411a044001408144244112007012100030b040c61501d00b858109410121024014100000d10148540303004034000c40e4024000d0304100101b5907407074140700581d4130a40105142c0c80c05d114078002c01d54005003214020358003809 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 319190998 1250 319189748 319189763
    0x603060f12080403080702011b0804031401091101180e010b0307020601060c050a060c0318030e01080a09021e031509010b030c010507021020150a0c08010f03150f09 72
    0x60806050348240340c56980200314089121a51030005150003081d202103a400c60050b030744507140390006071100002550000041d10304a0084801c11840360090f20680380505900c03030a80c4200f05425080b100c0c81c003005440040403002100043d131084070500f00c10025401d100906a0b9030707031758a071051071080e08201c101a03000f00801246585c10082a40142010310b0300c0b010107030075611456115410740720064a40382e190125501c1c854020b82002d840d42003002d1b00a1300b000c0d4103003030041c0a103800d01c8404c1e000400c1480030070307000d500030f0040701c400c9a002002c40d1900709161900d95199401f540c6041d0305401025500031003440e121041502c600542c1c4e0010650708400001c040c105050001d06505104042c040000507031641101150102407500389010150502075002d46e20f40300d1202c0c0ca0b0460320414406445c0c81c051304406a0040b0940316040c000008800e00907664800240501301108410110402c0412000c10003c4000409500c0004140c884440c075401501c2450b8410356040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 319192248 1250 319190998 319191011
    0xc120327121602030d05120103030f020a0212010c02070b030907090209030c030313140102060c041214010213090f020301050d02010503040606081b0306070906020c06070201112401080a240b03070603 87
    0x5090500101005c0c002034a840741c0b8000209406400d020720601004e0100668080c003144618020080b140c216a0003d086d840f0f00c410070600306010b00aa481c0f210010b000d429000500e0071044415a030141c1004809480c910b4103100b003900094001e16005503140c4104c1401035900c4d10180b0003000c158103128000945c807800d009066581c080840c20440c1154414001c0122106402c82580c0646202820580d54040107043c2004141000084407c141d48000f4007510b40720528030700e0608031841104203020000102042004034002449181e0b00880340d01180c0340150301c03841c025036110307115403800520103859600b014a00701080c02c901d445200510300500d44c600d020170103075078131004c18a4074481080c24580d0094a840071540caa5018450218068045a004840c880800d1091000300c0e00902486c7d0200800b000094540341d0300d18015900105d003c0c0c0010030f4031100f036a000822556403014107001200781d0380e020b0268841c819940d00321044a550180803480040c415554089650f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 319193498 1250 319192248 319192253
    0xa0b09010209150c19050f0d05091215010306020a051605030a0e04020702031507021216120f0503190906050405060604060f030b2a0a03020c1203271216 67
    0x1c00318950001e110f01041c041c1e9076201d1000a88920b21310382d050b4800c03a0380c0e440740c6032040c9008020060000b06018015415070007581c004090048054200e42ca04004000003248545903409100f500604841c544010b2011502e15001414031050703a1070410724000040031040785201a10300220303519000001c43d00c6006038484444042c0050843d401c5180c00701650000e0703a640000207030000750205180c00540441d00030701c03204c1c582081d1580c403a56207021800019100300030303140c0101c40703002c1041c00c640c4030326104078450b002c2007545444080c6580c4807614896944041e41c2c030f02451254480c01c8540000b400303405181e01070342c4030344014815070500600700404d5a03820707000758055281d041c2041003c10541010150020303050207445111007501101482c0d5103455010101040b01d0000e01c0303c100c1607042d8010214401030030107490010b40c506106a50a210903104038007104c1e008281460303180f401890709100c4881c0b00c001c8900f0a100700c0000016500240e1003550310652810002e000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 319194748 1250 319193498 319193509
    0x5070c09051b0f07020d02011101060e060916080714040314060a0e0d0504030b220c090c0207060504060e011110090b0f0105011b0516030f05150106050d0207050a0b09010209 76
    0x20030007404410b40c0c02c02d030310380d1980740780c0307001d40c241c003911540d0b126001c40190f90080301a640402c00141c001d21074283c5541c00c4000a4106131003203802091240c0003c9c50407900002c110300040141d9517540005c3d160301c80101e60060b4280e141c04005101000000006000c14841c4506c00d030313004020b08807a250218070501100e84e690703000200b0750040b400003c440c1d83c0c420700b1901520b9000c14800319a49400103506400c041a081c0c00c0c200b0b812500080c070a1002000711501205c0c0891340503c401c00c625030003241c0f01e00042c401d150108805110a010241c050b92107140c40203010302d812446510002d0f0700f5880c041d110128580165601c410a90900201c2c401c500e60001c060a481c006039490100000e040d0303184602c4003000b80c0c000b1280001000400d100d20030300b1002d20202c4c03848154490411400e0f4000c10328049039a80325425005001c0c0000508131170407038007107844140c20060584440c2c4060342c85140d0407646130007a0040e49002035080e40c610360158020b40f000688980c0e41c0800e001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 319195998 1250 319194748 319194781
    0x1b020d020705030706140702092a090a0b0306220c0207140d0611040f030510060909150f060801060314060903042706090203070e1903020a140105070c0905 68
    0x100315002450180215100090040211019480d06010304403c0d04c002603018042d0140c02988081f41105100714258100c00480d1102420030b00801c4003400707580200784600c0341d422200e812a6070035600b00000d1440e10051a44044050b00613510120078401861024121031280088540c0d9112412105d0390b042006001818412000e50740301e00342c07000020464540e1504c01407445840d655004800450481036400602510000c1a2034a480f45051900e90340315410800c0294900040000c8010702802192003083d00321918034400032558503104040c0510311090038032140c41d5035000910600074890b00c00210b01410102034400ea0a810b0581846005842098180c0c070030300c0305000c208003d03c624001c0b100d04000c0300849202400e40c450280070680e2140503028401f2007086403c5401102c0850384481c121040c001c40c6140c400048072052107408069048196950103200080086040d01203000c814141b060622000b5525810054119001a0a80c03900d0b08140902d40c8903c0b02e641 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 319197248 1250 319195998 319196023
    0xc0303030921210c021f15060f1403040816140712150501180f230a0e01060b0f030a06030c030302030c120a051206010306092313030503040320011b02 66
    0x500c15401c140000940d1b4140280c01d242003500c0c040042154118180d02107074008407070f2812601460b94a810143c403504a890354000411116500c803070072070050904582c0b0440d0301507201400c0101420303034031a00844018003202c0c880300e4100f070300140c18010480c2d10010f16421901c0e0710894094500300785c840750001c441d8a00b06061400600121100d200103d5a2202c0300308006903490003ca0720f14090450b0340c485c1c11110180c3e4980ca010024844200d902c2281c40240500008400c91509804c0394894406ca102e02e2400b4080c452030f60b0b00d000001e5030040d04511300490460344984843c1c080f418258009c501607800061100c45094080c04003c03a4034040c151061f0030030350b0707d16003c1e01d1445003424143c8102143d0300094282c1e230090784040c01601500f241000700349001c0001044130009043c600181036295000101d80c1c04841c84d03003120b070310340c03640e00c1c94110344448d07500790b40700856001000e655100c0212020060030091085c0785004c3d066091941280d052600040d00300315412070300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 319198498 1250 319197248 319197251
    0x20a08060c0918040b130f060507030c110a0c0504020f04031403120115020705060a020f0604030201020c010f05010f0b0f070807030207051005160308060d0813030c060c0c030303092121 81
    0x400020420300e20210ba4000048106c0130f0307003903185280400181c041a40010135442c80c22042c400c1c0b40d903055110854140117522070101c454030100b41180d0309d0b040010024860303448080c0c24091410182c002d0301581c1d4038803040c01d04064681d038411146070000309643c1c0d075640c0082240300c0c440029006007801481403280040000510b10700c002e403101d1f0070b4013803540608000140d14002034820003541e44602a00010f8488604180c80c0081c082c5d445455051529802c24000c2d10015041c0e1003024100c540000008140f580303850307034a030b596400900c02d0700080002441800e011419031070080101724800e50261051038280701c10841d0b240700b81c41c1c1c8542040307420702014031005111642900c0ca25014200000703560364910000d2000c0058120040c10203401143d4159208501040d041c10b0300e100f002c1c00094540c0b140c004580f0444000b070040c217280d403500800c00110f402a88440c8205003c0c08102c06528810803d00d1078150300d842a100015005e001440003061a040b041c445a81d402c840 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 319199748 1250 319198498 319198501
    0x30702010e0a0f06030b010e040e0f100b060d0f0603120c02090c030609040219080a051c0806010909110f070f0b0604020a12050603030918070905060406050f07020a08060c0918 77
    0x403103541d00e00f95030003110b041c542e56000d40301180c2c1c001c210610035000c0c000c1c4207001e0020204100360f02c4015504c181c3c100f038440e83d01c1c0510b12101758000c002c3e03440c1c80a04414244826101c46070040c08a0101159002e5500ca4010020900e4001e0500c440d8402c0d40340c642d450221441031010381003008000c448800d8081c420b114451f503c140d8a076810030380440e044507515100d01030308020b220b07031076110b0601c9101d840344141c204500030400400400d0100400d01814490321025944108103d5403030340090343c24481031006000d00d5000444c01c1c0ea0070a0701c1ea0600c40c02d000b0219007030b400700405580c141d0f0341e0005070040108d14403600780d0000c8256029820300d141403801074000c403004000044c110f42c40b40e001a10f542c8040064070034903100146030440a0442036148140100103070b030444d00098010401140d6400d1420884040b00c0c0c65545c1e0520b41f0080c02d600c230f091900466022a4003034130184000841003001c0110030701803602e9162541c1d480c280c080c10080004c101904840d0040d00071030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 319200998 1250 319199748 319199759
    0x3070302190c0504091b17070f030f0b07050409090305091306061b050c0d060e19031409010e030106030308071b081902160e040b18060601050d020c01020705030702010e0a 75
    0x2065041224020f44005c50a01c3d01031a003004504490484021105500680000ca290a6a00c01e07280031030814140c481c1940c46007031000000a1303502001d0000002101100001080038104036440302a07440d04034102070b150b00609003654614141075000a2012404078410714001c1841000700360b032194100011423400034041c017184c001c9441c0141c021003850f0000c0520605228038000c4950092101c0030142e03552034507030014032030340320080080d1144e6071542814260500841282c1c5415403500c036401419040c1d4456154401d208442c10800d83e20588044c0e52024003e980c00f85100f81c98407401480d28080050640160010024a45400b109103074089041481104c1a40d032442070901c0da0312000d40c005910300348071241070006002c807059000541e05407503020280214070448424409440ba071080b0308040c000200801401d4000001150b9950701078802000d140e10710704405401c29001142c1c4900f240c00602083e5240e420010320b040456034002ca41c2440d4000446840c4100c50800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 319202248 1250 319200998 319201013
    0xd05040f0e0601020a080f0d0906050103050d020d02060a0b040b1008040605060303070c1401020a080c010903020607171305070510120b060c0a0611120403050912010204050f0603270307030219 84
    0x500c002d41b04540000d500400c0303450385000c035070706084540c000788417030320751440c1c804024442440291907030300404051512040c400f0403030943c50151640200305a440320300f424001002261402a03225503a00d0440035291503c00301d17060904d01030b4130b440c1070750b103070900b803202c1560001041e951081e0400c101180010307403900c0280c015202c00c1c2143c60760030070540700141d280c08a1084040c01c0e0b40c001140c024440003054021680d030300e01c01d07400c2e580d00c1d40700d80300180c407045a00b140c503007085892040000c81001034103805c00d028500800c01c540d041955000403820b45101d1440c0080010080d42d030410942c9154011840280310655816160200c0b42141c15200d0301d01c5900180a1500c9000c4d504998800100307442807c01c00a61950319401c1615014100341e2282514901949031450070f041032407018400e40b8200c40005d00a032154441160410650f070348000d0507010764081d15108a001089029845ca00c4000c502004550300c02207418041e107071000c4483c1113080950702507481c00004688 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 319203498 1250 319202248 319202263
    0x9011e0c0b0408040905010308070c050603070c02040207050705040e0d030b0a05031e100c0c030e010e06030106140d050114030f010203070f030c050c0f07090e03030f0c030601050c0d05040f0e060102 87
    0x400355841c1680c940b890070060920440e80900c1d03005060100120030310030300b400285506803181082d90f11203a6240280070701e50000312604004244500c065401505203070f0010030413184144107941d12039442c0d030001000c6542100e200140c5910040f10381400a400d4414070704160341c1141c6e5264201e00d41000a559072110180e038240c1001ca1141d8011200001c209130728000100400601c900145000010311036080300000740e00040058280c03e00355400341c008045040300c0507160614580c208641524000c6407005200c0c1616810852042851410b1080718081c240c0340d0f080e50480490381c5e0406103044804009480a41d104206002800d5003100580001c0d2019080206500c01c60000942d1103018551410505000d200d1803d50305240100702c45007601d0340c5400401071600900340c201c0c3d40c1d00046401880c41907440c0081000c899012000d55800981490480d107840300030300d501403c0451103070003c8041400485d00344204001041c500b8080c280c940c203805254540000003c0d56000d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319204748 1250 319203498 319203503
    0x604020105090a0e340c120504031a0906010e10091805032109010204060e0d020418030503160c110d081b0f0708031c0e0a140309011e0c 60
    0x22002c400b900c900e00000c00415030300000c00c103a031501c0343d43d41d00c41c050821350005000710841144442c040722920601400411680d900c040b84140e9510079004405200800040c440c0a00000001440c0700d1039120139075144456818080c20030041c0d0619160381070304001b94842c01d1100300044180a82580000c80360712400c04244190008c150b0050902e5140024080b8040042c140380c90841410100a18540c91280c03900b2550301c2d00802401c0b4055030007008001000402400c101786408022078503e503000410000e207145440c0701c103a500c8817101804402003a004402c00044007900da504100340c0c078050401c000200115582c2914400045d1b0400c0d10455101c1c8040040c0840d841c04d4500c008203100700b02c04551006182e040c0d4411606003650380b9482055004541607170044262001c81c4101c1400d50342d10728020340d100c0041e08055000b41d000e842202540300101303250b14080305126860001075980c1e0715000c00010481c01004c820708040c0d0800030900480a42d0000c1074112154 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 319205998 1250 319204748 319204757
    0xa1208030c03100e0a050702060c04050109170309030a0b0403020d0e0a05012d031406030109120804062904050609090303071b1b06020d02060c0d0e0a02040c181706040201 75
    0x240c5184451103880f0450300320071141030041040200c1c1142c1c03680500e000c0c00168080f00c90b556180100f6007030f40d101d240106030008807001303c01c1012442e00464007111098000c00c0d0390800f04588c01103480c0026441c419590203c100007440309054042c0701074a40b0100d145810210300e0801004544098a01e115080c1000310300403903003150901c0c040b42005040300c01a9014040312802c03000802500c00780035159012221000403408030302d41481041c0556078001e40b04646807003111815180c6107402001950101d4581e800700880061044102003901425403030210303004001c00500c412110000c01060040c07101c0c4c2d060110a003000400e595000c0d44030701d1320003802c1d0041e980c44502441d82506c001d1544090601012481090804410585080d50308507800741d421080201d03911b08084e03480c01c403107200801005070710084640202018030403810481d22550425800b0030121011001c0010000d5030720b0741343c0803604000c0181e480c0289500300040d4003980c031031100c19885507c0540b0090610 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 319207248 1250 319205998 319206001
    0x603091e0305070f0b0702150f04020103091b0f06120902010801090b1201050a0603110315040f02010311030f06030f030f0f0d090f082101060503040b04050106050d0f020a1208030c03 80
    0x107219400300c1c0e48240e0700c1151404e20001a1402c1c85c030450050304c158016004e2006580e021400e90760005209401040008031320307860700d40066005016500041d13800c0b210b00c00a4140501040380e0780e000604c0350740c004144031498003a0003024600003000103070a890401000d0030250307234407489041c1582c1d01c061001451411a90004204005c00d030b0702004c1c0d130750811081042004840d4404003c4902900c1603113a08400a000c05481d0f03c80d0000a103960482d02c2d021401148a0b9068000c2c180e2040c100012092584072071500140c0003102c445a400280e001003041e1403e0903c0064124018400150b003894048440400d490240700e03803030b55070b0410200e50500c901c1030b02d4009004654100d8040c00d03a40c2d50f01d00f45180d05a01608400118106da50650450322a81025084c100ca5140e5145401c40e1110307544d00302c02107400340c0169065903c514010640740e81d42111185054400e0100065034102441801705104170b81d0b0007100910b40600103040896106021a54411040c40c0b81983e02d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 319208498 1250 319207248 319207253
    0x306010e06070302151f0605091513090203090a0f050f0f01150e060604030c0e040c120b04080705010b1203090102010e03040b041806211b0501140a0c051203040c0603091e 75
    0x6d08280041c00c26445036150800103040350400004e007c505010707075000c22643d080c1a1060554412a844080c2c003450030b0004101d040d4113a0301a40e04204a10140c03100441c00351500d4002c00c1c03d001d030544103600441900c801c1d10030700308001700021143c90000d100d10310034441000600c214610800e07400240d01d01c00125140d941104440c00b4562012110750401e84540e026032006400311011100340e003458801045101e0341860710341d0b0142d80070090b803013160303555902d510060308200c030300705c2d181d64884a0801095545c104902e001e542c029000b103481d003c03007000081c290b07a51500102c130030390030412040c02050035200486e0213480d0700b0090144085c01c680c41003002010305902104048035003001c59480300440c0113403c0798040c0544016a0f480d00390112051410005125a501061001500042d6221003601034421122241080c80c5001d0141d160107060a8110320030003501d9000100700410440d02c02d0034070010708181e240c2000128000e9a07600c0303002003c5138a0065035900c0142d402c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 319209748 1250 319208498 319208521
    0xc0b0d0b010f0f030e070806010906080f0f07090f0f09081903020403120c020102120a080a0b0306060307090e03090618032a3007090f0c0e04090201090512030306010e0607030215 78
    0x10642074003108c0056a507801250010175880c005c030310725400348030072018403804002001c1812045103000740061526110444008199506450701031a03283c443e4807010f225203228404086005412240c1d40e90303425010400038001000041c01418818441807010490304600c20b01c0307000c414140080c01409500050349000a800e564006036400001c610080551108205029100b452005d02490380c0f500201030301c40034120340d00ba8042c3d00404d030030040803c00e81c0000c103071200104192407401c007000f0b005c00c030140d10680d0b0a49240e501c4002c10b14150808000d01510001e5011803021000040c001c01011500c03000e41da1071003010071020070710917500d50f8908030403c8200c40d45034440156014030701a450b46954402e00303c10901c2e001089811007c14015580781072407940d0741c09850040401000300600501030107a0401000c0d4401040544512401601120022005603220f10f003150006051307502c401d4220f4000d00003401000c2c0007a40000e010400440803a210f4502542d0302c0701d0488c4c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 319210998 1250 319209748 319209763
    0x612150f0e100b0f01090810050c0c07060503011a0901020628061202090c0306101b020a0b031807060804140111030c040f090204080c090903070c0b0d0b010f0f030e 72
    0x207505014200d4010b480e40001d9100c100c42c00002c0d2036070400d0200d010019610300519100e14140c036080301c2c862540b018941d80c802c2d0361110044200d1801c050b111a442441c100e002c0e0031103070100e000040107119034003000c280300103140d88003010281740a862500007501d810000c1c059122041c10003aa4071640d200788951907a1314801002c080100b1a41c030001d100f02448001c0040e4001c04901000c01c041454041c00c403845908013801c50b03c00b40c401d44408a03500c0f01d44d400d01001e81c44c51505c0000059a642c0d070040008c1150304206600d0b420802d140003c1d1810584c080400d0368440d520402c0115001540c055200c0d802c03906180082800c0803c0c0385c054030311030501e1a20114000b0801c10304205400140058542032140790001d1a26801080b04a11550148400c1c6078031010003501c062410f207008a40c85070040d4117807400c00a450b9550052080345800010002038042240c1c00c088006214419000e0f000340b90542c48920708444c041c284072104a47d0004058955500648071002045040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 319212248 1250 319210998 319211021
    0xc010e070b091e10030c0e09010509190f060602070312050703080a050a0912030c0909050f060607031b060b090703090f0204020a03021608090405011a0f0319021c0612150f 75
    0x3c8009210504014006c20042c2650400304010400c01c481c5410510001810380b00080c10121041c0c03590309284400300030076071090100c0da403225911040310b0814011080204038a40091a08a003540390680b60380708a0b04500c010000c0502440d0042584101000c0d00326507203090028136602c0310001c41000d02604040a0308810036400d1401145138541e000380c0041c0c51075a0341c0101da5890784100d4041e0f1b44207481c01e40d00c0d800700320013144403464044000d01400c1d00c00e080003102c109610010080140d020780e000d54190f98bc80b140030f042803e1004a85512583d40e180800518500380d8541c4042000204084c0c0179a6010034940c286500075070454104941c42c01e00c00c40d20701181e10700002c40d03920500071175000d5802d040000400250170300090600d1301d085021242032442030000400c0c99000100803060b0222100c1902044449030f2004025084040491600d03070351900c941c050503118560310150781e02450415810116103040f291031a00316958101003041c60480c59414064541905032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 319213498 1250 319212248 319212259
    0x80313050405130807030c020a140105040e0c0c060403080712182003070308030603010f0608190201180b030a05180a060f0b04020309070303080a0513020d150608030c010e070b091e 79
    0x45e18141500007010032519482141c1a114090311070405000d404030401140380030803c1130105100056010688503444a130301854a03040660002e46289407890650381030300455031020500440c640d020a01d042071005800b001e200060b0f0315007181d4501400404080c111250802c80b400786000481c040d01c0620000404550321207072242094ac8455000b41c035804d210398078220b03010008010714090001100c580c0b0000d00488621108040300d150700c1c10000f00e0403c11440e0001c4c80d011440c903941c038064120354401c1ca440340b40000c04103007240c030050b010011404c0307600c0201c001520005442001140c3c0070b000842c1e080c41251200000e8480d880700e455019002000300003c080f400a5a002100e02903030b501c441e25100c09c1c83c56401c071001a125014010054503151380941031800104483c14401d5145031000c826003020310702200c01d550007000c669000000e11144844d003d01495100103042005000c281e85405210500307441403e43c03c40c0986c00c5c1920b07100740700c0301c059044604207402504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 319214748 1250 319213498 319213507
    0x501020309030d0605030f0a080d02040509010603020d1a2d03010e0c0a0b030c0306090c070f05010f0c0203090306011707030606090c03052503050c0c0102070501090506010803130504051308 83
    0x10301d600c0343c10003003105900034500203001801d071900107840d2802e079072840082c0c58440607648614a05901268400d03940c103800700000265074813891401c50007000d03107940041e02c90801c05080429101400f0500001400505a140e49503441e411029200c3d10465020711480849034001041c10741c0516241d82c1c10751030515070403010000403c00e80c015090446625001076190000c540c01d41c00140c5800740211810700009440b81800d881140c0c020754501d1041d810242d055964000c000440d58bc11661039440380c4200003a94000e002d00c8580e0303c000d002644c00e03c15200701003996410144503440c1c407100c01e04548205040288184405141c200d50140310040e01c40142002400940c80e1160000f032405e00094110146c10b00648103030040f6183c061041158540203c000e4032024111441c0d03e04104054078000c00c00748003c00100e0702c20310000c50348030518104035080020583c050061a04200080b89108a030b102d2403c061b01e204480c009281d884400d42c0c0e8200200d610b8006000d02170025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 319215998 1250 319214748 319214761
    0xf020a0609050d030c0203030c09010e1201050709050f011b1b0e09031905040b1b01060b1621020628060311090105060c0705010e0402070c030b0702010c0e0a0b031305010203 76
    0x14801904244a8034280080340070104107d969201c121041000b00714144007a600b590300c02c081401d0901d100030b081403c04440030b00c006085030002e0f100280801c0b0410300400050510341c05615611509080180d2465080500900380c6405014003c1910703043d402d4900055003042d0841000d440981100d520501d0f02c135089903560b90050060958480c3c208140940311849030040f94260380c2141e02486c00d080f0214111440107003000c541001d655261744005c1015940b01e400380004000c00700b18405140340a061070001d0601d1200c0c10002c1180015200c9201c1fa000102907400680803104080350110b840c4210540103003100044409070f041400000a0103503140c418a47c04000726034400b00799907544200022440b80045c12002c680280c0340c00c2191b580a070020000b07201020303001519202e41580d1f8420003126680048032040d404006000b400d40d070911404034140c61038188443c08907610800164000300d24422a41254000070000e60b1011003030903035030340007a40030009640302d05004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 319217248 1250 319215998 319216003
    0x402181906090504020a06080a060509090c13110f160b10050315040203061f051c120c0807020f22050105100503160f050f0412020405060f0109060f020a060905 70
    0x15200c94124034107190303000c82c000c0038601c1500d0086031300800c0d01c0d91282c40d000c803c0d940840002d142c3c40f00b80c1e070390f00b800003110388901034000d00c04e9031180d026107035480c0d00d6010000c0e011949400615000d1a000c0c5c180b102030181021140d5080b80c114030140c1b1482c000c80c56000002844100a0024001c00140724100304040703440d0003a50720807000d8651146c0030801d1001008003c98012354589d01001c013085000320581c1403540e4111002c0c100c0e5001c2501e810100300d07240f45c00058045000c1c0d100c0003074004c0c000d00344c0f0510810b032141d240c00d02d10720809440b40c1000e4040e00074040d2003001e05590f17558640d0b03103e0285080f180355860645003810a4162443e008150074403a4034001e0281c2c807075541d50340744900e00322031284545056070700706c04d00b0480c0e0445005545000a40900c0810044404c1d01e4084c00701500040c2155200000c000500c3c0c810301c07058881c041c0c4254003480ba42d004030011603800c091341000390f8100d4a410076103c19140c100b24030341303004003501508080c6041d10040600030003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 319218498 1250 319217248 319217281
    0x30c030f030132091005060304150c050307140d0f1a03120a0203040e040302191103120f03040204090305040b0c07140105190513091d010c030501120b040218 69
    0x2e0090003208581d258201040c540e0740c1400000b00f4009000a500580381c51040d1940050400d48840740443c3c0f200301140d0154005d03502503903203001c1466038102040050191101004d05c82c60403e0035810700c00070142000d51043c5440e00b158401140c0020b000515a00040070940991400d12004c800341050240110301504100c1c003d009032a070348992100c900b001c4802c801010f03802503241a19202d42d1300400310f03020303000710214061020340c60301e808000e85034025020f004481c07154206910004041c41c0010036040c1908074030080c486480d4003c611400d4a52240d0180c81c0400c500c2c0d510b2800329080d02c07035a0001800808040b450b0f1504503000510082903544000544560022038401075810b8015060240700d14403500039612400d6210300068800402940e0400e0005600c0c1c280b07042c29580e412106050312541c0401c4060f2a9400b4080c0031003808540c2010001075041000b45440030a0040d0060284504000850115100c03130140100448104a44110500b0a243c401422199 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 319219748 1250 319218498 319218509
    0x30403050f030106050d0f05010605070602070204060305030f130f1505091f05040305120f030612030d021801020c100207140114030f04200a170f010c0509042f0903030c030f0301 78
    0x50100141c1f150b0500d4800c650503218103803240ba0601710960f40340800b03503222120480c1c11548175a40000014020400760413075403080e00c5010f80750000d403102701d2890b000660100c416040011402c011621401c41040d00e5150b552a0440d42c801014021804010884100d000c40b0f585410440c0d250702c1c0d000d4040c106a910074000c1d41d5130b0780c0842e103030010a400b0b81c01c00c41115010030008600b003407804140e1001c0c1c0d4150b103410390341040c01c6504d500040782c000d03510000b4524a9070103112615a4140b1041d405204100d80042c6109170b5000020350b218114058480d0010070320002e444a40c0c0590305001c03600340400c0b1907d58070700e482007080b02d9040e400e0f10304840d42e40040c0c150a20820f240301a5245800c800340c119407100b4644458101242c00948414a00d070081c0d0740300318003080c0280106140c03900d041d2510307a030303a400e02003e0108a45c0d9940d0207091300d007004074034104101600c600d2004c3c500e40d40181e540d02c420003000003e00350322644000020a210000c1c180300100380c2603000e0340c100d68 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 319220998 1250 319219748 319219751
    0xb0408010b01020703050709150914040303060905040506070f02160321020f03070b28090212010b0102070e0c0c0d0c0302010c261f0602010203152202030403050f030106050d 76
    0x41c801005994449442c00010301580000c9001e100341d00150388081c000003c0d045034003264a5407210442c044a03540c6101c01c09029801040009041c3c160090744000c1020b43c1c410840d510b019250640c5501001d0005c90400403040c04181d0014400c108454890301070640c02030001d9900e1070150f1058820903d215420f182890241c62018008199024412465405149010306640d1066a0918010800e0300c1d216110b24010000c01101d2102180d5440508400900803206004009084190885846880e0b04040b0010907990303010560340c0488400d00c020085a07201c1d6012450b05000342a43c008052140b0300807418101d62208126181901980080040304d2404104441001518016210240c076070007440794a15551248550320554600c4160183c1d03014811180201009520840043c1c4d008024420b900e00d00c2000c2d0880110229030b400d0038005203071810809a003a888200f100d242c1e001c000181818003880845070030000c20311140b59250313101d03000a8850b411217441481000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 319222248 1250 319220998 319221011
    0x3111309140108030d0507030906021c2412051c080f010b03040c0510030605100203041e031211012a1205071209110310061505090916020f06010b040801 67
    0x811808484906030f484041c0a9483d2408030321503074010b40b00c007602c0c200c10581e0f198000000f20b1564409441e55240000343d41c5d803450341f24007081c1d041e582180c901400f8607105141c20f030050410307170001c0c5040321010380043c1000ea800703007015030500b0030728408a5102c032990303c01c03031890941c0044910700c0350320740c60b00900c200e9803500200398075404100c800900d2541800c805100e40d00d400a00c503803078450b0074a00825141c3e103580c04102006644080c40c405a880402c0c14001480310b8003482c0165014004c2d0043e0700c51658a41000c103244000f44a001d21a4010084031441c07429044410001000e030700e807048c02440d02c10b80c0c1c07000c201104803a40003d503007243c81410803130072405924000c3e0030781c0e03030b50101580c01039241a00408911008a50f88049840e4032441d40e1010f203d1010040507205000400030700c5c010103501c0001112410380100041004a0b00700745c0d80300186143c0044002910301141960008168078011202d09142c010788601130002503042c0741c000050003590755110091015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 319223498 1250 319222248 319222271
    0x9150602120a0f030b0607060905030d0b06090d0204320106080c1608090d0b0a0f0b09010e07030b0a05060c06072a060e01321518040303111309 63
    0x2805a40c129100140c1c044910a9000d1311980284a05240040010f03280449070b555000845c0e51081d4200d4540c0c001103100c003030505a52281c500c42e040c00341c0b140c0345000c0d010743c00070300300200f003c0000b03109666807003181c60081d20b80031015400e1032540d1070070340c80c40318000d0b441802040d092041600060b4803070001080b42d4801015070f45a41030001d100f507102c1c0d80c15946e0500c0d1f81c000c0e00000c0d420100701200c0002003800b1405050194110398000110640c0390741500b010f503000d80320041e009070594401000075030a554005607200205150008044122038009010007001f83d01507503018902040b04135441e80c001c030751640252400d0f1911028030050004142511400e400d0354140b4496550303501010941c4c0c0d401a41c4007409107400005d07201000041505031902800b03142c02c0c0100c10810904010f01050350305500306c20150b004440c1001c89800240c1300d8202d9407007101400c4001004902058040e800911045843c040d402d40c031902000d1060f4043e00041c400c402e4081e0030200c1d40f002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 319224748 1250 319223498 319223533
    0x412170c030f12070c08070f03050f12041103010c020d0c02010c082101170a020118030209252307440a05090105220e33010f020709150602 61
    0x1121a030161206d401c1015a0311089001140c240b030990500000f00507811940000000928801c68100960792540c06e0906089096101900d1424000d0789032120001110750005000724814886203044119001180f00403242010900030051000001164000071001d40303070b08d004100c503560102d542c03c580c1d0380e282600740c40110103e2019a504804142400740d481503000c001c10081103518204803d03a65404580d01c1402201d207104803800c800c80078240506c0d14940d1620100c014034003883c00b241d40c04c03455103504009200240c0300080000c0c0c0c82082144001e01805146031880c00320481d40b035100d4811450759003602e40c08031007601e030310003000c5903401040540f40720010954840381050389140c0155150b501042662120034003807400d100000c1e080b00f0309400a402c0400d820400d40c10040039290440c60400c0000e41c40b0249850004d80c0100d40340c44407104d1803400d2a00100f99200010140d0510900b600071208076414010b07010700e202214440c0f035045418603402c5900380b91607400402e1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 319225998 1250 319224748 319224767
    0x50115090b090415030c081510140607050a060e0d0f050408030301060c0f05060406020a090602011e11091906111203061516050601030302120412170c030f1207 70
    0x38410410b0042006900780780d4407600640c44040c2031030300003d40f0fa8a980c080d443c00307940072803080d9102c80410b40c0d0b82e220020305036820280203082001003d0a00b01512080041070500c14042e110106016080c050200280d101c9150491000c02c80441c03410b10054a0300000d64101010411440110703541e00d1284080310119504400607504603400d0031001ca6054282d1103054601d01c880d8012440464010300603580150701c81d28005940c2c1e0442003014180108507400902964913080301400a20a81c071144e084050b41d50800041d844410001a0400d02803080010340202c02160218031181d54442054185c0d1250b80302d003403c2c4100c81b4003031503458071026028482d0b04001d101082e4581444242c0b41c10f02c1550f120310038100788040b00035001d00a0b44000503510f0f41d124000410034150148008200c981c000300810785045d0a117000b80a1984c3e100d10010b001c171084050340300c0ca2040303c0c0240c0d42d1000380c0c44180e030381d908405d5903c4400e80c2c01041200303a40c0304c52100801d40841c011b0903480c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 319227248 1250 319225998 319226009
    0x40831120507090b120f0105100b090306040201141e0301080715050d0c12110d05013023030a030e0c0d02010302030406060506041502070b070b040b070909060905011509 74
    0xc0409900f0041ca14000e009500d44542d008072000d0010300802e4814001000c0c41d54111b400044d09151440c4840c0d004600307540050404802000380480d01e4802203080c84c2d0082c0c080c00c1030022400b400164001078800c3c404005040300181140c40400c0c003000c40250704a8850700c0031141c81ca81c441c400d14021150050403600840e0042104210f9000751b0f400c1180c0c034221604003030110210841c1c00000b0744008810030015074500181703809100641c1d100d224050f0003040d960300c05d1784c030070503070b00c405020f0380d100140000d0520540820104030780c2040c240b40c80e4407003400c61900c5201c40c040b19a5281c108400400c042424a4601c1c40b561000081c03140caa40380040c002d107401f0205800660081d030004d041a20380302d450340b00108803911100000c5c40148460303408000d142c410420700030304100280e08041e403084010400346c03009c03c02141c00245c000d0381102c144800740c0c642001c10307189081d841e84404d004500300680041c402e100ca51140c1d049480c01c108410a52a074900304556140326030291 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 319228498 1250 319227248 319227253
    0x302031306060f0e09240406061806090f0903120b03070305031207020f010902030604120201330609050a0b1312081e120403050a030b13050603070605070b01030b0408311205 76
    0x156051b9160200f8020b410a01690000a140e42c4602c0d11381102a1025000d8a81503220b92040041004500c501c1026070034400003006503204c2580c009041000010721802203544131084922255020b0001000459010007201d5981101803c3e481c1d01c03003000c4a9440160040004644640ca01800780c0208c00c0d9004010f0002603403150341d10070900c124501e0000440d9070b60202c8407840004065400b40341084842c0b48050001140d4651030003110a40146042000d0044e003040b4646401140e4000d4480c142d11590301c03890882214600b42c180d07a03200c0c030703501c0d80308a030264140030004005107422486600002902d40c100c0107130020a108144a20301141468000a00030038415006404d40b062189004500c0c00101e8002a4800c540c25464a03041360341e402c2032001c503103010440c51005080e141002400c041c16900d590307601400502c0041c212400000001d010840502e0880b601900094408a141c1151029240310001d507030f192510150200032020903d00381146203007184c035074400300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 319229748 1250 319228498 319228543
    0x7030c02060d0906140f07140304020f0301020906040b070b0109060b0910022410060206010501140307022803030506061303020d0807080c0318010906050a0302031306060f0e09 77
    0xa0121690040085800141d5104450780c000307110750042c03016905418251005c2c90510aa8008903010042d0100080c070104d401140100e07450101625849030b0100c440c02e40009121003c01d019211b0304d1700307081e4424000240032607292503620203080c40d14080c1180c180b443e038070341c448101125600e006003014180c05000c0800c03e403800e00e0180f5845243e5106681c1d807410090409100d002042c0c0c0060350b0f044845e000c12180d0108000f0500080c00c0364401000f441d4035100002c1c0058160280500038003030000001420140200700249840143c8001e0102140c0c10040180803400340c2070003100000d0402c0c010450030314000d0161400740c1c1c484042410514595400c0140e003800f2074004443d0078506000c624045001d00f4050481c5241d00b5028642c0c90080c07907440c41d240c101c05005281400300c0d0180c04e021066000c07041d505160007505005a0782e45803600d010382c00448106c1c0040416003040404030f0000c040c03234410012951644a00040c0340c0f02c640c4001c0d260080c035039804c3c480440ac050b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 319230998 1250 319229748 319229753
    0x110a080114040510030803041401020406050904050a0903140f090307090606030e0a03080c091c0f0c0e0f04030806120a120f05040b03370c08072f1006080105040c050607030c 76
    0x3c0115001445a01d0300c41e03402711a040124266003280e0f00c8000441c801040c014240d04250107134030b03886280c12400b040038a6040d60043c1103d1842840071303885c2d48020416424602e203001c1261225403008040343e20f065590b862140261502d4092000043e00f0b258200c0900400014990b842a9140d15084000c1c0c0c1c8000130710105811949820380e001016920a02240c805141103058180c0104030b400491406410001e0142ca00da50200110300524010002203a000c10341c00398120f0b62503c0e05400036103924000443e1089015800d9075180150b01c00c0b40c080090b00100e0780a0300380c0e070b61240016510000016245405288110a1801d20400014440c0303045c207100610f00341032520f84103c5400c03209061442c1c4081c00c0042505807982e0382c00c00880150460410fa61107581440c101d08404241306e144034005511803001c0c400d26080d03441903402040240900c1240d041d0400c41000780590700c00c5800d02034901a50191002f9103002404180c5e418900c08039445980c060f00c9a040d003040c01e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 319232248 1250 319230998 319231013
    0x7180203060a05120321011703040e060402070f0b0901050708011a0f0c03040308030c0c01110c0c01030c0e030d0201050a0605010c0c030f0812040807050c010305011d0406110a08011404051003 84
    0x503c003021060008200c81e800c41c84842c04106d029541c10001d00c5015810001c0d081030881081004400c2a8020b0104004600c168140300e5481401a103016071911007d251640d140440d0420091580d00258204081250150700071403151040d6903501010380d0766450100f815100e0b1055210001031b00f0030001d031402448100410b0300e405401e00f140e161503078a40714500c03290010740c0c84450310b0300c0025149402104c240170300500d0108103851139241c100e6101641da0b5031402544460b05250f11100480d22440c0130311510f021088001d030964556040c0840000e0003000d0468460841da454500c0110307540d40b18801040c00c503071b840381e50562124115141d000544555080031140840108042140c04440d0000d41d4029841952880d89035003107464018145020b44c1300c201d0405141c500100b150f140040001d591804000021030341c02e4a890401030301a000305540c081c00034000261958405902c50201812290703008402d003619161102000140c8009803140b50203111611700900129200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 319233498 1250 319232248 319232269
    0x30e0c01140d020301270c1706010c060c02010204031b060c08160206130e0609090601090207050a2027070503060f09040615170304030f0c0f0807180203060a05 70
    0x40e004640c184040085244244d83c026040800741c002c0200c01c5200c0c03450303c010700310709468003c24144200b0300c0740710004000501c541c4074009100c85d100c01140282e4050440d5680d043e0700207001303110190960330301078044d5002d131008071410020200d40c17103240d481d811000030541d01c20380e8440246019644411089800c140a100707007444580d124540140c0c0c5003c010300b4207031005040121103034a4500c1204a1100007015103006040c40c404012030703e0070202c0c00c0c03415507402c480c00580340e528034206039103004030002d401040e00c0034848140c140d0b040e41c6402c2c20200b00d41214032100e5000c00d00c000849290006405d00303480c4603554046040d2030300030300283d68850009440080c58285400000d520001d082d01d003525401c2e91080c20509000c0c1c4590490041d06003110b281032010001e0020b241c0c2c0c0c2c49a0b202c094041c07107411fa220010001d6510150300149034111f40e1842c0c160b02d0343c0499455800600c1044c45070200082c0313180c1040801d00030b41b0710410000b0140e20b041890b0400340f0510001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 319234748 1250 319233498 319233527
    0x21030e0a0b071b0b07020a090c020115120203060c07110d03051603090806010815010e0703090515011e0320040e010609150602120d150906060507020f01030e0c01 71
    0x8100030030340d0000701014010142c000c0c442169065407100c0c1d10041c00601d504080c2c51040708208400268446244100485c3c4080c040015401c002807412401000220264215211640c2c3e0010304c010641598500140c0201e05071038680e200c2d000c0c0302106116020317005010000003050b540452030b03d00c103907150140c0a428039a15040841e07145080c840700c61340c82200070940803001809160010440c1c1c6024003156030041640d0080031062640c80c000c140710305400c0030201c0c00050706080c8241c005003a4140d100c401c0b12140c2a900080014007042406a24500c2d5813841c51341d00e05000d5015040205c80d085200420700003404041d4009204036010311642050319803020b50500c0c0303000d204502c02405000f200044203d048190281c081360142c0c40201150b00c96440407606030041000c0300d070703010071103c40042d402c03c0c503440940c178203c1c19520107031034145004000100b46d50060000d1241510031941464054041c3c001034085485008584105509c2080c0c1403050354040c13042006e10b1503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 319235998 1250 319234748 319234759
    0x61e0a0903050d0c0503040606060513170a020a0e0405010c080105090703050612030c21030405061915231e1903060e0c0102070b16061a031e0721030e 66
    0xf0007200500c070943e00c0449055000500010802003801100d114410203042e03a4541300f0300d00340381d4600c2e07254814418010020120310541c0c5d010f10401041200c1c4d02c031558060010080f0603030350104540c0c101d108840944465081c04e0f00c0412961140c00700d02c2c16100010020f00e06619008000c40040a0052180360410351104011142c030b40100064135041c040d20b00100b01001c0015201e60a0f44140c2c030351071801d0a014420f200010700c0c0466802d5011418240041e0600340300364421010703148180707001c00c86021188005c1107900341002d0300c2c080180a410b040b10052800801c0c0480d0020207942c000d042004400c180009240645400e001c4440d5440c1d21103045d1b441e80c80c0e0790200c42d401041c10300242c0c8114144042560140300340e0005265480000f410115100070305d000180a03004000d1440e0303581c00308003071100900012204017070030240450340156002001c000242c40304072022003081c0b050400024010607400c410b9111803503c441d010b8103007019980c1c01e507034206140540d1075110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 319237248 1250 319235998 319236007
    0x3031218170d0504150e1b090c07151a06071101080709030804080c0f0915101e03050402130c020304050d02041e0209040c0c02031e0c0a090b03061e0a090305 69
    0x288018080e0500850203011850b040c02c071010340c16070844240541c031b001c03540c000c110840001c22602c403004000c075605681082c51569030b079004000610400c00021b1140c1030303100d42442481220340c06010003103428030b40d0403141c20388039040280e030f80130b1214000c0842020701070841712944034a0a2603041039042c18503007010340d00c81c0c0e501032140d005504074440ca64001484d40301d06147c4040118007108094030240c0403414240214140c40c0e02c0062030390701030f00c00d00800002951041e00d0f0610b00045c084100b50865207850b4000703015000c107950a901c41ca1031040403502c00001440741c82c41f039000e2034006600c2c192500042c004100c14910040e170784070380c0d58921203401018100c0c1c402000600741c00c0060b03580c04000e0802044404121110007000320242110307005890002d10026036603c10600014803c0c04d80e14134070324080c0c2002800e42c20501c1440000752403281c5802a00481310b04600740d411540d58031004842183c092a0200c20600011002c81c440c04516406000c03203500038030381280790 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 319238498 1250 319237248 319237267
    0x3030e01150305010f050f060607030c02150d050405100e100e0321010314120a0c050c030706020a021e010c15090614150f090a0213050310060303121817 67
    0x40705550391042c2e4190351602075414503482c1c28400d550b400966900000c000b0300b4041d0105e0f102d4003030301000a050010014640302595111624001c1180700141c5042d035a40c01d43d002c84d8080e040c01c0d6021100380c89640500120004140200e2074500f069900812103420007031100405001364251080305800100a0482911042d10401d0f100a8600b10804465455440d10015042954900c2080342e00081c0d185e141c145041c1c011513030310140304d1030640c82d5450725050503818184250f8030135030b0620500720000341d42074001c594441018001c0342c100b0500800300c000703182030325100103401d80041c000348140340005000340b0740007070960105140005d070103099940c0c52080300d09085044040c48000350411101510064109490190660b5501b144400e000302140882d40c1c0500540c8400d40c010032190501c04400c0a502c2c002e00b0010100c40f00303852408580c00062141c0c0c00241c00041602190203184081409901881c61810324200548401615000c003643c0c42ca031400001380504100c0a02d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 319239748 1250 319238498 319238531
    0x1391202030c0c0d05090901030b07170a06050f09040b010510020f01060602060604060603140408160f1a0108060702120a05040506191806050403060b0a030f030f020c1c03030e01 78
    0x4140b210640c0d01c0e60f20101488110b240c00b00100000c0200320b405c1111881940b42c10b80b07000c0c1101c0d480381042100b500c1c8c0440a80f80307001000c00304513401303802a04000229407030340c0120b030459105551510751070500c0c1e000d00106490450300035140c0c0440800400190400c1400d14094a500e4030594401c050102c04580c2554000c1c0c0c8170f5070050f030040381800b09929081c8906001005036050400000c1615246082c80640061000d0254040481e008400310080c600321a5142d5001c0c49602c0101950301d42a80004c0f00340c1340d00030139001e4250001c00c001100141d61402102c10390010400cc170f4100c88403240c1c0303910102c809810082c0500000416440704005401290b0880403030210120005400405800380f1001101246818400802069400c241220241c940109022441c0d082d580d011900030b40c181d600051450074000c403044c1c04d140d070110440782041c04030b6003610010b400f20030420031400c0700421000041c0c9505520100002c0c002c0c0e0042091008010002c28143d28613200c04a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 319240998 1250 319239748 319239751
    0x9030311070f150e0316020a05010549020304060e0f0a08090604050a1502010e0304060c020f120d05030f0f04020f0105031b0d091b031a04060207150e0139120203 71
    0x1c4007041c4500500046103021748d089030103060223180c00c506111032001c1036240c055000c48a00f00780607a0100c002c1c1a01000801c4003a00190f04000e4420306a44605c0d110007544100c42c2522000d10304102e040c07652070042004001d041e554030040181104580b500803190b40410381c10303540088200000200b0744c5a1907403420080031454090626000780e0800642594908000030510307402c10001404003a07000b44005a01540507240061421040e1020844000480b04101300f1440b030005860b841a60060095108120600365480030385c03030741201d9401507441030301c0096100c602484500040c1d44600043c552298446c40c80700030b00f03d000e4810000c5a0312407017800c1040c94075041004140300d40c0c07040b0000d4014114680d1012546181ca440706030b04540402080e0724001c54010405000454040d9021a50041143c00c2c11b4450710001200030007444109903041c0d4241400f12000c01482c03808442180361800c1801d5981ca046140d40800b0505030480700b0a20054520b0241500300324070185 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 319242248 1250 319240998 319241017
    0xc060f0c030507020a050601060e0a032310020c060112020d141605010e0a030b0403110105010b070b060301020a090504020903030408060c0a0206060904031707050c0a0609030311070f150e03 83
    0x62000c00c048004041c1c8400500c81c074299400b0104280010304000b6042d070440e5010b2138416500c40d8074900041d180c4d0002c0c0d001034642918800b900101da1252172140c5d0040486000300c03160341c0780020b0604140d0085a031004a941c10100040010b903080c54180c00c5020707c000c1100380d40c03403800c0c0c0e1210307c0700b20100320401d200d900041c501c403021810003072500080e01003420081444c01e2100d000445415041c04010100d042c0200460304150056030301d58078014100e0b009024540c1c5448231800f03107412000e01901c88200050200d90582018402ca070103603400c560310820494200030500002c3c2d0300aa028541600c410480007803ca4814040c645c0a50300303172a901030359000d00e120001e152042c081c06251080d404107040c040026041075040d0703035680c11041d0140a0f60b5400e0000c0c2d9990060306080b101c0c2d40282c030000b8040096503440310820521a4800301302d085800703c0c400d18a40100d0700000d0003004c080e40007902050b010383d03803090461174103140070403a2081c0c1082c0b20704682106602 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 319243498 1250 319242248 319242251
    0x6090712050403080105091b070f02120f03090a0b0315040c120f0509120301080d030c14030103080a091a0706050c0918040308090a110d020f03010203160905030c0f100c060f 76
    0x10700880c90019145a00020407800440030f00d08c406415441503c1016801000700701c0d54501c070411522811304a4520704407080c02c0d0740050781c1000139540c45c1d900a1608912038007540b0300100c0c0002d060700580e805260320803107a4885c9903148040c00003c204e126601400d0090341924443d21685a01500102034203502000c203480c00e010b401e09240c40d03147c4801004505090005000da45030000301070044104030703e004255405000c9003510101a05223500001c100e0000010060260f900002c189151084d950b80100c1c956603440c403a100311030038a5008040d013003000000042a80368202030340208400f01044e15041003440010800710358040c3e00108401c900303080005041c3c0017008940d0100c92031016050400c25035444030031040541340b0042c440c2c17141c40f17000000d5481e055030368088150301800856a80c14203080000d0b0461205280341c0000761310391008595403c001c50b9407601013401800381c4104200e41020000c1d00e00460744020100100e0032080c0300402e1840c00303200840a1103110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 319244604 1106 319243498 319243501
    0x11010609051b1c0204060305150414060d1a01081c0516080d02070b0405011b05070506010303030222060c0c12050a1e150b1008010b030609071205040308 67
    0x3030f802401d1001c50040b80342ca806610040c0103c05034445c09601c8940e0b030b001c100c1503403a21040042091808400708034181400395000f2840381c840c002c840c1c61010f0003080c503c8145403da021000c10750000307408a01031210840308201c2600140380c01481d1500105203c511044c1044001b80910350004a810382c0c00c241c2e605442c50710307510506000d4241881e04000b0302034110a84c00002501001888004d168004c5080701c412544c0400602403503031031500c095000b074001c40c4101c80c0001030001800000180c08140402611840d21808000110b508001101c503440d030f0006510035202c010950046440050322034801c82e44469a42c8000586901e03003500706080290060910310010307040e00e50020300e86c01c4802182400d42e1008506005000100c84a800a1007800d00300c1500708041010b43c01c089c1c088690241da58140190200820744151040f44e00c01c80d020f03800038100c0e10 = true := by decide +kernel

theorem cover : BRFrame.Cov 319064748 319244604 := by
  have h0 := BRFrame.cov_init 319064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 319064748 ≤ n) (h2 : n < 319244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
