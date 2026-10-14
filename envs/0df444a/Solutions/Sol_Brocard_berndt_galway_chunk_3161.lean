-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:50:21.408535+00:00
-- url     : https://prove2.me/submissions/ce96061e-4692-4da7-8241-9130695005d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 568345323 ≤ n < 568525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 568346573 1250 568345323 568345331
    0x4060f02090d0804090b0a05011b030215010e0907050303190c06020c010509060a050703050f010605070c080610030308090705220204210506162c041103070807090f05010305150301 79
    0x7060010f01c0c00600151503000340c040001421141c100890071944e031040a02288103040c2c3c44503549010070300e00c03e40d1406401503e241140b01310494501c12400d8228400041d60441800b51010080004c030300509415001149402d03103c2200d003213202008c1041c0c00030001030844010810025070195030b14006800000d101d00d08240300740903146c510460312181c42628007000144180d109000f4030780100034030610003034641d0a000d0100c803070354040c0f8804c0d100800a110001140c0604029462203079900c0041c0320055030a5207002040c0c2200500155402c1e800003005201e00d075141506001501d209001442d5000c031400e400401a00035540111a2001c1e80c2c0c0003c520314007840c041c154143e1080702503511903645d0301c81c0c0c840414103846c9064002001c902d40c28410b44400c41e11148909910341e5028265594076000a054803102c2000c1800c901000c802c2c4844145c102e100d0a42010450400804280c180b00d0002103c0c40035106250405880c1c5001c20720514086109500103100540240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 568347823 1250 568346573 568346599
    0x150301030605010314070621091703010906060e0f190312031e02190f0c0f050f010b0d03050f1303060207120e010c0809040507111c030f1404060f0209 66
    0x40107082c00d100580c0e103941c249103001070300080400d0850941f04107440740703800320200481488182c0301c0311041c038003c20340d0b03038600c5008a415800c516941c14070409810b6504d40c140b01c400000d03a110b40c0d000302c05108480fa807041d01c41d510010b4914050000703891043e20b50b85000b8214001c601c15134005420440010314a000d9154580c0006074038550008120150060241c80e00b001ca2085d1481241c0d5402a03a40070280140b045401d07001926442c54900c1a101098a601081d00e50030007044440e0362020450140e000320038029075001c0d41d0116440740d45c0b80d2043e28050094401c1500d010000b0100003807a002d603600d03410525001e15081041191030f107800707181207003203650880610700208060b9109484590f21a004805015610146250401e00c10313800b40b0000d010701034000010720a101c42c0d2140c00c104104401808010902010b09500c07500c1440038007107501c0031055003003080c2840c03400d5008641c0400d10716045035001d400040c0412061004000074014001442d9005000e45501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 568349073 1250 568347823 568347833
    0x306030a0c091a10020307061d120304060c0e030a06050901020f0a020109060e030906071e06230f072a0c0f030506101a0f16060603140a051b15030103 66
    0x1a40c1403d40c0c4184841520315030001c00000d00d00a050002c0140e00c204420000110190800b030411805020800860750155107024101400080304004590000c0100400d1016502600c1042000c0f820500328021120011a441709040701c0c02801190326000800c1030020258100c1d80d00b45a408411901c44090300d4000703000c0e0030f002c08251001401d02d001800e61403004412502c2611005220526113091a0b070342411400044a40c1d510311051151210f0225140740100d40d5180700200f00c03500c03001112800c0e40189500500322012103200c00f402c11403c2d076084401400d4034091980010300308505c81f01034080c03440a907000104200314580001401c01002c0014100340c0303100d1070544960343e0701c94640702141101071084a542801003104e10f500350340302078010103100f1900403042d4601b00c40546003c0f0007401d00c1e1003c54000f96075031030400c10302031044480580c5001010150103002da01d501d40300c0d541c1c41d86000c0c01d994000d00c10000342181d542d9504032500070300c0015919449607036030f00305 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 568350323 1250 568349073 568349081
    0x703020703020415080f010501150c02131814010c080432161a04031b0b0c0304050a2315040f03060c03060b0a0c08030403030e0312041709030606060306030a0c09 71
    0x7405c6014410702c18860180c50301802020b040c1c1d0b1a40c11400d0100985040072a40500080420b0b0b03004080381d0305100e07822500e0f001d8140031140c43d4180c0460340e43c240c600030300c00d004503c0e00005580d25090840c01d4041d800444076400c15008200d9200380030f0308150300261801904804280c000f040520000800c1001c0740110050f4184280011080d540c0d08485031900714100131440341c2e01c0100070a00025043d0886c10000c54042205030355051340f10800400c06a01c501c0c0104050b5101140c01c0007145803035440c1d88082c000c2c03020200114103055001000801202040d64480c0308454051107500503800c0a440040c26903241042d1195030302d040074801004044440c0001174208107002c16802c1c5c0703100860b4941401640c402803404a144c0700e00c02540c001030011010180c40311a000350500341000074050811020705003100f5400c20f0300d0041d590040e484407200461005200c021a16503004c40d003581d01c00e034156111956642e0b003070006810a5480500100f01c03403850100418000ca8540c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 568351573 1250 568350323 568350329
    0x3020106050a0305030715060b0409020702190e2811091009050a03030e060f0a020d02071406180f03010608061005030102030f010b0d09020301020331080f0703020703020415 76
    0x8102040d150710620010501501024060358401c000201c005101000c80d103200e20181078001440d1521000c00c1c02d5190310031342c01908065000706d0803006501c0c2180440010601c1c1520301c80005182c1102c0d0800100000d050200501048803500b00254008140204e2504041c00402512420200700c1030260869480c490203041d5091410000d540070360402d40c01d0b2000101060010342c9150343c1154080c105005094205c001030048807103030f292030307005007150341d82d65006091200000300c0c00900e0310a4650003050b84201800368107600352541000c903404515084900c2d442d0540c000d010890f12000440072036050341c030346a00080c0e000310228040d80282021080000125540e00802d801d0340000d890301d090403100070004100c4000c09200604c55806180300210300c085c00390b0002802c9030001c0321051a0b2111a08440010f0040703860342d100128045092100080e555490704101070081210b00400c92800084030f4083c14000c02170b42d0300555000344280300407204003c6050640000b84 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 568352823 1250 568351573 568351577
    0x118090f05091902190302130603330b010e09010b030106021b0f010e032506020f03130501050703110703060204150c033e0d1404030b06010305060f060307080403 71
    0x202103072103804007003a502205a089143d4a22405650302005142c049000c110549140003035030000044c0c80b2140108400c0101100010307019196040042c110100700311035041f00b40000300d1155a1034840c40c441d8950000c2c40c4000a100641036005031780c2506180003442d4815940380c000610140f419005605079505c030341c01d403815191940c0d044c3c100081c0c9441481d510004040c080007555102e045200c0c2080401812101c00410001c0e910800e00d400c55035507003190002d00420f00c1003d4041003001440707540100110b00e82507900c2101001139030a0f000d0b290400034002170309800e2511404000a00d1000001a941203a58915000000f98814403070000003007030390312a00d41d00320f00840c05800000d070940c468403030706014861090b218102100c111134900d1860100c1003001c00b20b400d41c144100541c100109402409100c000c4c00d06040401080440c210820090000890702200103030015001c1c00c5c082211749680e030010f003c840003c24100c0d08400040200320104d5405406180500e0281d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 568354073 1250 568352823 568352831
    0x102180102030711040225030207090c02030a02120c01093309020f10020f0f0f1213170a02091e06040204120813051c15020909150118090f 61
    0x61801640c03280203a6002628100c0100410a1241010b4008000746c0c0341c58000220f400c0203183c102103104042400a40c0180d2209400340540380951044111a120500040d030070503001c403800a6460300d1004000d801c010300031556400400c0c0940185150301c0e03108034580729162800502c5500c1d89000a1190b09041c803921800b244071041c0e100c4c118070303030b0340182c03d540c814420701c81801282c10700e003c6030354118400e10100000b2980e05120b00f4030081c039440054046440c7c0107076214581140c00d407281304038040410070090442d10402a51048070140c000071401504041183c07410a11502000307904144618100b01c510501500c00c0d0f03e114840b0070658883d41c4410081c0801c90203180251120680d50711003c401081981000e0b00d50403c010710307207071102512140410000303030300500031405130740c108030981040200c10100c42c0c07076952080c0811410102010000f400000000d000d50540c080c1151400388a64810001403008025903811080e120340e0b540100030050052503040b81c426813030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 568355323 1250 568354073 568354117
    0x6041205130b2109030c010f110901080c04090510150903030e04091e2108100302010507260301060315030c060e0a120b0a0501090e0a120e030f0102 65
    0x14010340e5100760401280ca01554103040356180258080000310301250990525022000c558500c064840c4072444042e43d00c9a80e510030907800d42c0c2d46030741d04060440c14034a1515180b0800c20648848150920384414540c80e480c0c0b00c0b0f503691280d0380110002d03608050811110240c2d00300d110b022034005240780160040543e00490b40008680401400a20007404405041c076094002c21040c0e4082e115568080011030701e2090700c83c030b4121045541d0f0135000d42c00b00340321083d4240010000b4190400c2541480d2070010481000b04502000703040c0030003ca0f4540c148a4100d1520700001c031154518442c07640940342e1010260400d1155000003818054039070b0704c0000c511901c1041701c1d0b200b100074810f141400d6041d03505c11550642160031615491000400c0c0742443e0120b01000e0007a460f000399820103021240940b08160007400c4240e09089440009001c0040c0034481030303401c107000389650712207010211001408403e00c030364944075041a01c40c0c80041036008002a150030310841418180c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 568356573 1250 568355323 568355327
    0xd1209171b120a080a02070b0c010c1b0b07080a0f020d0501050f010c0c1206020c0a0c03020a050d021f120905070927030302070807020d080d05090303090c010e0d050609060412 77
    0xb6102a00403450308410807080004d00620090450344007180141c2d01042c0e1160f442e05520340201405140580d100d0300118039503500000c1208640080214140e080350327140e220050301641c00361200c01080301c10380006202d1801030b130220401d21030201c401e544c2c999103506600041d003002c3c06042c2c82240d0800c103600d12580200200c481c1a60b0100c03d8280031840c000030500b00c0c08407981e00b640d400d6000c0240d4200204240034110b0464402d401c451981401c50040c80003500c2c25800c0307280214018150071026031f603a0001a2841091504038450300c08a200d41142e407021503850f858086421700c0062010804c001c140030302510704104040200340100c4603001c0841c07417401e1100700c0c803214000014004c24031940043c8003d40c05088183c0c60a2a50340c042041d51004890580703429401080d1040355a020740a92508424544001c43c1103080c49603000f5110741005030320038184a0350081d4440a522079144d03c0404507001b8050301c01c10700e40325400903207401040741c0494541c1a000d0000444c0b034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 568357823 1250 568356573 568356589
    0xd06050403020d0305070909150e0903030702011a0604120309050a12110d0b0601080c120a1b17180f01020301060c0b010e01030510050a020d05040c050a0b07020d1209171b 75
    0x11b42d5070310300000901d00300b0f003080280013a0040c1603c1c0d003007494001c071f00e00703000483c2c40d401890000000c40d030300d1130035960080c00c503406902407140c4540000e04030381607940c0c0d0005131020b68000584400040d20070f03144c190b840c100d207580f040e40c000400308400100160300c2a08201d5050141c184031810300f0204080020b0302484a8006100705240004a05c865111720700559020955020003442d0441e9040344640000003125094402901c0d03901d40b840200c5010303108074500c210780c1404100c124a141c8030750010315004144444401d03014075505c152100800c00040ca0354500c50086569584503e40102021000001601d000001e5000021390200e205001412280c002003d040505100455540074104c09040401080d40a0011440c4012140700d01380c003072880b1ba04800401407811090006a0456501001d070480e028020300016031a201c132400342441d81f000302c0c09101d400406003540c1c104199006002c001c0550210300c6010000000c280714888201c0d4a40041d20090101700300500b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 568359073 1250 568357823 568357831
    0x51312080301141201090b160804050c15070206120604050c0c281e030207090b010804290a020d060b0703050a030b0406081510090b011d0d020d06050403020d0305 71
    0x4280c2000104209209841000743c0e0110052030030001302c4050b0080b40c03d403280ca00040c0e6100c81030006100c01091410072289030200c2d5810502c3c01854a40c60701ea866580440d4000d0080102440c00e0340484000400c07540d02650040082d07803a030071100038588151200300c0322107008915140c00304a9180402c41522214500c0038002d00b200505060103540380c10100031800003070100c421030000020350914040301c010703441103034108010100e41002454100d49500982605283c4184144644d82c801039269019400c100350341156100c006442c41d08545210306030314204c025100740414000035400130544101c1800c800e002039603c0740b40d00211441505001004100c04000e0541014041c0c0c0000c0b006441c000c000003071966450144500303000340c420180c6540240c950822010560611001c40038004c051002c104540c00000041e1081c2020349209050100d088404561130352400c528502090380a014100c08040394603055003e800165412009402144541400340f0f00c20b00c281d03481 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 568360323 1250 568359073 568359083
    0x21614030607030b01031806090b061906050903030c16090b0906060a030f09060501120b1302030c120304051c03030b010e090a09110402070c06091505181f051312 71
    0x2403500c0e809000e0f0020b10450155905064494a582119900900201e400c2d6809036801007100c10007841c14100c4124010401031080b0021280400341d201d141b5000c8055030201d050142c1d552034103030002443c5000d0520302d08507511900640e003011410b10a440011644507190900c4040b42410801c00c07400313405c076842504940284000c035400344c071035089056495180d040014115242d61588003d8807002d801c103000e00000010058200034000d07124650120071403c8800806a040d40020b0301c403000d80c0d040c1c0b4425120f50744600140c4a083c1308840c0181401000d208005d6005140f19040c01e88104040d00464605004465154003405420000c003000400e410142c1e924504807500074024500c040c1c1d10004007103207405c00e5031118402403104502a40980403158a8050010030030101a00074008140a0002030711a15400805031a80480504151008000381501140407080e01e0001d410320960340112040d40160880014039020700c0c000c241480c07503a103410000080303142011008007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 568361573 1250 568360323 568360333
    0xc010e061e0601120905010e1e030405090127050106020601031a060a0512100504080408010b10020c0405060d050316230709020a020109080319050703050c1605030f0a02161403 77
    0x6143d600c141280c40a8000c809070001d90540b42e41c54203801c40303103160601003290784031100ca00c2c2c801140c0c03017020500c0802980214581802e01012441c1cbd84d5041c4103141003c050340c1b9050349100000300c0499901c0702c03010810812580d548500940e540c500317120a40f0480400382d4201501c240310403150f4491000903040c0c03181c81e480d03d01442550803030030b40740d00814010a0500d034094405406101d024070301409800741c81c1c81c102100542107480700080e161203560044560801c142d008550120744640480c0c0005041d40d82001240c40342e0b01c241c40c01005130000003400705075041c0c1c80d01340ca00418010714920011040c0004540c049a07035501003c509030780154401c0091034959001410500f0851001107520130079a511a03c458006441d402d6030200c50f403003015800f03a0903101e001d0f4808810319060043d801c0440c0b00902c0c9104014501c01c5464814002034244041001101e01619100050b5a81e4042c441c40081d00c1e0400c4501c030800034040004c000031805400a800b2890b0790008001d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 568362823 1250 568361573 568361581
    0x7211d0108160315060e0f0402190503040203070f06080a0506010320071509030c05120405130c03060b0d0c02060114010906050d060f0905041b0308030601051b030c010e061e 76
    0x20540741402c00d142000c1503200c0103c610402c4220100320010807061300c6000d81e843c0d01204000c2802000168540501e106000a0140e41d0410490441e040c0301801d1490303807a2102c0c0003107400e00c40705401ca000da20503202c10010f40340383d201441c10321810704024200820b84454004400303942c039900b0740481c0d4000c21403031003000000300d000816101c0c0c400c5a240c030300366914448400941d10b102d901070340070414400d201c20500009000c4100403203a400542440c050030000001c401d030043e20703000c162003035880c0e20041a95000e640050040e03d100c805035503c03803195400c06c0014003106090b074001402050300004903e00d01c2c10300010319000585604180302e007031800889807504040e01c081c1c1076513100c542c002070102401402e6006021050001b040c6898203003403202017040c031500e681003034000d42d01003040410a600705480d00140240b800341d40d02c1440c02c6c21400d46031420040f040e0a0b0000103544603c1d14415480460301d0500c103016141e255585d4521900840f4003000d4001500900c0c02c001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 568364073 1250 568362823 568362841
    0x3170c03060f0a050d0f020a0608330a030c08120405060307080615070605040b0906090a03080601020102040e0f270319170403180b0c0c0607030507211d0108 69
    0x24420b6005000d10f46615640d0380007890704c021060003a00c80075203465408095040182d50807014080d241081003607800c0104040000e00090317200040e5401e42c103040300c10100300711501405151802408028000d03140c1c00c200790007603c2480388582910480d50400c2001410350203a07000c8510040c10700303045694100713085c0c0f40341d00c00401655005482c0250b006030034007440007602c852809100000b07420f2800b4030788260710340c402601d040f115500807020802a048005901c00d0340740e80c540f40180703060701c0e0200103034068052500880c42c030143c1c460400000d02115182c00c0c0c8070700689170300403160001448460591701406808900140c00800000d10400d03041481c5500213046d1703251038111182e10340d008810000040c1da00b100021022a140300074010074180f5100540040440a0f15000404011503904c10460505da4010080411010203140c050000c0d5040c15070489400c8030701c4101c880400341007948804616011171028004261030080340c5a900008100684070201c650301d1392560 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 568365323 1250 568364073 568364089
    0x15040915050a02092e0e0d0201120609060305010209150a171306020d0902120f031b01110f0304050712020d03030b0f1f08090604030f0c1505070c03170c0306 69
    0x2c81001150204020080358030388601a1001c03500007036012012468400860381000c81125200c02045400c0c0c115050b155a1030182d000c401e5424213040707009200184540010b400c1503881001c0301ea24100000050040c190003c0c210703d2011130b0a00c2c0c010000412048040c0030790030b4000c000440d00d40c03100300b01120724456144c002112203180040c010413587c54030140da001039108034950742c03105e5210084ac10a4240101013030443c1d005800d00280c107a480c02d03600d000310300c2e9a0000168034001880f10a40a621814400305d0425010343d179122211541c1081e680185c0b0221400e1080101c0010b001d10b10b0090701e20103981c010035000440b10a628228003414016103020380c049107031012480c00b50f4400ca0404805114040000e065041400c0d0141050800034000e440c13075008141000002503005010010380301503810501201c000a04102009511824a042d0802c0c9400288112190041c0e042040c80e4841d81d03070b9650b5002041c0c8c0c280010181561444c2c240042800802c0b101d14007900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 568366573 1250 568365323 568365331
    0x607020703081e0a03020c191502221d0c040f0902220305010e0129150f0a080105040612030206041e2003240f2d1504091505 55
    0x21040e4140c0c0403200f110b11154843d00008011a07400164584156010f00c6407090441566006150b650300d83d841d4908a50401c008010800340e00150018244807404424202e500c21100c2121240c1c4d02e40b040103401980c0305e00c6802c00b0713041000000b199154410f04440558410f030140c002c0345441c00c080580a5041849481244007520300307041461414101a4002180100000300308120b03080b16560840c3d80c1702d00c101d41420740b01c0c02e60072140d0240a40d2209030a40949401070b2070b1001c030300d10054500446541556040d400654243c2103907002e01c9142c16143e00b102c042080541c0c17107241e4109400101c4000340503810003030008003c05c8d041e055250f0862851441c0441600c3c0542d41d5403003210802e85a0900b0b40c0390b2561100450408100c0317a0302e86810009640e0400e00c82109219102c00010b2407283c00c21072550000b0b5011110507a40c0d04820280d11040c00c1d6038495280c4c10b44007100403a50300e13052007515044404186098014100081d030000f410741a440c10040881c0301500b0010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 568367823 1250 568366573 568366597
    0xf05130615020a0b06041a090a110309030a031515080606041203020304031a09060408091c031e0f0504051903080703120e060606120402040b04060b040611060702070308 74
    0x20001880641810201108000650140c40f08800c1031901c02c082500c06485c80e4042d520781003501100d5140c0303500c4c80504000031a40e0a101e65990402c000c06064051050903400d05c000c070900034006000000b4103c00361664606100104081101c00600081c520035070100a042c0b034080061540940c40f41c83d04000050300706880e1681310004081040c00c06c02c0200e0050b40006070400c01c2c800c2e40d01d405541000000d46605d05400c240000e19070710340000d04090440c58000651300c80981d40e00320036168050400c0d0340144151407504005e01035011400a038100e050302566540d990620400030003410046c41d0711094100740c100400d1103040c240090610300c0803002000c012000c91459000382001c2442a503032103c1c200595480e182c10f99880301046045a400f4a081c01030719555041994040300703030007041030b455070344ea80002005000001d00701d9402a1030b280021804580150041007038401c5030300c0d4403c480d080c42003002d42d81c3c0400c840500050b000400207200040e500c4000b8003a1007009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 568369073 1250 568367823 568367831
    0x6010c03170a140c07050105010b09010c120e091018090507060c1b140112092402091206070f0c120f121817120c1c020c03090405010503070f0513 64
    0xd020a583e0078001a1603078121300f8004207034182000424001c0d0390150100025007418801000000380c04040a25001011841490140ca400e00d10500000d008204c00410b4507150b414208e0004034003141e94040e0500500c5d031260f01e100800c5141c0103882e4050743c410001c1c42440c1c07038260221101800018211032160415100307d840b80b4070914040086e22a0110304054086e003200058418208140c0b02c110060402d400c050220340507009006904558201e040d00601c1c0052550b4024807404007142d42c0484443c500401c003c800040c0745124040359210380c006411400c2041e292401000310081c1403a480004c008166407158201b07801031081c034100384d1088000001104251421082c030301220b0014407811905004041c0d46040038100c0d04045249031a0580e003604440b05130040413055171010020f00da0011541c44e2480c0c00e061000c0c00021510751004a94140c3c40c0c1e800700c2e49140c80345003800004103413442e0126000c42203803200150070b0045450302091044601e00e01c181504020740d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 568370323 1250 568369073 568369091
    0x91e060d02030a0507200a12030f0f09060f021e09012a03020d08010e0f04140718050928080712020a0512090d26070c0e06010c03170a 59
    0x34000345024000303c080208581c58a1040180480440030b0129108000701140c24007814002c10002e80803500022412410802d00c081038018119000700a90703000d203403a070408106113265100c0005548144414880f90615440302010381c01603102c42d498042d01521640b480004180040203c0351041c10124402d2540b582074121100b10703902032010380760a44044c802090742c11b110503034801c2303442c5c20005541d50600d1020710041c8401440036810b0000d14021809110080c01d28801066541040303542c1580c5070f070407607507100c0040007001907201c0c01d00c00443d008007008902c1c00c01510541d117407000528407001d0b00081740680007209456444041002c000172845c1300e181004410100c1c2c00801c2c0040311890814903012441041282c2c0240901140d00c03c0e540c0c1001c104940ca400c81080502980c03d114140d0f41004508440e032841040041e07844100039221400100715114440d44a0b034a9035100015901090240d40c014000b8103074034038441800034904c40064101c40d2401300020141c207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 568371573 1250 568370323 568370347
    0x7110d1b0f0b01080706091a03070309022e110304080309130e010219020d08091209041506090512030a05040e150d050f071e05010309050f060406020915091e06 70
    0x2003130b0800d0081350416002032201540000b50900104078503180c00c0d0040d010f0b00040415804080c2c10f071010180c075030340e80e1002c2d9510300c41c02601241190161000c0340440154521607592500986004140e800381884d0307039201c01000b510200d809850103145400e00b080308000104205601215003a81c1d2410b0f0304411400c2403000d40745c10183c503602a11510311100c0040c4c50010b0882c02e80c020400082c040180c0707080d011600c0220102c0d02820552104070040c0000c001d02003410424820071500d071000280c041d841000c0f0340c00c444003030380c1141e940d002d400390540d02c92181c1d00d0b80002003070040204005000384281b40c654072000c011075540c155842da5000174001408005c003540d840c2e12018190f0b02e04441444030200a08450f000041082003603000c1024800c418403600b41070550b100e61785410b0101c00d0001c40071580100b02669070600c1c3c2450000000d4200614181c0256030142d0719603400c6000404a0744260b4004000e03c0c06c0200000c0381c044818400400b00790010310134030111004030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 568372823 1250 568371573 568371593
    0x1d07030b0714070b07080609090a030311161a01051e310b01120c020c0f0a0e0f0405060a06061b0206090402120117060c0f160c060807110d1b0f 63
    0x1a101e201031322010304212800600481000d81407074841d8240c03606000b41913a0000b00d0309206a41030802045e5224030079106c3c68a801200011001c114a443c00c080410031000511b624062003800b1340f002c13a07601c40060107038031156860070030398165031403680c84170a1034275800c1e07111408034046452214190180200c41d410303c8003c0f502c00f4a9440381c280c03201d50340c0c0091020005002e1014108800c825000c0000e40d07034010100d10a00540c00203411110a80340c40c03400310050001c101c0314001c14208507218052600d001c4a06503194000c240107d5008903090103010304a501c03a81e90005898604c00c450231061580c0c11040364000c10070490240b46889600245c6503036810302c40803110b65850025144000c1e0752801c8a802030350009020480003510311f10036550b42052a00f482d035120864030340303800c048007040d02d00606008031403107000900690006400d485507801e40d40300c581104070700b00ca2aa40309080341c6104081480c000c2a08003100c0e81c0c840c84000540520b0204255104a8a5a40c110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 568374073 1250 568372823 568372837
    0x809040207030f08010503030f0f0f0904020c070305011b1d0102010e0f031e040302012007031e15060b090114040f09090512070b0a0504020d0b090d031d07030b0714 72
    0x3c296040c1e600c00c1039036000180540108416405545000310b804040881c9204046500408001c003041d00b18004070541d003610500710016004650b00c00205012903540c00c908d1204075407a600b07002c050180ea9040c0244d1080d00c0302c0c15150031102c01160a8074020481540c90040e045659900c0c1c05e1043c3d240810040071000e0b202409142d032003400d06035840a00052202860302c2c404c04000400060f41d10103c80180403106440500c103032404140a141001c0361075001410700490320030030304c050501c0c032841584918401c050a541203071080c0418820f4680511410055200500c100e140c29400341c606220a40840d2202d6840e1a4513401c500c03201980c150000c0300d00c175541d480002c0402000300311000135404a8584541803024558415907031040040825042c01c0e219000700c0c046440f11094a0301080c4c5c005c00d03428461802201c595518010314403100000703403d041000541c0e544980700e1349400c6040c035000c3c0c8041e50440d140c544500750060407881c100140a40403c7c04e40c03540401800701 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 568375323 1250 568374073 568374077
    0x6041412041a0306010c0f060209010305010504090201121d07080d0228060c090b0a180f03050c0d0c05091008011406060a030c09050604090b030f0f030412080904020703 74
    0x1004050405103000110340120502000422080c04810745a100303114440301c50b905015500d90758400100c4101c10000d10017892110b05009a0040010540241c0a40402030340d00700420b80c0e03100200416150f2700400a40410400b008501c00144a41c05c422448100092a411184140a4010310300a21540540da00b0341160384807020096051080d08403130815440e5209100e20b040200c05001d00480000504496039196240c4120b0f010f211190014200300c0b102c15100d031507100c0041c0c2a1134032101120034034100003c002c00c00c00000e542c44030a80c0d42040082079140da200040c8100c0d8031018500b543c0c41c655041000032035985030807100d0300c210882c60745c41c45030a15107405103094440e2241c0502d0603104000c1008078a803100310136100c444480303140c0441c0c50880e45005440361079040e044950400f40c00100071981000c2a00180f40c04c020560490704100d10012405840704642201002190001c1104108010914140c101c0c1c0c1c0d40243c0f40d4a1425000c8400982246c0c040b0f101100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 568376573 1250 568375323 568375343
    0x1507060504110a0315050c0408250b1603020c400905031903110f07111003150b030601051903060b0d0b04050709180f06030602130807170c060f07050604 67
    0x185d40c1d800c07030290755000000414114105401c240b181381c4c4072521128a0b04da034200d0342000c10a0300c8600710001000f014503070a43e558030705143e001864038102c035950039400743c814441c00c0a03540c100281162407003103048041c0400210801d0780303001c048001071031207003c0d03141000041a0801841c0309201034036104900540c1d907800c550341a00c6003c47d05203076000c05e01d0310700355400c8440829001180d000031407005441d50b440c040f500c0c001100e840164201c40e00501840344800d510303501a400f0861511031046c0e04855142d5545d82c01c0400d11040b42c0305800120140240c1c04904d142d03079070980b445402400c000c50410340714140102c2d590007500030b020129844200c0060641040d20540390450490715200d070310b203402c04801e4808d0b0707590f488000004a40c0c5040500c0b100896074040d41c061580b00c0010342d95882d102c82403144042d10bc1c00340a030729004001c1c1c009242100b144191034282d5905001e07144000707151003084407a0308044800741094008103e008001802844414452886038050700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 568377823 1250 568376573 568376603
    0xc03140c012a0903030302070311061501020724030e1f090c050102060609071b051009050f06190906021c1a0102030c06220b04120e1507060504110a03 66
    0x2100c0c940b20208903882c122100c0050003015400400b80041d2509030030b0169440703d1510741141c0403512520a03040b140654000d2090740c680030126420241c01c00d07421500b2131500d03291140348000301034803a03440d40546008c1c10548a8065007003c031445610030151510745e91740988c1080400d00da62410b05015681d8040902000768511080000e02001e2000344000d140400104952120141c0000f05000c920010300c108400840704000d100e079440340071f540d043c0200aa030300c000380c004190308071114056800ca0040380c2c100092400c0c030074852074000303c0c20101e080005d400144200c80c400e49105408111400b8106c2014000b111202082100010441602d55141000410020900c0c1c1190010821581c6030480000c00941041c402c2d04506411000440040c02401e50300000401c8588080100814880e00040c152003940082d11520030041994041010517510000b108901354010300807036000c02c0c542d41c0000e501901c1800f510160780c582c4400141d00c03c4071a401202d000c12141044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 568379073 1250 568377823 568377851
    0xf010203071e0e0409060f09050307050609010b01210b0d120801080706091a0c1c14092107180b19080d1103090405070f0806010f050a0c03140c01 64
    0x8029041c1c1060008010207482d24014104561900d045114907100c0940d002805142c1d4000350710f01518101c1000001c2d030b18a0701d00d0b1650000b010560b954000d240001e914101c041c010141044170503950034404250300746110802c0c0e40850015007002c2d59410302100613488000600c100140140c1e00e910800784100c2c8020800d1005030800195504040070400031281c000b0070030400d60315110030304108005c1405040284d07000c0c0100f00441d51190101110344030340100c1c0c0c0d078240300000d9907452610000300030480030329104400038030350400c0604450100400303008500c0c04001010394240da005550f10a07888a80d8121000c50f105241d590f44208012481e08050741c2030610580f4201c81c0d2464030f0f00c50400d4031540c0a01400301804410350788102c90500a000321017002d41e00500410850a00200040581d51112006004980842d01050041d03009230050444020305654840c40d150307801000b00c607a200c91000403400d1105018854840ca400c260103001182c80700030001900030b0380700c3caa07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 568380323 1250 568379073 568379087
    0x5030711011e1a010813061e0b09091c0f020a1505090f060114090702160e040b070507051b03030921070b07120c1a16020d05040518040309080f01020307 67
    0x103d080780c4106400b48940c103982281034254030003c901e030801c06005190a000e40030b04450300c5580300040c9003041d160b2940780c0b00d07805420010380644000d4000d541e802500341e61000440600d10342e41415039007a441e9039100d00421070f058052481038075040d217219500c0800180c42038100810309a00d4004106600004000e688200d440400007402203500d0700d486103046882c07172003c1900803002071000a0803540200040442c91a0aa4501d6400340e0b0b560a400ea03998010b03901200c004000e5000310303101900c0b0300c094a0b40503400102400360443c0140210030b441e01600d2040e5054001440700c00000c1c0e540001d496000c81852965131590101c803515503042009a4101d200c10403824481c0c400403400006011580b0340071800e100351000b480c0c0c102030102c0c190078000d1903030300440c1608010a8454170455069407007000d8003240c207941c050301030503030301d0703010b207006151300500c0d141c0c0080c1c148030200c3c454a4229002e424000143d41e111450319003820394400310002d01e43e400100b400340d01688424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 568381573 1250 568380323 568380341
    0x2010e010c090b071e06090203010b0402070201081303030f090f020f01020609030d05100f080a060b06160308041a0403090f0504090305090409060b030d020c010e0303071205030711011e 81
    0x10080107424030846000d41149240c3c041c06642c4100400c204080061940300703581d03890b005c6085240c5030036031440d1100141002c44000c0b4003039402c0c02e03403400c2c00d82050300070f07501042da052f12056555580d1f11040101d2240e180c1c000e03402c042d2034290100c5000c0242c4201246a030050030041c02680407030042c070008148241440d0304641c000c80401c950070724040103031003520400340f84c0400d4039101e40128a1482005e5003040090201081c3c000a042c18002071001030144100e40c140090f60840b010400c035030040141102148c00421502d500191060301040d5010f80728107404d100c4030200e005401b85c40d1500321000c030b0100b0040c0038144582ca10f1885010000d0808840920091040c4c0d900240540280040c01d03000d0b507154610f200405c00103030015103541300d01404a44540500b010001e560341700012580c0c0c0440c080000701e20341030502004442403d41c0110b2b0086a500c1452411909039200030210070070411000c1d6100d0446800380540203152401d240140315259000700c04034200e07940d0b40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 568382823 1250 568381573 568381601
    0x70e0d171611030304141e131e09050717030d021b100506010c03140d09050d180b040533071e050c010f0908031605070605030c070b0a090b13030201 65
    0x4042004080442c01030414284810364406802d1720000e2147c0c0c200070440c40c0c1307065000d011001441316218465000002100810b180100340c5445016400c00312001c00002400b140c0020006020407001030740c6400c0b8440545044038500045041204100e82202e00d0380d0a0a0106011044402c0c0b0f0411032500d90308008201013240303080c6040080d000044549006003404900e24140e02e0440102d41030340d40060003070f50706101d045074a01c0c0ca1070b1039841380044200030400031041c2c00c64001e00c4c01c1da2403003602c1d50070050074603250900303040101c0c10740001e13191045900301401611000000031444616195402100358030b03582c0301e24161002c46890440f5410320090244c82d5000b05800140c07001c80c0100c2030030420882001020200c404a071280c1141e4254400043e103a030201d03090002501900340a40240c4044a440e02d00480d801d10064841d04801d4400f441044082010400c10641000720030000269441142c0c1d0340303600b148011a40a8034840b4400311a005058080c001e40c1c20f844205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 568384073 1250 568382823 568382827
    0xb18010e060a1e0504090f060302120304050a03060203090c190602190b0403030e010f0606020601150207060f1107050d2907050a030e0c0301050c03010f0e070e0d1716110303 76
    0x4064003c0c007a66111428041c519205000600b4050059003105d0141070220401d004030702d40c000f200c0c40641000c0c0700c00c03401038400c050301e003804000110594055640060161890518580300d002c00b07508041c2108119001e000e150440b141c2e12250b02031740041494880341900d030304e0a2806070401c100d00c000400c941003400e0400001445580103c0da200c0d0f070509000a520110058090050502c9140e0442141c5000d40c041011900050f00d18100c0e1417014a05010200480080b619a003252241c00c0228001c7c042007160b450080742400c0e42d04907103500329504940c1d98800100074400f0014290380343c050780e00c002000ca0480980280c004001c00c07108803001c0c24003841c010818410315600f4410190707103079000d041e04241884040c00c0c402008000f8400303410000d00d4000141e1080c8180540c080f4405800162943c0c2d4270320003403141c04180c66260b840b075005828070080020a01080760b03541621104194152001c10150440d1200044c1522039441103241c40101c0e4201c10f0281c1e8801c2d401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 568385323 1250 568384073 568384087
    0x90801020403170c011d15060312161103030a0f080603010b10030c0c0b0c040e090606030715030e0f0102040f0e040b06010c0f050304090b010912021008100b18010e06 73
    0x82c1e40c00320f062040454a015034601c45580d00078014002110300d80c46180340304002c510422800510b403025000014901c07c959103902c0101940c40b10010421804004103000c80d8500c02d01d658807a1104d50b02401c154911001d60350002411940408000d60126060801554405502401c8183e22480660003005229103100001c0c044500342d650360001c25855005d00000d0324031440030b821041d1703803000100c03030302d0b0801c0e807419882d0b034110b8021808450103d1000603010030b8009501402040d014011f030440754102440c0c021011192040c0c5800d03d62201e20f20000d03000e0410660781708405043c001a11a03007408400c14180d0400e50006000c2d02c1c00c0d80c240004103956400068200c0402d00304a1402d119a1501d2aa040114100a0828040480c000405081503040321000120981c1c886020a0301d86025000c0504010000382d0400101c008011402d070140f91000d030090300075014691020341c4d078552024103a2202401000380e4007402c0c030440903940c00000c10441c0c50030480e842070800355 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 568386573 1250 568385323 568385333
    0x5040611030c06011809051b01020105061503160e1c051e07050409030e060a091a160f0c0f031115190518060412141b090411030a0f03090801020403 65
    0x20f06008180764507040c00d040030b40600b5582e10104050394003030250385c00724003000a9210f00150b84403800b40035509000000c2c956140c6900744480e10781401c04100d0443d03d03080300c0c1c0005201190605005d0000514000b0711035961480f580c1c0f148a0403a107000e414030501e1400710b06103560034a1116a00c11342a00300f040151011500c0c2041c1e41040e50000348541aa050450340341e602c544503650003460019070b04110b5980310509201f5103c0b0140b144485040c0c8002090351840348149029456001c45850000a907147c50005007860280b43d241c0c0509031104103905003056540d20071554201904610440d1741031189001c0709000e54010390904110b0311510806000041150440801c200050740c0c030601410610003440080000d4885901c958868120603c1940d01c001c0c1034a80300310302c010510030340d1400511260201c444000003103000702007200384254042c000c3c1c400c880085403c882c0e40007130f071002c100e09001c0c0c50250b03050941c0514641005004e054a82d0003140b1182d004200500100b6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 568387823 1250 568386573 568386583
    0x706051e1603051914090c19050409030e03120a17070e1201150e01061d010905131b030212011406040b1b0708101503020a03080c03040801090305040611030c 69
    0x1d81c40c2c1404202c41d6900d00d0740c0c502992100f00c19100342032901e201e010810441d0351081d44203442100854580074124010000c04503084c405880099105a10030301030b41c10141c00c080411480b038241840b800b00114006410128200c996a41d214000b19844504a6100d00c04041114004e10403a0b42403c5c140d000420001403503190600845030280201010b4001354450b50740c1882012103006078580fa1400085211000c4c41650001240301240c00c584070710064400d001018140c49018145281a041c4003500b03200d0b040200c0f450b603a070341d580402191240c4242c1104d4059540c010799440c03008401c541c000f28103030400201000d6541041c5099140d850403101514002c11010317403034440b0044800740201c1000d051600c0c034060118000ba60b0100001c0c0d11240940341181884642c01040c2410040c0b5058800039600c040c60701c00400c0440d0001004149280d44c080075281b80a8a56500b5030a564603001c080740021b1001030200901c551105085041ca440400038500d01042000400e60303031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 568389073 1250 568387823 568387861
    0x30905060106030b13230702240912030901020409140903160c1d0108060106030b0604050f0402070519050d090b0d0522141203100b03060102030f0706051e 68
    0x203d070b942c135060800c0740c1d1040d0401281c8891720b03100707003c5a0820003400c080c00783d400c400c2c01202d202110100c1e82990000c9031240494010005000b140c41c81003080325400341c400391640040d4040d0000d205100000c130001941701c1c00482002580d40ca14105a04e8102c0c1c00560810000300307842010320103102c01c080b08a030260380c60354001c2059801c00741842c10b910541c0d548019202200350a4051180114040641c101c0707081405440305682d842c8410780988030410580c40d071040003040188181e18140d1105080c03884060001400c11b800c86e0f981c07a1624807000103048640004480c1082040070400001340703252010320300f80748014684480c5005500032800b0110300c071512000094401c110080c0d01c1586d2010b102d5070440d42844034100030351004c0306221422228080e04440c4110211041c04a078012080048030035489460f04000103000c0e0406442d860450008120300c801d040701c61005007607018007508001a807810030f03407020325240c2c504503102e5030562191001c0282059030788030031100e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 568390323 1250 568389073 568389077
    0x8070b04030804090c2d0215070c03050d06080601060c0c050f0f0f040902040c0c05100b15030c0d06181b050d0b130e010203040209011220030a050f0319030905060106 73
    0x1c1c85008039020f5880e444d221b610750b0007000741741100e0740115007650504406000b054098491036805000c9141400000301c0e910b001043e1111405000244140b00a21101c070040e18000344036600c07540f4035070810900b0781c04071000a4200c0c4d04001407106d03004551000700f01c115010200d01c103000d00861504a200b0310342750b00c80e5203d084640b04640791504498903045d4000c00070401c0542101c0082d202680c0c40005481901c6950800d80f9480418404c0c000d0620303008150211004100b181201e0316030004004900320750051002c02841c20641c041c0704060058000301e28000c00425543c1800c9030804105a5034280d91542d201900070340010448080040307102e0003080d031000490104034903280d400701107424185000c6182c5a030b114198081c5000c1c03807003250a0707421a40e035004200b40074000c613080a014280018245001c0200081c40901e100c03402600b0341d260301003a44c4030b8500f400b4842d04000b41c1354000203034040303e44903401d42120320044503040800c88040e060701c6980d5203400c14020401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 568391573 1250 568390323 568390331
    0x206100806060405041b0f06170c0706091e03050403121e030e1f0902090f0c0d020904060e13030306050a0f0311060f0c0319080f0a0519020a030608070b0403080409 72
    0x1407102e502801c0e003101104c0f0425401c6d0a036501d041e4103000420388100c400141003061607006242c503c1d101035000b0380c00d4251403401c284454468200600d8220303402c5030942c0c0c0e01d11100c4451405441c1c6040071074003e448050b1502e2860401a0014070a8451041004803600c107518815002c010310302c0300b011661070005202c101109549213040324001210724045c4032961713013a00c20881ea0700224543c82c07084d19600c1864441e00403000c0072103029908198040c40a000000c8142102c9d4091703d821000100301055031550380d64181400941910405100504046604185a00350240310010401a107500a1051030405100700b001c2683c04018407410301e088104103541d540106440404440c0754480d41c0e901d034002c4d5020756940c8003502604a48800c01e2000028a000d42c124501c102d01003102d003001035075000304000007000010113400560003414441d80d08010181301814100c01d150b1400158541440240c41c940f00c282d0780300305800c420030841400080e2140c0b090b101101e525240110f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 568392823 1250 568391573 568391581
    0x209010315050a1823031c0b0a0e18011e0506030f24091e070608090601121b030818010806030a0309030b07020316030c0b0703090507050f0117090d0206100806060405 73
    0x544000b60384e0017112941c8808503031000c0c1d1600143d024002a44182070412007142a14103000020580380310f408482e4884000051035910440c50103e80440514000100055000348001110108445448030f0b42c0ea41c0c010007400e401d0400c50510300c0c0820b40018100c0382c07003086003810940200158035811005d40d0740414180c407404c001a604d2001d40084041804c50316215090380c0d1305191240d0000030380c0703200214681c3d07180418040d059402214255004042a84039082403004001404000c41c803a031a00002040c0884040d001100c1d07000d16540c610b25000000408900000d02114400e4210041c01800a43c00000203c22650b1001498113a581c40c044140d007180540040c01c1040e9403501400340405501460100d5074071710131440e4849030748032403104504641c4113500042c81a484100c00380002e282c075814005c68000e05241c203640c0b0110307200e50440b1070803065843c54829400400100c03803240d0148400742c6d200c820344001249041c64401700c0d544c2c0304005003985004640e120081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 568394073 1250 568392823 568392863
    0x60c02010915050702031c120b060903100b04060807080d0818030d020a1e09050609040f14102c1b03100609050402070206031f030209010315050a18 65
    0x4074010008116100c290714a07182020b44507902c0030000324032a0294140390941461000300a07031101000d9603034981e02c004114290741c0104030941205038003050500c64113106590070000c03590b602d01110b1012808030300c0710042c80256201e98000000c1030700003243c1404800c0001030103690700605480d0144081c0c5800c20340004401d0301800c10406030000251350300c140545900100343d920380b21b50710340c48440300001d20768890681490480000543c44441044170303180110180250300c400400009440c440c11038201c044443d129007003626a80e0030401c001c0001841c2592500512980c0904442245401c0c00082c810202c100c4448040c3c2c4968003040d01006481e20f241520350300018855a242041011000206658420f850010b100044003040354201802921010380e03002e4011400c6894110000503038440a80080380140007420001016a0f946881c4070b00943c02806004080c2c09002082d200f5030740d00034120040d050400c1c00c80071940c24a8200d03007050300c0c0c0080200b13000b20302050381 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 568395323 1250 568394073 568394087
    0x111040506071b05130203100e07020a150b1017061c0f06020423030f0304080714130603030f170f07030905250f08070312270e0f10080304060c0201 65
    0x1308982020084203080310200c020750081d4043c000c404402c1c0001d503981c03140b001441504452600060b08040c0036080041c070542c0c901321102100020102e00355020001203805420021002c0000230400c0d0388440445803403000d007a0300410103031040301c688400d10f50b90f18882885002c00a02220031109031800b40b00c0180e05071005450030190a48504070f565030318410030f040a2001c90310900503060764502d4071400000310380481c0c80000213003c1d0b080c90b00c9282000866914403098000210420345281c0f0004d600c83c1c10042e42c4240c64080c00e2501c100c1d03000303003448114404010320340a800c2c2170003100c840380b204050307001605160100b030745a810710301039041024016a4043c00d2900d4100340c0b0b20025001460700a4400c83e402c064900b6a4844120b40e41e50f0003440050848004000007580c090310900311100d520300300b5403402c4801ca8074094400c00c1000c40c2d600841c6001c0c2d8a800340507100d0090144250000b00c803042842409003030110040d100d00c200c0c0b141c0424030940101c9003045900803c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 568396573 1250 568395323 568395329
    0xd0609020a0906090f0504021e0d1a040302150c07020f04140406020c12070f0b060a030f200f2808100e0c060703020c061c0507030c020111040506071b 66
    0x1080e044070a41d034840d2840038204034000c4d01d000d281814011925000786229441c4a070780c000744190103410050144003401c0e84440e403450340000c1582c0b5141d01003106c80300d022100320020a1601c00c0c80c901340c10024184401d00754140f016401078401d00030045041070591781c21030b404071003100b10303850000c00003030091200b03400c1c810076408107200700014001e499020b0140380f124201580c070940c0d5100c5103a0050300c1031400082644900c40c50450118040c1c102c402d80c4040064207001207980c44c1e455212441054607000c8800302c1d4841c00038030380c4080c002c0c0c51082c0d0a03800d41e480011209040002030080e8606132544140301e070304001c610203070700d00608000700400980c816549411140c80e03030a40603000d41c40c1e030040035106100011581d802c1090849482130740590252080c190300904004407a446048500c101d43c4182e41c085100ba080d900ca494080d00c007544000070301260480703000e0309450144240b803408040c14007080009442c0c1c4d41c100c507565640458280b40e80c520142e20015664070b290 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 568397823 1250 568396573 568396579
    0x220305130e180d090605030c0f0403150204090b0d021e010210091401110310060807030f050108010902010206070302030712020304021f0f030e0604080a0c2a1d0903090d060902 77
    0x3051110b051002803240040400c200d040e20b40e405107044041c1e40d070790054400d11001801c00c02c000341c0c00c03003100300240c4030005040a044e45060754986541403140700310f8042801042c0c0c001410861410540718114001c2029503410004803416000181080080e95000304080e542c440b000b030300c907072090045451a440d008000c100d00b50040c107140a0780503c10040762202c1d840c01c10f040c081160080c0550b482440f98240c0404041d04001c4101c6480030007603d4601416150003808070780e00e10a0140381d02a12040d400003030081c40c5800028607240001c1c101d0000d041c410014801c205501205800003d4580ca60160707580c3c0f1180701090341c204072190b40d4031401501e00d441d0344110313038071a000c0c92002003d0303542403200c142649809503e800080d034005209404c03c11440d0b5000c4d0180c81c0d04165580034400706002214035507112540040c0c030450044403204500014811445416490880c00c070301e4813003034401498810541c80d0b0768810b00036043d210b019003c0f9503008102c015084541215400303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 568399073 1250 568397823 568397849
    0x14070309021f0302120612030406050d230402040b0f0f0d031e110f01141302040b18061201090b182802040e010504051b031509030a0822030513 63
    0x10b0071004000b5006848160120010800480c0345890300c880041c0c40b075040701c0c020b58902480c0c401b098555611045880c0845a200e140b50007004401c02ca40c40701113610071480701d030240340c10700c10041142c045008662160075003e03100310782e50700c4100881d40125810b680e100c0d070580480c03c080c0d90150351a800081024080c1145244081d8042004181302d9411000c54141004080c034503801e13500200d4412080c0c202030000a030301903941c040c031200d46e82e0004d44006010b0311500c001c60080e0841050b03c83c4007481802c280440c80c02c0c818988508000c9450003000710100a42c1c0710f41c0407100c068615100b01030143c2c0b000003840e10a005d06915000c0994070040d0008800c8004041c10b031000100707a116600d020b04400d403044060260350710595002014107525a10780d1103c4006100182c0040e815108d980c1c0780c0c0085da44418130080c0210031500007191101c441120041001d04014001000105a400300d00d607880d101c405276134001a894181584c8803104c40440614101503036024248801d15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 568400323 1250 568399073 568399129
    0x102150610031116030e010804051218040f151e0b09220e120408030904050901020c010e070302090c0909040b0903090409030f0215060102030d09060902030a0c181407030902 76
    0xc104e01c51819210b42c50303240b00c12180400541b05240126800b1704141c0041000401c0303c50040b000f0601c1150740132030680000040310101c0c003261840c1c0054008642e8800104c021103070901745403070003003140700310721041c000d0110031000340741000c0c0c8078041c840b41e4040f582c0e2031155111040345808605001c0c091130713441e50106000f0041d00e105603415441e070046200c617541c0303501c1d06011034080d244250000d40c40c10042400784001804020b1034044155802c0c030843c3e420102c28010b022001d0300d900d0003030840c9030031801001448800904905107c800801c1450001e458110445038465085003901026503151030040d8110b1090721086d40d400361900d200201015001008402e0aa5003682140d030060300a61056595080503110540540d2050242022003481600f2801855200d081c000c55980c2c41540820300d80074503108111641010303001c042c0035031101c0d00302c40b048a030041d00d020701459200882114000a018200a0400da2540104030540d20ba00d000c080f40084e0480d004c440c5186 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 568401573 1250 568400323 568400347
    0x40e030307031109181f090b03060a181b05030a08070b16081306110d0209030f0606060306012f01020913090803010905101505130501021506100311 65
    0x80100c44000101e49010f09114041418009a07030000350b018040320940c80544803c0141040001c0070412160a86100000021a5000000010708540030040703510085c101c201030400340c000b00300ca042580b4064100c0286150300b11104213150f00084c5400c00c080402d055000c03061910b03000f660b018440d11010307901300440e0030000c00d0070310701172801807126407200e1003154025440503801a00254280001c1400440c054a000807028400c08001039410f0701215164815000251584c400e035501065100690905100605880590101a15251074840000713449408040c103094100040c0300c4051a18040c1c1116003402c0c988110050b03825941c00e034010902070f50002400c030b4010068400d0207000780f181d41c003c83c0001b0b5400a10142103a08184a403001000024500139040d20b9000000580d5803804442c002c04c107100f940c920b65190071400740240f802030564440d604540c00343c0f060348044081d006030b107038001c9000c44034008200b49a000440140a0522045044010008500c04080303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 568402823 1250 568401573 568401577
    0x60b0613060f0e0105090a0e131b050312040f0e060105091315171b030a0b04030e030601141018051e090a09030212070201180b0309060c160311030702040e03 69
    0x42d441d82c81c440c000ea10034004440b1401088407042c0c018079103203030500c2443c0c03801a4007513000000c03104804103200e490310f90080c404003a42c5050503a03185014140070303500f402c0c85050391000001d1062441c01d071a0180808014a10303204811812988402284450b0b04c21400c4909262004001c1c04501003004800c0e80180307522903145550020264002810405115070812030007260306c042d000e44c0341114910f4418581081c0929854000d501c4580c001509004520f40643e000f5030701c4014200c01c4c6414541b8000b0180c0003016280040340d0044210f95a000c03004800070702c9460444240c4500c40001145280590001d40c0e11241e142014404040240c14512480342c0031101141c02e601c500080e0340440395002c070003400580181d481040d41c1c0c0c0c1141c000b450305c1441850046041c4207203144100c804a96504050640780e0008107010070b0401c1080303850f82144500503001c0c50070904c3d0a2405801490039001414040c44044025070300c1c0f0144291800c0c07a170054001c1c80302101000c501510783d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 568404073 1250 568402823 568402847
    0xc050d080d0c2303060f010f02030405011b0501141f260709020d2301030305040b0f0c072c061c081c090201170105060405041a1003020a170f04060b061306 68
    0xd56214500c8601c6e5600c038440d80906013910350080c42c50641410b00440b84614a0000070f842c402d04032107c2d2000503402d200307481710902d08003030140180c00d203945c000ba020b10700c00c100754000301485c0805002c0c0b50382401d1282124210320404641d12100e9564030f40c01d00d051540464607c61002c100c50b0215030761a001044010142500d000c526148190705221b240300030700026001a07020710043c0720a8000d4001890b02e41c60054249040c201c04600301442d00426411910502e000e5422045804030031090482c40d10145020703c1c2d046113440b8011800c01607c8211104924114800c0e040c24021000111502d0035000310706a02d24190701d8078110090042e01c0002c9002601d102d00e0740c0341c602551200b0078140c03000104242d01d083d02e041c040001508210403499084191511003400782e5507940d010b283c81440e103460140e02c0c4e5600c0003000d0702000d41007010006109a00007005251648070550580c025030003c0d0000e42c542c1500c020842c41d0007030240d0b031950080c4540d070102d0400d400c14464008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 568405323 1250 568404073 568404079
    0x20a03200301020f0a0e0a03080a090501080a020a0f030f1d480f0d0b04021c031b0c030206030406020d05010b2814160c050d080d0c230306 61
    0x1a003203050051500302d00c00e10602e418440300a002250b925071043c90803000c90035000f020300a05070384a80364041d0a921403001e10000c510340510801c02560041351440e44200c02c5001141003d0740d896001e0b04805854840c0c40c1050b80c1c031080020640810381c030402c82c1e4010070040401c2d64481010f69503071040d6800302000f841100011004100d05c0111001e42592107840f0b114981c4a0980c40882000c41d40c160b8950703121031310881801042c0c40340d488038103205004e440c01100a04060041c8101c0700c0996802540c2c0c16052882903000c81d40000d440d20300c50000c0800301c461b60105080420f403400003074000940c081400810b01c01030002a402501c00880308a00030070680e641e42c020355080340300e20711448480b01541c038a000d400320b81c80d0980e0344101d0b1032800c0c030f45c41d0904031403001d41c2690b00a403868040c401c88070f19400b042c004210744440c0170340b4042e03030411103d100c80d0310785500601510780031005094070340703140b4402680325030f00020042d505089002004162002c9a41c5240c100300c3e03400e80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 568406573 1250 568405323 568405373
    0x130e010204081e0309010c0305030703110a2006100e09030c01062c040f06020d0e030310080111120609150409030e01021b060d020a0302040f0801020c0706030e0622020a03 75
    0x8003c0801000b00e881e550016103801d001c0c101c4503a410307500c41d003005144500707150343ca1850b4400c9110420090980820f5541c840b02c001c40d80e81035071200307060042510302c101d52101040100701100e04180c14160740d404455080c881e41c2d130000c03141c510312a00540d200c480d400c20100080c4200000428042c7c1911111035950142c00e99420020b6000100c4000d80304050748240440410a00c0d40201000000c00a0100c2c103840d01e1034426107564000d46100c2e11500d01d400c820010f0308001c2c4200d40c1c080c40c030018982c0c07130000403000040c0b050300041c02e014445d00700c040101e1601e4a103020725a07031a440250040c007140e007171b90801800303400d1040c00c40c03030140c0680d40403580c840701c810104002110004181d24101005105080006c1d0810790552013410350070030010813101fa11207a00d00080035208009641d88083c101c41d2814030b12154000b205150400d0b00014603100041062640120010803034065800c040340e020400a0300700c40041e4000a0059007c001d000c0140356032115000300ca84100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 568407823 1250 568406573 568406623
    0x114100b03060109090203150901030507420203070f0308040b0c0a0816090e0103050604122a111f02011802090103020906060c0f101802030309130e01020408 69
    0x48031a01c0215080760010b01d0711041841415499406160000f42c620607001a07401980d002c1000c00400303030000d8032294814031040001004200e1217544035403900c540011382c2944000c0d40891110742c030500050300100c440721481e10910030003d42e06110b8001040d0094180581005080403000b644e06a441c2080f5500090f880c280751021074500c040c06503101e900355541e0300c1c02d6241d603440e8041c001c001c03c24203541c0004c141044608082c0a140510042e194070b04062078118410b080f0102d4000c203004000301c6034040d00f4940c1e04140341e281044402d01d0b13090456890803580d05a884c0074059408a01c0c3c560000c45030a507482d041d030a8101d41d40082010980301402d00c25418441076000791700c5641040148014100b00d524a90881c0c40648030600300760407330310074608140b04424952400e9003d05c12041d0103051600590000a40d00c0c0400d001001c01790700842d440b803145a02e000d02070302844480c0c84900203a035201941c624034686c0215100c07605d40000760b071980d94010240407400000000c0c0c0d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 568409073 1250 568407823 568407839
    0xa1b0f05090915040c053a02030703060905010b041b031a13020d06210521040b0a020708011a0a23130b04021902160e0621011410 57
    0x145004038501401003c038040304151407aa4448001c0003100d40840e4850700003403a03240c0c481104090701e88242403025030326405039015020b0804a82e42021040800e401070050f032000700e140802d490700050046000c01d06410f240d4013508e00b94182d1600a8903141c00e80b0320340c0d81148000a20380140d9582444004203456098100b400c1034100d29611421003111204050b405a0041c40d0070810008082000c0d983c2d102070b1200b4000f0003806144c1e000079010140c003000800d0020711030009850341c0043e01d1808041554516000ba03010f5499071040010b112540341e0700800c55140100f01103002402000020709a038404c0c140540384590007419418004105200ba90003480c100418507004044168191010000341001d0a42000034481e0f56103206c0b502615540010f0409840d0111001340305044040000d281860300a06108031816421040c0013800485900c2500030400300c80e2006880355507101c5094030b60740d0007000c4c0860b40c0ba21104001100c84288014841c0c401c5d008000c0f4959602c0b044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 568410323 1250 568409073 568409089
    0x50304051f08090f1002090307030204061214120711120d02070609080a0206191202130f080d0c020909100e1b01090e0f0403120c030504060b030106060c020609030a1b0f05 75
    0x1c40700382e00201c04160085d400d5601501102c040103084814250b0340c0c1c0c001c9002ca5120341c00401444d0010100b10b81840880c3c41000c20128880d0014244c1c3d00c10500c2c1e003919401224801015511910000003040d13803001100c420641c10300060310001c01c0c0b04a40a50349101c1d900c01d203004640e41450005211401080fa003055a801805051410000000900b0400400320601044c0311000c15421030407280c500c00b619000a500c00c3e940a014188040c045d171000040d80240d0140d80121500780c0b05035807040d840c2581c540c1c159400d02498a40e07616030341c14144ca0b0301b80152503e1418030020301d15500082c0802d03050350f442c50a080380e41c40c05001114102c080c0c3c041c031410071000f030b400700d1806802e0242042d40716020349041000705007451201d5090368041150703c0002078a0380107100130b0104510498200c82d404500803c107062804c900541240280000039125000215194510780c4090004450107540a11041c030214698103900c010b180703181c05001d94400a01401060310b00300403003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 568411573 1250 568410323 568410343
    0x15040513050718050a12031404120c2c0a020f070c1a040b04060f0c0f03050304120302090f060306030f06040b071707140a020c040f0212090604020f0d050304051f0809 73
    0x31100400d402c0c11100a0705030606c0c04114200010110380140b1805000b001d4400f401244580c0c2180018506250b607129507281c0000101e070190310038860381c2c01130038004010344031405000445507944401d04507009001e9000320383c00b41d54001030003604119106582206a84c9030b03a030030884e4103005180403e654061405003401e002020170041c8085401250350380c0c4023906030300c0d0940304611036584080104900c0041140030030004001e000411483c2c1d40c401000804929045080c14030940c0018800c2c01440c0380d80f405000300002151854030309210b140e2041680c01d080710b819040500d04044003140031541180080c1002501c50882c0c800041f485018012a0b9502080840907902c080160790000100000358441d01d0444c4407140c90b81c1c002c210f00051910401614bc06420083d2010400700078118042c0341c02640420005940322059001d40d010191000c54505c0014a4010700d180300c0c507080154010158000d24a914049801c0021420140c0c1d459038010340b1504095079882d14010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 568412823 1250 568411573 568411579
    0x105010905010b1c110a0903030305090d020304061b0b0f01150e030d11100f050118180b060a090e061503010507080408160803011e05090408091504051305071805 71
    0x4004e00791201510308456031024095400070310140043c041c3c0700190322042c003103008a032408400f00180364045c4140e070341c000c920740050481a2403000c1e000f51688124010b010502508104000c0680d00540500c40c280c4d81c461001e4115042c80c1c140b00341c50620920450f01080e0514001102441c460010b001e440d90000e001400380840605040d01c0d03084009109400c3ca204030300050020f200071303010f500e128100d104000205541405640401c100d8003074050111242082e0b425039402040c1d4006041058000884010390745a00c4001001a40c16900c0198030605101440801003004030307440340251301c007000885014042c2d600349070990b2811107103400451594000030b00401d406400400380d01c0404441d2a02c00c60203590307424520f4100303030000c1e54800045240b00d001008944030000c05460b0480b24900945010b5030b0f110000c0c0318195696019a00d0a030500440c00d842c001a02c0161000a00000c8401361f048500c0004010403a500c03000248201e41b084550a096000f03901514009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 568414073 1250 568412823 568412827
    0x106120c03060b0f0d03031a060705060a0c0c150e0127110609030a0c05101815020a0f0602030f0a15050f0609030604080406020d0e0a0330030204080105010905010b 72
    0x5441e0b00000b45614607003150848150309a2007420384d40c2629001d10b003846610005040c91243c480401d80020b140304c5580100801c204da034001c5080000c4240d400f111006002c910703030550343c4045884000c10360005115034559000c40c5c144d201ea07074004e984a107980000802a080d0710241c000c0e5003044005400f00900e40110100d400304440341a803a18010014140e1894407035008042440c4c96000034040d2600c2806e408140101d107041d1111001d600c2c0a4681f9600d4481c0c000207c5d2450f0040303100d170202590741180c0032088070780280086201240c02c444101c400181505089000c2d500841d17903107200c0c0e0840030005107107403440d20403500c2075105800203180450911040c08410a4910f4441d079110030144007110056030f040104500c5948111006031700c891038860040d00d080c1d600c084071801d020001300003021035201d4200c030004903900000d5500c0c401c08001d10765010442550b10400b04040c2c481c9400c107105070141c008200f211200310081040daa0707a545040c00b120000e01601d8000d25003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 568415323 1250 568414073 568414079
    0x12060109052d0603010801060501170609071d061c0c0c08030a0902040e030714100614090c07060e061605070b040201051309090f02040b010e010210021b01060f080106120c 75
    0x248608110200510803822403014080b0340054aa03410036440f07100240c0d101e40060100e542e01051000b64100c1c0100d44003090b0600d240020303803101004140c682000504200b080016a1129000b58010030152640d50f0f80e5028400c8101c5650700b014a10b1b40141c148402c1c00602c51044100d40300e040d400481721405e43c0c6030051a007019261055099074880c1d110030808006240600040500c0c034031800c0c20030328600740d9800450401410708180034131b5514156082161550303007031000c1d11345001190032131000c0e40c8403031f01d0440303902030060040c0c075052508000e445040340c000b4500380903201507078200200414100c011200e0307126002c4000c203140064404100154020b07809496410700042c072a071503d82e1282e65440031503a001e5810b41c0d60703844000e51802941000c2c454500c090000b071030115091480000041d5982c0c400d80c0e8135448059002441c00c0c4041128864401c07002c020000900c52507a4600e8480000c900b1400752507840d51a010000541e0400c510414039419032161081b00d01e030346 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 568416573 1250 568415323 568415359
    0x60e060f0f090c03030c0106082a0d0f080c06090c0406260312040b041a15010c110a170d020d27030f03081503070b0702040e12070302031206010905 65
    0x802400300102c030321607000e420715255802d102915048901d4400002c1091800034810300e0420152000f1002030601200e0b005003e06100d00300d03003600001d8520269014241c90480040d0111510117003a802011034185400c7c1c6001c95498010110300b422145d09550a40800048441d28800e0380c0f91200e6418070000c2402903611281c0f801da96071003d490401500c1040c091280c1d9080381c08951458030102000104000303203000c43e46070b05290f8440341c1c60340f030041725000d80c41303c04040007814000740350840410810b0005941d14101c00c0986030070122380d900c0d603010180e50200d1400ca40e0354011102d00c003000354800140c90b07041ca01140c0c1c651400f4680590340e41d00841c04074056084218610030040041030310f59103031a1b9102d210b540e40d1030007498060720b0300d802100e074084142d100ba04011010081e020344401550345442d0100c0d000200c04404800307072450814504503450000001003030384024943c012011301000c01600081851940d5510011601c40f0160300600d0ba0102da00802249010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 568417823 1250 568416573 568416601
    0x120309010c0f05120d05100605030f060406091104030302010506060712050a020a1727130b030a0b04061b030b0105031b0903010f1e020720010519020a060e060f 70
    0x902800c5880b108148a8031000d00b0038041125081c6098400560912922814450035901c0501c0250040301642010f2008020340b1018040850700e02c0e01d200070039099134455000340020003440d0010080d03401c10b20003d00b19600580f00640240d4a03000000d10681420400c035040b8580c050001d0040341304103101581c050300b120302c0b0901140310300002c600000c2c000c80000c1c044681c2d02c02203940c661200f030103da104890020b48403800f154209102d18104d440c0c6d025185015401e07541e010520107441ca000c203240481d032600246c00c0100440910051000135446116108160009031030700c040c00410a5080d0750303454240900080c0d040000034072030301d82c040300700781408440030a05151076040b4000a082d00c00d207081a0840c540d40300c000c003030301031501081c0050507800c200043d0308111281d19105100601001e145110f01128640c410032a84200100c0740c41d6620542c6191100d600c4210080d95250051011903d0625200b0b0761000390a00089070342c07241840403400340d030b655a4420300c3c14100e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 568419073 1250 568417823 568417847
    0x100e01210311060708010f09020a0906050c10060b0306091006020322092301060f080a0903050c03070602091809031605120a0c0506010909051c0e0901090c080612030901 74
    0x1082e0308010b4610501032040c58050340136070b0340b0402d040d4140b5840a90b51240c0d5441414094410806851019003261200049545605125440340c214807a424100040c00320342c4428549442d0010900d45a042d0245004d100c1c2540c0c070401030303a100745054800425500840c400750340144000184035443e880711200980801032842284c0c2d6030380c5000000e851000001c11480410080141641c40c0c1031a1011b00414072490516005401d40130040c10765000640045034031520345030904d003414000c00031204080c0b0200200c90b6034009504110000b900b03e005000d1048041409150107901c401c0303181c0d4054148130014504d040b29800552188009625040700c4600691121080d9251100702510409a103a00c4480f442802d6203086820140d05800100846292640950204200040250b1003071103440c003900c0c0880210505503044800e2103070946d8021000c000101c0d040c0487c1c4c02c0b143e55011982c907901595103504017089544000c080c0d41c2a00d560050007100f0556110740c0c0384400e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 568420323 1250 568419073 568419077
    0x4050a18020d020a0c061413030503040f140d090b0a0801060e0f030f0114010e0903070803090f06151801031515050d030315060f0c080a03020d0f05100e012103 70
    0xa040300400440c0280d802c005821303008100000050000c1c40500e02414040f03c002c0707480c03070400d490451030030010084408805810890044006000c204004e0100200c00da003146052102d2a0801c6d00079540b55002d90100300081c1103080d000039449140d01c1914030100c41ca4860200aa09003202164451090300040e0381c80054440d400c489500c0c14003460311100d4014002058011004017110068401a40085181c080c5c0400700220590f0210a88505a0740020042ea03281c5610070180e290090f80c6c00c40000700c0c003e40c0c050000c0f401c01352f03909100f85e80d000d41c1d20300703c402c01070344218009040c240f001504160707960542002008050b03000170008844841e002c5580e0b502c0e1000700b2403d203078000c1c0c22408243d4401c0c201c0040025041044010250361500404510508000501d03048800324004c000140104d0034000a0b402501920030703880b200d51040024140703d00c007410103040d0503225020070703003148080840e400720b450030401c1c1610f4084401000b050070460040d0040c0e426018241c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 568421573 1250 568420323 568420327
    0x606060a030b04090b011a0c0c1002070905010b070303061d04020111030f0f07110a03051b0a03140709050109111204030509060304050d0f08040b0403110309060d060e070504050a1802 80
    0x140c199214403036116105d0099031101006e41c18028038002c5540e80c070172101d071003100900918444210000d0710303400381c0c02d040d1124440e20440c007800b40d18041e10782e002069000c0c2080d0012440e0b0031810701030185140607540901c5a203981c0c03100c00c4002c0d0340c00018580c050049800203130155000b003401c040700d491030750304880c03600102c41c1d0b0641050300921b070418040040090003105200f2100d03144582c6103002c64004084505d19071700d48d40d8903015504c40f484120a4010781500700e50781c8484c180c1c015038000b40940841030f14030f1030998030340610b8000d4940390b510f13041c0081406e409500c11075621080c0000340754a0043c2c02c0c212003d2442c802001181000010041c042c0315842e0b502c06140164030520003040c0046038481c010307021205043c43c0c0010880b040b4200b1000c101d1305692507401580604021412403800e0b200d050071445049102038201000040c06c403401d08140d0b104200311460940000d0f0036840310401220f05200318400c2561260504000b40456a148440e2188140c01f800b0014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 568422823 1250 568421573 568421591
    0xe0102100e060105130e060a0e010603080409050a06230d1707080a0305010b0a090e0709080607120b030606010c1b120305040315051018090b090a020a0801020a020606060a03 76
    0x14241c403a603035a404641d401640c0104180c0c03c1c143c007150312104110400380090807040103c170360344441c010f00d00410b0076251500400701d603a081d40018003035900920082d80d503076280d010170006001c05548100050b443e00c000040c46c40c4005032031002014035580d4a40ca028510340400c055002d080c0d8064410012000120802002007001400103d00c1011116121414094058202c0e14142c2c00310190035004c00c02c02c00860707444082c040c25142020341c0da07a06034844000c215058919034100e65a2403040c441400b503040c2c0c1048c00f182c9203034903413601800005503c02c00c0c540c40da041078440724003040c2c5010b00b050000c0c8600d403000e02c40d002e0b80e1003018421561526164481a04904190089040006c00748103210640b4229001c0342000b030001d2000c5d05001071104a200c1e00c0f48940e41401c080500b44020b5080a40c0140040541100c42c002041c10001880c944071484500101c1c8200108280080c40840600a903501480150080d000b1642d0b0802032200c6548410024402c144c0c1d248165 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 568424073 1250 568422823 568422853
    0x20c04020f121e100f03021002030c010c0306050f0604031104022101030f03030e0a031403070504270506091510120e0c2719060b211003120e0102 64
    0x1140306588100741e4905603c0d403041205000c20700502040701d0340c09034103014004498000358540407240e040c0c4628020842c00031003281103000303007007104600d5401d1410034402c66500d0b42103d0151002280c42d03620740104101084254032440c8001400b043d5111030008003480c10b80d02600300b562a01a40d11000e403044165481e81c06400d804c201c44010f412094002459858414202c00201c8440100045860f50302c01500a8044078100ca91156000000a5801b0b11a000752401013503150066007186500390507101b03980880d9051415030903d06000902d031460119851805280c1c3c250191800c201800705001c10300100720352040520074110340901844009115050b401503040d005004100309903010004410350303105208801d88203120700c640c1100d00d90400e4540010190100d11001841682902e01030020b03523206e034034462000301c2d401d510032440b082c00a44132002a00720716850f60b03c02400b01c0511801d4000a46141d44621026404901803030698040c40814011211040350840003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 568425323 1250 568424073 568424107
    0x6120207050f0a0b07031505010512070905030f010b180606043807030f02120414030f121e120c2208071404020c1207110306131e03020c04020f 63
    0x202c892010301390401500329814403404000c0010b000b031044480d49032000080c407034020320401e14100020076010900e024021103490004000203800d40307244800c50080e4500130240d10f0405801001c80680040c88814810708952003100000c21050515091003031104030103201400c05a02e54009204c095104503120018121024400401595900d0f0344e180043c00300e808000b00b402590302c001d103021045450141520144c80e105125034949001c9603002903d044216002100940034130043d10b0003040701c5000600c440504003a051400f801c0c09500c02c03030903104030f050319501d200d003020102d00b800c1440c400800818a0990380001c403030340c1c1c0812703145004096034080c401c5640708074010054030808906c1d40c1e0040380129011820300c0c0740c00103a243c8a043c00f100b01c81100380006030a05c100170000210040b100800740488100c0e1614b20310112010101d10740644040b0610004025030781484803032589025407540c090001c0082d007105100c065046807060011041060080b14440c00f101d0305 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 568426573 1250 568425323 568425343
    0x14010b0f071a010503010b0102010e1b010c1b03120e06120415141b1309150906090227030a02060a0903020405041218031a060a081606021606120207050f 67
    0x48002c5203501d48010982140c0d41c0f030000d203041d641040b40e1020809804600e08090f0307241e00340280328030003040004a0302e02d46041ea0042450000108411094252003680300030740e48038180c50900502c50310340507070b038241052002c0d5500002c2080710f41601d50128041d40e420038429442a011141140c00c2103040e260802c4015009010f0401004583e211300d071851040e141c03182d01420b180030380520302120300b100903000340312a050f241c40c03c40c402c521800b404480200000141000425110500ca1001e5403100e13005490003840140c001c2002c8138642565040b04400800500d0b100186500380259a040f148803101446034508002000d41c55900030248154400e01c52071984240c0680c0162400080c040840140c1446400510003d8403595414140d4510583d2184503079441d4800038501742207a8014120f2405030800c0d4040e498034803461901035400e25025100c0ca24031481001800b015107124000c0069400c032000d80e071160a6500030301c15171380600c0a541e80c4c42e078500011407501c40790403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 568427823 1250 568426573 568426613
    0x301150516050f0d0f1d060f03072c030a140f0102040807080610050d0b0417160c09020a0e0f0f03010c05041a0304170c100606020c090a14010b0f07 65
    0x1014003003400c1018406136803c075415050054118240300300c001d14484400c51a103034484840b1a841091383c0e280c42c10b9074004a990648140d61380f070401e2000304800b0841c041031042d41d40c2250704296001d1405a080011100503005001003104d83e26040380004882c00901c50b1401440d4404081100070300090014003500340042c01c0f5145003112007490f01078004c190791150345008800744040c1ea645c1c0100f404050b089a0405401d454504000d0240d00031052080c285032000280124051079000707200100700d000c4c035549459a5640c07a2a0b000380e1052604000002d00214540c3c43ca91414141d1700751410303400303004031b1400e88806012908603080d072030380c0c032010400c049401c00442001500701c081d19080d02d1175150450510743c1e5200187c2070680c580d0a1007101c040303000510305000b000140d07041840008184007859480e0f0700a91909c804282d041c0c06503040e04002506006180500032014181c3c2150000907841c145a00709641c1110b0014051200b013040403030b000c144d6400710503072055851 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 568429073 1250 568427823 568427833
    0x315060207080f012c0c0913050606120d0318050f0303010e0109060b0702010f050910031a030109020d2402030903030a1406130e0709050408090111060c030115051605 73
    0x424480d901c2d060501d2502442e0b6810242c500e82c0101207107003502c454450400031130003040300b402d20050400041e2061b2030b801898035010411102e480b50038040c0f01030b0142013a90090b44422060020094030303c080c8040c160302c081c0c0044100d512903030201e0141e04840001c1c4101000f180e036560700303115282c44011100d5101200611107460403841280c01007182d0082080300750710f801c9003500d40e0302814402a06100d16045074040050081003202c0c0122001405003105102c4040c0c064024030036030541d07415500020460501c00d04052240c4818a07400030201c080640032950b42000c3d1170750811300803080d0051020060050f0401c1e0019601560300c0001840d12171800580c10000c44c1c1c4816206031440340d001080c02203c0c2c07181c4204c40301d480302180340400c0125032024614030b40b2856911080015182108000034440d50340d01806011000f641c0d481402ca40038034120740d43d5981602c800305031800810040140182c20520805e5052850600c1800e01005031071500d089990003a007a43c40d6045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 568430323 1250 568429073 568429079
    0x1110020405090609011505031512070906090b130b011107060c020f090c0d0504111201061806050a0905060406030f0809040c05040b180d06110d0b030c090a0902010315060207 76
    0x30a0300003d50002050328040c44561501445c020b00300c10a10014003441340000c04034464082c00380e403210118102400c2080484070350708000340d031410b41d17200320f443e2245400b0004c110007400e03026a82c0301c05001003a035125465030548210090240d141241d05114500e032400e64809000e020540041402d6240d0100c28803290062083d500c403400d1501e8801c0740e204003004a98407034141540e40c50090128002a150f5880c40d140d442c0021008085a20680d110120b044294054004405449651484001c1000d00c0d02c100015602c15001c0e4076840b25000d007040c444507040d070f804a544404003d10120b442e079501d4a8900000815500644104000040814003401e242c012100c00c40206d00d0854541803034000700c180c45000b10034012600b24004090381c5100c0d41d59008504085030030907020840b43d5500701c052842c5034043c0c0f200c2c0c42014140680904035290105007135072110b001804651080d95590a150024118940101d06241e59504150560349106c040d00e0045d20040d0000d04156007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 568431573 1250 568430323 568430329
    0x10605040e070608070e011b0c050a180e0307050d0c0c050d030e01030c0206090c01050a110f0105100b0a122c1e0703020609040c051e1207020303040b04020f011110020405 75
    0x10700a05c20030600c01c411546040b20f0340e0204026407ca00001c4500494604d54685100d010005a0003140d012003580301c0842c0514200a0036051090104410000801c0380301c940ca850703004400001d841e070f03084a0b064031600c5020b0500b2103000342c840c42c600001240c403003000800d00390100400354009050f49151340c16075601446601014102070000708624a4460145a0307502d0100207564104107000c0340b1050141e000d00c2884100300403a006030740d07265461403000350003480220750181881c2081ea100046c40c2d4807010488640750705659a05040e40d24030818240504001c990441140311011261407418514102156500d90800d0141c0800380b81400c0000031098491514880794010070030800050b5a81401c0f02d403c40c80554000c2031802d2042e1003943c040c001c0c62500c81c84100342c001160411025030000b8403440c5d42c0120381c2d11a0361a80601240d40340811600246560854404640986099000e001880b041403400001a4a039401202c0c00c0090021050307042580216090000385 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 568432823 1250 568431573 568431587
    0x31805010305040203070911120103050a03200c04021b0a0302071e140d020301150b043615180e01050108030f0a0e0f060c0a05010e0c0d030809010605040e0706 70
    0xd00c1c040c00241401c1c2c000070744680d00c40c81945266036603852125106520801a01d2641c00d42c02c010207065030f5642011a00c0e03000d00c0c1310407030020f00207136294100c1c060200618803a0080c070310000c01010340b03000700344402940855034100100c00c0005056003c850100611580b46100307034007030641d56103401600c40003100c0b03401082110241d8494203001e01c078200400300456180807503c80c6404107160011034010f08050242070401801441e0205415091900500c1212900607000e84517002c050714be880305604070304011100c01ca00c2e00e00480303291030319000601010f507807400480301c0310b540710b5164039044d45800303000b450039845010544a05c4002c0c401c940c01043c02d040a58607011002015078041d1141d01405ca0a01039030788c0d05080107031a8403c142c40c4000001e084540d80b10792561541d036076050408c804440a60070003d0602003520003003010071414201404240300c8100e540c0c0c081c0d03081007000b8444461503596100004007603559000310842104003c000c0c01525050000040c40d034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 568434073 1250 568432823 568432829
    0x206041814010f061409061e18030d08010b0319020c0109061d03041e030b0a14070c021014120c0702100518060706020702121e06010b0a18120318 64
    0x600f112020400584c0000b8101c0c004a034141205a48100900002d0058000c40e203210585107844070980c420607461000500d20403522260813030b88407034030a003055a90010380a42030005001d1000411001e50b040c0042e40c0c0001d5141500d0884c01117040d030803400c0303820881c01c010560703440e81b103d10140b10b098406c03a1041b070301c0500e112401c140200c403103550700d20680c895a440046003400782d401544070001200003650348900d003100c86080c02d01a01001d130024070100203c1e83d000e100070541550107111300341030240d805800d24001c052440d4050b14044141448480000400c0203840000604e02c2c086502c03841c80c40c4482c40c0c54800f0744c010300102c00c0320001101f043c00b40c10804c81c4800882d510308907100002c120354040e82c443d030718a4414013034040c030800203400c4014200400f100020200c0c444a04207050001e204001005220440c0d4440b000c0c8142c2010501c100950b2526501c41d490401954403245030340c104440d9121001d20003034040d4031007a80015440074458410280d61402c0d2802 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 568435323 1250 568434073 568434089
    0xc090a05010f0e0c12090a050607020a060b060a0c030807030b1206161106040227040b010510021f0207051f24080d030528020304060f051012020604181401 68
    0x20500e07084140300905e1280005072118010a10006002d0207000c0004078105030f84042542c05900302035130040d5891a9100c4102c0e4114204072a048090030b0100070b40d214801c03965180e5980b03030303a0707a1000e480d1400045c160b0341c10180c0b602c51103542c90f1500740560071902e80003001404203290000c110741c1240c2d950443c0004110352108034007100034002602e15040b6404a414580e960b136402c40a481c40d070070384503010500d421400100414851124040c41c100c410988280010310303c0360741d04980b100c0c4065855000c0400c01601400c6040303040d405004024480d01c00c031100c101c580703d455075030120110780c401e45040e240e01702e6041c8010401d1001000c580000322030030303181d42404040f80e151030000303003c40704042d960700010745c91413403c40b242001091b5006601b9120703101080804040d40c401c442c10303035181d030a100e03110b87c003030116105480c4244504c2015a44082c20034290708022440082e0a0b40d00544c18400841c90780a0750007626040d002d55000001c00080c95038040f81005016401001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 568436573 1250 568435323 568435349
    0x4090204201902060906012d090b03010c03051003080708070203070b0d0f2c010b041a011403041e0c0803160209090c13020a0306030501020d1e090f060b01020c090a05010f 75
    0x40d050b0005500e034196040245001d40300707011a4035449903c00790a00009851023600d000150ba1005944081c00c0250160000c2c03101c4d123800003003581962025111031450324ac10130420400704040b0700260143c02d1007910907030301c0c040e034030b0300000e1419020b50042003608000085c1c44006040c1d074030604e9031600c00d80d00700341309044070b8802454406161042189408030704100c0c1040100007036100c5900d903100100100016404204040034100300100503e0120b101400709400600500c0b0980f88601d80c8048055a41c15070702151068a070342104c412142015598004102d03118140301400c1001c01090044203036010074010000c20050103402100aa00403180c110310301d45884000362a00d140800c1c0241e581c3d0038100c0210010b1140e03a1024010394804102580c0c40181900726020038141e0301c01c502c10007110100c8032000c03100c013008001c0111000103403a00014045801051034a80c050050b5902022042c0114901d50727001c48804140d151b9690040c00003442ca46250f0780544400c802c990 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 568437823 1250 568436573 568436581
    0x90108010b010903060c0516120f02280c0909060906051302090a020c0c0d06050403030b010521060406210c0602010e060a0b120703060f0c050c03090409020420190206 73
    0x20f0400c1035140400742145494070b601031030090283c001c54110b40c600c141e0381d0f106080e03241004103064000d40c08000028481c06d607164035903840014880c890350188003a6000800a0396000410706d02402000c440c1e60b503258100003400e140030f11420090600a09010400030000d1520340d0480e0401031112100c1000d18202c04050303140c1013200c40c2e001c00481c10044c4d90304038000071540b606103071400e1540c0c40004070006a007042101e41142d40245e11a40381880319a031030800544003809400140c0c1000c030546460000c400780d8914a2580041006e407000980c59150300485140c0c2c550010760100301c01c103444c011810040d41c400f40c0390080c1103602c000c20140000e448440c3d11640050451131f5469141d40d10443c1690766001c0c4251070515040488010607924500f4002400305095004031092800e02c1102c0c256000b801281c0c036614900c0081c516007940c0c2c404120042c02840c0069070030982e585603a5a083c070f8281c2c40d0501c000010611a030310350f0010085560160654815a81103401070b00a06c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 568439073 1250 568437823 568437827
    0x303140c06280c1124130606092909071d03010605190807061b140c1003060e0c07080417120d0e150115030c020111030901020306090108010b01 63
    0x54010206480c01c0310007500d110341c6440c9241e6141004010940f074640146440c81d041008569140402400d50344503100b00050154a0f0141e000d41c408001e4030b03034000407106110349510610461045100240f1240c69441c06421507880404036000301400a560303010040c0345820700e4042c104211540d085910300300400070800c0410480c0d0f00c1c0250040d400d0321120781c2d020340007113015040c0541000ba1800e20b0030b034616010041e42c860300a03a4005c1881c0403403490704c100d201e0000e00c8080980f8008080c0e070340e9503284a00000021020130f600a01c43e9442082d6195064040083c0307085d0703404103a660400709496603280740a01000301c08501008038500040220080e03d003101c03441841c52090600318820a4142088444100e0250720300040b510034810705036004101d04201c0408441e5000d21205c40001d0200f42800b84c403180b1030307002103151074042c4242c01c051424901c510010900c140142404105900b00b902d02c4049a5000b00810104d410308018060051040320000d00c244031103a400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 568440323 1250 568439073 568439083
    0x17011d0304050d020f0301020a09150c050c122d010b060c0c06030c130305011a0d0515100b0301030b0106020610030b0a15030b1608063f160303140c 65
    0x158601441c0c2c01d4043d5001d540c1c8240103c036010802138029562200d0440d0000c107256464000c0241d10641c02801806452003410100308040c2d00c03800a1001c075210304100720303200c040c4000e919030303a1081c040c0a80448507800d00d1320840303915080920480400120219017034031009205140612024000c09000d4100003d1400d50f6a1003650616502d446081000e88241324004460341c4692081d0303000001c2250541c4051030803d14002d401c030004905c4030401c014900318050190441d4800d035800c20f548640101000c2d001311494031420b251300d40c0d6005062107a0005d0f841a03401220f17080040004540611186a2000d520b9200c41038541c155a20f0f080001e8003d007003945610740c1e07142c02005c1d004114100c00f0180d5007005d0120307100e2800c01c2d080302200c096941394000188040d0045203c6041011a50510030802a90340d180886243e401d645450091079004d50305520400c0903000d005424058690843c0481d40c000101c182035043c0504603000c040e05102e6460000c100c00d0240760800300b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 568441573 1250 568440323 568440329
    0x108130203060c0c03220f05061c0510080a1b050108042616080702031002030105030309010309061b1107120812060310020406030b0112090507060c05030705060117011d0304 76
    0x2c10b2a2030310754246404e891802a03030722030b50080155500c1201c03c444210040e20880f41c80407000d4450300d40300e8061143c0d5002d491800054107564041c115041c05245e00020303880182400c9420049690342001450f00ba141c44040c1c4400010742000c00034000820b9450707010380002e0074104e085040c02e90320b0081c4c043c034281c82140c0080b00300b000d602182180400f2940380c00c8403090401c46d840b030305082640c480c0e807040500701c0c031a202d0311500004005160007035074104c0381c0c001c001d541007885100054000d46654075045030106e42c1d03410750701502d60070300380300d4081400301c1d60b9007400502030000b007036141442c2034101d141030b440054034076000644042c04564105a81140402858680401191800768a000c4140c000703800030a000c24500ea1513400790561040980e0342c0c0201c01d485490080072108841c0d80a00503070401d0000f800020302a41d0b8001d07885e403241048a291480e41d8507410b09081c400c0c4c009074240100c5485140100d42c00340104024503400c400d035030b591070800c545625503d20880c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 568442823 1250 568441573 568441591
    0xa030308060112060807061d010f02030d0e03040b0c03130b1305120f010915060906051806011b200306160e1503130201020114070c030c150218010813020306 69
    0x300000f00300034825008440200904421501a20380701e0f04050982584007a80026078409018400c410f50310401e08000c031041c3e9174000c1d610b00168000d2200280204800307401399072104100000d4194451401400001b07100c101550300c40b04480501260b22005500c01e50300e021003880103a100c405611101412a8001c48445100217025502c00b0b00b00010818004031035441c2104003010301480c402a401c504058880411843e922012020300300c9105016641c3c01a50031000000d02255010034250084014101010500030002c0b02c1c0502c0110044100c1e1800304c00948a9020480fa20050100c0d510483c0500806d14100c0c00030b40243c0c00c8204e2950410400c0350300200d01d80c803560810710f003d60a414640750f892a101c031040800d851400002c0f4010340c40d02c0449408200001e4450740a640350b50340c0d4450707150583c2c0b811100c0c00303100034080d548074400c84071690242019100810800c6010300b03408002c03a84038000500071100041c0001c1c100c17445140300c0700043e80c3c0490782d903034084941 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 568444073 1250 568442823 568442837
    0x20c090f13020f0907020a06150308040311040912020708070609230f030a060e0f120d09020103110706051f050a0e0411100206090106061403041118190b0a0303080601 73
    0x1400052481903540a100b134020080300c2c1442180c03a4042410340b07109000319401d124a90102c8028050300c4024840039022035001e200030f100084481c01034108411000b0400305441035185c6070804400c000f80300144c0968049030007002010002e02c80c00c0c000707000c2410400c1c0480e07e002841424141c807080d480030814002c18450f26503984000240c160418080c0032290000104d01d0a04024007005020442a01c0f034150004e65104001035030403603105000b4603440c10042e06c203038100081c1481c003108a040c542c41d403500403031006019000d8034006004800128207030414002107003100c2d03001c000603d441c0d000c40f20180a29281c6d52a00812140c40032920205580e80b800c0c05403843c90340c490880d90260f049c4c0458111264005180d41c0912001030080143d90303910b41060f10301c0f030030380310f034048952500340001408541040b117204030180303000d0016052101d51200700e0074130302022900446030301c50481566400f2000e80c850140480000c0c0c41c41c1d44101d05580f0003504580000704014104442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 568445323 1250 568444073 568444111
    0x1020f18031f0903030e0d090608090a0203060a0b01080a092406080712021203031e0402060d0e0304091410050d1703040f0308060315060103020a05040803040f0501020c090f 76
    0x7003008031585a4020154401101242201c1c450103003900c44000c0c1d000078101003c1da1450840491941e01a1015444070020540f03455802d4071140c00050200c940c90040c40e0749103015031018000c1c24490a800000000c840c1c000b24005444c003032001d040010620b20381190300c000101e00900c0c203090680202c0011450f000840c42010140c102600b141649010f996000102e1296982510740002d03c21107401641452000406580e0b0000301d40e810f018172240700500c900d44c0319891115400500141c14507152905038040b03038003910710000b41104298030014007000008041e110f00c80c01085000b0700030b501400c08a47c0060210850b000d50f520840201402c0d4040105004003c1d0800c407109800d00c2d03c81c506418103516546145030140c003c11800400614a032901180fa130323a48000d00b605603546901d80500450085d0040b0a042c01030090070080070440c10070800c040d200038071019128002c07150810700020704104c1044440e030701601d88081400607002c0b104520603400741442a0718031103405c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 568446573 1250 568445323 568445329
    0x60301060314030a09052416050312010e060a03050601091515050304060b0a23010509030a08040513050c16060209210d0206091209030a0812010609060201020f18 71
    0x4031550005040c1d5000c181e8241ca00c820110280030602d41a0f110200843d50758018422800010300906001c00f05004000501030300c004068402017000c00c4044030741d145550340d500e00c1c5900c02410400418001e1004003c055410101385601c500180e40c8409024615507649544000c103008440041d03460301d00c80d03d01c030410700000000900204081a001b0340c0604006011a40305440135118142824901742c1241081a400c10480d407000407403c80c21825103610105c45024101036030704004040168100c0e9075001c11184103400d016824490382c89161100b048040c0000c01d15000200c0d00700401c2040400580c4162032a0b0507510341c403241c10107002d00e040d50080c40b409985035800039100d84880100010003201102c4e1035006021545030242d10b14050f6030f11b00342240e118005500c803002d100310303443c000030203044140340c0541140d00303260095403440c0a50301300c0c0660101d401c0e2000010080f140e8400744032001440f050008500c0d000c9405040340080c4120345204001030701c25440e20742075071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 568447823 1250 568446573 568446581
    0x11d0916260303010b03010e0919020f0a080303070306090b040e0a080a091d160c05030301170106150807090603050f04122f012306040c05040909030f1e120203060301 73
    0x344840305a950720340c3c50341140d0179650000e0203217080b0201884002500810001103500101c4602070351143c0400040d42044940c400910380d41d5040880c1c0b5000281c05602040039602591080e140490401d0034202400704540d81480110b20890604800228240001c80c8105030190480c5809540e020540000d440d020100d40c8880340e010310104c0071000c0b41191720820b90281c0846595440c981400000864421b120b00360f000e040c41d001000100403e03044511800200b4500300b001040b85982d500b000d08405001d0710110b03010480103002c10103070950000c42040641801e04081010f8140301e40c010b006560000c00040c00032a13900020f0a80c24014480d16603030050590300100604500002e412068074001d106030b896600789804242d600c1d64062022040004560000405684403030800014100d924014018014100310119260b0340764001c0f49c2c0d407a400307915000800c5200031001420115070f954007400080c0d0a102035282d43d5440308030110741844020000d80c580c3c03540d00000e8018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 568449073 1250 568447823 568447889
    0xc030c050a060c082401030506130f1505030a03020601180207020316030c08121c0207051603021003140a0506030c0a060804060e0703033203011d0916 66
    0x352140d10010010841e4541080800e91070550f1400c1035601d8112401d400c0741c20900303c81400b14036075080e50350594800d03480b0300c0d4020001024003800402c0649040211001c00c038614040c0b94880ea1100c0d0910352a40040d0f00409054004008100359a10003d4403600c0600902c03849441c0000481c0705039500c0d8040d100c20300d4009003521a52510340308550001c001b1807008544010502e01c0000340d013000402c1c1c0b94000b00340c0300c00d2285003401000000170301c50301032248445803560030301c01e01e0301280301001a00b01c4452030000c101b69044c25401003020203034541d0240c1080500b094410780750082c04c50101c4e17400c070b00c104a020845840b4900001c4c107010807800301c560811080308000410a6110052074000e602441c410044514207114841d11268503000140c045890b141072981c0501c0c109100c8070071100281c044003141402010b203c02282c2c8281d00001000f09801621200c000b1181c1c401a006842040100202c000039171160190201621415401600700d4180c00d090104880d610708030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 568450323 1250 568449073 568449083
    0x7050d06060c0209090d1b020a031a1506030c041e35060f04030f0e0316050126060d0303020904091a0714030a02030c0c0f011a0402090604060c030c 65
    0x100c0c54a9400081c01c1c1d0301c2c00a0103911520111010071008a400301b60180041c41e0343d5115403441c11310383d4543c5140c500c0ca2001700c2e0860042c41c0300001040b40415080e8521f81c489246e0100ea0070030782c08180c480c0103051412445403404000780040254140200c0d400c484807501600c0802520540440c3d24001d10781c4064080607243d6030781f003140304020003540c040b000304490014032243d203512000c1e5030b09000c0380c11a01c0072541a002c900400d00441e00690015200d14080d1200d403030b070354040780c10070b0354614802c5261032140000340810345c1c120f000840b0526020b40b07190403101044c102034154200207455940102240c040080c28180309404455510b4405401070021000c58546030121700f1044112105a1194030003144115224100c0e0020307943d9100440c90554540d050010000e600241c00000e40c0c0c00b08004001000100340032600c00c64032401d00026101c7d05030f02c090000d9495040610780b003580704000c000082e5880320191000d4605528122420008600d4199088203501c100904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 568451573 1250 568450323 568450331
    0x2070b0702011e1a040209030a1b030b07020c01120209010306050301060311150f07060c0309050609070905070504080703080304030c230d080f160e04020f0310120c06030507050d 78
    0x80303803501500503a0141c1c0703001e003410300401001c00c1c0b40d60440d24040881d4024a80c8050700c2002c40c54580c011303020859008050725039015541e6101592180ea1851600c481d0a503d1810028041c240030400d0f84003041d400605140e650003000280000074011125030001e50120307440701c0b02e91003a44040060034020300208a03003612410102030b0190704410552082403804c0c85d28120302d124005546042d40001c0126090401035683c0f140a420b0384070914040590b20300090001c1181044544d016100080c0500511030900220a043c0c800040045c014000104000c0000b00c400158a1003101c0d001000d8035141d40f078601d400c030b42000c4d00840152150414004110b04200b900e600851000394070401c5503217074450080b013503c0d82c510440d074000c07004502e400000e440710b04501c001c010f2550589050700c11880240c002a049821030700400c106030b540802044819100c28040e00d0151002c00281c02503090ba030313500c049003100c0f02c1c0116010903440fa40801e000b41d01410503580c2015040d03400b44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 568452823 1250 568451573 568451581
    0x3021e030a0b04061e0b1f0c1e0b07051b2d0309100f030e19020405090109140a06060f0506030c0c0c041b031805120c0c09070e130c090e0a02070b 64
    0xc06040481010386c842c02907c0080c05110100071540290780880d5141c034940c004441d1a0001c2c200d042078981e401803a4402c5642e4001001c84034414440c02c4c4a0b21a83d40751079690b503010001c0b5a000c1c20709801d6600c80c028401d00c81c60b4103202c03d4100c0d0154200601213400890b01c0f241140543c130600707508504681c5483c1040c80d08181007180c0c04207142d0f010069035048000c41580c5144102c8180680e11990030703804054146504041c0d40b109c0f410002240c0c030316459850740c1151003a543c507908a40c0000030450200f00f014000e401c02010b20442d8841c0070f904000c0040c58034030001c1c003007c1c04528001040c681e4418288001e26040c000113000304014402c07049a804019013500c240400240b84c4005034003003000a040e807500c200c0e00b010040500c0e24a1656800701903009082e480140d2042207011078013a642d0707403180b9106200c0c60342c5aa040000d101c0c18030800e400c21106400c0700324200090440740d07540c018010411607050302c60503d0315440c0c2c1009140288111500640085681d800300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 568454073 1250 568452823 568452881
    0xf02040509030a1d011b1a07050408010b0102010905060703051003350a091502070f090e06061002030a08060d141f02090d0609080c0703050703021e030a0b0406 70
    0x50007580e181d5403281100110721150003a42000c0221526006c15000d2406841c894010344520501c0751143c03c0d00300d49020342c100448800f010031074002c0c0001c4e50000e01400501d0b801c1c01051000f103400c3c0020b10100c281959001c1e02e5940003011081007558540000e43c001501a030200021500b01801b00000c2503a140c040243c503610000c4041450000700c0805d41c0350100a086840c007800a0f030b1240021820b0121617a6983c19000100045200b0044080b546000409030078005040c0740d080000d00500c80d0040a00300380004003030030702c034840300c0303c9039042c10ba00402120004039040c600703d0034558861303002503881a1900d8019084e0042080d06211040303001405c10300215004098000504e00401400305a10400e64056007202840182000146954100380441d034400e010050a104a4104840c50240c6541c4152042e42c4070800403c258242800201c90440112040883d6a40114003180e40d13582e1200008180291400008003801080d5121250b000c40c2c0b400341c0c0315010500d00d54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 568455323 1250 568454073 568454077
    0x3060c02070e01140f18070e2b06150b090a050105091f020a0f050a0c170307112106011805010b120a1b0906081312050307020703150c0806030c09130f0204050903 71
    0x2000709423405c401c2295490200040d0a40c0d00d03102d400100002c079200c0c00b0341044020010101c41310364869000002e0081d481c4034840c00341111010494803080f4034810450f42c204c003580f20b079050000802c50345030706448107000150301c121448042680091104070491070000520000341500c1c1e020801c0d2002c114000ca206080c2d180035a03080c00080b500e40c01d900d002c0c0d44025034078420540c020011080050342c907200c0b0b0b202a103002012041020036548010f40b00c044071048500840d00312000512a0304414041d110000750f103803408000ca5818550389038001e214410400c2c000340110000191000c070346030010b4802c8016001009000e082c03110000c2c0089000d40038260209440200003144048458400500d8541150700f590074030110880030754241c1d001801401c11400b13495800b02c0031684101c001c0810140566000231401c541c92001080024040e1815110740c00503491100b03144d948520645e0405291209140504401d160a00c0200034448001390004d04150070000000300c0400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 568456573 1250 568455323 568455331
    0x304030c090e010b060a0f020f07030c03050f060c0a120207020a0b03010503010623010305100b03010308091005120c1c0609020306120706320d050103060c02070e01140f18 75
    0x4001c0c00380c2600d041c542c1d030903920700c9080241c0150042c445440403501c01c01c81440356030b5880c01900d120740c402c5018036081c20595001601c80d4511540c0410030881c0811120045410b500c015200c2818401d0f03020101e417040c01604002c00c50103684441c04910365504482e10a0390043c501c5040c2d90740d40010428640091103900d10030351038180e001500d85102c500342010764500e00f050401c1c10307942000640040c4409800c5009001d0402008551070000c07200840c040d602401c2110745030484401084440100000c14004000c0103001010040000511003a00800645030b61902c80c408400304031101803100c58806401c9060a00c00911320400341d0046010b10026180700d10302c4c600f59034219941d07900c50300c00d141c00a003054603c5661a10962000c04001c078803031102e2400511400f220240c203030400d000f03148001e07a0b14401007007002064130035220f0202c02400a000c0d030a00e09540b1410b122414415004a03620f02c20161200f40d9400c5a021144000185803180c1900f40104040c8000c01c112 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 568457823 1250 568456573 568456589
    0x13090c0f0809010902010e090a0209090a0203220201050d0e12130e150603070e0102160e0f070f0906030b12190309140901090e01140702030a03050f0c04061d030304030c 74
    0x600402c0301c00b4410302450a03038030b8043e181d200140540205100d000d240042c0003c5440d40c0c28400d07155150b4a6204050088416200150b12810000401c01d1126260340b528211580c0b142c0f0a4801030760001d054030b4179242e02c0c440001c0c00c40b40d029030590400c07400b001c00c4109890b0020b035086903a040101940207986902c3c1c001581545d0301400c052090200c035800ca503200000707000082c1807034801c4801804604040c410303154520380501070101000ba2a800c01e03200c54140c0e0082000c2c0301a9140f03069817110051400e5000200300000250201200d07000c3c100405032907030106000c6841c2c040c0076002d0900520b088132155034001036070324880ca41b404001c07800145030303c4ac0000c0600602d61020a080e0000740043c1c00e0742d20f044120802040680d08504045d500c541c40380c40d40040750f01300a441601240c0207555198450400282214001840c00314002041800c0c030110031300e01401c6c2da081e40c4043c01c3c544601440c01000c500c45034100c190722581444009070200800c002c0010060442d0051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 568459073 1250 568457823 568457837
    0xa0e0d050c16060c120921050c010e011b051c0e030618073011031905060f040213020d0f2d020f07020301060e220302030a0513090c0f 59
    0xe81e40c12101126602c142d6002560390001035000c6007070ba1a0104817a031480c1051071030140e42e06c40400c1c0040b8005c030056441c14440030400103211051140351401d41d400d1a01d2096280000006000683c040b00100030002c0f000e810142001810480010201c81010807020501000c0200429801820140d5406800741230040340315840c00c0324648811100e60809040100d00b0001682c01700d10070010500c1090703c03084450a64110920140700c2082e02842191005529201c14180780c03180030301c124488494083c101d00d01241c40400c0b2160080500840c1c043c0940b00c600003e04046000440c1106251002501280469240d0300804541c41d00340300c20301c08074200081d1490368070b4440c100c0d14003000c0540b800c0784d0100e009030f0040ca912800424190300b00801600420708498142e00074408041401c07080c031124001000070f070070306a84003a20034400f80f0082c0c1d80003034803401040c03480c41c140030f40071402480128880a11802414070780d04200580505103000030110190981d9100101d118 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 568460323 1250 568459073 568459093
    0x30f02060c070b06131d1b03150a1407020d0801090509060612120a032307051e250201030c08010f03150207060c08011a04030f0602030a0e0d050c 64
    0x20846620509070510980e00b0044180c9072800d15200050400340c5c0490103021101e100000c40c480c280790101c82c02c200140c20050903035114540001003404c1c00d039412003c0042640c44c1d40000e001008055005500142d603180c0c1c024010250058810305855000d9070410042502d5001402030310640103a910729106076039a00303052003150026601c84c40550042e0300068450704002484009044101c400c071b50040710b0196001189811088071030740000e49a5034a000c0704c620165003454588514465000d0908002e507001d0500c4c4962141000a15005049c0002c01c01c186400e4800c504101d183d440000c07002892042800140b5042c120301107441d200103c0c0d2014850f060081c140c078940300c40903400c42d0840d1254074641d400120032400050f02041854005100e44c0141e400d00d00d955210714500e941405c9140d0600c020303401d20319010030420300082000c03803400140c030f03030800350410070059803a1280b8210a0140c486880d4480a622440c1c1d00710321140d50280003041c0e00305100081c3c0b01c2c83e10f1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 568461573 1250 568460323 568460327
    0x1b120b0a0f09020603070c0201121d060c181c0b0c0703030e060402010e060705070306060f03050d02030a0e120a0b091006050102010e0d0f021c0201090b010e2e0e090703030f 76
    0x2c803001c040e40111040c80081d0000340255640000700740141481e00e42c0304e10540886060b50645038074400c201c401110010005a01041301da42c00032000c040e414241210842c500e80e5145111010718401c508200307508144986400d202c442d0a07411020750480c5151243c0400e02075440001c0c102e00091815114850449002c42c403640169416510014600103407010440e15400c00c4400f507a2a0003441d0740040018460b10980d8014007815420301c1c00c031413450404900705448a81343c9001e54008000190300c680c0d0154981c0e40c10038080390300102e00c2d0300030030b040381c83c2c0441c11100a1018500c1c5040c8030b140307200003c2c1c0b00c5030100c2000e42440705a4039180128240c4003124100489584002004c1c5c03200c2d4002c60001d245201248120380303d50000009a0604510300c03102000580d5580b00e20009201d8400950342c05401c03001c0c40d0780b896050070912114070910300400100584800740320000c07041c130582c92442c01090201c0d01010b250170141c84064503a90b451004402042d021001400711078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 568462823 1250 568461573 568461581
    0xd08070b040b0f0609010303030b120a050a1403041a1308010e1b0a03020d0206070501140f070201060f05010c060b01180308030123010815031603050a050d18031b120b0a0f 75
    0x3c1300940a0039159185a505801804000c1032040e0f200c002070040c880f410303800f00712003605036024034007d01c82880d00d41044551014100000301c83ca8000700010721142040817100800c001e10207070540e42d1020070605010300044c0700d40212800b5400c001c0154807404e80003403844d800030521555003c00c91500e0040207041c02c11440000d40040100c1a15405440c0c841c003d4100940183c00204040541131000720b50f581048524901040d092400d10901e10750910400010f4018100308841c10340c04d000018050484200c0700078241074554915000716441511070210001d00c1c0300020310403540728604450150003d015180c40c40c50084050106500300b0794107010580740603140e034189521603900d0320b48040907100007142c2612560f050500d01222142c8031400440c09840134120266180c58424100b404c051620030812003139290103084140410301200032a40e2006420608540058000c5011300241e070103d00d17001800c4829106000451030001e2180062090410200100030074060850f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 568464073 1250 568462823 568462831
    0x1020c011d0a0b0c0714030c060a051e0a0e03042607050a1703071e1202280311030f0a020d05071718040504140c010908060c03060d08070b040b0f 64
    0x250b001408000c0416849029540c11551003942d6628020070303070f03e651907140071540001c60030342d200003071900340b95500380b29280d005490100144900c5c02d041d04a101c040c49070740700b40040d440c030b07520209404411680c8503201e50100d0740241c98035669120002c0383c0303c5000d55a481c0221000070001040000003040c9401500e4000340991b086074140324041046042c003440d40003561104200300000b01d03800e030398150818150f88060700c440103002e14001c4140c04414404406551016040c41110310764220401800160a6442c00d0162102e09080b18000d0070703101d40b03c2c4940400555100005807450043ca103441c2c1d1074081720340605c4915002c460724490958058121030007401000c0a901c42d20000f0020582e040d0341d49111080040002001c8600540e421286509407250284007000c0902c881a80c42c1c1c42400c080d200a0300c1c3c100c500d51240da00500a50140c2000000100701e82c2c2c42800c0700702001c0d0065a0517441e80503c0c5046240408140c8041c0c0f00c4808a10029030307001683d400c41c91003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 568465323 1250 568464073 568464131
    0x10051210050a2403021c0906020307090b18011101060e040803370906020f2a071d090f071508060603040f0f0303060b1206040507030b062704050901020c01 68
    0x43c40016031045000b9085401641426211451400e81008050042c00307060384c050440140d036818036020280c20704610f80e1100640030303014880d24180803101c0400c0d41c4d41300000e003071915042e829400910700620b520f0300200308001011081c8003c0c04000b201031b520448550002c01e00b514550390951400801024040c110a0460b071140004600c2d20b810440300280b10b103801500305031581c201e0000301d810000780c00313200c0c000b0361198104c517400d0417000c80a501c80c0c100180401600300100003081c415048840d150a00740da82c00300d6201d001c200280b04480740c003901650182500c40702181d1076980c00d00c2c040d0000130708120104205290400c100e07401a940903081c0141001c440e81c6240c13001032940b2041d403e05a580c40c0001c6c4003c1260010600300c0d6205000c017085240c0081000700701d84010700510200b610f0295104401d880e00c40840342d00c0c42c03104500c210281c107c1d0600ca075940c5000030b00c42d6040360600080c0114035905401801044465400904c841e6845101c01418107044001b0001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 568466573 1250 568465323 568465379
    0x1906110708071118041e0c0b03060406090b0109050904020d062409050f0103121e02150f01060509060c071a0c0d023c031204050607030e030910051210050a 68
    0x84032011807000d021018840303a82584000e0300d403503008041a510102c400380000040102b41d140034810b03400645090f00c000c01151050b0000240720f607100340100c3e405000100042000d40d6161070590301201d42c442000c1c490040c1d074001c8444901f001c0744002c60b10001c281c04c04210131502d8011548910b140b6012941960300e0750b159849a120500581c07130a02c00c0ca90441104c81e40900c484040d44051a00117000102614401441c4454014180000708030b40d0310040c880e09900c402115046c84048822545400000605604085081d80451411f0241c01142c6e034418480310b002d4030480c0d29800039100c5800b07280b481643c40f0340e1486880c64a00096940d03644056404070040482004850f80340c0465141f218038942c9158441010050811f0600c4100030401104000c1c4950202003481c003406016401e192003681d9029038242c0303c0c8100802c03007510708414454016102c10801a54205c4c0d403508103180103c4010040c0d00526026902c0d801010821000e003910300c200c070800b6410035807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 568467823 1250 568466573 568466581
    0xa0e160507020f0306010b031008010509030702010e01050409020d0501030b0a05040b040201030c1b05030c010c022a04091b180c0c02040507210c0207050a081906110708071118 77
    0xd0301548001000c903800781d070840610100e62002c010070b40c0a40495125141e45e82030903616401d2440c1550310000483c2e05240c01c100d516100401176400e0240d080c20401c5015820000686a90040b60040c00400703101150300b426814560f0001412a8001c00a1801540302c0a9050341a50412203005d01104050750101e00194801e0388142c4145002c3c0c500707600d010350111403809a42145003800d42e0141d001040b40d0058070420b100380126540c8a00081c442010003001044402e0482c00c980c40343c035410f1191030310960f1030300c1d007002007a5507100302ea030244901d041040c1002c2a00c80e00802d000c0d418002d1501c240c1e40c02910840850048a486030351654000390300300405440d00400034400c0218002030360250307006040d0f4040c0701e540c06240200720903410f501e0080c6860000c1d40500e2003281240e100b08001800420446510105524192406002030500c0c8018102c540920200a2800140303202801030100241840310b00c552800c5200500302d03070400c01c030b82c0b441269400301750105070049 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 568469073 1250 568467823 568467827
    0x1e0f04031404050a031103070509090703030305040507050a081005070926150f04030f0c020105124b04051504030e041409100c0519090f080a020a0e16 66
    0x1c699460408041d25050712038000c01e50850150b40119440c84800c400d100c0d0628007486501c0c00303480117031041101860101041c03603030b90003d0f100c05000c1c141e460000c00c0500c1000e10203103019050144c00a2419581d0b242e0995a40400b00040e6108a28100100b81c00e81e200e00d200300300321010089050303e808041102805501550f103248020381c4100e00910045a01c003602c624401c4090301c44a00907458541409049232001c6422141001010502140141e07080020b45c3c250840000c4c1a1103d684c558200781d4180e15200030484451400c118503840c070842550a0341c002c000c007014000402820401d0083d14050151001030141c2c02606020324500c1810714929440f600a24041c40b502d002d080114003101c0d1070f08407211000342c0304400c0041c0c0580401c008602c00640400403c584682d01400625030f00a050080808100481039440c072544904c0751400034080202241600c6542c40c4080c80d0b880d040f8203022409085542c00000e01e8525911495204160340d81c90000c60502107072007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 568470323 1250 568469073 568469087
    0x43215091002210c030603060c030103030f0302031302090c0c0709060302060405061e0c01020306041118040b0607060f060611030c030406030203040c0b070609020f03030702010e100306030510051e0f0403 89
    0x901c3d07103484120640c00c082c040410700d256004014804a07180d60341401000c0c10b062007c01030100302003050402c01080003c0d880040c0401d1b03111140740042e141c8c0c40b64400013207002007040000e980700344020184256000314000401c0e410061030201e840c060b5480c201d02050340c0c05440082e41c040320510080180d410300100610b0710348054503e48145c41e000d0000401d0640000d004000b1076075010080012500b018031450844208496800e4103295007440c000c4070a0660862440c042ca48404170000681c9500050705c0b901584503400b40034040205d42c088009120a128090008940c84503401703540c1800300c21200c0025072180a0f514003810006c00350042c0d4005003003190242000140002d040440d0009407a84500c2044086443c00c4140100524650038200603403007600104601d000603038104100100d0110f0580b14071140e201c0000090b001051142e00151681c040d400c42c0703943c40050366002d00d210715582846800104800005044244800ca0311403c3c0020450040b4011a005840c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 568471573 1250 568470323 568470337
    0x105030a0e0d171518310209070302252118050a061d030a06020a031a01030e0d08041110111c05040e090a21030b03060603060f043215091002 62
    0x72110030b004501034540500c20145481000080c05421b284c4046242c0040707032a401540518080d070401d811200700c1c91000b00c1140a405121203814449400c100f00c0c04445100710244110010484220140c054000d02c2e0b808ad02c100700c074442080110342440e2020402003962140c1d500e24406990403000b420641c280203509030390510803000c401d000514280006e25040a455a01151582850007030700146211040c1c81da0526081c06028a110b00c00084c2e102061015131804900c65112400c2030005080703420446a00522080c66280c00d160308940940b6100448108540903030899111a0310b0000707450b540103000076001c120030403154091100594125032200d060301d6140940d6558400e2042a50424450035220754000e504615014880d81d41d08200030741c05007096141c502d0000fa2206e100800300046811b10101080034006030100020980700300800c00d032071400a02195010344000701000e0205442200084404060f4102099029042280c001e000c0145100a00b602a4005c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 568472823 1250 568471573 568471591
    0x31410030b04031119030f080601210b01030216080405100302030402090a051806011724011e0b0408060a0c031a0f0607170d0b01090b090105030a0e0d171518 69
    0x22011960803404030179280c00318400d41760107284021412018108a40007801e45040c00880b0000030203420342000d0310a1004518403000030321000f080c006900034021314021840c030b2942c2d4501c800800a03944000c005550040305c2c108140716000c041101640300031103000b034000c41541c000c96000c032480d03003026400c203d0710924014a40c0e980700416140150903440303e0070300100b4211601350543d052102c1c00e40c0c03482d10003060803a01c4c003100b640380001c84184a01c0341d0740710310303d1036201403015041076480c050807594032038940d05d5a45003051039850b80c0542c1c3e40d0400c1c0785403080d5680c00ea800307032054070742c0c600c1c2500310080d070a1001c2c810061900000020280c02070380030800d000004031448114407034141e03001826500c0f400341561030340c1120800c2d6005414061034801c240640c880e020243c1e42c0e803180074070f0b01c50303070740d5550030380c218064400005c4a40c058401c4200b03070310760b0395000711074005038204100503c2e02c1a543c1c000d0b161892080301d04825082980ca0308030038a0700b00741c801c00541c814452 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 568474073 1250 568472823 568472833
    0x61308071119030c17031909050a06050c0c0607020d12050913140903040f0e040201031104080a02041b0504050913050a0302062509140d060507031410030b040311 71
    0x21020841440114240040000c0520790038420401401510b9001d4400c007509032454001c108404da46d01d1040c00781500007040f4a0401400d25441841c02d04083c088c003404030302640d60b4a080c040e0203a0043c08600d40140a4203040050b40d0502e4010b031100c140d0010722200c0d0f05000340c3c03904c0287c2031140c03850600f0030100300f0195a85880d800d203402400d0410720700026003052808080d4030604006041c115150f00100800c202080b0b5041d200c100f0380d6401d0b220f06025484034401a00200800300140c0b4820b20040380c0007800100110354080d266000762424450544141c00503040800300e01c111501044050100703001c207003030003208140c3c80341c03503000090000380884e140c280c075010010720101e0040c0c2c89802003001855030400300c1c000c0c0c0080545c07402003494640901030485c44941c0210318110080100038a00c90707640d01c642014043d0060304c10410740c01c0103000100036002e48110329504010340c0b00407880a8260881403800c40e41c201007050725030307111607508403102490500c10305074174462 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 568475323 1250 568474073 568474103
    0x9041d0d0c03030f2c0c041d0f03212a0414040606080a09030c0203060f160e0a051c170301080f03030912030402060f0406020d030e010e0d030e2505030f06130807 71
    0xf140318240c0c0d811025528100c40a2914140303a151498610f8001c0c03460b001070100c3c146040e848841507440751001c1d00e440400d6900d42e02d0790104030501452224010541894cc000142154402482515503804490002410403010b100a40c2d21760f00c51a80094000b800141040f040355020000251092a10b203c03945501c3d00082d180400035a076800d5903100c800c05020f032000c08040c5034114030700ca031708040706407502040000c2c10340c4040b445028094810000102c2c4400741241150030000e50050000200040701000c5200a4009001c0c00b12148980841140300100000580c1c1c4200e500400500882c00041c21082440c0c001034012a0042418000c007402180c80e0000340003d0605a0700900b01c030084684014180c0d29016000c0345564036160307256a0f00c200100f190307060068076041c081614042c92881c103191290640c070b48110641c00201d2028520040340d00c0c40700300c507012021503140c004501d600782d4903624245c0b8140b1000c2d49007140803000442e42c4014201260140c4201802001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 568476573 1250 568475323 568475329
    0xf01180908070b01140a0b04060f03110a0c0224040b09040b0a0801050406050f01050303030714091504052701141804060209090a0507020309041d0d0c03030f2c0c 71
    0x800901260407005800c01400701100700c1711402208501112500c2c2e00c1c0303180800725011407145000f007404000c020010741d45c1e60f5009410140090780c41e50407460b958076010350300500d10064820100e11030f05030000c020348081d00b414140c408580345621401c0c80c20f441e02600c400380e640050011504142c0326040d801d4140e560001e0785004044600022402e45858903020007180c4000b40b031440035010040045c0400d85000040d207503c801d80d400c20860010184481901070f00524000300e80c45a1030384081c0340e54403d00400380048420566000c80c0e201c1a2000956000039165112030020036440c00420508801d0800d0311080b2001404510310205c0d00356420075044000c50341500e005070006800800741c144194043e6100d00541c400f0411401d010314003c1d102e114803d0458401c6442e41c0744060181d002c1102d00101e82e60080864111040c25600a002500980700c2940031900d071421403450317007850340a000010307003844076900340485020050114410304074a001500d88203a500400c2c80c1c1d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 568477823 1250 568476573 568476577
    0x3190c0f06020d08010614040608071413050301050903031302010f18090207030e0d1101030f0b0d060e10090b04020111030915041701180803060303070f0f0201170f01180908 76
    0x107260301612103480c0d401009403913480103a010f01c0410965110b282d240c01036180549042d00d0007450303c0341094683c0c030400c5032203201020075295070520001d180315020b0040107944003118016030007032159079560740429403280003c80315065200421582c840066110340081f110650040c2060f10344404040c001d203100c21081d0704443d40c15a0b00180040500d50007101526030043e00702c60341105a0f003143da80c1a01021039100b114141034441c4890000c601c101d411800c8a050f0140450060584038200352001d0440c4245500039402200740c103048a001a02a440c07000d030b040700d0b80b42501e847e00e500445080a01c0c282c0031509000c280110b8410760368600c2055003180c480705000d9165400e02104000d04002110000c481e03a2400909a032420701400310381401d40d81100b0b0003902c3e81d40d024042802d5105402c8020034404400703030741c902040000e28000700d04074000e0340e604c1c0d000c20780708070001403091094031440d0007452004010010580709451401511300d49080102e05524181e440c06059 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 568479073 1250 568477823 568477829
    0xc0f030a051005190603050a090b04050a060501050a030314030a060806040b0a0e0102090102061b1c05010e0a0903210b1012050604090206040306020f070206030405010b0a09020903190c0f 82
    0x50700c500512a0064008469002502c030883e0500c24195005031000010304c500d11840050548600004007040081c0e070100800f1500003410b181c25140c286884c03600c1e54034503c41125000d203420300105403030621441341070070f90b035054407080701900204a07400043e400080548010075120107001c01c0e80001070200b240517900c109401d4800e400c2803958201900c101e002c40700c500d42e2041c030482e110fa82e1300003610b98000100c81400e40d2031450044107013503030b8421204507a030722411080d03401c41c01025640c0710701c2c101e6030305038110219500d030456140c055036003540000d07000540350805207100d0403601c0d111004403110b446000035144405408641280000c1070200c020a461144050458200c0d0003116409002141c0c104084501036001a07498095400b011b850542d0100b80b002c081440507080310749070380d0000d100c11f81741d01d0149840d902818201d84140e000d4038041c08000345100d42030084c0d810141005024050000c0f5454040038485080e04040d00c00c104910b81c00a9401500211403010f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 568480323 1250 568479073 568479091
    0x3130c030f03030912031505062d040303020708070b070303051e0c070c080703031704060b1309060f0605060405060c0709020304060c0f0804051513062f0715050c0f03 73
    0x20710500c3c02c0005c0704e0705010300041c062500300b040d50301041c0da40c1d00d00c40e000c2e50001c035101c5403615900c01c048007808085040d40300c1400c44221200f4103c980c0b03030002d04104c0384a6400c0b10240754079a40c0440d2200d01620800c84411801e1012000090190b001154000c101d102c02c03044200703c2c06101c0306844c7d070a9469030821000096080c0c144503a44130300e42e0203070046d178000b80710880c0b8640d0000e003220780e407d000902c1d100030140890100b0109030082d10300c09000404001e11400c041d1602c600402d00030a0446905d448d188040d000d9411340d005000c2140c0f0000c140341e040c9842d08003800990b50250700590114059007102098858107803001d1402075004403000035070325041d54006003c0010402542007440089010030000038400210202c01219200b4a2003044d29643c03401810001d565800a042a040c14180000d5540d528100c0c81c00110919a8102c06030703e00003005100d00c1b6000015101d00700345c103807484110760283c2005030082c5c1c3d03019180c1d290030315007000200145c0040e540004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 568481573 1250 568480323 568480331
    0x30c0c06070f032304060b0127261002090d0515040606060c11040b18040b160e01020a0602031e040615050609010e0f130204060503100602011103130c030f0303 70
    0x8003958580b00303041c4801d6a5980d910650b0500c104e201042480042004026548524000c0307200e900c20f00002e0507044500c0e43e08412007440340e07a5141110030500446c1920349100c0c00d40e807000720790028281400e8410501170829001c0c050000000b0750302000f44140c000d8071001016002032010010302c01440d02c4809000c0d21400e152800e403040d500160300440410507065846804191010007812420074119000a8003a0b981d0021403e45c115003960b403030a41c0714100c00c1000b80241d0199261091880135039504011452000c15aa111854201640142e101070b0b8103000040c820b500641d00200c003542a038a9021f54284041310030442154112942d6449080c203083c05503a455480d800380a040720654141540400004e10a0b42468045441030a49840e0038005440b0a28480108042c0308025076455480f42c0300a40341e9402920111100003100c0c200040c020303c188182144907244030095461500c802c82441e100706180341b801d55400450f07030b01c0040000c0c00300926814091280d10042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 568482823 1250 568481573 568481597
    0x105010503011104060e010810080d080a0b01050a081504200705070806010f0b03040c0f030c060e0906010c061508161d07080412140a0305040b0f0105030304170c0405071808010e03030a02030c0c0607 87
    0x40191440014ed01d41480030a0116160007a089800580d104003046060140c40801d03100240c090980d43c4500085d2060250388245040b62074401403800034081d508646e511540c4000255a46400b403155408080c81007c0601001110f13400030b50b000303070198441c00c140544640c5c000308040c0306680115640780c40403108000540c2c2240c50003109000407554942245031907000078104c49020f0000030849a5a450046013103407a5002002c0944800700450b2410205408515812a03a40c0226a46254004902c0d4660b940e00024140303c0c3d40103030340340701c00d58a07203544e0340c0040f203584003501080c024000c4408036200c0310701c0c018103e1220560750101c2c1034205030034000941c00006d03104003100c020b00d200601c803980300042210219034160030000603a40d021940b583c1028107646d1b1340d690103410402408042f550100c5c0210202c030000c461840580d90b03984015080300c0c0e030030328102c071304e80c005000144580300d05501031075002140410711461b02401d100e610341440340c111400402700344200502 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 568484073 1250 568482823 568482841
    0x1091b0303021509060a1107060c091701020c0a0209101802030114010c020a05060a030609090501091a0910150302130509010b120705040b0a0503030a020105010503011104060e010810080d08 83
    0x58110030f082104604001210fa5110315005140d000c440761a00d17250b00d90541030304200d80341d0075003000041010350842d1200400780141d038800d6030364858506802c1c400501c01031084500350081c2000a0034052071903400d00100302c4c40180500d0103038603200b2000461818000200d00c00c00a0b181e00181d0360340c1018241d003d10290920480e0400140120200042c2ca03a4034848058540072607200c2c1c1c661034001c208030040c180c80e8110342200d41c00e004603001006415040851014880e2603140a6400d040d0f800351060f1108403900c811a5101610051007000389620400016084c1001c214005da200d80204044800e42c203035015007581d880080000a500030310405d030303008da0200c6204011b03a5526500c1c9a40e0382c0b0600496100d241d031901180300780da07581a0002c005041c09400e603a00c03003c00d110064001d003002d101e024080d5080810104080d890362007164182c07030040c0c030b4882c0d00380741c0d001c01112510070040401c6600c0d0315682006c07401b01d6041143c83d007031700030a55a11a4038038002da12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 568485323 1250 568484073 568484083
    0x12062306090714031314011a030f0d0801170a0803130201020c15070b06040e070f0e06060301030f0303050a143103140a020c0904061a09011a0c01091b030302 69
    0x40401054a6021900b03100c500f0489400150018800c2410513403070500b03185181011034003001c1c44d840c000d4441c00c4004d0080081d46c065400724255080150722034904e54803200c5001440001071482c0c401840760030400e410070282c0901180031268105203a640306c944d80c0e4010341c1d9240e50109252304580866a04000c0c01a45002c2590715640402480c05020914010594010000b00c400d200180040c1c032039a20540ca4042c03218125140741e41c0d80c2144c800c03402440c2c05401d2400e4486000124107050900440381205d6000340c507101d2401503034400718000d1002074206124545c0340c03d0440400c441c1146c0e000d0181d10007001c00700c0c03d040009004040d0b080c4201d00f42d0b45200202c1403400101c0d0b00000c9214100040400131390340d949134100120b05040c1001c51040e072104182042c80207001c40d651102000420400c0c0722140031a613903041003420384007407107080c4ec0e140c12641c0d17803e291049140a4128040c0c544008140c410240e9204601d0052010071500b04c482039260410034580c2c1005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 568486573 1250 568485323 568485331
    0xc0903061303020c0d0201141207020d020d090b0d090c0e16261009020f0301050a050d050c040218030a110f0d0507030201052a01050a0c050c03041206230609 69
    0x81080402841554044d4581c06200300c418820205800008107590050418040c840280600d80d503464900000c0d1029a02007928208010b206141e5400603050000845a0302204692924681240360004030540390b48640700000c01c2039100c20f046030010b00c1072840403000c1c07c6488055503082c9080c10050304043c5c80c003500c0302c0070400c00c101c0481d44c03012586c01100c00f4100c5040d210016540c1c1805e0400850015409002c41c18130015446102100d01130141d81624012200c166455a84408000b01c0e069480300150150b0072042a011862a00380c0c0200003400002c0c5500c22401048400241003891101083c1c6505800036a501c100c0d14040d510280200403c84107403410101a03220240e07513078040d000090501100007030421260a102190300c00300d5020a00080c29541c4408060303001c0c220503200b0900407402e00352041d2890f401007050b43c2503d10001c008604003880e012a01c8040390a400060310100c2e990351031500c2282c134007461f002d480c009405c60446da0b810018103202020394010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 568487823 1250 568486573 568486591
    0x60e06060a0303091503062d0b0304231f0605031203010f03080d020d0c4a0402070b01060c150b0f01050904290301110f0714010e060c090306 62
    0x441800000c1c2c00c80584d0050b03079480043c15002c149981c44c21342c002d0000b50007182d10704c0b1000e0520725220011414903242490007012060f0440d507682440c03070351804284c40c02070144c80e0124003c80481a500e41503e800000743c0e040325882103440c94031400b41c90b807109907007005c1d6455083c00c0c491410208000e00e04544100c0c0064510746c501816080044400c0c00b006110583c00554080390410640585240c05030518042110300617500c80a0000c03280c1c0340004089608902400c0c40100b419408507280700300341c00200e1406e54074150034551261391090b40590041d400d0180e1001b103041b440500e03010780002d884524440b21242003a1310f1811205051140103401c0001c0c0000d0303030701c07003803881d1340844d200f0708002d40c440f0b010b64002806090900380000088020b480c58004e6400442c240c1818036505800070421004070b801c885003244212219642140c03000c2003210001080651110080c20f810b070000513041104c4038407113041c02015184400b6990000c00c10051500d8180b1806400039070720 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 568489073 1250 568487823 568487839
    0xc090f14010b12091f060501020c151e0c07140a0b0a0507030c02040207120206161b0b091f020406031d0a150b0a081606020a110409150207060e0606 65
    0xb03060000c0740d208900c00841d00c10741481c00325005010030402008120764500b0070700c2c800d50419001d800240b24922030030340140700f016010382d154145624a0b50a45003900c06051170698803400300e081c80310b05404840400302041010380380175003090011401400c040b800400910b0b00000030083d441030182c120000c40202004903034891b07030704071007241c01141e49402c048902e28411300018009019600c00a8440a005810b80d00707000c3d404210715101d6120200c410604810705e0b101150b094850354803000000e0ba1590b80350000c920211219607000b000102160b14444111032452000401c1030215608960041810b1043d00c0e01802191003041c46011840b41c8100d002030310380e5485214404c0508040f51001501050b1480e5404c114a2040040c220f000c0702c96a03250038558600c410168480c40184240e00030411520210f010b40b541134000380c88400c03122a050030480141982a4103e5050b5103100c043d580a0310300c1d0000c2c220041c01444000f5500e40c107050320303505014004000c14851194 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 568490323 1250 568489073 568489079
    0x30c0d05100b0901060c0605180d0e0310200c0a050f0d091505090f01140a121a0a150306092a030e1b040213120c09022a0a0c090f1401 59
    0x110038032034441b40341c01420102d0b4a8a403010710f1340c00840e240e5000c4119000c1c0223135140015401c01c2c44945c0110342581111003480002c0005400c80f030000104031164400c40201d030140c0180b010181490140b0b80041e00d0154000da941c3c9031501881c0c0303072900c1d0301da00020280314545800001410082001041c084c00213004030030001c2c400c0c17081616061294070030442c0c0c007180e64480c140c0701e01c0480442186036680d82400d580549070100c064000840d0034140103d8540e440e02840e502c10079000090444082c0314213200c544500000815202c03406c040c2c0c0c030100040c4030403060280042101c00401d100f9540b8140c4004110408a8a00c3d503200381340c00d2000c1c02c00c1c884030006414031b10103074a80f001c011105a900c00100a03119401c18a800b002c07d00710003040c0c00d14509140c1402070f21401380c991449580300c15040c186c0c011003240c21511703c020320000c07240311001d40381e0b02400703a09c040c240e444602850352094010b04290308120a03c5540e80c00b00c24403c070390303482480002c4450548240440d0700d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 568491573 1250 568490323 568490327
    0x5010501020c0f120a0503030114040f06031e03031b030f0e0d021b12010609020c0f070506030a050a0b0907020309040f090503030412050d0203090a020901052d030c0d05100b090106 79
    0x4444440a0b0068424130180d4020f60b80c14850219443d50110949649594402c0c620a400c0c48a400462040341342118040100b94548601011a5803108280b184c0d07640b0b0580307011000c1800c010136824035403111081c8006080a00716015231485649000806031028603008045440014091030039a0190001c14400c2d42c0000303000d404422900030180d100c941c0c02c001320700d1070041c00100700015820413001040c51001a00500112458441118a007440750042c07940d8a01c2d00b44202600b02070b0400100340b0800701c0d600015407003400e0b480e000c6400703242c89002c07500102080781c00230010380000ca0482240d00c1e00e80265080c0e00e286d41c0041c481100c0300d803201e0b0b45901c8007030300007000d03079094026415a443c0107005603401034441e00700442d2240781015550b038175104c1c0b4500483c03244000300d0000c07515103406000034030420718024102952022140f084011a40719080382541441080e05c1044140d403451080c0d4105841413010f01481a965210901a11004d2004500c5012204010310038aa = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 568492823 1250 568491573 568491589
    0xb0c030405120c010b1309050d08010b04140103021603270308030619030b04050703030807082211060a0306080d031b030c03060f06080f06030f1b0a090608070905010501020c 76
    0x428050b96a20800b5044250060241c5003c058000e494400301c8003511042d9400400d44500900c1501c60407000341d2000c850080c03003405601c0c0c02000a00040c030000d211718509060720b83c0181001440e008940c03410f03508540046a0450024841e203000c00c420720403220500090444600c42c8640d441e080da60740d04540c1c00b001b009140a070003d00012650175414500c24402150031403904449802c050804a45136409400186c01082134480442c441c076200e160380c1841a00290840380b11294207198030305084404480c02d81d13a00d0044114140b582c1d4a140007410382e003603143c4000826500d84003143d401c0c003040d424490185480d184047c2040e443c680c92108001c20306150004002103034800036401882150080801c296810b0804114103400042c3d642c090f410381ca62580240c2e9600040541d68030007000c501c0c0700c0c0d402210b030b290b00b011481a040d22820800408480c4803944410420040311015407041b501079000200c100070a00c25480703800e0140c0420300c003a000101e08000460030300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 568494073 1250 568492823 568492843
    0x150a03090c0b03040b0a0b090106090501050a11060705040f0e0601020d05160b0412120506031c090b03040c030c060e090c0a03200c0d2d050c0f01090b0c030405 70
    0x2168540000e84200914020420041c00a80041a40380d04090902010400c41104c1c07000900307180440303615440c41d0260760f180c1218220b9403581005800c1c2001102e061308031914030780500c480094018103020301800418480d401d6540c4941e2250716040c020700707400160ba4403103200010b081e402d025841c1d80c00700d41501000c2290400c1c941c1c880c440380110592802546015002e9136184051104008da00d480c007040501180d65929018140856240119582030700c60980c1640a000c0540f4050740340612402c1e0b100143c109803203415592002920f150b40112000c0781c412100c1c0100340704205041c24240050040b600d0300ca4120303442e01000c1105e02c10043c05030301020340c001c6a0600114465001004e1000d501004001419041c0d041007060350801d40441e4418010b18540f000c80c2e5108500301c4420602c0e4520405065045c403030349000c0c0d0500c000641c01008420000a00c10100030800c0d000555250000004d9104a5007006000d8842c0941192403282c0700308148400300d240010b4143e25 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 568495323 1250 568494073 568494077
    0x5070509060a0e0a020711031b0f0102030d061e1d0a1805030a030f110a1409030a0b010806011a0403030c06050919110a092c03040f030b15150a 63
    0x180c88401c0025404455640040300c1455a182000300003407440d00a049614407811440b010100303403c082580f074802c08c1c040b13903080304141c1284074050310306000d5040021038103006691078140e4003450402580c2ca0760f040201c56104031000001c00e564a2081310004082a10450442444804082e051780c2406041d9503c0c032a00c0f03c810f025290035110f4030300035883d84001180d641c1e03010a940500074041d070003800101589044c40a11f44040050308480940020741d5550b00d98240c0d400c903e0b20070350040142550984602400500056071080b555406000c0d001e0042007a03616101d040c00e03010008808040d03009405002c100002604049004c40040d4010720204176a514400558681000744c460804500030300007a160a003c040c0c0100001c400c41079a8101754252112602d4003513420091f58200e09112100c904001646040c2120258000d41410340385455030759180074010720002d03001900e00c010000144209114501c0340e80c610001c081d10b514403441c0c090070000085008821710300003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 568496573 1250 568495323 568495339
    0x9170c030d0c1505010e071404080c0d080f0a0503220b010303030e0f011a01091a0306060a02031204080406020d0216150302090a1e120503040501050d0209040f0e1603050705 76
    0x1000480c924904101c0b6108400b00f110f0342c1d50f020151804101515060042800c0e40e401c84018280348e01190f0507125010014080f0000c440140121121540e10546a4200c1804191000201b40b00200103519542c1d480340d0310703070030160b011000b1008184000c980011000d070503803000074404418541180d406041c00901e80059421190800411454a4003194070340070541180302d8801418001d04942a62a092820b1310349035000c0805807030350030b00700800d0300910000302146068802401c0200301c86c810b85c0c0c10548181e003140628502a102140c0400c0c2c0401c0074400d0302e50410601140308414070080000c5500744416400068440c05000058005000d941c0d01d0f090094048458003500601087d50307180d5102107020000d0000d030003600d06200e4074040000c14811114040d41581c1c1c01201441c1ba003850080190341c50341c440d0581c05001a001d1084100c199120b00c99038400401244000c00d200326a514038030f0626a44841c082c01d4100c0c1e4603020f0001c1a000140003040c2c1c0c0c0e0030f440074a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 568497823 1250 568496573 568496597
    0xb130b0301150806090f0c0a03020f060c151b1608090a080609060106030e030703210b0405310c12020105270f0a0e1315020a09170c030d 60
    0x7805800301100020700421040c20018001c0c0001501c544614032076010751305c50300c1140108588030201780c205a41d10200e51602030000d0b00d840344e003072481804000c200c140340c01140c1c010507040840320382070007001401100401c413244006075840010f41982100d202d02c0d02e20151560014000c00d150040c060800100e61401c0c0768030740901c07260240001000f00c5002d4502103c01c01e950701c500b405040002030400070441d400107400415103680c0c542c0b40c0c5600d81c410301940720101c250301005504070051a11101001c0c0c29459a01c00c0713034081c81000c83d000c404050303148040070f43c200d14441070b0000e02001143d14404141e03000100019102d00700410440004540012a001e0013901c4010003a00301c0203c02c2410300d00075491000001c1016508110103025135010041504c15030302c1402107649030750001600983ca41c0c9140b00449d40716001070846807484100d503104a030890b02c600804107606070028403840c1c00e440700b110300ca036490000801982d2504400b00e61103d1441c83c0342010b2291000b680 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 568499073 1250 568497823 568497829
    0xe0c010e03032a0109080d0606140d090c170d02060105010e0a2106050916050307060504090222080c0301150f0e0c2104020f031612170a080f01090b130b 67
    0x7109696556100a1055190a00300184250307c060450000f891500c8800184a0700a5a9050f48400c509128605081035950103802920107403a040700c85010b4001d000c510810301401070720303051074403000070b218105c8200c0d800380c902903040c0c01031414400e0010b001d03426941c030602d1400a40f4260340840c8502850310b5554140e151101500030041da05040c10408a1440001c20b00d41c42800ca084503592079035500f00b4583c41341502c0c000c00d80081c1c0100014011900f40d60001c1c03135550347c03280c50069034913048813201c5882602e40d0440040c03038014180656291600340640e0951199a031021b10800307107003500800200c1c10794070640e00082003a0001031010001801520070001c2102519045803101c00e0840d810b0300c10458080380300d040519199616410001050114900c009103800e01090034416901189507103a20704617800c041e0300d4407070403191001101400c581d0226460310b566600f0909190b654500c816081040c241d4980a4030700d5441e038900142840c40003282000140032520350000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 568500323 1250 568499073 568499137
    0x20703020a0608060a1d060103091b0902130509010b0a0e0102120c060f01060201020c0d0e1c08030f0916030305091201230a060815061f02010e0c010e0303 68
    0xe544000760020000e09290448402d03440348070200c0b4403240d03142e124030320050f085134200c54440e9080c440340c0008540354000d80c8003410660190307507030000200c102541a050120743d60405030205401241c1c042c0d000c8001d46804019120481d80710ba070545c10400006514010070340070708100b002d03100c60103411342d009000100b05805a11032540d56440d01201d115a45c030000c3c0d8129060007482c0c000011030610610030741e80c10b01e4451003d840d000404100844d0102071000400b039005c44202e007403800b100c11610300148241c1c4070300000d03502da00e0300400110250740024400942e40e00107101c1481000c4101d1031002c162a0b06040194445006501094000302a220032100d150329000d802e00ca05550300c0182400310208441c0140c0c65503803060780000b82d480742d1088240c1d81c1c1c0069044e030105103240b0310340390f40818046c0001032852400394541b41e0b2a01c00d2040c16025035914040e04413484000e100e85444c0c020282017544180b1500404241d480c812035110368498945d806a11940c00c05800e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 568501573 1250 568500323 568500329
    0x1002031510020102120703090b0411060f0c07081c0906030509030918150103021303060513061d100501140d0c0302040c02010209010e030a11100e0414060103200d0c0207 74
    0x441c0c039155107003054000e4000e6220007039101c045981800010360403842070050241655004a444640fa1504d0341d4200981c950301c0e00c0315078030140900c0b004010440c804050100000d4640082424920702031245090030750440038800a440d00405010146070040f4101d800c442a900d00080c095941681d0309003180107130001c05520104900403074112070000c0010324060352441804110400218005400302d2180100d02688a86558820070101d492684101c0e40000410140750420015981d80411584244c0411480e40c20142590f01c1401c800c11251100e4045800104855410140c1e1400c82e204540003ea204401d41e80055040046803150240155400f0380180101400f00c50003074040e4014a21032070000d80742c3d404514003445c00080320f030f46032600583e0b001c0f0034a06040034043c0d844030f80400038051000342d03024900c45407102d11070072021004250310046a4101a0001000e5030041640c90310030030380c0c1030584c034150710303c00084a00c140030301c00d80000c60101074030090f81010350940c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 568502823 1250 568501573 568501579
    0x30325030e03070605010303030b1f03020a032307110c01201c0302090f0315010603020703050f031e0c090901270204090203060f1c0609110d1109061210020315 70
    0x71410a0400551740c002a0690f40300791414042c441c500000e00c038484244c0c02c440c284510440303059600075802980200101c04480c5808a00078070003002e2030060702060321801052480103420061026485183c05007202e04800c050402c0c480c403240000c01070040142c1840b56020650303a80d04400d00c0400009940762450390105601c3e0200030b402400079001891b4175809a40310300300c2009185004120aa03866420000701051a42408400c030020f401544040382409000c020f184e6000f5226009148031700c402c0c1c0f40e15480322007100700301d0b400b0103c083d2440818040920101095a9030500e01c81e06640c0c4a00d20030b8803608541c44004c1c080480d40c0c0c10342e00c5540c400900400d00c00010f030000e43c030601040c2e230711042c02d00d40303030341032010745d401440301030040d0101ea108120025031070350403540259002d840c00410081400d000291009941c0a0843e426481c5c40c05090450600c5101a6402101112005d1310107220300911900c4e9600320311508903155000000489010302e0b03049200d1380c5400a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 568504073 1250 568502823 568502827
    0x3060314070303020d0212030a051536040f12021f061a0708041503060f080d120618090816032c06090d030918060f0503030325030e03 59
    0x310304281c071001140410360050042c98032010501c3d00010394515401022001e4520359a0364850f050010038010305000b07a480d00003810441265101d002903141d00c1c0f00e10b1f20007020b1090a41248a110b00c0801035429145050410400855184000e05201c1a0040d08802c805031501008031b0070000c040e89400a805215107141c1950f805550010040c0c270304819000722120b02503540441e40d4001c5180003084110b0070007003406841101c0808900030f80040c100800d4040d03c500710701d0940034594021b0952030f88202010341e01e065010424002490307002a04014140c09c01c600c00c00410036001c2036030801c40c2c64249801c00c010200f0201e40c81c0710041c195640710710b02d45180c020402000c1c020846800d803410292400c0004d8101004100c0203001094140342141d94424008074075210401034043c040c0d080740028426003a059049180303800c405000071308600f001c104101d1000315070403a6000303a03c2403080202c6e403004450841030141000c034050500e200500412000381140505000d000c0c040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 568505323 1250 568504073 568504103
    0x30e01032f0d111305011103040509150405060f0906101803080c0d020c0d0201120906050c04050a0b09101b05010f021b0105161d0d11040612170307030603 68
    0x100c400380c0320b0000107800621082e01d5441c3c180c1c0d440d0041080c41c04540791804d904005940c040c14207040183e0400307080d01c0c106a6501e00080c44003104550520f807281c0e05007441e01d00c1d89080e1040300d512a03021a030003101c3c2032035180421514140100180e02501c01220015543c5000e4843c3d250311910103200c41540681360f241001c484c0c0c0003022201c15500c9112406d44801d4004290464400c1000d0042d980c104244d8004441c2e2044c0c07252501032040d030380e003413000104080b409514400d005e544140c59a8a1428050010030302c52a8401d0b24114000d000300e100694541c41c07c100c3c54241c038500700810051980b801d20020403101300040096107014900c07620a031180d0043c0c40c8820002002c0074408e56507000540c00d1f44c0b4210340348224601120800034080d4002e541045403480d80d0310010400351036100104406a40480040c1c800f80c0380c440c418517042c075150103903030050000c0710004100035010740d03100308604000380d0403500c84110100008648900ca81e00c618001d50708010200300800e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 568506573 1250 568505323 568505411
    0x3301020327010801050109080622050a0317010b0c1e031603030606090f03030f11030d0e030301030209090f101a1503041104051b1b030f0310090603030e0103 69
    0x70301d103055000c104070100001d03840d8026140d59007100c0640d0701500c900c2d81c407188c0d40d004000016480081c0c0340c81d40c080a801150041103450405c6210b0b440e8080030001c04028030341c820303505a002618015040042109840340030400d1600205070f600d0f040011915078004a09600500a5600c00000c8040425050603415008030003242c400d9200c0e0100380f602c070100325041a40900000e0042103d100514952901c1402600c26182c0204192402c11194002d032105982007c50903a95942c0080014000e42c9060030000e40c015030744030001d2100c01416005203456072901d0103d8082c0c00d940d1120801d9400480641c9040900b00904010002d2a180d01502c10342d081030b074003540c65007284c0b44804c0c00382c24940300c1c2600411140c4901c0b1685900e816200340301e94040003a401840c10f40d240740d50586001000070300110b40104204075124580380600514040196112082c0b4904203481040802d41000d100c240c0600e0a10b0003041c411315070304a90b03c030f542200030446510107540700c800900354 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 568507823 1250 568506573 568506637
    0x5060f191a030a0506042003070e0406090905330c04080102040f14030105010501050f1b0105040623010e0c07061508010c021204050603061c120201020d0533010203 72
    0x180040145440d00014071040700c47d1402000802c89803c120004031104210203194010f1907071800a803684064000710302a07404a902142090303403100c2804d41004400d02000c01404850324918410700c1007170301241c3d0756014010410b0b005020700c0001c41d882d89a414104c90150402d44025590340d59102140001200d49220b5214980c4080400c0e80c01d070b00c0d041c0140c5049034016995142448076801c0e035248150701003126408440c0500c00c10f181a140b081c080e4500c86c0e4002c1e500012460004e2250340c510448229042c25481400300041c051148a6998142c201e45020201500c50980c0d18181d0b0081c04544114200b214001f940040c0d00c41054010032652101c07135003a22045609041100198000c0780036465000005200141c4682410455100c0c4900c01000c004048c1090b40c4400c4158416052510010f0b500002e6a09108101e80a81908945100d11007030714000e0701e2031544007401407001c0c2d8004440b006aa4281030381c0c400c0041d500030b8010010b410454407881c0210401c81 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 568509073 1250 568507823 568507831
    0x911061c14071214070f0908070b03012103080708040606030605041211032b091b1d0402090a240f09050606161410020f031905060f191a03 61
    0x120110700300c05000f0b8240c01038200207482c0c000041c1040e01d4900b429512000c1d07040619041003020400001e48400070040e0600038218414034079940d5041c03043e410f0b82186105580440b5002011010300002e174440000f5901c90010b1a25955944917480c200c006040580e0014180c1410102413105200c40700138400800101a00c58032100d50801c1006500c90003001d0b000c1e03038042418034455042c40c6070006254082d0b400e0920000d40910196a0300f2140640817402c100c42d4084030701e05002680c42140503140c0c01d2240d4a003404a46026400620788000040104220544910851500d607014400c6064010a000c0a140300280c45012092140083e072045420090170b00c00032881a08140080350f1021042e0701c001407070f0525503100c2115280b82d04103103040030301c202516801c9041261002d040315042110000340e6070704010000b0440c1214004031011184d103098148426680c45624007845580107465140c000340100400250700ba00f6980607400c04203040d02d401c014000660300071441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 568510323 1250 568509073 568509077
    0x31d03091221090301020403050717070501021606110a231c08070c0503040909080c011b05041503020c030315090c03010807090e030c120405130911061c1407 69
    0xc220803014105a0300c0070b41c11074006008600360a80c940d042c0c002d1009100b0142c01400251400e5030b641d841a113080b14a502c41c43c545c4080c4403501e161803000b4451900106424802806201c0c1c0300316400e40307a42e40328410601400101006d00a001e0f10510240000d1500441d02c00480641c01c04e400354121240305684100c2c0c02840340c1e0070b03c0d802181c80c01e01c901324140e0756910440c1d40c4a00c0c00341d07020b0616500968580c4030a0100040074412400b40382100b41c410706a4544441d14404102c0c25181080344038002c43c5031148124154a5011040d01c0490720000544c110382d120400c0160002d100c0d6044d8043c89000000c10032144864072045102d9000095a04542c5c507600e11410f520980420300035070125802072034040114054503080801d22255146c01c1c4e910302600241c1e1285000030b00d02e501201084d011808203e54134012007182990141d100c814818581076170307a03c2003268214030400c4d220300c0000c10000201c16401d605414140c0c054203040141d40103180c005401d420080f01c4001c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 568511573 1250 568510323 568510339
    0x80705091801030c050a090e0a0206031e01060c060c0e0d17130f03050c060c0d03091707050706020717100903231306050f2a071e0b041206090201031d0309 68
    0x1485c5d00d00c1d4844c2301041c405150182041141541c20400583d0001d003e0717101c5c00101040300c2d42000380762145940200307080c0d201c7c035040e00040c3c41c028040e284172400c0faa09000008240da00544c80e10300103414a1607202c500048880300d00e2108141d5400781da48149036224102001142040d849880401502c5c0503404407800841027204100962207446104180c03070b04056841032500e80213070003540d2285d200b0081c001484429090740e9200f60850b60303064403298401c6008001d03582e01805010080d044105010b0007001c15002600c0e510014001e40040040e41c0720a0481454425468074180610402d0301d035900c80404095841690461100007036060a003050008030b5a00500072100080c2d04032041d03d00b071184a0302c6905424482d04000d0400343c00604001480060601100020f0442c400c603012090003042208800011140c1001c80c01040411060001c011410354020705103900c00c1001c2507000341840100d018004044107401c55159050300c0b01070401003c005050340d9001515040c3d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 568512823 1250 568511573 568511579
    0xc08061206010308390102121b0702012a0317090601140409051219020105010f0302060415020a0c0b0306011706061902011407020f060115080705091801030c050a 71
    0x140c07904428800140040c0041002a602c00e006179a207034044441d841516141911001c01c205030082e1010f1844c0c0c05940c00100b180c900514404002c0d0080c4a90544141d580c01c0142c10510b541f281c10400313414464001608490084007202c2d05801020000e80c10a14000ca450b0161101c40d14404001d03000c1d0360f2000090700d0990020700c880c101c5441d91038015807a10024180001080c0f0350106580078010744805100c0c50706144001c0954070600d140c170300c030a0009541c3c0242114010b0b006100011220501000540d40700ca098406840012018103003000c002c0f00c00740c0ca8a0300c111001084003160910002e51030756a44003440c800c0038203880704008038824080c007a40c00c0004aa0300d80e88454203000000c48450f40d040c1000c0981864000010241007050306650001003c49800006030b00c04114000e04110501a003030061019030b0030005c0e0b0000d10350b070141c440a402000d440803c8004104958150b030340f034616441c0c00400228841c11340d6120700708100d41c00340d83c1c0213a50103100d10100c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 568514073 1250 568512823 568512859
    0x30b070806060304031b120801080f1209012a03020d120e120d0908030108010b120303071205070507060920061c0b180106030902011e17040201020f010c0806 69
    0x592060600806483c80e681c0c40e0b0b80c040e91400101720401080440752841000000c5000481b14030048140e1107400040d0b150440c0a8a020070180307000c50305802111094110410010075901e00d800b0900b0002c6050000340d218910840001c03110030300070416014590141500030034902158030140e600c0c000f075000e0810081c001da84131b81203e18032540c00401e2120120794a44080d00d00d80c1550743d40454040e00d60384440c10160400c0e009000540d649078003200040c540103800c095a402120050740c15441c20240c040c1500502041c550641c507203e10000d40c40c0c5100381d0840c1d0f502503010074100424036507030400102c80881d5103030440740d2106c10051403400c1d150106c140d4585c42c003c1c01c07003000400794480c04480075004028400360025510090000042e00f00040c29000e08241d41c1c3c009231f09032003400010705814500c17a02c1201420100c4009002da41d0060390103200069034600d90140ea00c8030b1004030300e42030701000910200e51034038500d902d50b1341d400650b00340248401c680401c810302d602500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 568515323 1250 568514073 568514087
    0x90109020a32100309030e040c1e0216140d020607030302030601031d0a11040605040c050c16050901051c140f070f290405060d05180601060801180603021801030b07 72
    0x30090f800a010048604a54840d82040c07601c107219207450580c0540e541c02140548142c04040b0003c5400c01c0b400c1c10f08404150200b000c0302e1020b00c0288a406090001c1d207090a14601400d0203454088103d180d107034039a581c1074500c469000c1c01c040d5403003442d0b080c024020b4105580160000e41810309528140c85440c08800313074a401c5001800100d09555121351a0b020114841c64100d6100c450002f8a640c0710f1258410f04c0380c25072188d0f070369407240240007801e2000c6502d200c080350302194410300c1300c1d40f1480c030001d055607030a4032000e15043d81e0046d079100c01c1c003000300e0042a85851455413050340c0000704410034101022400c4404190f00c50342400c0c640495402080c0760143c000701c01317a09000b50500e000341003100c11515980b0b020b0b00d48002c50207652240303401095407a201d0060007460401c00b9141d0161034842e1001e040c0e6541007110042c840c44061041d441c442d61481801800c107070841c0e10503402150f0042200489111282c04843d819070244010303a01901c051000840d03460003502 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 568516573 1250 568515323 568515419
    0x1d0708010e0610110d03060e09030f0a030906150b041a12040209071205010e07110a020d20060705070812040317030a06030812092104090203090109020a 67
    0xc01111550307201c005100b462011181d07181c041180e0048120b0042209000503032582c5d21658002c54054100221400e0880015100d054164020030040c80181181000e07203409490700e1034007054202060404e48068800b000340003280800e16007000600c40c16003001001100c1c032420498900b1800c1d403140420900132250600b00c440700300000107005140c136181041e4400361038100b1301c0111081480307100417660260499044815104207011800380c0124040074180f850038011b00a2070070b168003003070313025200040013003089242d5140342c58104400507001320b00c0b500241c1a0760300c0e00018203042d03035a0340040c403c0d018140219402141e5035a010310444050302d17000504107110919069a0203403550008040070200c80c6d48000210008401c0c4004000462234500c3c00307540740c24680c00c414281809012501d841050302c000520b01c43e4803140545040f5044110300603103030369580c07410b18094080810003d500c880084004240600f00c0c80b0303000d81501c5040152081051160300030000307030758000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 568517823 1250 568516573 568516589
    0x1d010237090504020901140a0504030c1202240405060d0906060611030403110303270102060109020406120b03011b0206070809010c0c02120a0b0c0a1d060405210303011d070801 77
    0x410280b085050540040104080600d0408a9214000c020b8070031604510008400100005010030920224120000c042c2044000080304e80d00d00d0780c000743c3d1003d40c0c0b03e0b030100e100000c03140e507000444c8014107890003014080e080c159107402840d42d0230000c0801a03811502c0c145000400301d080d520500384c401c85c0881440c000c626083c110340301d4414409460044507810700c030400c004240311050138049050860401400c109801010700003a0414038160420700c01c02d44144400c010695100190710803448002c1d4001829200741800300b8090210000080850504225070995242e40010b80c0c91151101d540c44d0141070301c8081c08582079840c0c4c1d010030400074070030f40d800385d025160070322035201c3c402045000c6562010290351521000c4204564030300c01140003080d0001e00302d40003b0b299081c0076502c420854648500c0b8006a428007640c01007034016031030040c0202241200270342286c00d005045040729100d696812644520f00003c0800b045080750340c0340070481c1c081c000c0100d94140d0f0058 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 568519073 1250 568517823 568517837
    0x1903200a020105030406061a0408011d03091c061d19020306010b09010c051f0c050c0613080f0c0304090b180a023403020105011205030d1d010237 64
    0x10350011540f507000030b88151480c40ea0348a0004101c0c2c041d5012100e01c4066000030394076241303460703103060844440b80001541c1e031031500388040804901000b19502a5402c031003200d115074002c04040800712004c40010280d503e03101c05059103043d03400ca44003211034090200c50030f40780115994107075074040180081d0035522000050042c0b54a00e00075085264047c0341c40580d144194444038a4050044803040f4050f584940b00c4c5441c1002e40100142c881413414110b03c2c0154a000071a968000201400340d4990701e031910008001c0684202c49031018103814041d2100c0284002c180c6907801031003020215481c0060b030b281941407200c000bc24800c442d02c040801c5a0303501000700041d40c82102010684410403024943c04ca0f9041c0300007500105800804520b181d4510f00a42102c0d0103802114100044a03031440c00500000201d50410f0b82e401c6010400380b1b607131000c928000c2030b0035040016a50001c9003102e00422420604100c07078089150038641800c98840843c00d02d041d44256034006480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 568520323 1250 568519073 568519093
    0x5010c03140307030209131b0903020f09040501020c0d02011509050c09040504020604090612140313030f080d0504081e03070c200405191a010c1112190320 68
    0x3800080c660050907030801524010820002425140c0d402c0711003000720742e541641d010340703034039223065101e861100341003c1400302c1c02c1d500042d41d000c00f0391901500c1441000001001c20400b03405a5040f00302007411034010041003600a80a42000c1c4545202c0d0300802000040d020414020b860047e03d2154843e0301c1d000302e0b601070001500780100b0584c5c024030f041000182c5071085110300c00c002d00000c103d05100742c0301454241103000c00385442c01c000e64428000d40c03c0c1184042102801c0b268070120b0084020018540452180248082c0007640c0d89070000300014001060020701c1e02152490505104607441060328101d400700390380950008070b0890f40b50000603206011001102c0d03c1a960540380d080c0c100024054440c100daa5041c540c5901d2100d00c500c503410301681140f8140b64a4805140c20254002002040c0609003c1c02c2c08281d4096200c0c240c40703040301c9440d010100300980d90131103040e44000449084210301140011501210b12410b882c1c0c0500c201c8000034840c0180c0352002c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 568521573 1250 568520323 568520357
    0x609190209040314030109060f0b072d020418031b20040204170c1e091b0702040e0c01020c01020606060a0c17190e0d151109090a0f0605010c03 63
    0x10002c00840c1030140d500498035808800e8000340d8001d113415031000c5801410996034000c0c1c0c444d071743c0c4008502e00050240344009011003042d00d030f014101d40d001114001c89102e05049049100c280070750030030310b071400100500403090811011a07000e0344940c000401c1051242030401510036002d0105543c0010003104ca4025046c000d007104802800982030607280c84522000600100c0018110303802054809042d08001111840d010700d03401c06003425400420115890b4a001002203003403494002c0300c41060b442c51380507107010540289c401c000d07034070b8802c0719259030704205010741340988141482d02d6500e43c4001401d611442001c0c007494207140340f548050383d09150b04a81100c079003450131a14038001614001800304228070070410038200100c080041d00d02080c00d0710460188001c0ea60004c082000c503500031019140d07030800081d507007441740480902402068082d66001c0d40c18002c1c005148400e80181000b0f5035400c0d0200140c50340c0c0c00064070181c81c94400140400c01c1d011260b903100b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 568522823 1250 568521573 568521589
    0x1a04180633051e0c010c080f0405031903020d020c2a060904020313020d08210601020c1905150306090601170f0618010b070c0902181e0a1706091902 65
    0xc4080707203c0b40072918036043d0740348180c001d4002001035039902d001c150301440c1d1208516401001e0b000340740c00700b8105900c4080c5c40c0d10030f03020041c40d141c2c82c002a009003240309504940a16440420854480004104440d224202c40c07104143c00e4000350324036203402101446041954074010140d9180124803020311002c0d400082c88181114001050480981c80e0000140307451446494003a03900c00c040d20030701071640c0c518030740c41890000d01c000704005640c0001da0240c8030b5204681445a040d8203034408080c26801e50405500700d0380130f031281280c0500940186004101c00c613100f8802d130380c41c480111508a04540403055411217100852040c0090007126500000060310f01554044560805013201900b03900c44000c040d80000c00c0c03018846241d101e10050031a03004c0a500c0c22500700201140303c0500003040b8411203507050316503c0c170380d5503414180c11040040d00094245587d21410340b4078800c04044100c440c000c900000d00310701c80101d101402c446000360303910401126602402000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 568524073 1250 568522823 568522837
    0x7050d06020d0203010608040b0709050f0108091006081b10021e010b03011409062a0d0209041a18070c0803191b140f041a0418063305 59
    0x9a0307007001000400c1060740001d502810343e640300c04003581014034200f0707030140c40109a0340421004800c240080c1c0e07101910381c84c81500903e04000c3c1501d5000d103013420001480e9400c1c02d82440c003040001c55800114142400c6020075940038590202c0b14140540301c80354010b02030050304005010a4400082c4040407416032307980300000703103078145100441d0840314080440725076072800340200000705408011481d804a65580000003290752405a48603031803150884d240d4030480030409150307401e00c0c0c0d81503400e180401031050002c24030f4500c00020400c44682040d0151180c00924040c50190300d005a0044040d507891054108003a1aa211550006010700d80c00b02c00c060718460b0450414003440c0541d04845c81c80703a104032400703840a03103081c010710505450500d06002c0712640e100000266411540c3c1400b0440100c00a0040790b200c0c0d01c1140c00c403400070115403000b9032103c1c03000e0b406801591401030795542c0000120010403c2010720501445030003042001d1680352034840c001506403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 568525179 1106 568524073 568524083
    0x30c0a110429031501030809040c18030807080904051e070e030307060b0307120f03090509010302030c150d06090f05060111030d091a01080d090501050c07050d 70
    0x5a104449681c046440b03540a1400643c609010070034040c02280303103000b440d40c0c5030b19100c4120340203081081d01030340c0b4021705401d41c9030141da00d10740e055044005541401d440c546d250f8020350b114030403c80f00f00500b4802c0304c0c5c0c5c68486d4005c65000d900c01c0552982e110346820310090b0b03c0030f4020a41d00801c05c10210200c451740b00481102e0300c86801040c0402c800441c0000310303180c254a680702468114010704031400344011034000d040c0f603a100b03a5407104a0782d03881c0100b0001460a0102941c9a0049084654186841034619402000040704203080005460090048031495482405215241e000b403411000c0144101544035409003414140461a0081c003a600e008107050060382950324601c04007405140c09071004041940d4589012035038644660760340b03c05c05101c10340d02003003a07090040361540c000c0d016180ca500003403004008542c9801c0030800c82860802003922 = true := by decide +kernel

theorem cover : BRFrame.Cov 568345323 568525179 := by
  have h0 := BRFrame.cov_init 568345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 568345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 568345323 ≤ n) (h2 : n < 568525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
