-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0373
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:29:08.152388+00:00
-- url     : https://prove2.me/submissions/794d8d11-bf5b-47e5-92af-41bd5c40625b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 66906477 ≤ n < 67086333 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 66907727 1250 66906477 66906481
    0x3050706060f08030d11030c090d05030c0f100509070f140d08180a09022a0c0d0f0b13110d0201120507080105130c1d01111c02010e0304051c021206 65
    0xf1102000070031452800309414041c1d50780c14000d1503540d120507a00d11511300c5081020300001c0c1005090300c0c101c5402035080c0ca003000c4607040006e040c1242c41c01b000039079800605000d4600c600f20300c513840e0403919580c001c0511908089480714248100d001d001100150520740001e507981c1e492102e00d407a61301040413502d03038102030310f0300b0300d0004030701c500d00e04c100c480d03280c00705d0828502d10039550b01242540e20300d02407000d0850844011091038a90f00b880e401385c0c00c60b10855446540035103105c6445608100346050240c28192111350b0050880c030f80c040788000c107a1010560245407500142400c03140980d80d9001403005031580c3e070800f88403608444c01c0000b00684a600034a15504a410540e1481d4036000c054949000300c501942d24000400d01c5480500100c0252031001c290180040c100345070500c40d600310503460841c1402850310418500040e86281c0daa080c00341a14541d1950000d5040c02e04140004502c2108080004201643e64400f00159901c5440750709609005100340d45482c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 66908977 1250 66907727 66907739
    0x1e06220f0602040f06050c0705100210020310090f09020f100c240e15041716260705120d060b030f07020c01170601110f010e0c0f090403080403050706060f 68
    0x3a410a1081403601c540c6800c1c00030380f0a001d04107e8520b81103a4002d04945400c05041000601c0004800b03011403142581d1503043d207620344029405102800780640d01d05180c4010b601c2a0750001c040d000c0901c2c2008000f40c01030311140c0c140003803818111510444e50484070011104104c142101a001c5c11510890132030719942d84011007005282540180107211002c0c3e0b0003691342580d100c4000340380c07002c10002400318458030300f444d00038100300b44014900021607003920001c0303180d0031b400c0c1c642e031000c1c4000e0303d20300c0da040400002d2140d440f0900360401701161112610340703c0004140c42203030400a403d03903070b81060f80d0101016100001582d500c0741001e031040040a0800c40742030b00903208010300e071189907002e56174440c20b110a150200d0090b980e660011111344500310032603541c070310440075000320603c42800b4203644800d080000b401c10055035000c010703002c00c80401d0f40b40688254030030700001c80d07072014003554003d805091140e55120607180000091045900511f140d40761002c012450b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 66910227 1250 66908977 66908981
    0x100f050603011505010c0818060409020a0e09100303080405010e010213030506071d040b0f12010207110604060203030c31030b100509010504150803030f06031e06220f06 74
    0x800c810760081000081c15400c41c0c1d03c401c028082e03d07000c83c80081040300003405840007003010180300319080030400201c01c0840d865800c030340c0203105600d402080342c1070850751141d5102112071084802c0c00e070500380003c0390223502d0b0850002808001c600c81c00641401b400750007c080301c101d400000c654900445403044214503031400110b609008941c040b4842c1e520410041c048040b440d1880f5400f03110540070407005102c103c1c00716030404003280000d441551640700c0c2144a4083d1000581c0d5034460b803610082580008034180c1c498002480240149a40001501e501500c820b140c0344c1d440a41172500351000c084d502401f0603552a03221400c00c072001210444040b28460039202e80070351154100e4a8520007035001e5282c0000c1036000410a51505400404500c41194102c0120b41d45600740c040c03e5034011030701d01e805c910580b4140032542c02c0411164404582d8a408000142010103420f5194600600f44582c4118090045484102d8521030840c01592081218020800a00e41400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 66911477 1250 66910227 66910231
    0x3090a0e0105100203090109170a1203020a11030403050601060c030504090203072109050a150608010e1b01050a080126031603020d0c0519050304050d140d0c081605100f05 75
    0x7008880500f900c0030180d000000303480d00003605840f0000d80382d040000368a6079000d02044c031802c5125040c100c001260342d091110806104503940940e99103d040d0b009048031214514806003035000b00000c0000c10408141c1505407409843c0c0b8a403442c1c4241000c5070140030b6504143d500c14070002c24404007c0c1c00040440c0340d000355103040d840d000e0700524071200b1940c8000010b4182c0e0800146c0800144d030b02c094036088a88640c0000a034140c0b00c0d0040c40c2182c1d0011010410355021001080440405c5d4034140e42e40303c1d0920f480c4c1d2811052041c01024a1818410004400320941d024502c040c04140d80050024913041140d440c1d272200e901101d4000c10501c026009809000c483e1102980b080706802c8186420000800704c002d20b42c0300050055128103000d480310300003440046600d98581080f003204501850a0741d8604007546400785c2411540b900100501110781e0403400041d4140007626202e440c07120022042010f81c1c03d2032418a01c19080c07108901d403501c080714a8680282d40458 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 66912727 1250 66911477 66911479
    0x50f030a200309060a0b0d03140f18030c0405090d0507020301060510051b0303010503070308030406090b010303181d0a1d16080c0906030c0d0303090813080c0a0302150a0203090a0e0105 81
    0x5905921030403020400c440400e181c1580102c3c0c600c11f0768000ca40603405401009028211080c5891070220006243e50001c030444404007106091421a901c0d0402c0140300c406011078081100381000c0c043eaa90380c0c2e1410140b40180040843d4090956900703510a4008100161080d804c241d1200001804c650000e004c100f1b6031304600010f4048520000143d0b41078440180081a02d01d007962030302c1025403c010401c81d01d550721524040006104040110300840c86500e842d1030380b14000709240025459a00036580e00c004110900c0b12942d241007c2e681c01424a24000031000d5404600e02035030071907d41c01075024070628004050500d10720303405504660401c07080d212003805200c100400100309848956040d0703c44080400185081c03800002d0291090034005001034443d92088280c0e007104112524000440c101001442c00922030155106001c48880321410f0855000a803443c083c0500300c90310440200c1c414502074020012568007001c0181b51001599980e0389010104e1005d000c0c00e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 66913977 1250 66912727 66912733
    0x30b0c0d1b021009020f060f0c070311010212180d020301020d1103060a05030c0f0118031a04060506040509120318010e0a120801030b04110a030204050f060f010906050f030a200309 79
    0x920a08005440344000d140d9009082284080048042180540041000010b02c12303040114200000e401c204c84c900851013041c45200b03a00520b400a800e200c1c000d0182c0902200810403040403980344000e010402000b180e241d6900c15103400880e0090244920900aa5141c050840c1c0c00f181d1990103144944001c07034100c40e140d0b44400c28162109400c001240d0404191400d80410f90300030300000480c80c03080c4200d144604e9503070f10f401c00f2110a00202541051800c2c0600082c0b140a00460350312940c152002c1c0164280060310907a1060845542602c101000c00440c45601c41e011031000241007042c028081c1008070382e0705c0380d15184400c00454107500030500e450310050244204c5812a81c01c2403d04105540d140c9034015191030b690000355100000740000300042c1d88510a55020307501f084242d04441c680601444417002000325500d0501050703500030456150310100b100c500c2c014500055441f42c44111001000c1c02415401150b0a2405510303406a45005405540f05550300c03011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 66915227 1250 66913977 66913993
    0x1806100503101e0c0c0b010e01030b1005030606040902040b030106180507030c080a1808070303150b0306030c06090a08071205010507030c1d01020a150e06061504030b0c0d1b02 77
    0x940c03411582c1040002d010002c0388030107298104051307800a00b83c08018141703c1a003500641d030300b02405509802a00f4101f11200050040c40300861415502070240418002402e0070320700041c1d55610000c2050b44919280c5a0020864445400104011a01a00038011580c0b40d0014880e200303180301c070a2003000d10300300000d10440d100380260a810601d13612400443e880f04858400030700502c00d8450089110b4810039000940800020b150b007034080d580000d504880c2c240301d1801201654440c2c0a0f0705004d0041c042195008114a1501c1004681150b61204072801080c221789456110541071301034a800010500b8409010400c0180700f00000c02180d80e81c00015800c66490105841c001410720003034031a000640f4452110307848050044640e425500d556498000328903400150840e9110390480c00038140403c5016080401101c0740d2014544c1c114418501c0e001c0c610001d00b00c003000c1c0c00840d00840080342240d00d04520b54030306100719421403d803203200e46810030540c001849a484 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 66916477 1250 66915227 66915253
    0x906031f090f18110909070803030c1b06070815040b0a0e06101407030507051507030b1e0904020d021c051608030702181005060c070503010c081902031806100503 71
    0x300003080a80c00044c1300b5600502e501800011100103140c00224803d042c1c4c00700e501107040010714403460205100e59503620782c1c40d82001507000d06e03415a14040e4410710902a4440c0c002400e03e40c00740c040900c1804400342180006c0c003502c13100d41580c0e08040d14610120b44000c3c02c1c860713540701e01e4003035070008140e0355032074022500e0707140000c543c01007000f0030b10001300000d10940041405034052021100444585507003203d051000f501d0040c00300360b692200f4600c82c100344204c511440020800300b050364000b000404c00443d00140000e100d0701c210603000d01156a00250070700c4091120308407100303000c060318009688101c01a49560301104022000510a800004440b180c0c2d50117841143c20140e02c0d014610340311009802c90084d031040c15001308480d200d24010340a1510300f103008040052520052500316040780301071808201d4004204001c0c2d070340382001d003008070080140040e074968a01070121142c504403c41d551007802814144104515102a10405e60f8811819108500c414503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 66917727 1250 66916477 66916511
    0x6160201111506010c02060702100801030210020309010903080a031104090b0913020d030c170a05030a0e0c060a1d04090b090606030d020c0f030c04050108030309011b050906031f090f 80
    0x100c0c2c24801002400002203295105808075040188068404c600b4910325600040d003010003042d0710340029004030010019490181424200080b480c0080c51070103a18070002400000140005000c4010010303071840305500c654801c1c4844601010b00640300c91b1a0107440d00600440c13241da6105003525004241d04103100e03403a002c0c070654011301c80b42e002d96032035400752400da51500f0252200042b00801c0c1c0d0019031614001c100d030040c0703076452030f94914060303d50302c0c222a10140340343c605512001840b455030b1240740c110385074a115414000304007078030168080b4a031103809564581117400e0959400c10003401c9100140654500400e941041e695a805c1c59511401882580b006138801d40d8038a0181c10517820069601300b002c1c0560f550510901d000c2015100280d0003105254070000070849441c0c03081c030481c10381080c002080d500342400b2200080c410b01460143c40c0c42060300101195018150101451b0200d900301550b16695554405101c01011803ea00071181d9043c0168201c0000842d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 66918977 1250 66917727 66917743
    0x8030705010f060f06030f060b03011e0e0c0f03180111040302040e060c030109020901020a1a010f060f0207060e010e030f0607090f1203030b03030d05010f06140a1205060f0616020111 80
    0x2030130280b41c118500304044024284845403001c00b83c0c0d5810000c40d00c0700780e40c0f00039406050f02e500403200544169001d1010843d01d903000c0d002d940046400e00c400b082da41d0302116040d91034100350315260340741c200391414000e030030042c000c0d025842c00d80c2c4045034001010140045134002c81d403c0215106504242e501c5180840380b00750700e004104014002c801c825405041c9220040c411201003d640d99501c4180d164046c42d074903201b034020380040000c108100d01480c0038280c5464031000d02241c1d8071001c0e568080c980505e01c00c0c80501c0c2488203440c3d00c2010804601e40c001012600002203030000c80d42c9503a0b0580380600014903108010495041c0c0480d050200e49a10218119100090b01c0881c001d1000c1c1c0038131541400100700d40450140366005a902801051000c903008515141c0050000c0034500c000c41600b1409108141c3e006030000d040074140d040c0c00d08081156515040010021803009002d150301c024003085e1110b945c04110910b160480c401c2c6c81304100700c0991010140e40d410f007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 66920227 1250 66918977 66918989
    0x90c0d02060c0a0b1602190201031a04060308040512070b07020603060103090515010e01090902010905060304050114010807090609090f02040e070503030f12010815131a0106030504050c06031e060a030b0108030705010f06 96
    0x47c4409005521a60000045000c400c00d80d10141d14800005825208107034401e4032038400120f07040c4068a0801091808800d50a00801c0c0346841c3c41c0015809019001001e4424007001c400140c03940d0190300034001155000c001d40e2550a102050105d0301b00c006e00500100303c08600000c10598080d100d0a55443d40503160040910b00e0102086196800240700304c07a2035482e140d01e545400e0440c840d940c042d015101c081c04030b06041025800455503c2d5121410f03590800a8101c082800d401c2c40c6001d15406a802003942082c00045034641059030b4481138042c40006a4103800c0f075005005840005881481d110440c1d03070f0b4101c456503c07008011907114003003503180850390301e030002d01c00303030554078400c1c4e02424000d0800161620f0340b0b03500740e101001181c0c40d24100400c214041c004008800c20488a0358114288440320384002d011780380414008101034004900142c0d07507200742034001c541c0048075580540e111480c5981b607401044040701c1d65800c121100c0716400b254011141a101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 66921477 1250 66920227 66920263
    0x3020102190f12050901020f070f03030b0108100b07020102010905030d0f0e07030203151902070b0405060f09190302030f040807080f120f1b0109050c120303090c0d02060c0a0b1602 79
    0x20f800f14075400108000b815078a800d66007000b4595000c0c002001800e81c090040040285955203400c010f800d680c0300ea44401e04001c02001001aa03610710788840058500312181c054803105580b00513801441126005006444003084441403c42150800400148145c80c1030100152039000302d541c80303040e0f0000075459005200c02190300070449003c0caa101d03200005000b205005220203a0880c2e0002000f81c6a105400b4100b00c140101004120382060715041645618030b402d070340e69601c035010707800e4101071407800d01030440600d8420000c0e582c0d0803007502940d6540e1560380c450540d40720400d209142c1c0c0350050311000483c001020a490020303100c441110f619185051a480c11030f42e028105003104403011004402c0c0b8244244115010705105038024801400d100003001822603d400003103c0702d80c030030070800141050100b128400c0300410342c0d05030341031000762002030101c1c0915001480d00f071056040344814402440d045c2801a0090b1104107440c48011008a880352000112404158 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 66922727 1250 66921477 66921497
    0x10c0b0406090219120c0e040201120c0c0605100906170316030c0b0f0a18020f040c050405090901020307080f06010f141c020403140703050a170906030403020102190f 73
    0x18042c0d00200721081c802002400c841c1c00b1082100b4040240342c000004029a03100c07004200817500c03050310040e1004412111075843c0540c0000c2860400b10605000d5944401c0b10414060141095800f003961001d42884a8942985503c0c882440c0d4030580410358209030b40011140c60ba285445603030000d03c8095450218081e0040a840652250480030040b0102d90fa03404110140d101900a1010410819090411950075010b85031405120711601424040c0340e00142e0311041d503c0c00716401901e020400b0058007106840c140155880107030403002410400c52031075810350040d4842c00c40341d2288446900d5450300701600d048100d98103408291400184400300b07015003560b840a0b00100d500529083c00c401307051000000c820040c0754419000f0600340204000d1040703d04e96064508000c2c080c551840d26a40d41e50400d005020b46240c9200d42c0000c00100c40100b19082100050303c00c99807800e152400078003d500030002d1141c1517100e2008500610b10a0b40100000003040d41c0e000358038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 66923977 1250 66922727 66922733
    0xf090a050a0b04030b070c0611030402150a0f0e04060b12010303030f020f03061216080c011214011a04030209010f140d030203180f030601030b070206010b0c03041818060b0f010c0b04 80
    0x480d029286d41c00380030a0324441000a034290244140050710703048025224240792041c010460320703101804251000c240308800300d060f8480c515025804842c40e04000007041040420010801c1d030f0090042e0440014002e0110441c80d519603042b43e1283d641040701005200c8408224020020844001c61040000c61400c0c50a480025210815070b801c0d15024a800c060b20398001210b40d011030002c2e00500000c030000d41c1c008049800030805180188807105c81901c01d880300700310500a0030307050b01c6241c484500341c00311401581c01966000d00f008011b9615a01e038080d104c0203611600e040002d40b9034550140781003d041420b421541500218200444503510b00ca801e2810381540317802100880070000c9580d4208255402140541409152404d21310030084c2081c1c030513041024118400c1002420703001002003294120f4440f000305a00240445040c070340a04142800c50395540030300c10501d018011540d0080c8859601151216041e032200001501da03082c2400c0701074400042040044c000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 66925227 1250 66923977 66923993
    0x70b070f120513171014042603010602010b09061002060601050306040f151508070e01050d020d0e060106180503070527041b1a070312110f090a050a0b0403 68
    0x19030340d01c0d041140c100a480b0b0005086002240d000100e100c050b0100d038150f0340c100380242e1440718107a030420f101c0040e14542c41032022402420040801508010310300c03403084e000030200b2500d50056071140d940e50f07544000030f0180000d0340f101803140110801060883c80c0509480c00c1c1c0e01030301c3d000f4140c01c1e40da010040d240b5820052500d600103451340c496440094041c840d200d1983c8403408806403a605101c080040440703400400010300c50030302e003400b012a40100340456501d8007482e004c0d070b50b030728110f500101a02038400034100e5a8100140d008042c480032841606036151551107060a20380080e0005c0300032114456981c240d003201c18103020034104443c000d00480500040a0003446000c85901c40b0b501d4210b40c00da846030f0048000e44509511528210000d0440c0d03403a001c2c402031245600d1200d803060b2000102841403800b8604000112071304404011131b82e80b4421500c1e0801102550a66405142064071400ca40e2101141a01d40450b003034003920354540265050070b0940d40c1b0006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 66926477 1250 66925227 66925253
    0x1508070311040b0309010c050c030d09020607060e010c020d091d0903070c0308120c04061706030f01060f0303080a020f04060c050c101205092803031b020106030302070b070f 76
    0x104150319079151100700511030000344010010031004940d2440d1944166084814101003c010404104801c50302500000159180d040145c000001c403101c50b0b2002560031f1103102c1d40106414100000802542011741c410300d1282c0c881d40036034059006514089910811a0080f41c1401e001b40718907201d0460000b4000d075001142008a0340b40082075202c0c03031004103142d4003c80c0c1c0240c0010b07441400e196080542a04000450070aa0409061140140c4800c809106014100300a02c0010f00c0d6640c1c20425010070231004d80081001d25224035200d600031549000a030081000c010104060918034401c940210300a60386442c249418004220341c2c1c0340d030800044e01c0500c41d640d00254070750f07036460241150625a07100d00f13003804c004507554410b50304001c1c1214099000184081b0801c810f90b0440324103039000b00380b41038801005190680061000c2d5006151100040410a01c001c1d0150300c003070182c81c041e80841c0c0c50303141d0f01d01d002502d0b03100300d46004010410ba1141d50380000d101710300b001303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 66927727 1250 66926477 66926491
    0x40b01060c020d06020c07060f03020406020709020f0712020d0212070b011403100501090501051f02070603050c040803070f0209010510050405060a0512070216050f18060a030503030c03010e010605041508 89
    0x40800e0b1044e440300d03001e030307041000d00640c25000350300c0401446030040c81d5014080c030303c0d0a0540c2481d1070042d000c1c1d240d02042c8100712003640c0010301901082c01e04400c4690195200150328400e00b0301c0d0f50025510009944204c0140c812808101030380358070502900e0455500042e130790b94503802c5c8121400220448261aa010b1148007081e07200c0d842072303028543c00f80c90b100070001340c50b614080800030040303101c11180000c251520120303400c070b03940407036000c0903500e8506001c10b240e165048080b0083c415a8410040d50201166500400c0380c039001040a59001729850002d5036203510810a09100c0100c200c1e01043c2c0800c02003155050000103041c1e10342e0f5a050150030305002a002c641e4290048802c540160068800081c9200c8208288000b51009a40c81c20940f40b00381e003c60b0107480f0424140c40c0980c40c10f17002680340c0d640d00340008007031940a41603948900300b250301041150070130f010f10302c40c40b00700400120f1894407410903901101c1000000d00041ca40181c0281d0b1108000f9200ba = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 66928977 1250 66927727 66927739
    0x309060c02030a0f0204330f03080324030d05040e060a080a06050601020a2001030c0e06040306021b030703050c01050f0606070803060a080d050705070f0521390405040b01060c02 78
    0x10300483e8100d26411810001c00042c003021f0385400e8074060040102e1a0000100f11840300c02c103001194240060300d40c48082e6030f00700c05541c4111001007591203001d5140e40da2600c5900d00e000441da03404030143c001c0718525150341701c0640780c840030803040c10954002d105550380044600c40c00304a60350882d9400c8041030056409805c0b00b510f44845850301000022503508500d1441c0d20340356850300c60764400c2e00c1030f480d1185d5138491031400200310b0710552102500c0690007007051000e02c4150003483c0c0410000070102d0b69107540f03a00d0f019009400030b200114455280200003610b4034080401c940c819640200500c2c5042e81540d182078464001402c055007158040b40d020074100710800c0b04007911415070325074070b07100ea42900e4060b01e00203050308400078030800d010041140d5182d0711000100d4449004075103e100c0c2d0b4040c4448c2c032b0301200e01e0300c10010341c0440802d004c81110002c40941c0f43c42c00203042c00128000c140503c420344000741c8000304000121401049082d100700290403c843c801011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 66930227 1250 66928977 66928991
    0x1c050702090708061002161202040f020c0604030207090509060408160209090f4c02030c04090b0f0d0605070e13060608010503060f07030c030207050114040309060c02030a0f0204 78
    0x49244070314100c0d90388000c6010b84040c09400e2400c07440318040e00036144000c00700e070081c05250592200842c400c120064110102c10811556140c00c82c03540001c01810840d141d542503655a41e80f000140c40640141c001c006021442d0340b00b23401010312551040700140219102d9a0714440194410408403401806090311203005070f40e00c4248a014520800043c2404145e07030b0f880c0c608205000301030949600008450059003042940b216035410050480100c550310304648140e10b0803151007681107020310000805c45018881c0b00900161104004100030417003121003489940042d0300404c592116a401100c00041d00035000968031520034904004038101d000b000c9116810320b80c0e0882c001365220780b01031103101c0e07000003420b0041204400074142c2d401c2c6002c8200c002c0c040a8a40c0080584804064101d1800b80e0101c2344510b40c0600208948031074510f108085840a581c03c44c001803102030000f411070712031181100e4071a0020007a00701c140c03160b50340242034000540100c0c1c1083e16140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 66931477 1250 66930227 66930229
    0x3080c0a080c071e0b01060e180406020706060503070e0a06090507021c0203091003020702030c06120a09020f13090311030c071806030c0e04050d1704020d0c0305010627020403051c050702 82
    0x5195040309210f041441500d504245000e04000000407000d40540c0165074140c954001152707000e90015008140103994071003909110001c1c2c0b40315082150180318006002880d50220600c19106007960081046001d440f101014140c6070107032243c0300168001b498070a0a141c4600c6030002d03c481c1401140d02e0300c00811b000c900542c904078007a40110740e0100c0e41030150f0500f4400845802003c5031101c2c500410407500210401020340117007216682e031740399101192074504030402e00400c0100560601d2001031a080007501420744d045000840765420030303032004030020070754803a80b0045020300080c500f01040b0415021010f10003200442e02c0d0f100000c0881c0d02024800040c210210b81d81100c0c2c501400c2244c581210f00c0ca407001084204c02203a041c5885090510703030460ba040300c612000d070003103051032807001104d41c1024007994070f4103000081c0305c514140764ae01010102643c600b040ea85101999089000314800502203070810901c40000382c0110000b1aa171107030781e0601a0801d11190 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 66932727 1250 66931477 66931523
    0x1140301060806101404020708070318030b181b06030112050309120312010605120f04030e090f0603010e030306060f0a020708030a0314011217031b070f03080c0a080c07 74
    0x40c4080c020110544d900f8045454089034102c0318250655065140044907a07425146124054019040111904880710404001605900159000301c907a44150070200c0c2d141101d0705103d04070440a01c0362015100c10b003042c5500c51404d41c2001400641035030711382400071181810001003156140010440302c40140e45004000380b041c011600115150002c500c042d191501060700010103200041c441030020b4110009070380d0f402200202014241e41b51443c096890403c030510340b6078403003852020032221b004480340091040c01d0403802485151840c402c515202d200c00c0c3c1d01182c014404201c10f901d0040540c0080c41c242c0141d05c12994000e0391008030a0868004500c440002074030303040080c420101109200d0b014051800080304407806541d20740702c40d01c20200700e548010304044000703030040040d54490004020040364859950255249c01260040c0d491011800305a12401242d80d80c4014003d0307500e10307000e40c1c0f186e5001d500c5190ba0041e094001d90b000b00c03004805050058a11a062 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 66933977 1250 66932727 66932731
    0x60105160b060907090b07030507060609020d0e06010909231203010b120106030218040f02090604030b04020a09090c09090807020406080303090d030c0c0b0a060b0301080709050901090b01140301060806 88
    0x18150072545410040100441c92401400d81800c00035003640500092a40c003044840103035040c20303e0390b51407a20345040800b9001c00e900800c4a140b003c280c0300054611904140009400e46094481310380c0c070382d10264102ca400900c05440510940e01c000c17041d0341508048034040d8025411240291841440001258403d1300803451002c004103503004264008a0004e015140c14103003035041c20355603007400039205c18900c0702c02c1c85036444144540c00114213904807502580080e000e81e680300d44030f0038409034640040d00d00720302500c00e62000096080d003900c10301c510164010f50200a0901e00803640000c2c018440b01900c100c00c2c200305074401640d03640f1071940140100d101558407807405000e200e080944080c0e40200f4141095090030345640e10034442d80c0300d280c5c08441352500b40c860308190300080081e50440c4803510000800071507103910005000017107a01c1d5442c01d2001d50368100c0300600381c0e0560100200404a80d0b401804140d1661070103080c41c0201400014030159900b1410b0310304441 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 66935227 1250 66933977 66933983
    0xf040504061205010c0f1b1b090b0102070b09010527100f02010c0f080109020a050c011812050c1e0c0904120e01140f0f0c0a1112011a01030506010516 66
    0x2a00b012000c0140a00455010010350300307140c82410402c10b40a815404101d40c800070b0411000100001c00400046409401c0000f00c00d203001ea03501c0f0700c0e2920040c410503c05601511408100260b0304401c41c00300d98003a0750680d207403410110b0100112514074401d2032032080383c0c50510b41c046001e407900781c2050202c848903640c5400100c17140700045d007150380c040106403c1204911a0186258002c0407150448035454001651501d0414040fa114086c19603d01015420150140c500b52000a070628601e0f00405141036000e01c240410b84480c45149040011a0000c0c0030215801c854141214003400000c0d0685414079003000001e00b90304421030302111503003c01020f2801140d031040010070744076402e0910130541c0d92000c000000601686040b0031b038001c0c0028091054400840540320841c8a0100b20341c4241d250f0300e0456001040741c0c2529014154619040d02c08c0c200500070088043c40c00380c10750345020300040046001d042c006000d24188182003003c1c0411340580980307001c0c0140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 66936477 1250 66935227 66935249
    0x30d0513091e050901181b0f09060602060612070509190504050708010b01030e03090904020f03030c0d0f030b010c170417070801050a0212010b03040c090222080601080706050f04050406 81
    0x160445902e07040340d4003d0507030b0343d16a05d03085071441100009030360500c01c59004640c8401c0d019200c2800a00c004294210305400c8601c01e4001a00d10f050b0b801c54416035207281c007940e406603034140a0044c040e07011111900b5a60000c682006103040c01c01c002504208030319004007002403104c003a02c0030348000365000c03900342e8041c078402c001d03100c401e105107907410100340703401d20a8150300013145560303000356110b8511034000440803c0440d954005041c1d02c1d00e01c007a054035101e92503000c3c03c0d40c641001e4004040031400510040e220140709100e17115010405840310440c04000b030b200d450500903103070018040103004000c04907a0400500d80394107021a6140102401e504180c883c0742500c2015001c0020039006001060040c00514021410360344080c8509880c3e682d03a04100c150101c423a0f012001d2036200142b15580d030211031712801c080c0c5140c003505880807680d41c800e26994400034840e014035074004e907500b44403480c401c1c4000c20f5440300910580341002c0c0c5601c0000c2c21a00c1590103924044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 66937727 1250 66936477 66936521
    0xa020f16050f06070c060e0c04050f010e1501091502251a030f0402010f020a0204020d0902010f091a1812010621080406051b01110c01060803030105030d051309 70
    0x1190421641c2c56049404000e40110708000c41d0240114a41001c011701080c0c07245a1490000c504002d00594184000c009104e41d08080b071015201c03480a004482844040303400190000b17581c001901c0801006030f6400c048503141590f444019211a02c80e030f0110b000306448003456049105203007142060031801220020b02d001c40c40d8810303045003201003240307a409004211000b00c20200240d400f0360203085c149186501e80c00c0032070401302c000100a50103840420003039460b42c40d65104080b00c034804c0e01c429450102e00c020503503c0c00c03200e10034554940c0746088020b812400800160042c3d06013541c1d0741c0003060400d000999007503043e06085803c0da41d103a604008041c0752040345142005240b00d100c4070f420850f01c030011244228010314080c0000005c00e0040c01f412041c400b41c401d80300400130440ea04021505000950141d4110803043d8203060000c984036501004480c101d820090082c07281c1c4840e4030741074a05402c50034038844422107a0b040000d803042c550085048a16096044000c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 66938977 1250 66937727 66937733
    0x804140d180e060a0311180a020d0b01020a05060402040c110a0b0f160903020d02010905060d0e060601020d090e04020307030b16030f0207080313020a050a0b030402030c010c0c0902030a020f16 84
    0x41c01966002e240442c0d904024002251030362004281542e41203140c0000700d0f907100340418103c030181e00c0b84d545aa84804100301804c40c0c03a40c041d00108007003000074080605000012a81c0d00c81c001009015071f04031030085401443c0035848094400842e050004254000f00c1c0740d0b0741000e162540540e07005038010b04106880755070b040900d90102c810102070554039070306000184008001c0c00001c0c0103905060115040d07a0080503050000d01c3d0003400656914000071810002d031410440100c0944540310100e5840c0d800410090045156941c4607410310b46003020240c035126024100b1b03a014000c404001c0301050340d00000b244200700460320320350000070010300181118030703481c0070890913071040c0a0000000e0713150045980102a00f80703544c13102c442c58000a4440c00080d44040c3e44801080d6000070f8100310f4901951041c0e00850540d1408505d0800649955100f61801080964025020301510f003090340a1038101c039176454010b08094520780054410760000b4a07603012248030060840030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 66940227 1250 66938977 66939017
    0x50402071a010f0b0d0e070320040f0e0a060207060905030a020d0801090218130f0c0f09050d0807080c010204080106030c082e0e0309180f0703020c0303070804140d 72
    0x14040c80761120f07680d500c1c01140d03104038000d0031001c6912907298290780003103200070400c210180d904003201880c106500c05440075091b01c005141c90083d070810b020801110500d00c500350650b6445000b822440c0d01541c0c800000758415403044500a80d90751240020034404c001511112100c2c4d001004800074110003e4a100c0059000c6008680100320002c1084c240745030681060500740c1308206000304801214020b008a04a101120741c81c11000841040e48200201000004ea442c2d10300925250428000343d0003455601801c0000708000ca007000481c0c05004100e0210305100041c20316850304200380c25502d460344140d415081584c01442440820b002d800310100310180c4140082000c0c420154004451081156a03c0c5d9203440180843c00305008481407403000030300307021900034502984140c03d0000d4611a00c1c51410324000313140b42e07000f4402c40319000c0210006505550301c0e02c3d000c0306c0503900204119422429480f40460221080040c0c008a00c07454403280c001c0604580010b40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 66941477 1250 66940227 66940229
    0x109020a200a020907020307050d020105060f2413090609050402090f2401020a060f06060f090807050904021c20040b060712030b0a080109020114030c09100207050402071a01 76
    0x200300009190480c1c00840001c080d0305859043d11802440da40300207060b403e50040240241007801400010304401d541940110f200d542c04447c06d29018200a05014640001e100c802c010103e18150500d009100d20020b055402310801000742034a8a41c00020b00781e03006d692048840b030b030311903040c0411458207449042e805040070400003098074000000b203581e28200d182800b030350440c04440200c5a4800e1102d00c1d041a08402e051221502c103400c4d210081070544100000603a00040c00380c2c0303d074403c50303504d001ca45c0c50a00503d907090401041081080d4040c1049a1000b11b0b401c1003000c1c91101c0380c42c5503007140100e89403a0841e40228840c004204011045031196180950540c40d07603454101707031034841c2e0704003088181c030350ba031144154010b02040d0062540400d080a00182600b4150000100240b00fa6607841e01c6c103804451700b8015002c16a510783d190503003403007001c000e03050040070f00318555a984110b40380541d896001c101240c0c000c22065170b81021006181d4030410405030824 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 66942727 1250 66941477 66941507
    0x1030b0105060708120a0b0402210f04080409020f2b0518070902090409060509030705070801020a090b0904060f06090807080a0308060910050910081005040c051201140109020a 77
    0x6460b090312640e400744c5612600f41205000e541c0d0a01242c01c0014960008864102c003820456a400c5140821103000d4000018118100c0d0341c500000d2001080021541c01103900c005c6013400c09050005a102a40150902507d00307030080c07040ca14140f07450328002c1020f060110000503036854414425090f03640003000058040740fa82038458000c0320014030b120444651110040c1c4501403040050050140d900029000508010a10040c1c40010009258140c8603100f2a042242e0303c1000900340c1c001d030345421021610680c802c0003644a013038020025000c0041001490b0b940f41c107800c50102980d40c000c000003d496107020b002a82c01048048060a0501e00030907202589660003401808001c2056004918000101e24010f85106064000c0d02c1c0040074410203240480f440001d00c482d600c5012843e22a5084020403142c0501c5010301550300145a45115806c0c081800440b00304880b60862566030341110800007161a02480c2c080c049584016170340315848030f8000c1c0310f070081585507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 66943977 1250 66942727 66942739
    0xa0b0f010e0102030f071103030c030408150114010804030320030709050109030803131b06080a05011205060103060c0504080313051005030124050c061501020f03040b0d0b03010605031501030b0105 86
    0x501c445070780020544480342012402c5c19621401c5160540041181d01c4000303815120102d01081000c1000c0090f000f914078120890f09102c8010540003550107080c0700c0e030300703000351148a140c4183d40700f014240c1d4480d002e03050220300c1c016200d95200d203802124003038042801000c401d000400d540410b0040050000340307005110741c3d055803140210f03480043c101c12106500c1904136401c0010b40340301d17107c2c8003090310300c0307040015030311a0041c08001045603020b02840ca024000b140d594115004c880400350008014006030782140c0c0da040051241180d0a0180041404001519107042009100e249298a007a00c19a4948820f0201c6070080d036000a040c02400d10041c81a0758503480d59811508903242901c51250074480d00f070301c40b80700b6900d41c420240540d00410140303941c040c55282d024002a422a482965410181604d0f400785000d81811408200b003403c0d082c1c82c07142c010412014000300005216035690001038a0100200b1290b40140090401003051203042040c81e40100415202 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 66945227 1250 66943977 66943997
    0x6090d0903080301050405091c0201020d060512030307030b06040f0602070f08070e040809041e0e0c0a120201110f2b03050103120f030b0a090905071208030615090301050a0b0f01 78
    0x18040b4a000500546004690b43c400140100304100400303d004441c88200328482d60100c60028003035840703604204155410f1000000c0c0c80c0c240a48403035916041c1c003018500316128402c0c11000b800107142c0443e4850310521021400002e44107060b00181400d800810005140403480c0325440000d0b03001451a401580302001b00440007001c45034070a60201d03015548030b03800030004008000a411800c000c00485041e4114000340b82d03c1380c0502d03212041200c8641c0010070400c2400d41480c0600700c0782183d40340c0c0300d400550213628101c3d03ea03403210094561851080f50301d40c0c502510b0400308209030340c2c140c50000303402c40d21800d001841181c46c90103126560640c2c5403004c011074003051120401c88415801a1074074400d6000d12428100200700c2c81a840da541c000742d0103042a1704c41990b83e40140d400028524104120880300103622244d03407030645c5d89446c101300c1220581c031403081c100c2030208501030145d0750030300c90075114214042000410a80c04c40610501c0080e40380c005040c0081014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 66946477 1250 66945227 66945233
    0x70501050906091203040303060f1829040f02070f11011107050d02060c030903161a09091308070503031918021f02010e10020403060c09030b071d1206090d0903 70
    0x305102903440c20303100c40b17649881d03600d02200240724603070180b0b88d00042c0d004042081d0001148100700b4842d0400705006030780b1030100c030700c10360710080f00350482e01000c080c003000c03944c2025084030500d49003100005050441581b142010054146401c0b20907e01d000c10011056802c1080c04503543e041000400707020341000007050f9046240c2030041e100319004213030403003042c0d003c00480e40e44110150030b9504044030303602001c0004500780560f071421080140e46050303854040068607000940104041302c05c2d200c0d550341030603008103000159078102c82048258040b0f00204000e5020385101d081000c801d1707803288950000c0301c0d0a0700c1d098071481540680c0c900503079240c60500c1640030303940780c0c07140c00314200c020140e005009952840380e072401401c512031041c01090f070250040f2030050a0600003009240002c40c3c071900355001c0141940e41d85400b240720280314000203840840d8140c041c0c07190180c10000500b2403280d640c507062a03a407042040103864001844458040c40c3d0340d081812030242169 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 66947727 1250 66946477 66946483
    0x40506040803250906020d021216060605030322060c03020604060c11101b030b010903060207080f040e0a0f020306030703020f131407030b03120d1a0901080307050105090609 76
    0x508080d042078004008281c008462000c5240610b0607441002903520040c10060103500d114071411000d070080c040350605203070002ca1400203400d1400d5549103099649002e01d08820010f60054992594501010449450810050044429503003c2c0c0d80c5040d4a0740303414401d18945c4c0c01c01d404000c2d0b4040d8260019400107049900300d503014901081103002d44100302c80d22000304404481030700c5004900365404480d40c1c400584294045502180146c810105505a4481e1983d007400542101400c0001c03510507400352803900c0c1f080a1443c5002c4e07450400d01e009401903040804484850820f010b4622414822000840e914003015402d6150aa0000c1d4403228580b101078000d0090403410016075a8680c0e001003040c0031100100541071f401010544029011144140440e15000902c0524600042c82c002c00030031040c1d105140006049116001c2c000c40e2100010045c2280d40480c0b240c0c0c0c41e51905406848150015500c5944d207050135400e54102030580bc01c2e40d045401403101d50030000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 66948977 1250 66947727 66947731
    0xc020d0c030e030a0b07050703030518070302011d060301090b030606101d0418230a0b010312050912060a0b0a030b01031101020f0604030305010f0b0c1b03010902060c0309041103040506 81
    0x5092a40b0814503040100c1d003031089000307009151220210400040e640c22101400400e8000e5800300010307900e403c00490342c013200c4898000190301003102040150300c61a11701540c40f0b0072404c3c0000c01c102920100b4040e40082c1c029016554903180b030030319907007020080e0790340c044001c0700c1d103d23044580c200c0c0282071121011106c0300311104904c120222900c85411a440707000100d800c1d200f12042e03034204a0418424040d5000400414114168811800207421440d140c3c000789603c04a9185540c0e2902d0804880c1c4648103004042c4040f0342c0c03941d9021058045002c20300050401848c18203425001c45442409003031164100403014000b01c0e012000c401e042d01e50115100405d0502c00006034030700140d918181070544a1241000101507041c1c018604130f8107480030100c62107494045000c0d05014244004140b94442140d852201c80c010010b20300625015000041d45400b0340c020581d030703520909440d02d040e0b00000745d00780c41f401e1612682e0444460729403210700f1420103170b803410b48444c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 66950227 1250 66948977 66948983
    0x9042906090a0212071812060e300702010309080c0601150c030903060f1404060b0306060603090c01081b07030512010501020712080304060209090a0c0215060a05060319020f0408010c020d0c 83
    0xb83c132480b8030081c8036003078000c01a0452010301c5101d12440e00c2c181c6c01800602500380c0380ca004074003146e20326000340d1500318290113130321440d00e2b02074200d4002010540c000c0c54050b410152504500004107141c2001414140701c0c14024080640c10421f20070030b40030f0b15440070810041000d003d000401e52012020003640d9024034082148014201c104001e4010040340c81c4200300c108081c802004840ea20040c6100400d8050710002d644017820003045010444100f20140c201490052866200740880d03940031031510000708ea480001c10640340c031608205422000f1640c005881c650034814040201d004040034230040c0b5085040080319042000320480007421041e010000c901040101d4044c3c82004034090160081441c00080a0001c2c00c6000c0035072001d409186c0001030303415001d910f00c40c45014003030486c00d0007910b40010b00003a540024166031004109000c0030710600d8880c00108803a902c05840c0c2c40c0c5540c01c1a10203405c441600f15954150342c400081181d0040e000042c0e80682c0d50 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 66951477 1250 66950227 66950237
    0x5090706020a1b080304080d0f0804031b0c0305030a050c0106050a0b1207092313050408030c0a110f070501260a0b01110d0801060908060609010509042906090a021207 73
    0x24160b11810700c4071804c0c0c12019141c00041008120004000341e4007080040b295030384c3c1c1e4188501107050f640d08500f91009800078141004640d039a0044107a00c903d410f00c03840003e40d04594035254a42035401c05070000300000c00014600b0380d034500034028000a072108450301c40c0b500d0702c3e1103802007240c0303d11010100c3d00c4010100003042135001d07680c0240180350020f02e08171052980c100191480424000940c400d207800c5040305c104140601c0b4075403045038400e500603d15101d000031440c040c1c001b03580200400103a0003900d070b1040b6041c000310480b2031942c0018190181890300142c0082d071506034420301d4003090f001102d20810906e000700e421412a41c8000b801c887c01c440100c8074240107450322041c510500c00d1000c40298400c0d1024100d80c81039542c03800e00780c0c0340c08260303845601c2614801c1d4002d401000501c9185031020b50581c01610580d0b0710030318402401c10f80c0b58000d41c039005440002c05c28500300085410200003c3da80302114180c110314280514840b091a441c000d001d10b001c05c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 66952727 1250 66951477 66951503
    0x601080402030f03070503030121030903060e0c04090507141504050420210601020c030604083007020d1707080702010617010f060b07080a0c0f080703020606030105090706020a 77
    0x2d00d0a100400c9950420800d503a03035002c0705e0406c29600c1c1e0003841654446100d881d2202e40800900c010b000d2102e9061380c5240f034031407558940300c0c0070b00304070602d10001d8058040ea11040740d4440c801c284c803482c420000f500d8a603180c511002a114140e10340035010741c50b407603070701c18020100400f01c0341580d0007260001002c003231a030f001e0020908c0c20801d40d0700c9003100040105111800440d030b40a45500c000ca1180c1a5440c034004980b140e18031a40c041d0180c1c0108041800a910703003000d4004c1100310021904a0042c416103080a80c081c001400404900f00060298482d030500030301c44107601d142000410391418000d00c0c80390f031070000d00b102d040000d01d602181c0601e100b9049003005044003c0d40c1c8194820386006180208580000781d200301c0c2c600310001030084800e4054412090b003001f810350a0100c124001d882801404e01d0031501c490000000c00700194101d0090040076011703600030500746c5020b10a050840b40043c0841030f03180d200c1101000b1841c3d0025100780d9555000700900098 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 66953977 1250 66952727 66952729
    0x12030201020706090305130605090a0306020309010908042702030c0304060f1b0e010e030114180c09190e0106140103090302150c09012a171303060509010b03150601080402 75
    0x240110034000f0211810300070000181076000021705504002031409100300c560b50a001e60361071081c0306a032a0410103c190030800725a0580c05180c2c400101d03030000c110039403565145416a4004d40113140582c0e40e140540410b4008a6100161001488001c41c81e509101e03041c1442c0c2e001c0101f00a0240380c884070400a01e85d92600314071080807502d401140c03030303400307096000d803010302050030560018180c0300c00800c842c0380c1401102c450081d074016410740ea4941e1003082c40240004000c00081e03101e40398014181f5142c3c03c900510420f072680b20f0650020008500e0015503078401440703280d6a06100e001e20440c00300942d014101e001c01d003800244071505180036070800d00c1209124403600c502204115040d80100018482c058090b40c4840d1601040181c3e42d03599040250103020121a42503201d000610302c05400580034580d0381198203040c050540b4420140d002d40040720000e48580a101d03840c81d09010741d070f5170400102c2c0030b001151500ca006040c1c40a008200604004120002c9425 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 66955227 1250 66953977 66953981
    0x9020d140c0a031118160e0a0e0f1510020601090b1c080406020c030a0b011a07060e160b040302030a110414150f0a150f0e03011d01050a0507050412030201 68
    0x18074000034040342c410540c0c03030500b4052440791405650096042e5a00075038002441c4a00a22030f205140305000300550206d4100c8642e202c460115400403401c13540441d22120b01801544120502c002109452078520419030741c50f581a000a40600c86054105141580100344141075490369480081c80c8400f64001405071120303001081c0c015001a803001301480030503030041080c3d5007690200c494008221013030554a0781504c0d0082c001a80d400010303c100b811520040381a81d034100d0400c0e04220362078039100202c81c0300c100d903c2d9496020a068a034111102d403400c80041031b2060800b81880e2444e00401d86032107031140014030b544d12201020100e81d465034084129502c900341440c002e4a44015403078079a10f5602c2e4454410302819031b00c041503181c400003040c15070f10b011001303c3d11000d42e504251240703051120680244030710441c400c100c50310244543d02500740400c0701e0010b412511250700e421103101520b0241c07001c2c1041c042001e007942241c2103904550490712000c050030f0944c01d040340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 66956477 1250 66955227 66955243
    0x12030c030f060f230a0b0901031b0f080105060c070b130f0303020601090e0303010f03020f0d02090c040e150102060103030f02010906140f06010807020c100201110c01061809020d14 79
    0x20009180600c00310b0585400c42010090391030311000e0381149909807204804020207104c6003640000c071002d06001e05017503840076260b06a0b041c180802d9540340302c0801c2c0d50000c5800031b0503000400d117142c0c5000160b40400441d00410065500514102c0b4004805488505038000d58000d40701c0000c0c1b08007000c24940e0380700c0041800d10840d800d031545914000303440e80e40030b20800c90141c0c2000000d03c00d941021088074104e034a4a0551800149107900303102d00303034460615161744a0312500010003d616841100e901c82c400c1d503901203a9690030411200440340c0d001d0030100380903508500564050341c0000725141501e4060410403080100107d0413409403a42d074100502c400c0c10f02e2080c8100719000082c0901940510314240d407140d40c1d0030011110709030101d07400c9005070b2000060810505103018610703013400151001050f0703002400120155a0710403215030310340d80e54401c0100315800d4004011101010035800501001d4401c2e000180c00d48543c02c030107441d6014801150503140070411a0798 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 66957727 1250 66956477 66956501
    0x4051905100203070203040806090d0804030e010e04110415032c16061d0108090607050904020906120603070501081302100306051009030b0901020a200304050910140105040312030c03 80
    0xd50b0f20f1412a100a40301e401034800c40c41c0d240b18160205242d03032404940084405815a50610907035034903142100c00f030070300000e500d042c408041c80c0f02c0c116440342c4c05040c041000000c5d02d60f91f100d14020034400110300c0d0b81d500c601018a8820744c10181c401c0c0340390048005c420181c641d900242505c0025041c0310405901b00350149621a0002d0041d4101d100ca40c3c2e40080b2407002e00340b200c101d40c0107441e01c2030f0488150480390840b100003500140140c01905140781c001d8001402d003803100c0c0200d04130340d00070406d80f00e40381659420802c051900b0440b0030701425083c60304804030b0a10385883c603140c5001200c02482a4405100381500c2c903c607600040003000d0041400b0b15520741e483c07028118102600003500c1601d02d40e00001c0b034540050085440000095507840300e4948468004d80d02c42c00304005000141c0410000000c40e03940b2060424011341100c1c012103e401d02d4900701029184120116905000050200304080340107118021940c910909010692a25101045008100c03011000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 66958977 1250 66957727 66957731
    0x90905031909050a05040501060206070c0602190215091c052101060509030105010e0112020d0602091504150f0503071b0b190608011b0c030c0c0b120f0405190510 71
    0x30a07150750040b24082214002c0d039683d00e440f07482d14180f0095a409003d0080582d0108003c27844841c820944d0480740350045800500700750b00711007003c80b141c6c0b0402d28030005038030000182e02c0d02800780002c2c40e04003030040c0c0280b43c0041060482d42c0428141305504082c05004140d040c1002c11002ca0301407414102c03086a0403030360f140d24001d4910740022450b06d00030345c42d203000410001500422241070342c40201a00c0b000c00d03020790802c8142000407100b00d8690ba000d110990f90342e00d03000c0200c0210010110103907155410046c1d00c101c6008201c454000b040308511000b80d0b20b5030401c00b01c070b40040d031500d42441c0115403c408410030300b03a5844010165180703142048600000400b161141c1c02640409104803031340d51401c50309072980d00780c456441d1603207001e00400b03041c040c1d1003258000d807107818810201c1c03280e51030300302c5241240c1d400110030341e000051118424100781c112035800130722502840310904003600c0d080d545a141c4250f2020803940405100b091150411103e0800ba910003c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 66960227 1250 66958977 66959017
    0x804080f031003061503030207050d02060f0a0e1206160309140a0318060305090601060c030215010b0703030b061806090a05061801090501090305060703020318011b090611030409090503 81
    0x8425200340580c8010380e4450300d40040b1706a0400440304900c02c8a402d0741c01003410900340000c01201c3d070010f40c0700b20f80c0301d0b10400450001152a0000d8010b00149840d40c2c6603a00d407900c240040c1070760741d0031088420741242c000c01540c0350b101240c0602d8210149400112020145014910003a0320013030380b001c9100d5007010904040e4850600e84811b041503150a1045546603016000e4800a40c0c8041e003680000005204951061401e040d409019204540c5042d2044083c1c03011000e0a821090000380c0000c3c0d6003090641501410001c0c403c241c0300a441c00070b80c102c0c045408849021054414040082c00400c0760f0f450001903009480300620940c1e0341c010740c48a90700c1e100000c00d450703800704007028000a0550301540310030b01182c1e0045c018001d1581c0d18103084000350b0000303150b0000703102a4183c00144001c03d1203080400b03500e00d00000c0c0d10065040000d068000c00794056410031419041f88441003001001740ca08035410310700d01145000b120b240441c01c502800b05044585440000c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 66961477 1250 66960227 66960241
    0x80c070812040204060f050108040609030512010b0703020d110316021f050301090c02010504051005060103091e050f0d05070b060604030b090601090f180209190f0f0e0307020f010804080f03 83
    0xc0442c003443c42220204082c4e96198030303141c981e007450b20401d4041061000040d01240d401d4000c10949407081c60914500103c0d41012118140283c01c00314001c0004500c8008058042081c0740340b1000c9800c004400306100180c160b070721321505209604454500103d1001c41d11085258003000c0c0760010340d00c000d80101c0c100100301cbe0b00244250761040e4200080003101500611680e40140c3d000400790940c503208441d800302802c8007800300360406546090708804a4000c040810035840e041402d40030000b02401c0042c900188a80707005402d4001d40314035041160090101c0d51450b03488140343c4210740d1075900003002402598006001d80d95a03a08100b0301d1000030460b80e040e101c030160204501c0041300d000d142164910000030508905a925000c05440c1c102c20142e444200105060320400c1d4040c020015101261142401280c43e465122040e1102d4042c00c2d5800010000031410002c8940009159143c0310f02c0342c1c0d040c040d0840204085c42405400c450710901e42403511075607818400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 66962727 1250 66961477 66961507
    0x4140f01020c0c031b090606220b091009060504090f06050d0809190e0105060309010b040905060a06080303060a14010c050d020a0c1707350c0316080d080c0708 70
    0xa80407504c07901540a6408803002280f403280c0103031801030901c11940c1d9680091009a0784204040800301950503e101e00e1034a0035941400a0850803441944408030002400050f501101c00001484003c003420f02c8400d074010b0035101165924000031642001e00791100c001850950400c03a001000217504009200c044802806840c2054031146410b10b1040c54070300c0c0940e024020b9502c8040b46600400941c5004005182c00100316070000403051741d02d00001d8200c80500340c0480b540d420610402148901510584c001080740758013442c61841c0120015514804034001c8000c1510340003a454100c1e485040545202c88c3e00c901221400410184080d40c4c900c5100801c4034041402c05001c5008804020380a00046404c0e0003040c080b4100280e124000c21800d0b8502c1120310310000b40e00185e04980649610324403c1805011481c0c850f4080c5030401e541d240010413a0b040c4840300f08151540012010528405443c0c6440c040d140c041090f1940d1040c958003510f10f0f00082044061010b8030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 66963977 1250 66962727 66962743
    0x110a0b0103020102070e0c040308250605010302030c0a0509040209070309080309030403050105060406051e1c0b0f0108010912081f030803070809070b0a05070c030b0108070614070b04140f01020c 85
    0xd80844007861346d01c040b5410082d400312200705060006200401c00100003201401c05056004c004042d0318910301c3e607190310010160416680c4541ba60010015400c003400500c40812055501001c41e90424000c566040030140c0b00900400c624400503180300d2080c0c3c808805907038031005480e036078100242e00c0c554a800c14001903602d07506c2e050218000d490300c1d11a10003213400190a40c844c220b00825600d82e000303c5104041e8012000d04a00100e020284141e41d640074803072180440e06041c400a10010018160460166607140c11074040200340c440013920030100d01032030008080d41c0c440c0c04580344041042110641180600c0c004801c012000d000f9500c174490540c1d909500b542c03581807c0741d88002074820501c502c40304002c1351428900c07980050407240c2c0110403d0107a19178aa84282031f01e08243e0202c9201e40100c0400d0201c160f11414580c116030034100e0590615050342ca1302d0540380c0380030300300900c1c80f180c910740c100038544140441415245d070760b0021500d407081e103c0c2d22a260454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 66965227 1250 66963977 66963979
    0xb070303050f06150a03060e010902070605090c010e060a05070213020c0c09240d050a081903090503040603024f180203090a0506010807091a0112020307110a0b010302 73
    0x200750020b41204540e605551250000600780c0d0000d03180d6031840801c5520121404040580368400814003010064420f4000c080341c04d00103036a2a414100b007400c071200034250143c55001070203024000c0c1c1c0c2c0710720b01d501c020004031100307552040c210a00b61160320039081d0007504800c55540c400071140c000d5015180b140c401034103461011900c03100304002c200045518810340300d050014039a100304450014480c2c05009094003501403d2501d50614005d4200c07401c950b11080041e00da10903403000040c02c04c0104203030809000f8800701d9902c07207071203005501580c4101580410740303a01003c4585045850030700180b00b0f22858140038030102c0d41da520141c0c0003401445c1c3c050542c0c926441481d080504441400981d0040d4018260103c0302a41c00508400080c1c03003a441e241005c58420300425008240d08001000c5185c030342056203040d50701000504008451070083c88003541d800c114081982c00d400c40005a40340e036410419070b00d50441484440301807240310ba80c40208120b881c0420b040c0d0780 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 66966477 1250 66965227 66965231
    0x7061503120c0b1504150801150501020f0706140405120f0c0f13051008030f040602120a0f080417040602030c01050a061d0c071203021305010906020d0c14070b070303 73
    0x61420001e954542d20000700408102580000404c0303401805070002c60110004d10100350301500030780307410442003140c01c10090b595541500392441d100a404a40042000380040c00480e000340c00e0311501d0ba02e4520460041c4050408449070050210701207070082c0c034005000d44c0c2581c6c140c05074a40ea03401e10b02002800e9101d6003404d1112480d0000c1054a14407009250305001044045000090000909110041c03000200f000c80c6009061025010300303401140c8641e10b032864400020300d400c00c401c6142111020800c541804140d001030302251856440c200040d10340c45624100c820f6002c03c0c581030000c0da402040200f400b581c0031004240c8080780400034050b0b51152400201141d82c10710031f4510102c070b03202214191100c0e0704038555010781d101c02c5090500702540c03180d090050303805111270006940010b040c140314082110300d0003d00401c0ca0141265170a240000c0d5440114010420501a922100340100a00c100d00e03084450104c1d0f0503915119640e0003040c202e5005104100c010038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 66967727 1250 66966477 66966503
    0x15120f020901090203220c0b0a0f02010b06090618190602030a080f10230405040f1506061209020604030818011205040503030a09080d0501081e0606030303061507061503 74
    0x2660007940d003d41c151b01441c1018425052101d0a802c002c40d00c11078007001610800101460040043d11548040c6d450b07442509160b410001d085950a504452040300144504416500d410069820460104042200c1d407031010b00096121030310001c0c002c2d59081c0c4400040b03607540d404409050480701030b441d43c0d4407644424000c003495000071140c180700d084400c0c41c00c01c280c214407441c205501e612000c0c1081c200000c2e10116081c0c0d68100e8003581c00000000c901d40c100040300b0750481103200203400801503030781880f0009041107a0100b29641290f103e6100d803041d541c6017011100203583c40241d003139590080b80c1100c00d2608803108494040b4904420510b116030a41c018980303d1540903020f18075503626900e0042c001c2400407c1942d6400080c8500c080c4030f0b01603c02c01f40609000340040c000c03030002d84015103000344400d0100c0381c1c40d00000c05002c0c071034500005480c2c00c40e0b0100c440b00103008062070050101c2c0a07105028020900344240d01e0700042800955000340c0703010701022030403a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 66968977 1250 66967727 66967739
    0x901020c10051522020f0909070f0c02090702030c030408070906060c05030715061707090b06180f060c031c060b030c1c0e010e031809010f0915120f020901 68
    0x842d001c880751081d40354200300c08030441c90090404200c41c8119004074404040c5000407404a800c1034048224250002032052600e18241c140154028980e161060000041c880010000d003110b200c003d0286111700007081d034083c001e0094402140c240c000312a120b684e1250402e0f50b40250388102d080e000d29044010411910946015007000e40080c029451301107513a03a92030524040740700c4121016a070b00404110023a00041c90184441d0030402070600c2d5040000349011503a68016143c4136131420050740c4406280c000d0903400d01c50b8226540800d030121540032806512803005084480e000001d40c4101c01e029060205001c0b0f9000301041100540700c4264104c944400d980903050410140321f9050300c2d60041629101d099403600000c1242c4401b040840e003036503010800007091790004180c091032200c4d403c80c2c0701c034107090448140c0415490011a001950341900510344030300c2d101d00c40d5203080401d81007044010706000102240d0101141403003e080401c221040380b02d655414000550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 66970227 1250 66968977 66968981
    0x1020405040b01140a110c0a03060203151906050d020c0102070b010314010519050a09120903150203010e010e1302180703051005010509011d031516020303010e040206030a140901020c10 81
    0x5840521131400d890b1002400041c1d98001c1d0641030703140b2600c10b0000031201902e6499108000310f1090f440940c6038102094020030600100c45154000ca04942d00c0c03441e0700c1c0092070f501080b1500303810a142e0382c420b26404840a807044001d41c000c90342c00043c0e040108080340314247c2c101d90080f00594000030090304081c1c00c1c0e80056401003042c00c0300d0040342c1582071980e80543e80000c49081c000489a445a54680010400100c1040482c0380c0b4142002030110442144003540d88590b001c6103158104160f03c0411308040c0102c404501c40200062020200f003006030440a800400d02100b404032420103084940382241d14600083c10034011540750406d50480700d007901d00507110642001c034540b00440e007445102807a1104581c1d495060b4000351414884281000d24101e030721090ba140002440c5c40030002d07410b89902b10340c42000100050071015030095045541150102e5036621184200d001500804030441d15911600007404607480c4158018614001c02708d00761801c00c00c4141110701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 66971477 1250 66970227 66970247
    0x7050d020c0a170a120809070501020c0d060207030c0f06050601030b03060601022e05010e0a1103070219060b1e1f080406020a091509030209100b0702091009090501020405040b01 78
    0x81c01280880062043c1c0003a01082c0102c2941c0c002103411245098070b035480a6032100100310040354003a400e0140c00c0f8820302003103010788030030f00052007035240302c00100d02a4400c540024003d40c1e030100300b0104240c400c404500001d9000030003014545090304000e0014401940c03034901083c40d12100c40c8241c100442c00c00e03c01c400580203012000200e41f040304a41051074504000301c1d148806102030000c051003054042c0c2078086416010f4500700c1a5141112102c58cc0040f6440040c81082040b90303000503904035840311070101031106040c5281440142c8040c400c0039511007000ca10041c07207425048500f4061001c121541c0c48001e25070340400c180c10085203003550010300d1040000b400b243c15500100705400052030310315501307540c5d02c81a00c0000080c01500000400c1203504105500d401c1e080c103504286200640103415107042034823070062044040c002c0c0504007500c001200599420a80d10082208034418050004e4a21300079000b90300034040d0f02d101c0c40ca0040c049915520482d4109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66972727 1250 66971477 66971479
    0x1050a03050a0f030e03010207050601030c050d210e06030403020c09061c0b090304090501030b0103030801061403071b0c180f020903060711010e0a08030a0f090c120302070e0c07050d020c 82
    0x1202d400341e5100c5042255440c0340c00d8003440800050100c0f20b803030034402441c2050050b000350540c2e504510340302621804981c0914420400c50254a000c80d080150901e0403034807400160444a0b0424800d8442503065096168090804410802456004100580140c0d0122038649082d030311032081081074a90790b402a140300c1d0b086002400003411040034540c11083c1c42007220306040e5640380010940b40c0980003120701c105003000420425401a8550f40549000d0401c0500d00d58907034009109408002c1074141001012008400a81d21088001042c20381254603000c0c040e840b51809021480c408002d04902072801c07401e124103003000d209071103501400502038501c54454810480f44489580610071203956251540755107440c081003a4038500717109000751520307031600469500454020b0986622110b00744440240050701101c1c041d0252011403002e42c18140b2203040881c81c00e0a039401c0000151803403002e100d0b00d038203000050030a8601c0703041140d031200d1a85408a031a900c0d581045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 66973977 1250 66972727 66972733
    0x90102061f05040b12010c05090316080d1b0c061e050705210d050703090b090f0604120e030a06060915030803010b090103020c1006050910230a030215030f01050a0305 73
    0x14042ca00c0c10390408203035414002d04c0c071081d481d010b0360f00c1421922200b01c1c800204400140704c0e080d505003070284c021861100d1a04003041031178011140d4440c0281c00c100310404c11200c0168804030041c03800a40001e401010030860180c0341c0d00060504000e4200c00c401c0c2155141c0d91501941c07142c011104c0040d8010043d241c00e000e100c0c2c0c00c062224194150554802d401c0c04018120360b09842014400c000554010480c0c00b100c0c102140c41400281c084c0740719400117060704454100005000303400c598414502101031244035001c0702c41e2004265082c3e0f050099080ca581030040903007105064400000c010020f200c03122815210081c4280b00041091800b8401081983d01c1c0740054480000e040c14058078020082c154141850055044032040c59030320442030050b42008212203034048440c01152401605081d0040c04003a4000310841c090000c01018000d44d86988000900441c0e02030010070001d8003200041c14170380c004442d00d00c0b0002c02803000142c07a140005d11401266042005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 66975227 1250 66973977 66973979
    0x7030e030c0a140d050f100b0f06030f15030c190503150f070f0e060f190806010c02040207060608031201090c0503010f0605070f080c0a02040501050d031b0c050a0308090102061f 78
    0x5101c0341c2444c0d00021340b02801040e5034030b0316a110a000032201c6011b0047d0000780640840704100c2060f0f1003c0c21a03018040034400c11003200a1480400d0f000400d1241002800e03c0d1440000c0c50000203103801030b0070504007818404e40c010b0880d4054103075101102940c3c680440480702000d0a601101c40c030094040207000300b074140e405990725000c90b2032189004c151018114003c0b0b8540d604c038a400b107049400020f8004043c54030746240b0002a035840c6040181800c240340000c0c482b4604a0000e0300c102d45c001003400811480d81e02480040c5040425a81c403000c000b0150140d140c424416800c0c49414504460850351094049a050b03540c00d02c030344088139091020841d402d0304103500c11502000c8444280c00440c444c50b01400d170001c070f003100400d0441c03050302c1404184c0d80c040c0d2081c0d00800c0040c140000183e0002c5035000801e01d11280005100250300f403442c030f5509a41d020f103401c4000b010003c8140a080c00060050080c21f0702159038540301c8207440c00121800e0071110203031405600d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 66976477 1250 66975227 66975229
    0x408150a200c01061d0403030e0106060203040915050d0501090c0608070207061d031b030706020102120c070f080309030d0501060c03090b09060c01020f0307030c08010b03011a0c0307030e030c0a14 86
    0x101800c08002e40300000103c494485030810440c00c0c4141035211501407070820070042540c18000c2088000b4058001d210325440c02d000655640194007440700115110070401d154010880c2d284002010001c2102039515203508103076008085940d4140c85001450b2400302e4254069021140134508a900a000e01c0b494144226034a040042c40900075411000e42e8480700c0c1d8041000403092119a0f41115110105100701840d02d1090391011043d64014412140c3d0940702c404d45540c020b4003d502940c1e22400d5152031800d00d8000d60006000c410003009011030514000041e02401d40c000c1402c0041ba40c0300c040988080c3c00e4280300400040c4510020700a52811401601502401030045400c14403540340e0346080e81c014946500d001030f008800c0128003030303060064100c901580e05282442c0d5040c80d01034a040c1c841401082102c1c0f52141c4419801410312080f10307405440c5200b5a510780c0c81525008010640d07402201c1c0c468465452502d104c1e00e0112004000c841300c01444004007100b80c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 66977727 1250 66976477 66976541
    0x901091a04030b13140f0106090e0c0d0206070b0106030609050c030c03041401060b040e1603060b0d0c0c06020c03120a05070e15090a030c0f1a070803060f060408150a 73
    0x40075800c450f00c139019503a0006040900702e01103414404090800009121090350844006078080c41065050401e8501c0c0060042080c1203408802d0761700c00010040b5001098007407041842c01042d0b00380c0300000080483d030541c0304400399540002c061103581c0b1800a107044500064900711402c090030000304c7c00040210003856000c81003040013207810355aa95500c585500036900c21a8649401d0081003108078100410081e49074060034100314081c280b010030411801480405070301c1550b100110f1110700e010300b00050b1b0b01c42c4d10001c103642d41c444540e0200d46a802448090302030400207008100b982119010301803160040396031f110400c0e80c0050130084004000d050200384441c080040031034940340c000801015501800307103480d1841c68000d40001000d042c0e884000358201144800c1120701d040011039103003941006c080c40c1c80b40c8a00b40000c02424480e1104c0d03602800001d070005000001290751102c11001030b82e0004d07599651100001a5401c49002c2e0700c41110100360709030040048 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 66978977 1250 66977727 66977731
    0x6030109150b03190f0501030b0105010f090506030a06082e02090406030206070b0f070212040b030910060f1a0c030910050d06030614060618040e0c0a0306020901091a04030b 76
    0x180e0307890190a5490300e11000c1a07200b41c9a0740505001010250881029070084c1aa1211004410000780d8556103560400e000d040c0a0709042040694000e66102e108110344c0014000080401c0e07034900f00010a50010f00c10351244010901461039015041074203031400541845280700c0a00a0003e1002600000d61011b241c1a51280c3e07990000320140c6c070303650f01809044d489618904007506000d103d040d0100d030010041011944002421241c003c0c0e072109035022210304010540d22a100d141c1e42906140e001010344003003a01d02b5000081c088171031101c2c80c049406000d100307044100464000c6181e031085001c20002548200f02c010110b0504496140c90001c50345041e1b07062600c581880c4090381d80d41d030b205465091b19050342800a00040844640140c012200c41d0b01e0710480148600008840c040e200744030b20364800556921201c01d00944c190428024201e0708110f4a070b1801200030741201100a0005090010104085502c0d12802a86a2290b50541d0030940780da51061070310840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 66980227 1250 66978977 66979001
    0x20c040b0a08060a140108030412080706060503100f0e01020a02190c0302090a06050102011b020c010305041e051b010306050d0803060103021303060222050d030c06020c06100303020c030c06030109 86
    0x74240015444014442640500c1c0c88201c082440c90350203074036919442d0107801001c0c1c0c942042104001140b900300b50300c1d042c039611801264441445041201c0104090313880950103001c0c0404044105215a2001e61402c44140c400c0014950749000c0310700301c0c010705a15102680c031442e131041000000d90310b1002098826032400020315182d0340407925518069802d4058030707449140610041d80c0a0041c0c00c1d1039202e2400c55011000c100d80700035559040c050805041c19990300118080c4440a64029480f24003400070381035091051424a03070b40e8220401c110b001038511001c08805622a018641c1140c800405212900f00c1d11340303401446e40d001900d01c1b810f1590801107600d4150400c2e0641c4000c3d4001c80f00140c68038150104281401c112010600100c8440c1d0030510155469082006400390580f07422560b07890a40b03000e100034428442c881c8514410381c001c110302550030300400300c1940d10907800e494000c20140145640d031030401e03d980742e20480c02e000601c00a4103503401120b145203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 66981477 1250 66980227 66980239
    0x706020706081503071e08060402301b03010b0927070312050301031101030504150902190e0108070b0a1e0210090b01051804020a03021c051506040507030c020c040b 72
    0x43c0380010345000c405034405c0450200146a8001d80c0300c041500100829024001c0c00003494241c0c000344240580138004c400c141c807007400d220184e2904c21400f28003e0346420403200b00f5540800700241700910b80f10b01350700c81d41c01c0c04000100c40c1441142680110740140301c0d6030b00a130006240104007148030101d0304a41c841d5010000104080c01070043c41031407d5111545d59504500700f0030b010b0702c01050414107150070300040c4000100681c490313400b40300004500040400407803000810311002d140f144d070039650f80c1040101322050307020102c0e4100da100d00c0854500310f40d64000200c060003606050400710b411454001160b40c0000c022140a010600c1940c001240b100882e00440354140406c5c0d4000800e10014000ca0038648440020b11303c1a440305801ca140580c00102c080c20741e070000a009241005552203032824001140c00089c1d407140c02d40e41d0040b8440c1c0c207000c0482e02200d00c1423140741008042910305001c2d2061941c400740175800b51806c080b0381c605000151513030003011742c1c01ca9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 66982727 1250 66981477 66981511
    0x1180311120f04060908010213140406090203091c1106060103090809031b090106030b09130206040e040302010f050c1908060a081603170405030703320a03030c02070602070608 77
    0x2241c014020700d000d0031020302154440e410310340001e01c8241c4682004a250b80f042101440b0100c4200110085a254201c600d0040c4290b40104016143c56031040c90928004000d100e911a40454218210405042e83d091251070403582210854031840100400c0c1d0802c20100700154401d4200c2c20351940100795452802294101003882e212a160324603008000314444032a083c5449181d1500501107072409100b074403030100000d030744544084d03c03040c103400003040d001045488500c2581c0081007034050030130b0b00380303010300b0301a010f40801e44035a110a03140c10700140807011312000f80c070030603083c1b240707002c0c10f00c24412002e461505028212561280350a40e0006030341104210003110406801a160350103031462424440040b61540c8115034888240003e00c55a20300003101021640c1081d4010b032165036450092580e111203503032a40039402c0a452554000e500004c1c1c110344036210303680030055119240d001b2622040c250290318016000701c4810400c80f4462401560440b000402c41c0351741c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 66983977 1250 66982727 66982753
    0x5090705090702010902040c0e060d021602030102070b010603050c04030804030209090f010204060c0c050904080909040c030c0303210509120d0e0106060804020102120a0f03110d0f0f060801180311 86
    0x1e4030045a01e240103039120081d24007142414003506c00500c0960500c2469540c01200142d81ca000ba410f241040030790106040404524040030380400c40d4000d80215661111401c0c015190002401206c02290130705005c04d55044450040780c00720303030b0400d00460a150642c0d007003081c0084082e1804401e0709c5010030382c039907101e000c0c4000d000400d03040d12a58403154003032030410f604c103041d907000500c100c422400300310200e0801d0b07040b01e244000031940c80495a82e00d280000301601d00d90409800c40e0403c0c400030041540089081207000c2d1a01030407040303269000845002d8a204541450b61344e040842c000b2116030844001d442c18282c2da40010810100d00c03c013050868005a10020024007814140419540c041c4500d00510700010700c44d0385071140101380900260003204c650303c10942d44000c410121601e00381a0703540c21420300802c1c451345110f01580b401400c94840164502c030714101c80010400414800e0220350340341581c10480c01d0f0342d50740741036518603901003e01c405405044410208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 66985227 1250 66983977 66983989
    0x5070e0a08010b0307050f0a090b0d05010e0705010e03010915020904020706090c030614010e06011808060f0402031603050c060306030102040302130c02210d0c051603052101050108010905090705 85
    0x1400301c040c000210029110100b41c0703003d2450348a01e00500c041d819000650f02c884080c00161841c88001007060398240d004115140e2000001802e15468038500c8040c8030f4000c80c02104031513090342c5040d0501043c3c002c0500700da02c44076000b40740c03412805080d2503a400c250050f00c0e1004004000600340759141c4c940c1401e0740c640c11001c0b200705202020a2003000004e00c1007211840f40c26040001035030420542d03440280000d0720079030500110350f00180b0b43c0710159911501074400c00c3d05481041c109016511000d00d0191822882405000541780700c603406030b03605208076500903000700012480001400310560001e4030051f0107540800010000d45c403031a1928920100502000070085284000281010283c0b800d281c80800340150740d480740b081603016102905060036000641c100400c800340c0c0c86100304200340d49140f400340440c806154026001d40001c103007042001c0301d50001101d0780310140b0b0f000d00a035800f00c0c2d60400107002070501d9500065108444c442210001341d121000104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 66986477 1250 66985227 66985229
    0x8071e0908072702120a0f0f0e011a1f030914010c0203181518030106030c260f0a1e15091109160c02011704060c1b050d0305070e0a 58
    0x450541960f118042e442d841280000d4040f400f0082103080429440300f04101010150402c0304060701d400c518004848264800020002c0340d100821086200c3e0b0489406050380340b40400050404d05101001030400d001159510300c4c6041094540680700241540180301c1000c0a503490b111003402c0408002c0c0c03d01c20159200b4440d00215158800b46034103000c0200514140341c01504000004a0581c00701000d6509110421902ca4140c50842e004030b80102b2055001a103d01c2c00700d180011f00f8103805a042c0c0e03058814103250505008a40100c1d076030b41580d0141070100d68080f01410000c242c1d1039000c01d4200f41c1e01c0f010500f0400f0180c80c1c90a039800301e1043c105100d6552540d40c401c011034a01000e1580034255003800207803409444c0d0402c15441704440c1c500703200700d81c0030320300c1160f03c195150440104d40803401015401d10342041801001c841100c0c00200312011100340c41d511058480c20101c90b03200d0000d154400c05180704a000e041701810036018041480f0000686940d0611120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 66987727 1250 66986477 66986489
    0x50102070b0907120b0402041e0903080603010b040b3015070908010b010e1c0b0f160810030f1104050411030106090207030e060f040e04080405090708071e090807 71
    0x44007609140ba4500e00f0301c03901d81d003e0746142c0100460b150009001121540d070154044a0000e65604002e0006c80041c50074400c41051a150500000c20545c1025041f0f01a03071041c0c0c000c01191850b48180401c494503e14040d0f07001c803615964a00c00d0319001002c1c0298920248440c110341402c00c01d40b450b000c0511410600404070700100520b450f803001090300148030302c900900c4030024010020b02100d045505442c000c000d030182c4881088004001c2c010030591000418000c0d2521040e46804110f00741c803065070f07020104410f220050710500c4014096542414010342d590f26540c1d8a4924600c201402c50710803404007640625907455110b40e43c0304d02d020700120520301040f101003600310303071b00e0781c000d0240d603031042c4240d0021940c0714000003a07054080c1d911503035030b01e500c4031180d0443c0a40e07840003050102950400040080200c05041143c4043d2405a0300e40c8440506a481400403200000019109030500d203803140b0343c2c00240a0b801c00f6040400042c0e450f501c7e014203090b0941c01c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 66988977 1250 66987727 66987743
    0x10090f0519030206070305190c03020405060c070906050303040305120306370b0a0504051507020a1701200a0c030c050706020106061e020703021306120c0303030c0e0105030105190305010207 83
    0xc401d241e01440300e55403105e402d2504001c41c0c9007041c2c44d0f0b00001c0d51a002802101c2d91201c0c1c0001e2036000c1d41c1220b000d0080181003a4664640c0b4000960320400c1c0e006180d029410000000342504000050300c0c1038139440800741041c500c8001c424081c5420040a0710f42c049003050380e00003400008040302001c1d445c008200450064000a13440c00340c60a0740c81083c02600800204095613800401c3d04e00352036045400d603c01807800d044030b9000b130040f40f4029510646003400002c0d5038821a0480300b840c0e110400034440111042580380400e83c40d00003550300d26038200040740303001d40714203d0002c102e4030034103100c450880b0300c3d00c45525008150708080c0141c0e550b1070051210b240c0107000100d81c1860851000007442007810001d444a41d00c0c44000d020310740030303400300c0542c1e44107800c000007800c108442d04484640303e05000703016200314032054010910703000e13616021078800d422003154144107171105407859203030005125400320704010f1601e0f21440c2003c0031000a07000e00007411040e00651407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 66990227 1250 66988977 66989023
    0x40914010b100f05090307090501090519060f0b0c03070b0a0c1205040809010c051903120507030b0d1101020f030c0c0901081609020f19090305060c0c10090f05 70
    0x206400c48900c0540d5510440030260b00185075640250102c140c0542841d04a80700d19003203001c6403810341d0b55041407880e035082a002140c2c09119038000c502c0340000e1100a41d44682840b089802c03507146003d615181100d1000030300c1101c180741e0044c0070481054045070324020707294807040281c0100390380544045450380c1c00380e40340d9031b40b0003800d8a4146290008008a060a030390b0b038600361007034480c0b1905201410382184144441484006003c1c0b04e104000341140c0e09524005156540c4544156240b51410f400716001034401c2c40390803007606014002c00080c400b0798031004401800b503031802d8118400c0710b000d9004034001340054100405100000c003405a240d4040005089050300a04079070341c400d02084c3e4609110304a201c084420301440141d40740500c10051485d031050310310440004401001c3c079200e040d4410b15590860f07001d1016100603894580175250184908940140554401c501d14005284a940840d1201d031080031541300000c01503880301c0c28613814000418403080c0170303d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 66991477 1250 66990227 66990263
    0x6070b0703111b061005100914010c050a0311060a0513030c170f0d050601080c0f0c0c0d05100e070503030702122803080a0207020105071209030605100501120e12030c04050409 77
    0x89000d014111a404035840740c80000600b0300008d481080d0440702d114040b1040d40c0d0007075440700c81b030b0764108081c0d52000700c2e9414040c0240b1220110202d561084400041688420f0712845010705040030200200741c4076910212005a00000d00ba104203c0031184c0040114540c40240400789959181588a1100000001c11150003c0c070650601c4107410800000d40c2582046851040400c00350035100d268410324285085004504240c100071000124000d001c8001074069104c00d41d03000034000b180a40e00c125455040718401d50750541e006018140052820f6180b165640328107900301c800100040b065000310070007241134a408114240c00341000e00d039010050b01d03486074460009510b040107d41c002001403141c01000b80003503100001c144d000b41d22071030001c801560881010b2000f410101c92689403400f052187c00d010559404d060802059a805051608003840c0054180804030392161103040c0d200401010000f801000041a695241d12034803113518000c1c281000c2815101c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 66992727 1250 66991477 66991501
    0x100b0309010b01020f030a090303080405010207080708070b07030608101d030403030306150206010302010c06020f1b03030915010b07060b01020a0c090c0f030e06010302010f020f0f0c030c06070b0703111b06 90
    0x441c105c04941080140c4032203150030030717803034800c13240c0c103181c4041d9655890502c240280036a44000300260000654102484050005000703050f010300184001e54658410503801c80b5030510400c4200d4005007605a040c41c0303568018101a980d4490b01d05000c0400c41c1e1907401d42c0d101d83c01c00c40c0440e03502e10091040221010000010610b140000c00840d4150340020300390080c0e00d84000e00b103580002e15101d00e512548161804c8031018204030b50484444040359840c0d03001118000c0051049914228015460418183c1225010b8543d186080010748490000d841c00c40030b05c034107522910001d1800250141403c03030080c45050300018640030790050080c116605040f00004050400d107006d00f81d0140410789504481c1d0909000d200142e80c41000e80c02c20302201404091401696034600c915400460f14120a20702101503450021085040002c06d0080d810064000d00c01c0100180b0b41e28000c2d4070210300d1440d4642c603241407a0403111a0000200fa100304810250081d0041c000204054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 66993977 1250 66992727 66992743
    0x10803030921030105041a0306040c030b090d0e040b0411070804060e010302040803090d0203010b12030706050f0705030106080c040b0c03091302090d1704080f070608071b0308100b0309010b0102 85
    0x84040c08002d04411480360b0094081070007241d100b580d4803003208429880f00314082d00b1024018054034494a018100011845090300c0242c1d400100040010443c400100320082081c2c00c0380c41c0d818901c003803501800010a80241c0c17141c3c006076501381c4c0380042045040502101442112855640e43c14440003c001c40391140d0328a05060040c030041c03004086c00b00940c2c0301342900b40d0329a42200d440b1b00000380501603001030319070406442c544108183c00003200034010315000c1e44060200380c803020b0b454200060708032100d00003e002880140b0080d40b0507004150401615003d481c1407c0d1035114400301c0d03601528000180f0362001a81c450541001607115042c0d454425046051586c1480414102c9000d204000c000307501124030039060040304405d0390080c099081c1145e00c0016101c101c0c40d92000300d400356a01141221002640e054803c40300e0545c20110305503c0603a403441d035030702695400000303010300da040080300a01142c03c04419016510500752500085900c2e921007002909100131 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 66995227 1250 66993977 66994003
    0x16080c010e030d0c0c030c060905161503060f0b03040b09031207030903081005030303070e0a0909030203030402090109050408090103020a0c02040e0c010f030908030105010507050f0304090203060405010b071a100801050108030309 100
    0x441700b0310030220380c11600c0d0111161f00150042038440d00c0d464400d00301b10100801c42038055440300041001e000090715011445442c0c0c4003080655141c441145840440f84500050312404100090014410715180e0390400c00e4001280c0c18030781c00200c8042000403c0360014006507a828803c001d05901003080b5410148080c1da01c130301c45051402103503e0780b00050000c024403c2c0890b44150300c4d00c8840c03500000b041030040c2001500010716000352a40d100307943c00d0b480768501000115030b541c180c0c032031140a1070f4820b80d401c0c50810303010700540203500400c5000062110b44012803026881e00d000310601160080050700c1410403040024201500899010041500d08402c450000c4c031001c08030b906468003400c0060700d4150314034105103440c00e1140550340c01e000110b80080c440402c0e4000c2c2d4040c0904442c184070b2aa2034100c00b030440e0042c000040c00c4050910081c0450b006a03005091f008841d003400d91008941310400942599001e90101141c0da00000030028100d000303002d07a03041164 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 66996477 1250 66995227 66995237
    0x406030915051308130302030708010906110c25050409060f060602032a0f07080106081c020c0405041707080403050c0612010b0d150e150102010204080316080c010e030d0c 75
    0xa1000040540083c0f00c03000419024001507030805003c401079001000310350040803108150703156001079000c1d1590030411a00302c0d0400101140950008040d1440d0340d0704140148408503e0585046a20031500d02100c4400c500e20341c0464aa1a0f500420042900071500445c02c13540c280c090340c1c216401c541c044002c6400500c85004541e01c0101c400041c48843c208402c0b07808250004141024140d0013804058810164005250081034001e80300302d031540403e840c24481c0391030004241c510303020003e07401a04440201d5115180c280d1000760010300035080c8805142c801c200f202c840e58040601038640c0301c4040780801c20800100440c0c954068141c1c0e4881c10001940c95a1600e80418051900c0c00c41c0b0110b41e0030814074556000034800200d21184010352aa40d00c0c0c100c400308070980c1c0c2000303c0d2040303020320314440d4014002c44085035280e00081d403400c04240c440b9070100e0710490080711405010041c1b20182e010074042e190580785140c02440ea510912150705003142c1c013060601d02449 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 66997727 1250 66996477 66996481
    0x90507060203040b090f042a02070503120a080711010e1605060403050303180109050327010206010311040e0109020612071d06120705090d150c020304120201111002040603091505 78
    0x2960030300c1903c0145d44203440d0061081007501c0002d010745140103110f001c01642d0a02a880c0000c3c21401d588a8078107a02500c0b4881c0d00c80040c16100c0e000000c0d45031840c1000c00440040070b00c581d2a40d54080c01e507240c80c440f848034990100c1c0c2502c05800540309a80d1000c0110720351590006200c1009100486003545001d02c3c5544464403404014603403100e80f07110404d06580c41030290050351586520806803541c515205101000100024001400c500260000503107154000140c060680b0b40003c50103140700808010000500781d03000801c99a5501e410580e00180c4590020b040355200005c00d101e014a840c20f00100032114041d250b401011220076026016215801120b080d14156200079401d5a210002501c5620881d03c025030005444040c020034811144900001401440b1041c0000840940201d981e4000c5e07004101c2101100c0707030240010743c090995441014a40015075800d80c008110702c200b26046070348064003090310303890041c04000c042d9060482d4106000420030040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 66998977 1250 66997727 66997739
    0xa0510021e0705120901090e0c04140d0b0414031e09010201050c0a0c060f0608030c011d0a0309120606030b10080706050a080a09061b18060905010819150909050706020304 75
    0x1341e01003c50074207501000194004059103d0045140503009900034034504d420419000c5401d0b0b401841405907425817610750399a580341c0610740300c04454215401034000e0311543c6a05a1403003203a0115408c5100c204052149101c0171803d07144412040c1c007030103803035400610002e82500d4005001d00f034140c2d410031400452540008807000410f4210f000000e99915150500c1d0042c0083c2c7c101ca4458840481c100303214003015045016040e01c07800440c046001851a1565035090068004020805960f070500568040b88144118507008545c0410360640c1d90312443c4040c0030699018884140500e018050340c0b10402000000341060f140c020701c1d24810000007400d4980180102426980f10582c020500c1116000bc290580c1c5c048a50310700c0800324200580b0b0146134000000078140c82ca000010000c2c0144101422500c060310703201c0495a42040c0c41141c546289409246581c0c0ca201e0320a290702c1d14200c080c00f03010200d0000800b1a11404c0c0145001402e030310010455200700420b000c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 67000227 1250 66998977 66998983
    0x6150e2e0e04020702120d02010b0a08070b070f0f0506090d021c0f110303070302040e01090614060d0e060709050915012a050a030305011706011a0307020a0510021e0705 74
    0x2140c4062500c4a1401d405000103000382c429041d0103940450f650480d020380200c0440c08030101c001507002003100b807011206214840c40700f4802e0f015550040582009480c0501d4014082c40e071082d0511305e0500701c00c1d65a5441c6408414041d50668088410410860310800c915000481030340010300c0c02802164039481540c020400d0401001070711040603420a00071481050303400c0c518070a407a101d180029005000703400501c01c00e5000042c00c800011020081d104250565000d040c0400b007401007402840100da000f222405207442d46e504104034240024442180a03244544c4e90012080c5041d00300410302e180606100c4413503103c09a86001d607a042440440b1406001044000c0720000245078411401700490144c4280130303400700302c400c140c0c0c168003c80c180c41c50340250602810030a4421960ba110134000d0040c492142d44000e4107002040d405150320260a00c1240c2c001c500d1130b0355044c240850702002d04025034001c03501c0000c0825101c540007030703503040003d89070030041c203038071285c0c0d07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 67001477 1250 67000227 67000309
    0x2300a0212060f0f040c021c09030206090910120302010606111c11030c0f0706200a060504020402040506070f03030c0201270812070507051002070f020f0406150e 71
    0x44218124401000c040d04c80b10000b00441c80020000c104c0a081200080e4440310170701d091200709151105c4485690b8000d804103000e8a4014181c942003860080a10040e00070242282c031411145050016451120f07840c4410200e02c05e600205060b407501c0f2006d41f401074000c20301005500a00c07480b201050540d482001c42c481545001100300c0440c0b1100e60651056401c040a9401002d105550700100014004101c0391140c0d15854900c84036515007400c20030f4040b1803401031704045041c60114029400c8283c11500003400103141654400006241b03034030840701280e010a000380c000b01495014810143c4060303103800240000481606a5003004001c0407041820441d6002000b081c403400c0001c0e0b80d2507826410441a030f505100001810540101508403110301c10301042030500d506ca030003541c4075554420100d014144c055400c000d545d005c1401c443d03030000d40e81c1600003040c4440121400040d541030716015000140c203414850542c41d0030a4540c04210000b100c8050007420b00b45c01d00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 67002727 1250 67001477 67001479
    0x6060504060b03070f0509130902090a0e060a0203041a0901090b09070b04060c05030921060a02040530070902090a1202010509011107030206030a06150320090402300a021206 76
    0x17034800910032810703a410300440304142e070009000ca588150044844e8024100e0794000c4401100d19030701d040c0001c064401c140700c80480c581050000c15883c800980107590000d124030a1078000680007a6008103d880445031303007005a440340240001c1c00008600c058100d88041c029208040c1025038144480c440c40c414502000b0541100b902030000c14400d460100b10003c020030a04955020401c4008051909102c001d00812021030700c510014400c0354110741010f040e06400c5ca4070303090308a681002e4800429920110b041e140804d50304144860340c06802245001602e07034044009000395041c030f40c0c000c1c1610700c9a400040300542e80120031b4400c200c070300340703040666050152000e900f00110303540029042007012040c0001e0409503080764040c0c3d00b15503081c01d04d5808841c400c5042d51a68107100c181040000c4800326401c011600030494024080c20242c43c004c51000c0b91040c008011401d0a100c200d500b81c0c1c04171396014a009144c000c02c0b40342c025400d0503180750f80d00d219154050300803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 67003977 1250 67002727 67002737
    0x41e090b0a0302031f0902040e010903020f010501080a03050a03141f09050603060a02161415130327050312040807060f1205061503070c0201020d090f030b0601050903030403030c06060504060b0307 86
    0x4405c403089150848507140e40e01500034003210700380e486158081c0030b400104034058019150035210907001441018101c030650b1004103140c0c8501d480541d050341c042e9060310101902e402c0c3c090316031012096114042c0f200e28280104169070300c4520308014416401c01d140d014100b03030a01184d69000100c031500000c07032090060ba5104030340c92800481c03441102c02002510002c0c0710104104c1c001c07400012400741c90310210165038a65a00704048160900000d01042c0b9800c1079440c544190090002c0c2181d40c40c0e46030000944840c006894400e502c01d1070800480001820b00c031303d680034000140145502d04000381060b00c0260080d1080d00902d411281d400c1e501c10014040c0c0e61041e0224590640c062906590381c1008240100b40b402ca5800590162142010f020203880c8035007045c504a42280640c80d175042e00395034441441cad6a0107000d450400006101d01102583c041c002840254402c4e116550030715010f1506100307413180b43d44202e02c103516200082001c2c0c00b80e00100c03a8410814600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 67005227 1250 67003977 67004023
    0x50a140a05090d080d05011a120702011514180906040807020a0902070807060c02030c030a0804060b060301120b0c03041203020a1206092c0307031103041e090b0a030203 74
    0x201c07402d00030014029404190040007034140000600242040341040c0c0050004d070b030300e402c84031441c02814414103034039030420043e0840064100d660140c0110b0a40f0001ca020114044841440007141c0c1000700000384900c01251145445410310416803840041b8194901d0141c8810352220340040001d8001d5600240039411541c1e0802c8103809054076080c21901ca560500b408011303a0460b03c01211814900744038103000038000401e85605d11244030045141040020040f50425400b0b4002c03540c0304c2e160010440d040d0b03a050065030107040450000b210049403400c2c99840d080340900b42d040d0b02c81080050101043c04407c0e20b040e0404c06090141e660102074804030f660440003038030300014a00d82600400c07015241c0d0000f00d179071280c003800d00150b00c44200c1c400003690502410301549610810422b00064003e03031030030344412142c5055a04090703484a00040d0118034014141000141c2801405010f1041c03050300c51103c000d81c0c1080100b4155070100384c2d40d503480107181000c80c10103a2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 67006477 1250 67005227 67005247
    0x5090c10051b03030a0504022e031107022106070c0803010e041103010c020d110c090406110d090b040c06110d0305090102070507031a06011103070f0314030403080115050a14 76
    0x1069010510b40c200031240d40b4070708000e20070f0082800340d404034031442e494181c2ca1610382940c84085818400310b41d0301101c034042c0f4441a4010030480680100c0c00e64144007040c00351382d035560580c0d05040000d04280c05d0040c03c035070142c14440024441e0090020050741c440c00f08584200fa203040d1055510300034000d4032503090a00018021010311585903080c2490340b40001e07030120703034035040d600107440340c43c0354808a0512a4451480300e000b039422400d200001004116103400003140c00e4825000baa1901c05821103810640e018500c0950b0103903210030620040100d0205110010800d80c40c0c002100700220494648035520002e00108260f260004500d90702429411505004d40c000c040710b5030340384d99190483c2030031400c2c8041c1ca11070080c04001519540111940c00c079a0701c40002a40c90a07025aa0704e6015100254090701000808001c0340d41d148450002580124000d0301d031403c2561410222102c0840c81804020400c0024403c0d14034103900002002c0041031400c0401e6101e40f5114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 67007727 1250 67006477 67006507
    0x70516030c060507020a12050a020c0409030c0803040f11040b0d110102190c080d020c0a09090503040b0301030b04060501080c010f0e060c0102040f0e0606130510030608010615020105090c1005 84
    0x40c00103480710f4504403d2240c01d0b9000100305c07003094400c5800041c0d0101700345040e91140204242400540c20040e2011486d00c0d05a002c211000d12030308140310740900646920701c0c80d4100310360840b48400e01101d034009020f840310021800c0070313048a0500030b050207400418810318000a0080039561200044412603009100c6461074204108aa0b43e01c00300c2814091044000b40c030414aa40c010404110083d074404164110000d0015140001c01c504d000031080003000b03108015a441c0c0003d00000c2000c041c4100154000d60103845803112a007407500f0000b0854006900881d40c1703900441e07004c90340c2d98114110303500030035282c10948036501c1c2c0040420064801d00c0150440f952000602003645c1c0d8079250844150b584840e00410550750b00802d01059119920707102c41e0100c40d0413020011458107411206036191070f4900859002d1343c0c0c0510500b9a0040d42103080d40380642c0308220380b015070900c02c4a0307019131214010801c01d001c0c140413030710340c01d400071501040000010305041c0c0d120881c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 67008977 1250 67007727 67007747
    0x50c070201030b03010902060c0c0f04050c03040f03090504020a0e10090311130b0904030c050d090807270e0609010b041a010507050321041a0714130801060b1e0307051603 75
    0x1428440e035500e080c80c0d00b142c40e030382c0034224644075020740c910314250ce042071302c00c0900c41d80021800904d10384039900d91843e20196890124104402c0c4d40740450a6207660015008030351440d16043c9161f10034404019848454600ea842003120100b420000308020392560102d89400f582c2e040641c10b9070744000d42c040c044403c1c00740d0300b104440303091000b016800001203103254003d0084e544112050b44045910100d035200c1c1004951005000b481130700e0181c082041c0c1030140e941801c0fa26a0f446982070141c58030341c03102202039000182003002a00c028000e400078401c040b5402c201e00c9100c04080201c008110000504002000c64180c080100030001c07a0380c0041d840007040720240010885c0010000100c80803102c100c495100041c681707400e81c0c20140101e200351152412210010103075101031704203e04196044a4050700011501000e1040c40040c000040300a6919039500c52001c0300040300e80214818240b0420400000e5907000081d10108205451300910074003032404c0880380a111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 67010227 1250 67008977 67008979
    0x150e030102030f04060509070311010509010e130f050a110415030204050a0b0406022802010305100909060204051f08130f0804151805030a03230c0a030e04050c070201030b03010902 79
    0x300009115840c0d8000c0801c5204c0da208a8042c041560751121817034a13803a203444001c1c05d00c0c0c00410031004a6000c0c0f4050300007500c061522401c4070304164002102c0748002c003610700760307150365241c1d0504002e110700a1680c0300500d00c00502c9885207144017403609104602c10114201c1c400041c8421940c825011540209001002c1003140740d03c40d003c00419a0051050a003d8800d10116040b180e030251080b03204070004914080c62003041d07800540c05080001c03e000815841107901041c9402e5610407145000e00400c4016111130500062183c1c6011b43c1c01c001a100d110781c409021020b91182c2c541d80d1040c0b2100d110600e8510078a800d01580391071301d40c02002e00e100450040760000d99102e078040c8104440d990109550802c0708580b070071100c107000d8943c264020513103000100380030b00407905902d90803064001121020049089036038102c45c0c1c0c1d00200f500301c88443c200741548500070071407905049404006038204000581282e118030340d4002e041c5900d410103c000f81d81d080d808a02501d030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 67011477 1250 67010227 67010231
    0x102040b07051c091202040e2d0f03071211010e0d03090201031d06010b07080903070602070807090509100e0c1e040e060402060306040525080610020610150e0301 71
    0x11940707000b54071003030500030054100450509150180c0d10480580048855031100485c40741c0e800d07020311015100650b4200058071a19964801c1081c0c0c1c0c841048004c0702c0790119810800c2d0b080c800b942003502510307191006034070a00010000c249224801603c102d200d003803140f20724204035070300d070b01408404043740c48500600710100e00c0c20350150400c952051007603800300540111740b41ca074951010100c5004605501c490300500c800602d0b10010484240a01803603810300701d014000a10340640754104034016003207200c041000e0171041060f04094140850300703220f140b8004e1038080d0781d000c484202c4099244c80381d104190102081c0040090386002810844038490510043c000352030210098074011403a01034180000d00011403241c2c0a59801401d0528544604041002500c0083d040d41c1d81c8111901071001d105840304081c46409409803140c80903458540100a0620b13075015407202990400d2041011401c10b041e820015103600d0140100d070644101d40490388420b0402140350558 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 67012727 1250 67011477 67011487
    0x1e160902070308070804051c0302040509041b23090601050408010c0905030d05040807150e100c17070209040b0a060f060504090f020405010f081302090c03070201060509270102040b 79
    0x200d4006002003800390301d03200780c1601d901408450b010301c00c44016160317401c04040003030840f52132100301c08a521286000f504060722407001429601c8280c80403207802e207030701601c80c117104141140000204102c861400c10668111a0501340c425021a040d2250103840c0004401c4c1e80100b081d94050302e0044002c020700e40701c01e503001d020203950f402418464801d2a2202c404248a0400c5405449007030001d40101c0e403038036035801c0101601c03940060a104110210703142c07a803038030020302c40e0a1000b41c1e1010180d07185810000c40d0b421020b030380b5020341442001101c004d80c40e4046216000b82d444081c1003955501c4034041001803040e6000110201405140003030140c2d4002c0247c000eaa10b4404100100720201300501c0480c4158841c060115034142e0711240924062844a9400002c00120281000c4d003640002d0360a00120744280203000040300b03021446078248540006018280c6400655040031480004031148c0c080958070814002c0c140c8000f0100e084d01a1b070010180b0b410415220 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 67013977 1250 67012727 67012739
    0x702150a0b0108090c0a0902030a020409020a0504060801050117010302060306130501090b030c04051e0712062c040503091018120209090102031003020103020702030109020907050c0c0406081e16 85
    0x948031a1020900080c00c04003c1a030151001c1006041c05e08010b0100d00f40078030700440d0340080c0d00000c04c0c10620903402e200016424400f4002011160b40c91740e0b40d203a5460070404060501181a000b040c1007043d0081d031780c10018900001e55043d00e0301201d00c1500c9030b0300c03040094046000594020002800c05000040507001604244800380c01241506c6a406a079002d01084640c2140d540d00e000c00310a01d07001680d1030a040b02c03504544a440e0502505129038101c0080e00c12030340c8a8622403048035000380030003240c0c058084105001c0a00013005003440d45965540b0300501e80b203548a000c5c505c81c0c0600c441d000c2c0103070404e0301022000801c0305965416502c2622005010b045e8015403500c2c00140504506208891140e10040395450300c950540d00114000c2d00165412601903594407407202c0942c2d644095a84a0380b00c650303405031344210750164142011070184156003d182020020320503500c0102e10460f07019020312007405044102c1c8440e500d003100c15080001401c0c04400c001c140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 67015227 1250 67013977 67013981
    0x1050f0d081e03060f120c040b0307030b01030b0105010305180604030516060e012403331406010905030f0c0f0f060703020309031c05031603021308070906050d0c0e0702150a 76
    0xb0070401201d001c6924171000082c48198100c00300c04d0200c0d03401004100c2c001d4940f40d031081440f40d0001c1e089910841c3ca035912400540e40030780040d900c42c00310900401443da4140181980202d003e81100c1840c0030b865070059039490058002004d011740499101c07280b0100b04445c480742504007000b8484405100c0349c1d40c0c000c1254200d203052100816011400c120200310002d02107991105080e914071003202c04d100180700703a0b0701c0610110000b5003500c0c40b550641c2e0041c11410744252a0102c0a410700d40e00141c09400c0d640d1100b40030387c1051403d42602000850829140401030300c91134079030b00e016030000d00c40080c1d00b01c003240d00c48004684401819800409014114030507800c0b00c1d800105030510402700f1a03004840c000140c01040082c40d408810a1150724208060030050704011460440445032a039580240103d540a80002c03c214042070060b0401400e090350b0394101000a5100c074081000d040c050880e49600c20000b0880603031081040e2001e480031000d080100b81071084007400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 67016477 1250 67015227 67015231
    0x60a08182107020306060105190f200c1f050405040203060d06020c03040e0f0606030c090315090309010914030d050a0c020d060902030c0405010b0d0c17010b0a120501050f0d081e03 79
    0x200900c05c0c44002241395000781d080301c2c0ba13a1407090b1180710a01e0f1b000d00451720941c401c00000108014200d00d900501c544812102d0f01c2d070200070150807490000c030213000e81c81280d254911840801804080380d00f07038100d0211816100f0a03640540d503039440802080100603281c10044c001e92001550041c801408405081076070300f069030009042d03d602090042e01801030756031950001080000c6072500c581c0000400d03014902074141c130500d9100710054640c081040310104c0c070940000501484540c1c4c4a00780b5405040d1302c1c510090800d54a10201e0768401b134124400090004c009500400c6a025100b40000298020840403002407a45820b00160034035900480c02846500034417801490503006590684a05183c1a404d0000070b07040040980030180300c00c4107000610f05010071034a4404c3e0014007812108212035566080e5940c001c00640360006070b41541443c2500520103a40c030b1201c4942d034910121501a42c01c00d090a1245c5a8030a007a00c240c800300040100300c550340c8000c2c010754 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 67017727 1250 67016477 67016479
    0x3140d02060106050a080105012604060209010e0d1e03120519060b18010815030304151106010f05060f0912010b010e1804020405130f0302010207060506060a0818210702 74
    0x14207283d07030714401510789014119103280810605030062005d0352040c1500460082c8001030100e8a80079a5080210500b090300d00b5207525400081081c11960415103008040c6000d41d2217122008207070326202d818111402c002003c0881c11001002894414038194100c0703049a4820019818a119180f4000070200345181201e030818000040350400c04c0c0c282c030f080c140c005600003150b1040000456581000510b02e821a071240e4104100b140c0381000500090510200d40301145d03002000f0160034138070022203140310781c0d010000501401050aa041e8106c5a0581c1c01d47c0d240d0521a1158a46001d0050400c2d08a090007503558005030054001e003011803002e8a4810b410700a00082c4000e48458241040d6040c031150082401414181d03c00303540f01138240c0034200c4e1501c440d5a40c0400c0c4c070080d40181c0041c0e40210300c1c0028400c140c802c1d181c10010403101039203000d9031100c0103400a00010040785040e413682070304050714041800300c8007481c1c2d0401074201c541101029043e50a400541e070503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 67018977 1250 67017727 67017733
    0x708010303231b0f03070f0b0a090816020109120f02011106060a030f0c050303030106050d05070e0f1309051006030605010b071106030919060b030606031f1503140d02 73
    0x5180c070b9071941010b0342c20389079407140514103484002500a00b0b40100a40c0c01d07644590044413501e40030500180507098801c15015462080798101407120050203010194030910f0041c0c0d90700016240001c0b1610212a80350b0061204135a000503200400c440c0d01000c0c11144d404000c81c00c2100c00d440e40440c452003601c6107803071910305d00903a943e00c02c0100c99498000300904410b1001c502d03130403402c4d01601d124900301c030381503920f600c0030a040d50001c0e070000000c60130100d0b001d41d002c412401125802842c61911300d849051201c001013419014030386885c010302d8041c40319102c1000030740107080351640040440e8800c10f000c00c0541b0082c40d041c8010340307010745814008103d1200c04400c5418142c3c2200c0c4035091800104200181d540c405005105c0f98880c000100c0301912075015480011030081c10002200640c01c000e01d0305100c0c00511503442600100ea02c170561102c4c2c50300304242d566040344001040d11141c50a0720300c501e02c94001410401011500b019034100c002581d1b1175429081e404c2e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 67020227 1250 67018977 67018997
    0x7020406060f0314100506090604150c1202190204020d020c0d050a09050102010b030d032a02010204050906040213210512031e09060f060406180b040510030f060b06120708010303 78
    0x180c2500002174410480d0010b02140c100520314122000d0212000300500084c501542d551207404030103400c00c40710003c41c0c45126a4010301008a400d00d4501a03503001070610710240a06540c209010752500078415a070100b800c000d0380c1000c0c0d0585000301004012101c581c03400f01c40181840e089924500000350000201040d2544103012b140c9113032a001d0000d0140309500031007078028014140341c180c120b480224885040b1100341003108204280d5400041e9100d0412090140400c00109060b02560040000302c103c080d0600d2544119500307040004c10b69043c49407803004010003000003810f20b00c22071208192100e8007400450041c40c203038403454400d800140501501d40d0044500384180d4201400080310100c110304603d52080b0003c1001484680780c1c0c00141041101c0701350160240da4034400c001e07135402c4c02c0c4240f940290140030b241c4a40e5145544010302145841801000c83e03455101e241d00741c3e1221404e42e1004680340101c6941840d080c0300c010180a0244070960005000700701c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 67021477 1250 67020227 67020251
    0x804060f2405040605010815120a0b04061407051e040803040e0610080103050d0c0203160603050403090f080d1121070b1311010e010e1201021b0d0507031407020406060f03 75
    0x1045000705c03101030315019103d988a01d00404c1500300d0f4140150450419510803514078801e00440300c05520602900c81981031500b000821070b10322001141400740300f01d05000400742c000c81075034161021103141005494015480c06054021580000c9051101140106040e05c0381030546d84140320039910250451420802101d2651003848040e2440c0c001000070446c4074070841d5501010b600280844a8440306a04070155560259205000203580c0703001740700c20180e2098641c40140408000c6039075490502003156150030164804505001c0d040e070076030300c41074003c2c01001c0e18880780c21031101c80c024130114000d0f8a40d1005a044030b403403030b1040014508841e029030710360541c0d030040e900c00d40b400b644000545480c11015400e07414030100035400207203a591240010f43c01425480090b80300e5190342092129051075030400e02140c7c10038583c200b003440d441802d4917413280d054549007a04076268101a1101d00c65080d01941181c240ba4012030900c0d042a58502c0501107650708001d0034102107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 67022727 1250 67021477 67021481
    0x703110a0206030103021509060423090403050a0302180a06110d0c030c0609020102010207020904050d0e031203070f051306020619050f07081b030f0105010206090703050d0804060f240504 82
    0x40300250b0001c000e10042c405420110104201804402070030351500e24540700281d400d410031b0b44042180051460709000040760200e104c040c110080d9130300306450a15a402038054061107141904140c0d002ca082c0e0000085c2f0945602c1d2408050b001091b01d42e00d4450050146621521030f0384030784180c0e46011001ca01c140b10b850405901a07603000c2d04d0031000e0b990078000e4a410241641159002d02c00303000583e94800607580610b00c100010010071364a03e00140c5000b18040700e44d8440c0d00b05901d03c0b9800c28001040742e600a005c1e02d0078260f080d2000324207803403d00824550120342c05055101248507900050b41600958240b180001040d40d260000303026100c00701d0f10424001d8460300030504060040682542007a290b0b40c619081c03480c040c01d05411a001100c0f1080d000110500400c05d44d40c06000c0303250000030020103091042c0c2076843e01c1366a800951199020060140700250601901c5d500c4407242070000c400034400946441001240329808440c0c01f1341c506c5003a000001c50f441c242c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 67023977 1250 67022727 67022743
    0x170f070b030c13030b072106050315090a08070308100f050609010809190b01180902010813020f10080603010606030209030a06050a060305010204060908100b090408090316080102070311 81
    0x2a0320868503564850560054540051101c002529031048011000a01c90700c4a10301c99145c1d40d0790542d100c00c192210307401209041d200c035490700d890158240115280440c010150494041c0c48220503101c0184180c5080c90703205020b0050b1340041074a80405500c2885280a00d404101100740641c4541600313000d01058490a0742c40b100800035211554040c0300990b50000e0781c4000e43c0c3e000c088016451100c2d001e50a030403503420720f0100c014070048182e80103c041012540000700a000c995038000303031018002038800c1d201351100399815000c5586441d4440c0c0001d00203000c440044081d03082c05056090151780d0584a9420101c020401c41d12a1082d40c8030f40c10300400503c10020541c440e000285006803070409500d03100e40c3c000c004180240001c20042c840c40d6900400703a460b082180b401c11a07a0b056419241d41030a039001c0861750388080180e04550010303a89513940746000d00203484c052408800083c107141c201e44c0000c4071030040d8003030b0035040d00070b803144c03130403030800c4600c1c10344078011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 67025227 1250 67023977 67023989
    0x81204030212120f1c0605150f1c0501050f1002060c0f070206070b0402030d0804050a0305030c090307080f0c091e0601050706060807210c060305060d0c170f07 70
    0x414041000507281c0442802d002450100c20b07501c40e400e0308007a564940e0302038a0384000c126400030b5008440c40c12800342641c00521510300300120350401000800c12046824000b043c03160100c0c80707200100e0308000711001e03c1d280000c0e809440703003407030003010240400340b1030b503481403801e0060111541050302e080c0f491420654098480e03952039156001c420303017040b80ca21030040f900703004540041e22900020040c25015000d00d16031442c02d41704241c905042c6030034440402c41c0c040d080c44009600014551032a5178581040341d100d07650300201d0072036400f031000d1b40395043c0b04001d400a001e81020542140c09190300080da281884031000380462602e080d03400d40603036003888690441a50228103840d80094052500b140750100a40360101a101c01b43c10850b015000305004003d81110303040c610f030010300040c030f000911003099100e10076022480c3c0314040c00d05860304001003c0c0d03920702005a1503e607100398650101c2d61074907225180c03901000c1303c0e0780c10f80c480c1c580b05000c001400580d107812188 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 67026477 1250 67025227 67025263
    0x10061d0108071112071704120f02010e060d0504020406050103020705030d1805060403080a0c1b02041a030312040b07020106030c180603080c0109060f06140405130203240108 76
    0x2098001120030701030003841c920811188011a031142001480280d090703202c445026620b070341032410085084c00ba100d80340d60038824100020028010300d008901c50b00d5801c0601c000c071440c3c803400140c039100710940f00c0070342c003030000035091900c4101540070b68010f9000341c0741008030903180c80041d800c902c54000043c000340e0092000c000d0040b142d4019009022030100344041081d01655190310380601a202280411007240c100300300b5242a2041000d0410039151459035480c103100d40c1c80314000051006405551180b84400750181d10003041440c07520058220303682e03000940c0c010900400203a03070171906a9244404034130204e1050244d42c050b60b40112046901c640b42c9202e003840c0316103154901c0c801c40e071120130000c003141040c0050003844114800200340800076217008811a0129100d40d0900c40c90b000d400d020280c0c007951071584801c0150350018180c0c03110a10341440600d130880007940341c40f9460001120581c0148070881c01c1c1461100300c05140d8a41466070346a290f84080922400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 67027727 1250 67026477 67026527
    0xe0606060d05040203120f0415050703090b0c0f0d091a090a0506070512070b0105012c0f0a0b030103030e010815061603050903060405031e1e0c0f0a03081006 69
    0x41c80d0340d00c066002440101180e45211010100d08400e4000e0031881d001104085020400030307107444030021070b511041c50114030700329151b0303005801400c6c07d0258007001c00c3d01041c03090210400300154a140d80114040b03d0b027002a0300b40060201a050161000350701681583c40c00d484d41e100b05481b005031004003612081380c01d0209001c01900f11603415182c9120f004036007002d00e400400141100380c05013a00c10394a604007000506410100f8182c8040c040e41c01c3d840c81c0102015050360039690710700f100c0303051074800c09200280480c4025009002d1900d0300000000400d40c2007440c0d500c0c1c44000f07894010791035035032401c0754011490150b003090f0031010030441c1e85150514480d8000886100c0d0030304504200b60100482d00d060b408590803a215400051021218000900d09420103680500b40e1071420b410056281d8400c88500440c0e580000d0100e42c2003540241232042c01c4200d18000704540c0907641505004061304406d0305e036000c44001412303001c14038a1080b00d0440e4042100703410070781c1d46 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 67028977 1250 67027727 67027747
    0x70302041e020f130518040303050721060801110a020d05030601110d03050117030a093f0215031e090f0706030509010605011106010603110f03070c060e060606 70
    0x380c101c51070050715000aa071a1482101c096102605081c203001480c00c0d1518104008441000902d400c258400c0e8402a0f40c0100f00c0b081a14150b400307a458a008541522408016200e1400d40c1008107001d8100a00e4050402480c3e80311804a0340c105001b0711040d00e145448010910030304a18600503003190305010049030048004507040350701823400031402821900343d81d09101c090001200080e44520040005c12020b0b100ba284192908003d9031074220f00c02009804032101e03104502c1d14580554014070b0422101854110151008114064202c0b46180d000e401344080d04c4100c4c820b407590941070000d020500300366441109201c0540c0001c0d0000340c0d04403401c60300200400800d202c0c807080c2c40000c0b001480603c0c0141055200440c60381001a09076081d1802382c1c100078104001e083c2d00214540c4002000c070304440540c1000039480c100c0f0f915003806403045000b40c80100d400002400000d81c0d000c00039080003409100e00304030902040c100c454881c0e1054600c4c0d03501200070300295100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 67030227 1250 67028977 67028981
    0x50c011d0114011508190f20090303160f12080403020609061009051005030714012d080a1410030501050f010501020303070f020f0106030f0b01080703024c030605030c0307030204 78
    0x601100070210303c04c406c01007a047e180d000700543d1184e41c98a44440f13628040da008004403c00c002981402c100f00100829900d0180700c40000b41e000ca540101d0040c03000c030600b4010344030381118042c2d51403491140d015000c0038090b1400c400600c42c0000040e40710001140a6004240d0600a21000b42c80c1c81e041002804001d024584070000e050030024440d030302004400000c009a030101e4440881103c0050013001191080400401e114502c0c2c8100d4625100002c2c151120343c24900d8035901d4010490300140351000007891b01901c1d2209010710481c240621a00301da22810003849190b48540603044118001c0c41003a0150b4418808a0503150044a09401c280854411a10044580f06140342550708640c4150b81041c100b42202042c002c401341c406014252040050140c00d2844e404580a000c0c020442821041407544032483d402203e034040c08112000b003010448141c8031411010365040740d45c0d108000c24900500080e2506000c22030411045008003c0d2010380c1c40c40d001d200c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 67031477 1250 67030227 67030231
    0x40c03020d0212070e07091a03220c0803030114010c0b060f060720030f0307031202070f080316080105040903020a0212120a0203040f05010305190903050c011d0114011508 75
    0x40c0c000035403020071004907000c01100e001006044450f54050411050250028809801c00003041c5442e0707882022440c0e0200444e500552480d40007100340c50070800072b030030b0001c11180042c60154440d00000e4000d50000141d4140d80f69404101282400d0f00010340300c44151002c01440f030b60802001a0342d61170130421080030940054030700380c5008040d643e40325040e000c412134461842c1b1030095202c201d09041207034040285c04c0034000c5140110710748000e041c0d80302e84004c03401c03071503000100482001403031841e402c460740e88901078a449061450081409250740101d2a0016410740000101d61030140192004250960090402d089543e007c0c043c81003001c0104070041e1007006504180e6a034140010409a4016409181c950707080c8440c440c1e40da030b210f81c0040d041504005c20b1001d45c1e07070780840d804405c00703452070b001a0b03144142c581580e8602030444402c1c0103510f80009403040043ea40302c5011950708510003001405801c04031600114800c3c011450102c1d1900c403455426401904041d13 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 67032727 1250 67031477 67031479
    0xf0103020f010f050d060e04050f0d0215040501020d020d05040605100b09010513050d14010f060509180111390604030804050a0803010f030318050f0d0204110c24040c03020d02 77
    0x1840c040e50401e80c602135a03074a500082c2d001100008020030b00000b44400c80c4240cac1824003401c0c0d00210808002e5489128100300710b4ac044444001c103007000000d50488414181109044d501d4601e05a8050018801220142c0324581008001000e60300703464024000d403000000e0050804000600454540e004a14050140c0d50200301c0801c00317603115619040600d00c20320400c80f80c603404150041c00d449440141e00012801c085042c44a656049800355000e610300350000d071101461403425002d80030380784003d00204070010340b078810000d2451035075201003980c2d03958544034000c17003808114601c0c18899202094002c040494006803003810200e40041c064001c0300c100040d1511142c68580c002e0740443c00301c0385050010010140c10401002c440124085c808010074a05804506c1c810f045650b040e110f510b4068481085607180d0b0701c851506c2041d2103100e921204003400190b82c42e44e4503d90b0700444d0142403a180390b44003020503503078407996018030070b40207072461a801d106415604000407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 67033977 1250 67032727 67032737
    0x1150809070e0a0f181416051c0f0b0a060501090602030f0301030305031003061113060e09010302150d0e070303031401141003110a080a050114061c0e1506090f0103020f010f 76
    0x10582e2001c04251204501d010301a994180c00c61441b16524040000005003200c5a80000420941da2860941c402c906410b00f00281c010141749880207503030703035418401044c01c0003070400d1121f250360f1a0b0000c42556000c0e261a5202501c9000c05e07a5240622044090b460400300014400a84604040c2d40c202c1d070501382c4110025180c1d81c504e41941c2c03281019250906c00480c0c041e030521619070355080208650f092800b02e040000e40411a040d005002c00790003403056805e802a03007442d5030101e80701da42855030f00b00480a210440c2c207032910024481600083c0c10800c2800d000c24a40290038101e4283c51080c0810300805020f103c40509112442d0041c541c0d2210407034110f00008004296141666440508618000c40b10790100c58040e001444099000b40b2604156125042226800d504461803000740e010662038450217020071070303089105402288150104c1248034820b0b03500940c000c40380d406603a40c400b01c041414000034400a0f5100b03c00000303544055001d080c0c5c40a02c00748911309 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 67035227 1250 67033977 67033991
    0x140f0708090a090c090b0a0f0807021c0503090f0c0618010905040c050c061008030a050702030c0315250e0f040f150501030501080307050601031704090501150809070e0a0f 75
    0x6a219030b001d600204080b500ca02401c949540e10010000150100007000e40c01e15041840c000e040c1003950348c16206209441d0003089909000300250b00302c80d100300202016106092200400b06d8000342c903203400f14882c400700c00c4000c4401055004080070027410715424036070030140240c00c41d600c54110a05004000601207650344640c0544100b10842d921a10350b07404805010a01d03050f80103003001240c40c103094043c44441808030849503070351171902d0101c1d240d8050740002408c1c034a0080e007003a410711400342200c40c24130f00d204500388105e410309141500520348100b900503030107081c405000094134213516044245007500f49404a4400588000342200c10b03c0003440840e003e1074074a20720003d165108001070760303040c003c06001d462480080e6041408984e1080c2e0783d2441800f00a12041d0203e60010980c140035043d00c000f050035103c1400a940d443c55080c0b05030750400d000304001100302001603012100020036804039a4529012031040c0e072078400c400010805540e0740300e4010f03100c000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 67036477 1250 67035227 67035229
    0x50f0d05012301030606050a110102090306010806040b070306060e01080903090310020409060b0702090f040816080711061201061803050f0c0a061b02010302091206041b0501140f070809 81
    0x42024040d1149021140c1071181e4041c8007039008529074461810141443e4086c800f00e9401002c3d05d0031a8a20b040070803010720b80c1015180a0f004510003580c16100c2c0d20000125100b00041c80740c0964018200d0702c000d42c5805000f02e056030960300644010521001401d03040b54441e1510540c1705009000380c03414080c46c800040d0503c0e01203124140b88036000702c0e0601000c405880b65400900144100740c0c50304290760b0108600402c010505421142c04500090501c005001110041c1c40701c104107500708d0896103000a440d401c4001d068a024075010b48081c028106042160000010891580030580c40c100c812a41402112101003029550342d40000000c2c07000c102e25031400034424003402641c02850107200c5130a4040d481001005a00c0140341000304520640281003902071034056951004100800c00311121000029102e205820410040c000390210342c1c5580c054090340c0700502a1340f58011200c01240d4101040401000c2004c2900c0c44284001042480e1044051030b0a00d40548 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 67037727 1250 67036477 67036481
    0x307030e0a0507080616020703140a1b0306050105090103030e0f041b120e0307120507050c06031602060705130915030204020406050309010b01031e020a140f07061104060807050f0d 79
    0x41c074101e4050340010342c02d001c20b02d000c1c40040d03440b00046403981c00c4202c0e0002c000f99180d2051201604204101c404200640e400707201032400e107608000050854661071010254104603440103648031841d003030001c01d961804a2045d412617130583d840e0440480c0342d904000241c62130045440d4060fa9680d80001e545048001c0d46190000070740f142d5580350300e9044040c0543d420701d509001c0340d400411482c00003d01101071810700110507c1d01d1a100c00c024030b030840c900344e04800c0c125805000401001a00d40561001c420060550760960704207803200d005c1a541360049240303090807500420000d000c10f03500b903888019001075503003607000030700c2d641d0700464204c2e881600948000b54002041002640090003000403841c420b107410440c03d0301640f80050802d00d000b29010f00340d40c0000c2e0814205104260072400e14007130b09401030b540c001052003103400d58840882160380310700b003c83c03500c01c90b0200d806a400300d64075619003621701d0703a44d00c104455030f034801d408070008000c050200b10034500713040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 67038977 1250 67037727 67037743
    0x20f0915031b01030b03010c020304150210020d0b31020f0904020a020304030b13080d021c0f150b0c10020a0c0c08010605090c130902032701021206030a030906050307030e 75
    0x4400c4000030281d860b4001000da80404c00342c0760003613040015520b00c3e0b42d8008112012590f410705002e05c10341e01c050040741024042c0d01504403850002c110f565070300900d80e00401049074103c61141c0070780081c0d1051184c1901c071281040c510b031055201803100105680041583c072180c007139020310300149040010101d030005100b00700142d00c0400c09104020803410f566402404035000d03014598560368520443e4452040c030850859000302d449183c010507400c80312508461014140031222070000040010100c0b030a4500f81d0301c148550004802440c1340444222801080150071829100c0080c00040d500c10701d80314080007070030300c190000b2421440204015021100003c1107040ca8001001084200581a07800c1000204029200204500428421111203c42c05a00d0703513292052000b41503015a030440e1503820500304070044030780647c01090542c0c0c1042c42718401341c4484050640d10826580f00801056400d01c09000c1540148099a8401d0702e070318000ca1004001d030f5a0b9810080300d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 67040227 1250 67038977 67039003
    0x906090c05030114090c0f01090512010c0806060708070f03050708030a020c0d030b030604020f0a09020703120606090e0106180b04141e01021917040618060309020f091503 75
    0x40004103118910702030045584401d01d50210f1344290401d010502e855018618005101c0c9542e03c00450441c1d008a42d80b4000b0800205400b1080000c030a82e54041e003e0070761380b000001d0203140020258504001915009074000c030a25084c56030541e40c00000448540d030660034080700340000c20004054100840c4903031880b080142c2c031000c0d029581841c2840703500d548800d15041100e00501e81d01d001034090f50003034040740e120b2003810044010a107010125000b031403085000080c7c0d0300c00c1c5a0000d0340b000c4200a9004200300d02d642e0751108441114150050752150111400108281c612902c4949a10f039903d000040c0c1039903580500203030039405640101140d0181c81460041480c10302965001e2050700c100b5440d5030024170000035119190040c0364540560009500d20601505c40e581d992094400111a555141c6402c8040c01021444004000401d503a4801052003482030140000e00350780641a59002c502e81c0c800c00900f80c000800300e0b0f14081d4003484401d031642d8204200400465 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 67041477 1250 67040227 67040243
    0x8040f06050a020105060a0b0706200c0106030c12020102030301060f1103041706070806030319050705060f0105030d03060806060904060b0405150103060803030f010e06120d021606030b10050d090609 87
    0x2c20100107400c0d01c2c00104034620030302c0d02c00020030800c41c0d0700c2d04549015901600c002160151150501c01c2c544907440492912000490070109142c0c055101e401030701d0044901100b510ba0b01d1100c1b19000d236034843d0090041e00180300401002d4003400001d1411441400e090f1028414019403a01c6e5030450f500c03642051901307000c01c3c0340c4440c0500c0010341107403645c40c0c8030b00e0519150000c2562031203458148649031081115100319148a00165407081d5844800e941c280c1c204500a42d0740e80c3c0081c01104e1090040d20500b40d0040c6c0280701d018111000c00000e481e00343c4d501010003000d007900400554400d0f803120307403034001981c45209080c0300b07c440b101142c0410003950001806c031407403600100202d40c4100248104c141e169050181140c07042c0440c2509682c5e0500402c60304d03a00c03800424281d100d00042d030030400f50042201d007812180224a600010b540b0746080303094a0310a100c064001c5401c4111851003440f990082c076031040f1054000c100c1010355a174030310440f661407000b81c50600b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 67042727 1250 67041477 67041487
    0x30915010902030907030305090a05040f020403050105061207060e0609031c030e070513090809031b01030510030b1b0c0f0102070c1212110709050103050102280210020708040f0605 79
    0x499121001409070a81031421821854505101a42d4255500010301848408560b07440703a41d45500f8101c0c06004050300070f0003201d0f03200005601a41060104a495508200024049003041c0c100d070b81c0b090100340003e0002034038101060714a41c0700b900c003450304480f080041c1c004545007013088205040c140c1180034114141c1000040c02c40b0200402c1c0360786500705c2d400400c025603d40040e200300007004000098101402e1602c00414882d9401c0310b80c00d8041c1c40c02c4400600c140d4518084480030a0f00e0a000f1035a88900590002015010042c00c14800c000414241640d1840c08003c411070207500d41d25000c000c079005481d10b01340c41c11090250303400003011001c10240758651801000c44031030802400a05980301e140014245010b4810000004115403212404001c1c040050850940c20045940c480c24124040d5101114108880820f0184080744001a03e0100780e082405c0e405890424230800c8041c0203948050010348c0e0303c003400d12000c1401d0000064482c010581912182e0f964 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 67043977 1250 67042727 67042753
    0x1202030d0b0a050a17011805032d030708040f051c0e0904030906110312010f0e060d1e05010f140708010b0c06010504020a02030d06030c090b0a180c090305030309 71
    0x256400d41c00c10760140100441c2001591280180d1303909645084600008480070741000d540102501c1c40726007070141080300031200780320011000f0002122007125800c000f012584182e00c1801030700c0d404510000d07003000041c400302d10070f61503541c100d842003802c2c884103400d40c0c50321840c0c201d0488107444044103040710b001c0c4058228000b800040016110b1401a1038161405000c1500c00c0c840c6030300740318282c881404498014412500314800c0c031100759090b5612440a10300060060240c140f400c462100072901916103400409a030a520452600b08092500042540200301160488040d926907101140c00d015030700540c4941d080c0e05c500704543d4541484020603545041c0e001180d4440300b0003080011140c041507040c1951f50680e00036a840074030140407495413041400401901d450a0b1000c0108004030f0b85241c1200ca03010b03000c2c815046240d00b04800c4110700c0c440c6090702410303504103609414640d040515040c6150610542a9540340c41c1d09086510841c1c10600701e4014555a0f424 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 67045227 1250 67043977 67043981
    0x6040f0504020604120804030b0a06060801061110110f03130209070903050c300105041115030609060a0503030d020d0f0b01020309090910090f02040f0212130305071202030d 76
    0x24100248400c0c006810140c01181d440d21990241141041d078a206030418083d4050071500110f9002c3d6600c5281d180c40072500c4010300d128001c0078001100c2000024842d44204c0d14011425080405840c10b81071526601c0c0082c18404001c044883d1300340010310320451f984015500c03540320301c14180c5004956104100701d181005103000148a81401c0030300201328001a001903002c001e84e10611040f55050440c25440303848041356550b00d4545a009a2022064100a02941c85105c031280001c80020400107030140d41c03140170f00101000d1000480510701417070040c2d000980509582103103030312078000c00e0440c0d00000405110301d8000401d1001c41400e841070f030140c4200d6843c01c22043e04802c00003902c0b440740da0066880703a01440c0115642c410180043e1800c0201000100001704103450f1040c05000c01c000d041e403007545080c0841c86004024000c481c155002d9012021a07561411000600c408041d242942006420b0000310300150200e0220302c4050200d070002c0d900c590100b804001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 67046477 1250 67045227 67045241
    0x405010603020f0403060203070c0b04241b05030c0d050c12010504270c150f0201050919140a0506070c050c030a080904090203011121010e0103081206010c0611030604 73
    0x30070035104025440021000a064900384c07a4824005030b41c1342c640207402c80340d40055642c05440c50200b001807200300800700104400e000c806243c095040000007640008440300c024047d528034500260b0004650320a10085a0281c0328020403420001148205001c440c011140501100b0340001c80c0c0c0348440070080901e0040808403024040c0d17484007504c220107000c46a0958820741000d90581d4104690500418054003c2c3c941410420010b020001c0540b51002c5e0544095464100498001c802c007280d100300d5240a40d03030030440100156202c1e07810207030203403000d5554001d210115002400903c607aa014071007980d80c610140c8024100300381030400c403503800c0384654000c5081e08006000320303040d075005160807500020304c40b29500109014100c400c9801103610390014958141540318044600201d142c4402044260780341e0101e032908000030300020b840c08800b03100c1d403600e610200700010341c01003041c508020903100e140e880034285e6a4006012400c07040200420280b0b0400e03118101c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 67047727 1250 67046477 67046489
    0x9010207080111070204020d0b03010f0b040b06041a1608160c0801050906180708120d0506030601060801030206070606050405100e060a0b0711060915030603010b180a0e010b040603060605040501 85
    0xb200b901d080c3c4804415110f19003000b0700468000c10056a8032405a00084908001400910050a200308124001d04141c08c1c03032442140303802c1c00c00625040c008151000d03901026025070201000c072024490b1904208404541c142003902114005800940648000307400d45e01c5088140140c1d02e0b0102c4648000e40080a06a241008002c00c030300c4001402c580047c4545080d002c0c04140e0103071355041c051950000b149920a000045003100c010400038030001034203140811081e1100020151121030030b01c40c00c40003440050042c00503240000040c040941715020009107907a40f40003090940ba01103413149507004070903004000394543d2280040c0e20513012100c0740b03402414103811070003a0081c164054071180c28815149410303180c1400f2a440854010040c900c059410541c0b090785a108840c43ca01030750a1142c007480c2410121071031010860701142c0400740d641d03000401001403c1c01d80e03181130760759203c950440b50f41d2103d06c10680079501922000c00e0303403070408050100303071403060b8002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 67048977 1250 67047727 67047731
    0x70801090e0d1103130f0302190605071403070b0903030a0e0f0307031107080a0b011d0106170703060e010609081506030705010c2a080f0c06090d0201140d02090102070801 75
    0x260300140d101240701d02d0350344802d003014281042051420307840c601881422140020300c0200110f030b110001c803040b0007201d01c03c45030080403600e0801d001c107841e00c0522488011078014040c190010350400d080d548070480f1a801c69042c10b0303503501d5001c801c00c016903010b40b030f42d003000003480045052030180402007031a210040c4201c40705d85c40785680e00c2c45290409000c1180341d2100b8000c0301d105110b244024101201140e4202241d0700700341c0440c0c4403c1c030400346104c2d50001141c0c0d00f1000c0300f003664100c90b416210181c101c24844000040385400410500400d540c0310404681d004e020304246d4003130007040d80c507031840310305041c40c1c0b514240500030030301c12107580b40c000c20601e0358000070240e0903038030203103484080941e840c90900a0401180401000c228850207002c0b01880105400c808540d03054044489a0109003d12501c07080c01840c2550010010007400c151424201007845030340b48103160654807080c2c2c0408150f0a43c000c09121407280d030f00000e42c0000b543e03042020314060f014220003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 67050227 1250 67048977 67048991
    0x1080d03200d0908030109020406020f1c030902040212010602010c0207050103090b06060703020708030304120e010c0f11060c0613060b01020f060106032703020105040204050a0b0603010504181a07080109 89
    0x101c14588101d04000074000c000007603041128801500320403c55603124658a89a507195054480a50458010f5400520500a558240d00b60004150b90300e6030341e43c00002c8284415543c00c5000c3c00010a06980140d0200301803503400c81510241c500030b0149a0002884c0310f0380b500028202022940440d04041c1030810241c04200d5100d21a03801c400101e90040d0340f54460300e8140c2c189a140e0f448903d4500002c410403091003031005941c84d80b0f080594410b510b20303240c50019901d5151849001d40003441d884000b0340020440c0c0040340311850028803a600382400600240c0c54120115500e07181a100014920200000303401501c0c48400240081c11050540352036007a600c4a051085008043e2216044810745201150102c2019242c182c1090001028100603010748010341c1c00700e00451401000405004480c40341040104001345901d2640c0d10704010400135003a040120002084040264030008a1004030b00f0031200c00d40f4055040e030700e0012005499140b0590000c074000d402c0501c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 67051477 1250 67050227 67050251
    0x10501060813020918160303121116120509030102270f0315070c0206070803070210060b0703140d0501030b070306080a020f0103150e07090f120302060118021c020301080d03 76
    0x591548600b001d01d0503590a60034922007450aa0034011180d011101020003006065022740c0f02e411100c0c0469040c88503010080020600c2c0c407500d01c040945200f01e200c51000201200910030052182e4540a400c21a8100000e401c80c0c0c040300ea0890100c100c115001c10034090201088807005007220382804c010320780b0022948801030321142c42c041c5042180054030b194056103200d11f03507640280a403600c0d008285480041c95000340c4944016101d00c1c903030300c484041e003402514280c542120b021410076189503000d036101d0384541d0aa40c04c1718030500818240d44243e00c40c040c000c600071a078200305410210310142c101c91080d000640b031f6070440448140036807102e076600e128085080c6400034010558044662071244e01360070505559039200f09202031294403240e0841500c0700d488005185607565408100761400b000002405078220b04010000004121618001204c03c440003510b082c980840070b41c0a44908020081c03e280e0110040c00401410000420344072041d0800f000709122071a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 67052727 1250 67051477 67051489
    0xe03040302040b04051302090c0708071109060d0c0510050405040c0e1206130b131506080c0619050a11010f020406080112020d0b06010309020301050a0b180106080f0411030a0501050106081302 84
    0xd00290007500d00030027007600300414804454400e81c0100c2c4490f180c8140e0f00d41000b0501c40c00310113500c07520744800410079034030701017640070b100300d0f4080500041c1034603200610111921100024040c030405010000b2039440e20f001781c1000314070554a0311940c0c02c1242c10014801c0c050386040b80349600c160708118454810820b24201c0981150100200e941d4403c0010f1034012200070040103240c1c1001c800c00035100070382003030302542c100b8000e40300400105018030145009245264035801500351b02c498845d0f00541c0204140c0351f182c90640142c452410a230340c03e4138040c3c2601100d00f80e0004003000900c0c1c0c003080d1680540b880c0d02000740080c0c80c42d00059071030b24604a01a11400403003000c6125030b80a42e1003050b202d0360240090010b49840d159000080007071250050252151500c83c0d04032a84a511a9041e20000d4441c00b9164641c13030030040322041c0040044881c40024030007040c00d96010020980041d10490001c2660342c18001e004012040213803100d9007800c0e004000c0001a9206 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 67053977 1250 67052727 67052761
    0xb07140a030f0f090b060a1a0d0504052503050705010912031103091207090606050a020304031101020c090a0203060a050109050a06180e04030504030b0906040c0302011b060e03040302040b0405 84
    0xa240109070160002c0d403940c0103203001c000c18480907207442e080508024040050501c1050704660242171955103403107400304540b0344040407201d10360403c141c407105601c540c445a0031a0107101101e51844503210144c0d0391070400f51042c20002c103c100100304015041108402411007807900d081103030f1409801c0c00b032030800041c0c020280000b142202010960810a4601d2000002d245c9025044100202529040d040c025480105d0030100046401c501400442d1070708445a40150700d06455510382207003103c504000a4114003804095202698030800380301d00030b850400c00140d41e030070f088041010300e441c203500850511020000c20403483d0384054241c0e04031007050920140c2ca00d04803900c1066000183c20002d0b1b0894080c00780428503034000c0c00380007500d00c510200000e51700c0d07980c40300e0b41d6032204580080c03906c090000e0900043d48100d500340070020032101562903c0c07200340e544100b62400c40c1c0d806480d40d0300101c0c0400652806009100303880034151010800c40c141861000c40d0002a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 67055227 1250 67053977 67053997
    0xc0c060c020c0307062006060f10092301020c01080105010228050a03050717041a1c0914120c060a0207170409140a0b030a110f04050f040b0714 63
    0x65109800d80141c0240406002550001c041d14550b544445010749401042090900060090004009001c0000404900419004000d001c0b0340c1c0e0400c08210746220300d405d10604000c2c0d240c1d400202913031b41c2d01d903100c0340c4000d000d0500c0041011400080c5441000c2d18151b041140c40401006143d8000c00c44082030001e84103600d49203240ca0210245607074141c6d60003410f511825460b03005059001c00600b010900c200d00150024188400c0001c00340618001c1c1c00590304408030981741000003400926030800641d4208035045180503600301102c000f5401a58170000006000d18400340a200580c04241c621800030709203210484d40340e0303032110028090084240d0026000e414050001c030425521035400c001565220b44600c0280d0152038501d0040e40401c500c0340200d140c905030b40c010401d00790b2001c1c00403c1000029102c4a5000d8030076003d042d00300d400d5600c0340788691664040c0038440ca45501070107519040034a403142e04401300404440030420030201c6a803e03050500c045440c5100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 67056477 1250 67055227 67055231
    0x7060f0509210c0115090905010608061b0306040b1306090b100c0b04050f0a050d02061005090f04170406030203061201180809130f0b1806010203161a0903130501030c0c06 75
    0xd21020303280144006001003200040017403001901866540000034031a01c160000c0c080c450b981c00750039035211410b40341c41d81c03895800850f40d00380b0700013840610760040004001240100e250004204502c2c5089c02034641d964030350780c041c0300481c41405040040c1e41c080c4c500456414003810001d0040030030300070042044903a24041002d001c2d04011081d40030107080f069548600951504582e55010b20319450058099400002c20001000c0c0c000400c90748042c049090640d22800015039110b0010070440d143e802410400c550020721002500252480e610b00682d030b401c024080085900f115040c07003003160304001d064205190a020090580b6a02001311a21a03140300700081d008400c40c07001904503071600c500b541c003501041e007007000300c40c0d82a070b10188841d655011450010100322103c9026a204001000960307003410346680c104d901608051000c00c1c16202c00350884002a901114594404141c41081034050002480281001d0a0030032000691000c041c01d075031240000034040036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 67057727 1250 67056477 67056487
    0x602070203030408010e0a14070617060307032a05060301081903020c033408030318070302031b0a09020c060105010309060239010b1f05040b07060f050921 68
    0x744040064801500e4800b00a0048524012000703580e50305040040d9000f070320205507402d03000d0f07000c2110790640c1d20554030000e400301c006c03585c031042c01c8010740780c141c2620500000201180426145070007080401c41c440e40824a99002100710088a4005501c1940200010447c0381c00c00603800403500000c100d01070350700c515810f05a080880c6080025003500503401e115181c0088051540140d42080c50240e90103080c0030301441c03604c645401100015032041001c500e100000012030110b65074103101311492280c4990103e41059010846000e00c400301000c980d0180c03820f8200790000d05600c0c6001c505101a40010300d0340c030b010601c942e41c1413560b5401d001007032003200d404807503185444440c1c80e01e030401c0c0c509030091a02c081064007450213a170411541c501ea041030194015401004003135181181000603100c043c108184008400d00208001c001204480320b4040c0801e14080c4000007072a45600420000340d840c02821a40301c0e0304640c2c4040c1041100340350f25514907038809a0f40c0c0c2c40e2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 67058977 1250 67057727 67057729
    0x6130b0c04030b100504060605070f03140f04030501060905011509140f03011a0f010f08010515040807141503040b1906050414101205030a080702100504060911031906020702 76
    0x144110b4001808101418040186404010070315a040711402c2c2c2d000c0040075070b2008210740074042c2c640b0080202d1302510031003004c40e200300b00204040030b00309500e500d00049150186c405511650044440765100c200c204540816880b95500511010118920450f00070b60002e240704445d0090100b1041d00d5070200400d030300e50040c0b0440100c8058020001072000020702d41344500100070051040601e40784040045d4070a0a1644901307c07140c0b01c196050b401c2204100007184442401d01d807003182032000250304030080216034000c080c545214000540050f06103c80407144402c00d03101c29008000303110001350750540d01da40c4114905001001910300f6100036018008550103588d2060410314004142001900b860380501408501c180d1030a43e21241640c189140090142c070741d41041c4801c00342c00c4e011b0f81156a0018a62040e41e5034001840b0030b020840c2d106a405507031040d611107140d01080b20540c070300028404114001c2c0b058182c00481c4004204440900805194010640c01d00b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 67060227 1250 67058977 67059001
    0x6070f080709050604030302060f060a12030507020303070b010f1a040e010608060310060b04090b04200c070302041107051509070603020904090f0f021e18090a1a1806130b 75
    0x1c0c001c0203013082e0b65141d4a040003541d900090b40c18508a40d040d1000c100c042c40d0a005440884008100303144180603c0e49040d500f58101000503030700b50104000c1c403000201720400450203050513600d071544442c117201420b10380e5804100031317000110040000380b2403100303c0362244d4115400da180c8030920b55035031004642004e0310000c00700511401c1c96004150321840f075014100740c4406180c01c010300026042004280d80b500600c0c9480400c501c4503060208150358010000d40555004480c1c0090790396000c281100d29040c88802c9030318010641c031003008014003040c8920051a1203d100604117244800e45070a070501c100710a0550028080c10749448070707044101007a0700500d1600000349981814201010094000ca12800d0306000c080306401200465030101c400140c4001d00c1d64050100031103032014054804c2d1107074417400b440800002c03594185100800064042d4610718185079112101e450502401d185541c1c001a0030001c140d0714848440402d56003109404003113441e2603e078061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 67061477 1250 67060227 67060229
    0xe1009050c1923090406090212060705030114030c010e0918060903040302010e060403050a030806150c1f0b06030406150b0d0c08060607030509130f18050f06070f080709 74
    0x50410101007000c0c0110030340000391030071200d0121030040b01c2c044412102c80c4601850350f0b043d610241c60800324020803820f5103c86080f0f44007810001c0c4010034a8402c51801354111000800202c00000620a0b00c04420f0006041e801c00e40080c0407200c42c1c14006000d44c009204003a00440070800001c0c031442c0526110086030501d4410b44dc1e403030030301104442e120791060000f41c0c041017030101410b01c0c0d4203016040710122078020000c0c0024103020f03036040707031422009001c480e401b5010105e260b00d02c0110200504046807000e000384050a480d004c007001078a19044004425894259609020788a00040740da010341d0106000841641e816071900c05240304d500144681080490707036400105040c0e000254940321611600d071296505e0307007002103038824290020f00150052020482d582425001414084080b00303010900034030301560380d021503482108001651100c055444203025060000c89810013094016140d2440c00c980f01400d502919000350003000104000183c440f889030304500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 67062727 1250 67061477 67061479
    0x11030d0c14130e010f030510090204060f0b030604051605090f060d0606120f0204050a05060a11030d020d05010909031407030905100302030a14011401110a0b040807030807030e1009050c 81
    0x82c1c46841c25500000c482640d8007400d500c0440f541c002003841c0c02903010000469038041d000700720b02490145a100903100307441e4200d0708161120404a01c010100b118007000d040c03d524695200d03d042000c12081e01d80c05071102400705c8903000c000103480e41c0706080b20f648000640c0e203082c55080003400314995106402407181c005280c141c3c00b0035250f500200704c5510a5a003c02407050500c442c440d2404c0f840f50344900356000600407030401c140d05118015140c2c0c6416410010111082c6009060855001a0321a42e6050b4001081c0883e400c16100c5c160162404c054200804240381c2c2d0080c000d1000d00a04103074010021607044101407107412044050310014080d081140d0001c0760180c06074000f91181985a410b10701d40802c06820f03651841e048840301c1424418501c428001507601012000325000d5034010742e060f410100e07800001142c010b41c418007400d941e6090701e0074010440170b4050409010581040103a1014000020784a0780702500810002401d0f105440c0c03503860b210b0840511 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 67063977 1250 67062727 67062767
    0x922050708091204080a02010f02151602120408060403082205030702010e0d0c0b03071101060b0406020106151d0d0f050606010206060303040303020709021303020d0609050c0111030d0c 81
    0x10007a4010815401052190102c808034590398000c1d400d140107a0044605580c00071403450701542c0300e00304004c0420390701c2c01600c00c420441c0c10549946502120a0031201040d02c0c032440003141d040200c45010b000300c0d0051400c0c80d0400300020388440c0c0140000e001c010690002c1781c2040360800101240600d03038039811100f0360141c42e145440e5004210700343c2c0480e14144610b052410000060300e204d0383d001741541f03012402d1003032040d0690000b42035081046035400312681900024455900641081503089844e58902000282075076880e802c4060018699045a0b0400750004e0556911100249944619011b0b100c0820103601d941c1d240a0103058007544e2000a0002c0464824001c801c00c0c1d00381c450741d64404040c540d0700d100341c0c44001c0044c0d01401e41000040f80e158054074001c2100f401d60442c490b43ca400050300407000103002c2c0c6056588240000c1006410800307001c1d442020b003003001c003107501650050380300d00407880009003698590a4084690388240d040d0340c66042c007031680b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 67065227 1250 67063977 67063981
    0x709090501021902060f0c03090a0b2706010f0b27030a08040909050105090105070c0209130b040305040e0109060f0b0a0c06050a290604060f0c080703030c02010513020105092205 78
    0x950780c1c101903c00c0c0316280b0325440030802447c0c840c8112403142114000900e140d107850f603940400440c0c01048851b00b500f000203c007685048080c0110700c10051000108019410801314000ca460103910003440d445042050f60b0701b04800c690162144509600c461841002800c04681011540b0740014401d4000003404a03100c03109601929505000c0d600802c025a034450442d822070b20180c40040110304418a41401071801c40c81c040e5201d840450a4910380129070b0300e003152803400b9142100403800c04030301070000701c0c80c510215005244040302408001d01c3d0000802044109000340060703000000307a040c3c9030314054800d4480c0c0300e07070080d0100150703d04130080c48014000295546075001500322002540986598980224a401081203150504d000000d60701d89000d2000c0e801880310710714842e0f01180e00302003d000c0c180d0107501d0210300185000d000900310380000f001c02a5400310038050b040541d80c4103041c0d1712180e400350b03400100c2d4844450320f00360703064690003114201410700003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 67066477 1250 67065227 67065277
    0x403141c0507021b0306011a07080406030507021006030b070305090f0a060213060c0206040b0307110105070807090b191211040305010b0a050d050606061c0c020d09080f070909050102 80
    0x40002d02c555415425190307640e20101341c40c5182000c40004a5055100c0c41c0140005280000a44515040b080031030f483c100c0140d481c4240d541042d0300c00004a542c83c8100b0080d245c040c801103001c400080c00c00c005190440d5100388100c03e0103040e110816aa680001c8d4003400200824014000f07017404aa9403c08c0615014010798000420030000303845005c0c001641d00e009440702000107038020121030820b410a010000550030040c41441008980d5040d05401c210a110341ca006950035500ea069034a031540018003001195400746c41005010400b007456040c20801d5801030845500c8c1180444080d00c2c0824058030140d110280d01900006001007006015408000079203420b4490400c0c15503203078104000402da116024119800c00d10009607a450501c1c018450f143c80311844540700010802100202c815402d004805a030018006620240d0003016440045c02e0150041007031400c00b400c060b495407418440c109859888009500801c082074041e44c01c2d490031341507100c2a41007418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 67067727 1250 67066477 67066481
    0x302030a050a050d021b0f01022401080106120305180102070f0806090606030601080a0b0702012d060506091c0f12051201060f050f03070e0306010f06020c0406030b0403141c 76
    0x224210f0b1107104a01803802040e0001c2070190342d983e8030450400d00ca0401c40c040c070000f614000302450441c0030b0900602100b00c529450859680e00036000c0310b00700d60400480908481440c2c0180e59001c1c12104031708000b9521904440303002c070020b4424404546240c0043c1d15100441d00410000480100081000c02002661a100e01c503207404880e0680c03100c0e02410388560080c0a2205a0f8000820400c042412000c00540080291000041000c40c158441d5016031140c0b40207035aa600c032100c9102404660300801000c2c0c04101ca40d01d00d00102400003860b03001c0982c084254040c1859208811300455445a0f00300c0c80d0420101010f4050a40d0014403913030084075203280855941001047e15842400950760300310700d0b5241c03146006030003260300b0300ea608000e00c503500b042007012120140e5107044c40120300916140041c40183c900f4100d02030f0500d3b00710000341c2c6c0902d01d04101040810b6032018801d0f0000e4160a00702c000e4550401660300510400295002c2d12040ea1400d01d2220059 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 67068977 1250 67067727 67067743
    0x506160b130204060e060312131a19080c16020102030403080c06010501090f0806190b03010f02031b030606040302100c05030304030206191a01030b01090e011203090e09250302030a05 80
    0x3c90301001802e0700d0f5101c20400420903681c00303801d0752040045c285000f201d58000e1009411441c10545040e50b034121030140c919402001101030400802d85059074225031007846910007803828031900c20310746404082c81e103004603042c03580710000c4c9400c46401d5900910449001d0347d006076000da500d01c0d041340016aa80303000c1c85074500144046c100080c4101c13010b03620a040d50311000151000f074803421012240620050003c0010030381d15281e0002a980900c5000b014242d010360268891820750f00c50807000c00007515020171b00e0300030000c00ca81032303840b041220300b6a6812644d04900c81500d00c3c044850003540c65008143d40300001c24403040c581c0000d031f014813a0000e004a0600450602c0d00441684e124444d1081d25407014442030a03258000e4002d0342c001a411f1400b503180d5039036180382c0800d881081c2d010112010700040710000341a403040520006e008980907a08290500c9a4180da403108a2881002d00031021034612000e40b80c00096200210740060031a800e0041f641422500c503e44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 67070227 1250 67068977 67068979
    0x406090518060405030a0e1804050d020c0a05014a03060703090b0f070e040f06080c0f03061b0403060507050a0f08061e18250c0209010506160b1302 65
    0x5188803a01c05510005020344210303800409103081415080f4156149100010010380c00071602110002130700380d0451140c4954007502c000c20074480b1900c6c019080081e90050b2034001c0c08030140034801c40e608513543c0a070845082e440c0d101c0104400500410010000300c043d10952032640c00340d90440d14280301100c00c0d0700110155506522912400e900300c50860000901c41c2c0c118800183c810b04400c08500c1e4000060f007800e003413500e0101c002904035008494520b00641d0b072032105000000040112840048040d01d911000411160000380c1d598801402c10507424640c08004003801d0800c0c1c25503000710340c006814045410112809007158021680110010700a203000740b01031032061034014010840034144031043c250f4200c800e18007500f0351032443c0e005583d1020045142411114441c400c000441026100440c8500c524010800000c0c4c1101002070300e6640001603580c1d901c000d81180d0084490940d0350f2071500180c41e0441900c1000741c030000044040000380f0403549070340c2c1d00c410700c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 67071477 1250 67070227 67070251
    0x415020a050c240103260a020703061409031e040302060418050f060f040209040209090106090302030d050703021b030f070e1801020313020f0a17070504052514070204060905 76
    0x1603c04611010b488030b140c0c2c0580030450754001040810304545180c0c592034010f18030040c07180b03c8541d0b1400c440e442000c0c0c2c000160301000080081c410039200f80c0c400d1108143d00202141880e0081d036a03a401030a031a64212080c004070744110940360000ca80007540d01800300d503103460b910101c001c20680ca00c80300754100f5040c200029981e1060f8044030344190801400d666801e440d010910000790000f000064016500300803030005650384800d618020702c01592180c7d8014150305c14541006401d090704006c2c044d0500c01c10000035000700d6204002a5203000c0c0c10014080440000d141078044060b0990a006a070703000308070003141c04505803242940d14418400b08900850b01c5080b032000b00d80c280e40e490820b0904200514200b400264280401046244641e032108400b180102c0a08410031a80c0c1c480318013048142014000d1960241e011034011154105a0b46042d2a0a40c200148000c204451070030000062040c0141e03681540c014204209031a12100150001c001c2035510b5a0111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 67072727 1250 67071477 67071493
    0x81f08010c09060f0212180909030409060812092209050c0f01050403030c0204110408100501090c08160f050415020a0c0803070305040306090501230711010b060a080415020a050c 78
    0x16024000900c611504c50b4010040120500048855508048000001c42d90300c44100c840694860b0200341c000d0381410080d503652442e0181310300848426502117000340d04081808048074070790900b070b03c06803042591542c05000400c284007022001210701e80c0252480c3c0360f1350780b040c80f01c0080c041c0f030361110075034240131840c040d04015500b50040303110040004045c2c2e800c0b0401402c1c5500301c90103140390545c1450400d13850b843c0c1f050030580c081841c40c2d5450340d142c0c010050183c00c0d02602d084a4050f08050206040c81c910821580315003074000c2c400d0010035280070702014403c10031600180111700140041d2030442800039161a021101580e41c4600d800d0003294642c0080100c50519074185c652515082c0b450707440760082c2c8401141920107560351400702d4450405043c0c560300c031403441c10000b0454541500c0240103a030b948071000c2c0b6168035108001d0303829240c0404451001074103080c890441e90355450000a020b030122521a56030307002142c0b004109401c50b0180450411038004c0d50444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 67073977 1250 67072727 67072739
    0x6010e370c230f090604030606080604030206070801030b060603060310020c01090309051206011703041211011803020102071206021905040e1602030a0309060e0a030909110702030d081f08010c09 85
    0x600a0981c208641c2d104000300489401c66100078614460080c02440c03c00b030b900d880342c600701c4182d5131240911303070024010030041641c1032191795803040c454180040d03694115125420070440c02001c0c1d078022032001021806543c1e00300408001882051015586c1d00c0d00d0340c0c07019000e050442d8007213010640151010440d4a40b100180a4000a15004000503032801d86041074041035044090800d000802012550000b803502c4107aa00707014008031081d07a03280d4400100702c40a80030021030001424402440107030390109201d4110b880c103540303021940c0900e00741f500080c4542d00d4420f01d408400ba101c804802d41002c054821500a1080f54465035200781000c1d0403000d40c2d000050068208202402c02c00e4042d510094240b80203500015030243d0580402c2c0c80d0100c0e000d015004105038030003c109a40490080400241245000720f060030316a9010075505d00e03104140b441800444000030700081e07041c80d01d0b480c3d5004042e540309005c0b55913082e814000c0c41c1d9040502700290b9182004120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 67075227 1250 67073977 67074017
    0xa170a1112070b04080d060602010209010f02010c120c0509091302030105060628050c060f1503010c0504050f03190326060d0b07050f040305150906010e370c 69
    0x3201e210402007a01d401500d5030350b00400500180215508403050109040310346003881181e024180603000161790301d603c2000509410768001001c021a8104400c4003146076100740401e0500a003403802082c20401c664051743c01c0d011300c059040c0c0200c0e00a0400800c082010400542d0394002da008010301d031601d0050005034411828955211106081c01d01c611007042e000c05800c0310100d1074018104041402080e043c8a015628600c82030b00e90000d001c1c03400c0c425581000b09100c110000c201d007a03803c00019245025600c18284035800c51112102203441c144000141030070304a00e030a8013900d180c900500381e0700702520702050071a40548040c4450103200b284501928009188191041c010b9480c0807031a10020400000c00006003e581300c40c00300f8030043c1c80510301c0382000c0c203040320401520380b0029200a00c030789010b500101c010095102108051501314015030000c0050940e40b841c410746014010b075940c0424504030101c41452003a0b0750210302404070740e5460b40c180890030b0001400d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 67076477 1250 67075227 67075243
    0xd0c050a0b0426010b09070201051906081015150f140301060905120109050706020a0311030906071203060b0315040b030705030606010309030215090a15090c06030903020a170a11 78
    0x1002d840c00e810000030082c041c80f50ba81e0700e10070140081000011070012a20b80001550301d200541c2d100c800303100346a200240460400031004070100100d52404404c0c81ea2241d0307400a00c41d00c2c0d0358650051044104c900101c82c05000308a5905940b0035620500504e404407290ba0301001600c25500800d0204213482200d0484030a59280c1120600b00401c001500009411280e229903032148910b00150051010500810ba241c019003000307141c030304001d40240560f02421711a90020040c2c490f9517a501410303500e05a4018000080c06982154154010401c6400c034a000000c04010000c3ca03003506000c0c01d01e04002510300b405018200b409050b501d040d20300400f50316422142c000340c000e510030703131000c0c52480c02481214071254942c4c0004d11900d0090b01c6540e980d800000c505030078018510464415030320700e201c0401ca04103050311001580c9400303000d5001007544862030801031510030000d04950075006004042c624900c12080002c41d4090074a0702c02040d8004060034840c9400b1070110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 67077727 1250 67076477 67076489
    0x6010210020a090b1b0a06021b0601080604030c020a0f080c0f040e060103030e1512040201030e0f0c040c1403180c010c02060405060304050f0f100612050307060b010e0d0c050a0b04 79
    0x20128100300440e5078580108001040700d0308500185c0340181800c00025031440d001c2c030790041e601c52000e0541032035a001c2821540b0280d001c06c00400c503541000404d50f0b40b2982518010201000728070001d4901509a40b00d20580c11701404085071042011561002c222021590b00b200c0c4020f010078401601c502c0752001d01590800c1c0c0040011a01962001d440303080d00808543c0445c020585114103600f10b040381c0b4881510000400045580502c22a880881c4240040001d4030090ba030140d60b60030205051400389456600d0311000c0b6005075118050822112031080c0c45c0c0c6000b0200b004042c1a6030800201071083c904111080d50090150301e200c141c010b0701c0c0030301c0c040c2081d06200c040c0c0e20140048850f4402d86d845c40500b800240030841c1c07520710284c05814800c6040d208282035404076045109034550810300000014000404c88001c194407540106640180c03100680700300c83c032000c2c80d603000840345595804104000d03122500b60b41b000c4030000c003101e88810000500f03000d1400381c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 67078977 1250 67077727 67077737
    0x60703140a0f06080d031a030303040206071e0f0f21020a111207030f05100209010c060b040603210207090501050303040303051804180303051608071409040c0806010210020a 76
    0x109411101c5a008403070000d11000000c070341c003540d56134200d2034801c09001c0d8400085d039070400400003070f00da440e000c4050380040f0011411814036800182191003543c030018941c1004d18801040290380544010074250030511800000c5400e040c201d81444a0580443e14141c403d12800c0c1c001d202201d1440c02403070141e004010000d4680d845850606170b64480a43c0f001b0362800c401c1003803e00b008101e015601c1521000382c6083c880ca800c52508c502440101c03006401440056080d9a115281c004103035040342002c14440c000038003240080c00b144d04050440114450b05421250564481e83c41244481e8201c461541d80e500110089a0702170091517807640041000b000132901c241e028000c0041940300341442c214216000508851320521003e14581c0b882e11017000b4960140300d02075010f107243e0074280d14040030f07500084c810b14009100e50300f400558889003035181034403000c6c0c131805040034000704040424028003600203441101c0950052083da680c000c0503074503c0c001c1d12000e644503214 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 67080227 1250 67078977 67078981
    0x304080403021003051b0d0603080d0c1106070503040f0204090b0408031503070513050705040b0d091205031504022d0301080601050604030f110402070503070b0709060903020303090d020409080a02010e06070314 92
    0x1b5811640f0000d20a50303200d480301c1011011629140041071180000700c00058807130030320040a0300380351580000606540180040008068001089942c41640040342004c0c806813032000800400821001801040c000c004200800c03014900450044100840c1c4400400800d02003540d651802e0103142d0b0000301008030200d081340e090308030b950005823031304181e424961034001c2008903801c841500006140c9401d0a01e080c000108401c444980319441d0207803440c5000641140d03100c450040c00c5003c2c6071300107181581c807181081e007942840120b800c80c2c1400c0c0c01d19101d84450b84c000380a04c01044c0a01d400004140c600b40c8100c81c21079500141c203d14840841d11440d00602d074040000742c00c82c1d020820b01001402c01d000070301c2031910841d9001005d04010030010700d42d00380380c0c00c00f2041c0318260805101580d800401e903194440112540302620380c0c54800b08001d40300803840144140c6005c0341c0c000401d80c064018030040483c000071a4602d98440101304c040d00c0c4510713a90395229002c840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 67081477 1250 67080227 67080271
    0x14040f0b090f030f1510050d1103030903011a0a06020a030c08032503020a0f1d0d0501090b090303070e040b0d030825020d120614010c17030408040302100305 69
    0x3025218010005141c44240c0e48103802190402c0380c02004284c3d82d0b04110081d0843c000004ca0302034100d15502510014141803402080705000d903020094200955a9146074880d2313000c00c1154040c40010b00203000012040c1d8404008407940d81ea9036229105c0300401003401342c130025182c050f10b50946d4490318480b0352070300e40202c240e0000d400d0020320000d400da950340600800c3e00f059100c009660300142c1c1c9009084004000044520118040100303900e0ac00368a480419001078141c00c0c103c4c1d80d40c094400030704c0c02900410600f40014191007511040101c0124040041c51068070b01d42c03944120021101c042104856525442d95841a42100494003103031140f1031403136201300360420850305407620803864210640741e80d0340540141c0c0624415001c1a038089414041d2850303207001071000e00c1c1808050115401c840601030704010464081c0c0047c40b01d07000400750b8149100d00c00c26aa0300701410490075a61160005070f014283c501030341600c1e1072081c4a014403c4070705402c5202c180bc0140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 67082727 1250 67081477 67081499
    0xb0409020d17040509071d0a0b0301090e03161209080a0b0109051e0a02130f080601030b091e0a17130b0d0f06090c0206010509040804060302030a0e0105090109020114040f 75
    0xba42801080240710215040d150254000c4c05501a51290320100c0d42c540300000d520110141140e0081d98041402c1165504003400d4906407051160040b451811450005195020741005141c8681300d0429030010f00983c84040d0000c0c084a90fa2a032a1544803481d05c2c1d030700c4000741001402c21000c000100300e44030050b4001508002c07002d03007507a110880201d0100c01030301d05440b500c2c1201e0340015180c500e000e02011312030040c0f0002000e280c51a150080040d2601d005100c0501100255800070329480030602100040d01e134101d18003c3d545084881c00c076554001450101c851803103450b4592030483c160000ea80c080c583c11340e40015003a0910641d20180d41002e0446010076845040c00004d1507130178003d2002500700042e00080c20006008001c0c0b6055060b80700d540a0300445c0d080c000441c8074003084506980031703410050b94980722050a4002000500c450115079481d08044c01515030040d00b01856950003640c940700c0054210343d69040720311035841107108580c140030081018078904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 67083977 1250 67082727 67082753
    0x810080a060c090803120906060f09040206030402040b060a0203041d0105030c190902120a050721182a09020405010228080f0c010c0e010c0f0c090f0207060b0409020d 73
    0x1480c1a0303040c1d40d03480c132000307145400803c9080c41041c01c1000708045102c0401c4a16401035086030000d80300c0740114007007808083c001d0006030141400000181c00d5403a10380256444100c041c11940c0d4070300004100a40b207403c0350103446d040241e403c0090b511000354030f5085040eaa0f0040150038900000c00c1005000e05030382400f5260007000c071600041c2460948090076801228041c80181403900504c1c01c811900000c1040d0240161405130f5031440c0c058090000c104104083e001580c401000141d017030381ca16002004141c6a8a110300c083c5c0c404075040290984c281e12a00d0403a4943c640784610168003ca0044c18010380c4a0100003403940001003481c0c100c42e0482e400c19030008210b03110240c0300e501901c1030100700c40c1d001032007031030f04402407040c8122035906141402406004900080040030100e4015003929001d00080084c4030341c211600c1c3c02461412020080258908002c5002c1d400c9803405032502440e010010a1a0806000714843e29034002d0100400207444e50b0303450452808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 67085227 1250 67083977 67084001
    0xa02010513080a030e1501080106140901031106160506041514060916050403020301020a02010e070e010b0702010e0319030f020f03030c0406050f13080109020a0b0a1d010512010e070810080a06 84
    0x5801e18074041b08980343c500f00e01030304843d0008540c2c2420071303001920482c40c20042034041d074034400040020420400c2e032400000d00841e5a581d80303018950100742140a007400140581c0a180148001c0044006105032580074450080c045142c04020304042c0d08001c1b40c00941140100002452414208000f209070204e81d081c06400c258681e000310382280c2140d0300050240c3e6450744091900a0204840320040000309000440c660400e43c044820b40501c410090501000d007860f04407964051280c4d0440b17441032105903220615a00300100240c290058400c094003c0180c2d045064001004480c81504000c0001c0d15191030b0a504640940c00703c12840031030791040c03200c2e11001040c4000d01c0028454140040f030030240500400155480300da100c1c10300b0036800c006140c80d180d0041d00708190701c0ea00070351080c40c40ca00e00e00161307058403c0c0265036072411200000810f01001070740045018088a6842e0169a0790b0716441e40c010b00b8280c0500d800551101900750000ba0b9190061455480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 67086333 1106 67085227 67085233
    0x200c060f0f07050703030207060b180a1b0e0d080702030f0303150a030506060f0103060504060305010906050a050f0c0a05040b041412010203220503040e0c0a02010513080a030e 77
    0x404e036a80142495008582c05042c404954000030050501a00384440f40c0d0180030301c903141d410110b81d6407070464642400307100000c0110030000207003d0381c0d48030441e80e400c3d25010004248029001140e062108112010060301d040c050055030807a003400031034803809c0100d84092440e4010400ca80911440130040000c5140010340c680c05c44810340f01c1e425403458200040b005003249410403600242460000001c00c141580316402d40c80c02a10f0030045510b4811804094075401e1710110001a40c0501240d2050400c0d001401b000e0300d80d0400a01e020754600c0e204095410a5000b5006845402012006820800706000b00c1005c020001c610314603090720000d00000b103001000c4135a402d031034421400c014003003044a010f0450000c100c5030b64500b41d0301d0101240d000e0344450b0015400d100100d0b84500020810240c81580403a40a0821100007401c8000305a0424100041c0c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 66906477 67086333 := by
  have h0 := BRFrame.cov_init 66906477
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66906477 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 66906477 ≤ n) (h2 : n < 67086333) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
