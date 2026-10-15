-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4216
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:34.146418+00:00
-- url     : https://prove2.me/submissions/874a7a4f-e4b9-4876-b541-2a2edef7d87a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 758093525 ≤ n < 758273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 758094775 1250 758093525 758093527
    0x5010f091a04030819080a0506030a12050d0908271315050d050a06050f011208180d0506040b0a022a0c030d020f0f03030403050a0f0203070b01030c050909010b030303150406030c0b 79
    0x80720503080b00e00706607c568254400c1005240a1001039038030141d4400251012903c001951005803048084966a1403091010f2007030401e50318040119600450450380801c00c03036080c08101d186640b4000c0e00d0010010400846881603c4440009010344264100d1105505c030000a03207855604420603018007400141084040c5401c0110a07200300402034003d45510900500080c000c0c4560b0985050300401d505854402403070881c003120346841c0074607134044d0501c03404d0350400c400024164490780c45624020450785074880302d842a0301906118510310400c10180240901c040e8000b02d505042940c1103440007841d0307001281c14841d081ca0721000581100d40d844000090821500e805001404015443c40c0761071b40b0010060300840815000308a85e4003090100b4920800690390340ca03420003980c42181d42c1d80e1500074070103110752145a018140302000140440018410503c1740080600030314610b50320421f90040045010700030640c840d641d414080041422101010090300c06200a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 758096025 1250 758094775 758094817
    0x503060c1c0f092009070c0c03140730141f05011a090a1203090b0301081e010b0a0302040c05070501020c010f0506030f0a0b040212100b040605010f091a040308 70
    0x80c100c4c01d400d4100300383c09611516041040da100c43c04c01c19404036031890000d5041c0540d140464800341c4990010704100b03103002c0030104000303002c101c0c14111a80002da00030078460308038409004601c41583e0f204c03143c6400748460007090f140802400c0c450304c000c0a5071180c013902d020013560b85041c5201000c1c80d0b551140144691780042d40480c0001200800560408022400140ea0450140140e0714500219051a02010b020b640610040c203004105203482e580c54440042d0780c2e2a2030041c1c240780301002d125000f20800180b290721031100c806007030a00110b0842d000d1101400b0790100800030814104101008500284003410f440d81c5c0300c2d40003045407181282144180c4401030f080e039100340c00c0340c004110407060002e003083d1010740c00307208501c1135a43c900000c1c03044801c4c1d6000c401d041c051500d00b80601c00d880d50050346920b01c115000c004040e26a001124010200c1100e1000300e04084c0d410301c0112280d0030f025440c1c0840d0b003007440c60103849540b800101d0f0044c40c2e24600d02908010f82e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 758097275 1250 758096025 758096033
    0x30f1a0a090b1509060418140c09010b0403050a03140d141e0c0712031e150e010b1c02070203010c0810090b010e0907200a0203160503060c1c0f09 64
    0x152070300015403141c4050700c0c058001c000303240100301405007846647d440c0c030f048010501030b001007111076401c50101c105c48030000100743d441c1d0006288051040c03141c100040f808206039000d80e002da82c1c002c0018440d00d0401c0d542690440c0b502e03c1d05030f10710300041c0070710400d2080602900c3c41020420b401c90300d550800b0b5000c004144d1030301c40c68444408138041000700c298520415241c0c07441c1c02000030a50030301040c8041d0700601c2d031140158003200343c986c0d00c80140c03a0307240c002d80c603526104502150b44075500c03080108640c0d4203000b83c8100d440e0811060518401c00c0e00750000b00d2080400c01440d184c280d5000034211900314505101144460041000c05851102c1d9000202400ba005124003402540002c013100303281043c462040c0c440f240410301c11740c850540d22403041c800030400c401c001460317801f40b9a180c0800c64220711901c40c44105018040c00c051203082103c130090001c00301c9485a00c900703903180c0c0110200071010384183c800341d0a00c40d1540240327240c4004807500090300385081c0c14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 758098525 1250 758097275 758097293
    0x10204080c1507170f1305031b0a060e0a08030304061407110c1005090d060f0e033a050705030105010905030613080f1308030d061a04030f1a0a09 64
    0x114901c2914190854070890303800c0e100301d82c0016440001201c3c00814045a004103000e00e1a00c260344a40c08070700c410300707090301c06c90030310607503000714200c1d0000f44801d60303902c1d036204a00c00b0480e040011140d082050301c2c06094883c1e01040010040f1954075160280c2d07034607582040300c040d1189074035076200101d00c920120780d0b075812000d20724100c0403150000d800503591349800c85006006101d890301c003100c041d101ea0195034828000070f1000181402d1400e190000d01440b10183e03c03c1890b06008401e810000011903120391050448071010210b551445545c002c4440007412081c0c00c403186c1c0110710040c5106291240342c4e44e86810b03481c3c0d41031000040149842d9001103000e503002c034040c0804140003945042d0f1180d03100c10704039501c00307012a1900d2140100c0d82030f8072019440542c040b07441140070018082141d125202009000e98a43d101c000402d40544c0c1160010000c10080c808100070320607120280d1b0107500c40355546040da8610341e481080841c0e0300d03071280d0b40d1081d406081250b044 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 758099775 1250 758098525 758098543
    0x80c1e04140a0209150c032502190305010b06070515091603050f070501030e0303130201050904141e01030c090f14160f05190c140a0f0501050a050f060f0a050a060201020408 76
    0x1c0038641401b0b644100c0540c2c1703200340c40720b001c084608440380c000000c03100a000c4403076607809413102c0f60305056901d03c020303528024041100c140d4244000c0c1c0b5076a00f041070030b903000c26030424028120b0380400d41ea90718074500003034035105485c01003068080c003444603400c0d03613401544580c000340780d1440c54a22050518846400c13090405040c0b801e10003a24100101342e0303401554540100242001e2440180c8080c0f0403020a250440d007030184110110480d00341d01c3e0311410006803921000308408810258198003400000e289941101041c402c45490b0340c42528042c511100000d803010000c40b1203a00d01204641d4240230410031002c0d0075805601050121407800070f41440c60400072607581030618000180d03800d10800c0a040005014805e54106044400000000307494500d107040c10b08001807000c003002511250708200c04034108450901c212807050744c043d65030742e00c1a02e4500420a081000e403036001c2c0e00c19003000c0f02007281e9686035044401040c1507000165158901108982442441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 758101025 1250 758099775 758099809
    0x1809032119090f0b2502071403070b160609080f0d0f0c091e0906090b030706020a0210110a301b022803050d0306080c1e04140a0209 58
    0x10b2603400c005038000c0b42a140041c0e110107266901d5848946680b01c1d4004410b1148080800004074181d141d00892214165000715480c094040442d005055880605200d1840c0d51581004140c420401000d11006001c0c41070381b011070040456190100c4680103546a040210743c0090540e1454000f449030520030400782c0d0003400412141440a852050039224120306283d2540c0384038000c0984071407410240406900070032510381c45001210007400a40c131090b0082c450070001089103400061550b680581c000d11501c2c11810454003200c445001030a081d02a01c00c920142d0b000030201c2d6052103c3e039041d00c100e0310002c158051644070703404c070510550302446846807942c080180c40c90701c20ba0722160107440910f503074100160505954203140301203405d080c9400201004206c004510600c44042a58003404086d807240c480d20344a4201d81ca60a0b401804001e0742185003001c3c0d061145880030040c00054174940a100e002da661400311260147c240d80000c0d420107a01c1c181045a48407045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 758102275 1250 758101025 758101031
    0x70302100f05040b0a020d0f0f0e06010617011e120308071209080403060504210801063b030c03030409140c16140c0a08100e03091809032119 62
    0x46034440d000022009000751704010b0300010310b85081a141c0c1c20548004800a004024161800500781d0007030403010800c0340280540400025014403c101c240150280d10742200d1181e407811680d0a10904070b210358130032200071410f0003d2020002d103c0d4400590280d11501540d1808001c01004098400d008900303039454903920801182d450740c20303902565070004e0001940d40b1181001c01042c0000c20b00110310743c02c0c241142c4071242d88090214102da1440d100c650b000c42d004074505200ba13600d81c1c0300f0310080c50005880c58042900c0381050803000400381c00d0711692520680400c0c20340c0d0140c0c000f5600c09441d40300d00e10004c0f1500301826407100803280c4140c01c0c401144003004a50f0a90540940743d0700c086864004104010700124490001c01040d00169507aa031a0319521400b40140a240075460104004140140131085a03117048008201180019079940b40c0306000d14064403400e82c0d44404d05c030b91890307411a680030381104031449101790154500f200b0b030035504bc0d802c5030008620500b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 758103525 1250 758102275 758102281
    0x1908190306080c010e0d0501021c0e0106060c02060d1d032101030302070b0304060f050106080402040c0908190c0b18150a0507062a03230405060406051308070302100f05 74
    0xb00880d4140e141002413a142c05a05040e000007006502c5008000d0055440000c5006c580896950300b4400310401d500e0504c6403100c0b9810440c200c2e07002d0f1280c03201146010001c48018a0144000d11101d403540700b0014001c15500c12405070008036000c41c4889600014114009142e001d00080c1c043d40d00e11500701c4c00e58190b640094a441d2203118601000f00044003003010484075410044601c600007a04010540c0c0d0303140c000b0a900d8043d2410fa005615154030814200d11840010080e00c41540041400481134a24421580f5060506030350a105c0c841005c00d41e10300403801402c05028151807040a0484030081110583e401100954640401c0000151158002040d2900c041d04014001517520880311101a51412202010902003800501800694040e0300c041084520080e8501046d800d072002141c3c10041580d018003140d0100000030000340ca242c0019504c410101c0c1846004c041e90b9503846030715005040c0c2100941c003c0c1c00d04007041022480359804082105009000c141 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 758104775 1250 758103525 758103539
    0xf06050901050106410d0c0801050f091b0903070906080705031203090c04020f1c1a0102010e060a02031b040b0703020c0d0213090539060322051908190306 68
    0x40c4801d0000449200c140100b1602990900c040e181d0040d030045c820311101500580080880009008403445840c1000325032f801c1c0e080440e0074a05c142c10400c002407003080d8a5400b010300d504801030030365240c401c020021980c0c504a006030001407000e1001021841d0400d000c050820170305030054005004140101b040d000710000303144640320015500140d03030390400c5c60107040301e210340301000c0381c00050123030029400e54080e0f0288140300380d401070764104150783c003004a00f6100d0715007560815601c03181c0803e001a120f40c0c011900181e04141485404020042c84c6040da08070b07a100501074603010401794189501404a0191000c04030f4560380c800c6401c1d4009483d01002240f0400015502c0800c0f6003040310402004c8095088041851031481100e0700b25526441e0526035200c1c1b0b407a046540340300d54100b00301643e00a80e0b60030800030b1740c08070704110029242c0c05a0001d0341d15210340050880410100720118001c1401545200d5441c80d10b05114250880c110061104252071328104000d18 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 758106025 1250 758104775 758104847
    0x209040f1a030d021504020d0b240316090b0f100f0e0a0e27160609050f0108040210020a020d03080403030b010e0a06030c030b03100203060910031e0f06050901050106 73
    0x4000c540e05d1000c0903180c5001240e15082070213401012070755407600b1700c07904211482e402401c010000b034146070564908400e0548482c0000c002c01c9028030014011b0110501a801103000e001c0080e10204002c4c6400c4006017102c650045140081202c01c5d44054502d46d00990b003000800003175606107000e07858410300240030b19005080c0c1e940190641100150b94014002e0805a01c10550446230100b0b40801408600c100038031034100440e2140600203803078100214090710740c6205850307050846d910385c0c00b03025940b03180446900444c06518580d00c016030b1451500100719010b56280b8115107880c0c45d01074101c1d0f010384035682c10310140c01412055592229035582c02c0d48c420386400316224101003400c1e800703130a5000600790b0601546100750681c964940c051880780303008032030310803058440d86800313040100c07140030280ca0850026044200701c0b04007807081c244c4603c12680003682c4445500d0340c1d811542c013550f8000740342c0d4440b00104441a8003618409000410701d466818900e9080e02c0c410745 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 758107275 1250 758106025 758106043
    0x20a050313020609031b21120a0212030f180118080a0c02030307060c0311130b1305060c0d0f020f0c09040c0b0d2a0219060209040f1a030d02 62
    0x1407000c1a01466003151a01d8007a00c02c811006002c48410100140c20140d840101108080c0114000324a00107244030b082240c4500107440809400c1c2505800303149800c90f403210b02148113500c5409400040110000c00440c82111000504911820014400000f04110841543e16681041003031491907003030030b510481942c0c0c0700c5509a83d4095080d0b003500c20500c81540a5418080842c0f00010700101e50401c05601501e65402c00074840320369103c55140c00b0349214504650180d6406001c202092002000303005159000481c01a40d241c0005038650b000c61200000c9400c03c50500d04c03141e07007050382d10040a201d400070301000c1c070309014541d0761010304d18020340c0300708220404102402004840100500344840c00180d0340c0542c58912405402400a450165148110203146004407160210715160195000d0940036400100300c82c0c03000c050070310581e411036082000c1030880d03840f44205441805070b800086002007815104c0000924240310060280d00030003685031107035901060002c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 758108525 1250 758107275 758107291
    0x3011b050904360611072004061206050702120414030c0a0614091f0c03170417221e0f050307051c05150411010c05070510020a1b0e0a020a0503 63
    0x480103e1418440701502c110304894040480004a0310107000003000c20340e28000d000040c2a0040c0c5821081c4070403100f030391254201c008010300d90390b4000340154211390341100003403049866500c91311103600e03140c2d48213a1080400038075040703003042c05040c00e010000115004031140302c0f01d2890040041c2850808224441110030005004911039540c03d0441043c1d0780c0012a13030188107400203010700b00c030500c103500b5030104108c0c8844e06480b0710b202c1d642c9442aa402612085c0d40c00003454402c040303030000800001010381a9001c040d40d0008010602d0051161410040400407510b00f2520824031070f81000076945550b42040c0015140001c090b1304a03402542da0420481000390008180640003100514500401c0010319001600341201d6000c5e6019440308080d85001c14011b58040d141110003c00c00d4000030410050344c6070010302c20010180e031740141c440040483d580c00d02e01d46000d58003040d180b803030300b107040c010040d0120f0400e50150640d20210310701045100d010b0014000100030074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 758109775 1250 758108525 758108621
    0x612070509070c1401060b071704180b040e25050402030103080a0804051603050c100e030d1d0a030c0603290904030504050301020316020610030f1103011b050904 71
    0x40208a09150130321800804c0c403000304002d644440c5d1315615540403403020343d203a0303966020715a020320011040714100e030150b0403000c401d420480300035000b80c010030140c15030050303603403030f9846003040c040c00440032440100c1400403001640700c0c65100d403000315405c00c601991040c001880007480a8044603420100e40c20420032a075500d1900030301d06440c0200728403c8007110310000003000000140c0088190f02181c40d05c2808603180c80c00c0300d0615014040c1680360b44004200840540601031907000824074280d000c0c606c8271000c020404801d9117134421100454100360400c01942d15105041c2094031a18503000d0002c04039400e04d20503107030030b03506c14400d084c4100840e003014007841c103c03002004090025500e918210404480140b025400b5401501030580000d0384100520081b1041da0340c0300c40c4044010a00d40c07140b5054980282469170503640e20840e119030100500c116180d030f203640759240c0c1e41c1e40d6503103070600c401d58010340e117100c0070090042408500d868010030b44900e50040b05580d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 758111025 1250 758109775 758109797
    0x10905060601081e1915062d080a050403020c0d03021614010507030e0307120506100e1014190e010315020a050904021321060612050d050a03060504050f061207050907 73
    0x541c01003090000c0c2064046c0880c00c005000e981016401d0684191f55010032500b5007c1902e0f88100c1c14402d0585001807141400a041c0c07040a51107030f13401030b009104549541c181c55002c034114002d01c0c00c095000d0f038000e102c0f454412100c170803000c01420441d104203a0003116680084d05600070402c000302071019020141d0b4460324200458001086040c6050520001a0411030348503082600c1c4240768403504a40840d90881048119020724440c0c5618a0b01500d084041414404074480b420f45c4070135500254050601a0710010300a05800c43c195001545035180c20074403210707c100c2c100e130001c0c014080c040ca41a0808243c401c0c801d4140c40250f03880030601d8442c032416071542c0042000c100c40180d1340700d81e802004a00040648074841c1041801d4460704405141001448010840e9000e28522041c0600c5040030344840300540c203010500da51240c00040944400b1039110b02d9a40d40881000418506000c46d83c031101c0030100501030650a15000c41c20500740104840240300b410068 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 758112275 1250 758111025 758111071
    0x121f060915032f030604122712050c04060f0806010e0402060706091e030509030c06160615170307021806090411190b040f0803120a110705010905060601081e 69
    0x42480d1041000303040c1c5941b40740520344060000c3e4011a860001100504804107400c40c5004400c50079110604151040e0324000350103485078a0040219041e000310800318820ba00c0b540100c1000e800039003002400c4034103051342c3e0361038144140e110f00c00c1008002d06100150315144101e03001150011008203014050742405010f00445022254440280041850a05611401400c02c0c030b030044050f9040c1040c404200142402036440300443d201c451044440016a9507005180b032038003101642c4039440d6110000313100d24080ca14501d0244c0c000140306001c515004180701c0c807105084c540c070301389402d00c6808140d03802c0c4c004000a141c0c5a0881c00304201e5940e5140b980c814101d9074014014007030312606958040d8000c0e205900c885010b0355030200c3ca0302008001d940b05060001f1034a0740c60b6880c402d419001d081040301d00c2009810800980e408104207008180d0511b004900074142410300c0d01c001051108018840400b07072030b5949080c080003c10815813a044401c401080c0804525000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 758113525 1250 758112275 758112353
    0x260c0313020306091e0307020102072d240504081c02120706140c25080403080f0a2a0305090415080601081c0e121f06091503 55
    0x20080e515214980820001300ca00080c10007001154040c52180c525194103042e68a01442200030301607001800b081c000e002e4030781d80c0b4504c03d08a151035906075200d8078040d0b03000c104060300449404624104180300c8482441440030b858000b0749003031490301c0c0c0340c00340941d15140c880c030310701d120341c16040000b206140c800c00c0039000d00c6802221859980e4080d00c1c04200a180100c540310364403c40b48006141ca6460100b40c41d013900d8a042911400d2a14289421103548054421902c1030001e00c40400400e0300d60010744002641c603807182e42e949810180240041009403618420740070301c0400003c4d016116017801400d242d150501503103680c0e8800000e03018010025107101d0890100100185442002031441d040b00c0040c011340704003520a114400c0501c0941c0e2911000c50380e0416417041d2810303e84401a51400381600361250b403000036801c03040e48800c51010840c420b4541109011b904440d2069a42c0c1d58034514070344504034035507500d4a004a0000100c0c00200704101032141c082d8800c90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 758114775 1250 758113525 758113561
    0x1141809120417060906070507141507030e1e07090209060d090c1701050103030c0b07031401081c0e090a05180a0b0403030b01030c0801090e01181101260c03 69
    0x1202490702e070794a405921051005100e5412042c2c8a000045070081e400460168050480d603522146003520941b584028004501c800c00304610600356881045180009420f0080c14265400718510b2619001c040c1303000642d000000322242d0912005031449030000c3c0820032200344590240e214521840007039650700401c13801d03201050401c0200400c00034141903040648003c1d4031444840a80c808449007229800d000040c00b0900341a0608007088100405035813107001450080380442002400300b9010f2000c5c0d1216000380e00c64661600300792035464098800070707010324101411000260000b42c01c403030041c015011540d0703100003041c3e031002080710500c80d004401c0b007101c802e014940362081c1090000c82d000c0e1b000900d80201210b40390302c01d02072030055010740d5850007060b03401d1121600080c907164a10300000d668510504415003503485001801d540642111b54861400300d001400803080c0e15400c101e2540e003915015410b00f2040b01c0c407500710040c1c51102d500e9544052030441903907620 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 758116025 1250 758114775 758114803
    0x100b0a030c0b0d18050a170c01020705070f1e0e0603010902100e01090b0a0c23010608070306050c0309060c09240319020a02100906060e04030c0302010501141809 71
    0x105001203907100400008010311001e0300c030100080a20890120103a0b02d4281c8010710716004408040c0100c2d1f00411030494110305030500515100101d1805801ca80c000c200032100b41d000660104548c030305503040b51004090550988490000600c06100050041c0c0560700f10815041d001c118591000d6000000460740508010420220100054484542d00285c0c6002842c900c4d4082003500120f410354500740f050b41c41e41d50000f403075551008407081600218903030410f240100c20044180074046c1f1b0005007840740203801c03440d04500f080003c0d100000c260645030302d020000d11017082c60018140da40b10009012082d150380600b00045ca0350a01c8208082c0d804144110440c0030048040080d401004100d524020380d0150030b80c1c6505a0050041c098056006a43c00d00c0a000d506e4200710001c0348106e80010307900f074640114024a01013074900f9000a8510440c0f081003540920075a40540a0454000141154200005c081d503580112405030b000c1d0001c04108511400c10100410f041d078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 758117275 1250 758116025 758116043
    0x512090f06010807140102070b070b07180f0e0a060305060115090308030a0203070f0e01050306120a0803090109050f06010b07030c0501020d0504080d060f05130c090b0a2f100b0a03 79
    0x14a076034159807090640038a103500381c102c1703129070111760001649208860039801100d04184503a1600c00302820014007900511001818403c0303c50000b004640c05081c489110b000607a09181d20010740c041c00801450085140141c01d2000c640002816811624200709245034140014411100c00d2201d40c03008082c014007205000001c4c01540246116860b0360ba90000c00078050341085036034401c1000034a0100780d0800204001d030074081800d082018900c0c2c211008025560795007645680103c40340c0c60583d41d22019601000414082038850a01ca070005100c203504201c100600b0f0710891704000c00388221154003204128082d010786500c07500200c42048185068101100d5071b512003440809294605200818940960f004842c19070740003910901800147c40361960040108050200900071444400503035140301c98000c007048955580c0c0c1400b82803c0c408420b0420881c00e01303000030846c03181180ba0140e0000070b200c10313451020b00d41c04201c2d82821000b01d03010021030b80001e0280d0207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 758118525 1250 758117275 758117279
    0x315040b040b09011a0424030f29130f0b090a050105010630020903071d100302010c110a0512030c1009020a030b150a12051c0512090f0601 61
    0x303103121405116900481c031558595940d681011300f20303518144000d400160304d48583d001400c06601400071890928400129800c0400c81401c9400742a8411214040410017100400030800340f440f11034110200c1c15044c0b02d04d110418030440700c000703058200e19050407140605025074810007220716500125001c0c1c071400c00e2000c541d2a810180c030250b405609000000450138403c00301c1400252030460a02c00181c100340c12828a441c4081e09042141c3c1c0901600713425660610500c002043c040d032416000308503051002c06d110b103005061141c111081d000c1000540d07002086200d1243e03100401c4d050310000c820002d103201d0005c1c0c009582040c203410300f41032a00f800200402011904004542d80021081050400c0e02e50000c0001d41220200600b0000203450201e40b5402c0201e021341d07140391058103400b0508032a45584002c8803030884102030320034032800744121043c41d4840042260500203070400640144190301f82c00c0c1c0c01c00e040c080000c61090051010341d00d100346c000d06841c40d0796 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 758119775 1250 758118525 758118533
    0x1404050604030f110c010e0d080a0f02120702010c020f0307081e0601080d020c10030f0c0e01030e0106140d11030319020d1b110d020a06050a030b090f010b0702031504 73
    0x10800720307000c50104021940040d4400c0c0901d140b04920054a001071072041c92210046443d40d42074003070960481c044004250006501e175001d0400742c0055600d50701d000c00300a038020704d410308030000c3e042c0c080400c10410300982d0380b0000e00032a494068800000080d10304002c02e14200c0158000d10f018040c50303000d400c00304007083c071000d400040f0f00e003110416602c500e50641c13183e07408450040503034042c0d090101141040000e0550126243c00d00060f400c0002072a50156125100d20b14000340740352124018644c0c062242e150003480c210001c1203404d0910036411510b00103a80840d01c00c010400070700701082030007040140522000740c181d0781c5440c0104070003031a880080811300050b00525600a44191007190020303101c6403c01c08224101c0203a4842c0362503961810b1880c2d400003680e00e08900542c44050201c0f0040c42c1d140e46569458400281c0181115003024480b03101d00c48007810721483c4802c3c850040d06403404158815070300c0619200191030984d294408a07400c41c0360804220030300c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 758121025 1250 758119775 758119783
    0x122104030f03060506040f062d050901030f1404080c01180c090b060304030503040305070c03080c1608010204050d140a0221060f0402060313230106080c010e10030c03140405 76
    0x8410603031000d01c9004c1e100c2003000003034000d84c010105048490b101c10009207118805a2907076800041c20303039019112000425070110000100c42c004600c0000e410b100559052041a0188807580010000b0a2600329148000b80010b40080c1c80b621004c104610b0240081d44032811590074151426507803070032071400300d40001c054802d1580840c0341601d1904a0305044040b01d10555255503191303d11342d5180e900b500c6d140c11003031041d0f610440c0ca58021000408034001002d441d2180d0005103041070740d85003645c8081040d9007089520f40d00600042000b0b0b00c03070301301c00207001d85c0c464004814202e2a00d48c1515080c6141000707503005814400041203002010a103580a01c0400142d0322156514036071f000d18604250ad0080d0001405c2001030038441c100951030300d1640c81514001d0402e2180c0c48061003c40c441c51050301283d41d80d0b001000400c1c0304004008040d1420f0804078680b500c1240002c0800000618078818180c41d5100c88000310b100b6441400c203030f00004d1b6016080e08150404e00d5403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 758122275 1250 758121025 758121047
    0x3210c020708010c080f0708040606260106060f02150946080418060902270f01170a0b1e040f06081c030b0d11130e12210403 55
    0x30b00d51a003405255040d1041c0744440c410801c402c10349985840740d0400326601c03000108152201c40d0780b13001c00f0802d40040407500ca0b2016402c21001440502c00198070708443c440d501c44c03018865103100c2c0b100c82d942c010a90110180f08146810310075a507900005090034004040f403004000c160352018966100c141d1a882014008550301c16101f0b250301e800c001300c811304840075010701c40500040112a007108094025041620000b0540300d6031107200f802aa04604c000d8120b1400368800e8003913029486481504058046070303c0380e04000000000b0741035188802c0306050715104c200014440c0d90300c030b810802c01c00314003515442c0c94040c028150700c07a040b101c1d500760780b1560501c00403114a501c1b5004000580b240c0c003014102c0c413000085082d5481300c0c1d030401c000a01d1f40311840c402d03c44d580c2e40302c00080e1038003410b440b001c444448410084400179048200d6405407411140308404c0f0400a045c114548070030032416038034010010030308440717210119a001c41600c00c01c1000304043c0d100c03d01c940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 758123525 1250 758122275 758122289
    0x9060903020a0b1b03040821070818120711120706090905061e040e0106091d06130c090903050d091511040b0d0906021c020c061303080403210c0207 65
    0x2c5a00c405840320101c0e001c1302c0080910240c00c1c80442c002c141450010140040d00f45d1401354490170f0340d0003811001108a88020216001004024480c1c0c0000d00701d0200e902680b000c1d041140b0035a0014045008240c406801051141f4524180361107542c0c96146071611a000c4071152070350383c08024016031b0785020310f690140c1402c002c2401d44c10548140c405440050080001c2d01134010140070050044072400c009564a40000060b440841d200e81c4c100c40c000d0682d044e99000b0b00210007803034400061300310100801d036a00c20a000c21441c100040c10380302e0603400811035402900302210380e0700401c00b44406491508040c2410440e0a801c840001d861000051040c4a2102e0102c00d060269108003641c2c040100458401ca8800e98450b010032407080c0307001410701d07803668a00b503425a04501d205010075400907264110000402406502041031064010f40022550340204042400f401c01814000c6403c0d05401a841c60308400d82c0c14a2081e104000140030508025a41e840b81d208d614 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 758124775 1250 758123525 758123543
    0x7030b0a05060f0901120f060618090c0b0310170111030f040b09030306150c07090e0a110f06040b09010c120c110303030403080f180102031003060f050105030606010e030109060903020a 81
    0xb101c00e082c6113075828100d503207a100401d24641039460b4402a0b4040c1d00d4110703002541d80c0008100610348420102030025000c00005900000d0b21305070244402035000100c410501b4810808140503038508841607695016600c0c018202050821f4090041402d42000c90040842046001c0c40784081c00c620660080c050000c590b00c0f0802210781b00e00c400e03036005400040380d4840303a880316070000c01400c403048140111440715540b4075981d01280c0100c0780104094201c40d411105002c003040d20900540c5040701c1142c1e03c0100b0000162003840b862060780e20880740441c2103c0681e004000e150301e02900030b20b845078203100c0e61000904a021136641110711800c883c400c07990f00d040c0082aa441586e05445d500019201c800c1180c04046008207115140070500d401c00112000a0000d0360017001180300a5129038214902942550300c10201103202a28000041040f0703070300020848d0300a5020b0910101101000d40800e000d019419030180030181814100d50030590300050295200380545281 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 758126025 1250 758124775 758124799
    0x1905010b04090506061905130905060c04140f040b0406030602090109120203251e14030a051b06072f06031b0a0c2003100917070507030b0a0506 63
    0x1108031070312110b0151284d80f041c0700092044c00c1203070310348412210200001d00b18030b60310000100f034480380b0440031601c2d5403142114001c0020411201c0d401542c0e03001c2d19800c042c248032001c0145007040d0b4001d407107210314030380152039501e860348140b21044003e0b0040c0166510f0f8144140130b58400b00310380740050644800000c010a1400d000c0b103600368001d01a00028030800102c500c1341d1898001c02c0b880040c06400058003045002060703c10140d03000c1010591841d201c3c4085420707560b41140340c002e4000048403000035070003181d0001c44038030854111002103010400f05000313000e00140100300c00d01c4444443c036680001404c02803400b80250701001450f03c00c8080c040e4030701007a512900d90681d07803020751150902541c00b0700342000480c40d21131800035460b113504201c550a00c00c0710014441d0f11512140340d05091140366950504c10070240014491703940d40f04440d4101000d000e4803450049a0b000400c90240b003100c0c019500600d280d1240c0c1049030014000300810340e2042c2c4929414168 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 758127275 1250 758126025 758126029
    0xa1203023013020604030f020a050310141e070f0306050d03080a0b04020903060c03090a02040c0806131104051302090603040b0a140708070f2304050114040e1909051905010b 76
    0x200402d140c0c0941554109881c5603981900b0800318407017241e00c40e43d00080400e01c1d442c200031581020620000203d4525140070303200d40e02e008041c1542040c2c0c08600200d808801881524030340000c100d141c01981050441c108400826140c0c2020750301c1102403600609045e4050138007800707540340d4001040101d036003a04010403403042c4d100e1550540c01c04400501d0344001d500266a0000c400c84c2540d10043c1ea5074001011104d1900420000c20b1490082c040241030000e0004405a0001010400c140416002480b980182c7c400c0d2441381070010302c205c50301006074058032014500542070644a04280c5818220054204c5040300d10514064020480d440c004c0c0c1c140d40aa24642c40e0081c1c140c5601401300c0342000c01d481d5550901c8031034014580340c0007400c42e50409401cbe1004c04070b40c5990034580010700c903180c41d048950707004005000c144510761380c80e103000340c1114449120440c0d1030340001899000c8c1006910240c110f000781420440c519084845c1400c02a1144c00204525946042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 758128525 1250 758127275 758127301
    0x31f170f063402010f090807060b1e101404170d0203040501080703050a090b04080d0e061509130606080601061403070207170109050609030a0f0804050a12030230 71
    0x25004030620444001c60600941509504103603082c51001140040070442c60324150750304c1c04421100e4030f100061070810b01c11148240600d03664110784450501c14070b07003051511503410701141032184130301414100e03259000b2400011320184a407111034540340e6455584090506105140110307020300c802c5c01a089102004031416107205840f0b5080c0c984440000b140144001031803c144203540d8401203011501b03185500c0c0c8034034455035480b036407034030070320a20000d4070302088060b812a8081c00512250303401004003090f10810554441e1500da0340c0414840780d2030701514014001070f1070f02c0c0d00801c90100100300d09050386c0b801e45038a02c200e4940e000a4446201c115a40401600200c0b800e02c44072580480103441190b81d80c002003140c3c292a01ca0301d040036016103254103150310005039901d1041c8c00030441095040d040c104540d03a450103855250700c0361b1010000a0282c4100014101901d000354140c2d590410005006400c1c0f440c000c040c141810100003811168200c0f920010380307203030900c82d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 758129775 1250 758128525 758128561
    0x9050c01080f0f0103080a03060909050109050d090b0d0b061605071e032609060d02040f09060305100e0106030f03020c0102061035060c1309060b031f170f06 69
    0x4510950113038a503840d685e44039040161000100360303c852000803051054007a4200351800b9600001c0c001c0c00520b8001d24002c1c0503c9030f0014031075070540420946002000369410280106c0001c280032594800195842c407507098890040480d42d0038040a00100180e250103440c003981200754110900d0745107841c40f900510000740a5a0300c0110804140100032800e00044100c1503014181607894000843c0307600007000c1c4604a43e8041402c014256031088500c005000540003001643d042d0384541c1e440c0c80c00170206081f440d407108081e00d481142584150015908280e888540701040c1c84c00945030704003503943c140140b05130b4000c2440542040803403400c40d41c2403044c2520f07226081a46010391803100c190b04840c280500c01d0f460b540001882424840c0c0c0d035080c1070603075414080310407848076805908000d110f28901401070040c414010102c03a002226a0310803140c02c1070103070103110384030703d1030700452000300a11843c6414440d0009a6181040111041d5070180c1d07507401d10382510346206 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 758131025 1250 758129775 758129791
    0x12060b190e0a27030f1e0f090f030c03030813020a0b0901030b0f09010612020c03031317030613050c090310050a0e12070201050f12100e131505091009050c01080f 71
    0x40306189001a0141705840440515402c0000a0030008407460001d40755103403035200400e2402141420565100700c84c4406403000c1c0204100b044c1c00c43d102c45080e8a054003005052141440c04220103107011031040ca1000c2c3e00510b1000030a899000c81c44c041c6d001954a80c2c0070905240c0b203484103180c810401d14041d18081c1160000784c0c0f81c110200e8000d807202000394002982005064118002400254410508821f00a01c00c0c01c0900d0041c2c12124485070314442c0c80010b109020441d91900c4050440c078404120206080c0c541d94031600d007510600380015411b11a03140c02c256424480d401c1180b241c01c0010042020a403455041c6480b209103120482d4040c00800c039000056010f040071308440c00c230034402c2038101110100a600c0c00102a181900014a004c0081100032120500c16074022888400310220031410b503541c9600c1d01c002a60500c459440e0000105070b100c007005018101d0784045005d0044c004035040658882c0c0b2100489130014103804000b48042c41c6400d02c1c1d80c001c00365 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 758132275 1250 758131025 758131091
    0x311010c050a060c0507051b01080f040804060507030909240b0702030c1c02090408130f050f0409150c0801090f050403140d090c08240112060b190e0a 66
    0xb5643e649002407819421140074000140700b00c8011031001c00060004c9041141650f600b402c500c00050103c00e4000c2c022103941112100700300000341000155011104180cc03d5615050f030b41c03a00f580c07803000702c0e04609525490603090507178140540740001c20400030113035481102500c2e410107010902c64441d019416502041c10a5401e0510071044000300804152080c04598258009243d010302514180c41d00c0c034010803548030030000b5440307a0b002040d5201c21200e202d882c01c000b00f400002c04c100d2052040e561501d5038401e00c607031501d01c01c0d0340e081c0080081000d01c00c040d0f00034083c0c0350203028007015546400705c0c000160007188903007406150107890300100c821000d0101e00c107681c00040381001054440850303400054060454030b014056010150805541c1c045000d01c0c02c2d0310342080220400113250040140f5080300c0c04405c402c0c2d420207804640c1e13084520100d144d0480c040d070512002d1005180000740c19075010041c0d800740803144818852000150a08002c0d07082e100036402d24021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 758133525 1250 758132275 758132293
    0x1060504230f0306091506030a0309052e26070504030f1e03050306010809061005120312090c010216050f0f041407020601060e1815030703060905070311010c05 70
    0x400c400c41001c005030010580b08144000b000401e061080503030701c08910b94003010781c82c0401c4500d0b250079680000c05400800c180038503902d009100100707134824207014480e40a0310b101c0562803011b4034402210010600f03c080850050000e0030042c41d80021000c44840c03040d1412450070600c61a80076948541c0c03140e041505640700c08107101a0702c60115004561030810b48040c0003046809030903503000e91103407500c03880c1440014040c40340060070400280c121100300007001c8010402c0e10f0a840382510070f1a40342c0e074000d00f020714505c070f6084640303003510984040040361940002c04540d4080203030700350340000380321150341000d1050714058194410b00510703040900381000d000d04a150752005002280a401205514075001c07000d40300840107802c03002c01480140c0e0441050f000e0701005071100310340201c2540390f075414420040e2040c8001012645441581d5901f08800c0d400365401540c10003000d00c1174640b1070398402ca1072100311000408080601c00302c0d0f0085904222898100c0c020340f000035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 758134775 1250 758133525 758133569
    0xb0d2d0803070e01050c010f090b09031306030f02091c030207060206150d020f0d0606030b1501050d050a090c0f0f12080d110d11071505070512060105091005090901060504 75
    0xc4031507608241042010710408006e480e00340a810074101c0c0b10348000800203a203040503c12100010121245980100a101303501c10140b014041119802e14000521940d4501c032031001c5e00ca005407003a40300c3d60107050880303c5030440d140c034514588603401b2101d92550f030f200141d03101c0004540e0100d0002003001c040c00076080c00742d510348051344018640e90100d038503040054092002494141c840940e600c82c1031040002101c4101c0d0002100107540d406814020b00003030007446400402d01341181c80c3c01c0412504100c542010981650002030102404d840d900943c1006400d4491800b40300d141c0500042c1d100710400e49241d4060300079460514282d402d09012015003f9541c030410790301c10410244e00d800d01c0900c030f0054804000e0120039500c08281c242003000e010318448040035031303203050300348294580c20204454000b0740c244081c1034655580001030322240076043c44940c015010801d07a00940b075100d4001c10034641e0465500081d40d0300c40800b101d4901503401003890700b880c11101c41c20b81e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 758136025 1250 758134775 758134787
    0x1214011701060f12020d081b011d0304030204230705210f0106081801020d0b03070b030c1c02041a090102160305031c1b09060f0804020f0409060b0d2d080307 69
    0x605c0c0003030074140b4828000e0303485803200e5114902c481450130b640c0d04200540c0c0c00c20b01441c10b14183c05003411429008040c0e2040e01c0380320301c0c03000038491a9940380b00c0c052050540030940d11807070300268032441c0b0300e003061001c0d14990000301e8641c00e109000060380004110100007d000b421004d0308001aa0300740341c004c1d91a102d014182c1191804a5810082c003140709000170b28003000c40d00e4001c10410030403c2498540007450b0000d02106609004000461000409540060200c54143c80c103003941700c88250020312641c1c00030406921840b110b07803c40c06401c40100352111080e030031075422003822404c98024640500000301190000c0061101e100d030740003c141d03900006030342d0000303000d408560309501803000c40c80780303c001c15403d030410081c5e5a00405105000009030504003824179040d40054240140200c52510581d500d005070b0007800150390101002d020007404e062140c0c0214148030703004007d14144481107000c01c401240b106c031866141e261820791301c020381c6030440d15260380540c2d103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 758137275 1250 758136025 758136059
    0xa0b03011404091119170c0f0d08070f0c031e321c030c0206160309080405040905010905010e010227181521030702101214011701060f 59
    0x104c900c81c2c1c040350a03503150555090070031902550380d244c041c584502000c00d030004000c1d03100150422000c0420359141c0e84080d100100c000c41722030301d0142d424a0041c200b405880c0c0c1c007a2549005ca004541000304981c14002501d0140203000ba8420924440700d100d10340501c0014840310540d18059100e1170704980c440509a0304005440805060b000e201e072401d91400e4424041300032440a020b01c0750780500c2190343c040d403648060803051505081142d5100c6c850004403003003642c1c44c9141d10070f02401c103050b18080d0000a106010700c084c00d00707103079010f0420a007082d281035180441070314103030030148226444201001071407c1140b518850911221002804841c0c100181c0361702d01030550119118548900b1613042190100c007506420b020302440c5180c000f400c103410280c01c28290318000000e698005504031040360030a1940320301254070300c4211900071200c03400c08103205401c9074070035100c4e41a65150741014034140c54441031076007030710b1051240c07031512101400c0038480c1c107a0000035206 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 758138525 1250 758137275 758137283
    0x15140703051b010605040906020d0e010902090103080d060f090c18051c0804090e0d031505211e0109030206060a05150304031403011409090609061f0e01060c020a0b0301140409 77
    0x16400340d8405c04281550000c03401207a080d540000d0000341e51a46208204278103102000820003040e02c1d40c04a2683c3d94103020203445014081128150001560020000360164000080341199540c012201400500c10102c020816140c003801c144880f19405108441b40117094582100400c6110703401c0406000d0300341c8264100700301c040b8408009000e004481d103008002020f00078400500207044481e10360004041090030316040260b40e5903000d01414140491000740300c0b2400d00c4610500c0d140301e00d284400d940352031071440821900306511017803881c1d000e83c00b40c5045507281d2017001040306040c005c1a81c040314143d1400c2d2201c040101456005200f420180140200d100c1c0c02001908242d01075910020100014812400c10f03101e5240c102c1c41c0768005007481c0c1448110141c036030344000d00a124110b59922585980041000800c00400041c003503c4115611060b00904454000c901a4002e540d0303114001110100181100d048503001c4420720308803280041000050145190107036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 758139775 1250 758138525 758138531
    0x1b0306420b0d15172404030e01110a03030213060305010308190c172809150c240606050703020604020904020a051c050c030d02121e0415140703051b01 66
    0x12021200c81081003010300900b00d203245100203141c00c80380ca008041d8040d08080010028603206600180c0805d5400a0341418041042c04100c401207030f01100408420842c0c1c0f2030861140241501540145148010003c0105140e42ca503141642541c2c022b10006082d48420843c0d00083c0240c4c01c465520240d0500e401c03001c3c10042e0f111a603081c162002020541200014080c02014036101000030305200100030300440c10a50300060100d259a204e003442c0f030311503002082c400e50710031501d80b541d080c4d10115241825003070496207400b400c1c141c420754018500d4000c01084080c011019a01c01c5603060b03008050075a9503509100080307001070001c0360486603445001c00c4581c2c561010410103020644410071143c880d003084d5240c0940d450290b40250030201020500e940c0c04203c00e0b0500060f02041942d858007141c804003e1001030f50032100c8400081004102501d104c0707041c1e90180100c0d540d1108441000b45440b91134454400000c0114008104440300c4107854858070009a0b0100000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 758141025 1250 758139775 758139791
    0x510080c090103081b070b090a0609051305060a05040c030e0118021e1c050c0f0402040f170c0604060215010b04180c0207050909010b04180503071b0306420b0d 70
    0x2440c007406c1c0e41151094000114241101c0c4c100403a2200080c1003910300394842500e400c003c1100146550900c105a507112000160b00d603d0b4602160020032016002308001464141d004005240c0310303010b07010320b5003007614202c040008141c1107102a500105110400b10003610505190880c111030f403504800c0c0d21501c1403c0582018281ea0f295000324050200301d9165000c0003001e120240c1d244d40316510602060048210510140c0b050301c0744455201c440c4103019450320314025503852050fa004200003404034825901144000c6d110100c0004010103988491859078a805940180c0100d44002e030510118000070780c028a04446c241c1c015120040c5c0c03a00c000c260154800c40c0c030b124060b0f46500c1401c46070f080034484c5418181c08500441d90b600032681e60f1644034030030307260050112404a95001003404000703070440d008561042e000c00c024550f02411524144211103403103150b240c0306d1414117410b28030013841001020120080e4981c00d0070301c191403e043d000200182c415507030756002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 758142275 1250 758141025 758141077
    0x2030a0c0c3605011503020c030904020c0307031d010206070e06070501141909081801050f130311011b14070b0f0702031212070c020607080a030510080c09010308 71
    0x604100d0b21019010380d2140701c914400300321515402e55035400d0302458500100320405100304d198000303802031314001d6a03900011001d10b1071030240302c400309d900ca44002010544501c0c0000241217591181e01d454031241001c0410600419840c1c15027400360700030000190300c03948180400384900c1d0005000904202042d01c55908440101042503071400410003441106041120303600d40100e9105030a00151b107440e91410360721300410b00f54014100010850340e4880e0b0040d01621014041079112070380b40c99a280d059841c07a0300a20081d0707816240b200c001c0206510840b042031000600300300c030000d003a055940d6000d1071426000141e03010b025815003c54941d2a00d4000c1800800c40086151256070078010103062101030003011110080400840c7c01c40e14242056650040c82420030903545002030010039058403232414000e14441002402d2022250113a1041d4061106503825100035900e40301050f58a000000180e0341c8131881c01c00400000d442071004054144441407030f200d501a080705 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 758143525 1250 758142275 758142299
    0x918060e040b040c0b271c0302061e061c0201030b040f0e060612060a050a06030b0f071103090a170f0a03080a14010f05041508031606140702030a0c0c 66
    0xd0403078542d0700101c18030040c8111042048043d1403858415846c118005a090f030740d03080002e02d168002c500e206c020011550790322101204d04c0480309880400403600340340003501d8035400c58030700c481c2984042c0440e0b030703a080c69080544542e101400e196804e40f5141140c1c1e84004140724200e040640301d1040004589460250424004010b800815244601500c03030341020720007410325000d051780350407801d00c1c040000f0344142c00482444c2c0c00074560f01c5208084010344030940000e059400f4040910030f005400b0340b05240b156900369903417a00100e440b1001a00c034030800b401030790b201c503c110040c440c8407031210b1414820300d890401c0300c101d21080010117090014440095010460010401100e8504c6003d40c10b410b80c01d02600e4070f203e605105d046041485c0c5405130364050340e602c40c1100303000c0004480705001f6043e120101d0341c441d4400c0041e202c070614610070442c0c00c11f042c00e042c0948d6464003402c1038001c00c13030340e0003845c24052003000c1210010302078442a140208902070000d11714074825 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 758144775 1250 758143525 758143531
    0x203120d0f0b030a0803070c03050405041401060206251d040e0105091c0f050a02031c1d07030c0b07020307031208040b0f0f0402010f020c0310020703030c0801060918060e 75
    0x11030007107900200c6a20700d5085a4584072140d010f6009842e6120000e05100100c9a00c80040e0414040c61010350070211074900581d008150810300e0810140400e0802c0f4040504940f89a400c4818036503412000144c0382445002d855003610a40031040d00c907030b00501c012691074030700c1d0a00340c2001c020784000500742e4000180041c10759542e0340500c501c000c0148001c091025240d28002d03501d90003803200800d48a2040000c00404c0004202046009d2003442190343d00e142c58130910322401c0840c42550000d1000c00c0141d9002240c083c507074a8140c40104009084940040010a4240c03808480391480c1e07100c03090890389401100d0b40400001c03440810f00030907950646d41d00c6403610b054644110500b001800e0f1409158030701041091107060b00008603481036082c40d14140e1414052004d030300d02081c01e140164540540c45081d0304008581d406480114007a03902489020074090096036448800e0091000040c104d110600451071180000c0c590f403080050005051903444d8404002100d0507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 758146025 1250 758144775 758144797
    0x141c020f130501050414040c0e0301050414061303050d0209040b031213050a1401120605033a080103030c03051207080f10180e0111031f0602031303060504020312 71
    0x125884401c0003400d01410050842828000d240c141080c03000c013041030348002400e21a0b80c4030060260f40b184940120b01b0300c0c1c400903001344034909284c507040307a201180c20b0a0001e90b1160900040031100030700b950380501500b540701c251500d200318141c0d80103035002c541c2e030f50303000b0743c840d64660200d4904001c4041ca0304da10728140341e104d02004002001041d40c0d0f52100b40b04000c0000c0c01d111402d41c450310410034440900300314500341980a8100e000d81000c0e40043e03414080c06a0340c3e07550b0b001e0924205c0c2c076500c42721803914820012a4401c00641d450031258000100e0050060002a00030050b5942c480e001e8200b280c109a03006c5c8814440c0700045800c0c0b0b0001c0c1003a0180700981c0a00d006103070300440354140c081c4089080c00c2e01c4070102c440550f03501000760b40310707080302083d900d0070344c008081036190f4a600e0b90359190490343e1440d07408660320100001c074100200001c00d5031005c420345600b11180c8000c03a80d001c0c80c60f10f40130090000900240e91502a00d81010b02075442040100305059503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 758147275 1250 758146025 758146027
    0x210510030b0403081f0f180b040f020d0f090308041202010609051302120109020127051201021c0b100c031b060c23070f0c08011404120c03141c020f 65
    0x70074417904009091a543d44101801e22200303100640101c84204240d40200d414808103014401400d400b40a04107900d6810030b1800d041d4640012058004103645501180c4c22b0048010919600044905c4450050002412400030030000707a580141243c00d03039181c1c400400c0d83c0340c441e02d0003000c45d502034034244602001d0724101c41c1107040c036042d02c40e480f0803100d000700030710740341600060b00c080700a00c000c503210605401022664500811914003604024007480204164100728500035400304039041c141d2418221011400b071070b18040c0d0080d04032f01810300182000d040409030740d0381c2c40c170b142e084041c01581c1517078a41d841980c07008031480a0040c8400705a030321b01404003510088802d0b00344e00d625002c03000340c4138a4821003c11a10703102e601140c410801051130601500410440c3c01c4448103500b44909544008900090180038a0040a0504c01c0c01c007008015958190743c2c0c500140407840104200d07a0003e40640034000c00c125100010040103803402c80711049070701c070901d10007007000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 758148525 1250 758147275 758147281
    0x106020c0901090507090b0c010908070b01031403033112090306050a020c0304140301201323010e042c0c030706050d09030c060905030c010b01210510030b040308 71
    0x181050001d401411121010001c40c00c004a008007817901c64010f89200410015040f01c01003825445600d0080d0042103854840b243d80c909080e48840a21050743c00b14607070350803040079030300c00300490f4003421030703000d4858004122440c0351801d1041c11559009403403030714000300013007001c015200d0a60400c42d42c84079100f508618240382180c4015004800441c4180849098290004116800e4411642125108994400003e07000d80180d50b092242003600484200d45604200013074102940320030364450601ea11030b0a2481518524811007548038481c40c0c000119500940d100c1c2c0d40101d0282c804150289110503220b020b00203036001400720303089000c071810800410701c4803585481d0704901801c10f162078080d009001d80140a4001600c07680d80240d04101400f690102028a074880c609100c540d2203030400640725000702f0755004207542041c1c00c04149600c9110074900300c2c1c8071078603040030101c2e044030200d000700402000c024484031155030100c023141404458510440c401e035500710300340ca = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 758149775 1250 758148525 758148529
    0x10030c080901061d0a0e01060b030103110f09180c09131a04050a0b1e01030809120115090c020a050f062202130e210c010b09040b06060915030106020c 66
    0x840024400426a45440f000b408440010318402560071603030300340120307280c413406000401422001d130071802a611304100041d494148401a5040781e0040780740e00010600c0710180019441a10b180c5075100c1d11500c0003c644070b001802c042c80c1c060211f4111500003100002064030440141c860703041e1141120104000c1046402550b512a40d00400031710503400c1ca0f50f200d9076900c0311003400505d448040320004507010000702d009480e058040000d086a542e581c1001680c40c1c0c4401025400b031840d030400d840041e041400b60146104403911860308051410901c90001c19658040500b140070b84101c0101090b0100400b00c80c001d04000642001e0605048140034104030000d0980007018243d01c2d000969a07580800d0a41d0a102c54042403640d00d0b0000641041f15414030003051100589582000d4050f480284c010040e4540082001866640130001d0300b980803600100741c100c0200000d980341c1000d101402016a014100c60024061910040b08540098118a00681c000320340140c2034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 758151025 1250 758149775 758149787
    0xf041707150c02072c01090c0c0507060f0807112e020301090b03061e1609120302070303080a110d0b01170a0e0709090b1501050f0d06091505091f030210030c 69
    0x111010300005511141d01e0f242c5160054814461f04035a80d40d030340141d00c0c0340e9004240c1c605500ba481000c1c0c4070140c0d110040901404402a403001c0094000e00000700c0300b5008607084046d17001080000c0500c0d042d000400c000c09070301c855203665901041d420360016a04a4000355001c3d000890010449640f01c01c145494a03d0040c14040c940140c01e048000003921121525041070a14080c3c045503124400c09807500000f660060111030020000702c810300d5400310300b0700f040d0f034070954610500762202c02c10b400554226800b000040141080a169222840e620821040c4030604119485d002e20000729100c1441c11900d1441e010b403100b409100c1d5410078441080504401001088100b00a4503215900b800040503e02c5080d5000881002a8002c40990307000c00030070030089a462075101c8052000e05014401c02010a082030810384a0345e10840c0000203480c4c010b0441201a43c5100d4070f4095042c1c80348411010861210020000d82c03294201030712004003986000c00c0d0002c0160f401042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 758152275 1250 758151025 758151059
    0x20904080c030f0306030f03031003030503100b04080f0c03010c1b1a160201050c0a08011502010608061f05121c11030d020301031a0603120a050d1506080f041707150c0207 75
    0x11f15002003042140072410210f0010030f682d014a4219141d5071004036401000070750760040d04449401050008038840b0010301581850500c0c2c0030780e2a8024800b081c0741c241d880700003111011440307010543d400d0080000c0f112144600441004aa104840100d15804801611020300c030904510112a43c6c0d03409000d0036402ca89440c18a83c64004030000091003850180161000d0701400c02a002c6945d05c00d410040140c00003030107031000c6092100d080303e6809205542101c41500c90380001230186000c2680c04072900c25900a0141500050751443d0740c1c0e9400713001d24081c4040f180101650020401c080c01604001000060340d071750450902000c2442200c000c0506c402c469810801c075a00c022400d1154006106140b40d2a146504425119405503504441280d40340510801e00003042c11000000c40c0d40585460f8801d46940580c85200107040b03030040c02801441805020001d500001000110b001e1001100d034034210781070700020307900401401e03801070348502410f11918510344aa41d00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 758153525 1250 758152275 758152303
    0x405180d0807020304031124092d09130503030f04030909090203070e15120703020a06050f090120010e100f1a240c1c050a020a020904080c030f030603 66
    0x101c80c5001c080080d40c030700c43d41c00003d00b00381c00f02060140c50b03210204440034a030050020814107010b51001042250020043c20384210888030107140720007021600c00444d142410240c2200c038000c0d10074840b0007180a8801c0c044003c65403c2000440c10a101440c003800340c9030208501e07402d090070008c0c8080c41640081030321503c0c00300c01d00b00698000803030f0f0b001ca4421403d0f81d4080d40e10b084ca003075046c1c90061307105500002d032480450b60302000400d801c41928400c540700f11040707850300710440c1c5078054400320b8044010100b00d1140590b008440d141800b41075030325101002840c1e0100103094400d80c04403a540c961001050649180c810702440c1110b440c4c90b2410814040d00c20040c84c10081161591070207400d010f554203503201007054450003000508400c2541d242c000d910104c0c1d590310000390100c01d80003410b82010149110708101d03007500020383c2c000c00d240d130701c00d40130414400000351089902c10420060060a20400c0c0050040840140d40107502e80ca040030506043c01c182a40c1d0355 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 758154775 1250 758153525 758153537
    0x207020306011a0a08071103040b0d0516090b090a090903030b310b0406090e060a060f050a06441605030f070504090f02090f040501051e01020109020405180d 69
    0xf0b2810b9060506841c012120761a029000340c84000707055440307842c0c49000044070f00001501103200d81c4468002c024114200c0f0040110f9940c6e400310350f0a04a0b0501c1c0700c400a480103204001c4540d007800074101180000b403448130099540d150203400c4442540302200420f884004c948494a00010300c0c08009003203882c015010a134501c0d0b4090620411504d80d800e840e81c80040c1e00c45070311544c0c000005420541c40811042c0c41544901c1e584807001c80d1120350450078840c000c10314200d800000c00031228040e1030706143c2c0f400d2000540e411403610034001159081500c540308480e454585150300529252244000d003d480000c241d01d480004200428509a02c0000a10154031408036075104400408075200e03038444003001c551501c5240d0003440101d040800403031184589034010080d8200c00c48900b000c0001c1f500c1444141c0e5424407c0952040030810381d40c107583c01c01015025810360510000409081e00e50000d021242e007594001c4107070740c02c20002000c40c8010070020b000544241060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 758156025 1250 758154775 758154809
    0xd1811030c060a03150b0708030f090a0515070c0c090213080f030d0c0c08030a0506010e01030b10082e30080d231518010308220603020702030601 64
    0x220301070707100c3c01d0454010560b03945242040704e1446030700d59001d000c1c1010003d81c1e400d07607403d101019410550382c0c1160329240e00c0205485040028050301d040f648000580300206101c0842602d46400600c2001808124044d0f14009050b980100d0007428401c1c100588907a005541c0f11220940707a0002e101c1039020065901134002e00006482d031500310090089401c50062000f15001c8040b001e000300fa40a010041c08280185600840c3c4142002e0f030f00c401c981c140b141d00440c261207006407030702d401c903a9200704120a1031144401c141c0c01410401d01e0440795090038108550b218881c20748882203040320000b40004411450b41c210703801c03c07100780c2640d240c2c60070010099049000c2002031801d400012034040d0300080750080351aa800103a00c002404440c1984400035504c00c8a840350005001201078829182400207810720b5488030303061511030707030030740c3d0b210a819070010700e000304458208a0040c0300b8142807203400c40038140680e000b43c2c8501907031041c1458550182c2040014103210140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 758157275 1250 758156025 758156029
    0x209010507060b03120f031f060512070905270c03060603130317090105100602120a030e0c1c0c0807120206031e01140910050609150d1811030c 63
    0x70340c1c0e00039400400010302100400b00103803408a40504c03d01071014085100c135080301d64080954810010303803235010441b544210714055109524000d07a4003103801402800c0c054100311100c0d03039200506003002410700d40c03250000365414560b0700b0348526245801d22001101d2007001205a0401d000f9220203065040480000b1007500008003812842640070702010245481081c02d40302c01c01d81c042c00c91055081c60355800340039280450b51013500000d20309000804510000e001980520a44c01c420b04080d91480c00320060710108a40c0f121a1203405003215041d81d8800000c01025010004c41c0300301c54081c42c0c40c02c007148043c0d20404198004084c10031040070009014601143d04a0340700e5501c0c0c1d203101d03039031045080741c1c0740000a40d0324500000c9070305080040488801030080755040c1591f0354590107170201d080f4030300402d40c10810503c01c890050402c80321400301c0143e680207850404d08140c0c04c0c103085030203044010386a003941442c10402d010034010000700190303050b800707000c0c1c5800101c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 758158525 1250 758157275 758157277
    0xc032104020d14150406020409180b0714090a0801020a140712050a110109200a0f05011803120e0103061e0e0a140901020318060403080f0406061517070302090105 71
    0x8010f0289a044852044180424405441e001011036414041414541841030085d0800e0040b03400c074a1911017000b403000d507510440c0601f683c0c089880c04460340c58420841b02e110741441d40d07050010b001d0203049007964032450198040c082007800184c0fa0415034400601c8610600c81140003070204010b00b201162a44c40c5410156150341880383d524400c01c0001c4074000c82111010419529028805080003420600f550b01828803a504032410081d04c4100301002c0e006205108104485c080c0412007540035696015140d2011003130314041581d1394450602c0c0214220399200000d1101001c40d209603018442c1703201034504400726403060104406940a0455030f401940e41140610000800c544041c0d0402284822403002200310340c00c20064490207900240c4450f4040c8040e69100103108100264051042d901a07a81c00c6068442d05400c40e90200003610a4480640380d05021503503511382a0102c20041c1036036100110201c003070403400001d03140548110201401040143c410740c0e8420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 758159775 1250 758158525 758158549
    0x7150c1704080a0e120106180608060105040b0102120a020606013e010f060b1e0a0801031721100602010b0a03020424032102010203130305030402150c03210402 70
    0x2602c12a9641c3c584402600c01c2d0080c0c550040d4002c01000100c401e00301d06410582c1101d08a500140c8542c090055000c1035400070700640e0155802900104014a460b82100c0d028041c1030050754040c802c0940d0910341030f0f0001800d2405640070005001665034040744001c08548005091800e025214261220b00346907c80041c103000c0d090400090311100a500010191a200c1020842d4613505d0045072002d03006501514070a016012003075408240d0841100d2846e00350390745180d0540c0c256a140040f08003140090045c000c0c00f440b0310350301d4803080160120320904644e11111103180c0000710251800e00c58100e0030071641800300c50303030b0161a20404c603002c0d40c0d8111400b00d00d807050030030002070112014400300698101610000180140300a40b4100f01071411075007400c0c12020340042c0e00380d202c00d580310040c024140c459440400d11850266030468402080a2981100c02d03a203103001d508155560b00c85600001100180c0c0700d010001302c8051074020440b0f514030302d05a0001001d0390805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 758161025 1250 758159775 758159783
    0x5060f041a0306010603061e050306010b070c030b01061101050a141317040605030402010212040e01030f060207051209040b011e0f050d0533090a0b010e03010207150c1704 75
    0x100110072142140c0300008490100140c21540550307510100100130b00102d01c01c0c44480b0315001c1c120090890580080d00030307280c1c0075004082076482c1a1400c0d2140d80121410f5800700c3c002030340400007641441d8114000c007015035030328440703c91900d03110342180c134080e0155114500d08050080b10001c04140c00350300a00040d2200e6403250305d4142952000f103071154420360044001408030340e240d04800034502950007a800c135050301084034800000d61080e4012445844031800040000440c15921040c0c0d4500c629001350900d061903407034900d80300c00500300d1035403201c1c08181e80382242800d10030701c01450350910340003041c407200c0d07000240e60103e0040c0f40e03003c0000301d501600140c3e009400b1112041605402005103140190380160a00409001d034070038a0f60b81a502141c41510104118411000801070a0303140c4801c2c444400030581c45802605200c1d02110200c481d50302031020745107260056a0040c008212074407000100c0d202c42c81d000c01480f14024880001610280307030242c2c05544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 758162275 1250 758161025 758161031
    0x105090a0e072007150908120f070506151903020a090b03030c0703030507050d2f2812052113020a0306020d0b03010e0c040b0402130803071505060f04 66
    0x12104122551800b41c42092543c4481c02900740303e00100040600032070300d0321480d0348203040104808a40d054560300c01c400303280d031151700b0b11002c0460301c100908440e201d20040038603144040e9201c905012080364440314002e4244c0060980b400d00010001074101d141001c0100c55007942d000880c0c0084c50701031802d140f076807100130340a540c808108441c0b014515070204c41586540707140040c9154043d10080700c603400360244100c5680d01070b201e4020040000e07512031000b200000900303001d50700492000c5825114031041154406900303440c40c04108450024940c1c0b513151804c120301c02d00f03009410340f0208041040484540010032000c551101c403a80324007400d0391110520050b0901540b03401035403282941e4000010031116a00510503c1c100920500051b0702c040201400c072040e03030b0640005038100c1070511003076103407544c402e954041c0000c0c80103042850040d1030700c1c011100e80c0c0242328140d100243c8442880403d4103075070551070f00600c0a000030b160140102c0d407440c0d40c3c40541c50103291 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 758163525 1250 758162275 758162281
    0x90d0809040905151b0405090115020a080a05040618050901052103190e040b0906010f050d09060c08010e0615030c0909150a0803030903191b030f08060105090a0e 71
    0x40c41c1c0e040690075980110494100c030241e00440862050180c442440c0d030f00c8261442a01101d00301c06803811290020600c407143d80c80c01103c12070302d8001c08075160460103128100c80001d000e1501610240e070169a800b038030341d0300b0150058940400c484e1000a503100c0700800308041d584484202d41034175005d80d14003441e0358007411464400401022410210700001c140c101111200c111004540115680c855908450040500080740c2502070616048008100010700c25409186802a458134928010303281942c88041c01c8102c4030304c003208541e0a5125400780788019441080e45001d02090181c030107050401d4000600145560080d00802d004080005080143c4110545081190103004c4020a01e8a844810441002880e08910445a001010620030380c00010789106001c107900a41c40c0c2078441e56081c00d9580c00c4e4142c0c5042140501140d5100321802c0c01212400b440303030b280c40d914a4000f0f0405050381c1c400034559810442c080c00008460741e01c81d0b00b01821290f1400e2081801d0b2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 758164775 1250 758163525 758163529
    0x8070501020708072105010f0203061e01020606190905010f090c0809060403120f02030a050108010608030a05090915031c030c0309030e040506012a050c0d03020d080c070c0b03060312090d0809 84
    0x880b41782e102400551030303c00021313156815600198030845c012201e0454040c40a10450854040c0c810000e0042c0c0c4800001006800c041508801c4000402c10500c285070340e40d0b14540584409801141000d80940b00c10441c0d60303500d0007407c4c0d200c0700c2800d002400d4504081c3c6142e407400c00800190411401060168400c1c086030f00407058041c2003036055542c0c0c94400e00f2840a0103003842100d01d2507191050000d07248501009a403002080c0da564185800740580030800c500d0340137003003030548401000c10160320780e804000d407015030024200344079480715a0503400f60031110f0140740e110138142400c10220009500024284061304c0803140003a081d10355000484001650107210883c2a151000d0303840c0390311240c280f110710030f440f0750100c41d0540000030510103144e41c540d02c0107001d41e20841800b03540600800420303074080d22040b1102e08084583d142c0c01ca4225095004281c07640303000040c840c660800344002c1168124a05800d4506244103002c5907040c031044074017401c020004a021415a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 758166025 1250 758164775 758164829
    0xf111c06231504062103140f0f030402062817040c090917030a0617030909310602070308070f09060e03030c0d210603021305042a0807050102070807 65
    0x30708041705414455071111100614002072080c402e0700451841d540e0000404504400c4903108002001403030300306030800c5081807054002601c01c907881103060006002c004180018190074036405903000c22200380c45500580000c4040b86a00405c170489000c1201040d406190141112903040000a1586460511aa04041c40e1030b5030302d02c48030000240441d5240c56000203042c3d49040c5e040300f403250740710094556a031142c03041054000b22580300141010107500c600745940b212201100c07656003902c0802101e0200780180449170182e000c2101010300d0340c81411554011b0709400c0401c902d00c071560b40a071114425110710300c1008000c1e1030300703041a241881900c03040c8540c20220380b860740c4000030143c40a00901c0b54500700c0e80381303078604c031040d90403c0c0500e20481e600a80210040040c48540f80b010340b0004009a56550a41d2040416074480700c90070342c060005020318140391b6040458036800c0251640c4514110b42c04400103020914010400b01e0454010780c1d40010804d004105000075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 758167275 1250 758166025 758166029
    0x70503070b07120e0c0d02190816090609020909220c09021207021623060d050601030609090c090e0708061503060109020c0a0f111c0623150406 63
    0x41e450260148a2a650480380c0c03100900c61165050110004041c3c3c0140d0340c40d1180b8507217030302c030110fa06101e000d07046c10070903240a11030601180b40c3e200e8448855600e40914200752000c108081c550410003107201c5c0c0f00d8400541440c0d00190b2814110340c000404607507004e05203e00981d080c01540c28154000302200da40320f076000d8414010240c1e0307000103800a4201c43c0c505144030416000040b160f80c80450608851100d03509191002c1e82441422010111214002c064202e28040d80c00392076a0303010701511402e200503c0100e540d1034503100041c144c40e170540c400280e00e81080d0f0200c002400d203503400d2040d40c0894200241c4e58a50204031460200503501c5480349010b15810712094031413405e02b200d20500280d040b030b0040d9a80c1c2e88038400b241b046a1602d800c81d0090b0466030f0004a18400d0400200e0059104403030080820340018500710320001c0344040a402a0301078020444540030b01648003180706046001c1300c81c2c3d0341106e0300ca844010510300300c1c000801e202c51700955541e4071040c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 758168525 1250 758167275 758167283
    0x60f0f040c03020903060711060c030c120c0c0d2102090a0302060a080103051203010605030424061d0c09032e020304030f111f020a09031a0613050108060c07050307 72
    0x1014904111002c1e0081d4091080e9a003c4d01601e400a5000c80c00b682c02c80a40240b464020280c550700c6030b000c0081601f026102106072542040000d0500b00305181d41400303041e80181090307451480c00c0c0242d10701848818414184482c81c01d0080540b0700749200e4410b441650807015030303601ca00a0001d440301d035503508002d41c1b01d400814168243c0d0347c0300461030705803841881150710f080d0380b0040007440c038003091288000003002000002c0005000c0e20300c03014451400c281640001e161910b4013000c2d203135550400d04c43d405411409101100c0e60801c3c03250030131f0700011007903c5c000446c00030031344130540035084419a522500e4601e4101c141140031158250f103203c0c08546909091800403c101c0d912045040004e007042800790b40c3d9180895040c484038605820010114212103204020303400503d032903000d10101a0380080071603d15018090209507080f0045c00500e00082001f85480300b5501b111000381c501401400720080006501707400c5032a1100c03207a1038500324504a451481040d000070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 758169775 1250 758168525 758168531
    0x4060c08040e0103030c020a080a0807080702030c03070b13090207020f0f0a12060207110316030b071202040312081609050904060612030804020111010e0c10090e090a03030b04090308060f0f04 84
    0x800c2c1035002c03009a11045c07080b90075004040d42ca44007032b555044000c00152400350100510400509054004d01d02c0c0c520150a40321648103501c0024140b00040d03000285000000594441001440701c40b00c0203420609407c600300034903500480d02d4881c1d100021400380c0034242c036044190351000791b403030010080007418609003403262030503001130f40084c06c040307551840d45020080b00e85030210b20442244054018501a01e02d0360701ca440991034040c10400900140174813032561106280004d00180d17010320050311140208681c014000b08004101807080144d10499264580d440803000c0100c5604450b201d2160701c5a040000c01440c845c1c3c84403404e40803031416001055000000715121314000d0321150004c44074040d07001e090342c0c00c00c0b9010b03a00d504440b4007004e09140c01c81c5500b10400c164903150a0443d11802c40c10306009080c1d54400c2180d1107030b00340c4820542d00d03024460101c0000d8805110050940d50007410088020701014807816070768000781ca454a803801c0c00640f10200410034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 758171025 1250 758169775 758169779
    0x261905241219031428172701021204050c01110307060209060d0f0b040b0405010b070f1401050106020a170a0e010e180703020a110a2303070203070f0510030b0604060c08040e01 77
    0xc41c00d05110080007484010b005c0380941d00303490113030060500c11741c041200205160740c0d12400c071000311000c02c54080c0c2045584110f5100e03500c24406882403800c18046401e06040c075017085031030b1600803100d030f40c10461101200c0d60031501c00700583d09000e0f440080542c44582c0300000541c58001e0000c4601414a4002c0c1f1242c02810341d003040c003400009940c2080300b210301c0c03000d20003030760424094600c8203402004483c002400c0207211a40c604d024401d91040076603d408180e09544c0c1c00c0e4846070069124551800c00e11070917442d00c0d04c041c42c1849000f4504246002d010f840e1800c01c044190604c060141901c981c0e4035100d20442c5001c0f00340310300551614000308043c00a4100140340e0001501c9903010b00b03e000d03030000c2c00b2401035402560005100c1011001da20042401c0707242884180018010500161010440a0050141c5454108501c1e040505001c03803180c040c01000209828a640c042054461504841c140e80135450410144a09070800307a0b0f152043d81d0141d21141104800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 758172275 1250 758171025 758171047
    0xf0c0302032b0806010203040b0903030d020403051e0d0c060e030c060408030108070503151b07080d0b130513030807090e091c2619052412190314 64
    0x11a050718108881c008080424a074002c84205400f1140e135805a40208070130f2042c0c8206a02518400b4001003c4a02e403a200c030280f001647c110790300c11036460b4094021b400303201440c14182120582848001c01d030501810348010300d10007810b04081e00080c1c1d10300308103034610b2003442120a000b80940c212102414145458481ca5009110315440c9000d644000300d1145004202c03640103a122001c50505501c8507041c1441c0d034642e0501d01c0810340c41c100b00c030000040075200641240340c0c1c000000140d07501400c1c24000f0b50541101c01d03440040c981010030281450783d4400280b100c2e0186450301140d42d801e9000c0d10505003e80205290528810070001d040400143c0c2c0d00041c15100b6969441a00300503058802801c031541c2e110300d074a000c960594000c0c500c0c10840e80e0104544564102d131402e500d200e242120300c295624500241000003800c50094a40c09a0300c06550a0b02c124807082c262080c46512a41200e858844200742c002c040e40900d0b11854101017500c0d08040803541e0b480e14160 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 758173525 1250 758172275 758172313
    0x2404030b0c090904111e0a0e061f020703060b151204060f091b0602061e090316060914030306030c061b01140403120527341505070f0c030203 62
    0x45c64415210b103807a01c00201c0380426408040d0780090000b00035203040822806162000610280d0041142241c0001c0901440e228080b0900c881d006010028110304140d0256680d010f525401401e01950b4180d03504070007411588002c200c41010f05c2c560f169854041d0140401100101070207081c441d8680902c4048170185007240004001d014502c0d0740c620041c1d8803590100e9010030505004995060034000388500c0c281c0c040d1009064924283c4d420700d0410b08001d0316007060300d0321b40d59420301c03104100c000c01e0060b5150000d0f000031400d40c0b5103000005c2e504c80c140700b1054002d09010560290700228008207104d5200e2a10003446000340c106001840c07101c3c11076060340061a40c1d512800003e199101d190b014000c0007043e500070201c1c1d505558201080c0e10488942403207070345c08030040149891245152200322460040300100210000d055900540c0c100005040f0f20011291810b40c00000b120212507000c100c00f103080056003000c803142c1a260348082e4040c003820b52101d41104810b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 758174775 1250 758173525 758173553
    0xc0e0f040f020d17300708040b10050306010603020a0201180b0705070311010c1e030209030d05030606131e090506090117030f19030e0c09060909010e1207022404030b0c090904 77
    0xd4502150382c002d0410a9522000a440f00c0010407e500c1c0410007080e418450941c0c050140111451034035524404a803034500c00740c0c070401c000f90780828007500303130713075081c00742140760600007210b85c00c0c40c0000d803184c405400000e40520140000021707248201409540503104940c0428000c00864103450b0b00075200c80d0820001c131040e580e440c8007840c0214040c8c070903146038400240c000d021400038000182c841e5400a0300e0250300440c00e000f4100940b0b08840100d001c0c01d210340c0140030a00d446020210360080640160806500385820840c140d2901080541101c481e9400303a280840020f910b035055100f00075112100306400211085002c3d0366403004491003107580d90030844005210681d50f05c030405003000c3d030303449108030020642628044203030503001065070000113a405a10f284140c5406007028020348405004280d100640c1703448800d914801181700400d002c80303c1c1e0190502550311503400300604824a1001003207200c0c5045c826140961005000d030510707401c16007444a82c0464030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 758176025 1250 758174775 758174827
    0x3040302010b1f09090f1d1011180904110409030f0e0a08060c0f070206031515040e0402040c0207090c02071e05010504060f170f060405060f0d1104180c0e0f040f020d17 74
    0x2180602c0161480141151074912000c441091843c811032b04110007400d001c1e20a030343c01008200031a080340c0d9248945403035180700351640440d10300300c000040c00300d1000100d03180c0b26035008034042040c21400b041682d800443e181240c2c0d5903405a8040c928503004029001e07400410100130407110b5403a05540019a00d8100c4240b120540d0380c0207010719034880c034090881000700c000089401810aa04094200703589401a1a072a03a21402001c04682101e000d500050744205010032080a64080709012403100084020140d802d140021709240304038402da50400c9010341131071014074810b0070001645041062a58482c0c2402c5440304072900003170315154419454240401e48910740f000000729548009485501d8411881e113507984401c101040e080d0300207460740388091720388115040b142800c6105040d180c80c49818982070b02090000201000000c030405002e05c40490b490070f10000c411a412070385400158401d1502d1300802007440762030210300c103000c030740c540c0003042035204075110300c1d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 758177275 1250 758176025 758176031
    0x40e061816030b0f0a05040b010e030d030b151201060f0c081612020a050705041509050c071a01081002030c191112130b070203030c0303040302010b1f09090f1d10 71
    0x24403410401440c0c080c8261302c1e0b011403014401c20560800e600983c444c4441410076081c2042804003117400c2248122345030b00020759031f1040704824542014250382c08050510394a0512145442000300c441d0306024810078000d1448480c00314610a41c5400249640141410384403145d50141200089070304d40c080320000c440f4000c42d06d082e403000440e48500381c1c002009003a22071402c1c05000042460200031440d01d242c0c04004202c0d8a281d0051500404507116880e6483c21181042e0340440c00424682015011401c01080034060025612949400c581320050b602d4072000c00c48107042c401c000040c00300e00b810200604e0a242c2169194440180724000c2c0c640600100894590b04d00c5612040105000e51f08414000c09004d41c0c00341c0780c0c003803014084074940300700079440c680356800498040740140e44a140905090a152410119604440742c0c54400f850705480301411b9000e4034050010a01d07a500309401d035108964000900c1c244189003801103401c0000d4010340c80b070340408c1ca11540c0f242 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 758178525 1250 758177275 758177291
    0x1303030f1418061e030f0a050916090b0414040c0906090b0919090503040b09040c0c020603070c0201021e1e070b040614041d1803030903040e06181603 66
    0x65840100e61141001d074011030040540c20040002c550000c1100c030740004c2c0c01c90b803d41d04403c440d00003180121101904200c0d42d10300601c000041c2c0e40020424500c0350085180c280c10701881c200007406940c044c03100498100155008100180792100044550121300d100344000d20003494480000e076112a0000c0c0501034a5001490640b0070b082e04041d00941c810300000d804010341c080c000d90312085864041040f1301c09450b1145950886d82047c50400800190307244107181c44c2c401ca01185010b8289140e0480e16500000d1440c04002c1040c2c040c07084908004045a1003030101c01250300ea2600840c1d420150300c3d940d03e5880b481c071940c0e408a030741a1490f0810044000a06504607115204402e242c1401c000c001c40d2154040340b01400c15950a00011400c0004140781c81081505280700190620708000d40c0c2003298050000c0b800281c1040003400084a4040200c800751981481000b40c152a04008079820243d01601c80c00e0300c0d000c1000f8009602d071252103110103000182d03405c0c40741003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 758179775 1250 758178525 758178557
    0x504080705010b060a0e0d0807140303090715050406320d27081e040303050d05280b010908010207030801150f021c020c1005092e0c05031303030f 64
    0x5c8104440100818031007400e54140e498110441c0802920a040300340c20400036a0f6001640703501900f02c0541a000401007209a0004004410043c44610003100c400f4001d03003006400c9125601a1700200542c07003850b9480c41e2080c501c8940c8040282e0f900480c4d04041012940240e0402c0308900075031410482035510003403521001c2071803401c1105c001003d081503644d132180654410140700c0d9106c07481c4030207284410181d0014000640c0242c076070907070f16071f8040015011100c2c0140340c0c40341e010201c032092244014800300ca4090164102000a0402e01c2c0b60040c1c5003004261f02c802e803150300001743d25081540c2310315564100c401410200e4240d0580a005960303030b0466100180060388080c20301c032003003854050b0310006942c840c015200c003506c0701c030003013003c8800d0384491002148000035964000d0404001c100008071001c204101010b540000700320714944d00b032800c5820000641c1452090260038806c54042414624001c55a9a42c0386000b0f89800402d00680c0089600c22902001c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 758181025 1250 758179775 758179777
    0x1512300e061312230d030501080312061005070501111b0d08040f02150703020105090c1203070b0601140304060b13020901021015081f150e010e07030209040504080705010b06 76
    0x159000c920401c0740c00742400c00b100540f118442c02540c81c0312106100d810f1800d15024143c07941080800944203050511501500f42c40041e4405141640204001440d007034900e0710281c4c014034200ca481104407000d0004035001c2c000c1000252055203010703001d94110410100810403002c00010160401400a803a0368544da9002c4550300424803080000300068440600342008500c01000d6840e580c400c2c449425a5401110003240541c4d503c109019940004000111b00c05101f160b60f50b050300c54103400c00740c4a02554038000c161040003804200d01781e00031000c91000e110350301e90058072440c0034208500070f0112f0740e040500500091090340603c920034000c41e810a24180c00030316058407100c45c072400421100f104240010007014010030b891a05000302c0003804007909040a003002c8001d45c5104a841d41a80d0603110030048208200e02900000d42504481801c1c1c4406519901c41901350040d1050344043e6510030b1a010820040186407005071520b20b003d4030080140108050600900d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 758182275 1250 758181025 758181037
    0x40b0403020a0b130e0604060306060305030309010501080706090e0a0605060304050d0915090b030406090605090309030c06120c181908150105240f0d0912031512300e06 74
    0x451507144e60280842410316008a40003003002c2e100150040d038030b4071524112101c0703400445140d0000400d00c0441c4c06c09026684c05041d00c00e01501c003040c604540941210200c3c4515003070f0b4403001002a50507103c0c1da1082c8000c0c070002e004543e580c40d0900c0c0160f201c0890342c01c4203010034110341001c980a0841124407c0c500e1094a450104608024409503180c000400403991103445601003000201c241c0101e80c0290080b100854681500340101400d040c001c0340d509014502c03c0c416010300444c481c0c50640c20000a903d01592100f41c142d0210710084200b0340340c0e400140c0300744a5802403141085020865001c0e40039607101c0c0d000603038074545c00c900a02c0340c1640420641039102030700e041c24000440b01800c0d100c045140c030603000300076031094021070341140c01a69110b0700740c03050068411076024040c41c02c2c40e04000040e10401283c1a00000c1d00072080b40071001b90f4407000308505d10700c01da15507016044103941d4100c0031041e6203001d10310161610000941d01105030844e8100b00b410780c1c0c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 758183525 1250 758182275 758182297
    0x1030c06020f16030212100c030b03010b240c07080d05190309050a06270507140d030c03030911040f051603090302060c16080d060617010501080612030f040b0403020a0b 74
    0x4100f0b89036808102d84813140c10785006840c02030111111002d111485068040180c40e200850403500310020142119218200b050044003a40d640034518480440504017210408042c107444240d030510725440c0050503044020503105440103d0755a41d00302018005c843c000701002000070030100d00480640d1525a07006100e60b004c01150400980c2c1c035044004035402c0c48039041c08010210084c1400b1207034411040d50103412020707051160381c6071503c3c000508441924001d581244942d0014101d00308402c0180c10156035284400130803544607800d0f0b0300460010024044218003c1d0034400820b415280c40307003102034002c0041c1c81d09010380192000d41b070301900988982e9840350410f111075403043da014001c4175605200d03079000491043c0540300c001450300c1e000032044c0c18800040c0c40b08040c160400040d07182000100300c240c0c1d01824240c1c2c008810b80305094043d19280d0fa00c0c2c40d40c01103100e0308540000203d00854410a000040c00481e4001c03207000d1040390303a0b00d50040311403041105c008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 758184775 1250 758183525 758183563
    0xd0f06050709180c030e16030b010603140a050c0d020703180602070b0f090d02060c0a050d1418030a0b070c110402030f010e070504030501110301031407260c0901030c06020f 76
    0x6680700f92941e00802802e901e40c02c0100d2408070742c070111410100e41485980b01441905000e1043c428054605809880141010008207007014041038841c00c1c024101030000d5100d41c0000c16a0074000c0544103801e042100a648034030740c1e49000f034254603851f0340120a1880d66400090823910000320034040726544803001e403038415804c4400f00b42d81d01c100c000703a4003d100040018010b0304d80c4c000608030644e80002030001e4007030500c0c0c1139040802007181c00c020040b03061090020314a65804984d001407040d00d010103503d1003000030074100f1f0404c14020b482041800100100341d5002102c4c481ca00c0e10944410384001180b41c104002c13400207a4225031266200001405202605203426410010b1070401c4c83c00c10380d6942c0d076507007035941140351b0314010100880104104491a0340340b008408620000c3c0c11150708013803816020303912265200c5265008801c4085540c1418051341920007400b504103c0150b8407800c01c6c480d000003d2040d04010300c21040d89542d1410003003845030720a5201c000038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 758186025 1250 758184775 758184809
    0x1506150513080a0b090d030605061917010306151a07021207080d02160902070317100b041202030c060a0e09071106070e0f0409030c020402070c03020d0f06050709 71
    0x200c03034a40104500c0402015418070102c1c1040e02000000314841c45044040d9503841c110721094145403100b50a10203041c1845814801c664074281076440001c011105c40c4541c403248441220714804800c074a03e100190b040000c41407201640000301c02080d10345000c1c0c0c6140c0c0d9207440d0502c0140d80211144050b800307029403401450451001005510040c2c1160511038440c500d00e41001c0e131020603280583d003c044000c20301d0181443c104c3c004c100709802103060062548001e80030b00400200d0360340e0001c0d00000951006001c411072006090700c2040e45450300d07240c182010810394029420f0340f081c80340441003806c5142c107104940c3c104496613560311030809680d090002c00b24014280c002846049651200001c03020010070384680c0440c3d90b884041003043c014410b0b18901021305c64040c03410504800c0109410078064903500364150390040e56124a424005c201e48210b800c004d600c01a1026103009001c00c0030f4035100780303a0040d1420001c9032600c4c0c8040c3c4032135000388600080024010781c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 758187275 1250 758186025 758186027
    0x1a01050418020f0c030408060f040f061d0708100f060312050a2105040b092410090606050315030106050a060c15111b010c051c1413150615 61
    0xc20141c119250000340c244000c8900d41003064005100e401d48035813001c0740c10007103000704108954104082150041c03890900c0c1e102c90f0009a9210805400307140c0364510100340c00c0e864096002240c3c17540045d04c6807280c4806a003520b62032540b000703208a40c00c080c806084c3da5400c2c868001205e90104810308091030b00c100654041d0030000401c000d0044650403400252130b00403c529903214508000599413070503240c00c01c3c280c20701401200403644900c1c269074101e0001707052441d40454840980c1d4285e03036109619002065280c1103021321608003280000d035183c102002c1c50080c190032105040d01c1c2d07442401d140c222025446040c1d40010701c4001001b03030900940000400c80c6c011080c8500e11140072021005554231582d801000c044000b4004d02c0010f817440e81001c802c4d04500090110241c9201c00910174040d8900e11103699480700849a242c44895000c224844400c070040d159034034004084125244510070142c500002c6804401d121400d20700ca0103054545480c1000d180140c0010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 758188525 1250 758187275 758187299
    0x15010b070312050c120c0702092503050c180a1d220f11010c0b0702071a0712050a02161545080f0606040b100905010c11061b011a010504 60
    0x46d40da0703003c81001102d0258540140c030b584659001011081090380743c0070402e0400c0c0084405004041c034000c00d220b201d200074001c840c085000001c3d441908900740c40041c0042c5129804140206200441d01c184408074a02e110301c90340c110300c9943d2010108190358070011814640c014440714902d80c0d00d00c000342c2d001ca443c403018001072501002100059440450300e903002d81d500c40c09070f031001e41f0070024400110300320300190540207003681c140410f40c2d44a02900042510700024018085207900080e03100304403e42100230032406041ca865a00d90000c002d440544008a000403a5202c60102e21544410005070030b1411240500390100312401461050703074500040d0000c451a18000100540100010098440b2800207000f07142096030420049610f1740001358055030410f0b000b081300070b8002952008072442820301282c5007c0130318010075100e960741c9940d64000400b207110000e03044c80fa4850340111311050300030012806000a000c6074500c00e41c41850004404000134041c030f01801c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 758189775 1250 758188525 758188531
    0x50a050307050c010e06040c06090f17150a240e0a050408090d030207050a1a0a08040623040c1721042714011a070515010b070312050c12 60
    0x300e422401e103400b00041c3c50a41e05545801d01071a070012050209104440c2403a0004020f54101505110700d440013940942c40d140c45078056603000c00803a07401c800300511041c01105d041226041d058a0a01128801404449191040c500d0700540301d28408030719013504000d907001c010540c041d564400001ca07001d00030051044a02a90501c066055500c2e480d824a8215220307401602d0740d141410140f01c5040103580c06425007002c0d2001c13240390307054040219041c030001d07454601426511810044003410244401489410078001680041194200c06a000c0c41c412120085441d9544010388501d59042c40701d049640c022107a039040e81c800705585040b081400c4001c050800d80d4500708880a43c07800c01e40100342003034540e0440485481e0344905090510040140d1040e54140303008907855080520901d040d00c2d000040b90028071108000c50701060030303007203165025981c559500400640001710110042624206900302400d8180a902e120307079004c10103d81866400407001828000c06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 758191025 1250 758189775 758189777
    0x6010e0f030f0d030606111b090c0432010e0306070e0102100e07061b0c061d130c030e0a0b07052b060e070e0108060405100504091202060601020706050a050307 70
    0xa01c1c211212442c180031119001040361000583c2501e07008000c0c050301c1c001c08146020750410a904568081d282034200710300142903c1c0100140e8480203400b025101d550000400000005084212001000d4100ea030724803400c03034992500541d40b801561071011900c0391540c560058000500d0051040c070f180c00c14032005204032200d1400d4898400e0480e4105800300c5400d800144060200c1600201a02d200c03501c800380358029050706440d83c0b84150881d001710700400c4880c80a54501403088820111712402c0104080c507840c0c40601020020440316101d50080b83c00d0900d10b0a02c0b820100346c0b507950540009004400755986481240d80e030b4002c050600704240c03448040d054915410411241031311400000048083c1000d00103201864000c0440381000144040703410180d034000300090b001a0240c0d00032600d52516000320754000c40d19040190000c0c03800c4058010310000030b41d9681c00407140d40983c2d0b061340f200c0d401242ca8030020b01030400450010444043c00510030401160b024001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 758192275 1250 758191025 758191033
    0x2006061203160b060f01080c0d0f0902030312010302040509030a0e0607050a1b03030818030d111c02030109061a073c120302040f0e040f0c0e0403120506010e0f03 71
    0x880501d00b07041c842d004040d107064400004210290811450864205000b42040881ca1401c4003040c0e02610851005052250712020603410f94119500000040341e801815a43c441c0c40c104008001d09109100036841141010045800d010700401140c0841c0e00964541d843c52040b8002e000c019481000c003280c1710702c5041d07082d05c0440c43c0f01201030a04000701c0c50010001f07245080040c03108201614030041b40c4016000e103070942e0b6000003110400c5035917090103e04600c0300c0340002e00030f0080c5605c0d071802c1e6405a0303040e2800281e550055050310b88418042203415117a03442105040940d2035140c4131035001b000303000d02080c08030f000d429010741c641d29584081960191a0118421381505940503459903504220401541d075401c00c690a040c0d00c0d086003414030707046100c81040602d21540800076030740e4000c80d06005a4541c4400d42c90780101c2114515030b500c0c00c0022071020115415400101c1403020a40b04107000c0c06224020007050b564106103100000400205911801100da4140300b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 758193525 1250 758192275 758192287
    0xd020a0e0108060103030f0f080727080309120105040c05090c07020303040308030412080403020319051204080903060901021602060a03092018040f06110706090605072006061203 78
    0x185a1104038082d1003004041c100300c0d40b45280103403074903000038106c4080c06003071207843c0c0c20240d0200405a2003082441c2c40c01c03440030742c01034014440d141880c2d014040b43c0c504c040402c449070000002c10075a1019910049150900c1000c03508940c0203481c01005280f050307408000518290415680003065411070b5407502800d0350000b840d50340b0681c002c0701e0046001c8100414050446d8510b070459619042c181250700d49603500075141e2284c064401155558083c0c02148188200d058804125060303244072401c0c2454109503400e0740124004520034441c14000031414001030094500e09848240f007401040d900750300308655038204e88000d03010141d4901da881c0c042a05190070490310036003903600241403075100303090040840039980003140d0b025159040c40700147c0351034400b0310010740084000440d11800b41c8a0681442189000b920040c20140020140406a4001e9000c1e44141c2c6a036880403803040f509030304604034212010415000103001640504203140741c0d001018990b030951349000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 758194775 1250 758193525 758193539
    0x2e08060109060906150f0f2c09010f0f05130b090a060317180418020a08030d060905070f0c08130803030a0501050111030a0f02071208090f060a09050d020a 68
    0x2500341d01003454151a400100701d2000c0620403007010b8081c05101d0821200441c0d0080c1a0520710301004041201c0b40c07041d46403040c82180c0c2404004c80401301a001141c595158020703000110503051310801c4248000601c800c10101448222001548040310080c40c0904000c0089220079440c130681e81c4905003d0340e0356a68188040c07242700044800160141103080400a2400c41080c0d20500341040144007040c80e0051000450340d10304840200703000c000516915403440d240b0500030b4006030b007041c01289142d4007001425800188980c1040368656480d01c02c000e65006480c080301144c43c101440c4107403403080042c4154030740100c3c03000b03107844000610001d8400e116072000790b1a03000032041c084681c80501075513004180910300320007000116900a0340f2440b070041118280703c3c0100ba030450040c000e2000c0e01c01000b0300d103144804042c2e9420b24280750740c0144002e5100392001c1d80380e0020341c5499819950031900c0c03580c80310302260601040c41119030400e030059a0000c00001c00003004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 758196025 1250 758194775 758194783
    0xa0b070311040602010e0c010509010516080c0304080303070215010506070803090c03030d0603140d050f0c07051c03030c110d18090c02030408060c09061204030c0609061b082e08 78
    0x100030513400050600e1204c88a14204445242440e04002c010013001500b071380e1040136200d1031961001f41d8081c0040f02d291030105445503916410325404049400207a118010000e50f200b0b000380c1d02941c0c20840c0f40390400c2d0450009018181e445841809104040340281c0003441d405081303001110000d0306003000184c615046501c1c07407074030182c41341c0083c010001a499000d0340f21041100412a0100302c1d40d001c2c00380d0081c1e424100c48035101290113024804208842e000800000c0d101c10f01051a000701e035900318030b070190180c0210741000b8225403c036202d81841180421644041c3c106468040401c43e00210590403502003e00d1f1050007040c850214481c5551401060f002180da032447c05401d542400d81c021305c00c0344008001d100c4225030f600c1e2001203070040748842c080196540d0312440c0540c1c11504170803001c0d01e201e24040156080180c0c5502411020305c1c0f10503c20700400040b04200d480b521b081394905118261703560749491003500c40c0a01c404022000205401c200d440c0c3c04541d00d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 758197275 1250 758196025 758196029
    0x1b03020c0c040905100c1d010e150708070b060d050d0807020f071706180c09040218100f380f0a03020904050a060303080f0a06150c0b180a0b07031104 66
    0x40e00b0a81244400c0e0007036104440c0c040f122030524147d034510a842840c909019015440c0c1440340444120085581e03600d900e03100070041901c01da0b00d40b1407130f007440400c6401c0a0b070115009009540800c0781481d0800b41502443d501000500210070151400c80d450b50000c1c0010741503101e10700e101c00c084101030208030090400f50b100c421100e542900201e1801c9400380012a10103902088901c2400d00400c1ea69660380003034070190842c3d104c5101003010395441c00d9602d520341c0c0c1c0f031005003c00c40c0700060000e000c4a09000f14004416291160500311009180868031900c41c03015035480c04004c0c0b000701c6407052103601404c508008030615080000d82c42804030340006540000c25901c00c1c94280302d80e5810035942d2004102e464115a80941074110150090b440140c0110020780441002e40110340601002c40c260004003004a0014064042030441140c0180d03144000aa4950a0701105010387c0381c224010683c0e4840c68072410071410740038114034109034554030b004205450303034402480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 758198525 1250 758197275 758197283
    0x3050d03090c3c05011b051e0c010f140d0b040b090c04150207030c0e15060c01060305061819050a120e012c0f0f0301060e040b09011b03020c0c0409 65
    0x420f40380f4000748096400c5003c40404024420480300348a01d0740c0c42404009010004115041005102d051480c43c21134012901544400008403070090054017191314810141c0c00e0f00e5840300d6504060301034a031100780d2800d42007021400d202d1400c110710703280c00a0004035000b03400007d40340f880d0004103100a6003240d4400703100c940042c08100d1440d64815400d050a494800b80c40c80390f0559440c4880364083e441804034184450300821052085440807412500c030040000b0b50b11000d4100281c081c11282c4802d079401d0003000001103a003400204043c0c00d070055507001d000b07000f0220300d030b5850380c14031154156203520403154400c3c0010407850380c040792002c2540f5401c0c101e4015400042813400f211600342c5492568031050320340325034025103031a1800400c69642045559080100b4100009680b1303481d819030824200141282d080e0030441c1c003840c000d6007076010541c1e0f0904540d0985150359104a440c022032191440c8140c441d41c00740c100e00d0300c2c1c8030981d2402818100054107440840e84180d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 758199775 1250 758198525 758198579
    0x2120a030309170304020f0d061b091505040f050d030c0b0f0a1107050c090c07080301031b051c080d0204090c2c0d020d030201061d071803050d03090c 66
    0x10051012006a004141c500d074200b05107135150a40c0460340011044456134010000f590000e000c01c89180c00c00341c5400da403451562413002c040f040042000d0100d205640055056000700040607101e601240c0990b980d803449034810a190009010140c00b114030305408101400030407000041c517103803003940a070043c94500320041c01d008062a04a5032058070036000c410b030070000d4600251000c41c141c1c1e80f500c0708483c490f40c282c5d034488001c43c492050800c010300c202d10010002c01004905030f5043d00001c103003000c800d4484d4a8605010706074160380b04081d03e042c01d40320750700000303000d8100910400302e01d07440160a0642d0f951410041c2c0303102d2400040400c01381c1d61409050120610260f01d0416002c0200384c1002c40d010101d109480403c00281c004c1d44508180c00c14903000350001c1008040c07040c04d42090500340c9000700131880080c0c840100280020400f40c3d00d0f40c807000ca040341170ba80c000d0f014001041001c4e0042d4000c0228000848510048000004207030303502400100b540700c0c240100c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 758201025 1250 758199775 758199791
    0xa050a02040609090308040209072006090c0604180f0207060609020c060627060301021303140f01090c050f040f0203010603060f090203040317070c020a031203140702031602120a0303 80
    0x10555180741c00064840d0304e00000d0b000826408154550400e4040c2c1d40003049444102084491100e1206041820803014000010a10001a40e0f501c1448503c058071040c0c030404c820002640718501c29207418044003a0a00302c0d0740717078961110348a05c084640043ca0203085545080583d072465120209556002c580410319000134400c00740d10180444c3c00310a00f48241c3d910f00e4260144541c15200d8000c4400003c800c2d8609504a03101407154581c0c00c4209a580c0c54801a0259130840c600e006000d1186560b00401d01400f544000b640c2c042c01003d0304500f4141800180100d1001d025442606c070011050f8000b0f01d80700550181205070760104640317007400600000415113520049035588100104000b00307502101c001d200c404040f8003110303103844905003103070129a13600c3c000e0340c0308a0b650030010401c44181c503401c0440c203c9441c14009500050040748241d441250b111015030070030440320031415500303a40b49220910043c44030b40340f940005c804501d89480c4c5882180843c0c2e844c024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 758202275 1250 758201025 758201029
    0xd032604060221101a0706020c1608011b03181a16021c0e1206011202090c0313021302040915081606140306130c020d26011a09030a050a02 61
    0x40e005100d08020024112410099400c100c0d4040c80c1c0f0504c00c003105100d1180280000c545c0c21101c07440d40000c01907450344041d64a00c0d445544074480d14200d034181e8800041c0544040c003515800242d00f003824400002c40d00380a030003806041c0400c00001c02009084c10020b0851200200309034002060000c01e03240900c14001c480c024682044150342c0518014440d80c03071561200c0c0200000303480e003000711480c240301048031103000400b148540d024200012610300d185045c00c2002d24000c56004180d41c50740c50250b40c0601c800d44031042a244200d59140142c105048240d0020400150061900ba55115848225a02c11b024610207100c10107082044100804c550316a0740300008440d20035602c0c002d4050001d09119511750082c0001100042e280d5403980c0e51100c1c0c1c2964958248400326150000a4554101481100102d41c1091818401c0d0910300956140e030341e2813000e904407a0342012814907541801c0c0329072180351031040010712000d4078248050121144604000c010518032441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 758203525 1250 758202275 758202307
    0x20706050108010c090e01140d050a08090f010e030a12051317070b0a020601091512030203120c04060e06070807051203011505091e01111213140d0326040602 69
    0x10102c100019105c080c0200d1414017005411281d40d00c100004081d91840407521301c000074000034010740101c03090401400027a900074560400c04490a9031108100c1c0015141300200140454140e802a1984400a2110322898940c203003d800c01c2814404840c0400030103010582000b0503030001406404d8280604200314401f07068410101824402c0401e0029514481440b4046015407643c00960b03c05c0d42c0740420380c4c0078040e08090038030142442d09020396030364001f1011182002c00da000240040c0b1996090702d081c2d858179030380c0d00c40f21100d941c00c010858000120644035a4020420440050001c2201d4030ba2440b4908181d5102e41c540240b046446900c0d1408000317020041068000e07513034038024a06105440c5d04601602c0244120040300e00e11801c212241c16449098002c4c80742c03d1000014090720441000c0c4400c000380c175481c8040300c030514200166040b000d401c9680c0000b1b4043c2070080718103012042015850402c0280444080340e003520b090f00c0c8207900242c14087e03550409 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 758204775 1250 758203525 758203541
    0x1104090b0f03010b0612070c0204020d0e0d03090302060a150f08010605270103032f0616023c0d030507080a0e0c010305070302040b0301080328080a09020a0302030102070605010801 79
    0x20000c02910b0f01311804550300b40700f00c00c0316108100000c000601564021400103286a40140003151500c803142c605178014688003800c007109100c1d04410410030b80c460b029401d01540e040d4050401c42c0c445062103005050280d9a8901510702058049100510f450604000700305401c00812200e141c102031001c8050030503c100b80c0127183e5014071a8410030705c880781d4112641440c2541e90b1403000ca007203102e6000101b85060381e1040ca10201c409524001075414080d241070341d032641100e2006041a039075071598440d150111034882900904803110028040d0401c4600420b07c0c964a0518030800d0624103480546000b0940e91410b1041090380000070b0b50388030090000030031000781032241040d560b1201c000034504241e141c070001040d45200c0d8054a000b82031104540e9203950f110302142d6125000784c5c4641034603d40540000c8180ca0701c1c00b90181c4a44000d84030100d194a41080034000350000c0700042e88c03c440042c0c030000040c2c40034030042102c580607410004155040200050940b0103c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 758206025 1250 758204775 758204779
    0x602120703180807020d11120705010905030726010e0a12120209060304120e191502150109180b041a0901020c0d1214130b06060403150504061104090b0f 67
    0x2c1c4181100180c0c0035021aa8866012500d00030680414030f054400034100c440c40d66040b1800f45100b2410440c00284072060320f03000d0301ca03081169262000d05954420b07921421250034040202d045140d5080c543c241d48419400c030000c594011721070556860081402c804071441000200c03182c801c0b0345e2100042001440fa01d0f410b40c50402c140e0000b4829000142c00a8190700078841d090324180e0044010200300c0c003014080459810504044906100350f40c0304071800c008403410290000c920210318000d5a00350340d0201d01d081e9081c0035060005100d00304018a120341e440114901140340001510300c540c0c0726400384060001041d4003c2ca100101400d0807405030b00501c80e4102c8010040b841890b020103d141416005007080ca0100240001580c01c0002194260610003a070300700c1c0701000d0b026801201803400c40e848480c18040700d0310440c4030150503800059400b92245055420013500700c1c1c0240c0010407071403c0c60306031010707076442a8015032040303507144d484100c6410640540d900040c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 758207275 1250 758206025 758206061
    0x1501090e06040b12070611010f0c091e0f17010e010c020c060f0f03040807120c0b0c030c09041a0a05030304030f12051606021206030d090303050d06030602120703 71
    0x5054200340e940d40010308014812a15403a003010903840741124207000c0703480041110b003030f10b9540d84050041060031001c0f000c81e500b4054425240342080c02206448000f030740ea0181c400303161500102c022204c940962000728a0080006a00c240b05620580a000c8154100f201010840015402c489030002c4400913a4100041103a0454001c216940001800d440c010342e1917000142c102030a215404604000d00c0340030040c1b0060102a5014200c02c41c810000c201402600c2d82e41510354648809000f094035031100d00140e0450202c0c0c0c06540c001981e240c1480c10b110032071000a0645000024070245001d58072078901b218508820984014070b03051f0003a525090650300c1c1c0350311144950501a01005184c3c4054210511503011102c81486014402441c43c0c1c0528045010f5445850420f0380f07040100c1c00b0408a25000c200f2102d0b03050142c444040c17461071641c082c2e440f90451000888440d076070f0200000400d0981c001413044040b0b0700d0001206140030240903003101c1600c0b05050780110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 758208525 1250 758207275 758207279
    0x606081e09101a0a0e0106111b10120c02150a060b09060a0507150509060f06010e04050405010612080c01061a0f0d1d0607110f07171c0206150109 64
    0x45009200b4204904002c00e42121044030300402d406005541e94000c500d40784001000c07170744074011038181c2d5095a1449552285e0042c0d85543e14500314a101003012410100007a074940840a2605114a8100024014200c900303060465040c0c0d401c02c400360b0445404140d400d490034100300d50001e5000e00410420b4103202c403015090180481c0c0302d00a01b400155080e1042c001c0098070700180e44100201014540c103080c1a0181c182510484007502c600f001080600310042c01c224829503040e928000c00380c410200b044058607011b00156041d545e02c400105004c81007400a229031401903504903943c1d07019110303041c212001507010902d41c02e05804000a008104021940124046441a40c41c0c0d48801e0201004050441e000110300c5407059511310b0026010440301d104034820b81b40c41005034040141580ca035440d4000440650300a12403d0042c1c2424502d07005035581010211007440d06140864607041a80044141c00360b03010100f00980f011100140549000342883c020010314 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 758209775 1250 758208525 758208541
    0x90601090602120715050c0a0f080c03060d14010c030b01110105060607150608010c0905121513060207050d0206010e010b070b0c0a210e0709110406140d0606081e 71
    0x104003444403010248006444801e01007100300328020f0b007a07095410006d60900300b820040d260300c40c035900c00214114441d1108030500490807144151456000580345554100c10000c9a03080320500701e80303403080e5898601c0c082030248113007048005c460302c0c0014a481203500160048442c0c00310041107a040c1400c02803107440340f1041c0c9000540c0703c0d9001847c0e019010704140a0310058100701425032916101c02c1d00d80390310000e1136041303820558001c0c41040310b45021507141c0c1d0990040202040e2044040348512580030744440039a4004c500050410b51180c1d05e050600c4003400070030005034000c070014400c0c29000c0c1d011300e0050101c41146880c1040a0f999610341c0034005060702803001c0042a0003a03201d0140105224a48144080e114160080032107400101588511401c0324850f080021172059501e2113403000f000b8a04501c2405c281c07800400704c820342407180b8003402c62803050243d2040d0500b2401000054400ca8a94078400e00d403076800310f00e0340020b60901d100190030510a00080d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 758211025 1250 758209775 758209783
    0x6060a1a120c2106150309120f121801230411010c0b07020d0806060418090809060c0307121e0c03090b0a02030d060603110a08131a06090601090602 65
    0x300356100e0303a5089542c0d91401d428441c1c000d40c440f036088040418000c1020581d0340c9525485244102c841034201440141d00d0801030000700c611038003036400701a4860007080d07002d0291110110042000e4a04004250f41c0031002c032050350050800101003130741164a500038050716888182006481440700780e0840301e102109000780c0050111003609500d43c4450344140c0440c5c0002d50012920b090758100114020b68450000b1603050000711414089045031404070112811220304a207126100c0350042c03030f103500601c0001011140070710700300308218103078855402074400205648040e64851040c1d092590700d41c908010342200300b20352550046589910748502e42c040c581a480e201e0100941c500d401d44040300f10750409110341d8004180c14107129030010040c516203100400c20300030507a032503001740c0c19541c2c40e000d820345480003070000c0782e1a42d22a04c4596800310b1000c10302c1045101c25110322880c617040c110540c0f2504596001c1202c0c41c02d0401c07039690001002c0c6002e81c40315140c000000c0d11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 758212275 1250 758211025 758211037
    0x406080607090e0a0f0606080f0906060f01140d0c020a290103110a03050f1e03071a090a020a0909033009321c120507050706060806060a1a 61
    0x11800005002c12403460030f580c080000624031417005c01a140c0c03100c2010f4078001c422950f228017408504001400404003280780c500850740076012040078240e200064900480c103000f0141034010903c513a50701d82c91107000d1080c0408d001d801508a00d003050501d10842c41440480d40040c00800c55004480c5142032403290440381c014140c040f00503200c100080c02c01c01f4550014120f84903981c20070f07180b40e03c041b4481c00f1801e0f54124604c208801c0219550b01c174042c0102c0a000442400c180d0303881030951040083d48910510182c0e001c4000303a03800240407074869042400d0942c2d40307030007940030141c0103881c091200001511440340303040082410582da111b8a4000c80e10036890f81444002c0211040158400d05020705070514102113a10711110580c01d52a50300400340b0858100840d180d0801181601c2409240d031100000c0742900a002e01820014001c04100711081005402148280c45900081d10121002e0505810110108200600581c02003100d4407441440350403140810012104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 758213525 1250 758212275 758212289
    0x20108010b031b0703021f060518060f0d02030f16090e0307150c0c021f09051e0103111204060f05060a0503150c0405030f0601060314090615060f0406030902040608060709 75
    0xd600c1c4c106113400c03802d0203800031440010300c41c80e90b140403480c10160044000d880c410f6030540b0340c0e27481c2255103150301c6e00140c5a858224500360741c400c1481c20300894510380a0b001608940c0d590054100c0180b90035910b00009890501d900700600000e00c45004d0f0102415084004504022143d203c1460f0702e1910b070369031651295144a44030301c0d10300561511100c907800a10b050140680700309445010420305020000044440310040b800e4036084604000c9051403911000704461310f040107400401031048880c80c2344400703100c103101503240f031020f103881107220f4040402c1e1001c0303450070b02050350000b030605031168031821424489610000b03829629503511070284400364961141e03c4516100707503007103190580981d5a0004044000240e403034120360055900b00101104042004203540701a118607255800c0b880106041502e0450b0000700140000d200f07901d000d04552503482d807548568004c402090306c4280780c209518091040c0340081034484061300091401000c000c1042d0100d0103003003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 758214775 1250 758213525 758213527
    0x702010605040615230a1107120b0c0703051b0a02090f090d0e0a0f0f080709020f03010302010509151b0601081b0d03091d0117010c08071d03070b0304020108010b031b 73
    0x101452145001d050101503203000100c0c3e1711400140020301f40c1800b807609107039910030b117000060131750250301150511641140c1c0700301607074846008001c4554080c0c00281c04110050110030300110f40703698401b003007400d400018208400580306209030340300001c0207014a088070f4010000e288038042060401c172030702c0d0311b0941d112186680c002401203945400180099840740ca020900c0902c052043d03082d5000b0f00c0850320910f943d00300b400180d00c100c3c0c0740c01c00b42000038070041006500500181c41070a20051030901c008181c902114482e401c0346224900d102901403600d0b88011041c040c6501506030305014003181d40003c60303002c0d01803d81e03042690080040768100410f040c4140c204101030000d40303030200d41c6460800b101440c00711003802162a0310a0540840e80428014482c100305948552100a07041c1e444440c16540b111a0b03100011b09514200304d900720f540c0c1c2c103000c0302d0064035400d11100e03100d0511380001060110140c00041e0000001c005200c90000f8000c0d43e9000202510191 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 758216025 1250 758214775 758214797
    0xe1501020d05160b0106030c080a06050604090b0414090d0e0603061f140307080a0b04021206060a0e12012a0c120908010507080105010e0a050d08250b0702010605040615 74
    0x484483c41000350041d09102040c00007040c6281c0c1500b06004418095035911480d4480111001c21980c6a102d0a580110200301c20801710100e40c00010ba4450010400211210ba030100700c148000b04507412205508000c0454000e0764104e1712a004a40b400c0d24203609503d8118042904c0094408001c4410014400c0c042e400520622000708094511341050392a4205054041c00c1d500040e03524030f040500f400d00900903801c191007514100e01d03402d403045d00310703440b440306102e0b03a980720301807450030004582506526502c0d122012407241056000010342c000d55034000b241c4100090801000e03115040350181c442e298005002180a5089101c0d1103140000e003109540144059010030259400c7c5130810480603081305c0940d04907417003a00c814a041100c14108220484c1c1030180e583c4c04010442110b0205e107446020700000e50551140032065903031107c0d0031000004e0322030700f00c500710300030381c100000da90b428019180240820b41c1e051281e2414107901c03207004c141210000c020814030050b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 758217275 1250 758216025 758216047
    0xf1527080405030307030f02010501050f030d1211041e05040207080307030c02150a0510051516080705014107080a0b09070c0501270f0c030203160e1501020d05 70
    0x40794010400141103d542d00c2c0c40b454080d00310022a05440d015501c3d103000064142041504000c210300010040e0001186c0d041d01500c44880c10721a9102403a50355130540f0130848188020000303090740c2c1c40189030241c00382c01070500c1c2e481035030001d0b400340d401401644c0015000c0e406890700712003182004603d411074440101c3ca00901c1c80c4544102c1e4240360b0074082d4602d420b0780700500403280310803015081d40d150410b10450032403200511440400c01c1000c2050135821488200910348286000c92030414203031102c070300791440c048003030142c00503028004050840c0c40360701d1118000f220309402d0815041542039440c2e01401011003040c0501040011101c0f102a4450503901c44000c083c4c45c09400c02d40002011185148800c071015807810041c102c1880d4907004038101501d0091a5a040100b55507074440180d03580442221019580e0b1800300059070207014280c403642d030002481d4052460140a51130b403003809001200078640c0d207106d045103a40c1c0802c01c2d101070b60380c03818a03558034400444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 758218525 1250 758217275 758217277
    0xf1905060903090102030f1c02160212013b06040302010c09080c01050409050402040207020306250503011208070212010e0c041112010e060f04140603060106140306150c0a0f152708 79
    0x25023020300751001400f00c0b402c45045484054a50098035807a01402d40344094a00303d1302c1d849400021011031104200c2440d003001c200c02221000380b0002c46810300c1d24140d02c1d185c03440507901140940d44405c0444407142c1d10015550003131000c0c400500701100c0050029049129500948456a440f000000d007591610b404507558280e01030201c0d400b910b0b0050b0650350420400030aa43c0040000c0c0b03c60150b10b20500682c4c2c107880c0035000c224542044d50b520b440306030740b04042c200d0300000000c0d80001016400c0c0302c0e810203c184070300075010b6031541d142000704030390506c2c41e11002103a00b48040d10701c25030011501070641d84000b00886981d1648800a01d40002545111340e000381004090034a2404100c1040e0290340141d007142c0059807503010913a4444036402881340742440500c0040c01c60324000c40c0d00c401c00da540c0258a0715040c0d80b4107809042150303c1806803904454010448200200c8180590b001a0031032010410142a00b902c060b03d0000c20540d4106410440022402c3c842120 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 758219775 1250 758218525 758218567
    0x4031b02130e0105060607050c04020901020a0c1401170121060f0e01200c120703050d0c261012170a11070501020a0f12020f1905060903090102030f 65
    0x104503a107541010208840030b42401000100d00e0f5003004081406805c20809481070140d1103c00f400d84849201c003403000940101404a0441c03003000703400340c04181018410000b6102c81950810303c01d0032240094101410750841d4002020001d00400004048402c01085680044040c9c0d0361801141000d1f0f001d04080c0e01c1803903099242180d00180040150710104c40d40800c010003041d031030b041821952513805902404c3c00345422800003490000a00b1006215151181c24154101805100700700c0840c0e201403159808251004000c580059801003103000410300c0c3d42c1e907903101c0e1800b149a0054500584500703210210014100e03000c00c4430507140340366450203031643c090301c0305292480107002c7c81804050340f4003806400c40c007162951002c150014026007007111825030440c2d41e5500c8002d56041e0a1490450103282c0001032800000c1c841d40c01ca16140040704803078107031390341411742c01c0241c05403100030740c0d5004000045030b07a40c02109030355080013045103041d00c800201c11803c441141d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 758221025 1250 758219775 758219779
    0x15032004031e060e16050402040303080c1b150618041e020a172a060304031d0414310215040b1c2403120207080f010608010b0102030a0804031b02 64
    0x904190600340c0001003171400c821034194a0a611035907913042c00128070641c00080d00044034080000e8203d0170510080c00d8403603407503103034042000c51791400500b091011645080c41101050a00c1081d14003402c01c0c2c0381c05002007040319554100390341e80502014035514910340b1040c0c804001415990785811b503000610404d1a000c2040680e000a180c4511941c04c1c2804003031f005880700303800556404001c018018000e8040c51440e100d0392000d941c848030120503c842001440d100f480191a00e001e050000100562203481e18201544140c07808101c14030750100c95200e085181c030b00c2104004c0c007001c246406a4030209000154004002207203d13136004102d90150010b05481910b10000b1b0001449030402e00c200b2490b180d1440b02820307040c0e00c0032000005850b000052001c603098814800600d100e41c0101c40519603910b0116040518100709c222080c1d41d07410080202940130300031840b2100013480034618002402001400000380a000502040141c1146004092500c42005200e90300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 758222275 1250 758221025 758221031
    0xc020c090109061511060a0b0621070305150901031415010b040302010810050102030315040b03010c0c050d0f120207060908030103080307020f030c0c010809120415032004031e06 78
    0x54000b4000600454442c64038203002c0b40c007444080710f01c00c3c0f0210168440c601c1c090841c5880f0001e2030800381407a0082d142d4030100401824a80403012447c9101c00e82940c820191140780001c409412200e00814103040e01080d200c00c840c0c10350714200310a0550707030700001c845444134005060b5881e2020140644111540660002c5840c500313620161040303910036130318540e442d5a944c0c950401c0c150789108003405039100f4008210540003401c1c030143c400c140500b00042540e07a0000003802d50b8045174203140810181a81e2a041c0541408004101c0546040c900c0c1800d2903101c008081140010602e004258082030000070805503410001d04290413004082c3c03203584a08280345141d0081e0388050151080d01901d1030303194804015a000381c5480c0300646000e119400040d5584100109a2030007030251303042e500c00f018103100281000c0c2c204100c0f43d610261100e180502245e0600311820f690090132982d881c00b04100030704039003d5075842009885400007101c891100c0c1581568003c0c86982 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 758223525 1250 758222275 758222279
    0x2b02040e010b1804230402221a1509090901062c0601020a050309060c10020a09050a14090103170d050705030916121112010c0f080a020c0705040c020c0901 68
    0x180b0360203481810a0f855010070300000f11002c210840c2c01c000500e0400e00c0c45929103078910b50154400c1035220780083c0003002103000701030500d641c4078103100c80200b109036500e00300d42c0d28907640d800c01c000301d84066581c02c3c001c401c001000c404d180a900107592040ca10840085d41800080d08000010700380c4514903c05030185045c0c11203280d01a0300031811b10244240014140c4d0710010744a010035400c08040c501e0004030034240102c5d0340c807050301c400c2c5d1441911524201245c10388000c18000106a40345c034441130500041043d050a40d038042e11241d151105145100e0b5070741c805140c11690300507500c4420000c403440e007441c01d0240f200c043c0245071a100c100a03150350030400035407280c110f40c000d8034815078500c03600a4242e1500c1c0165000900d03000c0b859030003c0e0b203e40700d03169061001084e2000d59000c40176041d080d500e103400e02100160001e41001d07440d81c0c014030425084644500254102054088107980e51080d40c8030b2a0b120f545c0300c140ea2101a0f00a0222440384200a00308503199a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 758224775 1250 758223525 758223539
    0x90203040b091b1302122e0b0a0c061b09090b0409030804020f01030e030d1a15070201140f040e090607080c0a0c030915110708032b02040e01 62
    0x2400450342507903510034030000560320b10400326030248a0340d509a4460184020003051107411340044101451090b400c00058141003041c0003428480c2484081c910038074510340500d00c2c006081c100580e24010800e800601c0700700d8121068031548403c929260f01040000d04000014040b4a0503614000c1c291100c6102d01c60f0340983c0990546445520a000d5580e21f44207100884494000c040d00180800c80402c00519010501d029031050500d00070071203024400d012401d5034810000da00001e6a41c102e8200e8001c0300c822001b82d01c2030b0468102c40307113000b4031040000501c12840d00034108581e0304000050140554280c1305030705c4d051140940c99685920342040c4001c416105854180b107038000280040e0300ca5400c80e80f155034084551350510350303005410b88141944900842c144031840c24045004c09038850030001c00d40403640c4221107114424001030500100c0e400508060f0804c03c0748144044054880c00c4083c81d500740c07980c0303645031079001c03103002400750b03802c00000707600e07040d0000440ca = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 758226025 1250 758224775 758224777
    0x15110406030518210702030f1e0c0409020907030f151202012a0b0c0403080a0309110109060f110a08220605040e040b0703020705100c091a04050d050a0c0902 69
    0x66410180f0010b900220500c19598407080c0601a410600c0401c00b05643d0007105009410b0707542c030180890704072040c601d000c1805c11a16050480401800d620039800305079003041440801c0c18151810001310903180c010403602100105002d09042e110301001d03800010341e60041025680b80c010000449442d040c4075800f00300020402e80c00a50111080c0d61902c1030310303000e4400e0069218009000280f80e644448441c1001802c0500d510750500c00080840c01482c0100000c4240d035800080007845450464000140c111066040203200c000500025400110290310b141c0d55041481142190b07140d41480c201e207044000f06180c401240350711a1041440c0240c1e012504070385186491910b40c5001c8405018604c03903100f0028110021030b0100301c0c07500502d5002002c5240151038192141c82c0c1d071b8641050000748801e1039540c3d01114070215401042078014100c100d8080940690b0700d2000c0a490145000702449006503800d05801c204e0104030f007040c0079070301005e0621003941c4c4600704802 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 758227275 1250 758226025 758226031
    0x20a02040509160b0906031803040801020715060602010e060a0e0f030c0105090d08090a0b040f1a0f0105010e0102150c040e070203121003030f0c0318170f03070b0103151104060305 79
    0x203100e51a9021461620060030f448100174082d24090550313854503480b103d48688002040d559000c00c100218140340280000c1403401c0c003400b000300c00c1d0b04030f082e01c21003282da442c0d101e0021640f404003120030740724000c40c0d01034203c00441c002051100c1805d01382c40c2000007101f4641c1a0b072200041d03e48940c4c50640080744560381d118161110000a0b02040c0c580a20403580007020340c0103000c040c40004e69501583da040390140f44812080429540c0c4c0845803c00000c04d0b2003084100c0003004046800c014070640500f20a01e03003100e003c03140303600103940d81000019500c000c1c0d003248009556200800c00344e800a10700e40411400300c5c00c00800194403544140c1c6040f162451980c00201e06200d00c0e04041c042380d50540e2422003042514008960071112240c0032000c203c4c01070342c1d844001c40d20490319009000110340c201c0b0414240c01c501823801c102411580c01d1a0030038040343c000328103017147d418112504006004080c103114205280108108650402d4090007c00e01082c007a900d41e2181c1e01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 758228525 1250 758227275 758227303
    0x6040b27060f0a09020d080309070905072d05040e061507032319180807081515030606011b0206030a0c1106090c1903060c08100b0408060610020a02040509 68
    0x345a161554110f0981e549510040e401000211000001400800041d03900c11264419a800b082d02d50028000362281610403034005400c4698a12050f0003094841601e00580c10b85007107683d5074050080c1007030080d0300c2549203a4000390000b40d1261585801c40c50341802a40b0410b540b070000d890040d24a400c540c50805803500a17090940c880c1c040503080f2180003d11500d255408149283d003119808045410524080e00c03110380010a0301c401c1040401618101000d00f1100b6441002c40400e114024a600c5d4020340e00220b04c05076407004290b040d0032180a19210060510300200c54244401e114002908038000004001440741d541d404404034681541d503916070207105000141c3ea03034078150b0b001328090704808510180b61420b01d039030f0000710f103040f501013101941d81e0b1100b10031600750341c052801041c0d1200400400801e0021148090000c0d000481d041c9818a05003640c0c540d00100928051810300034110134030760007000568006640204140700614003010aa501c079611068624 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 758229775 1250 758228525 758228551
    0x4150e010e010f03150507021617010b0d0c1a120a05041101020a0b22140d1e051e0708071109060a030f0b07090e0108012003060306040b2706 62
    0x1c03c00500c110000422a0f130031214620009603000086801001c1c06000030302903110307031220803d2819a0741c0d0038000602c180801d0048600364803003503a00b0741d003e04030100c1c400c50044400c40d000a8205010609940b4005140703907890b55819880c84443c8100015202480314190801c40502c180742c100c24801d134481c0e5440f00d1009040001640d0f10481400020446000035000500c600da60710084441e47c1c0c102c9100481c40c4440b03807510181540c0001c0e0f0032600342c03c4840600c01c2c40e600007410b114480214041c2c0740d000602454001c0a03030050360424606410300f4004c4d002c62944400c2034505a0750002515540c3d000b25280c003c694444503940140560b4020000480500d0320220410849402c241851000c406a070384d00c4e104078000401c20800d100011001248914030500a40c2c06407003804000660010455084134418000f4403005020402c10000c2204a0724041000c540055006c00058a2620360306482040022107001c400e001d030b0100185824400400640d05000303e201d02004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 758231025 1250 758229775 758229779
    0x813050f071e0f0308091e0d0503040806060a1212050d020d02090a0506030603070303051e03091501091b050705011b0e18040507030b2d01081606020601050f04150e010e01 75
    0xb03400b20031044c030015000103400c0c040c03e05c00d810600b0b040c0c0322207059100d0281031110002c00184624520b010180c0b0a03502c0490280422071003008001d8210070101d8064640a24001d0a002220840d01d001804608075003080302c0300c3c50040c400e039180c51501c00402e54541d092155000c00a410000078980305a02454000540d030510100300da000d513001802600c0e9603800c41e14251850780c4124401c0562045c001801451103901c080954085d102c844087c104244442510004002c410b8100c00c600074503111012214a50b109621039420318103040103516803003e4103040d801000384030380c50b0080b520700030480c1c041c1503031003228152003050442d4100810100c410740240c0d14001120001c04030380c0103100500110b2042c1d000b6540c8103140207600848041e050501d041c0c5004c0c451104070403506440018441ca0308103010100404084034512207a1918044000307507188070600c2194014080c003494440c40d030300c40f80c201d480903200d82902711003c01d43d21144004c02100034440d803001c9080b02000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 758232275 1250 758231025 758231039
    0x4080a0c0b041437030909140108060106030e0a0b250206071121091c030815030d02120f0d0608030c070b0c030706050a06170a031d010813050f071e 65
    0x4007013100074a030000c42104252619030070071000c1030601a014000c1954001521082074000c080251000d031780ba894895243c04851840c2c8070301038210109041c00c045428500e818001104c5015036081103403000c0548441841d403199210568090341051407910003050f0590700000c0c2c3d2401360f4050b5a6111014118198594032812280101c040c80025050940030507000c25000d04aa00340c010001d6100001d5006009102c0d416450220089002e100411401d40c01640746803012140a601030a03001c400320301c00a4944a000c4c01c082d540c0000800e980307920b40c603004141e84103810a42000c0041c1901c03103280e00d5894004100390200c510814a010601c04c40f01810745800360b440c4001035040c01c0700c0b0391f2000041c0200600d081c00a5030340700e50029058008045032040d86034818040c11405125041c001c100200007030701550031030000d0400b0201d0343d1380420115031000c105d200551903600149405410945a001c13001c1040c890b245010410702c4c03520240e5019904440b80c0d1005059450f88 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 758233525 1250 758232275 758232313
    0x20a090e130c050607151a06040807051c080d0e030f13030b0604110a260f06130e0c0405040618030f020d031802210304090204031104050f04080a0c0b0414 68
    0x400070a045451641141c0c0c541042e000294200c002a581190401f0384e074020901c150031552000e804c5d684400c40c01c10490520031000031100d0564a90b003101d6070855290481240b0170014051455651400382d14801d039806d00c152402101304000c6560350701a44842043c0018843c00182c0c0d9403c040004038a00740390502c646100070034410b401604004a104003561031465000c802c0d2000728201c00202d04505e640100e05108091514500c8954146032060121034294040600011440c250060506130000940d036a0500307412280452113945030b00d414400b80c034884d20b940e002c00c8000e40580c010550096240350b0403503201d030300700c40090b022000214140c80252030504076140f0b190105c0c50150402034002c00c95126481d001074060030000c0301140c03540c0e20aa202d040450380c0490188100001540302401c801d404640a02981c1001c003002d168048000e00001c0c2007440024481003214010700203410b4035604008041c1c82d91a0030304100400d0500301c4090f003581c2c010000b0003510b280d0505 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 758234775 1250 758233525 758233537
    0xf0d14010c111612170301090f0f0b0102100c05090438090106140c06010602070f08030909010b09151204140109030915030b06040b070204110a12020a090e130c0506 72
    0x100b0f01c3c0064501c1c1800c4c4134070510701103000342d512040d000400c2c1112a0004015802898250340c0001c144510000361000c0300c00403103a04031f001d4140041c040c107070b0303a000401000c04044c0ca50000b441000c0003100ba2000e10076100042c0d00039040c0400386d50b440c4d40b0460421103585980d000c0d01014101503040c2a04520a241e100742c3c0200000010b00009104960f6010b5601c0303000b00e9240b4160303803a84040d19103502641f0440060b03000c0300c8140000e090000710380e002060103800440c109100003000131a146014000d1200030400840d0b0100c4959400100c00030407120b40810541d40c0021b040e221441050444003901ca03807103090200410f12005224480390203400d0b80da0040503900b44104460881890740e01941055152149120b103a80c6445c0107100501e00c41207196502c0f0407c0c41440107540d0b503141480c9080f00103202d20a4202d822106450544407055030050340e039451f22100303480c003811740d0b00100c6a800e43c890800951040450b60202564000c6508540d269521030401178680b0502e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 758236025 1250 758234775 758234803
    0x819080403080a12090b0405190804120c0e040302030409110703021b01020715080423120703092601150602030f03091c08010e13020f0f0d14010c11 65
    0x10003080010942c084042c201c60705152429100400e02c11003820245e0b444024156804442002030108011040000214800510301c100d07415481903200c2c0903040c0034610640501c844803c0c9200c080214014407a8080c118001040c1c08505050a00130b607a9001030113400901444c01d10505080321901040c2c507401580b40e401800c0d20300d100480150005460030820707056218000300812188090241140551042c1e580d013280c80c0f074a8104100550a105180007078660300c10f08035032192501051801407025203e00940d07a0b40411300d01180c9405003580040360344420301d01c2c0c6142119590051803800d804440080c0914180400400410710003445541c1c0503920402408070340e555070341c0c040d5901821000a5502802c1d504229140c40c1c0140004100020a010014408030003c504600d804c00d00351007155400007241c1d408100031411100d51580305085031055100155190020342810039030224500c210300386504062406080b10a08041c0462084200111440380010301203100b40741d6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 758237275 1250 758236025 758236027
    0x302130302010c21050d110301030308060d15050109060302011205070807030f0207050d0201142203081510050a020f011802190b0315151207080705040306060906081908 74
    0x55540103480e0f0030b11200c0d04031540784800c204104846440c8a01d1142214507858013a80d606064041c681250000d040319507070b0072010b01c01440031031740c000f410580c000010707a4a869a55071030300b008180700c1c0b0081ca058446a05260021034080c8440d0130010407a8402c1c0c07682c0010240081d0079030240c8004585460025140300b0001d400c03070303110790005441c6140032000185080c1c0103845160a0920302150080940c0d1617a8603a1585185014280c3d401910200c0307100e0380a03a0342404d41c40082e030088018007048007042c04964540b58070fa85407409140700820481001fa00d4075000b82094110612800142c003409402d10210705040c05103e00c1c0b42c2105808010440b01c03a42000841c00200030486110400540c0206003029000c0043d402160780303480c59418244410100207180d000003c82d01c5c1080c400b031001e41c00e0740312040d10960700040355080c420030554030040c0407100c6015551025000604000307000036041c40d91b5002d402543d1a010035103080203481000b6000040c1d80300401006490 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 758238525 1250 758237275 758237279
    0xf031a0708070e0d080705060601090b040305190206121603110a0503061c080a030506030d0521150a0f03060608030405031b0609092410090519030c170607030213 71
    0x84a0f4114200085004101403d4003010761100c070740c0c2e034202c1c41c41110545d102c0d03403d110f410768205803880010024031070030901c0c260441d07460f5030b21400705211a0618244000c481e10440da940c506031100311000c0c4140580d2803401d00c2044c80c415101c1e09441010915280303c19441420482c2143c04010346612258955119070052054030070040c4814101c4c001000c91000002c0d07119001003074101540d640104141c181042054108101407400e1005d2141c00c0244428001100140d0b00d01c084a4040c0001e455036860380c07030300040c1c011568130355200c5c1c00400c001c80c507421115003550507640a28410030003546c440700899a02d22a0b0301845074190720194000418032035400b407208180c03001801ca81d051460680220715400300c1900d60040800021055405c41d20191480c0304060000300e40301950b9907524031018040c8055801441d004205c002102c090b80249817030342c4801140c0c8920aa208195555071b558038010f1100380d140b945002d202c001c01c050500c0385c025241d10b500401124500c40d8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 758239775 1250 758238525 758238527
    0x40213031104020706050708070905010c030c110a031707051b0f10030b030a211805210f0a030f0e0102060c0307030905070306021c0e06060d0807060203010f031a070807 74
    0x1a444140765079002e5003c0013110009091400780c50301070721441d10b03805030380d040c2158050f098060b5508035504115120707603480080b136440814620303219008000c02c0c40c1e4600d403c012032043c44003a00b0280c4003500072a00e038505a114600100701c0c4500680584a0a40c0e01c0075074500f040d03900001c055440400c65003507041b1032800c26050703044050f0608000441105060100b8200b5070481815a4000c01c040b60300f08189080c00900041c041092034400885000b951400118403003e00809000b0120f81e001d04a0f141071114111004181d2030045079506a040b1407565511000000100c0004020609514086004100140302c07081c0580240c0015900c0e044102229040100100101a199455000800d005200700b00c0030f94010382025946180403030307080b003070300c0c0300d0801c0048814039010880d00b4125000c2401d5400040851b110f20011280b401c00700d0f25406a00307400b5002610000000a90000281509007182e10611043d030a40b080a00341020701c0408a41840c08505840c001270549 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 758241025 1250 758239775 758239793
    0x903030702100c1703040b0f1009021e03040c0503011404170a0311030901050f1b070b070207051201020d060e0f0424110414040902031b040b040e0606010e04021303 72
    0x100d03251000381c0102c191200800816080b213005000800041484280400c01400c16808801d881c6160014107010349083c6050305da034403c41011070b42c007007074241712280310748403481d0341c15000d4950540701c1c289400c0003030a0b09041c0c07250b584607600e08408a55144074508141d8031454000c07a460700c07044c00014620310150302049114003010b6840000d111008030000203140518241d0300006501e26007828201801540540300035142a0305001884001c041c400071210344c50340c0720060f1041e40d25486400c0c0e14294107034200701d40c4180d00c100b048070403002c1540079010145600200f030003500d81d140800700c2241c00903251658070301c000303d0004021840c41c3e0510082c404440e43c0b070320301412a59844004460303402c0d20424400d20b00040400c40300380410464001c041080314104441c240d01d038006030f510a03101031200c407641e00c0440d00e04c1490f61107a000400c2940042c1043c007400107400c2c101911110103d9179680415124804103045040601c00d0700c054852014420101c581141c50b84008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 758242275 1250 758241025 758241049
    0xb0a03050109061217210411090609130314040b071b0e151905090a020a4a04090b0a180210030207110a120311010507020d0c08090a1512020903030702 66
    0x31b10490440200046aa9401c4611560055096004100b0f2500c200460014041c1c059441260020107001d00800083d10610300c40f03038941003841011041100800071030149500405855802040c038000388610842c003010b041e9642e05884022031b888042c0d4480c0c0c00070650b030034124883d04401000c02810110301c803455003040d820312418201d64500c0011900303c0c0450f100c00500b038020486400071a00325108001c400c8108410341e00c0000d15201c646450303401018078030156101d501080c0b070044004c840c1c02c143c400014106010106041c01d009100b01002d407140c24455144c24240580d4105281d80c40303080380d900034810105610034450450207508406822750744452b40801006041c0e82d00780003180240030f5645000c081c41c1c014100646501c01501105071541d040000700034400c0c0d804036000e18510418180840c0903c0d00b4201444180103240c44550004061000441c15400e0802000170122003540c034444e806440303400010903401045607194059009010b014010319012402c254 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 758243525 1250 758242275 758242297
    0x305070b0333040e1515100201060506071e080a03062321010212240d030512070c15050f0a090201080c070311060a0e010c05090d1101090b0a03050109061217 69
    0x30316000603070b81005c40881680c420000d9100c1d400c8003d142d00b01071440c212981080c3c0000c000d05860040400d615102d8a0030050580e80d1259005e04000001000340b01415041240305817208003400d0090001c8c03003640106498151824014641c0c0b8003400320758446400c0117803184002e4041003012011403c20390f0b10000325550244400b03894442c2c0780d6407440c451049814401d03180341e8102c14060411054035039107400f030600f444100000c21381000c2194940042021801c42e1a940d807401129004030441004080211140f6240038800d0503401c400d021f408030301e2340c80200e6241d07060f40a045a440e40d6009002ca040070703000440805042d80031305100760090900c50948080812030500780314080300c110054a0380c0c1d818021034010f0921840400700c40741e081ca00c0c0f03062840400a01200c030000801400301c03660b11540300d1140d100d00d404900a00c00236152580b2032498050142c0681b009000e0311103d14a0a040000d0080c2d114050410b1103411003840c124081142a4100b00c940c03004003004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 758244775 1250 758243525 758243533
    0x506040608031902010b0d0c141c15111209061602151005100522031a07030b10200d05040510024b0715090305070b0333040e 55
    0xb1600c7d14020440401e10500307130340d08110704103c00021200c0503400e800b8059503404880d0500500518070788400f480e000021000c0c16442c112481028014810750b90b041d0720787c00b04500c0007049041d2220780c003840c00101601c00661301d40d840c090191110003148030040e0b01c03258140c243e22003130301c050540002c41801191800f0b074452001c950a107801414a030f00003000000c1c1003401b000598015000d0031019440100c6071072441d164112802d1141c641441e8007070304980400e580340d010368442c1c488404040c00540403800000700203061108035409001d62014101c0ca104280000070a00700d100030403079203456003000e00b043c05100b0a2441c0208090030f41c411310310310100303030b9034400c401c000704903601e4909808181e04d4044900c841012040c009a050140354800b0081840c00301d1785509030b03054244500c1c074901c0e001c441241e50010aa0004d00b01d40507115001c9005203143c0000c0d881924100c21580120700c040c60b542c81c0c100d008000c0c046403501070402410040c5859040b51002c184800c0883d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 758246025 1250 758244775 758244791
    0xd141c060b03040c060f05090a05060f0702041e0605041b0c03050d1407030c03090b0703020913020f03040b0709030c0513060806090c0f0a03051b03121c050604060803190201 76
    0x700c585580169000d5688802c01c8000300804d07035000f13443e075848000300c1c68001d09041000d004649108001e00456205036404224165400d40200540d8640c9800400c04d004a64407201c08070b00094100c0240c00c41c2c542400004112400c0600801c40b440440000f20098040e010b0402c5800751030f9008100c007040320410100c45017010500400040d5094003820a2040c00e20702c10141c200c0d43c41c1703040d10051504010309440440c5807580701075400350360b904001d60f944580000144210782580740c1c8200552001c904400441e000c0c40c06142b00350302c50b508102544e00d0303504c4182e500c0c0350940303c01003c000c2003a8051050b414404050003403044120000314180d0b80b600101410710200f152007014991008071800c45514290800075201c003c160b4064602e00c3c2551500c3d0f45a40207000a00110341040307550085544040000d042c1d4052220680c540710b80a001c4007000d01359040204211040c10000032038a43d107007070304c18030045800410065140c0245c0d84400d1080d089074441c0d510030b5542c1c035108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 758247275 1250 758246025 758246039
    0x160e0402040e0f1c03050f091b04240e012108090d060609140a061a0c070b0310031b0501050d090c0503070b091207080624030a11030d141c06 62
    0x150364403025130f010a1802d48030003e0008044410041a40701400c404900703210383d51030045207802c60400e44a003c0300740014000081406070504213140241203641c082d15141490a00c284681074071403400f41c42205036601c8041e06042c507410606c01a1051100c1c00300700000d011400100b98864016040210741c902e19140c0c14101c8846078400c00d181911480141103510805414680c860700e8540200649403c110041215035459407145141020000b02251b05440400100000740700f1661103555030b01c0e2526000d51a0043c0744021115030a8864260218102070303a0500240d1b00c06035911818001c8140b081005400040003e40d0481c1134640c005c03402d52000c0c17115802030409111203ea8500040050104200720351302d10140580001c401400034090100e4000d0700160514100181c1001490304102400c00d49206c00303505115440350482001403580f102a003600b0700b10241c55014892100a8800c0340702c1c400d940c035010344104240b980c003040841a1100030310000600081080e20780103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 758248525 1250 758247275 758247283
    0xf1401050a090308031302130507081b040527070f020d05070602190503010503100603120f09150914031f0f090b0408031f0b12042f03160e0402040e0f 66
    0x86d11403480103441100101307608060f07070b80b07100b046940e00041042e450960001448100094281a500041c0d03145042401e0071002c1a039000d07010090404002c14604500c200034000810301201005003480006105103009441030164510b680e009044080c000e540c08440d9076000b00c00c102c80480d03013800100303103003301d03583c0144000120761075080e80c0b941040c0400d403900040807140f0032941d0411600b4000500a4443d0740500503850400008110b5003000170f42e0784440c590004200300e070b4000f0000220301e0b40041404125050300c0d000000c00c4020200b81500c3d05001e9030104601c1c26101d0741070b030f080f807403982c030489080d102c02100003415001c1d640c81107035403401980c003516004804820300a81c0158100d04400042d20100c03207074511480d001c020206401a01917000302d035070031080000c0a1240603000206020781e120602c1e04040e0005040c1c0380722417803170748525000344a092590004882d48840e1101034608182254a1682e035950800c0054101002c898516001e80150702507403840c208 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 758249775 1250 758248525 758248531
    0x80601060536040f150b07032d0f0507031e0210020a09140607050d080406020d111306020303011215020904050106080f0c0a0c1b2c010f1401050a09030803 68
    0x10703180c1c41c00102e00e040009036225079030349040c03036450710409a0058043c400040102c4059656040c0c0b900c00b075007400d0b22148100b03840480307807000000c1c400b4211030340900103006181403034982142a541e410b00496050050050040200d102c7c6030082d4444900072000303038240c45c810b104a80780a401c00598200340c0e000424005d020840c2d40d081400b10302c606483c0405040c07010381d6290f050820340c0c1c8585a035084d10010030b00c28007980401003810300003141c0445da2032118142c01481200002841c0c2c0c92580e101c07141d0200c0a0781401408038001e8404400c490403160900602082e003111501c80c0d8681c000c00e60000c5034041d82c200202c140644580c081c0c00d000b84425103500703995241c4a41c171851216001481c0369191079080100d4a401a044400420b6283e00002e0798905e4400781002410b2421041d0000d03051001e4400d60442c01c08540d50911600312100c5010310040d90740d43c030300941d000129001e43c88071003414206801c0c540d4460340c0030b801c0e00110341c50300303d00083e500d48801199500603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 758251025 1250 758249775 758249857
    0x3092102090615210109020c030306280b1b0a03231201120c0f05010507060506031006030b150f0901030609080409020418051e191d060703150806010605 67
    0x5400358043d540d003118080b0b401410070f100c06500d04080c1360000c6440c0d01c00200f00911a50b590b005c01c40f0030040940cc6501c0c1c46c80302d0880000c4040c1c94021584040d0071161f812000c4405821111a4003080809d440110310380c141c44d80c00c03500c046151818858100b01c003001c041c1c03203000e00c0380c0c280040460701140d00070404d1684d450440515800d080303d9001940c6c004116000420304104440d91b4442c0c21902e4440c0c11200008041c0c880c2030011f0f0070b040110006201c1d041c00d10314003005001d40001110f00400d14429900840642001400961031071121590f500c107010100403c0030070080e0f008111203030700c00e510003440c0c1502c44081f8012600640c0015660100b52485401204080e10802d9080102c81d5848000040a0202d140c107140000b01000080140c000c40505ca852103a00601d5808840c1c1038102d07010440710700080c1e030f20b0030102c4015002034144124802c5100103800f14100742c0c2c402c2c5d005400d0981c01e004041d00c0a5001040e182034034128400200d440d01c030a141600710355060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 758252275 1250 758251025 758251057
    0x22422030c0806150105030a1103041a090d1d0604030b0906040b180a02041e140a110906070f110d0503180f01020727110703092102090615 61
    0x46007041444500590000740b0254021001d00c04000a00b4400104c482002d11306603031303203a171014010406001c41b000102d03403004000c018801084020381e0500584804125040e00302c0d5154066a07640c2c107419842440440c8000c1041c65680e00b2a10075058008405403640d4541030741d9030707501540424112000340a98010806010801c80046078032600a100040c4011034814440011929841c0c5000003d1085035280410b42c0386000361201070071a0140303014104503010342c200780b1088405048816842003450185a55184001d84050710350801c80500101e00300031359607850000400650740181c03080062508110140d40d9100747c49042c4610480c095602c3e050800c100d520342004400b030940c032a03230004c000c0c0b5084d81d900250300d1007190311310a0100c142612504803200a00044041801070500740312981c87c19031009802404964861f0b074914903e59a2081c0b110059407040041101c82008025580b02600d801c025060b00100f00510b03c03030032809103505a010701c1d13000004104201c88 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 758253525 1250 758252275 758252279
    0x1218040b04200a08090a110d03021507030c0905040204450207030e040509060a1d1902090a090f06320106030b010905060a14130e0a0b010c022422 64
    0x240c071101054108080c00006c1c200d5810315075458181c0c540c4403401e0f9015085117150402072620811910044000541203100c281c102800c00601405100b500340000c51040040080c2500b810701c00c0f2070031609442e1415003400c2c2540004a43c0741c040d0302084903000c10310187e070010206c51095801c81652240c200582c0c44140c2d140181c501d002c0019818071070740c988800c00406138070110381103034080990700300080e071243c546006104400003120504040d1051090708002d9284000142c40740324000caa0900399940c1c1d00b4428400c0e111641001090300040c48180300000d041a00f25082204c584075402c2041d0084441e19280500d075000071002c6900c4840c0100405a00f603c1205d032030b03d6081c03070622402d078240b1010441c548118502c68041004041c04401d80010031015078900c0020000071001d4599074600b03140ea00d503804c0d11044090752410401c018a58003035140c017a011907018103080c2c00d80000c1c0e405942c3c056001c0b198000483c504008203507228010020f60306240d040c4822000c00c484c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 758254775 1250 758253525 758253527
    0x18100614270103060209011112041d1915030210171006050f1e07060504030f030b100819230a05091902060409060e091218040b04200a 59
    0x107854403040d031111103119a1010380080d089000c490559130090400350790b0714000e200480340301144600c006154060b42d40e8100c162108080240b00320b8410b183e0400d0010301198400d82048000d482c101c03a501294000c852002d12507802c03066501e00c5000c030407080265242c0101c2c2155111001d000c00046103056400003081c00c848006802400c0d002011200a08081c00a001846070685095031604042600894100503200b0669507545d00103081d0380300d684034039000b0041c04042c0c03421008a58a46200f40000c2e100307100305054400010000842c2403040f440546400c00702901c00c81c107103003a010102d100341040d4003910480c20b0407404043d090048010308602c107004040c06064246d800d0074148071641e00005000a0f4000c2081c00c0700c0d050080610001c6d50078030581d40b2447c00141403200002d40080110442485846440103641c41d580d51201d008a0500c56020600600d8030034007403002c1c0c941010f42c07103196046009440000c0c03c092210800c1f00480040004d20141d00c80080c11005007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 758256025 1250 758254775 758254789
    0x13020d0504170406090303120e0a0f060b01030510050402070c0e0709030506010b090d140307050d0c0210021c1b060f020702190503070324050f270618100614 69
    0x7481d034209881d0515007084c000918a04840c88041e0400c6007541e0500708140040d4410000e280c40d040486a6640d440d01d04039581c10f103210029601c00349003001004c01c80d4004e014075807042522400d80345100b410710782040001e400c504800e41d00041ea8441c089508803943c0e8210b0300a010607150000e00714070703500d002490440143c02c004440c00c0240030303403100360f20b50110015070309903c442c0700030707103200340074030f030f5499805024406031607886020304071000c8030380040b00c602c601c50003079459500e5184a22801c1e070355182d2007007401401180c0010340029441c85400144a1185140d1174178804d9409900c5100641d00c01005031102d880c1d00045160440c54005841c0400681030b4183d00545490315001030780f00c0761a8072014082610720b111400418595804c21480d1000400082000c0d061118510020b003100f190070030b002e1018110ba8481035404440d01c0da0304555104024001503640b503001280c05114000d03100c0e014842e032100e1440c0381c9403501a400140c00d030b42c180d64076043c06000401101e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 758257275 1250 758256025 758256053
    0x61a030106081c0e06071115040f30261911062802040509090f0f0a020609040c020309030303090610140f24070f060e0d081513020d0504 60
    0xe000c0390341c0131407489031240c4003903800c142d030040e044c0c140381054400400c008090303520610104080006012800c6210010b14505072703000300d500c0301315602c00c801c0420a18041868068049040b030f0385080002070200c19a104410160f46880c0d0414407003440225454000070031385407000e90b00c00a01a400b5034801e140c481607070000001441c9a00340800d100e0315070b2900c603803800440c0100d80340c21101d48040b030301160b004001c050203400580c03a00e03650040e221140043c00021314007070500441c108001c00941d0104498005008514016215041000800c0d58041000c04e601091080803a42d503820310146100f468000003800c154604844d50011103103490700041c001c2c8160b00305800d041d8641c90402c6034194030580d0740301684508140050040b6600b00140a00d0b100b0004581c002c000d5481c142c80e40c0c06108000c140803580c44100e01e107403921000e803d40c100164480d00000c0414910b518100b681440203002c1072441140080850140d070702040b00c01088580307130401e0008010743d000c0707207541c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 758258525 1250 758257275 758257277
    0xf0102060f010e091203010b18040203071d0406050d081e0f030103120908070b0406143a0501031a060d0b07030b0105040e04050115090504030507061a030106081c 71
    0x80d24505240a214000c006002d00110500810002000c0c20000c00c6021418100440f005c4d4503583d403549440c402c0d91114003444c802144078078040c149401e150003a41d008031030a8a6403940c041c40c060422680d40114500b4a9005032114030009043e16081e03078815420b800745080316a510f580031141944a02c00800c58102d0801c20044c2001c50b0007005c0590741900d03400303020106e01079815103089410b0740c034681165180e0b005e0001d0014140003040014021a24180c82c1e03044043c1005590106c01e01038454010280f05002d107210200145002ca80890303a0700750499051515441000e00c3c00701c4001360003c03500078440041840380504144032882d4000c004030382044580c0035543d107070465448040c1c0301c038051507141e0303100303080381e038010000c1e54054850218074440b00d14050a00601030542c5601c01c0c0214220204080b4984c1c0303003409114452505900d0711442c10000c2e0340c4d648020305040c0c0e00405071207040c0820321196a000e0056070010715280b80102400c018503039940c2c1c0042c0e82072020314 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 758259775 1250 758258525 758258533
    0x90705030d0c022709120903070e071202070605060103110c0717070801020d0f1d061923010503010b040b01090e04020d050d090f05100c1103031c0504020f0102 70
    0x240d5000500e07a01c01e180e00d803030580c40701001c07031010501d000c5814684810403c01124004100406071200c0c0b8404c54152040712905000204a86035520600c0401e07034043e048140b040c8980c0b00700b0382d075540c2c0007690b6142c030700e04031416060b03104102d800c1200e00b02e60b401d0310348003842480d40c0d06004462055950480741c40c0342c90103800003244d8a40480c4a6030ba10f030903802d40b80c03000c450000d0102c50010006940255038030903441030107900804124201950141c940300714004035078075591400071218507000003005541c60b501e911350b00145914070341c14180b42d01d6814034a01134059050b030080d070110401d507031401e6505200800d420744821000c0c0714012440c056560010b0303a8088201800c0f15101c100b1076403503072101d00200d1600042c03440040d1840c0716121440d140300740c0c05403c80c8101c03807a84220150b10364032075003049411040212070744001b422080e4007d0100d498001d80103204500101141d18080100714103c4003060300061004c01c02c2d58840400042d4203005036600c5c9001e0003440a8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 758261025 1250 758259775 758259779
    0x50906010c060b030f0a080d1a030303010303050d090f0b0603070b09030d0e1813030809120316090302280f08070608070302070209010b0304140f0c01120f050f0f0907 73
    0x9250000101025014580b903c0005001d62000d000a00b0301005600c01c4e9400f903003950410324050b40c07024101d030a100e85440b030031040c8442c00340711000002d03100801641c0745d0392964408492640141d41d140f00c165990746916000240c4a6451914592141d8003005451501c40101070070000c20307912402c48450304104030306050f80d003c10300440c1c2441d58284402d441084002240302e501c035850041960501030020b1280260080080c0707103031903200c0d5440c81c00c2a0344510a1540340e9080381356220401c40d0a2001c41c80038a56031010106900052400c511000c0e540c1d00012036203100310414145800080740d041e00d841c601c050369603001c1d0201c8000f4400c0c642c500014655100d41030b20490341008183c1020500305407094040702c210702e400500154995031120954501c5500980d02242c203500090000d025041010407070745e5480c00a44007030404110300c4ca00640c1c0100c122615075000301e9455094000e000300611606000d10003090303e102442c501040d4100e541103016084030703d25400301100b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 758262275 1250 758261025 758261027
    0x60306060e032b030b09040503030405071205061b090a1e0b21060604031506240221070501050a0b010e03030f03011e09050a15090905250b04030303020a080105090601 73
    0xb04422440300114559401c01c4600c2c0110004e000c80203409506c0030942c4113010620130000041c40c0114025021b0784da150780c0e1036004121900c203510004050342c06c000002802c264a00c101142c0800e0013401880c582030100d00014860030054000303410300c9078404000d100502605411001a2130710200e1140307041000301c081e00c2c2d51600446525003002d25000050526210001a18025607000c0e8100d045481e40218640152045000e88070311b003484a00310100603518074140409010007074001e03200202c0140901c00658112494a0102550400c50240003c200344a00f5100e1040c03400300150b5546644001480340c8180320750548264230a100c40b4000c40102c1c8110380c1181c1024000d00ca072400b40c1425461910030b80d504c11500c0b03615200170000001000d421251020b04c52a5000046a856181a0044078500c08003c0e1060f40300074082044201c0e035602405840c0025500070071131580e80c00c1036101c23980c45074008500094012842114840e00560311038098082100c0d030102038600240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 758263525 1250 758262275 758262313
    0x1d04110a080a17070c0806070e15070609030e03160e0105040221040320060f1018090f02150d110307080c0d0e07090e060a091a100f060306060e03 64
    0x400b42080401c8842850403c1d02d15040b00c03491a0704c01d8002e244140d990601075212941201c020703000c00c100c24031800741d038a0300e07600c480142041c1100c064181710007a20f41174000c0c90550011014002000c46420081c2d408108620f080000d105001804c6070a1040343e102c58103040e070260f402240140190580c02141c0503d1104154490380e0724250396640341012940b440740c845010030511003040440d102c0250104909204000d0622040e84580710421006254086032180304d44103c0c0b4195150b12042c080d801c508030280c01441c2d4081041076603000200110b6886120003003018001440c2c240c054000c1c012205603004510b0124154a8994406484c02e20014030f45017150742c00250030340005140c0d86c40b10300304043c004200c40d0900d07100c90084000b448103240261443c411000080c81003c0d00c0c2c0142c0e4072099100010070340801a074200400c0d101e1002e0a0121071003103124000ca11407400340358190043c10716503800b24400745401d03000361010f50000c0b8018025003003070045081c1036010027 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 758264775 1250 758263525 758263543
    0x90209280501080c040b04060e0f0a0f120212100603122d210f060902030412051c0504110a14010e060a0e0d111503010617040c1d04110a08 61
    0xc03c14100681d2403d514034518412600a04034014000c80d0118241e41c1c0003034009240c0c00c0541c0d07000340c4c00410204120101a0501c00c451180c0c841d0181408081d280c2c403032a500d00c5101800155600e000c0d48046420800140045100c035070381ca01c000c00600c40e111101c00507903191800c00c5040c1c8540703480c0030071005110528090000b440d170341c1502001882802c215901c62414a003c003820500650564040d0008000300c10b02c803410124081498010752003100d0040790321100c88102c030418030718281c0303a941204185080d4006160395a400f41425401341e240b0a9214034100d030354400000003009501c1076182c002e5400141484529019a60806013019842200f1030305e2035150180c03d40200c2c0d20040340e880352900404411300c034102304610701c145c5010b0710b10229028070b03100307041384440c04960000348a440e000602e103440c1c961001181010fa01c0d0841d008500d507034841c0707480d40042c5c40c0e0010004490b84c03038030981e1070801082c00046a200b91000d501200c84419a0703151824040d030b0307a1000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 758266025 1250 758264775 758264777
    0xd060b2b02010e060c010c030915060617090c0303070c030303050c121b0d1103060405162001090f08130504110706020903150103050307030f03021303030324090209280501 75
    0x942007080e50b5542d0005ea03403014a00d04002d010004080c0e8004000e002c4500d01110180c0c0040c8e4038828960300c6000f10001c1d0741156458041174194030302240806103005d400e0b41c0b0780c0d0048401c000c0c4640c40900c010800240036120f2001d00741d282d4680102144c4c401009807030320040c240000508960844056604440751120f24600e5002841240c5100d00c41c26902111052401842d441071110100185110305803ca8003005140e45040b8035460000d0354103030501c002001880c0404d0248281c80fa07070300ca0a00b1101c000210f5040369981e880382140d540c40d0691302240042080300c1031030034060810014103030568040c46410141d2030850200d004803c40240710b036401007845c581c5a01c082003501103691040c1c0781001e080d6900d00f8959201e6010340400d400207034441d4009103a0501a000b01c603015a0b03041002c50440b40b0b5030b01c0440c02400101c06141b501c075121080d442c46d03070800011030300180140c09401a501c04041041081d50002c003580580f0b031912031a00d40c0c1540881c210f0074005c458007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 758267275 1250 758266025 758266037
    0x6080c030a0b041e1104051507050a050318040f0b061806091305071b030819021207030e0705180c1c0908040905090606101103090d060b2b0201 63
    0x241c1285001078500101c540c2e4100c2e2070401388030001064110308503104c0c0b9405404100d00614841154202e00c00e902600340c020501c81c01401141c038540c80240640d60040003030355100b00d01581e41c035003107501003001014180803c5070b0b2414240b5040c8952140da0340118020801185500d003c034285000794903860340b01c040f01104032145511410211440721a00030810f20441d00700141c00c400170401604e0a00000b01109a041c44001c0d112100641180e00740d15518400e0b96400b141d0001e40011036050850710b03070280101c1d6030285886007400e01810981d1000f08510308030141080c582030083d80300c14402c00c11818603032000341c02184119009003103000b02e80d130784003048454a007030301c00080401081a45000035903828401a0301c05882a0351080708244240d454040c2019a00c10341910460b901c0000d03200703102c1e40f80e070081c20700070072016010007a24200b8102000080b920042101c1c180d81007502d0340111003080c0782600079420300110604021216465101090302c48244d103a40080c10f00038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 758268525 1250 758267275 758267281
    0x1f030f0207020612010927020609040603230d090b0910050c030f070c2301030e0c1008090f060709030809041509140f060f0405040c0801090b09070f06080c03 69
    0x105540444580607000350945554081d801c1305212564803d01c1900c0d51503140c20400041800d13904a103211217a10301e003200110f00d0072a020011194408989590f03c503a84810000c0000c400f1800100f03801d9507004c0220000c40d40360030759410004481401c80400000d400140719003504142036412180c002c0d151022070084e1a64103840d01c0c41047d001000790700c03010440718484080400140306d680d1049403800d6a0a640e1541c071104401032b58000c3c0d0000e00304102c40030495129a10945241c2c02c90400c451300c0c13540c2c403000700c0c4950001110301400684104200082d1a01c00c0161015a500560081c0035619002c9401840107400340801403807800000303018540c65840340c000901c4d04805910f1a03c141e0351768008140103051a94007004030303404604c00150442244003816202da84040d0001c00d4070781e5010b0400006103c0104101c03040e504034100407914003c02d00c154036810380301d981044494200b40e13503442e140998a42c07050f5180703a043c2600307012640d40701c0081e5401c280c81001003074590b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 758269775 1250 758268525 758268551
    0x610080408070c0807090b010e2818020a0e0d0f02010c05010b101e090f290c0114130c030308090c150306040f050907120311070f030308061f03 63
    0xb00c80d048015081420144003c19180000300c0c81000b00c4442c0e203010401171481000545402e50084001640000780b801c60000c0c1e03000040c0382d1940141c600746403808041d1904a808010307440c6040c0001c415602040d007801c070581089982c1300c6010200c0b401040314009580702d56500080010007070401c0307000e0714201c007045001d400c0301d209400000c00720003142c1c00c0044018a14104100d1000601e000c3e2402e1b08406405104071400703580d000b01031000d5440c00c1042c0c081c0e1140d8440c44d00603010700a20781c0d0000c081002000f0340039001e0100004165810a1680740d16000c0e0090402d1002030740058800c0005920290030f2001c8035030505184021381d846000060038600a52110b0783c005030407240020100035441c0056108031802c036010084825141070600032107030300701d4981401d42e100880a1009416040f4007090700d074486d00d0308aa500c20340000040c180001c40d072001c060410720900074400c040e000a5a55445201610343c91040c0c8103448500d910401d000082c40e06044d51500441824 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 758271025 1250 758269775 758269777
    0x506030c041805060f04060f0e0c041107051515010206130b2814090102090a1e03020604080a170c060718050607031707020a020a06050d060918020310050610080408 72
    0x1030f081815a80369181424100c444007408550031200d40b40b400d01102c01c00d089074400e00c0151400d81c002481c1c1c0c4e004960601008000250150a09060502400340041c01c2048464a124055030291285003001c0b0603101c1d11074500d403c8181550404800c028003001c94200c41020950400e4140b103040e104c410395900242411840031545800c02c904a5088810b41d0b0005804c01c03144900b05400b681e28010807500302d00400b01d13402d0703009403501400c0240540b0100320b800ca40100d002c0b2413113450b03984d81c00140d00341c0c040e502c4511113401c1320203a00c091100c0030b50003401071749060748400c1ca4003103038183e25516001c3c024440810b11000300b868a10072265041050054000a408544c1d1402c0c1c07414090641d042c0040424644644500024480d510108490304202d5000c0d004000303c1c0d0070240c0607202504450202014142c0d07480c1d00103900c2c0c105020300c41c03d1a01a458050b18072641d4014107051041600e07a0004050801e4103003c2d044d103402c0025004d901161a15001c2d9407214588a003603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 758272275 1250 758271025 758271071
    0x181503060c03020a0206160f12021312050f0106050604170a0b100509061215070c080a03021206010c05030405040905010e030c0f0706090806060d14060405031c0506030c04 75
    0x1110303180076060603030580c0650080114000c0b5400300c079240c1d911400d0740300c00070701075a108100095603003c0e0f0101d4a401041c10800921030300e01e0250070601a010101946003280e4004042411403031200420b2101c180420b45c03250603244020300a0500703040c0440c01c6071155114100c1c150460120840100078103101207503141c1d0b849200c40040d42808141c940300300344c2034081d05120f880720700b0101d091031520005190751a04000007404c03d2900c07481060001c50300c010500014030508080f81400113480c000104121800e50b140181c0791000c089098948040043c0941e0502400c605038002050000080ea0200c0d0303400c9038046901141c82c41c001b40507000d0409003000c0c5100100e4400001080030a55040b200400b0b8121031480342e449001321202c0489104404860b00a0004903102d420002d030091105801103d0040407110111183da1504c00704440544540c3c00c04510040009134404200b0940c0c840c03610f041c01a828150006519200d20f082d42c04c1c0f003203686030303a101c12800c8200c5070403103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 758273381 1106 758272275 758272283
    0x70e010e071812230a020307090f14040602090f03060c0a0f1e030605040c0207050a300b1b03132406080c0f01020106181503 55
    0x10b80b42c441c40c992012000b04102000c180510803020001d81d01384264082c4800481c2c070307501081060761a01e56143c40e500080000005179400041103000c0d10180c81000602e442c00806142c01451103000c200100c2031504100001e1010950103002000c000340c41803064144100c0806072151011260415448814400d9a2010703115001c4081c0d0201e0505214102c2041e045584d107444060f40890b0000a44448081c021414580241216490140002e24080d800c050020307005030b00d10b02504150384419200e00754020340d801c1c510000d80d8a8081803c1d4a4600da0400c1c1820210032550740314541c81da4803425a412401c641102d04c5601e200b080c10b000018640e41700b61402e60701010001a1080c0000c1c5015051098429a401000001d00800d80c03a00a2414000c0e000c401c10324207410359152500c01c100a01061356a01b003410121031002a0344c0040002d01516010642c001030 = true := by decide +kernel

theorem cover : BRFrame.Cov 758093525 758273381 := by
  have h0 := BRFrame.cov_init 758093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 758093525 ≤ n) (h2 : n < 758273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
