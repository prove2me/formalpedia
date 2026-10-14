-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3442
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:27.784364+00:00
-- url     : https://prove2.me/submissions/b91e34ac-7d5d-423c-a012-18d563340c2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 618884892 ≤ n < 619064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 618886142 1250 618884892 618884993
    0xe04050c03160e1305100e070f060804050613020d0308090312090c0a050102070e070f200d110109030e0f060d06030b090715090b09011101050f01140a080a0b06030109 73
    0x136840c40028404120818080000d03e40002c031030401c0c00050f460082a500090f1802c1301040d00800c0558000301c9480c812807094088070100e55600d02825401d004d1554001d410091012001c070020380507a100c994040c1c6000b040f60706180076140c8031846154151014415a00001c10b400040d061201c81400541400c0c002022240d250500c2500e076564018128000c0151151003039803100c0c030505411030f07a02419400e80510404c40b8810300d8a076410131642d000030640170a549440200180124851290540c0f94502001e040340180481c200d0402c50640d4000010041c0d4042d1342c00c20302c25480078500a101120322481c08580c42450154281c00000e10009a07043c544442a0b02494480c151004900c540c0c1c1c1380e00d00b40c1d0040ea826400c05444000b15400c01040210001240d090321707040754040040c49040c415140248078290082d03000d081c48513080030a000c404940c91152154002d5405400000e41c0d160301d0b180c5203007003641c2d00c443c80c007250520203d8045402010100003103800104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 618887392 1250 618886142 618886171
    0x40f23010315021c051e01080c10090311040f0e0f0307060509010b100e030709050115090504110409090213020705150f0c070b0415051501020f0d0503010e04050c03160e 74
    0x1074003010791900011030704030041030312500040c800b0302c0306c0004200e8090240b454411207584841076203854246550143d070051500c0300807140c9480c4604101c40881e07801c0540a0a0440d03240c0a01000c0c0044c011024101510b5402041c141141041501d1280600ca0003442c5c440540c0c3c03921a05548002d400025540e040c0308122419568014160b41110b07000d01b8440300010908000c2803c0415683c044918240f60800000e01c0c1088c407042d0f83ca0046036035842c4444151a4800c0200700c40300b050030b84640b00070030b0005206040041d071090780100d000400c03a0003000802d0303a451f0706076406110103c0c2c0c590400c10000f40140000c0c13031016000044007013403140034a0b00c030b800c5006a002e908030251881c450b500200e403d111107482504500360080c50244103910f400c07000030301e801b06290001401441905c9100c94040d80c086400001341525503a03491840e4a030800725a0440c01c00742c03056840d4003424205a9450b6004c100c9680e00c5c205804200d4204c5292160240c40080000c195a0510401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 618888642 1250 618887392 618887407
    0x2031614192c040609021c030f0513030c150801080114190f060e0603120415030b01050f2109010203060d08130b040305030c010b0d03020a02040f2301031502 69
    0x14a10218141d0784100100001250320700340002480c0d420302014407082903201c00f40000d121442c0c101003456030090f40e00080c0040840300c003c4106116190250028449050030146544588010b1694041c00401c8584c0b0a4480c0c0360040b603200c40c0c0d4070000781140b505010040c2d90703800200d2607006002c2d0400030089040e0601d00301402c601c00030601940250000f001c04105240c036441098000f162840c200620b42c2c40307165a503000501903401034440c3c41444101690b00c5481002c58040d278140f40360468550b080030206401505d6007910303040c14450103001800441103c0c402400142c144180001d880c071210001c0800d12200c054901e83c000e034010400c200e00e9450703c4083c9001103034070100459860f016107442044031401c580101c1361410740007400000780f1100002401d140415100208214005071040109090301e00c08020b000d0780281c0c0e00400580303040d46c04034840880c0c04001003007800021003032107400a4481c40200c0320703010590040c0240400c040c03c034802010100c800b145440380 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 618889892 1250 618888642 618888679
    0x6030f0a080a0c2102010506030c180403030207080d061503051509090c1e040c02070f18020d060603240b040302240a120507020303070818070302031614 67
    0x1009034003610801c00020100d04807480b540c240d68070300c4d0300b1596562030aa4459541c100c0d008045074940c005608000100741ea5150200b03401c104860024000c1c5054000e26420303541c0600c00504c02d806042c0d003440343c0404a042c05000308070307803141c00800180d46800c00803001c1402d40b089010b40c0c10940f4200402c405039401000101003400102e98001c6d0315941c40101c0c0e49031080043e519900162540c1c0103087c03505c80b105001c840410200d509000c0241c0803002241c0d00c1034140305010500500c580c08000701d0004883c3d101030041c1080001d031a10440c640e49501f504c00340c1d804000000c0d903d5442140624003c3c90201c4842111200c40c42c409140441d009040c3c013030341c08040d11405150005c0394903254980031141402da0300500041e00d070307083c8800151445503a0500000aa410f1100060394244040102c0780b040b02d0716214801591502e03441200da00c01100007904d5a88224480800903a40800c11000d2034031098461040c800e00300400c200503484c5900209018810000c0354100709403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 618891142 1250 618889892 618889903
    0xa18170304030f020f09310c140a030204020c010f0b030f0d0507050c1008040b0f071e030b13140c55020712020a090b0117040b0f060105070b04030f0522050906030f 72
    0x600b01001c481c070142509d800103d4501442e40000d50080c80024082000f05042d0080e482080c01687c0030000300c514181410784541500c0c0349841c42d60450000d00e441a4010805060941c2c0504120340925000760701080c1c008114802e000c0c04100300c0350800040004031100310340c0c0501003006050043c14410b0001d00804058000c6050310090502850320480c0b00e903200740070414004041c001e8000010000c0340080c0043d0b00080403441142c0000341c58080000c00f00ca090340c00d00c4100d482128600c220100c00c042e0031921f241c880b0310b034000001403030381010040b4110b100050150300407003114151001c1d29006440d071045052400d20786006025982c1c0700320700c504903401404041440414a80100d134103418004203035584c0582c00b000c0c4001d2001003110544110000088580140c9641e8015601d9000e00b002c0200341c1070940c00002c0009204d0000a014800382e41461814418003c21100150710010801d290900950f5001c00c000d19100000641140081e07010f0166200e108000341c0c1c988 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 618892392 1250 618891142 618891149
    0x60d0b0103110d06062408040503030a1e02180103180c030b0c120a0c02060105010801051c08090d0506060411030601091a0904020a18170304030f020f09310c 69
    0x52907141c801d211540b80e1544000503140d00c40e008100039074603000f2400c03649107006c9501418503910310000d80b0003801103c0242c002ea41000046055558929480740640308000c0410114110034895888502890010303086030042c08451803c40122100010100da4008d100031032480f00c000358410201381c80d40030600980b5000000a09190f40d1400c00a045109024503840d028141504108508690b5030000f2000c841039803e68200780d98800046407101d1003030156a174084c00d072556000c485100c0948420101d4864041075041100100c000b40756401c017400c0690b50341d00030108001042c03825200d460302c1034014128072411401c0c9400000c00c0085d041c0078141b240c402c04a802940b40c03800c1c230203907094030000070001c0d540d420f8000070081002c0c040415200b215812890049001e4484806441c0107400900081d03040c20700e1600d615044040c40001660003d0a0b8440c1e00c02c0d0751524400184180747c1c100c80305a42c80c140b61080700d40b86008043e5024621032030082400080d0010079410100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 618893642 1250 618892392 618892403
    0xb040b0f130e0c150a0206011a0a0f090b160203060109111c090c030f12030504050318150d021e03060102070306050603031b010b0103110f0910110102070f0209060d0b0103 75
    0x500340b4070b14198501400350395260341c40090f400110b007000789100c000b080040829401e803001070b41ea88070340f85100c211110b1803c02c0302100703001c040c0b0361501c1940760181858403403404d2101c03d961001001c04036440f840c091840b80342c54024040070350034104002d07801003089100802c51184045614151230181c44844103a0000303940c241c0c1e540c41020303040004042c1c1c0000003420b545640b482c00c0c14040c1d501c20400c40f490b80410400014180c000d2050520803030700600a54500124550388140750f00e001c24401b40d1068641e8440c6203a10441c0307001d4000c00500d0200140d9440322942071607514800360a80d40d040310070401c00c004690f40d012403030100310f030703880540451030340c0360310b80021b0031401035140608050421400b800c0320610150401802400c00fa2410000d400710007024412030b100340d484580c0200020400014a0b0808030111052000180b0f030800343c0510010303543c1e00fa43c1c40008155040c0255034100320540c030701140d000360080401c6070036104c40080c03952030120302841407202510 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 618894892 1250 618893642 618893651
    0x316170f060a1805070807020619050711160503210904090f0605040f02010305010f05011707030b060c0c04110304051f021c05090c04022b1b030b040b0f13 68
    0x210340c54401ca20b5002e814450310001024414412540c010709049410000007861540440d81b40342c004240140070303481849c0704c4400d802d0322030341030b0002d080094800d50400c40404540070b12407809204444a1444443c02c03c401f0514010425141c10400740751041d0a6142100a4100c401004c003111b010140a0320085090b40090401403c14140410b018102a00b404100700400080e04108611079200b41c8041040741d80326201c4950012070b50050380e000c50722942d050505620071030342055100081d03180100d58030004e5408101a500242180381090788142e4a03080c01c0c0c90140603e5203640300781e5031507904501d440d842e03051f60340d2040b5080c01d41c165502242aa00040355070100d0700d070403443c0c615040c07810b0003450070800149411076100403140142d42c8a258180f80074005ca50000c07480c803440c0c400e0401540048102d2580070015141a1540d070400c044201440702c803201104d402e20744002440380c64800502040c2d486240005119106003840c40c10b841c0d64030084500e1200c0381c2e050004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 618896142 1250 618894892 618894901
    0x62401051b07030c091b0206130602091c080c151b0309070317090a090e030304033e100c05040909030e04051510030902011403040303140c0316170f 65
    0x38101500b07600068612010b03220003061161068202ea9100c3c1c401840c8501c1107058801c080783c550405840741c02d610641d01c0e080d40003080d481d4000d458a080018402c0d242030030040c0d008002014090011502e02e10041307144240d6103428030464448000315501e0f0f004030703c0d190760005051410a042e1030429030000c00850703860102001084081c503800982031036503040020120085810401c2d885101c2e0180c0c0c000850f407903e55006001d40400084001e44c00d5884030307a41910201020768806800c1c5000044455100c1240c120320300c016080d44c0389415084060000c220f0402c01407550424009040005000410368003808480480d10b03c1080012117038564502220740083c9800e441d50301904210500110f203103503d0b0850700d0420100c0360015249000e4400b5015038407071303000290114000e200c60301c101483c0d03070004584c4540311313240025240850641c41e03454800e0039103014045c0040881080003514803a07000da85046901d0a1102c0d000c0e075844082582c1d0800181460a031094560105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 618897392 1250 618896142 618896197
    0x11203030e0a0302010f0c180b03062e11030903060c2a0106151b08090d080d0606020f0f120d0e0a0506040204060b0c0a111207060206240105 62
    0x12607203070180c801512210511800c0080c0a03010300582c4070140782c0303401212103540c0e019200c141500b0141c2030b01c540c001850030034000b520344c2009011a802c02c2800300002c081614840071600003001d2100c80c40003c0b5030a500c02090903a98a210314400e078000c118400c01981d0000720301da4014500c21400b0f90350300c60f10a00d1140c0c1501c40b2901d840003168841c3c81000800c041d0440c0082c0d40424081c151102464007080b0307002c20202c801d5614401ca0750b0715520221791003600600c001e20b009000c403050200035940e01081d9500c00c01d1998125a03a6540038810a030341844a0030b400300718000106040031450000d13a8030340d0980300014444c0c0340005000c00f0b0f00503da8000c0c240042c4070000b5200c1c22880c508000b51155400c40d1308a214601e82003020503d1035401040e15441d83c1e401c0d005007803c41a5135501e5003d1030a010312560300c0001108105c1541c81c0030000c240150001d540078101350b08110550039441444000c1d40d0200500100d6104ac460740e1000c00e64140c00c1c48030305100d80c40c00d03403d10035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 618898642 1250 618897392 618897401
    0x61209060b03120c1203010b0406180314100b01051305040519150906050105040e060112110a020a030216030f020613091119090e070c08130806040317040b01120303 72
    0x300758242c040c0b94400990581504050510b8010700c40079a003541403518580c0c0e80030700c8240a00c103040101030000740181c62185002484040c032001210620319117075100c00003546000c0c664025103074485c00c50001914418001c000d80c81100b070034024100203801c00c204505800b03038001e8a014035541d2001440b00c551210f18032018262001c030800c0f00b02501440c4c61248102c1d8007800480710705015000409500c03400c01c0394102c500d0200402800e454507030044501421298101c01c0058454a0000401d0640350050851014030303001003903820010704d00a130800082804801002d0100c54042020038406007031003800540c11203841d99a4964625403505c507a01540000481e54074055881c08814176100061808402144030420290401c10701107400e400350740030300c815003580040400c00b45030250420112244c416400c0b079080c2440b00030400072a44007031740100300d654402c00c140018550841e01c03038203100401114140403890f0035118804c0040061107003d072a40301c82003038a41031521a500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 618899892 1250 618898642 618898661
    0x4150c0203160c030c24030b120706020714040603050d21050106020c130507090b030604021b07170f210c01150302010801172512030c0b0105060406120906 68
    0xd03031003450015802c10a101002e80c1c00101d6090111070401b088000c88040c100d40c480e540900c4140c001380c40700790110043c080300154036411845c1041c802e032480d4010b00102018104030341c01844424a000c1d02e0441400c50251200d0040d4034080d418400b040001c95010001c00c035504107201c44103c004a5000010f244c0418410410b02d0320380045501603011403200c48213201220250040d40035061011b084480a8460101148481c0400c0011403130311030255030300000082c0f0060520f644901461030b0114a000800c113150800309040c410390400001243c400700d1030100600d2100d09034160316940c2c07036001c4400a5604100b40703900036200061000c80e405061108002d104004c3c44c05e00501400700c2d0742c0002c9010801000c00458004200565a40d081c6107030300080400c0c2085559055504600c3c00d010703005003103074020105005040c02c2d4000c1c842d901c81e07554804d104105007000546100b0607000607200ba001044204091075104160043d104030140300000c51458914091300104031144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 618901142 1250 618899892 618899917
    0x3060c0905090112030e040b130b06041805011e0b030109240602010b03121318140906091506150903070e070e040b150403080a050906191704150c0203 66
    0x400200c0c1c0d4554148080c0450303417283e2110810811002e04201c2a03400b0b0702412504440102000469864503070071104d0103100141c41c103840e084d1510f0103190784186190304582090344070001013002c1c1c01c250180c07114150401000818032410f0a920301a9444180700c3c03210300703a45070589445070b103014800d030360708103030040000d940f040b60380360b102034042d08001514610030b000d10386d10514000004400c9444003c03038143d994030481d082002013000003046845030500c480c0e8034503e2450040b503c2c0304440c0074404100040584d440c25001141c40d00b5105203a034007105000340203103d000e449040b5601c1001080d1144251165001c0c00460702c2d1548903404401c000e0071a1062246d0181c200090140e001c006a800313010312482842841868500c2000180590302e04002c1000420030b400b008c1c002040a901e040c41c03034503002000180740ca420054140c03c8841d40d101c449190b00381c000d40403001206054480e4070041c0b400b03880d0089420900100454025203642c14103103024403d108131000c0b00d4070f00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 618902392 1250 618901142 618901159
    0x50a05150f0d0623180610020c030601030b01050907031109060a020f07031b0803040f0e180d0e010f030c0f1115130b07080c0f0a260a0507110703060c0905 68
    0x102d00c40c0c13110100b2000f01c40725500c80c50075116040d081800070b45d560806400503035182034403070506010441b52002c05240c210701131488000036640e000d1100c00d000394011031460200e54101410400740c180040c0189050503e8060700008408078802903410030502102d0b441c1d200c001d841c00507030605000402c02c00c014018001c001c820000d21300034084e0001100c900d1380b0307422516409050380e0b9110350f002d2001400c041d01c40401528051a10540d88200700a00e0200e41110400c483c0d482d05801541d030070301148502500c02c9055900141303a070644407081c0387c148041405201c01a000417101800c2004000380300744110341802c07041040c01c541c410a8045c03c0d42e0741c80c00395840e08040c07001381c01c101c400240d40d902291781e41d48168400c9005944c010000f03480d081c03412801c078546c2c1e03202050401c00d02200c0d60f0b680c6001c0c00120765141c0d403140322002015142c07500101000c2280d000604500030b0040c21001e400e8100380004480080d290301c4640003d00c406122001d96405085034045130340203600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 618903642 1250 618902392 618902399
    0x3110307030306170c091918050c040f021206010e04200301030c0902131202031009141c050f031e040503130f03021305190c0207030c050a05150f0d06 66
    0x40d40f050382250b0040c0401d00159040359002030f22021441c00312603110085c0d0380030908008084180141d040c103682000200200031008a000b00150840c0c01c0d02c4e1a00705190b43c6542d0706090040c820040040e020441c5803030528038031051000d102070000ba04102400d641e07071215840d00d90000c880030079205411289170a00510a0315558002d000c2140c00c0c008100700041c15240d14003d40318071000c5241104105c506006035103094150403082079030f16204801503000354052900c540074100703000710424600108002282c6292654941e040b0100c503440c00702c0c03101040d0740035003541ca0301100c0c031f9041c80c4c2d29101c250300c200800e10b1000c1241d5040300e043d42030004024000006050729413007403203e624016510302d45046502020f10006e1740140c421221000703241710380da01840d0300116800155040402c0c00c00c0280850300b0342d00038070340540e02c0840e00740140540e4500740d000400e41201d41702603c41c00c000100385559050500f15146030408981403803580500c10035580c0214550b0700410140d0365 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 618904892 1250 618903642 618903647
    0x30c1b09060f05060c0d11010f050c0a1706010e011110110408060705040b03060d03020a2a140303070627031e1107170304050a0f0503010b03060907120311030703 71
    0x1c51092074011401804002610305008040e1403542c05144040d000c0442c506100b65088103178600c00701055541c9030514180d9001d1382c825603009a2100078944c2d00c41c098080061301601241c101d4408001c00795081004070f81c0d20420440d0300d10800c0c030701440107c20450b800f910346594070000c014400c2c1000c0c1c1b01d880400003480500101d42182045400c507842d14002960203209034001d0002c081001c000240950a040607038200c090302c00d10480b001d0403c0c984034100c0300c4060300c904103403c0e2290b00720107040203000e41d11040074081100c4000d0b9001d00741800203613281300b0a0802000251180c0c0c10307036a16040300e2030b1034019640e2440c403417510b9140e618008000801611828250410342c40030403101c03e1152010079405203011004040050030810f170071100c2000d41e80c11409074401040301041795124888a42d0042003091070600d40749040c042014256001c001c1060b00030b80c4440c04000450b00001541000c440c205000400b02d40942d06080310b1040c2c3c5085c07420300b1880001001000c056 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 618906142 1250 618904892 618904901
    0x18041e0f0609030f1803022713060f02160f06020c03030109020903100c0e22090614061912030c0803040b040c080304180f0f06032402030f04030c1b09 66
    0x14440e81e40c2941c9070401380d00a032540001e40720040d42c050005034040c0014148545c542d00c55030300c5542c0f13048506101494a40c001f4008880300e0081c00000010141000800d004416001d282c0e5081981040102c40c3c401e1148095070b07502400011425801500384551a0704030307100b0a401c1c1d0709a80d0b40e582c4515146029500c01100c036402031203a5040742c032041145210303140d10250f003680e84a03180320000c0100450740b1020360359a00c42c07084c03811649828400078860400d199109140106001d0000c100721100400002d00090192400302e4400c0c0340082030b00840b100340d03440c0e10b0310300790b43e50854101154141380c0300300300400703104000040c0800d01c8240d1018610551180941060107a120440151280603501c2001c1550f00038000c04101d00045400031500000c6d60500020483d004100c41801e5401541c01075071b8a240c0950800c81c0510741c03400c003c0d00540100c1d819071450401c0480c2205101c4c0040004d030030402d0101c241d0f010042580311501d03651250410074203149840390050720050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 618907392 1250 618906142 618906161
    0x92d010c050a1d0a050d1406010f33050c01020f0409021209150c070f0c060c0b0a0504030c080918090309030c1c0323070302030406080618041e0f06 65
    0x1a800c0807296090400c3d607140542242c1014203545a05031070072003440034514040f11304486121007064808511141001400d00030000c24601c444070130300e042100d003480384000c44240c5503824018198244054502c01c1c6840001796440c240c1d65444461511714028058542100381000c40064001000035542e00035001c14810725684203290780783d4402c40d50f61001c480b801021402d070380d400000d003140300340d10241120340c1c01a000b050304400551f44684d600c46a5400640c00b060b0780506000922419404140c0e104040b42d00070030003410700d514054000c940e074400c020b10f880400100c404094442015100405103a8104020f113400d0a9011684030b400031400b69000e441204a51003c2e0300c0c0c096184400d03112200a02d4254249607101200d80480e403041035400b0240308007018003c280c0c03150003840300728000d601842c0c030380381020301c020100240940140c4c032034103c051603295070030100e8042c283c009070b000001510140c20b00d804d03416910303803000c0c0c054505030013403004406000042d0000b0400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 618908642 1250 618907392 618907397
    0x50a05070b0405130506031002090301060b0c010c03061205031911011d01050a0908070f0503070807060b01171e10080d05090306060919020a020319020d1205092d010c050a 75
    0x40008801d440c1382102d40c100e0359564998020001c405080389941d000b054980c1020300082407103925402d004440c1c0c3c0c40a00341b50810382d07403880d4075000d203589841420040c21044000700100c0c2c1098517403690b40c0c003c10391a82d80107a54400980700e12800380f40c5954001131014000d00443c94404c201c4448414440000507141d400e00e40040c0c110180c44c03203403184480e0700822aa042040d13546074000c00c04100301c000c070b60030701c02004030f04003003076200000d4006d6a10410b004508211524001080b8031204100400300448207010301943c0c8a81010079046107101118001ca40d0b69140360070403c0c96010790001405001e400c0e000415558000300030150044150b0031200a521040c0a210050904846201504001200c0d112109026030024880c54501d0320491781001001d0f0340030b100003020558a68050b91003155030b41c0a298010340148591003401e541004649840b007030b41c0d038503082039440714030203206508042d5940c110a10108012829a00020016103002c542d000d0115800030010202 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 618909892 1250 618908642 618908659
    0xa020d0f05100e030409020d020c03031f05040c0c0318050a080f010612030c17040302090a0605040e012c070e0f07020609190809010509101e05180d050a05070b0405 72
    0x2054800703010f085040c45140c1c004502d0586009516802904102e10711002141c0800c81080350031000c00c05140508507044800701e000104054070500c901455111a02460174140628450341d0052002441e4070f409d410140c14070802c0101801000d00180c200907800340202c03401040e035143c0094000d11011902d0020810381d07403240794400d0300e071440c0e1400400080241602d0000a45000d46610804081c03062041c10651241c1c009002d03c5030441e20390020781e6941c0d2007082145480d00410b01f0b02020b0100070000d4100001a6030707070307400e40d0040c00c821185c13a444041446980410000d8020b014480c24640709003445854000b001100f515140014440c0c00040f60120704007040180100208094502040e5020b550704241500103100c00d42c180300c01800401d460780c0780c08007101203c0c0d42503a1214034402c02d2025825548496261503410044144881e44020307020940c45c8010b1282200d56a002182a1402500e81900810004c1650150721000603820104602130300940707804075201c1c00d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 618911142 1250 618909892 618909913
    0x60c0d0e0103140411061308011a04180c05040e100905010209011119120e0402070b0405210403060216081305100518010809100603150509060601050406110a020d0f05 73
    0x300c0c0f01510080c14280803242e8012051a1100041119100345d1801908050790b030402c540c21a0615901801800e00b04404c400d000e10b0300f0721540c4c0748940c44810440440449071280304076036403580941c078092545d0f00e100280d41c28041044640403c2200d50520080c095842c3c024041d4012030007107404200b915406c4040040e010840c1c628900070710504a8000d0f00b030f80c0720700c86910b5481a4070414404850803d0805031124001424114090103100010341028940700c0c2c502100c0350741c0529405a0b262000304aa035100084a040740d400c543c016858046054008240030541c00e0000e0030441c0000701d040d90320240c5d5a0440c1150801c80e40c4c10f2814804c144182d80501c100c2c083c9004103468003c2080c0c2d593b016005103a00260040116088113400804010880c0d1803900700740c03181000204428103219a5002c0c0d00e038803407010806031055043c00e1740060200d004900070f040034400f40c0144000c50040401c040c1088580040019003c1c510034146190403540420781900c25009062141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 618912392 1250 618911142 618911171
    0x60c3c021003090209160c0804030302150f06010e060d0f020403050d11010203270a051e0105060a0e01062a031d03012d020c060a0b01020f010c020d0806060c0d0e0103 73
    0xb1402139000703071280b00d80e669400b60b034811244002d220f82c002c1c805c1c42035281d000716070060003400195100b070f00204a2356086588502d0304100c010702028082542d0004c21890303903407000c1403290201e81545c049840d404000103620160600c1d0b00b40c030901c030707202040c000140540015800642c41c129121610f28000380105603080c1d01c011103101103003201d1909000c10101e0b00c1061035043d104050243c80508003540e580a04000c400c2c03411032424034440c202004200c0c0203110780c5070000c07001c840e440e44c0d59240c038085c056210307014440e0f00e003400800f00072407940603001c4503c6ca400790422256510010110300d00030301484591a03a42104203a140f00128003801c051260303041440c0c5100c03000c4030b224081000101006610040003108940074801040c46100400020b801b40c615481e001c1148030303545000a203061405100c510903603040182d80701000741c0200c0d50705040c0c5428504441c0b5581ca100100380c181c890b603070114501e4032624091010040d0b04c0f41c095410100c003640d09100c2d107000e007003d6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 618913642 1250 618912392 618912401
    0x7091d010b070b1510020f0f0a05060718080d021507030524040b0301020310031e12030507170702010c0305010b0f0f07020a0e01060807120204060c3c021003 69
    0x701c0c1d4502400300000d4000c41e00942030703503a00101140c1e48040100c094008965000031010700c10016a11100005000480074007210340c4000c102c00c0241f04130f043d1601ca003944c07004080d00c0c020501280404a800c04103106c072046001c0c19a1104403400074030f032120001d581e00950010154100900d030041080984240201c1d4090840f40f0000e401e002c803654080600100001d5103140e01a51700c5044004940f020700145124010480d2104400c52460801080700c8140d03030620b400e0f55218921000010300f1801600c40c007040c151400240030f654140701a107002c504007090044138480c810410002c01d60540107000080f074241d60500c003d0340e0300d01030b69416028550342241d00075800d00002401307c041501815943e0b0004110b15884c40c4d80d4501e840d02043c080c1c014000144070f0400300051290414048401c1f130300c0ca1a4110310381498030b10f00a0580e02000c030001c02c0340c030807000e5469961b4049a03c07064116241d400c100401d0201e07002c00c04c0c12159450302240035040000c81c8c251014068800e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 618914892 1250 618913642 618913649
    0x30f050c030d0509010213081515010807080601050d02030103140c0103020f12060a090516030e1504020d141006090b0301090f0b0408040305030a0509090603070810111207091d01 78
    0x31030074500410070b001e002e0080100038501c290f600307001d47d94810145140d1100100741010247c0300302d20302c0e014003a40400340100900e08202d042e402c03a800f680d038030080383c940c48001860b01d00c901b52520f1004840708c1c403406452513200c034008000030003480051103000c900910010200c0f9000b418020066003070780201c001d696440a001e00850b159200c207100384076403024006000c4000c15448401c15403c44800f070703c40e08171b801515a03101d611540c01d881200034003000c50008000100359101600503648000300020301880030985000200019410f0044440a01c0c030185c44480b024102e044005181d907100e111301113401d0408171515810180300305200644c000321007251040440e2039958007104050801c0b94a50380030400000030580900181103ea0219501c860b6185288800c02c005510084d00d814030980090314104400c1d84c0000d0414100c425081d804141078400d0528008a80201e215442500d107602c0d04011605601420340815560140895280d01e00b2110019010580900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 618916142 1250 618914892 618914917
    0x3140910020a051608090307092a0c02041a15031e06010504080312150f0907110f1e0d1701030201030911041d0d0509090c030a0b0913030f05 62
    0x110800c6140c4481e002070042c11201d0600a00c0c1c00c0000301620346010302400c090b51652000301d111111442d0912a0600038901c4140500044410700f1514003001c1002d052007602d0710f90350b0180a039550083d0302e00003006030010710030003449038040c0d00090312003040003c040c4580c01002d80110919210030582c0c0c00f03030b240c03501c030044104040e010904425034040c02d014103104c1e040c0000602c0d10010801001e04011540504103d42480c004e007140c0000039401c050700c41c000d440560403482c4c03202c170486940401ca91a1540c0707641c03802803541d41491568180c0071100d01901d101c494801d140041460300d046415400c50300c81c420b00b45000c80e864030701c61352003000382441140104055071103070300b210170135a018074010718402420f000003070102d072074100f1066041d801d484402417080c42c007400b0649a0240b24181a8646040600020582c1c0c6004250074560007000c40803542050b4180c0c81400092000340c41700005003800d00d07100440394441d410482c005842c0070441c8003480d1080c001e5800c01c89000c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 618917392 1250 618916142 618916153
    0xc03050715200304050907090e15030a0201030b0a0518010302330a201b03190f110301111309060e07030905010b06180a0e06010c0b18030703050a031409 67
    0x5850000001409070b02070201c1e03100c1400007203020f940b00748043c4d000311002e03140c410b9043d25201043c1c042039002064198400c1020000400d207440220310308038041e509182c0040c0c85501140020555903a54109070b4012420314004160000051409030580f4001c5030300c00c141140c0c40e09042039030002822070041e689582c40c540044454514003904162030503052569a4044044204045426800c060282944a241c02c1c51462104801613804160150050411142803003805501d80203410002402c0240c110300403400d01c5401c031010200310354000c000b840310803011240484190802c43c40c40e51070850303400d40010320628510a2604460401c403603120340ba5a041003e400600150105956a548804016031030b6900c04004111100d000380c02a0400c820800030301000f50340c03d030481012100c400e41406456a0840d4a5600440e40951401c2050f1f44039100d030040d0321002d514607d40783c0300103d0b00000301a00003000d800060340d152303002c209032510a000262281c5044c0c90020407034002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 618918642 1250 618917392 618917417
    0x2a0a030803040302011803171f140a0b450121050c030a061a09121f090b060603150f04140f011d04080909060406050d0c03050715 57
    0x80300107140d010340a4000010302500300b4000b10b1240600620440009000c0410b0000401c809401c1c035400414005d007500c40f10b1913259040712451003c2c0a00c0345001c4111404a011341d58501459003e004804042612002100081003000502c420a010301811002020303607104c1501c1e10780d007800c1c1000300381200e000301c06400569102c0100c42c402002022550f078940d4105085006441c01134454182c41d5a4910b85411120125021504110841c0340d100e1200520b030403101055400241e0100c409007120061031101528268900d10048078104181d03d018018103600e50014070840d01444041c40140d80707800c108441413000f140c071700d840303207030701130b407a04c3d201c0c207104441e450702c2c0c00c02400000d942d1901c0300c4540b949117002c88105501002c00c20051221109401000b00800446401c0308410708040d035405840d4018107110500500c04580043c005a4840d00414018140900f031080411518100000300070020300041d61140f0940d000040e540d06810170381e000e4010141d4030b18a01000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 618919892 1250 618918642 618918653
    0x42411060103120908030a0e130209010c1704030b1003021c02010206190225020406080d120f0b1c020a060906141e160b070212180d142a0a03 62
    0xc3d044281010015641004942000100000c1800c40c00940362000d4400200c07007000884c403512078070305000703d0050081d5041039130090942d40c0d1550748241c150742c80c0c030402010401980603ea1024016a40d103400348203000104501c0030781542d0098400e042400d050510b15451a0101c1000a0050344907800041d4074070421482c1681c1d19808a40140c07606c49485104140802c1d0b00014a84580840c030300c0e6070851806129141c000d20f12800a803c03201d480010250112035608209d181003501e511040c01200d100780d01194040300018612100000d110805004540e03034040203d000b1f00e48403101141c1300c5d000c1d100f02d00c02c032082961103401401e07004a0a804541140e944000748041100c12014800c00c030001034501c0f503600001704c109883c001c1c14150034010340540040c0c10f540005e110a160401e8036411503030600c0000340c035030b421001c501001c00c0b04680804005801c01c3d950001074040104081100030383c42c81512103a8002c1185008890403003540d1201440d8030041c0c0000130000100c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 618921142 1250 618919892 618919913
    0xc14010203011a0d0605120c010e0a0e06060711041409010c0e030601061b0803010b070c0b0a02060a02090319060e0c041107060915050408090913050a0b100308042411060103 76
    0x142d0f03402c13011038a00e5403500404c0d080071080441c0d011580002070f03030029550b4084521681620100d0741060b20340c3c9801c001040403c005400030340200800101c0d0300c01c0c050499a0007800303104c0500208401c07142c48448107210002901d01203055402d18800d40c2d80c141c0b0550342003848000c01000f0300300702d911b096800c1d580ca48403d1008140c140200080c0d40220302014091070081403d4404280d0310383c0306203040c00f02030040c1e8004182090f0f041c030000d28660b0340011400d91020032400016551015480000e20340030a1503003200c1c026040a04140402c11107401c401e00548441c01201c220101003000c12065070f40003089250303050011300844000c104560011010a401340890720f0914842c0b215010603178004440950302140001003030000d0b4205604269031203501e00c40301600042d007a680d800c0e11400c4031280540150034450214040da0064485a130041d54884103450381c890341c035100c400e0081241c41c0011a14806809221030050180b84d04642c9003030100301520700780c0c3c21503a0342e01c11325 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 618922392 1250 618921142 618921157
    0xf08061201051006020705010c0804050418150c0f141e0c0d03091a192a0306140306060312180d0302060402101b0b04020402070b070c14010203011a 65
    0x2125003242506030800a108950191085076904070556040010191825071103030b201e02c2c104a039143c900004070321010207440980d2000c4501042042021441c181d1040b1000b0001c0c00c0c0341741c4d1003550318a403111a44a0b034600c0420b6240d504110300d0360381082d10780c07106103011000240350400180d1314030072868503008084d100141c185404e1400780c1440c240b8041c81c031038541c808640c0c2c0b0f18a84040c00100003501158050310041100da502c0c1960300000c069260f4400c1000540e110070810402c00d40c04103500d58950400800004164041d0340e0050140c1818480e0055400101c1aa525242408101c0d1880b40001038014040c114550448003080d9008403e0712402039920207104902da584c64103154a542d001781e004160600b03181c01040b1940d0010844a800d101a102c54050400c01001e0030290280c0c0204640d040e6a40398004074001e8840c40b24004c02076044941008441900080840c10b101e01807109030012104100405d801c034842030191100c0070032204009060341c0d01c42c00091008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 618923642 1250 618922392 618922399
    0x60e0f0c030c0a0309051e070801060e010b09010e0411161a0411060a0912141501080c0105130b0403052808030a091b0b180105071203020708040f062d0f0806 69
    0x31f200e13040c00c1d0003802c0300071402c0c90710305030090001084400000d01814002d020764401c04256540343c03502c816840e11414100030f05109403042e8529407070f9210313071022060810060134241c0e81e40155203889407400306407030111200c04d8129440081e040914401c544502e074001c0d819142000328030100718060b001100b000080000c4140d001c40e0342014082642c05191140807554030610349265040e040075221500d040224118600410086400080544c1d40600030700740700303544100d001c3c0000810442030b00000ca040d1000100041006000946010442e0160031f5481d13000b41c00105449080e03030005000303041c1c501d09001044078680503910074452103120384a41c41a0309045c00702110b20452540c072500001c4004200d041c20f900a484051400079400d1070300030701d012096600c0551040c00b035401001003650100300f04081062600c00ca030040c000f1200411012945c82c4801044408800807900311a07200740c505a000120480b40003058032025140e10100107005c1c2001c50b0006001040701c1c1d2f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 618924892 1250 618923642 618923653
    0xf0c1803110310020a0203180d03080601031d071e0b04060c0b070e09070206090c06090102070b09280f12051b030111071a28050601030f060e0f0c030c0a030905 70
    0x2400c80d450310003440415170395000b6540760340144040b003410f800d140744c155006640011040000070350101440da444442400e00107010030540c205000601844641001617100b503c134041140c0e4052001181d240b154243d810140d151204aa840180114421300780801c0f00b8400000024480f102c44540c407075554580142854003c1c4001030f0640700a50f80100541c00072418004021f9050181120f202d40954040d840c049400c00000d50340d90780f500c910502050007081c020318541d500e0203442c1e4020407072861907107030100e01441c9140c41c40380c0d0310070304032802007009000446e0a80e03504880b003c140c220003c1c0003620b00aa07248d440f40358100d0149035255503140e0ba07100800d100300d0050155503018400c0d10b00b06100311000706202102c040c0c03109100040c14402e40c101c0321b0503c0c00200d9600c2e482c00703010030940c0b01c0c0744c0140d0140051840c5510a9402c1040200d2214001c01c40c0a100d2000e20303480d00f04d07640760410303608028441610f041c1c00c0b40904001c4984103d000ea0061544507100d40c00301c1c4d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 618926142 1250 618924892 618924913
    0x307110102151e0f060607021207080609070617100915032901051c0f050a0c06030c0305130503091e0405070504180b10140d050106030f0c18031103 65
    0x896a02c2e0842c0c0030240210a058032005900d201005954401c04000f94002a814081c000401a0041150080c4140d16602210741888810b12804008140c01411030f01c3c0380c00c0002c00c00351a80c01c503004038000034410381d0b0484c21910081d02c45034001d0324000404400346060200d85005032407048a40d140c840e95020000002a98801042d040345d1403462070084c0840040c03020086800043e030189200740114050381840900080b01e0642c1e580d442000e1685060507843e0042c00d1114040d0043e01440948200113402da4058000001906e03090b6020000790f07984240c1c02c8003001c2c03c007201620303691051042042038140300821101c0d000c000c80210815812410005042d075004407220000a640450b041281652800d045014442c1c0c5850078000e620700c06000c5410700c1c2034101803108001800b0b054101551104049035074001c2c101c40c0512013980c41d41d0010340135207900f0001c00d40151418507803142d00ca2056000d414410b0841c507101044a24548806140225000601380e050040242c240c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 618927392 1250 618926142 618926173
    0x2011103090306102909060703090902030f01091d06040b0912041509052e05270109080703031209061b0905011b050606090414120405040f0606020307110102 69
    0xf900c80e50200c49840409400d00100155400d20b401c03170441062030794105071030929014000d851244c0001e407285602d82e161230808403a0300245600040d2480d00c000180401000c283c0c0c1c000341601c2c1c2036101801303044650034641004844154a00f0b00319040003010070000b508480c0f40da90840f401408441c00c1c1c1005088480c00780e4090b40c00f81014050416030141c17629001481d69000705012106244000d0070540746075034010910326049100b40000b82194006400791050310303022025502444007841c2500f48165072600c1040340d550100b580008006850180000c1c240140c0364560344502454400c681254060000007038201d8900e610b86071144010b4029004c0182c0c4e8405d2941e034444801e1074040054401c041d0742c2021340352100c0c0580441c0c0401c0340000c6d03168100c00b0a8440790786590303a500340400004822521541c80740030702c030b80b01c0110306401406007065480c115420408002c84030070401c2211854410840540c0092008102103030404204076500a8180155214521020b500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 618928642 1250 618927392 618927403
    0x30b0307050a0f030c0f0513020c100f020a140a0f030e0f0114150301060f030b04151a030f030a08040f1b0f090e01090308180a0807050105040201021b010507020111030903 75
    0x4040c80f5052101c10400d202002c0e019000500754000181074450500020601e901c002c252140c82c0181c0006614110140c00c024000c41160b00d1501000a480c041200c01e01070342c4200c408500140c0231200c002d40d03010f189422510152240e80f2015020100e101c003e03000703000716111010341400b075100801036419080c001c041102038501d01001082c940108024054820703c241240645e00d000d405209010301c2240ca041641c0c1c001c00092039a0781c552800101d40011354030414851130034600c0030020300d000c100c04050200801c506a421565039040401e550b4020744050600280600001c24040340d0303000000704410780246100000f44411000f402003842840e404415601e54250041200040c40d00c9040d1658113410000d22201c921034800401481000c0d100c200d0200d00b00c6601101c800d0200001136005a2258041d9101e41982c14500e000b014100c034103a0240c02004251414440725880c07480d0030b183e05844903401e00309607400440780d0b08020041803405100810900d5850743c0c08028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 618929892 1250 618928642 618928649
    0x6051e04080f060403110313061407060e0706022a040c02030d090507030b090a050d080709050a03050703061508151005031c031a0306010b0c0a0812040501050606030103080a030b0307050a 82
    0x1d00c0f080c1042d140003000c0c0c40d0303c0d0240b042c01d5001808880c0b021012100314a04030b402600d03040c42144010303803d842d054490880020046442d00380110200e80300882c4071011294281c080c0d43c440740b20404520803d0508003042341c00500d440d1801d8040d8030340340e8841c650300d507a144100c905001044403003008955030500300380c0c2c66a209038020410089141009075200042c1405418401000e5031740540c1d5550706c0685905020042002a0441d8824a0a1001804014800e03d40144c0d00d04065440b01105d000941d01300d07042a110000001d00100c2c017500b12412600200b00300720007118604024000604400c04c1203c0d600e0340040d81d0b41d020480c5100c000d40401e0400a50080942c0c0541143c5500450006a403e00740e8015110360740410b02c64111003403609a140c2e103040032800da60074071030800402081c190380031500900c04039a10045074480c601c508001c05c070303944469040100c14003007484010480c0030308110809089102c1d070001282050b02908030750405481d00c000843c0c2c00103682 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 618931142 1250 618929892 618929923
    0x6060e0a0b0a230c0d03090807170d06090b030601050a050a140f0409030f02010c0912020105091915260a0b04090605090c0f04050103030f0c0305091c030f0906051e0408 74
    0x2204854213005110b492401a40b6060400c00100035681d030361810300403190068406a041d09407204912030000841d00d240e041e52000700802a155110b0b4801400001c030120700a1141c400041028180160014103889004003084106842c00201c010300400307a1a00c0707600404030010081d25521903008025603180319450313500e490b008000c0c0c001d084031890744c080782c10050011020000c1ca201242c511020540a1a00360340e01c3c02c594011070070005171100d413000e81c950346c168002996580090300782c03030395815540d90212010080c0400c2c803103105801c1c4041c224082400c0882d1031101c2541c0005810320000d04042050381c0c035502c0761801c5940c00c442c050b9280d0000c15225500c1e20700003250149500d82281c003084194190348004018400c0310a482003401810140c035010b03d80a1426141d08041c01401c19a40d10000409016181c901d000106c0110703030301a00e0b0302c81981c000e24a080a40b100c558035203040c001144c0e0505004d01d001c0d218011117400812002c941d440e0180b01c400c41300c07054a03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 618932392 1250 618931142 618931147
    0xc1419080c06060a0b0405151201080a05071509052209060209040f061202210a030e0a0608070f050f040810020327030702040906060b03041506060e0a0b0a23 69
    0x7071030515800402240c8258101c40c0244601031481081e1400d48400f624945450507126060380c2c0c1c0b40c402c0101c0300f040090680f00005440c1d00c0000c0c1031825520460680da0740c00d588803d1100510642e00615021070300100c0103001d1403c009003880b1902400303c6007000b0400d90801500c08844a03001c0644665400103981451428940900b41034800200700804c011450004989907004103c1002407203104a0500f003a48844129850828140d01000356070b0358069a140143c072a950b441002405034180110004980740101c40841c0314120380d03240c24140307840c8100112800e0b8402c40031091000010311011a01134400c1009032031200318210010b030f6a00744514500b110180240c00c801ca41c901040fa80c100c13100e80482560001c5a068a0109000c00c492403c0340152600303030030101001d1130200410080c8120b21140d5901134400c420108103050300c1d5502290510402d8080c19001001c611040200c3d801e228006d0000c8801031902d000782e250100c0361050142200c1000d140e196002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 618933642 1250 618932392 618932407
    0x9060c060a0b01020a03020309040c05071a010e06041a0f1909021308010603080a030515120606090a06050607080309070503010203070f0815130f0902060309010e01110a0c141908 78
    0x50300c10b002c40c0250034001403100c81c1107590002c1d5284584201035000f41d0f02e8032401c40030f0900810656403c20381c061050408041c1640304192a2107003489440742851801d40400c0b03060500d8483d4044004141c0300c2c0b4600031a1000503c06411644c1c1d8001e50000800d000c501541a40c02da600c5000c0c0038000005a9501c4100000c0803640101d600420744036450243c0070000500000100c1c1c00740100c030704010550717549910100409440322080c2c03541048020300b102d030703d000001c40c129114400441d105040e54450181d80e804a42542c000c0703c0d0440ca0030407182e030101d0307001ea01456000300070204482d80b55450304003280c01da030010358070003000c54030140c0c01c03540454101c42003a620480c50802c0049070514140041c4c1c005480e403110010180d56441c0740d407800c0c0016003202d004c0740c4d000780219969003458001e19000f061088a04403040d46015400c0011380028000c50358100758076500c02c502d05816481e80059440030a40002031031203060800005801c82182e0030100a024442c19602c1740d05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 618934892 1250 618933642 618933661
    0x509062b0c0f06020706080a060806010b07350d0f09030e1e03031e0702030d0e031b1f1b05030307031103100902160804030c0807050d050c090c09060c06 67
    0x482e4000120000c5881c50600c4690380c0010b4210880c3c02600d4000341a13100c0c1d860080042c030403500b010540780200400801c0e04201c220041051070702c5407110307151075070f140c403c64002c1420341024486000044c0180060b101c00c00e0f07010303141808101c80c001480c5a420010700702114880d080031000b1601c000e100e8a5189000d109101d102001c00c9081d0074010380d80000030b52a4031a0781103101054005c411113202c000540c0c019690071a81c00f038225038210f051090064090601c081c5410f101c1d1041000c0d40360500380c84903400980b4580500240280c0110321140051210000403000070081d21424000c040c60342c1070340310000b082c0a030317015503520305203107400070240d450350385080142c001c0c1001409102118116030b072040322003280f00181c0301c40109110582c00540701c007011703010307650120340030081c0300d0741125100884400004884025940b80c00b400655400310001403c82d800888a80b90982040301d402c65000c5640414185003585400000b200354005091b45450b035801842041307000c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 618936142 1250 618934892 618934913
    0x120108071a070515040c08010f05090c03011a04020f0c100507021504031205090c0d080d0b03012009061903090302010b03120a1803020d03080708100b040509062b 71
    0xd0720084028600407940d210300e960340c0d0050035503c5030740c2d108500150900003000c4900c0050b05050f402403280356100400b00d005008165100c0000d4003035041a4a8503140510503035003d002c0703000030624080c1c4a001004000e4002a2460003ca4800c010820080d041130220000700c141d40d03100082c0504001c80002e1901150291448003d0030920500004c242c00201c007000c0481100c03004900c0ea03607628a050704140000030300704d03003115080444004010b500005045918641c68042103c07104031800c1500f40e81d130a100301207c85502c80d24042c2190035110040401c240302030196840e180c06001c44000f4031400054203c0001e99850f040c504065080c098211101001c8001b80041d0200108060881c0320b4200e0380b2040c00403443c0018656540c1e03081a0006540081800c0161199420040c02c10305084800c08001803882d400a001448071000d4802902c0340e0681c10750505007400c05100380e03918050701850f4031a0301c1c401d096240340d103040c03400b440901ca41e000b40c40e401c0a103031400ca840c26 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 618937392 1250 618936142 618936179
    0x303010303171e0a15061106090c0d02060d060b0310031203060302010806061308030a08040b0c070c050103050a020d05040c090c1106061903080c010209090a020c2112010807 76
    0x828041e05004601c0e010382000c1d99826409050f681d00c684800d880780c0014200100750014484030800e000075800e400002c00c0c4601492a4103441e401e58580120586908001405550021042c00e008025040500c064418060300010000b1055100e0440001681080701e000c420b20aa801c0c0c1402000101c04d8400c0d203100700d41c142407010340d045500107030107000020300040c02404080750100440c2c1c1c600c00818010000c035800c0c0c80e903c200446000305038001c2241c064542c1c2105502080c0709003036110494900d0b540090f516600c07582004011000342c1005020201d55580900594020783c0840c4a264019817050019a03001450201081c050b14400c0d982e000038058034809140c00540c000c03640340d40c404412202082c09180c0d0182c80080002d1940001d40701d0000428001080a815401400e0a03001140e2850403a96a410306c14181c1c89001c042c1204e0750072182d41e8107080464441c881c4d80a0220800c0356040c00700310010340c020f0313032801d90043d8801d901ca010100a0f00202001e40c2404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 618938642 1250 618937392 618937427
    0x709021c02131e030b010e0f07020d17100b0d0c0f031103061302070f0803040204050606030c1c180c0518011505030a090c080610230d17030403020303010303 69
    0x3021800c80c2c505022070258460f100710244804508980c00b1509a50790024640c00070390f55180303584a40b044000800121200700d14003c0300c0003c94401c07800021050540c1041d1781d28040b02c140382c0e0002541181014000000c54000e40d0004501c070b0f6582d0020348a08030464100040030799007c1c00c003d003400c12510070f03401410300d4102b07110042c94111040700e6004100765801c0c1c0e060726442c1c00c035000a20514201034080198140b100040103c039100843c00750380200d80a00440d124241007009a2106861030520000208541005841145503140c4100442c0c0c0002400302a907088001000c1c80203101212810034001e8240102d10b482e002031300150007a01001c00d95036040a03003c1c910840c00b0481a000d00c0404000911040c4290304000400d42c2d2103004465003030340c4c3c1c10100360f40d810180c0360718140b041110004205d4608503d402480c5041004034080031140c0714061100c0c0103c800000c0d1a140e580a010000d01a100303001540500d109500965496142d07050040100e64849c070941c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 618939892 1250 618938642 618938647
    0x72102060c03060a030813080307030c0c050306130b250906020f0604080901121e0605010806030615041806050f0609090d05030103110402090a03060b01030b12061807080709021c02 79
    0x2070700c0d90084c1c201a260303c000c0807680c58100c1070102010350100e900c2140a4400001c00400f050340c882e0100024510074194480503649910402d500c544088a1541d01e034072110300d035080030481d800640741d04000c11887d0b8420070801c034015100244002d10149001c110304860410410b5810071100031181c00c02c402401a0341405e545180c030714840c507000b41e410415180d4003072035000b61503400390411500360707440289023076204a0b80c0c0000d0100c0c1e2003014041207080f000a115414081161480f84080302e030b030728041100000c1040300508002441d00d05540854940344006450f41c0318041c0100034007032070450b05103080b4003003050b0008014012a4035030401d010b00740400703402c013040d03a0540381e1024041e0b03041560507022400038018402c03941e600a540400000a014171a400300f08140b00031780e81031082244000c00d00158040c00c240c00c005e154042c90014000496003d85040b2000100342510320b19603a402400b80b500b0243e8200c1e0300d03600c0d0b0001d2003980341c1c203540140700e0185003030000550 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 618941142 1250 618939892 618939901
    0xf0b010620060112021011010504030e040b031605120f0f030c0c01230d0f021c0b0a0f12051507030c080a0608100f1107030207031403070510020708072102060c03 71
    0x1350ba81e070822000f030043d1704035502040000d0140074031034a00c3c290f11008010510b0f1904009007602e481201c00c0307004610303180301000181404120902700d001051401020300d40b42400340001c5800c080d0721032070140500502e10414141c140203040280c69403600442d2140c19031035045043c8469401558107010a0541c0030150100c4075041e01c0d8080c0d25540c0e110344504400c900ba201904911052040061000600b1000094611040e407020900e1060401185940100b07000c00d0701103500600026a804800404c0301401d040d04442881e81700d4810307a6202c0c81000900f1140100643e02c3c1d5003c01e449980d0001c61a610001d80c40e481107080c00c080c000360b4905160340d51211b41105040c00340540301c0891420200c0c550f00407034074030b080d0039158650b0351a042c10000e480340c07451b000465094001440f0407480c0c000c000142e03442c280d0400080c003941d20048401750020f60006008039180f1000740200400b05068107290403160b018144608aa10800c0700000d0429030000d005a094220a01c14003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 618942392 1250 618941142 618941159
    0x118050103050a0803090718020d0c081e061305010e160513260601300503030105010c03030f02030705040801050a09230102070804140a06140a0c0f0b0106200601 71
    0xc4025412140d01d80d629180c0d808087d0509041c0e0304001840c881d903008448207810564001d2204809100c010014020030383c2084030070702401e540450941d945000d00d54035000050302500d03005800109000c1c0503101005403002030368000d9000326080103e00c4100285000c0c0110300104505491400d07130714080c58820900c0711004c0f5405840300b886032000000c22002212001400030341405001c0f1216503a42e0580c580c0600c02e4904401070b00103c00f400d5a40c1c1c06a0103000301c20f20303a030007400340d03045a0030a00112000b8458500c03c1e0101070304c40f00c0d03024000c0c00ba0b1000390b00030309155031520341c0c550400300c0391801d40714041e201c0c5190301c0c900301009010481200204a040c0480c401340c02c0080011a1880d01900500a001e04207082c0000c000810440b0440a039080350340941d0301905a40c1c0e00c000980340480007a048111405041051581103403181c081550340380c1c4200f03540140c1080c1c039103c00140e11002d07000b10011501c201b00003501d5a440b0121482c92a030710800a01041d030426111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 618943642 1250 618942392 618942403
    0x20601030b01170c03250b0306060f091914040b0111070b0a121506090e100e06131404033902010c02330f07031d0303070803011805010305 61
    0x3c601149107420040c515402041c42160078003540102100c0403210a5004840042c0c40c0020581c80c01001c0000065089241001e403449a04000d0000307051502030a0784024903880802e40c1c4d03501c0112052900c401c010043d20b080c001d070550855440b040c088400c1404101d40519954a040c00b0406e0800d05440c140090301c0d0098403445141240ca0b102d05141c01e0301c040c0a003000a19070782e4240404604400d0b07482e01d00c8401c96000f60f55500c40781c3d9958948075008401920000c0401d4103049003031052850380316a0350b82260010b02480f60310307100e8070030000449110400c40651603194200f4403043c0f640c00b510107241e0a00d80f5160030440540f0f2883c94041e00050646251002000144135096a000d16690b05440384c01400208400040350300105800b8814407040d800910504020724140d080e6505030303219602c0500c2c2013031130085240c501ba5078503401e0400e040841c2822030341c13008040e2418070190440074803038408030783c880d4100003266072110307220b01192021a02c5d2800400c0401c0340041c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 618944892 1250 618943642 618943649
    0x1e0603022d04020706020d05060d0302070e041a07030f061a160c03050a03050d050a0203010515070c03140c01030e06040c170c0307180e0a02100f210c0906020601030b01 74
    0x20340c00c80565400800d1416200d006076115070041c80460000140309240c0c0082400c804045401c00c5141d403071801300b202c9028200c6000d00184d00c040c1c0140000d0b5081128142c01c01e0040c030465007841900182e0519088040321398900094450082415404050040b900038107208800341b0182e1190716070701c0125015142050100e0503003030f0002010b101040c410100516001015250110b0130b50070040d18591003a8040090a4500400244949810320a9134140c4400800100c810b44000107800b01c0f64102040a03070700341c1021040000010b800610030000066254041c0c018030b08403200250868207000001107460f045001000006041c01d000b0768203444926070074405500340f05145c0340c64125032400103501445606404541c01c091201d15880801484d1010f1014899082d5400c0d2515074050000707402c00303400e20140f80594001d40082ca00d500b4107181a0318071018015445502c0c401211000c2c10f80c5903646003200c40c2542c442e880601501c07090004156551641d928551048030520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 618946142 1250 618944892 618944929
    0x603120a032705012003040c0501030c0e090f01080f06010806011707030602181e090c090118031a0711030a141603080f060a06140c0c030307061e060302 67
    0x1218400031212158a4002c0301401d030a040407044400d1800500030114078450395606028000074000034555581142e101e113600c0081c200d0f100d4a0000154040d0103181d06201c01e02c51000c0300c82d44240c41d2000301e03034030416071b200c80001e0b5540340001c181e081500c000da2a213026003005005216801c1c000901d01c2c1150001043c0107414424040c403c0c2c1032008540004103001c1c00003c4441d8551040081038142007021a482280b82200140c018405c604480c020346d044103200300002c1400c16110094019640181440c184e55a2403c03643d00c1c4c500040e4004542d58042030000c9a1241903080c0d80301d038070004509105e40c8488400014980e680a407646030030811070108500b0058180d00e0056030300900040341c1070107036a0100c3c60041e0240d07908903002d46180c158940000c04600d0b094800004490103a10703a580840d030864040b0000c0c2e0f011002e5081d2074850320301c0d08140d54504100a01c1d10b1401a00001460b40d501c940040008a0a1585000483c2442c1e4140090380c2c0e00745540581100c0342 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 618947392 1250 618946142 618946151
    0x50405280b1612090825060c020904060507050405041d010f02031311010c0c0e07022b0c0f0209180106060309030f030906140a090203070b18090a0e030f040e0603120a03 74
    0x40003200c903444540c004c82c200d0f0040c1e040820b0103404664004000e22503007106c550f07150303840750411203525040c1c05002e540000c0503000700300401c000b603000315089002e616180d494103888002050550b1445402c0100d0103440400002480200307100e0380c138440c05854010343c41d500301940090202010329030081d0841d202c6041519450780214105650b5a5204000484031952950f030000590804c650b04c03409801654040c80d100c8940500407001400c61445812400000d1703141200c0c030750741040f42103174900400a40980903a4401c8050f80c46943c007020510791202c042c8000c0d07403e44890307600000c01d040c204a11000026040840c20000041c04d242c0015030001d1414008060020705042d07180c40b10181c0c0c280b001a8a49800c200c1c0d003180260b084031101030342c0c1c6880303140d14801c8030809500401484000a0360f80f034200712060b0000740fa41c402040c031040b603001c050b085da40042c0310748030440000501003048030130035540c1991004c001c5018124180309500c680c00301d407003034038902ca0405030f82c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 618948642 1250 618947392 618947423
    0x80a0803090102090414010524031501030603080304050a020a1a18011e021e0c0603010b0f0408072c070e0103021308060103080d200f0a050405280b16 66
    0x95064441d134820081c424480841142410151072900703020380f60140f00720601c004190100b0400c00c4411409841c5024516521207600c1d01642c4031003140741e410144c550764000045000321010350300450007a40a80200000c510405c40c403030240360b001000d4481c450300481014550101501c0e1306a074079009040005940c0401290100343d2000960440048050414105580024281c043d0101c00034491174503400d0088440c0c1c1da0500c40c9120381c0c80002040103020303202c0c2d42006010504031030401c00b400e0544070240315051104940101c02c00070035030360580d80100c240160100d07028018071007100d4603081c0174a0050522418018090601d40c000880e6203000d1032800e126030062050f030043c1e42513541c40c0d2a000b10554046614810400e0404400340c44a11118840040c1c20070240b002c14601603460441041d1070f0060f40c3d40d0000d002051100092503240c014600349907240b8406001c220580d0818a00710044554100f04d1440030244050040700d110810102c031490381141000c8030001c40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 618949892 1250 618948642 618948661
    0x3040305070f0507090b040b210102040815070f080106021e07050d15050601110a0312062309101d1b07050601061d011707020c060a0c0c0e01080a0803 66
    0x180000204408035002c860360a00c0808207402c07040d644103074001e2141d100c04008002c151201000d2465110003540f0710700c8685400400c00d4400419100b0016040654a548035403c02108110409255400000b00003015a011184000100441c180b81000c1d5041110003940c80369640c1100e0400c40e80c1d24a0306506200070410034004181c001c7c110428000203140c0703e45003070322094201d1091810301002c140690302070b211031400c80d100d510050514401684044503040c09042e80303050350940d1b840000ca9280013400e018201c1200c2102107008500c054404c0c07044400c0c1c010f20451904040d40014814103600c9140840d50140340390011030b07161105900d880c0341e902011100b05030510b0005680f000c0100200e4458103c4815454204d9005a1940382050051000198a00083e2040c2c91142c0c0c130389584140d01d41004107441150b03601003d00001c03503190f5008690760700100c2c0b1004100e808000b40468000007801e0020001001540b40c410034541e2002110f00081465002000040340781e00d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 618951142 1250 618949892 618949897
    0x50a0c0303091203020a0809151b04030614010305100614010e130c0c020306010608060d121707110d0e130504050a06050a0207031209030903060c050c0102031501030e1b0603040305 79
    0x40d00408102c0d030b40c0f44540000b900035405402d00c000400d11520014101d01400b04044401c3c1c080c84500810668610410380c0d07070450510102081c490050001102103900d034807840d09140071400e181c030f4180d411810300d585885041d00f02c0c64038540c100700041c80105c2c0d0007210109010802e0909041c03c01c98040000c41410900210b8a1014600032051541c1c5500c0020822840d00a0303003070310100c2e42c072900129010101104c0c1503402800d40410342c070011f4420505058288071030b03d07103c0301005080401c007001043c2071302e00a0014042002c0e61185804c00c0c03141d411400c01030b06000110303882400c042150444d0780064540a603a60764001418402c040c0800d41031298021010411b070324204824000a4100203016400101c11000034048908184601c000ca6501600c0381c601c0c551443d0f0301c03a005096a0014501000002c0c0078120007020240007546c068500b44000e0400502071800040c2150341c1003442980c1a80907441c101e008851410920305030203010341703605503280c3d51401d09a4851 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 618952392 1250 618951142 618951161
    0xa021908060c07020a0506030906130807051f151a0a0e03300307080a111c05060418080f0c070b0a110606121e010b0a0f0e07050a050a0c0303 62
    0xc1c041d03041081400200ea4004040040c0700b1a0182c920688585c1804140d00084441011607031116022515508038021240b0055214904062500c070a030b503106410013807a119031500203030701c841207802c2820082c05070b03443c0000c4240c02e00c500c0e80c0c0f4100007941098001490f0419450f40000e00c5a0f48a00c1600401d40301d500190840341c40106203148a10704601c4614070440685d41148002d01e000c080b00e040300e00608160b941c440d101e84070580c100c0020031082c410891030741003c00c4200b40c0a4103881c1a440e1445000c000010249008810300040d10300d4889421001180840d010001802200c00d039800a40d20f2030030143c40e1a14484003034680b9246030000d8120703010118a4510b003c6d4840851401824060142c40258548406010480205132070380036241d001100001b41e0f031020f0540c0596041c003000000303c0c05015440100300d50403480c2d0049004d00311074010074018800c941151580140c0145044d42c600094100020168041d03845c0c0041042070904007141031510a0b00403600340c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 618953642 1250 618952392 618952409
    0x30a0507021f02060108060f0f150f0a120507050d080a050304030c0f060905010c032c030d0e06040201020622030311281b050a020906011b030203040302120f0a0219 72
    0x48424401c400b81d500c200074840c500f860711803000052662500c400a25004086040c2007145d5526501204900100e81c110500e41205403114541c03103036a10cc1c411803000303242e41c10416050040c24280181040d855400c040d004480000040b40001d44a008407402ca2005152581d22921031b49000c0b01d08944404001e041c078036031a608030080c04410392010441a20030402004400d460000580030748820102e9020104042a07641d40c030003948214008030b504280042e240341900d004e8100b01207591400e00500c5a5028030200021960100308654018041180560101c0004416403502c4c0d078900c40c0007400c060b2158880000300341d59406480c02c00d600c003e004034101d89080020401144201101070005601c62180c0c001c80b02694450002580c0080c0a0100c940c025000e2184502001c0c090030704000b080d036010008490380e40380d0550001d01c01d80c06540c2e1107140d4010000d0b030305200584840103401c00406041000b10004802001e00c1d41a26001070803010b100c200c031030303a410542c0300506 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 618954892 1250 618953642 618953689
    0x40206040314060a1a030706120b131a06030411042a03150b0f1e09030a120e0901150804061806140c0c071206021e030612030903030a050702 62
    0x182d50b40100b0080c0c42458141c00403c420381d058180c41203000725040755141c0540190310f0034809030344101d204101700c03290300d03d01240c8100e07c0c1000c14128010010003021440c0d5445159030325199408503800b0682c0e00700c0d145402d5041540f1035101c42a00543c503248560760f101e0075901f103021890002910800302500b090003844a170140a8040d02c042d174050907082400e05404603c1664410a90b42c4403460400040d040001c640301010500f0711110a4080000062241103980c0d40c1c10030002610354420400e500d00d04ea03c20310090040b80403c0303902840344407850010300c03040c05100c1800c0d403200d496103005a840d0311941000401801224284041c0450301c03502c40080c0142c9401c541006551088404455a18003200407107501480004504580209608110f103101c110b5800f080070780904401842e200d007840c2084d40c500340700582590700c8140072007081541e140200040c0d40742c250000155182100b4080020b032240b280758002410302c000481c6010964651004100101514100c00f18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 618956142 1250 618954892 618954923
    0xb0c0c07062303041b0512030702040905070b042904031a060a03021e0909280c080102070b091b0906240a050421050705010c060e01050c090301060f0803030601080402060403 76
    0x22001000b80d0f01101701110f8003200103100e082c255000040b018410001e5414400c1c01c2e4204000b40034007403416159482410008103610a0101c0188010081c0301c2e1800450303079014080101038112a90a4079104105101c2080810f04101c0c1200365908030075105141030380c90f03070005055820581c201940000480301d0081314282d40d040c82c82229602165240441d0741c1d241301c001d58a8100d00844a10544d41840501113400c0c4483d01b01c02c1c00344120014500c0c180c9a00b00304d82260440d5600341ea0726020041031168000d414040b0f000f09500c4404107028a280040c0424012203024201e54046c3c0071001c2d0000d0701d605c14444c0031a0603415201c8660751441d01c500014580c1d0802e0080d06041181d1140c400d030070002901d041030045502101400d43c036442c140040d100b590388440c0560340c550311505a4242c00d2001e00c10300e0700c1101c0081040b41c454041c3d80526003100c00a40020300302804025050000b128000192036101d80f09181a0007a42c1e5281701080e07981c002c030350004100d81040007010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 618957392 1250 618956142 618956153
    0x90504112209060f0f1119050c0303040f020a12030207060806060d090b04050c0901120b06010e061909120b0615070b0907051302091c050118050a0b0c0c0706230304 72
    0xc01004c01c89081480082c121201340000c440d0f98041010108200b04804402104400e00d00e40c460921400d0440c10650f40340c40050560b4021202100c40c1d59004648104600d0206400703005041e42c0d060041e241041507401964401d502e000e101c0c240800400019599980d038001c032080c2034442d940621a4030124a014010b024003503404a980d4040c1c502c01a00906011144904a81c03201441c010026015150200300c1440500ba150410034001120b919030b4441b40010700030701000c4048808040110b1400801034803544e042000c940821003e010b0100c0c0419105030380181c0101e0320114440c503191070303600b110300c2000c8005040c0002c42c42002030300400420741c05d00725031080e644001e82c0007426045038100d210315401c0d154016881e1a4811640c03039144c00c4801d03080d200c0c1c000042c5075984213010300e4401d003491401300d583e60b108852010070024480d8581ea000308a80c5041070501000c05211501c0d40d0b00d600a0030200840321405a40c600f418042e010502c801e280c4001e175481c145030901 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 618958642 1250 618957392 618957401
    0x21022508120c120f0703030b0a2c01090203131b03120f1409011e030e01020d0204090b0306100e040c030b0a0911030609030a050c0111041e09050411220906 68
    0x801c9401e006a690f20152121403e0440f8803040007040c4140c036000b5140d43c01c0d0000c10f840c040403504282288000300c2c0a84092581c47c2c1400b0b003100c00c500f81d080c0711050100580b80c050b00014906070040c01400018507081407807004151b440141c40d401080780c40d540300c07541c6006602c064542c00718080107802c4a80c010003055022a200c6d82c400ca0007103814480d0078030f244a1400c803540080c1c9807203101008152f4203000c40f51501d44500d070200d0480c5540268900f660420342c0c0c2c079604582d001900b08101811032040240c1c0c0b40d01580680602e140003a07050740088030034800c104005400c2e5002a0403c9203004200010751361000a4a21900f0a4110f0400510300503a0441e181e8440e0f000780c010328507000a8252081c114030340110328040c0f00f6202101c05c1d410040c0360f41d042d176489038080c4e246c0c0c0300d096000c1c202519071651644406141501141e00c036091507404031b035032145407809000100b510300055001e4841d09a80c0f4810030429004550b02c0781401d41c0020210340c0c80c101ca5881048682c1c0c11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 618959892 1250 618958642 618958657
    0x309052b0c05031902012313090501050a140607030807020f0a03020a02090606030f06060901030609020c0c0a0e090307020108100302100c0b010b09060d0902011803060204032102250812 81
    0x200c0d130440c1100000350104151501001c0c1c041606c00e0b60382040101104008504094140941414200c0003402042c28a031550001d82580303407100d0042c05541821021440140b00c401c10b0086400d6031440810800e106501000d0200b000c144c00182d50140204040344003c0400ca0441d1104143d0303080080d1034045161049100780c2015010a6071850302070141ca009912041074022a46c440c04100909036100c0480b081c14103072980d000050191842c400f50812000a801405001c400d040801c1054219078000c001421001400d10402c4240041a5421945c0c20308285e10305e074032002144030448903503610082d800306480405c454440c1d440002100b900340300d40540c902507600d8010b00034443c05030f408103e8110030280034000c10b503c505d030000f01803240181841130110310f0600303503800c079125240c1007a42e500750002410070820110030b07201001000300c0d440c1d507504010b440e00000e464640c00452205141011400181c1d00350356580010000c000250455a80d1003801c19005600e800440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 618961142 1250 618959892 618959899
    0x90803100f090912114605070308030606120106120e07060f051c021b0705061c0902031018020906100903080c0f060408250309052b0c05 60
    0x269503141e805071180041e8010701c125035000d0b40c128105c030b840802c145400f046100c0e51300814240f803081c200310038225448011117440c0b10b00c0c42e481c5085140001030601c045102d8840004040340b00070686400341e036842801d441c1e50341c0310900040d61070300a0000c0b40d018011140f00002d150340c0c1081e400c0c2110301a1110a0001414551030681c03560101c1c071407007000c141e80c1c80381e628941d44686c0040100e246640b5a40720040c0b0070344032200480c1c001c4888202484201d08142c07403400001c11118005202c11228281b4200e802c2446801e447c40342c8161a80d0540c03240648011958180310882c0091142d0074108080b09140c046047d44211020080e4002d00030100422158202200120791034083c035181d00a400303107150740308140c40c0e1012241d4039044c002d0001301701f0b4843e02400494011401101c10035110708a65441e14000302850308100440541d40c4108000130790040c05842c00c8403022103403580002212034600d889000e140701407032510b21513101e002c010058100701c0707842510f4064 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 618962392 1250 618961142 618961169
    0x2100509010e0a15360807080a48061701050d14030c070e0109050703021306030b04020702130923060a0b04060506030a0e010b04061d06030109080310 66
    0x200f0320150140d036014542d40c2c03c034244e281c1c58045024074202d485080085014501c419180250b8500b00300d400b000c0101d01d21079143c8204001e80c010000030380502403100181c441160b003a40c0d20300001d4000c0b905030501c258800e01c082c0b909800b203250700040390641d40f018803101054075044900c142203400707980c01007050880081d1011101c1d00845050707800141130b40030020380c40e03110206c5a00c0e42050900aa00c030800c55204424400c0c44041c0c0240a43c510140b41ca50400c0d40c4035099074802000c0780201407041c800035116080d01e0340c121007100d103d405c00141c0c000717030301011070041d2081c0c0310041e42085012030300e0910944a64000300a00d40034070b4010500303030500180d0005002481043c516658400000b00320024400d40c000605010003c100282c0b10780c1d640c4c08140e417500704441c00165155101098005c4110a0107131441d40241140c041041500301782080b455020150241660101c00000181c0d281d102588201082508800001c0c1c0300c1c0b8000d250141c008006015851224014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618963642 1250 618962392 618962417
    0x5030f0705270f07023f070c060206060f0f030a11060f04080f0c030f06011406040e070203070b0f06010203160c080102040b1e07030503280e0c090c031e0703090210050901 75
    0x2581001c0460480b954070042d164040c1042061001c40345120034042d00104600307c0000c40f4800c0030b100800e00b036005046281b1381403081010107155400e6003400341103d22441491035074085864550340780c4c4400310014a600d00310104203280038480c4d03a8100f5044c000340100c1c0c8080300050400400b40110308941560340132000b41621803d04840100d0640c2c404030050200b9030040900605101c1e0203400c46013070a0b511005035807444002c0d1241000340e04000742040c2071125042c030966000382000c031503503034500b003c0c030000b07603284206030344a04400b05401e11b1400b00845006100d000300341c07080081d03444548400b009000390303001d280420095810a039000e044a4190400d66070559010740b0307414159540d40404044c2c095070b80c900c0301020703221030520b100c0c0356501d44510000c1d641c4103001030030301ca101c00050011724035010308103031700300f441c244100309005448110300102272118194110264a03900c1080e005800700030b174020342c440c003130904207100164490003070700120500b640c40e106103001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 618964892 1250 618963642 618963673
    0xb090106020a02120114010b18090106030606170c090d2603090f010524132a0c170a0c08030906070909090c09051b07150605030f0705270f0702 63
    0x7844c070350706c19140306241c010000c90410300003800d240e203e00110161540342050020b010b14200b41c002c440466641c880911091381c1c05412001c20030411681c00d203290404003a4250f0f1402402c4480d40300381c0150f03d03040200010306038000143c031180c1d0707900018901e0042001c48907410071548030019218a202c55030f0300d0841406203600512000d01c0031aa5140c3c40d000500d00400340c0040e107a003007100090307201c42c070b1040e6204005144c001450170701a003d10b1840014100c01d51349020004002030081ca860210f040c440c0d41044540c201c414461b80c5030b80340780c42503c414000d82c501801d041d0340400ac11200c95800b01d100d511907222a911403003603030340f0340308060105c502c140d901800310300d001310b02801440140c0e0300441e000000420381c3d10394404102130181059210640c111982e0b04200304102980b0414014640541070072000b8100721843d40441c030b541d4107a51701c00e551250352180b81c40d0410815040c2d030402c40a07085c1e80c01c00745606d810602a90120800d0303618400602c100700d03501c40c0d21807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 618966142 1250 618964892 618964901
    0x80d060e190e0601121104020c0607090302010306060e2805030a050a0510060b09090403030b04020d060f05010e010804110409080a03051e010b1806090301021605060f010b09130b090106020a021201 86
    0x40c008150320410900c5c0c3d07120f031000c10b0744c44140160042d9003004000324203e02000264400c8a4a45e86d21003000d0542c0300050a552003640080140041c882000c039180d511f000c56180840400190900d1141a41d0401c002000d0180d0080b60140038000c0a10305002d8045406c17452903001e40111805c084c04020107404649452040c4400c80318203104c070300f84030718101402e2508203009160100381e50201c0b00000301282d006a8821b49100e50b20941001490078181c031000c020902400c01654840b800e500181c84584028801402030400d0040c451290303450f94403000c402a00003001720f0300c0d441905030180c001c0000340ca04040c203001d800410300000b030303114400d0b9050b600440341300c50404e20314121200502d415011025030003c400d100c1d03030040ba2000d00c0070b0310444d002c1d4602201c4500450a0150500d4000b410711000c1d020010018002c08440b43d0881c0c1c04400251400480540b4011101c001400b40e40304a40e4032503084000002c500c3d500081d8500700781d00803201c2c1e91094840603203207400c03503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 618967392 1250 618966142 618966149
    0x90d08030103061514040207050c04150302031c05040303050d060f0b0c010f0605030c010e010306030b0a020307110705030d050703050921150f0609060105070f050d08010801090b04080d060e190e0601 87
    0x3081d20703400c01e460341d00785900034040c028480d400310b4080200400004040d6800c0d214040050080c0340b90810940ca406c0200843c0165954643000028990444c010118401c40c0009814014001049403002110341d00560007045400004584281c8440c5103441561180d580e61880c0c0d0700b003150400503650300d84142422590014010010071b40c3c404010f442925881203418103046c0c0d24203000011030007841407140f04004401d40103907285803c005c054000d82c600000f0312055448042c0510035901c4c0090800705040303150801f981c4030219807404450f984164074013281c1011100004211801e4001c03843c9800d0301001d02900c10206244104161480045901d240c9001ca0031010030990309040d1039861f08200c0c1850071901d0284c1079201d1100c5440f040d5001c4170564031050668000f15402103040e400b6000002c000d0101e400c2d240c8410f504200040d10240c10520b0001e844040701d8101d51040300184000001c04100346000d4090700c00d00003402403a240d0f081d0910382190201c1c4000b14030141078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 618968642 1250 618967392 618967409
    0x2206060e180612010906062402070f0e10080319260f0901020f0a05040e010f180b0319031d09040b0118090803040b0403090506030c0a030908090d080301030615 70
    0x140d41e2241c2c1008010359004203441819541c035034a4101007103e0b40a45005004400c00b04003188012020001800c000001340340b00b1900b1186040c82070340464845003040302d4541d9441c0d240da448520403a4640103607540003191501c00010703602000311000420b40d0740c1010070b844030301c0018144181c011401e00484804500c02c1c81e650002030100960341010780d0010001070005040c882c868a1045140d400240b1220200d03a0200d400c026040542c550540542191480d5800981c42d0124000214441e1a4018111030b01d50100600688013000180c1e441100010070f050450380e00d0401800c1190b41c2080d42c203502d050031071038041d0b6007420380b1031500655001c003645560760b1030518280707503081d40c944d020302d016030321000404045043c450145001b1400760141c1c031414101071901400950f0350f41e1095014010500801c5035580c2250240c1c1e01d200403030b040102e0103201600d09014184903052625500c0255245e2036014000510060741c10b03a84220410030444800c081040b04d1800c1c28442c0401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 618969892 1250 618968642 618968689
    0x2010c0905060c150408070c0f12060218030d0302270315040c0b1801030507020a050303150a05030f1e070803090609010e101d06030103202206060e 65
    0x1506080d0003d003404901c1d001070310b02001905104401c101d50544080d5100742000c580d40083c0a5010213170f030000c0c8584282c82000c24641100100c02c0d03860048081c3c0318a9010540d5417103d000c0c66003c03040ba04000b410b44146100300d20024000b5001695500c015203484205c0012840190304203031b030742201c010018031740d502c0c0040c4000c0894000070001c44640c4040b203030005040404401a10103140c1710500414000a0040014201c0c0c1008044804541c070a81d0342c42d01049010013140c1e007040c0304e41207808120a2403c00f14100d2030565100700e40512a010321000c8d045001705034080703200103000303401d0079000206001a036a50618000c201e101d420030000000300b813524400070840e5040605140c00c90b58141c400241c41c40c0d842c2d0742c840011032160841d21705042496030317410f615900c040360341a0a55045854000c2c14408000a0905210380050000742c4c81e9520910b00400200e0b40c104404010280610000508910b22890020a100784d02402c800e15059941c00203011504c05000b8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 618971142 1250 618969892 618969899
    0x1e1406060405090c1603020a060516080406050903120a0f0c18140427110402070b0406020a0c0c06030e0705041109130b04181106070c0303140d1a090702010c09 70
    0xf16402c050700072503003044100100c40228410719200c2e00d206000c0d4001d00651252801d00400340c80d00100303400f098a1114191a802c0c503001424503800c190020800038441e903c0c1035202d0b02c0c610450001c4060200c0010811605061036000004a800c031500140440582d0324020f540003004203c0d15040c135459200e0033f00c055141800c41c90a0a0001800420000b40d410701c481c004030100245820840641c541c64024024100b01060f981c01040e10114903041c80764542c9140c0c803401034001001c180c1c000071441d002c14443d00c0030389075031a00604050501640d4900203070040c8407005041c0a00e0043c0782c0300080310710f854460310030320300e81e4410f82d05d01e09400e41042100c1c12000702e0000d00015901c50b030340c00958680b132140a425a80745608101601c42d1030031300002d000f440c4140a41b007660100032000000302000030903c1126417504059420302c15070181519203001d20146684024a0840403005d506040c40316031083c40d4080e01c10141305d40750420120300342c40690441c2c101103040440e082 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 618972392 1250 618971142 618971149
    0x50d14070f020f060c0609122a030d1107050c0102010b0d1b0b0a0906021207030c12140f0301051801031e0c080d0504050a08030a08040201030e0c03011e1406060405 72
    0x7284244002c180f0b440784880200041e0003900208140d81e050350010f030030440d00000070040050a01071011400e8101403188800460b511024903044450380c100e02d240c2e22a04404105072804204190b20600600060140308001500400c4098038140305801860360503500600c07404e0011000601511a192052b80354200c005100000035082d9080b00180094074580803030162aa0f048681c1c0d03110562458104000e2038421455000c503c03100040000b44c0c0000e420140b00001164070aa0b03000802c0e00d41c14045e56203030103606da820300e1038500050984032f402540d0010340c16264100c03401c0035000d10b20081010807030030900009105140c42d5030303050b0000c070441c1114514140302ea11410b80d150340f99a505410a4441400003010a4000c90b0501003803034540c90780b00180c9050760040d400e101440d4402891942c000d1300182c181540d400140c0c100345030500844240340c03000f44c002c0c00031400e55030140e070b010103120411180c094505486c24a912011a4049007e02401030509042c28102000c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 618973642 1250 618972392 618972413
    0x60904080903030c1005071115070807140a02030703080a05130b060d05070305060405070501181a04080303070905041503080315040e39010804060b0109050319050d1407 74
    0x140d0760522050140c3da01084c02001000110b04055501260034140100064504940b00c003003200c0130f400401504ca8424000d940e040ea0000082c134040042d920381c00c400380c0300d070000b40d00c440014840006001e07981b44d030004020440c10707100b1740d100c2c0307503950325054408100d50042c0d441095907111040d42c4004524020b14280d0412001022222110301560701c0d40c1c504840c5500469003500103004000a0000030b2006000522081c00c101142d03440c400381e8052000c1c5a030045803000d43c4100c82d4202c40424000a071806021448100ca80d00d05041034080d0150f5000c1c461540700d00d0428080c00056400039101000b16913021500e14119150b45008a1620140c940c1481c0c1007541e44001e0001e00008010b08a00d049910400003003404c90f10007642800319000440c00204d03e407600c1c031318003140d0f841074281c0c6d400f0342c202c20001406071a020042b580c0e05000c2d400241e05128044195004280741250541124400c5040390003c8640d420191801e81020100402114090100002040030b5004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 618974892 1250 618973642 618973657
    0xa021201110705010e010509010b0a090c090510050c0d09140108061c12080a0c090b0921071403010b030601061407060f0506211c030e06041b0b0306090408 68
    0x1041e4404007014124a40d042404141d5850391210304110004500703101d5982c001c0300d40030080c0100c1c508403001c02c1500c0d20602c20a40f09070b640c2d9515503030313091182c182c003001303000000c0080c100208100c20003001504403265402950090030407035500e05000300aa4812139400003c10200400540019103508100400868004101c42415408070030040284400d191080180310f0420340960750040041c40000e2210010f10315101401011507041081c0c1e00071a01e2500c0030990b1a00140040340c060740070311028080449000a140b02e100102141d8041075941c040040c80e100c14480c0d040500340d461121000e42c16810400041c070589200d00c403c1c2c1d020140b1520010718000c580d560741411246408589884c2559542c1400014030300030301928200d0440070100c40e50920800790090b1035207014000ca10360b00c02c0c082e4041102c140260048000402d1a8003510045e02d404e00302168800c1c1d100c4020354007102400e1010032440340701e8003a60f01540c4d020304081c2542d55640d403040a0365101d800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 618976142 1250 618974892 618974929
    0xe01021002120103050709021614030d0e06011401030603120c140604030e0a0b0910030b030f0a0f02091f060c170d0f0501060c05030f03071710030c060c050a02 70
    0xa200311646a550008044042c04402070049540c55402e10303a0404140c0d070800c0420500400a480810021003200e601391a0000c3e40f05040d200203200e140d1440c450003504030245410036840c12a01400070030418100e0310902a0210b0302d40c1e1901c011003c5814030b00008068400083d500020a44145842d4150500c41c071542c0100d83d40c02c0900d6451b016040350128001940342a22000314106503a0b4a402008070740d000e07500700940e210000f000c000f80545480209640d600f06080c043e03074208045040c10b2100400da0f28554140d00705210398590320744041c1e006004a1001c203058100002c08600e02c0ca00d4140c82401c035504100d02100c41e82c15440081d158003182c080c40b2000701803030400030041c54404410008503c00901902426103905074412004d0140c2c407049100414804002c4950b030440240300103583c0d6a811a06462080c100b010340d401d07041d110b408001400c0d003c0d641e45400d481c02021a580c1081d0b4889040b00c544040741e200802a42000d00740800500f490712400c02c1100070320 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 618977392 1250 618976142 618976153
    0x9070c0b10030c052d0102210c0d030c0c02090601050904110c15060a0e0709090606030509010b0402040b0f16081209071401050d0f1b0504090605101416020603240d0506070e0102 78
    0xf842000303c030742301144203042c078120f00003000224000100701981c04451242014000c0001100c00074101101c0110040c0c068410380001500903807007401100c01040c801002001041c080c0c210307008094001030138064281c860604660031090031401014403c01e0000c10300c00308907081005800d12901302401d010144200c400d8041034100c01800b80c80081e013003a45d0005414600f4120a1b403c0d07035051035415020300e1040106200c0c665010048440f901003010036681e4842d15011b020f86459086a0090f104c3e01000c034038070303280000d4410307824040e449140c11102c681381c4501852014094003003485011441c10410392307003c1c800751740100e20ba00049540004002d0340e240400080905200c6030000050300000e030034481d0b00d610703102d0300000d0030741070711394001280080001074456124074505031200300e0040b0310f040c0300010f00c0c1036001200d40c0c041c000d83d45a0900341c908515030f004003680c42c3c031458000000e456a6090091032300d404070340c1042c010011a299441c0544003800c941d0106030450284 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 618978642 1250 618977392 618977413
    0x9050604080c10030f1d0d090e13050a0501020705011508010203070e011d031f0e06010e04170d1e1b0e060c0a0c150f050c0a0209070c0b10030c052d0102 67
    0x2244074400e85241c1800c00c4103080501b24101070b0510240c4072815040c445050f0b002c1c450103c2562106074004e00601d90031040d000d40341001d41c505401c4080c020030540c0001051003c111041d045900000710300c0049441c40c50f01da89509080c4e010403100c1c1400a01d01d295190481c3d03108216804082590a0070b1980d103414100109003054600c0078000311801c1c0003400c03d0401103c0c1c2c819000c0301080400540300f01e5041048140028401810103088003000da03585041e40c0040100725804003042d01820811408051007030034000f109052789038251442d102c410921070180318262503000c0a00e68502c14140346e40010812640c00140d124203c0e4800c0381a810002003449030154040d00810b01c0b1186020f0000c0c0300200b0192800e400202048405c0c170040341c1010000500740d01d0558122040030140d52103507011246008103420140907180751006120180c503103888100c007130380d00608280e241c080d198410f01051007103110880f40c0703006400001a15513800c05c00c040c1425001481500c103041072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 618979892 1250 618978642 618978671
    0xb121311120705090c07050a0f020a0803030703090c150c0308090c06070b0f10050319110a090c0f03020306010c082104030f0809060f0a0b010c02060d020a09050604080c1003 76
    0x1c1603000240290300c644000d01007441c003064400d40c040b4000c00281e2030050b0030341da043d840e1882e502000300742c088113012102c110350b00c00b10081c002c0e0018808681d16071502d4540100604580c08040d990020024400b0500c100c162629100e811040c1c0c942020b114076035601210b070100c000388400101c0c043e115803003070b046d691107009203801c1d03004000c03030103c5007480a819510700740c015144951101940c42c003003209880200f01040d5103241145c240402e40c80504000300c001039014142584211202c101107032021091f840b440081c0556900c041d125141c1400540807484240d40603808102c00c4070f440d50010300050001d20054002c0c01c016003442c1ca00030100444c401b0150b5040300410a00c01c2c03107010f000d51041c2031543c031014440042045090403443c0c180700107006070199070744a072908403100f82640607036411110554003510540c0e60b80d10400b002d0009420080011300014554403000dd4246011400c3e94182c0c1c410402801c002980c3d041005855001c40081c10180740e15011803841402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 618981142 1250 618979892 618979909
    0xb0a0914130c0903150c0e1c0606120515061c0303060b0f0318240604090c030803090d02341701090c15020c09100f0b12010b121311 58
    0x180c03e0300c0c0c581a107811441c203140c44040d9079144003500c515090085c58619480780a1800490050300c880c4001d490300b03003008041c0c40103024050309a50a0800005014511801040c015800b400039a80700702034000b8001c031040d0094480540c00071100401c50034044000000845552007810000f600300e589001102e8141c0124200c5540840301204100702c40700842c1c001015450000c02800000143e00101ca04030b194807400304291810244c0002c0460311182e201540c20f076003000c0680100d55482c50300080766401103e481415024041196140c41d0000407200c0005c40041c0641d03075403500c83c1952182035040e24400750224640098005583c02c903400d907481c0d000b880c0b10000320b0348084508281d500031a2540c40040c01070b1000074082001580403912500903941192000101d40b11070108600a1405400000010100107000210586240002c01d00400d40702060b280030780c2d0360b0002500710f00031050a9004603030203a00040c0241d04140340c04003064410f01c141071800350301c0d402050441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 618982392 1250 618981142 618981161
    0xf080a1112070c0609030305180f09090c1e010206010e0a0213030503070605060904151a060d02030a05010503060f040602130306291f080402030102121f0b0a091413 72
    0x100700c009051002d221070020100080c100034200507009034074541e4001c0c1035124460310450345020300c1d00303001115513175205280c003da1002804a000e07401c20030340107500e91000c80c8007240b03d03074000d000c00d0403210074100c7c084040c0720050300906081d030f20f08205030000880c02403507583c1c801c0e800c0041e60b88841c03000c1c00900145000b00021501c07000289058001c0b01e4000d01003d1250025008000c006841140e00c0b0b220814413a03000302c0e1400034501000318102e0b51807115640450041a107004c0c03d103180e030141d4400c07550303c1400d01c100d036139810a160300c80d14261100705084040f000010041011a00101049442404010340442d5640c031441b04803032200c100f0000c00098150711044854038502488000941121191403500c800301c2910740c1019065070140500c40941d0004081d5682941070b10032814928188a24520384100d42c1d801030600320b841d480681003404401b2440100d4541034503c8200151030b03000741ca0741087c44850f000088030860640c0308010004500b11000d46000302c03040b2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 618983642 1250 618982392 618982423
    0x609070605030c090a06090305010f11180307030524060409022d0918010c0806100e0d0f06020405090a020306060706050c090a031112011b08220b06040f090f080a11 72
    0x3403408d61402500399120019403901c007600f8865240d00a170000800c8034148042040030780c001c54020b0011a040074480d03130015142d406007051103000690f00c6424042100002e8020241a03900c14080004440308500003a4001d5135590b06070308210723002c1151902c2310b45800028115148441c00041071b2040440b0791440f41051000e0004c440d038002d01075002d2005580c1002092442d1070b102180e03801c07080d2100d4900700075901a040e0000d80310701c00341840f0039810624083d0b5640303890a081029522034401d4901846807200062520a041e1080c0c3c0d01a190045c0168070b00485600e569010b000f0240010b0310b000030800c03582d030955a400f15000005c511444540c158400c0d402c00300b00c50700c1c1464610703802507418610742c5040021001c10440d01c0c1d070f086d41022501a00c900069140000700f0b10f407940300f01c0491b00d00100501420360407040c0f10f000d080b01e050081c000002e40590a0b2054120020411200d1216200019a03100041c0c10950081d2070016a4a5027940341c441c41c01441c0c0210a04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 618984892 1250 618983642 618983657
    0xc2b020d0f0e1c030c140705030a020c030a08041401050c06090c0a210813170c0910050904020d060f06170706050703170411300609070605030c090a06 66
    0xc0701810780200389185075101c001d0304404189600b1200c2c40070002d042d1004043e1340740f12003a000303070140050b040000390b0300e00001c0d101c4019182071503895028420100c05403207400b03208003852800040700c4d000c4541c005001c50400d450201d5495a00720001141c2c0e06000e400d105502448408010f80340c4030f1080040248070300a8854284042c4560a0304000304007680b003004000c0c8000c01210015190b43e0000000359254038a0004030003400340c80d04003640c1080707801c401c00c1e203000c000643d40c8182801102c1c0ba4880b0f40b2803403008040b040c864401c0541040b0383d500094007503d4800f50000307441d8028070000c45c0c0c2d40d840030300301d0b0101c0e80c882e002030b405400345c8020101043c1c0d003000a81c0240002d800c225140132000d48000c1c4c03454041c0d234a050b00e00b100c200001000c001c0b4815403071009000161500305032803140c16903280e01d41c00307181c030306810030b040c41d038000901c940c0014046014411402c00381ca1043d0610208584aa00042070140744c80d800b00884c812540701e021101d0b00030120f070f0f583c440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 618986142 1250 618984892 618984911
    0x3030b090108010218270403090e061906050d060e01091505060c0c0904140102130503010506040b0105221e1e080606121005010e011403060c2b020d 65
    0xc81458180c0066429a105000c4144840c9003400d80ea0707201c0004483c90b00d00070060fa103607283c000000301c0b48241401c2070b8800380010190400c4800c0107031410014800d107656507210500903441b16a482090b010074556808206003800b8600824000340c804c0c0c80401e00720344074040000d00040aa101d40b00455642000c8080c0b103151100581c090241210803a02c2c0c480c00c1880290394103078281c01136105080307401c040380c104480301500030009039008009640782e0020355030f48802c46c612889401d00035400e060015565107414403c0e020705400503115181805000ba02c01c0040040711072100d074001c02108004030301c003008400c0050b40c1003e0b640981c4004c034107025481c040f540000a0441b0010101c480a05c681500032542a9014006650303a01407180b1588210745070031001d543c07070200c0600c2c0800105540d0700300c0c40c48505079400d54510090840c5001d040c541d40e40e100300c403195901c00c1c0074441c900d1055400c00a0008000150310510060404408041c040340d22102a44a65642c0d030040407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 618987392 1250 618986142 618986149
    0x1810050a030b180c0c030d140f010b032e0812041d10030204020901030b04050f071103040f0509070512071d09060d031202130803091203040f03060f02070b0403030b 72
    0x80034000d462041104401c200d45a2403a68091320001a1502c04110b80c494040108161501c0c20a40b0000b80081c1007946e40504088406849005440b1424000865040665004c130f82c06400c103004140740c80d04442e0b58020100400c0d00c0002c1500001690000b10107504101d0300505c2c00d01802c0f080d035100c0c07410200b105140076203600c0101c00308a060410a410304c140c4511400c40790107840140c0d43c2e0b00c0c1d20004900500904104c41c0d8403d1400d0180100740b6a0b0001c03e41c4074043c00d40340c91206130020341030950f6034041c5101d04009003020745024401ea04182e42e905030000c8203070610500300100740184158542e41103032640001440340e007400341038540a8007141d803840da00ba50080040c0c02d0407408988074182045010301404004554000d0460159044441c0342000c0700003510a1034440186030b4a1368405a2081d10448200c200c01c0c03914440030040317804481c0c0c440c0c81c8652061441e6552070240481c1c00551002503403d03c4240701182c001441d8a10640c842c1c1c0d000952910600c080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 618988642 1250 618987392 618987401
    0x7181a0a06050d020313170c0d0302090604090e0703141f0605101b0602130528050918030d0606020d0806010822120305160e0a09021810050a03 63
    0x40c45200030400400080782c00108846a01c1c0004001603681c1c0d898001e140c84409a03180e00400c804003050060318400305a101030b000704100d0400703440c01745002d9203040f016401b070390008550061040108014010705a40a42c0c0b082100c1c40a886006035280c40d5030782c8135200790060043c3da402103074044011409404610b030401c20300f0007003000502e06090100d0804142d82880b0014024041c1b881051000c055031503000c40ca034012015036440c84840c140002d00740140c41006d0144071828204126406801920a83c41c98124680c4644601d000204085100d024020700c2c14007440502c1c144041074113100410b442c01c1c0783c10010400603e0110000e10b440d050318089020006520144140d03607034040513140e0090b8012582d5030f0384401c080b5000d0404001010b000b844c04240610400c1000c2e05908076610504074442a40d01840401006403034080c48010076030380c4103007030b50414452440703aa805820b00480341000b26036141150004215040c0200d4020b0000c0f49004c03e9401c0240e034103004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 618989892 1250 618988642 618988691
    0x40e0903030106020a030f0c020a06230f07060b181303120e0c15160f03030b09010e011a090d1103070803040f090209060903150a050c030c070b090718 66
    0xa5103990301d041002901c507030f01d040005017005402007141300d11f244210b540050790b0b900100b04004c5e00c0d690394002341c08070ba000c804845501d00024522407021101d03c00781c41346000c41d04140351a00c603041daa404021700c100401c680d0b10450740c0c0f810b182c500100030312080c400c525002c001c01040c030882c10090301e01429161054201c50070602072100c01040032851a00d140c00540b20085000314040c02c4480d640200120414608410a4100f0600c0045009942142e000b43c40401c05c21078890300344601c480d001d009080d100495580100000c081c032000181d01c90646000c00c0341016013500c0000c0e4040703110581582d6100303408422401928003401028024845080214500f514041e0b031641400618400c81908580c08241405641c4400085800c103480040540e02a062080002c13449628142d9407000c1c00c500d003100280ca618203203003c5900602c00c05020f07130708020890b5aa141c46400c014800041c5024031500007902042410070150855100c2401180c031546241c3c0524030401e1a04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 618991142 1250 618989892 618989911
    0x50604050a091e03050f07080409060807061b0c0e0c0a12200c07240f09030209040213060803030106022808040303180b071a06010305040b06040f090611040e 69
    0x14075950015035043d800d0002140d0000c0414001011801c0564107130040c80740c069031005001449000b042405002003055031800c01081006640360f086c9555500c14a010f08408100210303146c0f03001c0c280e40444200783c903101d05165041142c8035518400300320000d41344c03980075800105212142c50341000c030345140102880020015000175010f01541810546180c501c10131000522711080002070000300082d0242c01590320b400020008d260740740c21f4000902c0d0300016051508041818414a003003001c481e0028074606045d1101c5d02001200704045040c14101d0f0303034a1400040308841807010758001c0c61070b83c014141e451aa0414280001000e0b42d200004400e0003a26800003100030042d5820b0f40c0c1c040c9001824400e156000a051050540104001400105d6081c0411001c042007080c05500c0d840100c0e1146c41c0c1c2801502990360031307980103026510190005034142000e61000c6040659a9070108110301c02e030b11b5810860360041c1120040c0310b8002018884500c005101c2e0f034100b0b4030130 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 618992392 1250 618991142 618991151
    0xc04030c14012003030106110c09040506011e080d08190c021f0e100b030708070806073b0310050112170403053d0507080c040f0314071701050604050a 66
    0x300f00c4542c40c3d00c0140035100c18000d1030541c03120344060070003101d090580c0140404840c0d040c90b0401039a60202445003103401d80d45280032442d0706034054915000c40d402c0344001c015062810388103070b038420307002030100c403040011000080c0e40080c14000e180410358280c01901e1465442c1a8608230100d01c4d2928002031410861200304080c0005400741039041810b200080e401c03407110000b410f22201e90b010385150f100c1c0c42004038445101051050246c60661110513000c070301c9018032030258080c169981c550604454000c01c1046944a0f50700c400807000703050320005182044004202c0f002a0040c2041011254a450400c0980120301d10014000c945c414209880c6503550365803800c1c440c070999441c2d08841031403030080c0398005000f0040003094000d503030610b0141081e83d005000466605000400721804a0101010001114152a109030641a542e411500c0b80f400405540c2e002c2401c5100706a40003801d01440103642ca444200403001181c141824010041a40c4c4003900c2c292105150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 618993642 1250 618992392 618992447
    0x30703021932070902040e04080714120d0c1106130201181202030c03060c1b03070c06051824031005040c09030501051005011205090a0212030a02010513080307080c04030c1401 77
    0x61f4103640780e0043c1c3c07140142e40d650000b40792500c070400844061034003522034030b40b01d80c00e007019200140c500303a040c008082210500c81081100e044c04180143c103140d800601c041000c00c02e41d1780188039210b00604182e03910803045008403181045036408151807081c1151903c00f146424040c4520085045000b00b0090902d001045e420f4032680142d0035100030f051b046000c07000e00600c10f40b02c0c000d400140352003102e43c0e90703640a08558000c80e1228516002d00d0340040b40e81c9000c0d41c107500c00c2868a10318036401e502c22819005243d00251419200101110740010300d42e8940c000d0310f0320740c070350b0362f4624440364518500710342503820152503412070448460080c002a6800f401d968888070342e548002c981900c4891009050510404000e900000400406162520000000c1c2811206907000b0016981c80c000080c050540b0700c00d00400410042000c80e0500d44035058554004001c000c00038038080e903039a64002e100000c0c0c0e0240500c07582c060400750056270090748000a5129440034418030001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 618994892 1250 618993642 618993659
    0x13061206030b01120f020901150806040c020303130609020909031b0c010e010518210714030a020105070203160f4202151003060e03070302193207090204 67
    0x40500130700d0341e41310713920000364140300c1c050485082c5250060500c0034036503107810f03603106e603500ba0240c03810114601e1800307d00300d0f007024404d04041e20300680c040c40c10764503210640d4042c0c9213605e20a803045a1904403030009617031034104080c060003030f01d801142d51390700b140c106008001c10072100c440e042d0405200100d03566001204c0841032802442c2440d40c5262210b0340c5c40c0c4440040b0000c5403c40410480f041c20800c030300702e0b80c54044001104903154155103000091403a00281c110030b03016000000010010350141d009050480d10007025200c1c5c1d2a940704115500005071390040403091140202049941d03030040030340010407030f82668121440c0c4048030400903418540c40e0020401d098420119400f4402d12400450f206504a0443c090070304004080320f07650315000648001346800302d0b5206040c4000b046550040c0d064004d8030349040021045003244403402c800b9070340c8000c509004600031103044809443d101c4007060240c80d0959203814946041e5280d04400e941e00d01c108000e04c10b110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 618996142 1250 618994892 618994913
    0x603050c070f020f041d07081e030702040203180a06230112032d0e041505091605070803040f0c051207090209040f0915050703050f0705030402010309081306120603 72
    0x50301138800081c01c1303007440c001c10018070010b14202e5042c05860591403400101240340c0048400792001c550840040c0c1140e840e5803408843c5013402d03640200031140040c10507030080c5600030352412800b84c01d0348405425909202d1a0b035421121607607151141e80c00410318028114000700040f048075410360400080b00d0644550300005010b004030780c2b195041c80c0c0c2000d003107100485e221134940001c42d541104081e00d80035a007501e00f4421801e050300074a000c1c00080e010b100700c0d00010715040c0380344c540c5840390400c2d80800c6001410080700700800b01c04201c0c05002140214401c01c50b803541c84c00c15081240b2341d40300c941c10140c420240e10000120060380010a00d0a07620f0380c500041c0e4441041d80082c009090703280941c90090708100c882c0c014807950224000c0c80d660380c00c0b018081c2e542c0b00d50f011001c80340211168061450002c0104400b548602c000c1e50b4000d2060400040c0400e083d1150704080c4c0100103a00c03501101c000091060b17581c02181c40509480483c0140716079802e6a540c046001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 618997392 1250 618996142 618996173
    0x240a080d0503550c0f020741060711101e18050a0305150703020a0504030f0503070609080406030c140912031603051801050c06013b010603050c07 64
    0x208a4038091108010000411144070070f4121041000c1059100050030f41c1c1d5040c00c008000d4020710500086d40348c5100e102c0b5510004150403441c0f106542010790356900e00503c0300901080000000501030740314030b4020700c6d291b030080e1400f1800300180d90230466034644000e0404100495031911007a00c950060036240703554400e051044840c0d808044a2078514440d511031507019080e00000000e118002c1602c1010f00d039151381c1088240c2e1040d10680503882800c00801c0011403c0004002003106100ba05130580d1184003503030716040003910360b0307016200080000d6450100000b800c1240036090b104001c4500e04a0900e00e240204c401c40743c138668021602c60b00c0c028104000c0e00030b8508000d0084801030311040901181d140c4035810020301940102d0030141da400700e40381c500f44403503000700150317503a501e0044001d1209a081160f031b640c4c19022030f0082007944030959200d0f000d0710380d01d40740d00c0c0b05215040c100c81c1c040c1d8507000c801403c3d2440070380006006801000100d002c5000c02100e14500c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 618998642 1250 618997392 618997501
    0x7091b0f030b03030c06010b030f10060c0b04060e0a0501140112080906131212170405031c0f06080a021504080a2603090c18240a080d0503 61
    0x295142c4202207411442040203071206802480000b00c0c00c0580c941c040c40c0102e0314544025804c0c5e44909051000c0c0407280612004102d41b00d44010010300240e082907405031040c0c801094040c40d010040d40340c000254011142c60b51030300d034847c1b40c40706100c2401d80108038003003403002072440a0715801e40b140b01b05d0b10070038000c41c80000c190359904450b83c007802c0208512444104118000d0500070704074a18030040400041002d40180811000c1680c542d0003140c02002031031500c00d11020043d654040e0b0040d5860480d10780c410f08903242180c0c07040200030b280e40d0010b04400811031041050342c2d003a07084c5101580f10309010034818450002400c40070030368003034800107140819400e40301d01032103001c101e0702c2500030010070044654404201c946c16550113a0700a0204080c006410080e05411500c002c4400c1e1247d040050309090400d0100c2144c80c0a0080b0b0500754560859a0034101c2410042010942c0002400444900000b4500c4000100610301100350095401004056040120102d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 618999892 1250 618998642 618998651
    0x9090207050109050d050c010e1c0305060a03080a03020a0305010503010c140703020c0901151106070828050c120903120c0f0c070609081513020d032007091b0f03 71
    0x100300d0709603c8504110703045401c81da6440c160307907070050080d0b1042001581950030100220308403c0002000c030030003024030f62a4400c00c0c02412045005020040c04030754031100320900000440c1101c1c0041c00e15200560700942d4900c107244014060300d1041e40020300aa00d840c09070307001154001002001c44032034005075035072000710307040881c0741c002110340c450307800300346000002420112484000d00c25030490700c4904400340d0414160b619000111419404a8884170004d4074400c05200c80d074848411030020f043e5820159003c0c041166030854045164881c0003542da50680b90421515502035270200c011407814071030400118045401a100440b0341e000800e45410034100300c029150b440850404690810781d503624010188482e910484c00c56010f4485084d03a00070310404860702c6203000040c0c0b081c0c40c0119509020b81008103c03415010404440b6030340401c8030041c0d01c403818540380000100041d40c05c01514508688602d9104401169048000140b254100c3c1c0d6803030b42c000c7e06007070002c2c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 619001142 1250 618999892 618999907
    0x60103120908030f0d0f15090c14030a0c030525030b0d02030a0f17280216080a050c012c010e18011e0308070f1505070e180601090902 59
    0x8441045a80142e0441d0102080c1c0740d001e940860301900d00e407060f00a040c00203030f400b107079130001f15240001581c00d0003900060038820340f051600700c0c00242c4002c1c40d20203503c2000c1a110700c1383e40c105071804c0030455154441c840b880381d0305015041e00a4070440811503201e9202d5500030320074901c1c0310786c40c0615450703254918190741c0b006000d02101d40c019054850440f507074900b01081100d0a407088580e09003440441d407074194280103462408151a0ba00203110080d83ea003101501d03898140d450462291081000c00c018030010310038000d001c03040003003054002e146011b504000d4922000750400c807148201c6500919103404400c1c03400c0e2540c08510f0b4200700040122018031079840280e030030142d4240700400f400c044401290403a68081401c0010010360128850608800e10000e45144402e03c40d180c08140080c50003070300a84034144028801c4e4110b503000d030548400311056400b1642100038080c2a00340b080c0d000902c101b81900e50021490040c00190104d8500c0c000c03050569808103240c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 619002392 1250 619001142 619001147
    0x150b0112050a150b030f100803041e0f03080d0606050a09140d1416090e3301090c110f0d0c053c01091502220305010203060f0a0806010312 61
    0x105840e02d408203103443c182e80c48611500303481d0310542c4d0070305544044034002840c009041c4a08070540d100d50000d1403032b0510b050464128171400410b1201201c840400010307443d03515075040d00003144204400740e11448102201000c032100350384641d092090400c9480b1420b60b00c0802c2c48299044140c0c85500c8a540700c02081c091a24108000c040080c103802e0408082c5002403101040410380484114040d00d402c090001c0c0c03801034062840c10ba2003244281c0312042c1000c032010172450782000d00211281e410748200d402c4503080c1c0c40b00303824641d90480200810f038040320304030341d0491840048c001d10755a0455250b444c40c0311080346040281c00c6000f081000000d00c01c400c0c809140344820326040c0002681032200d1450000b03041d02001040d090000400d00c180110f42289802c010ba6240082c0141c00403c00303948400f0050051460784180655421070600c28003020754000c1c00011385134541031090080300c0c01c0d603607012449400c00c000c00300300404000900d40e0644e035105843c1000c04200301c105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 619003642 1250 619002392 619002401
    0xf060804022d0d031d0613060516150903080604022812090b090601050306070504151e021e07050a090b041404050606030601150806010f110106060507150b0112050a 72
    0x42c580d0020200240000b4554002940524640546555490541c0d0202040b11502ca0038481003402d19880c1003c000141c006c00140c0200c401c00011110784c07451554454003101c44051308141d00d95a145102d030181039000205a40c041e909507000c5141402000100c40c4081c1000100702e40042c13686030040100344208503100810010013400d02203400c403032512801d241c5088650300f04501c6410300001c0d0600d03000601c5405000107440e4640ba00b4142070400d01c10300307075180520091143d0140d0b99210f030307504014020040082c076406072081098040e0080903c81d4110080d403010740c8102e0b0180050313605c0300241800c48100300c0000440242c58004170300a8008445910300c2c0700718410801051000c003041c01c40c4941421020765038144e803110403240500092208480014080d100000c62070b5001c0e51450955001c1c80c00c00f550903105101c121829507185820100020380e004c9007807420048000300d400139400320954288100004400000c002034896030344031603150b44440c0441c1041080b60300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 619004892 1250 619003642 619003729
    0x1080606041a09270604060f050f040f03020309060f030f070f021902040f020703020604110102011a01180306050703020409060509090619020f04030f0302060711120d180c0f06080402 80
    0x120107204003002c41e00d04e07440c3c0400f00d07400e89000307040c10303504003c182c5144181441400d002000030b0303003501d036030312414041d5a14131811801d51100304030740d00040d80c1d550007414640443d4580d190382c81c60244407080c2d82c102c003d4642e07828040d403211147d5900f030300825040c01209003942c85206810090000070080d100c0ca11f4101c950034030000e200001c0c542e012441c0d038400c5000300099808081108012800c07520785101d082840c000c90710540e0007640c41212181201a140101080600d40325140d89045440a0b039840001c240e001504100c1070701a40140c0d0020242140d101c0c1a40c50204c0100c1e4551200500322001c11303503041c008014004141d0706540910490500c541e44aa45900d271543d5910301c1044254054861040000c510030b10a003c89201c102c0c000d0060070b0003400285160065800803002e0510503922000d0340488280c4800200c0b142d103020f4038202903a6403400045403400c00c0603401031410000c00340d00f0030000d61202c02075070100106a42801c000c840005071309012035403221b42c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 619006142 1250 619004892 619004941
    0x825080406020307050607080108070e0a090507060810050d08030c0a1403010e0117010203240a1d061206010b1e0412060501092f070302010912050301080606041a09 72
    0x1400300e4a60b41c0000902502c600c0b0740b04580306c5403140300d010782d0640001d10800003940e00c103441c2400b112000f6070810360400880303400802c0c81310070342d5501030500003603030460030024000508100c030020b0106200801417900b6190102ca1070b0840d112060070307210080c005240b110700005e020741154801d02e1100c1d54003000407003060710395031940308810082000b0700c01c1d418041c07009002200c1c0c058042c400c4034041e2640202da0b43d64540b81d50814802168170300c0855500001b483c80005600b10750044020381c1039560f219080b1f441c540b080800208204854184210364445801440bd9141d00011501d10607800b24407261b004c014080c001c003040c4a980c01a03050884c40c0000f810412526070840ca05032480518240302c40890030352143c02050b840e49100040b085541d00c1c0041d00b0400000500c8043d00905c0041000c0d07e06840e0a00d01e03500000d002400240000010840301390240042d54020720100c0d42403100f0504541c014500358040300700c45102d54840000719442c0301c1c00c64402810440c1d401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 619007392 1250 619006142 619006147
    0x60d0b0406090c08071701291e0d0308090105130c0311041104090b0a0905061c0606470d0e0f102403020a031b0509040b01140a03082508 60
    0x44195006c204a81c182060441d8207000c0300d00200580e0360711161000a40c0c1340010301d01858034081004048015101007400c02400d50030380344171f850b95020803813507074000d80f154801814031b001941d08407200109207041c0404180c03541d8000607418124201201d4002900103030961340103000500030000c0314100c01480c04001800a51840c01e50400115180210ba242d61029602c04038981a00c5088035641e0b0301070884400100d140181611032101d45000da540000c0d010f440d504603135004030701000540d241003602d6100c604240190210200c20301d89c0b08818021906591124100c1c03802045082000242c440c04c00f500d213a841040100700c1c1810400c01c8035448003039140c40d90000d0903c081041c1c031641c5403001c09841210130030341d907508aa90203440c90b0040b03403941d254590450031101c00e448103158a4540000d20740c0d200412640654040ca480c00b032194502041e201c180580304480e5400b41322b44420800100d242d8109481e25203101c206281201201c4a20320001090744850003050142c0c007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 619008642 1250 619007392 619007399
    0xa061103121003140f030f0f04090204030503031008031303020f1f0906030606090b0316050c0a150b0d050a021309080d020c06010f0f0b180904060b0306060d0b0406090c0807 76
    0xb0040000c40e0b010702040c000e10018481c96607110320069020070104e40c82003004200341070380710303000b01005900959002d00300380c1c40c1c0a10205981c010741c41500c040e4004014042c1000345440351100070a0040011841c0c03034000c0c4003a89100302d452201070f125640904030801d8036161580c900b05019604809180340100f003034409003211032940150030001e0700d001c102184950189140703000341c60003440080e08580d10414004600c0a0741359412007006028411420340000400080e038002c0d22504070214940341001008086440020b5120700c1620032403151030218001041d0204400e40503a40003240a01303410550018248118004024500005000b4006542c560141005520031000c0d1403082e41ea038802940801010700421004504051b4104000300010000344190802c040143c43c41605110026080080031103003074a003162942c05500f0a0314080c40001e900c01c2c000c940c94021a4401c2e200e50a00c0c8000402c0102150b80c0c1c0d621004c1445152920040208100411100d40707584 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 619009892 1250 619008642 619008661
    0x12050415020712030b060c0c1002030403150615080c030a0b0a150305040b070e130903030f2a09060c021e120307050c0a05010c11011110090302100203060a06110312 72
    0xf000c02c0e03c4000030324204a49200b443c007101119401d46c10b1748010b006c25002401044000104504182d0543c40200000000580c0100c182e03103030301c5905200024082e02c1c18420b501002c4090301d41d90300300660b010405c4040d110103002d81fa0840c4100c0d20004031110f840340851078000c12034214803071260010002c1d10032164542c0099104d07a120710380810141e01d8030501500d2030040c2d0000c82e580546800a4003180c00381650200f00c1c028007a2902144540c1c2500a0b4804c981d4554111404003000c5c6c80c903680c08052544459015102920f005500c540c505a8002d02c055403841000348101c0d00720068110401070320880e04403180c2d000340040301c50481d15a8981da06c1d0310280382260315008800a6007500d242ca40c00368000c0701c0c0d06840d00c0c00048081d64940c0d0282d480c4d440e0990511003030100100c2f94820030010f031b000c0e00482ca000021075400c01d04002c1d241400012455500c1801041040f900f03440301134065044452a090010740289441816411801490000032100c040d4604000b00c220 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 619011142 1250 619009892 619009913
    0x33120703020114070c0303270b0304031107050604060f030b03032805070203100203061c06020c0f16050d0807080c01020301030201081e06010e0d06050c12090a03120504150207 77
    0xa200f600c8800211543e01c8070580e150050f82c030058140450300307608001007030003940002da0703410341d14008001485c0c984040f18281c51483e00113404000011040104150b003100d0080020881f000003441c0b03451400001840034402c50040100700240b06204251050090700004040c6034028150398840903008031440c1a00050703c120b150194030b01c5080e403410303402842240c200c070350081c1c080e01501c0007107504c540195201511490700000c03800090107070f8600f11b401c04403845114070381c09030b03488910118441c42c0403c54500c0740c00541140c010032a84228100c0c0307000459000303407000c664185160078042c0d020302070044040c040804c001000d4022203419401141600c0c401d88640c600c0c0d440703034261414400c1c0203600c0790030b1582c400c6001c64019070054a2540480d00e0051a1101360000340d515442910b4007550881d402e13103008202c5440302113041d01c9207944080300b0801004505400d0301d004192003003107641c00c42d03459aa08081380070b1040e140802810040100030a654074280b0340b41c00324610 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 619012392 1250 619011142 619011149
    0x90b0a050105041d04110303180906010f0507021002070b040b0a090f06120f1b053a0c05040b0a0f020615060d180f140606030303331207 60
    0x100048880450958002c80541d4156003218011414081c8460031011001d200a04199410740080301e00c140c0c2950108014260309012a581d600900041d406104140b8009001b0605214640c0483e42e000c0f507120003950601d540441e4650205000000240e09101c03460300140c00f4540006404200d41c4107090017000d886881d0740c0d6018400c0c0d51205900304044160044400107030b880b2001115880036038000306402944200001442c3c40c01d01c0d601c150240401c600d140102e00e011400c02401413624610364106810702201e0100e002c02d8030a81c81c40845001c0703284071200d80e01c034084d2034110710401c262005403601100c3c1c15541c0d80c8071000904205d1240c80301d44018800c40700014409040500700c001e040f0004ac0009041412200058010341890f0b081c0c0c60503a1141800800400e0281c0e92051609000785a0403038030100402482d401c00200070a1207019900401c140a402c400320000078001a05403801e002401e000d983c0b03020301601d4007001c401e80c004a08518280e0f00c04000c9000c1088 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 619013642 1250 619012392 619012399
    0x5041b0609060f0905090c21010f18060b030c0a031e09050613050304060c030c0204111e07050c3105070f09050303070201180305060a330b13030c090b 66
    0x3c0c46081403046a0554090292542100894000c168100c0a14024040018601000b1b5011312200c8946a040010903400340b0003408002c441045040c800800c06000040d24510a00607181001e24035415440f020f030541c80880710014040540c54807035405510740d1038013103a46110200038080d01f40044c0c46460030564041c010040810500b044203046100340c5c680c00006141400d00e04407059035400b540da481902444210341e05240183d54501c29420f0f624114503000740c545010750000231074202103580103268408104294004200f00084451594004549001003101c034003244802c0125a00004100c5000d83c1102c030140c40f4450b00b050784110481d40c0c0d00204080819822a0600c0140c403a00d60560010031004015501c11241a020441015040d01c40c83d90b9950b0f6240c9040c00c00c40d03102d05804d540300000f02643c1c6411045484800d248112a1160801070408200709019803065640795800050702e485040a5003422900454020707400301c00c1c4a98034407048000c0d00e8411740c4c0380c0c407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 619014892 1250 619013642 619013657
    0x308120703150306050c13090e0111120109050c07050d0c050606010504052d03030d0506090c0403020906121204140312040f120809100f090801020301081005041b060906 74
    0x203500d4464421440262160512050340c60325540f240030042034046c000f00240e510801281c10450030100f07038080100455030b00011001c920100c02803c540d032403020340390340140411840014907503070b041700c80c15100c1d4406c0c002079948a02c08104154420900010101d0140c9044d085000c1d4200c40591005400359065640542c3c0d001c0045809100714060f8aa215901450b00703045080b01c284c8030080b0107100050a61480801c000182c40e6030000c1180c2d22586898500f0040542480e0300c1507500301d1801c11450b0b04040c2543e001820814009102900030f984600c0e4003003460108024848a140583c02c0c1c0750f5031540c44008400852000c42d00c124040c2c070440000c04c40c90803600b821101198030080300c15441a08103d00d69500b01d40c401020741d16698140b04a075456641c8081c1c03280d50725410f495000c0d141c00f1108005c0c01e104840d50010909034410b1004020800012405d80003060b6240400035441e0713900e14122880701c2c02c1c90742001c927000c25003d0114100350004250b00607030300b40c3c0d100c800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 619016142 1250 619014892 619014901
    0x30204050a021315140904091a041101030204031e060b040608030d0e0604020306180c030106150806400204080601060809010e0706111f060609090203100308030c0c07030812 76
    0x40070701c450414070000084042540c1d41c43c0c8081e00300900f101450003440030800098130b486c0d0800014909904c2140c00d8270031010721040250103c4101020102800e0642c10140b4503103884900c640d03600720340c0111100020b8040c041000d103a10541c6801d900400401c140d540ba8440543d507504005059001c2624003c00600e60000000701240b15640c010000c1c40c01d5540e508184403130710811107003207400c4d110f000b0141107039590a00402010341000400e00e102c20390082c00090150001030413460007031500c00c02214006c80c18229003181825444049442c0000c000298141d1551001180c0c0cbc0f9a4404200443d42150101d100c038120f400ca9a100c001d15103656000c3c074229544040d0f1504660300c5101c00700421802203114544184401013900c045807002e07441d4086141d00d103820100c005030384203418407c0c0d513005522a805025000070460452411105503040c42c2040e0102400d200408800100842c03005822a0302d07801e10f0409a0382c03441c0c1d0382d24200312950042001c0a442626020008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 619017392 1250 619016142 619016159
    0x10608250b0304060b0a090f021908070f270308030103020f011b1502070b0f061c080f0304050c0a030b150d020102100b130e0f0f0f0d050c07030204050a0213 69
    0x80d5003076a0003807480c54a4a0340c1d030000070841c8204e82c680015000d000020b050340c55101d4900d0301020900e000d40d950380081c201d40011480100090140012941030024103a4440e00880d1041d815042041403040c00c410501180c400a07402e60f07080c1c010647c80801007001090141d81282e1003031360040070107001e60b401500d03031002d00300c4802408444001180d0109054514070740c0790001502c80145002c1c02a11042102101190041d4042020034284916401c001c40808816006844092800f2003d076855007441e2148000013401a000480413400b480360a2050344010b18000308401a0705d5528038103404180c034100ca040d00c0b4100014a44003a41c2040c01000b00c14a41c140c1c0034003030043d423a85901000300015403040b0b8108948002d181541441c0b48601001d2010860003072280b443d01c003220500e045942000c441642d00700d040c41e1201d45000081c03c0038140d260381009919210f20706002454200c0592002e580039041c1424488184d00310b5005096112400819140054a40c4c520 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 619018642 1250 619017392 619017463
    0x608010605180709050d060b0a06021903030e0c03032205030102070b0f040f0206040b0705010b0301153c170d0905042a0305090f06010e0f0a0e010608 66
    0x5280d000b10310140e0085000100c1c18a050b44500c050400303281c2d05861342c0c04110980f80490003161301595800b05030a4030300e8155250700013408144010700d22019400c0c000c0c4059110402b00806260321000200b6104000740012540f0340005401c03030740c588080002d1855a9540d000c2030345040340e61254041220700303041c000c075000d05030808070116503601c03000040104501c00a0041d00c1510010381c00c0c400503554540100010410b4031203094a81641d030402c18211003854000c20300c40d03850000c030034000010307000004040310301c00c805142203807440391a0140c19001f00341d40407008070203925050742c1c102e078a02c034000143c5140b04e1a0790300201c90644003a9075000d00002280109070b01c0c180800503490143c001c81c052124040c0d00e808906140101110803c8004031000c01090b2200b00f04410729504009114078070780503400815203035140c02d003426800400900f10306030120b818400610000a1034020040890301c0b030380204074480d03480c10001d80b282c0b00818078054190342408904002e0400014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 619019892 1250 619018642 619018649
    0x1e0613080319170609180a0606170c040204080a060b01110601031b0b030702070b0f090409110f150f250b160f08010504020a0e091009060605190815120a050106080106 73
    0x1c0f04c13070301b40c45120f01c84000c984810601e0582d0303c01c40b440040092124028240140b1140ba0f003400c050300c1c0c9010070390912005000e02c5001c0c0e8811320040003810400240c11014030b0b00301d4000242d502c00710b001225104a240642c44c0284500c03800001000205090f02140180c102c1020007019100c03400c100503440162030103001039000c141d00340045003408006045602608001c50b02e06040314001c681600d1500380c0076507020211441500990805202044543c581160744000002c081d40000c6104c0c01001e8000e90f04020100c4c3c018000210b01402001440c3d5500c3c0407661130509141c0140e60f5442286c07860f515070f03a489000100c1c24040c207080034a103d503a44962455030f083c6020302c40250001c0d0581402c006655814048544503c052940a01200d010170322031182003052120a848850380010f00f042010015440f900c1041000881041072524012243e40c030f42a18840003440714155942d44500c221103007850803d0001042e4451911034402440f650341d44032499801c8400610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 619021142 1250 619019892 619019899
    0x1204110a1a090f0613090b031002070c0e100914070e0307050d020d0c090e03070c0503030708091908191a01050108040210170a060e061e06130803191706 67
    0x4038852030b19040e440346036008809011136041900c01c1005059140b903640c403207510b5030303560300d07603400c00781801d00600514800322103065151490a5840c1c24150314036225003d40303407202d00045400c030b281001140e401002200c406200c41e41003660001f41009098a45801140c61019000c0181c00c0100f8034800321900101802c1400c8411380a01c00c1702090120304441803018000c01140000d802d04c181040c2e808100020350300d4074803529110624580740c0d0010b9110f5801403060200203000031048403079642c03081d2a400c0d41c283c82424048101c003203d0700002018019603080743e0051a40682000304140551640c0340400707020180e00c8100c0c032080c003580f0b0000d941140000c4c0036041182d103e01c0070903100c0c5049500e03407c2100f24008040c5050700c2900c09641c50f000304001c0c0120512000360021000c079500c804418000040c1d0b60103d142c41c10990040c003003c2400419410501c4d0403d00401d500020740b90344020301d07165958180440c250503408138918440803840360031078900c060f12411018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 619022392 1250 619021142 619021147
    0x51f0b0a111e011404020a1202150a020a05060a14070309050a06091209090b4516110a031b05060a0509060903040311040f0b1009060813031b0201051204110a1a 70
    0x45c10340342301c0440c0010240e80010142e6400f81241e03c0ba0401460044080d502400b488545890306505141d4007034105038105007442c007103041402d480e041e1141c10910b1401c0028580d1100e241260510640d21805003415203010440f074180005807021441005030f55a0380c01881c1e4071000014104c481d586111508099075200468030000903a40c0444c1000e9016084c0c014044402d1400f02000d0300b0300e9090045c00481c905108cd140c110300d51342a0004094281200400d400710081c0e903445802100180c20010348646038021100c0380b01c441143c040d040303815111246008201320029220a480c4075019105010029011441c0030065a0a90f03034007072407811008040d00c040101510782e480b41c40c0710352942c0341c2e0a501e483c0c0d550025840307081001d40b906c0500c0ca1410348081c10054008040c2000040010010790000f03501143c6da40700b0100005c03819444150600040f1480d000d41a40084c00800b440140828050250355500480108450342044943c940d0380c1015030b0400c0282456142105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 619023642 1250 619022392 619022399
    0x60e0a02130b0703111c0206070c1407062705030703080d0609020c0607091a0d0207110a08071814060d06090503031504051f0b0a111e011404020a 64
    0x503001041c00000389002018100e8451507140c41c1648504000c8001c14a03850a10f40302e4401840f21210084525120003410b001d2144042d4661000800000c1088152402c5d4010007102490a545544034441110003560f22103101400540d00640c0158404090640307100b074480580c4e40f01e000743c40020f00600388039851541c078600b6a400031130600e0203242c0c513418049069143e030f20103052142d1040b0010151410010340103003400409401c0b00c90118408080c41d030802c140d900c110b4100c00d159440040ea17845a90810841d051060090f040e4401040300c0c0001e104030f00060310205550640c42c000e145c001102414400301c800c0401c0c010800203103440041d00500d000340c0b5560819000c0c41c8085040121551401e00b540c2c0106c81040d5416140a03002510381010b1244a41c403403511029000301100c8034161803152200e030700c101019048005000f00d1060b00c036102c210540e4000108550702d409007100e00b0740c80076203014060b034410340c82c088a04004c1c1d60071a00490040341c000d8504d4868a0a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 619024892 1250 619023642 619023661
    0xa0e0417030a020d090b01030318051c0303180309030b0c040810020705030d0603030306090f0b090a02030603070e07021c0509100e041409060906060108040506160e19050301060504060e 81
    0x100400b509003881e400d00c0000c0054030300f4010994581d2041d0010403841d811460090441d2004000c1d454548066200522076621340e851a4185640d900c5000000b001e0589000c0300501400e4000c080c400000242e141c080540205600054a100307100c540d05560700d03010610158012031094068950003100410303c40c070a40d50081034114010750940e803501043c42d0440041d41c2055101328006640c58108000041a51107592031954039001c06000280c2d0325000a00001009040c00d10842d9002000c240c6a55040094100030104846000910300c1c0c040d002079119100a40300002d00207100203a8039190b40b0510403145245d60081c111411905102c0f0102c1c0d403c03074402081074015030355002e41d010590102c202c0320710681c0000001e01c400d141c5298030304d0a06034003802243c140101c3c041800002900820710303643c880c0c0c600914480480080c50101e485104819450b41c0100c004000105070440340307199002524000e43c000e0140d660340d070090204903499031044814115250b0702049001d403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 619026142 1250 619024892 619024897
    0x6030f04081309021b01061d01140d0212150604050118050702030c0f0f0c0105120411010903021201090b011a070b06030c19090b06030c0a0e2803020a0e0417 69
    0xb000a03128100040c0c9982c2a04100c0c0d104180300d4542920100e500c5030000402d008140c00760000110010301101d18a242c3d000680040c0180040d13603005405800c2c494644900125210760000c0c489911030703c5a261054442a01c814030407685d290703180c0002c00c103041a0042034100c030f40c0e41d01040c1c108903820364203d004080260a00e4110300081001841508040100d5200d4054035000390030201201007845180c0000007a0140c14000103000c06001488040d541c10380c1f058101a9004c5042c02010049540200b103030002503200e209090707801c07181c03d0158807450080b0300c9203c0301030081e6210140340640c1e190070803003949410401c20030240021100c00380b25800207000350440c0d001c08038180026030203040c44103e24034044a290f0b0304010740c03003030f40c0204074001d41c003035402c02e00c1c40c181001c4016030b42c1710303990501051150701606800147c441ca94010b08184042802d54400e55250189030700552075440709030300c035910182c0081204a600b4070528040d0b54400e810302c0501544480e400c4a54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 619027392 1250 619026142 619026157
    0x201021011121005100c06060816051206060f1009080a05010c02250e0c0d0e010b0f0f1f110d080f0108031903050a0b03030403060203041106030f0408 66
    0x6004140c09034594203040d0040e42140007044101d1500c400d196400d02205200041105001c050900c1c4104250b49802540346a0040545400759000c89541081c0001c1c080a5000c83c800744035209099055040c502e50020a9035812140d2244600d0b44401c80d641d0b516064400036440000c40d07808803032a1516295108a800040c10807500c2965030741803080c244201c031941900e540c0d4603000c090485640c18020030380600c40394800d07102c048012032001c3d0b06034801c81c003c0246450085010400c07401410b01900e0035401014810301c0091a2094010f029001c0c0440d15805001d07003a2640c4064a410405201d1022000e400100d021030800d40c00d1080220481c860814040003c8440610920900440410741e849880e10040b40c00d282c2c070502188401640201208d800034030100440742a24040005007042502d00480d4a8603010b40300e000914598005a9143c88001400010044180c0146200c0c90003002078807440b1a013003040c00301c176103c00c540e8085003c114100080000c8d002c0800360100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 619028642 1250 619027392 619027397
    0x7050121020c0a030318170d0f15060e0301060e16110f06010501023f221a0304020303040e150d110a0602071a09030a0c121401090f0f0201 61
    0x4051203805204100d0344212107416582d0802c030411028160175000307101210140641c0b1260b9000140c0341c4042400c02c0800444074544000341c900c181d060316401018030f1100841003040802803400700e21100280601c11480400c01008841886103010301c2000100e418146548a0076921420020b0320402102401001c0c4000050b0f51a4a06005c101c102c83e60a4007500030891541032100184c5031899003411100c000e000902d1501c42610300035052498644080064002082a255150594020a05080c00031001d980c14980b040c0c505002400880e8108042c42c8000c10000e507070300540d40b00c210f4010f50150300c2000f007003003042e0808201d42e5100d07203402c400c0209150100e0009181e00c00040e419120003644002c620410300c3c0408009004103d24001850303810318161a04040003c00340d4036200b644030100d10041d85c3e441c203000d84806030780d010680960301034892500020701c0c101d044041d186d200305489200c00d40801449000c65680c0c005a00e42c06002d8255500c0786e0481c400301d0b04030704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 619029892 1250 619028642 619028687
    0x10e1f090206160b04060f0501030f020d0512030903040e10080a02120c090c120603011a0d02030a06090804170d051806070506270604172101060801060e12070501 71
    0x140d000c01240d543c46411310070070b4039980a00341810810159015041801c01e0249028010800183c0380002c61664a0341076540b010000f0441c00c00c80e06209074200d0382e001910b000001c2110030f96001c80200165091040880c1550300e131802100a000100e0159a038903038042d4142c0005454598001d40164810900719080c41c030400001c201d5510069640f1110341c0e0001c80c5228000000000c2168440e0003500204a80341d2156000451030002c0081d0034018603c0c041807005548061184403003041e00701400f8030a40c42c051030721101c00d6000b4402c2c20040803030320000246c80300001c6004180c1034559964607003440240700b559140740307500300d41c416408141009500c0000e4400e1140a103c1e0003205207440107500760543d0341c1394121942000c06030300d8004204010003d4811116010020341c00e8800c19102c41c01000040c0c81c08500c0035020b207011105500000d03140b030344421900d050b203e040d6543e18040c45090148669113aa9290701040c50b00450400d00c859449007070030310410451801b4030302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 619031142 1250 619029892 619029907
    0x1180b070321020a05040f210803060f042301121208130f120206071103031306180605091006060e0d0314070501020915040501081906050a0b0903010e1f090206 70
    0x1400ca03440711400d000450004030341000504034280034600100f41070f03088c9015140d0118680182151008001000080c011010406070340340c2e1500290314036000b80c400c00c213500300d082c1612504001c9a81590500500e980046424503201d2132403403015520103101109a01043c2040d03a407800c0040441e80911105190340700071074030b8500346011050007208000ca4001c40100020300f0168000c00c02d0041c00084082c002c1d0385500041143d07405041e000c555680742c0d41d545032170340240542d662020301841041011005000a83d8802d40c05160094100d0740400c075498801400c2d03603614440d401c0481c42a541902e450300304000b5a4034441d1285c6882407904403940581042070f041180140c400740e60110341c0d0354003410b000303c124050204400417503084c64034020000707186803001088450051140700703504199001702d401c05405400e000f0a24207d0907200d0390111780d40e41148501910035800e16a0850311400c0c0442d16461102034034544080d80c5081c000980050302410350100d0b003001040080d074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 619032392 1250 619031142 619031207
    0x201031806020304140d02030706050a0b090f07170411010c02010c05070b0c0105091612030504081f140106080c071401050c030106110d020303070e0f0d1101180b0703 73
    0x29400e01e10a090041e22400c05003020300244400c550340c820380750b00c0301254120310798001050780c0c0015484000401d29903119000000585034040d100e03a0001c0a920900200c1e00d510041c851040503070355039a8000c0c20440510350744800041e10050302c00407405402c00700651003083c06042180c0181000c10a0480681c0c602d0b2a01c69568099081280701090341019140b00303003e0036810048502c0180200100002d80d80101d1203c1d100303d4100d0768001107400c040500071419580240341c96400d6600580d12291180440360360078401c1040340b85861040540e00508070803407410b8401e185c1d5a001e042e40c800e542c3c041c042c0c1c44101c0c203803106002c1c5208100c00035000d0041c98420307a10000c01c81c0e100d501d00b12001d407a038610101c1070703242d940010201c404042d500105071303540800c0525200512800620200b60181072008800d50008000f0b800340003404004810b042e242c40303081ea1a2141c4205c4070302501500c161601035191004010000030011034803030b8415103034200c1307810903d001c1c0748410b9058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 619033642 1250 619032392 619032431
    0x2d1803021c05361e0102070b03090d031d0708030703480204051f080f06150109181a030304080c060a0203042402060a02190c110d060e0705030f1009020103 68
    0x100200200d13400d1901c07030350356410301203040207291214500f0305500700505942d484e4844e0380c000070101170395012012104600343c114840c40c0311101050707803030f09511030140548950bc00d5900340c001c194400c03610401d1881d50711040d610104038461240046a0f00d95015a0b06500303482950421011124050b0150b80c80703115150240c000c0701006840b40e962800940c0c41491141c3c040482c1c2c0d0000300b0b0b06d012002021410070f51104e0f02d08a82c15843c110310300103807446100c6801c0540111040d202007d14007403158411600d01c10003031a4884480004c00405a17a4815401000b540c1e030806241d241c0142001005000b20748214019a4203003600d41c0d001030b01456041c0c0e04050004a000254048190103200103a000841c0c000c085d441c00c2c3e640c0b0590442c0940c6040c0d5072040281c01c862031000d0010198000d020868020503526a004190800324060034081c19a50f0050007100d0300041e003490005161503045288030050050002c1e020f10000c000c1c03401c24410390506458914002030b05200000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 619034892 1250 619033642 619033669
    0xc03140d020f0301050a1205030a0e03030d02030108030a1e1215150206150405040309270c0f0915091221050712032d1803021c0536 58
    0x442d0f10f940c5080b082019a5801303a110392010001e07a031114010410200c1200e441100d2810b01c42c41c403110b602c0129203948280c040300500d2510100001c1139003030000c0014500e001255403a803d00c40682c00001000c442400f00304004035480300540d01052245270803c80c41080707002203e20f07100e03a5928101480c50030f40410000160850070802400c3c038070148002c200481c041c1c1d010056031500e0758010304044094025031580c40300e5011190540c0012804042d520440131600313100400403544050302c8100c80084080c0491140d41c1c0c041481603003040148505515565803c0100d850902011100442c081042ea41d0070380d1501140e1240110740c01c102c0d400ca115076150365441c002418900000e0403490003c508060420f031140740030038009502070440c3d800300c1b21a00342030b080004550000f000c9104030580224203c1101005068000c9024000505401d00c4601c03961601300f0f00312103038861400c040780c0082a20011400548a191200b541106100819aa0201c1e0070303000034844d00400c034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 619036142 1250 619034892 619034917
    0xe010c1509050d050702060f0913061e0503031c020304020102030409021804050610080705160b0c04053a020f061201091503030c020d1e060c1409010c03140d02 70
    0x20081c60410908000b80e0b0000c41d0640b4080d0f04010090340001c0e031a20903035102460343c55001c9001e00881d40c030321084c070318880480740042003544e0f920714000032402901420034601c0c40507501c0c0040e56040100c1100c026469211040b2a2000c201e038541c4000c0d04081d00a074110700c01403002054100c2c03584010460044d6902880305c0e049110001c000560700000c0005004004c12503032820060382011205411035014244251615580c1030304000103100040040e04111410060000d1244001e00400640d60300780c9400c804003c2a0f040e501036041c029802d100c5003030260f2111b1861030314240342c1e09100ca00c000e0520a0b156603200008100d07802232125180d104051100402071110544a10286082a801e07016244d500c1c589020744621060a070203400303160301009400420a00111825041c103001a070302003007501c207060030705c01412030710103403404a43e00c00c20300604071603802e040d07500b0444141d42d8400981d200d03582c101d0b000fa50004200e00303128001d008112098400740003803c107010840 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 619037392 1250 619036142 619036151
    0xb06070611360a06170c0d02070305070515010e0f1902030108060a0c0f020705010e1f0f02100603080301051905091812031506030c0708180f0a050307060e010c15 71
    0x2061903071882c20020901d071007207015001c01c1041030b4000082e14414241284100307000d41e00c0710164209442011204403041d0b10004000d4109501704e0080c1801c0790140e002c03958480721104c85503032031702e40c01c1c00307a00e119085110010b000c00e0b89101c001d139801298040c905182880d1509140282e03003080c0c1280c6250741203041088101c0c03406124408042c0002d242140a81079140fa010707407500c601e402403034100640180c4807001501c441700700c0b132504081d0038418840c184514a00810307a040000c003900c0107008540b074070364000c2c03028060b80007900e4000c401c1e145164640001c00004410741403070341d0206562014001030680e40c02c5070280c880c2031502c0030841d41d010300400160805c01140125001401c0c10b00c00d010360f800e1107041c0c181c1000e8007503400e20b03940d480ba80d07861035090254010092505a00041c7c3c085182c006503c0110101d00c15910664403090450803c003401205006482e00b6900402d01085802e100360034400310120181003075955000c443e2a410042041d5031468000c06498 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 619038642 1250 619037392 619037467
    0xc050105042a060e0105070f02090f1b040b0f0d090b07020304050109080615062101030303090b01090b01020c01080711070f0609060c03020c060a0314040f0302100b06070611 76
    0x110082c441103020b5442d4020040e0030034802800d0148208041410403101007107010802400000b01c9050a400405050b282d03e41005001d00000040326900b04200c4100207100e4007403030350f20580741595190a40c1508140200001102d5500314950203e00191101c2d00c160200303070a8400540101d0890303014550352400c140000d0701c603000035446543c031644100100f054002c440750100c040801c0c22501d8030390b0f034151200100d0040859102501c581c251400002007055007640c04400c001344190401181a80d0f80d102210488116000070346c05a040f04241061b150300c2500002e6000d011800c3c1042c0c82005129014503203006500910328000d0000b20900840341c100c55980001c1445143c0050222400d5400a40700d07003201501c00c0c01010007241e60784007940031f5000240c12000b412078040d8189482d08221492102a00058002d401070711001808446036005003000b021002d42045c0c0f40603d50b60700c9a00030170304840500c0c2100390500c446248081502001042514441d0b14000501c91 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 619039892 1250 619038642 619038683
    0xf03230a090303020f0c18040c030516090f0b09190f0c05030405060a06030309090e120d0903080903090f061e0304030c06230c090d150e070e100b03070c05010504 71
    0x140d0740421070346601c5810104250b47e22030002682d05905240c48103880e481e2807809114030031282e003000304036004041d00c1012007103d201200d4216040c403a018003045980201c0700b001c9490f6403d5040e001512200002d842c205081102d81c80210348000028404204440100450b00244440c0d030000d08000248414040b0030010950031501100c41000345620395a000b808000141c403900c8181602e030505004240030600260401807d24030900c0d0b511000f240c048030052000301e00031808602c0c2075010601c00b131030002c181c1c1c0c0340b004050495906040303614108482a00008031518610080c20b0002d8105031180c800b840c001c074820307151184d01854604e0f00c1c5e03040d2040aa4544814292a8010040f00040c244040d410840e030f00c40e25640c400640011544007150a80041c00300380c42011080d85e80100d96100f4040c10041c04195807013161900703414801c03050300782c0740a6801d2a101c9014000074902c3c200540c0c100701207003002c0382e02541c41e0340d81a0030744401f01d5080d115604101e258004004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 619041142 1250 619039892 619039903
    0xc02090906070206061c0618060e0d0e0121060f03230307140f070b041a03010f150504031b0f0501171f0305010504080c010b0105070f03230a09030302 66
    0xd16040c090800781c0750028000356594001030038584103820311505a846003071301211740010a80c0104052101400c02d60483d0b031501d90714501115102d1a00a1103680110080354500c14042c860b079961014807403e80c01140d1490346c40028040c01410040300e03400c0d8042034410340c8001c00c080200c4080d12451400c200041c0c14a000c001614412510300f4441c20000203c100d602c2c080d8050007040c028484d0790b0b03007245070150b142044101845104d201003400700000d0050f0045034950b0702c0411002004102444c00d90000703100d42c2075000d807220400d00c031301102c0344240c5240c40d1640c50101e00b015038a4803580c50302e0a0b080001c0c01143c23402d110910442c2500c00940c0042e00c4282821055070701010580450342100404c01c150200c2c207c00c0051002e40126004401182c219009201904042c10103140d55803016138000142d41c40d1403d8001154061003d031400c4540040301010101c2240e14140c80c0c03061480c820607040500c40204161001e01d110140085d16510358031030b50920300310f2030040c0c03428 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 619042392 1250 619041142 619041151
    0x10b01030b060f0403020402030c0d0903020a0b100e0406270609050105010f0302010c150e0f0309101407060c090b0c0a20030c01030e010908192c121204060c0209 71
    0xc80e420451141d01c20b503e2000c490442c1e5060f640141d81e0303940c1001d1a0b640d0f0103031841401501e400c0c80c0c105801e00d680040c0d681d180d01e0094044c0d8455032940d048800440407548103816944003400000b070003003103081e440240780800d80c45541914083c4a806a450b1346800c1740c0444645903610b00c0c000030f12400348580e502501a08100388cc0c000c3c15600041d0040d50604001001710000c41d008800c00a220703040384802e603200c4c00c210fa110300c8400032015200d801c400e680c68090200d8850788500c043c0306070460848480c0402d83c4030301d0301e1610b0f154140a400704464100500140c51000246581148002d1011072038240141001c020740f4079000406c00f00c0215460780b000c0100b0051206503034003150403031000d042400c00140d801004007401d070140250040140c8950008120420f20300100d42042c0f242301c00d1039a811a059205080702d0900302c00382c0c0b82c004224070000c070b443c40c40350401c084200004884501113074211500240b002400364081e401010018001102d00d4045003400411141c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 619043642 1250 619042392 619042399
    0x409230c0301050904080904060b181f080739200102120d060f141f1d0f0405070e0316080a0206072a0302010e2403091e010b01030b 58
    0xc0d54500b10004e0281030001d800034041308000680000030307076200e0b44014018800d0810030354440002c000040a041c1010340b59501a401c1c034412101e5500302c24201e10017490b880e0300d5081003502c590000312924503140d03070300e04502c520420b9030b80d440c01c01e421146410f00784050750080341c07801e442c5000c01d802005299095600600044480f10342c1e87c0200e8980042100c8000c003903100c02c8030160404c0030b4284c40d0710408406100c280040b980310414080301c41c20500a89050711401d42d05070031015000e0348032607408000340d00c640d402c805071112641c0a0480b030302c2c01424052242000800241204d005451020124440b034038100001e040a002070210150f00d11900d180c02c520b0852541d481d8850900002e10a003400180c2c40704000b002030b0807200021070070160010a252140350310000c01c0d00c0f4003050303020410101000d052032030064850078101c1802d2001003200c82c010161344c134003600041e00d051924000c110f8807080c035076110f110515401003028000b28580d07400c400007404461600060901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 619044892 1250 619043642 619043647
    0x42607091d010902180a0b040e010b01080619050603070507060f0603142b090b040e061516060c02120705010b09010b0406091205010f06080303040303050c0901120b060409230c 77
    0x5680c429170b4421030072026007500c034842e54440200b4002045d100d90b103654403515000a220882070154092424004d0070380b00d91000c1e031204070400900c9103c4840074000b00d00845c000b40081e0920130040e641002c5141405800c1240c075507030346800d0b00c0540c9528100195102810402c0c895130078044139149490750b000e0401503440c0b08000301400740d003d2200078000349035246051140c0c0710301441c070000c2c05d96907a400d0b101d54903000e2051103101b040d940c191050601d00c4084520a80140c2294403203e0740610b00c420741a040c0c1d0719003019100e001c06690035409440d0091110b207101134001c000e6648074800003e0318028010410540300c2e010780045c04207040078402444120380000381c1c1000d943d1646880d41819160f03292050140c01d0b07a43c1c24041c482e0400d003001581c01400006180180e03ca81c906200710f640310030203c0e1150050f100b038075001510004484000711040d034064840c900003d0b2020b80f60584600206e0192000c240060f444807203864550a00c000c0e802c0d040702d4003c20301609051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 619046142 1250 619044892 619044911
    0x40b040b16050d020c19050715051827010b071e080304170403080403030e010e190603110403051209030d030c020d050d0f06091509050c042607091d01 66
    0xb0882d01501e09018602540042c020007580010801c13030030300e2510710001414104840c9070460321040740c5d105520740946500d414010650065040d03c407104081c540b1040144064001c0040c140071114440d02e449440780d160141130100d0120090291000e404401c1d40d03152035140071146181404045400840743c2c0580d0000a00080c3c00c8a80194225044d48004030210034451020700c81d99100411050b0f002400008040d00650a41c2c1c2080d000d8a802000e1000c0760b0910000401203150303614100002c2c0001d01659010783c1c003840c0d140c9406880182441e03200d0f0b41d910b241c45480824846000d4012039803040b14a4104281d85000e001031505100552001070065600c42a80c6102d50610030003094030040c01d1003a1b80211a442120b00f018880d19507a50354071402031030403024503002c4114000d40880c4031030b40b9010307ca0080c561780340d030700d80b82500d418120104d1805259903480d90840740b002d61911400100078070405001e0750f400000301e120107038014000d03500242a45400d80c1e4141803030704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 619047392 1250 619046142 619046147
    0x10c0b040b040201111c11030c0d03021c06090603060506120d050a0c0210110f01022809080709141311010804020301061710051e040f050c0603040b040b16 68
    0x1980c10590040300300203591100d01c0140c5000004c180c00c5141c2d440703208020003e0b00c01003c001c15421245407100340c21309008079143e90f128071500402c900c0c664004645000300e140310340d00600500b8003038040251280c03038104040080e660240e219403100b0303480780c03000d04c01d10080d4403c1c0340c6c00c95022211125000c4903400001d031580725413892041808004100c0040b06805029151800d540c003c01d0758580354840c65000c1e0040c008141900c40b9881001101c0f07003040c1d014800c4655980c1801c2001d28100e804488001c030220f40322001e102084201c1e1000074041c1000c10052024140005001c0b47d1241c584008041206006004c0d0420044903240740010449411400040307100a10b0302c410320740c2d200c1c001700e405850140d0010050f102003401030b80d402c80010580c900c4d000310f6540c092207207850300999080350710010f400ca1704680e041500460005181c1580c0620340911650655000008800025085405c100c3d810f582d2216500c04100030003190550b0181d10118030780070b5282101ca0349800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 619048642 1250 619047392 619047413
    0xf0b0916081b03010e09060106020d0e0904020a0308031602010e011e0b0d12030209010201110403020a050607030c05010c0801090b032e060906090209090a0504020d080a030219030218010c 82
    0xc41400032aa001c504100980e991071291482520000703540c950b580c0d040380c0b40c044801c0740c0c0603ca40c0114800450414404160003160300b03030b25522558030507801420480c540401800490f031044412a0010024600708084c3d031203a071400038080e8801c082844080d0035100709090342013050b45000a04030181c081c5004a80c0c01c0d508120001030681c48a00109000d1f0311f007540d020700030700f4404042d5200240c0c550014440d00c0c10aa00a110038040c03400301070918001e500000b0760224001c1d50034840c0d0304220300038190f80350003850080100310054480b1803c4840c007444001c00500c201d4018000d6140394012006140000c3e001440f0b0300300b101d10f0f28941c5400a80c0d01c4010840b80d92404420091150082000b500407180200f02e426651240040250302c0408800e0045850a0005a255000d4882d49201b6a0081d110754080855a990580030764000d8503031f0001d041e4240140301c0b11024000620081c940346480069803820701c540420200c0102c2c007411410030580d40109000606d50604 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 619049892 1250 619048642 619048681
    0x31902010f0206070c150b12070f0e01031203200703030c0f2c060405030f0c041503030e09060414161e14090607121805010c120f090510030f0b09 64
    0x9a1400c500d0160f11002c6c00342c141a040991300441440c03040c20500008914030302201c141d6180900c2c0d10756941514801030509100103403105480c444000e07071440c000e820a10305404044559260820030b02e601c032003507401c805815000681d40e82000303a500b94100620030701c4a901c5003401d1400c405a5900c2c0c0c1800800d40b01707408140c0002040b140310a4079010203540180100a040e52a60515004001da89940f03c1504512440c203011b001c21254903c08040019030b03030107030b44000000ba18034041c010701300000740100e03802599a2407801c0c90140c115041038000c03c40d038030305900b1117246001d0040100060300c10341c8600d50090145001626002015041054000030035181c59079004400100340b1f008440020700322000c030070b003e03000c00c941c00384080b08400c9214a500f0301c4942c0752401129900610b6400500301000d4000400c481c034020314a410702d01006260201806882c1d078042254640040401800f04c0d403541110f6800b01c406020b080d07221035041e260750041e480c00d20366000148501c1e00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 619051142 1250 619049892 619049903
    0xf010302010e04090f110a180228050d0515090a0c031512020d0206040306020408071a120a02070f1e020109050411040b0d0b04091a0604060b18030c031902010f0206070c 74
    0x4202c6d01c110348810501c080142007005646500200b0322140901940c0420800c100c041100e565194808903114400000085030b81e032800d0400090410030002004094406240d80e0513800d141e038610340c1c0c2e0f160142d00c15001d814021405820409000e03041d20702c0900b10113545500781c2024450120801107069046404440303100500e092030020801b40c1c800e40c0c1016140600000e00460290350000700c9104503050402403922102d1403a00380d50290141d1350400c000d0011140100e64020b03e2034024100050041810480d41d4019560b0075900d081e1000c9651158a0100364410940d84c220541600401c0306460500c8100342202c601c6032140f1681c055000000e001023001d0381090070f56409010311301c0000c3e1041040c4581c50420f42a0500c04881144070607920307800007030880c101401160120381403580d8850809110303030004004840c8032524150540300742c520a02a07070f034013040800104a440300b0040c0c0d02c58104e000040c4041e00b0005010b0566000106200040307621080090f10207401c03c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 619052392 1250 619051142 619051163
    0x1513020703050702030a051f200a120c0e15030103050a021c050a0b0f010801140a0b060c250e041502031b21161d0a05090f010302010e04090f 62
    0x1e240690740e030b00a07444040d4061003054216020442d000818401600321420300240141b070312141a015640d1420080140c03110800108100d40010720251100c4115030820040140d110080740c41150550311420b030000d8088070b45171040d410f1541c0041c0b0894580c47c0710034610340c107507241d199880491031303c02402010800900160754003002d0502032025805000d542040241e820034a440c803000351401084500a00d0000800c6101440307121400b200910611043c3d51720002c801d0010208900c940790007107420010303919014001d005407480da02003070314001a2054164150309402d4000e4121001e100210b0341404042401c11101c0d030003240401c0d502507926034503000c03008044660300400852074000807a0101e42c0e4050300480b04103680c1444900211643e80811045444036040003c030b011444881210203024021160321525076005040e40b8003040d55000428031300403040b100000b02d1203d00005008540e4451a8209000c01c111018005071503e0b403520943c13100c100720000c1c0790040e40c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 619053642 1250 619052392 619052407
    0xa02060f0f0706060306050f01030b070c0819051b0a03080a020d0204090e0318010f2309090c12060306060a210819080c040e041e0f08040806151302 65
    0x520048800d10681c58000540720034a030300e03226010340308502045501c20b041c000050b100440d003140e101d0403641c001ca484110340d200e0780c1041d14035010070031095030800000c000c031494040d03040e051115104900d81e5940e6844c2511003090545120600350307a9034540214400c1004281e20016154114103d80401641ca010b521105402440707550300403003445040001c039054858012001d40310090821440010201c914001160350800030b0f0f50b2040424902e03408080c03410114141d824000d02003950151804000c03c00040310342504070340d000e4204400180c5000781058005441e0307000241070f0010243da0810703000003103041c007281c0564804080340704100c180220383e80c80c41040c503e40100c0110394400a01e401d481c0c04510040ea09004519100c0106040f0703003c00c0c048504a9060307000c216050b480e6981c40711165405211a400302040e00c0c030041001c07404015030b01b2070003071284100a03501c926101d000703820000300401440c07880654440c10506070b11201d03a0191000c105000042c0d44010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 619054892 1250 619053642 619053667
    0x709170a0b1f1a030f09010504030518012003220803180609040519060506120a0b1503010b19110a0809030307080c0106051807020307060b131a090907080a0206 70
    0x903489421070340d008855103c824003d25008500030f0303002d802c43e03440a41d2114005c40c01d8030004d943c009c00142042090080300c0b00041005881450305141ca4404400c03581c5c40c1c04e4221841d40301c0180c47e81c00004a00700a117407901c1420221144442080542520300b0020513103a01907140102c0c2c3c000070035083c1c0300e03480d0f9404c01103030079540005100f001141000050720b0701820390000c240090f149814008103092404074180c4200d0b800d09220500940d65803440c180190500f00c0790550000c4452001104500f61079000e140a003900198040d00c5d6906038429100d0200c03107005c00340503c10f000e03603404a00306c004900940f02e0380d0007464050b03035a01c094010904d035100b900409064080086404444030700c1c19000f882c104c541c1228164103692a440d604521050250b6150300582d2040003448000381064201040340d14000b41090100d082c107041410076600c2e1842c9542ca100040d03001580c803880d00a100c2500300c0d034608014003845042c00480d641d034503203034000a03226070408180d8110010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 619056142 1250 619054892 619054951
    0x14010f0905060d1d0f0d0c110f0406030b01060804050705040605031e030904020a02030c06150a03120e060f130e070212090a08010e07090b0603060906010c030212030709170a0b 77
    0x31070310f60079401d180f405681301d6512466154079881c002c2c01200d8803542c0051141402004c0b40f030b00f00c103202010403039490800041a401e0010990003d4407440c001000c940302641c054020301040d150035001d46000e181042c00c00000b5040248185d26000c0c041c0f206480000744614030701942c2c100e01441d84001c000407499030042500c1290720600018450031000e501001034541c100204088440c81d4541d019480b00d603a0903906d809421450000c02000412501d02d000e200d00e10b9281405086041540c01181d01c6510000c1c000296100c0041c9000d038420540d0304800061401e044070610504280c2002510369240c45482081708034003080030038450790b901070100b0040410ba0002c001ca807220202c034549440c1503100791b0b25003c8c94408015601c2c20080c0869200d020014400c0e0070640e00c03d001503a0b15813202ea030035070840c41141d0401c40e00c0c900ba28001c42c051380050b29183c80301480e16144000683c60404012102e811400060001910342c00c49248c00c03010080c416001082114030800060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 619057392 1250 619056142 619056161
    0xa12030b01230a021501060c1205040b0a050304020f030601060e01110c03070602060108060f13020907020a061a030c0315040f03120501060818030703080109020f1e0414010f0905060d 80
    0x2c4400000c080c1014040c00c01000514110b400f520103958203a003404900030320910910b00804d0010800c000080c0002003601705e5102ea60404a0a080d02e44210341e0341a00202c00540202c2c80c00006e2005514004141501070801200200b4481d810180028503048608240b035051140310706040044000610000100e0315010b03084484d92036071040000c0d5030705420300c1428024011900842d8040c004003494605c103254000328280f036201668280001c81a0041c00f0200314007272070140c20b0010785a40680c88d000302d141021203a4410391002054100700e03801580c18030a07406181440804211901030650082c0c00c980c045a08034030b42d041c00d48989411403640400149041c001041c0c02c4d401c1000d2034040c0c0403150150264009002a1584c0e038415420040c011807450801000303140c515800801000d0a20f2100d94148440c071820140b21381a4845200c4046d00007140c1070244180198034161040303000d190070225000381010150008603a401418010140081c5a010070541d6400c1135298 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 619058642 1250 619057392 619057427
    0x2030a0908030f0a0b0d03020309090a0605090a0f050a09170d020408030c2508100b0301020d0c030b030c01090b07030c050c06031512010c050412140321090a12030b01 73
    0x5030301d40880c101800d01d80c100d0700345038580d01d0200c81c0724176424503025220103640e05400842ca0502c42001b0040f4103640100051940e17a01e50102140341e0715a1038255000f003200281c04284400b00d1401d038420b540c0700030001d807040b03480c01425074081680481202c525070b00301e8007850740d0303003200b81c040074003074880c640000304c0074403000600b211001c0d800207080250340f40b00300002c00807000f5038808041484140c0f180c4211a4070100c0c082001046c82d90280c45041801800140b800d0500528001520302410140300402d42d50303014411541024400c0201c100b200346092083d050500031142024050164040c0c10010340c240e1440420000708202a1010360040509441e46007803921b180e20404041c85140c080c03c6c45c060a4580608140100019010151102070a040c20100710502c0380000c10350964803402100c07007402c080041130004000b610a820b40340074440303840b07502022120f10b010344651800c2e882851280003051443d416040e0403841c83c41e021038061069001200c52500f104080e180d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 619059892 1250 619058642 619058647
    0x114070f030504140f060706050a2c06010e1b03070c020604090902100f0801140f12010e160e1501030e070b0316031427070b0a12020c1002030a0908 65
    0x5060300b09000d4000c0390003500c81354a8201c01c2c5414000c090f2a000005900a0f805002da880015455040a82d0200a440b0001504404a60303202c1c2c1d1200812100c200c080c44244800312031413010311095014200c0c0c24204111401c007400140032806171403410000c124004404a108644159200c1303010a800410190301c50381c546100c08010300165004070321610350341440f41c41c568000c0841f500325444075211140720740c4c0780c50a4034800444449801d98410841b03292001c1d135503640c225131408c1c0c2c41c0c40c03c0000341041400710417501e0412403000008000c0a580020800400c2c0d0040c92035004d01c4540c4078065404603000164040c20110403007540c14051050003040c1d910349100514030484580c0c604180b0018800350680031500d0f0042c03582220303c403020004140c02c00c6d204121701d6844c3c03d89400110618907030681c50800710950055940d242002034503420a81d48150341d441c000407004d10031441d2118443d4190f40c0c60811072150700740680c010001540340100c0ea84078455640d0400f07607442c2e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 619061142 1250 619059892 619059923
    0x306090b06192d0806031902100e0d06050108070803031b090103020d09060b0103180b010902070812040b070e06040605091e030307030e13140a0e0a14060403120203090c011407 77
    0x1e045110400c0a4005035964000558600d80010206280038156030070640500548e001d00404c441c29034526424800d2460b078007852525151040d082e024000c0c3c0002620f94108807666050130090f52007541a1b60040c024003003151914500381c0c0030344c0c030000207159480b0294030041c0c01038001c00500e0060036241c4102d48042c0241904680c0500070240d03010010601a0b06106229481032513010308206034000c01030194a441e80d0040c5282c43c0659204d2b41052501280c82581ea00200c90444031820a1428410000e401c841c10060007042101e00340d00f400c2c20020001d00c50302850f03405600c0b0b40104810310301d6902c841c09003c0d00160002d010b6a64440d09424050302c0c0d44d496400ca5801811071a40c64803000d00b00b84607200445118203007a8405480c1c14141d5400740000780407828a90040c3d100c100c0024200321000407210014070060400351525040203440412803081d000744042c0100208501000d010408141000003400c7c004884051159411400c0c0035440000b09046142c07410310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 619062392 1250 619061142 619061207
    0x60a080613021813170a09050d050312010305030406080106030c0c02091b030a060e010506090a030320010f1a03010501030506070c0c081006052133160306090b0619 72
    0x50313200b409040925004140912031000a00c180c1c1d00f04000140c80d06e406200620740703181da0380c0c400c5c1c1c021000c4031300f006454070161132075100a0784101c03055400094104501c1381c000950a0041c1501e040402c01c0040307149003c4c04003c140803000f40300b04401340000e414824800b1003070083c4500702006503100d02d84880740c00020700b0300d030192114401183c0f00000305890500c4c200c0d240803001a10000c2960f2071681c0c02c0d200d00703480b0341440305004410412524102000d02c1004150140c001000c61428001e90340b1400d1039a0401446000340d04080051012400000c1c4854001200340381015480181d802d180d2107290f095003101d24240a10b06010000381301c16000f0a0135030340100c980000d5012041c40c01c4a0a00a100010045804c070034199034094041880812050a00c044a0b80c5002c1c1400140001e00344100c54072a1000089284000030941c14803d0134043c1081130b10412820000c1c0001945a005607410b58011a944c1f07181800c160b071103825040c1c0c14004030000d1030380303401c203400c01d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 619063642 1250 619062392 619062421
    0x7061814030a1403010f03080f04090207082a280f0b0f0f09120a03180f0c051c170c060f090d03020412030c020301060b040b090405060a0806130218 65
    0xc00001c03d0440036041000003503007104d040300e00b1041c2c80c01216145944e41c5009402c46a10a5040b603414040001e03101251300041545500c508242c03076407400700c0c1c000c06294800b00511031f040f045c02d01000300584080040c400c5000d14080946211050186880c0906040c00c94001043c05012400300400c102001d000540504110f00f140d40741a40c5100c02a020907400b203c000000b40d0050f94088022070300348004180a110a2601040d00b803402e1814900100390341b08210303100020710780c6c8503090041c40141d08000d0841124501e914000854010050507803e81014101100021005000c201943c085a402c210703c1c4003a54600c0c03810307404a1000607000c850018041c00b81840c00c6112600c20b100b21026120002002200048280c80407500014840420ad07019940e80d1000304009140030003400041220480c501e594148107400d00083d01d0015040ca03010b242200414410300001058217a07104845103840f8641d107000f40001041070745980c030700100041e080303414004600058402c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 619064748 1106 619063642 619063657
    0x7030c0c060b03241902090307050f060c120403030e0105040f0626090a05010b42030708041e0c12080424230706181403 53
    0x1030a5640301c000e001c0864080d280c139003007040e0034188104050340d00c2c024032829420400240b012aa5400d454003030648149480c2c074207100303d502c032881076407141c9104104840c1e40b030011008a0030a60300600081c5d00050105a8041a95000300119821101c40409940200d0324000c0101e4a1003000042c0361100c0c106040407841c1d08002c0e100d21805812818081c00009025141031403c4482550324980200c162100310340302800c84410500c14001039500540e1580e410848525040025880e03c1d01c22000c04410302010a61000d01d09224a11900007426021024088040300d4480403000401407214000144400412250f1041c1078900c2154040d040c980c0b18101c1c03440100405249021545000a0f408800c5501018418101d502c00ca880344d02e02d001d402c0291460b01c0b44000240456449542512a10100700d440b001240e411040c800c03400130007031004503200e0303002d40c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 618884892 619064748 := by
  have h0 := BRFrame.cov_init 618884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 618884892 ≤ n) (h2 : n < 619064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
