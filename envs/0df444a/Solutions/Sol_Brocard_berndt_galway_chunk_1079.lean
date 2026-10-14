-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:08:37.926907+00:00
-- url     : https://prove2.me/submissions/1750c97f-dd1c-4b4b-8cad-39bd3ff42589

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 193884892 ≤ n < 194064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 193886142 1250 193884892 193884907
    0x901060506250b0112060e0d0912060906020406120b040c050307050d0e010221060409020d030f050f0a0f0e0f090114030a05010e150114090f150d151104080d1103 71
    0x3c41110098000f644450b01038140401488070f2032155100a60070200180b8000e223074050040c142c3c201a10981e003000040da11480c013000703426002080c203103070f1221095407100e4032590b01030b0403038242c903c10403d45803070150f904000d8649401107c10204044e1209440c5407071303040e0704484a600c804d040d2070400d5111085525407040c00d00c010408480600c02ca1418002c488680783c81c1c00001800e0140302d45e00300052113002d0381c3c501503039070007880e81400c150170700d8411500300b55218058244010034900001c99581a1650400c05c0c80c001c4030915a5507624201c084010080c00e22084005250054116801030010400c02410180303040310040444901118540d41d003420341d0b0100d04030181d9038000c040c60b80c1c00c03944460b007914007400501060100b440d600c0c00100700f040800801d0350505040c4000450400d45050b01440c0c3e1108010341540300c03000301400c01c42c912048800d410003040c0d180007409a2500d05c00340c00e1368280e8150710003601d810400304104580350b00042c0030b40c0002d40070402845 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 193887392 1250 193886142 193886153
    0x312050c0c072601140c030915010f030204061d0402101403010b0403050c0d050307020405130b180606120c1314090105061f05270301060e06030105090106050625 71
    0x920080c84500d07a440348400c101c04070605200c0c80007004540603810042e22440170070003602460b03070180115200980b00c2e0750b40c0c500c4500d88161100c1156200a0714000071400e0780d00e034a1824203480c0290350900c01523651304038009200800412200c45480740342c0120740140f420341e4800d0030040542c90100f401c1c0c00c581258001e258800c0c0e00a08022000007020420440140300c00f590004040301c0003178200d09140c6420351a0312900100900c01d0340c2c2e600004d6020b04107484110b040c10b40040d80528549001154a08800d2042804030414820302000440b40c0c501541e0b0700b0700c1440258090310f05402d440017441540c50b031102c000780185440f400d00e00810f15021012074441c1c40d4079400441d040c1000814810101c050083c0b01a000c901590019101a0007808980c20040c141c000d180c4402c401602ca140112207042481d43e0550030301000003035030340a0752000c80c01a101100200855210307201030320300b250048e01c140350b040707203090000d118680c40c180c000920007008500c1a040041141d40c03031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 193888642 1250 193887392 193887403
    0x10c0201120c0207050f041401060516140f011a060f0c010204090203042105070c05090601120e0d0201050603070e010b0d0f060306020406260c070807020307030f031101090312050c0c 80
    0x6040069004100c200a103182074840098141000c7d02d04000303001c04002c121a103400140034000602c8030014039040043c4e081445000c040d500060002c03c00d00112080301d854045417140514250b09046c1100280e50360002c90003c1004020800707403900d41d03040000182d68000711203155155500b0f000004030010180001c511a0b880b4248004100c002a14001c6821098980e0503041050a00c9540c0020390408403900c1655000c0b540c042499035103100480d8840d404600d0403541604140b283c01d050680003c081c0b41d03080e1107400078002947c514062503500d20080c45400c0c2c0c200d0398100104420700e0f00400400341c141200401207810394525003da02a41c1c2250301c1219820f500150070400294464089900784241d000d545144c040c001c1c041489032440940055003084c1c0c00180201000611401c54000650150565002e10781e80d00344102d003214140c1c0300785c0c04a0103144038030f005204113116544ca1544c2c9904d55503100020910f11400810004002035920003003000f21001e100e008014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 193889892 1250 193888642 193888661
    0x7061b021c030f1803081b0a0606150c1707170403030804060b0108090c0405060d020414060a0501020a2d08030a0c020d050405010507110d02090a0b010206150f010c020112 75
    0xc03691924100d482e00901405203020b4280c10010f0000300450081908015642100d03013040c1e4060303c4204003501444903503400c0f644144c4600c1940048410000c039500700c5001c8482d0304904880c620707080c1806450740d020103000146201c01201400740700d000f01901030038610380250107078003503201c40030000c10159021350815804504d40d1004c10041280e10700414001840c00c0ca400e01c0c0030704000c10403d070f6500580c10280c0c41681c071040043c45940f200d07003404424030b0f0000d0040c080160b891034001c80c901341c161089030003001c099102042079400004c01c0381d107203548400e01c06003c4d07280f41d0051001000c80d0080d51a681180c81004000c0b5000401941c040d40c80140c0c00a00150140070191801e900c1008032014048140010406680c0150070b44036104d40007205071402c0100400005e21411012400940c03080c1720106008043d15507902892020744280c01301c0710152114020003540a000c008400d40c05070346004000301e1035100d0151000c103e072042c1000c80054401018a20a90341d0802 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 193891142 1250 193889892 193889929
    0x60509071802073809030904060f030231090206190305090c0102070b040e09030c0102040e01030b01060c0c090b03010f0518160e061215010b0a031d07061b02 69
    0xb501400c0c00710300c905024013181c15900e00704c0030034031906400c2c0840110b407000300c40c011508000900f66190900440d181c0202c01041040070030b403607400780c8501c440c1900050780078584450310501d414944403520300740c040d00a00003141d401002c0c1e0a072400b5110114080740c0281007032003030003200d104a84942084004985002c0351510344a00f1417868000d00c00a418115800060104a481e4924048405548094038015a55030381c2c072107141e01d9881584080c24081d880010300080c000003900e2154180c0b8030403450f0042603682c86204540350324401c800070300484d4600408010840b01c643c840252404060008100c00c0c42d180c2c0e01c00e007100c0341143c058900d030210703000d4010903801c2400b68842182511524114003424000189200d11005251074080e4440c03190031070b001102048040004c050f50808441a5038644c0c85201254004459090101c2d08040a09010031001c480074804161400001d00315181782040807200c01241c00200420141040380c00e10141e03c6d2940e091100325000f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 193892392 1250 193891142 193891147
    0x4060902040e06040b0a0906110409150902210402030c180603010c050f03060f1c080a0909020a0c020103020d150b04030b09070f030b070311030f01050a090204050d060509071802 78
    0xc0c014070090b940b24011840d07194112004000000c2c0598584a40250002d500010140c0c60b81c41c0c110011301440140b0810f02c0004a000201d404483e00444010707440b044003038040f0740d0340b81d80d503000740c1c020710841c540b0700802454480b40b9800c14030611079000780020202c5610170581d01c0450b005c0884522144004809041002160f0800740201d008507203451600a11700450718407001d1300ca0002506151041151580510007580c581800700c00702406110b0112200e0024a0026200d610008640020400013080020010802e01c00d541c4800e00c3c61322200700040655004500952040018560b0315a4842c801c103003612490340104081c2211603403032540c90b0b0550070501c00440e00180680ca0540c40f200051045d01c0350018064226503020707000c01c4d0907840d0124250f0141201c40d031011819075020040211030b006083d00326040710381c1554216400c540b2414a402680700383d00407603822000d03090b08800040c915a2169078810184030076240d1aa85441444500c0c2d0b6260664803036a0760023 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 193893642 1250 193892392 193892411
    0x30702011b0c110603040303060b0315030601050f090a2a050d0b040509100513021e0a08121602030307050f030d0608033a1506030f0e0c0d0303060801050406 69
    0x5040540120300c5150401d12080d40e40c650712843d8604030f07140c20354042e110204c007040406029030400b80c090302110340e01c0d41d203e2a080712214001200b6005551185c40f0fa00d000180c1410001c4401440610103131a051195a8207110703a0090019092211041c034104011a001c3c82107a0f0821900c840680d681d50360364004210403101aa10740d201e00324452881c260501c000f07882e0000e28006840c8000340081003175540e00300c40120960010342c0c065044050454622040494610071410b011402c0f100c0d202001e071503804c0c90b0355860f0790029201d01008104894100c14001c0040781c0350b4140f00404482c602201d0b03681d01810420040d81e40030a503800415900f408020074001d000103410028019406e00e101c80d4242c10283c0050508405004a044024800c181020042900c00249800c05012111401c00244d00090340c034401c4c4000245001b000d4904146140103147c1d44c000d0141c01023901d0b144150030481c0900c843c920441c103269541d200000c20310300130300909200360b0141000065a241 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 193894892 1250 193893642 193893671
    0x31204060e0406060e0121021614060907140a051009051003090c0515070605090d030b0a050306010501051b010f0504030905030f0a080c0309040f020705011d0a060207150203070201 79
    0x1c8010020322032030514a00f48481c41e8040c9401e40150b03002d1170f120b0764548501c070b48500e2100301406407074401400000c2c2c6008000384004451412403103003d4000070030b00444040b0303844080541d0300d007130301c0e030001c1340d0401045190304032500e84210004c00c465900c0355140002240f00d0a03020361a40882d4444004020a143c00b060603161031585003003d0112081951b0340c2e060301400c40c00343d0f1384500c200403442c0b00414180320a8808180e40b05038100400e08010089070355030181d410b10440040c3c1044088801c2d400c1c11034103101140c40c00f50042030280d00305001034a40e80c0290b48040f1310700440b41040d03a403543c800d000c0d5881200603e000001d007800c050800525045454108030b000b03503c00c180d055076811700040c2d42c80c0c00540250302180c40e0081c0d122180d00714070414088940c0b20f428000c52203c4803150382e000300903080c802c00081040c2a90018600710801118541d00d0403504240c03260004105503400604082e40700d680d0b140b001c25440c8584034120303001074641c44e0060f95242d00c003680014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 193896142 1250 193894892 193894907
    0x7051c03090605040b041a04120b161d0f030c0306160f090e180102040b04090618050906070305040204020d0507050714031602011211040308070b010501050313020603060d0203120406 80
    0x45030714045107480d003845d020031308070b10030740c03040c0c0001041e148440240c001000c400c0e64042c00000c0644490351400f4142120b401000303a07141d0800013a41821115481e0285525410780005100b030f45010805400070821042d00490055030980104840700640380da0900070241308101207035109007001c2c12207a004061710040070300c000c00e01540c503100303001d880c031480640740c2c1c095a549800100c0c0b042c148200d50180c0a55803154054030800310380407800c0b4401d500440700350b030008041103e00d03824041e040c0054420645032154290001c401040c0002c0c8a50450380d4401d00150002d0720f42042901da680403144200c84240001d40003044041c10420b0620391600300c1d540040045017400c480614285060f042c54200906003c42135110020406680e001040e030060300f405456240da55a05040320543e0140108aa84070030480c0080b07852360207a0250380c01b8001c500136883e641d03107041e400d002e005c0d07002401850b80135214034481e00040ea02000340200041c1c1d01290305460b60b140000150800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 193897392 1250 193896142 193896149
    0xb0105040203060a050906011e020706030e0102070f0b18060106030506190e0c0a120501080a031103031006030f0b0307063209090c1b07060906020102090a090e07051c0309 75
    0x507030042081c000b0540c0d03000710b10f100742d44040b10406195260140141e8003512010a600816604c088040360b4054010030380d00c003198014ac50500107000c2c030790011402c0b8881d80d1001000890862425404942d0504120350710248501c50488184c0720492403d2418400340d11000010b525081040128100b524462989040c18001c690f012400c11012144030000140040c0711000041001204280326602003002c9125284080105503121038015498003d201420b0700400c03000f507001c614076070b0000100c82c840c04088907414216030a00304110301410b000410290019140d181140d4560f5050104500816042e151100801c40702d950a145102c1d40c4000f58028510204400303404c01130106c22240701d158211074041311270741d80c0416000302e40030b03c0000507601c541d0b001981d56080d00025059041c0c0d00147c403580c960075562030049080c2e1091a64041d0440c0760b10304c041101491541007201c0081e1030009688559132144081155100c900b1820f00840031500c8184040c15082804a00507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 193898642 1250 193897392 193897399
    0x190809060d0e101d0c01050f070602041403060f100e0705040503150106080907030503030f1003050712031707020c040f061208070c05030c1005090d080f1c0e0c01120609090f0b0105 79
    0x800f448500040c0c1721590100c000c3e05100001030030300140f5201d1411117040a41c0b0940c11505c0d0768862006800c051107005200740a0301c0b82001048040114943c42032091000203044540c075418810501960640039003400244841408013003200c2e03500344451599007502c4182c2c000e20b0340c9403140083c907104000c0c000500a42200e4002d1002c01c05c04012254028400c200700e48443d21001010524400140c1c0f01a0060082c0035010a1414030000400b0020380642e403a003030038092070b804488250000341c4026015034484220180d00381481d030000804868081c1c800251595243c411079038960042204a40b031500000c0c03004100481041c003000a018150001c01200d82e18030003203681e1043c4081d00805108002c1501c403c03550354030000501a40d400348899440e0a07507a0110661a002460040c0910110385461096071100d842240140248140208000940030005441411484965138500d540b078010104003102e15003d81c50545e403051054604e880a43c2c100841c4035241a00a03911 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 193899892 1250 193898642 193898681
    0x1614090105041e1107060204080a11060a0801030b090a1e02040f060f03021507021e0f010206192301060c050d03021309050601020f010c030b0a0503190809060d0e10 72
    0xa040503d00080e0100b41240344000604090100c0001c01a020f00200200200c1c00082d01045010002c960100010300c1580c5419210900700d003002030718015032000034006090b101c01080400c0119200b20f410240ba001a00c40d810b82035100c412440100900002500e8101d41d00340003141050301ca1001703041c134000b000300400b070b0501c0121401002d882c84041e00c501102c80301501d240011b0011181040d90081c10071280c1010311004008200b071030400503208010400d11016154000b080480c400e4906c1c07500340c0008060851000011f003103038444d82101518195103034190303d0000d14414081c040d02d455a00a91140740381840c43c0201d000146400c00d8010320403100541ca00a100d50b0039a00307100c1c404140740d6100170040740b070300340c102003500f10560900195424680e01076000b1000f2880a0717404000e031988420034142d4464201d00c80036441c50025410701d0104130b09c40c0c041c2051a50082c00c030f0786007403101c46000c03081e6a0304aa440d100c9800c07007805400107060305e01c20710401c2100d0246149 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 193901142 1250 193899892 193899911
    0x903090815041509020105160b0402090a0504030f140403170904150e070e012c03010c030209030606040c14031018050c16052a03060703140711161409010504 69
    0x160b41c80001d0300c1c03290b83c03a600c50394400308580c09001660b100280840e030f250103010441c00d050300d0022060300c0580c012001c0c0008150341040700d00690b031040782c060722801e1000c05041001c4800c500313080309000c1d18010070b020120005508440c250a1030406280ba192915407480c00c100c00c0710206000c502200380900020022000d1800007668010201d0406031409201100107945080d001c0408100d400642021000d6a0141c001010311505099008001c0035444e000240d00f2441030f80030413907140d813207407001500c20310f000e4102030300d0354000746400c0a4501c8001c0d07013000b07660429241c10398019a2044140305550220703420320000480c0240c240020b081c0002c401042c0c0c0300700c1030100c07800782e00213120b2410f0020404c2507901c909040c0280c030282580040c2404401c202114219110307024050104110741c1c8203006840701e0011036000c10324280c80707a090070360301400c03482c41d40d5426000740c0703003c51031030810b055420f401041c2d0640c41c0d03086c621203c0e0410000480581040d03100d40c0c40d240410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 193902392 1250 193901142 193901153
    0x8030121020d0b0c040e010909060b09011208031504180501050f060105030a15050a0f0504140708010e13060c050304050c09010602030d020904060b0406112e0f020c01090309081504 79
    0x800a00da0028034441842d201c074100316045201781d41081c619010340300f00008240505070302006c48c490180340d04001c1e85440c2130402a01d8082807049060b60310304400c000d00402d40840046802100e102400f460fa0216500440d050b075420518604414190001d420213201e070a0040716401003101c150b02142d40342c000c0000e041808044c001041140da50741144d034904100810540c042c102c000c01440d40d16507107207031900b544100c0380520b500803820404074140c11b01111081038001c5100352a201000e03820540400310f0080c3c010218515440e810310f400b4080360043c40344400404807030307aa5503070f0791516007401490004e00000751402024500700420910340e010040d40c82c0c1d1a0200c1016035a50001800900078280c1074024480400b000140088c81580202d00a01400401400d41c1c00d9400d00c440510340d482c01c80340d0000103109107a1100024000c69900490480c0a03240005060044510b1003900b15101101c0840c04641401c81c140000d0f00d04001d101c40c3c0c400110212145494941d40702d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 193903642 1250 193902392 193902409
    0x1308010b1e030c03011a010f050903030915070b07050d06060509030a031803080d0207060507140f0706020d020c010e0c030f0a06150312030b01090501030c0f1d040204030803012102 79
    0x5260401c524210740c01c0316580078003600c00081c2008009014040003001d52001004034011a103010642c1c210014100c0d900400a442160320028040c0d42440c07031380030074407400c0c4038074650721841c10000300101c00009502580c158001c00156480c4c98980c81c0b01503241003100c0c0c46170084414040c5c140460801c0c0e6500242040241d5858640034803140e140e0041800034045a4100a108410119030160221501d60142140d0b82c01a9014042a201e11304292000c02c007101a0701c481041c10011004020b15490007072070f0451144c03c00528000040309100704a070440c01d859895079454032000400c40000b0424000c0f06c035400c801501441e00000012a99a100c0500061049455002108a02e000c22049500075508090012458054100000c1c011300d40a806140070882d603120101d0254400d01c22244090308944500c1c03030000300d1600c1a25282c2b4081042c6041708031901c107144007919607002a0005502c2046101e40700d5050112424008007445d0241e803840001d8002e00c030159581200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 193904892 1250 193903642 193903669
    0x1e18010e060a210c0819060b04090905070b07050a0b0114010c0b060a05030a1a01080316110a0803040801020d050a02090a1a070606060c12080709060513050907051308010b 75
    0xc0ca800300954116501035a00300910903004420700d401380c003001043d04076030302c58131404444002c20448107600800c04120b0b070f50f50060040743c203800c0c802400b203c00550700c04c0e68414019070480e09010703500d40444040364440c40301115907030490501081001280c900303060150101080104050310403e0000340340340464080a82038150590110341240c4410303401c103016003005001c0d035880070b0103418121020701900c400c0e4106c203032005000007409500402501d0058602c9520fa4034908099210034004c2140004110381c000160400007400c52020001403004011460002d0380740d04941c0071540072100028800038800b03004100d004030303668424450405948441e882d40300c0a0041207909072150160b107000500b485d00c2d00b0404200107820454024541c0d1141d6841c40b52402e1040e401c60745400c0940c1d88202083e41d181051240502910150020740300c02680b204029a5510002e1858a000e40b5010041540007401d0341c2c619140843e198003801803440203102c020b5070000030a20b1080c0d20308 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 193906142 1250 193904892 193904897
    0xe010f0c030302040302040203040b090609070308070f052409010608060118020a0210050f0a0501120b010e07050d06150e03030f0d0213121103100603050606060c031e18010e060a 78
    0x10003108050190f4140d5000c0d50700030304219164601842c009514507800c1e240901c0c244142e600040741c4510011f04503050b03a030f01c1841c0909124040c0c0c0c41c041e1680080343c088902c0d00a20a4140c04680c0c00c184041d2040c03084904880b440c00d00701035141c2140c225070441c2c05c050300a540140102d44a96000c016017001d1051300503920701502c14120305021011004e24042400e01c021303c034444810300316041c0100c03080b080420059a80700344180104010030001494501c00390010050045107035070301d59000c5443e041c568500441a0140c1084074041d41051644800042c014110700d584070000000610042d070086280600c511448a42070003050071540b0075540010754105040500d01406d00208143c0102440f854001e28280704081c80e08956070b4040d100b0051101e403d100140510400c0340e401502405403a141e81092022a0f0301894441c030440c03008000000b90061b18445000114005116494691104d0315030031140745140da09075810040801128101c1d17076102d508a801c5481340b1f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 193907392 1250 193906142 193906157
    0x16030e070b040e0c0f030405210301030b24032410081b150d020d1419091106032409010308031302030a0501050c07020f0301110a0f0509030601030f0308070e010f 71
    0x60104415901c40d1703407503484d076441d0701005000c00c204c0002a203a0000c042a00729401c4070b0109914214130340001d20003d0007110400300451100800d03d464010501040711200c80c030401148086450041d000685183d09020241911030f00c4040141a07071f041010351900340c0000d45004645030b038550307603a1012450500303418044403040c1d590003001e50071008104d0b00d258490980091030390094021100c88481e56003080503442165030002c100c02d11a0111604661000c005007288034000c0c18110400c03540c015003458a80303519640c039005103208003122a0030f0100e00071803450300c03007203483e90704036042c02400c0c075100500c002015002901d9000d10150046c8080e4026400020310702180c44001401c46c4d441c0070f0900074403021040c01820603178001d0b84d0790740c1d07002c0c0d0072002d05080b50100d400e05922201d06009800c0518400d10220b440c100c018a03010741040040000a410f1800c02c1c0e1088038001100c410900806400001503944000c0e00c0c10707c03441c01080e200000c0c0c01c025070740a40b501003010381c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 193908642 1250 193907392 193907401
    0x1e060702011101150b03040b090d120b04060e040b040201021c0503040b0403050d0603050c03070b0c0303060d0c17010c170f15040e030c061b040311090c040e16030e070b040e 76
    0x7544482d03030f8414444c960401055075001c0350032050340207550680d0401940741c00145207107800140030800d19281e585403480c856199803650000c05105460345e034001d4696100080310340c0041c0d01503000310301840c4d1500c158101031002a250016101c101040d20a00328101011950007406885c0c0c0701c2c1d0401d0180405070fa50749400c031003521940c01c80840c0d961800001000b442400903201c041008103400300e44040e91202401c21160207250402c080e1a801000051400e04002840950061090304064030301610740016940105282151030721503952501c0d030391111a40300c071945042e845141d030200c0c058148841e03240c02d900001400c0001701c8000c20601000764031540e001d0080000102c05603a1240107001169855031415030310412141d00004005281201e19000c80302200ea0000410002e84015018042c00d900010080b00000a0a000001d901c030b5001004c00c1c4210300002c40c80900500464001d811640c01c44038444403a4041c100074811400c9540c1241c0c00c0d160f0100340b02d84590344 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 193909892 1250 193908642 193908677
    0x60f100b0906040e09100e030c060a1503080f030405070e04020607120203130e100f0806010e1308040b1b010b010e060702030c0d0c0e0108191101020c0a0609051e06070201 75
    0xa1354490000b0381c03491300c01c0040f2007001158618440c680d807481031201517604003d4540d00d0245801c1000c498000740d01082d07020b050b0b688041594840d120020500541d2034442003a6030300a40e410f4580000000f0404c020413000344024006050201808a0a414140c02080d0240141e410090410413440d00107040c8600810a84150060f1048480b50840d107518150700c4d09081070b2032042500d00d0050300819080e44425440c401d441515000f81403030f80c0780404800720040080c2401e030301488023407502001314200000500140c10401c5100d640c0f1310f24084922050070702c2c00c80c00400c0764581003a0000a030f0780403020b00004501141c10b1034840310a400040d0a04124540c2c890340020080c106204000400384040d0855040010341c03a85680e0724403060382c8a0082414561980601c420010000344485241030150141031041729480400c0c0004034900c019181c100c0d034041420791304104070518280c90f0310800361141c4004030480d00400008201c0c28011000300a061000b1051170402000c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 193911142 1250 193909892 193909897
    0xc080d060b0c0102040305071a1204080f1b0d1e21050a050708070c03020a0320060109020316020a02030c01080603191a0601030504051005090102041206020408060f100b0906 76
    0x30150807441e650318246103068002d40c00380c0301c11a00e5000e00507000076900f0020032546040c1e0190381d400e900e807582c218500e0a107580014011100c4200600c0b9401a05003148003501903482c051000c105400c0030307000b80324034141c41401000108084803401081c104610390769005d1080460400ac09080039180422400780310120190100300e1800040100800da00c1d0006402403501d600c1d010582c1d101d650081710003084004025016a221107020800281300d07004114101c04a0704800d841d0820240f08907050030802ea00480d0083c1e0040706010362503900d80403d0241d24a54001007014a02c6940807a440e01d00e4002c80e94140b02020000414585090195151120f824a41e401d442140741c94402259144000c039018030031200400208075500910503540a15000741c0201410100c17400d214016042c01080c4580c503540a1200040e0b020b40c04011007016442454096107950901c0405498020300030400d8114100c030f20240071411070a0100101a200715000942ea180304940c0880e8061 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 193912392 1250 193911142 193911149
    0xf0703030818100f050c0711090c300901020c0606041d07060c1115090d050115061e05040501091e0302060a030e010509012309241006050403030c080d06 67
    0x9000f200b100b0850b201c5164010900c84002100070405600c80c0d94800d5068041c5010060030940d05d00c2d40c4034a14a0082ca0455200e64407041b5035161040520b2034601130382c03180c0e02110220080c0d851050b0980d00301d08000340e204002030021030400a00325082c0c0c4c0e45a001416150156130791b6412a22645805d0742c80070145600e4000b2241050341d06d40d0000c1103840c1c0000166942a0307503d041070020b181c103035407203020f0070751000d001410103035040c4c204840007a28510864280d036840300b541004205000744d55006100946516411000baa05aa42998074101020040007001c100910039030b038000a61109403484145010609400c22103180303001141504041d500510104501070b220340d168026409801e0208003e00c8aa114040342c075080c0c1c2c005100780310492056040820303102c00f0204080f40c0c00f91700300044807080c0100c403003c80e44d2881203412800320308107103000f046400b44003000c81d88010000e9260507031806166490041c4603164a0b14024a40d040020718040300038200e402030b2015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 193913642 1250 193912392 193912441
    0x40f110405010810091508070902040515160507080f0118020a03080307032a030c0c020a050402070206120408071b0303140f1210081504020a141c06020a030605030f07030308 76
    0x40e110300107207040d42d0580c034447d81c00d1600c141e40b8045401120342c0241e4048580c0a4414118111100d404120582041c0320b042e01080e0044141404a00208808002424800e004c4c0c919400c0c1e0b0009a030070b44065400418a0046007103801c40180c807004211421a40c02c07011742c0c0c0d101d03201c501045000e0013250321a1600078498080140c100103071011018001071503034408000d142c445030310940302a03591010103980021040010409420300350010b20045100070304a40c6404030110340c500c40c04900b03880c16105c611021640344100a20002100044da065520610f40c2d5455a5801841d2050751280c5504019011800780703540c0694805680c40c640044c5503503285407801300c0307440b094000c151003101d0740c41c4180f420344001180003003400c5007d9034000e8a60f00b04d850518100c115040501c400164001070a0303e00c9400409410090b1003903d032040c0c10150380c40240310801019140d003500240c1c0b194000c91888100c0b02d80005086c070031607034941030040440e0340c0c0c480030b907001109100c040c084 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 193914892 1250 193913642 193913651
    0x21002100608010c080603060403080a0b06040f0f0f080601030b0619090504050604060507140d020f0c0a0f020907050a020d030c09080f0303040c0605030709030303050603010906020c0606040f11040501081009 91
    0x400301c10642104014000b195544217083d0f60301802c15503101c0090740e0140114540700003103018420282c1081303c55400150216250a907510010b4403281135a40c84840c0c2e002d483d030001d02c64601c1e4000610020140c61000340139950554032a6407910704082d00661044030014500ca85584400ca031900007030800d03400070002443d290600f240c13944400c45044400e1031a000001c0c0c07042c0e0140ca00b00c007911003111059801c0881c0880f80f280250300413204869184c0c0d086c0b1804044a20410528aa40d441501d13080c149084030320500c04008409000d850520074107001d07101110b680000c0f200c0000c206840e000ca80712051702e5080d81c002c011a004425030303001c5c450800c01240000001540118800c102d0780c021680e442e0003c986901080d12000005042c0304000c10129100707401003904080002e000040f5001103940c2c6000320303031010340c0c0480755400200400c03406242620410108990005051208800e8070f0b202580e244120f01485040c0321108000c5080424990701d0342c40604a410703000c02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 193916142 1250 193914892 193914899
    0x60403060e0c06190c020d140f0c101715090106020c1c030504060809120a03091101020601052b060207060501032303070b1f0b0a0201110c0a0210021006 67
    0x2000d4400400300e02810b01c180c8624801c6400d01d4400c0702c00070307880700c4190310055000301012511007818400c20399000390062111008507041400c5003040c0b01d420b1000305101c464180326a0b04000d410300c4507a01c900c20105201c80c40c0380c2c01101000b40304030844501036044d035404110b0412103003080c801540280b41c031400802ca0b642c000070400150002183c446644003111582e16040038044440140021410b002c10050980942049a04258041d0a403040c2072451100d401c207940104018200003615000490148a805112450024030070704c0601115030410001c14280f100b9407001c44204180b12864503091064a58a43c0744150700c8581035680f030340c041c100a03020700028081919004801d09042d1024286400d014001140c3c003800781d42002c100751101034850100a084942c4124521540b0302c400040c90800c1c40585804d2014948801c4d40400080c01c680241100703464400e020440d082043c60b00044984440b681268080c0303c1c5201040d00b01d042c00703410156800c0d0b2a05265011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 193917392 1250 193916142 193916153
    0x102150c0a14180415030501090305040905160f0509010201060302061c11190f090806100e0a150302040e0304050a0e0a05070f12050621010b0406080705010f03051005060403 76
    0xa210050080c0d940b00e6070607070154000d11540c440d480004403002c0308115440b50500f4103070888240341c440d0758a01c82d0f9035a9240caa15003540c090700007c034001080014180020341e402c1c401c260308821b030a10301d01e1005840c1940070f03140300c56440e98002808404a0b02c407241e43e20035005580910b0780030308882d0303c926110840f4103c003281c0c405221003c0d42403988203d010b100100555500701601d01c90303482c001419400c261080c09504e1200c008110300305c0c5002c2031000702000242d00401d100500690342e103240240d140300f10306000d0005607031241031401450200c2030300f0540300c00782c940490300091040c08ac100d48900e944260360049804c10918400028007200d065100c0f0311442c0c03192020b0115aa802904541c0c00000e0751510020034025801c0d400081111307070000390700c00c4003d080014203103244811054494031b6403004610301e81d11800762080f1400c0901a100c010107904008010079800c0000280c80340c46094201e6080556420004030321140109402c0c6c0127080180005035180d07141e0824 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 193918642 1250 193917392 193917397
    0xc0f061c0501080706300b060301081005060a08030403240e0d0e0402070c0b0d20040314030406081b070c03061a010908030306011b0615030b011d060d020102150c 71
    0x10403016015440000400c0b600812681405078007400448201c1c003404000d50900d0310086d444199481ea6605541110b40c499000a41c040c108481c002c08001c800000b0709000e9400c000d09a9009112010381000020b5002082d1350982c0d0b48404403148440880035030a140c0e0761160440e0201c28144159501040e07008902608100201e80da100c0c1b003500034030148016445a61310081190b000c0f00410002d18444c4005086071202168001c14407012011400c0d119101b0300c000003a540100040400070000f503030b103000c801101032101444c2030a01d009400307442482c00400d000200116014191607800040d000c40c4c0c2055808a40030304402c0d107030305003107008003021181c0842c458820b403000b940700c4d80111020011503049200952860303840400461340383c541c2d044040a01ca030b8500720f210000d1038502942c015000d04110f00d126051039410b00e42c10701301043c0c2c0814500840341c000c18001c6681031504951205054800301c020000b24070040b45010003096410440506c0d40d81440155040f8000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 193919892 1250 193918642 193918649
    0x120c070b0a0c08041202030702030d050c070501031b0e030a0f05011b02030922150b0702240a0f05040308030a060608150d0b07030207050d090503060f0601020c0f061c0501 75
    0x80549660350301c503900c084445910039003010401c3d00001a00040d0a48081c165105041c41540d05080e1990b000c40c1c86c1035090b010400c007040c2e001c13504c1188203d00704403410090909107001c4c418508500843da21004600da4840d0410440d0a014800c9850030010031031415441070140700300d0156420010f0003841520b001c1c8503110b42094025000c00e00c000252400c443d001810300100202402408424100007500000c04c541c071002d170584034561001c000c0004005643c40f680d942d0000303104024181540d00c04090340540003040e050320350300e040740585001100e513041c010040300d4002401d480b10701a9501c001c003103031400000c020b01c003609038000c0c001b2550f03076480304c01c13171625041500c3e04105590310a0b01e402c02c50b0808204085450ba03980142c1050243c2001440c0560949515080c40710810343c03200410200750003000300b0700b0200101540415187e111807202d042c84e00000752a102d4941c9502e208040442000045940b540122070b08071640307051254054069002c0d41001c2c00c030034407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 193921142 1250 193919892 193919903
    0xf06021c09150c060609020706090209010603060b040909020310090f020909030306011211220602060615090108041b1d0f071710120f200f010e06120c07 67
    0x600c010490098107004280d900c4218110004000b80ba0101da81a0041c1020f44585448140000b082c002510007007910900400001c20159090b0050024062069001c039041500c1c144040000d1000c3c0000e5400b560604800401e4405050001910340fa5484002c680c050f45004107841c1005050074118601c0303442561079000c00d5840904030b0b501c1c0d01085451134041076100076008080606a0701048000b10122401da0034442c00410561b030f00d6074214413084010200340001d00c191070b01004200c0c0e105100b11000c8201810700f020003003090040410041c180312048000c101000084201d000c4908692415134100c140d54038526503d04030070581c10003c81c0400c1c004640c1e181d4100125900c6039984d41c0741d040400b0130455a072040d9140c000c0c0070813109024094085490041d41b0b6900722102d01540311010009401e081520308805903180050b0054031611512029440301d0020124240003403d1042d504201b01001c1080c41c031030000340586801425007004201000200644002401107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 193922392 1250 193921142 193921183
    0x9050105040c03090201021b120a06060e1f0311030c090901020a0912050a0b071b030503190e0607030203070903020603090307060c1d10030603050105280204050f1302040f0602 77
    0xb01400c1d01102c01c40700029005070000350140841884003601441c4d540c0018080c80440c141c030b0048075082c00011441120b4941d29600100404901c2003241904105c0c2c5103600542a141c0c00a03086000c45613100040c804911862900c1c942d540601040400d0400640150704038074140600d18000c0d440031552001089a44502080c0041d1000d1617107843e641c408000c000268a5441e03800305103c004040d003003040800790845030242e4042007200082840b0341c80e00c5450742440c04400861650004550050f940f8244075005010700c0014000e41000503070600694035240c0304421554811036070000703500542c001080c0020890008010030301180540400c01020039000c0c3e088a00f49005240114104c0c0d404010012a18000101852580544c02c00150003543c941c1c50328207580c400c4440d0034600382c451008009280c00d1072148410000b1400d011460503041000090b40c0101c04041607029450b0302c3c00b04c00f0004031580c101d4010704a01c510b12400284d803544000c0d40d500c1c1410b0000503a8801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 193923642 1250 193922392 193922411
    0x303020f160509220303090512070305030a200a0507110909030318150f070e0901081009080403020a3008030402090603011b0c0c171e0106050405010905010504 70
    0x4290003000c1e4503148141811907107400c1c01c0041c3c4210281100500c40040c034070781010841c41c02c00c07504c00e081c803e031030214511480c3d0600e07074280780e810000380d60508401c05c003c40c0040c0d400404c1b07036445a000280000d42d03000302c1d00040c88404070941c03507a2075072100140c2c07051032507000301c040e018862003002060790302c03002e802c00e00200b0f0109884801d4641c3c030610124282c1400452a0001880000c00710740017840c0000360300a03400300a44039000a03d0820090119166001500d492031407400c1e1041409945855030b601d070b0f1000b440d4a6aa22655608050410088604c3c200c40c000d58009080c020421703180e4800003045211100340b00c0325800c082c44500c2c3e00c2c000c0004070245440e00a40c02506503525a000e20914880040003141d165594203803110600039004d2500400c1a0b142e0345491740d03450249440844e142c0640c110041d00000040c08005444002411108070700e0144580304407005940400b0780900320326080240d00a0034078002081000c12a803115040f140111400e00c2400e42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 193924892 1250 193923642 193923673
    0x1060503250f12030c030e0402030f07020f011401060c02061c0618150b03060402070c080717030405090c070c1706070914030c1c022806020d0f120e06090106030302 72
    0x118410f51079210b4540d491078001c44d02500380a220503000c1d04040c40303040c983c180010100ea000721154201c030b0720003005202e2156410001c0c0c0c600100240e00801000c07800e5201031a10b203038148508010461841c1c1c403038003103440d48001e5038000d034007035002d001100145400c03620260100d806800c1d021300e218084078510b8882d81c020092054030391103036085035505000c0290403691004000d01d03003103602084030310002098002a000141401c8010b0160301d410484205003806000d5040031803644107201c01e2200c2d5849610030342d00b0428441110ba80d07020145003080000c07100d03030312284565450080c00c440c806408113000384200c1c01070b030720410f8494441c0c03504038054640304101901030344109541085400e01ca464600c209a240990b21964440d0740d001641e10038070400207031080c82c2a0f014032a41445c1900490001d4480e5002408802c040380d5002401105031030300010400400c8042040b84901c0d55000800e00f00045040c3e80481c46e00c0103999000c0d200b10300c411401403003800000000d914 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 193926142 1250 193924892 193924919
    0x1b0c0607180e0a0c030608030a090e181b01180e090d0f1b110d08070b010e0108100f0f0e0307020a0602010606021f060b1308070b040501080a09050106050325 69
    0x5542641c1001592030784041d01c3d00820302c00c0c03468000d05a64480205e62880100040d080440b095603840300018104122014018400b17050007664440030030f8205403110010031520b407030000f09a1a05c000a45000040351409164207100c081441380d8100820641ca48408a522800c5a00120790a00144840c225106800000f030200080c81090328109110200442110340704c0c060400448d140e18110b00017050030424000480d248040000c1c480700300a901d0036024014002210604c45661402034240c3c0c5a0f0483c64460449956071600f860482c60607034000e0000d1300b001c4d05d01300800c00e0380094199903503210700d03000e9106282560002540e41d00c14059002583d40980c050110300d41954071403039160300e0710b20b0329183c06900d501002c80c45188100107000c0307002c6189000304000e86007000090601c2110b0b00903246012040006002e1642c2000c1c1c5540c1000152200042d01043e605140d8010860354120f0390b414001d21040890380014161044001c00c940f0305c00161440d03a400c02e46100300d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 193927392 1250 193926142 193926149
    0x10605010806060d0902030c04020d140c07031e051201030c030308060409110f04061a09010f14090609061201090b2107030b0c13060507060e03070c030b1b0c060718 72
    0x120402c0044901004c0b5000420307468409401c464021040c0d400060a03a00315480c030600080c2c1e1404614407801c1c04031405074000801102d0185051850b0b14020300c00e17042e880101148032a0038054090b410322030011030700c0c0c00118100851540d40c40c1d143c0044a08154441940011170100200c0c40b0b03481e05100f40107101d980100300305100b481600a0125165044107441c0d4840d42d6031a001030f40d480000441e150310440081000d665501d003c00140142a010719490200a0301c01c603050034000c90340e0112400134400300ca14a4480d020840040d50910404118900403113040000144a00e401c1c0c216410300c06084800b103202c00c2115442c1d0310201807801540c071080c1d000311810004203510700c11a6800c0408075682610b08a50003140e0b2100000315806040001c800080c12001c2c00001e01c01d800b4088540e8025514000c12511442120031060102801c440c03d201c02007034103040d0600c2d03005800c420540d40b181d240c81d000e84445803140b004981100101c0d052484001d901606003403154183c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 193928642 1250 193927392 193927399
    0x60703050f0f0402041d03181807050d090204020c030a090306060801020c0c13020702090f01090c0e0f150c190b01050a0e0403080907050604030609031103090f01050315041508010605010806 83
    0x1160f40b26001c20002e00048003010203101225451003404810600080001c03403003803800e02071820380380710070f112181c00c0c0940445104040c107024405403a82c030008555420002c1c1002003290102400041c0c02032003016040e00d15403000042c60000f0a410104101c1141e000f5101040312325a5500864280c1c170851500c294150814030400c0710703c1c80d02020140942c00c544800500785101076002c180d22440c10b41d4103a01800070100104181c01c0903000d103111422140c170700765000c901c2e02800305041c5180f50484900c580c403000330500c400c000e007000b039500900082c4110741761541c98881003100405009402d44140e803400c000400d85080540c3e1740f500300d80ea02e102481042d130700e50310308450700f41002e000e465060241d090006003540e100000785c4007031400f5540010380e42c2d281c0d141c0a0104210050303040d04a40050201e03112940e518428020303880000c1c00e0541d680c0d601c0e204103c00004a01d000e559001d4903140c2c4d07021b0034050248804082d40c2941c1d000f004a585c0b41c070019070741e151040314820762 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 193929892 1250 193928642 193928671
    0x4030302010c031506210f02030405250510050c0a0605070306030c050603040203120c030c1b01020d02121611030d02030c0f010603020d020607080c150a0c140a1b050708060703050f 79
    0x40c6103411020051140b4031560b000247c1c01d1716044900d00381e03402510b00f42c401e03a00c61120b0b1003030718290090480d04684100d400750007184c5000c02203071035120640010801c0c8032002c190803090b424144910540c1d181d2011042041d4505040080c0040c09640029140c0fa001c3d00301c0401c3c0d50034032400b100d0040381c0040040c040e110702d00c0c92070869a40810307a02e107554041840100c0301e9007010410009000d07102e00d03011618200c50400249041051348410b400c540c0150011480c0070504801c645054120f0400070040821605040c00c2059106490f990175214256619a50503804000b40c4080810701c800d490942c1030390402c641c262035080c000a9441030200c010350005140100080c03a40754444d41c079550415810032682c2d41050404503400441e4013031141040602071242c8620098100d02d8208104c1400140030310880c18002c8120020074880742c0e00c00f58042c12885545901010343c400122181d040c0c03666201c5854140558240c03010030304200c04035560740e2401c5100d030f00c6102000c81c84031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 193931142 1250 193929892 193929917
    0x72714090c0f03130f060204060e040b130c0e1806030106080d02100f0b0414010503070902070f0f05120d06080d0801080a03081906031a22061e0204030302010c031506 73
    0x685a81c006005034000b00c1c840d06413000000c4c03108400c10190780c090940141c42d14981407010308080505681c2c144100c2c40d020002d0400c1d0384000c03452451410b03036440007400342055081940c0400c841c0020079400142c221b44200091007091000d40300c5c0301c05070f0007803095654481406903112030409032000507820130780304440700ba08203074001070300e091205102062903100703031b8003050880d050100c8000d02010b0880050200e818200030100080881003801c51400e451511115051544c0980051000040c0021030050000800004a0107452050110b6440c80d81d1011900100042e2080a080f4080c160750104180e01406215040300c05d100041e0030040c00715030301180c01104c001e08d150907212999545d5644100c0d11710407074002c0e41c49405180d4240da950b12440300211301c004d0449207405040658215000c140300981c0c08074940c0110003203100808080000403880d120a0141182840400d00005240c0c3c150048884440280c07010072070f14440507010084090a0300401d03020648110050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 193932392 1250 193931142 193931167
    0x31903140a120e03030601021e03070b090106030209190b0a060e01030c031508010e0105060301050c0702150c010c0c03180f1403030403060c02010b1314040b072714090c 74
    0x3006040c4051514040b508004081e500488820120041c0c82d64404400c00c0055601041710541d5150300c1c1c0c900d2142c0d0030f0200000c607603e00c507210004111603d14000b2a40d07900382500310101840d40200203040c03910b071482c802c06040b5020b2120091a60030101e8144160402c6940f020560308640e07101400700d540c003001034010308228401e0508065942090303243d8510b0650719000038191942c00880d14a11412000707003540d2000e00000d1003070345401c0078014002580b00c1112040c5906a40e05a00030360000246003690003100c2c0d2000003942040f07100d1840550005541c9802031203a03c2d06010313200c0740b0303c43d015104c1290003940b201041c3c81d5428410020b01620115841100404403807030507499940361001c1da0008550840540c0d101c0014451074502029101c1c2030a8911800708100c0c01000104103241074042d201a20014030440480e004a1103440803070f48020100301e80031265511190940040d0043d4803600440c680b90600c180b40500d44040c0d92030041056003403190400c40090f19a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 193933642 1250 193932392 193932397
    0x7031e0806060c10090b0702160e150a0e040c210201021b04090512120105010507030c0201030207020f0910050120330a0e011a011209060f110903190314 67
    0x50000f44076119040309810454010175020504c00c804043c900d0170b00040c040d00d815140c1002d01a0500309880a00c02c10040070b203416403003010007028000d0702c9140c0b0003180c03240495800c0006145a03c030100028001c074034041c40c003204c4040e0880b0b10042d40c0d00c8442d4019620311900280140c0103110b5882e0b860061440f644103031040204001408445640c2e454035140540014501c0c2c0c0c0004241c000001200b44c011600400d030170708025180c4182030b50300070560401c0000c028149035010401900359150709403c204000c0d000b500d048181d0170b01d4203241d0340e14030f214030401c0c0c0000d820540311901c1d0180e48841801e40404580104424084144201075007801c40f80d000141c0c011184901050382c010f03002d0540940c4240354009000050000d00714292040d4000d074580104400c102418243d07031114036443c03400b8599500040e401028a0721401800381d20311940105814141c54016000100c07004008004044045441000788086041401074004074040e000c01c13210354a0b0410550758000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 193934892 1250 193933642 193933657
    0x13090b0d0312270c0603050402010f05130e0a0207150c05120606090607030c0506010e100603021e04080c091003020a060528110c0a080309060a020705040507020307031e080606 77
    0x10224030300000351140c440b0f0f1100002d40001000650088106114a0544480140a1520303050117540b8164002a107003d0100b104802041800241c400312021000c0f04d2401400220403141d90340e081c1101d880010390004401a1900600c0c441c1c1d0200300b100fa4410030b03414000700d0712801d003000380f0b140c2d049500300d500070092a04850100310380c075903541d00c480003003880d00d1080d01e5000000c0d038907060591800310142c018100380e00105c803d0010920120004208555141c80d000d6070f10000399181c2a9001d104801002440b20040b2380800c1c00d01c0301203020403030b1450a030340903011655002c03081d400718080c900c80a50042040d81040c45002d12540c010004620764140e2043c4200c0c10080110b01694400c3e032034000914625841540c422003841054000c00c011182c0d2007010f42004070042c0c880c454111080d10903100011a0010140288059401420001d20401061401e804003079281e03408008100e0025005c05a0001110a9280c0302a4499480d03a58100c09039180010b1115540c031004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 193936142 1250 193934892 193934927
    0x60409030c08030c03181506040903020a05060c1905040b09010f1b0b10050d150b0d05060c0417030c0a0308071e09150203070f021c0804060513090b0d03 67
    0x6000301064180d401540144000c00d4260751740c0c503141411401014106010104903001a603180500c0d04007941019000401242e0025030644289020b0749003080143c0002c08038042c0b2010840d9412005000c0c11030405041e240c6800d00c5c24012040380d0910450040450b100f005000400c0d0715481130500071000031140c10690110400202d82201001c051034084441400140030010f4030101145288020081910b140c02c101e40990341c0c0708001c41811003001c1c402943c444401c4107541c0c0c2c0b01c61942c807458000013a50414200219000d94582c440e02880c8150400c2545e00307000800008101e4410403136510140641080303640d4110f8030901c010f0200400c0000c01802400d1040041a00042036070903520b82d400342c103241c81541c2d0b102230614080c84003236400134031034100850000108150130030350460301c00b607500c10701d4005540030524801c0082e141c2d41d0081804200740340c020008206030101c4071405421560b0310a40c0c48141d0740e50025003a003100d004c2c610b4000007401100000d44508407503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 193937392 1250 193936142 193936157
    0x712050c0a080a02010b06160605041511030f160914061c0504110103051003060e030c06040c030506010b070804050d03091502010b27011206090c030f12090e06040903 73
    0x154102440d10716240c01c151000040040c2d03100015030240f142d025102c00a81e01e0f282080244c0154210070480d003940500807944490000f0100407800040c002d00206110003080380441d0300907072064940003142c81000c90503032000440c041c0511803c0413944e41a05030b0311501c070355040800406c140c824019805402c2427040c04a0440044078226410302e021000c5000641858503080007c0d40405464a09050510b401c050040c00300620020600740d0707801c0000403c060b400071a09074914458452140400e001e88401e0004000901c0c5200081780d0040702221003030303600c0345400b4070780e80315000009045420800040005081c0550324000340743c0203023030002d010703640d0300300c05641c807280c40d06500010303550349440603041d00d009001055400c00071b021080b0801402401003002e00d006000f10f404001e000001c3d0b2003040032030382005e104141d00c081801d042c0c0c1d5503131409500c03807200030404a407054184901008030b01e2280f0301d244211212010200c040b9142c420502006000d620416400c12502 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 193938642 1250 193937392 193937407
    0x11031f03080d0c180b160314030112051b100e0607120809010c11070b2a010c030507170106050309030705011806140714030a0b030a11091605071205 65
    0x2400c9610b070403281c085802590000c000740011260245510701e050400410f0060520307040688581c141400c244040c4031300d40741030030b03201030341140d145440c500c0c0008004100c00785c10b6040403000da4800d07021900e0480401c000c040341100a200c48035040000a422410f0031880784610301580032018200030300d0000c150712190103a107180703502503002c6180303003040c003518290074402e0b000c82d40b020386400502c03003c100340343c15100ca0b107621842c00020800301e200118003065008203a400c41001380c110040807107601186001e0300406144202191420300080e41d20b5000b41400701d41221040703c040026800d183c01514250000303022002c2610050090400141c030910a0b04e801e600c9859500d6404496403500400b940c070b0461012032441402001c0c02441c0390071440c10402060310407112502d81d941c80103407000402484c43e60503850700c50300801600344a10450b450850410513a51010140d440b40b8101c054070030001c403001d0000700c08025180204220321540410303901c41e40b0f4202c1c6010391 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 193939892 1250 193938642 193938653
    0x4060902120604110105090915040b030307050c13050c160809060703020708190302060f130b13020109080304121b1d090706020c0d060b120115050405090111031f03 72
    0x10072000540c0c0307035201c00c09000612092208079a40c12070f00346406460250030201141e10800c0180c0704d590130ba801084105800e0751250800b115011000d0102d0f51a0f110b00d080943d40c543c81407d0050041805103200369080d5418000c1c18801c41000c034a10b460568101846400c01c041802c050f51400c5062182d82c016a0342c42c401029081d000b0340c020b110780340c148a00340b420600101120001d04024500c4100025000301d51198040f49180e4100d000d030303807a514407200c000890300000300706141e524204105a9002011850128001e90740c46111a44444d0420b80e684520b00070603901000b28a00071700040c00b10081616070180c1c44000b0301c000c0741c0d100b081c4c8105000514482e405d11220a0030004401c0f005c1011030000d02c2c562008180400400b000701e10100c45003000907054640340c0701a01c140e5114443d40281c01000c0000030000465680d00965010f64580541c2e807103203007000c000c075814850502400b848981e81905c0e552540d11010a010b00d10090320440e00104840c01c040040841c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 193941142 1250 193939892 193939909
    0x140405010506071b05190602010b030d0c1202070302031005010905060a06080109020f0d050a060305100c09051201140106030b01090801090203030a030b0d0803070203030610110d0807030b090907081c05090904060902 94
    0x1101500600c12501700034001c9d0039200d00c046c58038003a42c803121000d00380c1548603200444141e0400019400a403101800300e0900e0010340010f0340501c200a0120503200d9158442412550102c2042016856001c20400b982040e4410000003e20420040c40901c54a50040407a0402d402e11645450714640e105010b0302c00440f94900802c1d0780d01d004000380f200038854001d151107100c07401c1002c0310100c10090f1240c01e031401000c0c02900440380710710317001c01d00358440030800010460030f084569581030001d000c0e01d507031000c49000401c0614006403454050103400c990541c01805541080e02d0b410086004025144038154000d41030446200030032100c00c015406080582e0103540d5918181080c0001800c8150a00c03041004410084003045804101407000c5061840c0c40041038548483c2200a48003444420390300c00402c10901040c170390005580c030110303032890003500d0061043d09400b403a128858004507000c0340041008642c2c520703200002540c0180f0076070001440001940200c0d4014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 193942392 1250 193941142 193941169
    0xb210709030f11040b060f040e0c09060309010c1e050f03060f18010306060b0c0303070305060f150c070b03010f090207051002030c07050c1c080c0111030405030301140405010506071b05 81
    0x1c0765010a078040c9050a020700017a030941540c00e10310700900c00103641a2071049105417100381c2c00c07000200345c10003683d008903141040f005101c151039081003400c541c003c0260382c041c18041141804108a00000d16402181c03801103034581c207040c458029600c100a130300051009520000078450000f10384c1e18a040440c46600d202d0a1041a605602d041001c0b2032103900548000352007401104001b100010407030f54041403e281c045000c1c0c840101049044800c40301c20b07a0b0045080365140b8900f41c0300300c06083d4980341e04080b02c3e0800d6640c091100e040c802801010094240300310140145080394008045c040e01c514201d499100f00802108100e0304103031103102c286180007c00780180181080201041d400031103d06640d1200c80e5890324405a00c840014443c1002080001c0004801c1d0700c56070480d0300c0c0c1d08410341d503441c051400e00e0701c942c001d000b40082d08400c48081d08150400b8840c00c2d040c0ea1001d82110710f00b21841d16030070b8140c8240030b40c016903841329820203e001d44510f81d40b603020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 193943642 1250 193942392 193942403
    0x30d06030b0906070e0d030e120319021c0215040311030d0b120c01050a0309050715020c030706020c03060703020309010b190906120b0402060f0f030c03040308010b210709030f 77
    0x141494010b450800d030001d803005082140c20540d0301603a68071102c10313424013030341820b080c51011603a03000304940304400203c40c8654000400d0b00c6000ca103400e64010200086d942c207a0725007031030703061134101d10300d00d503040c5800103078005d450108080346500c0e9095046401780c280490000c81124005203503510600c952051a519200d40071100d003031850320000703205805c0020b001003081d001c000a10074040c4214103420961501c8c40d03581440018041d8a002e400006c4401c2d030b0708003982d94081c0d43c8103002078819001e40700380180007406502c00300d007030020f41000901070070490300d904408a0181d0800361401c02c06569960495402c1da840d0445245000002804155480d1a00c010081202d030b403544810b9584003500c055000056000d8507482d40268120f9069840301c6220014043e43e00ad1403100c015040381c00024071090705800b501442c8128840d40d1180000da807a01c031a8005030044002c24800d14940401044010700a88a038941c040c5461070101e035015500e0715400c4003141c2c0e2020a80c2c0c3d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 193944892 1250 193943642 193943663
    0x7260a1a010b12070f11010e0606011106010e04120e19170d0207051c0f0f0203011104060f11160b180103060503030409050406020d05010b0904060e0705040512030d0603 74
    0x100342500004600400c2e01400941c10281508401005254010f20000030840e5000c111000e080c01105590349200c440c100800c001c120498215546610aa440a0103d98590245c9205100014580b03040c1c64007008150201d4560340c0e602d100300d1410101c50420f005001da80540180c130f503203801002d1004400805036003940b070070746032281c100c4406010745410741104400d2500c680e0000b0701401103640584083c54024880c0c04200d000a0140d00c00411540840110364140049011840e200070700840080206680020018a0a2113144141c001003a04c01c3d100b03074000c50044d030307a00c0d041c0244001a201c0c0e00900300042503210a0b190411002c1e03000200c0c10b0818000007601150b00c003034080c241004064148000a0b94030301841c818034006549400015041104da601943c0040c2d03038003101406196101d80c2c0241c003940041d00310600603842c004000448039030344024240147c0c0c10340c81d128901750500090003c031100c080c520014501c010041031441c1102071003442d00550080c54440d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 193946142 1250 193944892 193944923
    0x203130303110301050102070302010e0a030b16020d0c0f0602090a0f080307060e01052e080610140118090b0d0f0305030103050f03030402210f070305061608010807260a 74
    0x1411203081c002e00303a261440034001405103036000a0b140e01a00c1d02420804840b080b00300025206d90920740004040100000c20311040c1e41181c1c0c02c48028035010b4003603503503144041c0012244408a031780003a180c1440f0202000114070264000c1006800285c00303800c03505e840d0400002450f82c2c940c0054210f82c40001d40c5018480c0e64480d45c241000040001c1c40241403d24900b170314607048903800400c56940b003800ca00000585e0300c50030018400e80f0190f0b885450044940f1040c1c03412803141c0d9041d501c981d00003440c01c1d03100d85486e07544004200d28503a00207040503812801000b107200c40a03002070701d500300754010030000ca602d035201d0780c0320750f0314688e0301c0d815846c000c1e0400b1b100c40522081a4018030501005070390324a115800c486d0500b48009000c4400e0744181d16181c418006e540f0b2a02507460003100344074022860a02c00c0d001e001a000c000c02e8031010480310204240f042400325000510140400c8801d4081001c0d01c584481c05104590039081c00b55080080086003218008030440390f84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 193947392 1250 193946142 193946147
    0x3090105071509050c18040f0623340f0f02070e010e04020a1a070809180901050a1802030309060307030624080105010c0302030304021210020f1e0c0a150b0402031303 73
    0x501240343e06e00f028020500302030b40e800180011642d40103044c1ca4542c1110101c507c22007226403040002101004040e0a026041110755021580e841000341b10050100c0c1c022040803501c0d01c0154481e0340c0307036644135074507000895002c0000307600e00b401c5004403400040c01e485a1041c0502070b08810704c0340021420207204118914071180c0c00031204000c10b42e000014001d00005543c841c135003107a1003d0785e5529060002d40d54100d40d1030001300a005000c04e01c0305020b0158042440340800c91410000004041d5484118080c1c02030001d5041d8010031484d40035080520165401070014200450895260520002502c010200001c8600e00c03129024420700e610008150040c8000e0074401d07100202d0ba10000d4130b9200082010780107925203d42d015a002c010404490070111740b50046403100b41d80c5418140315400640c6c00c40c0000c003c56458804505101300f156088400c20b00180a1141203940e4803011401d10040c1c02d4000c1e94548030000d02e40c542e800218468010003409000071021442c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 193948642 1250 193947392 193947409
    0x9060a05070219330b030a05071205011d011d0115030f060b0d080a03050c041805060f040e030901200607141303030503160306050f13020f070b010314010e03090105071509050c 77
    0x44502c240e00581701f04002c00c0b004203000c029607200c949414211100d0f4149503003d412055054080d004160100b00104001913000303142e46040d80c00e803107203210000c191942c00d840c3e9000e40310301000c0c3c0301d040c02c01c00198100c081920b80d900c542000700d03080380300c640041c900e440d208009841039200050b46003551a41072140503480f0321302c0a140e0781064203200d0b076a60201280070002e0141641c03000455980d960b002e05240110300010002d03c007503095030150030b07125081941518003150b50030b100e5241032881110a803041c1c00f0528000e220701c0e540c003282207480f58219003001030b074000100120441641e1080001c03001d14041d895803036507820682c10341d00c00b140040e2a030343d0030941740c000b0038000c0c0e685451303a91329a18030490307007004021401c0c004c000091054201000500710009841d804012011103518101ca01812015240c0315485824a00b0f0b100328544c41c00d40358204002248883d0f00940160031018014101008c0501041614008590495a064440e607002800e84401482d04041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 193949892 1250 193948642 193948661
    0x703030b0d26190c02060705070603061401140702010c020d050d05030103170c1002130b071a010602030309072306070615050303070b060f0d050703030809060a0507021933 75
    0x80d06182040e000f00c168006910201074404101c82c200001096586034802c1d41e4146400c4002e80302159683da01c068001d08a9200b0100404d107800d0328a409980540303c614505114010180c0c9072100c580d00450340300400140482c1d07c458030340d414502003107003089112840c00745030f00c038582e40703506605003866000131540c3e40e4003000c0303000c02548505140100d62034602082c1c410b0007603200c848165200642d4820380e0040c02c2c82c480701280ea4030600508004079030000c2408203e0a0047c1d8950508a03142d1108a4101220354800340d02082007002d4156128002c250a01d0550451080320000515560110340140d0340161906040740d20541090503800040c24114011841c28855555107000b010340103000760b1007140240700c1c0201c4ca81303c442402c801d0303a82c02070a462001d40c0320325024010101c141e8485c8858410b240020303c099032a4403607203024416640080114a04104007580781c0c1c40e211750100c941006400100380400f46101e0f07074112400310311200900340c1e03003031840e43c0b4221001d102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 193951142 1250 193949892 193949963
    0x50102280c0609050c0d06090c0e040209011e0302300606030d051806040303020a03020d090317090d020303131406032503020f040e040b090601060f050703030b0d 71
    0x50562181640002011054a901803404200c0f0f180e1400c00c41c2c20500c800c44c040fa00220f80255060400c007031070f40700a0510340301d40115070b0079980340c0301d10070f03140d40040318000e401c220020010310074102618140d000c1c2c4005040006207040d241c1d40800c0031030301c070a804104200c2c40764803071010052503043d40c44101691003000340110f103000c1e0300081c4d0303920041ca1a0703070500100007007101c54540d00100703910101d03002501103a900e0317582e031400947e5550021000c2d00103010702050f00030308611403a0b04d80301710fa420442a5000d172820341c0d1484510b0303210710359140c5c1c0881002c0c04000161000d0024040014040101c006102c1c0340c002601d2140c07090001040c80340b0020010000c00c0380c0d032401c20a442950380032030110350b00c4103100194024414101011804440400e00042056803d090303244100e00c24051410107441c0d281805940304020301445020035650240120818802c00c041c0004030b00924020031140b85800104001c82510361003540d46807410b1b2152245011288103c07a07071668100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 193952392 1250 193951142 193951207
    0x11010e0f010f03060f0f260d0503061c05010203090714100806060706141605120a050c120c03010e06030604200607060c110d051305120f030403050102 66
    0x12000104140e00c8010181e042c400c4101c042c0728880c0c801d6201d00d0240100300030b03400e0803e4940b1544040090503110742407451001e003014882c2c2080d4001d60b0b100f0307115500c2c0142140b140540040c0c0304d907007004020582001002c03203d035590b004245121200503019800050780c03230400c0c200b80c900f000080c1d0840030401030050454142900c0c3c07250340e20141c90003407410000a4071003a0004440780700700140036203042d0820040c50780c80005070217001d001d00106405d481c002240000207031024040d8a980c032100500e0b0034001226503d054006a07444480c41941628004101840d5080030b1b200f82d41d0360050520100041c0000c550050b81150090710440080506190a5980c07107071415803001d42c08184180303903000e0130440e1a10010740d0744103030b4015004d0040e68403105008100c50355a49903500b9600ca0041c0074030081e4000c504a440c07d410504a050032a4100360078080440d14011fa032180a2191014026191300b003031010f1701c050351041c000540c0d11001d02c080342c05911601402d0030b006c42040e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 193953642 1250 193952392 193952417
    0x302100b010512090a080705070518062107150810050a0b160201051c0b0a0501110d110c0a0b120a020405060301061803050706020f0106090e0703021306090c05071101 73
    0xb001c141c0d0b02c003003600c0c1401c0c0ca142e92500302c01814522042e8009090795408103690081007001310300300007511401d448019014000f60b00d00e607458141511301e2904a0030a64040301e4481d0300340205881581e0b04409c6410903a039820942040c0720242c0b200c0ca00080ba00f83c14441600f1055807130078020003003207400420b494200f22000c1450300c140e0014504034008020071a04690050042d1100a141d019110126140390f62035070f4013030008184024420001030340f001c11650f0264800b11880c1c440b03e402800c0c00903c00c441681c00521241c02c01038180308251907040c07995038401c2808040c180381c010030354981202503902c1600800141100c0b10640c014403050101e5122002606c1c110b80711417400142e01c400c03c01c45650341021030707000a0098064000003160081e0001120001181014001c00040d40c0d00d0702410201e070450500352050740c00403041040545440d142ca00513510a000b40020302607500c0e400401100c9400100d003010483c080f542034140700322400080c41c114400e08200612040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 193954892 1250 193953642 193953647
    0xf02120f0916120b091c112b12050c0a030c090906031406010f030b071d030a03020c120a110621010602060601030c05181e04050c030406060f0605160312020304030c0302100b01 77
    0x2c41c11b000c00407c1030300605010051020400c000d101c015a0b003046c0761681010a5000c0100300b9041d112011500034031641103a10300520a02e481110701c0032441d410021425400c60140402d440c03914100319180320045100360b040d21480d00158401c00c241030703038101d40d10950740c10a803050340030200200035210b0803c00305882c000307500d07031044d01d0f0301d0311072581c2c104081c840040048005045805104000e200000c240e0000b0380600d00c1078046407410300703216041c0c80c1e00d03544401c9181c00806a4180381c43e06a507500b007030409004a40c142e2903102da07000c519107500030100f0400741d00c0240140e12807014452656014428224440c0491070880d190103001000d04580c40a54501c640c09440c0b824100c81400307408030304200c8250b1000b8004d00039418034452150068101765400d54646282c6a000141c520105034400c0403952180c4405090a5000387c0180004460b86802d409101203000e142c18441030f2403004501c15403180c2c50380c441a02a604000707250420107500014800c2c5405036040c0f031680c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 193956142 1250 193954892 193954933
    0x108090a05030307392a090203060301141e0705120708060f0d060203010f0b030f0a0f09020a0b0a030c020601140d05030904090807060f02120f0916120b09 68
    0x1034241017004010600c40c01082d000e2054800b2250340c40783d4a80003956140111031540c1c0c1c03160180215241c0c8402d001e4511001c022500e8510440e85d6820784d0400c80340040f034001d15803100300240000303104081d62a200b40300100842d40700c0c007120b100028038446d0303a400c0100c2c40d8120711b503481d0540c2071101d0062405a03004010b001070090010700400a0a07640d0b80860481c00c0b030b074015042d41041c40042c45c0440c00f03034000f8043d4451304600000c002c24130103505c80c2030b24865083d03c00c1156940c0c071624103000080000ca4820b001098940c5654030168a9011400740100000d40290b81e90f001070100041c1161180021741c0300b150084801004065103001d1004a103100807110b41903905902d02e4941e24503c503074501d058000b03091080c0350b401e00c03030440c014221441c0101418441020400208412071050004000300b0744500700200b0615002c1800e4030381d000003800121101000024070000040d0761942c000c038440707448110720704204806404038036007020221005180710040c4c520802101c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 193957392 1250 193956142 193956151
    0xf0603020a09061808011d060108010c020a02090a290f0102061005060912012c120301092705030901090e0108030706091a04030210060501080f04060f0608031201050108090a050303 79
    0x5040d500d0024250807941c4c80c0003c1180c00d008000d00079403103244008154a00c15160001c0c051000005520003040c050064020070b15806404042d01c998204210b11a02415280880b03913030319a42070700845420020b00240907a156400d5101c0c071148104007440109809103411074016200740300c0c108409000034015207404550103a204d106030380109110703400d004881d010641c01d00048080f03584009401004101d049a0464070441d1300c05d03409540c030791404c41124011042000100440c182e2680b1040e000080000080c89415107041e911081080c01601541c107a00f00050035420f0350b800140034402802640f03414581c41d8544800b56441e8041c10001a1080da00c9a10540070000103080c3d42114695111b908802d50405080c001c0d56042035101c0c4c2d40d0068903001003c5020740c040c080c03481c82807191000c0e0400550711230780c82602070b003945080c0091050712000085208442440036052894101070a84869854500010300710000500392101c030790040840a40480c1000c011285c0c007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 193958642 1250 193957392 193957397
    0xd0f0303020c03070f140607020307050606060901050c0105070822050a020f03010b100801080d0305010b0a1416060e120c0d08070905061b0d03050c0d090f0611040f0603020a0906 78
    0x40d00786580c0c80718103512903044c1c020b04002550040d00100b000341d5001d00031a07101c0030111903540d0381d625016a0b880c412101c0151032684000300162007884d0400003800840c1c8185070040c1841003007041daa0030740d103003590050007151444041000245d001c00703004c2c07030400c082c1300d2110342d101c0d0a860b01c0380c60f0404e88138040c1c02021003400901030f5444c00d4115511141024020612228400e00c004140c03400030300078030042d401100e018803030440c42402803078140c8481886040c40c250021070281d40d99400a0381d2182640c0040c440c9188481c5a4160512150b00070000030541902c2c03005050304200104049041d146420f2010900f901000654403d03901e40b541010342841c1c0f90701078282c54140392030380440d87c801c000003980c0c59584c14007489092030311180b000311224111030250942c03d0315802c84422128140620403a144880581c000780f8503103004001c1c1c010102d886403168401c0e203486141c1184035042c0000d0400038041c034800c2d01c03801032000d8a07046051082d100c000402802661048208 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 193959892 1250 193958642 193958647
    0x9141606140d0204080d0f02010b010201050601080f04030201060b0a0309020f06070c180f0504061b17131e08210402090c07051f1a060c030a14040807090b0f0d0f030302 74
    0x48a50b998111000341500a0803162801c001c0d030720040442c110040c20000550030310f85071956a5005004043c00340c0d805844401d0240d6410f0200c44101d10000d00c15000c541d200c110004690600c0c1001300103103c019a00418040754500500000d03d030301c014503500a500402641c000b10300c1101c1d14100b6900c0203031603e29010036141039800a071a4807084a003c046c642001d12040062503400359a159a80341e1305050500220070042e1000303000106640f025900c001c000400c1c0070010b010f00346006200f00c1c01e40ca440d202c6114420032501561b40c046500301c00020300c07158840280d03910142c1e00720b8014000b0aa03454507a002c01c60050b005442502c5960700450701808001040c01200d4020f0724a030b080c4401743c82400c01030ba015144d481d482d4a1541d02d000c01802e040d0429408464843d40175100031464104525400c5070903824028080b081050140f2022460348424002c1000510042502142c000148400c202c09032901035000c81c4208503042151001036003003039100c270185415080040c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 193961142 1250 193959892 193959907
    0x20a0c050d0c15030617010515010807170414070b1c020711030a0605041103030915070201090803030903122404150506160b0f0f0a18060914160614 65
    0x85950000d43c0281e08084807040d0840421076240d8066811140000d49602c000e40d45050207600302c0308140d0340c0c899400018070204180d540904021074100e40c2c00d15015440303103144e1a40801c03040c810b9404a8900001910160000808001c100041c00c9020402c07890312240407010200b030401400031502d01500400d10a00b403150882243d0718008019094500300d4040d4648080201000c640c2120703602815842c51000b41400010703143c84000c040c1592214000701c0c1c05212481d04208401c90422102110208800d00d041c40698010700d8040c0046844680b116005030401000a005a4040380314414045480b40c07089494072900c4816500000c4c411a0001c83e000303803040540026403c030350001500c0464000300c110307010440340160140103440c2c0b034110200081074419901c044000d030803840410701d2104035a002e400040110380aa1000303640b950391720307000d56424207000d4a55180e102401032029005101102009402c440c1d0303810024104400541082d0700c5290004420704003242c00c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 193962392 1250 193961142 193961153
    0x7060c02030319030f0f020910030b0d02041e0c0e0607020907030f0e1b0d170f040302041103060315091b010c051c02150103080304080913091101020c01020a0c050d 72
    0x111440c550300102018a8002041e0213009828000c00c1307440b1461a10010001e101071520030750349484d030014082e42507000b498404a01400d0180d0002d58456000c684074001139a85104003ea1a80300084501603040303040070008c00c440020143c0f03800d024100c84034141c25603401044804c0306a04a841c5451911a410210000e080255034903c0840c9421202944000000380801c061180b0003d0110301e8034460040c05000402d10030020501c078110710401003003481d5400a4620100300c1c488041c02d0650300c1c0c00080c191044000715030481071002042c446a0b003024031800340e0700511007200c801c1d9400c00c3e03035055036520302003090310003009455440c0070340a0303100395035480c0301036001412121007003200c40c0340a01c04c043e09090f59003d03100d01045102c1101400e070080341200d4010b1282da05540d55030700c1d01310040d4800800558021422946011034000783d1003000d14882c011440f2801070603050002a2403d6003c0714a141036503c0501400c00264814000d10141c03402600e5081071410310385000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 193963642 1250 193962392 193962397
    0x3081b0307030504031e0504170712030c050f10060509070302030603060a0509120d0f05101d070522031e0203071401140d0b03011514090408041d0609100807060c020303 74
    0x1b040d5440504040024660f0b4420060010380e002919600f158881c0005401c2d07076085988280c0f48055240000704000c80e002c2c07000003035040e008005441c00c005040c00d03110300301410104141d00c80d940e40d1a0074040c60034801c1240d6880740050070110326600b0000f001980c1e03030100a00b5909029291030008014210500503d40300005003608107071980d100415440280c2050702c0c030408524600000991624042e20b02007044a050826415211035003d15900c12504020801000d214041141000501c07003c00c0030542006a800c880c02c4a508524002c0502003041000780e41c800a4590342102586d80401c004088650700d10280742442000e000590b1040e620300412100054082903603014407845420081c0c044404034000c2082e840002c00d0880104c0300e40c060a84c0e042c401c09588102c6003051200280c106001c2c413a11800c00740c0d184004004c4c00d1054003094001e00c003000600003182451041c85803c0a030910400c0b004074100701c0300316a100114403c800402c000d8001c15000d41d1018000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 193964892 1250 193963642 193963667
    0x20040b060412050f0c090a0c051303060207111905120f06100317071a060103060308161716080d020702040f090b0901090312090804050306040f03081b030703050403 72
    0x141929655100202d009181d541c0105403254020a007001081c620081109200d459008018407050b8450b200e1610007030000e5080702041c001d040208840800403248100c1c0154400c11000d41e03214150304d008811103541d801c2880c0a50b600c146501c8110f56081c4030313401074070410780d00c8040ca0402404424035004040d011489140111424013181c008040c0149081d41e024101204003584254582e4034a8450114090f14802c92400788900c0c201c030100b4880d0300444149404560551661190fa540e03500c110000e004070801c1e4801c640800450501c091090320810480a00b4040d62300545100e400041c00020400d00c400030b11504000d00d5036054075040c3d900074108015410400d48050000c141420003524042003d10024458500502580c401581c0c50741d1829109140d5a2800c8050202110100c074981c405110101d5140c07000c10000707115034080d0310540d86c4d046850030b020b000c00310041c2c600d02400412210300001008110200c230f0f0403281c00c0c68001410b40d91410100c960340c1c000701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 193966142 1250 193964892 193964899
    0x105040519170304120602071407060203191806180e01090606031d1e0f0a0606151d101b050a0204050601030b0114030405030f0a1e0c20040b 62
    0x180084407948010511406440c2c4051401000107201c0441c40e03038a0099101d0050004214074662000896a0300501501849050000c0c01000b404941034200406c07601710b1401030f0302c080303580f8040600101c508609071405090200840046401c410a4608140100002e021102c0d81385003c078408800301354001d000301d080c03110300b03544c4880106014118034410b170130020f41031800f049548400d044030021034040d0702c0c2c000c0c1408100b00c01c0e40340c0b01c9604441543c00d00c2c054007020f40711615042c405078404e24400d100000d8110f0030861010b8031140440c2d032100801c040c00c070103401610a042090b058a2000301c0b030030700c10300c00101c0c800c40b00c014407541b0042d40d04640b80b4540c0104100068140c190b2032007107400740311554410004408403064031400a00040e149042100280d001c10000d40c5c01034020340c1964a010007203c1c5ca019990301c075606e4a00024a0700301d19010508484208240c03050031441d10b4000c40e05282c40741c01c801e07002e1042405010001c030180c0d06482e0740b680c2c0080d80300a80a0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 193967392 1250 193966142 193966159
    0xf061505030a110a1a2d07050106051e030d05130302120606040501090516030504150501170724050a091505071106070308040305071401090804090f051b0901050405 72
    0x502d880011420b20362061400b91319002c0c4040740c01800568848200c20600b4103140c286100c201190849101158086c203400d80c1400314a0a0058500002e0141307a0003040007007110343c604400d2042410401500c40b1003000c0c013541d040c44503075021a000301140c180e80b4000b40c540310070b91080c0c600f080031a48020352046412810501f03400020602d01d114440482d01001180e1366100000180c4001311480041214160307021a44180a54817a03508980950002a400200341c403008040322000e030000802814410260105600c080010a0240812595404480710544500c5070a4070b640f00e0701401388007000c240c03649000e200714040801030800a0f5840518200d009000e00340780d00c5044181c4e41c45583c000d001c022400c0160450b1301c40c65050b61229615039807901d007210280c20401088031401d00e4005040002c6c0c1003401f032072107800d0043c14565590f0785032007103040444418415210300c550401c010003a81c0f005440d017802950402c03614203035841c10301301e004803040e01c519000154086c809 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 193968642 1250 193967392 193967413
    0x5180d0b09010509070605090d05011e0504050d0c051b060904050109020a030f0207050c150d060e0a0506010f0f1412090604060b0604030b070e13050901150609030f06150503 76
    0x10965550040c040c000c003c111507100e142c40242c442d0010300034600401c03001c004040a900f0013940540c010b500440002554000448020b200d80202d080703480c2d052600c500600c0709110041c0002001010681448001800c00e41e8846450b078400c800303464910118000000c50030303243d09048030f01184005104001c00d603103d0307050b040250032052240c0006440c14466070880d40c41c0d0b00c00c4892a0703410800400c04e0b450080304010780c0c03015406605800910501c950365003044e036409018050441c1083c100b00f14900000051304480c03008000d40e04004200034206100f54002c03c80b1110351040e4a0550a00f4100c1140d100d80c91044110f020f24200049041000c7c0c04c1c0c010440c14040c3d4440c0500744a9440e02c182003081a025500001c0e2a810031480440c1e81d5078040e00051a2812010344031100203010b40c2142d0702101d4084440041d1039450306c014515410b003038000302c4003404090410754001800c58842201001d01c441000f481d003a960507281c0c10442c100508803006140060850700d880d200c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 193969892 1250 193968642 193968653
    0xf0209060c1e07050105030a110c0f06010612050c07020405041119030209070521040512040602031305031b06132c1018180501051305070e1605180d 65
    0x80c042c0300b03006005001e0003103191055000c907410f412510140d540e0350071340c0c890040b0040245112564440006800c10035140b41c17840c140312800e0080a071401400311989082c00250001c290141e800700620301c1d21007005400403604080e1581030303070141c3d40020243d94500d042c00309404400400b952007591800b8402d821901c10041005a91090300c54440170784800000f07032214020080c168540050448003049480c10003082e0940c80350080080300d1914001c01c40500182e407040e000500160400690b412111202640b6000105800c0c2e0003030509020790b0f0744500074032000e4400c01340b2661002642d022102100311220000d0103401000018019032044440c15202d05c1d50f11440c4210180d03400241002280101d240803580d0240d006004030024240d15002084070401e1070078031441c8106000d000c208244141c3c1d100304a00080150642140c3c28010328100c100d9000301000301956040000250131100c0e14802040d403401c001b80c480a540b9042c0c0c4520700160032050700145458414402e020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 193971142 1250 193969892 193969903
    0xb030c060c010c0e0906030d1b020907030e0c010c0503030105061b0304080304031b051e03010222090b04111b10050f16030b0307150203092d031f0f0209060c 69
    0x4103a0744036010a840071409101522074211b40300c0d54141c02c8043d03600b101c24014100c0781c8841e80c114868025440507030340010001d420a039002800607a6840e10300c0300d4000c081005280d032071424200826480501e940f51541d0703200c140100c500601020840710207494981001c14010005072054a07202d035103d40c034060f945d8209100603120106088070000d034040c0c01131128030076248081c120f41031300301d20705400a0059600940254066508003c0280040c1d800f440312a540c00b84400201c00680c501a04403003600d488541c01803166190201103c0c5580f0ba0b442280e02c1c0e110b8101412500130780005a07e0700703101860240604c0281450104880c1d104100300c0c0034401c3d85168180041c446841d80300b2030444026040d0389406070b10002d414420f02c2c1480700020012813061040303a1038440c140f40840c1007040b050070703424410241d21070b4a0034104012020720503080410340c01000080c499845443c84180354942d07080030f80780d55407098510000c05d60111242008080d0443d0f54410545050f942d960 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 193972392 1250 193971142 193971161
    0x30f0904141012030e060d050106080c0408061602070e04060b01030f0209012c030a150c02060709090f060f0b0903060108060c0d02160f080409050a06050a06030b030c060c01 76
    0x1246420000911601c04554560044050140d0804940d00b000088203000400c10000d40601803280203081c01036880100034031034804034074130100b125450294094200340300a00b200140c10003d00040c480c2d5280001d1032030788010b05c3d1451801600c0040ea00741d040c1030940c0c005880c2000c0c040200014806241c11900b2100001e030b07800c000c48a00c5460306822070080c984210300284801d204400c0c28000400b100402d82ca8401c24100800034080000e031514152001c1103800042040f44881120402d00c01d1422888103400030303103071501e4203210080078100d160142c59491a503072a14105294071540c4400d0142020201c00c200c49038848070782c0c0039182c2103800500e01c030b0302c20100045002c040100d5200d01402203d0380c018101000f00c0c00301c502a420a035203210041100d1100c210100310901d12350607041d8002d03401246d4440c14095a0002c0e940000e040c0061181040e4003003259445003035400040303558910700001c032503c030400060300344001d08141071380c00302c0c010401130010203040d07205480d003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 193973642 1250 193972392 193972399
    0x1e04110a0e0117070608060f150a030e0114060a0501080403050d062d0f21170a110106050a090e03120a06060908070b0d020f040902030a0209120a0b01170f030f09 71
    0x412450200f580d80307100034080c3e800010208000319445060100240214200040441c0d46840214241003400d801c40f1081c0300010b40c507175904044211003889000030411301c002c0009840e2405070041060600075210300c50406c050540042c050501c110203440c0c0109900406200883c0d494124460244400c0c11440c4040210700c0400c0c0a0b8580c0c000030b01c102d842c207c0030716005a00e0072003482400f0301c0079900c503200c1100c045d10384000180540507002079404190125501c80c1a4060014072559071a8090700143c0e14045043c480c60b920418240700b00c0304107802c0070505102d01c007030380b80c154045e079850600301c1409502404100e10840d0400000d03594107981d0341e0621039071042415507802581c4110480070f0400c00c105483c0d11090f8009200845680071036600d0305030340b440c0b070104a0707000700c41200a01e58042480318045c549070400c001581040030007030009403000d80320703400c280c401882a031400d2208d450316514180c0042c000c00c1220550301041c0c031380392480583c21510716482250040d12 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 193974892 1250 193973642 193973669
    0x20a05030610050103020f040f08061e010b0d0c2a05010509120304080703020102090607080702040605100f08090705030703230a0c090f020702210111031e04110a0e01 73
    0x1024200065900d10840b10088120038051034000150020740c000c070201b1465030000c220205081403019505802040c4507402040c2074542041c0740c46215080c0408001c40c40700103c0104070100c154015a0726a000c220000201c2003a0f200003580d80410441c00250300e000020318205100802c2030041000c41e014400a000075965030500680740e503d01800e12500120510126011a01d224081c00e103052103400010310f841220f00000c0d5107030300040f030211140b14000452070210b00380b900510340109019500040108185070001c0d2038401940340040401c040b600004254038020401c203001014090161a4041e469050110400507001d4800304400c03941c8a40e40d0505100044440400b60001000644641405548000340c03900c0765032003031100d4081c00000056926104840340d013400030350b8408044002600620300f9101c1c1c0f01d04a0203030000500070002103010072990100c100309e00b48d685038420f503100e02d4407100004400180c603401210040010444002d404a418143c1d080045c4241 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 193976142 1250 193974892 193974899
    0x8100e010801090b09010e1b042304050c04020a080703050907031401021b15010618081902090703092a081e12040b04090509010b150409060b09100c031107030b04020a 73
    0x207082c1d0b0500c48035100c50323030300c80f6460940c0e10035100401041030400a001262440c5100e00d448405075011444041c5841d0040c1403004001d010070200c40022020b941c1036062014491002c1c0056000078400c10a241d15400001c03030700502072040c103002c1c43d1b0048031010f10541c00b2f06414000e40040700d40e10410341cad00488040c514000011360f1041c080844000f00e00582c00e2031000c65080500d071004c070032026090a0080f480010502865401c0022504a40b003101d0080c01008a9000080c200d0008c5c58a0140b4081c04120b0120030340c080c000303080300304424440240c401000b4035042d5600040c11030048000e040340340714015030f410009250007022240100c00142d840a40c0f4840d070301c1038042c41c1d02c0c10003081100c900c1c0b03500a503501500d41000003d13176221560100b00c0201e115080186840d40003c0d0600140202c0c3c811000680b00e241004c9052041c1c0e200072803120040f01c0546014486006e040d2420148070f4901c1142c0c100e030840039245007079078034a080301141006590482c4901000500030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 193977392 1250 193976142 193976161
    0x110a0c090b0402090a2c040506040201080c030f061c020d110f09151e06070605040b01061b0605060a0518040201080f0402010c170d1d0c0d0206070308100e010801090b 73
    0x40d200c9030310080804405e549014010600d14100000311070001c201e0203030050100701c2c001421842640150b0180203280740502c00180030000081c0714080301c44c1e00344103000ae00c0c440e0903800ea07070083d820380e030080203c0c9140c0d1601c0102c4090860095010b180d10429a04010000310b174149080310680b01c0c0e501d10214102001042d01040b02c00152651080e000b000041c6005803002017003468090096040c4c500080218000c1d5000250640f01e89448000340000c212445000600400303051410200c4200181205400c01040c2000034003020f4848011901c641d50302d20503d0b009107401082c204541d000d405160044245c00c03030b410790115280e00c0000c0d40c400d109115152155074165104000e01c150359848111042000100340316441c0103102041c80d41e4030a10980700301d021034130000c2141c12241c00c00035160801d490380c00360080c6002c03800e980068984c1c0003610502c540c5404c22103040d03990403002c00c02000655001c081410000030002400030019404028801d015400704042035a980104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 193978642 1250 193977392 193977397
    0x20f010b0307060c1b0f03050102070c0503010e07063f050a02040302060702040c121508010509030408060f0c07050111040e0f010807090e010212070e10031a040c110a0c090b0402 78
    0x403100031405000d0b41c100003075220611010480f0811345031500c030315194444414090300d07c0d0001c0b0342c5a0b500280d62410b2003211121a00204021002408205000a0002d44401c40d038450380003807103020444940365102e07440a5540c01008501d40c040100c041074001c01901600101c0200158075140100310010000d008507000d480e0003030b2142d0324103006542484024105441414100211042c21020325541400f982d0148004065900d62682c1048212421500003034440300391540200300070003000e6004110b140d4816400109075201b0f541c6c410f00c0040501c91003c005119520300400c268403a41100c000d0000d80b2080140341807a561948020300d070040080c0200030140d0300c105810891a4066085201611302d92000982820402c0001222505045c4d13401d20105420a10501281c100244013020040e201d2070140444401e550160520815032021540a0350300d403424400b500740140074103100c14801004071000101c0c2404c158032510030307901803003041c01d007085500a403500e002d009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 193979892 1250 193978642 193978649
    0x7030201180b0406110109060903050c0f01050103020f010f1403090a0c0501080601020703080c0a08280c03080103290403030c030e010e030301091a0a06030204083a0210020a020f010b0307 82
    0x1e4500c0c16003004ea058910120007501701180b59240c0807031400040c0d6901449440600ca9210f40c0e88030880d83d9000c0341400304a84101a4070307803600004101694030102e11000110003070924a4041e40414022036609500314041c5030314980010501001404c0002c07500c864074010036280d48026264001112a50400d48820b07006078440700003403002c241c0342c100130103150034039a0448940072135035550310000e070300002c1e1034030990f88251000700000e804203049000b141009140c4864800d507241d4016203012818000902140180090049000082c07010342d0314100882e8400c03580c0c0d161a140c001c4c06007100c00300c4080001e060107000701440c00705000704911488048055800d40c0c3c20541440000c00284251000b038040310721481c1c000c0d80340c0c4001c28018003030300e80d00940e8543c10311404501d01003500582290349458120030400c180c1411802080c01c81c0302290446920101d080300b20b00d00301c418145018203a1000402c0140305800180526286906030b000b804098041010075854905520 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 193981142 1250 193979892 193979909
    0x801050108070c021e150c0705010903030c0f15180c0609060914030307020415030309050a0b030c0901031d0f0c0607030806090712090c050103150513021312050703020118 75
    0x1550703d0014039201800c00c80c042c40702500340c1c00070502840002e016129180c4020f090724000122618401c9041c84110060726003800c1010459256560050104213810406080080c00701c02d40310411004880c40c10b034041c813000341030140d60440c00104122060340e030003c4800116015000034034600030051801110301580b142d0000c0c91920703075000040c10b24003099a62500040152a006036102e10941e04400c8042e8040700c0007908618001c0c02d030406079081540b0a02c40b500d000c004041d00c2a089903801206a119141c59900400042c1c001d840c1030b55a06003a2400440b60252210000418982962084c4200e42d031900c0200d051288911500780045c000403a2400002e10030305201030042c0d00700286140c030324090810422210211040c800e0700312410361501034100036540c0d0501079529020400241c0c0d11003203203003100003044138125400741a641900481c00442c45091a00e81e40c2c000e02040d02d0302c402841d11407524030784402071808101c3c0841c1180d0349003042918010a202d05943c181c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 193982392 1250 193981142 193981157
    0xc0d030e120d1803050c0607020f0a06020c0102070b0a0b1c0b01060c0203030c070906060908031c11040e0c0406030c02031204031206090e0a02030d03020f0301140303041d07080105010807 82
    0x35100e031410755001002c0814040c0c1c4403444002e14844004060403054001e81e101502d84840703e072a6801d201c0042d0028045610a4160f000d0010011078a003800e0b640c00f009c0181d95800705050280039025007000600f84c4410081002040c00c2250880c81000004540c1c00003144000c4000100caa681d48101a050000c07400050143e980501c4005044900043c01ca0b400c0040e0500980d1801c5616088500007903240c003c10810b5036001800700010703260b0540510309107003020740014586510100740c542116141e0300703400c0c90391018130129000b410440d910841c16152003204496181d0092240744006460030301c04180e1070b44080140d408031072498030303494410780700c1c2d880c01c03100d14007180c03038041c90580e641c540004e00035414410382031400e010310041d204803c10790040606080e40c5000c3c0200b4513004004e04020003c046040382d06650144d80302805c02c8916034082851801140c100090101707c40c8660190101c148040c0342c0309a62954946602e0780e00c4100466207003d0a84803107000c40c00c00b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 193983642 1250 193982392 193982413
    0x32708040302040b0315100e0705041203120216030c0510060312030c180e0411060a051c0204030b010b0409060b1608030403110105010b0a08241003090210050c0d030e 73
    0xc3e13044205071040c002c040720740c010345004c028090b00304241d9a05000b40c5170f8000030441d040c00c104a00b80d00010b2800d02c42e092910f00342e8450186c034543c0300010200640c42080c0b0034200c136298103945504416040c0403401b2440e901c0c014101380c900d0a02610244141c00c40d204005000d80540015a0f900a10a034004292010305a018088024288082c0480c0e503030040851100545840c00421181503d80319500b0107060150b40100b021030010701921040141990803600041100d408542c03442e40c1840d0b541c070503580780c0024000d54100030201c8640343e00005050b0b0b910000340044d1250b6070b00400c40c2a503245201c0b4241d10620061061506d0b4403441e0402007000a0041c40c0d00038000e0074120f581030641d4000d9802c48009030454580341c0c074041001d00205038014012648403000c01207212682e5080800c01c843e6403031000100f80300c2c04007920183c17800c1e0301ca0381051301c0c0d0760343c041c040c0d03c0046500140a095130708007c08041036441602001e069192103801745201c541d14803406800d04445 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 193984892 1250 193983642 193983649
    0x10f0c03020a201c0203061b0c0601091401080a0201020d050a1b0804060e0d0b0112031103040b0304031d010e040b0d0c0b28050d051009050403032708040302 69
    0x24100000c0d410360080c0e203072400108120725a0010a4080020350585460541081260110303a11012541400f01d01007240010b1300c0c00210f03d07401605c60b0b03000e200f015400d80d1400c1180c0c40b404014403a05d0003120000111640c80e41c102d10103410582c101c81006030303243c1d03102c00d60f60681d40b00060b0069200c2c2e801c0c00305c1d86000c0c1004080d41001440e10503150013440e0386480954000243c115111440001e00300501a031054019800340030031101c9070038140a03030b22950118134040c016648113234104400031080500584001c10004450300903a0b48456440d021244190801c860550200c0d40301f0460110f003075158500d00312400816120b501d44010001c0904c00240030541541d0b4105183d8001000880c990301140c10082040300c0e441d642d510b6401c12a000c02c0e40b00c40010845000c128448002910303000342c10f6649003411514005500c0c1c2d5102d000d03041c035105035400349202d54942000d2200385075140d045402a0f0084012108198074003084c4511351410741e04000c0c01840d0144400d00c018035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 193986142 1250 193984892 193984907
    0x5040b031003120e030c0604080709020d140907140a2106020408030708040515030702100f0621061119180308030f0117060c09040203040303060b0d06170309010f 71
    0x941480c00240d01603180e682e20507015818003100f102041341c843c1006164074081082022200b415a0440d05061401100c940e40788c0c001e01480c64025008160f0b241c040303c0d00e50050f096000401221030ba03034180b81c0809926481c5034006c01d01080340d10002c4840070f00700007070780310200c409011807506200101011003a440f00f51000403950309800304400541410100050107040e4017071034906641d14541001c100701800d002c1452000f609041c010824804c0d004188180c800180641c04180316518480e00801400c890700320100912046641400d240d03a2007c0312031001e031040c1d07010404404d6040001c807070340c040c2542d04c44002d000054000310392446031006000042c80d0925000350705072296560101d9802c01c07145501d0716010b1600401118180c20f0304400d0907010b003405000703d03003040c0e46440c0c200d10420b42414003903900000890101880b0380d0151000305801c1007459100c410001c01d800152886204485507000c0f2001000503a200c003004451300940b05844501041c0c02100080e84c034407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 193987392 1250 193986142 193986151
    0x30f310203070504110c061608040b041a010603060603050601021506061612020f15040b070507050307120e03071406030f041a07020705090f1509060427021f05040b03 73
    0x1070146600010b0b40e07455500462040f01d0145c20099211114170141c50304d4440000c141a00c0a1a141c000f10700c2d4507000070b900c0c1d03000380e004081020303a5030702c6040991040765000c070302c0a229041d03c00009005540b56003c50180c030700d181d505110341c1d1600d030012a40c1e000901b81104030242c1190205045150810041500701c02e00750202403048401c0e181d209060303058444a10242c1c100340312031083c4080c180015002400c5002805000b810140c841c1001400001d000405215002a041c402d0080c20025500926440f00d04803403884402040240300704034202060b4007070b03c100703100460300702100481c41848100181c621801c541e9002c82038118044058025070300c40480b04d04501480200b02c0065104542d950010960249040c00f4003850070002405800204044000d00003100c05819800c0e038104002c1350f051505846400014000300548003094810030382145584c0d0001e118170310f0070051940200c880e8094050b21055100100c4000300010001610401040c45044281e40145421 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 193988642 1250 193987392 193987399
    0x901020c030109050d08180607030f1e1a1509190519030201081005011d0a051c020f01020c090c07110d06050405160b040306050405010f11030f3102 65
    0x4a030501000300b42120001c04050301d458020684501280e6044039946410180000c4924010071100030307015102c1e03802502c0c1c1020142ca030701c0200c0041c070030780e040403000001c01201e00008123a1442802c00034090806100100920900460300700c1c13030114100c848120345500414034080118003089002c403001030520180c481e1500020036640c4075141120310301100a004007080034214000500f40e030340000d0079025910b00c1c203d018000369a0008600e26074481070340780c218185280c100060004445a00540c0e005421000c080f240c0307148060565008a009960801c1c0040d0b50b90012602c1300225000d458000d214480818541d032034000003812054040d6114000c040c80f003034000794006070484d0b015561940c44078103210610100b1b0000a203050b04004a9089480c54503050321001d016510005e8900c0703655000140c1484000e4021f1040c0d02c0410030f04000000c038080c9aa02d040d0000c2c2d4400007610b100b040000d4840303c284c03480141d00349000740c42071a03070720206400302c0c0c0070201e245040780c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 193989892 1250 193988642 193988653
    0x4060503130b2409041e0204110f07140f030901050c100c080702010c0801051003020c031b030a090b03040308181c05031b0310060e031c05040303030605010e03060a02090102 76
    0x4282100b84060240030200785540804143e410300484940040310084d200b8400032040c00b000030351081040e24070210b41c0b03501200381c5d20640000b800904040140900d010b80c0000e001011202030002009480d101c0c0c00700742d40e0a144082070365030703800e0a081c61110b1076104002c6d10549601540103020302500ca0710880d400b215400c2006025110303c041e00f2400300300c0c11030030701046540a0203200d006400b1890710001c1985090009554001c50081100c1410f40c00100c80000310020b000b140c43c0381002200c0c042800134007001c1950f5a03880100c1c0000000d20084020440603840d404032401030f601540c4210203a02c0d81c90312200310340c0f1801a0200b15200e150f0155005603403000000c0181411515900d03146c0c40c00e51144810158100c1c01c13040624070800c1000000380c50400d509094484c9485c29010191250021a10380f4000d41c6c0c2d400d17440c24225514400003a84a0005d00c180d038401c2c0e8041c030900f1b642d0001940c0300899151005e60582040d000100040030f036038041c10344450305104842e03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 193991142 1250 193989892 193989931
    0x110a030513051506040609090506010504021602120f0105180a170702181f06120b031f060807050a0b120901020d0f0504063206061b010f2004060503 65
    0xe1810f00d81103500c2121683c00070410603945080d00ca0100240060b007010304c062420740e035609171161014000ca511882d0301140d6003141400c2c2915a40c94281e019040d400c0795420520019540d90800d1254245da600f4500000d45500342e003c0c070501401c0b4581c1c001d1030203100d43d07510b822602400041d502e161440502502002d0707900c0c22a012003500034081c0107461402d2105825084113a103800d80c400b0100507031010001c3c20391002017246580c10500c00050b60701160380c0040e060000d142c00403180700140c40008030480c54140d104004450301c220494a2107a0380e4018070010f080c440c030540c1d011500c20311407042401c000da50707442d5100070540c2c0011318100b00c2400040441e403080d1610030447c1d956100b0081040b50610991804803244003c1e0440109400542010001121036010001081c60041511510b0703130f900380c0e4050420b04c40c41040407140c42031158000c051109190002e1030030007810413154054000b80b40c40c600b030b08824039071803d03090000c1503d10b984080e2200e0b81020250708182c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 193992392 1250 193991142 193991153
    0x30e01051c020c01060801050c0d0207080903030a11010e150403030207110603010f0905061504120f02090f04020117010513150b040f0f060503061804020d0b0114010210110a030513 79
    0x1000c02080402006843c0d01c001000329085501c02d4101d41066850700060104940d15081910310000d422400503a43c4c0300240b4190250f80510b0000c50303058030001c1901c070042e80d0007100700029810410020403031506004525541e84079001c0c00c011821980101040200e07200780c0007885074500400d128448000c04001244031580240c0c0001003d142044040c8241921030041d2034000500b00c81607540488911481a40c601c160b10450001c596030250050400441e5600e04ca0001c6d002006904203240806515a4418080300c041b80010301c054072802c09000040c08140c180c5030b0107404c03803021654128540004003502800103a800c0b80c13884001a20310901c500030005040039464406010307152410780d440702281c5400c9001802814820004541ca404008909012203008a010f403601eaa001241c8051704000c40540022001000850f40c120b00e11080e0710071003c203a08442c01c0d25021540201188c4610140901d41c4400f0082e03205140e100342c00061704a00100c001e00880513441c0d0780d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 193993642 1250 193992392 193992427
    0x6010609090608010b0604060e0a030f060b040b040504030212091206041b05060309031903060b1201051201020c0a1b0b18130204060206130311101d011404030e0105 72
    0x60001440c0d900041c4299425409204010109031000340070745190840011458011360007400204100c0c0d1100b881070780c1c0c03840300d11401107070040e54400105034a424203a003d030a203028102d000b14200b00e000f4865003080d10408d0300c03550f00b543c06080d5040f068421850280c1c406e80c00c0d542d21600046104030700e4007060050b980124401d00e0f1850203d0800d91040d035055141c1d0f4031092040328140200500b10801200300d0b0203551003504d212151a0701c40105070020300194120720b421070f03408240d814103448600c4516058a0f0308a540c400402c0c60610020f00341e214074500c0100503002805110001503224409000c1c482010000d500c080c0e032110100015508a140400300024400e459001d0301e0034181c1c0a80800c0b03402040651616080000c0a9a50000501440d00441240d070000040c5441445d41c1031a4039282400d66403401074105c205406060400c5503541e10030b800c240c01148280051003085414919001402d019550b90303201a6600000c407001c90341031100070000b41c160160301000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 193994892 1250 193993642 193993649
    0x9080906041706060f0d030507060f0204060512090601060509060f09040c1e08160810030210020a05010b0a12030f0302191d1813020d0209010801090b0f040b0103020f030f0601 77
    0xc00e5032484865011240f601c0ea002d4034040c0030f10042a000750f401c2c1c40c1d2000f180503c58040c20101e64074810341ca400001043e424400080303a5101040204400358820014241c01c1d0345481d05409a840f407a10250b2680300c00e201d00b0020a41c2000402c0d19070403c24081c080c0c0c60340002400d42803000440100d4181d03070580391000d001520070710b0625911034802d04150b8841c0840d10386403880c1c0c07810000c0f00b0070000d2400104414002e00701d0019a007105103005480141d903004c0c0c05a05a8070002c000030756248001c0d041200c4c15403c11480c85c0c00c41c18809095402c0341c4103115030004020040d141616010886c00e541c10030180c00f0000390310a010114200c1404a0740fa0383c1e041c0350800c46107424624141e20602139032003855441003120201d41d040990301d13000505845d0841107400244002000c030381e22900002d401040c11000041d2000042d031090392001e0117000314681d0b90f030b940b280d444590b40007240c005000b0b200200061002d400d0454200126078405000c60706c0e50300c003d00900303190480991 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 193996142 1250 193994892 193994909
    0x41a040e0903030115030b0433080a05070e09031209030a090b12041b170606030c0d03090603050a09080313050c0f010c1401021209030a140901080a0908090604 70
    0x240030011030514640c02540720140002450a55050039100030701e06000a0442c810162203684294859031554840c1c0c0c01d4815048055680c002c001d0401c01104801c648516040c1c85a228000303400403021a2504d02c050303000c1c001c0d0219500b45110401c4600d405403103500c451100748052013408a44000700f50290070f041c4011904da801d80400203250346d9554011459203481840480c181030440d0200b16001680103840304041203800400003070108140d4013900c03240d200c540c04904481404181b29001c1c00c820380c181e815042d00281030285c115010300000700020180c0f541042420310039441941c1100d560400400d8011450b11800e02130f4100740e5032a244a40c3c0a200c50b03040150412549540c10300a503003048008501c28001380151104520103441d04d040c0f6011a8910b020030350440d16805501d2004690a05040741444e9490b00b11103800004207010008510444038031406803000384105944900c0c00f03039100e090400241a00007000c5610301028000441c40d96241e1000c0d00c060710304074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 193997392 1250 193996142 193996147
    0x10b0f1e15040311010e0f0d03031808030109050108061e0a0b0409060b03160f210f030c03090b030c0318070803180a0e0402060708071401090b060103050a1e0b06041a 73
    0x181400c440c18003e50207501d05000c2400f2010103680c840114010b902d00c01141d012306192607908080e000f130042d01c00e0003c41d80701c91040b508c0800c032400303010354140c44500c04c0c1008140e0b21605a5551139078160399441c0074021880340d0440e0501600c4032194420345c1e4000c080303805003240e0081419078010b42c80850780e00e500c4154113000c904003048010401c030307007017010f00050782d107000303014840800e19000303c900040056021038165004402d4100d4910340c011621134900c040d03814000d007c008030031001c400045003000d000034a43c1c90403007907e01a00003d00c0503442c5451f84541d4410000d00020001a540259140055220018005001580350301704188002d80d13840000c200440d0b149404c000e14a040031014003015845040030745412660010180703940d80b07860f0400c090001c0700034801409540c2045009020041c0c1040c1c201c3c080d8000781c0f4180a6074888004110507136503000c4040c2502c402d00c8400703003c2d010003500032407180e0700f002e020140b80035100c0d5102100034003044100030240400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 193998642 1250 193997392 193997399
    0x3050a0f170406170f150f040915021c1a0d140a0602090307080a050d0e13090303060e06100206070e0a17030c0c0a081f020c010507030518010b0f1e1504 67
    0x1100e40346034040c25030441c00030245013000b42041800400442107010340441402e0602c0c6403200d52010052030f41101030782402a1800b100b100107507107c1401d0700c146080cd405100d58480c840d0256030361103a0100c400105405030346050007081c628000040d151012500f869545244040c003461441d94002e442c05641c1d90001400d243c50950250300a06141d401406c5410118401007041c1003034589070300e0507100c10200b8900290104036200321800400e40740500803410560594001011030b14030b00000119640c0f1328040200c0d032400c042c90107000d6000a400200c204d4403c1401c820303a0140100900c6103942c49412542c00400e040110710050791000032241c100403820060b4404155044801c1d00c1100d00f48040ba58a44111072064075038040020000c0302071041c0368050ba450402030000801040c41c200342c0060141205540d4000140996060030444040c180500c218040b000341145445988240500483c0101a00314071071100c01040400165690b9010010302d4003481d002080d1076906 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 193999892 1250 193998642 193998677
    0x5130501090c020a0b1602010b18090c04110a120f020706060519150509030c1005071b050109170c0919061509031e020927010603050a0f170406 63
    0x40b621484801e5502038140300c000a424114400e610400c04c0c0909028a218000709034050101781600580c01109210444005580130320080c0c0b00d018400210741e04414001c0c180021100c140d103080340081c00c10002560124060700684030384044010001611800460750b400890f0405038084440e1519094104141e01d0404184100759035406000191140341c00614030048140740d552105100d00891401110341c1d00303002480310500b0144c40101d05080c002401001d0ba409000c0848145824403080c139200ca59424540302130f030300181c441e94005230a010f060040f010000e0624500342c85514450b91041e1202d051080c003650f070b400c0c1404400c03c0c3c40b110000c00c1e2030389900051003c00100314000461a4024103084c100c3e40c1044040e001c402c2c8001107501d680004c00d00180d002111001030100c0d180d0606070001e400070740318500c00c1e44041850301041c280c402600c009051640600001c2d000700b0142e9440c04030192280a00b000b032907005209004803a000343d03009002282d4081100e0b4030b02078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 194001142 1250 193999892 193999901
    0x14071b030b01122d120e1017070e03060a0b0d0507240206090703080306120601180608060903031f090e010522030801090c05040b0c03040305070e071403100513050109 73
    0x9405015440041c0028413a4070f0340c0042010041c11840408496080c450b005601e0030381045c2d000760184841c1e0044c5040034040311807112800c10301a0701040095a003a20840043d0807030180240903100640700c49080741c0c041e059083d46298000c00008190001034400c011003802411004490308500c600b2072081002401c0310100794040d504050300704030403a540490070800b80c0354032641441c0c0325241c50000c60184011169901002e200350740001c5441d407843c0040c0c0c900c2c01e64107034051107400c0d00d44603010f4544209803001401da91080c0040340603824420b0801e007006c22054078031030f66250b035041b151080d40c1030340c584007026035034070700a21a01d41460741c2c850802010070707034032924081d00a40c0c0040c009801442051000390b92014003040c603d00c2a01104d0003011000100b0f61200c802c502210344941c800c1c40121010700c07ea000c00500c0c8000400e105100761503580300e4090707111030f00a10980c075600041901302c0000c000c0c080400c2c81c1d87e5005030345940c142607a500050307942c100200c500403078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 194002392 1250 194001142 194001173
    0x60105090108030702060f0d050405010b1005070521090604030c030209150d0b041e08040f080f060403050c030d05040b150301020405030d1b0f0b070e0114071b030b0112 74
    0xe900030401805100800000c03210010350640720705681c3c10360120744000e940202c0c51804110f60030401032205200054024040a041c110b41a8100e000d660200303035017911401e2801456074001510040c501c00c10305618504044032001e5051030400781d50001610740c3e0154100b02d80d5001403c02c01d00541c1040c5000a03403028400c034428140420314000504040c114107001070100c0000000101040511408000300d03001c60801a80004c815103821000340c1c0060049600000c1e840d00c00044c1d5800c0091280701c50700f8480c0280401340c0f51034038121400c3c0e1100759010110310040240031050351061042c240b04602903882c00295040c4507214040c60200320702c85910907801440203001e2907801240b030101c0074045041c061100143c0d4600450615101c2c1d00150060342c048010030300384202c0c1c0c00765034480e80b66a40c828a254039030800640c0c40d4005454203444802c410300c0383c0c6001034400c4610600114030600c0a00c481556540c6264200200341c01100040c404030200504102a14a102244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 194003642 1250 194002392 194002399
    0x807110c010c080901031d0102070b0c16080d091506090c09030803131401050a02071e050c10030b0a0305010f0b04140a0c0903080d0603020108070e1e0a12110102060105 74
    0x1503181500000301920744182001c1e010600004011010380c0c0603520041e05001e840b050028401800f00c0003074001c2d0445401036a00340d444500144808060b4401c85590302c006903000c2180500e591a0b1441a0300860034500046543c0e004120104055554000c4464002c000104189047c4030071542620740d00c0c220786050004100b0240006400c42c8196540860008442010010a410124000701c0c219601407443d520704004d00c5040c051a40017030011b20701030201080082c0c02003e03407203401520640090003a030022076410340640f905086203100315150f4a00483d9401684000800100303080c0c0c01100d00c0c1c0e40d542d0400303900000b18045c80511440442e01000b0a42c01c4070580001c0e2240248604401c1c2e1b528464020039500510320b1b44051904502c9583d100e41203071400a00038045804142c1c00300d80baa4000440080c03050f0410110030001400507041003c1410900750400040e0041d9503000302e403220081100e00f400300e401a101401120040040c51040c03002900b4480c06030800c901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 194004892 1250 194003642 194003653
    0xb030f040f0602390c060f0d02040902040e250509060712020c0301060911030402060f0c0717070905040201020a030e041b03021902010605010504030807020406260c041a012607080711 80
    0x20348a0003244940055800741d909035990b0100030b0321f0302c0c0c842c42050240b0000e188003040100306080140d0151040d2000000780c1e00450b02c0d05c114951442c18502902840016003101e9821810301c590f0140c880c80c02d000c0c1219051103016900c10600711445428280168003075081e00e00180b509006081c000c6c0503000d0100b201102801c002da51500c8020700c0179000da000065941c20b40d0304610100c40d540311207a415903510325242d101c0c5425280400c404042980704d02100425502c200d441a1030040d80d05070003c28540c011a40c041d07400604000d50154010b0b5142d8070450881e0000e0b8860a10702c080da41c00503918400c0079031a80060704401100421a031608009108a0342c0200440707065036045820a92240c0040c8001030203072109800004000382010388810030000c1c22101d4550529159098038140100704003488200d03200458010490540018090841d50107440090000890b0710342e8400d00800798001600b08800c15038071240011091f20402c006941d000310303100307084020301d0040d10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 194006142 1250 194004892 194004997
    0x1002031515040f0e0702010f0216030c1506060c030206010f03021c060e010c0302040501020c030d0912020301060503010c080405060f04050a1101020f01060f090c08010b030f040f0602 80
    0x940400340e10001401641040308075400e1407004400d4030020849000005981c40c0c541c00c02240c001000d50f4220007540c00c125a040290005009581d60010117031902a00d6208a407000c50307007031400040903a00008400c4040c02442071500565010f460940c5410030044040c0c46c0081c601201603105040c6062860300a0005903a1486a88024080d0420250b80d10950313040500041c1800b2413803008035848c10000302e032900e07010703000b61084070400d809555034070940c501819120409000c1c00000035001c0c3d034050000341e5000d4560402c1c180041c0002560311345800219084407007260b40407000ca44010100410404100141940a5010b03a601c0305182402ea0391030b80d850310269001400500402c0c0100c00c20f034400c012100a8184d860000c0c00700c1030341c0b00030f4420803a00ca402100a8141005035448240380200300d024102c62150910a14683e50446500c103456405482141d0b42c441e503001d02c9002c41c2a90000d00000606400880360102e980c010501c200ea0444010082c0054058881ea = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 194007392 1250 194006142 194006161
    0x4020304121103040906080a020111011b03180206030f040209071b060f0902100f080c18100521010801050a0b0306040b0601090909081e04080316020f06040303020609100203 76
    0xd190000c15420060240c01102c1d00540c118040c940142d03014600e06000006c401c100041ca8090b02030003070700c8036004250514441805d0b1490902006600b94541c080d11713840c940719500103c07030308048072a034505040c2168000340b055481038902107603400700802444194900340780c00d20b0300700302e45003045990b4a10050550040002502025124990361103d0794402c0c4443e80103a40c20b2580200416100469140040c1c40c5248000030700001881c0c50340044e4440101070704459506111410640d00f02c15800200503040d000ca07400801080300601c10702c202c46002450400388031030a011001003960601ca401401c5a2004006004060030079054061503200400c106810582240311504140e0390540103070350a15956008550441c40d158000080c018107101170101030440915051255000e80c1907142580101d02035924540c0003044124455203007150001e841074070182168481e01d8441000400a800c41d070b00035800f50f0010020004074600600c0207000d1100d40c040d045040d402d10210380c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 194008642 1250 194007392 194007413
    0x23150a020a080c0a0c0303020619060503100f021e121303050403020d0204060803031801150305060f090a0503040b0a030f060308030126240903030f060f0111010f0c0e04020304 77
    0x280402c2e60004120112007414003000c11001e4008080c90344150745c03407400a541c0e88044407038290800c4046c01102e1103011a000752000c84500500508500d4001c2100900501c0500e050b409940d90800c5001c044010344810740e601c13039404411709a11100400c880521542004080e032024071404100c070030010340c0010503502501d805656010b4000401d1010500a204a80010910b0701c0b0200c1001100b40c000b41c24140c9024000b0002d004040d01c142c94238002d0304190100600c0b40c0c02100005441a0078916002e521a4500044605a42c440d0721018215805500061080c9000155946050b60940501c9808845581040000034599111340e91680418050858841c4100c52007904401016145c8004607003a402641c03080e80d200714520328010a01020006801086000640f80703150100c1034900c00c111052800c042a43c4030b204000402406001c042e040c04120400c15038440c01c2407068045d1400a600c00160304400c000010380403410a00d02070344078074010010840000c00c15102c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 194009892 1250 194008642 194008663
    0x606090a0209010302130e160206040f0b0603120a1d060c1c021f0504060606080f040308040f060c0806040e07060e10050702030a110108070504081c020723150a02 71
    0xc01a101c42d44100100c0180c442d200032901140102c40003c40c2c001c0f8000040da0055104018241220702a104180d89072401254043d1807802c50003006030203d0840390072150300c418001c099915201c00c02a203441107812081440740001c00d00b0101c06c41000d03824143c14818281120340d5400c060710000c2c40c07559404000b00e41b0700250301102d8003001c514000c0140044060050718490030b440040c0e603000c00108400c40f402c0e0340755414a44005103045c025070100b0300444d01d8918044103030391552002c0c2d031590340142c0f00301c1c3d0010450b032030400410700c00c2c41000300260442c0e0b5071405e207081c44400c01050744c1e44085031220980200104000c644c0d00045040100c4400b542c0d6109091700081e401d0710903001c2c21102139003500074000c030041000154100030300009004d03210501640c03504c0300b04503150f0113103014a14075680a1005c0c0030429081000c0a1007840c070520480300c149484036071802c225000b0b145000d1400d981c509008a643c5804a45c42030180c030b0204440d4101000f24a009658610350070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 194011142 1250 194009892 194009911
    0x50405040519080c070602010b0a060c03050d111e132103200f030706060e0f06010c11060a1808010903050415020f030f030a0b03010603020307150c1b0314060609 71
    0x8200c2420071030040f050380c4035243e04500307072051599242c3c4042d01030311000c1c851134441c80e0900e00100b4800c0c040c0c00b0351240e207501070361594140046442034070010b10140c1100c28100e40180b000e02d03030b80705d50603400031092201c070242c041d22612011007401c2c50800f503401c00200400441c084883c041c0b41031807100649a010314201e40c00254080e42c04000340d030503e0340c00b0054000d144441650110000092526500c9004108280c46d600c010481f4007150640c1c40040c0b5265044c042a100c0d849050100290b90207400c040c080c24082e071000641c0f0f64440b60240000c0341c80810051a095445501e82000b00140c50003800110100c2c1c0d030003480e500ca0741c0203032000c2d401101004200c0d541700b00140f1081c6200356044960f81c414070040d190042c4c00487d00800003a0620507020340c103003810302503c0101e0354060300400c6450f08041138042003000b40030740d20040240000c04070300802c5040d111581840c8040a94862550171800c3c40100603c64145a050981c00f4500340703d900d882d4140e00d190301c402c2c0356 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 194012392 1250 194011142 194011183
    0x18190902180403032f0906071109090c04060603020906070201030e03040b2101080109050c130b040603060218010912020628030506010f0c0f0b090c0a030503090a0504050405 76
    0x61001400100c0c5001c803200d0500d003041c0c2040308041d0940d000c28038184070b841e20704280802c00658800d40c03d018610140c03140718203005558035418200040c00300c1c1441882c807603880c080b1007000700c1c1c1008000c0351469039560100300324807401c1c207051003100c0280555150551404546201250f264810554002d042540da44800700001c181801610050111040299541d0103010454044000010403d2040200360400040d542005108000801c0d034000045c1041410340e004006020360075012030082c030358a90030825003a603518400c03003001c3c42c8070315001600c8200700700388021170103540040300d0705100da140b400b44900300340712403080c4005c0d070b04403800c40d034640d64100b006000d80e0300600c100400750010f5880702805905a08001e21481c020b1781c0c0c010042158220031a500031024501030445241e521000010401c40203c407a444140303403085a407a2581034004c00e001d011198400e56807900042034a024501d014820f000c01413100b00c9043c045401d244d1102500c0308040d00c0a042c031031945 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 194013642 1250 194012392 194012411
    0x10509070c2102010605010f0804030e0102191406010509130b06060f0a0e01120507090b03090c030d120e1b090a0912090602010609020a05220305010c030204051819 72
    0x2070100010712a5000076074481c4902e003158992a400860100c1002550800354089419485100c07250318496080d503510055072916241681d075440242e61940c114002e6100b01720230b200f40b550780800094440e4081d1094000001e0949041c100c06030402c501c0340380c0150a01c4050482021525911074002c2d0524045480701c6000030308600c1380d0560420400004608a102c0e144c11a80d21340d40741c01c0a0300c4070080300340000c1d040800c80d9000c0300c10344041110043c0134010429031101840e4413402000032150000d415000180c580301c5403000340300010760303c4082d409083e01140501910101d04100401c3e4048a00040184443c044102140160f05560001da0324601d25008040e0003a0043c1841000d032501d0b1100425030105801400c01541c204500062640407610071600da0b034046a40725410500c0204a0410b40581030004000c003007140400440400c3c420310960f4202400d640f0016aa1880c1400740507100b181031803081520940700782082841107401e801c0c01072102c041040051000c0e030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 194014892 1250 194013642 194013647
    0x1c050403020d08220f021032040e0f10060215130f060c0203031b270d0c120204060e0402010207061b050709050a14090712060608030304050a030f1701050907 69
    0x40108440098070b0344403598424801c01043d1145c40c0e41c002e441700f00700422050025a0015140060b010101e002c8a4403915183c0c03120480000c41c2814410040c03070141d0761045809000c605542d20400c0342032603028050b400310101141d00050200380050036000c20071480c4100d110340b00030820102c0c504003082c400100924404c00206969204070100595003203440020740e40c1d081141d4003600720610b51410003502d544c048c26240c00658a80c8ac07021002c0c0e030b560b0701180301104111419044100740c281080001c03540c0401402410040f40e20082e000b0403401000300b51981c179800302c009034013180203010242c0d901003102002d540c4141400d001d918031441c214050700c8104103000c0c1c200c1c042e4003408074915144c0d400250190b41d1464052020200c0d550081c13440700000d80d245902a030040d1410000d014103840c1906440d4000c440018030503645900700350071540203c400301c2c3c55800c0700c0b0150003096007111803191000b4070ba02d40061084004e1640c0203440c601230140703500ca01d10160004001d0b51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 194016142 1250 194014892 194014921
    0x902030703060302030316031407110d021908150604060b030f3111030115030605070207030c08031902010501060509220221150112090201030e121c050403020d08 71
    0x44d8040c0c212550348101081d940c40c0346204070011000546aa11080c2e0500c0801060303407101a00042081005140300082102403034204030100d0b002158100740d0208507051141d00c0c03004000030000b406d41daa101032501001d00000070b086031301c00e600e8203105002103031005094aa00040b03040c0d400300a6100d0f145100c101100d444149500e102a40e220500a13640c61082c0da00c4181c4142c0300815003001c940d0406098940041201d460084020380400c041451600810703049141401901c40c030545175240d07800c5001d4240c1025030660320001d407500e49058421683c20203000144020000c95040c280c001744144a120101e81c854110315080310b1900540400c0c00347c0703404404504558400d046480180c08001c2c0e85164080403101000103044030b19078211400342040140e44903541045120015002860035080a0781050b649002501d4400010050301c0e43d040d00c031094490302c3d0314040c2029000200e600c40405402c40c01c0030280700009800143c40c40501da201c1c1000030150751842008410075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 194017392 1250 194016142 194016149
    0x512090c060f0409050105061602060a121805060601030606091202011107061e08071b050c030105070e040c0e060f030c0f0304060b010314072c03060a020405010201060e070801090203070306 83
    0x8800042d4000031a50703010001c10440c2e0441e6001d0000c0d80c1d9803070400c5010300034400740c190f80c503107060791840040c40c241004108440daa420043c090b01e01481a0604540e281c00c3c1114442030b01c9071030441408801c10010358410350901c1c0c144120f03410854000c090900a00c40c1c002c41c7c00890341a181103a000da90401c1340c807071141040303807020713582c40000902c19403a050548000260501a0800803485400414810340711502d91100d100042c2c283e02c0c40c040c20030802541e0178040c51029054540d001e024850144a00b0340d2041030b001c85d070300e04202c11201d030042400c041c0001450313641c40f6511100180d652120200f0040d50b03c3c1c1d03135100c2100890313201c2c0c0707050002510300c000300300000c0182c9640508040b60b03080ea407c0014180b2011044000042075a00d8004203814408001440a00c841c019590002d410003240011480c00082803601d48140c4140014035000700741400380c0e582c2481450001d0180080706016030508141c05800907906001703e9a441c0d400000040507103010b03400c02e2004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 194018642 1250 194017392 194017399
    0x20d120c05060a05060a0608160c020109030209151302040608061302040f0b0705010f1a1201060b041409060a05100f030902060708030708070518060c0a1410110a0512090c 75
    0x32450003c0301940100800c882030380c8524440103000c11224881e00c506445140c00e0400c0c031000c17180c10074058611b0400004100d0410688400100c0141c969849190182e01c5604500035180509010000d00c1c46e000703030ba00c0e05c10b03602c14082084003d0f0f11050700d5811507005e83e450105148192000c002034840c1d07411030307074103400c20460010309500b0007070007004502c1c0294020071400510080d04000c0d0740d41c400d2182d10790452500714140a1600810031904240d0080001444071798810402846130003a600020070f046030781207040d00030300300300501036844942100e42c9000941004001003601c0d070241c80c00e0341007000c0511002481402903100f10701458000700050f0701c41c0b4440c174042025501c115000c800080c2002c0100d00b14501600031b4400420048006114003140c21080c08183c0e000383c00007080718413a100f80c441c0401d0025408039110066a4054146242000c104105031074007025081c441d044204081c2501c40ea00c078003a00c3d800401c05601040c182c540d003045c0e901d048035080c0310561 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 194019892 1250 194018642 194018653
    0x608032706071403030405100204140120071202030708011b050f0409050109020304030e0301090506073204060f0e1807120c030501060908070503070306050705210103110607020d120c05 81
    0x550103c00409076120b54420760881d00308a055007000426070055200c0c0107003598004806094540c0111103502ba20611a03001039000741209000500d05681c992100107031414030140c14055003420b01072000501280ca00910281c100d50848811101c0006410f0040200100d05002d1550084d000c880042501c0e800c24016541c603200500000c0d401a1001c40c00b0401001083e001401e06009100010350008068090f0b6656590191210300c0c0748050303000060806900040001004c25143d000901008141a01c0b40d0500034043d00c00300030014200e0600000984a101e5503032482908807803003462801c090110b880c0c0f058107890721b645000b0004081824500d00b05401941540321504803080b0f0755800031803035030300e0300002c0e02d4075281d00440340c158100b039106001062180c1c101d07035049986403a12a150020b010440d4a40940302a032406e4691001c100403c1481040c080d00110381008445039481c01800d940010030f22040304200074001c7c00c4880807009101c1c0111805001e09070400c4c02d44a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 194021142 1250 194019892 194019923
    0x30301090b1201050c030a0605030c0a090b060705011e110c060c07211206050114030f04050c0901080f06062d0402130b0306040606020a05030a030908041d0a060803270607 75
    0x401da0422a0b0507070359940340c04800a4113290002f0300c8140610081c0c800750780142460301b81c4003c1e0003000f0304103401c80c10401000000850034455550800c0c0010204100c4151160540050340c0c1d0514120354855000e03c18401c1019010a03515040242c1600e042e58400035882c05000e08c0103142c58405400300850111000150418004940c840800d0010071840717484500648a055a07541400c10b0a1002c1c4001a03668101d46142c54105000ea002c171450380c000140001e80044003600240190f030002c0c000100b40c0c4070100700302a08405c080350201d84052008140b4581741c0c0080502500d200400c0101d80c04035101c950444010284d2811500300250b01c8a490014552064484601a915042e000079030303070b440491507150155002001d50f1a094807080300701c0181010002c01c0e1001a0100000541c00038941010b01854103620305100103842c00701802000c84107242c2c401e035829001000640002c03084c900ca59070041100107951091030b031a440100d4000d01900324010070410100200700b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 194022392 1250 194021142 194021161
    0x308030a050a060b0310140a0909080c100603080703050d0f020a020c0306060409170d020d0216061404020a06180b040816060504051c05010e0a060c09050a0305030301090b120105 78
    0x4610509020a05103c020343d2890b070030240e0b05c02101c821881d050650810300480250300d004040700703d002418403100a0b10b030100030040300c08402084a955000250203481072100f448a6101090781f5942004030341c0c0b40d91542405481604001420058002442000c410280d4881040170b0300c018011529601d0740c45001e540c80103040d408511910900300011810b04c0c4c94007420713603c250320040148602541054155a54100c076014100e41c54090124886116042c4040c001d2054013014000018005051002c115801c0c9094491041070304030820002d03885000c5200d003100c2a500d000d84000700200c81c62204807001e41c0000d070302440b001800040361000000c0c404000c0c0e0030b98a0b52003189968002c10381b12480b4622800c1d80000804010071074100131510751104940c001c000201c2c00344011107040f8200582220116851a0368041c545440e42c1d0014202010300002e40b464030b10030f4116228159240070500c2000d00c242d840d070400c070000741c03210440e10580440c0b442c000d1100c2c0c102003051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 194023642 1250 194022392 194022401
    0x50702130c0203030a1413030509061908040b0606120411210106060906050301031127040c1802070213180b07020304060201050c070f0b0a021308012c061801060308030a 74
    0xf00b040342468604c0e0091160f421b105401800080001c40d0002103c0e0703130603596030300070180e156404002800114070404106845014040180c1c2d103006140c502841e003216890300c080d241c6030244200f8420350f4a0081d4a1502e6900641c02000c00441c1c81d00c00c80000305012100600752501882c03860002031102c005400c0b00041d0303107850f106e9000154588100722081d0109110150000364021800790403810310f1307000442408010000386840143c10000c2c1052600c0945080b035848010340020005a929100310440c400d030610400d610b0b205884c0c002442c0804c200144001b240d940380b07550305107242c140c1c04150449900100901c881c0c0342512000e500da402c54030459026500b8040080e40e0300765030508a071076a540c08400542040065207880244802c01002c43c1c810383c0d0700b042803207254052611000001c1020314000b041a807420403000000a8901d98040c820400c880070410101c880480c1745903000924031384800003040070b06200c07030140c0141e41c0060305081d000400d010041195400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 194024892 1250 194023642 194023651
    0x1e030c03250e0403081303030605091305010b01021204031b1a04060e1507030f11070b0a0311030c030c180a09060602150403050f090607021503100b09010906050702130c020303 77
    0x122224036540d1607002c0c40194003254000c001900c20340002c0c116000c10681904000e0080c980010f2940d200c00c0030071300407002a07490f241c0030700c0001c06000803c0401d0103082c030341c05028800b5000c3c0c0688440c107100280100e002c000d000b1b2800d02c5c1040018031510013200018451850088240f48454840309200d5206004c1d980011341c50100844c01410a0b40d21040307140c61019607903141c064030703031402c0742c000342e00a40c00270400a102e0044c20007440b0800c98100542880011b580d034075144004045c0860714001d40f00f0b51016801e00070484140c0083c0243c07a84072017149800ca507210250300846240380241d0031200c2d80000204130115031200c040d4060000e955150302102ca07020030b0440100a003680c101d50050020744200030002c0d4603e07250015081412014208505180c126800600c0800c0c80c01c440115003800032081241c0724081c050200020b00011301414500461070000810200c2540642c1c0c06018000449404544803c0c0450444100c80d503000c000c240d61919000f51a85c3c420f0302c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 194026142 1250 194024892 194024953
    0xb0702010c050f0906072013110a0305090c0d060501290d2007050d0801080f1b01090f0902131d0c130306151401051213060e030a0c1703061e030c03 65
    0x700783c0e1a41d823079803090318500807511121504014105034106c0103000000c1c80442075000720031070b1313100c0c50722040200c0800c944104408143d0f9810a440000b40107441e01d00d201941075410500c1c0e647e1115101155000c040001000c5014520200000580700e00141c2003000b646001800c1002e001012072291009440c1c0d981d00d40c9140d0360703402050b9803480340782c1040140703400c2607130002c030100100a4030f1445d0490606048110ba80d40341d03011021405990720400c80c150300050b4a074034841404441c8000340801c42c10520702c456400803075207245000240b2800e41e5083c00604015040301000300c0e40d0041d80e010701d040c071003c1403052101006680d00e100305480c0c0400d400b040780c55580500140e071a80283c00d0280203250b85c4241c0003040e440c42441065400541c0d0b000e82010106c03051009088003a00c60712020498403040c41c0003582d9215010648940c24010300038824165200f0640001420b6000d92000d145017001c40000d05007400054110350600c110044d01188102c20100240e2948119 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 194027392 1250 194026142 194026159
    0x1b091f090f021e070c050a18051513020408011b1706010513060309020a05040216081e040303021b0303120601050304110a090902010e040501060c0305030901020919030b0702010c050f09060720 84
    0x580c1880b203443c949008c1c0c0c40314030040e00450030403914150b0159501001c01c681c00e40c615a029000304030f00143c0e0206202c0c805800050501410100340590000c049100510200c0801c011000422002404a04500c45802d81c0c003c079105038070a0044d10480e414036445410030940c1d1348400340081002040403402546010800180c40c5041d00c250b0b81c080d05000301c0040c10030710550745c0000b035a0240c1441c1c1000d071011b40d400c1180300c0a81c070142007d144260000d1403031b035410326164401c08089240c0d0074030a80c001c01c035000000e21105d00c01c90b08003e003824202e441f034a4034500409401140307440c4a03006082c0c80300009800045c2e4210300e40c10f41c000e88501d84400406c2060109460090260b84045a008950400020b01c108021070b8009510b00c00107003070641c0080001e2180c0031481c8000d0703455074074141c28018450040240c0340c1101450008002e0802c1240700549640581c48240072807140c0407509604680f503000c101c0d8449039002c00440000000d001c840c02070081003426050241588 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 194028642 1250 194027392 194027399
    0xc190305151e040510150e090102090909121e09090a0c0e060705070e06060c06090703060c020f0c0609060f0309030d0605030708150a020403051b091f090f021e070c 72
    0x81981c80b6004030382003000350007907111140c030003030240005940d4000c04981c00340300004c1501c1d0a00c007160040d25108009a0ba405896081150000001d0801079040e000444c40c8458281842e0450f000b1000321142c40b0144520488004110700409601c01c0d08980d80108000041020f94440188560103490f2030340080502c1081c00014001c03603034010199803002e4006e0126400030b03006d07143d010500506080c80c6c140300600d02401c01d001522241001e900c03000d418030030040742e4000c0344e0350b00344a4401001e08003040031a4907030b500d00700c9845034040c20001505116035251903044407000324102402603500d0409001320359403648071044800e0045d1815401140c1840c000c0380c50411116000c00404814506d041085c4c003005001d090805055400c000010018a0a11000990000300320ba200f844001981c01e002e50307980e008150203020004049104503a003600000c400a640c8010030000f1240c1c02e000594009101d0382c40c01e5900c20f2240004d000b100041000140042c40c80b4107a0440b5083c1d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 194029892 1250 194028642 194028691
    0x1206030105071b1506030507031b060c020d0f03030f020403050c0a0617070302030601091701020307120606020a0f15060305100c0503010b0d0f06030c0906050a0b030103050c19030515 80
    0x1400802c51140480403c02e590200d60b4040103420b0141a24400150a660303a5840c01d02e030079100e50080b18182e2060b038008801500c03031801d0200030040b50500f03082000d0181d000404907003820728000c000342c000455410034184203500c030100c0d04080c240b003117642d603880c2d0901c5a980c80c4040740e103902c601c441c0c09022a9031071180b44088001c6050031700306e143d540c0b28050b007039010303420040c1110b0420001230f10008406400c90301c038001103200c6500040c0c0c1c034240140000e08009140ca040c04c1c1d06820600c082015079400903100041d01e4000d101c101d00e0304990300d440500144402240050700741842c43c080103018001c12508400c0c4950502080412a80301c0144c4085c0401d200c0c01c100b0900600c40c2c000351442c0c5400a90701c00c820400c0008030f07551207544103684080c103500080d488a90b10b90043c40282002c515031400b6141c6070550358159855541c0e00c03540c508800001f54007807000000910b0020440494250182d07510100b9140c40a012110500b9406012140c141c20480b804080c8071400c80c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 194031142 1250 194029892 194029907
    0x60305010e010e03070215070606062d050f181003060602060f010f03020906010201020705070f060207080129060f19030609090f12050d06090e0f030a050403150908120603010507 78
    0x90500f0055400c0000917020845203200c5690b00c1e00e6005020880840061170f21f101d500701406181c2c03580d886105240018240d00d0344112143c031801014243c0c0d14410b20741107000e40c5c10000d0a4003200340e80300400c0b650808004814003c49400810075400c0003d03680e090b4000000381c4825070f0031078855548d68400ba40061200303104190242903401d5082c000b5081c504e10840d4401010300025180c1803043c0d42c1c0d50324240d01c9a0202903001c1020ba01406070523410301c41500281403280081c0186400d1060f01c480140046800040311040b51080307003113546644c001d40300020300280c1028ac561082481d20422074100c5c3d404000000d2600c1000b080504e0f952088184154102030710901103000c03070b07031071600e440340e4001c0700c401b480707818407062003a40d0541c01082e0150800c4400816905500c0c0303211032038101001c2034292150003d10032501c00c0fa520000761401c90b40c1000c00041c822030386a0600b0000d00060300e0240442800040003021507210f520000d0280b1402c4d8020400c995800c0d404960740c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 194032392 1250 194031142 194031161
    0xa0e0d291603090614040b01030c2304320703050f0411040b01091a130602010209031906090b040303090b010e060d060b0307120c0315060b040303120b0a09060305010e01 74
    0x3900d0394104215590311a5104501052040c2e00000d03417080c04203901107504100b01c8048412503207140043c0b08000c5000e80c3c0c54020f155400344541210b58000e5412007076011300900b903004550740c0080d001c600c0901c0d0820a8602c036040303042696020035400042d0452803c8a07903c000c203040c003010505030a8849201485a600b0006a9400e0120f034030030400645482240e00303040115062021890600040021611030320800e0259541d144440341a0b0304140540c1c4040196441446071003220f44000c142c070324285801c9190702d4400710b900e01e000401055503101c09400c00522104010405425503c83c01300c941c00342d1846100d07681e80c2c000b03100c0e00000880b041d9802403413900524000581a1300b0401070500f00805a1b000b4540390b15901410200000040d240d2043c282020802d111549502e28001c070b031001d90512295081965441241c40349100040800c0114800e84000350380e10f50041d01d180000420080c030307050b61800c001000d070465000507103580d445c000d0300180b003c405105151a9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 194033642 1250 194032392 194032411
    0x4030f0305030a1b120b0a0f060e01110c01080601120f3206031b030a06020a0804021f170a180305090a08070e04080a11060406050a0e19080a0e0d29 65
    0x17003c0548070390707034043e100c3c4070009900401c80303030310115030f20400c03a00101c050242035a83c96680701c5071700d000401450b1000d840c200d064100b44008001a42c0c400080e640c014400c1c20244070300d1600e5541e260040100c4000e0f190014a041440e002803803c072885090750f0b280d171a980f030071640c603a410941d04c4404140d910030744c95800030700c01010a0040c05000d011400b8010155109103c450320350005a920507504c1c45c0000344100204011883c00e138942ca020080d000740922810403147c1c3c0050180078118403071245c0247d822000801c1203600d6040036403500a081c0752400110700340d14011706241c0010712803602c81c00e8202c001003400000050040104d402842c03281045441e162200c40c0903034010900a810020b169004403048802049081e001d0b61049100240c2e615028401c00c041300e0f44181d00181c190849003043e0b0500385020000240035811401480da0b88155400c00d903424941e0003500c45d04a00c1c222044020b000e48130a61443d0790420280e0032125192210015114043c21280140c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 194034892 1250 194033642 194033657
    0x105100f0602240703150806071407050a06020f19080906090f120a140310090c17180c0d030c110901051509030106030204060305060405010c0203030c040608090304030f0305030a1b 79
    0xd200e12500d8080384c00240a00f000a59440683c1201d40084d15640042d401791780444140451140e0007045080b0514200c100d25040c074840e41e42e4152140c1d20900c0140c4000e4000c54105038071210b010496900281c5510034003c54103005da40680304000c00c07603408445004400003c0c941d8180451510901c07002000030701004060360840001640180034950704005d41800700d45180c0b01401c004500405040c200e00040c90700e070684640075103240d00303142420410141c80d80c0c02d440e1140741000390050032200101c50000409034505242000110000c0c0e07108000300405010b00d60040303100c41000b800340c10b40d09444050f020071b10030030f0202840754582010500071044441008a40030b400d0440c0001d0003c0341c21035030303500000c058a0050304140c2d619013180b024001009024400c42000301e40707034009541145401500c4071454015489807609008801001900c111020f104a80180d9400540304602000d1428010b00c10b0b00104c4d19881298940004180381d48030100c3c1111803100190744060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 194036142 1250 194034892 194034943
    0x20c07031502071406011701060506040506031302030601150219080f03181b0f09101404020f0a0201060f060e032802210d0c050304030b180105100f0602 67
    0x514600460551a0354035400c3c4114000544c450584002c2407051000800c102d50510070500001804207020303800710f80c5024030070001612854103640c02c0300c1c02111103079183c2d502c010308002805c0200100a5142c010040082000e65080c1020202500075900301c03413038492101000c9080a51021307024001c007809024441d0f003c800e06004561006035903851540f00b81041003401e2424000074822142140a481c1482081c140094006920001241d180f6514109031600c0c06503130300c00b80501400c010390006404140c2d00d60390125000d90501080456132000182d20003402000030b4040d800310014503038000541c00e44280b12210340c0c072034001c1c0904005407007800034a00448000707401503007007400c0001010140e91074803040c610a003d0150410140b0500c0c03402c0340c0c2400b03040303500c5200b40550303084040046000003040e18192a03004880400c00c1d00c1d2085141c20790340c00604600155800e020403c09110382d5200b041c4111112007111a000580701c150036611100742c9201880180b04e41c11900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 194037392 1250 194036142 194036153
    0x14090a0f030207031b15030209010909150e1005090702120f28020607020c01020f0705090601021603110a0506030f1b041a030609090f0a0f020f040603030c030f03020c0703 75
    0x1042051080c01110310503560703585c4001c680e40204404120000c4206400c01001c1411000c074165040d5500c0c04514089203e80040d01102d154019145211b0307907248042003540042c00504050081e0b188010301903e0024400403d100c014014140144492004510842e00000b048000e0301d1706c400d900d50420b0441c0c0017a071503907008240350091400025240324002000203e00589000c255130103040f042c44c1c850740c06440c4c40401e20f186411984160540060902e0220300142992812140c1030f42c0b680720900103c0ca04520080d0408024441d0003000040201000d1140c000c6c0f4000c1d60a40c3d5410740e604200405400100c840303100f644402e0307000880e402090741c402d00190300039042e1181001d0300ca50070b0703904904c03013165030b1100c0300d0340002403140074600800481c1e07002019600505079013613401c0b10540c45040328074000308600351244c03801c0c3c1150354a0444104421024008000965483c20f00408036005000258049000682d003107006910900895002201d1003000706006480c6981d074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 194038642 1250 194037392 194037413
    0x604021002010501050a120f170a0206160203072009100609080a030507110409060221011a04150207150305040605150319050309060703090e090a111309020301110d14090a 75
    0x440d2844200d054810002d45100c0440d843d2706202c140203a102c40000801034034100d40640240041a002e07100f00000503400411a4078031030f402085010350958004594104a4081ca0990741c408290010440704203460b60341c2e001110065541c501c20b02d40c4d01c00c91107407180c2d0121170150006004004100110f03c400c1074011107400c01a0000074581c07420b4444c04201d030006d0503181101850148040d0612950b84030180c0034180d500082d0085000a4aa54205114511402c03000c0004140c0400c080c500a02c0004000c1c6248004000c5001c00584000c00030a8101e6044400c0c0e440c040100d0140001e00b19180c2102201400401c880742243d031080c840407142840c12642031108011204031030301d0319006454260b00c01d480302e0440c4d500388034032000700140040c5031306c03100d034401a80f80d804a001c80d20b0200802c4401d0710124013107150796008a003d800e590001940641c200540f03403000d502000024440226042001c00075400303400d6003c44512005d58180b0456807001c00400c003c0f071595900c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 194039892 1250 194038642 194038679
    0x1090209030604080a020f0109240b060d05251e051e0c031e040501170708060f0a0506031e06010c02010203040312030212070207090b060306180405120c0604021002010501050a 77
    0x46403150b501c07d007031140c00c0d40ea020200729009e0012060360642caa060060100503084aa0030511215150342c011070b0490051411b4542910380711408600d20303950bc0404420b58481007000d40c50700940c0c001014005a00210403c1d00c8003c0740d994003080b0034414000c1c0c03000b4802c100a420442190030300c407150385401600d2104600e010410080c3c40324040d0072020b1000700900680c0c0d0342ca8515000000d401466804603548940d81e07070740c040021550f071064800d43d01041c200e482c410314441510100740e802045810031604884000b042c055481054421b20304bc91b42c0134400c880d4169204001112643c0b540e1900901681c402d00c414000103060881014000c440c518005007460300011340d24124800036101140540c125400500c401c5115010710005400305445051541c1421408985030704800108602da8070703000408070303080007800d114800090001e0300c01291500440d032502c58994906072000c0340b080c1c0600d40003040c031a0040c000c15040f1003004007000443c901e03082039800c51018941 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 194041142 1250 194039892 194039897
    0x5060706050702190c0f080304030b0c300a0510061205090309040603030807091d010b0a210c0e030615010f030e0316020906090f01140d121701090209030604080a 71
    0x30f040c440040e00d000301134454502a111014002d072500301c010400d0b080350340007006260020071060020840c2400b002d0340000c6050900c0740d0329444816180c40302c00080c4001c0c400143c240c480043d00c044503546c914001c08020300100241c0d119000c1e036420521301751013002c01054081a030442e04c80c00c1680200d034401d50a400f9a0300d0031011400090854240360021408600701c101400308030b56200b1170b4440940074041c0c0980e50700d2510000c5201501052150340100340c0009043c03201e052058018800c0c1c02101c01c40462310321481ca0504000d80b114420220005103200004800e074500019018091254034055114070700400004540780c200020020050684501d00e1280021080005002400303406180290100c00b0344104100300e04003500300b0744155420b000f44441c44080100c01c0d8110f908214000c0448070f40c240105500020724640031f001104500404004c413600442c0056580122108a40b41a078039803112804901030340285a4143c2d0200b000540094060402409074405d01e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 194042392 1250 194041142 194041153
    0x10311040b150d050405101107080a03021e1b010b10080601020708100f0b01052701030902030106030b151e010f03060b0c160f050306061309140c0109050a05060706050702 75
    0x11080c2c0324075a445040f41d0800e26542c0da0420091000030300052031705010501c014000001c3c486184040d9014014028000240014020804034000c2c6e044030b841081c0c1110103581801c140b108407409410480048030200d25071014080361a00601c99001580d0700200308828910701d505c070840d04ea2200815044c194465034501054001003003107600300105011501159a00400c404502541c07454200305061240502a10200161107504802040d2200d80c4440c90031086c0001203024018046004e03405520f400c4011040c401290075107881506900d900c901400081010700080c0324810380b038507910030f024000c200d5080d0b1050381540035030900392402040058981c40305031015031044642c0d03951544401072110388000b8050000340240a100d152900d0b9510307000200e030b220b4400030045481000b510400000004066112140264101150103170b0744540d440003e80c0c40d20368001580c04180d130f081d4001054507180015509807003014026034241032482d070340c85000e00b401510100c20760041c2d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 194043642 1250 194042392 194042419
    0x50901090c0528030c14031501030b0d14060c040e010b0d0207060f1a01030e0c010c0f0807030903030306080703020f090a1d0304030c08030f07021309020402041715010311040b 77
    0xc1d80b94116400705550f4101d0a5102d81101c00b90443e04020740a038140b00c45200c030210001c0340d04003a070b94420001c117208444410200c00480040002410390f60344a10079a50300350600034078115103d84d000c000c0b02210442e41350f40080d003444c0e004030700c1504e1480300d101c8018040c410a89000d495407201c400000350404001390380395810b440c0b440c5010914140e0b581658100c13030840485c10303156250b003821b0400041b90098410b944030781a05800605220010101c10100407a60000d0002242c01025003030f240c0035107140c02010702c4007030b10060b8002401d06101284ca6840401c4000499034000c1180314032500706014843e20100084c0200545992101501240100304000d81c9080c0206009147c0d101e00b90b00d803500300803c0c540c220740f03d1a0310601800c808071440e54203e0b4020341d012102900c040d100340c921240a414003960080d0018000304d400560564a07809900308628140280d8050001549160a031150244000b429513140c001d151140d03403e2681c0901c00c000005003058078010b01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 194044892 1250 194043642 194043667
    0x110c070b160819170610030b01020c03011406130c02060103060b06070f0b06011403010e1524040302011b0314091302040803070b070c050705011404080609070305070b04050901090c05 80
    0x856124a0086480148400c3c01e055000100c000d941070102101d40040c24100080b82041c0040c0b086181459070300c48450100c0d0307008001450a81d00000c000303014a100e500b04450b0858016940d8038010981c1ca10410340003412800307806200e940d95401444260320f19190500078114a2014a80010080085601060394900060042806000c081e44a17050620004003200c001031400c2d0300001e002d000500c0025442102c1c140c00228012421844600c084001080ca8018609040865070343d14040780446440300b001e042128000d8035030a000c0e500c5580d041682968a1100900040100c000c00c4008180900a0640c03481c0180014064a22445035202260710580012200342c2c40810000d040000d010702c1d00d5440010703403400c4070503d030302599000c1e42c4000300e0150034188440304500440669140c810380c0c00501d1108126101418010000340d1070780014001030741e15018410010401c88818001c031411502c0150881d1402e80c80c1c11003e034014019114a0801c00104100c0710300041c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 194046142 1250 194044892 194044897
    0x50a1404030206270604050a181b03061a03010e060907050d0f02070b060f0a0b070206090a060f020d030e030d0207020f03060c0d14011802030a1409030d110c070b1608 73
    0x220030410f40c900713803900500c110300c00c5544c807005140b140307800700400c1c0800d4460050810840341d11090303081d4101c14080c0030b43c0261039208841d05544600a01c0300c07442c5580751300064120340000303001c03032a0413002c0132964605110034010800111843c001046641c141242800d50140c03452500074180000001c291091b51081042c2042c00c83e004a180418094011700b8150460002c071000c59903281c10b00081400b60065101d240c4c103003040820301c2010f5403600800c6070013a00000703280510050300c0b0000600303190300401100d0010b00c24500006600ca029101d10030155902000960504100144c20000b951010340d080b608034000c0d0606c0c41940c0c404014282c00344111010203500c400f003140103503080303600c4040c802030307540300081c01004000c0c00e80696116a030385940002d690303640e5802d00c400181c0108500c4104410400c0e04220340f0a6010000d44401003c01e20144030001000e280d0400d64000c16a100d161900680401c018449111000704011071501903071600400994a4401054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 194047392 1250 194046142 194046157
    0x10020a02010204050f0d020102070506070c0e04080415020d020c10031103070f110606090f0c0702030607030506040b0d1a070915180501030903080a020a020a06181103030a050a1404030206 82
    0x182e4021a05000300e2a005042004202050b2040804050b079900000d40d1444180309160195500013040028480007036200300241c82d0581b43d0030128141460f0058041d0700500c030302240f8a1404500140b0f20b4804100803800100c0ba9009010201c0000200320074a561406408241644c84151b04140340c9548003444c0b1692a03600d07440e48240c25414064510440c0c0c240b43c1c3c03501d4000108110003590f40646c52504081120300546855030f0b0f100c107250641c40b0300c18001c0d40c10700c03648007048075a980c1600100c1c8224425503045c000303150010144545c42507019401444560303217245c065200e40840e8003660303003c9498909031041d5a51030005034804804008284005038004040d51981030070b600d02a00100001e10302007100004540300103207400c20180c0203000c9140c00080c1400b40a10810040b5044c5412020400c030300701120903030610821f50307010304440000b00c4d00c0e02100385142c0031040c0c403644031003615050b1a00d5030080b000c980c41d1800361a1122105c80900c0f010015844007400740000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 194048642 1250 194047392 194047397
    0x21806030115030f02010818150408090310051f0302010504050d0303060f0303090e0f09060402040911100305011d0c030c131a0c16150e03280c080105130b06010210020a 74
    0x504d803603800010030480004200569083c05040d814445030000544c0481e028940d40005600d600c50340b9054003a0303c913400c422907140c4600000c140c40d400944c0c5c003040c0280f03d211055400d0124514801050103414070010340400c40501040105051146002d10940d00c2807800086041e12406141c80c1c4851f190000c1d07000075100d5200380107505003413942c1c0c0d070400c080500303500451401346c0049517110300c0140024003035501d6000510400000c01134140394a03500401c0203500307001101000b00208801d10601030054540c01003016440c03c10719100340684014200345186603200d0090b01000e502c00f503008100400c80d0200042d40d0003035401101980026161242e40e00c4403c000000c0c81d02041d000c0408106040c54000c1110007628280031144421504042c0740c10240c0c0d000107801e1400e20012600c219001000c0a03940424000810701c42c1e03441802e19404030781d1280540e501300d450032200f40c210325840300400c601240c110801d07079502880510468440c0d110510030361090740c100e881d504c8007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 194049892 1250 194048642 194048663
    0x1d0409050303090714040204050a060509030f0118200109121509140d03060b030105040c020f01020304030507050d03020901170a1d060714030624040f0311091302180603011503 77
    0xa84a84241106200303c4121b03015410b02d4100f10008250010520582d81800000591817040d41c80900518643c24600c10080002c81c0c4094a2004461040e040881c1d1300309039150302e24854040807801028208040c1d4980704a2800e060074030351506c40211065840580c1d1400301034240b000340c0600c0f0f40c0340c0e21a0b40303010021200782094507d0a0005071001080c582003600c01c0c08003100500503a4111001240d01041c01401ca01c0e00f03900b071020080d0f5880a6500010411003030540010040c02802e1080d03007201c0001d10840d00c100c0072802040300c054001444201c0c1c928070b41d110601c15541050403950002044440303000a54610b200b51031444545402413010041d080e0f820503501c1072030000d03290110345146840310000c0c031040c440b80801c04031548400c81580d403014105059801602644000d400903d0322410807101c00b507000b8100612500070900010070030b00302506490500d41d409000c202c018441a0400800f620004000940541d82d54907042003410000301c031000110f004241810 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 194051142 1250 194049892 194049899
    0x2040308070c080105090604030e060c060405030415050310030204020a0e060307080a0c03092301090203030a0c0605130807020f06091e03010c17070f02100e030c0c030d1d04090503030907 82
    0x74050882ca900007441c036458032042100712000816100e80c0f1503410728190480445110005099008aa0f6031100d80e1040c2400c0108000000009000b03991411146022602c0e41000403101417104450084c03051070000da0400050406402030694010503003400032610948401040250300100c0f04400000c02c40001d00103054441d04c01c80c0c8a81c62580b8003404855260784560220300c5500036440c0103840c0403a49a42c01da40298003500f0302e6540103041d29501e4004520041001c000303040e0603501c0034502000300c2c0c19000ca80c0ba11107081030f4080c00c03982c20f02171541c08004152116603200c60b0084000c101610150f510881d1000e03950703400c81030980d01e11010300c003031608454061010030284005040c2c26031568060446c1b99500041e1032400f14941c0744141e070124208048445411426414001c001809200101c080d044042c50007040780e0340307101c0381c2c42010b81d00c00c0300c5202500400c078507420035028540c03000c02013510a07602030800308a106031680c95528540c01152141d00c0c2d0f40046d030050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 194052392 1250 194051142 194051153
    0x40f1e060605151608090904030203030901240302010c1b09091e0305071403090607060b01030b0118140a03170c060c21090a020d0308061014030606031003060204030807 74
    0x9502400c0c0980303410410aa0300078461103e032003104d1484000e012922107110070042c02008171245031101410101c40c030300300b030328001c0d540360010f03030300701c2d8503542000812940c0d541003551004007080d008401d42c4000d85103400640300c02d2038521040d64032800c00d44c15410710b0403d80e6130400c000d080e0002e00040c041c1c001c0c02c004c0b4009103400500080501d0411400d00480c1d031260a480c0d605402c0080303008078041e070660030392a600c55045596000800818031a00b031042036400a100e8090a0b20140700410b1040011510303803400e284211043c004030002400411900b01c4910f80c031070005085401c80300e449488040c81102620020452005d00003250700d0b022400744145508404000381e1182840c04600491058203103008500d075200c2030b410001800e0f40820012841c0058000c2e01c209070020361400d00400100048402c213000d0200e40c80c50b851114401e034070680c2030070607040885055484800c200185030b0b1020740b03402c8034566510804001b150042c80203100071740c450032000303079540c1c010311f000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 194053642 1250 194052392 194052401
    0x702120d031409030d0b01021f150b030613020a1112040906060516020f04020d18140a0528141506010504060c0314041e0302120102071703040f1e06 65
    0x8002c0c2d07200b1800188000e08000000b40d5040c0948090b02089840b00c1c440101e14200080d2050086800d902e044010707811495070041003040910112142c11644450303c0e80b0181c80256001a001402840703032010407030340c0d0b074050035001c40306e0301e0a1b000d08504c00001e80e241c04041026034501190000c0c0c10080014644a03010092443e0704103142440b51f030007040704100719003520280c00b8118140d40d203d00ba56503581203c040d5080b944080111440c010710b21000c000c034641007202c8807221008486038900c1c000800d41ca040354040010181e400110304034003207141070075040302d206082442c55100081c15040c4414120643d0100500b140d2480c4501000c40c1d180161103036051150801092050b0740d030056a8802c4c8540600300b807801940310103111066803140c0d502405140d0012102c103260200403080c0c06003240d00071031301f500e82000141040c034202d2181060041030038004052412000b152030340a15406405404c0c905103c0e0704644860311442e100213030201c180400d1420a0080106c03a03c01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 194054892 1250 194053642 194053661
    0x61b0e0907020d080a2007060b09071d060c010e030307180e01050d0605070210060b040504060e1302010c060b0303070605040209100311041d07080717160902030403050702120d03 78
    0x80c01010780803c0701501d0040d0140c2141e0f111038869070780788030011191000b13003001140d007500503a032440b00342004401411440e203c1481400940e01140c4001c0c440c038246140140016460b00d10811000304110241d8060101780006540307034442c4d44900c00341440614450086070b02c480408251011051442ca12107802503904d03940d80c030006010688681d03c0e010946544801c000940f070321a504140d10301006402129560360415501144080200010704112402607070f0503c01c540d259015146501000c0300d030200203102c0c80510801540c41011518901400341d1000a0050603032804030f8215400b607074050b1981c81c1c8450510003182000e201140e4881d08c2c640840008500319650540c2c2c0d4180f124282d0b00c65500d07811002400149580c03884c01081e00d2004840e65035503515855500c1e4181c030311404200f5404000c1529800a000c20061003090784040107024040c00c0044800094202a0055003003103414041240144c41e60255011640b0f1000024940040896030040c2138585542 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 194056142 1250 194054892 194054897
    0x12090501110d0608071a03070e0f0a0303120f09050a020904032d08250e060c060412030516050d331e0e0c070206120106030603030e010908100504061b0e0907 69
    0x94005000030101080d00e2300008035242c01e0110031100300010701c0710b0a407180707159404500428000f0406810030f588140715800206c040c061207250403882000c85003280b2018085810003555140107281103000107510610034105419036420701151034090b12a503082e030244645d01c1c0080407855503003205510f0340c407000b015081c105605136001c0c06000d11817020074540c2400041c00c038412247d51000283c805265180040300d034240761a007800000030300c01d440500301007450300000c90640a21a000d85554408036200e20b494800d0004d00a07000300801b80350000c80549540c0d030706a0f4807814040382c1a0002200c5000f000150412501d0083e0300e800700c0300c10000003606202008400d070521880f80d40f00e040901070580319500c900118403207129496003400c4400001c8000300d2001d42550014007a24001d682d01480c886203e030064454522600801405a1025048500101c0590000d5074024450752020031413002c6809080e01005242c1a104003040800b900034010341040005103501500c1351 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 194057392 1250 194056142 194056169
    0x80d0c0606050f06221d011401090b1c020409180201030506011128050114150103090b0f0601020a02060a211803050705031911100c12090501110d060807 67
    0x450001d00c2c1446a5000c43e09042d030740000044015603141c0500c801005000b20002d02c0c0b8401120070308401c00c6c01d01940409480400d100d1206500c06e4840d40c1c1074525410f9000e00c0c0100704604007100c00003554003000301c19020040419240319500903e105058101c010f020a66618070024094a000524841c108242d441c0e0708610100001400040b550000740740310340308070460110030700ca5400480090019030800318403411401a83d0060b62040c141d0f4000a040029400011402d48032101b030302811282850700414240c84294100c0c540102050048030320200c2c00f54080381e240c4c0c100c40005001718004800301c55150000300080ca000715072010382040b5041c000c1c0207a110031000c01c000070342040000709606081040810491b041d144507a0b202810b0720041600040c084210302a0140e0705009559000320313003c0e03540c042d625111707200d42ca42008085040703101c5002000807020644483d929480003c00c075045103001013101034000030021035000d0812008625200590348072503013040380c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 194058642 1250 194057392 194057419
    0xc080402060912030403020402030112020a06020a08091210060801020a1214010b070c03050106030f06110c0703020609060409020c0c10090305061f08060901050f0709060210020a09080d0c060605 85
    0x906003182c0b0301840480d0025607441200540901d14080d0342c0009400c02d00c00030003c0b0310011240040c1c0b0100b442140c0300180d207500c070130301203803984100f910090040c003007804110070900e854489000800d68038000c031038098076441c18030010341d00240d001844d1030f503000501c46051030744a6460103074080460028000524040300c8160211414420140d1a5501203480b00400c9407214a0380d0042d60000e0003800116240e003000f50308007181c4c400458445240c6003049401e0300b84442030340d548000000280c16611701d10f40a004460f8001d400c901d501603401c11010584003020700c00382c41c00c465600001c041102c0440248024000c01a82c20b03024410128010400280f0024450381e2010b90035100512140010942009070713041a089510540103400130442c2d0814150303c0948107144944c40341d803250704e030510180c8240b46240110b1005821203502000d1a2600360010302c80000c8600d0003582040e0740d000744600b812004c2000320000ec0f00d05e4004024000e10740030f2100940030803a60003918009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 194059892 1250 194058642 194058649
    0xb0c0d020f0a0306030b010b120415090c0e0906250305060418060b090702071809062307080c04060c1106090405130302010509030f0307030e0f01060609051914010c14120c010c080402 80
    0x270300034002009421141d501002d80b000c540c0180380d28a03030003000300891030340701c0d18401601c1c1400c0342d541e42103215400015850200d42c0c0c540c0d165402100f403c0f0f88014807503000440103081e0082a15400c5500c608000c0d079001e84a40c4204440342c00b6039000505e150400302004141c0502030b000f41c0840d44400310500c00000c1d0f48800c4d81078035642850000c1c80c5d0303060b487e006014104078400b113550f610740d0781401180b10b81c0c07803891070748504400d0351040c0740c60385c480c04242c3c20307800740d4000d0800140d180100303c4001074a0403400700a01000400040c1080d420f0302c005400d9400c200e6000d81c400300140d91000415409000d02604512600702071810807805002014584c08020100410581c07a0390525040c82818041440203030007078002849120b4849030068180d491920407140281030120041002c0d820b030000f9071056032040f071150240342c07044400443c0e04c08003081080d180c504000080941d040c07000c0104021030503020f4100c81d01d880b03c80c1a01400c4910242c15070090200201c200301c0180e9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 194061142 1250 194059892 194059927
    0x5060c090901270603031d01090e1303030605030307111002010501030b153c0904170705100609150504140402100908010905030d0606020a0b0c0d020f0a0306030b010b 73
    0x240545104400c0f42480c40b03001074054140038049a0031442e081e40801859801599800c2d980e016001d241202c2c48410011203100000c1e1003154012400100401d480c444103080610f560360192030007040240c1c480b00020304550107c801213030380581080c1c01d501c0504040c044506043d1550001f00203643c9551195142948024a8498102c0107400c046a0f90356036a101013107844601780c0740411410400c01041000490a040c15043c44001c1401d842c1c2c52520305c0940b4420f6a01482c0700442154000120340c80e500075510031a0207009140540705421035074414000204006480440e200c401040101004180d541100d806141400720b1240103d01078010150010760540f1709003a45a0601001c41c2c0d030f0111a0083c0d0320715400d04890304240040000070745800c05c180c1d030f0100001981d698040c0c0c4e6858524900a03d000805000188007800020103415040e0400401600d0550b15143c0b005031580f282c0040d50220303a880000b801400340c07a11005016142e8032003c0c0349480340d403025001049 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 194062392 1250 194061142 194061149
    0xe0a2009040c2c01020f16050d0503071403090a0902091020070e041b2418180507050306010210051005030619270209070c02060d0905060c090901 64
    0x403500c031440b002030749100d50391502d00d072098410400d060030400fa0461009008600c4014010b01c100c01449410030780114040c0c81041c0404080741103070707242201b0302914140503a000e5030745000c1488450045480c3c0500c1c0d0300910220b002560f030307031a4107030208100a0301d140c1010000510522010b0b42c0c0e0740310b101c0d1b60b00f03072140c41e81411740300c1d0a0f0810307180301e55030040c01400321503010360040080c1250204103001c0c05540324444000100c0541c44d0340b148000711520402d1107580d80045403500e446800e000f014070049e854600052400c00080307504950803229401f00c0d180d0301500102e200300316500c2c405c15810000b5850b0852541c240040002d64610105070303900180c555900114003d00d04226508008010250a440462800300c900fa81c8000509401000343c90400c000b102100c000710200c000a0101d582680e10030203042d4080c40f02d40540242804207100b00c240c4050096070b11503002d81607801060b03001151841261800c54100030029040600011007403003025041d54030306203000d054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 194063642 1250 194062392 194062399
    0xb01050603040c08010f09051b0117070c050d0906020c031f0e0703050613021206040f0f03030b04060f060e0d0209040807230105010906080307020904030e060409060e0a2009 76
    0x10781d00c030360403c240c010490341d02100080d8a864140003513004190400c280b12801442500d20040c20407801e050460040204d41c0d002902c1112a410300b50018001d0b15004200c070300d449400e40c3c140d580c40b60325101d1041580c2020400030181001115410084240d6072481600030b020b14030980d072101c1020020403415040503984442c0130148511042005c03100075a0031504490080c00d2400445980340d80c0d408099028914460035035907000c8000030654003460303004011942d42101074035080080c03420b80004800701500c80c607003100b80b0b99490150801921110741c0390307161a417901801800754ae0000d240540294100000403026a942010090f032098011000507600d031064038141461402c0c44c08540b041c1255082c10b8016a00c056006a040c2d0f0b180400401a035a19880724a60741d0080f44002513014a00500050019104411040c10200054089800c2a03102c0100f84181c445a402003030100e441a010850003510b2030051001c00110f01041102a02c011154004940b091801d074601 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 194064748 1106 194063642 194063647
    0x15030a1103010e0a020702010314180714060f0a1404060503060a0504020313030c050718050a050a05070c030e0d060e01020a080c0f070b040512030c04090e0a0b010506 73
    0x50301c0c10300d903003003c40d941c0d21031550000e0750080e50700300c0c109600c840505d901d00005095041c0280744e0082c210009041300c520340341c0b90010960190003c02c003d0719500b03540f0340710311007103900c001030b9104503a81c0c038005c02074142c42645080b000c18000c0400000c0c0014200e501c10050340c0078000c01c51701000140e50304c0040000340e01003990011b003001c146166480009001d81040c0d144540b140050318951aa41c12082d40e0340303400303101c0c90500c1540300c1c401c00289103014032406500c018201300c20051810802e90080826081c2072008080c0603a01618001c15a128541d40304500d40c01f0b41d003440040c0c4600780041c043d400040d801000304540300007003800e500210054a060b1024207021900780251b640320382c4440240603109441038020f014030310840300c5030f080c000c604c0f404484042070350b03031440d117407859044401c003284400245e0000085040010002880c3d20304456048818030b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 193884892 194064748 := by
  have h0 := BRFrame.cov_init 193884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 193884892 ≤ n) (h2 : n < 194064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
