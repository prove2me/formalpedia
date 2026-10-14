-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1301
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:15:37.391466+00:00
-- url     : https://prove2.me/submissions/6d43acf1-0906-413c-96ac-5dce1713c7a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 233812949 ≤ n < 233992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 233814199 1250 233812949 233812961
    0x180910140408040915030212010e01150518092803020f011e1a10020304030218040302060c0309101a042906090d17090405060301020a020c0603100803120a 68
    0x562000d58a080c08002055a81078606981d0b5281020807103868889030b41e00004071950002e5400300d8400c40c43d102140040d44800c02118000d07000707000c03404943c1907410030070b0204e106140e00410041ca014803c20790850b4041c0e005202601500c103852070740300c114420380d107001c80700807550422800d08000b096010460a0080c0904100900265900d81c00c07020004000c0e8104040860710f8502d240081c034508404600c03500c0c8010704000d1450702500000b540c80d0440e001c103e020b46e689041441d0b80b8441000058452035043c1d00a201d9980d8444000b0550382000d000d001217889040000c0c5d6403d402c500541ea9480e040344034102a080322401000700340d400450f070000612003041502c05100c0040000098100401d54006d540c441810010130844000000058040034070210116440244107004095075030701190144010b450f908101407c030700ca044042c5016a0081888207220704103040038541c82031160803010f900507690f08509045910001240a00320160380c104044401684101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 233815449 1250 233814199 233814221
    0x7170d02040e090d120b06070c090b091806012306070f170412020d02010203040810051509010e040f02061303050a02030601090504030f180b0a0302120705160809180910 74
    0x400801144d41806403101448410340080c058841c1e51030069a21408210f4240700d078056480100d2550381c2d40080e006090f08165a4826000c1d40086640c048694030214031988143e000303028240d10744910102140403c04070705447d1400098140c6141e43e510028224040c09481845001592880c002c00c1106e04400ea541007503030244000c0c4103e00a280d0740400840d410380e01d442c0907003501c1c00140e00e03500950784035422510440c1a10b039490086038001a0140384200146481c0085560800c00c4c0c514090180500d034030925030024001c03600c4188a10000360000e05501c5c0f030720403184503840c0c15160f5508243c516134000c0b41c0d040214142005014010410303a2000c01182c1059a00104540d4407410384a0800c00c00c0e00c0c00040129400c03482100800940d4922641e0b00c1c00c40c0e001901035040804a0003102681200049000b409031044030388201c00b17044091104052682c400180f604400d00850700b103041c03003840d00410101039400500416100d0010024180010000411359030b68200e9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 233816699 1250 233815449 233815453
    0x30e030c1509040902041b0c1104020f09130f022212050d0c080408061312030b0604060c060b040606050c07060e010c140c130516050c0a0807170d02040e09 68
    0x154441041c9460305592590b00308440200b0b100501e400010003030300c141da080c1c2c1d6145010681507084660409180031145100f100e40306503900000081100700c0c0201603580340b1210081003510b1092900e402d01c0f0b12010131050001501c840d40c045880100e800031046d1030310310349520385a030f561000e40e040140c000700a160141d000a0f0f0b800e598158580c03040c07001032002d210790708109c02d04021f03409081d240505110005c8a546240104100c0301501681c98103031550b007400e030810181d440c0300e80101c0c5a4460b018040c41d2815203440001c80c1e1a60790944107840d0155039502a2515603500c1c0a114000e00d8165202a1035003032201040c0c0c105001c560080c41401600a14018036076040005002c000382c1003001c1c1500d1801c0d00c04082d050200001780740354004010f01d074000d2000300590046000304401b942e03003010304210582c240c40920a1203844030065000b101c0b028006205540108034803480740d5545042d248502c10180142e4000b8100398034002e40229090000c041c44040f500d51002d101b00c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 233817949 1250 233816699 233816719
    0xd1509110c0309010507230c130c02060105011101060306140601020c0a08060105060d0204030803090f06060103110405040e010b060c01060801150302130c030b180a0c050f181507030e030c 82
    0x5001d0340d6a125100201c1d040c0400070805600b0700140101c078598540140b04448483d2105425003610340c5920030210380b091180d040e4100d90144244111143c085c161f4009100590a01d03005440303411903541413000a640720b0002100203240f5025001c00000d00401507119401c0400001e13040407500f091050140141d04e4040115074400142c45045810588602e40d58a0010001c0800792149d42c1020781801030010602c0400100000c02240b4030905000755081c644510004400361a2030320100080828148014882c6240c1a800007100c0303a908000003415602a00100d000f0b03400c68080c503c500d03592524104000d201c02c2c0500007082d038400c165181c41c2400d5a00048441c1c1292031030b01083d6030344402c240012402036001040500005240f0344120b500103022040710902160580040c50619420090041c02001504c0c004001c0d1b1204605018001d40f0302c50004007110805640580d0704000c03228200021780c01441d695010ba5038860b400703901c000a0500e031440c00b00945015100c440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 233819199 1250 233817949 233817967
    0x90b0417030f010911040b0315090f010518100e190c0806010c03030e0a020901090b030c12030a1101060e0103060e15060f040f09080c070e0c09010e0d080d150911 71
    0x100014155482200009a4a105060300d207503980a182c000300301e281000009c0c0070300c00300c41c014800c212410440b138050301075990788459440b5840a101e080c5d04034203d56012000c000c280d0140a500240c0ca10203021915507035042160307030450940b52401071031015018540c81008a00510700c01d2074150a0440042c10300c000001c2800402e02409002c040d969520f40b03910340350510046100c560010240000c80d6183c80f5604020300e15139412034801e114220f08110705040000103030b00950001005035017403000781141500c0c28030075080d01c2d40781340d5683c407404240700003022101406140030701000224042102002490140030f44c04c0541c513140d02d4001c100b0b480c1d541c6100d00c1c0f10f1080c19680400d010600c011450007414040c90010400da002280c59122401c001500a0803900141d8141e0b400e52618103190460307200b5100c00d2800519802c0c4096140d0915a0090499510404002e40303031030400440b00040301d0070781529159040f80203508200c02081402484902003030047c1e0f0600c0d1802074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 233820449 1250 233819199 233819221
    0x100903020a02101211030601020106060305040c0e060a080a0506040227240418030e01050313020603070c051014091204031103032802010c0908190510090b041703 71
    0x74500007403168005011030703001d0521528050031413140d1300c04144449007008102e00280d800c00c0302d61900640c6400d01c0010a81e120340116400b640d0441058010307107080031445900c00e0001400345070030143d20140040c0e03094080140c11010750184016250600b0148108012155412214901000e030140e040c2c0c886103d40c400b603a00408400d008882c000c00715403401032006150200c07240d10034a0411141c504000f0344507907942e418807990f14601c000c240c040c01940c9a00081e101604080640d0800c48014107203080250b410285a00b40309500e4403060361002c0c03524503400480f10700c03292251071107019102e26100f0700e500308038020054100300007159541b00306402980720150203400351410120041d00c0c280101d60410350600807405140282000790441c2d1000303440c5c010010b41c68201002c010900c101107070360940f0004005004448149010046103c408480940f40360181d03164250070b0180714072400b5021403060314000d40324941403c0114290110f200100c10101042040003016034031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 233821699 1250 233820449 233820463
    0x9180106050307030510080109050705042318210d0b060309030702240a0906090504090c09241d0609091504140703061a0406060203030a020d20040810090302 69
    0x1d10b10300001c4030b5640400008800c0810f50202c1d6440d441d10440b54144070011485c3e1090320cc0a88090ac8040380f000311002c03003280d44455100e000c9000d4004284410041c0d1401407208580404880d00001c2d0048aa4102e41c1c0c220708001c071360a00010038400058040c0207010040204072003107400c2d4580800425100d110302c1e0700c0207103e80b9a00d0b5800d0355007107010428a40003a020070b0b12a844c0d2941c52400f820b03644550040e4404241b45000004181c505401a0464280d002040000081c90400454081d01302044e1981c481040d0303450302d904521000c910000141100d0050820001040540e40c00500f8081d04260080d02070100700000c0301400113201da01c40509400c00c00c6540d8440c181480d040444000380c0d4082c1c001c2d00c1c400001c2c007080d40c01480003401200e4036103140c9a954410042101c4452251a003d0703002400010707010080781c5c2c00781c80c00788640078001c00d00d04a10300b05401c003140d580d0504a00e03054080350510655030200850b2501000c0e01c2404c000310362003a240655900c1d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 233822949 1250 233821699 233821711
    0x30a020603130203010f02192a0209150409030f09050102070b0f0a090e04110916020d080a020408070909030305060a03051507051b011d070315051b040803091801060503 74
    0x1003082c00c01191000d5120190482e0310074000c540b01c003070001c001d0075001e4003000010b0018501100481c24801210600d008070120540a41e607206041c0d401d1021161004007a0121440707070f04503e403281d40303427401404c0b5800d100740d80e174006501e50041d01905510090708124110351001d08140320300b0015508460075455001a40740d111090240d085580c140c850700a07040c100f8004003400100080c006049000e802c0031210740000d82e6948103254041000300c0c0c0c0e14401640b11588424955000d03070f0000741c10080b1100302614050300c0c0e0424615021903a440007034400c0e030300c0742910145a40340c803440c0d4001e031003196054096460768070346d55610005a5a180c030b02d0030148000c103115901440844840c01d020365804016200070000301381c0206003902c2c10035088100305c42110110301010130b515060303a50000a0300001c100d2108007170024800141018030450080e845520b01b030400300044d0008003405002140d1b10481081880104108903080d40d0300d1180e0040103000103900075041e640d001d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 233824199 1250 233822949 233822971
    0x9010203031b16080d06170c1207120503070b090606011e0e0d05010506031b01021005040c08060103080a021b090f130209010801020409110307020c1003060b0f18030a020603 76
    0x1c20707038140111485864814402042d03d81104410014a00c015001019031150100b040581e989829488142c2200d5905601d8000d030f028101a843c1000340c1e0b58590114800b22002240c803110503841c40b00c1c4108007594203a00210b1aa8100043c440c90190b21826503009040c950615500181030400c04000c00700360407000101c8125858451800b0107400880200a00d6003103259045c16402801c0580f05180240034002c800302c86c0402081ea114003a03041a0300030030b10040c0d030032407500080001800840700254036490000c1c1000080090501031806032800681d038041040000c0d140180310f240002e0007945a6480c148903030b80d1400f0095000c008a42000c91075519010028141c1c0c2104c480203510403086800070601d40ca05601820507506105808c012a24100354074000c0c80c00210f07205c10050340310420302c00d041d040000e99621001131a081c0851203d445448241362034020140d44180c0b0100469824a24070390301c100b0101840302a0003401c01d00075a5008102c0320f110080a10060b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 233825449 1250 233824199 233824231
    0xb07080a14100806090a020a26031305030d020a1524030b071805150903030f040905041104090c090b010212030405010b0906090f071206031202070510050901020303 72
    0x80960001c420a80d041030080809107820b8041c00080681e5020b944000c2c46101e00140840d200054186004c40d0000c0031802c5403480c14042c07920b5070191134058094010080d0b03011140e448208058000700764054811100345052005040c5016900e458440855001d0000c680200302c06030724190845070b0b13051000c19992410700d1b00d82c2c42c844140c001c905507819549000010703c00c010090b980500307000d0343d0381010014045a040710407004c038002e641c2d01c5408103911030540805c2c5401402c10090290a4904013040010030141d01c5e00664899a5910780b40c00c00c200c1004140122840321a000321006c00c000451501c1f40b14400310b0500494400382c0c1d650629800c01e0b0f000f0051100c0c0222102ca105603070f80b17802d10b0440e010303150180c0c07964011103081c00072a80318034051800d1845800c080a50344d401d40d0312040212081001098110200d60741c603100400824103546148402d0441d680041004910308000e002011043c500d071403080250920420320641e0f8040200d07500f10130b200c1c481c0c0401c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 233826699 1250 233825449 233825461
    0x1c20030c07060b0603100e07030c0e0922150b0d120f050c2a150304030503040606050901091407020c0f01112d0f01060b0f0d0e030c0c0a120b0708 64
    0x2c14100d10640d0380302c138010040040c00720b9031000003410f461a41c00d5a501d503445248054040e10f0b68034008034041548060400000d08103a03041690120f8181001480d155260f015107003000650300c81036500000240030368200c0700403400f441d07403000002e40780b101110400b03072180c03180c03404952090f0302040f01c0c2c1e0244030403451080301a07404030304c0d1600c2034a03855005965003c40081e10304070107020b170450f095091034492801c0383c580c2a96200d170071750451541d6140c0c0d608903441d500080c07040307400d83d6031541c01191741e466004250f4080d0840c40d10005044030a0f249841e54104000c1940c0c2c21540701220041a94440c22020702e074440003030a044295400080303840b0305110305050b4030b440c044500003050000300080a500c41c0514421820341c2e01e80002d81045600781c8850f8019020300c040300b0000c40880d0450b1100820104000300c10026480211a0300d0030b00715403002d280011b2551001d040c10150b0302d403a080450003005126080c0304404802c0c2e842c480791601c024854020b00581c0400280 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 233827949 1250 233826699 233826701
    0x80d050d020a020a021507050105010b0a230c010207111305011a0c1e0a1b080601121a0106050d061e050402250507090c05090904021e03031c20030c0706 67
    0x1a1a03000342211000f066604561b040ca421100c400c0d6180d60802c80000340c4803070b039082190210072141e500da101145503e0039011078503001d0000c46031445030401026401c145c0030700c040c0005a00c14076603140307540303000350410144c030700c0c43c094600c070035450400100141c030061031030f210720034507107209080d01c420300c80d1044c6080030354000200a007050800346220980b8030100b140c0c80303900e12411403805074000d0b0139081d600700c15007409910703e20341c8120300610030307501e00f42d4142e0718442c072034900b012269001088141500d2000e81c03108003c42d0011482443c00b40d01402104042d1828454500001604000e1019481014410240110303400250300200564034249031101041506509404000703500c1c2840d6038081e14070039403180c00c3c07510b50341030480c500c507000321503441d0002001014191a00e408109107911035a81c250249040c40d620300d044d80e14144007820451400d1903085a03200d4107041c0300b40590300c00d001425654803010103e01d03a0003d12005032070300548114a45500d54407545000c00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 233829199 1250 233827949 233827963
    0x30c040b04020418050a050c070f0609080702031506150a05120417040b03011d0103120e0105040906080c040e0115090203060a050406080c1002010b0d060f06090204150207080d050d020a02 82
    0x75200c04c9803810703148000000d4209502405581c40d042100d66214860301e2680d02a00c0da005203460303807641ca88404140e05410100c2a2401010318500d00002903000a19026028000000c510580000c10500e440d01d144101f0800c8610980646850306c0326100a1041c031809812030201d8101601080900000c08904a400100300d014160f940d9250380030709503107800900c18003916140700250500030564220407641207940c00b0311605c0c004032940f07006660101520152904001e410b02000481d801c6600070800204900c001034000039000c0c109100036541c0618031a1080c0c0e04084580052044201c1340c801122540b0a0060304d82d110f0a0025003410101d51096510509090010034600c0c8082103c589528040b900e0b0b40c90401c40e50801d84c280c403a083c5a8692000c1e1041804011800c0c41e00b0005050340b5007500001e126844002c0003003240c03c41d030001152080758020903415070750100481800740000d0340042140740c042550003020f078468a40c080c1449a008100045240d008107e50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 233830449 1250 233829199 233829209
    0x3071e08040816051f1b05060a140604020a0807080901020c1f0e0a050303070c1406070507051203011a0c0a02030a150f0207020f06130806040b1005010e030c040b040204 74
    0x15a5165a24411240d85101d4024004090700f900300d00020b8a250039185109011035900d00e002440d00724550a944107000d00c42045800083e14103041c2c00282c00740043c07842800a00d000240c002d401000303082c3c9500b0020011406144104100505560041c0c0c0f0a41e0101e4145010032860380c0d03030355000c0c0c064000c41010441c1d600c20242c00460546292010903041e1042050404c18a40d001c800fa550701c4a115070040e1941d003080000c12981da01c9010003d002d14029240c017080f010444a9192800034101c50410020360042140c10070031a040c003000c07164450181985085506120010002c2c51017042400c140441c00181562000c600b840101d03111600141501c0f021402810900c0d58001c500d00c2e0700384024500350a01060711003d200391010160040c10180d015078241040c04180d0744902034404412125140c000780c02001000980c0c426486600302031040d040031541441c00d2a80b54000c1e505000d030f07120348500941c4000494510102c003c0340c011580c41c401c000403900034402d54101c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 233831699 1250 233830449 233830463
    0x2070f060219141218070914130201081f0302090c0d05071106060913050d200a050a02060c07030c06020d030c0306080312070e1207170a15050702100905060a0b0307060203071e 77
    0x6c0010301c2804e07580a080d03284140c10211526907030328180486c681100020080c0450710500115485404d01e030582c113288011b1900443c0003e88076000642641e03405c84105419541c000341d64101c0001a028480c0c10045e00d00384005035160804410b40c40d008000c01e0117008015201c0010030f0780600300e02140c2507541100649141d50340318a801802504400582c0c0040c01031100310842c06040041c070120b204d074200000c0c00fa42c4119500704a180c3c0d02c561074070713801403058580202c082000700c1e03640340040003160010038086000d848090f09880c2c00507001824540391803801c008046010084540c80d420001c4e00c011548c1d980f201c15220b8424121100350400d4400804031024800011600140d8071922040c86071814240300c015502c0d060024020242d820501c3c00f504030241c540c00041d0401e0702d50045e22400d08001e1034080c11180810b0059506520141c2489298501d83c42555a828001e9015100396401d180713021b075891103040402000e1400c03c450341341d095945840b0303280d0f11300e80c00b03c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 233832949 1250 233831699 233831713
    0x40b06150301090b030f0d02031605030f13060e030c010903030c020315090f010e030307050f2809180903050f250b041506081009050102070f060219141218 68
    0x3d85480140f4250308070b00d01a00c14030011014990001a0800412240da03008603d01174500304aa45004208002201e481c8002e2000d6101e41030b0300c9024060300700400441011103458000c0040100c0070589090380a0342200c2030f081c4290f40d00c64024800d5035050700302007218030400d101280c50b204038840c0c1e80d000d05c0b181c0ca05100e03c104011441121020080c0000d000343c4082103c41600d0344425500d1101141c8108001001c03041c00c1c00180c001001051140290700998103220903c400c2d2148043c0006000580107114003d401d42c420810680403a00400c003000321660050060300c601d00d810307d0145008114039403a501e070301e01039141184000908920442840c07a10014480c0d09540444040043c05989008401da91083c001100c42c0c0d07000030310492031200c0314040100b40d02e403010b8400755000c01000d00070603103819014105030b200703102c01659007120100645021030546c2c1940200b02051030302d910206501d10564503503914080402803140c4405210181c50040389040740e0880c05109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 233834199 1250 233832949 233832959
    0x70c0606030c05040b0301181202100509030301060906080f0601050c0f01020d02030a0606110c040c1106070c0209010501030b0904231b04201806090a080c030106051206040b06150301 80
    0x407160443d0000d440500c40c4040e20700c1050300380e4561060000306a44103007030090216400440b01a0410b41600556040001d1910080305aa0382200d052035140d01c000010000d0650001000e401817555140c584200d080507006000a00006800b040c1000000300351304074484001e0040e004c1065100c0c00031595070b00c021403108065041140c0000c1c50b10304e843c00002d001406018681768a84444019103058851007003040014a0341413441300401810072514095140100a000c1c01040680c4520f900d0b080c1c0e80c4100110350700305030002410582091030114880d181c4944450304507612500500001c01c9401d071128281900400320300303c9103d00c960710079140080700c55041c04030002b80c2d07007402004d1480841b14000a0711156991000804200b0301c407045204c90100e2208010007000d813440c1c0b0070003100140919020707801c002600d8101c4074200400c0d00d808d20461005080c01e980c00c1c58025204200c0948070200104041c051000e80b100140d0140c1d5128003460080e1030a40341d0342d441c1c1d6110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 233835449 1250 233834199 233834213
    0x90607150509010c020703121709060402130b060a14070c0605030f0109020403020f011b150221060d02100e0a0306050702010c0804261e03061e06090108070c060603 72
    0x50440d01403151916000c42e40304281030280a031302d2211500106806d910f5a51002c1404021180d0103041014651108800202542c00741d4000d0b1583e10003418542002d00401030810150b0f00032001007031804040d0b0690b41c44440a17500460300340e091980c038503441c130f8200740280c1c880c011009011441030f07600420b101d07400402542c020341329000d8984c41c90f0780782c590400c201e110b58040650700c20403419801c80b06622444500b4801400052080d055a9840c1d5480c607440310004400c006880c0c0110b2140307140401c11390740f4861200b030100300590751300b0940041040d680a110020f8040c00820000701080740c01021701100003a0064200900c0c80e1b078a0408000a050030f0740c0002c010b50a025141c0d88080c86448518010398000b004100c400d120450180e8030b240e500c00910f103010303400f400703da10309004130401d09043c0c0c410030220598034078086082104c210030080c9041900b940d00c0c1403402e040c0e21103100351400d646003800e1031080740d20b03004403e03101c003160610000c0900d820500301000308020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 233836699 1250 233835449 233835473
    0x90109080d26040f111c080a0f020a02060a05030c04120503040e0112020a090e0109050a0f050c061201140402040510030b1017060d0218090601140402030c0a080a02090607 75
    0x28002c80061000040000280d00180c01d5070054046061000a03601266084c42900c104410080c01d50410361801017000d410141034400075100b21101160513012550010700d52000791440d0b20140103d032403203a001900c140285030740b0701d0801c0340210015081508050455016101162003d142c0211034504248c1e00e50040c010500151510400001c04942201404c003070158010444c0c1e100070705003070841d0000d141c0c0c420031010542d25000002c02140c41404006a0385004007050552055142401840c0c100944240c07030081c1c20400034040c611159a40706410358060001d81c03000c016103140024040e0045400ca16440f8000450240400c2e0f01075001d60301c050740c2a01c411820002801003691400c0340000c80069a1840c58009001c600d8074000c1801002e1005200c2c0c2800d44024604002111003200d1703ca285500540c01807001030203016180d12001030403942945546050480081c55004594050701880102d1000c180c926140e0b4054486107170001d02030b079441d041c00b41460780d000d4103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 233837949 1250 233836699 233836727
    0x7170d1b0e090912121e090a05011a0f1216031b06020c13020901020a02131a19030f0203030d1107151503060b0a1a0406080915040b0c0903070b07050d020c15090109080d 74
    0x200e000c103980203c18145c0540185510b00400c80580d08551505201e4002e000dc3c0e00841a40100504407400d00e882c500b0107005036014100041322916003e05000100b9410340018066601c010081c5055654450f4080c00075401000090f807280d01031030040c3d10f0841a0303200254000c1050074000b40c840e92030f9000110085644100381051450b06061005400c0032442411101901d00030138400305010031302403203400344050b04681c41c2500c600c14060031189011090100d4482c00200c0005020002c0906a6a07150480c0100b1041c08a1040040d10419910005080c0c40e196048010381ea6a2140358100808140308010301e1030300460420042540107019003800315000740c011810f40d07400014808045001030480b11015210780e29002c1c0444001011100083e10802002445403000d0107010b00514250b100f0a44840e1645401410b05181d40c0c0c140c021980190201001c595411481da04540e250072080d555815640e80106d41c1200c23207802503521803054001c1405040d41c001c44031503402c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 233839199 1250 233837949 233837951
    0xb0726070e0108070c020310090c050d03090302093403091208090d1106070e1f120f02160b0a0e0601240507170d1b0e090912121e090a0501 61
    0x561452810313201c005a210000c0d4041c1d208070440023000800d94407440c42e09004100d40c80e015641c41001504103209003604500040c600714040085040003e08281c0102c24000030a490a1417a1a180142c0d81d06c04030004041401d00800341e0998004c2d84180d613400e070491217085014032120000b4240d132400365080d501c070b8810741041940d014861000701042e20040c0d4041c10f920344414034111940302c40c0ea0009035202401b52164103035282d107607051031000b01a41d240c00105082070744450003101c0660700c503042c2003070042014907079000901d490f015901d503201c002c1c9002900c500300101c0c001c1c4801d0704c003c48a03210310400030440c04c000c000e06400340b1441801540b903801001074102c80700d0003010b00040100800315800c40360a4106005002200008600060050803055844c445030704600500c1d400303c3e0280e80c85080381c3c02d00a090310303403007040e24005292107181050031050038807458032041d04201c40d0001203460700c450450703945100341c240344c420102c9091a520064035807030200c0c8121015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 233840449 1250 233839199 233839201
    0x3050607030b0d0f030e0604030f170c0307150b18060f010c0201090909020619050c010630020d06063003090b16080c0703110d0b0726070e0108 63
    0x150710074011802c41d98006019041d00c2c00c003903641c0e0380102008000880a201d5403a050750056140c6101400045002c0d040e901da5140e801c0c02c1540708030400e04c45032817030030703104219081c90141d00004482c101e91f80498141c0b0040c40c0d140302480142403d00d413450b0700013020780071824454400c041c002e0080f03008a031401d0304109a40300645901c01d480000034045042d5207410460310748650b100307400d0325001800c8a49000050703a000503501c00000c42e52008204d011400030303000082481010b01400c00480809921900c0d03c2c03090303030f0074040688011020050a0111411910f0702070020700e2a60344038100340107941e00c8004028514061611110381c50004110581003624074031200320105803d038650360421820034036081155400b041c112040d01c4260301800000070940801401102c0e0384102030558035046182001040d9102c40c1d140b4440c0c0c0081601c2c001081702042c1d040c0e00310400e07080024026018004407e03c0e83e240c040c440d402c47e4013000400000f071b0381010004120300307c00d07a82c180e01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 233841699 1250 233840449 233840461
    0xc0709020307180906060c0f030905090c0301140907140f0c010c11060a05040b040f03020a0f050d140309100902011103040e100b192a12090f08031c060e0a06030506 72
    0x44480c00d00c030307103000103003e07013400000314408ca94907045040c0245489000c04d620344004c42c034684c005071000103030410000010010700c01c85c207020105060b01198000e2140c18041070061034080b1200364996000700c000754442d007991200040b80c42e0350300c2c0d8030001e10401005c024050000c121505003142c0305c0c0110400199680b0303613403155510869110a02c070580d51155110f810016044040840951058040c1e01c0081880742e1300b28200c032031190005005d012001800185000c0c40320b000045014400c0c42130000760790002c44c2803090762098040014082c1c105000407995442800c6041040740000503011880407450400184150100002c40500555400d855001d512030313483d0950a1a0400c55285617072845200f0394542d101040100603e105c840100250700142c10f508100c036011561420380907540d4215241400419074250a06807842c98218143d469200d04240383c0940d68006081d5646081c1d16071002c0d028240c50380d8901d074207250564080c00100905e00007660036100381400515 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 233842949 1250 233841699 233841701
    0xe1b01030c020f160e0c0f122d04060b0102010905030d0b061e0301060912050a17040b0406030b0906010801150516060f050405011d070b0702060705030a1709210c07090203071809 78
    0x44541500e8144234948204a05000d48002c8050500302080340400c3ca0103801c031400e40803a418295080c3e07001c110a0500b031a20360b04071058640e909056904041804001c00d0b0048143d4031a08410000441c810001d0f000042852041100c8098544c50012196a240a42030302271030503614103840b2201616224082c003030f04481c11200082040c1e04c02c03e170304c1c40010300c1c0c0e1617101b1a0600a040f00350801d134451008509640140e001040003a5490161a0061a00401164010b8030030b08048000d94103003000c83c00355a0101d4031000520400003040004020b40504203034540350418010024581d8030b400141c06890705450946266081a0b0141c03071901c2d0000321400b05500007001400b4940c5070802d1050f0940003041e0990b0702c02d00900006d80840c03002d10040421110039900d5100c00440c01041307003043c07100039001802c0b0ba1300172580701e288140066407e2400390003482e0407a80303944000302c0003864100703933404c041032050010007030002260f080380440f507039203110507580480140c40306030341c0c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 233844199 1250 233842949 233842957
    0x11d07020105060d021c081303030924180f080d031d03040b0c0a0c03030309050c0301111608271c02010c0206030c09150d0c081504090212070e06040e1b01030c020f160e0c 75
    0x2140711510a05014060b802907020dd0780043c4018030f51303262a6a9070110400146080c0e120b48100d0300500111142035505104040381100051030925000810040040d50f0327000398096200c640d900022150f011840401045043c164000c41014141c0e44038034004010300140c2c04201c403280b069918a9034680f0301800740200021031103400702c0c20300740c0713a170700703001e04031607000c0d01522800780070420503001c0108a40c1c19400b2a8001104234048662513007400404440403441c0285100d42a00f04001030307038403085d42e00e8110340484002d40c60761143c031440c0340e45216210074141d00c007502070306046072a1000c01c050050503281079810400900140300940f415281214401c110301501d48184071180360503231041900030b001500300c1000c00100d0500c645061416040a0007001d0a001000703003030300d081d00408180000d02005044c0c80400e0320a031340092124410070905040d2541c82c401d054a1080080600b58039210b012107195000300181d84101a0181c0945016500305030009800c08041c3ca04035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 233845449 1250 233844199 233844239
    0x102250209062101111b0a030203160213141b04030b1306020f031008070f03030507170903030f03041103011e1a09011d07020105060d021c0813030309 66
    0x2124150b031040104a920345004408403107004a0f5004800300070000d10072814158151302c0d1340b82d80c2c0c08102c001894110414030315460b46500c10741144001035404019038041b2040b0000c511a0101c0c00d01c002030404170740034003650301d82e45401030242c90444202c42c07490040303525071480c003668408840e05500520550001401550251001c110320450200036403103058000e400049c186100906034803800e5000b0781d41d1020440c48448148481310050122200504050760750300c42c210b203140c4c1c014005010340240904004070074004981018946070442c0d14110b40181503d0b5108501c4680c0f06a0350000e0702e043d20500680d0714040d00b1800c05204e04030340c0d80001045180300403010710702800034003100d900c070314443c41d40e03a40e5054548d00c40103a11070182190b10700041c0040801c034502000c1c401d00421404c11607040c02d00703000541d00d501410801a60b01694490400c00e81000c810340351501c00b00b802041450001510000418146404015280710b580c1e102034240d5200c8c0007186450703074a40c0d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 233846699 1250 233845449 233845459
    0x10221060d02010c0809040212090c060a080708041110120f02040b09130603060c0e090718050f12060430080a090303090c08010e070b03090d0c030c0605040501022502 73
    0x24140998080d070ba100c09405d00c914251450f00d071004011505a8200301d8034258004283c8c4240590f0003401e1040b140349400a07600c01c1d00340f1101c110010900c02019005000b84610000032405009400024184050000e40300d03560600c120301004000c1100b107852908400e1921210303821400c06402100c0c11503898070646810410040304100d04918800e050084c2e031595581d00200080c42030041c281520140c1e1030741200c0b0303104a400d114030102c004084d641040401d80030100101c0c1800c1c217900c181d80055807820000444003010940300810400300704a64802c480800c8200314001d070180c04001545120b05130440c01400c202ca40311825442210085980d8100042902d40cec40ea02102c0c4c0030380a443d011814001c0e54031401030405c401c1e003204070507944600c411103035074004100c1040200040e9070310a2441c90110300700c54540d403c0c00c0420f03040040b90842080dd051040400000407508801c04024a041514240f0b000b5481000043c0500030342009400340a074000c1c800b43c00c0280c001d06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 233847949 1250 233846699 233846719
    0x506040f05090c16080304022b0b090a050303090d02070e0702060403030b0a03020607050d020c01170a0f020f030c0909010b0723190606050315040c09051306020c01022106 75
    0x81040314922009104508a83c0103000000700d40002c001103d8845004020036592410300d4010b00140c100c070b08000d41c1100d40e600f105e845c2000b402000d450143c1d034206c00c01d46d45544440d010a800c114a12070f010700144004400d0106d00315011600342000390168089a8a1f60b6842c2c2c40051070b82c0045904401603003240e030000d270119020b5000240700030030040c41c102185480e43d00090564100010988950b40107044c2d005c0460b80406c0081c031684400d0910035000069500c00441d0348900810a8a03107545030529090200302d26015592030207940558291030f03142c0702620410030781000703012a110b61922400001c03400444c1d0100c0d11710642000341b454207000061000707080e004130380300075190074400c2110040c0b4112020389001c1c4031031311440c0089541450700c0d082601e0402c0400b407030b61454000800303200c00980b080c80b001c0101c81c0002c1d008202030740c0d61100103880c2ca440810217400356000081f610790300f11040d0300410300c0020b41c40c0400e81128001d9462400d400b001c40b04190800a844 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 233849199 1250 233847949 233847959
    0x30e07090c03020d0204030503120f0121020a03050d0507032a06020a110d030204030c0504020405032a1507140a0312020d090c12120c03020a060b0f04050c0408070506040f 75
    0x5085001c2800150a000d031608501e501d0020499100f5801682c0c213404c0424400240180c010046400c854429110411035042c10b2500044417010703276805505055031043d020031900c4070b59003c2d00464108060b5650340d40d06543c050099800120200d0025030362800e142140600006640c00d446c2c144801e585445040f6a1002e00075804200c1c01350030321800b03041d8228195410844812441b0955401503221031071403a0014005906420081c421401407000748865100085c1450710f03507441c01082103800130041c84020a0190f80d0f01421740001f01300e007031103000c0000707034005042c0d0500c00e2048088018024601c25240c0d14008001800203020b510307001405481500a00381c0f941442d00d0000b010b480596039014141c54591000d800000264030803800d00c224907180003082615400c1c16001c0d206d183e9002034844c0c0018100815050741e40314002036988880301c4a8219110241c400c00031070624031580f00954100d0321491443d4420203601240d41d0801d4820345044030025180b000d0500d00349 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 233850449 1250 233849199 233849201
    0xf0e0d0207060f0509041b02030408011a0d061503051b010e0306070801050405090309030601090f050714030103020d08090d06060503010c1803080a0c050a060501080601091e0b041d07080d030e0709 86
    0x882030b40d41c5c06919581c200c1c003580384070042841f0010098005680d03a506d018803180c25910f054003484120050440c0c0100c05031140d000c05510f5551201c80080c801e80c411400c5241c405040d000641117220700c0111501e0701c40000207260000200340c0301c50314152a048105079840c50101c5074100016500f400412650605810203500b0900140a880c10302900b04042031426809a100f8400f0b00c0d101c5198501520b81481070982002c2d0a14205454940041f000c51040c4018030000f8001d0401207404070500480700280c40c0c00c580020030b449414600381c1001c4001d80b00c40d01429100f54a44000e40a030340d401040d00c03090391424450ba00080f00d00e552170318031060b080f040e030341e03410720030140541e50010740180302024440b03100b5040095a9410164503070b2030840149c111201d80d510300942000402e003801c2d40914241e05040e40400c10950580100c0c02800c6100110940b80210070341c00483e407000403451106507082501211028086414210203940d940c1d05201d107107800c041c50038030440c1c000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 233851699 1250 233850449 233850457
    0x50f10051b0703030926130e07050a12090b07110708030c0a0201030f090c0b0406080604020310090f11041401020f0303061c030c02090709090c030606300f0e0d0207060f05 75
    0x644c1300364148411203450400004d40b04010355144500c00601f140021114090401c064588a071000ba21840e0500010703180c0c3c800c09001c034050191003070110001c0449a007100091981c01300c40d4000b6030402c498090540700c880c0c20070801038003800c000801c800100206a074100a2148014401c0d20925001500206030803031540d5000e80d00c52481101050800d20503100900e4500300c05079a131803510b48001c1c00340303070090005c07403084c4e00400034083c00c142001c035000156003003001c0c00070714030b0400a42007000b40b000180c000d0300140b010800040740503040524220b030030340a8083e902c5c84001031002c140ca9200490f080c0754841644140c00580a00c1c000304060340c1c80c0719081c003404141c3c1c030340c000a1205a00f01c803440c00040c1002014010107070680503440e81881c0506060203628205040034001c1090f610440440820300303000711201c4a44c402d5a03080c200d800302403c0120b03101803950500680225807844402d8401c0b03480104c2c2d160303c0090f103101124074035070310400c46040d80d240442c0d150340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 233852949 1250 233851699 233851703
    0x512010b09011712040e04020a0e1e0c120403030b0a090603170a09171006050f01090308090a03060603060603120c0809041107140c0901050102010e03090d030201020403050f10051b07030309 83
    0x404c28401619620841d00100040c112120360081145401c4c41002001c0b1140c2e0484207081900405000302148071802504031500742e4801007079140e41da031910100600442c444030420035820802e100506805601250300042d040d13070f410300c0d00354075982080d0590381c01b84170081c0000203012140055030b004001621004100e46480c4260075a0380618501406c040e821080d8076421203500103245108912070040145811f80d440060740c1c05071800038022801d030b4400944201800500c05101d41d592504040281d54040710070407020b44c0720705202c0010481400308469040085030504450360154550600c401d5108010b50700c5e20007084240005007330410700001340500203000f080000f0361200c04000029400c0402031600c2c083d00c904104c00200183d20203815a490017078900c00a6001000b00c0b06101c0042e20302d030b0604411440c040340207200d203510150950265120544414034042441400c4001c1c1e00f00501c2281c903006526052103220307840303840d9111010401440024001c2d04280003540c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 233854199 1250 233852949 233852953
    0x90402090307050607060e1b090610030b03071e0506030105061602010509040615020705040c0509010815100807020d1e0305061516230a140a050111040512010b090117 73
    0x40d43c500100703406804c005400c48101313440b00d0280d0841e000801000c82011041707614203c1007540b00c00410325a04000d046207000f04d1800c00e24003600c90007500100e520f07450207400c5a054035a9140448080440c030101d4078903400c107084c40000c0324030340003054078182c66000700107600e8414544940040c41c5101d480c1203041c8030050180f0316103556148182e2009120000320510705442e442c000900740065500300520841c5804202c80100d9808803c0e12401c500c03c3c208403495840e100c02c00789040300344503105035101c0d183c400342030203d50380240e02c42d0242c0526000c0302c010744402c0c10190fa980b00711100304040c980e10f440b061200580b0a801481d08080b0181c401c440000390820700c40141d500030005213010b002c800014000300002c990303940310141420501c1c3c602d009941c0c2d01064179031102d03044c00307030410080540201004000b40002c000056000340204090400000000307210740051140300e01c1000d11120240c0340c4e0b0010b0280c4030004000902e00341142e0300300085640300c409001c10f1400c1e28 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 233855449 1250 233854199 233854213
    0x509060c0d0e100f15290c121905030606070b0a1d03250203030706020901140307021624030f091a01030227060f06091008180d050904020903 62
    0x42c41c014050200044155000496416840062202a6540250a0f50b6480f45404007080140c4d0f194a8880075a07001d0700301c80065000406455903240101c102054550290b01030341510000740c800201044210000d41007140c01000b18181e855000c2103994503048101000144c000540203610b240c0c1c000007602c400a000441204c040c060124180d940041d250300008419545445403401c880c8200a2031040c9120451250f010030f44900a146004101680100c0d040c400e90b0f0081451128203080b600303e6a8403440c2121002f0354400000f01c050072120600b01002c00c28000c03060701d1000444000c03c43c81900541450110001d200c0c03021422201d503a210111000a425040c00c22030a0440f050f800380380354158010403d003100c41201c50388010740c004007815900500700078072544c4000111289100d09100b407010450724461000f1144d0701c1203c9000a910080d045200c84e8000d070003034a0710300302000301e00000d281c0c4c803240c0352404070100e44284030103c13552403e90010022040003a05840c4a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 233856699 1250 233855449 233855471
    0x150e040b25020d020c0d05030702100302041206020904050711210c0f0708011107030813020a0512060403020607090812030a0f0c02030a0e03010b0a121103120705100509060c0d 77
    0x410304901c400440141c2242e0740c00c0d04040e60400c81c200c41e00760110303200a02c484807070303460540e03e10a2a100a025110b49811041094069815a4001c0c49014890500c41c0214644030000390f200300d0a4a211b645000c001c140001d1003150014508850480208100b0034095066020540d90145c0c011f44540700b0004005464818050004081490710040103d1410700d05102e00f03440c0140a40c011030a824013000d404a0340c08400c450708105200c8aa01c2c44035400d00102c1c02030029900b000c1d80041030040210039200000a1080c41075020f5429a607050312400d4013180c84890318450b10040358048241d00640f4201080215003240d02c1801c0000c0a5040d00800003e45d4040075507240580c0010038a81c10b56604808903504154044008000502045001030340c84644c502801d12540846054101000306440f40d07256441c40090417030b424200d1010000c40aa4043d0108880314000d01050320503124550090b107001c0c85082024250036961160300701c0480e00600c1540f9041e54480150040b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 233857949 1250 233856699 233856751
    0x4091103010f0e0114090d0807110102070c0303030b190b0c0c0301050703060612020301180b010302161518050a060903120606090e07170601050922060306150e040b 72
    0x280e10040c1c80100348112542c010381e0031108a06a58000c05e1168010010a01000314452056030b0850420b8441901d50440440303510741c494080c500550301c000f80400600080d03080791b1007142d1080d41e090258011040500840214071140c6020300c0154400922448801c80d020b810100b0b017903821100d2803116030001a0956100b80c800b640800e43d207203018041142d100700508500e03e0b004400b98503551512130300c0c0c182c280e0701140904801c2d9490042481d40c1e8402e40480b40040d5600c2506c0c0c0d591002410002342c00e10800075518412440c100c0305054498682120402181d00403015003030840803510340c8400303405820000c134200402802c2c022842c296030302c610340c050545641d03044d03a85820b0600c00343d4101d00241208060000c070762101070381d4840942c182a4010000c0c40c00a442d00c241da000f1404680196110850f81e41002c0151481c0c2581a0300450442c0d02520082c8040058120f0303400900790070b0f006884111855034001000b0841c0c1100b4113410080400030803204441c0310120b11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 233859199 1250 233857949 233857961
    0x206040b03070e15090d031403100f1202030c0f0120010903030c081302010c060f020c030304050c04020301030f0f0c0f060215100b0d111603021c0c0804050409110301 73
    0x24441910100510001d039510601d6200c00e20004d480139001c010004145141d18060120202d204102601041040500c0b900400c0d042c50010341186485c1d04118650000c44041ca003c1d4042190408038005901c0c0c0070000300244040e0041c0280001c21811f1060051030811180004e0601c4250300000301e004414528141141049c5800060fa929061600030151412480c01d0820042d280060009000f03501d226802403580c2404c20790124500340c5090805001c00103014000b440c404560142502c00c0800158420b62042d800d950000c8404400c000c00ca0100307001c080c1031098031445042c001401b101c0b03282403840c0a50301070007245640b05840031096849810050050300540e407008018441c0b0a2050b4000703200c013400c02c034030500b0100c4030700b042d000380c100c44c0340c81c0d50b1195041e041c40c1e4a10011504520035840c2c150b000c0008e03a0501a6179080c2c000e01c3c4000d103507460801c5005061242d4070405000391f100002c00d24213443c040401c0090100c0790800e41e404940350381c004c001030341e00344151 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 233860449 1250 233859199 233859209
    0x307110d0f110712052a060d0b040f0e15010905160503040f060524100f050d1503050609060108060c04050f0f030a060515030a0b0a020714070603020d0608010e1018020604 75
    0x40c100c0348944589180d204d140d0481403410b030002c08444842c187e13604411b80c4d0428150401c002550644000054003a022105001d0f103100d04c1c003525900700c01c1c0007040114428903034040000060741c0e10399111044940403a2003130042141490b4107812148214011034105019004071407043c040c544907101125001da9081611b0944000d00301c10310b90345800c643c00b210608440d019690705519070085c013410b80c0c1c0440e07581084000600f06403005881c0d0300c06190b04400b00161440603840b0318219560390400e84440780e15108100001503008e00001f0181d00c90700041105504140c9031034180034004179140d5026501c0401c0c1c2c80f00f5011034900300800d01c060b80c019080402e81c3e0070805105240c0b014410820750207070700036a04180128950604558008940340c900581e00c408500344080e4201c605080a007060160400001c0d03880d5240e0060041342c081d407001080a0343e502c0754481c2c220b43e0f0201400d41ca98016800c454514522548045c0b2816842c801030400348100d5800101c0346d921581013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 233861699 1250 233860449 233860453
    0x60e01020a0b150f0303090114090a0305060406051b1305060304060e010e0703110d02030a08031305030a030b011803020f0904030203040503030d0603150507142803020307110d0f11071205 82
    0x1282e2141d2a04c00a508000c0c001035001c1c610305808240002d20700d00c000b0741820803066001031030118a0302d841c402b26000b140c02205490329130910740303030813000341c8420b40751240c0a50a80240101c0c1240304001c0b02c60103030041c8e42c000051031501d4248012600010002c1e02d007c0c1e41c510124030b99800c01c0c0510b101024107035020700b100740c1c118034142c500910003407101e900408011840c40011388000698020064115210f00d40f00d03518460080c0c41c003141490000c000740808030b90560419090f030001d0901890907210a54042c221000034810b1828500c070180d841200420452014201205400d81203030103481913178030f00342d00c1e0b001081c40d41e881171100088542c0d03682420424003d046004100580c080c9000303011a0400c40e0780100100407407000030207110300020340b03400303145030300149100948440c0419a00002e40010060001d400840318107010400ca550b004802107000b0030405d102c2c50a9485400309130742004021514030610554000380d40c0b1030660003180d520b40091901086032704c2080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 233862949 1250 233861699 233861731
    0x181e0b1302010215010b0409052d01030b090d140306010207051e0112020408070510020304080d11060907061e200a050d0302040f091e06090c110f07060e01020a0b 71
    0x4002842c0000c408501e40504d101da40040c02503029130004c81c0d00302d41e080100820561070700d06a083c003020b204a06180c5a07109602140094000c2000542c1264060804c2c4001c0c1d9503040340158481c00b244800e4000150081c400181940440000c1c5422003410300c100c4000e641c90b0000300301311080e04040038143c619014854406580d1103141906201c0c6a080c0540c103051074050b41c0796845845000f61407044121038105026a442001a1001021100c1c2101c0705004c5209014100741c03081c60100003580150000581a038100150441c100c503800e684016601c1360f5040d80103d0025403500d0002000181c41c1c80b005002c0c5914072003c90004071001038010521355252140c0340c0546c0c46001801d050060100b0481d901e650718404048861140c004503141c18182c034007066640804010b000d14038030341071001c0740b464584d0348a801c1c5034146803204140c00505413445581c0d180800b540365850351002809201c0c03503110b070341c0c0d00180e0401030040340c1c03003603d0aa541800d008002c5038003543c1801300003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 233864199 1250 233862949 233862953
    0x100e040504081b1c0503130812040201031d0601090e0f010504060209100206010e0103150b1e03120403020901090b0f03030d0e1605060a0e030c0d05060f060103181e0b13 74
    0x3c02c903041c0c1071202d000788500300003a005000341c6200c40d1282d00a02a0110004c3c005a80300c2c90600b11071544050481d5031501d2075405001e000106440a070f00207407816624034100c80c443c03458540036002900c010001d9a00e05007529020706072610380520769005d8a00001740f0a6400d0003120b0040f8410701001d6100c901c460203202d40d00c0325082c58101154040340c01000784601050101d81560341004c42c00124034880b10b03603c40644200c040c0306400000c8031b803074201c910444241e060860300b004c9040d11703049040300c00c1d1041d15004e5808042c2d071020a035001009043c0c5107610840d00350b02d010b00191000c8075448e00081c10341d00010500070311180c480800310800c05050000329801c08250450350b8845041c90080b800030302810b683c0c0ca0902074034515644203660b08001b1008100e4000700810b809100030b03e0328940700c00090714040a181c40c800c001c070f821076000c2d000f0070300c40c07208104c1c41d0f802c00d0980e52582840044072081c031508070080030304803802041d90703032449030b10840e821f00480b9801d800c2c0c0c5c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 233865449 1250 233864199 233864227
    0x171b030c0d0602040914070c060b0303042d0902181c0f08030f0c0a0e0105070501151d01080303370615081f050f1201060306060f150509100e04050408 66
    0x172100c4214031b0460710208108640c00075030f00403901da0485000106221504042443c40c0304640000034020120a10340c070034a0340c01c6104d134842002200a0751041965440f8030000d80c018626a40d030f04110185c1c0302c0c0c085042051528414640303040381c000542d0403e80368100100c40348441902d0031940001080018584011069085820000201e107440854503004085141c404030203130401c54001203410501400b500702080395a142c2c0482111a651902004640590344007220b90320229840001000000030054030311901418480d01d1060300000c40821104065400c82d080102d00c2e142c0e6410f541403c0d10811010304024016000408111140a0001d8a0082070388085001062121811811b80c0b1550030458a099407103d034808039140010f60f011640540c4503802d580781000000900c01c0300e8008104a4200c0c0e08004d02040d00c52a100015120f140060f001007074041080030441d0a1100036941ca4000c4c501d00f00c6280d2490f44001801c2e02e106507000d4a44540c0885c0070400c40b404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 233866699 1250 233865449 233865461
    0x60e01060c1b08060604050408130b03071b0506012612040e010819060b011704050601030201140c070b0f0c0f060a060b12011a070b0901060807171b030c0d06020409 72
    0x210704030042c0501d03281c1c03401d6031035400803d284c2c051502c400200d0304100800c401d443c0c10708040080500c14588603064490990012245407000131207030360420780d07400d1800c550885c1940d0440d01134031003070b82020070411054a0601102c80d100a12a203c000d1401003408140e2504c1041007040303980b9840c000010b0074080068100c641c53390810f0300d070300303040e0700c1c41c503a1100c1c80300c0e8000c002003200280c481c016641e43c4d1040d01d000001d40604030802003003150120304a8141c9200b43c807104c420070b5680c607141c0f0842c018054a107074207502240040c003800c60002e02910110602030703007440c80d000840c85000e040036203110710108903500140501c1a004501e009030009071825041540c2402480320782d0200120040c07250710380e06010381d642d502a04042c0c204494106070814591601400d118251034024a1a481200303c503000d00300d00400e42d941402d1403881c50603904001080c80c2d035218240041c42c041600c100e0b40e8107200780960701caa2a114109101e40c403500035400140c0300c6140c15481c1c400d45039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 233867949 1250 233866699 233866733
    0x9160b03040b0c041404110d0606080910110708090415080105040b0702031303020108060303120405030705061501090905070c050d050d06050d03170c040506040b0316080f06010e04060e01060c 84
    0x183c140030034030207501450103030a0300030400c950125002143c0110114984904460040d415086c8a03003c5000c64000a00d580646462022288901c40c943c03990710466003000d0302140c011904200c007501003500034029000e40500100002801102d400c0e1058080c942ea6003d81d0207030351180100800e008070300103040c0d4042e1603800511310340600d0102d0001d11184500009050046c001d0203e08161010000d48003100c0344454070751617609003810480e1b520381000303c0481c1e03280700d008001401d4012050149121a1068440010b00c5082c62001c1015140052444042009150f90b10000c208100449010b4524035250b1943c1c8001c240c182030305541c601d400c040d014003022208200000d500480c0c0303150560003180d0504040e22502d0070041c00d403250340d200b6a800503002c580821a60030020007540151300304640907a8001a02c41c069542d0070084503903500012503040015060b5005516140b6140801080050396a490300c075098000c1038203030030400c0065500c0d03a40710300b003242c0c88100f400004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 233869199 1250 233867949 233867971
    0xb1023120106050f060d02040801020a271805060103020c06040b060109050d1214040306150609050d0203120d02121501020d050c0c0d0212010f051f0506030c0309160b03040b 76
    0x150612021a048403001345040d4010714000071a0745c08040705a055501810103500290359846244200400050074056031405c848840c3d0b410259502da008071080480c0c07542c031618280f0524990b00c0000800c0002c111034181502041a4000c0400c288412031280b4440d4519101b5410034200051901242e50091070203650143e81c6c030b00100750302c000700c0384c2c05005514201614030b02c00c210799040c070301603a80020170542c1000d0840c000384613004900d4040e15000e036141d90341c0c1642d4404000d0b8180d107220010f501074212010001100381e114000345005002044054500310000c2c000302d101030383c1101c09004400c00000c44106a60b418004000340c0e1b02c862030880c1c2845040c0621503140c140d03801c2010b1040d000001d0680464881010300da036071619940003042002d0407485000003a01d411590078404002c9005242c508000d04070b60304040e40e0014040328250b075203c68140b0004e50010789107a10741d11400702c0c0f201d900401b0070541000b81854000d91600e0381400d140c150200c50000c5c0000043c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 233870449 1250 233869199 233869211
    0x190b0a17010602150c090a030803040b2211100e06040e0411031c0f0c02040c050d32040804050a0305071a030f0720010f06060e040902030a0b10231201 66
    0xa9140e0803603da0451030325060f041e5035140090001d40c54411f942c0c401400f0410100c100010302801e05440c1d44644641f50005055441d4201d031003880f140c01a1008040c000180400506411300c034010007141111824400010004440054a160050340c4039480300c0e0000d000300710402203041020461038105400230300b207205180c00c0200317800380c40c028114100080c1000786640f0030321500e102000c240e009041080151200e042c020b02c0c3d6070104034501130003418100704c428440080080070003060f1083c4410141c00f05180319444440402030310541d0b44002c244804150f80c0d031402d851000861103040103202c4585000d04e43d00001c074251180466002e000d00403c104410a0f05c06035501468510b080c5e42542c40746510002600f45e10404c2c503141d0762914160810310400c5600c40c80980c0e2541e00e40703294001480040105850882000a401d0b03002210110002240b0001d5143c10000d07001075070710503d8880308078208003000031100d00221104200758250904080e0f0381446e001c45ca030b0b0006d0000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 233871699 1250 233870449 233870473
    0x60e010c2106030609030f02060f07081b2502030615060409090206070c0e07140715150806040501050f150a0b0a03021e0909160c02190b0a17010602 65
    0x25069041240c0641d18180e20600560400a68820405154807034001c0001c00201c1c03d005008440175400722000d445450301041052100b10b45052040300d041d500c8200b180d80300d0342c0000c82e040603100c030b003403606c0e1052100b280c0d26000c0c0d944003405040c5601c0780c2a8003000900425203494000fa0250050440d80748000925454400c01c0b90141c0b1001000843ca4682c0f600c003003141c5200c1e080c80500014440840840d200e03910303034403180c020411669004901c642c500c00700b141071302c100d04000703201030a018000c00ca00c5c01c59401c0406a010704880356601c50b6903410b5494113103501100c04031041c5c0d41d50003c00c8025210285100d8000c0b01d0040034040f0308048401045003100c1c28050481483d030045400441d4520907011901c541580c050010b0702e00484c41e886031059000708010030300c00c406034800180700c00402000400c0e003220036a50202074020907001d1010446003145041c01c410380821011503c043c0078001051260451b6640c507404426200b116514440186c10203401c41d000100d00303100b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 233872949 1250 233871699 233871707
    0x305060f01031401051510021e1b010c1104180b042102010b09011202031e010605010306170613111903061d060c03101a03040606060e060912010212040b25080c031503010e0109060e010c 81
    0x33714009840004400009030740e8000b01d0017142c0c01c01081078902c0010041000040c046407441d011030800e105e51807030450401a0300b0b80d0b0341c0307001c025082070b5030100400200e00c5000034111410300241c165001401e0140100b0a518803c070400038051703440f003008022035641482800300905030a00142280b18410150544801c409000c00721420000f0b0342c10414070161200000f5001d0004150401c02c145800089481c490329100c00c0ea041c1d45401a003204a04c40c4c0400a94a0b544880103418103661300705021103a604094001d540d250200035001c1003252006034800c0049000c8144540c403403a15181050a5031150b401c4002000720240391810315440300030a8501409044031b51030700b1030070408c015178024040d4281d030460300b01d100c03001d2006000c0c1a4144a01a0b40818441d009440c00341058484844150980388002110000001c001c1c1c580d18002e1a04040c81c441d483d01d6008406e00000c0c00d4418803081d01c11107035501d41448040009034411300c00004200c0c00280500000850b0181c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 233874199 1250 233872949 233872973
    0x60405010c03120b040f0b1503040804030201050a110a031d0114031506070515010f0801060b09010f020a0212030307171504150305060f01031401051510021e1b010c 72
    0x900340b020354100042d042000e5009103e20320400345c0104056109580030030082c0840e0441e070303409129111003400c0381200e40800c42c0c3c4183c3d0044003841c501842c41d0300440c2c4030740c07108040703408205a680c015418000140400c0e24180c0c02651501c10342c480c1c03a5414440c0044000f041810b100c3c0e400c1245005c40c040030150ba070311017402005408900d90f54404906244107500d001400d038044d08080e6003043c0701d180505414ad0303501400c030354a0300351152217541c01c0351518003d43c240988140441c4a4640c800d044180740d840451040e0f503011541c0b9800700e800796194146c20030b4250000300800584643c860910030b41440b400d000c55405091000c103d941032640c0c038225600564982c11240700043c4040c1e2100b004640c44011522135180110200000716420700040b0303801e4240341c070510403400050041e05e003d802c14a1021500080b00010000040040000d031415405131050700e01c21032200007080c0c00174100d03410150045c291060020288065000d01c02d60500c030341180450082204020a6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 233875449 1250 233874199 233874203
    0x108010b160605180307060e161d0a0b0607030906182411070e0601030b0d0206160606170109050f190803070203040b0f070c21020d080f0307050c0c060405010c 70
    0x1460b5224020300c1c00e6010b04d840d104040321300c80000c0c03607030400031181d0045a0080505042d101105026000d490350390030148180c42000804101030442140000b45082d044505500c0001c0c1205040000c2a071580040d40c003a80031030356001040001513040321001c00345a1140030110b650324140a83e591036104007542c140e030400f210b40d01c4020028083d0001013017503113024084519640d0340e60501d0405603002c441a600003420462a2074407424488146e036101036004100c0c07800c00048041240d650400703102c0c01d5a19a454100003c0d001c1c81004c00540c0c20b41510002142d42490b03414000e26005416080c030b1965841300300195040b035907040c42c80320026400b18183e40e82c2c1d00c40201c202d1540c05943c00c000101c079400a8100746280943c00108001d030710131320042c580c49664101c07c01d114810300800d06014805000060300518200c07468003030091050f8100d6081110b0b04c004100c0d079400880780b10340407420024405210071800c10600c54509000c03240c0c5880d05051000080c02e40003141c0700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 233876699 1250 233875449 233875451
    0x10b04060507021512180721030201110d021e12040816020406060905090a060608071103070c090b090135010b090406020307030c0e0a15140705030403020108010b1606 73
    0x814115600c2408008120640002290f00c540b00c1c030001501c5017100756003046018120018445090f00302207102400c032489080d105448059040b500320000240c02e40031411035689044c08041004c2a801400701d803034403c0d60050305e0340e0740103030700c400b03110180c18001c0e00e040070501c049030300703044500b8050713074803c1d0310841550303e0f02034424540145420f001c078020f51150411901048450340254400e085502c111054600d50f29400012012030704e031030081c01c0010b10482e00107807145014421030720300b002085003100e18003a61912110f030308102c0c9400036a9102d80716000d0407101c1c07410741000e41c05480911445030921001d0203c02c69000c095016001c026800c0540b40ea0f0504da003036102c0c140340c100c040c0c0f07901c8444c640f500c3c004000390310454011020034900b00c1b4050585100e550100c400c01409045014107074100f04110740002d11a1019400b0060440e00290a0340c1c001405403108510600003903031558154800508048816000001c00580c00c0c03041720640c483d4242c0880070280c01c020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 233877949 1250 233876699 233876707
    0x603020d061d0303070329010215131407080f06070c030e0a0b0a030504030210090c05090c13030819051c0c11010c12060e09060a0c0504030c0308120a05010b040605 72
    0x10704451110034041c2c4090001104004076581c041d00540701180d0300550300170085800550080c1c1c42d0100311091401680940c0d015000703203203180000c41d0468038904c5403821008a55960341003600c1c40c000d000d0841e8004110030020440d0030440e81d83c915050740c025020302c0c58142ca00501c0c9007040c540c0a01000b44840469440382c0343c24000704060442520003030f5540e00310310000b03030141c0f00c241c03022001031241e0769000200391003900c50301e00619400f480c0702040358900000c1041804d00a407810340f1201080140202d0b0300d0150808100442c4580e40342602e0380380100e5050800c060041d030380c2c42403000401c20a0078200500440320074000840d02c0014800c1c0402200711060510050042e189604c3c022034245034981000e040343c00061440340500c0300a4641c1007002a44400303032a01040c0340e001d140410007464454000120200741c074034041d420700340c1d60b41340c8183c0c020740c661003034a0340d141c00a850351000c00004001a84080180402d024035407500031249503500c580d2080c2010050081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 233879199 1250 233877949 233877971
    0xd030c1b03031e050f010b04260322080709050f0711120f0c074e08040806180712050a020909150114030714030f010504050106180603020d06 62
    0x80d00c402d81c040035400c3c40d69480d042456112000340003d50b4000520610b003030000849203450b1080310309039030748171151030b0004e0703100020a0ba1941c185c014180e030501060142e8072040f003070310505d00741101d048800d40c0041c519044846003000c0c110307081b0b040100c0c20312003080180c1320380c07a0348142c00500c81e10303040380c1d0300e80c5140006041504003c14019114000a51355804000700805001d2510341038040d01d0a00380d0b9803558114038035500c185408910050480b4107800c01084d1403c3d00b803841050107564101c07903174142030820882004c0302101c48006c0440c041c40303480c408102c0c030380e4800340400d9500e0b141c03828001c03100d5031400d00d4803072420114400340340d80041100611100129543c0a0518002410900a42c58440907050313446403003003541c0e000008400411000045204c2800380140981c2030403d00c0280c0c15000351035410b6010b120300384000d1100003003440340d40d124a0096000060950800c000c1c00e920107034241d9810302e11401c2403414005a9107103c542d43c44181c1c0f14400207144a848 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 233880449 1250 233879199 233879201
    0x1505060f06071406010e06040e0f060121080408061e07020a02100905130204030228050d0218070c020f0312040927050106150516060b0f03100b030d030c1b0303 70
    0x72107490f459004010000030044401c1d070200b4065035040b10240301003140220015640c01c00308001c0079032544614010084010180e852138800b035550740e041c00050b0b55603241d0b280d0660043e840240c1c04d5101340c04000b0380b001e00b410f4880280e224020601070500741041e00030f644515006006c2e120741c0c030341d8262088013802070501784000c20010300382c04441c0d4420188000250045d2105a014540d101c03496249900f07005140241100c0d101c807208901803d160520041081c0c8140032600040d07101001c080030017291851501c030711b000d592912000c40451050224914200703004078081e0b40200c2c0078000006043c02502d040e03032882c0c01c0006144400440829410041311024080d41181001070414044190044800c1c1c900c1680c074460004070702ca10440e464443c0400e41715440c0400d030302860000b1301d15003000651803030044c03010000d001148002410701007603404203000141d80310300300e43d1035040900040e4a1017101c0d080c10070248c90032140103080c00803520441d48001a105010000309802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 233881699 1250 233880449 233880473
    0x306190e0a0308041a0c0711011b060e120a17060a030f03050408010c0504030305040e1003020a150225030b0c0f031008010e07051309080c010c0504031505060f0607 72
    0x61001c603000c9820600b0080c010b0a0140c8050b5001c0e00440381072400f0a4841030003074040c6200c443c1040c40d2128544400001e00f01842c01c9504110709030b0440c8410035805812040c0250051200085602074243c1183c0390980d0140400f00000050004a03061600300030148010a10708030f01041c20740e124030020300c1c00c1042c0d40004090860b000c00c0c00041c5540b01001c0d00a46146c18000c00035500381441c1601c0380d0007144030040c0040d508000a11012100c0000503070030801403858004480d45980c0068001d80030707500f16400d58481c0619621b5001c1d8100030600100910b85500303035841030340300400351802056010150400c4221000309111701d48040440720801c440d15a903d44a042036840d20038500100c1c4609507556080c41083c183c500c0300414034900311a4010015000060b203000ca08002d000c0c20481079404079030500014940c03404c01c2c003400c45034480300c3d5245a45c8070705624014000d9070204202e59641c41c9810100001600c0300d070b440580d80c003030841c0e00c581c0700d00c03c91400070b403d00c1c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 233882949 1250 233881699 233881721
    0xb012a0203030703030b030615060703030c021e0c032812050d0203090102040906150c1403040f1d010e040c0b0306060910020f0d03090b010b0f1201060815060702030619 74
    0x100002c3d0800525506501c0810700c4101202a525192607076508040c020050801e403540c011410403290300081d001e81d00c0a0b603203101c0360042c2d4441482c40d0001d410941a4058100490341003581f04010764642405003049a14001004491201000c54004070700c10b881c0c0401425407902105400449000750183e81c0c0800303c00780b080d950317132030010700d424040d420510611075006d080c4000840c00c12000c4085503513440c46555585014007050f103d48480600c4805e1a445078002004040381e2165040340c0d1801404c145c1c43d8600540000004280003450141c1c811034000c0040d44c10b2000240c40410514100d45090455a4807911810b000820758130801804561040300180b4520a450300400c0d48030402d0030314000d450654034042e41c1a0192b03466018002d1920078903e00503c0104101800f4110300b040303c00c08039040450064a08814410031b801220200e1076840401401148540b651042c01c03d00342e071100e003400c40603400300780d480034017030406e04040310f446420708003100c050703800710342501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 233884199 1250 233882949 233882953
    0x303021615060b0405010206040624120b09011b11161502010b0f0109030605100e040804180b092706010902070314030105100f0201021908060f040b012a0203 69
    0x12860300011600501092076691030620400291000c112402e940446906030082c100035070300c590340d95001b000c19482c0c40e4441c414141c5e122401203011141500a00400d501e00300b00500e090401c84400340005055088983c1080d041e403002118010005500f21440e0500d2046180d01018107420540d01044141c030b0740304030400024031203100040c003000b4540300350000c10400c01458180056000d061402ca8041941d5240400019215a00603039000302901c80b414440754607503182e005100820b0320203444000c0f0120707040c001101212658219a19402c40401084c1500c8000c07502e0010000d1032219590008042204100c2031748281d42c956000e150306070303142503031550340f00d8000350002401500004c0000724244c4684008404403416244001c2074010f1f4180c2244088480020500b04c4a0455400380182c0c0e010000481581d245200c3d1529440d41ca46008810700500e803250a201302d108a0400c108040c143c3d803c821100b8940202680c0e400041e90340001e90b01810081c418025014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 233885449 1250 233884199 233884237
    0xe0a110f0405010f0c0b0606252f03070b1b0f011b0c02031504021c110907020312010b0a020c120d0318050c10030e01050702060129090409030302 64
    0x1a8035400030010b980003600c0d2281c4c07102090304201c40d0004600300003440d1030004004190546007900c080c1c015103803034141c5014141107040d4001c41c07030f07010510104e4002403903120806c444211503003925581c02030b1074004001c01d48030000080d650382c0c2611580c1c5020307034001403105596004002c0c404844090030700700c036240d52144540c0b500070120124003d26085c0c0c1c520b182401c031032040515065240d0010300518800100c289000504040604200d83c000c036201d14070341184c04828544030102c2e00500200c6e9a4070b0000040c03240c0c02d07000a20710740842d041040100b0ba9403518a800d070381561881852140c4940300040c042e449d01d640c03000c8090b4428151441440300b5030001504403072f058000d907021b102c005014600d000008146690060040c0c12808034580c1505180d0f07943c0e042d503811031038081005680c010312030742180c1c41a00c0e0302005070840401401450390040910030040c0300b500355002903501805290311640030b000b01c024030403905c840c265002d040c803039010340711040c030000c40401c21 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 233886699 1250 233885449 233885467
    0x15082103041419030f0e060708090103060323060601320405190f1212030c0507080307080601020c032d0703050102040e0907050a060905210d050a17010602070e0a11 72
    0x181501084044001170004080310f604180b151244c60b00ba000c02500050414480d50742d103500341d40140c01d910f4100350717580700e002010034450b0b8440102401108844011a50398030308090806500421083c10311100c0000e9400f2844006800060b140c5c072154a060114815820040e0b58403945e448168014460900440a40c803545030605c111080175481c0d46542d0342da154a0261518032880c05091522900c0e55008018066000810411b0181c64414600324240d6900c003069042540c54a0001e00e125040044650f01000800d8003031004600500000c520b1103909c14040268481800405070705200205044000b08882d0015592003002551203907240e001038040c2c120100e031003880c64800d252001840781040e00300c1409544003565055a240e003844240801e4062400c1d030020051300d003290140140405120300e200c8003070981d95280d5141d410500c000c00300402e04481341d1109070f0fa00010003000f40c000965400304c0396240c05640141c0d59150b03040008203440340034411061400100c3c3e0b40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 233887949 1250 233886699 233886733
    0x5061c0f0b0f0d05030f0d0204121101020105100315090f060219080c0414040902031005090313050603100303030b01110604120f021b1212040306150821030414 70
    0x140284050781c40c2c2c4100c1d03544604000340200e20f004064400c0d00100400000e083c5000c00030a1014501c01002d854142d54006021004100100a88081c0ca02d03190702801583c0c207004064103c102101d00b402c4035402c2d40c540542c4443c8440105d108503a07190b44a8042082c5c100d180840c03650021003c648075540c11007082e0728440f00440440000f005080020800000074094609035080788291001d030703c1e086001d220003016101001daa040c41010702d60310740700c1c9881c09810300c6104004013562302d0b14a0f440d174001038a0030380e0300642c2c4207000910410100500200784079049a13050328003c5074043d101300042e2039880b40300348442a0b5004840421042c0020b00d01d2a400340d180c9565803200300c41c1894001c03038451040c807001e29025407458240c44c117280780003000f9110308410f44044d2020215004110917069100754802c45034103440b00c1d44c035440c1d0200e8000020003010510087d102400b61000c4001510659414240e00500048041800c2c4040c02103031090807041c0e10210f44400201c111840c2c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 233889199 1250 233887949 233887961
    0x91401120911010f0804030e040515040e0706180303020c04051008030a030501060e09090a030819060627180207060b10050310090c052703011b02190b0105061c0f 71
    0x6021404c80c0e202c1080b00340c4030b031211501c926055964801c1455078001080081d200240440c54200c0340c185444000c0da0381c80c0300d10224040400024080945031010252000610350387c04401408e1600e0104042174003c01e65202c01e100840d000161541d514039400700ba10a00d800045243c070020860003113461f0194049416150030317840380d6442c1c07040c103030170440511021661001aa0880f45003000028056602c0ba40c001d45011405042c12500c800020216003696008100003a00482e4040d4a0361004036101e9000111010350300e615428245440c468202c0741e0b81d815501540050b8840610a085e440070800010061000c3d60130482084010020b410644a030704500d080d0410000342020640304002200b206502c940341081c803441c8400343c00452030310702103500c00c100c0800480f066800b80300d1004450160603081b8402c0c114414000c0c504800403545a100c07400b0490b20705c0100c1c3c02280d206046a10841e1050b41c3c49a100d202c0354211040c0500502d4501e0800401c8119404203030442 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 233890449 1250 233889199 233889233
    0x4110c030703020c04051e0405120a03090b0a0207030e060a0c08130501080f06030c19330206010f05040e0f06040605090c0a0e0601030b0a0b0706050f13030914011209 73
    0x8031000320340c040410041b01c0c400e41d0240c0742c20030100a401d000280080000d50f000340501d0958880190301d01088902d0303845040d000000a0381c8445203410848503525054001900100440c1485241e80e4040e00003085100064803941c00031500c480524030035206401e102ccc1d40301c02000c2d00c41d00709010080c0520381500800e40400d80d10400500b5110400300300301c0c1b04400003401843c0240c4c0b100300340070860446035107a204804002c80701060307082200801810400420090055440c0707001c8a9103402c0044920003011500803200401911801c0315040c02034800484d400030346201c140011501d0b116815045840c07030f004081c100000d0000551103507105d403140c10706842040e5241000c01107103200c0c1d40241c04c10740340050007184495100754880e101c0b900003c1d00900e02d0301c1c1c40301c959684035001001c003154413a071202d040200350003800e480307a90804600800e00c1541d26107a50003410740a500c1c010306816006904201603142c1c841c0300041e404011483d0304002d1148170341409060044e141c410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 233891699 1250 233890449 233890453
    0x9061517180703240c050a210b0303040b0306100c03080f0a06030b13061803050726030c0d06060e010503060d05031c0905010b06161704030b070509030f06011203080604110c03070302 80
    0x1004031706000b001140c40c50401540c0d41704900c0e02e002105100d0318080b400c00c80c200c99075010642002c0c1c44c10801440580130040e9801d8a9181800400c051807614001003410041989a484000307a049810643c0000c2044401001580c910203400c0081c012a1b0001d00202040420700a410070b07180d00b840e0b58180100f00600c200c4404800b070910711900d1860080c009802008001c1c0841d00669502e840201a0500c190317102000b000018140c0d00140d4514807030705c40000340d81000d0300710751052030001c0445080c030324041800200040c140703000080044ac0500361102100e02004001d101301c44030801d100044d056490400b0038072000408108408549030743c80d054010711103162000c103455400d03401009a07600303148242d403119680d040038115005120008d002c040005644581002d2180b1030300c1d590380d03413101c44c1071080600d00b00c4907100e012582e402000061000b440003003094503003e80c042c201a582030301c0e42400300f0000d006074080c14144803800f142407038a0f408003000408a09004c0e0342 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 233892949 1250 233891699 233891711
    0x506190212071a010801051501050c15070f0809010c09030b040c05040612020102120c062a030a23061315030f0b010e15010c060b04150906151718070324 67
    0x801c982260400d031494030104541c3d108d405410740c071460003000c048610b42c1c19522110950203405000503004e841040201d9143c0e002c0350300350f40e4003092184d8014032440080c8003034510140e014201c0c0c201c5000103011003021f0390006060005011b016801440080c00800001d03945501c41419895144000c90040c0260500d407910704140d4425100108008009072580380c03900c0c0c00c1110802c1c00365602c40c86500041307401650282103440611b10681c400b038030100c0e246400d040c1d4150042d40701b00f4000420705224082c800c0d240c0380c07500f8500b10306200d20b0000500d000440ca441002e085203a0006041141c0c50b25130f03c04001200041e036048550710700f40c3c0c0200761688140c4161901c50300c0e00c410300158007500e024020442d00e806c032114211010b000000c55205404038014490b04e1500280c0043c0d0301c1e00e004000200144007203501c00c07400b6103415601c0c180c0c0d0103101020742c94050050150002c240c1c284c2103260000b4440c00d0000d5a01c5078800c840041c4c1d98004400c1c070180d903034641c40f02c289030103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 233894199 1250 233892949 233892959
    0xd1a0a1d01021305310c120203071218020307080d0e10121d060703060f0501031a24070506010f0501080105090403030c02031303030206041106040506190212071a01 72
    0x100a81d003404800c00c80c00120396040400340f10100c0d10b81d40304215040c05a240704012417155686078115140f000401144a5103030f8078001c0d00b00d41c1c0303506004420a00c10410441c2c0d19510600e203060040704404049505a500081d020440b00c00801c0654903014549000802203400241d0a01d602c8280d120040140c442d8403c005030140c50907179400100b4201e07003c078108900c5540c0301d0f02e0b101c0d400300b00f01341c00c1c81d111820032403505600312410380100390354803c14842c2c10b450440300b00090009107010312158001d004c601e00395403821114280119400181480d5120084d1403110041c40d02d05070070781d250b010714100710361360310020310a4200707012040401082c154811060241030305c0001d0000d54060703d80359411070003445a1202d4a0450005000306149000d01c1e40181d4000c3d4040d0740107055a08140c20492040c4400d0704543d071061380200b008100c56216482070700c26013024600449a0628040c0e020f0b030a0540c0b2000c0410902000103414080211005a01201401c2c245104946030307264 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 233895449 1250 233894199 233894201
    0x70908010f06050a1a0a111507171f1a190503041101020111032d0c1e0403020f06030406020405040f0f05060909100902010e10030c1803110d1a0a1d01 66
    0x2410f645e1280d50411850049900944804a02c041341c1e400316950102c6581040380000b00030344a40380090702580c0d510744c0440205070529001181c1c840e80c8001c151000c0b40e005900c91051141c0183c06401440003100054800700b640c4415101c1103c50002d0040303914020320707550080303070101c4120070204d810072401e500c1486544101051324403450302c1c64031103202d40341c040702a17102e0701c200544100b11040d0008040e60350560142e200c400013a52660004c1041c0c1c08500c00401da80e610406090104101580d640c0800c0c5000000989500c1c1d90303078465082c01c0b80a489250030036604641001804840c015035076000c1d6601e403c1c4000c0800c00303600c9000070401e40b4035095076080c3c0d00340d00860110303038848190350002d07103401d00c1410000c86031200d14001c42d003c1405901501c01080e580c145002040e500941a01d11807205140c1d40b04500b42191385052450140c1e0101c18022500034074420104030210701d15002e032010203111994a45011464100642490b4040501c110000303120784c040c084c81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 233896699 1250 233895449 233895479
    0x9140a0209041106070501060b09040609050c070227190b0607020a1406070605040606030c080312070e0111010207060605030c011403130819271d070908010f06050a 72
    0x402446141c1e02e0b22151600c20360703d9500108658020000c101c40d000140c3d0900c6203900903d80c41001c95110201c5004010844005900101d4280e04040810004260f8901100d42c4070b541100c019504081c00e00c85050403103540711516580752030070824441040b0b00002468aa006990001d104034076045007444014091180005d40112030a20300b0f0081c61941c080b160300d068006040c40c0c4c1042617545402c01503400c181d83c10b80380c050f034910060080c008088c0908003d00030340d800442c640301a00310340b0000e03400003d0000c0c1c1003000d20b600306032345a031180400c642c00f20544c900035929103c1030b00f8400300034070981c803985100344110500c03d034540d4011203400c0041071194010b181181d64000b009040020442000c80e01d81d0000c00c103504144141d582000800f0105070303200102c0b8445040c002e90640b010b0711401c104180c0fa10000c20201e5051500c041800c00c0c40c0b015828540c65064059500d0b620941066000e0350034199011075401b600d51211040704c104586035030201c1d50b2640c40e8404000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 233897949 1250 233896699 233896703
    0x3140a2003030714010e010c1e02061308183c010c110301060b0c100f02120112020a08241f1505090301060f05040b011107050f03031c09140a 62
    0x1400050003192150341d100055030b441c240041154120418561f0031201040c8541010450b000008808031040070314000c100800740c0002c0c41e65040c4010b403941c1c01440780a00820640c0300050314601e403007910400d05000d8002402c0c440c0030600b00c19402041d51580d41814442c0760f880046c034446c80c5c02107000340721408010b840b890300400164a660b2018002c0025054244d904c50307100046209489005181071400f0310040c100240c40b5030051410394150401e400003103801401036810426030301c984c03641121010303030070b00040541a1012400035401a4031090703045c010a88031440c100b1030303407005e07070a03d80040c5514002692030743c0510400c0c0e000c441120030f2020900c1f90603c110b98404013813115600380c90412900b00424480040e007510711540008800c114404000c10030b6060500845041c0c84090909075595105901003a655100e03a02c42c030f5106084144a0048030f4a0a1040703904208250142c80304a52110b0680000340202c0c5000300e4040f00c072050b180984084c0822403000281d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 233899199 1250 233897949 233897953
    0x506130b0105120c060403030215090303010f0509070c020904080a03060b2712010f09030e041e1e0e0609060903040303140f0408010f060f09090309170703140a2003 72
    0x203402c00051112100c1c01c0c0d41414218031460860300910783da079101a200940c4244d00814840c68407248403038a00c00080e0080c1d00692040c8011b00c514883c000780b0b0701c1911002d4a50154668503e102260310507010744000e500892001c0502081c03000c1c0030010b00710b000b200e480501000c2d6603440e04006500c2a4841016202c0310f03149450a550113541c640803040034003c03d9900e140c0050042542128051076140b454565100941030400d45c008a1403046684c2c2100e040041d207603000d6814280ca048210380c04001640c2c0c00340c9015210103c9a0070050f1241c44008101795058400c00c5640c0c1d884c1500c1206c0d85106040000c4c0707010500004442c241eaa0507075400700ca41041101e604210b8000d07000c045c41443d410700011503410b809115580b8850321448002c10224640700c000804c050142c2c011111841c280449a0003090b0489001d03401ca909131200c502c2048903007002c90741091000d07000100915031980106240c4030b0700080d150351040c01042c100c0000006810500300380569009066055 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 233900449 1250 233899199 233899201
    0x3030405090a1a03030c0a0506010b030613090305040f09020c010e0604120c02010509090c09040b0a150e0414090f0c0102030403031403070c05060a09051c08010e090106030804120506130b 82
    0x1040940e00141001850b02010b03d03107050542c00000d0658200020401540d0310000b00782d02031210030044d003401000d080c049075165041c08800719408010344680c103181c550303c2c3c250761002c05100d002200c0080880781c03200180b1a4440800358040d50040c0e038520300560826100e414464004525940140c0c2d03c0181c4d5007a0400e20303a015110b800c3c5a0301b080e810300c4014010a000c40e2180c0050034841ea07911500d20340d8800700c4004110483d5010040c0b1805442021b0080c0540076001d0081d02114519007049600e40c014a030010340540030162700d0b602c10b040750200f403001d00c01d80020705810080b06070095403425074051004a82d207001d288030260000310001480010016100c1c0255008641480c00032a803810684880c0d1800e0b00549242444075520101c070700c1485024441c042c40604c03052122941c103000a1001021102c060140070031240030000410080e64003580180015544520310b584c1f00c50303070780d8108400505410343c1500d290080340300141c10001414070242c080d960040c081502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 233901699 1250 233900449 233900461
    0x150a02070c050f011e02010605030115032001050a030e100c0201050702070905040203061302120d111005010807090b0319060b0f0d030801030305030705070f0c0f0f0b19050d020d09110303040509 85
    0xa0b09109244100c195503888c40301003090f440a0242200c03901d407078030820f48081e241d131070002c1c3d1800c1101620b074200e08403180c58540c079a034807008898200e0140c2c50042068441c000c22141070043c51000d140c0c4031458580003601c1d8075010f4000510074807a98090790001660741c1030785402c0c1c4400300c43c025459002070002403080d407088085402c100d800942040140c50003c15503070316011104000303d0100d50110308000d1441400c110304001c901442c042440a0351500700c0f220717a21001c50244121007900c81890800c03030b4900b0414401d5a400032150740380c081600d42001750041034020300c940d01030000c48201400320305204512103074080d072695802e480da0f86180c030201ca071074002034000001c1000030400c2d00b001c079085000c1e100c0b84900030f11051400501c0d10340b08a0710344250764000564811004400c0140c14100f0741510a0f6915a00030018400b22480c011541446500c8105007104d00c003203204000700c0301540c4001c621501c50170b1108061401642019503c1c000c0e481000d40c02441f690008003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 233902949 1250 233901699 233901737
    0xd08070c260412060f0c1d0405060303090613150c030c0b04150903020105090d08070206011503060e15030c1e060c0f010914060a090b040311150a02070c050f01 70
    0x4070326120702110354241030700d03401614900f0610a4060b04c255890b140c4084900b4024403171010400c42d9401c0980d0911180101d4948110840721002d1066944000048480c0c60500442d022004d0050425684600380e5100380704010517802511800a0384400c00c107000350140000c0100260035807140a248074070360fa81c2c032550f50300041c01125541c088540c200c110002c5800380d141164481e400100e10b91421942d140c1c60095486804410480058144812a6008145a41541c1810311103852542c4a90019400b805a9030300040502c03138040704000e40103a00c0000301c40c100c141102600d4801200b142004100002203507004140b07030040b481d0265610f0260010704104c0381403c00c5e9614201d920b0202800c5035000041982d5250b4540c05035100c02c00c05200c01980519125410051580e082d00c441041100040c001000c0c0280500b21462400e010002c0c3d0b02491610001c00c030152400c04030b810b001c3c2d0059170080b04c1c00c0d407030b650001c100c0f031401516919036404107a4a1001d06c10740c4d640303412 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 233904199 1250 233902949 233903003
    0xd0206070c08091302041502060c0301051c0317010f030b100b090607061b020a0311060f01050103090f020a0f051815150d0501091505180a0c02010e07080d08070c 71
    0x103620034511200e01d0f030f0840352400030f00003d1048482000d1100d0b410040a130270301c0c50040c40d24466520400051080b071781c852003081e800b9482046140381000e06403400b922481c550768075011016a16038000a540e103480c0c1c0744581502d22402101c6410b84948080d400024094001c142c00b802c81881300d140c1780e081c10f5010b02540b40c015040866010307900700c2d0261a60004941c2c07440144c00c040c01d000f0a241c3c212190f640790a002c0b03c0107251501c2c0a03181885512018042c0c54100364860070700c0801d001c00500804503654000348000c004d2991480c1c01c2c21000e200b840351030f028229101455619040401c5005c4c441d08100204152800c46a0304000c045c03810f182a60035a04414003005095128500c140c0c0e020304961040069001c1e580d80c1c50254452440e4451480380c030110000204280c400c10038203070820071424010400d0032455506a01400540b00c42540501c6460703000502c0282c0043c035100450300e0358940300b403e80c50b504c0040307601200c0c1400140c140c5182c10b96091800d5000c0361a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 233905449 1250 233904199 233904217
    0xb030d08070c020904200607050a080a200f010b01090815100b0a05090a050405091902060415031415060307050f040b041514091309080c0a0c03050d0206070c08 70
    0x2580700b000c0590b0004881100c1500c0a81c1d5041d034943e804050102d000d407841c2e03124101228041e040500580ea255510b400c0140014078005011500c1468540502c1c03400c0d0007035944071030700742c1916040091107a03a5500c00000346019804d28a1490442d402046240c0555019a014051088404440518011015001c16641a00381200288c43d0701400f004d0326645806540d060358451041041000700281070b000544210302d88014070940704400900b504100140d141242e032a20160b00000d82d0902859204504951010b042d0001c840e40c5944807098100c26800c21131195243d50102d0640155400340080d00300204002280003c0c0c028005070611881c03003d880b91400d5140c4c440c4108503000b6030b03c1044100b422581160b8815003180d044c02c0c10525886843d41031040317000000c3c1d8442d0311207030b08011a66071010444c0c24099808100c803405e41c00c50301120388900441c642440300c21418402a5001d001c0c11a00c1f0040394070204010b03019920681d5407441814032500d46c401300368840241 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 233906699 1250 233905449 233905457
    0x2090d051504140706050a0e0d0b090a26040b030a15031113051618080109032003120f15030601080d0908030405130908121303120b030d0807 62
    0x41800049040111504641066118101504161504109080c030300155000b86070088101800340c41e901c941910340e200e082d440d092950040e6000415841a440c50003c0c06900e102c80400c1003207500001d070b001496114503000c4003500200c00b0744c044c1039400d021560400e90000c00c010015010002c018640100d01c00e8400a0705819000c0c29051140b8681d104540f00e003007554524080b8078014910b00840c80040200b400709191624003410700070902200e1509101e804030014035002c1c100a04e00d0064002d100c02001a80c1e014100600728001001071640c103801282a00c0d00c82e060007000355101012071425003a16a02e43d4844150341e020024500b078003007000c02c1c00c006540d070303401c000c29030082c0001c20140261526a01004044121640203803440d540100010480ba4407600030404280d202d0240000c0e400c440c81c43c0c941180d01c00e00901412244005044c40200c40744a510301d490a0720070b4a40c0e03142051490215003e5451f840310240d1f26401075032174100907074000c2d0141503003ea51460 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 233907949 1250 233906699 233906719
    0x6390b06120a0b0f0703020712081e010b190903120e040e01020315030f28050f0a03030204051057020f0d020604030303021608120604110c0a03030209 66
    0x2034514242c80d0303100a40c0c400140d5000e01c400c120b00c0d00200d6030064003918040d031910041d078460780c00a0b5442d40c069020081c8000001340d012415003000718202c4c0718800c0510303403560340b10b0a8980e1504500050070307207254032045405031070f030058031004220703a40084202806100c080c2c05076001045900c0183d00f103038649400007004070013840114801e14842515201e000c003034206242ca80048004c21a02035408034035510130701094031442c0540582c802d01c83c0148122980707059810605078501198161140201103805c040e05600500140d4409940142c80e41002d140107c03252031903080400d064511404850765801808440700d14049242001841c03110107007100302640c4512402c158140c0c0000c0500c038000c51500c4910055081c0c0200c400c03040f0038081d600000c1d1184134622008003031682c0000c1d1003080c4401104401c000e0303a005407281c0e803200d440c040c0c103016075103017102e1003131084c0d2502c2c03c0418139003450b07070540f14402100c40080c80c84001540e800c3d00254070003181c082c0e00c407480032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 233909199 1250 233907949 233907979
    0x1005120c03071b050d080a0b0d11042012070504050d020105070606051504090b2707230403060b0d0503190e0604080d020709020a0206070f170106390b06 67
    0x3e000c990300c0c03441000200000241d42c0070040ca208000b91080c889142030910350240c5135280c941c900d6505070051302952070a181d4a0001d80101103060080d503c07031110951844001d0011303005440d14041b009005002580c5088086521380f080c3d000c0c1e40d9201040c942a14050352042001d0440d0fa48620300004e825912800020030300c1d21103207140400080009014000c8000c58001c103551000143c0750803100d05c80c1c0c0c002c031400f441072110f400e031f2002e4440c00006044a110f00100b0f010b9002a407103000312343c001c0600c6810180d005010564084e42008008805420042c3c1d010030000c0d040009541400c0c0c002c5101e140c8900e03061020b0b000c000f80c00d42e1890035980e800004000401216004103400414040040c0c20a0b42c103910004c6500d1062140c040324a8000c245140d1208041c50290b4249541001c02e441009003000640c81000c0740c1400030410300e030010043e03980c406c16400340c110000b04400010744241c40c40c1a280d186c642081c1811b10000d500d2013100b54000741e00500149074942e900d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 233910449 1250 233909199 233909237
    0xf110d0c0b03011703070c0b0f040e070c1a07090e0a0b06040f03050d080408040306051905040b010801051006090b0a09050315040c0605040b070b18010906050103021005120c0307 78
    0x10382051a0341e0700000010031200e4284c2003d00d903048400806107040012030348a0f002d56107000d101d4400310000008035500341c1800c00381190041e200111012200341841c000c010500349045c20210b4100340750300f000c81d1512943c2c80c080f9101c0d400310780e11041e82c1c1c1d04117294096459805041d001d103d545139010307940c0568414002d003000d002e0010500040340d01d103040c05071804082c140480700748030b40c100502c404030740250210340540e5004403001c40c0325115040c00403001501d035920003039998902400d20003040504d82c45941200c055000034041d50301d0700c0c01403030300da900d0920400b00400c3c5150360030042070b800742c000303042c0100d4241007010a60742e448000c00c0c10203061195021110f0003031820801080b40014100020703003080c0c070740581018102001c988141c812040050002c048440000303400d81c502c910101d03c5851150028441008103250860180901f80000c9124285031803032154951300c58801d80340b01c2d042d012890030703071511501c1228105903c05094941001040c0520800360100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 233911699 1250 233910449 233910473
    0x9031b0308091b01080406090302030d06120c05041a01080406060e010303090603180c030209091002040f050a090209010801051002070305031902010b1f03020906130b0715090f110d 79
    0x1e4640d12410b02c1d100e42c400c1d05001261601c001010342c0c1224043d6281d80c442c16540d805a4481c1d00021100407908080e4a18007070034a0849d0664103290001c51600d40284110038010700c92000c250340306494030200015207024590b501152250b085217641c241d071290204581007030084100090301031b1036096055201100f60815408039035001d01c10001e4a9241c805c0e840000c0c460868505401e0f05a07031a4220001c00340700180c4900c0002c000700c0c004040a01a0b0082181090021582c03540c0e622442c0f2800d600a2143d10712030b100201c40014610003a00031a0744035413059444508681c20700c800c111105601601050461007400004800120200010207030003000048800213807100210090940d5944103100e40210180c5215a005028112000c00343c20080e04000d61101684408903200d07025003003c0c100291a02c01c0300007822003010000748009030080d82804540d00c1c2c248106415070300c01c0f0100900034001e001506020a8845800010304940241008100d10954480e10b5200e48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 233912949 1250 233911699 233911703
    0x4091b0303051b0a051509100c0906090b0301030b1303051209010204092403140c040f060905180d030504110409030305100909080d09030c0203030403060b040b0a1809031b 75
    0x540000e04528042000700101c03c410244001408015015550319885a2407420900070624030711020900c80c01c8280044680c4d60000c0e4802c000d034508412004280c04800d104100c08240050400b20709910000216416242c02090720350b07850321400003441c55540d07248070a03410803200348002c002c08282404c02c5c900a405d604005610f642c02c00360010201c418000d410401d503000c00035a4010307404200203400440342c01444c244010340d034500304281407140c1d00c140f8070b0b0305c11724060101b5455181a070026007a035801100400442d5140030f50001c1c0c5030206a0040d40a80c807020089000701c0c4240c1009901a208030742003a0407413220f07004141a950000b40440100380c40b80c0c20042075180a2078084000d00419030240442e00041e115400684602c5002200715619140d28005040c05180000200f41e8094112907407603980e81000c030f00a040310310750284a142008082c0b4114640404040300752003581e0440c40d141095550325000400c030b40c010880a0140004402104111101d842c0408074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 233914199 1250 233912949 233912957
    0x4260309030a08031e01140111071206051f0303050409050603031201090e330603070e0106081504020a140a090302120f01050a0507140a0903050105070c0201030b01140904091b0303 79
    0x41040303071410f42c80175110780f24410782c20002e400400c6480302454107548089070a0800c0d84030310340c1024901381020050b03008034029000000c480400c01110f0362003e8414100c14501d41c4a10a5030300b230b14210740c3d00c2c0c0e10001c0c000803002d0205011703000007070780800c0e000000102200e10f042e06801e806803190409900040209540351184407a07071000f40250315220450115014402c40301407500c242c500c001c07942c219500d140d00030019040345c0b02001140c02520403070504c1c45454bc1d4071070000b00160811601e040c0b824060085403001418203000b0780c7d001e118281c13a040b0920b00d002c0303800300c201e8018806400401605420010160301d0b000011001080d8501c050105a03030000c002d9429100c000d401400307650f04d400704105045922005070820f030206250595038802d0b1500c0101c8000c1d1503500098019480d101c01d101c0c01640140040c0c0645100b81c03010302c03614800500641c0c007040c155400116140d0208511855480d06600c015004c1d88102c1003000341140c0303111004070208498000b2000b00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 233915449 1250 233914199 233914201
    0x9030507020909150a0b04020405120d0906110a152405100504030c0501050304030203190e0f01171501020f011514030706051806091c03110304260309030a0803 70
    0x1d81006004550b100c10038400604c1e0751002c46811840402c40100400c402d00d40c1e480380c2400503551038040380c0086c03400078030b0a00305200c3d507006a41ca600d4040d4050000c10400900041c0c00d901030910328801d2003040000d0070b078101c42c580b1005040c440da01c074003007049640d42c0c030000400c0c01981d811607034942c218400ba4810710305140a000740003102428400902c9401d2000300b000a0034010106d00f41c1d4002e10b405601e07521140b400340c0c514082c05070450740d07840b903c0c141c41410542c4014190041142210752240c00072013400103580d041c8031020810101c41e200c9000544140080c40703e01c40b003101c1807045525860500d4040c1d03003165809140108072008024080017070b140e24182600b0131030070403400350260900e4600c003c0d00901c03450007805242400703410000b84503960041614029403000c0c211058520640700075450403000d5039401c40224070341c9201148030700340000666042d10744014440804010015100c1010280740540f111140300401000285441c11310100c04214071810750706841e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 233916699 1250 233915449 233915453
    0x7030903120c0b150d06090206070803010e1e070516080c0703030809010608120d0b06090402070b061503060307030f020301090c0f06090801110901030b0a0302100210050a050c07031103040909030507 87
    0x1804001414841307104007100240540c40c1c1d82c000d1214640e6600c000002800c070280c1c80441c1c04c5015811020f044010003000001d2109811a403e6108a040c05400c81c1d4182140e80c4010380d00d1400d403003a0300081c4052040040c030407100e0350520b071810b01412807207040000300800749103000d4054100310001011001801034000b424082c2a02030260440503007044034800c940342d0120f010701c000c0c01402940b2110792003500d0322080e0403130b20b94487c050420b45d0707255047e04120790310700d10a80740640216881c1c1c59a94030040103c1c1542c5c010b1800501411000d859521100300d00040e841c0140e0389550307a034111b08006444148080001c0911340e070718101541c9080b50241c1060403d500950304c83e41003000d00724504245200303c030b140040900300015540c0e4240c0204412512507080203401116444c11486082d8000800f0301103030240c0907044c803c9584400075002a200103488420082c2c40c10300c082e0300028001d0b19003400c40701101e011030b0300709075840a0500030786046a5094010600010305402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 233917949 1250 233916699 233916713
    0x90c021e0c01030506100203070803130203100c02160b0a140d0504030f0f020d02060105010f03090f0602040f05120a0b0705120f04060f0506030601031407080102041403011805060402010507030903120c 88
    0x5170002d41240c1406400d041c800c0060f46a21651100500c00e03a80000041d120744a040180c4103407a40150807640200c840e1000f11700206000c07071440015204122902016040480700d036401c3e0f40c0c07580002030910013a000c00343d905c0204092061030240c0140b04074501c1c00c51314440c0714070440c041d40c1c036900980c60440015290016000e01d0104540081005944103600090100d04552003841d1166101000003001c0740207021021005044560710300325803090107507039000b41007070700c0d190320b0207051040e45c071410400004402e69418030141c00c03214804000c51502c8038202ea201f0418201546000d04110b0388450012044803da151b100c056002e00003804900e100303500721140400c004014500301100000e0f80c441c8140300c01000f1031101c40304c0c2405254140044c800a140030790003591241c0d00c5580b01d1072001c1906000030702030344c070b0304d94440c9004407042079403d810b42c0c1140180c0b0054070786400460341d81d881240283c040c441e10302c500000080c0c184002d500503000513070b5400703030703040c038503d4419 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 233919199 1250 233917949 233917951
    0x312030a15080a1a040314030406060f050105040e04080307180602070303020c04021611042c0c030109170d150603050403020706231c11040305010b0415090c021e0c010305 75
    0x45183d0100d2407074000144140c0c0c0c01c0d00c10078450b5280114071340c1c41d450100e40c640300c0408503549a07034001c4240700c10002c0d1a0071200a6034000c10540f9841904c2d0030044420340250300c161961f021a54000c540400c12503001550480d42518010310301c041400c0000c0e5440020380d11150059100e02c0040041c1941032004000d00102240d042d46845401c1c00502103c0210807030103040700740c00000c2e403412681c1b50390108503108440c07588140d03445103650000c0c003030a00400d1904014043e0300d940f041186410301c1004615540301065804001000600d401282c210030340d061a801c5d5680303800c0080c3d4a07021119001051580c1d404200c52a040c94000d05291240e8040000e11500c82c81642c0d2040c0d9420060070801c05404038961249003070b041c41e03045034a20b10707880d541c2a0714200b00714a180c000a00100705580c000c100900410312a40f060004841d5052224500d989208a091101003502d400c10600f8202034411219200109400404180100c000143c401c2e440740054034019609070080e9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 233920449 1250 233919199 233919209
    0xf060201050f04110f2e02070905100e0a0603051b01170402220b041109030609030a050307031d250f150302090a0807060203040314010c020703020f0312030a15 70
    0x80380b1820070b40d6650000380070781c1360280e2107820000b11030b05c040e40300ca01d0310260700043c10000c2442000001942041d02802d0300340c0000501400d00e02051034241405114011200310643c80d0a05240440308800910058421309402e034a4500010204900b000741040101258a40034814030003c00090900000038400d0004042d202c0104400b40c1ea03001c04584414550b401090103086c0000c2880c002413a0710103a050340300c0d03d044c0400d0705814914004c0d0427a120150b080350020303202d04c00c02e180c0d0703800b4980484002170003c00000d0802c2d4800e4000840c20018041004034110b04843e5042c203080c807056080c0d0124891349076019080448421100041ca896500311900a040c0004e407014614400700301424550000b801c10965222901608000d114a1007030703545968076260001c0d180d6200b03110070759106402413540c0320407020620540e08009a15001460418515030070f001d10b0940e094140355040c0918888020f030504041d00552180444171400629a03207280e40c0341c00c0c1c40c400e981013 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 233921699 1250 233920449 233920471
    0x3071a01170c130f09080712020f0312070c0c03151a060903060604020c070b0a080402040614010c170c0a03170708010501080c03090304030215180f0618060d060f06020105 75
    0x520315034a0303d040b04000203001c2c00c0045410800c40204001500b0071940003026a000010346c0d02c240044000c1d0310b0b94170300c1d15a00780d4400c4210000130513503a02840711840c50000002c2c000c01e200501582400851070300c40c03e00102040c7d603d031500003140c15580040c0d2802601c45030300078009003480160748011401100c406041c03135485800300f640c500000b400b80e40502e5000a81e10407887c0c04104c803030001c00c0d84140196480d078003150300511306e400c2594205e01650510b140841e20b4041c60030158507240381a990340740c2c00b444170340700d80e49101c090300e00c41c60440308100a0b01851035000c2c80700d0000180a52103456040c440d0401e40e40e4904001444a0104082d510051003240c2c1d21070102500404524440307500c03074039120000f40c00d500c40e60784000d6010015004000740d07051548044e22142c807045032244481d54042c0b0601c40e144481c1c0d00b601e603112804110107140e1031721450031030341c0c008000f4120504192016104404603103185d00b0106000441c1e8108029140d42400703816480005416 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 233922949 1250 233921699 233921713
    0xa03090f02120d0f031116140d020304030308010e04200d020306011d0f010503062d010311090a0e0c06070314160b1518060301020d1514010c02030a02040b010203071a0117 75
    0x3034140c3d05028200c0300000307c2610154800a10500740000d00340310704030109031881d404103001e01030340e203034090700c401c0300424480c40c0002a0103c18081680c82603402914140710228110130307003408102d41c0d010050380035215031201000351310100425030180c2002104403445c0c11080c2c040c01c42c1203100609066010f00f0f03443c01400f440e00c01181041e0000340d80fa204d210207461616469146001504210201010010000061040890010355041815030f004250343e00d82a00300c030180e66141248490a5000c581c040410f424800000e00c50f10b0301030700c0c08200750349010449441903400104101c6079100709480110030301c40c0c81402280c2210104028120030251035001c20b420072045e00c2c0100d0800c038000700103000340d24290104c40790081d4190023040040c1c1840031040890f030041c01200051880920020899409201c030041750b40c0d0003d0080c2a00111031b402c101c042c1c48a01e00c0941103000074442070000502d0b0300e040c400d24a5056a081d000c0751b040c0103002c00e200079600380d03040c110b82c0030341 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 233924199 1250 233922949 233922971
    0x3050309010b040b1507150e031308030a080414120c010e0d0c03022505040e0d020f01020906160c1d09121204031d0613030b06040608030a03090f02120d0f03 69
    0xc04d865100c0e10f10740000688031101030800980141c000500ca215a23400d080e0074507081500880140030700308868440204042e2511441980c0e80101d40d0300801140074000410b000ca001c0b08902000c7e0103500701107840411801c2d0381d461468114014082c2d46070345a00540c1c070480411301050340c00f4240e62521068107110303a1070007959503c03c0840810030641008030307224400400c0a1140c05000054010303c0301c80030b07440c0800c1c1d031881d651080fa0018000c80c0240d6942e800e041c0225a940c1c180240b0480c18000a200824514540301d2030454050714a0320000440340241c120140c840381c0c40c20b41161081c602694201d0400201005040c0000b0041000701103e044d58082203030016050f00e4020406e035240558050401c0c1d802a0fa81e03400040812070f003c5400d4a01c1a17802681d220f111002c3c610b444a00602056450500902c65550024048070100c40c4c480d900600003903010707a132000c2402245401140c4042030f504480310310f980040305044100e94000c00c0c1c5620351015442d0400c1040c3d81b071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 233925449 1250 233924199 233924209
    0x60720061303150b10080403090f0b04030204020f070609080301300602032a1806030105010f230d0b032e15081005060109080109080409020f1603050309010b040b 71
    0xc1d000003095150041242c03403040150703910182840502410998005c00040b8020b81000f004940450008070030040c08103a48a03100c1c4c440e000c49004161030303414241140c1c03c00020390009991811122001e01554021918074081d54010b01d000d04d0107181c0c3e80d4144086040c1030302800c0c030481d4807900342e50341c1c800405510403000d8900c0f9400200058694448910a20480c00d06140d461680e00940c00304882054803900180030502c4841e01910345240c181003809a280024810306003c96510030b010080da50048500480d225222a002d02040d051048181c90640002142d034540942da5071505d400d509080100142100301c00405d202e003000e000410150482d06450000341c001c2d12500b01e5400104c65003045009402c042054403440100c0340421002820704607803d500180c591381c000201c000d410310170302010b940c0141040f03160508140d80c01d0040d6100f00d40707141c20040c0400c441c80e817010017440002c20152107031b581c2c503940742404a0080e0a4940c00e1983e144210324202024617240c3e90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 233926699 1250 233925449 233925487
    0xf0903050d0e061b010203100e06030606040903050d0203070c020906010c201507050102070b060a0f140f190303021e1b0103020c061008120a0e04050a02040506072006 73
    0x151910005405210010030454010803013907582001c3c404460045180041d0080c43c855403c0d1078070300910941e612601c10a5030780c00d4902503010341100f0003060b51030605030001c130b8400f8000c2c02c00394609030132107021000b02e9004844500018290304141c1d01180340100390650002424a010715a0401548030000144040f60b54003050603481416500b031031712000001c0d84540240406692210802d0134998083e40c4101c3e01142c031300325071200181d02450200c00751400e850358a10b000b0328a07820003121826403e400b81d20241d02081011a881282c3d6615080c649000c910501070a00649180b6007e072515840c44521001070180401b000114500001d801002070001100c040401c100e050040c1c0080c400c046820380b1600848040180d21012500100112042001111342c9441c1200030100140030756855180000d0300200740c41c903d440d064000c103030888002100185001d030b0b504005410750f842040c1c1103410001c0702c442074141340c0d20f500c610780c0d00c0351099075500c1c5009190780001c60207001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 233927949 1250 233926699 233926723
    0xf060306060f0c0203013905210a06030f08130602030a050a050304060603140d090b1201050d0c09020301170f0304080c090a020c070e040204051e0c070302030c07090c0f090305 77
    0x590303d50302400d6680c00d401910302e8001282e840d101e101000000385000d00c0f0b5146a4120080440c42d0900b041c92060048072441c091204407102c019140c4502d003070302000050024412940c43d804084041118141d6440c4154483c40440b5601c45050f000ba1125480b29840301c0c05640040c0118a00244c00604648004110345000780d030b25504c07403800340020156504060540f048090413640c4103000040c540c00465000e4407003034a8241d80310301ca41240c2c4200d036075035812101d2002c0108240c0c2041c824032248076200e07002a051450b00c0d10000022608242c0c0402058014a40b5509045400b400084a619200380140d49802c1c203103100313103a03282014074100e0702526031400040e00d429016070584041e06d08240c180c4444030354408480f4006082503c003039100e60b29280c00314071484081c4002241e6032900b10900a1555248402c003821030704045030540550104200480c18250306008000141500c00000644075080400083c003040c50301d11030300d0038006c09810030310100f0400120744e11404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 233929199 1250 233927949 233927957
    0x3040513060803041409010b09010c0809030a02190f05090402090718120312050c030f0f0c1303290c030109200304030f031a06040e0723040f060306060f 67
    0x10200032000090503640c1c8208400c1c04003040c0400d03220103120001e008664105d8458101e0f9032501c002d2240c61003181242c80c046100c2c0d110240000349100c01900aa4000074241c03007510710140c002c10300080290b8940001080084000e12801210f00c2d0b0312009440183c50255262070280d02090700c4200c080c103628244460304940c000e0030014554164040c06020b4401140340c100e074500500344409054001820030304000010302d40b0300910041e2407003a442982c00f00020b840b0800705c0e56200c0320140ca00d00080320200502d018524511402c3c000071445050414176442814800c2e8500031806a0000c4070882e0b0202442204003182042e2419102c40c008001031031000790110240840750b9401c1c4122036040401004240341d0000890b1106c1d20321a20240410780da031034841c410181c0c046808030750141c01400140511952141426804181810071034403121a4490029900e01810054440d00d10300080a00c02900340c82c00d602c0c01000c8d282001d00205040a0001d82242210380c4420100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 233930449 1250 233929199 233929219
    0xe1003032a0212010f0b09090a11040605060c07080705010201110a0e01052b0c031509050606070c0f090b060301150806031e010902010e03120a08040501110a08071205040302030405 79
    0x884561001c0d14400d94020640901801007501144c060440740721420034031494205a40401e05010b203d4500c9a80c203c0301800e0f40005a80e108040060145a0182c10940d03952021801d070301c43c100103005487c1030f400140b00d41c9103018aa070b0725202e40d0b40c00150441e410680204000306001090791056030040c20045503510f003880040360f0a0003489034413141d844080840058450b00030401d103141c1d080f008020b0004000900c0150103685031311441c441440b46c400d000f0000500306910090b0000d0000f0422440c2c508562905035810385560401c3d02e070110107620070031403c2c019108c2c4400c0d4040580d4030301c2c2150b2501801d04413032880b4460a40600040000090032684e050120102c0700304003307098504c0a1b56250024000e0400e4031089001ca0100e500182c1c0a240001d0700d0b030580340d130204402d898081d49540440d101180900210b0700d964948502d400c423480200d001c0d0009028a41e44d01e2020f1915060090403a05003e03601c0c00d605d4500302c148004a94040200c0e016a101500d5a03044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 233931699 1250 233930449 233930507
    0x5061207031b0309020306060d03080109020d0b03010204030615060905060403021e030a140706080103050309010c0512030a050402150711060315030a1b0b031015051908010e100303 79
    0x1074900c2442c040c0c19501c40010032104560140e0100d1509802507040b5540343d5a00400d100c1c41040502e409004a258000100b02103142c58009101010950b0404641000c1b80008282a40c100340c008840c115103510f0300c003006051034121000201034502e0500580380c07914001c10820b100f42d0001034040d0400c01c1c1d0002c88840803580400401d1383c09011140800440c0c103011504e0100e519a03c511809503407400907072248601d10007416607070001d0145191190050064030030841e289000c8500380580404c00743d0141500019500c40c28111501240c180340c0380c810418074481e003501e002c0c1c07c0c1400b4440400841c0c00900507400c08001503410710303640d40314540000ea0111a040110380d1600c10081000208110900001000d903925502c2c44a40c2d41c49403601c40e890702040701d000300c58950804040081405c0300d41c40308020a000d0402c24500725011612030101d0b50340c5080c030000b1076000801008104901c4071225481081d810f84801340c0e908640e8020182481c494924040c2c0c1451480090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 233932949 1250 233931699 233931701
    0x305130c050409240c0f030b28080a1a070f1209020f060d0b03160302010f1202040b040602010902010908062a090d050d11190201031e060f0512070506120703 69
    0x20b0f81100074445540c44503141c40d05002505c04014100005103029412288181c02401000d10b51040107020303880c0b1520144280d840740c0c2040c00c58078140503101030300152a031010311103030801d60700a000d84040010030401d40c880103000034060104120f02c44208180043e402190000d01807406035010403060414000070750345d00034012925a01110000d0100b0480d07800c1d83c02030401040607030907900303080200ca080486c0a5480d1101a021605071988036100718411070800c407a4803c1300c1c00050405403608108440342d0440c1e00400b01603035480032030000f5903800000050040c458000141441c0c03038080110b4032107082c4480c04440b5080d50380142c6080006041c1030300c6103503401420030300c182191820103d41d206501841a00030420b84816241400300100c0c21024880210494402c00d649650044000f0440750f80748104514860300c00031445103480c012200240400d080840c0401e04200c10000d00303641c0c400040c9030343d9202e9001000030b6201c40064400070110030407481a141d849400581c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 233934199 1250 233932949 233932973
    0x609060f0c02040e070302030120120a020c060109050601082404020726120f040b06010e1c080301090c0806090402010c0c0e070306030c15080c090a030f120305130c050409 75
    0xa602c01e0070402014144c040000d202c2003241c0c02203009100300400d1040350300c80c0d8a205407094002c040d041041400405148040c0394028000400040c0340c04400d54881341000c07420780120465540f00d4041c009150392201416421641001d1542c0440c88103072919850703188919505400b0315004201402481480452410b5010036007a040c2141c514100c1c620030f1a901c01c08409000c050403401251001e02410340f103d110765404401c0064545941005640c0305480c070a407541d2081100400d40300c80c6c8501c00160500c188600c4c1c2d80d40c0c9950620901600b52031110a181013080948400c000180c1c3c3c46442040e002a02800c00314865a51410300406801181d04031182014001040c0032a5503490f40c0304504480c0603040d40d12900307490307102e0144404840c0795107000050b064408545a84192070082c44003081c0200080649690380d61408030f00d00482509541801d0460780e844020360b05401090f030b2003200c01c124a5020162680c59100c04403041c01032a010350b5990780c10004100300b0011403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 233935449 1250 233934199 233934203
    0xa140615190504020d0501051002031603050f0d020705010b010f0201152607121209031a25030509190c0b03040303062706050a060c0f02041409060a150609060f0c 71
    0x10340d45c0e03401406080c00a003100f8030940380111401d80141200a1010080d070303614232900904151141ca40da1005c07510b0740c06c9414940c000f200c0400c80080c050308944010519180702e1000070030725540b0000090411840a04c50354151790401303403204100201c4c12400340c1510f869602d0380c2109123084c000312240513403403040d00d10148608040403942d4520030703801c1280e82d407040c040d0051580600e601205e40d80b16030b2100a2650740484a0a003041d00d01c48403a40e0300441440b0043d00300e4405100d03221a4090084445021070354680901c808107209001815503080035117024960b0308401e941c0c40c144981d003031144000e4024040702050415200303400041c003e20b41d0003540d03a845680d26043c543c4100c11401e19480c0d06162800020301400c1078800031048460725166264500381e2901c4060000108490407648150303941701a10520000c01d0f991400ba90040c00144051326000181c01e046901007000786881c0d01100c441042200d51001002042d120346240c402d16500050005813190300d610500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 233936699 1250 233935449 233935451
    0x30d03050a0207120801080d03141302130501091a09010303091802090d150c020d210207050a0303020304021201090807020409030323090c060c121312050a140615190504 74
    0x4001301865005104074181d0740060700395005c04d040c1c200140d0481c0c100d040200d444581d810002024203400c0c0ea1a01c2800d4009814450988030380343c192030481e03600360000f60030076940d9a10000154041c0348440340c0440251001d084d19419600d0203031150f520380c03144031107200541000b9010110a60181c40290b2400381180d240c03c00103103490a50a16015050003290f803420100a40d442c0c4006440c05400c451502c40091030250841c03c0f28a82d10b10b28100d180d229001c000c03d4000a030100840d0501500998005803a8201481040380b07903080480c01f841541c0c1807a40700004a5145011904007070b90403078000850b6000cd1a080c3c011709005046a1011641482c0070701c42c00e0521900070340b242c001101920f00d030b21100c0080010074000e01168420301d0307200ca415400c2c1e102ca500001d000c081c00d1000c902410950b10b1044120494500c04c00311440d4101c0d640d090104040180f4050b005020200500310301d103886c440784040ba0901d03100d180c3c812401c007499100424001c6030944050308001e08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 233937949 1250 233936699 233936723
    0x2a030302071a070210050a05041a0c150c0d0b040f0203090c010f0207120f1a07050409060b03011d040303110f0403330506041b17010603020306030d03050a0207 70
    0x10040c1d210406842a06840d940000024220742040000c82e0100340e4002c0c1450004140ca110455080c0c0201e4007078414043d003004003280d80307844e40070406c20500050301d440e6a1090414100c40c1000c6d80b0851a900802c025028440354848030019650380c052068000509500440e00040203003c1c500c00081820f4800800c0c0000b440c80804c840102c13a2080c3c844800740c181d01c1000304c2c3c0c0d544203445203842c00182e0542e81d0000032003450020765041d0040a2814408241065800d1100f0041e6025004507000080802581d1140d0140000030071013441c6c1d890a48d0326214404141d49591090411051020340020342010b010b94004100204850641525011044c1400207030303a200d804280d9012140e0680e55144410030f03561005212641c040054005c1041c1c4201c2d0003400010342901d030b0103601c0c0c0c0701451031140c00405141e2003204507512081b14030131907200529100c4040e001102014010810401c1755180081c0072641640c0914001944d03031f0342e101c0d01c20000c1c02030460042c0850f45541c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 233939199 1250 233937949 233937953
    0xd02120a0303050f070912050a02040509060415060b0415030e10230c09090702012426210403020604270c0804140a140102031f0b072a03 60
    0x5038045031501c0381c0c40c1004207469503201c00e500c0a50858004c800140390a405001d2003054500f400d00a5204108803000703007400e81e002a090303503003c54110307034154080001c1005000c041a1161850342409030100010b600f40309070a4075a02c00ca0144100c01d0001c0b54070744500c544242d004040d10a48070050380e20a4024240680c09407900341060000b8016a43c14a55101070f02003006020f1190480390500d010115024400b61400061610302503541e6403081030701489000612081300001424110345260800c0055800e00761411590070505803507011011709880001aa083d00306841d14245000c980c1500340d403080343c0304580000390004c101040004220025665881000145604100c0000ca41c40010404c0360308150600c000910b01e031002c0303800b00d1a40920319808030035910546a60804644445e00103a5141c0724000d4540c1d0700004002800c0c201d0b00c086642401364200c0381e1207030761526071217070028020b60740040c080003908040340b24880300b500079000408000050f66624130f42d50b8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 233940449 1250 233939199 233939203
    0x70b0705040504150503070611190317010e04050a080f090604030813060f091e0909150e0a020102070b0a030b0a06020609070905160309031206080c0307060c0b150d0212 74
    0x1c0c402c10740198100400740c0c0d590000400c514003a54405401054024500306003213612081d0540c04021600680e0b0002d00306480064100c03d0305802a02e983c44d201341c0c958000e020802050303111454500ca80c00c2800001080030408015051b00040340c83e441d1076840700035007000d114540b1140e82c80080002c3c00410020510080e08084001301c441301c02840d9a54000d0b14880101100d500014100c1030044c48040080da0003031165036104400342d2005a00d0f88503050407120610700548000314001d4a80291064901a400010f9000d0021700f400764100d0780042c0d6034113058090a4a805804140b0224032403003640100c1188074028075a501c2d10380d41d850041c1d20346238260b4041e41107005080012a01c050340f8000c10380100414200807249006529045004000c110011400c01041e1045009400780c94001d4002418080c1c002e042d840110908040c50010359600c100d050186152402002ca40c01c54040740d845200c0116035002e50049000094200303066400c029406051250424140240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 233941699 1250 233940449 233940457
    0x11407020127050a0e0a1d0304090207150606030b0f03070501120905010b0603070503070305101d0406060e09070608090f030301360e010b0409020a1202010c1505040b0c0924070b0705 80
    0x40b06e40800c03801c2c3d44c02c5c198015144007070345501c405038400c010405c0250526402025020f0042c5030b404001c481c03855482094400c00d504c0f12001a031100812011407030502c03a50000e42100302d006001842c03a040c0040e00301115505e203500c20507501d41003031050200a41103410040001000d10741d0724030b01120040d00317070341050b214000081d00d042e00041c56008610175005c02d454110310b0011324078480e141c0c0142085401230048410a4440e9000512142201d95050085403c1ca000d003103c6410039400518030000100700d07a0080d4002203012907011070100849066900da03103131540181c0d0b8035801e100620901c406008048034440702c66440306034042d034044620004031038028041000c07120b0800c01070718890400654040e90380300c001c01103040da0b5148070f01e22a00c1818500210040394aa50b01c0c090000c1d00203607051903c640400c0304110405d050f0507804409031503010f09200c0404041500e01c40325800f100ba030501e00f0f2882c0055030310b81206450340564821134002241ca00120000c0c1385400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 233942949 1250 233941699 233941711
    0x2a0e01032a2708070b03071106010314010e15011202060717040f1202030d0e01031107050312010509090615040905030304060603020307060c17030717010602010506011407020127050a0e 81
    0x40701580d11860302240340c2d0b42c0407540450014802d40b4200302ca54592680064022401c1c8421540081c0030b00710706011086c025030191a11600b41030048412500f550340000d030307a80640c0c02440003c0042550500417605440d540d0741d80500c100390500c0412000d04c1039100180c90548100035459440f00c4281c000d000303a449007c21103454a6590070218143c10007158003c0d45a0040810741c0d00e482c0c800c11402c0da00d200140340108003201c503900c48042c180d10010081d141a000011409a0607141202c0e050041c0000c0e6810040e51400e070303245a4903400c0107070840182c0958800c1ca034002d5031b20703900310128007900f20003507035560706003481d00d88014100c904c0120700900850000046c4030f4094007045502640010440350004007545007014945c0c4014103c2c420300565500b40700004026000f03007030290a0030340000610b4104400003400400d69104200f410f5941080b0501c0140d81c402a540c1c08885081c10714040309074074510040802d032140e04020f80055038201300160400031401e0480c0102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 233944199 1250 233942949 233942987
    0x120b0412030902030303130222060f0f060c08072429010207060c021906202a01090509070207050909060403020a02061c020307032a0e01032a 62
    0x521041036094070b03101d04000c0e42c142c1003440001d204060021610200074801403584c0001200104c3d0a0310190448000004040e40c40d242030281c40c1c40c410440c405400c1070a0808031013468008010001c1c0501007004040001c086844010405182010780031a42e84144482e018030600078040010300d40b400034005000b0842c5102c00708215a0880710001c43c9041c6e02400d041c0f0709000b810f80d420b0700a017a040303030841211900c49281d0916860f095000d04a00d81e5401d4440c1116040241c920214400c075003a50340010100250610b00a401d0800800c00031015510000300140141e51354800c42d4006500400d100041059896011031038000713880b03044030a000380ba15803807002d030ba075480c6c1220020056030048401c40098a05034028201c0d03400c44459007803940341041c90301030590f0019218003002c25100c00d0750041031803803080000c1301d4100300c0e003d11140504504008100010b0b4a9805040c1030b556204400040300201c5040c2c0b560442c07840803005091920b030010540504c0c00b175902101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 233945449 1250 233944199 233944223
    0x10203042a050108180f030c0f0d111507030f09051c050405030709020c03070c0305070e010b0c0c1201150f1d1021020910080f0316060c030204120b04 66
    0x1280210606078161401a5901c1c14143d0303c0c00305502c10441034088082d80fa01c01d41c041d4146c0810100018101c184400c00501524644141010300d06070080c4032103c1403004a044043d0391213800500311441c445082d00f020380a84400304168010420350868080c0c0c07600304100c41060081c0000c90300e1205101d0340040b911500d12030340032107150007203019855060708249010011005180c01414680400c43c065030b01d444007a13074030550030745074960040701d0f40d4020b03c104000c08512a200c9a00400006080f1072501032840945078440000406240c442c204401d06030000d010258032150702c1d6000c100401310700f291200c0807140030030703201c3c80b45403202d6100221808004944280c558001c001c07046c26190a9400c00e01070a4400500400c113405000c07060090300c000d6550301600c1402010001007401100f810300c250f103420b000d20504606500e5100b081001440b03581d01d271401210a422000000c0c1c80f0180c944101c1c080d200f0741d80590944203013040480c0c24820314007805030066100d58690941 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 233946699 1250 233945449 233945513
    0x1080c0415050405100b0415200d18090c080a1b05070b150604060c02090c270d05011506180506040611010627060e040b0115020c0301020304 62
    0x54514000210a8905030314074200420305241c0c12140d0410612a0350384486610340b0003008458015070320a05c0050208424031560301e411004000c1141080b10303a0300c00c0b0a90403502d10381da40f03400300c840108002c041e101c1425075025a108240203800b81c041c0920005510031002000d418080d52810030042c50000070a40c400f41000b2040d40552098664504140440e103902d48400341c020045070400e9031074030755400547d48060050001d01110b48654008a980380103000d05600e00802c4219841e80403c00d0301404003001000c0115900e643ca114607030303040134801040750404152801002d0b5824810320f01800e1108403045402d03031b584d07907035218420b2410800b0340380408941c0c070500307412050401081c415244103101b580564160100003042c920b50314030100300030118035050389568003603082c0b00c0b20f4441620700659006142c00b0b0840340d1070b4100780e220b0204039001807040051240b5000141d4031618001c3c010400e1030407000f00215182c0c540382c2010700040800c4031002c0c17464001c580380124 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 233947949 1250 233946699 233946701
    0x1e06010302010215100504090804060807030b030709090501020d0501270213091d0d200c0f190306060312030e0d090621060f05041401182a020601080c04 67
    0x204030303601607008000398810b12581062412001e042102c441070502c83c0403800c0c0c3c82e2030080041da0f600c20403c0e01e41c6c40380b41440c000c003114805007200c01018108640200f0681d00041d00e0301c103541e00d4050000c0d0076500341c54840e00a00c1003903410840107040000000750307110981d000424003950401d109a448908082d400120320a00f034000b018034000c01001e01c6603996a600840d52244100a010140540003501c64a04a555048040060400e1400b101c06481141c400804941f1082c02840d040706000001900400c00c0e1044502507035002d034000403800d01400d2000f00035900710f07800304540d50b240d040002d0310811005c82040800c0c00d051103034008880c00200702002085554074410b084e0306100044503008180100200e02d0b4110092880021001c2c0c401c8800030110441200219441c2034144419184410113035244440c2c07400040162804541200c0f0041248100000d070105600520000000c0300d00708918844d5080001c0c3d48480e6000a16241a030740140116800b20900904202c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 233949199 1250 233947949 233947951
    0x1a010306230109090201110328050a0c022b08030a0b0a06081603060b0f03190207030801170304090e060a0f0c02030d1109040e0d0e0108040b160c0210021e06 69
    0x10544401c04010024030303025510000b4445d205151407149020b1111180e45160407101881401b140c2e040c0341c014800020300c104600100a40c10828100542080080d1200064200181c01200d00301d4155001c41000b80c0e0341c4406540d100d214490f0002241040410ba0300200ca0603804d161a000700200640303011144607003111a242e940c510569038441c031110045c1c40442e0004213150301c40e0004501d120480d406000c401c3c0c803036907c0701e03241d1400030440c000010941d103106003240e1042007400003280d80000c80d541501c0c5004002001e18084000302440c0d48116030111400c685400c051030300059010131098010010140d003408210b800048000440321040c242d85c000d40d00c00c021611000c1c0f441d40000d404880d40480032802c04103202d02160640303c440029020306e40010f031a09071015000303d1001c5502100b03181005091416584625200c5000b8080700c80d007186079072540d1a03941c85104881d2009502400d440300da00e050707030400ba6540b00c04d4031108461400400b804044240002100c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 233950449 1250 233949199 233949251
    0x2d03040f0807140d23010b090a090b0c0a051204030509030706080a0e0601080d1803050a050a05060a0203330a0f080d0c08030c161202061008061302100306031a010306 73
    0x85c0900070b81c240039007a0110b40101050000355202c0e10540402e684403d40300c0c0c480c18800700041822240c81c80c1c4012002d400800c070400c890410700c4001e44030307503015050b81c2d8030340b0f4190b00648040e29541002c0d580c1d070250a1081d036040c03252400105400c0d50002815008843c4030005000c510042c01c40c590301e500003400341d048140d00405014000a10070344020f0109035205103160311082e00c0e512001d041402d00c070002d0f02c3e19072200d0000750803c0010440e071688050300c1281181541403072000c0030003034101e10001c01c0e1064100070800150b0900140e2800c84020000c08440c0c04030303502c526203200585240702d001c84038002d82c2c03100c000c12030203a0805003c1075070001200d4039603554440420304c203412440200a40710314a0302c01c400050700c5c03286000498500740e00200880e241a0202c50842d50160300602400e401c1001444040034903040c8038410141d0494002d5843d89a140c401c0f0010202035101611480c541184508588088074440c1d0517240541000c1c045500c0c2d50030519440142c500c0782c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 233951699 1250 233950449 233950463
    0x41a07030f12020705010629031003021504091a010e0a03020a0302090405011e0e0c010f0215071103070f021201020f070f030203090d03050a0f022d03040f0807140d 72
    0x40307441402d100b502c03240050b20104000500708140c036150142140c20035000b0340c2900e56003101c20b23190b03034240e03d122840242c0b440300d400d807031440c02c030288162581c0c0610000b4080e8407036001404001010318155006403895130303410091000640444050080c0c0c00710600e01044010403003150500b0140c0d0a4001d894011f02404903007407450f03090212401e4000c006a13070955031526100500c01c140c2080c7c2020300b11401c0d01085101100c1a92808c1448422545040c0500341420800e8540c000c01c00101c4c0012020300e81c00640e40d414019030315012409024000303170100240318000c00402c0714032228800d00136140d000c541210b00b64110700b01d20481203c6412000c05210240015040c50031011501c2d00c244182d0303042040b003078089244007905141c1200850004a400070806600c24110301c0307444800d00c02801c4103132a543c0109880036099030010b1003070a0303c0320010032003c0204110750042215015015243d80d03150300031074a504c3e00d40186541d9044031244a1410301d8500c680106854010750 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 233952949 1250 233951699 233951717
    0x503070602030f0d09050f0615100903060902030c04050117101814070302150d0e0a080d0b041103010303050717070c0b16020916030c0329010903080708041a0703 71
    0x83c803070f42d207a008800c24510894844401c00000b4406004101c03e284044005043c982000b001c1d01c0003105007007020501800129051060041e40081c0d0807007120b81001c2c00160039030460012130f0502c0c0e0720600c02030300603007044000100c80700340c0003021410401070015903104480d1000f102041d28107026040700e400e0a089d54001c040740d82e61002c2d00c404c01d1600c0131144216174076804180001660b074440010302001042a01001d030707160107044542c86000780038080304100303690f540d892402110310303d081841d07440300b401c002a2150381c014070f02208130041e01516076942e4600140281c2c44403004450580e0300c042114070002c113070401e580402d40e02000240000d03080c042c404685400c000b204808526104c02c15078050b8582d072601c6402044130007000e0901001030000501541c1540d0801e5042515240d21038102c52400000003858041114411014001102c0100c0e0f030102c00d43c0003d03100d0300c0d00103404000c10007500024002c8412002250340503c801040300d030414040c120000e030100c3d01e181 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 233954199 1250 233952949 233952967
    0x203011202010807020f15060a080d1403092a0126060105070602040b0a110106080703080405040506030705031b0f0a05210709020706051906030210080601020a0812040c050307060203 80
    0x640590303441320031441152054031051503075a180120002c140c4d10340011060601541e810f040001d0300c080c00904008160780c0d240003600429142441c7c4440003040f601202240f0515014000c10604600c0041600c2500901001d5210518040b1500d00c2c00709603400d829454040300148050401c1c1100103684075948d6a12005444680c809a402c803010b035404c01010400d40e81c0d24000d080000420380e1008818000d0501e800d084503010b80040c1803648c4100720070000111070030100d9041d501c0544002c500707903c8050110745810702c0c1c0c1d00010b52600403120095105151640d13442003402e01101c00140d803a6148043c0141440180543d5030400b40010035030002c081c98841000c00c00c0108000c8410199076140600c0032a040410101c5c2d09588034401d20a86025550240b020345500380010030039030745940e0008210b40d8010340320b03a091042e41c3d00020107a0b030003030080411442d00007205968540002d00d01c035440000c1101e0840706001492000302d42400c000031814180e442c290001e601d401015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 233955449 1250 233954199 233954207
    0x7080a0b040603111207060f080402041d0604030f300902060f0c1902011e1e0306171603150207020a030606030302150f221505010e090c1c0303020d09030905040c0201020301120201 79
    0x1e0080c0d800cd5100c42420044e50034100010b02d58031910006807001303003042d01e002081d420703551391a4010890240f000e4401c814070a076603201c4400c41d4160003501007a0421641c8050411014047c3d0700c10404a005140078941e4801030841e00000c009035004808000d001c404400040c0201a001544801da807802c2201c46c0d0b039007088900068100065a500d4401d10202c102408140a80c00a078495508015114013142c665514002400143c00b2040e02c100ca55009182d092001070104981030280c00040221641151000d540251504544a8581c10100040c0c0b800d4401140144074620400001007407615505000e030410005021254072003a148038114441852492500408900444000b4000d05000c1c040d008840401180703070362410030421030b0403000600f0341d040c980220031204060b030341790b0001030203007285101094240310050130300728001d000743e0444078641490039143d00700b8150000701724411204125000c1c03084180c08141203090707003c28480c0d480201d90001500c0015802 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 233956699 1250 233955449 233955451
    0x11040807051309050d1b0b0a0e0c040513030f050c030304050a020a09021804020903030d020d050105091e0103080a1b050a020310020f03010b030718030b0114011707080a0b040603111207060f08 84
    0x201c01e440c01b411003060b182e40c440001c0903140d584603940c1e0b0709007071400d600e41401801800304040b1403c01c05031900c1010b810b5084e04080000702044100c0400c2c00929008500b41c60702c000c84101103e803240750030300d425039a600300c0c010140e1054031030240000b0700031694001c591406c0720003540141c1c01c100403405d100207500647c41c941e605000500401d0b1401e0311394800f410582100c404045419490102886000700c0060903441c0fa0b180f01c40400003c1d43d1061610504403980600115614551003030100ca000d4401b640c1c030341c041116224480d06110000502c0d50700580200e080e0384100c1e89014158017280319103220320515203800c1c0010042c1210000141d94082001d0030100018000500072202802664004480302c80c1d00358014451011201c100324035a5101f82450750030f21510280041c09514002c10b03032030420000c3c0c0d00040c003204550700042c01c03440e005081448000d0b1246045181450142034941c026030099481462401d0700141040448800c0d84400f62909500d003411126408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 233957949 1250 233956699 233956727
    0x4020d0f140616120c11160306140601020a26070302060906060a140622030804060306050f0604050d0f05010e07090f0c05070b1e04030503041401060e130611040807051309050d 77
    0x74008000105091b014046003030016641200b4203c2a81185481800c5540c060116440010000304006069070005a0000b44031341062000080c2510400c014a800c40041d406000303428000c50351800701600042c0c07080c003c0500c402542d885039a01001e1100002203407250032903c801050480a00e03044c8080244400c1d88485000c0311007140ca0007c0f0101071080354011281210002001c10110341e040c0305400143c041180c580111510000002e1502d00440c05024865101c00401408108550142c03844695210000780805160380e901c0503141e01040c413030051040c0c2480c00345c3c1c0304680c03a442200e29a00241e19610f040002a4440b044107820040001d2000b403035a4182c045030000d03841d14544560320a540721035407031401d482c102a0052520003002c449038148a0144074150710b004a0300d03404840040d2401006d4554104040508440d01c2c41c500c0000d0001004030340c15001042c5181a510150f07406144000c4002c0e0403011a808042c01a009070002220041898400c00b40020410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 233959199 1250 233957949 233957957
    0x12031603052a0405090103030c0506090a0201080f0601020a1a06180c0d110c15010311041a0108090309060c0706090501080c09010302030a090b0a090c0f120b04020d0f140616120c 78
    0x1038075403000c103480303150a17001500407552760030031a020068104035417a8480b0400001c0e2614080d2640081c0c6280700c0035003400f440589410001d8080e9208016000d0303200e0b00300030380605420704105407403094003041d80d409006070303c0c010348400031030031080403240100003c9801500c0d0082c0300d18100d00a00040d6212140054204101c1d4242001001051146481c50304903003059491841c21f41c003021012096540034030f080c03820803101045403915000d160002820030b2409503640404103130451160707000c506d9000c440443d005075010310000b8180244c912a484806209440d80c1c012354664000300e4617130140c01c02c10000c00c03a9a5102c2d070061038020744070740b0011401c10902d0f030741d00c001d82c0c3c41104c1c04103903a80e80311508018000408486c01c02401d40c000010075160404c09800745270000558040c100542440c041011074889516409445070030100c038490081d45071400a03010200d031458a0100d10444001c02e81c011100f528540b1400300540b2001140d02c071345144100905111444272081c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 233960449 1250 233959199 233959207
    0x30b09150a0312020f19030c110109170105010825030318050a1d180309040216050304080f160e060f01021501060507060e03040b04120804030512031603052a 69
    0x40880302464400d00349600684103004400c5017040c40c24101c0b6188070210314546110501007500166040115a0000308496215280700016a000400c55204d220806000f0911104c0320300194060380c1a502e50000360b440392403488a42e20100410300018100407440e9810400001e03000e8000307038043d040c200b256001000c1c0d865002a20b8820942d01010010301c0c43d8008101800149100c00d600030b54241e42c925602c043d81010700d0781ca0158501d014021580010f05180310074032641c44065980e8004102d90f607940c1c4030a4225183d50042c12002014810306c02030030a010040c214003c1501c450001da15060b5070b0b040d0401c40c10111a000c0641503000d1206c08808400019440c0e50180242d03443c1c0340c1d0b9a004618080c0700321511042c8890603504140020302c03a22006a0031181190b4400d81c1c0c13111070b0001420440c0c450b01c00c680c0010900e00c42c0c1d119009120403581d002c0d40c4a004041440c1c0300c141c0500b8815800d681c4119024000b0a2640d10164502c201c04c0054640c0500680802820 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 233961699 1250 233960449 233960453
    0xc0a0501050f1806030406050915040302120906070203100606090609121101030b090a0c021501030c0b0c0f07030b07030e15012106060f0f08031303080a050705010f05060301050601030b09150a03 85
    0x113640c000c1d00e080d0b03031558940d020400d0b840c500b040381c80c2d0f9011f60113110201900e0181c900940722801c0036076400300510001100f00c4150366803015980d80680040c26126001c05e61065800100030f54401c0c0c1c004650901000200035001c3c280120440c0c40a940e503000303c2e050b982c0c40d07080103008101914107059448181100c9c5817107064865102d6102090b0001d15512542c41c041c1c5031035406648020000344004c0144005026105030380304444107044116114110004854101030442162007294402e1304000402c0c002050300c201d00904040c2c500708007840b102c040ca1504e44070200b1110301020400801004451000c98883d00203440000580079440710582d40d00c420745c4c2c0b03e13038840c8000b491540320911000c0f400401c448020001c000055151001081c064074000071144000f0b890301030081000b4042501403c100c41006a0040003000300c06011002c1600409040d00d586000350b1070000001c1065002e449405175500c801010344065075510b80b441040c14240303e91454002d01e802c000000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 233962949 1250 233961699 233961709
    0xa180e0606010801030f060f1e0b0a12230f060f0f0a02040302060a0e13181b050108130201050409020a02030304050f03030c0913060801180b070801030f060c0e120c030c0a0501050f18 80
    0xc481e00449c00206040b9450070802c0340309000740d08486958941480d4000005050345440a80310000c0750717204003928050601d15040c80e41e80314018146028400400008001d08641c50784200440d819101c295181c10205400702c1c00360b808000d40240081200001140c0518141803024200501000c04090340000f14000c2c0c03000003070b0382c0030f5040c82d5140480420505d1400c02c03c03191101d449071407000740b80100003803002001504c81078415000100c00710940e403241e030440c0c010307000d003441c155510642c0010003540d82e4007c9600380c03583c3c02a60012041e6a60100c1164000e88285000e14140003010040041c0d00b12203a5154407400e540f0400050300500a01421340781e04000940080364aa42e4100520341c0c0e078000b41300070100400e41c0018400a002816800344150300004001400400024141c640c420f00b4900603a20a10801c981c04e0407041c000f03003c00c0040c078190166601402c0810a001100e407040c024580451010310034003065403039840150500c282d02900c214088104000031030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 233964199 1250 233962949 233962991
    0x210714030118150515070b06040e1f11070b040210020d0503010504020a030f0f0203061e0102070e15120c18010e01060c05030706090303022104020117060a180e0606010801030f060f 79
    0x409541c0f000300d0345105000700691071f96404581950240845900c2e5444c05407a115056008100040f02803124904090607601c02c02c3c42454204100e80d032650107087c1010030401c01c4504910079030501440b541074504c00710703802c045100f59440f224210703403c0100300006504803034030314810103984880284180840e8023440c0d0b40202c1c620401640d0713042000034020b0351542312606080402c0c5580c401c0e8036590b80040c00c0d1040342c2603c00c001c00c460b2140075149600258001d11300d80d0107001c0c200d24509404e0301144e24134a200d012a60304007140d15090111440680903c100250404e00074010000c0c503002d56000030381070f0300c981e00742d0b850507031903039100001c5031f008003416000650701183e910301c440909401124400b03060442c28034a858103a0000704850f840c9402c00840c400e000001c221162540c0546a0141000801c0c00500c0074400340b034200140751817011420240314013030202d50594010422141a03c0c2c01981da43c2d1031140644401000d000300c00c10104100d030341c514800010345c0030350700c0311 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 233965449 1250 233964199 233964229
    0x70803010b0c01060501050412080a21050a0f0b0108060904020a0f0f1409130f020f0402040602061611101a1c0b01090501050d0f082107140301181505 66
    0xa1502c07519002c1255086a425030451030500400f084280200a1500c1c551440941e104401c03c0d138aa240010880351101142401060280341005071714810485410045c0301d8605140d04005000b0002507820a4800304001c45d400709402e240459298240f20303001960103400a0312105407260b66240c03c26402805500000d0f041408160a11007858605481e032404541110103144908151a81000310503404100909001824034404110340b1818041c1880c80301c014402c64a8982e90400a91209407c031050140c2291502050001030301541030044010040c0f0000d10621310b0940c800002044003841184091351040305055032a0380700030b0021110b04200e050a005ea0a180c9000c0b00c0300a4181c01c041c13001810b0a005011030349030a03820036507050700f286180220750110304028440d4860005401c1d1070403004410340e1000300240700040d02a0400d40c0d104080041c4c00704245c0c441c2d01082c0121003154441c0050840540090342020b0350900740810307244ca89541d80c0c0000340c1c5c443c5c03901c908 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 233966699 1250 233965449 233965469
    0x1209080304050633040c1229040c0219050102070c0f090c09081209010c0b0a050103120503282d0b0405100504050714030405061b0705070312020307080301 68
    0x100322440d0800c000c100c010508002c0702150481900c001c441201e528240142c0c042c941d90006c00c5910707072149400c142105040701080150740c00e0080b841c03000d51443d660311074025494181c50001410503100340c24120307035141d01030326041503a0b140b4800c1c01c00c40742c002076503a50340070b00014000c0707603202036400010240008140d07099460448802c054461400341d00707042c0040304004000c07d000220360a4205000c80c0c0b0b030f0a41d1070900700010f0f16481c0700d00344003400411401042040043c0d5a622039410380b4044d580f00d10002044401c101c0382072004803003402490f1484d10030022142c141400d81241d4a8001d00d01061001d01080030702d04108240550300342074141000d0b40e00c0348003410f2045101c4070784188c5042c4020725202007405042c080a1151074011640d5200060b00300384140380c01814035100b40b80f4241c0d0f03400c2a090880ea43e08068038030721005580c125210b0f01e460351030302c01c4072602c6620101621880f45181c558a2682001740900b0041d8001040700c4000a0000310045020b02404a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 233967949 1250 233966699 233966701
    0x801020406080c0a082706010e091c050f03040f1a040201080a06030b06091f060504050307060e0906040509010f090f0c061701030b0604021c051e1612090803040506 72
    0x1008007501d50103060300c1c142640070070120035000d034050003982e441810b4140101c90010503d00308035002e020801400018020100003182d27560703060150500030301602040300c1000c441010280720134001c4410300c0300442e00c02c005030b13030145880001841e0720500543c400f9585c070740c5036103603401c0c101e2210025a0044520004100440d0381001141d0381040f03a07088100241801c5a952200040020b0b00c824421030a4400144080d8070284119420380c040035140304413255940d4025009410501640e4401d01480c640464510b12034440070004d210300904140064440c401480010140540a04099502c404507001c0c0d24502d40200d043c0300d842240b06e41c1005801c0d05183e85980c03041d4101d04200904416003c01c44113030b10000505403070300048030140c00d890b40d60015000744110f4000d010b007075400350803c103000d003e181d01c01e500c03404130007001294641c1c0711038a062510a00302e9900c48101c800a1521034654801e0250f10380d0104110000140f50b042e175100c074569034200303d5084407107a001030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 233969199 1250 233967949 233967959
    0x5042310030b04051b0904050a021603020304080106060e131805071e0506090939041d0108100c18030f0515040b07030b010219050d0225090c110708010204 68
    0x222a16a01410800c00841d110040c00c10400061182006e50b42c030558403880464100c0c0c41c158100c80024030600f0f20060009040d00c1c020391242c2007841161501d529050300002c03154024280034174022401001c00070110458003081d030040c043c0691209040a40d8403000000520410654024044080d00b8120500581002e5080e1003103d03001035000c1d010502140c0350903280c0000c80c1c0d41201c021940211203021711880c2c5030340c9198030380b03400c0300c134002d0b00003103c0b1141c2c0800001c0003511421000b00300003030180000e0070b800c400300703203e00070700f582c4240401501041198004203500700c043c904180f02051016090b240d8006a80050b251010150905410000c00f000780c0c050124644e1916422880c05441d214546480107215400b0325440d1016028581c0c403e2040303280518980c0c4000982040604140d5030b10313010000701070090700c104461545003450307824607110368150a00c0c1043c401401c1c51490000350104c0c4802d1380611203c00800003034840d080c03148038003412000c000161910720706 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 233970449 1250 233969199 233969201
    0x533070207150201060e0c0c12030403030902091f0e070e0301050907050406061422050303030907143313030b0703060611030d0b030309040e0a15050705042310030b04 73
    0x30b00741401907a140c103400b04070043c20460003603441005101641d8039448450301103410510642c4405111103000070401041580540c80310b1500ca00075564554540c2c0c2e1543c1178000a03410703032000c0080d11540388040000c0080116019400307607039454050701c00385c40000802d095403016543c3c98843d4004420502c01414a0f20654004050b14038007100c2e51000d400c640a598410b144d0b0110000c960f1000ca0b503e58102c0400d18001007001034122035803498000308060300c61085026090700381c2d0380c01d0010f00c0700349080041080d8000c504c02c1800038100d000791f410110068410401100100240558056070049246810086014070b24809151810b6900101114455008503044c00b1302100c40309c004c0400002030b05c1c40b04810050020340340d41804002440d40c05401140356100d0304000c10200400404541c00448038402e038001c1c843c2c440009400c60507035804490000020b50180030400c032810080f10b1070050389403580004050241c4400200f110242214000301c04203448403201c00301030400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 233971699 1250 233970449 233970479
    0x50f18100c0516080d0f15060c0c0312050702030105070f050d0515031516030216080705102c0c0306062b0c05120703050304050103150b0a0c0209130533070207 70
    0x4803010420711918102d00e4000b042c0d24022300702007150303004680d4204100444400050741e00415044595002460001c00c070390f0104504a01035400c020201c1c41c3c01c0c1c0a52802c80301400036407a40c600704101110008001c02004142440e00b14003802c455031140c805210024400d04150038400c8146402d031620208011004400c9040601c104500c2880300e014100e00c0c0015a40108803940c0c44030700d130500620f000d00350b00c0810030310707450014401c40b042400080420b264400b1089041601030342403c06480d40f050025054240d04150000780446c41c0c070880181012175640d41c071000c0c00503241c60006480c49080ca08455203030700d05205000c50b103042d03404071080b25500002850b01d1415a03803107940300d02a5124007414140c03914886000e0175496240700000c0c2c4085980e80d0384924900b14000c15018190320144c0c00340c0152008100c0748000c08800d085602d80000042a401c4c0742015101a40011048803540c52147d644103000700020380d00c1131034010304140d40103140c041e00303080c042088680c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 233972949 1250 233971699 233971721
    0x14040b0301080a031e121d0d031a03070f030b0c0c0105040312141b03091e060f010506070804062303040605090705031b090a140703050f18100c0516080d 67
    0x298000086071003544001b80b51050340903542e002c185042000c07800d47c1c5038000d08403c01080d0040c3d4203d081c4060b0b0540c80300318040030b9142454a00101c0c0420315071224003e01030490320480a40080c8003085403d8060303074000f08002c8180b868208000849800c454041d1000c8000486030141030180900c64010004103441252a01400b0b0400b80c8030121950850b820401d21000c000c4000783c540038041c031002849500c000155510301d81d101e0540d603100c01c011a039080e6461140400400c09050140544804503800080746181508103001030383e40c10103c400341c0301d642100544200400208002450040e1301c94000400d035401e04008583c117001d2950802c13400381c1c2c00114a6010f0141e280b890240e0a5419220520703151281107550015111101c03c55003200000c00070300544030740c9a44050300c14821540c08100030744404882864070710000444100d5540701034881e0089020700c0d446690481e446003842c5180440c0d48140c0303104480307e81000d81c2c0d040d8010440d450b546a0234026450058 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 233974199 1250 233972949 233972987
    0x105040203070203090915060a03021911030a050306030106030c03140105060910050405040c030512040f0b070804260d0207030302010e03030603120304050708010f060302010e0a0602030a14040b0301080a03 90
    0x12070030100c0203540f03005d00c030143c5125600400110b0b483d200c48a10341d905400700980745036075403400c0400140103980048007011030000b0246468081901c503411041407500e0a074051460904110b00882c0c4503080505080c1e455517841c0c80000010741c00d4144480190b1066140904405003219002d003111401404580030340071160030040b01e00100b801210035603e044400150a1710f9030700307040d800b44429800060252040034400c09000700600050022641d174840b00c004010340b2841109181c0c020703a500104a04000e20051100c4862021580c03c814804803403419245282c00c0228541300c0d21400a2002d40c0005500744141a03081c0a41c105280401c00203601e1070401d00c01081d910788030002c2d80080150003002040401000340700c03000040070349200074080e14030040407103c010301c000c0c0f2040340810741010380d900403030400c8000082110307221b801560074100221002c0d9081d00e082e4001d2000c0342030811001c540603060b9006580070303040b03803001450249407500c2d01500c02e003210400780d4005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 233975449 1250 233974199 233974201
    0x7031e1e0206060a05040c0e06070b0609100302060304140f010603030323090a0204050403050c07060905010809010c12050a0216050304060908070b0306040b1f0c0b15090a240314060105040203 84
    0x3d511400e00103801c440b01920300040504114104498043c502242183c0c131840006000080c84010070391300340184c004981e0a00d554488402d00000b4021910000703400180c1400004d010400304503040d2884019417003500c115030141c606280c21103006400480c0402e54890f0001941c4802502801d075100a42e4402842810156502075a40d8502d040c02846076407114001010144964203a03601d101d04a070407542015200ca6000e8000c004900070180010b448200088003250140600440c603c81c589030080c1c6880310070480006010010f00b0102815000c118100c40c00001c000f40341500783c0190302030b607165420f140d80200704510036030000b500d55016060174010790103882c0480e41c202800b2600085c2e01e1140380f020074501e05a83d030743d8017001161103119070100b030380106000d0325036442810020441d644484c4202d1100c0c440c1c44065400403030802c00a00e032a030681d44080802c020706240700040c01000c60481c071504c11a03402c222401004c90000310840002001414094901181c0650035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 233976699 1250 233975449 233975461
    0x60e04150504020901020c09250302030705070b180d0302030901060b0f0a05070312020406050705060702010c020d0e0a0b0a111b0d0b15030714030601050406050f0607031e1e0206 78
    0x40c04140603252060f41d0014244d1050380c000c11681c0d08040d805420320034a80340000c00c01004020000e000102c0d200d200d43d440c607250340300f44222481410113445507810308001703444d945880707500207050320a00d10808070714144d0384100f00079200c0c0c14003050385c0140c4d0f00d1501d0b4041a09540352940407100f14101400340708460503000094845030035007480d02c0e43e100d100701c0c1421035464580c940324041c80c520000300411107070303803060062043d80d0080301261b5260700c03102e40880c02c841d2540d400380016000100c500f400c036403040d841c0004001c4024901ea01003030b124a1001e12580c0140c60010108400c0354031240020740a001c49559002452598400016044c001c20041200780714010800400000050032400440f0541c0108a1000e41262035441e22050400c000c40d18101c6c010784244038080001806250071b000b102c06813040900b0445990b1022810302c005030300500303011410300c46c140700203a218500105180710401c00036070f55540d50600360040c0b4040a0000a01401190001c1c01002a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 233977949 1250 233976699 233976731
    0x121205100519380403030309061824090605072007080309060702010c060606120e010204180216060c0c02100e01090512100212040204051305120d09051501060e04 71
    0x203660f00308440701e1002c0d100003000700b01c1c8600446486291409001c41d0100138540e1560200c61f039a0711030308040142000010300003203c4035900c1001408602070100c81c160300c0c3e07944c0700c00b1940c500342c5190200e44050b55591b03400942e8001c80d0304200141800300202c611003042c0601c0415103184c0c10182c09002d00b401c074416124450486110701404000441e1030440e441303100c070003045a4008404214031620740d40024111928801c02c0c0c2003180c10218031a45a50040c4212800c48a0b001c03204184080b0a01440c4080c0d0050303030646151006441b040b002050a9001c1c2c5a580c00c0703299580007080307000d0303c10400610311007103540017000b010044040480c0d03040500c040c1500e504a40020f099229816428646644001051070a60010034480e64100401030480c0c080c6100b10360910840d9a03c100c403403180d0340240005402a0701001210080541c0940146034001c500c85020810202c2c0b5142c4504c2d02689031200b0014a15903401000f0031030f88413405144102e41164140301084007942004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 233979199 1250 233977949 233977979
    0x20d0507050c01300c030b0a0602070e04111201140f040210080a1d06160507050303010b07150c020c011121031021030908150103121205100519 63
    0x505020200e041c40321000c00040c030b00c4d04000914411000003000c10740040d009011440d9026021078106400c14910307151005040d010303108282d00610041e49003540c21699032601610584110010980349012502c4bd0b01a0b40c1c85103800c14000b007480d12013031001c8000a20001c00c1c40404100b10004d220041e0750301c10340074100040358030b88056180c5941c10b0702402031940440348403071180300c0720400e000d120010031118415100c00c0010310a2007210081903490340b2411100510a800410061203003001403005803610703134007481000381000b00c0351305030408541d496181440541e01c003900855056071f101c0500349503200d03444081c1c00c0a02034001003005803021030410a003000c00101c005072178034845055603002810350b00520141d541c584404c1181c032126442e02500040c0c500f040109000c500050f500c0c010201d4800030400507842c1d901ca50000c4005c43d0f00ca034040160707080380702d103001074075002d514000c0d0400c24002c200c580c82e0904011740700982081100346609071301c004009a0440ca0080c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 233980449 1250 233979199 233979223
    0xb0106260403030507021006080705090a0c020d1d04020409050103060b0d02060306040b060c0a0803010e0f0108060103020d050f011a030714031c11060103051606020318040f060f15020d050705 84
    0x8581c0c5d40b90424140d062003180103491034010314045001400a4001625004441040d6501061519170a000f501a14a00214540580e21020301d40d00610322484038401010482000d9000003003030f29001600341c0e40a54000d400d1940c4a000500a000d034070b20403800a9141110807100400d01980819441c2c080100354902c165514100700c880c9803101d80442d2001c4030320500b41c64460360340740307429002500203004840d00d8507520b5002680f0a2500390405050b91007601c0180851703841c560800400329011881240d06000d401106200038400740548860300202001e02842b40e01c0d00700605141c074885900010808411003000956518003103980c2d25441032881095031520a425802e40d40219084029500b6200789000041442404190802d0121506200ca4200c81c0e41d070b0402c90b03507401204040e010074111a11412143e18059004113101c030896400410711942e1411194140d40041d881590401e65604c103d029142c0e05010101c0194018101581003c80c03644807141d46059034461 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 233981699 1250 233980449 233980451
    0x20d270302131404080304050c010f17180d020604021e130e07030f030206061026100906032006040609090207030504030228081c05030a060f030b010626040303 70
    0x842c0190700ba00790000d081120011181003080d0400d490000001d90040324165454061400742c02020761180c2c20b144e00d000c00554030b207030b070100720710f4070b802c144180103030164101f141501c00d220b60300762040c40b45c0011103c0c107401600e4180350900501110311042001d05002d00005c804441540d59901c0324402d4000007090000b40710340b090404207281060940000c1d0a40ca0002488420507074002081486100151662403200b60f849406450884141e4070340c4d500d05843c4900d071079816000b028420317801000c0348000742c4203a0340c9001410885085400c1035400c0205032403000040d1110f0404480201003e8581c0c900c1c181c540f40300285580300350700400110355000103841003803610400075a0040c6030020000d8800000d104c400d0007085007408014410800400800940420040b9410b611003a10030781e50012880e03143d000311410b0744010b003400d01c00c9945810126507804030605440103035200d0f21130101c01d541820009002d01d00e200164403248039203c541d040c07050105d1a401e9802c01c1d81414 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 233982949 1250 233981699 233981719
    0x702160620060c03190606051b1c0c020108100f060507060f0f091509020906010302070302120403030203030103050708060412050903030706151401020610060813080703020d270302 79
    0x50041c9154066035a980124420074081c0710a00e80020300842c056003203408400c5c08044041c0007902a00c03101d01c251404100c060004505170944500001d680016035030645044a020302440b06000042894020008000d0000c1e0011542c00c171040c203800003400d20114503818034250980b41702820900a031400c105000c10000100a01034004005010304070409100304501d0000b687d00507e06000241c40c401e280c00655002c00e4428030805050300d4014162070116036446006601035404950220300318401d11503058003480062019002543c407a40c0034513aa94514140306180c4200f541100910350065070034440000e051010401c0c861406007003590300c4400c2000040d041d401080d0025080500f0480801107000520000b182540d85c46a101420910180d004981d00d40049400041b003080301141403004a0151101540c001a07848010f012144a9a40c208850700300d00412030150b44a0704a6100f4584c010001c050328404110722544292050b40041655206621019026000c00c00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 233984199 1250 233982949 233982977
    0x1206011103130803030a1109240903010504062a0804060c031103180d03090201050d151505180108060618120d0c0b0708060612280903020607021606 65
    0x100545600310a040c88090b05550340303d404a0b120f41c0101d8410424503d884a51110030091500341d4050000c0079140203108410144801d070420241e8258801d03480090100401a503424002ca0b40305078800c0601084c460035084102803c04a2040010104080428409062a40030101d01c0d44a6045030340401c41c0e400301c520581c010601072034044801c2c10008108207600104a45e88040e6140070400c480c0f2a10000034101e045420142000380018020002011285c10541020880600002c40c05811541d00c144d90b040c203a0350781034400040362000c552020141059001d84140c20b000b803c021041d450403a00180880c410b401c603000300349030049a12251500e541880c03801d2449190b08075a100707800d000c0040c026003111081124214500000039451511401d02c1500070a005440242081d003501c0d0a400103820050442200319250100c00500006004485008642c900000a40b0b0b41d0a401d00906140c4000d1400040d54403d200c1c0001d041c000403982c1e011079031709242107460b03941c0704 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 233985449 1250 233984199 233984203
    0x30b04060f0311011812080d14070c0516030206070b0907030503040611070b09150c0c1801080d0810150903060c03050709080a170304110a09050108011112060111 71
    0x54101d0500074180000120402c1034052281c0001c0a09803240310000e402464109994210f60080a40130103080400e58006100302c0058040e02c80b500e00c0205043c24070785450310054000301e030410001303601c2d40354440034413105100c95160340c66100d4400c5038250075600825110700c00c40310b00410040750300e000103400b540c003800000080d6601009403655165591402800e180300340e200103005008004000460100b664100c40105501410003d81400b15851740d001380d07086044a02e07814052a482881c080d41c070250f2440c02241c41d1600324000354185a803031807500c0403a07a11801400301440030712200b0340a104180e402c030f6048400342c1480c43c032024001c6031440055030006140d5800c0c039001c1d089454150708014407400d032903034402c0c020f00d90780c00390580d80e44c501d07800107050649042c802e064001c2481c002550700602542401801c0074100700416020b101940c0000e64555840005003c04482070195400ca001c50300760140c1070560300e130707181028504060690340c107202040f50346031540101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 233986699 1250 233985449 233985461
    0x150408030703050c0102090d061d06100e0405070b040b07030e0d02010c020405150d060f0506030706080c09120f0a020f0a03151a1f020c01030e060604110c07090f05090307080a030b04 80
    0x74001141d045100d181c0f00024ac96200d04000802c0325415603403d0001340010800e2154520952180e58030317181a0340115601009442a0340d6401501000300e0144c48804c0100700809a0528042e641c1880f400e0041c82c081d80c4039990703071041c200c1202d60405030780e00c0381d00ea00c0036a40440b4001525201e0042d01180b8101080c0c41d0381c2c104200ca0303902018800a80d1010514081052080c8501d0307403241d0030542c886089000e00301c0402c10310008114451241c00280c40000304c05085440750000000c0094a0f01c202c2c070a540c0e02580c801c04200c82142805060b61901000965064240300c0c00c56503281001c0d01c110030361a00d110717691103140d005844000c80f494100b0f000a4040c0951900080b40190025400c848a402500c14103550f40c0d0309510910541c1c0e100c00d00320020305007680740d400c10013000e442500a440c03c0d0b10400d01c03640e5100750040c811203005107100307100000c00c40203100c1c1c0384098800060900790160002e0141c0d0000ca003003c4d0490b448040240350001e00020304030005001000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 233987949 1250 233986699 233986717
    0xf0106060302030762040203100507020106030b04050604050708030901170a09021c030f0206070813110402031611150f041707030504050f030105061c06110d0209150408030703050c0102 81
    0x205c50034071850310080c0036004484000c020724500c0c030710105c0c000410800e01c4095400a405034442c3e0300030102580554842038011056200104080760303681c503840c0c20210140c4003911542c00c824240000c11204220700b20081074410701079420214848000f074030905202100101140d007000014002522651100c40e000d40d00030310044800c204000c0d0200e0f5480303007081c114085403048200038403907400052614450760f903a070707926181c960b00c0c604940b0700924201b0003240e04c0910003002c9c401e5680e950016600c60311103942d503074004110150004010300c0c0425101202c071380114080c1c204444440c03518590190b0810740d400c500e13031280d1815150742410412504030061000c6100d804159005004008484003102c0060500d8129000c00d42200d10a82c1d055a0151000c00c403d49400c0141c1154141580102c500040380318401c6240046640720994107609a03500203010034007484d03d0b280c103028044440600a05190408104968a200b140d03405004d1080124098042c40425012111000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 233989199 1250 233987949 233988047
    0x70504051e0d05010204050117010b0f09040f0e031827060303070804032009090a03030f090b0a090209010b0703090902030c0408031201090501090c0c20090103050f01060603020307 79
    0x261107414858000e406c1400385030300040085512444091950062a0581c1c90103100c15103044411006181558001c2580540054481c0c01c40c00051403030b40300e61220100c101c0081c41e611030649894015000318201028412a019112450146407031040b601d00b072500c00108020944600b40024607600802400403c032020009000c010095440d82424a803103000d031000f1030200c940710811803031031801c980d411200d0340071a0602c80403d01c070b6000310075821000b05001403000b01c0c4d501d50481801c03040b14200111515000c441c01141420007009006200349840c00c1d05000f80c1e5070f0000d000c12028400d8081158011000c11103e100700406c540c014140c840c100c0ea51540c8018421518200c244116400549004000564416507000700d0100040b582d5445444014542d149030384594103682c507020200c003000d101031840e11015840c03030295003e04010702e8100344235031215080d9400e94104404041c014030600c65010703001401e08040490288005000807108d40c00400780000000e0515803031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 233990449 1250 233989199 233989219
    0xb070b0a11030702010603030207092a030b3001050c040e1509071e020d0f03020d0209040213080105060d0c0b1c020301060f030623061b01060611010f05070504051e 72
    0x43e805602006c2260b202c0e40986036515a58000d030801c440b40c1c500d5a0f2007070810722070981e03403281004550030803200040c10000341804d241804155190381100175040c101c01c2c00c910303108150040410581d054032070503000303010f1442c1000403080a800b46109108120341080041041d1000f00340d47c00d1488500074000c1085403424200040ca842d144070400340b0b0020b0703000710300b8140b588042050404000940c0b1549030b46c2c049040104c0003544442d0b1129259607013485018040e654070f00040110341d06880c00d03140b105003011030742421500064100d41c464941c4200d40340010b00360903491022900d4000045448e12940d10020f40c020302840a2406620310000005c211203401115100091841d40e03000c10030503454000804103488041010711410060709035103441441c041c0002c1541c0ca4801c0c80002070031050800303450035150355403c00702c0450300e49010035050300710900c103082410541c0130041c026400c0c80c0201038180d128500130b441c0614051080c000070400340d001100000480034000c0e4101d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 233991699 1250 233990449 233990461
    0x110406080c0315091b03130201180305030415090510030c1205010e0a0c030b0301050711120403081206030f0102030408090909010c0c1101030b03120d1401061e0306080307060b1302040b070b0a1103 86
    0x861f4031000070882c0802c0c2d44460f480080018000c0410580740d00c032004528080c20700c3c10009924030065002d004108100ca004a82919000c0300075103182150740300481c1041041d000079010340010301d40d400ca280e180c0b1004008010004c1e080c0f17900211100030024800041036011005440c009400356010740c24034044c08240c2d9849a554010900d80f8410f036107640451140f001c0d081c1c030551001621081c428480c9a003075002340c0c00055088030000b0110355010202030f0303105007640c10072141500c0c00b010204042e4074a0030120050340d03001425a008000388100c1c4500606100300c1030f10301800d11440c040b142103180e40258459601e18200a04450100010703c00c05901917002c1c08044101034280069402034416501c40e56050741d03119190091100d140a010350210102d8514903810561241000110b9803824402008410700510001c10350740250300a002c0501c018181d0b005190b0f104000410200602d2001d5498299000807020000c0c1c803102c218102801c3e885850004800d000014050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 233992805 1106 233991699 233991721
    0xc06020313090c0e0a09020316031e0f0209040207080405030c0117010b03070207031406041a010506070611090604060c050d1803020105070312110406080c0315091b03 73
    0x1045408004c00201c0620281e4040c500071980041071003058420101102c0e501501c40c2001c1c800d4425110708100d01c1ca0440b402c500079596a80b510700e005003041d80440f10300c9100100190740307544540c1460903031a44948aa580700c2c0c42100d80b480115401100070944170b150204000019038030f000b000340420b50008000d40f00b18081c1450100004075590180068448008001d1100380f03410728003182e80040072440d40c010000d40d03c0c010013065407080220f0301e0b500d901c038034040342d42c3c400c40c0420525401080304255004c1030200303010a40a41c41091390301c9642c042d1007101c405203100042510042c12008441c10501004d000c1031001d54000d0008180f858400e01d00b0041d841c1e0b161020344105d0710729810b80326080e0341c00501080703219030080702d0682080034a44940e1441c180300030300d511290081803071759002d02201d10004410750203101c140809510540c0242e0399a1034039141035030b = true := by decide +kernel

theorem cover : BRFrame.Cov 233812949 233992805 := by
  have h0 := BRFrame.cov_init 233812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 233812949 ≤ n) (h2 : n < 233992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
