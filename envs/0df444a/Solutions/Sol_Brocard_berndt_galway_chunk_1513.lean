-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1513
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:20:36.163362+00:00
-- url     : https://prove2.me/submissions/3f1a7631-e3e7-4a11-9a41-1464e44a6e8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 271942446 ≤ n < 272122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 271943696 1250 271942446 271942457
    0x100c05210118060303050306010f03150801060f0905010e073c030c0908030f0705030d090807050607050301060804260c100b060a0f110c041b02060a09030f0e061303080307 75
    0x1402c90511a100d20300650b501602c0d41821682d80074011140701c801808034008042e21403c140d10301500351a6244003400840300003181840c10704142e0b00140c01e80c0d40c031003600c880c10100100000e070700040403980c00004524040112f00c00e809682c1c00c4141c5445501810101c00b009103803484c8280300305482c280800c1d0740d02480000d46402d800c40d82440c00d40259680b64004021000032180440000d0603498800c00a490600403a101510b08803203c0100c20344102500090801c04c000d0148400755000368103041981c210b5041820081406a000f800140800107030255402d03040e05070104056105140c4c03042d103556004000e07440307131a08007491001d04010b003480e207110001e10b03001d400c0d00d040c400c8981d111203070f16034001c0302280c031080010582d800340d000315500c090741a16240580d000c1c11170150800325824110b0b141c001d190060003400824014074081e07001001030b900c80c0048001d81400d18005c0d2031400301400055061040f9400300c040400c041800000700480940070714881d443c0c2d511007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 271944946 1250 271943696 271943729
    0xe12090f180105130f0f06080d030c02071214010905010b03010e0a02300106030516060206060a0e0717040b04030e120303190e0f1b060c100c052101 65
    0x14400e0105410304900c50192042005000f9401c01c4c114900c11100c00c10004514014180c240c0b0b41111116080703030320340136140c0c107080c0f007000400c000c40c2016484a1404115102924000075207894103030142000848101c0484c00c244082c0b510074001a60b1050000c002d00742e00da1034418004c0c070526a00900035401e082c44090f22070000300d4803401054000e00741c031a010340b8090b6a0061004200031009903112560f000802da00c609108020145100354000e010203d00c0d07046604440c041648007008640c4031604101c2107407940c40d4003002300c503001114082c650300c650b00182e031100f02002903c2d1039408031074100f0080c800c4030100140590700a032105810301d207000003032102030503012410001503401000800c1140c2400085889e901301000000144010000189424075a0b40303220700f0796a910000582c9030288040310341606400044481320321b800011800c0640f2500c0c0c2000850000340d844140390b00650241040762114041c03c43c0e05140750103240c914150206081c05800b41800a0420 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 271946196 1250 271944946 271944949
    0x501050a050f130504021c050706080c04050f150d020f040e010e04020120120a050a0206010b1c05090325050c03060618090a020901090b01030b060f0403150e12090f 72
    0x9065403209016110036402c1c100390102402600001c5e0040b82c0000b00181c03051002110700d2110080c080c4120082c2083d10f00c0c1480c0105101c0015140c011410b000700420030060307580700f0640711095402d4070500c542c2c00300d0315017061140c00b41a02c166005030000070300b0440c0f02124030042081d03e0a608401d000c0381d1b00c81002300b0036603100b110b0090120301d240d001c6105419140c1400455107641d41d04407461005842142d00d030540280d051100881e80104500801c0c0c0e40502c121405020381c103002034145448400c09040700d81160304500e0f81c1603901d00100d00308680c140f04580e003910154290828524035201654002e5a0012054450b80190a80c0350791510340440d6190103104010107050080a01484801c508203010b041d80d5128400c2d06000001616112041da000f450069400520b0102c10130014064600f00f5000307501c80e0741c04222405003034400e1001c2e90180ca401c47d100c0b40c1641003580001c00140000a05c41ca054841d00c154108085102c8000740104c050a581d801d140301c2c040b40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 271947446 1250 271946196 271946209
    0x602011103040822051509011e0e010309083001090c080f060d14060a0b01090f09020c030c01090c1406130306022a07080d051e07031e030501050a05 65
    0x46004020078004c00031001c209042890705a100c0c0d0300120f40b0004141c2e180d000400019801044407101040819485215078000d0888600f020309220701000c1c4030441c141c01880c051204c00c413a8141542c80108900340507120080e2000400904800001e039081c04208040d03d1011850200710103040000110300c8054a0207078404da80d0441d205c02481c1e0f00c0d4040c1100b880360b001081640c02c1151282080080340301d000380c0b804165840006041e040c109840b81c0c030195010742d400941030204101080284400142c000781c1101c14460005843e0540906440e0440c490900c0080d91982040c00c0241800342442c1c800c1d0807564a0350084418407290010b1100c18000d40011161948040c40b0030404036460780c00420409000304a05800c690b400c1c0c0103000d0030040203c83d0300d566400399034103125900007000000129021707414942d040000e400305114000818410b804181301001c40c0348070406005000038803000000401040540d880040002c000308000d214a80c8541c1c0000ba001a4600b03242c1d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 271948696 1250 271947446 271947451
    0x50c0c0705060913020d0b0f0d0305030a0c170414010c08010b070209060609120708060c0304021011070b0f09010306051518060712120c020312220b010f0602011103 72
    0x6409000da141c9080304215064100b0910650483c0c41d0381c80c11a008020f03880103050203c584040021006041800e00446160f41c19142e405401c03003807119404130381c019095a07030201d800030000c128450603a9003154009c0d05801403c2c1611000c0c42800104480803040c40101d4034888020080c10829850440361554288504094a0420042d02003d0b091505400b80c3c032101c007801c100d01d03140000c40451001c03814014203005a801130320081c0400300050002d9504100788048890440c20585c000a040c00c6007602d810007841030741581c0100019051103400002c10300071000710344a44035101c0e110f8050340000503290000f848c1010108052408101010002c043d00c0e007010b0800c07000c010039601d2400e03901e05403540b000d401d00803180010f030060840310196106a44072601e1040209040050740c0c1d14094140540d00300f0b002554101c0c1442440c2580402c0c020381544d40781c203004201500c40100050050131100c2d40100104541c0712140304002120842c0d0700030000e03000301054032002e60005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 271949946 1250 271948696 271948717
    0x1b010806130f110f04030606091a0d0507080a06051e04170901140d06030201140f161407080d1202030c090d0203070906060e270613020d05011206050c 66
    0x30318500d0309000105902006608412110004000030003285038040f0b908261138214900780000350600c104900c0740541c41c01040c0c440400d010710400c0d03c40c2c482940e112100e0190081c04004024000d01004100207030081400009407858625035041c50310140104840003124003a40d108029594406000040d1043d6080790302503036842c2d0005500325030756210000c2c0c9810800e091800d81c4040860100a00c0c85400c00d0500207091840e520001d06500030010001d000c40c0824040000344002d00d40841d15515103212140c80c400c0c0c120b180480316003003102800341c6107100d003120100b01e0441c0005c600c941d841c01c907240c0d000001d03040754149061b032104071600c0c01c070002c050000c02810305040d00300c545514030040c00d0300c01841c0c90b211903004444d9142d010400080c281d2151314410700302090f81da4440011031105208100e000d800750b0b8030700c40b8007400b00d038040c1800c0d05840045844039810340f10711041d0000180540d5075610b00081262403101410b40300549007c0201c1c001d03003400021074450401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 271951196 1250 271949946 271949959
    0x14040203060c0a09030206120f0603072436090b060415020a14010f0f0209090402010807050d0c02030403061401050d03051c05070c030306090e030f0306211b010806 72
    0x1030320b80e441c1d011078110310711640030301218180c007000583d02c200c0585050729155a2076844da2900c070034101b20404001c0d0096000360400ea105000045581100300404c040207903042403813032138800d011107000d15030032108240c02c250f0010846080c2c01d100c00c2c01c0d6804007002c0c0c04420890b25020b10b00d040b101003458141c2c0c881000c00c006c11000303070701c00305044099000e401565400c81c49510f480b000c1a10326041590340340d543e0300103251008864030403241e02c144050421070074070340114040b400d603841c00380000c2c0c10301001f0b0002450f018491b600319030001d03c4135001808202c05e0b020010b556500680411210241041d1494001141044038a812164010708924040340c89031009d4a06502140f403c5009041c6a205500041d646001c0c1500500c090fa95041400d403280c10700508441c0182c0240c41c1480c100700303084e584c0c0c11000060301c441c40b8980745660303903035202c41c00016087c201d44034515540f0310340130b0300d082441e040c0401c00d81125403204c0c5c0301c50812140c00004450942003220555405070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 271952446 1250 271951196 271951201
    0x606120f0216030f02070f030210030b0a090c02030705071a0306011115040c080d092402101a01091703070807290712051b0a090b1c1404020306 63
    0x842500441601101410014075116400004000341e80040b201500070543d00b0b08440c01441e410060300c001800407198052680d070650740007030703074112504440c24100340e100c51400c0e40c1a903074400032000401e1055401c1003140b050002c065203e4005517800d480a0280c0d80000500d140707080241f20000c1900c170079461a60380c68200541d10103401030030804852041c0a0310000501d03003100000d01481c0a14640c0d41c0c00380ca42100586001d8409825000f0407401213005c0110b07840a0240f0724080e4501b802050000f081c40a040703103003003440e1903001410b80c14072003046c80004138040b1415072408280d89551200751030320003140e20b41d0305011482805900803c42d0720007003030540029004c450300c684547c06c084aa0703100c100c4a21440860503c400452407003e02516503080010101921403210050001c0c3c40c0890005c201c4036000000e00402c03840c009029104148203945000261516a61040d180d4103800b0034110341301c04900c03034024a50301c0d0401c800f014081c1440d0040c4502c2c0c1c02801011281d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 271953696 1250 271952446 271952477
    0xf1701110d270501140108011a0108070c02041407020d020a0c090902130504030905030f0705030c0d140618120f090415270c170c030c090909030c0c03010606 69
    0x20403411601821030b1808801c0b41291490440e00c4080681c092400401c01098855164030700c18410703031100354560304d0305c400d2043e01062881c0c1c8070340002007420556070907514541d051700c5803021183d0083d0700900d00b000d091072180c1c8101503280541284d5080382c8000a9a800680c1e88982001010308038440c440341c20040c0c60b0498001c44070681c405050600070b28010680d00060301c009544c03c034007080076944188814101004250940c1441a00901c03a5a00d81070100307840d00003000d8101c2c000c8012800c1c0600340040408241d13099140300d0200c40741840c162104980c1e3328038084070114640a41100a1a0814040c0c243c0b60f4601c007081c0d0140c58203510104010007058460240305c0601d0100070002035005044a03c2601d0039103003000302580c910403201140c110307105a02c070315092004011005a00e00590b4207240d1b4401c0c1456080b540da9100c000b00c0701c4042c0101c800080d4000046410003116034004030160480c20020790840b201d40d00c0e450201401c1e0381950041000099074001c030030508 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 271954946 1250 271953696 271953701
    0xe060103090c06050c15010f0e1b0a1706030a08031306060305010f0207140706050702011b0c121b0503100b040f02030c0306240904020304050f070f1701110d 69
    0x1014100092032222541d039006800d81c965020801040700402c000803446000d214110055071b045660f048a58180101985014102c1c0540212140b9000c0050984600c080c4540701c650749810985403102c1d02039200608604924940b604041c03031500101e1558140000c0f0038040c0c540c0103072620f09503503074400005103100d221070046d2803413500e80e04000b000c26020300c58010589082000035985454900b0003001c1311001e4881d03286585c5c4192004c2089641c40740640d0561542460034003048181c6044e080168105d85801409078001c450000807414078041003c54403911506070202e015460325103828004000344180c07a00740e0001c18261401a9041e880b0401e5140d0003480016a4101c807113150301243c00845640c0309004001045c4425442e0a14480440380da840c0302c003601031003420b64000b01c140121181d250003240c01002203801c00005118020b40c02c000c1c4001c40300300b00d541c0c0e4081201ea03100c500c00c070820300f921803280d005108018000c540301c121100300e0313040c40d110207803920b20300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 271956196 1250 271954946 271954951
    0xc03191509151a030c01020f3a0504051f2307080408161203020c09040f0206160c05010c080301260d0e010314041e0c0504090b0f0106021203010e 64
    0x158440210b0310740084903040e11543c54503401c800c1e209400c4480c0340051600c0d0080c4a40400d0565000480300c448400b400035109040c01058000e01c08001d251036030504042c0c604010400c1141c100d07076500d0009540c0300d00580708540c0b00302c540321717001d1451060050313607050380441540000360405408507007481c1042060190040c2e00c000b403840d124168941040300e4101d90402d04094000085003140a8142207800e40036003121415242d44600350f6030007a40c0c40c258207920a00500d0b03000c00203000d0100c2c00b80d50341503051f000b4004940c0c3c1c101c1c000c1004c0e060054040c040311200444a4007042d2075124640c0c503075a640e440310241e4990b900f00003101552054098081d025200401080110043d050110701e090307071b13900c0d00c5183c1c10101500014041d121002181605020308508000200340200f20803000f4141c0200350341034481c55424100c0748070b038040d00241d4202c1d0a00d1400802c20a01f00740d001d21540b406803410708140d0320b404e004c98840907919400c040f2000e081c80144008a1420b50390342c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 271957446 1250 271956196 271956203
    0x12030507020c06130f0e090319090b040e041a070c061d12040e280209040b09180f070323010b0a030b04032304060309030c140c03191509 60
    0x10004488103000a42036800841d2a4588125801c0c0801900c0792020458014054010894011f49817000792981d0783e000390b009214140404003541d000c524000d02100000d0311405400540d03a0741c0b140c00410804500307807004c88014001c0407a10a03044e03031403090280078044603903462106044c551680ca01400c500000010611100182100800c404029802184400c955065181d928120740c40c201011300030040c0c10440c051015203c80d03203800402c040e8900008640044e19280f048001ca001132048040568206420300d05100d40b07410000c0103501691804000c45146095008201c0d44600d142c3c800141080311011208840b00d0504c09a0094007400c0700000403142203090009030540b646c1d6006580140010b010300c000e05900c400c0c03100d4618511184603018501055051080f4131683c46004105541ca030045002c040c416603d410180d600103482509420b866655292100c100124180c424801d800c510b8049040190b018640903401070403080e07481c2a116100000f030000000e044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 271958696 1250 271957446 271957453
    0x60901030e01020a0804050f03030f0609130b070504090c1e0305190c0e121506120c0402030a021207080112080a030204090e0a06050907050a140103060b0c06090d0504031203050702 79
    0x26070a002d1024281c03503241a07640ca03000f030600f418102e050100a4a103420b02c0e810410800854001d18480c50b6007007172094800002070343c0c0e807171201c035807450156400405400400702800021a80880580241c2e030640d0002c010100310908159900c1c1855101a503002c0020120300d501580290300c4103a0081c40926107517102c10407040c40d20101c8202601c8880841c030b58188404660078064046145108007100808140540810610003180c1c01443c240c4a000404000c41500c0c10501003031450040240c4199100c1c02e01a1110010717400162042c1e240a040340b000603e0984038400960407140ca031140901c0101c60760303e4031903840c0c0c01206900c080c182c00b0000042ca4010601c605800c150000c1c0c0500302080481ca4040d0503110042d010440e0744e030080e0020300c101c8d0340e4407003440b04a440800d01c0e02c10034008400160040e01e855400070040d01400318541d58428030102d40d5a2003806210709440320034103008401c0e0f90714092404060302d03c052079031102400900991020f6001441030045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 271959946 1250 271958696 271958711
    0x905060304210c0b0f010303021b2706120102030106090b0c120319201815030108030a08010603090f0b100f1205010506060a0e0d0309050303030709150c03090506090103 74
    0xd8006920802c1000c0300050000c1c01c814180000140100d400c042ca014840b41e0030b505d90348000f961100301100600360b404284040600310f940307801c84036403074048503601c50001003008080c004403d4030403282c0c54050800c00b440852209010301c00c5906079152503c41d06111410002c081540b034208400403141d0744580400c2c61001404040914411014031801040da480c204d20803a003903a1409060f548030b07040c0b400019000d1760040c03007503841500160804c1c60540151400007400b81584801c1c217400d40c1c00020021803070600c013000400350850103880d03440043c0d0382e41a0403000c1f2078084c1c001811111140400f040060622500700b500000500b400c01c0d80f9035225608600c095109070301210070240c1054230300082002c207001c0d10ba0300c888102c83c80c40c04c28990700005440d4915011440f4480c40521046804041c000c05800340a843c02404607a1030740f506040140000055000741c41d51444480c3d03c1c040000c0c45803441260542d8159140c4e0714240c60039060007102d4112080da20b06041e1074a0350b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 271961196 1250 271959946 271959983
    0x60602151e1303030e0c090105130b06030108010905070611070b0a050910030c2309091b07080406090b130b09040e0109050309010f0c0f032a030806010e0307060905060304 75
    0x40707000b5070041c040c04100000e00d1801038204c4210072400c0f0410f030030020300e46066554081301141120400e8803440590381c00d03058600020146c0044c2190700c40310100c0045440041503000c0c4071124442c0085441d02c9403500300c01e4500007030900142c6640d6001d04001d000041c0d00002410304100b1f14184141040701040000b111220a041b520340040d03580c6901400362640320030364407142c040b0355200884031a14070f9150304079446184507960141e0414008610300000c4407560070940c0065008081d116240e51800304800d5025118940001e1070003100810404007402c202c1d10b2980500c0e1401344031903d80681250503402001e40d455001f80e039905640780d6400b080c0a0040600e12407005165580d410b40005041000b00b02c52002c108481c151440002070045051030708201d0705410600080c01c00904052040c0020f58400340001c00c14a2200e030030103800920040c01178900340c0310307207007000c010401b8195103040c24130948000800340601040f560600c0300c002c0d0b4100d800b84c1600300c0c0c1c0c400700aa = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 271962446 1250 271961196 271961251
    0x1051b0d020607080c04081b0a26010b0a060804020d020a05030f06011a040303050f07050a0c180501150e19051f090504090b01060f03060e0109140a06060215 69
    0x3000280982c200ca002c0048540d408114203922956504181d4146030401001036901d004191916a1360b820041c4169400d94540d0b0b81d4100404080090345208a141021308000d880a00c034000c0080d070030410700c0074841c502441f2100580b0240d56440410750b4868080112441580400380c0e08194614000700307058030280b14038170460304801c004088175450040c1c500002814a8400c210f100014001400000d500c001110038004108000e25141c80450509a080c1020120002d043c1620315a001a5003000c501c1d58548000f980764080003280e0f43c42440390703d44001052810b00081c0002142d98581c1b03000468820380017003044d59111400c1d19030002c14461541c00c003161120b400210f44210038190700047ea100907040a513020f002009099440e00d6400d1410300500c002e01c4440ca0604040ba0312a90160008200228551742c031035079030316901801030640c40c40000081800c1c00000d42e49450b039000d458111545070b4011f0070315080c07a0b9082d40a10601078440100011610143c00d408039805 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 271963696 1250 271962446 271962463
    0x4090c0b07020a0e041208040c0803040906090b0a26030d0c03060302030f0d050708030603010b10050301050a0b0408060408031e0106020c09330f0405090601030209220201051b 77
    0x50a06650710900d00422581c00c0480e444920181356a00400c000501d11804d01070b001c40060801e0340c2561564a8174208102046c3c0100903284004240001d80714410b030402c00c05ca0380c44440802210048009102e0204068025050301c808990030b41e10541c2c11f030200301d9440086a0040c0c904040f142c4103024140e07007103003107070b0b40019448100920a5141c280141e5007006010b00c002c01d0304048a1501400500a00710081c145140c01b200185071520203421001102d8402008406034800100028005030002c1c043d4501403c0980400300e94400440f00700d8055818200041003e9a00c03a038407806140d00082c4607c900c48503409035a840744101c0104180a4800c030340281040b50210414030440c0440140038103406000219900c0d008840705010b05191890103070305400c981c00082c00700d10800b079070403101d0350003501d418100b01d01d04c036021a80605991007102c52030b03a2901c032120300018581104404452201d14071440310015800360f4010243c00d103040c100c0c1075100e00c800035a5810440c50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 271964946 1250 271963696 271963709
    0x32009060f19090504050705030a11041d0a0311010608010b030307060507020703080705030c010b1005030f06220510080d14090a1a0c062202060903101b0228060b04090c 74
    0x200c84c2440208041400503001618054005000424054540c0b804440708103504d43e0150f559400c0b00c526068192100d032007208254001c40f41440c020b413500505410302202c00800e59441d0020202d00e441042c010b80c800d01c90024000c40c01d1a0700c2e5100c041c02000098004d5003503204080000000524240140103210300400255856039503101019080d14072107020644900c400020407000c00f40c2007c240d9030842044121940e0702e41d00d403008070703000008541401840151220b043d4004c01c54940056124440c0b00050507000c0381c0d1200c000c2c0d5107080c60074405011614402d01c00f0305090241d4050840101700078480f0a503540e4889a945070700e8042d81d0724050355500060481c1e4143d8003005a240c200c540a02c01d0000041071003c2c1c030700c0782612804000e102d01400550225203942c01c103c402d0f1500701c0288200090a40707a07039000d08111880303000802600400c44044040111049911182544881c15142104031540c61030b0041103000e0400c0e070b206550b0020f00c00803400c500c203041c020340b0300e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 271966196 1250 271964946 271964951
    0x603021c0e1f0c120c0e1e041b0207031b0b1b15010503060112020d05071401021e0606040c0210091212020415030504020112050f01032009060f1909 65
    0x1144070700c2c07510311200d20602201c141005401d40090381c0c072054510765040764590000702038680d060210340c50340c0e41c070200c1641304000c01995500120783d0381220b0180300e0b084900304070b00c110107a581c1d014680203140c08005078206108c10004101d40603aa0441d005400021000c1c3d00d45516064019400a40c448000300c0c0c02040d02c5010400204820106000c180c1d0403034031258508400a0b6886405004036800036405149080441d12401c010b01c00a540c05001d55448039241d1491188140704401d0050040c8200341d284001702100d51040b0118442e02c0c006040c0d1551a001840050b1003150240001c40c4945207040b0195181e40c8541d100040c410501030301c010420800043c078401c4480c08030f6010300e20421013002082c540c4003000c0c0b152841b034200410740d6a140e00050703c01e1550084000800390400c01040303084041c254129058038490054205c0400304001030303c0c0040ca0f03485000b40c001604801250480c034000721990700c1c01c0d0700207224040c200c001c150320034070f9102c8541c411000e594 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 271967446 1250 271966196 271966213
    0x81e070302030f01051e0f040b0402120403020118030f030c0507080c0f01150f05100504030c14211506130f1a0315040602130b04030b0f07080c040603021c0e 69
    0x84001d0f00c01d00500080391641940ca10040d5460900310405154503c01c03603005007035004903184c98000d9207030050000e00c11902c1d08100c900340400a2801c0b01c040300154604004140002c00d4601c0c044051905070340d0f42119003900d0541680100711154820050103001e00c1507100040001008094070b130f2083c4c0281180f15403141010b03080d1101c4c901c42981c0c50241703079400e01001056440d43d40450350200c40d48003900307089060136605440307250006801c02c9040b040c00700d4000c070b452030852200d00301602d0ba010303072501030301249619510704200c0d2605508a180003141510001055035084080284082c00c600300b4002050121480e440f05d60340c070252103200b00302c2a01c10300001c81601c900260003500100c03c0403007171040c0c00040117000811580d40442e007070341c50b10040b6990001620081007413a80c0c880d01c80c2495592a80200c1d408903a54114100141c46c1307600c00c01d1814040c64500c00c0d07013400d09041c218154042d4114026411144154402c1642c0600980c0a000b01d491504409048002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 271968696 1250 271967446 271967461
    0x604051201140106140f0906041d010f301a091f09080913020903010507050913200c03070f0f1205030624130f150201050402060901081e07030203 64
    0x1105078800070900c12000360000c00c01e01051700711040c1e6032103c2209580c41454100045981c040c9030417184500c0380ba2040c03007001003a8010554141d44500104205a136075801d81a110389080052829961184171200b40440c208098044146445650113061481d507400c00e45803c15801c42d0248265442050500f15008881d5070165803958a100b080c0011042601c03280342c0e40c03241d80203090040c641d83c03404500050056040e6a0a00b02c010024461410012402880c94100c0c400052040b2840c0b21004000c0c0000d20580c00c45041101090f001501141d03035825003600708107010007050004001c5040083c4420b601c000344948618000c01182c1c00c60306000605a880796031402c01e2010404c1409242e6880600b0485459040041c80b074401a101000c0394950241c0d00803101721941e00000072403002e5400b0b10f1003003517503200703141420b0000d04058200c3c02e032a0250f030082d411a03003c0050b11425440703101c21650000b40a4520801a0b55a002c9a00541802c44095001076804000d20400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 271969946 1250 271968696 271968731
    0xa0206311404050f01050d0305070c0305060a18020102060c090103060504020d021209160302222c01060e010b1b030a020a030215010e071133010503030703120b0604051201 75
    0x4208050320b00700710074a0a1402241024418019103115102e02c1031003400b058422000c56113210350000e60010361541e01d00e80341b41d03601c0302500e6484000303080c04207007a40702804540011046405074018203031500c80d50b03103180159211709031007410180c5038071000c59a52101d00080c0301c80c0324404001643c1e1055144040008a006032407040290040c00f621308040600880310406c0e42d804a6074000a00d00c490852404c803d18401c220a956081102c00b90082c90b401180e00c4840400c441d420002454020646080341d0f0342c0d0040300c5d00682c4400c018854000030724060322100c01005c070546104806c0741c400300d240da08a0310105d0300591010a0303080400d0f03414400e09208405610313183c9455414440c102c50242c000412040400c90020842d101c1c882c3c04102801000c5c0c0f944910181c07001c010804003e0b46d020800c0800010509000002900d05001049505064143c3e58076039080070b501c80c07508094540050080d602807028032000c10983d54612100205165070400042c2c0d102d121a1001076 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 271971196 1250 271969946 271969979
    0x6051e0414061f120606020f12030106091404020903070b041d0601050d0515041d06090601060801050d0c05040c03092001080a270501020c1204080a020631 68
    0x1401c405080510071a40c50303880106074084006079808000001518003241c40c910800440c401c00f9003400c80000b0120703008110321080d403040200307071b0b0348003518070406d003445101c00e04c14180017542c029002c000c0071600354030101c50017000410242c07424280300c0001c0e2030130800790046007124100040400045072218905a50292100c500007803603d04180044c046001c0e9110341811a0b480b900068030410080c5024580040001c20070002e0199034130110450310149100401e0a102d41008030302c07240c10014203e8121080c0e503035101e500b070f82401c1c14003007280061b00701141e054040d0200400c1543c0c45018030301c00d072105075800140c0f80c000ca0801c0824a10001140250640c0d0b01032030300381503640f02e503805074041012540458a20300c0c80c02c2880c02c84c40d00313184000305108a17403280b104008040d002800c100c4100405c49450704000103010a052146100340626130740100420001403c0500c080c02c2d4800e00c1460600344080d4000816400c0c20f0101d00704102211210424098181a00a00d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 271972446 1250 271971196 271971221
    0x607020109020609040903051b010c1119030f02070e01150e040e0c040b0303090301090609020306010503060c03271006031416090e0f1c08010e0609041506051e04 71
    0x442080300b60040b0303c41d0322035021481e000b035468000c040300340341c010000c80b03880412070410310100030640c0841c1402025248054400202a0035485141d0b050024400c945910080f12080c0f105109540940b025030600030310200758041d014000034958540c0846038000e107040b1500b8650419808030040031407103040405880344d071510011100c80d0342c001032240072901c02500e000544225080000b8610300038201d140340d0641c244009a0204940c94200e00e2200b4401d504851130303662510109038130341e48100d410781d42120090000036118000d030040b020b04100981d01c103403e6480c008444608184001d16156440c41c0c59400030010070044840c242c903c00312490107801e0314100c06090700079404285c483c040010382c45000c0741114400c103000e05030748409003104580341c00701881d9880200d4089164104080340b030340000040c13002d12041029106000003400064641d49a0340c0350103504030b1007002c17013519543d246c0d0040381d030341c950050301280a092408200000700d0707800100000e0340d07010f40b00c0c0c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 271973696 1250 271972446 271972451
    0xf0105060711040c03020c070f0e01080724030207021c02090a020901141b01090309170c06030c0a020c030d03140a02070203031207182403140a09082101050306070201 73
    0x19002c80c1c100803500c02801c0040328042186404084214040c2c0200c0140342c07201d0003191400152103955240ca030341140c80b1041101c00d140e994014203901d801c00e41c400e1510f018048a0003a004182c400100000038030542001070400301d458011481c501b4003000380c003420303400c424002d07010741c0b502900070f41e4451003c007000d51810b03071030030002031405040c80c20b6004503910205800d401000011210140ea005580007081a2a81030400070a901c800e881003202002d00d01500900c5a400460869203030900540250715540345d07000c000d20039501014001c0c0443c003a40e150102156418440c0d01c0411070325603404034040801c2e12002c1075000f00985509421841080104010384010054515000d80060fa0013000e41c0c80075419507442c200b8100c0c4100300070761200046840ca011944002c41000b25000241c04118440c4080d021519101d1010881c005a84c0000b00350400f550050741e1943e115821840c2440d041d100030351500340c1007803000d0650031301a90040c405410f0070041239920a480740b009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 271974946 1250 271973696 271973707
    0x804171303141b010e010201020717070215030402061c021303060b01031410030303090302121c0e03031b1b16060f020d0f080601350c04030c0e0901150305060f010506 73
    0x3d80b15075203200600034140000c000201170707168003e6054810300c0d0303000110282151203400e0b0512013980007031030407031091580710190019622480143c07481580d010340748902d401c1d109411001c00070401e101215030944c0070040700d55416000c000d580011403143c040891400322410014043e120a8060804103100b01c3d010000302e0842004031108072038050a00048440c05800c040742070540c1d044045000c54800965140d1082c00c1c070100d608031650f011001c100c40b10911780314646a100036542c0ea880c4132040d90010007444480802410750790080007002d4903a00c10006140c0c24030b8403070f03d40c0100d4081c00680c100003081c1c01144241c2032400302d1018241e041b40011018101c441c04481200801003480c00091450340691609143e00030308241c440c18801601103d02c54040300c540c2c144590038894004103401140d8031080c0e070180c80d40003c2d200821400c28152104000c0014400b40040d92182a51040b05601e841a40d0180d030140000e401c0310f00d0301c144050b08285041e0301403401480308121 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 271976196 1250 271974946 271974973
    0x31b0c0f0c011d1f030b09070c03021605010c021216030807061508031603140d020d0606111908160c090b010c08040e18030307030209011d010f080417130314 69
    0x1802e1064614004052103250900130100c000700b01c52444540c000c0400f10900400742d0b08240c0100d0400e00c80d608481201c3c40d00e64440e0000301080c82024042004000ca042c01441c0c0000f00d00744140410301200c040c0e50031750030308120307d580316030007075800e000e00082200503c0154000c00c030200f01c006204108040c0750400b4540d036072003810000408800c0800245007054030800346640c2e02603020740c0590321001d0b507900c80802907203c441601c48103803500c10002181400f461000780c3d4220307148042c00c011200038909009200b40c8030812541c6800c01c04c00d050811000992208a56001d4401e42d03034007a040003000c0c01260040180780741880384017003020000034101c000b01c0d02520004c0c40e55104588403081e2402c00c18034000080b02c0d0500002c000c004800d40c0c554090b03c603404013603803452009440318000c03100080c0801c104600007030060b104c444981d40607041494220344500840f02207541c0020700010306810245440c9486802e010081041c00422007000301c9200d078003c0900641243c610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 271977446 1250 271976196 271976209
    0xe06090d0c0c030b0114040b0d030203040603021b010510030c09060e060f031c02030c0c22020f041802040501031d1b030a050105040f03140a05031b0c0f0c011d 70
    0x38192040041d260280010402c1400720000103540c041d403613450740c1d41c5540451402406a224403409940340c1090480c2a14008207880409901500654a0241000c01c124060341c85841140c7c291042c00341c002440c03107424443c0d2841142070b0300800c3e52460861904022500d1958810910f0a00301842801240d41c504481600074004a034941d00203040440441e04112030001e4008480c601c50b80b0709500550044000c2c016000c0f5107040d50f103002c66100c201308200c40b8035103641404444600e01c2d010889040d50040c0789124a4401880c20b11341d81d001054584e40d242c3c0f600c4100240c01190400c12940c05000360300301c0ca07540040030301c0c1c01f031200301819540300c07107484030002200c1d40c0f1041c0f2040d94400348810f01c07c0781e412000074092031500b401c0ca0321901d0b099980c1200007506989119803403070410002d580703c00200740c0c1c1e0305103903448002c0340031100e0390502040b80400030108003001030840100681c500040011002d010003c031980f00140c044405006102c15091200907890119510748 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 271978696 1250 271977446 271977463
    0x6010b0406021c090b1305090703020a02100203060406030b040602071b05030c0906040b060c0304170609060a1e020a0e010305150a0e2205030c060703090b160c051b01030e0609 77
    0x2410030400001d00002c403180031180e88101c2d48400001002d451441400303412105036201980d148d0341c0d6881c0d0050480c00c910a10802c40010b801403804408000c40742c1d001035411020040c8081340740c0351a034a41c40c020340825102140d50f1030740042c002003040080c07902000480b010070003402c821171800307003c03c0e2520581094948540440d00c0014030300da41c0d503407000180300c0780900416115200a480d250ba282d02a006000506024007040e08124600181d01403040440d800a081103840781c401307020103014500000c000440103007043c41c0c907940f1144040d003281001643c0c1c4014032545400054219600606031498030140301c1c000c1c51940c1c40d010070a43c111401429450000d03075036020b103503014665050716030200c10290000c10701407007000805004070050900540d0b1917911414400d03000c4076642080101481c480600140b0300d054034802d180b05140c0142041541c2d101951385090918524001881c2c01220445503c0c0e4103591500c030b034207082004003005190074105241099034440a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 271979946 1250 271978696 271978723
    0x503121f060c1b090e0c010e030102030103020f0d0f0b071205090a0b07120905030c0a0b1f05060f0d0e0706090512030d11040b030c07030809030324010504030c1706010b040602 77
    0x1003540101005001c070403c0c1d00401407a03004014160848030916211140c400d010b03400100034580034411840d0600c01c490480c3d6000702241040b4560000303200c0001081c000c10b44004080b00300000101c1d5040c080c2c030b4071824450b515542c09404041280e01101d0b80501200d1150f408020601c000660405c03036503410a44e070b0300700414540b079441300001c050802d101d0b001300140030103d8022840000003541d80345043c41400c070545c0503038409555038010201500c4030101c082c0342d44010081424440003c2131444510f016051074083c458030b80c84242c5001e543c03448003036408040c0811003a903002c102400507101c01c41c1c050103000b943c0015255079025000c2d010440036a2100d40221803e02c04040398000e000d008811603ca107480540c061440d080010103030046842d0400040029002100f181d1040020010400e031840d4034041c1403070030700d01010416050240070030021000c2004c200d440e100800e07005192800c1840541c10031800d003d4183d12050b0890818041405015008203488006145 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 271981196 1250 271979946 271979963
    0x40f03030b0f03070f06020c120712020402040e040b0a0b0103021303022106040503032502030d050406150b0c0d030b1e041407030c0906050f090118030503121f060c 72
    0x55440064214010b0b03480680c3d00d031261030300000e11480c41c100040112040e9030203541c2041864000c0c8415075403602c1b021160b6400c42d160901c9a11060810501c030035002410040c02c151321030080e0001080c040e541030705c080e10741d0001c100e1140d03214003890703054920a1800350b052000c505c14200c06013455000092140780d0078030081c41c1c03074209950080340003862141114018141424a0f5840e540299840c90016505500006c11181140d649000d40c4045038011458042200c1480c001030001603c04c485064848102d149000c400d400110f02926891403a07681c0c42029002243c0740a2800c00603400f89400c1c031075420030540c1c4492030030826420008914100320f04401c006001022071f82d040c0100014102c051001c1140e150b80403030401030303558a96803461511400305888038041ca07494555030380410000c60545501c1034104c0400c1c00b0030410418407842c1c40c0e907645415500000d525508002c002c00400c6aa1106890011040b01490001c2d00d0202c2c100500204036440144003d0000d04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 271982446 1250 271981196 271981211
    0x6070f05010906020f0a03110f0d1a10180e0609060915030a0b06180405100b031005040f170403030c121209050c03070b1c090201021c0c021305040f0303 67
    0x800c2d000440520781c4440c00315550032200740b50324020f820102c80c41c000a8548010314410f040020204c80e944070006c1c08541c1400f00340f030040b50160a8406002c3c100b40030300440419282c442d6120b0501c508403684403002c2e44000d8607564950216940d001000d04c0705032005005494844601c01a0003003400d882e000c1e0165103000f05980c40502c1c504085406201345400102406140e01503503014500842e55035014001d101180c0000c03842c00d80b07000d031054200a5241d41a81c190742d05c4802c00d11001b80c140c8140410f01c42d440c004a072011070f41980c0092108040303408102040c80c3e44a500c1c108000c40604103819500e001707215031030500d00103104013224208000c2442c0950810344111044030000c1c4046e0741c0e645000c0d40c4030b0040d16021406407052620100700d460640007627800780c52091080da101000059001009044500401d07030550180c071201c0000600d40102c14100000c903512008c05694083c4140007071314600102d0281560314041c184000121985101580280c2514000c00c650 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 271983696 1250 271982446 271982453
    0x5070f15020c0a1205150c0a0905030a151a060c06010f120c0501050708040905160f0912020928020a09050604140114040801020d05100f0b0a0f030f09140f0c06070f 72
    0x2903039600e000121b040550200105001040c00411100c10303a517544506856881c41419541c465000d40181081404504102d610041d07900203904000000100c0502220f51808076103198041c0311071580075001000148121002d03145030754001c18081ca20300055001e103407640c0000701140c2c041c035410030100080c12400d10406409031070240c0100c4800300040c1c18500b1810b00e02c140a4014000812450014100464050b0f003600c8c0480d107135081011594034881d420040641001086035001004001080c441030300138807c50144400d06038001a503803a9146005080d0031400e0b800079200e80740802089c04103410208030a000c2c0082800c09c2003008246040c1c1003030500442c2c100d41d00ea0b40c4089051007602500b50425070250440b002941d000c0c0d0786460b5003102183d400d018003200c6150030045074020b02e20900002074110610710700000e01c030300028001c00954482c0c200a5601005980b4034449001f030600c40b200040058100425503240800080745043c05600c00c0602018010780010061 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 271984946 1250 271983696 271983703
    0x901050d0f0b0301060b0c0c060708070606030b0702151506030402040b04020d0603020f0a060503060105030705070b0f07080a1407050702041103010905041a070203030f1305070f15020c0a1205 84
    0x20204141400e211a0710455040001018150b1569109608207040007410020410856405422030341c0a80080f00c9100c3c14405240e02c0003100300d170401c3c4104121804540c1d98410301d0040c5115064452040c203003004000d02c0e103606d40040c0881801020305022104850307084107000b15400303403030316078482e559400010010405080c14030b8006000203140c0781030705c245a0219040d00d00c21281c0150f101c05040c14032002e8401030140d08003180042001c100c031903004401545d8000710038900305203480320980c1c80c0d184891003510159800c0020b01d00b0700c508190450180c6030f0080502000304000003020030704904030a0041d2012045c000005800400d41d03e40750000045034101c03204040d5a543e40300100c2008080444007940c00e0705000b84100c82403203107100030b280a00c0c425801103086031212a910761038120b010b44070f900c0704a4421401000203005009240041c40308000440103036242c056560900890b40f003007282190040c00c0204100d6448c80300d41800d46a030f1421031b041300c00b02884e08030324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 271986196 1250 271984946 271984957
    0x30a0c031b02030d0e150c06010b1c020a0201090b06240c030403080c06070f08070203041a0705010f0b040506040606090b1308060c0c010b060304230c130509011803090b090105 77
    0x10180034090780740b04c1c1241c01000c8205000415118248440c28281000d4994010107000c081c1980102004200c0c10702c4003405080040580480403011000c1000c904003280d00141e03074200940d458800078002c4c4014000c1c4143d00000640b2441401034440046078007610042100c84001100403501045091003007060324003641e07002c1a2581c0e076a030006000ca540710030441e030303e5000540505645001500c80d90185000d41c40540055041504007010b104050341e00041120f814070080c08030301d010500c00d015a0500c0c50b243c6600041e10050401488155140200218000d40c1805002c101007540210904c084a1090161a485110a0300707113000b41c0d0700d1580002800d218010501c130210200308000d0007a4102840208262111941805040e00040394040c22003002003c4d0903410a150a50399404003003108107071541000c000001845242544140100190340d030720400c0000002403140e118100d01c98154045401540d0707a001300b020b0700740e0040c401c40ba400400c1901c940d0340980700f9902c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 271987446 1250 271986196 271986199
    0xf070201030504080c030c0708070602030f0427110901080a050c0d050a0b09270105010f0b0a030f02030721090f030f0c081c18020a05040b0a050603100314030a0c031b02 74
    0x80d502c14102c580c40c0d03902e250038009c55880b405032100c00200540000b08907205000c56036480c5080c2858480d0203031074040e1000d4141c0704a1112410440c202d0500e216040014200b0200162159082000100102002000003041914002c20b00c01c0100c0a9400d5480d282e02088000c0341e503595507142040504070b0440542c0e00028080c003401030304200000e02c88061020780c00300c161900306034425a401e03541d083c445c020f42048043c80a102c05403440c001081450100e00740403600318610310f0b0400403a8402c56103000040d10290500d00502d0440040c2c7c1c00524100304240003415060300c60780e1126008e0200102405050428050100d0240702448980fa404c1999107840e503202c070402e4003500c5d031098800c1a4180c40d0820b04140c2c1300c241000340034140c0d000317495512150b0805052000425021000c02d9000a58800000d820303a20302000303610800003015401c14541c51868108268048468000602d4009121189480c1d510040c0c0c1f040c0300b60145000f5404540418484200c9003010101030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 271988696 1250 271987446 271987453
    0x40b0402070f0c0513090b04080c160b0d150b09060c0f0708030a0f0f080f150a0308070c0f060509040203060d0506150f0111060103060c030b0d0f02040605060f070201030504080c 78
    0x160148408042c83d182110815901910f0307140c00480c0c0c1c3d50845091400041c106000600800c000c509a2809803620340c040e9412101c418550302a056031441255000703444003e0001030808525529000f440c8040124a20b00c00b403050a00442c03003071a0082020450043d00d010407070040d8018100071000c0302e002224141e0314074607180c0e2089612540308404042c007107505045030070609845640c12030141409561820341940324101d0b51011240064194800c0640c0c11040b050313541ea4050700c0c03200a41c401c0030790075075658651034201c211541d294440754179000b500c0c03400c10045070400e08899600008407070040c1d99584030030004044100340c1d8000342c0036100d44020072107501c0c5140f002911840048400300c165802100044039010040c2000d109141c00c408010000900c40c0e420803810480f1a0401107403243c21540490b20405100c18265600036070910f8400a40c100340c803484014002c00d88141d4649101c1200001f114401d020009041503031300d4001506000320300050310900c3e101c00059 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 271989946 1250 271988696 271988723
    0x33090e1c18120803060d03020f1501030203160e1305010906020a11150601020d0305060a030219030b090c18100504021314060304031b0c050306160305060102150105040b040207 77
    0x519000d800580c006100104000c0400d40400407040d9102c065032001440703103583d07030705414000700e0010758908509520528908440700913080c02200200703207000d040301c5010343c590b00403d0b161200070689060401d126a2090204a0102404a521480d10011581c00125900d0202c1c010078111401070701d01c2c0c0c4041807010015038803036544490b80610000300d40303d03681100021100c2c0007003a10080d016902041030400700b64001e40140d580b00800504d2500403130303569000b00d84d0703030f00c041e00f00315446811450080c02017040100c502508141d05030000c10440c0c2c18040412440c4618030150501000c24000040102014010b14005010b0142c81035448203920b400d0707140b460b4101c0c002c03440030120304a05042036040c1281541d20854040d034071100e4128099465041079401442e05640040d40d2034000304054030b080142500078940b400794160040185480107080300c80c0a00407a045400101820500a001c10f2565042d120110380004402c003038040024024421088001e0001c100c0c40300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 271991196 1250 271989946 271990003
    0xb0309150c0301140103060e15041b05120708070903150b0d03021c020a0809090711150601110a0203120c0307050712060b090103080d020d090609050133090e 69
    0x654101c0740138141501c0315148400056080d600c0900400f0000d507404000107a5060301c0c44162a0074180203000024409080c00035880440020003072003000c5500010403a1081d085400305c51f83c0000c0c80c3c0303051162801c7c0580000e00400591202924503401e41c41c0e4a402e50340198803009003448010003400b410920341c6000b03074580440c2035601e44000c0c5100400349460740081608180540c0c0070f9100d51a0400240c1000040a0054403850411000d003c032104414010805507400103800b040303040192400e40001070011120120381c41d42c0e80c0280c00314400588000030074200d444030240721151200807001d541841c40c0500d20018010b489103c00000b403e1101c11181400d04ac000c1405011083c035540910102c02d9081c440102001d40401030407030341d95140da0180c18480040440401c459100340c903010309030b138040300d01550b01c0e954665800c0600030130644440089400c890360000600d507c030390582d8911981e44140d070026521400d810702e10f4101800710003c8024542100c0d0805c00c0c4012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 271992446 1250 271991196 271991221
    0x2040e19050d020304060e0d060212010303030f15031208041b030602030906060a12080309070f03050c030c0415050d081308030a030c031103010612060b03090114060d0c0b030915 78
    0x4009441c1805000070b840200b91012040b0340542d03101d41c80c2d1010480e110402e01c814291140070a0341c5065090050203a440d00d41c403a043d0007940a50b4021074a01400c0403040c040340c070100c0950040300c074803070710401c0014003450f8104a02c464a08120f00150307241e091042403030620810204105d150003101004022035035010398015480c10381118030b9070340c46c0002e01010303a625004e06620a50803086041c00070390050000d40e4030001980c152525980d485251310902c4186800c21282d640150a24040d40d0038200282034050f03104a50a110b40e01004100400c0b0011034013800d4000c0000340c14010070300002e001110500d84081680c2d42060303581d071942903100d820460f100400030341000415400d5911034058281c001190ba1452860741c1d1811100303841c0860b6194000c0052621010000703500485c48001e14499039a040000c00e0100c800c20b0402009800180b05070b209107031018903400420712102c2107900b640c0319011216540e03180d800000c1c6c50244890410342000b00803808000f007140380350 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 271993696 1250 271992446 271992493
    0x20603061201180b090105090307171c0e0c0102060402012a020d06060512060108060705092d030114010803070807080c16050f1215180a0c050901080601080d080402040e 74
    0x415861010780c030b502805c3c40c20380b2001da4100da65a0301c14850b0401007000001e5041100c5081d01b1880c1c0303400711819014210300c0d2500e0f04103066a0f40c5001c4180c500c2c0d82405503c6805c0e40901c0641018509a800600043c19504521842a1012006c001c0f014040184c2c0c45401d41c00410240081c0f12130f1801071301900e01809800d001e2212410903614015001aa060698020360b02030120344e611000219501d0f040704400301d901c5100c8103640703484121f104084414500c00c0300b02c0034980a42e200c09041c01d442c424813030030000e85244001040034445c0441917411240e4040d00c0907565007031030700b884a400d00843c00005540d0195a140c07109142c50016480d08032041038400914000c81a010030003d42c04021850920341c0201502d601986030070310b0443e9002d030710801c0b9002441c001500c07041c5841d5020301e04a413800e0360001c051115107000304606006041000003441030358100f2490503101c0710800b41e11070601035100c010804555030f075048450f192a11100302d8203204440d40c2420b048400c034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 271994946 1250 271993696 271993703
    0x1605130b09030f06040f021306031407141c0b0901091407180207030c1101090b0c030c0f0a03051602041107030e010f021c0503040c0b0f0c12031302060306120118 71
    0x70804030f484903000200f152842550049080580c280564080c440d0014030341841500d0a80d88140102c0011a40d110f0740128503440c5004010440c28104480451003092803118490b14200303201208860f00d1052400d4a40c1d48410141010388071188940c2c003400e00410002e142615415226a8503039000900f0b1040b5400c0c00320700141c0007200300038101244203644001d40000c1100c461600400c01c6115480c42e401c5040c0b400c07090b050340c0c841072101590404a244c401c0c80e00006580320100c407040090316900040440580b0154200341e40141ca20700c40c1007071003420b0302100d000540c01e541d5103903c200740b440950036a09907942002d01c1c0052940b015910060301040305008207640380b51001421940c11007140030b030b82c0d001c00310241d000c1d1400d800040003282da80322280c0021402034860720143c014a1484c400064541d03c17003c421506001070344440c110a05070078410008940e044100588101e5019103285a0700c0e01d40ea000314020324851811001990b00340703100d5070441080c807070820300441c1c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 271996196 1250 271994946 271994953
    0x10e0a0f120306140d022803200904151e0b0414040c0611030f180a0e070915111c0e030309060a031527050106171605130b0903 56
    0xe08070507000c44409000b090303500414041d42200714182000c0119501c0d000603d403030321550300c0c2561030034400300b0740410303a0384070000301010030422620100801281c4034406e010b2070186005000b01e80c044070001d001070040704003841d00d049078085aa111003482402c44035440c1c1107180360070122018041090403680190700d0550015003d030780f00303e44240110351150358446c441c0d150038001c403402c4a034076080341c80c02c0c0020408202c034840440001d020042d04980c503980304039070003000c000c060205544140240c403002c404022405600968080a0392458840250b0a2116100880c0d0403115503078400404e02c168080205a5802150080c040080e26a0f80a142c0044001031648a0181e08200c40d0400700501201d100706e4000d8208051100004840640d0349175200d4240c254442d1007080c43e035101a218140220300b040d1707402451702505090034484070002d04511500da102000600d0203403040403817035652800a1048089400300061502d1030010f280d1100000d260702d43c80a103c2505c28032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 271997446 1250 271996196 271996223
    0xa0801060509010c0821040b04031b05071a040902120907050f2d060a030c03050c2d13080c040e010501060c0605040206070b01080d0801050f030309060c010e0a0f 71
    0x384107400b15014402c041e0350340c080d0811166154115504035081c0810005070342c4403003945266100c1d51062150f070003110614441e042c90705000d000d580c0104100403080149059600109030005003110469080b2034070540c500740120b8049606000302d41202e8500717400040c441c1c848008400d1514000e0081106071240651748030104489012003202c026000b0000103441c4524036a21007142c1c40302e1941e1a02480029412000200c8507880b0039905008603584090300420207034548109a44020594259440c2814403034030943c08030f1050443c0c51003400c0300030807080c40160050603118807000f0f82c46485072454503160465261080030307014500562506402880c2d24205028003412150141c0f249800981d40741c585001a180040c41681c01001c204000000682c1c601d002900030141000a001c292410b003000401c0c100041e41318504c02e1840035202c0300c50303507400b00894504000c100d6686d680e54820150003405401e000c14800c0ba01d0151b801003109105011101c6c0ba0010f100b000e1401849 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 271998696 1250 271997446 271997459
    0x2150304050f1b010c081b0a0c0617041a07031103071d06040f0b070501020f18012303070c061d060708010b040b2b110d0609020c15040c0305120a0801 66
    0x20b4070080740c14005170380700340e00b00007040c0010024019800700c00d10003008141c100524924102151600b00d40032801c030081005000e501c103401006004254042d44200e017800e403141450301c0e4503210b141d103818400202240d180c40c0240c0c00f40e2b4000d00c2001d41d20383c0302d103022500134042c22400714601100103c1092400400c0c40c0020484094415603060708118905201c1060380980160070111110340d0708000701d02c0d0b5030390a5005041080301403142400c58903113650004000c615500c00720a010130660311409a06288001565400921880c103002e00407618104080a031010f515a403414414680600d000000d000c11407a1050603581c0f64080d860740c0c0d07a521800244030b2072180d410f40c000e0a01100a07140320795010108a842c2040c4460300c81d086806040c070444485c5000711240007400900e01481960a0280000400081c0411800d2080d5070802a0300d0360407401d280809800800c00140401001007014000b0716045070441d00c845c00019109000b9034408100300000c1000c080001908 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 271999946 1250 271998696 271998733
    0x501060219020a060804021212090f04090c031514090105071404080a020d170d091401021e1303150b0901050a0803092b05150c030f0c0702150304050f 66
    0x5030390152503e40824600b060031583c40c100507108a1b445041c403c4140c080c0d2000b00903030030011003076a000541c0c07441c01c00c01304410300901d5068203000d03d00b018010380100e2039041480003101d412500114204050030f00050040071040e82c0b0303101d45008242400207840341580064410f1010f5191941010441071040480d03000e10321598010340c0c042c0c1e02c0c000060511440b4006268407a00480003101401642c030402c58002d16181c40d0800e90b1060100180705400850911056004001b103203424500c0c1d645100f14940e528245008010008110b84c800081480407001540c008440207047d410040c0d003c005061141a1a0700c11800c220001c01d0900d0640080f801303c41c280300081d0701d80384d02c020901c0603503201349140d014501d11410b8070b903048204c440c41104001d48188050960781d03c1c06422864185c6000e0002e014060041c820030071018000e1a07230f2500140780c0707241c558584a9a1000035403451003a103c0c01c20b01340010040c4405c0002c0011030008041c2c16070150707102201e01c2c141d05d108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 272001196 1250 271999946 271999993
    0x501030b030d050c0a0209090a02011403070e120f030708130e06060a0c020a03020a26010209060901180b0d060302090601020109020609101829090604150215010905010602 75
    0x240764000080c08202a80110010401c0321410000c0c2d410300c080c40d0b000210b001034221485c6180b0381001c1503e000310740e0302010202c0031750407a859a600f107040650005000c00100002d09018214013055482c070b0540402103401070f414840c08481d55540e880c0381c0241d00350004205e01d002d0110185c008200e05013841c1c0302c41c1c842c1c0800307002241440720008088800c546102d0040c0c3c0c00c03185241c07022025031138803000c0714064a010241180070a00e01d804007010700800c0454940307103900c10701031007a2940d200c8003103c500701000d00c1e140c07203680c143c1d8494201c050b081c1e500800c00314400203a0b030203690080e5000813080703e000b1105400b642e1341751001642a210031707001c004e40c4102d04100042c29890f01c018000703e40f90040c54150300c0f00706146245c01c503103561a01b10011044200ca484018903058400000c072890070412070909181007140819403c4c0118002c406440d809012604002c5208202448003080d50720502d0001c0e50352100500c00401f401e0003044014040c2000070314011500e40120030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 272002446 1250 272001196 272001199
    0x10f0611070608040b0618090304080c03030702090711030409060906060909050f06040f06051c1e0c270504140706030605060304020904050c12030c06060d051f0204080a030305060301060501030b 85
    0x31040c0da03559a17040ca0700030001c0445610080c40290005030325030240040b84608600002999280d0825038068503040301c0c0d6500c20722035401041180010388440c1181d680021003410190b036000600d10f0120b0550080340c100b030382402e10704140001c1c100c04a030441001c803000ba4440c1d89005444030094415200112a46031041071503102203201400c02e58080c60300c9000203500008e80f1512540004d015441c0c00c0160040740000407500010300c400b81c40c2008100502c4000c000003410655580d80284e5454440e5000740c4103491106110310340303620700e140144410800108128038051410308802500c1040010040c0705140c001700380140288201802e0f80c500400d2541940e07103a508202e400140244111003601a0550740b515581340c820080e201c000031031001c2e6442d480f040e800546426001007449205a610241c0359001c20b00220700a000042c030410507407130301416840900b020340300341d1380034100c0d0b0301c01c031b00c19070342490790550015014400441c020b00000c0c0d685c0300114280c504c0b01d1070341c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 272003696 1250 272002446 272002457
    0x1605010b01120608031206031608010b0901091506050a020309100c0501050108060603120c030c06010e1501080112030804030c2102010f0c050412061e0204050f0108042105040e010f06110706 83
    0x3441800c001c0761310706030300c01d1005027290304508040f0500000d28180340c1c04402580c0d19100c0c0a0040c4c07900003115809007072440001c10460340901c2c0c0351108030225100e41c1081c00b00014503a0001c0e403003401140c440600c0500b084141e9840f4440080000113022010f0755203510700000440c0119021440500500d00100101401c403d100c00c5405260700c41a9003041e10300c01009064551a01401628000c0100c00381d000c1740b510b454000e10b2581408049014100082c6400500100c0f80070701507241d0342a014a0030800c01d0780c0398601950082411103001d07180150518140384041000380c80d8050440d2203078024070034904914074207001d035031101407002c02049080c00140031601700e0045200c61607003d55400305640d03030300c0b1f09008102d10480c40c0d00150150000340130301050030202d40300100385000786801c140307528142d140c03581c40e80d8440004080c5100c02501215100f4416003d840c090049002c0c4e008071940c3d5010700030640d031813621580000c5090301c003c40c2800000400c45000329000c0386c490 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 272004946 1250 272003696 272003707
    0x21c03020c030a03210e0f0d1e2c0904081308010608030a050c150103261305100306030209180706020a0f0321020a0306050f06090d080904021605010b0112060803 71
    0x2000d082c503401140070b0030340c19a1220042c1644008001440d040c06108012340844aa4590b00030028500d1050840750b00c5220000750101030f82c0b0040c4041541e40d0401400d1a50741c03003014142d00c221002030066485050b0340144030038044144014858141c0e969a203c81c02c90392000d0a5003a10360610480d2074580003130003e8000b0a0003003006290381070501d002d9451030003100746185100c0d070080e0026107040071080800907060b82550006600070214032200350504580c941010400d0109000b00c41c003c035220451071000034041e400603000341d81d0040c4081c1092902560b100c008105442901c0801d200d24900000c0450000c108800b03070f04d4000d0014041c401440c1c074162001c0800003410442c52481040e41883c032113485c0701030880441e0b0703580c012032a40e2404080140d42d08001003021720585040091024540d214680b41a400b41c0c4140322646031300c1d040300000c0090040ca2009400c0800159010307040001c190300002c4c3c3c6032400d0721080c0080a400100004540142c0600345169000b0080e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 272006196 1250 272004946 272004977
    0x50312030c03060a17070911040e150319111306030807062a020a030e0a0605040e04020d082808150103090521281704030c021c03020c030a03 62
    0x31948a200a0b0020308680d42e44c0d1715488144520094120007600480300500828039507003c0d20301c515100f009854101401d14041a503a8075001e03012103810089500840c0003614184444882050003100741088040302e82460441405d40484561040c00384021907032444070036100d07450949400c10402403c05003181c1d86e500c01004801c2140c030b001b45070404400c03110611694100741c44241c0780e011300320110745840c025201c0008159214030404540d81c081c0070107540a801e6a04444014010480e5900c503030010800641c0c0c0aa409404041c0000d51003881c8030b142c1501103848081c80d841f4a40345169114212810242034402d580e01c108603440c1203800d50b100b034005e03000240c061401d4950b18030368a180c3c0c83c1c1d01c3d5150000c1e824409400702d0316042056818803059000c01907a603a54220040e5402d008000004000510400198000200b001c0c1403082c41e100e64040d03800340024031814580b078105544101a860100c005220314003070032840d82004035440810a070300d5115500d0702c480201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 272007446 1250 272006196 272006221
    0xd110108090a240c230a050408030412030906031109090c16030806030c01081b0f0c0a0b0f130c051002010e0106031a06030d120207030e030d0305010e0105031203 71
    0x148450164494040442e002c200c49850511260340d42c4a829a4404090402c08095a980b0030303814050120308010305086000f00c4c4e82c0010306244200700355540c1d060809081e0789a010b82c0e00303c401203201c0450040b8817018115030040f84240640c4444203110782e1002d040703080da8038100d0300084403c01403101c410345003400400c060308807107440d01950420200c0c144501d144c0c00b1641085e00050001410b11550f030800303000b500c46464007880d082c0c54514200c80a5991801100c1a62040c080c0c006114410102c0c40000e03589a180b01200f036031506001c1d82425130008406450442c10342e134400c008503d504141038121315026078001014410940303040d0130044d070001c450383c0b01425035403160050070145078203104030700c0034620440d203451130140301c1400316407820b00003001c8900a60006881106c540c0c0c0001003e403c0e454000c5015a442c506840c04990250304040c2158051080001c5a12425016000903050b81e0312040030808680e0303500201640ca1202070805600709408102048064031203c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 272008696 1250 272007446 272007451
    0x110d0c02130908070b060909030724090209040602130909021f051b0307110d0b04170f0c06070806030304060c021905100207150f17060d1202010213050d110108 70
    0x2680028030318899107034204284d1221404440c6160328000300101407600d003107401c1d0400d410b18001d41c10028503942e00000b165050b0b00072080520b20706868081111690081003510383c0c0039000b1201400e1916040c00079400641041c0000000007402003185600d510907602030540007010500184440c501001c0c2c00030125001c03c04100c02044200042c83ca0705600e0307060030650300000c582e0b03000c090410181c429517440c2c14601c624030007516100400c8020040641141e00030604490700080142c140703603540301da0150401142c0c00172540035859500400c1e00380c42603401d41c07200f41081c1d95003410513444c4e120f01d010300303408100e1408143c00903040103454450f900c03038080310101c9001d480c0c0001a89c0b07000c00c0300c101d10051b40422020f01a02c40c9201c504860300202c4d080c500680c480803200034006018102c036018140c481c0b4400142541e454040780070030a80c00c540c00e513065881d5644001c0c040d502c1083c001c0301060f44030354005220b050840c1c0c041c0c03a590f00052a25840c8428000468100030301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 272009946 1250 272008696 272008729
    0x81906050702011b020c0405010504060608011a071208010302010806030604032a08220f050306010e0a1803090815010b0a0c03050c01020310050f060c07090b060d050412110d0c02 78
    0x703d142d02c041301c2580c015a841c0002e041c3d0014010401d07800d080009450058006a0269007050402c00c406600a4032850540d0b008a48040c000c541c0080d06075494056030300080c025009802c01c41d083c0b01e4001c0343d0141a41c0c003e90702c005150b43e0382001e0681e141810b68004001800c418030074110268142d021880c1c20701c8001c94405a00050340b2a01011340007126400e5005030002070300c050320419030001c5001404d2188003d0000c924000c0041d803251814420b003142000a02d0002e03100c8045c5070b21040c0c000301c080380c000b220302d1444d0034000d0005030b05000c0c1940610407080d62183d40b40313010b104c1a0403240811100c40c80c042080c202180d144107064812020f2040520452407410428000f462060304d5010301307540f446240200f00424040581c001900030181000405001303900820030000340d414040b400b103642c081110100755544165093700541520303000500003003080340700d2400090343d0281d8984034402403500d69140c64104c030400080100d101c007180c50005090072500c1c910041c0c1ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 272011196 1250 272009946 272009951
    0x30d030b0a0302061b2b03020307050909100806010911041214060711010605010c080a1419080402030d091d0408130602030a02120c0a0b1503032208190605070201 71
    0x55a50101d9082d4000300e0501c0c051010240607017400b14070806c03031041059105034505211007032900401e841c482410304001d00300364000002034621802441160007100015010854624264005201c0700d000c5009440b080d001c1d0100004080704a801401d4070003010010b818a01840e02541c00303481002d02000b00c64083c100034010030b440c0c105100840c4982c215890340c1c000c1041300d006050031501d40340c00039414001200b015102140c800019a0b800c1c000606240001c0c210540c045800c034040d000c82c001004680c40310400c000c0307a202c152a40154070075021038142d8080e01c60143c82e10a124050304012030030485222510500d80b280c01c85e00030b030064640d01d00d4688034205803460885ca0b07804c10405a0b00000d07014078910383c1042410100301c0842c0610303062402c50000709895991046000c5d2050400f00d010400300c0101000c0f1561551008048a0f13031240c075994500380310900e5106200d1480303104030b00003031828004074482d826060502c00041068015540740d000a0102401c48004c40d035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 272012446 1250 272011196 272011199
    0x609051005240705071e0324060503010c020c010e06120f0406090f0303091b06020618010605062a0304030203060412120e0c040f0b06030c070f0b07090905010b09030d030b0a 76
    0x1442d40d005106403806140502080c4c1d040c04030f030f4002c40040042c1080d0f11440c1e50380400106141c000c0c580c4540241c110111250b074042508907000d07000603041300b0f03450b500c1c002d5126000c540000300e40003540002e8903840030031039500341000018058107941e40c00841600e40003442c0320100a48580c1e10601c69900060f0400300f0340c0f00c0880c0c0e9040d140701180880d0352011100c3c14840c07120705520400e80002e041c0b154050070108029115600035198a94442d910080031030340b48400c2d041035001d401c0182c1825100c1c090550300d05019640c1005612124480c008c0c0c0c41d22903e408811078042da0380140082045850b1903440c034492598a41c42041044811096800c41600034082c0750541d211060041c00b22210f00300801040f1361000c104189202d14104100f506504c0e1002034940c854029108192114080d08000d100340000020051000329200d04201800343c00c000c0a000b614035991041006a0b203a4002c045984901a0100d5041d03006410520105103c0d030000401540c01401c10303851207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 272013696 1250 272012446 272012509
    0x703060c0203120108030714010507090312021906050a1104060806010c0f0b0f01140103090c12021527041e0e211c0b180a150303020f010609051005 65
    0x1404217800808054000160a4040c08101403840980c62100d4000700801e050400f006000da008920000b0311001c0d0a0000412580c002d1140359000541451891800d07030040c40c1c603000a00b411140d6504a91510801c98030303003410101030380c09070352081e100c050003515a20015501c80d0720b000b03c100c5040d1404074214001407043c5006900a641d01c034003140380c41d414081001c0e507441c0e000403414105403030850030201040c08501113104035103403d140c140f803000306800440e4014070440a416100800000c1c211440000200ba1000c81d680b40007403200d0a60080e4100001c0d0f880e441c002144007503500c00f0100032480a0b070320401c00964143c0c225400e45490514200c07d030010b4003200101c0040101d003895044c1d45520040004a00c01034041100208680c002240c202d001c424a0340510241c2c4001108204142c2c000440c0c00c4a2000703001205035645402940c2d5a0b40507540545c550a00500040403c0540500ba020741c2c072402d074201c42e090520050248210000c0c034210b034403403403901090300341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 272014946 1250 272013696 272013727
    0x910180606060507121812050c060c1b0102120405040203100810140c0309190501150f03060c0f051803010b06070308010812030112030f020c031e1e0703060c0203 71
    0xc20740c070f84900d9226026410084000741200303039450180850000d0f030345444154000402c0560b262100a1000c91003541403513481c3c05c09605042d40c0000c00014039001d0300f000061030450003a01003928031401125400126114030042c0804954072800748414004c03071619401450f030041065080c000c240340e5a202c418500001c9003108040e06907108400703401400194880355003c01111001465401c28601c119917a552040d0780c0700c0d0460700d01950f041040001c0d00305d46030750703041c0d03243c0c507510b1036158400c68120040c2484121425450f0031040d0060074040d40711551411210b0302d50500b0030102c011155150300c0b080302800d034035540c1c5a03289519030740c540e006070800034043e5036440301340d60401c45410f28090b0990004001c022003800100003c40701100c011fa0312592515060010318103100045c0d2400300c0010394590f06000e20101440d0060505509505201d458001ca0f48100d414180f8030452810300142d4400e680c01c61002070000c50700941110201d80c000740f045078580341c00401c8103c3d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 272016196 1250 272014946 272014949
    0xf0607030507050c0a11030c0f090703020304020604030b04110909190803090106080102030112120c0503091e0409060b0a050a050a0905180706050a0207330207090e0a0b0f0910180606 80
    0x1519043c000c820005d0342010231460049080603203030051600d20003c00984142e01c010100010035400200090454988005440045d540b00541000c20b05052030304010300d01d041e0b0111400350f22004001900401c0001d05a900c400000c01c84149141081c5ca94205a5000030700104656403107000004041009200440c001c0011500c0f45200b0200c1d881c0031241c1d80e04054001c030070010101800380104101100721048103004030b8105004040d042024903203540b00d901016405860725507400c050090a030407130704400c0400c88540e2029910b90b01000f4203d841c0340103041c0c102019071411b100000013640002d421089106143c4101a010303112186440d91541002000076004609a07082c5030301040044050403600e1980d81c60b2000c07500c1100309031040d0494650348075880c135001500881c020b0003400b000e040342000070301c02010324a11075a59801c114500700d5030b039444507001410841c0b65250041c007840c0070760301504c0780d0a1944c403145c01900f1092072100c030070503208034658000707601d07489101d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 272017446 1250 272016196 272016203
    0x2106061815090a1e0509070909020306011202030a090308101805060303130b12010b040608130c15030b1e0312130e04060c0810050102030a320405120f0607030507050c0a 74
    0x290014142088904c01c000d0a51203103018800f0b40044c040c1e4541c01500c080b00369000c000740103860b5691040121014080404a4846584000280300d00c00646410141d49117000313848504a580310340841c40b210b809248034682c52044150054600a511900f20300e810000050850f410900046c50110110b00b595004a001078800516400e846030b08840040c010500345004034103042c5000700c082c080e2500186101c000c250b20f48600d00030040c041c1c10709400f130140c07429040611080000064014614604164030034442200c0011070740d0f1011038808440c100c0079000c1c0118006401c140d200541008448401220660bc00403407000c80111a4a2140b03004890204200c900b2903406016110040c00308217505003412000c0c003080e41c0000894110311014a0800414500021208020f5030280d440c0300d5100002002c030700381c2d501740c1e00c090416260704a40c049880580d40c0d80c407540d0b070804020752064a03040800000c4416000307600042d0700402c107082c2503107005462000309041c40c40e95130084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 272018696 1250 272017446 272017469
    0x1b070905011a09241c0f14010f030b0405120304060c0f0e181f090204090b01080f130f08030709082509050901112106061815090a 57
    0x10066907a803803852103699240440d07000d15001d03000011406078a0300d500c04950900e41d800e640380c004042c1d00d04440208200322000345d5000009030f440390141048840d2804d503103083c0300c402c801031046015400d0480300f00011003250300d80f45070386404e9007050050099a43e0b0003805080790702d09003070a000f0342c4540e01c05da90000c0c0068050001602012900c00b06804000804500440e940c0307524107000b0344036204030205059a920f1803070400c040500525844202c40f081c1600150310b91440d005001a224a40010310200d0280c40046071061012031700724410284441c0458400d54940d03403000c142c10302a0a9a60001c2e20700d0f210545281e005840e84c0b0002802d81c034013000803080a0108100d40440c080150009002e031044e850303c1600280110080580d690020941d00002580950f40c148014258541c803180703032984158030001d42c2c0c51010b4400301c0d445c0004501d85441000c440d0b03404200e0010341c0f0659000020301092105c903082d030310071380310007005880f001d65240f0320303440b0007000810100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 272019946 1250 272018696 272018699
    0x40c05090109050105010c0308191805010f140a0b01030908040b0316080c090105160f05100c03330302090a0b01110d05033108040501030525051b07090501 68
    0x40c0008018141e009002c1d152030f180040c4166039125000b03140181d010721700a50152252b50b8031450f441c00341c40f4089006481c1440f1500b215010488841045010384000c0082c00c0000d9444021703100c0c05195111080364402c00034410001c41c0d80095103400d41803600241021a41d40c074600c0a40c07003900514201c00740031080102d510807521100c812000b10b0320b0003c90600344941c0c454402e004206a45050100100300380a444a040c40044070701a044a00c114040b406410602e80720314030036640e0310050b03007401083e9807440d00a0081540900d1982e00480282c1482c100c1d4400c0720000e0380c0712995405a0150010250b075035542540c2c0150680c42000441401100003d0400f114800c0c6405085d0002800c0d017034031075081003e0320b50014250080402180030310800c510100e6004a615205400040000e01030140c2c40000d0000d4510070f8074104120388410000140900b01c2c51160303078507008200202012903202d14041e0417503140c03142041d80d4010b03018281e6800c0c0340090300084c90300c0355200700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 272021196 1250 272019946 272019949
    0x60305011802010f030b0f0402040b030702072702210103032a02090606030408041203050d050f0906010b0a09080709020d0b0d080d09020619080f010609060905090618040c05 76
    0x98169400c464101d99446551a90000c3c200c882c4130b400c68000d2560302d09600900e80c40b4021404c00f01c0000400855030340780c8a4004140304c0e0000c0e0346030401440348107000b241e001100e44130304d5140e8000c0790b0700a0880300c6075440d0030041d500107400700800b04100410520076010071a26180030754426150100d03030249265104941c2105030307410700400c0110078015030258035901030030754002c3c205503512503407507849041c0213200f4410390b8040301003030f4003110b00c9009051f0320902602c10034501d06410300c19511100140b004088043e54580c02e150071034001040300d5920382e001001d403412a42050440266220751050034282e03a0362054074100d80000f09445084010b2181c3c402d801011180187c07270040c00d84070840e9501409a01c0c1240b16959102072040d9540c00e0261894103c51286503d44c503900c84030010007407107003504c0548802a00c1c400104105c2e0040f49428155112951052040d600e01010071582e0440134100c103030000401440d012200c04042c0b82248194014101204050716110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 272022446 1250 272021196 272021201
    0x6040201030e12070215040506040f09060b0403150902010e1c0c09020f04120c0e090a03031a03031204020604030b100e071809020723010e0c0f010903230303070306030501 75
    0x40484020f8202440461038a0069829922100d40640d0310340c80015150780c0c1c0e1072407403049810007030b484200418000f5050000511603801d0729245081804a03c0d134500d00c017030550241d03020042110145001c00034410178541d1200c0d8400f8014940401c55180090100f29101151407115a00002070030201c820300c01c1d607082c004020078000d4011840e1140d00520f19007240524020409000034000101050010f0403281d030015001c020b80e481e0b02800d100421942e00c40307281c641140481c1c2802e2041351a814646060034000401501951410701c0300c81d031800d607407400140100c0e8821024403011002c0341004503464401e44032001e00b4000350b4144000e07000c4000c00240081d0030840d103d11805000200140d5001c100e8010003c056151417061074042c807440c04500518903803c9100350f07a6009013505400c4200301c007000c40c0a58105a03802000d00c000080140c008074049000c1260400000302e030260f82c1400b90112030920100030f0303c0903c0d900e0955000740c41c54000245c81e00750134418400c0a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 272023696 1250 272022446 272022461
    0xf120105030a02100f03020c190311060f011206020415020303011d010803040e0a09050f060a0f0501120f170309010b1005030f011401110601080109170a0e1903020409050604020103 79
    0x840c014040c2e01c031594002100720510104010800c04800e11917501d460003074054481d0741c0c020708180c82035000003000241d2068141c081c141c000500080c03614407146c102180c0c0354080c1e802c0411045003a070a0072000c1c2c101c00c006d10421250704bd420400000c511780d1a88045250707428a6010315500c0d45001204002c848071500c1c2041d0190707440c0c004200305403002044604642c0104440e12103580c2c0d10450030010500346002a25600641c1c40d28801040701040c20b912641d46503100b0000e10051402010440e8403d008855525402c0c2c0d19140c01309510001c12401248900403140c40b20172241e108603003c0c0c00039508444940c0d10341030900c0240c503011400403402c00c060b151403030842c6096420154001010300c104000300022070100e640e264421401e010032003002804882c01c3d542d444901da4000d0103944c10544441e1006144580c80300030341c00c2200c1000880faa6400d080044550802c01c00002120644415400c231690020040e2181e01a102c14a401103000d40141e181034000036003641d590 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 272024946 1250 272023696 272023699
    0x1f05042114060c0304020118081e0601120503040b070c0b0409020c070b0c0a021e0a0b04092f090604030609080717040f141801150f03110406030e0c060f120105 70
    0xb601c01c0003041e24072901603a511a409103840005000790000c840c60080035a0030211041c007501080784440c001654200d8140008070040350310f203070f036070b856000c240c1002c00f10002d010781c100700030400c009c14129001c0c20502e4051044a0f6005945502009443d4815400a010a50042948900b00100348801300080000280f060301c0e01251041c242d4a424000345c0080c46040c000441d001030403058480c1034403044021f04a11200c035111146a2030a400074070815034014100316840104546207810a06582800c0403244802d0b5540e45283d40700d90080707011560840014400040840d07001c0c0034140205004054903a90380515090000741700350808040091564200001c000700050801001c00700c5007000c0c100030711512070b500024145000e01c0c0c0d0307a8008400301000890300f40150381002d900c148440c2c03504840044042000e509503200541819011803041c40104000382c082d0b08035030001021001550440988080002c0301074112801c003c0350340c000031841030f1220780780c401020b002d41030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 272026196 1250 272024946 272024953
    0x4050d020c01090f0e190c05070203010b063903070602070308130b01090f0f05010f17010c0203160807060c0e01031d070303031d06070e0109141f05042114 68
    0x2d140d010b070303900001e500c40d40305c05030a0030001410392142400320745007140d200c0300c042c0490010350f00000c3c00ca0700b00070b00070b81c401c0d4070705100102d42e4a00501222a1404100f8415882814174071103c0f00035100011850781c00724413500c041d40d120509000030302e00360f44911001a211a418103008111410081003804404506140d6402041100c130710315045418810002c5074031140c0b408428040c1201a400035240c1e0b09150010812140200c0394034142c4008952200e01c600c1c41c40440360a0f10620b20034280542c00070443c907200c071006401081c04150168211502d0301c2d84030342d20941103c01d0640d039200003c860704810f0103035613410b000d0210410651403610300400341750584c42c6d81350091403000405040c0d4403240007408808000344c0354034034070100083d41c030181303040e2030b0140a201408901900084a0304408640560314000b4842409005058042417641aa1030000c49926036100f1105101e010b110000303500c0b07651074500f80421058640d40d0411109850f2022160b00400d01e4400c9580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 272027446 1250 272026196 272026199
    0x603030f020105070c140106051e01082203080c0c030c06060307091e09020117010303020703021c030f0c06020d06090b03070609152d020a12110304030f1a04050d020c0109 75
    0xc0c1c1c005c0303051081ca0781006011846141c01582240109990b038003154000c0322416914403422102c01034180b031581c00781c886104640e10801280c4503600500714800540103e0841100480d201e80162030b40020340600e0740c0d00d0008042c0c0d5081ca10303080b61b55150411f40c0071360100005c901f0207018031401070032808ed05200242c00032400020b405007c40c01c0070301107a511a008001c3da07102d040e0380358141c5e004003100481540c590400079280c813441e00007640a0b14441181140f151072485880141d41d03090380d41c03111a4540107904896162185609845030f58003801940429440da22941009126207480090315040c8041890b003441c48035480b800c18005101230810100c1c9050043c3c07021181c084c038140203540520205030020300b684d0301903c3d0040c00341c6521800300f1900010740b0088103020354000500140c0054007190003070002854456240c0081c441080040d9028502c0030b0314601c101c0c01c800500c0390462010f41411012078042d1141d600c035040c0200c0300d54041c0603c080001081c039040c0390342c0703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 272028696 1250 272027446 272027461
    0xa1a120307110607080c0601081510030204020a17010f0503060a0204030302120a090f0b18030d0905060a0c051518010513030509060c0a230708100e150108010603030f020105 76
    0xd00035403070080c280700715969900140303654100c2101c03110381d44025031a0301c442c4908207840d50384009000b41405813140b15102440c2550799507031644140c8103134820141c028216400e00002c1d41080c090b01d01071000c10700389012980003184095020748601d1a11401f11440c0104142c40c090b40a0503010005204001c1400803030303400b0502101c5c0c600340300d491954276284000704440303248a5612092090032490000b06850708207000825052040c1c18a07210114854070425031141403a41e103003404540c04400400c13081c20311001134480f40d01c0c64181540447c2c900e480d02401c00c402c820145200c094400100810394056a049080c4185848000c00c0603240c902c1d050010180c01c10409401d1107008940500b503582c0e00c80845050f00f40a4040e682d41e41858988000c12044000b40c04981c1c000103856125000303000510f240450303814100501000031460340503402001c490725401d11902805c60305040c41da501e11140350081c4500c0000207803491550800400080c10032001c00d00f164180002d000c0c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 272029946 1250 272028696 272028703
    0x212090a09091a04030509011e0806011404030f0b09010e0a0b0c0304080c1f0608010b151602180a06050d022818090c050406030f080703090b030a1a12 66
    0x5540c007030440003603800918200900040d0840388a450010356a00c01c1208060340903010f091814420388031019940400340307a101e041d02481388280001381c0000700145030380d07124407240e039a86040704500394075160b00c0791079240305d401c0030010585010f0800d1050185c000c80910070700000c0fa410300013501c8070714155a143d814590024021004800700400410103100500301240c08040c1c4180072149100d44606c00700701d00708550800451158540f07140040d43c1038041c040c01500000042404810200702902010640c104009a00d00300e000320301c0c1c800068464481d84807040507040c07030410441c900305840b031040c1c1740950002d80c0500d130115421030040e03e4081086261200b01d10442c801d00c60440030345030b102c030341581c070400c40c9241c0320044c000d5040503507100c113107200c0c0910082d210090b107502c1031000359500c0348802080c1d04003414041021802c240c014104d264820701d040c0041558880460300c1c6074000340c2d150740b03825035144118003072448a400518803221042e1201c0701031036502e40110740c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 272031196 1250 272029946 272029949
    0x30c06070924021005010801050f070f0203090d081209100e03120610030906060605310302240a080906060d03020d050702041103010602031909080a08070203010f060e070212090a 78
    0x204100c0002e00003210314024480042c10090fa204208200d6943e40f245078060803060700c11602e00c1030760001003040c561181e0401007120810ba00103501d082042c0044c09001c0051079000e0303500c040706004608010b01e8904646004102110080c005080c01041c84011903050051102c0c0c04c1e401000f030714072030707801d00700f203103940300074121585a404206101d06401501184c1c000515481c5400404546170381c001c4090100b072842609400384a1900c200072519800c50086805c03041601000100300529002d500c0e03203010380403510110b01d11110140e2400d525080112440b020528290810440580801589600c4481101d4560000c0d481e9100a921082c404115000300140015020150340746c580081d1841949140310556070b43e034500e0000d45a82002581d80740403100080241c1c0058400c00212091b144148080c22054a180ea14401903034801c1e80103d806540f00c0c0142d1284409501ca100024510000044402e107008413009040030b00741d202640c1c0844e4248a034446070380b5401b40410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 272032446 1250 272031196 272031239
    0xc070501030c12110a02010c050903070e0702242202090105040e0a050a0803040b070c0302030a1214070306050a06051c0f110a030605190b0a120b060c030c060709 71
    0x64080d00703803070044074202c07409041008102d00b450b00c030b1120041c4c0000100304080e15075000304034007880032804841c14464070400b250701d540580401c1c0300041c0078a440da40c00c8485130040300e811a4013000301c0c2c02c003403551a28800c0c401a40c035081240c0c049002641e0962401d500d920119000e419500194050006000380b0303000308d554045c0741c218601c00f00900741050350464100c501445443c80c1c110b04550017190100c440b5041c14001c01c0c1c410f4004d5105114155154000c1c41c20b10100803401c607405104001c1031105103031103031025146c0050703000304240034030440d58000c80c0340c9040800348103000c2140d610240c00c1110400c56004605005107000102d20303440000801c0303030709029070500090200d4508a11688600182c00c0446a80540c0b00c501117a00030b80380213521b41a04400d02d082c0000b01c2c49018000442080780001692260405003041200c07100000340740540500801c1180d0403170082c6050503480010345454104040106076032054007031600c13604050030000e51b0000c0110f0314501c60f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 272033696 1250 272032446 272032451
    0x10605120a0608011109040b040c0203040b090a090c11010c020303160c050a0c0e010305060a090201050f030702210409050c07050a081e160605090a020609010c0c090e060f0c0c07050103 81
    0xa4440001e03800c80d500820702400240000c6400c81440390250f0b025109440c4110b1034966205002d0410740a450920321054011f94141031401d00511004c0d800080b40a41c005d581a40116091080340f040c11507940c00b6a8501d0300020769605003c0c01c542e220522041594000d01c100124a21041089028800203240005042c281407a0440c58400d440c14003e1068402010200341d4460100320300d030489020708101c2b42140c031052001e904a94541c41d020780018000c024940300840142d00542c0c01041c144104c0342e08405400c207509140d2190764a41001100004d0200280c100c5405025000344100c0c0c9440e03c1c00c2c40b160b0351a9614808184000c1201c8004144080344654060b030070f51041300080000c554800050070410b140e47c6280c01d00b02c940c40c0c545002f1808800000a041c8401c030780c098206131030042200c0066904a00c01c1c801218541205000031400083c640520141280c40700010a681e0400307044481100400a12100b40d840003845000364010b40000c1204c00c5507800c1c00c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 272034946 1250 272033696 272033701
    0x6010f020307060c0201090510060609030209090c1026162601031a09010b01080105060f1b011a03191b0b0a0809010c050f0301030602300105030d03020301060512 71
    0x103a003140601280a410b152a18082403a07864041d08164500c510800c10348244210750611003045807440c3c0218030001b04038010030f20042c1800141c86401045507003c49540701c00d80400280e079502d4203410600098803e1012890f08080482c1151a100d02d010a81c560361504444400480b41e0700c0001a0030440784040484501420f110250703101c06d802103105c0800c0d0b860303081518040d41c40d4186e105845100c00006511b0110612904a0951059455400303691910341004010b07040401401c0e909042000841c840214800b01c41c03812041d020008a2503405103100403400402d201c0c4491700a0300030b00380d15a8062100300354588015400f001001814444c8140000c0c0d54005030007a01041000040300400203412400f01c900ca13070340800090002e0403010f08108c03070601600c0d00d00303074001e5010b0005000044064001d880d161106424801d413882500b40c201308aa0b81e4269a07072040880000140a581018090804824074509003546035500d40381004156106041101c0e0007038411001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 272036196 1250 272034946 272034977
    0x7060e040903170c120f15040b0f0303040f0f08030913091e03030912020d0903020d0f0206160b09061e0403021203161d031207081905030105010e0301050f0601 70
    0x1d000f42c401e003200c400d6240e0b1030b109001070380c103a100800c1505100361840c0003900c0741d000c0c2c42d10544500044039080c1c2c40030303034401d051001905040d00303503c0d40410305c207000714525141003001e04010007032a40700c0b45023103281041007526000740f500602081d070420400c40a681d15126002000c402e084400010aa40e06060030341c0f821101e60104602045041c0084c4203142d415045503038101d004220411138503607021000d0740c0d1000728400c1c010104224030020009413524500141c94140100581c110301d0389290700280e00d540c03210303680b150500400c05036481030111041c0c4080e840344c1c03550000d122500709083c0f140040528804800b165061032000a0100352081c08041001c68001440e00c1d00c908200d9410140c1982c00a04180003d1214900071400042c00d10040c00c3c452015010b04564180d600111070703d540300c020269a82d00c0208402c800c400004034074002032082c184d484d40d0f101d506003400109246104961070b4442c0c0c0c1090207120300c2c035080d994216000013090904040d02d041022 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 272037446 1250 272036196 272036207
    0x60b060f1b010b03100506090a0902150c010605151c060501050712120515011b0819021603051b0925030e061f0608010e0a0b06121e010807060e040903 66
    0x24619500b601074419050105d510700c0d013215021707110407a81c19030b42d5654100d5040c100d60384900082e42c00040b0380c1e010003130f1b0403080004101c4000a900041030031038030750740415448001c106080a01100008a080d0103100a4600006540c1d000d10180a01407500c1c00007441406850390180400e070143c0400c02c81c581c0907270b18030002030400301c1c011b100368034000c00d0146071480030343ca40e45d0110b00c01c8544c880c0014003080f40701c13064642c44100c1505023030103a1400088103065000000552103500610981e5806101400000350301c58001131040a150301c0e80056212034055106000e45141001e2002c5028610081180d4482c0c5101c510798203c00d108040f0003070074040301602e10318059602805014030000c1ea544004030705001014244c8c41d95004d0844d8507220904c11010181c14441c0401c0a0900380d8100140c03c0c0002400141800e030900103809401c9815981c4000c2d43c1c07060b00da10b16078000107002a81c010a033380ba014141c141e24111014120305803a408251060760703a40021403c040c080c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 272038696 1250 272037446 272037461
    0x1401240f050a030f051e161d010207081903140322020a050a180b0607051e0304030206040b0a11010615120e5107110316060b060f1b01 59
    0x5440c14003007030800b040e4403001b5102e03074610403002d07030001b800048a0800854a1590f0035003c1c0c0d03225080846007090f5000d01d503440e03100b07590460040050004007032070f0400401141502c04540c03803034501818503005d020409030013100380e00e02c070303050080020b0a0079050f000d065640c500808440b0584040c80011914126504880e50100340f40381c2c0030416140e00c41c034010b590b054400c0c0c10404104440c0800c00c07103001c0c107034004010742d005282917805450411003035907040c0700704401c0340d003059160340c00034400b40c0040d00400b06030300f00880c502c8810395000c60306010300500d4034020000d040c141034a9460310740501d4284d400340150114560740b1b08032254004112403200805075038140c0201318038120b0341c1900030040317803407401e1120300c941050200440781640345213503880114030b40000b41c07a40514010014031500074010101c1541c0c88042042c0020112040700503010311049950b444c103482146c2c2996000c501410091048a4100c00640100e402100e0002c90900c1c917010560704031405445603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 272039946 1250 272038696 272038721
    0x90603020c0f0d0504081b0918150421090b0406030e0f010614130209130f0209030601080717060c040e09030415120f0903020c060c010b041401240f050a03 68
    0x50f0907807010b800d0740c0b2401070020381d89900c0945426202c03000102c40003402c000c00e0700360300072100004111501200308100c940100e921080d43c180c000e0344001d0400050046906a60480f19803806294034154001c0d2480c0f0b21115041c007600c4541420000c0304d03a80594018002810390303c00c00382c1c0c981d000c10081c40d003010300b1341c030700a103d030648844220b18818080d41d40640565045c0000b43c105c00450f00a4a000d10350141c600b201c420080c64401c0b02810038543d0b00021188e00f048440c80c951424450180a040584010412141341520f00110000c620508981d5508480300f4007010b0b030b9640b000c44040b031f4030811280c0c00301d03100c01040d2800c5100320390244400340341001c000300d640b50f00984050789850000710100b005c030a40150381016500c081074024010f8005026101c210721300709001d0252074010500000702d010301580840d04458017821000341709010b8400410104000740c60100040f84040d6a90180850131000540400010b080c00e0040c0400859003044a0b88207034041c10480d1310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 272041196 1250 272039946 272039953
    0x70e040606150f050a0305130b0f0709121110090b0a080f0604020c03120411030f0f1002071205030c071e05010609060605120402030304030f12030e010507090603020c0f 74
    0x1414903020300100894418904120035001c602d2442e90300610802d10303181e0160321040d241002d03040303045008010081005406070414440600456900d2503140e100b9003900150118038141a0805440100964000b52182c1c6030984d001c400508051602106000d0aa441c00c201c055402025100c01401c0c0d0002c8501c40340115540b6407072236210800d9801012000c055a12686619041c442a0720602410421a500c1040705414010720300461070742c401e009840404180c2c2c11400007034200059480c0a011590241c07000381c100c40c0d01030001c0d010580b480355045107800c2d643e5544030b498040700b0f442d90040c0700010002130b82042c0707260120b403003165000340b540c00113a0100003e4485914862010307100f640c40d042d03022412448601c0f808095940c1e07070b151141845012103688107040002041240c050000380400000207030139044100980e8821900d98001407441c3d9001022103001210800300b5a0500040c0911250024001001c1d961285400f50341d41c1c400101c0c4619000e170340d0062482500c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 272042446 1250 272041196 272041201
    0x20909070207031e0b182803260105060f090a03240e032a010c03051e0609060103050408130e0603120c1b010c0c03031706030105040302060c030603070e 67
    0x140d010502c00203a9214104038015070443c11881c1c0750000003035100400244880c0c2c0440c8400f10302d03112140f248a400811105240b0955840307410000130200039441802100e6908020950401c1c070b4881c3d00d52484194141050600b00c0d120b2440700188281c5000341000503015a4107000700c01210381d031100141071700503195520b144c1103034480108500c51410b80069070020220384007038002d01c03001c450040c00440c105a041442c0f9442c000340725146030301c00b082055182d001000280140240080540c50006103840e02c034110035003800802c08800c1101c0b24030010800799507140381100380c10450a10f80043c00b81c3d40da00c2c1c2585244164106d030fa00c040001800000c00c4ea0440c002075100380015015104038442110b2080080c1c0241890341da0550000324600d0715160602140380050f440524048202030029162080b400f0b005800a40001c1c00a9003a0b0b41d0040710180d01581240c81034008014500e4603032002522000c020702007004114001020480b0340c0d804106000c054598103000b2681e90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 272043696 1250 272042446 272042461
    0x5091902150f0703110109020a0311120f210f030a050406020f0309010c021213030209070302041a0901170c030a050a1d01090b0708090616170c070501061a0405090a020909 75
    0x150003030030701203001070298030240200780011f004030444c1c02e034003802c0b880a4505540d15040c0c007e94a4819540000c10702c046060303810010071a101500c030000b0007424164850091010800b00b84c1a0a40c5558204001d803888000050341101e61080b001240000c598645150800291207150501172140c003012088c06082036065004800b008102e400b00c50718422107000f124a94080d41286044a06030313000100090f04160a0b59076200344140b070018075043d1192035030404400003020600340c0314804922062a03507041564111110424510000649481c1100e2806840b0040c4019903060b21000030074003941890b00f12145000156030641d0244180c4d00010f4001e0180d003a06550325030351000451542405000c1d030b0f5001d22034210240c152503031926000544c02c0810389003001040030f25405044008015003240d0301507018100e007595120b8150a14500b5961580c1055440041d04801542c0d50f02c00d81084904482098401c0341c074a55810000714002d010b409142504010710360708100300c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 272044946 1250 272043696 272043727
    0x60a0b0a0503150919240305150109050c04050418050f0c040f0207020a0b0c0f01050c09030d0f020606040f0e01050103060203090d140a08090109020d0c060f030509190215 75
    0x680303aa107420076030150f110f000b0080310301c0003a609180c454411103151041500310350400302100c40f0700b00301c0a042e504210b41450a0034050743c400e0302c0c00e410941003e0021114101800d00500e580181400380b0b0400035400e034801d108600c0f07410b12481d9111b06400d450200c2206d5135125503007103010365040045104040d901d45110360482c500c19894105105000340e698801d07207040d40d070003403c44488030b0304002e603096041d4400a00150039210340089031038001424000c691244a189000544412012040c10b10b445150600c0105008204443c107001e03a03800282907900410850340882c0020041d41d00000514406000300344950030a0700101c18442150005c601424950b000c443c1030340440c00085646e803510001c240301d092400c20000441d94400c1c10a1904200b80600010b0701c126507078001501c01d1843c084c11181c01000c08005c020803500058020440300d101d080c240218588071942030b032520340000500c170f407105c414010720317003036446020000d0240b02640d951942d482d08090103040300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 272046196 1250 272044946 272044951
    0x91f0c0b0a060f2108030421050d0b030d0804020f0d0501020c06060102070e0c040501080a0204080a050d0e0d050a0212160801060e060a06080f0627040c0f0b0d05060a0b0a0503 77
    0x3e0355040d001500c40c100c00e425a02c4804250302e10610301d0350658418000d0340c00540142e482c3c0c4000d03400030103000000e0ba8241042c3c8855202d5036901c42d881404402070b0340c0f180300700340d110750048200707000c04542240c0005d500c06e80c11143c445208a005000584c0082d143da0050070642c0301180e201424030000540600480c804d8003140c41c3c40d59100b0496060300402c44541c101000c0500081100d075004031040c940011500c03001608003500d584010b031400903222802d803020b038851203118060300e803c200952400c40050f95048080801070701e030603640340c0078103c0c001d00400002c0e4203403446200034400c056080c4828415101c0c6170b035440c10a9130190a081c020103031401381d544003103902da180c4283c80710120f1f000b50300d401d401b035030b00e4003001c0d00340c0b41e8018030342ca4100781c9905030300300082c4450130003030000070041000410703e040c6428494040c0030369400840e100c0c0b2100d41c040c040c8801420640380307405507049002c5843d42c1c40e1408181e14941560107a40300400c0406c1141845401102441c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 272047446 1250 272046196 272046209
    0x3020606090c0a121802090a0506040b03010203060a050607060b100c030206010f14120c15120105090114130603020306010f031a01061d19031a0705091f0c0b0a06 71
    0x6440e441e07503440c90b00c1500c030344080b8002150a50a03400784401558104010006402c491500020516000300700d801e00c00f02d916010300340c2e03658100051484c141c801e40b000c218090b00218114030346203020030310900032805494814100403502008001041e0031480d003150780a01000000c4515040c0504400f41854080307016004481c00402c21a1030065040b00b1031f04100d85a040d06000071041c05650712126840d01d845004a1590b00107a44031740b0466042d66050482150b524034403c65003020740007040c2c100512560840d0010000b030f1462804450310180100ca44010075004010314100408050b4002074041c000d0a000146001012803010110b9000e200d400b84007050080d050020901b09018520215080301404178001c81400d4020b0940320020f481070000c242c590078008001000303a8801c454150500c0044888400681e13000e03070f00802c445c1052030809039040300081180000340081c0b6100110a215103044a10400c0100c1c84039402c030314840d4003810801c40c3d0002510b618099003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 272048696 1250 272047446 272047459
    0x1020d020d0903110111010e0c10092d030c120c1d0f0c2703120f04030b0403031404052104061416020a06020706180e1305160303020606 60
    0x20a0500e0011580c0420150107540322903005045507900c400d000c95660405040241d1003207510410b540c2445060138031028040103104808108003004084443c90101200f00a1014010802c20712180074000c1030301a41920b1910847c2064005030070052a6403020380740c070020b100001595040000b54500150180d00c82c13084250f2100b00b00541c036a05003240c4c4041055a100203900c0002140c0c00c603420441c141c12003842d001d01d003003040710345c0e140a1500801c0303031541800c012140c0c40e0801111a074426100b619a041032440c8510310440c0c052440080c00c030402c41000281018429031161200201c1c00c3ea5460117800d01d801c0c5603580d410800114642d150f51000401e1500004500752002c0f81c25994540e40300100035521f00290342c101030910303a50458220404401642d480101038050860303039000300080d0346441d000800e1180032003ca0004804885003c2c030040c6080103030b0036401910203c940120700c1583ca0441c1c0383c0a100c22801c050800c80d07110110030154042142401410300f101c0f070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 272049946 1250 272048696 272048713
    0x1090501050117071706010905150c010c03180623070e090105010e15090f0a0e0906010f03150504050c04020d0212090102190815130c08090a030225050a0e01050102 72
    0x4440449105031380f03420110300001c0c100221030101140f0203034050b0703044c50562555030347d58012070f40b05646145c04000c002c6c004110009450303802d00c983c0100903440d150a000d41d00100d0141204500c0c190805012140c03100c40c0d40c0002d41245880615000829200034800d2406c0b100c0100000b0900004920440f8407500028943d0b01c46c402e4882c420740001c0002c407414a95a003007810300ea00030054903030801950003824285070384001c1034800070700f6001405e0b2917901c1c280d10131904155058115244803101100240302191004010016600312507500142c20744940c00c04078a040c4010301704690003400002d5a5042e103d4640251410895050044140341ca510348031500382d008680c08522a0000f903403030483c0701c42c407407020107810465005040314528145000714004522800b080040c2c0c60719059069080b6a02260469010380000050101ccc0f01daaa03070020348402c00340320385a419145000032441c01400c2526490000c0c01c00800381450b8643d221460001d00321f0074810b540c00f40c0516580c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 272051196 1250 272049946 272049977
    0x24050103150501050a090218040606020d080a0c0210050c1303080913090f081b03160b01060c02031b040209031603120c0b010b0d090503071407081203010b0901020a020306010905010501 81
    0x2450f410303984000c00c00e038442410021090000d400c850b4949601000c0342501440c0340d103407445032801501d2554060400c03c14030a5019088400282a2510891500480c069207a0740818207040000b551000810700e0346460740120300030f007d100310849164040110000401240b0720082284000a5030001034201c0c2c01c5d001c0c0d104845524901903c80f004410310000001c04000052001d42001c01e1a80d805094804d005031440d0405c1246440c0700c140b61065400f0300c980c94581c10b004207001c0c40c041e40c2c1c0c41c4055001c0380d00c420100c40e07032503240724032008810a00e80c1c1d2034068540184016003140c8001d0b103038601444d403e03619440300f5901079401901030242240302e030030807480990304400700813100c0c0d191138454003859100e4000301c12407981e20441000098001e1004004c081e018500d8050000e4030041044d0814107107501140955001c038410091100410781568111004681c03410384a00ca0840141d00b0039601e800700035490300484001280c5541144d0005041c0d4070203a170303076240d805d400384c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 272052446 1250 272051196 272051201
    0x10c03020a020303190221010503010b06181002191a070206010f0b030405010f06080a050d050310030321050103080a0f09030f1e12020d110c15072405010315 69
    0x101d9400142c00c1040010748240e207040c12240e500201c403600502c0c20001c040034501031282464040c40c8034154900410540c130f800d008241c0003800480700755141c03601800c01c011010040f05005070160042c5641900702342d00a000c0da2403006640500f40d500d0b0180b614140d840c011021444100303444e03844000c2903d052001a200d8141c80d65000034076500c1c0c1c204420090203410050045910750b4861001641003005405070800416242c0000d240c1d078813403450400d082408817014001082018001c201040d101043c1200c1203e405003881e80c4d0705882d5440500a4645440e0032407105030900b8000002c1103c2034000304000c02d91540c0702000c07a5810030046800d003000740300103810007466000c002e0100d00c800f44651402c90100c9541046a00701d41e0b40c0c401030003104803040000da0003050341c6021950704050580345007994000038280300c09495000426640c071341d64522a041d40c0200d500c03000c0008020107440701030740135486902c00c04802c004031070282109010445034180c00100f245681c40f100e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 272053696 1250 272052446 272052457
    0xf0f020a0216170a03110102040b07030e04140408090f040207050102071217060a03030e131509060f0509130503120a150506130603020d0b06130f080604080d18050f0f010c0302 77
    0x3e01c050201c1c0801a2001ca03160401a548003045540c20000064103000e120002e00000b0f200c0d4440200d148400e1081000f1140b4281582c02d003c01410304000003d540c1104591100108550b00c1c8000f030b2014000c1383c024000c0950040156200241d010b06002e64201c540b410b05919903128000001d01800885030040103580aa40041e15800c1c10b00000e07004a00c2904400005010402d503145d151414038180d42c41c0b80340103004600019020301c13601e0742e14003860024081210101d070009142001160341d032040103124500f42c11005000700c04100c0180122003810316050310f280f2550500290742402044070750b00070036a51a5008000031542011000d980307019122002505a0601c1d04d03206402135400854480030450f42c07100106039a646400c0a0800380c03c03e45030042e503450800f03400007a0419540c0168a25074405010400000c3d48407044401c043c2b52102e002c6078001000b03601043d890071412000301107000344000d0700c0b403c26000034000c15400440740240401c1e454640190100c2c8180c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 272054946 1250 272053696 272053739
    0x73213120305090405060103090f030f181a0d021b0312010603050915091f1e02040b0a03020703030906020c340303080402030a061103090d0305060a05040f0f020a0216 73
    0xd00441d0703803e00d402c5d40b180c0d9110344113060209040d082507882460031190340c00c0c1100030980301180c0c00603641c0c2c0091640d1201c01080b04603000d05080c0741c10340902e0348100400154140c400508038040c50402d40540d05144180340b120070980c084604075a817603401544010b0003180c0f890000007007261007400307024010040b950180404034034079200f0f41103104c4014550340c940d01c0b03000802120080e50070f41406604014040000d010b242c4c2013500c000303412481d88030030000740c014070080c45601d500c00b0849180071403a0400607614065443c0540140800c0c8074054042031010a07a06e4900c540801e046c410081c464911881c02400240345901c64440c0500541c2c604a0034030040c000203001c1c0d21080e4001d40020115800e1600c00d0350f480060b101000515503071483c0200034007807014030030400c40d10034a0040c2000e00484c604040802c411040e030b4480c080c8516198140103070581d015a01c4201e103040e000406540c2d40a0f0000044e659600070300c0d040e40000e80c088800246035409500511000c4003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 272056196 1250 272054946 272054957
    0x204031106161509170405090712060f060503040506060a0e0106030e030c0106090b0909010522030c02031006050a0e060a0b03180703210e090732131203 67
    0x3210040c414240c2008410421a070414102c031004039001d41e4881c3e00440f80d40c0350124414400e03180c10318440b4250040140c2c0707000207020900440e680d00d604154044500c2c036048900041109840c0054509130740041c029400407a0086080c9a012000354410703800f45044408544550052000070403491081502c0d00e4040e20041c41000d229403c0103401c540d2540440e410f003000e000182d406c47d107540c2d001c00070b096510140e414190400015256000c0740860080100b03140068548180f11b44800e40315900e8500c4076407500801d4000c50b03644058030b40180844a80004c0c00243c20001d00c80750084605c9503c065000140d00d4840800c801e2103003001501d502e5040e031030b00400030b010f5000500b406101c1e200700b0101e016410303001c11150009500506110014030700b40313816107100b400102880c03810000c10100c200f48545480b10441e402600c9840e003180b4401200c001802022120004035092401310004040541103017805403060322011107990704426500e4548400c0c02903e03401c001c01154 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 272057446 1250 272056196 272056223
    0xa0201032c15071815020309190501080705122208190e060c0304291306120209030a030e0109090e060103050c01020a0201080f0415020a180e061302070c0801150602010b0301020403 79
    0x8540b220a20f01c1c1758450040b242440c51020006e20780100710b4002c11700407503818004009643c3d005440a4011030242465450059900483c560050740144541030240e071880c40080100190703818000b105801c5403c0d561180081e601c5c142c6460703248020600090b0200c98001c42c20b141080c100c0d00840c00c104029031526150018482107148401070480000c4094030a054550315901c00528507403517600e80b0f01207d1800c0041c00f50070384114103a0100c0709481480320380c0407a203001614001603a0103050402c1e03590300c24401210108046c2d00b02100b001d003000d8907410101800904181238a106d0b10a0b181d000e54000f004aa0b40d0b540fa031400390003d4000408142c4440000032003580060059150700410380c50006414141d13440203844500040c60240300030008040340010202400e46500415000c2c100000040d84501500d5848807540b6400521003040242d0742403020010010710000303000c1950f10307102aa882c2c040d18480c103005542003984407000c620781031088809a90b03000518400b00e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 272058696 1250 272057446 272057459
    0xc02070b1206031207051c210b0d05030c071403060411120a0204020403080403140d05030a0c05130b04030c080c03060403050d0b032b110a0201032c150718 68
    0x9002510b2140c0500031340404c020701196a02c01040114000c1000708800d80c1c40d0040d0010188103618981c0802000030740c4011060582c1d8078201a0150901c0007180308440480050742c505a0346000030024480003950110795039001c101c00c0100d0b407203034405c07000002400c024540c4400e0105d50003801c1641500034000145000b041c000034030994042250140115a80818120b9015403c02d03a038642000c5020020446042508014042154007402d5000040355020701140000b0703018032041034a4400c0c03140242d20600940c0d100d10900e250003008a507032040c0550055025010940c1c1c0c20b811000041118200040c1c10543c0c008081c005108595860b201140d00e40c00034024078080c246c0712000e4042c41c1d07604001000d21024284c2c0010100d0804400e400006a0503442d14000c3c0300c08145440d090102c0810004500c940a007000305112044034030840c0200d8040c0700c600e12450120750f00b1244030200268400101104415401b110f850f641d1055400500310b801e20303c004074940009100e034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 272059946 1250 272058696 272058727
    0x90b010207050d0b281a13201b0105040c060e030712020d0204020d15140d0b0c03090102040f0909020906040b210115060c0203061e040b2205100c02070b 67
    0x1c45c41500340c99442d803402503407013105503542000100c3c26030a012007a01d61910b414803100d45c285015400030015001403040d031484950305600d00c60042e54000c1251a030400302c108003c0c0c2d000420302c008204629140c079040c0e644c00c80c03178000d410006150043e07c8106060005245080c0c0b00c03400340b8450f2940c215420445080855170003280c01c10b800780048001c0030f25502a80d40b29a070120311030400141050f9070500004882c101c80b40c4a8004c4808640100b01e0301701e41309422020441000e55031765508200720380a07200b035600802c40885040c3c070004800450703a011005240c030842d62800c10b40c890500300301c29035903007a03460341d0310140b400321114002105000841c0301004010001c40d00e280e82000907401080b80d07903c4440420f100442000840c502070001c0313a4403103000b08410400c00749e0b046048e01c0c40d40b00200300520306904a030100700141030490f54100f2a441d20f00911070b01031102c1c074000307442c5c01d0070b05100e91f0064241012000340a001050420941d10b01c0451350303013072680d451100c080d07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 272061196 1250 272059946 272059981
    0x6180f030b04151116050d180608150d0c0e0f0f151f11120325230919050112020901030e030304050312070504180507030213090b010207050d0b 63
    0x21650741e5402d040c0d03a40ca40000c050007100f1710000601d8104007040c00e0407030400c0c00c1426110200403407841061303400d0101050070000c0c1c6000c2c0c9040c55480d03541082c004191004456540c0e8884558400401044141c1e40c084090701c0170102c0c0d80004d6216503285401043c030075540440703202101030000345403443e2032203401004075008002e102c0140c0784098822300c40c82c1c0074034070500040c03d00640a0440004005051101400c1c0c3c0002d4610301e02021240148102d2001640c2c11408290200e02101d2081028691944200d00300b01a252110810025146d022000031401001700c803180d60001d8402c410071408880d010703141c2c01600440191b4001c02980251358081c18103584004544c2602400c1000e14400e5110740011903480b80b4000709103e405000074484420884200014000194032041070041d00c02e01c00e00104268030b034000b00742d02074082c8001e104141d17400700c07100041456854100400040007030b000c0d41c0c0e0701170300e174414040450203640b00a000c0360303126804a0801e400f980b02c13000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 272062446 1250 272061196 272061233
    0xd05090a030305160f060f11090904230102030703020d0605030a0213050a0f0f0207020f10020d080a0e03160b01151d0d1a010f0609180b040209040606180f030b04 71
    0x4810b0485980d0307491030b01001035810b413407040e40c544000030144050301c240e000700c41c0c0702c00d208d90418416034000b408130400108024020703500242401d004500c030454005065982c88001d54891800400060080d004440c1c02e819031814135600041c90b040124000031110b070007a0a03d000d4074160440340300079180180105c3d40700342e0383c0c180070a2089142e00c80c1d4244010400d40250f074504141c01002680c149614041d84588403481c25140c100d900003a0885000100f41017803881039a842c1510001806000d14107030081c04000b4071151081c601405c0c05019a02c0380b007003d500740e601c50b08224426507148001d41d002c40d40202840740c3c0c19400b00d0741c400004070002c0c207031402102103544d0f0230010341d6020030484a15000100500504014201c080060681c0385040101545042c0c200c1c000306071081c040700011a81d4164122098079641c049480200e400340c418031034255a06001071200700c2c2d58803a01c050781900c0e078000c921007034803404140c101c03134002d030741c900d001d403100e44450500d5070460040340d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 272063696 1250 272062446 272062477
    0x10c050c060c0a0204060806011206050402032406040606030203130201050f092101050915071d0603010b040609080f1c0314040c14031501120201020f03040b09030d05090a030305 78
    0x403a107503a010000c026041c01c1c640948090862841071000340c03809908079030700540001d170042c09525440e40c072011600d6000300001c9003035180d90001c20f01f848403080400900300c240d0001c12020000c644950740c010201520100b12060303844038220128002900d00c5840c4210805604000d03620a07409844a99906061036141604a10004d11011030040350161040245040e0343c40191082c0f02e016400705100001d46141c0f1070031080c90403481e0000302a030092060341040000180e4411901d0b4085040c098102035070307561030300b400da0000d070401e01c241000143e0880b000b268010700070034991200c50301f10006264401c01d0805200980011021800c03c156480d088164820820b4600d68052400344000040340c03410003403a0000c0d00d40700302c0b5a5020f940446071520070380c1e00b0214031a0440325a509c041d800c01c080c0b132004070b00f031030a00000c440603844080b45c0070444c140d1b444010801c5200840446103618030000781135486001d10303d00181e00c07070103851041000c20b0081e4014000b031020000780 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 272064946 1250 272063696 272063713
    0xc030c0610030c0801150501030f020903010903030b040c0e0d06050711060a0b010f031e05090c03061015020a0302120d020706090b240a0b0702040b0d0302060601081311010c05 77
    0x2860550112102007401010810400600034181010405800803030000e11251042d402d840000c035442d446040d041561300c00c3d0b1440178035915410f940355000010700074072080c0b405041c024080c00318000541e1040e850041f04030b051601445401c00301181c0030b04044058403054132548014500200f1244c280b0010203800c40b0348900500c58240311301d20324480000c15849400004203d190158042810b2602d00401107903943c0c610396203004685500785011440c0c0d07407944207040c00c101c3d150f142341e81c1600c210014480e44001920031641a120540b80e80c0902c88031200b42282e0340c07030301c240014000d038222000394400e5604060003040d820380752200252503ca203a030759103822520702c45d03030036116800d00c40c060040303250f00d5060031034180c08101c114a102c41c0e964030000700032601c507228408261400007456000c64070303190003962480354018a040420b0b2103508001c0d40f82d1740e00302c076903070300007011480000d00c06504080540c4c5000d4001c900302031300040701030042d580c1215000064443d03100d00c01c031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 272066196 1250 272064946 272064967
    0x30212010f09060e0c0702100504050d080d0e01022106031908030702100b01020c04051e090a050c15042123160303020a0f0c050604030b0103020f04050115050c03 71
    0x4549000705541e82101c0c14603458012420101c035801c1d04004400c8a12000340310b1500f900b68140c5002603011141055560075404082e1018811688056040f42c0c1032031920081c0f05c62840540309850314100c0502c881580d079850345080f413240d8004030740e0340202807501540b00c0c01d2003001d141e0310002c00303811624585040d007501c0c000303400103a10845081c10300104100c500741d410322044000b004e001d2800c0c0003805007440041d45815403030000b140515903400005540715003404010220104408040d0000e0404155654903070b144401e0a448520504640f54501d050148000c819164080d0070f103801c080c00e1881407494101d20b0b001d003504110719180758801080c541d19a201c0d50710303442c03038182c0307005120700c0c0d129401c050003d640700100303c1000303d042002c00c2d00440e10b0f01e4641e60101054140020350f25040f030640003550000d580086011902104009501c0c3c40f00c0d040e240201d400c1d980c090b8506040005440090262413200c100e41c0c0704c5070103454010780140c8881c03480c0d0303800d4230b060031007480c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 272067446 1250 272066196 272066227
    0xe010e0c010c2a42051e0705010914030304080910030905010e03040f08060903030705281706040218060904020f0c01141b04050f120307060b1903050a02090402010302 73
    0x2040000d840007822070418210245002d1505401001600c09188054210b510100718241325480b074184400003403458248010204254074030303403030000f0f125101d4801d030034414020201c0030780031210307521042003151b4000c3d0000203407032003180c1c025525445d081da0801401003940b00300310040145501c0e2011400003500a0203191403008406008585951500c40f1041843c22140c0c45280d040e0440c0e4140f005240010045940c000c031035041c220340e07540300706400c0403440a4415035041c0002e031009000c03200c9988046c90b071084804081900e20540c9070f000410081741708150384d41c1780781840d4018000c00c0d401c20001400b40c001d0010301c0141480b107010107290351039121b03006004142c3d5413120355080e40303045142c029800418554860290155690614209103c1e41c00340c035101e480b52802d10b801c1903503007001d910400b19218050b41d44800c1d0300e16012014180c8520071a00c155080404011030780c0103403040b182120f42001c01008203910940074007548800203441a41019020400d81c0c4142d20b001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 272068696 1250 272067446 272067449
    0x207060f090f02100e0d121110051609050102101a040f0b040e0a08031803090409051006080c0604210813080f0604120813150e010e0c010c2a 62
    0x10451003100b981284104180480040c01ca0400c0c072001c100c80c8481a1642044640c03015070200040d000070543c6a02074540060b6505001c684d44210340c0c00c003014110640096009891030304240220b0001e00c1c0060b00d168141d80242ca0040c0e105070080189112141c01640802e00260000380f001c614040102c0c5c251403504240300419070710f4968045550a042c4107a4481c1452400a41034103c1ca95072225828400600540310001c40341d510648008418002ca4404100c018020041c0f580c0e58502161520080350303102d1191380c0b0304500000d50b01c1d00807900035104000181318500c4c00b030511035400610244aa00c20310710007090009078000406540040000f1340ba40b1904066030340c40c1c11001444c0060049110066400040a100000e81c428100043e00d0403a0300302116140c0d12401103a68a02c0c451b03002034403150b1384480041c044a444d5000c001c0503060708000303000c2c42110062a540da0003503207182d1070016461416400109020034034000c10f2003030000101041810b11700074284800c0a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 272069946 1250 272068696 272068703
    0x80a1407050414090601091806080d0314100f060f0203070f0305130f0b030606071407060807020706020304031104150914010f1203080a0213120804050108010b1c0207060f09 76
    0x103050045101e00c3c000c9040118045459030854984100000c0006103070344a4074401042000f1010422a2150000c41c05411f140c8201e41c0c0104004000034090404c1c15100c4104842e031501050490001c616680c00b03031101e0501e4074060070701e04541242d0690007141c01b8001c40c04103000d00000680809046050341380a03035030702c0b5180c4405900c2c1e4010303003e40358002d260701000503a040044601d80c50582c3d9200000b10348240d26442c03582041c001c21045640c001c500d50042c040f0210309140c00114241c042c014940c02c44058645400c82640c1c2d80c4920f000250034011800c010400340e28040d0844800101e440604101c602c2c0d682d4001001c2d6261101c0402c0c00c0765482e00144654000c070019031000304070345c0e0800c030303545500354074003815850011b01810640c507000100821000007030348030040204103000d904400c855440c10110b0060b0064050350340090142400024104546415121045044200e20f1003110315080c03154000d61100500f114401d0701e83d9021459038455104000f0b92601 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 272071196 1250 272069946 272069957
    0x8030f07020d020f0a123006060c030c2d060c0e1816030b100306050f040213270c0e01030f0e10020f041a0c07050a0e0403080a1407 58
    0xa1051001e82030507612081001103502c02541c40b142e404d00010350081480d08813075101c002c0303505000c0c1142c0c6039400034190f80c403240100b070345440a402d50f100000c54419421310100040d80d01c400c41100c6151040f04040c0c00030b1300c1d80031180085280c00b03844000924901c0381043c4d04840704094100b040f9040c4200340c0d000d994955180c4421900704840c00080c0310111002650100d1364070403d86003200140400c10080d004048081c6401d00035404252504c0d0000c20980718043c0107031008000c0c048034050036000341c150f484403031068141802a0390000c01120707624203109080103007003800030f800f020342c0301311405080300e0703421070042284240740e01c1c1e07851a510315100c40750300c000240c1502c41c11381440421500d40840d40714825004129000700058080b805681c0724084042c40c80140100c3d00f10f00504e541c40d00030000580103400c0203040c4042e5980a81c0e442955aa040021007070040c03282211003014440080c0c0002e21400300141d20041c16140010901010400710b14001e40854131036000c80c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 272072446 1250 272071196 272071201
    0x405070c050d021c0809010b041e0b040902030304050d210c1b150c02060c01020f030708010f0e06011419020309010306090501081b030f0a06090c0b030721060308030f 73
    0x70041c4501d1076a8070b9540014405884a9180c3c000182c0404100c4810040c00c00007040220400b900541c0109a00610510401d04180910403400c404018504c003200e26224508405061038043c1c24074158008000c0c504041c0ba03c424414030041c404800c0f03034003030707180a190f0316a6402d004500b03040e8980780d51104440c6090f840d110703000c400d0a40d10000c07040d0640804001d64000c1081030344111042e0701d0541c050304580c0c40421564001c00c0683d403155400418020445c04882e00a1803040015a4030f003021071741d80b02291020442640034980c070140200c1c1c0010155402004020200390741c1100c4540303000c92000800616094940006006030400141d040d880d690500850b030180103041c030701300b080c0d5142090440d03480000108032040c100d07404403002c43c182c0d4240150324489a40c0804d032481e0880500c1d061000705130f840070444501654810129421958800350384c842c1000d629468210710100744034945040e900c401e02a100c1c0d0325144088000740000300550701131014041201210f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 272073696 1250 272072446 272072453
    0xf06060303090914010920030903030946050f010608010c1106010e07021204060e3a0521090901090903080103080a0e12030d0f2d02090405070c 63
    0x24030300d0f60200210905003804031084503045640741c1e0464402a100082c120340c1c55050047c03102c0075420040c4064008000c000d0015404002980302d406200203407071541c101d1101d40b01c03c65590074224042d500e19075040880c60b40600d03000d6a4841818880d481c410a8545c1d40c2c0c0e441d0605817038404a075651141c1c800c0080c40400d004400b5041190300300200e01c64800da2102303a951505110304442c10412001088107140240950cd41104c5400042e0703541c0c0c0d84814026100144261031540035400300903a04030382d140d5005602075111100d81c0c0191078485011000ca075a82601d00041e200c03800f43c5514070390440160184058070701805080640c070380da40c082c1004442c21050344000380b01800d02d0030010010354400380c1141520f81c0240c429445074021842210750201d0f05d940c460f0000a00824a01841c03000009408858030102c014003403028010001e0055402a01003180c1c060208001c6043e400120145000380f00c41d040001801c1501e40f50000701540e40903120100426443c1e40c115050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 272074946 1250 272073696 272073707
    0x201140a0506150304061112040302060f041e0c09241509031403070c0e06040e010c050a0f12060e04051c050304030e0319030302031905060d0b06030a0f06060303 71
    0x42001100d0400003031038800041a1840c080d506000c2003e00d00200090410005510401501c031541400507291510925220b00000e416942a4054403c032030001d00d0711000e210a6138404c903071040003000f140750104060200344080c018103e9032482508004900700c16540f081c9460b1042d0000c815600b00007140614040090381d400050101c00001c54680a25030031454060459510001e80c070400310281000c02d00714040c1c2040146803061a1100082c040c42000e5950300844046400300300d82c02d140303480242214246041240420000d0103031410581c054002441041c8080c117211205400c400d074000111040c0ea0000355401108009200c184a020804601800c80d49100c00b8842d0040d044060060702000704001c042044514080c1d9880c0c40500004040c013041f2030003028110b000e0300d0050007030342003182d1036008107a01c5020b022042ea41ca0140c580125406021348103044282c0c0c94104150900504698043c440c82100e0b90000308071890a82d181400b40c0c000148803030075850002e04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 272076196 1250 272074946 272074951
    0x30f021c0c0f0b0c061308120412030b09251412070f022113080d0f1d01090909060e0a03180501050702130510051309020f031504061a060a020114 64
    0x403004043c801302d1003034400020165000240c80c400381902c4445071400f024030b84201003c4c1403801e16003005000410035a88511074800c825038900748048062030041c80b8607820102d90059401005041500254501e0451966200214641120703030f58841d1480901d5a4400c024000303903180c07444c04022010ba4851403a250300c01c040e20181c20543c0d044000748100c250780d4a00b10039800c80001707451350210381b50451a0014802d2500360350603955507140140403150390f80441000700382c0c000d0342e845c4c810529001003d030421058484843c07440c2080340c1c440060056140488086a41d504443c07165101041160300c1c41d4400c0d5143d076440030010224020720039080c0d00660500200b4041e510050380e031005808006001c07041c1c00509903680150b1039240d40c095500446e04520300780c0030301c1d24042d260740000c5141e60081d14804250310721003040c16030f240c11102ca098152100c210201d00003640c0358200040384424035200041c2154100d000400680c040001c281c0940c0d580c4407122402d00301a0411603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 272077446 1250 272076196 272076209
    0xf0a050c120102040f1403030d0608010b0112060f03080c2407021c0503010303051303060c03020909010b070305090d03020f060c03070305070309020a050105130f09090209090c0109030f021c0c0f 85
    0x18201032a0040036401d07031641c1c6c0101d00020310300355403200b1316440802c192540c41051080901686030384054450003040840c01481c005901c00e0010b4070b10503064041d203822107000429a6501030315603103c2072a02e805c104101d021034000c0344416400f001480300d10808014030803401d9515410a040060300c0d2880c1d010b02d03d0904144800d0b010302030768100c01587d044a405003000380d9035560031030040c843c1a5a82d000100501d181030942e810850f815405040030840540d802c007031690f01c52500316a80e0040d243c0080c00260100400107080c100341100800c0e0710303c40e0044a4a00701074031a540d0404070103c40c4060a40380c04410428a5a4540110b980050300d604080280c0384050300840c20400c550702070709050280c0000c000e40d040d80285420401041d980822105203504e0702d4201d000b81c19029000da11800800001c58054070001c9070740001c6c00816143d08203254611350381d82c803001c009200c0981e400040454603c0c028144003088825040c840c84802e280d00e820030111041c500d810790000d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 272078696 1250 272077446 272077451
    0x120319080702121b0f07080d021908160506040f110108040309090c0509040906023411010c0b0708101505071b0513060906090519050601020f0a050c1201 67
    0x2104250300858880c8000355980d810554036000c1c0d41e03008201c101000c80c1081d8603c0f45c100711501c030390400b00300c4200b0303a5a01800e40b2102c0c11102000c80e600e11000c242085c400104034108400100702e50020100a0120302001101107119154242401401c0b13405940e4035241c80c0d1074104011174148003a80701c40c2c00b401e091034030703040a0301c00920025050141805060f41c0300c0c56207003041c0c02902961840280103100303004103071007071078403001075080180074a004075034012410980510301c8007400e605098002c180c40780b814072a150380080304000c0b0003143c14004044440b070042210500b42c0d5100e88a04c0e124a409030070b103051101c00800f016030240000f075107001d40380d0010b107074401c0440d1607094001c451000140490708090300f034003500c4c1d449503074002c4581c4440b92a404181e0019401ca6504c0c0000700041a90707945401c064410440d00158607007400e46c103910038014030345c0c010f0750800c1d01841200c51800d8501c5031a403410003000d8007a51359074001e507060146d900c1c018102d4002220043c00a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 272079946 1250 272078696 272078701
    0x203030712020f07062c070f090c080a1e050114090a1a040504110604030b040606061d1c08030a021b0307080405010f020f0102030a02360d0804030212031908 69
    0x62075140c0c0a406001072440340c0310b0422204940da50200b90540c0c1d40d806c03480442c80381981420304d82d01c240520030200c100300410f00004405c0298801c583d00d6080c141c640f540150388804404c40180720a82e9070f041d0040042c0b9020308420b4a03403040038003030148142000d9044819504220700c25500400300000c503400c25003110b00000c01c007010111300f4203095a002c601a21940f400342e050044401210303810410102e030000600c0b18a50000e8022802401c0820117107071150350454540d11041d2204000380301d80032501e105810400c510484040121400301521525071741d910a040c2e00a07602c940e00d903500807600034142d104010308690740c22502c2000b103103414410364607501140240d1040d503060000744e02c00d038011240240f00215503a01c203507000715664680020200300940101c94120300003280c900010005a5451a2440f440c1c102c0780c0601d00904094004c012407050200300c1121040c2d002e020010058907082e041e06075140d41480995212040c080d4000040c1020041420400101c8000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 272081196 1250 272079946 272079967
    0x6021201051c0c120c03021503040210090e280905030a1407020d12050c010207030c03092c070302090301090c030515010b070204021602120609060109060803041e080d020303071202 79
    0x5124003116900300c1c44c03140740003817810903004500700350344040d402045030b40da219403200e061002588100d10848c0d04c0700f001855410210750509007806110341c41d9808030040f5400c40c042420340540b0040e0107540c010042d20509840090714007894089a803070b4004569400c003d0b400840001075101c020007000e00746062500012121404110b001c0d1804100c3c0b035211135010f00c110100c540044080e0006c0d980c2d040d051070001c0203203210303801c103400041c8500300204251008110314000c020b40110029a0030040307005420349018058034010030f140c1c0c200311610b05d83d2820302801da92030b800380519201d014614100350342003c943c03200f0612030640d0000140b08491000052380c5640d80c042d10010303102c26116150321102001c0b544d000e076002c00054002c01e40c20f5000603c0764400c0540c1000e0f120070382d070f0340c0142c842561020b0048140541007480140030b104c95102050501860041104e10919602c01d109801d02444800d140e0042e0000170800001d00d8004030200307c2588800811441c0824200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 272082446 1250 272081196 272081213
    0x20301140105131a0f03030c0607110105061507060e160f09050603030a0f0f05090406171c02150405070b0c0d0f051e0306210c0112050127020706021201051c 69
    0x3504c42c4540491310b80b2240a881c104140e486000c6204225080340c1040301c4081c00401140b04015501c3d803c1000050301420078035400d440b140b00c088a49402c141913940c3d19800b030074003501c9040780391040c103d442038141c404080050082c10103184204482d8100100c400c141c030340091207140258020800716009a84c8020803003403a41031490f041d030f58140305030402c803500c2c8a52a0b0482d07105040401c0403c50407035100b01a04041035a8044520f40311582e004800350b0000e10340644056000b4015403400d0301e118002e0164414400c1040d07501c002e03181c1107400d4440d0000c0d240300c0074560203449155159604481e000e1a86a428281942032400410384160f18620148594501e00f40c0800424140c0d01e4810120400041041001210204429125507151002880700740000d8201d02c0088403802d0a204030360680d81680b40c3c92021184010720302d000c40c0303038800204540039070030490000881c80d10b2000e481c444001c42c1c4c081b521740d49001d0402502500041d40c000c8a210347d040709170009401403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 272083696 1250 272082446 272082491
    0xd27030e01180504020415080f01050a18020702090a0507110a0203030d02160212030c01060605040302060a0806010c0c09051512060a0f0b091006200a02010c0c0302030114010513 78
    0xb40b90520303540e84840e00d040c140c1c0300180d014540160012502140041e00005110b100d502c05550300c50303046d40e503415a030031900c83c20310580d5007100a51000740301001220030000c40c0080362203009882e1415076804035800c200102c401a0070306540390b06103e0015400369a240030860344031300030100c084203a0006503d03841255036020640b42d002540200380c0040b43c6464410a80091403440ca000c0c0608002c1c1d12a031040c802101513500e040380100d0300710702400070354050381c0d0084d00050800e004010300341d03081000070f0300305418800529400c0c3c0000e0002100480a48403040001c40c2c90304180806905500e01c441d051031007043e21000c100e100b50310004407a50702c58080c0e0000708080c40c50982150080c103081d8005c5e500445a03100f0002d03914100344416080310a156149002c40c0200c1802006a01c00d0b020407404503048a820140558031900041901c280a00541c07052a60b99a000900715600205140091107034080104020b240007010307040703d404640380038000b603100c9010709100207408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 272084946 1250 272083696 272083699
    0xb03011505090a05030d0207090e011104050d022e030b01140a0c081c05010e01090c02150c04090e0d120c0917070e0108060a18110105070f0203030d27030e 68
    0x102e020569541c40b540303c90014403000c0c060381c100d8824004000c2d11100207010342401c035801e040048800b150140704240720041c640f8412800c05040000708065500075160a0380d01104820115560900c2d0010303400c010101445803900c1c003200e010018058030303150340708241030085a007078050401000e101110303418404c1d850300c0e060403d00b52904c1d9400e4020805078084d04024181d81c800514003c3c0c1c400c50503113010b2500d50606a99034441c0c00180d40d5042504801600001d2031649ca50f10080c1100d500607191920a9040980f90703414981240c115082e9a042540030056034a146504134404070000d03825035609004c2d92944910240c90f80c5424071500303d0f81001c00c4c48900c03500400b840755801070210f078095407035a542c0d1444165138401054070110701c814503100c0508007540740800c440c60103030383c041d10072501c80d8030310030040da415080340c1010340d1500c46104500005940c02d0008003070382e1182d031000107852100711014041c41d60065079150704010f200074869002c20b07009054621811340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 272086196 1250 272084946 272084957
    0x1201060b03190b01020c0f040903021002130303090806100308180613180501050a060509030114162c0904080c160f08010b0f090403090801060303020d140315100507050a0c0306060b030115 82
    0x262408a00d01201502d000e02040c2c40440d0900007007084412000849000c2e540c1c844949842e0144b40c1d840703501c2912401400c800c3c0c0c042c10070020b0340300c60150030145030002c45103544408100100e00c4580c40300000c6900c0c06e010346400d010104484448056102a621080219606100228480d20124054141070120200740103503659804d42016840380b1074016030b01d0190400610307452100c04034a0641010615038102e07943c00060020310700590518060700b503040c804810060119170480030f401a51010f00c10000300d400c02d80c2c20450480c100426400b1000101d02d0003109a4003004240c22000e0182d04119078403107503070b4445001c0440781c40220b4240c44291074606d81503a400500d6031010b0301a5091103000000d1540200310070070114802c2d2281d1456510206004070648012150250300014a2510000c0c07810090800200080d0f1800e00c40d10340f4826442d505e240800d908021070703d65600c603100340200925801100000c09043d00c400c0d0865042080180000d0b007982c05240400c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 272087446 1250 272086196 272086211
    0x90b03010902150d0e03072f090f1005011b0b0709030512030402040b090103030f111212010f09050403020607110106121a10141201060b03190b01020c0f04 68
    0x15020340c400d140d078a6006010700c1c2d11040f40180114150010710980410a1038000c000c1e44015020040f1440e81e0380c442c1c01031010442c5500d80c130460346a04401a040a055400f50204175202c41c0704280c040c0e02401051101c40c81e10031907025080e442c6410440c100000c0854007070001c104820104001c580c0950101c034a5aa080c0f4101c43c9940d0359400544035108032141080c1d044d502c0c0b00290301950080d10180060004035040c000020001c0c400180010441103001d4051442800d0030301400114809803061180c103e01c080700380d6004100394141481d046c4004129040328406100010051300c90305001d28a082c5c0c9001e500d0780d0b0300400c48010701068a58244104600394850320141c0715a060000541c840c2c3d00b02401c00f42d44031801309480418400c0842c2820b0716580700c080c02c5413160b1400c0e0081c1110f102c140442610b07c280e01c4034141d920b1343c03000700369106080042e44c4244034200942203841440b004107026120807068050654220703c28a01903600e0f4450001494502690301007800c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 272088696 1250 272087446 272087449
    0x3b09061f2303010204030804030308150d1e060606021f0c05250501050a24031502090f09070e090a0c08010b0918010902090a0e060d020103090c0f0609030b070c0c090b 73
    0x2503a8581c0341d592551001402108204002c006003050304e00039600c01d82d040e83c9280403480003120300f000d4075a10000d440d06910002d0b02140c6070401c0c00c8102c010294089000c5c0c1c0d41e104c240c2d251908403402607048440c0f55020031032003500f0040054041e450074800c0788001e0034041c28a228902442d90b191007091564400d00b00742c01300e000c0e207190380070000300040e1611488050092110818030300054a110300100940307091510b040e4152038001d00c22030100c002ca10a114020b500060f081c5800580080d0f2401c0a40e0b12230309498480c400139183c40b440c20301c0780010045039040007812824802d241c100844841d5502050b080c0c150b6002055041c0d96040350720024143c3c2c151801c06041e540d59240010070450895005041441c8080d65500c0d40980c45d01040d261001e0111042900040640385c1c400256103c3d401600165004440012034180c4a4205000030100780d00203801140701a10100100f08140304056440629803411075001307122903580462810240c45151191519084483c1e40c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 272089946 1250 272088696 272088749
    0x9040206030a09140609010501060e03010e070915030807111009080604030e01090b1801030c0302160602070c030c080d1e020c0405150d140601080111043b09061f 71
    0x58800c0b6001704d070518544820040c1c046d0409004410008070810a030710403505050064450300c0300707401c0103040b0705400d050707003800142011980c00307072002415000000800d101a009180050040b203030301c0b6000102c40c0030302000d00200e4040604024003000100301080e0089096a002507051600d40c0805160000484600b00540c01040f9411400103054850001c0c60145181c9007500fa00c0603c606010282c09400700d024001980f0035080e400102ca8000900700d038010b00e60303030740f00b07230501402c59899844004034821035800200c2640d0142d400900748642000e044600354803545140c1007045594100291221000b042040c040d0f5103620129501c2060305041241e0700e20040d01044045685040a840d80440d0516001c41c1d402201c0000c264080180190076132120f1000d221480d01e8603280142d60301342c05c1c40c00100090702c3d1030741e01e40c518150200345203480d0603160b0b1601843c038140400610305025020304481044521101d0700f040d6500050f100c001161102d8542e08424139000714014038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 272091196 1250 272089946 272089973
    0x150c0807080c0c150c150a0e070e01090509060103030c12120509030a1e020309060a0309020a0b040302041404030e0418082d0913090501021e0a0e09040206030a09 71
    0x408000810b44580c48000000d07542011001141c130744c448840c0e40050440c05204640b146440e0303402413820180b1640300000c41c2c9800511801000501441d01c0c1daa10382000e4081c0c100305d80200c46640100840030702c03401031a8206a01d40040c0c601545103030b401600f521800b0704000d001d00814a07031100b0082c01002d0303001c841540c800c1e0a001c10300d45000340036102c2c2d208a11010201d5501c603980c001c191140244441c0c1c600c0141c00951030308207801300b006515000321810700100760f200d07070011005840c2d00b02410024440b001c2a55115800e510401c029900c6d400001d000152a00c3c0411010070340c003032800e500d00c0100b5500080d40041440010089101061004c0c0c60540b00049003030301c25141607403120312082410440b14101c0f440290754111803003444174580d40000b00200340c1001036660381c003c0710780d144a54001071500c8220701100701800c1500240400204c4d000c40c082c40074640084010149000480d81c40c07486150942c0011f120303001c09001a0f1016075100c03640c1e010010004201c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 272092446 1250 272091196 272091203
    0x601060201111611030708010c0f052106190803040302010908150a0213081f0606020a210e0d06090308060a03021c02030102040b0c0f120403030807030b0411040e041b150c0807 77
    0x10112501e4010b05d60180000040c270400141b00c09000e8600e080c410016100c6074510003020b1328900803000550891110040d200a60108a0525107040704120803040001048500051500c89145000260260f482c0f5840719036950408102021141448100344da40502c00b9031300107886288500c66503030004410b42103c0b80c148214854060f070003003d038420814bc1c60b4406028030046440b018220b85510400d14000c01008003041c014030b03910180c2128a210f82d0b0a440d1800d036000700c0800003015084503000c260341066540b80190140341d40001034030ba010505941e085400c0d86140d0100b25030411a00d000004610841d4038a011960290101c4d030042501d1858aa20390f107076011000e482e050107449483c500c1c0715010001c0c440511240a030707000c9a0b00342d140d25482e0303503031020290050580400780e183c0c0700d540c0743c04070007068048101400140104e0b05220410b803a2924001078203007101d83d10fa9085c1c1900550401c1f100c25008110030421106282a58900c072a41c5010711940c0039041004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 272093696 1250 272092446 272092453
    0x3010207050312060a08030307030905032104030815030703060911040908031009090b07030c02010608030a050a09141f0c0803330a06260c0309060106020111161103 72
    0x100070700038000090000d80c409448112460380700e80c070070444503221314802c1c07a0007904244002031403036000e40e00c0ba207100c0d80a001078a1034900080c8501100035694041c3da041141c8810a00050640c0324040580c0500c103c0105d6880c5d40f0108006555075065110050030f541c0c803102c40b14100040d001a90360345040250003440700580c43d01d4003c0e4160400c0303c10100003901c0200001d609140ca0052004940e009980f800c1d298031040703800c4002d09500040c0350250b649072100010088010001800a02d44541e9950380301c3c002020001c0a5608542c0329042e0070705522a180385507070b41d0440e40c4034420310041c0c41c0802044001b1054849959009010300390400110030407105207613000021101040c0c143c80c43d076401c1400b9001c6424019200402c580040502d08103104803402030603c03044500321a40c081a02d401e002d02d8410408a04940040c0400000f0040c402d2481040241c5405420103000a02c01209084041500ba00070000164200d4102c094a0f805000d40003001800c50341004d4142d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 272094946 1250 272093696 272093707
    0xc0e03070b22080a03020d02210f092d0405041e140102030c040e011e0e090a0204050a0902031519021606090c0303020c010c08120c0903060709051f020606120c030102 73
    0x609444004146042d0091f00881b108604c1840c808510a1130310828141204820320300100501031540210002c0c0e10385000070003100045a1340c01c0760a1001e4611051007a240846017150f143c090204100910b00617801c04040c00009034403103915070704800441c21426400201820200c04610825040850651001050090080800d07006009403500e164540d11566a00da0302060040c4280b070502c005010162400c0c00140740d4190460b411000f24400ca80540b8200c0e00018100d03081558401c0e401a0303900b44850440c1414080308201203420f44141d0030b80d1a103100b005c00044000044002d0180d4002031001080d46642c0d844c0c2c030541e4000390308110041e05132520602c611050f00042e40548240100c1c109030350321480c0714241050703100c81c03110308000b0710440300c442c9908064a41ea05c0d40c80300303111405050302c0410402c0d200d4816030f0340d00d071221403130b02c418040114080c01c1b00300b11812000f840b0b03081a0341c00081c0380d0340218064034000a0f11100140aa0502c801801c101e81e042d400000c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 272096196 1250 272094946 272094959
    0x507020a02181b04050619020c132702010c03030e0a0b090f06090c0a030b0c0906070f030305060d111215070906080a021e070804030b070c03030c0e03070b22 69
    0x2549100e01c3c00058400b1000e000d00301c039680741d801948103c1758407400801541024100c95110800494003d00440d480c0d041040001035880302154106e50803c1e80c1c0340000c0f060003140306054090f0004220b030021030b101e490b0b00001c0200c0d420400140525843c0d150a90000000b006805803081d0403050107421400d14100d0207445035414903070076410340329040201c0c10000d40810016081d810013400f40e91191302c0c41e9100c01c4100700c0100300644030032050008002c02d4562000070a90b8610900c5c14200102407841e010f81100d0000c1e1006008184601c000e00c0000c8001a040200a104aa110440700303100c2d0703445450885040505115800361205011446402174141c00a80b0b8039520741c0025903071003e00f00d134224041d5041d183d8180110060088010240703000800d5154028900350b85001d44135212018211000d803000e1000a0482a171350707003071542c035200b1040e07880420328201c600103240c40002550b4504a00030f6404840000641c40c1020902025414084058942c185201640c3d241e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 272097446 1250 272096196 272096239
    0x501020a081602060622020904060803040e0901060e15040b1005030a060605210606070f1a010e090a020105090102010f0f06051810060e0d050604061e1104090507020a02 74
    0x44039a40e10748050260380c000c050000c130300c85101c5d0501414401d16081a12405420452182c01c8000540c4d42000a10956140d030b004841c0908200c800869030b640c80c220840b402c600d002002c03103816034948038040c00028a070155064100900440b0700d8181a10500003030b000f00058118141d114414044880d20550880080d622400504408100b110b540d40010340d0280303d00c030441034041c000705ea01c01040c1003a00b05803540009001c0c052a0030401d85a070b541e010a5242c0005980a1a440c00f0642081c900d0600705030144c0810201c49496050845200c0d81d03071900d154000303060042c08610900c450f403013503001401200c01c40d542401110f01010714103006210307078090280035122001d61802d8210004070a5801281c2480c0310030f44440c58000101c0305140081d240607480385d080d040d4072001c02d400308440c80c042c40c028070f000145641101e0003000d403034810980c1c0c42986070812070341c0e400c140b14850907038088420703106000c1703403e95448000b01c1c28013001007030080d400070071680025040314112 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 272098696 1250 272097446 272097451
    0xc09080105090f061807120501021305040b0303121506070605091504030512190e0609010501150507030e121507140322020a08030a030b0f0a0501090e040f0501020a08 73
    0x9008001e1920b6001281e5100e400d46071a02049600100124001c0c22000050390080c2601005a0310300940303030000d944000710b489105995a030f401203100d80038034a20110340b41c0201001c03501008588002800b081d1603003e030105130f40e48050b0510010340500308a031040205200d000303013556654001490500d004000540303155801d03100d91114550000c03604451079000380e4040c1c4502d4146440084400e882e054000e04c00e02c11080c0309443d10203050310a002d00c21410003042c024280911b00541e079a0f0841d60140e0000518044a0000190f21504801260700c0960140b4201901403c3ca4000c200d618007030030001c3c3d605103d040014807216020000312030183d12140e0301d0002c500f101e907a03100298003003a504100540302098007412905201041000c08070310141014410583d19008c550079500140102c0340403e8031100301900c240381c501114410f8110880756210b0181c14940020058410760041a1400346014041002e00c00050706405c19180e01c80020741d030365024000d0040169400b07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 272099946 1250 272098696 272098709
    0x7050a06120f0c080112240606080603060c0d0b0312040306060503190b060d0f0218011706040c05010c05030f040b090f0d1104110c191a090c06090f040c09 68
    0x1e00200b20040d51440c01030400c00412940da805a690810071001054108034104503402a110704000c441503040c298421030b0a00b141c10000b0b020b41c64140060b0101d040100150310030340180f42040070880c40700c1d055a00032132001c600080d0442107000402e203060342a4105180103000030500004116850f0409000d03100203909485071714407010b03a1817010404245004101e50741070340000e1208d05000c428508034034024012141103080c603802240f1029500c5d0201c03990302415600500501c1c00c1c1d1541d40000c595000e004100c5807800b80c0381c0c030f41040c1890085e50704102d440c51182c401d126003007041c1c46003070190340646542c8a60f01c00c0380e07842590045403003500501004185911504e0701003604c0c0c54030342e0010410009e5200d2402004000c0004401016054009104011032400c08000c89204c60428a4425081c0e00301030600100c80c08a42e02c01340401940300082001194000c1240f002040c4141d031140e45540054000512007040b40380c860307412a14200420ba4401e61150608d0101c540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 272101196 1250 272099946 272099951
    0x12100203070318170f0405061801090b0f0d0e0a050601140109090212060d080f0409020408010516021506060f0d0504120311090d0f05060915060103060e160207050a0612 74
    0x20807410010700c07441c42007401360203568203c6002d128010344500400c031214628595500e015100d0000901c10740000c01c8000f2007191141c0c40301a10b581004050001c1e051020649040c44201000b04040d03105131103091111a49038190f85141c248108881004142d0102c01d840c42c660319010340c000d0502c40301071102e000941101c8000303540915813080702c0c54840035505032001c0e9520f240070300c0821403200408542e2070108100c03821280207050060809070a5112001d0380da217140c21840c900756640a015030751000c2c00004140074550f0000350f00c0742d07150018008374003644e817808001100d5029003000310724150000100c421078070005a0181d44650b100c0e510542c2c0d4100302c29412800c90750600c500050541c01000b61140504c2e103034888061891144001d80007500a40c1d850344c1c20600141c640c1169548040300c0b00c0b1411f01d01c0745103694030100c00e00c1c0401901c0d1808040c189040c1c0b0240140103081102400140c00d140700340b10840c050540542180a1103556600060050080c00c040c9810f851 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 272102446 1250 272101196 272101211
    0x90d0b0906041703010303200a1b06080a020f04030212010906050403030603030f08040b0a090503040b0c061e09060103120c021009061d0901031b090c050702040b01080603060411121002030703 84
    0x22035440036217060304d815039034142072241500d80003e80510010365100d59440346000400000720000c1004d64400032880030458031b680781003005804031201820880e000c3d80103000400315141940191411660111100d5440c24a8040518011702007003201a00c99404c0804000a02d41c0541000007101d101e40d65450b40c015040d08110b40701c000545006000c84d080c3d50201e0300900007508824501401a001d0b00d20306540c0c0c585d880129032101c4142181c0341c0044007081030b000c21031a1800780c40c81c2508112007861900011a5480d802c05000040102c2010b000d01d0701ca4a00c5121400309054ac0913080182002c81c540d40602494075130312407080021420040c1c4000301505d040e030f009400c0c10140084010341d08560304c40c0820900c884048038294141840000ca500841c0600c0d100c540361516960380c1c0e000300b40180020740c0d52282c0068140300188003440307015200010000e9100384c00c01e4003001c0501010000605642d4480d50042440c0304241079040421010390046010b008a070f00c0422205 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 272103696 1250 272102446 272102483
    0x306090c0803090d110a05030f2107051c050903060a05010302090c160224040e27150a0b040e100b030114040305030c0d090615050301050c0708090d0b090604 69
    0x24494600300780d804c110107113000c130300003030352181c01c680300d014000c1104001c45d88500110386045001001c50f1000d901031710b4100380070640000c1411510b000008494504203c9444103556445c016800a512501c4803200c421006d200d1019140c200c034005007581c040d07040421007000030300b0080c001644030303103844008900d0302800700040341c503c443d507040b504254807031a0b001c00c6090340201210013031100c035020100e44034100d10001070014081080e5801e841b42804043d0074400b0046045503810170403800b22000e03041200003840c81e0942c0307904000b46481c0c0e813880445c1e00074100b41c45200380c1050400017280002d68001c540c10024000d21242000f151100170b0416083e40e45400001075003010318070100d400301e441040103690001503841039500c2e00505540c0c6d2005c46180760b07000c1c1d80d0203a4600e2500d0000d001122502d00408045000b0301050501c1eaa840401e071041c0305006000d03510005050703016480b03401ca11541c40d0341245007110a85401d001c03540d1500070440e001c40311421094640c10302b8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 272104946 1250 272103696 272103703
    0x403030c0c140d0602160c08060709080102071713080118170a08040b0a091a0105100e061b0a0c0f08060a11122701020a02010b0301050c0d0c0c06060306090c08 70
    0x14503000414402c207005584e1550030080d80321146401200300008100c2d1301240d6488001d1008142c101c0061046140000c1b001b80803c070181c010440c0c07640100138240101c1d030b82007400440408005203442d80ca0911829401000e410340e07003c54102c3d4248000142040071751080307294000d0061401d1482c1c4030810111002c0c511444030900301082c102c10216002c50000c501c096031061100c4400245400701b41c03100900e1280389400e0700c181c40b621000501c083c0c2800c0c0381401d0001001c1c20104000c02c0e29500085d00390043d11144444400707100c40c0c500107445c0070080c540310180c22010703458216448000d07a50b0403080764024417901d8451200482d100708010b1150701c0c09025440c00f810304100b001c990f04050240c0262150380700d07040d0b000b004402d900421042e55003c405000005940324440d200103070944d001c9525035442a4500b10400200b01c0404c0f00b2220400b000030000521880d05000958000081c48006020a85845004410894142d004441e854083c000400e2680d98035440e9995 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 272106196 1250 272104946 272104979
    0x90d090e010308090109120605070f020303040309060e0d080c0606030106080d020c09061206090105040309051504030611160309030b0109020301051c050f0102310e0403050a0309080403030c0c 84
    0x600d44800d000401c0458036aa001d4802c200c030502d0911000d50355501c8109031b0711800e00302614015920700900001c0c030740104221940500c9400594107500e4207131000740c162400d82c820502845a0420380302401d643d1010549070b0940d0050840b0344030b80f15950741c0c540c0c03400b003196247d00075131030050040b80d5a000003901c6001c019076580244014140c05040c06014000034280c4c1c1c0c2c008095441000580c40c083c000342e4401d54500713000140c145881c1c20010494102a407240d8011080000c4203460804408212400c1d240c003e0400700b000d40101ca005e0784103100b420141404034807540c194404041d4080ea01c241102d0180c0b01d1940641d0300d44103e03c080344000c0c401c441d0721030344015800085000d440d0740480a103010354259100e0849030004142a684451040904408078854881c3c0841d00c44003884000c20000b510030640c5400e05041480c806000340002c1c080c0310001c1a03034440b00d8481d8200c0c14070b080c0d100304040d881e6542c9183c0507100181c1d450048a0085134034001007100030420b6590704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 272107446 1250 272106196 272106209
    0x151b010917070c0909061e0209130204050a0303030e1903020a03020d030b0d020f0a09020d0e10060323070b0d0501061e020d0e010e0a033504030605090a020414090d09 73
    0xc03019460640440010b1024000c210703943c036120340e2030003505461550360384801f02c40c0900250f540c1840d801085035854004042c181e0740d510520003071080380c0352800c6000545c0d074182400a00c60600401c80303441e0444542e0410f429062003d03256040503408a00c2c22585032094003121203680450500b80c050302d500c10b503840d8104220307001c40c1e4054075200303403011070122004d80030310780c6a91914500400e0ba806610401d801c241c85090150303504004020444c0300201002c820806181036030303070310105e4007840c2c843c81000250f280030648a0041c00e0150100038440b4807801e0360348401801c0c407903015002c2440340402142c103500c0e410b100043c0c0705006410003805540130b0b28114584207015210b41140c11031036410000440300780b00240c6c9602501d41d01541c080c034070704155410501d0200030041030481171000f10b0720711400d2403040b8083c01801d485c1941c0d030003400850150f48804001d031501c0e0300d105003c5e50180c2040804441101c1e14010640182d68140a81e1010040030718251000400383c030520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 272108696 1250 272107446 272107463
    0x909070e1501120f02090111030f031b130e1006111e032b0c050703050f1c09120311120115030207170a0e040504050a02151b01091707 59
    0xa10700c8609088014605105060a01011080c4441d541c102c1c0c590701d40409a413a40012031034200d6800000416042144500071460084c03480004c00076404040c10b0580b45071070700c001c4081450100010764066aa01c48001c2e40880c0c1d03540540f0408580c1900d03031304500e0040900101d282e41c0320751701c40034034a5880d500400301c0840d00404440103110401c0900140d00081c8800b40222034801c0b00c4108211b04000c0441d1034008040740d21089039401000d00003031100400c82103001940000c1a2110a02082401c50b02c4014074408610202c502080302941d0520340507000042000342001003003411240d40d0f04000c2000240e0312a4414446c2d030007650b50107440000100301c40b0360018a03142a90005107405428500c4540d60401c1085042d080000542c00c007140100c0d400e54854440c040702281160709200a042584500380ca03440c40030340290003917240014403244c003021041110481048460131301d0a0030071740380c82c0c40c4c020030705420101d8021041a51000315498101d042d00c1c0c100c0d40100300c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 272109946 1250 272108696 272108701
    0x40b040210110a1506080303070815010207030210031406011d0607021504170f0a08040b030a06180605010206090610060807020a0804030c09050703090b13020d06050a02090909070e 79
    0x200200d200410808038104010401c0440d0b103a0024010040068801d400482d41340f02c25201c104143d0b00076410082007607006100300280164030110054101d1880d5601340060503207540100c6c00c1c0749054002035085002c440145030302742d0341903114441c00c0709101003050540d110807004403120000c1041107180c1c1240d040f014121031a2a40c020120b0903c001c10308082c100e0043d0084005401a0b80540d4510000b0700c48080310035028050401c0c85000400985618042d51383c8681c11401140242c20941c080480045c0c2400c8a0358086030241c22000c0800c1806039144be0041c001e06950301509005000300340100e8549140041c055009841030055035903d541440c0701140c400c98010310220451141ca024100801e14413401400170310300900402100b14204580b00081d950050300f02d80070180342016540c00704110312442c50b040500d424110020680d640005604a40d00a50241480e4902001c2c044803010540c01400720300e005589005483c0e49070858079441d242588110750f0b000d0700d038100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 272111196 1250 272109946 272109949
    0xb0406052101140405030c061305100f0e0609030405100206060d1205040b1305040c1e120b18060a05060414010302030601140c07080631140d0305040308010e040b0402 73
    0xc5500d02244074038000107400d0030142410801080070344065400d6040002c0e881c1d1101d500344002c3c0c0d0301002a20003105036003000d42d20b00b0350300c828151040e030080f941da081e00403110400790804901811a841128440e0900c40d1000340c580c2e11500c00c0324411094400000e81150021800360700c180c400170080000b124a5449483c1c241d09003804000c00c0290400020a400802c600942000b071040c1886241c030f681003106000c03ca950b011300c19410b011015800c080056440244a01d50407c1481c1c070348070326210000403d0207002600500c6600c00c4070725034041000c1e00345444031440fa100465140681a6a40d81031103668862030050900d108020858807a45500a800a5401c05818034181c0d0a02605410308600c0f82c0207054179143d250403a044c100f018020401c40ba9400048a20503a0304040e0340d1543c180b4071901c421042c001120b448845002440810501c00c984106c00303209946117001035400c003d000300070032101100450881400401c3c0c07002d40b56071007440340d40c0c080003018a544543c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 272112446 1250 272111196 272111239
    0x901030f05090c1e031b04180b0604050106030b22060f0b0706060504060b1e071a040614070f20060708090d050901080a020706090501020c07060806061312080f0a0504090b040605 78
    0xf440f06d0b40007070329801641500c04065000f10f1105028156000907804c00800300020790300182d0142c0d00301810610380c0c960513603d1500c0c0014900c0a0842e0b41281240311310898042c0c10b0717940c055810344c14000c900188002c0c00d000240074592181030204841c40e02c82d01000b0482d0541c0c003c084001c0c4050142101c040381c100e4904880f403800303c3d461802c01d40c681d070344c007500850220307040d4107200644c000b030104000190040610300030619200504e18600307260002d01156038030b02d4a40c1004005c00803a2000c103a1001884150428503065134460b24014201400d101001c0d92032042504c100000340c40880e2048050700c2c0d140c0350503175506160762502000075010750080305064030f5040c2d46203030440000d5401d01c000c0c01c400c501d50020346000343c03800c440a0803030500100f516000384800c009030908680c0b60361050007070320b200070080d084600c89804c001035540225140c00140481c0082c0d880030340c54124000d0801c83e01d461006001c0700c0b243c8030510060345c00758850150800e00c035107200d070411403190 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 272113696 1250 272112446 272112493
    0x5010b0d1524020f010c1d090402011215090c0206041403040305030720030106030b0105040f0203061026040605060a080307030917030d06030807020109050a0b0a050901030f05090c1e03 81
    0x103204464540c13036910511400c44144141e800c0c0480e44001c2202411030050000000e0510100c90344012881c042c0c0005c2c150303e6003d20701c02011551241d28548039031001c0e10a8000c0d00350000208074600880c1001b075911141a503040c0c4400103002e08809c03210030000121002d03a54000302940c2805050ba4801c1484020141080d0034503255681c0150f00e902c09102d0080203500400400c0d16652522090100710740880320000c1100340100108607154640b4030300d020021480d46490484a1034400010540c0c01103034440d00d0300940d10000340b10078084036030800c80c050a411a41201120303580c210181e5a403241c03000050205800740810460502041c0040390041c04c40815245030002c0e10b1064000ca402540081303030018000704000003903580c170080d001c006d858150380302c0300c1042c10b01c1300313406060003a00e0110007003100c00640691140d10a03044041c81e55420340050240d8142100502c4c0c0381d088655802e8081c5080c845010711224811084200418003d40500000b01e410307082070464010301c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 272114946 1250 272113696 272113769
    0x607051b010c02270106020111071e0b04060c030b06070f0f080d060609140301020408030f0315090405010b011d0a03020111160f0303180501051804060905010b0d15 72
    0x2502c4250150b144d00c2c1c5401200741d40f03900d8650072100ca280400029500607008003086a2400481c1400e100d070316400c540d51030350480c40b142404181e40c904179901042076900200481a02411300080013025000044800001d441c1401180498020300c852400f07400d40113011641c078410760401207680c80300b1000f10340b401040f95602c0c003a400c81406080d500c2d5a448080003800b00001000300400c034808000009004400070b42c43c1910f403515156803400b82c500c0007001d141001011030001642214241e08405000d0810011071600307060050007400f0204065010070419408801180030304403400f00c186000429010782e15003160011115580d850544600e184038000b06451140944550f440040c4180100080390500b10310b80100340c458210b4084209205c440f074280401d83e000340a4960701c0040c11180c01d06924030400140c05080b01c0da002540140c0f4110010603a0701c0c07002d000700010312a400c0d06118400d258499034001c9401480fa0300c1514619982880b01459103070b100c01c03ca11003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 272116196 1250 272114946 272114957
    0xf010b0306120f030705010b0d0201020d051c0f0509060703090b2a18150c070b160c18060503060421050c070b03012c04230313090b0607051b01 63
    0x755031503007a01d8114014100f903880c0e80f000ca5181c5c2001002d0042012684003907411078000c590035030000c0e5a80a8810210f01444000300e40d04070010708038103c5c0c032286403207144203200c1215418440c03401444251030304680c50141c503000035000c9009008a00b14076502003d0307101180d582c444661700c94400c20508000000385040c0000000509401500e1081170100c000b1703050003410320400c80d003c00c18058040c07904406005c0545203c2001ca414011a804049801c0d5184403494800c3e0030110100c000500050110601049021503c01a81c8907403032042410170a851325a0704040e82e071402102e005007070300000c4018000c40020340500324019840c50030543d042030304414030f0604110140e08060400c0001000420010f40e400c3c48403840724000007041084140d1149a00c042894002d102400003002007160f0030a0b1f0721584124415146042c0589440307561015a80d181120b2a200e072002e90313401c0006208451814004031404980d101c40201641e20601c16910307100c90180c41c1c900e05010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 272117446 1250 272116196 272116219
    0x30a1104080309210a060915090b090105060301021305040b01030207080d020702010206060a0e15010504080106181409031b1f02030f1501120213080a290f010b0306 72
    0x100040944007a040d41406951281042800e020b501604074000ea42c01e0080c81c900c0842030341010030259002030f003004012840c0807644c00d0071582c032807109421b19596850801903800348105001824000c104000c020701640d1543c108050903070003079403440c03984111140001c00062900e43d00c618444034041c100581041d105456608041d0801c84114040c15000030b4510110340e81070052940c44442200c1900d20311741800f01905d900700703005180045231200c072004002a0380c00b500607036004080110082c40407a48a1030a5060282e00625090320705003010721002c00041d65030502da1103043c24030015030410b001148404900d5000041100706402141d111031505086800f003543b04031045080035969050032003640501d00b50003020015006a41c00244205a90025404e43c0154060001507250a01c0194001c9a0455a40b00300160f2040e50310780c00410130b104080200381280a250410b0340005004d00d001c10040c202c654822141e40340d4014080e140035500555040140a0722405003107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 272118696 1250 272117446 272117471
    0x108060f28090216060c050717070609080a090f170c01080c161109090f19080d150e010b0a0f0c030215040309050a090b0f04020c15190c030b0114030a 66
    0x3a48222102c551214021300002d00f4071505001c2d080d035401c0c15113000d40c6010041d032035a10780d030300c441650301c110004001001c500b4400360b03821420ba0f69070001c00c15a03486032032020103001c80b209845103074406500000b00090080e003801e01030384140d20040180200746d103248011180e041c8010000100c2100038018504d010014000c802c0324580b1540e55030210b40f039130800700020410300900c1c4103002d034020080e04211810100e0003640c2550b41a610b8204091685410b885070b0091405000d0f05604d040382c0003581129480441c422a504156210096600c4500442c5284543c0c180100841c2c001c3c000c9005203803080741d440a405004c0e105403a5001d41055030988580c0c000e4509034001011580248424a84030250100500100800708112030000300418482421003558902c50b550114551817801e4043c04515080741d408403d0600300d241c115040d960b00003100c00c5a030748040c980551084054000d100d500310180c070585560710003e0030644c1c19940c41c0d00041078505c0d030725151610807804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 272119946 1250 272118696 272118701
    0x90906010c0611090a05030a021003020a0504051206041a07080f0618070e0a0f0302090121020d03020105150109030807060c14072006030c16080415050304020108060f2809 75
    0x30542d2030240660344000740c50801181d2401031b08204d100350045860480140d440c4404101e075002c02d8140940c903800d80f0501940c0307500440e031180ea000b9429a081998000011035518030071841000c20194071070399600e0800c141c01003158250049000c00c4003080c01e103041d100000780d00c40c00c000c0c00189101100701c00300c1403102d0141c4055011441c04c101141302807400c00e1600c0080c080d0f410a00c400c1d5071664000400b481c1c01842400c00c10303500610b032000c04541d0305c04001c51940c0c000d0202c1045074103e00d4028000c1c2021102211040886569050658480e507140412a60804c4080781013107444d032074010003003141ca40780c1003e1050700116090300443c06005000c1c00340c001c000e80440084005807902d40c00b41c4581d01c0501c1420104108481c08142c03205075141125001042c12207000b030391030200d18038440d9810900021102c0d0312109125a40000194801d9201783d07070303051083c0c88140c1070010782e031003c0030340c2d9920149040201d004d019a502084601c0b03400503004000c200d0f41c80d0003100c03c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 272121196 1250 272119946 272119961
    0x31103010b0406170d1805060d060e011217030f07051c050903071502040b19050c03040b04090b040905100b0a030b0c0304050f070308040b1c24060c0206090906010c06 73
    0x3c078100d800e501003d4103205100040300d120300d60070210800c4040450b4103107a80c0b803034000e1034232415011a0402c4000001e40c8031310090040780403d1403603961224000c2d000e240810300c0440307040819100c501e01900d410420740e03010b500b2003603141602d0b407611602502c454001c83c41001040c0410300000c00d603403400f402124059150f0030003841d560507082c10501100b049400c0f0351240b00340104001c004113102c0904480c50503a0701410318103540300b5220300315081d02c0340311004034607880301040120384240204010002c441c0750301020072628800b4801d02061b181780820242058000200305810100103400000c0074140081420303c0140d143d80d60400685416105400c2c040c1002c010841001000c010180c0c0d907200b000010002289903541340316041c480c500543c0300c000404101001080c03040013101d100000744010034000e04010002519403424100440e100d482c9440000040d100e004034541440306d03030054566840c2c052090240480000c1c043c1034203042060070500c04003c030303030540328603030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 272122302 1106 272121196 272121209
    0x261b0918190203091c02060910020d09050f0d030b0307080703030c110306130219050603011e03020907030f1103010617070203250b0a05090304031103010b0406 70
    0x11003040c40c1c9000700442074004402e10102c440c0215001104098040c03010150a028002c120b03642c00d4180c401702c0302d9411035045140a420627400405080042c00d0010070703030200c10350b94103107000601c440d807040035042a0704030300c520b80d0306002c5c080b5450b000307e008200150030300320803544481262200906001041c1e4440e420080b2500340c071989114020140c0d10180b600c0900c641c0d0394403010308102e1207103101c3c00d11800c1c0f042c424000352040e200007904484c1113a08000c2c00b10562000203440100c2d40d5860301d8004010395640ca9501d10450413a40c0100308141440011000d13200c24a003404d010034418001486030740e078001c042a4007040015084a4280c9030020b00740d0844c86407140b0460583e0342441441e140c28102d000307032281d0511444810310550f465113402e004440040c0d80d94942500100800c0000c134510340d51004428000030000038400c404000082c0231261658440c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 271942446 272122302 := by
  have h0 := BRFrame.cov_init 271942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 271942446 ≤ n) (h2 : n < 272122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
