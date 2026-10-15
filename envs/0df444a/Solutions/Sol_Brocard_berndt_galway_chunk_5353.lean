-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5353
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:35:10.650973+00:00
-- url     : https://prove2.me/submissions/3c7e017b-c7ca-45e4-bfb0-d66ab5e473f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 962589928 ≤ n < 962769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 962591178 1250 962589928 962589941
    0x9090f091a1639120c05060c09061e0703080907060c14160609140105030112080a02071a09092a090607200108060a0b070809210105010f080111030a 65
    0x30650071210000e0b00c2ca41c05003450140b400543c0034035241964401c1008012048002d98010354249a0500d1a90b9181d25440d40001031819510410005115265039505c500303541041d00704160300c5420348400c0907050900d901000040d00420b5410340001c010003400180f2400350351680d07a03811030b079030b07880d6440341004000c0c29040c2c450f900965030074080280b041c0303110000819880d5505c0d502646031110105130000081011810080c0403c01408800e100c503810000299103c8855952444401012405c06400303401200e84031b03210307000d44030402d25218054000c500c011508580d407902c90031030946a01c00b0761036041441d8a007241c3e9281c80c0000b040d015203106c04e0003504251600001d5a9040458445091000d10315406100d070f280c03007540d01940a41d48807a064034800c0850b03003050003074182401820030080440500140c4040079803101d100d401040c09003203a03440713100c0840382e40c49030180000740550741d04500b003024002807442d8140140452203452225061641c0c45042101025011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 962592428 1250 962591178 962591207
    0x103201c03120608061017010c0c080d0902060409090b0f07020d08060a15030e01060506070507030b150402031303020c01030c050a180302060304140105090307020f01030c09090f091a16 81
    0x30307580300000b10108117104540c410454030030036829090800f03060150a084451b000c0b02c0c1070303240850409010350444034a200c400c1d08018580d0300d03a64a40081e101610380c4000007034001e280441e000401400540040211034030034000302c05207603515540682d264804440b00d40c01a400301118801850040304000e40114025100300e00d03090700c5e0f00c8021000c144044503400080e03951481c00080c440300307114003005800100c4025241440ca5142c2070307590259404040c0404003c44045042c840004a4200405502410954407403401c0e02010340380103145032080e009806150040e8045c0c1d813007481150b442c5550703501c8050400341168001c444110388400c44284503d0102e50210150b940c10b40650701c124410442e501021129550040c02d48001138000ea21070b80c014041e0b03d00503a43c40d10100407588081c1b90015480d0702c03840b02100c0080d505d42c452401945010b0380e003000f414441d0850310781240110002c01f01c00c0c10b03a00413649110421151006042c124403991b612661055110310000d50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 962593678 1250 962592428 962592431
    0x70f0c170d291c03171005040606111506090a0c0c020405040606060f020c031b0d0c171605030604020d02010c200f270a020c060103201c0312 62
    0x44a240e25000286840c0140c42011221001c03030810a240c01c155404205040c0d2111008060380c9136400707001c00c5100c82d010300301c1c40007120006020340000f040c068018038008000740162945d5503400b6001e48080c4144c8480c4e40220041c403a440301c100100309004001c00781070140e1580d510403c050081c100411120100822030b010307440940d44d5801094080ea00540000034441d00d4041e000d0004031030b041241d02990858000b01220f40d5020803600381d0b044c10320307041ca02c4031300501c00040e8003814020401002c9151450005c079a681c0b8104103000c4001032031007221030419600c5e018060070070f030702e205142c2d00d540000000750050521803180f0f84102d106062801c0b40c94160354030250324101501e240c0da014072441c0720341e800d980f410303901c0001c013048180d86618007040604002c0154803001e50740812001d6103030010a107a00e00c0c3ea8119603d07050b081c000d07034206584030f20b401c40c0c1d211032040782600100c0300810680d242c0e2602da07820001105801164801d0000d460703034156220140344910307000e610b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 962594928 1250 962593678 962593691
    0x10b03060f120a0f110f010206070210090201110a0320190f17030a020a1d060316121409010506030304060507060b0a0f0b030402041b022e020c0303070f0c170d 70
    0x1c24905624030f50350300c1211003043ca8800c8000380406d201000d050941103610100a000c100fa4005c10304804910580c20042600415070005891042c6440120f54040c400c0c0da14640a160f03200c2c00c05e0f181f0400610008000c24007542c40302d5a00d81e0080c2d2240711850b2600c0c03403080000c01c909141c401701031092a81c080c040e900642031a1498200311071038218039400013005001603074001e482000f102c240103041104070952501103001808018090041c002c48506108091406428a040c0b440c401050130f0100080741c900e408030727980c815207211443c0d41c20b00010a1140c81c1c00b0040d01c0584119603519800c2c107881c0e484000c05005542001a0010b001031404500000d402071041c002e03000b00f6030304550300c0c2014418041183c10300481170400c40c0c0c003465025081640410111070107084800107000a64449030350308800a03550b80d4070140b1b6480020079a191030000b001443c400e01403034130740c54400c200740602540c0c1c0010000008040d04c014401000761400c0c40310181501d00c00740440003641 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 962596178 1250 962594928 962594933
    0xc01110118030207030c050301110f0a020111220b070512160615030b0f01030203060105010f0e06030f01030b010b120105040905010e0604080d060504020c031b150708040308010b03060f120a 83
    0x110107035006900603000880240188030240140b43d0081100f43c1c004c109003006070303000c05624000c0170301d0740351030030000141203584c2413003500054282e65a914165903101540360000a41c5442480d0380c0200407285000000c2c501201c4082d6280d054000011f00580d81700e12001503800c2e40300b40020b9100c3c003091090040071410907c180f680a00385840e0008545046083c41400408001c09244260038140300610050b100441c10a046070401e0a0802c09150400015195007200b4501590441000b204105100c5202101c0340c0c1202c2c014561b6030a01d0340c948602c1c41c0c4d244501c0541c03891502000b4010800c50500b98001000705004000000d01c0b5010940c0003030924000340c400307641500002c1000714480000e031040f14014642201c04500d0011075003034660701c0e4001c902c070340c01e0b041100200d560101c01d0144060a040100e4003c501014580448080d044a10940301680041d40800000c11815406011603015210050102404209080802241e4000360420381744a003e1403190000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 962597428 1250 962596178 962596211
    0x2c0a0c0303031401090b1005030c2106100c0f0b04080d090c09050c1309090212030a1e0323360f0622020609090a09020f0906030c011101 60
    0x40c40c400d98010801003080300d420300c0040e406030031042001c0d1030540c980c40240d8581c203d0b0307403120b406800e01c00d03241c2c2e5581440c20914042d00700400ca5116080e0840e190341d110344019984940c0b1300310340050314500704420031550344403d028014003a4040301d21003004a036041e449030798000e10400da45454021410200c500750340061800b103800f1780c034405060080c40c50901072183c0c84410500060f0802c6805c400402c1c41a20300d1042890460b601e04440c0155214203e06c0302c12501d5080440340c1e074a003420b80003021162004d1100841c42c0c0c0803217865115510030301904460700201f8522140704050040c00d20308800d00a481e18544828403408445061428038172100381c0e40344102c01c42410151810342500b809004c0c3c0100c21950001c40400c02c2013099040c0a032107a01e54075800020020b030510100380c0b9840b81e9100154007821500c02c021130342c226a00003003083e510a4482c0d040c03864111051255000050310050742c1a08060000720455105104000b26074004c00b00120340c0403d080400304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 962598678 1250 962597428 962597453
    0x180307051003050a05180a110d08190201060f15030b010e10030b0a05190b0a1b12030b0d080a050f13030812090303070c0201030b01020309041a040f2c0a 67
    0x1003603c1d1410003145074010b1155a500c0f440d5003441261380c1d4994403c072500d80c4041c0c1c60007055500d80312011026502d44000c1c0310022980030318416074070804000580c00c1044c0e41c0c038901005600705400820740e40d00f07810140c0101c0ba20410214071202038100250701a08150492a0401c80c2c0b051884805581c2c5e102d901c5480c10207910001030404a00080c404841d0040c0c10407070080c000320700280714030a40d07a005031084442c1c2500a940750040d081c0212140d8020115229441717081c80c00400a10440a10314041106036071001c228800c0040d042c03049107220301c90702400d011400d100c5800a1405a0005d0226101400c0003628004003803215102c040140e0300207a82d4014045114281d40120031041e03908400e0302170046082d80340c4114010300d51164120024101600c1d03403111a2944d000f00180d13813000e10014800d0140c1300071665402c208840010681d48518100400308540c0c4150340310710006200ca05100c0c40078a0084195050b500048c03c01801c81031007a00002e0010500304160308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 962599928 1250 962598678 962598709
    0xf090e061309150606050c071e0902030f011401020109030e010f0908061303080705031302100c06180312020a0507110a030209040b09010506040b0f0919020403050c09010806070518030705 82
    0x11584160020300c03c412142c0a070001c000307008040013030b81508003001440c041260b0358003280c07c1c003269103400810000c5a89a12a125490001c8180b000b01c1d5808031095058071600c2241c25400181c1200483c240c42c0d0000c40038001c00e1205503280c1103540320304100d2907003240c2824240b01c1c8a40d0f40058615042003201c0014440d00d189004d4000c165210070850b801c11903900e01342d419400d207004000d441150002c0000d00c15001d10103001c1c5070754050084c80c422141c01940c1080181c0c01002d0420741e00f4050202200040c00c640d0f020401840340748260380c082d101035540d00e8201007150313486285102d40015816805900c005000006960b001c031700e640300742c0c0724980003c40c50500d410403909480d0080c1006d803041d8245071801e40103403141480306ca001c00c8215841440c50300d40b42c80c80c01d41c3d00030a08060203240e00008010083c0b2200140d030708145074045e6104003082c1e0384e92401e2510341d0401d9403410009801003004d02149004039019492942d001416509155900c0740010500706ca100c411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 962601178 1250 962599928 962599943
    0xc0203130906051804080a110c10020c0109091104180e03040b130504060303050306040903090e090c03151302010c05030c01020409050610020d2001110a02060906070f090e061309 78
    0x20700441c18101e0f002154103c1244c5414001c0c00c1c01d039a81503080c001d034449003042068039a03c6003480c1801304140544500c0c050540d250814800c0c4000f0348509203498098081401c4d110001031a0b10030344920841c19840300300c0d142c00c00341001c2c0300580f4042c666600c0348506403100c1540032201710620040008000b041e40199868001d0301400c0990395460b03200304d20581c40d0003c1080801d03002000c60394403041c1201c00203141180d80c6800d0b206441240c006801c000107540c00c008000000058010030b00e5001ca088400744c0450800e4510f802c2021101141804092000c0400550088400c001c40d98070a02c01d41c0c3c14421850481802c81c2c200c0c1c0e101001c11a2520b06021a41c24500c6c0c0d04038a0541d02c0c800f0b0507801200400143c1050210484d1350717103550805c0d058501c5e030002944030001a15400441c0d40d55840b07905002541c540b4259140340c40e13401828040385005004595031042c401c8142c40701c01c0300d41d00d8194025986e080c014900e035009107041c41c00030700e6140b11f4071603008118407131602c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 962602428 1250 962601178 962601191
    0x6120703080a05130f050105030f041a07091403030c0c0105090105040b0a030b040b031902010e040b04090f05010608060403020712080c0303090d03051b090f030a23010b0603190c02031309 82
    0x41c1381aa6101d0750081201c10b14100c4c0502c95642d014041301d43c02002003415903100e449918103126500080c1107441c442c10251024441c00307aa00c103091400b203e0301c204550b5405802c000030580c40303200d41c0542c3c10656110701803004441d4042c0c0c0c054000306005040903070900e903860754181d26079400485c0402c0041c2d500c0c0705800751880c181c03044004d0f8800070f4009208158601c001410701541c0d038070001e414001d0007284c8150556a68104c8c400c003030790240c824492283d403480e004020b284081c0d021134444d420844042b91102d0b00280c01d40c07195806a00900071986030000d12101f60300607038800c0c2d0703003c2c03410000e0070190002000290b0003280c40700c00034234100c0d20442c0000c0803198083d000312103250407400303541381ca140488152038942004540d0342158040480c00203251444500d0000e0140018000c0080000e12211351110b0002c6510001d0201604100c00c1200c0c1c1e02c070441d9a03807000c841190b43c0e1210890154400c04005003070f0300442e482c3c10a0507050220010883d40000360041e160b90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 962603678 1250 962602428 962602447
    0xb15010212040612151706180a0b0c0c03041508040c0f1406090a030b0c210c0304080a03110316020c0f01020721020411032d06120703080a05 62
    0x41040e0307402600c40c034441e007043e0900c80018100320b80004080180c0d52540840c016062110250100820440389a260001c14101051343c03100403c5504084181000e02c3c0105c01032004622841a180e0044000d401951000707031920103034116860003040d81c0300034017000ca1a6511140390700c0d54882907850344003281c9018070b01082e0031507880e0050300102d80e6940c0c2c100320b518881d2441e1101103e00312070b1a52202c0007040820240350423a440a00315044400500c501e15003150010480f8044c83c0c032030340016400d2282d08605c1803005841c10b404400b01080040e01045449000d00101c1000e85070214401e411070381d08801e240c000b80e401031011f1040e40d21f0030b0306c689d030104864a5488000d4840c11101d4a1b007000107034403000c580c81400c00d051034410070361820452400f47c0002e06a8014010883d001c003c880c0402d05030030440b401071001000c00c0315164080c5075490038224078032003040d02d928903070b45640c02c0c044c020680250703040340e0303105800e0084002560b8201130102c0e1905961600c2d15500e850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 962604928 1250 962603678 962603683
    0x1206080d03060801180c06110a050607030209100207050f041a0909030d1535010609090b01141f17040605090c010516120903050d0206060306010609080a1203090b150102 74
    0x781c2c072292101700b050113594005100c0e034032040200c5031141407a001c1c0d103020046141c2400003031180241140103040c2048105500341d400b40001036010b644800880c000408280ea45141500620340d0200380384950000030f00e0325400030100c151044284094044951020401e031410039220601c1c03a80010600180c141a030b44140b400000320f0001d81008685800d1400002003030ba180d19816400800044050030600c21644600001c060002004500c0d82e03002100001c0103a80341c01c0392410b210f0400080ca031940b00064070220700c0c0007041682c0440520400c0041003540444620a00103112182001c2c0d911b00200c65100f14090900483e8510f8612515410f010054004a06004090141d03110184501e15001115076000f0704140e0310050380c10003902c08202c281d08c01051403265450031405542d0110341d031030052205038200c60103070741c84000943d10b0481c1801006400d03404070100b000031460b00d0025101e02e980700d00380000c01241503207039041c3c000c104480c005401c401d120040c01d00c03540e04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 962606178 1250 962604928 962604941
    0x4020c1b19051207051c0203070b09060d09020114040f180e060a0b0d080409021e09130225121d130c110f0c0906100e011206080d03060801 61
    0x12100c4120450800e24952841c035214016076000d4041103181d241038610070060b610150500600e40c0c5025102007071400e40c1e05c00b6201d0101e001c2e0240040009004030140b00b0740e01e40010003000c150411448405d80c0c0001c0405090a0341004110810340082d80c450701c000b0806400c0800b0b1440b140c0382840c0c00c1c11200d0149000213040e407440c0640c400003584010410326017100704030380b0118030f051180c400039000140c084030280003484005000a001e5995900030002d0441542e5002410401008229614010020000d030410322800c2c02c01d2001e52581d00078503940884440c104c6030741c614100b00104400c9074150032074024200d40110715049800601010107454070101103501c1510160200d6620320001181024103a02c03944003000e00740c01901d00c0301508800d40b041f20720440800c0e84803541d4180350340e00c06004124203000b00d10b15007403404c1da03c0c030288403940307425403980060b500440f0f80094007400901c5451303603502c0c04542c6410502c08044560800c1d80c01060207800c0c13118a900311000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 962607428 1250 962606178 962606233
    0xb0d1b0507140a0501060605091003060e0a0f0f0c050903250e07020102070f031d06070f080309030d090b01050108130b160201020c060a140106050a08011a070204020c 73
    0x15400452140d401400c55a040740c2c40300d4590360002009045034508400079900030215401c2a00110741242e2040190614440840d03400b44550400310040c1c048410354003400d0080d40c840d20005d11480070640005611040743d8030000707440c0c1070100d80d20045a1140c0c1c0c0010014100203214141e41c0f4041008000702010a07000c0c0e8900a200115128a00054803070360105000030302c00203030b895000703506481c0415000300e90300022225614000303201941e07008610004e03003c204c0c3d1803105410038030103460181e6072007074440c05109003075202c0e0350407a04000e15084580c4020420000c40302213074000d01c0e86407072294140c400c65506080015209d01d800030400509100300e8003003280411070f034071001c80d00031103148070600c0040306004040340a0721a03a08107800a1144401788810341000da88052040c01413032041c6409641c80c0c1904072000c0c03090b8800c2d01e00041041005102044500b07040303410503e0380030040d51400308680c0c08034040c0e07080042840c0142d001610440c100900b5202c1c410302208 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 962608678 1250 962607428 962607461
    0x20d261603200405010f0516030917010621051609020408010f05041101030f0b060f04050a060f020d0e0619020303090c04060f060302090609120f010f0c0c030f180b0d 73
    0x3540c4042e203082a008034031400d070401a02054082c80c0304e020b5812541d02c074000b1480d45040d4425414094035140c1627108140130f02100400170f0054200600c61311050b03400c031088541c2c5e1706400348404a140e41c2d84545c1a9241e019115200d00c1c20007002c9520300003070480b42809a1110314145e00c03603084440261250070014140802c0200180e407240b01a6130040e000d0800044031805114032100500e00303200d24540020340055a034100314002805401180c4046504807083c2d80c40c1c883c2120f08941d03454111015030301941c45096001e0084203984041070000d0f0109040035400c5002000d606000c83c541701c0560800028004980f9007403000c08403055060750180003003460518440c03400ea07424441c3d02c0406134007182c21b000d80d42d1204100c5a06e0b80e0300800d035400c2881306035001901d030001440740b441039600c1c10040640a159502840003a0b20481c0c0702d000f0544450746040d80c0040e500c10b441c004210750301464194030024582140041d1000c2c00200c2c0e00c0310f18010307000c4115a48000c40b06c0360b00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 962609928 1250 962608678 962608721
    0x30207080607300c020109020a09060e0112032708010e070602031806040807060e0a090b0906040504020409051b032505060c0717010228020d261603 65
    0x115003040c00000e52040c20000f225402110070360403400a0161000307940c996013440c0c079406041e80c0c1500b1280d20980229040c0300388960f02d40d0b58a0407100a8070540740d0212842d0010404800b82c80302c54000c49010f420020042d002030902001704400008051440010a49050114030001d00c01e084140007070000902c000c1e41011030180da640101c401c03581d08040680524080c0c3c0d00d44c4e20986005142c913034200d802694642e00040c0208030745c0c05590f801780c1d40c6a2800580b0301210302807805051005428000161a4141444003401004105913009515039091100190041110548d2003410340104140a40750004044c00c02c0030b1641140080500b10007079406510a51543d20304899045625a903510540580141068125031081102568082007058811410b400400300000d00c2e01102405400070b000c0070000c1c20036210464010790113100464401402440c0c82c01d1520744040a0a40e0120003560054400b10200c0c0d00314550414400400c58664060050b048101054035075900c16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 962611178 1250 962609928 962609941
    0x31b060e130f0b030f06071b1a100b21070e01050d0510080a030906020c04020c10090809040c170c1204080313080f0703200307030302130b0a08040302070806 69
    0x94000c420302400c0d40e942e8842903118100c00540c80a022180081d080d21a10303411004841c0e1229000c5a02401184a03024068681a003001009070314a80c4030500d0103171011199000003250702c00070000c88001c142c000d03004c0342d990b0307a400140002482c070081200714a07a500f17600e002d14400240c10041841501c44c403003102d1307a0b04801a5801d400241d40c0000d030507a10000e03c2c0d240208164401c15480c0220030311841450340c0180360300e0507141d40741c0072540020711000510049101307407224803245030000c8841221420182c1c2010241902801d8910f00b0800b03030358002812100401c41c00e002081c554036030081840b11010400d030b804051400201e00b804007058440c0041480208024114040000012282e0b0800350501d04031780d810481680c1c80d106040040d9005602501c811b9000c0381c24031428244840c50903c0300105070350301d42c0c00396040510503681070300a90403002c80d01002100140002ca00700c82845d020b450484225030303942c0340d54141401e000c0d0500c80c042d00302250713075040390081089 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 962612428 1250 962611178 962611189
    0x7110a06090f050f13020c240412030b0a09020a0e09010b070f020121051806090715050c0a0212010606080903040f27050c04080f0c091609090501031b060e 68
    0x31500305480302040c00d51904000b0310005d2010074600c840c0c62002c80c849140740340000d00a005010b0b0020252864004089140d030700420840d001048032a8412680e0000c61203030300101000b01004d07000400c0103403a000d000c0240e030800f40b1301c4000034a0100e95811507103058001503005003a440c50313180c500031203512140740d510710406000c2d040c803c0d03242d208014003164580c1818104402c0e03104000300d0070004031a000a0112485a405174814103000c501e4201c0080380c0401150f550481d00d000c807010a040544142c1c1044820213031501621401e003000d07890304014a56482c003c070000040300da0609070050b200010141c1720035010fa2041c001400b4030141040d0544c190b0740e1402c02c60201d004442c0d084ca0b204851f1040c0700b050f06041109204030101d0100103403094035008801d13140104494803800f5661500003d0042d4410360300c1012400f204c84c810320308540070b444e51504119036a154000c1d0f0068071342c02ea10807550940400b602c2500d82c802c0c0b10000c0060400da2a04211641c40440002c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 962613678 1250 962612428 962612459
    0x60902121f180f02010f14031018150630050f0108190305030402040e010e011b02030a080f0907150c1a04080306120c030a0b0f1602070306020304060204050607110a0609 74
    0x341031206c28120004058000c40c40c0d4251140e40604942e03403894001c0010403404a41d01c04c40c8e8410554851a401e0707280d1900540d0f44d00300c41d95041c511581d1800b6001c0b214030030604454644100204124440622840151a9048841c03080403945041c081c05400141d04142e02c110007903002000314172a90814012809034039505817501e00d07103d44941c000540240116074103c0802e61925800340301030030040d00a10320425103400d028501d050702d48416612880356260050004503400001030b504211076110a40000c00801240d10f00c0352156035840d01f22404461141c0490150b0380110b0030062003408845c16518801c002d22418102079952414500000d1f101c01e00c25603e00141841072074082156004448008045030b0a2885600b0922541c19094a0b141c045003107000008000c01545003100e40b0700d4032250b002300b82283c6503841b1103009410142044840980070800001e513a0380d0b541c0584007907400340300a11301c0801e80c041040a1011aa0f02000501c489032108005401d6801c18a4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 962614928 1250 962613678 962613683
    0x711240405030c09190209060409020403030c020a090e03090402072102060f1620010f0f09060b0402040e012106050115031d061602010608190209071b060902121f180f 73
    0x587c4030b8000754005221070059410810006d4070115000040c180d2004104400d82d0094465038886a03c035407161003070303036003105010149a104000d4180035050a9004180c0d00380150012600d00340007040c0844404011842c44005034020014004242c8003840080d400104130442006c000d003e9490180c42d800c2180039a480d04101e4520130425520290401d07140b422030034400304101a03403c40e80100400142c2001d81e1401d02d8001920040e04251080b203094901c080a21603860703180c10046c4000120205211002d014030444031000511a400b440e40a0101c140f0039913114902035500501701c0d900302a0185c862000000101d9000801044a45c1c0050b84044c0fa05c0d10f016000300c1c16409030070580d03c0318200b071040402c04240300d035083c21b000120300d108072080c4820341c03a005c07402c50b15501111000150703200108903a9000403240e512228000e03201800d9085002c41c1389001e00d0800703030240e403041c80c0c881e00c4801102c02c04025202d9010842c00c00328070501e03010a41d481c0c0308424120328000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 962616178 1250 962614928 962614931
    0x1c0f020108220309060e030a260d0509060f091903051e1303050f0304030506010902091f03090b070c0c03060906150803131a0711240405030c0919 64
    0x4100740d41d003501c4524054a9051202c124000c0d1a4075004244000500c50580015440fa001e44154507022403000600340d005813403290038810340303118440c0381243d0381c0482100c1101000320360051100b501510788a0440400607045624024116103500000200105a99044140c030140241128142024042d40620380b085c1c642c0302017214003c8000e071800c4003400000001c10243c021001340180d06054034440c0301a512a05035000c40d99550f80075901006102d90003c900610000d0096409001d407000001c10506070081e80d0b4100f00c46a0f208440070400003a12010b06000f84020042100d8000d01c99240106182c2a45d03181d25110401600004001076280e4820030309101d02900810b08840c0601c1c05a03174107998620070700c1d030340f5031000c00f021241c0b0400001c0043d40e903020700700c101a80d2081d4410703203240894684d00c95200c40ca81c0b6084551142e008071000c0140325080d007800200554480d501961141000e007050b10740340340e4884d0503200b1491b500420500c510705042000000007075050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 962617428 1250 962616178 962616181
    0x19050d0e090708040821041b03031209110405010608100807050102150603010e010e1e120d1e02030a360f03020a0206120f46050a0501051c0f020108 65
    0x2c0c550102d116030948508602d1407504c1711b400c8103030800201c601884c8200d0f0503800212060549170403a500c075100c003401003000c6120814508020350065020103101c0e45030300800e1a034000015007220b02c203030000b100182810040041c0c240c01000c500010f40320010041101078503040000b0356402100b88030310715003094680420041c0c0c400350000000564104002d20048604010103940c0f03590b8035102e0300c0c60366410b4000c01e04200d40456035221180b01c0c0b90044d032501c4241c00f003001c0680700c584400d00c66489441948203d02102e88043c60249a4445010501e03001b000310700d01307128a41d0040001c4510007050b4941590101070390303aa40032907100281b214080140e040c00d034204400403e020b5080200081d400120a450b100114070841070b5402c616802e403582815508990200302c40318261580805d0301c00c1c0000074211045c0340e01380710044c240340d6440e00301c01e41a0554205817000084030391541c0050055207009076000c224146c011000031001d0101c0c5e00ca000340075120f031502130305103e004070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 962618678 1250 962617428 962617433
    0x11030109200d230103021f050c011103060f040b09040b0619092903060612280204061d040602031503010e060702010c050c0304090f0e19050d0e09070804 67
    0x281a6505214800301da80307036515401d40c42c01400448140c014602c890203010341400c207043d8040340c140d94000d04040e600320600241d082c4a01c0d21040c184052290510004a450701d0034040d484001900302c1c0070704c0c0c0b20b0a0003002e1182c054028050544918102686000c481d00c403243c3c05903005800c804000443e80702c038004120094003030035204001140e644004210341480e60800c65414101036807080e0320320118514a0315503111140d41a138560010310200c2c01628042c3c8500c0c1070480c0c06015101c582d860004092400c4000c116004c542045000c09441907103414402c000c0103000000040f015845100c404034544180103100800450b0f01101164a2a11605002607a00d001500810031040180b03d4540e6901c02154494010b42c2410a000f0b0076030310802c02d80c1e80f03031410000210b040a0514600a014154403c00aa2150ba0351885640e506004000019444000c91030b1a80e0340c0200b03041c80c0f81400c7c900c1d1403440030b019510342038031010b44691302c0055100a0360300e0201015225803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 962619928 1250 962618678 962618711
    0x120c0d0303060308072904032c040e070314061006050c010b0d1b2c04110607080310080d090501030b03100f0c1e05040302280308040905070311030109 66
    0x1038001901503000131075000c00304601004419601c4014220740140818980c00040e280e080443e0004c001910000640127034160803040050380c0044a8103d500350340303c007004102110b03400340c2090040d601c480700401c00d100c507403c0c10806034034083c00901a1813a01c6882442605598032a840400ca0000f031440d418060030752000c1c0e4007280040403070102e001e203802c1c400f01c0c10303002e402c07000c4800c1042d080001c0c461406200401d48440100c4645012002d1340010a8000c0802002910508540000c011140d503d450040203070504c102c11041d01c030300305041246228480ba400031080c60b40705050300344d034954100c029002281c03c00d00e004111040d11001180c240000c002084190505160000c0c16042d80e0340c000b0b8031895090f07075a90600b10b01e0042c0c0c00c0540526201c031700e030209104200038000350030080020b02c2c0032107070b410740c0c0302c20007541c4801c070240c1c092580e009031058800400c1c00d0210b41d030b5602415400403d58034043c00048585171400080740f00622846940382e40c1c1e61610074003100c12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 962621178 1250 962619928 962619941
    0x290306010e010e040c240f030b011b0606030804032102070302011209050f0706021b033c0a0b04030314040c0e0601030608010e0a020907112107020904030c030e120c0d0303 75
    0x14030868443c41425004104003c804a4040401252a084250922078868800c02c80c400005030b482845441cbc00c442c6560309682464010b489483d11910040040b800d5000100021845943d41d06030500c040c9404d00c2c40c49010000020442d0401030341000580c0e40082c4641c0000c809110000c1c04581c0d92030098a04210140341c00010b0145041c001025600840c0000401d07c0b00350001022038001002c240d00c0c0c5090040002421000000c000350401000140201e1882514101d803528452009158508003a4210441d03603048040104000c1540c54082d029803c42c8111029885040517a10004042082d000701007130381007070100041c510b038401d4010400400403c0c0003041421a448443d9807100041c0c88242c0c068800640030910307643c0718081c00662507005070b01400c03940d10000c280074032851040300e40505c1c3c1941400070708050b03070b6503e107407900407031094940038a00c00180c980581101c0303940e40c05a00c6200e042d00700388603010000c03660300c050707010446520b0140e00c410310301034005001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 962622428 1250 962621178 962621189
    0xa08040b061309030c0203101119050c030f09190302061b1e03030f01061e050930060705090f24070b1506070312021c290306010e010e040c 61
    0x34081d00f8014141c2001501d920a4000c1d0191410100c0b100446400d442402104211440c001c012100b1704090f10407035816400318a01d802440c00c9540c0700520700d0340e0480004203501c40b40010f4200010310b0002d001c50a507585c809040350344d00d4519000101d0380d00403802c0b50141049000d0310103030640424400c8010320351818400b8941b03608802070782c5541b5001100d2181502184200209040d40640c00501058441e02484400c8400c03069084800d0340040303012030b4210100c0091f010f403038084000b8425041c4242c104101110300000d00a43c5003100260a00b02480010410104591165040c1003800c40064403144402c05030412685001c02c1c401d1160300802601040c80000c0200080c0354a004a0b1140c2c01180100c8080080040310722030920300070045841c0748024010a031181e006400e001c00320442c0390320090344407000300c41a50200000314034042c91071103080e69564003038450001041429001051590b051290f030040880040c0200c1d5030340042140060304200022010a02410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 962623678 1250 962622428 962622431
    0x2060c1b0f100905060a0b0307060c08090310020a030b0f1f09050303030906060316051806010c050f010b01020721020402090d0602160c0501180b0f09031506150a08040b0613 76
    0x648803201c0d8000d10f812081125980140c0001c00d5960f00240a912020038009018003e0249403c40a481465102000302c40b0260240801c8465560034081c0004d036283c0f8243c0540d540300740c410003c2c100c03454510420f1040d001c1c0c07c00070b040760321040c0600c0041402030021130000303401020251001c1306aa03001c0741e0706100004c100300f185100400c400e8000c1c0d5083d0216000c21a500d0744000000e44c850043d50707000a22240d030701011400210082e5008101170401d5404001d441c1c45441c1092002d2006044903912225001569641000718400501c4141c1c3c0707401e50003480207a10b1001126001003c0c0c401c58000c11170a10550301c0602c02c0c0796456100b84d0455603400e10300201007201e0311030202078800049500300040c007035000f0803c4c0b0070903260940040e0b0718503041901421150b000485611404a411301c001c820301d4400300600c060500301442040c0452600c0700412816007083d000f2035840d071000748482c003517664200981740d822070b0380200b90340e10965650700480c51303c1107609002e15a85 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 962624928 1250 962623678 962623693
    0x160818090a0209040e0307080a0f03180b0412020106030314030a151401090909050c01180506130801230f0c0d0f020309010c0306080a020f0a030b0c0d0b0102060c1b0f 73
    0x1250b94020b01d0301d5203098800344001d200e84900142c80703000d010f5000e4001c00c000c21079400707170901c04d10f1006004600c030b05000a9a030f02030002004400b1810100704c500c01e40c900240800e100b140d0b03960180b0b5030030510003031085c1411503400038200b40c03061b80705030b001001c0440440d49800c1a6003110b8140541050000070080c2d5031050220602ca02c0e821550100d1036039040485d0014060044a00702c503040b000030460603d400004440300070300d603032854102a011420116069950100030a440105251114800f9090411050031121942c0e500c00600c4144003030146540b91442a070b5500c01c10b003102c0c20161f44d440c0b880880c810702c10840c4003c20301d8039004504604500e242c3c041c60213688028000c01074004180c41c1076007121050302a200807503101044100041c0b511522580d0228006840400c503c2d07901d41e654010904141e60064ac3c002c0c0100c0d81d031003810624810520201c1c82440109007600300301021101c46d2107080c50001043c0700c00c60f076010150380708002c0090b2030078808003210f550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 962626178 1250 962624928 962624941
    0x320010c090e0c03070c020f0301060e0705040602061302091b0409020a210b03030d020c150a0b150403030e060307030207050f0d1404050a06080403020a0c0308120a0216081809 77
    0x14529000e010b9103941104080f4100781000000d07644194101d40328420701b00c00580030011500703508403010b58950b4985201040030311a12561500441c002d40b501500e40c0c1c1031000290500c840244843e404002d0201c40801503950880c805400207002d0740c440e560003502c80380c818114801d42d0040450180000342c0ba0080c15031007200c00c4808981d24041d5020050b4801101058552114903541d15900502516800713007100e500602e000399408003214510904000d50410074441150600c03130807551035405241070b09280c141c2818801c07000c00c140d0301e007900b9607801030301a440ea107080c14080d88011001604c1076019078111218150007030f003190201d50818040a03628141c107102c80001031140c182202017201c0110035202550340040250070b101d418148221403c00005006608500c580d400c10700c042560203403c04055802414819668030202c011801500406414004200d01c1005104000b00000c5e103070040140e840b120f9556140000103104110507a01c4d0905039001b14000180000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 962627428 1250 962626178 962626187
    0x311070b0403060501082a01030b190501030b0139050604060501062a06090615142106042a0b091503040b07080604090c06050310051207030320010c 65
    0x4991143d50140020b03a02c5544043d124101e6094010100740078220010752a114440402c2c4400410f14001810020303010010340585041c20415a00103c0ea0005004559050207010350300f01c02800c24803442d0711183d4242d00540c102240040c6074114450201044807944240300f1006604802125041d05142c05c002000b041d00384101008a400a0744a5840328809811031108842c42c00f001c084c0700c0d80b0b90311204d000d800070303010845100d65240c8442c000c0b107400c0311840025080140710054800d840d4420f000202c10607039010403040c8008400d950350b100000460550107988414281c804209148642003110105400d200d44040c0c0c014003c5600c01d41d40300074115840d02240c0c845c080c0030b80c0c0c41c0441c00b54030066501401e2208800300180fa0035005040c10354100da0060000100d1040340e0301c42e01021082500901b00050001017030225642460700503001510080314070181400010f0310055550403588002814040545401200f02c110004042e520324035002c000d00c01001c0d0010f0051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 962628678 1250 962627428 962627437
    0xd0f02030a081c0e0705060421080c1f02040b1b0a05030307020a02010909051b0a05070b150f120d0e06040515030405101802210a060618090506040803040311070b 71
    0x5074604d28003107034603d0710a400520641140c80260200e46480d0405000c0c0c10349407140c03135500c0c2c41076229080500005050fa002040c204442e035000d84500c01c82c00c00703000744a50001444451060040c80140807640088044448076454020b500000e12049120b0500703000c030358000a400b07400003004004a0540205d5420a0300303100340e03140c1124a40700d0116008136102543c40030006000e41d000541a019042c004100c581c81c941001030600d078481d031354001c0c0e00e03101326002e8101c035000402d11300050a001081030240c1c9030490314801142035504103142e507000030740e0f420000c01c2051f4261440e551902e404030703405003501400001840c1100c01940724683d02c103480c2101c0038828081520400c046911445898017500049490200710b2034082200074020301241160704907207040d5621170403208009041300c10b803080340041040e41c60100c00c6020415115a04280141400000c400081c804105070740e2059104003000e88940301c909044824120b6079070180d045100301d28000c281d00b00080c0142 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 962629928 1250 962628678 962628727
    0xa032010060e101e03060b1206010801020406261b0d05040503070308070513141807030515030d12020f04030203100b0f041b0311160c1502010b0d0f02030a08 69
    0xf01e000c00c0c0d8075489180c41a00d940300228003200304c05002d100007042c9401040f08458000d21042c004030780300950358201482030f48019841da41c0043c0404c081074000d510b4503101032090400450301081283ca58020010040000b4800303500140782d580c200212600b41c440080921004000d00e240c14544241d80740c0c4103407402d4000c10788030000110030302d114500f141c2e8903005040403040701900e403800c0314548800685003a03910811958800500417003082819109401a5070045045d040240d401601502c1c2e61014500075004407500b80f40858121b0b5003081e040b11284001640c07880044084036080c0a140c20003503050040116a290612181c0c0080220000440b00b09440306030490400089a034400010414005d1a8140f040701900070780c000d403d40d000707000340e00746014036006c07900040c14120700007195122900c060a00a040b003448590711081d40ca40001c0020100400c0024104500e0b40320090492111540078002c40d20b00780701503850b95a010401e6603c0d000d9035681786d803440080d801e10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 962631178 1250 962629928 962629951
    0x10915030e100501050d030507240c140a1709010608070602060103060b0906010801050f030f01061e080102030105030a0213060e0106050d0c020703021c0f0b0702030301080f0a032010060e 82
    0x2415982c07140d110307090407500300a1075155409817603601902c4a4000a900f0340d800c03c5084200c103000424034a0100f941ea20300b040004a07100300c40d4002e0440102d22860b0000e2140a200150401ea0411869902803519000e408000d41d18603405138054186074021500c10b028203c0000340242e00042d5107030580e0302c203200505c46c1105100500240c1ea0044800d940001c3d0884010496800c0c01c1051081000000c1e05440f100c942150341d150940fa4140d0281c05601c00c13039010060902c03001607161002c7c00d00000254695450203000a517190000e841c0a032141d5000b1121008102c5c039940710400604039041182d00c2907944900180c619000741002d440ca943c00c0c8200d02c01024404500c240c2580ea000b01071030491080e100b070320842048014000c442004507111000045010343d080c00d846440e25074021030341c03581026505410304089684c01049a400603410000103500240c26a100c10f111029401c0c01404403c0c07402d10307001480065030107092611307802240300d0300c414070100d110f0480b6040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 962632428 1250 962631178 962631193
    0x60d0e030c300f0304150b03070e070f020105010302030c15041e1409041a09071a1801080c0d0203190911041107020603060607170d0c1806021b010915030e 68
    0x820082c24482c040300c1520300b2000b080018005101d141c26003280001081001601741c8101700801d1418950350440c1859100810800c940e5135072007803500519102501c024029549035a0200f59103013030750a0403510803041503010b0a002849807080c0c600519400c18200d007024600044d5089800c02801038010045155070000300c1d0741055280607004a43c000c240d02c1607803500504200b4101005448030541c2d0240701c3c400122100d41100c1c121100d8040c03240250f66626000c09080d0b0401c4243c1040e052280c02c404000c805003180701500c5802e8882c60016030783c0ea6494464010303148909003118141c84c0f410308240f0a04c03245480070445032030203a5080000440d140045000d9001ea080000d500410800c0050458104603000e4020302e0f04c2109001c407581e0164a85810036008003500e80175840c0e6030440d00c04010760120300e081c1c100e85540100c1c9029420148001c0d241d20f100e800e0000500ca007140d50a0b5164072400494000300103110340410700309400c080042c081c0581c005100076a205a40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 962633678 1250 962632428 962632513
    0x4020114191719050603031b03030f0108070f0608040c0306050408090405070212070f110a170d030614011b080a02010c120506030a20040504080301091406060d0e030c 73
    0x82c0501d000703149040040740303010185948100a081c00401560300b41c0010301c51000c1c447c000503260700064105101075500c4e80f4108000ca8141d00050f8485030007640140810041d0980359490003083c1d5080d0315042c0b1045d61281050304240b5020343c0000c280d217180c0000c1009002d0036201030025550101c401707100703680300c01b90103c0c0c7e506d000b40070706000c0b11001c00a480000300b08e00c0c0e00c100094412481e0314090407a0000043c005d04071540140440c0c5d86606108149400a1001c00c0010740c090900300281c43c140218001011924070000741800214900802d0350b00000d820252055844114960b036140303e82c41c002d02800440040a000c0398500004805600071801042c0c400c01d009801012a6605900c4bc8011803d100d5541101003941054592030b81e281c902503039201350700a41407603980c4d52400403401d0032116603a01c80182c2d02c0028080c000541d0312a0100c4080d554030210100304140401d0016003988542400807665214000d0840e80e10402184e0980e01101d2507101860040c2c000e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 962634928 1250 962633678 962633717
    0x19050a1e0c032613030c050102030718090e0714042901030c08011d071e0e011101090b0f10080102030a0b0f0a080706050d0b0616290406050402011419 66
    0x30301c2e0700c980890383d41d80020180d42078052608810340c0286440140354495407111400c907031080d6003507000101c08041c600c01c42c550300b5154400420840d01c0820140d448014103e480b22040d005146450281030b204445a0b5500d0700180035401d000383c512012440100c40361a442242030705c0c00d50219017410520403c0381c0c0220f40c01d6040340c545040c40d03c4d2030103e0003003050b80910b005044909202400300709030303401c10070540e0076000c0503d03507150740882d0b096502c00074081d2541e22400c14450385c103101070480003079042c02035103421018003040341d00c40d40c80e07080c4030160448040d0010062503102000f042203c685070f402408285000391083c82c4a209200184403010000c0d00030705030340e83e00c1514100b2401d48290010400e02088460002d4401030700d000140c4070341c0c000240d0500c1880c03000d22500c14020100c0c442013031203803290440c1e650403110b800307908030b040340050002c0c001c26501e100080542e4010580100c0074104690741c0b90350b9215003101591007401006a010000300c034419141d0385050039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 962636178 1250 962634928 962634977
    0x90c0d230a111c02040e010608060a0b0322052a1009050d1509020907110c03071503020f09120304030b150d14070911041a19050a1e0c03 60
    0x511041601d00403001d1410340f5521030000c81100c800d0350812001a03041c1c503103000e583c060901a170b2030b11107905201c001c00c00b01328099013044815080c20014000e1102c40c2c807900340400c90000001c520485001d0920394149030405952107001882e800140254092507509003186172401c840c08031b1240c400b00001c90754010700e0b00950340c000c00d40e95605408035074004513152050080003408109200f207540072951105066070143c2c0031550b81c040c1504001750031f100e0007034808415801410302e01d18103650300280e0034841e4010740506a0001e400c00203880841d040741e401c01c00103072540c4030410f040d200050742d81d80706100035a0030040200110b070101070300c48041c0036400b80041440950a4454032003803040c0801d03417000511413048040014101900740034030000041454515038486244c200c61107000200c000c8081007401c002c004403640c4403698518039085d01410320b403c0341c179501d6038002078480d0300c9840051102c80d0750201580608950002600c00e00da403080e61041e0b40d616a414511007032182 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 962637428 1250 962636178 962636201
    0x1415040305070e0a0e01090308040506090a080d0c2d080702031602060309030c0d0e10020a02030703171308030d0b04091124070b04020109170c090c0d230a 68
    0x2202e941007000040c00c07a2003d030000c00d00b0900189114400d1001c81c01c64035001011800f02d4221010042405420b0151a500580b240040d201e016102e0340c460290b40f080b201d03480c3d40e0710740d515801c04c40207200d0741d6030500031004100c04140050404104902e02b075901c54921300006c02d01c800044107a4070210a0f5000c480c3c4602e000380a48210b542040015000108514650320003800b031000781c00d02c00c0158106004a54a60a4408181c08248080d017a00a0784020644d84112044001a14000f500c1022250004108581d44145082c4508603210303054134180395001c1020041000000800100304800284000b0000d8032001000e010640b0304060000d4401d0711541043c0d1401d06007082242c2e503691508021019040a600c41011150480b02d0150b03000c408500410085507002010040949414050505803c8003501d4081d5154a1110514001c6d140200461201c41079001a998403100010341480342c0b41200d0403005c01c51103003440380901c1c00042c00100d086004544a580310b040d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 962638678 1250 962637428 962637433
    0xc080f0304121103030a120f09030806040b030703241d0d031104050402040311281a090a0305210a09061b050d050301031a01210510061415040305 64
    0x41c9050072040c2d181540e008251101403035166020482e41d014070003441e1608036500e07003982101da032114110480b032201500134501ca01d80440440400c0d0001c00446d408017040342c001ca4180660b03008203003070451aa20040000c00035203124503404600035066200350007018804c0100100e03540055805a402444103242a0002080c0400440c1720350451105c0743c1820466615042c1c0d194080303405c9034071550003511904155030106a80346000030601a040040d07441c1c0030200c000402521640e6a11803280c0a4101004079490304c500040606550a2920003094404419640d0405607102c03101d06418981c1c00812510b80c001040b152000d07140700f48250f554116100741000350503500400518102c034041d90181c0c840100055080084030080509903032065203035407640c0b40004882e000c1c45500380382100e4039030050080018550915076488010102040518500d0501078200000070041460445c20410f01081030007440d10b40c00184002174400e488905807145200d022401f603400010800c1c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 962639928 1250 962638678 962638687
    0x9040e24041523100803160b010e060a1e0306051005030d020d081f0302060705031e03041505040602070f11010f030e071e08030307022409060a1104030c030507030c080f03 75
    0x7404242d8202d94010184d0a06405081e00d6900f598a56000801d0321140c0c2d40340ca44821040202c6094a0350050500c9900f40300182410b20000d00604940d000e0304201118140710220126a0010070701c0080d50400402c0000b42443ca128519241d000d0040d01c2c000d100d1f10000c41c001c1480010800c0030303074410303030b58082003601c8911070780320302060700e40f52060b40c510440340110169503120000c02006224500669480700380c414444440124605034900e000400d00400001c0340c5450000d401e480041140018290798504d4a60024056135801415851070103002d0820000c0c19a18004e11882c2600d8542200d82c503007000301e040d185c224024681c1d68011402c104682621958881d80040d0a04204041142c0318050103141d0741003103482d1801030f0b002c0c0c84040020306013004c0e40c01c4140406007410340075141214000b0342d61100034041d4108181e5494822025420101c240d030065540300080301d103500d940c3c0c1000342d03960300d03d80804d07500c3c2c2c81526000999081c2c0042e0341c83c80c03011038a01540c10b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 962641178 1250 962639928 962639981
    0x21130806060f0f030f060f090d020f070303030b13020c010f0b1504170307020d150c0302070519140703030201090b0603210c2107060614010509040e240415 68
    0x10f00d6420304800e805225640207050f079540b05110740ca00c00d6a0b00381a4101c42c0c0381802c3c880b03180c402e001036814103541241031001103c020109161042c4c9415040105504c6a144046034056a0380d102140405201181e804012101904084041000000b0522403220348a08100c50064130910000c185401044108010300d5070300b1629001c2c1401500340ea0800e00e00790042044003440e208100d880d040619511890f94803a0b1054103840345040c50118105842070b5113403039075a08a035440754401003200320b8000401c030464402100860951095a40e142d69138580a4040d116110003117610750040e80018a107400c0000c0e00b160304044041c85204049040310368651254446c0583c07643c1409601c1090881c2070041c07c489d90882d2080120030341c0c451041c18100c045404a0304600e5420814051070360242c0c0e8890241e4203040d0f02120300103412104843c1e15803510050a05511a05245040c01002d18038441901d030311031402000070fa020001d154003858115001610300034201c070b400c9a40b411301c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 962642428 1250 962641178 962641189
    0x306051e1c0b0f18070b0301030303021305030f0703050c1503190f0507091d0c090f06040504050106021e010606020a061113080c12030c03030a0b0321130806060f 71
    0xa0400c00003403100780c80e84075625a00d4441c081150b820b07490758a8031041c0a92940800e0716100c07004504000381810700d0411001005512040c40060b08154000c10603850144007020b505c00244401000c0303500d629502441c1a0700c03a520761105481c0e40c06030103800307955418200e0b039024410808901d95443c607503440625140c88680301a440611956825201501c00c00ea80300d110301500054561401c4140f40c072101104058005550502c0c00090b0404d100b5051030040980341e0158045031f1894090360110003050300f50280760301042d805401d04000140d03d60300451100018001d086000080008001c262030030f881c000d100d01c6005030720a20523580825060750140100c4501031510501d00740b449803030420030075900c2d00102c0c0d103500985e04580c1c452406100083d40002c01002940c202034142c10541c0c0c507404000c0c4040d510382d807154142245507a0a0103001183c03c82a1901120403980545080c4103400c5000c0361425100e1402c0041042074000642c54450940104800740c010803480034802e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 962643678 1250 962642428 962642449
    0x60801060b040812032e0e1806040212030903030f030108160e06010c1a0a06050102011514061e1c0c113406020c031005060306010e0411120d0306051e 66
    0x2894504410146d0b1040d21101c002c0244842d04a00784584444c2800d01c0c422200c1e401031b11102001d001d6500491041c00c01042c01c90340260111011420402c0081103e8110700c150705220340c4c540000a81160303000c400324080c605881407501180c40c00302e000d02900660701c400d405500202c81046000403d40d4bc4180b805a0096108003a00d0014006035500200740c0d62013961043d01440e00e440e018886940c1c240b02c0e041c3d84801305521900c1844c0b130070400040240314401024080c0313400061101c28038050f10400c808640742e4800090f5102c1070010030300c2e0325070080010542d2840c20041505801803060b40800d0510507010003520304c1c446c8402c40c0403486841c8040c1034500d4003e0300d8407480b0216109170039000400880d0041d149008104003054200400e08550707440b00c0d49048180440c6d500c0c006000350544103401d4214005859906007201107c056007011503210003500d9078103051141c041a2803210817406d4800707120700d540340c404100508016118800d07501c1d108092000041c13400030303c0803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 962644928 1250 962643678 962643691
    0x32306011701110a031a010513090902060c0708160501020a0b060105070501090c0b1e070f0206072607020102060a1b05090a051008040b0717040b06030c090109060801060b04081203 79
    0xd0f502180e06814100d90010413201011964032842c550f004003c400385e000c0c1d036900074038120b0320b058141102483e2440982c010b008210340da6000c610119123074072044850400c0c80b58200c81080b552080703100c0c0d903813501c0c11003d403000b088480009595400055504246540324500001964031a0011111500310f0b4809641a6484031030703d102081c0741105500c050001c50702103a650720681d041403041500001714154034803d04100110124002c10915080c5550403503030720303503070750440c0c10029801d0000e0392013070b400926080780f108010b5011a00821109200303800b079488554031000040c04447c22641c47e8500200303441d452100030b92103080200584071000b494400c1550312100410807030050308204502180815003030000f40010811400d41c007020b14904800881c03600b06401e000303410007510007028105103802103032595509004003102940c000d0208422907a580001801600c3d1a20441c4400d5180c064040745100342d05080b2410b8848840040441d0081103113202c000d0360005155 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 962646178 1250 962644928 962644931
    0x13060318020d0803010819082a01110904050a0b1e01050c071e0b040f090506040e0307051f0b0f1e030a12030f052203020304051801032306011701 64
    0x110030050340c07802d080b10b11042c0100e880585075810518100d14002d9440c0301e520036085c54030a08000a00c420044650121070171750707441d1500804020030705605038444401002c03942017412618604600380080d01900000306c9042c006900c03910a002c080b54100135085410003442c00c0c451052242c45040c0500218041c58031a1030070302c50520003424050b150f008200301d441c07071114840d9420002d0035400c1c003500c802060f46250501d8928008180241485080030464a80340090140d030b0792680259030030318a000a0300d60316511480c159865412a0200689400e8404103110b5214000c0c07003041d40c8014050302c084018044c060801c03444c0a0a1400620400711034900c0b00c501e902e050080780040c6105005039800c810b411100075003501c1104464070001340c500000c02c20350030000401c42050502070440c40f80ca548007030030100d06501c5240c002540145007900c220906400c40307001141281d0080042d24059040e0036154103410707030050a065181e40c0404014014425059108907801e0100d000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 962647428 1250 962646178 962646221
    0xa26120916080105011a1218100e0d171003080c19050718051005121507050903150417031530010501061d0105042102031002130603 58
    0x2641c07800112500411110303511180104030310242c019801540d80c103a407803c5d43c200149080200340501000b08040110300388010002010003080c07180c155581c04c4031000740401702c4a2120700e07036945002502d007400030b5190304483c44070100740ca8140d40288104040c0e40c001c6807658664a030240c1007021400760034001c045041d40746001141c010390b01c8510a43c0605200d624102e0752110a6441c29403400c030040c2090200b00b0071440d28490035003541d2080700c081c920461030800d0503107480b800d5010300c1c008041081c14058102c2e017250103800c08843c100d0407540c40300640305500b450950165801040f1009490a820402421101640c0d1000c50310250350448409600000c3e020361013502501520484c0315000390407041501803200701040302c1c500910455240c00d4005101c1103025040f2101503504010300b1105a00c942d044034020018610742b901c03180c569054200c61043c3d5170004134801e01c50100f0010140300c2c680240c420300640d106408914501d082820b84c0034108201134490303000510706 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 962648678 1250 962647428 962647453
    0x12060e030315011d01080601080403170f10061e03200a05030a1b0c060c02010f0203152818090204090302010e010606091a090607050f0a261209 63
    0x20107144289a42003112011000b010005441c01c40703180072103446044041c006503a0350b6000544c0c10b40002084c44c00440359600c6080c01c1724902e880462003140c5520350b03401c0c04070302106001120f0041d8000380301e50485968850f0142c8051711803200090740c03440a405580030203806603200c2c6001114420070031454084081041c8490703401840d100c40071074008804e02003100001e10891490401c4070700c00040112455002600d442401c0700010029900c409450410620030b40161a144200c0034055499040030300c80f400304041c000f07618501840c501d01a0141c54103010384500b04400d1031850039840d450401008103100a89860020f443d00d450b01070b100c0050b201d511132006040d019a000040503010b541c3e18a083d100303580c0c00142008051481030140007400e100c16882c418180501594032203500e03010407100d0103004805402401511002e01c8240070208103600540e10a14941700e00d5546618020828428031290312681c40c42441401c18042c208449181c00c84408011190301c1002503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 962649928 1250 962648678 962648683
    0x409052d070b0d06050d110405180d02151b18041401030f02190b0901030b0a030209090a03110a03090905060103110d0606080a23151009062003030112060e 68
    0x142d00c241c80e0b401d40003d50b003501d003020f4401d640c0035000407901008900c03015140d00c1e0319403014000040c07065070746030f000c1160000d000002c0550701c0d07091800d50b074103014001000303034540000d0b034982d12541c11404c00098820500002c0b90a0000200c0740039410941c41075a0070040c44500309800c0c1c0c00c541e48401114880724124450317802076210740c0140306011880c1c41848003150b010444a580010403000502011840205035a4886420710f400200039400c0350000b15850900d1380b000c1d4002d00e800c401d11055401c003240040c0101d01907110081907665241c03800d6070b03c02c60580007400244950400b404080c0080c0c002c940c02420501d00401e64007560035034001d0b03d500c10300f00000110350700e40d81000b80c990050911175000d000002e0400c116a05990590401c001c0c8600c4001d00507081c100048002a460300b0018200c08050111018895960070250044007503001d501d0108503411089540c00d1440c00e05110202c41c52405581964a450001c2c2c41050b0182821200c503a15882500d8115804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 962651178 1250 962649928 962649943
    0x90a0c0905070f02010c0f1b0f0b0609011202150a020f06090d1101150b0906070f05070f14010f0e01091a090103110f040b1c020304060c0207050409052d 67
    0x84840081d05051486024004000c0000c0706401d69043c051150642504440d03250080700c81c90030026040354025214502900401000401d41d0358420740b02d030140800d03e40024864030003a6040c01042c0d032541f401c1046018851002540500c0391040e0604512803d4050b00280700c20740115500d403030080c10b240d4280f107405c585010082e8030070b8a2481c4080e0b84410403185080112000304118000322100d07041c800c820b03001d040e060403000109104107031500000c4810300d60700702c0100d2040c144c4d1442c0041d01d80e855842250300d258032010020810290340990190354110503150343c9039a00c2e074076400765101d2003500002d6040c400c203010009004404214042d900742d01c1441010780c0c1d568080700242c1200c800100328440040184510070a125094003160f09840711f040f461510b44200d242c00b1002c4452a20b20141158000b00500c020444c140c3c1105203601ca039038003034640c40c9444a0070700c03046450b00c45000d045503200482d03103030418008040d8070031542410501e411499140050300c9107070000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 962652428 1250 962651178 962651189
    0x12080403050a1b0f12120e1008090106051203030a2007080316080403091413060306140105010e01022109060c0d02060c0f04030201030c120f06060e180f090a0c 70
    0x2640d801e103c01d500d40d550040b101411810181e10986410a00c9820310092200001016051013640e45c6070140d0248503003601c2940020044841e091000300000c060000640700741c0e45540c24440d0114652a01514036044411018002c5040d0369422040d4409070003081015088041071008284002c403104000303100c01c6000b070027015940d0814070101034000c1070200c0071900b0000e502c0103001c00a9072108444040b50401503505080e40c8103200092121150303000030b20036051030308a0020030840d154100c0401c036101c608c070f900f480780e0341c801c010b50714841048041030058028811074045048002c030f000c920314241014032414035400c000490042c0c1c0c8041d1001140d5801004003c814075810003074140d11003100316a15080144281c50345d0800c1c0140e01000f4145910745d11404502841054040c100c00075403e02440301a26060900c001414030f4041c01000031040d64405440d4108804201101c021048008000b5554200e050310011806060480c25000f0100c8000225102079640c1d409440b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 962653678 1250 962652428 962652443
    0x9050703091a0402010c120302090d061d010b1507030504090e0309101715042405010e150405151b151e0f07050d021204030806120712080403050a 64
    0x3806810404460540c40d042c0310028000c00c410800140d911440d12019240e00900c000d40298044005030041e014850f042508070318105002c409021190700510306030029000c0702c215100d08041c1382401d0b211000d030441e40000340d00c1811041d00480b00010115030740603141c15411b10352103211000c151188010340c100c2036807001c01c0d90510340c0b904c000c00ca08161810b042c944c0c00040c0040c0054078000c00148602d00b0708800c02c0f0145010786407a007000301000203982c1100224032a505e4490a000c9140c06020b0000d07940101410081c105901042011944200701d141010710344800c020040c05440342c1e0f501c2064050000f0741e00f40f0b1f49000402420008200500750350856242c000c1140e0ba002041c40301d52005401881c03a25200d404066a08004200794440c103e903159071040d91244070700116101c10510014001c0c0c400344240120a0140344a961001401d4450700301304003803e005030940600542200340304102040d41113180600d280e20030128103060555a85500e0304003510390500352000f8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 962654928 1250 962653678 962653691
    0x2b0203030d14010617060105071a04050f1603020a050f040902060403060e1207150507112e0b0a2102090c0d050a050702070b0705010f050106050a1e210609050703 71
    0xc48a0b000501510726031402c060315061101c1c1c1010011405403c142c103016002525a0034094401d044c00a030740c0c0d08e16107044860420345401584c90404000c580348a01446d100c080c0c940c601031282108582d0000e028102c040e00340002c00070030990340e500c210352056441c044c800040c2c8440d80944000e5006040c0003501c240c0c96440a4101120100301581d003200070040000010518104603010a04503000061241c1e9224000e4508041e00760440c440c522031710200301c070b0101c7e0f03141c40300101e0030f0390103004a00c3c0703041d0038140790035074a11203885a0f01c082c940100b0700c80d40c0c0503260814000c41d90380e0752180244a190300441c141003400e403004444404001483d030110b481c5406060b8004060032010010352902c25002911180300f4042c031900d03913400050743c10a100d02500842e174207900c190800c10140d65250340c0039055034450075030391022902e89402110a849411030140280f0155111051070041000740c56809103025156448556941c0001003103003185071081344e2182c0e11030380300058030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 962656178 1250 962654928 962654951
    0x4030303060905010b070602090a090e0a0c0506040614031b13081509100b01020124060212030408040501140c0709051f050f0906011b03050d0608010b2b0203030d 71
    0x152a500e0300098000b03070a0500400681c2d40c290100c80740c0603041000142c68102e26000903107640304661201c80078604100010b03013000004100030440038415074a4204081c1c0d03d00031f01549000b103200c1d510101e404070030792120514545009580c003030340c42821100460300328150100c040e000b48080a0381c0410b002000e200788101085451807580103228002c04600d00f0140c066604d40610310300b13403d890303119024070500c1d034000d400035082050750800c2070305824080c4002042440b0580301c1c4000511901903100e00124a00d000c80b40101d403c00002458035080000640d000e51402c4100340a640040100005900c010f00200c006006c0080c000704050402d1440c0d20001140d01c8441d0410486500c2c0800c1300382c0d146100041c0c012410345c0c0781002a50344e04e005a45141619030200100e51144032282c04041e8460010100174440b40810024140c031380310764900321211107041903085000310454001d91080100308442c0150440c01d20070300d400302a80800e042d50000000001100d03140c0040440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 962657428 1250 962656178 962656181
    0x105010f06031a0112140c030601080610082412010b01140913110403020a080706080c0304030f0c0204020d02131502060f01060311070c060c1b290405030d0504030303 73
    0xc003a186000d21001d61402c2da8080c002030000c10b19414017110083e4004c3c0c0351003507081400b0681020801341513900e04109403000740d1384102c40b12400100041c00040151600c003c00340a0b0301c013a50b07280079181e81ca06030703800014041c5c003d03064642c9855030001141c84c2d03107000d0030b55202100c0c1c0c400070648000c507030005410070700006a0381800c10411300007440142c440c0f00c08000d131b490b400b00c0c0200707401a40811948842c4100d801c082e402500d034590200d00c5e40000508541110f58076035444505075502e403070014040c042a100240060100550100000c2c41103d4805156000410041ca40f03985503000300c080740c0c00450000b0748203082d110200080840c00c00185072450690000e05054039190b8040440e0140500452007407655801c1e0240c141c00100c026031348000c0d07101030034070310407a00c070306010b00450a8108100e0b010f000f41d000d107188a000c0a100a401c03074500e900b01c083d001364406001281d01400305808201386800f40000030711550b007000f010071003c9954031281d40d6541542001030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 962658678 1250 962657428 962657459
    0x29190521070c060506040f09080c0d0513050402091f09030b0901090c1715131b08122d030702062206091a0109050105040c09080c01050307020a14010501 67
    0x16900010040128598102c290004080d90000c8001915600d400020300200008500703e0320840c034281d07a10b030400c80c41f04000d003510f0310054219400c800c00d0441c01c4903280310b8000c0e182c00300201c8003010011800c01d50054210804020100c086410207940481d4400c130444511100040701880104280601101245e030003900c00710080c070400c0b00d1611515640030032840744981140c40310894104c2124144542e0f210940c200d941c2c50051700740fa80700c85284209509042e1440c806601801c00e00032011128002151040801b51403181c01d15034241429410114507504540144c0100100e9042c0028049603504c0c910034005480b8200800024602107006045003002c0030811527000c01c0041e4a074480c2c0d85243d2202d000f00740014640350a82e01030300c071040e03c0b20039083c00314000f051440703a50300030074140c4a0540b0304118026a80100b10b600701c0c3c50f032141905603040010054807951060b402568441c800740119000d010031540d40b8603d03158042003103102c41c2d55a1005201550000c01c1e0780 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 962659928 1250 962658678 962658727
    0x918070906020613020d082b0513051f020c01020309070e06030610030b06040603080a0c171204110402040b190e010f051c06120303090501060f291905 66
    0x403c01031034210400b80c104410600080c1c802c04031000d035901000b085104450f003204550000f510b0354400da688504062100131688480e00341803400082203161000e903034011070741e0010001e207035a0072411101981242c2d80d200542e002c503000c000b0540280401d000950107411004020701040d40382a003000710b141d0001c0d040c07502c650800018007072900e05541611091b42d03005142c5100c1ca886510006004020552000b00140d50100711038001c40e4100c41d594580b00e020320710b410701c12010f54030100000d00c185407055030418603407000324012441d074055281d00759502400051405031650050350603504000c0c404440c6400d10031a5212160388000c42c21040d080030308022400d95104130001d040390180001210b90f15007244460108d40d101508030f10010080d0303a0595281c0030150500402408030a6000e89896080840026081d038070101e55800301c0d01c06610700720ba0a115020034502020948200b103895210900c500d140c1c5000304503000c0c0c0c180c500d90712110b650795200e04c0c5103d880403420111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 962661178 1250 962659928 962659933
    0x10c0c05120f030c031f1e152f010615090503031219270204150b0301060c0602220e0f04080f2a010c080a0603020f120102091807090602 60
    0x40d560000701c01d000c1e207403c6100c00d0202070302ca035126154420303004440041c040b02c1b01c4808130300003110104042c00ca91540340c45c085081c00306407500c80f0f00185c140480d00500000d0712050b090700003c85020300140c041c5200160141800e80089070440c21341c0d035035403c403029200092100da894541c00482e09030003408298065402d03d1004040407500700c2d4000c00f2518000741c000f4100d400c01100b68824030750002402d0804039034105c18034480d00100d18211049001d24a4902001d0a41268030b1004c01202e41d0250443d1442e03090210454030b8103042c103c2110b14940078082d803442c0c945102c1080d201c00350203d1807507812900c1c24a013444000b5000d0052000d03141341800344401305035805c1c1140c1c04001c60030091380e9141c150110b41c18441e00d4018001401d1f07403c8503003841d40c0a5040d00700e000c00c01141d680d4112940c48003880e101c212a42403000070341c007100c210354811745814020001701000085400050900d44103a0104848002f40099210321845150400002e16003152920000e44900e100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 962662428 1250 962661178 962661187
    0x6030616020a080313022d0307030210051b010608030901030b09130201140c060a0506180f011211061605071d0406050a020c030d0203040b070f0f0f030e010c0c0512 72
    0x10b03444110a0b10050801040000002e0301c4800402108000301c3e40a80b80d900804002c04d520803038251054080d9401a40031b50350201149070024113501030700e4008113000389800005406a038039611060550706141803488211181201c2840f85400410a030405142e6881c0c04e0f200040031640d00d0784400744079010000c00e1003500e01c2205040391130350385e0a0a0502c0c070001c06c0c0c2e13407100103030081e18038401061013501c040185040e0160060780c040c2a081e241c0c2807100201110015800b1341c1110b42200e03092410f4010040f2168086803541d20600540c03908030020560b01c0440e034103900820340040710003410a905030410000b045a1001040304850403a81c01d480c6d00c030b0340402994050720290006888002160031300c04642d04407900a4845412241d41d00481543d00c0081c0d0070440f0141d81c8a25640d0004824074003511801458040a5403076603001c1d050754400b56065145900c84100301503860b6400900c854091182001016242c2c43e0440307055510302e00039280c12130070309601666100600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 962663678 1250 962662428 962662471
    0x80c0906010f2102040906061223040f020621040c0605030114010c020631051f080703060b0d20070c05010c030c0b040b070806040522050c04090506060306 68
    0x1c09486070700402c03003c0c2d08038100084001c00184c0919041544181c0c40c142002420359001118407840f031104440600200e000144590503981ca02c02d0b01e5403c0080120015000035400d10300102014030040c81e44d07080c082d1106105200c049102e40100ba01d0050100f40010300c56800708101c000c003d5440c02e1031440d810040c6441c2000303d8001038a05201d540e40b02c220465a481c030a60f8030003c0c3e1000c2d1960124400000d90307003d106031000303c1042980c070000228a0b8100558107403c45003c80383d030001c0c00c501c070a004403500c0038020121000c2584c0c0b40404240885040c0040c510454080800708240e0341500c0c4a1812000e94101c018001108000d00c00008921905080c11076000342400b14028449040c16101c1030b900310002000540380d10708110401035121901405000319a40d80d524030b1755003200740f0003251000c0e45c1e29040c810f0070304895400003aa003d00d031015144605d01740c0c0c24900725040030505640c888a02140d141d0425000c00003141010814aa400b5400e80c50080c10241d248 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 962664928 1250 962663678 962663687
    0x60b0d0209280513090b0907180207020307270c03050601031505090c130807030602071406042d0b1602330703060b1b060106261f080c0906010f 63
    0x70310400307000d1070204c003078242e003010385a0240045640140004080e45043d00849466440c0790007071540d1700554156040d040c0d10039100b9034401d2a03020300200020ba00b008211b80404c205009030600040811101b284104214029041c644807903803400701c1e26042150000d070644d4100c2f65958411a40d500003004660380310382002e03401030071252a181e0b41c1c0fa83c1d4000d00d4000ca002c6e0708039210328411958004208001680141090350040380115101c01145450035200c0300203035009800c141e2080d00c0280900904800b44844100e840d11000e4050701590f21441404021260b510000242c2c4c400c12030103a405204040c10a0084030030040c0343c100030740344224006880c1d0100c0540c100c03000700080c9001c0c001e030f003c800503110661807030f921401c40e0710b8800e5100d0030881d074410250050600001d0110300503440200300d4070421030141141c3d010f0100c80940002c000341600e0043d0012480d012204030750810807409400b074600030b4080f038074070081485450b0001520140c104003028a00c4140b11b60311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 962666178 1250 962664928 962665009
    0x1707080d0b03031603050702090f07080403120f110403060e0a03120218120303071101020a0509010311070f2f0a090e1e0f120a050307080a060b0d0209 66
    0x903404001004480d8501003403440c0038002180050814110b100c4040c15000f10103404000d100311070301a041e030b4814030030007500c1070700341c03004004a6415808180020b005514550100c4c0e41c1070000900d29230703400e07600000e0700c0606400002c0d0150001e014000d011040c05045002c031035200041c11030030f1840e40c00070803425500502c501d2081c1e01150752400d001c19240c5251400f00c000f0301e00451a0413000c91075441354801e0740d41c40c4c0880c02032110385100c0e02040c001e42c1c54443e15034172040d06007061800158041e20900b800501b61140410100b00040e1050b48c69508080c02400350344042401800c6c0849514600d40c0c0c131503664940c2003501041560b071884da070b40c191003110341c000c6410300f0b644843e1403501c002064410092285061207035140c0d000050325124039240082220072081040c020511301c2d10a403154900003800410004016500400038281c0082c965040010b0140d62a8003441e80c6170480c0842145468002030740c404685000041c406c5603d08854401d01e105000c24412000403d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 962667428 1250 962666178 962666197
    0x906010503100905160314010602121c0c050a0207090b130e190302030316090f090209120109030207050a050402270607140f0601120314031b16170708 66
    0x400108002450b21900c0b00420989034180034505000c800c0d0a86502ea220004000925100100648119000c3c206040303410301d0f009007508628074200c20f409680580010000056180101c6448500700c2c0304007902c01565580c3e140c1c0310401d0400090a0901d241e0005120900705180c00425070389a0314a46030b4030303011420000e00380c80b1150600b07007480444100c010b10100d046245109164001c00154407400541004582400f542c003030a40c0c0902d80c601411607286000d01040c481c50f10b140d80100006c2c00000c049610720b0185015182c25907941e1902240107030043c02c0e081001d4245501550040c02003214254200001d801f022003840502e4524a944801e61035851441c4d91252403c0b1800150010740a4040c8032880c214259034018a0b4450451803041400000c1c101d07004020b100c9000368145d80ea0700032119148078049194202404024071650000034020014103504000c2400314804007180390084092b041000e0000451405051641c20421008000888240841e6032162 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 962668678 1250 962667428 962667437
    0xc120507060f1e3f180f0309030c0f0305061326130b031e06061204240e010507300603050f0303011a1801080901090c0f06021902090601 60
    0x1188120484810501e1481e0305124820713103210b80302803a40c5400d40024080c1e2886401d58000c44d00c440d1000310b0345c050064550142800e655000002c0440260641040c002c3c076009500d80d44030388a545060300180c1c4402c0c55543d154404104100040c08815444140b488625600000c41d84406500e5940b00300c0001544102558aa0000c08940159801410b10703032100c081c01910340c0e052410681c02940c14105103204025172503814035410204501c96400600a0f50819240e03211030844070341d02800c01c8600702d0101804c50040301c004803003450350310700880c0003042003032803010081e08541001d8606010443c40c0c000070100d40a4150700c0801c1c000d403201d408401c0c0410700443c000200000d401c010418050908039a40d02d480000156060350596041c0060303010140721000118070030092910420802c181180540d5070090b10280d520412410003c100e004203030352003002c4040c7c0e40e000071540740c937548028001d060341080201c2d1041042e0450503000f64884d00083c2803010000e00c410b0410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 962669928 1250 962668678 962668727
    0xa09020c0f0106060507060b032b23070b090a02030d1b050a081e1207050d1b030e15040b0604180b04031d0415170304030c120507060f 59
    0xc1008100e01a034640d401c4008000d61074840c0001842603200e1482641e803c0c1c1000e00b460400c0c034020808112010003200349810081c0c400da24a00e140301c140c1c41c07038000e000350300c0d01012910540980c1503041c0070980d402e841c0d0307038101407070b11090420340641015100d6100042c1480140c0700020700c0111403609040103084540021022282c000d02c810004100d8018440200208000040503010302c841001203921a413101075940309031401603000141c0c594004c000440c90090181b002040d11300210100400c0d000f070000340320b444412982000030002035645049046515041c032000c0c40c0355034090100d4043d0305003034a9003030140780301401803440740b0359039102d0502e0741ca044124000030307650081041c13060b0714283c03c000d8404219809002c540c1070401403000c040e40f078a44600208000441000c1e296030b4188620a40c0350104a511124103110070030012010503030f02031030840181110203c0310940456450064200041e590150080c0b00091401e40c00440d00072508030281d40340410f40340580c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 962671178 1250 962669928 962669947
    0x1051c15080f06060909011d06101a0d2012150d031211040e01081c0c02030604060504140a0b01090b030601150c020625020f0909100513140610140a0902 67
    0x500490754500e031420f405100340a042200441c109100702d400441d1900d405540301c2f164000d600d0f8003007840307090709410414424000f04d664000d160307000031003101300306a0000182401066100000546d000d0750003d042060103030003d0388a80c00c24005865040a000d80c070741e0003074052458650ba900880f43c48217072030412000180b080da4000d02d03a900c0210406c0d40e40700100d948401080038880c00d1400c440d110088214010000d0090540d405001000c0c0707540d468540000411001d03108a500d1050040c02c090243c2c4100540b8080500801c070740b040304e5250071429802c98202d030117180c0c001c0e089400100030707800d071102c24100c5220b90744c1008022810548002075580c0f0844665035103240d803c8030030194032101860480480c5100b69284030b039400040c0e0030041861007c46038102654024811004000c0c465004980c0001c1c4410741c410114040e55184e0340c4103411445418441d510040410034201691550040141422040d80341650f1a880204600f0700c03d070f000e8100706a8002440710301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 962672428 1250 962671178 962671181
    0xb0706020f07030c0605011a0a0f0c1b140405010b030403120f05100503060619060e150301030308060910080c010509010e040e0d17091b01051c15080f0606090901 71
    0x41d000307540d09010b5465003a0b143c040c0c0080c0d10141e0a80303059107020004100d404c4540c03001c21078513814249580c00d06009031401c80307084e81480000410020f40380c0b9000000f51114800070328050004074668040d50401b101600e00501c1c0d4042a8031817410240101711110015040f44d0700b06030546054010f0300d44441803c40645003c5143c68203041c5000300308000c4600b00516882174400482c00c0e1490742d10f07000e0402c1030151114040c40a0300301040e8082040324040c610684034404050080060003049840206140d00240d20507404100c07004104256440d020240990020706240302c410300504001c10150303a40c81e0440755505110001036404d103030b60b000d88840300c201c00009000f480780c1800b40d1020b50301c812034184981e01080204040d03404c440ba81d640780c1407065030100000c14984000b40c04c0080713036504940b01181030100801c070701d10907500f1f400c49203144491a00c80c041540074010213022001546030348040b1540d00002d44440640700301080c5c82da00b100d0204c0702e881140e12903030481c50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 962673678 1250 962672428 962672437
    0x1b0d03030b18090d030c0201020c0606010e0109180c02010c020d1205220f0203011107020d020904030c210e0a031a0421020109020324010e04030216060203120a02090a0b070602 77
    0x5030b8142c030010000d5080707000414803032140c201e6800380b044800c9070320164280c5c0144226180190030010005285512902c600321a001052410703411142e41c8203202c29000003510b903000030158560b0384410007150240190f80407103009100030914001c1040c80144210340d1a0042004c40d520754004c10010081d00001042070045d940e141d0003000c0d0140b0f0701408104000500324025401c10f5807008401c0030303080590700660707000b82420044410650030002c16500041c81101404580c4012034040359845460b0040d404882c40601707100904040042c20356200005200c0c450800d490f0180005004070200c00354103201510360016603281c2d4039040c1c1504010f4000240c3c0444c40f41c800c00782c0c890f07054001c1d5214500030340544140040c50344640000d03221154110058102220040250007001024907511600030b00c1a42d044004400b2003040728200ca03840400103a0010400c02c2848140805994101e0305d2064114078184402010503c400d02034801d1100584012410b0028032100d60102c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 962674928 1250 962673678 962673709
    0x120630070819120e040c030c0e012307140a030f12020f18040605060d140105190b0c0102040302100804140f1011040b07080304140604110f1f030204081b0d03030b 71
    0x9201852480000130001c0c050383ca20700b00000e560741270b0f81c902c950040c2e00c0c800d410035a000150354003d40d1500700c0340a940c41007100325a038503085c610080b0f41250a10801d04041e1080d558580c0701044a0002000c21010b01454841c5038410000120141001011200c410420000c7c0c062007450400000d4000c10b0654046078121000140b50074041680e40d100c0010310451901c0e01c91927989030010322031141861900548528411141845440710440282480404240016180984960205a041c0580d0b11442c010070040340500c0304002c21b41c0e660a1020b00c11400800e000b50500788000e40d504482c0382d0308161103644400d4032052030449021903014048190311555039000c1481c0c5100d031030f1300844054400599000000c03154000108449000340d40250301c0381080038461081100002c0c0c404070301135102944101d1804400c02e400c51400d8004950f40300140c0b03803807503e0203180c108956012400140d100c58000403440380e484040380c014954052800040707a80c20b4001180f02c5000070f4002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 962676178 1250 962674928 962674931
    0xf030f0403210e16052b060606050a1e020703120216140f01080c1c0b030a051510030b04080705010b120f0d05040308120630070819120e04 61
    0x10390010710b1581010800303600705002c8510090803000c0410051542e4051070b58450fa0550502d070301803a48480c4d101c07401c0d50480c1d01e4200300e901e680d240030071116030341d014001103100401c1d600c0c181c68004c401d84040000b40f1112074031413440b104c0000e44070b000d140001090541d803407411034800780c4204100e0020101d0885801c45407030319100e03240500c0840d80441442003452070120b4159500ca0854540100c81c1c00700098100b00e00d40000c00c84603d0300500813042c46549440780c03009075400700000404503005802800d551040241c4003000c6140051541c0309100c2c0350700c01040082c0d0f620541992060300540c41c81d464403e240b4026000d80f0008102c5035001038082d480006684000c10900540011602210940e080d0b04170290b50f01e00a1344809401c4070820b00c003014102c143c9001103a400400240178404507070083e070350340902c440d4140310701ca080503d800c00380360601c10800003440940000401070a41d00c442911100580c80d10040060080240100d84007000c1e0081d9411440920000c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 962677428 1250 962676178 962676227
    0x904060f0204080a0b0618070c050102120411010905030c0a060503040c05030105010b0a020601090b0a0306020d060b031f0b0702091305010e1543050918071101020f030f0403 76
    0x900710342d03c004c4424207440310454640071074002c4c50700d0710310788085864081d01440e990b42e139030605642c00003100005a42954080054000f0620a2242184214841e209400310b8400d404001001d08110390842802036000301c20124159981108180447d0901d180c0540e5030740d034511302454081131a40c40380f6015802c1c100081500c0101c4070242c00c4c034010039402c0b6205680d0b9100c503641544c011180082d0815088101400450920340003025044c08201c40421065512120040395520440714405100070351810b014031196801002c0c0d00130400108820b00744811070700011500b802c0501501d9500c0c2da00406101000029040503000350200b034203483d60078480b14403649001c0c504450440300030a8801e0020f0b15120941c010b000181600f41d0888a20070001c103001c1a05050304100f2818004107100304581a600c54824a00d04203603500310060900b05038901400254003000034070030990060092185c0310010505980c0d003c14203044020751521181003d4407010401c0080c04c034401200c030b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 962678678 1250 962677428 962677439
    0x140406020303190612150e0f010e120c0c010305041401110d06080a0f03030c05090603010b090909060c0f07060b0301020d1505010e030304150302090d0f05011802030c0904060f0204 79
    0x4060b40c400e0160340d03d008001403011815804a56007406012800303062050030402081c5042191800e0b03240ca200b0009900b045c0f40c8185250040180c000c901507074490380780344d040e0507007400301f01d040d061074001550400003441e14582d00c85c01e6400c1c020703041507035640010341808206504915041d211100810980004a61031402e41d40040c10714000c040c10b0240008010f8800104120381c3d582040000e5602c0c692036a084002e884151407403002c0210030700c5099540d42c0c0e1000158000c16880f81003d60715440381040c00060000105038848581241d401c1000c00c010000850f29501404c004d42540c810840c1380181c001c140449080b501907102040d02154044140e100c00080d00c1c0b0050902070282c1e03950011958000c14401c41c5806400500003003150407100070f0b490325014810700340581442c0703103080420106030140c5000e07905003c8448058007400400e120b000c0007a043c0b42c0740310241c1d03ca142c0200c0d40c0c9140004103180506a50700005046c004198032032412202c000005654440e41d42c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 962679928 1250 962678678 962678683
    0x10212070501020711150711060c01150e1006050406111204060c020906030102040617100b0a0903030e01140702010c0314160501060509060306041b0317041509061e14040602 76
    0xb03401c01c48410340044040e5005d0300d41014003403d154000d1403100d00c1d007801070391f840c03141c0b0b40d5008035581c01180501507403010ba44203000392001e170f6506a001c000c04034076041101c07110200180410030f1403403086405201490384901240c01b9120103080541d403a10004d00d0701860054009042441d4005c08203010030318030b520040040c8410b008444030601ca49601080508170301c514403401e408a0113a900e0a408440d840558503070048110101c1c080c000e55826040000d076120081010004041080c28410907402c03007080c9201c8503003860983c1403243c0c5200312841da80300d42000681030169000c000f00406101d41440000b034000c8420f126100d41100c0c418644150384000c0c11111035007042c40c0840d440c01c044400c1803207000c1c0103008040d02c4d1500d0711107043e8085460320175405010341180200c0410200b89110244a40c203c2c4440d680300e18124141228030050192501002802d4808004140e882030b1152044a1590300c82407012840510907030740301c90b0321030b0100480d15000c640010365075000f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 962681178 1250 962679928 962679937
    0x50a0b0102011415040914030a0c0201090f0e040807050f1b04060902070209060409030210020a090608090d021e160801020405041103190b010e0319110414130201021207050102 77
    0x281c000b07005060003800c4031805448120703015007a03074400c541034070424902034000d0b110150040c812000c078499031008240c21031b800341c1c0350703900032843c00305880341107503403080281000301306891602d8900ea04050011198080207400541161404075400050003020300040360364440e80ba040702c60460640703403011101d8030340c0303401544141d2404c2000280d84401d4000c403401591f00510380f8000c0c2d43c803101048010a49694103608600c02c24240700065502440242000e400685031081114a4400010700c01c401c000c02c0302c400c81d0400002c070340089800055008803000c00c2d1a4060b8903168041c40e451402c41405040d210425000300c00184100701035000b0010b6500540301441850003400d2540790070700c000e407150a25011580c0c07070349800c0e20859000000c1c039001450540b00304198039000902d80711032000c5084c0f50340c8a20a0070020000210004070350000280c500f400b041400415031026001c00030a50b1a4070b0928100e540c045a20911017900c41c45840c001d150b4480140381840c6000303401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 962682428 1250 962681178 962681201
    0x804051906030e1605360a0f0606020318010e031e0111090321120108100605030f1009020604050303040b0409060819081317030a0e0a0f1205070306050a 67
    0x504643c4909420022541c5030306003e200d1400c107180744c904070500040c1c52010302c2c641d840c1010488854041c07150400351840040070598081c1850800c000b0b140c044540751070901c0c1c202440c00104002d62900442680c0041c4007620708200c814040f240140e0700420b4040c00350750305000b8480806900c81c140d8040840350168200204a100101e0200d81e81c18860818000c2d80742d80400d116510b09240c0007a02803001d0444407003503080440c410280c1609070001c0c0c00c060329030381018901010409041c411030004000850007090007411107583e4a0b180d094a21201c4812034035045004255241d040c1103d00820380178049aa0b501e5550708504516005402456051800d04400081d11f4800181c2044c1940c2c03840304c000303190301040d9941e01d5541d0110011004c8892404030000d0700031003c60320314181442a80c0910b5a0f42c0420348000d24820000d00e03031074400c0101c4242800b580010000302415209016064140440142803842c41c1024a5000410310741c01c00041001200090b00200880c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 962683678 1250 962682428 962682431
    0x6030b0d0c140312030a0e0f0d170a15090e241303090317041509030b0a05090a020a03060606020709150501050306010c051b09180606060d060905040f1a0c04030609080405190603 78
    0x186001508d0b519010a0440000050041114803221441d0340d01d07002c0d0000a050800154120500b420f42d03d91855a0300c603244442c2d850755041450082171010540c07003140340709640a40940c0840303075100300760046c005443d100050403d000825000b440c0030300155800031910300354161900f2071482142c0c40750040c1c0010702c601c202000000b40c080d9202c402640e41c0010007000664402c08034400a100c014100d544910448030190003580300c11a641c070189d8010400403502d20305014019103440c2c0c0a5100c010075924003106401c1c2914050107810a46000340b07001c0382e0346d85542004942c00e111001d005852405080100c407030075880100b0705502c40340192481149542c2d990f503400101207000300c5900458004c18005490b91610780014907002d01c1071240080c8050300d601d0440d0440b07400301c0d422203818406030711040074130400b0701110f1141154003184000c0b524280702405003e0049100003841701e503d40701c150382000130031400c0e41c0103041d014001c0350000014001b40f41e00c2d580e240c0306010110317 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 962684928 1250 962683678 962683693
    0x140c072903090d03050406140702010c0f090b070b130b1302090a0b01050318030417010b090603010b10030f0204030605070c060f0e0d0e0301020d0c02060106030b0d0c140312030a0e 79
    0x14060442980c0c40390108401a043e25124150240c0c05488010003c89500e684e4064648491241142242c000e81c1c484d40006810703003012034040c0c0f0001d808a20340c0140a80003a0800100350003a0460305050341c402140d2070300f0707201c003200d01d441c18403841d4000b0204e0800c2030810101000c4000c0036031129008550703450b03407074440000c07103800c660001002a0000d201000001c2c9005042003016002d1065001101e01d403e0740c8020703028100c0e50001174421701d651500c0040525280c0700151503006003044008102040c840c03000943c0f04090100000249601c4032249c400e9590940d0595008540123001031089181c031b01c10003044401d501030119161860a541d1101501481c030814262018447c02040c450729480c0e405d543c65100b038401a94599000c201e000d184001902840d20000c00f00c1d0000c1586505121003e4141c90840000a000d10b40b00240c007000308001e038801000721102042000d90134005500841d00700003882010800320a000018403240301030075440700140d45080e40655905 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 962686178 1250 962684928 962684999
    0x2405060a0c140c0306180610320a1205010f05040203100b06130f0f060206190c03200318010605130b01200303040b0c09010f140c07 58
    0x124022030351590002584440044002250405045030354400d020403901c0d000d0f10307800003034030f007240480d2112811000815031210304d40003041403503004611405c12400343d80c140082821400d15840e5002c03640031004440b0600b20451420240e206013000c3c100e05440742d1645044082180031310011a070319840d141c04d90441e02031902c40c031400740b507005000c1c0526440200c21500940300070020310354016001c1010090080c640821000108160b0440c0060729140010180d241c80b8280e01c54000d41d00300d10100640071507503079204100b80300c1c0d04800051855050b40100c1c02800607458003600300141c00d1040d20000c1642c1c002d54400e8210040d0102250700303d41b06182628000d21559800423243c0002995504103074221200c21074041c900811210664007540c4101800712900d400f00c1d070800010b101c00d104a000200da8030025402d40c05161401c0400000e0125490180050410151400c0140e05250101c2150b00d01c58940007150384480c0c4880f10490843c25480f0300e00d551109404142d0403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 962687428 1250 962686178 962686189
    0x80114060c0d03050702030f220806040803060d030507120e0a05060406021002030402010c0f030e040b01111906113108060f10091407020d020106180f0f2405 69
    0x15106034080c040c001d594109a010f90181070050440000c6d80402c0c0641c00030400d50501814a5079084100001c8400c06004a180c003045190440b120303a41040d400c02011031000030840303801002c10780300c50010300c90030f040440c2c080c0203280b002880040460001d0541c0c0341d02c46001c0d140110219001000b55a80d1420444148580c1c4178603005a0048803c4c10091032896001d907910030b0040c1000180e2100070f0340e6078691500100c1044000c1842040b10300c0c40c50809204560100c5000c0c20a41c203c1000f1680c8169680041000140080d02c1c0417030b64001c0004d02e0300440845000103042c0d5480e04004100d0380225050b10ba81c0307503110740b42c5002e052054500c91042d81d0844040f40042c08454458549042003044d00401d80d102500701e101e00044d00741c80d14450b01101444052404000f07041041d0000d0400d85960311000440e81040c805220412403612412000b00383c05c50b0001d8074403510ba91503405800c503501c0076454249040707460400e08409031a120180c0040c41e00592600780c45004004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 962688678 1250 962687428 962687437
    0x3170d15050307061b08220e0c070b0403111c110111040b07051c0c1a0105061603090f03111305150105090607051f110301030f08131508011406 63
    0x2d41c140e00034842049104d00509044502d032484000c0800c01402c1501c50002e01e038000e243e5480094180c0765441c03206440725081c40003802074003a107002e9608114000701140d018400010701200801c10200d403c2601514400b141d01c500342d010380e088921011220801c510302c194040c408038440c514185c680c5d1a041c800d0b038001c0d0003100d03501e274141818055080e00c0364120100c2101d15200d41d50300a03012107040403c58080064907615080004c105141c0700c005003450040c00b515110486005200540d20780c02074445284041034241819181c030700382201c2460242c2c0c03108002c071800403004014892401c5000031841000e03200c150141000e48500402c07141d080f0b0741c651100082c00c100301840c1d8032030303030040a41031401401c490810b83d07285c44540c2891149050070301e098000e0002206a0041c40c02944550429010880d0440d890b5488800d82074030f017500f00420902d03001684201810119a107200034058801504000300000300300075048000030b004903403e1240072036012020385810350444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 962689928 1250 962688678 962688689
    0x80a030e10050f072d0e011428050c060105041104090516030e0a030207030f02180f0702070b04030209220f030c030215061f050903030720010525080403170d15 70
    0x86600c9100170000316600080c90011504210060101d1494070401c400906401410460400a04001c07039580740c80d00e006401400080c06428440f034120540007180c20b0741120020356021480010f001c59520a600c030b075800a43c0d00c0c61034942881222079004610754150300168504001000280710900c2e0340c3e44190340c0080040e404040d05200003005040060b02d0303544080c00e550403051007200e40d2240d4800443e120101481003904200c01c840e81006088000e02c3d4120311145081e0840c2c000c01c8200303400030010412607000074035402c141c42d84058100040e6402265210b0200360615008104012444096006205560400028010b40040c0c05d0103100003c180c4001b50140085080a20b101038888a00f03209040c800b41d6042d403402d20040405c03034418005140783c08120f040e03032180e01d01c294020f41d0411a05010010b500c4a840c10100718020300c048122070294864038110b00030b440350340c10040c020449400c0b640c03181d5403074a01425848100b5035043c407070440b50540c4c0c1300050705284190b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 962691178 1250 962689928 962689997
    0xc110910060e03010b0a0905040515190506180702150606030105060a030c110f0f01050a0c0c02150903070303030509060a1a0d0f0206040f08070909080a030e10050f07 73
    0x304001d40c01030090a45404003d0700205005e8626400210600d115600030030075a511441044204001031142404c8092a040d511059003844c06240455103503160100740003550b1580030662955070070b07008055411031014400060b00d4185002521120301240c40205032a11101113104c900d000d00669050301c80191926041084005044020f025108030050a224204086000100d02072011868029090004140d946000d201860031110300030304110300185020100c1c40c41c19800007007140382d190112100b9500085070314202c4802d10503c1c000c9035262090100c00400c168242e0400751060302c0b00022f503001540d840750b05000b5201110551a00c0c0403082003004c0b441c3c41c0c0002020295402454480c40c088181d501040c26903101d504114441c40541004206035603081203c4c20141100f00b5081c400001160740d640030303500444d160381d801d0644030b0b042e5903c47c0e032040040b400c1c903443c40d40c0d0a00550500212641102505031080000a56256080200060b4103024490b28100c01c00c0e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 962692428 1250 962691178 962691211
    0x902010e0409030507051b120102030603190227010f0806070f18092a09030b0705030c160c03050c031204031214130905070c03020a060b1903030c1109 66
    0x8100080101c030314101c1c2400310510101011138000c0050101d12503031000741d045d010f017118080090000f0030504504262b80100100501c5031000310318414085144848215000741901c006030a01580c0e10b10340340c0410040e42e0340f0301e840700c01c034084034100c0d003000d802c02c0c08081e00d80c88220744500040710000d02050000d078000074220b2103400a206010380b01c08081c1e0603c0c1d10f601002007924029414500c1c001c0710602001140344424030003684094050410f12a540d00e166252100044001c01c000305100001c00062600341070340040740e000301401d2015050014851030540a480607034042079030701d486440e6003202d0509000130008010701705190154102861031799030812207001520118200020f180102d50320100380c1010300754406800206004c0c050405c6045812510f004004104000d44c4c3e01040380800d40100d0040c07132041e00880c011858480400100ba4401c52701c0d042407811580c0b04400105144e4804182200b0a1003103141250b0080c040f820090490310030f4507610070365140030302c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 962693678 1250 962692428 962692457
    0x2915030a091511030613180605181f02090d06090b24060d0b030f0a03051e0918070e09130302070e01060e091b03010f090c111c0e06040311090a090201 66
    0x1443e61030012844000804c007992154140300064840200c01c48500d5101e00610042a10380c40c01c091924079003c005000060320480b0bc00104108007a071182c10380c0c0d0011f40381d142501c0e15550140c045803c60f80621401c60245082c01030601c8c1203a2254030000d651030301c03940104014404120300480105020f0411100c0030050340241000c602869061044d10644984920305002c0090760034020384806844500c02e42465038400c00300a966011064100b040d801c00769118101c0c16404da9402c0742c4400c603565458010b5682102058109610450210400618030340b212451200c0b580302e50b0a0743c1c845d541d6418400e200000c02e0141101083c1186095581401c25200b680c2e40404040c142d0703095801e004094038020340c400c0c2c00141c240030f0184014021026103002c1c90011038980d1038500f00309841314003900d8641c000c3c030fa102c001003400300c4011000c0f43d11030a000c502000d40188010f0f82c0325032301d01d88505440152004035009100020009031001101d1203403101044e0181c5659070f4180d0241c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 962694928 1250 962693678 962693689
    0xc010e1e040609050a02030615030403020a172a0705010905090f09030d0c0224061f02120f0304022b06020a1b03030614042915030a0915110306 63
    0x18030095810070341d28100024041e081d8020180600b1400741c00598a0610b00c0c20b0207000c5244034042005200104240400a540080c560707030040c0c1c00400d564041c1001c0381d08000702e841020a402500311500f000418810b2140e043c0d07100300000c0004880e1001c4d40c503401034501000c107200301d0380d010180c540000c010b1910101c41c642d22111842c143d0b032600a14004110807944442072140042e8000c000b1f1030902c03e10b00310381e2842c2810321500903205151100014101e4101c810b1110501164602000035a038002c10400b103280c0d09413800035407102d5000d024154150412507050344294940641032072000000a01001d104494010b4503880100701c3d11490060343c418a2000308000e83c20150700700448002c0e239803100f000d100b590701041091410700128400207600c080e0902c190b02d04802c10f80706404504a81c1c0340d507000841400b480500c075000240b0012003450494105613000030070054903540d20f44c0030b000300354810443c02c890b0b90010580e00d421503003040d41d2400d43d500c0400200c0c000b403400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 962696178 1250 962694928 962694979
    0x3220816060905191203020a290a0e031602010e040207150f02120c300a0501090213170109020d0b09010c2f1c02070801110c07030b040627050c010e 65
    0x780c011a10032300043d03601c3e208482c0145084080e000d0b91000e2081d074a003040c5aa032a041242400b040c081044500751550316032151000302044a622920070004590080300032451118008000b10340750303030301c5040002c01d100248254490040c50414190780c01e030118425640c00c1e00d01e00c40b030042c9035943d02c0000001d0764024007240694000e0b032046410000c00c0c070360640b4246d200c3e0100303000041c2403415440c1d06441068000014003401445035000a02c1c452040b0b00c210b0340c002215004456496620038010907041d0740103500414990030050a118000c20424040d10718880204170001c5102002c41c1d928000801050710b00f0b8201c00031034006105c82000b4101452a042554001006201c2e0070400324070b1070b44060302507000030004201d401800c3c031500c400d440881d207d1038a00000e80070b40644a07096800300800d20040000402c0031701043e80c0c0b0040d5084404161060300042d07518140001d8505004210f49074800c0103420319003540f0a44c410010302d9000b60032030720448071130a500d04200d0303803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 962697428 1250 962696178 962696183
    0x7030b0c071505010902090f030a050d030c032c060a050f04020907051c050114120d14130306060911090a180e062505030702032208160609051912 64
    0x940075907052000d180c0e220f01c500903e040400180d50345544400d110f0900039508840b8440c0d040b100e5401c3c040390020800c140d01c0070305440c00103014035801c0c01c10b0300289032100d0000410301015640c001c10406012141800211000c00c03030300950f807859a21000d4403422550305c1440c080e00340100313005040c000d00381c40d000340780c41c1441170509860b00c0400c034012486a407085820340d05c410040140e10850f90089208480036501d8000d0000103082c15681d030041c0201902c200408030300604081c160800603162400c001405490025680c0e00306007000d08038500501c0403051400d02d040701000050401c544ca2208098180c51426241140100c3c00710883c100d8440e00301e449000e41200443d0a000c406d118032030404220100030b16101a400240b48004441018403c0820a114487d5000410344010913041558419042d109102503401d012040c0d200600d1441143c1c0341c024441c0601001c1b5003900c1c020b81d5a004460390318020814001103820078000f80c0404070505200030602c0200030681c0b02e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 962698678 1250 962697428 962697443
    0x706140a0c17121e1503120a021204060302120112050c09040809040204030f05240109090f1a0712060b04060c0809151804021201050105090d0507080d1107030b0c07 72
    0x8420201034596011106400000c05003031801c1c0030140ba050341300360001d454910128a0503040004296100140b4902c41052030020800318481e9108005000c0425441c0c04160f4a03150b640700e010740030303421101c540c0c0840342d00c900002c90f0014507140c080e01515005001003171103502c400280464014080c2c1b05840302e020030000c0302d440792a0b50000700011885011041c01c510b11608003035040c03039a602c03540c00b80d288070191804d0494070004807203410740e900395000180a41071481c1c440b01503119440001e020740720720f49a13082207650812199100d0748140c3c850904c004843e2005008580a070300580c0c411a200740024004140318586202d12140b160110528005516000a080c412242c8140061000c00540300c2002e00640760148024081640c09506114904488260807401405440d04100000c0b0364500a0b0b41c9a412030031020303801c038003a141550303140c440c402d81b201e820401c6100401d40751002108400c2c4000b4502040301c1d003250f00d400850b120251300308103640c0707c0c140c29078018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 962699928 1250 962698678 962698687
    0x3070315080c12030307090515041203050315010e011d03011e0501060f05180105090d020a0f080d08101401141303150203100512100e0706140a0c17 65
    0x65400c48141000c0c04500c03005244204032142008014940000000d00503002441409080390b001a041d00070b0b50b41c111080388090119158402c0349020395030000d0449010b5041c03000a00d0b405c040114020308610000200c1401030100640355444a00c2400b40050101c0740c000203d5200208541d45805d0006c0001c6419040c03401043c651110403507910600302d07030760801042041d0308801c010601c01d41d91f05007a41001c02e4480d0f2000b481c024000240d050210010303280f4a00e941d02c0c3c0003110450390040240b10b0543d1241e52105002c1580d0081001034072900c804010914018a8540d01c6000c05a407044421070800c8180848203240f00078160500c454280740300c80410035040500060802910711f00515482c8d07080030002c030020103010586107403040090022039090090f0440c2a58816100d4904005010250900d411405102040018a442d12000d601140400c1500c206d8a8035583c900c0d074070b0340c0310343d410190788544010140807070b9010000200103402c3c01c80c0810114614121141030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 962701178 1250 962699928 962699951
    0x80d0210020a09170f0607090f0614120a0507020d030e0703111f0e01020c010f02060a05270616030c020a1b0b04090e012a05220806100806040b0c030703 67
    0x1c40c00042c8400c1385820020382c0442c0180d003000f001e94000e50724034081501502e06080f00e0650b8110b03000f80400c100b07500c11840d081d5001541212564030480122205905d80814180000c01c02031b240d10005000b10310b080f010061181c00740d800340f2003113580900640351469541202014910880c142c0145510011002510304c1890540403559140c84440d8035120020009090520b51481c1c14140300d4001040040706600040c4da0307620103d0420009259100c036060805070b120001ca5046080806407101c2c0d14079200454141d01a600f01e41065170303803000b404400c1c3d050762840b0203c0700059000900940c085100400c0105401c0200340c071462075a910303031a000000d0ba0043c2c220a0000391150b40e200c14159003441181354554451281452100007280c008a604c544190802c040000104410313640101580d03241354410812034000d08002d83d41d00250342c40b42c0003101c030100c0f00d0f41220f5000440c01c44c0881d40030310650b403009000d03425540700407401388180c202821072401c00d0b94605400c0075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 962702428 1250 962701178 962701199
    0xc0f0609131a030a031805030607171005131514060f0714100903110a08040b0904020903191403120606031302040914010e0705090115050706020412020406080d0210020a09 75
    0x700700d801707543c4818a07190400103032400c020485d403004d0b0003680700d0420840c0244c0d0180c1c50710300d4540c1d003075000012516080c0c40203083c0c030103503040390b64080101321032840404403691105503420f0003c0280100302d940da1001d0b290642560b04040c0c0c0110b020031100c80b08000b42c9004003a018400d8020305015242907102d14508009420069146540d406010b4103060700705810310400365640300103012040607960b03000304d1405a0b11a01c0810303800803840400c607030745a4042c0c81c0c1c1481c01804541011800050301e075140c55664809480e145808254a010600003000300d5440c9032100c1d40050441e1a45070502c905a440104100c0c2e4900780e00c0e84d07290040e43ca07030003050480340c00b440b08903050140309141242119600c1184010384d1740400e80420143e100d644580c0d0445d400b110700000c03151459032040c4ca091085010003000148000742c0816403429400c03215440c00e00984c1d007080203030b071251901aa0303250100c165001580c8507141280216130716800400d25056145000101159036059124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 962703678 1250 962702428 962702443
    0x150906060f090b160c090929040203100b010905120606041803050f030a0e031b0607020d140c0718051b0c2d1905190f06090507170c0f0609131a03 64
    0x12aa82848c1200f0040d20f96880d1503421140c0038500303118000c1c140b031f90010703544880d0904650300c81915600c61620310380c09a11014010030f00940081516441c2d001c0b030701c1d202c080403180e8610940c036140c02e1281c151841003003046455072544a103460403505580b0f418140d00014543c1d01055200c200c041841b250605c090141c1074082001c40c110382d0309210001e4200301d0003d0180086501204030010702d90b174820050320b0300041e05d080d4980d589038141b01150600d421500302d02200c18020f200000000d04a510140c80f90214030f61100c0742056511008601e0310410041e1000350303000708580c001c17002c5603203101c84c181c10140241d8010303003842248242c00c05014240c00021101c040c110402440340601107801d030315500e00d03103034413000c907542c0c0c1d44c46480d8459100180c60346070303074041d403030200b020030002036024220070240b20064400c040b07407850b5203c0c200e0080e140035141d07290701c615207410003009075000f00c000140030402c41c16107081038900410b10101c10040d040d4003852034413800d840500911 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 962704928 1250 962703678 962703683
    0xa0b0301021306020102130603050c0a0e181303080603010204030b07030f090b010f0608010801020f07032016050102210315030106030206040f0806150105030402040b04150906060f090b160c0909 85
    0x6d40c69403501240380c618680c041c0d102c401410b0804c003c00030402c41c502c0c11195440040e04101c08054103071000f041c0d0300041b892a00c40044c0e0710b03409004960780308055081c0c02038484e50310a40355039510003d2500313074002c074030000380740800450100d84c0c4c00b4020342040c0545049101e00080b54180c1d034484006050007a40040c0c6040c0301e0310f009010180e403105565014000402c02546428414400088075120b0303404058100700c1011030f25000b121500d0b4001050344501811194060480d9000c4105110741c4e100715400340c0320b1305150104a1094440083e05641e0802c861b90071661072082c421200e4200201e1a80d043d541e42c0c00110050b90b072980070f80007400000c04080300040c140340510b480c1c42c5026014181107821001e1012842c1c4e0b00508030782d03010354180c80210b8000c6001010a01800c4503101411752100455000301d10000700342e014004581d82d5644040c0f920324903074000d8401c3c120038014206031110420505504007204840015601c0c42030090094040c4c1d10050f03081100c1220004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 962706178 1250 962704928 962704931
    0x71214010c0809010c0311040b1b03030103060f1b082a160204180c060c080708030403030e100e0a0212070515090108060609011b020102100c180b030402090a0b03010213060201 77
    0x240b041c81c03c001d11448101c10702609040010f00403c0d048000f845c06036101d10307141641c00190345400007004c44402c1c2d100601543c00c403522540c5030701d0810040c082c1c85200d50300503850101028000c0749103d11a106e010602e0711a01040d03103556101c00304990751500a0103a504406000c4148503ea0000030152204803864003003440c903461040009480344900c81e506082082d81482003c15100d07031402048680303a05203440c10707120234500711642e8002d1480c0038020b42008000c110900d44c01d60001840320721a04180e4504009003510502254401c120898041c2d1103161907000504040181e0a003018041c001c0302c0700d85035034034009031600d01c1c8084680341c0c2080201703000300c455802c040c1054000b401220041c1c10448003000003031181c0c15010581d40e1140d02c241220702564024020303106940b00d10b0509010301c00381c0120141424013204514082400031900c001503103c40740044d00e0040d54010001c62840d00c03210002c03005080016041c590655080000442d20410b001d80a0003d000c0c9400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 962707428 1250 962706178 962706181
    0x70801050f070f020d080402040f06031b1a180616150647270d02030c1014030421090506042306040902030f07020f071214010c08 57
    0x100e4507681d803406441e241c24440e040100c603115035004620000c5540552804143d26900c600006002d0101d03040034810f220303e00754020041c03010709800820304250341c0c00160360455983c5130300e032130201d00c0462010000c4d0040c000300664841d078071001c2d850301c03000504450410b500e030803416070851380c441030840d40356200000501610440b030040c900103018040e5040315052110f5043c1200e801d101040f28005103100e0a4041804100e00315030a003030011500c050744035074200c40c40c4804001d11001452082040810149040c907000f0b0440440a9000d03018000d805070a01c00e02a07100080d5414500780080105010081041d400285100e0b501070b482488a0f910503020b03105002c80039400c41401c2101488007884170340c4800040710200d600c080003018040c000d9180b900c1401803402000c4e94030100004000412551940283d230054414038082c40180e213408105030303910040c0c40380d004650f400c50b81041110320305080f0ba0300c59650003550802c0480c1c0e1120383c0c0d2821516144c0f01c00380070a007504c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 962708678 1250 962707428 962707441
    0x624091608090a020d02130219030b01031104030f0b0405031207020303060f041b14040b031602010c1b020415030618050c0102070317131707080c1c0212030c07080105 73
    0x828a40003644100508083c48464000c2202e1081250019000310640d0807584100c600742d80c1102c0078000f118a244129108440f40113014050b00c2050500180c1481554651003080304100d401300c0b60301501d00310307945c032a507a5401e43c018001407041d43c4c14001400035115408060750024881d408a0303000d180c6d85d103081410810f01c01414004140514500480e5464400880c41099414616814428816001e20003a01c40c50b02c280c0d040900401340110600c81c0340030702981c9054815400e60020300250221401c1110080170b2000c8000780c076407007a1269400341c00c0591000c044070751403820601081c1c0e141d46800b0709131188141540c00c0a480141c03c0b1090000a0009a601900034030151680c1031850701ca145003020852040c200c040750018030030a041104001c000d00400341c0c0d460b80a000360320390407819104d07525032041c072005002c1c40c080040d03240340a10400b0b081c020303810703640c41a181035034080c0950000e2004005c280c0f8882080f0a03204003104000040040014000204103441d155 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 962709928 1250 962708678 962708687
    0x1e08071517070c032a05060108010e012a09030204061701050c09030307081b06130b010501180611101a03191101140f0703090e15010206240916 63
    0x115141ca0700506803500740001d55030f0000c807146049030075191080c3c50310900d12041c0d0350030582c00c3c0c0c02c0d030901d0001350008003081000f00711641203d030f684c0020007420995204450a85034a40f40f900350030883d188100c001034a0303e45841595070124504081c2c11034507640440d040760001d0b00035892100705070303007200c10b070190074001c2c0b030782c09002c801c1018100380440340465906e008002c401000b0a5000c60340780c480810f10360205000e4410001200d069082021350300d174542d400c5890039a650600300d400480c0550181d02803454079520030310302c04c0e003082c07500c102110002c003140047d662a00820740780e1a0290b8183c010940c1d5404401021702180441ca8200761409000c3d8405580381c404007254070011860000203001030364004e08040c85440c00d00c0d00f0842c00c070701c03e000030004c0440300482c04c1030174103500040b0481515500c042851a0340c98040800e0300c901702c0c054500340140d1145000400c107443d002c040b5034000b07503003043d04841c203c0d40d500007036515071046920365403450b03d100c0d404801c0d6a22 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 962711178 1250 962709928 962709947
    0x60609021b0c0a0b1e0705120a11061302060d0e0d1833090e040308010501030612150f0605030111180607170304080c0105040b012c011e080715 63
    0x80301c0d403191903441d20244002c4d42c0a81124114000540b8401800154200c4100d5010941c85015901070b0820311070050540d03044480310b41d00060162900c07000303000c0e000a01038025101c400c19403543c520b00740d00b00f1503a9813144000844450321f91000f45407483e400c01010108841e141c44200004143c000700c150808610784c449038018840340043d68203044010540d212000c80070880c081c80c825410003d44a100081c1d102068081a19040101f0b141d0301804150607a0400d0364140022581d908000b40c2d0303100d41442c041c081c2092440144040c0c41c00c3d5020440c611070500d0046209a603910009007141d120030023826042c6070000b034500c641c0b0300d48007004010580884207c0d0074028241c50b1281054114a0100d007000d0000000c20207200715641903903e2407072180c0090009252a146c84007000c0c600b8810a4600381c0400031a10a16041c51030002909211500349001340e840d1500c40b1580185c1035145070345002031044c0200e800c200074084e00c8040d01404120810004100e103009114128 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 962712428 1250 962711178 962711203
    0x30b040903020d0f0228050123060901050904111002070b0a0201230106021b0d060603060b031c02190812100f090902010906030b0a090f060e090d0f0804060609021b 72
    0x8603c546c00340e01204016135034144095012180c880d04c9007441c1403801000c0c000c2e000d4001194544030350318001d0303103111880c0c404e04003540c0c0c0d9003103642e982c0b0902c40c0f9418140d5008043d4003559600c0b4049090070800100840e16901c103d6500507503407400c184041d0700840f81d00340181d4607103070f05c89401c0f045203410441171006060064029807500388001d48035070b07449000a0792400c00c0c9205400d00d0b510804034940441d04041d00700080b030380d40c0c070b030035001010810b0348180a40103514101c8180001c40c80c0c6240a4250ad40103010080c01c0101c0c9107425001078101110780300740c148170410041d03c501e05414400d00c0e1495562a9890420000d004840700c5907024040c102c2c00c0032400f20050340c0c001ca0140450324181008200f031700d010400104e80c3c0e1f00540290000f035180c042e050310341c400140c0002007103503401c12401040d62140f1080307545a51600c2005000706040c0002c15080034440c504050b4030502a100c0000da072500d03051400c06980c00340110400d00700b85031070b02844001e4184007010a028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 962713678 1250 962712428 962712433
    0x80307020a0e090c1306080d1709070e0604090c08060c03271e0309100f12050f01060806150a090e0105010f020709020c011e0207170c03070210030b040903020d0f02 72
    0x6420240c842c3d4444100c4c40f41406070b8071005100c64a2030682c0c100030054843c100998041c030384510070051010390500c0c1586c0e503018000d4042402d0b504013090400a0700c004c40340c8146541e84e601c0c240006080e51103011520360210003030000f00550280079140c0100c090702482c075030300d0500d4440c160705051850f02d881d580014000517441d4006d000204040c1c60714010810240c05000501001d095002c0c5c002d00c02e8002c03001503004801103602c00c4840c1c0c2d620703049407a43d20b41d2500042103070080b10021500b00d44200403420041c04200c1c09020500c1d8050002010b1140c00a044903111b80550002603109022543c107143c00d00c0031208899115014007c20701e090700303210854000080d41d5010500c24000003960001d1030791400791080d04403810014420100c1c240a00903100740200a5001c134400b5500105229201500b00302c08004440e0030455600046003440055000c01960b000e001d2a12401d042c0c0e00d5600d42c0c41c03902d0310301500c41c1d041d0184d0040c0804050000001d4100817010700014110f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 962714928 1250 962713678 962713681
    0x405030706021504020d03090509040b0f1303050403020d080f190909050603031812011e0c03060f0b0d0b0d03271a16060e060403030e0c010e010507060f06080307020a0e 74
    0x29120f1003106503029404640c3d6a071802c20710305064804403800d421041c0c2049889040105002d220b550b85405500c0d0f4000017030740741d580c0620401510b001d03890001d000520402c07080000d45002d4040502003801101c40c18581606140c1d444025881510b690309038030400503100c24060b0700414198010011103905111502e409400a6101e1095268541502c11307a4400482c00d80c56002c0d04c10b055101000003000800380c981410300c00110080300651042c0d04200c0070b00b080500c01c0c041c80c3e04a176900e1840c01e41e00d9081c00ca8001454104d01070249805131b540104503966075840e140340b80e41c83c4c0203445405000b141410800031258044244148401c01c03040104150090700000750554081c800b6026104d10002c01c0382c40d00100d0b000b00141c4450700f801d0341005604d1010036070500030b80c801d4804000300e141d59454161640d101882e91800b1a074042d107540c405501960051400a110f080300141d17030501203070400120b60041c2c11442690b03001048480031070410080070000382c074582c01e805106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 962716178 1250 962714928 962714953
    0x601240810030206030405251e080a030f05190c02030606040501031205090d0c0801050603060924071b061e0510060c0f1212060b12040201140f0d02040503070602 71
    0x1c0c40144802402100000700003030901030288080c503c15002c00c0c0241c2803844c49002041d0550703825000d444001c40b061090020f200c01c003103802c10200ca08850243c0228450f6840641d542e06195140c501032080c2046001e48200498810320070340300542d04d400803d66110f0050514040c001803071240030320b10f003800500c08910750a011600340d03503d501d881d90742c40b8250303004200e205245210091610110120104100d18107411062007550141c0c12545036949054050342d84050410314006003900408401420b45c51642e007203035104000d070038000501070003006c492008070703d0f00d10140c1300c0341d5488005100c1c5001d000760605401030542ea05108134182000904241105071080340248940000710004002e00b001e0189580b98124030703402e002d815840400360000c2000b090f4121494904000414003130140001d990704507008500a5043daa610ba005403019502c403140e00d201c20074140000d14003005400c00806100300014005030b00e031403510f0700345458582d40780c009005542000c01d42008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 962717428 1250 962716178 962716201
    0x70608070c050a0206030901021204050319050711040b0105040e0a14070203070b160c020907030203040308070318030e220605040b1507030c02040207080403030e090708280b0306012408 81
    0x10144e01150220b540743c54100300a40284140c81980e14042140c0080009001000c80640703d055201000c004940c0103500c401c03141cad880703000d500404000f0503850003262410913502084c0c040c8070606280e4035094480c42c42101000044441100040d00d0b50080c601505c80c0103000b98000720340e400210304080380e556641260381c0d4000c00c400440d104010460300c0d064031801c0000c503525000f601c040d005040c6a440100a540101e400b60042102140401c0c8003a210344141000021038110084ca180d0403581d00b22419031818007403561110b0340100744990015450000c6a070b0a050440004115140a080c0015540903541040c07154410204500e030302c1114400f2602c900798035140c218044415480010024022094050112140490080200f507046684d942c1c140a00b1180703c809030f524901b040340d948204440803102411103920308442d04100d462501418400c406000c01c1100300a8003003498440c007607100e0802011000104110001c5110700c0408000442c07406e000103140c0001a0174 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 962718678 1250 962717428 962717443
    0x9140a2102150c0d140412180314010e010e010b0a050405151201020f0f030106030e120a05130905070203130b0309032b1d0106232709070608070c05 65
    0x18401c040100000302e2010614080740d0400407081c04c10401341c0181c03542c44410407002c650071100c06461041011045018140d2019420000e40388560618156038a2680d810b000300542802d6640380d11146a003c170081c020301603540f10820000a5000800003000b24071a910342c0088d016a2505040c890001940f440f03d04100c081070750040354200b888203017a8024414140310942012000c40d08031110090000158100c80442d0707014400b030540c44c1c417140c2e02c0e51381c04c643c2203144800800c66010018028400f81031170070b150303840320014140e89551000a940f0300316004c50040c0c2000490480602d206002540600600c07100c00d4114501456103d959105d40b401d10140140c0da5481b0210801040d203680910001460b018007601c51110f403070700490074208100c1c000c15400e1103070215003aa1200100c102692191802030210222101408455035101421840711143d5604866484284405c114040c18110300102086841d00350001d1001d4400307411442003006100c2036002017000000c226 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 962719928 1250 962718678 962718703
    0x51321030507392c1b12010e0a023f010b0928031509060c0206041110050d0b030c1c030f11060f070e0d08090328060b030109140a2102 59
    0x109058903026440d00c0e101168011a9085c05400a504400107003041e07a42c3d13041318034109441035182c484403655803d13806000d030024100220812841c003524006400c050900d0713541d036100540184106820303040800c098020b0302c1a024001030b80c080c0c82c01c21064008041551140c101c2d0f648680d5544c000010005100180c104103030410145034410059000c2840241c4c00352013008a1550824007075200ca804443c2500e8050105003030400c11700304036050450b41e0001d556014a094003950400c2d006122091540f07400d441148076070740075900c400f48070034408d20b0480e1090040c1040d514004004c40312803000030003041240c3d0a4141c10540024000b600041a45d031007518030303503813108100c803003110801030164484540d5040700c09018000d0000c0c90f5020050342550b1420800d80c595079600300c068846510b0714034640e0584c0c03020940d2070340508213000c0003c0000c200c00c0d54944903008090311210350b4001c00e410050944013000120303980100201148910030700b403e081c082019440f00c0404402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 962721178 1250 962719928 962720009
    0x40e1b0f060c070e0c09041a0a0f150302070614010b071e12030207060f0507050406021c23121512061b0a030e0d05132103050739 57
    0x1017188032600b2025100c02200252040103504561034034050001c4940d210b6030f000711003140c000b091041c04071100c80305441d03002251b102c80a00b14002200207510a903000d0301d2155480500e03030b040260040800e8020028040801c0d11444e190401000c0070107021100e0b02d8544015607040b0006615031200100310a42d4140140c540398039081210192003041c13164241c15140004004a4a802801510a64126034211070302c51071062040076269402c09c0003003000c19030098103c100150001c51680d0f50720f0100c02480c0c01d00c940c1c21402c11402d0010703a403070140c0c9081c00c3c40c5148a0f007032900140c1d80c046a07050050070341d81800c1050a02421210f0682c0010030301c00119241018003c0d0000703c02145039034211803010000310030080c82070300002c03200300c3d40e0944200c000918074901c500704a00c000c2448051040c490080e50142c502d41e102141c111611018418400450400000ca11000c110035406038190b00c111414000f900940c0c0e90002100020000c00340000d41442d00030308080400010032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 962722428 1250 962721178 962721181
    0x70b1b0a030909180f140d030b0a050906031216031b0c060516050a06020309150403020c0d14160905010b070804051e090c09091006080a0506040e1b0f060c070e 70
    0x284d07074404001450180000d8961030034582048090101c0543c002043c2c1e05891070305250000440c103445040402c65480f00d94810107009030b00d80700507110b4100b0030003400c0303500d84c0c2c080c4880035401d0380180e404407900f45440041d6505058110b1503203000c500310500c000c4102d000365034410981c90700343c0c01050100080420141c4501d02521581803440c1c0d000411130303038014110f181041c084e41c022510340c80c5070b004100e540000ac150090703c09014540c10380140c28400600380601c49588044076043da98249421b050f200b2880050007840c60f50307000406026602c905007081c40b03054400c180d0285a181604120030004070300048107460950700112100034201c81480e150303210040304102c0c0c0d207034030041e044203115000182800a00c410301c0b041d180c501080d82d3386565415110307050b100c0c42000c6084039000410404c00d590241c3c1c0c0c801c2000f44009080c4481d40d800780d02d0444075125225400b600c074002110140340090f07545145c40c40803210070b80340c4804050060341301d20813403003203808003240e100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 962723678 1250 962722428 962722451
    0xc1219020c030c0c0a080607092106140a050c0a0c0206071b1d10030b04060e1f02040303030f050105010f0807120f02120609091e030408070b1b0a030909 67
    0x101101e00d00d406420459480d0a818410305880f03111551086203d1800c55100055206020500703070300c118803d031101500c06190400f0000c1070855103802040741e030940812680010301b01d210348074580340b008000303424500d0030250312404c03281c0250690400d00400d025140e0038507488018008000d5064034200c1e12103000e4900f05144842c5a400600d20140804011944034000c00c101d041e80701030807040140070740302c090b4061100031780340c080a400c0030410b5000030b0110b011074110001310310040c42100c0c010000000c40d01484000c443c1542922500040d0030010702d64140104a25100c051728100010351426001030486449003035800288200d0100141c031aa010310840012645031a2051100d001d061114030025444082403000f1041c40d1000b1aa0b281020046588103660440090500c030702001544400355111201c60385c0c840c8410030011550744814000040240944a556600da4010141d1944482e809140b030883e951b11010358100400d500c039100740708503202610002017015154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 962724928 1250 962723678 962723681
    0x120e090f010b070c0e0106030207021315060302030c16080a0f09050f01030e030c01150906090b0904060f021b0318061c15031a01030302010b01031a04020a051207170c1219 75
    0x10307030001954a02c617200010310703680c0640041c07000610031903180c0c1b400e81c400f050300030840709043c2a12076a80205003092007a507000350300071034011201a03101070070908440c1540d910400d410404807082c2c20f000c101c600310142c000c0403a120b0948035062000b0041c0c24500450000c40c1f04d194500e0426460304505032040b00180301b01c4001c0074196009003d1007981a2a94103c1880340c41680c080d90b1a10070f000030024064401e00d8102d81c0014000d940b035880c0c5072200c00140a420420085043d401c000e400d601c0440248240c214004580103503849a0f482c0a180314018110036403d03009000401c0b1201c81c03800c081d450510313007181e4100d001900c61a82405e0844072030340e40d0002441902c0c1500002c091031009101d66040300d22980c020700c0000000c000450a4070f2200c07006643d043c6422583c8202ea181c140c010382060603203483d1450410b01b412410840101c0c05498503008100710041c1d48901400d549a821351007079882d207481c2e10309035072103104085070100246250f4080161091031580011107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 962726178 1250 962724928 962724953
    0x10e0621060f09010f051809190c150305060a09140c0c011805010e100b06040509060415170105070f0507020904020f0306010801020405031b03120313050109120e090f010b07 76
    0x40c0c0b280d0407035a145d04561025135068003c551242120000350b00307402002011082c407814001001e44020038001c440005a0315040030100c807a07a02c52180820354003025031054030055516034010a03036062202c1481550b014039000002884c2c04e0030840541044e200281a4202d1b074140c0c0415951030f0a0a0958010003500c80c04400c03800414944500344441500600c0700e1440c8001594500c014184080e0f0803150b84561071900034205000c100920300c2e1524200b5445180508041042041a0719695120010381c00080c680b840034148001101024400c1a5002030320703040c025000030340401e01512601030190001d10072074606c00002e0454903a441c009820007805400c881070342d41c45161580c0030350854003506000e4820416100c0e00008128014109040d010b001781640070a144040d01090707100402e454842601200c030031f40041e8003441021100340c040c004034806100304260003451543d80140251040b204c1c1020b00c2420243c5c01092030460b08022221a40d40c401c2d49040c40c0b40c00f00c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 962727428 1250 962726178 962726209
    0x608100305060106030f0c11100207210f020d0804080909040201120f060504140613020a2105010311060702090a0b0d0b010311030c061305090612030c0c010e062106 72
    0x2508000082c005e405412818075203481c3e44c400c0c050450340c1705049404080318001c091071540b100c400403001e140258018403245016900100300c60011001221400c01ca07280c110000645902030840d4041c0d040c454100d000901d441c1085d0385040ca0303203a410480c0545803016104d8595200031808583c0a164441000c01d00700505002040c460110200146402e105560041d81004440c4906540440c68036211340c400801403400314206e042900c7c000e41040c0ca0344000d02450850f02d08824a201d115500d00071010100800c045d03040d8940010010401c400d032a01a180034414840103035101034905511045400340021030254507030018005202c041b4000c1d241e1a11030001009020381544041c084000076412a8034140200b814041c10f4820404820172034070440c2401d0055240c040e0416811074402040c0724560000a20356074150ba20440440b280c681c00280b040725156002031a441105004682180c1011200d12030b44c10f0450701c4003101e40010140b4800035513156120b080c1110f1402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 962728678 1250 962727428 962727433
    0x131d070f021c210f1e020a210b090109051e04050327060f030117060f070c0206040b0f0904051501020a0f150e0d0206160905100201060306110715060308040608100305 73
    0x130b83d6407030100070501c0c09030746049642d003a8400b00d000140c80c021a0a140040e9a4282011150780440d10f00300c1078480302c0c8a0703100d8450070039400c82c3d52200718040c0640316018001a07182014528500e1340980c0c0040c03107544113044010840418004070558000c4d0403504074030014510010034800c0120141c24560340d219030085010340c143c05610300a036041c0c4140c400303103600c14030111540c0350341d0784d0048035007145a40c141000500c00d14400c40156055902c00361005080c00d4460301c00348003c1d0407060720b804d4144004280003420b450540600354003c42c15070303c00c41ca8004103a000075203510904002401c0142141600c5040000c10710303512180d4030100404000303032184100706c00d8507004044a01c60040c802c80c0d0108664500684100030f455545031070f110030640c54002031002c3d15141b0b1801609555881c2000008a0414041d05000002c2044400e0b9240002d1501600d020309860b03890480c189841c00500000d0f010f8401c50302034881c3c50a10500039030300c0ca51492090b4501390002070050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 962729928 1250 962728678 962728691
    0x90b1f200102071403031003080a210c032f2503020d08150d03110109060e06090706180e10030501180b060609090705131d070f021c21 59
    0x1004190b02500560f80308102191090311003007901a542e00060340c0b91a03801d10300400c20000141100011302c1041703036508203c0b52403d00ea5401c2000201c004148140040d00d455a005d4815403622548030500c201c0e058016404880d0380030a035250319a09000407441e00c0001d0321040c090314120403540c2e070440c1007944420030b240500d4001d4540103401c06e4200414401c4d07010860580600e45a0300340f0581c00f41120841210740e031411544810010500e28040d543d540d080e00119481e07000b022052584400103242c0c0c0d0a0500c825441d0101c15071045041040b0540c0b8000c0304000762040030100c1c1e84d0000019078645840484144580443d80001c1281d0b10f0500040d0030318614440e01000c16000b003014551507900c8000388445442110070f80d03580100c1410004500354015030281045041021040c0441070b03d480200e048041404054039121030702e98208510542c0c0301d1b61a00020203103201801c03410820301000c2e071911100454520610011026582121500184002c8090038950007801030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 962731178 1250 962729928 962729987
    0x30b0a09060605120a080a03060b0d090507090e06131406071e05070203210c01110d0b0d0f0b0402011e05130506090a03020103022101180501090b1f 65
    0x40840c9482115094200840081c40e031034a103000c1e01001c13425101510f5211600da550030429480b40b07080000b416a80e980100d08201f001014044503294140001054440342c140b032480c2c0103982d0b01141c165400c00c0d051003490032001c540a03422140200c148042920b0610b0008913200020070f03004254800c6204108101c0d40c0045805080d10941c01c01041e110071018088616100341c03c00a07406611190b04201c4882c0e4002000c0702c0e80c80310050040c03e00b00c54494050955a0686210b00725550214500b000c044076071085202d850070407600c24401c1d1560b03a07a00001c04c0d52008000e00442801000a070569003e0386201600b014510b01500885c15850030103001500022100c084a80098101080a0030b19800312440340788014a00c1c000d085c91580110f0180d40200b000c09280c8003d00405e82541420514050203030032a94a0b50003106078000509080380c005a0281440e00d0a200380f840c0991260040002540c1d1010701c8030510f08041502680c2d0345201d840e001440c2400007284030034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 962732428 1250 962731178 962731181
    0x18090213110307090b040f150c02060a020a03080a090506013f03020f0106030b1803090603070509090c03010b070f030e280602010e1b01092c060103020c0a060e07030b0a 74
    0x7040f0034980314800d0494480400520341d004074001d40c002101d036514180444803401601483e000203a1a005520464945c04200e81d50082c800f40070240e805000c121040503040300c81182e1041c680e10040140546644842d80ea07800706204500100024035801207079010849941c0120780031540c41d07415002c140c81002d00d5100154901980180540c1030003070180241801044100e03504040d0f40d1075143c0304c02054503050f071005444500300380320400c22020b8a0321350700059840784550b511303030684a02c0140140090940010400160b900e401c000500c800a9443d007034601c030541014180326240745914043c1e4514044200d004d902c008180024200c0c1c40e407009400402d00a0325000c43d8040d541c135281030782070f10500c80718200300c1d82101c00300092208440c0c100414100051519503039695a501905c914041c01c4412a074100b901c10819802c007003803441c00c10360031400c03e1804501d01040080030f603485002070b510003001103407a4400200c0f0860104a094040e64129401a4960400b4030502c1c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 962733678 1250 962732428 962732431
    0x60c020102030f0403081b011a150405040f0204060f0207030503030f0411040e1c0201020901020c060702040204150804031e0806090a020f0427090312020c150915010b04180902131103 80
    0x7062082c00000b011f00c40d1106009a41050452010000000714a442040040c0038a00c0400c201340d1070602000603607030380358001c80c00c0c0700d07000207001680c5509020700200707100744801c9100150b5110110810004d000042180d40c083c000710a030200070b8a0b2807504042051461032041d6106c3d0904234008404c0d10045a4810004e010107106283c1c69a135203000d034240e0044000203405a08101a02506814244014110075200802c014607041d211045444a0b1907a50680e00c00942c070102000101034100c03043d0081c0f03e184e040c0f8030045103400c0b04003c005845c0107100b20700036a442da010a0659140e5016610312011482c0c860b51501d0700c4490f0144203011010768503c08055980c203013040718455200740d5060981540d00c140c00c020003017880342c3c080d41c07046c1c1d071603d903034445d28100c3e12010325140c001030b025415180141403440749040e503032000004107070080f000c410410001040503010006c0045c91071403042c1c00c00301e000619800054a2500c5504007807200d03605180901200c2000f040045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 962734928 1250 962733678 962733697
    0x815060f12150405090309040b03190b041505150103180822350304080a03121b0806010c0804050301060e040b070305070f0804050c0a080304091113060c020102030f040308 75
    0x603a010714004040200303942041d05c0980c1d50350420440c40c021414142c1081c0650310300501282e00c19001442ca034940800c9482c001d581044100c005d0000308099400c05031048a000031081c000c0782086640386211200d001c1146042c1a81e460242c10500c01d040394460849402ca0744860300c80207500e05412001e0140352407040e440700071420114091122002100c20240d001501c80480c83c07210140548086085420405c244010b100014000d0010020031000e10710a030b81c2d03511150b214074540f405603003c0c2082ca44503118071150581001d548082e0b0250f100c04d0034a030001e13614440b410b0104203032081e5009290554240007001c55008000c2c0516405107101d11b221418542d1003100403422146d00f922400001641d0007041c502e428400d01030640c0160051064403400e007140d0340012103492090740000110307000030904118207207080c4150042c0840308100130303240c014a2200d10000094a000300d00c1403021a80300c034004d69200300305803001d0401640d41d01d0382d160b480e81002483e903044040003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 962736178 1250 962734928 962734951
    0x20a23012007062a0b01120309180b090a0917090a2312060702062403030c160f0b1b030408060403211a090601121e0b010f0815060f12 59
    0x4c1212581c481d2001040c29400800000141c7d091048010181000c180241d0401c0620217001c1b0319900e41503881480262241400940c1c501d404050241021004000398400703440d20f4010070105941160001e14503503624501640c40d42c00741c000508400054002150380004106c54085001c80841c0d0340d1302e244011103499000c41c01e21059250749081c115018001038000e20302140694001c48042c804e0800101d144078402403800010a26641140c1d417803c1c038651000400c03c02089811070900d010700214550348040d507003400e40320607461081400074103900710360141c03910f98402d040c0b0030745000e03100c1041035883c0c900306801c00811400001c5001e0241d1505140d507409050007038801c081c0f032907044001075282001ca000c1040001071000300702c42d041c028910b040322107414007845000074110040740042e0f0802c10310f1021401f1240003000c0241408150301c9030341c104035040f28407203074402c03c0c94120200d4850f6520100c0d00c180245440300c54500404200f040f9180030000d0300034800d0704c03003140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 962737428 1250 962736178 962736227
    0x60201060305070f081b27100b0f120402030304080708030a020d09060917152806030206120a09080403080c010e0a0320150f0103020a2301200706 64
    0x207561854030f07803440b84502aa111b000f041c440f1282c1c02c0e00e25000100f00800042d40202c016840e0f50035407000c0d208481307202810303004020b803143d00e418032503002c1e00d0703405501824804005603000c124420540c18514620035070001504559041003242c01801c0c80c882a903400966030b03207003143d590304400d400c000075000e018440c1c401c641c03103541000c0c0ac4030407a990320001c6070318046810014484106002c44140201840c0e480d4070034004401c24004d11200000c14181105e150b94101d0020500c0b25207030003a03040200400150742c1d01019500c20700d0038404201d00075161009503c009244213200100000c2011500106008161000d0708040360010000d2104e012407189d603a88035402100d000340828501014a6603001001551000d00c2d40c0200403150502e244407101000941c2c100c624107002005000103004600301099020010321818041d005c13007050000d014039102000044c1c40d810040c84000c0ca4042d42c000084140e0070145c080c0680c1c0060391641e400034100ca02e2110541c03160750304100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 962738678 1250 962737428 962737439
    0x210705100e010c121106090f10051005040e0316060c08070806151305040908070303230f100b1b0c220b190608190b030d0c1b06020106030507 62
    0x1540750200141c1656442c1102880d981c0c0c04940b40c1a40e24400304000d03481110030600e4508005880c0280151030041c01e2a014243c04145440664041c182e03040d4148801d0000c07070202444100195a011100031030310000300b036250780c55402074180d400600001c403034010080c00100c0d808140000c1c0103a5034250340b9501d6600c151403c0100b551200e400c00d80d0300840541c0801d0035000760141801014410740056900d400103030540b8100320b0180c8901100250b040d0030590180300d800c013652000031140300340c540c0b060b880500c2505e0040c044000c400714600081c2ca48075034a20958041c101075180c3c55145c0450522985080320707041401c0d038041c820307902a10014503046403062901d108095000f0420040403424401801101041c25004030740180300c0e80700001040403000141030381d039590000e80e280a0f4400b400c040315100003001c8844c40c0001150603a10007040c071501503c05402d18802e48141460001a81c0740b19245030b2000c80b030000c6012488640c107402035012640554211a0b41680340e2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 962739928 1250 962738678 962738687
    0x6080609010501021504150c0503010503160e07110c060d0b10050f07151b0f080a050103080d15030204060b07050f0f1c0c06020a050301090e1f0b21070510 68
    0x2070140324003690055259020171007201c2d500650241c1b068131540c040d0841c0020820664a50401030000300d000440140070a0401700041c0d2034843c000d4105840303140c5407020380410804058440340400c5001d4aa50302d606004106213103090001601c0c096980052048010080038000211849a4109100300100d980700744184d030080c815000382c03d40f4004250351110040d4120b40d5002030bd840d121221000f0000c01c01711640e188980d42d07141c24903011001c0b0001860648010480c10382c00b45042c00520105100e03e081c1c449410340c1c003c0005c0e255074030780d0640da5009103c1d40300079445410103202045003250000a8050b40703100d0022201d880440910762500c2d04640c108100d61a884030903840c0e450003541c0c4810f0460842d5080003207625046880700070599105180c4c4071b0101d0030002c01000404034a21940e0484030039813000d01022131914007183c0621414074101c080040c0c45c0c1a00400c039664034002111400d004071161a0344464003030501d03484180314031405114030080026108502d00a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 962741178 1250 962739928 962739931
    0x30a091506050f0d0606050a0312111513031b06240b0711060d091a0705030403022d150106080718060302181009030212072301110d0906080609 63
    0x5180c6001e08000b482440130507a1442c400351040d54856000240c80e4490800e00009180034a83c02c1c0a141910398010b409502c8452100200354450101c0310744416040880641002d040c002040c000341c418282102c0310601c0354800c0700c03e0607004c2a80b41c2085043d03440042d508810407011160610b82282420f501c41c6244540030b10010304000542c002080075000d2240b928004141c1400d0103000b01100040714150282141d0312a00c032001456541d0b0740858440d03001c189890a01e245250503a4005d44400185403401d00c3d507910000051820300c0781010303112403418a10201e0740e5041d24003240d4140b15201384030300c0002c1204c040120310720394400c0360314001c0c20081041c0102c541c0e140c65000c80c002c3d030104203800b20320303140310b155031109948050491401e42c48a603587c084490850041001190525182c0f0b4240d0348074400c1002244851890b01080b1004200308107040e100100c0103031000245031030780300080d02820121500f080d400074050001d40c1c5140e03464907240c0d41c40c0300600094460 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 962742428 1250 962741178 962741189
    0xc010c030903530c03040803040902031902030403021c03110d0501140102010b0d030c0201050702060706150504051303030e150c040807050f0a030f020d1e06051e0601051e030a091506 80
    0x544000c02403da40800d8000c041001c1c560045900d400e1b40c50400a06540241c2c00c210705031500081800b0840f05c418a244014007c3c1e580308610310300f442d98002c0d59601c0031880500d840c24000b01118581d5004e50b000b24050503245540325501c6038000083d030000e20003406005103224580240e8121035105204940c1d9010024181c18048038050310182c403130300b080f07a01c228100b010801178900140c54070703805401d1540c406d80000c82d8a4145050b40c44030406980c10030b48c001ca141004010001444132200103a40780c00d401c000a011a0f0808400c0c10b0024100e08a0100380c4014140800c0103030620003881111400c505480200b52079004004010a41c41c00e4254415030072107040c40401c0381a541030f00b51034802420346507443c100e0759620281119015802031a04000082d0304103001090162a03407004c0c0070803800020900d14030348481c0c05000644103a042000200f07074210381c07501c00501201e03407201c95544603031241f61200da07401c0a802904400c640303a642c001c0128641c07204330b0081109640 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 962743678 1250 962742428 962742563
    0xc05011b080105120f030a0302040302030d0305071d45100b0313051002031e010503070b07050a081801170709180b130b210c010c030903 60
    0x3460942044070113024a003c1d510a13014000080402c1c0100b0002400090010340300580c4461540c0105400c00030a9428a0305040c200360030000c07140ea008801003d425014140d00e000f80c2801d4010a00e0b8272502000b40b050300790343c1d40d042d079143c3c6d03189100502d02022100300e400d05440c840c3d0f051411014191b400400c0d11345000400e10140107088003840d400740c108603800c0c54058903500c95030310780a05000110b00707984e400024010708544240d803554000031902d080380700d10f52600011a0b0b58000c0e5100303011114601081c6401040340910600744126000385c45203450301031130701c03071203508000a00020b404502c401507403003c3d04407030075100761040c003070b81d2601c210380b92800b522402c050018030a940f903001d65580d8110500d550fa038201c40070840b9003010000310140071038107000e50520a03180c0c01000401908600100f04400100b20714400e44c2868002e2100300c85180030750344040b0a4000034003074003034880402e0895480c12100b4080c00d5182d00baa5140c10710701d03211404007401c0c2d000e2802c22503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 962744928 1250 962743678 962743681
    0xe1f0e10090506060612070806120321060d0201090e09070b0f040501091409060d080c03180a12211e05091503090a020111150711010c02010506181509070c05011b08 72
    0x65000d1230840f0752044019021802e104042102581142d11102884000b11200040909512101e0340201e40c0401d040d5a10b0101660540018020405903c03c0040c0e151b40c000c00200100c609000313500061860002c516155074040380032010316003050140702d00088c15401d0020300c192a8041c40c6e6040384015101c2c0c81162141010300c50103020003d425201841d04004a4a84190401c02000601900d000e5001e000681c001000b286061580c042c110303001a022084e00402c14101034101124184034580b0801000c1903410b030307a105a600c419402031002d4802c0742d2101c0d900700008241c0703103108a030885401c44064828826a00042d0b600310f02c907920544a60780154059005034103400c41c12000c480818210041c40313403484000304c84d60400100c04811000c1d2460b000d00880c20411001d00083c48545400380205a000350003002c1003100390b44801c0820149030020400391001040509036608601d04980c001c0d200d2152007000712403a41c64074203030705034140c00f6011026002d200c0b540c81c20400e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 962746178 1250 962744928 962744941
    0x1d1c02240c0304030201142a0c0d080907031b03150e060106030b040f05070201060303080106021507030c0c060f021b01020702032d16050909010e1f0e10090506060612 73
    0x11900014000c609543d43c075a102440d80e040001d80303602c1040040408d00b0809400801850f4240248041655515041c000c4501035440800c0c2203c40300c180d4541301e502603461402040c60608507a0000e40080b1040c1c100ca0a4880c8d4040000305503409141119228070504100c14216114030545ca89142c11103401400894465080701d00295001030000c540b20f58203966401c1214000c0d07d0007030250f0341d540c50030800c040e0840142401800f403400540303c00422400c10450843c40200340e1002c041d60344130341c0781505006090502c5034682082d0200241c41400070400c0c02940b0041c1b0138010702c10020f0882030400d07414000c48043c0359014001d084011200100c2e03094014611220380c0c220030f01c10403061007004d402c0040009103a201e01c00240f58901d03001c107200522001510200160741081140c03041084002400c0300c51081441040c101024132111207030060110011465440c0680c1d028144480200c1e0004a000d07406181a120341e6141c850400107140f0894084040d0f06901900003500d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 962747428 1250 962746178 962746201
    0xf162f1e131e05070e104d0c030c01050702090a021207051801051213032105060a0b09090103030c0515010b07140c0a091d1c0224 57
    0x1616102600c001c608400461448062401d2074074410b0125555501000350f1a0381c02002e0005400e8107440020000e40741100041c0200515440c0e600c242582150281c3c0280c9400e8404040c0c0102d01c803420380603903803480d00c00c1d0f501805183d285101d2054800090441c41c0110301c1d404007501c16101c092514055500388413418000800c600d4100d03074240201410781402031044d0b403250045645070b55541c20480d1007445401c1c4821034880c1004010300900984100500b14641c00c14004420702c00e5001d42c52a00710b40c004181241003403604094100086a1441c0e07401681c020b020885210190f6922810300303858078015244041d5101d00d4000040000c00e000f403020144d2140107030261490a849061201d10b1500c0a91001e01005400101402072150603541c101408440e04090007651100b000001d8103644a402003814881d96a1410000c050f00300c02c10142e000e0f514010746180900d12046c07065400b011200c03900250041510801110011000440400f0f08030054603006450741c0c1100c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 962748678 1250 962747428 962747449
    0x30a03050a060b0c07150c020a0501030f290a0806042604080a080301030201030b03150601030209120706020601171c141e0408070504110f162f1e 64
    0x3141c1030b03030300c0b100450445158001044035041c094014036030245803000c00c40c2e02440c0e0344c44440400188012210050b40e41c3e524000c1101e100f441d0115504900c0002c90004180035038080380360005c409885456880b110b038003042200313022189550381503511044071742c48a40864008003a41c160825080e86c81444902e411020302075200444e08058403100030703e2419032b107090709940300880800100115a40340c000e4001034001500504002d043c41c03441c0118456010705141d042c0364001c508201c02c1c1e155912007004042c4004115101e1710750382c1302c0194503004280a4007200440320691540d071440005030581040074124183c072503201000404494582c44001441001d80080205122445015004900400c01500e03620344c0e030342ca00400c0030b00d0020203070300450040307040200901011015105031003401f152401441d684002c000c8210ba1002c8100100411042c1403134130b51018802998800c1d1440041341603503a052070040c030100400030151813024440c54285099a60031414040c0514 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 962749928 1250 962748678 962748691
    0x61e0312120f1512050c040f0e03030f0601020105340507050115180b0604121b090f06050a0b03060d1e03020a331a150c07060809030a0305 61
    0x868501c03401140000d41d10714002c0c107404951200c1c1904035002c0d07000031000042008441c40041d03212907640d0746442c0c0c3c0440400911595079501001d05240f0541c1103442c4000c90101902d80c2c2c0c3c42c0202c514910080182c1d10240150310b080d0005901d081603850303014000207103501c541c8807421200c040c4007100016000d03000410400340001c20001d8000d00a1400019480c0d5000d007429084c2480c1d200d092030340746031011069041960f420303015101c410484064031400818100104624285040c104030700ca240710741000280700300020513500c56413042d09400159007045c012107070f8807001c2101c51815400b440303a03c0401000481d8103490030b84445103004d072003001d80100c0700b0007460b88950b49195440050b000350f0000c100d45400c001d0f01c60b80307000901002c0c0410340c2058441041040e489035190307411502d0b01d41d84207945407665039000700e007100090006180385d445010303622641c0000d400200454501e8455840c0c007242640c0550a000c0c400c801400c000c40c100359070410214050103024000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 962751178 1250 962749928 962749937
    0x703110d150509060f07091814040309090b030d081f090c020c1f080c070516061e08090303061c3302070507030f0312060306050a061e0312 61
    0x80c0004040711042a0075610385200000c0324504400e01d50300f03040d0300401c40024081d4003010001000c0c2c10902801c00d8542507403804041e0114103e00400a01d640000c0c0d4682c501340360200001c059100b5280744c19a407207071034148160a17100c0103140d501c403001101480825030503000103001070301880001c4208030036600b07c415501c1d510503041c02221044401040140c000300c81d10203c50400900341d09a903120301e507014841100708007005001e9400603000d80200b500000c0d8000a00904110501c00496440c010f804410323540e60016000e40300c0a00c04000241e03134240181d1806011360741c100c4c820610384010750708d542e980400304407006040c802010884001a0000c1002c03600c1c440090110320110709118070f20404000e84110010760f9451583e00c06401000b0750000150042288c4085a51104090400c1c21072803800b40c447c1e600c01207a2400e1180740c882c00205020b0304d604003c2c02a40c0303072141080129128480031905620100c0004818002384d54200005906a4915502c030175072482c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 962752428 1250 962751178 962751199
    0xf0726030702090402012304090b0a0f0b131806030311190303020c10020d0b0405062b110603092118100e061303051204030f0308270604060506060705070311 69
    0x400e0207103000300e010309444110f00230500b80701c011114132403640c185404481c07100841d0b20b4404010108901806110303a460400f00d52265248100144e507006440030302540e03403c03008100e400303000402c0d1611059000031045858441900000b01e0703d1902e003c240d040460b040c013031a8030290040d5101f640c80040728825240c5181c0c0052a0b480030f400710041c1120041101c1011008000664502910461147ca06c03442000ea041c2c10141d40340301454001c2000d0307118036402c0d00f000c5403c40b10f92105513802140c0041006a81c0e9030114081c0d0f0600d017004000002824403485000640c015040c4400180c0c95880c1059000d1600c01e1031f04201070700c070740340c040104400c1030041451038104052865030109001c8041c0208070062040780c440d5100900390600306403454136040e4081182020260a108001001c1510000c4c0030762032100818007170a003940502c054400d230982c0e41c501198196a5280f400c1d005c162145010411122210b0300000200b0304a8195100c001c0000440303202c41cae500c00d8441c203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 962753678 1250 962752428 962752457
    0x90c0c0606010c031112070c0b0f12070c0605011701060806013204090f050d050f160309030b09030a0923150702090f0712050402011b140f072603070209040201 70
    0x800c1b1080f21801490b0b00c032022071030f09035510111074000d040c900c1400e210058800403480241c03042e0b11000001d96105480c2d40809861482c04004003030703c01c608113000400e2900d800c265510403415500002c10150355510aa00d0301e0b080c0130300803c071a078038145140d025261816041980244101d4ae803003100441c803040020700711241407104681455804100d07000384002401001401411805c0041c03408914a5010708984110021200c1c88400d00c01c216091511914102002d903034002c0055142c1e0400d00300d010798075081000a040041c00b001400b140310500c2085182032082e40030144070000190000308030710340fa03032148440c803405030078071045001d030f622101d80d24003406a1a401801d03e0800d55001441c0c000340d51206d0401c2800e00c401d002c01030b40e0010803e1070040b45890100e6590b59140f03002e010b4000141003451141c0b01e2440035450107080800ca400c21220280300000480282907003078220b1803010030000c2003580051180d040541040d070f0116500500c141b400490482209 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 962754928 1250 962753678 962753683
    0x6140a030e160302030f010606020a02011d0d11100306050603060402030c0f03100302090a02270409050a0c15020f0604170c100504020906010c050a0602180a060e090c0c0606010c0311 80
    0x9154100311690b200030100705504042c8141a01d804049000b4805581400c0011f03541c1c44540d00700034100301030a0410f41240442d01283c0e81d0303400d001007040e10110910b040400e54655146080ca20036a00119000b8005009104400845034081e0880c4e0440d0340340310400009400c000d01100c29400c0800c00303500d1140703119000394451001c4c0c1d0301d1454618254018040d05003401800f070b803400d91040005e55120b0742c40ca001c0b40c60030b82101001e040608415000700300a004010b600824a11940413964200000c00c580300c0180c6240c00d000701007203c0780b01801c99a0707880740e04c1c008985130400c0b40402e0210310350251888080292541651900d051800110300e01250203014401d100d0380c0e0341c10300045140c1002102d402c80c10901c1c159031514056140c843d201c40e42c0490040c041c03a400a880031301009541002c12846600800001c0400da644001428081845d55818440c5c80000c00041002425000b542c2d03044081318001d1500313030f45010041d121000b07601815814400780c6458070482c94000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 962756178 1250 962754928 962754943
    0xa020910052a0c040b060937060f03200406020a0b01080f0c010c330c020d2f0304140f030c1c030302070c0b2206140a030e 54
    0x1036540700c1e50344034408440300115094007080c10b0b0240e450848800301180c4001624080a0011540098000e0040340001c1c814400d10600d5a08081c0020400340950144000e403421104076840c4d041d0402246c0d030010a8076040b80c0205400328070f00121071313101c940c800e91000c2c403240307040d140100e0600303000301c40e0310b405801961200d0300507800a6200300070031020008036801000034030018241030f051050f00a450309101d80c0c2581c10000030b010107800303110015851b9050b070344018034184025242d0711109102840718940e05e26109090145c0000028400658048000780550783c0c401281d034486207494111003014018100c031028504107800540c000c0c0700030001080e0804201e12640c44600a00c0405140c1101c0141300780c01c420002e56075501e80e07910034561100d220907142094a0070349801d81c000e010308003000e0140070300a0400303c1c01c0c06000006041c0b400442040c07810040500c52040c9040c0d0490044034000b544401505450746c030448048c00100d1014103000c144120101102da140151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 962757428 1250 962756178 962756209
    0xb0f040b03040f060504300203040b070c0e01080c0109140a09052503020d140606030a110403050d020a150221060d0b04050a0209071e0f030b0402031612090f02090a0209 74
    0x100454114640c0015500002c50182251240c1f13602242100b01a440e40624429120381200014114003041020317442100540200c404003e050b5843e4801c0c2981d40d8410502d0602040c50f804001c11030101c034901003a040c180041010340f90506052500340a1700000c2c24100c00410100c0d45171465078618200e04070724406940e030043e2548055010042654500119991217500f10824000c4946406089a5000c008160040340789100480d0039092403040c0d03417000d400c500035a04944080d07075020801c4200e02c0e000300c500b1450070f412152a6800ca00c5002c0c681160800354440300720700e104070b80040d40d03448180200a4500300b0959182c603012104111803c60f43c40d0481c100000441c81c000d0b001f160045503c2c6800840d40485800148070f0448540800c01400200101d020f4030301d102e078001504000014109544909100b0301c03045418888001040128040c00418040b01070184610510242c0016021201d018540c0900065200191020400e640c082103440749544907100b008442c02c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 962758678 1250 962757428 962757443
    0x10091d0c0420071b091e020306120a03020313050405070e0d02240405031902030d031a10031e02191b080a08071205060a171c03090c0b0f040b03040f060504 68
    0x481c0910000c0820710150040c90941d49001c00c0c0401c1440c14007103ca03980c0c500c1c0c0c000141c8c0ea0305d480001442e1240c080b5081d41451055180c8001099030105c040c0c01c03903151445040300102d8441040005031201100c4050000e10903181c000c9151600c408901d40841c0060280311030b11004040034224101d86038010031041400041c00c0210341000c02441d01510100344c0414080d062030360001e40c5548110488008045c0c5800804050000028540708550401000d0300a0704500078000740241a2000003840e001c21010080e110851243c0226240b44484200800d810001840f00382c42c41e002282000f11503002e08910000007038040002805082040d0311a62454500424000c0c111136407410000740c920706100a00c41c20b0703181d4040f101c0c10b840715405056220204100024075000100b101c2d40d503400314160502c030b107880e0150b110100761070041c00410300b16500c07015840c0c61441136000c43c42c2034040800c07040103400f80900207541c00c18440c4007400e507900d090f0f842d82c0c420b030f4030281c50903590f11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 962759928 1250 962758678 962758703
    0x61802210112031e05031807090504030f020c01021507140c0109050102270d0602090102150f06010f08040b1b070b0705030708010e13030e03011410091d0c042007 71
    0x15400902e514101032904041c440000c4d00d811008242d03000140c2105404100c3c40710752640000c003404004007400c029003003045145045d04004001e204200780010141c080d280c5814032951011898206003100681032410315141c426003103410840340c02c0d104262017400c4c04032102c01d0300c003030150708c403031a004400140e1124002040c0004500250102130070540302c0d550184551b40700c080e0100b038030075082003006859000d0000144e080541041d4142008a480003c108a201c02e042240e4004c1c0000e90b07900303070107521400e4241c454550035a00608026010000280d4540d5030705ca01168640302c103074a02c2d090410665030031503412016200f01e004507001000304071b15103900c10450784c010220f010048156040107205402c0c1080600006070421583c0b0040c61880d4809401040844400e130b8040500c43c81c00741890051020306000c1e0181d4181401486001001e0301618604080c0801015000e40384800003004014900401852500e0030540408a2002580009000e6a601808c1d402c07107107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 962761178 1250 962759928 962759933
    0x10e01021905070e250305070e12010c020601060f1b0c05100f08060402070b060d02060903120426060112052109040f020309030a03020c0c03120a0e010201061802210112 74
    0x13480c4000c102d14a88401699070010310306000e0b165880c007a456003170005880e00c3c2c0c60701c2110004206003d494200044010710400c0000540c442c0320402c280e40d00362561a41c8802d0308440d00c00245203080002103c030000b150101400c807042e80c007040d114610f0021015560303000b140340001e0160b560408100d1980c0e020030f205400c10b50f05540154200c500310b203090410754506401850146c2014042c0c44c2d41040c003811500da5100702c81c4d000c0401002c460b40c000191440318804c0d44130b8091005203c0500042082540c00e459011607503c03201806041541e0034440c1d50071801a5003075003a03401d0700c04c241d05d6000a039500d070340700080300d002d2584803a80c3c0d101440600040d182c00414011106e4410810007149a2010044e12221020b030319000d030b42c818201401c2464440120032440c1e16000314012101000a07080060881542584481d00240c1c622001a800c0320700910400651490090001c18040034a0f07004121400c2d260740101c03040546201d50060710354098000003070441d8003080c1e5205 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 962762428 1250 962761178 962761199
    0x10801091505061c140412091a0a11160504140112022e031d07061209080405181803090102030d0e10090b0702012019140f12010602010b0f010e0102190507 68
    0x50301c00b50419040d5036103007019411009d00c51070b54158540d01c01180c80c2c2c8820f44101711116595400104a914000f94907003216080034862084511586c40e010303440102c0b0807504240c03412a511400710304103d8000e6001c0c80340588201c40c51ba20b6510000241d00084546503030315120b003465550300001d001d03401c0440b0058451410040486a61001c0300c1000159444000084946110070000c01c01c3c240c00e1414048502447c4c01407a802030200c0058400902c00c0590a846590141c1c0365001d40c4000040c083c2d20703845822101f6005804c03c0041c00e40d01241a009882c81ca1185003c4619038140300a2040c11134481000403110103c2ca00244103000b80d090084540354107180f590b54424070207907150482d2a109846401603140350045050301118020800c0c0c04100700c0b0300148a03550310004403143c0301944600c018450b078020300000803404034414420b001904002a059000041c0c45500665004880502c6181148134074a81e44d840e04c8984a0009201440740c0d00412540e03040c40d04504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 962763678 1250 962762428 962762453
    0x12010308120906160f02162936040507080103110f0d17040f0f150806011704051e06060f03120304061505090411010801091505061c1404 60
    0x42c41d601500c184111854601c466000e45000b0742848200018030a01c141c2c28203000c1008849a0300f024440000c650b0300800180c020020680b405032a40220a00030145034001d0440204149500e240c0301e40200110400e0114407580040414210004402c0060b0603030300111121070000304a034004008014405555001060341181c01019a01656002c1086c4841242000e41204a8000410b515400810403207014100c000840c05006440780d1205801064034400c212541140b0540d100a842c410601e890040c04142e461008601000e000c1c0d0001c9000a00140c8943c00303080146040e42c41c2e81a0a041101608809001070303191032801c0007100c0350900741090198019140342114003130400c003101c4e4400d0780010005284161100700c1c4420104a40010ba0040e80c04802d00040c45191021640018805d81c4c5035000d681e01d400d2030000761948000c0d0700483c5241c607581402b003841c003000541b03072001c01d079180448140b80c48410981590141042c004005605400b44070910504103882c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 962764928 1250 962763678 962763691
    0x109230418060e1b1e0f090f040c1a030606030414071e0b0a050301030b041104330602060105060a140706020415140319140907081009020303070305030c1201030812 72
    0x1c5440c01c40d0130000c03410ba40445100319421003040d000f4111556a08240c001403440d010f4042a1140b030304c1d0544800d41c1009580541d1003001c0b1040c0001d03460000410502d403001d100c4245070031510ba22080c0203c0350030240088070010701f40d03246440001401c000da20000d01034050b0040c60400e00c4207103541c01d22015007040ea540c000410441c0c2005030003108990460707a00c03518420480c1d5890501150301000705c55595802030a00e42a0952600c40284040c2e6000c910031580891410f0b03c200b00c0c100c69024072448016070803c400400c960b182c03c60150042c1c400c0e504040856030000d0700c0d1a403150340000003c940c0e569010405100c80301191001441d2101c003800d1011140400001800c03560000502d0301c2c1490300d0b100404040800d0f0303030700130394405e9030b4188034140d145c1440006c00c0c2c0c40701030783e01861010f40304901c0c290342d003c8071a02450030016009070242d880d010300c07034600300c4071644000c0a9016102e02013103000300805e0102e034114000c40c007480180c4c0d112a0400880fa54600c00981007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 962766178 1250 962764928 962764963
    0x903080a0f0213030201140c06070c031e090b0306190801060602011407050f0d0209060d05041520070c12080a1403041e0203010f090c0806060109230418060e 69
    0x241085580c4a1160f01500e0702424000c90000d040d200300031240c81102c28480315401070740709000585070080c60400c1c41c00c3c03107030b1501d60806220311641c0789a402011313010400550072030b0701042209498801990000e40141600c50b480e00003500c99440750303540360b11031035a40c1c0d90348204000440e42071007100307180f6526121120700b606260400410a010b15900f40640000021703502544480750307411030b85103400c054400d076100d00c03030603080c075005040407a4103403001c40407412aa000b2000783c1c42002c04810b80c51440c030090404a04610902c0d0700f054804541d0740a0741840400c56407020051241582d220720400c41e500c0303000380c000800c0c7d001101e00d0750030046800e1090000103062644d80d0100c1a6100300f004050043c84d0000a01400025120303000c440c0c501003041c001d001d0444c0c64501502da030b40c2c1c00c55450342c5542c801160111820310460081c204181d513280000d0740ca078102e02c4a600402000410405400c12086581d419a031000321401c035680c10860040b03a1003403001682d00d04a00341c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 962767428 1250 962766178 962766187
    0x41101050a2115080109060f060807030305070623010825051c0209100f0b030105030604081605030d0f0b120d0f0c0b010807081228120903080a0f02 65
    0x100540a055004000c0480401e00c101110080344154083c1c101a00e8549890b4915992514418004c0803c800c042c1c98260900301e140c1200da81c03074015482201da40c0700c02030000600d191002c88194003c1d000803034180352586440c1402510741c840200c0030800b10b00340401d0b294501002946000c4155a030b2200e501c49070845c024003c2c4000c2e24800c202d50050740c210385108120460004540c0e60518000e501181e8038050080e000075220903034064500d100c000f1003245883c0c0f40c41034224002442503503415444403000800144a4030060401e8100c8120000911081903440c1c0f42190400d800190316240c2d1910b64405402e12401800130300780007a1206032090301c0407040113444d80030404401d070500030340c40c14a03045a8451003080240c56003003000d440a650f1518802d40d1541c0c5513208a2849101d44405078003860f03005000c80302032026800e0510403540c2c0b001030000d04402ea28a900c002c1c03040461028903423080d00d010742e01000d413181e0760b4000c607450107801c0342c1e0032904888400d241c060700c1400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 962768678 1250 962767428 962767447
    0x608190308010605030a021e0a170408160f0f030509040c17041205040503030408030c012004030b0618070201050601020d0c02012705061201140d0503191101020a020604110105 77
    0x3071681c0c0c1902c1140c035086075a41d840b8942d03480644155a00342100d4618042081c520700c4092010f07112055042c3e40c3c0051345003851002c041011019280034000e44402c101900d900001d03008800d081c0c5105643c1080c410000b0740307a0003e0304071040d030300390041440003034001018a454404c01034102100c2c144100c4400f1044c0446440308030040005003d06906541500f089010384240e60050070000c01f1070769116140c122050700e030741125120007801e600741042035a40303405280c031501025441039003041c20702d80341d5107482541760000381c031040d044040c0300980624445440010381c416130081d0008502030800d2800240745c00c030b0039a8000c08024442c115800141c2c0d00c0340c8080590003190000e400703594400e0100c0250b0052640c49140c0c003107000903101d02d00c0041102d40504807510110260700b00002101805403d00c102c4e40014180e400070803469a200346842e2401c20f4070030740d41c50305030300c1203244050b400d0890340142180c801592040c410071080185c030b400300500d540c1003803802904094205 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 962769784 1106 962768678 962768687
    0xd0c0c0506090f0a030f0306150507110108160309021906081806060a0b030a060506040f0e0108160e0c120c0a12060e0105010513090f06081903 63
    0x80c0000d02d451401141d01c0b800a58010301900b4407103c0c43e134049509040e035035900d10525036155400700722680c0301c40001450340841d03124165542e40501b42081090040f200b0a17042200361002c2210442070503005491044080c180402c02100c00d00c000b4860b40c490505080290504150008013250301c03d074494019800103050b20480300c02011080e864410489505406c440516070403c10010b0f001c00450b0f1142d94403800055558903980002c1d00396110f68480084101500030621100050216507401801900000e0a15008a000080d203030050383c49070b50000003501c0005184c21034580300b00c0e002c59040c0d410002280c50074044114880e08100c0440001950200d01e04054800c14030070ba8080d03400c04c07840101b881e8640001100d9a501094010b0718400064000144400c0c10b401100050010b00b20f001c9200c60800c80388034506002c6003150492038042010031004640c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 962589928 962769784 := by
  have h0 := BRFrame.cov_init 962589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 962589928 ≤ n) (h2 : n < 962769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
