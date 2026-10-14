-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2611
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:47.201213+00:00
-- url     : https://prove2.me/submissions/5f36f4a4-4cfc-4c60-98fe-b585702c3a83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 469424460 ≤ n < 469604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 469425710 1250 469424460 469424471
    0x3060402030a110c16120302030a0804020a120506220818011e020d1e091a0c01020a020f0f060f0601110f0f0703030e030c010801030b0a090818030f0606090703 70
    0x45103101070154042064040f4030040f071004280003002800240b82a200e0583d141e00ca552210b500c0c29481110741d000c0d006810800000280a0083e20a0fa420a04c0600710214050340e4008131800030381c0e10036007112141c02c1b0f00180600d030028488500301175201d6080d082016180c59036248100e11804c0f1200c01c85001a81420819a014240306115454040810f409002800d403009441c0c02c5040c55181c042004110700000905c01140c4003808840140c460f02c440c5810b0403c151541c1c804108602c21a001c20040c14805d00001e00140111803d250000e05082c440b4000e982d09000007040c0301405603120004028200f40c02200081c3c0003502801c0c0749903a05444948a41803240d00881c1d03d0070340c802d42c6181028054005680d00840b8040e50b980c900442d070900c209500d418210b09030134000754a14005001050074401d880d40c220300309900000341915155a03d50442e00002080e24004901c3e50070046182014410114140d0342500640024542200001c0c02c154015001c0410142d452 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 469426960 1250 469425710 469425721
    0x606090e0c0409110405010807020d210f02040b040f1202090f060102010b0307030c140406030803010e0c0d05360d050a03060801060b070302010e0610090c03020708071b17030306040203 81
    0x1503080358082c0030803150501c020380104082c4da036680d12920811340000d41c60000a0080f510109603038840c0c001c503640c1c811000b484d810340003025075207940010102e00d82d04c03c8800c210460030310040000b000740e625420b40b21f5203804581ea03045651035201d05003d1241c10040310041c0e940044a540c4802d41c905464180e4880800403801000c000507100c0e00341c86095008024082a440c0e80012103141884812155040a061006642051000030300b80101440144148020310800c0750f84203a040240a0800c40c0d100008416a80183c1c1c1e490080c4c80001c914290b2803940e545107203070500c01464070b40802145092820340d03c000d5602c213a0108400801c0c0080018803907000a402010480d000b0300199071100c44419155101e04400c501642c6400e001a80c00d00c400b14a0500c41c15800c40001c50991808489401030004650b076142056403c000171070006000e0f40141208074014944e1f107440001d19424240708230b0442c2c1046810602c1110a000311104c000300300c07130b807003501554056100d4889 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 469428210 1250 469426960 469426981
    0x10c080c0d0f020f07200d0305070f020609061b01060909050c090604020d15080f06090a0809010224091203010f0611010e01060b030a0c031523131a040606090e 70
    0x24a90365200c441c40001d51700c0180100a0001d4003081c2652103092040c50103802002154040b803400200410000e01003000440d00000c0040e4440340040e116900c0c1000712400103615a00c10744105215441901340080f01680034800c40000c4c051410307003000141460b0b16411781c4d42e900c3d03100180c414005000003032256161501550b0030844039000c1400f14140b042c03d4020003d1050081485610603007901003d18030000a42500880c00e20300682000300003600d42c810a03a20040806041d4894015002c1d2007002104291170300c02188442c007030540c00c0044c441821b0040725004041c81d100280010302c4050420102a0111903041c10801c12400c00e80724103502404244400f24455446c010300001d01e40300b038200842c400c030f1b07070a5410010407041e03840580458402c0b40070300040c641d003c902800280112049021288425101e1041c4000c1650000b050524240404090b0f56280c4001264205850a25039100402202c00b840810708205005082c205148208001e1144030808200310080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 469429460 1250 469428210 469428217
    0x1c020318010608010e010b040204210516060e1f0516020f03071e0812041503090b090304060f0516020103090f0816150515040203100b1308010c080c0d0f02 68
    0x40d000024007090382d03110303c0365000b014038181d0700c056942802c07980081e610b840d200303c0f004d03509040c403c0710101100c444010340c080399880703044030207100d0200d04180a82020b54100000c0c60190380705164a407048040c40f808040003031903642c48245803981220845c1d0800140c0b5001a440d01401c44c03584541d0000425520120a0403030309030242c0d86010598500100319444c0680c00495041001ca03a81e4040707941c0c80c000d028020303041c000c01303000c180207860600d040402c0b0b4032090f01e030200310317464151541c1215410a84030106203030703c0001e040040540100400c0005500c0d81000c81c146240300000603550021580002e04042c0c3d11701c8018100441400d07156a9030303800200b06c0c0c0e240c0400c02030300341321500f90b00025544d2040100040c03d40c00c080340201031180d07000d404400e584403180801e001c00b9400180802c41044440d24003c560840264050f01006441410301401076140c103d401c0d0840744840603641c2040046c4007045044841d01c4100c5229822601d0006051000520000300130301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 469430710 1250 469429460 469429501
    0x4140f06131109010305090307030c03120603201207030209151f0305070e0a14120717010f060501230a050f0304080a090918080d0e011e0506061c0203 66
    0x18507050040000800300300280a800c03c003a02c041001c0d84a0003100d642d24003405030020005222203004030002840b580002d8800c41040c0300108415480390340e0048512070840d0307801c80c1f9146001c4040d104c0e02e810140501443c60350b01c0a401071a08640208514040082c81850440c410160000c065112a0703038031030a1454584113010384800f02000280601800c0c0d650170f0009d03800000c0040700d403412003030800440e42014811048141030074240456032030301c00c0c1442c00c98090000700044000d488024440c0e0003031404000900710503042d2928085607000c1c0c00490403c60000c500c24a07030b60422440c50303c03910609550f1a110326100c882100c080c030802d405811003040c04000c1c04200314012001d08559485515091029034469010b40c0494038a0b4501c0d2010300e01c41406a0b02144041006164807001b0307078000f040e0601e00401d034500b0b440304180f0010b100344481240000d03146039440380c0c98001d4000c40d140c03071400d0034075007a040036404100001d00d6003e5000002c280d0b0300e01003100c0d940204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 469431960 1250 469430710 469430749
    0x5060c160b06030f0d02071a030c0d0b0a050307060e0123090603090703120816020d020c060702010201060e010b04031a13060209030109170a03060f0b0a032c03040302010e04140f06 79
    0x245e0720303002500c481ca80d2052011107851520407054070312004080c0c03032003110090403840c00c0a100d02652405002c1d01541150015103114010600b0b880a01411004d81855100e41203010100400100b0040c07030395001030f0001901d0f000103001d01c526042191028001260220388a0310b6502d08581418801e500c018250042c41c6045500742e40c00014043c8100703510300080500c1004c0ca44c1c1a82c443c07001c8101d41005070481d101308035441c40c00c2c0d0301514441e40180700000740191100e6203180d4820081e003000e0415400817408108015800210403040340111800006d5030620048060850f209800010203a0b030b008070b007c0f0344544003503201c8203c46800008442074040060a078a00e254018502d210019040c1380d804100a40f01c111b40e801190f140010082c80c14030080002c030000d01201c008003e8444001c0c1c409840300c502c00b80ba07105000741e540c000c0c568607486c610001d408903a0140c03990b070282c2c1c10211600520703402c030003d1543c0000f001480d08951750310300c0d00090060320840741c40c5840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 469433210 1250 469431960 469431973
    0x914090403170702240403090b16080412060b060403080d1107050d1205060307030b040611161a01090b091501020106052205010608280605041805060c160b06030f 71
    0x10268005400c5d10210351500d0014914140f24403103aa402500325030141c081440d090080061112190091840745011900d070250f82480b69140c2c2c68a40c010341c05123031a40e10704913802c010b0008511441e502a0021919180381620356551015a4018581520300c190b1340d9092111541c2c03540c208855980307500005079013072580042c201408820180e01460506407602d00055020b0400281c0001502d80004030700000d540c1d5555100040d22074005103c055407410b1003100055a48090244c0303c0c03510a20b0800445d40c0708a90710076208074142c4c030441095062281c54412500c6a01c00307943c1041c15004241e10000d29403005070b01402ca29441180c0010030394a404444030741050183e20b846400310420700140e640c2d01001c40e00d4050513500141c1035884200b070324540d010024181a035850083c41c0216401d550789000504940c002c4181c00782d410243c22003841044014400f02e903104003c904004d0030044500d189403c0c0c04400c5030020925445900410901d980c01c00c0100010200385040b20310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 469434460 1250 469433210 469433221
    0x50703032a09080609120310080703030503040b0912030403032a09090b03030705060726010e01081507091203020c060403060e07060c050d0c020d02100e010f091409040317 75
    0x1030400074851110001040300b14045089580804c1c2a030061070018014441c0c49622030a4203416800a4401d18010000c2800000c0f0810180500b0000f14000d455441c0c90b86081d05050014242c01000c00c8850b40107101e40240201c2410140c0e5001500352a001a004005a070710046103114401c44083d00c980202481103a40e500400301020341c1c040420520580e0406000d050b507a008100c4010101d0704601c0010300e0261040200484491150302000c2c1d02071068141200100d0b400c0c3c00c94012141484014411224100500d00001200034600c0c2443c4c030309000c0c0100322081600406000290704450744040c10b00c00c1005601e46040146a140c2c0ca80c1e0b2854501c005240d00c005068060043c2940040d40a001d2003400981603041000b130000048614402c450210005000b2a44649114040405030f2030369600d05820700e070103840c0c20080d40b180500161440b121000341508101c3e0380c101c14444140c54604100c0c05481c143d0b070309800c40c0c81c0c500d03041c3d600e480182020040010002c04001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 469435710 1250 469434460 469434521
    0x109051506030c01020102090901060503041a090307060e190b0c1b0705010f1b08091c0609020306010b0c03040b0903011b050409112107020f0d0305010e0903071205070303 75
    0x18080d9404600b10f41c2c0c250b414400580c00d038081c500400d540b08401c0001042010f020b80b00540d4014400c010324240c802d0800c010b10340e00081030b83e0700072250f400410000c0c200b00d032034415090f041b0402002070509041100030a24402041400100b09640080120706c0341e00c0e49005450004a091814910b82e64120307100d180d50794190300c54180021a1900c1c40c014842c05144011104540b10740c1c03032041b01a0031340300c003d03c51788410f00300703030f0080554092842031310100d25004500a203c2d01001c549020b4a0040524000f0107030071040694030100300ca940c0c0070000108a904413400140820340b58039103440000c2c0140003400ca107545510701409400c0c20303207500c00010000c1d5090ba41041002001c0c0708001c49417030240c0b0800400300c4081c0011035520180c0500899800701d0640f04907441340b1000c400c0f0700c2c208842401030001003502c890061200545020300d01c1c1e40136a0000c011414a01e6036140c4560403d0400040028808005407910500d4425041142c80181d50100e5680965540e00c516 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 469436960 1250 469435710 469435753
    0x130206161104150f2c04060b0a0b030c0d0f090b0108030301060318020a051201060918060b040b06160c050901141002011a15210f070203030423010905 66
    0xd01c51843c1204034042d0101d80ca0710603082c0c506681200b015241406600e0782840e2491182141c04540013003000030414045150314416407281c003021603040c0d400403d00c80c0d52402600700b0500200c091081100501d040001d903002d036080c0400100b41000741c0b0140c1e00051041040c041d1928442d000046a81c910000c002e5040300d00f6035504100c0d0002c00d084403000c600b4021002948000c450500700220b15001812442c240740b0480002002c9607140108000c030b403054030024107910441e01810042c080d0610800703e03c800b080e1400d0100160305c2e800030356107110b040340a170005002c2a03c04401d01c1000809130001d0b02d409094440b042d61601402d03103d0700c81c018042c03032007010680d080c3d0640c1403042c014841c80d2025614102070b11190758041144245031003004100408042c40001c2c4502e00c181011602c244a05141c41c03442e04185041010a4200410040c1554000c1080c400003690324005c44480c140c038041542a80d0040c0c100d42405400c400402808500c1141e814000200340c05004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 469438210 1250 469436960 469436993
    0x2b0203071106040804030f060e1e07081b041e050c1207020d080109020c030906040b03011a0711041e051806060406030c0b070204090b01090603020f04050405030313020616 75
    0x3075040416414072595038859040314000c0c00d80e081800200000b03041038181e2241d00b0302c2140007140844001d00c0c400d143c005960340c040040500201c050113003400c01c3c40104003030b00e4004040d2104071510f182103c2c03524851185d0310300841d69520081c01c0081104039460768124400c000f4410f6041080e011945600007903000981e80d4215408200401d000184c41c204404040d225000750381e281c00c040400a41054081c0403d46c002000042980d07a501c00c01400540f8000300301ea500da506190801d803914000b00c1c0c48074442c0c9030401c240408680c843d10a42c801050403200806d42e40b03402c2c0302e8100301d050032003420400f02c1d00f0131050009c195140b5940001e2828501c0841b81603a680000f00800c1d40c25900c0701800000380300ca810300500c061000109140d50000c1c10128060a0a503504000440264000302696035191018421840d02c42202d1020351b20455042c4194141619110b890307100c00740c102c03804001c1c801110300c11502c610054451709007510103444145040d038100250403080c401031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 469439460 1250 469438210 469438217
    0xc06180a0c062a0b04020d0203070803160c0e09070314150a0c0e040b1e060c0a050f01060501020a0209130201090b0a050a270303050f0d020415110a030f052b020307 72
    0x12004083c0ea0b0149075240615040b84504000f601c490b020701030f4544601c04141c0e01400742c0b980c04a144002000100049102c0c054403000c0d40026003002d054921041c1c110b03001219a10701440244400000c1e441c1c1503d4210040c030b0104504400c0c200c1c07078154219800c0c62150300490803c540c1c82c144d64051850340f41c0b951250403214105500304011520354071189584003203800094045072142c00480210014080c00f181e00c0c2c2003100241b6898110030f000102c44951092400030f1500200f8011400205000c1c002040302c108141c0c0000c20494006254150882c9070b0504d4100f0f685c480c860040c018601c02d0300c001d94a01d100b84000f00b0503800804039a004ca10010012641c00402408200754001c1d0340d100140545d0031590121900c1c0d001410040582e4414400241a90058070040000300043c443d108109011004003030311907044c0c0740036405907403c40b200d600f01081d04114401e800c1070442c5002c0350354009145a66290f200809001207240a0020101c8200b004550045003e94000e88 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 469440710 1250 469439460 469439507
    0x1003270210030507050f0a0c050f01050108070f081507300606080934151707020c01050c030706020f040e090307111005040806040f02040f020c06180a0c06 68
    0x54094043d20000c2e12900009042006000d03902801c3c040900000074040c90030703400d00c88441d29214a0b10300c0e0709071001145c0e55107400401040c1000c10904d00100588802e0030b0480345403a00e6240c84012a95020945000d03c0c000552418440c5c0c00c55040301e24490f42c040e560b64004945078a1003440150414542e03403900d60702044450042e007a4030b102d0b41124000b0605551080403d0f083c1c42852a00d6082c00201c130100d050030440416603210142c01240d03600381264540d024020150010304840ca14001502d0080c0906140c0c04244445490002c1c24480e5807000360100091461243d404041d060714400309190135503528803401803044850b000000c12440d11955001da440b07105a90000305048007101c150382d61810010004000203003070f4200142060b658070009803c1000484007242d07106800c070011b1085103081d1041d0768a0216001c800c45c108401d0f00c008541d5038030098240030203000300d10610901c1100401c00c9001155003c40f1103c08a41d8414016120b10341000500742c1c2c908050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 469441960 1250 469440710 469440739
    0x201060b090a12080f0315030601120305071211010204090506030d030615030515090108010203040303110a17042109061202090a030b1305010e0f070e01060203040510032702 76
    0x44007503494070000145551015441c0540715005811000c90072598114144400c5006100d0b40707019620502545603803000c103200c150101420103005801400492241840c4940030031342c0f060541d921183d0165201c842c14050744000c0e07441b21031314808029698000a030200714000c558100c18001c01c426001c0f02c1c110403441c101034013522110f0047d10030b805a02807a40c3e04652080e00019003084410900c0c1c251841500040f6054003c05d8001010607034002040c0320805034588102d076080f1200300b42046c101147c18038000d0400204480820754003142d4000f050074000c41c1c3d00084d204002d50701d15006000a404409000591184550000b05404218408030201c90307008540100100600c0380303480504640d43d8a030304070f00140c2000030003000c904000c0000382c424881c1100c1c00e03040d20001c000b4200380c50109445c0c002c29800020310700c00c03407000411005130008240c40a8403401c40b041890010b03000001c40003041c1b80e400320440071171842c104060b0102d0310403082220380c2c025a10b04d03a440380e42 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 469443210 1250 469441960 469441979
    0x2808060702030703120b10080115140405010c06020d02070506060a09060807090f0b030a03030b040609020c0a030e030a0f0b04140319030c1412060f1f0c061b020a03020106 75
    0x12910000503820801a4000103441040504000c200179040000c02414900101d14215503040c802008500d001d80103001d0056034001045103c1c6041c5000401510400c62403100d50266104440c1840b14201194040042a8040d18810003151a00b107403101c040d0f0400b96645c40058520300c0c0100e51107080400c040580d80290400e542d0000001d201441c58250340b04020b08450050086103980d5000e4031501d0ba405010716400c60f406650003042820080f0100f00460307415a01100352288100103a0409400101d00b0305c10440d05400d04182001082000c03c0c01c04d03000d401c0c010200101c480521040210040b5402e01560003106100c01c11075883c45000d503a44110002c4031460480000170f4031410307100e078201940e1080c291810348484460b0800743e540135000314040104801c1c500d07041249e182000054002058011900c2140755524540560541041a6022410041c014802170f0a0003000d0300410040410700410030001c1d00003410007500d17030408800450042d406c01c40c00140b903403103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 469444460 1250 469443210 469443223
    0x1704032306070f05040512010b0307151e0504050a09061a072a09020c0a02120601231903060f0b010918150e1e06030a0b0c0c0c2808 58
    0x10340041405449541c070030b40700888102c00c40000c01c602000701080d103446001c03e212030f481e01c800011540c0d6050000b0542001f078950414140d1502810341c070408203038049480004180660505180d805582400b00c9040c4502c0e04459003200c0002d40c002540232407a40500112240c802d140311a8415007410341041e4803078590043e110481144030b00486000c2d0b1001e505d1010300d040e02080200d81d0b68480102640c0089011103025000b8150040660401c48080d81a10404001821300c40d8104038200266091402c1c0a41c8407081000c601c8486803140c090300c3c200780c41c1054440c42c2095503403500c08090401ca014040c01d0504040c440303140c950059141000b0f0b034409501070412007500d00ca044000b04001003c0e50400c00f006480041c48003c0400d400e4042c014070388454075015000c0300082c450010107809070b400f83e44101544d0022900401c1050f401100c1c035100c603079407010004c800c5850319a0503500b0583c006105446100c020f05a03080c80c6c8054845c0000030300c42290380c2c581076600e840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 469445710 1250 469444460 469444523
    0x308120103120518010e0102100516090b0408070e0408090a0b0d0f09031409060904060806060306010b0c1209030c030d0908010b0619030b18070305101211060307020a170403 76
    0x6444c00302048158096480140703000018030441e601c03d0700c0803190b0004d17a001990007600d40d240b940c3c001d4002d0740d8846028005058115415880d0a140c0b4084982d114098072a4140f12510b80d030200c1d0400c41c195017160002800200070041080c0ca0b01c0420b0310642c007038219951550b1070001c000d024045540520000e29800d40c9808041c02103014609050758064154558414004c00c960903c4d0754131449501c02818440d00100103d1400c4001d1501d17040c0b06030043d9044090600a02c1c241c400001107160810041800294580e000000400d280c001031034100307a85802154014090154400a40022200c0380c8009000d014070810500041340b0800d0001240340301c1004180203114040d0700203581da04805000d600e410b40006d00c160801c803030251091000203433a141481440d060071041c5201401082008100c8140c60703a80700348076001d145048500500c800310000c0d51142c0203114000d0741c4c03500002e0700003020580d0111841154000d0008032410100100200340c404180501c241c43d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 469446960 1250 469445710 469445737
    0xe0f07030f140a15080613022d10050c0d020105070f092d030b0c0703090906152a060204080f060105060f09030c061207080105220f0603081201031205 66
    0x2511160302400281030203518810342c0c020314401c00140600200310300b5101d102506031f11244101c81d03204102c06540c4100042045242c11290f81130032412000b18094a4481112159103500740c5500960742401100c04240c41030181c000b14110154040d0850381c410807250361540141c1d907040c82d0640e4001c182c0c0c000c00c1c001c0c0402010080884d045075444060304010a00980300590345c0e179455100020f011100e0950581010640008158100c00f05a02500d042802801200e045c40b01b107042e806440f45856080060b800c9103400114401000484040c0b0700380122107900d0514200100a075009114014140c03240c0c0e0a8500400004102079060300c100500705d40c03521600004990039504054500c50b8580501c0341040c0d00b07651007400038050b940010650200324a45410060104041688041e004500b000e4a19030201d202a060440c48002d692000030704407141901280204050380004015080009032a885080c5d88840e96048a1285144c1c806007a01c00000b15410f0207010710070440da = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 469448210 1250 469446960 469447001
    0x4260f0c060904110703021b04060b0913060305060108160e010b040510090902280c0b06240a080f0129071b0306020301090b09060303120403090e0f07030f 68
    0x181d150000040894a4004001280083c0301e8558240103620048046001d42d1154142c3c01c100030004415905180b0304680c1000030074030741402c0304294452054042d100302d05240c568003c420b420382c0100c000d107421a007200e9103036071283c1d0100e0380c3e0b5105410002842c00000360020f01d8421888403181070350321190003942440e10b80810b0018422503442c079501406030449000c210b400151016040300c81c0803140c0d000e05200d045c001d2a411040c61441c2c1001c01c0382188241010804424600d0341081050b103003c21459010707041c00d003034850010901d55003080001031407040e190780001c0e0240158802d0030702030b0850340e8480d11010302d503000301820442c662280e0076900301c000a00004c0d040751400361901089407120813451440204190f0070849140e5404001403000941d18850280c410710280e0300e081c0306040220002c2e40e01c0c000d00b11040b00340025031700001d080601c01d001e07900041101c448101c9850402068090103404112003002c0000d14004031101c680f40113024160381c10711146100c144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 469449460 1250 469448210 469448233
    0xa08072901261b01021005190b0f0d03080907050a083301051e030d02101107030c14122701050a0f080709050d080405100504180905010f0204260f 64
    0x101d1080208904d05500401012031030401190260a108000480f0400301c0f2043c0c0c4004402103586800750580109461110410a0780701d1390141c0910f0b0390181081e10749940e9080d603445c50071525400c038682001c0e0901000420110000310501605a5184002e01041c61000207440100c4151225800e00c074024004012070f06001d02c81030910784000c034008003840c4819003c05e01d4004041c0201e0016804001d10440000451284403140c00b0020062841d2440588000705481b04070301c4050560b08002c401c0b01c0105074100311f9032600f02541910940c98140c03607441e880b44e001e410100b00301d45040d5089a001c0c1584260101d46c03281001c3e0716001c410352568401107480ba40010b10b40828048800702c0071a480d03850911000d01540314488043d6224141424040d42c800004181c0c014000140000e2000000c20b0102000301c10340100000f504940390700b0498050704002c0e041504e01480041e0110f40c505000108152440b01a420030100f841140c0c922551141c4170005968aa00104208813 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 469450710 1250 469449460 469449493
    0x91802030c030a180f0516170c04022d12010e040b1302030705130c030f060302010c0f0303200406020d1106060103091103070602150c0c0a0807290126 66
    0x40503440400b03210081c0c40c0d22980e40710070031700340e11100745d8803079000300e09031030302c4c1f11525681c000945600c0c1810050b0710a165000703662560072040f0103101300d8010903501c0031201012074900800290500080c007803c410300400b2266880381044422140c031200000c11b041d018002058081d0703500c40201c440903551851074030000c2071080070480c0e040c01807110006680e41e8032a80310300f241c095550001200c140000d0041c0480300150724400c81c2500b44401080541e800081c19900140c01840440384800203103421401031040d00c802c03d0b50310384c002c01c008100d030301a1005001903d885400310b80e004140c2d41010303160010202010a0b640e230005000644651090308800c000700e208070f4005008400d0b110009083c10081e8000c080140d200580c0050040744c4201c02542214480d00040d103000c0400704065100e44401c0d9010b070800c0e034000f401908100c1142646a1540034040e00108880c020980040301c9410078401d100c4513035910304c41815002014084084c89078600d4008111701d05080310002d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 469451960 1250 469450710 469450721
    0x2070210020f0712210e040c0e030a12090803041d06092701020f0309010207061103011802091201020703030501180b0913050c120604020112020304080306240703091802030c030a 78
    0x715410034080300c0501d22004442c45ca00280c48043e00c8450318100c0440078482143d5a00c49281d0070081c00c01c840c00e1694401251000e5260b03000340c3c3d0703401950543c89058035030400950140040340710011f000241001d0562038250b50155203240120700791505010040659402c0d60a06044555003480c1080040e044100c920a800301c0741c009402d101307103603101081581080320a61540d9400181820802080748204c2a050700100001d60665040040c201c2c891002003a04481d000d0380016007000300e5550b6540c640a030701c500402559203078540c1c94010007500c405e118000c0c03030f441c80e08000f000718580d0b030140b2100c1000140030b002d100c1c1d075528518115064a803c00791050b0041c4640c002050301c5201c0d82100601112008240c1410a0320004100c003031555800d01180d4414018480050a007600302c0b6080a000c0701c0a406d2507800180c000c0c04c5520301d0106040d050303070010f03903803003050f03044985c0004a40020000b07050900c0b682405000340d20085520030084401040007c1c0d140b644c2d80d112 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 469453210 1250 469451960 469451963
    0x152806180b0102010e0a0b06030c030d0f08040204090b0a0e391302030f10140913140303100e010801060e0403051c060902031501090e15010210060902070210020f0712 73
    0x214000d07102036950350a002da100b46c1600c41039404410080b103414104215800818143c004099400d120800200610002c4c4541010006910082000d65079160041000a07030406000c07005401c0c8a07800307000030f003090b200b44819405202c1c2c054102450903000581280100380303109216040700e0840c0381690301081c02e096800350b80641c510394641c2481c03014500c940c200105001c0750b810a4440d0509000281d4810310b460a1a40501961500e40c03e000641025020214505000e094a4000c0c1490401b050101240c80b011081240f48000111240c0c00c40340301d81c284106a9803030303130320717850070703a43d640c00368059104800000ca00082d204000900640c0344407002901503002001943c015285503600070305183d43c010051001d072451031030529680711000d082098905161440d011907016005082c0182086c6904060b41750b41d00910030140e012501c1401045442e8450389084001c1d00b1900d81a400317800e00f40d0f61095414000955500d0500080d002440c54900d010500d009070a8919070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 469454460 1250 469453210 469453213
    0x2116052b030903140a05120403181a0f0f0702090c0310050d2102190606060e09060d02130b0a0e040b090f190201030e01050907090e12160302152806180b0102 69
    0x1f900e5001c100448a1500a80c800d56613000344071343c003200f050507111040d000141c10381000501021809a1030040740c21214440c1ca4654031020071141402d0382d030250f01b2000e50818800c1d820401c43c0b40303620b80110310400450005105454650341400301c090b408060080801c88540d4500022405582c0746454204451040310407005403000d03040c01c0c0c200110000c90b0742e103499500500846400031100c200141064408114600e00b51000584083d08d8000107400b4103040c912000180b081500103525900014021000c0a691102e202900744021101034070786918007004514110004502c2102600c1c6400c01000360002500040001c003940b0031049060556800050160000a018891248004d0740103000102c2c5002808001e444459554402c0d541002c0c030400034100301d000594030702501044000c1e0b40c004403480d05903c0d0415109081503e148260200540d181c1f030036210400807100703140c1200420080c40c0e104002d41c1ca1a01400000651619544400c402c0d9a0b100c040c12010510 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 469455710 1250 469454460 469454467
    0x61715090a0c06020f0c040209060a080a0b060c1005070c020904060e030714011a0f0102150604091a010815072a080f04090e2116052b030903140a05 65
    0x1038410703003081030651003c0050780202c90080d24001e403c1c8003180340e00c0002d81d4194a400c40b03060004000780701c1ea0042c0424080d01138040380001d03000f42c1c800c10201e640944001d036290000c1d001c1d190348880f00000d640000d070901001913036183c8500c42e00701c102c90f406029015180c80ba036881001400e201d01a108462009201000108640780b1001190115520001400160700c11109490300407003070340707a4020488104c0c52120b42e42d0001d0007060301d0310070200c1711000c0d0703c4160028020f41105607000d0103013140705e5032644c0303110740d4602d00354122005030044890040c0c80450f85946c440c01182e500713010440e040741d15881004a07002c005801140c0955241807a003139582c444099030420027411080800106083c4900c0603107120302a0300c103183e0002000c0c800854101030440054282c0440780c403180c0814000c8036803d181c819014140d0f0302c0720580300c00800001c0491304071103812068000b42d031810810750401c0750180c4540002c0703036055501d400d60091041142c001c5a40f003101c080c000c108041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 469456960 1250 469455710 469455713
    0x4030c12060f02030403030209010206060108190e010902030f060712050f06010c140d0305070e0916030905071a03060f09040f0803220c0f0e01151809090c050301061715090a 76
    0x83c4000d40c800e40c40394900580751404400024034101b4001d10950500ca401018481f58030a040d80c1e05950340001c480214981e0501443c141c094004040000e425105584144d11000004100c4912442859840071060240d030105030040d00d9058600041e540100b5010031515441415040b5840340101480403481a03d012080e1500c010504000d0009503154180640c8580c0961007040109040b0341e00d1071942071019601083c0c1c0b81c2e10801c441855075442c12441000380605c0044000c044901c2205603105a40c200380246610460702640303c1c80701c01c80c9800b29458002e034100d00903a000070034103d0029040c0d071240041c8d400039090002e401624040311142d0701c020840c090580b4818080ba07400b540c5000402d66108900b600300d441c0e1010400010f00c0341c01c0300c0340021000c201c1300e8a00b24200e08001c441c1c2c0300094545403c0300c451141401b4006051200e001400c50440d0b070190001c00c00140ea40854101242c8103800700586600084d035050345a1070b07501c5189400c100c00c03074140c41120b05103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 469458210 1250 469456960 469456991
    0xd35040b040e040c0b21060411220b0c030d0606050a0806040c09080a030903060c080403021906091505070e01050a0e012006090f0601060905010804060e01060b1b0c03010204030c1206 80
    0xb2010b030560100448001503a446c0a030444415202440605104550100d282c02a07001c01c01c5a05100d06521900b00d4601b280c5070018000e0040c0355541d4000c031800b82c0e84079030140001c01a00f0703040800c0055114400d034101c0d480102585d036501d1403612800304220150071000600003c00040c070380003191001c014095020518030a407544074050f851450082d0a44a021303410000784042c503410800031036008a203240b4039040d074020400c800c18062405e00005c0c1400c03200640146207007400c21300d13a00d003554099401907616480b4440800c5030400116081d2003040e51402c0091290030701d94950f940500084c080144007026011024044445010700e003400c00c0b98209425441140c2d030252803401032005902401c00e52400040142c01c20001030000a0090401070103940c5e2204541d036004420b500c850301400344108900d58070081e18030042c1b08403050305a000d030240240420414189014821901225400300d00c944140f0315110700070305242803960382036405035218101d03002024032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 469459460 1250 469458210 469458217
    0xf010f020d0501050d050a080f12010e042a05010c020315040602030106120605360c040f08060f010b0901051c1b110604060b0d35040b040e040c0b 64
    0x100050058076041c0d025108002c1e00d806a0000d4003915015060001059010450034210303030f008010290360792220191b11049110f0301105400841c00500003080e40748003e10524040c60085145105a040f1000301d01141040d9140366a41d40001da0020010f5501134844140d441f40000e0a41e80740000c0c042e002c2461780411141152803950010050201d0303138110380c0c10700160b031940008000b101e091801141404405448003d800184104104200c1d0354400085140240500500003d420b01c289481c4080e081030058180003036202d800450040c200048191040d41a200b26501992030700e003511410740d200305070182c108203080080f0b04091544812051070002925000a220341004031030192100c100c07406181027080c070381070b0700700540000648281c010b5000800043c0c06207083c800640031680f04140104801a0702c00b84404849001c600c00c480e400d0b0003800c0402c0007842d4801039846129034000c0021126060109010780c600e01d03402c240c0c0c024403500e4865103044d00d400c2151010741 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 469460710 1250 469459460 469459481
    0x405060607061a2b0201050d0207020d060e0d05090a17030f0c06092a041a0d0605060906040501080703080a09050d06021806090a03020603062803061a09180f01 70
    0xb14140422410443d000032401c2c1c0c1004d0111400100c0e01c0e02803000340c68403000185c100003000c1400c403001d0b801c0341c6c1160b00c80c035402013106809800c5803811001504010046010a008462281c5115030103117045855039000245024441d030b050003001c00c41803141e400962224031003400f4200e40b40c44000000c020700000c071001001d1901d8400181850405030511030340013401151002140c074000e00a2500d21140222000304800b19003c3c10311840c0c5001c0105503900070484d41c803c0d018081e043e44028000c4000307543c400815600c04081c0402e031a028420801140c3c04010300b0000700b0201c901422102c0d41c94034101d034a6503074520002d002d0b03c0340d0010070340380c0c1e0350300142255a41c0c7c0f00b01c0c0505941d4400742c945a09100c00f1000240791840c20788006805a000000080c100d641e40840130040c8040134541d1950483c0307000b0f004001418207010848490345400340080c42065903a500c8848000000d064400c190359065001d84501e40c00d5540d40c40728402c4800c81b9964510030700942081f032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 469461960 1250 469460710 469460741
    0x10c051905070f08030712080402040e01051e161e0c0204050c2208030a111606050903070608040f0f0204090b0c0a140f0f090a0f0816060e0906040506060706 69
    0x41c1c204501030f4080801a880920f495004002c90320000d4041c22150b4540001418a40415600c0c0d00120700507000d558202c040a5181c10104540c045100107400000d0041400d500003079642c070510a001e01c00400c00480c049000c003002070326215407600f443c504c0b022282c50550010b0f0043d6000c603050702c0050f2114600443d010481001d0202d448040c10322001c010480c035290180b034030803403684034030401c0041400c00541d00d80c0190780d003204000c040c0040d01411a1000b00640e282c100900b16080209400d102c1d000c0c1020000303240d8418001c2c5805590840e0001d0200003a964560180d40b0012104982040e03e030404036000c154148040d0340708420007088650740710584240101f04442c4003180c0c40880b101031107001401c21030001a83e2141002001030f6030b44000d000000380340ea44c40f41d0701000c4010700560021070042004107003880c01e00314080030341113455191034040e00c03030055104c1c1c182d401c0300180f4001134192810790059500440c000d000b0501c0c002c0644c4800c81501e01c03500404060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 469463210 1250 469461960 469461973
    0xd060f0506120c100f020718050610050a080a1508011b021903020307140c1203040e07050a230f0708090a080c03060c18120a0b010e15010c051905 64
    0xa0700b04040c108800b5101000a007881e2402c410001c0c079002c1c3c3d01c42498041150451103c08003070b000b00080c0300074021301c200303821240d1400545c076405040100d5500b4010140712a0128030540201c0c207441d002c1c4020b441b514219591550980002c108100e41c54400204002000600e41828411806500c02940401e204d5030140000070340f510051f1034615030b01415054813403010903401b0082d00c0311290721103080244400703071200451920b000405040d60086144205090515002008108560440a641d01169180003003039580f801fa14150b040441c80142d0002d03034441c09a0907a8600e0115038640905022200f400c1c51240e4108440c00c03a4070100c001103010541c9030001c072442c0140b103000006c04030340b90b01c440801c0d103403407002d0100d0000ca40c010802844040300700c045403503418806441110042501c0b8207150b951031140d407003070f00c2e8010705a00102e0204651408544615000010070000d004048011500700c1c030500010b481ea405000d001f170040d005070401445289001d04000c102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 469464460 1250 469463210 469463221
    0x1e070f12061e0c111f05040203030706110318120306040207020312030a0e01110a0c030f26010320030705060a02010b0a090c081501020705010f05120106021c021b04020304020d060f05 80
    0x1d001c0b11415101982e000c1721000d90408031a80c801d03040b92140403400318280e01d4a2011a1442c09400c00080509080102c0a00c2059034813001c0d502c10743c0a039100030b1094851202c429150841205549143c500c1000050307a84e0900340c0003459040e1002d01101c07600c08ac850603ca00039041540c880040c907480f080c0d8850458800d003e8414040160241c1503d8118482000307040e00100c410300a00b03100030040124280d50044070115100c11400b021603a075007000043c0421008000d010840e107091040303060288100308070004c081410fa000d03000303000d0030f402c02e0100620b0790010011081150349036074441b5066181d03440190002c0076402404500c00340300050142c64404000e26412146018020895590f0ba0014465013120380a0030302c2c00310340c807032254125000d1180480c034025114072840005107a690025242e1101140b45032120080310243e0000c9842c1c00c031180702014000c1401401c00c3d498905a030066030428401881d00d100780802d0b03503070081075400c56415a03614603621401c125 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 469465710 1250 469464460 469464467
    0x50408011d071a16150507020a0203061906081002070203060f10050f0a170a12090602070b131208070605060109080a0b04030e121e070f12061e0c 64
    0x48200300012120300740500015415030303071100203100e2410030010030a064034103114440100d40c0009141040160340700014184032070030060745059400d4207890721001a81c0c1520114041c180154000c5c040c0601e0303122450304000d4030444c0d100c9501420794a078070008680d10300304071000480c1180040907031914030600405040c031400522144810341d82c0c104004240000404140c00e030380c01210141c200320b5121021031031010703007130700304c0a800c041e446040c821004000900c100c03409c2c4103022000c000c014030042145d5100e410320580001d03900025062151b8400840500b0010025101054800d5640c00b1105c0c1241006c14081d140d8000c002658000e00c181400780ea54072200a0078860034003460408040d681c1c032200c080160420070b01707001041c10903101308503513202c481c0d008140135900b907140b0701200e4640c6c62102d040410000ba442014070760b000c000ca04402160540f11440302c55601d094110089500501811202540d0395112401d079650f800c0c03102c401c90720358404001144071022a028 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 469466960 1250 469465710 469465721
    0x151008010e0f06090109090303020d14190204140f0312191e1e0207030b0a020a030b04150e280c02160302030c040b040f060b0a1215030807020d0c0605040801 69
    0xb48a450400401400751258150076044846810000601c1d0505080880003030003030030002008142400309040903806201e00c2640980f1708081c500380c100d9007070030581e0100c0c411403041000c01103200001104502e40391070704007a201000340a990000f4400c062280c800e41c00341c07190b440200c80380b0f030300441318690198600d40071030b08000881c681182c130034502900550881c2c0e030380103107030340510556104948240a484019035100006901c2401d0850172000a900000000380010746082e40408041c98940104071b4151440204403548034145411100007000c010441444072660380a1001d81072003841d016210100e0304500058003c910200082c00d180078400300c499001034880c010700c0581d5010409a5280b03900701c07000588030000d040881c0c00380c000107880407440c5291400005005804d0801411b0080099580d80c0d03003884414020000c49a0001c1d022200d0000359205000060885000b44074280c0002c1440c002c40100740e503065401d04440d000000007810200302000300480c00d0051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 469468210 1250 469466960 469466971
    0xb0a03051002070b090604111315060504090b041404021903050d050405040c0806030d03050603120c07050103050f160e1219050607050a05030610141602010e150a08151008010e 77
    0x40c00c01410b150b01c2d4120381208c5441010b120317103411055803400d000264441c1e030003050001c1c101c81b8003980c1c41c07101404a4210340700b002542c030304182200d00d0615040c491443e03088280258491151a1a002c0c0075100c460040e400c0044070320340d080030011802c104245030307003200b85640d69a561402c0100f40310a82c0d006d400e440f814440c10600744030042e900401e008040c0121b07071038000b6a581e1444002840d0901c0035103d10540c01000600d180810008202c44059031b4080c2c03018011030b101c0c8403c60009034805c403510b03412005151320340c60100f0f101e0b41101d41d98580050200100c000d0100c081c5081c40c0b1f60740e40341044590907070f01c61010410b0500680303900c4076071810f0160902440070805080c030301c801468030b44120041c1840504442c000c10525181140380d2550030307111050b050740300e9008400103401364082482c0c2203420a1a20b443c800ba1040d00a00d80440c1c0d050025000040d1174000c0058156036042c51004100756040e220b03044016000307103143d501d20099514015600300c0b1403d01a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 469469460 1250 469468210 469468213
    0xf110a050a08031207021c170105010503041a0c121812160b1e090f0f03070f0f150e0304052706060304030525060b03010902090a0b0a03051002070b09 66
    0x2040201c0040030041d40d0b00166440f001c4501c030b9840005c1241401c00c900d0012501500c0c1013040e41c40290b2003810540014800c07100201c550340c82d003005540034002183c0052180b001d600c4031000140c1070442c0780350040d0f61045000d0a00e85201c0307200540500440d08140e1120312204900039203482000042c0040c0b0640381c20700c1c9060440e824116400a0054024081c400100d02054a46140d28480c650010038911840244e051152803140c0fa403104104405040c4580454070307002c5030000c001c03030350000da01200000d075441e00c0750750b041001c40301802c068400c00411a00440a050b81703002d8104081259005075646030300307200030001403000c0203030b4520041801405003102220a0940a0341240c1c0032140c0b507480365124070b001c54461042000685900035500d00da810000940c0c0450710b2154460541800007070641024142211100b40029600401040c04244205401d03031140072074141c040c3c01c80d2207094481d00ea0074a00140040440d00041d400500d00342841070407141613803c40307800d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 469470710 1250 469469460 469469479
    0x120903020112090203120d020918071d1c063201090e030c010204120b090109120509060405090c030402090f04050307020105160614010602010e010b0d1401090f110a05 73
    0x100001c080562032400002c0c8203590f8820807041d0340d02040340c0c0d006006102c03000c540c0c405041419002a42003241618040c049007503d01990889401800c0d20600c90b554650400084105402d4043c202e071f10701c05034000b250604464075080b1510700000c410345c06610082500540c0100c0d010600080070a00c100c1124103420b40030b8003140552041d81100c0d40300c0300100d542003540148508603c20303040301504940c400100015143d0040c0c2041984c180910400501ca50710025820300780ea40151008040303ca0080310848894040c2c40907050103240940501d0070691a140482c40019080d40c0c06500c210b0003008010452a091701e9a551020003080c5803180341c200b80d91140e90f00e009003400241401004141c00044410342c003505c81d015900500144010310300404035604003107080c050400154203080d00c54034242c05c1401110540c100180c210400c10901d0b445520b000d199910b1800a00c1d5203520b80c00e008078101d410400d0405001d0410040a82d04100402007941501d5201a00450221 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 469471960 1250 469470710 469470713
    0x161401090f08070303020f041d060609030c011133090a33050a05070e0609030c0d060213080f1606050a0320031f050906060906070519030c120903 64
    0x2034407045a450352000589440720f59900d01500a40184048409400404034000490400140e501e1050042041d2454042d854400501c0150b00c100004c46800d9807060240c03452a510500120825108c68002d032049980700541a2414191030b02503220f811507201c0c00d11210040c543c0c1010b800194240040ca4084150f40d03829084c4001d0350041800246001e00d0400000f40d0070881050a03441110200024503281c20007400404051b00c50b0070000c0d0039031004007401e0410000710780c5543d000800410540b81410100308180749600c500f00c07171840c2c080c03000010480d0039981d01d401421080d0050421001c485084034600403038064441c00714041c1140800c80142c0001c11134441c10840e20740460b0350321162a8943c0004080c0f0a0508110000401c000e155140307092007074411b00c3c1004010741c1003036a44e0201b10004205407141035011408100c40d0440349829001040414411001e803001c05c00c0403100e00d0501003444006901242c259601041003200e01c0349200045081810007440c03887c1503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 469473210 1250 469471960 469471973
    0xc03010b030a1a0714121e0103050304120f02030a0f0213020708090f03251706091c02160b0d0e15010302100e030106090f060608160804031416140109 66
    0x10b28042d0340c00b20031058041521030384240603001d40d070100c5d40000c07640c61045c035505031400c03c01290b00209024020025440b42602640001d04aa03081002141020300b4000d85074207400380e4034000c40711890300642c40401030320706101203d502405880e445243d4005801030100b5881c0101188000034810070440303000540d18070a8642a440030307030305101c002d840100407a03d00011800c0060400740600d10921aa07001d03006040d0030755100c982080c2d11540d0009030143e581c081590461100d40041d401c01200c80480310301c007464106035104071011240c00b000c60b45410301c1746403c17641258030001801a1802d00a001d039000f040e00c07040080c05070208a03190345c0039200303044c040244100410f42d00541190311464100540e400001d008000d1180e59502c07920040112014040255003424030004907076000b410f0f00ca20480c490300700c0b49240403845004942c2180700030802c41c00d0000f9122004900742403500541021a04006009890404d6084c5030703a09908000040b81141c0c100304180001400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 469474460 1250 469473210 469473233
    0x1e030705010216060e0d0b040b09120403050723060a12050c1216020f01020c0307061802010507080313060612020429040509070504092001020114010e15040c020c03010b030a 76
    0xb030310324000b06607a2009000980301d004150024000b095010705201c18001c0327040a45024800038070460710741c0d88040880000c40e01030f5120280141d0400e420400000030070b5000d080e926204c00c1e10030750702d10102400151854101c00644170010f201c075503145590184a114003030300494270400660415910040f86210aa802000c90f1040040407511184080c000c000c140e4810590000079512562403243c0e070b6540340c1140d0019281141400424200400c04800700d4103455010f944152030f00392140c68501e602c2e400909060800310f9030070510404280c45110f00409014500c00b08000c0e01454010003003030701e85848113818449282102101414140c107000a40f0240541b8046540c1d40c40c0070781141000c00d59444980c2050500c0003240030012001540005600314460742c8041c0003100300120f0032100504110b8030300301e019200600c0f400003d1044203030310103601c04595241580d400c01003000d49103407000d800c0240c0d200a00e000441d02d028094101c91103c142c0007419800342644500d1001c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 469475710 1250 469474460 469474469
    0x15020d0c020303151e1e031c0e0604080c1005070f0b0a1a031f020405100c031103030c03130f2a060804080a0503041412041a0a020a06020a0c021e030705010216 70
    0x384180050f200780c04500080c1b8020200101911040700141030703d0140d03098645580760010300c024001d00b05503c0c02000b507406039445c10004280254000c0c1c00e210218120b00a51024000c051105c1d800203240095140c00c200d01c60500c0a0543c00d0070900c0c0d4050b11102c2d50000e031102010401a40c0a48001031208807000851105041440701c41840900034484c50f08031681000076014a488080c1d0072450b039586e000e01c00ea65465804419182c0a5140d010648214660310b10800100384024010152961081d0144502c020300100e9595100070103450a00f0501e5152022500c2403541545800110300804090900d0011440c043c2c0ea0250140f081d020710000380800840440c0c2030040c103040e90b60303044801d1000c840c09150540380000d6542c205101d0310307404030707520090120b00085020035220811000e07001050214003d64070315000e9000a14a01b0812418406160240e91130706280000d9691500406130b031848501c0906050440603000726040d036014100851031601605400011039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 469476960 1250 469475710 469475719
    0x20607080a0612112d0108061f02010b13060605041707030803010308090a050d0209070c060b03030409020d060e0f130203010f05040b0a0606090f0315020d0c020303151e 74
    0x1d035103000401004014580042d1900050000d00d90200003c0b55403159004908583c030241d0090070383c805118640b2094001d0020b80101040c100c1194012100d480d00031000600000501c3c004400440981200c8140c1c040180c1d1144840240d80c1450301410b1070280640c9824411582030040140c04c5110300d100d60f40c9428041c200c000c2e0b03a4042400042d018582c868819070392565a41008401307900241907a903c69404500001010316144101108141d03000c0c001c850b099840b49020344040d852500150740294a841c8240110395046c030081c07000e41004a801611481080c90780c1c422190150841c40c194200982032028040b42d0048840d13218016440c3c1d844090050300c08640988030000101e9010303030500080c4010810340c140e03042d126229401c000c104451765202c003221440320600c43d0b1402c0b0300341d1080a201140424070a006603104d5401c0140c90050090200405c80341d59102ca080160804028482e11007080424210140c904403202070321111800c0518100105007200207219 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 469478210 1250 469476960 469476977
    0xc0b07180501092303030403050d0f08010803094c021b0604260304062601050108151c050a0c080313150216080d0e090408041203120501090c0e010e01020607 69
    0x1551701002202e002d0356100c02500c581d24604000900710110302126000818403201c0081115540042980c13008640146401c400b1304402408404589486200744194480c0000c916000203103042d101e00c046080b040a0654003124000c002d0603d009801d003000707002d0340d044ea011800c0c0d031003405560646000000d03000c80044043c00c01c1183c048402c0c640f00040c0000310700040c1c081d422081801c480d00307030300c2081c490080f02c41903c2c0f100c4040901403280400e03121008590250311025203082520741c00b4207152580c02d5002079241a4902c80e840440c0c4c16449800d8140411031100381450017080c1d01401142040c4009a64642d607010074012100c3c0c03030141d03500c07140e9814800c10103102c1c1500c0f80c4401840b07207030300c0b050440e0f03d074000d062004c401301d00050380a0b129418012004c0d032203540c010300d12905107420042c0610004c10858815400c1000d020503211003c502442900d008000c80040021030a03a460b81c0074040001d022a1a81844090030203003c059801052095022856240507903a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 469479460 1250 469478210 469478279
    0x3060105061308070801050a0605103212070e0108090d031e090c0f060f090b0702030a0803161706090f0901021905030f010f1d04030c0b0718050109 65
    0x9602e240e118814522860000240e1a9010740c0914014804030200b401029220300a104040368040709080c0090246100007034422480d15130480c41101180c44e200c2a407041400c821a40c1d0469046045001020820b10440b00e4129000d115144400c0c01c0c500b04901e4600f80c800d494400620904041c19120304584c6000b0210895821203040901810041e070b08103400d00d0411741809016080f8201c800c0b0002241043c000c00e090042481156660755070f0714217110f000200f580003143c0413605445403c110b040000c1c5040c01540c882d01c44403000310b0000603a030304018200d2021001c0620174085400034403034151229240c1d0755220300c24140012264540c60005402442401c0007000703454001d440200a580d40080114003c008050700521244d07206c03406071030b03480e1852180c00481100001203101c0620100b00f851307402400b900f000500d01e28952541e42c074461045452000080046000150403c50502803070f0203000b007840e0840009040000451054820251520071030850f0021100c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 469480710 1250 469479460 469479487
    0x7060e01020a02100804061d030a03020c070b120f1003080f1e0a0c0c0e160c05011e0e06130503042d030311061302031b0f0a060809010b01020a020306010506 69
    0xc0b049a004d0002d19000510101c000c0c407150302940c04480d41c130304090000124a81307010019000060b400082d500e0403c007580142e00039400b00c0c031030045a00905034005903003ca200d001e00780ea003140b240224101d14045062104c5444020202d00c030303041c10501c02f480403641640c04d81c5c031b0340915584150754030790105007107000410b03602151038800c02c00002c4407001a40e0181d20625075510904c01c0c0302c900c07900c600002c11952000c03901402c103001c07a44505111513109606660b480d500030070000800440c0c0d4140c1c000003d0318620108002c50302e0780d600d01e4401408120059200585c1240c9640b27001055079031136101d20580c410b000c100c80144d440c07418080341e213800d18414411101c2e10351880c035550303180160108003401c0c1c020601d8040c0200182d00c1c0b02c0d20010941e00254000c002d40012032000804a0070341070060b0005400400f90482c10070651140c081c010041c19203601c0e04015071609040c0c80303007075480a020042c11034110480b4003006840000300641928401c443e0940c03101d46044850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 469481960 1250 469480710 469480723
    0x90301020c011d1b060a20070915060302160602030a14040b060103060f060504090c050d0c030905071d0402090c12040c030b1e0a0f150b0904050604090507060e0102 72
    0x1c0c2095442c0030140e03140f403000700c215040c1d4100e124054602005256800240d00018150701c50b4014a0801602072000c2c814600010b00004003500080c00113280a00c03c0c1c81d03c001e9400c0311045d03640e9000011495800c5504200042441d1324003540b51611305155104200f0200c04001c10a41d00800440c00703000890b005000c581580a00e00c000c1854123080140d01d6010039264280424648200410b00c1c8103283c40c08400d8800301e4a40a00c1c02d03140a10040c010489501d110741000002c1c0a412500c030f006000710781ca40c9516a40204205021703007813a0b1705010950b8050850301c2c40c08509a00e40802c0803d5650307000d50103c8140c0d00301e07941c4500791032062080326002c0c0403000000080000b00512030f9650401c0d82e014011140c47c55441a0f4a0781852000d031194054080780c900000308058115000003035000700c1040b000c5811075500c8825101c85005400000e15650701041c1c099180c1480c0c85143c1c1c0c044001c403018444604180c543c15201e0b01c0f280995000c0103110035040001d42d0082010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 469483210 1250 469481960 469481977
    0x110610081905010e12070c05030f06130f0b070519031b120624030b0904020f0d050f010e07060e0303160224030a020c0105070206090622080c060118020301150509030102 74
    0x6607424031502c4014418154406e41c000c030f0302c5050721540810107040000302e4a503882d003000000c1c60341e1303220700400f03802c544503c01d0101d0351025144144030002c2d0380c00c00424002d1130a40c64403501e03041428014000310010300d410300c0405180c0391450780c200c104100d03181072011050518902389100e0f42c000350b01030102e42e001412600e80036001c190350918070f0a02c10720b0592507035800300040c10211041101d10300080d240a5404035172501c00d1515072424011401d0981c0c03040d000c480720f0b40782c154856400c0d62840d88102465402c82c03d4200300b441d80010038003030098400c402a40c640200342009640080280c01c01034000c42d84081c0303001d1964046a41184a0b400d0b084440c4d80300d03d030a420303000280d072000c40c0e0341c852075080c8004290301f5800081d01c5030103030040001400e0f1960303490000469184480c141c2c00b8411400a0a100100722204001e142c03400700240500b0156040c07128070300e1004454020030606510410040000b030040019001c8184039a00d0092394440d03801c00002d0290181009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 469484460 1250 469483210 469483213
    0xf01030e01270203060a05010b1e120c0a02010b0f03060f06060409020412030909090c2108030f06100f050f030613021c151a03040201091203110610081905010e 70
    0x15407111140e407003a400c0c002c6100720115203855442c8000c100c02d07602d0a1140100c0f442c81405080c114a41503100610200c014901c5a41481001c10340c0b1481d0740c44c240c5a601400d507000038081c190390303428040c00e0418a0705890320490169090003003607543c1c81c02400c55064038491000306003903907110701c11500200031805081d5100d5850350202d190040c10104220082151006c001510011a0044080960300000d000ba03c00303240104000c4480c10050040501212511120000408607001f40d401810180e0801003d4601503090000100703000d003c1000b4004e0004d10340001c0c580c48801c03294202040c050007600c030340b2844007048001582c2c002510405002240440b0a44080403001083c0c2511080500030b100802c032400c000d00b1540e000d81d109407210814001d001c51550402541c2191061521186865484003a00907000da0060b085000508408034120303441c10420840b40c006251096040e00d041c58506425562551105610b40444c29400301d4420b20030203500081d0380701c40110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 469485710 1250 469484460 469484501
    0x20606190e0a060905010e15090a06090603080d1d070909020105090d0b070201060b09010504063606020d030615081b0307090515030105010f0c050c15030403120b0f01030e01 76
    0xc8062024146501481303c003d450200000303503c40058080c2405000d0700c40d081000300303160006000a07580000c1c1000c207101c2d100c0600180740503e84c443e0500850089103c241c413000c00303085420580c1c901007103000c4110f2480c00c844088000c0030501500720313200008009501c17540c0b440142c86a0282c4031070f0313943c8000400c00c218144002001e020344111266402004001c0c0c076400010702a00941861a0000340d003800180100e5008089000c03000c1d41041e80c0070f0204084501c801e10980b84800d65000e590800c034030401845404100d94080e5102d281814010f00e4102250407405643d00d650400420000401044500f143c0f10001942c1c000400d0172070f5030300e20b024030001d0706010843c0304240c01500803e240390a5502204190f90595105030766090500003034110869142080003801e41e00c038016901c540c1c240d82e0342c4040c01c1341480c664280003130b12490a414060040d0300190010480c1a0514507154050b135503450301200d0400003400d0014101d0000070880303004120a5060b00030014506 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 469486960 1250 469485710 469485721
    0x1806070b010501170403052a07080c01080708011202101107031211150c0a14070b0103020405090a03120203150307080c0a0b121605090613090c0f020606190e 69
    0xd04458140d801c00c0c0c96a0204a07111581c0e09410f403411500940000c00074000d1032180410700d40d011141e4100e41c2801200341c42e91440e114140181a80701800039808420160b26a5820540c0181d018010b4102b52050b07616213508408110a1b48500034030070803c540090007074900401d244540c402c0080300702e510190f02d030310303009907030340714886e00c440110b5111002d00c0203407640080c2010740407508601014540c2c8a05134221a070703410070100d0000380070311998103005e0485000050968107004000e80c411035450360040c4012124094116130140e0007003550f20b00400c1c4c100c03036440c05a45810f100160703681d9890f440c234100c41d4000e90505134180120080042c00301d00c001503064000804075482c0d2159a540c02c8000352900c100150409101c0c1806d000505c0100110503420301401c880c10414900710310b0b03800042c0320703900a40702500200c9081d042440040f00c00d02c0348490404550070150603e00d4941d13006076450314014a43e6100d074502355903c02180d4409081d0000810700f0f154010b4071070801c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 469488210 1250 469486960 469486973
    0x7080703110d060e0c011e0c02040507050906070c06091505090907091505030a1103011518030c0e1801060501020a0212030d0203090d020f0c01121a0a080a05010609060b03010b180607 80
    0x701707241e16000808900c241440c0101042a0002e00c0e20140c0307651881600a42c20b21015100013001c5005002003880841a0303070b211900200b00442c420561000c00b2401c1010140c52940d0707941007007070204191844944d019400034102d959504048078000ca0a82d5580340465010109030050360f1000344807505926a19006400b4601842d805041403220140300a50003070980002d1060103494080d10810603055800350040a0719250194900b01e6401d84a0303d60509100460340840030301c8d03150108005840b1484101802d0682e034100007840a1450980000d41d200d0781c50030040d205d0050070303005c03440c21103080040742d1400351040801d540300d14200946d1034680c4842140d000c054080c1410b2707070351940c07000729440d104c042d0141c40d501e070418a50550725004044400c40a1102080301041038442d6840030911001846080000c04402e24107107401802d58086500c40e40307165082480510540141030300b62030546242c108801d48071940d0b44640412100840c20715038100000060403010b0010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 469489460 1250 469488210 469488223
    0x9032104030b1b251a0403080603060c03010b0a05071e03110d080708040501020c0601081f14060d080f03100f051f20030f0a020d0207080703110d060e 66
    0x3446010760542e81c0e010031142d0b0b5034100040b107140f07000c10400c80044070000d071141c402804201d1400d41c102415aa10034201280542210383c09403003260804c020036601c1099036a0140065015103410708006050401e0b034041030141c00300880700440c1d1450007e01c10810b640c8401e070403074407860070900301030099518524050000e50005180107107a136411040042c1020388460681c1c3d82815907a00c6030700c21104c1107006001240c25540070004e6200c1d0100402c0114040c00a14010f00751003040c116602e6410003480410802c224117001005603803d080050703140d881841038540e0810202240b82c04107840c41144c01001d504000481030103009080c0022810540c1c0140010610081d00c0381d082002c0d4420714410000c44858032000312a04070702c101c0c0220714036026103074034046030024098000d0851300800450042c0390808604061055030400480220542600144c151981890402c41c0c0b07407170050001406580c007800132000552a00c5440749201504148100031141418890740d40707c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 469490710 1250 469489460 469489463
    0x7020a06050c04050f06070c0b0318010903030b03010c090f0e04020d0c091e0621020604050a080a2603131a0c0703080a0b22020c03030903030403180608010b0903210403 74
    0x3211445c05007000d0601101701c032100d9811400140f400da2506841c0b10707a66200400b034404103800f21090f2a1400b80074007540b103103140329407000f10341c4448a50506084602038100c503400c000f2240010441c3c242d6190411003035403641000101c0e0781c2d4540c0081500c1c0c0b80700340c000800c180310035880040c1d03211840e8840752000c1102c21400da02c0ea0000d011070001c1d070722a030040c0c003111102035501c5110a01584008060036101400c00340c10581d0301c1c0009001c0d40e00d19802940c0941200100d94208a1031690035602d1041d940d200d041102084000188140002401c07854001100c100d20024030410000c2c1030110082404101c0c82c07458054014404c542046030103c01240c40c000c00f00ea005442802015045240600510780440e4841d1242100b544001100c1d5115942084100080c250500040d4801d10018000f1a545e080030f21b0014031004800d04c0074061540c540d181881800d500900c440d04444100d00c106403149080310009090869a406084908158440003d2924005005041241d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 469491960 1250 469490710 469490719
    0x151014130f0e070518060a0c020907020c090a05160822140105091c03090c1a04081203010e060108062701150306050d030f0c06020711100c02030c0907020a06050c0405 73
    0x182c41d90f8205490398001c10104462284a280798501e807410004040d1015400030700d040f142c03007141074010580c0b001c03041d42c140f80103811201c00c5400c20309007210344682000d4012030070002813800c40d649400050146803080104110b80010403020300d228071940d10107a40505104002a55030b00d00340b4912180392602901079400d00740002c406020108a4085c000c3e100d00c0c3e00900840128811001443c00000c12940814010303030201c0c14140011504030054503400c100b90799181040700300d03803418912000b07810003c3c0c8100b0050201040444d800d981001d02800c0002d425260900000d5a0315100c0d04c3e6481c840c0781d4180c44201108180a03170030b04a42400340031180a495458040f02078a250780203054128000200b80b2000a100704244c3c028001a460040700c5032000d5035400e020703a4004071041e038050000d600521040d180626020301040f00030304040750843e04039408682c0303846003803c80a01c030ba0388820004220307a000b400302644c41075105c02e04100074540a0381c2d2070f82c0f5400900485008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 469493210 1250 469491960 469491989
    0x170319030207020901031407080102031003140303040c03031407050d021c090b1903110d0227011b030e031009110108040f060b22020c06151014130f 65
    0x501074400c0720409500603010111a030700350345031508612400303480701140d407154000000c0c03c0e00080c4051401405a915000306951035801c1054941c2a0310004007800d0300100709100010380c20014882c00c803a031600700706151002c0c2101d13032000c0d801148000b6010707008103520440e04590104030195100e0215041409400710640210791411050280d401c1280c070400a866440b001c210480148e2907042c40e000c80d04020720380b140c036150b400200042c0e501c1900403070401c0c3c0b40010b485907044278071010503200320340000f09000240001a40d2880d4041c001c480388003c0c00341407140030003140f0304001070100d4241071023450240340149805481a01c544000040940d5558814110b460003940c0007180320602c0111911010020300291900c01e41c001c403441e4004408201c0c40040c0b9840054810005844428111900e410054010079801040450044220940c0d0721170030a00c0ca420700501c0c011400c942c0b054042d8420f0b1040c4606020f040341850800105011010382c41c2007514a80000010b9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 469494460 1250 469493210 469493257
    0x60b090f06130906091e1a07050706090c09061e0b03010501050306012d0c050c010201050405031c1d010b0a0e0f06120a021806030f12120606041703 65
    0x240d01035030410341c401580300030b0b040a00e91641100c0d002e240600030001d4111015920001c212004800c0000300c441c42c13900e04801c0c828218000311290502c0c1c01981894541030b00001c0c0144a6600000d14155942981d40c052001c0d9003001000343c900c0c24020031070a40c440140a0750b24100c1d1454950070f00540341c0100b206103800c8185da041711b0040e1141825510b84030b0042d5140d40e240d1191a5070010081405c0160801c64a01400c4d403003040d8844210300480390910504099141c2c0105055a050806100000c2d10000c06c595240300701c4402c8101001c203003000c0e10003803c0001400c0042e103250024800c4280f5040d4040c41300001c044425200c1c10703503101c1104181c0542141d80d42480500c1d00c0c00941c15041060150810345090b02c00c0da210f11000f90b00040003903143c103850000301010701003040914101040b8400001c4c901340c0c01040d120f141c0030a01c0100e03200d80312001078404211000b1880584805e400e4402409805440030000c105200c000d0b5582d070014140c5500e0007008062040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 469495710 1250 469494460 469494481
    0x5090705010201110405010e12030a200f0a0206030a02090a15090e0714030c0906070c03020f061201140307080a050a0302120702030d08041704060216061434060b09 72
    0x110b04130a41414075060a00d0400152031008204035030541144548440030b0900034184002e0446080342d48a508116040d214411280c042da1030b100585c6078811400741e0040707403000540304d03000f6504540159895030389803698800307401503039400707900002c50030004a0441d074602d0484015100740e607291080c0c6551340c03050005c8003409484d000c000c00c10200701244220040e40c008e5500122040c40c00c2c0c501980100032403021340c0080d0041d154101d00fa1014011807800d042c1015207036404981c400e09054030001e0303454100c0818400c40100c0c460003030100e03c003928240710901c01005003106894403170440741403c5459490f0700000f10014051500c82c08002142e400685000940140c0181426640c1510a0f40e040328064400ea408110750008400740040503801031000c0c081c2c903400b8005a000d003030b02d002401021038100205101008801c040101042c205030368907205042015210300002e58090303092089054807500101c080320707003d03205100381d50f00080585101500c02d0141e030f50710000c581 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 469496960 1250 469495710 469495721
    0x3303020f030403050c07051302070b0105010e0f121203010e0403180311040c090e0c0c07210b0c070b0a0605030c030c06160c12120f020307030c0b1305070905090705010201 75
    0x30800e810144080b070b0120344290040c280100103030044800c3c00d6101c00006840d118074400b04903055800052400030402e030400407500408003820920b030421041d00c00180b10b03403805003510380114a00c00560a04100822813000000102c11501da070380d5841e4680080d080d0070840e01a00401c2e0308100504004207a01d04080071a80c00011035544c03012120b0400c409000d010210740100b0882680104200c8110890580222003440f00d9555503411403141909100071a0302104820403201c140142a4224218000215a00032041011617031040500703070060048401c007500340c010507810401c40c1780181d0b01250944004904541c4509404010942e4481d41d004801303810001c1404131451301c41c40c9071040c1601703d200d1a05501c042e51286c4007141c5a50300c8800a41c3c41100008006038a160000700302d042c1460240b0245180070700c5518003520944500c240200341403800000280002034809007152244c1e404402d0710070650707503039100760040c02c400d503004403150060b150002510b60052141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 469498210 1250 469496960 469496977
    0x160f021606080702030d0f1a030624120a0b060a050607021e01030902044101121109150306062b0809090a02070c050a030812040606330302 61
    0x1042006420a10200c0b01c007103018021900b9440103002d8000b20480758040c880780c4808003940084e50413a6442c40360450a81101414082d403c50000e00503c040303032051031041692140088500c2c9100203011401007914200d42d4403040c001d41040c04200a4008031079400307558200c0b034056520341c0f10b0003000081d200d00030300207620100074656516043d8030710040322003003081410001884561500031509655900840100c802c00d16211404203001c10054081580400107a42c0e521890015007400404c906004124000b40c205c02c03a041040380510103c951440003419002d594144100340070507004804514a100e40140c1000480c9410259401400c0050340140350300c455503040c2003400040100d4806580d60002040440c10720b848001c54280600c20500c0016a00c20741418110f054544603000180700d0b0030501c00400101d0b0389001554001d0026040700c40c01601d680c6400c400602c81d40c0c0c071150712005d01c070002d401398100c164200d008050180c04d0001000030f11100480403407141054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 469499460 1250 469498210 469498243
    0xd1a0405060603040f11182401050f0f04090e010c030c1803060504050c1504060201060f03020105040e0709150507021f021203041401060f0503010f0c0906050706060905160f02 77
    0x20f00030480190681d18180e020310118022183c090b1b01180d0941200b8030100c408011140620607140e00395040c560910701d181504000b44001040020564801ca229901e41d141700030070412003040c0280e04039001802c0f0550300300400500d000e2001e020342202c0a505001c00c7c90800c62008d01c1780215040036100e200325075880d4a450039907a65400810700a07105554511440d4200741c3c1036100c10300101d081c080461400c0ea00e980ca04500282036980d9030708a84d0800800e0002040141d800070b041c0c509a40b8240c45546060b078490700b04075040401988036554601c8002c2802d002581c0010081ca1494000da0303505004044278003495074095103000a500040e400440141d0002e95020041c44c1c01c60701c40d0000c03c44048000051034255400b9030080c000352001044208124070703007407061a801e500c1c400024844000340c910041c024030442c1c0b1903c003d0041c0061540100491588854094003044808028500348a0a2240e620507403001e0360010078451004041414000910003018484910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 469500710 1250 469499460 469499467
    0x130822150804031b06020c030f070c0b0703020a0303050a180b0718031e020310050a0510060819200309070e0f0411060f040905070e0405011e031211030d1a04050606 72
    0x1001131050540c5001924282d609003c0308580c02c8080c00200b0745005983d0585483e0003403070410495103c000d61140c040307035004202c1240003c1d0081503084495806047c0018150b4450074528040c1c000d0101045100c24520024010801d03000741c542c0c000c094a40d00d8690726840b07024441a00d01d0709000140540022079940f4075030600c00d00c18005068405400c3d01e88200710002f2560980e9000d40b002e003203040c3c41d5001c0141100204158400500c042e26110402d401d09400c2034041ca00c0107007a00850740c0d2141302c0e00d542a240d40407000318004039101d055580b85441410304e9110740c403a00414401d055100c1c003087c40c0300000004140500c2c1c1002030920034030004c200b0464941d00c500b10601e2100c8090000013284019441054410303180c40d12403950b280c050340c04000c11518140c0244882548030b580d03c5e07002d5100d411190080c0c2c1e50140c0c40d0040c0351001c40c800d8440d40b80b0307150880d1084c840007400100d00c050130380080c24514000d0f11440303a83c1c076448042006859048075180d82204060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 469501960 1250 469500710 469500737
    0x807020402070222050402040c0f17180706050c1902030714011b080c010516020705010c02030715050a030f050c0f210c0a020c041413082215080403 65
    0x980c02402101d1000b4403801c0790b5282030403061660304c180d415036401c0c15a5103081100303504260050185000d445d11b804010340c40c40d004090144002c1c02c1c66412110407400c002400741014480c0340004140d10f00880d05180c0e6a1031008041c0d40c800c1080d00114040c408443c01800040e504584c4055401000f0309841c6040801040b901041c42c11082d04122800305038001c252181050410312074011120140d40b141c0e04841d00c0d0a4880103024042e101c964409004200390380410306406481003460315450b0180c4900000c0d107000640d07005545408038110003900c1e0290000020252000305840c01e11010309150400c00480e4000c4800c00c411010406ca2540c41001072402060303008410120030311501414848000b0000c1c00301c4614001c400c001070091610394040003500f0404000301c070123200d07210411003820f40c101c8004d481644152a101c55030401c000110040d02c0d1010300d5450b10001d00d45030ba0300c518011072980d2240e901041060384180e4003c0380b00b84005841070ba05030f210721030310580c203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 469503210 1250 469501960 469501969
    0x150907030308090a081201030201200d0c03020a12080403120525020f0106031b050d02130203060319030e01141201230a09061403030a020a0f1a070809010f020403080702 74
    0x30000c0402c0d00800c941a000900500040d200300c6d5a220660b503050b42c11071001405071030742c44030550f510101e00c45d015002c2440c00140c00a890340c40e89010400410103203030030f901d08260314100900211a0b0240002107035440003207140b09601a03510402030340510850101180c0055504001c0c1040192010506100f0488420140030350b0b41704031080010649281400c4902d950004c07502103010601c00080280c10081c8000544000c60310140326400e55030000e1700380302d86004440e01c0c994011000640c81e580a20082c0c0e180181c40240309542005817070014110600d00199a01240c0501021000301030640141d641e82a03c081950740646d08003c0303400c0c20424281c0305900c0107502c02850f90095280c00c225a0010070f12140c02090789820100300700984040c40b040395020354400e01c4a030b000d0711b41c00611079000710f4102c0c2001d4005115410a0090b101c80c0440000010b02c4010034042c0e1694031140c46131086403010000c00001c881028550141e100b948400740c140101480035502500c3d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 469504460 1250 469503210 469503227
    0x1701030f080f031008010e120d2c030403120305010608281e0b040e030a0e180c070c050301050106050703211d1002040506160f05030c0706021509070303 67
    0x3a004103410b04640d03006041040d80115a41076060030983c5082103a040c0900801010109410180054074007011040c140341c040e000030044c090b80c4442d80700d1201a0310140d0f0740c40313031580641d0100204489040466607588075200c2140d02c51030940511a00604c40d204035410380310f45a5404559417503200006818543c0310242512440450004c0c1102088512035016180004000c0030001e210321850350007112041c0501c58002d90400f40042c1420030040202c41e541c1403141054400b000b14000030038041c902214013480d0381080b40081c0010040c030800031b03109840c881c0104c00c40b12902d40050500783d0343c00380308640c080f84050099800080c090075075088035152180c10345d01d0010030034404505803021202c8610088001e0302040085a02c14801c051140103601ea00790318003450580894130078800d6064402e021113110724012b04002901e410ba500c12a08141141d4030344502e064002e80320300780d51180d4005442081c0200c1400c0041e1501d06204200042c00340105920b540c400b89d03003281 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 469505710 1250 469504460 469504463
    0x40611061b0724150501120207030f080a02040b03010b07140c09061002010e07030308161d060a02010e01060303092303030d090c121a13050705011b02090108011401061701030f 77
    0x18880703d0358184000035842001280380130754011180300c52030320380054003000b00c445030030700d07101d00400c2400e0220303822003a100d54418243c0790004586d0359142c1a00024083c50308079070091080040005510b01004000d41415400b43c00c00f00400c00041d4141541d808114903803a400c1a0680005505403a0114000a4040e507900010403680d8080d40942e0031f00501d0742040340440d0305682032004048005407440d0100106041514070100d030340015451078403011040078481c030300004850429610030340000000302c0c8040001d01180d070b124540a00060128050f80c0c0c2d0502e1424100310081003c141c4081c8401000b4000e145031143d40d4026a01612480318140e503948240c89000511042c2880515076140c0250040d01d4100004016070700b21040103401c0d001008420303010726010034130204040d0100d410908000013840400d00e9a80111130003001c0c040d6000003c040000307140320f07040d000004581c02d103c0c44084181c0c0c0300c1805451312680405605c00140441c4010f00026611402414405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 469506960 1250 469505710 469505753
    0x91a130b0d08030c0403113f0d0906030c0c031403130203030703170114011209150213090b031f0203060310021614030306062d040611061b07 62
    0x50840307840342da0803584244c503451016080014200140720280301c5c041d40d0070404880300042c40c42c15801240d50b00880d14075103500c00c80b20200b800d0111ba4400b079207080c03103022201078070004c01e004640034003044100c0c8140f0000ca81000c20f02c0320050311076030107141020b60503101d400e09604004040140ca800041600c0811b210800d142c0015a80c00c01c050440248680c0e110646802030758040008118107a00c402074921488035001e07000da81000e22490301035036001d00003c1e00041820010010023100554450b02d510015110040008500031941910f0242e0020701c1040c40346400c0c155107034041056840f410802500b2f9040310a0f00343c00554200300b00404580c41155488031090403640116104800401070381e0080e005c0251140304501e200c03800002440c114600130001c0352191048041c0004204002ca4440b0b684000c03000c0c21620482c00d9400c841c1e140d60722507202605894a1200c0f03c8954450040040c940701d0900c52501e0030b240d402c00b041402c1605a585030304401461a1302030000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 469508210 1250 469506960 469506979
    0x15040c03020301050c0a1e05030c0d15060909110309060105010f050c031803010b031c050d06080a05061807050307090b0105070b1f05030604020f0d1502030c04091a130b 74
    0x582c0d400d01403240205440034250b0303a500c0410001074040c1c104025103803109404689a80c04140d002402e5075440b2010820666442071111145c400500d80c5103443d03010752201a41c041041c1d54031005840030b440324194108400e041c4a00d0007181e5010031074102c1c880b41d10040050009500c9000302010000e110308246d420000400540f40c25a009540160848607039220681250315003409880c0c4408815030141c140211024010500840184492014003000290148007054640d01400c002c1402506444482101d0301c1c0c1140c60b071806440500c0803d03c2209481c000010104a1300102c5030000d000b02441c0b4980044035004c2c00d02003200354103000d810300050000c05c1f00188680c1c4201505031000d414403e68580038a0380c040140c1103103000394080340404c001600e907030031422042482107850b49486c0200c0d00e44403030184d9020007440016400442400078032100000a003041d01c000107418040f850080c05460b504004031488140d0180c800c070f0803024a008254420402c0c00c01c00b48c94000b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 469509460 1250 469508210 469508213
    0x3041a0c031e0711010f0e090c13030f02091f0e0a0f05041b0602011406090a06080d05040602060112030c060b060d1404060b0105090d06020d0b091503120c15040c03 72
    0x70010b100da4061078404400188000030005580304482041400f403d01c090742c2c48404200401d0400349011f040c0c0112030310307804590340001586c2030320700d2101404415080c19450f407174050750710300004100724001e141d880040740c400b48500403981245104554042400c5203080c4110b000003c011700550207490f030f16401a04604654004c851140707000c3d9031440c003050b80024607891050380c0c0d684184110b91524000c0d901c040910340c0b2a54000310211071411180e113a003000d400040000303174896070181c8901950303d140b05800002a2007160540d40a07601c403a0380e1040c0142c0d01d0001d200004000500c1c1001100c0064a65440314040c0040680030034180b00c1d2f009028012950340404611110b003600040004016090044820480080c03904904008213140401c840b03d03801c0710003d1400303030040340d180e01c4c0c3c400703503880402101001000d4120a0800210345020350f6240300c09a8024014286080140c202480c01c9035815081c80c801403121340b0360301e0f600c00c4d00a0f502900440b40804040c90000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 469510710 1250 469509460 469509487
    0x50d0315030b0403020a0b0c03011809021f1d0303090d12031b031a060f16050a021c03020c1e0f01050408070602031213030210090807050a080406030e03041a0c03 71
    0x91040d40b181d001000c5d4052203040007c803030400201000030095003040180220202500f059842c0c1758281e40100d11201c0710b00c006491506036030b902101c06104c4c541c40001255000d81c5000114003c100304c19220075000c41410f0700c1c4c0c800c45910542055007000e003c800641071108003040714440d440c000800c400300300d40c021030311601250903800003030b207a0032400801c080a0303041e8603c1d600f040312030b5880d0020fa604070348814068400c515017050141f40301203040c00418046040701a50081c03065a40b00f010a600c2c1070b440504110550040c86910100a16800c1071019009110b9213101001d03400c1c0c8182c42000241442c03194a2810442d003888009141c1004100c00ca01810941e0081c644450802040340f1420000034100541d22500e4440e0b9000700e500401e0442070713104050310202d02da040c1404d0070502481003110042c4580724288555090010340c0d402340042d40e015550070b00044172015003080d40c900860290030030b41c030100b00c141d04030350074080010221842007030292800c0034044032091 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 469511960 1250 469510710 469510733
    0x5030c0d0b220606030501080601030b09120703021b01050304020f0f06070501050a05041217010b0a0306080a050607030b010507080d020306010e0a032108190905070b0d020403170403050d031503 85
    0x10b540d90710307042c0189058441401000c000e0085490100a607601d01408180c1c7e40c001888045e008018000200d05400802c0c4400080080c401118030b985c0c10451034001e64600b0015000d842f000c000702102c941c150303c0f61040724056500240f50701c03140300c6a50108202c400c0101040ca620140400c280400107500b03008482c03141d0b27401c034030000705440c09041c006900701c1005000c0c010010b05e0588114000184a18a41500e440c83c6989881c0c07180900b00340c00404494020764814412104d00d0f508105c400510303148542e843e0740d010b01800c0c040e040150303070038001c5140003840349034103000e00000e40c801d41e4003645d0b000c5814945608107034041c0c2c0100d40b480e00640c00540721061208603100992001006c4c44d1b2803000d0a180c03010b01890034220790225184181041807016481c1c0c1e15207414010b080200d00c020303183d510701c1581d903041c194007050025401480b04a494501e0042c074403000865007800d46041b6900907016000c10149604220b0044c88804d0070189050007034000400450b200302d20302d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 469513210 1250 469511960 469511989
    0x30c1513090509060f041a060312070807030f08070c020d1b030c0303140a0f11150907090f0e03040308160503041205101a0f030f0111041809020105030c0d0b 69
    0x240b9800c160140700c1c2040700081c00c640405044e40705220014404001c1c500000e880890282d0321500c540c0006800e0405800707060f1b070518800f0401c0000e014004008004482c42921600c2e801c034601c0303000b0754580d403080f681c403804542c400c0504000743c00d004201e440207521403a0600c50b0401c540f80d01a010340d00680040c8c80e800625542801019003018981c1d05505240b01510300f0001d40b034000030a480301d800c0c40e0104215118041e0708440e4003c100080c6c05000c201d041e0001440c040402594500b60f502c107001845041858107102200c50344a128240c283c40c50256140c02c0c2562681c410395446040d5540380800404200004560144003400c003030040f40006001140703072820a61b00e406200c07a00408468948101c01d800501c042021003032400c0151588041c003003900f0300280c10001003024003051542070242981e00100d00e03400400a40c0c0302008940e64484007281c03213134100c5210341002800325034100007140600c00060302810100c0703244000070400c028802d0200d95900e40b500d60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 469514460 1250 469513210 469513229
    0x91201020405030709020a14030103150c020a020312270a090c051318060e090604030311221508041509080d090c091b020c0d020a0e0108030702010815030c1513 70
    0xc0359130a20380d01c83c0c0783d006070034010062107081d54115211071a00342c0046e13651014335a990302e04944c0d094000d0100d01403030354009064469401680800034a035520000e6024081c4c0c001455440c402007010040407403803540a086030689506103c80c1c10006c1880e4200f142c2400300601020a80080f0350507401c000e001c0c0c0d40c030f40c101400c0803132407105c0585401d0380010040000d403908000362584001401903000360946408a6015164400c40f00e141c460031007031200142c0c000008ac842d45d03107640011400c03155900c1c1c43c0700301505c0150f411102ca15064800800032010710042c06c83d00c0f42c00e40c01c110f408030b000d030340c0d414076012040125030708840010608490b0089a1002006500c50303902c5001180301c078003011009000c4c041a070007502e500700304244a104610784c54480c019901c0e00302540f4003801d0141c040800558640d211140d4a410400007280003642c8140020384040c0c070703d036501c00f440001400030040c0c2121042001405d401c17040c003d24072a6370520030150703070507110f42100004101c1101c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 469515710 1250 469514460 469514467
    0xc05030309010212010e06030d030b150c06090d03020708070b15091812090a2c090a050f0c09010e07020f010c351f0b12060913030509120102040503070902 68
    0xc0901d0b50013059203d001c0c5054032108001043d1400f26590359850720724a000200310000100041c10000c018400452411010450003400301c030009009018540d014225250146a81d038220f05920410f68020150a4280b012500003042d141c0d410b80c0004002a020340e15200d081c01040e03010508469240210a000d4003640d07030b40740140300c400c0c4100022400945031a0003980491111509840b81c030202000a1140580d2000400440101039100c007045050504107080c0455486840b110255072a001c0c00e40c1c0c041060100091100c0c400401601c50101a0318040b02285600001028141940902c1e079407000500c0c001c0c850a0191202c03600e950b011005038441080303041450060010101c64400b8541c0342040076220b100e1340c80310403109014040140301810b4100c848141d40141d1144030040f803681c1c0741d0340d203051899209460503a0140c02d00e5030307814003015146107840c1015000c07502c1040b01312040d00b408400c50340ba20002d00c00143c60aa541c1010038a00051680094112540031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 469516960 1250 469515710 469515727
    0x10f0c0f110a020901142805031603260c0d030507090e010b0910021c05040501111501050108060415080303010807080d1413120b060a0f0b190c050303090102 69
    0x503030824800c0c1e00000003048500b0b41503000c903008007010700449010001c2501c0399401541c855161046503001c402c81d600611259008800d540c100c140076444c802c5c01070700351400001d014071083c10120307600541c5244449900c10402c85021402401c400d4010304208424100102c1c204a00a45012251307400245850305560017801880703550480071529075440010881d51040c3e00640b000130004480d1540740d070300402c0d0b0a0f03240050441c804540c600c0c01c01c1c14011001c3d0484050800c960b400c0e250f0019850807030002946400c500703460640d050001d000180003a51042d01595444100903100082030780b803600340d107900d0401c00da2002c4042c0c1d000000510040350140401d80040c445c881c01001035060482004c0c0042014154005405d900412840d03611101c064001d001030007501c843d18004030507404c0240c0200c104542c0705018800c2d407000050303088038202d0024100ea550041540c01c04020040520a0300f80001c4c0c80010040b4520411703010920910003940a4600c1c07000050362045803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 469518210 1250 469516960 469516967
    0xc07021e0a05040b130c050403020a0e0a05011d1f050301141e060a060e04140a020c010606081006030902060c07120605060d08030601030f1b0513050402032502010f0c0f 74
    0x80b900030a018904181c40e007007894550040751340c40c0d185060004680b0441114040300d0500481d40043c0d8003003c01400012030f410664222400341d0065801800780380c0e200e036048540700c038030407081c1e00c0d0507608000041c1c00702204001d00c0d010700d000c6440070780d8a107540d60300117403e48403142c0d50341c18034101c0c610502c0b10a01d42103c00784186007418217030980c1490458001040700d0142d01c107170004c3c0541c14140550382d6403203500001c00c030001c03800d941d1003604160000000a4114580e0a2000e606c0c0420100d10b0380c0c00b9160b0144070b4038411403060550341c00c00328228080e000740801240c02070024400b0200520043c03000c1400790040c4804402c00d9805030908a00355400030b0a00c3e030007803041e1864032002ca001d100842c0c0d804002030901003070b03512581901c1c100a14440c1c0e414214181802c80080c1c00a40c050000e015142081c154945959201c5081004031b00c403e8400040045400303ca44280d581e10700d410301c501050034000040d250360340003511400d481100400a000030105100d0b170101942 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 469519460 1250 469518210 469518229
    0x110a050d0323010308270d0623010806061003020d020a08061e010903030e0f0d0b07020d030e070312050409110405100e150c120c0303071e02150c07021e 67
    0x103508450b50154510f444070500d5215500c1c009179000044016481c81490300d9420014829002e0558190b01c00b150402c0340041c0005075805000751100000d100003004180701090507a00c415010780308030f031540e0081206480081805509058091244281854035403018028100c07144d190f109803031070311a04111003800001644007140400605099490341d005116800b078076814101844032000841c0010b8032110b801900c0c5500980400c45141008491000a80205103039000c170f584440d800e90703040d421360300110040c0d030035030380410801c00c081303243c0352443c0310060000e0034800c4ca0152503607040b600351620700d480e000c400d080000d01009a4207052404d10701390ba115217011481c3c1c140180000320056031802e040b10100001007a000c0b4400c0f000d000003102701491684003503947d4203016429490b0b4000311041404100100c040604000f910707400d5002c50400c642c0509130000e4260120420f149003d040b0060700c441c184148001038036030303019040e03c221050905e090641001800c1100c0c4a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 469520710 1250 469519460 469519511
    0xf090120070e04031b030c0611210414030a0306081005010b03040b0606210f010e16030c020c120307020906011416080f07030507050601060903080406110a050d03 71
    0xd1103518040c00020020035080c00b03075103880762060440d4031141800c0780d265000d0032491013440702c4a05800c040542102ca41d14540d4415001403001d4042d00307141c4000c07402140344040c0b0043c212a0484454668004200d030700911030080c036160140491549450341d0040d00d20040401e6540341c090100c85c20400403100e01e4034018009101640c10f00210304828000600010101510302c3c0120710305035107407800c1e5841c0711403042941400b00c03100790203016100030076250f074441004200c00101e000805440f46c24482c851040340041c1d01c51345140110020401e5004510440c096010100110b958032481400c200241400541d11a120340c01048140100a042130303040c8a4600000f848030101081992111a00c5001e040d03180001c0d414a00000d10401c0a00400760b000000c40310100360f0404080e003c583c0c068422601c3e1aa25045c0a60301c09116000181ca841001d00081180c1807203110310000b00e00100003070301d0341c02c41d195513024542030046680201082c1c07201c11110f070a01d04410004c5404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 469521960 1250 469520710 469520747
    0x7080609010b0a0e01030e01020d0b0f121911030118061d101505040f050906010603140f04020f0d210305060a0b0c190c15050c0d0e0307030203030f0901 67
    0x652502001d00c00c40d101e143c0070b8106129000f00041ca8a078083e030301c645595000a0001d660705d602c0300e40c0c0400180860b4031600c0c0310b04260007a640903030a2443d031042200359120001e03d8500c0c64030398003000802422504850123111500e98504a44007806081050b400c6000709040c0e6060070325150062b2828100440200d4038800703040d0219800c0016868a40c840940300000d103001502e445c0100c2d101c003600040d030028182200f45a000da030170b500c42c501c80c50600041c0d0b1182d03605c0c0c1000f1810340b02d5171040301d484517114030040385501c1c005000303980c0c015100510070701400c0c810b8400708404103070420301034500031140d0000c1c1014030410751802c4805c00484c82c4c108401d2030203400150320102940a2840403c0022540c05510001003103080820b0032001049600c1e00c65614080690307040c0c1d030040300381907807120402c148454011400d03140303040d0a04024101281070000d04a40410b00c01c1c510551611074558000b0168509000034800b40310003841c5260b46202403170014201c81201040050312 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 469523210 1250 469521960 469521979
    0x260406200c0d03050d06030503040b0a0e01080c030609131a090c04060e0a020c12030903190e06031315090510050106050406080f06060913050a061a0a080c070605010e070806 76
    0x21a59002d240c1080a503060034980d4880b038103040c4010003480d180e04010f06520002a020404010380c1000e001c003603020784d039140b80b03d04805004507080c55003076074031400c0d002c01480483c0c1107103403c0c4003140d84012602c003500301030803081d10394411080441c0c000c5c28885071442c05010300b0120503c016086820181c80c14820140b07040768010074075200414034982140d000c90750040d061000e02c4008440c0302da10224070340360b0070595105d94890f40099280d005120010988542050048144642c031a20081032541559101c1c45400000c0c0c0382d220040310340152180184022041900ca0354180d540510001c00400a5640d64142102c0d03040c0c00c01d0041c042c052100700070b0720750f0000800768040000d0420011a4640390b02240007170141c07020550340481c10300700c1045801401c5d0b00483c0714680c0c1c00b2007030100c1076442c565690120400803241d031404400b044402c1c1d6140c05070641d181c003d00d805549038a002410707260702040b59001c0e001140290340c00c009000e113031584940e00310b03040702c1c0450703180c000b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 469524460 1250 469523210 469523233
    0x3030903030515030d03020318060f0a060603061503090302070b0d0204030507050901150c031b06020a08061504061b20150a0504030605070e04050a0b120c09010326040620 75
    0x151410712030170017000c0540000000b0102d0700c10804c0c03110f8090300881210a14146121010300008080312980501464200c3c0003800a00c41c2c05080200d480480401e03280e4105d0355411000b030203000806034150b11841c000001e8410f014030040210403034800d401038036981589022401e0240c603a0081d03218100e941c005004400207001c00c0031200c0c4081c1017608140500b85420350751440c000d4101c80e054446654441d040c844c2580090005c00d5032982c0345d001982e20f0008200700591059401d03c01154148000e20080303000e610b012548881e402c0d03030744000a081c1d03520f0801d10059601480041d9000f0080803002d410800076464801c540115480d0400d0807040000780703140158440a01003544407004150034901407842d6410888024100f80302034034080000b40003400c031003a0340c41d02078812104040115040455950301d00740005000b0b50169285494a054101c1055055403039a50f090042c422020315200080000340041e4a45610310000004000203611703009800c904143c00800003d074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 469525710 1250 469524460 469524463
    0x70e030105040b0601032301240836010e03180102150604020a03020405121b0d020607060f06120c05030c1c02090405030c0d020c0a090e0d0309080f070303090303051503 74
    0x44c0c0c8884203180010300d07800c031014024a0350704905a540540400440085901c3c1c50f01724099180e4105c15040350300d5015600401c13204403030210f13008070310100320100c082d40d80c039000b150400300364140118644407080e100000303e0031100641505003065000250b40c080c59988540e0804404109001500c2620018a03400c0c504000050841c0c0c8500d40c00203251901c0c5000f0f0b07043d039002d00b402400c00d49040e80c48005041e07590808810801c1c1c06003074192030306081e180040c41110322550282890f81480c2d0740780c0d03c80010306403590361058407070b444240c04500b038022855010344040c081c0c400c56a0007490300d002c0c1410500b026540702e020300d0034034080f142004807000b06102000e5040d0f904e02019a9039007099810750007100c40200c410b01505040320801640050070b049030300307011501c2c402d0703140c2c0d40d0740000112100d5043c40003da81141c1c1210004c1c3d07010f85c0c001600540641c820500d400440c03c80c0b0481680181400c4000c03954549200b8203060341482015442840301c01c40e41511850040001e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 469526960 1250 469525710 469525733
    0x42309011707091805010b10020a1e080c0616180e070c060629070c1221030e0105070314160909061d09030403021e12070905070e03010504 61
    0x210900546800c41e01042001001090700610712202c0410040440c540000d22a006920050315650700b00303c40c5200030f28000c160020045456002000a40c2d0180d44d03c90115a00010200c0c1d40b025084540307001c107001400500040b058900500410300c0c014040b42c074158a00004030301007140e800c0d42d00b92026214404202511405c0c00c400c607040d0391b01c080844081124550040c01942003090015001ca91011420590024640ca20b003401e00300da03502c0d10181c06030b1000a04005001e101c104106124204800c200c40c1c082e101440721740400901c00800200c0e060007083c002581e800f14400180402c3c4a21600306005181c20300c0f03254050300000301c0c0008080c050124a070702106180c0c02d8a802400c440c2e000b808442c0f81480b5065903002140c1c900101e0003071410108600000060703d0305000300444007903da0041003101c4460810b01c0c2002140d402c00742c100d40007c009000b6100c14003082103070304014640b03080b0104040c42d02502c001d01c000c40d0342c4040c81c0281c1c18030007400300055150341c46 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 469528210 1250 469526960 469526969
    0xd02160b03071d1009063207081204030f031805150a0e0f010506040b011e050f0f03040c06020c060f09090402030304031b0329160e031204230901 64
    0x1d82c6600c40e80360030011144030203000d66a1140128404240c04d07038000035605c04403869501d0b1000040e50440e4011800400f202d4141c0365039001c2d591200380e10080b40060320b20380c2e000301034543c1071920b40000808080c00a44095002c5105c1d080000700c82645805120500d60311414941c14092280e50364035501c29843d0304c0e02c03c2e0003c402000030020000d039801080046078000032a5a00411071072480e000f000c003540c02d54001da003450b61030f00707195001c3d840354244121112880c1c0c0152242c203a085860303400c0714905103002282080f0003c440c500723440c0507500a500400c200c0c0d0800f03180c400064541290108400d000ea1000d200c111034488038030341a6041803005580c584880da4070fa10010741940324540009150141202540003440004006a402e59104103130030071840c424210340394034404e1417000b003021071400c04c4005107184120030074040c031305c484a04200901d8400000082d003046118488150712881c041002c000d1001b980800480030300c1c40c5003250038041e49000120b1000c86e414020f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 469529460 1250 469528210 469528217
    0x5070b0f0d09020f0d0c23100c03030603170a02010605010206070c0201081512150c0f04090b0d0203030301061101050f061c032a1b0503061f03020d03020d02160b0307 73
    0x440c0b0042d0349403415140000b500042a8110344a55450084070304a6075001c1d201c042000350b01e0515036549040c103004c01000d03000b00068a120301e9076500b04d881d0700d000030b0200d08164a5040000c0010310000801d607a999810452944400c500c074030080c211000360380090704550110303041c03041c0e00c0d8200350110000c64080c40d007000503580b03c1211601100c1c183c1d80f1103412050f0b048000341c0403840410f0302102d041c440d8503682c400391500e015a40d0940a03003441e0103841c0d40100020020f01c0b1881d0300800710300501400751411000c0f075400080c01c54100760f000343c0100714006c28004500d0028450903030300c80d155009024490507d240402c0b4949150484218075012013140c3c0300526003e078100800790050301d03540140c0c4644030b100700d110b08003400310110303042002d004d002081c41014607421026a0030250040c0840d41e9541c4c01c180030100030b0300040c048000605000701c0561a420700300040c4038001d40080040140560009180c0440c0303910088251003101c10900c080d424003000ca0ba0800f15500c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 469530710 1250 469529460 469529471
    0x1b1806060705190c0510080c1e070b04050d0f02071d1306090605161e050c031207030b0a0501020d02280f0501050f010b0a0e010c02010e1e030708030f030103080a230705070b0f0d 78
    0x80b2527202c1d48600c08010344400d14940c01c100420400041440e141c950380d5480c900940c082c80400c0c1d94855003030145091160130100c03d01080780c5c40c6182c00ba0f10520403280f04210712015110441164000b10080e5109078503003042001e0100064203812010400345880c0c190400300400600715101c0d103240748401c00000043c04500c81c031003001aa0000c401e0103680c0302080c102000c0280041422100326402015401c2d40054590300220b1010907a5819402801d13603100a00c3c00081d078107900d460b042c010714105203001d1020588070744210b00ca03140314200005003410041901c10603844140c0c092141c940c0e0400800403442d602051020140c002800d0006104620384010ba940400000000381c00c8a017501a0f070003a100420a403c29600c41501600c0303040e51a072000c1a142d10481038170705041d00381040108005030075180140624611490310340c0031103c241492071141c0303400b920a03180d245000b24412007071020030302c41600280110319485141610301e4030f80c240140102c01c2a504055500d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 469531960 1250 469530710 469530757
    0x1060e072606062502030d140703081f06030b04060b09060403061505130906050703021e090619020303010603060509061e0409020307081b1806060705190c0510080c 72
    0x1000c0e558010381350069a0060030a0000e05031589480d424144e1003031007070f0581d1071540c1c1c0c05240c030b100201307208081d0f4610749400750b18203840c0c078000508010020801002e007800f04041c0d0b1a42d20000e49465a4041906a1403c08000649025400c01c4540c0c0d0000c104c0091a139958004450440790b01c48000704403159454905030254260350310542c1c12858141d20040600e8240c2c0c07021030391600c1078500300000e071200c007811807c0340504444c1a1080080ca07085010900344032028022400c0700620307a41c42d090003144104440072284403160051ba0011005100064140c0691030241505550b154182e00d05100012040f0861000084030200c01381c06203406034485801500107280c014048484090303645007004d07a50b040c0e4140b8040c254082c102040c03a2443c000001a005101d0354117613001035180d11081021344e0780a118200d52620844281e178025240450f002c080040c0141512104030f46050240004808441d09485c10081307400b041140440b0124251410003c1c9040072083c8030a00703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 469533210 1250 469531960 469531969
    0x30717031c060306060b09130b06030a090f060204150f0201091203180c03081b0c060304060c02031201030c0501031407080c0a0320040f050102060108151302100201060e072606 77
    0x143e04082c00840c2401c1e404244071441d03500410301c0728416603401500820b600c040308100c0e40307810010f0354000740400c0844c82c000c00701e80180ca40240111000c0c841003010342c2c3e40da0200d17070003580820440c03100d08070798001c1560080401014000c050000b4000224684c1e2000b14030035140710270030181551440c0b9024038507415581c000b0000e910403440c2e0503003601c0e8109030700310f508000c0521150f0311050301c5000241c200880c0121600c000a8885403e40d1142d44e1103a0203000c0a44902d011407006201600e0850282c04185000354042e118401101e230402000400b690443c0514a00d40c0c4c4406007803000b035903030065129034446102650651130398984c00003280603181905250b00322020002880340d0000c008402842154102c91058514690b9403006985680b4240300d00c4086801c210f48406001e24114180c90380500004020071318145113500013045505a540c0c500b0040c2e41d0303071030107003d000d400280303654000442d800e0406000d000c2c9a581e0740c0100b0301c058002072200340507000c60708548a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 469534460 1250 469533210 469533221
    0x150504051009120b09010b0d200d0c06030203010302090a0b09040b09100e0105012402100e1240031b080105130b010614041403120d0b030717031c 64
    0xc0303220f2851560750b07032401c01010304030055840082039480e224228040345080142150841c0d4481d100a1520549030742e0b0b80401c05040015a402008456103240000d107102940c81c00341509490044c3c07694110700512088040c001c2c400c0003400d01d0482d016903940d650515071a0300c90740c4201660500ea8800c02c06d103003020b450309003030401c45040084010400c607040d0085d0b8180c441030070040ca100c440e02005890400c015104200240e000008a12601e4035250060380c0d102010f002103c2101c2d60318040219a0b901a0603511105010480340ca680040d00348a4070000d01100c2e1100700e6010b808845441e2600385a2000501004025801c1480404040c48070002858414001c000628248241340e00d084816141101c070042e055001241c600d0191701d51092109025941c10308040c00c3ca240b900700c60717403640c0000d41d041c402c400360b030740407460060020700520b04000c60100d2010001800d00d850880c8035002a103501d0100c0f54001403c2e030000090b9000d460304005804407103448070003100000c15 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 469535710 1250 469534460 469534469
    0x50c030303090a1403071a10051e0f0f06030703090201020c0306040c03140f03030117030702042f03160c0c1a18010503100315020d02070c090501150504051009 70
    0x110030000e030b080000c038140100c1c070b02400c00c045021100c241c04548034800d03000002e101074241c2a0414001c00c0ea05003032503100f1820718210001940b900c00145000c801e20408650130b00410810034054104600c18008962064514191b0f0280503c00903005000060000c020075644031820702c1036a200f00420031209001506440c282c0c01d05080402c052030f040e0105841d401507807c80821400000590901034428803005941036900f014401521840c42080785003a610040c0a80e402580c0d1328840d4071260100040441c42084001035100100190a01043c80540081c010026210820011840341c01345625002070680a5407601e1001201507070400148080481a40c000035005000109007247a20708074611507010325800116501d2008a4140036402c081c52010400140d00c15009a0b0034000c0003005800c201a0081c0700c022a0401d490603030722507140e40001c02c10b0503414492240906045143d0711118842801d001e8032a1113544100c40c003500c0e908450085652041040c1005031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 469536960 1250 469535710 469535713
    0x6040207080f03010e070507110609130e010906060503010c0914150a02100f052502030910021005010506070812100e0903030402011805131a060c0706030f050c090904050c03 76
    0x14000c1c4100b12510750400d0148880c0c09491102240c0020b0040082d50821030344418a0a48140007405100190300520b55941c0c014a040a04280c43c1038280248003101204500001b030000b1241000402d640c0e09610180c0240d24101c50701a1203070b4070002040550750020507510072402844042040f84000c881d42c400d0254002c14140036a03a80800c255400346c22511017400301910420b44681201c0e01541d044a941040c0101d036031a8080e640300d2a80c80222900649040400302004109030b0611102904010b8100d039681e440c8000e0b15216607400f41600392811410241300c0e0ba00c1c413440340300303041a06441211035400105418001030f020405490260200101d074242911000c1d40d84d01300b034030100e001c10741c0d115003891002c891107813010444400030002120f41c0038030420300004160307400f1210201040990078102c11307181d0300014010381c440d04006100d407a1609400600711038024203020354840c140020700c41e2082c985000e4030702540046501c212035071640c1c0b61040c6449120801725805 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 469538210 1250 469536960 469536967
    0x908070504020f070203070617090102041d040312061805010801050903092107060507060513051f0603020a0305070f080705060d0b030123070e030a200a030b010b1804090c0902030604020708 83
    0x404d901c49c00c2210044110801075082e03898240c06242070b070181d0700613406c0c1c031004d21a403000182001920107421500034101240e0880340800840165003550700200e10310400d0340400307000354401e84161401403000c0310003002581030840002d80c480c80f840c99018404c8488480300100740c00c0f512000070b0030791841c070216840341c0c6d940c0f140500a60400c2d1810355207a407034a0300107070312010f09079608468268004080d00007582c00740d07140601500481428041c042c0e840d400440143c948020302805540184000c02d4031a28140c400e5074070703075016007200c00305d80c000140070070081d00c6800984019a041d10404100d034a280e40100317004080345a0720001880d0041a4001007259a010540c0135604c03540d0b58800410300031082c90703546c0c00203881c01043c0007030303211010882c0c4041202d00355900c400204007044013a43c82e10b0300030880e442038015010020001805081d901c100d0240c3c0d20090005840500c582c1c0c1186d25011520706042c13003405042c2d90000700041c190340d100c0d03044030b00c0b050344003040c541c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 469539460 1250 469538210 469538219
    0x10f0302152116050c1018060e010510060c05030d42060201060b0d090f02031b010e0d02090a0b0105130e0103020f010302031308071e110f010908070504020f07020307 73
    0x300b414140c40e451002c0c16120034400708148610112140c05100d03400424281d60a501c85a004003058419491130300e00965044001a643c2e00a00c0d80201c0c450001207000d081c200541191081503034850130034040c0400e40c0d040092408000e032614a04442c000140310420b12280100e070030500508142c050328030b11502c10b0105080c0007411541a103260a0b0351001e91214030036030803205076010361100b0316401e00c184030b042d4040b0b400000303005104a154111518151340400c0c070389002c031105078555003a1081004040d503404102120110710480c0d1092010b1055000329514240107170290382219116000700f01d050b4010310894400c8a000e8a508076100d80d109803c08500c5801c0c00203e215101e1991540b01c5580f10f402500c2c019000410110403169045c3d40b0003040c1d0b400120110351400208100ea602c241c40348009a0302d2601550441d41c540c0108000c20062082c11390103039044c401c41c120306028480c4000740c2c040c1075503019100140d5600390b40c103035100203004e140030085d4503118149000c103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 469540710 1250 469539460 469539517
    0xa0e0f150f091e0c0405010203070f0f120822030e100e1c0303050114180703060504140106121a01030e0a06020703111905030a0f0c0b042009010f030215 67
    0x80703410203c02d2905043d21000b09210052046104842c011380c818042d2030046446206200c0c1382ca4400d445000008005a55000d00c0e081c0011810010503100810841016030415088032803540d0b111404003c0d920507039001d01182d10555005005540e114040e40c03100303000d07203150b8070030940080c42d0742c0000c8015006500c0502076001c0c09ca000074203110000881d81c01043ca0150102401012580c45001c2002c80110000c070080c500c108054950f180010310b5220761003180004c480544407100c140d81002405010701e595074151071400f070324121100c030104035104500b0501000910300450500e074103d50f80c902d07145034804c010704424400200d810170550040c901c0f103071172000e15094440d21040d13108400c440b11407040c2e0181c81501f0070450b441c00d42d840780318110b1181c0a14200741d0f41c2c1d029030f0b498084404004071000c440244013a80c0a41942e1051101c9842e84903045a41e00001d40c1010122050034149110082c05042210504503402003a441510803000781d05e40a03600c48183c500551 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 469541960 1250 469540710 469540741
    0x90609030a110a08070f0b0a1205070201090201030506030c010c020411091203070203060108030301080a1101091706090c19050d2405060a0902040b1c020d14060a0e0f150f09 76
    0x3140f04041c00080000c440300c011034800c046600000301d03141030a1415130300c10f240f50321560021040000741e4070040d40202207845500c0c0110916400002d81d4040340c130014013111000340c001c500c0ba502c6415003080c66a80301c109400003c2c1c0c191030200e407840040001c080e0034000d6800300d41d808060101480000d901c00009000a030303000700c00311040c60b6a01e13641c00b0344074882805685040e41280c00c0d520046086002501034244041c074002d412640d6840400c03991051000700c00e44560085428442100002c000020844100711800c0e46a685004041e10000d03000c0d00c10540a1421052201c050004000c49082480441005001e0142080d002000141821160184144051040031a903680e40e4030aa505484031004140c0c6044800516810025450209501e1468080202c01090206806080c902812240070220076050540c20031882c00d40715082007807800c100c02c0c00c0041480c00d070001e031500302070341a10f02c0110396940404103003980802500260041407010a00a00c064040c2c0007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 469543210 1250 469541960 469541993
    0x13033f0605060304030c030302090a030b0c03040c05040203060d0f020f09160210050402060417100614091b1207050f04060e120c1e03010f0f0204080d030c14090609030a 74
    0x801205403101c040142600007503038040c00182680b2509000240a580100103c1400420389070100760350f61750741d1201040c2280c683c018490040140000c008901000134040c0c0000c032415401c510300354000c1500112070079000f82030a820815460107548035141480c12a0501a080c0b03caa0b1a005000038036005020440d4030052040a556851009a62007550300843e401404180380c40c0c5040790910706c1541d14107803003606001d20008012801d000b0b00c00c582c02000c080e140c030000d013192141000f180040007420500d40220350b400740004d5030f061504641d03441d80c0300a0100c0080e1610b0308215a54000c0491a030b80c0701c9400036011580940201e00d0b001c0e01c034411207142d9034521a07211000d07160707a54a98100d401c190b40b8213446480c9174400c040c82160301000b8000043c0301c00d041c11080182c9001c103124540c01c0741e00140a2260b04014401eaa07040380b02420103229165501c2c400401c0048401041c1302c0194011529481603510041101e245040040884150f01000d0030074520540c0e18491 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 469544460 1250 469543210 469543337
    0xf0e01021902010c080c1803100e0c0d020a0b16060e070f06110c0108090c1c120c17032203020601180e03091c200114031303 55
    0x40c1c49980d1050061009000391a5280c0b5250b868060224420781c020090500d02c00307404280034880c075101004600b010028107031000c1003c503841211a420480305140d961f020740301040310000980c59038100081140c0003054001d0340d0349806240c07001c40301c03003507100180030505150101d0000000010a0000e44e00401c4445100030f90f10303581510703404081026494942c0140030350402c598060351186920106a8017580d100c48500303000900c0c11202c05046102c004e540d03020f43c400340f0424040b003203001d030002d080403a1586800e03100c0100a40741d102144210703480010014500e4905aa03514000900805d401c1020041c0b80c50080d44500c004d000307180001006c010b030311021513041d000d2401090492000f81d40351580440c03e000b240301c880030114500c3d001c490b83c2c2c0c400060403140c0f840b18100c2188000c0d05542054000101114035520851101c44414400e0000003420b101c001c440f8154181441440f55109100c01581134125800820401200c51f101c4c01404403070b01060170080b4403c82 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 469545710 1250 469544460 469544497
    0x6060f060c02031f02040f08030706180b1323010c1103090604050d02040e0a03170a090308010b28051e04030f0308130803040320010e1f0f0e0102 64
    0x210110745002411001a41c5a4000c451002c28555030f502000a414000340025140c2915981e14600703002d0560702100b09684002081d0041c41240e1068101d050503510300413500f402c40c0e1b114021542000b50240d081285c00321158000c11911070003491042241011031110b007581110498000e00013418203001094000786410304910010045646144c0014805414541800e05200c20303202140c034220703007041e51030417906000c0f101040400105c1e0722a41c0c929410714038030743c07003a081e1a401601029007582400e109a0010760060b0205054901d19002c01d9100d9080340d92020200c403070740004650302d110301090707481c040780c1c00350041445150301000050002040d03509401188503031712011b84031010507504803001030720031000980c000c8003910044002e040c0a468044007548251422000314000951850400c850900340c001c0a1148000030010380c3c45e0001190b0321103038140160003c1c00001c1216407070501160f4000440c0c056a60340802c03134850580c0ca40e070300039884000a0180588047c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 469546960 1250 469545710 469545719
    0x2090c03010503010b0a080d050d0e2e0203040503090d08122502030711090601050d020a180b0309060c0d02042303160f03061d1915020708090607020102011806060f 72
    0x4280740c0c121001c1800508000ca488c120803030b0a86c01c0f00c0310400c0b80c40d4450004009846003017110b41c0303411080b0000851940440c01c2200d03844030341d1484910321140140204404501d01005503403800d401035030541e2041410b40341208007441482285103080400300140a110010001d43c1d40000c0250103440444211481d4141e94138050098028910802001450424100242256040141030403e20704165820443c0c00c180d0300302e08075043c00580708080c0c400054070301c42d0150f03004204214003140b6604150030700726120390004021410790040050103428030070351641120010b00c601046200d0340d50036102031841060380c000d0118400d11030400b006042590320b4015404aa030302c103c0700903c06145650b032002800b0103489030107190282c52003861000dd001d21400c0d1512450b90070004100202d464104180304044250803040ca00c140f05110000d1000340c00c5400140301142e2154503140c00c0d01c0100c1c050615256001d51007440d00860404012641c7c00404c1961000c9602030f80c2e05031038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 469548210 1250 469546960 469546969
    0xb03100609140604090e0717010507020d09061d15070807050c010305090607120f0e010203240a0303050306030c03010204030311191113200c011415060f0702090c03010503010b 77
    0x480100b41d901800c01c010400102c076140d80036640d0095403506031071095a5030b081050081c401c51100303003101d1351070b14108450160f0600c405204203045040c840c114030300f0004000c5c96400ca8580314000f0700c00d684495010340c0d0310900e9500706524030002c640d941b6805850012901e820400048406120300c001c25a065800ba00682d449503052400603c1d140e80c500c0f10444580c404643c011000c19603c501c2e04021240d28001c0f04040d080c210005a070301e0500142e00c02c801005034869011550104401001d19a40e151000f82103e4141c60041c0c2c41c1d403510400642001001c1c419240e00d03610015000080603041065260078559001c162019244007080d41381e60003c0000004010ba41c8203180c19100380f52183c9461840c40704a0384c00100c802d40b190340c0d29007181921281c3d06483d40e0100701882248802d004080d40010358001064244c10402d04051025907030401c1e0b41e22650012074000c20044480e425544040d4004104250341c4c00c0c45c01410301b440d03000b03028103402942401c1003000f5a040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 469549460 1250 469548210 469548239
    0xf1f080a05160f050f040905060112090c090902010e100206040c1202010806010c1b0303020f0708070506070627031e020102070f060e2112160203070b0406060b03100609 74
    0x2c40d038911001da11420707041140c0c008031001205083c40740a215030810170992a02178805020105070000d12410100005460640f0703401884259500b4a20043c001480da02d80301001c03108000c07070124a8951030302c01601c6101541d60080e4002811600c240d0095500040c528099130180d140080c8036030306c540c4682c00d030410b4110b000e400701d40248042021544aa444030340c0d803a025038840b1010300601144980c000e1110752040c0c0069000751406501c58606102290080c4803d000412805103000c0c0824040e01400001800c05540d03486400500e03034100c0c91441c440143c1d07034682c00ca00d02552602606280d0310811030100050b0030300104102a005100b05e54409800c800c080c4440700c030941d140006049656083c031030301e001d007116011005510141c0e0740c0c0300c6003c1c8000341e0303250750303007144814070000000b0656400442c10a0b4407098494003c8102d0312070a0f00f28841301c00c01da0ba6401c1000140150381d0040301c47c0000007040101040483c2000400d4500d41c0d41c40350342c1540d8400c510340c840382 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 469550710 1250 469549460 469549471
    0x303070605060126012702070b0609070e03120d0204080312070e040c020c1306050604061d15030f0405122a0303012102030106120c030b0f1b03060f1f080a05 69
    0xd8160043c0711024044410700e8200200d48031806d00c145480c165a000da03003202030f048540014400074840a407070492070407a4015014a080b00c0441c2c58035000a03540c0d0070391103200104640000300c1e03400c0603c3c90b804990290110200303c99860801c007180410604080f6000000104a22840805403905014000e00810940d00031320080c86200304005805042412030468195201030018054031504040d0005040c20b48880004205402d0303071485001201101ba4442c21214202c42c500010076000c1c2d0740c00445061a0a141c0c1d982c0340351441c50044040c01c3d02685280100e41c00824010400e90380c40d80c0c001254510b0107403101941003d550340400e0140340010502441140011420a0180c40e10b550000b400414816a142028611060720120a40f059200c856051090217521031419801440d10798509190345481b00407044c0441040c016407102d00e00010100e01c85940380ca04407240d0100c003e02c1031042c582e00d064241481500d8185070f02c08124403500251a07800244659803064 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 469551960 1250 469550710 469550777
    0x60f090f010903080c1305040f0f060504060605040314030409050127200d02090402040e040b16050f030402030c090c03090f0703020307030206030702100207061d0102091e0a030203030706050601 85
    0x3902c40c010503100c1900f20b490400c08150f40c6d4000024030b50b6690084020210fa0750f030700020b01880311409002aa4110303006203005e01d0a000342045140c1d4070074115402c8035000611907072188148120f8505600c5154498414039041000200760788601d0b800c030547d10f01c1c140e05a5000c1d905642d20402c150741c207102c0043d003400c0410507a4803280d891b03003000f0b20110040400c01032825654200140490304150403000802030201c0800c0f0400503000c50058100c6008103c8058200c06102c0060080c0b1407159003e56050300032020408541302008907034a0420000c0840145290442c1c81495a400c00ca48608080c800c1020501d90f031240400c0c50741c2540c0d00070f009064203d0450b02440400d51000d0480c1046104081d00824500058070251100c6031040101140c0d40041c205940c1c903040782111086220b074810096241241e030b41e100001070803000f4006483c82c000401002600354110303640065054003000441104000040d80650b2045400b6224034041301000440195484400c403c2054030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 469553210 1250 469551960 469551977
    0x9060807090e0d17070504030b0a15060516021302070803070e03190c0b210910050106093602160c080303011802030c07020a060807020c04020c0c09090a05060f090f010903 75
    0x1130725591800715400b804c2401e000b40703403e9980da260015258201c6d000c45a003541d0342000c044413035640603c3c600420003890300c2070a0940c02040d185038a1030009009204285d64000801032140340d07019917846d2a04100c0154a0345404240540b5204200400c64807030300a0081c10351300c0040c4051300c0c01c071250b0441403210a85091002150803a80100700c1d948900000071891606100505589880b0f40035240252420300c942028407415941c040e0080014440096400d120a0030248415484c142440c0100013802c0b6800c00500d5002008082180c00745000140040244503800e20070321304513218401e40030450f955030818540380d0000f030250710710051808103001039800050700130f1a0000031a024051030304031a60700296000d0f0055000b080032070182020010000c1d01806080086032066400703514141e0000d0040f038a88226001c0c0303501c203064220200303000c10801c0080180060344902115440e003040207403104510000c8a00c0d05080c03081d83c1403011028411300400c040c0319850707203030901c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 469554460 1250 469553210 469553237
    0x102031003060b1207060207080f0606010f0318050118050f010204050136030609061401060f110705060d06030b01062a0f060f060f0b0f030c030c0409060807090e0d 72
    0x15001d103204a6512902512240060544c05e110200c0106400d800a0000f81d28000085081925100c90030486030021001c101459070080c015100038005841c0001d000d290450410199910440d00642075601c1c7c8000c0030b80021914020140c054010004c5503000000c2d19070321401d0b071085010341800a0034018000030910455615a01002e80c07612000c2040f83d18040408107030800c60f48151440380c1c0b1100b803a818451030f03201e162075190352010003808540c1000009005584030000010812126501c1d001c01c2c2d43e400d00060001c5d007801072566a954884924440180c54a40003c2c1c44904a050001038102e004007030221140c10001e448a014100f01c1c16456203541d1442810750703030219024414400600f043c402d10809035442080011131909100070001c2d00030440e04501c40c400360810690365900203e00540c1e81c0041d11000b129503031307910400e440b44603000b81c1c2e024550700d40c18000d010074280c1020400a090307801c003000c100304074070242c0d0754603640314202c0001c5008a0310b980302440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 469555710 1250 469554460 469554473
    0xe09030a11030d0908030610020a020d0201210e010e39010c08120919080d0c05090a0303050304122d020f030c0f060c0705120c01090b0708040308090102031003 70
    0x80c1c04282401502d042c80702d0b20070141c080d6040d40000b02c40e0144d001041040d985040b164540c1040c10a1000300302003e5680d003c26059440c000010f0b0612683d031895803025104070551030340c4550340c1081888401718407020380d03001c0c1c020308075151035a0103050702c00124800500f082110003800b100341c01d07400e000c0706504d020344403941009a604001d134084055000c1002c040040400943c40c0004241c1407a14031440d41c04d04482e0044643d611000d08000d2021511440c203580718540c2d01031000880e45103905d0166014496511155000a11024000185031300080510300c5240070326000010640740da034084a005442c0818500034000c2a49a600144842c07640803c405d00039004035400c401c103240d07803149150058020000b00354041d100350300031400c003440219041948807130341314145000341d074403551034071008828a074501001080d0254088000d411400d24240c03c406000c801d8240800e008200880c203ca081c4c010466080100d1540c840510840344511060821151024110395806 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 469556960 1250 469555710 469555727
    0x30906030c0a090323101e05060a1e090b031204091a06040f14060304030e0108092514010c1707060b060c010203180a171606060b130e09030a 62
    0x2041003018600c0c001c130015114100a154a000c24a2885020614010f216240c558240d0414000c2c5041c8115400c00c51f103814160f91020f640f010007c00c4941d40d0502003020151580e120500707100c000200c094504c14019005020356014001c103000700e820f108140f5950314100c0320010168601000b0410024509600a40034013a103a66803085100d041c60000e00c0707640064000080074401d40350100000c07035540c0045035400d90199000c5095240a48005d055000701014080c10300040c1c80004500c500240100d50380301e81c1b0303000b140030940f41c0300c1f00c00d8465010078014010046569030311a4500e601801045045a90084400e8000040b141107400560081c1c0d4044440c0fa403604916006951500042c02c01c00f103400d400181c5038944007400803e0580d8603492010942c01c003170343d8400414040d0050703842040140364840e540e0032503140000181d820407500038242600d400d401064050380c0500030011848880d0007842055180c1911141005080e5125102c95000b00031000081c1e02400c0c07036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 469558210 1250 469556960 469556977
    0x103020d1103010504120207080105010302060f0f0f0d0c030e160b25050c03070e0f0c0a0e04050f010f0b04080304180b0a081f091509061803020a0b09030906030c 71
    0xd4540070054003012034252482602c0c1101d01705107146e2941c401a07810801040180b06000003805035500d1900890401c2c400c00ca488103400750009840100301601004a03091036540540c842e603695a03010000c2c0c001c00710800c0280000341000003031031200e24002503040320b090710402d54400c203d2520143c94801da00c0300346403901311300d03603003082c81000d40c0601501d0310101c0c081d02c0030305050480c4100b01340c2801c01d03030f400490148035803200744a5800801c1c1c032041d920140140c9a00d84d0307152034607820390302201c0924441e54458217050820140a030b00c105801e040312503021136200c9140c1c8075804600180034500402c40d0701c0c2d000f07000c1081150421300c1c00108a809400c800521100b912020a45071041500481495400224070b480100344039440000700c91806081006080041c1c0c1e203000c50540d00c804044401611020480240074440e401000590b034980700c41d10400e00e070740c9406034032140030103019a4070200ea0400541d8200000c822a1100c480003400d00d451617551009d82181900983c45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 469559460 1250 469558210 469558223
    0xf08070306211202010905280b011d071d0405040213020f0a020f1b01031d0d17060405010e010308130803040b0913090302030f0d02190e0a0801060602060103020d 71
    0x80015070b0098804400a804921000844200700b040c01c207410800740c10700e00030003103a140035101c6010503c04a49050001103462114500204007a5640140c1c40031800c05060070740e0550000401e040c09605000f00c2c060b0505c00c9070312a03500c010b801d90f142007080710301c0c08184480d922032083d64585175005992141c0b0007850303c040031161911400482c0c00004103280f14000000703c070303030000d50100324401503143e580d0028000c540007c0c00742c80d050001d00403054140360312550303491110081d600038052485d110100300c50710559200e5004054500d80d00000409011202c08240207042074003606051f244400c400380b46991850b41ca40000da1f100d41003080064a24000c01f00c1c51403000e00c010401800c50100b59500d4007010010800400808802c29041525110824000a0300403007a00d40280060039800d480701c41a2040001030700c50418074101400b60b000e46600a982c0100001404041c142c9004901d5503c13003d2035422500c0c0d40c0900303005a404580100018a403500704040d1980c450030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 469560710 1250 469559460 469559471
    0xd02060708070305090307120507030311010b191e0e0429015303040801050c030103060501050321030402010e100c0b071805100c0f1104050f06010f080703 68
    0x2100c00c1c2894024041c101c0018000140074903d902c0d00b0424000501900341ca8202c52207229550560baa000d070384402000d00182014034401100203611030b05c6407150107060708030f5501042c0c081d282005841c1c0a8030300020703c20400c80c20f91400001421080e80d4070b1000f1800d03241c40d13135120408021803407000c82e18030740e400d80e181c00d607402d080c410203900034000c01c0c03482c1000190b12340d2001d4400311440030301640c3c01c004801d0b010042200c0140c1e08a41220394131040d000d80c50348400070b4214400c94006100c90f60030305040c0180494464000e50480380200004c1203e45d8883c0101620344240c0c902e030401c01000a220700b40e41c40508001035800c00d03c141403c50381010200045030300d016140300440c0106501031504828003000c652040c1e40b0014a14024401801d11000c40c0103e0301d480c051107000f003913807110320801607010701400072281c0e0300504298004480791600980c00180f01385428011410000030505040741c0c2400742d401008140c440d441442c4426108980590300104448205601d84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 469561960 1250 469560710 469560713
    0x9061204050a1a0601080f07021b011101020f03090706020d020a170d1e0f2313080f0a020c0f090703020304380108060403140d06050604121e020f0d020607 68
    0x343c14103c40c40c034107280032079440c50300c40005404080010b011685120b146010440070342c1c2e010409542c062000000c1a108554a00040300c11809000d01501c0b190720000d005a45401110080d501c50b1180c3d8003220702080c2c40b807504076100d5a08442490260f07010002020010f109040f0003c81041c2d4002507030709021341101900103882c0140a00042d80e0a140440c5540809900400401c0c44000506000170400380c0740c19101094140380c82844e40c2480008120801401ea0155541981001c1c42c1512142d10700700710741d403990110585401620468000c007007107080c11400c0219102008019080700d64903201c01b500030b0741c0018411280c042090120038659414441500da054842c028a58001c03600d0b4007546500315070603080180e042d408481040006680604c103104600320403111309465070706444124000d445903420003903105402040c0460113401c40011050300c135005940c15160807001c103140300d0003501d04a070040d400c035000c00e882e800c4c14200b40c10100d4880e880641000d250611a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 469563210 1250 469561960 469561973
    0x312030c0c0703030305010303081f050f030a05010911010f021f0b0d0f0503031506030c070807080403062a05090a210c0e011d1608060a080d030f1109061204050a 71
    0x181c00484c04079a0f80e600520078140d0160900754801030010a41d80540e03c0d94102c3c14540e01035100c0e4621510450781c582069483c207001c0e9001c640d9000009014404582c0b410900030110200014005900c503260394406520020700d2004001c14a21548009107180c064640603041912310190850581d503c1d407000280400c8070180c10070b024601035912410564541e81c41a06090015445020240148580b0101d020308542c40755a20401c3c0d0307591000d031407400303a40074041d50780050706031442e19482c0d624092200100d2203c1d0301900490302403d28402c00705a8140c06003142d0a5008141000180210b40c244024009121441800141e0f020080e9442c0302618803190850b40e501010703840108040c2401c0d0591107004012803c1403e0755160082603200d030b0f000704c00c03c807004115440c804038609803500c0303010074003400d0000151803014010000c05000b07016482e805494035858040d51001045200d81a2490f80c00700405161500510200c0d400c690134014200307032a00e010381c20803400090070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 469564460 1250 469563210 469563223
    0xe061006230a0f1e02060f070905031005150d0f1202010621060606020607020d0c020a0302090406090201090501031a0603090709020a0c050105070203160209090106080d0c0219050312030c0c 83
    0xc80c0d0f545000d004401d1000415483c0c542d41200200760f02034030f44540c2140c022582551200c0685030701c02c2d242d6514541180d00c070500754071441d05801103c0000b500901150040c0340710302e6001c8803d481807000c01c402d020f001210124050f01003035418180100040c1c6d01c0291140b0f41001d0320000c21265280d041c83d408108080040c01421501030215104101310760240c5401006039002510b0f140c5816100a5112110591f6440c1000701c480041e5086540707201c603e0010b141c024000d082c00d440c0c10310308100181407546050380803500301000018958440c0c0101c1d80412500058240d04e018120300344140d40d007000e0000e8400e8041c844001c1001e458610140080c48855078503040036400c14242a42150800b8080001310742081000100d00b00c4001041c2e250307598180d41c440704954a0001c01c03801441250800030f024002d503d21001e155a00c20309002a5900840e03601004018043c20700030300d0100c520555415420100d164100b9030408006194055000325526240401c1104114100709 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 469565710 1250 469564460 469564477
    0xb1b0d02071104060602070518070215040c0810060513060f14012d090602030405220f0603060e0115050f0d050f07080a0b09030a02120d02090409050109060e06100623 73
    0x1f4401c140401c8035180c6500c0f504501c5444150450060428410094030f0702c00001403800300c415035101007410010384c8072000000b841c5a0054070810070001d941000504814450148140d00c03882202191418610940044030151850f9003a100d18060940d4240505044040c0c14004076100341e0015a04d2a142035401c0300c003d41c00c1e6007014800c03010103460440b05030403400840d0710a0000740300702d4461020503e0b14480e014141e589003480306480d40050501079481707008682c00e100c00003003000400e030841440840000028014a003020103980482200c511825504c0000c26020395010308104007444925070090b0140c80700b9082a02d01c403840c00301c02d41d0001030b6551040042109018008510540210381c40014500d05200640002d5903031022400a8440050010700803080c03d20b981d045880540300548184051561401d1850003010780c40e0041d00c00320300b040710345c928020011401e14852440c83d05c3c40300845003005030841d60540080f0f100c1516456410002c20348103801340280811a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 469566960 1250 469565710 469565713
    0x504060e0f0f06060105030a110a030f18113c01090f0608040b10080a0c051005070201080a0e030906030c030403030605150f1c060f030b1b0d02071104060602 69
    0x80e00204401071030000c0c0e80000c45001c1d0050310002c0a01c00000c540f0b9130300720000346041c944030341328008042d00503c102e40b0742191091000403e0142c50343c02d90030120b0740411691003000040c00082e54036401c8400110018007110b10000d00c14450701e0060400740324511001030000e44122400c0600070b9503c2264a821202c0302c0c18070440da00c540e40504120b014195081c101c590300b610b01b180140a003880544001c100012801c00241e071049020045401014581e0840718031010a06101c4041840c0b802001c1c000e01001515001c15802281155a000ea0607940c06072540d0b61101484002e1051f6034250b8850701040042d80d085a9680c4050350262183d40d0b40c0d21741e80e0500c2d02d0054100c400982c0218015030101c0014221000803009641d540303e00703c50320907a86d4103050a030b080000b5040c6c00161540d881c1c000b0204a000000b144002a01d224810400403a1030700440703282c3c882c40909961800403010031078002e4469260b00504801031040c035030a070f20804408002410384030310380c1007040103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 469568210 1250 469566960 469566971
    0x30303040507180204030f140a05120d14071b0809060a0504090b0409110f01030b0a0306020c0609010605031c0201150311040f0218010e06040306150603050106020d0e13020d050406 79
    0x800300c6103000190703d41c2440c58214940351940d641c960542180c03c07030152400e59074002043c40a40c05000c00d007107841c0c0c0041940c04211021040841035007000907041681450f04421142c900c401d846601d000b03400e16101c00c0e10545250f01501c852008500f01100e0006d018041c8610b1516404040c005000c0a510b03155191810000384030304407030050b0701c0c40d44280d06012040c00495006003107014540410f543c4640d00301c64150068018020392201c0d01c1d0002801100082400240d0340030f0318418003410240c5081d61205800b2b1400e94803d8012a40d00d03030000821050b0380c0c0c0551400ca078480201b40000b01c0c2c0b11032000040c0f403083c0142d910517964030790111200001440c062040506008d4102021814111a100702c51007820300c400103107042c0480c1200b051050f6455500740c50007154414410721010584c1c1d030044054102c540700300c40100f41800001701d030040c00426020044205aa01d078520200184108140f441c00c00c080030718820341c200b0103070408910300e01403d885a402130303401082c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 469569460 1250 469568210 469568219
    0x5070506070f1b031409041d0f0706090303080703020a0908010504120315030b160309050d0521060303030a110405060d561e0f01020d0509091302030303040507 70
    0x100d89070815182d801e4400b031002c800004c1c1e04450849030351010200e02076101c081c036802280050001c070100300305112903050308086607503000580448007095401070760794a42e608d80040e11240e09a000c000c0100b0104130000314624482d601400d100d90035850300300b00003582e484003d400c454040d1404c2d03407002c5428090296090701070040c452000021300d1400c06c13442c65500c1d81c2418600c007400481c000301c0c00c2501d85030030911070b03080700b00d0594011060b201d04031030396800500700343e00c40c3d241c01c1e9805503903404012012100307009440c410f10380a0017640ca541d541140c00380c010801d01103400c4020600744000b1402e600c503000a080c01410120300041c04840d10041c9440007060034265000c0716280c0e031110b14619986a000429020402a50904a110040c1c0c103542e207131200c00601360083d00000c8500e002c4142020305188061003641c007081c14994002c01240c403030700600c90520105008211011440c1480030f440c90780901050883d03d00000164002800d580c8141c0e4159251b5020102c20701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 469570710 1250 469569460 469569467
    0x6053a030e1e0103050c0a050409020d020c0102040b19081e0601023415091205030412061b11061501020c040e0705030f0703172104030504090b06070f08030705070506070f 75
    0x20781051001e21b1b1103042c2401400700406501c5180603240780a40c020034240c440300600e4041d00c140a440000079920b41c2d4076160b682c03209403c000020031410351980f030001d07c400d00454409014840342c480302c0881c04506400030101a0025010034114803c00c04804403407500d10218545107045851140c8061803444003016590009801000158001d00807141e180340d0000c1510049070804c600c202c0035a11181041030030b40c0156400582c1c1c2038095004a81001051350000c020440168450014050320307003070460321400704140d555030b25406400032030030980b100030706a21300d00f0381403040300c6003900c800d40424151900d050740d0011650000c101446546818040944540031201c0108425840d6448609454074050001c014100380050580c4860301414000104000c59060b107030054240340c500100a513009200380c05200f031400242420b10716008003220049074200461184c80c166544800ca00795001801391428050308029007400920b040c003229102d005603440d000d038404010301025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 469571960 1250 469570710 469570721
    0x702010f050606070201080415050901060f120f1e0203010e0601090606050a020714121504031b050601030b06061c090b070f051903061806053a030e1e0103 68
    0x240da6081c10a020005942c4848095072882a02440c00902d0b5403154105501618216003040300f00501b0001040712a42e0150400070440f039800122014455444049014106a000d0f0041c44120140d1a28020079407044550701d84203c04091504a00326030750000782182c4c0c031400013500f0f0b41c2040004021ba00348520600e0010310260800d103103055000f41e0001d4644909002d07811400b48141a60340b0350361106285070750955007220845080c88098000d005c20315004507412800101c2d0306665203400600c08042c2c0e03071841c1c1e1200c01004030742d0031a9034031035021100800040d0003100511454114101c5a0882c110b50540803100083d030540e1820031080c0c02e0300003001b0700c090040415103004035681c4482248d03850082c40d00442c2c008440c104040f80580101d81c40014100741c5080b10000a20683c0d00003000c451040b58964003142c0e4812011903030a00c02c0c42202544503014100700c80706240c00c207080c40316510900d451003030240d118002680004000c2c1035002c00500c6000c82010950700b51041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 469573210 1250 469571960 469571981
    0x4030c08010518030f2203030c05060108010b01051204080909040f050d050909070e0d02030d0e03060a0b06031612051e07020c15071b140a0608010b0307140d0e06070201 74
    0x540c0074110b80e80340c3d250342e910503402910b00d401c40004510a401c1e21000c01c040f0b01d91079a5022255071075803814000c101e0603141d01e06460307600500c400010f030a2414400d403540174406071261401c0080203c14902c4241006000b51807003d010019501c0c40d68840c00c8252241e8850f459054041d130350381c2485440c04d022000320750b09101c420001103629503101000e40d0b41c40b884a11303000b6050402d80011a000010120000350144110286000c40c00d4004801d10040316051741241c0859031820030710070549459510298001e841080891098200980c90402c003100500b8001c454526400d2a24110342040b0382c8140f1a41c04100390550010042e162207070001c04c94401820f5074014000001d20700540d281d20b180c218800003d08404018488483d141e00e0580200b1034403d00e580c40b8060341c1000e0000400758400c0c10700500126015025100c0c0328140ca0940c0c0314541144c1d6942415501014401a043e034695414040505660a5400303401c036480d24100c0a07108604000c1c2000c0c1c00e44812808 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 469574460 1250 469573210 469573231
    0x260d080708010902280509010e031c11070f141503090706230d050411031c050d02091f0809030a020a0615050904030504060f0906050d0905011104030c080105 69
    0x280921281d221070168190b40710300d80010399800c140c0e880d80009100c181c5c2c80d010a2205d448a41141c1c4e50010081c11600344c00ba25115100110b0200b01a1140d175080d034140d18801c1c0220b61705010078410702829841031200300c225900c40340c642405540c5001240c4c040c0ca60f90b420380608007c58240501c01005000301e41a029055050110045403a060a4020b007010080c50410402d04004440c105400904025405a641d1110203e04101404c0d0484003a5210310000700d800303d00d0704000074082041040440185a82e0482c2141114164850131003654515000d005048080da03442486140000222440c00740040a0301d4001d010040018443d604c0e9030802d0000c491100d0700403640400c016480f10b000680344140e65050400826141c0155400c85c003490304010815070404001c2c010340d600c60b210780400c0300503401c003260244054050800021030501031241c1444094008505081c456000414010307204000200641c006600542d0f0300403010604019605081c4942500000c6004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 469575710 1250 469574460 469574477
    0x1b090923030a0c060605060f1206010c03050d200c010b04050702010c1b0c0b0310030b0c040f0302100207030b1003020f0a0503070308031323010b37260d 67
    0x1840e06440340110281002400403c2c0c0c008002c008160748480041e00d001030416444c0d401140400c42c458100300c0d02d802603250710102144080d80920052550350354159182450b2442c5804a64041d0101c0360080c031944080c0c02e102240007030810b000c0d000c4641003000014000141c001000166000030f0072450959140501c50303019140d000729103103030040300701d0a58020a81c481c90300d41c4a03c29254007011200c54040140001d0b82d1200f2a0801100e0050030541c105894504000c0304a01c658800c06102240342541000181088400c01034603804e40c1c01074a41b401d5032034659207d050421034000d10101d05610041c4118684440c28501003070090f58103410090800d0b01180e569135003400302034080b00c00440010410081003140d920400c0d030000d2804241d055180580d41e40032589468045194200461344100341854146201b08000c1c498040042584040380507500c80c86900320ac0072080d03002d60000c40c40300002c0c04062082c08204c0407003d00e42400c901c042d4202007010b0b40000401a901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 469576960 1250 469575710 469575773
    0x6060a0c1505060906090f3904030309090b0a140d050a060608160803040603050c16030305011d070e0108100321080c0c030a0f0309060c1701060c050a0602071b0909 72
    0x7c07108944c0403201600b0a400c1d91300b18000301e07100962a0304815440f1504003041c40340304444034058006c4a1181c4c40702c0b0320030303034031400c540082d1168080002c0c0c01509045041010268400c4042d900b0100500100000308080c0c6646040090350b0b44140c444507166082041030b0141001084200929035441034051420050f001e9203d12031442500c081646420100710001c0552084a4045c0400d607940c0c80b207555680341c064080c0c0024820030084044100035000d500c910f441032548681d81543d0346c0c120004c80480159207509002c1d051500bc146a4030300840080c440032501000c02d8642d03c080c8045002c6007100901401c8020010164078400f40142c13900200700006440f203c2042e0b040c034411488244904400178005020041c1640e400c0142d8001500d404c5402001035050f41078400b0030340d0307803a070205945405090400a155504c8030103484e0101300143c1c0503220aa01c41c0040c192020446004c981410800e90820790089985405143c09c0100c00314002465101c081c1000c80010040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 469578210 1250 469576960 469576981
    0xd0e011406030f0a060e12070308072a06050411150909060307051e0312031906051207050409020d082a010b09010501050d15140109050604030b06060a0c150506090609 73
    0x84a01c000c005948800c0c0c001e1015809020302c070356400013402c07d162151000e0400800d01282070340c011011407140400203010008925170354548043c4101c0100801d400c41c5e8445c00209002070080da6090b6801584109030340e148100841c5203483c1e009441c0e200d000e01030070080c0d080c6000d08464800d0b88038060401c820340320042c420110142581081d90302c2001070000c2800c3c8039031424414203a280010802501c1064400c2020040b00d4003541004640c0c0c4034028407011480900001285511040c0d04015519050b008048039901c06480e081c003420565564003003e8000c09805d91141000908495003d418000803100342c2082310001c3c0801140140444c101203010b00425041100000e00c0701040625500b02e0800d40140302d413209207071035a0751104409107400d40c40d0540081c14054001030640740900544040d05c0c8c0002000300c0d0360b10341c0c10410400382e10080205040c049080a840c000c100c3c1002d960784982ca0704200450285418020000395000c0182224821588170b428001007410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 469579460 1250 469578210 469578223
    0xf030f0b1f09091a0705040510020307060c020303010303180303080a0b0102010e070803041701060b03151f08010e010608040b04060c020f0f0d0206070c1e03050d0e011406030f 77
    0x401001001650300c1d401c812540c00c90381148031a040101c044400507a020b42c1d076202400d680e024100340c1c0301080c0000d02e400b8100e0015188407000400501c000d22980c6080301107140b00030b80c1401242d14000141c2c1d00c603010381d601541008056000400108180b41d0400040100c912840e82c0c901001c0342590ba001d4003804024101d4140c103541d500107600f45034004d60000110410b035204a803a00340c0e46000c0c0030781d20350082c0902c0e05008010108041c03009014040c813010f441441d101c1605554401f0b014580c0049203941c850b600500850400f0b201074001405074410002e143e940d81046d42c10310204007818a010b030b028100b000301600810001c00c984000b1180c00990100c40444d126040300c904a2404403c403000302d1140c0205100f00745207a0000800c585160859001c1d280c483d6a504029220210b90440281040c50010404a5001d410314041d548041c402c0c1011030130300c8001c44c401401c581d0b0364019540660343d02c0b811b8003420100e854103180d001c50210010800d0400076010b842d16042d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 469580710 1250 469579460 469579463
    0x61b040b0f0d092a0f0509040203120a05030a060b070201020307021201200c06090105010305070e0a021b0109052820060304053a0e01020a1205070209010f030f 70
    0x501040c502074108000048800482c0420380910603078201e4204000040e1225221401d134528200894a0324800c20380c0c0c807021a2a501da221540d03034902401e00402000080c012a40340c001d20741001c1107980c014001d442441c80e0f0350740e526204c0ca4003618042c00c8400e03a41181d40000130510011006030f900000310351600f6419036010700c45911070064a4050703c003402048048019030040c21100c4003900010b0400b000040f41100c9164417440d050b40c3c2251030a00001c0d0043c1c1040f1424018105a100f0f00742d0081e42040c40140362080c0001c00c101d80c0c202c21211600565101e00d201824000100603900d01d907201088415244040304501e00707460144050010202083d481e130000d40941580c00c00d400e03980e80174000c541d49190601d0101d448107000802400580b46420125612031b01e103803800a007041070f02e000b0341c00c00c05404406650f50780006c0da04504500c140d000c02c10011b8003030a08400209100e1701d402d52245441e104001211405030024180000300520800c045002c40c0740341207009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 469581960 1250 469580710 469580729
    0x40b090a0b0a150314010f0f020301060503040f03090e07080f090c091b090405041b0f080c041a0307180606020a0215160b09060609090c0d060e03090301110903061b04 73
    0x14030207010903a0070074085070b00240c1928820940031040150641080d100380080d40c908002410504517808d04070301003801200e000039030500010f000651a0342c40041102d01074284080f20640d11004085c040c41d08442c1d0400081114003840010400d0400840d0841e07100400b50205152110104600e000020020441e01064a10304000c4085850840d07003403240252060000e8505820441510000c02e0000e4000140b104800210940d002c0040c0003640e01500103400081d51550400004e003e982c075a0340e0542003059401103d13580d0412804004080090303101d0250326070845000c0c1200c1580d40010195007190100b81c00503a80c0c0030316103071640d2111409580342d8560a060380000000070500502180494083c03140b540b4000403418490801100c11404682d20190f04030b88a040000c0d5850708440c80280160029400382c100c0d00301c0b1b4080000700c0f130514020000203829140107a000c804d41e500000b498030304604080c0700701680428100488543c00c2842d214450842c440c0384a42a00c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 469583210 1250 469581960 469581971
    0x2060601171e01080109030f020f0304050906041d01050603010605125101060c0209190f021c24090e010914010c09060e030703032a0b040b090a0b0a 65
    0x540c009100700b80c1c035144442914207a03684030b400503070081c11110310540105000b050402c003000e10000d007101002142c1c801442c20180b0742003e0100340d080c00740c25168040c1d00c0f450030791030350203080d4004083c0d00408400031540b410054141421520a50003241c02411505800c0759480400030310b0303002d10800030039a003080c1220381e03609481040d44c1c5011102c44400c0e6050200c2e0300078070307070a486c422020200c00e0310046903a541c0e0705481024101d88005e400260580001e03042e4481c14031104413040d68440003145ca2200025070008036400140b480d155600c0781d000c402022140be2003a51001281311210b80720114555500345e03540c0c0380c40d1103100d07441034695140c0310b40d10310b083d048103900b9613100500c1c2800b020404280b030b0181c081c450440707000400705540060000d1058103d44881480900500449415514210380c025205600b215200004520400b5905a4001500710250051988841034103051034450000f203800b5000c415180c3c000c6803141c0114480203455a04404880c000041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 469584460 1250 469583210 469583221
    0x90203010b070221070e0415140106050714330f0408180a0f060206071e050f040b0315030d02011109091503121324050a0507050a0302010b09070206060117 68
    0xc0051300c3d61390ba9040d50042e03d10004400c00c0e0b100750507000d50711a0548084410404000900b2104144040e4407200b10000040210b240900014948540111495441090a40321080c40d0640382103065580149036441c01905540000032010070b684014031680c2c490404a0784c08003880d101610160020100043d10240c0034441c004100003080c3c0648030130580c0b41e951040084a8400c1c1c071662000d401250000740307546100b02d540c0980c000c40340b98030f009d1414070110101c2e6550001d40d0061568081044041030040e541800b4500c10b04008282c00a14500c540515080c0f001d055500710035a03041c0011108220090000c0c0d03844030905603103059039940d6064100790002400c0344040c0d054000e04a8040d4400da4010080502c8075801010410700341d0b886903500c0d071428034444140e0fa540070b09250f00754502e100300001d20303240106103003003410401030f0b49032030381801c007010012805170f1f6448a290b070b100c0c102804815403041090022f802c00b0300c0c08400107050183c54154003095902602c3c005203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 469585710 1250 469584460 469584499
    0x51c0908151518070c0204060e040b0403031e2c160e0a0209180601020d020a0203100b0a1a03060108010b18010807110304090e2514060d02030c070c090203010b0702 72
    0x842c07009045840d503445013450f502c040d05044840302c1c180d0107503040880108800558000c900e003d9940510303440010364864804400420300360403114480c0c0365100b84d41d0400c400d680140101c450805440802440308545011001009804140902d4120798005401001c001c0c56103005c50300c00310508800e90352001071803802449403143c6203a0194400d00843c4000c58a511194407645081c2c080b2000071032003000507030749e901202d031f0001d6040d408540141c8011421b900080c281d9503000e0110300a441d12014944005803000381c86040300080803040255540e40101024010101c21294626050000d42c41c0c10142d80307428605818808000c0114186510a941c00d1039030a4050003070380e032070300d48800055001e80f65400500100384941154681d6a05a0904030103070030690003100d91425240c80e02581540c0704062005601001c14800800d45c24443c2c00203500ca01c4414113015518417491038400c000e043d142c1c00600c2c40d148140014407000391400202e0b00400d40486400d010841846a0749 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 469586960 1250 469585710 469585729
    0x301170a0602040e0a0f02040b0a0c05010603080f0d06050409031202210916050414130f0204060b0a12290d08131d060a0605070201020a051c09081515 66
    0x400c41440000c3c0018107007101c090715406040605014844e03a11161030003020ba00607030184404802c000c1001c0c811703460007000c4981d61540b0a034000b0071681d83c0d9407034076031664100c003c5a0b44110070010314801484118411080600f40482d010024266a40c400400c0e0404e813400305d840d50703607000550184040c03200d80b00d5401c1094555104005d45014030038941c68425011003148231501110340455686003c1c0507200074001c12044100da81d6a80820b0981c0002c81e000b42540c01c80c00607441d0707a025840328011480a0070442c03034820343d18080120000d18003500ca00071503d005107440d9021803a08001f104150242ca020511215060228000603a40c2c0c00a0b0308020240c00b00002c4101500c41c1c04580002202c3c000c0346440c20b01030462a006c038400704111402540304140390010300c40301d40500050080c550049c8100c030a40d03071081c1d07a241e2030641c1c0340c0214a0b01c04001445414907030b41c006407140107007600d10054001da0915007130801c040c207000b40480303004050030505804581c4511109 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 469588210 1250 469586960 469586963
    0x3080c090a0f050102011112040807150e071d040327050d060e3304080d050a05060909031e0318060103060501030b0a0504020306130503040906062f030301170a 70
    0xc0d4202182c0e503440034100450140b00b128059400d28403010014030843c8142e9400408407401446180d0300e950381d03850981e0000008507110301080308000283c060601c41d01d60b2078a070f84001460703c541807032009940308901110325030a00d0340d00003c200001e03502049181503075009040428005c000c0800c1d03c040d05032a42c101d640c00ca44405203400c01c0c080582c0043c01210101803d681c529030b414454000c109061410381d00181e14107101100c0c0c0540e4000344d1075030003801982a80d01706400301c500e12041d114143c1d4a2940f2a440d5000c1c41514642a104660040002402945407100401c200240851810240707280c124011000a01246200c1d000d0054418404141d0300c166841c3c1c50300e03500404080c003095520003228800240444424407840d405603070020003c01d400c2d0340d117501a43c1103c100ea101110b0900040c840020224001e000b1480a001203403910001003c1414002d03032400e8460041d07180400065030f43d0f8442010210840c2c1c1501c5070341001a00c00403003088450700e401c000050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 469589460 1250 469588210 469588219
    0x20c040c1e0903060509120a110304170d0e0402090307060c0813030311060610050304080706061e06020c0607120c0804150c120f020c040f0b09150108090a0b0403080c09 74
    0xd280c07a4455102e071040090301c0c0b10b140c0420150700d500c00e000399290003070b00d01401d000c0c0e000c0004c1c591080c00f0b0764500c5040240c01080341d242c00d440e40c00d1805090b03400d03904d05c0b020383c0c030955001d81429084030182074180c0040d54218100305003480042d903650b509210b004180000c183c0e4002c2882400d004448404a084400303030303000c2c0d550f450b00a1200c80c2c0d00368041950700400c0e0110741e83c2e2508080c6180d882546135a42404c5031140e4880312000d80c0920780c1202d2070350749c4060004c8c4900703488030b480c900646886021040e0f2450300320041e0801c0c0303003a9202c910640007042000002842c0c1c00d003d2200b1402441c01340c0c1c41070200d02d03144107288515004501800741400142303981070b038845890703040144652100107442d0000f00c03007640d08020b440c0812025801c6141004054103165112406001081c480491700c110a40007158042400340c0da049100c8180c10061038807035801c006066000b0070350b0002071441400c00d032580042c214001c0c0c0000d04010300740d40460020210402940d151440050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 469590710 1250 469589460 469589507
    0x90501020c0a120c0503040306050916060e031002040e0c03130515180d120c03060504060e060414010609060305071e170115080621160311060a020c040c 67
    0x7203042d0745104107082252001554402c039010307a40b00d8900041a250b000c0011421300d030842d51018080c2c81c0082007000300c0d10840b00600c1c44448075203405030080c4002d40726548c90166079814541860ba01c29114100140100402c0081c40010400300781e00c8080194201e0700c07600d503500d03100c0500c200c0c800050070b288076850800c00301c00c180c05102c9009030200b180c40c0c02d1104401c03c2d4031786c444001b80380400106080200803603040615400180050f4070030324001032a00d84500000302140e03815000305403140f07429403c020751402d09205071035104c0f200a018200135850b00c10010301e441070078001c02d4100341c0c07900045918603001e4400425049090300451008402c5001c000f810701c4003000c1d0350088080240000501c5250311040e6141340d640d1a580c1e030303100341d0700c1c1d03811310003403c010006032880000c05518a103003520040c0480d80f0782d5907920711945d1001c1c1c80c6003882d05440e81c01461007803040d40d04001c042c1c540707500002c007002640b10940b00405c80c4101018180d5203100b41c91010f840056072030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 469591960 1250 469590710 469590727
    0xb04060b0c0f010501060c03080f0403180b04330c15020d020c0c010801290d06080a03020c0102010218190f09090c120203070e18010204030f0201120b0f0f010309050102 74
    0x11422040382c101c104002c200c2d0380c1c0da40c402250300780b107070341d201401052440c40422111016484016801400b906054501901d49101400c0001181d032002c40042d001280034440c01000c000c1001c401820b0f13442c00013000b05850f156950300690b80e1a1a020f0010200c07480c000c006461000343c0b8280010a000c5454481e00041480690b100d8502c006c05070084045c4040c00c1d6014040d40e034140c03003801c00142240703810003804108892040248080500c428002c1007034401407402194060300102014010020071454080d29101c00c40103020305690051283c0200742180800d8250050390444002a4404c8414410300c4503603221307001400640792114010070b400d081030f004000110310500e04450307460340d02d1079084148219900001d616410403c030811480031100362301d0760046003c07460070411420703038944171703003264030075441118400560f10245065603000008844807140289003800030080880008240e140c03914041da00c40c29456480c00d011b41d11a50200d450380780c0c07200c003c640e0340c50034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 469593210 1250 469591960 469591963
    0x7081207060b04110a1239020304060e011b050111091914060906120103300804060e120409090b131203050a0e0610030b0106031a040b04060b0c 63
    0x240a507000c41c1000088a031500301803291104801d0842e02c4207050980613001141d0840161080e1039229495141000d80f5150306d20380540d80c42c44600100c0140c0311041003c441942d2010102d81c190740060008004141d00b11107031100c0b01100746012941480016842e0814480d240b80140042d803801c00140c1c0e80d0b411079801000305490480e0045004044941001c103c14954090011905030b6400780f4102406d00c0c402800f8107500040040742080c006034000c2d80c0c0700c1d1090344203036a8401610150b2402242070b13040100d2070804da461803240743c840c0c180c0280600c04040d0004100c5903550702001c2c0d400c00d0034007c04445141416040703558640e5582c00c000070b0110a00160746900002001c60a0220840e03060045142d1250030100240c03200071003500100002400300c0407032522418a403000c01c3c400d20203c0e110b0044134604400c407d0860070442586e90050700040c00340342c6031080c0c00804400d28090503c0c80350048401007880504403003c54050019503100e186018400b10710071155540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 469594460 1250 469593210 469593217
    0x9060d051507080a0b0d020906040b060a02030d18020f1908071e0915141309141c020c040f02040f081b04020307092315071403040302031c02070812 65
    0x2420f0760303a1400c1c0d40300c0d07512020807642d40319022a40000070b0098040142441c01d5040c0d88001c0052000908080102c0440c940b41d000350541d0700180c0000500300040b0000b48500c082c080c3c10301070322076000f01459010035000c91034403c039507100300310341700360701c1e19585a64140c400505030b40015030321529928544040c011a49041310121b0070a42900800c1506081c4078a005900303840c2d04064003a46411000851010070300c100320b030880a226554000400640221450a44600e0040c01c0c261210760f583c5060902114080740c20f030074106030403c1d040358001495a08810201c1e4002049410940e6800c0244590340c003414a20700750710f000003240b8a000c90548001d540c2d0342940104020000e04101c03c034442141c4100104811040070300220182020003400410a03070016030b01050b01c00009114911200b00c00820184005424030412001180c5d10600d10700c0c101c0114181400d580c0000c0d03e98400803043c901c20801040300e00c0149108216403001407010741c040d51030801e9410072140c00b41d403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 469595710 1250 469594460 469594471
    0x10e150904050a1b082506080408120123030705031c0c0b090708060a0203010e0415020c0709150b1207050901020703140d030b030303100308160204051602210909060d0515 75
    0x9416103041c2d05d180005101d403004d041b540c124210883c14803800b40c0306500c010f003095590310303001d2010600e4422102c189502906950301800b65030750682c5d1201241c03e2603240d941d402500214030401c91078500203441008442c5414403180900c060240c00c444540d41400050a411121410b02a010202184101c1515400d20a1368042e98443c0805800c0c0e11080c86102710185401000601140e01390420384040542070201514012103c04450b107000404c4d0402e0382c529a40d8420820040c4074040c10074010b054401c040b90401843c0342c03000010060040014040c0500021410380f147e101703214140207150f10450014020f036030380f44001d80e941550303441c4030007282c0350072032250941c600013050303034426010201440c10b03290843c0c0c0c409201e900089094007402e042802c1c8200143d4580c09080c0c85411051710103146420203400082c94283d45911140b02041900d90703130700074a018601180c100d107070191400780c20307611303138601054071314203050000341031f50054207038000380c004919070014001d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 469596960 1250 469595710 469595713
    0x1203090d0807080601050a050c0f010501061107032a08100c080708060f10030b060c1b090402330304080a03050c0c0d030506030102131805010e150904050a1b08 70
    0x25980c85400d503541c8109440600100380f200d40050305540c0311b0b2008024205851900c0360400303030b40c0c100540c509035201c0b40c24801a516800184502c0782e02501740244102c4c402c008283d01440e42d02d8454080041c10243e0b4109481c5400143c00c0e605c00c208070340002d000360310445400d08030100c44071008000558680000450200108024600c100c00080c0039400040548203001a01c20400059245080b2507009041d1a20413400c4144c2e41c00c0003411382c2c1001000604258071000101c103100c04244142d00e4410010002440b0251322500120800002012540c5840000b404428404425002c504d001e000c0e40001c100300030400b010002d0014403500d17072011b02c015110489401c43c01d02401c1c00039070060740304c1c210400761071b8071a804c00340d04010040d00041c501400002900340105950b0000c10315013554008101001000e44a00d600601c2c111000d18400c1c10719030508407483e4482410a40711340c1c1c0030404a418844244115500c0c0750b0b000396a004120305121900c074001d0740c140f0075040203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 469598210 1250 469596960 469596973
    0xd021002030406030b1008061903120c03020f0f07061d150c010b0f090a020d0612060c09140607080d231801020f0904110408030d061401050a0206061c0203120309 71
    0x1030806c207521640c514810b40714048580e59420500c649001c80d802d2500f510081c00000202081000301c3d0351008000c0d0795035011041c0c4c06805d0107860880305029000c581c0d480707200780241c101408155181a211545081481d4002e03240159800a08000000390300c01032031461200451044001000b01c034450714000c1c000d0509031020031410304070715901c3c81d802c600c102e0001349440b04183e00034044420200c80c009030454540c01210703200d84c405c002c203d5410340d071555101d05040d00301c00d00a0040400c01e502d0f1083c0110a8003094260041d264000d089402c0800c0b00d00076104a60011071540310030541e1007035019503682d200740800d641655403040c1c0441810350048022018000c440b517185802600c145400e5481d01440b0003020403009000002a0a101c0422010390600041822210200380401d00c0340c20030600340c00701503211221074180f19040002940994001ca0703140d5024000701c90321584104000c0802071812a02d401c029858003542e200076000305142d1010b14003d40640088411303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 469599460 1250 469598210 469598231
    0x80601120c05040e100f0e07030f05060f090307082a46030c1209050126190b0d030203031b0309070e060d0609110f061305060304020d02100203040603 66
    0x3c444401001c0b64040d0019941040c206502d500490004048107000007800a5415a40d88c14803019800403100c9440c0103c440050007000c00005822082c0b4400e481e01600745290415642d109110f40200342880c0490440203100c80c43d550b601c02c0c1020350007200040407584404075100d118029192040100c0075000801c0340700d0780000c0c00030000c00d0146074942c40426500c81014070100540c200e041010218460b00001da50031442034517101c1c151035071019981010005410b400c02c1040001c40108801d0740c0302000c0200d007139165007004503950420030221015480d40c000d400604030301500841c0c113100040815900200451285052500a0004002038a0104602c2c031094400c0c40440d0b00802c0d0511003d40841580780c0c101000800d00c00c81d408081d61006c040d00c010760340548000c10090021000b81c00c181140130301c9000115040d51419240c59001d00d400c3c00107018036800384030007000140c115140e1407024512a42c005000c051941110240203549902c1030080100007402c00302401d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 469600710 1250 469599460 469599469
    0x1206041703010b1e04050604060c05060c0f0a081317040e0a09080a050a03150902030f15030d0e01020c041a100306050d080a032a11070e1609080601120c05 68
    0xc0c1621454490145072440c1120f040049610070003003013111000c10000010559203c41c010b00081295817140c4542d0410750030000e0030113071300070001500c0340000c1143c94105000c0d503084944480c51424205115102c00300301500e040c0044c03500074400a000310450024819003030203402200d00307041c2c040f60650344091000080c1c61014000401c0500140030b0018000d015002030450407035203142c000b030030140c0900d0720305800ad040d51146188941c00010311688586005141d54052091507554016010705070100f07607030f0303840c0105840400c516034038046d100d0703071080c80114a0717013100a20600c41c0094640c0111800c510748046184141d0703690300132507600350007806402c040780e000414981014540e41c44c0d0551030f074030070118a0109a51050310f441540b01c081c003400b9150030785e072030040500d5440d120068107041003518100c56907480384e141000805400000c00740e1250350340032010b00708055000180c0d2005080d4004964900030400042001d4050b103d1a038459402502d0034000b0075620030500c17 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 469601960 1250 469600710 469600717
    0xb1c061d3912100501030b220f141c030603170a0c02040f330806040c030809040b030d0801090c030b06180402070b04050f070b070305160203100618150e0112060b12060417 75
    0x7009c841450328200f0105540d04010032400c8011829079084621001420040000000340322001c25a2200b041c0240007110fa00d503030781e8265665405251181c0001c0280c5080d445540003449a900c40c0d24512174596103402800c041540289100c81c0c05d848060a0640c44c40401111030f5002c04c20000002c001a0000d04a8000c03500302ca44e0211035800d40c1c4814650750b11401c825a00240c5030081d03055103850800231300700541c0032030317560000701d5041000e0901603400102440d02018102003050109135901030403111581c0c02c80d4942d2003100b03503850206d4060701a5002c043e140840580810080c00b50101c0c104848d200381c0000e07510355503281c00701500c590180303480c0540055400d20034003421062840500814a00090480300c403078651a500034203446450300900d4542154100101c1c60404902500d4a801b160011500c200c0b814040c030300c0c0c11b2650520640003114020542d40092064617401070041d044040c0c1650921500e420f0059030314a01030340e0407036140d0070303040c4614080c8002e081603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 469603210 1250 469601960 469601963
    0x1908030a09150806130e0a0f14062a18150403060f02160b061305090102041e061407080f07030503040302100b1c061d3912100501030b22 60
    0xf9010382800703a0030305c00014918020340d44800c0c81902c1130746010421014410700c1c01441055aa00075410b031401182c01c00c000a84040d040c0c0c0400101480452603c0c2c6081c1c00d0700801c0c40100f41c8800070070011180720a1650000c90304020400b0340c4141480c401070080050342d020b40c105015022894030214203d11a0403080d011403a1800c0249001444014165400150017044802d1089101060303008a400c1901c3d040001e030340c0090100101002c0b050120b40862002c0781d860b49a5180c6a00500403030501011102844000142482001283c0040d1200c019102e40199201d50303180c60090030369402034034250701510840c400398002c0341c03850040ca403240b800980000303000640c4001351004242042000c41c0c00356101c450b403003078603110388401105c3c03000c00b40d0052135601400340c0c103136090424550031402e920300d688807260388e6440c000141c05c035481402c2e941882d4020103044114148080141090151803c060000040c090b010071164040d03c0b100d11f040118007d085990406c0f0740d01c1070300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 469604316 1106 469603210 469603219
    0x3020310050f0a060302220b12010902031311030c1903030807170c0d020714010903090503030a0801050f030c030d0221030c07021908030a09150806 65
    0x6400611054071035042c0d0050b44030100700300981500510303013071540000d007145a400e85203000300948100e09505e00c11a60f1601c01c400000d40c0030480d2035402c032000200201d08070354039208490051005241031040b4460b95651700411240c59406654103000c0d40b8020341142c0c0f2807002c0c2d6504030a102c0c01406900d0708614001c1c0c070313800d27011340180100a0707100300c003144008201c45000d402c00c1c071403030f90181c0391850f002405010384903c200003060305501c0d01d09074540b2030054100d00b640c03510980310382661603124002d240ea6030050b04480000602c0706c0c0c004019505140b2241c032140301d03015058500e40301e50a4007291804036800380d503c0c01070340200c1001c82c03151b0841403100c80403403040031528a1400c16220020440c00394040c040d11520041d444800010100c0100c07800611540e01544c0d02d0f607140c0c46005c0c02540070740c031038101a03500840303480c0c200c3c5214015071481110000c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 469424460 469604316 := by
  have h0 := BRFrame.cov_init 469424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 469424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 469424460 ≤ n) (h2 : n < 469604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
