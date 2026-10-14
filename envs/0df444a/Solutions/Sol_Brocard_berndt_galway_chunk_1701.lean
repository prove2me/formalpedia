-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1701
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:21:35.58575+00:00
-- url     : https://prove2.me/submissions/40785d9b-626c-4e34-84bc-59ff60487441

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 305755395 ≤ n < 305935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 305756645 1250 305755395 305755403
    0x14090f090a020c0115060522090516110c01020601060c050f0303010b040524040311010c060903030606200a0f02120312100b1e030a020c010504061b0903030e06070314070f 75
    0x4510f01040c40c0780c40081c0d10610030200442d0080c01400403008e400c841440740072000210194820b62100003c02c12198140e81551711800544005801540c1010400704d003003500400800c0250f0907900003d542d56014062041000040149001001000c04c45480c007914102c1c140ca8896840f1494049aa0030a12910b80315100c0c47c0d5105c0501000301ca8056450802c40c0c18641c0b4040c00d6440e10120320f0b60808180d4100045034211034082605031084060491090341c0203d8558030307186005000c1010441e003c01b44c509015810710343c040c000103010342620ba0086280c41040c107030307000040b038014005290001c6404001150010f60300c070f644140c0e100f0251801c4d00c0e00c101c1c0c0c668001041381d0164920300403005000140060301481c00c80061540a628404054030b0004461685400d50700c042d02c0464145407101004030960751121000f00b40b035405482c01c03050b05440c40d10000e00b2202d0070342c0114000c04d0001010414103200d115401c0e92442411a000d50742e2a203498a10520950307080241e07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 305757895 1250 305756645 305756651
    0x50607050a06240e070e03030d09050c060f040905060103020c07090902010f0801260c04020c062d0c07050102040f060c02010207090218040e100c1e02070614090f090a020c01 76
    0x10814001154910010b405000f029940a4242400b0202c01c9070f000d01810240300c0184100d4003142e40404c0185040300d06450081814a05450240c1c5084071000186101c1d22090096564012001d07085c1c1d812a036500102240f1511a040140c00034451110044243d0090720030114028896070000a01d05100b070343c580f074030580008821a03a0300b01c207004020300345000140c0c88003400500c0025850020940003a03400b000c01000005080707034450441e480301500031000700162254022480b444803421340341002000302c0504c1c840228104024201d403a90300c0003180c0d01d000c2c801d007581030f1005032442c0d510721015592510703030240c00103d014408034010310408030040780b62031041c0242c4a007070140303100d000c01c0c1001d05403c00010303000301501c1400c0d5200e0040140003043c12405190504a590346590003d5500c005000c403101c066032203210250b500c42c18040000070760000b6100815a0900c031750740e403140c40140001e048681ea101c096075014010609004d40d50040303500070004414030350020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 305759145 1250 305757895 305757911
    0x90f0c03030906030c121e051f09020f090618060708090f192601021605100603050309010804060b041d0c03070b03070f11010f02070b07021f0e07050607050a06 70
    0x490070f44251720074901c00901c00d076131710301034131280c94010b003406c0c640104100030440110b003003050850f00e0807100c454000c3c41a28411440d2054811084090705660782d0a510700000ca1441d4042d612030044410301403c0c00250f00e1041c255460000d08440d40010700550342c6240b141040d4046030058041b1a11842440043c41e04d41e1501200142c460981080192200391030500201c032140c1101424403903079000c003a074020404000f840100809070410301700640c0c021943c02c1940c0340040c1d012a101030f0a18200c800d10100380000150341c0381003401d00e000c0c0c000d079646181c680003810a1101442d0003130309000c00e00f042c41030b0440500c205071580c031045455452140003010b640385524421074503e00f104002003890b20f07201704601c1c2d0040381142031241c003103482c1594041c02c5410b41004000a1039000c540302e4200601d29034599003004030f5100a004103c40504005055114080d001e00059922081c0750340c043d109100e200002d2078010f1546844030040c0c10305c0d03602d540c0b01c120121070701450f202072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 305760395 1250 305759145 305759147
    0xc1a0304020a05060f0906030a0c080112111318030206061905210a17041511100b01021609051009090b040312150b1801050307050706050604090f0c03030906 69
    0xa5038895034000702805611842c08051186981c0150442841080304001607141034642c88001e41c003c00c104030780025100700c0d031132005260520603000064404039030000304000c298500c80c0e6017808041180c070500d0707002c0540f03440ca0040800c3e0029441d01881a1f0120050540202d075191041005882080700d40981e03490b02c0c0039280da0f9000e0b89130b1244044030746801940000780318440b05580102265418101c41e11070390326010814074240015040002c05024071380660000d400c1006040c14504040c2404200c4503407100000b00609a4090355243d80c81c1c2c160703200300441c1180d000b541c0e440d910440c2d11b4865101c0078100c1101c03984500c0707000860004222a10b841a60410390f00200e98203010b07162594103c0d449101090150101034903a003080c00c0b1aa854610350004040c0000c1507642d80028482840010496500c00b81c1406018420402016040401c0b2082191b02403000101c07542c0c0d0100060040404031800780404214400000c2000803401070002503900a4494010007035035098 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 305761645 1250 305760395 305760397
    0x7030c210c0f050a050a0503060f1903050d0219031809020a0c2d170f040b070b060940050d171e0403050706090605060f01050415110a0f0c1a 62
    0x2081c01c0000c0041112412440c0f0030f01c06549c001c60010305003100103100c4000100d400c80440e90081a00140c11820410800100072040803610503001420714079250070f001c08608551240064248a14000c00401c0d0451041c1c1c3d01020340640c84086445201c00f1000130680c205801d0101d4425007000e0003a4038005140d0500480070101c7e110324602e0480c1d40d40d03180b070503100c40700803060100d0f801d005114032140d609020b03101420000c2c0700e00761030303003d00d080c441d01c1c241c00900380c24003994905d01408098250310078080b0000d103510346040c2010039400310009000c5c82d00c0b403840d01c4606843d0020001c01101080d41c500c104480c1d55011180350550607000035051040d02d80550300c0d10042d0b001450403507500c40190f40580a170501c1030606c01c1c19100c44d4103883c540e001c2151241d40d00c01c100612031a094800d1000300d8000e190607400d090034110002e40b030081031b03e000400d01c03100e04504221044100b100d041510ba00c4501712900848a19119201507900c0c090b840d10843c2205440f03ea010300c1d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 305762895 1250 305761645 305761657
    0x150103030e0a170c19080303090105041104050412200616030c09062309040f0b0a09020a02030f091f02100b010c02010e01081009150e06030307020907030c210c0f05 72
    0x41c3c060a2001044001c10070149140f42058801e0703440d44c480002d10b86000d1001d9407248195030000b040c00d1810b898000c0142d54010140c41c400c500e010140b10101c0c03414102012001e11605001007095401d52604090020104034000584240b001300560b404c040406680c17800d4194030b051280204082c0103984851407406000b0001c1c0400498810301c0d08088205403445925400701440c0155560106059514180318000705a440b01420100c50034400d620380d00810b1800800c50410000000003501c1c1d1084d110040c920501c0800c19200b0703035460609a4008045040108130700d40c05032b00300a51034800c20343c0e101c0b400525002d800f29055000d0110012103d40c141e458150540340d07403005503400103019061500540c0c1706100030900d10403030700c520222100c1c00c440d805409858140303a00e0800c08014a40b5019030000d101c0d9800603121400c410341c00584034100811181c0000d80116030074544004505150103800306c40c0b046201c4136501c08044984265607a00e89030704011001c1d02d0030300c540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 305764145 1250 305762895 305762939
    0x612050a020a0c0803131208180118110303040f080d0e010306050f10020f010501080a02190e180c0310060e0f010f0612090203070b040e0a0509071205150103030e0a 72
    0x6083c07000d00080700700c03000f183e001034a80001e00c81c411454580c071b8088400710b04c0b000d000c074002600303200c003010001a5118000034140020311003160103401504421503507074401064000e000400000554003401501d01900404c005c00c4051390351020314503505c0710555604808540d00d0484813820754031034010703032058400207000c9504040910f0f05210b01509034a0300c010840c024141200790a01d130030701600d8000c181c018028444010b1600407c58002039202910030500040e080410804e902c4680039030b88805203045140303003091001246404c2040e03001c0380c194140940454181d60042d2640040b083d00c03401058030380550b9407507281203400d00c0280201c114005906504001251050385512240042010081001d40044c2d0200345010980d13000151180740104050104501ca44152644006011000d01003406c1040b140d03502e07010b01d802403008400459052800b0320400704481810340850030307500d00046da568200100912000e10300540300b10f406c100c0000740b04840300440682d4400b9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 305765395 1250 305764145 305764157
    0xa090b060301030f02040b0907020c010315051311041203080103060b01030506030c13091703091501140603040c051e04113402060a0f0201230402040c05040b040612050a020a 76
    0x7151203484c1581306482080780d000c0d48504e00c0340c9042c1c803010f800c00d001c1c090a80040c001600084c00260a845144244140310b40d55010200030b9551224650490460380c50400500041d41c0f00101c0340781e1085401a4000203008580007080560043c42a4100e900480c01040441030460046040e16002c1c1c84460341a80510101e83e010301d0141080ca03050b94003003500103034030851943c0d10300d0700c4240c204110039009008002c1101140c011700c00800e8010825405201640c10100b004200c4c680941742c1d58000d0308084001810414048004c41c0500305c000c1c020000c18240ba50014110350481d4289030241e418000900c1e01402c54500b40c90701840300030040c0d2900d0507142c610018980c0c0500107240100d030700004407005a01e440005007541c0c4219505c040880301501801703420750308003501c0c8000c0181c08400c080d103081c10030100d42d904a40d0440300411080d94008007107a4900030703904110103400c80020300049540d040702401170007048400c8148140c1e90b031200f026040b07000f072103250703000300308 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 305766645 1250 305765395 305765399
    0x909110921070909020306010509060105031f180c02010c0302250c150504141c0615030503190806040b030a020d05030f0d050103031b030e040b010c0f0609020a090b060301 75
    0xd0000d1084100c1014561070401207558110807914000155110441c00ca03a514100e10a508040c001d581c050182a01c1e03001c51410b101c00004c00a2000521001840700344e8114140d00b126488202c000031b05103100030000a03030100e00d0300001030001102000c003540c40d1000300003500703009000b42e0b40e8008415003601e0102201101225280039005402c58018002e80008503030503210125011b82411540e642c1030701d880c203042180da90184802e200521995201402c0c06900d00c49611030340d021356210348040b6020b01182130228210b40aa0070090480c0008500010051000c00301c140c1301610310340c0c4401c0241c8528040c4000ca895030248036400d034000c00c540341c0140c04d160b600410b043e44501c0890b840c2c1210203820303c1d0300790486025200002d40b520010030a2507070101d030782a110919101490203582007603401401c445545c0185d40d0065844200c201d031280e000c1c049100c4001d41029428024940f03d1400384003d254540d0308034454603490340041034001041c4a14411040c0c040c0c071080c5164 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 305767895 1250 305766645 305766649
    0x30c062c0616050319061206060e01080102070510020721020303071b0c060e0a1e05090c0910081b030103060608061e010302041107050d080f1e040b09030c0d050a09091109 75
    0x800010702c54041c06c5c0c9800000680180718a12592101d0040d000040e000342000385202d002841030703000014030b0780107000c00400b00e500031070b40d2a248191070600681e250202d142150022801e000c180381401c124080d207502407074012004520070341081c0d0b01d00050400c14075081280414000c0d0140965005a4040c00301e02d010b419840c092220040842d04825a505011420b504400004804447c55072004002508001807138a8001c0d860003410b030b041c0300151740460b0041c00002d211104200c0e001c0041741403001300443e0602e420a0202c081a80d1b5a124107205010303040511843d04144213040000d0400e103440e0b060303100c96401c040f03068041e0382d2070b580811021300768003c02d040540300300700b0484000900030030414081750000e44a0074042d10300108401d10405009005c3c00000c00307e607a90712048038490107402d5009910070301c92492503d5020b0f920713286000e401c0240c8003500c503a426854130260010054032040d48650750310741c01152100540b20654620110355041503805212a003030f07034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 305769145 1250 305767895 305767921
    0xf0c0d0b0a09050106120309150e0603040209070504080d03060503060708130b0c21040c050609030a030c080904020310170a0c060302090102010b03010510060e0907080103030c062c06160503 83
    0x803501070f1001046490302c603a0401d41c41c215440f030840c04111400c0080021028600151603044028280403000d040c48030045070740340c800100024070640382c40c0c00040e60030f401102500c0290181e2411104984c040e58009002400b0900030b141c0700340b0841c400141c00d0f5100b0388400c5e2141c00c003489400056001c9503034034858500083c103400c0307c400e010311442d45052a440d484d40c2c035a283c01140e281f15820581081a200c40301038001a015501c10000030685440006090750410b5062170100400c05407802c5c8a492805500d60141d0312a0001042c4107403a500120440280d46c2c0790f154091083d4002c00200d03507124400344000b0008401c1d003008126450017540030b028003030410f000200e5603528000000e800c40b40100e4004500d5000c0d5007051081c503038403000900e5070420039510b0a10504220b440a40840814840101013040000e14601005440d42040095100550301440f001401f4191440f00d14408480b0700087c1c0302e0b180000c1c20090b04074a210b9039100146d1103a80c80c40d101c1d40401260 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 305770395 1250 305769145 305769161
    0xb0901120b1b07030f030f05090309060711040e01090c0b090f0918060f090d020c090c03071b0503030a0e06060907050f1b010209010e0102070602030a031d010e0f0c0d0b0a 75
    0xd401c0048400c001440b4469005100d030078400c1d500d54610020402001d01140da100610044c040d140000304091588000115003103060111006034803916a4030740780c3c135001000c1160301e4001e82024a03104851130150061250780b1702c191845281c546d140ea140320300030f006017403866070b200c0342080c903008981c10320700301d00c40d0844c140d400d0f240801ca0343d14562038074140050341c408965400d00c07820031080c138205004c0b801007400b59101800c8200c0c9150001445064060200c004540c0000049214980502048244103921010381c030100412402c2070780d1a60004c40703204400d141040302801c180703c2e010038000c1c4100c0008041070141d8440800c11a55600070072003110310201c040003c0307449041003021800190003d0000569110f00550004080c02d0400360b0007415075209000c05e0240e15004400d58901204a20307000502200d0034804a16a00c2241004455546082c036005180100400d00720700240302c2030220303083d8030400018014007455003203000d016011008003003503003140b06030441e4803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 305771645 1250 305770395 305770411
    0x105010f0801180209030604050a030305060f13050612100c170f070c020f0a08011a030a0c1701020906070305030711030a0207090f0e06010b0408070f0b04090b0102010e120403060b0901120b 83
    0x420701d80c00b17002080c0392003000e403816105544410000001c00d07915024242d8421f40030b491800443e18810080740b440210501008045501d55002848a850300241783c040004040c007221000d4541702d0340320b0010000c80c454140010790300c002510764020640002801441c41c9038040450360381310441104d0082e5200822070b84003030003400305030003640c400e048240034040000001035807148101d0105040c200190000f40030f81c10040480c00030070358051102d81140c4400c40501817040310a45100d00a202d40b15400380c2c0304401007001024168000083c51140039142c507200742d0b03102038150b16642ca028003000040140e00440080c8080f100541001000d03c0b02c0b5100820303c030b440a03c8040c00c20009030040140100041020800170b0400c1015100814000d520303031138018100404841544501d028100a0580310907000c0382a034400d602540d0f2000151080d200b69000340044214240e01c244000d890190404090f00f18a141c0300112604940b05125112540c0d8220380d60000801c800400c818 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 305772895 1250 305771645 305771647
    0x5060d0f0b040236010c140a050604080d0b010e130903050f0301090207170c06130813081c0806030a1e0804240c021005030a020409060b0c060105010f08011802 70
    0x2016a48075800070b8035484642592036001040244d03504400c4107101000070f6021148400c0d010f07820b90b044501e540701c868114a9400707602c0300b68442140b50541c4908010141e01c610703001c00081c8400c12010b085031800141040c02a849130b000116060813401d0801079214444003070385c8040d0605a407047c030b0228802c2c100242440c0b0b03a04445900358009a1080c01101d13000118541084014410940c407600e01c1d0a00c1814003800b007a586507280030003001c000c0404800c01c0c078807061221034029a0902d0b1900d191040c0003075194810143c6510848000d030445041c0e9180c1e000c040ba000f540301b2841031070094018202100c440d100c1c00050341d04000341c1003625081b14045c1c0c01207032600b001000a00a0044a12040030b140000741d05c034451b14003204030170402444955801640d03090302c00c0c001c5070182d1030103a03180d4484003039540091107194030104100d45466400a14a1900c07409070150200c44d0090301c00f1a031340c8a00545000c080b40c0003020010b040d810050052002d81058580503030303803100c801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 305774145 1250 305772895 305772911
    0x10816060f03180503040905011215050612160806131a06041409011a060901020615132c030a09300803040215390303100e06010905060d0f 61
    0x881200400f1010580701600300050030b11200e1000e000c1c0c540140200068407500100b2615450101d410b0707603030307800300081c1c850010030030300d599420022040b040c0b41426101e004002e0380900e014840c2c40e2003840401e01030600010000d0500c030304180c50b41c0c2d412000c1403618401e0740c0348440c80240c0c01449607900a6503103840d8000320700a801e806211380000400041c24030250712b0032014100030410306600c00c403000c100d10802641d010858540185c2103c82101314100041c0c000388100e00f158058840d014907121405031781d0000f10303a07801005040007038006600038040d500300c0e40724841d00d040b0601042d40ca0b2800c2014504181c0505017400300c0c0e00c0d85101051510091640d031091a01003a5080d5502005010030362030030340c820300110481510100d2a01a82190f0221590000104500c1424406620001682101c10b512241c080d222081e40da40c1d240946200a128840d40901405100110006a5107500510200003a14001428a4145007500d00c00704040c0c80f0700343c07010341101d44440003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 305775395 1250 305774145 305774171
    0x602011e09020a1a03180a030903150b04020a030204210f020108090f0111030103060b0a03030e04090c03021002010c0f02010e031611090a06090b030703152c03070b010816060f03 78
    0x104d40c080c100580469a074908094400d00b0409140c0c0081007026007101c0e152000003500300d10f50300112507010005c55100c0044034952001440741d4004c058010340000b408011465050b401441514582a00c6845210071451041d0003900e507500700030201e04800c24060b01640c020300da9590b000000d90100d400124540584500b5143c1d0b10900c03180c001e102100601c00c00c0783d140074095003080d05648500b0070503d0340c0c80c01006024210211030042d0b5840300a0020b00a4040700c4038007460300a0700001c2c6424903010024001e0495041c0903000402d16001c0654442c1f060140c1c508000d10b010003142807401601594002c003143e0842218007540a50200300f05455a242e03088c0714009140d00041e01900e40310340c1d0390070b94850110091103038025440034000115103030000d00080460030000101500352010a06000c050010202103d140d0f412042417843c90001c01454510712400290065036a19101c00d5603580300c0305008405484101d00c1400864401c0541004203070182c40c001c01ca50500b485 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 305776645 1250 305775395 305775419
    0x102070e06152b06060e0108160509060c030f03040b010b04060509010e010504150801030606081f0b0409201003060b0a0f0905060705071a070c0902090609150702030105010602011e09020a 82
    0x107001240e071104410070400d0b400801d002c406d44401c3c01c0401080c580040b9070715040c10746005480911801144048041d00c1d42420381d003150040e03d0460ba9204075102000c54160801c84003107507945402d00001c2141601c00003520100c0d41603440d05800d0100e4400191480310b8032016446c10001d0500c800a003108030b0300c0c00c20300c10002d0354580000d02d5042d410100107603a4107801108847c0e104403c9040890484180c4855440d40c101d000100106c2980020f8050111210080c10301c0080050a00201c1c1083e0750406420804031107810b1380041500c41030302038544a10551070308000c00e0005082c098015000c0c0720809282d481c00035421619140018025000781c2010b0710154000141131018034001e05c080300d01c2040d070031a210309220b16503460110300010360050410154000c1001c2c24642c50b20029207400c1c00f0020001500c032011000c40b030a40e83c102d603209a110b0360903c40000390490040c410384282d0500511910f03c07503c1500c00010140441c54812078120086c14000a07000740c07c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 305777895 1250 305776645 305776717
    0x120603030804121805091f080303100f03030507020906030f0303070f27050118090c0c120c03141303062a02070609300803060102070e0615 61
    0x1458981040c1040d0078074400304204042500f05215104000a1400443c03940c42011aa0100c0b0044220766035001101071404180c200b00c60024121b990224805c240030010f0341c840c00000701c460341034503a1503800701c3d40b4261034400a00400c40c1040480d000d070800894443d8040e901400725a5041140d061301480d5510403111000044d030703c0c86084400710760008540303040308400c2445101f1940c0030098041e2400d2544212414800703840d400e611405010b0100000503d4042c10400120301c59032406040c504c016a0201c0319040c507841d030040d03800c1c050751001c214503070035540e204020302004942c2445a030100210503c0000328002c000001952400348012407901503c18600c00c01000f442c004694550600c08015900981ca091001547c002c00c841b04032540e10301b0710340d118114400c50495200a221414a90400c0c410f41901407100c604003c501800c420703400c0365002c41c0c0d034100710f40100320142c48490340b02c5c2c000c101040d10324078524050024443c680e51a002c03420f000201c1510070312885 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 305779145 1250 305777895 305777897
    0xc1a0c040b0c190809040b03010504021f020f06270f07261002070501060b0301030f08090d1505090601060c03120b0105120a09050c01031103070c05030f0a0207140a180c12060303 78
    0x30305c510941070500031496076500a40083c45541440d50015150947e148810070000024100c030329061842040b5140c10680d507401614024184819150a01c02c40714880c0d0300324040d00020000040e60004d428107100e40f49030003904560b41080b4000c020903507110404007444a107201c11000b0200140140c00e03040790b0101006995009914155003907400300d41c064440340b50180010000328880300301d0008042e41c013401c81c542d50700c4450000340c19101d0001d009007a000140c12107124000752940200e0251403120211061740e130f030300c600c111420800000b00038000313035200100034103094851f04644808001414400d0900030400544046050101c480e00000341d00d8200c1442400024842c484e00c1c40d90a103020701c4202040c00b00d80703031240300c042c040c9801c104030040c1d54400d01105105541a07a0207480040303036101640704e0000d64441e1a80a8440c6000d500e441c07401161425160300c2d401c0310b01d0021140e1080350074900c3e440c02020509051418404444035031150712425100c1e4101562203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 305780395 1250 305779145 305779147
    0x4080d050702150906160813090b0a08120706111b1c030b010806090a060e16092411030702040903121424010e0d030c1a0c040b0c1908 59
    0x140d401001600924011000d81c3c03400204589440d5840f07801c00c540181c009082425103a80217032070f00401030300c58a51149540c070340c035000114010344280c0001090450442d04d010041761102c0c1a80c0e100c044403528410320749c800300715000000c0e48a4201050035024010032508103000c40561124403403008503072042540200c1082e20001110410800c14407000346810044007101d000041c101c45030182c4458032030102000011400045274019602504000201f81014203011001d14002c0a84000f030001017040100d0100740e0109506208442d02030241042145028140e419212400c144443c801a400100800d02c05a00d99028003146d140c8240d9034078035201c0340f01051800311003003000d11011070780c40b0209112030340d90900721030b24000200c481b02c0702c0d00d2a504401611031240034074a10340c0040e40d41c41d40384141500610002c2c0d00c01c4c041c9000710041400703000c42241501c800c40d04111032640502090201040c1d5501520b9242894400c5421880c02030086d1100105840350441d0b0400b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 305781645 1250 305780395 305780407
    0x1030309060f05040e0c1c090305040f06030e060a0207021c032f0a0b0907030c0b04050a0e13110a032003070605040f050409030522030303110a08180304080d05 70
    0x5842070352080c4000c6140740c034904181c01d1034050040d4020141c96440100b00c081040c034008084130b901f0091030342c000002003020036068038014010b500580303d25900032410010000c2c056029016078074941c903031840a000d4a582d111444002508403601c140d80140140318880c289118a40d05240003900989440c2900742d020040f0109052070301480511107440c086490821020010b0f00c070880c954012810344455031950344c424078201a0364406006040c41c0319002901c4661400200700f500c0c025a44500d566843d11105400c3c018190350003d9010203030170076840441c0041c500208480030050014022658986a045c0808903c140182180e0001482c6020b58641007000f1030090180d030505904051401d070f06150085120f10035075010725160410700d42010301c100d046030b960b0340e0840400d0403141d001189545075544a40000c80100e8038100700c095a2607110170640340544c1c10707551020560b90314000034620b07d28600195900a00c0140001f19119105010021404403142e659980b195 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 305782895 1250 305781645 305781647
    0x304030b0a0c0e030c01110c06270406030f06020d0b090915070813060f0b0d0b070212030f070c11030f0f06010504020f040b0310050301181b06050301140f04050103030906 75
    0x280c0c4003201d8003d01c41da141c440345054a0118140d04101320900f00700c100351503080d07002400c005051949951000002481c4002c64030500f0b1484290742d1400c44206070449040203000c1119510b010140204d00207040146c001149a00100500500ca1001040220a8102007040c5800640d80c8e50003030b030040c001103010b1519900c21107520071442d01d458061400c100302c00004180303642e0070140c40350351504450a0303944a0340d0412108205c01a00c0f44000003d5410840721800b02558800c0040c050607000a10540e401400d0368080c110b08180c1c16456106c40c5015100c1c400c20b400b0840d212554000703182c01e0350f0780034040800b03002c2071007014010700900b56604504028050708400d100750301c140104004841c5110a540580f529002221340d2604c481c02c3c030100560490344000d90560800c00c1200102c10882c2035201d07054411a2054140101d988002e2540400da0003108002071f4207100410201d0341424410000d92400307480004101980300104081d179809801c1600070a50400d810811700e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 305784145 1250 305782895 305782901
    0x5191214010b090c0d09060603020d030206040b090a0302030f090f090a0209010306120503040618090606020313050402210601050405041b111c140415030b0102010c0203160b0a09050304030b0a 84
    0x20b42ca003190091194600501e00c950b00c2d000342048402c4043e602e03410002004415448400a160014802100c9019615000750345da0421142203a4140080e00401c1107400c00288030f0100d1783d8180c01a6042c40340c0034005030301642000c4d54641d0312900c0c2d000002034584070400424028032400c3d4000d42ea85c852440050143c03509a400b284c20030030500d00784804100040180c905441143c6000410300400c14500c2d0100e010ba078002c00181d0b89091030010301140c00000518810799a4404074080310354500800040740900310f03803440d00209907501825090b800900d050f40c001c405052582c105500e031804141141d00c104001054400c03802529501c56800416903603c2c107a16a000b460346255a0015a0038903a07096040d000b4804061500d0381308103058000d4601404550071074001e20695244000c02030301201034201e003d540380031030154003d4404000c9030a642d070928115103031102c0581d1880b8440e10000d00300c1400c2036444214a00040c006d000410085000b02041405d60134007140450403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 305785395 1250 305784145 305784161
    0x15130b031b150d090b0c0304020102010606050a0c0605070302131d0a180803060d1505150604080c121903051308032505151e010b0903070519121401 65
    0x450300764541d4440850b0707100007151074400c050000d040c3e25440c0c05425400a0928600c0042402c1400410000c144488002440c4118004d81c0203001050f41e60600351114807404807103000060108603014081103198011503008a05403400628003010441018805c540d20b40210f10700040040003280200303440140e003504024282010030416013800419162144100c100030203103c000310010b1903960301c02540f0341d04250810780035200500d5004284000384412940c480038400662034070b000c070b400d201d010790b400d80e4656401000751050540c10820a1929034642d00e00510400c803d0125140181101c02c000724820b49805444d0145c41800141882044c4c01103005030740140840c4e20340b9403901e8150b1a03c0000800424480482803c000b4180340d050f02c0202c0701a40318509111440044001d0840e90130348030801c00a06903202c05101c03043e0702c2a42d02184d4141e00410041c0080d10b4555084ca52039142011403182659172100a0708031148180b00545a07480c884108140c001801c0c00388100e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 305786645 1250 305785395 305785423
    0x110a0b090714090115180518071101050405031e04180c110a0c06080402010e030610051903050a020f01110d2118030302090609040f1a0904050a030815130b03 69
    0x3d81581000000c0c002844642500c07420000700c2001e02c2e008000742c1c900303200980030240c104440c52000b420a00b0119500b502c6002c00141b001c280003000c2001031042c94015079208000c0c52525181da0310700031a0541d06940b00403c0041008002485c080d26000c2020b0495050404180d242502c03a02030300101d0101c50120094011040c50000201c3c0785c9101d100740e42c00c6007490074241d12207000480c1c114205400040d010702c0707400103114104460005200440340121800341848006500e0100f10b0209403000600560081000400620b4500500794079100180b40801c50b540c1c1e013000041c6400e45d481c4075580812240000001544c1010744035504039040458240524540b41241e03440303200d0030b1031002e400c050b408600381c030140d940c1c0401c40740f120800030800e00100750001d80601c01014080c1d108100e013440400381024070700300000d0492049802001411162141ea2001d8880440c02015107640d100d104d03050a50b15554801212007000a4100c0055540d010900b4036181145c0f05000c28 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 305787895 1250 305786645 305786659
    0xf04020117090a171c09060b060705060610020102090d11031618050405191a0105090f01090b040f0606020a0b013005030706051306150b0901110a0b090714 68
    0xb40c0e07401c009143d841c46a44008041e4030b14004011402d29406040040100404410711006000ca03403a001612081d008010400c151003c020801c0b40910a01c88002d00b01d400c101c000803150f10300030490104081c51400094901086100090b40e1603000d2001120a00ca1101108a0780e0030208500020700300451010030903141004040341c5240c1c20450b190714106c5d2200c0005042020038402d81075410102c601c00543c02c40c131450000b80c050080001066aaa40c3d20000952450103044180c01403100c041c01e1000ea03420705c260301004e89141c80026410a460341204060240f1500c82c24004040d6580900009000742c03070000b82c510b5040c3c1c00715030001c0c007091150840b80d03002c0b0315032001038266051a8048070071515085003140a62103000e41214902002c1240301141c0d01e0009041600c41d00f400c101c05103400c1c01c0040780700100d00034444440310074032803812154012881c152300015400d080783c2003481190748180c50004200c1d031484003030b08007040800c100c20000941080c1074900711060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 305789145 1250 305787895 305787901
    0x30301060e100c110d0605070207050f06130e04170d02030f060a030201140a020708010f06031b0b0a03021c05070201232a04080102070503040e0112020a0311040e01050f04020117 78
    0x742035a140d80ba000c0c0c130250080882440075540d45500181ca140e11600c10701c96440d254102039203945403803050030302902191000c0521403820300120750000c80c944030080001d40c281440c00c9011000100b00b12007100c03000d040032a15150b00c0c406044440b60341600503980f440c003280d10003000d40d4080c6c045070080f0990882400181e80045e01d0040c0c03e036410305480d46030000203004a10b4506107030f001c45059442e21405099460141c1c114409807400f402c1d0704806008030340e4403030518400c80d100f8544c28440a001082a0314401c4d0010081c4945c2c901e620001400d0642c0f16404803041030302e804015071740d10501c92001400c040c1200303420703c2c030b041d01000c01c0c0e05d0202200e000c4018541c00c152899100340da050a950b030360760404d490150184e071000319110b030403520f0300d91f0b5250301c24018668014020000001d02c2d141304e15201d650340307502521440396140f65070384401c08900e001498070751164580c0840742e102c10b800d1180c0d6104100d10307419190309080c40e00000d000020a00307140803c182c210020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 305790395 1250 305789145 305789147
    0x901030609051504020306150c0a030f05042102210c0901120c09020f1615050a050115110705030102161101050c06071b0b07020d1d0a032012030301060e10 68
    0x303c0259860155000350b078940e111000189898418074180c8403001021410035000c900021f130f8007a5040c425180e51050040064041c1c0b4140114030440d100c21049803078511030103494090302c600051010381803c203019011801c801c03408080c110140b4942e07101040a504518126100b1030050840e6000109110065100d50343c5c41007541c019000c8050300084c91000f10841c090031074840e10104611500e07465080d190181080f0092072135100098244004104403003002c6c42598100c070b000300c000c1030788400c43d030400340c4101d00c41342c0c4809058010000002040e0301c1c203000411035115420081c0600e44070915045010110354460141003020510040740e000c0300004500b80c015425041c0050080900c82d01d107082500c400500402101d001e0060200c1c00d5000505100e070100d00742c44042c0b584502c21503001303200c00071500b00c542c0300415600420104e0180003c00d041e1503191007400c0c1c440c4da00b60300841c0740c1c107080c0803400d00680e00c000010040e155105001d42e00c001000c5542e0b511958030814 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 305791645 1250 305790395 305790421
    0x1020c0108040f0b0403050703030c03060f121a01080a031418120f031b01051b03060d0809190e07020d2f06161409130c11030c0102090103060905 64
    0x2a5038180310101c4041420b1014424001070803544c001d001074020b1800b468001c1c166001040c01300d01003410308002c0100c0f81d000303028242c165204220f45d00280352404103c0d00d000044458180ca10000c1a49804155022800c2490103094210003c0030701340b00703a01c0c000305501c0710310925442a000511009641e401030205156448000701c0c1c1c88501c2190904080d41019a020f080301d115100000d87c0d6115880c0c45045000c90101e828020001391349c074a81141c0300c0c4462500200c041364800c0001400d149403084007050640d0203044484e0401981c100454281440080210718041c6020420812100d41180c859032142c5944050300c0d04c00112407000d01000204500314031003688550450084100d000702c0c00035a84001030441d60b0500b40f07450b81811050450017884001900c580e000e0154505201c1140c10154000c0d0904100f00f50001d0010018103c6840d00d40c10089140f804c28a4444200003034980d8030758420006170360b411900000740c2166180e512002d8130030b0802c0100640103003100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 305792895 1250 305791645 305791663
    0x1a031207081602031614040b0405090601060503091005040b01090e0f030313020d02061206130902060d0b01030e0601060504080d030b1021090b090106060503090604032609010c1404050102 82
    0x8640b00d50560548000f03400d00304d014441d8800340d038480400095501d02c00c3d1140c1c020003c190340402a400d005005e010030f803001180c0b003031082c1d84008010000c062143c402598070424010135100e00800c0c0c4075050007518001e032010369000e40c030400107000c2d80d8814030541030303032102101c01403402c4600c5528940c3c40b400f00070b165400100c072881a00e0295140c59411890b102d60040040e580c8604d038200b11000a6070962350309026031482d0307880200300c48561240d07030712013a0002d0038036091401100105000d000810209810961124142011032500b04180350280110381c488603103503410100384034948500b11000030201350a00c00b8620054440030072681507040645412002020001c0c06400020048030358510018a0b0283c1d0030280003050041d5405446a04000d001171035031404129818081522021006c0d008240410f0000340910140440440000300000100340c101162511041d000c80e07030300066944a50010300d00642c040e450004801046404a0400e420000002c0d0742e041d944d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 305794145 1250 305792895 305792917
    0xa050303220b040909050f0a0c060807120f0207050f0304080a14070e07110105100e0106080a06050a06090e090303150d060b04180317010f0b1c1805060c041203050d0e011a03120708 79
    0x8c4bc1c0030ac1c407414800c040303100310f25182803401c1c0004c21802101000940c0886819201c0303004141e29010400710110407541283c410070b00400c418050358071603810081450746a40c240c0c1c03103186070004205105101c207500c1010300e03071254485089040d07a01401d5580c028012124100390490a0024901c1c02041d40d05413a900d00d41041d0940d035603000038000b4500ca400c000c1c1d0100c031503100025030b1a4003c03980700684420310720b07080440d15485040399581c001994000341c4094414410100c60030300d50364185400e405242e0206050f0b00c080042404c542c2c0d8a2501082c0302280d145c940c051503005400660218005050f8030495803520880c4201c03400caa0268101000c0009107061009000a090000d0100000700c03c20102102000c15001c600201e074088a55009550010746072003026020388003214480d44541c042003950399000c42d10355018884000c21255203490b0a0100942403040d0b5003808244206458952540e000b014a03080f00c4a00550512108100360000500c812098179881662 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 305795395 1250 305794145 305794157
    0x1a0708010311010e09010e01080706020c090c0c1203070c06050f04031d01030b060c0304171c140f03090706020106050418120e031006090b0a050303220b040909050f0a0c06 75
    0xe0382c00101c1d402c6081c040810340c40003031000041005c0c1c0750818018101d41045084030b40b803a6603848141c0e22b8592190000380d012003280002503490074003100400070001c1410030381e403c01c0d83c0b840c42d6000710b070420b403084000146001c41000412055104a03a01701b801603c40203080d107400da80c02800a100350410248402022211030040c2e400394201c2c1c0c1e025030000384400e4461164106c1c950352030304544203040300500c0e000210304190101241149080540714130b0310440d444144816104204151800b2011102c104507001c1a810600047c40c01100444007500c1620301c0c10070000c0c08d5801ca9040240f14510300300c1c0b14040c1402c6030f0000d10f0f0481e484408503090001c0007100b40c1e00702c10000017103030b01400b80386485c0c50003030b135168810b00c15589111010000e2124480074000300700030ba030041d0358044e030040203d4140003195290b010300e000e2200c0c802e0b0700c180361103130b252011640056028403090364580b02d40710208070090003180030724441d0000400d01da82e41d6440301c04010a05100784424028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 305796645 1250 305795395 305795423
    0xd0f02040f110d051f0b0304170a02010c12050106120e07050d12020f120a030527010f061403120d022205130c020309060c0a0c03050a1a07080103 64
    0x403960401d50180ea01500c00700700c1480c0b01101c0d19000e038001c00091200302d103400001400e500c41181c80d00d18480103581c158a001e403c09800d0180c6a0025005072003e036003500170200145416801001070300c41503400403845045a85d0084c10514800d44102d801780e007000014061954820803045801c0155800820810440315100d8249069900083d800c101c015080c02c051207a140300e00000c1070f40f154201c500d0101d8092005031901c100804041018108103d01e01c0960700c20740015801103040c024030340c10720078540950450542802c285400704d0b5140c22a0384400100c0d44100780c0102001b42000c20b0507006140000d8513890007904007040050041841c219000450703040e1000700012025201700709036100507440a07100144200c1e84a01c410035406202e10815000340c03600f1101c0d03a00103500b0311200350100106600312085e07281d0317140b156010050110b0399811008001b580a500507000143c103a0805c0d103412859001a0741c8418040700900c404a64070018070340c1107076000554203101d48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 305797895 1250 305796645 305796649
    0xf0c010f0908030a030504120507020f0f1c0506010906050901080a020d03050d11070210020312070323041101020c0d030503190f020a0806030f0c011b0c151116050d0f02 74
    0x40079500260384074400490740081441d09a40804d010354095400200300c20720000c0c044403a07100c0d0100c000c0d00030070361100030f0260f4203110390424020b00f002441e1403110540c5014550a8040c40101543c40703600ca000100040d45c45407042c2c4015000c1691f9080f817641c103005003280d0381c80c03034660003d004100002e101e406151040c001d507451b010040005004421240e440c50718260400c8005038850500101350b4042a80000f081f00d04a0142c110a280107654516064005050f0500c0c0a0b003480204803540186ca11100d189510503803180315032800000545000a203800360840c081409124001460b4000c20307040310640e40d1001034210011400001c030405040513080c08000320318814004281191041d07042082a48642429421215002c00d0030100c180d40c0d8880f2400b940c08204c501c02101d4078000ba88440ea04074901a0241c8142070780e03910054032404500213a85000a6144020380c2d0200005101819400c10303000c000f00041c41c2444001b6524004159004040d41c1510949000319 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 305799145 1250 305797895 305797907
    0x3070b09030405120705100305040b151f02030d0c090b070b0a06050a08150a18170903070806090c0405010e0f09011b09090f05090604080705030421060c020f0c010f 72
    0x2600b070261213401a40e44a12495646130344074040c15102d43e03008030160030014802d200c0c1c0d600c243e80000003090951501140040030505c15556140c011800034995541170441c1c03055908400c1050703000b95a01d24a00c0440f80896103103681200c200310000c8000c0001e1540d00060303603091038228000400316110174150000808043c1e100e182c01c1000c03143c0000f030384040490f50810144602c1c0800c2941d0380d46040700c40860700d64210003e200400c980c041400f00c1c001a4440206c45a04130f0964582543d0600003494608103034025800c0d54019801c0003048034090194420302442a03d05000c2e9505000368840d070780800401c2010f100300d0207030000d46400d20940280000700d520210740703105800038090040c0a506640101c4e00881c0c24405080d4100035079110341445a28054050405502c4a5481010580c85041c0c251400d110510020404020190004c000040c850000b079801c100719280c82001c1d19081d45001d8155001452a42c00c6d04c200428400075910017440d00c1a901c01c6108015100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 305800395 1250 305799145 305799149
    0x302030d200a03093312020f0f03060a090209010503060411160c080d021b150d060b03070806030312010e1003060e01050406151802090612070c02090109090503070b090304 75
    0x3403294140031424180c00c4001c41d41640c0800701c1d070b400d104c05140d01641c1d06022001c0c201715241426544032041e240702d2840c0100c89013401344058a40510130401107920f80102072034144110f0700105000b424904440e4003001071803000d00c15030622905c88006032072400002c18040c0a1600d8502049e10300d8180720889d08403c100741d4101101c0c803224105400464040d0051901c1d81c4101714405860a000181020002c841d1034906064810241c0500c04008060341c0d501042030000d00014000582d80d010301005050301c0145181c403440c10340c0005266070300140840d4000c1d00f04200024000f2100920903041d15409000c585442c0c41d8141300b4105007a056101130285854007098458055041d005240110f0250105002104c50403007665158010352280c20402c0034401c5040c4040c000580182c558074600505603800d200c01401c031b2100c000d02c2103d00900041c02645584210301c0c12840683c05041d404070b0400002c013403030b510140d891181da20040c00c90301d200000128006800c01c21200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 305801645 1250 305800395 305800457
    0x301380105120f0a050601020c03030403060c09051c052b081504020703180e0f01060e010915050d050c0310090b030f0a0302100c030c080601030c0c0203070f05090f010302030d 77
    0x401c2d07152031698410000d4041c3c07500e00300d042c20704021480035032001654854402e4010003840c903007881c0d07985001c01070000300000818880c070030307000260540c1c44d88909850309000d43d40c50303200703030601b807410a091400510b242c03803d83c5e502103a40e41d40b440c1c418a4040ba4440b140c20a0003c0b07490740e0b84910340809500c9245035002e400003441303d0030164030841c0c03d50900264103455000139161200d00e51310140440d405c3c0720418440c00100a000c0c40307a0b0b00c801442c4030606045070400d0721070b407580c211003030620b480c100031401c00185120540c0d0140301d41a4001003030110340d41141802c0140c5035803071a151080800103922000101c0b0256404d00010748601c07950001c80d207204010380303000f030744602445c51185819072912803200c450500074001c00c082103d1a545209565030b4010041d4000c289000c050800c01a40040c068016241004140d01400c07506011100ca50700d00710801500d200010105802841011300400060b10002028805c101c00350503c0c2a03054041140444003804a00e1080303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 305802895 1250 305801645 305801677
    0x1109010e1302031501090509040305220e070504080d0306080d051b0f0d020d020106061b03030906110318071202090606071218090b010f0305100801020c0c0301380105 73
    0x402040010504c115488000303807207814202e41d50300104004980115405004031303401300b24a68107800e1071050401107000805904510584420030802c014004590b170360301090000405000c40e0300c08003e241d80c3c03000c0918041c44800c0c140351085841d61242e54080082c410089400000c0315680107055907580c0958040322448190320400681d5034625a1515000d80a24150003007142d00c1070003013600780c0e122525038000411450450791841c000001d0190101540c445101c000034540b80140b205a101450580340c4a060140b0032440440442c0a045801c0e400820200b02d0a101466082c0160703404542c0c10182d60b8a50011034814850321000410f104c0820740d4415499400ca040002c1c032034a02010303455001c4d214803c007001c58036204940c0d07004c101035800c070f01d000354425001a50721803e25010307003820340e55688029081e600a02204079044d00090340d170700080d00f0b00b44210700d081c0055000e2500d203a030620181102c0c5002207008000891106420003803164004c200311002c902040c9200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 305804145 1250 305802895 305802901
    0x71802160b0a060608090307080901030e0109030f1107060e1002010902090a05040c090b0f1912030c1407150e01020705100c050d0f050d050901060f0f0906091109010e130203 76
    0xc1c0d40e00c8001201c4100c0c6042c907010700416064030519480e0306c5806003000440c0740c4081612400350030b0b00624003460400d5240c0032013a0354a5030030700582140510079116020309107220300c2e0241007020b040202e24496442a5801c0081a1f400400841c00c03810680300c000c040c5610b20022070141001a801030b4001c41020b060103c2c1c019690f000500c95400340c20090007040e1100315036402d850142142c00d51107500e00001048920f461144a10701080c82e554074107049a036085c00c100790501140080d800318019003404c100380302c040517203107011101d814007501026003070040765a07602e05403003070304810400f008407000000d900170000d45018041c000c00001404210101c002d081d81c8283c08125124020404000351440c00351022900620094889604005440900f0001002c0082131303401c0948d00d50500060b1008404c20000242c40c1500e054003404e41000241d200f62140e40c0e2001c207091345003580006220129000392803800c02c00b460000da000442100140511504d103c1d14041c00d0300c00014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 305805395 1250 305804145 305804153
    0x2060403080c10060e061e120102040603050c090a1215151401080c0405040906020915030906100e070c03121b030b03150c0a140a030522020307180216 66
    0xd0030101110700c0803108840f1020003500d0a566092140c6600344010b207004c106945440070a41c0030352006001801e14002d030042c00030303540350012020304502d654001340c1441042d80c9409826813000010049900d085a03140110312504110700c070f03143d281b0740d0142203c1d08104c080c0e00c1e8104036180603601400f840101c4500012840c04510500e1014215146108059405183d52501c5a052a5081401c0c1071400c03050001500015030126015542001011810341e80c10203003c0c400d8580000c0161607281c580311203454510f01070031881001102d110301b0010050b810311455400315241c038200d066110309107801e48140e08218000000a030601b007020481d00741055480b090120269820700c6026050344c18540c85080190440403200c85900003c0c600e0b4244600520030340a0514100900720764030904815140c000c40c450305c8c00a0380382c0090005810204d82060000c060301d5840f605800e05582c000b9544806038410103550342c11801404980021940c10f440e44450806104544003209243c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 305806645 1250 305805395 305805397
    0x1b130e010609051e01030f0e0304080304052d010c1a090a05070914010b0a05090307030303050105241b0c130914060c0412060617010e0120090114070206040308 70
    0x9074400030310030020014042c944034214100c500ca8880b4020840c0050500441c003820150007285501500e07026506124001000204010081c410242d500c0e5420442042004003105d88c0704210300088071064804192103d001c0f00c414503090078040072540440c506060303003610355004001d80015143c10040f032080e02261401c500d510820664400c551100165012a44030f0800a800b0a80020051080c5c400c1300f0014140d0a10b54100380b4144040400007910700105908214000790700c0381d00412039402c0c03048103a8589a07800e841c0703c44070849180b407400315010b141d5a500c403010480030221804802071101105d418005002540c0e07074188a070000e8003424804c0c80c104c0d005100d00580d0503100c1c001040c1540628404030b451031030580b90400741c441480c4003080c15110682e50305030018440ca002040b0f8448040300000204540140c0c012071400c5414000060b090143c9503600703072001031040001c85041c1d060909000903c00101089000135006030140290408800240030040c0000c81e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 305807895 1250 305806645 305806649
    0x902040627050c0307020c090a06080102160302100911061c0c030c020712020d020108090102121305150c0405120304030203030a0c05070b0403030f110f07030309150503010503061b130e01 82
    0x1001d01c403d4840005445403440100e9032140142c00000b0019141e10301414025000514a00086009030700c94041c9400c80c0d010b00311070002860140605401c141d014001402c031003202e104101701b8004240c907801e141c036500f5142c0030b2007620b00241c102d10442d08036940a80040c0310010802070000c4900e0054020411083e01801500c10020002020640407072641c1d582580908400612038450f4015030700000054034905003550280880340c103020140441c00d01c105042c100e40d150b0308400d81002418204011040301c0741e8042401000300816451085404450081d552007103c40c4900180034198040d60700020b501d0301000440c0c0d421a50f00803661640703240103100362202c003030340c17014108924421340c40b0040119809040c0811980d000340051012414144181c41c500000c0d182c42c2403c040c03142c0c00480100d002c4030000d101100c240c00f80500040b5030b50900c5403a6504050000359100001020179410740041c1c049894034018032001d9510801682c1c940d005880c1e2a044c410303000342024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 305809145 1250 305807895 305807969
    0x30f110301180501140603340906111f020c16050a0b031308090a0b03070f080901020708070f02030c0d05010203040201021018060c02030c030703090e06121009020406 73
    0x4010b2002010b501c0d108883c12695048007421a00c003104043c0612030300020314a400c080d0304c6170910207102c040c000118122000d007120298000f28030410140074019190003230810040c220904800c0c0440000c1d610a0034001749102d0502281d80d0207024019102e0f10305070403103a0007090b041600070139041d640c039821f580040701e010005a032680c0300f0710040d000c221000858508500f082501040c10400100f54484001d4030005010341c03100c3d40d04219602c16580300d00041c0f24090b08110440e0301140123a0084881e200079440d05405444452082c014a400030702020200c00c420002c55908122102c4001005446442e600c0340504159000750030880701680540034181c80c5201079081c501c6140100e840e4115000c1c509442c58483c0d0000b002400400825403108003d4000034440400140c416203103e0398901c0180c83c100904000310b0b540c060800350280900a0030b2a080795404a42c119019185810000d171944031400000c0140c0201e9111011001880c01d00c81c804071302c0d10f044d5140c41c081e8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 305810395 1250 305809145 305809169
    0x2c10060b0d0e120d0905070504110a12110913270b0f01030c030b06030a0206030a0b030c0603011d0a020706110c0d0e100c0218090609071d06040c030f110301 69
    0xc1a402da64036400030450080c000e08042003075152001032030b03110701040360090007100c00039521800880c08503040b108121480510200301c48072001d41c024100407411501a00c00e00003641101c0c00250303580211117080d44140040710311066809c07403a41c08510310031104140b5040075200068811880c581c0290250f81440100c4005848440c0c5000054100d0f90301c192100c032154a142c0b5803140304000503080903454003078030020381c002d03a50b0348014500403010a2000941c80714201b08062504a80841003805042c040c00108540c3d02d04603071540005e0307071601d550803c0382d46140e94039000b4418600018849440c0c4842c2105410a62000d040d503100c0701e004139540d400d2410001e4036149040012b9541c080e905a82010500344a61820020b00d0f2000c1c0811048010111121a04034011502c140c0f84e680310208015540f8020080c8a000704103400905400440240046483e000010300c1c131760055813200e40300a9064030a511440fa0100c409404103c0c0260030494400c00f64420710461195440d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 305811645 1250 305810395 305810411
    0x1804110a060e0102120a02030702030604150b090c0a030902011413060806060702030d03270503070203190f0f02130c030f062304050c1e07060f2c10060b0d 68
    0x7001d00b408403400c003416001001041c1c0e00d54914a00e6034000e02003041140010b0103041d006031410045540a40c0c82401c4c2030b440c0300b541d81c00880840319240300d82840364503440c041c050074544803421103207150318038580840c050a80c0d0006a403141495030311400004000288428000280c40d00e11083e03074419580d140300c50304c0f88000c03c042030258480107503054000240c1d4601c4039009034004003034424400e26140d11140c0f586100320107900c40040544854000094440840c80c0c2885214020200d140240b8103a10b069250000d03a10619207004000792095030108080d0b42d100c4602c003810300d07900071003030081d8102c03c88014050311a000040d01100d052000120302218860110b50901e00b0b600c5038a15a420740c18200405058040c055501090f001c011001c07142080f590140c1d02071030701010300c40d40c0b0340082c5007920884400c0404000310a141c040f041151250580d00b9410f2020312502c078007111034103400380358288200c02d0b400240c0a45031030000a50045408003400a120a40f5020081d0300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 305812895 1250 305811645 305811647
    0xa050f03071e0305091e0607030302180105030f0a050a140c090312041208030c04050406030503120a0b150702040b040204090606090506030c03070c0305070203030a0819091e021804110a06 82
    0x41d02000b001408500b0034040104c0c1410030b41c10450111400d046140303007403016000820260750020b03006400194000901c55a8940f038030b9424803203100c084c80c01d580b45207407080b108101248098038040302682c0302d0011614401d0a5041014010f50703543c10500c01e410200c040000c0b580c8200810fa009006088007686520b41c104295011100e803a20041c1c8812450f07901d09800c2d0b80010304a41e400f520030305c404603d0341c03282c0c45041302451041c0011580c5594402c1102e03c0964010401032105042100c83e80341502c5001c0311080c40c00b250010152140d51510006015180d81001d480d0440d00c00714000811541c035401001c02c0343c000c0c2e01c45000594992040c48810b10044805142d801e03002c0000c20a12071007a100310301030a002e49402800d024842e40000d06662124075850001003982c8c0a03c8240842c00c12220604e000c55801000b000316286d582001c0051400b01c0c905c008418409002c040d521460800003072070342424804406490103142603001d41c100080c1c0c1d14012514840c02082035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 305814145 1250 305812895 305812943
    0x1306090510031e02030f0a050106030506090303070e090c090d0c0612020711010e0a080a0506070e030a0b070f090819060c050a020604020607030309141015030b040b090a050f0307 78
    0x182c0c1e04805182200001e00c1d994501500c0111812a09485107022402012500b4014201c40c0ca11400012a4482ca5801c0c15403420707001400c0110305800400501800580003400c4880e0b8082c2902c1000c0750b651500b115448900401b8102a0410040c903001010081c506950303000f69886521317a040c0e05141941d082c0101d0092000051801c2c0c2da0058105140d801455000044400203010700030058440202c141880100c81080711715a0102c024460170a07041000110802000c0d4002d2080c58042d80740c01c030304d0314000390492041c0020600843c6206d4400d545aa000e048000100c0c0c0c0c40d0350300e1008003071241942c10019914203240840811101d4131481c00c69001d00300c1580248426220340e020410b1035440803000b202419a01c960520000300011024881e00f0317101070140c030288820201140a03240322410244034040c600b0020300c0022030b101c81030b82d0483d400c40c1c0364100582e50ba000c0d061400d00301242c054007e20581000c80707000c50000005040b00340c07140011410502c07905800000c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 305815395 1250 305814145 305814149
    0x60b0306090d1101150b0c0a0f0501091109060d030e03071e030c0501050306030303180a0b1f0906080d050c01061a040317070c0b0a2f0f07060e060c0c1306090510 71
    0x66a0b15080d0301300704801d070a01c05000b4400c0c1147c181c844221007652000703036070795032618226020303511490050180401001c2528200000303a8216031a40f400e00c0000f1a2040118001000d10412034081d10654504100403000b40a401c0c0c10300d0300c05030890b82000d445076814441100d8844e20b05101040340d5126a05603405810050f00841c15038481e000101124044882007102e5441440040742c003140200500c64011054041c0525100a403a5154501e0540c1740d040b00f91a02d0401f2803c100c4800d00240583c80f803074152400907107440481e13808901615041d400445810700c415030501da00c46600c030080048a04c41c200821164100949040f42030040e140050403481c05030008000c1c0e660002e004200b02100743c90691700640280720704a800c880c0700030240804080d842490081072400700000c00c204c543d528014810035280100c0108629400002d0502400c40410000034912003000441514500146074038000303400c0c1c01402004101612800c0d80c0d9506080220304204081070203001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 305816645 1250 305815395 305815421
    0x100f0515010f0503070c020d0b0603010b010c020a121412030712060305070b1809041202100203060f0609010c06020c0c0a14030c210111030a060617060d060b0306090d1101 75
    0x5459000302c8001d85050b0802050f507400d020100c01d40d940141c2d10740100b0072003d8803070b100210541c20a1b10605084a25180550741803000840000025079103c17480c4074221041000910000c88080c80c4c41e081c100c201e550300b540c4c54070906426004804980d4080c40c46040d603070742c4028201039500f04040c152080c0e40710140c0306401c002424041540100020400c101c0d40b0350304034221000c0c0c1c00108000c0c0100301d41c00d440702c1c2c0e407080440a01a41c140002030354040311103404d5080d0b0400d03500060032001659101d40c03143c40d0000c0d80803030a0740120324041c99507411400031929600503c1b0030544610840c0303c901e04c1148007040201e10009581c00c1c04100c1000a0010b00384c09428505200c0d030301064010440f0020f02040c40c400261200340100581004008070a6446e070900c0884201513030700c150001340600601721150003840d41e0780c156181d48030500b105c0b0310206000600381301d00201031000c521030301402041d04010480800080845a038503042d07440c6139070010020116402c0b2001d84189031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 305817895 1250 305816645 305816657
    0xb0c0403030f1b1b030b06010c20030c09040f0b0601090b0a0c050c1207090e0c060d0b01171815061509030f01050709080c060708090d1103100f051501 66
    0x5010038400d240007211070f80540d40e40b040c000c00c2c0e51642ca401e86a144000c003c524a451014820071408203d1541c02007400e00f0481d40d000c070301e076681840b00407a002c074111500c2d00d10f8840a8082ea010011900c09103805403040f0781d6402d140c1003185882000e504203035030005e444808141e480d407103460080101c1d001d49441900b003420540c3c5c00c8071000c088400c1940c4074411803081006a0740c4440c0c420003c40780c6c86004005e03852800305440c00784c9215065542460b0041820130482d030700c4000c115082c0000741503001625110160051758605400500350000c01a104100040780f81c011108041511400b0202c4802c0041204281003014048511641040d2a0010b05480010100180a000c40c0040640d01703131744003a44003182155801c5541d8000140e240100308210f503001c2c41054003c01c8281c80680c034010003070312a030382244241c183c000e000e0041000f03650144905d81081e644407500040649814028010035003000d0000000080d80c00c91070b000214a1116078100c500c0354045042c0c40d88 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 305819145 1250 305817895 305817917
    0x90f0d020321100509150a08070e13080c01090c140f01091203050403081210060315060c051f050a0e01061406030702031b0313060503071715061201030b0c040303 71
    0x1d5804000c3c1040b00d9601e0210302c04601d13581c0d103070b003254443c5040038905410015040d08101034012180e0107078190382c0060720180f000c90000040694040d15a0540d82180107441c503003030069109900103c00ea55203044a0402005040d11840041f00c42010260320807000c0081040b003040010711410340415a440820403003d0602c1308c040c8105406401c009040690740d0b101c0460315485615190364010201c0100101003078400030440c0a40723024a0100801452041d0307240b40c0c038a241c0900014031041c1ca4103c0104042044028014622000045c00c407081030a04007020708000d0f1214401542492178100d20542d0511030803040700e5940c42204d0001e4185400c2c008140c2c40540810304601003044818140c9640140b200c0e00c00f40c2c0304000b156034010a510f401031405580d003140080020401c14040d80551200c3c40320a4000c100c112104070303440e02405401c140400310740b0759812407004550b52080c140260030313007030481e4011042e41906035180c03c14620544298000180859001070107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 305820395 1250 305819145 305819197
    0x9150315030303050601020309090103060b0a120c140411070b07030f270309120b09100507052a12070605010807030b0a051302090f0412050301050105160206070b090f0d0203 76
    0x4416081341047c0181e0345059801c0c00810240c00090308244d40043c0c50300d0003a0388904008100f680141014030680c05001d009a4800800040c50312891103000c48480e8580d8059032035038040c8201c10392005022765110340070320304040b44080403100c00c0701080c039020310b002c102d4215001e611109040603000300078401045100039550804100d050701041020a80859640f039192903100806001e1606070b892842c1582410340750580024010f2081400d15040c410155005001d40d440050300d600f880c1c000b024070900c03040b04800c079410810130a105001e01911110b48500c01011041c4c05040309008a07070300d0300442030f035420031444001c00d4070311940c002411004090740500d400503011070380d104288401c4d800180000c40141c503050a5141c0c008288410403d800d5a040011411800c08a05641c54200003a00b40e000d90815a07031000ca010b0044811540d4001c1201c188d03e0344408a0f0b025428090046581e40f02e140e040800715110b8010705000a500000559800003042c9a1024801502c041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 305821645 1250 305820395 305820401
    0xa0201051e03070c1403070f0b06030f1f1407020a080c0a060515030c0d0b0118021e0c070812030103080c1009060e1536010c09150315030303 62
    0x40c00c040070791000421150000d6042006501455140d60b40310303050046410f0500030b40400409007002c07035201f08403a500288520000d042c0c1582c200b540b4141a030790b44c0b000710307040c40413003104008580510107a1500807401d00070f600302490640c1c00c04000501c1c0e240c507a0f0f110750000707503410300c00350740810180c000140c0a000100000501304094038000c10695460000359101a2448919103158108490060408104c00740e10224202e80f400155042911440300010b018007a00595001503c81180c011047d6011031703482c105440700445075030b40d1528120305240c020b480804024029140001041c140005000050320f0f9000c0d0514030703503481e5990b400100e520100034140240030392080d00700b40c040e0510817800c1007402114040340421048003103a0805000030f00300390f4555190000d1200c42c0c60600b58a42807074404131003546040960044115280454200d48103007903080000070301a0b1688000341e50b00301c5040d0716040410110920055054803040e2031808048501d4003810000b081c401c1e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 305822895 1250 305821645 305821657
    0x309050606040902220507081609170304120b06030f0721020a15110c0109080a110411030403090906060c0807031202090a09020c06070201020f0d11120103060c1107080a020105 77
    0x28920b814504801c565061702148a558015102c2c2d5078404011005130021400c1d42d001000d60300310640c41c0c40c00080507040480500034111a1100102102c24010040003198080d0124000340815070040345880700f15410102e80040c0280200b00040c00d40050000d200c00c10b880c0c40e001a00c4d0354003000e0050541940c0b40d56416a8480d071050740000d501c0040c26154003a040187d0384100007510708045080c50818001e0443e41000480c81c81000030700300100b40020500e5220124005030892000050060403042501c091290000821701c020107401c41d510b10100c48047c5400d00906903540c000381c41c40712020002504032901007064900282c414a403540c404c03c89980014100070820000c9802520745030441d800d115800920400075420400043d80d02080d984020342c6889044131400c6410b00440180c0307260540c50705100c085401d205070503a524200c5e08070741d8145035079403810b000000d00b00389202e030004103003414504074020b20041a180107403602c400050141c0c0c0c0480d401141c41e0750000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 305824145 1250 305822895 305822899
    0x4120f050d0606030209030c0f0a030807060e0d1206120206030f04030207080f160506040f0b0304081207030f0e0a0206040612020d090318090603050604020607050a020409051c0309050606040902 85
    0x10030001c89424424418000074003419500141c0318061101807600d80044c05240c24482c610800301c62003079603100c003a8441901d9202203c5034441c0020301d405005405101d1031000e5a01480071101280c5d60301c4940b030502c004200c03038140316135981ca400340c40c4991168500603402800402c00540041100d81d0442d40040c42441111031b81c0d55141d04442c24504880306050a540003107001156209044c26000e001c1c002c116605403030540b602000b000040e185115000c8041070100014040c45419800e81d400c0c5803601e4a00012031800d1040180188850b001000034545401262100d1010010340085c690780d000c0c0202d803915040c040d0a4410000c039130942810039030200300c03075100d9400c9406002d003814840c0d00e5106056503428041d15401e04e454000f00007107840d040d010000706030000349041c2c001d6011380b1050380e504018100242070120b0240069005810071044200300b00000400300800c1c0c0e0440003400700700801140403401d031000008080e2407507010201140891405504c0b1540e11440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 305825395 1250 305824145 305824147
    0x7090b030316030801150810140112180213020702010e1903080c07030b160203070609080918010602101e051509010308090310020406020d030b0111070909020f040504120f05 76
    0x2106581d140b0b403000405080f40000c0c40710f0010441883e400e2502c0c0c42400c6941410103807031410307110b0782111b131003103216404201c000c003074100c10700d64000e0f0401035203c8c0300d83c0f07001c0c00035101450403004071213045032040b800b4281c04000b03103126058070700c2079842d12541655286900b003221420051030114144c00c04035541240c13140000011303200c00c010902e01d1403d0029160907480e40c1040e030f03000c150040c00014103180c0495004960b507030101c126606154002800070f0f401105003010807040c09411901504000e0824407103040c020400042d50480e1034581c01c0300d03c041501c0614406584000c64001d14010043d4003028100145400c010350080d44030f000e5210340c0c202c201c0065200d0400780e00c00e9800c408005200066030405000300410168175060961a0030301c0d01c08020360300c0301c00d030b8802000c15640342e030035810f00d0f8400d5489a44039440142252141900d800b5110008c041c19041248600b0700c403a88411b20782064014107200715005040e0780c504980c602816501d2041142c144020414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 305826645 1250 305825395 305825407
    0x103050c1c11040305100614090c0c01110d02070c060905010507020d0f0204020f04030b0708010b040608060103110414040f051b0a020f07030c03020108060103140c0d0e01231302010207090b0303 85
    0x70702e01000e0b00c01140100000d0000c6c01c1c0e8a5520300c21904181c0018400c2103d690341c0710982c1c0c44603804180c000420820290b80c403d0420006801000c140c840041201c00010f0301c2d02c0303000159009421241d014096540c1c0b011354840c020b0354840b07002c4c41014007242007070050703601500c1c02808a00b02140502054907134084598009000c0381d100e43c8500100c2d10f030100d0f05000707000000440c0d6602c1074131400c2080440d4140004108980290b100780010400d108001500076403107500440000d0140c4940e240d104c3e1b0705d948114007049401852079000314501031440c6010503030340c000c0741d01605002d4084020303184e010711022044e40c030803260b00040d4883c4913168650000f0800100c0015030041b102c501c0c2050440c8001030070100003506003030401d030800601004030800305000342e030400703507103001c803542e9200c502e140001800c02011080410b501c0c010800c91054044681146219180c451b040078580d0307a40c448015030056031700080d0040c0d0083d6802d10a48100c0e07130007190703a04030050450342449 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 305827895 1250 305826645 305826671
    0x30809011e021c050103030302071406010501080a0c20030c160302100305040c0f0b0d0e03132304091202060601090605030103080304080f0a09050103150501170c1201080705010e0103050c1c 83
    0x4d13401c0e48102c1c00070303500141e088280050201032501d00000500605525498600000c0c02004080d0000900300c0e92004120301541c0201d01303207107040840c0e218544901203400942a10703030700102e00084044c080c419046c200840c048001c0b80940b60700810800282c40402412002000000c20449484607420070100fa0054000000c200034034400003015598032441d482d500980c1d50602c00d109c0c0750703401440600c141101c608104070a4404500c0a5403a4221720302482100d1041c410b0802d41186c5030083d40300071320500d80b24030b00c0b80054a03021950643c442c800111201011441400d000072070034001800007800010055030014050320980781030090290894200e6840400f203180447e8041c6c400300b00c5540c0501030b10320040620010b000e003a61800001811260722000c150001d174a144000490b445505410b8443d180c10051030308a2668445072102da4407402e50050901050786030040455561107030180521548001107107e00b000e52000b162000c0443c0707038085e01d00298071084020110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 305829145 1250 305827895 305827901
    0x70803040c050d060c030b220b0a0909030c1e0507140105090406081b0402040510030f020c1c140307090b03060a38070519080415050304030809011e021c 67
    0x104d0141e840010f041e895410081d08a882c1410003a000c6c4000c64114055031070340e40c003070640300c5101400100da4552000c001641c21100b81c0c2122100b14506000c8805041d03215182d080c00313030311401044102120389650402d020059043c0184164080041400080c88050303000c000304206051075801c1258400c00102a0b0701c858000d00d03025800f2100341840340f64030304405204540290380c210f1400b42031101243d510060148042c09140c0c5444000c030450000703904076030b242000b000941d50b4107900c503070410700d0a12070060840b00084962014a150511400440e401030140362171315170b980f0b031404081280a80004007080e602c012440c0c0b001487c92403c844002c28040c00394002090b103030607031014560103040b030541c00010107418003034280012400111540c01215144104e126950540b804045903c01d0ba00400014011420680c503926000006140141d200307031903036400c544d510141c0c40d08030f42c41c0320b03281300000812410822a40e41154000c214506800480f00d4900007441500c0c3d0030303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 305830395 1250 305829145 305829169
    0x170709090b13300f080403020c06070203030403020a0915061812030c0606090e071e0e060604081501051008040c031407080303010b0a020f06090703032f0a030306050f0303070803040c05 81
    0x1c1c182c0c00d524103240c43c552101e0825108031442c2800c1e221410640c038020f40d0750318400c8000c1c1c007500000400e601955802c00554004541c0240b000100701d844000c0b11000e040860710048414801510105006000f12140c00564503580344030385995141c01c10455080908843c2075081c44007200e8040040b81c003a006080c00f07044160b401140c10000c010030700d032804807103a2210307951006a122004204c08594101c1086900b00c1c04400026180c440008810b88516848001c2c00d00c50820140c0014050400d01030403103000b25041c901196500b0810745d46a401250020407900000d241880040c51103004150149081e17021200c4071a1a81c61442c91070b4420b03002504800707808a031041d45242e04000e1600750744180c0000d08014200148500c6e034454850100405005c900c0c81940000c43d0111100203d02e041d101d40214103541c0b41f00660344500703580005800180c01c1003400310305406e02c185003034a15140034009503c6c01c041340c0c590940a03040917200300c8182100510004003a0707904401548 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 305831645 1250 305830395 305830463
    0x20409090b070e120318010207080a050d02060f04080901030c0e030102070614010b0f0a03020c0a061112090601051809190b070906020105100315060f170709090b13 72
    0x7086080104010302003002590009120f40c0714036403c800a05400300075605c1c60f100c1c02282290160716400140c0c1043c46a411078032640c89804000002c0c00000281c07480c0002068081c0d882a854100d8900d0340c0c40030407078024285420800007910154480c2d40855441c9116203007c801c0c0d102340320006400d903401345100381c0c3e100361030328202030342500721546841c0140400f40502340f61108002c4c41d40041c3c0913075241c43c020300d940400c6100310f41e50140941e0310900d40c0107608001c00039211302c4104441e041001000c50099003000020400e100004015042c0c4074000d0240380345515802c028019040010420781c0f0a028070011072070702070740d200e20901c04248903080d03d1103103141100c0b0007056540da580c0a4011607042400384209105489006001c3d07075001151a808684410030302c0c0041e14866001a900340412680020406404200071151840903c1550038041c1d9540f000d0381951403049010b00003107507090110700c05004146454181510030200e171603545080a911111071002c4a803659 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 305832895 1250 305831645 305831663
    0x190201060f1205060a15051c05150a0b100912170301061707020a02100e0d0c0905091002090618190303020312071803023007170d1b0602040909 63
    0x5410000248144c85e44900b000c10100704081134030601d40180c452a00c2410b0041c1d10818981100b07002c009003244034a500002200d0750100d2035034400170601011101460918075000d009480381c50a44191544000701c1e03a941d5400d94140b491110b10f41c00ca14104441d440c0b021300480b83780e03103280000f40d402400d05850701c0e0381c9601102d950b0060720400804140c1150014a41c10b00107943d2540460341c29907881c40e2801c0402250f4002c90721420011701d025281301c2c40c0010001d0004140e40060f0710402e040420f81d04034609500741941071340641c0c4612944001705221030500417081d12010811580018403c03d511031600720981d0201025800c154010303000007812019032000800702d80e4010409103001580f40511100c801c0c6c00d0a000d00000384500f40020200e00d03500325401070800192244951031083e403142501d66596481c2d144642c1c13401728004402c01030a450007240000702d01080361036089a0510074a0b074407244c0881e0074030450780e0603424440818200030300d2040c0c0c0ac42a06c10a005c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 305834145 1250 305832895 305832929
    0x15090103061e080d090305031611061305031606021f020702090103050105060f0a061d03030d110c010c14030103061116081b010b1e150705070e0601080705190201060f 73
    0x381c10030791051000c40502245c07070001c00008100104607060b0201c5103000c51023800301072030b0120904400e0300a45a10910100c0c4100c0307822184120b81084074021400c4840410300e0000308002c90009201d8440560400612040f0b414414028059000f03103040d401803600002380e001405800080e0400c3d51140e64800030440705040030307080b0404104040302c80f0600645003510050050a0003030181c00d1644151811900f103450820940d042d80103409000e00001c0d01041e55020260007100c54000c0030741c2040d000c240e09901804980300c0f10706203006078625680c20364480d58081d1041c41915580d4450030003120415004001c03862107440e00c500c1005503a130024018121403110741400001c042c0c0d2420814004659910404000400490807041000158840000c011100764450340c80d82110002e62641004008030303a0f40280c5901000a82068442d8001100d115400f00d45c2280440c4003080046480c4110395804071140c250b40c4000701e041501e0b400714907d02000d903800095100c441010f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 305835395 1250 305834145 305834159
    0x60f0206060f060d0b0f100e01021b03120331141c0c05011e0b09010e010302010c020915193002060304171c0605030c15090103061e 58
    0x3055030010011620703100d8120301800024860b02c02c0031205001e80d07503584555004d81d12060800d4600c0c510041011040c100c45200261008894447e5103006000700c000e51407800e03a80130607a0000e104081c0080c5600d440c40035203560700e1341c03001d4488482a01000c10f084840c4001c95200040d40007010180c1c0321004041c50080350341c120703800c15013140380c01c994000440141600707d244e2200c1c140b850240c407a5806401c4c1540140340e64068099440040300e0702140c88821a00711401d501401c0e136000240da80d1b01e0708040c00a043c2800000d0010341220807540c05032a01c2900190041541c8503141100e0302160005800342d0070092800b0130741c1d000b08108000f0106205040507021485d2a600194414100100c3e1680800c0c0c5c10002c0c85040e0110106060002c840c0c103070102c400030718076016690160394054020b1852018501d101a80c00c3c040c0c003013114180801c582c21142c40290084a503480c098403c004503800c0740306810b040503621240010f05500b0305041040002510680c046001c1c00c0c480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 305836645 1250 305835395 305835403
    0x5010f142d0d1b020105161d031006050a0503030a080406050709050d03091e3f08030a05011205060402040b240715060f1401030209060408060604050601020115230406060f02 76
    0xf100205592409042084902c8000d10300001c0108a10f0503185418440c041741c80f0070300900003240c2d0103224640c0d41d083d03002e2060707201d1030035034070201e81000d01641c2e43c808244ea00d1003502c800d100001d00b48800700c1c4c00999580c1082e80c012106050568019031620040b0703a25281c20403050300014102d20081142c550810180c0b240900b107101001c40f154140400702941401c0f24248500c82210402c890024078241000b440b078080384140c07506004002801d218070142c009842c4c1c100c90b50725000001800d19084cc01544040b980900070385290354894003004020102c10a41c1d0b504840c1c44101034004e0034186c0350400c10030190417081c0303448408038200000c0321503068521148a038986401400f0f000410741c294000c0300c58044425620824000c0101c01034040d000b401600480d011801203002140801c0c81c038031800003035604020030341d0340c040128280c03030907078030704409800f601c20080c01030529004510540c0d900d0410f0700304081d817014011800325046075021100280480c00c100000e558184 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 305837895 1250 305836645 305836691
    0xb04090f0204050f1302060306150a0207140d02010f0507050c150c070807080c060a02010b031209100201140a0e070812030f0c070804090b030f0d02060105010f142d0d 73
    0x1000e146028a05584540c90001799201d029200d400c0100c0000c000d503270380c3c218003011104418003181d103400d52400080e54414150113450448080700440000d02d041500d40075039101e4059403190290000000300766120b50103c6800d54007805402101d80a680710203890362198000451050f0b40c44008102640c00c000c40c542105400f038100c80e00c01c000318240058101c4180100310380c0659182040003099004142c480c030780035014000d001e90481441d01040107460b2460081c0c5050b9946004000224200c500d42146039950345c5411010030742c1d210695000000c000c1c800d8080702e0040346c460111307038548018880790860840300081005580c5060220450304944e101c5038942c00c6c00035a076241007490107140035014040b603680240c03120f80e0780c2c20000028500500401c0d1820800e0390030001b900c0d41024001c0c01e01140d5a8075424007010310501401c14548000740200d03050444901540300300c400408081c4a00b0034980080c01c1c040d50803980108402c803800c08001503254076a0313201c100c03414004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 305839145 1250 305837895 305837911
    0x6090c03290903041a07060504032610181509020726030604020d060b0706090c0609080a08090f220b090403020616050d060602010f050a0c020319030b04090f020405 72
    0x3907090000200001064a0a98144102c152040f41c050604440503001e12440504054181000e200506801549000758040c505440b881c40143c148a190140b050540b1100e001c42c0440004000d8196103401d204c1c054201c020300424121206d50f80100e104455401028601ea40051040b00700f00c81d040d20301841c460044080c81003015100402c1c02c240c00000d00c21030090782c00080328480d080d00c80d400b110107004009144c640f41c00b22070511074014040040122101042c40ca0040785c024003903d1409c04482260008051045d05a40c0c0c0009a800c5183ca2035082021411200e50b250744803d01d038a000507032404004016440d0755800e00680d20100002400740c0b072030f08d0a2001281d400b094043c7c0c00f5825102e03c0c902d4080f119400c80b03c41c0708000104500070b10305030010a00e55410742103100c4900c4090401c1c0004d40340c4410b140f00700e03540b4555440c0540e10800850360382445560350a20040c3d0b140c240003c0d81d083e000302150940d240c1e038030111440a000d01012003140340a101e990381180e28 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 305840395 1250 305839145 305839223
    0x60f0504060b1e0706090f0c09050108030a050d020906032a0703171302040513170a051e040801060306050402042307050c0a05011406031002121306090c03 68
    0x54482e0244042c49a003081083c01c40d4040c640c85251140b25084943c0303903500010800c00d280460418460000c0740610440c1c0300c17000700000080400080c00360606803451200914030b05180110f06070b866a00c08001c086405030284507102003907488001030345c868112581e4042408901c02801140b0342041400031582275405c0c09028040303030b071010b00194000140383c2240c029445403021220034090301e4000943c881d081000b006104490b000c5080c1c00c0318810090149202e10b503480c0d981d5180203460042c000940188102000b403c00303085410041500ca1042628042e1200f01c001c0c25141641c0098404c552298144400c5040601c035150300107040c03001403031010100501c5985040f00141c98501013200100d510400d0110600c038485000b680300000700038004d100f001d0141100c404942c03031403080c0180c03560345c180400740c0e00884002c6455002c000c4102e0f554880d45a80c01c2c0c02c03041c0281c550315968104980040c001209510145002c0d440d854a80528014101001d49818070f0b000341c001c1c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 305841645 1250 305840395 305840399
    0xb030105150315131101020c0a090e15010515090a030b1303090510141e0c0a03080c07050a240e100609090507030807020409050312150904120e060c030d060f050406 72
    0x12514040f0000300c3e4001500881c1c00c85c0400101d01d0000e0f60840558000050907002541c072900380c0c8084031041088003941c0f20808907180c040110385c8240b003a160480140b40c407100c07082c92006d000700756904000380034403040d9407603403114040b07a03a08039024441208018000f00c20b040e085407040000702400c6600b004041a40c1d80010481000c181c110004108003080c8440e540340c40703940c80c400541c9070310070141d1100b18004810b0b90b02e200a5170284c021444010210700052004400c440480341c000008005a2404d6952040318241a040102170800d10302103203080f10300075003d004488462140180b0b2064519038511044641950260794013524100001e00083d40c0411040c00300c0340c101c5012602c550f500d0010074040c00440340024401d003c002100d4408003c80e0345554000c1866184c0e00031991a02030a0040c03e0390161400b806000780c0c082404292845000e500c2502c002c05810607041c4035120041d41e2035500126504085651141000e0080b010710400b003000500d8102c605001c214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 305842895 1250 305841645 305841661
    0x120c1a0106050a030f0e0a0501091b0e0f07170703020306040b060313030302030a0605043e0f030604110a020703030e15120403110607081e04030f030209040b030105150315 75
    0x48545a003c0e800d250302c0300c60141c0b80007000c0c0d10500030348240030700f0360701190703240c2c6020380c001c05c00d2440c125103500c50540100e8459900f600901c00755a6484040c50307090f102c1030f80203c075034040105100c0802505070066075646c29250400b502500c5141c9015880342130040c1080152101660841d0207030700d0a01c01c000041d00200041503a143d0142001652921450785000241c07055070040368010b402c000f000c00c3c265441e22a056048000d82e4440540401400388451450f82d01c0705800740b00000070f100d900d0f4010004802150015401800060013040c0c1c608c003803010344c0080030701d0005030b08081c03410001d05401c030031160729a07441120112900d08114a0040d464040d00412000550001c40000c4c00c00d0700610200282d203c40104403001460144801003840400322212040703680c1c0c00300615400600c101c4180d00869058172251890341c25900c0403402908605107582d030040e101c0c0b14450890718288502030051100d02016241cac0c495401c10705250004c055610b80c1006e1076202040224 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 305844145 1250 305842895 305842897
    0x1d0a0c021009062003010e07030504020d02060d090c0314010c110601063c0909150b0904020d14040203010c020607140901030e031b190507050f0d120c1a010605 70
    0x41000c940c0000d0000203414100000c4c0301404a00d04044941e13039a02c00100d5004000e503040300d11510b8a15019600c10300b04034190303241600d0094104402c251291b00510300480a40708240600e640090340c0300706a120701c080c041541e80309442a0000b16820182d0800a004080300200b4a007041444000418000341e0340f80c1c41403082038200300ca00c01008211185c2510243e1a054100d14480860b00300d070000201622603003610800842c40c0503d00040088080c00395000030040900f074400842d00e0200310204d16070140301c056a1081d070800c0a945102c00d1841046a804495a0b20100900d4584181400c40300018440425913025800300811180e00c03a400401e601000101030f0345404910005074003502441c0403410301808085101c1c1c101d907860400280400c40941c040b80c100a034540451907221207140d1010b003e94201c25402c0c02542008140064020781c0540f050030075203480d803102101e41030000500800100c02e85110028804044400c100740b04e2483c20381d01c402e524180001e002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 305845395 1250 305844145 305844163
    0x50112020a0b030c0705150907060801150e0f1003090b0a0501081c03020f031302011808070519030c06091d0106080a1e1a01030f14011215061d0a0c02 66
    0x2c0c6000000001c4c1100402e40d003602d458560140c11128200d01c8403810451500b8211210b200520446000040325445001d085040390104840300c0340f4038884103401c03039080c1c4500083d2030b084bc840c0d0120702000d0b160140e020610303519942e000900d0480505d02100e40030805860785c1c4040b4100801440251400720f0480c940c0c00440e603101c02080e0324400242c019001b10349000010182c04020007c1c1c1d0030001031020070841c400d0340c0340040500c04510710f08140090b801018250350041500344502e0034410811490340103110140e0340300665940e94820040c03040d82103940014481c00c402c101244648801c6402480104030300b032001d40c10f041e0024030645c402490f510700c06895180041c42c100e0341c0d5401c490900800034040c0030031890f140c40040708030201c0a2842c0000c0c6005d020b040181402d104400058602d2084041c00303903e00810725410301c48408003a145030752011913030040f20105100d0305e001480c583e40001c4808016040e480c84040000b000354108030305140e19094115408a2100c4d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 305846645 1250 305845395 305845409
    0x90608040609020604091a19060f020c1f081b0307030c050d050c0c0d0201060806010e042405060406120507032d0b0610090f03170906030a0f050112020a 67
    0x521656141888009428110070181d04032600040202d081c401c03a820180450788004032601c102e40180040c0022254403444d4030310080d8201000348001d62107a60700851349907042c81120140400c0030006400c01084203589100500c1d072000e50480c807900042e42035800301e5940070b210002c1360480c024144a21000f4442002c0544c0c81c0500c003844c3c7d0148041e82c814210750801000ba91070703d503905050b030341c1c0500e400318003e100310110b405256105000d40c0342070b40c00c0c0c0ca000d403903036920303120403903981140161003101d08101d040800c1c01e9130300860940d8460102804804102d609106040c401114140e030042d81c40c610307068406001140002440b0f000700c82e400404c078000604a1a010f581303000302c08180308001d03505007040b5020b000704410303014000e82c0210384c0b4401c410b404583c01d5519944503c40c003d15910f14040420218000942030b01c0075800d0070315250714040410000030211303032007122020040380c0d031000e845408606a1140c2800342ca45c2c41143c40404841e40c00080800000c4e200e43c103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 305847895 1250 305846645 305846657
    0x170705090702120301031b08190303050a09020a05040e0a02270606070506070f0216060302091314010b07030c140f1002270f0613090c02060717180303070f140306010906 74
    0x110301c54216447c800c01000b05005035051014200012031240b0f5030940140c4c0024106000328102007030038452010080c0c2c1c018010a183c40c544018880075103510488a00340b0b010b4003582c1c6002d0703242d150711070603a66032409036100c56101003801c81c2c80080340a000d240c0203e0090101c0c0000950006a00e07400000300d050210000060398070882c507200701481d00304820044001e00040f241c4d059000381c6600c8108a40c1ca86018441180341000c031030703013207040071002d40c002e0004001c00b11a20f8020314038a40a454103500745804c903100c0c80d00c942403140410f2403982c0581c012522200c070600000258114640c006e624000900b180071001d403607018104d89003040152240d1045540302610740e1a40311002e8402c98503a13840c441100c48a50107407154403045810103281c01c00302480411003d200d00d609032a10345041d00f080e000030845043c0280b003d000c0000541d461098903504101443c821203440c1da410b60490075030800200020122288858041da040c0140111aa0072199850075113483d0f103444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 305849145 1250 305847895 305847923
    0x304060908060709050108091c1805100e0904080f1306020d020a051213090c030203100905130f11042d0902030706030507090e0108030d0612020120010617070509070212030103 77
    0x110304003003a48060f049400341c440271005420380c10040c8100f40a08009080103810354403000e00c40c5040804c102c950000301405081801482e02200c05500140503084090801c00102c00c102950ba1000c0c41d079002c6044103010801c4071582c1000140117642c85440a4032030f58460742d480654480d42d440c20000c002c04081680c01c07862a407031035008002d101e010000d10000c814410060f000f94016a402040d204114070080b500d0502ea005040c00350b19030007414030340381040d61203000310000b00039002c44510807040d13040000c940d1940512040d0000000c2c105078544c04050101c8248035090004007100c2d42451603040c0983c1e40820b002040300c509003004220399446002c210f40040f01c94005c40501e20307503140041130b200000000340c6545001c59804122729a10b500000580c5010410000e001441025440c01e400011180c5241840260000420b000340c1300e03020598048a85418002a54070801d8100001e24000d092a50028042d0001c1c003003140458000791400c0c4814080075000301181200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 305850395 1250 305849145 305849161
    0x150115030b10051b07090504210e0d08190215011d22020a030b0a0c0302032707080a0303050405011121090a0b07111b060702011404090e0304060908060709050108 71
    0x883c028880c4e40e0056a10241c1c65554036030041005840c00d0729003842480d883c0c1c4407110310080c0720803055001d480e51a00820307420b040042140c0d003000200c810110621125035800d908a240700045542e0350050b02625549174030300000315030142d0040d010350391584040303c0042e4690400a0300401140008842e60000c003d4184909442c070f84002e4200d540d180000051200e19000c50340100c10700842882922840400ac505a0200b40d03402032058400610000103460040c5030200c0d18a55603065030a101d50342c044260030000c45903402e0740402d440e1020002000001e01c1482120f01102442c2d60034400c0c550314025802c004c003c070004500c4070403408601d82e040d0420001e0300c5d066110390380d14010724001c1b400810b601d410b800c140400348640b410301086138500003407041c100c03500034105600380040c3d42c00468010480058015000108000c0821103880c4c5018444041030020021035030366150680041450b409070b88201403d030088010f000004d58003c05039000c03900c1c01d10b480070b05603d070310403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 305851645 1250 305850395 305850427
    0xd0c060b1203121b0406140919060f140a051b010f180212070b0d15050409052b0504090509010b09090d030b01050304050a06020c03040305150115030b1005 68
    0x1d4041094480403074070210000203d51602c0c45101c08210011a404500e22040205d00680c0522404130b000a04406500410b40e0042e1801280041582403542c81001011100c0007994014000150281003014409070700456090741054101101518017a21000c000740507024542c1d950414200780008080091000d401c1481220406e43d410410700b80340709850300d0780e190b000b4170032402100019061280184003250000480c3c4202160524112a201e580c100400b00c2c2030502c2882070350440042400d0b00c5034454001a13074410001082c40810f402e1501400c10241d80342148024920210200966030040a07141120304d0010003181c0b07919014181405443d4443c1c05580003480a4200184410001103500002106403000c0102c008050011141c6100895010b0210381c048401c4400203001540200105a9508152410a612a9100d0342865102805c017410205000300500401c104850b91054a107181e08041080c090400d02081191144448002c1030103c04980d00c1d8034081720b50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 305852895 1250 305851645 305851669
    0x90b010c0602030c040303091403060412021617121806070c27060807210309030203030a181719061805160b090a1a091807110d0c060b 59
    0x20700640d220f01e0051401a810380152109500141310380a00146644010074174070f030044c0c40500076008070303a035a480d0b00030801046581c2600314858041c6100b22407030010a800081d007400b0304078503464508012160714141564801180c80441000614407410308014142c02d420410345107aa114401d40c2440501200c56500140c01c00c0104050354101c03002c51141d0303280000200d04100020381d140d81031195102e00b00d01511040011000320324032000c40c0300f441e02c000188a40341103107500d40c491307001c13a0542e0480682c14010034080300c500c0744414071404192019042c3c0380c3d99003100040141419980702e00260700710b6050319000c07050b00b0078804a50015195080f01c8203c14103d030b00e00d8075110741d139481d00807000500d011102001107040e480c08c80490b0b00444c8c1c0101003006190406010b00e1061402d0102c02022890422034007000752140c2400c0103040342001002e100f240782a0340701405844240b49030000075040702c5090281c050300f040e5000407880d000100050810105c4012441c040009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 305854145 1250 305852895 305852903
    0x2010c06020d050412050c030f07020f03011107120815060d0f0e0c0906060424030b030a03030c030c08012306071e021e030613061d070501141201090b010c 68
    0x50b030300d1160b910641000340941e208000080702d034a1464800c44160203001942c50958000b0001a4043d1001c0c0e800b41981c4d60004003509480d40d0700704000b034212020410000c03841c0501080010074002c51818124465003141048507441c586421000e400700b5401d00c1e007602c1142c001c240d031030661080703501554010050707000400c10ad00c08540c1003a03a400030b00010310322469039480001c105041000c01c2d1812100c55210500b5003508580c101c070800d41b18036800a00305541c812030f616095408106690076030340070313803000a840c042840c001030036500d02035001c100784203281004000b00801c42d100560035440f034041401c1b40904c03400025106208680e005401e146040c08505421600c4490f143c800030f02c201c0300310307003280c00c000120003a400ea010802c95140c0c10440004648c4910f01c1c41c080c2800340b14120018031454480c0c40d40c203080c402040c200c0801e03413203a0301c207000703658000104c0a01c4080000000c0d062660b02e042420202070305015020300709850701100c000702e134000d6905020207540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 305855395 1250 305854145 305854147
    0xc180501021216060c020c1302040506250c0905040c0501030b090402040b030c0a0f06030c020d0c030c080d020315040e0c130c211a0f060313240e06090c0d0f02010c0602 74
    0x117803a40082d500e55480d07460700e10400001420b481c010069100301d400320381d0003034003240c18126072520032a80c24580e03040c0810210340c407aa041c4c000480c1c55207031101504c024540000d2a0415060071200110a9000345051502d0040f907800590344841c90194490750407a808103180d020240440d00b8001c80d52141c503013041d581100400d01800f441c811304140c807045d075030801250081c0302d8203e135220750800301000422010350034880406c0c840c8ad02401224024401c107882c0c43c00c1284d10500300c0e8400c890400301d10862400080b014a0180611001d88081b5001091981000c40018041c2220a24451042596a65504c00d254007c0710030f09006880340300032210f051780400c1d154024042141c03401c4403401525200c0340003441d00d00070f42c0b80d25440207403540d41140e0b01c0518104c00c0501404c01914145848070000101c030003020340e110f510350401c000c0461016001c0c41168941503003d40f1010711501b005000004a40350450030100054004580080c03010f034900060b103198040d01c002600940c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 305856645 1250 305855395 305855411
    0x3010f020703080603190c090e01140106030b031c091710050c030109050c03010e07030e0f01060b04080127120e0306040f051005091002090a090608010c18050102121606 74
    0xc0c11079000f501c42d101c141c040e10b101480340100107030211580f200041c010b02d94520184a0809a07501c05600446000c000041c4a03080c41011074094209a1000d000681c0f103e0b04040b0a09080c0301c0019500c19140d15000803004908001d0080d001c0c2e8054101289150054105070030b0003005100e4286008013030400060078855507101d8254800d02580b040c1f1410000071840303c1d40e00c01c088a049804402086049031145a0100d0141000c100d14824511802d04c0c46240480700780301d03141c010038181e04c0fa56a25481d150189080d00c18400b54010085c504c0c0e03841618900034441c0414039030340d01201301d0404c030039038035010b560407440803008907058440d040400c81008814468101b41034091000c40f000840412407101c296070048980d02d60356048802007112002058016111100c1c0c01004e85400039140c0d284001190000d602204152b912032020b4a401034005065403100700c81804e00302c0d881414600040d66981c03c0c2031845144140000380d030020200d03580e0746a00043c5d480201808418 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 305857895 1250 305856645 305856647
    0xa030603020a0f2417060d0c230406050f09040213020d0f1a0d0209060d020909010203060f1c08031003050a141e06010e0702070f150f0801051e03010f020703 69
    0x14518001d52405040010030451445849400c108252480b1703601c0406034595400052800710011340840d4000425010f0240011848841200030300801c8014440b0f000304c01030310303c000803072202500340101d203010b1040c041a144e01a04608070402a200096a61100e10104810107004907140c0e07122440401d0301d0084540c00e4100c4c00e000c500003082484038450f401c2002c480e114190080b244c0c030170000109807005050049110740e1024000b0a08607281c0480d4000c5944420100c5900d00780b0b03507000081100d0b900d40b10039050507586080c2d800782024159083c4800307640001c245c0161100f07001000203103460350704081d00d170059503000b4251070341c001c40d030303c2c2002c0141c003101c06680490090501d00302c0303018a1044225002200b15004002d244d2030941c0080c11041e02800da4406c40c000c00c900850210401080003009001c03c800801004042082c0200081108003102d010010140c00400280e913440b040100045000170203500f0280021001a00400b4940c01c06032005002007006800d00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 305859145 1250 305857895 305857919
    0x201050706050c120709080c04060e0f101a1e09061c0f02070b040605060603060f01110a1a040b0105010201020f04090c020c0306070f230307120603060914010f061a0a030603020a 78
    0x42c0c2e0b007c02119800712408082100751b031501d001c1c249450303a2000026030515858041c950300002c07043c880c00c400f1034540d001300d1503141483e82400154030000800101008140c1071f0500b000c20790030701c41c90815103041c0016405101d50080e6a181c0d10100d86400c40300d1940e9031110040c0b40850408642d0351109141c003c040102c101d505541461070710001401509059007201e1164074020002d030506810b480040d00c0484009200624522070311a008001602c0c002c0003100e4076010011401891800d80341101d0300c088142c12560459005101081101407076005881c1a1a0f43c0200403d820007041c00c124605002c0b054202c2e0325114001c24003200c250040c1c5001c80d00181075a44855071085601e8034170030200800300c0e20720b800004000003888a4444c0b02d0300442c941c0365002c0400ca0654a0f210101601d2040300c041c1c5520000140d84400c401e42446112604195041c050000d81d14000b107108250680c1e520641d6401d60014a10002d20301ca0740c01900551f6000300070414071030300e03444800c0071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 305860395 1250 305859145 305859149
    0x908070e090615061b07030803040609050601080a0809011419051c0905030304060b1801080102121503070510090914100b2b0f050702010b0112090201050706050c120709 74
    0x7203018080c00305444039030110884603544000750949140101000140c2c00084c104683c0403500d00035603001000003801400158002e82c044c80c0007159048080c140142000b5040e400160590703c1a0582d200181d042c50076075050500134204803330a00d040f10180f0100303109408036000d1204204c00c54183c6280c04c42c024100071303506071614032900005c405018040350840400500280e0043c400600002e01c59000442880009042074a41c100b490284400d281000e13009400300c3c1c1d4002c604a17540300d43e0080420344c048804002070807444550360200703844a44e94000c181c0504900104280218080d2480d40c0007440010001c104c0600c01328403221143c941502c0b407241d075020030303600040c20140810a4408020380206511a0310000141036141151400c110304c141507151041221306d00500d10900c2e12a60302900081604101003000402c030001200880c07003414640107007070340941d134004242e5000c1907004100160742d441c0d02400740c005000c4c84c442e0b10245440c0000b0010700c55441030000301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 305861645 1250 305860395 305860411
    0x110609060c0d02120f0d11040b0c0a0302010b09040f0209040503190e030d0807120f0b0402030a020702190f140418050a05240c07020d1b050a0510080c0304030908070e 73
    0x6442c1444020862080c818080b85500000341801b8212040304175a00441c80741c03241a00d241c1c1340581d41c030348030316182d08040b500300c020b40c0198074481c0900d602809030300811740d0100c8000180c1d00d099903802c00e80406170304010b40903003141c01c0010104481001101c002800c412201d0034462030030000103141480a000303a0b40a405a085102401406980001d004841b282c4864070500d0420781868010002c1c03140d01600c0350703100c26200031142c60700c0c4004c5000e00fa942001680ea030f000c900500c5040001d800c9a0351014403401d404101802c215201d9000f82e80f601500f1504a003001b1000a0140003a400d8100141c05959890800c1100002d552070490b4401d40030b44035494000d51b441c00d034039910a80f59912020100b000075058500a4008140061008244030080f500c5519078810200306146011400e0302c802000340b14504e400302c00e50700201030450381c007065501180c00c0182106805489044504804408601014002c0031203a010740401001c44040fa0740d604c4007101c0f00201550505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 305862895 1250 305861645 305861653
    0x51321030e0909150c0d09120e01020714010c0812010609060f02030306031b0103020c011407030605040504050a020103020c0a0b090a060606080f061e0405090f0f0316110609060c0d02 80
    0x4a081c02d00d03030340d002d12074880040902000841e08410242482d8001c00d02d03a0120020801d042500d1018420560006c1c003c10b5074066842070041e0191134281594181410740d44003081c1006220f07811403000c0e0f204d120a282c41e030000307450791a04452600440c2c8054601c4140680046070b8541d2065041c012160a641e40c01d40e00400b45400341e84910080d40c074140c0507041f501100200c4100b0340c01000c26004185001454002c80d102d5031400c4540700c00380b450820107490f091141040d8540a0f41024040844080180341032a03507800759143c0503218004d0601d40c001c20710101c0f80c2c805000f02c03007000d6008801c150381d03807900b4503040b91912564401210414035082012030414441c140da140b05401c0c088501c8503e45031304c020070550300c11280e04200000720f0b02c072440d500c1e0b86031800307218010140080104900c1c04031030f55281c2020003040107910300b0751040c00b0007c51840c00224090880f07402225403801f041402c00072840e43e119092101c0e410660000b00d4000e110400039a8030718440c00c035802c2c1c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 305864145 1250 305862895 305862917
    0xe061908060a12081b010c09050102060c0c21040312030f050a14182404050607030c0807050706060e04031211040614090d020312120a06050d0305132103 67
    0x122102c0d0030381c05041c200301202c20704540058034500040940c150310301e2aa40c0c040c0111504142580d20781c1038401c00050b450002080f195030100504d64110501603109820042060709903991104217880300001064420308007903442d40e14808841c0615040404107249408404000c4d0180032144c6408100b0391822001424415151060f5140c0310b980c1803103900280c507030308900a08005c44604511060148482d8003c900c1c04080348a42e0001401c64044102c0c83e0504102c2d080c0580140240285410480204541070344146020352048160908a441e02c103141450030040141d608480c030750307001c01411711003030542207000c40030102c150000900a2440f080588d00c49401980b09000104d500788140c3c0841c0403144028224a403030241c0540460b032010b4000a00c2d2000c1c1100c20100c0950010700262189403800c04540d06c2141c060060142c00d1604001c1004120b000c8400703070800001140581c40c1402055800f4014113002c00080b90102407507030340c0240c0100180381240030a1568007130b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 305865395 1250 305864145 305864149
    0x2b0803100b070b15040f020307230301061e171312030e07060e030a05060f0403020706031104030b070e040c0e01030e0712020603040503070f0b180c130b010e06190806 73
    0x440b01d00d20340c040240800c60720350504030001c010501c028a5401511030420022043c05072014610038142070344c440d458440066120000404400e20a14000c04100014089290004041d4442004070030038803030340c484a484110303070009d14a4030101c1399400342828000040c64441e40345001e9402524243c604284000c4141c04607804848001030b10b8006080400500d401a0708a501014019003543d0345c089480d600e1504214080b6410b03001540c02000b03100c1416410000302e009441c043c1010081c02c0c00e1a8004041070140344002030043c0d092200041000344104521030bd400b00203802400b51144444024260401c00c1c0f80c22400a8035060300b010007075800107501d500312a240150714803003100355001d0000f40d0303100404c05c0c0c03007a2004001040c0014000314203440c01c24001c1b0031481050514407456441904c03100c811181c1c69001a00391740940d03490350945d03c0180750861000481d5101c030710058503404003814a07903911510201d09904102004040c0c2502000d01c1d0b0340d4500a5510141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 305866645 1250 305865395 305865397
    0x105100201150512010b03192a09020f04030b07082d180c1e10030c020303060d020f0a08031801050c0d030c02010204051f0e04050c092b0803100b 64
    0x3410311280d03082c5201c104582e040441c500780d00d40c1e816800102d14000c514000c030b4075126401000c10350a903250001c1800340080c1c1c4000d9031103440b010320845590180c00e0b0b0b41003407100450140c03464290b030010760908021503480840740216031218001c0d4803490b000202a0402c1c0048034060380108a009601d101c034107580d41d84001c1d0315400c105106907030300e58100a0300e1104002c5032210306845100c9181e400c1c1e5079040c0750341184040203405003216210613011f0043c10310441142000341800c0500480c003c54010007600d50028080d42c1c0c4071791040d51400003500d4412004006a0019401e64002c40c117040040000c14002003501c1a03508071a0b1104011606c5124106580b02550003100d44801e0291090300008040803241c0300140c209511800020b030598505801c1401510010300d08414045e00008170003c00042140d040103d8540803d040a040c464601500d01c00c12503900c00542d00c031031008055034481419000e035a1840c0c05403a00d0270a030f600944c0d9105002620806c00240206120 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 305867895 1250 305866645 305866661
    0x50d08150a0b030c040812070311060c0d0b0f090a0c0e0a0803090d060b0901090903022a04021606020c010e0f0604080406031e090302070f050d0209010302012d03050105100201 77
    0x103450061680d00d440302ca20001e80010b44102c3e909a401c00000900d2a02005000c08070843c00d803120360f071880c040c9005003844500c4001286160041c20402440b0342003003080e5151040036010100300c0903a04800150001c111440071603001e44404280280c507400c550004444240030b07152071092210740010040d0050103441624540c4c2d00c00c000c07014060038940b12000c61103105480100d92507140c8400100e641070240c00c102402c0e0380d2003100d00c092582c10007610000d42c46040e80d048440200180e40c000115243d5005402207800045440450950103c0018050f80080045440d00c0115003424043d2005100b20a40c52141503040e6105000c045040741c0929032180982d880c180c6064001e601910074403241501030034495522981c1d50a0500811138414440c0d8042d1a60b5410400700401003440f80d00058092511405134000607120b404415042d42c2d02401c206c8042c0307000c4081c00c80d0741d45410300f5103102107040b0400d20000c02d0b0107401c0141030340d4080310060004082600121b0072101700d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 305869145 1250 305867895 305867899
    0x90506030a021009120b060103051503060106030b06070b04080c0f12180f030307030f080903072312040b0403150b2809020c0601140a0303090311010e090103050d0815 73
    0x1858070400503e4058a12008043d80c3e0800312280c9580300b41892007510712880c240c48450600d03003008203a6906100340c9500c400a003031080208032020000c00d50b00c40c0140640b0080c103a550240c0c401694424040c0c0b00c90560000003000c0500e410314000b070642c1c004012030003044c4146449003140d6440480c810080020480001e424980d000443c1109000741002680d0441180c0026031442c3d01c0500050070500d000352a811103508500d40020200d40d0028020304068200788501400150440604248580c0a10204802e092231511103824842d03140c03d080c0040070000b034006164400312000c0c10032a13002d41400c0c00000c1d81c02140c00103075041075030040c2d4011a2044040c0c80948044c54001c02902d1a00d09000c4903a16181e0300030482e8440c0302008041d03070207000100601c02c0c9819428604400503211003a81518658014211420500009041800b01502020700303900c121891059000001d101205959403401c00ca03455440c0c1d21001400100d1044c00188100c48065110b5254100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 305870395 1250 305869145 305869153
    0x61707092f0306060712022b020c060717190206060402030708060910030b0703020403020a17070e1305030a0906030c030b0f04020f0705010204080d0f0914041d0601080106090609050603 81
    0x20780409101c541c001000d00368800d00901400010aa2407902d600c49040d082d00146000c0500c101e0074541801c90703c5511074030956540ca124001580032491086a40042c0c4080d901d440451414842000003150300407020000843c0a500104061034001001e0829070280c4290b80c4480080c00103034401213508002158030140850042c0c1050a0360303a610481d10100c201c00f107500e03071b0340d0141050810380d0001d000903000f04041c4107500c1d10030448401400d090103498199451040029200c140d10f100780c078800070703100000a256019400c1c01c0d009060380481070700d0762900b0141000e801c14156000c1d0100080c90840c42d030381d080340280308405c4140b000900c501808d41c507000c10040a54460000f8560582081c003528000400900142018190300000342200d081c407800c7c020a5000d8140744102004981d24042042c001c4003001200000c0f02a580811a0b041901c0d441d01055810f0543c0401c5100c1ca00001440542c194002c3d81502d44481c1c0600803a40c1c2c403428541602d600351900f544c980c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 305871645 1250 305870395 305870471
    0xc07140303100312180b0c07270506030a0c15030b031b040b180412020f0d1d06040509042004060305030418090b0108011e06080a140106170709 63
    0x82150004e071103800c403a207041500b40800052002800072150301080c2405404180d8243c0c0790410701c0880060300e07054045003290300c50007104d4424040141e40084d803407651100401d019480c01d1140402e51a00701c41950807140d40d0341201803030044180c0903540041d14080e01003002c0e01d40400c542204003494000907070024121010032004041130034029904c6803444684961030340b43c085030984148c0c0603030004010442c960a010342001c00300000355009130070007101610150780100d00d88003110b8551146c020494140d60101e8100e20403500010b50103200c840800c01040012440242c429000c030541a04202c0030310144410f03140396000040c016001800103010401006181c3c0110200400d000700d0300382c60a480b03500b8982d03000c0e00001006e9464042c0d6243c0314401d480301890400a00404114181c0340803003003605c520302c6980c010146c0c4e4019216000456007500b0840c043d000c96088441c0121143c045a40e40721520f109001c00a400c12a94400700b64400c0c00050240500090324034102c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 305872895 1250 305871645 305871653
    0x10906030308190e0115080c0d0f1b030f0b090721140a1b0e071b03110f0d0e120d0504050d03020f0604030914030c150702180c071403031003 62
    0x100700d446070340c3c8525603901c4241c8101107090190002c1e06a08031110076496084c482024241100c03038020318001d06810b1404000a0781407802c141d82c1e240c01c500b055066400190320804164036952001e81003114801c140f03004d0220706d614035800b80c41c0240407580307a5607503002c100e030300031580da101160403a646a0302000420014110b81c100c002c0300340107846401c0d605a48941d0701c0c3ca140d1f04c00c0b00010020761001d0007841c042d00482c80c0c01c003845040840854103141e107030340d82c200e0ba1b0510041c20810300f01403800b9080303401c1000001e020050010355098030030f03d010051090b421040c1e1640b2905240c02442181440421180400d000c41d035100ca00d400d0a0200f0310a0192040808a085218401003043d40d02820301c50309010790300c650340301d84040d46005003940c0c041d03000b89040d85c0302e90040f204100c8640d0711400320310f000d0f4441c100281d03100d80c910700004580102c00030003849405000400c01082c0340b00d0700000c0500c94451604080e42051045282e070340c80c042103034030b55042c07010b2160500c085 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 305874145 1250 305872895 305872921
    0x203090d02011403010e100f12031b23011d0d0f12020a030b130b0102070e07030e121908070e0105160501021207020106080f03030612010e0321010906030308 69
    0xc0740181410000f1145550802c2e00c640d00c2680140d0701a44c554040c07080045000c1e110b40002c00b4030b454005ca2042c28a40c015407109034640c8003d06100c1e0082821030082c81101d802c0031425080001d45105c48102e40386400700c0d65241a41050300d51a00c3e030703c94101104440400e94000714100144a04c03d8000380550340c039401c4a11b214180003000c04170301c10710819800240040081c2e59400300e02c80d00b0785400e210f030442c1c1900c0292101c9080009a0010b0b0340d000034200111101442c81d40d805840341007041c0d0081c0004141100f8034050414071006100780c45004014900300402c2d041816002d441c0110f035160703829510700e800940c5225054065610510142400540318800118055681c0d9907207422684a0b0310510803688040e410170066540a103c2c4000409111001e0103206c1c007214140307a100e110003000d20f03104186044454803402e1095114038403950074401103950710b44072291201441c0062416682c0603240c03443c0080303098180f5020f00022654075469070122911050785075900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 305875395 1250 305874145 305874169
    0x20d0612150c210f021209010e06070c02013216021c08040902071104020a030b0a050103060b2a060705030f1302010c0f0f0209100e09010e0d0f0c38010501020309 71
    0xc51340d003c0c08043c4198144400f4140a042107400015072079884142c0c0d103050003801005042800701d20701c0c4000160342c0205036007011442c84a0100c019420341005580e80000018031031113400d00c086042c40180000d01d13007250120b03000f140e10204050112112042a01141d0782c01024158103000c100a0650950003401c00c46100e49400207001c4e0100011808a807c001942d0b00080d841e02d41d41c0f205070420107804006004213107400d00145003092144ad0035846424102a030b140c00d40700483d44001c0e0340110010008885205680840c2401c0030010000e81090720741030303032a01c03c074404121000240342a200c1e032241d06840d002450030068460342c417101c07032841c42501c40b914940c0140300180d071217281c81403146007081d03542c0c2076140c20142420401c0d0001400e03d45207a06d4550389440c1b50100040c5200d501c3c009140a2100509a010882d41c2e05601c3e003004001840d086001502c490341d25004990340d460308141401102c00b41901d0220b0900c00703100e4036000d40c1003088050b405091204800107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 305876645 1250 305875395 305875421
    0x809060c030424030c020f0606190b041e150807080c070b0a020301061206080714180c0d0f020307171e040f05071706060103020d0612150c21 62
    0x41083c2c2c0d03e090156440745010395807103a00c44540c2c42112001e03018892003a01c01c007584001d1070b200300c03d035030300903542c6101600c401d11802603004600c0301c0241c131071006c0010b031000c914010788aa0383c3d044050130200d44046050030348a9030060204406400401041c00340c011a915441143c581c1d903010b58501c100a4140e010b400010890384c00482d00f46000c5901030505000010f943c0d6141440c0248110b149100380c01c03819091042c201b000040000e050310584400102a0040c075035a113000400b414a284501c64000c0b414030100010601201d01030119038144130b41c28080c13403c1d4420341c1d80c1244401c6401d035001c5001c01141c2c10001e0901075810740e000401154070a40c02003401344500d0001c1c4200e808464082c0d002e001d040c2000000e01c444002801b1420300011406030143e42a81c40c1c0d10f005140a04240d40400c3d03c4600c1802c0d504480010100f101e106200e84916052041c144911017060b0601c1505203984903c3c0140709c0c050308200d001e8000c404c90f0300050482da1040180020310043c0b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 305877895 1250 305876645 305876647
    0x1903140d020c0d0905030c0f0d0b18101e091e02040e01060803250c030305070201020c1e0102010c020309220b0612090d0302090906121c020d0315030809060c03 70
    0x21858450402181c64104521307251410711a2424041520340314441d09018028000c1351030008190b155080a0180a036011102445a586084581501b000480400c10451145e8085440c42200e1075000404205d4010021124982c1028402c1c083e1403038198010300c20714410408118070883c42d8a400d100510040c004a56000c91010090075905160058641900001b40a81c0403016010709900c1100115100483c1410301c1d40f1040d5007a60244000307800d100e400100d07501107a00c00d00080c618500000c00c41d030b00b5103400c0c160401003541241c034854003540ca0006d80b540c0742c0d0700002c10344108400081c4950030181e0031000010616054101101d115a102e19501046e41e0301c10003d4480080760a01d160a40e15060203250b1a1821428482c018113104100269182d2664501541e0280b0103507000d502c0c60303030303105107291800c0d0707140da80180000301e01c2110700e030159804108141100c880c0d070703824449414144c00e81e60102401c0d12008000d03100800005141d424001e0240582007010710a407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 305879145 1250 305877895 305877907
    0x50301051012110408190206040e041401181a0f0601200601060201051b03060907050c031306050903010b180f1906080307060e0a02091504020906070501090201021903140d02 76
    0x141e80b0043d007441c45003e00030a0502802008020600d11a1800900c4001d01c00e6503801050080c441d078008c900c03000744041c000605000c440801441206041c4c802040060b807407080000c0501003102e400c42e034400c2c01c4600421450a103170340450007680b8020345030350151254030054500d03522103103200c042e4502c25100128801c40500c2518000c1843d900082154507201d0010402e41d0080b400c04903c840c0e00b82309100381500c3e0000d0310390b880102c509105a940c40012982465405031201050343c98480c0100405c1c0d841e80400a001c40260541c024450581c061040084100c4030340b50303d9440900030400204210340720651260003580304900c0600701d08030b0003a00010b882c11904040350301d0b8070009204080184610071841d118002030007402d0321104035800600b844002800100c00501600340a80d00c1c0d07a141e42c11114001c0c40202803668409042c030b0024080c0c952840c099000d4014030f03014a254030402d91890380441c1d41583e40034901c004880c0030b0103c9410040c40c10707800c01c0e400c0c885 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 305880395 1250 305879145 305879177
    0xf05090610360303020705060a120507090918170a080a0c0e0901080a0506150d02040b06040503010f230906040f050705120102071202010c21091e030201060608070503010510 76
    0x4001441d07003440c90b81580035400d5050103071805c121980700364054841040b2a4103101d07404000404011480c1d040840e007521004006c440c06150354022070f4000b03107070000f4150b4045800d07a082d60180d20074501902c0107160b1801074002e60052040d08030214003000001044100c050f4840c5107000c0c05e605020841340600004203000c000300343c10596003030f0307c170420700c50500c801000700c541e20075031441c0c106400e5042c01011840080028000034000c6455000c2c01407035507516410b580281c00050000c02581000f40c800f24054040c480401c6124554152941d155800d0740c005103100d807014030300034a0300303450300e68520b2002e020300384003038503140508540031425659030076090b225250343c40009a00d42c811404c0c030544001041407504250780c50400614103003034201e0018801410440f102c4480720359540c070410041e00c084180145400c0c64030030300e1041ea030340e407943d10b003800b5000c3c1d4000c10010740c681c441076a190000343e4a140200340240700411861a040724006011002490040360341206620b03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 305881645 1250 305880395 305880467
    0x310030b1311030102040f030b071110020406090503060903030106120603050714041505131a0603041212050606090909101d0d050f0d110c0307030503010f05090610 72
    0x907420344240201003049052100d0342d450300c402044214021481d240c544000c5410849140c4001003901007100c0006a4a900402c0010b43e030b542c0030403c1d9941c41c202202010002d500c18020791001c1801c1c22400f14071030a0004960b44580742c600d00862450b4201082541c44940700d1071340014980e111100480020000d1160b040200207041c5040400c0300310004010a4401c05e20381c0039490f01c4d054a041101d6554003241310203040d0701810000d1584004035119001c103550816030b03500401d002041c0001c102c5441c40751010f202072543d40c3c168400f8107102000a98806a81c0b444e840321702440600340a00c0c0844500b03400004e0041150303558041d646500d01070702c020020b124080100c82441c032500c0707107027070000a12410b2a441c000c0d142032024210b01b10140203c226884030207589a00504602c91810101c035890070410003260713103036101450014125802402503800101600c82d0014250500c514801d0203660001c2020360038507403e1a048840e903000e56200c0002c00340740d001c003c0e6a03d0480c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 305882895 1250 305881645 305881651
    0x150809031b1e0a0614040203060a0f2901030e1b042d090c120b0a02070201140301230406050d030806010e18060406150504140612180d051801050310030b 67
    0x38083d02c48401a802e082c0100c072404040207002050f60070801005075001f082c0e1680c0894151030000318480e24805580c000c0c10000384c104030035120700d4002c3ea850301d40c0c003a4107071040400340da051064107403494036280c40d81801d420101e5428104c508008071490030b504080401c1044900004061400c11602c0300403412040214070029941c001c448144003076410913001a119042c1c001080c2c00304c95545d007400180081c2810752960780492006c0c04c5a1081c6081001411102c1d801510b81d61541101c5d0b143d2031042c1020210640342d6222400d060034940155403c4031002000d50b00580102d407029103444000820044c100207070b500c51200c95549003c0d04040d0008000c400c0e4201c0c0c58920188400c9403401e0b008074481854600c1c80c950701903840f0013240d094518030f401c0c681c80c05040402041080c0510700540a86020b10170400ca03103141c0f20404142e0b82d5001a086909603100d07607005840600c514031400101d600040b0b045a2254040c80042d81c11050395051052166540c1d11040b00c40d140507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 305884145 1250 305882895 305882953
    0x1201c06060f14040803091302040806040305030f0108281406010920040302060322080d14130b011a0c25090b1f0e04060f150809031b 59
    0x48412403440d807180b4030100e01d440e520b055514003400d042c84542e4902681c941580705585c4840d03806c09213888c0d601520003c01120b0204c440b0780c2004c1c1b41c0642250011104812035a14000c00011030303000001d12214451034203280041d0840380a48440086c03040d10005440365a07200b080c22410709000c1000600908105000064941200d001c0264a440180000d1403150b002d10007400980d40b61011260040300c040c01f2404042810f95282020110010020340103103404501c10000c01155044017009822000d0180075a564500030761900c5600070340041c100030044e01c0148064185003440030000d0840c50b51003070400760b0340d140c15485c26440300c242c21000d040d4a4580c14100885181440c041c05d42000d01b4400101c03a80c020805d00c01c101c4015010248621500340b081c0c07406503000000345030000d0700034803c0744c6d02d8400d01c3c4810500d61048604881010390412580780c0f29440c9540503c1010004d18034101e184c55a06001e00c01081081c42580a2209104440c000300742c4403d1581e980 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 305885395 1250 305884145 305884157
    0x6030601170c04060f05030c0922050a05010f32010207080a0503040e0708040305090d020a0902070b010302031905071203050405060a021006090e0a260f030402040c0201201c0606 78
    0x2804c00c000c1c10b040d2a5003888040c0a014008d00c0b090386500c3c002e880c6500016038200c13486041240c1100103042c41c0e040c00b4090145030130300344445400b15400c00c80c141d8252125007110300d60744818422010a5483c3d0300f00f84a4510401d40e9a4644108001d480108052040360981c1d511244107030b042000401041303c0c0c40c0e00000d010050b008800300280d0303000c1e0071400c0050403482e041d00c0150030b520400c039081e48a02140300c541d0003190340783d9850601030080302d841107403034001c140b9180301c3c8000f081c00240d11070320a0f842c040303a80c034145541c4404001e07030180c064114180703464056100105001e20031403d2150510000c9103c1d100d40c8080c0191030320f19402000d05840039040c0c00704450054005000441c240300103440008000100103d52715444801c0c2034411b801c1200e182030701c82c084581e082341101d0000e02c200441d104580510b00882c002c4608201744088001305a08842000b145111017905c1458840b2020400340d000c1d0003201200aa1070054080311240300d012240c0d0b54000d0000b10321 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 305886645 1250 305885395 305885399
    0x7020906010c1b06051c0c021203040c170a0c21020607053a08040201050a050307022503030e1c2402030a0603050c0a062708030d050105010809031201030206030601170c04 75
    0x51402188411b40360300c25000c1281d13840c04074000791030b20711210b001881100d000021030100110303085000001e00701081c850080824840c2c1d45038845001004c25039105160000101c0c580c1988000580700b0080b001116114811941c280420342d006078400b600e141c040d40c5180c10a0226111000040018400140340303c1d40e60718442c980050f4032100c100e802c10000204100c0140d8001040300c1000b00e081c2099600c0382d481c003031300300e18081805404043c42e1000110040342c094034481941e003a2407280e20741d02c0703504205405010314040c0400c1c2400c2c00c034070a400d10301c01007070a010811001502c0803140c080c83c00140c12a910683e070040d1650306000b17690392420000e1000a100c86010400219071070300d405450038500408040e80c443c01c00c4036014420903101c42109108401c2001400d01c0c0084c1c03030b103403100305600d00001e06003440f070140030030b21000004440200100486034040006409030041d42d0071602880f1098200500711390501000050390380d01ca00c40d10640c0b81c4603031460688155514 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 305887895 1250 305886645 305886667
    0x801140a090c030912050a080c07020420031801050402060a03020304050304030c03080d0b041407030b0307030b010308090a1d07030b040b09180f0d090e04020a0e0c0c0106050607020906010c1b0605 86
    0x200d0a14001406c00906000c60b44900b5409001550440c070b14010f800e450b29a40d00000d00186404d02088003c0703078007042001c485080e0300e00507611965031480e03030b51034800e1204501800e03200101c40095106504211440065000c0c1d4042d54200d40150126801e11342c50f5503d01100b075141d9002a140720101241419082502c1d000d0520480400d840c240402c55140d0000301030143d02601701c1c824103480c0c1e411000c0c035450401c0760000858024040c0d00040d652420f205003950712842400d4040c081700039000c914a900483d440046015000c40040207030390b4aa400c07001480c81030a6a40d020703440b011910304603507540140038000d004002111109800c24a400c82c50000e5172111380d2a60b801c0000c2c00451039800018440c201c0d2268940c01c82c49565520029205001d40d4010b49030020258050100e0f4480d281c01a00300b8219100c02003002c2c03074881e02005180e0085040095000000c031001594551080300d0004030a403240c1032041400384449038450352041242c104000089020824507064 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 305889145 1250 305887895 305887913
    0x2f0904030225080d030c4e05070806030607050f0706020c030a0207060908070308030a0e011d0f1606030209040e010c0509040f1404080a02072303100506010801140a090c0309 76
    0x103054102003000800460010704401e83c07000c5003a403500400d040c041803140c03420141d5030354030302c50300000074440300400071900086587d0912550031620303050019203000d000d0041c1c02d00924001300103082640d41c00e10204c0b15070340114081c4e04500014810700340050300038000b40c040703034822101031615403e0100000f85800381c41d0f88a201044403000d000c100e840d102042c01e406a81d00100780e1740c1e595480f10103407000b502c09841907000541c0703048900310b072001003901826203112020f41605e900380b40e00c60220399141100710b08140024418101040701030300981c001c0601010180c0041110500030b48840c4c01c4400ba09000b0004c02d80c00121403042d80741a209142c010303000d5003020003610143d504440b01042004100810b400c900040110308136008001e284000c01c20b01000e000d0a440d40800e081074180c18520041c0203104170001c00103140d25034010305d0311907001a55101035680c42c000e0b03071415866440301d2030354008899100105601c1528042c5541e011b030680c40c0802d0300075080c40c044038a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 305890395 1250 305889145 305889163
    0x204060305060a0b0a0c0303091407150e0306070804020d14010f0b0d0807120c0f03030b1e0d15020d050f01140901380a0c2f090403022508 61
    0x1c078050101c4140020340d42c02050b05c480e01032600d003031918100e480c86c0a40048c810b02101a0004c181d1100940a0300400902181528000700e001c080c060303e00c1d0780984140448004440e850303044000018105031090000360303400790004003142345c600361580b1a003941581c0119482d40310303519504000900c003802e008a42e0008006d6810415081943e202c0c000345000b0004024684095401c20800c00340c410300440102c0c0d0380101400c03042120381d1070003a0003031064000003030040c103910300081410801c12184005841010344404031001c035076542c041c2e0800d440c08034a808a40c2c00c2c850046a5071a80c401c0500c207013401034072601c4039414074482807030122141028911400c2d240c0c0040c021210005100700f85600c05074681d245824028003000801c4a0a00150350740407404541c80c00e0241d400100d032004580030b0141901d42d981501d0140404110f1100d1250864000c1c400703041c40781c2001d00a25511a0181c03060f02c02051b850525054001c8079803a600d110746162820500c4814424005084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 305891645 1250 305890395 305890399
    0x40218010809030703091806080708030c011508031e2106030f0304150c0602070611070b0108030405100516050703080a110303060a061b051f0510081c090e0703020406030506 76
    0x104000a554004007401418090390094a0030f0900010201c1150380088c03000c4c1c440342040c0d800050301d42c5a6250b80f900035032071004041d0300f0030510200081511481c0000e0729420405540341000540580c240c1c5208910040080c00c01000202c041604d18680441d0000c02e80741c4c00f04031400c1c004201072512020a5000c40030350000c00c020002c584034a03001500d2505507040c8405144503c0c00c04000a005840300949036500342203000801c05200300081c82d032244030746004c0ca9a42d8940d224213640c3d01aa00402e90032854022222440c0d50241c4068403607042200106213140007a40d969604000031540b085039187c1005c940022815040441d0507102880100250b0562030b10b0000541241580c0c444c5400703001406803a0303500b140355100151042c1d42c1203011250344821111100200114078101e1240c264a0301c00401d1b40c0c5130780201d080c002c4482c4500100420419400e41d00140000d0001007418424140e0380000c4031004250418400d004a44005840d1442c0140240940e0f5004010034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 305892895 1250 305891645 305891647
    0x614090705030103170f0a0806010f0c0c050d0206090a080c0312070c030305071a0106090906050105070f080c0a050d030902010801090c200304170703061407080a0c050904021801080903 81
    0x80011540401581e0440360403c01000098044d68408000e5220b03280028080d811b0001d042000d00ba0000d04942c01280c0c00c0c1e80e0350b400103600f514111444220240001d0800003c0c4004000928200500d45c403181d000401c80307840c181c01078000940c580f41c594424005038108220030441c5203414440807004240d16401186010596030b038400500300a40030007401d1010100d07201060040c101d4114201140440580c0010b517101c040107006919507124040c0c80070300f08080460254843e138103a40b0300c140e01003441d0084c0312865983c0354950300701c00304e070100034032031001300c04c1c0841c0c410030046003040c9503905c0004810506000060243c00141c00c1115250b05103004640d4460b400440d41c00b031440701185d821251a41e2114a40c21132040764844e040c012035a8015803482440400d00e481181d203d00c0c41005250594100848840402c40f0700c030021900e5500084e003048072036044502440380501c0e240d45002c0c81c038000501243c01124400aa1415140c010030065170060082c3e034000141c88011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 305894145 1250 305892895 305892901
    0xf0e070815092502010615170105090705071502090f090606070308060105091215090c06031602160605031e0603030a111203040f05070b190f020c04020c01061409 71
    0x31a808030000d201805480110002020410a800d40d500031001d1014211043c000d03070700c8000d000c1c0c0700900030381221a500708014076038140501014048a888510300d20460b070710b403100b0030900d200c00401d400240501044244001604411a0783c01000414001629041194240050b1078110051035000384d041d90288501580c076003007a214115858a081c2116a8030030004a400e0b0040d44103480d00080c0310480503c89920105088811041002c01002681d44050320540da80d10340c60a10f980110003000401d136144450301c80e03030740054120f004a0300700070007a0b00084004082c03507004800140020003840940e00c2454141d000a0840ca02503442d85c0c20154002608c0744200140300c400d1100740d40c19005207001c01c0c089621214141101180c8a2a01d0300741151251030f103040071141805100b40c08640304040100366105518400d042001e0394807440700c151a00a8001c12450031340c891640c00c001c00740d42d079000610140541200100d162454040e170028003070001c4800c9407080340041c1c20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 305895395 1250 305894145 305894161
    0x30906162a0b192004090f090c0603140c0301050a0e100b0d0b030c010c02061c09140102070201110105040309090c050c010516090f030209040b0c1e071208040c03110109050303040f0e0708 82
    0x30369090341c03229140000e2218400744051f00400e603a10000f0180c0c65003101c0060782c2c40d0950320545444074030301d80f01181e5070b485041d0020640f1013401903540c000302100e400d00442c403070070703192aa000640f03250225590303455150784240e6401c0700216613a00c50f1144602100c6003001d01030300140b0b400030308284c0108815540018158042c40f18062030901e061312591030300201c1a0820280b180e0082514040c48407404a4030340070b9482079a0590200e0f400c5c801000b44400e052286501c240d8241d03440707034201030130301009070003070006000c0c1081000018001541c0c40c00086c82840d0043e0f4040003140404005441b0162042d02982d00c824a0300e05050010009a2a011380e9a81c0c0a80d0003003800c0c0c0030381e44070071000074180254011000c100343c0a1340c081c00b801d42000014500380d1b020340c4254900300c54500d002c40e0010f40c122401003812031415400c0001500d18100741c0c1071004141010403406072500042842d58000f54800702c070080c0000c0040010f020000c010765041242854180107600e00454 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 305896645 1250 305895395 305895397
    0x303071703091608010605040b0a030c050409111f02070605040b070611042102040516210b10090e090307050d08071b08030906162a0b1920 61
    0x82403640e5035001000981c000c1e010b2100c02d000c400f043d00402051034403221294000d041e540243c0e0b0050b881c00c00c18001034540300381c5071021241e1040070007000c0c0b0f0500042c400540000c1c002154141091a04184559205540d205101c01440e00e00190860603a034000c2c41c00b8441c0c1c1c00041840401c001c02d0054007140c4040790300464205001244910600785000c10394440c55001c004070000c445090300640b00c0f46015800f4050085070f00b440a61140b07a50b164007801c030a07003503a01080c2c3c0d4080f04500c043d03c0403075803800713800e02c03400001d518007074100803c64840c01012000001212400180010003085c04196040a94200150704003d0269506540d640302c0d00740220902c500000090801f0f40f00e00c1c2559000c0964041a20150741a4074213241560801d0360240118050030340019206085481c113180085c5490762001c0d28100400c003a071841c0c000c041d8000115401d4440740001042058000074080d0308103c1701a03071401140003014046601130710b0020007580803404e5032030422441b80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 305897895 1250 305896645 305896673
    0x20a0b040311101b02010c2109150801050d02010806030106030602181201060b040b0f16060204150807050409020901020a210f0503190c0c060c030209040b01081e06120613020f030307 80
    0x2091400e00c07d280750400443c2e410b81d003415940c02c0c43c82103540122103907010b503480c0f0032100701c52108a070340700c2d25071400e80b041ca000340981c44d0404112407600002d50301c104006a04864045c0001030302c0394980c0c8a03102660305c8803841c64103007480c180365600b560a21030000c406600d2248000c00c9120f0903c00616000d12852192850000d400b00748102d4003603100007201c070818604500e108510780280b0709078019404c075110b0758203000c5901310030b1300416000350b880f24403442c416074881b0303d1f043c10058040029000038502904501c1401c0090b00050104100d0b2100d02c103503050b2010003800c01c0200144104981002001000410300a102c0a0148112068890007a52030003164490000b8402c5814854140010b07052506215520400030740582c002d101d0b070001a101444000c2210005503105402511150113200110b406000608140c0c0c410941120009000e061403420f0780120b42d07d48042a00c503860b4031030390303410800c08602d1300010b400240711096001d14144400d41d1108941e100c042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 305899145 1250 305897895 305897897
    0xe01031d0109081b010b150c15100315020c070302040e0708030d020d05010f060f0e010c02032a01090503030909070302120117190b18120414131b0c020a0b040311101b0201 75
    0x100b01d080c1380d42000d1209c1d6041940482c02e40d1554035102d50f8150000d2810305c410344a08550903030543c031950b1180200c6060b041e10310010301070940743d40d01b808001c0c0005040d024243c0208040491060300510040c01c4802c40400090388401c104034640d0111074041c0d1207081084c0c0d0b039540030404a0b4106005060401050400d80c00000a40f00161003401440d04001d601d80078103011981390320000f42d18a00b030361318155111011045194010765070060300c1d00070164158000e01000c400c03450090340495221340c880c0b80160402c960001d0f6880c05e07240c2070304000c454064082229a80107400c01003441c1c03a00b03aaa442d41480e54407602c5003100048050845819107824000700d5000fa2000c204400142041c510368580e41d680da070b284040801401c00e0341c5c40c8500200e0380c010800101600401c07045c80145c010314000c044000d1415110080920022a0003000c481c1002452a960710040c000440c05141140b2100410108002803060444413180038000b81c05d40d0244600c0c440000000503e0382 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 305900395 1250 305899145 305899147
    0x30506010302252a050f0a0302240d140915011a0705030c0604050f0c1e06070c150302070605063a0f0b06010f030501210512070c0608090d0e01031d0109081b010b15 72
    0x2b5401c03100386c103208105035030300d52a00308041950400d07074410003188100b400d50309480401100c0c0c800c0d4041103d0a110700d1001000e540c0c140c8000c921050020140903210754200c03890205071201c62420300d03004590559058000c2080002041400e00440401c3c410860b110a801c01528a0411924000d204614051100819460100f04aa80080000e0440c4841610400502402c004c020f584031701000c4845070b0619000c980103080c0758804004581c02e03103189155045038a0f500004448407802074505264040c0741d4840410020582c000340c40340601c0e070401346440d00c440090031010340040ba1030100f614250040282c034082d400c040c1a10458815458100d05a5051041c83e09091a041c548401000103000040260b1010004215a00394907400003680d100b0809544401c0303404100c2010403065082140550f2280c0d0010075050346543d24441c0320301880c1e0340e450840d01851001c94400200081d00034005a811074102c801610b008000e00c03101c68540082000b102c1010800d01c2c181030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 305901645 1250 305900395 305900449
    0x2010203160318200f03030903030a030e07030c0806040c0e0618070c02041a010e03060f071b081803060a0b0d0f02040e031603030506010302252a050f0a0302 69
    0x1540e80030485042c1c0059415240000391044c52001c1c52032100e626100e100710f100f094440d424040103440a07841c005000e541410002c803001d070046c2c02e04a031100e055008616002c80040c03800f2445e540070700381540082075285000d141101c042400c641101c2901030303841f002c0044c0c1d03076240003a40c40240c0c1d2411803030305180c407960015503213040d55000080d0720034205040c80d81e00c0c18440704200202c074800d90780d0501400c40401816120340b01606c0c20382d0140040320003c0c01003070059116070040c1d103002c0b8480b2100300080d01d5080c02900298690500d070409440ea40750180b07070070030074190071203251002045501c181d840040d140d166201002042c01c0c22080011081d991103501140c010f12822095a0340d8814421202000b1002041c003240800d1800c1c0c0410070ba94401e00c00d0b40c3c4808681007851102d1355245884e044200059182210350040d500c903102c90142c20091071480c030b40700d06c1190602c6641024204803440c0788803900342d0700401d808402080541d0b40e040c44c8107080c1c01300b1348280d81da1070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 305902895 1250 305901645 305901671
    0x2100c02090712060b0c0c03071a07140a1709150f042102060406090603050c070b01030201080414011d0601080a080f030403050909010b180d05121308010608060f07020102031603 78
    0x10000d80e01c042843d80e40407503590344210300407d1103005c16501310b05407007403035881d92320701081c0181c9000100c207410700600598000914110040265007041d00486003060100d59518481424410720403070f08a0b000701c3c1c1a1124142001101481040c460056003400d8044201004a005238483d0495603040c2408034850800100002c07840290080e000c40da6458072079001802c60916403041000003484e010010780c0a104440039902c0e9036074055207820003139186800443c0c090802a005072840f000c91000901026070922500070181d056492040000e51462042c504201059200340302c075070040c1ca107520018080008561243c8c681c3c14502e03480380c44a0500b12018000c850754a900048000c0012400c40e0a56001d40019000102850000c410f250240021450311404c020034a0744890800003c0c02c0c0200040c1102ca4000444142da05584014032030a4441d59401003281c1c0c1c0204042c014405001a01e21f07a000849000a510314140400f00c42c0c900080c503006202003607614101d0803065 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 305904145 1250 305902895 305902901
    0x308160c080304060212090703034a0117062b060243020402090105161a070903110108180d0e10020c0d0f062702100c02090712 56
    0x9401c50801922440c00c0e1905400a50007a4024502410000c00082e4554000188130094a6056403459219848000410004c03403803500b15010100c4500941e001411204010b40301170b1300d000c5585803581c4400d00014050060401c11864031552803410000383e07440e08000c028564111080d1070448040c2507016001320140076200600c4140001b4440911a09520701c422200105c0e004a0041c4040c1e081c2080a407250740d864500020302242c500390141c0341540c003500070ba00060410602d06844405401c1d400081c00310103ca1408910b038212031207500c15100c0950280880c14000c200504580700d480100e0b030706500307882c10417800c0c000040860b00f252614601500d01d84049651090841f9405824104030341e01a6006200b0034404075401440003030820901400a001c280074141551240f40710707500c109106590464a440080c1d907449480344a40c0b82c01c40d031402640031340c0071251040048601c8400b2450702045000035046000d030b82e6074101540c0003140f41c18045210801070013541c0c05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 305905395 1250 305904145 305904167
    0xf030411030a05030c07120201080708070212040305011b030209091303020c090711120a09050d020a0b03070206010326180102011b180801200d1503111804030816 71
    0x1802403201c18020450000042c0005e141d500742074601141d01c40307188544c0300c8020180030340010112008500d8541c007034040c1c15004007192040d1552445039000700c48140d8001d601c2226160340d2581c0d03c0c0d00d00407104281c1040100c891a080d481c28181000142002c90080c12510110b4a650490010940200400050b01c18098004003051800803005004e4061060f076004141c0500d15140d81e41c4440704045031518052511034282260901050201a400c0440c04030b0700704840260114901e14040081c511604095000344402d60552410141d0342c103000c02d4030054480b030a90744071301c20f4140000307503441032143c0e0b846241c646c0f81c41d60040740907100ca5400240001406d80c010244a90320404c3c6074440405c241d442c041c0c6036511a80c241c02c0720500c1030350448c2c510203036038040b407101d10820040c901c2290401000c036410b4140015400c00346901e6208607094445100010018100880000c0500c20000005c410600d0a5100904681401450114200d00d0110903100f020f00400007450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 305906645 1250 305905395 305905399
    0x11040e15090307020904061b030b010f140c060414071a040504022b021801170c0c12030703050105150a0c080d0f020c0a05070509010b04090f020909250201020f0f030411 74
    0xa06007407c03c10001c1c290f503007020505880d55110209161f000c1c0c001d5115030b80d4103940b02040300200d40e4007140c0c801030148164081c12410803214100c900200140d0780502d000307010821070301e81c420f0341080c5840d101340e00a2041c94a10192115200c04185c15101110f00c1550050f82e070340c0d0f100509045103812104030742c400744444c265044241c1030b50b45c05007440c90758003801c00507299000c00054684401031801e625582c0e01410020303001c064000054025001c107001242c1001c0d0700000d03402d44940003258801f0000385d6800c010890762030001790340070400024284842c58003500c004024420240707050090606075000443c0003100c0400e5001141c05c0c1844d402c119118658040c10300d8071120448170079105072013040c0c00407841e4a0700804441c100c8440c00d402e2490306151009400282c800708168222280d801d010351500d44c1c035038244140c4035404800c84600c0941d000d420900008107030940c5c0804580c814820f04c84842c1c0c104086440e0005000da201da120f03a603030320300840c10242c0c00e07030159 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 305907895 1250 305906645 305906659
    0xf0e1603021c0f05010b070c21050d0c02010207060c030219050c040e061b190c030315060c051612030c05031e040f050409030806040504020d0c1211040e1509030702 72
    0xd011071070301d80c012643c1400141080c09541d0366205007040c02c4c055410040e1101ca602c140402c130040400601201c00c0d0705a040402d031500240d22201d081c0002a03402101003100304451008641e414401d14010b0b00c03641c240803400c0c1c3c0d03068030025a41c1405241c41031480c224800150184082000381030641c0354020424442042c84014160b118541500e9034040e10b00c1c10084a2098880305042e03900300c022303a620f0020404140042150503004000040d03040c0b5598802517440d010302d51411001030f2000740c5960a80845503c2d100e49800b07044c03158810004030205080c08148100c09005030115018a04081111603d090441c00c5201d003800f040004007103188511034080c07c0300050000c4030014481000480e5485050200b6034101a000a000408681c0041c225103043d03401a0740150001d850070084d007003190341e0601c00c41d0283d0448441c0101c00e1104204012a0307103144c100021050302c05000c904034a503480c03940c4444000b10314441e48418000620345d440300b0401c0d0b82e4101c0d0020208 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 305909145 1250 305907895 305907937
    0x801020c0102040501020106051e01050726040806060108090c0d020103061707060908031c0e0a0c0612060f0819030203160303020d0509010203040b010902030c04030510020d05010f0e160302 83
    0x400e000f0350180c401d640c095420f000c00003401307180c002d0041342d003443c0220024804112001c01181c181e0b00080d000c40b440c9014500740625003d02c04d001d46466515803807010750781c60500d5103151070079000510306410000c40d01c0810001441c007183c02a1720751419100f0000300f410320704c016005020786400020620040030404600341d03170300282c28821035050f91103803010261103411141d00c07449616800781d1002c2c13410001000008840d40014813604268041d1601216035541d110001c08440e401200022440c6000d40110401841010010110b1302180504640342c241c2050300d0790400000b80d08442c495800d810300b03140c001d0013141c0618420f03803200c4c02c5071001860060002d40044000c03d010138a000c001402c500e40c14401c0340d000b0b6403c108800c5803a0718001803c000395000070030384e40c03200c141444000001641080744d0801108000c0c009a02c915a200607042200c0d0140e01980140700307624400c0000300e1189070116080018820300181018102030309902920858108081c140b03070f05000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 305910395 1250 305909145 305909167
    0x303082706060f03061b091f02070e092a060712020d0909060e16030b0301020d090b070305061807031805010e15010501090b0d2d06080604080409090c080102 69
    0x1c040d1103484111400000c1403070400925903a01021114810f000d070520310140303000c03941c00e80a46929a070090512900d1050040e03441c60101a40210f54090b0f8030441060129050701001260312900100007443d1040c01786486c1c03689040c0a40c3c14031310140c410070070125661100000c07181019004080ca00c0c4656400b03800a42c0d54840c00242400101003050200310740c0c903a40036100071282c0003802c1c00c489454030704e080130514000800ca0000d140d40c843c0542c01c192001c0c000f0b0700101c040000700140c0015141048030072103100600b4a02018030b4601041001d07030794448030018034001c50310207410a9481c0c1030250000c29001040604014440601d1001c100054110501c0c50a0010540e00b03147c031244a40101d020080c000c00b4049002c001040c000c820900020b454100310000021400b80401b00084024403010740801c412508140b00140b00d9803000c1c020703d0000c28000c1e000340b0480c40c01e600c0d0808580901d028010a05450312008814480d54514100c00703481c094000315901c90000c61 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 305911645 1250 305910395 305910403
    0x607060b0907090312020d09030b0a0608190201030605030f060c070c0e0c030403031404150f0219050903060702061306110c01320c070605130f030201050106031d0703030827 76
    0x401180c400b4000c60103081c0880c03002c50318034816000340e282c0e492400e040d40c0c0c550f2942e074002049102503590782d01000372042d008001d054058121400700c800d08007624000102964811f400480c040da014042c0714800c1300340003801d10340c001c095100300b0b40c64040614009002c115641d010310700d604002820321000508c14001140603034480d880400c051100d203007d494a03a841141d0140c0000340400446401302034a4225550f030542c0f41038010700d01030480360182c940014040083c400900c0c04210070405050400071076801c9a40c0d400104410b2030450301349041c4ca400b5a40091949468100ca0300041c050f04054940c0f40c00c0c580c0003400b000d48603d04130200c3c0400c01d902c0d03c41204204100c50320018a80e1a03132030040700c4540c01a4903208881e1541c802410002d00401d401c41080003006001c40c0c00340d540041020703c00d90005c91154944500202a1446001141140c10301e032035420318000000102d1034201e95060400100580e42c00410900d4003481c1492440c41018000c900549510b01003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 305912895 1250 305911645 305911649
    0x14030703080a050a09170310030b042111072102040c0e030105070c0308060f0d080304080310050a05030307060c051308010f18030207030609020609060a0519030b0f0607060b090709 79
    0x24010400d650302c4940c4413040c1da164420240940018000500446424500440e4001c00752030000d004070f60f8950390341d00350160448040c1c0d5403544400b03e2190003028000104003100f079034a4044a44031400e100d032340d143c0d9154404c0c102104810601810300e4003500c000d4807942e0360003c0c07007000400f0494030068081010b02d05a240720794030301800596164050f40000b20340580680d101045a0341780350038062441140110698000701c1e50103040700040c0305c03800030351003244100a042d0301c900349862500450700d1141c001170300c241c40c860000c1c0035988000085d96102a00050046040e50703103600e0944180c4620100103a030300321145804075a5000540040142058200041042ca444c1f2494240191030400b001001a0000742c1e0400c00b04609030000701409000809040c50b183c017000c00150540d0007200140045040890440020140120724009110150070148003c9212a00041c051900054118450304010480e4000d011255000d052058000703881e001c0c0da4140a1406850070002d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 305914145 1250 305912895 305912911
    0xf1206060503011e020c0c0a0b0a110601320402030c1c0b21152e0302030303010614070212030c0d09080307021e03070f170313121403070308 62
    0x30000009050038144507011408490071143c0d10140d14030100340000e0742c8800c0038601240700340c0949000950f40c41000d88010101060750301c2e0384201c1c800c4c015224203c51280d03090b2542203074004008000715104c0303040420142046445114108480309030a614076441c8444e0014404020010408020401080041c00d41a4400051510808814280d407410700c00a500080c03405441e06914407408258460103030f4600070741d07212240040c04058421000ca440c0a01540344858002044045140701840f2400444c4846482804c50b00422340d00e11040c4145410020751410801d42d44218005030303205103900902d03403410400b48103002036030313604008a034460764081d140c02001c0003802404030b0b03021610708c90061420712410b07800700040c0b0000591403200303d42e0301a1600150b40c1e001e02400d0f020700305500219081500b0820503110300001000040000c0d4810803803a00000c48400c48001101c00c0180724400400c291b2401c801e020b2040180010607110104203d4101030300400118030078446 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 305915395 1250 305914145 305914151
    0xd052401092d0e0f0a0f020f031504080306041508241506070602370201020708071101020f0604031d06070308070311160803010512010204030b0c0901090f1206 70
    0x801030b4036944a0103106a03041c040d2000404a0700740003154104214000700e003800c4d103d1801c3c4002001d410120342c01c000b280c2007203030700405004502d495650451040402d0b07006049204030821580422080980040e008c41004800074166668940242014186949250210f5503542084a544000a040e4009641c04404001d254403540c902528400d0b1501400c00840401c1d1009102d90756000300300036582d03141c003041a5510001d0328003400d0703c042c9040150500b896881450510007100207d08401164010031405012801203806d40d050700b9004500f01c6410942400140d281c518041300180b1280552070410003416000008006200001c3c0c0b82e00c41c0482001041180310b205182000b40824003001c0030843d031078802c0e4807100000c1007690f02c282c60107001d07403903104489200700004c9940040000040c400350a0151810301c00e188240000c0d810b00307055039118800040020a48a580c00c004580d21803940c0c81103402d0b60042c200700c00e0300c96a103501d5586465900c0045c81c01954842c0c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 305916645 1250 305915395 305915411
    0x40308030a0509060402031c02102408010203150f0a09051003050f030a08010905070905041d0c04020414010f030b04060e0f1806010b0d0b0a08010603031803020d020d05240109 77
    0x2a011500303d05c0749a0050180c08203407a4050208620828110365404520402080880354148c5204804c00c0000f0140302064207890f0351521669a1116048081564018020f018080080d000740110b040030403102d503030f111103442c03001c98000d604681c04100032906042c2804951080f410084060302d0168003074400d19801645050303601d206540105c000102841c1c0100a1401190f0081d85c10403110714140040a40c1d410000741030b5201111214204002d0503820340d40a20200445682901c0c00e9070198100f030300d80300d075030580c8d01a5040c649041c00382d21100381486034884e50101da60303454010402c02c01c503a190b00e005860000211801c01841031080085030b03910b06030f07400807080602e882c0003c1910340e0030105100c8090700286151903c454480103900041c0d91100f8000c1c0242103a80c0001a0051a40c100284802e41456004c8448884040e0600c00358503002844c4081f69010b40f000070700303070442d8940380d8036024003030700c1410142a405100803403102c0c03c414036504071404883d050103010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 305917895 1250 305916645 305916661
    0x8071e0212150c090103090f06050a0606030e10024b030402030d0e19030b07020c06070c060e01110607031b0207080c0d0201020109241104060c03080a0e0102040308030a05 75
    0x103501003003403101003411840050780f010007120091160324010700d0003040070003013582c60035000380505a00721a026101c05c100052059148181402451180380034050300c410b0134201e54448121140f01c0030b0300b076000200807040c2d5412120302e407104110407840102480d2075002d0a01014000d400c600048441003d5013240203428000b66030080342c0040c043c10035090340007000d0341c50040401e0910f4000900030182c02101405940e52002540107500c0e0407098504400c0007818401c41480462003a20107001143c0405d2000d500082a100b01c0e0500e41c0c0e802c00100d006035480310702840d08200ba0706c9910b080110710340d030542103466002003402e011440340644042c1644c4403031250080b01582c1e88418a4160b481c944580d007002039900600001503200a140c88490307501d0310499261228404401054402c00c1c03a610403558240e1200c1000c0d8206814044004e1824911007c080c0810401e074021480ba0b44255100f9591f66007194001c55403241e90340380c10055034204480c1c2012007072500c00021640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 305919145 1250 305917895 305917903
    0x2010c080f01030b1302130f0212060d12050903010209040e01020a0e01030216060b06130f0e0601020321090f100605010818030901080a0204080607050d05070f0e010c08071e0212 78
    0x70b04e511484c103404554803990440d805031200034041ea404080c20174031042c0d18503d8030907140129085500581d68001181c00c5941d00390014140300d00a00982c44000c000ca4010f007090758441d58245482542c40d103a10b40040e029004860415501c40c4c80c00e85800e11641c0b05600620001400f9280c104200080e88015822805203110354081804640c000d080041c920f64000590408002c0807541000e4844c040129080c240c0e0304000c00001c2e0441062052480d000d2005038045800d1005501d029103e80700c403122405030b0401e82172b0428446022440c0300405201810407003030b64030104c410b13401c011042c0001030314180c4aa01d022510000c045242884200e60f005102e8074100d00039490b0080ca5401100c20380c1c0010402c0d0700c075560900000c1640c0000b0700c0741d580941c19640e141c0b0b4031400e03510b050404880e0050410014401880141104180c115122030443ca00900740182201d000e81094440c83c8100500107084400c1c904c07003400c40318590351801c44014002e568807020303000134014407991 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 305920395 1250 305919145 305919149
    0x240c08071b06060e1e0f160807260a06090b0906150c030309030301051201050f063703051507170c0405040f0c080a0614040f060f0602010c080f01 64
    0x310384086140c5a00c40c01001e6241d040d20420b00010f029595241c00301c400042640c200940d03c00900501d80880c2c0c4412405400805215030603519043c880f00001c041d001c0e40d8503d4040c01a100005500b42d4003542288440070900c407031142c0304400010540d01000000c44000d411703540b030860041031000d200e128204549102410514281e00d4070340421521850000c08030a2640b0101301d014180705042c030240d07001c1d407484001180c403541440e0400c144542c48501ca4a0168509010002024046003007607400400c00e40b803a81030650030300c0080c4202c1044034003401c0b4240d03480d54049480e004000600d42102d01030020340c5c400b000c064000c50421801a80c80e400000c1003480d16401c4e49030381c4079a070341c0c00c14071900b81546080d58a82c0420199125612070100c0d155450300c80c110b07050342003038005030700c04610b0303000708101030030704a8410301e443c0a6071100c2c0c0140d960341070011841e2161b5000201a000340501904141d50341e0b10000d020f080001000000100a5004a12101001011181 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 305921645 1250 305920395 305920397
    0x30501110c1f0e0f060109110f09090a15030c0e07050712050310051005091206090703030c060b120303040c21060b0d20031504030c02060307030603240c0807 69
    0x40c0011840c285201101c00804202c2c41a03a0b2294072140314800c1004081c8000c040d8080e00013036150000c48000c66180c59210309443e08100400301da4001070744220351302d1100c01c4610251680303500a030000105104902034001400b018400300a1240108562044444814000b882d0b81d0324444126054010084020051148a0050265240203e0196921032142020007503260b503240300217001d808071a40d00d0070101c2e1000620400500b49988049004001c3c1001021a401c05581c0c49941b500d280c0300107010030084241c040204465601306508401000704a5502c0031104895252030f94001d440031241e2650601c80000c03c0744404501c4002034800c3d58219601040d41d0b1220000327004030480960384208440001c0000403110300d128001c4242d10380c4480c44100e528010f15190004203001e02d8100b5058000304000682d0200004134132641c19940d080d140c6d10b4201c425805062035400050000c2d00040c1c02800342c52003180028100070b102d000c240551000d84c2000d0b20b80010175a0020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 305922895 1250 305921645 305921653
    0xe2d0604030c0f210206060a03030f0e040b030f060712140403120e0f031306031401091814012306130c1403040804090c051809070509030303040c030501110c 69
    0x103008a4040c900100e00b40380500c4950542d10320707656400341820314901001d4071402000154600840d8100f02c001c0d4800c60581c2c9030503c0d02d081d9180600030540c0707c080740d820080e007000e00403c03640f50340c0c10110800750054200c6145c15456041d01c0c1d2140c03821102d00700002d8130901d01c000e106c40c01e07002c3c40f03010a500c43c8440045071100e40b02120300d445482d02010360551503001c148500c000410940d00100c03500009180c039a0107040d9203015002c0568482c004050a0000c0e000a44003585010b07270440300b03445800500640541f181d4070340709442e92070140070002e55084a0311800780c103400000030401035000d40c0d5008c800400c003800c1031610594245400060b03144ea82a4032080075400700344444003605020703002d030352201200c0c0059442110100d98101c3c02203810400c84c946400740110140140c101142008000300380c404c600349032000d8241c411401d00011424882c084c00890303012801c041c0c156070343d91038642010b4840e40c026200480701586801c09601150312070300d0a5446884114002d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 305924145 1250 305922895 305922901
    0x150103080d020702011e0207030b0a060e01050607060b0a030b0a1b0e09180703030203070c06300207080d0b03100c2106051f090605090d080c0a060e2d06 67
    0x440d009400410f000c90610010001c40c03c0300700c00c54048080c0705056580102071840c01c52502000418004d040c4911640c24201c0500c0542103900f00d8034150b400c140c85007034898015003802000380c4010b0402c2a0071040c0c120000c000c1c80120f04080c0e00c00e9400780c50074015050429041000c41d10101c414100040c2031001d0319540f80f92080c0141e41100c80101d81c11402490681c4040c1080900d86c4201c0140c0d0002515008001d816807052004208504154070003031011020f40e480d400750840ea681d2841c54945480401840950684181a070015032041c0c07516801e00c0000c0003040c1d140c10182c428411420209120140340c0190919400e06540e280c0c203040c2c5415254100c1214450740b049055141d981c041a41c0d154103490350420b507503068800091080034000944031811540104c810402c08100480c45500c4003401d51501070381c42540d0f00e40e0f40c240456420308144800b2001003100f420450981e400100005d009185400704500302c001021140400000710003a2a004000130381001d800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 305925395 1250 305924145 305924167
    0x30809121c0c03110a0921020306070c03020f030d020c011b051b0f0d0509010f03060303050a110f06100504180b150607080a050a090803090102060109051008120403030215010308 78
    0x80042c00760b0a0341004542c0010700d41c10b0043c0d9410a04104002078040c00c4204084e803110450f8011070802955641d1401506802083c1c580c0e800822075000e10501c0c2c46ca50040602c2040f001041c12030400c143d83e1140452001100a5031141180c0c1e0346c41d601701419041e1201005010600c1c020258445a140c5101c0341040300e0010b01803800400640556411000c031400203226100300e14100d55030321030b079a580b13500004d402c6000910420303003010b180000a100017a0480121220044503080030304a8040e6901c4992905010401c0740c402c500408040c008401d607015200025160121400d0000900c2118000c0350303a034101402a050603810307404982c400380314540030803c0e0034018108501d400080c0e151ba01540c0d000f140d4810000e50001860303030700c07580d03c044494050600c0f40c010f54600040072000030765814040c01852070050faa00042100c0c1074134802040c00030080c0606813004d040c4a0320024400b5081480150054014880360601c042040234034103068961050007682850803040d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 305926645 1250 305925395 305925401
    0x6021b10050705010f061e06050409020f0403051e010609141306020702030312011404050c07021306051507050f01020c070303050304050102090a030b040507060305060d1e0f030809121c 81
    0x4030000510008210700c0011031828042e10a00e0030340c2102c080307042894000b60500f0110407009829440300d4803001402065402030403101210403240e005030321819038503008a103501c03440c0d00003811032060314412b42c0412602190410142030a900801c4020768410402c0c0a8a21948410340950060745c00a885150f000084160b19030140c0070050419006038007180c9550301050604d88854070b00c0b030041001c900c0d44030050135a00c1c0180ca0034815070038640140042da000700c0000034414140d140150301184910341c000002410010907405440c0c01102850b001036000d0102a203182c00780310002005030b281402201c2841c0013860041203403134a1501e0880749600007600840d80365408110000c0c06607246d125100c081e45c00b41c4034006090410f4600310f0300d0004a94051024503041a080004640d81c00d100032041680020650700140d1000c0c030034240701c80c082480106003100d040c401c0024507502c00b60081c4504460000c9a00d403e0446000982170302943c414101c00e400841100d0703500c01c425030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 305927895 1250 305926645 305926669
    0x60a06151107080303010b070c050103090b0403080415060b07050114010501020601050d0302100510090e071a090a03020907050306030607090b27040c0201020901020d050403120c050a050f0a0c06021b 87
    0x1400703031550242c035083c8030340c215802a40062401c04000c6407070010702c0750008281000b0102420b04000507045507031000e1041000a10150034803005600140611a001f050884c1c210f80b0b4602c204000c2da15038640b0003c54120171030654407986003000505002c00050384003416100160014a6507a01e00381c1000b00c0701c0c500e68811000c50081c82031800311410640169030044403141200f802050500da81007044900242540c12558481c0b2420044a5440c0080502c808a00140c180d0f540110002103140d0054650000390081c0c5080100306401d503003d0083d60042c6001c405543c0152190041221048414012035400360340400250507520042c040842c41c107141902c0e00340a04032a5030004044030101c80400780940d4000136050302a41e03042c4002101c0f02d40c40c1c02c1c03003800d2505503142c078214410102c03031101c2480000104117051050070030022050700c4e8800108c46e0b40030041e01850707440e0880e00e502122010100040801d02500105581508100316030700c1152500c0488204610300b9450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 305929145 1250 305927895 305927927
    0x6020c07090c1e0302031603020a03060b0706050f06060a0e0931060e010c0e1315090608190510050c19091509050108150f0a090e060a0615 61
    0x140e2000240303410705014481d04020a9240d005840d041d0074040308035590944204020188104104142c40340005100e0685c0b0005d46801038803019928025002007846422014102e07901045007000c000c81c0d42c000d18498200110b55000707a482c2d12062084a015a25044000c28070024007034165050400070194003220004007c2050304401d400314594850401c1207501c020781e11000c00042c0038840c02105a010446002044560600720303005001444074558035115810b401c0c0202c003c400140c022140407d070300d0300705035902d03035442175039400030318851140c0c0555014000d802528118102c098542a5402c840540268079880c04403400500d0000c154078003540090101c040c0403080640c1e6921040c8068a905600c0703820142c00302e851209a048074410045182e005000607607000d00c60b1500060300304080300c1c020840c0c20028880c05411075003550082402000010660b029400c00300084c9421000d82e459070b1200c0f400c20f0145c980c10300603c11500300c0740d142004880c0c032510040d4400c1c190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 305930395 1250 305929145 305929153
    0x60f16120f092d0b030402010f210504080f03010b12070206130204020915030a0f11040305030a180308120f071826010504050a03110616050c01090f060f060806100306020c 75
    0x4495810766084103d904280e2902c20b001c0104011542c001c4251081160030b4101003c0000e07601c6001c610400c21040440002512032000c901000001401ea4040c81014140d0a4903581c5401d0083c030683c100d04001e100c4940b461011a01d80c138004208580103080301e0041449031143c0b40c0900c006907222030f14041c0c12106201000020080e4000910700a8810b40e00105849000300c7d5800103981a85e045402440002c1000b000042c0000040300c401404904140680c0c010302040118000c071950301c041d22541c00082c19801d42805038181503c00c1d100800b4411064944101c01c40d651783c0f2400005500e0510401c06124080724a07290f001c00451a50090810343c0340c0070354080c00d40c3c0701601c0c2203501d503101040711400c05400c00000c01085a190700244190710304200300600f1080d04c0704c07688091100008070040442c0c0290448281507800603d40507005002e4a0001e0041101d074445a10301450b0420110f010300300030594602610114900c0030b500ca0458681100030b61080500505904c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 305931645 1250 305930395 305930459
    0x120b010912020f040c0302090307060201110a031d03030a0203040308240906030106050a0305030706050106170a05070e10360308090a030b01090b01080f07021902060f16120f09 77
    0x51303103005440b681001c036a03016032a070400c001814a4103c032508950203590403da17994080d02e8142c001c0c0e801c100b40c00d10b0041000d100e800200b0040c0400048110800c1c0400810003000c030000750001d5000710702c02e58032940c0740c3da01c02c42c0300c408603031544240c401000e110441200187c50705208040d00500020000035445603240d002440079261540110f506030000b0409a0034840c0a12400d030040c6140d0400306841025980c0348082140010244518143e841011500b00c602c202406003c03044054005c0501c82140f03034020300344407403d580c0118404080c0c40c009058607102405040b682c8200c00d0961103403820b40c0e130f401500d038120001d0360343c0000784504000081440359803540d0003003022443c00201408504001400c0d000024a084110303100d00d07091001d513a900044400600b000c4c135070240d40c0c01e03040e407001914622a107a2070703007034121001c90b240d8420001915000d8241f4070070078004825001d4004e0541e01851804010700120326201000c000513a403503101030320106414050050711310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 305932895 1250 305931645 305931649
    0xb1f0203071419140c0f1503040623040209010501050a301e0b0901050a06030e0c06180109151715031218031209010f050c010516120b010912020f 64
    0x2140082055400d54142c0820440d13103003092100210141044e0380c00d041a82c014004280142c0d801800b059040e500000000c0034085903500c40e80203140702c000c451a100e8800c4100398031041040e80c05a02c203158610001540c4d40c01003003107801d4803107a6200d038807a59881c0c4040803104060340b0b1000300c96484a560000002070349105610f50201b04503031203480607448a013044200e8001c4841c5a00403200d0341c00502490b95050003000450b20f2619000c1313240b003103800229017090741c618030183d01700d0030100d00c0f29000b480030060281d030508203a96886d0000c2d80e0b507049011a8000e1805040464030f400c00344002401d500703543d42d42c459a140007034000c0180c50340209103080400c030a238000c84900803640d0204d00d44074030681d506196003140140b07030303204103808004072a12a031503040e814000b0031188800c0550140d41510316030b410383c0c0d000b004685030000003043d0400075201030b60006080d6080c0121042060712612501c60010381d1100107290a00c01118400c1007402000e80c2d21480080b80c0c0d2540f6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 305934145 1250 305932895 305932933
    0x40902040905071e060e01120230150d110909120f120601020309010f180504020c0f0c01020f0616120c11160e06060708040f06030b1f02030714 63
    0x2040c501303041071110500c0c198100e20010003900008200082d00c1160308583c0c1e40007420051a010001c001a503403644800c203d5500841e6180c410700107600d000710004103036905240248103482d0250400d103041c0c070000801000c0c13071620304014064210303042c035617601d0706203082d0300c580c000c503200110f4642c0c000d0301e503003c3c2283e0000321145480e110b000036040c1c0c070244181d0382c1680250b0300b8001035050080120001e84003202c00c0070a041000740b82c02804820640b6205014010000640210369400c00804c403142c80e601c1c41d02c404040352050011801c002d510000300c4622805005018007040c6c0c58001041500180c0348410400300912400804001303800c6114400b1400e042d6140c02100d03107003541e20241012490a483d403243c0c040d1040c108050240e1140641d40b100040311420b55a003010728050901c0e00403070b0020021003111620105101c0d030035a0040d000c05504070703000008607100c0003c00081138807000640d00180c0003400f02c80001540e10a0b48400381c807184041e280310600740a445c00e04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 305935251 1106 305934145 305934149
    0x102100f0612080909011406070605090111030a05161d010e04020d0204030c21020d06050402180c0d05010807050603191b0c0b0703091104090204090507 67
    0x82490396809a009402012840d40b0314518a00348209160461910746018000720000450380900d4001074560340d81c030041c2010720b41041607440c0c2c405070401a00000c071540d212801007038000c109070055841054007510014443c6401081d26000d8080e060665081c403022501000b4810246915400241c0b828207050380c01c03038076100105000b0b1048410510550344041404010007000c924100216030f05e0584020300c40d4940598a143c804030311800a61100d1429a60000a0100d8000d694401d0005256081c00c0d0350030400074017400422a05042010000100c0c154200c402e03110b0140035094020050101c0c50504010030b00d01e200142c0f1448010340c07420a0103007883c071a03410600711014940c01c00010b000703202d94044d000b1a201d8000722900c00707a410001c1e40c0140b03c1c3c03140d5079516802c0523004004d202c5d064244401001c2482080ea001501e030000c3c00d01080c0100b1032040 = true := by decide +kernel

theorem cover : BRFrame.Cov 305755395 305935251 := by
  have h0 := BRFrame.cov_init 305755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 305755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 305755395 ≤ n) (h2 : n < 305935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
