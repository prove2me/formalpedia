-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0391
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:34:26.847911+00:00
-- url     : https://prove2.me/submissions/6ec36719-6165-4400-b4d2-ff7b7890fdc6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 70143887 ≤ n < 70323743 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 70145137 1250 70143887 70143889
    0x809030a0812010f05180703050c130e04020a060504060e06030a0b0409030e0405060607150b010512010e060301140601231c1b0906080a050603070f0801020705010c02030a0507020f 79
    0xc0440804020207400001074a0061440c2c6180401d040b52000101030160aa0300c038144202c080c2224008200c2d42400340000c0c0f040750003603100903004a0030700d980c1c40c01c0c10000e003481003a010954000d801d8005604040104504e0961045000390049162590500d841d04101610000c810302c90103124900c04000100050a01e9002c01080040181705004407812410b025102445440600340200d0901000504a0802201301e81d00c2c69400141e81098407003607043c640003410401140c9040000801c001420b080e24182c4150203003940c030206008604200c0d0130035084951000056150a21117003c0185036030700041e4141c0d030b0701c1840d180010486204621010300d486000a04240c9107a080d010306290702150b4865808030401111650a5024007201901c4441c1180310b0280017500301000110500c4494000c0342d00b0400141c21250503e4440b83d400d503448485410511b21a9804240401489424040d095065100340042c601d0b0024245005185200f001000390242c104500860a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 70146387 1250 70145137 70145143
    0x7110604060b010e0d081803030a050a1b060e1b0a030b15150409090c050406080706051b01020417060f041211031210061202040b030109050405010207140708070b0c0604080903 77
    0x3a149004102481608084c03612941c0307030300145c000090700340f01d90400e40c005080010440700450443d0b11641d00301040d481c000c584100c0051500c3742c0c560b000315504030002c0c0c0300e4040c840e65841c140d805804403070078062002019004d904249840b800c00050f0420100b00f00110b15600000c2c90b03210402400c030a40003045d4043c1200c00345c0c23924079500084c0058412400c2e4403070341406100c0d40700ca458095035041000700b62203071805003208039007055904200319070240009280303442200041c03445a01e654010542241c1095000401810214084c10301d154801d010350750380224000c2040780c40342171a86480441c18038088510702402140b007154919201c0410503079120004c98200510580741c43e04009501d8182031080001262080b41c030368503991210300980d020b403032041c0c0c201410741c0e2070b11100340c0141401070020388081d54200502d00104883c0b0b1a082c42c02d4400030020080d45140c810803502e0150305074002c0c1c00e2510140085a881e100108a1540142c2c0001089486010040000341 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 70147637 1250 70146387 70146407
    0x203060105070c030b0613050c030606130902040306021b2b02011808091008010e040f0c030204020a03050105150c250e040501061d040f03120b0414040b07110604060b01 74
    0xf01c0124031580000030003a9011095210315000d80304607001030f02c0c40d0000815100151080c01c540c5c1000d000058050030320002919072180c6840b01d80480e59501c4046d8003c0b03a005400c2503a44940000e668400702944641c1a45c501034414001e01d5004011702982c0491030a1150762040841006910419607100b5084070104160003140c440e2980c2d15841d000d03071694419002d0f14001e0400004c0b1300b041a019003a054102d0314a12140141582c0e1581d5201c80440000412101c6041c44100440582c07a030384003512440c41e450b00c0001d11541064100f111030200e40d01500d02e803420410200c0040c0d03c000c11409181c000d080c085002000d24003040e60300f00005904040c42c48194141040300740310054010804540440140301417806040500303000c034240403140a443c0000ba940d600000a01ca5200403c800d01c0c3c00c10300060180c040e000040580d4002100808c2162003041403000380201c60080c950420308605000382060312640d00b030f6031030b00c1c0010710146c074403981c03504030b100b4a034064a040c0d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 70148887 1250 70147637 70147643
    0x6060c05100c0509042a090602121e0c0f1213030206090409060207030c140d05040302010f020c0909101104030f1203090501090f050c0a05061c091b08060c040e0109020306010507 78
    0x10240c40e50440f1803103402440400030809101c44c03500401b850b540240e0b0081c0070b03558658040c004c1c100f211051010180e205c02956002c0c60f0891003984d000e40d4074000540302c1d65500602410f000040340f01a1858000d841400c840481d10400005200009801c9400b04403541940c034035484154400000b00104079100000e4505030000800800305941714960444180c410480a1101c001c01d40c0d80a0742d44207a10754550204400b0001440590300076510603134442442e104803034a03401007001249182e031060b14006402d510841c8100da55002c0c1d40103024030700c42204011824945103859115000f0601d22002c3d080f1035905d802441d00740d22036000803102c0d5800900901c000d10242c9000380c0c0801806400360b4840c024005401707601e2030580302d20002c03194000c2c29a414160304000f203c0c18080b1a99407200b070035030748200181c00107642c24102c1880c0d00c12007254820343d0340380404203801c281d8014141d482c1d07103c007000148241e8660310751080c15035aa0b0040141c40e03503100d00058469124200000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 70150137 1250 70148887 70148891
    0x1206140403020c0108010f0e01030609020d0609241509020c1c120612020906091503061003060b0102060c040b071a0a0c020d0302070c170c1806010306060c05100c050904 74
    0x401490b8001035004843c9800fa40d9210307640c1c0e40c440d03110810352031a00407040710388600001000800c16580000401600017007040189254541d5008101ca034041812100480d104070ac182041601c48034821a1801d80003051040c1903600c510300c241c2c11900d00604268681c04181c22550761000c0080d0038040a60228039001d003a4072600203800210403452800e84242440c42c0460b1460a262209941e540e002e08041415140c4108200c501c44004000462024400c510340e105580e04219090207109110300036030b60281107040c0030b0140e41c10803c415042d90b21040c1489407400b01d00b002c4030200c90a05210303a40310b8280d80307021105024070f2030f42c0d08480101e0805000e2410910340c040c40003940740d6000c40719010360300c41d400c5e0181d018404024000d0040448100b09032144119140084c1000f201500c124040c01400116820840c003050000071202c4001c01965582511500002d0641800c00103d030682903030b80c0517601e000405048510588414a1007646c1d07011342c084e2201041c0007801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 70151387 1250 70150137 70150141
    0x20d0b040f2f0604030515040206160f060f050105090403030e0c0a08011406040b0604090f0e01050702060403080601020c1f090504020c100f02030c0f07030203071b0608100e01120614 80
    0x9080400c003811600e200d40d654580310318a0b4645020300455080700d9100c00500a001d582510320b600b200c10040040e41c00060410488005005078840c00f4400e9204200700508500d0078100801255150b01c40940e1951a0800600c6941d613411400d43c0d21591502e00420720040312040300341407104c56030130385030010a0f51a02286004042d003210442d20a21505151150350740340400c4161009424219001079080105006190241e0030511900c000c0c10804070302c00048000d0325086400031280f00005030020750601007010b07881904107421010034401010200c0c03454000810f0f400494410031300120945070b501c41098042c141080041000130421500d0b09404a40c440d21200c2c1000980c60302c40c40e01c0c00c9200f41d015540300b0317a802452032147c20f504014241d0b050181301e0384581005c0e019403109201090024808000015400310101d50b0502c40c0ca00c1e00002030540c43c8040e08508036080c0d514070a021b4181404a034504480c90510610502c00c11410701b100140358484110b01911140c0e41 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 70152637 1250 70151387 70151423
    0xa1b0f061a04050f010f15050903060a090512190806041805160515040302090c0d06030c03020a1502300304060204080c0607050703020105090114070c05040b0607020d0b040f 76
    0x412525501c269400e002941e511081c20840c04402d00501040316904401130080f848120000c840e0403620b410701d40c3c074007c06031000a01e092011540c0c1c4480c0c0e074486141008000041c02110310711060405a24144440807124445000e540441d0008001c0a0f07400200faa607200c0e000818220f11500e032060b08130f849070400b5034588815501e10390b5000c2480b100041c00d400d04400b58502d819602040c503041c00e007107600b00500d80030b0141c07141000c03150a21080c00c01801c14801c001c001d5102e80c544210091652060110406595100301c4141c914240600107080c2c021800040b483c849100d850342019220050a0b40044c405024a00d94440441000204100c503030003041a0781d41c10003107800d030f9071026003004024451b02000500e00c1d0042c850420042d40540007500003010141410341d070f032445150f02d960b01e03500000f0050340d044a00d0036040101381030a110768001d44200b41c43c000c1c64a04c3c01e402103000010b81010007841d000001d00001c3c1409941c4201c11030180e44a1460141c0c91074401e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 70153887 1250 70152637 70152671
    0x201032a030b01020d1404050603091501080f01060f061b0611070303051b03060a0e0901020702120619051e06040902190e070c0314070303090b090a060b0301020a1b0f06 74
    0xb88414003620170000c452000c180590300d0105050840d40c502d44c0b40038104824032010ba007024100503814891000d0380f40701da03010022700c140640140c800070803034074003500041402d50791240d01c508032007542501c0c14082c050b0302c002581c03480c007180c43c80541d4110030303450564010403945240300d40c00500410407504140c0d068108078042d0a42d680500b1188003610300c81c1d145480240c600355840031001030100407003103050513001e0340031000c2400141090480e402061348026a284000040c4d005a07003000084030086100352075110007042d00308541e00d004448110081c05110b40a100e071140c00c0c3c0040c2250740c4a8014072048c03a0701a0440071004040000320340307145140d004116075255240c00140c103081c86030000c01e040b1342d01030340c52900d0003000042c1c542181d0700a8400394201500c400390030010a0325000c5544c081c0d01501d000341040656802c00c542200d15401640d40b180e4010402c1c409040c0c2c1c0035240c403a00b150100c1c1c1035240e0300b559240c03040c29010003c0008001e41c1c04c11916501e100258 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 70155137 1250 70153887 70153901
    0xc0501022109062203090f0b0436110405040603050304031203020c03030a051510081008070b0304030503061810170a03020d12020c150604060605040b03040201032a03 73
    0x315100c4041e1124802c03540c81d02d00444210f490398a588070a105480000c810301c0070441d0180c02c11640540c0c4448aa007444551500026603502d00000c082103506c103c400c4240b4a5440018000101d06884126031a00358485a01c5100282c9a2110040c001e03000022140184002442045465903e00e401522908544030a81d0a10580818120258024000c650241d10041d01662565582070011300080a024001400020708010000000c3c0c84080103000740707030482e03143c8120700e00d800c0c0074001c03010b44180c001c020280c2144004000d01d0202c02c0c2901c4d00a949030808036221754882c4086035034420380442c940f1142031a413050003001e440f07241824050315000d0740c401e0314800c406880d440e0b84990a031002001a8070040c10208018801e900c9100d4003801f00310094035245c20241c3c10703442c10b171840b603007030072040c00c00001d01a252500c6e10519005103110705100b801c1c00e18040548410f400010b00280c141a19101c480c40c0e81006041100c0d400144114205584054414010000c02407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 70156387 1250 70155137 70155187
    0x7032006041d070503040305030105040c03020c0d08091b09180124090b1c030f0201110705010b090a0c021c03060f12020f040e10020c030d09030216140109090c0c050102 74
    0x40c2e2011a41c00f91003003048901c40e64150321028610391811050100030000404904105a42481394003103503a0309005800700c000c4141c0c4e494000d410030455080c2001d0403488042c3d180240300c1e0880300e01c0d40322002403a50001d081c0401240484140001901410b9403c1d503a80044500045824070342c000c051801c0c00b5503c00300310800c000c42c100d43c2072000c48500815041e050755140d02c54000000c3c4a03058070148011980f0010620320140c07900c5a8030340d000726001701c0b40c0d40d45a125442c2641482d194042d40140341c550140104003501c00041e44a00405a4140d0480358020041040c98000d4010100529035a03002c000940ea55400040e405400300b0001c81c4900c5a102c2c915040d86000c0c000c1c014000000740c0505103840300a01d59100075485030202c0d034080e020900180408610780d2040c0002c083c0260081e241e201030348a030302410492aa008104903503146400e030180f40c0d070301c500104140c032840300001440081400080d9000ba0640748024147c0d0b00000c1c000f440d42c0740c460b00071031007410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 70157637 1250 70156387 70156439
    0x130210120c08040f02040b03120c01060501120b0607020d0f020901060509030105090a050c1905090a021c0606020c100c0605091015030809011404210c080a03020703200604 75
    0x34040d04101c5002c0030a5602804030000780650304098034140d40405918400181101c2c15a803000c004c07518140c200d41e400104a075950082004656000390303c111908034000340402c5948405c0c80050014050071802901a0030003450032020005858600012a50020140b04466030744940c0202150b0240310b1450203942080003080c0d0b030000000d079410b10b16a1000c003411000902e0014440c4d040c050f0002844003210b0810000303a140c1740d0312100d500807598983c0241e50f42c400c0388200780f5228120501c0e00c00162030460200035442c1c0c007040a442c2d0b9a41101c051100c074803001c408a072503109410000d0115031500b0b0500524140018440070500303412081440064000b1600b01c600014500c005422600100040045036100e010301100c050400c82143c1d003050786900313560a8032142644d03004031085a0100550a22800301f14440081120a0040071110700c036580003915007000744801400101040d0704000d80708800003114202410250240382c46075a00c0c12003211141340f406000c0e051003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 70158887 1250 70157637 70157651
    0x40b040c080312190209040f020403020301050f040b010b09150a0215070518091008060c0a080a0c0210050a06090c02030d0f1404080d020f040e0f0a06080a0b13021012 73
    0x32801005032240004955110907241e950b958000d00c0202e1108200904d26608020202c004d564038802c460860f0340300e0000507203580c2103106060848a0181c10710340301c41d407040304000000d50200011815103003034840290710750342c0c000c0224850344c0d0b2000c03031411000004201924050f600003100340702200c400390a50a5915900010b507500d202c0d1110105880e120140800f8441c18240480d84c1c201c4114a400000075a440079403c0c14a04152901c800c580000641264031540c05400142c10140183c402c122843c007499002c3e66600078012440451606d900000300f10036400d501c088020850070700306100c04400c00d02c001303450381d000364424450140b401d0100c900d1340450742b0a41e20107640c3c0301c070f02442139102c0352290202c50300705003201011190208501402c1c03100c144040c20080440e050210b007207090207408005c1c460030050662038142d00d882c80801140c10002101e008049d004000c2400946615001e03071449440014007941190100c5c82c104c20300c0358450070842604401488c20010a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 70160137 1250 70158887 70158899
    0x101d2806080603030711030708030a050a020f010c080402010309020a080f070518010e061203040b040b0406020f0c0303041e032108070c0c032415061103040506070b07021005040b040c 80
    0x1a1400351206500f5a0040c4a03040000d1a09600711845c10001001c940c02d0a03940e4000d5455544806c820800050011440142c807580422414104030540340082c042c0031483c802c000c148040c0100041d04041e00da104290035919481c08000180032168141c80001d5404800196642103d21815025181c4602441341000a00c404203040c0c68080b611908591102402c00666403050413008245000420001500300c5109004100926007040c825485503c3d20070701034185110300690f0b04954201c011001d865580110841d4245d03040d0401c00848061514a040301c803000c981c200030100301c071580c51103a403500d030a070300d080d103500381c50752101140daa91010480c0d0142184000415428100c03200348000303007200c00d290901c1e02d40460182411411524060143c950041c8400c925030141d032010320205034001c150450600c2294015450146800301081c498880d14201900107210103010800e480d10a00075505402255841404030307007854188071031283c505a07402c07240f04090140c002a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 70161387 1250 70160137 70160147
    0x3060f0a050a05090702030c0a0c1404140115030e01050108160807080615040902041a0a0605040b03040f0303090506010609082109010315080a05060f06030705101d2806 74
    0x19a6005000a9166850102880740c82d44000c5c0103c001d50200f4001c410f420742080244802d55070080c61901103c40c5000414a80c1a002e501510302450424100510702c0f0411980641110050070107a8480441c0d070104400500e100801c030b281d1942040300000b0907190000700c0004110304900c901240c555100002c40e507480c1244140034458004c0e200054024030907a80c24402c00700f02800105d100e1020b503002404580790012900c4441c0c2000c0440d007009e06000841c0c40c05401c5034141b251505080200713883c0706001c0140001c01d903580d80070607181014400d8000c8aaa41c0d07100c0e08441d200c0d42c40d460b01414015650040030b207e403056031070000d00c6003c03400c0700800c1c00e000003c4051a040c9400011000f600c03030051509108007090400140444040101d0014107015030040e081d40e007060180b0030400c0b40d018020510a50003a0420705c8203540d1401030440d01001410207450ba40441a6403191508800b11020762003c4290090340d0b140100b0b050107008568004040040300751544000c1e20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 70162637 1250 70161387 70161389
    0x13090b04060801020a23040e010e0a0c02060907030f0f0803090601061101020a0e01031d0706111903050f180a2303060408030604020f0702090c220506030417070606060503060f0a 78
    0x40e08540043c11b1110420741012546800010110320303050302c8910746109400b00780d02600f4820b581c0401c02c0118221482404882c88552001c0d03e51030401c07585940c1d80740d42a0101605d4283c0f201e0b10802002540095a40ca45a11100090716454241201d9490320000d22070600810b10749000b414441d801031003202e0686d015511000c00380541a40118024010400c0c449030004242009443c0500100104401460300d541d4420311540c04200c490b042c10122042c282016008001c5080026040f500f070340d0080614142c410344500380e00b0941013128a264001e1500000b003500c000c14507a450709501e06402c990718001f142d0243300b078030905548940841c0d018100f9401030012490a01d030940043c4101c484185159013011a075400040381400c040d03600300e00003d80042c61540e9200d01407a807448166140c0ca0410361540740c500410381c9840f00400c01421144142d40045090085a041c0c030303e841e801c00d03000c02c0500d845090151181c1d20650b9500c0c411541c01103022664a0a01e4802e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 70163887 1250 70162637 70162657
    0x1080f0706020d020d05032a09040f020408060a02090303040f150305090606010206012106020d0b040506090108060a1805100608070803040f0b0a09051e150a020316030513090b0406080102 82
    0x31002055202c0226503a03000a0100803a850344268803038000d02e8035230390740d0900305055449980d80725141c10030082103401d200400340303900e40107000800181401042941e4020504400943c0c1c1e030345690300203419403040781c0052401000200d400303c0e040c000e200c0c040e82403450a40341084251500314123aa5100b600301d4181d4016030044006100713441c000358480100041c2c88020911182080c0c0c4d854090760008541031001964070281d04846240c9130040680080040c1c60045165040c410340c00d45452005107000002d58580301548404071180c280303003a5603900a400e407080007903540300002c094070003031080020604c1000f00100f81e40c80084111022201c003243c0260f1900d00d80f900b403021a401004000c0107209403004001080c2d11105510740021503150035046155400030204100f902001d0104035000c0414020066042c0d000030882e51ba14040e09600c0070290003520b030458183c400c2035020b8601279000c1a000580900c1350b00034503035400b400c031802c2c04815160890a1300300c0c02080440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 70165137 1250 70163887 70163893
    0x6040b1012030e030106150e0a0918030503040c050618031c0f0c0501020c01240603050103020a030b10030618020f09040302060412090302030102070803010618260c030601080f0706020d02 82
    0x700c0028091146101c00c0340000e4004070340513580f55842540302103840000c00114901402c0c10680b0310740b0401c08800b07001910010081c1c540840c0c4810503005d6000c0d002024040008085014400c5491682d0021b045c02000d180d518114980c4550b0b1850180352518001e12a103842189034807803008a0380046002551104c0b0b501c015944101d40b181102d18060310255400c12012140040c00c4c001e00d041d80c03120417900e45e440c0160090701602c200c0b0580c000810549014014401079035591900c40c00c40c0c2e013020540c03005854070a84050707041300d1540000c1400d0b03d8040746000c00141e860f0741448060003100e6600202155400780311800ba0b0441e00140140c1148002600041070f0000b185000746562800c005603030384a5010a00b2684080e409548080c00400104000d580c0107011f4a41d041100440c001c1007450128444d200c4590124115844240c810f10b0817406030b41040165403900000b4219100d559498410075101c1000d25407003c1c10303004803000400d8007800014100c60815260b401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 70166387 1250 70165137 70165169
    0x30414041a060a180906030f0201020601090b01051b0313140316120f0302120309060f160f050d021c02040503060106050307050307030506012106060305070f0e060d060b03010806040b10 81
    0x441341d4051010300b0103035035129032601080540481c45954061407103070380078101c0d2945070b0001901d401016804074010782c0c03c0c03079070280b05a684031040c3e80340700500b081c000610200f2808a01d007140a142c200300e600070b400300300010b8880460f650f0b00410000607415103611110b4015041d002c0e002600900c910030b5180c0480d500060369042440c52458021701c10750301070840d840f82020940d40103940d492107661000f001e0283d03540c0c607502c1541d0050014486d407100c100b80e5101c098003d42000b403520052200104130a16400d680781c04461308043c01d03805012803013010420450094005002c0d8600a01c00c86c400414014052412640510100d03160740342560340b03110b002c40143c10300a0100d4100010401c034030801010340640903200c030054007c00314005042c020021300302c8074024074000c2040b06903045104540d40202055541510a0340c455a50780d007103003940d4010f481c0c154450184258008000101d0034004112280600c0c0308048800f810b0b203605100700d6039440640a020900c00d18554 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 70167637 1250 70166387 70166407
    0x201140708071406041a060108060d0302030f0d060f150c1101030b04110c010c050a091e08030f07051005060604090b01030f0e01060305211207050408030414041a06 72
    0x4080c014007440390014915065080d40c2d0ba040c2c00200580754169a40844107200030001d41d1400ca0075110121444a500c61800100080c609040038003c24082c0c10407229400c1418402e00480b01c012400300180f41e900c203010340301c00300200704500c10a5204007403054046035400c1c05008012681185a582e400701c5001510394000041030350340650f0503d507480d241030b00c20f44c40d18002c05040618040720705031140040b0303404600b540c0440007400100a010400459080e03008000401034a01c8120040d0b60f800301c040c0f03d900000d0f2507802200743c0384404101c24200c600484010b0903c98803600545e130f1040c80b0341009034203a0b6419240c0301c2c0e020006100034801e45006038070910030f0150516020603815084240cae403003180c0c04007070030100e40d9441d0441030051200801c100c18000c02400300e8130100b1f008410500c085801980180c1d02c1020006000c074001070300c140260f03005400c00e2030649590759522144510b0a0280311480c3e8059801e180c2035500c00f0b110511529071008001c0d10107490003240310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 70168887 1250 70167637 70167677
    0x90d02061902120a0608060a060e2d010b07050d0207080a020906010c2010050906030105010c0312020d1b0c0c0501050d0905060a0209031501061704021216050406050d0201 75
    0x12003550001d99080c00799081c0c0b0b40f41c00b0031850045900900004800707080050150900b44020301c880096030400104002c0c003400c0c84020b50303002c80c80d01d0b00c52103461000c1981845d5a9951200555001c0461001180e10115100100308680c4224101c0e03144802d15507040c3c2e11071245104d1000160404c15004001d0300384107031500c0d442503052500c2440c91a10765100c41c0380e041e180c14a580c0c02c0f00d2095040e442410440090050f07106582826402c0618040000f5082c0c4414091213040144800801040500070b410b25440b04411103019900c5400c00c2044c40c3c000d0040b0b4400324101031000d2400c240b210300840d810b00100b604845031800c914100320040d11a640003161040380c803a41d40b00000042502440000c3c01021a0700000d6510448041098984828252041110504040101300e1300d40c00241300700c942c1100c071040407900e50b5117000045200c5e1120700b6404c0f160040c1a40340259080f0501c0d0300b01911012242004096107950921035840d841c03640082c00f1031000c100c04420740c0d0001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 70170137 1250 70168887 70168921
    0x4150221040e0703020c0a0302010f050106050906090f010201060308030a0b0f09010510030b0a09060602010603110105041d090c0d060b0909070b040b030c070203030a0918050c07080309070e090f06090d0206 90
    0xf40c10301510700008191700f41d1800041d03071000c1d00107035990042500301e0000d5005880c01400030b481c0550502c148500003820b1841941013480c42045e0720310404410740d00070b4200e50021500842c1264580c0341c00c10b505c501412001c00311134800c0507005401080340c41c00f144414180d40e0080c00c505000d56a0300020b40080c001e195156600c40019200024468240e00035203001d48102da0000ca1200d1039441c5c4160301150b020700040c14032005000c184894421408030304c0400d148030804ca042d640318240420304280003581e01a80003108140720105210b01504641c1d00319100791064000d03070b6181c0740826241c2d08240030700190f80004020410602034408042e40d0455882c42c80c0628000b850750000345180c0c0203070402c0c004601c04890410005e000d04505051482200300144211303c2c200d000e80318a881a240002c018080c040040f54840108100308000303005120001c0000e4100080d400d980d46001ba8800840e61181c5800500000c0700440c1060f80042c064006040ca61a0f03c11a98000d030f1307407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 70171387 1250 70170137 70170151
    0x80306190302030f0106080f03070512070c030206040f080c09090316030212030f0609010f05090621070b1b030c0601060e1305070302070204060603091101120b0604150221040e 77
    0x41064003201682e001d10103a034030304e50010000103500303241420503400c2c0304ea030b00a02e8203543c0081c003401000c14404107580d05188603100030356035101c0c0946424a07a4180c942c10207500007102080100710041440740c401d05840303000c02202c00c050f4006040111902d4100d6802030550814400e101d906100000f841e0100ca10030b00540748808102d5541c41034a802c202c900c5002100c88600b803000c58241800d645025180400d09210ba00b81880003140c000d110140035980660318078403044c801d044001c1c0001c0c105119040958107100d0303840400034032982120700291404046205d000c00702c440000202e07103003460094090310786a0729114003513031401d080c95076080e00401c0b0445d140c00341c1030851150b02d1199090341c8005880d00004d0050104507401c07504420241894829010045156142c8038080c008091901c11200c01903410800d0140402401841d003046010038046000751400d202c2c06400021070f82110075880b55010010036010300c061201c1020f0508000c00d0201ca21140c02060340020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 70172637 1250 70171387 70171429
    0x10f050c030714041a040f0504051e15090c030103120203030403050f090d0602070606151b060e031204030305040b131a090c03070305030913050106050313050c09041a0c0a09050613030804180e0109080306 89
    0x30382c00700411983741040740c800a0080b000001801041118043c00c40c20900910046003103103003036500030300588900c41101440c003001284a40c0c4640d03a40f0504000380e9480b5109544549542c038020b8084c1400780a00c2c80c2014010003c5422103100c0c41c42030303110030140d501d440d8070380c5007681300d55005200c03500c0b0822039400b04000948d403104101c081240510b1003550006820300d450700780f814a4100181c81410360f181c0c011a640e000c94401c4444640b600c406c0b07030780d0050980f505410f4034682450a03002e603401d809111000014484040081c080340c14041d1240407082140701404801c0b80c900f401004046081403000c02d03800c07402031034006007407442078084454064005000501d0400105c0e4112255444107080040340310448880c00c3d0060b0102180c1801d000007654003810400040c00b4644c09580e011464611010f10360015800030350300322200c0785c1c0d2a5112407080310800070b4240d10181407400d0102001c22420140701d15141103800150707060541d11401700304281c0303400c121040c0000341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 70173887 1250 70172637 70172671
    0x90106050604081605060307050a36080709020906030708040f060203040f030e030a050705060c03040b0a08070f08091005090309030105090f010f050c030714041a040f0504051e 77
    0x103250700000700040c007840c80041c0060001201400518900b85d00314500905040c003d103e00e1603004016600f41c003815040a00650a02110b601c00007410819404c4c1d65400071100751040c001c81c0c0c0418000d40380401c1c19100c0c41e0361154400d4081c1d00c50903100356042102040012000340c4541c0380303150041d1140c1000d045100440e29042c0981e041a1030966031322000c1c0800c9410141c00405022074414241d000e01500001a100c00e0380304c21492180501542000509280f909410b00c101ca0181690301d18198494083c2c01c80101540b4044480501140303450303102214440c02003000602c10800c5900078040c1c41b1040300200090200030381000720714801888202c00956082c01480d00c60049030005103920b8081a4486081d14594a4003000ca5881c0600780440101d401e0216540460300e810325098201140d90306040ca44a10350103a188603d00742605031074441070380010002c9522001800301e010340c030f810411045401c1521500f000c41d0080843e8129032000400840e400fa0301c840e2166150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 70175137 1250 70173887 70173889
    0x6081b0a03021305010e030703061107020402040e01060207050d050607031a03010221011202031b01050403050601180c05090607060e010221180c031e0703140105040309061806050309010605 83
    0x68005612000100c1e07004101104003c0c00d120740c8038000c01003480e018140d0b507103400209032102001c1c08003801c40e9450704405156800103c0c219a4141d50151045648559503040c103802e44500703019100044c001d2800010791443c03e0b00c0e80b4041c40e0f4000010304040e483d4101c064004080040d00542d88008041c050030360f41d9020301c0902200044104905600e25640c031a2001f0100d05800c0014011403540030380c00580c40c0058000b500c8492003065600e0300f81a5001a54603005035800200588206800450180424810700d014048840360134803e0400d00c0e41d0035502c5000c2e074000d150704a10140801c401164aa0300102001424140014548010740020050100d0500c4d002e150508844c4144100e924622424440346041040a80030000b009400207444400080b891600201e000b5105900301b83e0030b0002400642e84a810740400048025049000c1c00c2e0446060340890000640010070a026604040c28406218034060503a4140310f000c2d241500040c20a030725035940c4d50404074107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 70176387 1250 70175137 70175191
    0xc2209020408060601030e0f15060f09040c09050601020601050f0603100306020c0307020316080d080a0e03181009030221011d0a020306010909020901030807050109050d0801060201060b03100608 85
    0xa009200d000e00807504c0c2140c005025244090b134107402d1684003c950780c02c2000e0100311962081e044078840c0d00c05842d458005070040040da0122980411201d05110411090b44110411603600402c14000c9540d81c00059844120910505800550b2410f6041706481e0010055511000c114103104105442c0c6c2c840c0c4003240c00c0048a00f44e541c0c40001d40e0710940c5410010081014a9443c01012040c03d00e102691034800140e0058103201d80030f000710f40300c407075503400405207100c0e21401c994503114600a07032000544518100c500400c6002d00302080710b4420408001070329006004c0a0001c407190004140030600914802c050b55070702c14211180c6000c0207001584102d0960051041001c02d004260502c0c2d01a444401158941950100162100c44d03e0a0440c0d4002030181c2d10b411741401c2060141485080c02030040c025a4030508080340c00c440500d050320801c2c0e0003041019101e206c03100341448203950710480061f0346070040182e0744c8280041c0360b0162030710000030390001d03820901402d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 70177637 1250 70176387 70176389
    0x30d0f06080f010501080c0f0315040606030b01050913030516020901080a1403120115030e1005090c0f0d020607060b090108030c15130b0c0913090b0901050c22090204 73
    0x9995151a82006100010000c00005246040c001c00095141942c0c1a60701c003406c000d00c0d8001c8035441d103908000e0b5000d0101d0449544840d6031104540380034030703090b00240050300080b180f8442e000c0c00070803141030405c0e40034421400200c1c101404071540d1000e90b02c9400040d6602d80000c1c42c14980d07001600c44011301e40c000e021500051110141926100075840c421062880c00c55005101007200312000800041c11140c0202840b800d4125141084002d40000034200300c2d20b00c58566002100b415a03840b0030700c103422540c25140513a01040c01c01c842d202e0900c800031340c055061500400545440c10041170328030b10600300000c040d2140008212541000d030f21103c004e40010542e145810b4042c410311810900345101e414040c0b40411404100300c1d0000c41c080d054140180000c2c0305071017008200c80342c0b414000c100a10002c00e0030021409031407400000c41c0c0642e0ba00010a944950500506004000b0b52104600b04200002c4043c01000f170150602c0d040400010002001102840248 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 70178887 1250 70177637 70177661
    0x515030d030e12070201080403050a170721020306010c02090604020c011404050114010b030f1e10060e0a0605190306030b0c09010f02061015050c010f020408060109050f010314030d 79
    0x8200e00b00319000311424020507035900910034404220020060780d12841003584140d050400a4840d02c0f03540d411103100301540e42d41003002440d41c05000a10ba0010f420703100c414440d00140700502c23980f1900c001a4001507a0a03404a10300703110040051801e03000c0d25610050140c401803c141c118024030b401d65242012a0021030b000c00103000910030280202050404100300c2e8030b6042d494040450100c1c4001030811450203480f00200707484074a64000c1000146e0314003810030311800c01c5044465840920310070a80414081d031103061003801c0c0400007004880280d00c605040a150b40a807a482e204c4c0b2100f041c2c00c0680c2c401e0080001940001d0f080e0140402d250a0340d140d100d864005031003481c070900c0745815544000704020181100422020a2351032600c006001503042134416940d501860390368035415424035409074180301040e0b020300200c400032400c541440e60395025100c101c900c07d80e0741c031041a903038000610204240c07882d1259408001001c5a1601d419070036100c040b1071081d2006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 70180137 1250 70178887 70178891
    0xd1d0d0206040e0f090601060905010c030c02030d020610090e03030a0b0a030b0406062303060a0b0301090f05030712210c20060601020609010c02060406050405160303090f09060303020a060515030d03 87
    0xc03040f400b04580135260300800441c001e24455042160140c00d1201c44c6c42094100400940f019080520806d04450707015409001c0b01c2c10300c2c5110801a403100c0382200c100780c0711100664000382007182400703006403110022014628503103c034020796014280c001405900440d81d0140080003607030b00c030704403071103107001e060001589800d052000b403030001e41030104a120340f070315400c9040310780d8040b4805810103202d910020b041415100440d02508204101038518030a8000140900a0120040500303d1254242ca80d2010710301005842a04640c04d10542003a04103180402056059005480240d00c40c1400c5448031030203144a640d000d04d011010340740e50444014800b86580400580d80c11028401c004e00c4000313940a80256145402403029111035107800104052003801d0111031030071000c1c0100c038a5840c1e03c03400c1c0034107800c4080c45041013804030140d00143c119114030880080da580f550181c0300020060300c8640207008007800d48070200d0b110080070740d990b0340c0400c080720096030380d5100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 70181387 1250 70180137 70180141
    0x1110c0a1104020903060a05180d0c0b0702150f0703020d0204090e060129131508010305060c0304030c140f030a0e0a0e06030a03140f0a0e030f0d1d0d0206040e 70
    0x2201c07045100e541801d00641c01030101c86003554000c07402e69803164001a0000b00d56407014040c01200301c0c207000c0340c0440c0c0200e03030a00380c6050f03210980202690250b8002e01c80e549070704034102da444050000e0b64412150303900204050300c203070b050226002100c51801504111000105500320f900c164040b100d003d6460b540c680744100d080c040d070380c0117154102d01d9034201d00c02028207400d9800641412007440741d000030b246002204124407040034001009280804490110014000340402c0c041a00c561154000041c0284207041c01c4034852035040d82d0341c44243c0c01c075a0303d0081c246500e507170460381c0d030080601c0e01c3e0032204104050301c0c400c03c19540d512401c08030f440502c0030554694200f40440110700080006507100050328102c1650301d807405a40888101120804038042c101d40410020400140c41d8242da80c0070043c900c0c054812015111100007a030702c0c00d03950349940c0383c0d58000b04090015505003080c1c240f10501c5006005407002210002c0d507400131f15142d0107600440c0034002082e00b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 70182637 1250 70181387 70181393
    0x203090a0e251b03030603080d022203050a0f1112030d06050102010b1c0c120f0c052211090a080d020f030406140f0d02031003110406050d02100201110c0a 68
    0x81800300841040b58946207503030115401010f02000c0d50494200400d80d44480f000c0601c01d9000c10002e54008081c0c40e2126002e0503408007940c000c2c541c07041d56400c0d03608130210714040e400040f0210b1781d10400800424003550340e1180180d070b895400307a41d1520480e0401c80e0540b12040d05401060006e00070390764a110117042d110480d02550041c90440e0700d8000c5492a603102d102049014800e80044203061110070702c1d009400b0340030346e08924180c0512000d0541080301003014288028441c00b060900c0d42d468100740200980e03200c01005545070351505007246860903920805821010000c0e00385000c50030808680785c4a81130388108080c0d400a00b0100e01e250381800a040d11280389000345103480c2c901980100f0380c454072040801800000585009402c2400040311420070110900355220718100e00c04e0000c4003c0762005580101c4480c16002661030148225019554001c03d8001d41f004e051702400388071031200200c0741c00d640d03860311034440b5001c404005c4c00114151000500d0042c00f54a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 70183887 1250 70182637 70182661
    0x4140a030e0307060905010912060e1e1002030708040b04021201020a09030b0106050703141606090501050a0506040510030308092d120a170601120c021e0703020306040f030203090a0e 80
    0x1030f01100400983c240300f401b107aa440800b4404444049916100440e141e05104004100c0c14064440301d10681226200e048040b00c0b8600070100f09030150368074100c03001c440c0010707840304688510000756201c000800080203c10602c0c1c10900140c01069031410403c2d81c0c034226488141c604010034480070ac10410000b88914035030162201d440d04908200450ba00070301070714407444d4144091200418500c00e503085520030800901c1d04140e0030b00c40903190741403042c001e080941700c030b5800e90b00300000114281003900070031b4002d032501103100500c580365480c102c5040c42c0c0a400c1800398002d10000340d9412005075407550304000340249404094440c04c00c440e01c1c1c003982e03090403502420b00740400d1810940102e030313601c03030180003081604541d41c5d503600403201c100b118002c3d100071034545121200306582c00244400c00002118100c802807078121a03a0342eaa4080e07101c004d50650040c40007800090440b03404a0310f0380c8c40703401142c2c20f1822400c0040d801ea078017900070044d0301e1108400c010540040d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 70185137 1250 70183887 70183889
    0xb090c04030c1a0a0518060409020a080f040305090f031002131d04051902030a0609050c03010c0e0307091104171f0902010e120a05061003140601060c0b04140a030e0307 74
    0x21041c882e400f0701c41c80f2030b4607a0090441080900c03a02003200740840315000c0843c804030304000d00d0542c0c1d4685601c0d0100007034101c881c0c0600010b04000005500030b1920013405d01594158030355600305802107082185030b1300c40e42e41c0c4a8050084c6403d2221140950014091941e0841301400402d410940350020b07081c40150711542200311002804081840440d5084a080c2401800601c80c0c1355400403a00c0c010494400500003031403e1f1500c803c3c081c0104120724402001c900030f01840c49a04004c481c0300c2a990007407a81070700010403c10861072282e01402201b46550505820039035200f1011101b44066400c810305a0070500c0840c80c050303400700e8100c042085514042000910350b8000903d02541a460b49028030b0902106901514040200240d085d5000c0b04035941441c21100044d2641011700c8112040501c0300c1c009154040046078080c16124981e4030b0ba00480307540d443d000030181c8081d00c03e5400400401c88121484800d10012900c07038003949400c98030400400901d894240d41b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 70186387 1250 70185137 70185149
    0x102030a0b10180504020901050403020603040605101703030a050901180614010603020301140d02030f01180203070b041a03040c03080403050d09090c050a11010f05040b010e010603060e0403030f0b090c04030c 91
    0x2902103c8650410a403054009440c0b007a01c0058403014001d0060f612445990001b0398058404410001080050b40005219806850040d2540340d074485482011201c460798490560700107200040c030b00e4040d68417841d40300d5441400400c124403e80b0000d50540d00c212001e0300c000d502e40040c807040340d0b081441c813401010700d46421132a41d854043c150366481080088240f0804000c503404095540801203105650940002001920450540c0948452514000320301a0107606030003c0c502e41410103035011112215015040800003642801b01a030004201f107424861031040440820680005040990b104078002c101056001401070120b80c0660b10465056041260740c0028540c0441030724501c4071142000c003404164030100354050910a0008407040d4a860104424030011901d503030704032402c88009546a0362110702c1103040d503843d4013410603036560803008030b0002072080e0b200e0f03104a288014005040900c203000103035064010f494000112601180c20310901c042c0c40d4400d801001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 70187637 1250 70186387 70186397
    0xf0a03051b0703050c01060b040f050312090108130819030c0e030703020a051021090212030301120308060111010c0503010503012d090203030d0c05072a050405180102030a0b10 77
    0x100c12101d91807207201c0c00400a00b0400e0124140350b030780a003500044c001c0c00344261003079140c0d500c49031200d444181238841c00b842817207407003458450704248200b1a02e6400e410780d200300003666501c2c0300d60001101c2d0381085685210400c8800c0551281c100820803c00c0c03566400b00300017038822002007161402c03481c028442d800142040005a40d488051411034005a44405c16004408003c0c1c032a40c80e007040c031000340ca1a0201064681015a01003050544220b40c1c3d00121584180c080d60751f0b020074000d04002d406540c88030750109005129540d80301a05240c410300040b070300f403030f82401e4a03005d805203004a9001301c014082c81c03900f030082000b50281a2400c580200d940380f000301200c0c003400485c03008155160103140c103644052003207820260400750306120750803282100800c20b03886964103991905c004030105010f6030321b038a40da0300501c0004200c0c2190500340002c010050a0103080924140000181e40c8860032082c00614818100040300003032340707103541c03041c400c07800400700f141340800c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 70188887 1250 70187637 70187671
    0x2010e0108190b0301020409060e010509100806010513021b0a050f030f1207050c0a0b06092d0a060801090c15050a14090102071214070602010506030c01110109080f0a0305 75
    0x2c811990440000044080c04a032128009001c0f034024810f0750403030b8640e9404d1000c007196031420726085030304859050302d84510075610601000315031107660043c1106034107c140100702ea0300d814074410010005514006140c2641d0040107603038134a2562401c0100d402c200300c0e0509000c0280049055000c00340051031400060b41342d841000e11445e00b01da00d01030701000c0403541003881001070301c451040740301c2100c440a06500344400581c2048903035501c901c5003400040c00c0268003510810303903d400303404d21100c544001c0580c001040d00c000c20801d16555260750000f0048000d01664400300e00590001720000d08008084101140b40040340042c010b00b041120b6100d075000c6102c0040400c05c840e10b035112405078004034102034542c0d200c00040c101081c0010144804081709078042c440c3d00b8200d900241d503604040c0e0a8500450b04644e140d00001581c454550184038149408664280000380601e80c0382d4541c4629044103904850303058000c29800c12480d01445500d42005080501ea40f1074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 70190137 1250 70188887 70188901
    0xf020108070e03031b160303271203050d15090204031a070905061e0f0a030c09030302190609050d030b190f261f060501030b0604050607140d090302010e0108 69
    0x80c4640014103480010b44004010340d05c80a0000c01000304241458811a958170300b8000c00b0340f48000600040059519401d07581551035100400c12030b4013071100030042903020786040d24103030130001c83c2e1003a42c7e884400c0602c18001d6290f0301e0001d010100d4005031124110b003001000d0b110301c051140e29a401040500c4545a000176850f021564121045540c82e40714406007911442908608001c203880849c07148861404000074180082099804010a07001e00790100e40038403580c8405030250300460740007058118860341b0540b2183c020140490621b50540d00d01e4503103c1c0180d038040000740c0e541c90713139041490a46881c00701c960480305400b254505001d800464034540b841140880074040d00b041003000000b104504031480c0c0b00044e18203258202c0040030003408410165408540b0703080011030b1960081c414803007100005403038503003080e050009214056001640c141d50b400340e07030300200000003005c0010004e002c29a40c0e6113000309141d0310000d8441e1902c00e1076a03040c05a080104146 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 70191387 1250 70190137 70190143
    0xa02220602060a111305120a20150304030e010503070306080a080a030e0f0d030c120e0c0301050a020a0804080706060f1202041103040f0b041b03080304150207020105070b0c040b070f020108070e03 86
    0x990306e04a13006080c000300c4000c41882d0034114140100300ca002e510350400d1064114560103500340096640100c5000b601e49030f2512480100c40040208403000d800c14001c0d40700f00c025560101c0941000035906440b9a085454840244001c4400d00c0001030356250150b8140910181c2c43c071024002e2a4003c03601e0b900a40b14210710440748101070380c540d038a50302c0c107104000c2c18a8000d07a1100030088003440c00c00d440e0b00c441d000318010380a90308040c0401c01c407130058401ca503100c0f0041d03a6006800d0326039640301e541e55403024905031006510740d007010658150f4490024024045c1c14130058400c80e02d44184406d5076040442a0441d020a00421001c0b9401400301e0100701c1c1c0c410258206075455140500411845c0301218800d10305040000c0200310059000b0742c080c0340205a4446485541044030060703116050000380043c0081c015040042d02c00e00007581c000100b907039203608160b1100c800b40d0b10358000c520290382e072124100b8020150350304802d801c0d410980c2480c00c0d60881a0702004aa5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 70192637 1250 70191387 70191389
    0xb0303040b031603020f0f190f0c0206030a1413110f210703080d0213080601030507060c14010507030b0f01020105010506030c07060b030118050618060a02220602060a1113 75
    0x1203c3d004516002d00540b01e50304840c501030303140d010b15442c0c050101c844100b40c4c020210b00d030072001020601242e818094048580000265662181407413a190b0901c03200350005000307011a40e4840101c408142401441d2504c6240b000c02c0e1060348840d141441000d01000b0f44200d030282400501c0b210550301c40b030380443c040c00000f4144803003c041c4000310350b02d041c0c80350340007038400d40011440041181051300100b400f48840d0040394502601c0c0c040d95901c4030020700c0020103640c00300c5810090319015070301e8003400394024100340f10281100e4030341d1800d40b14100d60789000203540d9907290903185000f8402080e01d09007031008000d07540c10803000c21f18621002c3c0111940c0400402e1200c10001d040c2c11120030f40c0d402400038001c40c400300380c0c204200d150000d0201d82c9405000f001844150380d0300003512203114a80010a00c64942140c0701c8000d5024110248078071041e0701c4071b81c400c0000340060200400907035005000611300100d410f402c454000801c02e5080f4802c102c242c215482d5518410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 70193887 1250 70192637 70192651
    0xc04140105030405030702090c0a11010b0303120c0c060103050c0a080c0102060103021201020705010f02070b0721050709081f0e0106050a03020616020a0e10090507120b060f0403050304090b0303040b03 88
    0x1a07a980f01d600b0814a0f5000e0b4610080d0302800308010894030401d040054003808043e5107440c030780080c80c4c0821a09817102c2d00c0c507403901a807041c4070788601001c940c401d85030090040c41009203000c4100380e400c3d0a041c400d030410f88041e40110400c0d041030424070303032a20061451313602a1444c003241100003034440c00c040c4000382c0f01e1a084d02e92003400c003400f94100c0b50303641d602500801000309072090f40000394012100c141c07200300045000901e0a070044038a640b500d01d50070340c2610781e0b41c0d4100500380144000340c1100100701c291480411210410000300c1d80c0c001140b904159a1341081c1c4c621015202100e91900c900d074107004080003213407110809041500d40c1240c4103a10b550014102c8014001c200c000179501101e9280001002403117014014000c0c0700c1c1d40500c2c4480d07519030003007400740e4100383c0e440b000103040b00c1d8040c3d8104203550301a420940000b0500752074800000c100c41c046410a8006480c19000081c0400103d030301481003841103d41a0095030504d4503000c1e404025010040c912 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 70195137 1250 70193887 70193897
    0x60f080c012019141902030d020105060a03031103120f0a0b03070612020d0e07030f03020106050d0201080a020904090503030a0c110a0209010608070c050109120f030e03030105120a0c0e06090c041401 87
    0x3000402c040d40d043e84a05104c0c90341114101d0380301d00c025150403d00600164000d00481c20200803451060040740d01c90b4001411041e403803483c5590807030300644100c500c102540800e2084088100d08888074074011407009801c10401e041c0206254100d80001e406a407203907010003000c210aa03009025a0f6044140d0680185c03501c03a017580c85c1c03003e412600c00f0b450b401d000d4000017108004044000c03054050180d03000300710781c50302c1e0401d000225020160280c04201108000b546072000ca80042c5500c4034043c0006c22011040c1d42d907546560400d6070035810164031030700c0c800181580186004c0c00054600010580380c882c98000c1100c015041c01081c04002d45180090121750080822071846a4840c008110012a50400300e180301c01c1041c0540000310115013116031035104c0c1c007032500702c202c00da405145142d1a080400c40407000529241e520345c0118541c1c500410702000781840207005100e90707400540381420401010040060008041780024041404003180380c2c010711110003020700305 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 70196387 1250 70195137 70195183
    0x60d0201090b090f030f0a1403040602030d1a090403050c12030609060f0a12060204060e011d0f03010f15140108040309030308040305070f05070e1e06090703060f080c0120 75
    0x1304002d00948a211a0103103c4c0c2c078901c030710142000030208591405803481a520410000140352039200e07a22641c03006900030702c8042c6801104c0d42c003242003622016180e1030700524000c041031180404940c140c0100700c000c50610355214052100310555024908000c1c074514108001030b282d020083d000c1402604000e030090138648891450101804456500c1e500c5d0350103918080020b0342c014010100085d60750720483d600da501a000300031020044021000202e103240c0c09018901142c500083d03032544d21542c0910b0b14620a20440e42003404a1422030800e90810070802800f802e010501c0f410840302c68204400700b136006848000b584d40c540741006080e151030030101c0d034a0150180280000c81d1801140003002070024040c411114021800303005941c46894619a08410b6120300785c0d00005007001460b10302e0721000da07603070006440c1030008100d502c0e8080b40c070100e00f031078028542c0e0764402c8031940d01a43e00a0181040b4451280301d02c00302404465180b91503407404650360401d1301031561 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 70197637 1250 70196387 70196389
    0xe120714190302160312080c16030903020a05010f050403080c01020f0309010203072a03030f020c07122f13090b070e090a020a0905090406060302030123060d0201090b09 74
    0x3664408994140c11900c0388450069100600c40404504038054400c202d51010540712000c111811241c000f807803400c0603008481c0aa41c02040140036002c0402c080049540400c1e11001802405000ba6546030109055205000303070501c141e0441030511469024117501c0c01c1d8004221819654041d21013034070b074000440c04a01902610300321404140b008410041460703015409144a2081030741c641081c8002d5011100152074640388050f00d4254014081c1c000c00e000b0b400948045440c83c0d80107103000480a0114107045c020b802ca20303e44c4810121036000c1c0550f060040b00c24128503a20080f0032860030321012064031744c12515500811078100101c04000103a442803112a40000b40d07811b0625109030014602280315520314403c071035403030125001900501c240e41040401b170726507160950501e8100804030034020706c21a10345883d2072010006071000e00400305000342c03035140c50300078100d40719052541640041129015440842201c8c02607a4007604003030072101030350f1000c0d0399003107118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 70198887 1250 70197637 70197653
    0x3060616080408030f0702030610060f05070507050a0608011d0601020703060c0c020405010b04090c140409111c020306041107120302030a0e060112023303060406090c021f0e1207 78
    0x1502000c0343e8000441c8180c1140352020003840c10f903108909854165031019850106003003d8040d500000740201c105281241c040e000400160740504212045260ba500008500c0d00ca0b41d0890000500c00304c004100000031068200c10032080b81c500001e01c0d1030300b0701c0000e44d81c541d01e00c0050505901c030105800d0039805007011600c3c294028205002560312812000f0040c0d02501c1580081490310100b506a036200d4412108081c420aa013103160614140c0300001030b240110034a0230650082020103419400c07010312100309070024002580364a4050104421550185141d11003800b00b0408000014510035000740b8850540c1070041c0c4903107a404a10b00103007071005000640703109030000860010310350b4005940b176920858088201d641044101c82d603083d048101040400814200000042c1e401e40196511440c090800200c40e40d80d04401402e940d24483c038140541c114080000300640101c2c0d0b60031508064580600101c0041e8880d55580d01540c01c0d0074450380c1e4003140e031300704000ea0300c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 70200137 1250 70198887 70198889
    0x10e010e0d021c0827010e07060c020108040b0423010b01020106051807031d030f0304020906040603020d060b010c0f0f110103060609051c0204022b0b0f120c09070903020411030606160804 82
    0x78480c5c010744070980100c014000c0a0b444401240d42c46521000034030750703100e02a80c0880e1503041c0d480e699540c481d0341e01c60903240f1000d0001c840030418041c40c0741d40824407091800d00040e00e0800800c2c2408100006801c40da290380100e40144107440d109412031401c840c600360081c4440c075000408101c5e4208410b00030b03d024002818070300000600103070020810000e14003403030080340c11406a440344810030081b60010b20009411084408841020540c0c42c0c0c00ba403c80c44042c1840b5245a001c0d40d40d1403001e06a20200310303025020740015105104c811040022004428207080090301d0030f200b4050700c011800c4c401c0900c41e441020100c821011103681065680d9805001503454010215000310740191600fa91903003042c600302c907050032010390300401040c5007002d08600c20349220701d81800240c030610800c40b1164880d1041401041d2600b010880c4140d41c25510b07c1201d40c00c1d44100300c00d58031002000b500c2200b090003807049698800080310149010100788080e20001464004201d000c0c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 70201387 1250 70200137 70200181
    0xf0f03150b0703140304032c09041505090a0507120206190806030d020a030509010e0d170c0c0415060e01021002040e0604060b03040f0605060f03010e010e0d021c08 72
    0x452800080e64140d420080c0001e90f1007601c403640c40707141c24101c104082c00111405400144124140221044c40385204039a40f018104488500903201011070320720b00c0d0545040703a880f1400103510b2405000380c031415401502c0c2c6000741526040984480b55924010f000740d4012210480c07210b01150350b020101e459110700c0070800141030404078000340054004079040c83c00707400703080010744100344003080d10104640d05840b503508007403811f001154203080210104c0d0300100380c000d01002084c80c0e014820100080c00c0380c40ca541c0e0101002442c200a5501d0840d401b0364140700c2c042e007900070300c44070407810f03102649000b2041c1d4298400403441c05010910030032070644005400b02d40302080f2441503100303480642c0c1c02e204060b510f0381c40d91142d1204890140001190710030700c2c0e00241c040e03003140d9006000241021070024038040044d003114424418030815a54600729a425400280240c0400c041980007a0080b0940031041c410004000011501040189000210705080c0400c4201048231 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 70202637 1250 70201387 70201421
    0x9010819022811030313060507030603020607050d030f060b0301140415080606011b080a030908043501020f0a0c062c07150c06020c010e01050c1309020304030f0f03 72
    0xe6400003800201c0980b49500e00014146040c07011400e00010880340070300303029000700d00d03070400a48910006110141404d41010384509000000d6030794031019101880c0110040d068540204201804888a9902d40031089045c100100044440c0c081640d0450b030f500000c2c1140400c3c8840040c0040164038400510b100200401181681e40068a1440340000382c03241c0c0601351080300c02070103480380d121005000020400804040078401c2e001208424801d02e43c0030309140d1101e44c07440030a5180032654a83c0800440014ac0e0701582c03011400c04000f103000214078201140040711428400c40e910740042c0440002d01c03804100e0254064005c0e4441440800210199450201200d032a02540070171030b44140b60011428168502030309000c154592908000c6503e681e5821003e50801c81604d4255541e401a500d030294007802650710400c841350304507070b4401c0034003820004020650803c03a80148184104800240c10003031044400c0c005040284118800304003c03005448001d1903050f6000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 70203887 1250 70202637 70202677
    0x10020706140115032301031b09020309160b0c0c0d0c0b07080c0d03140115030f0606080907090902030c0906030c15190201050910020c1627020901081902 67
    0x3041c040c40a485540f529078091211075242d2210450700030190307a02d410310404140c010030000300744950340c401e000c60035044030820310707598818003040f0381017103c0600d11a00b080a040b580301c0c40e01c90b420005018000c20050501940c0016190344490360b01c8001d000e880e00203013100500820041c0140101030701d4880a948403030926103840180c20083d0b22800034800c10503485000b9000f800703110740907145554801074584c6070090000e00c0030400840207013490350b240d43d4200d41c00d80d103001d4440234107003645405021341449011680780c00038551000e5229031800200c1c0c00141da01244951442e241243d00540740d0301c0b40c00c0040d040c40040c01c0403d0b03206488011500303115042d40041c00203203403203501c01c041000b040b00c81603099800480d00014580c0001c010103650315081d0303019180b83c80c9107400b21581c0d0051508212070900050300030b0601540c0301c00000c0c0c40000303080c5603250b400301320803000d60a00108400107089441c01404081605425520000701c40302c40c1d1b41620280307003103403006010721 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 70205137 1250 70203887 70203899
    0x50a020a17090109050405062b0c0801050709050a0e161709010914010204030c05190f030b0109060f1412010e0312190c08040f0512040605030f0106080603100207061401 74
    0x10b51155040764045011000300043c1ca290500c1118401c171000303000488001c480e206039003074007a40030040c9038000704503038840b0000c10300f81d00341c00000d400440000200780c28400f4026110001c282d00181c815094400140201c4040b242a02c0d0442c07444c0b010150710291103003050b07600f5140c1d1020011031007959000c000d4121015002192001d014008002c61040741518040c00e07131080d4000a800301000010401440c02c115003031143e0400c041c0400d00d445515501c420f40d50f101e2661040d114032184500601078a44107100303020007031100c1c2095a580c0fa2030068000741d03224103000311031b2045c030007090f00c8048100207420001c040000481501d80c0e0b2914202000d0181c40b090300c008a0ba40c00f40c41c02a00300001c1c3e4450710b0603030300c0680c072400040c0e5207560f038491295040c002c0c1103c51380102c2032042c00410007040039001420050b1a42500e0303182482c00f00d281113005070b00000070030840c102800681d490102d02c80c1c031000010080907039145814100035011b42808020500078040c1c0100000b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 70206387 1250 70205137 70205183
    0xa030b01091716060e0d03080406020408010e0d18031707020a0e07050714150c0705120a0c051b060f2506021306030b011209020111010905010b0f030304030c06050a020a 74
    0x860400b40f10001c0d401074440c0d07000c9440c2070ba00101030f42c000113a1503408003c24012180c03564403511a400241c541521082c1c1182907400140f40100310b07034881100c0c0401c2540040710303230710800e5032000707031852092840c5c550b4165200b9030703641d8426150001801d0b40a40d15115024030142103410794015041c1000e06004040c1d511158041e544c00c20340c0250030026445c041403900b201590240c0107132140d11006600403003507018200c200d031144507203004603c441d1101000340208260355251040b03594a141401030030400c1c07206601c10b1460302018140e4059581a0030f880000c02032502ca240c0b100b48039280e80e049810594805042d0800d100c07044010000c490300100280c5070b20080620301d0701d5035200c0c10340548080413802030104089000c444c0b03620136642d01c4810605e00500d00256101c110510345401c5809040007922141d440e00c00c00d02080c1451080001b42860a40c0294070301440c540f1140034165039400f40c5810454002800c51807a442003262442da81d82002040c40e442501c080c1d90f080c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 70207637 1250 70206387 70206403
    0x170a060509010e0d0815010c2a0e10090f0207020102070e06030f07080f150f0406150e0f10050f13050403090e0708010e01050901050105070303091e050102030f01050904020102030a030b010917 84
    0x4140d86c000071000710300354804c12060b180903502602640c0c4803840c91440350402071500c054043c24401d03100300024035807500c81c0501d01980d032150101e08034909104030102695100d100400ca0f0500402442c00142d03400124101100d40441c520f1110b030700d0f490000782c2031800031800c0400520411a0100300514040303407141e241c902060441d0798901c000c07030705c1c400f014204444500c003204a6000050200700c16130814500544021220b17680c070703621601d80700d80c01036007903ca080343c0480ca4004c00604c00c4042c2c44802c0644400c455103070501904c0c00000b81c1130740c00c43c010448115101c4020408150041d21424090a191814a05546040030f07000749181003d12031500c0c0060918000212401c0c881c00705810380b08181e54851400200d0b03141034014011001003210b03607211900c240711b0004032081000c80307181c0c86803001607500c2c148402500d001d800103801061103030484105000060b0b800000f1200d0040d42410081541490500103803003000700380d4805c0c120040f800e9111242c3e410701140d0b0744 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 70208887 1250 70207637 70207651
    0x4080f0a0e1002190b0627060a0e10050105090604030c0315050f1005040c0905040507030b090928060f0213030b090a0210111c0206070207170a060509010e0d08 70
    0x42d5000da6241d0403682c41c0080e07000320f1280b42d80751914a0104010b821400e500c0b15000d00007103900040401d031000c1f8011003c0c0c41040680350041409614545010000c0c0109a50020f45074142400c10014400455134441d0905215000035660801e4403400300b5203008641144044075007641d2410204940529080441d005601d071600082d403400e00700c691fa0380036066000c00d820b03030360781014184002060f224445200780b08000c000083d050380c030380c090700b403080350703165000f040741c41d400c0c2c003406042031001e007000d049500402c010011906505d00072030402103094080d04803044490901030000c00f000407a01c2c01070381c000a0740702d80b1300c8000d81100d811244180c841402d16590007540c29296006004001c0d40240782c0b4508028a80c070a040140341400314506035003044041580102c2c00111084401025820000070044240d1301405a20000c04a140c20710300c1108403058800c3e1601030301100203012940d00c0c004165029801d40c0030074140c1d480c50341240d05800101c580a004184111400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 70210137 1250 70208887 70208899
    0x406030c0f0f1512021207050c1b060d150e040b040212010e06060f0301060e190617280b0f0a06050103020c100e0a02060403080a02011a030309040504080f0a0e 70
    0x2a15201030342c400b40448141d202c400051092083c0c0c1120800c1d203803204948400e40a0011104205140203d02d005405585840c1d682d000081040c42c20301c40c80003401c0000d4900141c1d010115120002103a84407008014009494040c0000b04100380005c2e801a03c202c05044081000304111443c10303d00550081300c081501068444010782a601000103107500d40d000640807800509140d150b0600d0a0310050000c81c40340d850301f0242d6035503901207400800c1c10408038001040031411f0302c94440600703141000410f090024a021070707514040041425079000c5400800d48060040000001c1d009a01444030103050401400c01034606009986041d100e519180c03001582c1d41c045d20865001e42c1d1000068000c4408000c51030b00242048640c80360f00b402003180c1c0400580d07800d402003000e1407040e55120780310542d80100a0840c0c2000c10b01d181800c0e44520940e4003581d00009841c10100b044501161664880c1b40000c1d09000301030003900c2c404000324801000c260402c0c0f4082d40154140c0d42 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 70211387 1250 70210137 70210139
    0x1508040201090e0405211c0209040b1219080d0609020d0608010606090b090d0503070b1b0306060f090f031c0e0d08090d211e0215070c0606050406030c0f 67
    0x90450541038030000d00607484a003e5a02e440091b024106da501d1729096000e0810914860340d00440560b201115840c13907000512403060b103402d109100302d0a405655103003140301c039401b01c1c030f41c0e070b0360324103020403010641c0c031564800c010f403503000c4580644203aa414400b56541d10000c5003e5080000304003070f03143c03d000021840a01c140304403000c88809a0700c02017100c0c40d200c0c40001950003030740c901d600011803440520101c0c008000601c0040d1244207824010700d0b00d4401488a8010418840415003041082c486150741d04002d4902100712010b0080d5100f040d4000112030045010030941c050050729401a0511405080c0079155030b8a41c07107507070307848601c030b02000f0036030828150081401e4800e0010315000c1c20001d41445115200e09103003260f00314003501c070301484154560928000340741004218180390000d0041c4020003403500042100c41c0035140c10381e045001c0103240104010b5080340c203a05002d9a034118030001c09000c0c104002c0b8035280d080075941c0052034002c10009040c030a41c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 70212637 1250 70211387 70211399
    0x14010912080a051b0a0c0201020c0402030c36090a0912020d230a0e0102100e0304090605120a03030c02031209010204050411040b07080702270708060a08060411010306150804020109 79
    0xc1d24068028034060828a800792049046c3e94540b400801a81144070700d0101080075100ea01c0118000d4840810300360f00c0307007943c440c0009491070030789040410018034a81071080c941811460034051030f08903240041a55a01e150b0300040094100242c41480100803a4800f2030f004151400ea48a0316039a030001d000700d00b003204003055114010002c2c100410001d105000780b02d02d240d036442000c1441075800001d150304409090700c240d071080092641001408110b036001500c034910040c40180d03001088550b000b00802c4c1c940c140001d01606050312035034103000c2e451082c411580544500040400e00d800c0c0310494500075081809020b02840c54018055140c4200406403001c44e5007003103070180703000015a90040c0700d800180089800000e09065084480310101ca03080381449030102c0c035a0349240035400140120300190501b405801d24a01c240b0600d10041605507015400100c001140311805c401200140940d900c041d04942c2806580c0c1c0701d4542c0300c079a10303005034000d98807046040c0e00d0700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 70213887 1250 70212637 70212661
    0x40507020705010e04050406020c03040b0418050c030a0b0325080c060301030807121b080d06060311040306090f0b0103050d0809011506081005031606030509060601080414010912080a05 81
    0xb0080300e0100703c0b00b00c0040034614164000c690b01501c04c0c03070094240340d020000549140c104d03070030004109001203400e110120041400100d01c0d102c885c0d041c049401d113000f4104440c440680000301080d111000d403050f50300c0400c60341c0200d5010004c003981441c0c10424110300c015482c0142000c03806a08030264452600e4019030b816660003014480c5000d4803070b55500c0e000c900c0e090740b0105120042e42102c1455000f0328644d00350783d02804185588100d4692003030100e45c0340c0c0d040351041c9490400b8000d40400030700113942c01d41c1c0c1e02480026162501c0d040030f204090f40000010020303201800080708220b004109540ca05c01c240d11030b045141c40f0f12400a003652402d40700e001c1214400c4104004a611900c241394000b10318803152142162220701003410014002c43e0480100b202c1d200400241c0d50501c641940860700328040e28860a1280000380700c888098070260860f9001d2600c0a25044298000380d8255440803043e0344840105201a0000008542c400107840c545030005034002529 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 70215137 1250 70213887 70213889
    0x6090102091503090a050d090303080f0103031b11060f130b030403080402011d03070308190309080909100b1206090f04050705130609110304050c030a080f03330405070207 75
    0x24050018244880c0940d251a000105180041e1117613400300b001043c010300c180c1c90456880d59a905c10035081d414042d00c2404054490f03100c51550100410102c0e0b8441546150341402d00d1854048031034600700058807207810010151700450003e06c108501501e08001c0c00400d046451810481c0c3c0c0d6280d82d001c46010031074000d07000c54004400a401580706402d88198031300b41c0004d400c004060b0f000428a41801c076042214800b800141c1611141018155029004814501804040415942c1685601a108a0502a000e1000401c981d158418550005800382c082c00d41c0d1108100588046c55a04c240c0d4074501070f40d0007001083c51244106400d9206039008401040070610309001d02ca950394035540c030b1440d115558200420320040501512070101c404405440c0c9034103060400e81d0801030117090141c404e900110300307200000c01c560169442c3c4c0040c22809a1240e64105807101c1e120700c1c8510000210244a104110010120000d084000d0003648d0030270a070713500c50a0982c1c1c1c541076 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 70216387 1250 70215137 70215139
    0x519083c0d14090c1c202d1509060415020f100c030506010503131211010c0306031b061202030604200307090b0f04140a030506010f09050903090f040b19170609010209 73
    0x8900b8040094010a400f44c00342180549580c82400c4129548003a0180e041444c01100d400008070071f2071071500000041d03001001140c0f141ca400c0f807010019446108070710422070300c0042a90b02b1b1882c140244840001b601d290420f17036040c0368200543c0b100610000280a012078501804202c140d4469800d5070300c0b8a540c8c50100b030b00c2e42804d40b07441c02d170008285441402c204009180350803181081c0500c91456a0300c0e00d01090030b60641c601003048824100303c440890000da03104200d41c0768428100c0b05070f400a450016500e46503034012401400703001454052101c61181161070303280f2120000c0d4401c00c60340e0b4507441006e0301c40895400904c900d5070110640542030109008001040005200102c0c0041485201f280e40f50749680c140340090b800f0b440c51013140081005034100a000d07569001c01d0040142d860001c04d40300150f40c0352840c0302c0301c0e8065556146000455103030201c0c2d038110741c00b04101c52100e00c0e95591002c08519400d0300280810300907603000c1f91030200305000795151404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 70217637 1250 70216387 70216403
    0x1209260307090609050a0b2212030905060a02060403080405030c06102102090c0a09080d09030b09030909040b040303090510060510020f0c0402070519083c0d14090c1c 73
    0xc9404507142d5240c12000c4952681c5041c0d00140543c000c5050603d0009d10200a41c01c0c1c2c800481d0a002c0e042d04d074213031b1165018140400c41c0c61041030f0302180721a030042d03040c00c01d40480d0715241441d41c40c0d030103003040d405828442e00051081c104039009050342240d6114020900c0000c0d4103200034155514080029000410310001c0390b0103c0700c0700d000e842a8416031038064500c03540c4040a9141840c43e03803105010a1021200340b0174130440c031402a5001d0307071000003185824800004604003a5005001a007203201d2240480c0416109400c011380c05904441102c10300300380e0702c441c18014000c13841603501c22000000c1100a00780041007034100130440034003600038400c0883c02c3c0006580840c0f81100c25004000260010030305482c9442c035820300800c181074907648030300070030500d090b601c01c88612442483d070000a070b52040f40c60b115071034041010b85180c603441c0601c0103c0c041c081c003001001451814004002022034001555403100078125520811282d00700302042048035400c03009002d0038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 70218887 1250 70217637 70217639
    0x30a0c0614070204091202010b06040305030702010e01032306120d050d09060902030a0501061a09060a0c020303130b0306130b090112150603030507020906101209260307090609050a 79
    0x10780100c6480148200da01e002516110581d4001000c99070b0500e801c4402e1441440140f841035424811b00c2085d0340252400362a107415070f00c80950703078042c100000741004100c100e00a074607403090b01b100392101c5052410600080311006a0440a0f0741200d005004a00c40b15401040c940c000410190000140d2511860482da100801340500031000d0b090f2a80b40e142c0c0044001130305d041201041c000d0144000043c0c60342042111040d550700c60040c0c003413100c001d1042d0f074025550307202100c03500000380c14030954040d01840070a04602409110303007401ca106050024580782d4210086118107411542e132029010560b141c00c0481d1508441c8a0b040f01c05d100042c400103c0701c1e83c000011030b0003440407079040b0721041640000c0c0c0e0a981c0003200040e00c0800e46c2d404600f0b02d00c6810f40c02c003100300c1d011103101c459070a00420101900c680050483e07140d00000c1c0500800c5442e94aa51208641d1030380c1c2541d1180c02501c03254800d0310342c0c1000915034540003460390b110b401c8807000d4440c002d155120341 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 70220137 1250 70218887 70218899
    0xf0f020918041e030f020c011409010f031e09060e06130201080a1103070c02011b11060d090b01080c01021005040f080a020c031606030c02010203040b010504020a170a0603060506030a0c 81
    0x2018002c00488002114014002030703124aa01c12480c1e0b944030ba911910850101003009003401c1d50201880d050101580303c81720905200e20603181401020310f08002e0520364048101d02030000a109001001000c1d401039000300c8031504a0302e11580902400d102c9803042d006590b0780c85e403040b1443c80002c3c5407002500c2c0150300c6001e809800018054000c40c4c00919000b560940323a2007920701401203084920003400710350700142c5884804001c5c011403802941035454440d2000d010400c25803040c00005123100040406078002e2240940060450320780c0d684035507190313075108100e1016502620643c0f4803214404c8083c02072500c26940140840206a8256902081d64100540e81d00c190300480102990710344003004910a104038072040c040e001464010054220342e0000d1242d021079004104210109a180c01c4c0d281c11101e00f80c0f0016a168270400044030301040010f850044890004140005a2600e40040080d2800380104120380d8554800f010342d00c0e8800b1a0040c07420640e101e0400903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 70221387 1250 70220137 70220179
    0x105090606120a1b020f0c01080a020705070806040b0c040305030d110403020316150201061a0901090302091003050d03090302060f06010e06070305030a060e24040209060408010f0f0209 81
    0xc04090a42401e2082405031445034601c11101203000780c1e5596401011821408403041400542e40090510520f0301018240c8521039528039030b0501101d5408160007140c00c0d4101c4d00741907080400e0340e20041d10344400700d0312003000351000c0d122003200b040400c26100d440021035045071b9000005628065409003442c001d81144038030301d4500c9006110001c0561000d208540d4030380c2034680541c0c01117080c004000301d80e4490b60780d032104680c905031050203152200801c00200000850045840d540c07071000407904c0055076000250849614414028440700c000912001e0781d1080f01550351440554a0840c100c42481d00f010740140c0c050004105114158841d13145c00000624001e0143e146060110349141e00136181100000c5000081000700c0782103101d214094100148040303002c0c00c0032100c02d09220242442c4040c180d0f102003c0e15280d5840d80e04489200c070000d40800d8030303a9655030b03280b80200b0308541005105418604046182e600510840b4450f0a00418422a4811044440300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 70222637 1250 70221387 70221391
    0x50a150207150e0901030b0402040c051806070204020f0a020303010f080109020f0112060b03090d0809010b030705100908071212090e0c070507120b0106180303050406050c0115150e18010509 83
    0x41070100d54000d00303202d925460785070390103540a00c1f4031304854101481400102c50444071400d00300310041c4607407422024055a03020b643d0341d044035035907121400782c00010000e114941c0340c282d8a03000001d1a068294010010398121071070040d041c85542da45910b030900742d880070040254030460b04500b04c2465070085002d2882c038042e02c440050030360b490b488005410741c000e40355010140d200c4015070360f07056032180d19594001900c0b0021300c940800c0002080e0b83e41c03900d0148910612091864480180c400c40414006011050032600e219580701e0002041c2c2e01c9842064644920344108812003c3c011190003046138a2604201040d584005a003040390f01f000c101203a15010351400041c9040d03111521883c4240240c8542ca0103500d89103010b01011184001d00c624a0300b808010408290440c2c1a50100c8040f030400559a026400300d1a004222402c120460b1600291021854038102c2515104001c9603848042000c5010b80400c014070607100b140745030b030114070001484a41801e904840e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 70223887 1250 70222637 70222679
    0x140c06070305150301050405030d061d0c0306030a1b0f140307050f0109031b05091b0d0207030908030705061501180302040c170109020705060a0209010f0c030905030102040303020304050a150207 85
    0xb200341403c02c0081e003520010b03034060301c207a40040342540f40e10a251003100c0c020943c0c00c80102e4240405c1058480002009081b0b88034a030300440011101c2e1420300c91498029405440758840d1103800d2611003d481c0c2038040d10941d013041c40740129401c800540c7e210100d520090082610710b141030200f15611503401015810020790340c800000244002c00d6140d950190f1300700364042503040400340000d40c01c3c01880041c80c2444400517001035000d000c03c8540f410422503000d0382d111058101900c504000e40d2081902e8480010f00c44280a8003150302401081420390501d0700d0644403004403080141003814a0344d19031080e030100014601940440e0000601c0d04044100000d42c000209100d9000d0713019410705500001c10340100071081c4450b65000290140441c00c0c8100080000e00d58050300c1061018440020514810705010361039100003070400900035076540b40c480c0fa0082d281c0d041485030500070914080007042241c4190b0f040950b00c0781a50080001300d1604480d800480c41c41e0b0101c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 70225137 1250 70223887 70223911
    0x10c020918070e04061104050d0b0604020906030702031803061b1819060f03180b07030f0e1e0a02101404091503050d0804020907031a04020c0d140c06070305 69
    0x1c5071260002d0200341c006000c45603a070082c0d03141c1810010255500c621a800d88404200010700541c0d660281a09541d600300020103200c1d80c50b200420020312074007448641c08440072040020096000001705003040e10950403c81d42da03c1601030645c2c0c1c3c1800d407003036100d021200c0c60714161a20f07000007400003031f8010300031105c48000803408118030000c50b010301c07540b02d01080c206003c00c68000012030b2003155189401c00110140d52103014110740105c50003040d0990f484041400c0c14401e801480108003118010000400384900e11955144052880f8248104580c2c40d8040e840c0040b44000d10a40c026003180552040340700200d4446450301e650206e9940d041c800426441810311901825080c2c02062500c4035003542000b80c90460314074414003c00001c94200001602c075070890700c3c0c020180c0d040205081d84030400d441c40c0043d8418000390807610116541d040c529001404c2001c65400380c40382081d41321b031540d4203d13991040c1c1c4021030040e4442400f0508080c825070056522581003005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 70226387 1250 70225137 70225171
    0x6051804060e0610020601080d030207050a0215091203041d0603070e01060201050f060607150203070507200a12080703081b07060608010f09050a121e021c050405010c0209 75
    0x101200c1140d001000410840c0b020000182000d03108244210183c0c0020000740d03240040d020703030300c42c440001c240801d600032582c1d00c04c010741044200d42c0c11368001d11600307150707291804034030741c58220400183c031500f0742030400c0455080120894041d80c0b54854050b006582d10001c4240412014200b683c25110301c05001407620030842e0b4007400b80c5000e9001003000c0c10f040c45001e586c2c120141c001413166104210500001e02440c0d41c201d4407407515140941c0320340d01c040c81a6170038090544090104484942140300c200e15448038100342d60700845465454946860703a2004403944c141000704411020008000842e000b4040d407544440190000001b842810156140c10303041070714219601d41d110b44e024000307000c081c0070366440c0218440c8100108840c50301c0c1c05944040801c0301138408404210078814a034843c0c1c1003040310300c580b0310401890041041000707540e11710303403101030118449120091000da0b1207003048404503401650303031011110858007000b80c42803018129501807084001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 70227637 1250 70226387 70226389
    0x40b090c060c01050403030b1c0b0714040f150207120605090a1202010509070503161a220602070605030417090112050901090b0903030103051207060e0102070f020f1504060518 77
    0x30081080c2c0300b04038004200d6040602c0d002e810784503003100b041c0c4164800c8000d8010014142c80c0008804d4000080c0e100701e0b1201d200035a1001300b010000304004800140219210b001c080d0724100700c65130047d082e824a08800b0080344c8420060003072401881119104202052881d0000e5030005008820340700500f20bd40d41d0401003010009940780543d445e071081046141080c041c0200800b016005410f925404c20380d2240909403c2c0100002c15030319200161240080c2415200e050002003010382c4004e00780100b100caa02c9441c42008014841c0100100b0340c1446481038078002d40d4032000100060004603e00d00440d0480d00e0602c6c104002d00071070b00345108250103a84d002e8800200009120002d82c2051341071480000d0426026600c00c000400000702c0014500c100c0e107003c40b0a1070340710034003071411a0246c024a18002400c1d03002080310701c103002015501d10310251085418410096502050068144c2007440690207800180020421280602c1c01401d000f000500301644082a5030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 70228887 1250 70227637 70227649
    0x607081804022b05040b0601110c06070303150b070804050609040b0d061e05160f120204080c040b010f020a02130b030715030b01020304030b040809040609020316180b03040b090c 78
    0x1d983d1009150a802d4003241c48882481003100311a48184103014528080d101d07407020400203401203040050000c9000a0304400303004480c2044002080c1035079400d000d04008000e0315945071004c1d2240c0c40c03102c00054640c4440d045034001c6500401c140d040c07a14140400c170264110480c200d8206d80c0319070405400e9610035241c1000e86204200009644002d40e140070744012000c01040030091a0a00748680380a9416881c80350101914061025440c07440044036400707807582030b61201900105000c01c0206000c034900c0500c07541920100805041d400045401250030380c0c00c1400740c0c00405105000d82061041e2203400c500c0300d44080707580034155010a1500e4010f0340300000541862100e01d00a66150040b428018024401181801c0c1991a02e12056001410090a040000501f582a900e85070046001441841021500e80c50508400e040b03410b6806a10b00005508400341058010521215815100f801c21000d0035075403260303101d00028001500005161150714600c1420756240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 70230137 1250 70228887 70228897
    0x40809030604140f0102070c12030302191106071b03030509030c15010302030c0405010b0d02030415020304030e090106110309040b060d02030103030504030b1501120c0c0209100305100b060708180402 87
    0x703c41401c0001c56040c00c890030801c100480d0341e9180d004002c1c81c004100c0281483c000e851840160345655980c07403505900920441c00c40780300d4070740a0b03c614480560051034103d000074072881501d51030396807400c046585040d800f01c1c1450202903400300c100400e2090f805540d012a111088a140c0801070051628107070000d12200c0451340040300520460405008001d6072038000e81c2c045c841941442000351290080500640310f4941c088001800c0c02592115540181442d02c0210750f02d08141c2801000d288181c0003582c0115080c000006080c0e100d2070a840c62a4050400355051909560400018210300341106034020303414055000108a07900c02103000714844c0e203c443c2d5491540c0703442a51814024005d03d0344034901d42e00e400c0d050f41c00c2104481803a402c4500091a00e4010000b903070f1604540b80f000c0d4015205508000500d6401c07860401568001e40c100c682d068080000c2600742e81a0740381e1550444410700c45140000c2410001d8481c40304e6030703000b25048403c001d0100f003c030b07044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 70231387 1250 70230137 70230143
    0x609030216080304090b030c1f0e0d0809030c030604021309020d0210090510020c0901030609140d030501081911060705030c0d0e040c0203160305030a15090e01050709030c0302010503040809030604 86
    0x14042003180e4103480f44041b10f081c02c1d0702500511610340c0004c0c1d1003868001081c4081d80ba003030781c3d010a00344191038011a00030010041c451903000c905125125401c54220309020344500000000700f460001a411311070741e40200708000c0c0d4101c1c15258009000b003400300700e03081504440030100507500c032282d41c1411140390365a01c820a20381801c00210980050fa510195080601094190f48480d44090f054076000b4501280d090801d01c1c003ca008400030210b4083c0d8002c0c2d02c0c1c1c00c40c0c0654140c02c0641201e0054041303401e042000004907800181168001b0888032180c102c000d518140b11002d0109580158280da007845441c210440c1000c00300c20019000801c51224030900c0e14203440380f10380c045031520040d07044c00c000140c0c408030580300000140a2180100c0010410000d5800075540400000c010113032a5540700101c0000c2d11001082c0ca05550800e000241202c5c82802a03d08590f00300c032802c210245550015644d03980060400d4401c0c00040102c1801c44c0c0b41040b0090181d84 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 70232637 1250 70231387 70231393
    0x3090a02040506060a020312062205090d09080312090f0601060e030607090308092404030606090e060702030a030c0302090405090a1401051506180409200907050304060903021608 78
    0x86944100001c844000b0301e0580301e03600602002d40490382c008151280c046c40020000e105846204c0011049944801220381c5c0c2d0450491402010080341c105a01648090040303640d0f405030ba04042e2800c0403079004103210343c0e005100c90f80091700150103951700459040291603018a252449a0500308240c00480106100c1100e0301d1290a00704002c40d8488003524040b2191815070796610014810400b003103124039444441070b0113a1002c1308503104100b4650880c0c564075a036030b14124020f00f0651080456080c60300d44c00c403003005400700f61180305000d241d02852070700240c00c0c000d40051a0400140c8101642840100c065031542e120f542d0003607841100601407924689019002c0e1041c0003100c06032a410b190a00c10010320343c00089006c1c05040701d40580750003980790f0300002c08050111f61541701d4184218081404184211200c43c07420014600682182c000c0610046030001e544240010b8400c000250200e5000d910041c0d00c54800c0c03050300c0d10000162b0942e00c0c219000c3d04290300750b030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 70233887 1250 70232637 70232653
    0x210405060115090302010c020102160906080c0301020405010c02011238030106080c120307050613140610061b0b010311010216050d1205040f080106030209071d041e020309 75
    0x2020403000d801000340c1d610030880022080d100400078002440300905201140640008580c02072161003000403035071501e9200c0503910100c0d00b019145511401440307000b041805400307810180221401e490341030b11070302c23890a41c40d4011124988085c40000b49103568040100c01418130320750000b161983c8100c104031a040c81866482c805081c45241c074420380c5414800c008070400403900d03007003070f0008445520114212340f503a581144680c0700300400030f0282d0410455660020194440320b54040d8500f100c101507805070300c40d922507041c1c6d0705c4801c909080c44200103072481150b8410b5a00c0d001541d0000445181d6070b642c410b20006e030800c5410300c928924044003035904000498400c00c2604c13a0840452401d004645a40301d00c50001d8000e10380711900d400e490b400313801150000c2c0078036941e00a509a482080b180285005d02040f44110381c40f0000c074583c1885085101182100c4941d0081e110541004020040046108041c1044140c030700038051940c462000c4c7d4401d02c1d07000090001c075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 70235137 1250 70233887 70233893
    0x40b040f051813060c0c020315040b01080601061d0d05030a0801061d09040602070606080a05030d051806191104030b010801111603050a020a0b010b18040209130f022104 74
    0x41011050210490401040f403040c12140c1c2d007404041d00a0800030301021850f008032142030488001035018452204e4401c1740d0414888401d05c03c40c00f44a0792041c40c0d0300d803103a41c1e07260074081c8036030000110004c94802002d0755500d40c0d0150304c04001c0c40030485445659131181190000070001c0080382c100e6004000440e0406241642000271003008449c0303442d0a0700140c451080580043d10103640414031008102d12503000e04060300d26402100c0c1d20420078a0710907070700d82c40b02240c01070041c20200030429100c4001ea0b9152052150406407141c3ea54002840e07100903110102c2c01c0e2100d80b035054554503106244010400786008158084803503041156503403c0d03074101031400004c4078080001d13899803c1c007808807a818950624240f6664400404100d18003218000c0c003800007001c0c0800024030158120040240200e00c10054030500f00c9082000100d000d40041185c001300151548260b031181c0341e2000d182000b00200050a040c8400400c4500070807000702072000c010b0b010184014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 70236387 1250 70235137 70235149
    0xd14010b0901090b2206050d051f091e020d080307050c120f0a05030a0605090705030601030b03010c2709020f040518150d03020a0530040e1605040b040f05 68
    0x350041840034090310980001050724071122845104a2041c400307078410500985e03800080081c44010002e08200c01103091542c1c5405041c440342d40f00e00c880c8403420445426602038511019008521690800c1720140601e056041d9900c003241d1042d00800c0f60000509040051805000309035501c48d11035030404402441c1c00d081e0039002e18801070501c48050010300c100201e481405c4549003035600d03520f400e80ca490140400c0c0e00b10980c003030166010040e545500201a522543d0700343c1e800d000380500b40052500300d407440c0440c0e40002c1d100c0d03081e21049550380b00181c200b94101011603070400e80d4421060301241c21491102582410001d01000149441c0403448001401e0494256050900318203242280040c0c4c15a140558101041c11081c54020300211700303260b4110b401d88903066a44290800418421425480c800140f02109084009148107403010b45000b050761003c2512544280419034041d040c425040005c1004080b4825024801820081490355a020f01403800c280030080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 70237637 1250 70236387 70236389
    0x10c0605040309050f1905060c1005040f0308130302060105100507021c0c08060f0712180605010819051902031e0f0d0804120e04020d020705060103060f09050601140d14010b0901 78
    0x803041b043e0b03c3c280f59030b0000400340d02084440c04c0f40c2d1607a81712550603000381440035211368082d2042c609003c12090064140019103005e200782e48100241d651103c51000140b62900c4c0075005070701c010010310190030300d8501429002c80508089003448240e5000488944035452a4440d25558150321002c0040e42d00c07080014000000c040c01d800d1500ea4101003000350003d04a100704106800f2a051020380740d8800d8007007d142c0140c2c0d5900a0503401c2450203443e0030711611801d0700c140d84450107540448024003224a522030041c090344a0b03c2084196030035101401640e05016201e841300b501c2010441c0105c2d04840200540400010381c20401c2c1081d505170400c00c1484286020072001803884101d0b06001c0f00c25040c4858a054440082002406130004c0c40d81c5040c40099040144000003e01c83c1c100ca1107118240088407425000c40c0c04d03244442c0004010b42d11420050003940420b8842c0d800c0314902a000c03011392051134944188282c1e00351100a1581d42d5000620154141103074018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 70238887 1250 70237637 70237639
    0xf090306070507031e0909050906070e0402030c0a0e1f0c0b09010b0a03060c09080607021006080a0f0213110304060209090709060801060e0109030203071d01140607080306010c0605040309050f 84
    0x1d080c1034444d100500f0180305e9098240e01c04801d255119101030251940c40d000d001455401c02c0a4680001c04641d11241580c1e944041040b04000b202c051915008507803050503000802402e00300546410755500032440700050340040c00c10b009445003a038000002008040c140d540c020040344c00c0c104045060781c040c01c1a0b4140e41009820821502d4a00708041126440680000d02030380d035100c112841403081e013041115004200c1030004941e400a441c03601c0c015410300030803025943e2074083c2e80c1c644545100401c001c10314844400540303040440f19000d580b5110001c00c16140c00091103a159000310303000c83c1d4295011801d46241c3c00c1100b00c0a6120758a0305020030051300309800900580300510600c420000301080f062410791140b80014000e5a0184c100c544064582c584244a070000c03420b84401c2c91014000011100304191010758800c0c006002d8500c0c1c0000c0351281c079034a600007441e0905214580075820001442c612509104a000e03030340300007003942041304002c4062006c00d421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 70240137 1250 70238887 70238897
    0x31a040213090b010302100512070f091d0601030209011101020301090510170c0f04091704080d0c120507020d1a0403140f0301050405040f020a080c0a0b0403030e240f09030607 77
    0xc0c0c40065184480d444c1940d404407010440e0702d081042c1122640b01c3d291403a41e819400704184440d8036004880304a05903015110400c100381c031145210802c82d0900d201440c04042c800c04a441c07135011f035000300998081850800c0440c115081c185099920030381c0000d00e4103685608010b01400000a200c001d01031040036010700117501454141c1c0c42010700d4009100e10700281c0d8241072039480d94400d24603580d014102e9a40404500a052410303003142c810309c251801602e0329006491b2041c10f20440482e4014640c01a107421110304032859007001c08120703044050503d1500118021404d02c00110301840d0450845281074a0003c000c14240c0c0303070070314560380107010b449640d515030400d40381074880940b4001f420307648905008003a000c40342d070081e400c80c01c0c0d42c0c004980003c0c04108041d15000c15200441c81c9591281c044120340f15510024000411a2100801c0b07840c021301c020800828146c041d80c000c083c02c0519220603406421811320303803000000c1d1074003203040034002180e00007801c3c00c00d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 70241387 1250 70240137 70240151
    0xc1c030b0108191e0902130e03070611040f030809100207051305060612190b0a06120509010f0204080309040506240a0522050f0405041101030213031a040213 69
    0xe8005400600100380814080c000c6080d0149590304c9110300b441c2468050320340d80c1c0800c42100003000300c404164041c0e80017083c640302000c4a07000e0b0340007540b507407401186085060703220300c00106a61000c80b0059402000000303044025181d0701400713940a01000c650740c0c0e1003901088500f0258244103001d6409c0b503002013240d039403501e8070050422002a40480c00f60703655000a2014450024001100c0c0c00020038000100400b038100f094040c0d80300c1040100b0b0a01e103081045082540c8200000207845000448032000180c010350740080100001142071400036005900b40e81154000d40001d03840415510f0103407038203004094104105840c00303080c9440d1503408128120320042c0c659440b9000141c0094050700c10003c89414058070300c56004210410054a01e01c13802d5440b03000c1c440c0c000d2a103080e405150901c1020b005036444110881640e414030010340203900014482049600500c50000c0440c5070400d1300020580428400717240d52916104110750044100150300d0054a4021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 70242637 1250 70241387 70241389
    0xe120307210515030706020102030402060306010c030c050703050d030c0513030f05120c100606032306031e010b010207060504030c030209060d0203030a0905010210020c0a0803040f080c1c030b 84
    0x104494210308240340541d6008944400900781044a04541c24502c0c50141040350362402081e0003400e0b0341c001c50580340440e90b40c0108038240d0101b610040e42c028000c102140c9690700418020701c144e40300c0c0c00c1002c1d020010381c84007410030049074806d407005d4102803981c1e01500e5052140e00c00050003414403906042040c50a40030426107400000d101c10703a09140603090101c108420004184000102580c868002505a807940e0700c202c01c2c1d0004505104000c5410340c042e0003112800300c949250f81d90440301030084065054800752220740c00d03004040f03c030b8803600e07489514555104800400070584c0c0201d107000a1034180d10b5400501084814401480001d01d1000c0010850350101c80c0e04441e6101e0f0b1001814042000348025414031000402c41115608000301e2411210242c0956000c61007544038072042c0e104499101d080e680140310a5000520400e000c1c5410034000c0e004071002e410342e45da40c207401e94407a156100c650360200706209845900d01e10420070164603031400380480002c0b44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 70243887 1250 70242637 70242673
    0x609030f050c090403050408010b01031e051909140601051005070b0c1908040605060a080304120f020301060806011502010c090e18120702010e0f010504151701060905040e 75
    0x102008010089110114052060800a001034480014002c2c9018141841e01034260b43c850b10540109500707018543c0b0081d0b0081c401d9804280c05451030000745001c002d004001001c00402c0c29031400b403c080c4c03802d0340d4140c512491202900c05c84a8003003013408082a140b4148059200d140300c0d410ba244045001d80e4800140d46c000b0358840b4034003030310f52184560894240603540e01c44011318007200c03007103420584c4200000c1c001c600401c82082203403180c9092000c858400d00a110b1184d10410003004800c00141c8040343d0140030316140000340c6003950010b03003501c0c0d035a488080c0c030780c1c000401404008111400800c000f074490008101140482101610f107036180d105544450718030703000080c0203500e0150051100741c05070b0140d8650006038543c11303c0d2a002090248d0020f0031800165510341081046222200416150381d810103162407040c0f030145903440c00c10000c00c00c42c000603220b600a07154078030340078028988601c0034041c1041c09200071180c2d1800c3d48802548400c9401c0000030440c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 70245137 1250 70243887 70243889
    0x504030b0a18080c07030206030f01061b02030d0c02040f020d02030106020709090210030504050c10030c0e0109080703080319020307120506030a020f0906010c140703050c06040e061903060c020a030f090609 90
    0x4540f629440ba100e45461509110050740f010b50062000001c01203a00155903041c3d05960080d02c80c0b90b100410b07190751460b02c0c03c01a400075090b501920701c5030740041c06004150740c007e1008001050b41040c0c070941d030081e40c04c0804010f17101a000700060100940500040e03000d0300b0b03c214100b0119640d50002800c2c1c8400d140c404003495540c0b0046014450207100341070175580f0107884004180030700c0780000c3c01060704507080e1000030002121903010303610403004e40c01141c0387e0340000c01d0401e0550321462201d50000d0044527180c3c00307205800c100c24041d4000f46104940d651201c507050781e0208007403002e172040140780754400c1d0018404880180c0d600041c510f142c4c00252000302c0b0302e030740b03500040e640d0500005c4d001d840005030312083e0050240020f95603017524442d0701a00c0a640c00f1078284440e5025600420b4049094003000681c0360410f11101400c50500071140c2d0340180c3c3d40c0d200c0d00300311204042854016040204000309058200009082488480c94142091854248000c080740c0700c13 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 70246387 1250 70245137 70245143
    0x7030509130204030803070c0501110c060c0d0b03070e061504081c0513030f0c080303010f090b03010f020406081f080c0405090a050d020a06060e0609070e01110d0504030b0a18 77
    0x9045000c03280d40020b50507640556804504550f41e030503c0d9a0207401d05020380d004903815800c1c04441d9420a101c64103548040741d13031100500d041c3e1030b90720003000c458005200b0401d0743c90350f50000014a0b9410040c1a004020780308068442c1c0c1400c00a100003000f00d9004e6041d803400c00c004c10030040303030f00250300001d000b120107200480c0d22034140c08544c20300c6000c0b003908805106031000f105024a032003403008103510403a988841075036600a0592640000d00c00d2819484403c00208003201c6640c12070420800c00900004800007041010300032a005a0441c000069402c3c08100c4048544c5900340e070604882940441d0041c0b4000406541d0040d00c52003034025174588001c191036001c10080007044642c000e0035215250b241c020300a54503500c28400342d8001d403e1100011b0a030740380c4c2c0382c2240203010280625890380d54224094408840b1700b802681004080d50082508070014004000706800030383d41e0641c3c4600c0c40c2070038907601171b0180c445070005140c0494441203120001051600c6a8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 70247637 1250 70246387 70246399
    0x1602030d080103050d0201020f0904090f06150603050f06090609090a08030106080901050a0b0604091e06090507020d03050601080105060703051c0609110c07120c030602030403080a0e0d140c120f0a02011107030509 93
    0x4691a01070dc0707126500200030403a509014007107200e80a98204503007034480a6800300565604c001c0501c0b1b46000980b01039421140c4107020803c50b08125102c1e07035000312140100c0d44e5424507a0344040f00381d40300341c0c842000207014005010b8420307028080e29422025035001440714141c044009503041c40b0b03c5c800d800c0d40941d940b006941d1841d1002012100d0500c3e00e4007007005641e1009408003500007200c031203005014401481c1c1070f250091250500400741a5522042e036800c2009105c4a5444050306406000e0300340899020070361142440ca407401803036003002c18807519260043c0d0035280102c020501849042c451110343d08030001c0c0c00800c82c0c190500e414105e904a090509034002190005003440e40000304200606030403c1d051070007050380340c10030013102c603407600d41a491f4901d0404460000e100c8200c5030b03080d518150041e10000031030105480032a004590111040c0c0c1c40500c4070b065426000c02d524114540a21921081d0101030072624036000490342c1c0108280300710300ea510700c600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 70248887 1250 70247637 70247651
    0x601090506010e030106120c05011e0c08090d060903090b0c0c0616020a0902090a0b03010503030a11010209031b100e01020a06020706090602030a02030a0b0a0b0f1602030d080103050d0201020f0904 86
    0x7078810b070500d00602e1000b6008120013600c9210a42c55440c2e0400280c8804408d4000091709500c81c200e981e000b4166a401101920801c600458040072248409c1d0780146040c400103a151303940b05595007506115080014440c1d116103800307800416240e12a020510082c4a0f040ca070000204a003103800d03d048403d01c0e82c1d1084c102940500e10519032020b5085411240007041c0c182965000b4414848200d070101841c40d0b651601c0c44047c4800d0040315010b410901403401580e01402d42c00c0c6502e1848000503081071540404a0b14003251100102102e244044520b01030381054810890014070354a8141d11400220001175924074019100400d03103079000038001d00f800117550200005aa001038155034909181082c0000b80d04140e8440b28100e01d8000e441031030b4640321203179104842084c003c81e801d05100c05002240d6800c002c682c101e00603240d80d00c04005980601c880c8880150a880f030384895411810114079082d040078202096a204001c03020000c201a8103a5007980d00480780480c0c08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 70250137 1250 70248887 70248889
    0xc0c071412030c0607110d120203151203071a01060807080a06030b0f0601020f150a0f0209040608030a1e02060414030d0516120501050f0d050a0f03080103061404050601090506 77
    0x7020700a61002041c08003080310b048642010441d039000d00b00303554412404180910010385c540c004443c4035004501142c8144080b40f1150b005103070f00010709100281d0141d48040441d03458468140101155000001c045c0d0800c8600410503403460880005400250706003038000d0281c62000e031241e014060803000144403180c941e00001c2c041c5078000398410440c00c2a900300704141205076112400f5009000140860b60400074481c0c40341b401c500130340d844a884101c0100e0041220b55124200243c00f0030004a0720f486030b010702d000a183c81001142d8405c40c818000b003a440c103138805034091125602020005603400594140c01a0f04007003a00c14090302d81c000c052852080d4441e11405900b4813040104170402d48075014041c07061030f19061442c20b40702408500310f9009000303150703022050b02c80700600c6090984030280d41521071002c980c00001503032502c2d14901d034201d400b01d0008984800500410425004200f9103080102c0b00c1d6000d802d06544590b10341c3c00501407603a42681e10400a40f103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 70251387 1250 70250137 70250149
    0x50301061a030601140d020c0d09091e020f0d0603082a06011e050d0c0302011e08010317130b091f020307060903020c18040618031202070606030204020c010b090c0c0714 74
    0xc3c01901c00310442d501c504000c8d0321a1540c080c1040d04005c90740c6004c0008012185000318214a08070a01c202c1c04032042c20030400c0250401803244c072040d00b06110019031034a640c854000654040c401e80d5403144040d03078a8002c000f4032003054101081c18180d1120340e07100b00040d0a07041d80e0000b5010080e11801d40302400344c0801c1540100d6200035807a01d15014800d1100340c00b03055a000b03a8030240341310301910017030203802d0391061001d002078124401040458600c0c820242e9040c0e00c06502032401600701e5008a00c4851600043d40300c2d240040d0340e8600c0c0c036100e071b0803589510100c0c000c00300103002404041c1d281c1c010304070045e00154031481d400c0e00f014801d1180d003800b82002441d0440c0c021002842c40405c0008440c101ea040b407410106200305240c000d110070540c0c0d8182c1e204051b45403208191030107900a4941107603070f05c0e02e504d00800180d56500203001d03c001404000503070f60210500300701245401900c030f040c200008115080fa8000c0c08110716080c1c0d01c48995401c06600000c010401c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 70252637 1250 70251387 70251397
    0x20c09130f080d0203090d08090a03050903030c120d0606021606110c0901080a0605150901050d0507080102030a0905011802060f0a0e0402070b0402150405100807230301050301061a03060114 83
    0x445900000c0c143da040400d9800755000d04034038000c88840070b40b488070540b0120303015901c1124550042d600a000244600c00034201501c0142c2034900300a00e41d055607140811110610084a0000c100d40f0480840c0780720310b600030460340c0f004008048200e0141548040b8500400007000041d0fa0b055403030550410610981c04c8014040080f290b170b44081303c1d40c03102071600d022035030f942c1403078013040b03400780c4c8030701013a121000082c500c5c01103928203010040312500c0100e007101c40f40190440002c82c00030a1003e14894403660a0110300004945045800c4407154062052004038007258000540c0f196020303a2242071200074580c0e43e07540e21110507280507040c500381caa0b01c80e00010b14442040010220a07000301c5c0300340c0704071000c051901c01044090041c0d00500790400c0c05214986a010700c03c07104a07402204034140061030004e0030400d01080300c0d02440f15101c06100200401860509100741002021000b4400c1290310f18182d040c00d484c0700203041503040000b50780044c0341411000048134 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 70253887 1250 70252637 70252643
    0xf0c07050d1808012304030c0b0f19050910020904020c030f0c010b010903111311070b070806010c020105090907030213080c0a05040b030c19080d02100c020c09130f 72
    0x1c00101c0003032002841200d110304040c2c065000c00000140c1524140682c8001aa080d000e40c1c40022034072002a046043c001c00940030080c40c8007400e4081045c03040028010302000584030311915028041e01100c500c441402d0351007503e07040c1041480f200c08100020345411001e80580c2e07804207500000c1c082d00640f0101002400000b69440030300324038500800d04e241a84000340005100d03100103459001b1180f00161001d102201d00c3c642620342a0300c90350410100420009a9881120340c131581900414000ca600308030720001d22402c3c1d03400186075580101e0902e003201d4a00c000f80d000130a44d00410207010700545504005c2240640240c050341c00c00380c4540451a5807030f0b940c11080b541c5d0746c3c500384494050030001038081072908290080783d074100300c00740081000c21a01014001c40a0350b0b05100501415020300200c0e010009103c51403200300680e000f00829003d0400010481c0d102406400543d4070005005080391114030a96603c47d0600588202d01d0f4a207090240181950500013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 70255137 1250 70253887 70253893
    0x609061210050109060f030c060e030a060c08060102011b0507031409150d0f0603020d0f060b0910050f0f01020d0f0306030c090e0d0314060f0d1b080d05040308030f0c0705 75
    0x6400c0d80000c65002d00c0c1240e1411005002c4556254151042001139000c050401580400c003400064015103040d44039600150403110308900d5a1111011500480e40840c00280004117018140d0390901610020740c80c82c02c05d8444401c0007400103403a0b03110390b035402001c4c006011021072074501558113840700001c019110383d00c1c402c4150314010f082d034025840c400115150a0707400704018018807035102503981c041d0400048145a1300c8003c60703000c003201c00315082610707003204c41902e465032600580101c15180b000c1100303a040000304030711503074049451409050150607522840c4e0f070006882c2210047c178200340c0380c5074414034002c4024089503040508424860500014030a80319403000c2c3c600e001c2042550b210380210780d01181030352f44134881c14900700400e0300405c1c001c2c40c11440140001c940284001c51a400665400403440141042d038503040401a4082105000c00e01070070b240d90b0714601d8094989800d655500780d807408090016484014041c1c00034650745600003c031a08942c100d411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 70256387 1250 70255137 70255153
    0xb03150303190903120503010b041403010b10082a0a030203071b2001050a0c03080a1805070302180c04030618060f060812130b07020402040b03070806090601080f06090612 75
    0x80d11549803440308031454000c81c4090005c551040050740d05a400030102d0915142c0344c4800d140c6200e403c115969415541e40c12040060f81c1e401c440e003c000c0606841e420014030303081c13101e250710a018000c1c10304e92504464044588110170b80864640e460070341030060b180d446813030040700d02010f50340c281170180e0315184074001400560003102d5203941c4100c200021203628180115150300980400c0c001156480040e4000207000e90034a5900c9050f010740080c0e4613103008005803450f402044140d400c0d82240d04103100b907003061000c099030080811211445400c042c2078002003442a48800b0304401e594200c1e009071850000d2040325030b50380240b4140003400103404640024007a030310030020700d40b003101d8481714081483c1058030002c41008040c20071107841d02c0040d41550340040030403641f1a80c2008041800e4010b1800b0354096070450b03664095038504441800030303410700900781e03d05100321141045064801d040001d9031000301070b95004000d85a030404070310000201e29079004940151070b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 70257637 1250 70256387 70256437
    0x705070303020c09060a0e0402040e21090319020901030f03020a08030a0b0a060e0d06021305060a020d0f030506060306060711100f090f060f050310090207060501030212070b03150303 80
    0xf0341001125400c40d4400e002c3d4071010208101091035204e0414003480c40030006015141c640d001c0320f20021950150f403d200311181110503528803501442c0d264900c0425809454103080140c80050803640c0100d28924881e90001a0700f4201407100804601019000c0c2d41014400e0110052491780140c1c05501e80c14880148070182011114040c003a00e0042d4001401e40d00c1043d02002107100901032234401d05194441001030750011030300400241502c00005525101c910062104135210381c0a80b0b81c407120000c004000700c141d500b01c04109030802d0140a00d69407800101d0b6045401185c40c140e41e0a650305e01080c0c1e440005160740c1c0c2c094111a0003600b41508600e625584180998501d18441e89071404101c0c52040c0740038641c002407006201d440303550302401c000c6401101e0041c40e0501c42c0e54414000041e41cbc883c02084035150784030700c010411801d0844015010000032800b0700b48441c240382e0016182e0200800480c0c81000c0b43c02c1d50411601e0134001c0340c002007020385160b606035203416 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 70258887 1250 70257637 70257643
    0x3020301051f0f030b0d0c0602010903110a030f0507150608010e010c020f06072f0319050a0e0405150909010207210806010e01030f0e0a140a03081308070507030302 72
    0x101c0350501568452000c0d40311412550805545029aa1103c90500303001590072001001180c1c0d1301900003040c0f910f00c202041444000b000184a10303800829a900d192800900400c11510210700e290710080312200002d42000c1a07110702e10f203928005403202242c0c1000910741c89604003001c1424580880460341c0a8190005008041103100070310040c01f080d00101d81e10444401d4000c41d541100d00403900403842000010309103030b0080318910004080200701c504100d4054011038465100080183c40c018001440e0505002d0301d04107581406000c030b002408882c0400e80c805e04c9103a5440001700c0c1d40c445602807480d848800340800315185441d5020314002e5000300e0058401a00800303030707107543d403000d10b10070320501c55103950f40c080688500f8019200700250045880c181500c4151600940550703100300c1140101450003040310680e1420000b14100840303903807006503001580c0e000c011030b40024a040d0040d09000d079151044841c1d052241882c043c0310002000d130700503000d001052503400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 70260137 1250 70258887 70258889
    0x9010903030e03040506040909081c02040306060b0304030206180102040909030903060f0b0a09090201020a02120c1003020c070e04060e030403032c09040602030406090203122206020705060c0102040504050703020301 94
    0x19840c10407400e4046041c190740c0340513500c55185c0c0464100028040012290410400c0c5880303991030504203a01d0380611060b034441d0b010320102c2164081030400a2083d01d00581d001084100c1e0558914100751300c00a4444000400d05e0f950359560100f03403101c4031425811100282140c1c13034100a410074510b801003401480d03100070b668290600d0f00180b08420030344106500460000d01c1c0c0d000c0c1c0c5203025040c501500180350242e066008140c0c605001d44c444007000351100311010040d1100030708080c00c00428a01d4543c0100802d8414400c16030300c07186c0000e6075005da42c1d03442c7d450803e0740d89500e0240050500c00c1404000d900000c41c0020405401034001c1c06618210291620044000d0788465003190034941900e51202d42c00010401180762a401075800600448000c20344c000a60042440e05e980c0359039000407004001400604d20381d9900740f1a440c44844409400c4203858804000e5a03030b041c03230281d144a00c400240940d58240f007541214000c200280042c40340c2e05d00414054020340003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 70261387 1250 70260137 70260143
    0x18060d05071707090501062012030c0d0f09030504261006060f020307050c01080402040b1e0f0102060f041e0611030106141318150b0d0617030702090c12090109 70
    0x41d0f6100860035440030301819040e01ca032903948400044206040c1444c0c0e24010441180c20f0242c1c0903407411201c20381000307521512144401c0350741c604ca90345800045481041ca2411018a8035480000003940300d02120200c400c10750b5090319240c0303002404040140300c0e446600d0b0a00c81c030300340c0c000b0041c1942c1154045841c141c90302c1524810400060b40c60740f060120050040d0800090f0081c03940c004c0394481d0b00180040e00010f0355000210118443c49521003402d0401d07002c40c004034086103022400c86c200d0407820b101034201c600300319040320354200002e44000e00d000c0b500d0b0004540c884e04100c1b00c91400350030007420b0180d0008820780084543c401e004500006241a4100b0172403002e4030110b400d020b02c00d50800c0c00552070104004616001528800e0155403900042000d10411100c0790f405440c8500401d555030907100e0114044075010350000c628082540c0014034081c202000f5a0081601610054034555170307480b100055104900f0865201e298240078049000c10551088503d188 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 70262637 1250 70261387 70261393
    0xf0603071a0a050a1b0f02030c01051809070c05030a03060f0b040605030f04020301020d09150b040c08011202060702270a02042108130e0f0105060918060d050717 71
    0x1444540d410255499044910341c020030030010058050300c104018940c0146910307149540f042d04810b0b1441520100c0015220b5404401c620b101350720b428843d10120105c2428007500c0d00300c68451121440401d621130303e10489000000404c800d02601d0380b05000765100b02070b01e5a404495102500400c0d550080c520800e451a00120302036980b88200d0701a01c2164032000d082d41e840a842c80031121004100700e806540a1190340440045030080d00c01851142d07a052060800341c1305a081103442c5441001c0c4200d0402c4044950190000d81e1141903c8243c0108078000d8034074008101280700b8500000c0d0001c210846500c1900c1c03426084041031412003a4232401034031040e1400e4180c3c011406241e203a44030110311003038009100b408014102d841105d13101e050800c200c03005e00c103105c080d6102403856600e410800c0005032110038103901410044840c01c0c00d0401d0400841c810140ea112010020605240414090f560b101000c1510ba984402120314140d104c0030001c40040b1200540c0440344 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 70263887 1250 70262637 70262639
    0x60903030606121009020f0406120209010e1009050603160f0309021e03070306050c0306030d08090c0409050c030a050d03060602061308400504052403070902030f060307 74
    0x101020084a00400c802403001e4100010b5856034881854082e00d030f0411401c03022030020b102d00c2c441c0042c0c1802c40c0030114a540315442c00300e0161403c841e110b401c00007144104601c0903c0e0781c12402c84949000151804048400c03400d80665016a582e0440c95002c00040100006000904c103010b00071502c5a075008030740404244154180c2d95000d0000350710000c1d0940c826a80200c0540c00c01c094074006080b909816526290001161801d41d41c0c404c1000c0000104403081c10b007000070310300182e100e2404050380d00d00b0030703915900c80a4040026100740d84840c1d210f03090100410180d810305034000c041e10140403061900d183e03110307104c070b200e040030138100b2600080d81340c00032500310322030800300c42044480c40081d030326140142c0c0000c000241000308000c01ca04148000f00441d10a41203107034040f811003078100000030070294680d00c80780c403c901f800708000842948074a0080d120403803003404001c41000c1400a8148246a0051201d552010081040180140d454a80508030076000d880041e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 70265137 1250 70263887 70263901
    0xc05070203060105060d0908040f050a08070305030d050a09080307020105011809080904020f070f082113110111010c180e07051818070201050403110102090a17030409020301030b0103030206 83
    0x14068440041d505401c40401005541001d070010902c00c0002c080015110116540303200581e0401c3c0c11040fa01c2c0710119007880241000c84440b40504000d1006091003482c1d81c0d0b41c0c1d6502d00c00d0010ba0105551240040f50100038070350454120b090f07102034401c1c1c4030725240c80001e0090100344103400100d416802400c00c406205e100780740505801c802e0241c50f005070403007408044d5000d1502808a1b040400600d0041001c0f0714070b4100d020702c1044400d94900c03928141e540340008481c018043e244e0078074244180c1d400301e506610100c43c1c0c0008000d2001d035030000142c0b01c5507004440d0b51055401c194641c050560302078252000b00da142a1504030781c5072504c4c00350314103000884910f40400e900b00801041c41201c1401841000c2e0000c0c0b100e41200d05803424900b000e071041c1d0b1031102607919070051004040d002100b00750303a90642c2d0000c50038401c0034800101071008510810f0501c6c4c514520f1501c42e090184111070281c442c1c9001955a96900e28015000c2c5209120581c0140540d80c00b007410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 70266387 1250 70265137 70265147
    0x316120c020706080615071a090d0905121609020903010e0a0203072709060e1b06030109151e030b0c040b0d0515030111040503011d0a0308090a0c0312030c 68
    0x1031010558001d003481e40c1055030555034040d0103004203030310142d0f100c01c0b50400740c1c54800078110544142e500e2680184201c4181581801c05000000c0b5500040301d10102d150f488003100c03040b10003c5801c2c40300000301c00351f040c0c240f000048030503500c20b1043d44089820545038004000224003a0300030090185000388440e103a81d6a954004e6141d00040e1040003a440c40e13102a03000e000715500c2c0c0c18100041e0036505422526082d1040364200e888108000340040180300c0c90b1289101b04030101c441c02403910000d0312500c014040d0040b401d43d07501c2c03040c484030302d1301c0103180190044403800342028044200130ba2a540d00c0e0302c0200c0e843d4918000146070b1851400c203603411980c0c0c3e9510b40381045a48412000944402800550000000200c3c20700710341e424080e50706405c00358400c00742e60fa4106000d040c2924101007a0704440f503140120a114590002881c011440d09031034031005a844a690507070816030000009804110b02420200910100c0c02c00c41400c4401c1e900c080103031095040040d15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 70267637 1250 70266387 70266401
    0x6050a1d01140a021b010516090b0705060c0307020109051504061b0519050712170601090e040b0702070e0c0a03050a0603120809031b010204030203120c0307030c0314031612 76
    0x103150703018100428007000c81c1d071300030740060100c521a11401600703407030040307007168401c5030011020242c10820003402c0b82c2062503c0050445146024588105a01c0d050354440c00900302d07210660b000400140c40e035201717511015440740c0c81001d4a0360f004400385419030720f18090301d043e01c90614050021412001c48044401440c005440e03050929005911384250404400390310000d000040040400240b0441545201007030207441d03004d1200550382006030204c2c002485503060217050001030200144000c00c883d4440e5001c04035001c151743e001c504030304000c450b0303011000020104081c0a81490090040d100c0d0020569081120f0b5450201d0750013036072601d03c4060548401c841210b5100307441915071540c030900e1101183d00d4002d41007041e0a20307146004104000d42d5010400b4003c42c40d042c40640c101410001805040c085602c1400c0c0d00d034824024000c0078041d82c000c411082500880010000840341c0840b50b4413498012840301295002d161000002801000010341c0b560345071003010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 70268887 1250 70267637 70267661
    0x110f0d0f0f0c0902040e0403030c1b020405311101080705040303121103010f050f190e1302040515010201050702060709060509030115080102130f050d06050a0906050a1d01 75
    0x4201846456080741000c00702030079142d18000200210f107204003400200010300041c3d030800818902424020100c6021b03940074000c0054090260041212001c0d40900c500d0301128001595140c603030800c42802045951032514400030411004030040f600000141c1d140a0380d08107803038000d01001160660000c680c5840481c209000034400b080c491080b0524041c1e00a10004101072044015582600244d00c4101e282c030b6030007018441410840180c800456042d541d1804c090320003a0b001650311954045c402e00640200c0001d1004080040c03140d40c200d4028208200384d00700340160070b4002c8420a0214050742c200b1010448503840000e10a211b01c0f46039071072149107410600d04858580c003010405616648880c0494001e48240400300c004024030000141d84000311400b0941c00c0451398012502111010010007082e101c542001111580c840000901c41d59070519040060068520141803a807400042045500c1558041c0755884001040c255040602402140c2a160032900305 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 70270137 1250 70268887 70268903
    0xc140601060203070b0604090b091c0314070e03031606140f060d1202210301030b09030a0c11040f0203090a0203071e0e0403050903030c010209040513110108040c05030a110f0d 77
    0x600c02103141c0d550342e11b0f0000401003000c03c10f030200d40c6400c0903c0c80107842c040c0e500c1d0040500041408540654038005203400d0505100242201d044012056001070480c07040c060719038810324232664240129040c10501400460f40310f115420404000c00a4529000b4000c12050104d1141011102070901c2004010b164580d03040785036460042c0d403e4002148403d6114032030108200c610250f084a2004400044481d1207600d54181100c2d0304c00044c0041035a0f03001000740008582d07000305800c0106401c82480c4050030225400f003401000d00100c100486840401840340560010406482d968021401c071a0740d142c0390303216144071402c041003801700c080e8424801c21900b102484d01c2c03944140281062400c040c40784001c80d00796481000801d645075400141004c03189414429281c000003090900c0e03001d849269510858400f105003003d05020380e50001a080001d9035484001401e00581594204c2d0200d261204400c1e592000c03091059000c0e6035100c41504241e030b16007079159005007134 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 70271387 1250 70270137 70270147
    0xe0c0304061113030506160801030209010b0705070510020309040608060106120b06041a030412020a02012715050a081e01060c031209140c041e0209060909070c140601060203 76
    0x74500040403000e2090403030b00828001010b41103e181c424030011402940504680c4c03074030044642e0200e00921142d01400000c400500260711005109810b507040c4944040d43c0b50301c0741c180981761000300c1d40125809001e40070310301945540030000c2c041c400800d90302030100c03d0301c581c60551925030901444c800942e260700448000d66198000c44403025011b4040b41c0352940342c242210007100001004a0400c2c80081030004001c030704442001031049600c054a400c41150340000c1444151907600d280701e13544c404803116050407100740c100007010079965043da8560700503000f5019402400100020820310750004540d8800441e611800920f41a0407407156802d00c0029179002058100990401020020b00d80240c2c1da20b1240396060307802209600400c000c0310088030b2824100004070350055040118098800c1402c58110f503054034400340268a038000b1201084040c0201601c850b40004000203212000c0d170004080d015842c040d5a400e281c41100d041143e65070765007841580c00580c001c02c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 70272637 1250 70271387 70271393
    0xf1121090d02040f09120201060e060111160e09070503070302060406030203090a060203010906050913020a03120c05010f05090606060a0c02040203070e0306041110020c030a020f010201060e0708040c0e0c0304 91
    0xc000c1010010110005102141c022400301d903075800035501c00b42d50b1040540188482e1800104a889144c4003d02c8000d00b0500e01118445c000f50409041c0140c075050350b01300c0203090150512852807003503110341d21035461f200c1c1280020143c5040459018150012516050204040b0280c94010300401c1c070f45842e00004400030740c402004031310b00780101d01c0b03250b000944a00007540205100900030880c02e052030f00300059040c1c007614440f4841d281e11101d1005845540c003240031250031000700851040c60766810b6070040b01003a0024515440c00100b815a062580d01040c095602c01044824642c0e03038005004051058000781d80c04194147e0317040d40145003580085900629905d000045400c11801091411005076012241e170002c004407188942440d45207945655035030702c02030008005c0c0c100420f4840307190071400303405410a0040c0140590007508004014000c5404001082c64901001030440b641038500715140d9100c05000503603400304140d02e9008102d00594103203142c80f203079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 70273887 1250 70272637 70272703
    0x60f07020a0b240306190f0216060504050304080d090e070503091f0b3102251a0405060403080903070b240a08010204060e06031b030a020702100f11 65
    0x1001100b40729109181d041c031645050004c40d0044005441c0b915102124411003007c4e2200000300074810340c4140720045504110208002e0902e402c820b001031261500c1c10b15604510030740c1c100c0d1006216000a800b00d140d03001121800302e82d49080020ba6588a20000712240d1001760783d55807140d80880e4110450222403024190b04040341100000d66620917130220340d44200361f906409140302c4e0100d0b20740d8000d046031944003c511000c441145003503001c4400100f54600d110740f040c07851031a400c04070200540e0200d0981c0c031000101500070140f6003403401550703910007290118005842c0002007a0301d0207000090300d004075840300c841100740e038805c6007402c000f5040e04030f04a14081016003030752f0b041c0c440820b00d001401c08400050703940c50400340c000d011401400045401454108200401c042641c2c613048400307040054280d90b2074494504460180c01001c0020b54441138070702c2c060061a42140707140c1d80000c15078a481c001e00f5016040140c0302d10b07410850708120800c0c042c403941d8208042c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 70275137 1250 70273887 70273921
    0x21203090106030c0308030a051032092a0a08070f020312040b010504270201051b01050108010f050702010207122708010606030e0f07091109040e060f07020a0b 70
    0x1000001d00b40e5501d882d200184030007a0302c107880e400c0c03001062001c92001c1d07029140d48801c54070701e1043c6442c5407175171094be9103030740012500c03100410074040c001ca94120209001c0130742c001000198141032070080a408800ca6100103002c40d4903441131400d0809820055442eaa40140c176682d59a540c2c800e0203940c1d032002c0302c82d8001180020030a071500003024100d8113024a00a440e45000c96040206200c129000e80036291b5208006500030072190b40307007070000140d065081ca0410f4603000300744000128580e41c0340c4104003a5007010008144c100c4154810a01e10080707410500064948207000e908138410901d01800400140355100c4030b0600582e116a404042c5418018581003414044401081c55411104099444000410400364540100d8200e0030350a8040d0070004841c09102d0360f520400c0c0302d904540c41d01c810040280d504210151810840d02800078409414000b0420b07880d000112123441a0751129008105003900c0001c4c061400356204001403c191140001c60024201c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 70276387 1250 70275137 70275151
    0x6090105040302180405010b15041a28020c060708270a06091a0c0304061b080a0216080106050f120a0f0f05120a050a050a140f04050301110a021203 65
    0x801c000000040e20b0b1400690307080c06022142d40707044e0816290480c25030329282a035520030f1080b04a50709101c041039007254126842d2828845010021340030080e214055a001d00c0002d03d102a1000001042d078220302a56841607800e40d4140c94580d41081554003607054090030003a0184107002a001c944408480004c41240701d2144a44215000494a041c107820440000d54425400c001004020005960164002d0703011030030034481920480d07482c051032141c40100803207440704440b5020700031403c070445500401d14039515003900740040d56603290200110751101c400c0c00300142800040c8520f105851000b40401005516642080700d0301c0d460b240703808014050002801d000a1000360030581c00341c07107907905400d0b6240e903040050030f001084c2840d07000b0090810641095076400f04c210744204281d808c116841703c402140c11200d128407100c0781e8025540c002000c1203045010030180040b582c00300c0c02070103521180744141c0d03090301840b114240560302c20074503001c480c1550800707541d000103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 70277637 1250 70276387 70276397
    0xf060806010221041d04050303060108041b060509010e03070602060a0f0e0a0b040308070e09060904081e09040f09020d06020c030f030a1a0f010c08211006170114060901 74
    0x803400000e000c00b41d1180282d0b103c8a00009030402084000003102c076203000d4500c050311054034040d2181034492000401c101e0401044100240400440f01c010a1f12590f00d44084e000322500c60740090643c0c5c5c04148140c2c00f0800c07007018039001d860300055503000e80700282e02a0182c1c2e250b21482c100a008000c09041e0300e10b4482031079001100b42000b540c2c0b141800f40318601001d080609000e002c907a8040c25001c100b02420340d000845403141810f441c0c0109007034920700d10075560707400c140f0b44034050709c20f40400c03805a021102d04058400c50240c80034800407241008400d213801904421520204802504251079510000100d020340d409041c145540d202900e151143d020b05580c22a4000c441001855030348000342d40d0481c0010f03821800801059504e21100324100700040e214030b400d00001400144002007204031805100141290701401c040400d80500340310b0340d0048102002e0260b1000a09428403020004c98100c0c1123504032041d04030f6034000714180d1400e00c059a48021042c0e41401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 70278887 1250 70277637 70277653
    0x14070803011a0724020f07060f14090307030804030e0d0308040506061002120d1d010c090b07030e040903110a080d2f0c12040902090a150210090218070203070302010b0102070f0608060102 82
    0xc0ba000003044541c3c880ca100091701c00c4274040d540c00f1920000c0840ea00b6204401c10070500f080c1c000708946e005601801d10303941607500c2d450125143d40840c2c0c04240c00100c62500d0400309a004801540600e10a005640721680c5140030310401594800448006030700403090010010248801003a0490040d240802c81c1c0e91034240140b079170510b10655048a1790740c1e6241d082c0c820b42c044161405802018401071414a00b84ca0091221400030081c6220303e680342c401104142c082c03504910030b8041392054030303e00b000300e080c040ca2036005001c1c14805282810301c1208901c0c8143e40381c032180400b06940d60b400c0c0304142c44000c0250407110881c40700d03106a1550810040209019100500200c480965182c2c82c2e0414000c04034201d5014514500c400d070440644142c0100b03c4cae0b00741a004500028036409a400041c28080d0301c4824060894280340c144204942c0c00700c0100710700b50180c0c00030700981c0c3c030220049030b079010b0381c2c031400d03a9503c200300c01030040d03910680c11503400001c148102da0340b00e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 70280137 1250 70278887 70278907
    0xa05010e190222090c08101b05090d02151206030604050703080703020a05010f0c120507050301060302090307150206060a0f080c01051b1b0a090b0d0b060114070803011a072402 77
    0x196031000007a6031042010ba81005000c5040044030180700c7c405d0018030480c1c0d803280350705000b9480c20840300d00340b010101e03d0071129125040c51014040d00100702d8040404180d0b84075010f58800d80d06a4040c40781000010450704000821900031540003000f40034942c07564988444c260000c80c01141180101c090705004900c0900559040400314a000160304108420250000c44500003000d902c50804e820041241c0c3c00505690445415040140e80c4840500000c0e0030310b0030700c0d00700840c420445034014203440c0e4001003440c499081561038a07611902c5003201490410544920701095202100c188800e510440140035000d100c2400c4550301c510b1007141c14148a1013000c0d00c2400c0d0424004401c035450003a81c11402018007100c01c200034142103002c1000c98120361400b819030f16000700886d0190344a8010044e160782a401e10540b40d8075185041c014561084c0709010300d04200800c4001122504001ca078449540500d0342c80c50000c3c2c2c4040e5100003c11a0a0481a680e00303100410301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 70281387 1250 70280137 70280141
    0x10c02180702071502060403020c040e121201050f060f07030507030e09070210060b040b190c0209071e030e031204020f0a06051b06010305070605030604020904020c0a05010e190222 79
    0x1500082d000342164a041000d100c1681c46255400c00c21940480d0038800400d030082844c02c4805010b0701c001c03a1000c2c10003070162524645d00c0802c0d9454200240500008218a80440c1610300c225605c402c000c03a0181000407502820380390901c40c107000c00882000900507002040364511900340018044010b0001039200d4100700d4860025801c1703001c152644840781d109260280829410031400d1900f41060400b13240290780380c502c1d0f2680080c026841550003151080d17141a4010520707103040c07a12035002090303524103414002c11440703120b0040b01c2090003800b900c0311034000d01e4011030906d0343d4080c40c05000440900300381d030007502e91000070074541c0302c1c080076202070031141d11426940d0240035031800c2205469001d1850350f4200c0360050000a85c0851400b0468040d0714145880751200800035000f03200d00000c03079621074400140c407000c0716004100a0b104502810007080705044c22030708581c4580b4800719400e00e0598060b010b100500d8441c00d00c0700d0102c0c80b00724040240b5054092001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 70282637 1250 70281387 70281391
    0x603030203070203061006020c0d0203030408060702100c050a050a200706020307020307120506040f0c08010203010f08010b0409020f0d08120f1807050d03030c020a0c09060f0e090a02010c0218 84
    0x603003001401d401941020010f1750b41001100c000c03410b91a1822800940707540b5000d070003178490340c450011003055503001c006840282480c14161405424441c402030350300c9804041d00041641407103034015030759001e60240c45030011551181d40c0b0700000ea040c01c48504035103d03600110104d24100425861204003c204044c140c40e800941da0b40455004040c5843c0899014480c0702c24045c0702000091000303d40e041d0000e50080310010451268549020042165080300000790300c04070000510900700e0303804804480d4404000c2104080c204240310903214200030182d0418005407651071103003001000105074502858146007080b81d108034221040e41c00362903540f182e890003c180b1600300305500200002150040051414510b41004104075500c01040a0289a41c58003c07400260003817010780b000582c00701d404200349494482400c02071503580100742880306241700c04202915031905481c007418030440104a890429401122190210300b012a0017403103d000e030780300000f49040b1542c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 70283887 1250 70282637 70282643
    0x9081c02010f050412030e0316060203190510030c0806280605061c0b0a12030305130b040b0708160e060304060b1201021207031406042a05030f07020c0306070c0201120603 75
    0x5a60b00300d17a074001000d49000e82e0010740650020007201d40d100408040480d8031940c0038001503101e83c1c540d484071549441c1c6661304884a801d000401c0807003540c0c058410150f0713205a103202c510980395000b4984e12807044400030304254111468514220031702121b2003a6141d030000c0070030103585a02c08500c10b81c2003190341c010f008001d070b0492010b00c5043d0155486d50902610020710040c981060b8840b010b10000005d002c0c580c0d1500450030781d5100a501c4101103822030009280e42c142031a10814041c1c00301d81040011b00c0143c040b07071020484103102040c030000342d030326041d8004a020420400e0f9001420403220b00c0e039a83e81941d41c40c0c503810101401812464001a143d0303003541340c40285900000c050a00701441d0400740d5000c035041035035040c0c202c403060b0350008080000694410001d1001c0034455200ba426844510295500400444c4218480a03a407002d6444400040e6910503d4407030b800e82c950030410024054900c01c91039001401e00524100b040221103003203a40450310325400503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 70285137 1250 70283887 70283903
    0x8071202011a1c0203031c06050a05060304050a15200310050a0f0603150e07050a08010503011103040f0507170c030106051002031e13030c08060f0411060f070c0e01030b0709081c02010f0504 83
    0x700090310742b00c00e00000500080d515646145000e98680c2d88802d200400100b807942216168079480d44580e02480000f4500e42c3c0413060590480c3c4241c80c141c204950405c030310403854078003181724284409204121410300351828601c50400c030043e8042c010940140690308a41e20303000448140545286020f10081e031910795550700f02d854020711968050b00403d010382c0c1400707480c501c24400da0007140e81c0160440c1120000021901d001d908004180e4442800c15212314248100e080c0d002c90111030381c0b0300071070080040b2651842484038440c8480321410150b002440414166401c45803000b40301c688400805203019200381c0c04c81c810500710380060b160111081410301c005a030400a840e0007002c110a080e0341031400b580c1d00c4050401344881103025050124540c0d000300b546400381e500481d031060740201c4481d156620002400b4007444152048101d84c1e000c41c11250083c00c2000903140400090100400345840345035044001941200031036603140c480c61045641442543c5c0035905c01c1a42c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 70286387 1250 70285137 70285139
    0x20f010515011e0507150905100608010f0605060a20030f03011a1306050c1906050601030b06210601050d0504050705030c0402040e01090906020708071202011a1c0203031c06 76
    0x400f88880903814140080c3c40f50803190714981c104090b260401d03030025403880740c0e21202070803002030f03c5d0741c000c0200340c0e2203210840300f0020050340240080c1c400400013000b50500c0c4400c1d08056552030310900b90050810000034040074860a0000c9298070170700b09030401d00c40915690f51441e8814451820301100200051105801511309668840050103525003018140400c481c2010725910814050050000b001c0944003001d01100408080b02280c28402c8101c0c0d040c1310001d000704a41e528002490050901034928018041d40c1031090883c00d1a194000c0c10701d41071720654009002c2606105080c03001c6c084a441c68014507100380d104c1c60180800300d1400050524005c3d030105800d00c41ea00602050001c20001160141161003040c4042120382c605c0c28041d000307104c2d03910044e2031850005040010301c00c0c1c10b4810b180c01c0301c1030340c000c100d5405c1c4508501603010310400015840604c80018032040c01d40f80c016640a47e0004068a01d032100c0e041180c40368102d058542d0040da611164 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 70287637 1250 70286387 70286389
    0x114010b0901120507020c090702102316090306050702030706020703020f28110d0f03050315010512060402030402030c040606111c080c18060a03090b0901060308040504020a020f010515 81
    0x18820302c402075007400034403450401703071000303500e403003800694502034040640003c03c080c0c401c100c3c0c000b02c3c07400400300b006003007000f80c0e031403611090040812200034110304c0403e07603000003451418034116095960710240e40c00d40e92914064580a040c020441c80148660350200f81d0510050802034400e40003844800550b489080c10808a903c0e07440300005103815000c0030307942e1010005002680041508040000d240006a5420500300c0107020100e240700f00c8003c05401100450285541d603460303050f640000c1004459510410700ba020701c0d451010003207182400c080d0069604144002e09076400b54000902240071104d99a00220000300510360169203040140120500a481d14520555007107000c200640070f08000341103003209030000111940103000c1801c50700d0140000500d0079540d5440b01100a0140070042415a68402c402000c2000c02005100341000c40b50300484080c201481e00302040000d401a0b410a41903000c0d00e44000c5611400384500c030b1090160030605162108010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 70288887 1250 70287637 70287647
    0xc0e0906061525020f040605100f0207030b09160909020d0201030b0d02120706030605060f0703080603030409020a02030414011d130f23070f1704030507051504050f0d0912050114010b0901 82
    0x400b005014611f0010140315640f52015000705441e05401c001949401188040345401d10030380c8080d08401e6800148403035440003203401c007101c54480c14801d00c0f040d00d07660f01c28200c82c03000e00c4c001d500007569840e072401075020350068842c000c401040560000c1e00c0e50049076007200f060a0302142e81c1c2100c42c0034828583c042c41080041c0006440171800c0440c00310f21420b040c0f04915000e424444050700140c030559007041240d01130581c1079410b6443c0c20503000069629005402400740d241281c0d03da041e03a6511524030b40e00c0f044410390203409100c0e001d40902c044040880c0503452107a4440010211282035802103020070205a4845074030a416160f9101e620782d000b400080801960f004a406170039484101c0900a01c0c047c06c41e140d403500c1d240760a94061240f040000d0580c010751000c81c1d121102a80081d1055006d04240c0e101d0302ca00703400403505e0340079455041c0f003c00c00d056000d0180103554810112028810030000442c0c00301d000241c204800240c0c03140742094000030b094101540c1c85 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 70290137 1250 70288887 70288909
    0x70f05010501090b01090e0606070816020306130510050702011b080609070905090106030507021c030c08011a0a0c0c080f0a03031401030201080f06040b040c0203070c0e090606152502 80
    0x1100041000c1307020000020a480924400c500d1079aa800c0c02084040d5a60340c200d40840e5881900d01e41e5030600c0d264803517810004404284d11034051100080c429070104c90201030b4459001c0050904500d0210306903004110107006d18045660310750340c2c1c180f4004084038251010144d0f0310b500c821440e0034420444490340003412041001040da90402481d160a00ca0906455203410041800d5882c064202e20345030b003403141c02e80381a1818a1243d82e194055100b8191a0520740d540e4800e03a880d0010790a05441512a106140e0740411034403000034803581e11302910398441d401001d961591442450320b4000405007004490304000c80fa94105074052151000c2c80c1c1603840303d031021350300d1a000a40b0a2000070b06100310300380c403500013520070b41e91a032180003d560000d00800040c044030740c3c025980c6c0c00204080f02c0f144071440c00420018502149544100f0038040101071702c0e0794190501106850329400f030b4024081c14021040c3e220103a203032000c0c01c00846803410005000b00e0040060a103c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 70291387 1250 70290137 70290149
    0x703051906110f090d06110f0903010507020a020307050d081902010e0706090602060a020304030519030506011103090a060e0a080f01020901090504090308060f03030d0f020702032a04110d02070f05010501 89
    0x8000c03e024042040007583c420880c1110a01e50142007030800001030070381a82190b00d24100090035040c42c100e03182c06810300303210550080103741e0f40c031442680e40e0b52180300041d5040e03112078001c000d1803400b1000380c03c0c16807141910038180b0000c1c0810b0382c1c4540d0311921840c003603515452992503c41041004400514103443d001075014034000e0040d4030ba143c00343c07a60044a40010004081c18041c904540301081c070500d1041e0a21009000140203060071b4840d5400920441503280d942a030001c00d0f0780c3e80b034000800e0704e4031143c9041c1c0c09a41854a50501940003a58000b000802d51004d2111000c1c40c04d0060015076540c100c00700040c44c0c0c00458004500c12440c244600e00401d500030211030388100140d50040e0048031080020f4618010f02e22840b0031f582c1441c1e443c100410306030300a460313624820303811101c0307900300503d0b094a101e0000d00780b040000142090b40040e4036158110b07561501d60900220f14100881d4010030582e030092500741c600341c0c4800c8150b42002024840c0d2401012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 70292637 1250 70291387 70291421
    0x120206011503020a1b0f0308010506340507090506150a0f030c030608030c1e03040b030a0c050706050c0a021203060a12080906031f0503060f1303020703051906 70
    0x30400007110848452103414504055000c282119158002e40c400c400d00540b950b4040c15441d1207103443c030f20003c1c2d9050203e0000c0c800030000501810442c05440c402c0a01082d14603000c00c04800c600040c00069000c2958078000c40c0c00c50000c62130078403400c0f024003000030012409140000520032290304003001014020810850105126031091860103140001e240200d100000e244040300500481e8000b01c030345010004000e02d00c0350001038800403070851100c0c03a03030b0b03088100070034183c490081d4031414007140c41c1080060414440d680c80096203681600f07225041080c02c0e140c01040314021120b0581d80a0b0025400f00401c0c0c040003141b24407051004250b2552410f2004504004940e104220700d244805000c0400c20820006071011000058003030703a103a2500c03000301448908880b0328402b14051003000031405d402c3c007148291103992903c4516110762183d1640c0b00b60115420b60540840c0542039011001a0303040c07003030203a407450940c000c442600e101c1c10050115a400e203c0350208030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 70293887 1250 70292637 70292639
    0x60105070209060111100f0e07090209090610050c0a0b070806030c0a0605070c03051b0a060801030201080112060b030a05031902060f06010f14040914070201050f04080f0c06090a12020601 82
    0xa0b50b0720280c50b80c0568207181900c003580000d004c0a103000d542e516480c0b00700e801c00c0d0303503a6010f0313070346034440d00c0145100c40855580302d039502003c1c0f040384140d110701604002c0a000007121400c05e8054200382c0010707840e199280048501400307080c290580d104844082e0340c1010300c14160b40c0030903000e0300700100310054003011f400c0c2c0c400640348840310300c00ca0062000210394034041c011502c8045c401507800ca416144520b10480c600910b1a9004407041d1144890b000086086849071040301c0c141ea5068407041c1059007410294002c420303c6038811a4940e84690f807590716510107214903801684540005c50311600b01d540e1280707402001820342011584071404210050b00100c1150740c1101007030910320b03d07454900c1c4040b2120082d0f9880003d0318240050f0020300c02c1116403010020034090400c200079034030b5104080342078560a0b102c2000c0c0152101c081030215003580c0c010000079034a04000c5140c07001d000c0420303003840421113901d0b03401d400110845060007030220060b07080041600c0940115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 70295137 1250 70293887 70293889
    0x50a060b091014010203071b0f060507050c1507050a0309030b06100507060504020a0806010b0c070b0301060806510306090f040c0f080616021906050c0904140702060601050702 77
    0x242595108804056800225800143c0d0092084946442e04104559520031040b108e1042d04801ea109400801965080c0002c0007481001500c0700345601102a280e20080c0c01c0030004858034055000000700000c002c0300300003500030402200f0b0103111391641c004883c61070070002004e1a0080206010340f031200405401d1030703402021100d42d83e80c004130025082d1680d001140c0d030b00d2215000421144211400844c2001000d400f41949260b040700300c40b1080d80385d40d036005890000707110f02004902880049566442e02c5c100d50490b0010b00049041180508410703482c1450386215403520300c80e330320034904100713969080d0b19509a40c00440100e1560904a01141800000510808800b08130744085020084800c250400070542e52920340c503141e031071383c0341551241c0c019580080c00b1280140da0350402800030480080e512058000d00d0090b48580c1c54030710141a00034034451043d0001c2244042d0b40da124403d0841d917418801d61440c0c07600c1c100d440a468070901800c0141805428000c03c001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 70296387 1250 70295137 70295161
    0x40314031f082413080f1b01061401050a02010908030106110c04050402060901050c01060909080a080601080108030307050a0201060b0a051c02030c030105040b12010f0b01020d0503060303041a0f0403050a060b09 92
    0x7000040d07540f10003560359410329403080000480401804400001400d07003c43e1034140103043c4200000551801c400041c048243c00c0b90414072071090018124010041d066000c1c1000d441d1600703240c00049410400d940e07560b505580241c01440104203081504900700000700901505400c058404005034203042d0005136090282d070100c14108100040e00d2000c0280a401c41d0000300b071001000e04c651202031800c46000e401c45241440041c0d42d0400090701580309150aa0407210500d014601d10f4480b0b01089846901c80c0034050155900e030040000d6201c07460006081c006190391315603491300941c102c10101540d0b0b98070b1380714030f1600500074840400300e1101180d044981c01c90b80001c1e0983e089011580400b0000c0c008010383d443c0201e801210720342d642009c0e42c680c80903401c0d030b01c078144100f0090341d0b2030005036021501030344103101c02c0c041820807030096003ca03070515840e1030400c26040441c05444d401758004842682005600c0700800405010f45620403000b20b503880810f00d00f044082c81 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 70297637 1250 70296387 70296433
    0xd030c020c0a0e0c03070923011b030804030e061605030a0311040b03010504180b070306030b090d080c0c0f03030406091b030f060b0a09022a0d0215040314031f08 71
    0x4c0c00c040c000081540207000300082e000a1041d0104001420380341c0071400700d107030031307004106000c00c40c03013580d5050407080351074512401395064490040f10303200d5031012502c16154035043d07900000100400700c11540440300007000640b08400942c2e40d104010001000d459840c441c11700c00410903c070134409901803000f586d041d100159000188802c006001c01c0c1d94080c12913028201030400300900000c5e80c4d045e04040107480c00385105001351b40f54440115a0741d0010700c1101e00194024001c5500840e2060040907070451010440341407609200030740d81103520551302242c415923103044000c1009007903042d02015655000d07880c884c1c0d520316200c424a164900768010100c41c0d03a218103014680d00e4111420141840140464440511040348209880c151001400c003081900c0100a41c410028000d0540c0b480c55014100e58200c40d488190041c00290003281402101e000e1042c00340d00307000c0070b58800c1c4055110081e80e8840f84000d403007000e0b5a0380120748150043c07041d22807001c0036060614 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 70298887 1250 70297637 70297651
    0x301090f0b040201020a060c031b050415110c0a060c0605010504050c09040903020718090302070e0c09061b0d03051e0103020a1404090c0902040503060a0b0a06110109050d030c020c0a0e 81
    0x10340c1c203540303070f2004030308040c81c402c4014081c6260406500b10795525900c102c0c01c190f1564400180300312490000e8490b801b6910540c9450641c0d9004840600e10400c0b2143d0200c000204807280b4020003400a4813410301a00b204000540070120003080c40103900406006080942d07082116050070000a0b62521070b0350b007040d000b42e44402d44072003058400c01c00c02c40184000342600c0e00c20721035840c40c20007410507540c3c00d500511401d07001141e04848a4195030044080c520028a06104501802120340151a0f03d903014000050460300c2c0c03a00a2000b40c00030f0340c0d0b42c2d900040500d070181c120141c0144101800310000c0c0e203e00140016140c203107040b000c4c1d80c0c04544149607a1207030742c002001b40c0b03000301000704032408410000805c180d04da0007074810344d4003c4096410741e986030181c442c102c40d658101941d111645030030821070b050164405070348203010322001140303090181e200d80e40f0741045c2d070365142d0020703983d03c8103120403660621869906003011142550303850301c0d10039480e45020303000e040d80c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 70300137 1250 70298887 70298903
    0xe04020109140d020a0303081602010203010f1401120f050a0e030705060a0509070512070602010e120702040c0917060f070c0201020604060e15100801060b0f03041502040503030d0209030c0301090f 86
    0x982c01e55150b900486046a000703001c421455200e18001f0f10510044d94000ca80e8100c42c17000c91030460043c025241a10360700c1100702404d510f0003011045d4040720020540c1404400c4801c2401e000c040c0c0500074030090f4001b004511410951400c9040b5852040e40843c280c00c00d00c07a500011311301103051178004500c014081090340701c0c1c690341d0b8100402c44d0720240c2c1c0309045031040002000c022a030b110403142c40c0d8000300004840d00c0303030090700c40c01900c0d05010611000c0200030f005207042c2d0300c5404044650b25011607250746504e569103940c500040507c41d503a00000c1007001c04110341130340c0c640c080101c0c602180c9240203a030000c1e58440c00540000c00c084d4079400825140301042003030708074980c0c007016016200d081c200d007004151405805410620350030f2190105515400c00c00721540e06941404640c511343c1d03a0f4072007000c3c0300703c00c071001c140841c0c003080009901e81c1c042002e0074000c0221480140c0e18403142c001c041c82e040342c80030114043e034182140e20000c0707400040d400341e0141e00b061310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 70301387 1250 70300137 70300169
    0x21209060a0809030904060305010b0307090504080703030c120504050102070605060402041206111612020106050d080a0320211305031b01090f240603210509040c02010b09010e04020109 81
    0x40f14114019a03c0c607075001841d001c0300100f801015003107000006425401c0d51030311a16030310340078191780c07085030b01800202041211000287c440c0e8407104040c0a5440d11000b0071154084620940750140c0f400d45080e900841c10200340045031203002d0f042081160214913244c540710300103040003c4480050328142c2c0d65071045c60908050360071101c4180651040c0a00b19130f01345802c1c402c100c0313400c1a8400540c60480007003403a0504035170703150b11a070300410400c2c10800e0088049024000604e034a090109407070382c522080780030260147c803102c0500100e525103162803d009078035410300107145400044500d400c900105d0070101c00c480404000c520780141c2e40030540b02c00c1e03014100b0712030000d1540b4100c2d24248144070401044440d80140c0351001d06500004001020681c0c2c0d09000141426890201d42840f00d10b001e010b00c1a600d0950416608003c85d507400a030844034440c0d0380c000075035160269100b6030703d82960042e0141c00c131f80820ba426410a600020f010300070f2402071242c150507a0b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 70302637 1250 70301387 70301401
    0x607030e0705100c0b090303040b04060c11160614090a030b0403090e0906010306050703020a09050f03190c060f090f0e15030a051e0304050d020f1809010c021209060a08 74
    0x104140c080c2070003a05400c803110300204020409076941c44d060342c0b00001714004c10490b007000b0007203c0c0540e8116552008170b03211a201d84004021500c1c9140030720000c000d00d540350600901c418111045002c0c40740400614007040074000d1381600503030203512201000304e02600d030303120b00e0700710b040e02c0d0071203440c2207030365640d141c252190708c103d41015500c085c00c2410802c84990019559059a1290303034280175580b11640281c1c02d03401101c8040001c542a0181031200d030401074a100c00140d002030884010290440420500099120080d03030480e042000a1003042d801401c0140c110106280145125207088012110070040c0c0c09404c29011011000c2a40c2c22500440300303021800c020240d5565038003d1822507541d880d01c250800031401d4040e440b0f050310601105450440e44054408001c480181d404c01c20400031406001d50300c504021240c0d1900c0c0382e6000100e00c0b61300b01c000001016a5462006490003003032035602100c610b01000303c1013854032150305590303042e0b8003400c10a00640b40d040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 70303887 1250 70302637 70302643
    0xc0b0a051b01060f0f1409060a091a0f0f0102120a030605060c01020c070b0306180405010212040b01080f061510030b060d0c030e0d0e1504051027080607030e 69
    0x29140702101114030001c00d000300d034194814000c54421042c12031101d5640c40200340c508400e0300c60303d082d0a8100900e0709180c01c0540b41c05a00080c0142040c4035980c03120300c3c40d01280d121400720003851643c03601580c4030b810641b08841c1c0c1d014086942c6204040748200003581c40750414903021040c040454076001103070094000302c0c003800c0001d0101d61240100c0328154001e41104045000300e21170204006400404802120b008060140c5140040f58040300c19040340000540200d0341c83d0340c00c00c40c20048d4560b194a050003241718900784071180d4908810300d46080007810764101c041c0c01040912411303030000240303001c80709420340e09980714000b9458250b00800d400740103550401e000081c28403c48080e83e0054164180035103082000f0703131500c80010356410b1282d4044000c00d104406204482c85d0896280b06140074001e5410b190948030700101e484022441d4800c0e000c01c40c103c0300c0144544881d081005440825411503103000e00d0301c0082d65030b0752030140424044c1561961143d104007014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 70305137 1250 70303887 70303897
    0x1203181e030d03230c161115030702120c0703030309030e15040602010e0f030f1309060803030402090a2a030e060903031503060108100203060406050414150d0c0b0a05 73
    0x8055480700100c000003d00035220b6a0b000b4844076032101100c0649010460680740950b0a00c11a00c3c2451810940c4600e1145203e9040d110003404180440603560f07540701d10b4442c91600302c1d20b01c0e160700305101c0103440e042d076900f40c030041c981c000d1054030b083d8040020f40030102d90309031a001c209142030341010f81c1c07200300441301d680e001418180102c0c1880e4448005200b1900194020000e1001a500f4030b620b481c924585003000b0340041001c00d40c485441006001c00c0d1501d860301c0780700d05540d0030b02001260b80070b03804600c280d0001300402040d45000f01155a00c0300b00101c041c4140d146448504a111600800c440310100c030403148182c40c03900c0f035844051068503080444002e414400d4989a0340d40089030250b0000707682d401548020b003804182035040f02c206500502e468204e031039000c0c010390001010b95810036550071000809079141c0c0507280c031071500a580c810460801c2c899910204c0ea1f00001540942201e0b140e407000a103a54140304112804040c0a585071103051100315590312030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 70306387 1250 70305137 70305139
    0xd02090a08030c1b0102030705060a1a1002060103051006050f10020c0a0f0e010605040f060305090c18070905040213030308060a030507030b01080601080610030206070c0e151203181e 80
    0xb050700f540550000800c030490052003140c1d00350001c801401260341c0d10030000c2c010595000075020650f400d06940020311007828642c3c15041440342070020403000380e42200d03050016480000100280403081c0203034110050450380a00c002401c0c4808101c288210020490040740341c00001030301030b07209210103801e12a008050200790381c0e95405060f1490b0445c011000462002d10002801c94019000c5600301ca4400030250300451401c00b068008060003407040c0300c41c1c0100380101030740703a460a40c52840350142c2a2040c40c2410255001000d148841e004240920700c10040102200c248020f80ca0440754145418042c40d969500850585d0f01140e2005020b0700c20640d010081100604280341600c01c0710046a820743c0c2d9450b00203030346080c103035510803004550420500c09420b010009085840c00351801e0810503596003102002c800c82140e00c54040e12180c8110185842e00560940404082000660504c1502981400c100710440e580a01c81d01001e03655925000ca01c070741403104250 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 70307637 1250 70306387 70306393
    0x10f020f040503011a03071203170c0c01051503062e0303080402100903020d12050c0d0503010f0509040510020c0a050703030f122a0e190303081303050d02090a08 71
    0x2206030050440e5007090007894841c1d400d001c00a6100c10319184140200c40303004008216061800c4032070164480fa1502c00e4040082c141c2c48100c541d6403000d04d0741d0060039003040070341e0784a0034844c0d110300b1500003802c004803407240200c80c1c802d681da00141540e00304400f907042e02400300b20002d0100c03405210350107590903405004400800c4c10b401507030a522981c002e6488099800b0140411038500001c0e0100039403003030464500c0320100301d40398005e07150404541000d078030303054250303410078a0414001e140d2800600c000005011414007040c400e00184010b4584400509083d41c43c640c4480800040310401075010445040b05082007012441264021080d00c00d540e03100d05000303240440045021001c103121941c2d034090280c0300e100c0c8800c1c41010b40e207a84030000015101048003002c0c9000d0308204140741010181607501d241c42e408121f030101000074500c9196240140901000800926410780440707000404079400008490081002a10060742c81e880070001642c824169003107143d01d84 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 70308887 1250 70307637 70307647
    0xc050d120b0d05010501060e0616030305040213050a060305070801090b0a2406020307060501050909030306090408090a0806010815010f0303050f12280b060a110106030f030c0b06030601030210080603010f02 90
    0x103010361189050341e600340d8403908254442d805010711449030008021082d807030042ba88012074441e507c0b1980061000300203d114001e40b5410700c041c2c0c0c030b003a50070781420f9a95420030000c10100b000743c0700080115900a00c01d46081307850b2a094940b008201407461500d64845081d9040c0a001e0b0086200580d12040003c94580c0d00080d500e4010080c12034016107030200120345440c200303088038810f0701250000e61842c0e580e4030034085001c1001c0e004030703010101400410165580d175290788007c1c2c29224014040c541c9080e4990380b401041001d03160581c9101c02c014004003400003c440103030f075094200b8070f64500f03281e0412001441748103440c443d00e13141c61007448040401c20441000c040302c203041e5005901c4000000038101d030501c2c8425684001c040018000f954041c0c10b551903181000000003034082d6403600d4000401101b01030031400128921610410410440c8040e6080700082c0c000344007944c1076501240500310700c0c11a02d000d0100e1840001c200f56825000703031219901000d815500da03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 70310137 1250 70308887 70308893
    0x919110d0b040b190b0d020609010c061805012306010f02030c010f0b03010e010b0609010e060409020301030302010e0f010510120503090a06020c01020c0102030f1912020f0306100c050d120b0d 84
    0x1d603400380c54240392441d400281c98460043d41700200e0014500e454143c11039003040001e40c482c410050510103000e0041c00414401e2145c40e80048000c0c8101d0303c41c204a04d030003800c464014040d2440b00f05401240d940f20920410065408082070808110301a000c5d0320992641c084d03450120301ca507090202c01129042240c00c680c4203420300354024441480b64620880c2a1602038001070741044007400391400c1c5600c070310086944480082c0800d031420b07466074036403c1640d1098106802503910b40062002201c0104114407606801e113008200900341642d10104511061068500d03941160a00d00180801401220079102c002054400e41039640c8070b0281d1a00c60300020180903008550309426154008400c1303c0021020000c800d00d07059484123852150007221070118208440011441c03a181410700c01070810200c54441d00c1e440e4034010081012081d18406414104a010f03160480002c07000076441000300d090b81091550084118101c20081140d8000140d00c0140509001c040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 70311387 1250 70310137 70310153
    0x62d07051e07050109030e01080910050705040308070b06090606070503040e101502060105030d0201060e130f020904060b1504180c0e130e0f0307050d0c060204090915050919110d0b04 80
    0x85d040c4a03846075228100310b6001912401c00c1101c22400c0e917040007005000c080c1c10740c2e002c690300400e2030902c0c90400d83c80c1d8030345a0082d048000d0440b4203911080501800b407425540481e80304004580716450710318159110341e140d005503c00c1003c1641ca10020521112020010300007404c0800d0f01c59522108414000303544080a00c5094001d0041c0f81808a4242c4103001c0c901c16030703804140c41001ca4a40b980301014107100c0d48410b84001201c521910016a0b4400c03002d07008500404010691114050030041c02030800d914607810b14000b040100705400e818092241001061318000804803110b0a00381e508828901a00b54440c48003c40c005400700164810813901c0d215104031250a00c1a5111a07520710031520041d081c2d602512010030084e00c42c0c40da1070040c0e4030645e009401c1c29610407800c02562220401141d20750501400b0700303040045440b030b40d6070029aa00041240137140d8110076140030040701c014201d4220182811484d864524070345181503400016440c80d46068100710796 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 70312637 1250 70311387 70311401
    0x90105040510050a031406010e09040203101e1112010302010c060f06080114090c01140a03020c0703060e15011404020901200f0d0504050a0b0c0a060905062d07051e070501 75
    0x2010914006070031107025a80e40f06e02c0c0c45050181c503006102c07622003040000010008004a82c541f041c0c0d456404105400d00461101c0420206420a110364555501c03040d24070614482c0c01c00401808044e002c20801203045046a4080c00d000e1001c944c54103003980a00b6021841640301e50510030006403060741580300000f00324014400c102213031640d11a0940f03507145020040d000851f4004850108042c0c0402468940000d0a005140222084d900c50606426610030b442e419914464030122400c20b1111404000000041024543c1884410307990429414841405260301061065140c1d000f40c000b4208040c51400303040040400e12043c035074400e04e101e1045828020070400c13030b49060080007510295a8010520004103052119115280e048003091920a2150040000104030103110b040006400340020303100c540f800c00f81c0c0d050000e00008070703400001d0402c0e0001040c0c0314083c040a80000e058540766a0b20f01c40d030045002c1104008000803090307100000c10308200441544070348 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 70313887 1250 70312637 70312657
    0x702090408040f050d110108060a09090b0403031a100e0f090c1812032205060d0603170408070306090203010207020603010b07060605011106041b120302010e060c09060403030509010504051005 84
    0x8400f42e0385450511079111a004001807a0704405580d2024a6000d901519408a03001e4003065405540b03150402c161072201c00c01b070302c1d280300e50428001410b40c1b40c054a800003140c403c08400140320712020640d41c200d06914007041020300b9010307036120350728015000c5442e1401000540e1509040d10002e000754496000e88820000b540a8200c6504081e01a40c0c10340018601a500b4041980c41d40f04100b4840101007040c10081480860181d0340d0b0009012940b0b640c2400040309800c510340381d540300c44100d07640d00c11824240300400600200203800d2068941c80310380800c035001c9a1020178064047e0303041c0294480d00100004c129800208064410140249400d00c8040c0d5944010740310f901d20440d041b00150030444c0028041840b0000c8a160910f084003007030402c2c0d66444e074221001c842c0c07182c1140181d4580003407403d0400100900740e0801d2503a00d01514040381480003c14521907844010b082c0680410000b800742e000d1011341e001405c0c0903000c4400c18642c0310008003654002c03a410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 70315137 1250 70313887 70313909
    0x121020d0c051c0606170a0f02071b0608010f060c140d05070c05060703050415020a06020d020c0f06060619091503091a040c050607150608010b0a29030408070209040804 74
    0xc4044000f80d07000b00030840c1c00d1a1070792010054440195150500b005154545039034a0760404801d2981c14402000c1041c082c0700d406059209451140c82c4540c4654032450801180100601241d0440080507007101c01600302070170424071900d40400094940d40300038520740624807007a0280d075040402442c60714810031554420503207030410030450307010b00a0040d00058003440240200e5944505e0006100b0349401219200f0806541c0d0100781d0744000305c1995119004100f503900c4000030464001c013100b010000d8901441c0002c003103949400343c01d00386440d04c21070048180c0d465024031090005008481400300c13003034000110190281c84190300c100d48041055030851032640e00f40b005903000d16484085d5154441c945400c20005401100e030aa8040b10f001d4034100ca003083c130b881110300902070800007040b0940788008004034245940e201441a07c00117aa03c02c5911030000f048140c0c4503000790290b01d13030b100d50800810f10700070079000035085400c0005000a20841074060801c4440050700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 70316387 1250 70315137 70315177
    0xd120b09040f05280311030c01050a06080c0109050d03030507140a0c03200a0201080a020f04030501140915040209040c03080d06050f010201020f040b071a0412080606090121020d0c05 80
    0x1c00c07000c203441c00346124200800e04c20b4000000b0302c2941c00f01c561110728021281170603803038a421400c454003900c0c0c52420a030350354000c01c141c20092045085809090074102515450a00070a180c01c01c1c40c80d0060405a036400040d07845401041180500540822010b031958001c00020300003c0c85807600f030300414031482e003031642d0040030000400300199141c09000342504550040d078182030060a11f90703480340c09210031140011018041c2c0001c501170800440c02000840d8180e480d10b0300a003840c111a0461010140c860280b04105a00f090781614540c03240c0c1c2d10340c24610511130380c031781000701840740c0026040c41d0310a51350495420f880086644920104c0d07140010390803031240c1a00030201c00804d2008001810640c0c0240c0980d90042d0007210705019070164100c041e100c122012140450748085041d80540d00192580c0d010b031b010f450311494128200d00191809001c1c081d07824800460740d494403111642c903010b9074455071050340144503149000e00041c1a41d04603401140342d079407030781c28 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 70317637 1250 70316387 70316413
    0x13261e01060f180f06080a030207030c061704080315060c10060509070914060d020a05190c1e060e0d0309020f0409170a05040f09090303050f0105030d120b09040f05 72
    0x1041c0c0b0483c0c0c20440c081c800240405260030140c04c0c004640951266100000110104148110300900d8030940c0902421801c0d40b5008003c03114640250040158918061442550384084940c22036000030340e468680d070700d000340c1d4118400001281c642041300400c0c1600c00200c009824031204150b817209010351610b8400b802450f200c129409000109940002c10040300c0c0d8800051607040085c1200e407419150038106426a8896104400010000034070034044150a1250829070403103403600b40310103022501d96013054403e007103984640903500c1d4007000810880c0c0e80401304120940c0181d0f408000c00b40d001600804c2040c0040e0f0203503025510b160300c1d40c9080e124071034116178030900c14030966010752a80384054210500303103000d10100704804a4104414940140100703400701000c0741d07000ca585002000d13940301034909190060403100500c141d5038089565022401c2034a41a20900d400d04101d20140424980080d0480c82417818031040c0b0041e01d0401003080e0041040700c0e550b2000386 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 70318887 1250 70317637 70317659
    0x1e03090f010b010f031503020913050706020102070201020a0b060105070b040b01050109052d03070b0301090213091401060302130302180a11120f0403120e16090213261e0106 76
    0x542da14000340141d4142c040c02e83c020b40c050480c00305500d0308140c11a4a0382c3c0421900441070b81e1042440c40c0300e1418030208101000a940604070a00c001c1d400c00744641c0c0041d540707441c0c40500500c1844604c3c001852a4425019120819001080380c4014281801d04158121080c020076000561600d030114042c00e103200821500454401034452810f05020680725000c11031110651602400e40000307034840749600550301034900000010f0340c40e144074260380c0c1c501c040c0c1d5001c801c8490500c52032180f100e2011241e541103031b82900f80581e0741c0c0703402008401c8410309600000d5018003e45000130020003c008550701c03c20341c0f800e080104119002c000303080c500030015072840710b005180014211115004c034940e041403003820030080d182204046c0d8402d40f0300e0804650560303070004040e61005143e400060000700b180d18811440c0c903540500b04180c00741c00f802074045440c46003094141c541101d1101e6900c030314508050320819a0f081e41c030000b00348040b40541c0040d40c00d1480c0407a05141007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 70320137 1250 70318887 70318901
    0x3110301060605271306060e0f011709030d02121e010305070b0a0e060403030201051005060c120723160b030105130f06170c03060a05130f05031e03090f01 68
    0x1d84a89080c61361445401e01c0c62402c00d034001c0301000300101040802c2c0c42d0300d000b2020b040300f002c0d0003040c3c983c10200d0080841d030880c00101d20a2804421000132a604104c040da07002c1c500d80242503551386d030540305920f13512880ca070688049100140065002c114625900e01903501d80405441901e19040c1c02e074009042800b02070a103070005042000810540d9000702100ca555050540b40708001d00d00081a58203d40e0007070700542d445104211a1900340050403015007030403280541014010100c2c907540390014440c941c40017200140050070701c1000b51a01c104c0185114801001c0800006180d46a00400e18450892a14a000428850b0310801664143e55000c1e0400b08542401c406074400f405003080410001551210041881c425017031520407035080079001410445445000d0619083d03009240c81200c61400d000c0c0301c0342c1061402c8100c400d030b41140c1400c00303007840313814640c0c00d51040e4031800030b2102c52903042e600842c0c0c0007000b6501c206a46001d40741c80d03c1c18120700a090b2614 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 70321387 1250 70320137 70320149
    0xc030f090a12180504270606030c0306020a020c1005030703110909010602070608011a0f0f09151e070506010b09030f070602010504060b10080f1e0906151c0b0c090d0303060311030106 80
    0x14424641e0b041b071454039800c1301018010341c404075000d5900d403503a060a06c000e400a0f108640c0001d41d40c81415010810b01150300000da80a0741c03500c007800d10040c0325003c040d100d40300b0161291007002d8516802000c0d83d404c440000e20034052542c3d03c003000317540c5102d03502c105c002207883e9400008512050300140761059a1050399145803d001c0440782116601030016174031039030002e00880703105445400807002001158041640d1390440c0d4280b80c1c100e5509032110764001031003000100002403000c41d01504540d00149156243d0a040000074105809501e20030007611940c540010300780e5054000500881c0200700400c40b8503200e07000e10040694541c84040811090000300320944076100f10140e2040000244001070f0001607000401010b06540c61176032644078400348140c40329034040d543c20340002203540454112003d802c00035195281e5038043c3c0418042c0000445560b039080440e43d034010024a10b48800c5081d01e405002807440c1d000690340340505803543c4690381814802c040603241 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 70322637 1250 70321387 70321421
    0x50307090308091c030806011d060d0207020f0607030e010905150a080601030e0a060203010f080703020a030807020117090f07151407020301060906060809060903030c030f090a12180504 81
    0x81103840e455141e03070160303099503081350030030070660003901c4980221501c05100e6581d40080d800d103030f000105020901c0c92a08460f01c0c01050301c04580c0d4485040b2540f070b54600101680300c4480d0b0000508040c00c0005450b04020002176020415074006000c081231202600e030064055111024007099600d420340c62102c0000401c40a20110301401005500c41014500850b00c018207818036402d0807000d403404c84400f60003200500c138012118000c40d0207030101e44010f0101614640001e01c02010034803000e400101d00158403015079208075020703c0d01481c000504092030a0405032030f50380c0d03805417040107001e0040d50713408290000741d10850329506860ba5a88031180c002011240a15482000226890f6603108030024008529000701e000900490326522480d00d4034600090500b10300034404c0030250410001c0020a0501030b0980f074004049404124259480c84a000d1800305d680701c000d8240d180180190521135407040ca00d4103103031046a009078201c0c1da10001d00007030f20008004848001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 70323743 1106 70322637 70322639
    0x5211e0615010504030b040f120c05150601080712090b070905030d03090f06022116030605010905030a0204020708190504050a05060909040210020a05120703090605030709 75
    0x30490061a541d00c6003441c000800c240704034000140750002c250045001c2c0143c4d2088205140e80c07050704201030389a141c6010782180b40307030103088440d44114040046031100d40310155000e048180c503a4201034036840340c15a001c07500350240d0580036640e5520000401c601c0b50000d40a00c1c0d054461416050400c3c052500704590341810005050401a02c0400110140f0341c218403103420880c0140c9070310000c40c0c0311013802012100855a0100107040c092403500203040f05c070309441c50703841c00c01a5075920001510a64000d104007a0705801c90100c110241c00c1ca60002e00b40184111141c518050b000070a120fa0710302d0442c07018000403004601032125041c001d0015002e040c04981150900300340e0300c001500402d005200034022a05c0c8021000c010f4001c21080c07403c00d500000751201c0c844180d54130051600300440590000ba03c4d20000280c880c011402c4901462442d40d035440b0003 = true := by decide +kernel

theorem cover : BRFrame.Cov 70143887 70323743 := by
  have h0 := BRFrame.cov_init 70143887
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 70143887 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 70143887 ≤ n) (h2 : n < 70323743) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
