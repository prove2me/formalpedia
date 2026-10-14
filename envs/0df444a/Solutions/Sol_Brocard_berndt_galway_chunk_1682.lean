-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1682
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:12:21.075098+00:00
-- url     : https://prove2.me/submissions/e9a44234-e0ea-4ad4-9595-953333735a33

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 302338129 ≤ n < 302517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 302339379 1250 302338129 302338139
    0x302060105011b08040b03250201050612030c060a0f090c08060a20160611070c03050106080d0203030c03040c03020a09061401090b180a0906080a0b0702061006111c03140106091802070c 81
    0x1c623624044a19005070745070403d201e0207003070622102e0b000c1c60303c40014516180b02413040666410000d130149601a507190401081440294031401c4455401000c00c07040582c3c070110383da9910001c0d211001c62526049041c004040c1d075101d00b504100c0303082c0030b0504000d035421400710350a01c044801d552170358450071103408201c0e010380248541c81c460140c001d0443e0950500c0344c210348841e0070600c002d601c100c4502a00c84d07000816240d0041e40303d51582ea5a56507440c14044281a40d40000d400083c0c0c008045200e40c403540041c01501d001080000003682c0c81401190b403080c8a210b25035000400304881110035860702280015410003821800000769900b0005040f190755034010607154000103211410403000b50049034101c003040c0b004021a0070f11645080c0060403230b00c02d110070701c2900c10300844c902c0e4033808502015401481c40c01055111005c02070f01424100f2080406c50039200c001240c3c050103034a15030180d42406483c4640002c0d00792024000354440c0c1d00985002c0492000007032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 302340629 1250 302339379 302339431
    0x5101811044e050a05060405030706050915010b0c01060509090c0f03031305060d06091103040506060a0303081915030c081902060703030c17040302060105011b08040b03 74
    0x4000c058640e4035016421450200103486054624440388400103800402d40d01e81c100d900d04811080b1142618410034402c1c64038602d4640c140e070f030060003070040d0410002444004005802c00f1030065500703104035518400740a40b50002c000400b0f0a5107886001405070b01034081c0904030f410020800006d03200d40719070020310002ca04640d08800c0c1c0d0300c880416006801c04c2a41c415103802c1c00e9008500380020140014008407890040c14094400465003c1c2c526089070071030f60051000003010840800c501e01702005a503c11070b400e8941c9d1040720089000d40c2082019002202e4250b030714004140c4801414000403a0410070b079030000d54403030000d40791307410b072407203856009511031810152000d1406c0405405c3c5401c1c900d510760000d44041c0c9090242c0c41e80c104481c491503140c64001020300c040340c0c050b1103101e050701801900300c5001341040105a00003842a060781c0f804d8894a25801c201000d0040014860100601b2107100388810003003951010003560b00800b4110107034228108035444c0720 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 302341879 1250 302340629 302340637
    0x30309140a050303100b1c11040f0311040b01080601140903010e030d0608070b0703020a0b07091d0103110301090309090908040810050a180506060d02010e0409140c0405101811 77
    0x30b0703040c0d0000414000130504010b001c0c0000c09900c40d0550501400094080c1034030180d01c00c4862aa890f1031a0541440c01c140072100a814003881800c50f198903400c14001c000c00343d0b101903015a26003007820180c0d60007510740a10403907050f1340c0d4607820f04444045100f107030810001650150348405c0c843e00018000d00107442c030300c1a800710010f04185040c120b02c5c50040158002c501c5014100800f401081d40030481412140c0c204002100039100c0103000c4580c2246507104d41d030000080035007a14000490310031541200e00951a105420220000f01401c0750845900280440c0c0007240410062156412954a007401082c4244c103090fa5aa04541809010100c0c0d4a0881c1d441017045000616889403001c40c001c14031030b01c1c59807d81585c83d0340e540e01000d0300c882e10a03200c80d00c030803046a110301e1001001020140040c0b1013800c151134000d4203075102441c2089540561213081c1e0940c2081e2040038443c869008407980c07114070308007486100c024980c11011600c0d8403400340740d9034100c00200070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 302343129 1250 302341879 302341883
    0x70902040603020309060a09020303300c1c05010b090922260304081b01061509030204200f180a1d090f0705040e0c122407020703030309140a 62
    0x150740d17490f0031400282441d50041c81c000c140c51a05401070050385000045c1e44000d4241c0c0301c903a440c4500c0d910b082c003103d8040144448c0358840c0801308461803200c81c0c0500444161005600458000d140012003070301c4090240b1644040300388011402d91900610070364000304108000507401c0c01c3c0c2c9280c0740306000c1c10786080d1000c480308040e4454080054420715540d8112b4026981141003d50b100780d450702c20300c001196840c086a041400c458000e43c821002009405603010246448410240102c0a01e2105a1040340707400000400140c80b400510000504101c04c1e920b030101d0a0741e60f201c150018225140700d43e9042e4107101003a02c5c1d000980d0058a40f4891151310410814200c1800c100000e040038003030380040d82e080304800800a051019183e0448001c2009440c01052a2a014800385910303480b145918011400c01c0000c1058644010141c000d82c3c00740700c40002c944040d96064410b100103901100c8208086440b80d804640001d20603c08408643d05c003e05080c40c082d40740b072003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 302344379 1250 302343129 302343131
    0x30102030411090c07031d0f030d0f11070b07061503060f0218030a0506010e1b03010f060206090703050604110103020706092307050117070314010b03270c010c05070902040603 77
    0x150b0709552034002c4040b58410203001e215450105039580081800401c56281a800111441120242d986d4010f0007086148003070120703125071021900007031816590070149408250995408411400085585410395421509052030301c40360f0b82d00c0304010140e04404803120700901c50f011001a4050243d0040d01b0030031800583c454081d0081e4400540c10307035040e5071099218012002c0041d5000c200c980c1112241c41d9544015641d5903a00000b04013400c803140002040000003156169907844100306882c41ca90884d00150384a100181d51070200f030001514550040001900007081d4420360307450020180b4000d030030300b000c41c3d45010540d9007800302140c048400524102d1a52840c407611094403802c00020700800d450500082e0000402007440340703000307460b13200158100f4003035000300000241d5508000502e60f580e0092555135002500e1944503201c4428012048140c10385800a03074400000c0a4a04c07031111400540314000030071421034041c000c0e03c4000a9440700c91000d000140786ea610 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 302345629 1250 302344379 302344403
    0x604051c1b021216060513090c0e10091508010e09030403020d06050a0f020a111005060a0303050306150703080108190c06031a09070c06060504020307050702101205130203011401081f0b0301020304 86
    0xd100c0c19100c00e680208423414a01601210711a501c008030181d0000c00b86c0d040d04c1c0c1c3e000649001c8410111a801240c961492000c0d840c103a281d11981150483d03615614941594641300d036559100c3c4105c0c44040c0d0300504010303491000c1149a0302454000707480c031400041610100b95128107a03000354240740045080c404400c104030702c1c14044586540200b600070072035860180d0000381e018050b80400341c03c11401000044068482c0000c4e00780c82c20304101403d4554206240041820030b003401150280d0246101c51031085d8280c07c40744020503400340c4184545030900804038010600700c1c2c03044000007482ca03880b1240f80c403420111742c014043c550b41c114045115040110556a142c1d1120340114410403c11aa25038040c05540500f030381111541d44044050408440c16000014001019484c2030306005507050900e1100030510b01c00d41c000d209069034170b04900031042d0240f0135129144c200d40780a00c3c9849030040a00603018091200040100720407000c01e0032608115021250240c42d09 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 302346879 1250 302345629 302345647
    0x405010b10090b07030c060609051803090604030b1e07020105060102010c02030c100902060c03030a1a09100e070504080105010f05030c09011202011d030604051c1b0212160605 77
    0x8050300c246035906894a0301c0500300034400501008040c400c3c00034100010a44004052040c10705800c103a1b0041000d00c14981c13203407001002081c098a4400c60f4a081c400085d0f00e84a0205c1920104070004003c03608041c0380d52103c1c101c08500400c4214018142d0700280150065000024010305203a030000440d0700c0c0003800a0b00b180d0703001d003a12043d0741c4103002480505900190400814200d620041a240e085101280c10b030f00412090f5030040c0400310070001f4441282d40704004c40c0240a6001040704c11100070301941d060140c50628606008180c01c0c04199030304919290001014508a4075082d915140c06007144c00c284c100000d0311446507004c2207035250411a83e110300204460705800b0b940742403040d1940446500d4002d042c8102403c00c2d29100c0d41c0700d507140c0111000035040c1d030001d11306231900c0c940320480003071a2420142d40c3c00107281d109129074009c40d58441c4910449101e190560200011000a1407002550340305084120f4040c641c0c105c034035001054144c0325942c85503010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 302348129 1250 302346879 302346881
    0xb180d0b0604111e0d0207020d080a0e0a12021203090d0f02030606010302040e0f04051c03140a05010810090632071e0f090812040314060408090907180e040501 70
    0x250034143c0410700501405140ea00780300f0b24240c030780f01100507081d6140c1030b000d4030b04044d020b030305c9010b50b000d980900c4a10620040f08010603e0349000d0369119000e0860340204103100304940521041b9901b2080c95200504203070107996145102c43c012a4101601d01e0002042102141c00450300d02400b04503000450034100900c540180d0242025810507013042025403c00d800101541c0e1410142c2000c1000e1010a009908010b51503008500307910704188006005000c404480b2000030502000007108452544034660582d408034015100404151070315001525040d41d0030307280150f503811217240c6004049003100030102c3c01444814151188003582c0240d0500604000034010b25030003d024501d07109031512008a51418065405e055440707084034041e6183d000f0942612440900c05045903032040600200c078443c02c1055280380f00300d010750740c684c001030f18001c1070340000340170795401440c01411302948118140f9004010f0183c0d5510048a140c8541c01044140c3d1580309100c02c1c0502 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 302349379 1250 302348129 302348141
    0xc030914030901030506031b01180801020406030e06150306160504080d0228110112020c07060e0f01170a0216080a080711010c0c120e09010b120105190b180d0b0604 72
    0x42180030701f07200340d03c4c02441e403d540d223198011030410802030148210b49500c20100b07800392000e0b00086458a48030500a0014080305880c12114844c0d803001900a258917000001c202801038098496903d40c4c1d1206a000300202081c1c03000c5c4002404080b40c80701042100110320002e5600802e9000b4240410b044e04181c0f500c1c1d4040b41003250b801c0315004c41d980881d0714121752820b10302040700c216001c0d4000000c0c003c001c1c091039240582c500028185900510901040b4030884200d90290364004c015181003284820000c4059280c400203994002540d006d00500b04d020b82c1c1c1c0900c01c00d003e942d82c0d15958001d07004000480e1000c001e1040903680064011b12018410001300480ba111400140c40720400000081101032041c101d8010944268603114000c00d0103490544656194504594150040d40100c0c0305589000c0000500d4078000d450303241c5201208100c50821401c1030f45032500b692011000d102c201101b04074083c0c440d143c0c14001c4c010703107000310380e50180e40c20030700208011b5504d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 302350629 1250 302349379 302349391
    0x90304030f0524040f02090c0c0d0c17071709010e0a03060c030612021807030f09050f0f070f150c1205070c0b0903191403070b0103151a040c0309140309010305 70
    0x1405030401c40040d03c5d90950781040da030102c441d29403558440445450500c00c2d0707071443ca004e001d40c0158000c0560011504030782c0c01e20504c0300c4807020400f070a0781c11241c080c068020b8000280ca0565200c0b900e40c20004140700340b0185058003050340d00601281681c0d5107036104492440d0380d04828801c1d240c0c90b214601c00381000c0507050010300c40a40004244641420810b0307545254200411400e5019600c260014015180140030313075003075410400d80701c520101d00600d181c05022000407040c0d0021440c0e038140c440092441c400c01e03081c850020b441c80c201000e28014001d42d540700c1c50101d5142c0c0d443c00c00c0b8420a503545c0344d607450319181c981c06000c0f5940c4064100b0754107004034503240c1d80c0401c4800100100842c0080008a50300300030b032285c800181e03415040e00000032403c050062804d400b0341640d00503e101d208425560204104641410200d000760292000b0340d1103c0345056000041c0c00c040710f2402150750821520b4840302d200c3d802c800c51085900020f628030180d605800341d02d40c450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 302351879 1250 302350629 302350693
    0x30c180406150e0a0e0108150603070e040f031202030c04232d060c0f190b060d051f0209190e0414120705060f0c13030308090304030f05 60
    0x3490881210034000316488002c040c402d16200710f00b160f446003030182c8000c0443e2441c102c3c01c0d59455840c541c80c1d02c5048520500c80e00101c0000c0d21506000509000301c80c1a800e100d02640da481e207510a40200c281000c0b010403e00000301c9050500074000356000b49007021940b03a44a24103084542400103148840240d1403442c00544040e545541c10002203000c81c08401000e00790078490020188503030b2a1302c40d884003011a0b02150780d100000c02c0b492a0441c00d04407030321a41c1040000d83c0c0069020030042021404000151847c10481e45050115106608852200c0d444c024183d04a802012160304895404504400c541c6020070046d1203805109904004080c20021028480f0b40000c0028110101200d54031448400411103010096490000f160700da014038a440d03515490306541440d1038000703100100d0098041d40086074056050440000c2815146035070030b85010100403c2d082c401d0000780400004250303d07180c0850b20354850301c090711082e0031070020841e107034100301001c81c1c802d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 302353129 1250 302351879 302351891
    0x9080607020d050a090f0902030f010e040c090f0f140702011b1e090e07030603120801050607020409030311131e15050304051f0902010306090b010504061d0303030c1804 74
    0x41d80110391200c461060b80350a5640795150007003a07551801c3c41d800700c006c0d17011065000601e012103501450045031b031103410700f8046e41d0311101e0071000c005c00c0c1c50207890414030f4601005004c18660005491b05030308040032a1011111544030200e0715403035441c0c003001d003169041208165081c81814600c140c0c03080201c244034249400100440a91301a1000040301c801035819864000d01803c0000d214440d1240c44501d00600c000f40608810720003250261641d107103182c0389a0003004001e068481c094811814001d0913000c101c0a0420006c0c25801d00d903072102e0a03c00c3c4a13003000145030214075070340c400072558640b41d141101113040c000720041101042c00180a180c00c1c05000301e003a10458907103d600c81d06d9506125007881451407503601d401c4451004103010804540203941c6680c000d890801c80241e549005005a94801c0896400100200000c0c0080e0f405070341d156034820180001c07642d612b014100402e103503034800e8800b81c1242c040841d4562008a00e01d0300410401c40075902070181d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 302354379 1250 302353129 302353141
    0x804030501050a0e030a200a1b0f050a05061c11030106111006050306160e04050a060e0f0f0c0a0c1703060a0b070203060f06010302090414060f04090b010e07110105040b07090806 78
    0x40d001d680c51081440147d800c188140e003001088048074040e00407040346c0d4110102064000041c03241c2c810061440400000000d0514020039810111388010f811285000314189100d084400301a916a03c5260350310700780c22158145c0c0015601034001621580003a00c0488810791030141e08c0b00c0d540011904120051216407000b00d000390b04001d00329080b00e401720b803c1c9015a9096182115540c200e07140c9010444107024136000703641258112002d10085480e0790a8503407905000300c85501e050b650140125038a0304283c07009205002c01c43ca41107039054080c0c1c0e224001c2070344101c00310403041404024040146803000301d40d00141154100303030b80b60603841c1e800300f81c544400400003043d00701250002580c6074042d404036140710758001c0040100d410950840300c041007080e180c090240704140d028035100e082c54850000d030207802c000c1c2000c182c3c1ca44210b5514409008054900b0002c20750680c0c0c4420500340038003401140b14070ba415500c0d1030301c01d01c0140718500c20791019429038400d400b03001c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 302355629 1250 302354379 302354387
    0x7230903101805150a050c09010c0212070f0906080c0108010e0c0304031e0f081003030507020d0507030c1514071109092103061507030210180804030501050a0e030a 72
    0x11104440103408150002030404030b10320000440c40181c9580070303240c1e80e41d80000340340c80d0352440744484810811103616020b80143c40381c040c22428601240c148a0a00c016151a4091190010041c1c0441d030b041c98649400c13240d40181c1d50701000c1c40c141c075007106025580080c00364250400007072034524815890a86100840c200c054017881030460004003003010300d071007507450703100ea22020a03120008210707084004050344000140c060024094902040a4141004c0d155044940641d210b41c00c1110907001c1000e071140c040d504580c54403c90704004001003550392010700034800a19400048200c8442c040c1031544840700c0c80740b0280702000110300003008409c6880d60000d00b518200c01d140d69003207003513260103012a0b51184207000141c41d040c8103000403000314801d030382c10348081d0400a00507030701d00150f0060840007805a040440c450b04550107640c4680c0040803044241e065001d010380b14050980d000740c2041d14a41d464008206000501d0b019002040c4d2151005500e000c4130100024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 302356879 1250 302355629 302355643
    0xc0304090f2016060f0e0c03010501091b140d060f090e03030403050313020d0803090a05071d011818030c02101809020c0c03070603060807080d091a0c0607230903 71
    0x1000b821a40c3c081444000d40c00f407481d403038a000042080402c07106220340e540602400c400d1081d070900b40041003c10003030003032000103008101c030f20504501e006420b0760129a00005420054001e00c01004150794030300504004000c054035000c07200b0b041404400031343ea06a40940020741c4100184030020f0741c0b000440e5401311051440404800840c800680c258400440c0641145004030034044050350201e2480340b038500c01d0f011100032503946c010f1943da400b9900f2810030ae101051004008540c008504180580c04007440001e01c445d610b6020808072256800030f40c001011803561404504081e04100c03850000760400c13402100a05051407154030039800f4039105103402050340e880c040020840440c4214000381580c04651729040004c004111903c206c81052203100e0740001c0414021844955136201582d42c3c0140c02c3c104143c0c00e2003103440481030a80240300f0000c021540030280540790081e40541d030384040416041c08850554801b41c1d54502000c80200800c464a9600251038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 302358129 1250 302356879 302356897
    0x601050d06090219031104271b0e040302070303080109090f170d0e0609150403090306050612011d060c0c1b2b02011808150c0c0304090f20 61
    0x200d0201030b140b011422041c10020300c0141440ca10720003104011030108094582c050a9400300f0981d00c0001b01d01009440e040c00468220805102c50000710302d40c80c0342540800c400003490132902c0e40d9030300c0b0125103220440e800d030016080004107200b01607114448500410082c2003d02501100e6140c882075040383e207100904000390501a11010f40e18003059032104405600d0030403041003168101d81e16464210751325600b41c0218841388003001d00707003548075020b15010764580c100b803819513030740000500740034103425800000307845007030301c0141c09019240008070842440b502d17554a1183c0d89151003005801081440c3e01401125040c481c0061004440583c103490918820106008103510000307214040d040c0e85010072803407011607003584000003070034030070380c0d90442485440b400f89099441c2c4d400740000d030b80c103d1204000e00c0920301342040c1d0012480b0040c1ca18051700c40d081d0700d00c0c55000740d00c42c3e00000d40754001d131038402c1450320500c2114103442450b112010008040c0d0741d2540714103000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 302359379 1250 302358129 302358131
    0x70e01050d0c03060506070f023307020105270109050306010503030706050a020d110c070b0711010c0318120b1b0a0f030905100617010c0221091f0807020601050d06 72
    0x4034499207031180d049003004100c003034806d554a00c100c4c200310628040520040e802001e560001950010055811380d8891400c420404040403040804040340c0e4030a0405a040000902c100c4c0c14148132040045c0410341c01c024013420002d000e20008d003981c0900d80c0603034400c1d0000001040f40da14003200b201c9280e54415000281d541c2d50418050007030003244c4680b811140381c20701c801c0b1281007000042c06903a15860031681025942c5880750f44031b00c80d03850010700c418007140380c0c0c0b485075028031079120324240302c0e080441040c10707001d1a048905045a00020040c804a131800061001480120f034000c10805102c0488000d121960100d600c44c04c400744d000c000388040020000c41c481d80c000c4d00641e81c400c05907003107440349294140242445004121392081241800303120108148110380d060a065009031007441d950681c1c0003d91094034515841e0440c04100310341b21341e40c8030103000d01d64100c17401e41141520030000e0010034286005014105540c44800148003a54034075070075210607944500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 302360629 1250 302359379 302359391
    0x80f090103090b0109020c07080304050307150507060516030f1a0108071101050c0d0608031305041503170403050c01050c0a0b040c0306050a0b01030b030102090f0f0d0c08010b09070e01050d 83
    0x1004030014a00150b01500c03450a00c8004910070100b034004045100444040703ca230940c845e45c14079101e2240b0710071030740d042e070192104020171180d080ca480c079140d110341030080c1801c4071511074805a8104440040780302140000d80f0183c5a014812003818214480c01040380b014032080c00d06000b0000024141805610400200803030310549103020101d60020091110307042c61010650315810400030701605030300345880071070103040c00070558a01c2021090000c00c00c41c5810b061000138900888292000c403203081c400720201c3c880d42d901030b10084a1189041e0b503076103542069820906082070f0385040040c10080059410b40c0003402e804150741202946915498600d440c01700300001d6072008007514240803c0284442c800d50201d505181700781c80500000d0308240400d401c038400d1022603030f401000d10715410118203000e035502000d1200a05488042c3d82030340c480522580d000c3e4001c2c1041d80d103418002060381801c58100d40c0200d0340e41805805007525100103840703070081c9003000ea80255641 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 302361879 1250 302360629 302360647
    0x7060e071203020c0f0906182d01080105060d080d0209060d090524070f1d03071206060b0a090e040f0c06050904060e01063501170c010c080f 62
    0x4049440144010007152480100501c1d02944070752102e40d00f9407041000c002010b44608180d41c5040c800d00005240c3c0140a104c502e40d214510320240c10480e44601c4001d51040984205038003c00000b500c3c01c00403000d41c90100d850b03094800040405004200048548002541d110305441819130000c901688540420002c10607078054803248901c81c9042541000a020001c52103001e842502640c014441e503840c031000c0b40e101819100d6000145001c610500c280d80f1030a80c07040e40c0f507200e030390b0004080c600c0c40000b0314106d41600442c2c0d5080b810f1124000f004024450a002007a00c148614100341c0c000d9005801c42d003551027803e9562801000080400010301d0b480361070b4a5110503c2100d0584401c4000c14581040da1564061480c1150204100300010b107003504980541c4c2e00c40744480c002140f8288030801410340b4400300019558010503408140c8506800303002c1ca054510701507400d001d20a480d02450484460600441c140400d0125000c601101c0e1070341c7d0180c100307a41c2d4800207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 302363129 1250 302361879 302361883
    0x4150312120f09051005160e0a0b0a170109110301060c080d0501030303061d040f020121020307390b091609020a020f06010b071716030e0a091107060e 66
    0x10020000381c50319001120000003807540c0700d0411640601d0459080840d0b29504000300c5006640d03c038120f82c000304064200600c2061481e0000e40054090400700b0750b00c92404250340c01030600000446c1d078030501d01c044d0924a0360114018008024248035444000b81c030007400d03100c180a6403080025080c9244280410760080301c5280d020007108015641c3d503428003c000301058011b1100550441a0000b40180d559005a000b545c01c42210f1f40781000c0740c3e00540e41c1c11082002d0182c0e1080f400007803005094248041e621800e120b0b1260300c0c1c001ca030b0490700500b0280800c0c40349405078081d803440640c000800200840075911981c00310107511566603d901d45441c110108000c8443e808000c510200c0c290080c00d000107003a000c40d1180238201200740d0722154240111900740100307004080204c2e4800014030b502e520f41181c0a80340c03602508505110507210001a0081400000220460f0400c404004010300c071141040103800b10221440c7d80e0f07882024400381100c0d8851508522282003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 302364379 1250 302363129 302363147
    0x30612120720130e100e1f1b020d0f170703050a020405040903020705090a0b010203030f040f020a03050c090109060503030a140d1e05060603040206070f0606030209090102130504150312 81
    0x4003039000b2003401c400024003404403010000603134002c0e001c1741c5030002070700c1c0281102d01584030090b00441441c401c106042c10700b030040110f2059211a100e60300e54101041d9007003125030399405020050006013001d00941c2070115501c08100c00c48042d0341c04180c00310b0320b103500b1000c10715010075680c0712100c1403400ba00441e00003a50152800c0649000c25030006403603000c840007501c550500d95103e004036070464604061140c0944c20401c00214844030040c0c926074841e20441d8000d03643d040131f40118a203001e07150000c9070223500121508115182941856004004191041c03202038200000300b0307103d0084000910500150a00b161580c10888050781c0104010341810030840c03050030540943c0710564582014a20b14080c0445c00c09c1c1401000c4902c5150060241454211f00e0794592114110160090301c0d55941c884002c00182c0d00d0b42111402a59013a0025071580d20030390308800c0c1c0601590180d4410b40c9065010222038440e0700800301240d411455455901d0000102520401d823 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 302365629 1250 302364379 302364443
    0xb060a08010c17010812071e0c180f0603050c010509130f0c09060504060906050f0c070602012c0d111e0102041a130302090a060504050406020306121207 67
    0x10078280c089160030f6004a1403012044240c0c01007001d13982e213000c51500c401481005220480e010040ca002159141c2250340d114000d2050244051002e611520400c5040c0d03041a120a00e50718140d05c0e90b00620301a60071481e1541100700041855540c5051781c07100c078491600c5c10300c0b0700810000760030344d18050b8960009240c0c54090100c4030360344019070020000340001001107410300b2000b1072568030500c2900d00b40c0d116902ca4041c3ca6043c54000d44841d0000c5890007840b1108210655801c941444a50001c3c1159000860351039005025108030304a80c401c02d034076445d403a40ca042d07480c50000035400444071560420702402ea2a002c013442c00c14101140310400041d8040d01e0740154641580117004680d03d4407460200204c1061039100c06208191600b500b10030310140a20140c82c201d0002c0c0e0300080c0300007001400035500d10119003a280c044400f80c1d062a0302004005803401d01070083d00140c2e6106000e0120048030021151081c00350340b4028000d4030a190905481d09600382225030000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 302366879 1250 302365629 302365631
    0x70e1806041806090b011a0f070206091c0b01051c06020901020a14070510032c03041505030417040b0703050c070b04120c0501050301060c1104090f0b01030b010b030c04030b060a0801 80
    0x1100c3c00e104002c2c2c0350002046401c0442c1d11700002e80e00c00700700031942000100300052407900140316108078144c3c00144050ba8480c60801c0b0303108031075903400c11207485501c40b01d803034140c00304a41c18203030340206051388414010028108848441c0c2d25908a03440e0700355001200507110f580d11030040b40f41c40d4282000800116007403d10064400000409030215102180d21034900e01003450110261102c500d40704102240f070141044a18040c4615400016401001c0340d04040d40c0c1c41c1880c81840c441191040840c02c00420702c014071a4008840003002c101d00b520615180c40c11840c80c0f42da21a42d0790160400001241308468000240480d000a0480d495050340b100c1c1c40c0c200003040360b40142c1c005c031140c9424035000643c550192054034100c1d4000d80340c281880d5607a03114890740300180d15650703602c142d98625540010360016050300c81c2038021403108410b58114a40300002d9101030300242207100b800e104003e81103207100212000c0c0d0f9800310a400c0141c8910003c03c15030074103500405115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 302368129 1250 302366879 302366921
    0x901140f1017040f320d0e09180106061107150507170408121801020a050715032703080906060f040905390105040b0f0c0a0615030b070e180604 63
    0x400c5c10b1020030130040380c10b1190842110615030b0b495580106281e40008140800401c5009103801e9811940c0500b20000c0441c554001400c0307217086a229400480c0450240040251990000c0007410302400803624854038002d20300300007800c3c0703000e002d0740100700c403d4440d074080c9080800010b84005040d04001c40b10300704141852034942c0c2d0003111495002808123203000c074096200060940500d0340200c040c04800b41080c181d8030344005c054034072600741034803801c6c0c450038141c070b249041d01910b0481070344020200c02d501d00104043c0740a80b81d03600d00c2c0c0c80b5405005259030b5035442d00c10007050450b40000c10910301e00d002424451444485070f916020410368052001084800715440c1032500940600c22402000542d107074041e5008068400ca0240070340c805980f40e100040c0210426003044400322001584da00c01650700071420242c0000c1a04810030070810798144498000145042140080e060800450b00c51150f10407142000c82c0d451003c100d03282c5581d8062041035060304421010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 302369379 1250 302368129 302368163
    0xf0607060903080a0b030102070c1401020109050a0f0201030e0303071b020d1505010503190b06040f11030903120112031d040f060b07021002150103030315050901140f1017040f 77
    0xf080480715201014100001c4240301e160610031141e0995201210701066401c100c6000080005441080d0540d90f80304001c1020807010480b41813618824144145a101c0701e100040c165880c400005034142d109100780b10038507410408803604420960110030840c0d40d42e0001034001400000040d1100c00c036610303422203810f602d80200d03046c0c039001e0381110341100c104400014040e00c0c1180107044818030300042401450250031082400c107134403030046075000a01e900c2c9480d60740166a450002d51000030250403045151307542d40c1c0100382e1340c88a11b41c4401c86403000340100c90001c41c030000d0404108071000150b03031654081d4502400d94201000081e844c0c40100308594020078080c1c1c070421480d010f8000042c070004103450f900203440b000d861140d01c1d56600364040c15005580318410f480d01d05d00407401d6101c00500764001c10040020140c8110280e041c440c140b1400c01400c0d001d0b010610b21a0f8103241c001c070a019503509105078041542da02d90429180003900e04200070705891034030320401c83c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 302370629 1250 302369379 302369387
    0x7031205090312030109022101060c06050603010609050f0718120b04051501060f030506030d05040e0405010615030b012322080109060203010501021204080a03030c0201020c43050f0607060903 84
    0x40c400ca0640d88104d1366002c0f124288da80c05000d209900006013a40480e80001760550407140d042079000d0300200b88070b901c40806400b038500c21646603040c441c06004200311503500400d0703101c440c3c6501290181e01d501748100340035001d2001c2c44c040c1c20740040c14081420031008119603105682c40d8000980c142d41c4071040280100181560b41c00003c0c103002c041061840c000c07500c81e001a0990303c0d43c9207010301d8145401d10f10071000340300362125561140c0000702813a4009188507c0350299a0020302990644005483d4101300c111a8004445031041d0401003038521081303402840b880c5080c1e2412040d09130505200700c0140d0032500195090055141c00c10465402540c143d0740d0907003e40320880190708009040f4002d07449100320f43d5009092034004a40a41d04c1006000361510000d460300c004040224500340c152035206881544121418020003084007101312501c00340d14059111254136a25125501e0482c010988221494240405665100000c03500c180390701c060240021102814050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 302371879 1250 302370629 302370637
    0x91505070f050a0210052d060306040311120406051e090108070e03120408060a05090604031b0c0b03090a020f01031401091a03070807080613240612081b0703120509031203010902 78
    0xc400741000110f8020100c205447c0318443d1f00007034000d0450b0ba40701d4604903060700080941c0406802000030860400211100070005400c1a032200c2c1c0e5154030300e40b40301c00c902015650b02c100a40341441840b0b105d030b03805a0543d80201d12481c040c22801e9035000080c1c00c1040422482069810001700011400b01c0420603038071921114804000541d44c00c2c1c00702341c03107020459000700001c02d81e680b00d44210b03942000700e4041c42e00803101c2400c0c558896040405c01d51040d20240b60980c0200a1841146401c88001310b01c80300a1030240404010311243c00b55204042c01881113079030300c501103549580c100104803880c5500017400c40745840c0c0d407036003841d8640c58140101c2e465400f4130740c0051001c034514a9100c0380307564403c1c401d000880e20360a0405010380404088000715464140000702c005010001404036401080b034240c0e100c800c1b0700300092094a00d4004c042c141c101e41c10800116981001e403c098600034102265a0385c22940002d0400c02c4030584860301000c04800810958240da001d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 302373129 1250 302371879 302371921
    0x10603290105150705031303030c0b090c0f0d080c030a080403110d0816120c020c0301050f0402031906090c030605150d0b010501030b0a030506040303091505070f050a021005 76
    0x3034105040c10241040c100c14090181c40e0300b1503040b034409000d11000c007005009503402401941c0c02c0c00e0110303046075821358150b40160700280c06c0941e48800d01c40c140f00d015801c004035030024070000e0b171808007240c0d4280520046034851782030000a042032109442c00c40e00300084d00030a40e6074491500c1000741443c1c1c41650190b00203185440c10b00001a40003c21201406045d101d903e06540c96429003104e410f4003008840400c00580c0f52025000c0d000c0c014070300060f8541d0050011411000181801c5600040c0a01002500c4009010160f1000b15aa441600315824a038401200505041c40503240395480100180941d810000070310140ea400103014007110f00941c2c3d900e480a10800403914500c0c1c0e8090082710740e1034010042580203070b00030510360b44040c1000c00420350b030b82c4405050000c1150260080398445074010704200d1034030118600c1c030711a002c003000345051071080200780317501c51113407101880400100139024900801c104480e10f600b008062000789004000480c00d0604201c0d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 302374379 1250 302373129 302373173
    0x72909060304060518010204030209040204020c0a05061017060606090405040f0b0f01060306080f07060f0c050a060219050f040303050d090b1302011d03060613090843020108060301060503010603 85
    0xa03d17100201802181e0449400034240003180c0caa079001c000c0207601c4422410600d109098080000030b00a001c032911800a1002241c5194901002010420200b15242c400f64209408000450760b0b910705032514000151000507079a910761404e81d060740d0f40041d01600764800081041014a40140003038180e465641d03040c043c1e581d48041c10340e6074262001c1101081e4001d001c4c00d110061082c030350b541019081746404010881c968444a0405100080944000b6000109401003850000201c00c0c5000b080c0307040d9241c1848051b48400700e000c0c5c0e0000904001380081d940b00d0300c0010340c100504281c3c001850b84054206a1034100c2502d0790f80c10202c1c08981c001003160310350601c18440c54490f25018028103010b13a1400c0400020708511400014010341d90f54549010031103907800342a011100520131100c03100030fa10b6601e1388040d517080c098821000e03180701c101c07868943c14070346480d1582070a00d050645c0710540000d01414554004980541c0781060000503c07000b580010200011080303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 302375629 1250 302374379 302374411
    0xf0e100204061209020609041e0f0203010f05100804030f030615031e11070b190203011211090c0909100b03070f031103010f0b070309030507030f0209090729090603040605 75
    0x800f4003d48002541c007950000092120310440e0810f034201c46981c3c05091101c04401c03c603548140200c44800b8581501c1c0c6034040014048866000b80c40000381008540002c1c00c104600f900400030701004000800704a003003800d084a5a003e81c1100c005030904641900d502d0004050007001080624490580c3ea1011032040d0f85510706841507158440006031100d107001c0d26074440e0f1b03403221009040c10302c50300c044401071a1780020920255000c0e202411411061070f441c0d04141d2900c5010001c1075100e00480414424000030040072180c2c01181502d1400301030380ca1f1510030104910780d0f4054805140d000041185450303208000c543c2c080724580b81000f1030b01560403880f01d107000c24000c181400c00c09080502610310440d01511074107100740742041d030642d1a0f9075000d080c07201c9a84110340400344040c0c80070462404402c8190700c01d400100400060f85001d0346140d00c42c039292550180b025500c426036040126000440321500d50140509a5a04180c548000101000c5950f1000588944 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 302376879 1250 302375629 302375657
    0x3060103080d1404050d0e0a0e040b09120a080105040b18010807050103060816030303020319020d0218030a03092105010e060402030c010906090308160b13031116090f0e10020406 78
    0x40882c81c000c0b50094006d2540700c40d98007082d100f00191100c120b90114490300002583c020215480380300c3d5100b00d130084818100342119a240031115214000780e00c0007072000404030f43d80008100d04403602110080f840300d6901e00440c01c00c01a41c509a20840000390001c11007010001d441401c8030340c01c0e0307070030841150340340380594954001040001c0034007150301040020034403d4015640005005070700d01ca00c03005034203615040760f0000d80b1360004290042505891000d103503420300d01080d81900500b0b040070041d83c00a000c441035015a0841d1941e81600c40007028484412440440d130200c002c00001206406456507103a0803a000c80c864840c003150518654400c6d503403d001c0700c0158031012411801c5907280040c0b500f02d56030856119141000340e90114488043c014000c5000e1200041d1171059414001c100c00000301803805244d10008400c9080c0c014400302108035680d07544c000070381c40b030544440b8010705002a4200f90700c1c8104d903454101000ca9600030011200942c6031141080031034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 302378129 1250 302376879 302376911
    0x41104150c11120a06052809060b0901080a060e010f0c3204121502160311030c0a061116150c080f041506180b0901170307081803060103080d 62
    0xa0619180c154001c440c4084c0001c03030342d0b0001500031064040f110460034240c040020551007084450f5280c40d212682041400764034131034090b0000e8107841490241d810444010740ea0640110010202c0c0d40d5150782a015003400e44c80b68a01400300c80052003105680700d0001e006444000e8400442820403020000c0030440c0d2044208d40034440b45d0280c03d1914080002125050360101903a141118201c0c0d145a00c00d188004d0800d108901d020590340b08103424020034031001255400c00b0756004001000120400046a0b66142d900040125040030b0784203107065640280a1200c043d2200b0b801c3e05020841c1b00b082d04903620402c07a904010035000400e08842110040d22111140d0440d03601140215007200d10040d0001c140d403034081806983c1722400030084280e208441603169803a4040c01649c903106818a0040101040300041000e0512019032a4800c0a00007404032800040e490701170552520600700910008040e80c40b150b941c0d04009200d0707030001c0f1940c1201032600800003280b40d02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 302379379 1250 302378129 302378149
    0x1501140901091b1b0b160807020a0c0b0d02120c03010509070e010f14070c0b0a141809040c0806010b21040c031b0504050103050d0f020318041104150c11 67
    0x403100074501280d610703040da40713241600b60501c440242d80c1403800c082408114079a00882c0004105082030a0072000240200e20180020086401003403501020402071840482503540000f03842c6d0762210252600c9000703108502075414120310541c100710041c0c0003c6c000c0d50485506640c249030036980c405084984641c0880c0450104010142d000000c80c4144c01600d040008028098035103825038441448c0c602050b0b000c07200481c0005000f0345207592154041400381341e00324005041c41e0300c5070140e9034070001e0b203556640070349031070b0b4006014040241000d0303005003001420307a2403950b16550000541c0d0b200050701c2c20141c41c910448071280080c114814400c43d0804542850030341566180c0d25480c80001f008424a4007502021900759180d00c1110300035482980101007007400a84081d240c00440e0032158155001440003102c000303001a0365503203c400440d00050990824052140035008542100c44500900c403540d41e20035820413100003806019000044051000d982000381d1108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 302380629 1250 302379379 302379401
    0x5181807080618070509010c052b0c031b03180b0d1b0806130f0614030609121e07080a0503150303160807050c030607051206030601030f0212150114090109 68
    0x260f0b0004281c1d6120b040a84289041458400b41401c0940c03107032858049400250400d2061100c442c0106804101c0302003104e0b803003418124501605034602405205101040140651001d214602014411680e100d260740d00aa5148060303070b200e000c05921a04802440da0b05c0c18605103804008050036000e85001d100c4c965120211a503030502400302280b054154480d84580768449640910644e0050401400304040d43c01e000c200424205481c00c0b4020b030000b0840d800c4011202e100001a4045424943d050512412040620803060031144035180b0081c001d1070340820500d580d1540200118000c0c2c00700002140342c00c11030002c00d078991181c0ca83d035010b56400c0d030360340700c00007a103901c06032003098011401e5411100c16031340440e0404e00100c4044002410002c0c95a01c0390294001040c0c00a405134003e05840d03046584050799a1080e1001a2084201190302d04280c0800c000c022500ca0000c0c415607180d5035110341140703081d044c100b10075102e111f81000100700315005100b84031100d0f03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 302381879 1250 302380629 302380669
    0x408070f0803041a18100e011205040f02060309030706050c180114090409050a060f1407080709030f0809040903030e0c04090b010e0711030307050a081f06051818070806 74
    0x10340000542030240d4440650300c481c0301e0b01c00c800c0307a12540d1600c5030315211186c0e030746843c3c010700c2458000400b416010481c64000e1031600e006d00c8041105d200e0031070300307150381510240d540f612801c05903440c60007890b0006000d20f08080412003071040030006422011081100820040d8141e801560f50780031a03004007410550500000300d8a242a400103c48a40210103480480505444060644058a060100e61a200c01c2042444040605d080d544800d46160510190400120003803800043c0d01c000b80184088140b07200a1242060807507d2082004008102903001444d0140c00f400d0300700e5400340180294624483da0303082078001d43c000c99600c412299202e038241000504010009400242001881d0b6544802080108010b6000783c45644481c2e403601aa03840040010038000c0ca2100000011341d1188000e508803801807003511620300300552640316000011285036207800105134800b034403103088041480904021801303140c807036850540a50b2101c080c84060381c64442148005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 302383129 1250 302381879 302381909
    0x2070518041703100504050108070311100806040506010306090c11060115140d0917040801110a05090405181f0e030405030703030c02040f05010308120708060a05090402060f0408070f080304 83
    0xb05140800640e44005a2400c5003150741e00d40002c1000c40700260060b448a6120b92400d0040c0611050300244a000484081c82c1c004500c1c0c00080400c0e101038101401940c5401c04900b00380c1c02508a60081c0804020400041403d01d20040c0014040c48407c0181d0190f5000490383e0f0501d43c44c50a008446501e40e0440700201c101980000c1d1310480e03c20300c030700d50b880507a1000251507804083c0d840d64036031211a00d07581007000031800c4980c0c901000304481002c0081c0c9011a800005071200310034204c5002545656800c50340c0150b00c004c0301101c81c2801001c0e00d4440c0c548100040325a08131501da800c00001c826010720a6a0344114011258558041882000024413425659040f103101400c003181090041d10b04000b990001e8204071882580810301040380d1014416440d4031088d64900300e0040c1c02e003613003c11040c10306030103940d024a000c03500141c290340f96032007125000d01c60314080c10794466407503003007139103a0002d405110135554848000055004002081c7d07829100c00c51028002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 302384379 1250 302383129 302383163
    0x102130311190f060f051804021303021507110405130215040e0a0c0206090a0201091a09030616170f070809010e070905060109050108010f06050304030513060207051804 74
    0x2038918078035005030700508540740c5100c040000d40030030b00105280010150310324203201d40507241d005900c03020b0f4208036080c4905604441502491542030388240d40c016500c80c4400021034a0b40b800da000690403c0c107c1030024401c0f00403c0c002e2004d18011410300034500706840030003090b9542519031405200e88034062401601c1e02c041001a11070680300f06c3c03881c1503900c80c1000c0714481c085414100143c0d80b41c0100300c4d0660148030301580841c540000d00311440e41a80041d107030300d101b4005d0000e0745040010076040181844115050b141006007102e041d03180400c03032901c07404484001da1002039051001030507010001c0da0202c1c010714002030084030940d1503110440303c8601c0141001140e6495001d079001c2540148203150140040940125051401a00242801f00e040d8802e50410144200400000700480b5810382506c4803850031a80e02d490303608041f1068003806855025100c0144000542c16070001601c008071107080c0d40c100b80038140d11103a0300300c180c011140608403032007626250754 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 302385629 1250 302384379 302384393
    0x403050307170c0706110c250806060112021c0204030c05040b0117070c0309030b0f01141002070308070c05060408060a0f05040f030311210a050606160605131e1401021303 75
    0x907559511241901f444101c00c60140340511490703440d88100c892640085485180120300070117001d003000100181c1c00c001c0002000d25044002140e0100d5000c525130120392010a1441c03202c4010345001d644582d1207040c94142e400c4640300302c9100318900703111880c295000d45100c0f4016040d0364290316441d642c00d0380c00d80b40c59413900422420082d070003901000240c00d44135a84c2c01140d030350082003c03942c1842a03000e15512540840341c858902c40b10003402d890303800103144095903440186140c5640c1a071400600d2a6500c0e0011640030801140200d8020b80000d55288074014524040c4003100302200f000007207503001d0300d02408400301516a031300400d0280d04075920040192000781c0c902803034441d030080e6940300310110040c0e413861031090001e580d400b4000c00d60403020840300240781034407001c0c0180c2e0503207450030014405a1030f000000c800c580380340c140c01803081e04440803240500c0f99507045040940180f40480d0820040e2000c0c4a1101051085d0f0700040e01803401440030a0441c1c031186 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 302386879 1250 302385629 302385641
    0x9030d020d080429040302060a050a0608030f0c010f090812060f01204305090f0703060b0f1207110606061b01140612060903040e0901090204050403050307170c0706 72
    0x500c420402078000c1905200030300c144d03407096010742c1c05000a401d000c1301a030240e42000d419000340605042090243d1100881214840c0c0b49018040f940d4014110210b0302400584900864017854a8030800500840000404e4a5041c01e05102695503882e4100a120151010180d001400da9400c100440c01300c040101c008061b603004a600550800481103081201c26032007103001d0b10111200c8203d0401c4441045900800e141c1c80180e060410011811500000b0111041003940d5400328110324040e41c414030180140060003036448460501d541c80d954441200b0503e82c0ea898400a119184160300b1034504111590182596807540420010303180c0040c11482001c034526521031600318024400c0200042d0f40c0c1c1c1188201b89041000c11401e014101c00c501901e8000c4000c000d03429030084211415240b140c1680000c3c0e40364949200c4c010b20b4904002500036241c00203010605400030061803207481d00c0d960322514401c918401628800e03042d1071514264078140714140c0020120b800c10b07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 302388129 1250 302386879 302386913
    0x6010f0b041518140f091b030601110a0303050f070c05070509060312070c05030c01020a050a02010305070e0907090f060507050a0b1f0e090c040b090402010c0309180209030d020d0804 80
    0x1000c98415010900c40f0780281d03a4071120800944652085071820882c80704242a002160844d8440c030705042e20b01544681030103405500c00001000951a03801818000d01c031001840442d4105503aa18018000f00426a50350005c1e1980000180c0c210744114950300c80d040c2e021b0060810145403c003030180070503028000e10762600604c4804e040f80714655010300031840c01015070f0b10700b8904c0c05040c503040103000400d150454101c3e036818000b1880000d0390011444e42031030001516a580c1801311807010094428550045c030140512151a42c0040980c05448040b03d100c90080d95400c81a41d0a01c60310000401c0e58101880700808207000821980e4407200501100916050103d130040554280340c1001940d09101024013a07104c42c1003006d5145014107031410080c9800c44000075100036802040203040103110344a0b0010036104500f220b00810400280d1183d403c4081490030194000002c918001c0c03040a000e46074852001030420518060746e124042d1507181e03502c40e00e0b072003105a40c003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 302389379 1250 302388129 302388137
    0x519050c03011e0e0313031203090f150b0f030d0503100b0c0f01060504023a060f030b09010207030e011413180e010b10030e0a020904050f06010f0b0415 67
    0x1903050a91000e020f041c2a46000c1140c5414400c0c1c155205800c484101a01030340942c003c1c4500054401d488410710180e80d080030460030341a0800c1812006481c5100b4010700c1b0b1380c9540384010800c81320811840c1c1d20341d1501c5040c80b800420a00380003000c3c1c04013007c5035255101d0070300025854000d03c000c46c0c00c00c001d001072030b0703d958441940c102a0361010220441e16401400000c803140f07420b02c40c2d030020302412501580380c0398042c042ca07920300c08a404c0d07805d1242082001c5542c0e916481c04c203185c941942000c14040c003547d40c4007d800244103031005031104100318000906c914018400c0715072840d0306440700340c60b000303c1c5d10046500045000c20455408004c00c0900c4061141050f03040090034041e40d00c00c0d00611682d00760b01034902c4039040c65041da0401e07840d030300e080c0d0311340e1010094102c1e103245c0040c0030f564042e6903a02c0c01d0704020010b9000502130042c0411f009000c039128031a60444402c4904c2a6600d400091280d446841121481a000d200500402d010507a91284905607860 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 302390629 1250 302389379 302389393
    0xb010326180f06040608010e07030501080a020f0d06050f0a0e1c03091704030503030a0e030703020604020f190308030103210f0e0a0305030c0606100903051f061a09010201060e04051905 81
    0x21419a13403054100e00082025500100090740142c007140d03502134420300d8140701a51505805d070f81e9481c05018020b00c42d08a03c030b50400b898849015102e00c0c150094000e0240d4108420700c11008481910030f01005410503005603103c403800184144075003001907201c2e0b1140403004c3d0480c010010850101d6800052080b5214408160360140010f14000c4014640e00e041c0000038030210782c0c0616a817219030f00103200300008260046146540541c044e50f140e441d40c1e4607240002c4150000041c400601d801c00721020051009201c00355058a12400e4501524095100101001040b06c2415400a0101078201030341070b100350608a25004003400c3d030840c80b03803695501802d6401001503141a0f501000411240c4c0c03a20b1160f546440d403950419420a46c00e5440b450f4440284400707140c020b444000c030503075a0311151361103c001010f80313117120b40d142403040070346d00c4030359101c07099007030056013040c0b00485c81d00c16051007a4001c2e42d00a0007403031a45444071059030590348081041e12113002d0f80e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 302391879 1250 302390629 302390659
    0x804090b01020f0a030503012c151203070305040e250e0621070f050f0a1d030307031706090c0d0e100c090303030509060609070c06020d0204030b01032618 68
    0x990340d00e03031003606d9281e12076041c4000c94100103141500383c0040c4040100c07011000c1d0398000c0403134110885680106010320404045640e0038051045440c0c68400002d500051540c4180540155020244001034a0701d42c40340382034407856404640e403c0c1409078181d60701e81038041c00005500d00340240c40700c0c1c1000c901c1c604400b24000010b90340c0066040040c100283c281c0d01170240044003401d070600034100200981e10098a0207064008014015a4100c820984400031034000391420028101d0703580b40766a1a0060000d010104680e500035400d401043d014131303000350101c0c40307001c443c0c1e274080c184001d42294501804004810f5910f501940140c43c5103500c4a006101d1010043d48400590340d20710301d0010102d440041034080250883d0092180507078135031420030340040a500d00380612080608240d0028403484003955280c0b1710004000003042980320034181246d0180a880c0d1003d1103120032108190040001501a4041000707a0b0b41c0c2200001140801e8550107403a50020074101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 302393129 1250 302391879 302391883
    0xc011d06030a0624020303070c05070302060703031d0102090f06181009060f0509030c01051b1507140c120c01021c02070c06020d020309101119030206090304030804090b01020f 77
    0x80d50100002601c0342c0c000e1004134540044055241e241e02004c4080c14040b40c4001c3d203900002d0000700c01c12002540d40e8081c030508104040140d50007d041540d00c3d822481d014000703040651641001400a8041844294042c07080d41c11700c0801429006070590b0480c10071401d644004210902c24001c2d40780d45400351141c2000c00398904494985017040c6041c414003400c036408030740c00701e41000410441044903450200301c0e540310701d0342806c01c42e0300c0d2111207a0910103da11410030460320b20030100400c0c952500c48402c540180c1c120f8940314039041021100800511900300381c6410340e4005900340b00403002560003000420b81d07900006023001d55003c2040d003031702d1042c2d03501e8080b2074001c45d81100784040300d0400030003071529000408601503190006034a80c051441964860700c3d2000c081d114a03405058501001c14400082d0b0305024140c2039845d50924003690f040d0300500c603503800248084000070840b0181e030b030044401c601305071501080201a180c8208814110b001d100c003901c1d180c40007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 302394379 1250 302393129 302393131
    0x60c0309060e0705031b0a0506030403050912060f06180f041b03051011030108070303030e0a0b0930072a0f08280b0604090c0801140105060c0c011d0603 67
    0xb00d0005840440d00c2d000406140101030740e540b4402c41d546040089044e969400e001c4103e590542d05640c5079600e906046e51203028003492990422000300c2610b120b24000b0600900c21860007880c401c0e103444d0a000d008842402102c0d082054160b2400b0a42e0482c00300181948184151b0201540207481000020b0f020f450b079004403130310f6102661200402420703000e440c15402d244602d1174115850085242c2d038404030f81c4000b07403d055480e56843c07032504003484204840d40c0c00081b074540f2824880304007591a806130003c07289405082c0d42200d1a202d15007404003c0404400c2c85d18281078103500c51855120f4a5500300100c00100600141c11039603141031440281110101c4010452a02c40458148050850000c5400b4a0199100010503107064540c0d196a0000b50085450b81c6240109006003860030700a000c40060075000200344005401016829005100700d403041d0740d807a010b0000c0c1d130140300c03c809907503080142c04041c154492401c400100401c80500c2c0d844c2d104050200d00980d03c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 302395629 1250 302394379 302394401
    0x9020a090e101a0108062101020a08010905092e090507060c0c0b03090d0302070204021308100e120a080c0f0a09032d02130e010509010f06061b060c030906 68
    0xb11151400300d600041c4281e804008841841c45100c1c80440c000810400000301124490403911070060b0201c01a2900889003941c0e01000b150340310100403000d01184c80074480c2282c010305000014100d83c0c80071401c903d420460490606162103c60396600b492900c4d4040c51407903a40e91001c4001066040101c100140095220102082000e0030303c40c0c00c030102a0052001c01d0002c0060141d1008009043c0e190005289001a03e440c124400030b0040d01c60456545000c040081003c01c6810000ca403100f20710304141820007810202e0400e040d25500202c2c00408005002e0100d4440c042c041c280c140e6020080c00e031424906400000301c0346a03500440c0c0210002410315409208200103800200c4241c0c05140e0500a6507030414a4811285004039009006410008440e46c0721003690b008941e00300b803528001c0c4150710380004070500038085080c60364012818801e002651034011400c1610900304000c080706012103540b624009419410741d0f5404042e640c10302d8030040340c030034440d04070030007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 302396879 1250 302395629 302395633
    0x1c230102071a011a040b090a090219030f0e070506160b1e150306060d03030621050d0e03060f070207050a0b120601020303060607020d05010906060b0307080a11070609020a090e 77
    0x40070b01140002c010340160864015090400c14880c000f81e1400c00340c50031913002c089019038030319019000ca250441c0c240c0c4050381d018004552044aa011000c58600c8c03605256410003115040f403426070190b6005840000c083d811620003440941007a000420040500d2103050071003a546507518040c520049074107011181c907a9580d000341c2c007041c0351410b8000500b00700d032120105440000a44800014050300c0c41031074520381c8002014082d17041680180800d804001d49103100003800480013952840440740740c01828951020240075031005082c0400c068024241541c54040f1034003000cc0113000c080651007a43d200013602e5558000a030003400815198540390301e12501080c0c20100043e04540c19500180304020700d584550007a1030305960110b42520342d80c1201e00308030740101401480900100d00b000c03008250103000000540c020446565074a10960310030354948201c50641640507584602000010b020031404e401003842a800100342c40a502e565a486000300c603042c1d940c10320f581d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 302398129 1250 302396879 302396903
    0x60c07080304061814011b0605070f0905090c0306060309190602070b071409010c0c0f030302030942091315051804080c0f1510051c23010207 62
    0x100d6004c8030303503c10622822041660306003415a500d01091208690300c0c100410003010358043c40c4848504c2ca6290b4200b1001c01072030501c05001403a0211b01955000031503400d10b000109414072141d02c81c032681c003003652180bd50711040104071603030380090205011071003420310708403102c0494012800050300c681c0b40107a849520707113801d2002d04001070112003444001c0081d1b0166910b45c000301c4002020034030b0f14800707443d0145042000d03603174240c2243c1601184141e000c4105034000000b4440000b0483d0b028009280c1c180300c00c0a246c46406545540f2819420129207114075486050103445042302d2042c2000c4181c03006c2191003c1c03003030b00d80f200151a455000c0140c140340000308050302055610a030100b4841038040201130300508014000b04001070012952002406002161283c1c1c0054491501c009000350075196410351f50b80f5136000d03141c3c10000382454503010501c0c104151a030038408000c03090710781800301c608418000d600c40040041164005a0070b00c028000c8601c00c2d4982ca0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 302399379 1250 302398129 302398139
    0x250c0902040906120b0402150705070b0301030b011a04050d020105091008190908180a03120309050c04020c1905070b1b0c090c040905060a090c170705131202060c07080304 75
    0x20b0b15034544c0306124140012810202042a02c8117165200790107071180d482255034907031000707403e204160f400b030854001e070b0b807020030041e1702d10004604a070301a4080f01d400380d807a07a0100c2c9400d10742500290000004020803c91418400011550503005040c801d003000c0d002c2000c184008001c2240000144072141001110950031011140e40c41000d041002003030050713038412056200d2070b40341d242040c41d40c0d210401c1543c2c0e05220500615805254182d00b90080d80c4060054044034100316540e000391481400203007040e00c00d48215465000080c803100e00c94040c10343e102d83c154501692540144480840d0040d03506009084481c0700103640303200f6020390f0509904085120301181e1050300740c04103002c0c2c28501d907004e540c103403402800c001445032a60b030700049400c03800d503005050300c90400a0410340690050b05034003003070305003552144207a5101c0400b00c07214400c1130b00034407039580040401c0c0030540070496000f540b6440030708140d2500044030f225130b1034600541c6c01010b00b0351000400f03000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 302400629 1250 302399379 302399381
    0x90201020d0201050c040e1008070e0f0708070801050607140102030907061202040303080f0a180303230f190612123e0309120f0d1103250c09020409 65
    0x9181c5039200801c82400c1241040455100314450900504070b00d002040390011020b00b50700091800c4030807924143c2e0307201d8840302402801c4826850070140c0000141641c0d00940540d0300c544401c0e42c9520480c0e09010402c121500903100581d205800c0006a9075103031024402035004205004c01801701d285000302c010b10701c144410705080300c3c50060104000083c2c0100030705030800545204040207580e100c50b81001003a00c0711066006640300f407282424503404d640302c0b121080403683e0100801d11606044903a030030080d101b13504174078051000a81508012154001c0d215052540843c0081d5118000d03d88224003841c01e54501140c48001501c4941203070a0140c050354407403500900081013440d980a8210300e140c0c00c0400302c0b400000c801e240c1014821180071180080210f442a15682e406558a8003901190300780740c4103940b081a881d07400780d503480c012401401d009502d03009442072004200180840c00058075000c3d5880280052585103455000d0324084100588076460841041c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 302401879 1250 302400629 302400643
    0x8071215080f0c0604030224030a1505060a02120c0a0c1502160308040504020904090609050705040c0c05060406090c0810020315100f140405040c020c0906030705010915021e0109020102 81
    0x100b142c0c0c8280e00b800b0494646900b641c040300e0b012542c54110911022400c1038645001d40e2001509100104000003180c0c01e50212400000100501c00f880791030b801400101d109006071880076a21155208290020280023045022107050130794610305010341e40c5000071007a0707410400700081100356481040750b0401c00d010344081054110460189151500749452081d4065280110f800042ca861203859541015030300562107002080b5a00c010706001d5114501ca00503a882030f0300780348030641507602c141c20f032444e03468000029203010380303842c0d403007000070300c038002e011520a500d43c9000540745009001e599400035000ca00507039a1b1800c010540d1013003001d08030a82c4075402c0c203421428111b0744400380c6e01c402807a9080081089a807100b0400e060b02031980020352113802c02107107002c1d02d9400b0459011000c0281ca0f000d0584d01d0700400c2689403c0e40713009030360000301303007107002c11400c0301300015224440c10a005403000410b810040b07840d481c0541ca442000c03691200c08035411943d0401c826 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 302403129 1250 302401879 302401903
    0x503091014040602220816050a06140d0605060307020604050601080703081b0703231528020f0a090816150c0201020f060906181506010807121508 64
    0x41050000800800041c200d001e403000c0e05455000c03484030710b1020500709500145011001012240b0703034074010a599020381124950f5211810807000a040c10149a9001030380c01e5030301c900410300501c0c07004203015048085000700f102d444030700010300b035140c8000450148801b81c1c00b0b046a480c0c00c0c10450b20b0501b0691240d045644480c03010001705060006880b1044401b0954005107130324030840c14070b080c5050b0009040034022140c080d80d2a450000d802070b55041160507103603101410300368018103a07000c50b10b1402d5030107503a000c16141d40c1518120241402c03031000060030b01d00581d00318606d58004521500102d2942c45040c0700f6070b8401c1056485c10650504101c161034200b402e0551100c3e0b140707204209101d44010340e6003c580c003e00c81c1262601c40c4030100c6440d45032195003255503d006460304000c19140e40400c0b801d0803000b164014070baa0036116514410b4440c1801120791510043c0080100701031003526440200480c043c0d80b1000700482c02441000c0d0800d020581004000c41c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 302404379 1250 302403129 302403131
    0x13030c060e240306040209010201140901060611120405010e010216030f0c0509060f041112101a040605090f042a02010b0d0519020103020f03090d03060501031e0905190305030910 78
    0x105000501400c2c212a031154043d50056190000000140d0250034404014000c241c590302c2000003c0f10154030440c12200d2540d00c50b100f030140d084000380c4603001c05685c1840e09008001c1030120b540100070a040c101d00600c100d81d035003043c034034120003a400706810444203611901c0002040c00160b048103c00740c00c04843c2d4000700e003001800103d80005100320325001307544411003000c0c41080744042d5519440040021001882d0845070f42a007415580140c9231564200d0b944001422100d009039429144a905e944d4544030f400000c0000b0100d61848040d440350321042003801c00b4245100c0310905c10700958262109400c0b070072000c0c0c2540c4642c4106400303441c0200003800070a40c0050031284002c580000200d26490900040f000b0b4801d10582c030b144103078000180101c0d0130001605100800c440d540800c01251142d0044040e1000103510440c03013001c0301c0c04c90304d1041d0546c3c002000a4071810803159900d44483c0220040a14010280c02184001c402c00482c900d0030f101006100c00c2045c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 302405629 1250 302404379 302404429
    0x9040f03110a060f0506180f0a0609140105090112240f020403030e0a1e03030c060209180708010801020f04060513080f030405040e060103080a050f22360213030c060e 73
    0x7c04000310b00801814080440318080114540240c02d0340618060b000380030051180d2615201c4000d080e407000c0c49103601481d00c4100010f9821961151403d007540d014400040078904000c0800d400e2110301c04c0141240d98401c0000040600e603c0107100441c0300c1d880d1901c1420000e800c002d05038010394442c500640304030012120510000381c1c0401a65030500b0810341420329410040024010040000d0300f0a415a0038400c5400840842a21404041c0d13195040c580e01d50510703c2c246d0103040803404030b03140c0078841804014005c001400c04d034642208080b10150f9070b007004d1840c21401a050310744642000909100504050142d4a100c0c003551009000651540c0c1d10080d0302c4c401c0c84001d404001c0d01080300b4410000010480b01d20b0103800c40b0400700480c030808940e070f095400d4802c40641080844c03c00c6004400c80d0340c00801400b030380d160f8908807580388141902071340c8600009a04d28001400100000720548800c0020f81107a07540d409180401c00c05002103400246600e220311101c0305 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 302406879 1250 302405629 302405659
    0x2d06071a280903050d0207050a02040e0f070801020c030a0f050c12031f05150a050409140a0f0c08070e01030207060212100b070b0106050706020705010207031e0e09040f03110a060f0506 81
    0x94100d44c017a40e250a00140d07030309440d042c0142018181c20000354081d0030b0003089110308000091114510325140e06880d102580e07a9401800c038441d06070304c040b0760b030424410b0104582c0034a00c00b20704d0742c5450800d2894030000c01d038a1400d100b400c0040804011011041c03041c0000c02c25600a1802030340034410103a14201400280c2c203084542081d24210800034101500c0e0344500c00f034030010481c4031018008074800391001c5c02403103000c81e03400c01c60341e19004100080c03806c980a035245800d8943c0b114817040c2c85030b40044440f01d40648045060607001c01900c070008016200501803a0700f0740c0040f000d0303410300d840c849801a1003035104500e42c032818041c02e00814180d03824070741111403d0500968840300c07443d0010103030103500310150807944042040c0e014550481107044c1c1005201c0034040ba10104514261509480c40f00890f801010762000140040c081c40309035494103003e81400c030703d92201c50380910b2411a41c0081181e0007600c600140014000c03900806420040454503828004148 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 302408129 1250 302406879 302406887
    0xa030f060504050d091a0f1c0b010f0e0d030305090f16031401060303050414040f06030305091f090501030b19080d18062c0a060507022d06071a280903 66
    0x2400c188007050354005148802403087c6e60490701c4c5541d44d982004025010725603044014140d201400340800c112501d503000b82846500302d001e0030403009040e04030710017403510102c005003001800d061061180c0c01004540320002c00a04181c542c56184001034a810341c17511812aa8201540120030381c18040107000180e0041c00b514181c41103514009024100c900000c0c000d000c2c1440c00310f04d05441d000011042c594404005c0c0400b1206a035141e84116a1004216050500660071800904c411320203020307a40c07280c0c002a000c8200100b010790001c00288444c00b4854895110b003e20b58480454017080603003082d05c095004d12a400c4440c89a40380c8032000e009110408090b030007501362a01c040d100070802103d84c10403100041c2c81c80290540310100078110741c2c0040382c1648600c1e542e04140685a9201804031410840c200600002e90144018403406410403d400c80c3c65145c5441c0780c003012415034046520440d4440c0c0d41005024034849410601150b00320444100c1d81030103107600c00709401c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 302409379 1250 302408129 302408159
    0x60b0a09030f0305070804030317060d030f0537201203061306090e12090307030204020c100c1206050d02010c081308030418240e04020a030f060504050d09 68
    0x4031040d480b540700035260850742c9205d14480142035200202d80801415030242500103504601c107030700051034440d0340400aa0350700c000001000145040d58003a03550f803294001e08440c0c0030701420151240e1683d405480358000c050002c80a100318001d81c0240907a000b0301c0c0154450024803040e003600300c000c0030030f521002400c0c2d00091030040000410384a4070341c1041c1c3d001000ba0440d040000549400e9000b024258441c280f0300f00e44101781466a0001442d812100c440c840140200519440d650030712010f03422501e0415100e0040002d5402c0c0102c1c035005248130b40300e0b140e17955020340740e0050503101100c05a0300200d0003030b00d14840c2c070320050341c0001400010940011034030b43c580043e00128610074420750000c281900021034000f89604030010340c4c5800c0003200000303100d9035007072207400b6030518503001c40b40040d48140503081020924515465400034000f510400035180c50740c803514a010000d8400b110141d82d51010801485810300404001200c40c0c500382d4000b6141500000e41c1e01c131 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 302410629 1250 302409379 302409383
    0xf1508060f0613022a07080705120304031406010302011d010f0c060b2e0f02210918041103010209030c12071505070302120708180d06060810060b0a0903 67
    0x702140c0420260b80e18101c00004444124a040d56610604000710303001002d030390762401c0700344501406140d05480c0840c3c18800c2c0c1d00704400030903a01c0d1a00c000c00002c0e400101c0d803440e15002c1000b0210109100007034412100c0d030380c24014841545541b000401c0800110140c2040034240c0c0b080e442141e900105030694010185032642e040000c0b800c1c40c42c003c15800980c1544010303c0707002c0580d031949014a266103452111020104214098020342d010054604000016040b290203060401d0380c042c100c5d142101d054500f10b0505c104d80001c01d59000b43d0102241201902c2800c000400144440400740c02c14182d00940c1800310301c0022076503690340d00000368450300342050000c0080d141044048001c0c407150108141e10180d075400580182d0104400350014040d810f424003050703044000b00c2e81d1030342c2d010014074a40740030150400d80e580800120076a20036601500c401c003003889802010040c00502018003d00542260b02200302c8145503c00f001290b801e0094102039500a0040c404490b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 302411879 1250 302410629 302410651
    0x1d0d03020406090902070309180b090609070e0d050a150b030f0703050d1b060207031707030501050105030a0c020c0904060e010f11030a0b13050702071508040b0c0901140d0f150806 79
    0x554502608c40003c2074000708490301c600a41c075480a400d942000314628800d0310184d01c103843d080c042c0240440c08807000340208249155012540c2460115400c800b80a4000e442d02d105d46030382d41400000c5440c0c8110729030b80d21113808421500d4140b000c1c1c85407446030001030020324503580c2c515880c3d11000000000b8071104501d00d18115000e480e0395400c4079409402103503528045d08e4083c0103404c0d00d80c038440c062400ca1000030707019406445598141c0390161507407030460b6500c072040009440c040114070211b001d1010020015114002428081c920a02d804103060003010b51070303070031288060101c0b10b6281c00c0c00761301c4141c502441c045a4010b941c00c900410780a03c07000102e00340080e6400042100c42c500010881c0003580401d10b00107403a2101c1c1d441210307044004085444040945021700030b4002c0c5400710b44000f900400401600d4018140810890030b4034082c142c8580114241a100740e44551514030580c90a229004c1c902d20251000c0c000f60741801140e81d0344000040c4070140310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 302413129 1250 302411879 302411887
    0xf0102030715020d0e060c12090303010e040b060f1002100f0c08010302040207051504060212010b0306180406060b0a050705070b1603030b06070204060311030601230d1103011d0d03020406090902 85
    0x941c125800c94400a1000030442d04142800c7c0306202c1c0e958403441c10340c540c0c0040c5d48003240781c9800100450341241c50200c0c0d040e6941e201e17070702c0d130f192a10405015903501448480402013143c844603940108400c83d9000781103010301010701c030815504605254901c60b4600701400500d1508035002a0650350162001078889003280743c0320340342011840c100104c03840d4103810041085180d400409881c5030942c82c65100c1d9030703240880c1c3c1c0d0078003040e00d0a41e44120008011020142c280300c0540d0701a015280c081201d0f035455a07490304960201e450880084d40c002603410a0260400090f0024108614200e103031030b111114004000c0c025100003020503448003981c06655440900340d0b15004d8004104102956482c44c0c174001088040d031180b8024015800001025030b18400b41d00c02d200070420881a102f0301c0c0c8005c0002081034541c0803203c0e0748101d2484540340c2c4092003504840400604100d140416195000740f6220280b0034020403d40104000e00ca00d40d401482e907800c80303c0c030140158403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 302414379 1250 302413129 302413147
    0x3070918091e1b0e0c070606031e1407050303040608040503040b0a0918060b031f0b07050d1409010507030509040e010c02030310060c08030115050c010e010b0f010203071502 76
    0x390809403400750034100d0209a00880340c460951050006110b6105400c3c049082c0718800500303c0148108140b40d10804000755010111500810701d1500c180800a041610f0f5034441c40c0d8151070001900d045a4060001e5003081400d04001075021040c100825800740380070006692446640034240402c2044008141004401c100381c4000d84800300c0340e59181c0f865001e00600b207504600c0745c801261605003d010041900e8410394040d00d000e405880d20b0350795015000c6020128244030350701c48049040c00002d4000200b0080c01c9800e108102a1941c42c60700b0320000c0610404070302a900e009001c20580700d480c0c3e007101c200c8501031b602d420101d494081e901c0005000300b4481241840079400c2003083c1610540c040000d5200304d21004141c105142c0fa84022100f001e11690001e00800d010401800318000029003900060f0b40d5241652922005112840c29143c004604407202c0c0c0d100d424464261500c50102401d0400a20086081048035291180c41003a0400b00013420f03940060a046 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 302415629 1250 302414379 302414381
    0x40902030a060c0e0120070504180209040b0f0f1623030708041506030507030b1003080f040f14010e040c022406040605040207120807180801021e03070918 68
    0x10409400030700403c80c09807407401c0607000d05080042c5600048100e0091869041c08003200d0104800070001064030742e04010034007004110100c48080c01d854500807050050340c071100240c1c071842c41a80040102c1c2413041e103d032003260008c0c000710002038415040190069210f0245440f1510030702d0b1803d450708030741003095100c0c0580450401c0001c400820840303440d402041050049110343d054500107480f8180743d004071030b45800010809d40204c3c00c2000400d240c00d0a0340d802240e50030f05014001d42d03d036507a8449511140f404a41d120010408205904420344458020f210046446a0426440e00020514240f80101a1140b41d88a4101d001144200005000942e20a07110700c414185451a640080c10480310356109608105022900d130515000303031500140d0100104240034401072083d900705400503c1c0904000141c1c401442d845c100c01d510710014102c4c800010707034640c0d42c00307110440144004501c1c0c080f0203007041884503080d0b01910242c2110b4042130711003541441040090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 302416879 1250 302415629 302415643
    0x11205060a030f12020606090c040b0721021b03160b0a03110d060e150a031202030c031c240501050f19020d2601050d081201030503040f05040b060904090203 69
    0xd0b00040c140310f024020090340d90001118001c8075001c503809562118100210403504440381c0003540310501081240410303540152000c03511495420050f1401d000907090048000060000103901240000b01042ca0b240000c50400c9400c0d4042c00f03000490081621001016124842d05c40c88005140c1040f2446070307120507802540105841d640d113407203000c11005010343e07005464121140502050021520840da01c40c104000b030100b91416146440d50008032034040b007130505602080108248118003072000703013079001564481d280799210280010044459224040049030007510040350410f181c8044e4034200c840920b40380da5a0f103005601c0e5405030044000c0d030141c4284031901001c02d190003160450010301035585032000030044150300d01107141ea800d042a2600c1d021001805103080c50241d90780150301505d042d0b460005100c060300230000090303001f900c1c0d0382c00c00f04040c044060000521070007400e00301c505100c1c801320788000031198402d11807258841c03592820340b1411910244144 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 302418129 1250 302416879 302416883
    0x1f1107020f0d122003040e0708040201090b032518051c06020f0304051908160c03050a0c050103060506040e06091b0708030f0601030c08070c02031011040311060306011205060a03 78
    0x918441c00703860801604e0194414003402080560500151156800000340c4044400b500807801d40e036146e0080690b514800500b040e41049803444c0f01195420000c00158000c80c0708001c0c07003000e44003a80c21403605601c1c8413050010060000020109030103020b018600b5a0411112814204941c02d51440c440075856402011b03140040303168001d1003070700d402851241d0f000340182c428107040550300941020900c6801841410248014800000703c4410305001f00c0c0301d000c1d200d0820f40c498031107070304c0d00c490039908603140382d00c06d4024403003541d1601030040180702c10760b440c0e410a810f0a0000110480c024417260141e00814005209c0001e5200404441e5a4030002295550611704280340030f0750080390f4448942c0c100001051455109202d190411801640c0740811074560301c0c42210500d01d5000240d030b05120344004800100d115110749840c443d1036040f80344d0345615510700300b880c0740f0300c07040003902c01e1200784108620b507600070003014801d120340d01b00002d0980da55000141c00c10496000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 302419379 1250 302418129 302418143
    0xe03061003052a0d06061a0f03130501021b030c070608010b0a05180a080a1e02060a050705010902041802120a0b0105010f09080a060515040c020d030c050c06091f1107020f0d 76
    0x2803041c040168809015500c40300d50044412100741f4010160b8440c1080002d81c0d26400c000095555a0700e03911924107502c548000b40c503148004581654240f49c110034010b03560070000303480c41100b03001c00203800200318500b0800203540c0340203a0344150b0301034805010280a000942c1514070707800810009003070480100758212003030704c1d050440e98540d2021f000310f80351b06075950359601c0328000f90004080c465000340400c1c541513040d84112160380100104403190b40d2078403c0c0c9401681c0b280161000c014280d4841c0152400d40d004000501000705900e038ac80303401030800803020441e0404a141903840c01c3c02c24550002c04801c0c1100d0703400c429802107200340500b070000b0003008600e41002e0b0054003000c005144d2050710300c04000803901034856102c0541d003c007191100700c9000b0b4001d00c554070781504000c1e05001c010980182444400ca0303402c01250408620380ca8003881d41907403401805140002045001c0080c3d1625520b4450303003201a214007070001c64900301381e60320b0269802099010341 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 302420629 1250 302419379 302419399
    0x70212060a02120c09030309040b010e1e0a060e06160302250501030e0c03100510170d08090303040b0f040f0618110103020903070513060f060e03061003052a 69
    0x2840e0094104100844401c121440815440404913081e10f4100c40018007030361070700b0b00590400c0003d00401031820305201c103004001c1c1c2c06545040c0088540c42100041401002107142045072014140d0000c2d4140300c46203c4c82d1039a500c40005071044407101d6024a0010069401c041e4602160b610f2803110b6049a400d040a0f084502a044012181c3c00e80302442301042144d807950b100c0010740c2c0026010f0784a50b04040d1030058a40040303400c1192040624980e6440d58103440c040442d9180d803c2c5031341e1000d0105a0116409404680e011f000c0c0c80146013507081680d1001c001c02d0011745204000c1d843c00000c01c0605c816001c0c0114403941c812000c1040b00035140304102d03003c0310361406640c801070b18142042554003a000b00e40404800801820486040008108901082c41d441818031503130340d82d010944550901210003d4040b503282c224040301841c0415282c44001007003410011100101040040c100141a080c034480744415003084444050f810802946e6060f015a40050a24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 302421879 1250 302420629 302420641
    0x806220b1507150c0806130c1e050909010902030c0313031e0e090f01180f021b03130906030309120f050718140702120f070602131d01180207021206 65
    0x10b0041c0c285010501d609102240c2e011340255054881140c1568019402c550142000c98446d8410300055002e403d001c0384541c01ca40404002066100b104000306800090016040c544940401c0c01844000b42c15451480c0c070303001c108010300000e000c1e00488241100c6d41c10030540a400e05201da081081d0099070403100e2200000d003a000032480780340c06602500003080055200301c44250680e0406440800442140803c81008103605003984017050741c248001036925602c04140210b07243d00303400454a0300c00c1011074083c0610f460380070b8040d00d4074020741000044c1c2c101586500700c03825007030740c038034102d09900701046012145403000b4098000d003100411007034001c283c54118446003240802c42184c04201c002d04a0b04252100d1015a01481038a5000711400e030044c4990001c04d07a00c503062803450350304c0c401a41c12401c0c0a104c0c005141c4002c1c0a00c0b40f26990700c0c104072460003118640342d40340440903400d814500d100d581031940c00050280542d22216100004402c103041201c02502e071131 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 302423129 1250 302421879 302421893
    0x703030b1e01110609060105011d0301110301050901091a2209050d020c040e150618010e0103150c090b0d0207082701020a111318050a030806220b1507 66
    0x4071a8035030224410b2421811200000100c0d51320400c0d060b001084a039003044010340b41008001552071040e43c1d922600603454900303004840c3c01c0310504101d69100d5041000b00725014505170001180745141a0030641071a4520015020f4014180c4080c4680c6c00016402113541560394030f000c0d0860b0812034031401700000014a2221106070740e003503a109811090401c01034501c0d43c1c0d8140b019038001c040004009000d004410340101000b0f10000f103084c10300c0d0101c25880700980c0440c40500700140100706115403030340107603165444c096003045810440640a4900010350250a600f0500801d050300100010b0341194032041d00003490356100c03400d0182d101c04401e601103000e0400c00500c00291a41e5000107400f1500302e90204050041c080142c0c28440b96031351520700030f81007980b1002803000604110301182c507658040c001030030403044541405003900502030089401220000d002242c8051000b91031803e42211100218081102c0c4000441000e0a0b100c0e121400d040050604100140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 302424379 1250 302423129 302423179
    0x1003050318040609020405090103060e0325030917100b06090d0516080c1008060307030b040807140c060703050d02040e0129030408071104110a0320040f03080703030b 73
    0x1c111000d0003280d0710f0744c9080045e4081e07841050b0300480c1c0c120040c000035400340c011203049000502101d040c081041c1da011410251942907c00c00d0401c80188070a155000d03080c640079040a015182008880044990760303014908401c0c543e065440c1307510101e6588403c200c1e100c1e50710080c0282d03440051401c0070b036254805000c4200982c409002c1c0080c140380b01182c84090458001d011380507030032030700c8015650490000d04c040d0307060098450200024205d914030034006c0f80550031550f251081450a0b1200191032440f080b03466015a42000f81ca54400044603c00b503490701d401516146002c0040c0c001c0d0245d600103820142d017140010a60443c0020b995404002c489501c09c941f5030407111580d228031050320080c10500c0c0070010400400c0501d0314021280001800c00200d0740940a0812010b030001d042c4800021340320f104912401d9144c051b54285d00514000c3c0703514140ca04962880000224800240101c0c03001c07841c001418003e502115116074083d00c104200852001041d0701317218 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 302425629 1250 302424379 302424427
    0x91018020909011502071a04080a0b04231905010603080406050307090f0303021b030a15020904060905011d040c0e010303051c0b0906060d2007020f030609030a030510030503 76
    0x1114000200404030004c1030812100a8004e003800c41c0c2001c00c2451801d03c1b050100d05d180c201000000350b14001040121121402400d0919060400c0d00d040c6d1801164003a100f031140402d49268029003001140c031940306454040d0383c48540006140a5026060560000d44101c06c04a0b0000c4c00a0704500103500c9058265220107083d91500000c100e00c003807501010b00141d03c1010b4010064000c003058001e1514021b0440f03100c030405940f914030781075510580c07440d41500032420800714201801890041c00b01403100b40304540c100b41c080c1401039505004400c540d128400420280703c3c1c8425124050490040b41c1d5169685904010f0441e9100c600450300d110303044560460360b4800d900c1030800056000b05042008c0d00d99600308401c9406c44400c546010f541d507111440e00c94190840c02000c02c0941e504030f41c8500c050700400282010b2020102e0094010f00304010b1504004800c48410340101c0c02c00040c0750311810325401002816402c01000c42c800025064180175140c00348000540c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 302426879 1250 302425629 302425639
    0x50a060302032b03051b1309050903180d290108161203030c09051801090c020616032301030302100b100909020304020f0a030c060207060216050910180209 68
    0x2e645950090b020340002c10a0300e00031003c800c0000c98007442600710a4100315406c00c005d910720300c40d09000d03203240e00c041c4024404176100881000080300c40e014480d8446140b20265060259400b0f11310804000514241d10412000c480b00080140200403c0020007109800c02c0c204120404042e04401c4207000b0000e01388030310315800707141640300c800800c1524404411b140101d1020740e002d401400394010f85406000c3e01000c089005c2e00d440c08142c50b41c030316805000e1883d500d0840410200d85003500c001007150090000c02c007401c410940048402d0b8054500003c0040d1468211100f120902c0c00d40c1c005448014000410300d50300044446000862002c104030000902c42007011601107441000082540701d03000b0401035016038041c5074440c0c00603118484c9608090002041590542c004681849414506102d900e90410660010b440c031400103200c001e6401c4846801550f107031140901c900c9038000011041d41c81ea840400c014203880111000d48180e45115802079000396860724020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 302428129 1250 302426879 302426893
    0x50303091b0a050f0108040c1a070309080a0305041802040801050a0207050d0e1c05012a08010f290d09050304051021020a1b05060403080c03090c12010f050a06030203 73
    0xd4030b0300d5030051044a2008000e08201a100c0b00150340c44580207006803a40c060520001032054214108080700f92a81c030f0095503a0341c02482c000d458042c0c1d68005401701ea00c50001640000d401000710703015502c800710412410121200341c280640b16a4000301a19401c01003400303500e0440e41c000c0c0c80301c00e00c40c0c400c1e1419408000c00c101d4102150501c5180e004600c80c000c580401a013400e18084c8501680c0089500484086404000c1e014060300c40c44130804d4030072604041c3c3c0d20407001c03405044c0341e441003a01c40b440c041c0e525103910f140710143c08848400c0c2014407046404c0000310391102807200c60522403524181040e5440c0c4e0401c2c03154902458001800780001032090b1120b540507041902c0f50102d90202c03440602c001e4200029002c207119411101001d8500d8220f21180c20501c120f00400481c582854000c00501c0050604410107109006201054002003003030102c1c50320507101c007190307202c15903901400740c0300103c21010350740c2c9040d05003e5408007030b42014060300d00903003c543d06 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 302429379 1250 302428129 302428183
    0x2032a01030f0209180c0d1b0f170106180305061e0a0204063e010f060e09030912070b0403060905010b0306040206040306052508160f09090207080705030309 69
    0x5030310039044d0b1254400516108030b0010414024110f800c2180449040d061010000009040b910107007410300c40c52000000100740c05500039980106107003c4c1c86c01c010141d26002c00501421018003449090100004441c504000294840c000a54005084816504214085a1002c0500510b0588108400001805035035450089a04503900c5a07100149284a03c0345075078070041c82000d00c1000c1013034005001c0d5101400700c1d034142d1903220310000142030088054450881c0c40c2c0764407050310600c041c0e04001900d00701000ba16003480e01507030312810503400c02038110300b454040e40000c0c5c140030000c02c4c0807090010b254406280c01d48618000c00100c00050101aa03c450441d002984210100020300010b101e5802058201c2e002d21440c1c6101da001e02d0304100110141340c0d4070b10000d01c80c001003000001505401c40d288401904000d412040c803190b000b4801281c2d401034a85054000803244100301c1d0580445082540090542c0e840e8100401038a07103d01c1030140c040c0d140000180c280207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 302430629 1250 302429379 302429381
    0x10e0105071d1203270102010911040213050907091418010506070503070f0b0a0b090103120f050d09030206010812030f0403030c1205070306080d050309060a0902032a01030f 76
    0x202401c441d4589921101c0c0c820303100c042d09501d04030590340003040f03181e0802c20a4020000743c1402456500c2402480c0704085410061440b0300f400d8604580c14498060b0114070419071881149070280c0c0d01513079507005091582c204116550080390008254002c0052103940100008281d4150941800c09914a82c2c2003000310a000c42402c0c190035046c2c03004201038a0f0410007041402d04ca041a01d0824590b81c603501c020742c4080c4400e82c1d1000c0c1000402c80800c019118408940d4000c0b90405a1941151221040e0410301080e0b50305202c0580184900b00f4020b0381540c07100e591002c0244116070051170000d46501e801e2055840901ca4040810958a81c407003d0320310451140c10358400650711034070220b019282c2003e640d010301ca62060f544880c9403c0740202ca108019640340071582030f00d8612064940f00b20201e071481002402d00038807800d620041841604070000e00808240e036101d0f400003d0038540441e100c00850b1420340301c0749108188090742d420150700d003600c04015214411013914 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 302431879 1250 302430629 302430631
    0x20a05160308090d05040e060103021b0123090303091b04180503190504080c0d06090816120c0506040b070519020d18080613140d020a0b15150307050f0d05040203010e0105 75
    0x7c42c903c40c0c1c2c500042d46c84d41301c0c1e4050000d803515084170144420785490782c107085507409410b41c0c0981c01c000b090080c0320402e418419802c120b907407000350316510b0303c00350140d2182140a2851182c1c0c44880b4441240c1d5119008250124070602c120b4040c6065803420f141d41b540413071800302418848540c529217240c0140d05407030480307140b600904900350001d01000b0648901d0383e0701b1a0b0702540c0701d01c031401060b04940917110a1007005d02006c0689221300700345d244505e800d60b180080000302c55042001034004180306030099805a140da680341c85010055546009814041d01100c4200d01d0280da9141c3c005030411414195864001740c105030031015001e50b880c0d034041c0ca800741d4804400300e2010038018607402005401041d0072640080308503012410b0190900a40005a0007105484140600103015640060b8000f1400403c80c4010021405c080d85007101041c244070003000003403185001e2030441c0c01004050b030300c5559a003424044a0010981030754180d00940c82c06210301c0c0d07a014140301e05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 302433129 1250 302431879 302431889
    0x305273105070903150f0c03020a02010605101403100806040821040b011403013206060304111513030b0f0a0c0206130314040803030415020406090504020a05160308090d0504 76
    0x140f9000742180c60780c1c0f48942103141a004819035450032041ca4070050b01c240c642851031981c0c0580c0d5040c090b08001d0a4411580009104010300c2a00c1900c058200d030f030f004110306c410b1148980700ea039140500b0783c816a2903070028131603001d403800700410000c11400821804c02d114140d01100c01608641d0507000300c0c2114000e201c0740c00c40c0c0043c00700c081c42025617144c2d040c0082c008101c00b265002c0d1095a007420003071903103c0f00c80b49042203410441001505034010f030281c41143c21468141c40c6c0d10894402d01d400140901300007160300b690f410300d02d000c0702c101200c03961051140e165280703850350039110200c40f000c1807000c07424003180c09194580550b20040f9007903402000a9154040d50316a500541c45c0102c080c400b1030301c10220f5840c41080548001c041103005543c80345064189556440d410b0031030168030520402050102c80d42102c940030546000f50350040c1c07560104030341030b01c0c2ea207c1e400500404800f400401402c05a1021286203e01c62000c1a1483c890180d01e05030f509001e04d0040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 302434379 1250 302433129 302433137
    0x40308040e01080d120b0d02220b060309070e060312040e0709083904050f010504110c060a0f090b090601060315030b13020a0b0a0909110304030527310507 68
    0x2141c100c1c6601e0350406c0382c0990008209600d024804e6002903622a0300708044c0075914106050200f01c1a100d00c1900b444c03081c10355049180d450729070750070707501c4904a01641d03100d07541c12030102d991a102003183c0c03207112104240c1e5654407511003e81c4401d03260200c803200001000400d01255541d40801c2c1801c600b5050740c0d44c8007030340d041f4450700400604aa00d0f070f581c00c417119014800c0d072696240619802012103003081c20055040905110603192170311181250078000700b0603480880310014095074000015800010070300745c119800340141c562500040c06840e07484040c08070400011440318100c13159900e082103000e0b41604403001d010480d00c0003820121103203000400c140908002000302a100828071803a9545610280c10b5a8200c1088030001a1440606101141c43c0d4401c0c48200c80ca0345140c80e09510f0310340c4d4014a82c1c400d41048000e4844050352000340d6031000701c044030300c98000801d01100b090041d00103039000015000101d00342c40940705d01c1403c3c8105440b03054000d6007240e031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 302435629 1250 302434379 302434397
    0x181202151602090612010f02070c0b12190f0c021b011b0209090a02030a0c1401050324030a05010e030d0506120a02010c080d050f01181a2103040308040e01080d 70
    0x200618a04020905500000c212403420307030002c3d081c447c100060f41c4d410401030f15095607092810044c1e00136040000424001c000c90003030280d488070030952100c00210141c19420446081c07002408107001c0341c030007280c10a00515085600031620071b0740400b410300d0241c0c1c2081080300468561000c0119426017503080c00300e00000d0b040017107005500013454405c9801286a55006c2898201c08000030b49410003c1c0d0005e220041400e0303044404080246803403821414821640702c1402d15400e1040106480348003042e049490501c0490500b41d00301000700b01c07501d50b0840c11601c95000c00594003e142ca0300307002403140d160041e0003000140710200200440c2510341d0055940340014172098600c07050074402410321b000f5038001d0500c41e2640b880c10740c40c3c0d5490b00104d080c00801c0b00046480142c1400310f02d280322201c40c4240d01511000700e44000c4c0e05400e07c2180502c0380b003c80b04408060000003404000d2014060003030049549000261099a0362101c0c401d8640e4980300b01c207400200c03403407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 302436879 1250 302435629 302435633
    0xd0b0910110f090a180e1005070801090e0c040e010b030705180408030613110405010f030c0f05030703060e0a0b10090b04060513050d03031401060c0f121812021516 72
    0x1d00a040511005014004c07403644462001d000991180160a00d030360322403601c00c90348113050141c03806030300d5550010f0140342481c0c400034010000501903081050f90355021225440000c20540d440c10502810820041d0048803030140039280b04142c00c0e029200d0f219001031181041c0b440903583c0846441c0c0507840b42c0720340e526450ba5a102406981e0322000d200d503c20001a6603101d0041c0c00303c600c14410784d41d58580000540075070341030042d0a00f850b20b048a4580c400b504800030014410300381c90a00c1d0341c0e5840420a80003440343c0d8100b0301c0b94405100c20040c00e4000c90303100c2010200121004c00c0107921307481040307480403940e01807500c6021050004208841c02800078064942401010011094980c004201d6200040c0c4003a8002521000c101c41c0c246c69415000d40580554689500a51003c1d101c500d20b0384440403008003005c24811400c0c0e205842808140440305250509540f1156a000199610500c0d400c040c0c1c8100c2803041a02401080700d030071a00307849450380d51070405050355 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 302438129 1250 302436879 302436907
    0x20d18031101020a02030706020304030611090603070807031d0c030c1012050702010f020a03020d110a0203180a0807080f28140a020a06180503061b0310050d0b091011 73
    0x41d890241584507050b19403005907000d10100000d08256070007180c44901d1030810f00705170b48048011803800041002082801d840d06412242c0c800c41608000045882d07004003100144002ca40680c180580103015034030a240c04242c02d0100c0500b03c04860341c4404990802070f04440c100e0100010403404101c2c2496503049411070355000009000000e428402e003413001007a07070301042130040042c1c2d001964030960b0006101d0000070400c0405100c0c103100031028003030360768415840302c0d451218111185170456a00c036140c01015051030400e45064139a140741e465910240b41654041c10f002d469003009013420405200d200e40c400d402424081042076407201c02c0b4000140a61040720300904551001680314003151000500d45c80e40c98103280386118074070303121080c0e640d007049220b90028818400d0408a224200b02c4550310b461416a5a4450200488100c030050780b001e6041b1908011580c24002d1490b000c41c0325400c01000d9907480480304103140201c03040031070403985002c000c2c010a1080d6a131 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 302439379 1250 302438129 302438153
    0x5011e0206180f01020d0c0f0e010819110d050105010f020c0f06030a230105040e07030b0f1009050103060c09291c0203271b0f0a0e0a0c020d1803 64
    0x6107080e100d07007910343e40050342640e1280501d08a13503925100e50341b01a50340302420f620810081e28060704025078410008010a0004d09906140d4039900c5c850803000031194040740c5120000342e0f2682c0d981880094440c0581000d22600f8085405c08107143c980600103c1d400390200001031018180700011000c00400381c00c040c268100f0595034021020110280700c0360400b016000b10040c082940c54441048107480340300124200640202c40200f000400a41d90360350030075803820f14003a13140d0b5080b0500248250070f42c4a2116541044000018410356500c01810482c140d9520700d10240c45c1c0500c001e1048076003051201c2c245414800e40465803080d0007410074034041d80541070440700685803040c01d07a003058804a0460601070000541700700e5408c031000c08584900040c0c0440c2084a22907100031100700200d030702170005840e01c526142d98125042018050040507a1418100560f10500806072191258054403a03c0c0c00c04c082c603030042c0b07940d1440500084403d08114210ba4400b001680 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 302440629 1250 302439379 302439421
    0xd0f080703110f0114090a050c040b120a0807021e2d04060b040e07030608100b0109031e020909010506062203080f03090c0603060a06030203090a08040f05011e0206 72
    0x1010407880441d002803121210454064001040d540d200188400400001034184081d59111f0000d10300002c10110b0700008441c001c0340c00180400b2404007082c4400040004004a4040c3c40502020440c02d0006443c040340243e40c0610b0542d100400002290110740c03405902c20641c0004240b201140c940302d090b2061503035100e624004071003021500342c0d9555007001d411040081030038480c0c480f0310450107038440840d15050020526101d0155141d42c0780d041e42d0803a01c2e0711001c00d40010b0f409000c038000290ba00240080010090103422010003200c0c107802c0707200c3c4420501013074400c0c605000392805144000c00d2145841895031309050a02e40b140d400440da40403203180000410080320191060007440c107000c668a1501c86505e504007400035a03050721404051007408829192030007110192007442c180103a40e9103070048640d24058600c040181801c200080c0803d141100d9000b1400301c650a07201c0241d00301c0300d15144500c40200944850060744148001801d0503903039400ca00502c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 302441879 1250 302440629 302440637
    0x602060106032702100306030203030a2304050904020d03020f120a0f0e060a032301080a0201080f040b04062a030b030d08060d080a050c06040b010608070e01080a0c12090515060d0f080703 82
    0x503609c2d40402d04640105074010086920f64104440c0840004003040c2c9800e0000c0c282072515050000103400100043c2c80613000303c410480500425000300040780f494403c0c00e0496901881304901900c0c0c0d0351007010410005101c4100020181d80100c3c940300da244c00040c07000d400c0c080314400840040c05104a05a10070306440b1340106040c1884050a000e00b0201c0064100c440050001415051000e4074040c07400d0014010040801d8841070b05580042e40548042210302c550b031400d4400c400030180f0300c00148107824002c9540c40d0140d002983e01a4180c0a864201c0c80006040c4c411403411200c180c0c00800d08003208c00001c0c2070340010302d06e10210b4146907040c000e800f44003616204040307a04643c42c800c500c2c0140030490b000f000c481d5002c2c4180c50825403c41c80140000c2c10b5020180156186130380303400340a0880c500a0b5505420403003403550800210401d41019542ca9074441e02540108a4100105e005401c02000300061160803001608224800d540d41d207096a2010178240c00308 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 302443129 1250 302441879 302441891
    0x1017060402030703020702090103060609061707061803021c020a171015180204050301060510020d1112070318290f13090b091807120507050402030106020601060327021003 75
    0x1a941c03062350501840c0107402c00a00d0700d0a00443c0412500e5641084802102c1a00c4512030118009011029a1104d140c01c4c00c604250101e801041c544580000b54407962560141c41900451221907203003034000c592260700540e452603401580d114010940d285034210b411400364030403003604128480185040f850000c2540c0c1d1020005084912030b0b081007940d0009810802481d00340031f03050103400f04450ba620f590541d0180a1340e00d85c00e02c0c2d6541d040c00300c0d0b081e00f11101a030520400c2041c95040c64030a80e02c02c182c0c80c0060503241d070903590a240c01c0f460382011038100b10b94881e000d001405e03003031401b91600007208007011070780005902c1048070008000c3c0d08447e14444d04482d00403c400d10300403c1703c192110811500fa00c008000480d045000d011859011000141c400d00b228071071810040800703040c0c00c00070308003e010b130442074025000000004000d0b9000529034100ca0082c2c1c1d0800221404150402003d8825001800040c0c0d90608400141ca42080c580c0c03a094100c4c00d0000358 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 302444379 1250 302443129 302443133
    0x809070302210304180e01020406050304020d020307090e0d02210a0518040c0f030e0c090c280206060907020a0510020d20090f09220201050c0708010b10170604020307030207 76
    0x145078026004000c0e04007003045102e031217180d0f90281c003801303503c690002c1d8201424003000510a02000f00060302c20482da50f100c0c000c0d9217040c401c6402900c141c0b14140905460310f200301e07030f440f44405010300c014890800302440708090000001490b0b0020b916080c0b4014940e002104c4613040400303c103507009000e01c100241070381e4600c075882c13101c1c5d01c980700e546407194601e6002c1c003103d000c2d00c942d00341600040c4c0003d070140d071468001c0d5403050150004a498101400e0010301040182e02d400d802c440e40c04c004149050340000341c81d44120000c0b0748075146c4d83c1c0c411000320307261482d00c68001c225612084061559900350f8014000302000031070001481d03030343c2c1c4001d81c00032010b4071612804803100085039800342c1840065481101c0e0281d890240130305013400c0501d842e0014136980c040f025075001c81d600444e8803840c1219042d0105500b1914000e4880f50b205008021762214144111502902c0d2034445025800608840b405940306402a9480c182800301270351004000b402019402c1141c540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 302445629 1250 302444379 302444383
    0x14041b05070317130606090509100c02030409050414060c0c0303190e0307060c090503010c1d061c05010f121203110d060e060307050a05060403110609040e06070f080907030221 77
    0x48500c3c01880500d50b044d03401d08045040310361075004003e049062004110347c01000017040340301c40340d01e001c1c002100ca02c5682c08038154041c0d0341000101d80d00342814081489501100300303131340d0b00c0d12800340c03001ca4507034a40c1800719208000440e81150014000a07d00d00ea2009920b0420580d2101c003090b0134100341503450560b80850b400310350f001d55a205402c0c142c1d81c041400710241c00141d0081140010340c010250102c0f04484240380000345540c0d4178607517902c404050b503541c110305695201180d8107900d03501000d88030034014105416007543c000142541400c0d107181403c0d401064417080189036002c1100902007a9040c0034000900300a5081c0800b4144200001810469000c24190030240201400c00d20950702062007604045024051540c50904880450368032500c1035802580d42408a550b50142c1c0c1c0c5440e601500d0010407a034105c0e404107840d031140440750340700100b01580810549005509541600c4a075100f10002e10044c101030070b011206010001d03c0b145241c0d4411000c0b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 302446879 1250 302445629 302445631
    0x30605090718051e070219060b04020f0a1b030806061809130212031e030a0906090c1401030905030301090f020f1308070b1c1d060c0414041b05070317 66
    0x148509940f2002c02190b110a503422401c03045002e00e0451a40c100240020350300e801540744400103070000d5200b03030100b110301d5110000700b03e40030b803040d51a110f468002c41032a0700100d07440c1010403214031009001d959900d6a9a2080703505440e1034156813204410f02c082e075000700f0500b400785205180313600790569851640611075900700c2016900340c0f01c03a10521034140034000320000940e006020480c05001d09400318485040045440d60f03e07546c6904089015010b404400f40500d1326200d02da10511039012500c1b400d0382d52407103001e20910030040044088440c01030780905075400034001400140800c1e0030005540122800143c00d10242040404007580031807450082d10040380d004011960080c0b21920041602059880c1001c4c04480c40c80b48800c0407808252100395510200703100c1010000740c02040b15040750456415142c131072041001c590050082d06402c811261a50711507181c00d000b0b030307048010380038a48004d009440c603083d81d25401400c2c04900b40844109000c803c205655546 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 302448129 1250 302446879 302446919
    0x6080a060501021902130f06140f152b0207140d090308090a03060f020c07051507030c14010903090513020901050d0504020f06030709151b0b070201020c0d0306050f010206060a0306050907 82
    0x30109d103005c0390141410740408056000b03443c200c50301100d903604c41600030801c050b10b00450707030346000380034188844203072000031402c00702d01410302045c401c400340d80078001760bd02c1041407014620000d85150b94501000203620006210200d080c80003650b02c0d8007409445a000d0700030314110791680d03240019940390101e1080c101d0760208210403d0a003c2050100408082e1103c104640b04420080724a03c80c1810140c18801c84280300010440c0c0071122103918000740c0000c000354455403400419111603441114452188406d07004a500303024821200d070040140c50301c0d450440701300440000350400030020703030380000600085182900c403400214442d2001e980c80d44070301170411880c542d0210503110300c2010885005109001582818200781d0043d80007144c229869031800c1d8101d029205149003050280140c20303100305441e4064100c9800c0c3ca40803240210074405640049a6070f1030300b1510b0390f92044411a0400114801d6030001c0d40080e081401c0d201b0954480003220f0000f2085a20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 302449379 1250 302448129 302448131
    0x1906020f040b190c02060313020f100503070306050f03250308130305060a150306020705161e0801020c070b070503041e030201030f09030f0e0109120b0106080a060501021902130f 78
    0x5a1140555525801c9200c10400d00300380e11350b80782c1034001c41d44a01009010035003c08031f200c101d109540c0d40c02d921000304100140001c0000c010404010010b400039a80301e404079041140104071484c00c0d00d0041c007414000380007000300881001c108034101120b00e4041981650b40d00c0e000c07000c01e941074000c03c001c51003c10045a2185946411031030300308003e06a0038003610380444c15610148000000c2c045030381014025071521102c3c100b0340c1c10b00c1d090010090b1840e40140313001440c406902d100c201521498151400e9140d5140c4411b401c0c0d125164000c5401d030004042400701c1c1b0340c01d0000d0300300b03140603d00720f90806842e04061080400800e80b50151401d0401c001c204540c0d040c0507a0000020055080c00034000540d030141140002c010454144481c400d5031041503445120440003c0c501411500c0c4106000d0501260740b0b2820302031100003c50050014480c2c6110f402850200d6506a00509184100c07600080807041251000c0340e0000840c08903034000e10090040588000809170 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 302450629 1250 302449379 302449387
    0x71e0b2d011d07181401020c04090b0a0b0f0a15051908241f0c0203011407030c0504060c080304140d02060a060609080c04021303020603070c03030506040b031906020f040b 75
    0xc0e50441d02c910081c8480204031000300003a540e424025480300441c2e80c1180c600da0340100880060f0b00344032041c0c04e0240c0007840c0a0080050050035900c103030180d80d000714200000001c480a1204080109042c20b41119280408000608452400000c8000c03940b60040c20f18485013502c941c06400c0c441a6000505490203005101491448109640c1c2044480238202542100490f04440c041b68890042c10003844000703051034003666103100250760041c020403844101151100f8004400d8880c0342c0000e140a01d05d041ca40d0003042120151003654940c45040202540c45003159800204211036048490030880c04c03d401c100f01d6417a030368269801912040c54000b2035401107533020b500800801400d00010000700c0c2c00455000c502e01c070251405070743c0d0b1304100505070b405c00b640d90000750454400030401200d1584034003d110091b10036901070140d030b265882044103480380181c0066050b00405000c10a1a84103040c50302d00718896400503040031000c0342c0c182d00541041d4000300c20040002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 302451879 1250 302450629 302450669
    0x1e06050402040b0a05010f0e010203090a06050301030b010509040c0b03061804050f06250e030f03041514071a040c0e1003060f02040e041b1a071e0b2d01 67
    0x4041c040b0007901c04e88480720b03c1da10300b0300000d2800440320380f9101440813600b00200c180c0d20a0040302c1511001810035210180d944600400c079a20912040e20501c0c0450004a0f0914111403203a0081b038208031443d0070780e41031501e050b500b9880070b170031240d204050003140c07003400b091000304d41d1055000d04060420140e500c982541030840c0101102c000404500c142012604030070300404d4a2021031410014055070100402d18080d900d0002e4480344c84007150000f00c0c10b0b151080c10004030107590310384001c0844a580304805003d152401001551040c85188505008402c110750290042c40b403e60100c2c0e0714408140c0802c01550307814520948501c081c403d020180c09a601d92400d007600840c54203142203803002070441d014000504004201d8000403c050060b0750b502d000c1c10711100200e0102c842d40600900d03960260400300c4d404d150840d1803141075001c0300c4116001c1600400610301c15942d6020505403180c103041304040b04c030b00d2141c0945454480020050203414821880e0008000d08 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 302453129 1250 302451879 302451881
    0x2a15091a07020129011707080a0c0c02030601090501060f0203040501050711010c0606080106082814070e160e04140103020103020f0705030304050a020103060f0609120602040e130209090102070b010506071e0605040204 95
    0x10340c010035030a600c506c107000d00710743c0c000001396101d200c0d40000150b1220b80309c8211441000390303001a502d8415200042501c0800c6e40c850341c100d071416100d0090308520700c80e0603601d03401030707110b010b012034814401d04000c07174920501003c2c80c46052410f40041d105030340e60300e001c032545d60f005036483c9da55454043c46205020040c13941900c07401101c56030305100601400c1e18850841000900e8050f8400810061410030080140580b652046000308c918080c42c2c21310600e400e50701304000240354160f00c0c841e942001c1c0300e40341170784400e540c01c044070b6070854005401962054801061400e010484040469024005503020b0740c03040002d8401000603000050541c0c80681009540c250041400c10646410106010407500c1c070904000032804030742010700007809140e00089030454034400b00001c02076040c1d01c0d00c49040c4204c6120300580c0b180c41c032281c200c0c0a50100181450000401480a4501b0300042c0100350f20441c030f030040103642e004c0c17144031354180b030041260020b460302e00380400c610381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 302454379 1250 302453129 302453147
    0x60c0a060f1107020f1906020604050d0c0506060411090d0c0e011a0307030b03010b04091110030b030d0e12370f02040b012a15091a0702012901 63
    0x4106101c03482e50b40d00041490312804800074411552040a01015103488401c80d00c600c840c00c0a880703001d6601c1c0d8000c2c0d00c48400302c0f000c6449000700c0400700e411032700525503080e00350340200c0100100e82d074800500c4002e01559507500111174007030180c0c110503500c0312a910109441201c841c9a51441d08034401004c440682041d1000c404000c2e044100000030030540760f00641516010652114070b9011900505800003055001410441c1c00c07402e1040d107410544101c001645c04000002031000708400b210300054003660306422001c030102c14140310f2202260348000007418210315000d080c1c1c10358a031181c0388100b81200150f40c1c2c48208000a90115004e450030303094900f8a022003103544509001440070f000910840c0d5078070400c3c00c1c0741d100f4160491480400d07a210110030f140300b4040041c00103072103402c94400301440b00f2594410800d0003002074455010303d035019002811001c0c060003180c010079850456694008800321851640c01c158000d4001e1b284440006004000040c11025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 302455629 1250 302454379 302454401
    0x2060a090807150e0a08070b0f060307050f04020d390206071b0203100506031018030507080d020a031407020d0c32010204051002060c2205060c0a06 65
    0x124103224100070590150803205a10303841441103071141e0748144240020074002d803440140f8441c028174103040001540040c00300300d0083c112031915a81d200a50076120f4011034030b441d01604a401d04000b982059407851040303030740042000d4104001fa00100c1d0450b103401803070108000d07145406c02141c902c07403c2c1c0b81030401d80422020b000b0410043e000303599007030050148400c0050803c0d40c83c080440b07a403d100302c1e99a00605548440700032a4100e000341c041035400318402e0150803d102564461486001400e541078110000406034941f01a10f10b1f801200040d102c4120411262000c418244000d001200c02510001001403902300c6600c4150740003411034065500691080340036642114849410300d91101010b05081500d0403056602520303810400e4504034681035000c40d411040d0083d1003604e00c2507402d40904030f85103200f240d4401080e101c601c032058041010300c4446615400840a0980d19405041640c1c4e6840110f0036640c800d5403440b4151304540354044c100445400340c455100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 302456879 1250 302455629 302455631
    0x4201c0b18060c120403090302270114010e0d110904080d1a06031902090301021201080f030f0d09030c020d060f05010506090f010516020406080a1502030c030403030c090f06020d02060a 81
    0x22401c86003d03102032003041d283c048503000c1c840000e8101481495444007450340542400e407281442c3e060615000070010780320507007100c03a400204070000c000b080b044810405940e2030120194170001d1006161500c00c040d0b4214003c0250104682c07206140240109e214215865658104101c803804840d045199400c0c10011152201c2061b80c0380c409a9400600260740764186441c004036400080c0f00c0d050b001900743d4004101c610150818042940c1207410706010340b01c20254200049407203104070f04980701c00b50001d200084d50b0b40e40907030000b4000c9209080c03416042c41c0301e800048035120001d00895500783c6030040a804800640a024014103060303c015040408180c0002c0d2014030b6420018104400464122042c19407412200400c1d600a4003c000c6282c50b9150180c807881d42039415644e0403004004403560028600c2120f101d83c044045440c1075844070340d82100586019021801001400f5101045003401800f51200034201a0001c00350840c030703404080d08100c00200f1022541e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 302458129 1250 302456879 302456881
    0x90705060f0a1b210e09070801050111071a0414060702031f090803010b091f14071a070507260d0b01020f010c050a0201060b030603060f09070f15140304201c0b1806 72
    0x207d6000080c0c141902c2003400c00c68482030b0202059403404a1a52002a43d800c1008a441035003450600420a0795a186e0541c0e519505100c1030056600c140ca4000f0f4143e4850581c412813224643d0010748041c04001010403408800e8070703000140e40007030300808404403000a030303032046180000815040000108a6080030350981d08080c00014000411607041c041c002901400c100382d5210040603008244900c1116040c18070000b006908580340858800c403061082c0815010103055941800d82d4150041c0c3c0340004400041d8043d2004a4415040d48542c11029030200020300072103040001a5940307d07114403d0040c02030a45642c0e901800d0310140410901c40c06490200c0e041707a10841803170a000040d201d02084030315040603070307210906881441c100415019848601c5480d9140d02e0790b03994400707100c2402c681000d031009030340c02000301c40c1503032a22140d4041611940280301c8028210543e041c0c038400c980080602101c0d0840700085881e00704886102d11210400840780000020151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 302459379 1250 302458129 302458141
    0x1031a0310050702030c070e0103031116090c03021620010c11120c120703110a1d0601050f04080709060b070c1a07060e06090705060f0a1b210e09 64
    0x9804030303140094141e40c0c035880018081c41c0200120394800300c6d29403c6820407541d8508150003160280001c81c0081d5484808124100000810000035213449410391280c6d40f8144114000b001c0500200c4103040d024820b0741290380300ba859403040680910345484110b0140c0d01ea210700ca6001e544220b051001c24180b0001142582242100720b0105640c9240080340100410707152590b034480490740081092180408044085580c40c1201d1042044032a005030000c02c00007210381c1400340c81e0404624a2490084222484080c0d4000300c040c1080351030203204c03028051031540181c200292550004404001400f00c51003042d009104550910b800d00e00180d4804400c2a03903842110115080406011070302d101107c1254010340e0700600400c000c1e202c440300c0f15141c01040350080d83c28040d4020005641c1402c00031104400b80b0b0380503562910841407016103c8004060600042c1c11241c00305070001202c2181041c0444c400740c1004030780c00c0038480018850750360b10a903d0b008603461014801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 302460629 1250 302459379 302459383
    0xc1608011a04110408010501080f07091b120f0c020c011b2f03010f0911010c0803070f0504090c03050f070302040b0909040609050a03030c09060201060b03060405061807030b01031a03 80
    0x4102482242c01150f801000300c1038003058042c0d90070400d0903518143c00091282c0c3c000450118005040c420395500590704c40c541070441d0030108524559116100e441d080281c0b0910794001e08600403000041d1541c0240400c008a441d0040c004004d64020702c1014295a0001e5848503010b029280341d20144503169a11101903400a40e010110a6502200e2924aa4089185040c3c8002030020000783c100c199090001e01004178003030300d40c4003514842c02134551081462044031a0451451484d40d00c0e5120201c0f0b215208013114020040b052201050380c140d45d000c5c240200904c3e0f0340110740350402c1a1140180100542054140751040008100801041c000d80710b000102f00c51041c5c842e81c5508024003c0c4c0f0000d50014040d004111411040540642c82070f0800c2d1016038503180d0807038640c3d05c1a0308a40c00c502071540041c2c005e200140b5a4a090780005500580c06042c08034141c44d8444c07291001c0509440c1100442d8441c40300c0081546d0621407034007446040c203150040380e02c1c44408a0303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 302461879 1250 302460629 302460671
    0x80f06091e070e13060e0114043201060608060a1202060f12041a0114010507110d0c03050102090f0402091003051005060a030b120601081b03120c160801 67
    0xe50768048001d45140c1020030300c800c6004040d414040102842c00103000000034810a40840b5040c0c41c115542c0c0000c0303014415413202c0d07005e02a410520740c46a171281024640000c00b41a28105102c42402c0c2d038003408040440c040215000100b03640742003407809041c200c40101154040c60020200b0000d03400f0f8034403038200c503540607141a42d4078480c180000f2028400c2c070015040081c0d0303000c2407004004d034902c2c1d4a582200010407140366a43c80e41421648208056540f60003e00140700c15000b0402c451400f05070310500800303c0118152641d20710305000d0a550054810b658003040700c13441414000c6401c090520101d40c21450201d918001811490000c190344040654500c005802d642003c4a54030280c81c0040c41c2549610001000401400120b49680d0044280780301805c1c45c03c000091003030603074100c0809040c0381da408100b4080603012000e810b59040c81001c82109100c2c003060002c09140b210030010700342e01100000124413024287c0c0c80920103078074043c030408603904c44052007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 302463129 1250 302461879 302461903
    0x311160614280f0209061612030209060f0c072705010602120a080613180201020c0d0c06081906030c050f0306071d01020a020405131703040804180207050d0801080f0609 74
    0x3035800303c0c20403400000c2c0100c1c660780741c00410010780082d9a0200c080703416102442036102c6040402d03041c404400384d000d5520400e030841c209114441e031424000d40500600c01c0d00b03000700c40400d50f9075402000701c1440415120428a0710300441d446415017401103a000d08100c0c0002c1800c140e41c0b041c004014070803400108108400040803550f603581d02c0c8608200b071288003905229200d00c2c000e40301c407001480703001240540300740031840b0403a01740740d89800419600100782c518804c1c40c000c1c0598001e2401017201050100c2690000b455000c24803c25020718024240d850714a4240805c1c08407401040c0d9109100e40d01c500b0800444e507501104401d80011041c4c83d41410010110050b460000a28802544182018104140661401d5484a005002d518041a000c4014090f481e007844151809090890108000d100c80c2100900c540801d91001c6001480c1c40204c5d26a141400c1c246240d05001a003403074010008003804004040512503004060030041c18013a482e190344a12003040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 302464379 1250 302463129 302463131
    0xc1014151e19030602130812040b0a0c0606090914033f0903090102061e060103020a0507020402030a1406030114150a03080c100c08010302060703031116061428 70
    0x2401c6000d0302d80b02c4200d110740e000040140105522458041e01075088181105103198036404002015a0b00013500d000c400f41c13104005251504121080a1940c00090781d81c0602181c0304000001409074442d020003400315600002e0002c1603450402d03d04020901c1e000130030f62081c45841d00a40e0043c40c000d44072489900f03049003018000c00f9005260341c09040c55501400d1510410000d15030200050a035120f0903800c1e1940c41e65007400d221400852070b000d00990000440000d034003035000740c0c018064541542030682c1001206c1e4006016680200c0e108210540c5074000c40312091111074100e07030450f404400a019035211100d1040b82c2450040a503201d4030040c0c00480d9140c1c40d00c40c129000b86400400d1544d44007200b4846a640d4404054902041460842545411031050201c00d040c0c9500401d05031400c8a681c40440107001039800c580c101c00d000300a454030385280c0d51401455580300340008103a40d60302c0c10920b04944030003403070280001d00045110b0f1506c4809030380c4084410752820 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 302465629 1250 302464379 302464429
    0x3150705090f01020c03010f050a06050a0e010b0c160b1908010815040204180309080d0c030f051c062304060602030406051602090c0d0515010e01030905030c101415 72
    0x100c2c64817892580044d01035281c604844207943c800c1d04100e20078040b000d030500102c1e65500500030004402e10902c05c4040303800c0d00500c0390010707000040020100c2d542c1162507501080d40c40c4c004514841e80601950000000d016074000f81d184140c030442c4459091210481d032400c62010f4880e01158045510140d01400080465450390300136044441d200f07040c4850f42d040c900c0c01074031001c01c0307004410592083c803041a26040c07144503052b079103e61581d01c0381d04e00c404250050f241500030b0b544000301800340000c0319068401c01e2081000508540b811003004036401040c000c3c1440d5066442e034002c0307007071280c00d00107142c00000b10303000c8900341c0c50100d0380c07140d99243c1001c001440000c000d41c461140400c1c8400001b158000d040c440c44403420801c8140c9503800041d1552440310441400300705c2d20703010b50407250302a03400b00c01c1d00d03805002a01e00d010702c2034050038200350007282c04950f0943e13211801c01001140e6410b441d80f205d0241402c03000e180103100000d4401c46015110741074284008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 302466879 1250 302465629 302465659
    0xb01110706260f04230309040b0d020907020d12020c030a080c1201030f0b070804050c12030f19030b032e0f020c0114060109031a0a0b0a060306050315070509 69
    0x10038020b1452000c5034034112424a894041181c820986042e41c4045002d114040c00d0000e441502903107903980401585051400d0042c00041c0540002c03070365102c00923540d070b040940c541d90900b51051301c00c1d5019011803101f425015084c80d09120000c0a514814000d140c2c2d107110000485122646a041220407607641300c030b854406101700d10401c000d09030030100000822603060b00c60f105040c442c1d440320006643d081c004441c140b00840d0094640d61003c590402c590038148000084480030400307403450304c06458000d50f05036100401c4551032141003e80e051141750305214011501c0021406440d5060790b00d1405501d480c4651045103080803206a43c0d9076040031075001000304603108405544402410302070500812080c450903001601d00c2000170030a44c03007a1609000d8984c8412100fa000e0013a031540d000c0a4001000e20203015074551040d8265a45e24141c1e100605c0d0f19500803409600701000d06040c400081c1640260784015414002d025421109035250288151005103c00f9203403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 302468129 1250 302466879 302466917
    0xc050a02120c12040e010503010507050c030a0f030b1e12010908030a0506040906060303020c1e03150406020421051b1e010c15061a07020105032a1c0b01110706 70
    0x1006040903c0f00300098002840b1012200c624100d07003040300208016518403005407190f02c11900716072031603042000000b00046c01204d0440050440c1d10300068190064800f00d0100040343c1c0c1040044880480000c01c14645280700e0500014581c000344124401c03540c17504110700002d090880c9503920780002900c00e0700c4503401200308a4000c0c000f0700402e82e0368100030f900d500103050814080c5201030390074942484d020041450000300680100740c11907140c400600310060217041200d1031074003003100190340301c8180018030001a05810807030750b8041ca8540646040c0302080c480c84031140c2d00c0c0f50041d007580c49081c113400b0740c21391500c0c0c4074084000000489039194089002886081528646100c01909a02610989400703844200d080e840d04540400c4034007a018000780050340420020b1500c0050915600c2000107220050589026042c0f2103103464010b003942040481817015084080c03000d030b00950011031001c3c03c01040e02c01d4601d400e661070310058080e4a00384030107461a00201c050f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 302469379 1250 302468129 302468143
    0x50f21030d05010f061115060d080705010f1410030b040206070f0611030915061005070c09051302211c14071b0608130b151806040c050a02120c 63
    0x41c0c060304015942e181c5a5004081000340145000240008003140c2c09460020b002d16607a55601c1241c103050f40c0d08001c22501481d810070841c3c1d509401d0120000003a400d0189404902d0540004101c0c06990070700740540e0603000340405041600300f00204045014443c0803900142c05560b031503550035043c1801130903242e0040c3e004001c5890901041010040c0402a50103007802e102a0750b0f102c050040052601c0d0320903101580e201890581c0344481c140110000c00c6010320407001b0100d2a40d480f4202d20842c0c0d421582d4110111144014070118a0302c004c02c040825002ea20100c100c155081045580e071480c43c0180030050140c805124440b40949002021031039801c0c41d041e0f5400aa00d08013107c10401c040c81a54035016031408034a1500403840c16201d40d906203035400c03085030592144042d0f408064078014080c07201c201070309002d071600307000b8408194680003080c215003400c00c00d000841d0328600c010420003c00744803e184195012031200c124000707201403141c44c0e0f44581c65080c10161 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 302470629 1250 302469379 302469397
    0xf030a05061509060d140a0c020d050a0815030a05060903090a090e030703030c18060c0b0901050f04030e040204030f1b05011d280312110715181a04030c050f2103 71
    0x3100b0010864031f0b803d00d41002044513580e509a031400c1700c0c0e17540c05079100d0142544400100e250280020b0040c1c1c85203600d0b072010000142142d1a080080e101c8900307000040c2e4503c2019000050740607110300f015a0107400400750a2001c1001d0400f101005850307000d001002000c258680300307513985403441126034030715041010132440d10f1586e4440016048140c1c0040445480c0918030000f901c00d0010b01c5400d205040010758404c05a88035601150340402904c1038950003a0b007404044007003400b0840c0e0201c002c0c8105180442c110103d02600100760960b0b128a042104c2c00c039080702c041249184c10010302c081a0b5140008650a0390825008809520345048508100900006225504070146100005e584600f41400d4480700295141e044c50f001ea8170071015021407504038a4850040c124011280030030901d1642e464203e80d25018000b2200942c814102190600c14080d00c0e0b6560002008125059800100c118001ca0500161410803040004501c0307000090000c0500455034484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 302471879 1250 302470629 302470661
    0x702150a0c110106120b06060403020d020909120a0305190509070b090d0618020a060201060602150a020d050702010b011407020a050d23030310080a1a0c0c030f030a05061509060d 78
    0x341c41760000d513240340603500151203100c40310021500c50b05101e42204c05494003c0c000e07118410040e0240b00303000f01d0152019405101d4a04403c10f5540b20700e0240111441c16034002c502170810580c0b03200542c3c241f181c400010f030702e02000e208000f80006100c5045640710a00d40f91640e80801c000f40d031200188101a0109040c00c0400240d1212041862030b2240700700c1d890b401c01c540b0b50700200c1c03c0f264103000342e1015a00c00c0c0d07425225809014030b100da0051081001500d40760b070107607490040d10740a8500e02d015070745900038001250f810902c03a05081442e0a506414002c19400261440c0c6035846045d004030903215140d001c0c06412510034020880d500d5401180300c08600d069a520b0384101c610f41550b0060030400b144440c80440c2403504241c00c0561031107103410461f1649000322026040c170100b204200101c03802140140050706000307220004003174403880e01648035016240002c180600c15103040501c500858680c4056440700b04050b0b40c4161110003a400480041001e01c1c0d4240c0c40c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 302473129 1250 302471879 302471891
    0x40b0d05060609010f0602060703110c0d09030201020f15240a030c0e1303200c1003140601050705070303122a02010c020f0706030e120f030f0702150a0c1101 69
    0x40003000400c1c9009540039070b4190801e0384e81d0890085075110a004401c0160064804600064425041a0201ca00f6000000d2a10301a080a64a8403d0200c03130580442d1943c0c804006568050045d030407113000c0309000d00316074607240340d00d0014000c00801350f00c500c040c2c0803614464000c1102d00f90100300c801800203908151607044c2402140071521074a81180c59010008440c844501e410f54025a85a01d03240c00055014000c1f292920110191140b603125121040c01c040e90b4404040715051100e441c0040c0214040340072018030480140720074144101040303020300013070000400700222605031401a040c403d100c4107560141079540f48c081c464000b52118840103070030f41c41d00c0300148507580e0000c0041408050717041c0d884d045031b0181e1002c1d0b600034940410000c3e000380c000d1880781c81c41e00203981d1310520541240300150410301401402a001004001c042c508000425800c0034050004000451801c203407141c2d80704c40200ba00418a44541040c4000307401417202580d60320342e5900078461 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 302474379 1250 302473129 302473133
    0x105071703090304140303181e090117060a0507080105090c0d110406081509060f12010c05092806050a030b120c0a05060702030c040506060d02040303080f18100506040b0d 75
    0x20b01c4d040360181c80b40d65180c90700708500c1c070314001084950351482e04417501ca0041c03001c0c040050300420040150440d8001504c0c01e1816691039000c02d000e81003010740c0c035448032616900c403407410400610b1400001d16060910561680060080c1d04551089841801c181e403400d00d1001c2038026110707100c03500d50070b141880c0e403c040240e028000b900d04565400c0410384e02d5401030b07207450801c9403140f030308907130403801149590404480d04e03280103801030101c440c1190ba8101c0c0c07600719441d0004a400213140418284118608081480308068a00703113010059140c20b1041014082184582c1c8203000c00010200394450190b0411a064503000f401407001404030807002d230700e03000d03940b90052140d011070001240c40d281803419105a82c3e0040c006280c40d8407105c00748401490060440c0740e1149050203000f0001d6401d00003440610303c00d43d12080309042c6101d04c1c204482010f442c240302e0211079a406e401c03905002030300200c90b840040c0013003a29103906c40403d0081c601e40f9256070308500400c4200d02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 302475629 1250 302474379 302474383
    0x30c06020c090a05070c060e07030f0c1a07030f08061f09210f1b12080a08070503040f0209040c09020c0102040f0f06050d150b07030e01121a010507170309 68
    0x50703070203040d91001c100356030701c500050480b03000300c80000100703039030300c09607000300c0c46a900c80c0c0042d25191049440e801c1e1a42c54401c80d800903000e00301e0f4001802503042c0010304089c260045a450884007190801c1c000da0340282c01d42490308140b400b04200e0400092081e65841c801006090280d10080d10003044210014007140743e03402070500f07004c05440e00900d10010501002482c64000000d0703415020627035141c0581c058402e10310441144100d13030202d201311903020965901071190450f1a41c403440c801e0040c1c0120002844401032241c20300801010a0220b4190707030105e0743c1220b80c254a17a03500d2601c003030515159048410300c1d41c40807481c1090540f0550007013040d82c45504a02c0d80080d9140004103501c180350055800041c000c0c404014180c0329604100990019092100c005a4440e06154040d401503002680082c4c1c4101e01d20242d1f58010509a424403442ca4007408010150a0421018808501114100f140c009442001e0180b400003918420310b080034099544d06013101040c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 302476879 1250 302475629 302475643
    0x8071b051f05060103050627090f0d0203040603150f0909031403160305060f012a020d03080a0c03090519030e04050108060115051c0207020612010305030315060f0301051504030c0602 80
    0xc0c042880c101c0460705515160710080c001408100c11300c48250120686c8084103900527005003490b10078001c0240c00d040f428402007000301455401182c40e00e103409001002c0e11001d50351441d0440c2164824401041820b00d0360302900d2052201054003415840c04950300480301482100707910011051280c81031000c030083c54210b01c20795080c416901e03a8010050541035000805011540486c03401d10b228000449403040c4070750074420904580070b9070700425410741c00740e1001c400003048c0304100b001c1402c2c1c1d8400c0941d603c4561408205103c0595120750f40c07004403404034022500c2d04a1050100741c0300707683c2130030a060050014010341d6580d0300c3d1180c3d903030020b00601900c04542c2c240e010901344100150303900400000b840382000d0541050510096010035400e0360802400c015000310021a034020b14000c600c40e00c01590349250948a4100740042103144034031502003008044480c105a41c141c0741524011240c801d403c58410201c002688503940c0b00030070100c0006000601c09401142075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 302478129 1250 302476879 302476891
    0x160b181c0c032f100804020d0b1003060e190206090d06020d1506050a0206010905040c0801020c0f0717060105040203070921060c080105012001061e08010b0108071b051f05 75
    0x22202014071075148480f10714140582d690000149100802c80354441c00649410500140c010706490246859844c0d00c15022a60262a05007924040042040303d22603003240240c00b07406480b8612101141d1000c901c0250800b81c46440b0202c4d80d00c3c0c0c07036030768030032500c0015602002c119504c601c90031800014100d403402440280c0c840010005489005070215800381c0d03140d501814036a803c00007500c00810010700252040d128030f80000c124244248000c20780e40c000303080107150001940d0061403030603411341c000e1520a00001c0b1190700501000611606544084801603240d81d1403603070841e4030001603403110b0760b455449844070100710f0221a1f081c1c00c440c001d4500340709070202c0d4501034a1220080c450305001070000150315002d424840b10a83e060744240700080348142e6a0151082141800d00845004111481c401c00058000f4455810b030180203003070444e1b140c908103070060840e05580d80724103031804508100d0801c014084c040c00507001c0034001640b101909291040009007012220 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 302479379 1250 302478129 302478173
    0xf0405010b070330140a0603030903060c14030702061f05010c030302030a091a010305010b01090308090402071103161e150f090f06030506010305060316150e0909160b181c0c03 77
    0x82644d00c00280501001e507274058484003e0304c1d24550340e11000b482d007550800104606407804078400803000000707600800c61075004180b10b0070008003005440c44042c108102c5903800d20710806c02c0d81d800000342d0301c0322074150400580f02e80c0c80c0e043e50f0015103910440100b4200882d8030180c000c0d910000e10505a82c000d80003040164404c02c01500d13030402074040500700307907024800c403400c5107800c1d00100815889021508006840000403030b10306003a20319203460114841f5401c1c000d400c010400381820301c40030f0061201c10b80c030b01911003800b01c410084100030802c2e07464030b82200d54000e03003004009014010030946000d0341c0b400024004c02c8282d031110300017400c0c040840c3d04e614001400008001c0b040344044082854150118210440d41740e852062041d074405c0000156264220188100c0d0010081d00354400042848044058290810b4040000a01c0850403403440078849010f810350659100c003c188881d0241203862040361030040820842c44008000c01180c011444012980c0d003031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 302480629 1250 302479379 302479381
    0x303090b090105040f02040b1801090203150607020d02190b0a030b042307080a14090d02010b03030403120e1210150902040b09040515100503060f0405010b07033014 72
    0x11405098603400c4c1c4018203041089000e15000d454903511082800c04005e1014050b810302d0003894901110984c4080d194650200410610010041e0801d05400d001c0390110f01d0b210a550004030784040c0034602901501003120310b0b8944180211201001d88424880d01c0d80b15032032002c006000d00454407020303001d1030802c1115200c0f49149200c0701507900c80001d5000e000d45e00c1c0360080712080c000074041c90712140c1314001c1400d803241f000f240c1030040041c00301400e0011401240a400d4607410070941e80260f00401080000c580d07610f03d01403401d849450801134200300d0b0000181907075902441e100c00da000f1290381c4207038810241e002c0603d10340d038906460100e03a60781041c0301c2240118440d55030540810801c00102e0b146c5036104690117203880050440c1d01c84010041664203a4400b00300f0003040300001402140e10b0000c01c0340800060464081c0159810107a1000c1030b4042d144004041c041c01114208800c44956603411380c00020f0800300b010300c02c598250300080d2a003020341146452003d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 302481879 1250 302480629 302480641
    0x501021312080a031e0908090a05060309100c030914010b090604060807050d0813060c0b0a050c07060b0f041e0501170c0618060406050403050c01030c2a02030a0303090b 74
    0x21400500d51034101002d07a041112200c004d4001e0300c051001d5010341421380c0c130a03c09010f13041c07145a64139400359098944a203161020321510654542003144940c1e4140100b120000001030307040250b110382880818602140c21003980a0910024014040030101d1561140f6140c15440390960303460407580c80303560b0f454450505c0112111801103007441d40000c0c100b03100604090351218000e82c4607074021483e0100c0c22454122040540d089003000403a114210814001c2c25070b140740d008110281c00300094207084030401440d00c02c408005066a445041d818000e650f00d82044c580090054801e1002c4511013001d030050f40e0080410208041c540350021500602005458202c0303500c01c4000c0c40c0350300d02d41c010481544c00c40581c164903c0003401c4280625221400036000411a0b5200e1603201c50031031a00504041d0306c050340310b0406252071585802c04c2c1d800400e20104504903c0d40708c42507400403405010303503104030382d02135018425200007004140d8540c4c82040a98002c14007100540c5400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 302483129 1250 302481879 302481899
    0x1502033a0506061605071206020a09060e09010522050901050702190b0c030603100608030301050a120b1807030503030c130e07140d06150f0e04024305010213 69
    0xa650b00e5410000511410301d100e020003101295050164088514030713a50340c031031002c040030040c100b16001a0040354170300109030000302ca080600140c0c00e00364031580d0880041501c0359014400c40f881241e29039400080d031b003003120303030000e410003001c000784554a04410158042e1401342c2e088001071145c814401000400100d01c003466551000500d44507407aa1205180181c00c017400d140d03414014401252030048192160700c0042c541800a9602ca40c5000c04000c0c209070b03150700000d400904080c04000069211b28942d601440740040810490002185e5602c6e20000e9080140148000414015a469000007600c80c2201c0c0745160112251140a56501c1010540d40324001c1210000ca40300b803907c0c010301810070340c1c00c800030015201d695141070100768400100300760003054190703156200c2c1c542d01040f600701c00c000a54066107400c0040200c501c10310508559802035802d1400c084003610002d5103425800c050304034110281d9611820054001d5000621081000e0f085540004803010703d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 302484379 1250 302483129 302483131
    0x6030b0307090f0b0306011719080a030c050904110706050108010b03031818070c0b10060e1c0c230907080c03040606080706121103010308041502033a05 67
    0x202401030203240345444504409020180c02c000c2d8100e4642403e01d4080e1800c0010f14000e22081c4000b0202c009820316060410361360011007400303071001007507250210b01c804046680c0765899180004107880100002c4030240101c101c207070b40c003504042c42d0b142c80303012040141a0a030b0103840b0820003642d0f40c0300da0038226004040016007580050010042d1500e0b820b400b240d450300040d128411181e403001709055042012680c100100c1e02d8541d911041c8200e0f11811f650003000d120341c00c0002400d104001c2d040f143d5640d01d0911601721541e20000e56580f54030b103203401a5201c0048110746403114080c449016200c1c3c110030f81059031040027045c1e4a00500100d016544a4036141c40c40d4492441a0140d9403000308107941d041d49030440041c6c0800d080003010700811700c954441c802030f48004103503400c0c1d4184d00700c8103804080a0005001180ba01d0049604940f80900780c0a00840c10910a80c00c41c01440144501800325060541300184180451500d030008a4103942c00c11107144500802c64030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 302485629 1250 302484379 302484401
    0x30a1101060509060d1e03030614090403080c0d1506020303071101020a0503061e0312031e06130e0f030d0c0e030105040b1f0308070804061412071409030307030e0a0603 74
    0x4164400301390b680c104100304521150145440f80f425150304108814012030601d800c8000a54070b41d410029800001201c0d0700b1008100c075840030b6801c182c3c43c003c20000d0040c1412840d404001466400b040b202c6d0302480300d026002003819407141c0c3d01c2201940f0b030b030412524600413414241e4409441141071088950032441c60b15a10304548559080c4401a4072191090b001100d14000030262607a0070068440740030300c40564241d4910340000c1d40c0d0f054802c0624a403c20030b04e20310611038141d4034011340e043c003000304410000d256008040341d18500807c14491640c82c0c00000703010760003200b90b60000e0f0201c59590f103171090b13601520f40034903003203078402c95000d41070030002c4010860403604080300d403802424181c3c0c103141140d01c98580e807840360b0220b00115001a0300180030011180c0000030980d82d04010081030341403d408030742c1880340450040c94441040450f06140da441076102042c3c0704201340c080c0850380c603800c5501d0054030058041d000d01e0700c10240c2d1100024024405d014581e04c8030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 302486879 1250 302485629 302485639
    0xb070809070e0c0d0e25081002070c03211e020a030e0102070f090e070602010e030a080a090803070323060609120a060213090501060e060306220c02030a11010605 71
    0x41c1c0b0b0b1110100303a1038005000003991072020030a40c0c10240090140e041c00c200c00101034070281110140d00b12000503514040c038003403110450108802c0801240c0c5285d014600c02c4003603520701007890403490706c1c800c3e03401c01880741d95108008420032004000080c0660380684500d00c0c2d14030020890003040506c010400c0043e403145001c500000c0c4140c0f800710714803806004655101c1d07280e1594aa0712509600541d0f00940d48054201001d0010820a001000c550008201c81415000c14545034420741140c0340c03c1c000d4000100e003074092290f11100000350030000181c1c4900304a00010080c02c80581c121032a140320045006507181035159040c09181d005100e140b520300e640c402e00001a01c00305620582c1e0140355655804038507a40001c01e80c0000440a0003099814019014225541038120308200503400080b0700c010b895581c210717600000211002c800d07040da12401602c40d40c400f05401d0034000d0818068900c0650000003401c03400915440382d00c6000004240d15003220440d12039141c1c04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 302488129 1250 302486879 302486893
    0x302190b0412030e0618070b0a021e07080a030c02030f0d20030405131e02040b27150430120c0c1401030501090203040c050103020309031c06030b070809 67
    0x28075610311a0030000024280440c0c100f00382c4065904000c401c4514041751b410060414034030480030321040f0007a216204066007082c1003100c00030341e00c9025214052103091454000005200c0401000300206501c104a039804211417500411542c00340008a000f48030341c4400c48003403803000c40c00d001c0d15021a40c0d03003649408000b03210043c005d0314040416903400100404211900e4018a00707151813103528002c81c80f04520224116030f401290303000d11b07001c3e00c10f11007844031503101e000300c9400d440041e91143d00300011800e45130031403049010140c0c0c80781140948425400c102c0c005031084800c1c0120700074442000b201c2d0400c4182c40c2d6070440c0034501d60511280c0014184d0900285505250724000084903000c1d03071102650b01c1c0c1c03500080d84c1c03403040b000f240006680c180162405002002015415400d16594400b00c0700118015141030503004000500c20590030415500908000400d5118090100d00514000c01e09404140c9548083c500000d10b841c1c0031380f000c2401090003500174080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 302489379 1250 302488129 302488133
    0x2010f05151f09030b040b0f1b0414121b040c0c0314030901060f03260408300708030604051608070f02030d0212150f030d0c020f0d0f0302190b04 64
    0x5100018092002d00114a0012000c05c0741500101d10032442241d0701e81d55400c1040661580c035100501c210340302ca0000300780072515041e610a4504603074140c3c610380025107500d00000d2520308004c1e911405071090b00310710090300f065080c9055020001f500c081204c0816143c00b21a02411514007801041100a058100501e488003c50b409070602c4000a149522007088242291059006851032480e9909181d50040a4407281c403120348809140c40c6098607000c81e1079160710091041481c081220000203441c810898840400a2210401240d58540d1880e121034190029600305020310324010010300e0142c0d420a0780464500c00d91181066691110700031030780292071404034011030000307100c0c80c210030002d800a010b49600140385a10140380c5061442c043d0600f80c03201e1071240c041580c01c1c14071900d02143e11b1700030440ca0318150f2075501c1180041481407040c031144c02e410803c01495441032044c0c0400c0d0141e494469820b0ba040d00440c03040c0c0108160040350050b09001401000c100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 302490629 1250 302489379 302489419
    0xf051501121112041b08060f10030f030809070503060112050105090d0e090a020409090c03052407030b01230a1d060d020901120c0801080705040e0d0305040c030503030702010f0515 79
    0xa4802d10030074440008500f03a00c00b121700000d41e580820142e90001050143c4d81c1000b103c1107600600c8801204c86051468480c0c03401e003441c503178001c1e00b03000008011461901090005902134103002d030468103903583d1540000c00b03c003002078040e141540b0b08030104103486000300d00102802d40360303521049140d0101b000c0116508c0b0161042050b2075081000141e00c400502901100d90f01070783c80c1081551071424000c0c20300b5000c1c035000780900c1c10000c0564000300150547e98000c1c000c2d141c00100f0040b000016034401c2c0c4d02c416002000d1816110303208081d042e18000341a984d02036a100d10812002509a850040c0240d6045910410074803814105100c01c7e4090115040145040d00002d486400c0e030404031030300184a1400949218014409a4820410385005220603913007040030001c0b40c403002d0f4445010064001c105070b250004a000d00071800343c0c500146401c241620303903d003003028000e0700803c0b1405108510341c2c00c1c04001060880140039410030250003400003000e02c140e4402d0a2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 302491879 1250 302490629 302490631
    0x60f08010c03020c07151b060902040b0d120e0f1908070e010621060308030405161a091c120e040b0a0302010e090a0e0a050618070503070e0603010f051501121112 71
    0x8420000040305480340c17115034400320010380e23000b04000564008035006103c192503110a005024a440303e0307408001450380b42d0b402519000318900000e000c1d400c800021509550310925a620000000d405120102c4000103101120507003030132108100e689800540402030b09201c4c0c0004944240e03d2030f1540300e03111035040d8050500010000305152079540390000703500140d905881551090040701c0c00440450007100240c01030b4045a843c036089205c0b403140034460280c0050041181c1000c1d050140801b14001c0180750b4401c248401e150812000144004078076a10710740720b1814814401c00d20b00706a18070034203032601a590341034140750f002d05000315013201030000c1801b82d42d10300c03000030782c0407040c00b090381c10a02c141c01600c0c15040410303104060780289a5403183d9a04100e1042010b079400080d00d0307003103403221070301d94150360340c2d000000e40142850040030202606102c10010072009070b00030f0180b080c1098031b8040c42d40020100550860b50140b082c1030031404204010814001110b00f42 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 302493129 1250 302491879 302491919
    0x108100903050405060a0509010206010e060d1410020a05070b060109050a21020a15020c0f09061002030906030f2a1c0e01060b1e160201030f02090301060f08010c03020c07 75
    0xb502d410354440104200340e005450100001c1d0011449150940c0d041c02494010300005141210074280500010400c40200b04000c0142c6c0e0301c1c2040e1380409506000340011141c440e4400c54a40081c10000781180e40084030441c5c00b203405000140b099800707000c42e501524000b0f8035100c8050b04151401c403806e8405442c44031a0f0070317480303031441c0103a030703140868005010b42c450400da004c0d40113580a440c2004881d41c16201d0310803101d40c03100c540c4a00c012150700c48400c944101d100b92040d030003a421445a40071641e0409c100000b0000000d0310362910f14092400341c3d80400003144000c905100342188041c0039000c0c00000c002c4000901c0d080c180b021007031056501c00007007a0071036480369821628a46d20003154554041804001002c018401000190b00f051100c0c1c0740140203500030000300c40c0b01000a05042e0f840c1c0058886c0b60840e1305031000c2c0e4130094000c2110340d48803682030181c1080b0f031140030720942c01c155400c0506846402901e00300d555641c02040101d046c210b03080343c07a400025003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 302494379 1250 302493129 302493137
    0x315041112190c0f050d080a0e0a170703030f050304031706060408060901140c0a050a0813080706060302030d03150510111516031404030e0402160b06030d080108100903 74
    0x20500e00141c1080948190034801e000301c00d4035034074100c221500d540c0c09034045c40c4900300c40d00241c000f0900410403513a0007640d41c5815005960302d1070001d4102156900300e0154450071150340c1064070400103044040c0c1e4081d884985a0f0500134200f05c410f407204407030040004c0d40702251410700500c44040e05030002c1c401000203042a450311080d0b413501804490540d941da4591405c44480307000025155040451654100d1502c485a4800f07031403403040540580403c54440c002680300007480e80d6003900d06d5131085203540c0c0d4811506044001d006039010982c80b0303020f460640712820f0b001c2e1007418011444888003041d10303460301c420023184035007400364101800390035001d03e03407195420b01841c03006c004250741c202c0060802000340c4000528400d42c0324245450840400f0340b1900d5014041d070702a90515225452116000103e8040d015030414032000c0c0d401c030342000741001980070a1500c11402541240c1c0022203001040b500082d0a21640d046130f00620b0445400d01c03040d41000a61034040d00f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 302495629 1250 302494379 302494393
    0x9112d060417010914060402010c030e0d0f0602070507090506131107020306010f0612020a122c0d080a02130612090b010605032502100207030225050315041112 70
    0x120326902c407180c4099142d075540c8a03007000f0082140c0c07000c10900100c00040401e4a0176070b0018000546188028040c0405030800c0748142d5298245030803103990204c3c121150813403e20340400a9000b840d4111080c2c018290003081c52003407446020701c01e084c01031503081039550008510b001440d41c16108074084804022321005a00c2c01c018144c005c0040981c85000c1c503103802001440034004070115900b56004010b1100724592040580500084880001426070318410a00e01a452070811180b149503408080082501c0e0100ba000507584071a140c008a0761342d81ea0304c8108900c2202d4000303c003a201c0140a1210038404c100040c110004000002900603d6480310086028242d0160000980000c10004c582c91902d110f0124007003003a5014030483d01102c0b01075252800180b01e244103d5020624005140c0b0801c074580b80c240141c0c43c19043c100c1c101d1100000c40d03441c1d020700d40c02842201c00110b111522010740601c611f0b00300c11801c1c103140703810003000080c0070b41c03418000b030b00d210307200f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 302496879 1250 302495629 302495639
    0x12705010f05010f031e020603012303061810061226040e06010e0d0b01030803070c061805070806040b07030207081215030601080a0816230109112d0604 67
    0x80708042c00f03400c42113407180d00145949030805050b401d0003181510004541d840b0001600c584050300d06540649a50700e100301220f5072030711703840006040c01c0c0d503041c441d003814048035900d01c40c0d004c4038819151040d0740346010744410352030991300745108500f103c104000c0034501140101c000c03081c0500300300740003980440c8041c0c0440703c6500b00340c004564901506040c040c2940e000210090440b10079140d80d00c7e50303619900c40c400741d50414071003d4001c1c840040052170181c85207142c0c1407526445801005031419031340e040d0000d00aa014111614480c401c4d0220b1141000070701c0031302c596481556008290b40711034040b0060f403c0520210f506050502100b15143d82c100a400d01ca40e08502d400c041c00d002c0f52080500e00141a4001074480c1c2003a180007002c030311341c4000c035030201c102c88040844060107490410403490200e84004d1030504000601c0c50202c0040d00441030303250140745100d4180d10000c04105060754000009140d081c0c12650075900c1e005080b4000b02c0101d001403001e0309080d918 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 302498129 1250 302496879 302496881
    0x3080a0203191713020907080403030e01090606030c36020f0c010902281e150210050714040303030b04060b0a2d050306091807030c080609012705010f 66
    0x510003180415a03030040c41008250300e03045103900105041000184c1042038010408840c005028002000410320004090500a0b0840000082c00724020800060b05c5e0500c8801041240821582034600c1080040c0f6440c9252207004001c0304008030301c60807010001445404c0c146c0061080c0c405409002182d5902d0410018100d0001428004903940509104111240c0314615903070155050f01451161184141418401034800e0f10040c0840c0903803040810007030064550010181040f0b4030000204658046851102e28282c01c105000c661901401510010503000c0b60050600c2e00740010000b00303229402c00c0d2180100900002034103620b808489600b40c0c0440c0945001c40c029072580908508880c01c5210340b00c10811a051004201e490f0045c528800500100d201d6030307444c40490780440000d486510513000130012900c0c1c035940c0303103041c100c10341a510444410740110707400940001010b004d80b4008002d01800c000075044a001465090700011606903400d40d80e40c4085010103e071307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 302499379 1250 302498129 302498167
    0x801060f0509100602070501120b060f1c1a10031d03091c0206070f0c09060612050105370b0301090e0c030a0804050609060702030d030902030d0c080403080a0203 71
    0x55000c00030a05003001c06000c00400054411160004403840c100082580411510180d420074030380300c005a003200080d803000d40f60700c0412035400640002e8160242c01441c004041412204040b18091320407081054115072004881080d90004650881680c0c030b4060929007480e407071404c00141040400c001d440700d205d0345d804408996400041d0004482c5048480e40c0c910000b01c03c0e41c0c000038001e40d80410740720301415100500c07098601c120030081000790403800c1e0103894940360400a03107a0b115001812000001c5080410918000c008101030a0280524111410300d8461080000c0035a10314001c020300304040c8080407105c02d0000c1260a81d12000358020f2204060100c5c0d02030f030580145003410450308525209030301940d41d2000089030b1b641030360f0443d0800c0329032035251b140380c1e80800c1d19481400d00c025498000d82407543c20342501079004994040c002da040300e02c4002c030a10705903400e03008508080c01141c401d1000300b0010b18500d00421101c401c1d44150381c2002100072852000c450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 302500629 1250 302499379 302499389
    0x106030507051207170102040e0916050603090319050405040c0203040801052a0c0c040207080d11180409020406080a200303030105100f090e09030a020606030105060603130c080106 79
    0x1444010400600c4010008100a04800c9540452544000c1c190307554802903482207541d0300c1c2c104000010200020340c141c030300070005004091000d04e8449101a15150411803810b808000c403500850542000d006891003013104800842c5440e07642255982c896150300b041804104003008041500e0701d4034002c2c4500301c015a002503441d00e00f020005425206c000b0140031031003040c82c07010f800d043e03030308284100044511501c1a030b40c0c400c0300b0b20341800e051044070a02d420a000069180401c46020020800d1f4180c80707008204511f244d490460310340c4101c0003040446c0c5070301c0e441409071b4981607000030140d42c401400000c860f603484103401d01302180c00c02c043d43c0e010009003089032141c1c04059803003108001140a0752a640c14040019060805c251480041015a0300210031030743c0601d060b10090401c10240c00c0d641c1c5040c0ca162581e90341308082d004018000e00c00402c1e40c07401c2c14040d0034040c920050036182140e90307011300101b4511803c0402c0d07030414100080050300b2031084c46140081c00d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 302501879 1250 302500629 302500631
    0x1506030611071719110f01061715060f060c150c1c0b060a05070302190c060f02191106070f110414090709020c010618020a0f1106070e1f0201 62
    0x18a0303424a03d002c1980c50582400090040280c0c0700d00c0c024180f02404446100c0c14511880700c0d07000207851038907902e44110b201c02c0d032900c0780110341e400404520f108240040000c4803140c409055030f154541c201500c0058005501c0075041406141c80800341c50030701c3c6100101d9401c58040350306020100d4007520340c10824903001821a010b0804c0100c4c603e500045e0308030038401d40c0c1017080422400d2190f01c00540c100f0002240b0002014803e110040380040707040c41c008107480182c180824400003d01c00d02c00030442e82a0341200d03003800030802c0248000703200c3d6a0405000f458540c1c0904098040701d40fa440081000380c00700148900c008501428050071221015131180401d21003183c109502029140c001082001a03680c00010070a003501d08489015803255266510540500020307040510300d200c1c3e030f00c080f6000b00c1940d409040003510540d10540b0403111110241c49121040b240c003c01030b0401400904254010110307020130704000380c801c1a10840e80003d0605020115041000503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 302503129 1250 302501879 302501887
    0x1b1e030a0b0a05010510020d050a0309140d03061406030103060e070302090a0f06120f12030612031809021e0723010f0506040b1003050c0408031902010e0102090d1506030611 76
    0x1100b14402c10b80034040580d0344046c001c40740340c80a940c1c0e40310700d01250704000300014500911031183d0840c6d00d2869204900e81003520f8050201c580328901d2115090002e8944080001c0c4086a00390035103104102900052031642191207000103800f0300000508640300740c0e140003005840e5031413010722848a0b00d5000910484440e403140545415500466401c803148400c2d0000c544a06007600000740c1c05005e01c082150240740a4015101503800301c900481d04036154024942c010080320003a02c0c050000c1501d0300d03281c844c40b204034065600307505088008003a0031341802520800402855004e40f12005652000701c0000c01c1c0b41c4180013020071180d44900300013454005500400e5008542142c05001e00800392000c11109041041207104060b2504046104a074002c01220f01500c48201660754a00c0c4d007900450303040101c0c5082000540ca400010316041c0c0d0188207550800000401004002c5800d4940307503182d80e451107920380c00301e40e1140300000140e80d034494402d0661407658200c1c1c803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 302504379 1250 302503129 302503141
    0x6061a0309010b030309010503010b0d110d02091305092a030709020d0f061802090109080f060709290307030e070915061103030c072d02121b1e030a0b 66
    0x3c0d1660301c20814002d0384107102c2d118060f0b8000054905442c040c0031443d03204c01c0c3d041032003005040c80024600680e00300041d5243c40c100590028000c540003610081c80246e240f6805c182201d0040380d4900841d0080e50f07a802c09000b1096a4805045070380c10204019251200020b003080010f52021425076400502001a401c49018100b8020750080c802c000203460b200c51042c80903c1d02c103145184650019004083d41c2c040d203030000141c80c00c50110340e0b201c1c40755500c056642405840d2000070611004001451804404050341d104011900c4018801c035603901c8951590009400b480030700d41c45d01c0440c400c083c810010b43d001044c03200300100d00c0000041400300c608045400080c204240b45685200c004000000c4a802a0018140596070344003810a40c45c030014041c40c190198004910444104201c0080d4200c050300032030340501e40c6961203000c2c135035825018407000300401c078140d0044600c1c07402003402e9658498004e00c00100852801c002801c0024804007154152400d00500c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 302505629 1250 302504379 302504381
    0x20d05070f15021606180b16020a0e090307060b180f01090c1d0f0303070c09050910050f07030504021201060e16050c12070f06050a0f0b04200706061a030901 69
    0x10b08918140003070400030300c0c10280d00385139a400e8010300040c4040c0510140d00b061901c0402d5004101030151170761608460007000081c01200c150070380c46000020b001066a51801c2c10351402043c000c8000d5142581079a034000180590382c1c407042d440380c80c0a5100c20a90f200303600d1300e0f104264070450300d602c9605000d1a0320031540c04d18055803c1202500301c0344012075030b01001d880703c00c1003150b00320309034494030000a1840c0300b0040003c0031200949000140e0884a8000c076018483c01c009a9070140c2d0343c08800d0341240d07411500c007806802ca203000309544c0f60080c0c1c01141c205001400300e01c0b02500c2d40541d182511110350000d1002440c040400440034880300c03580f01c01504619060b07107040650801ca50395085e0440d04c451040c07000089210400c01d901004204050348200140000d2030b000303101c68002c000c0184008a040c0c2071141c080394501e414800e4160402c05010000d405500084000358681c12584040741c204d540c8590224000c81046130100380f0160241d001640d07854983c40c094 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 302506879 1250 302505629 302505659
    0x315041b0b1b011104090911030d20010c0806040207020127030b010b0a050304030f0c0c060302030a050609191a04090b0403020d03020309150601020a0b0703020406170c04060804020d05070f 83
    0x20ba242e9141c1004042202c2d001400c4800303d41c28081c012a5981c0e45044c09040030314086000d5a05110b200110126140c0258400581403988600c8060612400c0065800d88420046040002d075014000415614041c0d0107000b0940c010303d403001b006420410700c030700b2040503007440c004100d030028010010010320704003c0340504101480341d410161000006000c07030101402c002c003486081c024500005201e0a4025041c90704401c8140095968860180095000340c42c503104c068140703000603040742080d055071801800c1080780003030880b480e005404010304118070b914030f014036030100103034183e03035180203103043d0702d0140b0000410390829103006490039401c18481380c2410b005004204e01c480c80426059130b10006255420f486581c4d101c0100d0510400d11340052001e140c1c132051052007540760303024009549591b184c0c00c0c0381424a44105903c1c960440759116241000c020031b110309842018042e4010340301400b002c20802803991224200b00450b08404502c040d204020001200042d486d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 302508129 1250 302506879 302506927
    0xc090e0a0503030f1e010306020301140301020a090501050a02011409030903151302011409030609060105090604060b18061e090411160212120d0504020406050f0315041b0b 75
    0x28a426419603403070a44900000780800600303641030b0000703000026919034600c4103071a40c041060742907840349400300c000d403c280100090483e4800d0800900e00b414822588114655111300034031925003401168968080310703034542155280d00c001c800401c2d02c4c158440c001c030400c40185855030014410326180400e1070300c00c40c500e9940103050282c0c0300701c245002e1500036028a0481c4035001000e103440c103244210380046030035204501c2007201c0c800300800c0081c1a0381c012110030768581c403601c003080151141c41c014004882402c015190000c101e40402040d08400030300b040707040407848440c42001c160302001c40c40c2004400683c0c00308910340f5114507490b5034540d10400e420310200040402103d1a1480020b014100d0121041c42c1801c08000da50140700d2180360103a69082d040342c44801811041d107080303014030300b0003030041a04e1500f03e600c0c1c1c2d210180a00100720381d42d1001d448030a0f00001a00a0b11001c1d00c03440003000d11800041201c1c00740000f81c40c12a620307a40d00013480b13508041c0182c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 302509379 1250 302508129 302508133
    0x801020d0e0d030c1704030c080a0e0109050303091e0d0210171012080307020f010203151207290d09080304021c0308060402090406050d030c0b07020d050405100c020301090c090e 78
    0x100d4100c454101c060321145c002100c1180426640d9442e098030782003980e41c0050035040f404512001d00070303440046032503064000c1e664144202da4a070305140d41c90158100d21030f0b02c4140040050300f19413000b900c407110300c10020007080c0b2078480c54000c80c3c0101d55120480d4000f5034a8000c0c0d00c010192410820380101808030174001062904c8040007420301c090718020590303400000400c90281c400c01c808400112007000843d940e04260b40114200310552655a0080c5040c2034400d40303401000c40c50b40212a00310410504e02e10100741d610101e018000d0f0520b0f01502e0a011010b200b034081c0c4102042907105210090740ca0030540104003030303c00d800c500c021b000212104041c2c00603612140144c0c2141003540c0158071172824a0020f4042c04054010361f8221000c010100140341d8000c0701400c0e002d020301600032440d22a900c049840f20703142c111132008558100300030846400d10780602c032012031143c54102d5000325107600080c252981d070313141941c84100310b54081c00080b015101e03a1450000c5400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 302510629 1250 302509379 302509391
    0x901060503182b20030307020c040e07060c03020307121805040b13050601030b0904320a0f021f0305100f0609030b0a140405032d0d150801020d0e0d03 66
    0x4641120a483c2c54080002c080c0030400005045000c0e91100203020100c6010b5429000c03203685140d03503a081101c01d0340043c45420141c80c1503051038802e250500c013802c1e007d0318156040000907541c0f00381e0355004404500c0208010340101e18042c40c0840e01080e160354101c1002120750300500c00c500541c0010384210b160030128040c40d80c848410024100810102186aa0720351005900414803100316a030068012010041081a286114081e079064104038070514021801071340000044032010282550110125001045601303e2000303015100030001003400118a80096a520b026440000031a072550107016039074607030110120181845c80000080c40b440d0120081000840380f1000e00080c84001c0415500520340c0c0000d85c400702409680781581c1028a01a9070300d50050b1042a41003554140c40c3c40c2055043d00342e82040c01411030b500742001440c02c3c0110081011400d0028641150200020f280b4400e0018104460f00c003000065503540c0720380a64201101540c40c6400c15160030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 302511879 1250 302510629 302510653
    0x40501060f02100b12101e06050907081906030b1b130e0603120a05041e030f140c030d0905041b080103081305030304141206010b0306060d0b090106050318 68
    0xa00e50b616603041c060210f9000003a0005c618510700d03880c268103842c02907040c42e00805c1d03aa60805024050141320111800c4680308000e01254030901440d94046068808a06194401d85040e5000145020345440c101c04a80b9007030110b5000d5401152030440700c0003003040b80d514842c549415000e252501500e04541084211040407041c013030899001e0b0319001141080e00c0400c140203c0d5910490491f56034201f5110140c600c0c3c10902c16204200c0300d103280c14000c2c14441100c60201c9500264849581c0c4859030303400c06001748625204a544a08000e8003403039582081034043e040701c982c4403e0007443c1480705000036103100d01029601194001091800103070700422290440383c10880b040d1b11520880c86800700d00b006640059494800403801003083d0308962480b410000c02122201c0342c0003580440251503440074881e29000010900009601341402d174001c2001c080900c80005480304500c000516540d02a04034800145020007002919000d100740e26500c051107030001c00030b4021003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 302513129 1250 302511879 302511883
    0x1006030c020c031c050405030106170706030b0d030509040e0709061505030405070b0310030606060503150d020d02010e040f140403020d0804120f110f15011505030f090703051b040501060f02 83
    0x40c1001000c030804070030b09103017031091060310043d0100030001d210b01070340c665124003c40c01c400440b116900403000c000030020b000b1b21501010500241181c4d5142950707880c1660f95801950720142c000f515404000d920780400e03c180005400210400200346040040f8402000c0051007203905008080081c8004103030001011001c483d0300401c0d0640c0c1c1d603100c0305804081d41c03031940001e0149042c17800110700c064121025510941c0c0000c050f6101c0c0411000b00700144114038000794200805003403140155125199602410002501c081075007071a03400c040e001c9519064a030075140501c2014482059410f000040d1200d1052800c02c1180c00d03e03131100241c5100c1c0003904418080300030a84e01d1618007590221910501200594404041c010b1800c1d4444080343c151503140c818000000c030300c480f801101900c0140b100d039103240c00d40da51250080d03840000640038990718851040d00000061003041101c03413142492145194a015001c280415581d042c0c10001c20301444c12042da01c4c00f980 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 302514379 1250 302513129 302513143
    0xc050604080304051f05160807320a030504020411190c03020c090c0304050610080c060c0102090301050c07120f0f0f031113031703090a030c0c0e1006030c020c03 71
    0x44100c01e9541c0d00e5604d8190300e1302e18402e10070502c682080302d9640c819507042d8495417052100c142c1410440c41c0c0484100d8805a085490714046042c08620070806044d5154010000c0b10600e01c01143d07040c00c01600d000c0d50801031000340007030388900070002141000d001d404404d1060901c080d080040c40c1e074685000303408c034035481c03010484034040010038140301f0050005140c81c0034004a00c0c41c00c2082066642d9442241c050325184540000b00c0d420700003004584044620000241c40160008420045c841e40b000301c40300707450364013807006240b00d41d803e21070300e4041d40d0b503d0007081d50b03401640303042080c0c0340d40d03100b000041c403050218181c015a0004600e141000191409518851a03040d09070f0003810250403114140301c002c24169200e4901d08101c07400d5a00460702c0d81c1d07080151710b49515551104880074507841d080000b070714000034017482d0100b4019100b2070754034485c01c0c0c454a00010421084981c0a03a080f03802c4800c03c08a40c25100e103d800030018809405030041d40070210756039001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 302515629 1250 302514379 302514383
    0x30109020a120f0215070516060f0e06040312030c110c01051204080d050a050a0b03070518070908060901021201060206130b130204180c120b04081305060d05070801060c050604 77
    0x441c15404208180c0c00610f00c44aa401010b05d185003e200d14291610703040714604a94a00c20b038600010300009031400803080b1401079440c0c500300040d2000490f01042250101d94115030140b001000044403500e540d42e851001d644c001403099840c40b8001c0840041c8401e04c070700b40c0c10803901c1a0050340d2180403900d080b070303010420360003a8449181550326071055021a03d0914589020301440076602d4200c9030041e140300340140030314802c00c42010348034176442c0714082d40030b900901744211450b03442c1d0300030b40d200c42a4140711045d641d03900305103828039038201c1e103600c0c2503540006d031003a80804010101e401743c04284004c0c06030745820001c0751000805108041e150041420005070b040a0400d10a420150301070002c0c0a00b240440401c1311441600e141110341e28002000490390381010552502c040f50403045042c00c58980e9160380c4c0c9141c4c0000d64508100d070b542c20012500c1d440d030031700030144c81100660004162401210040c004481031304601c04100c02c075890079020480003d00560000d0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 302516879 1250 302515629 302515649
    0x7181508060105040302040203040c03291b040e010f08010f05060d060e0319030603063909030b040807030f0e01050703181a07050f16140102100f0f0b030109020a 71
    0x51038840050f19140505d600095000b80000308110802c03c528050344226842024500f80340c41d000084480c0e4102445110910101d0410006200309165013404000c11907102c5c0d00c2d40b50a480e00c0d00d41014103000d030007048032a09402c804202c514000d2150101460000b40c2c108031900b405000030f45d06034007214014180c40d4641000d80c00c1c88509004841d42a0903183c5100c83d031082060029003e400c0910007580e13030514044543e500504e840c82c003500c04130341e0a84441300300c0103110a1622000011a094002c10a0410011000481c0c9418040c0950700880c0c6c0c064070f90b00300f031070001c10b1291240703c080100300366070b840d030740f116600b1005486c076503581424070011204440305002e03003041140d88840f18502c00030710310311110742c4458010821a40644142d805011140102c41d40c0d1341c0e2600d00d12401d642c005c01d02040403000b1801740050040c0e0504c10380c1c11140004581e0b005641e05109a00b6038550f858079444404105441909207104082c0d00030f0012070119000500394842ea031007101c9500e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 302517985 1106 302516879 302516881
    0x10f06060e0118030308010302010c06090215030f13020604050d03030e01020f0a14120f04230d020706091d0606071a0a1103060d080c010b031507181508 67
    0x184e50151640340380c6900e164011500c00a11540075600156034421860050384c60103c84510382d411558115140d043c417518103401c0207406880b465020741313a100c4400068079001d050310100c40007110441a004810b0400b070700504082d40117540d0951000540090503140d8101900e07000ca11980e03181581200d4241a510030700c00c451524080c01e14131000500403040f104803040d806442161000b8a5004080d03823000c400c946103d900f0040d070814800d05009690401c42c0318028041d0f440c1c006035a03440c0c01c0c9000380174030580310704221640101300040c140c0e031070752030071660b009500a018102c00320480c404800440c1085d240c6182d15230401c90200c403204021401c0e24001d020081c0121001e811540c0c4003a05603001d01507210080d502c841398006256424000c1d0b10f0b843c038032080360b4400340c507090200501c81042c1c86980380503201e940c282400401d0704041d00084a140d10b05080b061 = true := by decide +kernel

theorem cover : BRFrame.Cov 302338129 302517985 := by
  have h0 := BRFrame.cov_init 302338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 302338129 ≤ n) (h2 : n < 302517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
