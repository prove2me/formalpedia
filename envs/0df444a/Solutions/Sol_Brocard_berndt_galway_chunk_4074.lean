-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:45.644653+00:00
-- url     : https://prove2.me/submissions/c46a2354-09dd-47b6-8b91-a7ec6fc8d9e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 732553956 ≤ n < 732733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 732555206 1250 732553956 732553961
    0x24040b1005180a05010225030f060c0e0103021c02090303070b182b030b011701080c1c020121090b0c03011706060a09090f0c09062909010c05190303 65
    0x828260024402e036900351a1428085440303c1183c006800a05906208940c620f6440f045035109013064002c2100c000b001c2a00110342100103401343c440044c410400d10001000d6103040f90304281031600402004601b1403800e600700c108417000140040c2c4508038080041e0441c8a100400381600301c2800c1408001040c542c800003611103050100c138034589101800070855841d540030740f600401050190070509000340c1122000c8101490b06c244030160300018042468400c0c0c01c11800d6602102105295003491032020b000d03050805560054040c00364002000002d5480b02440c019440614014040c0510b401409115a200c11800d484d8030700199080c010750405d228002c08803d403030128118943c408990140030b0345026107500c0d8401e0502c0e00e20805480c136818125814000e442e503107000315801358101c001501921001003205460111000041d040788800e500d590b0b048040fa0710042840401101c441c220207003400c0042d00b4040c1840b90822020002c0e800c003010182151204050345617 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 732556456 1250 732555206 732555217
    0x30e010f0e130e06010915090c0e0a0608270606041d1f111e0a050409150603060b03070206061c0206031e0115020a06091e0c03050c060324040b1005 65
    0x90885136183e03070f00c0c10394500344c910740e4014582c00440c80f5010303c4002016001802c50007a182006000c00440c4400f140c0c103400c2c00c0d4400000030362110180030f6000d1078402c440300602c14143c0651944202a0340d01d9481350005040e9611079546c41004500b2001444004003003003020800303139980303001160030960b5004c4903010310404482c07402c42d503072118ac0c42c1da07425500550546224001d04181e402c0c1c1c030503113030340c050044582404400e22000807501d002d40101810401c844040000251900704c0190a582c0544c0016103485801d2080191040c2d000440d941c0c000c03422103c6400c55006680c0c81c007849054501c0c080d400801c00810404e003a41841d680c200e06110304504120a0780c1e07074001102d0040b00506c00200143c00c858145808140141c1040d890540030300729060a00d489040403402070403600204442c030410079101001444020f00c05529450019180da034658a41050f040c0c20719602c00380309188201e03400d0950812503c81d0b40c0541d000301000750200441d0044560b01408a4201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 732557706 1250 732556456 732556481
    0x3050102030114010804051e0c0307080c10090810050c070f0807020f0f01120f15030c080d0314040f06110f0d1506020a0201050a18060f02010c020604030e010f0e13 72
    0x8040f801c0a030307500c22603480d4440d40d0044090206140d600d684441641003410b105550392240c3e2091510383c0d94140038020040442d4002420541542c034180b00729004a40c9140080c0619004200309640000c24140038010305403c00062507920a050907600703007e1f4500c040c0c041c03401062030904001c4003500a000f018000c44020810105010030043c49400a03462240051040c484042505030542c001209002003194080b600310b52050a140d40340809610669015015034802c010009003031050070700c1c420051405103d1000035a414405208001d0300c010548124088801c0510481c1d80c401c05c0001800c0d004180e981e10600e00125064220444c10044103207003040055020110810200407582d46401604500d01030390015a40d580080100c40140500e920380c001c1310102c2c842d00400501456103400000a410080c02400c44003030742070354020742d803001041c00b020a8100c40042903a43c800d02c1d0550707040c041950201e802104002e0701c1b0750400b0b110f8441d5142c0c641c0a8100c2c0d280070f0003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 732558956 1250 732557706 732557729
    0x1501080105060406051005090a12030e090a02130303050c011d0601050f0f0f041e0504080d0e16090234050d052805091e0301060b040303120218030304030501020301 72
    0x1030700410002113032050b11425621201d0348150001840c001e038003601c9804002044006103d50341c1d4518411071400000850029080c0ea0503145186401e264403604a926071804504003040c1040341038010303405010190500c80080f941c00c08545094005e640c203000d1115080d01f01c00b400c0b25809035948000e009040c4a41c1c1c00c171011640c0790030000340098030103400504100542da10541404010100c85d81548011003290701c2a03884011300e401103500036440380c4405980c030f000000420f0100c48003282d0760581074005400c03a50600c1002c10919040c3c03503140e000181d0360400041405d60000000307070760403041700c0000004440400c101c4540b000c814000d030241c0c1c0d0304d640c2c051400c0780c0b940708620300003490040355032030307442282e82e800c0c02d5441503400c9041c46454013910700006510340e80d916505140b02005595a0202400d0038003581000300740b0080c10300d08240c11a40c4c080d103c4454001c4a103210360340490305116100c203030320484165182c0034003030f00e03030b00c40e22070801c0e6001c0e5000b401410740110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 732560206 1250 732558956 732558961
    0x1d01140105030d020d02030f0304111f141206090a0b03120304021f08071b06110702030714011202091c0f0c0e01051c020103201b01180f0309081501080105 68
    0x38004245804010007540c00396250230400b40391044550409401074403078a5184604481d5078135a09016180c41d00c800c0b03448185e600040d08000e040201c0c0c180c91a1850f0b81c10303c006a401c0340320b4090b0a401c0703002150718007490b40e6154100d00040c0100e40ba03403545442502c1e074108148101400440c0100d0081d6400049107081085206607c29a1040030b030002c0c4440d40090006442406c0701c28441589010800348541907849010668140d807040500c0020000341e1441186020050038008217030242c0000039429110740040c001092803803507039000580014228440d50b07039081e4108442000c03c40c4a1044044604041d417159203034101c03c955864440c000480e81d54440003805049500c020130365209802c80c8920540000c80c0c44e00c04905040c0c0342c41050b41c42d0b100c00340700140c40350b019050380e03500e0b80c17110100c8503001d1503200c0d070034032450b4908086250603035032040005011503000103140d50508918a41102c0c0403c1c41d0f48203034500d0140340c0c080d03004440c070000910b04a6812030002e200c941c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 732561456 1250 732560206 732560233
    0x130207020f0a03030804121404091d070e07140403050f03090102190b0112050c040507050c010b15031506070f03020610082a0301021e04050a061e031d0114010503 71
    0x20070031408040c2c0815110000580000c0c0300c20b65034103c5200519005c051008001903208d000c1d0403c3d042130380c150ba110501da0300c0e0000080c0005039220b03200c000500c200c030f182150032200640e0240c4014104204440d0302610449400d00721401903610400b2198000340390305c0440d849812064180b8014001e1501544482d03500c0a980740f039503074012540c01000d03440d04101c04420b08a94208890070300890b8180705090b41c07140b181a11862032904da003a83d6210900c1c0d0503086038284000d03184103031240282c0e01c00a80040342920740c01030304215441030b0745000d20001810303801500c000800c4260f160905801b003590100d015030007400c52080fa001410785960100c2d480d04103118142032012028220105491034000c038021040c00003600051a01c2c1440340060b1960001c4e08140c24000e42c0001c00b04058200944220002c01c2585400d0060300c244488018591150055000426031902c107090414031224070154040650440204000d410380607410821030000d1052510034090a107000c00803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 732562706 1250 732561456 732561469
    0x9010501060905030706020715030b0d11090c13050d021909020d0515030a03030c181d07030e03040603020f09040f050403270522020c150709030f0818130207020f 71
    0x1610487e8014002c07450410700010700000d0300a00100806858501d20303040350300c1d452040141c0034000c0c1d0208540454040c103201311021b01a214500300b24007040b110410050003500d9109840d402c4030b502440d42901d00001e03442c00b910380700050342c1c0f00c0013210000e2180e01c1131780103010904031380300d0030f02c035583d40c0c45000398183c80d10040d00340d015040120100b0020303200b03500074540040d50f42407801200d401c07030540100c10081074125080c11075150401e200301417005190180c2c0100d00e4a401d220845c00c80e0b41090702ca0080d4401e25042c19000310b5a1480c2207287c80955144003005801040100020070301c0f200031746420390f400c2d0301107040c2c080c3d54441180b9070305a0350401d03003003007119860306ca103040b00307014020307110b100d003400c1ca00d15100103500c0d0311480e80014031072500040e00919a141ca003842101c80003202508443c2806101c0c00100001780d8403032400400c41d900102c507580c50300464000441120b00e01d02001741c0c0240c02c80e0008041c44240d40c054070316140280e80d6070344860281002e0020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 732563956 1250 732562706 732562709
    0x4170703050f0306151c0608011a12070e070e1801240504030f0c080d02070e010e0c0712110d080415050c0c0105253212090105010609050307 62
    0x550104202c0b00300314500001075401c441d003d80b182c5041000000104403a8100c2e140a5610355002c102d0603030300192a000d442e015004400003004aa0b059569211103010403121031809402182e500e240d60800500110f80280503c0c4a022003034030f0108801450305900c1002d66100d1208042116a900600406d1606a0740024510800881001c45d03503002416400f00c0d0030f080082c10000800060a00c004078490f03103100700c850350784940c102a00507050403900707111b180444d4018541003042c0418010158110f642e0092540e1235520303000240141d80c840c2038800b0388504402c00008010315030040703180350005c0060b1705844074544a25412039400c94142c074040c0010510040c5142d0070011580180d412144030100d440c03806005030205820740310f080b141e0303035070405a848450407000605040d1051803203140c54000901c20328014040d0064061400740840059080c41a14885604e0001c552065001040c040700304d14040800758040c14090041200040c0701440006990500165160 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 732565206 1250 732563956 732563963
    0xc060403090306050c09150c0109080d060e130b0c09010903140d0305090106030807021c0f0c03050d08040302032205220b040e0a110a0918020f09060307050f0307030b0f041707 77
    0x400300c1145019587c1103800c1803c510705d4655940c00003000103039610300148a410500d00010410034540200d54902800081100303400c030b01003580c0800043c03018440c166218249410543d210000040120360100d925000202010a03441044240d5030000400351030f42001503030144074035607420030418203079030661200500f10442402240010314100821280300200c1c0c5c1ca00d1110520940c0706c02c04603200715801650400ca050b201801880001e1145180c60300c0e5500740f41c51a8145503034000c0d40c1e8414405502c0c40704400d00ba0141081c00f0007500f040017060000c1c1700c0d05542400c401e040640b01411004ad02085241020700c48043c10240284245101082c015000001007501c40c84070000105507035540c0103d0542010841105500c03c59155a50701d28000301641c1c8030784184010003003001d48c0a88600b08940c20000542c1e400181c8400b80d0340c0560320a070043d5050170119181c40c0b001e07000103003c0300c0f84000700300790441c6181c2c0c960b00c1140120400c0d880c04883d00400d402c80d200300d140c0a03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 732566456 1250 732565206 732565219
    0x606040501093c020a0c061406010519020a0b0c09120a020a1a0c0a030e030c09190209061215101d040207080d2906090d11060c060403090306050c09 65
    0x311015140f0400c115040390748114030201601020a440481c0c2c440c0528601149100c01082c1c00d000d11441002d031110340313020300105c5e01d0500a00281c103901943c0d0b20b8071820a00040c513081c444e442480815001d951005154042e4100011a00c40076000f4084003402400e0300701c10084c151100099035004030b42c000e0410310300d0504100300c012080c004c1e840d403100ca0603010080c82800d54410032076042c071a402565200c5d1205442c2c020182090f01200307115108940000903c003990103142c484002c1e107100d500c0b0069076945802c0202d000c0303005d03421544200724100410014804450b40c41050541c4048401050b200f1440f034055400c8901181404160892b2003800e40407424140c6c0200840c1b40900003450401034400c40000942e8218006032040d420f02d4000343c90040400c0621800f4180102d609500342a04403001c620030181d09100541a007540200140681d210381e802c90740008203c100395401841c050902a0491400e0700c000c8404602c0c02000820650701c5030700340c03514140001c104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 732567706 1250 732566456 732566501
    0x60f09050625210b0315070503042f010509010315030c0801141014010c050a03020d020106050a0515070f0203060a0e0d050703230d0e07050a120b07180b040305060604050109 76
    0x403c3e0003010b41c400c144e5014071880041403000b5444812252103001d0b16038400b40d4a01d068074000340c0c90000b40506d01c0c0c81c408000440c0b5031400015004034803484080ca001510780c0c0e80c01d030040300580207850000c06a050503800110030712007103120030340a03070b030490009021100b111211400c400800303c54820328411200014040c01030040800910100145070081500c40680c840302d0a00d40c0081049026900002c0003400c02ea8082c05900020300c021500038045510b03000100d20b100652204107501a0b01c0040d00d10100900e07d0100d000880d000307001c9400c1071800c004500020850b031421290503100c0c481c05100031030712075411038480c1076045d540e00c403002200074440c5114840c0005000804071040c8840071902c0c0142c0f0a0030700012407030000701010751501d014040304003d29042900840d104410702808a00c11a54080d0400c411303141142e0201d0030103803000d802c3c0b42d00e608500d0b8210400100082404000112103003c1d05040300c042200c0d998800249048509036510403a940044040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 732568956 1250 732567706 732567767
    0xd140c0d050702070504050a0203070e030c010c03051c0c110606040501030c060f35090a0812130b01060e0f03071518030b0f071119060f09050625 64
    0x41e070b000809801207550300c03600e0740300003001d0342c0b012191890070340c2d0f011080200d01c40e4009008050300c58140d001d07059080540e80000c081012250015051003c009034141d917191810300103c0b11000992001c20070821100e800a101098800d51000584244c40225405280c5403040c20b040700d610040b04605a882c1910075905148422a1501440705028401c0e4a142005110801ca40e5480a0700b000040c0e0b040380400034800e000e02031150f541d000300e14610005010108072a4001d841002c0310030103640d1402e16190040c043c100041004480c02c000040d0107030040c02100800c0000c030b030648200000302e0103041e50385080e4800d44482d80000404442c1c494000d888142c4207803032002c241a042070b22621582c00150f000e0b2031185000c1481420448031550200200c5005090381004d01600d100485500030030500c0f030140a00101e03940c641c00003242609a1100d490958805c040c0c82003071030b00e003050304803c10389182151046001e62940e03100307203031040041031546101c400002e52414070700748 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 732570206 1250 732568956 732568961
    0xa0b0a021606180b012403110a11071d1008150402090606090301020c0606090c1204150e0d0f0207060203131202040b0307030f110906010c060e01200d140c0d 69
    0xc00c0f048100c0440301240814a40100c1501820f20028090309201c005a14100440c1a03040d800040510f000c03035000d060084c0400700c0700c0c0c0700c44030f103031002080d40d41d6030b0018180050b940c00301c2048219070b4401d207504120101110310803001d50904000090703803028055100d050358019581107010550004005251850420340c0044e03004d80443d0511981c03801190882c3d00004076440d950303010004100303d52600f0140036a01c5030511000340e0401100703668144645402410041120440c05180520010160b000c0114100300c0c00489040c1c8020010203004020714020300f03001800790480208986000004544004649080c00c2072a1031900e0185902d880030240201d80c084d850320071f065420341c0c0c01c0040c7e4014500a0800740e0b440c1090340f8094001c1611000d9641c0650352090410109a07000308007010b0f40b070740240000c1420881c403030f0002d004249201d90000d10761041081240d002000c100a0328030303550b882c181000040d280a0940641d00e00494146980340d41c01c001d8221440c01e02d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 732571456 1250 732570206 732570221
    0x63003030e1204030c030b0a06180209040902060d150501031a04020702030304050303040f0905221b0306180b010e090309060f0c01020a121a010206060402070c050a0303020a0b0a021606 81
    0x20415a107034115504005a0b03203512540c000e440411a05009105011030824000e40102c0520003c00200c2d01d820f040d048078500c408500e060b04e69010a10750115183c075041001c5640d4020b002c3c558803a071042801d40103081400c07000b01c50b100c0c0882c010500d5400303403098688a2101084841c07038006003400300000b941c0040001ca0f0180000e000c0000d01c0c1c0c8003000644080c1c14842c030090b0032a400c0c8110b10301161f800800040352015903020500040c074030180c0c07642e0303040c0c0c1180c0c0c03195040303480ea00b41c0b0116803000c0c0e1000b031a00c0d1a040c0606180c02110340380f40720152061101c14840d913a0f94206171840017007a607004847d80c06c108180c03285031074640c0083c06c111050050715400c1003500c0526508a07080302d0004c01c041428080c1c407003000444c40c4288850584003c1c205401282c0040000795100001040316024950026143c0d083c0031006050760003d2030001c0c0703591500c2d6100d180003501c0703001c2944211030200c0d2120100340c64400700d000303481d100c03800e10303550a000c4010b548502014065030f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 732572706 1250 732571456 732571481
    0x21b010905040207120221090904230102181f0509222a0819060b0424020d0509041a09070306080c06090901030f0507120606300303 58
    0x110000a81c50b1034900141c11590f003c0d44800740071014489003c0e00b8840d07400f00c105080c14803010f0f4261164050025a100c0c0c031402c1d600348100d80c0c1c544c584400e05ea45d0405480f00d400c1055030820074003020540090105500c00b01504002d10482d10601044c0c00d0344c00800d00610600da521242d10320b20900181400c00d20003040c06141004002010000481d080000703c05140c687e82000603441e52215000711205080128581c1004407803401003105401611992481300d4040507000400b005130007070000b6040d0040f000c0d0f030f0340340e844218130798080c94002407440c8900705044407400b00d800810803080d58001600c9003803038400104100300040050599025603022240400d4a20707494000002c1d200d440107450000700c10b8207051066107010b5100042610404007044090b510b91a00f42c2503504490744641d10310320141d40e5140032420040980c010122410301c4208103014040c00340c00241c1258120013807420a09003102c4180e44800d103520004400384480703048240082e110743d0066030248403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 732573956 1250 732572706 732572717
    0x509060d061b0e100c120e0a0503010e011a06040308030106050706020712180f06020a140102090d08031602070b03040807030201110a0c06060b25050124030b0a0b01021b01 75
    0x1c030500310310420400d0340000000a00032600c00201e90401610206010b031071403d2017000000c541c2d170746100d40180a180c4408000d1400c2000509484260105028010040003407104100d00c1082d01d008010200140c0039a94a2010a9955060107000c94064035004074000d4650303800c041056640b03030b002040032500150308000900125000800703100c0f80c811a0396034020144a42c0003080d0b103420050f04043d1203222040c404020701d60300044d080580c190300a616203c03100200c2c00c1c4500a010f8040e01c980c0001c90141c01d0000c00c40408029881540700014444001480300c1040f80d80718614065080300010800c00f1502098403a0050f00585200c2e10001c030707000d245d0003018580c5410800e0325401045100718035604001c0d113401a030001c0c00c43c100f1400d0034020000d08080861701c2000003c4580d500c4115007105000302034005464104000c54800341c032802c000c8000d11868035503c010b80d03a4520f01c002082d0324480c54011001d07100c2050340200108010a04180c40c1452405135184c140302 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 732575206 1250 732573956 732573971
    0x8250e0103020913020402040e072601060e0301020424021501030203030d0216170c0c0f06030a0e0f030c070e010e040c0e06120a05030d0507080f010e13021c0203010609060509060d06 80
    0xa1b03440c0018400b404103504180140d040c403400160807208081c2c5454042a451115040150f2070790035100d0440704640352411001030f0348030100c0d009110b10b800c2a601d180342400010068030341444c2007020560b19a0854921001010602003280403e01001b1b516400c104240b08a002198028203580c0c002c00707004a401d84400e9540407141c0d04034843c0a05140004901442844801c0c0b01060228000740e0b46c1500c002185400542e0341c2c40b0081010351065030f2440290301c88402000307403040c45500324003203170f0b40d8400c0321204580e00c10040c42202510b803c80d00002c25240f00c030960b018003440d07020a40e20202c3c0e0a254841e0305e0403000500103a0071485100d81d034080c140c0c08105080303e1500440103180d40e1460ba03800d46090307030801010f0b081445054010700c41c1d224031003110f860444a0043e484803964581c03150006c0707c00642240a0751200e10107103401e4003d55655050b81c4140c3c400c40007001030329504d07118101640c065101d0147e200c2040f00000d5411f0a00e140550522403007082c0000d50300c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 732576456 1250 732575206 732575209
    0x80f1906270213200d14130209100501020c040c0e210c0f0d03080702120c030c010b03070b0906030a09020d08070312021204021c060608250e010302091302 68
    0x48401d4020701d150011a2401241981022261500300c1c40d198441441082c40d1000b03810100010510032400c50140050030035001d400036800a00340c1c00141c201100c1c0c900340114032070300700c59141c00e09a100d0180400422071400328462007900300c88040c1c0103132000070396607820000103060400010003403080503c003001c0e045c4e680740c01d82242e21801082c0000391204102d110b41ca0080c4030781b403060003005d500034a40e071103943e101c49104005600d4641003003250744031001203007042401c1d07015078680000411041869800031026103802003403c0000c0101003030601c109036480125202d0362030501010000c02c8445e0a014000350b90150b100240459903001365404122100c1e00c6041c02d48800201150b0f030400c1682c80410040c1c1521521003c0d03082082e0205c1480d001c00b0040c02c024070078500f040d000852002d002c41d814010b5500004100311256a400619403100706c1c078040ea158001c00b42403030042420030030707400c0030903100030119040d00c80e0300707503400e100810002401d01a40d1410701014540103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 732577706 1250 732576456 732576491
    0x60f0f23090d08030a06080708070e010e0c09030a08090f010c1214091203040612060303140703111005150603010b2b1e05010501030509060a0519050a06030507080f1906 74
    0x580c8178400e0000d90585020b010b0350070040351f60041102500049002c2010790305003014503064800703245181400e611426003250b0700348607900d03409030103000c0c0c0680760341480300440182800132400d90312280f2082c1c2ca176004490012102800038400d81d000e04942104900c59100301c030030807000c102481c0c54105002c001a0707001541c4030b0320414543c800901030240750f40c806915a10307000f520405000042c255540586209401d5034124005c0c480882c40b4001d05201d065010360461650040e2400c4020380b40a2038040c140c11200904800900140c000180c10000100c904035104c02c00840d0500c003280d01c03c080c014034000c0f000c23003c4095045200214001e40d04ca042d4112003c030541058200d030b110440000d450050344203506261400c1c007005801e11011990b181d1110940741d00003003070340d102c6a5000c482c031030080e4407001b2039291500300142c04e03540341e01900a49014008840c1c950755140c8005d640c888240b03d00d090203403c05030750b040560ba811400344552510840c0f003c15404025610b003101d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 732578956 1250 732577706 732577711
    0x3030705010615030c0813081e0304030e040b030a08030c0a11060106020d0f0e060a0f03020418090512091c02030316050105060111010614010522060f0f23090d0803 72
    0x6941514019603012650144144c0d80ea070101d5061840d414079221503140d501014000c00a02340c2403001400d1074401e00601031800b040f50000403207a40384d0415090062480c20141d0030180a40d1908115a016140c0000c3d2070341d10300d074883d00042ca50790384c021034042150041e5a0b0300b1b051108003c100032a280342444802d0190449500908174401142c0c0018803901c51041003d0a0001da4200c4800c0303030700c500d0f003110f4411015007840514024241001c5000b44203562000c0c400800c0c0400314000c441d401d8220030041c13802030701103d0b00250b01266a6030b15220740300d081617018a0f4030203140038201020319000c003110700003010f803400c20707a0317100c4540f15440692004442076551001006103d60308000141c49a500c1440200000c50410320183c64074084081818140000441c804480141001c1c8000e2245001c09903448001da480d0005458010684036043c04204000c03540220180709070f60f103111116120803c03c1140c001e070581081ea6502030b4141d160080500812100402d110740e00860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 732580206 1250 732578956 732578969
    0x213030606080f150618090f03030a15231002030c01110301051f0203180f0409050622120503071808070f050d150c05040909060f0b040213090b030307050106 69
    0x44440c0c080611a41081d01c113601803440d401560081c00b43c5511020200d0000c80341d031a030300300804e4031501101850720f5030403c021100c610001040122251654120454520600c10b0303800c90141c80b5400c040f031215648146088414110403407085a02c2c000034401c41c02d0301140141ca28141c0d0140f2071b14203443c04004070b140900000001000107040c4002c100c800c0c0c42040c0100060f20700041070083d03c91103240602c100c90110050129110b42c0c0b155514901c20030000c104000380340302d40c075100b84c80e10b01c201d6100001d543d0088079054064100840440c01c550300000c1c4484000c801c4005680c40d41000d030500080202499448045400c50520940a0107083c401021600c0c504568080c802a554200c18090550305d040d8400084941c0b11303066143e0041030f40030501031311100d82100e203801103910100c52a0701b80350382d03041803005940c04001e0084400c90b040c8010240c9030288070691003201e000e141070101c000c0c2d0401110391507610206007080000e099034901139103601c4903820359039544c0109 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 732581456 1250 732580206 732580213
    0x1020706090b070318181d0a0b0604051e040c0906080a0302070e040305160b011a07020d0f080715060e01170c040b010917061f12120201090b0f0a11040f09021303060608 74
    0x8500002c2c0c01d9000e145880e01c10700023001d4001403966031102010010b0a954011500c0760040703158158480350fa00d92040703100b1401d41d000d00c1e2a0615442416082c0310311096903242280100f1240c4e00860383c554010340540080c24501e1a01c20b41c9602014014400c0d81080000d0140ba8205150702c840c000c2070078025144465594100040d02d034610405000e0095091010441800140c03150184c140340ca0743c00680c902004203241c03c00160760300c41c4100007440400b03945103410200c00a0741c01907040c3c4a01141d45401c0b41c0e2038078040f080d0004a10440802030f401004103d910b480d19800c802c2c00d1000c18500b801c12603039500a400005220081e440046801c11810030410740921001500e80b40c99500d03954095510301090200300c44410301d00900202c505550a4480301d000350886103105030b022060440c2d03480c0510003540c00000596410100c0d0f0b0034014411450401c0000751810b40d440758489543c40b80ca0690800000c0d4440420303040c80092038103000020456030311480c0300811070030002c4e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 732582706 1250 732581456 732581471
    0x70c110d03051c053705160e1c151b090501021006030c0506030a2a110d0e130b040501060e090a020a050a030203090a02030106031101020706090b07031818 68
    0x7a0103c210600a09107000c0e28001c200308000a810740c150200300b888a80a1014581000c5180b842034031072155000c1e400d0500c1c0520401112400c0310102d01c014980c0c5480c4000b401c40e040050764008288480d1070090b0290b1410301254041c02650008080c5900005070314000101080d45070300e40810980110742c18840400540d60184012086a00c10944c00c20196040da0348010043c00b881c01414004c00380440012031503d2203078001199590301002059071003100e00507074194035000c00c540301c000880311061442241400100ea600c41c140c1c0d44c84520710404014103000030081001d41c1007000c2600d651011005031101e01c1a54040c11403559044800105030080c8648074070050b008140300c0340f04001c10401d4907800740c01d40c0c400803458900540d9940303c401c940c6181410818002c2d5143d460075600204204a425185c20f44200030380a56103500c0ea01c17001529900700d070703101e12440f007403040242200080c41480c00a8000714805041c03c1c07415140c0d0003803c00c08800d4011030b0b80066071240d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 732583956 1250 732582706 732582727
    0xc0e0d150b01050408100905150a061401030c09140109120c14060a0c110414160f0309020f090a110a02010506150a210f090b0a050f0f070c110d0305 65
    0x507001401c40c0c00e0a0480c605450301e00c5050350398203e0302940390980c0d40d502000c1c042020034050a030340700e00302c031514503000e050101a034802407400e4800e0a411140100440e41c0c00d502034051035442000a440e218442480c0640c82640504a5030410341002a00c0c50040f4034069410941c8541d54021001414450304165044111210315552144070340420f00180c0e00076503021b51000c0801d60b0120b80702f0f29150300000440c002d00000000701f68081003060401001c03400c1080754441c440d071269103840b22408006030550407a16201c202940150744060034407100d0500104294101051810010711440c0152146142e60024860000103035101c0b8203226081c54441c05840c0c85d004844001481c20f6880d00000d00380030070100010804944201c1d21003c1900d80f81e2010324000c5228009100d02c1502d840c03d0072011000711a0444142d2501c0d010a08407891075078035a100700a40b03406039219403100305041d2007048400400320f4030805c00c0710048074140c0b40c036000c48520910a1701c800351921801039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 732585206 1250 732583956 732583961
    0x204090311030d20030c03220c03060b10030203100b072307080708151303020a14150109020f160f05150f090d120e010209030607111902010509040c0e0d15 68
    0x2991480c00d020505c00d0210309802d41c000ca94204061a81d040103201007220300a00e504030b200005090f0350185400001440120780040400040840e290560790070110410b03000c82c00251480e00402104030010b22010200c2802418580d0190800c103100850450020b11040002c5800024035080240b041100748000c00145016081c5c50003d0711030b41000100820381400c008001a042a40602003602454002d00421007060b4205d01d182c280075420303645c5103548000018035031181070701e41c000004900e51700d44243c900491072215114900784125902440c58020510155280503104c1500400600100101a07002a018020304003910f44091502034160005012880d035401c1141c0c83c0c2c2d1026448991500c181c1880e24000881d5865128514024041c148001d505482902c09002d40c00350030003046407006d004003046811004900d130817004c18071a0840c0c02804150248058450b0345019007003c1c00f5030b043c0c0d21344041c11585a40003e000040617074400e447c2d854822044c001d00f83d0030350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 732586456 1250 732585206 732585251
    0x904081e0708070f08090310050709061409060702060c07090f0c2f0102070b0c03180304030b010306050a020d09060c020601050a05151308070602030d14060108040204090311030d 78
    0x12444142007441c1512200910b12031000b0003000791020000c460100040d40c81542e07080381c4064115988040a100b02c0d200030802a612207021031107440000980c035204182040c81000a03650b01c03800d102c80441400035a80108404036444101840094603c2804100300710051061010200f007051510003030100b110003c5031568200700c003809581d008541800c4e20180440500000e01e00c401804e000894024010040c0080c6609840d00501400540f49005180141d114081e151000e0a452007415900e200341d00c0018810031074240100085101548981c0c0d1002d0000c001501e0b0008110300c0c141155000502101c81c81d43d10380d20304810301e81c10042c160141c80140c0e80890030300e050000140100070141b0710701d0311958001031110207114818103607100520f0150100d4441036103907840692203410540c0303411070191030b00c0aa10b045c40702240240d4016001a1642e8502e905c69800b800003a0447e01c4040d0140034141c0314080c03400c481000100a00c07a1003400c0001c2561940c10704901e40c40b50b2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 732587706 1250 732586456 732586507
    0x409060b04080c010804030e03030c0609121314030114090d080c0406021e031b2116020f01030b1e12060c0f0714061009050f1902090609090408 63
    0x144814003509200141c0c5070f007454824241040c4540c0c60746800c88082c10800c0d4400c4d058000410020000d101c00030f5424040c280c044145c500c070009242040c0c246000321410011604520401045030001d90100c03982c00307540250001c1500a200100e40304099405d403185591035100c00100710016a11900654214049001071440c040c80c100340290b03901d0700512480e810108a00925031821810800c80d69240e1142024080d400c2031820700c16140e40b13800c0c80084607558800007441c26540c8450451f80100e03201d510003545c4020300d0702030004144031110000d050503070f1007070a4503c2c0d6941050240d4840c20821003d0360b2068210300344440e41007548285d4200e40d210009124040c44101c040e1041c0800c01782d10591901002e092aa0404800d1400d8226500991040c4960f40c41c246182000780c80c5007140500c800e80b80c2546031304046604440380e10400548190340c0302a1400c80c0c0041071a008000e00450034400424009415030b041035408403070071a00041c2010000000800c424200d058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 732588956 1250 732587706 732587729
    0x7050904211d010e181017010b031b190801050702150f0103021c0b070203070c120309051002120313030f020a08031f03150501060e06090618030f12040906 68
    0xc0310020001100718144902d81071101280480b089074482e0301000200c61801844107025003000b000c00c0980e007035a80614101110060403c0c849100140284d04002d60081e0003031022041ea2816503100d400360743c10707056002c0c0382c800d230300c0102001e10401ea07401350420100001d15401c00c0200030f031411224200e2105c180310058208000d00a02e0320395181140e8040c2c461000703400b1401c0820700000035000c8010b00f111080c400f441002d6600001400c80c0500ca4051318030026121800c01c44004240390000300003036500c0038140890f05121901101400349401203503a9032000f4054801d440d0011203044400c248542d40700300c00e155020081ca1850101d50025265100c1184c4601e130748c81c40000d120700c0451400701014508820740103400b42c001c3d50400440328122002003d0765020f00801e1046c3c00c00140000e052a47c240340580840c5d011420003803c0d94645100706103021420312444541030740c180661a0000580b1606001d910644040012a41d5a075818552000101c44454004103403410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 732590206 1250 732588956 732588977
    0x5070618080601051c080f03010509060607110d031206081606050322020d1502030603100606050a0e04060e090312150f01030b2b21020a0308090705090421 68
    0x1140072030442d05569091702c06040c60b04404500c08880ca84201c0c0041009200151484000b900d0001a50503074000f00c90849254540404105440c09054406021a0424503c1c50080d2038400440d040c081e201c3e0070048440701c01060b01c24111245507102c2101600607044026101c040c0c0c003400e02c042c1c00c0300d050032400c40c1003400101c0c007007104010411550496000c044015541c0304803900300300b684d00284503010902110030100c0603403c1650300c240640b103003400080a504e1f20380601015543d10b55522810821040022645030b0301c041081508107035100c801103000040d41c00c0aa1240c400c01c0b006590314200c1c524644c54095004003040011486050811041d6884006800070340780c0074a80440c1007081d0400141003000c034011070005c100100240d0800c500c0c0e801140d00c10f20350055008680303c1440100048185080c802c1c00b10041c0c111001000010340a000d242d60401e219038200d034200d54136540400d842890039641903810340891108062003251300c21700b070000f90340075140840207203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 732591456 1250 732590206 732590219
    0x40519080606010c0f060510031a0103080d0906020d09050d0908060103020906010807210c030c1403340305150d0209010303030b03010e0106150905011409010302030c0d050405070618 80
    0x5080c058000c03410040d188004c003083c004c1c1c42c001001100d0b0454030401c408d0030f00d5160482a40e000c0d2104485407600328a50820039802480400c0c1241c0e0881c0f54103140841e0f810f40c1000812002c00111000c0e517090210704d8400300b19205078410244500010310001c0c0c40568050000d40c001d50040380781354000401400142c0719035910f244c201c9820300740f00280b5100d80300261402902d2108140300300700d12308a6402c100d061500101c42003c1c49481c10403c1a20128044940e1080da41c11561034140400c080b5040c2c54a032001521a441810808500c818031a8602c1d42c101403c00070b0100003907182c0080c4443c0032041c41d201015601c3c00c80b2106507490080e030125140d181c052002a040c19a6141803000545003074003c01c1181d11010003c03c04286c0300d05c0c50129a4521190040028800d0100420700354000da111181124041c24041d050044442c0110045c0d80001d00030640040c060000c001404100c0c000c4902842c4600050701c10380303062640051038883d90f504d000b0302510482d841000300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 732592706 1250 732591456 732591463
    0x5060f0f1003050c040b010306150c0b0a0212011401020109080406030e010501090207030c320a050f03030402010903060203130605090a060e1b01031503050d02030c120f0a0507030c0605090304051908 87
    0x185003505c000c40d11407849401600144019444400c0c8682c1c6151036045165200d9240070043e4403d41d00038405896001e0f654040780110040f03407050780710080041c40902c00302155805160f0b414030000c0ba00360226a00d001c0780ba00182e1210b000b10741c8a50300d0b000701d0032081c01800d0140c01510001c60600e12944c078018000042008c0280103442c0d4450305001001c2507804644002c41181425600560442e000c2681c844c8d00c9201907031740d801610041030a01c10040304a0340116016910505450300b181c030365000960000e001681c0f45c0445680202c00200c5a000e02403080d60210098815101c2a0801106840300168010303c0d40d04104c10300f01c9049035042030542c190b070080c030700041c0c1ca10506121004400c4990009032007440341c05000c94080707500200801880499005985140350890380216150284100107840f00d0003c1c0800c0f9011449031001e8170b240d602030328110b04901959100c2034100c0d0004e548051660f000003909205904002c02030700d6102d000d03001c3c00c59402d80f814192a40303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 732593956 1250 732592706 732592723
    0x31b090b100e0f03012036091513020406110c091803040305120a021c080a050903090a062f030a031808040609050109051816020a05060f0f100305 64
    0x201c1c0b515034201c001151800d51040c0070442d0001103109800d44002c1c0708007144c0d0040c05401c0031340707502e06102d505400020b0b0480c030440096a060254500e440008010420230010041e64416400039103809aa80d01c905174810641c079200e40041e625410188002c04c0b82d48560620801e5511444070700082e91030ba001116406003480000032850710002900a04500c00c5604c050414410070070940c6201908100902d0300708565000c59801c0c107019280c2d8480e0035402d400f02e030700bc21010300010b100408240c00665101c6a1441030740d1030310b0300c1480000c2c604107007070304820009420709155044802010480c00480341448403407504400b02c201c5010b55138840c1d049002d04048d21600c1c0380103800c000c2d040410720f0540c040c0381580c0300d82e16210300900d05401c510039940020740c3c401002502d401d00745500d0051400c1304503404046d9603158081034282c4442100e20b001c511600a0000c0803030b50134401c0340e0103071441072070710703515401c040700406442e403030191407050340e0b00803a10204000b500c005416036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 732595206 1250 732593956 732593959
    0x80f0a0b030106030c030606091415040f06050303130e150a03060903020705130c030b04020306030c100e030115260601030b040804052106090c0f0613031b090b100e 72
    0x284203840103010902400d01a44014241c0306120ba0100c00c0004a0700020700380e50045108100a080100f0000c0b00c94809542e4801301c014403145e50b0600341001d4100c00316118400b45d0110b21243d440010905d9640302200c072100e0700b10070070303c04e10a403c0f600c8002a085041c2d000c490700c4900c550800500e0f51a11841b000b0001a0740d0048a400c060081c4000d00c02001c006100440304a0340402d00000740080c402054006898a04900507510305442500d00400d40a0001c00c1003403546030601491550f140c070110140700400801d503110759001d000303a81c400000040f02d2224140707800740b64003520f0f00c2c0d159521302000c0812501901d800b0300240090451390480841a10368031207007841c2c401d602ca42c1d0845134012082c20800d41c000c0d1412a50003046d0b500e80000c440d040d60703402a08580f9000503416a0b03230b00c1803034250100d4846c580700e400341105000b4501016042a540e07944c010034402441c0e43e83e5007c028003d010496601c0714031440e4041c1c4010b8610480400c400c460040c000b2040f5003280c2e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 732596456 1250 732595206 732595211
    0xb0316051315060507151104050907120c030b04110703230d110301080d0806030d0c1e0b072c042a0914040e1504030203300106080f0a 59
    0x801d5480c48541069540815180480702455282c0740c00030000d60010b20141c030810660725898084020301e1140740d10417507a10740d06500301820841000a0013601600a138200500c600c000204070a162181040340421903e000540d407003144140300545682c216034441c0b440c424003000c00401d4000100817181030356842030190440d9483c0301c00c00c3c58080c4006802050740f400b448881199a0700e0003d6040e668800121120f0b1080c00e002140c0210088845075003640041c500701d081d060052265041551140211084c0150301e1114503180b001d881d1815030703100c56160240842c80350840000780c5480c00c0482c1d41c07441038085070080344002c1d40c1101180d014541d1514010051452207030219102c90041508a400c107410000080003940d50303008010f213142080c00441424907143c8146014614017001a042c0d520a1001000380e5020003130094007507000411407104541070725815010402804249008482408000d00c0d03107071081600328206103e8100b040c0007804101d44406a030040004102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 732597706 1250 732596456 732596479
    0x1a18040201020a0c031b0504090f020108100e09010b0418030813170a0905040f0b0d0828020a06050c041230080a0b0901061d0f0604080a060b031605 65
    0x4034904461003c0c06010312118400100401c8000441c111500a6140d1642e41043d210410030003101c60001d801441e801c0ca4200f0880194040c241e55a0f102200140051046940e2600381d100114125003c0140d41d64031002c21015261900c40e91510b103a0441c400d036141042558041d0815001504004500c4100c48900e02042503408420390007070342c11540c00c0d403112039543d0050500a01c50140922840c106900c0c03101c40000c610459070340c408c0040100c880b01035951119419a40700310141142920408106100170502452058090119900400c078100050520f0411110040c065102c2088100020803101d1303264200ba403000c9803c0111041d1519410108500480072050403482203094401a0b645164210441c00d00c08c4004100c103004041203481000740e42c0c41c09000707140200324030780042148445443e814403a41c2201606041e42062200c002945035003040e80206065442500c614040103594000c1020041c03068008100178000582c07800c0403540e15000f458000d05104c0070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 732598956 1250 732597706 732597709
    0x1002071805040c051c060c020c010c060b0d1703040b1308040303050a11060703090506180303010e0403050c2d01060503100b0f090103050304060f0905100e0105130e0a1a180402 77
    0x1c0d800f008020090403400340301441400c0c804454241e01080d294a441d1100c0412030380c0c0042003402260758143d461500c10070079070340d940c0014842002a81d40100c1d00340700700800510a525040701c0040b030780e480d0603243e00d440d1070800d880410003460a2608281050038400054011080e00c00741c940c141005603c0d0308651800303c1e022020f049009800d4403482d42403041a82e0035602040b030107030148d0180c400d41c0e900c0b0318141441090500082855610400040110114040390a03030458824900030b0302d0242281e280d14a02031159120310404504880d04100a2488100c45203001011100a104651038100066141c0d500d440e40c0d0b49074251a8603000c8400d5560202008468500604401203540c49082c90369407a04103000d8440400c00c0000e5010307915028801e484200d0360002e0180b45055955a800c03100b215184548905011090140348003144030103001d00c01414000140ca422440e080513140c09645500c42080c500b0190900b4100d215122500c48603091000b4000038101c07074031680b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 732600206 1250 732598956 732598973
    0x131b020a0201020a03210f1b021902090705040902030702030a0806030c0f09130204060e0912161122240b03010506070203070f0816090e1f06090903020c100207180504 73
    0x2c91726001ba031074422075038641c240c280d01840c4500c480c141401c1c3c0012903507006a076107010072000c0203001080e1282000c014030304a000e00794461050b00e40282442d5a44803903038260f030810703a0304c80c000d41c10100d040c01110ba0b2060703205900079411002004594500b06c0030440d0b21100c3d09405000340c40305800280c0d80544908200c9035135034047c004010709555140c00145000c0c0645001e4454025296101501c840701d4081d5081036500d0070315452012802e0f95004031341d000c07400006800250845d621451505880a6245442039145011404a03001005008076203040e4554603030700740c00c190040c0103004a49080c1c0c0c0c1940d500b51100da81d50340d540e0000a1606403160310000c2d038010b10fa4070211f04940c0204180d058901e01920720003c03da1110000e80a440300b00003190000c0d403060141c0f40b090403641d400942e41c803102a9000031600d0310385507200e0a8400748a8258003687c00030b280074034541460118003840e6034040c4080d16100e81041d25109400104400d038013103290303c0d6008141800000c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 732601456 1250 732600206 732600257
    0x26030a15050a242c0d0807112103040902030c1b070905060913031d1216090b0108070c060f15080d110309060c0c131b020a0201020a03 59
    0xc0c54521155914003600612800404035110f51050500c1c0f802d0400d8000c03503111071610b00c000080007424810f403082c01c03d0001c180c51120fa020032026800c20102d03180c04010005140164170141071150170800b4401c0d0100d484c089082e00c444000d5443d0307100300000c019502500c3c914000982e40f038131020401545030040101d0180c43c01c069121a010600000a00c1d07402c840140c03070300340080d540b507800f0028403010460301514441180000e1000081c85413488200c541c10159070908801c1c401c0300440c450a05020300c10314564000b294844e2020a01c8580d5001401031181c14448a95803000080c04104c003d000c010074821180440000c0040581000e250801c5444080101c514100201131120340c003403044024030300a50300c207640ca00348030b40e5498a20300021402580b400450b14103010701d40e488240107000600070004d2640311071b40c803810200300303201d0038540c041954644400300110203a0101c10500555000003500b00045c0d8002c00c0c0c42c103090f82c00d41042a10f07500311000150020115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 732602706 1250 732601456 732601459
    0x6090402060327011b1808120a03020d0908040503010e1908030601050c0102160309090209010804020f060409021c0b030d0906140c010e0a0b060109050609090a020403080a0c26030a1505 81
    0x900b180728140c482d44200c00170050059998070100c5089107540e110724600316025400c0c1d103401c180c94074844842008004c00704030341c0a1600502d050443c0450204403000d06104170b5a504000404214a00c0c09004610b00c0185050207450800e0032000301d0b000c220407141d4028000180440021103503030003403040e900025a04402955561950f40000301d805000704811008100c119002084000382407081e1019914107031220355050700c0b40e800b040140c140000710b669102c4802c00c0046101c07600d0740060111002030756180d00c103041d0010f0491042c0c41c0e071030810034000d5202e0540480c01d0742e80180441d0485240b400c2c800d400384e600040c40c03010f030b204e8903080c1c91440d0708150f4142041c1d0300018075624901e001c0d4a560300d4513110300b80119040003051084a07031046049c0000d0f030352494484100c54121114000041c41d02d0b40d66910302150341c00910b4120040781d03040541d8000d000003403040300000101c1c200103560061074814001058000600010b00c0c6c6d65a501c3e8000d164400e204000018000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 732603956 1250 732602706 732602711
    0xe061e0d021c0303050f0f09031c0204120809040e030c030f0a0912320c060903011401030b09010c03022b15090618050103021f021609090204050609040206032701 71
    0x42e030801070041d010986850035080c000f80300042d040030b190010140201c00701c0024610342201040301183e45420403002020a5500b0040084c100c13504441401d00c640c890500142c861600504000c2103e20786003510210750420400f0000c0314801204603044801120f017420b80b1180041c1e02103030261070350303000600300c040405c0d0071030248110b50701810340e2204080000f42c000c42c0c501850000030303c01c0c1c80c014640d0783d00401c00d14174180380c640083d02001c10090000142014079036045a800b074000e0b801960300440502c20b01ca100c050a02410a204030387c0d04065140c1040b0346960002290700380560307907003813500031607100b8900310f942c01c01c242c481d660f1005030a22a40340c01041c0d004055074400c002c03850ba03a2400d091075002d458061036048a40003440342c94040c400803012051400c01841901c2140204008140880c0a003007100000c0d0004100009018245106100441d2006000c0ca031003001603c041000503541c10081700d03809003203000c8000000309a42c10406024a8514680c800ba50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 732605206 1250 732603956 732604009
    0x6072d060f141609060f14030106080603071719050a060c030b030f01092a0f2306030f0114060909090a0525060f0e12070e061e0d02 58
    0x31040e04189080c024002110b400c945800402d02c403c42c0f80328503400046056003900b00180c078096400d40031034440710f052107480c85800304480ca420707034426003190b004a1401d07030601c8030f542020400d0f60040c0c2440044540c0b030038920003e4558030b44100341d840d100100f951040c0010818140840d03400964850410b00c0303050300542029001d0403803541c006000340309010f03d503121101c05000d4030440fa03030498400c40090500f0b4010380d450f5800070002410001110200040700a080740c01c00d4004c2c46403491013841103010307403c0d503d0010809602c1a109030002e00a111110b584d609143e41103440f81041242041c14820104195000e1188510345c040030803810411400000700b617500f203070f43c0300c0c00c15a0650101070280b440c030940741202c06070440c4c0140b8028052940518081e071820700b41c03070419041d102030030400100482e10810844181b41c0000c001086048003460b10960040e00403902d21110295000800d5000050301c915280302d0a442c01d41c9500f9034a491040450000400c00c03c17040a9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 732606456 1250 732605206 732605231
    0xe030a020604140a210c05150a14060906040c0306050d0c080c1f0e031501080102070312110f18060c03070b090303100504091703070f0201050606072d06 67
    0x1c580c01c03036055482d89040880e0050600740801c015000703541c071904903065244450310440615408903030400c01d1202d541819000320340204100b41c6140c040304400e80c40780c0b50925281d41500e201080107001c002650050102c1035850041c070316070150041d580045c4041c004402200640700300e6106a4100c0e42020700e81c0300780400660004140e0703c88504554000c000c2405000d0b034054103508000070008880503201145100c0c401205080000030b044a540307000b2071100115012081c1d006000c16940011a1000c164000100515030305040d031041041104400b81075a06104007003040d000460009054001003401e410321520040020389180e032074040100543d5503c0d0311203042076584c04541d0340000e2441c00000210b0703106944c05401e40c5000d03454030050001034000504101d840104104805200445003000340d84030b080c540c7e0b1011001c1000c0720740070b401c450000d040702c0d005040070000000800c902d8030000503541e181070444a100040f20b0040c1c805415181c2009000703c0c281285112038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 732607706 1250 732606456 732606463
    0x50a08040f0512070b04120c1a0d0b0f0a05010302210414060a0c090b032a25120f02070f0306060e06010c32010504120219170702040e030a02 62
    0x1540c000780c0320f0350b004051191050350703a42102d204451214800700403d20038450500c030240001072090b01120441901c0f448500684003a8142d6048041b0011903004074518950142000c0403000303865007001108844080307190389405015080c140350b000503921100f40c4580105001380501820542500e04281c5840880f0031100b980c411031900c41c44000c55004246440780641c0010503481d0300441c186002c0c22111940c00c010004e0510b18000302000f03002859a48182d02550940d003505507654100e075030702c403420380041d260400ea4054910781a0b400600c00500d00011900c041c28072611000907110201d103494840c1c0c219655546685000000700724071a04514242c805100c40c1d01a80ea07104401100d884100800252481d01020701400c003030901e40c204028102404001e411034040d6204c01c640c251001542c0484282204146c1d140800d90705000c0d107410b8800b0b062164000281545500c03002c41c204078085400018000b4800045546a500001c10a8803250640740c2301c1c00c4e2a54041e45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 732608956 1250 732607706 732607709
    0x203041d01080f07180c03020c1f0f0c0206220c0608040302070b0304120c020625061107020a0e190509100507111902040f02030405071403030403020a030b04050a08040f 74
    0x545103d2201c1c0c018440d20301080480903204c03400e15059940032580c04000290403000010028150308011003054030030227200302142152021040c800c10840e03105000212200213141401c0b440c54080f40c543c5581e400308482e908900800c00955181c1900c02c00c901d0180c1450000510300e1b2503901d000585580c2158000788900e000c1c2d020f4504a554a4034170190f60712003110000c20350340b00500496200f90148400344071560028100354241184c89a05d05484424100142142518114504104034050080f6003a580e4412016402c0142070b50100f40c40b1200c501403042c40b98405000628149d0090008461404030058207000d64141a01d4080c4c45081d640860040c40741084001003486015982e03044241c43d404004000400e10b4546002d10500c20000881c2d2003a29031450490341c14040c0042c50190f400b0b440a80903051400c005400b490f890103070400d019400c180400c00159403003070105400c603504207101030740030343c1d031440c0c01410302542c1c40004103161404540400c003006040d44d0f200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 732610206 1250 732608956 732608969
    0x90302060f25050d0b03100e010b04021323090411030c010801030c0b0d060b0c2409030901030203061c1b06020303240316080102030a05011211040c0203041d01 70
    0x82054641852000e45949100720051a41e5824002c010a00c0e2007080208445070b40401e0005100e83c041002900740001c50301000d08064071a032189030304220030b21600c444c40e801210304510303061440d0b44984100e400c5200da9100341a03020128041c81c40d01c6103105200340e0004000c0500d910341071a0220001143c031800b03500900c03c1c81014030a039400342000b2810380c0e0b0014241d000c0c00d442d1030802a8194000e003510403990751134030f40004a00d001d003400b03000303080010f00180c8a502c00c80d01c5100842d082c3c840d44d000841d41c4400c14411000c00c080201c0e800307031000b0720340540d4940d40c0201090561490031050750341040c16250100c180441a801c0503203880d80c071841c01040301d43d40c4408903560f000a90f40202034002500b45070f4401c11001c43c07158007402d0003400b500e004c0000c400380d1550600c0c0507403014900d0f0350000104007100403039102d41c80c090803400f0784401c0001a1a2240c6048030364011403d402580c3d114a8000928020001e50300100a042c2d04491203503003203041c0c426908020f04c00d0a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 732611456 1250 732610206 732610231
    0x130f090b13030c12021204030c0602010b0303070f0204090f0221060903120a0b030a0f0c082e050727031103010c0f0509150d0b031b030d030b0f030109030206 69
    0x280c1441c0c00302040c40101d54040c0d48103090b08540b03844081d0304200a5900f5001d6100d460a0030f060b014161020340011806058240000c518051010b400d484800d100d444c0b29030420020b540008640b880a2100d09030196400100c60802c0d1500611140700803a0280d07200354400f002e6540001044840e0a071459081d0607a826500c031840035981e01d001c0c1c114840c4400403030b00000f40100c0f00700da0040607041d0303006044405c8000315803104000312030207140c01d449a03e0082002d0180c150100564107407412030001d0981c494074080014520301c2180080704c1c40d81c9840f9004148202c0c41000c4600003913000642110020322074010152072034030140700489214031168001c40d0f107843c040c0320347d0325405410b0b01c3c2d140401000c08011a0b4035804a80f806a100b000c454043e58248014400341060084041e40000c0d0050580704051900c480441c1ca0200f0380400c6041342c0142c1c40c0440c09030007086281c00e0214080c400b41c0e000940100024483c59003540c0b804482009041e40002e0840c011287c00340207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 732612706 1250 732611456 732611461
    0x1b0d0212180c0a050f0f0301180f030305010b2a01201201090b030a0b1b07060c080f040804050d02060702151e031b07020f280e060d06020702130f090b 66
    0xd010403c0618440d295100b0140d42288800342403a1400502003100140000782c9100328000682c0d42c10740b041c5040e90500180035101c403c140d0107203d21405070031003580d1503091080a1254281d80c610b01d404800111032070000420b940705094120300180d89200f40801d1052006040602550f04000045140c9011000c00000c119085100300c01960b14090080c0101045a03101c14202c3c101c003420a090010b0f120104129140020300038004080c4a800080b03059040b0020041038501e01030107200c8192504824400000c80c03544c01c4504690041d2001c600030383d024000500f1a0090002c0650400600d001900905441c40024240d60030840030318210307a803c0196644c2180000c541006040035040b003050744040a05d0080e003000d51004018071690000c2a0201e188002c0b0040da0314803081901401e8001c0540b0001041c01504c00720000600310300d070090001d43c880c4101600980940c1e40000c1d08030035901e458020344100b07100040207210210310744144100600c4500b800f500c141050402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 732613956 1250 732612706 732612709
    0x904090203070e0a181e02030a0c0b0a0807033e07061b0507050a11040207080a210e0717161401031802060a1107051c15051b0d0212180c 60
    0x143c1d404258100c0c100d8446521b2400c1307070603103001c01210180da0500c90000d0400000c0c400c1e0f0b0807030303000d8049108040d40303a00c040c50010b8000d520103003401041c10b061040359102c112081003260703621016070034007007d00e2110302c440310700e40850410310000c017040000d144024444e0640003032040220440c024299a414030004a0302406031890050040e00151402d10200b82c00e04012181000014001450b09600ea90b4507011680503400043c003103046035840d405a01128401e8002c0041520814040091000c01c2d5a803282e001d40200c131150351100a0003100d1110030402e040030034a02c071404880749500c41018a0008081a88060010b41024070703e90011191928429800da4054402030915000a02c142c2d115815607060b0500b46c429003600007a640d54043c00c0c200040c42440c0703021004c401d2410640b044944e130008842a6608040620260104d80c0d0603070201c8812642840e5107649602c1c0c80071000e449025021880041a0020321184060682c60075079240c044400f11081c0c03404000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 732615206 1250 732613956 732613991
    0x601050108040b1605090d030809061f061101090203031216050a172a0403030809060f061203130b0405041d0705060d0f06260601120204020904090203070e0a 69
    0x320010500003143c00424105041650b20f000780c3d1030300d42400e070308025610f40440c0c00522503000940000340c0340803d011031250244011908826500503901144011902c039801c0070b209407041804122502086a030304110a50086c1085540101035a90383d00801b42c42030140d2500791982e03d0250030402c030804542d0b0042c0100d41000d0110340f103d803002094005690b001c0900103140102c006040b540600c0070070003043c9490049075001c28190b86840c00c50a000740326400040c00c1e10f0741648080d09010f02070702004142c60340311404460410101d13042c1c2007002d0440c01406510390504c201c0c0000451a8444039026100761401aa0b0400c41d1007400c40703400b442151180718814140d080220140150700b4080000c2800c01c02c80200400c18030500c1001c50101c459540c010396220b079020b400d50034600d89082801051000c0c41d8002c1440394102841c560051140d100002e00c11035002810340b0780754943d504000c03119900117041e10a507969400d08072100003070072202080c80302c4c9031201c03201d04c050226 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 732616456 1250 732615206 732615211
    0x30702060105012001051f0609030f12140d050601110115030308130503040b0406030605030d050f07020f03030a0e12160905040309080d030605090601031118041b0e030601050108 78
    0x1a40201900d9103414010f6908400000c1d14044840c01d0030030f900010202401500c0c010103070300c248a01c6181c0ca100d01603181d8101034200c1001c1045010b4108040340946181c8440582c100250404d4504203403800da49250110100c41d0115001186544814260341c0c0700d00c0c49104282c81da0500c4000a245642c2226a1050741c208022500b80b82440428411a051640a51000c644c00d4007180c041c4c40b1540f07990040d030b10507410030f440010140042c1d40e0500450300240b100b5002000c80e05102e03070002c0e16501413804885107084022880e18255a1400c912101250000c0c09403641c0d04d56001000f4080d801e0318101170f0250204c500346011990000603426010002c140542c86602d0134080b025002e0a00a0400e8080040d00b101c0401c4a82d0180081ca8044503d61030004450b031501090046808009291505041c502000c1310002030042c0112040011007600442c031844031031000400400c2007009052140752043d401c480c000350011003840c41800114202e4021341e0307a5100441c0d03140c008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 732617706 1250 732616456 732616471
    0xf0109200904200406030507080d0807120207060b04060824370c0513140904080a030e19060608010603051f0b031603031b0201051902011104120b07020303 68
    0x310300001d400b2643e503400e0142d08640040c0c1d0049038060100c005020350344142c10507100c9402404042088940420400c9100310603410b00c3e64091422010192240c000c51003128016500060000c04001050f0703c100c14042c0c0c018000c0018685501055941c0d499100002100428004181d251400c21280d0240720f900b4954040d803501070214040c6003000f2040580302410301c1064000712030000c4d00e001e68144c00c0d401c0c0c4e0320300382c0755084458802d6a102169000c0018030143c401040142c0d03c07030052003a40301c2c3c0c00108090381d41382e461104500401d9034a6094015000c0c8005a1541000710b0700024003144c040c06061018a855030300a03401c84409100090040d80034249414902c0540300e1041182c454120000500c80c4580c0c1c0440c4c2802c040d041851a4018041402d0080682100d8980c0440c0380711074081040a0207940041c2c0648070700c002e0304165000340515108120700c00d4001445010301541d540e034507196102c001410090010204031403070f4202100007500c0520020aa9109506 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 732618956 1250 732617706 732617719
    0x120b031b1306080109030e091303020d0f1709030a09051c060e120409020306100305090d0513050d060b1c0309091e020c0c0a050114190207080f010920 66
    0xe030020491404009907282041e2601c400b0002a1107100784a505001030081d01d5036440c400c260410411505801080702304281e458503c054086640024025502d40d1a414085004010218280d070100c80c886a03010003840568200a801100071000e0041c111590316001c244176201c004120311114801c02d42d104000400d1101000700f299a000002400400401d4400356114a03148034283d03446a00074841c0e00c2e80010520049060050002400c400c0501d000c22181c14090341b0241c0b143e1000542404021000c0390f80d86028000100e540010880140f04001480703141c5009006403e000b88800c0c81401925802104403005c80302d03441e29103901d40d40700d40c403603030405c0c1ca01002411030880c90010404070410003405091548010943c0b4405000285120541a0200003044c40d16401450411600881d405400c141c1d90042c0d900704c2360122403905003441005e030b003203191a2040d4807030300c0d040c80b032488035015265040d0300068515020302c40c40b040e8454646641405080d00c2950a50041c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 732620206 1250 732618956 732619003
    0x901020406020c091e040f021503014a09060f01380313060b03240a090b070c03020c01030209130f11041707081612080705010903120b03 60
    0xa41880700550014100e220b05070002d00c04650f8a10407a0100c0d021194805801c447c00c05601d44261840d0f0440d01c0ca0020340d2035076040c28111030761a800d10304000318501c09640c00d41611036050018038110b00d1104601c3c40004000d01611a401405a0310004240a424003045021800849290680c0c0c19101d02caa039880c0c04c600da071050380d85070400c03003203c95105a01d0181d144000c40f00a500500e0a07607014240c410381420001c08590201240c0e0b17110743c2c48020400780c14480150b40a0503201c91141300300f41540e400c428900580301c0c0002c001d045104400801c1425500b0000b1001e24500030b0342210016200c1c000150200d100ea18456a40b040300941d600081c0b03521904040300502c00307060040f412200340901d00c01a90401d401000d80000c034000d0048400c00104a1000240103020080025200c100e42d2071750300420901940d0f00881c7c1c50800407043c088503804542800ba4044000c001c8040c031410300911403000e94210141317080c1041d281c0c5141e490001a0090282d218220031507020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 732621456 1250 732620206 732620209
    0xa0204050f091e0a02041401020a0b0117010f02210106090302030c090702010b1e10020106030f02060a0c12030f0501141503070912080306010f0c170706090501020318060901020406020c 81
    0x744000d00700104038401c89030740203c00708882c0d046800340120030805a00e0768107241080e0510311541103541d04540c018102c40002c96902200241121944102000448403070f45031140500542000b2810560002030240385801d503d04460400c059100d0b80b146440e42c81d0703a07088420700124030010750b0561000131003500514061080c0e5400003107a000001e1038440d0400860342d10421003040050080b041500c0c0c00803410146040148441c091000700100ca0039a511902c50b800301c180080c3c010100854520308940c01140c2516205070044518091205d820f80b0003000f0342245041404aa400d1200000c2c203100c2444a054400310b00800c01030385c1e0241600f03d84c0c01900018040300030003070344c00000200c0040c0740310130b405d245005e9680c040e520320344100050721484034803038000f0410920b40e01d804086001c040a130b00665491041081e60fa404a080ca0405401d80f283c02070841c1d4400000d20000c0980d4a103460340250521017541c501e5614107072568200e0003903100c0d1802680208000c0a01d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 732622706 1250 732621456 732621469
    0x2090f18100e0c04150c24051008120c070e100819030206040b0406180c0f0b190e0a031a09070803130618030f140c030a020d0213060314010902090a0204050f 69
    0x2607201743c40d000520344429110050310707002001d0794407802d85a900107109018518054150b1215943c0c000c944501e04d400f1010b580c84081c0c58103040d40035004600401400d02c1403044e60300600d0040721001c442e040103900303008100200e108044092140c400c9054112000481104081d509034001d4102c55559469114901b80f00400c100c0300c80e40c0c2e858000c07642406030345804a080340680710841d034160801907080c4c02080b503500071035840041801440001d40880b054007256540528100d40340c0811080815007440c420f40009002586211004443d25450a545440359a0041c100ca01c1c456446840540364425003e006101030380e03852040c0500c5004e040c07030411541d040ba051105090b44c03500c500a102500a2040352400046250780032240c4040100100f240380031805804500300b958002003140032001d000900030705031000303482604240c5601c10030056400c0f24515030114103480206000f4580610103c5c41200901c0c0801d1440030305100303840a950b00941300020102e21642007110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 732623956 1250 732622706 732622739
    0x51e0d0810060c0609080c0d0813081603050f0d0207150606080115020a0615030c060e061b0a3e0609040e0f070807050f10080a02090f18100e0c04 64
    0x113580342c07202111000280004000c280c0c0000b181c001e0000845e0162000309407800140c081044080c004241d1804a201072042702c07090301d42d10345c0d014003528140c9802c0d6081c2c022000051541030340424034501c0924641c008188103841014007584041d0b000c0280b404540d2503004502c00a101d040c01400340b014140c410180e856007038011203416204654605068402c80800e030078010814000800030001c52081d1240600507505101380013400c4540072540c139000300b110048903404002000e4846003424001750b00340036000102d01030042d860b0055131003c9440500b45a583c00000c195002c0c1c40501c00201c1401103400604403403602d0070030301c10030000d80144620309005003d0100032462030401000f194004002c60b0f00034004141c54142002806c10f1617a002074090542c00700a83ea10359803208400d90b010080e00001030304c82801c500450700070030680300195040b840c2040020007120b11000d40c2c511880041c6c01a003200350700c40103032182504040c4e41426a0b200184001d00480200800214 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 732625206 1250 732623956 732623963
    0x9030c0b09060f070e0418060f060b12040201030f0e06071e0903080d0c03022505070614120705090402070501020306090106030c1e0e060f03040210030c0e1c051e0d0810060c 76
    0x5c7c0103689158000a0001d40c52003c948036a550a908811846540100002804140780ba81d080c500c0c070b00c00750710358075500420090400d80c1d1080800e0304030441c0d42c0210220501c007401c84001c0d1503c1803014207024010410614841052440d80070751520070680101030700c1d4000c00303160411410003010005030140d80d074240141764090040083c1c4c030280118040e9070041401e440490301060341050340c04c1c2103498004100304030489800714001c40031034046440c520070303003030380015207a690941c1162140074030090640d1050001860105201054014500030032041301c030740c0d0140c1d0303803040260110341c007a0510b0000714600340c00a02010100420031000412141800e0030a07072003802c00516503902004e40c0c040c0c00400130050206500b0882e1026101c2c0c4042d081c2003215846c803070000303026000b01d2101144281c154603400302850084080211310240d100d8201c600c581034010f54500d11a520300c13000a11403049641c80003c2d544a000350030701030030f41d035407840c1a0346040c200100ea2080d103424055 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 732626456 1250 732625206 732625211
    0x70f0b0a030b0319230f071d220c050603070c1e020a0605030a24080c1207090209011133010e0c0304020402160b1e0c030a050907030609030c0b09060f070e04 69
    0x181005014940b003a006c10400360425504050340c4a100c50750f204402801d040c1700c41c1c20050790409040e17101c0241d041284410f40140e0b11071400c010048443d800c0a074200c1e03408001d01c408507030084205403015209034016102c007100072580468101000001030f40c007036200d4200304400d600070300003941c01403948040860034061698031426150301100714000da207440098200000b000c14085014804d0003240c0325050f044011035855a11495400381d0041d940d400580c40546030300cd030041c080d900f030500069a0607100d07013050404410b01c521132032540d02000411003900061141c1c07a40341c10780300760124249103070b01c0d41000742901c3d410013841260420ba0030800562a03e585110528119104944402c101d14100607040c00311001c680120ba1854aa101480340b440700f140103480e84401c500c50001507135a40d21420b1450718016500182002e841d00c24000c0a050384140040642030150512034202e4464103000c40c0d503020111883c8c04040c0071000403a840d00d1041d000c0407401c4000400c00f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 732627706 1250 732626456 732626513
    0x40c0338061e03040f12050c150702010605090f0103111f0f05040806091006090903230405061c0c0c12080c0d24050402120c0309070f0b0a030b0319 65
    0x190b00d070035401500c0c02e403905400c0c2a40a8204468540700160007101850300701d040c030710400c01c000d40d01e04040040203d003c4034a000501e00b2480ad50040009040040c507004590506c0c004009560310203000c156122000b80004d00e85900300a1025141c102c40411104c5031403a03840b10031651b80c400c0c0c108800801c0001c10001803200d40030081d25006a07250b401070325112400c41964800c5134115480280c0103030034082010042038003c000b1407414001720107401c1b08524028031540d2280b040ba00000d600c12404225000c2036a62055500840d10f02c0e80410808130752010703410765031401003074070040410380c84080700700c440340c030400c03030150882c4a130380c3c82c1c0c2e04020350240760341c0a40d40540d0f0402d10101e04004005190b08480004000400d020f5404501d401c4280d011309541c8900108100702c4a40000003080c583c07101049010018084d40c90703680c1c4d03c1603c032042d002d481d6103c02440f100107420494100c0b202d00d80407960020540c94a0f220700407451107036860b00c0c200b6842035010131400c0e130080103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 732628956 1250 732627706 732627757
    0x603130b281a0306191a0402041502010b0409210201270b16020c01140c030301030807060b040e10181b0512010204080a08090f040c033806 61
    0x400c0521803604800494210561481019112405501a48203071310a00a10075608441c9440922081e004840400d800003503055449903600e00c0303206160880d200003800540005480b0881880005130f0f4024801380b8221004c00c426912100405003d840c6143c505103000d80c0c5960310740c0703d00200b90002103500e01901880d01515a00102c0624010324903141c04000c00072410083c80c4d1083e107110032032205001a20000b0364814604e04100c0c144100540c4598030541a8000c0e6030354080c502c012660f9a68503843d280362241c1140c80f080701c0a500b8031083c1c1c6020301d8103016500104445100a05004014512480107001c030784030321969924840c030780200454448004549040321a01d01c0c481c040e0302d804c060140055102c524075102e40d1043c041408001800300b0182d0b01e45401030117980e00c034175071100004c0c182d140e845c281561085c607210108200030b4040c0c01402e141001c0d0035441c07052509004480c07152100c09603c2848000745032440036803034035109001d40400429003000c030100c43d542c0d84 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 732630206 1250 732628956 732629011
    0x721180b040810140f0414071503060602010903080601050f21040b09030a090e04061b0915020307030e06070f08070317130206030402010f050d09031d0603130b 70
    0x4120142000c8005018001008100700c1c4400200c440c19040200b42d0a804201c034401e071014101510004141000c82c0500c1841508800002c4203082640c1009654650a2138180080c0c00c0c0c4101103420000000750140c018411142c44c15010340307402c10281c0d506001120300703501c8002d072034646000034015030440c0144080f4090a40340c00041b911030b542400d080821001d480105010481c0e03204102c9034415642c41031518046070744800e241507143d01d0b60b15140c070144c000e40680800150041d00e5030300b8101e81c4440400103d079003140f24035206282c0c0351802c984a00c5012000b0700410f074500c50b2180c0301d0814000622055003d08a14a862003031582c07001803a0b40802d500ba00080c10404c0403441e94190300c90304c1074002c106040005000d00c02a8040303011400300500c0a418065011110f90391702d40980c0440e40041d0700381d0701c00c026200326854042c00507451112112a0300b4030814140707001d42401c004890140101001e19035000003181d6039040310041c000c250706210303101c84a4503149104080e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 732631456 1250 732630206 732630209
    0x31506031f0905070b03240607061b090b042d0b13060810140f0f090c040f0902030106051e04081f050a060e060409052d1002072118 58
    0x10002181c81d242d2420410f2400f0015000340b003042404100380040078075011035884660001080107110300d10b804002850b113000c0d1000c0948a5403c1c52041a4000c00345043c01d40c4101454841d801c3c0d09403120039042d41801540984d40b180304003407000140a0003240e0070301d5800360800744a10010381e102c0214400c26040042c0c0c4c4020002c0189003405015000185c5607405080c3e40d60041310390780741c41c030580d42c551041c000d880d004500da0b102d0701141d51030b20741000100000240c0314606900382a03101d500940e02522440552044441d80810611b4950003168102c1d40706607921410140361010940002c0d04907040c0e20081c110070000020030301010b120b42e013200c41c141c200083d82c0700f4800c8454801d6440080003184454a001c10611800c4048441560008803e840000c0c454800380340181c42c203c1e41c504070554120700d0302d84000c140600c80b50f070b260b0522007520a440d110b00c2c08061180603405110402400c041c1411094552240d511000002e43d4400346001410740501541c07484407280305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 732632706 1250 732631456 732631513
    0x1905030312010609090e3403050d0f090e0606030603150109052e0303050d1103160e010804080d111c09060b0d0c090b06070b09030a020d0e03150603 65
    0x34000100301498100313204c0c80080040c442e0134021040d40041054403902600d035807a030491017030f031030f83c840c17031034101030b032000d20091240003070602c0c503128100f04ea554100140700701d001403c0302c280c0c6803a4a00c181c5101c8215100020711801a8480404114a98000a141641520034121014100725215510754000c120241001400d41011800395811851003110340b4621042d844070300303008a10b00d10b41078040380d801d881c0c2907840e50920030035038000c5d111000c6007003014400442840703103e41e004c6070000f100d85a81c1d19580d00004c0d00000554400740221000341c00c41c041406080d10440440d000160800014401d0710f1034144850220418601403a400e00310f0a661113030081d0800040d80310b0080b60220403154074000c085240d47d00c1d183c00140e400780f4440140ca800403c18107450b04025100c030b0551041e000790f0380340351642c40c00d55250400c1428500510494171040c080c6030003103954511120700030b005007001881d100b2044941d140d01800141c0c1611411492080c0400c0240e0940c1034542c0d0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 732633956 1250 732632706 732632737
    0x506030c060d0b01121a090709080f011a090105090c07030318050a021810060c0f06050123010e0616030e27150d0b0405150f01170a0b0619050303 64
    0x303d007800101026400301c0421000c602d400910a0350707440e41410505c2003041215400955070b61403004a4040303a02e5401003005e40314480c2c41082c0041c0c10b420614a980c1a06001e2551304a02001c10007001801c1c4122600182d2400120768107c0d500d200401c400e80c0607040c0030560501410f1480d240b918540c0c01035038550030040422046240231018160b8110745d456074a0958180350800c100d0002540c0715400c144000c0900a000300181601180701d810740080003000b040da5212290f050380110888000f0226a5100002503a5801041c041c08420340203041d09042c009140b04102d8034080350001541882001d414198244d03070341101c54401540d15646074019488041c256180d0810082d10803000c1c68215812030001d92070300c503502d041d12a0401110709160310f40e42800790515682c0104600c85002e0441006103440c0ca910b0706074100c852004a0350703102c4184510345a01c400100100401c4902c17510f0114442e4504181e802036502810900c5130100d55a40c0002480c43d440001c644a0204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 732635206 1250 732633956 732633971
    0x13060e0604230706020c21030c010b120102070f2424080f030a210e030406120c0c150f090605100b0f0706020d1d01150f05130506030c060d 61
    0x150034070324101c0d421200800604003d030520344040c0d04c1d102c100c12514010342d010045524488540e06040078000550304c1981c0c0d0364600e03440301c54040d16016101c0c0d809090341c1004840c0e101030501c00c4840240d04640c280022004590b6485011070200000d81a200300f80302c0c0d00041c0e071155226901500680c1c0c99059000c9005003d480301d040300c1a8889a25904203000b1001c26560101c1224000c181624141da08060305802044d040101d03102e2168102e86064010400144000b004105540c96522950103a0200044d01c105071743c0b56141c18400110142d01c00e800017665a807403489599400c00e400b050000d03102d00b00300e040b038541c0441030391520345a5007030250441d4105080ea000d0504040f03104d1810445407034122071840352540c01441260b00051801d008000355028003007245043c41c090913220300c10741095018000e81c0589500e00e2404080004520008800c2c9104840b80a48160500d24901d410500200f00041659805026240d01d8140f0b81c1d40c0c0c00002d100d1458040b00008200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 732636456 1250 732635206 732635243
    0xd090b07090f0f0f120f12180f0b0d0b060d14060405070908330106050309161401050c03070f05071517010e0714031819030813060e0604 60
    0x91074280c0c043c0c04488810002407040e00b04401040c1e0580d400966a10b41150292814406d02c104100340030784607240b8418600c0545030700c03104034030303001e0480848003503442e494440f025000e415602ca404040c1008020440c05080b040d0840002c1420003441141000805c0c650b28060f02d03104510381c1441c1c0b006030204a101c2c5840c3c4075060300202d5628000303201905151141e641d81c607000819050000003604c100d00c0042c903103d030300d100344107442410100303c1d43d581c600035100b508143c0388401c0a024182542200340d0a2000c110219003070190a03401e8002c2030001035074640d01c4800228030501040141c0400b080b2100d0a501242c3e201d80020301505103440304031000756001c0140201004104c0309c00d901420301d024180c0f41554416050400300d504c0d25282507848513110f00b0301450002c3c0201c1000700c2100c1400c05a042185900d040d40c0d100491400022003c104011008001c201c542c000300c0c600401214003100394a1150100058a181c0c1040241c545481110100c404a6001c84403100c02c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 732637706 1250 732636456 732636479
    0x11010905070602100e0109020604060810032018062d040216020117070c060b011106070906030606050903060c0a09030f0602040609270e010b09090a020a1512020d090b0709 75
    0x40b0085c1002000090500d60008031681700303510840f810000104003185100100c0c0c2c000c80001c5500c004401d8140401c828806949081c50a0a07440f0b14223146100382ca0400b0201c405224010013048040381c4088460100300c10180c50038620b80e2000c13405805c07080c1d919980300070540020095001c4940502c140300040110440f00c1c1d881c01000b032048240500c0a8000740070a581540c080300101e014801080100d03103200740002075004912405043c442425040f02e0020199103a0341e40900c030307664032410706403a6440703200400364141d0b200f83c0005051002444c00341898440602c1d02c1c60085949440e03441d000e103044d540030b032601940001c2c1080405e0f00302c09503100519112003c0710000201d4002c0c035030b000060015451160f900c0d1106c440f40c0a40c00e6001d05403030071700100381815a06000c50455541c1c40a418200d0052840c11400b00311080407800b00900c4440950302c640001d1b0410307038804040e410102640c07100030349402d0600c00203401c8800c01071040a0075030b20300d2031142c1f508143e010b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 732638956 1250 732637706 732637721
    0xb0415050a02100b0d02040c0801090f11071b0b070b07171311040b0a0305060402040c02032d0f0403110a060f020d0e063916061101090507060210 64
    0xe1110030800e0340203440d000300740b0000c0103810140005400702d018000c10488850078030002d44c0585020054240a604011424140d4422800c10044070203000c80f00d8045a072441d00a6101a40c1030001c0c4001862401c80b0700c0d0440300c020705104d0115030303400007a4441c0c6c0200c14100c851079858402c0001a07540490380c0c0c5580d8507031811350583c1d41807203240200c680300c564101518141c0b0f14401c400041d10b807038014110038500500444000c0e41d90742000c03601d504c03090f103080b44228144050001c6591001094406e824440c4178102180e405000750480745040d0b40c00140050f039401c0c080700c0c10501501001d4001180642281d41c040c20742c000070003010b4442d90300f00909010041c10402044c2c0e030700142c2c60490b00c00900704488003003100c900144103802070800741d11032100948100b0400e03d1035400f0707801028042080c440b103034a964a20682d1a001e2900c1c0325803540c09c1c00c260402000d8401c440520340e031662400006048c00c80740d1100c07420002c0ca42c2203400940c2c010240b40040380c1081c4540d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 732640206 1250 732638956 732638999
    0x15070207180518190303150506040b0c0109050d12050f070206010618180905120301120f11190f0906030c060f090b18090a090c090e030408070b04 64
    0x11046041141140411410000700301d5080c2e81c5200090300c00d809070b07158100360b0400000b16004904400b0784d004c40c444103442c1c00ca0020307052400384171800301c98030400020740700000c00710390405003003010054040d00008038a4a0564071028003c012410501c01c142028240f5501ca801e00142c1c05101029580040d04e07001c920b4021004111049601140a80c1501c0f440d113032445550707800d401c4411f1100d040b07401c0000403059001d04114000500d0748051155841035064071003c205c0990380d10414002482001c03c055250130480b40000d41e20305049001a10400311440d0062500000c5012100840c620b9071110a183d4010b00400400204181c02446402010303c1011700b10350310f041508803113114000501c64101c60201d0f209024442100242c08917400242e21407810242e8004003c000f13115141c000c0c9100380200309500c0c03240c0660300c4025040351802d000301b40b038074034120018000c03340044e44c2030000380004113008405200020007002e002031140d840c3c07810420b42d40e003003001441005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 732641456 1250 732640206 732640213
    0xb070b0402091602060a331409040c092c01060501121107060504030c0227011715071e12050a05060108160302040f060507140105280209060c150702 65
    0x101e1104e50000300d5580c81003207000042010030180d007220120000360904400d04000038940e4102400b10100d0326421070780320040802c1c0e0380c0c81e09020310031410401e40c0c02a005041808003800b4140381500708400581940003d111a010310b02c0c0144404201520a084981d44888081102e90b902000c24011211111010003140b0f000c200c442c902442402c80040c022625480003070107041c01003031403240141e00507020110041c0c0d90103241c80710082c0c040c0038441c0c3e0910b2000100d048031020340250890440403008000c00740204441045881c03000300841c04110094550341c4d02400c8640901c0c0011a5907102c2d24a5610b900d20034805070340000f415400214030b01000c1001aa9018028a422103048031100900341d00c281c800700c02a00c5282c003c0040d615038003000003401c60b031080051107014021480310031803084031002d1500317071001940c2c0d00c1002c1c19102107840200c1804400c1032084041c4102c014038142c0070300c3c08a107850b000b1403102d07007268010160510722070341d0400c0796517884185423000c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 732642706 1250 732641456 732641491
    0x903020c04180615080604151103010e04060f150605040501090b0906070b040f02040218010206090105090606100e031006050112110f0a0210091412160f03090b070b040209 75
    0x1091400e0b0400703070094003007038540030b800945080000b60580640524815500e05280c64142000c450310b401805a50391440c03d040549041101c100352030690f07091050b1424540c6654484c94082c0c1f2100c801002e915580b40c242519080f4a40c101130003c2c5415142c03943ca0707615060014001640690065540d5031041009020705d030ba41c2c03412601e54582c440702c24070740754859040850100e06c40040c0250032a10001d080921a0890384070140104c8090303084506d20358030042c20030f09a5005440d903115540c081c0780410901d242900da10703420314072030740b0744050100b2220000a1070150040305904e1400c0d40c42005110a50f404440005d07080704e1094284211205120840d040744150381e407400300c408012400c4111540300384042c200a420f108070505c07244484e0704252600c1e0240c42071009091041b1088100c2003108141510803d282e02a8076144410381600d424141c003c01807000c42c200000d0300404505550030101520086001d1350440c070141c5464418002d103400d015140f081c4c407041c601c90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 732643956 1250 732642706 732642731
    0x1090b041a0103020c0709060f090c020d080f0c1c0507021c120f0603080a020105070e0d0302062e06050406021632280501090612020f1c0903020c04 65
    0x40504984007840e0050340d481186030014100051034101f4501c0b241072031000a228410104504151410350200300b001814003071040c0d9541c2001d03c400340200b002440018034000032500c4d120341c0038203001070040ca41110380b043c3c51a004d00c400120843c666076401417250441c0d042140300900c1140030000802d601124101a140782040c401d10b0817050f884209880001c0b0300d6402450007990300074522500d50980c0c82c000790182101b01e510500042c102000c0402c3c91400407040348a807030b010340140c00d0a840e83c006550485216043e140711001c100110745035140000e484c010001c012540d244c545072070030004001c0c02c20003442e9250389a220749240520919010307261a009400200ca66103085c1c20154100c14445415008426400300a0b0522100b01448070003030340420f0b452400101c44240e0700c40300192042c0d107850007042e00141c006040c615000e00030340d00501c80b546010490368140301c0c0e412021440100f09100418507662500e0304001003640401c411a020340741214188460b50f00d040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 732645206 1250 732643956 732643991
    0x203040b0d0b04090c0b0304020f0f0d0201032301060c0b0c0f120402010c1401020706060518070503070207030b4f0204020708070b01080723211501090b04 68
    0x301c00914a03900d0110034815034860740130640c0c042d400000300c0300ca00d9540c824640c0c1900200e030168090400e4496807403062034403815206d2808401130210800d101349070011001450840740074680204021440008500d550070100e008240031b98500700340c1c119074039141c900000054502c0083da134007888501c0940c654030341502e810103800e0440071015942d600041b24842d11702c6a025244403040081075984480640040014a020701018072000b5075950511a401901426030201e0300116400301d240d0b6441b90340250342200c1c071071040b101c40c0c94072900c4202d50300d1400e0312050242403080100c0340c5003074040c007204020040d0403c4900056040240341e00f0850044080c20141d6002c2c00d000242195a6a41500c030300c141c0000d149500c0d036882d0718000800030000e0040742410710401c40000307401c5080e80403100406945107020f403010f0803060240f04181c8204a0610b4264003815500e00c440402007012442c6040403100030320195140100740001c40d5030740c000460190703046c400c1c03401607540d581 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 732646456 1250 732645206 732645217
    0x901120b06030711150c0c07080a080d0c0c0501050a02210402150c010e100b031204060e06030406180b040b011a070206280c050715121d0d051201060203040b 69
    0x3804e102500c03040303480c492414107121400e0501558051414841c0f464000307406464120519403c4030b2030151100c1e5920340d20040c5020080c40b20b002040503048a44031034004413190a840d0509008024031aa552800d6440840b10390304965404100b243c40c002481c07041c0329a560215041610030306154012550098001641c5460500c00240d403111800007548294200038603c0240c8500c040382003002c0c0040d10f00c00c4c01540c800e02c160710314000b040c200d00f0110707003c80703410340c0300c621004071104103020941c0c01c014425109a640c5040c20241d0860800300441c600340314098000e141d00e040d01c3c0003440140d06030441406620040c1c41070a560b0340040448501e1501100c24036101c00701c0401020340b2968031003200050f181d07500c51030044181c0141d9401409803144041e140d2050715030b034410f08520074800c4804005613500c10451600e40b182e6010440616950224040400c10249003034038100e508808600000d60004e00f110181d0130106005000d8110361000d0351605140c120f030b4203024002d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 732647706 1250 732646456 732646471
    0x30c0e0315090f0712021216120510020a0201021222141c090801050f070e130e070f0f0503070e0f130b0a0c180807060c0c17030901120b0603 62
    0x114002c40e4180d0000c000c80540180324000b2a030055031252125030300c26240c14012402001e00010740711110001181c40304101c01c1c81409650050700c1c101d1000210820300380e05545902919100b050741850b18001007164015903000542d07140400000c900d00f841c1e00400592003a41c8a15800070b00800e1001044c0c0d15607001074030401155140d451090a000e1070210350b00198640108840c582c41d045802601100e02c240c1c0200300681e59883e0038800060304650b04000541c031780c0701038821840c09120051040025180000d00343c60103440304c0385890007581010785811301b0180c0c01c01c070a1030261160006020142e0161420500c0e02c0c040444080c0c0244c0303210901c09441c00040c590604200c0d000c0b42da41d41282494499080c000c8615008100d000d4845000034001202154420308110140301100e403100b006142c51842c25004407002c4014110840311160594000a4130082d0401d80302940300f9000c2c05107580e0310f0b0540001d0304443d41011429803590800089a00c0380d5a9501500e521581 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 732648956 1250 732647706 732647743
    0x70c03200a0b16021e06030423121e09060a0801030210050c06040201050d0f050901020d0b010c050604020d17030c130608070c0209070203120406061e1409060111010914061b030a021602060703020d030c0e03 90
    0x912f400101e0a0300542e000e0702c0d0426070200d011442070743e025121904882c002c1d036115262014401e004c039030b140700380e4240c00426400000807400651045c001400c1100d00072400003030303078040044020203a03a41038651294aa401140b6490903448078881c005028000f424078810301050b540c3c40c01c1d1600e0000b80043d10490324955800184082c4401e40c0070489108001c25540b8508aa00845241c210752240244034160311000700381070b4000ca900078002c0141c2e8550300501c08240c0c0c2002080603004240c3d2045001c01d03c80031040c03690384220b082c00b5034410341c808030b040350801000800e2100d4000f0b5902c00c4c100c0400080080f030700401c3c810a50600252840c0305503980e0100140d40c2c1540d160403c40703840d843c00da00e010a11102b07001c000350020940c401e90300700b900d03042285121300c640d464103101140710030000304900e9a450b41c000c254003408a84401c1017840e064000400e1900502d5043e07000d40c1054198484a5515100f40c005080d01c0307081c46403d1200b4840030990311900b1140b0780c1c02040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 732650206 1250 732648956 732648997
    0x903120903270506030903040612141f080106030b091c080714090a03080705300d091b1502061b070c03200a0b16021e0603042312 57
    0x303120400308050907026056545e00e0401c0b80b00d16980b64410712502c000035a4101c614a01604103000c4c2d20745200f901c260400b144e88503010700744441c1c940130700803200c0701e032280703000140034402070180c1e00040d170140014981600d0484001420050b00711f80780c2c0e00744c946040c84001c034160803040345504807011b07240248441c541c417030b4005503d00c00d618056500030008000001007080c1c1c000148003041c412000c0c5d4891003141402d0111010011035001c10300c621282206007800d4251019000e661184403001c20800d50a80b0b40450111810b030000100545612050000c5500001072001c80016440200700d40d1514040440c08460065445031401900241100c00d015489940c20003441d04026040700700204410481c2d91004210341450142d0080900002c4450800c002d039148006220014004070f8207542c204419400034000020a548642040c1c6a0944450010b944250312840c0500015010b4001c01c4910300c01c9940c4083e540d50003508101401500b1405507206000030210300c0c440d45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 732651456 1250 732650206 732650267
    0x30528030507240c031b021011250b070810151101060611010e060f01090b01022103060406051c060e07050301020c06070305060a030507050d11090a0903120903 70
    0x514091510304075003c42c01c1d0001001d10b415074000c0c0d5001c00c26480400992a4100c5072004117844a40c0090140c0c01503404c400302c5400079000b45000b00040b0a19614003a0520100c83c8105900e800310f0301c90606511031003041020b140c001d80e070010400d040000880c0380c00000a2141140d501810300b8101e100c0c00003400d564095817540c021303c07a00000078400c054840320010080d06000803d00240d42c03d0000d803030400c00c00441e8041c010348032031204892036820902205d000d85008400d560451040c0d28084440c01c0c1445600300c804d1040040040d0f40303003890320801041c0e5146402c91032013144406007a081c141000710031005400d51144000c0303002c520380814207040666550117150103500010301ca203811036021903601e100b2402514204102d80b1540144000c5598602004010f40c0c07080b442800030740344ca6488595180c0c45890a01d0044d05108080b4001f20400d0b01c0a212040e00c2d520150f0406030440c90310701451801103c104882c40d03081c0c8000b480c1c284200c1c441c0c68480000242e0b405003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 732652706 1250 732651456 732651473
    0x90606130e0105130302011a0616110901060909060902180907030605190f06050a09140a050a090c110c010f14040302040e060f011d28050c04030528030507 68
    0x3824860020429071600d001305008002d440300301100103510300740c00094211000c14030f02c1d5007000094110781c1890381c0f03d840c00d19000d01005007070f80c940e02c00480f820072a070303074444040d40a00101d6598103480c51034828280c043d54859040103c4031030041c8600e11420701d1040c44469428400c88072802c0a45503000103800900654000e513401c000d64401e1241d190100004010446d2020490307518441d03074800e001c45050182545000c0025207401e0100440c4d801e4502d040120075006160144142d41d8030000b401600950703001c008807a0f110040c01076200c2d04410403582d1100c3c0c0c48060070220000100080c10900001101c80c01c2c410281c03031800854000c0805d8030099a8060070030403003607031040115a5101021628035900300082e07800800c8031081c0c060a282c3c1c0d01e4580c080101280c4920203010380f50407041c4c1408007034080e01131035040705509034000c850050305c9400300d440c0c8d5141036043c07050402e1285071288280c0313960381c0c0b110200c180b040c40103010b505406290490f214500c525101c0e04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 732653956 1250 732652706 732652721
    0x80702120f0d020f0a030203040b0c010b09180613020112020a0507080d0203040b01060c12030e0a060c0e04230f0403020a0f1a090a03020c060a09030b0a0b0406050909060613 76
    0x1031249904050340441e0014510300955455000c842c4030200c000012a51020b5141e4010016041400100940b44070000981070940c0d0040c0080b0700380e220280030440c0881b0071141c14036030041c01c01d090942031100b072240c90740003000b12136610081c244a40010300b1080411b0010044a40d0010f422101544148141c1d598154460305460341c41c100c0c0080c04000e500162029945903550703000005d081401481c00c0c1c404a0303440110a040404000b40560041c4014109044980501440e0f00d000500501c195125500c007911282044600d80090100312085c0080341042130095007004070324004000c41160307000107205000013040ea43e5140072818500000030082c89004070401107003c005070052115608000103c483c2c881d603840c2c803005a03640170280c8000d07015820959220141c3d003049802043c6d40c1c2e490f810810602aa26501c40034038000c101d5801c0d00303040c1d031201903100514290003248014081201c2c608a181054045c03143c541c90301603c402d102d510320580000c2008101d400011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 732655206 1250 732653956 732653989
    0xf0402010509060f1b01061d0f070e10020106060809010b030a0b040c030c03060c080f16030e03040812030108240a09061d03030415020a230c190c1a07080702 69
    0x42c1c5520f042100c0c00100381d0040c2d00c1c5c2d0450f500300500401c007001148200c020b20a06400ca080183c0c440d0f2048161004000d00390200708030304154070284940b03885001d00d140c85420350002034180d1924030000d14104016108610590400b004044a9a400a000c206054100c8000351407900d42e80390281407041075520042c02c04c180c0600c000140011544101c00018540d102c1081c4e55030b1b40012410701030304c21107140c03500c40015071842c05a42d00c41c0d84011010712041d400c4030319254403144290b1030300312103e50300311400d40004018001100e0600003085030021265003480017115070390711408220717402440404442d540d8281c900903c180d40d00005103d1142c0c0c00b480803c4200880340c81d8881e4400c4805403901c070080d41e40c003140f408180c42150800703815075468880d41e00300320800c104a026071598110b4180300511080d4051402800068104500988101280031301841e1134159044d10754800032420321210004520062200100c551556022a100742d84003040e01c001941d4450700107000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 732656456 1250 732655206 732655237
    0x1020d050c01180516080a0f0b040309170307021809030a110115060804060b0d020609040b030a0803270f06010522061517190b0d0f0309030213050f040201050906 71
    0x3e40c140000429403034840d01806000307010240d115161075503506200d460040040500d90400400709050740186500b15100c2d140c40340c86a5501d2030703e4030030742e00002d00e08061a040094144118a40320204000890342c3c0c101801c00d900d040784210361240583c00150041c0000f0103091680d5500a60155403400c00a55944840300c0c1c481d00d00512044003107034200d8405103000d210208602d4160a0441e00ba90700604482ca0000404107000c0907040701c02c205a0148180c1400b2000101140090f6200b0042009013901c802203400b000b250141460102089541016509558400340400c119066032015140742a132030406204a01415950b40f160322001450300e80003150000400341c892070300c09226654082e0640c1d50b2715100c0d40c0c620083e00c4610b104d0b5014806e5016541c10b58000e00350006004003416984a83c0c0d40700c213288410780b41e9003140005c10002c4c0034421458000000c0300e5080386840c04002501d08005160803440b800b9102a05001d0042141d103055507610048170001013090801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 732657706 1250 732656456 732656501
    0x1110090f031208130c090b062115190306050408040e0405010608060601140403120c120309032a020d170d0504060b060c0a060203100314060a050f0601020d050c01 71
    0x686601081c01d1140001d0030f020007250a1134024520204902e0f00844842c0d8564a4401000c00030100f000354207402c0302c8180440c0300aa04141c91200d023500c140c590002091400c10b041c042d105421400c441d100d204a1042d943d018103202c4030000a0f250b1042c00004c1702d45641c14002507500540c0e22500301890044100400c101064004000300e0b08800c00b00c4072a600d62900651758601c45a07a51140080140720410100c0c601d440703040f104002c182088070203140300f03444001c0c00e40300d010400b2010a454200301c804043d8071070f4000c030b5041c110f54945501c24103034224002c840c42c41e520b00070b0701c148145a0301c10140300350b1981d07a860581185560940c1c600e00da84841c006800201e0302a00c18500e00748118404d810006c08840c00d02c00c7c1e15001d0521a20b8540c3e90b0802504085c0400308000e250200200000b215a01450102c0070b680d401020a1714100159100f40c0340e0050a4000d10340c07907a01400701c47e0b600013460b4a0082c00605195840c3d03400e000e281801060074011802520510190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 732658956 1250 732657706 732657713
    0xd0302010b0306092113050301091406150604090207050c030d091403030703021f020f16110d050d0e060c070e01050901060806030a171c05010f050307031110090f03 72
    0x1019000200c02d8007a00c5495582409181c1ca03141d08014421514401c0844000300b48000780050448400c4d40454504054880020078211501110101c508407019650042e100d0402c01155a000c000f48140407141c0c0000004100e060181c0c0c46600106600802d900080080900450500c1080a011584400c2e010500204640054450344d40746040e904c8688099040100469110603050340045c58000e0300c00c00c4c41c2d15122415030bc5151700c40d0303081c840500a5454040146030740c0b843d54090000d80000c40c2018004056154111442070100c45c003118000b410106540480074014100b800361503051201182141c8909448000d5900030064041400b030301c09211503040c0c034019506581e0710780e2654410350b2050015181154150300c0340084000140ca1503030a00202088204001c0c01e025000408443c160b20240e03c0050154441c0018442e82180880f000020f000880080110514680700c00f2040116031088074083d031001e81d038200e2140d010300b89100007000410003580d181d80c1c3c0d905 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 732660206 1250 732658956 732658961
    0xf031d09090102030a0c02030304081b0f0109110111010911060306011403010f03050c0d110d0309030618151802270c18041a04091403040803040f080102031909020303090d030201 78
    0xe4680290501e801900c46d021840001982c5c481c0d54480030760b910340598a103400c2c2d000d100200d8078284912031420384000106081c01120140c501c511000c8114200f458009058241815060b01007a85040c007c0700202c0c03c1d000d0100c1041070145c2e1400e035a500c61000494079100100700015414900000004580750012a00d8003240c0c012025114402c0d01202040b4903139020120240443c00d41c40c0b01654680f414541a502c0c0c41d1003410300754000ca507a070355100183e40e11605410586c404d901c8409062082059210796180c8040c1e41c1003200341300d00b018890140c0d0644001a000d40c0d00000d42c0c20001ea000031501201e00e09039041c0400311300d07140a4540b041e511a0718081c40300f42c400c42e201c0744281468025600810021403141d50b05000d0745c0140401858040e80541d0090a00c1607800c2805200344020030203092020701565a450074455003800302d0520b0b03406001d560b8410010004010030200d4900401c0b10004c1c0081010505400080d2130f40c021001c0c0c1c564021080c2002200701a01517 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 732661456 1250 732660206 732660211
    0x40b0a0b100c0b0c03101a070c09150f23061620090103030f18030c0b04080111120103021003090503030705040302090609071b05160b040e010b03040f031d0909010203 73
    0x20000f02da8036a42d00148031800c0e002c162031101410b07083d84001e00640e9400c1d50302203544001030b8101030070404a52030b0502d18080c80d9110003111070366103807a100d00e21545400207014060300240008010300c2e00042c110002d0219004207040c0010108140c80c954a40e41200d41c002c80f20800c1c14402d1404d07040c03d030780f1041c0c03040104d80312504044070700301c042c140381110301d049039059119051905492141664101c542d4889010402508400400040d41520708400540031481c0350329181d50400102608503103081c1024104d922051242c0800010003000e901c4c1943d90517502100e40c1e1080450a4020348002000105540008000c01110a0b407280182c0300700e2f4021101401141c95080c00e020401105440110000e0242d0542c41e05402065900044070351140c0d040f46c244034a801000501d0b410650400b10b855000020700308005010580e1080c003600b0090b900501c1c5090076a21903401d1101c0a5005081c000346104c41410840c8542c1210362000d0b01400040741d80c501684654000d42c0b04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 732662706 1250 732661456 732661463
    0x20301060f020f0a0b06120d051b0106050a1a0f030c0901030b0616030305100b0c15010e0f073906050106052b2304050d080609040b0a0b100c 62
    0x882030003000758400680241019140301c0a070019685a44640c050010000d00c03107604504100021402d8a908100e0300d002c0c400e9580d6543d44130781d000b00482580d40300040f00c01180e603041c0b803006e0008d581c60640c842d04441034562000302e000c0c42d40c40c484106014003903100100d001d002c0100300d40650000014040113909907000c1111010341d00400085020310404c0c990550448004a000a800703a4807040d0010302029840440941e40c14296410780c0c04881160802c2c2c101103003c1070480d2200c6001070260444000301c0c040c40c07800028a400314ac5000740840204a1403600307059a030044010041d80c80c200601d88001c0c460358600c1203c0318403048a2027100c1040c64100001000c51245058a050304559001c49002c070707040c04407900600c1400c86003450403642d100d07800d48000341c2c502e101c0a01d5038084011400140b030b0074200310b810032007068202c03020b01680c1e130b040003080e5a54061301640701b40c3c4004004902d0710382e20303a01c1f4000d0031051042c0342c20030340301640b00c802143c0100070351624910 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 732663956 1250 732662706 732662717
    0x90819031413021309081b03160524071b0c030c0803031801060b040902130e101e0b12090f0601061d04020903030906030705130b09010809010b0a050d0807020406060302030106 77
    0x1544000e405c90340c24580241a0351014441c01d03896403100d5440404070701d098400c0b00e0402c0402d603c1400c0303075031407a0383c125465485042e094028030035840031040d190240280400451400340780240401460340701030b080030160401d0311000c0140c1c0d800031314003940c1c001c1401c00405480d00d010a0743c075801961030b20110206400b09903100d4105001d05000e4419890320705040a180c241c68501940022080b0510440c02c08404904901491001841440071745074810703034a4544866006100d01d000307007001d02468044028851614650100c030302c0c421803d203640080760fa854030440d0400c081d480c3c1001550041d00000900c040d882a03400c15440900c0c4070b86246e0040b0b600400080348900300c0c40c6509a0400d0001c1050381c509400607551100c501d0a01918006203482200f6154809401c5942070300000700b001c0c88103580c40034105500204ca00002c02040c8110400110114010f2143c14800d0801040907800c01113007000765880c1c030b0340c040e02c14000c090b00c80d60064065042401540001103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 732665206 1250 732663956 732663979
    0xf0f06090e0a0e01060b071e123b01120c0912060b030d0f0e030a050d110304270507170a0e0a06090507090c0f05070825050a110409081903141302 64
    0x3001c02c20069100e40e44440004800380d40509c00382c0349503480000c85050142624481c0565903e0400c0703d820310702d4040000b1520f00e07003420000d030122a51100090040b4a1f00c050490055027200b400020380c0c00c0c80102c1c0d0000c4c152880d0580142295495032605405468010b102d581d13040100407403c1991501c4201c03124006506055840c1c4030384801902647c13101400c1c10001e4011640510702e9421141500e10b0180c4490405102a502c3c1e58030001d000c01c40c10704481d0510480c45219007003805803a01000d90320400741d032000d064802614041a5039030ba24070340c284125040003610402c80d403180d014400500c140c203085441d820340b80b0402c0d43c254208420704888512070b21503213140f01696200d031410310b040703038443d106190440320880d0906010a00c0d4000c1c050780c40d0680c40c003e5482440207281c0c2401514250740d5401000d01110300590901802400090b0103406484400d0100100042e0400f0035000442c098002201168402d02d40f00082c0b0100c8008188035907181c074000c1d2114024003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 732666456 1250 732665206 732665243
    0x10c0311090a09020703031d0601080d14091e1e10030608060a0b1903060c03060f05130203040c0302120f12122d07090f0f06090e0a0e01060b07 63
    0x92203804041d070340c00607840702c040c40744403865800740244a019250000b4030215613201801041800c4160001070b83c040d100400c40303507404102c0440d00f20311034501003001c030407404403581c1507015070b440711441490700c2d07a9602a0101d000c4a0141e608000901040b00c034202154650b44031485003014030301465800704038040290103400303482c040325058401802140d03204040704004010380070750140c1c07005024420308403010130560030303c001e18007c040000310411440c8024003290030961040c0c41c145034140d8104020703901c0c0c1103810600307801e11002582e079958502c2e1480d0a8160754100035804246501c0c5c14a400d000000c094244010510031204048000c01a148041c090b60b006520001c10310000215040c3c001d407802007981401020b22170020f00207841c10b42030303804112903040000310400e008024402c0801c007690020501207130628110b50a210004244241d14015821b4180344c0c90045042c800b600c0d44209d20b0003c0b80b07402000060345a0094000c541d01142d01a03070710107201d071294000e9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 732667706 1250 732666456 732666491
    0x1b0c09020a090e040525030812090c011805060d0e0102030403050a020d0801140f0310091407140315060607060204030501051e0f061005070206041202030f03120c0702060c0f010c03 79
    0x90303411000400b400f14540c0c1115408069403036860300700350006c0d030000001130001c2003c0c141d09558568444c44070b180c4009010702d455040e80400381048a104000350f0744814006104064840541e052a80c4500e650f107220040c09490003c0b448540c030000030041496409005001456203e82c00c3c0c07804180003500854403040c00f0b0084103001c1aa81901c12654500710a1180b8a188054283c0380c01000d5091054111425000c0690720200f0884c07002a81c08014021507028001c420369071041410140c000c0380e5034080d541c0048050b85c40b11400705010340d680000b1f450704260300103c1591384945a1501034080d000566000384c0a60070960502c0000d03003006025031150084420300385566841c24200007030000c0000305c00b000c1c040108030080150311071500030006000392003071b200301e20b806500c1854502100c641c1355442540052268680e0329151500b07064200c0450781000c1d88a4256000041852241603a4503006104843c100c100320710701034101001701172440d1002c00c4142e98503481d0120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 732668956 1250 732667706 732667711
    0x30b1f050103150509040b0405010506030a110d02041b050a0806220f0213090204050f040207030206070804051005011706180c1c02060703090305010e0d08071b0c09020a090e 76
    0x4601441581400a075200c0e910a0301016099401c25020070303690030100318010429038013650344000136003c2100784082402040d4124900768020502c0180c9038a8007c0101648288603100b511410300800070740d80e440d081060042c0c049840c0c44c41800c005c01c40039140340d00546180f0b011608001c00900c0131f19101d04002d03005c1e144002d1180c8540c01c2c0e00800e03402404c0040000030510f600340701e07110030096110009405011084030044e0303a00d0404040013486125559418411801001298000381d0b001c140c150300900a810a42da107038075a407400328100301030f044c480701c000c51501000007089554070f298204019201c01c19154641c0310144030f92040703100d01da000c1041d07a001e01041561814210710a50840e924001d41600188096002560581c08044140c000a100300c07014811b00c5402c3c40b8030740c8103140150050002803a424005001035400808210078000c8400501e00e401c00100031055a05900120308030801f038682201c81c0080d04001011000503504000121f1790420102c032550 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 732670206 1250 732668956 732669001
    0xa20010f02191e35190e070b19020c0301150320091b0c0d020a0210090e010b03040201030f1d07290c12040f030b0f040308041203090516030b 62
    0x4003901030315841d480c8144078008503400c02002e0014079038103002c11384004a0180a507000c03044850311406005c00213030350174428101000d030001d040070000504000c04035150280103a000c90410044010180d06001c590240c050305075003000005d6429110384501340f070a5a00c2007444090240c0c0d01c40c12001880ca0524a0079081180b80e0041404000c41c0441c0440650007145220f2801100b07070f640034141084005600c4c0075900020740d40f0f04501d445000c40c00c041c103041c5060b91032603107401141185400184142246924000042401c1d64840d40010360002460041445400d40c850010400e000c0903002c143d445010712000880c81501c46408a0009a882f20040003007503400507403800250300500810506200e04050050740380c0900000e03000034103031440c6110303019241d41012101c444004000d00912510f0b14100800a50000d500e02d030055044000110b92100c0c1d402c00380c0090440ca1009841c82c454440d0422550b8110703010141942d10945104000c1e445000002d0440710300b114112 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 732671456 1250 732670206 732670217
    0x2d0315090c14090301200c2107060b18040b06030105070f050d050c040f151b031e09081203090c030706090311010c0812060301060b0a20010f02191e 65
    0x1168420192a0724800240000342011a00c8014440e40d00c0706d9410714080f09000c40e102c00b80000610540b01c40303007140d50010f19600d4405204000314414040020700c40b0365501105812a112842c03c4e6400800104a14030182001d04001d443c0f60000c4a1f014442e60030a0000380c00749103e50302e421103544180d2602030610004000010141030020150100c1d050705200020321039032010000801050414100382a000310355600506070003905080e401c02d0341d0046408000264071549908016199510b065104941c150301102c1020b03495101c070241e4401d0817850140282220300450003003103000c0c1190382c84030b0448181a2101c540d4442c0c1c4000c00c1a425041000c83c861000c0c0c0018480145800a03060340e40e07503104011600f0003104440040b018804011050400744100340c058029140700d44c0c14410014001400034200c09001041062207011385c21107003801750448100c0c1c4054036415034480042ea04280700e110f02e001e000e600042c040c10160070070b006005802d85031f105c210342e07a01c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 732672706 1250 732671456 732671477
    0xc030d050906070204090809060f2206050a0503062d091f06050a03020903011d0c0301200a02070305030703030c1403010303020c0d15062402030f0a2d0315090c 70
    0xb004010100d82e1020340fa000c0b010410040c0559924009112012100014ac0d4952006001e80100e880380d021960b40d604607501018002a41c016054441106891074040d0384d0b5580c1c640420b26103540350074081c403c525200d1030a00c0900f102e02c0010603d40c0141d03200c1406940d40c0f25819200780203030b14407203410109110700740041d503c100000e004d25459410050700c0c2610b2100440c3c2100e0880e500451104040100c007044014244408801000220001d100505018550000c100041c5801000c030120004040d021503000340034080065400900756a20341c0e2050030081c0280c00380070f40c40f20006c1d80c503455019181c0f0300d00c0143d905903600341d0300410307010540e881407000c54500501c2c2a1b0701c0000b8203003080160129400340c0c0780582410b1004003158030060400b107200d07400210500b0700f55041804405980c0405000f5543c11109526100d9100c802c0e03406002204000080c00d031901e10701003003016035480c0e0550000606d040c205129405110ba442000d001283d60302400c21000502e039500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 732673956 1250 732672706 732672709
    0x91109061603090e090c04180210111501030b0f07050703090614090303031e0a090b1f150201060f09051e04142a0301060501020a171201080c030d0509060702 69
    0x4005070307aa119007807158800d9100c0042e85480902100d00c0b0900c0c0c1e01409100e10f01d400c281c050a1221220f8201d0202c40052076030015240c0030404072110104120360b1002000380400b041a041400d020000f56000c1d96107900b08001001d40c2210b80b80c0034640001e0100b48142d1145044a5009415581f280c050f0b5080003003ca45280c1d00c800103942101c0709008035800e56400344000e41c0252808000420b140724141d1210000745d00050540d05d01d20320f0000d9810101300f507032803800d0380036001403854030018414900d64031020000d50000220200a180d281101c42e805612a41c281d605404610800b80c1d580c10840080d280116601c0388590300c0d03201700c817420114455840e6007243c4103006501109440116003403400d0900b0003c1040592540d0703d40e00a0545404070b5540c00f60198020f06c030281c00c140c0040c0d0749070140c2c14020075100d10402c00c4038290482d50191411450701c000c3c44452965601038442ea2041041c0303c0307030710900a41240e2104603000d01d0440b541d100f000352075a801c0512580 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 732675206 1250 732673956 732673987
    0x5040305070e0c1b0d09060302040b0d0b03010e011b1e2708240a060b042303120d050a1a12010609050106050c15241807080109110906 59
    0x914803280280103202c0300c200101e6140d180d013556a0b4a2004160707000505400400c0d40c2460340c411801d06104100622001040c50219650003424420200f00c0c0010200030034010f100c3d102018940d035280580c1005050065008480f207018180d40701124680603072800312100604c01006000320b0b010010030210032561200a0358441e503010020070820781e0b2148050300304484c1c0c10b100d8040c940b4207c0741910201060404a8020901003c10440c080c2009003004d014400e07070003100c10303211010908402c2e4500020006440f40400703419618807881c1c1c0a200b0707a20f40c0203500e00002c02410070000800e14601c031b101d0303002c01c1030840741c0340d00302e414400082c4000d40150794120300d6555203400002c12070350724a0144500901207696565034550880340142c0c20300703103010006900c0c41111804d10402c40851108010f0000180d4905401c041da0580002c6039907401c0f006500c1409540d1080181d0f17240c1261005040b102070325002d01c98590324480c0c0d00d12138415031f00d030250f10000912280e018080d128 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 732676456 1250 732675206 732675211
    0x9050f1303050712020c03120c0d140f040e040209090313031202010f060f031406090c0f040209041b0912030801090917070804050a0504050c090d110d080c060705040305070e 76
    0xa090103440c2c00100c2d22012440490100021301585c00412541602e0600700400300750b06090307210f06410020f032030303010541315072190040e8020844022906081e240f80b04040760500a0600143c170f550b02e0340c88101d0302201c1400c0300d0580c4206150000520a10008811180b1481443c040d0701c010600f0355551404030040402984d0466580300c0c0c800501040502c1000040d00404d0b032205243c03440d5140a04a0142c0100100040d41002003484484c1a00081c0000c60b00021a140381444090401040007801801030300c1d0307445401c00d0b070301710f40d070195840a01400c02142d955800ca0940c86030105842c0130000c160007000070b01e00740010007210b6442d904c1009224481c02d03e19813130001c0c201000b207964100910561300c0480001d810032082c40d01d6060a0010602940c0600040c5000c5515800c640910840240248070011100d4104081240b94007000070f0018203c83c6000e80c43d0a2a4803a50010b0001e46801d206400110701243d0040c41503130f00b202d501600030018581020704401690320003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 732677706 1250 732676456 732676463
    0x110105041809060219110f0a080409093e0a0510120603062301090605010c0201030b12060c0409060e01083a030e06070305061e01020a0605150a09050f13 67
    0x90105c12040c81d5a0050754000415030307903ea0f4590321903c200d543c10011084400396003a4000440c00e00000c140100340c40894907405070015109c1d126041c01d03107911084100300d0f000c4200074188484005c019009a0315040c3d242490382d5844010401070121805040c000c86601201310000d00b801d6510905024180c000b0003800800e6180e902e545400c08e55944565815402d40c44c00961906030260303011242c01010010700910400d4076290020305172848454010b810551104c1d0440381980304d9455110300002d210045400a00d0001030043c05600f00d030164659031400d00c200054050902100c0d141a1151340000d0f0080103c0e10003510107002c3e0403218a6520194085025242c64411036000c0c40c0c03021b5034502180d0041c1c0c00d18840d041150081030f5000349450442849001d481d500426102d400488c00e926554004003070050346010610440104060309003000c1006c9441000510b5030f0750b41e001d840700e800c003c1d1501804400e445048815014000800c00000d480c01d08005884100e00d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 732678956 1250 732677706 732677711
    0x3120c05070606030302060f070810030206031f0f080106060309020907050306210d12050f07032c01020d0b0643050105070f020f03040b1e041211010504180906 70
    0xd0ba10901940c0d40d941c800e40260308414200a0202810000785610241c1498000c1483c030349444051790003e00f40c000603000700780110003e03420290400c0c4015415900394004003025030342c0d1101d490020b2031400707902030035400c2110004216001e80104002c1c00d0f80100810050768071200116016000100820351081100c8200c613403403140d101c862804505860042e01101004010152408c10000d00c1c00e005d15182604024408586564103500001585000700d00424142c841e0000d03008040440f10300202e030036403000044841580100110034881c9810310855140740304003d2540a1110f00c0222000d0350300342d5003e11a8001018031407408008084543d440c0301c4100751489404001c01260390b42e65600500400c541c0000d0240c40c0c4900e541f000780312405071003985648a010718840d8185080004c01d190b11009102c41845e2500c50221600e00d4985a07501000c1295030074200c02912009001d942e0002a13511440484050f90700307214507100340e0000250213000400d005c000030303a225076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 732680206 1250 732678956 732678967
    0x60f040e100f08010218090c07140c0307120b1f06030c02010212041a15131d03031603060501021903122705010609090f0210050c0a0b0a1803120c05 65
    0xb07a84000380720141031607100068a42074202d012a605a000140c1c0c60701ca905402c0801404000760303811500303a952702010f5a03007801200f00709a85003c3c400e80450794140658400032035066a5100e002e0220750103180350381c0064075034161040070342e001c04080d40361280c1480000d2181c28001c1c0c22070401420548001440d0034000d1036200c1100703c0c20b96003201d000e95902c0c19207560521000442d90403110754072402c85140301c2540000d40c5600c0480d0301c1204035490741600b88148600c10b80301a186144001980d640c0c1ca403009000103c0720f6603030704a070041380c035000001c9425480001c1c120000f0344444c08088848525890035a45a500c5001800c1c074070f6104c0708920442c0d081202044401c800849401006001d00d1401da425079440d0b402031510300d481c00c40301e0300210f03400c2d000302e003681c4c1c0d0181c8811601d41a24074044519120300c0300c0304100c5101d0644ca0740c0806c0401114944646074020703040019a1511000808040d440c9a024000417040327a800700c1c2100c0250710042001c04281003461410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 732681456 1250 732680206 732680219
    0x40e06280501120f1a0c0703020c010801050105031b070b090109020a0e09070603050411040c020d1d131d0f1e0a02101202130e041b03080d051b1801020705060f040e10 73
    0x301780869450885803000700d400c1040680402107018010f600b401c20203655810030000810901000341620519095010b0a0b4442140c140848801d41e40281d10514589003da40039400780038014012405881659030001ea224040d0070000d0140c1404009098910b1901c0e5080b0040c00c2c014200f914030300004580320b591a0707107500c00d1304600308481e00900101b85c1504401f410301c1c4401c14802a2030b5840c420503604c00d40e240758640c031040811450018464100f04000103a55900800050b80b500c142c6212403401c0400240b00d01400280400e4001c641c2c0c801c01c1b140b038441c003510390000c2d082002202401ca000340036080c00e030340e40760310401c2c01030078009800c410a80108440d407004901c10208006c0c8414003801c040c0300f201d403080700608404140d180d9514000e81c2e10a040c407400300a5074400100e800e49040d102200303000045108125100e0104400074404100181042400342c45000000900c42c2010400d50b890350111200160030145040e140313040900c0014241c441d001240341010620 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 732682706 1250 732681456 732681503
    0x70804030807052104060c11070909050319030b1c030e01230d020c0c060715050a060e090102090109080606030c040e0304030b040b090c190b09040e06280501120f 71
    0x10f038045030701388214034203160030044e0407909180c00c100100b00c2071100030440110300044590131208010800181070030981001d40c210300548007000780060347c1140c14404944c0c1070f0481c01e01040c00326448031200c00c0c0c0340145480c080070f0f200000c000c160300107241103075980240f00d084001c0f8403544416880307210071442035400c3c2d40725812090740396a001c80c202007006010414009120b00a543c80d0385004c642c2d4541d241130070100d90300c011040f6110400136a02c903060703402c110010000c0c14100c8010782000b5050074040c0d0007881c10140001c00500000480c1c4000003119401400c024010308425a0100300740310160904000428191008100c0000021a130840c0d90348224082c42000b54642019100300c0d08064184030460b1140ba031002e940390308800100800412919094a00781e901c01c0c0c5640868007400d40446a80d4050094208200f900c0000c0d091100e08c2071075150402070070348540140201110710a000d101d041d401d0910341000014580c070000c02d029401401011040303184511602e01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 732683956 1250 732682706 732682747
    0xc0b041520191a0f0415020c060a2f031303110303100303110609060a0c0e031507030606080c2a030a0e0108162102070501020408012307080403080705 66
    0x607689201c0e0b280b03014840c0e06210103042c000c0304402d0900505114140f201d40d00809040540703007505071346500c201e0654650464417445000e80c140c40d513070b2600c1107034a80144200310380008481114501036003154200b60000d1900700040b01c0f8241103403200090358601da14080710071007e2001e10400614800c3c010805035110754156403a40b002e607401e600c0c000700325803050402011181d01c45414088002408284035500c1120140c00003010501c4200864402420820858040c005d405140161440c0011b100d80310360900d48043c046583d5074081107a00b84800c407004c501400c0280490001500a018800702004412203015079450300d00c0701650569011161201c04244404102c2000b542c00c00714507039000341d400d0107226008000d41c07406030122008070f202281000000d62840f44030b14840d81650070340c81e00311000715100d68a80407218000e1010710040311032a0105400004031144e4280107030b10825081c0d81d007140c1034450359400e507000d050180c5481d045c04020300c03444980b00f4070005c5d08078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 732685206 1250 732683956 732683983
    0x503070f0503010c02061501231204140c01140a0e0a0b0301090c1d09040302250f09090302030a080a0617011d0303011203051b01020a09030c0b041520 66
    0x3500d240340008050841c0c494420f060b0540d00b040742008401c0c00d500b4058040301d002800c12a010f081c0e141e1b40f00b002803405441201c400003002c50104001e0f035a00128602c610301c901a5a42c1c114602080d003581d45800701d01c1c0e240069440c0ca0000402080c0d01d000c1c100c25945810445420145400010700c0c1303107019002407030f1589001c401002640800d000f030400d01d001504142240b01807071940034108044044885001c1e203d03880103d400c1610801540d040214003844803d00380b000180c601c04031365481d21907c80605803c103008100042c50f441038072140765054009502c0c14281c402d09481c032010041032450403603650300000810205509605892014020000400c2d03882c658641c1969015422601d09603402400184507500305034100d0450b140d01410030301e4444032a04004d5038501d840200c0a00c503540041a1143c180b90000f0805043d01c1c89040161143c175111056544a80030310700c60a0008100071107540c810381d000c0e800c8000d052009107400a0011610313550341d07181003144514030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 732686456 1250 732685206 732685229
    0x30a2006160c15051b07090c0e04230420040c0e180103051209060904090c08060a0903020304090b0301020d0c2012030105100512070513060503060d080c07050307 71
    0x404011455078082c02070400c45038950300040300c00d14001e06501540c14568410b0701c403800e071800011810010080107000e1043d0501030072500c0007000709030b0588900d03564010340c18600d40150000f10348450080083d4a42e040c101c0f00c1d91951a0b08040418455040c5400d10700313841a50503946490040b072900e542c10b9260b54408441102c1440000400d01c0d5290a070001070a0042c4000703040403540e00e44088902c901141c40d4140000014030720301c140e41803668098035154581e002c00c0b890415031011298240c081e00c00c00e40c0c8a0002006032071482074000d0058100b00014000c02d0071170703406085801340c041c0005050100652010003201c41c9210700701c01048210742030549103035441c025148030000b00d0025190607050042e5001d481e0006028543c40b84044888101019105005880f00701c0f004940841c0c55007080c4401034059031003403852400d1044500c40100300907020340c080301e005901c00782c400580c401150700c40980c1d9410107904500b0a00640400240640e0300700200b402400c0c9101e0503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 732687706 1250 732686456 732686497
    0x9030b0109090b0c0913050c2203020406051801030b040c090203090714060f1603050c0a030c0203150405150606041509090606021c030e03040b0403200f030a2006 71
    0x3c1511420007031912100078420450398801e03880f940900d40072094a8440401e491311101340d076045a02403491745064144400072420020f9980440e80021070f03001391b508210b0303907417541d00340f01b1040018074480040714000c00040000510030300015078004d0103041380c4462541c03908214820f0713a000351502107041d44040070600031500f004291b03501180e82220410f16001c00d01501800e10b008041c6018404000390303c6400506014000301c5900b150504140c0f00009c41030319000d090050b80d80700a9009104000071350b20410b140ea9607060007180c0242c010304c2c4280200e5800000304000410781600a44103120014440f04140e40d011074150107900c0b20001c942c10715440004a03052a03010000315401440d0301d042c02e03017800c0b501141e007030f110345404900303100e0041d00249580b00e164013209020000090010502c02503101c0c013981c01c0190074a0b000d18100b00c2d0b0803c408041c0811004d039045d0001c00c0490000749060000710145802426a00c0c01e80b074120000880a40245100c203207c6074100c0035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 732688956 1250 732687706 732687713
    0x501021206060c070306050a1b0203041a030f0105060901030e10090218040b1909080d0b18010b03190b15072303090609040905010f1b030204080a080a09030b010909 72
    0x10080c1d11400035220346003400c2000a04607a40d00d010300c4054251603440020401c103611940040120600f12010303c3c1850540c100000e41da940984500c2030800301040f030305481c090761401180d00620782e04280480c10b90a10040041076880740c502c0300c0c1415502c07540c0540304002842200740010007814001110b01c582e00600c0503c8460b82c074160705c1416103404000c0040d140c2c1020075000340c80309901c84414490b02c80303200010020b02c00085c0c80c4990101d1048001ca989402c0304030f94075070580d22030b003809845090b020081c880038058002558410b2000480f04400046000c040c1c00403881c01181e18142800442d42030810b5882069400800044010521400005000d800e84041550800031905c141c0c0c0c554423402103035000fa21440000480318195035a58010724001c0e034010008210540c0c088048400905446041d00780000303299001c104d80380c3c020b10a407811180000060001c110306a950030410340d00208140c000e1105035200071012595107003546018268419000840525505 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 732690206 1250 732688956 732688987
    0xa090501020a050601060819060902030a06080118030e04200405010311040f050105030c1b250608060906061b0f0c0f030a02130e1204031104060b1209010f0207050102 73
    0x40240303040d50701580e81800025000030703003d411512207203003400080d25260210202c003070321025040400b9003002c40220380016a07034000c50245450500c104501030340c1e414244c4c2602d10f822107254a102c1d0700701d511000300c2c1c0036050101c5074820080c40041c030b9041809105001d0821011110121240400c0c14060340d6014801d424a220f41315042d6802c0c03500d03008140220f9000350003880c1c100040803000c104200040020b9840b680c44007126603000b03411030000300e03540700c03d05046c02c40b031080ca40000440c0e103081e42c0c001c541525602d42d10444d55991b41410300c0141c8401030034070340d080340d010002045400c0e05103641e40c2d400c150312030180404516407a2618078243e0040382c290f1142d044900902c070f036982c1c00201d0140c050b60542d409103e0315200714241f0002c09425140161034002c1031344040d1500501402081940d200b8004070503260f502c1010300c030840c2e006004141c00080200108209826006040e0f41c0c0030390f88030004244d0700c89410f00641a40c110100441e2543e402080681e038140015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 732691456 1250 732690206 732690209
    0x5070f0b190c020310020d0c020606010504061d030f01020c15101404241508010b09090415060f170d0f050307110703021f0206011a0901030e1009080a09 67
    0x40c034403030902001051582403058100400c00c184004041c00b141152010300460506a00c042030440d22004198054000350660040f513030018011780c00050025030240c002d450a541e200c0c0c1d503420a51751a450310350742045824603103070303403521a0000342e9003101c00c240018444661000301900e1001803001102c2b0405001030300e86806100c0c50381c0b0038041c40c0702c50201820700ca00100ca0110300b1404804c7d0300b4864420010002107102010000812400d07040c41d00000060701c25520412203030380e15000b0b10341c03500840d00103ea00140313080118020640801aa60000141d52000110307941e4034040030188010941c4040c0f01d03191300c0d5030480d0080b10705019022685d07007a07003825450b03060b01e41c600a040c0c2c07000500038024050140078450600301c0030002803010b55400340840e4249034580d045200242410140c05006100b40300012404804100300c8d190690360f0b0450719401c1401c1d090055001d4031072250051075611a00c0c03031504420b0303080d010700a03103640251350031661042008030003042282035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 732692706 1250 732691456 732691469
    0x12120f03060b030a1d12030621250e4008130305070b07060b0d240f0203040309050102160e0c1605120a03180f0b15030a05070f 56
    0x200001008154040003c0b40d80c0000750040008040d620000d01c810801c01110380c49020348111000d5a900c11910f000442c0141c0e4111400c55205803040d100040724030090314002410342000e00300c103081d24071014400c00d102584100a21920703844400d82c0d0151202110312516005d0034400c00c440c5958000101049110390004a130f901d9101801407043c1d0000540009000c403400160020300c800351038000074042c60703001c800e4070109075450380031085036041481e040da48149480340141861800e89624828264080403007601c0d2032041075040264451a402d2400640e1200c6007078074001120710085100e41d100c0d03211804081c0c10480024034002e184018030042400b6400706100c2c140c036814006600003c1c480030720741ea5003a000380384910700c10700120080c441e1007000c91500c0030810b090044d00680038a540c0070840950511940c20100d512190040c1640400c410b144020540d40049180c3c42111004038000c000310324004030381341000c1d0b01c2080c0d03515001142d0074401e0400c04003582004064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 732693956 1250 732692706 732692711
    0xf030a0c08012c090309040905030304020901150f030203061f0809100c0c0f0f0c03032006160804020f1002010f0506041a0108131a04060c0c05101512120f03 69
    0x121a048041100c00b075800007420180f0312000544c031000704004495007010087c01c1808101d14501d45641d1b40c1e041036130201c1c4120000000442c59115440300c0c0e0520300056601c9800c0e403090070606400075440130702055000001807408800d400200c1c1c211401003640740d40d80036003c3c600405594200003000d2480c2000a04081004180540c00411404020381007142008002e2742e0785009211a242c40760020100c0c0c0c0000380000606402c00142400c585c02c001400c001c02040c41c0210341c0b114002c0303403000304410044a407000b4140c4a51115580b080c030250900d640c4011983c002190f02140640e1040140e440714504000303c50280074094025400303990034405060240e81201c40300325201c1602c1c0c1000600c000060380001081d0920021f540c0000d000500701840107035060049800b1901070315158100310032504c05910a0100c004056000000303040003402001c0d055015113192100545400c42e01d000c0420385d00d640d1010f52082922884540c290342034454005800d60200c01c034040241031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 732695206 1250 732693956 732693989
    0x3151c0b060406150509010201060305060c040f090b01050d020f07140616080108060a0c171317070b040b060d060509010902032503120306150c03080a02160807080f030a0c0801 77
    0x4950031314400c1c1c100d0404546030b00608004038014a000c0c3c0c40502940300740e506001c40f080e0743e60b000341300b0348010340c1440240c16140c1c45410b0175100d94030030b500c0c005a401c011850a03120203034081e060541541c06014604412030f2100c20400c15641a021500c0c0c0250050000b01e00075010010340781c0809003040422580f404195a0701c5141c02000e5064181c0c03643e0392400c8240c40380400c14001c40340180382e03070554200140c1100c00c1c00b0f0341540446025401c1035422403000080c1c402da0b0300341503000524136019500c960707420030880c0003c3c0000b50400c24000440300007401030300902c0d00c224840400000c8401e514010140b421110303020140b4001038a00201e80244d0155144074107494005403010307030303900d80c1d140c044000380303a1640030a09003100c0c861070304030b000c0e40a03240e0500c00340696035231089074854401000c02c81c82180c800d1298013009040c1c1d40c0c0020202009496024040c41c2e8150600d8030f25524010564021100c0761072031540c40f2a50b0058982007081c0c503004d070010280900e07502c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 732696456 1250 732695206 732695219
    0xc01053f0109090f06020306281508011202100e0d14060708010303050d0b031606020d030f050601020a11040b04090f03020f0c0a030b04111f02100e0705010503151c0b060406 76
    0xe480c80c40050100342c6c0000c001130880c0c40340600360040c4489a80da030750301d4044000348088011214081c004500090460000249200e68001816280c0f005041001122260b080091740102d081d0710320140003014200351180e0703441c019410b20701e501407410442000c1c501e044440c1004030052116080c000b0759070040c000309030712206450f24486941e000082a100344030000f45001c014004107030b40000c0000000c141290302140004522150741c600303000481d0041b140d40cac01d0f1030084640c6c1380142d00510381840890402030040070f4001006c1e000044c08007152010400f525030124055139294000405802010743c100483c51000550748064142c03e4400e10005d291081c2d10b01c000760052000301e010406010344991000c140c13801c01002c0e6582060380700c07610100e0b005a00c0e0803c02601510201e104004c0c42070288040f1000d851018044041c18400103481c0340d04082c02c10400441e9001600c3c80baa100c01c400d84000b13154800351441e0955481c900b0003c0508028007260166080c4102003001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 732697706 1250 732696456 732696473
    0x70308130306110c0d05210103060b0f0a050f06071a070f0f0c0f1112011b02160f09111c0b0a06031e0c050c071202030f07080c01053f010909 62
    0x40e030043d460007a6a800201c01f0340c003211101100c0c08611810746c00700020411400d5441b01c0c0c125036003540d07049030742c0c2d00761810008050702600c1426040079200c43c1c1d4a5071460030a00500304a8414107000398620508030047c054084200c90f410b010400b1141c4541c201c0d41c020101c030150359058a41620002500d80d01d103000482003010003404035001d440000d210f035803034010071048039161034020020042019014046021741c41c175410003600076841d0050707850318600340d1301c82914005043c1c10216458003c0c0b80005107000da205502611003406048907503094040500c6c4841c505076004101c0c10628403c001040030079038010801d0504d03203480f00190f556415800d4100046c0c4200005a00500c05019035140c411140421014000c40c0f0300401c03006280280b603080301e8001c0c0c1c1107612000d088907015607580380c0350003000b9190f880008841065072140008181c3d10314802641c0c80c5080f07030b5102202001c4c14003541e8050160b204640b0040083e80c3e0a889401014250700034003a0000c2521684130 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 732698956 1250 732697706 732697723
    0x3110610090f0207021009170307030e0f040b06040320060304031b020f0a0b040e13020d060e030405041a010305220b1b07240c1d03070308130306110c 66
    0x410340b9401c40310b00b2040641e050301d01168019008400e5200300c050000c02e603240714043d9881c1400c4550350710480040010550348915819100c030111450032008200050a0043c503840c0d000d40c464007404565112070300030708010342c802c00c480244507004117920307540140014600c5000b03110900030000800e501000b02c070492107100103007246c10b031a07900210f00c111103d213070210b40181446d0300002d14500014020000c88600680303101d002d80360300c20f0010200ca11140044d5104982000800105460f6407068107104540400c1303e00d400e5403000440c003664145c1034002d007106840aa0400c00d940c040c011b042e4011007040c0d142c000c03443c2050110080c1090030700d001d40002d0300c0030005030340e030103245446001000304440c415458020340c5ca000d6007098501c00000d607440350842003400d0580d01d6401803080c82c80c01900da58000c00a59040761220b4900b04e5002075040c8900003001001c50500b0004001c0303607441003030081708541103041407415500c0150103440d02d004104070085158a01107a60384 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 732700206 1250 732698956 732698969
    0x41e030507080705120c15060f0a150c0f200901082104081e070e01050609060a02100518150f06060c07080105070f1710180f051303110610 61
    0x1e440f030b409800c00d54034003011022012505200051252001d50000441c0804030040000103607a03a6141c00600c094203032101c40d00c0381c00c000c81078814032490402400030151013511f031400b90b03c2e40c0c02545810514148280c0251002000f9103d021081d507070018001c5031031941580ca21580d5490019002c2d40c891511165905902010440701c6503a502c2c5e8084800600c0c0450440e0a00340055855490800c0a409004210300c190200080c6154041d01100d0482c1c1008080f00d050a41c0201071040a5114104e50070450180d500c4a80940010f031003010301520382c071050702c6254600545864900454540d6400301c00c01040b04001700030b100020344641c411019071b403040d160000e0b8604189401d040f034102480039401c0c40c1c1000012548148540400001552080190b107022a22070390b00d400103032a400c2c0c0ca601030080c10300030300e40003080d0b440c1482e824260000340802440030b44006c84105030380c602c07940351900b903440052540c080e220b030501c88450409000751b801d10042e030141c1a41c840c4a8007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 732701456 1250 732700206 732700223
    0xa0b191209050303161b12032007060e0106080102131202150a02010f0b0a2103180609080606090609010e0a02190e030d0311070305070807060c08041e030507 69
    0x4810180d4280c12124060364050101c94880c01c3c4413007810300c40f44e5081c0021000524034131810940d6146400d00d80f00e080d03080300003c00202e240d11011400b4100d01e2500400c10640c01044400c1c0f110090020a2030070300600001860400780500542503901c16070015000e6801840b40114408084496400300c0300b40062081083c2198404a103003031040910300b00d0a55404200d141801e501034125002c2071040320700410020306081c0410000c000c650084018113500c1e030982a500c0c880c2d407034480340003900900344452841d542030210320500c0c0d140e8102d100055040c0c0c1013003202b4201000301d20b4014608546000c41c3e850004040703220000148070341000f0301c007200042100c100d002c0d0304864902c0540445404c102851040150801c00c0400002c0c2c040e04c40e17800002d801901c00d10485516032040d42e80e452810917251421200358100302d009503507488041242000040d030a110f020429107540d15044850310f010705081035100d00d00d41c83d0b40508404141d000d00020380c0101101c0c1c440342e200c01c41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 732702706 1250 732701456 732701477
    0x402070c08030f0406031503080d0203090709020a020c01090e0108060402060a050906040e0103140d0806060912190b010b0903060105040e0a0b0c1b070e01060302070f0606140a0b19 79
    0x1803621901a0380020340324080003c000d01007492034802402680d1300d85e101485194040d40e164441c45007580b10150558005000300c4060242c2074005642180d2950700300e4441c3c503101c210755000c0340d11100c4500702590102941d40340d19600040310710b00500c1c0751901c8480d25032518005545800e0000c10003481101c0000ea000c00c1d45008409032814071002904079030300c0f2622a10f6240c1565001c1c0070603111000b00f1441c25030b40303840014014a0200403559024810b845070000e1210542001e20070782e50040b880007844540402c2003040d9001a0154154022030b12090b08003403901300d4060f0001c4e525a80100004500c03a00c00054050445000395400102e4030041d547c9181082c1100c0001000110000e060005621045029146580e284026541e01080f4100038940e141c00a00c502a84048968010017195000b540504202c41c000d8081c0b5108000d01d03560360040b10b003960000c01403006040d403140001d0511144441c0a010400305c0680360903520000300019144192884007040b002c60700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 732703956 1250 732702706 732702713
    0x80c12030d06091e0b0a09150504020d05010608161d010306030609050601150e0d0f060618050405150150030f0d05071515091406041a040207 62
    0x200d60307044145010411005445155a10252600c04000e5034500d070140c1d064402560b4900c40c5c0320340c1e400020f01114509140490315005444083e00441d802c00c411f400c00034543e1154002040e110b081040001101d43c1402405092440003925076100c0c820b1100c80c40784255081154050742100700e110407048800318100490140c0140e41004040342c0c20503c81004000c800600d0f5416612000700d88040144100400c039108450101c4841d4000c2c020320701e803c0031071072035140c07820702a00a04d008030705107071151140841118100c1049a2a9a0396410041071020a1007080c120341d03002859403906500d800800400291483d0741080c6851000d034184210301c02c24001d11515641c2ca11076544c1c09541c0b08404158509001a124040d004030307101000c1d0203c0c081542c2549030f800e0b85806040000036195511004118040705010650308c49030b80300e540344450300c200b00500552102085910022131800780103a0098500b602560a001092401c2c00214503407006410041d100162584c0081c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 732705206 1250 732703956 732703963
    0x10030206040614090d08120f0c0403030305180a0308010e060105070b061905150a0e03030306101d09010f030203010e0d0f03020a0c0f06050603070b071a0403110d02031c06080c12 78
    0x440e040e480403170001d07160108004c19002e0582001006210501c0d83d4840d02d090462030700848444203151800c1200380006070080d0310850f007016400b00c5540c01c0f5010b00040915001c020803043e40421aa1401000110100c048a075401102071902c1803d00804e07a8980102c032401500c403e2162078002c105528400c0f481d0710b1f420041500a0000b4400c241810006940f076105031800c600081c907440c10b02c903403802cac004101d90080002a190030032140702c11604403081301c420700300000480401c1140e11b078960348000f241f030701800820081e11000d41c03442c4101421038403168441c00300c0ea00510500000c803034020b0b0160f1a03005540c20051394940103448102c4800018843c020808007c0518640a00c40c1d6a8072492250074154102c1e000c07203403035902d58004d83c01501d03001802018042699480b000c100049a5042442410041100710207103201074245110420390308016031000c503900b152501080c0303042032040134000c820001386d1308241310b1076114080c0401349401980034440d003006001040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 732706456 1250 732705206 732705217
    0x50d08040f06240f08032a0105090c040c0c020a0513150e070908070e07051e031e0a0c141b10020d06060503060906040b0102010e0f0604020910030206040614 69
    0x1044620200b203501c00c505102501c5102c0d181a80f0140132800d00c4240d100e04050703038440300c021414081c80e401c000d028003152030b904828040300c070703900492128400d0003514001c1e00110041e002c0350801105000c102c5072030840400820006200c9500561144002e510540d101518100d686114190041000c0c03c02900c2c083d080c04004280015446d08110050340115100c3d50380140c140d5903011050b03a202628003904070490001e80101d8885801352000b0303e42d01c0e406106038145402003140001d000d810803a142c0701d050040e2404101c21040c1c0b001c4403a44070316103403001c200c0645a80402007000038020038040c001c0400048680560136000031401c0c1042040c011210700584030101400130707401c86480c1880043c00c0c4000840d41901075002d50b8810a000b4219400e0766950301c0421000d000107031040c6d8155580d4030b1a200103282c05019503102c60303d11400400d80d90403d4030504c903107047e000b08840015070360f81a0520059403440704440031200c441c03500f045c10004401c00122074bc45030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 732707706 1250 732706456 732706463
    0xc14040e16031b08090f0303010b0d05041109070302030601031b17040f0f140d0e01050a030b1302031f090e0a140c060a080f130c0b0a0c1b1a07050d08040f 68
    0x804003d40052540400014441e9100398207841c81d03103d01726030321075807400f00b030084805001080c08100c1d81c200c080d9004950260040c0310780306407452440082440f02d0015510540001e400104010840d40c0500a59142c3c00b98080e6091000c0d03140c002c010900c40031442c103181c2d008485004501801391004048020b1a0080c0503140900010b180103050341c4000202c034001402000400c255842c00b5003507a42c000007041e141c007854036040710700c103c0080c64464282d03a40070030b4040d41c0c9902c00c00f2620145125241101403901e01c24281d007800718155201da4001201a8140350300c0700c111010100d016100141d100b4009903800d001c06801908140045541c5508210081241c1c5405c40e8003200003409810128042291516212200110f002c45007001801808c175500c010880c2042400c01080d0224452804807602c620701d41e511403225a2042c00340b4600c086400b018818840d184030b20700c079a124803804482c50700c03d00b95102501c440031388100c4800d2114241c001802d010484000200040e403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 732708956 1250 732707706 732707741
    0x120f020a0804030f0203090d140a1704140f1020061617250e1518060310142220070201200118060c14040e1603 49
    0x58440004000807812901a000500c00854890f03540340040126868800c018020745803144440e100d54808a003410300108482c0704140200c004544503c03007141070140e041240503580d501e4051000104584140814411006280b020b546035641312820714845085080040a0417554000105141450300241c035441c00b5213020405122400501c003000002d00f81c6034202d583c01c2c0f680e04940c1c00d40f0708607130300500c10401d121004005040780090880e60121803806008200085010512510b0040d090202e03081010410301f24120010034200e81c1014159612410b6183c82a0030301e00142d100c0c0b0400c2483d0101c0d10007090300382c9a080301340060720740003807106400784d0071600580d000740500002203540d4015854904800760020702210210380d0140e55042d041d51b62200000c880c2401e0344607040c920744d81c84500030040110b40c03042c2041e41d40038101c0010303104c0512201409000050460013040c0388100024056101910225500120141c1580101e00ba4140c4180d0040c0b122418034a151003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 732710206 1250 732708956 732708967
    0x4060810150812090406121208041b0602100507020f0703060218090127020910110708060c0703020d0e061602010e0405130212030703052515020a081006050406120f02 73
    0x25040001084200ca040d41c08015150380d1f65244401c210100000400003851401d4492001c0d21540d0004d0704903005190056204002d240180c00c078500e543d00c800056040b5000d08040d44842d1b01c100d0768010b4880c009402c80180c04e01246845003001c0c000105200d80c0800d482104900300c80c0d0410030142c020300003100ca540c6480443e4981410704803011f08a504182c000c04c120704043c000d50311303d1900901030b00480990020140c400800004003000036114000c0005035040c404c006c038078002d120040c000d9507101c059050080c14480f001142c0400d10080c4201f90085445440844d41038000503000a86011118801203c051410400c030950040c14601488441c0c008540880829482105c0c03090840c00c2d01600b854507802220801b4001c142c09005a1b00d03444000600e00240c00341c2c82e24000824001c03075485a41c0340759650403401070030780d001c10011440c0d908150110381110446062130b07140c600e0000000d21a11680c000c0e01c003001b00c43c0c28082072038032030780c2c10100c11024029025500c42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 732711456 1250 732710206 732710233
    0x1406030c07051609150b1b010b13052205060115021c020c040b0415030204180f030306060e0f150a03020c01020d02090906090c03070f2a0c05040608101508 68
    0x100e01d0f9008070505540307450011065a05004030001c00c9940441001d428125218003c608021100041342080d548848141446503640000003450f4260715400092505003021419081d9501c3c1102543c801350f01e007460004220001041e60449068452404180341d013503800b00e080800c03080e003c6a101c441c00c45c480020b95000702d02e6004400723003540c080294030480c0c010801903071901e10b0003190129540c0000d10160806030400b444154102c1544003072080c56641d420a07148481c1030503030000350750b43e1080c001c0f81d505c0303072403403d03050710403102c540d040c03142440000d0400c5002c411840f0728601c006002d540b154000d4042e608502d206600031500d410043d0100d50207940649400d901ca014041d000600700e1414140c1c1c1030281d030044000504503602d00a0a40b0701f551030344083c04c01d0002c2e090041501280c00e07507141402480201036074040c3c0b2a503141400720040700b40c000d24071640c2807103c28018100d00041104540820f0380b0045504840144058840c9480d50041d000314044c0009650f0301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 732712706 1250 732711456 732711493
    0x708040f0c0537050d0f05010e1905060604091515150c141603080304020d0f1112060613050606070203060f010e060102031c05040c150c03080906011406030c0705 71
    0x403e444440b04500d80c1c0000842e100c1158803030141a50021502c416040440e02ca0301c0801c0c5580e1065000040074001404031502d001ca0310a040021840c0f18400f02d010000c1c1485203917000b4800782e5042c44452402d40d1901114000c0c400144041ca6903a4281030008501c2e441403070040c4178000040c240c886030714900030141070034100c1c01e83e0110392048042d504000c00007440300003180e403100916185811540c542e10a40d00141003a40d10107166070808010607003841000030600d110b00d00c0e6210350f0904d0804d10410102c281030074101030301311b031040080a84401c56260320b8424035404c0003510343d40c1d1000042d1345024482000e5007500c00c0340100038800703040c9140f1a050b14514040c00e00d00d0398a02c40126600d01c601002220502d840c1c606464200d09039402142e0494440c1d150841100d884100000d00c01d030a0100c20380c00610720b202208203040d0400c6165420080341c41c060092581408454101c0c401c0521000380a51000030002d0f2160141c03030240c903800c0340e0000603200c5500c1d80601c030121 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 732713956 1250 732712706 732712759
    0x17030c091903080a0c060e0718050709052214090307031403070c061e0e010204140117061210020a0e0f03010e060a110f030415060506030708040f0c05 66
    0x200c0e200c10007158001d20300c503030880460781d1240105191618035a07080b18424002c1c1001c4441d1a103440c2c4d403100910040c08540003a103064a540003101d8400210f00040c1c9001404d05401c0c444009011320103234880701e0b00c02c202102c184c090b400c4200e00400d00200108407284031000c5100411040c0094004080020140c05000c0e544555080004184900d201e03c0252a107001241608091000042c41500b149a00e1140e60f592801c02404c410340d644150b8084021080142e54001000c0c4098220a100703050041000e1815044000d440b10340072110a4002e40b0f900d1207070080ca020000302d82c20801c20a4125000b0312400e54452341d64001c050300d9949503041042c8107068084903070704141814030420000c141b0f990300600071500c2d0300201c00c0091500e451000000e517010040e034021141c1c0b00e00214000c0b84035500f2460f50203824000c3c0701c12280e0541049208080400601c03010325806031101307400a800038840c8610844c58500000034002551105802c0144060003a07240c40b41c000e0a000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 732715206 1250 732713956 732713959
    0x30105040510080d081b120109050a0b0f060304020a180e0d050c0c120f070e01170c0102030d11040509070509090a060602070611030d0608030c070e130f17030c09 71
    0x1c410788500030300c00940c40071030181000701d511010140030f10610881640b500003188450890862924850700d58003984440e40302d100310449100104110402c500c10b16621080010041120302c0c200800618654110320b04107200d4400800420259078440d480600101900c80320300c4800d525151111018041c60346801801c2d005408083d1811400b500c100c0c0c0c01c0c206405c0c058413075800b084c0100039503500c4040291140c0d11841d59110807201041040c2009000d080004003030561500361701d002188201109103040c0d4110901e50121a600082924100280d1741004626806c0140f0500c989003ea41e1215510a1011040c000803503004001080598002d60b0741c00f001d40d640f10b000c04142d07403c40c41100700583c06107030100074607845440b00707513071a00454059924024500070b03070000355413050b0802031444d0030000e08080840743c1048000c00918269076030b0003062034901c008014140c01d4070b00180c0741d0690814084100841c10403e0f4420000540c0b0803a217900b07001c55440d8450b0006099503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 732716456 1250 732715206 732715211
    0x815041a030f1b0319060c3605061908131a0405010b01141803010209030601030c17060f0c072102062d01091805060705133203100f0203010504 63
    0x80440c2000300c0d03c2034091250580d5094440001d1b502e0301d000303000c090f6480d0108404c040d5101010358a601042e8a2201c0386032440d069925a9901c0b40603c0040360301c03440c40b5070790070444403503115040715000035021514186480341c1d95903840110140c034401500200011480443d4101045c03181440382c0c003c9000340000c00c5990f03400c0c401520241c0307001c2c090115951052141416051f4540801440e210000d00050f0a004c41000400e291030400c0e041100c0ca5440f8840520000441f10131030800b00c25140020121b908000c6110311700c00a026003150b418040020b005024440c80425000340c003255180d14000c00c6905d240025200c040c2070310110500c00107000020100400c100c4840c280c11a00d0b107184000b6460418003800409541035089030f119408001030740450b0f0248030380c40c403d40540d2510365a034094002070000f903d941e43c100350b40950700e00d141040500801c0211141080014180701554890100043e250141d44001521414142040d03041c0e605519005181200c8054406 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 732717706 1250 732716456 732716503
    0x3052505040b0f040f090c0b0c0c09100504090c0b0d0605010206150109120f050601030614060409051504210c120804020303120c07080703051201060815041a030f 71
    0x30072054032201c00d080303580310603014245503076440d282e030001c00100c9500c40001100c8402c3e5541d50800b104030b034082081c1950119643c91902c1d014422804801000c5840c103085240a000c6100e4652260107214003131543e40c1040c008014682448001800c40100c079117840310300c0000f034113020f03041c036005041c0107015810200782d6a10b552107540704041416114840900e09000203a841c42c98100d2080ea404050307510700c0b0010507028444580a103010b05804100f4030b42d480c81c05d440540e40508040d0143c1c3c50003010b10302180c4081203620090a1103840a201a00c0b5401c100305803e5900d402d009801c3c003031782c00c00c1c000c40c0e8029580e80d2403a480351041c1076214102d800c0c243e0301d42d0401c2710080e401d601b041101da00d030fa182490740180d010707503422510fa003000c04070388a400454028040442c003041c1c000070002d46803c030858445004007000d00e001026403400a80c103104244024039041d00582d142c0502c001c18400102d0040a0f03624098100e85200240400c0950b90f00c101c0581100c840b01159039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 732718956 1250 732717706 732717709
    0x1902070f062004141314090d0e0a0e090c06160b0a0504080a050a020f0a0b0406050a06060e01030207050705030a030917060f2e030605011e080c091003052505 69
    0x29102d11080302900840d0420b894400540f08000840b019980d03c503100c1e08170703012004010b11400417a2000c1c6080042c291130311554035450300810016203014460440b0088899556a220f12000e81e0705608166440e51120070b401860590840912031f880340000c92701ca402011908410400310740960482c12035170301c40c8a0078604503041564050f100c2881004441922405400100740c41603461044411094001100505068040f21304840b452120350902c020f02c0914068180c221000781c0302003080a00d00b40dc0940025600e912090625802042c2d04003400014081d0100a12014082d165025600c0c500100040700c1c03402541d4548400420410740b01900045652003800c40141e800c00755250055003001c5a0b00c5003096100c44100541c0c0721200b8454129a0401140b19500101d0f455051100c0c1c0020b50b0303003007200010101c1010604001000000600d0800c5680585140b07800351034401d2001c10700c49194101615030f105d0318190b04151200b03251042003031034221301d011034283d480341c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 732720206 1250 732718956 732718991
    0x606140f06071a1b210c1602100c140d0305070207031e0609050d02070f0b16060b0a0509070f02010b04050f0708090f190512211902070f06 61
    0x84060300c1203d40e83e29400d0070818168586030403615107190300c0e030a02c80c00714080c00c42d07610100040203132000c08105c40c11035054203e40e040c0c11850301100c3e00d00f40340002da05602e4604c40d110002e88142e40c0390094911301c60081c02e01001e0b07160440c18040301e4014a40c801580d034550f1940702c6002a01e0240010103072440070807280203482d806007030031508031022188011600020301041c2e038040d5807031b8170130720000300c0030441304900d000caa40241c0041403400d6240116403040d0b610981201c0f008100400c2d410704607185460b10f15902140000d940c0c8e0b0b0030000714a6400701c541060b500207904006121000d0f400c40a205600c00385076009200c510100c0f410b11003910419902c046a03140000042801c00707000b40225030b802000407084a40e01910218040c1c60b16101c1980340314a07007659402c51083c443c1c00d0000484103c82e03011001c4c40c05410300342d0868241c94114003050124901d00c0031580092070700200030010008200c0954850206044c804e11208200d5411254075160540803491a00100d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 732721456 1250 732720206 732720217
    0xc09060415090e030d1b0f022805070902040f1a04030b0a090201020f0d090e0a05060901060513080709050f060904080d020d060305030c1c090b09010f0201090606140f06 74
    0x2074041100d55260409180240c407101d04200b0082c0400c3c002e8152000c194800c1c840f81c034048001415549240e601d000c0c0c0700790814414001150000c0f0b060300300403d510b00b015049224a0911401380034400d0500d20305248460300032103c15400003c00150309152900c001c0b09070b5800000300d600c03108028103da6141c2c441c0d40700c000d020f0fa00500004080846543c802101c035030041c0140c50385020760860081c00c01d008075083c040810707480001400290324500100354428a100340030000ca04040c40020612401403041074100500000e040c0007001c08070f440d010017880044e0440340c5090301c52803488007510040b1610a1601d02140004031503240044c00540110340140d41186000da10714400310107540305552514259443d1200000003400070070081c862109000050001100190701401c111402d0701c0311b5404100340c1001c140240c00540007203030b84c901c00900745414500450b40e4143e01400e44081c01404640c54100c001940b040f0009883d038690b001168054001c880040401a190003030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 732722706 1250 732721456 732721481
    0x60114030601050f0105091f031805070e06060f03010e0a11030402090a0e0f190501050f0f0a02280c0302010f0c0804172502040c09080303071206050a03050c090604 72
    0x40c01c010402e41c02c00d60107504c0280d0040c90f1242c034040d0440c01240e5010702c02017003000090100e42c207040714645c1c54400c003c07035558a0482c13500300d040700c0e0b1501e03644c81a150240700340141c0c546010400b02d91354802107421680780701c400c458807503941c1c0d1800d62007481c0440b507010f40320741008241c02002c480002107a2060354000c0c00c0c01c849444e42030300f2100406010f1541111032041d840100d40c0410704006408014000342100040c00441e85811800c1d6440504100d0442605600340101141c1002025900040034000103890302c0da0b841082c95140d200010ba000c203081e9080c408115268090b0b4105a001d010f50000e000c0021140007074000c884020030b520000806800206c0d0004809a034140c010b40b400100742e5050401031240d1048000c800e5800440c4803111011010841c00d160140c800040c1070341c00e10b40340e1186001040c82d200e00c0014601c1040242200b420214184198020409000007401e66420340e80c4030307d132240e9a100c210001d0741c4505601e00014030341d45030170300801241009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 732723956 1250 732722706 732722713
    0x1e051912080424020c0312060f03070b0a030c0302160807141b0d050a060c0503090706031a0d030201090b070306060e060c0c120304091b030b01020d020712050f0a03030e06011403 78
    0x40030004030f10055854020103410700d400300704011080304100040c0041040302c28800303d8900307110040140d1740d0f042c0c0340068003a80085808000e0700d0714900079034a816501d82400314465044560440080c41002d0841c00e00364101e0b01070100b4044600081c00e10700380b1135000b80e025161440507082d540d02900c0031540700c0402288104105041080d504c0400c14401c0d01103a0040e415960345405035100031401c08009200801040800e070020001003000380300c582020801c1d105000038416085016090207800b07203210142078400c16100754803240d4000e4009847844441c0c202410001c001e0202845071000007007031820240c2c11890810111490805844018010700c0c44040a001c1e04c103036126401d4a00b4007040c00001811141401038001480040c050041c2c100d40c000c8000d0202d0302e040a0f100d0440d8414030020f056039170001130b00016a0074940b5449514610b40c0707007d41c60b005164000c4c09950107410340320420990180c2110184a035032009aa03080ea882d5103481540c1c8009582540c2e0603032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 732725206 1250 732723956 732723983
    0x703020901050f030a0b1317070b06010e0303130806160206090d0305090f1b0414040f2015190c0515100504230c0708071e0519120804 59
    0x28100d1078003803c0c1c0354064141c590f84105130300c9000d00482c0c100c80181c43c42d881c40c204442003060b0071000d020b10b600050311b21800c2c000551201130380703200000c01c043d05008948961000581c0d040094070052a440103207003150765150f030034584c1ca40c0000c1e03440d4441c070004000300c041c1882c00421414880e03440000102005840c80b5801c5014080223010381c00070b401244144807501c41c0601c068144031010003000030300c440c50750007484204c0e040f110580d642c02441070180000038040144100555801c0301500710030725211102411b03045e94a030703000f590bc010300c080e60071020205100035140c1c160315481c22001d8204258420b6175001680940208070782c00031a0401800d100c0c400205401c03c01c89a02c02c203905031988040b40880e0b43c6488102ca9149800e180040c4400340c2c1d031a6143d020180500c50b604064041d901c07143ea50042410091982c0c412204a824980e03070b82c804090311513004001c8440c00043c0e02075088180c0880c0000b0340e11002425420540d69014041c01800b45a00080b40140e41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 732726456 1250 732725206 732725209
    0xf0605090114040b0717070c02130506100e0102120403060b040507030b03190318030b041b080a0f08070f0c0e0c09011d01021608030a0206010906030b1609080d080612070302090105 79
    0x40c0403005000d03a0a4001c005000054011481004d00761543c00380001c242c01000810140b03000c10a01550a1000b0001281c403907404150104dd40e60808d40409642d4000503800c00c10040c01c143c07050300c0042400824070169420002c94100c0c00d1760200310a440e040000c0b030079502e00902d05505030340010049070000b4030001c03c00080b54000d00c0d01c845250b0000ca00c4280e00c5090394403c2d0340c01444981030001f03210034000c00140242034441610003c034078000340142c448420710006014440c01505030310278010640c04440f40d4941c00403a1052500709450302c8118440c1c0e03802104a0340c030030000006e1092280c2d00844084c1c003016100d40780071800d00c51031500c07282070f24010b850441c0a00c80342e80f280211001ca00d038000e071084030065a105d4000100007481c6c1030050744590951401c2400400100d103680d0789180d00f140075400c000c00300403101c51060316007941c980c0c0700d00d040c0c0c4181c03e880a90154400c110b103004400c219414408400d46188456466601b07000184d4088100710041059 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 732727706 1250 732726456 732726473
    0x1507050a0b18030a031a01020a0b07031a060c0f0d05030606090d050c120601060f0915030e0717061e0915070c0515090f0a1212020d05040f060509011404 67
    0x2111208031500042e000080c40d0a0640e048a48134001094680c0200fa488404c0048500010360080c8014030310410242c071a036604100241c9610240f6581b04244c41105810540040c50400003410f82c940c0c95103405078031943c03101c628000003043e0040c40d2880a41c24400d0301100d004400007001581042c800d20200410100034003012500c6209107003010300c01c0d4403101b10000c80b00504002408456140c90405070000f00c6022221040000b406004d110401d00c00c2a50202c6c0c10303440c600001d0003014207140c14546140c0350070104500e400700700b288809200008a9078400e1203224408448403002d508258501e1609030380c00031140e00400e0724210028003100b040e90784265070b803400d155002c440782c81e03603800c000540c098240254110810014841000c2140080304038241c00248600328403070300d801442d05d0311010b0703400800403078891000d0b08a0705030301074070020140e058040020b4101443d08007441205e080c02100d4190801d00060381408061041d0160010b03a03108622065569036030340f854 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 732728956 1250 732727706 732727711
    0x406080d1403250c1a011505120a230a02071509020d0312060b0f040f12020303030f040f121206060f0c1104090f2301020702010e0913120309021507050a0b 68
    0x100301d60400d0060125203000704029881c4411501c0308017650406c0c01c1c401c60014000303482010310404208043c0c00000c0d4100c0e490344104d0842000a14040f49102c2805001020004003002d05142d0140201c0b0642c0b54000c1440c00c0c41002c440400c3c558032000601656121340001c0d6011f0000c2c11a070000c40d0280361107000f071034102080011415224102c0c41c4540e0003403400e083c001440480c0c02d01001000780c21300340150440b41c5410410614a50010b41d4a1100420511924032010041800c04c4060207403207031019401609016465a1044000d00898241c100c070302000f0300300480040c050b8015144034081d512190746140982c0301d1900c0c1c00d518180c03001031258000c2c2ea02c554082c041444903200109481c49440002e0305c04150100035a040680e18082d01c9150b441080540010b07a00f001d2202d001220503266240c1507650304494000c4103400031409440e00e10100300c09881141d050b0b011036036503442240e044840c0344036145100558003408030001c2651380090740b40d002040c0c03445803ca5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 732730206 1250 732728956 732729031
    0x5060403080703090509011214010b09011e1503050a2a030c020a0206160b07050f0a121503030f0207061e0305041b1e080319030b06090406080d1403 65
    0x4031541d505c00204a0000003648000d0f10165004600402c02c0003000b8402128003400c2c0080c8144280c00001a4040c001845486d100443c1c1c9601c42c084400482c20500c0200b1403030842c070318456201308010f0b002e003000300c2e00c01c902245880f03082c222200d00d42000c03040d05907282032803404480b04400141d00801a003000c00c0103610a045815005a68900042620507122000c82e00740403154a8016101c02c4040c0c0807201307029040c480c00b00d01c00b8900041d241080203500e040d00d0b86c1880c100f803403401001c03282d06d0904540c107141d40c0401850381048104072101029801c41d00308994881c0f0407034210042c0540c41c140011424a030300c1441e48203070800c541260203002d081284c030070507031a8002d442043c1d52080c1c0c2c600c080001168a21030303c61624200070400303640550710304019207a103c4007000041c8920000e16035201050300c4203803070f108144d65811101510411407252940c104981d0345e8a040740500008240340c8046a01d0746030352040e240130724824016132501c0010581c0282404107007400c0c04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 732731456 1250 732730206 732730217
    0xc010e01020c0d15060503030c100903120218130b01270e0127020702240405031005150a0f06050a031e0f0608010209010c0f020a030210051206040605060403080703 72
    0x1006070390340f00c0c1100c002580c42804401004800700000105807075072507001512a800900c40e44150382d00110f8035403d040310141d00000e050481d854245c40120001c408002400c0c808501e100984985c03880054400f0401c690040d488035034110000c0c19202500764240c002075104d03100007044440000100d500400202c01c0c441d180761252417003e10800d00340c0c044909804240c29890004044070522551440b10980c20344c505092500851650300203129006c0c8604070b00d4407560405001242503601410380141600d22a41d544660305010308010b46480b020903260100314420344c23810366106c00860701180c1204100e03901d0b180080e681a00402c8400081c152035480c6040d844051694002c04100380b2400010b54020320143c2c1412582c0d183c0100381c5aa104005185c4140e03001800d940103070707900210b03003e819185480442c28024659000a4011070714107000c3d200d0681240142081c60700303400300417005c1d030345010402043d5561441155084941080b051022506500013031001034000c3c14030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 732732706 1250 732731456 732731473
    0x10609050402161403030a0608061b18150a0e0406050d0f050a0204050a090302060907030c0513020d0c0e1801061e05160c1a03092e1103270c010e0102 66
    0x1301c00050b00310040410803508004100f1003480d000e807086001034504000100450302d80280f444402c546046030f07440802038040b901800020101165044808019100c040401d0107048540b509422080e80704010600c4140034038510b08141c810141103440050804400180b213490302c1d190001e20102c10f4803140500182d10000d40c5840c007405004041980c00003c00b65400c2c00c00034140707030014001e100980c022100410218841100c081e094410441c3c0c0409640c030701800c104024440c1c0c0b0703503100d0540d04240000584c96045140e0608101d02031350800c44600c030207044002070004c00d0188101180340c0c1d039a1a00400c001849410304180e050070031030302d0030744d88207000b01c0b04c5168104203c0740300005400901c10404400183c101403078841080d0350546c10982006034035040303006c6845c98400c03000b914024002007040c0810070b032081e4508040025403401d40c52402c050f40100c6041c0079a8104290280d03400d81c4001900c4098510038026028507100c00300110b94051a14452504500c900c408 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 732733812 1106 732732706 732732713
    0x15170d12090b0a0506010e040e1608070b0f090d0506040f0611090a05061e040902030105031605010e120709020d0f271218030515010e01060905040216 66
    0x380412140d07034000040f1f03211040c1340b8811394001d051010a000e00000440e007000881b0741d020350442d4180d11083c00c5a134074031851190000001042200155051081010302107400f0010710450451134145c031043d107032103002c0d1410340750300220442c4d031400c102180c0304c0c450303c1505103a01e12b400e00b112140090820a001d20400d4001c40c3d000543e90603006003080c4100b02040788120050700d590310360000c1e80081d0002d02400d4000c2c8140e10a40945070705241000c0c044450507914240c0450030081807004c0b801c03485406024510031143d011402c00001d00140403600021040020380e050b0030246441a2500c41d0350b03c03c0c042d90301050010104030f0813490164020381280c049004200071000407101c0f0070101000c540100030740c09000c070401c080851021210fa01d240082d0450341d8940c3c400c41c01004007031040901150142e582040b9909140d00900366803413000d040703c4004901c0380c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 732553956 732733812 := by
  have h0 := BRFrame.cov_init 732553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 732553956 ≤ n) (h2 : n < 732733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
