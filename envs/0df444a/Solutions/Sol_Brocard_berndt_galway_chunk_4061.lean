-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:27:07.99061+00:00
-- url     : https://prove2.me/submissions/170eb1dc-118c-41ec-90e7-85ca30c2a1e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 730215827 ≤ n < 730395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 730217077 1250 730215827 730215851
    0x30d2c0d0909090f03080a090c090b03060906130308070c02091006021b0306010b070602160821090a020d210306090c0e0d080c0f060a090b0a0c0816090504 68
    0x140850049840d072648818141d0780d03842c41043c1c030f4104002070403e11448007510301090251401503072042e04210b0004481e44c144c0e42d41810600345400c2450b00360399818407a180f50404200c0f00740c1001a403002007038245810751121440d1a40c507500181007243c0030010810660043d1007140340c031075005154205500d81880041d20b1515503202c5d450041c8a143e641c501c03501c5606000000c40343c1d002d0701034020b60f030a00c03101c2403844e401440c04440581d404c10012400007022107100e04070314481c441c055920603140180822641c0007010301c00200b81c082051080009000400110306c035410340e940c0f406d0016a05065660715401000022613500b03800c522040964036521683c16900403040812040880e0705046598039085003001d5042078103000b4100104501802078000d0a40e0801101c2c1d40844900c501c0f428a4030544885400c0703070311800c0307000402660301c501e558060b8011404010700741c02903800405a00011b0990f0701c01014103445401d03d40d2142031070101810700a4000d1040c01d29581d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 730218327 1250 730217077 730217083
    0x2d0d03261b07030c320f0c09130b0415150f08070e0118090516230906010e0321031b040b03010306020f1e071a010602030d2c 55
    0x1d5104021044000c6150152a0034200742da501070780503652110300500d01d40c0e803607103009000859148540c020070344064165891071000e0f0450040400904101000b14076020b00e000c8078200c1c032500c2081558100180034a0f80180c050382e41d41c02c0500e410541d03c2e5403c003220000c15100b084105a4100204003100025030807520084030450160f071583c1965400f0184e4545181d8010031a120030410010000441120032421035400c10341c500041c030803003d5440c4c9150544001c1c120100002003042001034030702400040a8500b034103c103411a086094000076800f20303009081605201c0c441c00f965041d918104031110014018000c641644030020201084a8004803880c4803030b411841401c2251108030300541d0200e481b84000e00c2d0659003142d48800103508420b22840020600b07009013203144504003c08001008201c14441e82c1e01c405003070200002000c1d555000c103015a00c401001107550000c1201c584d40001200029505290b40b030640d001140e000301e4101411915040c925119804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 730219577 1250 730218327 730218331
    0x212040506010803190c0c05030304060908010b010c1505071e02010204090b0301020405101101230105030f0c060315060705070803120702010b091311040e0c2d0d0326 73
    0x660454400c1e80e42c42480c0796803071041780320070310322030044554038140c650160140da61881d00c80c1d0070085250740c0b21004240356410645c0000c0000b2408101000f0405080c810900068002e1030140300d0b1000c1034440798070a059401d40d00180545d540d0004070140d00c00c91007404040c540150003003890b000110003e010303400900824490515004810b4914501407007118101c58000d4003840d11040f0842054881041046403d01c0554a80e01500c081e1902c48212495022403128080c2d015414041131500d060850440080300c0d502c001e00340d401c15941d10040e00d40c07000c60828a4004e045490303020810900880c3c40042141c800d0507000304041070040701415900758980341c400c41f1541c5410080b82650030903252140c000303000c0300218040c83d840c0c000c00c452247c02001404005494440464201d031034858800300c0c40d07041600030b00d100e4502800b0751048180c0180c6004621152402508111522085c07a10303c40d40140a054007050b00820303802507607080500a5041c0f012031509010000a02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 730220827 1250 730219577 730219583
    0x3020a0f03051e09100203070c1e1709010203040b03010801090327060e0f190306050106170a0e1203010b0405090105060c031803070f030f0b0c03161b0204021204 71
    0x8114440d244611a224161154a03007010300b208005800c1107808031800041e095070401d018a00d03030f4490401007400254010b001503500e20403600e440b8180842c06035282c1c04490021540c604102c0d0100300171504020449500200c5282e80b4080300c00180c0c918455a4040100c1d02800300c00020440c0d01076004030f001c00c0c040d44526107011405012180b20805050b110304134200981d10600c00184542007540702014040e0901030310304d071040300103007080f01c42040102002c0203004060007040b210b80502801010303c4d0030140041c0c49440c20b41007014000901a034201c1d6601c028150300c05404012407041c03100b104006503a0b95854a0941445500c07a0146034003c8030040300001d07281c2004c02c1120300c039855090203941884010210300c001704c0d140c2460039916110f0810003017841214a0803100046101d4546d82d4070300d090310320b04510034000091001254a406000300700c0110107410039005004150729040741d1990103180f0082040c0a800c90103900148040345004824045406072401280 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 730222077 1250 730220827 730220837
    0xe0a1211030c0402040501050f0304060f06080f0d110a0b0910140406060e062209080313051e060c0c070f0f0918150209060702041103070f0e01020a12030e070603020a 73
    0x4420080c0000e91041b4030510b800280200800721014180001035600948102c1011036203031020f24140701903c03101e070400f1400b40c000d41c80c0040340d0388041003621211100d50074820714009141c010182c81e00e04085001d40741d0210007001a040340800e020040000c011008200461503108001140c00341c402c40e002c98030940703072481c0801c96402c0070386048c0c0300d04801010b81d81100b1a960a070403120103001e810018050721242c007100000e9090001e14070032000e5440071410382c807050804c28945040d6511044646401c510002484840030400e60f520600f50011039650342c82c000b85091410849030700185074030405080106051640740c1c602c008035082e81406211405034040d41c62000076050000900c8401e00700c42c0040301c00c28a070041c04820b000248940d0604615802013020780341c1e00e030720031921003c0000401140e80e4210504248140c40ca2034136060140381080041e5440341d940c41c2c00b82c15101c0c6041c2c4400d00030310a0b000081c04488600035036510a41c0e81d20050003a400ca09114400710f4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 730223327 1250 730222077 730222093
    0xc0e0a0b03010f050411160503130906030b0105010305090f0d0509040509011a040b0f0405131b060f08040f020d060e0c012d090314030304020310050403020c010e0a121103 75
    0x9550102070764181c503820501d025000f468601008002c0c5100501d0000a80e0140178400d00c62034010400700720715010703001441daa0801d40401840d000c4081d001070190134034010003840420680000320f81521030a080001b0b4075110486810b203004162481001184110491000800e078804060701141c0c1c030a41e424049620354002a0b8203076802c0400c075a0b0a0782e43c1e4183c05500d480c0c41e80000c07906407406806114115100b00200e420f49108a68440c2e5001420510908008521507141030025800380c0004a207030a150f00207108600f101405c508201c44040428140007003c0ca4150307020b98020512201c031103e41c0781030380150080403403000250085002d80017455005081c3d2054002c911150310b03841c41d4030390311854410044000001c1c00c0200b036034000b000164841e1075010540c01c0703c0000b10746900e49441018681112a02859044d9080c2018040040d4001581c170a960b0004d00700010160340000218512000c250301231813010440070b1858050040b40c05840900031000e400b075803050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 730224577 1250 730223327 730223339
    0xa05011a0a050108130c0f2c09030d09081204060903110106051815120a0c08010b010503010b0304030c051014010806040218070306050613180912120f0c0e0a 69
    0x2a00c1c841c49854041103401d00060710750300340315003a404550300c1410170200f055103803a0342e03000810303c0e5040f881030b400070609000c400c48803201c540b00d000304080100910620780301e100b03142c0324000c0c0f500c10500280c49000030020815000240d60089496101d00b0351185403a040181c040d03d0502c20680c0403500d034101041c0144018010344094840c050500700c4400004104000c10f644001c141861b030a03004070b00b070341c4143c2e216001500c150610500600d500c1070541001c81440c840e603171001c182a0b14128100c41d0a980000569044541d6401815126070312410203540c45003003250010b20f603004001c03210f05140b426500c4100030174848151514107a8840c50040e945017011364002c0d6200f140e685070b44886644503800e00c1d45c002080e2a0100f80c0598440100d1711580000404003100e8030100f809002c0301c088541002c0180c0043c1c031003441018150f484400c00c0310310300004d440812000e4614099100d64176000307944000715841c002c00080c503212500401d030145100c003142c07056000c0000000c074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 730225827 1250 730224577 730224589
    0x120806100906050a0201090b010e1b0405090103230607080121080712260708160c08030a0b19050109050d051009150c1106060d080d050c0405030a05011a 67
    0x40c01009844003600307030381011016601038000203031140031503403128044030000e0380320f074003142c000e028040469025003440c0403110b002d032000c000b604803902010b0000304641d9580c0c60599045a401c090b8120349201c105040034249649610a001540300d46401c1c07200a5501184160480d001c03035110100d90107256010260303c00f0241000b90003440107002c0d120226124000c41c050200352402c20040d414410700154400480c019055400004617100f0013002c0764020790100d50064168014210540c030a80c406040070b410320070054425040400040d10300c821070382c0300066142c00286100000e001d00408442000c1e8140500e0380002c503054000901414480c250340001c60703000d0050803105945d0001300e4001c0072442c0c07041e100ca207e4000c2001c504a4144104c2d003452503281d440002007805880d01c94507062019100e42c0c002c54500346a14041201101034800307840400b0408156174648031100d070080c0c040ea802655050095403810003c100301503101402c46c108103c4c0d030f07212201c940341c20030034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730227077 1250 730225827 730225849
    0x6040b042916090821040e04080901020c011e031d01110d0b2202030703110a3207080f040314100f0207171606051302010206100807210f120806 63
    0x1889038441031004880c0d1603040040d0000407820301441e421b0950f544207080c2142020b58050f201c800001800300d016590620460303004560038244101d6811a0300c0d8908603540d0749400700c208240d560700c0c0340d030041c504618850000304e007160300038000340600e822100d1156200004a001c968501041c0c035482c0d0400144490b2086140d00c1406240c0030701204240c0a0340c0020603038000c01d680c40200c1140500c4103409088861050750740c220807000500f135038802030062140c2c0340054280c3e906103001c80c0050201160301042e4400465070302c4202410070100c0300e0003540c06c01000581740c916036280c000b01c006501c1006405240091240315140103003003007203200d0324101030310b403182000c180080c1e0003080000b0080404c2441c1030642c3c1c0d41d62511060304451054580004024002203840b00f590f9042080d0360b00058001801d41c0080c0c50710030b40d00d0741c5050600c26075502000c04c00e401503007008004160a5021b03007010b03000f082c2210074509034111198582e442000b04509070081105401c000540903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 730228327 1250 730227077 730227089
    0x30f0507060623130b1f09031514090f06070e010e0a08161406161e080306040b1509100c0609110a0b09012309060d1a0d030206040b04291609 62
    0x30240e00c070032458168141c0806d1002414000031050000c0041c5203050b407511071340715071000051000703c078580d5100c0c201000b6100080c15400340004240c00c84003c1141030f0407800509203542c088451000580d03102d035082c40500d90080c100b03d400680c40340041200c0110280055241c1a0b40ea140c1174200c20101447c290150014010320141c3d528040c5580e00b0121103024200c00447c00d030340b25080c8a1f8402d04010116a201004024070007241001e0103039500c0503600b100c0d9403188032201c0360441000d0040354515440342c230301002180e83e245c0c0210600300116030060b44c10322881c13181b81450780428101141b283e004040c4e00800040c40c0000700c00f52003030110141c0d21400980d81c070700044540380950090502d1018410840120240c0e503007001415540540384000c1240c08140701101c100030b1051200b6406031080b81c140000083d0b0203c2c500b40e21903881a100c0d4101d403036500b09000352004c1c42c000d521981070400c060030072044103d9030b081d10516102039500303c40850050b04031860000d0348180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 730229577 1250 730228327 730228339
    0x2c010b0301230a1d0613050d262a07050d11060a0c02010b040903110d030902090c0319501b0307051c0207030f0507060623130b 56
    0x801e40d07040082e0044401d0007400180d442d0f1441410301e00d181040030a45a10ba80342841603646e4003005001e004201c0d4851050812440d0ba0003d030860350451b80c0c546045140e54250417000a0b2200060300e040f500b5400c408182035001c51640c0c0048146500204083d9064400d00b41c00650701c620846000a0261b131f08409401c654888114150152960001c02401d41d502c0f452041055100d6200301090346000343d84117000305985120090034054100101e87c101070500185001584901081513040041480041d9483c2d540040c0c3c1b2042d20340c1d24048421700c50030019910001405d8400c0020700d110460380200d4201005909d10000c80c0314520544007540d03070a07204102c0f0141e05051294441100c580300d448810710b05c4200c00c0a6481101c014010038270120344122107807544d000f80204100d080b4021880c00500f510701174110000342540c8010010001016410403055401c010014400001903500590810348010002503552001502442c0720201c0f000c5040c4550280d520383c000082c181c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 730230827 1250 730229577 730229581
    0xa02030c0901030c020c101713110d0503090a03080d0c0c03092903090102040e0a02040501051c022101080f0102041a031e01060909230a2c010b030123 66
    0x40d000b41400840740c4056000b41658201c280d250241d0316904070300f850342c0300350074001d104234400f10240c006001c241c982e69091010000059082024100302102101c07006002e42d85413614130b00d07611580d844141c0280d2604000810019944080c1c401051958414413010000c07039004c907083c8958080c00350026a01c0e06081210302d1422a4001075150311824071030651041903000c0805034800d44040c1d840313030350000f8104002d141c0c80c0d11a50b00a08801820743c83d091508000034183d004030328824a104854400280c82140d00b58101c030201c200c07400c0800350000c803032007480c9402d59003449440494019280344000030201842140c1c1a1403a4a13010034180718200603003001c50704014030304811480e030b403404c0300040c2d1040c402a900a200c5030751005021803d01c50f00e082518134040c0391048140041041180c00d000411115600c06240d600002c0c40401d0345c04200408802000428281000507005404103030041d04001b090705401c2e00240103041d2a903100010314070b0200f840b0701e00c040c4d403400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 730232077 1250 730230827 730230829
    0x6040312020c0a020d0b100621020a030603021c060b0a0f09090201110f070f060804030f0e06093019060c0201140c0a09080c01022824050a02030c09 65
    0x80a020961850b0701102c041081a40c0400d02c4800000000d5881206460030840780607000a20900582840d140c1000d1100f50b603541c0e10180c04164980c481300a40100b01c0214040c4a40d0202c001150010180000e0344001918603084140c0030405403009403c24029000300e00b0200030b20022502c0c641d45506489207006030303040081c0a0034070103e0403c180c11104010740d030f1381086140c401e1804034001c3c003405071400c8015038081045511980500200380100b2003c03a4020750081842580360902202c00017020340021454402e01070900e40c481d003330381108181c0701001103000a45250b01c002c040b21103013000c04030b6561140701075807c40c124a44540d0800008282707805c101d41801303150001240791940032404444910b412100c0a15030302011a007035000560042d14174004020340c03005481e40c42e0346080002d40b0303402003000440e140d9460314194a4800440340c824189990445100c09181c01c000c4800b034003481c0700d141c0700c1ea44030b401d1001182100106100316030041300b10790012403400761058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 730233327 1250 730232077 730232081
    0x50a0806060408070b090604090203100608010510050403240c020318030c0a060f180e0406050f0912070318080304231c110909010f0e01050c0702061b0709020702011106040312 77
    0x1d524980181f0b0501c17000a0203141400554010042c903146181202c0c106180185000c1c4140d00444c07159801d0140580100d80203022501070300e41043c0c101c0104d0104030f086540003443c007044d1445044c6400c03188040c256001c0040c00b44201000802d45003a0042c8041564624070b51000c1c9501c0120900100203050044265031500e1509050000380101d0f0703050841030b00c10182d8806e42042c1071000400003040014440c80d6070101c04a401c07400d050a1040c0e4050390b8030044501d000601200107004000e1600480016513507100742c0f052a900c0b076456044043c1c50b07810902c61140c1a14411001251040404080300b1031500c0c050a540084e0015503015038110020701d00603209044203403d980c1482e1203100e11a40b2031003c0034004500c810802c460301045071001c01801605916001c2405011030291080b550050340403101c0c29210080405a01c0910304408a020000d1050900006007031195401501040d03000b6220200d82017802e854094840808a40040c0000e44c1d440d803e0003602026 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 730234577 1250 730233327 730233337
    0x901051305091212040309050409110108062b020907020307080a0f1b050a1103031204020607110a170111040b030414010209030d05451c03050a0806060408070b 70
    0xb0700301d405031080c00500040c03540c04000c950122031845001c200c1415042003000c1c0081405031410480300c1190340301c1000b03000002c44001e0402c8242400700d0155170701c65a00310094008048140e00c0315680c04100350107801120402ca020f040941c1c00684064004816100d0454121030340f43c0c81c1080d00a8202d46502e41c207101c1d003040c010320504c1000280103642481003c140b19400070800101e003030518020072203000315a070340301c2d034000c009059101d606c030480140c2281e4140c0b4001d8596407030385807403141d400038003003411340284451100080107071144051115490401d8000c01458030b80c0c0703900001c14403a0340141c01d510038040001c0340c002446102c00c0da04100480000504050b91100000c3c1001c242511140000b0b130003007002c1001d4400d00400700f088089202d00c51041d80d028125081c42d6103240c0200c103d009410386070348034042e103500211070003140103039801503200342c900c2c9030181454000b03841c000b0000300708400168071418000d003160181e50030540107110031890042d01a0305030740a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 730235827 1250 730234577 730234591
    0x130b090a1a0d050901020d1b0909020708040306020f040e0a09110607050f03040b04050a1d06120c09070f120b010509190b0a020c151204060203150312090f0901051305 73
    0x304120b04220341c00c0e188111401842039200240c2d81e03940c1e8150034000d4410a4605414000c1811191012141c0200c244011202451005030300c8022605105045019039031000e001d15000056441441c031a140007803040c1e501d05081805262a03403905e920403104072200c010310380c4426452894291400c200501141da2061040b540c1580010400704c0c2503801aa0105501b0400450280064901007103084080c22404a254500506410540060782c101a0102e030059031150080e070600d0106010685c90798202502086140c100920001c0000310b46840c210000b4074180c80c04140d503416130040e0854060160341c0d480c140040d44040003a0441c41000044001c2d1901000041d03960710783c800f50690701c03c0d94003d000110204810f000c6401e040d01007404602d03108006181071440c030782e400c1c3e9801c250888001038aa9480070b150710004c140701c00107103038148104983c002040702e540d00140005101510300d0364882d410070040c440000b00a0145552140e0b40c9451016018010b41c1b20907800b501f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 730237077 1250 730235827 730235879
    0x5060402210a03020c01020d052508120f07090506070c0915030c0e090609070b0f0f0f070c031e0f020f010c020a061e08010510080703061703130b090a 66
    0x6a00744806180c100c03098000c40142c0c0005c00070701155a0180202400c01c038440c11302c249484240c8a50444603c0e5030301000100d500e000c5822414001c0003801c1c4e84e4603001c02d09041c055030901d481a210308000840300600080c1d80d00700302103602e04041040c1c5081d00d510940c00b07465a820645801d000d441c0007120f040c3c1090003c10f0000c08140c2420054000b040098080403003810030b01d03c864201440100004401d42c0904e408001c03c50b42002183e2107015480304040c1c44a5112107a19070710301c40c0880170300340400041460828005620401401c580c0300b070318040e0645510400f0816040010003000e01114401c0d0000409401c00c18080100c2c0340341407401500b40b0255a00240744550b441d000040000c03641483c5106044140c02c14201904680c1000c108661600002441703010400003400104a8800085500180a500000080e000306031504088000d0700c0200e960704d400c90f1500c0001084149000141c0c490050121400024094241055141415220b440302c44240c045041000c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 730238327 1250 730237077 730237129
    0x35093406054303050403020f040b1e0a0e1501030c02010b0d060905010209030d0804030e030703020f1201060503010204060e0a0519030b07110a15050f0c03070f05040803040e06190305060402 83
    0x340a0054400381a120f03894417030310b0b141107006000700084d903c03081502a0b8034002030010507036101e8060210f00001c42c000d5902d0b1400701e01c081103000c441507000104409601d41404010100400741a405400aa0b0100010b0f030001c1000c9098400c058001500846c07800001c0c8041540394000085541c014070026207450b4008010903e030003180070580b40094160803e00c020590b1041040140760421401020164119000102c501c0d1089001d036220303401d201c1324920252801c0d0050b07801040d00800841d02c490751000c02511a2140c04680c52184005e48001b203031518046207140d20400b50f42401560140c00d641d240301010201400e403c1c00d103c075914407207070340c2e210070402024a0782c81601106e00e903041c0e103c0004103442000d0501c824850307200082000450321541a69400146898603040a0254a006a40512441c2c0002507140400500420520440700c002d601900096a5074680e018038200743c0c0034910240d000c01402034210002103000340c500f1981c5e079250841d0300f5005001c50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 730239577 1250 730238327 730238437
    0xc0302061204020111010510051c20030709020c0616050c03040323010506030a020405150604090501150903050304051e060c0105073509340605 63
    0x1900101c0300c864084241030200411541c1c014444003500c0c80150080c0824100f24503a17510720112401058010500c09030f44210301450803400c1d100a40d00a5065015900b1042c005d6211001443c1c6440c024416554002401d40c8581700312400060400b029008a444011009111001154840c010410144142c00c8841e03028002000114490996110114000d070074043c0d28030521070340a02e441e45090104040e0b81c5000c902080b2280d411030300058030780d0b0740003d02c201d010780280206800110205000c1002c210325803010f8140c886150b03012035503281e5010104c407004981e01004225030000d0100300440d040c5280c0c400800342d5051054072041e60a100450f01d2174000c50b0702e4041d503a4658041c40969600400315510b0030f020321604422403451290034601c0e1100008640a012203035800040031000140150105c01d4803660840c40080d480c504804240c00c0380310351492142e424913100040c0b0500880c225011890484080320054540c0b07018203403095a403290807481e59180e050b8a01c58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 730240827 1250 730239577 730239589
    0x60109030c0e07031b050313080d0c020328090611011d0d0905190e100b0729060a0611072c061e0d031101060914090109030e010c0c0302 60
    0x68030000030041c15603d0450001000c2d11520765a00148044042403094102e52010489034840c840c0074445403260700c946090f02c0144070381c448030520360746051541d044441c1c1c0800242098181c040884a0520301242c55005101403c4414404116802401c0116034040c16005180b900844000244c3c0030420b02d00c1c1d03112141195058032282c00c95005018401e030072041c10405410199004524100d03140c1d40b140a03070380700f406a82411109240000e110340155990354003d010300181e91a1a03017910b10707000c8841c145207548041000c0990790301c0816240e00382030b240d00c600e0303006015403205803502c8800c4e10040112082500c560060503004541402d000b42c840b0401e0800428ec6a000110b00c4038840f0601c0001e0b00052203544a140b00840044251181710200300c02111400101070880ca8151003410b5510604208ca5083c040000b035030000a0b4001c2c40264404c003a199150354a40d035980e4200d80080301c0c002c02180c0c1c80d04c06054a5481401c3c040d4800784205d0309004440d48940000d40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 730242077 1250 730240827 730240829
    0x1103070b190201140f0402100206060604060c02030316061b021912030b12060717090a020103180f120905040507021b011b08130f0303120b0d0f050d35060109030c 71
    0x1021340014000d110031404d10f1188d115011200c0d102414060410200080140c812442080308000751180b0307030310643d0341c18001c503141001e0000b008602c03400f940c6030a8029020701c41000343c20410f10000403c0b042c0c0041401e5101110b003070300c220404005556105085180041d1400030590743c0c4204404549980500c580d5081c4020014a2a80740001005150702d05400d0268092070f40e900030700c00d48032800100f440341d00b80e0900707020a21156a110303a20f0005420790000d81782c00e0020060350184580a0407105200c02280d41d03801c510760300e64051200383c0e03100303440c180c006a000b0800e0100180c10603000005080c4145041c008080c400c5400440214a54005980702000010221580340005134800000d1003500400d00e2340b41e03c1e540b405050082100c03003402c1c8194648900c6082507030b5104004420070b40c4429110801c080c0ba00700556904100784a0002003100000005001c40781d84407480c09a0003c400e10000ca02103041004a29110140809044c003031001000700000703814940d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 730243327 1250 730242077 730242091
    0xb03030d0f1514131b03140105010c020d06110c340e0a24080c04050106090803161518030e010c0b0c07050c040e0102071103070b19020114 61
    0x40340c00381c40e054459045500c0c00c0b44400c124040e0300020003012101844408101a08480c2d0340050b1030700201c1035028042e608090b40100402e0002588000e070036600c400550010071014006580e2030308e00550709a50038260103035004e444d03460b99800081054020705600044456070500b090341c02d02c022403030101000107800b9054480c2d20745118a0490310380580400040c10300ba031042c50b00c0c00c841c620b00c240b0040e110120041c0c44401030200d60204005158403181404400c40446949002e107036204c1c507104001900c61400d0800000384d01c1d100d641580c00352544800551304c0d24840311613401c1c04150603482203032003070f840d184603101c0c0040c00d1060000c605600400c0b69420700f41c524005004411030481541445400d02842c00441c1c13140c201145e0003540440050341e54181420f01d00d151030791a004003039000717040143d8001c0c20354042d000341c03480d10b1080306e90300381c00317075940042548581c02402200c40c0c5140a10141d541d03503490000300003030f094190000099900010101d154198400c49210b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 730244577 1250 730243327 730243331
    0x140a0c0b13150209281d040605070c050709090f06050408090310051005011d0901090b0f040b031c050c0a030807121a090603030d0509011a06040b030703020d0b03030d 73
    0x198244040242c008441c50030140301149090400400103488141002e8224904030800045007042c018070a0303024040c04c11110862011104400d1b81020404100d0301100d0311418400421502c3d80a100c002810980c801c0113850004d02340501c2c60001c042c5000e00341e03075008910460030042891842603a029038080c2e00a60b40c1c411f03555040c5450a0102000a55803500d0802080484440280c4034005d03107500f407908146200034105c0845c4180348040d1129804000500002000c44c003a80c081e0754100000d850100d10030b0043c10401c011109103401c3c080d09034000e100c040d44004004000d426801103581032070340c10140800f4409142c00d241e10b0044000c200d9200038040c10350b8100110700c011004020042c0300d0500c0c5240400060103a089495000d46440004907441d035409105076541c1c9020030004100a161168500303000c0c0090204480f1a00341d030907c0200320303051120480d42618200c420040c070f591144141100207611048080003019580c403000c080543d818401000080c611040c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 730245827 1250 730244577 730244611
    0x1020d050c13051e030607080714120a05070219140111042106020c0307030e0909011517071a0d14150603090f0d09090e060106140a0c0b 60
    0x248004440d030203000c2000094040c0700018048422071084015204240d0700407401c0c801c030a4145005030154040c05505d4050001080b0855a0110700103210b028142d4914004a5060b003040c40b80c0c0c0301d01c0701117100c00d00e560000141c00d1142078100744d07002401352044455004032407000c0044d80a1420b400c90750064150b08010394110240600d031034084e04c80c11410b14080c54040600f403c90f81c00440804050000c1004c9405d2114940c180c03215807132120140c80c0e5402c2146401090752001d000098401d040d04801300e09154070500ca07242d0300d44049503420044508200e814228418044074071000d912a2400105802090010380d00c14074088180d1180c0b680f40300b02a24040d83c3d08110360013001e038911001c00c10070b0348540c1c1861003c1340c07041d648290340780c48002489060070a14a1480c2040c8100000280013541c0320245004030b0302c180c80308200704c010031190709468603020711480700041d002d841254442d580060041141c00d0860402000b002a5591040c0141004980d66180c116081807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 730247077 1250 730245827 730245847
    0x20d0f021009090f0501150309050c060408010c02060906040b071d030d08090c100816090b030403020c01020d05070b0f0c0d11090f030109081209070308040e041e030c031110020c0102 80
    0x2044404c2a80d484e00340005c0d03042040c1d6106c0d102c50074a0b40000c00d6190428101401003e0022001441c2c001c2d0102e6a290f44511055028245000c3701c3c8005100d01800540415808513580d800f4035403200c1000d070b9540343c3d49400c940810210922203001c2c050741340341000540d02041803944180c6e03c0d495000f0f8910340080d40c00d092080b00455075000c0c154032401091160f51190f80560f10580c8280850703017214003168210f0b80720310907411018140e80c000041c40180f40e0005820107070750000341d00300c2c1c0000c000c0030400c5030180513800c00101616082804110b1580c0080c80300c03a40600c00380c2641d8144030445958809540300c1881440100f08002050011400d00d10b02c081c48105045d4000d001d6441c0e5075640e400f0920441002c441c10200e081c020509203101882883c00442e040360343c407a265902c6000310b002810081e0f0b0122036a0314510028655000781008050b600358154880c00b28140541d2003d480343d03c10300f034100425010702c000c545181d41d2188058156043c08400042c0c072469059 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 730248327 1250 730247077 730247081
    0x20f160b150f01090b1608040306020d200909070e030a1a091605060306030f0f030a1e1d0f10020a0b0709050603070302130e01090e0706030605030a020d0f02100909 72
    0x140340e060040d1070b880981c05890b41c028200d14100c84401081c556500c00c000595000350301115401400000700280010501205801030194540500020030107003400404000b0202034901482900540a2041902c41e02e401c51403142e2055003401c25400e01510400040d00b8480c03605c1049680030441c1c180c1c0510ba84800b81e40c0c0e948000341e20010124103200030341e0303014a000c2d58410a0300c141c10000002d0b40039201480611003100c0010100e03102c4011035803416480750000d01078000000d20841c0e0082c1a0541c0303102d40390742030001e80c0f94481c02c00b030001411503101c0300c0e0480351134101c0d034480c502a07a140c40c0c840d080c2400792003d0b070140644040720700c0c1115082c0000340202040100340d44040c8055a240c03c00c072a08807000781001a965452800380d01d0808045500c552224040321b8000540315000c0d07084409441403107001d65183c1c588984040e000c4034543d01805800d588070f032007004018100b03c000c2d0181d95018422818501c1e449a00045a03e05048e81c0c040c0050a10b83d01001652840c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 730249577 1250 730248327 730248361
    0xb04060b03010216060b0d0516151e180806070f0305100311100c051b030f06010e010b0c070b0d0b100f05070807081e04180618020f160b 60
    0x4800a40c41d00413070081a83d0184005040981040d5407440010443d07551802013100700c075071100a5485000c0490031440c49642d5505c04d4000d8103203c944520b0303080f13209041e0300903c079000c1e21526240400300030702200e110f00102d40c50209074001d1b450108200c40c007040250302c41d84540c1e65611075044110402820307200d000e0184a481e601b042428000105406030382c102158040d41c1f020065880c245040382e00e0b40141d50050b125020f05074030271703080902c09070a0402220080e000c603866003110585007a5281c0c030901c91820814841c400500503200e03540000c000d101d2000e01215034164464501d08000e90000030b02c000a203503211840700090500103041e01c5461042d0911900690b031341a809020b500c0b80403c003c02c0c070f010028500c003c0002c0b02080d81c0b9001e9000e0420420200b5540c68812668010300400142d61f2101c800100e6103807440c0106029a0300d40294038402d0025002440041d4204050400701101d00f440000c03080184c9454400c0c07501d0003640c0c8a2140c0c103240d00c05a0f41c500f00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 730250827 1250 730249577 730249579
    0x60e0103090b0a02031b030109053c100302040f0c11060702060606070c0806131403090a03020f010e0d060605130c0e0d0303150e010e010605030108150406090f0b04060b 74
    0x51200c401c0100b841c403000b9075844000400e015035240d4071215001112800f2520040b80b0710404400401c0d02401c1c1d5200c07922650290b0045280c0714204a11030341070321548083c9080c00c0c1c3c0103002c12006042180c408542111080300b2003000141c413a8001816100401088108280c1d50004680919404035894030807510400250070b0034140b0403402500c880f001410a402001c00054410030080e81a04803001841d030781c0309480e4242005928440500c0d9404410b0303032004180e418504480101204440b400d5200601104a00d40303160300b40700e1402d06415142d8107000d066189600c40c0d4444003980d0020030310510000440f035040004100905d0034011101c41800c0c6002400e1500f43d070000b161003800902100c1c4040ea0000301c4c0ba040303000e450440c1441a1044648000107400446000300c40d0603141c9000f0801c000d6a220a41121075001c00d03c90524158000c02880d2035200c807440440703800c240120b2010a9960098907052107003582c2a01c119411928142040207109140c0b08520b541c0d18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 730252077 1250 730250827 730250831
    0x3270703211803030c15060306020d051f121b08030a0311041208030910020a0c0c08010e0c1504150c020907020c013504030201052406040b03090f07030b01060e0103 72
    0x40000304070b039441c0c01404002d0070b0201c2c110340b00381400340110742c107480a05040380038420f0545030b26006c1c01070342081038010046800c080103d40e6000c3e0310002012544118441110880d1800300c003040e02d82040b5000752100d0503510b040703108841e02c15100c2c4015001c3d560040d6503588002d08002c045a039400c08800c1840c070305203c00c1c003132040b2019034103140700c1e00a0030f041c0d102c0c1c84059119007021803040503001c0c118030000740102050740000000c1c103003900030254081c1c9171340d0b10a40942690381e040702070001c13a00540f15803042441c02c90700080304107485416450a003600c40011040ea00c000700c581c203020030040e00d8510110310340108402e501c0f900510250a00040b0b0000203848180e80082c030810050340440f0300c404d40c0d10624180400a0b0345d090058400b0b00382418007038001d060642d454044402c04e4942242c18a070200d00140d2a0000900303018074091410702604596000900a00518050302100e04507420040200401031801041c020500e945080c1000c1c280306500410141498 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 730253327 1250 730252077 730252097
    0x601030b0a050f06060d021210061b02030307082802061014030604020f030307150f0605010503090a08130b0d0c0306080d020a0f0606230a060e060327070321 69
    0x142400c00300f54014000740e0b522501c44010503641d0000c0c0c00394803d011007a000c8a030401200340c0c4240f80741005c58020741c0301c01001c807001e949140814a11400041c5d010740c802c004a800013116980200b00c03441c000c1e012185030344901d801100c06440030120800040c0c0c042001c0c82600d1001c201c0030802040350401c8516400300304030200740c4501004001900c00d0804a0108150b91800d00456121581c844186452604e01001131401050841000000180740013070104942d40aa4100c81c0180d203040010140c4e41259a20004c080d4410785071000008008880003131104000c00190600701000d0402143c0e0503540d00f0b00404581d101d50040c1015800154142441500825003460302a08522039840e6080b01d4100100506003640c80540491001010040c007906c80010f04001a04112130f00ca80d140c0d540d40d4102d8090745c181103600c1e1700600800110300308005402468405800c04c0401c8040e0090295115041004070344c000c1d10324a94580c3c0d8480c058414040c45082c810640c02d04c05901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 730254577 1250 730253327 730253341
    0xe040603031707030f020d0504110a060912050c04110928090e01021b0f0d020a1e0c05060d020a11030f0415030b040f06080d1e120f0e0601030b0a05 65
    0x44001401d908072203000c2c080401d10a40c03190304000e02103003021206640c0c41ca1202284002818104e03001e44084094459101e050304e002428181112100e5a0322402c11781031803c5404030003101031080380c40e8414480590b04c0c5450341c1c010085842d202000958860b9851820300c4000310078040c401c480880041101c40c0c42c080000d0709101035401d49240012008250040340740244106d131180b030800b41c1c44c160203c0c084a0001511184a104c4000b5161608802c0e201665908135290300246a244009691a0050740c8442c84608541c010400c0b03a0820380c0c1c40021400c954451507110b503c41d5000030b9030000700350f0020380303d40400d20044001e5140012848860013103004a00515005210f5001584011031107600000c0e0f2038030000700200b0854040d00f0030300004048903c9940114003903480342a08841c040c0140b20224110240805e0040a14200c201c8004668160100085039030f01d0080c00d803a825489100d01c4003065500074000c650541c1042c3e100c5a1008000714581410304d0200825 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 730255827 1250 730254577 730254587
    0xf072108250507021305040f1a01050f1018090e0c0303120a090f050f0106060801050306060d0b0901200405120a032a0f050106060f030905060f04020a0e0108010501060e04060303 78
    0x4030700d03080c6405a141c410310301c0014288144a00900402070809040c84180803070000c0c00648244151070400c1c0d1408098103201c200d090902c1419030004d0504021185400c185068184d40d15180ca007800c01d03190300400065608d1110340100ca10f095550b0794241d18040d0820000c0c20000045000310304001001a112501540c0101030310144d0b600d031116007080013440c4101c100920b13844010380340000708000c082802844944030303410000e1131034400050030f0304001c02c00500886000d41410400b1b0242c0d02c40440b1075801800310680e96507a8900710400000e003070300c5082c240000000035a655468501040004c03403410b81a820203030024844400000c1d00300d0031090807010901c103121090b40c007220b107194401c0c210760b07005881c260104206200f0404103510480c02c2d60420740b00d8038485090319404504894100308024110351102021543c3e02000015007a03001e44020082e103440b0b0349900319181520002e0f0b11800860391607100511185802c400038a2408105890800100c0d141d9140240 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 730257077 1250 730255827 730255891
    0x36060c030904020c030c1f050604050405060a0e07050d0602040f09021201030f1502030c0703091a04061101180302030301140105071e060b03030a090303021204080607050f072108 78
    0x110581d400982d1302e640c00000d2040d108000b502005071354040c2031000504000d0780a01401151070741c030307040010702207280a2141c240a20340240051132203554101079140102040703000846a80b04813040021542c1d900005d075644a031040c08007580b598581071804804025036048500582d0050264056a00400e040c1a0440e500004000304210190920075062641442d000c81d00c680008200a503c25403034009040c040d01c01c0d502d2040a555501c45502010407560034a5100318042004003d5903104482207000000c0f0704000244100040c480c42c2c0141600390412405608040010845681c0202890105400070300341203140061a940d0041410344884050b803070505039a5200b418424a54422820700c40081c08a075650038541d030018203030528030b100840062040088521040250300309690880e42e07000c00404040e147c40304203448940000c80c80004940d814851030780030400c0c04100800d0600c840300e10414003074001c00b000f484404001c0c820a41016680409800648801c00140e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 730258327 1250 730257077 730257079
    0x6080c130e0a0f0602091003020910022b030608060403030e1006120f11090405061b0c0c15120a0c1115040803060a03080c0606190609050d060236060c0309 68
    0x142d03583d2252800e18024015185c0558004240b8800750300e06c2500741c0d0080110107811240660070f1140d14030100d9580d00003105005800751111040404070b600414500301c00c1c41c0a003404180300b42c45201d05440c10504481c10740011f84c40f0400048000b0303052102082d543e0a8810a00040d410140408000c600d138241c004c2c5000c19078201941031041c600400719402d980149581c1c03843c10181009992440251260207125084c40d101200742441802100c0510742c2c444090039402c4111300c100301c11901c1000e02e05001031020000f04102c0030000030141e100703601d0604009505411040004c2040300282c17898901584600502e05174605078000c05540a58401f107401e070380e0750340c6a0205601680c50383c002800c1d140041203c406d194000f1940c94806c2c00241c0d541d1407543c0710000f00b211050014824500401c041c00780031303c44c07828880b00b6a0101c1d8001c1002501e032003080c01d003039400001d1090303801203000d09401d01a680d0011040414104910860b040c5040481c0c8010070703134407841888812 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 730259577 1250 730258327 730258343
    0x7080304030504080f010b010207060c0b010506030c0403080a090e01140102101d0706030b0405102612030f041403190806041d070905010e13030c1506080c130e0a 71
    0x201098450003c9401922542099452115000030054042c0000101c5540980100200480d14170302c203801480d01d01d900071403141066480c02050150f103500c00f1341200c130080810440800824085070041803020055690301101d507180c061103000441c03041e00f04420855050303440003250780e400a00d18500440750407000810a00c1d144d01c5020441051441001d1030143c204000b851a4050344400100082503406100390f54800c2800b02159049004400c803501109000200b40e000040003000308002c401c00b11003841d031031031281000c680c104450125440c0358081c10441000305020511140c0e03002000194105203460301c030421140d02d0002d1040401c0b0b40c090004829541d590003000c5000c46e0100120507921102d680b00e52034020501030201054106000001c400e400d01d01c240b842080941c441c41c5001d0255a0207c84083c16072400b41c03080700140003822078204040c8564802464080004c1646460507004d02202d040c826021929040c60500c0d1061200d8012800340d0003564071444c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 730260827 1250 730259577 730259581
    0xa05250b04271b0c140303090d0c0c0b0423040507050d0b15030c030615070f0206070807050f100c0201060f1208040b0c0606150c07091e0f090201080f0c070803 70
    0x220700003402c18501c580d1202c400c07411050f151607000350b01d50078094003840d655a14201405034a0355a8803054a008205a1014085048403481400701a5240d8441c0b48001c0742c165560710410615041342d0408000700100c2c102040300340001e01d00500b42c3b0f0318103884c103000c2858401c2005e40140a001c0308444a6515160044400d41d170382044c5030840b03a039481301541c90382003e001095803900201c600c140121101d80d40c030401064071900ba10302c4182c0c8a100750480582a40c00d004040d04003860440300d0010038000100014001d0020781031a0348088014100329609005c504c0035a1059a100340a69240a40030300c00114414528400e40e0419070056004211600d00312504d1710440e400701038201000309082c0721140000c00c0c041d001ea4012580b00c10940c00c103070400100361003800c610b0015940102c00401101c0340c1504070b80065040181c000a81c1143c550b4141c06444180c42001c0e0701503aa45c1130300c401c40d82c04c980301a403c07140d00510200fa0b031402c141700c14141c1c80b500b040541038002c0400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 730262077 1250 730260827 730260899
    0x130c050f0f37030b01061409180f100b0d05091f06062d0c03020c040c03020409050a0510090b032a120607200a05250b04 53
    0x7615003903261014102030a020540c0124a860a075041e003070800e4254032041d00d4030218600c000c070740c00750390b005443c50141e81d01c1c00c042a9042d843c6c00ca01c06691401c24060062503070744148000d462000d00c2d0400e500c091074507903492070403240000c082c0140c41191060a010b400440300613240d100013040303000505a110500514540030214102e06c03191101000000014a50b540110040301c20036290000c0045403840210303910a6a51102035081007201040b03541c03203100f2030350044414020700665101d00f0440d0003103400d1b52000c58280b4003180e0001420000c0b0340180c03080e154001c070a000c0410160510007220b00c10010103110744800107840f801d005100307a409001c041c60911a81c041c21140c040d0350315030783c0001d80304002a248100d014400d030094034403003c540d1a100e060303241c1e90800d01c6042d06070031110307405c1c620031441000e203d1030300d9020004000704854143c28a5498010b80d059000819031504450340d90044030342c503101440300f0062801104845105000d241000c00c40c0042002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 730263327 1250 730262077 730262089
    0x804050a02090c0c0d03050618060d0b0a0618090809010507061506030c170108070b07051203250e1e04090c230312030106050a21020909130c050f 64
    0x900040d611102e031a0078031040d4064071009048580c03402e015100708020305541030701100c501f05d404d40c0d001070590300c40608002d082e240080d40500d0017000b000d416070290312210b0709018111100340ca62503589034180040c407050f0081c50382c0b03004640d00c20300c10300c05230380d0f20060240117804441c0e05000340480d0307102c00c008540d0004204c000e590b0280c50486582e940c3c00a011b000b9860111000c0342443c1a400d401d2000c0100803416501924000e203103851030200703060b000b9404810f054505000e00700803400e900500c0d03002180502070240c0000949010038241009000d6842c4a01041c080c0445203c0c180d41c48144400721070f440740741c0508401c0d4120801150142441c61001000c816080e10049640c20000e1440494a441000c00d01ca2006a940c00d05682d6200090f200700d185400748010080c0c1440b40008103504651880c10507001c40d00c044040c7c9a100d0464a2840640e8001c1030b01c0c141420b01902c03180d032156202101405003c42600d8619410300203001d02d90081c1d480703441c03400d80c41c1c507030f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 730264577 1250 730263327 730263343
    0x30c100c27170a0f0302060a06360e01291806010305130218040b0a090503091c0219030204050a02090913110a0e0906070504031a04051e010c090b0c03040501080405 72
    0x3040c0030b0a1204d680346402500c841080340d0741d84a039854a140407402000b800582d4400004001c03644044907107001d48038954040340b40c402c940d0b6549075100208414000e01401011003010b002061419400650715000030018060141c00b9005091410804680500e5110740208080c01c0000e12611002d5820b4441c141c10301e0007a401200140540704202c81c50510a4401d034041d00e944080344c0c550703500c0f081c25101103071409425075105018032025440d14400c0744a0124420f180f0103541d103455804248e00c00c84141e9014004201d541080055044c07074059940d10032030a060442c9040340020000307403104000b8190148118400e0111030402c840d0543c0d4808a000c000c013440c031110744e80e0805419440d401c03680710715103019820110b207125020b481603405032603109801d01c160341e0503001c200110f081c000b40240d68610807140a041c00b16082c0c004003070344a0040c0008a0a40040e5202620960055000b42c421a500300401c0840000c00300039030302624000d117081c0c1c2d080c1e1038a041c05454001e003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 730265827 1250 730264577 730264583
    0x50f07082406070818120d0e0a1d190203010501080c0d140c0903100b03030f0d2306010e010e03030301150201020c030d1b0f0e06030405030c100c27170a 67
    0x400514034013401010406400034518290704000d24a4800c001d202c000201c21b0080d8489a00c000090340c2000e008003192103080e040500200b110a59800044a1001952070350300740004058080c400c002c1c410705072011422002d000198510f5140000082640c000284042d94480f00480c11002207038180d003120113040880000202c00c0c0c00c02d02101411540310341342032440382c4100c00c18400342c0c030107034050034296500c001c01850030688080c4681145a1091410000096a42c60050300741c0b12030b141611000c41e05251521140c0c507180c1c0000d0800880c2c003d453707052003140c0a81005554000044a055035040224003404d02a400c506030702a0013014064503040c00042070400440c04150300010070a10f410013840d030390402004050740c10305600130004001600c01024100c0d5030800c6401550400d200e68201c07454000b440c81400c0c2481080e8111104454541214203800769014402e0709045007108841d1078010740c800c01030b1081045510440d107107030926000c04441014140302d800040c0da0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 730267077 1250 730265827 730265839
    0x108090c040e1c021c0818070605040f0b03061e06040815090d08090c01052b0501050f101d0a1503020403121d090901022b050f070824 59
    0x110014107282c0340c00c0b450750000840782d10250034424203440040c403011000c42032851800415800e200869603406d00a0000c51020050400406800340800802c8001c00745039603150380761400c0c80c1107905a2440d80d070050199420174014002103664400c0884404215044000361455042d0041441802141c2c0b00c802c443c02803200901e00c1c15500ca070f075544268030f501e09076020000c4004003940e0040c4280c50941580c0d11511601a655001700010030020314041e07001009842c540a810b110101c0d40115803d1054862004100038102a0340010070420100e5200705040008079005162503025040e200b40890b20702d000c92035a444141064000d0002507001065007000d400c0302602070740c00f51004a41c4c8500c455080d00105100c0c00c0080245000c0f030f100d00180c29148410452000030107000a0140c0d5400c1098008c0303100a1800e01d859202d9000c00c04075a660b0000101e81200e000500300c0001513000420001525405802158804109954040d0812901c2c584021300c04440050390780001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 730268327 1250 730267077 730267091
    0x50d0b0a0b0c0f0d0f140d090b160201110405060d0b0d020405010b070c0909020109051e0306150a1a0912031e0405120f0304170f03040f18020301030b060108090c04 72
    0xc0225844049074030300d00403101c2184444008032400030001e04045e0020b4403191203242d942841e4402089140241c60010039641007603250610010000d6805078640c0b1035190455891903020700490080d5640307516041c2c1002d1400d004aa1075218480403100d00f550b54200c2108160341c0c3c020110704464000d0010080307503842d20f02c2c1c40600c0d40584026503808421101c000758103109409020b82d0715034182d59505126140505004524400458218488038000e014188a4508100d920312526000b14218a108440c10600400341e900d6007029030a0740100307041e01e00019003603080700d03c142e01c183c076101424031600d13030043d0031030203003451082070001030440d2a901700c0c0c1b41c200a00180d031000c803030927109100d440c200c05a80b01c031781403220f101c145c01c01d010400c848640c8060911038042c0302303000d90344214011000d07241998050b4002840010840030f041c064060085000001e03d82e452804501e1541540c517103080b400ea008140c0c5040049400018010410602071001028009031060000c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 730269577 1250 730268327 730268347
    0x190c0504020a0c21090b130501030b030f0a0b010528060c1505010f030b13020f090901110f120601322104110d080d0b01090f03060f0f0b01050d0b0a0b 66
    0xe01c4c0700ca582880090003d800209200c0880740071240c241c8220142e40043c640f03000015030140076501e11807545030041d1100c0c42803400d4280446421584611110500c1c1d604000070000c8c000d4070326802041030004c90005200030400e0110080c2a075466041081c80010701d17240c080c0400c0b0302c582d0340790b074a00c2c2071000000d80405407922001c2500d1240e0441c1000d0f40d035900c19401d10042098010790301100420003000c540c240303c0982500000d19000101311801c002000d024154080d48450705e08880002c3c44000d480100084981c0005091800c501d98401035660803440c8107141d4030552420a03c0300c8000c1311071040c035046482aa12902c02c140503010450500d0015510850303084c1d03132000300c2412008407450b04074841c0f203a1550211200d41009407e01c2010014034408041a0600c110041c020401031401d840c404001c521070312010440c00f1140b42001c090303508074400200c0301e50501c455104a03031381000a03642e000070400e00000b81c46141400041c2c0d8222554080d03810b64500003800154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 730270827 1250 730269577 730269623
    0x1506080412051215130c020606040e1f021c060602010c080c0a1706030a230d020c01050409020c01060f1d0606030108030406050705031218190c0504020a0c 68
    0x105a0184208400012030788000b91000d00c20100456450070074840041d4200b04140c8910709014409020254056079043c82c04040b90074150548015901c0001080424900760041d60100701c59880600b078000070390b01d001c0030300315003542088401507004660f10404402d80d021402c2c04600143c03050100c1503680310080d000307045c00109500000d80e89030028007183d40c9801122407400882d5124080242e07146400224039030040c181aa060189810b8013002c035401070380840010341c1c00031424408401b03501906141c02140034800d81590020010106075a800c0360039a011222002c002603540c078400076001d401480307a0b0b003060594140400010440501035448006504901e96141d0182c3d11244204441c9000912800d10150310130003080c00001c0c4514040d0180500c56170841e410300b00e50508955030f00b081107900148860b010990300c1c05510f800c01141c10b150b00d164610a906040030340b20042c200660b8095140034039000590380c031103c0d206161407003620b078010100040c0141d03494a0107003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 730272077 1250 730270827 730270831
    0xf09090b0103080708070b130210080702030906160602030a2a1b02010c331109040b1912170304230c04020c0d0906020706050307030c0c020306040c0612020702090415150608 76
    0x20180c02b40220f85440580100d05030350149010360011030620324180c08200244d4000c1e40b829008002082c0014001b880da40003a600540040b5808100c0300c0448142e0350398105609243d541c0d0106404081e0b0520f0340050404824104510b90012140d00c42e00058842c42c800d9071008164540c00403d2950826484980303807107007264903102041ca80183c4030180190340c0c0c69419008a40300c1044507070070303d2509034880d40790080d0180c0300c0f02c00082000c0c2c246040b030003541d000300c40e420b54440140c010410440028410400301c0283d0505504064640c0e80329080c4800c8403481410001c05820701d40350041200e0040200d00500c199507030521080700075111903e603000c4c0804562198004200c013030002c1008406e135107860355800d08503a6101000ca006e00266103100e02889011420313180562400e100552081d8001d00300b044107503180c10320092955011a10700307066244188140e0300140c0e2031a412a030440c3e08101d001c0020481412a9002070840d09002103081010b8080050040e400c890b02d64 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 730273327 1250 730272077 730272079
    0x702010e07150806130e031b01141e04060209040f020d11030f04080f131413020933070f0302210a0f030f0c05040f09090b0103080708070b1302 63
    0x41c101ca41e03202c8554894940071400c0c4400318254200140031130900c00841441759030b8800020915000c410b0205003154409120440c110a50f11040ca50040d001d006414006d000101070701d401d45005900d02c0d003101d00008502c2c0700e00319541c0109003805141c1d019200f1100006208004044201000c0002540200000011030f401d02c0005141800040166417044400c030210039000e81e140d5864002d036134496605121604070522000304041450302070b2001070041a000b1028010340001080306104448400c040380c1c5004100d1400191174031240101035070105111600054400c00614004c141025045030060001180d00303030030b101c40c1e071400088550103a0255090300820f03403e0b8800c4100d900c10303000f5800134104000c02d0790710310a20000e0140340080c03600291aa0001700380c041690308559076a40028808101484030001045c542d000501031150100840286540d840307040300d00c14400501421408148402813000746000c903a051503016140d288070f4500401041a1140200816 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 730274577 1250 730273327 730273333
    0x1e030c121302010f0507030c1a01090f0c0219030e180105100804080a0e03030c07170124330309063c02040b0f0901021203010f0302010c06060b030702010e 68
    0x1c104110341850381003038901c0d010b81d1030b20f4429004400030354240d40400f40440801c00c40e8210040841e040c0700c4078154a9408420000455250609440c25901d0310260700300600e00d815041035200e50005101c89100e950469419036110190606888040005074090b401c48034000c094158a074001a806041e11400c48094125180d40c40049132035000c00c440061551302c0070410488940e0203030305002c2c1504001802c41c0d18083c115281581400040e0740007050440302d8820f020080d490030b005a0604116460a000c4100d818a411030b80440032841204a2441d0340341d41e012010300e00010703d404000400c800030030003805040000b401890901070903034080303150007842e01c8400041212595106111440c0e0403519a15030080320744215000c8402c10029800c000001b05505004003915104800707880e002d4a0300c21940029040004d00e00303010743c110608000600000ea0714442c00c1c0d0a80341c0a20f00b001207101e841c60079034004c00c020f82010f064800040b0800c0555a41500b08010840660341a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 730275827 1250 730274577 730274581
    0x90c08010609060905040207020a2c06010e0618190f0e0c0403021e2b0507050102150f1e040615140303090103020f1b0a0b01080616051e030c12 63
    0x121a0307000b03540642030020780200020421403501c5d401600308580028000700d11150303250020000700c1c20740e241c44001044400c485452004030700c19455406402800c040d040f00010b0400280b01340325585895600d640009241042611401301c20714843c00c08180d40c0c003000d62140d50404040007a4442c40030780d4075441001501400f0003100342c40490341c0c0034105004014640203100030300e4010809040c3c00c00200f0004d451b0b4484181e0310580141041e041c1441405004c3c1411400c08055400880c15507004a80a64034500381000541e80444d4070302c10b020417615120120b5041c0802c0d140c034011240a00006d21051041c07da01003908080a50220200147e8a201002c0c0311940c480407144d060b04140000c030110b50182d0020301485085100b070301c0c0b500b17070b09400e0301110300004407843c01e007540306035074480c01c0040130048140949000001480d9516110814030351060111941004001000c1003038082c845098410405210315503140355241d180c0043c1302c0d00103400000a42d6020210800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 730277077 1250 730275827 730275839
    0x1018260106060e06040b0706111306081303090608070e060f040503010b0f09072a0b340e01110607020d1b020d03180b030c090a080f060703051008030301090c0801 71
    0x10b5080c0f003c6018254078201850030807041090382286005442c0c698445e20310302a901810002031201010b1509851041814080f0003400c1d0300005240d440600208610f5001182e0040004c0084500e586000f20150307550640445016401c040015044600412000c40500c040d10123001625400d800810000301050100703c902d02e10b40d1245500450120003044d0500c0c03044c0c0c2c4d90740c0c03003440017030300c1c080e0403d401c114910034000b013104291400716a074801e0250320031344103c008040b05105861400c1008011651038420180c60384100e00b40000b0b030b86130030601c2c0d01403071a0031000c14143c02901c6035498141c2010352600b54061004000800361138402c0d032020290360518444640161880c2294801a901615006030404800d1503003800280001254440440210b11441d041c0203104d442d01c0e000000e0201040207a001580c1076000a000081d00b82000108594002c4940c540420f0b251143c0107154020038103900044510b000000c000b0460310390680008610385000e03501c03c0d0340d0382c0e40c841c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 730278327 1250 730277077 730277087
    0x60d020c03070f0c0338060402090a0803070204112b0e061e13030915170703020403170309100506060d09050c030f030301210201020c1305060a060e101826010606 71
    0x2080044081a070034107280012406c110001d94044005000107162004410006091400ba070b40481000d42c0005440c000b1810075000c0c2400d4884d410900e42e081801c0290303121312010240101c81c100400c05003a04400003c19007184010304401401c0e1041401c1c0410405200d200384610040d5503503e050100303014090f07101504405640542d01c254a04e42064140b11300c1142882010041041040828501409913100903000c0e110712b07180140e580d46140341c0140911850766003912610b4062041102e6104080385e81040451100b900142e5565481d0004090303001d140d4000044a2a2508510802000180280b0342c508110202c8418034540c0d08215a2480b090040c5440344d1070140b1540c1217000c124000c20707200b40c07050040d111244138560104020010b0103c0103052283c866040c04402d0400d9060304014181528011940c60488804074029035114440300b4100075104041d13014200090101901401030004441200a801c01c1c0034101010381c00040e0920754602240090258011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 730279577 1250 730278327 730278383
    0x31213032a17040906080d080109180209040c0801050901020904110c07030326190c030c050412050106081c02061f030803070e0307080706090501080402060d020c03070f0c03 76
    0x81e00d411031101d9502d902100350141e42c007040d102c005100108012501d4001e40001c0c05001c0000c00b00c620b40220010250041a806103261516000800d4452488400100b05040d010350b40d50303203162104d01c0c20403141c18030341e4409012035103030009021101c134064006084444085400344211500e659007107602d803084d0b440c00140c070f40c00b5401c1000020f001c0c0103030030700e020090082100000490312000103180310403100c00040343c0300400f1000c04034285210f800c4d2007180324902001803030704000300034042e0311550044191454440103030707004221094010324081c2107030070b0643c0c61845007003041f860440010301e14030016011301000600d0482d902500ca00350039520601c4100b10300c0c59a107501405501c041c02e4903040005000c2c0304145501d003002803600801c6040c008090403481d01d41d000f019020590001c0c0c0c100030300b01d0240400341c0c0d50030040e11000000203000596030800c2e0036900c1d02d10300c5190002450030380400b2040d4184049180400100d034056401d81c0045440803410f01c0c1150740e8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 730280827 1250 730279577 730279637
    0xb0430141b12060a05070c0605070f2d0e060408030f03070801080d08060103020d0e0f070303020615010c080a090527010609030b04140c03070807140102030a02030f0c03121303 77
    0x8a40c3c0011404103440e000150003c00703d0508518903100c94844130203513581250340b040402c202612000c01190f1201385500d010150b040c504c8000b18800c0c4c440c107120b56407500706400b00940c3d80c1c0b1404280c2e88001c1100e00400080301142da4034251001ba07904d540d081100c00307201140c400c100004c0c660001280c15200c001c00c1d40d031020503070307540d01d00150005d421002030b417004a82c0e54450707104200c104119005122400400501140c0c1c5585402450180c00a10007050800c00040c04c1c4c920b82d0308801580c00450380402619120031019000312203041d81d036441a50302291100c041000705480c00004183d450085694946581e221034041d11104010b10000344070712205000940071800d582e510201024070304080d280b00182c4200001d14000c460f8100c00c0b07150304496020003c000481c070b1402e0081100780095401d286a01501035140d004400c2160005003002030340c601c0482040c0102c40503d205010400850b003460411a9000611480100c02160a003082104c281c4d881c446901e50090f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 730282077 1250 730280827 730280833
    0x50103060312140409021c0b01092114150709081207081606020c030d0e010c0509010810082b0c0b150a150e0108010b0430141b12 57
    0xd40c404851a039800300032600014410301000c13417078604500003003407071900484d0038552034685901810100e40340480514148081c0400c100000042c07c041c0b000d03190341c80c0e000c01c60300d400c280c10610072005a10100050501440a80184203001a00194041d034581c0e610340754600c5c0c8407160310340c0e149401180f82c0b00416007400081d00040e0803400038480259107103c078160070703041f96035594241d0b0070800c5031030102c2d0008964044405500c1c490b281d0550b40e444028811540c2080000e00103102d007501445c10818801d0000c2e40320030300c107100b0740010301020080b03c688891428241c926149024240e01980c44100e0031058001c0c454660404115000341014035a81c0314642d074501b107450780b0241540c11010154002136003000c0c082c0c422001001c50f44070300c00c0d0014003000042074600d0580210b803202d0400e2105002c0c20040312403207030740c0303422142c4034841085030100c81d000c0b07106a00e10020081d910903042c6c1c61190001041d0662924401d012000d0903484480801a002400060102e41a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 730283327 1250 730282077 730282103
    0x50403030e1c02090a0c110703110405130b15090108061b0d060f0f030b06090103050c090a0603120f0201050114060708160206030109020a0e0402180d11030d03150501030603 76
    0x300c0d10784501040030ba030340b10b1003901048050303003c0b4000c2d00085900705a041e603542ca090400c00c3e000b0034240500d030707000f0740034060a034117690700d0500148030402490b014035a0395000071038402516001050091308011000b0881c40c001c1c0707010000203031024500d80240d00080001482400000e02c240c010418200c0400740c00303007080c00021180c1c101c40c00007100103803102400140c5412000d00703d4058504903030300802050960412030840d401c080d024600403039144004001045000c0b90795503170084100c44210040e05c4078080c40d0054140c680000e00100c115004281896030401c04420b080c0c100ca80092007079a130b07581440d0300c03050075440c0f080740c2080e02048640c0c0000c100b0300040040700c0c0300d20303005020004180c0100d543c0c1d40091700f140882c0c2d50f00141600100750000c10350204a0340031501503151094101c500c0b903502e100c4a0465009031010715030700e000c00c200c00101d41c000035009002c0301c42d074070f4017802c008002d004401c1c0206403d009001d40404c19522074001c0d501544d0300308507482c90349 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 730284577 1250 730283327 730283329
    0x31c0804030c022101060302030f0d1407051501060f0e01030b031002030c0c06270703020a050405041515050f06091503131a09151b0a02031902010c020d050403030e 72
    0x40c10140c0c000c0b0f130b0003018890502120307074008200e10740c0c540003580005500e40c00c1d072040c1841c0108007809196a84d0102c1c2c044070000b640000140900c84040000680701c11030f514041c0d24000701a6503c0c22401000700003c43c00d55401802d580a51003540e503270300311409136a001035048651170090785800d50070181d04410f156a00b50000d5410010782c072006c503d002e1030007000509101c5d0544148d1040710150018801d039010b290404a0b019401c4809084881d2071540090007600561103142d001c0e5890300002003d00284c0d03a4060f50140b9040000e00918030006058843c3c8004d50040e28442d13070041811340141d081070402c0e40c24224000d040200d803130740c400c0d064520907040100100e0f24020b14a00c0c01d8000b07104030640d910380418200c000b10660070320b0402c6c0380c00c05144084001007000008100007034005000031024019004100c600d80d580341142c0200c0c154891000e546500748840c7c43d0300360742c050341544040c0c4400e4290b0300350341906074000d60440c0c00d480b643c800035000460800008200e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 730285827 1250 730284577 730284587
    0x15060806210703030207081506030c100201020705010c05131a0306060313050f010f050c090d120320070302010605030a030207050405060112090b0109110702090103122a02031c080403 80
    0x194442503101c81005140e40004185001d84940086005030410802000002400c008100314900c0c0c218008146103481400f01e9038a1300780c00741c4188604407401c0c40c060054003e5046800e5503401600901011806403c040c00d164000200c4c4034284444007400200381c41070310b9011f008211440c140914584132941040215007000d8200740081100f4071845000039002c008107400814400d0001c5601044111681c2c21903400804003200180104800315081c0e07220a900103a1b55403000c44040745881d980c1c8224010102842ca150748103030505074070784410f550b12006e00f50032442503000b03200c03180d103c5041c5911070200342030003409648400c50500c12490241c12540e4449018585242500c18080b41801650045e150a4070b1040c01440184203030071041c000c800045880262642ca048901d5000c03600801d014807000d40604081842c242d4250311420400c0c4c0c00101500d00b040c94601c901000902180ca0510b02300e00c41d201e216030035894501104201000c04103981c132849039640e155182500d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 730287077 1250 730285827 730285849
    0xf0115050d030219081b010911040501060203030601030504060b060a0c0611120115020307151506080610120f090b220f1203090203030a4b0e2215060806 67
    0xe405c28140007843d10320703d001c00c0c58601480110004149442d2a05200e041000031500c2079014a05141c01481031680020482e5000003007860001103664030750601200414012510f03e40c0824001100440140d20103000007a05010f200e04106491161030680718500c68070021740480c01c404001080002d001c2040b890002510f40142e81c40d00c041640c6503841c0c4032041c0110380006503250201e04941400c551a680a4251030030700c1006824140d00190031103407803e094508026803c0010080340a417604180e4000c401850244000f02217440c21400d81d0404561006040ca600000410304a05021840c2005504041c41e044031804070f440719020151040041030a164075070010000584042004040c038512542e60a25070301e0280080c9100101c03400711403841c44104c21b128400005461811100444d041c8076504100c501b4070509480485112005d581e2051880340c05010440040441602ca2104c0d01070802860f101041c05403800c0040b805007500090301c100020b481410401e41402c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 730288327 1250 730287077 730287083
    0x1005132312030d06090e010c140f07030912030c150b010e06070204140a020c011a060a110f060103051c05070c090506130f090b0907140f040e0f0115050d030219 70
    0x40d1a0031420058032080c0c1d000342d8411056556504651b0148442c00c0c03090a884000c035250a502070201c0103c85075881c011110b01204000d800541c0e0740c00c00d80903ca10000401c05406115004040c9050103442c45003054000d46808104841c4216101081d110740d10740c4000585070080120802814000d503a04441c0003240c0042d59031b48501001c409034074605108400c100c1001d607441144200c810f003075450511128050074034910036203210741c2e10101030b503080d0b50151401501601ca98141c1398549490502d02040c0d40c0520000070090080120321801e022030894084a4040d4405030110749038840d0355000740a43d1042201440300c1c030020340005801c15801059268515411900d1800b204d8a040d2402c00d0030741c0e40d09500d820401c2118507207030b000044501038500c0619200d50f19450307008007001d03a40304080c1880c08520075951540003030401144a821141407100040005000304111126051015030207000025a490805d04a080203649640540100c00c40542100890304c82c002e811 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 730289577 1250 730288327 730288333
    0x308031008010e011b030b0d1e120305091501180c090b1303050d090815040201021609150e0907050103090501061a0a0306090203040b04030c02010e1005132312 70
    0x4071000240200030408030352a0000030400c0382c03c0210014034211400e11414581001d0b41c00526544042c0c00c81409038000c11040600c60027820b0710303c1d00f4007880344020502c07590914001c010355410761001d486140c3e0036084401074107103042e0360b00b40c0d40801d10440902d0711441d20b62480381c07015a0800c00020030141401182962220283d568540041174100d01401c032001d400c0083c00020800022400e489007402001039082040031a10754000200d2007070000b00240c046030859100b001604140001c4840011249480d00b40b0b242c05004485440002c0120410b00442d01510094006006180801c01031041c1484c060064003e030890a400351429540c4120015074a21407040c4140344041031b400f410351721100d80001038200c2d0960380081b1140c0e0f02c14000c110014901000183d0456094205082c1041e22480104c69400e0803109582d04030f00311640c0111040c0d0824043c15000764520605504a510f035440c281c6804280c0000586d0f000131610055854100302c4600e124906120080d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 730290827 1250 730289577 730289579
    0x180d080912011e14010506030c0f1c0f1e1406041109090f0f01080114071b050708010618090c0b0c100c020c040b0402030601080402090c0c150a0617060103080310 71
    0x411003440d41d03c0c0c401e0700c08007500c40b101c0104680700d03004040c0c05020225013803800d40c02c0044420280707008032400c421000d80e0000c0c10481c443c8103c0d03840004c001d524141840401c0424840c1030290040d0b100190034002e200203545640a813502543d06003903d60907001c2c03031680e07603801007002a0892150001082c2020000100741d034442c8040c0701c1c41040046100100c07802c081484204170350050380098802d9241020780310190ba0424105908001240780c0a0300320121044c12075003600504200508501c104400011004030640241003180e078806928061101504101d0083e85c8880381c004003c0000d080041c000c8022110117400c03a0194401240d4030310819403038007000c07a204001d03e240503034400380c94403806242c2809603d600c200d041e40c041d810341c1040b10018010810103000280300e0404c0c500040c040c200c1e14419100201741b40d01c101c849020300d104811b444000142d030345611207820300b4070124140c115410300c801d484950301d004041c40c1e0b2840e00d0700d007081d403c045c000100d01003601c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 730292077 1250 730290827 730290851
    0x180a020405120f06011a07060506041d010b03010c051312030c0c1d07050712120e240f060a0b0d331e060e24180d08091201 54
    0x20440d00203504050050500c3e212001c01c65160413416408407080d00121890351007006984015144516446803020030070317840c1c040016016001c0708060448031416042c2c003690400b4150005854000140c000304206ca0101c181100c103445003050304e001500b0340304000c111840314002c04007400d07402840c025021003140e5540004121030b0b0340c030001c80049240d043c091a800300f4000c80d50040c0d12410500d150240c0e41c1c0e102111144c0554040c01842401000110144066080b02c610307000440181c40d6044800605c1c44641500034941b01c0041c02d102000441c9942402c083c03030b00420008009002a40c40c1c0480161294040c0300c1c0c011a885c0c55407094019130f2800d200d00c0072501800d40302202e6905607560351040d00003003a80000c2220312000510064a07025502d14001c0e42d660f07103005034941e0600008140342102c200060340010722041d01211400c0148005004154000045136011040100030000314a03400e880c00703041c1403020400801c0e549400825100549049030000c80c0700b4101c09 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 730293327 1250 730292077 730292089
    0x62001110310180c0c03081b041d011202090c07030e060706021b0d09180e0303151203041503050411090411131407182106110306180a020405 62
    0xc1e030b003440d0b08500090240454002e0402d2000d00b80703041d400401204500820061038011009070240500004401103180310020612004a00d02e94020080c0c1d1541c0e42c2480e5607924400303280d640e03620743d00c5000201d011404003600304c0070a5001090a016600c8107030f2000d0040c2e002c45822000d01604c0c40c0c555280351500d60152141e10b028440050300e80e80c2003220742c0c50f8040001002c0d00c1e19082104540c2050b0b4010700d503401075400084481e02c10120b400a9200100009401c0c00520321000c4104859071460784403000b81c4140035141e80004007024440c01d99680118010b120940c2c1007031780c0300c1650611951000341d109001d61580b503410004500800c1b0380e25020344045d40c003201e511042c5d28650500f040a038030092881001040601405182c0100f4020068242001c1010307100e0b200100c0702105e4031140140030282e140f40c00b60f95182c820b512584500007011565070f801c10380d240c14400358001c141c074800c05001e40607501808c888422240513241c010019619198240004a00c54860b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 730294577 1250 730293327 730293331
    0x130509031c0c1d0907031a180105150304050304060e0a03150f0b060f070605100e01060e10031a2e0801082808030621011a04060620011103 61
    0x10500190042d1880001003002150154030000c0581000c142003590b1a54080325a200c0c0b002c0c40c0029001e65220800301c48060007405403613205c1d082d420385000407500c03021610704882c001c6605c03904d4005c0c0c051a0260600046402416582081c003041203075601440001480d080020003018a01d0f8499985801c03050440228101c00ca5650030350741540c80040c800c100d0445422515141445000443c0c0c030041c1c410301100804e0f841c0c5070700205041009850616002d00804c02506000750386990b8010440140f04034014428166078000c0d50565000c1d21070301c064036803138085180e45a000d11052114640302002a42c265015400c0f0241894007100d0405040c007041e07070381e0315849d03515001d0300d24035003c00c0d010140300c11030300800241141c03130003010f0004074076510100c0d5949aa40310390000c1e500c68000c1041c0c0c400004141d0740320042c1c06040d4005281c0320301001000070003107203e800b030104a4a40e070294102082c8081d4041e82842c401c00208082d118009001160495900704601c58680003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 730295827 1250 730294577 730294627
    0x804031403030f0901020408190f020d0b1b0717070c18290102033001090c02060f0411010c05030d0c03150e04020a05041d0d020c0f0f13050903 63
    0x100621400b035144829182d0401302c4140254280703800d003400e0640f0f5203007095440c078030751007a4038400040006500010040d40c0e0000c000c8080c001d4a41401e440982084031420600d24484a5401560903080d00b80c1d19015002451035901443d58550703004107500100003030b10a51b02c000d00020700600c1411090340d041a460102040074810200c080100c0031140e00c812400d41007a00200550366800002c1c0c8041c0c0d9402d100c9198010302d40000c05040304015007102143c0400072002007000a030301d4010b031641c40c44076400c90741c1ca59a45c20a0042c0100162001001000c0d1a04074504940c41401c2000c2c60500400550389002d155210040803509142d0141d00400d071610004800d803140040420010200d66540740c0961911758001540b20015000c0d0600c12580c032580701c402d2400800d50780d001800b4203421120b41908200000e035941107008a8144a062210400c103003d0030541c0c03540300039440c040e0920951201c0150b056002c0c0c14010b2080d000c41c070080c002d0034800e0070055100040010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 730297077 1250 730295827 730295833
    0x2702100c0f06020d020d2d06030506220c090506122d07092a0206070503220515040203120405090a091a0c0a120e0316030504090e030301330c08040314 66
    0x14424400300001f4a03014422044c501d040c0c0c04001207000880c5180d800346604e101c0c0036801d0b405200620480b0030300b0130060904c446410012030559200da220318002d402c2101e035000618020503a20750b8404903004030703a0490070b0400882540401a4050a0509601e07034140e50f07100da01d0b1600601100c4030940c907032018030795241040c01c0302003012908010f01503d6102500151502c03080c040c0c40c2c0c2c880a061000c50711491141581582407101000c90040d038400d088e0368a0444542c14207000040c10389040e03200e0300680c2803916010091908580464001600f85480c5075101010340008001d85070040d142c0b02c038000340607841c0403950594030341300b40d00c9007104a48628500c00014085440402c1d100022441d0072681281c0c0e10002055a1140240803034107550724005183c11502130160f580101c503c18200407003214204004006141615410000e247c00380c0400191001500482004609554007031009120010b124a602520040c09808107a160590302d640d0741c1e0082510341c404160b02e030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 730298327 1250 730297077 730297121
    0x3090201122c0312042616140118020f0a1d0a0e12040e043e10200a02090a0606021c0f0e042702100c0f06020d020d 51
    0xc0401c444200d00450450021801c0c43d4501d110120401c4002e04007a084000d0580084509205488410882d14040c8211b9494080d1860804203010318100b048030452840400c0111000051203151600c00007146080803002d0541c09200003d0100040300e904000100004141200c0102c218202c00305025420109481d20b8490081218003502d4203403801e801414000b2002c20050b81a6402e0362031400902d04103481b10715000710006146046143c80d030850500d0034004406402c5000d03441c11925882e11155048102000401500005584007107414600e441c0354208034011002121500582296035401d400d40000b114903030101d42a4076019105d000510045a05100c125800c1200415400200341c000300702500603500c84860804125407201c005e2030700d6546803c94208000c4014040104460140b174500900d45803000c2640198040100b80000307510071b1090402490308075400900728a111350303551300a1350203094840714040d002c1c0440400c1c40040d100b02ca2900c081f24011031904 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 730299577 1250 730298327 730298381
    0x1e010216231209220608030a090e071218020a240302030c0406140f16110619080727030308010602120a050f0702090f0601020d3908033303030702010309020112 70
    0x30f460327581201c0201c1c05072005001040346c0100103001541e904030004154003e5506104401240e50880030750301801c040c0c40002d104240c580315061080f9182c0101e00c0705148280143c01381e1000380d0300d600d00a9800c1000300203851050b44071000c0d0118001c2c40500e80b4001071001011a00f03e41c046070051a6401814000c10107014140c0d5403600098400c14284030b0040c504c1070010703800b1140d190034400444001050315100d0814643e07100d08032000720900a5003469081291070f82e90000b100440d40740b800108085000050b0001032140ca0341c0c44070300e4a1400385007107070b00d1380000507131b1f1a060005121400059035003000c0741c0c1c86a01800311000883c5080e0000916100201c03c480d810b0120180c0d940e242003920220501d0245080302140d2840241e940000000740e00c14000a044040d01000340920a1410044190003201e0402009106211030b441004002c1c400c200755135044e03004000042c015406604403081d0140141070001d40010b0003901c3d0fa09555608101e40c01c000b8058150482c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 730300827 1250 730299577 730299587
    0x30c060801080c0d020907080a02131403010605010c080a050c030d050712140105010c112407060b031504061d010c0c0c090506031e010216231209220608030a 69
    0x514401200c9a800002c4c2c2900411302120002d0003a00400422900043c07081ca480d4046031041030b401340c2003403080c17540c8100445a0b2418485000e02c01d50800c2c0d800111584a000c80c100300a4200c100325141204081d410303030b5941d000c0c100c0b8400c0b60100b400600c20441591080c20f04c03440300c5449041c001080c0e42c8007403040742c50070403044000707514a400620090340e000c3c48d031581490b03011905405480600c40001e405008815180d01c081c180049680d9410700070101130840e05205102c1841652100010144c5403481d84000c1000070750200300042c0031510542005458803840c61085400b02000407440e4203644003120444003140d0a103060f40c0800511443c83c2d0700510030440200850b041043c0013941310100b0a021a000c101601c0102072111006c1d411030f84900c104010b52040e03401c480c505a40d4500c000e00904a0240500a8001202c080031a50039a4818040b54452a100c0014100303d002500c0c81020314181040707142c80200845c0a03c1043c2c040c11141005640740c0c2d18460700104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 730302077 1250 730300827 730300843
    0xe0d11040515041b0e1e06181923120f060714090607020405071b060501030c0605161407180605100c05060402010503061302070b040303050603031608030907030c06080108 75
    0x8013000103240c1503903030340c040410740b03014800302c070400c4c1e08204044420b65250200411070342d104030001105c40101560000c1180c51010a545203200390012180500000010740305081c0090030100d04502c0714111103e5050310440300602c015908400140001e20b405081d1103d440310f54440000d001c20141c00114242e170920383c2000440c54400880c010a0050040010083c0920b80340ca02248649000d030000c0b0b03510140100b00d900302ca200506207140540000c1c4003e5a096a1650707001c00e00a10540448100341c09010400c100d00700c1303035130b1640c4030103456041c0410140216400868041819502c00f242015965401708040d030800e420891142100407140b020b201040200c07d001841c0070911507030041d02400e04540304e80d1610081441d107508018124515440001c0500400c1241035500740224080e590420175a035901041c5aa40c0c403410300c1d0f003260312882501040004401000465001d4151410b0340e18141c0da070f0fa00e425401d54507410080104890f88018045c00c1c104100c440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 730303327 1250 730302077 730302101
    0x10905060709050d0314030907051e010e011d0d05101e0c020607020703120504050607050609060c03010803040317091f170c0a0e011808010902040e01020a0e0d1104051504 75
    0x403100100b40d5030091b01001540b486001840c0c3c5c0031001911400e8240151401031030b010703200340c06020198694490480a802090f07002c50030305043d2100c1944540801c480782a40c160004040c9100b20041044100880340101c0d0301d4894400e070300c01805801c0c0600340d2040300100c2d140034015842041c400603940980d100303404641c845030400a210b40c2c000b50907022640c03c500c299041c0ba206100841e443c0c03080380c0213240c10100010f0f102c0200030001803014442c825001c140e41c0203481310084100b01d80310a22818a0b107920901052004c50048140890341e4007088016034a8160003102055000c0c00c81c0c0501604514800c21050300240c2110300d4844d09064406000250301d40002159890700580340702c80108540d01440102c0e0b640103441070b4043c424541c04182d1040d59906209001e019200e004a004e1810003015168140c2c050080c0e404140c000d4441c82c1e07038a4050000d00809000228060360920581045941c00b03880c0e0f8841c00d0b0103a041e21001209001d0608144030641e1904821a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 730304577 1250 730303327 730303339
    0xf0c0c1521091a0702150424050106050a050a1b0524061003111209070503010e0102040803041202011427060a1e030e0601120201091e050d060e01090506070905 70
    0x140300020b9035040510f9401d203840e060504207499240c4102e280250f02901200000c44143c1032000b03100e51060803501d026078140c001c078413000d201407003a0155070080c4200408a0300600041c0c04140c09200940f949031124075004840344001d200e12401d40c104813800355400d400c5805506001c1c029040f0ba076079003c503071004000c42801c009022890851808a00c03204140e542c400922001c441981112544030300e86071418814182010a152039075468443e4520a620704640d44444420600030340b42214800000341d410a8074140920105c0c0e421000103e0400c5450410030501d51b00386801f0b8521941802c1c129246101c9003001c0d41301c420380c4411041d1041e01d00b131107000c200e190b01200c210707188001c0c07601640d9003088202054010b0240c002000b20140114800891002003098605034042d000340d83d039659042d51098040300b80b000c100d40d182100c1d40103082c01e0045047c50601c03641c480c0c2c86100002500380d003a8011500b100d010240440e501e41201c0103002110790b00201c0300028050495007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 730305827 1250 730304577 730304591
    0x16080702062203030b0301020a03050f01080d0212130b04080a021009080d0c020f100e130603080a0e0316150305010503010c0e0f0a050d300f0c0c1521 66
    0x802c501c54006002c050303014440340c06903002018442d40240880742c5018000b55100c0505c00c40180c00380c0b00c101c80340b04201c0760340b00000030802d030000307402000341480d50054198a510f00c50290200c0e8008103a201d800c424000d4001825004400180000d051a02c06411007110b10300c10000c0020340c10250508020100405100e030100100c2d240142c0a4203040080000341240b0200d0010480c8011742940a00c0c00e00301c108803140c2100c042c2544003401c89150094000111709103080358154040070303042020131321000350031600402000010079030080032248856072400808a41080a4100c0d4901601038505c080f030131a098010b45001d03000c200c00178000002c2c0d020f401481001c4a5072081c2c41022148100e0900761224400c11016180c00b80000200c20800c0c20800d451418515440010408081200c1d05000d482d954400740083d081c2d642098050074407804869003000020140e841c3c0c1c0c40c48600043e1008800c4100d0888116900d4510003400e001380fa0244444550103081001810108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 730307077 1250 730305827 730305841
    0x1e030403020609010813060204080c09180a03080907120602180102010b130f02040b0a26010e04030806060d0f0f060504090c030206030910050c12150d060c020c091608070206 76
    0x2c10344181c95021718040ca42507032080c6c409000b50654000103130010744001004a090000401c0c0202058420f03285c2030381e107490b000c4c901082d62000340713a2401b03d608170f0b0f04001c00082c428030340356410140e040d04a84602c3d403603000703081c40030003480c8049170034a500155004e048400d42c2c2c2c040c0c011010900080100c4d1215502007083d41c024028821400c503503400500f101007034640c1c103650180015a40c400d40321101e100014102080e031a82d03190081103014100c105010f00301032154140c0350003100201c1ea9440d50b9900b034603022000b41c030841d409102841303402d954140d988224040b203040000301044c1440380384000011030302190403141c011410701ea16100400c101c500c003002142e5040c0c0c0e000d42d41c1c1d910000900d0500c220400c00000542c01e100500c00e500d80620060010742c0450020380d801070f00c1e89400c802c42c820313406e000560440c681101e96400304501c2d03401000005a50300560b5441c503040400100010411240d9010380e401c3d007480301c925940d11032401940101140018001410000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 730308327 1250 730307077 730307089
    0x30605060607240e06160e04061703070302010b150f0306150d0902191d060301021b030d0b04060509060d020604050d260a0504141f1d040c1d040912021e03040302 71
    0x6d410380c09004214109154a46130356002c400108030f2604019800700180501544a078000714040d8015800d1004106091400140d8081c000e90385003820351400c920b18042181a0f000104800d41c00720308502d0b01d1103011110341c001c2550503030149000400381c00e1841000700c000b00901c1e2145161a056006020081c4510031009080342480d5446416070703943c01c0064007a01c100304429184185890310710300c40c000008041c02542c0071250b014041249044288001c640c55449020ba020b108800404d9036410480c501e0601c07140068041da29142d2500d010424400048400720b44a0341042210301c0307490548200c0c10b96410210001500e0940c003200c00415601941c0106280942c404070b044901d903503183c14030748003005080d0411400c0500000007810040f01074440501c2ca44090f465501d0300d1070244207428800441c1c0e10341c810001c000c1644400071110302c00d641a00603503034021035004500c2210b401c91f505941c40d4024401c0c1d5189103016403088900d0710010650741e10500c4203000603601c3e6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 730309577 1250 730308327 730308361
    0xa150b09010f0c050f16090c02120306091b0a050d0f050601141b010624020f060129220f030308040201030e0319090f050307030b01030605060607240e06 67
    0x549400043d201060620301d0901d00140c4d4128984e10412460382030400d01c01c20300c08100c0b220113100700400700f0303a824142d0701c822059019118011081000403100e1402d40b1078250080301002c0401580b500800da01c1c4c209a00c09a101c4000c18030210b60307648034488034017912000f45002201400a824804006484d180f02024009101080801e400b000303c0c000c10580c406241c40716000303103c2240c4d0354484d103180e803180400d606140f415901d00313642c409000092414688102c8401042942e20386a8442c0c0c0913130000e180e10000881c3d80303d6202d0501c250380058510403482c81c3d000c01c1041a0390101481215255101c9070000c00304420400c00b203a0040c0c081031344281c0a003004503241c100745c914103046202d50b42c41c0710b210f250720b0212400c105500040140c1900c01c07601500b003480e0f44031001c06030741e25644d02c03004200310850f8005000140c03c5800040c2c00c1080507200504280041d55603a6840a07a20400e000c102880c908a0b883e000d142e0080c80d8800c5900f40c098001824400716600c1d0301070035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 730310827 1250 730309577 730309607
    0x10206180a060e1c1b060903180f03020f0d0b0a0c030b040e2407140a05070609150510080a1407030c0e160906020a1101110a050a170910030b06120a150b0901 69
    0xa1444284103050003464a0a1105202010071040030740740c18004040d10ad040c04141d001350b02009198042c0d06004100c2a41d154110580c40c0059a0340e01c504000382c4142c0e000390b010180c445005111640f00d5005204070302d1a0200a40a0070b07201e0b4904c428100c0c0d4080d4221480341c40041404566904012040142d414151103960b85041001c000d0b901c2e0310400c1c03002020f440c40c00501c101480028210103400b4611041c0601c080c2e241d03103410812a5009028400c0950000c144c034400003031900e11106404404042070741c000c00d94030703110175074005829403006211a100004001c00d40c50001082c00806095040000c841070801750025510104000001c01c1c0403041c20317000364940c0c01540d0703004004010b241110050089440d0040c2c0f1003402540c1168049842d032a0b10b62103001d800c042d20307251000904030813a60000c00c0c904401510f01c105111350404000c110804804002d1508140b0404510002090107a0400048140c11030aa0300c008501c09080c0080c0e10140e9010540380041d5113 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 730312077 1250 730310827 730310831
    0x20f04090c0e090108030c0616020c010507060906020c0a050d03140612151311090f0619050306010303090819080d15090c020705010914010206180a060e1c1b06 70
    0x100c0400c1d40c1d900c0c041900700341d018494400005e90414000000d00b049a002c40c241d035a517495040030049040309108880b000350b0001d031594040d40d40308802910489001d40d50108036000e4a413102c1080364859a0320764207942000109000f800b40030494045000340780d15081000c006003e54000300c11401078081c0b885010125114100c0c0b090400032034944100c2102c10311180d00340821000310622100c001116010304401c1c180100b0b01e0440b81407481090b002c10303881d801c0d540351002c0190f201c808646401b00300200400104031f40d00c040107a40e0181d407290301d4081031281401c50140c5484501c0c40340c540760ba0300060042c4005003482c0181d4146803251040420554a0401c00818501c81c5800c00c4402929100e0000020b339400110038089660070b0702c50348100380d103503140f04400c245109680c9015a00201c0451400d8541168800d848201c1d0010740cbe2403055582d584400b980c1e00c602400402d0350082c446503001060506988010314800c1c1805c884200e124003202442025401004d08055 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 730313327 1250 730312077 730312091
    0xa0c0c06090e07050901020a021e041a10050c0a050601060206100905131b030609061a0a150e0f09040614130312181e0308240d0206040801090303061701020f0409 71
    0x39008101c0740c00e80c41c9d8005c1c4550201100500d00800d10750880c0c8800303201d2820f00140d500c3c545818a42850501409050455241500402035481e58041000045540304840645c40480c2c802d0042c14041d103e160701506450511801c04927018060b5003000c01090b1805090180c08c060041c0321102960380114042c0480c0520000c0500801032607001074030050414241004000d12903020507030504403c1500030700d03692603806004104c3d84074005c0682d590340405030500c0403405200350b003500e070900411240c41503040c034000c0340e880641030303d00f00c64460305c46107006040c00340041c0d07c43e40300c4d16a6140c0700d410b80442c0c800500f2a050040105446075032001c0408000c0d0684903030f9842a074004d8003c400009400b0000e41080c62081c0301070300000c0200c0702281c0201c080f401c040c0e14103940e40031012820b440e200d040029402030040c2c100e900890420000420440a010f0004868065140041c4943c94015180031180c0c2c804052500c070b910410059412542c144c094400303031081b00e10001508 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 730314577 1250 730313327 730313329
    0x15080603100c0309050d020d0c0b0402040b0d03030504050f120405190e240301020918060103061710051003020a03080c0a02031603060b090c0a1d060a0c0c06090e070509 74
    0x640050301c00c0d580c40d82040041c0b001203815030015440c003403050084610891021300b003203032540210b070794450004220702c00760404603204101180d0813a00040000600c403c81030001a40b02c071300c868048012903244c604110034450107021034480c04401c0c4001e0b02c120070050032400078030311445c01b0740ca10078846e60f004291403510446102024060340302c2c44a940d070400c21901e100ca0642e81c0b001807074102c0034041000140c02c041c020340e41164809050103080d207401008070f214484008018030f04240d40c0b00760010700c01d640707480307070b80740c5006103402800d903080440c0c210100391600140940013801c80d031102000143c0325540440304aa03004000d140d2036107200400d0500b02500ca04010754176108460301074880340d11390032108003220320641d400c000c404015000c0c000000000c40ea04d2078280c5d030610030a400c0c940211101c2c404c01c0c101911212451122400040064000c07900c2c00c4001160091000c00b00f10202d804c05d006003440c0d082c4040c0441c274010425003140e01c010458001c20101044a00365 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 730315827 1250 730314577 730314583
    0xc050319020d0905060105031c0207051e210c010206060906040b0a1a0a090501020c030a1104060e01080a02010807140d09020f0423070507030203030a110c07060807081015080603 78
    0x108402c00e8505003d42107080c14026512242030281d180700340605150300210000f51f42c01102e00341d07050f03005170907a60710341010010720506001c20000014103441c1160025902d0201100c901509455400da00c0f00060b0314040c64030380c040d855507040d035008030180010f41d594162080d902c401d049802044840710030000c62940d1603580d00c000c103800b030105901d031049070124001d04407100b016910b100145030340701c00490303030b1718644404550950003000e11000402c04102640401355030161012500940d101d00707070041003509a0144407960080d800c24021903a200851a4025541d0325001c8600842d030043c800c61031184c0d24480701d075959150500341c11034444044512910300e0060041105020b40d03586907000103d0f103c1c00034201d11a4400040600340104165101135030164000c0d421980c03161040c03c02444d4521980c5240c2605000c2d01413415410045640540059540c561003400c108102030400d410141000a40601490040c81050501000140d04002602d0058a141c48840120341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 730317077 1250 730315827 730315837
    0x9090103110402040e070f020114130b07030b21010606170c090d0f0f05010e0f0a11030f0d0c03030b040912050d0b060a09030201020708030703170406021306210c05031902 75
    0x245d0042180c04201a05800602400c0f03001c41c42e400034800141d0344401e0703060142040701d02c008012105903005000c20b90007c1105d81c0304845090020311603c84d240020809043d211040b503210400780141c00300b0120030b0003510014101428115000c1d03a480340e1480701c01c000200001407100c80445c45100c903030b989500000d9100c2e00080089491061400d015a0700000120142c43c0c3d50308110308180030240c009483d511442003071000d0005041070ba03541c158a401c2000320140d2611402c0c0c1c10041c800b0050002403a100919103500308108a02e18001c1c043d9810350300352901c29484c00d1568004641071501481c6018103500c0c00a503180084694080101a2210001d40120300403544400c00b5401c036032200183d9000f42c080b81c402d26a5212065035070700c248480140091402d0345401c81c411640d110f0540c1180c8580703400b60400c014000c00440392805503010b000018015810707080b010113080c0c1d180307a201c0c3d0083c0050101c80c22490010305035101c0a0305515158000c0c0b94403c2c21076030507a06a40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 730318327 1250 730317077 730317089
    0x60d021c02090324060105090a030507060c0b0702030403051225060e011a13091403070308070e06070f11040e01091127070c0609050f07080c0103020909010311040204 73
    0x903940d48103921100e0000c0d0000709065000b44500112040c40781107464811250340183e10078441266690b90044600b038200440d4150884c014250100005a0500507100900700c20350352802890311a0801c40e84c1190081d00200075900b0801c0180003050300464690345a00740e0b00c1c61a942c40c990400c01e078203201d0200e151121950110b503503040030402160000805107013020001d0241e24034090008860b050b01e0034041d50b0201d0181c0d5011040c101c0c98004030030303903801203603507041440340342c00c055055902203081100000c04c0c0d442000501e94120b442061000015500c9505000e510380c0d603080c6552000c000500b0340c400c000a8900f150341c568200204141d44175009100420441c90245203a0080c5c2602c140b04a400d203014081e80c00c904144580c9040740c0c0000c917200354071650304c103450001a041e815034010b500d4042d003002180c000c00420007030702c401030f0090201c585030600c240d083c010518038072410103004000c1c601d8a070351840340d8903054a070032840c264030704d84404c8000f9000340f00300d900c01c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 730319577 1250 730318327 730318357
    0x1f020c011e032315040b19121712101205030a0809031603021b060306060d0902180420011806030e21030f010815010303031e1e0f1a060d02 61
    0x1152900d135640096a9003001a5000d02c4860440d00030007160b00b1410b800156a818911001c01850300300900d0210114040e0f4031021021403031040120f010ba005021021084c0ba103007080c4540e049114440900410300e00208500405030342d41c07400c1c0c4074811f064074002000707080c0c0d0200d200c0303003020700444d000140d4185040c5c2c403074681031034041d4413002030880c1701c4000d01625001340242c0c1080340032644100802008140f2303198006000000420b100c00c401e0360044c124200c8400a1a40c640d1510b00590081650300307003082c072407002040062000c400e13560400040726120f1009050a8000304290380c424240031600d0043d402d0780741e10b04240a40c2c00d200c1615140000c502c81640704c0c0041d8080c51009082441580c0c844600b1551000720320399075180da030000e10040000c40e1013544244034080180c07002d24050141212050283c6000c0100142d400660102d540d51a55082c46050300000c030110b001e000ea40402038410800c280540b02080c024040000d41d40b040304400c0d811111002900412 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 730320827 1250 730319577 730319581
    0x210305090f030c190603110307320318010509010e0709091104050115080912070602090117040b2e06080c040e0f0703141003030513051f020c011e0323 66
    0x130754051000d03e10401012030b04c0c1c8000d6030700c41c840c401e007240e01c107102c0c503198080001e0200b46851550403056110042030a84030f81540310071080e9000641c080c40d84000b01c0744800c1005803101c1e00312040540445140d81c5840c40460f10380501280c1c03281164040c8000003050351007030030708804412141416940c8140b61800118410107404020ba10814a40c0d440140c0c5e070b0b8070b92024030794070080000d14801d204010b020801c0007032070710b40051020702c0061404c51800080d1400c00d40840c80191307000c88041042c103007048001300d06025403603200c01c0100d01c400310644195603011050700c554014030381085005400030394004890403c41c1c00910041e858000d6920340084400d481c0d00c8181c501400090400c4c0c0180f4501c0d0258440c0c2d80604035110030002141d145a50070780d075642c042400341c0c1c00446466000035081e543e5962200045c050118585001c8808050090a20300da0003561418056608104203121000d210907040c090414240001c004403020002040c4040c0d815105190907075440c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 730322077 1250 730320827 730320859
    0xe34030e030c0303010f05060a1d040915060509070309020901120201030b0604092f0d09020406050301020f030406060b0a05030f0a0b120307030201110301080c0f04200301210305090f030c 82
    0x11342c101c0303540c06c8200310b2003900c1d02d040140307501c22a2503850020309610f0407082c51301d02d44110004541802003002035090350641e41c4854070029880024006523903500e0801c120b0401c482c8540d0700408518040012005039400606101010300883c0d8441e54074024140131039000358040d5080c030400400a5840b503903200f407000d000c0c126500c114010340c0070f01c000350303003030b1040c00114403004091141402e4200340c2490542d000074844d031801a80d00071f03111080000e042e1000c0c402000348611002c0c640f0368038070f007504009050300c5140c0d03c905501d80d0108040c02d261603020f02600d8002c0114019800142c41d103954650213031568a031440da01000d041c0b512000b0391400401454603910940003448101385155509442e0f00003480303070f50fa6a4011071054001443c00d62000000800010400031344012416004480d215810f80103030805500007006000002141e021034602030f1400125442d0080310b550004c080c0d014007241e03a0701601c45500d0b000c081e50f03402c3c00358021000f00076041d4846500014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 730323327 1250 730322077 730322083
    0x30d14090d0509210a020a15020601150e150f1c0f050906070c030c0b0a05191a0f061c02030612071505030903041802040e34030e030c 59
    0x65800329140c401c1681860080340148140c03145100c0040211070207130b90082504501d180d0b2410307085454054011480016910000c03801c01403c600d14502c41d0203120148082c1c5042d6068101d030f000703100c0e0052900115640031056000342c510681d0001c0012210003181e5026000e40d1030048801c07480880c201c803220340101c140c04c03509905240700b44580c4200d01038100403550240c603118110380101001400b040d008410720b01145d8400d2600d40c120710010b490341d050780b04055481c1513100362208240401005888010700707158030b1a500070000c241025074081c44a1001018460082101807403032042d5540b282c0c00e880c08010040d40a00143c891005090000d510443d44e46d8840e91000071411082030001901c403040d079281c4841e07500050000a0181da05070802400d5200a100400002ca00c22a0019800b003680f40c030b140016848a08242d01c0ba403020b00f0090506c041c0d403007d00200d80303502403184c54000c8400500740c010148000001011800b900801012000c40c1c40005204441c11b4000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 730324577 1250 730323327 730323331
    0x90118170c03070c03060b09070c0b01091e05090706260114180a14310f050a030203091014190908190b09010e060a180b010e09060702030a12050405030d14 68
    0x8c50300d00c41c490340d500c4030940302003400d0302e8094606114807005021100700d50f80002201c803405504000078600d0b0441c41e105882c0226040f0b05180c100c08401c05c1482c4d08840b41c5051070303469062900a010505500c0802244c0c140314101c150854811000c2890f12030f17080403c421601e000020405103000d00c40b14010b480e4a070030b90415488600000f0313030b0341f905070ba1043e114010020010100c0d41881b18940501044c0c42000350f5013243d0806140000400422a1030200c61181d0055511000c03628108001070001d4010f1000b4482c050311980b0504407890210784648114094159584401400442da40b41240d000b00b0801e201c4c0c072144003600c50480c040a1409441440d5100ba42c0d40c44852040c2614114103881116034403081c04a043e035103894015010282942c40d8030401d07011140c48803048001d003030740084040243c2d101840341d4510280500c2d944900c06000451608402c440c00819440455840f401c1c941d551300302180420505000b11200c0c222410820311400c0c006500c0c001c046102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 730325827 1250 730324577 730324579
    0x81009020a0305191b030203060406090504141218092509050a0b04080316060b03010c0f1b02011b1b140102070f0608010b03090109050d0503090118170c03070c03060b 73
    0xc1007019024210f28003a011404c030486090244001d4601006c0e03029400191010354082d4030f0302004603048040c0d03c25144118011140000c680450040140c20a00b420705050a2800c08212000d88210380082d00421403805946c8484c095481540400700d01c420300c002e1b1980c11812084810381aa070007485001518000c0310f0f030b0651195644a0242d181c40303a13110305c09098000b484189410b0039822010200d2078050140490465498800a403c446192240a01299070060920086540400c0300640c10100343c68680400900e84c0000e00320440204000c408410000302800170041580d040284038813585294100d09911009641200049a40c41c5070052040c1240000d0321000041c00340111415034554441f50303424a0201140c943c03006095031a00d640751004a00090000c0141c0415032403555200380c1c0300c1c10515100f6003561400c0091045a614414411000c80c1c91418070002e141003103c1110f640d0424600c1d40c0d03042d4017400700050081404100004140002c40e082073300b0780c1e18 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 730327077 1250 730325827 730325851
    0x50703110a0b0c070e19060603090317040201170901090c0f090e15151216050906011416230105040614040519020f041109041b0f081009020a0305 64
    0x512041e40b20712600442c0601c0199502c18101080444412440b4a412001c401511200300320441d40300d009072200da600c000d0020b07030345100e440281544101d40208070b02a000c400075603814684c000030b180074140e440001c03c9800501c00301e2680c0303409502c009101036106100c0c148240c1d44840b260b070280310b01e10030801d820f030502e00b4002d00601d0200d0002d01340b05a08001ba8699124080900788040e9181303a1a40c10005100c2c901c030252004100b0405110041c00c51549060308100074400d40c600098007071814080b88601c2040740600140694440f040b03401c1c2456084103041c1880d0b4100000000f0110b403004141c3d0300500300f4a03064000c184214003d0f0414440c0090014400141c0303001168054010341103102c0f4151072001e2604101000c0780000c00500c460041c44c00002c2c200e0740e500c0f5820300c000f500040c1032090b6040c180103610742c800f6410b2034403d29854006000c0c040c0201c02503c3c80811407158000703840c0741e00b0154950040c008180e0115221000004090000c150a440344d4030400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 730328327 1250 730327077 730327079
    0xb04082515090816210203030d0204090203061003110a120603210201140402091f050910170115120606030f121107060f050903010e1b01080f0f0c09030109050703110a 73
    0x141d100c1c2c545508903440c00807000107007400316241c11082458041c040747d15010402c03a00d82101c00900151020702001c40c6c1c016500d080640c00c02402c40511069102894181071140310301039440d0091700c101200d2414000c5c50403905103000d0004003200e8000800e04000400440d44807198040e11711090201c54000308400d40ea9030200c1038042c0301c01c98000350310000341d1002982c1c2c880a800e01d002005901c00c01d411000e61114001405031070200e883e881d003524405401c02039082a003013644003080c8a10000c0086120715160340d40041c1c0d41f802611a000107500c06031081144540c00500215042503900d0b040510318038203400081051610381000070604020301840c0380000c207000c2e00b10340903078131246107904501d441910070350071000c480c6030705540c4e075465175610303c0040c042201808103038200c0e2201c04c2c81d18400036040c0305001c1d2100120070743c0c03802086040403808561580080800c201706446c0c0107070900180c050000740c1c3c0020700900032904c00004004420202c552604c02c1260012000c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 730329577 1250 730328327 730328353
    0x5011e0f03020c011103010e3304020901170403051c0b060313150207060504062d0506030f03120702161a0315120f1c08010e131a010f0b040825150908 66
    0x484080c0f641c1074009c0701646010180c42c40c0540c0100049841030401c0300410f00c000900184141c012123007580491000a45201c041060210380b40c500b90b1600c81c204482d0b6541e42c0422a00c3c0002060500b0002c40044070405000344600484a16003901800351b689030320504d8104050003040e601202ca071410104055002441440300d1041030400401c00d54088001c0ca000d00080c0102a01b0355805001d00b541440c80020140010840013440c040720300c1c56401d19680c02441c00d080f1182401064500c0241030168100c1100d0f001d800314030030001075840e52642c565001c0c2020078012102e610010b02110882c1d01c040c042a03159500c81614107803001c0d00200a40c682c8204241b03160f10700050600300c0180000301e1807a03903084d00041061103000c841000d540e40c4488981a41a9403a10b201c0702d5001000894480c00e01400901681c0c5a01d504051a08144e10703070b202051100102d117841207002116800d0608184040205201118108820011140a0044c1e0344074020280c0c0c9003d426000620 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 730330827 1250 730329577 730329631
    0xc0703060b0d050c19050303040902030402090f060d06020c1c03090507050a060c0f081e040905091207150e0d0512060405130821070905011e0f03020c011103010e 71
    0x1010f070024054000d24450500700541d4500c1c940016216041461020410b52810409440506426080182e0368101030040010140b0020312040c141c4176001c040018a849000d0000e00c40c6603c10801f60700c0e420001240c0d801c1c8101d0000489184071038030710300f40c500c07503050300443d01e41c07400744040d1a80151144c0a1103074000706070058401203003002c403060700080e540822400629000394602c03400c0c098818400b15041042e03d18003818020f01060502030900706100365604000f0722002040c0741c41203440e0803d094000c0440142510021a003110b8200e2900d13000040b2100e4403034140c60703a0101a010180c42c68110609110f030043d1a00d000444500f454811a0f00a01c504c1c0c94910b45c0b80196660084250704c4285e60b11000c82d001d0126800d540c102036401c031300402c05900c0e9050f2040c14140010112403018040d20404c51071301004c14071603508078582d42883d441e03902c5c01581d9840180754560243c50701e08480212a24000700018003007601021490080700b1400c00c00d00340100c0d00d01d4500c3c1e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 730332077 1250 730330827 730330849
    0x2e092405090c0613080109080915090f040c02150a240326041706160201090b07030e03070b15030706110705010804170309010b040c02010213030f03050705030c0703060b 74
    0x1800358008441100b00d85800009840341c0c3c49424040203a103920349030710700d00703640a83e0021180040c012511140a144c44183c4500044810074841e0510240000041c2c14002a08440c0c3c05541d840c1ca10047c41882481014032102020094151906004440320010818282c403400398681c4641203070000100030b11181c08032074000d240c910304e010360780413000e401540003250042444800c110005c0c04038100c1c1c015415103522072018061905d44010700c00800e2000c00351810031640341151203c0000d507085022034110409180000c2c00600802c907851540c46080300140c10421888108000d90241181c10722800c04107406030343c0c600e5030319030b41035907088040ca021510700d802140c014051948680800f5a20078011101d0851052400c00d00780560740c015503410115035101c0f981c0b0100d5040501540502482c503100840ca4103039401d0030200300c01d070035010080203003403141034241c207051041040d10100b58210341981d5540d00203181403a45c1e00490f1100f140c2e11410801054403038075240314a14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 730333327 1250 730332077 730332091
    0x110d0e09042d030509030106060c030c0b06030f12041509030f0b0a203c09060702271f0b03060d0b1302010806090105032e092405 57
    0x401203031a2991010303454840c00410780c0c4001420500c0b50000c1c0000e01106040500907201c450341c4448040915003920b03815006032003800b03401034509001940c4412034002082e04a45001541e8503034000203401c0c04481c002022180c41100d11840f03150810500038001c9032003440b05028442d40308802511980d060348006403600c0a01c0a403a004102c13401201a031000144c400007450403c401c61108103d071144010310340303255000c107a070290398255079429100c180303155041c440762094928018100c8000c44030303299040040416460035a0720703944142c1c1c0503507900605014407030480c681004c0c03401c1000710011105000302030124500d2181d1000207805d56182e40407100c1c0f141c1c100031b4005400e60000c0d1030345401200c0d83c4036802c04586102e80907402a600c0240c11705210180340001016424090304a500c24032015004010f95a8000f40c035859484540c4c014a1603a403151460180d10321100b02501c12040c00c0601e29010002d4047e503a080c00706441840e08510b1900315084030031290111280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 730334577 1250 730333327 730333339
    0x7051504090f201b030316030f0504050c040e01060504020d0509071a04060c051504080d0e240c0c0a030c0614040b06150403080d050406060e07120b0a080d110d0e 71
    0x4821a1540001c1001c44211907001504d03248860b859495540212440750040901c1c040c10210300e0b6050148843e2000c0c0c1c604113100c941081e855003602c500440d00c400e44541e90f01c601e0031f03000c07117001c0d0800001010020021903c580d160306000300548812618100140910040030810500b607903130103081c0d0505000903608140c102281510304190321101551144950481d440880e60825807662250740306240315510340805480103800d441007103042e500b8a811900e5a9000740d4030200c504296100c04000411898607511040881481404d51141480c064a4014014103800c801c10023140b07840f41c0c4007009681c10303810680d0a0f0b41c005031001841d5250320004607542c2d00d0800d0010304406100490303c0e00d400d1b070745d5551030034503800600300c405510b4503481088180203403403182c140200341403800b1201e0340c07400c110000c000141002c281c00c12650385040c4089152202164503018009040884c0c104103040480039240030060a170000c182c1c030071003842e030072880e2142c00494552031001d080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 730335827 1250 730334577 730334621
    0x1509200a091a09030105040c080111123103020303070e040203060d0f23010614030109150e0106052706060f041406091c12030203060f1207051504090f 66
    0x502c0740b014010001d05141c040007404000d0840e82d080c0b2400c1e0140d07214241d512440380c54000001c2c2980c07403404001841c550180042d0041202d20000c00d41d001c0d01070701c403101d8107504081032444005d15059084000404d001c8402080640003c0110301529484e20f407100307400c1400c002c2000342d10048032120382010001c08200c0000350810043c3c0c2d0f06034031411102d803800300c80c0e00075041307910380440203240a0f0f0b4644004100d6034031040300404c503440094000380481c07142c5880d41040282d484c0d02e101c5210350b03100c450b840c20700d60a622400103084020035507048000307075078242e4000240c3c0c000316052001d000301c0480c240345407400840307016000410801b41010f10b4841500214a140c2c5600d0ba0028020400509260f903008844c4403110b12a10400c0b00d009100d041c8110041e51400c9503009052040060120a40c0c40c8007180841c500708599202a03840380f00802c1e41850040e0744003e80003243d04186d0b0701d803035600e0406002a2005010208a24014644070206540f041c0503c010b080b1481740e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 730337077 1250 730335827 730335839
    0x131a07060c0903141b03030c061f12081b0d0e13150312180812070201110d03050a14040f02042c030a030501080a020a0b0d1509200a09 59
    0x120038401c0c0103041c40e240860f900c2c0c440d03403195040400140080c1e00005403030010080e41042c2038028160039030065040c07101c280c006c984d468102405100d20300c011560f440f02100344095485014160711504d54000d201546010700640c1c1103400060203000840c0b0f1880290180003800045010a540d10307896424088030500c402d04001d884a900301985800d03202d0340080d0140c4810000b9441001c1c0070180803d2043c00500d1031110901c01581d0b9a0b220f80200404100003501c03151001610131a070381e40300c00a01c0103039081c60048442c0c0406d80031b54201002c00c65059070046200d48544d01d8280001002052151f0028608950081c0007103500d1101002504103036004824854142e6110710401000a44560080000c0340000c0f444d03510000b00c44403816854080d1a00410443c0c00415120003181d0014030071020b41d010350f840c1c114022551401c0662a070b00042504640034030b405118945480c80800503003a080c04d49102840c00051290302104500c08a922000d400d40d24000d503079003424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 730338327 1250 730337077 730337081
    0x62103050c0a060e0319091203050a110604210201020f0d0b030c030601150e120a020d080d0c050706150503070303050711060301060c11040b0f060912030708131a0706 73
    0x140d1000d10381c0300d03101425000034018071130300c5080344100e001552505180c0803c4c100088000b02c032041003080880003003105500c41c00414800c40d41c50f003080c513264900709008a4984120300c101f010f582c400c142c2132200744003400c1744682c522002c0707400b82249903036440001d9081c0c2c45003880341103a1490401c9200001062035101c208034810003070980c0c070503020710000286003600c20b070000c8840c0c0c40c001c104000c020fa0007007542d484a9000b0780301c0172030040400f601c80e500c54290f500040c0c069080c42d0f84e11400c014580301180e000c1c10714078000308401c540e40d4500a100390030014046038918507141d1081d541604d048504000c4440060051400e14113594080741c181d002104200c50401c803d00310504180d56110207140a040d5643d10340180704114142030581801120b4402d000b680740c01e00f0400c0f1515002191a505041920300d20707a15034400010179191000c01c41900b14901021504008001341e11004121501d0642c40d84250251110200082c00348940d0034a100810100b2000000426513 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 730339577 1250 730338327 730338337
    0x12090a140f09071106061e100c02120102040315091212020408030f180901060210180212030a080109050709090c20160806010b12040c09110d06210305 66
    0x41e0010346441400004524041c40c16101880400c84a0b03528104240080003c540c3c08202151400801030500e41c8080c44991046c500381e00481c2500728880056001c1c0b048100415400303442040900f8050408900035089800101c0e00040048241000340c000c03070003403030b5403260000c01d401c143c2000d0143c1600c0210303a205a2a034000e40134480080c0c03200c414006850801c600307440040d40c2d648030503024450b5a80e00c84203684507011502c0180005c42d40060501c038a2134283c10009400403074039140448a05103032100070740c00704806030140c010b00004409880008aa500c0f900216600ca4003090190340c011150710000910b2520100450146a0000d1249003540d042a07503110340715510120306520b16110310841c5521182c0504854080e040c0d815000f003000c80f018208650501218400c1071050002c0307001c450071200c1c0490280044c0c210074600816502104006006c01c0c89041d0a80790003000110ba02140f40150014410300102029025903826050000100140e41d60649503500702e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 730340827 1250 730339577 730339579
    0x6040f0506161203060f080102180907020a050604080405010314040f061a1e0a23040c171305061608040204200c06040606140a03060207050c0618010212090a14 70
    0xb001d80c600400c3c00075443ca1014452540d01180356410308044c1c40780550242d0040d20241e03c1000050524182e90428100801080341c00541689484000b240307800e503449030150243c02914203010421102800420484d4400c0c1c03414401c0c0411485580349030001240c0180c040b43d030082c203520001d0100d40c48885074410120083c43c0303140c12580450a410200c840c68603801c0c3e03000c3e1940d4030710b01e030400b040001464082803207103800c1c01803241c54a12a5038103a00602441c0c480c44407103201d0b4010508420000319900a43c030360351500e44a9008c8030384141005858074000c0f0b40c0030550304c0000b40c4d0b06685848854448003103540300d44d4203020090003058844030001d0110b00c507010184070980014490544c602d4002d003a1810981401e004460300340c2c0c489100c03d201e020802ca1191680341e1041d0860341c008000684407000b0b030810b01d0912098450300f81d44201d00003000b4120386e040e1503920404200a900301d4412031309124001500340f244000e4a49d000324403503801c00040802482070010800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 730342077 1250 730340827 730340857
    0x30c060204030f03051222020112110c0d0e03060c040e0a090c090c110d0c031202090303040b0409151410030b06130e0c0a080f09010e0a0b01060e06040f0506 69
    0x280d25100c038078a03003441010880008000265042006c0e551020558101d00710900c0c803100d0400d00b00710503030046440a4002d0500a010512010481081d484070b480503401540300ca9403282c1e401780302a00d54682c05800c070003148141100c40d445003030001c0d8062040f51087d00303171417405052044194803001c0042a00100d00d495600e40f0340001d1001e0314400040080c803001042c01c40c04060094605100001c0d804015172000e079000c0407242d0300c089000c42d1943c040c2403003030401c1065010400648500000786406100015002a50f035988100820441b58030b03110810000985039840c2610515074420301c05602e40d0340300070070718928050303114005070201e90500003075407a03151300030034a03d4102d0700c80c80341940e2080d102000403105030100380d9402450340f4802d601d0110304031000340c0340d00c502514003d944c500d04000688401c40075070200d200600c036601100c00f0460903280440c00f00d1401d000c0c0d04000f4002002a90403410200c00741c806507040381010603099414042808610380242c3d0b503600c5000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 730343327 1250 730342077 730342079
    0x30516060b190e1321080709120f030804051603080d0501080c010e2209060218060a050d1512051c1409120307140606100804030e01031e0c18050a060c030c060204 71
    0x200c46003078601640d07070b032a6911b00b403030030039800b60039220540e01c61020800b080c170044001602c00c80141d00a40d42c1800d1000340398a850803e01e1804040c00d00280000015140200034011034001030300810602c6103042c041daa807a4103409449415401250703022a0740c03190320b00c1c0c007461b010049105072100d0501c0014805040f03901c2c1d00070355800800c01d0712100e0b030024110f2190b00c1c0b0382c10244182407040e901e040c43c09800745001402d1b0701c9550301c2407003e10354800d007148486461170306400c020302c140108402c0c0c0e407095042468031405a010b202d080c0c04600100c440c0e681d409684816106440c40c0c91031410243c4140c02c0c440540140c90a04610340000c000010001e01b010300c40703001c030100000041c1001e00d4941c00303000384001d4582a0700c0a1098941c03c2000096010002d0b160040082ca00456044292075180c8060369204194100c12414050070803600d9a02409071203042c14001d81c3c440e81c250743c2c1d00a0010040040c02a6000118880024400b090081c070318400c440303101b22001450302d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 730344577 1250 730343327 730343363
    0x612030a0507021906080705090319080901080105120d18050409050703060b0d080304150902090a0c1d0306010b030c0d0f1e1b0c030516060b190e13 65
    0x180c0c040d01458020500c04110300d000d509040040304c1d014426644800c8619040c000c018210306d00060115042180c0050342d450f09403820310010841c180d00d001c8000c407010440c60318004a400c00050a4005900350b8000581442c04101d40e500c0b60104101800c2c000c09a42c400300c822100c10042000d00145043c000a026252031203501e02d064040c8010380380f90b40c294034252080e107107903070080f42c4241000e21400e008100305008807508960300c004c001c51404c641d040964050201c01c82c0280d4000100300400000c40e4081d000719110625940e01c9060480784400745803100d154040c129138155110800501005445100030f580048004607801c0c1400c095652100c19600f002c080380692030b885000d2210840103407084a0784010124100344503840c88207482c02d02001c802c2082100700891a003841081c54010070884400d070f46c0808210340450325509290f800f80140d0071a0b207000365000c40032900c0384200035000300261100c0c03107510f4000e9140d0501d004285903580800b40c40b540b05000c040241 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 730345827 1250 730344577 730344583
    0x11d10050103020d093e06090103090302011b0801080f03030f060d032003041403060717060a0e0f0403090b0307020628090309050328061d0a05030c06060111060402090612 75
    0x6101440200c070301d91b803130301c0c1c1d030803003201d030203d10f903040e2494841c000ba80c601d40c3d03101419910512401c4c80c00050b04034860504070302500311003955400215a041c0c2c0c00710416481b801c01c50590300c00b8421212612a20910341c2ea484c441140d141c44034000d841d021a89602d04990070034a424040e26081c01d000700c105415007916409000b150a450b8800141084402d038602c00d82c03410040c04602070905450150700290103a021240d450032548542c400243c0b050f030b62040c11101510100d8071415481c941391040004042c0140c901350702055060b140051108189012240b081d0465030292445440301410f900c031000848065003411000360441658280c03072407051341c614074025507070560054909418581403884101c0c0b0522160406e24008c400c0c002c014100303150440c1d22220000e6281034110070301420b03146601c0185403074000c42c034441007400400005040d0710130000054500c1525020015540c880901c8500b0b8600e400c0480041c0240c6001d840311030780880003a00030904200c0401820303007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 730347077 1250 730345827 730345853
    0x150304051204090e010b0d0b16030219120e06010506071e150b0103060605040506250219060f0e090a020304062c0f03210907080114011d10050103020d09 67
    0x4000c0e0307591804c07407984600900800c1183d05041e01d642007035031442e40700c007a0301c800010845010310b20b5030b0079519011032080d8112098089040858410002d03840400cc121946503050b000c96182444039001e06020081040380c100d50004000318609a503503174600c0711000c840300a8112001d07a2107910404610015000c11491038210400107041080e50009000c1700c000d601700004001c400c0c442800366031582000c031680b200d5220441404007aa83c0d801484546035114001d4114032503041c088100c07090300380c402040e03a0b00d5403500385d840504c948046074584220030709580e2261182002c507209540c2d6900654001e030064402280c0403000380b245c180641110704c200c042c200f0b01c0e0021510010400d010314298100110060b618002c0300380102803180c0349802d0703000c204141c10400310724085800c00c6040003d2500800038072034403002803202401002c091241100d54444501c010031940c1c406a15548a20000c40c805540503051000441c02908910645110302d9a035224040c08902040d41e684 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 730348327 1250 730347077 730347089
    0x12210606160c08060403050405120f0606061b0f061801110403060b1c05030a0f0804201c050102040e06181b0702090f070f05180f13050f010f14150304051204 69
    0x7e40d6862900092140c1003501098501c0541c000030095800b60f4004150650801c20440352580c0311060000c80c0642040c485115070445c0c46081c1d401000000301060161159100030b0360003032040b000100d214240d031125148040340c100c08110a000041c1d05503c0985842d001402c0c442001400c1c2c0e0100e604030200a606480c4c1d5440424034008803036000d4003110406605140c0300b01035040c156940e51400c210705040a42030300090002c2001c9440700420000c0d620b010aa4500c030308442810410b001798498020050422030403070020b400d5003071170a00c0016080d501080405a41d641003a0f5030007440c10395425502c15001045550090380d00e20202c0b6008180b8a08401c40b50304040300098911403003004036000348401407001ca42c0c103400420004008010545828441c41200e0f40062030708c02c6440c41c107601c224544010b000c010400385000714143c1398001034460703d00d80c840340d82030302a01c1c5d4041c195600c5600c60b441600210f165901441c0c00c40d1141c0125080442005c20990554000d500a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 730349577 1250 730348327 730348337
    0x10806090c0a120f330e03040f15020a02180a11160303050a0f23070c0209010923130b0603060919060204080a03020d2d03020c0a020312210606160c08060403 69
    0x70004d22001d20514980c1b0b200d000c011440d2901d0006080341a0001c0d00c940302840052805d483c0010703009101e005503056000f0a80f00410341500c0742c0b2022542d050b101f0100032451305011050f20484142295059840c001e840110390441b80d400f10094100200b80d0076442e5100d03400144441c1d0070740258000b9a2521140101c200800e02503225111030041501041101100c114000b50f1140082141552210f040201c1c1400380400142603030540490640042e03d11141001200c0691756404204c0d244102039038006c90710780e8010180c1c3c45100307850310b19580e000b1600da00d60811103804030302e080c10301c141e04c058145a03403280c1c0300d814010080c42c00c1c2c000d60030480003800c13555840381c0c40400520300301e0b11a8a0350740038042d2054111204041a5091507800641c075517034a6410050000340590080c1200c1c40d08a008071400115001407440703d11070349086010f407a03884010300714039100e050f01800d560f0801c171400a2122241034009401d0300c0c0c00e8503650300490941018000c5510640c041d440b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 730350827 1250 730349577 730349663
    0x91807060c0b0a0b0a0b03040602040e0f04060f0b13090c17030408210322210f0302070f12090801020c1e030307090501120b0405010806090c0a120f 65
    0x400c150301c2d440103000609141c035142440d605540c5094810b020b852840d0701c10f5440741d50b02d02e0300c0c0e4028480c41e0491020064950708001c551003196002621842c45040c080c8410f041001c000400d5910341300d6a154404101904141c0302c07040b641c0500e02e00c60080c1a044c3d0195640c5045c0030292140400c3c040301034100241c00d10240d80200407403512600e00d028452207840309910014528000580b55140b450200c15403a0524246041c0982495401276a1507182045a46203060a41c0110b440075003c16211040701d01441d00a100f03036010507801c2951603d000b1115a41e4103c42c03040c00d400d800c18042004008a1f10480910140200304103440c02030468010a4840102d40c0a00002038120356100700100b16905901c0798210b404c440c1b0a01301400c140f1000c480e0040a001d80e0440c00350894601000081e805030002000c03406a0341c00c1c07040e0340c400000d180a100d8200418020154502c4003100c2c0c18001407145c0c011402c1c1d4901400420f5200b40240c00101c004100030600c0300e03000e03901105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 730352077 1250 730350827 730350833
    0x40b09040b04060509030c0a03050d0b1e0411040e01030b040303091a0906010b07120c020f030a150501050301110301060c050a120206092b03111603090306061d06091807060c 76
    0xc2005c0c1c005003404001c504202600115542d80d03051044002c00304a404a11202c000c45241c202c4408004020160480011080c0f2101d91000211f110f0301e02c6a428032120320340d00b400200807501a50100c1114200b16170854992000c0403201500413410140d580d50004003180500e21240600d01d24034268000d141085c40d07029141c94810303000721421001c100603680000e80e41002c1c1400f20461030030614031141e918000521084180f07040c05805020308520001000407100c8200c4070700c1d410010410859888a0625088034400c0702000034038030040005028071030142c0704181c901da201e1422100041c48035a40c0244800150b5002000f607800241030112840701440302d28101352254441080341019a100c0b4130400712515000024507546010035840c0644440443d44003000710b204000300283c0301d207802403089040f4403081c0c0302245032890106020141c80403460010480740032112042c2c035000104001003502411501d0301c840000244043e13864140710800c024010303502c07104100e5006013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 730353327 1250 730352077 730352081
    0x50601080d0e060702090403090504050a240609030314040305030f0a02010506181909080a050a1106061305090319030c0f030605090c030907080604050106030c0e24040b09040b0406 79
    0x38500c4144400d5081c0380b1000d450f620141c0c0c5185070111080c1c0f4403512181820b90b1007603a5a000a074002e07080404000d02d010a682041500000100300303040c180349154102c0622681600841001442080301000841c3c40703614a03400300408400c102e45082d60300d90b1454616800035812603034204020170954410740e02031191a80c009402c1d90b0407001462011100400303100d000701010010722003426213400c900c0c0654043c07624554050802e82d900e07a04010060415080162003100140c02d8240c84240c0b02408691113020f010040d040300d0014400078007200207004001c140c662030703100610440380202d03025140900c1e606002d40380000c159024010060840c00001140d00606007068001c00990b00c5540700780d0b90101014210039160340f202d40303207a41040300561007440e41c5d2041000b031000307010040d0b2000007160b100d801000007080e55210100e10402c0119000c120001e5002131760340190101440c0008030310750040c0005003080074400003512581d8207036015105a1400b00421003001618 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 730354577 1250 730353327 730353343
    0x111903111204080633010f031e060f23010309060b060a08040b1003170313020a0605030a1d03091e0a060305040501050f0c160215040b03091203090d05071e05060108 72
    0x10022804411407840c460580c5403d2500300700d1b0400c08041c011408a61195015004088956100340701c01c07030b51301986d04050081c5004107540e6852540000500c0c0c2004040d4010a6591135110441108002d00660007088911416544151074000302c0c401c65a580005154810880c0c4410f80350341031074200408030301001480d11a500035111000d01c00f190f41c5004400f0001c00507a1a5542c80c1d40b24940c220110340c03801e0303009401a2041c200821025000f501a5124080740407080010b507002c0401407c00508d03403152442184c208024500306428040c01c10f000c3d88008100c80b210043c0344002280304000694806400a80d403403080c40b08100081c0640e41e04046000c2d813011540c104154070045603c6088402a80101d950455101b15110f40d401e510564696810b171030f03100ca650b444103420507030044811003418000c4140407040c0c0421107054034020650f4200034000d2002143d0155981c0e1702008041c7e804040b02c000b005503180309180b120119502c9000034003041d52501100c2e0340782c0f50300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 730355827 1250 730354577 730354621
    0x31c0c0b0a051009020f481902150d06080706200304030b01050616020307060c05060609070813050319110d0302041217190806011119031112040806 65
    0x40140c941800e440b042030302c0c02e01c00207043e41e0800880010004440604d01c0c4a42c0020b445070705d807602d0300c206101e104030410001220235180c0301d490030440707030042d007014400007540071003282040302c000d41010024125942ca610310005042d9241c0c2d901903d418500c1c0d000000040740804514500d80742c200c043e00c01e50410b03800540c00d1904540e2042002501401040c0c0280808903c50300e509058040340c0c112241c0150540b000507444800040c1800c034005d00a403410b01c80c2001256032070500a4100788185242c0ea00c40d030503600c07518070001200340001400e60726444240108400c2c04080d5034401e442000940b2800b034001c07180072510b400c1030081a07584041c1441404100845964080e0b039140c103543c0000d4070110350300c50201c2c50115014ac091001039066412100b5164260080e401c00d0107104242c0307032904820008010240d031520801c0701800c50801901c0300c180081e0140740140c4c0c00b0301e200301c2034684041d10380201c0f07503080e00036500090380e960106050042e22080041030304080c81c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 730357077 1250 730355827 730355831
    0x50c0a0f0305030a03020c07030c0b09011e02061b091207050103061710020a12050a050a1a013507180f05030a11031207060e010b0906031c0c0b0a051009 67
    0x407540d00ca40d9100d00900450000341034001805a0203400c05025080240d540315103000c1d103841c0c444401d0342c501c4c1c00502c80d05001c10099401c031601050303505041c000e91070f500e40c02003281340d41d410085507050781030b055040703e80b41082c840c0300455510030400d809070403003050017008898503000004050790b2a6910044102800640d0390347d450001003182e04501b0140000541e0350344a52100700ca50000d88184050701501d80070500007560540c1d00040e004900064090001e0a40c1020086240780062112400314a007506420040000e081c80104444413070514540200c442d2503007014042422030700c400010b00d001c1040e460180b11030f0f031a08060510385420302010750900012968032500340301e01900e00230286c900c07400390380d42c10840041c0e5402c00104803a15281c0c01d1400d540a002c425025007025402c000c0c200b01241455072416200390310090060030119070b1341c143e001540380158002001c03c001c80349008081ba8004440c13a00404d00302000051503c5c00c481001e045810300d400041e43c0034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 730358327 1250 730357077 730357079
    0x10f0501080a080c0304091118060f04030b130501060e090d02010b0a03060e010e030a0210180b0103081806030408120708040c1403100606080402150c03040b0702011209050c0a0f 78
    0x207400041c01c990100e030710000540c1c2e0344066151035031850003140e1108030b0aa060400303003031818544c0000303418500b42d40000b07481c0c01003841080003090302801c1000140528140f0080010a07605c44031503030000b5414070802c1143c00c5a465441c2566181d8200c00103000445090040780402008106501d41292008101c50b10b840f80c005141400340d880301824480d104c0d5400400c9803029440b40320520044803c0300d40d00d6819100c040d40320a81a507481a40070714040c0303801081c020300071026400030780c4000c509103180e080d555002d9140c0c015aa02a070048111000d10700c454481d44001c50203030b0301805440e40c5621030a40030f2104100002d10003003c01c05008188800100140c13142c001741d40c04031122103081e00150340464a004900c594514030541401c00c0050780030b8003e080c2030300a900940f040d090080c40703400d00f000148940d000015050380204020840744000801504a440c03052510b00b00100100391303031409a43d076100c400d594a0300100c02614142c03404404e64030040c613540840364281 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 730359577 1250 730358327 730358339
    0x15080d081006080a09082802010f181b0b0706050f160c06051b1603030b030a0f032102032418040b150d0c1a04230a05120102030603010f0501 62
    0x1c1c90f405041001c101c0c1d00c440c034480070096040d060700e1a01d0300e02c50400b605401c102c451906c0005220701c070360025502c0c0c0280401a0045401541c000070290b4416038001e01e0169500110050841e4280b601c41005800110f41e485156004001e040c0c0940004209404c11090b80b61801c1009880d140c24030b010608030710b46040d08054a007203d0307a005840080d80b80d44641c84402c20112030b0b6605890036100141c18100404810041c4458174042e40d400c001445410081c55900c2d12000350140280f1110f485250000e0f209240c000d0102c1c3c01403010b0503021400080e0103059030426900904522003006120310310300e0f00300508050201c022503440c0c5094210340f454040035a405031018003100c00080c00103044200c0c1d18101442e20300017030b0081c02901c015040000000304680a0034a159413501c01841203624010192000d6070501403002016072485015039085c140801ca10325040702d07aa10000507503a0766050b00c0c00c1e405280c0c20016941c1e2409070704043c2103a105161402003985480018024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 730360827 1250 730359577 730359587
    0xb0604050f21010c0302030a0b04150b03070203090901060e010e092406070f0807110604030b07120f0c0309030e0603100e040303090b0a091203050c0f090415080d081006 74
    0x905030280c1c2c0c01c685580100090500d00d400b4448004455800d1890942165505600441c4076148040c420082a80143c00b000f00307568805025044c040b800d50400d111740000600115000440c60048a00c2c0c80f5048000c264029402d074001d20104106005c000f0f1103580004c1d10403401c5070b081700e45086600c2d04c20b800400f44a1140e410101041c00f485040c4140d8a0354030460b61020f400a5000818001c90300d0000210740c0301c000101c2d044258070007524000d05061b020b40742031b640c3c007015080c400d541da54002c8407180ca4103035541e503513036450f60500da00300102ea200d05100a01d459601082610480c200a13081000a00e21503008080410410a5526111001c0025109032400200d03035920346003022000381801d170001400c06003012080c81002c400c2d03a48000c807000d110b1318007000007141054054044030002c503180c00c40700b80c04004004510401d840141896040140300081c901e80d40110300c0c0100c0341d290440c580d10380c041e01081c654036400c10b1001754000c5110480108150070290007c203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 730362077 1250 730360827 730360849
    0x209090c2e0329010504030b2a0301050f0913210e0a03150209010909140f180a02040c11060405250602150709080610150302181915020307060b060405 66
    0x243c403106800980d522a0700c2003040342c005680251030141c036400d02c0403540c001c1440c885501e040ca4880d1000707004005402e20240c03412100000c1404995003602c031705000e880c00009000c03488408580e6182d00c001024140b14208203c030020722040c010101c03050107050700ca980c03d00c1034400c4618001c10000520380e502040440040998096180d000c8400140d41400c8a90042030460b82044d2022180a6100306164031801e258440407410b81c40f140c2120242040c00c1c0012440380c0c0181c04640090300f00f0303030450f044445462400118243e0348501841c2030800603101182e807038020f810013449595000b12802030081401000302e1806103040070281d030712000c0c49088482840c0310300001c0c030030501071b903031541c01400710318280c1e42c240c0b50844400003181d41d58040c0380c030450100b502c0f43c0e01103031280c8281d404851001b150441e100308140200000480503070701040fa15121810007061002181c020340e50407200507001161039829600c0d100050300e02c060001b074040c1106001c20401da9841c215602 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 730363327 1250 730362077 730362131
    0x90c030e2509022209090b0c04051e0604120311070b030f071202070f03050307140f041205030f0a080f070503040c090207170a02100b04060308070209090c2e03 70
    0x60351a034034107060004200b0755030b9101c8200c0c13440720400203104071940c021040b03c40c4640900c02907640c1c2c040f64010140981c0c050319402a0400841805d10b80603241a141e00040060419040a80d181403840d54502d5540040303002030100c181c0798489202c104a1a0050402c64480034258036040300c5020b0890700c001d00e0b041c2000001d440c0d0600991940c0e044a0b003103030b007090070059409030509000e0010f40c41500c1d20301c000341498005070145907100c410748a0301d43c0002801d51505241800450381180b181d5010365060204101c40d082c8200e26074010000001e10340c0312074140b40303882042d5a0140d00c0c010441c0302400020020000050444007884007900da80c0c0c0e070010f840d00501c0c1040c01c0340c1d0b0103400c0c1e0105854000948507004d1500000c900740000403090041c000e80c0c0c03410003400203452451000900c0c44400340410300040c41e224100720350045800046480c0c000d00840000c202081800c0e06404038001c008404d8400008001d4044600d02642018410110b940e54940b44440811541c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 730364577 1250 730363327 730363331
    0xf050d0b040303060305190b0a2a09050603130201020f0c01020606120f07030b012c0606090d0c0906051507020927030f0301080d021203010909020406090c030e2509 72
    0x600b0140254081c4001d0354201045800d43e40016601d00360b2061620402d4400f400e041b000a14058020302414a0080c03204802c0980724040c80604d6810946602502c81170224140740450b0b01d80b200005107121b800000c400900342c1c0802c0c00068140030684c1000317401500301d8140300c850f517600010070a8110006455035020100603044070f40c14013a5500c007015003409090700010502000802d03181c1a1b648001041c0154031140005c3d40c42003519400c0c2d40c40903000b07000040c1c1503141c010082c0500040c0900f00303090100e2982e846521070b42e2140c00003103035a1b40e0760b082800941410079080d25080722684130340c3d01e401d44940000f0406200140000011076105001880d0650324150003000004c0f041c040325110f1a40800a84082d0024044c03605548070740f00710201c46502c001441030810031110500c9140d40d003480403600140c44c02d840d003a81c015072151400940000303140b103200000e03000360b6400103002403034004007070418402d081e5084400c1e18003000b0104a560f40d044800c100e501035140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 730365827 1250 730364577 730364581
    0xf0d021806031320060a020d032d020c190b0921090f030c04061716060503160903080c030702010e0a0501120b031014040b010e0c030402040b0a0306060b0c070f050d0b 73
    0x404c85044481907103640185022401600b05500025220302c0b861603920103010101c0728004031116680e1203001c810080000401e0150505090360061204501c0107081d5020004141620b015001c000d81044400c059000b0400120a03400e200c5622001d03d50101d1110300c1c914200305401500402c40c98501c1803409182c20101c5580401181c500e110003d441071107a642e848850304001200b0300311034030540c000d07054043e1049071102440d409a4100d5201d81d803e40d01da1171202e64041c19826100414410282000303c0450041c070f018100300700d440402569680700d90f2000400320980100c8460061441c0c00d814030040c0c2e00811007900007404c00320300154020103400000d01d0410307007807400040c2d10300d0644030311420302040041900c198040c02c80034400d640e0f07901a207030101c3d07801c9410110b451000c0c00410010300c1d181d00001c1c02100000c4c90302030101d4494545404a8510b90b02031001507034001002c401c248010721480c1d000741162803200850502d0100400d02c402ea580300d00410203c4c480300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 730367077 1250 730365827 730365863
    0xd06050a06030b09070306230f070c02030303190b0103151208040506030a062303070e1e100f0e090d08190207060506011707090611030f0d0218060313 66
    0x800000116003042c0c6100850515094507170b11010513000c180c0d011800c21b05c406da0a041c00c18102c01d180c44864200380c0346596130041c15465060050f14000400408030120707005650100013450040304404940929582200c0b00c110844a01e44821410b2508096a5040310340c40c140e401c2c0100c51080180041030202c51030840c1f0a40702d6038200c3c1d580320780e0100c240540841d49501010036507801c41001805840c0303103400343c501c404103011400e5066005100602498042555081d0410000b85010901c084d407042c02d444e00110407507128600301c85c409010043c05031483c5503400140001181e95400d810080181a00d41003000c042c0b905011a01001c035051810380880581c0324495060115103c00040c03070041c000d0002035403614000b038401c2ca44001208408180b06019241c42e440b40c4595900c0e0000580b1241c900da940d040160009204501d0101102c0004000c43d9401107001039a40584103952030a50303c0d08513850b40100d4003801085501040801c9451900d50450401c00c81562006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 730368327 1250 730367077 730367081
    0x20a09030203032d040f0302060d0f020c010c081e010509040809090405012405030c15130b03100603020a140c0c1c02040c05090f040e210c0f0102090d06050a 69
    0x50300080d0140f10006000008241c680602d80800c41c403101c2d4840002043c881ca41150f0040740514105986a054100014903080c40201200c4810640200d600c0064141102c1240c00c07100650743c0d04c1c0d4444039400612130b40070441d9540710707001c05000b414954010840742ea4010050051070701464290000c00c0900500405544001100600c504803910707151603c075000c1c1008500c0e000c1e8102a0365001140c600c800054102134900c00340007030049a070385000b008410044121198070054081040300f0130a01c00c0e04407400a0702e613030010244d59040044a0070280600c550012041602c1402002c0a0036407050350300704503100801c0440e86400e0048440e03802e0000c0e100f0203d510640c001d0300101c1c28400000811003560003114100020850b4040c00d8038180700e0b10940745e51111a00c1240c1072145090351200d5078101150040700c1c65025004001d810300d07041c1002d01868800702040c0210b030300070304000c3d110800e03503118029400d18640b000400c003040d0000400501e0305407500700040d6031090603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 730369577 1250 730368327 730368329
    0x130308061203041e08030708030601080a0e0106171c08040f2a08010b1002030a0318060603080733020d020c070b090a080c0a03020d021f08060a05010804050709020a09 73
    0x3500d40d690341d25040d00b030035100c50032018442d11203803c80001c0d03017840200a681d600e42d0080c0382c5500e155510001103c403910010604502c29039039003240200c0d04001d20444019042480404d450850007a460910300b4030b40f1007201900312041104c26405e00d82c0a0340243d0099402003440c04140301c5454415002148181200a254446030213000c68603007038180d403421a00307164000c000000100040c4240c0050300002c45000d6031003000807800303543c801c0d030005651540034107a0022211895856a00f540c1d059130098031490804200c090034091080399080c4048190030300350000446d44c0740c3c242c01c11200010485800e42e40440c00c4800601c147d01101c03111101e00007600c00194490700110406e400145000d03010b401c5160022507002c030001094500040e005161018880c41c50303081240e80004000100e030002498840103000c2c0c0d01e50031141e41d00b2111900e0311541e0340340c07000034459841540d40c082c1e03041102400038880480c4000ca641b85c00da99000c40090703912881100192003004503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 730370827 1250 730369577 730369609
    0x3050a111f08041e0c05090919060c0306120c06030207020406090c0c0b16020303040f0501021c06151403060d0212030f071e0302120309010605040608060609070813030806 75
    0x910412007a0382d101c04260301c1244595044800a640a607014911082c0c2d410010320075090b500d420b0009103019548550700034100c2c0225032100c01c030300c1480742548554940440341c03036031100054070320650103001d06000303401c1e8040c816041041c1034130b880e0b403015594416a0306060780022032905540351604440d02034100c0440c1402000010000203141038110740b002d45085d20080c000c901e2030080d48016000c4035503070380d000318159140c540300c0460b032010341c1e01c0450f0159400c001c1410380490b040400b980d900c103908070004dc0c480c40d020050603000200754210042100d4955902c99103d03c18056075085141034604002080a500c0460b480c07154514110205101c00300303280740b044e1544401402c41e284104180c4106103c0381d50a24411542108000d0140c0c000c0025000156482000785610240c4c00002143c500e5407800031404607003607508640c40b030740c004004020b181d0a1141030300d5003000300c0d0314000c03040303140112802e0040c0305140c100904002c4800c01186c0503a40d000421010000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 730372077 1250 730370827 730370869
    0xc14091f020a11040b01020a0312021207081009050105090f0604090804150306050a0501020c06070c0e010603022206080a0e12211003020102100b2d01140403050a11 72
    0xd44100082e42d214018141280c40c50200b9240c56018103003402526112407040e0010b2400007000e64003a83e480000024a11086d0340c2480090348103400300004a00543c02502d031803086041c22011b001400840f508003007003c50400004001c51b441d2080d42d03540c82024030013001410384440001402402a94002400d5a02d0108021450304010000750031402007a0f02e0400c0000d5584003485030a298900c14030f4090f03041644101c2c00e0b401c100c4001d04010748914140d1064545680340000e21031020b170841c400099001c200826100d080e1605030040f403c0058811286a02d0520014005c00d4014000e21107151185541c030700c0500204221a540040e840b91a52280074078003042502450303c04c4281100011a4089520180750b1802c0c44140ca40680c0a0510080d021460304040c0c00211051508004403002c2c08001c44002601920a4615203a45500ba41107a0000600341038680503201d913500e0b0104020000640c1c002282c01005a01c001140740c8850030500040e01c40c2070640c00400804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 730373327 1250 730372077 730372129
    0x3020c09070305150915100210090b01030326010902161e0b070804030c0f030c240506030f0c1309081201030c09020703020d11240105090a0c1409 64
    0x6900364000350300c1004004403001000a015040015200381030b54008085805100c1880c031500b0811f101e441c81080700d00440307980c1030b80c1c454030000311004c150307050380d82c180010018010581d1259505202c02d007034000a58072400c66042d4201310311418442e81131501e90000b4141910040b0324017242d6120f421409481c0030070500340a030100040c5100c0121900c10f2100c0004030030782e0040307250b01c2c090354250b60361500c120b019588000b5510780d0030794150140204403c840c03000480303201511000140f031081c03030010801115041c406440e0701031b0242c2d01c25000002d08014181001a14100002040700c074410b500105a20010060021410290245400180602500c00d5200c2094101c07031103482ca8448050703844590104074003982c8401001a0415802c00080d140304086107402d5801540903919600d00e11005249a40c0b0303080000025408100c0040010749002c140313940c1d10602c5040e0502581100760402003108000c24050202440045500e841d03584490000d00d00c0c204034002012510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 730374577 1250 730373327 730373341
    0xc0321020405040b0604080a0f0218012c0129160f030801050306040803010b0a140a030b15090a1a0c0718050a11030112081204030c140703080405090403020c09 70
    0xc0e61082c061140a07506003042420a42400304c1254100d600081c05072803013000550f54140c80a009134030a0741d000e00c030b40c0c1000840c0003031105194001c041024240c5c0310000829502e140300b10f540c1440302040c00f0464010800780305400107010702ca0b600140c450408803884105645207018a201c0700148010303803a03003034040000c030110341e80b041d5000341ca81214680e0b81d1820956961030440d0700901c5543c0a100421942018201030301e42c400072030818429501150407010516008400701c1400243c03186c41415060420b0034003240c1d2801004400e9141c542402e002c90382d14952841141d220082134981451140311644c10b54082c3ca04032001c0d226400d54400202c240c80c0d80300241a1081880e207004142034050381c0c41507401d14049100058110303882e003481c4017000302058000365056001001028284401001400d21680c46501c6c0c5090410240c01e00504050a4880e2503041c0e40c0008420b002082141060310b04458044880c0f034001e5566160403070511100c951801d0f00503209005003d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 730375827 1250 730374577 730374581
    0x3050304030515190e0a1709150c190201021905030a1b0f0210020c09040f030912110d0c05040207030f14070b131704030b1504020403030206070c0321 66
    0x84900800440311000098400751290680907240345132030030910651008612003c1d04980c1c051050300c002d5503486006501c400f085180e0911a041c030840b0300042070661840d01240070100c641d042443c190400c00c60401c8155a01c42124904000e100700c070420004683c400c004581c0d520043d80c0b15200d01d5500ca1500540d030741c00520404010402d103640841d040307103040e003950003031030740240005456802d540c09100300b0080c002051002c50107040d00b8070380d554031050207a038000c40c884c0c14101d80c02801c6040041800f502034001c1c2450000708600d520201e88418004803442400726000ca05420b414540f10031030b07070110790286410500110b0002c041c10b8101901c00c552855603220b00504401940a03000e4621076443c00601c40e2700038a021480d1005900d00b43c00800d031140301903601c20020700c001c419840c2c00c154011100c0080c541c04000c1407411500b11602c000c0800d980c15424641596400f94072100300070010002c1108401018040c54400c60201c021081c204146102c80d1001d00b4641c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 730377077 1250 730375827 730375829
    0xb0a06120b0906132604120507080c01170408030a1d0f060f070c060b0303040b0f0c01060b0f041203020a150903020c03030f03131506121119050103150801050103050304 74
    0xc028000c02c40090304a00c180329002e13079a02c1e801080014140760440c0107040003c2d5000540308110418400403031443c030382d143c03c01c03502da010f04010040301d450f000600d8940145003010a04010080341c802e0200407030b0049464009900000307140d240d0340d9102c151001070030400000d8141d103240003e910440000030031424a10700c54407003503450341d0703403000c60200d807000d01680c15100140d500c00b88000070408680c4010300c0e21034000c05403450260f46000710000345d00300004100b51802c00084c4403140c400c09104040090143c7c005a0b400d00e40e4801d00803003103000d140300d00011800c01100380000c05209100301664158041030741d200441035030301280024192518120b003d84074840720140e0078980042a5201c65400041c0303286035a440c0007148580b01c5c104d050032a5075004072000004000428040d1001411000701d8841078042d01b42080c6002607004080c0034002c04007150b41806c06c0c2041002030056410a0038045901d8030a00f0b0b10800c48080c4ea44001c80952a010000c006c0120200042c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 730378327 1250 730377077 730377091
    0xe130501150608160e0102100209011b1b0608090a030e060715020301090f0b0f10090b03070e10050c0607030b0a0f03050f0105090f0a120c0b090604170909040b0a06120b 74
    0x4c103030a41c0c00c402500c04041c4001510301690004410048449041e0010041004c0600d002c0b5a0080d40c2000243c010007a5401110405603e54000004000c1480000014092071900c40200c0c1400d244907074484010010290070008002e0002e0805d484050403244515400710b0f910901c001d900c00020000d4000380900c507202810140ea100e8604040d000718000b400d401000700c100c0b240c1484c200300c1d204062001d500c092050880000603103158100255104100c142c031080c1009210b2000c1200b400d1a80c000030081c40001d105203040901c0010b00e00d80d005195050008802d001e641c002020040d41d03500c2803060581882d070200410401050302c600c0a80c80c2d8000b400513031500051a85c586400c80065030392035018900c0400410940c80307549941e86080e0808141450903074036014280e180850b1120050360118050008200700c3d00c0e4002c1a210440d4404e600300070f0004001100d040c00940050990b151a501154000c0000e5006400601421803128111821446c2c000500780088a6203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 730379577 1250 730378327 730378351
    0x60302011124071b0b041b0605190203160503070b1e0a0f0b0402031501021038030601180501050906060d021303050f03130f0e130501150608 62
    0x800810700002545030940c0d9040c00c0a416054210008440100c80180582c0030011044030403001c021a1403400382000e4091100a912403600341007110803441c0188800d031000050550030440c03e5403003811f5801c0307040b0340e86c1d040c910700003080340c00c0380b840c014005108291420100120104100040244000ca02c55918a1303c5036031004207240400303140d10320310b0071103900010006203507800b0f0758446841c403025514000b41070000503021070200d8204880300c1c01010008a400c141543c0c0401413501c4bc81040101030000490703c0d44940031388021b8981c82d5419030081000c5400d030317110900108100580250032030b01c041da5240c0326100000004100f140b4518034050000c6440e0624030322052140c1d80290400349848003010b001c0c4020f5010ba10085000080c2c3e5002000141d0144074800703214411500550b1522001400c04001002075840441000040d80c41000010442e0703482aa000d80c4800556403d170001c0c1c140786001d041d00200780003000d2400880403a1141c2c12824041c05043d0007004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 730380827 1250 730379577 730379597
    0x20102010e0d0f0e15120c0f13050f300f03120f011205060f060105120405010204320d080d0204090615030c080c1c0912030509120313111306030201 65
    0x24080f140012000505441c0345c1080b820201c1c41540e00741c3c2d07412291442000f89040706501845450760442c9030207880920826204100901d401b0010707001001c82203404240c82001ca41c14115900380c030f04400b40212159000140011005204640c0b14403c840b0a90355600700e64070382c104508608544102c0012a44000400e0b0803200500031050640e01000500c040d890740302081510420050400d4104041000354941d89000d42d14082d018034482ca00140e15a420300e000d106035008205c01d11007201d119104080100f1044c41240444032909031101c880941d0f40d4204101284100046202d00c50300014001540c0130250b4401022600c941d440c0b03851042e4695000ca084d1051088008000350ba0500410400003803040141074000c040d25020940140c2c030601c54056480c0f07000140c5140300c0d103c94203e0910b0701030045a51280e51000a0000c0480c16950009203000207000c402d41c0038400076100d4100a142030519020031001804020075400210700074010380440e000407400980580c43c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 730382077 1250 730380827 730380829
    0x1020409060f080d140c0a05100606030e0309040e0a053705031911120d0b03060408070605072006190b221107031112030105010f03020304020102010e0d0f0e 69
    0x2e2800a48004202420f01c800010501305d48030341c1101e05d0b403a020b1400f0030511903541d40c20000c240c031035407084028120402d00184050708840081d4006001d05041c218540d142a8000c001c940e00c0000844001a60f1014060b0390751900c4c4417800010401d2003440101c0c400005001d91140c03854440c14007403810f101c042030540b03100718860782c0e006101da4418480b80540d5903024250700b5490031140b4049034501c480c00600c0b40303050395940a5000c041d100003401c12040c0010f004480008078143c1c01072405050980d103410151080b042d018102503a43e2003c01c0b192441910000d000100f1f039100d0b8000300d40b19030400303a00c2e00760544900c40301114803680c04050400c20f00918074000300c020001c142c4074605500400e01001e0420704118103568910307107407400c0b0f04500c025080c0305000e566400f81c2104c0c0c0c443c0c0e041c0b83c4959800c0c860200c50081c001007040c1c1e83d1203003100c0107564040c9409030722034840d44010703405403201c00c1541c1d066000b00d00c0030100b1940e11141700640c0341c0320b9075242c2284400e520 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 730383327 1250 730382077 730382099
    0x70b040f05370f020a091a0a0302030d1404030606090c020c0103093201110301031203060506031b12150307171203040c150c0c08011406040f0f09050102040906 70
    0x2c034601e07240d08a0354507a040c1149040d200a100d006049096a000031980080c8411040d50450614541e445840e22104194903150702c10140c41a02e02050050440e00043d07030310201440c1c0c000c100100e50785010714100303140c0e0540b40250b0b40503400b404280c1d1600b640c08050900030809000510070000c8201956100b4082c40038a507400440542c22101c0c640c0c003903c00b01345000c40440c84070024800e04061500700f4440e41a400c491003101948a50440c80e02901c2400d0346607078001098208030b414007455a40d002165000340c1c15030050803181495051360640ea000311851107101000c010700b0080303541c404640c58000b00c60100c0075682070948841e002c80114940c00100c0c442948040f250070110442e100056421070302818a00c45211b070741d1500100d644030a00d441c1d20006a8114100041001d20001032000d0090f5034000c0c003c2503c1651201c502d081c00414071889140c480c01c042065980c0c0758001650440041020302201000d828058083d60080c42942d80c0c0b0381c0340c4180050344545c49 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 730384577 1250 730383327 730383373
    0x1403180f0d11030f10140105100203033c04030e0607030905060703230c150702061311040c1106010b07080307080a060b040e090705041a01050f070b040f05 68
    0x40000300070341c0c01070302d44001400b01854000d03010300c1100aa002d040e002000a01402840704030003142ea41d504400f010300d0200d060348618020a01044020480f68001c01560384c8040c503480b0001600c0c6a40d0b440c8440480b081c18104046084000001040d010003103540e0b12980c003a48603080c0c0c154103081804180d00c20004040e0025584010501c10340c0b80000007881e0442c000d1603c0300304024280c1001c00380c103041c1d0426403d0150000340c078a0a140003030054115920884807424031901e000303800a900d51100410912820b602403c025040005c1d030710a4459520024000300200811396101403c255114031510304580300300000007030740d80c16900848a03ea54031184440c215200d0300809e94800002030305aa206036151003020441e440c180010b4030080017500c0341000203080954145090040c2a040b0038000c1c1d007010800e000c0c000103140f00c0400540c0c28a0070583d9181d22042028140c001c01a004020b130402200703000c1403041800480f10028090820b5803001540d41c45c41c0b44905e095 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 730385827 1250 730384577 730384579
    0x906030f070b03130c0608090d030c0801170a1b1a04030f08031812030403030b04140601050714030a0309050d0804020a0905061c050715170a050709031403180f 70
    0xa00500002e02c034034002c0c5410003442e00340015429495665850404a182c00c02c90000d2098003c00c801ca410402004408400600341041041d02c231282c0108400703014003070f800c0c070b030440380b8450f50401504010001d9810380014010030708661089028942407640d102cee6103864403080c1403070542185808200c80890745c1c805001110003545988001c2c1c6600010071413008030042d5090041d100006001c06c07810540000c00c0c10365203241900d00034044501c80501e4074092403414200b03401611030b103e0102c2e0442000d0030129103841003440c1810061b44a07100342d0025002c00700d080c140268154106c0b805840c8154150758504202c5a0111200b40d004c40c0c000c1d600c20180441008002815442140c0008001d00941800d0342441400c91a0400c02d40007104d0301d41c012070042010301a000100c5076104442e04e80440e80d0007241c15420711070b14014200e040f0090b030302c001050b03015003e02c1a00000350340c003100130b1400800d0744100544a800c842c50074042250103040441c00340c40c00301442011904 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 730387077 1250 730385827 730385833
    0x1d0f010c180b03220b04060621240f0e0a03091d04020126040b01080601090b150a020a0c0807140d0f03030c030216060e0d05071e021903050c0906030f 66
    0xa14403ca46004c0d41e014246641500d440900c0000800d5110401e14462405080d001c202507140400c1ca01c0c10121082140b42c0ca4134004442e000000d8000c4110014001400110003010a070389518800a155001150b1034442c60701c1410000799001040c1440458000e0f03c554107201d59403480040d00c654406141107011510f000054010340c010040c0041c29079810b0900849000110601c10b62030500741d82c1030301c820403648010012030804000403405001c0b500c0048c80311140060205900402c040320b000d00721080072a040c007100e442001386501e4903400420140210781d50701c180039103505880c0030304100c4001118410003241010706c2e5980c6426400320a61801ca06c160b1000c030000c0c40c224400d402010f408100d2000801c424054800d403690207070400140084104800a00e020940090fa00510105111a030b0219150349950800400d00b130361010a840c02610018001c242c101c2c100c9003c005910380d011080c410009118124544107075281001c6071140c00c10556a19120f50085150b94 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 730388327 1250 730387077 730387081
    0xc170303130b19020c01090c08070803070807080f03011206060603110a051b07140a0f0b0f0304080d09080403030815031018020a09020a08010905010b0a031d0f010c180b03 75
    0x14208614a5500407098081180f442e07059200520076a03000c1c240d1401c9980d1520b12000520121926000c02012302e10004c081480c80c00130016224058070002401c05040890160305101c003903000c0f100c1c2e6a00c00c10019035a50b07120b1411000850344500c0503644145416070100307045000b48280c00c0c00000302c2d422242802810b1000321110fa00510708581540103200080009034010403550014001c1e4bc146c4500c2c06040c1c0c018040203441c6a03020f0004048030520401824a140742120361205064003956601ea8841c20603540078030482c4c6400481c4c0d49840c8a81040c000c1180140040d00e01c41d80d90b1110645980c8102d40e1800c070040c05150f40350b080407400003000085036201030010780004500c0c020701c0340d103a00019800c0210b60701500490390002140c51071994014030803805852803080820195050100780300712400345208200901d0b5031585000802d104070103104034492940000c95884164001086019005030b003241c801041e68213002c542101810344240b001d45091401c194116 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 730389577 1250 730388327 730388333
    0x1404030201020a020909012c0f03030c0f0901180909060c0201140a0e191a160f08270c1c02010203030412140c070e060105090f1e0d0c17030313 63
    0x140000d41006203c2d980d5002d480311240030420301040400301031118030112041c1500345810200b41006a0b8181c0d00100104a080b009501c19202d0040a20320a58ec8510380c2000603140713980d00340b4141c04107040006000450450b25044101528400c180501c10501c00e0081a400e17900c4c8a203510480441007400102c140600740d000340380f0145220101e8901080403048119001004a001c0d1000c0d8a5170741d00c120300350940110140c11449480342450740b0b051442c402840400c0300703420700303042019000c04034180a0482e10482d00e2101d000524143c9070f040e11100c113a581d1440c01ca811f02a5085d4070030b5404d04c030303038031204a0030858040e00954550740e5140e88481041c40212110000d02c030f01541c141e03801140c0040075184c1707514000006c2120038144001d034140410010903e50400c0004c0111451a0711124882e4011102c1a1100300a400c2035400d042049440510340582101c1500b07211000d1051a111702e6007100c10701607034030304500001c40c0c1d400d40f02d110030dc0700074080c008100214000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 730390827 1250 730389577 730389589
    0xb090f04090b0f0a020f1821070b2a010b0909070f0b130b030c03010905090a031409040f0c050405011b05060403080a020c060103200108150f0301090b0f071404030201020a02 76
    0x40141c10890052401c4c105198800c4075801682e041c21030b04440511143c5a42070052103003104460896008c1c05c00f02810003495528000e0380101c007119070010a21a01014225a5264040d8883c100b044407201307040c24194000c10340c4241c1d4510550003d40481c500700070100340d04081d116039803207200072a410b1010a62950780f00407941510740444000008200210744051401200001c161555a500d00b400c44000e80e04090301d1086a07410040000d00049d40150800c640342d406070303070030329121405030000400070071140611410700c3e401c000c074510141d503102e0024415194242c0b05d84082c1c580000046150049050000340b0980c04180800c0100b8014000c4950054180d04050701d8685401a100d08000080e44220b07860104004500c0a50050386404010643e080c640720101c2d260048100c010b090310382e6800c50040c054042128844d890070740241c034607503402c0047e0811174289607070b80c01409401110b143d400178110b240340c40c900e0ba0040c421902200e030168020052441070707400700a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 730392077 1250 730390827 730390831
    0x1a0a03150b0426032101140915010c05060412030c080c04120804210c0602011505511612090503060709030b10050102150603030c070b090f04090b0f 65
    0x6001e0f04481450402e051040009050982e460f40c00340920005115000704006410f800245254002449510054a86030303101540104503090704100b9090f00d0005031b80401b01040e001e4807034080c0104000500854006180420301c1d00d990411880c15000350441c1c840034255440d03540580d0411003040103040070340c0180045805617400b181b40960710900c0a0f000c2d05181da5620b070505000341d0400c103115040801c00018078041c0002d100e6440c00c10401500940c55000d01d902c185c01c0c03d1804403c640306c41507401c00d002900140c0c2c903040ca071610b1a41c1180c0b004000701d9110b00944a441085203010101500d40d4904810700c2494040c0c1c0035600c10040302100b200041c10098000030025043c1c0e010042207001300d031140c445003041801c50400c070520300301c0208603880c554021a0b04200070390340080c401001c54038802c0c840c0c4241d1903140c00a401d45c80f40c0c6c49030020501c0b844901080483c1420000d11080c14112a00d50140c81000180000e494503a04050210000c1d4800140d0a41000300825 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 730393327 1250 730392077 730392119
    0x507090503070936150b030a030809011a13050a090609140709230c0d060e18061b03070210060b040e01090603020907181a0a03150b04 59
    0x150103521400803078035202c0254800000c407a103656640f0410100700d01c0050b40c098082d8400b1801c000ea025601e07010943c1110001c0020008800b00d940501c160751250000030701c001c2c140c0d84840c0c0c8508005201c88001d0702c500c49035500c0d04504803008802c41035006141c0d60007134000501c13080358011142c02020300614408025844c0c003041d4000414912a018507035204421010354104511003072480c24030590010180c040c0b801000d002c58020760014050132610941034104503980d40c45203000e040c0520100c030312031941040030206a00581c2c425541c86070f02200b481102c9203828088465503520305072503806850781104030071658074425800460340400a070041340ca1000584034510102e40070746c0d101d40e00442c008101400f050303400040306801090191407d00005095400003540c10038082d05240030301042c2c00800c1a108095016a00140320201185000005494a6081942c8005480c40000f0b03c0e004103900e860360584210815118100f10342070816081161500311000510444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 730394577 1250 730393327 730393337
    0x60c02120309090f28050708060301050c0f09040f0204080f0607080705030a0504020105091806100518010c0f0b0907150318080c01020c0615120604050d0804020a15020f0c19090507 79
    0x1075a8081703c0c01184c5c44c5d000c1c1240360015992820060007420264080c208600c02d134107140a100000d2514803d451040d0120200140d891030041c0c0010020101c101c4100045400441c00184403017007c1500c01c1e0801ca0441070320791a540c0c84a040340c064008a41e290b0104100b48041040d03000d5503880700307a1003031060503e589440c007143c001039130401080d9900e482d10300501c410480e45042c40b440001051085003081400e00c0f00481d01c0d42240300c440e001c002d040003240444c0720144200c2d51209614540c014074160300e13504101c1d40154840c0028014004c49880c0d082c0781d1000e0301c0c0719110350505c42624070088143e00d4196a0394110543c0b141c61000400c0d074003031244c82d8241d00240506401101c078500301c3c8031180c51017014043c562411210001d036581007141000b000c01c3e03010480707070100e003424a4a10b40035500d070320004a840280c0d4000c00341c004203120103584e20540002d0940c460041e14812684019021030401c141c2261110705101118900d5004001c180100e0b04070582009070750410b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 730395683 1106 730394577 730394611
    0x9220303240f0f0b07060509032104110a0e0a0507200c0306070302040b121b04060e0f06030601210b0405160f0305010f1403010e0601060c02120309090f 67
    0x3015100903200c00c001184000140201c07154ac003500103103c5510a030091011000c0f0001b201d04441d040d03036012100109140c894000340494080749c01c140e0b81a80d0b180502000f908010b05400140207903403415080d1070b0040c0000b0903500c070b0340800906151b01d02500309498550042d0004080c1407040100740812000c1804031104250004000b0507140c68145000550380035000080f000c014000c1008a44207a11504401d125502100c00b40451415441003201621080c0c42c0c0c1404940402c048190b9610b4440030300d221141c0302400040c440034600085004d40320200c070810003800400171020242500811b00340c0000d13201746010030056040024040c0c0b401e006028038414051013044070701c000c0d5000d4018819490b11201910a0365a650102910040741100300701d104074045081f000c04000c0000669200b840c004200844a0700d440d800e082c0002c2014141c0380d50302d07519040c = true := by decide +kernel

theorem cover : BRFrame.Cov 730215827 730395683 := by
  have h0 := BRFrame.cov_init 730215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 730215827 ≤ n) (h2 : n < 730395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
