-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1294
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:13:11.046788+00:00
-- url     : https://prove2.me/submissions/cb0ee179-e1da-4795-b94c-1bda834a97d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 232553956 ≤ n < 232733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 232555206 1250 232553956 232554001
    0x4181802030118120504061b0f02090a1a090609041202072c0a1109040908040506030a06150207030b0402040c0e0901090c031104050a0312022a040506120714010c06051905 75
    0x120f079496107400415a248d00070106450340e85040b4800300041e80d601d040c0c28403a0f0500300700001c00006001e051140e0490700d05400303005170f8654060048640c1d0b00780c01582c0c400d5100d0211305c01390510300390481c01d0041982c007880700d6005524900314503110718100d445220a078007000e141c0075514a0041e00c21307200312a5400c404a941003044044608158000c800c2c542e010b800c01c0380c40c0ca5911404655281e00072034244006550f1020280039440440c0132034031340c0f1506071005040080c03c5445200080101030b00c020b108a80e103580e1007450601410801d8900d00004220306540c1d0b94894804002d4600c21381140300203490714400c80c40014542056070142d0741c010300412005400c680d281044c450340c0c11000b20941c4294200c0904002004505210215444440f500908048000d1100752080a45490300c20f005030200805d8402c000600203049545448845840a003e000103903004c1005a501600c1d050a0001f002101102003055034a0106024070401040d40c40c4406100c4482101c031405c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 232556456 1250 232555206 232555217
    0x20307110f0f060d06170f0f0619090c05091501020d0906020a0b040c1e03030905060f090d06020c1005011d04030206040b0a1d060613020418180203011812050406 71
    0x184480d08003403010303080510811400040242d1210003100380004c802d0700c1868070387d02031580701250050600c001070000d40d040380188072509001d0868100b020000e03010300415940d41007013406003c0c80c41c608600500b0003030284034180c2020380041c0180a0f2103038851b800351050820045115100328140e0040710099030282c8044411960b500b0840700c0007074070940d6840320720381012590085100081140340041c111a4000501d580fa000c0c0c160f000c82d5100c0c2e8821001803002150703c840d101c0880f6040241100c0701e4180214502d0b001000b4000c4540002141c4210342085100e10219800181a50140c18a48040c0031800c0020805580220340c020b0058012a01240000300011000c0e6000321710800d01080002c4880c816044000e0aa400881141e05c11018000c0700e04003928055a046001c100039442c0905014000c4030050f000e0038242c805555402d8000c105e450001049001d46a00030000d01c0040301c1d1f0b41c84111110b800383c005803481d6a400401d214041e0003042241c1c111241d58960 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 232557706 1250 232556456 232556479
    0x207090f1a120d0c020f030f0303180303010b0406030e10061d090706021f06030f0b01060e010e0102030901120906020301030828080f061c0305041a0f0301030816080406020307110f 79
    0x100c40e01303420103030100e03000484d08031901c6c00c5d45d0301030202540f050741105c015616483d00510704045040d038000781c1201c2e904108010b01c8580c402c0e00444050f41e0107070902240d0b114030580464a018581c2d82c155032500e103800c1c40030814803540c40c00844d401012001c0450240c44c0c5280382601c0f0196846030342e0150b442032184446144041002e00505841e8880000b8803d9907510b991030490001d000840d0800d22020060140c640c000205040d1014207203041e43c840010306001035035912406400505005a213840490350030907940091048580c001802d54036540d5a19107000103821100b00210120181715226100310100350702298024103943d038078980358840040ba6000e4400c064107054100c119980320710075608542002000c0688a07a0324940d660345800c0300b042141c2441620804268002c001c1c00b03280a00345410b0b00e055035081286280c2c0d408080c1e182081032030340800c005086000100d0002a07a075008005000380340d000300d4030b16160420b0f08042080c215012602c0c668005081042e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 232558956 1250 232557706 232557733
    0xf0c0109140604060e0607050607020c10020d0f0809010e160302011103030f0412050c01021305010311090a030b10120809090114130504030e06131d0103030f050a0207090f1a12 77
    0x46a451803c006c1c0250b490050075448003810010200c4861002d6401406480c4442c20106000030010030188003810010b64403007001051064881101010000071402103000d494007940011b801c0440f481c2110300c0c51040030300d1040281d03107034481603000c00c14801d64040d12400110850b4071403010901c00d0011355542e503465403141d114868159007004020300181100c07030400d200804038000c00c00d03c85a42149410001025604c10b1031140d84040b10900000c41d40384c8408060300c4c10350f075000d4440180380d07403502d005100d6240203034040c2d0b440006440b100005d201254000f403901d40802d90344510640c1e2141d0741942d10800100030759405ca1150510795507141c86a40c1301a40040c03003072501c3c045500102c0001412a00f2004a44851450041c41003004485020074000091208404e40c9070540c5035403009410091a01c41003024040001500d05c07480d0f10038801d131800740c560b50100700041c6042d4207540005058025114101d000303140f803d4002d6142101140800030201e000401001e1250316 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 232560206 1250 232558956 232558967
    0xa17090d0b0618062b020409080d0b06160b150d0c0617010b040504020c10150f08060601020a020d030c02060706051603090804140d02040617100207021c03020f0f0c010914060406 78
    0x103031500d181410b40c041544c01030f5512300541e1003042c0130340c10690300e031541d400e0110b007107030b4460700d500e442001c0410088039245d003903d0005000b02d4109001d0046951581c0344c40303d02c1d0301d40080071640403075141c5003a4100300c030401c031000c284c0d0050b0b07543c181040300c2403166000c1540b00307014200500b46d05000412407403034150020030200442c44199405000381903120010f0301d0002c030a0803650f5088103010301582c01c60b40c0300d00c1c00401410b0000c0070702c0e090545c0081c1d110b52030101301a018003c68a803081c103050280004000d03c66000c0c00085e503490076401c18100902003038030300280d5440c601381c074142c650b0b100340103030310070f49400c00c00303140c40d1a00d0302c003540c040449000d040c00c0e0400742c10101d02026a64904c502001090700300000340643d400598001d041c001640c2a20800c284103000701000340c0c80700000b10303490306c001000d44032400c00c56003400d80c6030000c04003075440c4500c2000084110782e00c0c04105c00700b08102c283c031100030003034844441c0c201d61a0010281900300c4020301040141038401e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 232561456 1250 232560206 232560259
    0x120b01090c120e010227010f0504140f010c05151501180e09010603060e10060b130521061609120512090d050a0c05090105120a17090d0b061806 63
    0x100051030441100d03540700710036100882803181b0444071807100042d542c00c001240807070050b0740391142c0703440e0030400306030b01050014402d103000310807500c0c411903141d000e0494002c00c4e82e0880c0c2140c0c000d080306024a001d243d400c985441c801c403c0102c0e198129405008011580140310021140580c1011074181422030010480e548541d00c6440010121f110380c4654040e400e0a4070240c18100800750500c1c0655010350311020b14000d080160100300103180140034251203040315024405c1000b1081044007844241081c20a1300548050220103001d401d1902c2c9085030317030b0700c4542c41c503a924000c040c2c44c01c4c00c011014110f9007000b070f058180d40c0d07000c000402c0130201c000e0584070400125180e4a00d0054a040c00310740c0d01049003400c0c0524a02010114010300080714282045d590100b22142c031100e01e190300410300c03507081ca282d41000038100280c0f01c8100007e0019019034445003000c900030b00b016241e250007500840018110000d03121009489404081c04a20580c5120348401d568211035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 232562706 1250 232561456 232561481
    0x10507022b05030408060603060408040e0705130b0d060803030c0a140c1609050a1109040507030f0203070905091302010c080a030f02030f0402180108060105010e1504120b01090c12 79
    0x514501204036511100001407850285005548603403c22800310304d0640b01500310361103175000200f0040012922412503090f03030311240b0034219903125005c3c223403014007494014a21080b16003c0101e1032015110141c01004d5207200288901d40e03071522000d84070720083e540740081103010001a01400e0280c0340c05e1200c030147c00902c524000c0584085810004008020020300b04c6020b07041000c90302e42c2c003d440d0044e440d102c0c200400925104288024820b41070210302650b190800030350b095000b42d109040d0300984007015556890420001480d4800a0161034407905030000400c192501500030001b0b807070383c1a1142409042c2c1d030345401c90143c120442c4035082585520301021025200d0001d907004404444154000341028130402c5011702c80c811544909003105401089507200026189044550070b00b00000d0398980d000c00319000e1000c880b6240803450000030001038201402401c10742e0107004400d2140d0030398841c24000700b9110b81202c1c0300c3c0020308400021070358040c0342d40440001202c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 232563956 1250 232562706 232562749
    0x30203090409121e081801150305030307030c030203090312130812160804030f0503090312090c0f0d030e060901120516031104050108011715010e010f050a0501050702 73
    0x200c00040960b02194411100d06003030354050000107420840c0e8001450080c030ba41e440034a00f0900c024008203009121090042542050044101c0300b940008011810341c0e0b0010241d80e228140242c1e80c0d0710560701040040c3c034009105510a20a10a40b4042c0581002851518130307066080d501e00eaa011705107100b1400304168810005010b040109052652084440190728001101c818518802c4500d41c0030f1211f40c100700000a40c4c030034081c60f600c18007410300907100d8881005d4549180100000d98000301d6210003800f800403800650811031400895880d036201c145c101c20311180d805a02401400700b1560700c507200892424801070881e131081858034000f2079070700000c0501070320307000c0c0c900c2e5412402042500314110703814084d030f004c08001c00000620b483d10f41800240040014130031049000030404c00404401800d00c2500080101d4403400c98107941c662000005940081c4188000c1d124814400111420000c0702241100c0c1c05840309030078a10b940d000d111159081490a600c0c490 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 232565206 1250 232563956 232563967
    0x1a1207030210180314150606090405100503030f130f12241b020c06040f0501080615030c03180703020d0206130305030c010209010801050906030a12030e0105070e030c010903080d09030203 82
    0x50480b0540c00a600030501d590072003811240c6903007070040703008804106d102c3d40301c1004915107400d002c94401103802e4400045a0343d07a12403a044001ca90341000f0b90501000601c15142c0e00344001800b04020b49883e141d11703944e5680d8041184100c1480703070550f4242d4030341007800400c03c4003090b000c5400c3c5a410000b403640c2a1101d28044824400845080c030302090340d100662503042003c543c0e00001038603e2031815003130803942c1c45213450318480c280c104540400000c025440e00400c0c0d51107003520051280d260f0615036482031440c1c00464420076120000e440e00c020114002901030101d9801600c0c8160100d52030b000d000f07450340b10704040141881e824400000140c010002446030121f0b0a00050301d40ba4407400050180006a100c10b220309114030521a1566011503040c0003142d2045a54190425280701980503090040182816518040c1008401d84e0000b28a50700c5040c210281c0c4d030383e141000019111905580000307031201e01c050290b151b0000d4554003940c030250003401102d090a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 232566456 1250 232565206 232565237
    0x51e0f010c030501060e092a12040c080f01140114010e100f090806160f2a060c020313290706150515180a1205011a1207030210 56
    0x1107103050405800256a4401009050341c41a03110058110465024501d8149155240c200c80e032a011001da0080c0d00d10003904c50170104104540564007054190b03d13540c13402d0704040c000e1224038400d84002c0e000b4110a80d884000600c540c1c211900c4003080907401c0c0c0d081c9501194054801d060103814841000c000740560368400d004031010714030f40d40e01c0c0c0700781d0b0b140c034032000f00260b0701940540110380c00328040c005c1c0018460203685106200d840d225007801510b440c2101d1403155200111f104882c1c440c891106465081182100140944414401c011404404980e13921604250000a052400040c040c0031030f5941a01018000d0240030b02c075101031503072084440da2040d082240c10581d104400c8040106541442c4000c4c002224a681ea4420820400742c4900c01d0b080728029041e050304541040340d6a114140e00a811483d00c420840e4141385003041c024106080c03030218660541440c1c0e00340b8a403107090341e855030030341c48050f200c1d862469003440103040c0300c190050107004094080d508035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 232567706 1250 232566456 232566461
    0x6020f06040c1a1c0605030706030908040b0706021303081e0c1e1e01090203010c231315030e10060f050105031009050c21040b281803030513051e0f01 66
    0x521611302c1c0c00950300b0700d420100b42c50f0174910b502060902d8105100d1101043c09001501c08880e00c00c0d0304195511f41d5440d11034000c0c4510019120018844040481070085030009884002064100702162400c21012041ea9000e201d500240580c0503181c000d9180440004c00450078150408890340c014de841c0f0304d0b01080b44019901c4619a540b222044154a024010a1603413403c9040406070310f031840490140040240800581c0e2000c00500d101d070120152204c000101030f01c890b81d90344900d03140c01c004c025110100e08408140b00303989908181740c45c6441218106c03160311000c00c4000e4a484015140d13504014004200c900345076100140462141c01132921951003031a06070381d00c1c5480170749110b82c1c0d00d480c0c0094a450101c0b200b0000045c01122035242c214800d0300001c0321502e021100c2c905a604000790912145007030543d081404a190200343c09410b201c1d0310180503a1ba14041d5825800d8681400540280e100800340d40c002021307041e8401200c0040d4040e10400910040c0c0c8509 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 232568956 1250 232567706 232567747
    0x70204020f121312120b1f0e0901140915030307060f0506100e040e07120b010305100c0e0409020d0f0309050f060705060a05040c1508040308010b130b090102100603080406020f06040c1a 81
    0x2410250000c5200c40d03445620f0130900345e403c40d45074034154102f110384000001e503808414040d4450718080f9040294010018004650080840c0d580b50700501d0908040c2a07050a401102c1c0e00301804034240349001010008d5030340c1d00c1d6507080c0c0301d030a0720390401001c0d2170404102d02e01c6020b0500042091280c0004d5013030740d18003400b907242842d4034600c0c105240102143d0006c80031440c10903003000d469400041b007000090100d9003c54900349500006101526240d170040020b40c2ca40800820550450312810884408580301143c40d401c400070305c02948106800100b0b16081040040d81500f000d030300c0160003034050703078400f040705880d040d1300c9150002c04c43c10300c1c1c0429040d100f04070415500030049405001791808050420a103401388041594207802440304c50341001c00c90400e0344c0d1007005802c0c000c0d000030b4028018560340e420b0491050784240943c1005011340007140101000015501d4002d5620000400980c2d10b081d210789000114003441c6643d0744803c01c92030303010f2000304c080500d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 232570206 1250 232568956 232568989
    0x807021504170c0330040c05061b0303070305160e031905070302060304060207020a0501030908030f091903030b040c080705041502120309060a0c0e100311070204020f121312120b 78
    0x481c001d07040d04c2d01040304160885d1392038803c0e05c40c104220004003401d412004454013a07400b6500c0b4100800501b01703100a0111402c0e90b0311002c42040002a0305411260103442e00c64500071451241a0040782c6101c2419030007605039000004e415514040f40e0200c0450601071016248120b4a0b54000390140c0d1007074500740e450580100d0351070158504070404900811090a0800c60715100d5a2000c0d480c2c0030050070185151000300000f40840000d01c544580c0b01c4c0747d400030241c2920146006001030085c5102540030390f01e0500c1c040c3c3d0a034022554540118031580740d80e400d2520303054904402c2c1c00400c0021007140500c400d46603034212842c0256015500350005003200341303480510a421640ea8084c0c1c2030820004c014400960b45a00e07503522030071983ea00d4003240150241e05d0140803807042c144000e40203807001503400c0034006103001034101440e03120114400364030340030b24814094036400c002038030f211900380c1d001c881140035200c0c00e501c603000c040c0041780030b40e2001c000400e0a40c40c03c0001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 232571456 1250 232570206 232570237
    0xa060f030b010e0a05190e070f0807090f0204141201060302040c030b1f050306060a020a0210080403110604031d0f1e010207120c170f010504120807021504170c03 71
    0x602103e030100f606141d00001d140b4003048070b49000010703400d505041c179600810b004c1e9280c41110f502007043c0006c102400ca914001034400d0b941d405019914035403031181010756071a02c50081420314460003100d0480d541111030301d0124a28004000d47d6a0300541e040110759a5a1000070041c0c0381c81c05040b41501d4503440008050a1100601c01d180d200c44100c1c41c0000107084e060240c26400c07106585e08004251900c603180c001102c001d0f46000590b101c00303540514411448150355a001d040e113840386109136075107441d410151030744a079500429100240480c1c1c08100700c014a0850240000c1030440003081d41003d80540c3d004140e401903041040290b08800840710181c0303503010080c81008140c1c80c0e03000c6558205030380b81c2010f5040b090055840c176a0380d400c0c602c25043d201b00b00321241c0044030300080005080500c0d01031031780303203054180d1000305030018006030905002003002070700c0106290020b4031035030722540c40c034010503100f14034204815030501c4224610711080010b030040080b401c903070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 232572706 1250 232571456 232571459
    0x31202210d11090102120c010f060b070c0e13060f02091207090e1f02030a020702030312010e0c070b070e0a120f021e100e1809011a01030c02150a060f030b01 69
    0xa92040c0c81245040c036400c1c02e400c1004181590340000c03c0341d040c0a40010181d1101030f82c10066002d05480100601001d06101780407820814074402402000c0c4202d603040003030360b5503901d00d030107451007200e0000300807407000404804038110381c024141c0c40b0b4041d1001441c00101000158060b01030050440480c0d0014005004a030458481c035114001407a0003800e0030301481c488480401002c0c505c50164680100105000342519015140f40e954002c0c141e071303100d104900c44484010801d110b0031040080c03160200e86100245030445a1064008480e24010f60340c2603020340d081e45840c7e400c00d070008611036000070185007481d00011118811800c1c04840251170040005001400b2054040b14201180b010055910451190400815428060503030010240001c080403859034001c45036024030300420140c0c45043d80002030ad078047c00c0d0701445d03a02603400110205c81c60604c403c009a0b10580c03600040e0284112440e41c011010a00407d036251540b011028503007090780202d42410b080d000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 232573956 1250 232572706 232572727
    0x20102010e011803120204051c0b010603022701110706020106081204140907020a020d150c080f070c02030c0d050106082b080a02070c060906110c090103120221 70
    0x301e00c40001650300900c404550720f40401064040a4401030920242c2403030502c01c881c4c02e4041d6801010002c1c80380400768040408141201c0c01944112903022851b00085440341c002d1094039411061328507100d2610320900070456661080c2c82c1e81e54140104e5004030050700310104040c1001e010075070b00119140745820b03030b002c0c500120101ea0400e602000c0c8002e001000607540c2900e2031000846852455490740c04060b424882d000384041c0d00f000032090074100f0b014400d01456240c2c501e804080040c0401050211000d1106849005001e1079940219800500c151030500c00240020300b03a07941c00000e4030000e040e01000250480d19651142d0741004540004d212072103104d102201c80c60300844200c80030219200d8001c0006051000b0000807880e50f60880d17041e10400d0f40d2154a21000c032381c48a001a06441051240c400014400160b4007240072010410155421015190206a07401d6a8a001008a0030100d41341148110610b0122401c2c2c4054040d501105411006aa40f0182d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 232575206 1250 232573956 232573961
    0x41503150f0605030d0f12060803090a14010e10350115020a2d030e030d0309081204020f030712020906010c0302060a1a030a0b1009140a1e060803030402010201 70
    0x281c40954041ca0040708000c1c5880204030300ba0042190716042c602c0d6202600e041d0b85041420006015051504c04049015003001008180020702103400c0310001e944d500d20307981840c0c4407400040c002090019040a142085454102007000d2810006100e0000030b000b042c2408690000c001d03000c0f41c2c080403140510064024a0142c11500b064000d410b940020103507840b007510304001c1c041c00003910300005210094904920403031021109000c44452420001c0c00c1038001443c49102c0d00070440000f400c680244a54104603921444090420b60b0b488a00302c032002d4005c0060340c10550500621714035039024800c0b41d02410071381a07000412007003070040c0043c1000041280c0d051000315450390010075000504158080c40740352010034203011801e54429009030850060b43c0602c80d1150071001c01540301d103401c1c4a900442640310307145980c0c03000002610b032030100e4101d01c4210f00000c038241c0e540f07d40004c16110750406a6104030b01e2000b0045040303400c16403043c0c030710f50000700502c02150790a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 232576456 1250 232575206 232575221
    0x40506030309090f0a090c090c02011a030706032334122a090905060d0210050706060f1205010b010309120c0f12051c0e0a0206070204150315 62
    0x40e001581082803040124415030005440e580320080b040c0009107154074540c020000c2d183c3e01288600c4100e50340d50311107010381400b43c00800903500b0061200858072441d841b00c19a548024010304805260060030380040410b284440ba401c441c600541c40c0c00c1d50116a2203015a400310b03400052908113464282808244044c40c46140302c42e01d10620b003456000e900000b80810a0000240800000c15030901cac012005d200e565a2600b103120b25a074094004650f801200d2503240140300b183e40e85004c10260f0001840025800100d4002c040c49040c03161010b0104244100c400149079500c0300c0078072b801d2142540c130044094410420107010020207000b800d100310400c0c24180030181041d41c2d001c4030101c030741500000b00180b442d010700c2841100c50040c3c4110390800054403141c2607401e0000c01607445205082c10041880410701140030180c401e0f1200e02010002404842c41290f08010190703104001c140d1b409619401d44d4160000342c002204000d41c4519010010600c2e900340350010740300403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 232577706 1250 232576456 232576459
    0x90801050403051b1011180102060915071107030c05040b06070b01091e05090d02060907060215040204060801050907030201090902040b0301030609020a030f0f023c0102030f1305040506 81
    0x40105000010780c02c201620300b20411400500040d0075081c0480317242102c200c00840344107003000d64448903008803000911702c1c820707c0c8400c001084284401a0b0350303000c081d03501000300d0303208035103283c070150340802c1250304101c09140c880e0310840030b04001464003941d0740094034180b008900c2000380e8a400d219500d1b0b0603000740c0da654144500f68440d01c8407084148a00c821640c1c840c8000d02240e0b62035240e041d82103180307120400560034545c880710307603034144100314002503c1041d011804040c0001400b0040302c8513035004100010912081504011001c1c00890b000b540750b080218000d98207005052041c170080000f001294650300004054601e90b034031050820b44104001c0c08180380c1d150490381075070b800c0000810008400d2020031071501c0d0b40ea1028280180d82140c807030811500d14020f2251070b008840c245281440020044446030000940c040c00c0500002d28109407c900c0c0318032100d00005005a900b050008072a400050b4010041c90410b0103074008184800c4c50315226035a000f110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 232578956 1250 232577706 232577711
    0x3050f0411040e010f0608071403011811181608101401031a060c1b0a050d1515060e180103020907051321031e080a021e07030e01090801 60
    0x4003512031003000140c680300785014039250601001600b00075000320009480c001010041556039015040d160050340c0120703c1c1906c5181040c1c00d035480d050260703032580e04c90356800039642e450301d540d40b220749052036100c5904100c0f50300700130708040f80380b031120703072103114603050b5190444604200241101001401c84101050900c0140030312600d00c07030b85185140c400e0130700042051060f8900b0300391020442d4160760203040002d4950b00d004001c1103060010355030100c0095034101000811030501d0381740c000c41c0d801c11408010300021800c444c10000d03012541d0350001402d90541114000702e20b549030172171408200395808402a50074034060381e00340c500120b104c0751119419a80000c00044010303088104205001c90b03180651004c3c0c6040314010140a0503882c4554014940b03254040c2210805130041039100700324490001c1421740314282c0c00c0d0141e480c2106941d500840d1402508034600e0083c080b03003480301d480c40d5102c016000f4848135000c0d032900c408200000c8001040000c00340c103e04040c0c0d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 232580206 1250 232578956 232578961
    0xa0501032102010e120a0e03150115030b060d060612110a03050c09031605030f030c07050609010203161a01050d0515150301090b0a0e0d0801090207110415140a0b0316020c09090d03050f 81
    0x27480328a00c141907440c403400f20448004000011000b400701d061405130b000c90005028144c003201030784503604445030361305c1d01e9200c5044091001c04a5030030761012912444104540c00c0d03514441c0c0e000980c44180c90110364101362050020170324005140c000c501b43c1d489980d03030900c024a4100280110f84041100a502d01090914240d0300c40425202c0c2c01d00034000816403403070a070b0080c000d480315450402411840004075040c1510000d81035003210492104981c000308090800405d0075507042d4200340244251072000c81c4000181074014000c00304a0b0f5030801d451040d44d0300380144203140c1c0c003c4180c0350190811207508001c550000b580d84502c0d5000d1084202a16001000e103070460320542d80058585802d41410b051400c0e0320b9041d9903015140039000c0d540401000c1c1000191612600c4142e0a40850400d00c581c81400380151003102005200013419442c036000e10f00f842e0800c0344140c4e034a024118000c15403414041e00d032280030b60071012000e05e40310761620425522109a8014080c00e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 232581456 1250 232580206 232580233
    0x3190e0f07120206180a030b040507140a141003060510080a050601080105010206192003240609060d090512121005090604090c08030f0903060a0501032102010e120a0e03 74
    0x3d01c1040c003110f0000c028010381d0f4585d940d81441c607100450300229902d0071460a0307d41241c4594090059001c0c8414801c00080c00d0b0070030350900015951038507600b148103580e250810074020944001d400c1016280d55011840da100c81401c890307007a80b640c03241d0f03c2e1810010541010384400038412030401c110b120040015a030b00103003035a0415400036040740c20940c01040341c4003412100c0448504040d0103c810400408050005d52140c0108421995000800304e40020b6003001d000724594030000902c1908014a0164014041c42013484800502407941703035616414504401d0413000310074400300d0031103003c0c10030024039540001146547c03d0400e0800780040d6681a0107010340d40501d60381c80d1035004024070f610002025001f07a01c00c0381e84411022143c6900c5900c8450b0041c040c2c041c10002c074030200d0b10390003958140c0354045420304410340366105210724002c061200388219900e52880505155081c410503001e00c1040c1c1c60b0590740d030500780700504240c91024046000c1d0b8042c1700f018500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 232582706 1250 232581456 232581469
    0xb0112051e18011a0102061b0301050f0d06060b0418020c100203130b0114030d02011e091b2301081302131103010803030a050c0c1203190e0f071202 65
    0x10506496101a002d45030448aa401c07801e500b001d0042c151300c0d007407207050b0036445a00c09201ca510240e084649a580e0554120308681214050042c10703c02030005009501d0000280311100001811340c942c145005d8a41d0010b0314869403080c4032900c0c00003024043d0070301e01d040502603100040390951401200c007500c00d1369100d441c2010020a41d01101007603690420800300e100c0a42c2007071154029507160314110780350600702c2c48124800c0c03240740c00354049a0b00602803200281d5120034041c0d86180c58403070726000340074248002c50716006180d00340d40c46004856144009403018203504440c0e0008018a440b0712480860145d0512030020300f04185418803190f4804e185a0580e000481605007601d9000640a030021141c0c016030040004200c801c4004003951060311580300501c40d58954201509a600c1000c040c1c039140e8100c6047e004007042032100854201e80055100c015400c03a04031000b046503d001301444050b080840000380a1108121030b801601c020711341d1000030704c0242c1c0004c44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 232583956 1250 232582706 232582741
    0x901020706020304030b01141315051e03070b0c030f030703091e0506040201120b0a17100c021009110a031101023d0b0301180303051302062208010f0b011205 69
    0x3d01ca030300fa8280146034443d0020b2703001c5064450710500404400540b050b0384203900b40110340c010300202d0b00c00307210031100f10390000722250040d010340b0b252400e085216000340d10000720b01c05c0350301c010404c001044c050a0015481100301340ea00082e00300c030342c4c9080c0c0680590718080c103100004807103803074010030008035105420640c24240313030140452003107044000c0d0031304181099000720f03400da00080d4840c0c1c2d0b1090300704041e11041543c010306529034900c0103c030350075041c01d80148e010720381c820014402944001242805090044915411103000844040d4141c004441c44440110f1082039540c04100315005801c0070700d403c012445015110300050841c036041246800203414100840c881075500c490410b0b00003900921403102443c01e41d03030010030720183c11000686418001010003546c60325184056500030402440c03e145101e044401d405c2030100c22034001c0284000060600f400d01c941e03070003400805004501000340b64005001070420322030602165080508000240301624074060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 232585206 1250 232583956 232583969
    0x15050a08070c051507180b0301030c0e040807020301060b0913110904020703030605030a0803010f09060503030901050a1b0b0a0b031908300a050a0207020d02010806060f0f0901020706020304030b01 86
    0x3200d01d03030035061682c94102c4072203840300c0e0000d020f41880002580071130403201c0c4505e00905406d0f415600c0110683c02d2000340b0028100040c981c1c030603c044030380b080400e50814018030b00315003059015000a82107030641d6102d101590300000e0b00844500b0160f038649040325180070104520326102e00c181180b4406c030780c10180705540c0000c0b99006c0501a520440240c44041c4c219080d2881601d8800415402801303a40800041e01c000000e0500c05400783c0401d403480540a1070405481d0001036070f40c2c0d000550150300b402080322081c580b145203110002c180030f0203030742030050714108955160700312441d2141d540d0090300844e00c0500ea450151144101c800c2e0701206075555580039004408040140b06401081080580810f006900f5102c9070f4034045c070070348482041651140b0b1019403c911076203900035082609065180050360281d8049688000003400c928a00a034100986c3d41e00c5d8031a80382c003602c541c008104510175580c1000507201400b0f05000852809045440389070421005110b0030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 232586456 1250 232585206 232585217
    0x1030e010b0d141f090212060415051314060a0c0306121b05090a0606260402090c0421050708060124020109080a03091208060604060818030307080115050a0807 70
    0x680f2414010498480010102102c00301c84a01d03459412005d0b100c0340f0805e070700c50982c0e02c0407080301c401d010400a00a56204400c1c2c440116042e880070061b013402400c0d801881403107c0c0c2d01c404140015107000100e035140006d404a0300c1c01c4c0c031011007100d002060500400d07140c140180049034800c10001c1c03000d908100b9202c84a130041c50441d13a44151608410382000002c0280050003186030080026900c6030348444d5007000000403405e901750280490300a190200b070020502604142136520b03000081001c030680b405031120380040c8030840d401016003912440d000100d013804824072546000d00702d040c002d0200c40d4036019038204000c90700584803044408030301100700603900035442400740a078410300d000d44402070000040c004010002083e144d01111401c1c01104a201e0b0410900ca124010310060509081a0044801d514010049000081c061603000030156041028511507a56a40d41810960400c00800b582030b0030007103100c041c020140011581a40c01622240c1d112400b807902 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 232587706 1250 232586456 232586483
    0xb0901120204050409050a0c1d010504021b030a11100606020a03050d06080601171e0d03020d0b090a0c1b030e09061807050415020a17160c0f030201030e010b0d 70
    0x10300a210b03c0c0e0003203078003a02c3c00000c5820040080781d103005460099440d220000e9a0394000b00f403c013010480b071150b040001005100c03528140d80905060300c404104241d4409042a0452940d440100d0340008907800d01107005610004116000704064141410700ca501e1400c031020b580c803015040006c0500c003020036000880541a0b1009000342007a901322012565134820702d052410440081e04031500542c01d8007590404d000700c15400084c40c807070082c034074100381a800314000d4204180f6031130003503101c070804a1541c0e100708074513014045400c80009d2038140c00801801d40c14140c4802c211130079500482001094009440117580c03030054807044041c0c4d65141c00642168010500820307a40a2101030140305544100030f00700f40c07401c2c04260004c2c50340ca48001d981d034010800001f4070711b40405160480d8031750858050226003890109030054920706503a041440945038100100900e079500080096681c14015003502170b10401c020444500d0300c44c0407803100050b0001c082d0a07481c06824 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 232588956 1250 232587706 232587737
    0x509060c010c03020306041b2f010203160201060e0c0405150409150302010216050303040b0a140a050d05060103060305060417130f0f0b0c0709090215030f041b0b0901 73
    0xc4440d0406580020850100035040140080d0030a032062401640307000030388038034080e010083c4c05040400e511500500c03901d441c0b0324000000440b0302130000c107201c50b8007606494403d001860043c01c03045040e0703181c0b02e413501000b42190465071080707212800d600c06105c44000711004071029214103580856a103a15210340060034480c6a001403006882d05c2e00d141605001d00d8411029207201740d003a20388070800c2a0401d080e450040c01501d5164000300f2003000005040c4000784424074a9003001c1d02042c51181041701550880c980400c04280002040700d40790800380b0901ea0f12020900382005120f040d922400d5a0340c900510042440c504000310384c8440b49660151100c003241c0da100c075010152a401402c800042612400442811800c000b046400c130250544040703102c0f070001410214034085a40000d05003001007a40c100780c40e5288158104419402148034a942c50f00d542030301d0801c0e141c00c00107055003030f03100c103401c00d070200c0144021002142200c1d400f81091a01e684162003110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 232590206 1250 232588956 232588969
    0x1060c03020a0215030a060504110904020c071707030501150605090f030705040e03070b060916080408040e0408040e0703061824060e01020d030b030a02010809010222092004060509 79
    0xb01c002e913209051000715804203580f03a00861081b2960803091020b1741e510418482aa03940c4000c000c00d150003800f011100d070905d07601405061081308204c1e5031081c0c2e03600e00d5202854a2040c0075480e40c00123401482880301c240242c00359450710680c000115490b01c0c40040490040100d1240300f60b001e03007109200c0380c0d41009207101030440203104002c181c0904800555960206008070307101441040042d00915150340c01c24400c59215008041c03040d0101d0301103800d142e000f07000325541181480b0103d0302c0c40c92003070038030320461048406507903603030403c41618a0300034000c151604041c24501d05029007052503100522401040301d0115401d103640311380401d2100301c2c4840116021805000060941d400300c10600940d07000e80907214848003a1104030b00752881c42c5003880d01503000b10013071001540708401c502e6000d030704100014107125070b640201d954a024215101d03907803190850b06110300c2c805403150b0340c030710460052500e141c0e0000c0d45000e600ca002d80d206d180c2c103018020458500549404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 232591456 1250 232590206 232590223
    0x20f010f1224060815040c021f060303030e03190318050157030207021206100b0c060105060304020d0b0103030c03090e010303020318011101110306100203030f01060c0302 75
    0xa0028440c02c40e80841242080c0082d107540c1550070b60721900014000d00412241d800307980e050703c0c4107180040400c248400780042c25400c008520900b210281d0f003548103840449048581030011900c1480c6090040075903902c2c00c06082c00e60010060040c0500c0c0c1c4821003192081c035418042080700302440c0e400380c000c0d050500942513500302400e180b00d84d401ca580c9204428041c03190f1a64041e070400b10000306803e4a0301c3c4150507180492000c00c403c0040e0032854030400f803440d01524000304c1794040741c0281c0c01e80b8a5084240e000c00c05000e0080107032680031010341300050005080100d8140b41954500701031054500035880000400d080d519100380d60542190000210b00e41565030780743c02414003140c3c12080d0000b50000b0300100c0c0d0221000d0a0324120307a01540214100f4030304481c034040744441820640c0c10700c039401d94868403005081c060340281011224800340c0340d26002048c491041e045a9104c800c541080040080c20344074007034500e055903101c1c0ba00c008000086c0c80e09900e060070f00f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 232592706 1250 232591456 232591487
    0x2030d0527010e010606030504150504020d20150313242f0405010903020609040e060109090203010e0607090b0c0a1b17010621021309050c010807020604020f010f 71
    0x94061030510504150004510f00c02418000c015480d03072203001300e04545082d03500030400c605411099a81200c4c5420903508140024071103014074081c0d41da4669201c654241c0c5401280c0c00340804029131501502c0e1a80800c5180409451440c114494658590709500003c0c21401c0e4070701404070b040c03442103044051a807400030800012440000ca4542e50042108095404018540079060030f040d0000380da0407070f0f0040e10303403038291401e541c200081c07a08042ca44030340090790b030342d0b98001500d400c008050007081c00c24000540001d0300e00515095401107590742a950380002e00707200c50603a128549030100d520f0812580e440701c1c0c50415031405c1000c80c0c2000b03883d0070f4101403000150401048a00c040380c2030384c01486c205203c60a1030f1804d860300c911600c90309101200141401c01d28214907071350040d00c003c00042606d03050a00010031156800350540f1660b0044034130700f6103540c100c080e55401819500003450680b8242c4d0004050140d1205000c3c1000142030300b00105a001d48103071410350390b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 232593956 1250 232592706 232592761
    0xd05010b030d0503090d0c02011707180b04050102070b030408030424022a011505100507050a050c0f19050d060209041d0d0f0c12020a0c030f050c090702030d05 70
    0xc082c8001c3c801e810941d403186090080c490003174080c5014920001100e03506841d20003035040c204a400403a0075008043d031052100d049811003480408030125800b45c50611041a00c1d5401e140c0020701d0400e071f642040c80207580400521000c103100d502074a034017941c00807034001025101c1101c00c022181c1e205181c01340310700129100001a428640f0b04100c2010980c82a03038600c10b26422600303031040b0302194483c070180300c001404203050019910207882d81c1070420514208165440504d0030074288402c6d595508003d8080c0240d2a00c1c1a902904210440300102034030412002180f0140292065610803910f8040080c00c102c42c50301030b00d40c410300c000c00c200020100c0429940003030b05140c56116050003409401401c0a0050b07907410001e8400e592007584001e900c1d96040040300412401900703501c10f499200000594401104001c5d41c424543c0c00759031842407510310b01c0c214148100c140300b02c0d4403404000c4d4561313002003540c0070400e4900010540e503c5001e01e9544540c0800d6422244c0c42 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 232595206 1250 232593956 232593973
    0x6090f081305040b010e010503070e3601060f1b02150f03150108130201050c0f0304120303200d0518030d1e0e0703080a050c1c0813110d05010b03 64
    0x307034000341c81084600c180c500707211448111004460644200c41c000303021400901c04036881ca4450b2450114400340541004a00c01c1c02d056001e00c0342c0c610f40c40811140201220240708084a540041e0040032582410142ca40481901410085a581245600041121a10707040d90b41e1420b406800411102c9203e5136501d88074111411980104c85102c14003005c09481e031125449184030f184075109081401c100900540d004540a610084620030284100304000c10851402c0c40280010054103a0300c10510000c1d18000d019180000f0803c919661003a045c90011000c01080740e0010031241c0000406580d00c0c5e2002900740c5944038962078a03c004210059200c40e1507105491440c03800d06007270807105100b40c40e07038252030b80308190700d641d038101c0d550800c009035984002e002c9a04803070501601344241000388610f001c4054410709015202010045806c40c0c001212030b821001c00e0b14803400380c515540340c00541180f15600c2d01d00582c09121440e05002081d0b2000082d010010700340d41801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 232596456 1250 232595206 232595227
    0x705120a0909060e090607080c030c2808060a060503010806070806030118030e040e010204080a110a031202031c0b090c0d020d02070809040e1506101115040507090b010c06090f08 78
    0x6005c9403001c4091048401240d03003107001b21043c600c1170100510035465a90340100f03c4407203030400200002c0c042c0c4107135107501c042e06101c054921419151795882c1c2c80380c0b07000f000304444000c0b213501c03080501004100621268001140fa55405034941c2403000700307611240c001c00c1c014010103042248030000503903030504159003c03819188603041146c040c0b10b81340300d141c0c0c2c9608030301c110b10445406074401c01003c400692102828840e27a080105411106642ca071a013009201d414405180140c000003000c0d802080651058402410703900f60402c962820840814010075010388180a420f8010800c8440c00c41c054040750081c810000c4c09640398070840ca419007464000d109014855820880c070000d40c00700014003000d580c410707a415554140c48450610040c1c1c40220211020000d49900000c002c110030040c0a1176403401c101c51594501e0300c0d017013039414803417642c0059035100c3c10403801d08801da9001a10504d49900b060002800c0d00040c60000884089508001d14404010078801c021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 232597706 1250 232596456 232596479
    0x12050406050a0608030412150608030a050c120301060e01141c0905010b0418030c0204110a0f110d0203310605040311030c0109030f0f02060c0d02070b0705120a090906 73
    0x1d22200b00c000e0040c0c546511990361640070b00d0042e5518a070000c0002e03030214010380d0141c01c0b07505140c2000580c164070fa80300340e42945c0c40000300e030340829030020328105580010068460b11040c00703054a41154188100140403203613800e13026041100900c10001e204d031020080340d401e60b91500c030070840c41461606082c050080c240041d6401d5107084200303002070a081c001e0440600700d048071107002c2d0b03a19a60035183c5042070202660171981d2070100e801c1c2c242241004003058045515441038030111014014200e4896a43c044003541110b001440300640000913a07840001c12841c042a403081f16840e4621806259282c0001b8400101d0001c0c4031a0044020400d40340500858080c10980a040c16a40c100e14424070340051303c0311000b000802c00d102144c2c10f41380c0c0b03e044000b00162180c0c001400036044a09014200d0b00303d000700002813a010010745004040c1c2000c1c250a04400da116113803034220380080000881d000007041c503d21071280400030054107441c0410070659032550141380071b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 232598956 1250 232597706 232597711
    0x60c020306091c08040c0504060906050906031501170a1e0302160605030105010f021f0b040c0c0203120c0f030703030609061e15210504020a12050303040605071205040605 75
    0x1e00070480811a030034808240c08242c07074014900c0d020507810300070007107413001c400030b00c140c0e2441500d2401090a1362180541801080000400320380b89050070100443d031700700504028400d0f8010f60100e5030307120079007003040e045070810170039030304228000e104c25400d0a541030801002603403400404400301c0101030040030220701079401c136040402c04c5600000c03100c00318003c03540461010f2004002c0d544c411008000d0800240c419901c0084d080042c1e000703800000400a0540c9480b400e86e1030301418103105544400c62503151000303003040107801103038541c040c0301c040140b411000510381c3c7c40c24604000d40c1380009031000450359180401d041c018010700c1039002d00c01543e8180b200020b042460904405020014a012030395582e10740000489205141ca891105000c5403200088102d061064510300a5050341d501242c2d500c2c1ca441000070002158024120b038902c02d0130300401040e00081501d034403651140c800101e03901c441e10251038120300e40c42031a41c0039041c00c1c1080200242a00442d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 232600206 1250 232598956 232598959
    0x308120115020706020606060f04031e020f01030902090c0309150a020903010b0904050d0f03060906030809132901031404080909100501170a020d02040b04031205040e0105210601060c02 81
    0x7004030620010890f1160301d03602c62000143d02140204a0914082c0d0041c110300902d42c0d420f40c50280d03607a0724400b400c4840e41440300b1482c0c80552a40039404e01040100f00907409281c20421200c0c0c0d5030002c0c3e80808003408815048201200141c981c840400c10583c0390009001307184d690b45031180006010354048542c4501a500705101200c050400801d994001d0394400042e026014890074100c0d4014401040343d02056102e10000603600c0722442001e010394025910316a84454000078001c1c00d01d60003c1100080f4906400c4004c010b600945001e42240102120100d00182000480c003401e913a9081185c030315200418401006060b40082224035025280c000c01c945e00d00701d000c0d5654000d845014041380c40040200400200201c0d90b980c8900c0240b001030030311819044030740c02c98006800003001030707500040900a20068a80d000c00303003800c0e880c10364501800d19455502915061182c0d500800d040d4029007205c0380002603807e81c0c0d1680504035942985d590000070060090010140d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 232601456 1250 232600206 232600229
    0xa060e091608030f0d020c0a06051008060c030105010f2601060c060c09030302120d110c0303100f050a030f05011d07060f0305090c0108040203030706060b0910030b03060c090a03081201 81
    0x15905001005503a00b807030132a100700c2c0c1004c801a8484010794071004e005031030345c0030f0748503100000b8159103c0d0301d000e20000c0c41d29150030360420685900d02032010f0000030311888244010001d50387d01209250b01801545004c9071201840c12000c6609000044000300a1015034004900b05521101d000c801d54003814081c0f05451616806031032428050202070b005070401207001c0c0c809a000c1000344041030091900088001c02000e0401907500080203041ca00e030000000d00090528a5100c000544030054408110303a140c1400200e0203641840000c1c02c402101110405120083d4000040e10f5287c13001c00141000c24801c8a1300c0b80c3d00c40c0039400103c0d10301d00c1100003581c031034852f6138403c040482c0142806030302d110065801c40c000910880e4944000c2000200141c050300407600107196800c24261280704103401c1042d406000783d024000c043c908050b00643c3c0c1ea00007121600031070102800c44e40c4d0000c0c0008036680034507a0300041c1055100041c174205200700c084c03c0904072864803414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 232602706 1250 232601456 232601459
    0x602160504050601020607080c160809040b010809190305090d060c0f050702010c021201090221010c050702031e031e0301050414010b0304031209060c200715080a060e0916 75
    0x801c41100c0041d40c80c0c0b4010303444500020202402218150b8011001da0400d50410115094003007900c4074001c400c0342c4524011480603aa4189401540140d4509081503480c52030440c0c089a50741c036121500c4054040d420821740145400341c005c86107440d02c05031038409a144203050100c003030a0b8100b030060008406d0365100000501c41c00640b803445a05944100390340c0e00759020401400240d00c00f10300e09540c1c1d040c900300140c0d294425075807806840f41094802d82804004a0b0071100c13000303141c1c01403040c10020703000140e802081d0343c03070004c000844c00c1c00680c446c0c6210038650700850607145840e41d102e0300c0300c0c401c81113000041c504031603044030144002113010742d80d100310707820031300c120400c590081c808980000d010328102d068844050100190b22149600e40005a8076031040100100e0f181120f203510800792400b82026420452000304580c3d85400301900c0203c16100750f01080000d0680803945256903608050001d143cac0112040305030030012505a1203014030256110005000c1e00c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 232603956 1250 232602706 232602709
    0x1080c030601022a041e111e0c122205040e1f151d071d0d05030c100605010207080f07060804030e0a06020c010f031811060d0606021605 60
    0x85920518041e4084c08a0f80e2804107068425206103020054044409000421548031446200d1248460304041100122034030001411035040c0482d00001d900c080000c64041074000c0d2070100150501c0400503920980b04100c6410540004c0012002d00c0d0b0004111585803c0d0744480140001c1ca00c00407100a035440081000321040d000a140c2c4681186092010399440c1d01d034400113590610901041c101c105240440407260260010401c42414081016000310700c80c5e13119910401c182040c5480e10060700d0443e01030748240c0801c2d0300c41d6501640240070400c060003030741c05240107201110340805840601001a200500a0a0051054000c0024168000210148003c012502405d511801c149040303500e00c0c001042942445011400f0f541d4503111103215400a1105601804224000000040202d00840a860200350501801041090407501a0181603178004240c0c9011300c083e40100e090741c001c0c03130038603600140b90000014117560041070020040c1ea2050b281c2c1d694649420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 232605206 1250 232603956 232603981
    0x12090f0d050d11010e070b2a010c08010b03060f0f0a0902030a0c111f0f06080d0e0108100f050409170711030709052206020d02041e080105090a080708071a04020108 72
    0x4251040a44c04041e00b04081b8161200070440840008c2c2c220302646600b20510328031860908a14100ea0354030b0540c40c581541c0903070030074054440340049a2460074048009448101c508030032501c03600007595503485950352540e400c2c0045c0580381c42035449140c56846100180106a01000403c2d00c100c0d1003a600310001c00c200c4400e60704e05018060a80c00b5a10b44401840300c90281c52020382e465001068800342044030315040e108503600c4501e404442000100a0034026056003003114032440248641131400303007480255103043d20001410301c407900302001d038403001c10b407000c0003003800148200500c60303450f0480043d241c00f40c08886845030354271541400c481c0201c039200f04072420840c0140070105044039181d80c85000d0240981050301750741801e4201d90207a4044ca81046036003085815110b0344403980401451543e008004518108030515141c2485440082c0741e180d00088100401a01c1c90039503a1054111101c4c43c10a448450b451980c2d01e02030701d00740d0116500ca40000c000b8007003203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232606456 1250 232605206 232605221
    0x1121823060c031302040b1c11010207050a0b070c0506030103150506180601030b0f03030309011a03010e12161b140a030c14060c03031005100504050312090f0d050d1101 74
    0x504002c0e1075962074001c50482c5180714001264401e480d848610300c0c07584d40c55441c40f084d1001e030403119465a818940500e4140e0340072599030540d0408a0100042e68a01000c4011900f09244043d50360800d89072882c0310003d2a0000c6a00420120002c070621030080b43d111502ca581c10b00800581e01d82d0002c1151030090200003102400440340003404c0c0b07502c030740c001044444c0080d06144203001090002800e5070012142e01000340e64031200030502101c8241890080e07281034000300141c00e00d6202c2c803a03c44103001c8180340b030160700080c200420b903000000b00f0200e68010a02030103103c03000520408141c80340c0302d50f506c0c01036210404212880d1160310300045950084008509034503050882249103181c0005580c03241c002c0c0106190300a0a000440c480d800100075521120b0401d02005000341c10658680b040203814001444286c1340001c4140b1401060400c2c00c1e12210301000080c800360304601d14a030003003103108403841041000511781c942181e09841d0000100c0c00d900600d822078042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 232607706 1250 232606456 232606471
    0x50a094d0403260c060a2c07031b09090302010204090f0b0306011401020f19050d110304090f020408010c0c1713030206090307030c06050405130209030307020112182306 74
    0x3c15410b8111800fa40b0700300c1c3d182c1100030031250a0800301c0041c682400c804803504c40300da6032a40d41000b40001c00300c0761840c008440c00061b03690121f1800e000d603624061800010100d015061020130f014690b51038840060080410074000785021389002400b07904584647c2c00020b0600040100900d154041d50038801c07400380003000640c2c642050580c8040000c1e04c11030541c0a0790801c0ea031501810710011680c21b1021507542401009403400919000c17500950408100041e400e0440358000803003142c0444201c3e640c00315030720b50b50550034402881503500c002c00300c0d8640620782c4130881c1c10150003441d00c1c0c058001300045000b05040340802d44103105000c03076403000d03030301d01400103181c808084e003074070340000d002c9a60207a16a078980c10840700130b802c0503002c244007240800c65850b0190307003010140700380c40b815400e018801c0d02182da2801540c40007418400e8402d40c2070007c0507594844000080700320700c10040004c035414081c07044c1884800883d4105e00c900035041c403581c1c0c001403040c003d810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 232608956 1250 232607706 232607723
    0x3909051011070e01030f0303050402150c16170a0620070308070905040b010507031407060c050318160302091807060906020c03030a0207050108040510090803061207050a094d0403 78
    0x151075904234000c1000400c12030b40203101002454074200008068004200c03004000c00310807540030281100400250f000061402d00411440201c0d0004a60341000c00c0c0d100d06e005c2840c1145a1b151400a038552208060043d0f02013481014594403050060041d02603846041d20303252901e00344001c0d550300b0074006011420800c2075100007442518954413845240303131031f40d0030460a079076900c00360340c40c502e517160009a001c000c0c01900940301d030788050903100f901d006004000844650f602c0c100d040d0f101c0a48104000000143c0404003410101100810042038965581e1650300141082c103041c0280b50041c41002400041da08000080b507461a050b0380060003080e1034040115102540100112524050340b401c2442e000c0c518003500700ca19200f040019144c0c80c01c0b400340400080e00980c52140c2d54020f40301041030340c40b0030003040256620313650045880c0c94a110742c600c0c0c42a1076250803201c0c010442c0d030194182c00c08403a502026400361248200300344565251500760060340400b8040301c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 232610206 1250 232608956 232608983
    0x40804061803030503010b1e07030e130501080c04050a0906150602070509040503092416021305041106130503152a09010302091516063909051011070e0103 68
    0x81f01d44000c0c18081f0310710880c2c0c44d0904015140340c9040d401c07030a07046010a030800060569450001c1c480788218240c68801c001030340c5811801d80d6074802c207589450140f541c843c003052000000d0780010b80d116800c401d05000e0709143c1420b9888064040c403500380140502e81c2c0201d85c614103030104900954001c0019410444c101c0200818613444450450354581018500705400b0b2602001c0d02e00b02c0c0508490f0400c80c0a40e00511040309095941e80520b24500020000060746980c0010601e400030384049441c1d600ca01501d039401c000c04c3e044142e16114084043c1c0d5001075100b9140e10800411902a030301606d0500c0004040010b03486c8900011014070091005500c241d01801c00c041006214696004031444562880c1d80325413000d0800c041c08800b1a410320455001d01d10f515403544911040074080c522404a0011075402500c58440600000c0d10a0034402e103200005040e00600e2000d00c1d44030800c010b002102c0551031500b6500503024002107008440715944c1c12213410140444084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 232611456 1250 232610206 232610219
    0xe1c05280804140604150f02060c07030203070b070e0d06050103050c06070b071b1e020406150512060303040b0307020604030905030705090a050405070918060f05062101020c010504080406180303050301 88
    0x103c644450350840d6083c440003400c1095641104500681511b5820b10b01c2c40b074204c000d040400042500310012010030240d00003c2d800822240020b40211420041d42c41d00340013120061404d23407940380c0c84601c3c8070682d0180186503100d54100c0340b240013201c52405851060001c607006017a03010748180d00d802c0c009202640900040300d10900c640b1001da20070445540c80070342c00c403402c01710b070401c41d007400148504600707140c400d6101034081840c1d140c40610102e500109144210245400340c500d1400206201d070700d0810555002d00255442e1603200d150403840290f8a6804075400c0d800510b410200140034100440c88906880e4050002149592380e0064100a01030203041210341c3d01c21050002030000d421b00c0754207014944590481807014460514106031003200d540510103034a000140b100756a034904400480462660020307000c0d00032407078598024010f00c25216015400e1000300710402ca0341c0c0000304150f841d0768680000c3c030119151000130000715400020085941000103000c40c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 232612706 1250 232611456 232611479
    0x270a03030f110102030f06090a06030803070509030f0609030702181e1302100f03061e1509080106030812070503040f06150f1502011407020d0e1c05280804 68
    0x186115410100074152540759080d0032170f40112001e0100743c07280b07030502126180446105400052400080c0203071170854540c1e52203448080c3c0f00c1c80c00c0c440000764031026910140039111000b28030400717440b1180740a050307054a03a0300c50070040f44102e218071900102078840c594010702881001140c100940141c119003040d04201901403000115590019801a591000881d03a104860343e145000e8020350312000c0c1c103803041900140d42600c04030381c04050080d10a268801210010b03042001c40c0b1229050a585510352600700d40101d5082440c04014414400d0042c41952000801090315580d281c4040f509400251002030488003142c0229000c00c3c00c41d008075200340d054588210800359204a5038a40040b40d07440006c4da400540105c920681d0203125505081180303210441141c0352011000b9160162040c0c1141408003d541d60b44068641c61741c5100c0d031070042c00005c140d0061a00b0701680c1ca20300180d110102c118041150080c1200c86020124080d50124001d0308180c00e0809680f003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 232613956 1250 232612706 232612727
    0xc040b03040602030c0d0e1c02070e0f0a1118030c01030c0507110a08010c020105150405160311040504050717070509150717030c041514040303030c0207030215270a0303 74
    0x11700c20414408401c88074030500c05c1c0d0000c0301580d0004c0000c0503005544079800040c50b8800415504044020002d602c0b012100c00e078041ea4002e415881c5540c3c24203504020148510305260b2030101007982202072082c89090709071410200c040744d00065000c0011426150144460700000340180401c00010706e075000052000380c002030807194101d44407000740742162101c1c0c80900061791110180460304a034034603406000c00040e01d0502a51502402a00110b020344c5461000c0645e40d40d030000040d6400c6007a00c0281000034003d10403800d015030002c02140307104015860344045c1070301050942d8002c400700c41c4050805454403400d0750038000303044075030b402959041d1030301e020b00e0800b07101c52551b07203008511a0b0b41c401c1c40180c41d513042002110440324003101400a1000160b03103140101ca15905680403030754946408114038000d00710032414003405e607000a400403040d840b0003041103c0c01c0c01034401040b1050806000f800702e40301c03032120034407081042034001da04408148003081c401c060555 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 232615206 1250 232613956 232613971
    0x120915010e04240e06091e0307030504060f0306030c0308070b100e01120f020a0627080c0d063b01290303070807050a03080106082e030b0405030c01050c040b0304060203 74
    0x249402d240e5501c03038103000d812142101d81f6001185415103e00c1402001c2492903140c1b40214200201940d01074100d12581c0100700c140004a01082662403094100e5001740d0790000014185607624a07210340d040c3c21415007190910440b00c0020f21403045001d4072012100034103203020050b4a003841b40c0a08250210007500c00650345902c20b000b503150240000014034480c0c0d5074612044e1030103800c1e0114908529205d039038010004c0e04200e1114005001410035804031031615080307040c2e2800000800340d03004500411144494010500400b00840c01101c1c000702e202c00340000e50b007a0010313080b10581001c4044034054a90f42500c00c5800300e880c040114009030440740b810095072a03840007030b00440d0046459601c004101c8041651000103e8010003144c200b5000900f09220742c0807041031341c41c00001070b00320510520421580307a011713000011900401d400e40c160070039052554880c0e211010400382c40d800c100116544020240803101164580201542142c03035942d600001b0703520192401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 232616456 1250 232615206 232615211
    0x3140a090801020c06090c030706022a030a06051f0e0a0f061e24080f0603190f06060e0403090b090a180905010506040506060f0906120915010e0424 65
    0x30800481c00d10090240301c6518004050500d4408803162401c500b5039002400f903040020300b080490303000100320b040c3d114003826001da022180740c442c101401c241054540e0510442c00c41e902400040c0d4410b0f405031440000c0001c000ca00d02100f00d510005034440c0300100303241600010b00e81c1c0103030b1303200280da1980d600d00880c4555442d140007032216001482488044440c0354104516a0050103440040403d841c048240710043c01c4080c204100041600c5090103a041c001580c81d9000c1c0199201054820760076017200f501420301008240c5c1500d401c4070340e180792100100e0980044015580700356816940c0c02a054103006c2e80d80c0f0a9080b1400e2039030442020503021035641c4401001804981040303000003182049410f24a09450019210310b004601e000c043c0182c5480d1082105d0b248100040413a6a550384100811080e00c41c1c40701901004c40128144034980002203100498070001d00142542a602c0700b88410580e4400c1e50000c010924449500c25049402c08035020b50041d0032800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 232617706 1250 232616456 232616459
    0x2120601110105012904030f030206100906061b02010c1b0e0114150d0605101d040603150b010903020a090507020f0d020c01030e03090a081e07050603040305091c06090b0a0903140a09 80
    0xc20503540d42300c0e50100d001d40c00c044104019200021704580c000c01100405000700b924050b0058803695a0300300781c1004000e41d0310740c9419640144070002c035096000012441c000c1380c5402510140b8514040d1810b0481c1c004000904110703c405822802031004180080c09208072099644640c40b466000c070120341c60341000903280da2082c00c0b155014001d912903107943e40e00e44400d15040d082403c5640d01c02c515281c403d001061014103010170540a20740d000aa031715080b8016120f801c42d507807000f940004410f102003003d100940002d0b01449440d02107038014503da103900307034548031090b000400503404a1120f0070b5540c440e0304003060408030401500d207080e07048000300354007076450303044036000758494000c600c40350f80d807403600900194002d40588562410b250002d1628800a4800723400c21501243c0090265142031011703440e540668002c1055440038074084000c0c0c0003e844c00d8813003081c150005011034209006c0c410b005036260b61500c44400d903000007400e0a800c02ca190b1410403080140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 232618956 1250 232617706 232617713
    0x2070203150f0601270501030c0e04020712020f120715020927010605130905280b010e0402030f13061506030b0f030a21030f0212060111010501290403 66
    0x26401c0c010312190700465041c0ca042c100241ca51415480c0700c03d445048045801c07500820040c40c00d0031b550b400d18021030790104000044515120b165100d9500c680b0000303c0d0003c101c103403240e955100b549074003076a0031081641d0b0040d40f00e016040a951710340c03c003001302d000010740a515100140124a00050030250880e02088060801008414018014007400b10111000b041c00b00d00410f5589030040c9072880d03001410b42030f00e0b403e12403020116200c00c003289030100c07648050003182d50450300711003c00744010441e102820500842d280490211001c8034000c0c01c1038002c0700d114042c103201541541d210b071174034408001b40c804000e682e0950380340c0e0503094812510300b22800074a45a80c010401580100c00c01403180d80d80b03000700c0c2c0702e54814170740d483c0010401c01c0030703a4100b10440c807012281c550114007540a031000046000500348001519489106004190b84c0121020380c0c4801001580d1018542212003c6c01402c0c4803948110100d04800e240700c0d103404408011008003030405a582d038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 232620206 1250 232618956 232618993
    0x109020a050f0706110d1e0608191419030e06040302011e0210240504140610020c0d0c08010b010212030a0213080d0305010e070c0209010506032d01080c04060f0902070203 75
    0x10221500321f842d2100314400341d80341038040200b09008001048a1450b01e48141d43c0c40d8841129003800030101014101803295005090805000c1c80055851034400100d000ca190354051a049011841030202c4000c9410480107960950b43d06845080800c0d4406161006480d0b15020840461007503040c06588240203000d101d0f00c00350344c0155600b10b071207000003a40303403c0303000d8002c2e900803841c20400c003102c1207000e03a8568010790180c40031140c91814000c101d00300080d0106454000d0081800340080248035840d1400b00c46851001f003002292500049889945042401580380e00c1440450581c1003e0b9004000003060b4103042d00c8020742d1469040e04012031001e04d00c001c070f9526801041a00c50a0604a50020705031511043d0000a9400560007000600030b480c0100307004000030700b803110500003401c00c1c000001c5203d440b05004071400e464120090040d08c00c3c1d030003004a605050f0a040c0141010340c0e0031251164141402c10b01c0740d8000303400c8903009a906200d0b00c030445041d0050310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 232621456 1250 232620206 232620217
    0x210d02160606050a06020109110906060c15040204140609070827061012050706120b130506010f090b030a0506012606040614010210051807060e090109020a050f070611 73
    0x60700045100340c5450200a4103400d030750700280959051102e0503000070032502c1044560f60080b980c04041e41c99645c00710340240200501c41c02c1900c40c61003c04000406142c51030f202d00e00c00c0310705101858520389421800721058030615041006540032a940c076002e6035110380d202640c00050180e030040d03132005017052a030715408007000e5002001803200740e25070000a0405050003803094280c5180301e03074643c0d41d1008240318090410170300d08910341c000b02c06600581d080000040c01056950511000080200300c02d075501d6000c40c03001c1070a84026800b600070034049a0034003400d1070556445008850282400402140c1001690071b01d950b20a0001e407190320514011181a0b40d09107418000d1204640f01c4d500070b10b550028a0607a440140c1e8000745c0c6d400702405091001c6469100d6403d00c8a2010102c4d100d07070030500860070003050950b0722409d014030200c07007182e80b01080d0740d903000303607104903c6100000317800204204103218800401d0b6008086140c45200b0004889610040403441134118 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 232622706 1250 232621456 232621463
    0x40609120e0607064206020105011d041703011d06010f090909021f0f03052202011d030708010207050111030f06010807120f020c0f060f06010e03010b1002030903060702210d0216 78
    0x1407466001c5002490120178010300b075640000c2000d035040c407000d1401c03078170295881c2a11000c030500007010003095209560803183c0c0010382a03100e50312070380310000700d43c040e001c1c66815041c0040011082e45c841d0604405800103070316103c03038003400c014500014103010322041e40c100c5103109000d000c003040c111061000f8802c603aa00c5600c1b280301720008050751005014220659518000904202c904000179448964242003480d04a0500c4100903818076040c03061903418014480c00003203287d0107400409816105400811452072a0380d028880c0340410741d1502c5100c00c00c0e0000800310350140f445260441114141207041c0400307070095205640504186c07401c41e94005c210384000c5042000710401c45184800a0030051030814042d180303280c001400c06041281100c94130f20319860030744c881100103c000d49190b407007121000000c0c0d03480c8e10a1720003901078480c0300005280c407032020070044554140c01d151041c1c2d20b02100034240c03880c0c02c2107598100d80c1d9400c110702d000b2034081003441d202c264032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 232623956 1250 232622706 232622801
    0x1270f080a05041d0103020108072715140c0309010c03021002030112030f021c0e010306050603091e031801080709170c0a09060501050d0c03090506040609120e060706 73
    0x4104c0c142d0841d0001c0c2e001e803064940fa0b880148010307a04440c42c41e9000c0094038101d98240700106054000c1e43c000c0c0091907101303581030f06c0400d1030b92440e212178143c94415221003080800b80c0070107101c203200d40c01c11030b4500e820500641205600c10000001780d41d001e84100d85070f0011800d2010103d81c4203901149800c00d881c04400205a0001500c80d1060344074009050810789420401100d02486d0780000200070700300300c0e02c440b180c0c020341c03126010304809402c482c5c4910700080700541da18103007015159020900e0f504110310300320000c100c80c01c04120124989400303105600668210700060280e20510015000c0031412200005460031000540c4004110702c1102d0810f1010040d101d40001a11030309202d418002a60080211901c14101420000391890030201c210000c103c5103100070840d01411083c00240021500082a114014003044070390118030743c0e040c0c81781041c40004580044081c8400320100d80c0d07590128060440b546101c07a12032206008010f010704500d0134450030640d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 232625206 1250 232623956 232623959
    0x90522140108060103120e0d03030e0f0307080c0f0a081206061903051f0f170703120503070306060806011407061418061b0f0a0302040803040902040501030b0301270f080a0504 77
    0x2554203043d50b0fa1f003400c01140c00d820010850501c030701c40c0050107060715810313517058081080050121016007002505e4503000c0383e00d40183c07554429260034846200b070041c0c00103441c00c089034201000d94007944803403405088070490003a420f00102460340c0281c05208446486080b10b61150704120103690000303042c5880e08900038400c800035503641314109024010700c0100d44481d01c142c03d07a0011040d01107490000c441403864096140c200421101c143c29002ca1202d4011001e1401200d55440500800344c4030081192000b00469009001840070101c48988035005401440c41d54010100803400054440744200c06800a5a41c0e14514403510000c2a10f40000e10165402050103c13025095503010040156180980c4641841401000401103d002e0003581110b00402c084030540361140c0d031701d050301d10007504648105400319043c02c1106030149010710440d4413000301100c1e00384602203140d1003030a0481900030104c0340c03100c00751102c1010440c1c00001c0c08071a51241d440981d510b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 232626456 1250 232625206 232625213
    0x5120a2706140405030405150904020a08010614190c0503160c05040b030c0d1712150406140d080c0106050409080304060b0307030302030702010503060d02090403110d090522140108060103 82
    0x20b85104861020000040c0b040c0000190f0100407202110310884240b10100252154000741d48606045503602c01e00c0009d0700b01305503401461450494500d07483c1c4070001d04014440000350711400c0680c4040d401298442e44000b401020002100f0740100b08a83c140348100810342d81840c0b095009035000140c04000f001940380c2806450031805081c2c0141c07450f0a82000483e80103c56003000400c0310040d003032410ba54191880c140e0314808441c500c450818108200800c0744042500c7d42c03180503500780140442c1c03800041501841c4144080d199200303000d03042d15842c0154100412811103552254000515a903e6004041c84a0f0245c100d4590300e00b003d1070801c04651084840a00a0f000307001c0c20404030380c010047d59030f1282c080c00c0150b600e0b650200040c12074204035200035031003da90011b0005241c2d10141c41c0002025020071500d10011240040c0c0302d441c401d1080c5948060030107103d4111158040c40045140505c2102082c1c8001808a454504009820a07412944902d0040060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 232627706 1250 232626456 232626461
    0x905030c0307030308010510180f05010e0619080403050c010f020301170606010807030209040915020a1d21010b040516080109051003020405040302120307020a0314040605120a2706 79
    0x40c0344080303009084041c0341d030360080c4c002001440f5652043d030050080b00e0146000f1108151f01d509400d802c0e94025864900356070303d540389400349900042940e28180c03031074140041107c0f0b00c5501078001044001241000710750000e40107201f00c003003040c1404000303041d02c6d090040c0c7e40340c1c43c009200562250305103101c80d81c2110070f820070011540d101d9002e00120b41d030404015500308009103070142e42c404440000c40e01030106410000d02d10b8102c0590321589024550141c8010300859076000c035088540300107290303400751003010550b200940f10b5840c50b038400c0d1907240084201114002041090042e00010300710381c1c00301c1e14810414424089104010f44c0b00c008107001d0000c5131000c20860030120350142090303601d808020b0242c0e0ba15004902814001c04c910351014080301c1055a50741740001e002034580010740012004501d0b0000e602040e41441e400f07070b805030f1350640c0d500d41c1010804490510500e401818061070690790308403c4c1940010b6a0308860403c000800004582c012071a08004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 232628956 1250 232627706 232627723
    0xc0307060c03081e010b0d02040b0f0301091505010806060904060e07050702090a06080d0e0d062f0702030c040528150605190e01090b0d0b041d0a061515090503 70
    0x504c0c05407080104c0c812038000340342030542e081c5081c032649500305582100001e20650300818641c00010a41684080c403250041d810794454500610810914203801408000140242ca0100318411b0014519080407c00303004c0441009002081c000d641e41080304d0145019a9508001000007520800b03505228000c1a0001044401040110b01e403008054552249140c00003c1201d01c1c250030b90956220007099406640155081029511481800780c2c158080c4107125445101d50304c005010427410303c140c40000b90060040d0000407880c5040000600005000305584801c042c007410708050060000500c0c0d50401c0340c00215940d102e4a0141d0040460340407104000301000300521219000030758050364000d0341003149004030b52000580d42800c0c81d4102c4143c100e4042a41c90100c1e400d6001a001c051041d101008994461004181e4020680388000071380d500c00c00c45100003030840c0c2d0240042601210f412014982c44100454a19014100c800000b560783c4600340b049141c01d01403c0c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 232630206 1250 232628956 232628971
    0x40312050313150e100e010606031802060903030717070b0a05060f01080a1b0207030b06010512041509020603090a02033f0706021b010b1504050d03020c0307060c0308 73
    0x5040d032610400b410407030a00c250004165141003224500d4484054202419029600081d41d4032100340ca08110000c0160b502c441c901d40d82050307800a800c9000e4407540d000042e1a2034540c03d40c4039160203100c002d601150009415100822030000461000080d809034011031060a550317916840c2040040c0000181c81c0042a0745001e05000c0309958480402d0b2010f0b0080c01c202420740d541865030070040040d942003c10120501c1881501503a0108a5600f80c903c07883ca03108050b2580001107529000703aa00442c800e40714a404500810a002034400b0100d14640d804505038070550b01083e015041500c561090b1390000741c03028214a07051200141c128203450130002e442041c41814040c0300d040310190b0a0404075142c0c8201c0e903001407811108030300c2d00003c0941d82c3e54083c04c4403841c03070078002d40c804005510304208200d040c40c10070f40b8400d40e5041c2d101e0307040c1001e041c00708002213000d000d04202c00f0f502c60125075004c0764409000c2100180010b44401e448050981406094040020040b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 232631456 1250 232630206 232630217
    0x130503030909040f0213061403010608060105010203041211041404050d0c03020c0103020702030a170310060e100f2610050409020913050307051209010924030f0b0603010b040312 78
    0x32441030325656065944a84c2051040c001d041d85800844c81c0c0400340102c510703c075800c102c0c01207201c256000305164160300a034020020542e82d180cbc1c450321410700317008550050304200020807044d8075000e2010300c00740c000d0100303c8800e070307000001800302c802200d818174041d14400304003c2800303000c0c0105600340810f4200a1200c807000d40c1c00030748031604440b015041c0742c1d01040100c199103003001180350035581700407a00328000c80950f0340d0150307030000c81e4440446041410081a6544600340f8508500d401400195242080742c100351401c0004000c40401c000020b680440441e025250144010389118034020007800c0085240ca4110030a4000501441c1042400b4005031280c62440d41d00203a0b4841800c2110800d14200d400d51080c42c0d1702070000e12510200441e0000750400600400320b0903258111420350b5480305000c540c00d15141640b024800051302c0a5260180c0c00004441c11072040c005100242c0708005030840e0020b070060484628042000d00410142c40f5154140707600c5420007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 232632706 1250 232631456 232631467
    0x312020a020d09090e0703020402031008010e0f061f0326180a09020412021005070f03090618060c061d03070303050a110705060a09020609040905015901020f13050303 73
    0x145d96569156100090245a001001460b0300b003450503500040c00c1c0710070092050980c1c0d00f0b1040d980b00a0a103038841580160008940003030001e21049a000168840d03001100e8919290314156180c17040b2021450301d078034043d02904070951402020100f6148440c07400250820091001540c02600122200d6204110078030800a024850b082200d504070340072034080100c0d101c1241e190040345e000522880c4c009048204240d00085143c080e41c01a40e20084038800700b200740c01c0d8a40d8184140004038030320070340c03c1011800350782004503e01e001d000540070428104071f002c0e00c1d5511814040c0d0000355520240f085050f0341e402180f002180041c90b10f07050a4040e00d903151140d50140248aa01d07030307140403500441d240d900a654403441c000f042009080c189003881d5020307007040703e184030004482c46204e510707012034030f5141c40301580c40c0c21480d00000106820354a44205d041161642000f8200051600800034001401c804031180100c1d600d136081c261404401411030b030001403294005226 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 232633956 1250 232632706 232632731
    0x10608091e120406110c03011814120408210a090e28051905151504080307060e0f0f0a060506010c02100207061412060d0312020a020d0909 61
    0xe0300c086402004007114100211801c00c0e0b07150400d019101401d180d40410000750b02ca810942c0080440340c90001da41c141e4005104144c200c8a02e846001d007005102d202c0c20700440c28000019051403902c4e0115007414003005c22005c8103070000d520501d081e50120110041c049801042c83c0659015a0900c2d070405a904401a00305001c0d40501d12070300c001e050001c0e8410343d240054003003900101c144000d06203134418155002e4041100c5a14002c0205851080d03103d07024450a44190181100500394103896001c2201000c1250100c002d400414400414004418030080c0401886400002861960141000d040c070f40d500a179204580c120b000040060940450709448450344400009600c1ea07500e00140d564415442c00650400c2d080a40c00b0035058000800a003920340d03d464058400521740850940c5101c0c100c2c61003028102d03d4040b035550b04141d118561400d220303040c440000b0510040c03a90407600010002801a40010745400c14140c210060b00e01401031410240905441c1d800c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 232635206 1250 232633956 232633963
    0x4050606090403020712200105090906040203060103090212210f030109020a050f0c07050a090902063405010912050304110d02040e241518101511010501060809 70
    0x10500303402008100c000a040510038005280a021010b0039055400482d00300325446103840c40e004006422586150b194542c020001e50320740040040500f2842e41d1410244006900040c202d141815103451010b401681c4490211108044403802441c0a540301c44046002c2e0402c0c0c081007031845801c004a0210740942803c9130306598036200d026a9034860803a0480e400d20034200060f180c04804600b8500c2c800020911104941044409820203a11116403808940f507113080258072180800107030303078840c00d034106207a80602d40d4610388007191812031841070100400042200e5a0355140604410000100c8022541c0d40061030514210300d0150350340b104424807041124440d0f804a0000c801b195500c0c6c01c50410b0980751402c0d249400459003181501a4220303200c42c0c541140c3c1c10020b0b405950206412013800741c01070598124609810040c11000400b0700703058020401c810000c14145c1c01c1c6e1020151080290752214994402078441508403401a048881017104070781c1480800100003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 232636456 1250 232635206 232635211
    0x910200d0504052b050c0a0c06020a05010e0f03070615051801080f150708042a06021009030807050f21090f060103030806010e040608010f0504120c0f060209060d05090105100608040506 81
    0x1805c1682d07407804a2007101d13290441070100101624100c10010403100e501041c40b40d1039511030f0009100c540c1101c158aa00c402c081c61489641d54814030550010803a1070300700c00d921001d0050246c0c40a500e0f070700071411800c241c1d80381c1c6d00c271031010720010440c90b0b03420800c1340644903007000901551501116081c0d54080040c003400d00700300c0001c0101b01449086200a038042a00f0b1003019008440c40003003000a03d042d106000242c014000c910f01c0c030714424041c4400300b9a055072002280c3e540c601040d5550340000040042c1040144054240010410b4404541d20b0821030b404c107240c904501c61070302d0301d0052040c091981e04040c00400000c0c0d041950980c00490909003c258001c4a10225000300055445005698200203017031451012030b0784464020ba02461690028503140d0100b5140341120503002403040d40421240c1e40800d005e07501910744a03030014245440c18100c512a80150f6200b5141442c01d6599101070080c5400d080e003041005000c1810040700e60300d0b040c9c43d00303900c40200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 232637706 1250 232636456 232636543
    0x2190201170402030c100f090506040b03180a0804091514031b0d051005040b060d031b08090d0c0e101a0325180e0910200d050405 57
    0x8020508540d41444170003e50800a03080311010040e504005218100c1400c004012606001001c221410a00f0845007030311440c001e542c3c034640300e04022400440c1c4050565249000c0c3c0d06c0c001e40050103002c0200000c11491402280030154000c061107000d945a102100d007150a4011200320b0f00d01003107409259000e0080401645207060204840c02620500202240900b0a1120325005190701c0540203c0c0164a0121175a90300c07814001000d4020001801140d1800301d0041e440710f26682001440e8400d140c028284210000410000b1020f4402211410800d6a013446141d0050011030750114504542c0080b245c0b4181e082d140c40c1818100303000d100b920010000b5042143e0780800c0e60168007070708060388200c07084403004080c99030f4800500081e1840b40000500100d100c420a401659124060026003c0440c0102c00400140004945000d221500711003180042d00140c48403011880b0041803505d018940507080c80711001021003029020010006000c0b41d03481d041801905 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 232638956 1250 232637706 232637747
    0x903120908041805090f0a02090112020f06031e0a0c0e09100e010f03110103020403120f0210110d060f080307020d06090b15040b03070b0a0c031701090c02190201 71
    0x429080a010501c2180c00c416800a52000491000308060340410305c5120f40c40203455461084081071900c07400b010f54003961000041d0014010000c81d420003030303c0a80300a120b583c003010000d021800d00c0d00308844184000d408514400030150f07200c1001d83d88841007a034104142d00503040003801d200c0c100d811650192051030000390701d00b03829003450b03800b8054045a0200c80e682d1400702c0c1c00d915016000403074600501c00c049006550080c000d4800742d96120070308104260b4080c008940c0c1d01c0c2c03100495021031081d100500c4103014248100c0410410559015540d142d03111015420b0b204a40d1002100c96011103040060080100968400540c1207a0240540d00b403410008041c0c00f104601621006002e002c1c814038095a04201c4480c1000396030902c41144e69804158070782c2500c0c071600c0e10b1200204012540c4034480c1e0340e481c0c0414403070f061104060101c03d0007048040c509801c00c812640d601c04003208455010030800c0e6a200100d2081c90481ca041d50000f0404505403120803d000d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 232640206 1250 232638956 232638971
    0x111071502030702060c010203191e05060d06150f08161202060d0e0d0e0906011409030304170f06180705010e0a080303071709010603020108040f0f020901030503031603090312 77
    0xa100b801240c2d003c5400900843e12806030300b004134001c0d031091721602e240f191880c4d0309041c00001d50141c0c540e4040d8111220b169444030091420207004018580365100c8250b06401000030302c1480703400c3c4601480c0082400f0a07080100300707055044103403c4082c0c549d100f03190f004050b09038800c44038150790071048042c484814920110780c1c44e0081803019401d9600f003d034440d0740000300160000d1051101e981d400d060109010500c2440d82c8203a0b841c500203001c0708030042804c01d28070002c0403c3e08015080b02d141c03995031815100c11508907000f00c1030302d0300484071900540b00d0070402150400b11860380f524070008000d043c02e984280d50b100c1d050602c031804000d8116550741c03a603428014800d18007a2030741c0c2d141c403d0000f0481980e2911074064401c600c40030514240e014490441902d5068403289a1910780351505012203444510481c1c2c03690b0f48400d144010303242e5294182c021486007006603142e0501c09410300c0b1590200440808041c0342c0b40c00c0102203680100c0321609410210000100003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 232641456 1250 232640206 232640249
    0x5040e1e0a0c08010f06060309050a031d0607050a020f030102120411010504170a0c0807050310020304060e07060f09080c0109030f050f120a02010b1c0b1801110301030201020606011107 81
    0xd5500c050a400e03140b000000d41c0c40c2c1c1c10342020240b1a080d403010001551122000c0d0110b403100c0e43d0245c89a03101c02d51620011b40909080c036000790b14140060180d450013000500c00303600c102c00454280e0442d0300d22804606240e41a482002c60840003036080c031900c00e0b0300c840081c0c401000030f456070013400170140c0c4c1d42c2d006000b01c40c041c0812010a0000d260580c0c4242d681d90540d0b01c0450b03101e01c0c01c5000041082001c1609019184000c001d80f410081c040c0810010350009402039a0300c650312150a480c800e1700b0400321f8010101a2140202080100c401401d456010740c4403003511740282400d103810b44c4c1d0040ca000c00f41ea0340041b00910410980c20140e14021951101420324421031f140c021b241640100a8140348403e42d00905c0500a040288200031070860400d03100c400102038007900140050f003009a003c003950751580b41d000100c43d5420b00707489155400b24803404000005100b9940d0500040358844000c0c00c4c030b54820404601c905940b4a428894414141c84620319007450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 232642706 1250 232641456 232641463
    0xa1803240f020301090e0d08010b03060f0a0b0c16090c0f0f030b09070503061011120a180609050a050405040506060105160203060f0114010c080702060901121a040605040e1e 76
    0x3807000c40e41c0c21512903031256500c80c020314844007118014811036801e055402e00c5004518140c8548901c61030440c3c6944060045c035116170f510a0390f020140e100e01003601000c10016040c200c0b010310051016106440c00c0070118111600a140000d0a10030902e441980250480f1915a054500042c144491076070480047c103102c5820b40d0300640b50000d106081c3e520501a50040c0c408440c14124803280d840166412521030403141076541252412641c5021001d000d0a18484541051070603100440c82d07484243d4003613040752300410503840050000d030806c02d074000080e00702078404012504185c0c4a003541ca4038000d10050401030002105840c0b407103210b1008900e03e40c040c0445919040121112451000034051480c048003440e07030002c5198401c034a0000c1064000505501d0038003181c0a114660f0701c41d4400e903041c4080d040713030a003201e0b640380f0030342541100c2d0040448a1451000800043e118107520043c0b0460401021982d45180810904601b4a41401c000c01108030300400303608 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 232643956 1250 232642706 232642721
    0x50703090e0f07030c020304050102061501051309020a09090204050f12030c030a0818011e020f090d03030b01030c030204140d020409140f06011a1b0715050a180324 72
    0x507425201010700074168070365501d01e8010320342ca480500c0701e0b039240c1070300f00da890081d40309039030044c2e10a078089851181c075025a54400300c0d0600d461480c09d07074044010400da1001d03900842c0700c513500180035025070341d101c410100680b2004500b94641031506e00001c08254008000c0ca03c100411118201000000c008581960070130703105498403280b5125010b044a0000c0320301107401d8448043d17021f2801e0040c0b203108802e10021b81c0c0f60b41500c50700001c40009410aa0204e19542c400b08441c00d001d94800355030100b079610070b07900401c9010400300014142c2e08201c07100300605006010a100300780fa401c1ca0303040e0040702687c80d5528080103000141c00390100c100c018040c4d1051032244d40c001c00c40880d0b44c0203440d04400441d01750f641ea60102c06425030704d0680d000d1403a0000d00601088010418070404132410900450300940d440f03904407540200c0030354002020540010b40304000170f41120b0b400c801d8580d054400350005207180c40b103c281c01c0c5001c000c5601011100c0c410380500007240d02064 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 232645206 1250 232643956 232643969
    0x1a09010b04150603230103080f040504181a060a090b010e040203040f050d05091807170c04080c01080105030a0303090503040e01030c06030f15050f15180405011203020d05070309 78
    0x482680b801e58446044860b030701800d0002070510785402032000f50520848002c1c01491102d241c1c517861038860110a0f0004421001e00c98000c2000240e2541d8030300400d6a802003210603d070018003149020925444644c00741d441d0741103d0350030000d01b96a01181a000c50301d0b0300700085079031921100101c0380381c4803410401760b0041c404028030013400a203020030141a0f2150080f2041540010000e4400d401120f032120382c002d80028081c0c0d00c0c07414070319440742c2100c501d09080e605461007040c4003482141c22200000d04290100b010007240d2030801038044418421b0806642c0b0f5410100441d8032410142c2c006414581c40d10705140c10800200202c070005d00e85800304880558480c50321089040303c51144500003400d004500c410718595109410509090703100300480d503490709050220070448060804da000200e90700c140002e41c4020010201034010703000044e440c0c505501040304035601038100003000079011a4401c0082e8000400c2601068207013041c507100c501034501105c65034030310703080318 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 232646456 1250 232645206 232645211
    0x7140a0906080705101b0f06110c1005010519030210050c100209030d0302030609130201140d020903150f0a1109042409020c0c06070f0209091b0306041a09010b04 71
    0xb540c1001203100015180c049440c45c500c00c40f485400c48100c03400385c0e01e07481c0744001014000c0004000062007226140300e140e020803640510041071303c00d500f0580076500d294006103440200d0440621909015260071a07d40716070079591032910a4000301404000e00905007140c4451386540110240c6045520031400c6030a00c1c00746c0b5080c40007940110781d131f40d4042d21803111000681030007070003a2803103804050034540142d5035440081c404541445426030600c80f0b603440e419406241d0b5401400343d07000751080503994002a4003032515114a94911580000100081c0842c2c0c00400c10003a41265001b074011a1460282c00e8a503160722982071015841440e10b10111480e03407000d405c003d6044020404081010b40d1144180282c5c4181403290a19402000c001205850010040d0a40b1401004000400401d80d404580059001d0380c0210060b8040040c2400c0414203007664a20300c0d41c00d070054641414640c1d111003950b544c90303031903010702c08d00c940010b41c41000035400300312600c0c0300070001e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 232647706 1250 232646456 232646459
    0x1050103032102031b0702040e010510050a12021c110901060908100c0f0c080f0c030304050d0201020a020706030902030f070308180604050d03080c1b01021207030c0207140a0906 78
    0x280610080c4105444002040740e02001c8010342c41c8241c0c1d202d00300f1220800c08076450900307184a2640003d80480c0c0c050b68500d041c462800003441154414160700702d4031550141404200030448066901a0515005210f00c8500503220311522080ca40d83c030070110b0f03906581c01c0c50b1512901c00c01005d4181c008249000015513507511106600480b81c00e8000c2c1d850065440302c031401550b0462030402c020821081d5005049d0f44141c0001032024000c54484c0c0c20800c0030203410400b0344c4074840c1c1803002d60000c010701003071007814083d42d4008000b6000031403521401c00c0b8041d40310040ccd4800d940a259880441c107095407010f128000301d111a120644400e00d4803894941d10315004a000703200700d00d43c0c4200c062014200308007101c2c15604010015503005041ea902100c0c08a0b00815000d02510144049121000050a0300c281200d8440001d600c4100c0000084400b510040010f4101810010b40b484071503004a170020549410f09800034090090744081408181d413035101c110a40d01d045030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 232648956 1250 232647706 232647713
    0x518090703120c06050f0f061e030109122606041d030a0c030306060507051e1903020d02061e06130b0d110306010905070912110d030f03141b0f090301050103 69
    0x842c030820f4452181085a6146c2c6c0c40001d8800c00116020740440c0c0f20500070800925001144103020016003500d503403030b9084103012a003914450041100d41c05507901c0d06e028816001004540350807110b841e10405074081e440b0044950401a05282c0502c0ea10310340320f18000c00e5404051128540380c1d00b22680c5000160006200b00100d00302500004e181100214034030f4810811118003c4c1c20000408144035140c0c20311000303031068030362400940b0405020080204414800301c80b542c3c045e40282030001c90b00c04010381421001803000c82c010800d402e41c5100c000131a01c09641111040e51a8042d5034102a04e440003021142d504580c00329000614904200f082e050301c00e1407100a90a680c03050343d903100700000341c0e030040e0703400340108803120310a11940711b00380b4003c4401c90142c0c0c1442402c40d00c0c0c1c400300d10904491042a400540d8140c101180d00350940540c622085020035405581e28007001c0065800d045a130031040200e01c00200f03040200480c805490520030024020001c0b942d5900c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 232650206 1250 232648956 232648967
    0x1d030a020618130b1318170a080601030603080a0e030705150403061802030a0210051603050912120a0c030c0503030f091501050a0b0a2c01020c0307051809070312 71
    0x284107489402520400003002c80707140508185a103000c0c0a410606610b8a4142c0107001b46500e0652221911403641011a1010f81e0340102070740c12580300d5940b002e00b030800a001100043c106414135040510401c0011564811100f80280a10702030501000301d40011703081100603400aa031060740c40c065400d0384e80341e400007002264401c800801519440d032170032540b150034251002c0d5068001c495420050300344501c00391000c802600e801c038500000668180e54018420805800007131012803040d90f10708103501d0701c2000c104580b008000d15801000d1040103486445143d50800a00000300e6003007500640c4080b04940e0302105580d00ea2808030b061828182088550080501c100c10002c440305403c09510340c1604d00141401000c0c41c10b02c001c1c4004c40d07001c0300440040102401c040d80c0441e40062144103031246c0403c0603550780808100081c58000c1052015100c1e8000c00e00800003a47c54425088480f48034840c110800c3d60384505150030b01c180c541c000b40c00c0710328500001e5034456001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 232651456 1250 232650206 232650247
    0xb09011b0c03110f0c1212030a050c0c120a09080604050d0f03020f0f03040606050a0f270504050c010809150105100e0a03050105040b10030503070f0510060f08060a0b011d030a0206 79
    0x50301c1e4403004282c0302c1c6e440d0b0f41d502d00d00440c0441640c801c1010445062581c0c10582d440030340504100c4c03511004c0407100c1d28241c482c00b140c000038180402c3c0300c00010340c030039a01002005803200603c21402c140c2c0311a074a03074990940250501414000f1240c4641c042e8050303800503101d542a140d19505410781c2c054542d0b1040303404607003403480e2003030114031440c01c024500203484045c882c04e90210700782100350002c0080c070355280254140b001c1044040e15014010641b00d03d10407809010184515400500203010107400000d55030820800c00c030108525280150450b10115141d600214003044161a40c44c1003142090f0420000301000c014400150411030041d80b081081d84560b42d100100b1913042e400c42d000c0104950010400080400d030b4107291100c1c0316004d00305503030100340303a0342a5000f140c003141d2084c0c91080d83e5203020844134030b040c400c1c00c0d40a001510b0510540d90450002010085c04095031b10380c3c50b84005007103040c3d4a04120f818103d580c040d100c2a80c1d04c00c418606d00c5c1e0503000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 232652706 1250 232651456 232651459
    0x406110d09060b04110406050705073b0601050a1404030f0b011503060b0403150b33040e0f250507050d0908210705010501030f0b09011b0c03110f0c 65
    0x6018400c0f03228103162040c900c40c02c81002c00c041c14681400f030101c0d01c0d0385c00500c00b03551901c0f407075502287c4805440d0504174090a001e91003902c00d0300b051828005e02c2c84424942000444c95410000284d03002400c54003074007a5031400ca0071081d0001c0c44000c2e1801a60030142c841c2e40f17600d0034102040a003c0d202c60503141030515410704141015000c0f001c7d2822801012a543c04c1840108002003462441e5123072403c9c080008034442201d0741c007042d01190040e50340170908242c206c080c1c2c44144003560355808940c4071841c180c501814078951558194024100d607080000050014911102d046400c42140c074002c0641da44219581d10b000f002ca4200340c1c1c003a503c500030100c540780518000c0c240b00040340c2004015011000300b414900748030003903400c00e80000b401c007000910b002550078461036010758401d4844112103501410a00011000201490701c00d81c542140b603a0f40ca172031f91110800a407480d02e000c400030300325880d0442e03124110283c065a60301c03401408074110a00461860f010303240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 232653956 1250 232652706 232652711
    0x140703170a09260d0218100509010905181602031b0601030209162f07090603170a09050402030703020c0a050c0102240c0a090b0f070b24090406110d0906 67
    0x80f010440e51000d003140e81d41c00048201002104c2c83e034041078004d0244420300b040300b6840e03640d401d40414880081904004001180060350f52280d40e002074000026280c26a0340c0c43c012614016501e00c100000381030080e10500289400030301c18400c0084a00003079040c0141c156444560383c800c1d68600080c00101d220f6a090800550b18900d0707440b0f4907a21459668440a41081000c659002e00301040a0203a03047c1e0004103012080c041004488001c00616038001a0070f491030400c10310701c401c02e40310f040b20b022041149011496000103000300391030040b0360041e0341340c80b5010309400921496900d030503603000e01c03c404014848045584489054203800740e94240440000340d280c03003000843e079501902065404106040400c1001e015014024100488002e40ba2940301d030085d0442c107280c22141c0300008200c010001042c5000c2c2e08031031114004000c2024030841c5840200e02c0c096114000c02060f40001e0a2214540025030016690000190b50303500241210000e0000702000f512140d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 232655206 1250 232653956 232653983
    0x50106050a060305071d010e06070b010e090a150f0906110703080a06061b0204060803120709050303120106030207020d0605090d110d080105210115030b070f140703170a09 75
    0x240a4002c01d0701c10113099a0303111a136030b0341c6c2c0075501c051110040140d04000a003886101c0e95107544004196450150100d0b180c250300d02450340040210044c401410b541014100e000010fa48445121201d44401030106038030301140400c0b40180702c0320b10080e02c0c040c244000910f90585000042500700d0203607850b0329080d9584895a001e540e1140300c3c25000910b000080809007142c0414840000e00c0203101141107541e0303200d95031641d00031180e0b161040d6008024020003541100700361000300001d6000d0b50600f4008040402190b10500c180400c0c0340c0c000910398115520913034029400da5100104101500b051003100c0e96644038120004042000340044069000c8006180f101e407100300d40e10000141e0914007480101da84030004003004410884500900208c280141800300c002008a6108507140d03041c10382e000000500b4481c00d0010031403402c0003042e03112074103908030a03405070071a685a44c41c0c541111128800300c1ca4884040a550902c003055500d604003500f0179000714440110352 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 232656456 1250 232655206 232655219
    0x120a23282105090c0901081c030212040318120b0a090609140706030605030106050d0303020a05070506010b030703050c0a020604080901050f0d0e060105060301120f030e03030d050a110c1b040b0607050106050a 91
    0x1400a00800d1f00550240035605940030b20400711410604888c0340140c104041d41c0115010050b040e81c0031004148108248001c156041c0480c500414010400c0c0d000c858051b11a034142e240058030143d11540c485034100d0030307c0440d4009004069100081010703420030b01305001c1d21401c0b03601a072070000e42000c0c00083c091405020303800549000801d070030b080c100307036540681c0254402c100490a002c400d1100201242c01807110a000782023235000e6683e2482c140000400300c0d440140345900c0c829050010347c2019900003081d69005512500c0d00e5955207190005a8540c0200c0d411aa1000c80024000e986000c642d0006a081c0800c80204c500c01e076210810010140401d001e00c03500c0081e25508400131601e00f00c02c3c1c0c140c6034000d00b855070b4810100d002090035036020901040c00c0b1038881c0d0500c8140d00482c85180840b0800401c07082c01c0c9408101d42c0d644641d045484401c6030005c90380741124560fa03680c00019000d00c010003a56030744406150040c040d244a00c00c241c402c14210720001102c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 232657706 1250 232656456 232656469
    0x1a0906060117060f0a0f0f0e0609010608040312021c020409060902040612050a020403061a01180b07170d240506031e09120a23282105090c 61
    0x100004101542140d9202c0c3c007481031403e042031590b540014042400105d6152014440b000b07000700e070061240303190600c50b60346100600903024074084c04c249001040b06c194007458654226070f01d46001c581c882290605e0601a00138409080000d503005c690321548281d01d0750042040f030304c01f1038060112a996030300c1d100403030049104903070201d0314103000c110215481d680015446035180d0401401d0546940340c880444007a8a81d46160b5040c0c441508295a000001141c0c0c8524a241142c3c0c0e0504081c00d1490601503050010f2a061609842e0a02041c8801c165800904410010051000c0d0180c50201850070b17503a001049034100c20b00400c0c50304040b01101e22800d0b503540501002c21140e1550310b0180310080120115024000c0d2210b41c0e000041d008080c192102c0c0d4680302607403c10241703501c090591420504a10304104010340500c540c03c617a01501c0c14804014050b54503c2c1c607020344000b8214400b4240304000302501031955400c60b07020b82d00810541c070440e43e2440f002c40c1070126 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 232658956 1250 232657706 232657727
    0x18120a05030a0507030318060b01170c0f0a020c1804020a06050c0a15140a0b0f060309190221010f05010b0c070e070201090804150806030a0b01050108040f1a09060601 73
    0x395041040180c80c1e55004a00401c031051091500182c9503004081da802815821003044a019440d005208501c1d03074130101e0303903640c13403c104101c140d107080c5045440c5180c41590300ac180b440b0b4022a078219103500078000016004d5000d0078444a0360454204904a00022141244a29001e40b80400c169100302d0036600503031402c800916810781315031905181c0f00c00c6c7d005403001060312032a1444030043d84042e4940a0500c2020100e00840d00004000080002c030360001d001384414801c05c008850b0001d08220b20082666102500042c140003043c03803242c0350400c2e100f10340c031382c214501800401584580c2c82e85810700700030803407662600c6000b8228400c203440d00c4010f9005000a00102e16030481c007070f4220b105030000140b4400143c1d01d084280e0401e5002440c084030812a41d8451600440440c0e07020724120058581014903503140300c5060810301032141040f4103c0d00003000c1203108001c10005a8100102503012000500722145810b402c807181007160156401180980d40903265819 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 232660206 1250 232658956 232658963
    0x2120a020604020904020d050d02011b03090203120306040207020d031e030e210904111c02030f0411030106050619090618092013063902040b030318120a 67
    0x300b500c403030f020014407441c0030340183e174845031051405000807001c00c15504140b41e16000403800c400040699080b0340c4180c0c0c5000145420041a1401603801003803182c1000d05003404d058030781c3c6030800864020b003d0144002c2d0005400421201070580000210390004110700e0a03400800c00f12100710107550b4601a1102240c1c041d02c0c2d0318020410021403032003090700c1400c249041a443c080000c00381c1d0401207520075482c2c0300080c858104a80140480c00034011450107501c2d60508400e14030407000d00400141200401103030300c2d042c60b5020b420034002004020302c4961540a00c0c071140b40410029806400810349200c000181c10380a072900c5c3c1240c0c018400c00303d024031b1a0003070310000390150300007403105200854042c0303007030480d102c001e0200c0f8995070680020302401c0103030181c64901030140c699510403200505075022002c26030500aa03c2d0040032581c24510248080307009814902c1806605000120b00c124401000c22414034541008480d030211079103a20f40d086807245c0c51044045c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 232661456 1250 232660206 232660213
    0x10209310213050904050c0a0f09050f1314030405030610180c12020c070b040b0c06011202030c0f210d09060e092d04030e091f051c08030c0301050102120a02 69
    0x1c000f28a0121107081d4810300410540b14044c100c41c000458201090300002c084010515061010018501c515544115614104040390801c608039400050910380c00820b00c2040ca8049054071340c090080e9801000050b00b1038100341002c0742c200c040d1440900a04041c4036081d10030041c90200c82c05401d150032044c0d120403c0d00c601c51304414001e58050103410304544614140018441070440c014801004581800c50f2184410300c8040d06210041e404400310311446226903015a070042240b4020500494019054850070000b00c2e03400c000c0303044401c910240c0841052000c01d004960100f1110450741c454060a86035001502c8486a64200540007a102800a5001c100c00440b403980300c02c5811840c2d6000d003131011000194402121b0450008004091902060030403014030398111401030801403074020f240f15848002050f600c507562080344003801000d2604074070002d40c15a035030081003641c0d1703031b150100700c503001540288a064010b20030044140c480c400400b0a031600441c1a80c041c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 232662706 1250 232661456 232661459
    0x70b0601030f021c0c02070611030306010302031801020a0216090606050301301b0614030718120b041b0324140f06030706020d12020c010209310213 65
    0x1180200844102d02c0d007050760800031480001454814030b548072014500115400609041c000d04003001130b80300c101840b6044582e502e030040007006880e0310140a00c0d005899940750301c25403c08804003422019154400070314014034581c007040c0ca81c2d500c051780b80301c4103100d80c0d0703103c0e814120740c1c45225400c0007990610040c0100740c2e40c2044130810610700044460418600004005240740c890f4003240c8a003c0d51030011010b07980030310000001c080d5406c2210140340d115109d03116a01c0000c004400b00001c40d110070340b21034810505000039104070403244000c1007840c03400d6003044c1001d403400d46007a13241801140300c0c400202451004d0b03d501125031041d0790003141044c0c0094908034404000f0381e480d07024010303128480302c100c544140c2c501040b8134041d0800000303050070407a01c2c1e000312045400c5084c007103d0840d00041c0a42d505a110a80140c0c0c3e08904200e090082c06090040c42d0300101c4c045401032011071031103070305901c40e113112410072080c0421060407049100e943c080c0001034260580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 232663956 1250 232662706 232662709
    0xf0305130b0c0705040b0310050c1306030504080f0310030b070f02150105030304030f0314030a1a090606190c02030a05160602010618020901110a061b0201140115020304030b010b180105070b06 84
    0x11806c080c02c0941210034010710190300302c003924405c40d110441c42c440880d1003403c101d102110100200700c2410200407500b031946513103149229584040c00203100000203d81861080b0116000842e00704d0420070140c01c0070880141104281092000140f1507810b07a5944410b0b2000880d0494000500451500f451591802984581d11905030305000c6200c1c510045400d030031005600c02c3c0580c0300c000412001030501c01c0141c82c0c26002d15070048012508100c15510344070700f20b582d405400ca030b4100440c80300c5403003220b0f1051107040094050040180303050400100043e042c4001040e9050300c18005e0b280c0c8801c900700c406511580c00e40a4003100c0100580c03000d40c3c000e0800800615110464004503030b9000e00d42043c0e00401c44036a07658a000d1a260240760800f0006215944001d0152140c24000700ea10880c040c090802e4640140085150b024000c00450b4000c540c007030881d440b01d40c0d4402c0f0403040d503009502030000031304104200f0111588100c040703540b03841e801238108a03180c49810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 232665206 1250 232663956 232663961
    0x16082a100305310204110307080f0a020c0307050a03030b030d0f03270c090b0a0f0506250302010614040c200709240f050d0b0408070f0305130b0c070504 67
    0x40000d1214050503504940c900c030052400041020543e501c60440c0c0001c1c814081103034540304800100c00028000c0c4a0296440310060303400207445202c04c40c40c0e4680700c0c0503100911502400144171300c00000e20404000011421400d500e000c2c0d2030405c0072a21140c14540c0340d1083c0c250403800248203540c000d0015003c0e0340010707801d001c02816103680c0340406914000265589c94248c0d10307900303e1641000484050f005281742500241c8042900500d0b1142c0e203000690035000360307403141001180b40c5151b02100c82d1003420115181001d4450310503141006402400c260140113100b00100c80311100d242401c0c000c00d0180c190355038410005840a40d040004089a0305070640386020f04600000c40c0b402c540296008000c10000d51501c50350007098045034032029501c204e0840508460401c0340740d803421001c44a00781c020500c404169a1450701020900ca51000145080c00000356801415884000b9104241008400002c00e688440c800d81c260700424040300455880b903002840030f4106034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 232666456 1250 232665206 232665211
    0x5030403120e0a08271e220504080d11090906190305030a0302040501080901141303030603020901060309020f0315060f010909020d020c120406051b16082a100305 71
    0x202a101000425640c00405034007003041d04144a080320000d403044165014500b1040c3c4c021120380c0310300580c030484c1d0074000c3c41c501c0c00075200b2100074100f1100b4005014400307d0344001302c2000c201500e045e16240e81c0300d0b009800140c6850346051840d0300a06281000c41c0c80c80c440c02400107585689039810050240030041101d90003e62004001000a0b8100007404501900d92005620f481c10034000400301c460041c800c0303455a06101185110141154050741c00c0310404484040c20941c0c4c0c10141c024064560000790811383c10400062410303032550000310824800c54000e41c440005004142c1c2d2540d00340c0c4810642c08082c400318265285c0001800d01c070340f0040c10000e0f5429901c004490898100039034801c0440c2d000102909a0b000900441215008800d1614201424200c0c018030900034518020400070361401a0b03d070194007005141c091700700d812605521140c88008050b01c50007250341c03507400c18250004000618401000602c03c1c00c0c8050070a03100c62301c0d490400c41c0540b401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 232667706 1250 232666456 232666481
    0x80304110d060203151507032d0e0a060c1a060f03030d0506120d02060606031801050a0b130614060703050c07060c020a140607030e03030405190509070503040312 71
    0x540035102040c1c80c1c210203a00d40c0c500440b00180c681c40c006144d514000410280e040c4169129034082440300c2c000c40541d00d90503050f15203aa111088440300c041101d001202c03414040812000301e040701d41d4010a091b40402e41900d402c40081e40d1118151020381130f03000001d03c00b2043d80302900d00b490707221078031a9116100504154901c1603100209085500000c00c0c216040d464404104080c10651303803904600e803405004080304000614020340768003001e080d0758450780f00040030079842041c3d041000f103840420340c020811400c102c05060014125820050b008202c0e9603111034690b4143c0c403c03e002c0310b42449d940ca0110f00130004211027903112020031814040244450343c80f005e000c00c00d001c040e1005407564000041c0500400c9a00200e5a20002d60111602c2800c4140d031902410381c0c520b035506080083d081c00303414000074290301542c0c00c819003210510000d006500c940c1008c081c2221802d440001d001c4e00c800c103084a446c40221006800700301018016406155954000d06401c00d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 232668956 1250 232667706 232667723
    0x3350c04050a0f0807050d0b130302150114030c0604050f060904060305010c020d030b060403030c1e0615031e030e0904170f0901030539040b0a0903030f1704080304 72
    0x4640c1c00194584206030482407802088000a0101040c200030a0000e080c08682509558100b661020708a080041610220302d2001011070201030082206200c0d02028044c0c502107503840e010414444140c41d14007900c00d108500043c1a9810f1190443c0c007500c07805410031300e078566820b040c481a80d0000a00c190480d130b44040002c0840d40a1213400003801c03199000d0200c41642582c01019508450365413442100200320070030000350404004011345510400c0989004a1040103003c0340d400510040e141908064404081000c018402c5e4296842140c1d021601460850745840341e00754800e0042c003240345c00c02c02e0100d07460724000c0203920500c00c2003507011224041c00c4840086d00040e400302140d04000c02d0300425503030036003c1c440d030258200400c0e40001d489400300c0c20403d440e030002d212120104000c4a16001c0001c401c40f0f0141100e10845a60303080c0310940103004900303512040c0e00043c10001c0c1e84000a02c680b80720091054100d004a0154a0701d40b20a0303c2075001400c00ca51400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 232670206 1250 232668956 232668959
    0x21050606010c02130c0e150a080a050c0304021011070915080105040804260d0c1104090213051003170c010c110d0f0905090a0603050d0f200a02030709060303350c04 72
    0x162007007d800040143e1112244d22551000c50280c002c2da0060501c581c5141020100704051710300d0801d07654400d804036140f01503042d98000665030a5500402d0700b025000b180c03030101e01e405181d009101c552000c0820b60510590b1071601d05e08a81056500601d40b050820040001c812162480f50741c191040c0c6d0550810a112220a454411410424008555040001405e01c10f100001000a5400391014801c918403580010b0203a1402894400b500340d8075000f08407444810300740c01e00a1540304440c1c00c1d48074081c01284006030007540f00849150f082501e010551417045140341080d44582004003500070110100340c8011140d188204104044000002802d40e610010140100d62480002480383d04509019040441d200f0003d070501c40002c00c40c0c1d9440c0d0340b14030400c50382105501c1c80204c00f02d10403401403e1807050796004e54103119108001c14807500c80c0d07122404480c4285c4407170401101240c800800c5000d03041100d81c0410410b20b440c119024165000b5070700c0560140030601d4035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 232671456 1250 232670206 232670209
    0x90c06071119030c0e150f151608091005070201080c090d0c090b030f16050d020d020d0803090607141c060503101d03031017010621050606010c02130c0e 67
    0x40c02c96000380d0b14100f00c041d0400c2480b03110241146c1104040d51030403905802c1001007941c0ca0b540c0000329018201003241c641070020700505480c40307100d00742000d40444440e41004140d582011005620802e1800021107001303000c0d20884111542c1070b101c50180740d0b24070014070420b4000b0035420340c0000349011100b00007019a900c40000d440200f10000340b0312100d006140c03402500c1c001a40701039100420805400380c0707909a400c00c89008a8865809150381d10101e544070300041030007504119044101000c008909020b1441420698112141c0755100130f0b0071140a0a2002011000341b01040305403103c0c01c0c1001c0310020701400c1600851110740d43c901282c44c1050b80c5441c070140700d50307401c090048a00380300c0c2010f40c02c1e50100010360071400c08941c001c002c00d81c24450650004002c1044440c000e80070740180008002e108545480850f4000d810140442c40a004035010300591000039501c0d0b010384640151a42c024182c030705550003a40043c4001c20010700c0c00030030310000c0e5081d11040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 232672706 1250 232671456 232671499
    0x10110f0607030c3b031009121701030c050906010302070507030c090608012a090f03150e2109010c0203062a0403030c030309081215010206090c060711 66
    0x600361950b00010004440c03c001440d00001d0800c00e00e1442d0307000e0364400703c07081c5155a68852151034015042c0c8008020002c0c3c41d1170b290b405000071880c01d1005030828051500645440c040282c1c5680039070151580e02c0b100305031000d00000b040f010b0399500500440c285402d117213034412070606005141c2151070f02d4140c60100c00d544200e402d500000070610007040c8a005503001440303604001c0c0242003481c1c118401100c500303100b0000c5a01c0650103903c0451003515014000c001c840c0321340ca04242c890800d0500c1e482500c0c00e0f0b1a03402e042600800c844400043c00b034504807041c5002c00b030000c2d207003001c0710b030b450340319003655410444400d00803009680d050200a000d05032401011000c071228240e81c6460740c03c405490107518009000401c0480d420011a4030011b50510b000260f030f1800c2c2c500000e00303001d00f61014203125031840c00c001340d1411a050311403011509030203d5000340c3d503200106a0f100824901d06070020010b00004e0002486503104c1d0341c14034001131009260101004034903a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 232673956 1250 232672706 232672711
    0x1050c070e0a020f190f03142a0301080c0415151101150618051f0c06020f0f07060e030f040905060a08010903020706030e0616110c060a0f02070b0910110f06 69
    0x384005d11150076010241c0050340402c01b0001c0e820244038420418a0b40c07901c1c1c040007061300c164407855031500003400205440544811414101007510b950311410a0307540d900c000c247ca14003035407510b00c082d5011003080c15000704603010040a04070341e5190207401c40300c100078030110520541d26113079034900c01494103000b500a400d00341d803154880c000c0e005d94101c07050126480640a003046008089405c1c842840c807802c4a20075003402001a80a40b0340780c00248598a44910300041c0491403003c0c150a103c0146915401110240001d40704040600c0d00d034412010b510700000d0080104110040707468002e164844c600401d40d120965035203807110300350741003000100c005030031402c014868203801d845001d441c1040304004042503e0803050074040800704000400500540d00050211442c00708080c3c1e041070750282a0a8403060040405013031071455201103805405403100105038041c520066550081004041441110b50b1075419202880c56601c200c007180186c20320741e00780483c00c100603030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 232675206 1250 232673956 232673977
    0x108010b130903080708070224041203140115030f0906050f0a0b010c0b060f030a082a070b090d08070f020406090203060a1a07020315070e01050c070e0a020f 69
    0x180050384441001407070385165201e56442880c0540e00004641e2003100144c0c081e20508101c0c4441c0c5039100b080c1c0c90301e03d2510114005540f100c5640411504581c6070320300882c45129180f004200c51103040d02a82d140000e80520042500010040d000940c5124010800d2034240041c01c0268009220143c0341c100009541198039a014001103406400381554801450602080008164400240b80078000d060150400c910000400c94903a2001984200007400a027111010882e0b803810306401e801c09503030800c0d4401e41c3c0d1501c0300500c10034055100c3d5040d81038041e204181c2800f10800c10798020510168210041140440c0001c42c21402083c0c0e080c0242c034a48002c032018410003080d515980c20010042d8010b00c20302c0550745030508944242d400c400d80c50b40e9400111038024000e4011410040d45c944696803442041a00716054140907450301c1d03036103040055600d8010344080c805c403500b080003980024420454111004212504002c8240c000b5141203905400014039420404004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 232676456 1250 232675206 232675211
    0x80c16080310050a060c0506010e040204020c01020a1d032d0c03070303050910090e06040902010e19080c030c01140306030c0a080124180b0315090f0f030f2203060203010801 76
    0x9000900d0704c2440e100c001e09040c5082040361103d5501c1c0e5441e207a041c440c8400401c8a28080380c11569030360151880c0300c0f1801c0007107482d6802030030010a0313140c103203504160f00c548280c1140c00354200480c060300602000c825501d504030050041111711801800c01c8441401342449004160381e040c00440c0007103020f46d9540d920346466000b00191110710000140c01c0c428408000c024403500582c02c1c03039025400300c0c2d0025801c82d050005a80c6500202140c0e07900020010510340c481e0000c103008000d4038544001c5440c04903248003416a2400d40d0200300b404107005450314200300c13284500079a800840a401c0d165544004404104c0e05e410340d030410342059440e4003040c0c440400280c2a8a07603000c0113248603541d20b10344920403403c3e1503034105008200b51106140d00b41c4d518200902e00c445445041c2c101403604d0100c810a44412070407401085070300825900103407000c00001522220890b8007419031821034002d0b90001030b110340310f02c80000c1100850380040425120300c003440c000c0020381d002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 232677706 1250 232676456 232676459
    0xc0c1912090608071803020405010b0715050903030c0705070f0905040b13020a090b01020304053c060a1d040504060204091805030301030215070c0b0904110a080c16080310 75
    0x2011244888000004100d00e01c8002c001c1c882d030049540350030603a60f0500092400316070300400e100008039040a0340040c149030001400d802d08030002c004850054181b2640c018001010341d081d904207684050555009001081c3e14171007410041c01020b00c100d04030344503070799110754008241603298080300a503a503e104200c10712401608a69000301380242d4001700721410350004680e40c407035014802c4240d9803240c00c200c2d66402042154084e100040051001200004042640e2501820030441414142401c40c030300c007000b02152203d4881c02401d143c100000440101c1c1c6088100b45402e01c001d20049140c20a0303140c61041300d000c2c80c014030000d130340d56080c0b0b0074070402c0d2401c0b025040c803003407120314402d03000c1080802a281580d03030450f6011052890000144224018400c0181101c120301c2c50005219207568001d000c0c103641500c007440964201000010140a0420458042209000001c800200100081001704084950180c218240b91640301ca80e820132100c4801c0905803070360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 232678956 1250 232677706 232677713
    0x908030403031a010f14090901080a1103071217040308130816030302101104050303040810060b07051509030c030d1d030712080a0b181008070f030b0c0c19 68
    0xf2081424101c24100c0750360440400000d1104030107440d008200000f013025008108014412a110100c00903d02080e550711130042546641011104441c2001da4150400036800c1c0444e44104640c00c0e05802c80d1414000e898880b030f0340c1c0c2d01001c0c099800a04010100c00103100070044d020843c07190085c94a01e070304012001d803420050b204881000d8000d03110820000742e0000b031515070344034511004a026904440007960901484c0c2081d0782c10f0001103408501d0000005043d0040001194244941959a4031800c0d2600c074882c00038020ba00014403ca0342c030240090700940100e804011646007144d6502c88a013144c200f0700c0003c10b86034039403286540c40c0f4411040b05d18550ba03004065841c1000594420154400b6842c1030320038041000009003001d0000d9000f02160103006c3c0941c030304201c4417901302c128184100d9003180c1c8803415020100d910781d80000c82c00c2c1030b0303040d00002010003410b40d10303501d1062100400c043c034134140401c80d2000308441172080050500c18000c42e005558014034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 232680206 1250 232678956 232678961
    0x20d0b13050c011b0f060e03040e10051c060209010c02060f040311120312040c0b03010e061906020d05071e03020601031a070e0105090607140c011704080d180501090803040303 77
    0xb64207a04000001241c110014051003000e40650780c0100c10a034034411510f00340e4060450000c0e206142d000114000403810b0b510360303446124116000b1409803503601e4604000003070812901e0034880c5281721824100046495008000321801410300c40c0e1400069400180982d0041545154160307001c03404004200540000d0b91091004603500d0384d4441c00e14501e07c1c0c1d68061901407400c18000e2001040510a9075001c400140c00700c0b9003040d5807503071118202d1a00d02000d564490140c940300c071400c00341d00b6002c54104160f03406c55024140c0e14580201c22107258000c4d05007903132100451f000800701103400018401610f8030940103400190300d18100304140e00d980c0d42d00034140840100420070090b03800741903c40d150400742001030f100c0e41c110003c03640c5402101c00042c4040b10f1a80406507036a070024590114880980c0e401d078001c4411016801d07521020354004184402c10b00140002040d190002080c100e1449018a403000761901c0301825070b40d000c1d0b419140001c2c008103100a05a160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 232681456 1250 232680206 232680223
    0x5030c0706140f2b05060f1906050a05040b18030d090b070206030a0b03030d1505060c0c13090c0b0d1a01020307110102010e01090507080d080f13020d0b1305 69
    0x5040c8641c1c807003558000306030b061041003034184541000260965816882e50414151040c64800c2000000120f000c800c000b410151102c3e48a0b042d0fa8107510081d10300411100c055504101c00d81c08603e242040584050700a0b0b4903078030601c00140800324004180320058800884801001c8120070102c0c814107040102e110144004c00c040d1410a2020080f100122103101d82d050780d035540d49550f902e49050040030650000d907414000002c0004010b000c03a0000d035003007100110001840d982d00c80410a90b4440d210411106804c212089101c510f0551410280d03800d441202080c2102d035992400051465a001421076050108220500c0340151141c100c107030350301056580c1110180300020351b4034000e0002c0200300480c800c94801c12039200303407c00500f840031400203000c0b040d5645409911500c4078003ca1100d44208003411075064400c204d002d000d1070051081c00019291010070034290b00c01044e007640c00080c21580c420000354645c2c59a8410342040e94412826295480d14034100500e8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 232682706 1250 232681456 232681469
    0x30b0a05100c060c0305011a070203100e0a120e030a03081b0403050d0e010203071a0a2405131b0c03111605031506090106030923010506090a0c0c020909010b040905030c07 75
    0x20140188181652840301c84200c440c287c0c9030316140c5600d48002493301540f10001900b0f00d00b801c2d200101c410000412003d010300c41d4602e4994505481d10484007900c1c0303004210380c150701030744001d070100340140805500034000d408100721500c40d584140119622980c0101d54661110030b80318210750780450b5100790324000b48040c61900005071900480c0404520980b0b1803880104007103514417041e58420700e01d03c920000107450303a580c0c18215600180607841003a00620108204119100d054442e06000c3d07061030303011a00c20042101c0c11900d205000b0011000c0c810205030445502c2003c00581c01603a080c030800e440c21030300b08421701d0b00707054640d00c10034041c01c503100a004050307568003a0313a130540b98589030001d01102682001c48005200104c861422003a40c555041404010b400c000d225000580e48031941e0349031144080f04440510250300c0008418214000040c07428202454001140c80000f01d2400800c10008040700c118100c01c603429440000c102c1c42c0c800041c0040801001e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 232683956 1250 232682706 232682711
    0x140a0203030f0f06100e040213090213050f090a0b030313030c031703040507150e09010b03040627030f0504091410150903140a05070b0405030118030f030b0a05100c060c03 75
    0x40400118124190005055060040c6e0b260b010b90030342ca699054500c02c008070792107840802d031354000b950003d510940c001000302c4279090001c04d450500701d1040f0038000c0301414010040da50440200c0041000d4411182e050004100c804480324a03202d00c02c01940c09851850b030300518525201b45a800c0050303107003080300d40034410032000c6200031511104944003c522004074803003291382102d61003205a510b9510501c45400454628090303406140b1079407045400b00304841e4584140122100c00101200302440e203011000c1c0040d01c45c3d800d8510034070480c103001d0f0400e621740314800c0503a0130b015820795210842c00108102045040790b01c00c002c04000383c45c03101d04d42d4041c0d001002c0b0308840c04007400d120001e48141c02c2400e000c11150240035040760550300c1c0e5035150803a008140c1e10921503c0c0c803941c2485000c640601240000050407a810307229600c400107030000aa02500c0740340d000b194044020306000a01761038041e8a900c41c401e55568803170140ca039a284c0703541201c9840c44c16900f05032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 232685206 1250 232683956 232683961
    0xf090f051509360c04020705070902070c0504060603020a030b091501050c0a05031603030b0603071b06090203240a140403140d020a1707140910140a0203030f0f 70
    0x116200851000500c1620303007560a03650100b180d0280c034203d00c03a030325859840d01e1000c4022421251600b0141204800352a114040001000240c0c01805809010f940080034100240e80c199401014405c2c8a43c01511313a4039980c0c40000d0444a1a50140002c030b500024490901c9a05204043c50204115900c2008d41480c03944000c0541100310f1181c1403002c0040c2c00b1108070b00c20058034800c41d074040e085179078441c1d98621141c41082000400c0b0007207410070549550070b191480c1030300e104904d950744e0164001d00c060700780304810030001c01c166826070744c0f1201c20f40903032000d004040c00020f0300074004005602c0340e1800b06400e4401404490064a409075032004000d00700320303150300f16400d450709103809003c101c0400c00b54403405a0b04201716200291144049030400d100701c52030344055a014480e40d640003400d0311045065419140b4091041100c500b80780f616500761006c86506262504581e03c03520b0b0114040e0340180210005030b4070100802c500a5030101c0d0842d445980c2c1e0a44801d2130 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 232686456 1250 232685206 232685221
    0x30224040605090f060a1709010c050d0b01050d0c03020301060e03060c1b0313061e020c03070314160f0e10030305030a020315060a12060609120b090703020a0f090f05 73
    0x502490240707400700940094103552590b12980402c1d03510301c000701504e980b1000c1804c041c1403485040c14008000415100090310010180b188600600103a10b41e2490181401c111790001e18007058010705000c000e1002c07850790001031044506030702c1300c0c0d00c006030340354180100a800443c07282d40c201e210f0f512090811040700c0703405060b0b43c00b54131500d22660041d85190300035811402501410f0402080644000601d903038003103003001c540c0c0c2c0389004000c94200306074012078407540031070388954056010810800020340b0400311000034101c10420348030484131b680008511410070360300400751010400c20030721041580b0300940c1c0d0000d81d212440c1c16554510b80d0007811501006002e050066400302c00210700840390794408107910401480d055554000b40005044401d0701c4130041d07d004d26105020400e58000d0401c6010348000b000450640b143c559030301e0341d40c00402080d0382042c2c001d4960010040e103540307002d4006412102544c0e1081d909101661b81207039060000340758054100402d02210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 232687706 1250 232686456 232686529
    0x7080a060506161211060906011d040b1308041502010b04060e0912070f021c03030c08130b09030408030f0406020d1d09180f0a020405090a0b0705160606030c0302 71
    0x80f00d521414022102c0f04804007179900700328040d0103000038080c280c20010400e2020810606881c0740b01031f42100e102141c150742180c0c10080704e00400e900d1601000c2505940d0710074524a4030352084c40c0e0140341a850f1a0001e948480c0c0b0003801002d0707916502144000d141600036040908503c05c0c0c04c103814a4a0315207250faa40c4108044088a200001c000c0d0610800201c45504030b40c020301101c00e01807043e007540429806210307007900000d151030f0b034082c1c2180c42000381d036000d80e412003908000302d202500d0700740c1d88a2020300046642d103c20400080c1d40002030024240521150341c240d40c81c1c80ca4a80064200321401c50ba10b800c10944051007450040c61003054601500300740c4403c90355940380082040306801ca8200900301c2d1084c1d03e241160a000026104c811500c00d03142072280d9101c90415540c0ca8078040030042418030280b000640c03541c03060025260080e14800ca00e00c0c940290b459400c11a07401e6001502c146100c140f0920560401c589036410a080c00c000c41c0f0190314030040801c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 232688956 1250 232687706 232687747
    0xf091e050d0507030507320604030203030c090a030c060e011701080303221506090f1112070207030b130309080c01120b040b15040e0105060a0c030309030507050607080a060506 77
    0x5115002c904402818070900c06d80c4c0d1010750100079240c584620621401e13450495040f0561880501a40d403030441801041d001d004690580085003141c840010720102c41d0820740b074894000c0c40d00320000004c60410407403440144119202c3d0b268030400c3d14001008841000c00702000302e12103d004114105c000411242e11040084600350001940c145420f0b403a0541d407405006204030b0503014020841650003031084408a4034100301c410303402c40114007900c4244002040751b0310140034031460000314000e040d40c0001c05105440c840d503180d40d58120f6820040d5035103911001010454000c0623000b403251806040004000c1041c0035100c00024100180c141902b141107403105051a29500c40390081c0481c204c00074055640c4803c180c00800f042d130824890241e8008030ba40000809003803500444440d04d0143d61001c0c50145207031002c2d00900080e0100714100441003082002081007840a2401404070b552040700608018150900344c5034140c2055128420810007042c6c985030300c0d5070259 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 232690206 1250 232688956 232688983
    0x51006080c0423040e06070306061107030f0204050903040315050403090e040f170904110903060f0402090a020c03090907030f061505040e061c0c080610360f091e05 72
    0x10201040d4041805071171401c803840c44034400d10040c00341a54041d080718054800035540c2c4804a0000d0803410342e03600b100c1c070000d090021300c0c1ca4104050706103604a0359000d034140c021249000d589a0b01c0350b50340204402c10340c0605680d1800d2008056000701105d0050070015001c1c94181070945810740040c428500013011901001c2c90035058031400000d403101702400800401100c0f510414110380f6910048181d0f10034021100011951050014001c0c084e83e0003070300f058800c2d0740d000002d5000358011604080c0780e10051001c1022592440310140c07090311a9a030108204058203a400c05950441d0081c900f465107110700c0800140c1d12a0030340d400c44001c0101c4858544501000c80c0300c0501c2c450100d5030300e00d0005000c10900040040320801c036a4800e048441541d1110400048501c503402024114411104030304250601d040300010304060000b1072035140f000482110703080f1205011a00691501e8000311000d02180e10980f18514200e0442c3d00c1c0d81080c103070b8075281c541078540d0b18076 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 232691456 1250 232690206 232690259
    0xd030b060a050d0b030717030d050f1012031103030408041d06030d05070c0b0309011401080304080709020702041404050607030f14070c0302160306060f080a020f01030b0f04051006080c04 82
    0x91304942c0d0108150002800b06001d2600c00812906031a5103d911146007603d1890414000c03070409001e00c1700c1103101703071309900c0101d184c01d081111181d5001c500e05410f80c01c00442c0c0e03001000007203007440154080c91094000b19600c62602c80880c06894414450301c1e140d90018041102d280c40c0411100100380103464140e544120b2854035050b0002542c110014080b404800c0240e4050158009007040b0701c0803802c4030440e81e03030b401c0581d42d902c114059908a03801c9400300f00720030781c4190090126648002c0010542020030640c00f2040c240482d410395440c2d026800b4070001359010b00c91000c0c001c140502c240400340f4501400702d510b54000d0821000c2220498180341030501c20f124018014040005002e40c80c0da690030210041c100f14000e411141280702c00000b02c841000070b120314031a80c0074040f50300350003981d070056000788592503500e508403150503420307015070b074652103150b00c60b4844001c170703034000d0707090910040628000400190078450100000d01943c9000c005103829144040d414 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 232692706 1250 232691456 232691471
    0x402040b030102161104060f0f05010804030e030334080319061d04030206160215060a090603030306150809070b07030c02040219020f3403140d030b060a050d 69
    0x800d009120302d1480d0600032070004c0c210001c01680a460214421086606000c2c0944920307174114003010b903104034085c3d110b250b031080041d5406400200c7d40039000f4204112078810941c0401d041d54855a4015034140c001c2d40d80d03c0812982e4000031040e0721040003981607000c241e5448000301c1c0300161229843e02d0790450350111031905c58002c5805080320104240080490080652600c64282c40c2100075000d100000b5040a5003401c2c0d031955540f065008041144024200340203901015040b1703904000700e4503000c1100c151902821000b18402d030780000d002458075072001805207109504404021045050180d05100090f4041c19540303415200c698403603192805841d1180039002c02904a400800d402c42c4012030215401c505601ca502a075540700710090041e51100e90800309201e03d41001107a400160305801d0850641c02d5a0030224543c2946a4403400c0f5010300008151200b54007010943e0480d950500514080b000103546150424840503c06085406130b02889400c0581d103144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 232693956 1250 232692706 232692709
    0x41514130807060608070e16050316110109021009090b03070518070507240c08040507121b03050f1e070b2a0c0301151203051605070b0a0f11060402040b 67
    0x102d00170704400e021078501594030050108001001c880d0860308140e01e2803908410fa004070100d1f48a0381000741b03080310000d2800d070196040c00080f0002d03280ea660721042c56005846046008425910070340b0342c00310903880d024913502a610440159402500302c50340400007070712440402d4079900201400c41c141551100c0c011125805011005024080c5000d5015000d4903510300c07084192108000030302084003071040603034079141d02f40c030000c2095001610401c5010100000c440e04248107030003180c413080c4040c1c000b520b032004079007013580c03140c0102e8000c82e0500e404119802c680c04940c0c5640d00c0e1006102c44554480446202c0c041d0324610000f80900ca81072448110140008480340c0700c8500c41c620b414042d5984400e03550700f40a50f18104200c1a6807098000071412128080da91240c1142e140d90121240e800003d584001c1895025502d000a44244120000f4095070fa100706d0310fa0300c503500000e0203d10f00b120f403d020302c980c540284801d100c0c0810840c5e40a41c042c3d80108100300d0742780 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 232695206 1250 232693956 232693961
    0xa0204050711010f020405090f0f0a020a020307020301050c0c0106081507030c0c060f05040314040302060d0b010c020a0909030909020f0d1116050a111009030308071704151413080706 80
    0x2042ca40254a0300f089180504503d5000c0e100f1b4420598010115070f07034440b007018482e03c040c1c0d038809900882c9000a02d4038031031074000b4849134000344180c9090282d203902003825500300345d8076140c0e03203840401d03818071884091190300014185e01e0700170002003512141003034040c40d003c3c00d000c041503200c9500d00781c103600802400507000e621a20802c601d40c0c42c495003500078181500c007200015481036042d5412010341099409407600105000c0c0750125840320304008000c05503025051280300c5032180c015940b8408004010251b881012460144a00e8010105416a00101d505038070606c00059042e20403402e940b00780b8262080098001e004a500315035034000c0625548001003055155010040701203440c886252041e001e80c085081d8400c20080d052495403258000100c0f11042003000c284030714020741e0840124103091071040009078003010725a5003101c01b40d6441e0f62150b0500300402d507610076180c4040320b6203000049401c0021030b0b004030044050000c3c00340c00c80451030500344101036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 232696456 1250 232695206 232695227
    0x1050d0209010320070c050f180406090804080f0d0c030c1407090213060809032107030605040f09120806090c0a12051609080a0308390903011802030a02040507 70
    0x65140301c0c44c407116503450106944200001c41e2882d00143c2c0026450030000000c0020340801080168941c8424103010754007040144196a45521901c807034020501c1100200050700b04080a0104a500d0348822468110300d2007140c1300700030003000d803680800e40c404103c920b5150f000314400c54202c40459402d1800405030007203c40c40b440050011494a16081e082c021204a0380303404e20b5954800780d030940c0b2805038071040441c41c020848035840d00900b80c0402603000000b4100007882e90f031150045070072140c2e41c0b10030002c03c0703558000400034488103144998502e142031814118614041d004100400c40103848001141000300c1d0035a10140140d510703060001c0203100c20452443c11030540c0200740444a140b00208024840200d18884003144100840341c2540b40c904c4591217050060041d8480480e042c1d0484241600e905040403d0700e0354094215608416036494201041c02c040c216046140115501070915128400580300072440e00c0702c1d5901202c0000351551200c90030358000e10803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 232697706 1250 232696456 232696481
    0x318060b03062d072102190c150e07120b04020405010b0c0c060a170a140c0a0e10030b041a01030506030d1403040201020f0d0c05060705041206110906070b0103050f0c01050d02090103 80
    0x71100c41402001065014000858031941500b2210036058008e0701e06a201c110040d0280903451711181c0304644d039420200d8814404030846441ea80e5800094440e840f800320304540440040b0b060105500d0710f8061f40d400740a400c4d44007441c000900304030035031300c034024085280984004580f1a450390b0140800c00740b0f440c40c40c5028141454202c1400000308013401030120340b103441c00003140780002c4803026119048581c2c1c950050620045081140800b007003a18941019140c0000c040543c0751070281280140c240c000741b44000f21408009820b54000915860080d0f2103410882401c642c032403501c1200744000300e4025a41e0310746000403410030b000a1042042d074400d0100b400c102c5544000d81a0880340035405441d400e40751010701312018425441a005102c0480300b0100102c1d60a600c0440d0f10849540a0b40c0380120902c041070f916002010141c038500860001013081c4101440340401525000c405400d51702c9150002030217a00500701001c080e030340c1c0801c290f045a40241c0c41035081c07011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 232698956 1250 232697706 232697747
    0x20403050a0b0112030203030f09030d090812221106040305070b07030f09032003070905070e030c0301060e0103200303190e0f0303190318060b03062d07 67
    0x122800d1403551000c40290455064425100010700b0a20b80d03040c0d00c0c01954142d0295265032680002c1d5120031001a1485540340001c00c445416800e09200c1c00c41d03143e2150365185d0300c4081040c0c0b030040b905c8004040d43c2075921910403290242c2e800c0c001080c203850348010408800c0b0a01c0b000300320303140625000100140314a050102c1c4480c002c101030301b01144607544000310103149038001c40c0c920805200041410351540b101c00310101d00184010041036001c0c04549030b0540c3c4200e140151403054500c5004074000c000703402c00604082c040015140c3c010f0f4000d000071403411051405515051001610303500c0a01da0704541411050707644801400001c08598030b9515000c520b030303c104411480d071000f00c0d540003240006820903074542c8800c1c1c040100550f0038a110a101e500c604141e10001104050b034958081d0058500c610342c0035151805180c000444000d08800e041c0b4013880941a03100702034041001120642012041c0310302800d1a444407442c5844a0f2001c0d550b4402500d6200f20125 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 232700206 1250 232698956 232698959
    0x204090207031106130507090209011e030614010305040b0106080414030d06050a052205100909140f070f180f0c0c05010507030b09060d0c030503030702010f0617031c020d0204 77
    0x40e400951926032641500648184c1e49890311040f0288108510082c80b542000e05c04000155141e40640805041030400c3d0f0b0304095403c14240c5e03020900504074011a07561503041c06200480da5504528030300a0800700301c103003030507115100344d850148140b200700501100000c1c03c11030700b82040ca005154603421203440d80640385130940035151901a060188160040004032441c0c080e010640607040b10301100c00c1c05421248040140100420001d0150f0703001e00300044c034210074422007aa1600038195a600800039081d96420b05e01c00551134481c1e40e000000c207025411040308a60221140a141040300c1912a41500c002d030001140c40c005580c501101c3c8021603410030502d60b2140e1203440200a290380c1c05c1d80c1034044a054103890f40d0010360003000140c59044c03440844182a0240c8542d1501d0380d940d9070b07424950351044030300034010b03515408070a5910ba058010305c0c000c0c10b100300354540c0c0300680d0908503a03640a00c02e0070340500c04029600041c134608540c100d81108444000555845 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 232701456 1250 232700206 232700213
    0x1205060f120106090f0c080f06041803080612070609060509011e120c0801150c0614180609060403052a030a02010603020a0e0c090d1415010509070f0206190204090207 73
    0x204680e04c00d010b4000d0403d14090f109513180d114658000c105038490781c90584030703107413001000c0c040101480d13003260742e031940c0d0300200032030564110b8024402c3e42d425580c0c0c40d1000c00d02849080c11201d6030000d038800d2806105450b0400d070716106846842c0f07003a070707261840e00c80102c401e901d807040446070f2907042038200074800ba401402904140060386050081c030f160440101d44080d82449480c03004038420710006040da10030b030800422640516804600948112034034000355105854800c0092002084080002018401103034042c3c0200003800795480e0a0300e01030494442c00000b9040c413885c4011400b0a0700070000325981c40b441c0481100c2d00c0f00c4941c6006402854280820b0f0711076001603c0000740c244440020500c00c032030140d510b9050100384001d101404121600465400d60000140c0c1a494400c0046401200b060445601c007545042d05010758904064041410052002103079045140c00050641d0131200b40400c00180006411104000380a250000084c00d400060400c060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 232702706 1250 232701456 232701461
    0xe0411040c350109020c07031a041401090f0311031e0904060b092b060c090f050301053105060408040f0605041d0703020904020c010e060105030d1205060f1201 70
    0x2031044408009060444010300d4000312120030403002c070a840303120040c40510180d40290103403006000850f101039880390380700664441c0001100211900700c00400041c000c1442c41c1c541034010101c000c2045078100e44071105105042180031f41485180d100f40c54141004008650110304052204c10407203550161041e080d5010140c075070301c601d04001c0040381c01c2c102c010860388601c000400c12400032000080031901c1d22010082501d907038044005000c0440c0c0d02e4000c0d40280109a0f5980b00c0c440d04103031700000f0502d402c0d0000760081e032500d010440c9116441404804021056030352005d18911401da003031702442204401003c502441041c4402c11a01002030020340314010340390310720640c5810b41214240254401c00070445044011444602d107080c0c2c0701500440c45240151030700850a0108050ba440030642200f039a6649100e52503411003845101d001d0b00b800c8001d031981441e0703910028521a400124000095039a40200b01c0b540d07103185c000c030030307140c00604410404280142090300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 232703956 1250 232702706 232702727
    0x506010e0601110c0f030a1509030f0306080d03050907090c05030402090609060303190311040303020a0c0501052706070516061103270d0c080309011d0a0e0411040c 72
    0xa1803090011811560155100503003007076080d0014904a4585030400010390800b0032040d405016011400d8081250031806140801380c80801090b050075500e0024940b9540c8045402007600c2c0500c181300d2070101143c00c150b41d405614010513503442d074403900c41c00c0940e0381c3c2c401400300d4540800401115009001f6611860013124041030b60782d5904103010802400315092641a002041b03071800700c0107034945203240034000d0703c1d0004005088524001c134a80c0160425805a80051540390412200c1700c0b140e030182c00c0a2034901d0608050100005007003608079115416005442813035003032500c40340169030600d41c01500f22044185001002441800d85024103000500c0111130300341c1ca608000100d07004150440d44414074030110000c01c0c840a500b40485650206011080c500810b00d01d0f807400000d8048000034641d650001c0c8005000104010020920308003188272412595071940c4048048990862b25031002c0c0d9203502e04900d0208085641c26401482c107550b6a4849038040c10b03114 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 232705206 1250 232703956 232703969
    0x160204050a0204050d082115040c021b010507050f0105011d010b0304020303072d03030606020d0206061305060d0b04063315090801140601030b0d1a0411030a050601 72
    0x21803070312504664010b030b10840c05829002040c0c5022000029203034002007606460154240c00509030006040e501c0311000e40d03240c04c4503d0840c2c4020401e1415100c0e40150742454001841c01074000f42d0b000c2d100007c0c02010f6410b004004c21020103001c0207010103034095247d00c00800003580c403941381a0a200000000c0c0c01c207900e0700780012402c01040c4049a0055400400550a000e61591030a1240441c401036441107841003141c400c1d41d015007000451800d12139140800c80a0800400034601440c035000481107500070303401d105041d02c42481c240c21004118801140541d101400300f00e04140c0101c0c02410780009400700000d014090303000546c0e04126082d0b105400c240e00c0005c500380909d10340122003070b0381490001c003d0115060903210000fa00c506000b044966074040c900e00b1580b42251680b400ca070507004001c010369041c800c64910000441d6017403003103091038441084070b03c030340b806d06400e04200300f001c1418080b408000c0c00600f40c0090888400a03640d280a94031240300f80700c0d11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 232706456 1250 232705206 232705211
    0xf0109050c10080408070204020403021f1101060e0f0901020f210705030402130c030e1506040c08010f090b0d0206040801091112030a0e04091a071101150b0c0c0303160204 75
    0x1507552402c4034100c1001c1070703656a015626160b41d100e0400c0c41d48040c81c101d91240d42000008010b0301c2d503102502c60301000035400012842c281401402c2c10390603661405c92a40740034801c1c0700700c002c40e00840d5000f0041c188807501e1076640c1c94035540248a9590085818000424000c02020303000c50001c407016030000d04031525464490b402d44031404269002580007003a0200007001c5552a4001a504541c514000c6140340d100020300e410006520b01501c1d02082d030104000d420709142c01043c40d41100ca03d000312156252400da2030741e0b250540620100710751520a040c1e01a51140807210328190000c1919680d143c2e1800d6480c000c1c0342204048842c0c2056102d80d134414585603407002d200310030310720185192400403101100d640c0310301c881c0f203903009a5451501c00443c1a818000340304000c0d03d0030762880c905111102400011250308012926030500c4400e03114102203035808421507001032250790711810107012550500301004051601448042801c0c5204400200700c000c0f0140291001c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 232707706 1250 232706456 232706473
    0x3060109120606091103041a0f010603020a120f020705010e0a0b07050d060b0f0705010b01180501140d0608150108011a360105130603050606090711060405030a03140402010c0308180f010905 83
    0x10039000d08e01100e6821020130010010005940250010140110f0728600300e00c0c6008100300c2d90044420f600850171000754040b03200340410a00344920403481c00003c0040c41c405007503681e60721040b1001064902000004103d50600c4400c0d900b2003805030100c2c902d00b5485040d000d0302d04080c1c0c0c0058805844640c02d02020342c00c5940580e62800940a0403000350041c142000d0043d9803030710502410b80c030440410018040210380a104103005400b0902c094884010300000304880d80704180c000601d01d074503002c48985119500d484190341c485041e100156000f5602181143e07485100400c003032200c40310103106000c9608804040d040e00c408864420354240c1070700c10b1400315012800003c2ca40e900000c0400e5080c603151100300d610288928107001e0400d00000b0903418a001a1000c507034903400440c00c4a00d264160183d846d0092900c0106950f51402d170300028072804603108040d05016001000c50000f503803009400070301801c00d000f11400c50000740344281c02044014001d0300c10340120f016 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 232708956 1250 232707706 232707743
    0xd050d0e090f0417131a0c010605010f08150a03050d0305010906061b08090307180207030e1f03090302281202151605130305150c0306010912060609110304 68
    0x101d0328040c541185240d0320444a080381c06220b45e200004100c10081440d4000030303c00e4903000c0030785059001117003c548404a4502490035030300240c2000c1c0c18006112508004c141d440b901e4141c2c400b5403108030581c6042083c0200c0d6905d50a0f800241150203201540407559800d078000354100c41e00b0318001c114199070703414112002160041c032503042c54081442840030a09403c05400c5019000b000d5a0300305640c4c02c1e1410f0010200c3d030414013501e4010a0720414142c01c0756a0414161040c1e69001400900030b54820384080700b0415103082c1591680f609082c544200300c3c031010244802e03444a18900383c035010503626a0f103810101ca0710360707421242c080e0441c40401c0c0082e1103071305064400d40703a40700d00740c161070140900c4044604100c0c00f40480c10b428034120061100460084010f00a80012540004da2401c001413040301c121108100344101d99074000c0341c0500b1030342d40ca41c1000100c4c4c0d491501801070816171384800240c41c01c04041600b13034140351300110300036480348e505841c4113940e540c2c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 232710206 1250 232708956 232708981
    0x50912030f0a0809150702060a050a060b04090c0e12071a090303090d050c04060b0a021b130908070f0503120a05070c0210050c06070503090c1f0e0d050d0e09 69
    0x40d070056410006028180c18140601c01c0150000b441c10140c40c0582c03039071250004803660031214000103034482d2040c403404030324501c21103400180ca08020320145007410800e94072446144600240760356940d4500120b144141000d02e01c2d01c42c018084c540780c00102d031459030f960002c3d00039800c03041180010003008450b684110703100520080e01841c241408070701080350002016030107460a0103056960740096840d4450007018001a0040b9a110400158000e02d401c0007014040100c1e0102d0802107403d0341d42110046200e0844034020801618601d0058010f000d611801840a0a801495001c0020100c041c18440160900e00001d40c0e41d400504001e0f1201a900c3d4030200e40181c102c40050f08110400c00c0544e5801c4c02c001d49005204851540b4080040301c044000030404014058880303030901a01449040c2128510940c0310520052840204c0c0d0818880c14001116202c610390740724060701c03c40154000d82900c00039002101c0151161030b0a05280f80324035282c0e40050440203115 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 232711456 1250 232710206 232710217
    0x1703090901080717030913150801150e010e04030206010902031f0e04021009030b0403120908030a1e06030b220b01030f021c0b040b0601031d0a0507060807022e06030305091203 77
    0x2428650010602c041c07107c01130003038041071030400321074100100712400300340920510103140305000c001740c92800e01c84a0a10b801a0810000c0c1c4109100b800b0200f540040e54906451241200503501d444045450380004144c40c206841c4e10b0a0308400030703003505904c5034540f046000b80c1e408d09954110031004c0700c00e070300107000080c002c002d081c0c08070700420312640b55071040010400b80000e1198180e2506142500110340340c04074151202c2c40720401404400c0b0a540c6055014410300050381140d480104007680280441098010466201048801040c1c1d01c50590740050b9041420358481c18035918560780303908140c0c01620800e100420901c88485201c141d660408201c224640307480c0d03291404040c01510483c1016145c0b4a0000a502c036003085809400c140001003800b001903203172a6007441440d07400318080c0704500702000441b070f401080c007100d05072510982070120302c05001003003441440b0b00c0c1c081c5055480c0074008810141c100c0020103840b00200e40d40048040c00d040d219a076032288 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 232712706 1250 232711456 232711459
    0x509010207030308100e0c0309010f0b0609013e16060507060c090e10090e0a050703020d080d0f020306040b030a150b030309030109030305061002060601080117030909010807170309 79
    0x7000100301083c45109002d401007103514151000d07555503091605a81801e60301d04540d080d00005010031805e00744a140c00d402050007040c03202140c2d2000245441c003482c21070741e041c8140b180c88134900d15040744e00490140e205102e5501e12800f11440c010508095040b003160303d201c0d4000c802034450804442c00c00b2500701d913941034940b80041d40c8a00103403520750145002e0015002e00071540c1d01484016510580c00c0c0c0000551952520300e00a050b140c1980d560031594010201035000f1a4011408000f40e0350141d9080284403001d103410f10040c4a0b5800b18286c903860004000800c00c1e66800960003060129402d01508500604040e10794079a40d0009144082e00c0d81c100e4000042c5801210b11243d000702900c3c10000104040390a40c0c5400204400080d03442c420010340c0e207482c00e0343e45280306040c801408189000b00c0040c0a80c101030081401288141b28958404201003003203544801e8084c00590300c80d6940c16145950740000d001d80544014170415050703410070004280d41e4054030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 232713956 1250 232712706 232712713
    0xc03060903040e2203200a060b13050906010302012003120403080612060604051003080c060103020414070e0d0602070204090309030b010801020a21060308040f18050702030307030e0f0d020a0c0605090102 89
    0x402c1c0c2d40079649080d15640c180c651b6400c160091081405c14854641524082d840218400c00351705c040000300b031100340403000302038941000e10000394800103a0605503682820081c0040c2c8241a500480034000640343c13130741340720004103034180b120300c0041c090043d4400e441d034000d20384481e400c0010024240440c0403190b444040003c0492400741c22582d084421906c043c009940c40751503440c025403003c03c11011980c009001001141018401e4080340e00300111145840d040840004149402106071303984520524044803041c084180d041b94174175540104100642c100a02d030141c40310350184025a05031002c0c600001d08428180201e8019003019640c20070380c1c4136001c5140714905504e03803d0740c040b01d60716140400010b00e901e008001030103040440d6010545081c4242c03080d452403c1980076140e0a08040c001c6440c1c0020550750019218180840c9481801c0d0042c0d00e410b8042440840501c6150700303d110f0345402081520700c103402100d0350001140c03111810b9500307120302c050003401a030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 232715206 1250 232713956 232714021
    0x509100305250503010e0112030c0b07092105010b041a011404030b01060816050f160f060f020a0905100504032613080c030706051602030c03060903040e 67
    0x10311070303405560300480701000034141544191000c840050b0501e02107000c03074000001880769032081511140185030f400b00d400b081404540c3c00401d42c1c0c0c2d014200620100f01703440460724141c020300216024000191400c4041c03200c442d092880f2031030200c401d482d2946050050840e0382820300940a41c4502a000c40e00c0c2d05203603e004440c10001801c120342200418072000c0002500e00c01201d000340300c0b079510468581040301180e00d1007804c44000d4410300c1410071030034240c01c1c21b0606440036000007442100d1600c440e800c0000b0f041d099800c00502113880e1450610003074681d54090440e60030240c1d6503403200c0340c03a0821701c081c040300b14081002040050000b080020a0303000038a44011021880c3d032701c4140e603203007106d90680180b0f1982c1000c405010381400025820440f20303040030005c800908440d8a4110042d1943c0704107a9445031040b011100f46e01503403401c000d442e004031000b604071b58441c64801c1203240c030b80d0040d000302c00329103807131402146001011400f003a006a611403043c640c0740 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 232716456 1250 232715206 232715239
    0x405010503120c0109021c1707120e120a08031f05030c0d03050417150906060a030318030803010e06150703080708060109050603070306080c030f030708070302010b120d0801060509 79
    0x1d0300700f210085021343d00c822070900103840d15124081303140d000078600c564440c068070b0140f05600040581030b201400511071400483c50540c0041c1664410b401c2280c484406030011840300300751a10010304d54401ca500c1c50b03041024100041d4032444031100940c8041c10030602e5401c0c0f810440c0709042d4181d101443c10036070351074a10030300c0c90581e00c1390800520f003568440d107503610081c030346862401641002e0583d40701c83c0700c48081070390b2161072440500454a030490014081c2c070454000581009200040007280d01e0100c0c9402c0040c5800c00d503c00e8480d07940b0010051120303400c84115001e1400301744035081500ea0581a41d100755070588615455070340d0614200c800110050099041051681000400f62981c0c0001c50003251260703408035409003009240c40c5022608203099010b6409103034040000c520200603120503d502c03112041d5100c00380c1c20308030b024008081c0c281e5070080702441c03d41c1c0346110001b154060118207480700e04980e0f0342c0f0202501c10f402299506900116511000c4061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 232717706 1250 232716456 232716493
    0x1110f030606091003050108010b010305131407170c030d03110f03150a0b1201140a05090c0f030702100c0c0b060d140d0f0206090d0c080f07060f09060b0405010503 72
    0x489000b0b408a410040b04100150f900394400500c0e1000c60b03500c01c01440340b0142809030044001c1d083c00d050020341000900d02d00c1d03962403000090028501c0c4003004046810500c10b0344010710a4200d00004a03184c20610303a00c4950702c2115920901c07500c10b8102000e4080d005030140e140030364401c03a0900d041c404d44001c65030700081c0704000034100c024500015581e44e40da4080501145804103442d0b54200848c80300c000d0041e04a0251802103035405420381c2d0b142080d0601703484043d01d0480554451b000741c1002401a40d00075403101c1c10110410051036400201d9904010382c2100c1841060340b041ea0503031740e1210003100581455040d0300015030074100032200c1b03180e15102c1c801003034951003c183c9907401c0c6698814100b000480074a08042d00c29810066680c21800620203080c1d0584100f0014100c1422440c00400150000c180b01000c003048100307817000750340c00c1001031083c650904c0c4d122001303121850301200c215103003605a1110f814070b81b04103410385601074002d283e04510017503003010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 232718956 1250 232717706 232717711
    0x309010f050c070f051e10030f0902120a030215100504090206070c0b03010f0b03360f03040603050916090e100905010504030e03030a0509091e040309060207060201110f03 75
    0xc0c00402c00c1620b030900c1040260400404210094112080c20902005461585100240c85d0984000c1603102c00e40d4400c201081010342500740040e03400c540c11450005006a10340195001e5040702c4403e40d10310021a210321031a1103a03003910302002803405000c5494400b41c82c280074240c0602800e114030305042e8040204240000d04190030a091650b07600440f81481e0000520317558040010050000b4101480b4007508440460303900b14030742121010141500c0a42005040c01d1104404800607103200030a01280340030030581d0038440d0000d02a582d030798440c0c410800000c1c903040000d000c801c804914445800700b445036102c141403414110401034046400d904160f40640d84d02154400c440d0711456000c0c622940c00400d05151905000e40f000c01c5036822a4040d41040000e4100598844200d802c0c0c03450440c0c05c0384881e1102e5500c0c0c04400c0d407000d40c1c604c1c414168001d0009040e0801d00d154111203995080b2111280c40360003c90a0350554110140e10280134810030102200c503001039030303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 232720206 1250 232718956 232718987
    0x5010e0901032a08010213030c060203120402040b0a0b0a02030316110c13060503190c0b070c03140c12030c0708030910230703090e0106140a0305040303090c0f1d0702030901 76
    0xb083c4580b03c508050880c1d01801030300c6250f151101d41081040a01c03446030000b000c503800a941054500c00300040800c10092000340705a40e41c444489440c0e5486d00c0e5070780903091035035549403500104000617540754000d03140307503000c843e5002c40c024140b0320030090313804c4050600d005811005110418088000d000070b08038404161030344404949500e04029203010a052068880000c1c2c174039003424601c211040d003050f001c17004d080040501181e51031030040c040f03a51004c05045480080000725003020700340000164840402020391404a038000701230f003035181c00d1006603850350b40c0e2410101c0e03980c4248408a40c109000f0040c540034030303000702d404081c003000700d074404000d155100c24014003903444000200c000c200320040510010414407913950141805007031010a61503c0d500e03d0b0054040c07542a10105511040081e04052107900449282544900b200d910b080c0c03100740300d68090041e4000d00c58461480740540c1420100255603902584464000d10300d42150400110b85812070343ca001c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 232721456 1250 232720206 232720283
    0x1050a120e0322080d050a0201090b010b0304020f0a051005090102010914280201051b0a0c0e180c0f091b0c010b0f010201020901020c01030c0306091505010e090103 72
    0xc8441001902a0100c00e1030a80041c40e43d0f41e00140c6145031001150f0042c03400b00b2010501800030000008052210000f5802d00a07160740401c18100d015040308900100b42c0101c05000044244100c809140524800c5889040c42e4902d1424090038925911600d036010880c527201441d094041e00040c0b0a410040c8004940141c850300c1d0003100f410f1700300b800702c4250710a440d054040780d003020004108040f424800c3c51007444580000b440c60042c0c4a0300705441d2004105000e0340d120410000015030b90080720240042ea892401d02100780f004c58078420f080550040d041c9051340041342c07400c09104010400300007169a80103201140c54010301621074a854042d10b4040e80e040c00c8040d020451094001061441c241824004442517290f04903056a00600c20000315a030080b820a104140038a00018124400c1c94104c5c090304503984079509a45c80d000f0000c1001c0e0001d04018266a820703211340d8030b401450700501210075024071010b0282d40a80c01c030142461700071401c0103408103249004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 232722706 1250 232721456 232721477
    0x506090306010506130306110c0105070906090911160606080f03041208030603030c0a051006141809030f04060216120b040f0f020909010b010e0102061009090807060c021e190201050a 80
    0x1501c04840900c02348605100c0701013400703401c0003002d00806600c420700780b514080352132400101401100070350184180050311071070711004e201d0101c0103407081c081480514102c04451030030001c0080a8030b001e102c46030b008001e05144203081c004221411500044002030003401c50b41c072050040c0e00081c11055250104012407403100c078040000305400c1e8002e4002c2e004941c0c074207840400301c03070f410b5000302148500d492030401c2d183d844c5e603c4060100301c0300c2201c0c4001e5607070000b8a0304510400108201101002c50041500c0d940060400782e00b001c1040181e1400da10f80c4a400b4a881e01c120000704080ca011000900107910301000390305644c0b050401c204800004da001880005c01218031060503035441c5d9aa0211b581e0068204003010b9080c0003828960516400d40c1d48807103510b006481c855902c482c40764040000388000c90f5070094010408004840011034020340702c145030310181c050150300f9140318005880210302c20b1035100c2ea101500e12090065030041d82e550300000140014052140030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 232723956 1250 232722706 232722713
    0x40906020d091a0105010801051c1a1f120c0b0a050915030a050f090601120507080d0f0809010209030d08151011010e01022703030c19060605060903060105061303 71
    0x7005540b6210380e0900066402d1448030b503100c3c607016403100b8100f040890040000740c49a03504603001526000001d00c0c088034a0804825150008407101d1072035a01d0810405408282101c1c3d82e80e034046410f40d50341d0103650303e4041c84e00c20052003020f041c03803030240c0f800c00c441d41d000001441404130030b09120341006040360000b080c054040803040401c03c030000030401a591144600c941c044007095104880d410724000c076a956400500070a091683c11401d094148941000503a0003400003c003201e401c0102600d0040c00e0400701280140403031a4135000c501414010700940e808014042c00801c0469030100341120200c101a1698070484055a1005c649480b000b40160310240c440c0c9a40b003552003103004141c04c44441d05c100c00700c541d1040c844515003450781d024140802c201600288802044940040d003580324500d0380c8401c0d131050780c140d60031400c1300c4518240bc081c010302040010b40d0740c56061007100d00c030758001d169150300030400500207483e243d40602508101c0c2801051030680380c0d607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 232725206 1250 232723956 232723961
    0x203070e040b04090c090c030e060411010e01020703150f0603021c170f0708030a0e0f0c1305010605031303030608030d0b0406120206041401050d090b04060f0b010905040906020d 78
    0x49055001a60541055503941098000c1000001041e603007040000400e444120b050710760f44c0152203815480d01c403243c039518403a4000c0b041000d07140c419151305007000d1900d101c1c907203c4000e034640884c4035960091142d41c00440c2000407650009000e00810070001002002800108144403640f41c0d0783c4800b1001d61100c0c04011b980d140094080440140c9d41d0620341d0301282c0d201d0400203064800c100d400e10301c0c207012094071019548540c025807252107100034040509541c40a240c07442c412400c104090b4000013980021105d03041c0ea4414000c03038950305e0001503c40c240500c00100d00d040020401a04812610110300d900a01d13000071400d8503840450b09640c07289414641d43d0741c840a11014078a070600c075441c0140161840c4030004103080e070201e251406144a42c1c0220b000381e0070540f45a901134030480f29055032411041040225524001421850036a000e0740d03054508124491616568400e42c010301c0416102d01c2c41c903a1910040001070001d0040413038950780c00744450748291310380c0e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 232726456 1250 232725206 232725211
    0x1104060b0706050912130b0d0902040504080a0801140d0b070e06190813020a0e0705190c05060f040209060d05070f06030e16060f08040816050309030d111504150203 72
    0x282c801051605004803000d20302102101040c40554080003080d40320030103660f51504888201c0c9500b40c85214080300c0c607004204000f80a90481e0030403003000200120807004000940407500d0388546641c07100d691100c690510440c2c2074101d51165401c4021a600400140c0d0080803450480503c280080101d000e580081d980f0310114240c40a1942c02c07160031015041d4030440d08040e8134000d403081c1c0c0014801590612482d0001c0302d480740441c141c144900200ca0591007210343c55440235103100070080031281544016212070094002117500c19402c0b20398680038640040c680005a26180c003000500f88002d00c04607110b1040040000c1c100061440301001449903440001d5106a10600e01c0d0511800344c603c402d1144d481c10b0180880740c0c100450200b01e1a4070701d000c001942d40c515014036a813007002050f090450604202004100000008207003070034055080d5901c0d21072001c001c2d03d1240d0505503960103500400b40441b030300e502c94082c00e58002d01541c0800c002e000307018280c01c1283e005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 232727706 1250 232726456 232726463
    0x1020a300f05070e0609150f04030c0303050406030605041a1323040308010510020601090f110c06040311120304151d03090301050c04050f010c0804051003091506121104060b07 77
    0x81d0300402c032a0b1074000030080720780001035174400e1500e511140011010881d41e00882e4103401d01090381345442c850b9200b550065644906a660150303141c1c10054801d803c07070301c1054000fa0070218040380701c0c1458080d0004001030140111190901c0004210101140740180c5c49966a03506c0c45481c0351510178803001c082c0054560805490038241001061350105802c250700800035034010002c02940020312034111008480005142e41c00c00ca080c002400701d2091030b404120001c030345081c000c0340c003282c0c4a0007544241c4030083c540c00e04000003515007a0341c61070940305840034030009000c1880c1041810300c40d280380350000b40500d216000086134200e0b48601520541c00070550900905091040c02c1d00010344042e0503060a24000000d44146142010702d03040080b58140f40c1f0420890388141c401900d0020a00a1130800311000107004248824080d6a5444403080303400740c041c41480b07450281c5aa11210900c0d5107080d448840040040b01d806503081940e60400180d0b00c060b0030060702142e0311 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 232728956 1250 232727706 232727711
    0x806030c13091707020a090b06070f03030f060807060504030201050d020f0c07080c01030b330f07050709050412050c150403120e01050108070512100204060e010f0201020a300f 77
    0x4500b440322000540d43c0c80300800e607204100b44805030307a8004590301100c182c20300c0442c082c0344050100b034580c0202c1000601105e07031242880101601a0003c0e504094a07007004c21009036140c01843d9104054400e07007020503406c110600c00355104400400f80070008210240c41c07d0700d12002082d26038000415041d407a0131414052042074010701040e00d035280f00b440c0a2000d030072a00000351540c07072031862820231541c00620765091f190101c1208106241c142401d44d403503400005540030181d0080c2000c80361070046182c0800d00c0d030032a1082074059034201e07001d0790803441154416559903024002c8510581f00347c800f00000c40300d00605551042d8400e640340c040740300c5120b030b000341980c186c00e0b80e000b80350341403000503c9681d40020324031084071022543d40661001100b035043c2030401d084510074585000040100b006030300140920b242d00b600780d0303078084014400d42c005c03401c07402000010000548500118441180200d00300c4080607180d0698450001c5c40a035079200b21441c0e200c02000c0181c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 232730206 1250 232728956 232728971
    0x21306030201020d030b09070e03010e070602060105010e090f010e040503040e0115080a090f08030c1e130602060708130611030f0a0e010204030b04150b0604030308040b0106050703050702010806030c13 88
    0x59050004407181a0380c3c1c101444840344040024207040b5000b13088e032042100131340400700b141d0340941003551020440800c1e60001901e03090004c0d00c4003424000e060100b01d00800445080c180b0750780700c0b4403484000f03075140150703400e120a0300070910010344203403583d110a003c040341e12010350810303138000c06180e41148046c014813400070f002c80360020802d01c4000c1c90065818003180628451500069000e8010740d52603940e4440200b0502803440040313102095804810a0100710303030010700d407018a011305d02d01e496668541c12a40e5407800c44485000424130f10200300c4a04103030b000040d04d1481010080f448d051340c4d9000180c180c20440d1010020030141c001e101c0104034a00c550311220406000a501d401e003952107d80c003111010f80000c080c11802088401c800304030754003880d04140300511a07643d071135032420000d10b101c50a40b000c4d40c26000315000000c07414068802c865245505031500390403c60241c0064a881c080207040700d17018082e00311045500d64580d01c080541c80a055070005011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 232731456 1250 232730206 232730209
    0x512091509100f0c08041b09020c0606360a14280b03030702060705030702090112060501050d0c090c0e03070605120604050606120702010603020d03081e060a06030f090213060302 78
    0x1260308400c0f240c1042e1624445a4800303030711060065100d038018640c02842d200444002c4500e54581e40848640c40c4040355546102d1008104a030107018100d85174080c08044c030008440750030226155138034140a070540c0c051460003640034103a110340f4010001403800c00c0d130b229a0110f507030215030306003586010650228120012142d6200001c640b9181000a0b46142c808607582c0d00c00c500000e84200c20100f00c80c030070030104004950341c0e07660240c10001c681d65980908901040c01c40412940c80e414000081200e0800801d03c0e4001600300412402c02450102c8500051411003c890100700040314405407989040208500900039950750342d507984046400301459103070141903640b1030390501050003c650b84100503110803207241062480c1a0302c4003203003a0b00402d11907000a4007e10501026400d00d90001e00c454032401ea01200d52010302910580c420b03e17800e04491803035005404803818025948a0f9125081c8007000d54130002d03442a2580001d420440a020042d85ca01d450b014144111b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 232732706 1250 232731456 232731461
    0xb041e0f140601060207141201060f0512010c050f0c19050303060102010f020f092803030512010501080702060a02030a150b0d0630020103090b040c050306010b0703051209150910 78
    0x441006102030042c550421000075210706036441045000007001082404958a20490015107450705008014003580c40000c5240341c025403081c11300c10b0f0303886400d5411000060159800d0110b41d641e80519103d00007221f840141c0103100e030350003580309603840901100d1106c6501080785004078010358480c0303050800242034560358514004c1c014010301a850f621240d81003919284801104c00052212005026488070401075401c5085024050000428141c00c040181100d520003d000a65a0b8a0384010f4449003800c0e240000103901003070000340031100e1940916044414440d02183c403071006050f45104001c6034110541c032400c00250058000114803616004000008017a041c001c07100c1820038080c07250100b146140002110381000310f86c42980841800b50740521200c1322070a15041c200740f948414011240280304480021800400100a0360303482d070340c1039413001d10308078950040d4400041c000c2c10720030651003103442c041003084101555038820000c03c3c008012004045113110217 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 232733812 1106 232732706 232732733
    0x3050c0d0501110a05040510031815110409140106170c1e072402030c04030212030904020a0c2a030305090d02040e0c0112180b041e0f 59
    0x40349608080603100341c9901f070350311079031318407480b8416801c0307030b0186902c0d807200000b1443c600300007100d192410040c8500d01d40cbc0420100b9a8900d107552580054104059083c0c4904929184000010700d0300c2c010445442c1030380006002c5210407642500151144042a0b00001e0381c001003800b603006914040c00c151085a92210030b81001141e061905d107516540550b03484030843c0c2807519000303a9025050000c0135516080c5150b00b002241c0022080503895404144240c004950f2244050103279216513403505400f030300341c51612102e14048400d01401403061451101c03910942c054107001a81e516042035a034800c070324000260709801c0110000d5205041210b007090781080070030a00249203007030302c03860103210850b14808251082d00c071000a05490403200000850305c05082207411074041c13256000c0343c44c0e542c001002c400d01e10320401c0c0c1d0101036071240e0b86d0030070855044200 = true := by decide +kernel

theorem cover : BRFrame.Cov 232553956 232733812 := by
  have h0 := BRFrame.cov_init 232553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 232553956 ≤ n) (h2 : n < 232733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
