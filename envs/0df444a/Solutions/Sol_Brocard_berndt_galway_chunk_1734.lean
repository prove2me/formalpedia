-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1734
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:28:34.89063+00:00
-- url     : https://prove2.me/submissions/76c5e4d8-3fb7-4d9f-bc85-3307f7c5368a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 311690647 ≤ n < 311870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 311691897 1250 311690647 311690657
    0x50708130e010605030408160201140c07081b03101104051f1101020a0507200901080708060601020d09031b0b03072003040501092d060807030b010f091205030c0d 71
    0x50100d101c1c00c410240c054000ca00c0c00714114501591140355070321074a00500c02c0c0d5443e00f180c0078116889902080c2001c1d40803120561284005091a6901e000f240030700d003010700800640c11600c1c1000f0340c060000d0380d0018020010300c1e100458240c0242003000f80b1226280d002c100104940d01c400c0811881e9081c601d40341240160f507040010700346103441040b035107207900400c00c001540382e02800f80c034041500280402c40b0072100c9070983c031a4010510415820500c008000070740201d0104042c03007141c8020040d59030965412004a803104036002e0030601180802c5000c4c804903003110041c104140340c440b48200d480f6101c1d501c1d002e0a0b0005c482d00c000040c1c00000c01100c2ca210380881c02e803507046d072500030760400b41007100281001000b400341c10310304407104480d4420074400c5490001c0e00d0610404603d800c40d2100fa0080001d2000c452050100e400c0c124400820751003501c01914034201c03641d0303038840c0031b0400300e119200029564090322644028041002c0d410710610001080954907212 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 311693147 1250 311691897 311691899
    0x1030f06021e220b0910051b0d020d020a05031b0c0d05031c1413032106050f03060405100509030f03090a02150a0804030c1e15150506070206070305070813 68
    0x40000340c0f00416100025060040f04200800c103140d0055552010080381e0fa8110300740510b008986a014150703400b502c151700403e6000c6010400b00f0381000c0000700754240c50700300500301c9050740d44d101c0d041030052082c2d01c2006602040c01c5206404130581200300c00f600d0782c54804400042c40c03440d4440040d1495000020024201030f6420b0200801b00f1440806125046410442150700b8000904a0b160220490183e004041c8124001034000c4022409102a100300c0740b0080c005004d103000e403d0248412201c00301030f0b4500001e070700d84615031000c0140384051100b08040090301d4068580314583c8400d2000300010600c030310107140715182c10030080503002020f004001c0c000307400010080720740f82e0402c2070040c099800030300c9591194040c185442920031915005a00e450071202c810070800d072020202d0b040085050b0007200b219142c0000f4040c3c0891041545e4402405108041e17001070100494001400c01501410303003d8043d0400344d0501407541c8507981c83c0d520500d0100009115400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 311694397 1250 311693147 311693167
    0xd03020f061003030e060706020f041203020c0f090a0e030d06032a15031a0d031d04060623040b0301121709060414150c0c030705040507020601030f06021e 68
    0x4507481500b049941010500c0d50310b000d060003400907482409524005207060a202142e0111000f00084400e0706a8941d5182004a402d92001c1c034210014041c10700c0040d550f00e0900c090100d060002441d0031081e4440c91031143c010309084c0082d40150200340f14404014189214440081d8043c0401001c590a40c0c0c40d28003000c04400e248402150529801340078034164009211440bc09a042c000f401515201c412400300780b191092a9008101410603020035511140301c69688411040d010348215502c001c22080d11b031300740a00d9000400c1c075811844c03070901d809100b64008000c01159032070305445000307210696000340c000110500c8144100c9082000d9a2000f41c0b00d204000c090a00b04440240001d08510442c49445006640700601c0040fa07a20301d5211028502100910340c1c2c2c6444485815444e141e2100c01030340319008000002406080a000e42c91242141e68098000c5e0780c2590380b155020004100152901d907424402d04c400003a244200c5002e2124400740c072603d800c1d2140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 311695647 1250 311694397 311694403
    0x102130e010e090d121b05121e070e01030b03010e01060509070504180c030b040f0f0b09090a06020304081306181512020d0b090a0204090605060301060c02040203150d03020f 76
    0x2e0311119601142408000d0b4240020484000b503d0483c6864290f50500b00c1c82c40c40030f441011840380050001300c4400d4040c540000003070100754a5042c2d1041155241c0d07956046c4550514140001048100006610948148010348540c181410001511034034900441d0031144052014425070395561400e10052a0583c41154010f2503440d08900c1c1509004401c0c032040c1102c1c0c0400c3d0700545407824529014000d800242000707102078010804600c08070307489406401c040c40510700c12403030560640c07205c0c1411060305125501c0e040050411610a030f075010001d6100400641e403480092200b15520620404c0e00030040601307940380d548504451440300c008110742c1d84807003003803d484d19412074182d800050960690078140030068442100702ea107800605404a051540024070300700700700b4400066805402502d4003100104041c60b103030300610203144020f015080108290151090051500d13400440d8404503003078500007031340308400c0451b020581c6481c040700560000d28200c610780d4010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 311696897 1250 311695647 311695649
    0x408070501021903021504140607030f0c1d060a03090c03060e120a020606010e1f02161509181407030f0b03070614180603070507060b04050118050402030f0102130e01 73
    0x24900c2250f20990680d4080d50301c40600d40c0300b4940104804c001401c1c41002c0300d903210b995401d035007035030304510b46480000d000380308140c46038804030b14000380c23044c0c0313030307114040c2d061641b140c412450400d240258101308064200300040307810142c0f00c00c030310000268240c82070002940300d40030200e548204171090908104501c1581e6910240c2845501c80891340064080d4100e042070034000622120314010542c64455040c0109040000030800e2120990000305c05001e01002950004140c6d11040c810b640031165661190004007244400c1c01012002002c4000412545000060400c8124140d1400d8601160f07075402080e81c1d0130381c5110018403409100182401280038042250400a025203e14103000080400c68404903002000c3c0c44a1101014803400c014030031a10782c948408010b00079070121a003152094208003007014541424010503041e180300380000203001c0038152100d4024940200180d9062007840c040ca01361a070284000c0c050408140740048644e818070880207424981 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 311698147 1250 311696897 311696923
    0x3010e1302130c111605031e0705060c1504060f14060604060f0207030f2301050903090f06090a03030905040b090f04031b15060f080120030603070308040807050102 72
    0x40550311000680d0380480082c1a0001c00d41d000684110351681281c2241c000160581e00b0310841c51104041c4002402110446408504a400201c13551496902072051a141000c86900c88038043c03040c0d1a0100282030401071000071a80c005c1c100722003443d040b10702600d050ba090780e40c400060303844e548c4500072581d031564038904400042c00c10002040441c4141d1040d00100131020b01c0d2400c60034401d01506000b181c21155052a80185050608010804a24100c21a40ac80c0c170320744000759041c040c15100b02c125801840c205081041400310442e04003103c01c0d440041000000519507412901038003a41c0039941e100d00c003d0400c81840210740e060400a8482c441240030481100500c200842c0d2181e4075140c03e4a68825902e40c0300412040742100074100644074010481001302c503400003040798050030780707410081c0c0e58401c22803c030340d41d44c0e08042e01b444180b130009004030100d100a54001c180501121102540c07038417541c500c3c0d0041c0d0845000c5402c03c1004024960381000b02e002800c030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 311699397 1250 311698147 311698171
    0x609090206121b03011d01090c0c0b06120102030405061f1215020c0303180d030603050303130501020405120a0507050f030606010f0905060703020c03010608010c12090203070308120402040c0e03030d0b060c03040b03010e 96
    0x9c60300058010f81816030000d0015041000140541d12040307482d025102c5072400039922400d0619100e5117032001240c850080324034030070f0544180b00452121108403600040c41c00d040d01c0440e150300850150381f034001c4414940030400900364102c05c1004610404680b0000040c0a00d554000c9013032510020300001010706052003400411004030840780c00c030702c881c80b8281c9005c3c858a40340d800390049a12a41c0c0c040071a050040015001199500c1114450025140550b80b540708005418007200318094050b8008000501c0550140051700c01d03102003800d1599030107a85000051141c5d00110301100140c01c03078880259203050034010b24001c0d1642c40001c0c00000f140480092201d0b48810020f20f0307180d02c0f40701030019500c05008031703005941c004407240d650703284035910324490341d00959049000e20b00e8990380c204068031401d803448a0a074010301a520b850360504400024114403446290b1084082180000c003080800007400103140c1c0401d51501d83d031403c00500fa0000004041c600058 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 311700647 1250 311699397 311699411
    0x9050c1c0330050604090506040c18060b071e0501060609050a14010c02012604061d01050105011422030f031202031009020a170c0903010609090206121b03011d0109 72
    0x1c0c2c54107281c1d5030703020580c000406a4850002902504980c0e070050628024541030100b8002c52042c01c0080c0d60b8605803840c101a00035100408070341d8240703e0190988014040540024180703504040300b24120f000c2d031202c3c0e00c4aa204d00342140c130f05507c4000802da00e40e10411103401c0c04c021110081c05c40381d0304500700d6009000040c140c0344456000a040243e0448031061580312a400d18100b06021000620740b885c10746810001048c078800c0c0b140f03c20294040c0c0c24034514050041d40e06030b44069507000034910410b4500c10803500402094044401900d442606410740480725400450241015403032480303032410b0103004c10000c841750b40c0c1040e004004110240315001c0c072940445121881c0107950710004038040740c2c2c40300c01c51f8649001840c07a03014440786850380d5000e4900791404400030010140e9881c840c008840f40a00025003000040c420180c454800000c803641c407030500b840034807601c10401084da110ba40300360003446008961107205c8120008402c81c50f0701400f1502070800c01a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 311701897 1250 311700647 311700707
    0xc05071208150d11120a120302090a0b09030d1805090a0b0a0509010f060c170d0b01020708010b090a020d180506010602060f13200319020f01030b09070309050c1c03 72
    0x12104c10491401110304007032050000108100020301690441c0751509040000b440040207903200c1c4245070300c07e201a0380041002003119080b1184514000c00600200d0000c071400d403003205041c2a90720354542807202c001540d46031a1545c901c83c00c1d0280700007038a0014a400c00540c21035a030001030240b47d801005103c488a801d0b007a40544800b0b003041144c03e48903161459202c0e00c41d20301807030920030114030b801900c01c50b50030241d50810241c090f281e0f060345900c40a4201c401e0a01095807000310103000c100040010b50050485070340541713003c106900c034450f4040d03a040c040d000c100c1c2d146c2d0105c801000f0f02c50341803280e00e4100c115401c0e074410301d04004121245000310351f003000c0d00c400204440402003400e01428090440c4015042d00c07030660145800701e0762020711000690080c41888500700b2503621074131840c072001d5001400c0c2940ea886801080b4000c00340e2945c2150760b84640107118825a460345103142e14400c40e1751030500d8080c03013032030f006081d90b408451404c0032018907200520740d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 311703147 1250 311701897 311701913
    0xf0806010b0406210e2b12020f04031a011505091315180c0e030c03070e0912070b060f0d0209150d0b1e01061b060c05071208150d 57
    0xc5402e1440c0800d8010108610900c106a054240803160b80c40e14585060164000c50f00e03695802d402c4000e035101800660300c02d206c8181d00406040064002c0c14400d0300340c09a64050f00c9445007082c080c81c1020b0700c994910742012500412000b010020344010080400c1041c44511181150f02d0701c6d50400d11480d0205030500c5940c962a10045d1320f0350743c0c941c0c0e01452540104000d10b411000b02040e5080c40403548010481e5003104c000007150002c0f0303003119040018102c8100d40d4007034002c1c440309185c1604c01560110251a40c1054020840f159600c0c0e410200641040c9002d01075000f69800e11408010040b641c40d00024042d0548a000b400560b4800d418141c1c402c480301c0c21030070542402c600092484000d010000c0490659600b88420380d0188291400c1150302d514598049076203d0000741d84094089444848158069607003200294054102402c00402c0707061440c18004199241c00ca0444409000b070000303043e038020404015110300c440201c4100a0394501010500b64607a240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 311704397 1250 311703147 311703149
    0x5060403030c0501090b041101021603020307030b07050c100b0a09090201080105120a050a0507090c05041211040209061209010c03180f050c0604150e010f0e0f040b0310060f0806010b04 81
    0x42c800c80901160500400703401c01c00c82c0641c0302d41d0308a00352a00b454032018034120107009034014810075044503035404d450919942540c4d001401029400c0c910764400c43c0c4481d0041032042000380521481a20000811040001681640300458800f0b0040d0a0261140300b80e881142035a050100010150344c00401700d0341034071000d9824441003848941440d161190304003000345544038117003d10060040104500003941e9842c030080c40401100d1400301c40c02e009a0045c583c8180810001d44005040c542c4142150388014201608004030080090000e812000704148403449240810401c080203110741c442d22015810108480d412021030400301100d44c3c0303401030800740907107603903000d000c410810f00d80583d1000b408259965280c00366508241200c01140002c00d11100740039085601581c1d41044d251066642d00491406800820400d031380d140841c250410303500c588030366864606010300035100240075800309600740307441c1205600b4007655005005540040006126000e0040e003114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 311705647 1250 311704397 311704403
    0xd0e031b0108041101020309030d120b0d031b020a0b0a030c031b050f07110402040f15051206101205010b1201050d0b1f050301060e0609060109030b16090905090309150405060403 78
    0x58026204c100043c0c3c44c511480f12160f03418440e00d010001c0081e480350500346003a043c00700500c40e40850006100c05503640642c014007046d002d1a0145540094000c0a85618001006c015035150313a40e000c60680d0703001c000c1303407000243c41d407502080791a01030051265400110450204511068600401d28001e402d074409034a4000113241d030074445460031502842c44000e04c11552550707030b0070b001e9152002d948203000c510943d5880f02c1c00340c1402201640c40c00038030760400c0c4c403090356141c0c10418010034030400720013405405c0c0c000d841c902c01103101d5107028212810324141e41d1101514150020301059009a124140303007084580003c00101c5503582008070701e542c80001000c22500c0f0303203104d441e035085660950f04c2e0400001c0c509602d1000c490040d40180c41c01d1000d600d07800d004641d442450b020151003185ca020100783c107148040b5a120140500c0e191407011107171112042c40a4450a0715003c407507038808609052035190001006944c2221b80c1c82440c0381625002c0461481d000d00d00c405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 311706897 1250 311705647 311705663
    0x190b0405041505040f0204030c08060f010e040302030720120303010b0a0e0a03051b01090509040f02120a050105090a1101111507110a03031401050301020c060a0513050d0e031b010804 80
    0x541c10700100b0241007014000040080c03214004426a4000a4000344425201410b642e0742c0001c0000c404142140500d5580c860403519a080600940d22142e0140044045120400c10000400c800d0b000c00800350a502c0c2c41990000d504a081207071004500388502d4207500204010409800c00344211004500b40e8286800c00035080000200c0c1c5074001e900141450080724016900d061004480369801c50090700c60003c0991554180800d44000b107d0080002900065a001624041c10790384054809002250580c28040d40c881d03003034400584000030703580e0001540030100214149100c550700d02c00cac601550818944241142e49010f0700982c81c3c240329070f040c007140c011031044c0c0e001844500128101c80410300a4500140104201c810140d000801c140000c2018507040c02101c04601500000303040c075480f414420001000c0152120206041c44402c60380003a006110040007200941c8641e440022840c00f4582490340001000710685007085010800780e8008507025041500060301d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 311708147 1250 311706897 311706911
    0x908011b02062d070f03050f15010809160b0306090a110301091e020c1e070605090405060d060e0a050d03050403091202011701090e01110403080a120603080406030902190b040504 78
    0x29001507038110048410303041801c041089242c0c1c5d0020f212018814403554200a10754070300060b03c00303c081c20f6548000083d50300c404003046602c2502d5807900060114199444134200e91201c518481071607011030703404000030040101a2618000c115802000c07130b4401c1c4541c50208056035218813050194107040740d91407000d05500e54403010b00566102d85540d0440d40d030b880d20301d441071b13550340d0400302c0780c60011510f002540304040103d075060440728a0344410303003442e000a080001824004002d55000054451003c011641d5800740c0307006801600054a00480d46052546c2424402400c01061508100510001941c8402c8050444050446000e0008044d00c01240c001d400c080e4103035506040c5100108440103240d1007800460b400c180204001c54243c8848803c90242d0310000e07080302024400c0c1003001d401107110380ea80707080c50310b80040c00d9501c95803408142d4200e500028002030380d4015020440c2070a01342241e06210080342c141546141c2160103803148150300903c3c0c081c0341c031095 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 311709397 1250 311708147 311708191
    0x4020f060a0509060f19021c1209020303070308090d03020f19030b0405010306050921091011100207030306050d02090402060c0312040b060114041811190908011b0206 73
    0x70303969a00002055103650f04000703105c0c2c548a0300898240c03040d54031782d851a4109a4000240c1c10140c1c0c100706041400040022815218010b81200100802e80ca1303000e610016a0148010300300320303210352206640b03030504418452030155421000814103104025081e040c01c02c2d481600c407041c20340f6260b210a602e10001c02c80182c12880740d025041b50070040040100034603074000d1841208550112001d000c511038502c03801280980381c80c0341c541c0040011540b2801c0c8142050614020760034012030181102040303500c0d082445040c0d840299002c9460420076a00d8000e9030000c02003248d043e2031280003900014088000030300002d00c20a030000e490704160134240140c0d1041031055081400d2840e00b130030036590100f001c40d8000d001803401c0150030f16400c0000d0903101500c00c411955025130b0000f2440c0380c024010540c80100d81e02051046000c244034416040340c4030701c1140e850108030352801c2103207800d60300040040d1170055090421084015400207003545c0c095150300003150313410007200c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 311710647 1250 311709397 311709407
    0x30403020f010e09090c03010f0c050d1d0615040c05040503032208010204030b0105040f020301061b06020d020408010c110105090c0409020f0a0620060421120f060906090504020f060a 80
    0x290159030044d1149080106590002c00e010f046a0030a500a00c24100d603d411401228404000400402c4052002201030201c66000040000d40c05d08100035201c01c0c2c0f007515181c84412030f411100401d0b41e4108820f503003014000c07020b403036465042c22030030b04d030600000030707228001c24094080e841040311080c003000740030010241c000d10b0914001c40d501c903140c2c1000c8403500707024012140194105170400368110860710880341210141e40e58800c40040141d00080b40d00481da90507607600d0303020702140780c03d165940f0040000341001e40001517680055000504080503220400303250382d140400700891950003180904225200322400107a43d00503100240d0341b1580c0e5020315803c03030100d00e80881c15a400c8060741d003c002503026a02d0105062144080e0794090807240113141020390365000040c1e1140010303e042c41c1c08903007803071000000010040c40403203083c440c02032700c51501d4090400038074241e0700c0b032000a40039200d8280020310b0103401080b69501c03014411801800c1c002009c1c42024464 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 311711897 1250 311710647 311710667
    0x80a03060b0301030206070816021e010201061a0304030507050307020307060801060e01021209060d0f0f050402120307050705060a120c1806081302010e15030106030f050609190507030e12040603060f0602030403020f01 95
    0xb0100c204100e880700414be040c614040840c2c0c0590318242c0b000c80c82001c1c50480c1820242820101c0e851030b6510b42c2d040300c00d5000b03d80308a402d44002d00c60480141d42c10f200b190080d0140341d5850300d9a40c5412402480c280351100300a055420030b00e540500741c41d525045800034902507410701c0e50361003100f030220020704100741e907607114030b14125040407070310b0440d000f003800780d4001c0301e082195040d614040da0720782c072a60b44d00400640c807824041107242000c0c000b610030910181041c000319481002004c0070350300002c0c880000948031440a41d0310180500598026110340d240c1401a03142003182100e002c980e610340a0b0600c0540407030341c1c0082e600d91200011954128109036100e5035202400380c06400b0714100c014142c0c2c100350001d0500d0802030382c2d151051444800141c4811b00513a4094010803010f00b40004040d203400e200007010700d04000d55404600700c240e04550342d91134440002d040350920340007a44801c10020302000300704c0d40081601c081d039404031002080c40c0f5241300140c42e0400e803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 311713147 1250 311711897 311711899
    0xc050702040207080406021e0303040303090c03050a0606051e2101330b0a050a030518010c0806211e031207021516090e1909080a03060b030103020607081602 69
    0x50500030000300130013800c03c54000d90200d031040508201007a2005006502800341c43e4418800507011920981000d95498005c964000030705860742c40d128200318000c0010380f00280c655204002031b0400820030290510781d100700d15407940d25500008d0020711428850441c500d9000c2c001800c002c000c0d0302c2084409601c4040041002e459143e02e2200501408a541c54121601c0c001500d8100362084400000c2e081d40d84034909028000180e0003004041c211608400d00c02d40440340703510003440b600f0074601864460318000e00c0c240c01008a001a074500c650494030f0344000b01ca80241d800202e0382c29040900010704100906a10345a140d4012568a15600c2000005000100d900890140011141d01c81c000703507155034000302c050484203d81504d1001400030b40040007500c840c00c0d01e0680118034010511203101d03100c0110700c00d8840c06a4186e64050b00011800bc049800d84154001440381d64019402c5600d15000a2090b0086050151007144001170380d00c0c034458010300c0900d550794 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 311714397 1250 311713147 311713151
    0x140406110f0124060f080c0319061d01050d0f120e0409080319060609060f050c01060b040f1208030f040318030b07110705030705010c0503040b030a020a03050f0601020705040c05070204 81
    0x500000408200c2c1c070050f00004569222040404c5440c410324041183c19903d0b00c0d44956030322401045a41540014030540c114200707014480344d50042409207000910081c5504000100901401c4d48440d50603408140328040788510720001801002120b00100d4110050750351030701c224030045c1c40c1d1191459082c4d82c01407400682d60f00300001c030400346000e003505441c0c20440b04184200603040300c00600406012840b00d00b81000401d100c0da59244041c041842e04508011050314800d00f541d505401c101803800010400707228511458601e00c0042072008402c00810003692504289440040c1110402003280c000180038580a0b100d4120303110003c0b0b0001c0301c841da9a007025108100c0a481c11000074814098070055031000091460543e400180138140c0c45142200641c2c02d002500d90480c0c0a00040c00005440a003250240d071049501c40c0c80903030390358480030004044a4000f484409200c0703441007405640d990024103c3c1c190794040e1000103040340030310001d60305802041c100a41c014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 311715647 1250 311714397 311714411
    0x1e090601120f020a0806030c0904020609150414100512061c0203060a09062906130e0a0e2103041b1503020c0c0a03050a1506150503090706140406110f01 67
    0x2d110307401004000119070703030b803106a11110b01301a107440024141b2030b031009541000c84e0251421400070645e412000745a0340c10b002104010100070f400c0b0340e1000d4000c1e4524462403105050218003010070b810700345080d501d44030b07200c2440d21030b40302c0c080d0005008644140704101340b41e0032050f0703215809400508079280ba191641071100901042d01d01281c1003410140c002c00e0003071030b2f8200c03c05c12030b08140a11120560303e4040c000650802111002c4644c40748200003013071840d110656000300c08000c008075000707080724100341c5045607108c60200300e11001c405a295582c45035050385d80180d072017040e156a0207100c1080c90074011040e00001844000f20540034500340c1c043d4000c06044924000351000d10f0186070810606d60214800946039030030401141002a1280255030707510507220400182168072140081c16148100c0140c5010500c00014030012803400c001d80c0000f41302c1454060000d40d8200461541401144100e41c1071110070195815000814000c00040d075403003a000304081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 311716897 1250 311715647 311715671
    0x309080301091a06040b0d0e0c04050708040302010c020c06090105070f0203340e07110f07060906230415020a0602030a050103150c0203161103060106031a1e09060112 73
    0x5142400f584014a8104005000d01c0d091450541e0304031480d0301010750400045e00302a40160280020b002210b000c2d08000410780d83e6a032041c14000e11180d41d680c03680c1c0c40e191038040d08480111410340159031240c00c0c070040f19a64a400c4a4480381d0030710f480e82d15402c4902e400070200000c400e009506015451460948112080700030700360b656860050150341d0745c0c01c02c01a02580503401071b8501d0344803140006500a009500b406e0401d22504111180403075622015414002d01e82c01c2840000d001c004200045903008265500c502d000750002414041d102171090310b5071180b4415404180f02010307910341c5090080c032901041641004007550383c1d04c1c01c0c802400c010002400700320b48040c5078a101c41d55103500d92051000019158000f546052010b1400710310b00349807008201c81f41540c20351025405d44050110324000c0c50203842c0440d004c0803400b20a003003034002c035509038045c51111525561051085c1c250020008065410180f1601e41100480c0d00314003103011003e01d46d04102a410380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 311718147 1250 311716897 311716901
    0x40b0103080d0f0606050d06050a050f241210080d0206010608071b080a02280f020f04020a0201050601031b14180a08060a050109020c1b011809050412020703170a030908030109 77
    0x7d00b084408100741c03911902000801e40c400c3c081c0341c3e0081c0003003100d01e441e410032100d4840000c10f104040c9444120810500146500017446982025118402d0000d02039001c10076001030138104015203014413208200a5440005100e81c2d81000100c41c0801c0c8064083c42040132000c8402122840036041c50030600f41542c0403091403001441580e120004d451000e08054144400107a02e0056000c403a88606540c0e081084084ea401100f4204c201000e54651008108049090300046407601e0b1034800507085440740d0407000e51001204a022402580c410049100810034030f1440341c40311400c03109000408485440c060304408401030200d088031002400c2842030303030788120030703c003d03a22600c80c0380503400b800203c0300040e030201c11840002128414820050b10701854100000050400b42040d422803a5010340c5145030740b40284414440a492094441401400140790035482d5940d82156120a010b00600800f000b1894444161080d007240ca0599040075004d5103d507103460f18180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 311719397 1250 311718147 311718157
    0xa080601080601060906090311030309061602120304060e1201060f081b0303211f0f09050c0a0503040201110c1003050109200a0302090d21080f040b0103080d0f060605 73
    0x140700e01000013039600e11542241c0b007074480942d2241006491640e40450310b80400402c160300d80003e1000c4145601c80c000601070080072101c1100702c0103a18010320130380304068007600d1055001000700384202c035001079020400a0082e106250300440100c085070042c03c4e203070084c0401000803940080c000b6800610302641c40d180003890080c0c0c2020307c0c101640c911a10a00d1021f00b070f92811107080c80d940c8002003e41c044011401d114070055406400c203114000344c2c00c51082c05840c505c040c000c49044e48903c6501c00f68411440d89001e540d60740103041800000c10080c10020156080382c03511005103c1220f032a80c01501d542c1468010000250141609010741c8411524041c002e1444000c01c08414105011210400c0c2c90b01d004120304a000e90f0040041e00c0c1c114881d0000f840009100014440440340c1900e02d40e01901c00c1441e006048040107000341032811714190900000c41c2e03071540002d04483e8040b6455554500005404018203104029212002e1502d40006400e5810000801d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 311720647 1250 311719397 311719409
    0x150c090402070c300c06031a030d0201020a020c0d0804050405340f0e090a050703240f05060322030309080304060b0906060f040b0c010207150204030b010f05010507020904060b0a080601 81
    0x15024290950382e07441400ea13a0180607003000c211940400ca424040c0e40038814415444c03104050080750100842d00d4044102403050040c1c2d4000384601c5803e5041c4407168004108403540a07400401d901c40400a00450046a01c80c65444000c5515940c800c028900d9031010b1096403407481d40c0400c034000d1200074010f03c000124460486904030540b1591070780060000080502a283d10307407602200082c0402030581c402d0655514640c00e682a4400e00d03100f10595043c1107906039810481120710794079095124501a80e0188103008004030558410381010811183c012039141042c1002c50180501590103071081d400041400207000980d0080110010107490904143e10741006004951040c0c01c18010101d1041c002480328844100090120503008400941442140d854000c8480d11364480700340110380c0000c04008009508542500521000b880b0350001881e04001810511030f2030b02c000c1c0f0038610280040c0c02c200c01540030b07224008014050440c0b1640ba500b05070398488080c0601 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 311721897 1250 311720647 311720699
    0x50d03050f0f010503192607060b010306080a030804050a0f0b07140c03070f110405010b03070207150e2106070203070201450806190e150c090402070c 66
    0x1003802e208022410b04032007020b0010100d0503950703183c0c0c204110941d08210b5240d5000340b0b00000180344941c10070281640a040e5075520a201d00d03080d42110501d03140f09040c5800c1c4002041250303008611041115014100f01c9000e5403240b822078104110f4090003082e8601012400050000311103c9900c207000a071555900034180c4920040c05000e540f0706140ca95104100000000b54143c401c580c955109030013405031010303141c0c0010182c8409822040c0308410110400c8080e90b0304001c064005c0c240810310b140520b0010340020400c0303c40012070341c0190010f0000c0a0701c6c0020340c0c1c11001d0220350409440d068101524003d4581d0721154003640025030041a02501c801c40070302525002c94001050020300ca011100034000200d920103914185a91075030001b04c90703074140304651050304031200d200c0c2c151045a88000407140007031307d0307012031f84d000f074544c1c8034156907160030580c00000c010b106039114002040000d0281c030403900d00800310400d540000803500641310307540100007503003010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 311723147 1250 311721897 311721901
    0x6090b0306060306060f060c030d0c0816180317070c0e070e06090a090c020f010f0516020105070f1d1c0209180a02090406061706060109090b01080105040b0d050d03050f 74
    0x20155121340580f000c2d50301c440b802d1440255440c044000b05074040b58081903900b0407c180c484a412110703294807940204011504210f4001200441e10124400c03d05244c1c18044214050854980003400028800c00b64001d0b0082c0000e441e80559818642c0700c0403016266441c3c10030314840300010740707404000c03441301600b00e02c051601c10140c1d0607070080600140c0140e4581080203016240c0c00041c0000e5005011458614400c03c0c040d141d2000307183d41020406051030008080e03050f808001e514110791400c000c0c040b0599110b0050300c0b80701c41600d0031000380c900c41051944002c0b444e034913055000400034072214101142c164180035060080742d02c00c016a94944412f08030501c0310303403441c5d11900300100043c014586290360b00d130040d008940006034961154400c40b05d20360016121070840d4016401c0040540e4000c000c00003600f0845c005002ca10120130020380031000c18010309118076120284c0506d55118107080c00c0d20b9541260403140c52000f0703d400030780203000944404480f00f0542c80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 311724397 1250 311723147 311723149
    0x80a1806090501020c1302090a030f020108010e150409140708101a01092c040602030f070201150608060d05032a070605030a020c07030b0106020c040e060723090406090b030606 77
    0x1a81c4040741e206030054200480094104810010311030898641c5039800d01904015032a44890b6401462140c941d114400c607203130001510a1030145d1050306600070500801c00e0f5041d11a00140090100b80d030081440030561805189140b500951f4804620030640000b030b0a110004e5603031038081104001b00720820700c141c860882c44101e4808a0302243c1d0500041010010780a01a410714010442d1240365400005102c10300c1c080550b024cc8143e038020051000c00b6a41c581c0c2c640d00000b10340000c01c000d00592105044440b0207110391410301aa01000807070a860388044181032030742c00360a40307588000030000107c440952290002081e0600300b43e080350320000003120f100351585511740c00d04542d10f400d118000303917202c03403002680c03805007207000000900c007648a18003a0a00b0740180a030b880b07040c800d000c102c5100c2d54a03484071354400800d02094940104030080c2204251000c03080f00481507100718918841c01c90550380191404200052011140e403201c041311204806850f01c40d12400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 311725647 1250 311724397 311724407
    0x30403020102030723030703090303080a0510060509031018051c090b0a1101151703040f0b07031704050a0b0c120114012c121b011b080a1806 62
    0x804000e002d42e20400219000c078009a50044030300d14508a4000b50100e001d500b2401e580164100310041940220705108041d0000310311075003c0d0714084200042d2070807035010b0208008a02c540c030244030002400340129101032180072103800d070340b16050000d005a4400b2030b03d100c0c0266401e54450003004151318007503040080d007920103001035498020290401c42020b23070580c8040c0ca8507081c407080c0d02014a0809081c043c00089030b0007004d2600301c25217040d603601d400741b641c1d40000310306402c104024040d2103d8a8103820039034a03130f0543c49860300464a8103485480781480d400c2590b5180703c0410042000004060b0102846018000a01d898075002c800030f5004040805c07210801400040c03180d021b4070f41002c142c1d0707d014034041580e01540410b507401c2100321910303020401c11305035a4011500f07241c003002580741d207000d008149910350f05444001a188407001241044407004200240d070024090108480c0c0c3c0140c91142e40f10341c002c1340601021202d40d00c0001000c100302000942c14024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 311726897 1250 311725647 311725649
    0x6060d0506150f0d0c08072108030601031d01020a021507020d0825090320010804030e0d08180a0503070605071b15020f0c03010203010302012033090304 67
    0x41c861030b10b503807120300c1c41a541680c03003540000406440200380d0355080e45002889000340c1200410501740521070381081600d4020321504101c18448502203400700c6902076030181c10980080d12915000700407000390004078909580d580303112000303984c015410b42c01005400e40507001c8031010f044103500e4141000e81161100302507000f1000c40390701c0c540195045507100307840943e410340700c408805e08094201203d908580005103840e43c2402006100c103078085280070700d10b400351030350840e0800090201c08020001010041000300101c0c0c40e80300d62100c0601c0a60210703c4c940c80d900e1014647c10405204680c071b43c4122005180003c490801007540c80554806070340b00c40c54010180c65076009a10700c008501520080b202000402558522404007180038640c064000c0c8000500e80900d8581486490391203a44108010070040c0e030400e10100c0426800041132100c0380d10a078500d818447c80300e50303080c030400313801180350300418200002c0e6408901500740c402d41e5444403204942d89000b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 311728147 1250 311726897 311726903
    0x9030203210606030a0c030b0307060c0201080c0408030910050405090f040221061f05031c090e0c0a0309080910030e010f0603050d0503060d0f0f0b071b0602090d081204030206060d 79
    0x1040401c2032403415402080d0b81006c1ca050100d004607c00011a01e40500760380301d000011a60040305007190b030f01030a171a41194100d07100505190508000315100c2c07049000b0703944541c40c416050400c042c01841503800800000303040b0b0100d450569244020281b003140c040703110744040d13071000340c0d403c1c0528045a42d400154000301625510800e2254820b032401c800190392400c001c000248a0b5410030807808034102d1204140700e040450390b0041d109501750b802242400c5241c41c10411016502816a8035840c2c5901d00070072120000c2c14410f125115100c2000d4000900b11000d04040780c260300b003040c544120340000c00c80380c0002d640c1e21049078041e000c000c207903401000004031024401c00156070080c2c4000c0c11141e10100315035440050710700d920801c403002c4c004641c4207000d10a0300310300c459201240d400c00f041c02001650b00314091b84c5540000030403895010602101c10f031202c844c42400e05074801440e559070211100c00318100c0104507000c0700103100303140c005001c0f42000000c140350594 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 311729397 1250 311728147 311728159
    0xb0307270f14011a1b0106060f020f0a030f030212090a0c09090b0a0908090904140610050f040510090c0e0301050c070209010b0306180a090203120310090b0402070501090302032106 79
    0x1007404900c00d14100041c842c400c40b9081400310103500d00841003440c1001c0405d00000510780e00c0c0c0070024004050303403851801990010ac182d004e00d698003040740b8031034940c1031401c0c0348039844c80242540240200c10900340102170305000c225240200280d010300b100e0051005a262a903290410016684048001080c5c4800300d804640b02e907a080e04210792142c4185140c9050240c6e00004c21000d50040b9400d41d00300e80b40c0e042d0003076044400d0000642050054074001c20b400d06120102d01181c08a12510780035075a1040010f200d401c2c1c6c3d029140250a2148050155081c4844014046400881c03010320a520b490f0101714403601500855440035805000300880768644030040b402a04000e041e59001125120b401701c0c44000741521a21440c544100000c1c018528010b01d40b030440d800f0075a0b0070105c01082400001c4005800100c1107401c00c10300864490701440c0484c000c0d01943e00002d140c5d42c2404002810560040060074070b205040e002c1c0701c0041d10240184040c2e20066640d41d070001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 311730647 1250 311729397 311729399
    0x70210090f021c14121803010f0c120522030f05130e0121052802030d090e0a02190e01052b06080109080d0b0307270f1401 54
    0x550150045080c00d402150030007103180a90b00403d070500e00f000300321a5000c1d0b42d03200b494200100d100c0441c9400d0003480060030b2103140b0b00f504010700d1003030f41c0040c0070846900c425610039540c00d411020a201140806001d004a0981e0203010368400c0c8650a4256044c440020100d07000010440c01c42c00000301400c024030307490f4506580b02c072004208841040b33810070a0f030108610391080c0e400209013000702001e0355072605401b890341c04240040900180300303011228020990000e01509585d280503042c80c0136a03004510050403800d0300e00020b415001e8454005800b03900040e00c3e108881d5500103d20907950341d0741c171910891041480914110085204408200e40b285500104e00f05044c1022403400200c0c0942c64000b03030480340076581e40107101e01c03907010101850044030010300c6007100922007007a02c0c1d5500c1340240110245102c645541d11644140d640d800c10000b001084c0025000e424142000020144114819100e240190071b00d141a01035101c0380c0314001c007000240100b99201d17 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 311731897 1250 311730647 311730673
    0x3060f040b040c030b150a06050903062d0c070b1e130804050619110a0807110f0907030e070b03090a0303150b12012903010303081905160806090702 65
    0xc620054020b458440c009030001c0001845c01100a0240d00103040483c17201180208024991131580c0007030341040018002a102c0340c42c0011020b401641c8842261030505502c2503584082c0920020700122511110034400074010700002800201d000701402d101076912464905104191240ca2091440c0c801d000210601480c03801180346501c1a81354074506980c890015401e40c0000b0b03014100d00300403144150400340c101e040002c0c074985007006800c4412068640203030902940d40c0142074410210884880c40e070310310070003c4140c0d10060841c0c0050030181c0c1d004005000100c44c0e841d8a100341100424841c210710152885802c03440c008011103240c43d80d0450190800820142d2450b6480c2400310780701c652400980380015280d944580780f90314000d42d8030200b80780c1c034108050318034104400300c445084160449054079050b0412103001d441d9041d462040000c21040c04595501d04070610641c200380c040e0450091070240d440b4049074561130104031000e1800d07180781c400360744080000024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 311733147 1250 311731897 311731913
    0x8180405040f060209010c0c080d030c0216050112020f07080309010f0908090112060f09020a08061c0210020a08031005090f0903090409050708030307020708071d0403120f14060f03060f04 82
    0xc45c0c003041c984560480081e90f40e50b07944400c03e03040ba180d50b420001500084591505c40c00d000c000880c4001d20070554100888030341d046080c06034504020305504088144056501100e240c08602c034207107662000700e414592510f800c260341d05030981d4200003107000d1261081c02914021074000c00818900500303e0300548403c0ca84003080b0050a0f00c030b820004155406920940007009a00c0002d41d45000b8404002d0089100a1070544200400001040c88421070781449080c2641a60346048800300c6c860140d11b04800c406005103064800001c00c2008511011520221142038403c03c1103501e440e4155512641c0450305a20154800e0100c00b541e0b01e0103801008415015000f61480707a512952000d0840d84202c40040141e8440d200800038050204980300c014000340d50510200b10b030005a600254001800143c1004402c49500302d40d10b143d03502003040d42500c02020800c02582000440305580d0071200c0c5403107160581000000d6080100e03202e4813683c1d00c5007090303249a0f80d035070714107203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 311734397 1250 311733147 311733157
    0x305210d02030612060a0e01060e0108060a020307090e090a110108060d08090105040b1201050315070f0f03060b070c030605130c090e0a0c0314070f24050c0a08180405040f0602 77
    0x5480b02c488100b000303030900d040c01164004d41121b440400d881200e0346a450075102e00754024003200444c0320040154580100c3c840e81c0024604a0150340d030f80b00c0100c00c440b40181a0021400f00906c0c03c01d10800560001c0d6154425103c0c84400d03425038000703001542c00030812520250408540c1d42064001280500141001303a01418024103264071039403802c8003600442d420b02444000c680060006d86010452110250198111b440c0d00380740910b0004c1c004100c614a00040c0104003a41c80c42243c000e130842400b91107010301103034807000e035070511403159100c0744030a66160b403912010a100004400302400483d80050895440602d0001c0101c020040c0320360031182d901821412000041e50701c1d00d041c000b540207880c440d0210368410402c90403c80e02d548116001c000107102081101d0f088070b00c201c00b02c500c1602d407184203084c1203410741e03036846620411a214002c0c140034108002c450342c00f070402c0c0000401503621401c140410301007110001c0d5006000755103580d030140005010707900240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 311735647 1250 311734397 311734399
    0x70b071e09360204140a0e01060203070b1b0a05070c060503151201060b0715060b0712031503020a082508030f130b03010608070f0801050f0f0a0e0c040305210d020306 73
    0x5000b0020550740ca02241c0140e04890300c0c01a1014028845140c5400b44001821407100820985d5141ca54043d56034824184010f12000107900001c5240e14140000c2007907110107200f25581e2510108010010707480742d0750803200010302c06400705480744200150b0748908890f82c405004881010108006d24400d05070303980d0103648079400400c0c18900b9034040d01c41c5a20400000400c8240803650101780d036100d4020448500043c8112008100001106241102681000260703400c805440c051010300c0d641019401940410001544c4200054500031a07031281d603035003400d10b0640b071a100c0421094407607104a540180482104508403500900c00b000541c580700600d01e580b041c144c881600241d1002000c1200d46040080290f04080c2c01d0703404003c1480c2440c829030400000802c0c01048a0400d40200c425184210090302c5128011014203c1500720340e107145011201030095900500048034540692004811620480c0713000200c2c41ca0031094050030003105401090094100408032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 311736897 1250 311735647 311735729
    0x308092809020a090617010504021602031c030e03040b040306020c1c18050f030d03020d09060513020a1a0a0804060902120114060609010203040504020a0302070b071e09 74
    0xc4000340c0c003041100024924048056110192030601425800d101e5000d0414000107440390407054014540e5141500e00883c0c00503121116807000105041c2c172804000d4142c82015040490140d2100c90b0a175054150b47c2c06003c2070b24001519900d90180348222000014140801d0000031100d8000d0800d0810410440304143c0350070700ca03c505280c02d100c5000100f0810b90413103142019030b40d1110060101503902d440706000c10804280e81d50381001050040540c0031841400500094002c001d0058010006006505001c20200070301e01c0084412440746002d460000351009032680ca01d081003140715551030074011a004140c0300c009009008451180d959190800103907114640c800304200c185000140d503808040680820860152440c3e205060610a4a20581e400805c0710261b88041c1c80150311541c2252040e0040d00a01400501c1e00c0c1c1120304010306c0c580d10044800d0644005480800601c0b0100e205455507491402034410680c0c552588511a00052006003880c4001c16a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 311738147 1250 311736897 311736949
    0x50114071e0b2401082401020111040906241e020c060406120b040e0a030309330506091005010c15060f080c091e04171803010e0106030809 61
    0x1d00d45440001c0f90041031850002c0d014070b00000c03259001d8010100c1c217081c80000c5007044c0d5521580f00b0426083e0040c0d0200300c00c0c11444c641d20079040550844c41c40180541c42d2606c070051180a004240207040165035030300ba01e000030041680aa98001342139440e00e00100c0002c103001480c40c81120002e02c00d51207002c0c0e0000080d10b69000400041c0110741e28241c9528040390101e0035a102e43c0d030114401d138203025142c1906d24011890903002a03040c00c0000d4042c0070361030000541c20900750015649030048942e11584100300c00003014210039090104555500c035420000b034180d00f504c9580c15100c4405042c001940200007034001207008045100d51070040c028440d0540b60310790086100e0080c603820030484807504110304041c000c012101c0c05014a04140d00f007604d20006056240090311384804981441086d0340d01040b8519805005a9500402d0302201c2e428100c205840340290319200700c0c1019024103100380343c00d0320780c0074003418540203400701000000300400d00c07a450705600c0281 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 311739397 1250 311738147 311738153
    0x140703031107060507023d060f0306050610030504050c040f0e06151503010e06150409020703020a030801140f01080705121515160305070c08061f050114071e 69
    0x150110700c1c82004041018a40398400030308004c0c1c0750103040020680118107c0d0f104207040301c0c500388051400030354a104030103105034002034403040d0310034007101560704000b0090103810341020b44070310006e55140141c0406180c04070304884c01102c019001341c2145080351340c603250541201041e070800c02d6010074252502c0e80310908010044c1d80c00009403a50144040365030030100c40c003009005003160703424110741c98201c02c007036001c000070000c91140107840e4100054640c120251006414901400c42d00c4e900c42d8640a5030f25441e1100a0b40407800c03060002450403608035170300141d1200074058902c0414004010748110801816100034801c05003c11082c10305104c2500d442003110020302036003c41c100c41444a40c0020312181002c801d010003121003060f104c04c2c0714003031580d85071401654070030050410750301042c1c840c1c01810281c042e4200340041c10306070111515030380101a510300c05003503070340006488100b460903907010004410721220000c03d0f980c4180d0b4000860900b141f00110180355 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 311740647 1250 311739397 311739431
    0x7020105071a07080604090c0317041503020c0705040c0c0f020604150905100503010620030d02030c030402040608010606120213080307030224010e1315050c07020f090714070303 78
    0x440c08070b000001400f0401016441100782c0c1d00a00c080d6010400b4000039220b52004550501001d41a00020101d10350914442d1080b200100880541d0494031901c40c20014003075403100e1594241c070f11a80c4030108003441c00e0310600d8500c3e009911803182105480c3e50ba410160450f40003680c1c080300900c40045c0c41d0304400780c0781800e0040d6542d0366110505080400a034481614414010002c5c00d100600055401503442420035a00e01c6607600505840c812462171441a602d00482d21400441444000b048500140d0301452007114188005511120302908032405841801c00042901c94a10a800c0a1b54003c0c140080c01d402c0001040d520b07600940e15681c00040d00320016801403070214888030a0002c83c24541308000314030321503540b41061680c14400050b107441d0030039910682050401160010710035442081d41803d005034078011803481c0040c1c010041c01d81c0074152851031003a0600c0c0400c074040c817501c1d0300e482d031440310340b0f1520003000603420600c400c400341540c5550501c2c801c1886 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 311741897 1250 311740647 311740673
    0x60301150207080d050a1202090306060d151401080d030908030c0705070504060305160905090304091a09070f02010c1407080a050f041202100c030c0201080901180f06111e0702010507 80
    0xa1745600da690400550004d00c104991391500d400107106010580c0b803a46c01080194210404540629003288141090150078501c1070794941e1281c074100c07000458010035a1031038104d60040342594101c0070110b0f009d805442d90b200000301005002c2001440a04061001e0603400b4000c40844040c55201d40200703080f112180c006a82035845010700c822121000580000501401d2602703200b035044c4076154540d00e010702d020300c401980d16110706170f425180500da22950840000c065560900f8640000380041b000c86002000550800e0b0a60712054042d048241725020f0386602c0c0c03403811041d511031146076082501c41500b08042000501c082100e510060800317012a50607001603500781d8030400c200301d88412889014820044c140e5804280c0103003c2400d86038080c20500303100d5036800c40c120b004080b00c105000404180b8003142c0c050189550440c690144103080030440c05141301c246001901074402c0e21156100b480354400628030041015110892041c18030034200304203035449001458203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 311743147 1250 311741897 311741923
    0x506010b090405180a240c030b040507020c01080105060c0109121e110a020d0c051002010902130e060a1e110a08061c06090c0b070803070806060906030115020708 71
    0x4080380c000c1c0e65251600c180c0e600107850104c6448002c40100105895100c61540607000f412550029104180a800f60390b000c0003c0003400c00052901480140040403001800c80c00fa915010000302200d00000f188050910142c603042803582ca04420080941d10034000780381c4039500c480c8035000088034820401c0c0082116111008801c0005001e54904160156110104070480c028240c41420120b020701c00650140c82c114408034081c2885144030569500282c0c000f6002840412101d9065025034000c900c01c60742c0381072444440051000303172000283c1d8601d81e50410004610301e0007466010404c42d40049040694044080c050601110741c690303039481000500140c40820f003036000880035407080040f515500c40003003a1882c0003042c40e1042c0000c1510f90351300c819400740108032400000400000590f60f58440a620706040507800990f070172004107410b080030840303505d800c4054407c0004040c20150540e86803550102000e41014116820341c010a0000702d860241441000b170b003001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 311744397 1250 311743147 311743169
    0xa14011a0c16061706061903090203010b06040f06080c030403050319150b09312721020703051504020d1505090706020106030512031b1314030d0807080c07050601 71
    0x4d10342c488003032448010100c07807080324100050584003465180704411050300345000074030f6100340c1c40480c0c010301c03040e941039030b20500108001944040011002055900303030780ea0201d85484400208940d400242c42c02804a0018800501d020060b00906091000d80800100740c0f800043e1f07080c03000a4441c0c20100b07e400c0005034040f920b09001c4040903003d401d22a216065032415030000415103032200c7c100d148581c0f43c5c00101e5002c19084052101c1850441d00081c090b802840d1458440344c01403030f039804516803428104c0e0020300119043c011240c008010f06035000145440d42e4041ca00100300701d0380100c625601034003050030a1401301da000550400014941031220b281171910750035500420071603040084c1440001c0d40840c8000c2c0000074050a19101c1d15040420440d00801c1c3c400d0002803240811200581000390361650110b0304145480284a60b5030414503443e64034100b11000460032840206140c0b502c200c070306503881074a00320070038103100507559002e042140a03840180100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 311745647 1250 311744397 311744417
    0x1203071a191103070807050306010207151101060b04030c08030f030601140c0303090a05010b030f0703080a050c030319060b0324030f0f07090c0f14031302040c080a14011a0c1606 78
    0x11741c00c10034032504000702e42400360952804800003555030046014081502010111000b0700341d0040802046000c5000000d01c581900c5900100d41c5410510040c0c420304c4104a00249401000c0308503020700201d5100d0034610356a01c8019102d0f520781500c4540b001c3c0003009034940742031040c00694052000903014000c15546414107a081d40e014001c4184030b03801520071314042000006190381226405066070f070f204c10f070180c02504d00d4050121400040e0000008000c0704060504101c4c00c0d4000b000304c10841c0303684403c0e000d011400704403504803000e01d40c0000c1c10040030140f80c4c42440d0390301c000c045540150f407101c1e03075505080504140070420b81c480c1d4400e00035141d16000d28400802e9525103003001061004c070080c409440001581e601010000216240c1046420b401c0f040c95005403081c00300101d80b0700300405d810004c6504424403403a0071404015807411649160481c0c0e8510242894980701c00c0e00c0c60b840d1b0740302c00380c12800c520038145000a041501d0340120000c140b00e071290300460b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 311746897 1250 311745647 311745661
    0x4081f0618230123030c01020a110f09040305070605011505070222110903010608010b1c05010902100c03031505010519200706110c18040524061203071a191103 70
    0x21503204c04501c203070001740713030181c0d1640e00160048001750032440781201c080ea12030200300d114100840c6d0381e801c85485001c000a1640100041801c3c5210759030401140e07a03a8094580c07809000440b0b5400900100301c8003000d8640408198041c0d140c00c2661008100d0324080d0000302c1c0d07101180516070380408110040c0c035107802e104601c002c181d000c00a0000d5000140058411200d21600144001c61105802c0600001758050000e170ba90203041c103a03048552002c06482d004602d601100000d042c04401c1d1012508503001c03104903181a12040e05024071090302c50303084803c07c0350020800c514452141c0042881c480780804008501c8040c0c03440ca130501038028800d400925880e0480d42c03059840035100c0d210048084108100c0410807907040c2c8540ca460341c10002c10508084018880c030010510400c48000003032b00405044848904040702c0002460b12400b520402421002500c00391034884240710b450190b000d41404c0941c43d65081c5c41a0410498000007c0c100541d0400304c204025 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 311748147 1250 311746897 311746949
    0x6120b01050c03090d14100b040b010e0a050103020c0f030d150806012108040510030b10090b0d020c030415020c040b0a080316050c0604081f06182301 66
    0x9010a00e015441d001402000da580c0c0c2c41510071490052001201d0b140074422460b4404046420350f000359000c406921381800050b1a1110301607120303500d01504140c0e6580503030010200ea01019006040c410b00d030000540c025000b00c07e89400074050554480d074141001d0004240e4200f2005000a10f6202c0c018403985030102c6802850039580001c005010800220020a815210340d060f41d5840503624900424075004a90000c2d411034003d140c40001c07140c050300500c00c40f44094030041ea050310b03090b0b8101c03a520490310801c540f01a08020070103205000e42c008184c3c445010040724602980d039a200300e030601e45007014000580002c0040081490b01c0e004403031040c0c5080700e42440303040c00d2049003910781c401c603514142e4441c8007454240c00c014050110380354007003004040680300c945e00c0e4030190300c50040b03000940d480f00c010400040e051501b40300e04000d84040c0c000c4180c1c8140400c12070b0700180610b035248000603491200310b240e014117240a840c0070b046003d000324443c0481c01c0d41480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 311749397 1250 311748147 311748161
    0x2109050a1214032802010f0207060b0f0103020313021e10050c060906060a050904061e141f1e050915010206070f1413050d0b04031101021603050702040e06010612 71
    0x154108201480c081c404d5036503680c08519510400506680c442c1e00180d00509880b410203c2c00f9001107000310034002980d0080b44414000d403810070051032140c00440480c8000c44a905001c0d8030045c000c405410a20101e1420200043c0040e100b0a0000c00103003501c08a41c41c80c40c00502e0008541c04282406d0052641201e2110018251400c1c0000014104a024000c05008170074400000c0d051000c9a007003281190703c0452018841018140c06c0b00c0078140303824200301a5500e4030040b0b98003c54420020b50b030305824400d404901d40c10f0800004034040d0b00860180c5110226801060660341c1904c210b000d0306d03400720403144024021001a06000340240200140b0020148a16050b5000407609030b000e002504c00b20f545509106558844c440b0580041e034018480341c2c044d0301040044030955020341c0c042d881e4841035051510b00d1078281e01c144454907a0b8600d0181c401000203010784043c05080d84014000320311402c1004a080c6040d4099000300c0000d400082c44115075149445145 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 311750647 1250 311749397 311749433
    0x803091b010507030302031f0605091813060b0a0b0a0c0b06061306081f030b0621151b07050d0906052706071203090614042109050a12 59
    0x1100d500321440060030b00d0040c0e4901509168001002074492050312104030030b04031100e50314551032500c035140184990052101030b40550b8020a8205c0820420301031f60340700d8511000050304440711982d0365406400300c0e00042d42c00000500000c102040780c0005802021019074601c600340b1241d04014001c03600c0940898081d40c000c1040c900c0501d0900e01100546a1904166030a0340b501e508403070004c1203d500c0d8100c5903080140c040b04010b1100201d901079501240c08140c51148a00c900002c1d00d0704c4810583c5503845000e440c49007040404280e07a00c20145100503854107208103070b4800070341c091807049a031608074039a0310303040c00d8106030244041c1500703140650900c101c1240310401c821200030149085d0a0312380004000c0e03651101105ca0b0075500c0740758984401c00821014002e0191980100d91180c1000c0800011440041c21184a00c1d00480c0c284140325505e4500b0410b0070200680b28100507081001140301e44901d4404001803450a00501c0000018103110b440048600822 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 311751897 1250 311750647 311750683
    0x90f05150a051b07020d2a0305060a05010b0d0b060d0f090c0e07230702040e030a1407030912020406032f0a080c0913330528020f07080309 61
    0x2030040e980c3d2100c266211154150798003101080300b81408503c07186c0000f83c00013030801d1464540a140303000d91641d0f007100e1003901242c51548074590f484c4150344090003205c01d9882c0038494407100420f40d4020a451250150859250240100d408000d4036004d0b50002c02c241e40b40c1140d0b504001c0c880310044000c2180c0318180f510790401a000a10030000c51501004102c0304003144442c4410034801c40b104958010400c100c00f4100f103890980f05e07040300c0c2c018808205030881024100b10b034001164641d541c11f03aa07454201c2c2c10441000310802a245003642c00036604d040210010f502c00c0c910742038280071280c0c51144082e46001c11102c005010300e199000f240817003020803c06000049120345110110341e681c0c129034800c418820041c0650300058844454a035208020b01c411041d4425200808a0040e0240c1102d6030a1800e584d0151841405181c10201911110454101090681c100343c0009403070080040903104281d04051001c4e9440e600001c244030004100b08880e14032078504040c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 311753147 1250 311751897 311751931
    0x302101103010b1305060304110306010f1203030c0c05011401140103110d09020316060305150102150105010e03030702090405010203010608060d1a10090e0a0311070f0306090f05150a05 81
    0x90502a07000600c5440e02c0d100e00410664060301d90309105401800c8090841c58403413410341801c0364074804560515000b409540e0001c207000302a8504142a00d24401d0000b156619503a4103d00600c03810700c2c110200b041d49000140003446c20300641c1c00403c40c0c0002e44c1100d5040110040c0d1180300c0006560502d4a000d02c081c05107140042a40c1d54507052800000c0e2015447c00840c1c1854116400000402c0519801264058242c1d00c0a4020704110080c2511150054010780c0c0c0c6401e21603010000c54448001007105601c5004007000503440541580d0910903654089141d141041e00c0844850350003000600115500a4178580e02180c200e8116552106544a1070000300b0071220300c5c400301c894240003079441045103507100c000345001c003c208096441c514002e5110000c480003107002900710499400e00000004402d8107517003000900d54220752071941c88400409041c401200c1c2041103080c3e40f40400c0080c0308049480b000a0640019491310810403000c542e401000d0b00346034042020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 311754397 1250 311753147 311753171
    0xd050c2b0501091103210304020a0e0a0203010f12080d0c0516140f0c0a0905040320060603330901091205030901060603090812100b041203020106051002060c0f0405030a030c030210 79
    0x100f00c00d0346c14001c0f038135541d030740700c80c004501d22120300d400c9813030121040d4090060b91901980218102e42200c58100300241c1c94501c40002059000c00c0a0305c10b00081c002c0280c1803407160f00c001c0400c001420302a2814811301c055801141c44201c09440c0014038445041308210b0510a030a4444441005006411480400610410210300413215019568400107080501628205684d00c420000349420440c001603025658181120aa4028061b5401e80d40710341c64801c030039200700e04460011180c0c070410600001501e080007021440c46640707460b003410100301203500c5445070440b02ea40b040d9503031500034192403c1d01c0300c540c402010036180515601c0820400829038100420381034401c4610340f20031501d106a801141c01c80d594440c0000780c00038003643c14008121109119030001c0c0700440ea217104002034049600301000168100200003250710012400600340d03403100006142c00c16446102091400d19288030480220b4043c16080040c16010800282c43d40100c140503c8000300d210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 311755647 1250 311754397 311754433
    0x10e070503091f0906140408030601030903020a0f030305010e0f01030314071410050a1419050903130326090a0306020a05090312040905060d050c2b0501091103 70
    0x24509800c008000c8041030082030305004012850f80d1881180c1c45103018007150340d00414540e581214018a4403d400c20300080c0e51000741e10031900041d11174195900c080043d0f0180800840413021401070300c008000151504007500d180364001da90000311581000165200f442000d091a80e001070403000400000340c0c050380565187e1140740d419034417070469160210341e2400c40c0385041c0c11030098903041c105000a690200d803188800000a106142102040d500c2e0030b00d040d075010101190a40b102103805040390402600080b6050849103803180a910441002015400c21030741c801450842c0401c0c441010882c0b0400300300c245485140c451401c001545440143c8030040030980c0208140038003501070b2090380ca4111024065031540031000c0c031021900e1344140250001540b03018007054117420000108282154040000c1c10300311500c03003c001ca2009080d41c5000d05c01842c41541001c92042d06100040301c0c814000030401160600d071030b080014480d4001d9000c0d40c81500044012002d00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 311756897 1250 311755647 311755651
    0x80712050f07060b0d02030f0606040f060e06040c1106070c1208011203080702030d0609050610090608010303050c07030602040b0a08150604420807020102040f030b10080f0d020105010b03010e 84
    0x8000199150b500020404481c05d460001e94103004400035600c1180011a886109000440d0104010500700314054110303008e0b40565988207918100091036820240d01102d100f0034942800c100074245148031034504036085817400002101d02188074204074401c1d0b013801281d0158104610030758103142c00e000040141c501c016040000a4010581860091045508054000c2410b000c003548420481c4080c104c1610010300800d058204080542d114020759000e0721034540d1080180d0b46161011503168018a80c091310902508400100288551004000801c0120941c40e10740c1400000504400c1006103010400d907100c41100a503580d0f43c208a5041c1c401040c80051121080c3c48814010760710941c00c2c1d0544a10308005407441d14240401c0781001d40156212070099991310310403420307030040c1d02c107068001f645c640c800c1c4000f03000e001c005980b0048032500c406001c0d9503010841d290040022420041d0b42040008071140d40c1d082c01000e01614000c42010b155514210403403200d5000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 311758147 1250 311756897 311756903
    0x1206210308180714010806040204211104092018072a080c0f0d020303160c0b040c0f090b030a12020f12130e15011b060207080712050f07 60
    0xe030400044085492802d01032600781103408841d04652591140400c4040c903505031800716440c0f90000707002d45028001c950030784800e48000c0e0b4420103119250007004509910403074803003200b183c0140c0750b51a280f00d42000035020390080c41e052511038600e46000e0300041186402001612907a10010b140314085580040d41c520b009140307150340040307a501026000d00b06c1d0f02000c0c3d410780480c051262100141041142040503260591a01c0b4074079691190701040180c09a042031000650b1031415002041200704181040c01c0d4803016a40e8407810b00800b01c034101e40d80c8025600902031180320610241c0a86440c0307404102c00c4101c440000da481002110051410076001103e03048a40700307100e550b030a044010f00329550a06001640003140d00f140217000c4a1b07911b58000010240c44141e04a03000f00b03103144130b80c001c02110742c3c0115040c803600c6482c003014100c14065580029000d10007091b8950207006016103034211481c09c59542c0d60600740c0381c03007085400c0c0085c0b001210100708546540384c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 311759397 1250 311758147 311758157
    0x110a02060306061b031b0706020607080c07080c06041103030f0d0e0708060103240b180403050f071406070527030a02060703030905010b0a0605271012062103 69
    0x1441200290f21889620981c0710344400781202d84c3c895902c000054414400661800012203540800700743e5910424455440140d00c0b000100300c002e401003640c00c0d0003d04031455603290024940358407825034009212a19140c4c40311080100b07101403444031041307004040f4040c52405440c0e61082c1284d006040300c0b400510342d80c0c500c0c07401e030000030003410005214a06c10343e205980c4d6030914071024003100401001300395030501c503c0d041d240c591160860102d00203100752001c540d004c0003618001c00090003142848030400204000c1da01c000c001d051640d10a1271042181072402c940d050500b5809844107084c88020702c5110310154050f1001714a40403a140010b0032031084500192400601c1712000c2d41000c4006a84d60505615410140500c0d000d03034020b202a079000801d200d0092440d218032400039006001c0d01d524203142c0d0003482900e218a550b9000740d40710703180006041710301d00300c80c003800300f45c00800140985469000d010000d0411049a03c801603101c0351920180300890401130400c9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 311760647 1250 311759397 311759401
    0x3050d240b0408071e0918060605091902030a0e01051602070905060114070503090d030c02030f07030206090120101506020f03040b0f07171b03030408070f030c050303091005010501110a020603 84
    0x5036171188960000e10303400c54280456280d25044006499501c0b005a0f14035040ca9000700d01ca041860f0007600032004040748809000c90700020750000d400c007808c9007000ba0346031103103d0f6120200b4004c42c2e000d4050751495000001c06003038040d140120741d130f104009e00380c201030400085a8000802505400082503070700d507151194680316003144140085294000015640a0145076001c0040700d0103034425811180910a000e89030b564641d41440006e500a008002030705403548a4a40d0320340e9004042d12000089002d9001c5d181400800700ea02c840c0169121148070704008902041300003000d15001a01142001c1d5481ca900d074880c0c1d00400250481c0081c1481c030300c02001e403c496400d41c02c0941c43e03c81801003510600340d907000d04100130b003802083d0000d0111441c04002c4a028a0340070b8911480c1070400c0d1f0705d1500d60815040c05a05102a9458032800b068003403000394400c8440c00050700e44200710703040f0302c4200d42c2c040c4c101c541040f0398841045420040054120001501212007940703035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 311761897 1250 311760647 311760689
    0xe0c0d02101808030306041103091213030609080705010c110307030302210403030f0f02041212020f0d0e0a06211a0307080c0a1d0c0703050d240b040807 67
    0xb28000d40b09201d41d8180c0c4520008880c04044040c43c010001103c0501480c55107080c0481140002c0e030700902c6641050492010095241008201c040180c00004108903904e0700c5260444081003002d030b44c0c0c41c3e000600d40c01046020711404070340c6425414544010300f02d03251101e1b600e00031600001c042c10750000b00b080d0107400d40401300402075003d420001c054034044c0341c000d001d0f12602c9a0f03038501500340703804101603103424000d490a4a00701c03291240c4074003194858000300020240b10400b940a80c04810240d041d0030300c124503001d0300303035190a8088c8080c1d0301402511102c80e0700800400a02c03501d1802c00b242d04910482e40010074440220348580340c2011006244010701c6015418032440b0400500804081030804c0c6c0c0c0141229070842c0c450765199090340080d091498543c0b841c3c1490b00088258441c0c00180071824020b02d0024140040b903100c17581129007140011103405c01d10810000007494001401c0041d255071105641001e18041040f980c4040724000c200342d10403416007003624 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 311763147 1250 311761897 311761907
    0x3120201021b03070b090c0f011224180209010c0b06040b0604090c02121602090a0209040f0603140c01120b12010911150a0206010506090613031103010e0c0d0210 71
    0x9102c001510900c8803448411001d40c0d81d8451082110b900c070001000580300d10010a0400001402404102c08000b01000441d900305005c3c5170008003030366030607640901080025101c0701407103075140744110150074540450300305c1ca440c4c1e4880604a00421281200c0c0c1d905c04040c030703074442d400070608000c3e4840d01c0024000d0f240c1d00650316001007000c00c0004e402c0b5020b1704190840c03003854090b5040300ca110460b040c80c0d4426221030b1095204107882150050414040c050351043c900c060041c201150320001905039007044050f5a100b640f95541401841a000c810000f00005100105680c001c0500064008421179800c140300640c2d62104411a854040c84001403030581d00c02004031003254944051144001c4006500800800703039401d03481440c6004646103651950005e05843c0e00e480200401d41d8498007a941d00048184140b483c0c050700b441800c4e020b50720400714030b1403003003041050508503456014288800d600c105040348464807614440b4840a40650b00360342c1e03443c3c0e640d4041d90 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 311764397 1250 311763147 311763157
    0x3030503040501140703022502090105060309120a020a021018030b0606070501090c2c0109020f0403080c1c03181203090803010e060a05090f061e0a060804060f05100312020102 77
    0x203001504c1c0820004100d5065000f441740c160804903001c41403c3c034060454104101c00c000942141800005020300c0c0b4004000d0755202e64214112546400b00d40c0143c1c10031740000302008056800880003104500c3d0600320081404058a000e40d036507503441d900383d03000c8079007840098810082c5801154050710f42508980f121b5400a009100c1540c0c0740c40c0100b0504030314441c01d83c0c002d00b10b440da002c4001c021091111006484078000b800c690802d14040000d5000c1c00c903000410703408210020000d29543d02800d241d1020902418060170350701c800c0805600000028001c05240c0740101032001a28107615854680050303c062484800f11b034241c0081c20050409420000003000018907002614000ba101303010079505102600e030b940d018443c0c40481901c2540030244e0b5440010090b00300040d40c4003400814443c40d80f000e040c50390108040c0961500200c00280f480701c108028400c40340a0b61680485882042105140151003508802094000140b0401000d290340301c2052007501515 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 311765647 1250 311764397 311764421
    0x2502030f1204050f06070512220b04030207050a08030703050906040e040f030219030905010c0c03080d06260309061c0f0b0108240607020103140c03250903030503040501 74
    0x240d0701c21421018600c0000d084404644610035003018251444000c100070307010b2003032611005e040600f00c00800300c0d0804010002d810003010711030341e0806416101c1c85140181c0c000d5692510303a041504000b410f01400b500f029000348249641000030282c0081142e080c0c0d5050300d40243c54912140c001150b40c4615403051051741400824441403200385103800480911a808442444100d409035840f11034a010001c2e0201d4562041084a54050040060028466100403021b5134496490a0719504000301d1103903116510b82050100078200d0340c09000703160100c1074030f80c004c100c40e80301941c1d40c0c8240d400c1d10340190804140c000074504500e0317804911804222062120703840f084c2c0040010034540c00450300082c1a040030440d000c00407102d18408010703108403104840315100a100003076211120803030415582c2c0090b940c103081c0540700c0a010751914510309a9904017224110901c41206088a01d41503a004e013203026180c00001032000c580d494100799899981d80e0800320300412201d070002c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 311766897 1250 311765647 311765677
    0x50d0204170706110109020603010909020409020301050a0e0c060723100f020a030f18061a0607051c05130504180b1303090f030f14160e0a14250203 65
    0x241ca0500010030140190b444a07501d14408500d49410f4a00781c0d6a0303031001075004142000113125440c881c1c0c1001e4103150020b800030408440315170110b0f0071074000322500144541e4484d200c2c0d144010900c611034010348100c070080c2c280034054541c60204c209503558020180044250032116110030f100c540c0c20350741447c10800004c1d92102851010358051440750340028034201071114041a28030a410281031410025000e40c0d20545e41d0000600b10300060084041c02401c420246170f4030704000740360551140010f441080d82c0c014101240b0032907607003180140f0806010b41c0c81c1c0505000281c1c003c451f0211070104181c25002c0f02548400000034014040c00c0d403003030030003c4042c4200440c0d00900d00c81c0c0d850045941d0b5450b9821791102003408000d010311617040140780800c0f00381072140c1c0f1202d410002e0f030b41c1000c0c03002c401c00102c03100da501c44030611140004000300c181007403140e884000c2048044010602d040c68490241c000300d901300101144181c402415000d10820686403011204154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 311768147 1250 311766897 311766929
    0xb010806130e070b0403060c05032401051611040c03021213030c0c06020f1b060412141e0c2b0510020a09081603050307020108041703010902120601090b0a050d0204 72
    0x282044030745c054041518840e0070085190405031045013240e1092820320000030700c00c1d50010f03c4501c00340703110031201c3c1005020700c4414000b88040c004034509034443c04441901c4981c1c02d040c40f094074500f000480505105100c04503c49900000d0303a507004400040954240c011403074140c1e030080603001c01500051820b41d0219115800040e5034a0140c000d1317046071100903d0300c80170b01d0a0300c84201c0558101e401804104450076076040d0b12030109102d2000490f00844644150740342c44610b22a1601941c6090254990400c2c1484200028807055918110003110760281025020b024586107000d82800020001840740034016400f030388450090540d6100440c840090400c84140501c00f481c2c02030503c25001703081082101400c0700c1d44100618105040d580054410640083c0144c2c0c13141009100d240260f001c08005501a0a0400e00142c0360b4928021068007244001d080506010304450148401ca00c09010b0b6054940c061030003541e21100c0c10b8110303019024540c803d90082080d001c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 311769397 1250 311768147 311768159
    0xc030703081f032003010e0d080106080109110354030403050d1404090e070e0a020a0905300307120207180f02040e0a1d010b010806130e07 61
    0x1d07129000740b02425a60b0300890884110703041e038510522000302640c1c3c8420f4242078001d40c0c80c44400f060640100000381c00c20240210034100761000c80380b0000142c0001c014031520344c01280036805003d1b40e4104111018000000392102c0c80050032024004003e145c90f640c80c801c04480182021625007003895560104001c040c1304c032401500c54500042e01c00011816054001080e10110307504000104820085003c00759071003084524100c101c40d10821011984014500414842641800c02030140c5490850012800a0040e006170076180c01003055030419a4007074121001d40d42c04a0341010080c41080a1008186010b0075850000000384421161004080042c004650098070500304041c88224102d80b81c00e080c0c010f84d14450030803049182e02c07810690102002c01d404003001450592103140352040b00b03a04490b00301c0c08a440742c0c11074003c203090000914892000038024428110b0800029203c5c1600810290280c482c01c41d2035200017903141c200031003050054080c1e480040d1141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 311770647 1250 311769397 311769407
    0x60706090f06051501020a02060409150b040807090c0e011205071e02060a050a05040c0605030901020d02042402010e070b09060426010c0c021f02012702090906060a15050c030703 78
    0x1300c0081800d90315a264038031a500100300003843d198001c101c01d1420b81480d98000c02407401050185281c2041c800200e8403108030380c0104007a044200c0106000c0d460505c40c503041d0341c2d0850070501003061824240801c0d903001148015000c1c801500800e0320345d1400c404990012191441e041c1113000046110b4a954000c0756580c042d007110002032090341d8130524020142d510940d130081c041041d4200810810344200043d6803c402088005454904d00f010310780c2c00c0c0d810581081e0038600c000b0401ca2000200003100c0803601d68580028460901544a1151070358401c4c480e2155000c000501ca05d019a102000c0341d001c2c00560840040d0382110b406110f01e4000300c1d28112049600c1d1152030513445005002079440158002c1090000c89668044410140007494818084d992102c105405409201c20f011118440c409040c2a20380c80310700402402c041e02514901c2c640d0807060a0050359100c5001040590f000468011788403161600308031410300c92170b103030b10104c0d000101c5c00c5401c00d40e100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 311771897 1250 311770647 311770651
    0x1090c12031805061b1207060b0f043c0203070f08010f0302031209030a12110106060503010e2e09090c09020a1710030f0b0417030114060706090f0605 66
    0x3954980340b03102c180b074107460701144850207926403081007400b81e100b4046191500010074103a40341560800c00a1000c4404079410130074040310305586851220116041a400781d141d00c000031102400501c3e445410340c01c44000c1440b1070f003888401c0d40204800d010840440181c24010340b10115035034905044000c2201c5415580480011641ca0000a00d141d07540d144006903900103000d8111250800701c1440e80d07900285105825002e141c0015000c0b55610035205112501c54a46280c6590542003250031248650001d07400c0c440c1c00d00c014004488082d440b1a480310f11241c0603030f1110100b4100d02c000f040720007140050b6646500000c91380644940240503e180304030301c04080c0391f4446015070140d014180c401d230002900c41058080005e88022619003003c04130341e551001325120f446500e0b40c100014001e545121114090100700b2600c0c5046041500b40c101c0d0980c04c55041c000309408400c0402c810b503200d88000310320402849010740c800125a54807000000f00c02d04a440c010b4007030081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 311773147 1250 311771897 311771903
    0x9030307060b0103060501020307030207060e0103060503010e0a1407061e030e030f0720012709090614060102011122050907200d050702090a02090405040309030b01050f01080f0901090c12 82
    0x30b05c880043d6950001017541c81c0250701d500a0311185090400444440c450141010b04040c2c80e00e00c006001e4070284101c130001c1c81034601a2045520b9424125180d0003c143c14032965844000104682c44e8407005042d419440188403c42001801104401801c00785070180c425000019141e0310401d140d00080224034401c00c01412045580030358020014040f000341d0f40480e06008a4038181000c00d50a01c1c1c02007400c02e2060003a0343c039069020215100301c201210344503903c8400c54034141d0f034000320b070798060320904c02488010688814900d150180082e040d052803120341006c0d0604540050380d001400010b89403202c00e1504d842c0c020031015040e0b5a5800c0c00100d407824200c4880045040503100c0c0f41e98452070f19006040e428441604402003412044540c28806010707030b41da40e4094180114020b90380e0140351800c40c1000480144181d1040344150391820007082c071643c000340c80c20b0f40300d0b036292219229941c0b0300c14078a01400c40058020075181c021240031510208803c051030700680 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 311774397 1250 311773147 311773151
    0x81e180f0604031e0806061c180605161b0309150c032003031302040f02070305030f07020703050c0f0301150f08010b010503012603040f0801050403030509030304020f01030b030309030307060b0103 86
    0x103600c400520001444d512075000a40002c0000b2498140000145840804c002c412040c080c41c2148080480382d4010000140751100c1100d80148000d034051540c2100c1904030b40ca10041000c407010744102144a541e214a0303840c5d6400100389800f072091071004094032040000c4010560b40010960303d01c52104502040360130710f1050009150103c8020040082c2d402186941c0b61810744035035140d0710400c03c0f07170301c15200c0d034586150b42030030700280200b02d06c84d071030341c0d9100d00b4610b0100c802076034014010411944041000c00104000103032100c4102c60645801902041c0540802d015040d0348400544d40c90244500080254000c6162012500300900802800c0038110046645210a11406224800b14449411080c0a11421440300c2d410103044038906550350b00c0d0300f00040d0340c0e52b002c0d00f402d07550b9508020615416014542d03211400101030b41c6549400d50010b910302000c8914141050360712910140a51000c00032101a420000e08482d1560320f903241140160070701400c01070000f4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 311775647 1250 311774397 311774417
    0x2012f060f0a0b0a181104080c10170601030207060626010605010f0c0b07020106050a0f0513020f0720032b020607020307170d0908070c06081e180f060403 68
    0x10503610915080c0c9600134100c0b13407402d241000040d03001d0402a0040c81441c1d64040c00846851000c00410080400c0c2003d4103002d040d51040142401038401d2603030a010020300c0551f12032031400c800d00d90140c001d0070b00503103c00c0182000f00040181d5048000e040d52000c1280510040015052201362100e41c000e105441e12580110340301100146241c002c2030030240214001801005015030125141c400059040d40c1c64000400b0014181d00500014100c85810f0010b401d01c80e1100625005400c42549031845008812615204281000e844c44180c80c40c0484001514201d1003c0200002c0072285298200c02c00c040b52140d009403121200c0c41008081e1498500200d502c0d44190500d0300514180405611042030140d826200307505e120000308a6224159014807d407036001d40110f02c075640320700c80e40ca00403500b111107400c0803041c0604542040360ba4262003055043c07034205180202015100c0007010a460b0308070b81407124440c0034004e81481c0c10300c8005002c5201e68020b07643e03d6292 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 311776897 1250 311775647 311775661
    0x51006090c0c030309022403071107062007080706120506090f040b18060f0f0a05061e0a0902070602091003090309060f02031b03030105041a0303040302012f060f 71
    0xd40400380d540012440850703000d000f00c0d020b07500102c1c510f0b00180400d600850110f0301100c1400c08254600070005021062000300d55008085d1171160401c0d50080c0701d400d05144020f002d41d42e000952035101000d205813844450401d004c08402400d00c04203d0310b40d5030f103915001d044403101000102c2914581000a0060328200603080d0041d100807420b00c01d65100c68407201d8142c54000c01f24a058292803141500004003000414072540e02c1902440c0c40d0300b04a086010183c070040d1044400d80e041c071043c80907030f9031060320308480d003025059103c61036070b140c1d4003040242c0c2c02a4040d1001501c08038000c0140310f400d40003003000081c12107000301c044404c203105900300c3c1c52010001d000980d010006010450150403c2c4070605203a0040301c4c0bd05056540801a45081c81000b0055030004001002507041602a03080c49000400ca145034802d600401309544c0d024601c000b07070402c200030300c0511b01d440400d010503060003546190003030446c043d81d81065445a042d114003100c2c44900c4000303004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 311778147 1250 311776897 311776901
    0x29031501030206250c03031e02010509100e07091a15040608010302040903050c0303130b01061b17070f05010204030201170c092e030603170c100c0302070f05100609 72
    0x5a9a000b04114201482d21003882c20413082c424003407038003024000350314010030540030488000307500c80da581d00896840c00314010541400d00a65800396070504040c400c680401040d400d00c1c0381c40143d00012401002d035a00d503c0d2003255484800300d0342c034100b4020326034a001e0101114500342038610310107040b024030300c2404c144200d01c03d54001074081c000500044c0307016084125054000e1074200d042521001909065074400e0300c8400a900c05030004e18104415030340910b00501943c1080c040c0410f003020300d0021540d0380c1500a140041c1c401d081b01d0183c90308000c1e180001e802120b40c0e0042d09007864014003d6015000613408140210000c080310744422601c07038424509183c82c6801c03e20341109100c0d18000c01907401c0c8807046003608003100d100000204540f241d04940e004a50240f8504020360045004014000c890000304510121554000340802c2400050240024071040790341c0114001e00540c2c0d0b004004070400850101403220019440003440d0442c0010401039a5422000003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 311779397 1250 311778147 311778149
    0x4050f090604140c0424061d120a0b0708090c030d0c03050a0c0204020d0b13020309030a08100b0a090e070f080c0d0e0607081b09090103110429031501 66
    0x586074420030014000400881d22103a4035603503d401c940c800a0030100160941d08a0f10098400c500d40020005940c1c503e4445040203110b103080200e07480c80ca1100300590452200c0f0080c0c0207042e004412450000c1c100006a01d003500013018450030b00f030903480246000f2056840384c409100b145400511031401080c507100d125083c0d10b82401c0808560f80c10340e496000350314000148111005103402580b2203000501d140d4903440e900142d499524420040820381c2c403004240381c036105000b0490b00d10000001c0700c0310101c10f03045c00b6229030364020484150f40c2a58001080700c50012568242050300903005e201910702c1120002d0984e41ca20408031488915882c0c011f0004506a021410095a0000030301100d9240c0304081040d041030030205151500541c5c0c1900012010001c001c1c491182c010300028900e00703d50b40c02e190001c0302e00002d011810600000d0000b0380b56840144245c0e4495120140c820b00c0303240d541c410701c1802d1f14620314407130081ca860760180c05031070842640050701c150024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 311780647 1250 311779397 311779411
    0x5040e010b281502031315030e01050606030a200a09031101020307120e0301060f0b1201050a0f060e0d02030a030e0a2c090102040f08061f080303070309030e040e030904050f 76
    0x518694036000c3c50082c0510701000d1103007940802c2000041d40d1038a41da45101801800184c1070800c444018020120740000c0016216a49001e003440461b6892004580d0049101e00d00401d80d0020000d40d540040c0c4e1a483c41c0700d06820002e208880b050300660074408603409080e8403130089203a0307401640c59206d0100018a000035084003140b025001b00d12240d10302001070000555192150750214068009030066440f842006c074030f410010501481c0280901000d035050424070f03107892182d4024900ca0b018080a011041d59504801d4441d0341c0903590707140e0000d04581c24024a41000b424441c0c0003108140070303140c0035201140c4000424001c211030341200070745072a0146001c0b80b10b05080d1000c2c2516602e55002c10000400382134a412101c090441007001e0306013800c0056030002c002c59903e0205120700031045c02049034a0020081d03a0f44020a8100400e48817100c4c90115890342c40411511b030f200b0318014402d0301c00c0710004044c003520750707080d207080209484404030a890144100c5940c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 311781897 1250 311780647 311780719
    0x2041107050a1b0b0c0708010b010903020a060c06151508070807050706090f061104090e0a030f180e0c04030302010f0506030c1306032310050105030d110705040e010b 73
    0xd02e0000d00200c0021041c064000107074044503840d50000c024540c824206500540e100000910641c442031017100000c2e0003d00382a0301c80c03407843c1d0205031984d21501c514400d11401c5030005041c00002d40050343c90b580301c043c0107910507485200d540000000e6140390b80005855500080319903008034041c9000342542e0719540e080003055920300010304180038045070f40d4002c0541020006040740211100380841010081d240c40c1407000c1c510494aa0314080b9801d0390103615004007094000885988c51030152a010030700c1d05202030415101c0d40e00c3e511200040c40510200007400c0a07880140054a07c60303802440f2589503140f0341e01c2a91000d40d00960705400200c0c9404081c5404200407072403003241000440d056540352034000890110a5010900c0304501403aa0b01042d018441c0321104440170208200079414180441da696200f1803801090000f9403180321410301c000c010b5a0020b020003003052009c121503a140c0390207071088403440b5000b050100c03e800c0000138441841100c1c04841c480b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 311783147 1250 311781897 311781913
    0x6020610140f06040806100302030607020c012307020d030230040e090f1c0f08070210050903090303030103080706110a0f03150801090b07080a0b03190203280204110705 74
    0x70010003264200c100383d030101c0c007040001a62034090003807510902c554104565458a540145400c3c160001e05080454000d40d645020580c1c2040160b0100c1220000b0119003102d0440040e056101c0c0c180302a500c228036030040d83c10107074001441124070407042509100e40c0201c021302c030288000c441300522220000e10080c881166800309031680300340311200b11580c001c010f050322820810340280c2059884520258003000681010540c81c20000c00e1805950350329101c2030083d00d400301c94401d911020344a001140318000304005071440700c54002c060300c1e6a96520f15080e40315501a842c221180e50a00d0340c41d080e11511281950801ea0b882d032251000140812002c03802440c103600390280c8076a02c12404514000b0920074000401d12908510030136007441c140c09481c0800051403010400d081030200c04145d280800c04100900001210310411401440020f08250a420100c502c02040c40400f2800040340348110b01e81e64001c0d50204944540741ca44c0501c81c1c425400d01610507807002003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 311784397 1250 311783147 311783149
    0x30b060d020705120313051212040f0c0b0d15080a1e15060905040b060609010c02060304141914150103030806040902040e030c060915040201110c0a06090602061014 72
    0x2000090f104900755015490160903c18075500f0695404a4030a03880000b0010010100024400303001420006800c001059046848003035008000402c00000803400d04104080301510030042c00842218139240d00950002800030104410002e003c80038040001801c07882c007007112079010b9000140e136210b28650310070300c1c1c1d5a0001728800f00c408041a0703d2800d802e08491041001030400c2d07076004101401c16051450f001d82c00542070301d1081808004e80b28031a030300311a4044030b1302d0b8183c91b1b85071255501d05000c08060034610380c074030541c001c103800307101405e0100f150740d00c40c6480b0384030100c05490a10860342e6a680814072401c240840d41c8018008203000e00e0341254442c40c003d00101f4084160740c04141030f1801c4032066041039001040070500d44505000d1070358000c14901c000c010714000c0e044c41c5100c51101400c080e06224116421a21032102800341d80c00345580a04814111541c80714010440c200390312840300140606000b1501801241006004596040b825100c094105074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 311785647 1250 311784397 311784401
    0x301180f0b1312030b030105060405010503030316050d15180507080604110c0a0309090e1b06030402010c050604080a0908060702060705210109050906011508070c02010908100e0c01030b060d 83
    0x10b0614025010b00c0000480014107504000043d820700382c1d40480c0041c0418285420f441000e440584a24140001802907807800429603500224064a00c8080e10940324251042d01ca21600c0090705d44c1132041c1d1042c2001c84034401030803190b50403a00f44407042c6143c001404c42c2c80c29100c010004041e10023062492816070080c1c084581a00c145a103000c18112205152945e800d200303e000c074182941c204035004031489009002d184000240101c0c6909043d00d1079483c0d15000d5403031003000302201243c10b592140410440c0580d0010807a109400c080c24041c0c11070300580314480004140b0702c40462043c10108426004a29603002402241c480d00c030f0580c0c43c0d422600d030030712003600d0368001da56001c07412601e0f290082c9140318000a03107003030481040c0c0c02c02c1300503081035011b00388900e92411141d034407802841e84540586007102018403144012100102a50300120b940d00c03405104c04142800b65020010a80c90719044929a03001c07400198195910001c0207640803400780680d10b1030034078503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 311786897 1250 311785647 311785651
    0xe070803070c0e22060e0606012303070e0a0b0403170c0a0f081c0203060f030c010c06020d090f031e0e01120e010f110409150e041113020a0e0301180f0b 67
    0x7021905100c444c0c07142040039880c081c1401d480c900e03201c180200b2156400d100c1c1c0380d0000c0080c40c2036200100d0070314110300d01482e5117195030344500000002540440c03052001c2d46000c2c400902c0e1550710313a42c3e400d4000c11600f25000c00e6070680000b6901200b902d951408880c422046d82019000010f0aa202c5122480c29540c0554429404101c0340c204426001324014004080400044e01d81c2090300c06c3c01180400c01c07100300d00942c01f0411503080e81ea080027034150365947c441e001603581d842d0842002c0140940d4200148881400441c0c2c1e404c040d0040303854030302c0303c0704d8050b1002c00b112045400c4031304000c00c42c07001c0d01250340820300d508410b085800000c202d400760000403030814444e07500e0104450800e560640b9000010030240004c20960040114080c0c0000c04240d031036003030180c255202800500010100f40c102d4406041e941c07160003ca00c43c06004400440d122034407068064042c282500e0072034030a510b04103040c5110f400810003800010382052044a50080541d5004108000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 311788147 1250 311786897 311786911
    0x10804141006031a0c090d050f01020403030306050111280602091f0206011403120901031527061202060c070b0705010609061211010f0516060e070803070c0e 69
    0x3259001188000c00c1010700d00201d101e00095441d00c1c6050500381c1e041001c1c0d4004041d034085040c0200403406005490804004441da0401918589042c1d0b2900a0300464441c0365400440d0000a051b05580b004084480c01c0e21050b424484030035820751244001d5902c0f0a00400d01d4110100000c00c1180c9014800d00c90040103281ca03541c8000a14555000508a40c031039003042d1040034411b6041c043e0714010140c1d200c003807008140d44000291202c0c62481c5850003450081840310f01a03110350484030258004280d00c0c00e20607141c1c03800080c03500d615030340c1f50849010b8000082103420a4803604084400035082d00404e0360090382007120503404410007030f901d03216810f004a2145c401000421070b50344030b0303800001c1040c0b6040001c81691301c540d00c4080c01d44c0342c2c420603101080303503608140998102480c02d016030008400d402d690502954820003200030303c0c1d503078980411001d9846881c0c00312003e0119650503684503601a40c0303201e50040188280b29648040004003d211050303a00314007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 311789397 1250 311788147 311788163
    0x1050f030d03021803070315241401030617011d0d0e0f15030903030604140103021807020106120f02090109062916060c09060504151107030203010e0601060e0604030b0105010804 78
    0x82c04d50000c0e1030031501ea041501e00c0b9100c0c410001500190f0702c03039040710285d121540c5030b04c0e0001207a00c41101609101d410030b1000140781c030603c06e078440c0d8001c4010702400150400301650340c5443c1402402091003034010813807103007a454400070b000144034440d002d80303554606001c2d404205021401c081070154070780200001220f620306580c100080c0d1301c42c0c2d481000a540324a80b032410401512901ca4503030000d01c00d04d00c018005a1148240002d1244203452541d40c980c40d50304d012801444a6070044540b4690120704804005004408082d464000c0380c9244c031590b210102c40d002c0b644030b4802d0340b404001c0c0301e680000c00482c5c3c0040c10b141c1c0b002e1920150828080354011040c44040c0035044071129640c040c101c2e8044c0e001a11200641010314199003041c1c1045600da00d500c0030200820203000c0b00c03000d18a0000c04c1041880091680030b8024010326050f1005240d0303c4400303000304400b1480c0c2044030790650901074240e80490340c0040311810f03a6442c140043d10a03202c00390040c2c0b02c00c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 311790647 1250 311789397 311789437
    0x130b07051912090509040804050108040213151805090307020d050703060903030207200312070c030807050d110c03070e06061b030a092103030e07091e0501050f030d0302 74
    0x450920641d05501510b960001021440802000c00c5082d8014522965211060202242440080d00c050343c6003030800074a81c0e1154000600307424440c0084101c0c0a040c0b00d003204000c4031b9810b2440c00c84519081e4409180010b43c10581981c0003100e549030283e0017401680302505c4c0c08006003100038041c000b510089512500d070b40056502c11001640440d80010713403601008088d241401803030010403850307942d000140000a03114075000500001d5a8008960201840301002c00d40c4011640000516a10302031850001d480e12a08120f03e400308440c1d81c0800140780d0041820b1243d0107000703000c1c243c090f040084414074410041e0060703402000600142161104040030442d232181100c0c0250b0b10f4a15403480100200f0054211030000006c2400324054907030085c1e1150380301c5905040c0806c000204808440c502009a8020802c507030030044402c503070b12031413080c05c400320f14003d5060051f60f0f01d0b40c0c1440581c01201d40c02e240c040e03005101407421741e48a80d01820850324403030b203d06004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 311791897 1250 311790647 311790673
    0x51e0f0f0d050601091e090308182404020901061103070b071e090e0610080a0509011b08060307050114121807060e0a14030d051804020307030b0f06130b0705 69
    0xc2c0098204d11001036850201c0120160090709046d400300b40c001041c0304510302964000c10b04a400740c42100e00c1482d00f0301854481d0303c10f201c0308820355035800307101d40400140c5a84a0030b10340e00381c605030b000d45420000819a01c0c0b01304a044034042e00140250b01d80b4000c2e699041c0080c400904020811903034001e0303245141c14a40c41d1002503612507440d100500d0900c141d001301c1000c064640c500c91340020014840c041d07004030600f0741c0058441c5c030000b0140d90319010940035100030f6001c4030240c90200c06516141d600424058051003041d01107030b00303840e00c82c40103544481d00d540007007000740014800403124810640005034810034401c00c01c03025000070344569140107090b400c00b0012400c0b184600c281810819041c600501258525040751090300e80402d844500e101c02842c00c0000004691100040c1410250140312024004540e00d24188000500402187e800a40315090100706002d00707150510985220131005c8007901e01c01482d001150225504c0a682102d090007a481c2031056 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 311793147 1250 311791897 311791903
    0x609070e030c100509180709052b03050c0609010605060909060301090c081e0a0305121f14010e030c0a0620030a020f0d0c0812060d02040510051e0f0f0d05 68
    0x90b44c1c840548440ca024100280e0185d0341c15020113544048042085865208210701300301c2d002914040021b0007102e2030060f8488460200708040c1c2000340c460000c060f8808010910a01c3c804140c4000f6202e01620600343e515030f1042c2640160184010100740c03802c0986a40c01c503000400009000c60140e0b15061030119540c040e44641c8c000d60004420148040c42c00c4480c905c0300c0b030180c0300c1c1d0411a54007034040e0144d000b088540d140039000040c2004410458000d00c4100089070495465882440da04804034134103440d4005040141415650f013030000c1c040110b41001040f10106508003103003221820045030509260342d44030443c05480ca0b0b0103200800240380e440d03014100800405d0460b031720f8142c15102075410469240035000c0406d035450141c030142030301b6022003100c03034441000150784501c010f040a58030ac0d1400b001c3c483c0c0c5e00c54842d405400c4560988548140c031030441d0303400a01c070f2110401240c000b0300c0e100c0c070815181f4101c0b0b1108a2200c00400b0a00360b0021510391a103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 311794397 1250 311793147 311793169
    0x40506040e181b0f0111071205101a0a090513120324080c060a02070902031005041505090c04030b0606161506030506250315090e0303040c0504050609070e030c 70
    0x2290a282010010707142c00c0001c0124140d034400c0c280841081c015407041607075107d0910410401400701d03802101009024048506550505141409415400c007400340148100c030043d288a03818000c0d00245001060240c07034400c40a000c0b08441c00c8010b502d0318103000341c6044121080541e1410001c040444a01b101540051004c80310040d0a081c181c61b03a146c00200e0308020303c01e0005003c50080c03540d0002e43d4070207444c4401005a241c0d151840c0d9890b1080c4c00d0b40150358018100700003020340c500c1c40314162080344c50445400206440e4800002807901c40d5000c0503203d10000740019645050000c010401c818400c0f2034031130034401988580510100c2c809029420a881d02810010f01c81e0030040b003900b0200c48800d510f108040f41d010145040701c403d070081c040c1600d890171040c0100240c1c2c1200c004000c00d800600c90380f41c10340503e0b40c40350b10441c1c045920b1040c0d02404510760034580b052a128040190500c86240c03124a01540d042a024003007036031500c01c1c105a10184c0d161002541 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 311795647 1250 311794397 311794423
    0x1704030b0a060501081312180914070305150f0d08190210150e060f04020a0215090708030703080a090804060c020306160f140403210f05040506040e18 66
    0x3500d1801c1841245054403441d501c524100b146010502c02e1040d40c00210081640c1c1c01424002d14115041c810344607a5001603861a501040d244001442c00403904844400c3e07401400f014800d956903541601240c6c420b0306d551100d81c0100c1000b21240c14003c1d031085070300700002d180105010b01c540d0780900c1684000d000e2441e84000030040c1c0085a01009040040042d03600b040c8518140301c1b80da6454a40b0511806403d07520000119010343c688020180208801a0056507503030100031020755640c00c2d0700208030000d140040040e0260340301150342c1064030030203000786181c420503031401c45001c1005012261040c2e52100200000f0303000c800207100411003501d800d50018158010103003031000082c80c4400300070002c42880b40f8281d2203401e8005202803410320090b0416000e1a4030318a000ea83c0009000403500140820545194104000600340984c4c031a4003c4400c06001c03191801030784101a0040130034001400f062281c040e0340c0b54002d003a4400040340c4085d07100c40a1810001c11440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 311796897 1250 311795647 311795663
    0x1c0f0203010927110d030e280f0506030718180b04180209071b080c060609010b18061c2d06030305040504090f050f1c0e030c0d170403 59
    0x4103010f54641a19885400440c280040300806903114500c50350b00414240348034403110681d0004160140440d481500006044a0078900800b18040b1000c0341c0705003244000703450f941c800980300c94004940410364030301825440c1540c840e90320030341e080d080e0003c0d1400e80130510318010038800d00303421940030007200c0f440740450202c42c000b00384001c640f8851300314100722900207541c401584540700c2e1250400c84a10b0320100b06221451400c7c00702841010090111100054001d0841c80000311705004d03a400701c3c0c001c182c41c3d8ac0ca04407800684580071000d180307030700241c0461140d450100b0103400310000e00040f00d0a00e404200301030048482a211a00c540f42c20490460034005040000700d5424607084010800e403811610701404074021032150b5880b03540c03201d6842080240001c1c00000d4540c1c0507084070106144551500e440e01c0c01d000b441100c460b08000c500490318402d02e206880041c000c0d000e45a80c085074014007901c2c948018041d10000204484102441070800c02400150300802030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 311798147 1250 311796897 311796911
    0x3051510050a08041704080c09010503030a1209050a1205031008010b013204031401050a1b0e030a0b070302070201020f0102040303050a050711040c0e09060301111c0f02030109 77
    0x11400514162a0285008200c2034084088003a000012910350191a0420196981c0e9500d0301400c108540140340c000b140c0080340001d060310002519a4407460308541d00001d40c1c1e01ea0080c166207010764450704000890304407440c8512f19444e8025105140200c058448484813034480786000000102ca117400203000204100c81c0451054212014210342d27002030000118030000244ac880b45805007102d40c0750422200f10075099610344024140d0a8504841c0d1101e030740f800c0c0f100855958100011142d4213144c002614207466108083c0004095030300100841c016803400c171040c590f1450041d0f054400d1080c5003020903900c04105100b040035540250b61090f0f1351000a041141123001094680e005000910000b5045019642240c0b140d161094a840f5103040003c030092040e81d903550080e25103d100d03072041740c5c40010303480540c109440071f84860700c8103000c2c0341c2261b06000c1140101041440f40c1c4000420b10501090400070340c12010641c580c0c50304500d02207038400c3c1c1c0300fa84001d581c1d0301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 311799397 1250 311798147 311798161
    0x51c0611031e01081e0109061a090106050721020309040e06090d0206011511030409020304121103031303030b060c0715031b1407330e19020405040606030803070305 72
    0x242c01161903840c001c004070303a54941200182e481d072810210348003268080300b005204620951108260540092050000352051108521b441c5110b450041c01135050784000705003207000380c04681c5150780c060720301480c50303002c80c0354482240001580340e421408208541c9070386030380741c2c05402c2c0b86001e04d03000b030300c03403402c0036140c00c2e00d069181d40203007007075400840041141c003407660304403000c1500501b44881503050402c10740e070840c4030300c2d007040070400d2001c401d0000b801107916140a81d105540c46095194480b0021196203001c04c6442c0074104582807a110300090ac2070300441c8012401074a054281080c0d1a14541402100d030403054842d41b07134500105065034507000740b10341e0b460720028600e800301140000a003486080800400c844000152013000c200021081c100784480c0101690000b1090308114044d0f9250f28140041141c100b070108081105c0116042c0e0b12001001904c40503042241d0900c806000024070940e0515035079100000403805560046100e2607a680d00001c80e4641a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 311800647 1250 311799397 311799421
    0x304150b030c1e03160303050a02061005130c0302044209061b060606020d030e071d1905010612060f050d0b04140304090c0e0613051c061103 62
    0x10041e1199000341d4080496854440504100c10348840200710044403600119160a000c1d40440340c0c502a908400018194000f024081464441e42902c0c02d0b51035040c2c1c04024820940102684122000f811448000c010f134820a440500b82c1405070078a1303900c0004840703a10203400d11026012020010340d003100030317140580e94110401285200b4060103404001c108071721500480061040548806d0030954481c010303481116032010302404042d03100c100094031200000701000102c1e040007030450b1030860101d020000c0e2010513200040c4803868440b800000c44000e0030301800d0714038010b0b202a04540301e001d9a070180c5081d8588907070b8207a41d10341d150222140d560042c080b490b0444001d11441c0d481c46096075000d5003108a0304442d413502d0520240300507424640580c51300c00020005081c500580100d903155441e81c840c000c980d21150301384102032207000c104490769107a0080500540c07404503c41c05100c800d2020000e070b011004e58901c4101d41e10001c00382d0200402008001d1041c50f01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 311801897 1250 311800647 311800661
    0x50d020a06110711060f09040f0c0f0f020c0f0f0a06080105011103130e1f030c18060b0406140c0109030801050f0103180308070e0a0e0906090d050702130b06030415 72
    0x54146083c80c680c4482c2070a0403084050717440358000040d2003170080c100302c007500c1003210014000c12882d06808212002000e41c42c01c0ba002042c000f1883d2b07155a40908242942e0003e580c024000682481080000620b881c8130100da01100610301408a07498103032203003000c0c0c1070546071825a54103080015040100c52540c4800d660f000b00304e20505402111121012207000e6129420306403a100d04a00c5400c0c1800b100902042521a000050003592000714040b0340112a90b803000b101c0c102c8130503050b20b40b6805030090487c8104000c100315481024a4000382210748070550401c0c2c1e0403400c0a09568a020096000172420701c010300c85450440c0d01c150f984d0409003001c00c45889034607000d1011507081c2101905200c24400060903150003200011340c4803000400001c0c103141c88011b69a04c0c8842038a03800150310914001900c45400000d4a000c03050254a1740f5007000500c0c0c0c00c000303c40381141e00c201001500d80760180421b8a4400196000781c0c821103900101c0c29090510004807014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 311803147 1250 311801897 311801921
    0x303010f050d0309150c020607110f0102010911240c0703030e0907020a060f0e01020a021501050a060503010e0411121b060301050a0e0901092102011b05040603020c0a050d020a06 78
    0x12602e10380002a04107a81108440160407480401c0003842c0080c0c0780100c00900c0070303402150001d404800c010381c50321064a2060102c800c59403018668004900300c804d280700042c49242070041c585014a0b2159010144041d50b1030000b111204440c07040f40b460f000f00e40040c10940c4400418010150010202c03554100c003030314001807078a0400d10003917070340f680f004001d00349560322580300d40103103400d8101c080c0500081009640d91505200001d69901d0310303943c02c0a890b6400e600100f981d1a0100b041070443d0000c0d503842c0c0c210307400d0880210820102402c101c0301405c2e0058a14040e40390010b0300403000541201900c00e00701c3c82e03124204c90104010415100707040810044c08159176500009082e61181c105584003640c5003020103005140e143d42c050021140c1101c1c141c0304080030301900b07001d210150300070b1100280c1040305031141c0c1c0c64810050046441400300344800345c440c2d4090722098603500d084646c10641034072040d05109a80807030700c0043e00800b0040301444402c1c0200100041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 311804397 1250 311803147 311803159
    0x3110f0307030503010b07020312030925030203060103031b0b0c09090f010b040603090203031e031e09060a090614010602030c07170c01181d0708180c1c060e0303010f05 74
    0x1081d07940040151105000c0d064900704007168520175034400f0000d4141864004003480e540c0d041a42110782d80d01083c400c600007601c0c82c20f8160f040d078841803400d0011240d01400904599007590781c140d075010140c0d25100802c003660000d80300460011103146000b2030301d403001e0960ba10005801d104074010000d0040d12000040340041082e41c041500b100c049600d64500002c24010f03502c0000e0940c0b00f9075450100b40050005001c0104107000021800b0b02181b484446800341c20519401400e0340c1212064210340017480010f06e5a8a036420494100307120354400a070060f04d400118001c02000e8000c04010b0b4400b0500600c090000c00c8404041c1107403414550724080c140328030950b560501c11044d8104080303c0c1c0f03c445c03488070510300e10300030740651900079107001c5420b51002c55001c0704807021070004e11013a0211740001c001d41e170845c12074080c007805401c01850180911002030040400d050910059185e1500232600c9845600000d107100c10281d83c0d29450b003506402c50307013070603082540700300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 311805647 1250 311804397 311804407
    0x190f03020c071e030503040905060a06020a0b070503220b040b06042a0905030f011a0d021305220501020706061d0f190207050a0c0f1d060f0d03110f03 66
    0x400002d61804480c4440100b0a40ca82c80d22075949504566510007401d520002c81c000c6044003582e000700e4480c21040e10f0040a059030b60341e00b283d440f81e981c0005041d00501c04081044148110002d41e408220075180c83e10350700c05420362042441c0d034075500b0b403a03000e01103003403104110079113401c039030400811141030040001c2ca0401010001e40407400201c1c0802400440301c2280c0039a11090007810010180c0e20b0460b18101e0460181c00140380461750701c0c1600c20380640d18a812028801c400380c0140c08401d08000501462000f4600a005030b80b25000403041c110b1442c80480000f007909200b50000340c0c0b00c82091400006480c10703030704080c502030860300c6d25411185008074510303400741500000b107820340c4845810101d034001081c40084124000101f0000f40103000850781240c1348161005900c8655562100d03400385224000c40807011500c50880344503d0004140380d401200041c02080c8011046d000a0100d01c460300044000c2501d100c6e11803c402000d1040d51145103104015600d05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 311806897 1250 311805647 311805667
    0x506090108070617060a03020904301b11030d181a0307050d200711040b03030a03020c10150e0708090a140a1205030901060506040b040b09060c0102190f0302 69
    0x5aa40b1301c0b0b290350440b0b601c0700141c025901d82e84100015600039108070f00504060514445a00d1810040621540ca02c041560345000d0034416509943d416612929511310400840c185444130000654500844110a50031031398240301c1e42202441c103440b514410300c00c4006a030410fa44652094200e2460707000b1000003440183c00310382c0d0198031803074020760302d503580720400000744507080140d0400c2a00d20440c0351a1600c90f8014000c0038003941c0954400001501048140d84004101c140c00d60402c0c4240201c16009802030700c080007034001a95680340ca10800d1008032549007000060f1100c40800812004404480140d0010307024a00601d0625001003c1c1c2e55400348030000070706014043c80d00c020007140602c4840d0b003031039010000400056501c400217040c3d23002940c00b08155442c0c01c00004081c0b601e80100e0b030881d00f031401d90070b04240c43d1540b09005504109101c03a000344041004405d501400c0c401010500c030301e000d42e40340346801c0190042280d0030307e640c2ea10915204008420403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 311808147 1250 311806897 311806907
    0x70602031606180c09021209010b0a0302130b120106060806030328091d0601020c1804080a0504030507080303100f120b0408090a0914090102030103210c140105060901080706 76
    0x749801460200b0421000443c1000a40c06004054952401c440700400d40c6030321600106007010ba0510701101c0c40d125000c900e422214201e188562118880d0300410042c1842c44078892030550085001904d038011501260440d502032060307521a035543e0324103205803904200c00c150000010b90045080000f00d080030421100e029540200311540c0c1d400340031311203105852040140c01030011f005580b501100100841041c19035000740035003e0b6a544201c00d045c82580801c10780707408800b00155448940342c032142d43d481a0300301310400104100100200d4030420081c00141040d000841d0349107055401d42040d55159006103054009001b0704200655454801e01100341d00134504210716181c3d07203042c02080c864ad0700c4064016520a5000842d13410f180e000080480e55405140181c0e40e130500c50601704d22007400001c01e0050b000380201d010202d81d864400b46814141015080c828407910b4449203c00b8941107240030760344840c200540e5042008a440c01020b10341c00414405040c02c0c400b5013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 311809397 1250 311808147 311808187
    0x9090103061802041a0310021c020705011d150108010b0a05060d140c0702030f0a050d0c051005040b070e0f010f0c030507140a0b0c0712050a02030c0d0203090307060203 74
    0x40000e803900b500d5069940510301d00c030520303a03004000704120b070106180c0300c0c0c0034840203d000303200f0b00030310391800c2c4600400d0003110716507405906407a0286156484031070082d0041e031025904d640daa07802e22039007042c158010702240343c0c00c50010080c0d1b401d01c40c540401c0842c141c026000c1039041c0f07488d824654540034070a00c103136041100c81329110803081d10100001c1c040f65694581c001e4407072003070000210b4000005c2955500a50660b05041018074086a80d03500c035000080059004085103c202449003181c1c10104c1d21840544010604441c0400203892040e0b50554401c0c44c2202484141c5401030607040c10480103540e052a401000310001c2d100c001454024414000f030141d404080501c2071302100c085590203070544064000d0040c00541d0781900300400c694460741400411913803043c2c42c06640103503920442403002441441d0080742c241d0005500ba00940c40240b04100d0340c0d443c03d0151888000f4a42d0007103403954045020185000350b5540503205540040013040c0724031000d800400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 311810647 1250 311809397 311809403
    0x30210020c0a03030f030e03070b06041e0c0201020a0914030607050d06170c0301060f12151112060a120506060607020d241109010f0806010504081e1209090103 70
    0x18544128045050341404035055034142c1c4030400a501004054000c000e404030150165400c0044e2a20b00020725500c1c4135800000e42482107203000680c5620781908101000903a0301602d50002c1414084042034038413941200015035008181041c076130b0f502510003001007480c41070b000c00d0100303c0000700f9100d03000900340104200e00050540705000c0c0c1c540040c002401003002d852948980c00b500e035138480302840c034124480d508042d00011000740100e142d100b41d604140c0c4009011240d40c1e680100141f284100500301c9450340b01001c03103c0c07407800140c03084007001c2d082c03228a0702d481002c0002d03c4426400503044424141c1c81c01011900004003a5404681074503020350303c10b01400012502418000010900414411403020744001207101e002d84410031b40040c0020508440071075400e0003040c18a0b40080c444c2500596424800d840a07901b000b810304205141c561a2040c40742003c3c0254045c5d075030603600700090b07103c00c00e0801900b040450303480d40050406640d41c1c0000c89800043c4005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 311811897 1250 311810647 311810659
    0x706050702010b1503100807030c090e07050901150e030613060905030f0417010c0c0305070308101a211302061c02040905010305190c05060f09040501080606031b06040302 75
    0x16084900075808601e000c40c00410707001949000c1420141541c5c01140c0301207200202140019004000080490a072030344103040d5015142001e02e484010004d044104225220b8480005850f07100c506c42e040c0604162410441d03211402c10700680603030504030420b8000d6011808001070900b031588031054680d80500d000c10720303603451b041481c5036024520a4115000d00040e0001c0c500c0c030a0840a1b881c2c0000030000d00100c6103a0b901900d012503d9440500490302c00c100d800c3c0004c1c40b43ca006039010794110000c0d911140c0341ca00d4400000d285030408101500c00155018070303607402c410391040c030340300c450240902072500c2c1801c815090714100d0002e0040b40013165070388002400c3c0450b8201609a00c3e011501d450341c601070007028000030310043e2080d01946104c1500d0010207140c00c22019042140c204041380362005006e0281d10800c0c1e0300c440d43c901070000886980e15409414000c01c00c9000400c030b40d00300b0008142c10810681150300c030105c0c400240012545a101c00e41c5e00b1a5011111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 311813147 1250 311811897 311811901
    0x5090d14010212372f0406090f0b120402060f0d0c0f050a0806100e181509070906031e0c020d11070e06040b0f031603110d0206070605 59
    0x304444411000600512650022503407242c060b6000400d0b5104400c6942402221651914500610405807000410884043c0e0f01401d814859800031000300303403c42000410310085600b0400501d5640400f1128200002010400b6aa20480080150141d0281202410b240c044800140e1041d41c0303c14402d0054040080c0c15941c400e0700391014070f080a0001c9550760448400d68009059000340c01010031034a08000c01058030440c203075045415a43c803005181d80f0307203d0811441b48403148640040200c4440f1041300340d00c81034145156207034144003000f402e0a004903034800c0c4200d84c40e0464004c078109030420144030f61010040040b03403141d08000030000c103803443d01e001820901009500d92428800c021007181d60020314142c00004903a911880180c0e0341c10f01b940c40d02014030403461b50311411000f194452800da40320118680000303101b1001c0f036410201090504c2240c90800c0b4440d00440c4080040c4801003501d0003040101311040e0290519583c0080d81038022528094011507031100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 311814397 1250 311813147 311813153
    0xc161509020a09051e093a031b0c021503040609060c0509040c02071a0c07330f12091704120303060e01261f0c0219020105090d 56
    0x40051400d039000750103041042c2e01c9003515009801c0c140c0e101c0604228104103400d004030031040c1103000d1030302100900b80042642108240045104c070b844103081e00403401882c403400903240c0014900041da200460010000e01317180c0d0741d102085000c14203104100000b0001603840c1000e0400301890b0180c0e13035031a0344a034142040202032551005281c00e00d8034060403001c503002000303480000781c01c80c0c0c140208585d11508a072610450701c00c5000c07600103243c0506008060030094204a0141c00c03c40310081d56030040b0001400510448601d40366099154080c400007c1c0301c1ca210072151400c2400d000303090176800034040904410609070050ba1a400c01c8100000a204040c0c204110207105407104d882d440307001810300b1b0621044001c2840c1238400103107401000c0c041c0d81200c212221144140040b444940c0740a003c07407035840100e006400c0440001403911130304035040314442030000340b8252058400392414094550808055007104e0310040143c1e407203021038000000c181c400c5110f60403103103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 311815647 1250 311814397 311814401
    0x100f020307051002090316030c060c02062808160f1b12030506010e04050c07020105071e0b16051303110114030a0504050607090e040f0f0f03080a050c1615 68
    0x340c0300410b14020b4444203180000c8503006801101012015210504900541c9060341a0544001080150715140070014180101d441e400c80c107001500c2c06140841141050190410b24102c540544488024540610394420005940085034440f0212a200e003680d004e0100c4103101c02040412483c04441403100b00c104d4a800e03043c507400241da0064050390b15018003e0078045030180e0005500d0440d020381c41c40c02d070085c1400341206008561a101c143e07001190107030704c05d4800f6a01076509506800c55802103209d200e1019000d05095061402c01030340450611503c0c200d4902005024044083c070707100d1100c440c0040b01c0d030001c00081e02044240c0142c0350016000140e4080302c20100c2000310680070360704028031540c46a400d0b9455691001c00030340d04000f181c001c1068400603440000c0014082c8201880d40900500310440c09804580d110189509906411400203803d4000d11078a5101030185680000000c2c84082c184080750300d8045d4034006854000d02511820303414011035188036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 311816897 1250 311815647 311815657
    0x803070807050f03011e0b120f1608150604081002070b061e010c051e0a020307060813080309010902060403140c031c0804080f0307180503010b0d060b0414070c0c14100f0203 76
    0x1f50320840c4c958184411003181114101d8000c110365001c04c0001d0010a0305101e001d9070b1004685034070609890b500100400503226440c4660010f0b400c010206154804000d007161441100002503603401d09882e04142039000645000d015006d8100549005100ba48104103641d10038078208208200390f09020349805011804200e0000c4006000b00b106180811440e135503a00079012074462541d40c0104482d03203a02210303a20b070b056210880c0d03e800280000000c540080b41100045001c212540008103182c1c860f5004a81900020310340c2c4c40551030622003403141640c110050a00710802e06888614034010b000e00004220701c0b100054108401d107010703a0380f01007901c807165840745070000d40580840b1a100c0100104d03000c040300002d05217414020205458030141c0859407030302c6d403655060040d100c641d03051070340240c6407104030201d840310180c440e10030001c41e6035907180b0255170308007005180b5440d0020403005070b1011a84400d512440b605034466002d910300b01000b4084044124218054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 311818147 1250 311816897 311816909
    0xf0703020a2a051e061801060b0a0906120507051902010e010603080309070f080a0809060d1103180307050d0804031b03090612050417130b04030803070807050f03011e 73
    0x1801c110b004202031842d60261562288007111200400a0080c0102c1d01134007041c603100340c2c000b000040d10500f50044a504107a440b10020400c10307240c0004280541040702e8400000e8090310080001e16440303060300d860800d84000c200300608000b10010a244588205410b12890030240c0c10f440314402d612500820048400800501d40c4a2504020950098404078058400c464021610143c005019002c0b242210001d107160907281c0d503507030f0075904180007003948a1010720401ea12140e00b40942c4213840c1a0f5100283d40b440c002340701031202a02a040c1c0c500c030758014080080013950014407460000c106051494182da52481c1c11504c80c040d45000c000400200c0e1640300815420809000a940c41503c0b1410445400c00001044407011139000d0500e00100a00c00c140c140c00000414000d10b84104415a450b1220003c6c080b541c401da20896a0329000820402107030b50103040c241c1c0000d02460282e01d02502116680054001801205041c4c40140c0c51f00300d4160300341d985080103210f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 311819397 1250 311818147 311818187
    0x31508010e0703050d0837050a062d050d0f050a030201150e0403020a06051503012906040506041a0702100f110309030d030f0603061401080c090f0703020a 68
    0x118110341c1520780015120841d1a8854090740c901c0d032a0183c40780c00d10803401a031106810b039154503081c413600000368a40d0340c1015041d04030b212081001e40030b1103116a1074032502095144c6003283c941e1003402c140d030140703450950301c00c4011807100424004108070348048030041d40c06901030500d0007074503205d403500030094881d0359a081c1c201034064010a402415017034800303c2e5207598600b01558850215002401604075014090001d0400d52100790001ea0820b00f0360340f04007840300801e08442c02841400101c4942d05001440100083c501e8080480d00351011400d041c6824003168260050740208280d605901213450825410107098945840d001400d9104030441c958014041d41c180b0b01c44280040c1c3c0c400c0b01582e40840000c211201607202030018849410402c0040380100b92a00821041c1a264900000401c07000c0c012075241c0700707040310702c0c2d03046500d00703081e01d4a401c04a00b072290251100030200001c15030010101540300d81103080242c0d6490020a04071440100503100680d020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 311820647 1250 311819397 311819411
    0x70215040c1e0303080603011a040905010f05191112061003020f070f0b09011e150512030406110c010207090506010512011e06020f03031b1606050609010506091003150801 75
    0x45000c2c45000101c034041c2d1a0720019850310030034113098030218501081c4c010103000380c0050742d06190740141c409a0048000064491490602d0b00c160381058032860b511154111680d0500185480340c2a601849040f60502d000740400f107454003000002e00e054031480300c4a1161100038000d40455031a0180c0c1000540d590750286440022548900400e40b202d4003001c00248030103070140300e041100d07050f4440b04410080c582c0001c101902e5402189030341c12000c280005240c1c4c80f40c8001c5001004498080c544890400f1030040c032101386c803820400158491403103449180d801080700c4042d201c0850000c9840d41d50600183c405129040082d034600b0002400051800e00d1503410101c1d41003d01204841d2a40e100740880e03890b03007900034501c2140c01c200b002c0341990162a411076440c2d80d0302a111420210284402400399083c088162041510f035001c01245180c1039040c00d01411013118410705001c400310100742c0c8010300c03136028024182d8811410168401e807000d110001c0c03000c00000d05c404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 311821897 1250 311820647 311820689
    0x1b0b070903030e09040309031401090c1805060d0c1206020903030d0c031803080c0c070e0a020901090f03150b04020c0a290903030708130c140901060503070215040c 72
    0x200c00e84402d6002031031000c81d003070003458140083c0d4041c0707800d035841415450540c0c1316098072080a0100308074640d42d5085d03e000046101e58140c00070301c44280b24903072801c20040c050056a00c000d1005100b0740c0d00b030320706600250006103c00240c410721140c0328903d10310b91030250020311400b017210b03a0510000c6403400076445d003034001d10340103440da0307405005a0700c04064102d44111702e010003d02090a0800180c04204018054841101000116240c3c595251101d00d0200000d0321100425500018195160b5800c100070070020807021040340c81417031640d12010b900107002e42090700c4060326a0f021022540d02c03038066950448209003901c0b801c0907245003e0400701941140710000381d040c62180d52042070a40082e078455510307900914590340c0d9015007124034a000404840b110482e5000f60f10101d0b00180c07c050280842000344031075500610200806010140d000da0200702c030800400c419503a0100d9032001e101c000000034900c58449161060b00c0f000d15070030880e0580f1030036007030f2411 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 311823147 1250 311821897 311821907
    0x10121209080105011202060904020f040308070507050f0d15110406020a060f060605070f153e09010e010e030109050106170d0507020d2303030603010b0a12031b0b07 72
    0x814446445400e045507848600600f40c4400b44115200d54403103200c1c18025040402c01004031000080c401480c00e02a4842d02c40c4c01d030001e8105841820300800c0d141c0401c402002080042d050403905409103440180c00111124200d0f0380085c8103d402903000d0030984000c0d000a0001c05650615944454a44500940d01c0b81412410703139880d03003003224a09180d1a0f40c4603601c00c1c0c60980e941c16190040311b03220380f04051103125048030001441144034902d41da05101344000d90310039458501081307030120415810031803484c1c818081d041d00c2c50b149030341d1032544070304549180d5400c1c00c2412468070801c00584a0741c041c00c1d036844d050f500785046c00c0d041280660280c0c0985d004003404d0808907420403841e640e110245500a00800c1c1300b084100007501d02030407904070300740c42020103652040d040300c02d8a0f0907801d1104180b000364008814020540340a0080301807000040d40c1d00e48403545000c10788610841d0b64407010b0f09002004c0c140c8591103080700340300d0306031716001401c560090500c403c1c0102 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 311824397 1250 311823147 311823173
    0xe0f0601060206190513020103091e0503040501120b012001090b0c0c060903030103050703060f020f0a0206060109170303040f11090112050c01050316120615180801050609040305031012 81
    0x240c0300d240138116410110b4802d45000f011300300110034132501c890b4010b40050100782c2080d942c200c50020001028082c4040f021362a070710580185854504c2c01002429140c0e02d5140195082e00780140e102d4540d038030118510b0031035030307a107001510921403181a60051200c0080a070003042c0d808208240e100040c0e004088010f402c00845506986103103516403203000078080101103402410b41000030900942111111403401c070300040c64014400d10860715a032113200a10050382180017005819030700005c05d400100403070440120100850707a12591240f0004000500f01340e041c91424040c02840708020380c1805d0050b084c590740f540c480303131289581c02c1000c8080343d0394800e60020019035441102607a004400d00003030a2030400038144291800c241a5221004007580c075480014844020065160f480405403521810f6030b107503080301c0911150341e0f004140b09a0500b410301c078030358480c524059441754051800039203944610380e4807408145940d020783c4901d14403a00340000e012170440c0c1e1071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 311825647 1250 311824397 311824411
    0x230108070501050c250e0f0f07090f03140c041e1a010c300302090a0803120c070f0204020301060e010807020106060e22110a020d020a150e0f0601060206 67
    0x61210395031a4011503191080b58014209500809280e115042c120120703000f11180c41d018a00041341c0700c0c0008180d13040100c980d01c189038405000e00140c2810001c49a03040882413070803142140c01c0c5540301c68100c8442c40002d04200c045025011940c0f0280700c1405d40b10801001400059a5110b1401c9140d44c81454590814540519401807180940402c030034290b06840d40c0c0e101451584410107031a0045100341d002c1041d00041c50710074241902c06040342e1455490041c0c55080c0c10f000d105081c05287c20400855100300501d00854802d42d005030340c001401041e840e96616107190a4043c400b100100940081c00070001040041e004019004003480a0707030345208075a6080c40c101d090300c20704e1044c070f00403c545290000c51420b10200b1801044000d40d2902041054801c000b400c0750ba804001112003a030200340c2d00c3e0310b140d06010210a184185c4003c00002003241c0310f01c84ea07010101300c1680a1360380e41c0d2501031220b03018000001c601400d03005032000f0b580d450b08040d4860394229901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 311826897 1250 311825647 311825653
    0x510020f07080a0f02101704140d0c15110f0406020102030f0601230c0a02060c0607110d08060f04110d05060108160e090601020307170d1104140f04230108 68
    0x22842d00301c00205800c585400100b154000d2050340c0900c0101c00f080c203245020440190000180301084400d0325001d544191580401003120381d40e40340c200400e4003119000c02c144000d444000c0b490410500328100040c00d0001821400c20408030300c1446050130140f0040800714002403000d4065002c0c6200704407111140e00c40790346031001142c0101702d40800c61096100c46c0010602503601c007014150781d81000085581c035103801e40028a0b181c0001341c0c07001e00c0d94420410419081c4d400501100041d840c0c400a2121007218200030345100c0000304502d01030f180300c0c81d0001c410307039480d040281c0740300315683c0d19a92904920800005000300300c4145010031440c2002ca16044d81c0c501c0d0210170a0301645c1c0b484080702c040c108110701c0d40310141c48103046100902050010682c407450249216669600c1907a6a15080c140402502e041c800d034440404000d00c030130407282000020348404000111a98180b09450704000380c005c05050481038264644480c0804a08080c00324107410b823a001001c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 311828147 1250 311826897 311826899
    0x2202030405070609180f0f09050c04060b0903100c021e010212010812160c0f0807090e070e1503070801020d0b0102070f030203030f2b090317010b1903060510020f07 72
    0x801e550100c80c0c2d00c20800408038045c0040b038400c1851780000c4041e444060f0200360350003080d08513416100c08280036215504000129019031400b841048001d0000b40c107894200521034000a48601ca032074422401c240d110000303101d03c1071003404040060480400740580d80b15a142849000350445c5480070100c0d0140000030803115000180c5101c1d840d00740245a20b4030040190075142d000f0031400c2219a0100c0c10b00100300c0194904a0901822440c0000c0003501d1400040409a8510b0f030021942500701040502010381c250b010a60310040400044180c84116004a442c00c6d81680c0011225403001c1980242c0230807070b4000003004102642140c845a80b40c0390303040010002880001e62543c402c03c1591050302ea124090301080d170000350789440c6116034148020300c06841c40d052844c001d980e03d01084c10107411100340d00c001c4c000600c0400c010760404609402612403080050040d00030855400000c602c80d42202024001c05001035002450007500170b03540b802c1c4020240f047d40141c0d50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 311829397 1250 311828147 311828159
    0x3070b15030c0d0206041e030212010504051002090d08091f0f0905010305090c09070c08040902251112190c0e07050a051c0b030d120e0327220203040507 67
    0x20010160300106076034501807070301f10008241c50700360107941440007800c00d00001681c0d5a5000c3c01c074142c5220b001090b946070919040b41416000000055998814031019510b030f2144180b08408551000701e8940e100c2c10f840c0003c000c600084030a80c4442c4054041915490f44a50340c2190149207403114103416031104015400d803201180d0300c120710b0340105843d6445141200c48241c004100381018241c500f055152409154841d800012107a80c0000f600d01050340114111080700b007071110041103284c42691201c01d48009004e01c0ca10aa0050020181ca603000784801542e0200000000700340c010145002c104a1002d403090004098040000484803802001141c018054a0303590500d40002d00e021049243c0c0001c044481c02a540d103420029034400f0400301007049505e03101c1801e0b21083e03040c0390f41500c014810080040d00180210000c00100e80b6198001c1402540c600c10100c00d8100854000401e8041081131f0004103c1404168101070740214002c601810a071600c06803115 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 311830647 1250 311829397 311829409
    0xb090c040c0e01020a12090b0d05100b0c06070c020a0b07030c150e0733030e0c0604050d0201030e15040f030e030a080304060f0b1003150801050f01030b0903070b15030c 74
    0x602414050717004000800b00140010024082004003420240812611912440c145070890720900c1200c664138018054007680f03e0680100a003200004030b0315000345500d0580d210038000d0010b00c1440070000c1b62008645d10880528090326004040b81c4d1a215942001403480da590311040d0f59001103400000f080400600600303042c080c1c1c881c000d2800b145044140000258500142c6d1446145090720800040140d0b9015082c1c0f030b00360b6804503203d4040c04805052504004070a0300c40d16040004200c2d41c2c5401d40010503403602424001404001a100c1c1428203280841c0451001c81403400c2008021540002c2c00c0251b0080d81e0f407255103080c0710245550360300b9007032002d032104200348000707000100180c01c01b5000400c00c542c041100c50621000c030304100310b6160117001080e11000e01040703101c88402848014402a0300901a90134043c4912607090410f00000d0110181c007400201e45840c00c0049800c03195002d031400d00c1d0b40c6044110700c94891074000c8078500c01e01035203d1200c007500d450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 311831897 1250 311830647 311830667
    0x11205011d0406090506071d01021b040207060b030d020307031d0d0b060409020901080d11010b06090d08040b040608010906060f020c0108100324060602030315060a0c0b090c040c 78
    0x1c00424502031103040d440101d00e1900030012680d040d1183d040034001141884428091100783d1108914008561104100032000c0ca45a904640c40035504036101d0b980d00b1180c100da000140c40042c0c3e103500e50305001300034124160105070144a1030715064203080e80000140b200c01c5c002d58030014001040c840b500b08007035040402661284138204000e0106404590b2641c0000b4000c0000601070060744c00300c0c4030410241e02c54103070740e002284502c0000343c000c400d406040c1c0c13160000708454034201e00041c00d02d02074207100740d010703000004100041068a4080368090420301181c180c42c2c6649090007800841d0900035000e07214285000021038600607244960194020740145c112506940011980090300900307920312600b0f10800040420030401c01c003c001680840807a040c50805540201500c0069000720115402042044619508190301c9100c2c214201c4e0084e5648215000440b42c0310b0900304050078982002042c440e2900e8001440421f280d000c1e5018081d6900038a4240e400d0450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 311833147 1250 311831897 311831909
    0xf09040e0a080904020a0509030a060f0f200d200a03060617060405100b04030503090a06020d0909050702070f1d0109060f09150902030c040608251107031e0201120501 73
    0x1401510440d1500d45c0181c40e800c80740e840c1540c00e1101c00c0c0b0009180160010080d0b030b50030759803001030b6880015402130886c60054050103014542c603484c951249900e65020a44d5080e401240e6034882d8803581c0c000c100c0800c9c00c11300e100004989440c0c0e4070340c42d174011a42070340441d2400f00d0001e00c2c4d83c0540c0051041140901c40c1c60501d580300002d100250030020652000001948404a0040b00c4030b4060000b450184004503281e148036401d0102145140c0c205109560190510405603070b442598842039504403840407416458180091786803200c1500028035134000301c00042040e46c1c08041400e5281407009a5540c184d03640c56150781128800d0042c55110441c409050000f407034140c11495440700c48680029000c4d41d10f480400490304282c92420f5500000113040080b154050402d94024501c0400000f880e101c1d4041c8141042c0e1000d2034109020b654800800f046c0404e100076002140c019000315240101030300d1140074000c40b03600882c00b01d401000d4150340c4040e14031030603040e141 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 311834397 1250 311833147 311833163
    0x207030c09020307021c0f143f070c06140f07030c020a050106030f140105250e0a0807172107021306090605090105030d0f0f0903080f09040e0a 63
    0xc1018030900103035000a044d0402c1d07200d900c500720100e5442561080140c042c2e503541c0c101c1074040d02e00080c40060402c02038032600e40c0030710040c0c018804a44583c0c0100c5281c038608d01e1070240e00180525000103150883d1145040c250802c407642c1d03003201c03100c604030313206d0502008030503203456141203461801c4e216841007088000009003000e010340c0c000e624000c0b00380119007031506150340b91420750f11180c0081b2008251050b82d001040300741c025500048401e0f078002d100c07610b8460207001c4560303201c4e62503110007002000c1540c5041d0003012044400031001c0d10030301003191540d0505980360260f102e4000026142012041c0100001c9099216040c4519940c022844107000007640d0380c000f0700046c0d071b010800c0040340c1a1700440b44545801450044070110f01c42c3d1400b4104420701d80305a004a019400010100b2000c941c400700030003891502d410b10980420001800711142403254100a2901100150768001041c514024144a0034116000d0000c5450600d200b610f440341558000c0002c0c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 311835647 1250 311834397 311834399
    0x117040b010528090207110102060c030f06060705060f09210d0504030306170a0203010b0103050c03060d08040503030c0c040e030a0918271b0f0302011b0602070c150207030c 76
    0x218103841014005203500302000d4814940f020304140ba01255484110310030343c009520020003000036890f992440703003400a00054942240c1c0c0748114400202061480a40080028a2662000181c68940d50840c044580a1505039810100f5042c00d9910b40740c240310361700e2082c044c10655200d07031100d0062481c02505004c140302d8a1005040083e00031014161107002c0414501c83d1210a50344a070b0107070001f03041ca00c0e4140181421110801c0e40681050b08240401ca05070941008580d04840c064615800d0030030b00e03040000f080c1c000c540103641e2500002402d0086205c001422120344c01003141c0800900c0042007045a82c2c0c41103031034080210301c13103180070891620b03000c82801192584490210b143d000c1e54040700e40200c44036032120025140c1d84151070034421540c10b55105c907510301340900a501c1c00c00c0300c200f040300132031301c0028100168403003001d290104442c2141681030f84180d0540d21a01a8a026a01c452503402014a0075019904103c0e03510b100280350744c2101d4002048040305 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 311836897 1250 311835647 311835649
    0xc0406050f0405120d090b030f150f13060305010e010e2802100c061803051e16050a12031b0e030a02030a1110050c03091c0b0a020301050117040b0105 66
    0x59004548240403a6078244070015068075254000b0440c500f509014001d201040e90000e0b0030803455401495525406008000405251448185d08145c91100d00428580d42000180d00c3c0300b0641c586179000040c080007044081c03141c0d04008241ca12131002444605010f0520b1070880e5840201809240d0003289684d03c00100384254a542e0b030303e030341110303007013914160089947c0350b507050b640e480080c0c12210b40e02c2c02e000310f074443c03080f90500c00c00d205803130b018854400030621300405000c0c8250300322a07625030841d0321071301e0304451242081260303e440c95406403d0031512400300c460700340c1c2c4056401c21003594052280c8100300311030b03010803088a50b81c0e00d0920120342da0356401c40c02d207803d407080c002c003240903950130003000c3d00051241e030807002841c900c0303410700048020b451424004e101e0b042c04194014200401a9600890280c503600c0354400500006010711900e03100c0034084040600038800c43c07040d550010750580c0c0080e2036038084510078581ca0359400c06c0c01c54002c0e060102c10b0005002c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 311838147 1250 311836897 311836907
    0x806060901031b0b0f07020906090f0c03070306090911090c0f030c09060702030a05011a0d0302070314010621050c01140a030504020105190201060e100e1503011803050d0b06030c0406 80
    0x41c2e12030103500c2c09003180e1941042c03800343d4445c0b20305100b0310001140704021807070007003c0785074020002e46480c400ca0400501038942d150028021540440000c400600c02c54132941c094001040c10020034040c0200074181100060100ca03001406010480000744c88000800101c1e580207601d481a2450341d502c2405c01d0106400c03003507019510440400c0f402d03001d45d804004031a8440d00403800040e100e5032030356241c03600340e02c0031180c2030203542200352543c0402d401042210440e900809141d010442c10f89280d8010803480d0080c8601202035500b00310081c0050040308000b44c460070403144200803000040d1a641c1600300c0c201c486141c10400c02084038807d4000c1500a4810f0400e1401c2034402c614040c1240c89149038840180e654500c100900c0d01000c428a401041d0717a1001e400701400d0018070807489070300820b8502240955140f80c0859102580300d1195080705002c410101c60181c0380c01811680f00040f007180807800d02506880c1450100112801403000c51046850b0518252080d18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 311839397 1250 311838147 311838173
    0x3090d030e03040504050f192705010b21010b15180a03020a090e10020310062003070b0a0c020c031906090605010b1b0726031c020310080606090103 65
    0x9000c2c001400002120746443c00b8490140c907660356545124600480c105e2030f922008548411200d007084000b4900c4086040c0104155182c40c03404004542c050503c0f0b4054007a070f40e491500300c80c25006030350800c140d1001c401c401080e400003e0183d46082010040720082c080086142d2840800000d2808904048100d0004034050300c410b40d031a40d03d80001e840e8061036444a40d10707a485001d8000442d400b4002038001c00c416580850440c10404d0640e8044c40c2c250195809000c84107041182c00c4c41084c81a611200c04101241d9a4055524111070071041c107440070f17008a42848400a121800450f10082070000640140602c0242ca100e1050425801c03606030b400d556a001e040c4042401800740303501a04140c400c103942c80841e212010740c000e8082c140081701d07402029040c0100010184a2140f80402c02d007014008080c0c2d201007800c500c111416440c401604440d80010401c0c9a0040e6100b003d002c4103099010b41e0b202034260b103645d0304449407039202620300014400078401000504d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 311840647 1250 311839397 311839421
    0x1b2d12020a1101060b1b030f0f07150c031401120f0605060f04060308070201020c0a080303060f04141006020609010207050705040c05070c030f0b0a060302010527100e100503090d03 79
    0x5080406102c103030840b982178100341c510100c001030301d29481c00c05100314040203160400451410b246e210400e05d88e80640d9031401401200022400140401c074031540c00c841e140c0f1181000002d4100c1400b900500c112400100e00119000c00090445040600040c010390082a2102c034003180d60b60b00d00007004000c00c100e90100c0ca00024031051b0711703240301d1400518810007490350b50343c806000180c075108107448110300c04c1c1c2100c1c2d0f09011489001c01030b660800019101441a51020780000c4c0290106070031070125250381e4000c00c82c0314000c04401c00104e80484e000e50b00117032a407409040c281d10031441d019245900403002080581081d078099107031980f80c0d140c4241030000f075aa840c0c00c91902e0341d2059902004d901003140c24400c4403100640c00428509013080f2151440d40041d03c0ca00500c00c45102801c03101c40d00b50400040c1201d00c85210720000c0540c3c0b2044c25058005d0060803400030054043e01034154110040c42c0100102c070b0058001400400d000040d508007240506420b5088c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 311841897 1250 311840647 311840657
    0xe0606030906070c0320150603061306181a15030610060e0f090c042d060c0c080708100f02090a0302100201020d0f0b0102100b10030b041b2d12020a 65
    0x1011003000004e10081081c840002030030248104002c612031fa8800074008900c680c02032001e00ca000840401c0314003280c0d5000501050b2403072090445502c000c91500041c01641000002c0300003600c600b80b13094810231340a01000b0781d50900c0b0042c50b558001c21103081c180001d690006000342401504154003010005120040c194200004030740c0c0700200340c0303001c2407580001c202070003841c5000303042203172481742a203d0100b004221400381040c186580724410074044500b0901c001e0181400c06400a050b451084410032950342030010703602c1142e2003500024a161030942c0101c070056008840d0440c000030507015920703044d0f40811880301151070b203142c19990708000242d21022540a007101c2045a600d0001e255a030f030400190a0109e02445d0070391162406899a490b86e80320528180d48003102e00d00018070a07000c070041801000c1046141c05010184040825002ea1000c0c070325500340709040070603400340c6c0800c455803200311050904c2c0c00030600c0417081d001c0c6548142d0140524403028548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 311843147 1250 311841897 311841917
    0xb06060c07170102030906070c03021e031e04080106060e0a03080a021501090b010f0302120a020d110c06040303060f0305060606160b0f09010c050906070809010c08130e0606030906070c03 82
    0x8035030078415000c0900c00060b5004006c01c018014288080f43e4020300505100d80c842841e554000c2d195814008122020340183c1b00303402c65000100240c5000c2c3c5210120320b1051a41b6007078000c030030b8006124452443d820060007055240c450742d211243e050000c3c010b203a01c2d50a50b40c4a0a075500301d040c850702144a1003130840b141c0400d0b60150b034001e0140301000104240d000700018407850a01220038217150042140b14095505140840c2e845400148016121001c54803400040d108034294500c940c00b001c10310b081045008207105014620a0710200301450307030351030554282640351201408a410260019103030b800d11400901011480c9901c51800c070425507a4400c04900035603100071400035203010400c400c42c4c00d120350b10f841710050401e02d003400c07a008002500303441511002000c415012540d40d206d64003480e40c000c1d600c0e0703001d8910341d1960403000340c4c502c0305d0956102d60348440c0c100c1070100d60241040000c69000b010b10b28050141a40c5a05082d1400070040703a0803000c0045240c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 311844397 1250 311843147 311843159
    0x30f03060f090a090309060c030c030806060c010c0801140f06030411060f0703110f03162418030f03050709060c170406030903080a0e1c03060b04060f080f040b06060c07 74
    0x41244581d800c3c0d40009801c0c801410000c00155040d0091401d2152045188002c207810091810f00c81d03615140800207960b8040206101d40100501407903907600b840c540901e220b0f0800e0b04141a18220ba844105901c2c5100810901020300360f0460b070004410004a00032030014490b8403603200014208518007501c10354843c1d9268084907041e40007030712a807440381c4004001d100003102038000318001c40c104040e203605440d40c6001c032000109000801803200b45000c01440301c804065071144020040d070810321600d0303d042d1100c084120300141002c5851a807050091040e076000d0b2400d90380758801d0500308102510383d002a6403050380ca1506103c2c0500382480300300000c101800040c0e40200b82c0700c20f2854050112940500f009440c1410b00d90b600140c1000018203540711050544408a941e0b60100142d008146c03980189607118000640462942e03009a082150300401d65070700704140d42d9040840c001e41d074040d20001d0803c002c0502083c010f151440103030448019040548a105940c1c403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 311845647 1250 311844397 311844409
    0xc030d1e091e06030c0c110d050f0102030a05160504080304060c0f060c121107112704030203070210030219050f040f030b040b07050c12071103032d040602030f03060f 73
    0x3101000d0b0440d1149014071140d6407500030030340d00c1c0540c1d042c01c241402c01c42d552200810b81c50390410b4001c400180e10002413000c1003105421039565071000b1540d9041c200340b01000340600311040001c800800c02d8520050344100219400c40722094091401c040c28954101c1d1012509079040d148402c144000c03c010407881e101d02400d408854503455000c0403114405003d551194072407591210060040e078006c2140d01c4100311132040119540000070000ca92030594007900808000007940c03e80701000704040d0008001c100e070f140201e59200c1c00c0c800340341c0c04405070320a00081d8100b03161124042070b0380318012030203490060b1020540d02d003425164101444540040d6009484921190080c0014001401485034100009140c45860400c0c0c0e82c1c42aa510910034403c215902c900042c0d2805204410340c01b50040c0c103005082c4c17607942e5042d0010043c0d10300d80341903004130030411000840c0d01c51249c408580881c0c01c1c68025500303103000e1032030000b419000100030581103d80c0a2003441c09513a00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 311846897 1250 311845647 311845679
    0x7090e0f0f1302060706050a022101030203011107030e010c0201050408030f0d14010b030c0d091509020a051e04020d331508190e0609030a020c030d1e09 67
    0x9100340c0a9142144118250700800741035031000c903240034500380240c1c0b2901c0440c2d04207600180081030b2505d4001c155402480b800b80401c009082e9080c2a0001040303488116048034001c4000348459070000194003141c0c4103a102c000c000c60351026059229500910a100d80c107401418041e00302075032103081d14110383c000322100d060001c0c0000d005441c100f9a21801100c05a03400c0302100d598100590790610b840042c01c0c91a0100020428110f1101641c02c01001664407844a03114500000200f00140000c0c0758102c0c03042d10403640202d0f4605080c4890300c000260942c4d4030505000100c188002544151441c00e203054a4034511012041c40314000e0700c0841c1d09000381c0522090500481d0711a03081500b0084e4410780c010391401075540c1c04900305402c080c0301c0740700304440c18480900c1c40003010140007078070060250900b0040c1500001c400b500c1c070301c251a000c1c0e0310802c502e50304254640c8407045109000c6410500403104554036102c04401401c0c039403c048100b2520ac0c18010610454 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 311848147 1250 311846897 311846911
    0x6060d0506280302090108030a020c21010207080403111206061002100603030818030414150c100510060504030b0a240b0301061b03120f0b040f0204030210020f06070807090e 76
    0xd401010001c5040c86010717180101118005581448010130009490702141f4081a12a203990f01900108202070541902c003030350040002c549c1c0c1c85442c50044507035003043c4826070b404a250040784103a801d000e0020600f0740c1103d0050310f4241d44804c1007082400680000408511401c8446030000c1403e2007408023850290b07c92016500d0110740078036a461264400d0798550700244020002d02d1900324282e0800c0c04112400040d2108400060105005961030705020b0312031064140300141d040d90181c0e0103410032641850f5901e449200c282e03a01c2c4189c0c40010a4499800001411074039240d02002002095044207820450403442c2c42103c81c109400050300725034000010411640c204648404a10514920900140503510b01515031540580108502a201e10b460046195503912007410850002c02c10000c4a03118035400000350002e010490045280a036090302c0e940c00080c40c1d90703006900c02c0061506d651181c200725a0b20001130704a0f0140501800007244040d45400224800c6d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 311849397 1250 311848147 311848219
    0x161b03060b060408062701290303040602120c011104061701090e0c10050904090807060606020a0b0c0c011118010f0e150306061306020f10020306060d0506 68
    0x20450518a04450740c0d081940e00c511020001049503140208500307500000308000643c44071008070030b1601c8840403118001a6520b0f0000841001101e1072800f1400b2030034180c21183c418000c000d16a99210b103000e81c00142c0c0c40030352a14540c1102d04000c00741080d600e0300101c1c0070800031500140c01e802c540c204030b010800400c0c6520003030880e00308072401000b034100180b185d245800c112075112424848024018166919031068603070080040311121507001c1d004100480b040e041000890704400170071943c842c1414400200342c0d10010b403200d884e07608106000c425480e210010200c680c000314900d081ca5490b07811175850a10400e02910360500c580c074020f4404052480010141c104101034001405108583c081d025296040301d000c00c802c0342c0384600c0d0f80381c03900000183c10340035910345c0030b030000100c45002c00c0640e40400e6610104240000302c61016003100c0c004010b81c0411241b064020750207000034017082170141c00c900c2c3c0000c00541081051655158140b201c400407224402c002d071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 311850647 1250 311849397 311849399
    0x8040308060a05010c080a03060f0b0408070806071e111516030c02030d02130305030c160e010605090906040f06081b03060408040312090f0e0a180b0c161b 68
    0x903030000d601a0344803208850b120356190420001918452140b80003411255010810700000c900a90061000c1c02000c12000003007541c4e507103c40c9180c0d009006074009070080f00740020700c820b0700085550003034100e074840640b4503400c511801000c00f28184803070100044074801c141070a000340031302105a00b6881c01c036846c601d0001082e50081540700310603800c06203822401391b03040780d0100c240c40310400300b0781c009603407013030590b00d211818035007900040d00c40d0000284e44890340400059248500d8124141c0b0400999654090368081009200d00d0003c100d081021450714540079a4003680304d00d00400018410200343c039800203d03002034016000c1c03640101c1c20103103240c07000c1d40c208100c0b40040740209040d19082c0c0e1145001c0c02280b1005140d83c2c0c0702da09030f02c502d40c01030300300da80640101ca0501440076991010360310100300a4402c08002c9141c400301c0c1c1042a407040d00d404145402c85000364176521880d030070040320343c804440c100302a0a4500d8950010700f50540c41042c001010008000e09 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 311851897 1250 311850647 311850653
    0x16080408010f1d210c01020f030a0509071206150806070309052a0d02120f010b0a120b0414030405040c08040218040c0b0703020a0b281a041503080a0804 67
    0x82c0e600f6259545156a2645600f806042c0001c0d00180410a820074540c8802e201c203802880d0702510304c3c1c404003940045840c08403000008051441034104100c14011512541c40654aa5241c0e0148545031446401840d000c6000740c2c2081c060b202030b15103a11005a50781010506110742964940002032311031004c04288030041201d01070100a00350312401c8030070000f040484070000c40c2e18050064518508107402c0d5a1800709060101c0003040548109400c108051130080c0f0021201c0c52055000002c082118501e9084854805610501a08182e191a11041c81241d040d901d01e40451000b000046860f85460007012504015500c1c0c990b014100761042060007445401c0007280c044180c4100008103c1801d0048112100c40c803c203035554400b4201207041101141000d0715071942c070002d0000d6100c04c3c07083c0c0c072128030001110007a1810182e4802040c1d418850306c002048070300200000c2d45107080d50180e4158003142d4250310721603543c0c0d0740b1b01405420128031303880403c0d0200200814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 311853147 1250 311851897 311851901
    0x60608090f030415110f0d090f0b0a08071d190e01081b060705011116030206090a020a090e03070f1202060a02040b0d020703051b030405030d03140c16080408010f 71
    0x9006844005507082a05244045100c40d0041e03030035130100120400022030103141884646c1840807020142c0c0c1ca00192400090a2005c03a8420b843c010311406500013130101d0060155000c008940e40c0d021a26200c03800102c50603020b0008100d850a5541c480f141c00c1da44440c01c0d011618004d00d1044d042c903182c0b0404a0040d44160301c01000e40d00a2a0480080e061520306584041d0088449586811303882c00e0090052074148000004004002164249128644c5007200d8203446582154075a51303070b941d80ca645561a58400a40000760040b00348100c004940210072249407170303002c89080101546400c1035035040341c0d9060b14195401b06400403081e90500c8030360703405240101e09601d0070780b0f440c0017100141724000c1140781c510350100b011000c041c4107100301c1d07020640700003507a1810421015880d460342c0c85849118070034424100b50a607203901a02400802e4240041541c0e4266102682c0003a1a40031201c001107000c400201040010000401b4102400c07205000081400180090b001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 311854397 1250 311853147 311853163
    0x4210206070e030c030a061e0908040f080102160b060d0b0a09020102070f06020a0b06060c0a030e030607170406020304031b0507150503091903021f05060f04020a02061506070606060809 81
    0x20013600245079403622610006644150340368000000500c01c030896030141c081c00c11200d03030285080d040600b03860034010001c01800589070070010380f10791250f540804034203d00c200b8000c0c000132810341ca0142d02113252010b009501031809024030091010342d5a550078664811105240f81980e25038000042d940d040103160080c0c49004101800d040c01c15401035a281e1076280c0040900110b1000120759840d410f080d036809080701400c40d01500928a0041c042e5203070001020300030321a04001074042303403007001c00050080352408058802d4030349840f030201945c00248150b05100000c240818550126001c04020300d02881c090900141405410410080203090f82401c0004c1030060007261000030440042da808644603880300b01160b403500341d0070b011092002c0d2541e50300c0c01c109107001c0e25160b00304c1882010120f0310101016095404c0000700d0040c000c103040164028400202c02a083c0d85c0102c3e402280140868105030306566500141ca0040d0400300010f400c10013803000007901000303640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 311855647 1250 311854397 311854399
    0xe10060e0f011214070b0301030f030e0105130e09160e0103030905010e0112050613051e06060c1f09061104090e0c010f121b020c13090803040b04210206070e 69
    0x30201d0351400058000b25015900e003c0c12400d50003119003c440c000b082540018500c2c514036945945c2e49040210409002100580c00b0904400b60030325198411011a040100c0400b12088010708012071941c500000070440c0c05103129280002e0445401c441b8004001c090f0844955459815450300910a800a5000303e040c0103e01c15a850142e03041078090005900c00340c0c0000d9030750796110001e5001c50020170003009213442c0c00c0502000a4400f00c140c2031000c1050480c4002c2d071508014031150348a18030425425070820410086580d00d00a42c0d0f1040154450000c200c0d0201611101e0407600005241442c0180015040108180c00e0081103d06003242d40903200c1144001c001030030f991442c541410401c030041d0348500c2100c03120342c0010198095800481d2360892207041c060340e1443e150850038880c120703500d900407440c2c02900414020541c08005a0b00795100c81e034078145907910103002140c840040b245103240c1102140a4410600040d40c0141442d00f000e50000d400700740307820040b0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 311856897 1250 311855647 311855671
    0x90e0321070503040b040204021b010507020106140310050705040902130f09090203060a020c150a050709050603150409020103140702010501031b0605072d05030903010f0b130e010e10060e 82
    0x19250b0000c0680e90301c03940010880c00c0d656260b00c002402881405010f00c070402c8203c00010304c10380305510a03072007040c058008002d4070751200d9019043d10301042490307515071b00501e40103103603600700c0d0402c0750098001d003051400c240d12010480140c1e044400c040305d04110b000d60400c68444410381120083c11000ea08100e64200c54010a460b420f00070300e12001c0640002c0e031103040301810001941d8900c413201c000c254900303000c2172240242100707441d0200060f4051401203501d1a2650840f4015104010840d090b00c1c24081031001a02e903140003a414150f481040388051500b0440d140c6c8100026400021250305500c0c0480c1443c5d040035020301c84403072511083c851a9009400c40d13842c2d941045170f105003109044102417501c40000300c00c0c1c0041d404020320a080090000141001000803002440062101c0d4841c03000c4412009100740d01903c403c0da039485082c1140c1c03118207a00e880c08000b00d5164414500ea618102401c069924400e0f0f552004000003042c00d008250010181822 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 311858147 1250 311856897 311856901
    0x30b270a020409030912080d0f0c050304030305060a0b07260901020703081b031306020d08060a1811032404020a0504170703060f0f0e010902030613050106090e0321 72
    0x1a0503591544004000c2c041c40e0b4812041041c513000d030720300394000c0c01c200301e1a0651498a107001c1742c1d103802c000001c800c200d043c6403107200d80e051140070b5070700d4040c0184e89060540d07840d610300310041e10000d4021f98010a11040c045030000300d8034004d2040500410070a241140418070b021104003081c00c8c1c0283c44070051142e00b80301c3c1c0e8041a16070490360030a6203681c0b95060954610441a60055080034034440061900040d4600160800882c7d940d0740a070f40704441c4410040d14055022555161303c2080400140610340f1024803542c0380c0c4540030000240700d507131403940c0301950340159189541403c24400343c14004035114014254054203580650405c1e11513a000341403405a0300610b006003600050400b0115020040e8100652308080c041c4018210043c0c1c050041885c06101c8810604105052180c010b0500910400942c0038009140558031403005138210300a010741107849540b15400010540c58502554a8001b00440a180d941d4074440340c000071751920072001b07100800100c003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 311859397 1250 311858147 311858221
    0x15031602070305031b010b130605010210060b12040501150f0807060519050c030d05070905040b1c02060d021b0d082503090317040309090b060412060c0216030b 70
    0x200340d50041c90545d82112250f00c4c113420032801b50859014094010300007140c03001280020f60042d00458a007138080d0740c0035401d40c034044004e0300d60350b0144054601d810010428120710485071280d01a000c0c400018480010004005101806520044014040300000d1000703010510088004200740e08006150580c0301058002c00300c055003581040c4500800d41e110700740414012100c2508022170b041265241caa01e001d450a0100d009180c01286007203111030190600c00800a0903d141c40c5114080490b60b40c00c010442d0700c1b0049055000d5000d100740c0c005c01d404c40e6804c3c41085009800740016140c4180b0003048004001c00d11800d10082136044250302d20f00c03242c40301c0c4000c228038011a55085a080c195408480c2c02c8406190601000c00c06c820705502008150585084201c240000b045a070304202141c0203d024102d40c401e0548605400500c095000100302c0f94180141c1d02401c0c078a5051600400382079105490140c0c1c032030b040000080d400e42e0342c10145050840c400b2039040301c1c40c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 311860647 1250 311859397 311859403
    0x40c0302090a0e150a090c08010b090f040b01050408070602010f0f0209091b040f06080402211f0f020301150e010201090c060f020f030f250f0f03030b15031602070305 73
    0x84034043d07038109503402040181c04000303c3c01e4048100502146090703581c50540f030004041450101001030381c0c910000c00c800d0011012500520001030024040b411408108801400c40b4110303103050003020000014034510500000c4000c1a0580002403807074500500e990603a1515030f0000744a0748104a44030b11740e03407660301045d0080542102d007a10b4041b051412051803189810510382000700c200700080c041c0d444015284128425184100003518a00b4984544e85980701024200c1d044008049010070b407020100c4807002c04a00c010880000208041d0300f213a10a8122000030440710020b10400364204040d10102a0284000c0240c0c0300780e6120742c04200080d0180d101002641204121094820020481007031115401d41f6500c90a11000c03c4041d0b01450b40002000741501c01076200b010b40c40001940307503400031a540d80d10300503a5500403181c3da5049084051503918201c2110301d0b100e242c070b200d030026151740520369a400c1100041c020503040c080e000c021507014000c00d20000d4004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 311861897 1250 311860647 311860649
    0x30405031510030b0a0e0715021606080c16020d0c051c0b01050105160b010b040f140a091107050105070804020f490c030605070f0905011b0818040c0302090a 69
    0x4606504403940740c1c00c80203805044c1b640d40001003845a1540071800c800c1805019000d4405034007144c0da61381a00e21012242001d51207200041034600c000690300b020300f0402484003640c1004515688509540040c0440c555508180c4240e407065200340014100a8188012104401c019105c141c04983c0c5140c01440140183ca04000000c0b4044030403499109409030000e80c4089007007030541e101d143e100407540040c400da0202d0004d408c400124904d400100440320300d0f015180300b000c9820030303020001800c04156105902441044030b100481e44c284103c88c007505403039aa07201c0d1400c05004100d22508c081c58010b03c54441845810034180990002c04501002003801d4241c00003411603004038940820740949428425506807010400150081c8050b83e00c108410061912035050071180c0b003460f001d02001080408006010310b40c019001d840d428145540c45001c0d100030b41d51458020380160303503860f80302d02d207030b0b2070403c014505070013042c0180310315190840c203180da0b45000410810903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 311863147 1250 311861897 311861903
    0xc020105011a091e060c0a0318230d0c27020a0f080a230610020a020a1a041208070b0c09010c11030111031003030e0303030f15040902040e03040503151003 68
    0xc41d400344102850078030401c10020030700400080d01c1e03040306c801c450344804000d80200c00060703c4100e41241391081110b1030041c1d401080000309542a00d8201200c48039240100700d034450380564440d0006014800343c2c4000d41034001c589101c81c21103400076113401100e607841908142c01170000e2910241c1c03010400342411b50f01d2600040c141c07180c2c4103801c010808000700d1451400e00207440381000500f240c0f06400b07640d003552601c1c0e8507480042d0480e103c00303241c500203510188920b410800c002c0000701d0310142c1d44010801500d029501e482c0da03e142002e404086540320008698103080c4100d2a07420369002e5004008145003400300c0000a01c0c40045070f00080222501034071120b4652001d50200c081d500a81352895507909282d0714900011199101c21000207032000030360400d9040220581e80034000081c035019081e02d5200d407220340c0c1c1c030607072540c5030b040b03603444103002c015075500c0c0074000c0c0142c80301c6c015564860400060504280c84592490001442081032104c9602e0b103e6000040301e030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 311864397 1250 311863147 311863159
    0x201f0503040312060821120f191407180b0f130b0706060807151b110910090c0806030c010302131707090c020a0b070e01020309090a0c020105011a09 65
    0x6124502075610003a101c48000f5010319002c00851094800140d00d820346030501803102900d01c460070b0350314140c855050380052854091000c5200c609a112581d90004050041140400104100f400482d9211492544c1410f821014030068540107005503000d10611030341d1528050500650070074900c02d41e0100079a842d0f0014101d0340106125407000c0140020342c10381580c03020182840c4000d040e40303015401d800c1c020f0707410000d20342e811340302c5c3d104c61440c1f60303100c0c2c24030205000301040381117000d22410307580a43c2c0c08070391081c16516010080e115030307800c414281c0d4043c2007984040031141c800014100b800720310400d00003e50380004025203003080034a00580d8440115201030604116503100c414810b00f50a030b222281400400d9800c25141c060400704107c029800702240c0e690980000588118041d0b030120352114811031084103460301c1801221710342400030010800e11101280c008102a50303400402d004a94203029490041000c0030751241150b9242400c192148218040c4900c110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 311865647 1250 311864397 311864401
    0x21070f090e1807090501050316060903030309020d05030d050f1f090c17040c03051b21030f1204060509030c070e07120f0c08180d031d0a201f0503 64
    0x46484001402c4042016055600c519a80c54848020740000c0c012984240610034075118140420000f610403034070761340d4891003500c2c43e6841c250010548450180c0e00142c1e8074101001245040004101d84040058005500d2515001c850948003000d42505038008421140c10022240e440054041d03800807040003420b41ca0f50042640d05024011310007640340c441d40100002c0c0541c20b80500c048a0260050714a46040714203000071412060b2141b41c1c0c4410400480340e80075143c03003007074900f02503a08d045031720b4007805c85140c0c1d615410012004449000180801080007040d0040ca80c1280210004605001c95006416210511405030200f549802c40018103240d200340300070200c7c103001e0807003000031500f100040c00180c1584112103020601d0741c808100001c020807404e407002c0d10320001801c0743d4200c6d44000c8000e0044507180c0c41c5158050703241201e44170418003c145100d80320b449083da852020035102003031a00c43d428028803030840404ea021410f101064031700400b2a0074a0110307620303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 311866897 1250 311865647 311865661
    0x703050a05070c110a15050705010f02031003060c0225090b04050c1c09120309050c010f021c090302060d05040320030a030b030a06051503070b04030f0803040804080321070f090e 78
    0x441c2c11740e8081003c0c3c091202c00690400c1d0054010041640514028010034041a6020043c0c0c44203803424032040d00d17440b81c100080b0b0900c2e8016144014031380b040c2c40d0704900304014841c90b1405444c907100700706c144090400c5140c0c8144910004c402c001e17a003d00840c584015541c10502884903185460039030f0700002039000c96036078060400726a0101c040418015060002401002c0d40c0310304854a210300c50006601d58040c1250030059071142c0e00404403c80420825544000c0122140040c04445800030005a4901002e0300c5d039901c0c6204009010700e098100100308803002c1000b07201da080c0c1b03158480c40100c0d02104480c42c4071550700f00811402d507044082450201c0e11900685007031700d02000d03c001c0c00045841b5003100e03c01101143c503000d0b125000c40c404d901c140c0c40001d246040d00b00003e00003c0792032000c2d43d4403078050f00d9400d04180e0740d0040142103500c0207a03915010f0500d1400305001c52104411a5007110340c0d0302d05104070780c032000c50281a14425004030740c40010003000286103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 311868147 1250 311866897 311866909
    0x230c011e050f07050a0317131101050d06170d0314040c0509060d2906010905010824030d0203040515030103050606011d100806030606040905030d090203030d06030503030703050a05070c11 82
    0x103d00c0d8403404969421060382070041411080c00c589203600040c250202d039010a0000c035007403019800001c0c2051009101005480c1540000302c82d85103180c8032840041ea002d803c28040f84420560310160010041c1404020112603401d07006038850010755081c04003040a030251314007521000d4500000580b1480000780320141c0c3d01c180180240380c120f500641080c0e40c400190402c5007841406542502e4190054514210703a02a0a002916001c00101c00c3c05030340411066220580d030520030a424004086070400035031507240d00c0581d0002504001d2401d00c0e000c0034140d4409401c1150855042d0750780c9544501c405488281041044040072b1100c90000c240007400c501c000f4004d521180030701c0405800010102e584610a0180b040050401c3c2840c1c0580c0309a994070102a528103103142046400070200381e0016601440140590025113215101e248060b600600046450303180c00310009081e03074402046440c50505080501c0801900034a078402c8440e40240a13008211700f00e004220713 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 311869397 1250 311868147 311868157
    0x130f0c090609090c05010207080a0b2214070506030415150512150c070807030f050412060e1e0c06070f02150901020d050a09050603090307230c011e050f 67
    0xe0306468290001003000031540006202445000c80a0303060b0f640d4001a03882d050b45203e0076401c0c0d0004155600050b410709600c4e580122007540c1540925014044200c0580c0f400b481165a110a03545050814204010281c01400b045070090318528041d5140b04c141c02800034200517003611007803504400c1c2072000107000078000142c03004074008410104180d4449485d2601c003403050a00c408141c84036480c000715610b654000040b10311300402a503040707030380114601c940401c020303086c00301098072450f050586076003901454001c00c2d01050500721700d003031a05c2c8204030b1070807031401c0c0c03549a041f41c00403030b00c0e841d060300442d6110303180c80103401c0035458200300c41c000a6104200e4081544160700c041c005e40307000c2c08281c0c01c5031144030349440300303940314800c02106001040000000f00420315100300156889404942903d007000000d40c2d680068205d107c108031010071212841040c8064100561550000e007403900c545681d407d03030000308407050611070f000e041040000c0d414680700900d5003190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 311870503 1106 311869397 311869409
    0x30f0f020a03060e03040e0f0f0403081008030f03070201150b16031215050f0109060813030504030807030206041a06060315040b0333130f0c 62
    0x8214160445000c990101a8940100c0054802e02410301c100134850000c2d41c0759410040c40e00c1c0c408100804140700000881d0411810500c9800081e81240c3c050070130000c0741c1c0b01ca002103000a280e9030025403082c48000b03001c03c81e103c8548015445205035a003700071030610100c16508154440c8141080d6101c1809030100008801d90111780180c802d00f811b030300b0303100c802c1c4091058420104050070103680d144010401e90a0444019240726000d00e4a0071415040001c040d10300b40d070140c18500c08130000c1040404050141c0201c0e0301850304108656250400c502c5d0007562007504035411a0711000c003410409040c2400000e1038010710380101058255554201048280c41d90540560751007502d804c0382e0151170301c09015448000003500380e180900c5c1d22107100c0d464140030401c60525085004010800030351102d0000f0400e03143d024200c200e05481c241401d555101a0760800 = true := by decide +kernel

theorem cover : BRFrame.Cov 311690647 311870503 := by
  have h0 := BRFrame.cov_init 311690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 311690647 ≤ n) (h2 : n < 311870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
