-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3755
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:08.628865+00:00
-- url     : https://prove2.me/submissions/bf412a33-ee3c-4187-8b23-1aa97f3b0d98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 675179856 ≤ n < 675359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 675181106 1250 675179856 675179861
    0x507030b0a06030b01181401050a0c0f060c11061009020d0605030d081e22031803060506100c08070f0f080309031b1603170d0e0c1f1b080d020a03 64
    0x2c00c8086e41d07144645405170049140f03541850141422802c0c084582031802c0d0301c04c4008002c0c5012514082c03030180e03280e541c1ca82003640c000e60300301d81c0f85848560382c0d0001d0350301800d1480c400d0440da00a02882c1440200c00706800031500508000039000912001420196040701c0020203000d812501c19000b0241d005140020641d800c2c203100101c500c0c1035140c80d1131138100c0350203100841e64038031840100700781e02c280d10380c1003540407424009140c440c00315104408400c64001c5004000120700c17803804a007041003410310480080f0074440301c1c105c0d10000c00c100b10180c0d403810b07a001450a030701515500741225855480d86004101c000000304000013a0f401102070685a4a40201100300e80481c03524117442c2e401440c444854204c00000410224094400c01b00c04040b90708081e80c6007030102c1e1000c00a0310721500d001e1040b60b21009441020b42004461443c0300030008070030020005180000404060b00590100301c5000c2075241501801758940407125180d5001100315558036010030040c02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 675182356 1250 675181106 675181121
    0x141206043602044a03030a05010305010c020f0703060902040e030c010b09060103060b0d050c311d0c0901020106120302060403090605030c07060203130c0f08120f04090507030b0a0603 80
    0xa80d060440f0000107240c094414070b9940501d0209050007086000ca884000003144003808a401c0b1300c03410b2100c2d1403814002140282a4500c01181560540c14103d00b0341303000e20a000e0866020035240c0102040c003203042c6054a92122011480444a000043c09040c2d4035081940b64000043c2129a0940c1541300403e8144251022412683c94100541c01c81d030700c0e4403175001c1c10340080081d00c00181050b4401c0d50700290500c00e00f810310076001c43d1804810203186c071020002c1c10343c00b4002510f40c402101080209221100f208542c909181c000d41e4503907000d840d030b5502d0f8101140e404031683c000c1d0000405442c404121401400d05402c000303550300d60568065010803105100464401e1090b811a07118110210382240703422002e40c0c0b04802544010120000f20102814031000680305400c1c0f00001c0083c1901030076214144441c1e181400404c06070000b03440420842c4040b04580340c810750f011221145000151035032010743c143e01400700c1c01c0e100da911614070000407552940591240c81c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 675183606 1250 675182356 675182359
    0x180803070810080606060a0e1813020901150c0f0c08060f0612060103080f0705010b060415021504020310091e060e0c0f0303030a090c0f060906141206043602 69
    0x111641e5080468550b4819280b00e50451b60412411b2002402280c2c40c4041300c0001c1c2804898810080070080850016203452400850340020f5400b50714000341d015000d00351420500c40380040c0c1c070801820b50001c942c0c004101701c02c3c2c100c865040c4038522007030200520540341950803d2070005d030004980380c8101c3d00f26200d0951504103258444001605506995101251914201c54802c604580390443d400840301c03903480d1a810000e584500015000803d050301b4408180b00c0380040c041d00749644150700745c2ca10304444040001603030703000481005400c4000e0000406e45c8550030b2040c590002c41c44944003944140744d1081c20003c083e4041c208200340c08003940c2e0307001c0512040000020012990591503441840401d45030405580010b119602c100030a4000383e56620b960422030070320b9070201011030040c0500300211600100080180d4140c50f400038070305220b4540790240f14801a10450045544401c14591b01205c1c240701306244407041c200b911400c409480041680c01c01c800f049 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 675184856 1250 675183606 675183631
    0x302030a1d0d030b0604090f0209030d0f020c0607061404051b0d170901050c0a0807021008160f1b050a02040b0a030f1511030f160f0906031808030708 66
    0x904045a6482501c50745995480909110030345494200c020f001c880903801d1380b04408000c0054820741601c81d203034944038140d2026803902d00150425041280304040c0c8401d10001040c15035460383c2c00b085010481404680d81610342c0344908000c0020720b02480c61302c1e0420401418841032040014001501c88050b26031548890302901c184074184400c4500203200d070010101040204c2d0b040000703001c40c007a06241c010306000b03140401c50310744032480d0811388114100080203025400c141d41c071071110140c1401e00c1e1415003805890413509039030035806030081024180304400c100388140c2006258610340d0340c20601030181c0381021604c1d00a0240f08030720591401001c2200c505150700d54104407501f103209045056283c1e1030f10a1040c0c09442c1107d15265201c0024040c0e2840314003550091541b0382100c1c1841c903005404002609081c0341c0c140a1102c0303c0d0710000d05940c040400001d480f12854003040d003000e03c3c1507014001a1602c0002c01c8440040204440141d01c485c10030b10481d80d01008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 675186106 1250 675184856 675184871
    0x5040306050906040209090318060c10060308030115020102070206090f18070f0206091914070e0a06061706060912030f0406050901020d050a02030a031d100614040e2d06070302030a 79
    0x244c3c0d84d00c40c1c122700c000000006034502e10146052800380c01e5414048064840031900440ca6100f00c2e0510341003111400c0e80030006001410f40d01008002c914502d0000310f25028503500018014010300c1c84240c4200f01801c00b180c043d480340301402043c0e01040c030410010b4103041070094822941d03e26102c4c018420440019040c4a002420003c45494511800c0381007069440d914081850b040d203001c841e01c2007070342c00218800c2001000b845002c2c0442d000800a0901074003d00c5c0403030802980480142107801d004031555044112030084a00302c51f10b03031a100e0580400780c110b0084500c0c83c50a1000031500081254110b0001c0c004031109a0949415810141058503640039200600005a00a001070f20f05503010358010040c0501604c80c5203590500000020300d0043d004a443c01d84035105c48040000746000c00d1850050141100c00b1301007a01d0304010a0350f1064061360b8000b09040d5190036565603220089481140c80300740007900c00c0c0e898008405400380d032047c0c03070324a0b29a2400e0030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 675187356 1250 675186106 675186121
    0x10b091e10020c0f190b1b240106020607091e05030f030d0b09041214161419050303040803271609021c0c2a060f0b100f05040306050906040209 63
    0xb0641d024600104017000b2903043c000004419000b001002680514800800e488410100320f03913041190761040040031101c5440d8070b41503a0a040e400788044d9800702d800d221300c15030807904100a0790f4a0070034072448010886103000001106500050305130244004124294601000030010136000304002c1c0303c116200d1041c030614581c05c840203000031040144210440780b181c4c1c09500480a881c030000d0030250311407007149007440f84107002ca804480c200140380781c4407018022070348030002e10701d200c4103140d1740d6440703840d26440018401040303080e0010010354a1040075a00c8088600100b1102822b14480b00e941d40d03440d0001d070310014210003501000103400c00c190007140c00c50760b09242c51405c151740a000c000081c05c207165044050140f8030b0304185060441c4031640c030000800c480f0000c00340120b4100b41048400003880a003004e410407100140c0c50f203d500e00443d10781c1403840d00c56101140c00f0307402c8403240a44d0704028001401c05050219410001803220f0069008440158103925a1007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 675188606 1250 675187356 675187369
    0x103020406060807021f06050901121106041203052d04090b100e04180b0901241d070e030102040b070302010e0607140c0a0501050f04030215010b091e10020c0f 70
    0x1500b51006074440030003202c61b403804c600041160000c0c0308000c45c006880f01e000130540718098100c034070001480d2003a50705109a404820502c814103aa80c0f0b407516003090008560580e841f2000b03010b000000529858000701360f0760354600c26400d0903841a00300b8a59031034441540c003c3c0729203022607003090290f403540e04d01a1136208485d2400d403502038a00d80b41718240400342c01082c06540c80200148204d038045151044410f100344941000007691321034800c1d01c900e03c04110001000310520305001400501d10840c20140011000a03409485940c0c40e807044513400c18042a07103405500204000a20034520805417103440d20039002440640d510324023040e0358000844246001407511180b4050501e007010040c0748903400e19080d581e000703e15032030701400d4480903038110103a840800104018950705105d09407045a03000350b64891545003540b0040c079401000401803264044d0001030580c40c150541d19244940041c080e80900000d0000c00f0f03480700d5041c4181c0c0d025400b000c5035881c403842c045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 675189856 1250 675188606 675188611
    0x501062409051002010209090f07140918090a0507032001110606040e0c0429010c0b060907050c0115050a0b0408060f0702010209030f0f1002030c03070e040b1801030204060608 77
    0x16941c20300102c1c60181002042803000c18500706555080200c14465280c24040e24414440404d80641e981400034004000c00c0c8210210b01890b1410b001000141d9115502568440b135203c0120031162aa103403105d08007942303401c000307200d44a007070300000402038030380002000f009480200c020003010000041d6500500020313044000d80240f00096041d140c160300600d03031415030400b124408610780000c1030440c2c40c00035030b80400798159000201016040c150b070b08000f83c02881c04505100280d9103461111101900c1c403442003031150b00145601e84200103950100301e1007802131213071110320883c066841250740162801002d032600302066500345001103c04480b070420092420341d82e2208108821140071700000110354003000f04c42120380e01008802020012500944031000349001468900b10884000c0740700300c0d0040c41003004030000350080d02d9210360241000702d4484600400030740200310703030409182d1000a80b08101710806010402d241624030a54041255503210f02040c0c6554104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 675191106 1250 675189856 675189929
    0xf0302100b1305040501021c0609061d010621090303050f0604060f1a040b0a08092803121b030605040f05060a05011b08071a1e0a1d0109050106 63
    0x8101c200440b03488503034081c982c450b010b00001820901e08800010403d05030449071100152903501c28444408244035071001400714035458034006243c400c0011100c0014404c980c00e1041a442c40e0f0158442c480c0071070341d000c000010402044509180140041a094400d00d00c1400c0031800601282410301c100b5050741d6490341440d80c407526203141d081d0340c04040c100c9a401c543c406c0c40002400000c02010741201c02958840c01d600e840c00c020090300c1c0ca00750b01100c001c044100b104903400d04500080c3e903040c171f40e01403414030703241135070490424040d03d0081b10103ca105c500c0410426800d906900150035030f10221030030f10040708803090030380c1038442c241e034056840b2414441c200050341c01021000c107480e50005a241c41c203000381e29600c1c40b6404c14034040d107801035116200040b511020014940c8100a8805242c80b080c1c61800c01400c038200071f1525030a1550380210481412040f16051a02500b000c024030110301e0503c2c0031406070015219400c6055086000041445226492803201500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 675192356 1250 675191106 675191119
    0xc02370b0f0c01110403060b131b05180d0c062706030b120a0b0f181b0d0b010f0602120301140d210e10050705030f07140a0f0302100b 59
    0x8141c0600d04560040c10862525036a40440c2ca500110b40b1001d40000c60142d600003912050700c2c024854141e8200c0c0d07508003020f25010f030b03410000b01625041550340f040d071310741a901d400c42d00140030120911300c5201903010381110ba101c000c004030b0168110940700943d075014807185030b00c195a10051506090344060440381c100900285100313a0042107072410061200c1d40c5560140031a50801e0301c1d02034103032010b55828003003103000c0c245420883c0c0c010824074408100000d2030f01c1450b86400c04030340c0d881e541610701d280e1b010700c6903140f02c0903802a50b04191080580d580d1862a800d4100310f5100d4500980241e03105090000c05510a0701d048424400998a070350b6010010041c0b8100c45150440703810342c140b6002810300c04042244844d0390b2403134840150b0030b0114410400713610302154034036007000000c0050000040c004003d503a440015441d030039850390b042d4034060a82541c0502001c51510403031030f44a003440105c0d0403600505000f038007910301c2c50704842160310907140101807581c0c205c0c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 675193606 1250 675192356 675192367
    0x51008010306051b04080c0a1a030a090c050301020c15070801150e01021e0109030908070b16050c12100605030115050d030306051002010b0f040504170a0c02370b 71
    0x1940303074000b29405803010100704138022040f82000c41070780041d00300048075800078075001d00e6414000542c81c050091a030030403410804100142071188402080703000702c0c0b600d500c148001c00008000345009804003e00941d12a45605d01499139486c100120001d049003010200307840d0360084040034103a40c003401d44110312079101c5900341c07820001e456020f07045115001060480419020491540401c0c044c0042507581d4981002000460701e600f0030036043c1c2105004200410700c1101b103540240200060003000c1c03c1078100607007810048428a0f03004040880300b030300d045402041d0000c1091001c0d100b0041d8540b079105240c00c1300c100c40381e044000300c04400c0a22503840d01401041d0020302c03d290100d80142c40d03001050902c05108071400260f9111090007100e8940b60f400e0700c3c02d681007694100164501a145e004254401000058000a0010702c030119144141e0b075032045290007404544c2c2050300c281032001c6075120154405c99034a864100c03041e0003140c92124004850f00d8000d01030070503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 675194856 1250 675193606 675193613
    0x9140402060f07150903020f070f062303010e0f0c070b0411120111030621070b0a11060c070b0a050402150901180b0c010501080d02030f03060a0315090c0510080103 72
    0x50b0300660103031000ea281402000006994201d0080c0204024600411003100758500a032070075110f11000382e0306400800c4188079941c2025001011182e1600d0806a00014249030001c2940503c040c4a820400000007003102c142c0d0b03506c1c560182c0320403000166560394400b51380c0501d015a01d0000e055485000100b4080f80d00d110f24010311002c0140103a03040780088085908540c0c845003441e08042010041146074a0540911400c3d4240302080801a070174008840d600ca0400b80140c0310454004070311204039502c43e0355908e0900c09031208840b010704000e03074007602640180c0c0c02120426000b100041300c1d11103e0054502a590143c01d88560710700812062481d40c1100c00000c0c104490100e8a02c0300324903080c03490000b00300c003202407030303445641c44190703800c0d01e2058024040691149050f594a2540001101c10202508601a882c0e0b100d100014081d02c000764005061140f60b44410003400902d9071001e01c03010b1140141481c070a0752001880024240380d070403a40401c40d80401080030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 675196106 1250 675194856 675194869
    0xa0308060a0909031d03010204120b091606090311011b0201120e0304032301060602030a0c050c04091a1632030c030708090613060e0f030c03090a09140402 68
    0x8030000408010a26844055842c2122480401a0005208150021600050056a0401c0e510f00358001e619060401000c441303d2030f6603902c000d280c815030000103074082405014140300c203032041c9600350500e0354641c0c00620032022400281c03455505181899030b00c0d0700940a100715101100c40c44105890603400660b100340300c2c1510000780c0303500c07103041140b15501400284040c620803a5549520280400000b41c090020318042001e81c0c03508406105050b00002502d000da0030502d4040402c0411785001e07800c20b80121a40c070380040c00c04100e40b08000419410013154681044140380907500c401045c0c11541c6c44541000100f60440700e02d540481d2031021a02d84101e8120084040c40c0c203d10300c1d00c3c2d660b8230459040390b942c4008001d228016900c2a2440d030085083d10003028613080c848000c03160000185801000550340c0c1c15a011006030500c0407458150328901580c2e100c0340f80d061415140c0c0c0c00402100d01c070360706c0400d0108100d840c1d841180003500c100c410040b029590707a401e0151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 675197356 1250 675196106 675196111
    0x8161704020d080a02031b0106030b0115030b0904080405120d21091b050a080102180609180c1308010516030209060708031f0602010513120908030f03150a080a0308 72
    0x1c00140b420124808501103a0003844104255070003150788102c00d0082040c00c0c0c1a00e442c000c0c00e40d04222040021034020b00300c40c0e041d50302200d0418591800301d481a030091100030303031003030300920001c04000920140390050701c202c0b08203444034200c1c40c1c0403018103900c076090010444041030030206c0c2902d5144183c00b10b00d42d88150514005403011890702d4042d4401075644400300c1c601ca895034140070505100680c4402010000300950903c0300c840302040c0c10980c80804c180c02b8001c0890368607426a900343d40c00303080a403c10400300103410240c0380d00302c203980862007444400064802c002401c110501c1400d104d07640b80010818082c40c504003c4019500042a00364026000d10040000c01d0710480254010442400f95560172801c190300c40564102030360110040d0391411041002310f52040c005c1d1620954014101024040c1b140c00a49450b881e5401600c02488081403a40c580800d6600641c010a0810f42c00c05960501204010001400340540c2d140360304800e5803180003d0080c1b4810f078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 675198606 1250 675197356 675197359
    0x506011103090a03080c0a080f03010603060b040609060e130903020606010e15040504200307020109050d030903050711011b0c0f080a0515372405060c0a020612070816170402 76
    0x174004081a183c08c005608581d403144242c55001004105850305445090020314018000500340751030000003904050241c03141d0383c00d20080400381001c0e0703610030b024140003160040c2d003084640a0f50030f00a6482d1030494145012038002d52484025241c40d082d48a540108901d005203000c6c00d150a100150040c16900c0c0c0c800c170a141541c42080d400500958403c007540da00000e40320b0300724104146488400c005107400c0c0b514142c0504003080c0d02404031071000760840e104880d020140801260700030820081c80d00342e00c00010a00c4108044554000c08a4807ea01080341c15900c454040381c0b070300780c0340c07030001e08590045501e03540111411000c254030450341a00076600d0040070700d0070785003c02030741c2200702045035241303000c01180e603607100300303000e10f1f068002c0c048034808140c0c0c81d440d81c09030038015503100302004229223100e0002081424010380d0b0241845403116a400ba0240b802c510564141001c030315200c0016002c401d41002d041c4464100380d47c1e4400705010090605172416010f001607 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 675199856 1250 675198606 675198613
    0x1050c1602130903020604031701050a05210d0309060e010c0f110a020607060f0515031e03071e0203120703050d09152c03122206050a0506011103090a03080c 69
    0x5030140340c2d40d20501c0e000c0f500940140c000e625017840c0040c040d003100703480001928244001408103403078a40c500420b0f1501a0341640301540e0480400501c114103041d546154031803031416152041e8160441041d452045200380908280d0404450903640c42c4a002070000c0c00e0704e01450742c02480340c05a11003412f02081524914400758020600952040405440c1e003619803440ba100c4101e1449815405402d000403200440e205500207510780b51501c405102841c003602101a40241c00c1c0f04076820b050b40900c0c91441a02c19010308110400340303500c160311900030355403144003042100d411503450661558502c1d15001c1070001c07580003404018019203a03802c3e03084413116551030a01c912002d501625190720301d4411400c250b078000000007800c021044e04140a14240030104040c604e40080b1010b01300b41c603505002807142001130072050042d1020707082c0b809201d2070345825072085014803402c0e070310400d50701100300c1500d43c1da01c200207003030b0303080414680b00304086100305001c0c0800c0000482034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 675201106 1250 675199856 675199879
    0x20f0906060d060303081915050928090201080906100b071406090708010b3c060406050306090708130311122b1b050c0109060c030903030b0301050c1602 67
    0x1007011100513400c00c0740406c2c2d032103041c030192030000904c2810600e02a07405009002c0c07814404400c00780148120741c090319100303010402c1040038003541c08170910a0707003900c0300c81c000048000b8041c15120301d00b680411010130220b54003100c0031a516110b42051211b0b080180c0c580650038405500050f002d4440440c1e0410405209c1818070855010300003502c0103010743c0d42044401400c45140403903041c40303030013030568900c420385008204415846021000d62f40c40030218815081c1c520f003129110394011800180030800d40d0700300b4041d40c0150000e89100c1714a599002d8152101ca00c142c03100180441c20403000000240309507450284614000241d070040c100300206280c0d60313081982c4068017903c4030041141d4020014401600c82c1601d0a820301c0300c1128408000004d01d0f55403950420031400103003503801040700350000b1000c40c0c0d102800300040040002d008009010700300007140005e00b440d2401c45a8a0140945409444480c490a00c0c1403a07040001c046451080710491300480318a08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 675202356 1250 675201106 675201127
    0x41103030f070311010b100c1e05030703020d0f09031a151f0201050a09031b08070c03140d020714010e0112020d0603031b12050c030c0106240507020f090606 69
    0x3404900e0f01c2500c4049020911810803400d40d08980100da02810414031002c84055010860040084d003101e40c010704451000000120b080440b1401351443c40b00140c3d100405a0011b00c00d010340310660368100d40c108200504441c08621448050940061101200440304c000144d540c0c12090030000401c1c603280c040082801050380d903000e100752407540103030484500d4083c000c4562041c05054100646909aa00604003054404000712182d0000141c04100528030007101c0c602900030045c1c000965032450500681c818030102d194003070050100020b030702c500000f4000c1c280c0f0b03400d01550070102c84840045952a4a2500281c10406598954007035410f8900c0106000700d4039950100e002421403c0c0a0210507c8440384030300e00b0400c4c25400c011a140141c08120422146019540c528130407441d14a075020b03690210140d0b5280004c00140720b0b40e0090040000c10244810714825012010262164025501c010f0340005c1e20402d49507541c40c003088107a6110300c0c000d01d940d050000f03081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 675203606 1250 675202356 675202387
    0x3120702060f16030213080708160b0d09031b05062e150311070507090528050c07021e03070915090209120607121404150b312304110303 60
    0x51100c200c54011123010702000d1000c2c440c488180308029120304071145003148848042c440c2c4888115015614080e2074100b5202d19440380c61004000700d1054004250b0070f02c20389520b0280d0301c40100b14840200d000040214603c4104481c1120041c0201c40d40f902c0700000c0c2c3d0350b211291600c2010364810391a1a003203015806006624000c10040071400d041201010480318098805412003401040c0341d00c3e01800d910000411a05003500418251148000001d43c1e0052080080d44070800c1a039180007810f00512588a1020032021a40e00030355a0b10340808403a0340c0340402109000c250010302400400b5001040d100703001901c24440341001e400d0550034520103907200c8000801c6102c01c09001030060081c120302c0740303048400f920300741401c3c0d40707100400052440c101ca400f6250302d580d4119a0b1404260016600740d100d0020000e0a203d501608001100c234507208610f16040a00041e0000c03103a540502c03030030750307400c50449441da915070310010810a1a500d5252100f001010f10285982 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 675204856 1250 675203606 675203609
    0x50f0d05151c0219151d06040b0f07050312010806070207060f1710030204050903030726160306090513150c09052115190e0613020a0f030503120702060f16030213 71
    0x9588060010010646c44910900301d210f406100c1c820621050040f00c0c0d0f14012900d2500c03152001e907907620601d24110381107018820310364060390415000081d55010205540d445141035a09681c880c94030786005560713500300003c440001074101414011104054440302f60480713500d80120003080e581e0360004060340d40c120380b0402c241c0c101100703102038550400481b01c40c007030034160807100c0c0812000100c40340c10b400404661a802ca1102c00342075090281d84100050201d4071028070940c07070224403240601401c280308541121030740d56078600844c2d4a100300000b0300910b9070740c0c0c55141d10700010069194a4621000c25603040e002005594420800c4403000041519101042501c1e18078020310441038200024040030b800e0102e0320040c080c001c500140c0c455050b041c4440301e4405400428040380840c1c1060903030b209c450300003205020001004c1c02510340c04a0148010b40d50b041e004036104c48081d55881400b04510300851420036580b144100b010030307036140050400c0d5110242c1c1c140b00c41103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 675206106 1250 675204856 675204899
    0x10e060c01090c060509030a03050d020912031e040e010902030601111005040309050d0b07050f0909040b1515070602250c030c14030319050f0d05151c0219 68
    0x12203005400300f0848a03032040040489040c000d040030f482d02e0100303403203070400781005041041c0094060300e6800c0e2170341a50700c1c045011b40b4203014188015083d903929030159100869280d104040002c082401004680a40780c0c405071114841c0d2900100c0d401035040034003c1ca0500c00800d400c624811b00411440c5901c00b29140041401e08207800d0180c40f000c10307a00064014807001441c00c010440318040540c002c041480c00301c1e5903429400c100000c0e070043c01c0341e190b40f00004505000038402444805402204400399510408001900700010910410201c641d000e20038001003000c01c1c4a43d000d000c3d601e9000e4102c19241c14a10101c3c400070b00c10940840300a103101c0010b00c18402c1080500b0090054010f42904c003000701c02c0000d81d41d0040c0389500d44000c00e14090340030030034800d1082d00ca40c043c0c449070164a560380c0d41090400391808480c803912040c81040c0340c410303500d0300350500305200495031603105001056809011240201c08074110050780c0b07082000032040500d841004429a2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 675207356 1250 675206106 675206111
    0x1202040929010e010e060d03180f0b190e090406050c04090e010e060603010e07031b38040b07140715030f0609090b1303020c040203160201141014010e060c01 69
    0x10103110f4400001c040e00300d5015501114100500d41d100d00603207001076501070a16806030307520380717003134000c04c442c40e41201054180703400c000140c04152801401c19194140010500c0d1107844030216421142c00251517030140314240401c0104015070300894100c2440103800b45480d0300d414a1130103407055041101d28a07076441442903140d580a00003139400402c1103009210140c43e1820003a55030308036001c00f4022400707480c0e482c0c003070f00200e01440d0300601035040c401c8034000c51078809130036a04000c10f890f4220954101500000a0217a08480507924aa00020304103809a1130b0402000c4071743c400303100284910310300810400c091243c00710903003000b030790007244a454068801082d030398103902c40350100c0d0070008481c0c0000c86210b952039000514039010304554607981401c9203804d400130102c0b50132901c004103110f0b00500c10003802e0801e10301da4001b4000d5003034100a48080d0780044450040d0b0000320001803050b045909020412840140360546035030180030001900d079400b45034030b030086a5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 675208606 1250 675207356 675207359
    0x16063903150608010612061401050c010216050705130c0801060804050102070f260301140f0d0606061e020c130f0e03040f03060612050303060918060f0103110a120204092901 76
    0x107903c00301c2441582e054007411f105d40740c0307490080510b00041c00c2805050081c045500c040d0b030602541900c81c160f981a8070705020300c03850f04007161120912700a40d40a50414800040c100311540105861001f40740d43e0495580c0c03030108103c03010344004d441103038255001c10091001c40c264004910309070380140c264204000c280c214001c9007030701c02c210201072a8018401080b60310024401c0c0110301c402a103900641144640004140395442030000b01031a251010114105a00c4540e400c918070744507050904030b000c0301e00b0581c0e071804c41011560740299500380005035034442d41c1144008402c0c880021640c001180c0490b030568106800648032040241ca04000b0300059014510040490314001a0540b105444007502d0340b0008095600a41c1240041800c0e03100f10050301e08a58000020349055060108000315031407030a01c0240d882c1d150103a41203403145000c5c01c2c2a022900c241c103145409405690900c00a00340712001540e0000500c164140810700349007096900c040c0e524174480556 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 675209856 1250 675208606 675208619
    0x30c20030d020705010504140619030906050705161101140409051e060d06090f0213140601020f030a0804051903020d0f05090627061606390315060801 66
    0x807142419840840d444600100126600402140c0903584101c10003000f0840d5000072501500c00c00f6443e000f2180740c803c41014007540750303004000140c0309803820f115946030b88908480354006d8603182c404001c403601b1004005002200d41d200160810704040b43c525030711103079a14081d0000d41c012101300c0d03110801c104d0f41c048115000c41b4058104402251241818000701d80c0043c04aa0b0090806a039544000f06001050900d00540c6500510307103020b2030540e01400c40580981300e00d400c0400d15900100702158004501a07014a40d100c00450370701e030908404503200749001e4400c2d102da014215990111440a00034800c4c02c40c000c1d0018624050b1a010050454001144007001c001047c8031600060751007404a50a0485403021015546003c40da030703c000245075a00d0300c0e4020000550074466003902458a03800c01d0041400b000109480c80e48804561040c44403c0c08059a0300302c5030890807428202d8502038451803800041000b1011220608440303643c22042c0840d01708401007041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 675211106 1250 675209856 675209863
    0xf1802090f09120a05041e23030c010c03050408060709060f0318300809070506070b06060a1b0501090b0c0a02100b15040e06030607020f0c0904030c2003 67
    0x1001d550006000c0c40d1511002d0320b5260448802d00140804000681c1e00f0304c0b5100f035081e5006011001e03900d0ba00072100c82000307444019070344900d090b45075a100b504a580740a0007481101810050042e028241c00e010045644140c504400c44c280103007070001007480d82d0104a00c0c0c0c8215a151613409503107040c0b02c0e01820f8920340503039031000c050134062841601603000d07040c15541c0d640000e004180e400c1c54240a0311845040000c500c5450094032811102680414464040c0811500b43d480f816110002c0c00428401c0000241400449401148090401100400541c02c0c24a400e401110691081c441200401c00082d14180c1d10341018105105515481c147c10912a2a28520b0500c001e6006074484501e1040d043e50f440d919501684242c0307450400c000503d0360394007400e0f9515194200740003021015a81700b8080e20600c0000380c0c84e5400020180c00000c50b107001041400c404100f00840d206c2d00030000c03001c00511020800000d1828101500303c46452081d03040321070413803c2414039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 675212356 1250 675211106 675211111
    0x20d060b0c0a3509010c080c0c130911151611031501270f060920030402011b030c02130c0e030309060409052203050304030906030908090d060f180209 66
    0x1d500c0100c01e4034045084440c2a04804004083c46083c1c45034520700050300d418071007400c040d10008000808220044020403003c2e03a1040450741d84040340150b42500e400c0719400400108200d400600b0118107140c0394001500c54044000340503d4424841c0158080700042d000813502001c0c200b8101e982c0d40740c00d12019080c06c0080740d10f420158500a041480c00b110300d0716040b28800000300c08207021400d03030811000344010000502c110f6a6689a43c03000301000b401e58450078054900c0312000d01c500da003c99000b50380580d684031111102094038814448080e0046003801084001940142c988803022024904600000034a020050310082c06604201c0000c41c403941041202d00310031b59415058a050b51510b070f0f0001210390703c22071002c5c1c21100102c0140d10508941800c2403c044e4801d000b580328511a980e0081d01580c2c96800341c06030361104100515111060000140340d00b82502011519406903101051410034a614a0121425003079010031452000a109081d41059801d180c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 675213606 1250 675212356 675212393
    0x207020d12110102090603010603020a030f1107030210150303120b0907031a18070c03020a0c0915081605060c1615020d0c080d0513051006210308040204020d060b0c0a 73
    0x42c50000700354001080c0e1f02c4140283d40c203140e404100b508000740302e0350020044560058082007281800440080c10740c04c4001d0441c01132103005066450103141303000d22180004540c002009150540e601590104040501150032076a10300f05003180313580d4102c40340d000d880319843c0020010204100d2440d0010303000e0380c1c540609400759080c072f801040860250392040705458240415003051904034103008200030080d00210304108049410a920745c091061b440c02c0d4400b00c100c40741d40c0d81e601031b190840d50070b40340403480c0003a4003000141449401408440180c3d410350b07036070000d03145000650503813581001c142203007507020455607950104211801030070036081814041095503a0340001d40301d0780c0600d914042d165008540384141e207994228603658071105880e080c0e0442044d81340100890301c641d0190000000d10b0083e62003041d104d0b0304840e605940d50100f55070710390b020301000e9840070407840003959441e40d0000e00d460140c4080c1003148241009000700c030301076090010b03201000c4003a55 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 675214856 1250 675213606 675213611
    0xf0318010c0e121207110f0a06021c1403040c030204182f0603130501050106051c05060f030d0201020d05070905030615010e1e1504080709050a0207020d121101 70
    0x1800c854000d20000b106401c2102c0016030050fa034440d4504003a0703070700c802d1001c04002040e0701d001c100080c845041ca00605841c0b1480400c0000108494061030b031140d1809a00400711402401c5020b0b03030079086c583c0d414240410215810072140d0b0362030344116020380d044030300c0b184248114a4140184074850b014041c3d441e5010b1116241c2c60000b46405c080d80643c0c6c0c100307141500c110281552580600c2400401d0191689032001d1080c21030141c0c0401291254170700b40003c00c4150082081d1880e040c4406102d50f078107004182480000d050240c070840c0c2c0646002d0305108143e40800c0040203582c1680c2c009610358017001620003e4500107000d40c0c2c14000700744c0040c00036403400958958003845900360001c030350000000584087c9004008141c0280100380c1f000008600038800031702c223610030b4174610a0016501a81515800386004170f21840d0005441000501e03640d03000760b07411901001d0300500e4074526a00180c441c2040030012920602d0850120600b01e0300700350809201c1300c40320003e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 675216106 1250 675214856 675214871
    0x28050304021e0f0f0406120311120a05030a020c1c0507030e0a080a02010804150f0506030c18180f16060807050c070506030a18030e120c03151b0f031801 67
    0x19a03840f20008465010f0203111184070303040e0350340e9000701d0010b04001000c03009014079800c00038080b1010a0b582d46080c401c451041060181d01d0049800014080c0d40b454103540340c401c8003002950060b0900300c04c501ca01c00041e041e1625807800301400b55241d440701a620070310340c50090901000805118801c400381841006500c201003841c0003803590900c0c11070303618bd8452820820a860300040e14240324640100c05811090036440f05014060403002c41d070b6401000420444c41004502810304401d04200204103d003040c0203241c8080c0008401355501c1101591046143c9180300c4c3d003841d85003d040030200311303080e082140e140e040782e40380c90070910308940784034690b590701a0f82c4038407030003100300000080c4585283c1e480200c1f05e5100d202961024402810005c1c199a020001c1c1442160880340502c0351740342c00680407801c1c82c40074000e400d4072481c0860180800c1c0c8020680c9101001032003641440b01c080d0300051146034204a030326522400d00402003e40d5501d004100085d43c0e152059 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 675217356 1250 675216106 675216109
    0x21b01150503070f03030503100803130f050d020d0b1e0a09031b0c29070f05010501050609180601030207020315040c05040603150c0509121b04060308040b28050304021e 74
    0x513140e007a0f9406041c00c1d81d903a144c0c2100048d8030074007a0310468507800041500340000490035400400c968050b4003014640b44c5900801145800081c0000c0d400480e0944490002d40c07a050500d901c00b00ca0b0b00d91410310710a000d66103482400860b403940c00695540c1e400701c201034200e0300c890382e610305880306d103c20030b80350741d581001400c03050140c222007581406042c411100c201b0b040302e10511841000715200e404918040243d0440762600712402d50801c4004034446c18140d055503d03d043c020000c411340e1482054090b00644007030155810103408028240140e01c00b003105440b0410f10356120815403802e810010800c41c03240d041503208a082140c10404550b00700c040c842c0c6020788201c00a0b40e022043d5054446d44241c503822a0810002d0342c840301c0c070400110300703031154040101100500b860a5010402190840d000042c0400c00501c4188400800c46001e000d040c1450a00c40f002422240c100b100004400c002250001c0c0340082088214102010501c501368088050f0b00e039140010070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 675218606 1250 675217356 675217379
    0xa060810090204121b0302060409050723040b0c010f11070510140403030b0d020301050c0a03050c0705031e040b031305010f09120c02060403170901090f0506070206030406021b0115050307 82
    0x4c000742900c00300c0750490070803010360030403d80110341c01803505984668071800203024000407110311012440700740c141c41c10a00e5041802850350428509503217000e0a0491665140d000140004101e40d41c0b0318800c0d843d0b00043c030940d111910b0741c9c407074552510100c3c82e29038034045085805403000d40c10054034609842c048034101e50415458100807440b28001c40c0841d90000741d00380b02035415800d2100344501c50f440c40c0001c0071001c50658060220341d0758048a8187c2d0300c00d00100500c240e00030407d1011101505d030725800c1410618800500e0960f1752313244204a9081554602c4c4079981c0320442c242041400d1260190030803400c64103100708111510740103e0f00200b24006401c2c002c2643d003207411903568800302d5024640c460f55000c034400301915003400e181c010245c514007103819150302099100000185208a81c0c0040c41c5038501202503003404040c0d000500101d5140e502440690440302034207803000100c8200c14000542c801940d00007050240240d44101d0094126010510141c3d0724078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 675219856 1250 675218606 675218639
    0x1b02120315030a1b080f0c090c0c030418020409061409010e07020f0604060606020712240f020a020c0a050d050a06020903070503071502010c08072007050a060810090204 74
    0x114207580300d44006070209090600c07101d0018142d071040445034071001680010881a5100f00c0221507000080c4c41c1803980e617201c0404110b40c4100c10700b0020341d144082000502e00004400d050320305250369200368035051840d40107024413082e00401d090055070014403610300100140000140010490b40124010050602458042500b410f0014020300d0003040345501078424981200c0d8649003500f441d40003001d5500401006001e4550005061041e850302c8440c1580c001a82e04801c1c450040c4e449500d035284c03040041d800303464a42c070141c501d01500c054083da002540140141402c0181084a001e800b50441c1d031040f440d003109200402d00010b0b402e0759070755011310010b070b4030700000300001d00e45062030f4031296252107550f8000c603490340602035442070780b0641d4009101c60501140161003038802150f00340d000511100c0c243c05004450f24006284440c0300054410b03494450b0003091040180740c000b10081215503040c4a218544482904002c2103461811804c06090849605084d50703207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 675221106 1250 675219856 675219871
    0x31404051c05011d0109020f0f030601060f170916091506030902060706020a050a030b041a010e0114030109200a0806150c0d21200c0c10031b021203 65
    0x14034100710104107096000c003c4c05210500709258441142d488030340a017002c01b40c100d010703003040c0300041070300d060100d0b41180d201001005091142c0c00d021040781c2c800c515000140411014141205a01e1030111072079003d14410300117004a218a0300386070f07401030754580c0084100c81c54211204081500c5070305403400e032103071858049002c0f85103000051003801400400b40070035100080c403c6040340c00c14001c20312100152400e0200003441c1c420003080703540541c48200c003113038885003806e20781d8464440f96030364800504024401503e440112091034109030007070b19440760b42d07654014641c83e944012011002ca1210b81c01c1c5083c03400711000740030301800740c5070318002d404044440042034119020386080300b080720f0407508100113031003004051400d0030101e10200d000c1ca05850301508800c0c0500a0b0707100404c0000307010240c1d01811100268000c0501d90041d00890241d6051503441140a4480707200c107950104010300d01c003c405020b0b66500f0100400e540c40070401d196440700c01c0041d240d00010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 675222356 1250 675221106 675221149
    0x1503010518060c130503010f0b0a0b03060307090914010608061803030c0d090c0909110108060301020a020d051305091f060f090909032a12030b03030d0b030705060a02010903140405 79
    0x403034000c0c0d0740b41e011485c5c00a641c15400c204c0300210000141d80440c4155000721850100241c1d5503c800030584420794419815400c480820b00a03d01941c00c0900c0161080d945020490340c4c52a11340d08662240d0802c2100c6d4201000340100c0310000801c102e08844c00c075000e540703141803901049016124220000d0703084c0f500d40080c48180207030510b2410040809802c140400c0c82c0c4c44c503101c00f000e03031000013036804220010b02144580c1414426915950500c2e002044484080f480c192580e070000351840c21851400b003000b192507110320041034091002090b010310500c3c0e025281c03184080e46c40e0070910410440c1141c0d40040c951004400089401020000030701c403000c3e0504450810300c0d01c42d80d4158408a0310103a11080f01c1401d03441119000340703079000f0020720452046064400340c4c02c0881d45035109001065401550b03600c400b140714402021285ca0f599030703030f01041ca0790300614210710150750344100642c01e15400a00e5508814140c0340c6880c03810742005c00080c202901c3c4110282c1c600c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 675223606 1250 675222356 675222367
    0xd1d09060f061e09101407020906130c02060613020c070308030a060308030c0a020c0402160b0a02041a0a020606010912120e130f150b12130602031503010518060c 71
    0x85502c0c0845a071418400d10685801d00f810318601060780c44524018040c90455054130040c5110340800151004421020703841c1c901e158007009401100544038680c0484002d4000450241d144255180c40c040c1d80c000d01014602482003064071000c7c0383d00c0c240400d0040003075084810700460418250781d4410901a180e44541c0d50130340042105070070003014840004288214101102e0103002d0f485070560854030000c0c14542444264020050049041e42c0e03c503901c03c0000e00c14404030390f8000b030b1150005052655030019210514040e41e4001c0500c0c0b00002c02c0c90750580c0c140a10b642c040020700300241e01602c1c0080c0c455908403240005040c8416155100c10003a00c070b114030260042c2e00519a01280b0001c40444e4010700040039041401303864400342e044880c1030003c0e28021606410f11460034907105100c452203501d001044906170410b103000c0b80002400034406180036410303140c0d0101030040c03010f0515023141c90242c001f580c1b48214aa400201c1c1c400052280e501905100c00c82d510740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 675224856 1250 675223606 675223609
    0x10e04030212160b0604090503090f04090501020a09030308090606030a03050f16150e1603080c0a06090803061309051b010e030a05060403020c060412030521090d1d09060f 75
    0x11100d80c00b0000c2c50344000034180e01e02d44161101c600d039903000e82140b00c0c03180c0300c200400040324882c6400805130b80060241005502d000c10810a21150260000c0b800c1680743e0f0340c4a08a0348404078082c00f144038408140207050380320140d1940200442c00a103c182840c81c00a617072210801c0c401020410005180c240d200c000100340d420b401113180c0c41d4400b583c44d910301a00c1090031322000a504901d05486485030301c070002071a0b0201c9500c0c15000704e10a09540300c8101380d601c000701c80b020500c155122000007400d2031040340d0049014403419601d030708114041200b540098601c0d0030440d821300c884a40460030200780c0d02c1398604510808070222142400589600601a00c907582c580614031804050240108000e48660300c05c2e403d0300c4600c0d202004121090180f402241e602c00c4540214000007030148000380360f06020b201e4074000d0890304c3c80c0250f030050340c100e6081209030803c1e00425855038201d43d000030704c10000c1078030f15100c41300c440204100c80390040101e44280320006001006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 675226106 1250 675224856 675224863
    0x50f0f16060207050d140a1d1909051006170604090629100309150908040e0705130603110d0906020d090c0f0b0301050105030117120d06030b0c0c0303010e040302 71
    0xc0a500c10400e5403035800a060450b22602014003180100f59501c6445881c1400d08003102c03490005a100c042003084551242d03819040726114840c0c111100c420104215180800010f005000b0b00401082130700e065000c00c00d1660455100800384801c024541c2c6240c3c4131304144951120080c1d60000c0c403038800342044400b520b560060b0340300e201000b2407000904104d0a096113490801601d0025201c2e0b41075a04508071070210b500505004028210f004020319181c01109030180264019400c0c0b0b619690901010b54003503800502294000400d0b50312041034214400c000c1000f828100840a540b40e03119030240304403c9981103079640e9aa400003084000d0f410f690a100652104016018032840e01400402c0f0a005034600d42040440c0000c000c1808811a41642c0e01a524141980d1a1145000302504811101d217618051800031554089041014122080b51020040380a500d5400d04500d1400084c0040380c014000f0405182c20000000071641100d111310040c00390740d071310b07418201d08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 675227356 1250 675226106 675226147
    0x5040e1f060e0606030c030609090f120307030e16052206031121100504050c09100f0506090607030f1704080a08130b010510120e010f060501050f0f 65
    0x4203400c0d0403401245800c05034014815038602035425036207501e0b8441080000d00003103502950f514001c100007422804c0c00e400e0950011b01c82012994000d0b190308038030b800c00d1543d100440d0240404030070840204d80c54040c0341514071600000d40814414604c0a201d4a4428040c45010781d0f4071250348060f04040700030142a24610000400031541c60f413a2039943e25050300e5032180700d03040c0ca140e07a15107404101d52001c1074004d094010440741d481c50540c0c00c060500100152114000c03119861081c0d01e440c841d19204603101e0a85001c030300d003004100651007079079400160040c070040c0200c0d260f40e10b600c41200d036403a806082002100780f2102007106c01100d2601025103491043d02404100600320002c0c2c6161002901d07007000703541d141190b410144035054400352421007040010410f504004150303690303001e118540850000c103101c040c1d0050700e031070a00c04440d0740e640d0030542d0303840c2d161403066002801e001d10b00b103441c00c192450190128044da080b4034802080001e6000ca4400c40c08404d0070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 675228606 1250 675227356 675227383
    0x506012705012312010f080d0516020a030204020703030e060a060b030609040c0b0c0123060607141213230d1209030c060503090d081e0a0209030307051605180105040e 73
    0xf0f680f0b5052010740c2c0812003080c8241d072001b104030712020810403000300381c0340b2441200d40d0700c00d4107164008110b00c00c405854103045c0e0304901c200358040051f0702c580c002405802d002c0d8401060706507004258918180004004290461420800f800003c0001045035003000b42112440e0407071302c3d54200f40d281420b6643c40f080382c00900052008100006400c0340c0400d603000800a5000b072246d86807030542d510129650b82e4000c0c000c002c80c000049018040076001c02070142110500c018055109607154005058106a03072048d92041042001c151000c50072414054907001e50140d04001050b00003860010040242c1803000400000034411801000110340000182541c1a0741c2c180c00740017507005440341e80d07050085007070300c00c003c3e4000d0034400c1c0100343d036140107040d0f1080da07a040043d2020140544036440e400700218600303541c0c00c2014142c03d82c05007000d000510041d00310380c2c401c00e0b10781c6e20150240d03403404000300c0702d01c8107030300080d0444c0d00039076002c1355100e400c105139418080d0549006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 675229856 1250 675228606 675228677
    0x602131403211b06190b0108071b06110d11090d020904050109020604060f020d1d0f1c0c29040608190603080406030e010209030a1e05060109050601270501 68
    0x30445000d0014800f07018110074800420074031048003246082d2440000c6c1940820720003070105102c00c0c480c0d0600c1c40b201080e00c054032030400d89662850f099981e85421f01a00c00030200301240d03062950f20582c00601e81c403100043c41e00390b901c1c011518030070341d860011344503c410350006010b0140039001411401e80c000d14450366151180005010300100c10070050040c4288401c041210f170090314940c00409500c4071950f00980c864007000700c0758a42a11254015070104038614151382218103a1240b2442581146150390419003031030518222680c002e40c80c2c0c1d005000201254044d0421501a5010740c600907619030360b01420003a031170076046c015952103440c3c100c0002c14003103d800504142c510954040c08940130544820342030340944034140781c1c5038002c51a42c500080e080b484940c030207103d151903001e0902e410f80b5050f092803826442540203a46440820460b036034032442c85080f050501040694200c0801e141030840f106034011a0b06004a00c021085403518003d548141d5140d000c074403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 675231106 1250 675229856 675229897
    0x2103030405161d0a020a020c0406080f010b030303011802030a0209031b0a060c0803360a170408060711010209191502010207210912060213140321 64
    0x10b42e245200c40000c0342c0c00b620200c0200d4148103090652468560421003080e00c0c0d00c2e0241d10000941c400071000d420f62007904240c6280782c0350780c01420010020070014260308489440c020f4251500311a00740d104c1d07041000144150800d000c50703034490654a02c001a101d9a92544080003131082e8400d140c1e1502c65003026840904514900c11454141075591a001e6075541000352a505651240241070110500004120303070103000b0051603030300841406d85403045a24803c0f088021825000d40c0309034020070003800910440521010700000c0e0841a68034141c034195080d9180d020282c0444108500e807141036401e07072400d4066851806005102e0142d21181d40e18820515889100d400ba00c0384c00c00300c218032014018401e6445050b08803241800b5803982c40e070007690b0300361007400300c0f828400e2809003c01c65082c0c00080403185442124011f913503004403811100c90601680c080b001c1c0d003800450000c10f68801140d0310b44540068810780740c0c00001e0427501002c9000c1e10781e0b291132a4119442 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 675232356 1250 675231106 675231113
    0x26070c060c0e15070606080118080d0603020a0b070c05030304030201170907050910080f03191407081306030515100c03031b0309021011060f181618091121030304 71
    0x901605111700303420024180e4503200d1a00362601032070411540000700f00e142d004555400003c0a0100c0e00c1080004c402e500c0740d00082c5290a2600200c011744000300304101084144003214020b401c046000f1030801e49560b000038203c031a0781a0381100c06003600040783c40788004002800c05044001d100254502e408a046204881c851040741c08601c508080d41200b10404421100400c42c60752a404c84007946540645900003c5908849000010000c03040840c030410090a040c5525000c000110351400b40f006080d502c0251541c6001084891000b211f507444001d40d4410580c5824090180d1490341400c0d001050b181010385140440c81c8449104c59515a1100075140e04c2100e46019488607031000715408540100c080703610350b01060200d0704044464144940c41011400c2201c203440c511003081e41840403000e071910000210360024441d800d800380e840600c51801c034400f0850f44c40552034401010455220075030061100d815003000303000c0c66452003600e410f02d500403031b55030381000d15 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 675233606 1250 675232356 675232399
    0x3070515120c0a320304150c030506090114100806031e16120b071d100807080a0c090e04080f040b040f0b1c0c0306090c26070c060c0e 59
    0x712a8400118250711454858420820001c003240754000368a00a80458101d1403c85e40064000d41d005074800c0318840c840340301401408041496568003003403d0402e8020b000080c041a005595030314507440803d4456110107000e0000144107140c0765442c4c0c0c5a0700003003400c1400c41c000001981c40901110510700c400000d00261895440d02c0c176880499a9004c11044200340000003801d4080110204810341e02c20281c8039940c0c4442058600745c014a400001c00c03815800c401c1d0004a0303088030420591980007586140c0c489010402405102c4041800403ea2815409000400441c40000c9818001c50394160f032000181c460711155115201c2815551507005032003a85002d1049140100da004225808d40e9120351034442081ca0400e11507007114003620b05c9030040010143c0d82c00c0005214003140c00794226031801505d03010309812030f1403680b8440c122542e00750030011101409005181e83d00c01c200000700c0340c1102d40058200300c8810112280311041c52001e0f4480c1010440342c0c01e4044c9807 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 675234856 1250 675233606 675233617
    0xc020a0603050402181b042303011b030209010203090406031101030605190e0c090a031b152f1c030f0e0703020118081b120705030c06180a030f02010206011403070515120c 75
    0x8040d42481c40c42300108050136516010b00c05114007418481d01c008450080d00030740908001401600c0c1844001800708044a1140e401511080c5200920100c80c0d6058416030000d080c007515018200e90806018254460085c0b05605111228000050034500b00e48140d5800c40f9008004404e155502d003021000641600e81c5a80c000080d0000000d1079140e41d240c003400005261a5140c500c8046092555069031600c4a1040000d5541004409690078001030850401e9080086070800c448003004003110040500144170901e0b09060144c07a910010380075007100d50901c0e01051169401803211181e0b581ca511030304c050700c60301c2072044001c2c041482d64200c00b0020b664818413040703000c030000d503960341c10310400d50190400e101c00704d40c904180c07008220440c200c0c1c80c00f200703000003a00880e404540c15803054030540501c18401003150303814401c281c010a03a02c07038501300001050380001d44800f003e00c034491298a004000c00710ad044070b10b09130b072911000c203409480540340c66080800c207076001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 675236106 1250 675234856 675234899
    0x40b01031b081e01020d060f14010306080a0204180503120411030d08180102070203030c062d010b070609290a110712020f0a030c020a0603050402181b04 67
    0x1c40314407491801c01100d000c800c84080c500205403000340c07250b110381c54048621501d00555020050016042068012080204192801c0125103440d0081441881c04e111100504140c02c1c00d0f801c07c1038210000f00b200d0b40c0c58040310b0005200201c80c3e00300c010314101c54801080c3c1e01002c0303440319507445895030803481240642403041c40a80c100d0105074840c03001a8a07140425161004079002e0048903124002e004010400145808000c0d00064070b0754002d888500c600d84e020408210842020f8911020194400382e038589a811501d0b218484401c1c050048041c844800b080b80c0b8103104a40c0c00503030300d49030003440c3e4403c40d031340c0c5010b4504900e10741300d58031039012900c5002c541c0c040340f140710f900b001c6203000c84854240469079440c0001d40481c80301e8981188030f05405017a2040c0244500140640300c1e448030302800101c0d1050200b036582c01c1d405181414500002c0201513100c0000c10358002c203c02441c01d0b80d50f50b410106142a00c0d06d00300303907000030700017140c0803600b000550710443c6040c44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 675237356 1250 675236106 675236123
    0xc0212071205071a0a05030f060a08011a030705010c0305190c0b070507060b09091203180d090906080a0206030402011b050105070c060f060b0906031012064b0204030b040b0103 77
    0x44c603400100c40d12415580a001860030000200300b02d5150415542012005104507811560b9145203803e45901104100b4420705810395601c06140400406000388828249144034a901d074401500501031404c13000d070440e200c2e880c84580d29100c0c100360500d06a02605104050514540052058000080c210b811500e00407084455142c01010944902040d070000d2011240c0303102c030031895400c00b07011024001d218a1300c40140e043c05024810f282c81d8685d44031131002d49407020700c07030a07100198040f8031160840d1680c1409070710741c00c1c2101e62003034080c02c10b0038050789000c240c100310301850003000e083c6510f07081c18030140c10b5001c50f56a01316030092009201000400541800302c070801e119002100d2020018504582442d801441e4031045000000041076600e80b0703a203000303800c1000c003150340560b1447c03442d0900c002d034480820b60040301240d00301090b140c04e1908203c0c0051141110f104206c0390042e00102500790101c078059030b40407803202c002d030a040c5040768050000380001c0b21700306e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 675238606 1250 675237356 675237389
    0x71203020c0108090d1d04020a230309030a0c0206090310060611061009092108010f08160315150b072906010302250f060e010b010c021207120507 64
    0x1071042c0c103c41d008200c0355002d4105174080ba00165400c08030402c11a00800c0b14003c24205542c0b1880506600d102c2c1ea2106900071850079141541c55885110b00001d089080c014082a40000401d40c1c0403407500d0b01745002038a289000241050041c144826410701c1086241800c406c80c540001044a200361035260f000125002c0707054075000101d5003914640140d0102300000b40440d080001440d0007210701ca2007000154000a1280985003481c1002c07400440040150000082c10320005007081c4018100840c02c004040a4580c1c40344409416854000c941a100e420142e01c001440248170707403a400c5442e95107003000002d81045070141e409800c480306000003e4590241da65048030442d41958055540a00660007500492841c502904001810290504010403420844c5003d0542101041900e00d8984191406070043e60080d906201c87c12120b660400c40c00d48619a049413200d070240048c0d080c940c135210056100350700801445500c2c6040c481c1c042550000c1d141c00410041004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 675239856 1250 675238606 675238609
    0x60b09090309150702300f0c0402030c04080f070608060a0311010809070b0d0b040f06060807110705040e0303040606150c060f020d050c0414030109150207020a0503010c02072c0f0702010905071203020c 88
    0x8a40e1047e003800c1a410191030702090f4600742c5e000f1640402c8100f1000d0400d9110580546404132400100c201a0b015003018043c46402101440d030150040f04d550100314155074a403191480113808507414400a10003254030307418207102d0540078168250801d501d8a0800d059503024110788c41c25103020310b182c01c0d1181f0000702d9500580d4140c6a407511169103540b83c44030121000c00150301e1316512405900d1010a4076600c5004001c0002c0c80000103580b07d040908080040b2012a031000d225500311070294145190000382e00200d00f80c00050000c0c0c66260101940d0191148040c036019451601d0104441c00c40c4c0140900203807075404403102403010302e002c185822249801c4000c2c1222108440800114407550010300342d95101401020302e00b071b621404682581c400f60148005608450814084440d030501c184d4031102d040400c108001c148111010180c160180c14500b503901c19a0002c0c5049000750000d044995000b1308a0f040240e507200404180c9007013882c114010302802c03034841d00a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 675241106 1250 675239856 675239863
    0x90603010501060806010822080a110c0306070f02010207050f061009050f06040e1606111603020612060a0315020d0c020f0d0513030204050112060b0909030915070230 73
    0x10f075065038448001503240e0100641e20841c0c024a01081c103111143c090040810001602961a1180440c01d45401505c0c0e8007504e55050707034030f02000c1540f10b40b0300c005142d41c0000300540c102c9041d05016446c503100c2042203019203c2c0f803070013920921941840744092240051050310421000c3d040034556515a01c001064071403d0740c0303491500280d4000304030782d4a81540020b42c00308094044032202002159010b2a00c6101c4e800314000c40d100d18480112064103004500c51340c0040021407940c01d0441d070004126000d00da25a21840700da810000700303103842e901a81c401a540204912008881030803c24019600c100c2c0c2012042e420301c2c9840078400d00020b400e85001500601030050040d07600c0c0115059081040e00b0402101080300000140e1500e00c200c90103820350b80c604002507106410480207440c03040a505009030324034030070401c07142004401d50303860f0503049554034041090342030351050501a1001c0039502c4212596041e00b1540740c2080d600c42c5000c4452021512018840d17200d49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 675242356 1250 675241106 675241109
    0x4031b060f0f030e160302030c03030708040902090409050a110406060f0215040302010609020f070215070b010b37080105090c040e100f030302030309120316050c100e0c090603010501 80
    0x4100c0304404008003900640285006902901d0001110344c10701844500d0109103a10200001000040900c19814144400781e41004154000d62900410369900407480c860380c82040305069011514582c01d43d10342e00442030713940d04542151030003121070800b04c1e089100d9004c1544114606080007490034025000340150304d0b03c54000e0031014400c400c0d8400208401401101155a29880462102070501c081c040049990000680f43c070301510600010000b880050b2481040900c0b501001418600b8458195032000c030fa042d440d040007200b1412640a1240d50000e09945551170402d800030300c00891503008095940c0b80d1890761b0715002e00540c030100b6240403025807002c100c00e0109401e490512508244000080c600c03030740e9280d000c40210340a07078200704c0041c0c000000b4002c11090030800c03d280c043d00a0703801891820044e200001da1a04050440d0a0200110b160100341105200804405001e4603042c044529000700c1d09803a21501c0003110300c80d1072050b001ca046410140b15090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 675243606 1250 675242356 675242369
    0x306150f12010e0105011b020d050d020c0a080106050a150c0b18061303050a0c030c050a051c020105010609140301020d0608060a0c03050f0403140f07111003090f1e02031204031b 78
    0x20845011440b1150a034807c042040c1c0e0000c46800a89000a0080105050807410765000c0e010800381c43c3c040141c2500140d01c00c0401d80c1c1003100c180426660245040c00300c8640301c41c4c121481c0380c1181c066038121700c0c0315009400c20b0022800c2081d280c411582102000d803100c2e098a0207691600e440b603c040c0b5041c80098005641805800d500500400003100001d0180c10103c00305006507444034941400c50b8012212604a181c0740008403141021002084072070340001d205940c1001e03001060503400b0712500c00e501501012403403141d1002e5045820200700c10406000b49511003a0080d40e0354415201c2a0956203018040301c43c2038403a103d0140200d800c809503050986845c2c0b0211607a8481120418036482c0401410602000540080064074400c02c8007406c0394425404106844100c07004610070b147c00e01e107901c40042c040e000090382e8540d002d0008043e000c1300305d0b601c6114441184000b901445400c510040019844d4060070850384200e001b172000744c101b892204118080c910130304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 675244856 1250 675243606 675243617
    0xf090302040e0705090429090a150609020a0207050108010906050f040203060102120705011a09160f140a03050118020412140c0a03060516020303100b0306150f12010e010501 76
    0x280014509508500c4100502c90111500d40d07480f41c001a001038406d076070450f00500490400c00e0040084400c01301c04c01809100a00b55290070401d8035120150000c0081c9030050002e100c050401a030342c480e9018200c6035004549030400254040d6540303110b4016a0701007100c0e03d00004d05564030340982000d030759002c0c02c2c0e094200204400d000185d0009842c0506500946245810341c0c4c02e4030010701056406040003044800340041a800040c0c81164a13038080d006100c200b002e07825130103004407000b031101d203024003091480359000c0390380440540104c03a80e1040010007000c8c00f0b82c580c0055058420b00c4003425a00111404503208038030070740c0710741e60720005007401139004100361140d6500741c03000c0307442502d45c104018800120045080d401c203c80482e551030511124403000410008481c015000852070360510703406003e03503440b080c41840307004480000000d14980724041403072900c0452801c4070b13449050b00041801c9507003050f1100003d20b540b00000052084503101c1890403648180c550 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 675246106 1250 675244856 675244859
    0x31e0c040302010c0804080613060501060906080f070908160e090c01090b0d140a09031106070e1011160806071d0d1a04060605032b1110060b090a05010f09 68
    0x19252094140c3c025107650342c05110015101f2418049148683c01401a1038540c8540d4503000046890680200b0200048481e052107450341001102da0499803545035110b40344c1d19600200c4100ca86500211014019050101020407000041c1415241d030040d089a242d96558031a540e910900c050082c0058032605040181e03040f500020604035003495000f28000c4000010181012402d68008185aa4030400b00040c0341c0e01c0001320480000000182c0568109540e0040c80715103200d00e020702c14000410310b078131024080e04140090354040e609984281e0304130038409840070400c2c8241c004a000390710008207010301c60105061422b401d45a0501d070300c1911070510182d10503416048461a18840401c207200e03203d88070040c8920701c00e00e008520039040c02d082c98200643e0900c01c0740960426403103403ca030394a003114480354482c2032030800a03245002038060702d000040700c0694003da24060300400d0900c594001810804403e0300d0040c821a940c400440b95401c00c40e10b0340c800a00194030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 675247356 1250 675246106 675246109
    0x90e0d0e0312070507080613060f0c0905090a021b0d030b0d0b0a0f0902030a0b010503010c0e090f0417130303091d0a0b03070b04090501031a070f260c031e0c040302 72
    0x107003c442d800740d030803100301c5500d1b10701040c640030041e51021900311410590504000883c0910442d807011480180141000c0410103022495940101d6228640300000512205503a5055074881d05281d9400c1c178080441e451210b3311b9a060088140001c1c1c01c1240054031810583c0180b59001e03032140d80400d259071100031500003070070031404052074252910b4480c005640e0070000849284d0013030f080341403594981010107003107402c1d8070107040601000400484550b9288541587e0080500b404102591359078908012900449506005103503c007050350341c1d500c6d450054030b1098910070f4441c0c0c184291113128981017010080301003481100c0702c40002e05200c0c0d554219007070400d0040c0407500c9090f04d500b00d130b030416003040e000001001d646000410911620034800e8103100020303049828a8100140c0051030308031800040710501840c4910741e030340c0d80118400450500750000d888500390403c0d082c45402d036402550b4101d0300900500340d00700c03d40d5900c65818001c0c1039800100380740524590 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 675248606 1250 675247356 675247393
    0x60f030708090a150e06090d02030702192106051f170703200406120302030405061e0703111e0d0c02012001061d090304030305071506090e0d0e03 64
    0x41101210f4040d140c41c660028035500700308140307400c0d103010100391190b00d8084e582c17a0110041441031280e10034105214070f16000310859040d0740d01521805a907000725401c0c02c8841029502154945020701501c8800342280b0001d0465248100704c1800181c90350400c03c98100c5401040c001603a0110720204500d4681e183c50703032039800c00402500c40c00356403510780000d451001030b039101c2004500f003240d1850740307020703c02c29020f0500d965850b80c8800d050b4038025070300d00607801400d004000c0010360900203d481c0100c0c0902000394281d540d5500407a240040805940303140181d103a02c107043e00c608a0015041d5100b007001d40f084010210110284030456400c2d0200c102030307041c840c1501881038901e0301074002c1d401410307280340041412454003003858070b2250480145891020010144440d00101204880c03c5907011300d8140d881c0e1070581800c10100c0070800400198a00e070001c002250000740e000404400c9210742540e140219466087e51511402d560459141e0010f40c0e07000100030580 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 675249856 1250 675248606 675248611
    0xa140a120c12050a06090b0d050d03050601110f0c01030b010e090c030a0e07080601030210020f070605070c080102071113060308070b04030215070503011a0c100c050c0d0c0b0105060f030708 83
    0xe14185600c1d41c0082e000e40700325039094910120b01521204180600031060280800070082551041152035590b01c841d40c440d1220755488080580b03400c0420442c0e0700c031f04d02c2054400c501c4010365035920104000c082c3c2d41d5800034001401319003032078a54052503000307801c40d21594501030300700701d015541d0030050495030b0301c0140100b07102551021030420944040080f48007401010000344025415801040100e04020000300c0865100740c6c0d02114048002c51003404481841c10300c542c9400b00391514000ba00c882c0c3d0040149584003080034401e0100c0610305ca401210161040204c040d071001d2014152181800050034801041150b100028415514254094001e10549409404c4080f4411048005840e1840014808001803280c03200c1c540444078004101581146854144420582c03503a003004a945e08007961501e11911880c0610102c0b00360b0300842c8242c501c5030b03c0605c0050149020703030801759209003201c0004a0541403140c00c49000c00024840d040c01c60340c40d81d004941c1078000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 675251106 1250 675249856 675249881
    0x2010c060509160f1d09032203080c0d0e01090501020c130f09080705010e06010614070c0803040602030705150411150c0613020f090601050405011d0a0b0a140a12 71
    0xc0c2480751509011181c00f42001c4d00d0241da2a500c41850450b8103400707075001c204084d00200c120380030b01400b0301e030020880c2c1c80c1d0050206d00243c10403038480c495150415079800904008000114440114004070b070000c0c04046940b03c610070a660800119507020007809401d003da07004201091840c603180346802c00c4401840d0001c01c189034030351604802d0303a01146044501810120f440c0c0c040080038024009426041d500a10007503241c10001440200d4400c0c4500d000300b00003e800c018441088090009403040400b00d0799220b40d25034000755079a01c0840151214010b80f4011100b5008204019004617005101d00c0d044078032010401c82c00140704600a0a402c0c802c0119480018041c0079141c4190210301e005440943c190041c400600c202040711441010f41d03100b00a042d07a0031a00b030700c00340d8a00b80703441d501008804105c4511042c0d403028041d4401120070340000c800c032a51004003184982ea69405c1d85522419204180c540525034900000c1040403414a80408150b032201c0051481c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 675252356 1250 675251106 675251113
    0xf040b1006141c1104030308130f140322050a0e011503021b07080106240c06020f070c030c030501110c0d03200a030603022704080702010e0303220902040302010c060509 74
    0x18804005003220800c10311345840340400318040080c180c201e1820381d480034852400c0180c02c0c0315962178090311514020700400c442444c10a00e00e00b0170041041c0d07141c1120400d2884400350040005980405103031195521900500d6408140302d043c5c2c000540c100c030f000b400e281d845058080c00540c06504000b00001d21600722842c2c4204200003000010014241c441c000a4003500344989002526820390300d84803030a14220f000301400d548a00541c42c9147c0000300140c0300e0a07251401013182c480c000d8050a1528405000710a020201c070f02401103a01c140c0081214402600048140d40220300344200c41d034000400c8124800c0c06074210044d40c0800c90140305483c0c003040c00c1c2c82c1c031a8010011440010780e40381401c0c01181042581524903001075614001d00b140c444075812120040104000c0180c4e4010072000300316409004408004400103040d645c41c0c00510100044144580340040c01a1050b071400240803921882182c080d13940603035400050520a4035200b000c0c101c0500350584512 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 675253606 1250 675252356 675252397
    0x9011509170c2805060403020906011d03011401150c02030d05160822050a0f030f0f020604030b0a0c1d01081e01150206090c18040503120f040b100614 66
    0xf91000040b00201440d0fa0120141050030704141e0741d4581203800950140d0030812051000d80e5035465070a91104007442c102ea000010b590750b40e841c3c4600901e0054141d1700f082c944400480d44242c2882c160b4841c0741e80102c5150143c082124607014200c0c001e500354100002c1c442c402489030000342203000082d241024a070002d6a04c54403940d0000d5200301100c00b028110862102402d180c0da8000d000442c0c2c08850746041145002800140c0d00c0300402201c1081015030411465101405001e90014015030315203540742070544c19250221242d101c12803600c0c00004004d4010794840c1480341e1500120450700c20190019a14072002030891064445031556085452505550b154080c03c0d00c5c0311603910a418041000e403400602a2031080303a45c11055011a4580f00c4100065169401011407600b507240c50070190b08612075091496590010b49007048540305401c90b04d60302440c8903e40c60045030b6a081c0a0f440c9040c0315018040010b01200c203c0c54210070036030060304840341000720000424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 675254856 1250 675253606 675253609
    0x1f0b0a0c020a091b0315180e060109150b0c07030f110a14042f09012304050f010f0e0103050709080616020f0601030312053309011509170c 61
    0x1030380e80050301140c0ca450f20100011926040c4c1408000c1608040c003566451100300030080704c66000b400300d40400740d000440d10041580140040031014400d50b035030b6503110040341c0d018000c0c1180c3d103600000d14510008070748200d04100d03800501100060811141942d0710300d000c80d0094403080d5426444e611040c4455135605901703400500c145020140c0c4003505d60700f444142d80c0c1842a44400c0e0b44002e090303014403681c0150b4809180a40c0750034590b02d815a00059035440d5440d0200f10309a003010883c050035101d150700a0041d100122546019003c81c1001120030380102c9244a000402c24806800154001e801091b00300c06e80381021106941c4403d801071070310700308442c0b0203001c08110301240c10300e5805218200112004030040c150070b6046403009441d03815564407414886e565880042e80231504014000c003c032107800e0300058040541e0422060042070b000803584074410404c0000381540700601d03554883d0890742c9551807803510308403401c642c4c01d00119011166024190041105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 675256106 1250 675254856 675254869
    0x2040b1c0203060903090a0b0a020111040611100207021810152a082b0504061a09060f0418120503040b011203120e1e0c091f0b0a0c02 59
    0x21940c9520480003081090041600d041ca000d403401003a60400c001c0100030703886401c17101c0165a8050f0105582d07040041c402c900524030010b48001255001c5400300b40191312491001740c07412808100da0f03031882c210b050030b0120b1003175410080d449562464661494a010181c0c41d52001d890481881d009940c0c00310b850500c40d0600346040003030044580e00708007000c00000d51074a119411607141141c01e140d80c0c2c2c464030748100c0c080b26200c000911b00d08030200069008510406500280074030042c1820300d4204054003c07500703454421100ca00c2400500e0030900811403044000400d5203002d0380300c0380103100c0281104491481020798501c00240882d003848c43c0c08003c0461680c1d0300e5628034050420800c41d090603008011611780700d5104101103a0b2203032854800103103400d00012a90342c0c0c40c040920740285001071105000002d4908000c0200114540044c034905640c552840c4d078662030300c5c103040004140d0105a0030709030001880a043c0410141045110714200b00c243d10800d44c00081e40d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 675257356 1250 675256106 675256129
    0x1e091a281d0610060909050601020c010c0501020c01110d0c0f0207051509150714071401050309150103060e070b090d0803100314060610020118120c020a030c0501020c06190c02040b 79
    0x41d20f0107200301c100200d542c0030030ba01c001010400c10400c00f40c01e1100000f510380510000c10ba04100000c030884050100030740c100d54144200c20300802180610710b1206503250094071540791a249805620142c1c1d0b40240444080d41c4650703409010914102002c00c9030400141a0001d0510800d010390f00d250346804210181081a030562183c9501c007030326007050035a813044010200d54100b400e08001008010440020400007401c203a5241e981c2c046000c4c0c075043d40d06901c10480c1100500010511819901c00d0310b2582d40314007074448898507132464020034400d4022494211490b071a4110104800303402940d04440c44182d00061301e82c0d651580350180400106908081d008034051000c1460013540d01213846000d8002402100181000d454803406656008ed080b440c8900180400c50b2007549015140c55005007440000303074407402c09650201483c09118090321400e0441c4840b07280c8102540c0040c16082c0705501000b144030780894214039805c07400c9800c242c481800c400a80d441c0c100040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 675258606 1250 675257356 675257371
    0x10b160b0a0b190605030411061c052e1203020c120106050a330e0303071a090c0604031e0614040302101b031e091a281d06 54
    0x745500c0c502003084516407a03c054402111100c0800f04206900032054982c031a40001d0385105120710100030800d28811412006400410303d4000c2c3e800410a5004901a40062180c41c81e1103111231101003000141c401c9111550708084410408205c140c4c201d144510310900c1602e903508c481c0c2e00841e8407070041c988965074a035180c2c0028030107030801d00c4494008020041c0130035071804002480c28031100b01d10000941075101da81d40c590049005901078254041c014003100e5580515041071628070b25102066072101c003411000c140400740008032076691000c0181407503d01407460390b070a443c81e03004440d00300302c0c04030440000001c900503210307405040f400341900b0001e619040c0340c02407c0404c5402807030115480e0801002d0081d40f4813003020810090390500240341084003034181c4000150803207400c815410001d00c102085074080041e15644140d00b268034561702c0346103036601d003108610406909800707054101a041e0200ea002010400c3c0c191809442d207421000c400303814a0411075141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 675259856 1250 675258606 675258611
    0x3080103050d050306010e010c0302010b0a0f0806061e010c030201090203030a2016050607060915090b07050c030904240e0603120f040b031b0d060603051509010b160b0a 74
    0x100140710052001e2144010340c1c1c60000d103149400301c0042c2480c05880359140c100042c01100d442014002d50001d0b4075020000c120201311a5035800401d111030b852301441d4050b0140c000410200e0401c004820442001084126804000340c401140c00019056080e0110b64982c0400000350300d0510003000d8013402d550301d45440041c003000c40040341c000801c5c08642c0d544402003214070301c510940c0e0303102035850443d011503580d000340c205400904000c000103486c0255014012505200a6108466107441250030000558070090141c685000b02044880190030400086a0904c0c04d0750020440740d103200d2070303c0c00c00c16003d0381c1d20035956095000842c09003286403e02c0307064503017003008141c40070455107080d203002d90300241c0c400c0c503000b2845404985c0e440800810004541e1200c1040503850328800c4a40b0340e10710b410000b025040318811180824582808101e507a500f038201c0c0e5542404c0642070310001c0c3d1801c9503070101580550329940c00f10711034004060020300e69401e5035009070f0424001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 675261106 1250 675259856 675259859
    0x7051203090c041b0f030c0201110f0403030e0a06210905240c0708251b1d01051c170423090108070b07020a0b0d15170709020904060e04030801 63
    0x5100c2181e40181303021815042003540d0a034025402102d04014498034940440d8400881d202a030151881020189000c2c10104481c04040600c1001e4022030313010355206000720750b660040c0305c0a649035004040011380c95403000c01205104040c5409001c0080c203002400c9803a44d26684d050910941400ba14640c621700c02080129040079000d0b001428900c441c4d1034403a40d940c5080d40c46c400d1b0700d20343c200e80740940300c040c0b1080144241d40e094290800d0b02a0361500c5008401c8014200602a109074003805941550001e1024103000341030340c0018000b000c1655110190303d40c0e07c030074a0b104503580d9000403032003114581160083d00c010003106200c21200c5d1014045840148101440140182642e0004200119000541c80d01329480410003035a02c005d2400860800c1056802401c43c0c80c800240c4c4006012844d40084044603005001c00a40c81d26818071103150b4858104080c2c06a228104c24072a0368900c0c0d00910401000a0000400a030380e0000b511010713000f21810380c04221074000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 675262356 1250 675261106 675261109
    0x60306020705060604060513150807082b090302040506130f020c01054503070b0610020c1e1c030c14030703080115050c0f01021305150901030207051203090c 69
    0xe40c2004c1c00305c40c1848054240030100e4000c01c580035102407000e403175400c500d07000390b62038000300c01a0940d802540c1710b9035140c18449560791604e80010401409481e15000c11100c6841001031100041e900c1d03000315848d40e02040040c11000d04104d500c9510543c0e844e008020a201c0c2c001e80c680068000341c1c42d0b51224000303a0840e03074024904902800820041c6150003c42e41c2844504995500311861a8501100d074003140040840d0711001e03032000090b00c1d8207025550400501c1840101c40941640030000340481e281d005041801d600303d400c3d44043c20200308060310300360703d90a000e015400c0c4011020300d0082400c1e603018080c0d000c140c24944800034802584000408080030000442c0703004035a0381c004201400510440001c000f80072070010340d075440740c01100d2452500c0c004489024000a154074001d62008480601e07030324a02100060a040c80301c0480004054240154103100c0d2a01c010b4010f940020303412561401415000800c11400e03001850007a0300b03520041400d20711180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 675263606 1250 675262356 675262363
    0x2010b0102060606091207092a050c070e1b0708030115110d080c160b0f091b0603100807030c091d06061509030d050309010c050a0207090b0a0306060306020705 70
    0x2115030454024104102c8107880e114100d03104500e064850029040356880342600740803540c1c2005048908242c401086400ba0030f0034544a403007205038401825101e21010744007032042410649207908011410490040402da01540c01002c002c924202c020243e1115515030340002030464000390007000500201e0901c98500c0030b51050381c01c040522041000d0581c0d030325552a01400104910031001500c1c06601c5402e8a1400780380d00720a8101044514040b513842c0011106d4a03a80005240000c400000000d0000485140b000b0800450b04000c3c090000d507603c024482e02e071403015000001884003003080f108008502841021107550300700b407109025a00c1407240140003503031640104680034804280e0340d400400c01c90703054508060980101050340641e1036119410b00039078981e400402d82050041d4805c1e0116030003009806802281607500b80101c600400c01640100c0c0203112282e8585e00240c6580c400500001e4200e650b90f9481060711802e401c2100c5094020810f13404008080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 675264856 1250 675263606 675263621
    0x10507032c030a200f24041208030a0b150d0e0a080c150a0605100302070f060c0512090601031208040c0e0a392304080129031e0309031c0201 62
    0x11100d4171154010200001c04000407000c480f40ea511009054684900d10601160014101e13100c102e055000c441c1000c50554008039000c160f07150070030f0b0540c1e425150903010490141000d0540f1800c084800f000c4074020080c0061000c0070744160f01c2c5000c045801340e03001c1d0243c20207200007480c103114113140008816101a001e003040368100f520a109070754a40c0c440c41c40088551800580b95070281c00d02400c03203420160080d111614050030144102d51190041c40505226807a8403040d4481e41c80c0320795500d8003484081c040201640c005d451040c17003a00b03900d420500942105040940791090700b0040001507480c4540903503103031070840040303000403049402c2580f2210b02401134982818014240d90207075064208006000300c0c042002c0725002401c2101c1c82c190403170030751280c0d20303101900c0c0203200300ba81c1020040501c1103009441c111007210004e1444004d0060400f409100c401010302107044e0509440d10f0109000306a81902c042111494401c5507030242c500050b10890043c0c21034400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 675266106 1250 675264856 675264859
    0x933120a050d080603060c032815060905061803100612151505100201090606080a0605010f0621090209091c020102040608011202150307120b010507032c030a20 70
    0xd008020150390b02244065122011f000e049640750384000a840310b0410400100e105020208182c1440320320a60004495840894040c4021600e4640c1564841c0d00c3e842500d502c030340108940c07000c00c000c2120b9214102c001800703c1d812242c0e001c181d5402d491440c1c12205c0801c0b42d00e4000d000388030752030b91024554012101c0420903007818240c0c4080c0b1845a0082c1ca0040200c103440d6050302d4400d601c4641d2142d0410300420042e03803503c034196180c0502d039506807070ba40d0030400041095500240800308031082911401c804050382814258480c880d80134140e100c0c0d40d14030f0301c06c0140e00c90f28281d9101d001640098000c4000c0d032480e8008d1080c191075003000b16841070209209071a000386146043d0b40840084004106091002400e42c1000301c5603160495030100a201c00c050b00044114204995a1010301c004807080340111032a0082040250020f21b0703a00340112005150750021004c1101d4028000385001ca20001c81c0c500311081804490180007014004501105032484502d030b50070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 675267356 1250 675266106 675266117
    0x2040f0203070c06150b120105030601051f03090812010312080a0c0c1524060905091b180a120b1e0f070207180b010206060933120a050d 60
    0x10082d4000340070740c2d40904000e20b030390f58030728400300c4a030341d120484802405c030301314643d561b50811084400b2008007803203468001d11400001003400d1400e480202607020380241c41c182d4680d095101100600310010f0181c41244d0108401c139405050303001050301850041058021314014040018042e0200a050203140c0c0d1804071807180d0300da4003090002c00250860141c070316440c0e0b8421003400520740071500203a40120090b100c0a0200c1c0d244910b030486038241c5882c0c200507611414400d0b803e0044400d00c1300711051000c403025444420000d4150303042a01d119a0081172010b000c11503020885d002640344504404180c010844240da0803a4401c009071400301c1400e101d003500030321404000e445840d002140c900002d00b481e10070060343c0028501555025100348034895280000c15a418000f03006016030b0000664a00308900c505010f56070440d8940942040042c0300000c0c2e20003040d141c01301c0c028070816902c2c1c0da5540c00f0b0380c01c0c80216030800780c4013003011807a1103464641c0900b07942041c0f14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 675268606 1250 675267356 675267361
    0x7020c0406030b1302040b030d08061c081207030f06080c13060305060610050d060e24030c100c05031215180f06040b130c08091906090c170a02040f0203 67
    0x410f2828143c0c1c02c0b8000c42800640d80d41c481c4001405040c18055640d014420700c00300b0075129912800c3c4900610301604c80308440d47e40c00414020f1152464800b6161160801c5203280c01445c80501e154809070720305d000034207002c05030200801d44542d030f48070021035404920f04154134500341c52401000c8400c9041080954656580c035905c407580201598441c20445811660b40c9001d00111001ca0100d007030300700021a00ca000c00ca150300d100341c0345000c0c1c151041c84110b00c42c01c160080e9160007032004000348104c0b0000810404680080b604440c1006041c5241c50000380c8104003400301d038940307088511010320b0841400c812a10b000c500303040c4500d2007440c1c00340d015600c03441c009070460203803580c0d00d00303956902000c103028002202c0003e400851080801131910389a5001d604034405a40e0b40c60380030b0302c40c030320f81e81e50361a01d40e079243c1d042c03014803200f00f000207a86030710802c2c4040c850440003504a551703484e8804038944804050605400c410181011480c184c0315003c038003020308100f1403c60 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 675269856 1250 675268606 675268613
    0x5150703200f01150f0602120f090a03060203043e0301020d0f0207060e01090f0305090a0b0705030a0f0305060f0603091213080c1c1101030924140c0304080a1b080307020c040603 78
    0xc12310405046d286660014005a49580340c03800c444110340003800c0700c0c200071b031789240000003903004072400c0d2544540e580a04502d0485000304410000810b8900750403100c0080c031a034a40c00386001000d03410342d820443c00300c000c08a4001c03240480c62085005844000d18100301042e00ca0885140380740303914000e103030000a507604040c0810b140d00b501d000b80d1142c1040b40410901100f6801101180c000403c0341d00801000000a08507a5119600c8200000c0003030025001d43e1010740d161035015038400702505c0350341403c0d0040e643c000c000e407044131181d10f01c0b11030000707640e802981c140612040b40a000c0c09000c1f01001003001030341060740c144082815510b0144884115508000d0002d51100540d0701c07136a10a4001c4603060f82c00008148130840c050b5419140303030902d961640d03178141c00e0099030804010b040040d148981901c0300020b18564541e950904158040000d00c02803110700d20906405c1d1038103200c0a00410300c2051815601d081c180d0002c3d180c8040d0845480c03241381400401c0c03000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 675271106 1250 675269856 675269863
    0x606091712030907082e0501050a170a0f030e091509150d06060b040510030506100c0c21060b22021e03040c090605150703200f01150f0602 61
    0x4000d0904a20760300c0b5101c0d500400c2c10714619501495462088140410310100e059841c3c0c0a030414442c4200720450640f54907100b030741c00905c259540000000c008118020300d01b140f400051040c3c01c01c2d211107002558030402202d000920a80000728141c0a1440a04112a04607000b52983d200c100c060b408510004c0e0368810002d02c001c080e0810800c620805440300d821000c02c05900c400240034041d140d14481455811a00c9114864200c070414200628081d00c21030307000b00c201500d00b031145140a502501c4104000504071107802c04140000b50062018040017040c40a29500e43c4449005040001c150f03058160f00901c11042c0001c601445d00074050020342c4012704c02d20140c1c0344d544c00349410300d1305c2000d140d04940ac20400820841000040c8090600f40e80c0c01e504104945a21407090003131803051400143c01010041002d070021a00440802042480041c1f1b4001d240b003c4070f00407401c0800e424440310b11691201a07000280307050908803809402d003414046541898404001e6a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 675272356 1250 675271106 675271123
    0x7022227030c0f060e0f01060501030603030504030816050d120c0e03150903090a0609030b0705160b1b0c0115060e060d15080102040e09072705060d02100306060917 72
    0x1070050306501035042004000443d0385043d00034000b0007401008a4281d92940c440c0100011035518245001c110396000f13201d194260b03a09980c3c0c80e4181400c0d40d452a6055000d8103501e1a5841c0c011410400070f4020882403200300800d5641c030b02e1404007100b0130000d0761642521359040c4842c0110380c2d603086d02e0001e03c0348044a1a48104210394030b071044000e081d0310a234883d0907000b0807562008104180c10142d02c10803244200715101007a599580110343c1c074003030010032000d20481c107000a400310b444980003541104003016007404448100e07231450490741c0241f00368040340e51940d400b000e0a0310b0000c8400000d0400e0f0600143c1621350100007407441c807030009024440d950301c50001010780001c80400d0040c01551000715521500c074681c070b01e003401013150341d550103225130080410301c807124501110030682c1c2c40c84250600c0c140314004502511005184540040805031010050783d107100d44103141440720f480008896040510090813003149801c510202c8115a140501c0c18800041528 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 675273606 1250 675272356 675272363
    0x4090b030a0b0c03070c0203240124050c160909050616122a090812070818010201090614013201080c040305030f13091e0c0507022227 59
    0x240d59a40d008015246c400d00706902940620510341c0c100b0b10030446802c1400c80b00340e000342920302030303a03100005d40d0084407010f03d01c20515200f040846445002d18003500c00e540b5580b0036503241c0407152101d801100e1140d8007081089445948000078400103000c1160801519100c140803180c000b800549000040d106455025070340d03aaa4201c0010705d5042050300880a41e01060714442c1040d0040007074219005d40d0003540100928050005411412559106d60080106003002c003207000c8000c07e001c800c6038550565403101050f00014a07580b04250003400704940468980d4100049220a094400d8a05e0340403d05041d07910f1584010802d15410300d0000d04c0c0020703140d034a00340701920070300660b4002001c9210118480c1e01561012002d06203d007800000039211b1952803070f071103007903d03564a41c98100e111034405840b003c98042c5c0100c1126405401c2c40c030718060b00303540451001303c100d2042074032084002450a42e41030003405084c2c01d20580e03098001c0c900c01809041e1810740071400004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 675274856 1250 675273606 675273631
    0x2704051e06130e060a0e060405210906030a0e0d0f1409030a02030604050a02180f24060a0e03010c0e0a09021e0c060402010f091505250804090b030a0b 66
    0x200c1c19500d04038000102112144207200444441d200c1030f40ea00d0b4151030355a030540c280341202d801940005081881a9000801000f0b0342203c685070f50031a400c00410050308080c00c000750340590311014001e500560245100141c80000c14540d5410820841e821404205501900b4945a54801011985460ba1107180760b51f405c13a2200003840c1140e0030000035014020340041000b4804003180302d914107402030f01c120600004845908000880c00c90b00401c00d5052000030802491607802804001d00b10f01c40c0c401052031039000090704030380044c2c554800241e2a0381000c83c1500302801015909030760350501c607244490110026898400364000c612403d40d0214600455054803480c00f0fa0120900c2880780d901c2c0704100d410f50300c42608035010ba000c41c88441c5004950391054114008980c1850f01c0e80b0030450030444100c1c1c0340c0d40841c4030103542038405d1180c22094200001d4004180e40704e000026611850300c5c03c120143d940a4141c0d6120f40c00540d1501e01261404503d40d91002045405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 675276106 1250 675274856 675274861
    0x117070302120703060c08160207061d0d020603130302010e010213120309180509190b1f0902030c0415050f070b0601031d0706140309070303232704051e 67
    0x1443d290440c6a80081d060320b04240941c101e9940000c0b0050003000010013007188100c2d4003406907501c83d00c40c410321000500150b44140d03c004003000c4007000c0b1a0040c800d003600d0140c0d4001460f140c2096800c00900301c250701c015020160240310b000380580c41e110096041070b04800808e041e5054510821824100504ac41c06c00c06100e24204000703411071081c0034600d80c00b461031480060a08590b030001610802c1044004042000b100d0701c42c2c50341c4440416401d940703010244082e00c500070007072022910800c4010030348510900180d40300718035030102c103074686251004540e000340c115407045052003400c1050009134000340c401c0701c04c5603030080d08800680e1134250040300201f002ca51900c9803c110108075481c03100010548500301e5009607120520181c0c5000f134000a4030040d00d005100d94000b1310200300280c0202d03038248000110305501080510342841c0000940d019140c1d148400c611035124200f1825814010805044107680c06c02c600d2034104006c1410750b8046401c1059900c05000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 675277356 1250 675276106 675276139
    0x2b0906320c010207050307030e0904020901030813181b05030108061620010c0305060103020c030d0e0309120601060206070908150901020d0c09030c050907021002031509011d0117070302 81
    0x11544928042070003190f45901d03d0401e15240d4000d0402240050000060f00800f0f1400c2003569010341e400500340806640795035210603296104401e0b04950440c28400010170701203080000c200d9252280780420410000c405002e280c0404610a905220741400103002c03d110024865070700560111f01c007540058810020303502e204409043d0b110404040402c00e800750b0341074001d221134008644040c0300b545c0320b00c40150181d02500035400d0301a8414020b98910f02c0c4a500450202c5903d00d0075240b914602202060440000103512840c43d405980104250b51741004165441541454072502d0903040003a0071340c030350000304805ca90f0040c070880030402e8541d0039070450341081c065940810a0310302c0040f0140c100d0309903110549048400c024009007908025640e41d11076890f6a01501d1521804c00b8104002e410190207820150030301c014400d8180c5030788200c41e0203006110103c0c0494020302850300802041604440c41302c0b41c81264800400c0c10000b00c80c801c1c4d0354102c8110891118459 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 675278606 1250 675277356 675277457
    0x303011a0c1c030e120a020318130203240607021c020a0503030307090603061a0301032013050121021507050a0b010f030201120603080a0c052b0906 65
    0x4040b40c00b030000c050394440000f90141d1010f54607011220559040d255400c201c0a02c6004400c01d1030003507002005205030042c030919060785c0c0e0440082204081c07598260502c02203030000c452400b080c04240d07070541010301403942d038518444c9040750910314250443d404101c2000315400ea00c10345034455150281107588078800f8202814000d4110303512403404850041032140684100008246090804204180b20700781d03456000024411003455a465a5a40190000780c1c848429199403011861400e070340d180e04d813040c00c1540c1140c020481e541010150420200f02901070512308401c1850140141c450401036044104400185a110070f0789040aa080449182c0020001a0305000100c2c908928020380c0c810f880c000c2e0b1b01c008144203040415822140c2e640405009500c2c280211016a8030829482000920900550f5500742a00860780130508103c800f8803207810300c0140140002c2e52000b2034100600003450141199159013400c0d9081c00d40601c1607001c10000030321182d2961001d0b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 675279856 1250 675278606 675278623
    0x5070204020a271e050307150210091b1d0c0a02100e060412050406080f06010e060706062c06040e1504030509010f08010b1c0b0301090b01090b030303011a0c 69
    0x30f10407400700c05000100d5001c003141c94040c0301030522201c002458946840a2410b05883e006801010082d051402450619041c22601c0c0210b105038402d050641c0c01500403101c2c164815103c02c402c0360b01070b01c0513034944071841d0400f026040c1c41e03039510300d0808051091646c00c001d900840554440c52400c04034281410340f8900c0700307180e041c003011340c003800030005440e44254010361421f0920448000304481c03d20462107404000341c039103030115603051142220103410400504003003072030060003808a801500121404d07034480d9581c3e4070411855103080945a880d010980c40102ca4940d069810200490054009030083d40c0c0d8149020302c40c0b00c100010f03c58454000c58405d00392a06117002082039009050392130010386103c0802c00c3e028001c6c0d807224180e804007074082d41400c0729a43c2c030000104034071016200c80350715480e030301d180d94500703110b14001c607400b40c034222080d581898000d806540010452500950003003004022002102c2c00b00c1300b80e0303419190b0b0f441d40c07442c0f95401303a890300684 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 675281106 1250 675279856 675279887
    0x90305060114010e0f03160b070c1d0406050c16150f020906040608181501140405040b13020102100e0703031d0906060d060f0b0a0e03010c02060c1c1112010f0605070204020a 76
    0x35082e01043e48c07076105005e440b07041d228075444101a40c40e01176007034012012000c40712551502d8408280040e071190000c990040505121600340042d00400300000010050255000c40401154015160a03802140f600340c0c9415419494a801d00c00800c1d031911a600ca01070412400d440418000310100700703900d000c103000c0f40071600a0b162807003000c2c481e018288a001d0343c80c4165240205c00e41054001c5da031007640c022a1004441d503030a10310103031519089500302c2c1140180e090101d032080e03072403041c82e055000c218000c00f456421031030090615035044000541d01c000c4505500311030390b1012030155125009aa0098554032841c1903040500b80c40d820100f010061001d021400070415400b41c40c0e614650358882d20446030304024035080701c00015000300140c100d000040c4480c61010020902400380207444038407015440300c0d1324216074040700f0195000600280c0340d1104003c0507242030142c688002c000d26034610302a40503010f4460004028051a00869601c02480c09904400902060b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 675282356 1250 675281106 675281143
    0xc2103041205071d0c0403170d141602030705061b1c020904050109090c06030c170414010615020d0309020a0510111002070f020603150a0303090305060114010e0f03 72
    0x1464116120602c0f0f019013000340d8441d108942003c941403c0c01c0b4058001c1e42c003560b140c541141c0f00d035001d140401411102c00c8408100705050004103206006c10200c2500c04842c0a040010f0710b4100c4801407441ca20442d4014000c170300110303101003a0540c000000c418142900703110598400541d0181050080e03144100040c004500860783e0024038400300100d504011580c0c942410300704440e0601380103041800b04140a10109000340c1c0703c40003002039400d20b800005c102d0341840c3e03204103044a049503a02002a520b1916103030900a000c094003040000407086940715400a59403178660300210101600c1d000007009640f60302c800500034280c0a01191301c003101c804000b038414210070380880300c0e5101c0c2c1c1c80141285284d41c0b0a4850701a4040301740140a840c03074003000000c3c2c201400048a003110402d40039019551403005600543c403035107550342072901c0c40c284141403060580c0804000301100c81010031303583e84400071032800d02e011075010503d1b01c1030303501081c60402400035503801080d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 675283606 1250 675282356 675282389
    0x70e0403080702061e04031808030a02011a0402030f070f120c08090d0503010605160c150c0506092e0f021c0b0f010e060a12050c030103030e01020c210304 68
    0x1075104201a100d19007503000c88405844442d10260b02d5408091846413290814000c1800070384076000002080800410032600b058035003010b40c0c00e5034840c01140025030354950802c0d060140303a080326a0b505608031030441c11460700800c955a200e100030640740401103103501218040d800b80f000e20841e003038507410420528078049000b4012900540c0c064080d4490004101c005d98071801c203c1e8140c40303803643c070103090000091002045c2c2c222041c04907590302008802140081c40103400d040c00b00780701d5486000c1c044c0d0a04003d03040c4200504201c0c07254004207007146e04001e00d410b5091401101351110484840b001b02d0703800c010220303a400c0d0010540009218480804103444254510446c50010840611300320200151a5030300d00380b00b8045603c0c1511101c16141c6a030240c541d00c07100303041c02c421780022504044c00302c0300103c0c0d04100c66a070200042c414107501850302d682d4513100780000e180303400c540c0e00000e00041d00f02003541a800c00401e280c200c087c4c0700340145c800510a0b42000b51114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 675284856 1250 675283606 675283613
    0xd08070b07081e091f060e040b1e04120f020a0b0907060207090b1005070c0f0f210314181908010c080c0a080a020405090a0905100b010801050909070e04 67
    0x20800c3d511010303030590341050182c40c10200294140912000320007809946854203004071403003104001500710540d1540e00041caa602e190100e4030a5100b45078501c41071510008910000299149140c151f00c1c0410800c00061200031590300d202d50282401d4040454200c4101d1500350f07401d4004151040310002e0101c1144000707144000c1e0b4440380c00b81c40249d610f640554045031400c0c511540c1c4042400018030144c0c2c001c00013000d22601807418a444151030b03d644120076140f9a220200c4000300580810810b500e120b9031400e0303030304501044041440d440d10010030b00a02c26408103140000040e5003045065551062080e4071000b800c080000030010001040164842c4124600ca50034003080b4040d5612a041c103e21848019043c45d051500d1801c0c100c800e1200100105070050b8200004039195442a010601c030f202960700203d00d0140b10301d4190302309203034007204085040c104a149103860b80c00840c00d6044d12010341c2c001a0b1540c82c47d02c4903140034400d5000c603a09403511002e03c01032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 675286106 1250 675284856 675284867
    0xe0f0d1d04290319080d14010b070309140603190e1f050603010923030d05150301060608011d09010902150a020c011b0803060a0f080a0512090607020d08070b07 70
    0x1800030703000d410302c000c90801030648841d441c040841c06084000310010002ea10440541811071220400003449440e2142841e900c2600781c00003041140081038203401c055001000c00e0150a1281c080306541c0c0304440456040c0c00040d08280c00c80000d0100350f80082415481101e12540c1e0714100c4001d0440d903050170101080700a11612154140000100c0301c1c281409001d007984ea115011000d00001036a001d0039907034801c1074008460200308203001c540e1a0038050280600010308411b60058222001c040c00c403209640901e040c050b20303000411504d070010f00784030b54015019514041540d51110b810b40140b1541070f00035407180341c00000c40098210000603119040f1701c0d4088504000e019401556040500b0304200c4048900c2e10707481d000103440c94044e580144020301010011516047c40307984040d42908030002d1a80140034010902608204044280c20072030001440c00300044085499403050300070280c09260905001020480000c0844001c5074110100c4111805d286000400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 675287356 1250 675286106 675286151
    0xc0c12050a0b071d0f0102030306010f03090b0412180b031501090f063203040f02010e030a05030c1005010f050616080f0a0906050309070e1005030303090607030e0f0d1d04 75
    0x1d1085034414800b00d00380691740556001c816001141182d54180046034480c000344d01060405072140b50010000711000e0103d801148540c5c482940045001c40040a8866000441e4100c0344c10103c204001d8801c64101ca1f0400c0b04c460300b05c410010f0320b00060360030012a134402c03011022500d800141c061380c0b020841c00ca4a40354000003540c0b14520364a000c002c45110485000d100040000c100042d501225482c5044d20606100040303111304400282090707030000c0165156000000c01d0540310105000d0701500c401c100904014a50400d00c08403a5505180a110b004020001d100c102c2c02d0700b40c02d0801586940456803ea844813100e14684103900302c03400290101380c0d11040420702a02503429644581c2d1000024142c0750b183c081c03c5800000301601005a20a06510102d00ca840600c01907204040d10700040c266030900c40c400404039901d4005000c1c03240c002c030f0840c400f103480200d0362543d107140d00d107841034000c00307007050808050103605070315a40117140c5041c043e42c14045102610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 675288606 1250 675287356 675287387
    0xa0e0304170c0d0503030a23280606020c040908041e03020102013e090d0b15060a09091113090e010c1b03110f0105100806070c0c12050a0b07 62
    0x3400d10502c503050000070000c28400a0240d0801d00000314800910303484980c5000d040b0410081b00c11f10740800030500c003015120031415950000030808106440440f805c03d0b100203590820100e40742c000b00944039440c08000740d204640741c059003030500003003501b5940506490505803420700384525500040c0821440101d002d5420607440329814840c3c884070040200107140341c10744010300403c50850010f614081055445001d02c43c3c3c1d00d19072550124041c91510461505801e414052001002098103040d1584240410040310070b4666002c890b01c0b0480380b9100021484e2941000c01800500030b0000306220321024100000d1840c0722508128001e00f8a00004c111401000100f1241710441c00c03c01d083c0c10403d5450000068402c07060908842100030546440707920700c241407402c1d5001070780c24a28480300c1003002e0011510500400da04442203041910202d0040d550f110091156841054441604c041501c028040c0500c842c44001c0c0d0f010341c45940510348440080c150545040040c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 675289856 1250 675288606 675288613
    0x606030515070311030105060d0207050f1e060a06050f120127060506010903080a0e060904050c1c091a130b0403110106090b0307050409140a06060e07020313030b0a0e030417 76
    0x1403600d0344c04c4040324103031140039121602d0844200d00590107540702c19011102440380d540c20f18200501440f800050a038003c0116101e030442c01c0c1d4082ca8006c0150448070300340d00d04101080195120250720035140342c140c6110a000c00103886803801400d480407450070050b5611884001c1441604259109a02c11401040303680c85034001102c6507a46404001e01205042200c021290b010310b03010b10921200070080c52401c1c4142000c80c0030f650341510170f54030340f0901090380c2121855880745149480504901040b00700d046403502e03c81282c01c20242c0c2404000140450140413088603426850780e04400118000c1c1454500141140445100540554070780315002c201092280181c09103500e00500801d0020f0a00302013000034100500211021080d8000c10a40f625040c40f076845114013800340049d10b14601480102d0342c0710001c0100c4110f410030032080300040031448044043c0d07034114035201c1640e950034a40600400b00c000c00548948804180060b0b5403590814203030b203465440d400c1c2e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 675291106 1250 675289856 675289871
    0xf03060e1912080a090c0911040b160b06031504081e1306020f0c0306040b070306181a041404030c020f06041e3203011107050105180309030c040906060305150703 71
    0x1044c116425041c009200340300700f400400600010790441e00843c205241100c1c917007603807044580b0565200b04804040c0c0302034203030b1800602c07404440c0305a204009038040c4c5408921102e041c0480c44005000803c40040810b4060141c0c00e541c010307942205419000340d640701880c01c41c11403018000d01c07500d8010303c41e06101c8660100003084d14100410060020b00050b1219600c001000314000c041104042c0c0e20540005ca40c0025180582000c1e02910000703449081410301616011018000750f0046041c107080003034100109980552094152a200501c00d0b980d1000038004601080071079806440450702040c06280020f00503030f2440404440e40456540d061100c00301402100c141090b0f99030345600c689000010141e1551803440103000003a44c045502500352240c2008030103650581d59601005076440c255140a02c4200c41d0070000c0d8180f41c4184000790b6140000c4c2d10f25070088c0d440c1d0003184100078058202e07001a5074000705890141300d58080f141e012100480341034001070f090402c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 675292356 1250 675291106 675291121
    0x60f050921100c050a0e03010b0d1a0603060c04120606180209120c030d0f1206062a050c010302091801080a17160b060303130f05030c03070f03060e191208 68
    0x18020f0140340c60325418108500001d050742d103000002c6c000c98041d5210403080300580c0d6a15142c07601a0b00c1103510005200e0f4070302500340d1501d00201880d000360b00000a20a101010358140d401f12503142000d2042d14080703140090207003280303030311a85442d40e80440d09036a809103034014203840e0b0b40c2500c01c0d001458045108035561310801c1400c54041e0000c80340c0408071442203850408007801c82c10074098442009a4550488005078000300000f10304002e00d428244034404a40138a00521000820301441610b80036141c0410855050605900042e2440180c54150951552200364800c4079001e42c1d603203c0c565181c41945104803110841107940d88401800300042e900349814007520002401030079554820303c3c040c0130300b24941c1840188803800034601c082141c0005440400c40101d4a031b850320042c5031a040d03a0051040c03003074000c41400c0c000440c84a00081c12260002008a0407288584031207003002c3c09054080300e12a5060110310522441341e0414049050070307038428810b0354a410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 675293606 1250 675292356 675292361
    0x601180c03110906090d170304110d030f0513030c03080405010206010b1602060304061103090a15060612090303110a02061506030610030905010605180405010c030213060f05092110 79
    0xd420588070b02800740d0384141c105140544001c80014102110740000c5031039058011010042080301000700101b00000c00040c030105503101401540c02d0400c15440350341c0541020303201c200c1d0404011010881a980b0001f01c46084000d607000300703074142225140e0074207030540e0b402400b910b030240c4600700c000a065440c02d8101c44040c0c4050441c0b00030b074802e95080003500d80c0081c1040e02c91545030f4071000240e214000041d0700494505000f41100052031400c0c4e0125040d582c508c45505240c25000c0014580103031070001e40401c0d1001c00105510145030607001820095071017000c0d160042902c1e404a500015028000e11102d00640c006d44500c03000c01c80c06101c1114090703000640c28a0502c24580a9085900d00910410000c038849480e5800700360391442d180117100b0522200c2c000d100c1444002c1c800c50441010a203025403a0554030040c0010403503513881048200f1504031a00710617148200d06a500011000744031b1075652416501c81c8903040104440911180240b00041d480c001051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 675294856 1250 675293606 675293621
    0x708030f0c03071704030e300c0307061803080403080a030501081908091203270f03060613140109020405100f080c0d0b030303270d1403180601180c03 66
    0x40da5502c0c8184c8807401c101e0380da003a0181044060105a49803020a59900b9039843d00320501d00b0520f120010690910081246889201140c0c0c0d402100f02e99006031000710b04a006d5070543d0a000146141c51650346181c01030300d92020340308120200d804001c2107215001018100f409a07003d21032a40c85502450311900c401003d480103400304038131280007843e41d0010305009907004020042c840c0c0400c070514107607071040f0042c1b400c8132500704520400c00240c40e03910011002c192a86030407292540c0100b5610040500014800c200c15480b40011495541120310640d02c40e04400d409542d507134000601030f4100f4000c161041051000400b0200c9c810031201c991084113a44d0900c2d161590451012654061080d40c0029516146813010300d4504000841c0031f01c2e110100c50043c0c00308800d1041d1140c0c008101e42c0c1d400d40000452240242d8810141c0c002c0941d10000b0565030b86038205035104464060883e5162809030303070300028a40d000004402d00018040c0e809110504488504030105c4a01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 675296106 1250 675294856 675294871
    0x503090303010e07021903020304260a080f070507241d150906030c121b0403060b0109230a06170a0209030f06040c0915050f010e01140708030f0c03 65
    0x107100400207100c0b0081d406400031118010344403500420b16811029400045042e80541c0c400241080001d81010780400c6011800d441c0d84000c00002c6417454883c0c0300410068041b490101748060240f1441084030581035004040741c00456071080c0d908420b0310001c0504500e18600c03448140054010448500c4030024817452004c0c0466034020400950504016a00d008806100e104a0794a03103000440c0194041c0c10030766100e00f03001ea441c3d042c09000070701e020040783c82c03d1890400c0c00b5001e4180d07001e896000f0030100310717800072100494904038a03502c281080076289070b600c0d031146508041c88100e0391081d03d8400c1c0b03803511000107690350807601344151202c0910300001410038400d03501503d01040010b0941d00c020350360304011843d080054070191003c079141300003005604624403c0c841c00c0688000d0500c4014581400502e891b2110a605410312668042c0d4841c01d07031054058600d000b40641c0c1481d02c40119003003c0403c1d400c2200c16040f891040380114a030341002c1c0c0103a034801e994 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 675297356 1250 675296106 675296113
    0x6210c100804082b0f0b10020109020315190501032009072f150a060e0112030318020909010b0f1903030c17041508240d08190504050a06050309 63
    0x1540c040c00841081e104c4182c454078805001d011038050114002c1000b042c40410303011417034406800821010854003c4000309580c0b4009008005840110b41e40402da00c5003021450703580c0e640c05012920900e80c0c020100308914080010040150700c2404540d11103240c184074000084070414440e900906a80c0301000c00c1000f400e00d4402000c2100007860320500001d58a40301001d5801e60f403400300c8550b540030542e003001d804c2101030a0740e44100d00c01054143c1d1904965490060010003118054802404040c2c42e21400a544581c10b00c4001c0c4107070b03002d88408068501100d50070300a01c0107001d01442410341405102c040e103082d03505942c41718240003103201c416195036000ea034078100b40c045c1100c801c884c14480305a049401d002500052a01070706601441200742c00050003402c0c02450070114441c401c07996920075001c0180002c40a009943e0707580c00c02c4003414410001c0c001c0b580a60280f4010442075051150300c00c2c050f10843c2c1040c2d48a010b000e442c0d00042c0d41c1c41c0801c490405081e803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 675298606 1250 675297356 675297367
    0x80f010e1902090d03171b0412030e030a030f03140105030303010b0705070f0303050310062d0c060203131406131b05030f0703050d030b0609060306210c10080408 71
    0x242003014103041c0800c0401032808103504041407034020b540a059010510740c2100040038010040e40d55800340080c1c0c1c282d8040310110440c0102070081d402003154002c0185403c00406020b02071859201e00000d0464003014120b10f8014801c0c4003400ca4000024108001c00000c0d0400c03155841c16100300501650540c0c2c20201065101d8000803401c1d1903600c02d81000040b41500b42c583c0700c0242d406560b4040e030b21303e45210689680d0384140e0000003004041c40320f82d03400b105040c0d00601200c603014440b544c00c2d1881c580444080d10400c60140c0700d284000203002da558916041301e042103101e85104a144498054540d4039001e04680320b1110240802c0c0c84030009801203c034150401041210050403500c40000c0f91400612019000c1079a001040610601400704240c0c0c12811552034280120400c03840442e44c0e9000761000d0501414010001c605035039900180b00314409851400b4202c18040c403c580380da209442d1750005d000709a2490040c0d641d52240300c0a40c4503581110440d80b404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 675299856 1250 675298606 675298621
    0x5040f032607030206010501020c0a05030616021002040b04140102030f030c090d0c091a0301051b0309010b0405070c0308360106150f020c10140c01020f0712080f010e 73
    0xc09000300c40d501a04080c1a48507a5000c2000d044460b0099000b8641981814006850800c84c0b0700901d00c034400c031000401c40d540e000100d0303d0b404003400d0801903000310441d1041e803915004400d030401a90020802244580f101741c06001100c4404c4840716008480303d00590301d900c10b240022015000800010720008014401080d107103001070701c1110200d1540d10b9202a000349604828180c41c0c0307034017000e0000d500c054056003c1d210b0890080001e800c10003169595035800c801004034a074070100000f02d03050404c1d44042032111010b4803d100c0c92901513070040c040309004404901283e078200103c2d130740c60302c5262040b140d02ca6030210486134820024048a683d0000c2c80080a10341d2034044c042180c006c139010100c03000140340c42c0d1200e94040c0c0308029040a4001c01024025542c001d00c10034005d9000404143d02c0390942c0700540e4481844c03500381c1c06807160540c0c4500d05000010500c00300308050500004181050307403081d40035201d5030001e9510500c00c0c810303d0105229100442c000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 675301106 1250 675299856 675299873
    0x709021305150d051501081021030c060e03091f02060a021b150a110c12070c1a0a09050102010e0c0405060f19064107140f0d05040f03 59
    0x752100921410044460f1201d070995204880701c54542c040c0d05605450303560880710803900004031945000003182481d0820700042d1000f100218289040301a20048c54000d04c401100c0641102091000070500070307183ea92941f01005150003150f40352410010254510048030200c8200e034043d09007607d030403a07000043c3d08035691170380741030701c0d803441110801500700300d4491808002e0f5550180e9190a08100017118074031400c080240c1f40403c20106000b8000c07818000d5106142e10703407a25240b15080c85000303408190004810420000761004450380311031b0180080c40001da95070520551131700012030a841c01e854050002d91701c5803c5920035450305800c015404180a0002400b207041d05000035095107011115411400c0491b506015281c1e000c82040003c00c221907215200b01212844840364ad0807100500c0c2100354084085a440265481242c10503908884250303943c0003800140341d00e03000140c0004400b4800d04201e00e00b124083d0043c2c5081740e10f407001e40c0c48a0791a64a45088 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 675302356 1250 675301106 675301129
    0x1020f0a053a020714060405150f040803040b0d060518042a260102121f050411090405070207050315090f0d080f010603060e0103080702040e010216050709021305 71
    0x1000c0340c2d451480d911409409420551401c1c19401807240d180b92030943c0c00d2400c0005a04d0f801490100014061034884604210f03e4107540110386550301c00d2005843e2840c0150380040b22140400280051300c2d04a400c0500702a0030718100030400d240d511010007040f03a0203540c0c40b00070380840100040110f40c17034485407842e01e0040c030280c1864002c610030351740c0806920b13000300707a034074142280703040b00500301a100030241780200d8002c40c0f0300940c15100070740704040200f0250b2a2043c680041c4203010341d10301e24900034032024005004a281e100d2400403207800083d011030065141000040700c06100060301d000329807001d0042c05603440b00100301952040020f2081c0e22034844e540391040140382c10040b11445008540e1600102c1c240000c24010324041079100300101401c00d90280501a4003034450750450b81d21412079561000c242c40401c004d050b5503407140c142c40d403000c151410180341050000821130311840641d4142071b210b424002c101d010b001d42ca07022400d14503100f400f80341040249000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 675303606 1250 675302356 675302413
    0x912030b010c0507080a0b09030405010203300a05062403070e0d0f030201020408060c030105030d0309030c0b15040b03011116030c06020f1e0c0d05090f13050601020f0a05 75
    0x202c1c100403070b841d01860000c003544070103460f034041407a8009000c2c11400c40c0d40c220f5203150240d0714091900b00000d50720301034085607885440c0e00700c4200350a06041c09182d5107031462102d4102182ca0709040304c1d402458200d07038042c050000170070b031404c17100c014280741001e803c00e80106500359100c02ca0115400b41030f4403549078201c5c4c9030450703003804034001226400107144290300240e034880c188141541044070213810400c18600034001441581ea009c2070305c2c05200d146180000b4082c1d90382c01e00721035640c0300d01c2014020030001c0e414480b086070a2007007142000015101401351540c90002d06080b00c0c20503001d04108501840000c4100392180c14081d015400303071070009211003164480302e0803030740404102e1213110720010704402e078100307074501a03404001d04071151420280ea45c001c0f02d45440511132064100400080c100d00f41307544001c81d00c01403030340c043c0c8205034144040394110001c00381914880d000d0b201e004c480c407221820009100e207801e0751281c007a0841c01006109510441494400d10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 675304856 1250 675303606 675303617
    0x601090207031b0f23100203040c1a0a030f1107050c03070b1e030402031f0209031903171909031206121a190e06041101081b090307050901180f0912030b01 68
    0x16034030000101b0158080208003880113030303242400e141071868462503500242400300010501e00f60050141c00380c5000b040315007004a00c00e0044a8090000d140050701c000707190401044540c10b0180c0050302d41410f41040e0111505c0e26154150350700c06008503107021803555034010174042d156514030095904144042d0803140c41c10740032501309404003d031843c1401c1440d40442c0854080ca0b042003002400b00c1111a2034604448a13100101a1084c40c5c5080c4000104c80f000301c0d01c100d8495402c0054858400020400d08020340750040481c10480400600300303003800750114114514550100c0c54039071144401c3d1424802c1100300032001c10090094252055041c400b0440440703d024003621400701c03201601c52490640750141d0600034840ca494104044d100402501c000d01100b44c0020844002c0c40644422050000030310700943e5030400b54000b20704e08000519060200c074440d03021403100c40f0500c00c3c0c5c420600710404483c5035103400b0780101c0710715100c18a41070013617101285115061500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 675306106 1250 675304856 675304913
    0xf061f181a09061305090f090118030c20090106050d050f01120f0305070206120106020f1b1216080c030d0f080a050402301605030a020111030c0601090207031b0f 71
    0x1000307040b0459607c1c180318007040c10052000c600788604401200070007810350751114152402880c650700020000d003a00d891214403601080f800000c040c80319401040e4600715a10b40c0d030000c1c2940c008564010505003050041052590740f108224142c840c5000070035250f4400c0e403941903802980510540c18400204a081c02503210170004002c1100c002511104079458aa0006d1030004288000e17201904408207800ea00380ea41c8412040e040c00c125040d0f410611a411aa41001c0ca0714019080038074072140001396584c0041846400c04130101e041d18204008417030142c0e091042c0600c001c001400301c000080048038250f1040d40c0042c00a0002c8420b40100e07902400780700d4520b55445d280302c0a201d0340145c5900100041c08059403890000f0548ad8600000b1aa90f00140d0000a050000303400c20324070044010400c2d00c004040e203200b1201c10f943d407080f404000358448041500010040000510740080101b40300e0a01070340108885441100c9844140a0004038440700f450301703011400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 675307356 1250 675306106 675306109
    0x1215031703180a060b0a08031305130f0e061e0405071a16030801032901030b0711030403030e0a05060a1706040e0d0905120a0206030f061f181a09061305 67
    0x1140a001c1c411a00005c1101401d410044d12110300e51204103140e1040112250700307814030403070404aa40640b841861901c010456501400059035044095803800c001e486e54210f0004416000e000645100b0300c1c0005508900e4260508c1210098203135841000304200b0361441800ca42650000d00d003c81c1c4c1040c0841140c200024400e480980000f01c0040c01030003444002000165846401c03035203580c0c0100d4000c0c11038020741d0144000740c181c503c800c0015003050301550300c1711104248441525625603d900e00504071f110f130a010140244045400400c09017440001c41c0c4600c1c416803511060003001000170801e10300014419500180c44401c0840556004c0280149184040c2c54600b00da40c1404107000a00018800d403e440f940000700b40400340e10358004803038001d82c01400307882041c0c0e150008203068406960f14a000c03d46662091209103500000c210703081166031904807051986c03841100c070b040030704c119000d020b60000c01245465140ca00001c2000108a41202d42126030314170 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 675308606 1250 675307356 675307363
    0x2030319090f061a040506031b060904050903120609041a09121c050a0219050a03110703030506030d020f1f060b03100501020d031109040504050a060c121503170318 72
    0x102c03c4420a03101c041028030710076100e1086000322401d0b18100000e18207000001d9841e40036030a1920013140c424502481a220501141e05110300503005201c14204a42002c0d031326441039503403a00c031307401c610b000c2101494516401e9003d41e40090000807170710f038144003803c2c071044090a800c03200d02c6207a1005034985c0c8040050904102c60502008103804005207403800d642008100c032007264410002c5101c0040d03010000700c0040c1c064034026807101c0b074000007030300101842410b0b42d0381b500c0041580410540e06030045489044140e00381c50515941050590341c0b42001e201102290f000b0944074185091102c141c0b2996094604001c00c800b5a40c180380c00b0319600c103580c51034221508031018005560104001d10070301456260401c8650300422805045015000a040c440c80e152808101448005c01c10782d80003d4021504000102d1052006001d1909504026800c5d41c03c201d05519104000c6a0201c100c0350840580c4010000e40d444103140c2c0ea10041c025541d4000e46403560806a0041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 675309856 1250 675308606 675308633
    0xf06100509041e0e0604050a03111002040321050712030e0c040608010b0102070509071b0206040815010608060406351b03010f020408030a0e22060f090c0203031909 72
    0xba4045982e41d00c64040d0a050300c44d84c440090095000105200024000144140c901501171400e9a0141038441d255402d1080050600200500209010003442454280006158010303055241d207070b074441009841500031018080e101a1000800c140ca46006c0e400032a1902251400d41d905001c074000000c0c121242a04410700b01c0c0e54035a1030503a2941c040190034040c00c400c0364124140e182089004150302c0d02c0d440402045007141c14020119102c000644000c0c02070402501d000b00c01207403d1984880c001d206020000d0306400104480e4103042c403a04042e541d00c0072408070000012300104282051440b104a6075215500d0549213400302800341c00820152462060380c044180002c06095840f0110b640144a2041000300001d100000440309100481c1c2041441340c000540011407568030441055064000c3e21142da0981410f64800f5094806034203000600903100d0740740500b00d42c0382d1030014000d80e0003040444c0004204120800d141005030310f01040e00012a81c2d110580801d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 675311106 1250 675309856 675309881
    0x6061707140c0f060c0f1b2a0a061112132c10050a0e072705040617071e050a0b0a20030a0c06020903030703170c030f0610050904 57
    0x10690640743c86600b80041c1d13801c241c03940c940b5828501d00c8416400b041c070030700c0f109107003000200c00e407804800380c184110b44201000150f242602040304000c8040300c0c42080005d40305401c030181c0404c04a01600224000004e0b000042c002c000c540c0748510001e50180705655189040c1c1c040001d000728482005104500d0054154005011000028030035000d0213026481c040404400510031600c5000f80e010850785200c0a0000035140c0040548148081c11006500c00c42c013540c01c030505041c1d072174600c0304a03082554200281c507543c10718800c490503003001c0030b130850700602d01c104501d0090164170142944100c460b03040c0603640390001001d0a860381c0c0300c201c00f5880851400243c0780c02440a01100009101c580c9a075191140310580b24441c25020405000c0c003401c1c0c42040c001e0302e41c143c1d4050b40029040f01d654445604000e05903030320502c0b03401c8021001400280c407005684003501e009001c000512400d588400e0200440350b0313402c042e480c08100d030502041803241d55600810700c10140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 675312356 1250 675311106 675311113
    0x20405010219050c041e05042004150b03090f1f060e06010f0f0201150f090509030f03060f0414070809010c11030f0901170403180906061707140c 64
    0x585000a8200480c080c2c0c14840c550000004034003241000c204481084d404460003d02c02918941030314079048255030b4400c80e246031500304810404402c095083c41d003568402c908040403242c040100b0303240c54030080d058003070401e0340811100540b01c02071904203100100743c51030508010069468140c500c16600c0f64491060003c800c11102c80c442c02e0050701e4030a40311141482c040c00041e0401d1041d1416104000200445400071403007980464030b124410004981e140b0340d610000e00c0d90000f5405400a19490f2401240004100200b1100071901d80c600c032505540e2000d0420141021a011050300592a12201c100d0621001d0509200340b02ea92503000c12401d00500003070071a07548210350814040356031980c50150000100341e81c050340c40d90031107a55071a92400101c8080042c041c03045915000e02040c00b04254200c0402d0a00603428401040200d60340c40082c0103640d503d1240b1004038504000800c00c0120030648154002c00c6414208000445420141c50380e90000402e864281c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 675313606 1250 675312356 675312359
    0x815130507020307021f0815061e1c240f0b0f120a0504120e0a03020603041104020408100b0301050105010e0907030e07060201140901091e2402030105090f0420040b130204 75
    0x350000d40c1c141c0c0008d02554103040d13500c04d03100072a6040c42404000907a8030302248003051854030003011542801314032011030364082a034001b1840a402c03020151006609032000b51408803101d60800401c40f480c110109540070f280c2145142968812506580700d500704000b403d95520b00c5c0b00086001740018040001c3c1480d140c207090861242103c00d001c104141140074000c01d41d900e8540c507064a8040b9000f96880d140d500d088240c18607500303030061b013150001ca000900750001140c1503491000d40c0800340201c8100e042054200d4109005080c045030f00c2c5400c00317141b42072554034140e010400b03040004050000c00440c1e86000400d0b0700140050391542c42160f4465094502a90403456001c0280060401d6965200d01469040042c1c0a100013400d0210709000e900b501364000c000c004403010094a26221840010358000d000e254000d020040104040784640500c40744106c0e00100b4034000041580030340c0c07540c4c0081c640f030a0b80c000d4861452100d00e9032520740003c020b2106080050755103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 675314856 1250 675313606 675313669
    0x60d0f0f2a050f030d0206190603021002060714040503061302011206030b060a0906050307150903120504090b03030325111009030e060f09010e180a0b01081513050702030702 76
    0x100a00480c1a0003038000c0340401e08042e400084040e0001508400076180c040701c4203c0c0d0004027496403000c0e40c40704900b100009019004200741c0c1c001c00305641c540a10f110b10a0400c800f40c42035105407070301030f889a00064180556000e612450320710516151038468210580792096645d15041a107160762510700f480300034504908404000d14203d0b8040c41418602400283c5a050b00d214051100804600c13200400d072203854004017a641c8880d130105108507034140201150085e0094010305481e01c008850340d4074001082d20300c15801100c15058081000e80d52802c0b41901070381c0c2e0703014812101c0514220100501801c02c1d0a103a640340010003080301d04008103041150112039000c3c1c2c104215513208502540101c81c0c0210f03003800c00114800e03160010a001a50150401355020144000e00030b51080c0d9820503010b00c0c0c000d0f602e19400703407920f0310100e08455880742c0e050b030305c40c515109042603880c541e0010355002010340182d0782094426004101030041c2c040380e4003050a13030381d061104003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 675316106 1250 675314856 675314869
    0x1502091809060f0702070602060606032e030507050f10030f18030e1003090b070f170415060605030c1c14090d021b01090b03100503010c02030a0206060d0f0f2a05 71
    0x450905c4c40240710181c50004041e440310006000280078480001c0022400544e13503545501c0359890420211034507403950581480c03008a40001c65250041c2c01d00001c4514198515140d5200c0c01030000740201003103c0180c000340f180e111000d074910341701c0c4101da1007840c80c1c1090140b0180079844400c4130007072103005c01943d140107074030f8201850300d006603c001103184203649950024041c24030800822003e10291034010100c032440102651010400c0100a8203502420805c9000101071080d981c0300c6500b51100e0208450510901800340450030f902d5845211158107440c1181000400c0710101584480b110f908803200090750b4081001c008010f5410008114408605071100c880440500b00081021100d0300c5a050b03a94408030205d0030300748480341904020f004c02402080b24031074103007010751a900310074900d10140c010b00b0300103007441c01c1210114410b2548062194072a10540d90b4000d00c0e047d01880c01d462020f60b020b000001200004191072901c100d01c002000d2080c5018208100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 675317356 1250 675316106 675316111
    0x70303050108060708191407201b06070f0206030406060807232808070906050a1203230708090406090212161107140901050d1502091809060f 62
    0xe0b1030b4401d0042144090340441055005104152500760000021080c10040c1845268100061000030103003d0300c0c0c2e81060707807000ca00784040307200c8441a0f1619049502c03601294001c036000b0b000140c40403400c2c0780c0301e0020303c1041c0c461b42004859003143d4010031100c0e001141c04540856807560700307000102c010001c000003000d075002c040081c400300f0710705a4010341e820450715005101c89400542001c480e140c04101d0320702801000c0c88103a90700c00303042d640ca0a5511500d98410701d00000031909040c150140340c15500d47d5680301d18110001d03036048841e10902e01888034401200000c00140315500001884182d0240c080580c44809a004100860300315600c44203501d4410043c00c0c541080c0c01211a50201c04005000400c0c0101e10081c0c501030080a2040c0c000c7c003d000c0c01007508851182204001d03501034a003030041d40c1e01e80701031090f88480d80d90064680754001014481038080341e0010030300b2074000b500f811440245400b04032020030060b2058000c94100c070b01001140c81c1d0070015180d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 675318606 1250 675317356 675317369
    0x150b010e100215041e030804060c170112110a0305030d050606090d350414090c0414060702130c0f03151404020702030a1b0506041805040303140c0703030501 69
    0x580310340c001c0656180e00a9040d80010600d500000f03040c030105495400c110700302c0340c0d041507082080d0301e4000c041801c200c500700ca0f0b00c0d141c1501d807040706105682080400c024031421070303082d90a040070680c98a66580c001c0b10001e99402e1102c2d0141ca5040b14000214499001140c40e40100c5801c03500340c8030028401402040f00740140103056652a07101d43d0a20f80140042da16503c035040007c0801591000e40d1202a0400120414058402c1e0041041f80d12000540040140f07403401c000c981d9070306941c00d040000e0180000c0c0000384001d40340000d1103000803c050700c1d000017980414500c0ca80300001044860340c680104620b1038100d00b42824615107032404118001400042d1044804180100c4208002c0f0f01a010800d84681e412121480d0b00201100d1040080d480d00303800850074403c0c041d0b080c1c0d03a58a170003e510b04002d016a0f094841461843c1820076841d42c13203000801008201b60205603e03030340700b41c842c1c41d0711400041c0074800b1500a00e0399503446041c0581a0f400691080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 675319856 1250 675318606 675318619
    0x301206150c0615051e0f060405060306090907150804050c0a0605190212040834062f0102030a1503050601060302070f080309030417060417031003150b010e 68
    0x1a40099071105040c1c406550007100001e181030303468a207549980c1c0941001d60040c0c4d1541d641d203a205c1a1344100101d604080350001c1001542205001f040d01662040c203801c00e42c2880032074914901481001c1d4004240c1044904042d994810300c41000e80701a8020701240c5500f00340302c180030f010f0041e0317109088140c6811150600d44032008105106022500c280080150040e061091007405149502c1c101e165149803620f0f1159803a40d01c6802c8100d4060b681c40742640e600d01204400102001010121621200303802e15044003030b1200c40d4800c100080c020240c90240d4640080050b010303225002c1c034400140c407440c1c0219014200e8840c00039680510a05e89030400c001100000c1d030034191a683d240158030ba148601c0c0030200c101c02224000c1011402004012001c10b002020307008031840058087d407142d10302d0544a4440c40f0a98002e4079008441c201740c1061a0028010340c0c2140410080555080c1d480d110201030a420381d019040460f05c96540031001d40e803004c008074000d50121040b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 675321106 1250 675319856 675319889
    0x605071e081506030c0d020c070510020619110c0a030f030501080f071e050604060c0b1302032d01020a03060305160e070f140301060e0922301206 64
    0x2601090350360345a0b622800d000800a0052180401603600200c5910310075500c0c0d01203140c1300e648500941c020103005a0344006044809480001c80a025541000700840151f8800c07610b1006498044842c2130080400c00070145110810003c20088034001d030380395505c0c0390701d405000702500c2069000515541c4960b241c910a0600443c3e154100c400c0c0701069078803014103a0005c000703681164405a4401c1380800d00007030f95134000c400c5100710307031250915401a6984506521207030015403c0690164402d8030018600031083c0c60900354000d4880c0c00c600106210840c0a09a0703222003015000240c07280c2081040000801401405a8001c0c00c1407490600306000c0c100b0203000203042c0000c0150304101c101805009008070035404880640381552581c4075070340517140b20b0301420402d0103403c090001038445036060300c00c00a01401c02c50344001041d841d4459521054403c07485008030012840032580304128050083e12850407030300c819440142924540084034260340c400e55418039500702 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 675322356 1250 675321106 675321121
    0x3150f1401080d0c0203240a14070509060703030f1104090605150a0c11031615090501140d060801230705040305070b0d09050609100612080a0804020d0605071e08 71
    0x1003c218040c9103141000c4514610700000e80340001004204054000c0070b20b04030604440b842c01c20307120300a5404184112405003002c50110401100c0010001e82c2c1407020440e1440c100004003003842c00380c07901041c0c000500301d042045515488041034808400a0304101c1505140103100042c00c04582000104800255038a040d02c1484002c1e010002003922150400c009d20b485450b4802014084414500107074032a054040001c1c01200c0204c41c250721a40b880d00d11034140030040d5001a592614bd0084115604000d50403080070244034a81341c3d08040b0350260300348201c0396001c3d040706a1614100e503241c41c01140c2400a0720342c00802c04c04110171b0010600014119046805000ca080c0da510428040360380205410f8000819a003d110240902c644001440f8814410030100401c103032662140440300850316038400904d4840180907811905008803400344d401800603000c00c00c00e054503960001101c00c204c84003004144a045034124162241c00340b05c000e07520505050402e410080d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 675323606 1250 675322356 675322363
    0x3f2001050103021c020a03062405030d1d060405030a0501230c1c0f1d1e151e040305040f090504020d060504051c08061905130b01030603150f140108 65
    0x98103d898030030841444e8215291013615000030354003c0c504015030900980700140303091003018617404160129031b002c6014600070030341c00354104568079034980000901e101c1104103480441403e40c00350f4280400243c1d80c905105c03481c1403d209000000b050a014480c408030f0900650001c00141201c80801030544c010354111282c4a1403412102d040c502c00d400c00388003034594034044410b011300703243c4c041c1c4d50305240c80d03c07100445442e40190f03410f40b9540490396945100d1110380070801d610280002d460307240740410054210b8036480f590605850301c0445410310002c159421000074000003800c100c0004181c01f20000340040e11000d10482c2855000203111707216036040900201d079560301080030408104a0780134503000400c3d08000380b400050020b0518034007203032180d00038001c0e20038078070801c88940712340000d40d4402050741940c9110801010020215503d00314140743d030720342020001c02d0200d0710002702e00c004120042018182c404900d4203031900c07405590451000d2a005020b80c59000c1b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 675324856 1250 675323606 675323629
    0xa0b0711030a080405010b120a03080106050c10051008250b0f0301090b1f02070602060a090f03050a02070b040b030613090c05010e0a05090705071b033f200105010302 73
    0x340b400c1001c0d516581045c82c0109100038000c0c0c1d00500118170070025081c04904200c64034000e4450844a03130740c0b800256414492070f19410500c0d003000203046910f01d01c40e0b00c21a081a10021201b00075610350030b1b650b14004454501a604254007551000c00c503400100d42400340800d02c85050030204824002d43d038500040c0a046592a26100d810b061510740c1825100040400c4c0c008054a44000c14080e4895149008400040c081c02c4009580507800340215201c0d184d115040620395803d9460448031074200584503411801940300003d02e0f4a1349401403c05050b40c40c0c40f0555a08001c000c02880702c51005081c48031038140451000416002c6103a0340858a0a080400000c0c0100c00050a010442c0c0c10071076000d201c0c00305201d125640038001c3d000242c4036000d02190003009070300d08507910380c8602c0002e0001c440d0a1800709084800101d1300070013100210b800445003c98030b410309141e03d10701407581c0001c1078001d560110781654040400d11241c000001c008550444d0040751040848 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 675326106 1250 675324856 675324877
    0x12070302060a2f0a20030405210a03030c09061805040213030c0305010b1504080c04020a0e030d0804030f1d0d0201020304030804030f0210090e0a0b040b0a06020a0b071103 75
    0x1038125070b107000800d58402c007110220003158114020982e003c43c4aa035008504441e0005481c070145031200c0030000c0d01c5000b000101401103042c5031908041044101c0c0c05600c0d44010b90f01004035200d00f1004101a2000e24441c1e140419072801000000303080d4100c3c1d6014074104410f0301107500b0405041800e40080e10070a03940560384a50f075410480500d805944003c000210b030310b40c0001400341c1940003080e40801120382402ca00915003140000d4011030165281035080000d40700701924203035004150000340750a10003207401d403020000b800c00345034054100c00b08500e20100300070181d02080c18111051941042901541030341c210b42e02400d010b4103498082d00c850a505002c2d6070080003681d004580c04000c459407152203160101c10b01069001c03c90154008801000e0340c0d0740070b403150005550016000c5151617803407190f01005000501c1000340c21907910a000400394a59488042c0a024181c0041c070030b070469854a50007275040101310384204146240c541c0610f18000c0210341c4a9a42c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 675327356 1250 675326106 675326111
    0x4030c14090f0403360f0803040b030712110a020d120515060304080705010e0a030f09060c1509080f0c06090c0307150504080102041202010f030915020a090909050f12070302060a 78
    0x482c5d0042840c100d0300860b41c4140a410001e40d0200c0ca03102c5031461099814254003208959070f1102465940e010f1401580f41500b001e2000494041c400d6400d14007101450030007280c05040071800e800d06620a84001c001a0441000900503035004207102c4120039003214108010300c0e104a0106030007604440303482c0b0495000020400b071001070400d8800c0640c10030020024a1580c034151590f81d5132000c01200890446824443c10074050307010401100d02507194800f54031141d541d4120030800300e01d010f0440c00c2d40c0b1907952001c102d6030000707011a014000e0b0b800e175503100654902880d10400034243c013000e80c003210380e1a0494401280d004103c800941403003105108004040d64980616000038010398030200300002c51840c00c40112820074004c5c0c880c0440303c440391100318152001050701908014117411540e007414040d600900d040c40e25483c00c01402521140c41005071110743e5803d8846500610640394820410f12105502400791b8000604d85895942c000c0c0d1a0304000702080b40f601c0c2e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 675328606 1250 675327356 675327377
    0x10f0201140702012f04050f04021c0527030a0c080d0509070905010902031003110102010207020a0909050708030a0c0303051302031006030501050624090105040b04030c14090f0403 79
    0x60007500242101542510004aa803401040c024002c244803010391181c80c59681600448404070025000300d000d012207440e291a0401d4241305884c400d2400c145e420690030400e840c1d100c0c140d040b40003182c0c49050340104142c00c03c4c400610315031090142c500c40c041805e4540c1c201c0e1900c000102c0c4c03104841c50400c0361140c0401d0818203220b0103081c0111610504080400002d100b000c40d814050350224041009507076262604d590072030004464080180200c1c040c00d20202d416840100c101030390510000d417500141d903002c40c03405401980300c03c190075141c070100820014144002c001030f1011200650800411403001001c030114031001400707040d40d03039021410611050322841c0c2e489070050100c8294032100303401c01c0003d005512003a282035103020081841440d000103240c006d410107140803507441c0b4103403400043c154441e1880318140002084009000205e00010300000e50044e40c030040c01500d03041641529401c1e0500a0744601113040400c2007290801560642042e0540341540841 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 675329856 1250 675328606 675328637
    0x201320a1104030807060509010f0504030e0f0301020c070f08070b131205070e07080402090f060a030602221212030203040320071a0d0b090c1b031c02030402041a030303010501 77
    0xb8031664002500f20480010781d8018042c03a42c000c1c40c0144140c100800c0802e524641420803038100341d9004000520310300116449150010800c0382e1032100030001445c080d010540907250002c83d60028548130880315041021440910075140100a00c90049241c03407030102035040320700d8203030189550920300000701e4014000101300b2140501110548050903040261003e8092442240c04910520621000811750340a698000d8020480900340c07244850465549001941010302c00f1400c000030009440105040124620002c200b40010301d0050781d01400d00350909038545495000f803600408c24080000d034032581d40900c00d802c0c10000380b41100450301c2d0358240300d50740d4492074002014600b1140c03000040c4004001b0400c003030320108452403000080c8282044200c074020f80000341489014158103a040c500e01111b403c59050b07a00c0c1c00001211011900480340040c001c0c154080200411414144580f01410102c008524180d03640030002903964481401a0350401840d0318460551 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 675331106 1250 675329856 675329891
    0x60f0e15100e06030c072a0506220f050a080304050109180e0106060509030f010513020d02030708121c050615090a09090803070320030103110604090c0201320a 70
    0x20b01100411203507032400c100ba216005c80d00110010365045201c424041400b0a5415003846095032090003542020b21740781c2001030940000300042c2e280124104103580c210f45810042e400780184121250b03c10b4189010310540900c90313008804c042c0d000300024815681c01031021412660203204825840d02d070310314800c001d8050303110303091010342c00e010300800c03010740103000b40403030000a1f002c5170168107100112a083c0d407010354090803020207441060016007444481e003c00d8a0000c0c0c01c54200e0b035511100c0c0c5160900350740c1c4070480084c0109151504103580c0390100d154607500c200900032810850000744001001c0c03000114001c40002c0c100031561034540d4a035000b0451840700700310340e4046060240c001d6008603418000245032200c20341c01e1602d405a80605a80d010000605580c01d47d0340340c12a1760b0003444c0e0b81c4d5101c58240400108000c4900580051444980c008103101142e04526000d1000b40320700300d00303500000901084d03486c15071100c0c0e503442005440e01140c150700b2103162030320 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 675332356 1250 675331106 675331127
    0x201030e0609060624072006030a020d0c03140609070e03100e010e0105011815090e010b0108090d1202030c0f2106060f090108090c03010f060f0e1510 66
    0x1850141d0400c105190401060881c071508094990301c000c8441c4c100392900150004100c001074200034001c80303001c00c909076224895240d8890010072204c2c02400010015081105d42144190700020300c14403050060140c26401015400c05203e280b00003241c00102d44130041c400b60040008a00050406118201d000c090401c0582035034051300ca410030443c041d2040300c00e24000ea608003420754101000510802d030490b41111902c09000302c0400282014283c3d0f40e00d601d25076041c1800118440c2e805101d42e2580c05580300000500c09000c5001401d1200000c201d0f224039008007020b0340503103420520308403491507110f10050f030781d5036100100d4881c2c1c019145004c02110740401c1131902c1481e0004240504021031741a118544c0d900420807200d449444120a81d00d60103011180071540107030181500402c001040c0c030644611680801d0846500d910452840c079104c070410046034a004881202a0801410020b82071030079039049541071007403a041e1402083ca2181490700e05218030203000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 675333606 1250 675332356 675332381
    0x80a062c151c03020f1b03010506090114040c0309080d05010f09060b040308071a0405010b01091e141c0615080a110112060b070f03020c090f04080304020103 69
    0x124880c119210050903068031160615060826501041079091285441004040000c000304104054403410100c50070100100310254450403508280d002420f0200f11080030109440c4c24032044500201801e4a0f8090316240c068a8950014007551041801c00002d0700c2d0240c0c1d01258580075810b048000703140110024203816004550715a1000c0981c0299048030800e005540765943c903a812203003198a5440742c203507050400c00081000610101c06042e005020340c54001c1490911607801c0001340007160300312074596407035a4440066800c841e00300040c0600d540d4072007100352000b0450218040d10300481c00072000a500204103035a46001d143c2c0300d003007150448403400599140a4000c0c18400c2d120700b85540f810ac40102d030003a00001c1e00340005400441d54408034190740d00655100091131941c6142e591600c1000c240b07034a0790300040c100a440307240c1c071181d0950142002030910940e86a0b0718030039200282405501a40c242c0d15540060304464030a50b203459510040e0000c1100d000c000c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 675334856 1250 675333606 675333629
    0x130807080c0105162f0a061d030909010b09030111130e060d031d240702040b0607050a030e1c0f0203100e03180406090e03030a1b0c0201080a06 63
    0x110030840d410010303001400d581c400038049510741c0c4800c02c09070000e60b82401e0015400c0d42418011222840c3c070402c0300025440c01403903070300e0440f0106085c03101004003550081c3c0c6824262101e840002e40a41240b582c1034091410b000c110700008407039140611881c2100340000c0b4120b83c0684e8207601c5032403401c164180540e81d4200b003044490304100e581c81008010f101c00300c001800c50401c1e800613140e440d4960b9a00c00501c1d60138030300e0415000d030400345c03d4000003003606003800a107204611140c6840042070440c2c0341c0320300e4410002961103007910280500c105100c1031340020b4000411040072a89403c101000e4003140011030025851416035060007842901400180001400c0d1070089038000c1e03054599861402004005584031a002d200700b83e4410000403000e81e0907030f0f801a030700ca600100301140c459924402d400c203403000040c0780c9032160400001d0080b003101a01c240340303110700d05516081c001c0201200107440d05100d0080070341884400300004510300040e5210070050441923861 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 675336106 1250 675334856 675334867
    0x82e051011010609140606180a08100506100f050a05090634080d0b03150c0a0216300b040507180216110a2117070f0b1308 54
    0x100203074070380c1440d8196546080000b05602040d0301445001d292000113440303840d00c0741014030030154000d190032000907452003070980c526031358449044003d18104006122080008010404980010302032600c0307031000c40d1683d0501a0003940030310815032a424001d03140c019041d01641d452144186695100c4000903d18411140c1100500076401c441c4407502c81c0c462030130700700070b03100040c040c8041d0507000c0a02c41010b8480240c0c005c120310010150580f1001080e001c01c814180005884112042501048440899504001c1c8288124100d80f140c0207441c1b0f800503124100500180c9400e034020466240708034120081c0c94039801580c05404040d0303515080c1072a0307444020383c1c026000c2c41c0f0104580c0b01c00f90609070082d6000d03407030a5842c00c8034629003559459410030302d01300c10380d4006150600016008118200d2420380d841c0028440c0340381d03046490440c5c98490420b044e00801c010500c007241c00300b183e20f5034142007607074003604803043c58444078105200c07003c044500900d941c0e000141c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 675337356 1250 675336106 675336139
    0xb090f0d050705041113030f060c0e090c0a0309080706050402010e10050406080604022704060f03080d0f0e030a091d0f16110a050a020415081009080d06060c12082e05 73
    0xd0f40041c8c0350203144c0820102d40d108404a480e07100150242d5881070303264020400d00c2656074000e041344415400d00040808041c0d81341c54481e00241030644090340d49134108401c1d541c01040d0820b00c0c0d0b2084802e5000c040002c03401520303500882c003803c410400790341e00282142c0c41d1981107581b4080008503045c00d2100c10340c04007841e203410b0f060990046080200c0011410104201d040035254411042c03814801e4040900c4002c0c105510300254007620b8128603074200b80244000c1081c66001d54880840c01d04102000520b0b006401029070450552810860325403642d21869801a141c804035000200c40c40c002110f0082100314a040707540074900c0707000d08105000424100051090f101400b1801c0c00301c0c202030000800388508241500300c181161a85c440a50011098501c101503540c01e240b480b0520400f100c0e044c3c2c03c203201080c600f01024041c010403580c0628030380b01300d2620b074040d071900000e5002504e5440c030f20201680e42c200600201e15010001e04805801d0203080b10795032866294 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 675338606 1250 675337356 675337373
    0x1060b04150e010206070c0213090f120801120f0b04020f040507020f0606190302010c1502070b0103150b0a120303020f0a031e060815060310060b090f0d05070504111303 74
    0xa1140c040b0706030901030a425400424003511031000b94403401d103200b1f00341e001c3c000410074000c51412015034030020711000440304804828031a00840002c0040c0000c040d02806010043e045002c041d5100d40349400041d20250320101110f034080403071013954440d0b01c0882c00143c60050219442420041006a0a5400203400a10940070002c44410b0b8562006002d0020390468070824106403030351040c0055400f400741d8680e03061040c8103441c0f00b100c00300c01c088102e030414802101c0014407600108203001c1074181020701003010a0007013044070702400018055080074030400f00c000440380045e005050196040d9041c2c0c003c00801c846e48c1e68031500009004084103a010082c12007112400c458005c07842c40b542060352441402040030300c1400b00c0f40c0804d5a402003819030316104d030201c4a45506514014140244010704685480d59440d100b000200303010010b0360b1303004460400882c00403c000203101d10895005070350016415015428104661088501141c04a1083d2000100b04142e40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 675339856 1250 675338606 675338639
    0x30f01020c07060c150c0c0c031212020903100506060d0f05010608070203040b0301050409080705030d09112d010306050d121409090424060b0904050705040503060c0c01060b04 77
    0x1c00380d50185880d44401d89000c00d107000003400c01412446111131844096101d500c07a280d050820308000e1200c3d640d961204422900b088030110700f2400c18007001600b00106007200c0700003120950038000180b01117079841056144904200343c44001003041c1d80c840744200d07400300394960028440510000a41400f07000d082c40340000203050b031000a2021440442620103559818402601d0350b460042088040c01c4051000e0b120880304003c018000ba4041005205151107150041410541030600c02c1c00303004507400e840d0244101d03840d040984c0c0703c904840b60042800140c034646e800f0a04004030b00800700c0c0d41025400040c409151810f2008500740315145000da5541c004940c6110034400400707004078051990002940000703d80011003a001c08454081954602d4003c503240c003400805442c9280d1000e40c84050006244409080c1401142d521441e20304150b4031382894140441d03940c074001010b85003200d0000c00c09203410307076003900b0040081401100c03903600c9a484403038601103000304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 675341106 1250 675339856 675339877
    0x5040f0603021219060504150c030e0d0203090105072405090304151718120315180f0c0d020702041a100c0201020d2102040605070506070507260702030f0102 69
    0x4003a0000f05801c000403a82103030103001449594110310365481401404019208541e19181515942c000c1c00c513910a1665050081c1e60100305c588900b45428240004c4940c090219007040000da09541d0700002143d010310340c0070000107a80c044c40011011044008400c0c88403440c100781c1440382c41d0800102400541d421120303401c00c14126154182e8144c2c0030101e080503a6070b96900020080c94158071040d80d0000780800340d461280701182c2e008056401140d005114144039400b01540382420325104200140b4200c01c109030781040501e510110000800c8004e101310300240d2001c02000603015500714641c040e105001035100308007100d04015001807903070b00801e0811010b901c80d84c40b6002d00412039406801401100c2040d40c41190006001c070080000120442e00e0b00d400a00c56200420042000d0794529031034894501e07003642000030180c1414100304d818404200841d22a911403000005200d500d07044800c2c0c41c0a0a17241809100d401951502404400e400c05036410340040605888 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 675342356 1250 675341106 675341119
    0x5070b070507090203010f03080c0a02090f011412030906090310090303060e06040209150a03020c12090a0b04320402071b05030a030503150d05100c1722080405040f060302 75
    0x21100500303c2280400d210b40034201109070420804904d249004140704019071060304c15811054010620303ea030162400482d901c2807500400203105292034030040795804540d0301d02550014040d072541c0b402000a018840d40000410700d000703690070011647c202c0d400e00f00a2007607891a01f0050020129403080d0306091001000060092409200315110814020922001d8112509181499800030409142415801c2110f4020300a007000a090807050f07000d1802d6030b540060040c27203050203d5902c07903240c2407000e000c140005901a4800080e007481050000e40041040240741d491040180d4840e030401e1000481c5400e2180c1482c4400e0b49040b1a58011126540c40c014540d48410400e00900061000c1c07020940c403081035072114140b00d40c000e10301220807525071611401d05480602104445030740d8411602120380000380c28040b60900c400c0e1183d41e00d01000d2500c0a20017080034040030703583c0031100404000600c019107000c7c003406403040004600700e102e240018075650000760321605 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 675343606 1250 675342356 675342359
    0x6010305070309020d0b0411120703060c0c1a0a1d16060912140c12030d0b010e060904090c0f0b0c010e012c030403050a03050406030b03211605070b070507 68
    0x42c028090089000d5020b0040d05a031103c82e12521030b080700c068021030b0105c9102c0188a590790b0354140c4094841d59610151440ca4a1071921030110780d00c0c40711080c144812281d462000c00c42d5884030b26940c11219802005503500d80314185c00409041405204503145000004a8a030000481c0383d48a0740c03208911506075101c460941d00c41c0d0840c840c51210400101000b00040c14000ca000f805150702c0e0111800155010b00254201c81100301490440e0310105902100007010701a14000e9003085c28111481402c140c0070a00620403080000c0c0501c0d280c1e440c2004000c400d603180c00052102e00180d802640e103440181001c0c0c2e1201045116a40c00e00c0800d0fa20780c101072154494040051111642c920700600402c5c0c1024481c104c0100d20340403e001c0000402c20511050000030301c00c5d9500b981d11400c20001404540200070398a000c0d920404000803071400c05940c1c0ac8202808002c1d050300e42810000e1104403040882004045000b8203200140710107500029080d202d102c3e0066a8506 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 675344856 1250 675343606 675343621
    0x203060901090b07030e03070606030303051f0305030a14090a030308090d020f060a1509050709031401090f1412040e0109060531060909140d0302090a0e07020a020d030806010305 78
    0x351940702e009481010441c0100340780300d00903480b22007508619000d480c00e180503516180101c03002a441500401e4032202003001801a5107004800c198200c0c00071140d050464031507a90301c0c01040e0600007400542d20603580301d0381c80d8070f03b03440a5540c000c040301d42054132441c009000d404252006082c074491022026202070001c9010400c03111403c0042c0f070346655401414018011203000040c4915100e0b6000c2a80707543c50049a02c903c0540d151861a549180f07002e0245000202d000d0109924000e105400141308948015403140c00001610340700b034484403650b0030000d0ba84d82c9000743c1840020000340c0c01c59401103071412a030303a03481d04004165840040c000c07c0d181407421801c009000c1c04902d412070200c00649082e07428940700c0040c0c89a2550081c10486100407400d5a501010070a09005154200804d000c1d050540c07405600303001c50080440d500c80703490b00550800d2455280080c503900d200b0040070040d00d40041c41d10003030b00c925003005043c00e40183d840600103403c00000617038030b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 675346106 1250 675344856 675344861
    0x30606110a0519020612130c0b09330a020f01270311070b0f0c010515010909020c1c11011406221104090b01090509100614071b030203060901 62
    0x100758010b00903141076061403010b41c0461100d0001280d015405211200c02e40d03e0302203400384540c078810040e0034515210705084201110561104080807402c01010300076441305076003414044690b5183d0107810311004400d100c5c110b01409a9101c540c03010400e02c00301d50340042c281104400181c000c000c00b9104102019007071030004005200c1411208500780000d03c0380d640c2c080d5900f00d240668a01d0354484900001b50341c40384074200f03490200031411340804003080c490290050f040d2035404440c09207050020b010048280310f59404030794003088a41ea80c61045c090811400704d176146104c0f00048070303c006448402da5190645082d841c0c8200403200e00300c090720450040000801000d4680016000a02c07148401c1c0d1400300c02c3c945410b2200418550364002e4400341c82a80001707d55001440001411134120b94000340c442c110b4001801591040b02102005031500c5140400da00f07041c0d200f040440c0d02c100070005011011b0318920310010342400800790203692003202038400544806614509 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 675347356 1250 675346106 675346123
    0x6080d080103030c030306080d0e040e010b030709020703032403050d0c030e300d02010e0703111207120602130b03070e040c020c03070b0d0b220c110102030703060611 73
    0xc204520014030100e4000e40700d000200b40700345070201e1001c5e00e076502941000182286440440c601c800d90171918905800b51002c030440040007040000d04010010781d80f80414401c1003049640040c00e0411715205e5040301b0062840aa180c6180b101600003c00c0e82d00716030721068416000c7e020070a8000351180c01800b07000307605a1b640c1d844c4015050200404118a114410307000ca4244d4410108061401091a06a0840307030107800d4240704680041d0a5031500305180489400c514400d00024401d14411080c18105440003008160360115180ca8209250410b081203076010050004110701a0018a2484002c0121b215001d554845580c6140020341d04400460010b00309000300303040070b52105da001c81191045030441004180031070b0403c2c555401180c0e85140025400d9007055079402074820725107055614100310040e40c9070364040490b070500310001d400e458900b500580ca00c501c40084034680404021541c07401c22070b00c0500200f0041c410600411040c4200307002e10940452040d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 675348606 1250 675347356 675347383
    0xa0c080303041713181805060402030705041e0905071a0a0f030b011706030712030206040210090317090402190203030f10290d0c08090606090103030915030902060f0d0608 75
    0x1650701e06040c6400880c1c9207181880341c24542c1c4d01b0700f00003030340c00c030152480340c0c54001c00240c000c50030180140f40c02c0c900d99412042c0143e09000f80c110f001d045884440b030b03c11050000000d4804401d1030001e0400b5040c0d84008011001d298980341d07080f103868020712480c6220b40700c60760524085182541079480410409001c14881400c55070034080c03e4841c0ca500c410010b0a4688090300d8844030100b080d1f1f00a0305400581c0124108011401c2c8000c409001c07100301d0130103141c03051840d5140090b80c03044003010f6040c0c41e03010a0804068a0361b805036129002908800301520b001c400000303640b600101c8034400950000d0b004038121505140d03017007081d00d400c4130401c0c00c1c68020080e4600074801e00240249401001c00c0410b1855155106124910314141d03900c0280f03003480300c0510302c2d1a6010381454440e0042400400010350814800c6080303804a03c0c00e9050a013410909400034034201c40301070340150000880c40380c140c078507000400804000d500308010340f54986581c40d40d904444501003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 675349856 1250 675348606 675348637
    0x109151202011101020d0204031a040f1b0f1d060a081009020a050d060504030f020c010f080405100c081b09060d020714070602010902090c0721020a0c0803030417 71
    0x28405251240c690000d100d006043c10000d05030310155141c00c9070b2088050b40713005640400e040c4200702000c0015401104041c48000d05400c054031140a5241ea45000800314851405e041070181c002000030f0000300300040390400980d54404a200501110042c0c0c1c0515042240000345207181200244050b87e074110700070240251001e041000509a8100990303100d400038200003680e6a60b160343d030b61610301c11500403e1504080c9005081089400006000d540207884801c400da40d0002551a0682251601034082e440300e09060303041c980c05560180020b4100319036000707242d811240950064402c8501e00e0410640b0003140c1d0300d28050002896400001082a03200b01d0707030160042c00040b400340d44104807003020303002500d14280700e90b400701d07015075100c0c28514290f02e44041c00c0c2e64000c00c0e02010f189407814558401602d00d010424106401d814191406001c038420049481c0c0b19a01000d54002c194030746401c690b90b0740003150308842a1074420030000002c0c0000e000c0d281c028041d500380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 675351106 1250 675349856 675349859
    0xa0b0411120d110c090c090102240f07030905031207090501020f0307063b16180504080c0a030c0b090106081005130f0b040606050301020901050708090315010806010e010915 76
    0x1110740b100c40b00c055024620403c8002d801171350314885014000c1c404080003940d58034010001a017441200d2400307909c03141081a90403210b01d14903c110341d00c00841c906003441680c2d10013040e0000c040000010b0403034400404c01d1603e0341c1340131102c180162441d888089e82c00b40c0d508012039984040c0c0410081d240c009000c1c420000780d46412090203004d040020f19154911100706074454012000c1004181c40544141d038028681407180010001030100c3e030400344c604200f0301d4944a00c100203801c2e00d0990f00d10014017406020400c1d20540388030003040e0b031a21619070274001c01070b1545000549800882d100480c10521051040e9412513503150b01820b5410090080400207005c010301811036880742d030344540e00140c088407030446000d120300300702d00039801d03d810007404a13500c1d6000b4070700036803040090465980c0c2000940388581d90054406503214106000700b4100264028144050004600049003900c408070715107050f14031aa26400380c03680e9440580c07007990680306801d07803801c141440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 675352356 1250 675351106 675351133
    0x807033e150c1506040e1903090e0103020d0b2701020904050c0304050d081012030908010b0a0b0d022203050d022a0603072706020c030a02130506120a0b041112 70
    0xb00c6a038811001000006d0b07410700c6e514858100805402086581c0499440110070180c01c952903402507d0044190700312981964003160101041040181c40d041168000a181d240988192040e210907550351000001a12174001d010750014100c0034821403c220000e0840114441507a104903001f00040c04441c00c01c0c00300f075611000c06402110b60314061800402c0e1103800041041d40980310b9136900844500d401181421202204525840744906403000c0091700346001c2910220383e074030070005903610050100b000b0108011485e0401f50748580034004280f040106290384910055002c1d60000d2240c29404103141c4140036002a20b844061603078000c078140300700696441090303410001003100b2000d114002c0b40345030344040d94020162410078800d0981c14031256400190540c02440da02c2c01b03a03400559607082c4044000607103903480c400103590baa24000101903802c070444c280c40f000300d1030f03003441d04100a040f2001d41302d22070307124120380c4c007410a0354814410b60990009010702d04e40080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 675353606 1250 675352356 675352393
    0xa1103031510090e0f16050a02060106030f06090908090108010e1e062d0a0503070b040e150d051b0f010503060f03032203120503010807033e150c 64
    0x2020b001081500034001c9041c1c44106041c5002d070508040602481c81c1c0310308915510030b200485c0000f0040300344550410a5000034000f4159075003400c01280401d40d80404400415603580000d20150506001c4828800c00e00300a1407201005c1c0c0e01d51015030380f06e01e90320714141c03401d94410718080d403407690b161581c100d00300320550800070081442c82104904517111803416402580400daa007002c45411040c1d18000002500401d03068000c0c0c00719620701450810240150710580b00c0151051000400c642840c084810312664004e02d444000c0c0c8080c14034503580d128001c18895000b581001d40242441c00c0c03220900c2850059644a2440ea929403d103c140c0da007868141340c041c4001c3c0700e4288500f0f5040300c0100341081c8442c00d03039111403450a02d0011110034540c1d22007813000070401440780c0b12011462030b05036a00401030310310400480b4840c4184961030460050040c45107940d6088074040c08081451302c40d401c50b0020406110341418a0b0184200c08420107650301117010400c030803a514 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 675354856 1250 675353606 675353629
    0x60409030c110d2f0405060d20040903050310120b04020105071a0a09060b090403090317040305010c11010e010606021e0705090403050c0f0105040b0423070b0a11030315 74
    0x10f030888581d20400c1c1d480d03007080c2c8000740c1610361210550414004075010380c0c1e82d0f1152120304803010301c0035081400100d00541c1e00c8520291084c2d180040b42060b030b00940b641c2a00307680c2c0203403003003001c40e10500300104181c205844140c0807090a50b0b0014602c200245000b50a58000509565170744444d80156115400b140c0100c48002c10344108941003030100200c2071003104803c5000c00c00c03202030f1410304202d500d03500f0002c0c40342017081c2c20701021030741c012a0700d01603e80c085c905c0c00042050080c0d00081d409035500050080d82040c801d20a01c55110070643c02d9509044000d02c102809c50106900381c0e4018016040168040761035403c40b15041d10080e03005d1348461061b00c90301600c41d0042000c0d200200c8003900841d500041c4800341a100700040740e242c0805a000308070a04082d0741304980d04c2e01c05040a005a08494185c2e01502032003115401c01c540c1400446401c1030b566094a02036400c008007100c0132803c002d10501100001100701d9205a80760240c01004550320410011a003404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 675356106 1250 675354856 675354859
    0x315060117071e02070501020106051c03080601020f01020307030b0f09310501022a07080a030806120a03020607141c02070501110d061418060405071b1a060409030c11 73
    0x900e6901c0101141400e00400012619809017009900304000a420355169511150042d004c00c1c2c0810010212801c41c8510b5592514029209444840041b46040900020300206500c00800d0206035174159002a4100b20159000306010b0344480c10009440c0b022038202070310090080404215a05582240c02500c03596401d446207541291182802c90f080b0065058803500c00b80070030146514400c01d6843c41000712802002c01c3e0b401d01c180b880e29851038403001818881046c0104800380d80c3e01c01c0256240c4070303000403200c0c0d08809046c0259102004c1c0c03520b201050001016401140780c1c60110346512070261620b601c6e09000c10440d40080d0b01100301035441c0c1d5a200c000540c20bd07100001881c00c4861403c0c08161142450500380f150400802c6207480358004c5858450640280c14015034801006c07640010603a84600d01910080c04041501602100c40c08222041220010803041103440326810341810769540f4007448211055000060007003a01d109009000480c0d944845030b08580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 675357356 1250 675356106 675356117
    0x30a050711010608010f05060a0f15090b03070c0314160f21050a0f05070c031104092406080111041e0b1306030b0114030c0702060c0d0905031506011707 67
    0x2100c0711150031101a40c010602d144d4560f14000710b0b25805d40502c40d08003004580307403102c29142c19003500c4100c02610803000f050314100321690070380d8001c00d00c003401007250f10a030981c1c0c0d01d001400200a20160303101100030075047c40c41c0c1035400060303206079040900c5000c500c0c1c40001260321002031508e0103074012540c0111103100803812441403549004554001d40b41c0540f5213008000203444851006c03041010040240640800304401e11405000c80b03800c4407084002004584c0460050010000050081d038400c0789010415100c820100819041444c0c00708403040d1902265401c0ea18404034040f10b19206000900c0100b680d1f000c44c030100403606084c0d680c002da5504030000745070807600d0555a1400021401c11050390103000780783c0c2c5038100b4a401c81d821403814149001501003c0c18001c030700b800224009046403038840403100e441c0784175030803200c03200700a190082804a207030064501130b0085c0a41c00e9007825103090514004d0030161207820840300c0314105680c40c210b008104e5802c108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 675358606 1250 675357356 675357377
    0x318041b02010507110607091413050106260618070c0c030503120a2904060812030a0e0d081918050f0d050a0909020c030f1204020109050f06030a0507 66
    0x91008408444440303064001007032a2403c0307940a003400810452005080d0061380c00c1000310365000c0040d100303540d000c1e81208514003159020528607800b01c0320242c0024030301030003c00e40d9900140c0d0380e969100004a200101b0b00340a01c0c10340721480c02c2d903000340c200b02040115805200c52150899000c2d10a140c0860b80c2401a107030001c100c00a9403045c2c1d41a000003866a00c1008451101503108103159014082c0d92100c0c1c0088da101d41d065994540d04100b00400c56010303642e15000a0010100c0340102c914040084440114546c02074071a144802d00d80b00c040c8424081c007164020703d4070f42585500009503500d0410800c20300f02104140d810503500c0d240450521683e25200080901480040c602030148825031490000a00803602c144902441046405a80240040c4c00d582d008500540c840050001207403442c0a0041d0078010b4200c00703d01c041e010800c0e840124441c1d4000d98550041581d100244065010059a81d90b004101080050be034084160003032078200e0b0045c40e291a112 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 675359712 1106 675358606 675358631
    0xc04030f150618051e090a1103010b06030702010f060e0c0f18060403080703090b1201050d02130c02010b0405060a0609270c08010810060305031804 65
    0x8200da49595990145070704108010300420490f03040503c0030981c0c0d200945011150828140b075000c00300100a0b0070710300301e82c0c0608135400141910703803c0c50b15846075207141d41d048550199260348421015840e140021489194550300008000401000020030b496032980b2540f654801c80007849039441035801140e880500c54440f05e0390701c84120110b4440003219000ea5a80450085000001c1c07002040c01400540d1103681c40304805c40e100c8143d00464000d0070706031880b5626910060000e4242142400800d900040c040c80340d12032480c82035820744110f800c007000141d445d103841c40940d0501c1c0c050300f0b410120482d800102e00c0d0400c40018081c2106104d0302c1a1203007a003040e0404005020588544c240009200f030018500241018150000a115003042c81c45940ca010400c03820b13511401003a258414003461030b040300140c91650404591907200d42c025036626040815 = true := by decide +kernel

theorem cover : BRFrame.Cov 675179856 675359712 := by
  have h0 := BRFrame.cov_init 675179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 675179856 ≤ n) (h2 : n < 675359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
