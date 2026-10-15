-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:32:16.361543+00:00
-- url     : https://prove2.me/submissions/c1e5d949-57e2-4c0b-b75e-911488fdfe55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 905575539 ≤ n < 905755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 905576789 1250 905575539 905575577
    0x402090402090303030a0b091803031807050411090f06040f09090813060c060f0b0a060513031e05060606090117060d051f1b05040302010c0512160320060601 69
    0x1c8141c401034122a10b1b0f08003004150080c0c084115443d02a811290000c0c49100d0740c5c131001c0741c11070010005946980c0b07400b001198040c400382081030081c03154010000c0c50351142d00c500c0581d041c2261660ba100e40c0c9600402c0501c0b807044646a10503a0144400d025980d104800c2c0022500c0c00100020022124a4417090740d004801a00310001190b40001581c547c0180c2c0015a6500c504010002d51000c000d1600841d140070700c00304e030070050940041c0704050140c1c00030b01a10b51980e0082d50201d41d60f50f10303403828070610880c14203540b031402105001c00c0010010950041e000711029070510000c900000e00d16030850f0002580401020045015034441c0c02080310041e40050a603981e5109070000e8410203070780054000c404929100030441c00090541c499600000d15640b020300d0549150011502000c4052060781c550165218141d2917601d200020420b4003010130500354804110708020303108030700b011400c111008030210740a44142000c1090340d400042403c0c110060007981e81620 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 905578039 1250 905576789 905576797
    0x60b040903080702010f0c0f0507140111040f0807180506120d021c03050906130c230a0819140a0b090703021903260c10141803030103020402090402 65
    0x1a00103162800300400d055000b40228030604140d00284485181441c0f0703c8225480e114131500020030701c00107017242c00d11500040002d03078001c0400303040c05102c000381d060071100c2c0700024a4101500240401100c1d003001300700001810b032400503000c12882d104149280c044004003030010b0f10350340c07000035006650740004404030545c42c40c1211015035414402035581d00010400108102c101980e03052620703c80d0040600ca941c0b620050907036516503007a1440b911000322001c80710349a020001081d1181d40001070f50050040c0840d142d01c000e568800e100072003e8580065615400c119030308442080460001810150b010943c010814610f0004908000190740000e00c25070540d0300b8044076801c0010303880b082c0e0b0300803260181312994071003420441b4080c6100041040940345100003405070414001c0c00c070a410007604a1414030354507680f6003449218000303a000a82e80c0c160a00128003042c210b190701265900307460700701c2060903103040d41d00e000c1403000074400d0f900020006140d4440750155 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 905579289 1250 905578039 905578061
    0x715090c0e0a0504111c0b0403020a0b07050409060906080303160207050418050f030a1409043803010203090a1403071e0605160e0409020a0807170c060406091206 71
    0x458200340e8552400f400040c3c0b0160380089a00300b50b82064076040b8030840d1580f554800c40250140566241074520300c000384143e0070341c055030300d0300d0010038100d00c1e81e0391042d41203540d03455440c0d04101040d021070340290071600040e03181010610480300c0010480e504116445030300890342501c0c4800f24a40507464100c150410306158040ca046801200140d03421071185003643c1c03144981304002c80c1d8174010307100c0000001e11800e03204070031081035400030800290003a102040c207010f600114410482046804401059104906411041850b200d01d4104004400a6103541008100c8960364402c41d80090311035400010361003101f90041049502240e8411601310144850640c942e8501c500f0140c00d0ba9914100340000786201d0300310302e00c0f0759880b81580350500c15107800814440200100304040340c2000950b040891904010007031704006108400b200d604032000d000781141041d41440c078280c02040203000c180042d41e0021156010b84400a1580c5510396060500d6030181c040324443d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 905580539 1250 905579289 905579309
    0x72a030e0a18090204061d0f0405070e010b09031b01080115090807120c0b07021c02040b1201020901021209090a110f0703020a02151603030f0908040e07090501050715090c 75
    0x203540c00d0761072900f01403030720b074000c0740c0c10800a030743c0c0d810002d1880030740813940100c22001000034602940c45c241c110380160042c0100c070000d540320324114542c0e90080c0c01c104040440271400320024038040210440110080c90501000d81d0303080c0000c1c10b80c20040c00384107007a00a084041202c103204020980042000104544a056440c1c203025078099445400740da6100381d032074000c601490807800301c59400c1e90242c4212400b44072403502111070400b41c9412a441519440e81700c0340c55554080203801104901c00040e038401035040064a044200c001201c0200c4050214003031a580d1540c00d140d020454031000f1035030314109841c0309102e00c2070118a821660300400e1134803d0640c0005ca9038410741c4260b904003a501e080c1108000c960040320b00c50348030301d20080910300003e442034206094032105000f0119060342940d89403441d68009400c10310010740c1040030003580b940d0110104005000c282400c1c5d14100135601c401203494400c40c10400c4107521044034408102e256402d441c0104812070f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905581789 1250 905580539 905580569
    0x23010f02030c0703080a08180a080702040219080a0b04090201080a050603010603080a0906300e16081005060603160c02030309060307020319030b030a03080a0e01050f072a030e0a 78
    0x1030301c179480350043c0301300c0340001d0f04410024088a444c4011035024000d4100180707020081603440078403980c44800c082341c0041d000d002e8101c907a2120026800c02c00010307140c8038103518015594004490200e801180700380e0a048581c000351343c02901042d000107045201060950b5141d01281c0500003d0340002c28aca08000303000a60182e00c100307010f00743d034450783d15024041c0700238503002856503500112002407100c4c0c041154034005039a00400012909209036440f00d01204465044800280e0001c840307a005401840c007840c00c18424113500c074100301c0d0554103601340719510355545201e50b80390000b07100e004011202503540400560701c001400034030542d52468030782c000a450387c0181094a514600070000040241e0090094408801019009006e941480c0e02c040f02c000c000500300ca11081d559404043c007080003800769911940714105034041e14200b4100c000c02190006100880c18610382000781384d04142c00e0b80c0c003a80c254044c609000c00e100394000041605015500031510603030744c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 905583039 1250 905581789 905581793
    0x5030a0b0a08160602070e01061107170f0106210209070207030816020907170c160f050114070503100b030402010e0d11120610060c03020f030f04050a23010f02030c0703 74
    0x403110f524410103042c10301076582d6400140d80e40c00c2ca5014102e1002981d80c014441d40e440383c0b04401c404026582201c042039500c00784c000c110291b403103182440d1b401c800c170080700c5902e003400740300000c0480c6800d20722504208440c4080c0141d0140009105501c0030010a200c0e604c200300040c05560400250341ea180c0d505000c2c2c450b02015104102d024502480020745242e000700b4200d0903080701d41080310035696403040780700c240350300c03008000790500103400b1040003041511201c1d0401c24030035000010414111176848144020040586081041c20001c1240072400800c0078001c80b11007007610b544079181c510040c3c95a6100441c50b40e044401035a07104148800c42d03084000040090f201c0c20b8060782e09010194403208100c0d2402d0141c04603080422005106c3e20410074218080e10640c1d061884100d120341c1103034882d1a628020030f401140c02e01c881e160142c181c2c401000380c8000c00c01c0d01e00c890300710844030350503400d092030600c19110180000d8a00910440750408031060a40e40d01030703101c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 905584289 1250 905583039 905583043
    0xf070510051c1514010804080901030e0a1b0f120303090f0b091e030a02062d010806220b061e10030e0d03140f070c0c120203010c140a05030a0b0a08 65
    0x18983c0040d03009000400941d1100000c04500b2424040e51039044c55501c03522000040c2d4454040c09040607500d02c00d460304524113200c00600c15201e142500090f0740350b6812001813220399048203034441c03104102005101c05860800300050341c1030078041b800f0042420103116110500b032020f40040b1240c0100724039982e000c0307021403800141808200b02850000401940c3e402000384520140c0e01c001c012030780d240a1242d40d039012800c0c005080030300003130781600395127554006c0e400561642e2204d001c0c00740440348042900000c62640004202e82000da4803071610460001d00014010b64840d1429001d0003c804900c0710040ea001d03095480c20b110201c8014000c01d4000c00041c500c3c0038960480e03a009219028580c08048134950341056038440d00304030107540c2c1029103520148022460303c900082c06c100c0901d001003000313050801c510b10b810300506081d100b41d4440d0008000000c205081040300c03070340075218101200d10b05513449a07646640b0900900020301007503400022528005030701c60f40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 905585539 1250 905584289 905584301
    0x150b060d0b04110901090506030604060902072f010c110d060c0c061413080c01230402030d0f020712020112060f03021305060901030305030901021b06060a06020f070510051c 76
    0x41902e0810510340c0c1d2811440c018054480d00364000b80e03000c0307003c22032450041c01964002500801c000740c02d5984588200c202e070311030034046411003105003e11b1410020810070a801c2482055009003502188000904041d0043d20080902c0500c82d0002d00036100c1d80d000541865000d0020400b40b00301100151001034030b41401c54146007445401c2c59002c51604a90307004107900f22800d5140f08869a644590740c00562a2000300d640c0c6200340026600070034562100100d05511003051814140141410520a4000f00080c000d00d04183c983c2c0c21780c00510708040b80d0036441000341d040e02c94801211600003482c0300582e483e043c514045600900d040903402201d1080300d0755104600200d0041080e0303007013103070410b0784044040700410109000d18029540910001b00040c41c0c40041e8119420748158090328110380d80c0454104400d9080030700f407490190110307000501e201451034050981c0c444860041c0b0f03010340709800a030b02c1d441c2d0050060703807411040340d4800083c60116000c07542c01490 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 905586789 1250 905585539 905585561
    0x804110904062d0c0504080c010806011b1115120a0c02070302041e0e0703050304051c0503070521390618070e010503030706200a020f010c02010e0a150b060d 69
    0x440c1c045a030030845d0180d81203404072032082000c0c00501c81000c0041d681da0340c005103901c0c1440310342820300d1035a03168420003140c164801c0340380041c5820000305020070344900034030b6042c40030070420100f20041c0e968290150300443c0100045904c541020049061141c280e00003034001c1c0c00d140d0310b40050f613550340d01100140350b101001c12044a10500c0307150f40c1c2c041403001070800d4004000c10b11240c14801c1249101071a512110703500d8008542d2107500d103074400b181c00d032015041803099010f0042807180000c910840d407812203003040c94200c40008036101c50601d04a0220101da103043d02030696a00034150310f22078030103880191034164250603d04501150078030076030091010208885405004250507148050011418851550381c0d1400070503503206207864985600e204202008240310046c201c000710345c0e01404000100d44446429034445629600540e41482d00045001d1400510001c045400c005104500c4111030199001004200d452641120380050640c000703e620343c01c1404510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 905588039 1250 905586789 905586791
    0x3105030d0c030e160302010909020c01110a031e0615030e12130e060108010b03190b09090102130902030f060105130905150910080c04090c05040222060804110904062d 73
    0xc043c00420010130501e4000240441e00110b0305001100742640907001d441003140000903000302c04402080d26402c003036441e000003034840642400c03000c03105816a480301314618050041c0c46c10304a9651071401c200c801c120400d541c48511104503001000b680030751400d1818019910311200c04c040c0a504228040c00410901c5100843c802d94401c5045c141281c03004071507079055483e080348048894500041c014501c41d00c4400d201215a0749240d06170003940d220000581c0c4000214411046101d240c0c0003034210b520620400104102d04c00009074400d009282407691101515201029a4501c0c1c0104054034500b90420103040780601010200800885014440381c3d01d95480709803628007401090380b59004190400001d0800d0b0304100e2400e4401c0c0e070325010950b11180494220303007000700c20020804e07011088111140030300040354040e0405240011852030252990138482020620103805240d90500050505c83e040c1e000d804000c01000c7c1c50a21041c45002c0c070b081c41090498201170355 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 905589289 1250 905588039 905588053
    0x612140a140f0903030708060102100c0e0a050a0506040b090a0f0305060f0603030307091a1c051e010609120221010e161406211e3105030d0c030e 64
    0x12401d4210920f00c41c0442c3c0c00210710310355034218211070080d00604036034198403c101c80400f04032128028402c03000b540ba601c1d08602c03110b002c100700c8100615070103240074010030b500902150301e03800d00f01d034103651100181d0ba81c1c4800d12008503c041400394416030b8911010100441003200124255014096501500b003070b64503000f00301038a900c000c0c2e45400108840340010071003d00307000209001070112140050402d01010203c00c06001d02c1448101195501c4080007801c200c0801c2c0c0389000c4211140400040d0306118020300515014007030a09141c1d8485201070440d607507000114000039a080754800c0e030246490080b406090007141c80341c19801420b007807108904111000d802290390000c20000c000d0504000c1c0185603208000540030107610703d1054000c55420361015005e00c41d070303d2111180080000000c2900040074151514051007076000c600614072000d0100e2500c00d03ea1404507414005141c154694402d15640c00c02c1d141c10b0948000040d505648002c0b01119240117071108 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 905590539 1250 905589289 905589301
    0x31b0f030309330c03050c07030507030c0807180504080403060e010b12030a050d0e0a05060c03090d0503270106080105130215120414070f0306020a0210060f0612140a14 74
    0x1220f640368008440200c10f0700b03850f100c42e900c41d0b10010240c0e4000e08015144c0f48946c0c0c00141801c449030420f44465009040810401030481d0254000305164409040c09604121082402401791402020038903151800700f010b000b08881204d00550380400200403904102d0407190281c0880001d44d071044030002020622000d010003110800f0700c0d19a00c051500b904450004018141d101900010b40b0400424000040081110600179143c00a035152039240419806180c0f203540500c181c00c00009206118001040c0205d824040c1a245801c41d115681c410190380100032a0b881810345601341410b00c0116070300074200c101068001d64170844c1c481c0044001c0c000d81d00c503c0710180d01d014051b00005000c00e481e21a210506044d520550301170319503544075960400c060b0341043d918180d00003001d1481a404000da0790114420709414000c2c00c0c03401c501d8011a04040c031504c018061000900c11000155500c000d04d0100f0020045440d4200401483c00420300481828010307034421010500c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 905591789 1250 905590539 905590589
    0x11030f070501121e022a030403050d081305060f06010e030c18101508151f0503100b0408070801050106020601030c12150524011107031b0f030309 64
    0x10740c0d01c180c54100301c582c2c052410100424805421000d4040407003100480304640b40000c140300311001c1c1041c080c14422094402a5000d452000109644104400c000040020405000c2d600031802c112251b80e03562202c455080801070801021405100200a0580e03d1807410340d010303800c01e80e520400240030708203141e44d410382509603590201e1000c440f5000c034070210600c11382c01107440c11408006070755405400c80f040d0041c964800441c184d0000c00510403c03405500c4030031041100e8031001c4440341c0c1c4405800e030120300d4245081020010014210b141d005004200401194118665499807030454617281d5446002d00340e03555003848c000040e981c0c0300242c014113032a0400e078004c5985150012801e90f982c410b550898010900300000d01c02e2810900c01e203031146800e40c0c02c8140d68000700648070b01a490703800c5118103000b0356600b04c1144c2440012181e0580b03070720119034003080c0940c100d54460300c00542c0c8a8415850a60b03004410564010083c0084444000001441239940007140c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 905593039 1250 905591789 905591803
    0x302071502030916051503133311121501110a0b180607021209041103131101093230030931110c0709091109180a11030f 53
    0x45040301b030030700201d00004820b42400c112039103c0d0b0342d68800701d10040800303075003024540140d910322200600e80c4100101940121594812400501864090001e80d0280300680103808501e4003045d10840800b0b0341d0003544d100381c075034803140112801c0b0000340c5031110130300c002191014881102c1502d80ca40720000002c40340e00418440c0c02821105ca4055a51190340d000307000b00c154001d8440c00f28085c40300c425001940280e4103045083c401461a0905070300c20b11300055110304020010780c04020800b1102a19520300410456000a6204101803101540f81808403194080040703001c0001d5140c111060101100c803008010300d00c1006008129100e0251512168003c094146442c0402580c41040b035000c92281104030014241c0a9a200844032106050b000d1500005000c0d2108801007251400078139290400307000981e500c3e529003d000b11042d05550240740c0100104801c481411040040100e5000441e400c4022504100e01c0010720340d0f085a00900500b280032450fa0030201e01c03d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 905594289 1250 905593039 905593069
    0x717091b030d0212031b0301090f0b010906020705040e281509020609150d05010315060b0301032619090e0717041401020405040f02040503070b070b07030207150203091605 75
    0x3528604d44001100c40840d4001040413195210290840b03c2280010010310301919070040c3c00100e00201c00350309001c461100d805681030248000082081550004590f01550f800392404101d10124201c250720346894103503415004035005980100c4078065050502c01300d40a100d04408102009151b0000c44200510180d004501005100420704240414404180d07040c4c036003038602503210709500c1c11514280c004951418000b031080904240342c0c080c810240215020aa01d55459580e070499000c68900c600e00401c0e00400c212060307154201d0940b1a5030380285031008443c080c0305c0740241150700502407100c222040b41c0200c0c2d60984610f220740540032880b000ca6845c0e41301c9442c1c1c00300c0e01141c0070403140999020400072801d61a42d0040c40203030b10000d4030140c1c030395040600b054248405600b28211b041014004103011806440742603410504c1814016690300c007900f868000500000d00000c074a90000080c40340d0248009030f040b0310082030010206010352a6410001c03080502124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 905595539 1250 905594289 905594293
    0xd3c051b340905071704140127140a08030711101a2b0609121b0b04051218030106140604031b030605070807140906040303080717091b030d02 62
    0x1442140c03030360f82c001c035000012070030003800103c610284803100d10781c00c607001c844003640a40d58140d541005d0140c1d040c1d400c0d000c4540542403640800c01c2000800d40b04002d845e00300140303100d811038541440142c9043c0d4000c2d2441d55030780362001004d09208500700340c807000c501c6180488051189240b01c1c5030b81c442d10203900c1e900e200326120100400c007445440d81007900c155040851085095569400b44a08e204070b2001c9280b103141e0400c1401d81c0040181117051014410010000c202c1c081c0c840b90000b680444034402d02c0e10b690502925280b0481d800750f007280c8001403810101c8080508110060601710004e004241c0c540003218490480d05c6012a0061000c2c4810310004d9841e050345c11065610101c1065401d41e03a88032242903d0307080e101d00c00403035016800c0c4030798154898659806180703442036451901190801192207032080e84005000c100303801c0c000c41c0400c1c0c810700402407001e44c840034400c5c1c2410310019042e162400460a000b1502560000010500340440c40441400740c1e500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 905596789 1250 905595539 905595643
    0x1207120305041505070314090d27050603010315200409020c0109020d0b071d150f09040f061d01140105030405030f0403050d3c051b 58
    0x140903005044050803c40700c440211410041080031403243c140b140c3c00954010404035640345070700494034809004440b9603001901b5403032185070800c01c207510322a400c28501524826110040e404400315070403103580b00c80700200000502402a05040061094000410408010107942035241030010602c141c9030b1000e000400000441d580504408040c0600104074030842da40001c1d140120104202c441030003000a00c00801e6200b500b400942a04401070f000e200304550000e03c0782140110300c007418060001c0d204150114010580b00c4081d0043c10900c03501c04000802c070302800f41d40c041c151410300b1503d80c0042011015120307030304a07150b80412610440341100116031540c0020000d9400f40701c1008040d0341440d00000034001540210003a04100201c0507008103440060703c803551500c01036480d01c911001c500308625003404400c2034122404032140c030055070303079000304c0c1010074456980c421584e694400108200b41103151003100344400c1300001170722512680350b2605514021507450307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 905598039 1250 905596789 905596823
    0xe210306031e0f010f050a05070f1e090b0c0d110304030c0b0313020d121d030c09071209080d0507050f040b0711060301090e0c0a080d0c080c0d050703021207 69
    0x441c00020002c8080d0540380980405900c183c203644003042034080c1c40750380784204898104a441031a800108500d44a0710182044030003d0444c014114280e10741100c400034444414000d02e510700041540081c41521500550302c1c880d2107910300895100071620081d0300f040030000110448080d2030b4000710304a0041c0c00d103000b50308560002800340c0808010190b0700c0c0003681d1501058400d02e0b101e010b8002247d180400001c001202c207019603402040302c10303013453b041d5502103415141210141c41d80b1405980d42c0108a80c003400780c01824500324607061005090002e2100100030070045c2c009c0611040e01d40c00411100e91103690165440c80b14140018041c032009100200720141c02246100b01c0000d40c7c03c00a4107030b034004e0780a27840d0b0315501c0707000458006090000c0c84200c0303030841d000842145080f1074245c442c3c010041440811040500d0754041003901b10a6405100c0150220703144011380142c080c1880d80b250700158050b10569148894030940481103600e245e600010410b0000c0d072603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 905599289 1250 905598039 905598073
    0x1005040b130e07260705011403060f240406031b0801031401060504020a0816090b0d111903090b0f0103110111150702160b030609040b1305010e21030603 67
    0x2520051266015000000130510ba110402d03500c2d0741c0741601c1c9514a01002e800c1c80c0e10b0b1818a50240d8107102c58160008400c003240d01c141c0f40d02c207505881c80350300402d03803a0000f50303030458404c410b8050a24002565440b0000b01d0050001d40e40203881c00c00000e6611940ca440c0005440017a80001d02007800501c0000d801c40312407260400c0d0b00b070011803801d44401c0094166080b6029990000e10808100144c5c0007130086851000880f60a080e200316040070424034581c401c820400d00407903220745c6641e00e60b0881d042110000b846890030400c00549081009003e01005501038485451210108105e100d0390104507048941c412600c2122180c000015203807003120042d200c03902d01400e06200440040450024807a2007194082c20101541c11003140f0482da1641000b081c0c0030060040004035110061110340142d088440a0400d40d21019000040c003102c1c40c0060241d420a0294416000f000a181c0c0341d80c1038040308801c4112407203043d503640703010883c0e80b07a5060303020407081c07032102e044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 905600539 1250 905599289 905599301
    0x2c0906060f01020a150507080c0910030e030904111206090f040605060a1d0115110a08030c0f07080918041e0302211b1c030f0b181005040b13 62
    0x106006413084224a0b44030b886100c5143e1181005498845082209040c2d008035890344c0809101c17900b41c100020040400c101c00210013224060655a001003806040c080080e540c1c18070006009000718103c0300e080e0007154200c0650000b409a101c00421032910f4402920381c40303900c0c80515006282c0c1d6540302c11028010103030155400411402c00801c0d00650511220116041c00e640f620345549002650000002c050446c0c104000c038081b041d04c0030b140d0201d80384460641000390103403642c5404504603001c0c80303141c0600390f204034009100f80400c0030074400781080050031144481c00002c450300180300c040d0100c90040008040ca0701c00002505080d541418140c0288100c4a44500040c009208205850320300b511144c000718141451020f042c107049c5560036594042c00c280c0303200340c0c8103603a44078101d400f0b442816121040944e0f80f0702694081e56044400600d41c08081d940b0300d40c071403501801a00c0c604a414030a02000c2200c0c14580075400307480d00c020700b0060140d6a000c00500c01815 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 905601789 1250 905600539 905600569
    0x40303051e0706090b10082d010f09030f0315180c0e030106120507090c1e14160b060306040302030a0509010e04050c041701050702060c091201062c090606 68
    0x30600060000c03d40f070744181c0303c00328403402c220700c0c0a050a03090205c14280e0365116400c1944031a012030b414140b41500c01580402852a941e402011140400d000d000f6150100303501c145001807001c06c2c142d000c0701d0010f4400396514100004400d5407284a0b0074801030180b103804e40804082d0340c0c0c0b0781d02c0c1944400b110025510b08100c04447c00c000017425100140c1c40450036203020031000b400d1150a20040005001d140703000c1026501a18010b00701a68207a04010100421040c5040240c00b454031818129040e1012541d00c894210008617203907900e070f9003075400007080c50000b09141000600c00307025541540040d41030000d5900300302c900343d1000d08180d0400040003408121621a8050140203513220201140c449040c010710469081c050000604030740c2c1858144082c07603402003a2180c1146140402580d94a5454003241620781c8030740c41c40c2c140b0740c41c1c400005880403441301c1107518180c1d01400188401401031480103010750540c0c1c1d0300fa640c0c10480201c0c0c0907140401140080103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 905603039 1250 905601789 905601847
    0xd090f08240403230a0207053a060f1b0f0c0b071101050f0901050606070f030c061418190302030306060c01110309030304020a2c04110d060906050c04030305 69
    0x8013004c3c4640700c0c1e41814030403081303010702017104091241c0501c20b5102600301516400c0350780c4171003810205da550903024281403440343c5060840c18002c4404a92410715000700051242c0300101050070000c20946582a03190000203902292051081c0c0795480341115540e20301e200540103072035139030182501410200a000b90300910403141c1d2420301459104942c0c2c00304110031490310090003800e45000400c62440b4003801c100b66000a101d60740c4000102e034052a000a24504501e002c90007801c00ca2140804441c0c02002c02c00708994281c3d6800c0c0000110080c1c81d0114104180c040c09070456500040260700140000380c5c40e03081100103003e5440c050800032820301c4500071007410703660041c5d49840d0203400000801040d414440031a100610a003c40c44800c1e43e084030354460591002c04405040401c2100410103001d052145000c04000050088002d4581442c0c400c0082c465200111120f80c20070000480b00408482504e0859402da00c42d145407048820015040169565941e1802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 905604289 1250 905603039 905603057
    0x60702011e020c031212130209012702030411130614130207081303031103031608090c1c030305160c030f090803030a020301080f0a0809011805030d090f08240403 71
    0xa136904103c40b003c0507480442ca50342e61b203065040c880015500500032041000d10074440b02c01a11000c41c080d0444241d1745c00d9800b8206009500760184403540b2078442098004004e000038803181c4203034610b40035001c694003044c1d60720041e400c0c41a07410500c5650100000185041482d08100c0115200f04996100c0186400c1c1c45660342d0070650440820290824541072060040503000180840c681c00756800942c04d501d032280c0255145580500310008000110010030314004c0104821541d61500421084420344248a12040d13590300c03030401c1d00041d04004c08151201070002082c0c003403905643c0c660310020b8050b00c043d00ca002c80c1442503010030011080000e040201400074600480c106080540c0e40d5141107411441c0001560444c10306401c4440584000340c50f8004582402d2000e0a016851840a04c01848916182e070702403078040c000c84124011445c0c4c0f0911600903070b41da1030120310314651100380c190b43c3e660708080c088064a00c802007000044540040b0640e2041c403a00d4401e0603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 905605539 1250 905604289 905604313
    0x303160c08040b12010f0e060d3002010c1803030f0c061b0e0f3304090e010e0a0314030c090619080901020711040902030304050d050c010806060702011e02 68
    0x240c2c1d0320992091070035200101c2d08005421289065030300400d8010618101d66042c211004904080605568801c0c0e03600300401040140c41c100300000b0741d00d410a0100c00d500011051055201c4480765940154a0000c001503074034005c802c01d2014841c2d01820568407400c48c6d5084c1c1d80441140d505805002c0d518451900080712030140200b0500410507200a03413040c01e90242c01c0d05040c1e00c0c2c1510078980001001090303150208000c1130f984030f40003103e19408610302c01c0462095100c40382c4080b01b00c0010301084041441d000b5003141a1424003c004884034807a100d034a031002104018000746000d00c8111080300c07032001645d045039441c0c021602c0c1c410510006030441c2e111014007841c42080350b140e001010b400c81c610382d034803030b5507007000b9490001c00380d840c001403480302105c0038420340e038404001096450820548020306000341c40348484441c20302348540c1d902d0b075802c5d0365800102c25600080709414103200340d8a580760306844581c031868070900e140401c48000f1014204500c03070b041c1c07003480e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 905606789 1250 905605539 905605553
    0xb220902130612020d03030e1e06061e090a0e030a0c022e05091306081507090803040b0c070e070903151e3b010501120c1502071211210303160c 63
    0x5005485279140c0034951038010500360411070000e01040c413500c006000c03610180b9080e540f120822804990b2a1140d65501c1e450900400724100c0d9210380b48008034140e955543c1041600590500840788100b5081d0780c5810306520104d8804c420081e01c440c55003094020380540040c0c0701c0000010032291a08108020404c211036503503002d580d07070f0f501c08120301144840c0ba10143d500501c0070b01d800200c4509009039550340b44290700c103c0e0044040040e1031810000c0c140040c1010300741080302c0880e503043c0b480004ac400d002502003512400e0780140000312050071307480b5180c100f40e03881d0045a041d03000c03400c580c07000300a00080c0c4401010000c4082414591103602150f2221201c5501e5031308082c048001400c42d04140c21200d88880c281d4561004039213001c0c08201110300140044000b244c07001c100301e00340701d87c0d540b016140c070260000140c01c100c41c88840100e440402d40d41d40d1503801100c11001c400610701004001303150070410110f21031054104041a079071140f82000240100e196540c05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 905608039 1250 905606789 905606803
    0x1090605060112050403021e01150b1b0102120a050c1c021b0604020a1721071205091e0a0b190f0c150b220902130612020d03030e 57
    0x88100355100304029007503070801e0080c03c260030703040e03003c010030718242e40e011795950269030485140c01d04036000001d11410942000302c0b0381c000c40b18032041c019035a41c0c0044140d0440414507500308655602c0d0342c00b128051007a030342c03040d0a400f40001151074547e06ca000402002e0001d482020381000303800c5070718150b20000074054071140c100617555941445403502d50b035115141100d6a4000360300340005a074940b01100c3c10381e0000701843d000400032800440c2751950040944030300c04131400016505178100300140071201d01686940b2902101504204e940e842240300b4107134041401d10f19600c078200e58404050380c0007405060131035620b80760301d90102d4542018504100c2900881c9000001c5a0f00c4024032000c8851030929490209140e0748031503e8524482d107001c0602d540e032404019503a01c1310f440f003201e03a0413000c3d080f69012481c04214041c1a0b100030690161581082001d080466803040b04c0442d040701d0102000c0403949d90030044041d440000540030140c0310960003200e21800d000da2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 905609289 1250 905608039 905608043
    0x12090607051603111804080c19050c031c02101526070e070f0806150d0c03060f05011706040207020916030c030c0905042309030a120902060703140c0109 67
    0x402c5082d45586004c00010b0b02100c0f5941c0518070030044059042c110b00d0300d0940160b07204038025200d0038144407644c60907041a88a24068091100d80002e2210200f080e1034210415020745400b50500c06480d000031148118204c0103078020514521b0580b03203684a4102e064011010320070503640c42420458a40c914807400e10b000c405d07403190a05052081110400500201c1420071817840e1404000d0420380d500d24006003404008000501c01d0b81c4c40e41741159403945c00c000c0d95902c50040c0071001005002003403e0300c010034902203020506889003c2102c003141d81c141e44103130f0001030004042002150103440742750042d8003448241c0060f070726580d4207485101950310742040788121400c0207054071440140c010034549030141e10baa02a40c010022400d4030015180450000d1800351555002d050314091580d80c40c28450600020090100003003540780c0880d40d400341915041c08014044510303502c5c0c001d500c00401c200400c0000c2c0510500c5500200d04403109040a00080c42203080d24150744007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 905610539 1250 905609289 905609323
    0x50622110d1d01330b0d0903022e020d11041401120606090e070c050f07140a0b0a0e01120908040302090c030906011815030b150d051209060705 63
    0x2c0d00e40d00100580001540386941e002402807040401610416600052521902d06100b01c0c42c01054100e00c1c2034580200043e1100603030721022229848014407860720101c0050060700486021000f2039440701c4c1000d6008501d2020741698180548020341c41010740051240e154007500900c00032810140c00100000c4400715030300500080010310946014a410350300502c0d03d8018000141e01089050641d015612403122a4440b00d03c00c2d900c410401d0001001d602c600411001090b0380400c850044400b4607503200c5004015008100180c4101d001303445100c0d9042c489490a103210303d039100b00703401060405600b60a158000b4600b55040c1e043e003918840c5001408104504004408070b40c0504459901402c508000815540f07030720f0184110300203480d0f42400002030030001c0d0301040ca150569003008020540d21310b001c030741801040b80d8cc110741140c001241c4c00c036814081c0e0148522903101c005400c80e160700c9902016981c001262082d04400144002c0d0006641040354082c4908007200e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 905611789 1250 905610539 905610551
    0x1120603050109081e16020f130504060f0c09061e2003030103050d030207210306171b010305040b1b0403080703021621150b060a09090f050622110d 65
    0x700c5e001141c1c40c100c0440515420011208441203481c102c01c5200d074100c0d01c0d01d10000c00d200003c0e286403598079824040c545084140000c02040d9400094855161141440b6150303000e80305544070700c2c072845624041100036448519980360752010200a80c0d1a0400c0c20b05984555021403040013000c2c1100c480c0da00c0000140140001008542d03840c503110300c0d0039442c0000390790360300300307011004e15044da44000fa140290080c140079421000290154080e41148026000b802603520341c0c41c0c10910782c118400500704d0703016510034026079109a0308450241c00c07030303114201600040c4c1000b2070035200310380081c003001c0002404a402481c003140264000e28640b0a40c0030b10001804607903000003207005000c20454045a801849403880d00d030006190304400d00c601034480d000e09054801140d116200051901451341c00030421400d440880f842017203074043c51551401242c0050340c540d9404128140000c0020183c176003840504c2c0d8501c1004030b000c8080304800902c40e00301c98000341d15039031962 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 905613039 1250 905611789 905611807
    0xc030b070c110d020a0302060d1b0203070201080f0c03011802070501050a0624120b0409050a1b09140c0703110f0c0f0105210402180405070f0e10050112060305010908 73
    0x8420b10034000760440e100451016160700080821085100003030048001007018510342040358058400801140600a25441144002034aa90102c0022408664210003207202c019613111041c0c455080214403078a585d003404e641411720410408000141d980800011001800a00072240282c401001c003080043c1481c7e4000c0008151603018159044400006e49000e60f000c0d148484024245a0014041120030003260281030000806015803207090221002c009042008400c0c0c00900402c45134055110103444040d5208010b040f6243d00c004404100300044100c01095070314840c1c20300c0f04030056040402800c00030042d212040c45e403c0f211801000d400c000c2c80c134034107a940034a850303480c0c940034484c2e54258000401804201c0340029000030304540b5222008035896400012010403854a86480c1d90f03210814090050fa880421200040c908000310406007d0a202454055410b0a00c001140c11045036031440300d24688070500080031030003e10400801e030f8056500103954009007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 905614289 1250 905613039 905613053
    0x215132d0c170a030302130803040e07030e0f250e0f06030c060c060412020a1b0f0b072001051e0d0513050604030c241b02280c030b070c 60
    0x40c2c1d02552034008109000c0d2605180800d200c8066541803c00503150108100000d00d50f410640009a103848000380c08195400c544040e80d01c0742c50165414003002110340078898170354500d02c8007002c0b5544291080200c01e48441808001d980841952040c0c05654114048221900f41d880c1480c0c1669001409100d05082c070440c8245002561580d2a09628615a503540c1400504c003424040040c204180064828443c01052541100410407084605105401203500c503100351000700d20a074400140c00c0090005480c4861341044100e0f1088002c2c8614085801c41000c0007070401904009154a00c080365071403200407616110704544400b8504c0440c0c0446002410342d8603080d84409900c2c000034400601c0a510640c14a05a10a41858500010f08481000b008501469180088003c11036507500540c2c0aa8112481800c0440040d400782e80310341c4217499050051495064000b494440a08603442c22845098800d203225580d45800c4100c4200340c5040f00000d020b40030003002d1101c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 905615539 1250 905614289 905614313
    0xf060f07360803040605121302030607080f0601020606090a0b030f0106090b01030f111e0d0513050d0314160509100305010f0806060307090b06070b07021c0215132d 72
    0x240c42c0c0118a445d041202c007400368060310419100c0e28a07250002207645c2c0700740a8a1b450140d000c2c2c112096030038175140291401c4c4049681070191082c4000043c41c9620018203180038000142c01d40800c2d03100d04a000d4003904400c40e510ba0144038440d2a044030180921400c001494114400583d000100c800103003074403a10381030503e50074140030192094610315402c480c2807694400c0c41d00d003410342d2011603550380d0040001d1194103d161100f000310700620044082d03102d92154058a441d07210b05042901100c1c00c1381c4000803082600e400044a0080b010074003501a40b00c0d051803414088014000b60707282a010307180750002500d030801041804100e9440c00c0203460300001800d0701c1e141480200340d80c0c034010700c2241043c40d200d17110444507440300000c540d07040e42c00c00c140b0300583c6088840070350758104410070120000d80701c07889900201d101051800e00c004050705518242c0d02c0d22484c002d00404ca0000c1a10b10000c8580001e44540300c0c4030034200020a41d01c415110070b1b2560402c1168019 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 905616789 1250 905615539 905615549
    0x1b0e010614210402180907050a06020d0c030f1101061d250507060209040c0206040213060303080105060304020a0b120118060b0307201213080f060f0736 67
    0x100c2801240030203075a41d40e1440210030400c00c0d40890f42c1d11030001540ca0b03035a04018400c0ca8030b02030f081c480e000303070003090540903141d041c1c580544090b604c0074100ea4440010112400044040182400080c0700f0324000801341c40f0b9261102610880700da8076801c4440f1680401903a001c1e000450380c0300d000031030b03000c0d9201028070740005000e4a240b16172544815110400c0040001c00034942e001c008241d81078451350782000e070080000e00c80c40c61010f0341d20901620160710030b5204011a070103c0c3c500d4015801030ba07501d0754414200da403134501448003d800181040b40c0c00042600003284050620700070340401d2174201c03041c00495240c003002007441d03482c01100d10341c0c0034140b04050101d84604c0b003c484e005040c902d024032800c202030700200740641e00c1c404000c0d580e01801460110508035007002c2e2001c4c0c204030b0113866a1994a28200356502d08021003050f1a0300300e070340003d050103881c000282d845425418500c841441a00b00410003402183c0042e01c900700403032500888000520b0f285001d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 905618039 1250 905616789 905616827
    0x22d1002070f0503060106170703110703030506240d020d0f14040c060f0e0f0102162c040309150201020d060605030109150608150f0607081b0111161b0e0106 69
    0x541047c80082241400c44000c440c94480ba4011a2800b031099010208000605030115250307285850020041d040c1a200ca511403c00c9a02680440050f0003241510030062100c027031070030740ea401c0813202942201e5219003242d45c1d500c407640003121130340c0125a2040ca80b40c1d00c0354400e10b0b00c0d1404403121b00305a040036040208003001c1c0b458054020110303090712103046508a06c04054100101e16260301c0e1034804440e6480c42d480043c104007040c10f0440d000e05144041e5950415a098426454102b101c0c050f0000d06204820060004ca00c2500240c900d076910000d403800d2086203544c004d444032031f81b00c000010750000c01004100440c1c03241c00b9100d801214013940769071802e00002d01240d0041c1800208010440840c0d00954480b40d03914035200f000390045481e8101401c2c00c4500d80c2140040d00c015490740c04003807540c00018420300b0954080e6002d0242400d9403140034107100001c150049034400e01081504203c402212001e40c010101608080340560414400520101d0003601c0c0302402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 905619289 1250 905618039 905618041
    0x1202030c030403201906030614090606070c09050106020705041127031f02031503030720041103090d12090224041e0e010501080103022d1002070f050306 67
    0x280220890b0304a1340c00000001c461000349807490b0b09080c05510b4141d021803030005062a0710826007501e022107005850030443c8070f0f03403030f85110540550450502d40c0542d4020002c2c8007440c04401030b100d29806440140b00183d00c50840a0441d9001c2e003002c400b523842507508020502d040d0083c403441000143c08a8281076540d15840f20303a81d0342c01e0031f0b101c0d000145004c640c50748d1020400d070602581d00f01603042ca00790380d44030b00000950068420a803201140b0180e1783d0703242000000c80381416403041c5231064460406400d011501e02d40125242c0c85910340f9a418164407003000551b001d2030140000d80803240d2041c40140854040ea443c00c0c40e25400c1150100150b40c0d071008501c1784100201c4e0004400102440710802442241c00c40c03254900c4640ca038442c1618600404801d0700d200c00c070140500d903228001556000402d110003503000d0550418903580c94681c201005118080718180d98030140810000703110141c0c5504110010fa0010108001c4100c030003145100034242a0b01503e12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 905620539 1250 905619289 905619307
    0x609111602010e060d1404120504030302070b07050109060f1e0c2102070b100303230304030507151107020a0b030103050a0f0f0c06080a0510050307120c0b040305010207120203 77
    0x1035194400c034041d060144001e0300c035000752651421100900e00d0010200030300c07100c5042c6424000e01c2a2015100c1035000003142c405d0070b0041048500352509034004141a07071400700e04050660044400f00c450303548441d00400002e425015003040d0302810140800c2c0d44108800d125101c900700c002c0c5850603414040400c940c0742d00400c44051000c50a00215050f508121b034000c003038401d0403001001c246040c0100505402e0030400740c002e403031003130b510070910504080011002505440103024a4002080800c0009016000500347d81e88107148600d0305801c0201340c2c0040328014440039400070000035490085151080d003400240150b46421415541907031603250f0b54429a00008107080003800b03d84007817007202002242c0c0b899011a4421010381c031640005d0001a00391100d130001c604004c081103d000e0421403e03010781d000503008041d5145404414100702100382c40076a21104010808110a4001c10007400950300400000d40e80701203501c3c0000e080b0000f4810b41046410510101c2d807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 905621789 1250 905620539 905620567
    0xe0d0f0b15032104090b0103110315120d090e07032a0e0d17031e0a020d1802012c031605030705030a03120209040e0a030305010524073003060911 64
    0x4c143c400240000600c5101c2030016002000c1400c500c004604d4044200054001544d0000700c1ca258140d8900c04401901103c560b550000309000c040865440d03402030103002c585d600c0b200d41c841c841e031801050038000940840c403410303200588800302e07003020000142c080390010032150b47d85105540b2004401d505480c2d54030f424801c007882500c0e0031400804500341d464100c0e903000380c041d00d0041c50f54a905105401070003d5111400c0c13024200d0602c2107030b0000b11650707640000002e806031208145210900f50201d16184204490144524035611b00c0405844c100415505020b0518002c0d8003e81400c08040c580384041d4403480c4680d103e00320743c200086c1d21070224081800035030409600c0d50300100014002c0e00c2d03040d03401009407146031010000d26501d50080ca049410964203202d82c05501400008140301f015409401035004210700c00c0094000d0006060805051410303007840512103440040722119460750000081e11564184040c50300d610522100c1d408940c3e0262074051801c000700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 905623039 1250 905621789 905621797
    0xa1407091a0a14030115030f0612113010020a270902031e15030a14010e03030f0a14010f0308090f040e0a170a0e0d0f0b150321 56
    0x482032a0300400c40c500c0080c0200440040f031a1940b8240c0d0300c940c1c41d00e100007a014201404040040c0c14075408150303180d110310400058819964007507503c10000d8461091000311401616040032104c501045550116420500d0f802044808061104601e050f02c502d842002014861031900c1048460880d40c2c002d0440290794030b8030f403481000030121240489807249103900c005001d9000000700320113031480c81c0c000c010200d50600f4400d00c0e615098881302c10020f003010b541d0b42581c882e60008010802c2c80c003a00015040000000c00c2d581640c1803041d04540050703a04101900e0400300340004640340380212031405020180748080c5624203401c4c0d0a88080d00c1c0320181c0481c100044004c52030300d8101e406811041e003d4403d01107901c0e0414100d03039440340070740140d800f407560720480320814a10000700c43c0c94900035030303035801414090307410444d20580e41034040768904400990900003d2501c408148103800c0c1c1d41442c28071500e07000a042c201420100307030f03448003480804070060225411040e6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 905624289 1250 905623039 905623079
    0xd2301120c0305070603090317220809040612031115040f052505190e0f070234060f0c06020d02040302030f010509070b130506031b030a140709 63
    0x1000a030703041a090108054102408074090820080ba160f0f815800c100d140a103e0750f5401c11403442c141145a41080507102005410340c83c0448004140345041032928450081c5409071410040700005800c45506074004210300c1e040901b610107040c0c0001e0b0a94000081d10050810107031488a801d009010050006100c41140c00c203440920208200021552540c0c0ca0074010f4404226181c14900e811072044504c514801000b14550004046900c021250901d000d04c030242c480700007050500c000185200118071502215000e804821800341480041e080c0760080e21403000080c00441c03450369004030003804103a40800c100030750b11500350b0b00c0701500084010b0720f4220742141d0101030310856101030361510480f5200d8440b40010b501150103062080c080f140034270f0b0342c1c542680840c0981c105480c03802640c03500802407410000001d40d8081c420a03c0f01c0c01d510780030010103600c0c0d0001d031440e50a00d44e60700c40514000c10664010354108940d8145041c400e0326207410510050074a00e10303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 905625539 1250 905624289 905624309
    0x120305040504180203012301060e0f040e030f070c03050c040506011b1415151519090914040b070318060914011d061005090a0507170a020d2301 63
    0x1001c0703da607441c3c02d9003084180d005009010500070025002041e488814210f0b20141e088000050140d00a140c03290420070040c3c500f00034081044100401032010b0b25a070040c50104020000d6000c4401c0d0050451522406002e8010342c1076040103850b2038828610940103c0c03420080c400642c0c0c0240c07058041c403800240010000f500c600e0440e200b0034500800d45010f118684980440d03910400c041403050f514201800084400c4008128503203540d0f46e08920805001c110b540c6d04040c6e40c10101c00000b209050001c442c550704d00c1c081c02124041000602410500814007040210400c9001e4000c206890180524803000d017150004500060005003010780e81d034488000c011a0180050000b0298030013044000e40071903030744c100182c0040c81c00c000c5005202c000b88941d01b451020105850002c4c0002c4010341e90b0002980080a0103890a03050011500030715010010b145222803003031a000340003580f540040300c4800700b625040e558080300042503c04c0c1e0018145002603c5044601d003180c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 905626789 1250 905625539 905625551
    0x17071a2703010605030d0203210103030c03120b0607060c1b08030c072405010f080312010b0f09041b02010c05030906040b180f0a0308010b03101707092301120305040504 74
    0x1001a00420603a880543c05021b444118002143c0100240c0f9070344040c502c0342d480c4d411802148030301e210024000200400c1e50954454007103440755542e1541c11490307280001d4030805141c0000e000d40c0040a04a0f105e40d10340e111034048070782c01407000c210706681441c08582a1504d40d505d42c15400002c2c6400d800c10350200e000c01c1400800c602c0e0b10f44000000c00522801240400920080e1409004030404081c020500289100000003150805140c0700e41d100000d90074104800c100e0b41c804280080c0e41f110910507169950395501c0340c42c4100c0c000b6044207039140c5101001a0944500315406000c0c09018000c1003034000c8040f940c81d600c01c0d4440c03c50582c1d691101c4c0092130000343c001c04c900c41c0f84203110302c400700001d00040c0035041d103000340c840035650780c1d80741d85250007440102c078403203840d0400030805c00c040c1030500c0000000090319801e0f510704036244c00140741100c00ca80c0e21242002c104144800300b0198910000e4007402906400720b16800c2c4076100a081c070720030717803150900481c1c0c1c6074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 905628039 1250 905626789 905626867
    0x1e03150b040f020c07240318150e060601020a1a1f0e0129090409050316030201021806190e040617061e011d04060617071a 54
    0x152205600c0000100108000602400715100030741003a0f010700c5091191710750110313680001c60781d0070801c2418840c3ca412502050081100900000c1c092201d00b40022000880029480c03060130054100c100170000c2da00e002c20506a1401c103001d0140d40c155080640c910002c0b4107500c000d1588810200402038068a941d2240d5182195480821b2000401e0140218000e051041060704071948001c09080e00c1e4004059178420910100721121495070401c5000820306098110b0480d10b40104207513401c01400100c82c1c045060070440490050f54006011214170b1155004000c00d0034003501c007079042c05516484010703004401c1d0109803e00941c607000b24210354aa07003000010b81141000114801c0d241e404440d42e9000030754154481b0904011140041c58150781100d04841c2401a8030030a0501d01d69141c507a148040d001307440343c41d250b01e0040344242190903036925004000c001801c2d041c0c81c0401d002d45800e4180740c02031004004100305007400e0b080a41803400070440c0259403100035000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 905629289 1250 905628039 905628041
    0x1e12030c060c0c0d03020301051806180a020d05180706120b1309020108060f060f0d1524020109050607050a0e03060c0d0e010b03030f0703200a06061e0315 68
    0x11120300000d1003407004102003449041e020341650302006040318001e840000050341a40024007a40b038025100c03036409401100c04003d12a00f00c100a40014520001c2070100c01c803241044505104103500061054000156481125031000f0712307081e02c850110780030344180e4030b8441364440d171000c0000200d01c00d010301049620107000350750002c20240c0302030740e00302400000d4030742c0d180d050780400d4140c800079030141410080a0386015006005c5468000741c030074a00903d4004081303103c81159980c400705c102c0c507240a10b010152070010144195540219801e41910803180828801c42e4140074082c2c0001e0800185a500321505081168450060002c2203d0000f251001075038544594418001b200d0f410100030400394001250030311990f1032201c04682a100c91156158140d84100007620105059a000e059020302c41d147c203c0d903030121040e84d500203000b6841c034030466801c4181141d08101d100d10a0f600141854005000d0094040704942e048038814840905881c110340311802000540f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 905630539 1250 905629289 905629297
    0x20f03070206030619091a0609131a04020f19050a05031611060a0509010f0e03040504020711030a08030108010b010806011e1e0c1109370f050a0b1e1203 67
    0x803004003400a55542d0120303038054507102031180200c43c104200340000d070520000712200d41030050b04074ac1d8003030314000c007520083c06c2024200c4d490a15042e088806c680d1980010800ca8501780d40050304c03180c0808010f041c0c0804d1310601800e0100400c030002d140e079088802d50b0760102c0da078225981203071000355090354003800c12960520f45008850030015140a1503000038050002a0000c2140e060b08140351404c46110030088a02544140410001807a15800400880b4815032030300800591200101e450007a40150864250718007000501c80404248150241c655003441e03d1052070400d403002070500325401e100ca4541a12000c0541515030060300c030300101c010354458404100b500071304001c00c40b00c018007080728034021050002c1e43d1440e0400030b43e40512006a0060074010a0b4242d036001c5840c40080d014914020081c4400040500c4c41868088444060301081c10719102007503100f183c0048480034420400940e012120030801c480d0b0359507144054a0402d00c40c211440400e00d5130003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 905631789 1250 905630539 905630569
    0x6021c05040807060606020c0109141504080607260610020f03041d09010603210c05070603050124050f1c0509070e0a06141c050a03030b0a06020f030702060306 70
    0x4100030601c401c0100e000001c1290600604003001030340d440d0780c022601c403000702800c2e500007a03400800380300c0c1102c41e0a0340c1e03105d6130004105800703405045480ca19250000e92122007950056001c002c0103a030440d413600e1903100000c2c84c003072101000c00714006034035030f025000900800403c0d460006140c0204020a080c0360b0080440b5201c03a0b44210b0b02480c202c40050403402c030801c042c04242c001c07030b050241e075042c0c0b82d10402c22103125a1a480d441141c48801040b2420041c2079a43c0c3c3c00030543c144910340c06000c2c15680840c0755030400500304d680b0010803943c07a02c662064102110f1b00e035440b009540d407860110301c08540c1e0744041c903101a00d68440400b815040d6140100f48041074000180da0021244084100c102651b21a440981155851310a87d0b150445050703000e002450401c400001d038491115501c08100e44544a01d4501500c99100310086075881c02900614a4242040310040c55188000d00904812061180d103034001d003140240103031000b0000c2005540c5101616903104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 905633039 1250 905631789 905631791
    0x1f0b031e28120e0d2904080a0e0a090e010218061204030806040e010e030a021501030c14010507241a0a0e13151401061d0d03030204080102042303030403020d06021c 72
    0x882a082c52130711a000a00d03858024110b170005402e65801c21a25240b00d945c21500031400c00c0c0c401541629240d02d8540e8140d4462904000032403490040d215503940f204000c400140c481c04501c64020020301d120401903c100001e0000740308030456034944550280e4540750062907515100040b9000d0010918440103d508098006210f580c1c000003500c0c1c00c060301c4e82124a409141010802d04840030f0102809044000c0c1c03062020030301c6002100c180b103106140403440c0100e40d40350005030403806222001500b4141c4501282c0440d540030f078814002241d0103800d0414a4400000d021116a00c81e03100d00d0394030380c000200000420014202d04540090302d0180c04031246504100030200c054900b20a81003400000c103102d885002c411100c00140401e038543c02184c20104030132003001883c120101a000c020115500c00203002400040021280703040940c10140c0000f91415802d40c072032030080d80180410000340c0d13200880088150b0700003100583d5140064403450a008840507110041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 905634289 1250 905633039 905633059
    0x1210b06040807060804110a08030403030e030a06020c01090c060f051c06050d0b010e0c12011707080f0c011101020c03041203140703091701060501021f0b031e28120e 73
    0x1075086100070b81b05520580400501040700030401100310f1540c010706082760301c240300a00011340070382e404c800602401000c840713000300e00790381e1641642c0c0440e20201780b07651075810701e004224190b8034050241ca230900b04903003c44100800203055003c2e00304d00000040d02d286400080210690046000c2d10300545484481f48850801c1ca543d08000c0c418070007000211070000740c40002042c203480c92407000f80381d5203229034645a410000087c0841d02501740d40100c1c2000075005404100303509950919001404041d4100030026080b041c1840820101e03034010482a02c0c2054044125000e03548106140c80f00001ca500702292103001d019550001e601c1c0010f01c81c5d00b80b64005104004840c0007413030300d48072041707601555800d03101c0902c40c0c140540e00000c0c00e0b40d688024105603c1c801003411400150403840032000903e01a01004010000f080c02001c2e003201c1c0d02d09210486118038001013489655040c16000007031100c8240c80a0101c00081e00030404041c480c1070360602c03a4800400340460 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 905635539 1250 905634289 905634299
    0x606090d11060d1401080708030f0307030b1807030c0e24070b0702070504060503010b13050c0d0603140c1507230f010e0d09230a050d060b03010b01210b06040807 71
    0x1d00c6000c10000c2600c4c644400003488120020313a800980c0c0c00b00c0301441c1019140c040313064040d0000343c0368030141900d500c00424a92541004201420040340c4800c0846c286032a000d821250314513051020860102c03c0e05101d5107030700150b00302042c100580c5812151007500e0b901f409001d0a03000811101050040c0078400e98001181003e07100b01b207a04001035540d41c020103080312142c030280b42e0070075400c125602d0729000681c4600c3e80009100e207600d1410070400605401c071403560704219490031a911113a002c0c52004c0100c00034141080d102110380741e07144201d041283c014410002d103003544454071040d444101c00046010768602c80c08035030f002c0310100f18541c040c01c50105941c00078070500c05003685c032030321038031402c4112080d1030313042d08000800000b402c5145002d020600e41040e410200060140c0b5070f035011034585409a08006001c0c83c40724201401d65100f009803504004411071001105668648014154084510300281c0d614820000c40c0081c01568000c1656015810f40003031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 905636789 1250 905635539 905635541
    0x1a0402072319030c1a0919030e060d02130b0403080d1e06240e0f040e0703050a0f06060b03041104090c050a0906060207150f08090102091e010201140606090d11060d 72
    0xc4018400c491098030066254420410303243c007210080d0300343d8405583c40d141401e50344890311040b4042d241803909d0303c06e00c3c1e01040c0c0c19800111900c440a6001402e0f40c02410b4400d030490240c40e040303e00da07280c01d1650700c522980b40210444042400d90390720540a110074002a0850042c0307a041050000c01e941d88180d0040d84904049000803490f9041c0d01a51140f148211222040e40145003503600341c6100305210080164110280c02807085110110208608018a00b04180720389480e818032800b40c5054401d45a255020681300c4e00305100303000010f4a1102071590075982910000341c20340981c244170030314901c4e590060750032071044070b03001c19450034942200094454503021155215030b1106030040052040800000040304011000301d41482100f50039080f1201c01c0000d8200122030300010101c08503a25142d0341d58503040c110304083d58080c0910600c0c8414107003802c0316450034802103051071243e114488d21408500114100300300d1200d28154040d50007414141d102c04d80240034038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 905638039 1250 905636789 905636807
    0x207020a120318150f0c14030306030d0903050d081e0403050309150103020604030210050c01110904050f04020a170a0611090a0f120b1003050f011a040207231903 71
    0x50006180d0081e00c00b0443d04610700f0100300c44100f07a0446041000643c11950700d6003852000c0200b140c0605580c0100388003a1100340c840310710f00c0281d40c4d641810f4040601c1e05011071814018000981c0042000c2a0041a10fa03c03001c0181440c214650350721140c4403680090940d00e1079803c0700038003403100745039000010314450300c0104100c40c02711040c003240c23641840e401d100096204a0400080c4014201078442d809101c0781c50810230709155048002c6400c1d41c8403207038000754410011a400075a86410701072035030045943d40b400e00d12414650089128040c0c170740584000241080140c00f01c1010400501c41075907040082084001d502e140411515031204001c14030a8048400100c1c200b15544844002c6801c01e4038181581642d5036103800c1203200080c00c4041c20f2a1045002000c94410b11000200c81f038031000018010200c1514108000ca200c650315006034414021303c40000c914585c0a4401090415400b6822003014101454104a405100c0070301c404441d8450070560030483e81e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 905639289 1250 905638039 905638043
    0x70b03040c21020901080a080f0d0b090f0420011d030c0d0b0f011d220210050705010f1506030b031905100f090c03111f051b07270207020a12 62
    0x7441c42640d0f20b1b10550340d10a001c0e640070f8141c3c00304210a27600f0000610052256803003100303010032001d5111000401194040302c45c4803001911400b04000c00480c1c80d0305552800381702c0080d031a0095141b0009214101d510504403400030a03000054295804102610300c20310010100795400500e890100b03031441003503500b41004440c0703030000f0a11201c242c2c0c102c0c222506c1c81d040e0f541903039606088507829002e1102508180c00c2c0c0358404c0700160312045d100700340b0080c031074a400355110041d1030210708440c2151038201c089442d1501035007658508202ca0400c8404a01e80443c180701c1040019082a11100c083d09074036200c9035080c0100480030a50b4034031031070041d20820403041100c000d0003d9502d403e41c000c00b951003e41042c4000f401e1409080e4480c2c50162507040c2540003000c030100035400031280200410b80100320032681002c9061510034200346071019042c1c03035161924840389000710f61220070a82400b000709510392038182d03059075000398005250100c1250344001c100c2d60310000b1401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 905640539 1250 905639289 905639299
    0xf04080f0303041205160611031503010608030912150412170105011b0521031803070c061b060f060608010e060d1101050d09060c0e12070b03040c2102 66
    0x31403400354400300035030384201d800c41441c203818007642c5001c030f4040d40000c00011440c1d04000c0984042101480788110000c0c904154075030304c0c00c203445807800c00002800f8440c13190707041c80802c0c05500000300584071200d10543d0401910b400c03008213a41045580b820f01c441c5216140d04100600c8030300000f0205041e01c0c0c4e1a03144400c45003004407031044a0901405001c80e41d080049080b201d01c404640d1101400389040c0ca0b40c845a000790360440034130000c810040c1c10b01c04800c1c0550706180b09401f0003221001c800451401c140c135078480740305070410b100c0c4c0000d01a4422000d0004101202c42d146c125030300c42e400304890152402508000d03e101e0068800082800c000800d41d600704108132805090000d02407420603134141d4030911010994640903041010074004914051668041c080b0902d00c2402c0110740002400030007450002c10b1141188213030098001d103c404440400c0703040c16210303051070865503075582c1d041c008024200c5a10124003248910003640320241d050545c8140a4400c0b00c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 905641789 1250 905640539 905640553
    0x60c09040c0801080a03050d2c060a0605010c06180c1e0e0103230c040617010506040203100e090c090703050709090b01090501260405060a0f05071b020a0b0f0408 71
    0x1c02214005000d0060b0403441d4480104100401e01602c080d02218420031008a103c404903040324909000902c90001c0a00c40d42e94100031900042c002c1d10361002c1c05200401449162030b0009008440d03055015241c0c6556200c44041041c1d1070010401a6400c00d050320500c0d0350300c40c000e010b0072000501d03d00d0100d02d41080071034050400c608660407650031030903410522000d01c00c890218001c0702848902d520651000d01c0e803d44440c010b4400600311390800d2500040e20300022400d45900500c028400c51040003040480640e282c180029142800100d00c0d050381d5081206280c102691221039103c3c820100704980c65902d82c03c2107120704041c3c1d858004a1703649800c2e00041e52000100903002c246908001c0c0040c0d4418030411808108146003030701c0c0c1d1002e10805940000302a03c0949840d081101081902e900c14014000780300e4039140c040202e46000000108001070507155008203510361504071003595904000c4601030308000f01c24035a10100c0f10064840c036070242c4501c00c040d011b044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 905643039 1250 905641789 905641811
    0x2040518060f0105130c0e091003020a05190b1e0f0415110d030f110a0f022e0222060305070207050316060507030207030503040f09110316030509070305060c0904 71
    0x10020703040b164080c10700b503050b001c40580d0b10042c10031b002c404002c11109140038610741d0380741488540101100303811b0400e0142980144443ca10040d08035a01802092050b07010b10551628003008580c403d140d0740e40c540803c001442150304554041c0c0c10300010120721060980300c0240100212495080f5524540b501154140d516221842c070900482d0002003051400c54025040301c03036200d5031030100203801403000c54541ca0790340203480300d0000600c0c46060122040d40402610396140c00d000c05145449007a100290b0300320000781c0a0014050700842c074802400d00d00321400c1c08442c81404808034098850100500508c1c0854150380144140301c000140d50801190000810008507407058109081c10f42c2525a0b13400301808400318800c4041c000089034051020348094014036000300420380c54a100c0c1000d0380c108224503032070580d0400c244080d502d483e48203401044400e040c040741070382d1401301450902d25141d1000d0000c0c091441008610306d51900100740c040300440d8100408200d02c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 905644289 1250 905643039 905643061
    0x15090105011d04020a030b09010b0a0906050f19050403210914060904180b040c0608010501090501021b06130f0e09030406020618120a0e28050d020d0204051806 70
    0x2c0c0d107681c01002850180801500302500104184840c03420b001c5002903582c00820300d140f070260301c854086c032000b103009080154041801c81c02000350789000c90034400b40203800344462250322245040300411096010f01d10317000300151002960842003540c0f240d000c03488124040e4a50769084000250140300c049440100e84440318000c05014000509180a16060000500440c4030345003030900c04a0304280002c0b115480725201d83e02c1100496070603450148050110f505c180c0095040c000540b03024810751341e00183e140303c07600c250441ca8490ba0207420109103144558512503400c2603d60001080480000c5a01e1084901240c0814000e83e640008a0303100e02584c014880140c1180001c284079014109511206010103c1521100d8180e0b41c80ca402c10303441150300300d0116026a020062a02e8444121603504816000010035404445142900b103841070185038450001c080e8840103540ba206e1507643d045e0703400351040009080000700340d55048050f010842c114800c15002844540034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 905645539 1250 905644289 905644307
    0x121104080c090a1107200d080a0206090607081906180b0f150a050307021203010306051f0f060f140a08010302150910030507050c0a032f06060d020a030b1509010501 72
    0x40c13441c040341400016036502c00b40c0d40c0c02c542d006890b00c540e001446200e42c3c6000e55008154801c41e54681d0720078040c44040e0400c4001440072169421903410001e4080d08075410b40e62044610109496444150303840500030489a08980390340038100d05055004213140e4005840481c045698070030000d071f4041000035400d44100514001103041c0250360945000e900a15000f16460051300c080c004030707c044070b419400903441a5000e42d00c5506101e1203154104840d60001840482601680d08101c28040414030700e00c1410104541c000e800054bd0b40308a440c114400e4050398095901e021141c0c0050040c0c00a000a034456482800604402c150901c00c031000e03548082c10682040b01480c02c140c0040000808440600c1803c014030072106005104500d00b481c0700b601d403541401811304411b01030845408680700e042c405010450a542c03c0000ca2903480311085032132041e60712641c400f040645102d54402070180711120240b118268998002c0315050809440c06500747eaa2040110780c4016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 905646789 1250 905645539 905645561
    0x3021e0319240e0d11031b030403020405010806070906230403060515101e031b12050702030a02120a110f01050610260612120706061a0406121104080c090a 68
    0x1300800004403003600410f556481503281c00c06581c2010340511201c448107074010b080403069000000c0c24421450700e171007030781e01602070a0014415440d03c07800140504959028920610120042180b28200d0220b00c95504001d2641001d403a035603070b45070010103003101351400f522800c05402501081c1c10b140041e00710024107130b503d000008a01400c007003000c0720f201c20390394205900c6849651400006081c0b0824442941d85d69450001c072220b02ca02c100c0b0005071a180441d003040107007000b8198000382d88100450101412542c03801030300e000f0f03181c0d0309030101c0c03501030b60040a4070255032140c1944160321410007914800070205140341304036401201100b000100c0b42980e03441140c0d03c40c422010300d6206801500700a03101d2003a1409a26154501032810099980080c04908119107801440000c048180b4644400c92541d181c00f03003180524010081000705010148410240540041840303000d004031481c0c4d55a19200344607180c10503c00c58500420910300804c0558421340700d0041b100e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 905648039 1250 905646789 905646793
    0xa0906061a030a05010605120411042c0d09080c06090d02210c060a08010e181b0406080106051c0c03020d23070b1602030c060d060f090603021e0319240e 67
    0x227912036840360801004102015042540c59030442c105090884a04607900203890200c28900e101008180c134220b001006030b810401c3c2c0d410104418000010a40020001210015220303c00b040114400c0700d40d0400196000098150512005d1304084005503251076810940301c15032a200b0500c60207204283d46840012140d0004000c8034920810b46600000350408403a4050150801585042c00c080510115280388900c00b031001d20742403050900030001400280440744c5060000b4513590300319460603c2460072500440304004500110001440c0d00500c00e1200709000d041c0080740d9104003220311280001e81c41d081d14542e000040000450f803089084914140742c50740c0110031141e0300d0a0803a01340c49482042e100c20380c0d1707100240c500b008810b000000d9051518035a0000c1c00196403105109501d070200c1440917071514031021411404001c46c0540040056000c203191421760603101c000e1120a914840401100710002d00c3e24801038a801001204503024601c03c8a9503140c100b0815 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 905649289 1250 905648039 905648041
    0xf010212010312020f0d03050910090c030f1b151b020306040312060b0d090c061e0503100b0a030c0216080606090403111b0a0b0a05030a0906061a030a0501060512 71
    0x7088007600c4060382e00d00384103480c2e103054100c94440c80d005443c035402c408223842d6010003203a1102008042c80e1144011002d002e1034085868043c11081ea42c00090020b90380e0f00400006c0c00b02c0d000406070003c407202c4681100c03d0703580c0c070000c4507050f40c0060040065154002048541491070215480907001800307804251100da5007566200c8001c112a6180c84d2210b600044a121080c0035044080f071000f004103e00b0030a00c1d001075840c06a07003050f02400005a104600000e920040d051a1903141c184560b0b6070b1038891030030b042a001135001c0c140702c000000d0380e95000b0ba4542c00041c200c50702c58003203c0d5559038210a0103c0482a406603a03a170760701c040006155864542022904540241001c005c0641c804a44074105210b0002d4083c0112aa440c0c22041e824400d05080003080c0100809040581f005401031045c84060f185c8040184c84018103014488154001d400600551480308015407400307803101540d42088402850851820000084a5024904076401103001010718021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 905650539 1250 905649289 905649293
    0x5061302031e0c120708060f09030f0d0603020a090f0501150f05090f030601150f020c0a030809031213050415082d1e0c011107090903051e0405030f0102120103 70
    0x6408424240e00b000e9100b1a60500229200c0e03501c6410b541010101424241d030802c15114a854405014600c00900c013004011450102205695024000300ca00c81e950300203030504000503011540004e9800340b481d5000062000309075014019040002c801481140e0b40c80e64a10f4171050300241c10b4020030340315201105814800c0000b441907120040c8400003141071070300821700c0c06100343c1042c068090790700311803070000742c020381c0e948003606145c4018401c0118035804200d0581c03042c880100051004144400c05a40900007c40d0115132130900a49500c55045507003080310380c0d4428203006d04d01e8242d40e400d500d0b010101c00c406641d82c0b203008000c08500340000c1603110450740d0180e101006124800fa59009003070080e2450700c060807a600c0d100c542007800700b80c18440e80c019a42c3c144095068001181a00400c4640807203021000000300800d06040642d802d200390b9220100c51402c102082100e001d0120240094a00550481d9400550840d50134200d02c0f40003002340b42003482100402c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 905651789 1250 905650539 905650573
    0x703140a09060e0109084512152d0417120c3a020a03020405040608150601170609060a030602070b0a1803091a070218040506130203 58
    0xca01841a00700040c0310203c41c540e02e085032840b400440c0c0c040f0001171041c404034461180300f4180e4031211040442c0ca98031003000e5284805c0c160795050714046800300c82d84a580c41400c00000300c0131391000c0e600700c1401c6820110503880206c0720008004907400c40044d520211101d05d209000b020501c035425070f1101d8980400085804501c8100c0007420085441c00f00000c21085000d0800d01007595180c406d10503600b030820482050b034030b1240c00c0e248079100609092507254440d12150740b5005039143c0d5400d404502174401c41d041240c1140c10180c000506203400900c02d4001c3c0c05041c248032854031018011a1001c11050150f14004628070208090f850b0001c0c02c0c940109008100f00005c59882da9a281a45c00c8500f055502c01c42c0e860405c110309009000b501c19520310740c8160f901140d403580d0301401201c6d25000e5400303546e801d240d013880c0301500d000c1241e01701600145a2185a00c14660401c1060030490b0201d440d40106c8000ca0340d07411107444020b104607402005401c000801d072400c1c003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 905653039 1250 905651789 905651801
    0x7080106090b04031a220f02270402131b0e0307060206161404090908071703090d0c0204060e18010b060403030e01051c0f0b1807090501110f061008060703140a 70
    0xe40b0b00080402c2040400006c00c0b00038009105d084400402c0765240100710b0301d0050401e20610700c0303502d2100d64080b000c00f20350407030f0300ca40e045034040e00c100c200341d05a400400609084940800c10203482c4403805410004180b10b2410403000c407510325032070343c000305d03110081035840e04100c54030030560004c440c0c0100900c180e000234540c40c00d820195a841c0040954200c104103a1b4044c00024900d01841080c150a8105070102248546035003443e030401e03a80c0c5c003059102c89007001003c0d1480300031583ea1342c106000504032001195920700704480b035134a10f0651700342c56508540c030306a40020a42042c0b4240c800300d0390142c0b108032003480e054004ad40c00768820540343d01c2c0525000c000c0f0000b84401d201d401030121034000c000811403178280030312506504407404c40150f880880d00300060180d114820001fa60002e1801c00d201d40303070100f21a85410506601621940513584c108090780c5002658107003200c1c408011550513442e070a60541c100c4c0e000d6109074071940a40c0b40040d4000075240c12032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 905654289 1250 905653039 905653051
    0x20f240c0a0503041818030f0c15020304030f090f05100507140d09090b0405010509160c0807051018052a13060501030605010503100608040311010507080106090b04031a 74
    0x900d01000c1c00395200c504641c400d4100f21621100c8903d100058640382c0718050b0f00311136070718200ea0f2500c1d00e41c0300039001280601c0090100400303100280c0230800d0f04410500c00d50b000940544d140e091a18000d402c2140501000b40068a115000614900e00b40a400100d4501504e440d6003c090541c00311503e03030004006554a00d0014604800701d17000704110b40320032415980d440642410b00304540f09640d8030750340701c9100700e05203001030041d580d0700c0030b00ca0380002444040c0d0303c508041100507911042c0e403141c00341a14002060800601c1000301c1c0c40c01030400d5101013000481000525000803d4002034081c0266104619803200382100844d0450102d01c007502150081102c0000542003003080d1900401d41070701d40104025550f054003400d03010301424240039040d40b800000303081540c000740c130502c030800c69400003090900d800307481802d0b5600301d51002803103185040c580103000c5079002c1c452100080d80341200000d608081006981c140c0758000c00804140342d5806900b122a407001e080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 905655539 1250 905654289 905654293
    0x403151a0901061e110f10050114090a0c020708030a0e1825090b0c0102070606060c080706020d0b090c07020a06080c0a21052502011b03051504060909020f240c 70
    0x505c0c0044c0800c000150044400800811581d07003404e200310300755039040c3d0110b00b100c0134640350f4101702d9440c111110f5100168440003e4005d00440d000c910300341c10b95000a007603000018841d154641e0108886050800c1916404e40300090b00d0180404800110340945410388500881a007142c05c0c0c55103031b20b111005140203015142c44642402c09075001681800c0035a42c0010002d04001c00c0e07024540007400e03141071030b42d4112466143d000581c410500c000307000950001e24600295003a500c00e510007840a811102c0384d15040c240c41007141e0111000b0391140216400001c2c199201d68140f603c201080103c0d5400e00d020703180140c80765800e551000b03070303042c5002e810000864400c0c480c2c1d038451107a03074000044080442a00040d24686028110216410300314409002004500b40c00050300303803858000707030598030410000705008850090551050400c9400903410002ea00014401402210401c106000401c200410114032040c0300101c042c81c803145c1d5580d107500c82d025046140740101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 905656789 1250 905655539 905655557
    0x6060403150f06090b01090e0f0610030f020412140c0f0607030516060204151e0806010c0c08061b12070c050307080313030905100e0609060403151a0901061e 69
    0x2070610b00f80c4076141c0264558541c2c17040000d00c0c641e8401652402088000070042c042e041c890b1000505040c014003090144046150303c546c8103209900a01700080365507800c54841d0380303900c0c299946200b13008054a452007410500854018003103022504800e0080064030521130040c103120064000200c2070f02442401d11007811040c03605241c288101d880ba40005a540f82081d0000f800e185040e4140410071032140d0080d1f1202034030506410041e02642000d03c3d40b5039071000101e90311624150000d09021504800007008a0000340590003580c1445001000d81126a803030400d5004401d4010701000240e00461841c03409603851744104d500880640740f811350643c5507082d0a9206a07040650340c55803118000a040d80088041c020304400c031005100750741403c200800801484100c0780c0300d6440000d90320b15958403001218020756000a01051310040b040b55807004081c03a4000080044401104031118585014240d043c2c075140d8549007131603000c5222600c181280c0500003c24014541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 905658039 1250 905656789 905656811
    0x212010212010b0405100f0210020d1d0f0601050d0302070e041e0b0109060501030207020f090c0c0a0302030903010b040b03100c0e0618030c030631080a050c150606040315 75
    0x540d4003902043d001ca40d911031818040c080d00c46981402c81c400c211921840d00ca10a60214841140004940c4050703151011300f0340d01c0c001070503000c00c1c3c1e41074000d00440500100d0404556508071401c00740030750325541c0c0d0322014020f42002c0d2080041c01a000300d5001c1c42912940302c410b542041c010b0701100100c80d9589040c40d40012000020384101502400402c440280b901910010344421b203015402c01007290301040c00211301a10442c40b0707003800c00010700b041c841743c1e040c1ca46600f203003c12540c4803030490501a40700d82c802c040041c040d50030030400290700d0400780190745a0b280003400034028940e981c14100010301c58008682c041000309020350305a6520180035100003080d2111400340052002d0801d407800011715041402504050100a01c0030307041d5464490b1410081000d28052a2412090380003804032080140f0001c4045a885825580302d0043c0409c03032203000450310f94802d001078140317044500311082035103d84c08010030b00019881d11203a9507030088021001c901c004600c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 905659289 1250 905658039 905658067
    0xb04051221180102010b130b030f1603021c08120a021c020d05070c081c0b04021b0d0504141c0f05010b1908060a0e0a0c061e02031602120102 62
    0x5039007107600a0501065807201042464480e59035000c0900007049242119000309407100501e030001c0036141e9442110101c50384051000c07004401c0000262078140f00000107940032166580000e074020754902e0b80d080d030f000c1d5000382444c6255410a02c028180f0024400d00520080003c150700d603641c3d024801020100704948402c850101c070404050b807145094480042202c200a1014081200901da00c00100d40d48000b102c901070340c07141502140c4169101c0794409400c1200d101a003140c0300103110400c80d408011903101c0355662009032126600303585c004585a010b140160303502440510062400d52520b140f40030701e1200a1060b41c5000032007a12615030303510042c3c005807082c1c0d4460529415901d80304660503029660385c000314a031542401c1c4441c1e690b1800a04c0c9039501075940f0b50410444c60200000c1a40c2644944174000b056211000140b64240300c9043d1805c08a04080c2000c1580c004000d48450010f0a40f40700c80c044010703020841c44810114081c00f0310355081001c00c100744c0007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 905660539 1250 905659289 905659333
    0x6011707050d050c03070e100203040b030103060207060b01020a0b0a090f14161d040204051302100201060e061c0b190609091a0403121e0c1709070b040512 68
    0x195841c1d95484004076006042950001012003100b032a007002002001500085a407075100e0003580d03050100d003c0c3e11000da00d503110300c1d0071030044220301000000070000b140d001012101e20680d0180301101840c1c1c01644d40d604820320081c909810040043c2040fa07140c0c0c0812040380c012522074403428100d4585640c1c404c09400c2e8188a83c10514008107100041c00f0b004000304480c92440079400148004100803c10160000707200d16103c3c0301264010718420380b500491600140035604142d90801d01a00a02a910464020340000000101d0b580340c0038004040c1c94285002c501220350b210307510b6655061008022100c10318581001017111f110301d20850700038083ca60000900c001040c1040c6014204c0c41c4803032401c06081074208400a90f0220007001410403500c00030078102c0c40350420204040005d640550344514014049900716408800c41c1c3c8039050012000a09445a4a180c0c2d110070040c020140d800100700820401d43c00d14008802070f6a8905003039405641d000b41510a00821b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 905661789 1250 905660539 905660551
    0xa0503040203010c050c210408010e0304030c05010512010312351027061a04060e0405160f0507050607020c0117060306040809040b0a062303040203030d05060117 71
    0x4008410001142001d00c40c4804040540c2460390825a0a201c2203a0743c0340415400c07207610307050301842111140d41708152009000840000d0050036602242140c0d0307500640310541e038205c024500003880d5400341c01119030707082c096840781000380c0c210740340c0d4000c0000700f21600d002c1003020391100045401d104d06111240c0300101d540c2c4141001204810120100a0314020b8100e600960130450003040d5080400001c1001c1d0b081c803c0319004c9000b100c002c0046a102e0001d002030048200042040440148156005034640c01000b0b142001444112a8202c07030b6540365186c0d50301a58000c0340110400304034407690341b80040ca000d4a07603036060f04107401030f20700c032015034422130315031a0035a00300c245118442110011000e281c40c0400010707079900b40180c4040c142c0d5000196403921610340b500a034001d018080c2c404441541d440d01d0082582400148483e1a0b04500130084014100c0380120b9006a400800079400d100641144c0302c024640906020305000f5a109040c242d081489e1040340301780 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 905663039 1250 905661789 905661797
    0x5030d021602090a0b0a17030307140d090308180f062e080c2b1b081c1d06040e0a150b0a08011d0406090c0b1c150506030a0915020a 58
    0x171143c10b0020705e001c3d6800c1085807022000c0a43c000110000680b03520480fa89442c80058040104070040c900c545020315655504000d2510249500808024081c0000c1030740311400b4500c0099054030381a1901502445030891000701700c03c2e8190794110b6681d5111003616044140900e072030361494000d0380c3d2100c40e4a40102816000601e014812003a0b00b00104c5414071b0072707001d00107142400100c0300c03c000705560345a03148000220410189400035210714011607140f030042e1005d07150009040f2840c04001150440039001584501c01320081515014004506240c20301071026030180c401810312180d03035941c0b040000d4030000700540307000601038004090b90315001c06000400154050b003000604450300710206a009020310041c1e6400380c1c0000c400590030615241000111f041340e44881c0c6a0500407806d07045112860038140c80d03084462108000c6806000383c000c83c9400c031403150952105044c40001c1500c103030b68000b036108600c501e80490744400030003004412078000181d050002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 905664289 1250 905663039 905663051
    0xb060c1005161110020315091302192303010b0d030c0308010b040f050904151109091006050319090218010323281505160c05030d021602090a 62
    0x4403002a02c2c1640c45805450300e20181c2d0104078580740d44210401e10794459a0b400400548880c5511644c000e01160040c04200642400810004101d0100c0c005034801c0da00c1d4400543d080000700511801c5421000c6004a004c1d1080c008119106001d003c3c1c6030595203591001c24107541d81c0c001f514401d8401d80b03910000c007007a4140102a0181600f222680c1071041109020b0702c242d402c20f0100300d5500f02e620f15030a80c0d07546030000c950b07442c2401107100300d810030314440c0001014002a001a18041c0da10f001c40740e440100c00340450901d48103030004103408002003084c490008080690540a100c0086501c2d0550390201d40e080c84410504800c66651100500411482c211803038005d844c0e100e030050781da28004583c40d88642c0d68541c0788182c0148950310794410100c0c00c02c0c00141c0340e01b140b440c032901c804940080740a003c00b1505a80100083c0202003142401041d0703a03071005401500550400106005c0700c8020b600c4051450340c3d40c00800c0408005a440b40003c52003480140750200300c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 905665539 1250 905664289 905664301
    0x8061912031121031b13080d0e01020304150c17030a02040515090a06050c0f010e0a0303061d070c0825150b09060904141c0206071707030b060c1005 65
    0x3c084800440201020310282460308107a02a400e80b80c1181c18880318400440503080c0610035403007181d6551412a155240004000e131000c907000328111415250706605210003401240c4030300c5503024614103000c140641c7c4c414a0300c60110600c500e8807400c80550154030380000560b1036002101c04401c0250002418809400e000343c607888c001d0b9084031010300303011903240010001d0119004581c02c2060204000c002e1445c20002d6804d8040e10b10f0080100503000071405441d0310304090141e000c2401c00303000159013444a508800c0a030b01c070103c01240360b12440c0d0100c85120079800c1c2aaa113103401e00030803103c011205400e29003070b007443c2c4000d1850f40c42840c050130110740514507508000d02d00300a403040c2c0d4079003e01d0641c2c00403040b900d1407040d0360789142c43c62100158801c1d2041c00e210b0300142d0380c0c3c0007581400c02c90706680d59400300d0742107070368410701120b8242112141c2d100048030100880c00c0c0e580280c0080744140c10060200e03040000604111b440c1600c00c1e15004041500d550034488 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 905666789 1250 905665539 905665543
    0x70209040b0405100c05160602090409060504110f060f0a03230402030607030612140709150e01120f02040f0605060c01021e0316081306020d050f16080619120311 71
    0x1481c0704e01002c20301c50410310002c0a80315004201d241c0302004c0319982c54400700724840d8103c1e615940f0082c4100101c6d201420b040006100441d0112960014103c0000581c900a11000104032000f071216140104c0540d007101d190700b10000700030074152074900411085081d10101100c0711003040001c240c0d80341600406140190240a0806061822000348007641e9600d844883d10341e081041d00440c0850003408518003512030380103050840c54002041c1081e140d101102d8116503c20100450702c0c2d88a0841400e02003124200a000c0c42081c080d000050034181c203c010504100748001071100c0c2d0f00c00105950f41d0146501c80c80995000400644601c140b040c0c01d1600214408094103510b011115100c3c1c1c4200390385084103000d01600020085019080300001c007a6101d00f0541d180e0281c81542c0d0090a401d80d11140340000326000181c50f01040c80d44402081016941c6000e40d40380c2c0024091481d82c440e0030302105030310390702e80030400040301c4845582e05840380d45e6000c0d145401031607483c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 905668039 1250 905666789 905666803
    0x106030311010b041413021914031b01080a050901021315170114011413030807020103050903030601140d020f190201050906040b070f0c02100206160c0b0f0c070209040b0405 76
    0x44d208901c1c1c0910f0221130307209a4803450b80301d4030154a0f1681648240001341200000c46c1543d101d14650b81004111428088161000c080042d022289203004600744006130b0350b03500e0302d0b43d4002401030700020842000c41c0c01081e00801c80741d00051402498100600203c4851740050240306040c4110140e030070782c402404001460b40d201c13207000e954105000051720100700021103040289000040c1c40d8015072604850403210189600e05159903030349030040b4a9082030409902180c80c00c400102c0001c03010003100d00c6031905a60308d080ca022116040d403415003001c032140c3e243c69428045502c0001204c001407991420203a144d03240302d103003c500203080d5440240105202e402000c01c1c4000500120413850b003205031411b117565152550071003200d19140a6030065031180c000c0c0740c0500896008a80180542000b03154001700030542c5400f070725243c1c0480c40051440001c0000240341900c1c0c0206141c02c90500803003607140c05442c1d0001441c1c000f080d50b069494018000c180410032800700450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 905669289 1250 905668039 905668061
    0x1d0a051e15040609030809060c1606031103010b03070f090503012d0c1407062a0e0301151206090204060803030a060602160e191e0b120601180608010603031101 70
    0x120b1038503060a100400c2580b40348030040080001291400003030b0b8481d400e841009608904885000e0300d4550b4480e01e01001d80f182001003450689500300c0c0e04040e2040303e0684035900461491526414421501c0201c000e810f01d0802101c00c90200b100c1c0d60a02440380262000c00c10817001c242050380080400034201350700300c00c031031404103402685038008882d4240c550300c1c50011603c4040c1c0741441c4014040e86002204a6165400c10b0003a1006018211844e062aaa60380440c109240145030803a24000c0a800d01c00041d2581000003101c4008202c0940707104110210b440105c1364040b5095803501d41110110750008401c1024003101845428010401480182807009000030605c030120075602654014007a034800240f08210b410307a4030a00650f0000040101c2c0b065010380c01c0707200683c1f524029003242800845442458000c0740d0b4410315042e400988400c4e4a0100c55040d5a10a0520f802401e031322160002070800003880b07850015406516621030a0101c0511142181e10103545 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 905670539 1250 905669289 905669329
    0x618050f0303013501061205010f09150207060b04180308070c08030406050604020c0a060204061701051e0a030f060b0f01031503020f060f0403050f060f01061d0a051e 73
    0x4106848030b00c81c085180c80c409010003008807007607880c0c00201c00f100c41c82904c4c1e2517007006000070b00480b4030144100540e02480007040301550702c1403d20280d60ba8014081c01241c180c41040001050a13401420072600c100c034006403141ca0790005c54140e451580e0008811002008010203054001301d015610414500d052200707007040342d40300b00d520b0002400c0a8603032681c8200241441e12540c4c11641009203802c21035844001500d0f10070003039801801a04005040002071904a8071100405d84c10781c0c600420700492080480d01c2d99134098014108107902103c0c82c0d4000000c500100d0350700103414000c9001180e449040c5c0c052004403205a41c14604061a041c0354078a0f05401c071800301c09503a8112540030747c424120000580602460b81c0203551103400280000400c0300004081e44070f05d07140d1040c2c8109540f09901c800b140f000034410040811010290750441c07802c1041c0282480c00300401c0b034440b098a54011070024081080c0380320090071200341c1d050700b5140c0b0100c66569681a01c00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 905671789 1250 905670539 905670541
    0x6040e0c0409050319050c030a031508191b0b0711040b0a06090f050d021809010213090f051f09090c09020324031c12020f1215040203160f09030618050f0303 69
    0x80625a07c1c451007142108142d076840c241c1042f00e50012404008010701402c690300b40300c10a02d5000c0700b400003282241d03101454814103029101c41c140d1402101c89154640d03050240b6500c1c0c80c07528442d80c1c0394981e881a660b210700182a81c4914000c005441c0701c0da00c0002c0715003400341c16500c1480c1d6810080c812103c0016075401681c40c02c004602d012011883d120306500c1e04016940039004520160a24206012001c60a030509030712594003150701001c00c0c0903a4540c1c034644a1055410b403990304400c400035a0501410569811488032940314100c0701031666542e500f05822a00305464035051841d40369140b807150f00050110702030004080300a458800100c44064038100c0745003200e4418400d1000313007285041c0c0b20b0342c10f5962510102100f02e030b0b9280220348040101c0c42c220f9a02d4241c00e0401402450380c1000e10940344904c3c0e041c10441c2141c0b041c91410369808900c0c5030354030200140c0c0316011002443d10b0048801103050441a010310703040919083e810301c0d19040c00c0300c5072948280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 905673039 1250 905671789 905671807
    0x3082b050c0307200d11011109240f07060209030c030f03030a18170301030c06030b0d060513200a05040e0601060f02030c010c080f010b030f06040e0c040905031905 72
    0x3030100ea400021500f45807810701359400034200c014402c40d0030006940580384012031050307000340b08101c10414410081014074100e443d44401c1d4016649503c0c0c01c000861414000714203151003036240269010131450400c41002c2900c803460b440310100315070060b0040340449550808100d22400442c08a010305400c0a070550369981d130f400b000b403c00f50810344440d104100300034426072519041d900050655100c464424090308981e01c00c4c4804c480c1240c180f0f900090103486441000c2c1b420500501030107061960b9100c07040600005001030b00b8146041c60560700045501c1401c40e40e108100006032802c001d00c3c010042e4504896002d24040c600b003c000c14004880464490b054603004d003054403583c510f1440480c03031402221008041513103010101c01c0030607042843d0300d04c90190300014100f9a80c0300c10700780e01680801e64540e0705041034a0045042454680c20490b82841e940044440041c078410000d4240c0301c4c49038084d9940c3c1c000144040865100000c030101c0c90b011810220301d005045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 905674289 1250 905673039 905673061
    0xa0e0f0303160206031f030503040303140f09040b06041805180c0310090c1706090105011a1e190c020f04050402150a0917100606030608070501050c0703082b05 70
    0xc030b64002d10800d40000011416588241c400310401e00310314522848586030700d8402e580358440c2c001034000c140409a40d00079152200101c6944005482545041c00400418000544024824950310101c03c0c00701080010790000e56101d004c40c1480042013030700b0000042d10ba18000310b07800701260b402035404c4e00c4890b100000d11240e002d1031000002001030040c244508640150b0304442c405982c00900a091420005105e50007006520300800007a41d8400c80300c25203019080c024a50b40c0428802c940701515020800b01080da104001c80340b401038002456845140f40c1d0b48100049544042800e080d030419129001150009440801007810150001414650800183d0100d01d031b0005075160030710b215402c000000c00d03414003007100fa07505404800f5100c1d64205040b01100b850203800040c91071190244400302d0700c101002d002c000b414440111207c1d400a0410029446020303400400074144a00402402e10031402d0000c004250782668002803480d000341c100c01c5814001071105040c69 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 905675539 1250 905674289 905674327
    0x4090f020d14132301050f1b031006030c0908031603030f0b0d120c050303070f0206060d0b150a1a031f0b09060c0c030a0c0f170c0f0102030705030a0e0f0303 69
    0x21440f90b540c0450716200e135580741c010100150342c06508140a00942032440c0c2c0b05e0a02442c0e0707100310300060f245940184410340c0400c039074048040800c2c07541001103c1c020360200c420380030b05185c0401c0703241e102c50300d50749140d111480c500040182e20300107005160b0301d84900c600c1426228010300200c00c0141c001440c01426800140c90071001d007540e46496070040c89205113669201040d00d84a241030040540841c0c548404100076004c6da00004000d840c0c041c0030380b40540e41c060303040b04564650300d0765402c1c1400110802d58201500010203e06135000007030780613140025000d210340d0303843d00c04003c48007d4510310700e080703d600161906001c0824010f040d1011418140c40d110b840307402055450b8a0007200714802c54141c00385135005024010000f5000e02500c0300c0d0610300811596903843d810072403608401510a5400a1180400a20300454900005e010510440e41000e45c0c0391603050a40d070150407290003060094900c0040d40c10050592501100201d0103141011038854050302c808030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 905676789 1250 905675539 905675543
    0x60705030405040c210506120a050715090f080c1504080718020d0509010b01030c050901080c030915090a02030d08010b0703111e031809060d080f04090f020d1413 71
    0x1d1118008001c0d9445003680342a040c9170100c800b1080080c0251110003048260303a0a80909400521084150070005440c03540c45c0c0e106004102c940e01d0802d003c0e090800002c0494208484a10001410503224130340c14054940900a000444000c0c4100943c402075200044241c100c00c2c0b004100c01040401c2541c1100c00c6041c03c01100d071161604180207206031130500c14031500d4402440415101580405140b9400381c07010001701d8000311055030103008820f50700340010400400a4041c0d050003000c0c640008426080303c51204c1c2881d1151030019007140d1300c1c20140d20545208040d85003c00019601d107600e401c122041394107000c2314101d10311030000064240051601c12106c0703200100b00d07800c82d0313045c80c160001004160199403604e81d4486030700b4400740300c0c90700314050852500014541c05844020306601e9420304950f90384100b1341081600c1c1204150501001800d0521405015043e01176100016a1603421803001800c840f8600c01840040c818907080003000d521034814507043d55 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 905678039 1250 905676789 905676791
    0x3030213060f1416020a060503090c04051b0d0f021b0705060304030912020102070e07050901080c03010506030402150d090c090e0f0705010e04020d0204060c0c090c1b02030a021908070506070503040504 88
    0x4a80392180e2040c581240e030000d40110741c51b10300251507580040514060200d4409990344104058100020b94000783c070f00b00da0030018210101d2002458000a180d855441f070300128403100c5414418080780c00c04150f501c800040c4000320111031900303010400203850200da100d425414182c400030008400d074060386280210706405070055a0080000600a043d0800003030308510704540000c0540e0410b0090794049141040810591940c000c162416208081c041c18119502c47d001c109a00e1006045490740d00000c00c0344e0300c500c00240c052a03d100b401040507d40d041e01e050320400440e801061490320503000131200c0d4000c0c400204d580000c468007441d0626018103150000f4009104007808440ca0f180b00080c002401d039049041d102c3c1080c0a00c079000d2000e640d0750320301c400740c99046200000041c003128045e1004003d0b00c84451501e400641181c00440c1250702190340d01141201c07158504003c024100302e0880d0800c09000600403d8030140e00f890360560790a981d0340a10f0007a94415 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 905679289 1250 905678039 905678047
    0x7021e030c0d0207090608030f07020d0c212f0906220b0a080f030f0708070506090610052e030b0a03030e0312070816081603030213060f14 61
    0x548010415204038004078002e85480c5040312001a42e242c14502c560078640d070074101d0015016030044180d071a03030346d840003009103415815030802a00324a1480202c1d204840100081914000400ca81c042c165503010b400b844500d040c103141c100d480d0360301c1c02e22090023a01c040c6112100002001c001c8076010958014030952200b00c0042c0d10490f9107640f200700d083d55002c0d01080680703250401d0f60700e1075003540c43e50465515503070110303201d146000b036940d640d5104000789040034090340014411240030b000e01500b412550356506061840503503480d1003075406a03060101d4018038894a00080038101c2e8200c541c0402d451003071002214610345e20085080307540f80d000d02140a90018940000300415400d01541c91386400f900b200c21004a0b64002d100c1d0300480345000c6120341c2140d440f9a00480018141080d820740800344d12481003040754064410710841c00d0202c211442e500c00c00b0712940f030160700c43c0c2c4403031000d083d0081ca0f03500040400c000f0725100320070241c118103888451800d1880007076503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 905680539 1250 905679289 905679343
    0xe04090f12030b03031621140319020c0606011e020d260c0c151005040b0109031209080f060601081807050904080a030b0108010602030a0c0512040e041a0702 69
    0x18003464802613014000000c0104004030f41000b4201480d00c18617070000010096a03200300001901006000800c001015903030040b43c1020203541c6c072400000441700c6da9001046030304182d82154503003101540c8800180919980c00c0710441d4440804800d4104554215810003940d55602030400001e000010300881c02000c010482c140070b800008a6801c02c13420090715000041d840b80440500324000d120241c00c2c8036030404803c034056840a403480b2100380c14082040001c06c060007046040c000c2c0c40800000113042884a87e000040640700c01e00380c2480c080d90302c0e00304042c50007115200d4120104110981c0e811164458000c00d6001007107000745c201074103603441c6c105607821003580007075800704010400100308010285455940d41c241b00b5070410b0700040d180090223010700d20150304107010492600b44201000540507026408449500c1405130b14540340741c1c002c0c0c000700321580142c4104014445507240c0411451448840c11810746001c0000075101c0320b20484c1c0c03d140010410320190 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 905681789 1250 905680539 905680541
    0xb01031104052b0525050312030901090b07080603010e01150b0306121c0905030a030905060c03090901090c020606011b0f2a060810050604171c0801060e04090f1203 72
    0x12001804240c05000f0141d040c00b680e0398000503d144e000042e9030310030310700350740c058010907080719009001030482030245545500706030001045e50345150750303034105a000700f100018000c1c0101341503110316186042c0f00f03007418291014040304036030341d070704000d603100b03c1444903c0b2540848692040c802c0d2285c070303003000080349403c1c3c1070304200c024490442002d4960b01c0c1c5c5400c01c1115425521076165003036030f903000c0c16280c1c01c4a941c080e011400d0b1610802040c14500f000300055150341e0305403403a19100000295050101782c000d039400d0b0355510511262290108203203a0008000d003481110145203100707001010344059002131035003400b00c1d21202085007548020550094070300354401c00d0354070700c001040d14001c00d00c920700000e503a09000c5a11403420386c00d11000e490024080f50f1a190a201110702d03005850044442c0510500700d0b2604074184c0301800e920000b40e80e41d102c803500c0d40762150007424144141116031143d8503080000c40090000321680e500558040c0e055440441c031401d060f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 905683039 1250 905681789 905681839
    0x60c120c1f050a38041b1e0809030324060d0905150c1213050f0f011b09060e0102151905010e040c031704051f030b0103110405 56
    0x50100da4005810429848041c2c210b580301d1004900308014100000036022040d42c50040342c40341e0181886040d803c42008030410341590b94028001080401c50700040c40c5980c20420311400010399100640c242207040340403125803030b4480d4545081d090030140c3c00b054580c403018000c03080c200542c5401c400d003c07500d001d0998806500400942e141c09840c01000082c2c814410704071914060754400b1042e0340d80b0301000b9405041d00303101282c104411038485920014001e80388003400c0020f039141c01c0001e00d0400a100c000c03181b02026015545451020070700b900c881da8183d1074481c10b0444980c4103a41e00448040840d000c80c5080e000142c030160041c1c0c20128041c103900c2d40440c050f01040201c29200d09504000901560300300000e03a0313245601d4010360340a40e002088610401420004243c2924103440b06001c103803515480d05075244001084108480c4075400c42042030704008080503050b22544603005003c0c00c040c0000c0344d0344140c425441c4105e00030300c0e200e01041e04a1004c03c0805843d40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 905684289 1250 905683039 905683063
    0x20a06020f0c0d0c08090f042919050f06030403110109081903020f121e13030801140d0611090d15110708040515090612090c060c120c 59
    0x465032070414641101c401d911020140a55100c1d500e030ba60b01c864420403100705883e42200e5114105a006800c100b0104507886240b940207845001000c8681c80312041c1c90440c04c2d801925404803606103041c007400d100315052407080d248074800d0802982c0c545107220412103600300c0320f0b41d599590700d1030207580400d10316011000a41ca02060f10b000c10803404010403207a440211042c03507011008808030203078851081151481034050010042c407012140c005508450328034042c100100d0100110704400a040311081042c04a200100d01415040402d05014042d40105048041114400700d5102e501524009000c9540e4000c00003041c40418181c519070603006000c010342c0e000303904140381218040c80511680718901a562034540d40c40c1400c03104920741c0704544070305091409080214092413501692404802005400401e6940d84000d050718412050800250300b0040c030118035040302519102e00034002080040e1a03083c0001d040910500300c0c840a6956001c0c002d007050a0104003142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 905685539 1250 905684289 905684291
    0x2a05031003060c0908210405060702030c06270108061c061803050717031b250501050f0603010509030412050c031509011a0d030e040902060406111c0f0f020a06 70
    0x4034000c00364003103001001c41e45e5407800c54140502480c00320b0740300b00e84048101d540c000104420010340c20400090244e85000805883c1d41314230300004150183e2141190002c6071403490032182007900500c1d42121003400c2864082d1441c64220003046000d070307820700d621203e40c10380b03131106003004110b402c42c034071422840703100c2c400e24403031441e018040340c2100740308464240001d5405108801402d065901c030790704404082e40389196940c10311074940d000c044941041800c1c1c20148d60280c084014024109110b00c000117003d140c0a80c1200a189014165a00c00c4c4d040c003003400001c480c0082070710300b91913404000c00080c1440c0d190040c50560f01c51401c9070503010f00185c08464020300e540341445101886d00074807980c80210b036900c0d480198268102d40c44440d0803001d601281c850764001409040180c40080c01030403640006e1002c0d006544210001121189280c0c4001c80a000d800c420006042a003403c0740310282015000c0c0001207105e00800007841e1401001c24800c0151400d09900400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 905686789 1250 905685539 905685551
    0x10302070c0b1611030607020303071107080106030f02040509070f090e030c010c0201060e07020f03030a270605100f08060a0b011e09061707020d08070903150501030201032a0503100306 81
    0x1e80b43c0c8041d080254207407140702007980c28400030708020810900c10881540a1440c50f50740c00c1041d1408e0022503941d011600c50a02d011541c000c0074402c3c00b000e140504000980089503104001c1682c000170500c04094011240130494458081c1200342502c101c504086202c405004005107180166000d4800e47e40c20705403103072401c68043d4841d4042e94554090241a40d90301902642d0b2150b085a0012441c2d0041000820b84811644800800480c0c0c2070040d0420601d8500110300d040003807000d0701c40c1f603640c4081c040c0501c2170041410040000000300005c45103008039a0741c86880c010580000d46481e41420342d03c80e8130030b5890b40e00c000d40e036095600c8114105100180949618055400070544440c1c00c03110310f20203192054411140d5a0003001201164101103c50380d130054820000c2c06482c410200025620385060050000c2101c0e0004966145000040541e0038000c48484030001e001003451074007042d68004110300701d20b802e00c0d90b520740301c0406029595101d640041c01c83d9180c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 905688039 1250 905686789 905686807
    0x3023f0a0f05060a180b0a08060a0c0e04090c09020d11130f05040b061905271c0c030b100f06030b011101290d06110a1b020906010302070c0b 62
    0x5400403501c2604940200311540d642e00600143c82d20a0290804042484089842404040d0031803001c01201a04500310259218842441e03d40f05640380310440d5105d4a009001c954040314020038040121010300000b00f0503120b240e9000a140610380219800003035455040100350454046a00742107080e44e503601d0660b03400f004030754030790203942181000000c1c009072500d0a070007101e50b03508008190f1842c00b03889051890040c0b90401100d014084180301c6805a0700110130015a003522024900d800c02c1c40c07034403c001e05503118a14405400809010580c04903002d200c146060380d41c8090741c1d600310b488a200b10300c0c00b10701642c001e400d1210780078000300d06103515030070210141e1001c0e02e640d03c041230b00d028021300740c42103466000c040d16580e070550406500360111580c81c640000c0c0140d001c042c840e0312003006459107880f00e0350850303200190b00c1a40c2d540c002a2041c103d642c02c403e84040000940c00110385d07070300180c80b250425030042009001e00c400248100c00424902e02156512103101c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 905689289 1250 905688039 905688041
    0xe071809141621030e040903020f16090506100c0803071211040509060a03050c042703090503060a020a0f03020f09130506150f0304140a170405090703023f0a 69
    0x6008001c0f400914001d02d0b4405001c003040462999410b88420f9881d070400428440140503900054046206208048915140520034070000540410440c5240383c00c007244882911000361205015407410b6030498201540102d401083d5a4880843c035569221000c0444603d41c902080f005d40f20300d00001d24080341418001402200c82c20303542088a90344d1082009180c2c0300358400682560018110540170b840c06078800c040120419981001000188028240004040c50110b01207500c00400780001e10701080074130f500007900c850a520b441110b4600400000078a0110801c0c983c0208410780ba0003859802e44210b04005050800c456581404400250a00343d84560207601c0c0c60710301c03060441c000c03005c0b0b45a580140a2040c80c68843d0340d00c0448141c20059481042d01070202c1e000001010b8010354000b050048481d079440f941805c04000d0030001c003802b40014103104000e980c510850b40c0100441003000da5821214100014502250400c2c3e000413900c0d458a0ba04100015460300f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 905690539 1250 905689289 905689333
    0x340308030702071a1806030c04170a062703200616030c0914130902030f06070314090a0f261e03010308040317040306050108030d0e07180914 62
    0x504000390000740c0701215080285d1203070b5002c002a4040782e403009451810520025900501d0041c90789181540d5803000740b00c4c0c0019010511031507000556030703000744803d40c01658501450905d40c002e20324440c181c410748600140800505111700400501e032981c10580400704110034040980c0c0d00b2f032038400c20401c81c950361402e100e0086480c00c1a50160070344100f413480300b035a0130035020038030001001e820440c46c00811110703603e0840e11a8903000050700d082c03001c0711f03100150000800050030501c2020701a545c10050388076500540100300043d05200048098006411202c86248440c2c01c0c1000a03c4100407072480c26106490f00d00383d90f02c2c00c0340500401c2810702e04c000408050318264081e518500c02880701420340341d810300c81440072a00c080d0403941102da44160862500d41d896803038030203a071001da000800366000801c03040425512805080102e03070340790f13000d0940d25003005512092810b079451100083c0c0d941e41007850400c5010840c807008044080100d40301125520702020f61545 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 905691789 1250 905690539 905690549
    0x9021c15090f020a081b0f13030204090305070b0105015403020108060312090111010219030203010504050a0603020603070507030207050306011401020708060f160e0409030e040c0234030803070207 86
    0x150030000610790302083c00c41000c2003146c1c8140c4074680b1850005840032038100818441e141104403500000581d200e2151989041c0f10b51141c0381c490308a400c1a0480c490168800d5050118400700940c0c4030307841828402c5051460f00301003c1d03803040345c00d043e03003031002c464022001900140a1112812020b01c892800c60740701740e861511507680c5a041c107481d05451901410f103050140700740541d07903001e5180110500160f90005003460315407036004500701c055185071070210ba40000140960705203402102d511262162043c0a22890760340800d0705440002c0c442d604100700443c3c040101031007805004000e0200400300c40142d41c542c0440034140d0454480385015101c1d411000030005000320b00d0310312515204034184859990708076688444070b00c0660b9041086480078100000da56903114040040c1c0c001d030f4425000704050b078284070881d031280c00d902c401d540c0103502540101d040307a038821802c01100510400c0d0001191040d40c40502030b60001410388070b01100b04103000742d00107285021a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 905693039 1250 905691789 905691797
    0x503120a0b1002011103070804050a050303040b010603050a09030e0f12010f0b010e01110d1412070c020111030408071202150d15050409020105091504090603140709021c15090f020a 79
    0x4400c2c4180c0c00c032021100f0782d6480660503c00500500e005aa5040e4442d0141d016500000643c0d500c41d41113610845003120cc0b886017000500605a140c86160360240866008016005017914042c1100400007203080c491901c1241014050301d60030144103582541034000d00025508400c5440505485125180090301c845003070341c2d142d88640405090110080041d001c0c4104624044031401840300031459164410810460000901a0454401d103132660f25a0554441c03440010b1240030210440e242e0fa9000740800d001c010703000306e114021204c0740754410f80c800c0018408a8100c44440c41084103411010503c80909100c54211400010080009400c160785a400300700c100c5c2e02e10100a40050828020b01e6024101910798000b40c000c14081d070340c02c15695a030f1402c2980c01a410469051a40b03060381500e440c410031030580030700003110b07065007042014013800702100d1051401408050b00ca011402d42c0803840ca5440c809480301c0d40080c0070013900c0000c1c01029522412a050000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 905694289 1250 905693039 905693059
    0x714040c091d1e0108062a0a080a14040308010603060b041a0d0f1b03050f0903030c07060e0d08150406180b030705030d11060703090c0e040503120a0b 66
    0xd600c5240e0580594240304507141c07036461200b107000d00b860001440305000500320710711900d840d02d00341291802040040c004000303c6c5041d8110321801c0b00c454544140f0854640180302e02d407900302e01a40d01506e518074100f2803e9035a0b101f640c0141180d505c0e0303402c000d5107030001c0c4820702d0350100030181070345c103d5102446510740d01e260000a5200d24402c0c01c0f2000b0500f2421034010510b803005101a6420480100e00c41010840150488040d2610340107002c9400c10030048103901400717400d501810702a41d5400900c3c241c03c0b03c986a10005040034400e0324001554000c200b00c0798041c0d860302c90000d0484413102041500503205c170200351030031400001203640414140c6024060b13801510700042c100000b1021040d054005020409665645400b4402c80803d641e01c04014120700c07032880c2c0d512074001804c506c0d600340c2001c07006020102014104031030036001c18280c021110480d040101c014141d6902c41c01c1440c11401007101d5044108910000e202003034420390044a09080116045108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 905695539 1250 905694289 905694311
    0x90c08010b04060203033402012c0622170d11070f03050c010608030d02070b06031504030c080f0c010b0a0609031e0204060815090111041214010e071404 67
    0x1e00e0180d440b5510050b442040026603298602c1107500743d0100782080b0145000204c0a00e070907494000c031407000142e655007014400798042920b22017102000602d0100b51200000055803680d600520407104500500b041402000000d001019207039000100c6c290100c6d402c40e96681a07501c00340c80c402e182402d007155042414141001c80b049250702200700180c0038040d54068402e60040c1c0d03c200e200e5580c403a00061001c40501c01424484440003005a0700d000c586442c210405c0041d1400d4002c0e80304019000b90b080550a00c2e81d0066058100141030300200d203021070f1903114411100442c03a6011500a4521105400599290301c040728964411a200c41080350316803414407010344500540502c1c0b048418003040040c0c100b60018001150751919009004d1504c014401080a45003100341000114a428424100c0b05260061010b242614003080d8001c21300a003400034003802e140d020002c00201095000e80b4a540c6804182e0308026603e9442c0d8504080440d0140e004604010082c02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 905696789 1250 905695539 905695559
    0x3070e13020309060a0f0609020a0203040302040f0c0903030806061b0a151e0f0209181803040501050906130509010801091403210c0f0d1a090402010f0309020316090c0801 75
    0x103c50084400202065901d158401c0041d0003900c80c0c481c540c50380c808000c0b500801900003000c96042613001980c2c0c807441d51042c4401c41d01403442ea014403d180400504510350300881050482c4d8040c80d00c0351085c1c44140c0090007a115942c00500941414443c00020403804100020441d000b60604030120343e0440110341580c81e001450b207035072a5034001c4003145a100b6403200c103405034140c2005090641800101d070242411100a0300190422000c100c1500c00c0c2180104c20a012400a10b06041c070340300000e0100d01036080300034407801d80440c95071514000200ea510003400001e101401035691456418020300e21003509803801040482c03013071070002000080750310f480800c2c41c00b8034a41d200a41c040c0d41441000e00b00051020301000040d6051034104040d00d0119070100d0006000602c19440c112080b110f540158083e0318000100005030f03821044060400700e0b81d0901045020031840001d081a1409103a0303001c02c080e030304000c0340d40c04003544085003100242d116a506a625240642 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 905698039 1250 905696789 905696791
    0xb0a0c020c0307052404090e10060f050904141f0605090103020f240a09061d012a02030f0313060513060e12012a0c05032a0303070e130203 61
    0x1909503000344400c104c01d0900c54030700b03602c0e000007042c0c030000711680350300803051640035520030b580413a1202e50604e1412070030b01c0a8000b0340c01a074000c108242c68a0400d61030302140784515449040c0309000034062180b4461b0001d4001102000e88031210141c0104900442c1e81c01c1070b81c0c03209031134044042800c1c1040c03410941640e070000c3c0700c1d0141c200064200081104510703810003900c41c00102e044048140303007010303004013036481d26001000e40c00c000b030040c280400d010150401d03c006030941032141c0d0300400d0600c400407221001107046200e04410b0780e008520040025058880d03c130301c02c04a44404405032602544518417001556034988049605029084801c0b0b50b01048803810400d16000e446600ca10140180c080004c280e0300b5040070303007110302440d0003c16a0100c2844120007114112100848100c01d0800785802c0016448403640e03406406100320b84002483c00d2092143c59200c09140071845950031280c6d03e19101c5001015042e0780e504c0315004a40014500050306000e00075a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 905699289 1250 905698039 905698063
    0x319110d02010c0b1f0303020601090c050f2703150f070f02120904180318380d0204120b0f062b0503310e01050d060204120b0a0c02 58
    0x400709640d41380c800c043c00014001140d002280007000b400440900f91802c019030103900030b41855807420170034105a40c00610f2107001c1100c00c010012214480030180d59000c0042d0110101c1100d41d00c6049641c108144000c650610130380350300003080b00d0b10019491040030103c50074040c1e038880031010307518000c3c194180800f50b005840c222080d000400301078070180070010004500030b5a004242010804198002d0b00040c003004802e0b81034071100703100c0d2030040c841e201c2c40c0700410100180b800c048200015814082c41d501000742c20500c2082c000740c48001c8040541155600d640e00401007804c0c0f15110110344a0350f02600040c8664044000035200c1c41c800341c503c540c1c0b40ba51407500035198120344403a000702c106060041001c1941080680f00c850708200c0c2d80b541c010084540c0b060200360560540c10300c0d9518250a01514100c1583c441c1100c0c0180c500c0804404a4034140010380101d403c90041c4640a01d510010b1090070b0320400c1c040c414400041204135017412080381c64400c1c0d4501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 905700539 1250 905699289 905699297
    0x20c040213030f080f210f0c03011701020c01060909050601080c090a0b010c20030c09040213020c0a08120601080a0b0307030b1909051e030a0e1e0319110d0201 70
    0x3000450f0081031000300b614420184035150684008589120303400c05201d05200c05030b8195a0581048140141c64105040c4400c8107480c0c0361020b21005a80300c14000c1e1240c1d008940040181e942d000d40554110700c04000c000e01041d6242c1003094007d160b40300042d111441060000183c85101140e158010750003d0701c59582d603501d0311031042c041c045801d0054104031054070248003181242c10140c00d650580001210721050035400c251401050702d1040303106808076004d110040e03940007402c92446034040e40c09601c030b81c00e030341d10a828006024000b1b4080e8000003030b442d494018003e0340c584500402d8031000c0142c0c403840305400444500c40c0061342c2581c000d0b28140701061240203102d40c032451500d0041c15000a40c1050829601c1102e002c50b4964808070842d4648003071403c00c82c00d4061800025030034409041e400510300d58034582c100d409071980050b10410600d8803204900c2d02c55001d4101d40c24449140c1140c500c4c000b80c42800e4510104a44803401203240082c2d00841003501691 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 905701789 1250 905700539 905700577
    0x10050a05071b091505030106300515010b0705010c08060d0647032b17040b0603070602031e0906070209040c0e0f0420130204090c020c0402 61
    0x184026581040900041030088612000143c0d05240c1c0101c443c190744543d01d50408520745001d150940701c40e43c010801c103000c0a4124203401a092240c000b1351170201e1100d49203140c407030800d1030816441a2002d140c1070001e0002281c00c012001c001c109d5240300f40002c01c05020042d4040b524181c051303581c03a0f8044840b1030803101081054010101d9400840000a440300790001c00704030004403c5040500d00082c1d601c6a258125401401e04e013105054000d0003c46000d032164281e0382c005215036564445813104445211032248100310035402d0800801c0429040508086c001c0c00b1045902034468858181e000c41c00c01c0c13003c021303642c00012600e40b0b90b5120b8a40403103040726401051201c0c0d00f0102c14800c01c0096900e00783c3d00c0e0f004030f010b422480f40003414800d07401d560340740061012244200400a210004100380c62072440810511540e042c840b0180700000d140030301d80d1440c4040c0c4d90000c08c0c04a4440d00f558080345130395815800300c500511a10092005038021960502c0170007020305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 905703039 1250 905701789 905701793
    0x90603310c053d08061e0603151806041808040b161a16030e0c040209030a0c080c0111150a0b120105010603290a05100201020702031b10050a0507 64
    0x980030460206903155035103850304902030300b4090203c6080c92041115080f140300410260003000c040d401503029201c4488142903004256642e100c0e03041c0d1180902c00c00000940d00c3c202d16151a044600000c00c81c8015100d000d400b146452820341303845205510308501100d03000c0005025540b4194820031040c205494200320102c141c10022203411095100050000010b840f460f03040c02120340599502490700f00503140c0341d4614101d03809182407520340b444543c80742c0400039401c0354640c1d086074096030b00d54400c804a42410f08011004219151028000c50004c00c00f10741c40e2106202030366100800080b8400f01c5941c2d040030141c800c51a80303140086800b460440c1c0003044090409000701c03045c1c00796145480c5c2151000d0348810000317951001d0103040c00710300f5034132100c024105603c842801c950410000c2c01d0582c481c42a00d12a803c0c0e9104210900c0c000e40583d0f070001d4005044d03610390240380911188248058051510900480d1200002d42d409002030342e1801e0320f103a032458180b0690b0f07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 905704289 1250 905703039 905703049
    0x91a07020604150209030f060907090b1005120a06051c02040c03021c0b010504030c08070501020607030b0102060a24090b0405070203210a0f020d0f0606110d080c090603310c05 77
    0x90150560180249500b911601c0303810440239004445402c000c155103490129100125070008544a1241c1601202c4101056100f001d803070320f0b101c0000b4450101d4481c0c0c15244001c240c1d40c1d00c0b544d00424031500b800d0044011406034901c090082e0303014082400381c440114200d1003080c030364040428030203549a40b4a81281d221141f4440103050007860a0348036115514500101c0d0310408030795104c00814407555a040c000107802490b54101480703079110140001c3d44412008025420155440380c2d901c40b038101d028406908800c8242084415544545281d400b13020508013040c081e606107408100014030006c125903001a1460345020070207001305000350f0010028082401680c3c64070000494103210b4070041c0011262800c0014813001141601c0b019115294042c90600043c100c2c0003400d038501040c032000000d0b0313515040780e00c1d40e12070b43381c440c41c0c0c00b80c07240c01307a08a1801320420010000240600c0071841a8040d8401d81154860100b50105030b079a8004213044000b0b0703070400c014100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 905705539 1250 905704289 905704297
    0x30c0f090612091401020715060b1608090a15030f1a0a060f020115150806040608120714030c0a02130204080304050d031224080303150114040801091a070206041502 72
    0x4103001e0100c4000001d44c01d5426600031384810341d4440d01002290104076554450140204203c445040c28a0000c118846035440e03000300107050f603540002c4001c8655101c0d0359180141c0102001c041c00380750741500c01001452000d22000c0b49619184d1044050000e491030428a50300050483c40340f14248002180c2d94100c10449105640d2103180c1d40300e8086070709000304040d094142080504005560009100741c90240225000f50700d0004248040c18000c00c60540d90b0400d8406070390b0790803a61400791010114402001c1d00ca002c042032130f400c18200441c03448107450017128440c04001b004502c4000f01c0c1300b01d2040801d154002c01042045060502c410350029019003050344032000c000d440002520440750750481c030392940c0c008400480c13080410b4030000e00800e1b002142140382001c822101c6203901c80d041b905114416144018030414441110060062080203004140c1d0515058040c4e001d0500c1500314104a000000c1a840c4000356003441030750401074042c1040c1f07450111a0017548 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 905706789 1250 905705539 905705543
    0x50a0b1605030d061e151e050c0106140a1e0513090203010f0509010e0114040f0807120c170909150f060c0f0f01060b07032a03030c0f09061209 63
    0x901141c0c110a600f071081d20002c0011740038046019401450000300100039400c100000098818800c4140c2d502441001965440800c881081c070a0840107860358000c0c6284206590300304400410000340080d54006045400c6c1ca6803e619516400b28010326080305062142012483c0c00410003071030300b4114810040040c100001c1c0c101d02540104e800e58109000310804140c9400c24000c964009110307514040020500802c040074088219040428028201415000c043e100560074061060101d0b1480390740011a556490b1030640041d00d0079403400c9094814800b030000c0300116074a203104030b480062000b06100090780d00d01a83c01c51001c0307180320090b00315500002c04030003515a040108070702c003a000300910500342a09440c40c03608401208840413170741040400c11840c28800301362280b00740d1509003410100d002070902520a150a039101c08440080c00503081410b070554400006a0368a650b4040c1044202a081d43da04841303126080002e40e40600c0302c00404400e07400000341ca4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 905708039 1250 905706789 905706793
    0x6080705101d0a140910050d140321070f17191103070c020f04060803030f0403030207050714012706110a29010806061c02030f060109060f050a0b1605 66
    0x1010440105030b210100750000d0740ca41100203084015442d044a1301313944000302c1c0c040d468005007002c0100b40c0400300e523280180036032990150003001340001e20540b10243d010f00500308107009100702054107030178140c13061000300d1840341e0450011841000c9213500094200321402d01030300c1d503107802c214605210f200d0086880d901c0900b8120000783ea0019030089200b569180d140b02228010040c0800f0003110240c40303680741c075600300007454000c0262540400607a0059240740d0362400c05401078418180c00402d180035032000803590281c0b5180da41e034140c0003a40c600040c0300c9035125440807201c524404516400100c45c04100350b9115250240e8401402015100849000d0307441800900080c0344c41c200400740b888070300040b01c066902290050220200030000b909200000c40c0381d400307078106003c0028151883c04415903c00b00f10300e103035409443c0e0807140075603511030b5000020170060141c83c903281d121400c005200d142041c01c2c102912400c008480c82d100718800d20459240410804031294 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 905709289 1250 905708039 905708087
    0x1b02031509031306050a200c010e1201022803090c0b0a050d0e0c19231503090f0706020c090105240406050406020d2a03020106090e030c010608070510 66
    0x400d8884000c00c020200c6445541e21011b040e00301501c3d5007540080c0c1d580d410210503060110741d60000c0c0555060b1001e09000c0000619480031a030f0605046810360320301d41c000910f21604d8010441007056214103180030710500e5211000c110103031740c1900c1d40540008550107080c0614581c10004150409141c2000340c64459040244019a85580002e45e100d800640c2240c269082106038003d141e00c00003190000c8a007043c2035680102c41d840200901001d10300c1283d8460717102d445003080e54840c0d0301c82458881c60014643c550b1003078444200c0ca114011510005a100d00000d248103940c2c100030b004806aa0801d000e2188140e40f9a01e00310320480c2a2170b0303e00501061100602c0980355a030b41c5d00d9072300d07824600c010385032003003001210081105402100708080544c000d000701c00154610018520300903400e040303004d40707459084840ca2501d0031455041e071460000081604c820064000c0c40456a135a42c40d42c0c48986034842d12b908501c0322103141e0785ca2407185030801e04440500300d00d2002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 905710539 1250 905709289 905709307
    0x411010e19030c0f090603080f0a02010f020c0109170a09091802100c141902280609030c050901210c08062805220528031b0203150903 59
    0x101c441e0320030385800c81c0c0c0550034400104c0c0c00003400041e1840c2030f01401034501d540d030752198511807001d030780c8004000800e006880d18030030341090840c8580030b0404c0d5202d00681d42528001c207900c500c01c0307804c80044588140051b2210301614032151580d140c0c18881c0b45003800c000c01a18400d501d80c1c0c2d000380c01030b5481e40182c0e81c20024030030406180c0d407008070003881494503900030301461140074400c0d4000c2c8034a2209002c00d0311140c24507035054810714035841c070000d80e22100c2c0b030158091b0f210f8103001d04004502903030320145580c21680a10981814296913505000e01c958080c015507501c05204d01140c525101d0200301301d1140d03032040040c1140039135140111410400181c42284d240000d0350500c008076903a803000c0c2c28002440c803808101909121141d05604e54601d0240c03400341d40e108464100703000060245001d000f48013560241d5071a001c400360504044100e40481c041208003055580780c4048411a5020560143c02400c0001450940c8a083c500007017034204944020007180003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 905711789 1250 905710539 905710579
    0x8040b070305041d040b130602070c1e050406030503030103141e0a0308060118170c131b0212041a250201111203150303040f080d080a02030411010e 65
    0x102541c02540d4080e12607040180c0309404070b0028003082940028001444040b4036a0701181c1c5e04100010901b05c044911440d214002e8015508003500c16400c0010000d210074518001244c00e1003003110010399951a8400c1208460740d50001034500d03131041c001880094102440014100040000c58228201240c62000ba040d080d000202440c0c2184201d2402c141e00941c0d107a0f0094003d09040104130320401c06003440d54401e1150585da42c08801240c210300206002384460888013402018013000d544a42c0405080c28840b129a28a40320184118483c800f24201e0201501d61085500d043d1402051105080c0304500210b43c4040410200c0c80380d6031100c6d9406d440010318111f603110000d4900003d0420701b010031501740d468001d1b51860044000000c00c030b960006021351540003d00d42000072a1640c0680e803c4281c00c1e680d001d4010480610010ba00e11804243d0345e14031800380e54001009042c1d00090f10010b00d05a0000400c0d8015801840e404014100140c114121403039040c580380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 905713039 1250 905711789 905711797
    0x2150f0c1213232d0f030403150b030a081813090203010c1e03151502100507030b010f050d1103010902070303180b1b04030506010308180f0f0d08040b 66
    0x102a02021000342040068201d00c03091643d09504a642000403030103950740d203580910720960701c86004031103c1c202d46491051407181800d1454119498a521140115640d40c020f020942e0080b100b0400000200c1181c01035420000028002d4420001d641d83e03800c00342c2e00202444142800001c3c9145215203c040188955078052039021813404190700500d42180c900204480400060b6048015150f0300c14038203050410b19807800240001001d0804078606c902508020011a4010400000755500191030005002d80d28030070000350702c42a20a5044440346000c03a40401d440812403045a40a00003030402c510200da4042611448403061a410354002d030001e0b20a15400304000c001e0513498885c50903452403000200c40366501a4480c3c0d080340b48010100100c004010780c0e81d04802d0b41090554008650107021541c0c4c42d6182c0ca4811b400b03420000c8161050302c458014a2454600761080102144000e01040c803005092000d0001e01d452000b01a00d2141c07040100040141c400c1c0014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 905714289 1250 905713039 905713051
    0x120a0504031704020a0519150305040b01081c080a0212190e030306090606030702190308010608060d0215090402130b0c0c0603010807050f120a06051602150f0c12 71
    0x502840c1524000c0c068840018806240310116400c000041e1104c030058402d460302210786c6201d165501141041c1c84c440794000304d084021640300d0180594045e084140514443d49405841d60380360020781d5610700b0810030445524080c4994203d8250240c900d10303030404500000945858105955001c01400031340d11010700309415403ca1b00c4086441c8900c01158907514083c5285040410004d010200f010701928414200007000c41e078414020030028400c0c507203100d280d07601c0c0d0000c0d080c00b41140c0401d00c1014007003040c4c200024220700d00944802202c50380100090b501c2481400c0c00c4883d50030001006402907400c003c09240081c803403219a00900c980009d00e40d5070030710707035980314207000c03441e00c1c1140a80c02c00d0006000303880011031500240c41080e1500144200380c000000c80d010280c0c6d03003940b518055018044203020054001c9403080b100824010b03185280b5280c102c0e0f480c1d0a2601803403403442d031400400c00348140801500d40003111f0041850410f03a1142108180310000c3e664 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 905715539 1250 905714289 905714291
    0x60c160303020d0f0918090b0705130b03090319030e03070f1103010b030714010210060b07050d110d0309080f0a09080607140712110105090703021905030d08070302120a 74
    0x1080080503810005404912510703d0b00d00d843d49242c040144c40c1103154060302c007584d00c61b100c6c00d2a948002ea480000c0c940d4010442c51403600300b00001030030f281c0c000300710100c04140d107010226120144404480c0a00e55000c021490300b80840740801d150181890018101501daa130380e0144010108041d2402c18024030b030b41e4000e0119031403c9408980035150542c0264100040b90825903408507011084500e402403c41c101402d02004034145075a00c9161301c0c4080c9480d030301250792802e40b00540b2a80b44240102da0b040842c0c0c0b0f5040c0c0e40440c10241c0089550304c010f100c0840103219800c0140060322510200e0f0400d00c0d03408100c641c94100703042a5002a1035804200844541001030540010142c1801d50300b00350a1104180c082c89544c42c050030015403c0e0303509101612506c052000502400020400303030800080041d01c880c5c040c40240e20523802a0740300c0903143d03030020300e1504581c0010028010401031200c203455407400101354505240d800c0c448d40182c4034044100c0c500c54042800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 905716789 1250 905715539 905715583
    0xf0315090703020d140f06060f0d021c0e210f16051c080601080411060702031218150a0e0607061a0111061e09010e1207140a050604060b060c 62
    0x3c24134115101003070343c0352005503214148034000e04044d140c5074022000380c0d8010381d51564001c08420340d215130b05a04008134400074120000070304400e0000044006003000740828180b029199907242004e041070300d1040c040d1403402285c003c010001b40061108816aa820b14103100c0058022842090050b981c03030300112541031417920f01004d860a507140c60705000c502c0381041c1c40020003c1800502c0205941583c0300015150b950712015203218903401002c44010b5048414551080d400c401101400801c07194246819841e05090b0303115a42c402e14074990030725051060489000c483c0d07041468000030704000f12408580c040c001c1c400181202502001080c035200001000b0b0528429482c0554000318140280721040003807250940c0900d80e1168070301e843d9089000c0c018100380d604001c407482481d03600306021044401a000541c001e181d24042040172041e0b081c2c5807210180c000b007194001031b00140c0025226402007221101c0600320350f08040300003d03040d1600107101400140415841 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 905718039 1250 905716789 905716807
    0x30b040f02210f04081b0a03020d120b030a083001060806010c050a03112e0b01091208160210030b0f100c0f020619051c0603080f031509070302 63
    0x102000450b120445110b9282c60500d0400e10070200150004010000c0069110000003803606904c9044202400340c035a544031502e406580c40f1443d01031500401d1192810448010040c03040008060010340a4028048282d450440382e5000000c038126000c1c06240002407007154007a10300c102103030001512469410100054040c0000411050410004615030000542c011a00354201d55250404d00b1152510064a50801d01c0f075102d0b40101c0e4880240b411561907060b0007005101480300020030814604400443d0800030501403036030b644000343e10000001c0d1010f030042c0f101e2140d0101400c2c82c40040d900040600744c00c000040000b9880350303440f291500d0500504001d1079030031591030049131100c3c0e4001d4412841c0c20000b0b17010941c2d00c4450000c0d5201c40f41111001241074001c00c00d0a100c20501030034541042c00c8071000d05602c2585856140414801d400550b90028911410120103401e00041e90f80010840c140c0030350070341d84148075900c552188501a2003551405601c2d22010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 905719289 1250 905718039 905718067
    0x323030c07030306120825020910050a080a0b070513031208060102060604062108090901122603130206070c0e0114092a16050601050918060c0a030b040f02 68
    0x42e0041240807905001c00c1d40007a0086045030703004c07e05240c00306800480c8250920711204a180e020350401c01c0b02c01004400703403020078114141d0318101e03280c800c500d40300c9191640c1e510f0b400c603004003c00f280501142c0716600400191803280d4511120f181950784a0352120101440c0030080004500c4100900003a50b805024003503000384141c50411202e441e05e120480c00c0303103001103483c46424040c580030050000e508100c50900c68042c0251540d565500c1100041c980c01d81070a030741c00038100e14646559000820100c490420f00240641503807109000700074001d004807402c0b039101d04100107000028420159031001080d0a0200003ea07602d0851480d05001d840e102e8188205042030411154030100310750181d014805946d50403400f00d100404490364490403442030701846c03c0d000c1070800c000c40040c01c281a1502030b503002a194641c500c45a032242d20544649240350010000104a00c1100000d40b081d02c0e168540420948442c00200d01110b1942202c60449a00001d1300d1550701c1d0b40d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 905720539 1250 905719289 905719301
    0x11190f030f0c060203071109060d0f0b010503010e060727090e06090d0302070b1b370c03080f070207150c02030c09041203021305120309030f0f07030323030c070303 72
    0x4603002461525200d5a030320300a0b00c811f014a80c1c840c0c845280401c805440b41041c1e2550030b07511080382040081607087c113100c80c40e070900c03d04e0b10075800c1c0500035618503400704a80740204841d0b119491500c00c810201c44651000c1001030b035034902c43c180e0000da220028012440034802d013102130040ca05214000d6820803d2a180746000d15004100d02800142058030041d0710002001c00f13440e6504560f01c600140744145032103048001500c00854007209034030203200c1c2000302003400c801e4152010b64002d5612003408580a00826503942c0001d013071400c0d00c00c000c0e82c84002071054070655500d038281c81c0e010307242a0084500040101050804604007000040551036044681400c41d2410340c0d140d628103603081b01e00500f0150045021880003501e803015801428004105038030303050b203003a00c041c2c6e240c0050503c6442803148142402c19070301e000c0754200107400c0030800b0304000ba003543c4065644882541007a410003444205a2401c0103480000d18007c400c1d800d01030740c0d5084941802410780729 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 905721789 1250 905720539 905720549
    0x902010e010e03030a120b0301020c0d0f0806150702031c02150903031510030f02040329070e060a0912080405010f0e0a0303361a030411190f030f0c 65
    0x38074510b6400c003c1e6000070584603824030f145400d9100d80941c0f0f483d0700c09401021401600b560002c0794014114001013100a2210030702c1c0ea803010802c650b10000c5903a06000d491194004400180b0361717113420703d1800100105070010702251b100302044201c501d0107440b40d4200c200140c0241454904144603002c1141d0000c401c0001141503040800c8a020314100a02c0300c039225441c031034446400c0307600030f411809031004800021522103a90b4285100f4442c2d400f60b5081c002c25101018108425000f01610f000d0040c0d80d851f55040f48084081c00485c1d80036007070305420b0040071500026540044d45440d2240d030b204607466a10f403860100050042484c00c00c04005001e151341980f2210b86a800c8103900b12a0103142100340ca48085255030030012000d2001c3d074034000008444540b0309e1002c1001801c46e842c501c0281561160300008103414002034034002c1c4a803000d50b22003192460000003000d80360940007034201c0b0301039446a03510341e080c01c9580100d071f03081c0c034045403030060002001505000305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 905723039 1250 905721789 905721797
    0x915041805060112020d05030a030506040501060c1505100e0c040314061e0406020f0a020a050d0504050f0f0418050a06051501300c02030424050409090816060902010e01 74
    0x44203aa99450322510140940300c4401043c070030078415503682e41a54150b268200003580e56030744032204000c3c0903000888165015038109000040d43c144100d03d10701c2d01c55002807440b29810074613001140501401361000c01c25010126000c10072503010040203014515081201381c0d00e5240d458203018603402020203000b0740c1c000d0010000c12640800e2826200c010100e00805c4a0b0b66600d4284000d000c0c10b0704442440e10b01249000a1359000148050014007450880b100e200e0410011106881240141a00802d00308448445070030312140c4145841d00040000c6034128091040940c0010301003001c1c0d8041c0e01840c48030f000e101c2248640c58201d210388030020414164600041c0150100d460302c401c00701e8140d40c0111404e020801c000c22030b80408030003403140d014042030082d03498000b400340d040303880050b0880c0800c01891490803485582030352501030038585014442c0c40140704141d0709543c150300c100a8504200c520050a26840b4816540000d2442290000605244450131114140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 905724289 1250 905723039 905723081
    0x100902040302060a21090b092b051b0a080304110307030c050607110405011205060c3f040818010804080306040e010b060d1b030b010c12020c091504 65
    0x141e141e15044984c2c1c0070041c1008003d04110042c0c0014118401800005144c03804040c4400c001c50403070310b5805092420300b00d49030400c1c00c5160070340126001540d80800001d06c0a030a00081c010400f512811034500a0704a00800d2411050f040007000d4000303d40345800082080b0812017805c0c0414003500056004143d05402c40e660401304020a0007180c6c13107080003042440c01c000719503141d0401d01b40013500c00e10075940e540000c2c08007810702c0c1b5011282406104c001030b44903036001003612049403039003d440450303190640324041a280c15003502d12805040020340307506840481003107806103214401c0d495807402d0201080b4a030500344100380e4104071002042c00040391a10060340e801c41c204a42c001000b0025403806030040070380c0d0540d00c0d080340c0c01040c1c40d010b0341026070041351202110307071407030403c0c03440314004608403003960013501d0108019501e00c4020a107500505400e8080300d004896030801942c00007224480115000e03861407180c00081d5005052500480034904840c407001064 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 905725539 1250 905724289 905724293
    0x8070609050d03031806090503091008150906030703080c071401020f060a020f070b13021f020613031202031306061e030f081603030204060215062d030706081009020403 74
    0x540b40c45009410141c030390740003040010b5202480c140c56544000304000c0f8000300c1c03516a48135040740c81d046124180b40c4811021890264032a9032048070a2041c405d4441c1940003040a000d401521968040c1314041000c00000c028900925a02c000c010007071807400c1c030f0540041e40500d503120311107046405c500b6000e0001e0790006440c83d0400c03072520300540c86900119814251b4003646a010f40a010840188a00041003003006500c2e140207588443d0782074000c83c0104915843e41c48e03a88016800b0f00001140c0d986041e41c0541d40c18828a441c080e29440389240a0a0b84c0050b070708a81e416a0240601c020040d59102d240020201d0f41512407210050703002510340010039102c0901010784051844042015000c225201c031644c14242c0b0640d66400d040080080d0000e006080c054421180278a46409400e40c0d0350340f041c2401407a000200d004d8804030300c862041c94040c0d03510460320400c440050382c1c0611915000d0011980e8401c0c961070300036034008070114282e02c90390b5881d10410007440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 905726789 1250 905725539 905725549
    0x1a1008060906130f060f09020322030c0b27070f05130b040623010306030b06060a020703050f030c150103020117070509040f020307030c1106150a09150807060905 71
    0xa400030040703868501070781d102d10104041c104920b090010184c681801140403880365481341d01034400e01c290000e00c441e100c280d4141244000da4030b82d8254106920a20000c140010100c9030b4584245020301d214002581c903071801d4401540c01d2040b51100c8200480078010b01c05a036042e08606a0040808915140829414000d01d000c0c00307001d10014078111522661a4200c1d481104000d0002c1111350b907122001d08190101c0c032807071410050384110f00c0780340358400e00a10302070f40d070000d800c01d610b9126401003002a078400c0c00484154002e041000022550500585107003e120001842c0d0ba1f000d42180141040030300d45880224000300340040c00036036400081104010801c803602c01554640d050103541d680a032034190340e8864240592202c801c1c0480e000342d4014001c03074070706120514241c0c000703941010204c10107005075030125001032152556000c8c0000703143c40252070303420801d0300d50f160303002130b03070700381c1031940c6141d0105c80040005450800603c80105810f14181407002d0810000407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 905728039 1250 905726789 905726791
    0x15050319120c08070c0803070318060e01110f07060201240e01090509150a0c03050a0903080604270606173f1206090a0605030a06020c1c031a1008 64
    0x304202c00020314904000000049881594001c80c1014500e642c46440542e41d42c044502140091034080d81d014803400c04504107020303106107446100310500c03410011a01c00c40c4802c04405980705201040926403030921810000d41555800825815081c040d15000255044202c20010f182400b0820147c2c1c80a140141503030424100800c5135100e1122892800107a80d110704040f090381c5060062001c4254000718104c50603480074040c50b59403c44403011201c0981001d0041000c08001442503c0c10340d200303001c1e421003000b030b405643c2d5030440e60500082d1106821aa403a5880000344a001d00710642d00100500d01401030a40034140206510010351200d078045002e0003c110161204950203041c0355002c20f031412850721605c0d01030303041b0100d034015113a80740103030702c18404614104658010700742170b2000500140900002d941e0fa8034000d6000310104d00c054000c004032052403009a04902003030104580c0d0109a032039018036092020341c00e01e040a031040800069075130100350484070f29 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 905729289 1250 905728039 905728073
    0x123040b041506080a0c1b0f0501020c01110d0b0306011d0615030c07060b060405010203040b2101080a060c030209011b020d060203011d0c0f1e090415050319 69
    0x100d1150369000104002d041601d01500c010080b003040410380540c001c22040c401d11803460148810b0030b080e9800c3e100c03200004001d01c0e07261100c0e480030012910080340001d100b44240001483e281040d02e50600311240741b0b00d041d100c00000a03d03003610b0f0980d0300609400070301c100c01501c01c55142031a02034001d10351701c040038001e8068031f000800301d9444034001d90200100c1e080c0d5030b40e01d20744500058070035404840c08689d201d00d004031001440c2000b0041e00c09072a010780080d4a050308040c040c10307841d04045241d141c83e1805454081000c2c10301000c25000309062401000c1c0c0c594280f9290041d40c4061038070388201413060100b981d8507030f4404c003079508118640980d003d410b8918004200d110080b0240600858000000018541500000690b00c5290403000b107110751180802d00700d052154680c07100c0114028440a05e03840500b640c003000c03010004000c0b51074407280401150644402ca003101481c0e013a1010100801d0506000030072134080a03c1070030800030f440399610f4a1b40e02c104415 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 905730539 1250 905729289 905729291
    0xc0a0e120d140f030415050a06030c06050d02130801060509150a140102010b040c021b030703050a0b22050a030f052107030b1c02100503041502030a02040b13030605012304 75
    0xb00c00200090800c80f41c5070448141950b84d40c4c500360908140d0281d100360f952800310714000c00103500850038400d010503250b01c4079108840c28030303141007160507422904480041c15030030024403038140e03040c042460050101c0c00001c94450710701420406000781c024402a044e440000a40c046c0796541e42d07698007078424010540658a00010041f40141448054a5001454001c01e1900290002020305500d01d02c801241289030001b4181510350b0041e10000b481540108441d000040d100c80900d076001101006a0700ca082d0361020820004d0040d64050701c2c4c6800a8042205056011340710065840841c10402c1c54081000c2c41c1060b0280c040c0c031401c8805420b5408182000d01c641c1000e0703420b26000301045581c2c45c0c030700010740341e17800100d4080f8468188c0d0400c0381c04071030294040d284502e400c10381e551200d0340d80c00340e01c00180d4401850181942e0b4200030100301da0101c04050881c44080b0300742842102c7c20341c5010300031035204ae042640e00d14500018210000c1200b520040c11007803d0324 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 905731789 1250 905730539 905730557
    0x10302071401090b010302030705010504030f02040b0f060f070302061513240803040521030301150203190f1103040b07080904090804180c0f0c12090e0c0a0e120d 71
    0x901081e8034040e2802020300d542018446818001214400e034181c900031002e8514140d918401560301c0d10680c400100055a03586140c8050314281d032080440c0407000d46142c0e41440450006099039201d010125001d00001c209030007419810080c007540445c041c000105840c4160340020b807400305107105480307110b03220040480d030680260103c00340c0103042211314004544410300e85403250090302803580940c001d00c031860802c405206600801d081400090f61843e400c10004102c0003003405010340c1503100270010343d0260302105022601c011f100d80e880d4001c3c10f80d00003006024078010b103501c0425074410b200500505510100b118041580104469030780c0c02d0500104010301100107024008900c041800100e0380030900d0002102d140300d06003004a1900010140d800b01079001415000034078021101d00000c21441c881c0c041d00e070150820a810740d550309070040000d0000c50340f0080221001c101d003000c0d260000002541c50034211031001c0c009110002d8560f40d101140d041504200360b4071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 905733039 1250 905731789 905731793
    0x4050403030f02040b1b070501140a021f0501080c09062101060801090f0203100e03090906120601090e070e0c0d020318030d1424010503070504080123010f0f0501030207 74
    0x680b0001c030010b0011010b544031035940c00503041680202030006900b0f000d84a510515102c003003103160699505031034000c0c0c5a541403158804c1030f004000010300390300c02d0b1803a256100c41c04000220b0000c40101c404184c96040c19080b50801c030541e6050703400b6004490900820359a10105c600d098981c07000e407203401c2444220500d015005ca90300c02416035107040400c6090041403441c42c44028000d60880390721301004023080c800c4440240026090b5041408504030f540f071302400c100d4000340010a00000c0500d0a021203060150030b91007500c1503070307a810f00c62000100a009450090801700980c1003d480d0643e4121514401d5291070038103103600200182c2d070251031002d00b1800d1029003080b80e071200c3c1f45600c1100146041d01d0b004a0030720741180011910400c8840303944615071404512805001c220005454941018054005004c000d00010076246424814100c1e50681c0c0c91401e0729036000304012840710340e4183c011640d0000e40d01c00910030301d4814030301c40c01164070a01c3d005039546454 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 905734289 1250 905733039 905733041
    0x2030c010f14040e0106080601020615040213180516050901020703140a081902011b0e0d0c08030a170c090108130f06020a0c06290607050a0503071401060e150405040303 74
    0x2c1d0700d1040302840200c1c01269510300190f56a040c0c0350180c0396681da075280e03071005aa07110344c101c2d02601d80c2d007034041201629003800c0d001350001c054080141d00c010394441d000c40007042c02d5104100c075041d40c1c490410083c91003031501c80e544107030b003420f10714540107240000039190481c0c3e0001802c102d00e0451850802d0004110141c29141c05c640f1258070f03402c08452620100c484600c4101c01503003019001c580e02c54180404040540c5191259a81880c20806214075075440340300039984844118000100148280010b00182c0d046a41d0b583d070410202c8150401d070800901449180b00c000c2c04030080d96600820302d0b40e00114842078564200c030403440d240001e18001c0740000d00042c000301d0340c0217400390006c61141400348a040305020007094469131410f40a8100d5030018404220508034a15003840401403180c1c0c2e0041c01902d805c0a01601c403030740303594003070304017200d0380c030b01c00d042038450000c082c4117a401400e6104050707241420180d01d5a107920a00b150014400c540c1c4e000410308050007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 905735539 1250 905734289 905734307
    0x3061c1109040c030501050c040b0712020f030c010212010b07020d031d03030a0906110a0809040902010908190201080f01180203360d1107120512070b0a0c0c02030c010f 74
    0x300811420709481c06241002d09103810744011146503080c8004204a000d204040e941503c419888490400c04e8070b4035440d44840d040280d40b425030240c1d02014603501c00500007010101659400540d03191703c0910941201030050340104030f1584180024070050b958010300300300468251502c10004403000d0703182c901080046a1683c1d1610000852404141d044841402110701c0c6454150489510300350403600c507242d02a000f0b000c0030040040d60f45030314040c0d0002107118018540011020380754240c0d1450515080c10035114401c29070030365030466910040d01075010548c07055200044d490280750f0040a1300199418041039000700020b0324a902e510017801c1d40007c4854440d950104010380b0101002000b11080c0807030154045626005024142d0039400c0c15102c001410100d103071800180140c0c00c0c000301120f0a0040c2100521b0140d100741c003401415004200c1a8242d05088180d5030484500341d9995060240148441000d40d038007088050920b1000e082c03103401c2d40140503040300d440c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 905736789 1250 905735539 905735573
    0x60c0c0f030f03031802010221120c0306090105030f0d0507140d0915030e0a02090a090b0f01080d03060302100309060f0612060509011b0c03031107051b040203061c 72
    0xc214800001400310301c05020207803a000f6201001080e10319207052040700c01d01072000c1e0141e804650034003a40d500c905102c05d40d200021200c1d80c00d040c010408120f0503082918001f40c02240407082c40710501c1d240031128010202140180310362100d0842907901c6a4140d00680140000030801c43d09010382c41000800e0400840b00ba41e40801d080c0300d01a022803114050803040d03108164081200368020705c00e4003981d103200390041c100c5000680c200140000b00a0460340740540f139020078000607800140c403501880c1d41c1244800c0ba5810118190300e0407010144234010141448420809602d0300748000e90040c04525011803c1784050130004054500d0001000e40d141ca01200011000098840d6400980c801d0030140280d441300302246003070302c0c032107503003103d00010700040ca00c0700c05d0140441c4500b4520034103002c00c000212050001c3c0f541c0149409803015081113803003d07151002c900080c0481d110443c0d0450560401e60041030000e9203c1103544d00d0300d401200c880050103403801030280606 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 905738039 1250 905736789 905736809
    0xf06151c050f0105010b041409061f1d04061a0901020a0b150906090c0306191d090114150607020a03120e18040f08070614070908070e010f060c0c 64
    0x9100707240095588410200d400c609510300300000c120500d41000301e0741228440006a55032004000030000c104101500d107950248241411610350b51019442500c1003c45458061041304120081424002403001080c8101d1a115083c030491040440c122840c00d0100700554459180c07a00603480c024440394080d050407011003c20401d03050b50018020807050596403501e09807202c40900010b0031050710b0104004205000190b82c9017003c91301540703050020541c40c902a80c0c1d80c21071070310700408441840d040580080400202003024001d01440b4003160303422001514005801c171035006004450a0310507a03001801d0f406640e43c1c00d0b0600084c40d0401402c076440e11100b40c0150014844401c880c3c09882810302c0d03400310409040c0350354405c0380c10105280d03280825507500d03225903114400850b80c080c2d980402d140280400d80403607104641c25201e2485480c18403060520303003840d9522444401b40f40d10010f1103002c2c400c0c00c0340d40c202c5009080001e40c400701803070840f5000c1031680000d5065 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 905739289 1250 905738039 905738089
    0xb0310140f120c010f0c0c090c1704060c0e060304050a1103030c010f0c090f12080d180b04052104030f030509060708092409101b050f0d020f0615 64
    0x4402d0104960100380c1090722400ea54076614141561406c1754480d0242410010702e170200107810094200c452a025585050894580207820492001030252401d0ba9015914440300c0f9441d41c2029810030031703c104840c12400c40c5495607030f01c1c1c1d444141c1035009200c15410510084262330030401c0d235042c4c01902d40203001d020710405c602d40051845220b0f12002903050740002a1072041040c0c03c0c07040c4c980e50300079071303800c842e8a494014095101104c809400340e9180300102c590000d035044290703542d110358000040c2e8201402c00625002c8240c0e0060004e490030304030b40302c80c6901c100440341141d500425001080c031003802d00f90f402e80178119840703030000700001d0010108041c1900074038001800310392600301c0114070814404004031001c40b54014030000c01880d041441c146010b1080a181d5180909042d00044950303509001102d0040700c0507880000350118010003403004802182c0c41d440186007000c080e0301c00c6070780d40b14058041106c2155007500c0351a41e40346c402c031041c1040310240018243c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 905740539 1250 905739289 905739319
    0x1b03050307091a272d1207090504080f07081c0605010c1103070314030307030507020c06041e210501050903070b0601081b1603020f0a0804060e032b090b0310140f 71
    0x181c039504020b800c1d021128152032032018038198019486c004440c01c0140f040a0070111040d00400d0043c0090302e2080090000c40030b0840c0d100300600c8518464421240c907100c0781401166550b40c0036110348922814004181b010366400704508600c280c2200002c88450158408281480c034182c0001d801d400007000040643d0800100650295507195420480380d9140c500032030316011005034941d4040e408000c100040a140d071000031500c94001a15031005035148680c201c4115014000c00200400c02c1060040c4802803140544c003600040c05145848000c1e0340707680ca040d04c0204550b0500c504880807a01101d040040300051000c8010610783c1ca046844085e034440403442c400306c0062040010141e00c2c0f40b00841e1a80da83c540c0320300031031300380703410440180c810f040440b480c01d4051151200c1404461540101e0a1540c0e14005c00c41100143d4000300400d8440c00c3c1d00b1140b1b01e09410030030b000c048400b01100c081200d030000c60710005c000ba004001842484400c0403183c0c07040e00c403800e441d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 905741789 1250 905740539 905740579
    0xa0e011704050618010203060a183309090503041e080a081305030c130e16091b080112080a0e0d060b011b02010801151b03050307091a27 60
    0x3c0a031404500c80b520600c1100c00315400e038070003120401e401030100300041101041c07a601c2594a64000b02012134800801c0c50050bc113000c00b9210501c0d40c400003007a40a15070ba40001c11006080140744c00e01c0702d00400d48500d503503803240703100d240c106503508041030804030441c09401019240300b40648200c0c03038090901011580000101c4d000c1c041440400254a140018004d02c044001500300303103c40178502155401040c404442700c40300e02880030f480d400c0c5040074041e000038002d000000164851004150030030b0f2131500203044e01380a20030300144400d1000d003421000195114561a80d0f0320350b1400111654000810303000e070095a0031000404214158202d96070f031100c02e030388404200c020000004031100380f01c1e0004c0d010a803044018405110714140070240d0403868140410015401d684206455038040070030b0700007502c00b00902072001e40c4410040e004281c16500e50324034054264502001c2d12516450b8049103d41d41c0d1003000641c0d60301ea01107017a0f500102440d20362284912015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 905743039 1250 905741789 905741791
    0x408151b071b050916120605030d0c3509060706061205010f061a070c0e01033e09070e1e010e030a031b11130608060702070602030a0e0117040506 64
    0x3074801282c016010030039051107902588514400c2c3c50403d0030403c3c2c0c4809a50501105280c014119107030000030074180c408003e0003030452034980e03540900f4138803400c0040090030205100c00890162001c03d102020130030940640740c8095100c1c0640d41c2080e080060348520440070020841da09211000030302138102d0321840c8030603001e40c0c0240840c10001e040c1c5002c44030280500340a81c54030b5141d14040705012409050100d02c204c648e0390000d40c51307003210311080b0400d070310442e589800c20241881110b50380e080c810020402082d0716008002100c0001e20103d2038400700f03406224110001b940640c8a10654111100302030700810b2140c0d1801c4201000e0440000500e01107004120300c0c1845007800103001200d01c0d003564600426821081e1704042114042c441500c1550442d14501400c1d516100364641c3d4000349440000c811340780a0340c45052101c006c1080042d500100c0d42040346540110485002503200d01d03007030074450030314401640c10010b4034441c603681070407542c100003c01000007105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 905744289 1250 905743039 905743073
    0x1b05120306040f0e03030c070204020915071e0201021903120c1d0a05090a090c180501030b060907022d01151d19050c12090a020a05060408151b07 64
    0x60107903012024003c0e06989810040c4501e0358010070004400c04108005011810710088c005132900002500003440710041c1152000c8044000030700300704128034864180e100c60b00c110300061020816400107501c0d640c8a1141401d443d00390300c200400c042c400c45400c030b55080803a500304803040183c5801044115000610017610f680002e13040c5d900c1c602043e4040841e100182503003141e40e100c10a420203000e04d0041151100c0c00e220010602e51180308120780403040481000174198510300703208803800c002a2055003d20621001d1042d0781c1e038049103184284000490354000c1440602201401050042180780a540780001d0780d16120000b0138020101c4040e072460703403450320a0040c0c00c207069406a541c0e05030f12056500e204100d44503a007025a00c40c00d80f1b40c819060620065440d2005001103030600100c6e0040e4a03144214902050071001800c01903c042c2d0401e820702010665840450551003003800c0c2420001d03142c201d0013001d081c2c4880c8901074041c2c60b0704207441d040015040017568 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 905745539 1250 905744289 905744291
    0x3120e060702061e0606070503130e160507020105030a05041113060e070201230709030f0f02031519050603030705030f0309070902070f020f0111030307020705130b090105011b0512030604 82
    0x704d41c1040c04003a2800d552407452904060310384804003001440e901c03041048030540402d012000c2e050104041140c01003402c56804039035890301e62400400d000002808c0c4003030220a00c654000f60740d0000035207600080701a0002104d40f40c9044c001c0f00741d0341a900e50399012501045100040129030440340849010310400e096030303200c2c190180e003602c6024204e86521441c00d908270b42030712441074086422007014100052030300e4407604c0b50448004211360503520000c50441860450808100090803034050b203121108a0030640c4980b80b00344020400114644d40f41c0c0080b81c12958140110703a10103a118045a07503e41c03442c0300000e25500202c0e80600180140c00001485520b58000c840d00300f40e004100707447d400c2d0301c0e50030080c3e007815138a003940c10864480351036007242c5420002140a03020540040c10329030b1404003000b4440c1481c64000305c4041c101039183c41d5a4803001200b80c1925824240442150002d404180f869040144060710070301c02c2500c401030744c51310b41700210301409007514 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 905746789 1250 905745539 905745541
    0xa0e0d0518042d060905010f050102060912040b0706021215031902010f1209050a03120b01031a060f0f0703090e0106080421020a0b0f1005030d05040603020703120e06070206 76
    0xc1000300c1d0001080c500c2402e005010043c08034426071069924110005400a0032070380f00c50340b28003190800d802c000341000040005021540c2c041108643c05801a00140084104039030034605a025900c140c90000c0741c08a803000c200b0035160103a07221001c1045041409203003000000150030204102c090081c00359140c0d0b181e00014031111403161503011b03190f2090400703040d1800c65440201041200e84990f49464032070010384144000010030303000fa40c0e0004004034650f01c075011645100c03205da051518062004041d00700380f03000d42d05101e0003107600301d840d0012809001c07071601c2068007030303020072000090b048105a08043c40d032054804fd80c03107100340c9030703256602510741c904192405041a0342d115107603c5c900d500030002e440710030450b20586560720410380c1d030b040300020156162004040460200f011500300f2919190017004110000c0c66046042c1d04050024829030050a0406800049010902d40500c0c100c40301c0c4100f400f410400344103041d11103500d90400303440507801409800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 905748039 1250 905746789 905746837
    0x903070e19050903070512031509070f030605032407050f0d0504050d0f051b0c030703031706040b090f04020d150b010f02031306230f0301060e011b0b0a0e0d05 70
    0x1045c4c9101c9a800300061501440102c1c0c582e400d5003009200b400d4011440a00c10000d40701c82044602502c41b036150101c0c40200084003800b5150079400c141d0080d8001003950350084000c0008601d8114003945421140c1c03a158001c031028407410302140d4001500080c0b03000d190485920881c8154000d9007a07075155080c0c414111400440c00d540b45000450910403511440c900081c0c9091051080088880070001304010070b041c05900c0d881940070804a41d1895260000741800652000d4100c8040113810600d40c0054010400034202010030040d05000408545031618a04006c03a00100c04c00505810b0002090180c5843c1c164140004d0700c010042e010782b40000255000090300c15800001c0e03605104045542a401624888048602c1e42021100540c0c0800420400000c00c210642e2981005d40180513400e0058185042108110b020395150f200054003110241d0307c101d0f04015a1a841140310103070500c3d010f000305501424144940392600000205440c2000104d100b03202300b134076 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 905749289 1250 905748039 905748043
    0x1e0b040b090105040c030e010c090806060d05060f18010f06080c0f060a031107060e06040b130c180e010e160806040203030a0305040327090609200903070e190509 71
    0x21a69aa003248081d4018845413825400031513201d0003900e0b0009600700300701c03103880c2940c4041c00c060000c00c141074020300c032891051143e1076100c042a5019a10710505969155a552008000e484140d8880e4003003512104180400c040b00e940c100c0007400a404000d49a0b0014113007480b56442c9031040c0c2c000c1d95006d04090320072080041c0010220342c100740d41d0007800d90241c43e580744a00700c200030400000340015140e22862181802d030f640185020b20f080d14055900020241110190580403000703500040e000700d40e464280c4100151404a0300d0403a440c1c4000b80c1a81d01564040d0350a0059840c00328000141e016280460040107250b00d03a91244600c4d12400e0a40d80a90140c00805c50002c42d2402500700350740141c800c1c908040117420162401120010450b4405a042594001041411039500401000d4007500404003c1d0548075114148550b00b0007014200021740892502e1065405020324001400e03680d1100710b02d4030f011888402044c031001c0115100e240382c030700070403040000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 905750539 1250 905749289 905749301
    0x303011508070c150b04021b0d020a0f030f0e032a040b06030406051b04030b09010506011715040e010f0b100e060403080c07090f092f040504080d1e0b04 67
    0x429142c8050601d1651038010756195603129190003145c0350a0844202d44031403008201d40740c00c00000040c441000721001c0d0801c41480306100441d805503140300c000c200008034910f021341d4181008404010a080d066400680310716800d549030081c1d0002d0105682005030810030414500f1000030b00d08000e2040001701d41005500e26040001840000c0002d8421307404603070414040380c014a003424a040c0d04207074a51058004441a422950500038041000d0140d0341d0004002d00b081c90340e0000c1d01254082d601c400074848801c000ea40c8440715070a0f182c41c1e003d0b10618030000024410005200881c0010308904040d4078000d081650500d400c440c82502d03440d000c1080101024a0b02c0d2460f00c80c101590017030b402209680c0282400098241028810080115041640031884031a58240000301c1c0c12810010901d440b0500a11160410f0100000c2442c1c50119400a113944480c18456214040c06c1e4003103026602d0328032000003214407050030283e0007040306014013142c00c142041c0416540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 905751789 1250 905750539 905750551
    0x7050405072316031805042301090614010507020f0a150207090e1c1106100303120509060610090807170d0314040303020c012318070e0a0c0c0b090303011508 69
    0x185220f010002403190020400d110321649500ea4465155400502120014840c1203107000c0d96000d486541c0550701c00d018014801e65004004070751030951700c030a4001400703007040d04102c40000c0d480c00315901c20144041980004e008912840d80300e00030040030181e02003080c40988030b8401e00151610b0680030325a801407111015080b0108d01a8801d6924011416200e0510504e043c0c1c110450b642001503511402280150104491440c14013070311800303603846400f1000742007004014200b00000707103154000c94161407140c8009245c0800b01c40500c65908518a40e0183d0640000d4000c1c7c2d8178000111090480203030744041c004100203501f298005011a00141d5110b400103001c01e000e43e006c2c01a00e61004e0000c0380034051601040402140c0d640352020300b569031000c0c40f202c13040b0341c0d2040c2002003411005250301c07414144801d4216000404074030f0081c0e2510b0082204030310484244050315030001e48001142844508662290000d0041c05400541150300c090300502c1901b0f407900880d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 905753039 1250 905751789 905751817
    0x8010e0c0d0f021c06050106030608030901140901051e0c01150f1a25060e0a03081f030c03050a030315031a0a0e071707060e090c0903070504050723 65
    0x101d540c0d60319440400b248400782c0c0e10001400b00009020400640c010740d0901c1010002100d604100d00a411079803540c200903525032081c400c03941c150b600300b480300412141d4822020384070018440102c90301d100d00550282140010f0300c0c1c0c075090030300003c080c0c852100104001e0107490600c5000d05000c3c0030364400c2100c00d0496080420210700d801c20086019060580c203d0b1900d200c0954450a030404c0441d01e001c00d1044107501d00901c03004d4072642d2000045600501071509040e14003c2030603401400c0c0c0c00c0d040c543e45003150391550000c0c0c0d011009542c03022000d0f0300c20395203080c0180c6078407070f00300300380c0200c2d040c140c65020000c0017001070001d0b2580010303080050503504c40005c0704c0c0003004004000303071a0380700300813480b00d00108121402010244a080704901d005100d542c1880d020368400c07820301903491014000c5640b0410041d502c01035528090f0384420800303000a2602041d40e01080c1c01c01d01c1c041c24444003a5005800e041e9aa001c01d01f031029211510000034218030880d144c0500c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 905754289 1250 905753039 905753059
    0x22803020306150a1404150807030203010f140d06090305180303070c0b070516080c04110a081927020319030e0103150305060f01081204120206030408210108010e0c 72
    0x50039000d0100c212042c0740c5510305e90f01040303034240c0a61081d00a5058408407051381c500150f40041c0c01c030b501028502d4150705651611210354104c1d0001e0159112803101100e4184c07082c0c0f962460800e0150700320505000800303c0d4100549aa44003095a056400841144030300c107060002c1140c010580c4151035507841d43c41c02040180540001c00115428000c0c0d0350a680322540303000503c1e0103850180c01a02e0f0403001801004100e40c6d034031b025490b60240078001c1c2004e450704040d0f0107a104419440d441448015028000014240f007060050040d60440350568070b1052200103181c024801d42c00c1702d0003c540c0d01c3d0044281c0d9601c00c0c1c006c0000d5111080b040c0a9403080d0002100c0300c000450144165440740d84407414580c04407019858006080010007440c94100701e9070b4248807401c0c46040c82e2905185106080d100d4400c2c01a0252000102080810401e04101c445c02000c069100c8120020754a00c20560301d002e20511074290300303246000180150104280c40c12000042c119814 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 905755395 1106 905754289 905754319
    0xc0807080c040509070302150d0501061e030216031b0209010806100512030403200405070903150c1e02030405180f010b0f1803070801022803020306 65
    0x1040f801c00c0140002050013040c803006403078050304c010312091020140c5d4031071442070540c4110300714a01000002e001d50f200d1000542c014012400b94804101002e084059000d0f154213085101000101c8400181c0102c240c3e007400314641d502a0006605600000c03d400300c242c0c042e4005802120801038810408040c00d00540402c4801c030b05520034800c00741d0f5483c080ea00008100002e81d0034600b80005001043e80344c0d01000420500c0207190007a001000b055442c0f200700d45141c000b14000d60011064044c0d192040b103141e036030303152202c010300218509454007020700d800d40c001044085400e4542901d00e00100350350003511882c038180310082012480307050303004a04000052200740b405100d040216621050030042c1114013030707030400000f0700b044116808140250720026110302c1c81c907412641302c5030404230f29940005211541d00140c05a1000300d800710b900440026010302 = true := by decide +kernel

theorem cover : BRFrame.Cov 905575539 905755395 := by
  have h0 := BRFrame.cov_init 905575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 905575539 ≤ n) (h2 : n < 905755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
