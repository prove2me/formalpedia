-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3412
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:35:12.042556+00:00
-- url     : https://prove2.me/submissions/7a518e70-3eea-403e-be17-2f697cc21377

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 613489208 ≤ n < 613669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 613490458 1250 613489208 613489223
    0x140d0f050703081b0309160f030f030507030e060c070302040605120a020108090c060d020406020d090f06180e0c030603060a0b0121020705010f061406121b0f03010b1305041b1805040504 81
    0x101c0b445601e0b82d988200240b0120b40ca0342e40c0146141c403010203103220392032b020f818003100107a00030825206404032100c0f04401000310351105072080c10543c0c0e5202c0f90008038000d030718244000c560362628400c403140c0944404002c00d00e03808240e004591740714025005407980d11482ca081c4c14540d40740340180143d6070308800c0068880f450188020318cc0070750414000140b104800701840703020411210b0038140e52040c20100061294110100b030a0500d80e4800341100224401380010f00303240e04001c602844e4101d04840380c40e2a00c070440b2086540f950245030202d44c803040c5006403020309a91701d503000013481c1401403d00c500341d1540e07420b40c0e401134500003801c0c0c2e07140d00620020742034450840000105480090130092480081c04451201800e9070510030300c414446180120311000300e5099408e0790708059140c1d6503491051070780340c101c2d92003509440404000030889080611403050061056810152a4201000f00381d4181361005a0103034010f070070700d10110710703500c9a0241da4000c40c420b003030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 613491708 1250 613490458 613490473
    0x70308040b01120201090e090f07120b01060810120204110334140d02090d03120f05160806120a05030702030f0705010f110c0d140d0f050703081b0309 66
    0x1840180c010050304483c0d0b03001a052044400740c2d038841056001c0e60807491168038940c403107244003031811010030303003003001441070810110346d240e6521a42000f007072061040f404549d03210707401554010345c00c0b40c07840c0d81c0031400c14082103400e100c400f90000b018005017001402c403514020125096008079150f1058461401d83c0c002e172100481403400720b440c254000d90560303107058a40140001c0b14500741c0d03100d4003000705410034003c3e1541d044608a1600400c0c01d50b00359010314001c3c001e80c0c1d041500310b88003807800c039403088000824040c0d00c0c42100005000c06138144001c406541603a4041d01c1150030540a9201860000c402c103d02500680658003c5888541610405182c48004812500c050b0004041041030766000440600a0007c5e400c1011410795440506031800d0b1080b252103a010243e041d02c0014003506002a498820140d0240e1301044a280b0041c2c03050700b0140701ca50300040c0c0800c443c0021070b1140d0740039a0000c616040b1030341c00381c0508000003030303641090b584031080d9000b608 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 613492958 1250 613491708 613491713
    0xf060f080a0b15030c0d08040e0f0a0e280c03060f14090307020f130e120304033e0703080a050a08011e060302030a1d0d020d0806060304060c110307030804 68
    0x8039869203c40c8514402e0310060015001c01d03154201001098000d42c40c010642c410058241c0c10307900501010792030343c03000f442c00c0c1845000b001e20640c0c00c0c280c0c40740380088035050844081402d40081c1901c003205510361644402c03546040008101c1503c2c4640c549002000003111801815040b00c01e1200c046030010403580e20302184030003e01034032404d5104115040068403003111001c59505d0440305140d04542010058014018000114101e40100f4102d030751000503400207540550f0107641ca03000e403031845080e03902c4140c0c401c54a18100c0b40054009681003141c2d01150107000500f02c0c140e882d0f40707640f95507640d031507003050f0170180104a000c034621046039400102d0b036005102c610310300440310b81c801e2840e174902180d6005040415800100080102e26a50000710740b20448200e038081c4c6100c06214252070718589840303580180103242c010315a40d84580381c1d0a01600000340000d00d580c589a4440340201700d0284000240109510090100041070015148480c000d0312040c80e2481c052 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 613494208 1250 613492958 613492973
    0x51e0d3c020d020c0f0312030601121b1209030207140418080d0b090c0304060c30050a020423010c0506010608091921140d020d0b06040305030d0f060f080a 68
    0x30316041c5c0140c40e62032012a0581d00015001801031075444c10656a032a00c02c0100d60b66190204000005400d0006002070240c91204401d030220031640e035010074581c108022400d46510b03010280040e0300040040c4110720100e4243c00c0c85210041001540521501075010f100b556200160350400000c10f0301c050a040ca0701540982d850111000070080c40e144882180780d002c0644041c10083d03445c80410002c5008072140d90b0640e03012007800074541c0d01c0380e6106091007130044016140a0404011031f25109542c02500c094903903070003001900407400c00360307040b00c0d001d407a158a04019200b203c00d00410414032200303010b440103584001c904e150455016190030442d01d0f00303610050700c1151300c60100780d074554182103010960040320007103400100c0c00c07140841001800f40e03000f4000a01a016622a9801820400d10314103007884525421801c0140e20f010300c2c071024045401c20403d050202e4511341c0078007200111401c000401d181caa200c072a0480c0e0290700302c803181c0c5e030242c0e400d0003d00c400b5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 613495458 1250 613494208 613494223
    0x62e0609210b040803040f0215070219050f0d02040f15030c0f0f0302120109020a060c02030c0901050607080d021c090302011811040209030f010504051e0d3c020d02 72
    0x1da01111208100a9950002880c402030026100e01c034003101107000c1050784007070544e01c0c0707400030f082c20860303648001480c4c1594840c9404a10540d0304030f4540b0003030fa00c40007600b011103100801210b400d044040034080040c0b0382100032a800750b540c42616403c20014400d1030b07405104c1c540b0300e06c007490440c6481c8444850f150130070f0010038100581000b603080144524400e40780c1c1030f1840540c0201000100d070142825040095000d01040c90104150303038001080415075000310119035000c403c0001340a00c0400038058a500a030041181101180d80c200041100c01c010710001440c110101403561049801e840410110350348070010201855424000c15200740b00000501440b1032060352031120f400380d80d0450f24007580d00412461419a014800c0450120383d51000b84014541131600944035802282001040304ca159031b0403c859800083e4001c44010948860451094000658503030442042403503002c00c14040012901e2010500c1303411000035142c0080c0409008500040d041c00e24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 613496708 1250 613495458 613495499
    0x30302120315060706021b0309131b030509280c14101112040f080d090305031c180501060801060503030f0702040b01030902090115030501140102062e0609 68
    0x3003441403000c407104041c040c4150b03000403100c5998a10b20b501c1d1540103402903202d283c030360240703030400c03020b000c10040018400d82004543e005405510792550008880c248641c007100351a50003807003095075000e640903940280e0800202d0303828a80000b542ca81100500c110201081d098208001c10008003060210140522200c05000c2401001c0401d58a050309090324040140305003070b00741780000038095410440c1d80c0c010016907580d111b802c154260a014441d8a000e48141b01d0805c07001c520912a8000b901d13484405145080204403800302c0041c4014100303051141e0300c01d0101c0d0041d180c0b01044544c1e500c6000040354852406c00c445003120380a50101c0e009410820058804201c0711301103a603c50b504840c001802c4401e800100c0013449400d4000350800c03810400814000b101e0a40c8050034030140d0b609208aa80f905040c0303142014000401d80542c0c8060045175015818002400c000c00e00140b9143d0036000200070b11500748021b13031100012450451045c00365901c2040d1180c202107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 613497958 1250 613496708 613496743
    0x2040b09070f0c060213060e0307050f13270b07021005071202130b0318060a02070b130510020a090501080f010302031e10060b09040b1206150d0b10030302 68
    0x50003010290802e00b02103401c10800554032594020824203505541c034820b000c8445600480e280d04000c0c10f50903600c5001807183c46181000109031902440c55210440054055002c030030307100c203203103000c0d080081c50701503100c400707003d400c689100c0601f01209207401195540064100b44a010b03050000c10782001150710f04201c208058950001610b8803050040c0d50016501c0c4014004040d0303049440e040f01ca0300742c000006108000702d604640c1f82040e446817090340c0003511280c1d607a504038428240018a82804217000488094214503d040c1c000c2c0034400303440100d451004030301e00f207900829656000c0307180713410240a075591003684241d111286000d004195410358002940c0c1f4001e40118010141402c0e090495406c1c0610404201a0a50409002c03060f11100b1480e440d405c1401c00c02d01591402020b40d4840c503012a5842c3c580e070100000c0d0140d030311b070254403500030300c1c0591045800c03019030111b0a00242c10201e685101e5801a01d000d000942181381c004c0c02c0c0702116075068400c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 613499208 1250 613497958 613497961
    0x80a0f0809070806132108060a08060f150105070f03031b0c0f141501080d0e190603050a020f030c03070e19060c031b030306080c0102070e040b180d020a02040b09 71
    0x12030700046081d08580035080d55000e05005c0e240031000840040591040721180c441d140e015242c000c1e0915004140c100e070030701b180e203466101050796000c04179a01d0720754545100116500c0c410558000c80c0e204030615015190206d143c94001642c000c42c401200041d986403040d9132003c0050700b01c0449804a4030b480345041c60a5107510441301141d180240615030405030740c03090043c0c02c000c00000b920495040781d0a039030303680c1040368441030866040700210780800402506450002d82909140c1142c0100c6480c141c00c08804600812004105009143d0300304288241c0c20004c001540c81080c00c1c0c00030654929020400800415404213034074000e0514240d20b12a07c09600c000e04242ca08901d0506401e1059040071101d4003207404400c221505110388000615506030014019100b19004407050103280e44012a6a40b00c10311916441c031b036800700420006003000c0c3c0d46030b4010014074a090b620a0090024500301822291224090b900041c4544210304190086403007811003101c207560705 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 613500458 1250 613499208 613499219
    0x3180803010b0d0219050901090e0408120403020f0307110a05030a08070602032a0d0506010e031b0321120a02180108041a130309081204050904030c080a0f080907 71
    0x2140418002e80d000314102140c040d09201e40e43e8160b50403ea0000761442c540a07003a240034190798030052070307540000e00040011600b1007611142e9805a68000c007402d250441003401300441401c05401101180188a81210303c0001000604481c5010703410784104c21119000b00098843c031903111034007175041000f040300070400480990700c916811510140c2e80c0d554074889001004000300d45070702c1031070036802c0321007210789050b020b003400f81c0180004200c40e481d1507006554060040c43c1180d03041c0d1010301d1150002d012116401103601000e012288001803d032001000e29119010ba441507140210300a003807240550109900715000c400214904040d0310300040003d450204060706010f042404241005500c00024036182040c40c05800c1a003842010a4242156402c0a800048207110082054400400c1410725900344c03520380c44c58079107844107100c0c030f401c4002d00c258280101040020013040e0b02c803000381520000c943d148034a2071510b0390701030700c00034000c1e154280a9000002c00d128 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 613501708 1250 613500458 613500473
    0x1011120c060a110327070306050105040507030522020409231006060f0e062a071406070f080d02071b210215090409060b10080702060705070f050318010318 68
    0x401412440c41c0b031200900e003121744150404c0d01c00c01004544a4030500000740303c00360740180d0513203204540600054031150021000d40e003040d14240c4a59800500e80101014011031f0b90b10381034030107800400c4040c81c40e01c0d800c24400b21070007000c007506d440080d5a40c0300182800300c400584000b0310f082001c64108280140014280c01c0b1100501190340150a1955100d03015243c102903031030b04642083c0b010040c0d42c1c0b40d50048112840380c1d8803803608007003001142d01910304103c0b40f0140c580350900b01c0d90b448590003c041c14009441880c1c2c100070305644861680000c02cbc1190007a2a4158081c1b150a0303c030052068075880040c00320781c0c21040c260b01440318000c041d48030b901100e481c4041400c1401904551003628031080e07100f40362020400030081f40da0800d801c045011a09103000e9041c8030800c1d9810442202e0b41070040e040f6070009500d090143d0060522503006000e07611214030581d440a24540c082d0745850710ba80c0108140340c42d43e41c0c0c076005a1104460303049038842107115980e03c841 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 613502958 1250 613501708 613501711
    0x90d020f06060d0606080d110106140607170405030f15070c1a0907051003060305190c03060c0e060304230304150302031e040f0c0515091011120c060a1103 68
    0x24401e1021200f020184a40e40d00a4030203001810140c424903c1c040d2009000c0104c280300d005055400c10000107003007628000510817100e8060241460a0550364524039100d44903810300b203210109003c04505a241000399828180100e0003c1c500915410120300c0604c50081c00c0c4000c00019001c0e04000038140070b40140344407000c05100d12140c0303580c80703924100950340d04400d40210310103107403030486681900f01400310b0b40200103a034100001031a07228203402d10144040e0002d04407101c1000002c800b0780c407003058901b079032030248081c622102c0003800d198420340d010b440e0031002c403204c03241c40808003201501001d0003600451030140341002510343d155940c1400360a25a010001422402000c54506d08c50780c0401e41618080c54540703841c1c02500700107001520804c2c80018003040c50b080c0007200c4480c000541100a0601c00f401d8204122544c50f1007082d0b04000559146105030101000840d68881c00044441e44a055440400e80751141c010711318001c0303e003440c6006c5403842412044030b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 613504208 1250 613502958 613502971
    0x9230f0706050a0809120c0102070c05060405010c0f11040501030609110907020d1d090709061206050906281410030b150702270a0f380409050303090d020f06 69
    0x4c01e09a0381c0c80100300d003030260f10354000f045404001804028158198010140507100f843d4002d030719502d40c0188503160190f8001d5078082040c2e06455030105001c2ca400701105c1d84560340803c40d456826011800751002a07104031009501c600344a003c10441920f80400003c1c241e070620540d19140400a68400441031315405204d6056190f07400780382e1500300311440c44d0001c0c00351409414040d200900ca6401d91003030b10300081560412280c101c880d030140c881203c50040480051340c480c08108802d2513603050300340c6041811441d490300d0301902400a580240020202c000254940c1e00a201009201101039800c0514220184c01c0556900c180e504984162848441e1500e00c140b002c80c90781e61542000034148000c100da103000500081260611400e6107007014841c806000e031850302176501e01c01107000c400c640403010082c1e81040c2d90102c910000d000c0b07140d03401c00c0031410228040300d0202100b562185c20000c10045156000c00a81d90090018401820340d131030000200d07600d445001e0020f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 613505458 1250 613504208 613504217
    0x190f09120b150102010209032505030609030307030209060c0114061e150705011104080703050c060c03180109120803220b01030b10050a12023a020409230f0706050a 72
    0xd03882c15901c00d50555a180401904540c120030f80340900c04100d07500c000440400a114a1001c60300c0d05010844500914840c001581580c40320710b000d4010350445900681c0140c8203000714210300509005020464024130011a41303410420240001122480b009031b05004c090420000561540b148500b80743e03403c201c0c00c0d030311801e00e071a0140c00751542001251031071360082004903011102041010403a4801c03c211404582d400d8107002480c05204144074450b0004c0c041039a04140d910441c1c141d800d0149840c101c8a5228130881e003228010030400c1d10103a1001c010403a80c0102d00903a90102e48816080c0010314465503944008000140801420329201401065031021030481d1031000d800d004205d24030b1f040c0c81d0840040c00b101d112070241e03c40c1c1040c000710120803140104450100303110040c84c403c1000a52004403102841150487c2c220756901c6207600400c00601c10b441c030084250301c905070a0307401c4001d010b2409150551903045904507040c06c00525810008688240e001e5041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 613506708 1250 613505458 613505491
    0x303110304170607260109050709050a06050a020106082113081f0f0e0601050f030f160501090605031012081303050609011d07030204020708190f09120b 67
    0x2005080d40602c1e80312240b4000030710701c09000703110080f41c22841140241d4a800200c505584220f42c0054005001141000b56900601c050180c03500010343c001414100952078a03556000b05180710b0003a4081000100c000c107036a03e11950a0040f00014103c1c4401050b010301900310740c2440443e14607119102860015010710820600c0011034010100c0c2400c0d01c500702e00c0c00e546400c490003522913074030b02245001d011954401d500d1090000c40143c86000b400a81c0c01c0105000a1a12140341c0d6a80740c450b00c034040081c40341c1001092039030f20000702009100d034602000580a1009038100b2018817006004001201103024030100031609021019080c8030035a0920100d907200b648a070441403400c070b040200600c180000c2240c06402e001c03001b0850ba000c1642c0440700140d1000c3c68070250b410051041002d41303415000340c11130354000ca01491920941456504420b010b42c802400031030000101d40801c0798020002c48018401e5501d0310303450701416130360300d20b23001c03401802810042003c40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 613507958 1250 613506708 613506737
    0x8090712052e0c02030a031116030f021f200307050f0f04170a031101020c0c040905010633141e09061206150403052a090c0319060602070303 62
    0x1150000e00748030b002c10800c540c000d0524001d40360f9022041d490046401c18460840202e80c80c0f00312041100d401c003580d842c803009a90210b4088113111103910451280200c001c46c1c0d0850100302e21041d1780e5a1000003030185140780f4000c03001410240c80700c6200e509104104031b80e50803404551201c45103140e031076a6001114806c40841c041d0b5006419109070a01c000941000001070f0b414210340030352900c0c2200c01d41d00c05010300380d100305000c2c040c05820200130501582069005070362800e11030b400100d6042d4403914115142040f21254031108580041494090148600903101281440c0740c1820344049000b040042482120500000b56201c142c842c403400c1c1c4104241e4111a000400d100e6403003841d4020f01110131010f13101c06124013035400c1190700c00100c050880c1c0490740c0c02000381400c0e81c0d03e00100180144503103804001030b864500e1854050b90b801400038411040c00e01031903100d00b400300c049811080c0070041c10301141e240c13000500c409a000541c1c041140d9252a04002d00b40808 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 613509208 1250 613507958 613508023
    0x3020a0c0810060f06050403020f040b040c0f030c08130809131107051207051504060609021b0f010b150d020d0e150703140609060d0b04030809071205 66
    0x10401808a084800d00070410040128440c8900490320905200703090300ca0703e0400e050415071180c8804a4020441000141400d903020362882c0c80061002810a0400c1d001c24103072441241d8040004504500505581e501441544810403107440c00c4101072500419010304407160000241036018040f55200459550150b51502c801a1074401d0244203044c00b040c00d01908088002c0340d2034090481c0940034600d524041c0d48403903400c00001c180c2203044020188180350b0190003540d84030386030304010651600500090403c0d10708607100c02c1c0205c0d201e8001d981481c0c4550259001641000780e000c80350341c5c0300e44d40c0c0e07416100d4080095656207294100b901c000e200d0984442c0c05c003400c10142c9120b0326000728012584414103e40121940e44414080303044071000c0084507101040d050211f1a035080180340e8940c02140a00000343c1002c04c0d455900210000310340440c00034081204101d40c4070300c18880c00000b401a03188542091013a5034425494070010f5181d040403440b600007611202a10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 613510458 1250 613509208 613509223
    0xa061101090606090c020f0a0804060305060607170304020a21020609010c02150a090e070f030f0e15010f0918021002010b060d05100b1c1a0414010306180f0308040302 73
    0x18030b0030480599116031380005082c0e0783c0340000c050b0190700907901b0035540200c1d0395101107611064039403400d42040c00640c028003015000640080c010f005520000c0c4421084d188284402d0b42d03120348074a03042c03040080503042d075081a031900c1c40c03150420300e405010031006030080d6030440ea0191200d0b8001c004036140c5090004c0a58081d480041050541054800a0a100c40c0302d40ea401503a50b207550441c0d20502050b81e044002032610b100b0106201d10a074050085034070944004104440c8104510346840051075904255212042c0100483c640c681024001020390810920000c0d280c040a10381840050f40c002c1d0066040d290103440303240c400c5d8009001948020400742d2110300324846a80100400c544001010090510105100c114401560f8614118150003070507081c0010700381d8064006001d04c0c49411541e848000c4190b50340c2e02510100392240d580c910740e5585142420710070b03581c080341000000d000c0b410713940c1d000c030355050140c2c3c03041c6416042c044103a4465203800c901d000c80c2c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 613511708 1250 613510458 613510463
    0x60c030403150b09010302031207210f0f230d09050628061a0711040f0b040f0522110306070e1207081c0306030f0b01030308070306050a06110109 64
    0xd012042044040d019a803610003030004010056602043c8040a0020302001e54140d0001800b515000e00c103000824046100364103131204021440000e041e0948607441d0080420303c007122070746d071042d800f02103109081640d25200c0d00900c518190341e40c000300000104018800001b600d03c8180407641c210300219903102c0202d404600e0241002c445401205c07010908001e280060f010991401d0b014210a40754508a40c0d092824823184041c020351010a08540c1745444d082c0c1c3c000ca41c1e480c1d201d401009100600045101001d08040004032a40c0b004060310ba41e00c1c0005220340360354414500e4221910320500308060314918148845012541d0340c40a501d8840c5c02c00308424207034400302c040100c1c8416540381e141400c4042013a1303114086030040c2d5440d54484108419005405810b001203200c140c1800281c140d2a522003203400e03d943c00c81a903501890200403c100344c1e01c200615481411441c04100c13850525001403258066803180380100000d00e604007024010a41c86215840ea = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 613512958 1250 613511708 613511713
    0x40c0e0604080c1206060f0603070c0b01080303062701060309150f06152c0a08070306140705030c1204060f0207060e06090c06030417130306060806100302010e040506060c 75
    0x75030300c1c80c400f55a00780b4104924080c40300343c50320b43c0000d540054098052035000300040d00740c2c02ca01c010720905400040000c000c0040502c01070012a1a010b5010301810b0003401540d903900e4030740144207005e0f001b002c00c225070a000442c21203c400d00040c445040d19424500410304804508040030b1000d401103080455625010008a00151560001e8101c85080e085071403400034103a0151081594020001410b881c0c05a92503041030072040d1300400d92030020200d00b5007640f10b010003403a10081b90001c44580f550784d60350024030411100102d51082d220720340b07549546071540380c00115008100000101c21030941c0030070704100050300000c0d0700220b50041152111050300b40580a0701450401c00c8541c0520404190325540202c2d0b00803000c10042c03d00c600d1a1103690710000301c0802d00a410f10400400e110312003421040010881c003c500420021a4a6051840107410a200503080c03040c200f442000810050741c015851403004a0103c0340041d041e50341c0c00c0820310a03c25581e5100b0344c0e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 613514208 1250 613512958 613512967
    0x303040f0b03010315020f03060d140f101805032d0a18090b0f060c010608010c050a020c0f010921080d0c03050a05132006120402190f05040c0e06 64
    0x40110080c41c100c0c0d0142a010604810085e04030040b40305803c02c5c14000142080040c019042400b0300204131841820b2251951004500403400c05060b5401c411058020800d005801c049030b00801e2013155007109104084100d668810b952407103007040d0060f030b1203102c0801c2c003036080344017000880030018014865079031a905100203200c0b0100d000000d0f1240750000707002c510b90009206000d00900007624104030700c001c88080084a8100115090301c0d07649a1401141d1f460f42030141038a540225114151900f02400c00a400c00c5c078580005401548000c103600038603a400403504040b07544e240003840f2020302501c1d00f0400505c03404006800e40e030000940c084610159440344615001c1580c0c10007094460350140b50540f00160350520703032402e0b509001800310300032004c40c0b80c454440c0d20b11455451202e8000ca641c64001007209040701341d080003040154204108a070143e500e624032600940c5042c0340c0c0341c1d6006074850203098001c980d21507045160b1070103844110354040006100c1078a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 613515458 1250 613514208 613514219
    0x3040e01061707030b0303030703090204090c09060302031009080d180f0506100806090c0f131406100201020304200d0c15020c0a03030912110415090507090e04110303040f 75
    0x1040210000d42c1400c2c1610800074110510038031485001d44001000356241d505c5010048001c0c201c2e003102664030598404002d00040c40d4600c0e071900421303144034040b407114614010182448060808500420700300107001000482400440304c0c41c180354a80090905140143d1184519003840001c010700948202d0714140701340041e51710700c1107000084451b1030984910086032601c1c4c0540344049213a011035210441440c00309604060200c001d040601d51000810015041e81d001c8130a902e1090000020f01c801810301505d18480d00728240020f618600f040c2e51000514094614003a412507900c0b500168990794400c6030705459a00403095401c03103074032004218540309441e15007502500c1103030b120032a1410200740200849405031160b5002c01d10300341d507200c0b0088000c0c1007242c51812002c840c001603650f030710810340d95000340f0b42109101c41c18070340c580f0115800030f4203680600c8041d000403c0b540800040281e071056024821030802c05030040070a2550040c3d4107c0b071510200a20702040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 613516708 1250 613515458 613515467
    0x60908071e0b100f030b0403030e03030109020d0c050403020f041e110c0106080c15090301020d09050d2723040e1b04051608090c090a0902010315061e0203040e0106 72
    0x1045005540500140e242c440b00b404a541c490f1145001c2940c0c0c000e01000406d8481d0000760340035000e07040102c0d0032307442490503a04540c030903082440341e143e0200360709480040500c50401098213a00b49145050b045030000b401c20310400b81424481c9885141d07940c0742e03c40450640700b0701080007005100c012040d1000d8211a045024003c120b5882c04400003010080041d00d0201034a002d800c06c032000c1c00c2c0d80712a45103503200e0034401e50503640810000e59041130301d20504e03000e180103c01400507902c500100801004800b820403406114a0f58009600c141125401044903815052645060034020049014480c2da6000c6a44285060842080300c8000b01e1305001c194603656002000e21a040308000c00c941c005e9405000c0c80604524013140b241c040c060150b000310401007141d1100c40e00c680010812031080300c00289031a2980d50030411941c25004100c041020320b400300c1025400c0c0840106a424a55501162501440107003010315000f41b080310050040180070f240c8030341e1601c60161 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 613517958 1250 613516708 613516763
    0xa11120903061005100c14070b03190605061801270e01081c03050415050403030e0c1503070e0a030510090b1503301303020f060307080406090807 64
    0x180070380500c200103583c43c12808680380035134000419902070080f0a040464034a0903007032044500090130103810b04040b104006404c0180008c8060580d6440c2507480c0034808100c40c010005290b007408400d00039980c58500b44c03804985402071b608541840e41c07004032041081142c1d00c0800c2d40481c92000349044088842c50262144d1381180309290740c4c0c4d481c84540d036103842c1e100c40d00141c03000c03078407c1440d074465000117810074016910a01110888a614000c984065600302d01103580c408000032040014451940b8103141125545201050014411500d00c0000e188c4410000300040300041c40c1c1e83c50501d10040c2d500042118015010500341e54020400d6070340a41d92001c1420004494501c0b41c04420014a0301402412480c0c44030800072600c0c0c0c940b8a400040c19500e07a13810341403d552140134014402c0c1080700030040034590300600040240052660740101410010002c008ea04001c20030f82155000400280c20540783c02d02000600944500815400c16095801215041c5d1400c00c0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 613519208 1250 613517958 613517977
    0x1090b01090602191e0b09010506091008071e120b041112030a0807020c033a020601170703020d0b0f010b131e09050103050a15140c0a1112 61
    0x501545034501a650f504618030350b481d840741203400901c0020050440781d1040d08017803a1175011076186550700a0191011a200740c002d03995030080002d50303d01516419008148070070b54090305801c2a103055201c411070301a20f4a200089402c3d40c0c041c0080c4c074290320040030000d0ba0400466450f28010502c804140d82c2900c6000740c0140c00e11440c81c010011050704c132131502c001d501c0c06100e44415991480e00401d4a410341c065a40d220115403414400b00401c1c8003140070108018402e14041076418110703819619024500d59440c944554001480c1c0d8151440c21480141508100408600e040305581000b50407803080401d001c100140d00887ca4000c41081c049400560b894282600c400d003d040c3d050591102d9601c410881c01b100788495200101d1400341c00403469440d030340d03804d0030360b08203030300448040c0e02190b149002d0104640325064282031124060005801740c09041c0d540c061302508001900700d002840100e954026080710645007400b00c196104604c034080d1100040d000380f00b16 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 613520458 1250 613519208 613519217
    0x5010f050603102705072301120c0c020a26010908070b040809040f0506012d0509060706020408210403020a0312020f150714130603020f041211180402031e03090901090b01 75
    0xc402c0302a4103420b6010042106030354141d020800082720b44084c24600d1070440c11b1025550890700980c0300c00d04400082c050707034482040c002d401040b805016609100c1d072280b903649805ca040c1c0008010300d0403112069005120340d611511142480341d00340c8030701480554010b19000140c2d2a01240d034101c68440c030030907280d81800190850154058194184032582c1455010141c0c5181380c0c010006030a5085000d0726031428090340d9599a0200d0b0b102c0e420240c0a503021040b400c003581e140840d4044411002092107050525507408114098040d01000b0801c0140e508000e40c00e906c2007141c2d0007400814001c4039824105603071005c24685c020384078000081c0640411108120342003080791203d04180c140b0841d400d10709001100250000000d40c0382d080b10030000060784091410301181124010b03002901124500c00800c8181c4032110300d031150b0645020200005030f40c010410b10303000e090300c500101010442c81e17030060441c41074400c01640075108000218602d07011754000c509070781c420781b03d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 613521708 1250 613520458 613520489
    0x10051203070b0118061208030108010507052811031303110301090c12051203070201050a051302060a200d05030108010c0203030f010303050f2505010f05060310270507 73
    0x24540303a1044a01c050841c0400b07000400403900404400303140c0c1082c418001038140d0f281d44409014410158081e2010440400180004042885107980000450a00c1c61900c1f854440302d200ba410813034034a43c0d1031440049608159409518000309104200c815207681c0c01c0ca00c800f202c1d00000d50300055460038510700c100105400e052046800258100103042404c80c5001050003407102d03d82c01c00c03103550090314030b014030f00c141407005036024040d41e03000401c042c03034005001c504583c1c3c010404004221401804005a00d496040354012540c41c81c0c10000103802c0800700c43c680b02c10b03c69948847c4600c001c21031055510a000e141a6a108030007400400c9031280200c0c1e99010640c2d02c02c03042e1071420010400240200300502e000d510188200342421450081a103160031003401c40d130f01014050b94074600300a07081c0300342d900b00c01e4807440030000707030a000e00401c1d43d400050303040040d0310340d441d000c50b1015040f1003400d0740c2084082d1744500202135145409a1140d0f805d1041c165200451751 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 613522958 1250 613521708 613521739
    0x50307030f0315050d080d020721050a050f0918010807030b1627030b07030e1c0f05092d010f0305060315330f0f0603270102031005 58
    0x501121a00903109603c0700b54140030411100c03e00200e401c90b203401c6d04100e841b030b01e04460700207000c3d514000c21001080071803c3d4003c0310b2441308008901f04200c000c004d03040c00c0b035410000ba51018402141c030141c80304c12040c04240b20b81c60359996140e51500350b00001900c4e00001030f9034401c0c2c178400d01340300d140382d00d5400d10700004c0010140c034280407402280f5400c0e034480b00d40c1704481d81c0048511a0010865603900c0f8a40f48500030354000000030f03140c800e0040c9a001c10410010500216242d00c41704140180d40142010000c03c1c1c4041000380000741d000c01551070907e102031081c4400c0714840003050078144c1100c091815800c1c00e005c44d140c1149040c0e01c0703000703128591007120007801400325800103526044294000801724005d0280c28411091030001000e40c00d01e0107140e4503c3c040c0081850001c014900c0b0503420141c1c4034000040740262562a810190f070b40085424a14107203404140305d404000d61743e2030004000540c4040308000c10300e41031541c00c5044413000d07500f8481c4042d045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 613524208 1250 613522958 613522961
    0x1d090f1f150f17071b140a1a07170a020c030d02040501090f14131404050601320d08070203190c0e04081c150603090c270b030a060504050307030f03 65
    0x2041509070440c883e0000074507590103443c11111030180101c070304101182503030b50406444800f14018881c4d621000381c407820001004641c410407031422000200c00c1c50407940c02081600203410b5081314484200c04900402c40c1d81e01600e1007145400240e81c1c551130721003010390003504075200300382c002440620001005100383d03c403e0155440c00c400c4d0002041000b050003201603451640100341c540d03502c40090f41a6200c43e0301c0d80140e1280000d05051b5241c000e0315841d03008440c1a4050032810b0b440d1159142060b601c55403a800f100381c0701c8040e0004d890901314941e0085e80006034040c0214846190611400a01c195500e80300c0d4100c1001d0075243c090041150381700325001042c12101300007501d80c1d01280c20103024071044000012842d400d06041100311015250722200120381c4640c0d0b08001c2001200800c4054154070402211031810240b20b40120110440a010740c0c0d5518280c1440d40e4609009243c1d90903040b044c140018106880c0090742c0e81d01400c030a800280694101040700c0b4800e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 613525458 1250 613524208 613524227
    0x14010b0d03090b0325030c0e030c0a060c050a05060f01030606080303192c1501080115121109070c05010c1404090e0c03120301061d090f1f150f 63
    0x564030041c2d89410b110b2020f62075800074150310900f010b041402124161641800103140b020b40d074000c50800a1508068500100d03628128400d070041c05225100303480c2c06200000311340880c43c0652400103541060f605060701108082c020f0b0003541d007008044902d40c031109040364803c41c410021642d8070000103890b8001039640c00b1590180300014008450746401c0080034801c001c0d8143d038000440944480b0565525848007440d8004250b40b109007409074140c070340184103502c000c0c07015120030181003900e4606c0c2c0c000c40d184808484807074814403c0044000001c2c070780291205500e0305010101070805084200112501e40c20311070000c034010700c1100144644002c03506040d0400f410070b0031460140c40c000d454030030b8520500701c4005095500b000750b54060718514803240d82d203505041e001001d00c0a01c004407049400e81c2040c1d040540c889064290b401200c240700d88201d40c4410400d02269480d0b60040d5092003001e080100c0d00700d18182c90304003444101c1e26203000d11003803060292480c009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 613526708 1250 613525458 613525463
    0x5010806010e011a0a180323010204080303040206030910110d061d06130f110403050f06090a0303090f0f0309091503020a031101031d0606011211031501020f0a14010b0d 74
    0x9920021640241382c520203052081c9190800307802441c508915400c50b40903030380c0180c0b4a07245d400c2da030080715612620b0301d00c90000b401c4000c0d4980340c00c1018041c0c1e6071101800090140c030000001610241d001e210080c40c1c566031040600503a020719030000d0706908014400e082542c0307010b10014400c607000b40003000781200000b4000450780c500301001203043c801c0c02c0b1450316549640300441c0d2082a840713071990710b114035448a5126401c5040642c42d00304054103011b155032000d03092000194002600803600c503818a000700d1801940e03c0c0600f5161409a801408612100d20003410180c00c00000070650700200010424031070403030300c1d603100d110b1644006500303c0f003041c1081c00801c00b0b08880700003010040c100032030000c10030141c060354804481c4052100c1c1d00070b14203001c4035692291801102c02440e18007445408541d002c4d0100c1440040c240380404240301c3e1080e03500d42d009104526804083c00103a961301601800c1410350040c1e0b0808035502940b030b00041080a2820b0410350110b181c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 613527958 1250 613526708 613526729
    0x908070308060306221b08300c030301030b040627061b090302040207050102130f0f0509010308040b0c1e03090406080f1c120f060504142203140a0305010806010e01 72
    0x142e910f8100c0c8411010100c2581b5110701c1101041038402084500214682541040c0410724136105600e010004840000c00710402042848140440041500c0c15a0b0304107084944903100e51504030002c14550806030600f01c202403c50142d25504140901c207136002d010306102800d00c40c0b0110030700381801290003020401c035600074000760a00e07034094040e0307034440d400061500320800008054160b1540c400c14882c0101c00303040c0441800044040000d180540d03a8140725411b56440705400c1c0158043c001541e54046000300001074200200685d0806100d00d000740551a40107184e140c2d8025400c850013642014000500340200103071154481203000d0283c07405400c259200f142d0010f031440442d08001e039200760003030110350b903200d40104d1000403603001401d039180c00c2c280415030301c40964124540c00450308101200d0a114808440b803001c2c4a88280b865556207006e4418642504d8140e079241004102800c0c09905948014142c4000b5021910b180e80d1302c03400e008030381d4400d01030001c071030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 613529208 1250 613527958 613528021
    0xf07120c02061305070815100e191a09040309150507021c0c031406190b03100b0102120301031518030e100e030d0206070f09030f1101030908070308060306 68
    0x2c0190019503c0e000e126609840c0d07603c1d964100c00d0724100c03542200c10200b01100341401001010406803600506800c0000c414624203020285400304128109a040949808181d20703000000b242110410300020300100c050b04050800901e03070083c41c00b50007000c0b468003e08000450003503041d516080d5000300f03840401c040f1524610300d0201d4000d001c0b641c0300b1160354088002240d05500710310039074115004000600e00354450201002d00701c1c503840c800ca454840800000c5d100071403030120314070101c1d50218040704001c0040341741c0022211004010100400003104103c0600c45600d00071410020500c129502a07000d001d00c105900402004241003035603106490070400507081e9125502d080104800e081a40880c1c10083d003002940010f0700200b00700007003950413600082c0c0a0380a4030304540c1c85400d560752902d0640726400040c1982d00100c1000c2042ea1003600400303441940300c45c0b40f40d2595694503002d40148401e54001e40300c1c2c0100000555119040b9207042040347c2d00e030040d000e54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 613530458 1250 613529208 613529221
    0x10060824130602070c060203190809030313080c0f0123060109030b06030a02120109020a150f05030a06031209210b0105090411040e1b1f0f12050f07120c0206 69
    0x800700600100c421503028000b0310085001d010703c1c8070007810990041c0daa280e043c81d00702c0f000e07072044100907024042c9000c00c1c0b252090b000002d9035880100c034094a010f800142c101101503002d9400416424460054440c000002c1074014103501c150901c14030614060894008011035821915140000c0282100b00082201e42992913080f2101500781da00c0310781d054010900030b0400344010300c2180c1d1103203d01c00860600b1800752008000844003030a81482c8607500914002408078100b04003e0013001241000c00158030020095900440d9030005071011075015080c007205108d41e503140b0001d20740c0076640742000601340300070319408406510380d41e003044200440d68102520550381d04a01e1940311500e80c491b03100c0c4645014620b001000121003e80707113551124141c0074001e001c1c02c5060060340065040b110044800c01c201d0519500410320803c04a8601c280b481460341000d04000c280480c01c4d5502c62403500800d10f80ea181c2901c03002400445080d40c10081c0b0032001a130102002882 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 613531708 1250 613530458 613530481
    0x70e1009060f1229070c1e022115091e030c07060f02151f12081801140a03051005011806050d0605030a06020928050f060c10060824 58
    0x55007901d4619141403480d02143d480194400c880c0340005c101040c0b14801440001e0007090b419015250b000701c80c10381123501086518200141c4c0c44080c5291154001c0880c03014402e818510710a02042105031a02d28442035456804000010f01d2891b8401d4070101020048202c50094201d04000c04000e0f203800e00c00c4440c182c0d8036290710114010303100300d550809200c3d0710540c0160580450010220304180110f81c1c0718482d680700360001000c4003001000a1214000c0c2d0785080d400c81a84140303940400b0050301c215600f404034010300b02c1c0015442a42c0c68059100c81d00685501d0383e49510030342c848005560300880b45500c4141240f010200700a0b980c400c000500a0402d42c901c003041140c1e90384003091034031503c820111070703441c4c002c12201c4903403d004500e480c0c99161030030255410a00074a9118243d4182d001d094000e44902034600c001e07440c1c10f8200c5549440001c101c59468292058500040966004120040c0a0a0300e00c1d991802688c1c0b8003d2400100c0903100c800e0f8498017406003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 613532958 1250 613531708 613531733
    0x3030e10030e0f10050901231503060c0a08010f05030a0615082b0c1212180b040302060c19080604090b0108150603061512070e1009060f12 61
    0x40805403100740c2011412028000f90482543c1440103100034110442c0043c00d8070380080c83c4d041182e00d000114081500d003c40c0781c035140030002c42070302c84a4451641e00100192250442034052044c041070250382401800200100318440e610018241d80310503041c2507800440c071034194541d000000f0503020032040c0d07101d00c1c0320030704c501469844190b071a4104d0742004a290210740403080f8071014004465030721841103000d00810b2803c1c8a0ba800130380c0d5030003a0040d44403092020050707641083c411005240e031108400600780c40d0001d551034494a00405001c40496046006005a00c040780c1810081c50076151020350700707407080b01121880c08040b0781000000708601d600648840284c0e003c651348840c0786010b040d01c030000d040940c4003650500c202c240040e1880b4041d600c20b4082050801c40e8108089110340f040342c40000103c65035a03a10300e0001aa0840e40c10307040100d00307020601351110110012900c10f940f0a01c501542d508248000060b030703105d0301d8045014000c00c440004c04880184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 613534208 1250 613532958 613532989
    0x50d0b04110f030f01060815070c14010906020f0306100f0210150e0106020304150908030319091a0106030e071505090a09060e010f1202150c0c0301021c140103030e 72
    0x50382e503008907038002440c01a403990108600e175510364003880300300c0003804850b1003003a554800c060503040c030300740c01000c0c1074501c1d502901d070b120f108007820b007030080079004001c140d50412000c0d520f500c0c0c800502d00c920b5000b50f4446100720b08036004900c0e8107000740302d074020244254000d4090750700180c0c03285000d4010a000d00304180c01100020440200c00c4180340e0203010564011520746040071038070f840c010365500e404814048443c404000c4c201c2c2c0002140c0c1c0c401044004002c069490701220005407041020081c142a0f81083c81070303110380310305081c50480c0c5495800340180068814501d440e041103008042c10407104800e91584940200001c110240d8041c105102d1240e50748488003c03140c25400100d0301d20f090748010400300d1100040080a00705a03116524185060703070000f42c0000ba07540d001841200c0204004044080078420520743c0c0c08050001d6580c0c2868002a4800a20002030b0f1100b40389000c100e9154507074a0354140e810799038552500540b6000720802c0140124141106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 613535458 1250 613534208 613534219
    0x5070630020d0b060c0109051e0307110a15020105070210140a0b06070c1d070f0f0809070803040909140f070b0d230604050a020c0c060906091005030f01050d0b0411 72
    0x444685840d402e00170480c1100c50f0000045101d01850729034204070700001d4115101d6010401005200ea0201c2195a0507a000c00b44481d03c052036000304241004070b5122560024200b0b0311000926010740145210b08200c0d800d4910181e01c2130940700440741c0301c8020581d10745841c4002190005550300220185034004d062505048156a0341b500440341074014050400300305e690200f06c05108403005400207064104003541c643c9070a401040b041582005d403040000e103801040c031540041c0a0500548004c0043c0c170b41e11500d454104000e0b0081303100c01c4584500035030030a80e0072000070901c1801c10000d940a00b4a4038035040181c183c540200740300f1041103985070300c0030880d044030810251249002e981c030f030400380c90064200000c459001b44123901d85c1c2d00400007181c0c04000450194064142180c003652a03c94500200e4964007501c0c02050700241000e03109143c50b504640039620030020019914856a2038209102d02c0c1d000300070008045094007004180021401544004501400303084d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 613536708 1250 613535458 613535471
    0x31505150a0c17031807060813110111010509010c080108030a050f071b030b0403020607020a0c05190f06020303180a03020303011205010b030d0e131a091e0405070630020d 75
    0xe00f4200d500642d0050084410020205440002800000010199420030b40010b1504010200d1002034071200104044070703a60401c034142e0302032072415034258030100080050b4584200d045000340802103402c0045014039000082062001040714800e203844d07034415061010580544110380c11049040340e1031003401c48205180e00021040c04025801603500c0d0081c2e040500740681450300180c014030454210200c01070105103500b18142c1241c0c4140d41c25200d445420300001808105c0b80c1240c0c0300c0701c451000c005003450740003010754020120f21386000014003070054040d03a10f480040c4000d008d60000e10041018408064150390700138092000812400143c40c00a41040d50b0904030001040c450b403410351107414100d413420410400c1e107a0400c04c4d102e440b481c41a013414000300c0903102e0501c81c000903c1204618120700c41100f0b21362003c100e0350410780390203a1502d015000e0500050400c2c80c3d00414018002a40d221908064220b03180d90850300601002030343c4401048841c0c1500c0b42c2c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 613537958 1250 613536708 613536743
    0x5060a080a0b04110105090306010e0a090605010320271306020d050109051305070308180d14064c12020906100816031506031505150a0c 60
    0x152801502c0380d42401000d2078141307820b400d9140091661410040300740015807080c2c50000391103055404080500d040342c2c3ea4100304001070011400002c1145043c84000401c00072140c54030740100c42c4800a03a140b40c034407502800f031195003414143d050405c1140e0404c5a0101c0e8400c895046840c6450003c002c0740315882b03000036a400a1a956070ba0355603070004205c1180c49102d40e94000e54181c0503066000e109458040d42e40342c0a000141c8813000009a4011403c4200d020041440010304803e12441c01d42c24446204001c08503416514060400080d071700ca800748103080508561480d036803c04201010021540a4034040250b20351001d500034140140000e034101c00050000340d49003509040030b84184405007102030300841c010344070b183c0309882d0550032914850780480045a40b1030100300040341140a030520300321484001e034030400003241b420b9260700b00760403801c044214002410f940e07000303204040c402e9040d0024480018018280b80912903280500c1c6a40509241c1c004c038501176 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 613539208 1250 613537958 613537963
    0x4180b0303070825020a0e0612010606020307020f04090c08030a03150f1403010905030d090507090207020a1a0d0c0c0302060601022b090509090d140304020a030f0302010f092a0f0905060a08 83
    0x25000403607c1035508040114a20346032210801e2507010100a02045250a0300a503580c041c4010082c4102c6040400c14800d45640d8003010001d038018000b094120703920b080c1079890307904c60154140083d0400603142003007544802d20600b16034114800c03e03040d500d08058000d4000540810a80c10754a410f0501c0106100700040c10000c50201d00005452206151481c94600303a0b40c4003c07400c50041c800d21000d41c2e105500030341103468100301c1c8a9110a220340207202d81c4a100c601140d90351030b010750f480009130322040500345144650201c42c1280c43c3c5000582c3d49200e105101e8200c891034840b40c0803c01c0c0030341410449100c003410805c10ba40e884800207807004208551140c0c2c0d69020b0b008520700d0560000404808150307165a2600e541030603008115440003d01010742052010388103901094400d500a00541c13032803d008000721001c918200c004410b0a0b50703260344884000802c401015401890030003143c5048245804962170040940c000c0e20f0000d0160b41d0000c1d070a0400103903100c0c02d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 613540458 1250 613539208 613539229
    0x120204080d0503060117093a180f09022104020916020304090911150c060106050702130c030905070602030406020c1315060305221203050a060b04180b030307082502 72
    0xc00c01514500f440070400c8001c03411141499103a41044928234299048800c10981b2006050b00d07050710003003011200482005903641c80040000c080c064005100280c40d80600400500307245200030b020789401191000300c0056502960010080c800f14461104000d011005003840c0d0040d02d00b043c0da50f0511608540d444c0300b05903840c0001010b801010f10b060200c98042d01140c444250070003498000b15652120140240301c240b060009400b025036640401e05180e80340805024401000e44c00c60090140100407801c980904c9203100c04903020380003209850995000b58020040c81c84040201f01047c20118120000f1a94403032900c03541001c40da160101a1003191400f003014240818070180611a0741503030340d184080801002c0c0014907200c4190f40d40302c66881c0200d45c0e81c54001c101001440280e01400556100003000190400c41f840030760325580b500c40041011003050000d01da01c902c20010000c01d5040104841c59031014492404035840149103040140099194041101e01c6030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 613541708 1250 613540458 613540471
    0xd021c030c05011103040515040c0b0c0f0c01020c0114161e0515070c08030403020f0313090b0405040305030105220c110606010f020d0e040207020d080307120204080d0503060117 78
    0x101c000d5a001d02c002401000400c0e15000207061562400c3d4a54a88840944a11440051041780072500b0b120341c9403030480150141c1d00406175220b02c0c0098071603480d824519056458040e64a8403038166001180d000100031040c0c540c6000401c646103a07400d9030b40040080c01008100900c02e502141310081020900700b41c681c03a60040708001d042c0217260940d4600d0040104250070208000b039a03010191882c043d601004090300ca4540c0d00e4140e09106003803407042c03641c0c88046010740010000301c00030012140719102c204200b446030800d2009480040b10040c002c03520410041266060260780c03070481408401000100c00e0354506600140d03031a9548120015202801d80c510b0403406100c45a0014800d090aa03185850910082e40340c60f400c0c07034900b051115420000060381c0f80e5030105c44101d07a00420f0000c100249250501ca0340c0c20650b050000103000443c4008072180c0d510842d0256008403000f0143c05402c8002200e403075000030700881c10000014401400c0c24280c459040c000e82 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 613542958 1250 613541708 613541717
    0x10216152f0601182a051e040f06020c0a150212030109140c030f1602010e0f03040303080612100f06170d0e012c1503040b060a05011403060d021c03 65
    0x14507014141c0c880d1440313401514440303442c0c4074115010354429010b140b626140380141d03108100c1a01816141405080140e0b51503640c2251691654041c00c40240151084860301d0230315182c9518089079a4140d0103001500085000410b0241800d110050003040086104441c0015500c0102a5961300283e00091545403070344841d6202c5011041620381c40f1109486060540c5024502c48159140c05046950b034030003502c030321040707040c802e403c00b690440c6c201c403c8601c2c01c841034802e19501d03801444217500150302400820000e24210200c1012995900002c01840207000380600050403400b40e005c502c43d0340c40d41c0015003040203041001e0000300207001382000c4d40f07200310042c08240b03110719078034104a444002e409640343c1150846489540e44289070080310703141300104000010b0070086920010001c020801003288a24001d4802c0700265009564503607594015525031750a207400802524003440082d41c02e00341202d5003140a4001400741d4400c070100101401c5640039075400b42c0008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 613544208 1250 613542958 613542961
    0x1f021c0b040b010309030c02120f0f0618010603030507030518040c03150902132c090607030c02060606030711070b0d0b010207051203030606031b0d0506010216152f06 73
    0x51800d84503400030b0b000d080c203080c0901c1d1100d5130b0061129429147c002d21500b10030384400480b402c10003111107200c40d548102d6010101c03541c0d041b40c0c0e41800b2a220406e03240040030b009800f10741801850112940764030b8441c01c01e010390750207031119084140b0390091015000e03080e22065689000e81b150010750b98900041000546100001011854000b14121070041108007400100c11071200111100c8401c41d092004503036003d40700c0d240c0341000c0b8412241d02401071094000000c41ea4500820320382d00c0401a8001a0b0401d0b6100e05080b81c5440e48100e0a1000800c1c0c2e030300486100503e05502c900f03640c40c26403501c2060095030024522050b03215658003a08486580411040c400391000b111001900d02c8080700140e524800113001e540109008808248115021086400d4040c20100825180d1075903046150040804850860052041101c00008261194022019a000041c00110204201100340c441206000c1d6a24000b40d0611450f1244455820380d6180004c4010161165 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 613545458 1250 613544208 613544231
    0x50d120515030601060e010309020306013807080c0c09180115081e030d02040b12010506070b1b04050a030b10080d020d03050601091e03020910081f021c 67
    0x220303040144000c100307036496489441c6035640010103034115502440e101c5000540000100c000e0901e408000303415104000020446000c400c103280580100c2080401c0b5080084000c25207664441c5040b20850700100460750200e00e001c001000e400b002d600448080282e003001181000e40110340300103c840b80e264801c5034440c1e080c045c2c00000b000d0001868030241c2000e01c0c0b60380701e030324104c42c1200300c000009500028483c28030aaa080d441e5920003103441d81e0307031000703400d0300f56001001c0342104080070000411545000b20582d146190001000d0310340c0d90341c4150600c0380540c5181d14400e200f0081c8400941913440000c68000746104018000050410350b014500d828896080a069030300000070312164290300242100e1441c5c000d1601003582e0b2113140058440d1000c41d004400a50710700c10503942040450080301040302d05c03c2d120510190b4800c01c00700c40c803035680d00070032405400031000d00c03000c04d80207040712000000c0c010f001450011402c2e40b84108518450070f1640242d15440848038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 613546708 1250 613545458 613545461
    0x607030902102d0e0d0c0501030f0c1d01050c01091a0702030405060d020a09051503041505060307060c1502030405070e07030207170706060b22090c08040f050109050d12 74
    0x5401c0c155003040154032108651240d0764140c8a07407208801e840d04014a03003c58461090130800a0020381644a4103940341040c90f41a1911700525000c01c0c1041646140e1194500c076681d1448002d80e1038104c245044800007141208280503181044824042c22442500070b1140c1d5400b1441011b40c0d08030701402c0d00e180d900e00c400041a51056400a00041082c0d40764002201c1214064420041c2e41d031a107200c040c1c41403d50350308400d0b000891081c000c410350203550025401280181341c99041602e401c0790600075203100321030241d01038011074400c020b441d0042500f80310301403040080d00c6948039000b003c041240c00c215802c0e101035210220401002e10919442038006540380380a41c6007110359100e00040e81a144017051030210001040000d0048503400070740034002f00030800d0340c2c4810310502c810000341050741600900c180c9210020311030034507102d0880140f11545518125540b0398480c4040f100e90038505403842e54842d040740c4005803003030000400e00a455144c4500700038290300881c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 613547958 1250 613546708 613546729
    0xc0317120c0c1f150b07050105060409050c01120207060f020912010b060301300305040f0b09100f090801050c0d050723091306080102030702010b010503010b03040b10080607030902 79
    0x10085402c00041c911214085204402c2e556050501c204500c8000d9920000b0200000e113060071501c1c82ca00030070ba4042d803034001c10100380500b00034040e50f111002000304031002101d00500a80c064445052154050041c41c85d0b00b80c554900181402441c0c0c60304008e440c0d08540e0034081c290700244840a9107046001c01c500c203882c26000304614002880440c2c1c1610040c060500703a800c041042c0e94010710300700000b030b10304580c910901003420028036002d80581c1082c0155070030303001384640c080341402240342503680c03006009201c010344e000c002400740e880465003600941004101240441d0b0180d00b401014020b0500c0c0c0c84441d41d58805021107011240d015080c02c041001d102d02c8503a003100750000f68070381c4010074202d0540c1e440c070300d400050b01034843d0300006485a00307003400051260810b5026502c91042600240442c0c8455801146c152109006190312460240003140114641d07440d56a0710529842c00c0b02c0503030361207030110313440c1040843e07107180065112170746142113090401c000c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 613549208 1250 613547958 613547971
    0x50103060c08161205060d0203030703020d0e030c01050d0c05092d0f131d0d020a0209090304150302070602090411030601030f060506040e0a020405040903080403030c1805010c0c031712 81
    0x1a043d00c408010f00400710b124030b084080383c1d81d48640106405640313801c0c0c0148425801001c42c3d584407801d180103500c50b000038a902000c21980030320301c580c0e400c0105442d009808161b5603603240040d0700d00c0c280001c14150003143c040020504c103564490319145010003900c50480b000000b11800240d6416192500710b030f901340500c08114403100c2c9600e4040c075600855a010501003440072000d694504034000c4820101810b202d41460640003903000303d0000b580f503000342c40e0b00351140d44444c03880d41d4a01c500e06c1007220355402101c403d402d8601c60b5002c0c1070594418040982b9098090b0300280c103540f43c003511802c1c10b240010030700405680500c1a981078250031101030180030310f440300240b954026449107000600348200011800105541201c0c060400103000b04941540ca09000342001c20032642140070911b084440c2211038080c0d04040c0c480206030300761002c02130a24004644408041d00d044410340d13802040840040c400401115601020320070039902c440c0c1c401000b001540b009803c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 613550458 1250 613549208 613549231
    0xa060518040b0a02070201050429030a1a060a050412030c020301051501020c01030e060c0706060503010e0a1505010e0c07020402130e15090906010509130609082a0607120f050103060c08 81
    0xa1305c01070b42c000e42601c0448a42403034a14501d079103d500405d0349040020381c410b00420001c2002034240d15540603000b0048541d091400801051050100900c9410f43c82000300d8001d0004100c0104043c103084420381c402e28045d08030b4400b5a01082c01e4401c1581c1c0c84ca0000014210b0100d1540d041000e60900c40c070918027800107070040041c1e1900d441001c2c154100782900000c8103400d12070380390040d000500b00540208100e5041805c080c0c2c6481da03408089170b40160042ca81d001020030740c001d45060b924100000041505c1e00794490205900c07240040343c01c81e1702403003801c0004184141d02002848850304004642c540104064620311000203851f204601c0c2c4014081a03490018859054400c150307507000d00d580300c690a00070003004070100200750b541000e8203c0d041021030307000b82400d0504000801c0048030b00e126441941d00240c002800103600440c0041c3d0100c0c881c2c1d0381d00d00d11500d00200000d410401d006a10140c81c0d00341c000303441d02da89070140d5005190b4040600755211400001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 613551708 1250 613550458 613550467
    0x7020307031e020c03070b03010501030b01090315051510170108010207080301170111040609050a0e0601230d06080a0210090e13030203090a0e0a05010f060c02090a060518040b0a02 79
    0x70050a40300c0c1280d041e00311040403865003140b450081140020050f0300a08940300b081c1e6031014844168000d008544c0060b0412003458040d50042c0e8641c804c0e81d42c08800844442071216641d802410000d01c88a001d83d000045030030182c91340c0c1c1d80e0500808141e607401c06001d840304559101c80c0d106921080c1d8583c0304220000100d00305106990640300c50441840c180e0680d40c07911800750920b000710142c101000200096015000500e12044030400e03503070310310344550700e450181d1802022108103010420034041c0d010070726800340c40b072602124102407407420103400040e42d008540d42c540018555a2010040200354501100d20364080c40380341c07401c4001c041c14005614a00391016180400140300c260310b1104044c0284140c0b450300401a14070040d15503104900c0c00640400d5560130b03003141c540b60011420704004001c0030142c0f5a5610750b09018440d690034040852401441110101d903070700301c003250582d6011a000c1c1100c180c0c04c034000302c909040c01c000101c110068a48a500740c030400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 613552958 1250 613551708 613551713
    0x60203041a01051f031109040c0f020601081c030b0103110a0903140a05190c08030d0204060e0409170c070815040c0f03020904020907050909040305180901030b040609230106050907020307 82
    0xa11480d01a02903180100d00106c0c21506840540075660030240d0147c144904c0c0b00102d9031150032070516a8065007114900c0e41e13101c01d0142c40e01404c4100c2981e02d41040a0004c0c800c1c066002450b4040061400048411a9103441d0b00590412455100080c207100340800c2408892407040140ca0307811006880c4121656440b15550042020810511010501d1400c203211103100044000d0603000252591480e040403150b00a42c818010320021810b99200d10308641018803481446a50044c07a41a1010744640c2e507040e41e8010145030142485860070104141005100446001c1790403402a81107003010b18007001c200c52181c0101403030598500007080960f8502902303507001501540c4000c010340300c04200300c601d407244d0000f03286c102d400d4030248410540d05c90000e10b03840800106044003004050100f02c0c01d200d00780700241030f0007807000218000c00c02c030f540403030a654460880041c0412420b801c0650440500307010090070795480c101041039051403d11680e11040a1001d10301d001a070343e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 613554208 1250 613552958 613552999
    0xe01141003121b0302010b0a0617013503040f3614090d110d1e0e180a05010e01051e0114120a0606030b010504030b0702030403060203041a0105 63
    0x5110103800341c9a48460346044500489828150704103000780f0190190442c2000b81c081d103a02c403c4140039030300022002030164400c1d5400921940094108040c4c0c0e403805880d0030a1002c3c1c9051483c2d84131040c03540c640c00000417817090b88021240805236850f01c2c94060f0f04014000b8640c0b0501e0a00c007800c06910421a404440301221054801e540c00007443c1564402e00034925020f0740f5900f0641c00c414030015900004642100d0102991075004090180445076280c400b80c0ea800408038507003844003010024030210003808040c2c00c0c07034100d03003000910000843d40700f400700004000b912042e090280c03501c0c407030142da800760002e00b0150400354502404601c0020344d8680781001003100c010b01e0b012580c401e500c402c281012075945143c6074242840b2200540c48245e030340c0c1c04898501000019040c0c042d00440070300301816100c02c0d0400c1d10310345440c030808800911a000318042040701200041c824805913001e1030084941c3c4103c400d00801d41a44400180c110318480c22000c0032840c00c01e03049 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 613555458 1250 613554208 613554241
    0xe01090f060b030712110703120522170c070f080d08010b090603100e010902091306030812190c09080f0c0f06090d060207300c11010216090e0114 64
    0x5034039100c41541c1d40c800c0d12070000c0c121b42d0003040b500040040d101c014507034030a1001c21040701610007003280c6c0d11403003903040e085400840791045005080da680c1c00490002c801607541035500c4c04002d40f8042d0000019404d0022a4000c0990321001c1d0344240654942000410030404060805000340e504011405c0a10b008000140b03202d070b0030000019003070180d0b003c1c0e000700501c0c01c00b05254644d40c40e0a542e0004e1b4110500750740c02001c014540401c1d00060b8000c02d812203802050540c0b81800600d00c00e121030380014442c444603100142c1000310f1001d144102440144599100d66032181800c2145040c415200e021103682e51100c0411a019074840003001c000390f4044810b0f50352401b00c0000315105a141c040081c2c055880864400300780303c030264201c3e0300c00d04400121000c0100c160360418600c50101261000a803005a9500001c0c1c03101410b0510544140112100002001c11202a0f142030350011340248e52540ca105061f0300342406291140403004104c1402c034644001032520030401d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 613556708 1250 613555458 613555471
    0x50708010e07120507030204050111070302100e030f0714040f020a02100b03010e1504050c090f0a020a0e10090602061008031602040b210d17040b1f0e01090f060b03 72
    0x16a640441c00742e500a80d42c00100038034a8034240b08520b480103000d0000c3d00944901c50205030503115103c00444041360f044240c1e540240310170002144510225800c0001a0f44182c2621034189a0001113004000c980f004040c00352a007280c1d1003510050005840fa0301140180660040c88401c1c0240d80120752410040d008100c0000d64021184c0020302400351444442c450b07001c0c0b540100300001d1075140140c07240c3d0050049401d00c02c5039000744062600224ae21101c0000400041080c885c140d40040c14002c600d07180100c012071050000448bc01c010604180c0850103081041015a4051107100e5011040c1c1490008152410041071744070b05c0380c0210101c1082d4000303002811940d0703550011a0200000c0c148801c0403c0c2441e5095800c01009244115445241005c101e054450102c00008a048009940d07581c0c4455445d01040403021b04119030140c000400c5ea8030403048090401c1c0104505030309403807194074000c0301a04907807503610421034241c1400d609020054810048980001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 613557958 1250 613556708 613556729
    0x21050a0f0c0204061e0816150e04060e0c280c0602071b0602030c0c0a0f050d050a020619080c040303020604030516050709060302010810051e27040c0905070801 70
    0x240700e4030000d00240043c0d0000d00102200b40400410b1026082249007038642030320840d02a03c01c030b51000c080e0110b0700c0c403c401f4203000007500003042a00c80e0291160b6002e000e4808035010780c4039030380249070407001c036554941d43d2070102e0610000709600d00100c2c0340c580c03065084039402c02043d40007429242c40d01d50250580d078000480c1001c010f11040d14144802c01028804070050302e400009480380c0c008980c1e00c0a1340b20301c0c0501341c1c091401c2d402c2c841c00c682502c2c0200402914101c140301c9040840c08040e6002d010300c10800000d44c407168010100303401203200440c0090445903000d4100c003000380c51128151030600007030002a030001001c0c0c0d04075425083c42901d40c0c084401d0312144a40d05100188580202c020004010525030800d60640b40f00b40c0f50074019980340c01c5264031090044c8251644490540d4045000c2002021040761408014056a82040d42900c43d011081c100b0020000c1c00040102000b050103074403120440a0b0407400d9080c859030400700030003003e0700c03810701030140b445 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 613559208 1250 613557958 613557977
    0x9060906010f11011b1106070c02101209030905031018032a0c030b0901020a09180623030f1f05070917070e010f05131a03030721050a0f 60
    0x10f030082c02d0164146101e0300080c082d03081e8a008140c40064004110310101e00c0f01440b40c560f041011410328850062565140c0760640540c0070490040e070010921700521007080e41d0202c0d0852a40503884406000c0e0315040d04440c035200525150610010090020600e0701060140e0304e40c014100c8080a501880c003050319503082c1080003d49003452941c00107100d240e2903d07a0070010080395000459009009060041c1c1d9060300b07481c280d20944858200181e00c1c0c0c0d00030f104414100384e00b0408001c0341900025000e4130b801c0c0301c4403030402e402c3d8401c0310070402d007600010510381001018407841c0c409018101c425261407020311003410030104444816140c00018041910980303140d0010b10510f850440d80000c02b21005403510080d0003080408040c6c4000480c5584494054100b151000342400d010000c240384001c006000441c0c080c0c12160407032182074042e540030800b40001074010b114007000340070b580a0441070110010800303c01e21a0034132000c82c6152300151007000300708482c1403900c0344 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 613560458 1250 613559208 613559237
    0x53408031c020c1f150806070f020c030d030906050606042304090f06020c060c040f06050c01020708130821160302010e0601120b010506130b0c03120f04030305060906090601 76
    0x2a014040c140c1c0c40d988502070300c40400c0c007101004c1500ca110080f00401a48400c1600c042c10240d15000d01c0e0182c2e4050408280d00500c2150b030308420610620640d01410307101b0000900f4007038207080131400030b901c42400c80e06115251041e1034014100301e4403940360614240100d0540012000f240560400c0640060b42e21f0301c8641012842c80d502410410f04100d041c90081d000b50850100c127825449503600081105180d24100c07003d40d0340303403510030000358035000e0202d809600074030080060755000c0c001c0700002000c01d00a042c201ba010001414401e0404034024580908800b00b0514a0010b00080c105000184102d410321740819101903105500d90505074054400c03441500707000e20440000042d250641c3c4880305595124100682990340d8032400c101580c0200800381015008601d400c0000301031050081c20a451158207a031308000100d10728550004d000c803500e078003810040781000b0401d6418400c0c154842d80442d0080642d081c041d001c03c100586c0107002a0600402100c000d85 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 613561708 1250 613560458 613560461
    0x509071101020d05040305030114040608100207020307030c06030203160c21030b0a18060515031303090e011e0b0705071e0e10051002030a0e1c053408031c 68
    0x40f007403e001c1d0184518140340c50000c020340d20074400d001e00c41000c40c000301144d2030301d800b9050807034a00a00600400e107190501c00c00030341c40341c0f03c1240d240c480c6040020008200b04000d600500481c0c40060b01e81c603125103810541d02c4565001400c01841603024000101c0320590305100000c5032a604c0d280404081c001e900070101c9104060b4015586500000e4942e0b0301d5200000701c8910301750500c900317a511001e10014000c25150006a50802d00002d02c0a1540b0385004143c01d001c0d1815014146e9550201400180c0130b130031002c4403a00f204450303510304646040c00c00091400004131403a0207200d49417580c4555440c081d0a0b075541400141d228450240c41031080a4029100780901c24100306051030401003403846031038007031801002d0094000c0d001200303903808103e5949900c0402c460342d1040110758816504e03000d041100e011001c0010600c100310a80404540380c0801040541c02c00c084500010340041c10405060418801d0140244c048241c1e8a620355042c0c0041140c50161103650 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613562958 1250 613561708 613561717
    0x120a03051605392b1704030c0b150301050c090d030e01020f071815080303070305040203031b0d1e05040509060a050603040308011811180a03061503031206050907110102 74
    0x40c46580d10720391125904045403034040c124078107085404c41c071071010a4054082e01890001c002c16000340201814040031011281d01074420311b8040031250060f540e1040904007520106460f4042d051200300c203050034401c0c260401000803000f8200603040d070014402921444008042202c410107000048e4020010010500002c600341c4040a446491080c11034464580c411513450414440440f11805048401c050b280450080c51640d90343c0b10f0150003030040034201b00e0305440100090b01800c0c80210f5901844980d403000380844401401c00104110030074004007081407100688410a660440708640c101c500030b40350600c040d52040b00003116104035501058108800200300010190711840b030038180d8a003405030312000500842c400007202c40b851f0402d0f4124008108041070f00f44608034603840410002c0681141c3d9859564201c1513424a2090803000d141044050042541100c803000c2e82c40c414040c01c1100d1446c11001602c00c4034060100300c01d22651100001c1c000c1020740444 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 613564208 1250 613562958 613563037
    0x8090607061e1a10090614071704230901060e0a2402061b04050f130c0914030f07030f03050705151905041109060f03120a03051605 58
    0x40c0d42c810070440c08050b08020b01c03110328042c100c80c840c5080340b070021051030040f09159074202a160a05034180c3c2c0380d0f148503c7e60f0f04489818040ca2002501c1c02441c694822002c01c185600c0342d10381664002112080c06c8600548506500070069540303035401d40f00c0c110358291406140d40000940802e07941c0d007941d00f000030440796501144140c0302c1c0c1d4094914003d0300c1039084600607928a9103417811444003008503280c83c4002c0104101a280c6a00c103240003001c01482414183e0700071038140100c2ea0000700010110302e140074208520b11840920758880003054028155031180700300d030103032507821a0000030210000301e1269014544940d080c0ca100a5000c000c503100038500c1c005100c0e800000b11150100d00444180715010410329010312800340768081c0076202c5000807507040091054006141c40d0300b0108108508140356020003a200651026401160390f031040d082000b000daa200501c0080d00c40b00c100540080954071004640c0c400d14004640d040041d05da1040b00c800c9403d04660 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 613565458 1250 613564208 613564241
    0x209040204030512090117040f030503191e0f020903100e03071a220308060f031f1e0c0801141903030816020601050a0b160602040e0405060a06030809060706 69
    0x10040841307004802401503c030240c80300d1001000c5503035140758000c01110014000302d0000c007180000f034041c0011b150460a0f612194101c92070306040034045807005c007803500e0413400c00c80c200e01e00c2e09454450626841102c580c154501032500c00440d40e00c00000b0340c010119542c2d1186001240010700c20b0b1210301e80e01058074000007480d00d1070b20740009000e86003030001a00a0a02a15140a80e50400e044503031648950000e5900d0340104407180d04c01c120b1460305070103940b2030b1003010340070b01121b1035210310100c0f000a142d00ea4003441154180c44d40300040f4400d440c0c000c80718180d5420104043c1110811503501100b200d41c00003040c80703007510b003020000e00321690f41e01008040c0c024481c184150240d407130a030390030f100c02641207079200c1c020300c141500035940d41c60078800304100341e004010a49001d210158001000d6460320105d9000c2d40c03107030301c1c0400480280401c203e030500800340c0000700f40c4424003005041d80c4130308007540f1075085054801e8500040d601e0401c811604007880e0b10014104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 613566708 1250 613565458 613565473
    0x14070914060f12150102010506130c022b1e08010b0a110a080a1b030801140406080f0c120312060603040515070816141e0d0204081005090a02010804020402090402040305 74
    0x4184040c003809513044041e00f200302d260400194030504c1202d109143c000c264045103014140c070381000b060070b42000011809484580048580358a02c40500030100c901d03483c9581d60740f50b00051a106843c002038400800449400d034016601c080498190746201003915030710030b0003038800c0c0d8900342c810b400025a8024041900c06001104000e05426030154075048002e01c40f40160f0055501c40c041e0060118a2110050224420704c00c0044c000140c043d00001da070340d03101c0303566620b400c601c1c124001e003a9120159504450038441c00340c002da410120000d505041c1401c10740c584915000b40700c03a0142d180803000405000741007080701004c00d4440400c1015003014407005000c180c0860b00d583c1002e21012136501d58a2149488203000c0b544118001c0c01c1c44403415400d10007150b03203088125038080611800c001c41c0d0321840141700600034100180110810f4100c0d101c207a90004084001d190000044c840250760041c01096109904440069961041d140001d009004d05d4001034043e100d5004d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 613567958 1250 613566708 613566727
    0x3120608032d1917010603020705120d090506131406010303020d03110f0c01090309140604090903020c120c1305160c050313060306031a010b121e1914070914060f 71
    0x11903c8401148824104c681c2c2c903a00c09030164843c01d00000c2c000e5121280c1e04080130400000742c070800090300c00100c0c110b9040c1e01c400307140100c190b0b820224403000030700e000b04000d44034600014030407203d00a044190700d1518069201c0250104100c03d00da16090440c4405e000b110855600064940d01983c43d01044e081d454000c5c01e0b201070480c0864040c50000c0b45205120344084080f0100030200740c1382c5800d1140c440b02401c9008012829031141c004149400d541d421a8058038807100d000501350341c200041007000002e460346800406516000130700c0b400191182aa50607140203040c4901c240e1040d2400520394421106081701c107120350343c400308407030340e0503003121084900a05141d0001680110400303d051420b22401500c41c0081040034564441c07448440e0b8052101000d0208102c03503c0150400d480c000c03144202d510000301500d4003450194800e01000c0c00c204c1d1024802440c140001030401e620031b0203040301a808241c10b000c0590f179080101e0b80e511041c2c005494599848a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 613569208 1250 613567958 613567967
    0x6070609150606020c1e2b030e1905060a1e02010207050c04020f221a0903060709060503070513080a050f0706022107060e0a03120608032d19 62
    0x34203001c51424141040094614030014040083d220010302201140d001200e10109241e11086100d40020902c3e82021040b1282d61a05107084400300700c8280f600b04914004007a214001c030114410090301350310394031724404c10320a01c043d12020307210140d0310003500c0c0e001d64807c014500d906441d00482015400030b2a41074024000c0e0a10400480d4880c15024040005a008142140141c0348040c040844d00810700400146035901c608140c0e03915a0b11021071040d1000c60440f801c0081c2800070780503c26040802c609079000c5000d1030600881030030540020001c1c03002038405000c00201088a2001c0d2141400c410300502c11217048034050b1215243c507544034020001d02e40c1c1c00f4040c00710300143e40b600100c0c2c900c2c07401000801040c0840d04603c1b800d8029000302c41c0c2514074540e02c2215441c5203400304074145107030f8082d03102e141c19034014400b501c3c10381d036407a0006103054000340031022445c010301c03900040e507da0106412406500c5e80d40a50000d0003040c40414070905d0b480400b100c443e400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 613570458 1250 613569208 613569233
    0xf030803060102011e06051c080306060a110604080a1704030c021e040e0c03070b03011206020a0e0d0b0406050c1809041416080c0109080c0405191104080d080702060f0606070609 78
    0x64810709007000c230200c3c80b00d8072450348a02c042d04030401000051128038284004250f045000d0802d164801107110301245030180c2201c08458201c0300180c080c00b050b0f0402401c1c00c020602d0701141c48146025a0001c015000f6240d0080c002c1da600965120340b140d154103d80d203da040604100f12012000407102d0342c4a028141890090140c2c280100e060b81c009001c80703040c0e504400303503420070196590700c0b1402980f06614050400104030001d0311285ea0707020034080224007074080b0796164103081c28008221140648282852401000700761060b43c2c80030700c00d030b440403c00ca541c4c011a9850307060203d086001c480446405018018002c10b00a8184c400501071700c403a0002c681c004401d5600545030b4200b030340124000c5130f002c5601d40d503541c03809401807a40711a8441141d00380d207140a8003d0107580c0d49025900340d03a50081014411950100980010481c0c1840c2c5158182002f00c1c1c0a925040007525801100900030006202c43d1500c80484648a921502c1000f03080040e04042010740c61 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 613571708 1250 613570458 613570469
    0x10207060b04020702031908120106020c0103110418050907050306010b0a03180f0204021b0105190e010b06120a0b10120e060c0a110a0204180512040f030803060102011e06 75
    0x16041500e015402c281c4250b42809078041d00811703005601351580d03103081c441100300300c0b81d11004005007030452815005050003400660002d0070f2103a107040015060320641a9042001f20040c0130401000621080303ca04005d580724001a8980301c0c40e2940b81040d0942d0031064051060b400000303001460b0740700801880347c481d941001080c8c000c114160309840a000d0181c503000900e10380201600d801e6008181c0500c2e0300300403c01410b8100046420344404940101c61080a5030b1010703140b079103d003d204550410340c0000c1050011800010342c40e8010103601c03030741c89455900040d40550095011001c0d03154003d00e0040c130b5942c1c0200040110412204403c00207050000c1e04181d0b2500081c054080c034500c500c81f6061103004102190186407140d00c5840c2031103291104000361300c6a00c03403116410680500941000b11606005141050b408904000e40c981044100110361040340d01d181944d6015410036a6521003e0040b4090007140c07500c4c641e02c01404901d0008000954003400498a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 613572958 1250 613571708 613571711
    0x1704150903054006082e030804060f1107140604030606090504121b1104090c090f050c04031703060a051201051605090105090d02120706032a0c021509040e01020706 72
    0x14141ea01c0301c0205200d11804900c6203008900341c020b44075400001c08114000011484114084142e1207070f86c2c6500c1520800d100050a01101e07074001090500406030f030034480c1507a40c4883c480c5030b50f40c096101d00840020f12000c0d1080c5550303801d044400440c2c115000707000d0700c2d407141340c5a4001d1905817005c0f40d00002d80040c110b241805403134821b00c00c00306041c008180e1101e68480300300c0005100ca80e154010b60318100078001504d138659003000f07440b9006000403010241842d41040fa02c01400314840b8a030140010400170303c138101d9041c000c1d00e055109640726200c2002261409400e600300c7c552240403002c402c288454154001413244520001002044494800c141d80a1164800c91400070310100241c02190070718030002c071903141c4050403003010344403641485401e040b81d54100c0340010b40c036907e0303400c0203c1701031111003080001740580302041444008050201900e0000090250b5405940301c007840751401d0a82d10700c01c0b00500144520155064003a00039800701c00101c5010303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 613574208 1250 613572958 613573057
    0x2010203040308271c0f0618050f0c042a02100c110607050a17061c0b090105010b091305060f0406080d020709060510081305070f0303170415090305 65
    0x42c50580c03144c112000c5c1400340303050b48200907183c09020383c0b0709650580d11030352100d110178a2003c9001150703020724010b00c054628111001c800340c0c1400310904a040c400d81c10403046566080c5030342c070b01c10340030500b4151146402e030960301d0036410000103000d210240ca10b02000440a15048120301c05040d08030300c00d85400360754a04c410f40351030080c20a2000001e0952401c803245401612480f40c002034000d208034a0010303410301d4031540c0121071a049500351034503010f015006100b4000c0a01400c40342031024100341c150400300f00110003040300c0b290603c0c2c407000801c02c1522582600315181d0400b42c828803480c1d80742d460300ea0b030b10980c00400754014810041d0010302d0201c917215a03010b441000b018040b0f103500001d4119064034010f0115026001d0001500c40068000c0260340b00810003c8641c901c00c0e40346003000340038980e0789040080310f843c01204120004800d4108080041d160010006124031141030031603482c0183c800c4000303913102c4400b03101140890016161600c40b03401d01140c110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 613575458 1250 613574208 613574287
    0x1e0806180108030d0c0c02060304031806020c06090d0f051e160302100f09120c031401020c07060f12140a0b010c0f0213020705010203070e030c04140606030402010203040308 76
    0x10150901c20141c2d01e42041c480c49110211642040f50341d1101443d141c03100c4880c980015599500580741200410b10700c0c0010810204009090310040645001619960240201240ba144149011540301f02c070349003400010810000d48070044039411104030b03802c241045143c00070314500e5000034156403003001c12141804810032402d206590380648816441c1c08503000a4600041150015040c004032490200e10710b5030a4000c0d550303450240b1040208245181040a404416080314030481e9004010b07000620000080c6030045481600e004006210350000450ba5a03208501032900c050400c0c0d4951100000e44010500400c2404020090f0107404401512501c5845100500e40b03500042e0840c0540707000c0c114901e4000c000b4102500d80001036807040c0c2240c0c02154404081020510041c0107818200242c42c000b410681d0200050b0101c40841c01400c28000c040c1481100d000001030704692080c001c0c7d0b03000307607440001240c4401052000c10b1a040c5c41ca01294240404200c1c000d95 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 613576708 1250 613575458 613575499
    0x4090f0510051c0b101710050a1415030712060504020906010e090a0b061b030304030215010f0306020d090605040b161d01050309010b030f0304050a0b04150f1e0806 72
    0x2081200c488840c840c0c80c3c003961580030f4410020a0054004120040061400340fa40e840350600d01000001d40f80500b000a0003004841c8090011090703640307009458070792030504000864005520808000350801c456000071700c1d02e500c6400156200b8440110f400822007140c10040c0624401c80307120405903604c1d0011a10440705900c200d501000c030b600819205c4455030b020080c2404040e02c1a460404802c80032030340c1d049401c40010701644004100000e0690620404030841c0d803000944d204e6502d805820080c0610b00d00004d840e40f580050541608040b43c1e000e070b1040355010780d0a0001c1c2c609424003401802e4100c55681541d0f82880117910514880c1c0c290000c40540325515452010140300110f82e40e400007000501c2c80d643e1056041354641e01040300051803417040c002159a1400c0c4018403072000596400742600100520042c010100e401907862106446841c2c0814128103507a0210303503001052126108083c85981c0005105034000040e0340708500c1511501081c0901c00f081c042d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 613577958 1250 613576708 613576729
    0x20c0c040b090c1e0708042607210f21030203101419090e070803090f10050f030112061a010f08060303070c0806060109050904030f0c0804090f051005 66
    0x541c030050003400100e06142030000b42111900751002d018001d1032a280004e0a5442210140c1d080c14001c2800c1005901d4201e90780604510b4050300b10608806442c01581c40c1074a0055007a41f4610302d4030001400c1440c15100c0d41580c0108100c06c5200544c20500700401104050701d941484117105041468024022640a04d00c40001042d0041c6010300d4600e00e2003990f005141e00803600d003d0b01180510322031489003d00400740340042e0342203061040510340318480e0f111484d107400a03c16880c05545a40c2c019072800e40076981344542c6c40760107030126024071624481d144400070200021440c82180100705c0c0c0903c1c4504410054160b41c542e59085810380c8444460004d480c0b20141d0b00079500c180f9916411803c0034044038280003050f07940781c000407841d402c420345aa200d81c00300204d544e4088c101900a08090b80c020081d414280c40041a05030715008034814008040c03101410484490300300d5000b080c52140800104c0130204405000c0c1c803040d540c044002c2c10740803011440303290048050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 613579208 1250 613577958 613577981
    0xa090c180b0304020f0d0b0a0b0108011401120203060a150f0219051906150303020c0f0919110912010b130203070e1504080105130c06050a0818011e020c0c04 69
    0xa0700b15500d0303900f0007064442001d24140c00941d0035240d080020060b0103810701076290b070f28001c10031203400303c001000404140c0c0038104e11000c03a007005603140d8101085504540030284056603a9480c0720110740d10110710b511640c880c200035080b024a00380c0c815824000e406055082d40c0303100703083d11013503054172800c0c0002600070303041074124840307004010b80c250068078802d200104140340c4468142d034410b062980281e0242e0041080b02c1818903010b011020f61107030890300341100341045207450500604207104e45030415070725085000c0002104c010340389d003540018016194141800e002c90702824a422005014071070345045c0d0001240c1034003d80b4440c1ca4656070f0b081200108404029075407aa11607510440c2c88204008100c405080c0102c0e442034406690800b2200e07a40e2030300c815050001e80c00b0600704001441070741c928a51240c40590402c04d2140c2c200e64900c0518007182c0100881042c0d120050088003420031226043e07009400b07540010016640960300300001d000c266640301440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 613580458 1250 613579208 613579229
    0x507080607050a0c020a0b0d063b100e0a1a0f2404150503040b0c0442030b0109060318020d081c0b0405010501030e0a080c0c0a090c18 59
    0x291422940315213443d1080314002802d03000050b969040068541e8402d841a0680301e85440d02840f07418540d220074020494000c0c41000034012082c1500900c0d1110f250901c00003000101161486088902d003601800b9403401030701683c10002224001441d0048035002c0d1598045508a020b203400312031105558400b400180201000784900d02c21780341c10005114054000b88000320702c41d000c1001c0000d103d00c035629070310380d01c0c182802c10030443c1200810503003201400308010f100000c2d588000303000803100e0501c444070108e9441508100e1100b1000d99050b40589078202c0c2003010385c5a006030103858001c1c8c8414110507240c0300b0860660b01c503503d10b4100c90750700310424001401c2c411b400c170202034011410036042841c01025664829140102c00030250f84039444800c0c10318240c81070a00400003401c0810819440c2d400150311010303040e901402003500482c2d1903034400740900c9080e0000500130b10503028503480c1d07039011008108007203e240c005180a90200d42c400d006503240b01c20b42d48240c48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 613581708 1250 613580458 613580467
    0xc0d02061e0d02043b07091703310b07020103090204020a1e030608060f0702070e0114090610020604200307180f060503190302030904020a030b03010e06130f0f05030a0c050708060705 80
    0x442c0c540000041d11b0f070001c202002c00c000410303210007804456994034140c050341d139800210150701c0e464103801c00602006010664020345100000e66030508444842d00c86545031030840c00160001d00c3d1660010707400030700018403480001c0e4420ac1114050400003540c924821041004070201c03071060141c48215408040440c8900d44000d1010303900650500c1140c2400d92124011411460213a00c4100381040400b049000f5180003070314258840000d403a0508941d80c1e51500a684060282c8003910541c2210301d0b00401c1d00074907502584503040501112803440d61500c1080d0041070511805406a141200128a1043c0b9006180c00c49000078001c1030f204c00d0000b0340311607102440704120103502c0200110b03c4181c03250300140002207a035490010f000307503003c010316096520078020500e1a4210104119081110031a00700640c1e4110401220b281458034090101c0d03080c240018080d440045603d1940c294056861074540b07201d10195500d0b240c1d41c1c118140e50384002d54592001c10404d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 613582958 1250 613581708 613581809
    0x90c080105060d0f02040f140402031e0316051212090d031802010503100b03010b0c100c0c12031b0306090e010b03101503060908071b08030a030f0f0e0318030c0d02061e0d0204 77
    0x2004c1400b80fd02031070a40c1d01c40c0036403002e03880607a1701486a00e0310303400810007081051181804007007920201400c0c1405014582c44982000c102c3e25100241444004800710300354070603103d8810060700c0b605800c0c691fa543c4500e031a07013554000352034100c214421070002078000c8070140a180c0c54071500d0741b10452050b4403035940c180c6080c1d041b04c4040c00c0580d613801411003004012000c0340540310710340300010058200b580d240213480f50b034803400d446a81003c94250360794400046403612480b450000049624031500f511840c26107a0384098203031410950b4800600c1040c0c002805482d02c0713201300d8400700c00c181c61528190700071841071140310f030402d100411031a8000d07000720402940080000450707095042506d02240c0c26160440d42950004c2408001d2102c102806800c0b43c000310006c040f01c0d40504001242c03a0b8024000034010440840d00b00485406d07490300d0302c01020b24101d00c54585421200740c1c0000c0d041072117030140300010049031034501c1e05c14035130800461003142801042c907006103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 613584208 1250 613582958 613582987
    0x60209190f09051305010606030b092a2b051f08060a090206220320091b1606090b0106090302010e10090b040801090c080105060d0f02040f140402031e03 67
    0x24991601301c4101ea02500c00510280305481c0941203940703002402e002c201e000d2050500005011ba64a60fa005215010007440703c82c11614450000c10380b42d940e408840c0c0b0b04170040a8030035281c2c84010a003000c5140d100c0e5143c003c0c61080e0b0040d6500049a2445254200180a18415041c0e03903002800843c2c41681c1d0b07070300480c9245002608041c03410007405003503030700301c01c100400c4840b50300d03042c0082c410419501c404619203022141d140202801107800114030380805003030303064002e699800c4002d2810034507094440075410389e240d0b800421200d090070009403c035000100c80310102080041851400b8114030015641c041c3d440c984084040f100380b041d51900c0418807401d020791504001140402c21005001402d422400030650b0a030b50720b01b60f419050582c00101c2203904100410203a929024408900c0c550411700162150302c490001c100103007145100182c030316041404860045640100e4680600e100f903080f141490501e01c0f03149040c005c4a140220706410411a40d10043c224 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 613585458 1250 613584208 613584211
    0x9090c0f070822170c0301020309070e1918060c0201020f0a0e0a0504020a12140c16061e1e05040c0909020111061005010f0f0c150e0a060209190f0905 66
    0xd020344105043c140741c10000302c40c1c82e01d44c4103140c150050300e01c5160000d0103018081981d101a802542582090390445440c1e200310b01804400c0500b460020b55007440499200700c1c1241c12400c04c105440030300003c42117490740408203499060401d444ca9000c3c51051084859100311880300078202240c14004840ca8400324103443d40c802102d0030b01240c540d80340d2005003e0340301180c4500354501c901c100841c0c03c1c0c9101c4181031007960040002c1142c100c0210084446182da040451140400c081c139044004007117400506440f04a28003403010310080380d40c0b1040ca0405400c0004071018611484802030361801c5038010700380d03500c01004000c0b0705225045180c000744141000d00001411a4250785844001c446290f40504003840400032960001e45400d0404924548242c0580010340050300d06406150020600b18a004600d28000969403054415842a00a4400891460502e04081e4000000c800d1003422103c81c0440100d030016080c104a0f0714008042c80840d01d44039117107009010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 613586708 1250 613585458 613585477
    0x50c010818120414040e070905061f080612030a09060f03200712020f03160f1509030f05040f0506031e09060f130b04060c110f0309090c0f0708 63
    0x820011007040c0c0002800b000c0034500314004219280e5280c004103054002d01c000c5264026464500c000801c1c100206801066805c014008a4940c13030301804140c005190350300d9420210005040652065400001540940411200304030703e07056821201c0d481e8420300e4240800b00d0000c032810001607004035510400035000c0e00f000906004c0a80f4005607030301740c50400c1a002940010154100100500d00810702d406c144000c1c0a1800803000540d524803940000b92414540740307050108010036002084029a8455110346246e064041e070300700544a5100c003107020450700d11480b480701c0e2041c1d01b60f9003184e411060f8001c00600c0c003800e000c40c5601c05451030703003005100c0c02da5201d010f181030001801408114001c01071403a11642c84003401102401141075004100007032000300350b8030044140c10a811081c0060050707284c1906441d03421440030302d10380c54040c60100d502d04160120280c012420140c4802810380e03200120300440340b00d80140710290700b04c01e0100e00c01091440700078142101e0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 613587958 1250 613586708 613586731
    0xe0102120a020102040503070b070f0308281a150405040504050c0d051c2615030d0e090c0c0a08030c1e0406022b1214250c050c0108 58
    0x5030440c030440001e41c848a4940d015030740004080010b400c0812503440200000f482d01da00741080303a40d691304164400b09020f010800b16001003602501249404005100501061816a044800c07450040c00100751503524029201044100c541080c0f01e5003000ca00e0480045480c0600b00010000100809401600c06200e500c0d42d4031a1511060351a0708210702030002010708407250317402c86081007801c00005e41009502e10b1f114122040e0302c880c8000000208234840403507a18845141d05000352400d2a6925100301c161509400340c1010035821040d1050b940180c00e55207060030041907100b4000c200465600c400c1344c0308007083c00b14000d0342d0829a000001703407809000d0300f540c410000440420700300351007000808110543d010000840b000013440d0030f02e40c01d45598040178102906000c141b10512041002140c40c1c00c1403036014007403025840310310411500b044240b00709c0c042c410f000340c8400304441ea01e20150b010f014801808035154040c000b400d10f010840d004507005000030b090a00c029 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 613589208 1250 613587958 613587973
    0x130b0a090515100314070609150e03071e1a300a050a0606021b011211040306060305151012020a26070b07020618010c050a030804020f0108060d030e0102 67
    0x7980c032112070f80249210b8002c1c02a05045017010003c41004291280c0d403075103c26010414250000302e250704440c000038040c8a001c0380704a09440c12030310014183d030f050007030034400700c0d109034a200c0c03400441d2200380b004904252541001e040c525503004000022203c00e000c503080300c1d41c028125000d031200000707940c0b4a0744507021103c0d8040f98140c81c041030b41c6444004000341e0104502c51980185400c2c401070002d011301c2c4207851340030f00a0107041070420003040c07d0101001d0107904010759902c600385056036120765905102c03000740140c0c042100e1500800f115000204902030313100340134544001090306868078101440a1103c1c21040403a00a01e400100040700c0625900080020b003000342901d91130454542c68030b081c400550818480b5800c00e001c040302589032603090301c80c1003c00c189850f04500c080c4006a440e02e240b8070000309240705a51020302019800840180030300c1c8203503200c114800140e4015291844100c0d00e2607084043c407600700012074800c0d1114550b252041c01a60400b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 613590458 1250 613589208 613589233
    0x91311030906040302150c12090c060a09081903081810050903090118060903260c030a030f0204140d020103151e120503220909030f0305130b0a0905 65
    0x68208941d001c4298000c80108800c0c5030701031010346107085115503003001902d458108030030380e8007800f40c01d600e240c0000c0001446600c0c040050501804001384140d0700c60020745001004429a4041c03003c8501075076074150391402400c842c43c90100c0e49500d41c290f065503079071985902107071080c5004000b40f013811148030740b1015a109035802428602c01559071543d1080000d8080c5e540505c010882d0b0b00d564034100006c80c1e01c003c1140540fa4807100801c50038044880c2e20a084039042400040aa03001a140c0300030580080103205401042e101403080d14030740240001280680d120b061001400300c0039500d058640020241c48aa10504000600002e449042c7d000c041540e0403000820404441c00140c04024107220001010640c01080e5400e490381e13a11900c80c050588508050224403000c050080c0b40390790900040c2c843c412041001c07840303a00b4010140043c541c0004003103450708020402c01d0441406032848607802c10f0003012503403a040340303800087c1a0404291001c0c00f503242c18410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 613591708 1250 613590458 613590491
    0xd021306090806070804050309011d1807110705010c0f051608010c120b060d09030c0503210a09030e061c0f0c0e0321070f080d0501090c050705030913 66
    0x14150a03680d80e0405801e08110b685000809000401841182d07010040003980c00011104420007c2ca4102080c42c1c4000b5940d0201034150780b2a42e01541120360b00552400884030141318001c103546010140c0c3e8082122a1030300694000c880c00103194031881008640504c1004266a129100b00d03010011403003034401d03401d400c9400109a603510307645003070aa19031096200b10b07058040c2800300255803410000641600c034802d415140151651400c8042c14083c08800c0541c58200c015a6a100c10400f0001003042801002082c001750501c04a042c00c2e919105041a05525440c0c0645180ea0903040141c0c0c0d80152442804450b0020445c0904081a00401c020702c40c1c2c0043c0410455550340015210581e60702c0f44034040d41c0510309101c0078000e12440c0e440c2540044405695805850400d0764650044000160800384d00050340004e600a0b903014504030b82ca5005c0070050209803075412243c500ca00c2d03c2c0540560301c140302c2d602607854164948034010b0120388001510903a4180c0d5000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 613592958 1250 613591708 613591747
    0x30c150301060f090905091506220b010512190c0e131d0313081002072103020702120c03070801110f0f04080106180b040203010515031003051c11030c03030402060d02 73
    0x181307400c823001034144514a0078130f09400010031541d1811109064000038440f0704070100c0403118a81b5600a03280c02c0e400340d070031200000001480e0f12a2481c200e210000901d150103040542d0501c0e00318080b0840d4440c00d030707100c038540004011811031500b20300d50002070030740e003079218207000315415400071080d10401c01031544401159654080701d180c00c801e6820300b1002400140300900401c01c080008841121258440001c0300a0108181540800b10000d00039030900942180800d09011040c4ea03000071950a0704000303c0c12039558030b40b00d012142c04d0b1401000a424141e038140810b02d044610003000e0440203a4607456107007841e9440d0382d0b003400d45509034407030800c21182c0d040c9001480454010b80b140520250303819032039949000d0102e004803e00c0705051325040c00110216031581100b01c003020055130010100c079800140d03240b120111403852800a00841c50184140c1d9480c2804010303200040000c5001e5415a600c6809100c3e49905c004008400d0a5003006110410140c000c1d210 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 613594208 1250 613592958 613592971
    0x403030f2a080108030f1219061410031a27100f0b0703080a09060207050708100c030509070b070c080111031602030c0703020f190306020702030c150301060f090905 72
    0x140000a400300307000e040c1c02c0c1c06821104180c0c10400046480083d00004c0b101c0d130200f888840c00c0e0755564507000e010b41030a0a001c550760707181050703c0080e00d48100030340201462001c40305c0c14109030948100f60115032910b00510380f00492250201240d15000c455411125042d01c5201c60820030701c0c5c1e0101613442c0442d002c00200c038511000303016101400f61a10064071500711064940f81031504d01400c9620700400e40d401c182c0d143e030b0080d010040142c041e5511103500c10200c03010507445144064495a88200b83e03054585001001165140300380241e41c00380700440c0140090303030300304000b40c1c40690200405607840c3c0c03004a40029412000d204032030181b00000d01c00c540300d003051042d0302c0700409480c8000d401c5600600c03040c04508008940e46046940c1152a24002035038800428251400c407000000710900d076401c0081842040e0300207040701c038030840039030303054600d0700d8104444d2040d20000c52408040c01d20040c4449806940c140e401454035003070a40c0c40f03da81c0c1c40810107072007045805 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 613595458 1250 613594208 613594271
    0xc0b010918140a141c0212030a020f07120c05010f15030f02060c03040e06190e0f06040b0d060501050901080607080103142107020a06031a0f0a09090f110303030c030403030f 76
    0x280303200c040f440070b22031000640d40c1c07004e890f4600c0d1f101d0010071180005001c0700740d40da50010326450310350070080071031710740b1a402580320440d00c1c00080080c2900100304400d5900d54200081c06015407070314424940c01c0c03c0d03280b403116900b42c1942c640c40052f00c20b0040c00c0340c10580402c905107665508001910003081d003699194143c0c070b821001d0010824801d00078402600d1042c1050041103584283c880c0e01004400189845035a03110000d405001841002038010030881d0608060216607048a8180c0380c00355802901ca0340d07507042d0756a6512003240c4110024800c81c0c014400a11042c2e40d54501c10210801c4408072480300ca01600030008030040400c0c1c900c0700180d01000c50500d03080400040c01c80d07040400c42040c240480d01107012580c04030600ca0340344803400390070942e01d0b4002e9002030b2549007410800141c00b458072109030702d40c1e4a0150b42c40c500740740c2e206c0e506140c0041140e100d4854866040d00b1a201e0341d40640140c200c2032040e0598a889400d02e0600c1c2e84403000000d8a5040003a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 613596708 1250 613595458 613595473
    0x20a090e431a0d060608060901050d150e0721020f01080c070503040b0304112407081b0624180402031504110f010305010308090111070e070c0b010918140a14 69
    0x124101102e104c0d03803200d4144407036002008035540d205a60141100c80c00d4030710408002492402d154041c10128000800d0f6250101c404944800025070400340c8482c41110341054071202c04081d800e9500c154001e500142c584640c40c015441104c2042d04030382151725041c10450980e840e142590419005041d40c914040104024450404d5100600b20800c2d036081c003040c90505003030702d18804040201081034200141040400005000b15010410102030903040d9034000d0103195243c81080d5020403c1074a072441403002c481e05080100b90740d10700202604042c0302a403e2650401c500200306982c14000d98a0486003100d0b9018020720551041403039407050b500210400041c54180442a410140b07003000500000e0510000c03a101030009003400003c42820b44401c81c500205034015850b6103000e01c091010380da40107007001e200c1910404030504070341c0c1c840b450103040307442c441101c0081c2c010240c940008a400308090b918007a23a45020b0320540403594603600103410f1401c0c02d800b400c0d0320541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 613597958 1250 613596708 613596727
    0x61a01030b010e030705091b0d0507020705010504060207140d12090e0a0603230f46020f03070b070b0109110a1e020703020a090e431a 59
    0x8105540210700342000361556600344040780d5594128003819006580c001c0104074107800803448803503182140c4140696030f01031032507203002506d020b4900d140544286d0001061a600440c02e840c141ca8940d80101081d520f001c105880c0448004e442d69005010102401c01041002c1080c01c080b03d10354a55200803442c010801d01048001403d0a899900e0550b00b480086d0039150f80a03000f02c129041143c4078094101003034144013000130780340070900c9050925076541d10300c0c4201204403440c151000d0a098410968520310801c1d07002200c07180c007540000a801450040004403907840c0250071035801e262910720b40c0038079074040d807030658802440e10010013210358030780603154241d01c544080c00c1c10100740203400307808461110070000c11805041c6030003002c24401c00031340d001540c00400389000560340c5c0308140d004007021542c1060f80d0042880000d0040000c414a092100c402991408108482100b0680c40d8140c104038a0703865416410015011001c0051003040d41c1d807042400341c1c0c03880c0c01c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 613599208 1250 613597958 613597961
    0x815060a0e090a150902090f0612180a110913390605040302220216060e303009120316020c04090b1501021207080a0c061a0103 56
    0xa140380e04940c02c19036130820b025511052030b000c8500c00e040150b1100030220028401c801c078095066080b0f10041001d40700c0d00141c0740f0642c01401c10340740400990440001d815214010420050f09030081c040c100031160901c2d042240d8840caa803100360001410301d5072103280380484c2000740140304075040c03414006100402d00c4070408061041074048000e01c3d11101428901540c80080d11519440c80a20f030b40150a0030301d0100360611003c1195039410302c1100c1c1d6000914407034140c50079071600744c80550072000000c0900b514071901180040100f00d0f032424a41c055813a02b4002e006610a01808d850410301c1000c41c03501d440b03030098290440749034100c0004460001403c06981c2e51101d0132035060a110101202d030044c00ca01c200c85480444000260718040e15600f190b83c21610300818581404507145070140545a190f8886032001d032070100490351401d4103503603d01141800c00c03030240012420401482400c40034101a40d0040e501e858040840703241078500300703041c0c5032025480e21944c0d15 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 613600458 1250 613599208 613599211
    0xa0b0a03050f0d08040533040b070e0d05070e070509030714091e1506072a0b09010e210321060a0b1c021605030702090105060f07030815060a0e09 64
    0x1380f0300104c0b18074007602c60503510b40c1c115144014545801a6844d5520200c040541d4510722012070401541001d00e8010700c80201107588000260764080d0305906440c060b000b03120050b81000c010044282052041c0306401400360004092000410201a50fa00e05101101c01000c0d043c8420141100d00c0e014000e01d81002041016448984900200390031480c60403240c204400d0110344111031000000b00300d41d407140c404040c1c0003030103282c0204d40c5801c0711021450031021042551081070354070f44000115002d4441401d0104c0c241402883c0e071401c09407070808950807071050311001a0000e010380b50075035000d100d0701112030010048101a00310403c010941262041d980d0741100b61420700f00070858080c04000d040b284c0c4d4952044001c45600d50107546209041001e415a1840e0515050b982da900500c4120300400016000203102d01d017450507034014650170b045880c540041395a04641d034005c002d2204e201c08842082100d42da495280180002c2c2c0d5658480e40d840080c01000c10661200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 613601708 1250 613600458 613600483
    0xc01050c04081b01090e0c03070e03070803120a090c0e090d090303080a1d0610080606030a080f2b05063c01030209030d05040513090c0e0a0b0a03050f 66
    0x81008208580c0c080014044090707140303d9503481d07a02c5071200c0101c0b11001d0550100c0300e1910744500303010200d000e40000314010149030700d4800d4048a042c09041c2c03610b045202e40f0209400c10f0116403c0041c0c08501c640c0d0203040d10400103840740032503559462812803031b084044642c0b0140100f068410b010070103a40f05050604045030301d145196030041c81031100030a4040e180d03449921105500344510000380100007044d0903a210340c503002d020305110f81a07a00c91640c07a8401c140115401e0b082c08504111940d400540f501e01c1c180a0b4020740605921840b145a00c1a00c03d0361115400015414061811440240c000c540d5040180402611030015802e02c605406070007c4840c044080c9511007600512100644c81a8540b031801a4000d0141c160360a4241c000d04800800c445da120000740240c407021a20044001c810003000f10850b0b98454004001c864081e07000d20407002c0082d41554890603071100450218120004185110032075403044680d80d104140c80c0707841000c1400078414441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 613602958 1250 613601708 613601731
    0x2091f080604110411090a030516210311030f03070c0c06020303070f03050601020109020603311707150e07060e0d0f02040c200f0c06040b18040e01110c0105 69
    0x9054841c80c1100f680c140d0b07070794843c1d07940e030500d1100c03061a982070351000f100c01083e034995244c0e80c0c20001d40b104c140001403032440c050500c001c11500610901452680d0a540e102d01d041d83d002d035800d4401c001841b42007001c40c4420300910303943c52000ba00031881201075940b0141112030914100510900f0b581100c81550030a00402c03401c03030740c80f800d241c65074091868045a0340d210000141d00420003103101a400c98800810480d40c1014048144951052040d85840001c80c407622000d41c81c90b0403500800780404408500000380c29103020340781e414050100c1c0e5001080201420044500042012903150022002000350315044812180c016009544418040c112075803027403410300701400000c0c803d55452100301882840f40002d1114030440140c040c1c03d6520704d14003d80c0d1044c100c0800f0394103104040c510801420640169000c032100c03980c001e420498124a00d0f0b1250748840c1d41903030080e9981404001c926000d0040902e5200e480c600681d50f01400d4102c40e080d19001410b01d400e04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 613604208 1250 613602958 613602961
    0xa0905070b1b063105030313110a0b19030b0d1b330203090105040506030411030303180f070605030a36110402040b030402062206030c0f2c03010902091f0806 69
    0x5d100841226404040c1842e6544404076178501100d00d6454403541c039070850850032022a440d5504001020600030203289440104121041207041d5202001865008003025400700700081d914410300440e031070780300000c1c0c41d0b03682c54000034640c42580311444051900088281d6241c0110060303150006001840510f280902500001c0c1180c81184982401900000002000e10083c031b90355282c0a0301c0107080d240d07241405000f006460304c4a540060460007450004401004000740d840c0c103e4010b615040e0a41d5a0014940b004041c02418464008828400c117080001080b229171003003480c0c044c05002900460a1245903406034010442c0601e20400007030240030480d02c1540e85c0b059044414070354500542801a01c4510254000c4031040c40c0404041210b9406410800000215a40b011940c40c0124401c5400000e400d03a00b481d240090641000d5110300b030505895151409000031803010042d80c045140c2031806c42e9174005c5150224030030348500703402003e01002407601d1030007001c09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 613605458 1250 613604208 613604213
    0x110a120e0915091b040302040f02041802040e0f0403230301060e030303190207050a1505180c0a0510110307050601051f0212030604110c070e0a0905070b1b0631 70
    0x1101d001a00c8a0110750b076130640341800d8600f036811107019580c0584180b000c2181d81d88150003a4106000742070400462140c050260610780c030981d42100c5c1d001950260b90b88a0340130103182160f0291040d01000300e00c0c8000041d00402800e540c540703c0c02490440d543e589042c100a2512010704a1070303101307401c00c2003801140445660b00c03550000343d1450042c0c1d1140b1701c2c80c1c042d1a01020b04401040c20304180f80e2840580610790200c0d1003009500030512400300345200c51030702c913056142a950300c0480c41c41d05100c43d080902c0aa0307001109801c09000c4810540c102d24038641041e80d00300c6842d441540188843c0c1050220481e000e05103640c07524080300c110401940354a006000e4245002000c170020381d00b076980317400000d070b00d400310000c8903540d980341c1d03c2c4980c841180c8e00030b002d0105050300128054060034420007204580000185c08030904084c001d43d50742d0b10224050f04039810700f500201460205000050007403001c030918001d585034004006002c0201d03a00e185a0365980b13854440b01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 613606708 1250 613605458 613605469
    0x5121b0a060e120106051903060c0e06190e060c07080d020304050a03030302090109170a0501050609100306090f081b0c06030720100203070201020405010e060a090303110a120e0915 79
    0x190301c201180c10701c50510803074040303c4c010001c0e50f01507a03000011035a420042284024980c0507240211814030884c01c403000141d6014190001880d00188104004c4139280e0844504400c1d0002c540b51561724020030500160040d0403800180e1901d8012035020402c000c4108911094014540081d40c100792500e000206610400d01c40601455000540701c05143e03c01c0324204041d0100c1c4d09484036484442102030350b10844200c0c1280d856107864049180c03440d00700101031083c041840d64090300790665580d0700c09850301081c12102604803040100c000381c0369001500341d1030800242405002c80e05c005031803034034030303908a0140a20780400c18010140e90007180b8181e1300155903000040300b240b980c0b980c2d00d09190401070f888840e102005004180c2c0c0d040d0010000c54509036509480d8000607000c204a601c12810400c0100d81550010000a8002d15444200350b80e45404c0e40d03518003068840d1035442e04030316010780002d03039203079104052885c0c0740200940050784400780721001c0c3d0031800840e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 613607958 1250 613606708 613606727
    0x11240f0708240604060f02060f040c170106050d06090c0b03060f04230412030b04061409100e010308031e130b0603010e01021201030317090a020609040605121b0a06 72
    0x19511104000300c109a800301d0801c0c0a801c05000e440c0d00d1381c455507114014440c812242d031b0040140500d50101e003d40c0c8203000014010b54200c0001040c2900d061210b5240c800b420036259600d54891000240303960782c500c0c054428502542c0049403000c0315142603400151240c01607803072041d091080c446903032a08204041000c0c03041d03800040f007241188151114040d00c0828100400c920010002000802d02284100080742d80f070500504d0000340421041d40d641e4043c00c60302c01040380f040911454181041034000e503400e017641c41c0150301d40c0030b56600444260000ea524074000024080720b0700240c803134030b00130707000c00e1000c2e9089042c01c0280111b4101642c202078010700800000c11b046503001c1d0b02074189103000f94021955210b542c00c140c4451002407100750701081070740800b0300e11a001c2c01790003441a00382c90003925031080b41ea8200240b540059141a80042d900c100108040e00c1da1a20343c0d00c115020030040c4080c41552400051a000d0021200d001c0c03c0341c2c0d6000c01c800740d0054501e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 613609208 1250 613607958 613607971
    0x20a0f09060905220f0906151805150612010f0e0c031b19171303050a18030609030507020a17030a11151303020f1c0302090111240f0708 60
    0x7006812150281140303120301d5038403031882c1d01d800001028810b2541c00b030100310b803080c0010701801040205820100070301d84103d27444003000c0c02c14105c1e070000e140e105c140d1001c4801d001d11048116000824015004084c04104240860006203c1c4448910b0782100800c2c815000604619183c00080500d0102600d1904200210441e8502d5030010341e0a44112900c8641d03402030718847d02d0002021400300303040c07040c030850032840891508698080b1452029425499041c0780514010341142c031400700e0f80848501d09241072000c070004d811400b41001260196031222b03207070300d03003801040300c1d10b004d5030b0280f0303c0d480f0941e000702203251001c026640e43c041c2f903080070442d01004081076402c00d02011209544c6074100010810a20541c0d8101071110380030790700b00e070800c0e84507900300c6640d15154403a50034080e0180e00a540c01e00c1c41f030340080c040104180b525807403009080e406140340c00c040740010f614044c2030b125154120050200025404440b143c074680d40c82c03c1009000d0801d0a016191 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 613610458 1250 613609208 613609219
    0x307032a050303010f0b2b1e09060e03070503220b21180613020a05090403020a170405032d0d08070f1409190e0106170a0519150801060801020a0f09060905 68
    0x101100c48040d03405502940c107241e1503a988d20074041d00c2e000080854402c120b50040c600b1840030042c207000802d0f1030b40d10703034860001d519000201c483e40c17840495080d0281c880d2501a0300105190041d90702801422101d0455101c90101c0c0301d040c206c644400408511104008130640d1048440000d85643c0050520010540108a900108000c02c840e60443ea80108105090108043c0c3c00143ea680c001c2c041c0d9070340c004140f4980c49110179445076205456040d030100d09025082d245200000500130362200e01941240d907022000c0703003440b2240103180081100c1c00d04100625402c107818080000d0300b0310f03041803402014640807810380940945a40038030034000e113580c20342e1880f6120001901004141c44190340e035850f00140603110501031070200392091408a820710159010303a42c011065000c04100d00c2003202801d00062046084a00542940d103200158182081c400d24000d015400700250340c0300c24411018080612000041003080309450b010021960701112250a0b50022501c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 613611708 1250 613610458 613610527
    0x31e120e0102131d01061418010c290907080715020f0708010c200a0210091703030a0c020606130e0a1a190c020307032a050303010f0b 59
    0x68a0700900400080c3c240b05242910081804c0010000010700310084180b41d030110f030780f030321400c41d0400c11920f1711008000040c00300407401d100041d404c0c2034024040c5095050344100351100c8a41c410030700040c41c664014040c40c00070f0740c1c45441601c1d0b845503014000b0a0301c1460080d8441d40e4030b545215034141501032a0011414a2081c0910440142108200c03000c0d10b0310307007000d00d00070f140c00300741c140c003046c40d98403000781e001040711021100c0d1038200003502c101025174007801034550201c0890000c21012290120b003c1e50b54030700d04040350020000a60b00c130301e03254103e081201c1c1c40c03c0152080d0360180301002044c3d51481d042507070881d0410f10100b80000b0048c142c80c81c14207541d4004180340a188290420200000042c9204800700d002450321101d02c4e1801e00c04a03040b0036101001a00100b08400200c2c0c014000800f07034282c204440d800002c80f5140d11289001301180c1143c190300001300405c1000f409a4092004c1c16554200714500660900c03003400340d140c22030184810480065 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 613612958 1250 613611708 613611731
    0x30706080c0c0703030504240806040915021c27031211041203021501080706031104030b0103141e071205030d050a1b020106050904170c10020403031e12 67
    0x4060b1198000150100e502140d103030318000d440c54100c0d0050f8070b224124101407059081d518005032a41c2100c5844030b81c1103450744028400540703280b04080d1038054010341d00303804041c4c541c4001d000c03202e18400b003c0d00401c89801c1c00401e44003586002020310002e501801c00d10840c1d00c0d400300000da40760801e1850b40710005e4401c00540100301c40155000300100d00000c1d096100701c0b10301805c600c20307800d55056403c2881500c5960700203004641c29940302680501c000d0f40298040c502e0700c01260856410180d03a41d07281c0004540907041140c190404403c003c161080c1005400c524154000e51030400b080d07844802d070703500c8e0030303c1c42503500c16038041740c034613060003c103000b2203007004407000302889149820095007010b011888406910300c031640d0b0200290f80d106210b044152180140340901c0354a071503c4d401d2803c3d114203140c0000c0641000748110401041042180ca2480c0b18805030304c6501c0c500300504080303c0361016410300d411070030034030300d159a10003100009510310180003d00071410a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 613614208 1250 613612958 613612981
    0xd14070519050a050604120e01171b0f0f1b0318130b090f010f0603020c100e15010f0e0c04050d12030617011428020304020f0a090e060a020903070608 66
    0xa4003410178000d0710284420f00400c600f04a24210326512180e00b021102001101e8040021012020041d99040854401c000101c112414051000b240608140b40da0a0000e096031241003160410075001940c00e0707403600601c00200e4000c400c0800740d41000100d08070b071584149a1081da61255244c3c804858281c40d45d944004810b420241ca5059117180903900c4102c00d10b02070103001c05040d00360800065807842030089036044072091b40985040000b541c0c1d980c1c090502486808014003440070ba82c0380220b59404101d00801500c0c501d555898600001d900d80403030301601890381c2d0030b42000148500d441d5030f28000b0804c0d500403042421418001d204900501032500f0940c00301103014210024200c05420298914003003690f81021a201c8603001c820a101c1c8400d9401203034070707441c50340d20244d4459010b1030f4843d001410092ba404500000200d0100c442d402c03a140142d6079000c000810503080081360f038000d041d040c0841c81e1182c9070001a075079035003500c501750030044008009036910701031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 613615458 1250 613614208 613614223
    0xb1e091e0103090c06020318100c02190e0c030406060f030b040b09070f08030d0e0f060f090c040906020c0c101d0609060c01020903120901120c0519020d1407051905 72
    0x1c42e10b02140311791a010002d4495000e0400c11201c14261468001c0c9458030b003d90605100c00381e100c520074641190300f0302c81d05040380d448000c9454190240090408400d143c00c0b84102d0404080035501d1070980381107421124590480c000e2510f0300300052000502c00200c280d0003503006035a209071a034071a4006880d14006410034141040750000004e5901800006815500c005260a115805145c1c0010b81e90b016240b8907550594055000300c5c4008664080fa40d0308030003003000b030b00e00b40b40121010900340c9a0b42d602c1111141d90008185508800034450107062450845a0031203c03a80349400800809411018105485461510022964601c001c0701c2e4074a1001c2e1815888004054100d4001d400c131000c02d038002d009200c258106006080c04440d20303a94140c403030b43c0c5210720b210f03143c4005000f203040604c00c0c031404000510000b42140034101d44c10303085600812a42e98240c1c0000c1c45c03000366042da2803404030148a6200000d50110711107080f03000f07002c42200030105605109281c41134 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 613616708 1250 613615458 613615463
    0x30a05091309150e0a02060901080408040801050103030903030306060215040210020312010315060828020409140f0d0504060e04090317180d050a080f060a0902040b1e091e010309 78
    0x1400c0c8000b02040b250711005a80900c041004004150030b0818081c0c40d03512900000703620040030001e078850ba41c0a003600b16049405000c005017015160302d40300d82150005c1e0000c1d00480c0040b49c00b0010141d241c01a04060719a0b032018105500b101c08141d1032001c1c001e4402441840c0e040c0b003001c0d00300d00c200103450324801e20240030b5010356942c0c108188038600715608100458101200402d0403100003c0c1100b10751500d45005a003051828403207030748550004000c81e401a00d40b04202c020a10409612180d82e60880c041d00182c034410901500d010b01c0d42440d2030a0284c00d0208201c003580101c1260750f41007040c0c401003154500ba15084035148450140c50302d032090075009000c0401c18041e15015003000f200304882c400e1450000540d554010f03100e850b800600c980001607101c008010741960021ba01409003028607450b8074850b4141e802030303004160101004140e40503d4122401c2e080300418052800c02d00e8003070710f8004500e543c42c00b0155544c1e214020050602d0591203684510000d0381c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 613617958 1250 613616708 613616711
    0x3060f090f0316051b01050706020304050c180712150b0f1216030605060f0304060c03060503100e070509090706050a0c050a0f290109090201021507020d02061305030a050913 76
    0x820045a001106010f030f50155140d10850b05d06840a4040c1a03400350b45101c161226410021640c0d2560007940c0010800c17602402171204234103540c0c4404015850b1034407044209800303440c1c158401000640400e500c1c424840c1052810001c0c2c00c42071118006507204880516504d22074001c0c406040d04c542c1ca501b00f403e140c194104030310041c51a11010100d58a55414400d0958813000c20815015824180c1180002000410000351040d03200c42c1000010381000f050035a41d4100080c05d098030042ca5020b500d44801d0340c410444400d0000c41c0141600312408501e40c02c03c82ca180342d60303640d81e025403418803000240c60f1800600400c600524640e0050032200020f03040d00c0c1900b00503a08120444000032144036030710300c25002003465648408584032250755a03290154074005010007040c2a070560082c4c0c0a084141c0003096140ca102d200e0980040400f140d80704002031425000414018602607544c10300000240d012007110818900d503e4041c2d124201d4a0000f0b13820100194a0309145 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 613619208 1250 613617958 613617967
    0x7141c08040923100302032a2814100201090f141c02070e2505030a0b040e1e060c040618080303040b0a0c031e1802030d27030203060f090f03 62
    0x200224504c0f142605d2007a400c4c0d0340c0c041540d1101c441c0041491202c85020f9040b0000c92403507041200405151401003183c420a101203111980150030050700040c1ca5042d402e0148802810726804019004070707e48020003500045803290072741d0161826000301000031810f580940e0f506c040102c2c0011448030707501e01031406542c2d8406540c9541610030b1282448001000888901118940d510b8030140302c480740720742125410003200c00c1d40c070003001c207140e06650750a4082c03541c80300c0c0301d5180c0c6408414028440b0f404a4070004500001c18440700f0107681c021001c101802d14010180c804494a600305803894013480e890410408040d84c000c803045110110801c0284400c00e2411401641021000c02842e000c00000301c003920582001da0052100840e02820301c3c00b61503100704d09501c1002900303800240190300103070400d134040302d08400082c0b144800b10300500740744aa02c0309210543c01d82d4a561840d550102e80c6681c070003040d9804603d20107001840e29001400348580034004a802ea940c1c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 613620458 1250 613619208 613619221
    0x60c0607030504060516020d080c0423030c193605070f081b0d23040b0109140a1a04181a100e09030c07141c08040923 52
    0x9160484081c0e03503450400000c107980106d030f6801080c1e41e9025a01902d1542d601000c20340700f00101420020310034504000010300c0480a42810304e07641308010b2443c15240d11041058070f06541e08141ca031003804641218044201e03010a80821680c0d00c0c43d1424030560000311030821080900c0c6d8100340c0401d00c4821200d4026291300443c455002c0b601c91515002c0400811031741c00c0070403180c07070107a03044175a20764040540d0b00c0f0140c0b54a6441e08808119840000c65114040307a00b03840000742040e00c41e052008010103044154054144071804004640e500511032000710341c050103006050b42d94809000114000c40e04034002200007800c1030006e015400313101096114040810b861018081d010302c1c1070a0080c2c854580508004032400d081603042400343c0c0780440c000303400d4410030710040019410b4110f00748048001062034001000000c52000c4c01e1100b40708403451a0038510642c04000f20015022100340d50070f5941802c0001401520910036440406c00034030b000e103400003c481003021 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 613621708 1250 613620458 613620461
    0x91012020f22051c060615091d0411040504020f1509040c086409020a0303031104030b0408040501180e16032a0908030a09030809060c060703 62
    0x31803814440c49540740321081141940381c40c2d560300400368410b00c400252015596051001e41d91035005150020782aa40d880c4030b0f60300c8403213002c10030300850b00c00a810041e0091078140c2c100b88180a422810301c601d029595070140e52400403006200780d688d28042404c1d0f4070340d0450000c0e000c60203415040c0004c001f007041724140d049103103500c2c491424820790314840d034820080c480c0140b50007094065050000049000a55a010320b0100075000401d8420700000d00001c9200c1104da02e0040b1340140c5000c01f2038105801c03021030685ca4084d040000b41801600d03000d640008032505854005000d04041180b20b115104035030000d00980035100c20b000500c007a140052040303c1090700c407100d5500070b1a8681420310110f12503441c8000030000003c6103180098101907509445140000da801c421103210440a00b910441c62690322802125280150704100c152016001d03a50040d820002d281400a00e4039085000041a01138003192003402525070400b80d42956014100b038501620b01400e0050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 613622958 1250 613621708 613621717
    0xf091e0c0207150c0b15060f1305090601090e16020102040909050303010e0109050405120c0319030b030d090810020706090b0702030307031a1503043023091012020f 72
    0x15000c65503071103449a90083c012420490750285011a003a41d40b06070b16001b0b031944200303580e0070640800c03c100e5140103072801000070074a100e5007145282d04100610018490041103141480700c02c043c24021781000c4454a0b5000030f084945400f4943c1256089019001c0d540c00108010300b48110f400030040d0100103541aa000c114403061142c1e43c1d400400d044c1c903002e540240c900c0c0c200d05c1c01c40905207108001003140100c0c54044a240640349a408100c4940ca2841400000e82d0342c1049800d51400b84404d2703812031a83d00c0c15542035400c0c16956500c5a807490001c41c41154000345250400c400f0303810035001e10f604607107038440d00d00d00041e0280d100d604c00c0311807100003031818070600c0d100c1c6c0d1220103004484002030081404280241007015044d17201500607503201c0b14034030103407800c034841d40ca40c84480501801d40e0349623003040c0c040c00340070201e408040715140c42c4003003017000b15032001130103450500d4011540c1b0090342502441c103071010880307522011403450000412403420400c110040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 613624208 1250 613622958 613622969
    0x30f07050606030c01091502031c0e0105070c0803240301050a051602031611120d200705090f06011e0305070909090b040215160609020f09010f091e0c0207 68
    0x2a8442c1d50788804060b140c1c09042542070100780c00c0c10090040c9081c41c207040d4500d5911f03004403403601d1440314006400da4071040e08004031030707160f8104114682080c0100354001d185400c01c10300b0505150b64025450000500e80403038084c620001d48100d20000218680c00030740a0020041405d24a092402900c0c2c111815602c00718680c8008800a10000c01c450041c640b400540d01040c407955a040c4c0c1070700710a507403194031011100e1030b8040f00c042440340c802d652000e0f4840c220041c80d56420000301c1192850902200d41106904220f29107a094841c3ea014008005000259035200c005079405030601801e440d8000041c0c280884154040d8050781c0111055183e050140340d03078844081c00e5695034480200300c1000040400c005007409000c0742c0c141c5041e0b544060405e407480040d0702c0c0c0d01364090015a030040d00e910b400c900350304204011418444007a22035112030742c18940c0b401070310440e511443d10300395696203500c401c1001d41a5115140d0a509405000e1562842d0000b507407117002b030056 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 613625458 1250 613624208 613624213
    0x190203040506070e3a0501240b0403050709020d11040608010305060a020418051b0c0a02150c071403211e160f02040e01052e120605040201020c03030f0705 68
    0x1811345501d400f0a60703280d0700344510401058200c1020311001d200440f4003141d002111201c00c5040001c41c03c2c0180d000d42541188007000382e0000e08500d0500310490fa1190200e0304e020001480230403400300d010020b03175a4a40b40941d0b2148a000b2000061030240d074540f084007008500468a070f60301c1040305040301c0c01601160b0042d1a0031909100300d200c0c52140034040142500c2e070820b9114a0b401c00c030342c4405954000c07500b80c1c0d0405203216140d8440e103581740c00da8000344005011803410610400c0d00e4101e0825080c00e2070300d10707440340340c1d00c29a9000300006ca6013064480340850f5410000014404030010328040b04000404107044a60007200107001c00f0310224090113100504003060310011385101380d600c012035640e80c5910360003084200c0c003a038100347c03200e100d94041d060034011240114680740b41c407000c0c0030900c640317204144520a0701c1c010303000c4c9501040009010082401c803115070081c01c00140ca440d1440140d103800c4444641c1e940501001c10302030700c401304480141c03903030901030001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 613626708 1250 613625458 613625477
    0x903160b0109050c121f0503060c0915070f03050f090402040617070c120e014805030f090414040302031c0501080307061e020d02091e090f19020304050607 68
    0x900b544d4004d101c402c09449880100040c007100303c8540942c9042d041c0502c06001903210341c00300b410124202e40c4010542400a0b50030a2424104040c1804a840c41c0e40c2030b0030203580780c1d41d41da40341301c400070090108240841d00c0f045800c0d041080360b151070701c001c2c402c5517203696404001c4e001d040c4020f0915500081c03c03001440382c0b801070520205c403a5112400c040c000d030341542c054943c00d507070340310716410841030800c1554285814941e40c02120f03014000110411000c0034007914001150781001c4410840c0081c3c1000a00004140c03040140010307200c2e030b10b0b052001c02240007401008900f6081c860207009000c00d045c4c001c0300401110303c00519204441d250079002c1c1c01500c0c0217100e40b08135544200704d00008206994080074886901c403018004c0b51003e0118801030b82c2209840c07400203a0b00060201c190301e0003101000c030307070203040340c1244994481c8030001d400154010300001c001540c070000070b1000800072186540c010315629045407642458103280c0c0c0e40b900304648a1300460000d80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 613627958 1250 613626708 613626721
    0x818030f0d03151d0408030702120d1b0f050a03020906070f060603020111010b06070f020409020907091503062d05030a0b10060c0f060b040908030c03041505071202030903160b010905 80
    0x922803048010700d500046141d2250303a610091b65200420b0b200850241d004040004901d6100400000e4404a4041900d044903c5425200d48000355070905010300c844d0800c6071960040c0999004081c41e050043e160302442010560350b104482c2e000301400380c1d6405d05000c2000d5a031104045da4002e98482400107080c250503403c9481101d0603035803000b402d00452001a1070150a11200fa101400c042880c072459404140342c20b00555043e0080342c66040d003444400601555083d915203103140900c0514071b0002021a03840305030b000c020b050200306081c001e00e0002000300300000d140150844d045d9481a044c0038404001c2500d4038050340300c401000181e0380d84210801c00c032141e0450f0840c00c00384420741e103440040000d030304070540258940114070302050308040030310b00c2001950702c2d00341d580c54240f52800c40b4104000b16020624604000d0103000e80d48410038804c2c4548500006039213032591001a40b80d802009254404520058402000c1081030400c0c10304845820005104035100c22 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 613629208 1250 613627958 613627979
    0x2128030e0c0f090a090209190b030106231801060302091e03030a05130b0412030201050601020f100c0e06211006141812011b0207030818030f0d0315 65
    0x1d05480794001921001c00c111890286252900030980c0440080c940b10941d0108580a40071030307200e61a442108da81099504880c0501c1040d0a07040b40200001410f20320a0101045c60040b04800c903a802280306c1ca40307407200da000245041c0c40700c003641120340e0345180c000c0103907001c0700c1e4050246012594842104e40d14030001440310f140280030f50305121142c202140d046c0c1050451008151140400162504441d070050000e0035a603902c030700e196210707810085e00752000584601e046500491442c5152000402c44035043c4651384000700d0a07074041841214500e40104101c1d91007a030003e6060504e105151000001e2141c10f0010012555440d040098400c0984141d034085010301e1130190302200b00754001c1078107040d240100b107400392040000c112182c50b0840000c8050399070b412a27000c0c0f4030102024000d24000e0b4401001814190741e604c070b0b424042c445403c40412100300c408646a42e0901600446c0c05100c1c04494000d021080000c003e0074244a010f04400b601d040c0104801c16070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 613630458 1250 613629208 613629223
    0x50a05031c050a021002120105010806030f0a0602180a260d020606010c08160b01140301061212030905030c160f0819031202120a060b07052128030e 65
    0x1c0401115605048181541d090780070062440c01c50059030880c5800e104188050440355110004841c0e50391b0422001411079100540901d100744c0c4404000c8201e01c0300003a00400003688410050f840344040c0404400d101c5985030203640c410540b9a02242c8001100c180070706a0210014042ea0030784001e421a80750550890309000581015000801a500807806204054410f12a91f46080e04c408452262101c00d07040484902e6540307001086281403085142107128800c80007000780c28070702404200c03040002e900003080c4400824890102038026800700c101c15401c0002d5030383e2940c0a00306203803128802d42001c02c0180400802049100710311340c0700010303680004c004100c66030300302042c8401b81030411800c60821904d4410304144150360300207080b00440b51201094030303042801304601511045d03000001ca42d401407000c900031030000164862244154158001c1c1c900588000d03078035a1081810580e40e4909401807071400c0860a40212060012036408110320604100300716282d070714 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 613631708 1250 613630458 613630483
    0x4151d01080919020d12030911010302032712040810060801050606040909110a0f0f0e06150f2101060806010c120e0102071206050609071119020409020301050a06050a0503 75
    0xb01014003142c007011540f540602d4002011011109840e03900d00044c90188124040003035140c40d03030f0700c04120000d400700419030400d0030306608500d1301c408600242c00c0c2c0c4440075501d4152804403240030941c10b2051005217520703004042d98881c1c89044003592074031800003090150340703070041c001460b410601c946c3d4010100200424941481c02c00e40c00007400c0d4180d003d8407082502d03c20002c0594404202100030269041d5250801d03181003480b18004034030740c0c0400d0752480e0b0002000398640d01d4480507568060781d094107075110401c00000074140d020b90a80340084541031f00496021060042c80507048810990b0744130030a030b4491004480c10002c4020040c04110000803047c1c400d0f0003088000700d0503030103204460869540390325441e08806004011384041d55520309102003410400c000a9122515082010340790340b2411019560305440c0e00e8503019100d41400301d00455584d600800d1400703400800a014508000d800c070001080c41713100700b40c89a0741721880024035080210716100d4100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 613632958 1250 613631708 613631713
    0xf02090c0c0d0c110907120f020903031b19031806020102340c151b1502032e090c0c0506060411090312121b03070f0504151d010809 58
    0x4006a065030581000f8004a03864140b0303024012242d1502c000040c40350034a5618a0340f02c5000c510950107c0b410b81510700225801081600c103e92400400c4414064070824480c4210b03080a2000381049803504aaa403409a408480c4092580c004814650070006d02d08614100d42d075014164200d114020901e0700b10034108003400040c4400850340d45080d011401035412403016680e8543c00180d09801c00c07094032082414480440c0d0380003a44211315890b00c3c040f080c1400894541e071440001e000f445400700303a0000001488040142c094548d11221448402c2c00c4440b581403001c41e244888c02548141450082006201c038810110700c48000e03042070141109440b90300520000d4009039049540000c030800244c49c141d20308004804d805500305082540300e051400b103200342c140c0060a81036414a4583c1c0042c6001c01071012290041a142440100890021401d8405000b680e1000c1d92110440000e1101c258020140c4440c0324800c4402c40c050822038001914204020355100c001903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 613634208 1250 613632958 613632973
    0x11406010c03270603050405010501051909050901200901180f0b07050f0d09081603020604290a0e0a120803010e222a15030b04090c030f02090c0c 64
    0x40c3c0681c401c18074440345010341680050041d81407154059440e0b000000181e915000c1000303100e03003071007072502520040303c0b1003009001e00711030184410100c0c040c8484480d514000702d00213103425484510940c0c580b0000319241c1c820100c2c40e81180d040030300c03560301040c1a105014842c41048601c001030340c10380920a0411400c05c84806202d4005003003c8a035031181440b03402012604001c00790248180d03903a165140c80c02c2015807400c0030300c108241c0205683c02c0f44144016551141603805076141c2407404800311500381c022030040041c130344c42c14015400003d2200c21643d4070035140c0038901001d5500d641c040b0341d101c5001907250f8203d80c01526901003030005000d038107100300e0303680e800c80c403d441000c03401609030b250108000d030f5401045520101a458108411000b84a1501e84c2955090014560342c07034007007405050000c42c400d402c2019910044940700f0366680d4000030603550010103240d101522860207a8525405010680c42009032074002040500c03100212210540303400e0103403048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 613635458 1250 613634208 613634213
    0x207060510090f0e19020102030c0114190207080306040c0314090f01060f03051c021e0703030801091418070b0301080706020105240105090607320d020c12030c0601080f011406010c 79
    0x410405c003040741140810080454001000d0040780d10400001a03107044504003070040890803010304000c41b20480c01407180e07101252403003043d203038030001c26034000c83d08410074603040380100100da605066a102000510a529600041007403034902c02c00003c108940e250310a501c02d82c1d60603c401005940040000144030001c0c0c0c4c600d07005014507004407801e1900d130003a43c0211440d06881080c40c0e42c840d050400500d548040d41a00500c02d420302006401c600403451154503600510400800c0003c00d04006041d1040140c14010011100d41c15141e5840e440750644a0b07002d803040b40c0c010343c00c01002c2500000c9042d40650220500540e07042c41c48440401940c0c66000906542e600900901020f0041462200920f051100042c0003280c400141c0647d022150710081c140052a489400600750068001510484c0b00300700b100d12890035070031030011501e1803042005200076070045800000d0080e00000381c03500307481e001c0402481241444100c407554002c00b1660b4500142152034141c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 613636708 1250 613635458 613635493
    0x120f011e05040c030e060405010e070902031504110f0a030f1a0105070b1302040612020a0b0f0d0f02090a060f0e010201020f0f2107090303080c030105061c0207060510090f0e 76
    0x3201c1c1c09900340410032048003040c85d8146803080350107403426516031b0790007421781106000900142248070011030071400e200c400c103a1240200840c80340103c0c1c1e01c10381c00c58502c0c07140d41622000c2c400d2078041541d450402c0002405000810390b525181400d0a50b035024802180035101d100f404107075165402d02045803501d0702405c4014002003198501c0300718150240c0c070f403801004007a151071240f900d0550f610f44140142c40000da84807494502c07043c0044ca039800800011541441c03004000450001c0311000c4a20003445107941156201d41c0004001460fa41c005444103c0b0f9103147e03d4410712000e40c04011383c203034412480b0b00d079158001040b848481080d8440a00300c00e5550720411960100502d44071500103000b81c0e81c03000400c104140c10020907500502c82a40484140319407825035142c076021990901404500000c560b00750740c2c0130900361322290306452200750440000e0182c0e090580d001c0002850724005d6140035403d1003903800c03840c8564000d03012400c40c1d1400500d28000c00103106074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 613637958 1250 613636708 613636721
    0x506030601060e010f140a030504050d2c0301110d06030c14090610111b03100207050307020f12011103010905060d0c0302011809150609170a030503100b120f011e0504 73
    0x14240148003058190350303540c1b04003411f00e92041e40c90000f410f0400781480c91822513845c0d407601c00c2001c03502e08900305490310f5886150303911090f00c1001402103000c00103409840c450200100d80030022400c02a41040c94000c08126809446e00034212038840355aa5603203205c007044250000a1000880c801e4148009010701440c0103203402501d0b005100304081c1810b0310001d01c0032050450310350002440c603041c42071582c2451104c5085241401c43d0382c449031079020b0031303c000e481031101004032240c9444134041d001d40291100020046040e2140c00500e00d5002801924401032810002a1590400c4d042c5410400d401c41c254040e44c0c4e203550700458107480070760450100390080800000314000e0f00d02421950116440700305019a00b001401403819480e03a00020ba01c0b8049443c80000e4032000c10701e0901d141c1c05261103544ea6031030800205e1750300c01a606c107a01000d00003600e001580701002105000ba104c400c07109000da41c0e9600d1000740e8110780408071707654080a050030001841c0c42d03030154 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 613639208 1250 613637958 613637987
    0xe1b0304060905061302010e19090c18060201020a02010b1518010203270f0a030b01120602070803010b0d060b0406050a03150806010303090e09120403030e01180609090506030601060e01 81
    0x102d6480c045988640c1440020358904801e102001c09000840d07070400c44058a4042c103031140e040449816004100302c5100380b01d03283e48035964600200b203031886a100035030348010382e00d061102c85940703c200a0003980710013484801035180100040c030394a00040c65a020903000c910300345c1082d10001c1c848850880e07545006040d403004003c003c6603032003403a03001d19554540441294003001c01506120310b040403a00700902c03030740b8030327440c103000240243c440c0506443c0030304403050740d14000745070080082c402d05801502841d408000000c610741d540c1d00401c0e241d0f205220500036141d0721a6040c1c418003650041d940402c009014802d82203100f0b600014407440000b00050643c0da95001c0281007445c01c0e0000e60004400c144244509a404000303150049101e81c014081c55107400070018043c05603000040801413084902e801981c4958280401400b1280950641396519180540480100c0c0b044203030f0641000009186443d01042c020704a84030f0b0b848208040007210011280c81c4a0341548 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 613640458 1250 613639208 613639211
    0xa18061503060501090b1201050906040f14011e0c0c0206030a0908160503030603060c030f070804050f1b0f120a08090a090509011a040e0d080a2004030c0e1b030406 72
    0x450320038025980200540000024000c0001b070900000c9118042c100c2c01d240e04040a104141c60001030703003a8800e401c5441c1070003081c205e242c0010300c1402940034038590340c00c0038a1249555620308010040c074a0200341009900607169044e51503030110703100a98050803d20009001010940161850701d200c0c4120f9858035201c1c3c0a035400710120b0400a49007903001108103c1e1034103040080d1600086142030341410340c64000c00660004600a081e4010480600003040800800b0044800d0400e46030013070b40c4a00842c8100d9120096480d58200d00c01d0715200c108207928101020061542d9aa13540500b4200b03ca030380340c40c0d41d103a200e082d8060700a030920354001050003052045500a005070360022806402801407040c80d84031243c0214807452400010000100e130014960a071080305040170300d000c0d030750315032540005e0034104007038041100780d400c8440d40c40d58200d0007401524800c20740040a00d0300d5200300100700c601200c600c60002a00d2105603b11044c40000c0c5030b1040c4600700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 613641708 1250 613640458 613640501
    0xf0605100f0810081e0d05071e020112020a0e151c0e0307051c08010905071707020102090a0e0414010501120303090c050d0b0405010f05060d0204150b0703050706050a1806 75
    0x10203d01c5c0000f06000c01c00d007903242610070b03000440103001d50600860701c0d161850804005854044000d1009040040310150b808450811a406031400c203a540204110031500c8002c0844c014104c0300400c5102d0b8130a0b018908410251030460081e00c000d090280d00805a0320294823015000340100111000c00b4030060000380d0019000300a4500d1200109011001900340e9a02c040c080400c1a00014034075414682003160180d4000310002000ca1141c480702c80c03544403c60141e00902c114103042d3b0304442e40342408100070403006500e40c0118410142901c3c19040500c0d428200c400a0081d0410919011140c00100381329811411a0300e0003510b00102c2c0c00c0e42ca400142d510041403808030b502c2c404403002c010a00c0001e00c55600d00c0080c03030710107005510f030407000240140010100284282e0b941e014030041030b68050300c1080a04000c4201ca070380c0e44443c3c00d0140654000c61000c0300c429045c40001503040ea92800341c441686440c0b94940d0b0f035200c0f0ba81d6182d02603c0c4607649094500006803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 613642958 1250 613641708 613641719
    0x1030e070906180b01020a0b04060902222c07060c06060f0e1f050f040e010207062313020f010311090d060f0c0504050a0e04080f0d0f0605100f0810 65
    0x41590020443c0403e00403118030b140604506540400f01c205065402031180d00020511481c0b0580e40240c1c0b102d40061000b4280c4000b59040c008100320003480c0d0090308000d80410081d03030100c442000c000030f06403050004000f40a4600e00540b2840059410403c0100042070041c1d0120032202e210b210041405501d42c813902107540413560050807110419000d100101550310f00c0005a00d2001ca10b0441c5241404003181039604885145800345a960030400d1803060300390706940720030f54865420b000482c0a80f909051200540c00f001a0441040e80420300b0000c4003802e90078a0355000d072110394400c0d40c850041d00100288403140c0814a420841440c96a540e00283d0391843d12a5400050281c0000c0b900d0f030032503001c4022842404070800061000e5514801c90400b03c074160700a15043d951149060b0005004c1c05040080400000c198800d50400f55041192610798010f0200f213065a118100080c42a047d07594030040340e90354451002441c49145050781c003888216080b020140d498 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 613644208 1250 613642958 613642961
    0x50a03020411160507240212090a0918020a0807030b040308060d050d09290702120a0b190c0305070503160e0324010b03010b0d02070606050a120c05120c01030e0709 72
    0x380800c41301d68124810910440203400500031b507074076042c0320b0882e504da0ba11300041d5480030201611504120f01080461140da108030004014202c0c00704184100d02860342082c1c0d0f0416041c808034880d451100010170240310000303032181225041176040515450325203007560217050190110760402031405ca00d01c081442007006450400c40d50340c2e081003075441e00309805aa80d00c206403003458003201c401c00c400b003040d480080c1c0f901342d03804840a0005c405009680ea01c0c01501510007070801c213118080010b24800319002c48a62606d1a40c1805205180b05045040382c034110b843e000492000d0010818010308000d04029054050502c0c810342c0740d841000030b02c0c0c0038544101145a81448520442142c621040f85004016a0501a056504124007940315000328070580b032440764080707010024445145c10080c0240406029a0355040c1c6540f0798500d0a40840707410307a946460500002503074101242d11007094001100900503a900940c01100541810305032010984500c610200707000c10319 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 613645458 1250 613644208 613644247
    0x30c051209060f09030306010921051e150103020a060c020a081b040e060708070f1407080405120a020a0b0d0b04020a02030c190506041106130305010204081501050a03020411 76
    0x240d10051202d450040700c42c0c2e1820341d00400c0c2140da5041407082c8001a608000740710142c50f1075010001d402e10700041c40390700c105996140a042d81c0700f010b0940100914802001170801200c5d002d0301d052010042c01c405000034284002500f00c1d00003181004194410346036500002d100170030301025240d440340100e1410b114210040c107a80f00882c1c60000c00e1401c0d10681d00740300c52032805031005250920014109501c0108a1401d104200c142a8865880340c080604010040d200c00da44603299801c042c11136030480e0023514001e04000245107a42039000501401c4a5401031a15080d14186140203c44c0e401003020804111b40340c540781d00e40360b600c50015080302c0083d07178000c1d034441b01e414208a1500071281c54050001c42c208032064046400883e02650040d004000700814090010100b401031240034110604034820440100820a064004004803403035042100c0745880c03080c81040049000384a0b05034012b03940081040182482d400c418000080c1c2960507091910040d00c1c0002d0545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 613646708 1250 613645458 613645471
    0xe0a05070e15090f0409050606060a020a051b090a020c1c110102040e0406180b0402240d05040b01061103070f060204030f05030702100519030e1c0509040501051906030c0512 76
    0x10085102e64007401c0c40b02407039113242c0d401c070340c1804112099150305444a00141400340514400214180c400d8020498610415440411503030102201058000c2c404207403030025104407038000114070750740e4803070090360b9542d05484041c04458131601c025005108202e40310b04240404800d0700d070003811080c4060001000e196030307050924509450850102c8804050a200da5030300e0070409004522800f110f40d034400d0b8140e94014007224419000003040d03000a441c031441000000306814641403642105008500c1503040c010182d803102c10a0f500c2da84102d0040c11103501c20300c9010003082c811101e080d105e40c042e142c01860a502c0381c54004204007124030a0b41c155000098090841c00e000101d01c12081107403800d64100403285404c41a0100703100800b0003011346441408000c00010b110301402c113007840388042101e108584001e03020750008401c03284554642400003841c4d041090340340b25000110603a403104181490310a600400e4240c00d61020080184010741c0084c1050a80321700449 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 613647958 1250 613646708 613646749
    0x203090c062128050402120613080c0a02100f08011512020d0608061f05040c20011d010f050c04080d080a09020a0f090f0e0c100201090c06110f070e0a05070e 69
    0x3d171500500221000483c440c3c00681d001e07400700011314211446245800740d01604840c3d4414036107100a28243c0f100c0380c0a5840320070a01c0d600c141c260043c840803c0e00c1c0f119120b990807030707030b030b40b0700c0b00d08175801e9000408082092501c40c035240800550040c001201d020500140b0740e912824a05d1a15004450b12895000800c034404944c185c1079100c14001d1000312003d05c13441200030030040400700910b1503120980b40c009031141c0c030101c0a4000401003100d03d6000d20703d00841040d01400303045e1821018a1040c60903012611880d4040c2c2150181e900c0d401c000c0034100c28800d02240c4d00c00000300414aa43e40d01c1411900690304c418040005100b141144105282040100c0c01290000080c02c4c1c00540b601481d41d011000115201c408440704480444904c4000781041e405410000740c001c145404c40003003ca2030315008200101005100303812200c9031209019040da4a01450241c40b04c400420000a403005105030401030380b1180740c0c58201560400c1c0320100300050b989130303000001c24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 613649208 1250 613647958 613647961
    0x9050706080f01051c112d060304120e120a030503011410020a02040f0605090a020703020d0c110f010c080307120516080c0708040f090203090c06212805 67
    0x440c0d010454540200ea0101040c2e529450a00050401c0980d44081040c000003014600c051000502a22494041c043d1400600c03414044100350070703114505905001000c08401c400b01c44c1030000589114580c0f112020034081d401503c15540b20075489122a401074100d40c00c0e50848100b0301200d4102d5100e81c40e01612941041c0780114880300a8060a008008500380b041055600050110803d80c058a0006940c0356000740e6002801d82c682010350844648010f100c841742141d070003000180d0180c0c0c2a104aa20f2404c02100d108140b0200904085c030075215241c11032170045104480d03584c2c141007c2e44403400c15502d002c00c90b003048922601291514001c83e00d00ca00a02a00340e04c800b4000207044540074100019240074400b5110044281c00446c108080140c0b280481d070281030064904206999a201c40d940a0b5108a80c230b02c000e4080e9040074065424004e003138a802c0e0f510407188000c1c50341d2111110403401001054060000e500c50000740c3c2070100390341404000b0f42da60078046040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 613650458 1250 613649208 613649219
    0x3090a12080f0a0b0105091e040903260606030a0c021c050a03050603030a1709070b040305160e060a18090b09010e070b040305190312021318090b0a0b01020a06090507 73
    0x1030b04020544a40c650408842d01416a480800c46001c803000702c03001c080c40700d0350010346800c0541201046810030724090000c1c0c14542c100c001407480d000180d211500d060340304244000c4040b010386040740c014800307101051149010b80c000d645515118030440d024020f19a54500085030502a280d0210380c0015960503813a914bc040c55500c09420303001140f0b001e5181d400103283c20311700752980313080c1e006c510302103001d840c005c0c0070b00402000e08490741038a44d51a801d0064031450810a90704154001e9440091400c48800c102803041fa0300030260300507149002200296401448117203c0d8603507580c4105400a514001100c0c0111840e80001546400c08107803549486007035009030003401414401040040e41c00107044601a00c0c41c2c1d403142566245250982d04c50012a202c9401c40380007003035401d00703600c60800b60000c40c1e041d100034520390080120800f0840c1c00b0b421002d00748465100c00103418260580021a8005c010300c104c6030600b01c5a00c98000b200c42c5400d00300c03425001080308201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 613651708 1250 613650458 613650481
    0x120f0207150e03090613082b0309080405120c0a15030e030c0c100c14030307080a1b180503030301080606090f01080a0b040f08190f050f040b03090a1208 67
    0x30340c4010004000c00b128a50369540e8034010a032015200d2000090f1a826140f1004c4040f80100b090008540740200454685001010b030740d2550f809041003912028803e81c801c1c081c2d41001c070f812071030207860203050105110300c0050104600c8007612402000c12000d445060001c0020841c0038088111400c041000600b030302c60629040c8040d85c410704c00a000701d0300100d29681400002c0380c80c50300c440040f000c00d2710300c1480307004045c1c8080c000725100341a046000c4021846160207544154444e5105200b6000310b404100c840440381c06800c1040c4e001038040c0c50202007504050100c0a291940c68000901e558030980112080d504003030103001c3d803802c11f0b60380207400001c1c00000c4c0f58550305280001ea0384198814015008100302c41c04207013404034184400444941241c0442d603a01c0a016044a00a00030300c00c10001481a0010212081c41501070354010b6032107140c514a02840e1998114181d00b001c0d0000b130a9001703965510001a070a070711410000d10042d140c0d20460301e4118400807 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 613652958 1250 613651708 613651733
    0x40b2409182512030912060209031c02030d0e03040807080109050601140d120c0807030e0114040605120612011b0e061e071104050c121014010f120f0207 67
    0x51251030200e081d90b00346400300081540c032404504000c0520300c1c1821034884103198458510181c00302840b0041c400c080c1c00510819200750308071006007107507844014040e01c0c80310020b401030700b06204403101c01a0503003000588590b0603003103038101520b94200c90700709141c0d03a2001c1210307950313401c020003008800c0c49124010003410806040c03100d40f42021501201c4082801400c1420149811064600a8031171002d01c80d000105030b500c810030351030043c002c0e290010b007450200d03910303840445046132120101e8055805654840342840c1c9580e107805401240135203010351101d070020040c0d8862100f4840c1c10340151500340b18001d03032800000e0141c820780922842e28050b4508021204190408240600078414030308400d640c3d821442c1070452190000030803580d4803e003040c040c440005c0300360015103407a85096200481c161a03020484620b03203040e200c0c810140c46015070480c919070040040344110b80140c1040c80804098403404c108450b80c0c0c880318141c29034041040c500b801101c10450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 613654208 1250 613652958 613652983
    0x10f050606042c0c0a020118201c032007060e220c02030a020c0604080a02010509031e1b060a140903070b0c01020c060f040b240918 58
    0x80205050240110304a03124500440301c00200070ba1035002d0320341261039044200041e4206041403400c2800b18440307603500084401c5c00660801928400345240f0710100b402d80c0d54080b40c02c101c942198140c03c0030910264003150b07030142100340d94003074005c0d4601e809620035202c3c0c1c1e41c45c070588a050080080f900241d02e5800300070ba01c0007800384120381d00709000d03022200c2c3c00c40300c06404100301d1092200707201c564000c90802c1810407412691040d000006418401c0c2d041e001d54009009160a02c1501e01891049240641c85064000c0241d40104001c0050190190950f0b03a00c04158030300050008000500d5807095200069040069143c0d40c4001c0e1035003000c483d00361802000300d40007004500d60480d0b5203500000040c888600b541c0c200b0815000300340c250f074040d031106555000305000b0b4000c160800340f2401500000bc0181c00c0203600300e8819640043e40d0304940c1c407040c2c0d9082c802c0d1101c41001c2000c4450564070710840c0d41e002a0144216240d449050005030446c1e100c1e0b0600c060910134 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 613655458 1250 613654208 613654211
    0x110f1c150e0109110c010903030f05061203070f031106040302070e0709030809040b03030d2c010905060408030601050d060e060a060908120c030f070804030501180206091009081608010f 81
    0x2440722562a020300d038119a440040410072010010741c0e203440f803180318040f81880d8a0b00280004154240c1c10805010454200400456490405201c8007004002000c03a09030420000c480c0018403c0c1e0441505a01914111b00701409040b00c15107070400a41301078000d60701901040182c560821002c6a000c5928506000068a542e4408076580146000d1510640e00d54000c1e84040d2003c10a942424541400601c0a985040f590f0403610080102414882c0143c02c0d040d94a50740c140200300b102131f4450014000da58454546030708540001c1e01503410010100891110229640694000740c10508021101402c1503020411214102c0d8410b000780144c130302c0f0411983d08045140900706440a13100d942d540c958000c17950440c414140a9800101c01040c180c090040c40341c081c1041d42c0c8641c00070060791182c0c0b00803105403180100029800b10702000341840703500b024034820b5050002800c111007c552182039907403d000102c000b0310400c10046404200300d1409008814049038000c50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 613656708 1250 613655458 613655501
    0x160e15040c0905010c050c04020f120112052805060406020901030c0e150906040f080624210f0d03020a091a040302010305040503040801050a090209160909110f1c 71
    0x100540b000c445441050305000c0c00c811083e06200c8140305000a841c0003c208564541c15158100e240c0d4101121200d016800d440001c2082e2040480a1580907005070040102c600d040c50701541546000c51324001c0702d5002003031318001502c10040303903008a1250401685070600301c80010203c41404174011b0802c48111210b182644401e0000740341310140c104042c0e5240c518101160305440f540d40200310b80038403143c0000352501d0114003030307018000e84503c5105150420400e422411100e0005650000310056a142c8001c2070303000690b40c0d0600041500d0444903208003046c00c0900581e030b0500425000950782000f070b030b800441d120207080080c1245c0f2580e20803646e00c0500e8055400001e0506a03240042000e0203410000e590051500300024090751821040d040054031000c00128018801c080208006007220058240f4808403a5904040c603490018a180a85903410360344691035820082a000c000f0704d000200124045403140300c0a2110541c0c2510803141c0c4841a4818505440b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 613657958 1250 613656708 613656731
    0x21018020f04180b04050616080903040b18031009021c0b2e030507050a0605040b09040c09050303071b0608061f09050a09050f09010b21160e1504 64
    0x104000c078506010350b000104034000410401d0401e810701e40103000c0e507010904101c200000010444c0c424a80c1c01c0d0000104a011007055850300c105841c0981c943c1c0040c002801214800d5003c6d05103101001c12a80c003401c502c20100b41040001011040c4458903550405c0960429000021030300c00e11459840c1220703502d48940c01c042101400c415568081e0000030113140703511018500380200c01c1e03440f068085540e40740803980e41c1c01c5485682d01070040f00c03100094446c00380051307a0468011001d21454200e030304041100900d81e403400c40060040d05100440c80341c0742040032f014464441c00c0030341d44561045903441103494050744110100940b84040011030748801c4004022040c8010b030490a056217031400741e4030040c41d0b400054002070000e5000a081d01ca079080076010360120b0340101e206d038440d407120909035000740110b5038228104c4444075044030200d90560081d22410340c142e03200841c40506d034400301c2d000c0307610040844901c00700340000343e000881c00c440301d075070100c404100d25003070314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 613659208 1250 613657958 613657969
    0x819020d11071a0729090123010302090907030c120213060308090d080d09030c031106090613150c0905130c090302060903030d050708011d0c0706020f040b040602101802 74
    0x343c80815441d43c1c0841c0c4a410405682d4108840401d940c440c509aa44030300c040c1038030004201c4074207080f50700300f1401c00030318089202c540b080094046130300d000c143c5c01e54003400000e5201a007120044d2003048000008031754a240150050001080542103c0324940100621800e401c0402d030141072070541d0401c00118010212892202c040d0360030500540141042520f070302032840c0c18131303142e4204440f04003007652020502080c1440b035142d821204240c100d4407903035600200c03840c05d1b003030f030106000c1074010b1240b01005551620801110329070f01d10340c46041c801c0d1190030400c0c02c04100c02c1c0c80140a180b500c410708051041d5021400c02c410381c003485d0028030303911152002a019003400209410591814812600d242d4140d400c180306600b00804002c0129a0074450b075402c040c541e0203064030741212914018090644118418242406512110025032003484108041c400400000441d240b001c000b920080409401408860000190b01d4046c0d400c241c2007c040303e1000f12030440103a0700d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 613660458 1250 613659208 613659239
    0xa0807170609030a03090f05010606080406110c0c0f0d0f0c08071d0109020d0b0d1b0b0405011e2106031104020307020a03030906060b0d0603060b060c15040819020d1107 74
    0x6500d00402e0b40500c40c14140d61f0040004e00180c041d5007040004120341d508030701c505015a105001c00c01a035541c03004441140c0c0a10100c0c01c081d0707005120422030070300d0038a2400059840061542c45134201036036404181024011003201d2582a00b40c003040340680900a040c01850158207441d400c030420000311000b04d005000d070000081d40820500d003008050750201902620240c40c50040700c1c0c9a08000c80c2d4030f0f42c0240e00700036024810f84d01148a00520054400b11001a11228110004102d040e009002c00c0d41c601400c00c140340c2164071151a6640440303e2a40c59008009403160070750402105001305c03901c03030307a0145004000344400294000b07452003040d038040c03600103130154071440c140000d0040c9510482810002058a900344103d41d8490000c4a1007020f04002555004c0140003d90086151400e01e98112028050100341504103241c2c1c020300c1130030750341e01d0040740361a01050001c9101265005a0012295a074250f800c9000600c0075400c0800800511346005000d2602800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 613661708 1250 613660458 613660477
    0x611040807092a170a060e070804051023190603080a0f02010b0108180c03070b0c0c1915030b060a0509040c080f181c050702010206150303030406020c03090a080717060903 75
    0x18500005014691030b548008050228070310040c28a0501e000c0092110208ad20f06032090b00440c0744203034101d21103104235480c0364120b030100030051001025048900c5401041c4a07a01c42050500d001503100d82d01c00e040c09544603003030031602c5441000380102014050b841d8a0156071501007c0901030381c0024410303502c443c0c070043e008240142e120722141070940b111402e40d014450801c01140c4101000090300c000221310b001c9503c400307250420402050000001d100510f0075144c428046000c6140c0d95007040300540c1008a03980740c1513000304d03515520040d0400d000480104288410785040c0c000e40c807401d1441d01d04041c140c10251103041003044003038200280903140f007a0b0810085ea05024a02c14038040303001464a4070303d0048084d0140c1e000850403801402030000091860072260361103000d004001d4011401c641da1741da17529002750301c0421901302903c0240404403850b942c00c541e050151280002a24400b40381c4644c41c01180503205100c201a0020310401c102039000100b910304182c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 613662958 1250 613661708 613661747
    0xf0902043b0a0209030105090c10080f070e01020a0c060518040c0e1e06120f01080703080a03020a050d0e0a14030a05030f04020607020a031b0b070206070611040807092a 74
    0x2190000c00702d00a03c2080c045980550802c01005407030100441c1e104060b5200741c41c00400103905840840300c200b011100210428000720200f00001e201d00c059405810301801100ca11000603251120601c840d9030004000690020b036800319208094070041e46041d0a45081c40701c002040303800380c240c20200014600807001840c4483c1000300084000c000070700c001e40130035a105541c89011080c8002259600f03020382108000191810740090b81204603500030041d079052a00d0110106c02130741c0584884c50400c4002c0c8548032500312a84140009000030500a2412007031900d803184d5007120000ba1845039400501c04c465409421400326640316440a0415986546510014900d4019454081d41222011602000b004512841c9010800e211107070002895655050361015200d81d54000790840014400030002a140750440401b8207849000030b801d2a13120300142d86004010340c42202c1440d21100003029014411032010700c1c440303c5400300701c10800c2c2040081c6c1503112401403c03941c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 613664208 1250 613662958 613662961
    0x201170112020d1b0e042001050f0a03020405040c03020d05160c170705060c1305090628032406050612070807050919031101020d020607030906060f0902043b 69
    0x40391000b100101c1d02503030a0004e207400d4484003051448681101c089543c1500c003802c058001a403c80640200c0e00140d441c68900708a140c81d010705030b04540326020a05070207200229182c0e4660050000c150f40e195401a1160086682c0c070065400103032214030520030500101140350b900a0300c6040f00c0d42c01083d125078039050032180111500c925000034010b4050001407000500d004e000420001c2141c14407840510b4643e410804200801d4400541c040340b000d1760260031486039051180440300107102e0742a07850356038450b0340705010551042d07104032039400c0281c0f00d010480d11420020b005c017600c00b181000d205005a085002c00900030b2014440400c4c0000c00c4644281c0484900c900060646010760b00300a4240711a0b10450204555802114695403000d510000e144a0041c1c1d003580188007541740d40005800401440200362021500c0c0e10f0041904031021101d00c0040121180050b036651030070750000000030085151000c10080d01031210072100043c400700400880301d22510116 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 613665458 1250 613664208 613664213
    0x6100b1b150f060907020c182a040f14030c04050402030307060f0c03060611060708070c05030705060603070f080703172104050c0402071e0c0e0c070201170112020d 72
    0x41c0203034011925410615101004001114190345501032038042e00c030080320703131151070b003d9803078010041040e900400408008941c540701600e43c290040020502c808021403000710044658080d141491250440003408000d01205011f0b80c0006050681805a41d907601c40002030300c5050b0032000c07504c99600c40001c2025980c080c405c0b920040d500003010000136141d0103212001d0501d0a00b540c1c0403a140c01c4000908074000c03103541000300305100240c03000b035440107030945011801905120812104c10032580c00a0f00400007080210300507001410070745401c00070035250a48a030015042914000c0c020400d48030002400000c1d03a610004030460303000355071400b410078010300c40007840410190304141c40e000e0000d02060f000340c0c0914140d5928610315401c3c07009921450b14001d010201c100c070007098150012113040003840c13107a08640c0c5010354401c0b8200e10080e003a10081d0540e90005006821903070055055140c40b401300000c035405616100d21841070310700746074000e4040e20342800782004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 613666708 1250 613665458 613665463
    0x120309060c0c0a03061a06030103210917071e06020d0509010e04020d0c02010b061e090301090f050f1908040504020721050d0f0513032a0f030206100b1b 67
    0x3000207003c1d01d510550380d41d070b0a2900c0a0a840d0101e84483e40400c620201241000c5089a058941115908484600714a41126013002c01ca00340700800c02660008500f012104000394040c00f13107000109100741c2400210741b13400d90701d000075448180c40a0300070402240c0104050310f007034005080c1903490321480301c0140d40281c01d5400b5254001d00c0041c4125041c4070541c010803410f0280d5000f0840d020700d0000b801413a1280f00d01041d4658860a044000112903000400141e2000b0f40041243c80081d0740d8204440f4500b9011200340e0081504041c01c40001c2240c40c092110082c10442900c1030341d1902c2840c2e10070b6000c1c90380502c1c0c0020ba10024003040707180c0f040d4400d01003001e0352106580340e20010080c3c1c000042d1503607110f00b00811440c4091541c012503020b800c02500100c00001c5950302074035000300301905900f40b149541303a0741c0082108032110500307490103040003000240e258a0001c1c14140014134403400c165001d00184242c0b00d03404142c070100750002704890200e0040415a03072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 613667958 1250 613666708 613666723
    0x50a02030a080a02010e0a03050d0f1103010b09120115030f020325090c0314071b2103230408030901111605070501091d0a02040b0a02010e0606120309060c 68
    0xa4040c4100c404078000c00c0b8040380142126003c940c002c00030102c809403402c0d124801d03050050f000a43c107001c151081c46055004924035610380000142c00c1140d42214010b070340003640000c0a0000110700c002450030120000341000c810100200070140b50b466a40c143c504d15130101505520041c0711240c01c540f0b080141849100003c10790203c1c07040c0070440d0340020451400b51984960030000c0c0341c0712240c024040c84e030181c0710b42252040760b59503451080390404400e005030030b0040e001000c010045400810240c050985961016102220305100542035505504207102d00641d803124168100a0204000380c20650181506a0f00d8480c000306074090940c0d032088140181000461307883c41e030b912038a45e10406101302c059610160350f58006441d0417407507105900d2880356180545006c0c1500e6448030fa400845840d0060038035071980040322007074000e05034410150303554031903001123444c00b0400d00381d0244080780c90800c0782c5044400180c0740d006040e00e60b8002d450108403c6844c840501140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 613669064 1106 613667958 613667963
    0x51e0f060406050727050a140619020c03030a020615041103010b1c0903050d050901020f0f070f06091b140904020d0f0501050c04241704050a 62
    0x45014043c014101c408110015100e07103003112490b42402c0022494800562015040505020181480c3d4005400300f1a820442d00242d60f136100494010140c11207040c5115411140d050f442d0181c0116415803501011641580c244c1d400184203105e50216503050b2000c0a001d014803080320305a041110418800300700602418110b4001400714010322440e511701250b0114100742260b01c0a4422400640c0000d40b18281210390b014035a00a800d1800071032a1000814140c03a09220340000701040000114400017484004a545960030384c00aa0900068644e8600b050b940002c450660030121000c0d07801003030820381c0368481e003940c003c0906101600c3d03c8a4003000000e0303c28410807101020b4161510780094000e0040078084c40a54080c80c0d140d900f0041d189050038500310b100c2900c105c3c15680c11102a90000442c4507040303803050100c541e9161802d10301c0c180302021802 = true := by decide +kernel

theorem cover : BRFrame.Cov 613489208 613669064 := by
  have h0 := BRFrame.cov_init 613489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 613489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 613489208 ≤ n) (h2 : n < 613669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
