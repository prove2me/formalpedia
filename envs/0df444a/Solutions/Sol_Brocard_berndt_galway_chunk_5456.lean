-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5456
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:31.723726+00:00
-- url     : https://prove2.me/submissions/14aba43c-50be-4ea0-a46c-8801f14529ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 981115107 ≤ n < 981294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 981116357 1250 981115107 981115151
    0x90603032712030c0c01020c030d0207090b0307030c0603140606030405031b0c040f05040c050604060207090902060f030901020714030306060403020103022a070f06090f0b07020d052a04 81
    0x715000341c51038803020755a00e1500391541401c60007101e881300d02e24480c642c0c80d9840880d100e40035214000b40fa5810342004281e25403010841c0c0c000d070041c0e6160042883c0648801803000340e140c05081ca0100c0060320151030784020b03000c0c0d585c0018400b2100c00d4000e03118000940f01a00c6110140200704c0000e90000403500c4a0b484190140340c0e600c61002c1283c03411f105105095845070400380050b03d411002c2c0c0c01140324074003840000c0421039842051124034401e5014640041c0c01000301031100481070341016800038400703030030a0300d45005011003406d582c105641c3c00c04a40d40004014092011422003150501703007800140d85581042000a640c41c49a444001d06040e00801c9603d503900301a840d10f010f01c0c81030b00e41d0340e48040007403009507140c4110740030300303040100c03c0f8030b01080c2c0b244100b8400c000e44164903a030b03681030b50420102c440150000d06040768010201c845180004906001030800c15110500d2150341440130441c800b9820b085241e4035010320725100141c0a030341c3d414020a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 981117607 1250 981116357 981116407
    0x30a0210150b0a030f0e010b04060b2107050d09150e1f0f02090a09020301210506010302123c010e03041707080604050c040b0415060f02030409110909060303 69
    0x60b035507120740d40250098440c401c05c84c043c0b1481d0000d554107124040d0082e541c244000c0b80c1c00c02905031215041d420901500d88000850210740c040c814400b260101d0203600448a400c01d02d041940c0e05030b442003501c0404004542000300710b040720411388514018886036000c4c1801500701603942c60a081044101c403440780b603540d512000360b00040c0c0314070341c103d45900c007015021070b40c5070b5242ea080a010794400e00c00c08501c0c1500005000c40111941d4407611728591000150401d40d207941c00304510038400c1e00ba031180038050306070b100080c910360751408440f041c0b0315200c0c0000d101009840c8011101154150501d036410410100081d040101c101d07810340722245000542c51005001e054548036441d000b035141d5201d00c000340800e01070b0004d01481010000c40c0c080c0109a000300a0105403401004103402d58403000405003c0c20340a41d08400064543c0c0c03040302e041660b159026019584001c8072900e040a0004156085060592400d035111400394005d5180c0800d1203c81d00300f0390881803948c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 981118857 1250 981117607 981117629
    0x10f270b060a08190506070804080a05030c0d0903090503060615040e07110304140f180403030c0203250c06110706110c1e04050106030c050f031b0705030a021015 71
    0x40040c2d075480e6071030019180110443d40c0110881c018090591214002078505104401c0010260b605c031312101c5216903845580c4908201c55424107959030f410160480100e01020f004e0000340c0c0c24244110b01500b40079030754044013280344c0006c3c14180b500c00340800f40908004501c1c0d009003c0000103d40071a003200c1ca41980b655a90700c41180d580d0280d0804403c940000280051010220991000c803c08200c4141c007584150300304000340c10070302c1e80c1d415020940410004020074069484151000144d005980c40c11500c4c6000741030070644503480d81c8040c13028071004c0e010301c480c0c1c3c85a040034210500348801c1e42d40d00b00c0010de58a03015807103031404000c2070440001500509010f40d100d4501d024101e43c082010003081080c1c804600c284050149251200008285100c4e0003910207000d07094603003611b084c018107100300d4145e2000b080700d04c1d42210311114170307208465880201013440c0a1070146894085071000241494203218180e401103040c03602c2c000c0301c0f5070040900b500310754108181c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 981120107 1250 981118857 981118861
    0x4140907030201180b040f080607050a17071419020f010509192907030b010c031d060c1b03160e0a020a020c030f0d02010605190b07140f010f270b 64
    0x130100c80030941d5000001c154101180005081e0756083d0134006071084032040c0c0d0300903076600c1b404071118020094500300244e144480403920035803005005e9041081e5241c00c00c03e58807024110303115940581c080b0140034400741083c0751420350510040b010411260000e0106003000078042c0d582c0d2810484000609034108511002c00054a1404006d07840e407907140ea0b02e12103d1030b449400b1080c00c40300500445d04101543e2040e41c841c610b44100a070741521740490201082100201983d080c003018ad07002082040303640c000c00020030003110915a00d9010b0071540701e020042c5800d1600c602052450800c1c016018401d50010002c0350f03620030100c0d140140c80b04502c19003289025018031102c0e425001d10315030b4070810302010030b40404c1d40c0f0080e00203004e00366503007060090407074207411810060f81c050001840b0b0102d0020080001783c0c010308150543c10b4280c0c47d00c50401660315420740d4160764902c00740958280601420406e014041d40d504c1041d480c0180c2c04d05290030641005002c00e141da40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 981121357 1250 981120107 981120137
    0x3190501030c060e011b0f0b062e110105010b130803040b1e04050d0f2f0d02011103030c0d050c09330a0c050f06040812060303091e04140907030201 65
    0x40e011b8016888030054955503095080c014448501da44040c0d0f105050300c0d0020b03426092041401042c1c0084d041070300c80e0040921250124411803404600400411007c1305507841003d002c1d85020380070225425540c5c00b104800c0520b15840ca030303c0b40304a900140000c000780c040d80029190040c21100203000b845c211294507910b2881543c00440d8002c18201c2d1440501201c031550311303401881034105890414540b4034005d50450496100e0103c496046101e0219042914404001d40c0c410706109803c1e920102c40075040d81c2044a00d050400d00c0803e001d42e0b100d40c203005140e04101078090142c0b41c110030101095040001250549454110791784020118480311039241c0208000101e458481c505884014244000c05400762000e1103003c2000748960305c04a0401d0240360f11404251910740d903083c4440c1e4400d4000c160780c1c0e05010030b000e8413072a07482d4100c201c0c05000070300714412601a46c604c1003100b120105100010346050010030803035045030009031003040c0c03602400c001c020704400e24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 981122607 1250 981121357 981121367
    0xc0503070c06060b0c0a0203010507032705101416090b040509040f120e040e1506270a09120309030e040902130e01020c0607111c030207120503190501030c060e01 71
    0x244c0b0080d464400003d90000c031030400b0411301d8283e4402c41c000d001d55102c0041c100c05413805680c1510310150082c20102c0c0d02e0040200e0080350610a10030358800500080350a400c0311803403001c1c1c44408026404000241504400d41d440007042805c04041440c00d0070000c0e4250b000e08e025403402040520041028001382d01e050f141c80b10360020b07005003060320a0000038220708040e407100d406282800410a4103100100d024525190201e000301034039580c4408010903000003101c1103e1000b000c14081c100310910001f4284216000c001c0400c0420282c90030400214095010108041c50f004c0f4110010b603105d086a182179a086501040424190001030902400d01e00c050340514640318a244401c0c41c190064544003086006890280c0d440303c4080d5092000b40100b68041d4020780350f10325142041008160041c2c1c240d240044c20855030ba42c030390001014084803c1c01040c808020000031303a0000100e600306450041d0305101d2545165540c03003071110b06008602c24001e41c3e5602551a074411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 981123857 1250 981122607 981122609
    0x50301081b010210050a0f06050307051302072303040501120c0918110d09020307060518010804030c0b0f010317070503040506070809090f150d0b0a2705010b090a0c0503070c0606 78
    0x1810822806e010031040000d0200c81104c0ca02e140c10000006080c2c540072a138030080f24005441c25450001c1e07044a04004e5000800c103c1d5202981078400769900d070351031402982c9000d444015540d417030500b000545180854020550b01300d09242e085d00c80305900c000a41c0450b031100c5002b550ba030450f40790050140c090a13108060303281002c42caa8003220b0b40c9030440c540050081d8150740c645521800100c03890711540b09041c00010703843c511006154460140140d01602929000700c03a0081c581d00d0141360341c000d40701200c1c60309045006001344555107012110b0060b840e07080a00d000916aa403686070301440c49654400d0a0116a02061128120403101d011a00400c00410b510f0071400700c110400c81550101d420540312506403d460070010300016845410a00841c2c480c0d076840080c0c8050401032a62100003090924500c040301d642c0c2c0c08640f81e645c4038170000725102c20610700b0703c440114002c0000d03841a00340620841c80076040380480c0e030072181514001c420342d522810700002400c11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 981125107 1250 981123857 981123883
    0x13110d110114190224130b060d06110c1005131514070207031505060a0e2505040503151e0903040503100204060e0108010e06100c020307060816050301081b0102 70
    0x441e01c83c4075a10381c00704201102150118252128100b00c07410010300101c00c54141d111020006e04c4080418110b013640399104000815201441c40542c1c2c54109482441c3d400111540010402002900042c031181801000180c0100b00c28074154040440400003c3c1001c2c00907100b0001241c0101034a0700044017081e13028000b9201818a010025500c4010340300c1520128403100a012101402d8060180503a078020164000039003061f41d0700e0b010070006803052040911074211440e4a21001001e500811496111603444510b42011b1509107400c201004400300400002c201d00d0039545041d80c0038400049200c242070f075984d298840c2c50b40c81542c0150794948100003030328069401d160018000e48120340e40d28080050750b80b0056427500002e0103521440c0385403000260403400c00b01ba0181d007058042ca07141808030030580100381440b0035500510002103000c2c0400c00f20300103c08c1522074011803868502d280d0340c075103500d10b500e4154502c046071800b1441222007009a00c02c01c8001440d840e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 981126357 1250 981125107 981125137
    0xf010e1c0b040c030212031201171903110f0a0b0a09020d1401020a0e010f270308070c06020c01110c01080705071a0115031107060506040e0613110d110114 68
    0x1d00d4182420840f2061108904c1607810f00780504400070084180c6800d87c00520440324140d0a15005a000c4020b01072903c00300e01c2840c0242c40c140c140312203a407440f00c0c000d4070b807030015404901d9020b05010a4048580544e80035207d0840040c0d011841c4130351081c50b5000004101d000d51000614100f165440a0407141c0c0c4030841c959007007810742c010200c400058503480c43c00b0b180c4a00650b507540c420f03034556010400751070914110528491004004a80612204001d03a80320358481c102a04983c4007511400d10010050180300d8040004004940c02400c061a08080740e0204641d80e0001300e029034100540754010070403490045090344c403000e51202591303030600d108150550041000b40b241100c1d400c1c102035048051806031040c1c44603544d03840402494403190303490312000340c40302405258000c5e035100113403500300d003050242c1d5004100c0c40040f00c0c00080d03503040100001c0e2180764070a10902001c0000f00000e0b1303960018900398003080c2804603031624000c481484c10700508007840641e41c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 981127607 1250 981126357 981126361
    0x2070204020f0f030712090b0f0c220f0f0f090c03020403062405010519050f0702180a0c0806060a080a0902041517010e15090c03010603110f0f010e1c0b 67
    0x44021000d903100704006e030b40311090714240d0700b200c4095410904001d001241540d020544090780c000d10540d0002651408c40d14249688843d90300300340d610501190940e034800303014001ca85070300441000038000358100c1ea8a4a00384030016088061500c035440c1203e0f520084c0c120424020340543c4c0c02140c000341c08001c2d9403e0b81030030070940008400644001441e40c1e4010890751f010380145d44a015100c4000c24980022110580e8282e00c2104da6054076803080c010100144c0d14200c41d0a00305a00e009111024185501c1c008166254052110240f00300b03201000402e4803550180d6554102078540982c690312810f071000000c0001b540040d40040c10034042c10f0039004070382e020340100c1e408402c070310030203500d1340098500700c0724011207100c0d858004914508070307c1083d0042c645c20400302400d49040005600010342140e100c1d034400c650405114192042c289024032403e80c0d80d03401940c046030b61042c032500081c1210800190700c1d100386e280c2541d01e800440301c402d00c440fa8a50121502c2d4040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 981128857 1250 981127607 981127627
    0x504030507020f0a0602061302041119120b010507020906181f06110303041b1701150b0a141303052d1516170f04020a0510090902070204020f 62
    0x81e601140041c0e0158820b007407030740728038140400d40c2030460b0380580c05411640c0b11002142510202800c003a42e01030744609802214032480f01c024503454803d0120201c0072407840901a048030200082039140074505400004242d810800319040c00794102e070100c0050fa00d840020f001c0c817000d0002080044281c001f00031980b0103042056441000f5030003201041d681c1c50004660142510003906e01a800a1001c5000541500c00c5030022401c3c0f007403000821034a52812211601e40c10380304903500c1c0e440301281c4084200a2a110000c0c00c1c1c00010700e403600040d11001707425020b05800c42101108001380010124000c006460041c40e4040282e0700c0006d2102000e00203040300c02210f100555454421459400c0300082185070f04104003140800356503501c00311a0b0000340c50b4100340a020660b05d0901003410400d0502d0702c69440420060102d04160051000300890307a0406801102000541505160001240006c81c1c2e00c1000142e0745040ca4400f1601034016039010140c4a000420b0740111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 981130107 1250 981128857 981128867
    0x20706141003060501081603110d02090c070c120206030f0a0b0a06050d06051c082107110606150f0d0b040603050a03110304060905042a050a090e0106210f050403 71
    0x880f80a614103010301e9881d0700c5a50380300c600c88200000d0301c6910700d00403c0020241500c54180340d100420390303a803181c1c841e00810000001201c0d203241034900041c0b80310800401249100203400401d4010401c0690780c0e010171024400a0f0241117555a404001a0325009541100199900213400000400c0d0b8030307480078015800c143d42c115112801d0500c0414281403900660380007003401a100d080740c46880d1152891a880070600c94000324990720000022001c41c2412030103400560b48040002c500000103500306200508514414544061842c03c10701d08842940d61306d440303600c0070035620042604440c000700610358046400608062002040c00004500c2005441c002d4035a00710445000351001d8503849240220030104a03012404d000c58201070b44107684e901a0007415084003002d42c6080030980500c80c800800140c8005500c01145a010080c1c00c000d090514800304c4d1941080c2000e4884005498102c420301254180840386100300c0d00032220f241c82402d01001181424100201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 981131357 1250 981130107 981130109
    0xa0c0f02120a061a0a1703091c0311120a030b01090503010c080601022806050c090d2f03060c090307030b091c02030c0c01031d060a051807060509040207061410 70
    0x1416900d041d213084c01e00300044880b10041d00c070042c00f0a03041420407410501c690310f2102c085c100740c4010301c0800e03820340301c000082e6001201103825485d40895442c00400c82e0030080038120145e000380d0000981d0901c1e007c151000c18030755060115180986000480701080303036a0005034550700301514501800d42041205020304030030f0b804d8445600e04482c04558006450f0303040459410102001004540141e2010340c120b81d8070304840e03103004403000004404070180344d81a10f41b20413075006404c1280030410a042c0b05004a030400c0c81e01c40c141d90010b5118500109000c140001c0000d040135a90ba0600184002d103a000030305060380e04050180c01d030b40701171204000104410806284d16801d000200380c0b280011041c004003207041c0381d400114094401200e81ca03429400c4440c4029604400340040c0e4443e4104080000341c42c0b92550341000410140030302c10713003c2d800c0b11600744490f982c0b210840302059400c0c1c0700580e5a40961411400a02500081030081c83c40c19042c00503020030040210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 981132607 1250 981131357 981131363
    0xe0a1707022806050912010e061f030f1119030606050102070f080c010f020705040c080a05010b07170304030e100f090b19140d05070519140a0c0f02120a 67
    0x141a9881e04410b0b01100c0d04441184603410142d1002c204041c480d0340201101207025100d0303070a13035000c030b504035080d03580340d008401c1d080d007201c0c003086000340c03803401d01841c0c41e0303000d1203071041041c5181c4031040c81ca5a0602c01410008030b40b22604015200d03900d10f041d40303050451140034001d5503804c069000308098051140103001d1920b00107050090030100605686c1e010b40941085140b18005550039040c4109140540c0141d400c0050580d41751700c249031800c0802d480b0241c281c5000ca491004032034050700030300d001c0501800b041000c203900d45920f60020700316107502d5659486905040d1040107420851719070112071282e01620680c3d1161544814040540309c0030a10f03034450845802c5c2c1d0080710710754944000350b00d00b036148180c8940c900d9500f05420404481c941900c1224400030758008441d071102007440007400e4007220040005000103604caa2a0648904080c200601410301c200b00702c440400c18985501c0c400d0200c0346980c80095a40141011415106002a6600c1c0d00c0350250039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 981133857 1250 981132607 981132619
    0xf0f090f0b1e180a0c1803050613060f050112150b1e21070317041211060c0601030b0a14090c01050705030412150c0e0a090e0a170702 59
    0x10040940074018459205801008019000c4840126298102d0110042c1da030242c585008603c10b1500703141c2041c040c0c096501c0100d4148551180905003030201c19204d002241e6041d01040482c4000ca080d9801c5004018802408030240c14500c01503d03440c5101c00c8807a00e00000080e220000c1c15000c001c052148409842495003154200220342005040540020140c1c0380090f10300c6001c0b034003150303d0030020300245c400d00024400c503102e06070b1088650710640c0001014418400c0000c032558071901014410740c03606050441c6511040b07000103004106a01c0c0d031643c11603558642040c0d540400910301181c100e0340c2e403424010b0b000a000e4900b404854940041281d6443c81e040e14503124090381002040140c14010045500740e02c41001941d23240402e00000c603c0002248014505501902e04c5218103076009510a08a5030000700c3c4405000207000f9800c110340f03404440030115a091400064000810741c1c0c1d0a0804408080060030480c0900c1e4031090b500710341c0e01800c45103000f6625 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 981135107 1250 981133857 981133871
    0x160302010912320a060504030908060c164103040b090904020a1203120501141c05122d04060507080c0a0c090903031103060f04020c070f0f09 62
    0x90b0000040c20251a2201c07483c081c1880901004036011040c4105929400143d0301440c61820b01402c072800321040e5490f07000b07010038903902040c2000035001680c0a0005420039034901403c1c1e224076000c00c0c418441e42d05443c4148070440c00c00c11220384071503030700e4117200158030501b42b08161800038401c03860025140200404500205903810380c0c1e001400e1500c0e00240d1020060314039002030003207902c0700c1180c0b00030490046003020700b04414400c0e15030350761400c020748030350302600c0c81608060780901e40c000c003180c010340c0c403858014003403c0d52803003903295038110781406802c0000c200c1c541c880c503a1000404010203407014805101c1a1945100300a000d035a40c511011140300350f104a0380000c0f01480b030f010100ea07650780144400b520840444000d413945a40c0c504128441e43d20801860340e4031041c880c1415054012200f50803443c0c4d16079403031840e1020016100000041600c0c0c01143c0c08aa101c0415104100ca000507100140b403c206483e034440d5405540c803064041d0319000e030b0078044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 981136357 1250 981135107 981135119
    0x50721020a0210020d09080403050601060206090c010c020112091b0f09020408060106050c1c0e01030f0c0206070c15020c03070c06050a0903020607060b19151106271603020109 77
    0x8241c6000306440d9000d0075400c1c89000040c0d0280d0061182c0310181540c52014100103a412001400150b00c11009080658940b00029081050080c84500c041d0009170142c079560785d00a804185869090074070740d151813880c0441c5401007071070074401400c04810008402c080c0852a19410803900411001c68551740c49850040c10f0b800740348190052a4801d80041c0000e90080d000f402c0688403401c2201c450826070004e01d00e01e000325030041c82c0414695000458956854012100e11060300b2205009007420400000d650700c3d0010a4601000980c0c2e0741182042001e0081031000f55014100303544a108281c3c01c3c175181d034060002210000414a00002c9507400754085d91240001e64880510700342c610713020b000d011390114504031604d660b500a903e80307903036403240039580745d00302950a0100c140c20016107525454801c000c48080c0015a410f1654448000851a40c800760b03501640010740718145091032041104810000789d4001c003c0344180420004c90340ac0100ca0003640e0303010b403c5030750705 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 981137607 1250 981136357 981136361
    0x30506030d05120c0913020d0213090b0a0e0c1b0c03160f091a100c0501110708030604090201140d020a020705041e320f0c092110050721 60
    0x302d002c000340d00c40015141315481000d46920640548034086c80418104140d0403a800101852009680812003010240f1241502c4e000b412480000304030031506c00380000c0210107544600c810f0118040005001500c105003034502c0078517600c2c00d11042c0c1040c407070f0350f03900d405498100600034421505000e00e47c1071103258000c212202151844d00040c14003d004000e4081c2804c1d040c4050441084a242600c441c0310003e101a40f550f6041580901c03880c2003803d64486203a8000007071000c4c8140c102141903070040380c1e00039508403800511900d5510068403080080c6600e2103442002203042e00c0c4500740e54008050541d00c0b0303400c3e6803a194a5070108400c41d610341c3c0703400406101c07180508000c18655030002222654181018080254042c4000c504800078140b0054005102e0300344101c1d28400640a0f07003295611100c642004070001c0860000c0d00090303408110406030005545030400c0604c4048400303540c800090102d4905100007a1040c1001042c4112007034140c100200b03200543c2c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 981138857 1250 981137607 981137617
    0x3110f0c10020c0a0e040602120f04030e0303190c2d030801090603110d1109190509030f071509150b03160305060705132103081008031606090b07030506030d05 70
    0x1044004c0250030700441c8001c01d0002001140e445500704282d00b0903221851900703110311490b0031241380a10741841c0c001c20356034a422000b8045d50003400506e80d010b10100e102a2019941d1034503000344030040c200b903002032a42140c07450000c0003001035680030f902006122400540a07840740f00c0e0590703a4503640c5040300c105200140c40e00301c1800120b00341d031801d00c4084072030038015105007090b50000c2c00042c0c40d88105941078281d54000b039515000803180f0f802215803043c1c940c0003850800241501c10005480390140c028144141c0890b1139506445607848043e809400c0800111115144400e0313400529180c411188240300300b0008a40d04d80380c1c0300e002c0007500d074010b01034007130342d00c030180c0030741d01030b00650726982c4000d2070f80d1004190049200008640450000310410107481039060240118601800704552a400c0c24014840e601d000012035140c0754000c80c0503010500d250038404001c15080c8001031072400f102c3e040c80300450f4150001406004210159840d116894006991500c21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 981140107 1250 981138857 981138859
    0x11060405070b16020414160314010303050c0f01020706060e242b0c0905071103091020010e010522232e06031e03110f0c10020c 56
    0x40d101c00d21200b00c0c1640034004a2a40606940c00e180f031540c00102501e42c2c4080070409488600d041041d501c40055642c0c1a00099003410401c180141c91843c0c40c2020500025051150000340841100e00c02c002c0c0c45070002103500215110102480c081c40946200d10070342d2461260342d0085805402482d104003007140e504500100b4248422090112000100c035040001c0000b07129031088808a400da5013010510500d00340e1a601c2c24440024100e4030083c08440130001c04800088550130300001300d410b110300032030340443d0b03a12140701e040314490103548112a00f030141c44c849181c0000d054005034504402d02009110300d81da589219405084500d0070b40d0303104465030414001044440c403929210038040030790a40c80307050a90742180340c0b071440076288800d4019100d4042c90800321a04000400800301428401c261a41e1610500f28940029101d11789202204050805000300e4808000325004001c1d5094076014200894468400b00821402805103407031400c1c01074808070300301200b900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 981141357 1250 981140107 981140113
    0xf23030307030f0606030c0f03110426010c1103030a091502040b0a080702060601090e0907050d080a030c0203090d11042703030b04060317030a111819060801140a120501050711060405 80
    0x11b5108c1c8202d015180c040c400b0f0b00c01300c00800c0041004091084030020f1032190034550004440d42c803441908451120343c0c200d041286601019110817800302c1103a8028685000200d0400031900741500c40a844c00070f803c000600c00100010103c00b00c0000d0060203010392a080d85c00c0d50b8244081c0e890b48821111a80000d2800409005850302400300035080400c00b02181c0c40e10b9241c40c00304112004454090b50381000c003195130014030703a040c02402610142440503504280302d24010841d59a640c540c0105401888580b0598036100d590007110130180f001c0781044d0b20002140c03940c4041101130b03021740000c0d09000c500c08460401d40584001c90354400c02c104282e1104940d042115080a002c4001240e100c400c004e4080d40040060100e03000c030040c29a0071501c444080010300081024030300088546904104002ca03080600301e41111542103107440f0000c1100009007000c680d41e0030121441c501e00084105002c0e05500840c400c0016440b405001c41040142c075565039401c0300c00410943c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 981142607 1250 981141357 981141377
    0xf071701050108241005190c02010e040905190c090f05090c0114070c0306050106120506091614040f08211e16050a0209060d0f23030307030f0606030c 66
    0x1541c010a00700700203000f62080130910a0703500113030101180d4080040001c0022a40c1424038a03a403403090410380c0e4a04198401c001c0c01e070f0001c0e020061030101c0d41c2c0b0541c7d4403000c1c502405000d0040ca070b809502d1818100c0c1d0701c0d100e454a03407402101e60080e0070b0720503c1d1625456150b00e052049078021502140204075010300c410044441040407240380741c402c90180b184000151141d4030100103503201c1d480208980d81810401011070f20400d6041c00003a00345420701c1600e882e500c08280d00110001300480c2000040d000c1922089420607049800d04c10014001032401c424070445800c0d2800c1c50140d540084500010740811100d104041a11034000c001c5840b820810340f841d2008450a0704165003004101c29064030700c20302c3e41e9410b6655400001e01d5400314681ba10f001a808581103a80304d04028051701c03069000e142c00a8024106060340c07984008500040c001d2200c0381007a103003269540d01d00560000c01401020698030741440c144030001c2201e60090296682e0003403903545140c818 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 981143857 1250 981142607 981142621
    0xc020a08070b0c090d0503121608040f02041b03020403061a130b01120c0f0206010f0b09091f030515060402070b0c070606180b0a09060e070f020f060f071701050108 72
    0x201001d030180c0d0205504001d11034450300d5060190900038080d5002e540c41d49020b0008ca070400000505040071000100110f0182580207090a50040d8120100051850b20351022600a10400f100440750610300308410b0301c900e6140c1c00510a03244601014410b04002c030031010400c444080d07000b80d101d5049101228803e009a01814040c8014501880c01c10f0401200c0300407074170008503900002d480a401d44410b1901001100d00400300c05140c0b500a41c035040b291303203036409408034840c8552200070100d55103c07510140d410007850106210440389030b0341e1500546d22056400815000d1307003a03200240072844e051080d40c41007500b10200490607526007000c0d4120741d0001c030080b1252692000046005a0146101ea421941c680000138207901f102e02000418580e80c1d03c00c18829080600074445280c154094540164007402c103946c0201c8411002c1c1c0c1429101442c4842d5403241000b0440600c104984840c082c0c45a9240d12105030b80c8600d1440c0d002e6024000c075070200301008041408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 981145107 1250 981143857 981143873
    0x906030d0503040f080a050403060506122107080301170d0503070807111009080d060b28050d05090a0209090303040b010314010f0e072c0705071401020703080405010c020a0807 77
    0x1001340b090008240060443c1d4500596810400e1401c2c000360020500b031040051900c245a00315504445008803444240c115a07a20040113119040240903079011812480c5200c041d41c20050b1b200c24519280c0da1194054044d8001000e00e50b0300310b110302482d11050034003030411030b4000d00c2c0c259a1450705a0302c030401a5110b5095159040a52046010501c1c03540d4051203030410880c82203c0c115943c24000240301b0649813549c110044400c070030049d0b030044009522490524621202e00002d1000c121501543e80f4002c00f2000402d450900003004029240030510110b854800c41c3e461006407200401079079280412100140008000780040c07020610400c60b00c4030b04811a400441c00100c2213600c80140d8002a0703040c141680310b40b800780141c007003500b21b66607004442e1140c108002d88243c0481803850f030150500c0248140001d040c81400440762002904c0102030000f550344015600d0700600b0003e04840a4405510380400004520b102140c000d00303854206c5202800c14000341c1b81c48030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 981146357 1250 981145107 981145111
    0x1203180308040f2108040b280507051306020106050a1202090a0e0115080601050306011508070509030102040e01030f060b061611030106030b1807080c0d1e0503180f0906030d0503 78
    0x580c4c20030031900101408240d00f510750b1068040c1e903441d902805c0510b0400c40d034074030107011400d421000c10301c0c2241400d401c848010742100701a0001c01c0c540c0700c42609940500c1403031007007808010034001c041030715034054000004135201594100c81840d0740d52604016101e03400f6000354083c1458002c107501c48d08540201070408203a4000240510485c0c445400e248080c0d4850b160507001040104184c0c5018030046005245450b0f52983d005040301c401001240010b0010080c08408901e1180b02e80f800d60642d03001d08682403020300b281d6182c1c10300419844210104a5400e814080207001302e040ca5015100f01039410300899505034903680e2058103441c50ba071005505996640b01c000042071480e0780142c0503034a100b030f940c00b4404e0b1050400d414000d0740e800c07190f450340c000c00d000390040d103442c8000b00b9155048001e0600011500819030031036166664041c3c40785c0b0003ca00181c0a125950380c2d19000388081303507100012a08141030061943c1d0440d542030345900f1001d032411845006074019a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 981147607 1250 981146357 981146363
    0x4030c141902100909020c0d08060402120601080415050f01050301051f0b0d110f0307110d140a0201021e031f050a05041d0303010902121509040201180806041203180308040f 76
    0x481c00b0b17034550161500301e070001705602050b5440603d1340f829554020403220f07000403080c0c3d001d5180c20301564501001079000b5242904020302c4100190034000c6503c07005079030f0242a1428072550801c180c0c0c1c0c15103400b0078044c03907110703501e05008075049074003070880c2c41c1008100b500c080c1109881c04e4600b481903040801043e00880e241c0021086034210078000342101c5011149280c3c4034104040020455032100c80c3c018555400303ca0001a0306030450001404900380704516542d4940104049005e8003d448501d0004030488000d81c14041c074200145100d803412301c000202100441d590803100030090b110306908008081014403007401d00ba007254840c80064000e1500c020030140780c8a1a69000364482d28040b41d0120b419451150080c070500c1d088201005030030712142c00c5a000800c061070180c030003414840d8100030301444001041440c80140621419581d00b0324150a221044001d0303031709560002464040002e0060308040303031011255402d0b944480050361199511010400316103025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 981148857 1250 981147607 981147617
    0x5090f071805030a082101082e0c032a1b0206070519021c05060f06011e090e010927050c040c17010e070c1e0b04030c14190210 56
    0x2050b241c80420644074203501c10f80c02c49681b040480700388801c440c4c3c92034041c92902c0d40c420040158200014452812241c00410341d010041401d07004039101101008410b4110f081140380c145040c5c15500c140040002c0400c041036088055030391062035081c2c0c001110103d203403001240f0010700c00c40121a03500d440503144601c0c00b071103520b070b1502e040a4000b01030030b8208801001000c43c1400710329440201d07107152001100c440280e50b250f4440301d00605041000b54083e00055070b03030b80b150803400c4400d0422400c803114070b600e90380001c01c0c0c40d04034051600c120609034000103601c01244aa0b0745000c88901070f48040d0f1492200301220070203512800d40d103074030544d00044c046550b00d00c100d091100702903c41c48921710408041843d0820b059214010000c0c84201300700f15203801031109840c60344e010b0306403001c00428241c804010300300180c0c094080d1648208000806800c0340c1c140d407025018541c0401c10f6015115415610b5020900880d0310380c5088000d84014140f410b0100034000580c100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 981150107 1250 981148857 981148859
    0x51e07150212150a09091109180118081606060506162306160504030c091a0a03030e130908041214060601020a060c170406062c01030206090607140106090605090f0718 73
    0x300041801da4104088121000c280d0802704001d21828a800b181469114000d0405482d651803600408929042d2804484042c4041068980c4280d0140200a040716101c0020b40203007003008004500485400802c0f0005c914064803c01e0112000d010440040030f881e0b85200f03c0401e42d201d9182c43e1300038003005100120001c0e49001c3d060000d40641c25001600c8442c000c4002c420350300c0c40041c240214803148007031010035441000c004900d07070141d9802074100f0f0700c051100010480d004010301a0100418045a101c03c03407001110390501641074504201529074110b074440300c0aa680a0141e80111050000584640c0181402c40c4e110705003101074042146010b0100030080301c08680d0555503520038403901e07038071528114804291180840014500480200e15500107000191081d030010a0344160740c2d40706400c5606090340304c18410308424030b2421441c082d00040c000c18800c00c0c00c0c60000310706400c120855030f01c1564003d40c0d8031a141c50b032401c152035402c1c483c08032052850041034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 981151357 1250 981150107 981150109
    0x303110c0d0305040b0f0f150604120b04030e03070e130c170d0206070f080a09060207080f04050907140340150606051e07150212150a090911 62
    0xc241641c0001c0d4038081100c4c507003880d2030400c118004007081820758280b0140400180340d0840329a0000a440c0d94000442100000403418021039101810b0407524614450410481c0301e4050f0080d0322035180e100b4001d03100e800309038841c1c50a01820081d030010500191106c140d0410401c2c1720760090049400003616441030304040094a81014902d0340003211040070140c1c100003007503100c00180b030103050101040324000c08104e0007414240c1c0c49500c654003403007403200b10350440b40c03416400481c42d030342c1d0744002012402c541c22500c43c1d40d00c15140007000564040c0101c0c002282c0c4010005054555643c101c4803020b00b1405004180c10101001a500301d190001801c41031150700841c41814095090300c0c0c540c000040c070686c3c4000c13460808a08202a035004011b4401c9070700308000440700c00d00d41d90890010f0f40202c0070080c290302c200110b0b81e0421301c0300e68020400c2c0b07600c0e800d0307a440d90b0ba12203400301c03440890500201e40040302ca90f810001984254400d4581a116100186001ca1a20 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 981152607 1250 981151357 981151363
    0xe19060b030f0f06040c230f1306030b01050405180901110a050c07090e060103030c06110301140f0d0c12080c0a1a15101110060806070905011107030303110c 69
    0x166010203200020b420b1101281840d1070981e03011000300da09001d4805100700c028100701d541d55424120b13042e41d400d4400c000c5500b90540300f06a0000243d2500c8940b00c051044110140d4800c08010071301c2c040c1c8000c119440303042264140c40340070b08031000c40c468001480d40030800090500515541e140e40306800941c4c02c500510011501c0d660342a10341041101444c102101a8448201c2c64505083c0100c240780100f08941100d03018200710302e205d1100d0030319101030281d1440480c086200040040388034030000c0382003405004151003a112456501042c4115004201c0000e0300402d964501000b402c0654094a25180c0c400c40210b410711741c08500c000c0c034144030400c04a440049502d0740001191400c0516584559940c481ca600703080641c3c00300b103118441c405000100410f4604040100c80200070200c00303005025001c008a5503a0071a80740c079107030b01303070341040004003100030008942d8404d0811f0714110a5601c00303030001034510360b030942c020004209241000c080c103100707004d4003002c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 981153857 1250 981152607 981152611
    0x90f03120f20031c0b030a060b031006080303011a270109050a1202040e12120a140f070e010207080309040509150112031b0809090601020304080304030510150e19060b03 74
    0x40003561103c4c100c280c0c003240e03490390340300c0301e5941c510f400c285680c030741d40c001148041542c0000d4005000034507034010908248208400109503400c5c0140001c03900b43c00030041d070407200032042d8040b00342c03034030301792a041e52140486401c038a03014000240f15a4207130451481c007914050510fa00d05a95030004581b0b180845e6010041560700c0082542c20f5003818090180c0d0984203401a0850303690b00420300070340380151031013030128140900c000b42042d5459805049044a00c1d0903d2401e850150b015000c0c11a00703c0381000001d50b00074001502c2c1d40001a040c0584990501840c101039075901484000d1030000e101030450f10a0b201e114107248000f0000354081c0c001404600822011420007501c58809204d002c07040000200059020603c0c200c25110000c3d400c0b6040d00303181c0c9a030340040f861406503421038041030000080010030844000b130310340c519480c1031505005104080300324800e1100544034070f90300e41d0900c500040c80360003031500c803c01082001c0700014403240c480814207420741007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 981155107 1250 981153857 981153917
    0xe2b11061c050402041104051008090118080a02070503010605010507080c10020a0f0e151602032a090c030112031101020d060608061306050a050420120403090f03120f 73
    0x600c02c240000d60511b4080d43e46200d0200380d400c1d03d4945440c020a0700084015004c2042040010100d0700d01d45080d00490000740c0c06215121203e80c0c40e0405c1744441d44008400000340c4200540050380382418004c05044a1050312403a080c481a0348400480d03a0100d92446c40c903004440400000c100b440c800340c00c590655079104504502e6400780174200403400d0001c6841140c2940041014600001c03c46219404150f40c0c6043e0226030b2011925141c9074682c03850a1080101d4901006068440c0440107d8400c4030707145c2c0c1544a031454102c080c4000e0040c2d103a02c4040300d9182e400f01c0d0181d0f000b5074058084200041c900010300a024007100c83c1d9030880d40000b00300c1001e2013000c0c075045515060602c1c0da81c0003042041c1c540400158001007600c5030314011902c031003462045041c0700301840201041403402c1999400700402c860382600701224200c01095030250041428031041c0000760a5a40c440600000003031024030940387d100c10f541c40c580070810103043c49140c0388800210300310000d45d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 981156357 1250 981155107 981155111
    0x30106080106080304060807030203060303070f0323030a0b0603040203100e0712061e0e1005072d0809120307030b28140102010c0c0b04030512070e2b11061c 69
    0x4100103004016107c05485003040500520a00c032265601000f00c428555000c0c0400b12030501501c1d054a843c0045000300501e00e02c0e81d5030f0490780c140b09800640c40b070616558200000004101048080d0206071406509a405440b0361101c0440c144d1291410030040c90031554040d41ea80002c0318403845010b000c4506684401c1210000c04400707800a12a60f04086c0500c090a4101c2081c0da42c1d220f01400000411348403404a59568080d05a141000c00c06d200c8119500d96a11030113000481007414000000e8440c00c0007408084002c540406021001c1490300e1a607103480310110041c0c900001d80c2980003010341c0980500c04031000c180324a105010140b10019403822803001000da90005e0700300e040d641003281c0900225404a043c45449900624012464490f420220f80c1d0740075182e40801c5205a00041c400401d400c0010002440000c50340d0200318140c2580d106807403543d4254400841200d420101e0018807010a90108014050704407810711800c00c070210090384440084c1d0301141e07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 981157607 1250 981156357 981156359
    0x1503081b070e090a0317090a02090a0b0418020f06030118110d0236060406080a0603050f03070519081602120610050109150504060f0306050904080301060318050318030106080106080304 81
    0x41e00408440c04054521105c000c0d10710b00b440400d51100da112320024881c014420014480c24456032003c59100d00181c41040360081d5041c6a03410b841403030308180d100342180c0103504103526102c0c044034140c0302d03e01c8000c80081031510b0b180d4040d044025503211843e401348110240e4181d14400b40158100104d403c01c100620120189140c2ca103c0d194034001580d0807003200d07042c0d141c0104442c00c580442c0b8000d40d241d076842d482c000082516800c02442c4e400f450070300d060421000805054214081c0080d10780070a040a580c400304d820030034000300012005c2c400710000c0811003000152650004e041c540201c07030603000306410083c1c01c1f1200314040c0b10948060001d5644241c1450240c00c1ca0901ca0400d082d0a85010b041c9018a00c2040d082044104901611714801d070880305c020130021b418000942450314160b10782d500240a4800001c0c9850702980c000e9210702452510580c002012b1071407c0741d034981161701c220861007915010f6407115000241294240314000052400c600656299 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 981158857 1250 981157607 981157613
    0x110a0219031b0b1602070b090607140f01020406110c010e0402030408120412120207020a0909020616050c01110307111c0507030501140903040f18110315041503081b070e090a 76
    0x181c0402400c0c030308550120b403050100c2c50f1f2840850f45141c5089444548425285c40d2210b14094207546030407040c061000c0720207030400150017500c2503404a0b111400b2200048800540c2c038004071145500040b0001809482420710340e00440d0024002c41c8100d103001c0c80e1441e4100341140c150740840c0c04420b40c00d10680d419038000d650300c03540420300805500e8041c06030002007241030300340200103d51780e403000e0550455540303401307c2d40e405605408114500f103290034440d40b0381c4005c100301404110500703090f40c286000442115207480e40064088480c45142e024003800c00480741131008145d10a50b540c001040041080b00c008502c15000410701050404141c1d9540760041e020050542c07040c80148004000c1c03c050030700340c13603034404940d00c1040c1900a030781c050300e12045549038030180003040c007911580d8014070fa80310601c16501803248202101c040d1810030401e1001030503150302480b0854139100803a80c245400c03903100341200c88454a0710071001c1500c0040c0c614001c2a40254901410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 981160107 1250 981158857 981158881
    0xc09100513021b07080d020703150e03040e0c09090c0a05071b0b160c0504090c090903051c0c110f030405040908070c08100e0303010605040b07030c0c18110a0219031b0b 74
    0xc1c6c440c140c4084c0c4546031030f40c1d850006841d402508001081c1d01c0d030311007610714503040050f18024040545c0b02001030510f40b41c680c0a50340700b1390bc0719006071401000142800c4818046828001c00303a0b4032145880c03036648400a03684040404074000b92050040001c80c2a1100054108804c0352000c80c0d0680106140114a0081590001d4011401c080c040c0e80404c8000301600115050030b00b0118191500d0f140c100c03218816511140141c140a08104a4802c0c035a48440640c404a4070303000c00c0a016529840e07600c0e400017550020300e50040009005e01c3c10690084032141d4824030000381001042d03079482d100a003540d004002a540b108010f2800d500175400f4203906250304201a5155505014000f4030070700c598058400f40100000e03e0108162250300f1036001d00340c01407107040703941e6158035508440d5001001713542100381c200f1420307480010b5001d0848d040a0030a400910240180c050121000e240120701541880081c0201c125644402111035015900c10300c8020440d103414503c4444c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 981161357 1250 981160107 981160123
    0x15030c13180e0c030f031c09060614091e0a090804090c1e050403020604030201030902010c0f06020301150e0f0f13020a0f0f05181306030f05030703020c09100513021b0708 75
    0x104c298884050000c900002000b119600058500824130500200b04118080c3c58482401800c992a1081c00a110144131020008a9500f100c42003010303150030740701c103919030b074007450703000e6003c490305d001c90740c00700b41da40c8000161031190b10454102030b5240460341c1100e02d01501500440c08080e818410008803030b4166681c0d000a00b4442c1c00e043c00c41e0086100f40c000c6002c02818150380b02007020641e03006150b0340c218035510152240820b0f04d0361401c2e41c0650000c0c80f95200c05008443c032006500d0081054007150f4001610040c0464418402c0102c46080201040c0d045001c008040c00310a0040c0010f0002ca00c00e45c540f03e85ca028051002044448205d0100e01001014012113000343d1000190400000d4100c030303244282110400101d008209540c00145514030b154040d00030010044050201c00c0d02075000d6034400001e01c0144110f11340c4c100c488041d035014425041c8118a0104500c90310b0001c014401401c0911084044152a01d5003100100c99844070108100d8403a0810940d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 981162607 1250 981161357 981161359
    0x70b0609010509090604030e0a21022115070315060207050901050915040c200705040501210f062309060711031e0d1107060b15030c13180e0c 62
    0x145611302601000e40794440a0402800c020104141c1d1000e595140008400b03402e002e9100c071441010702440258011b46010101d01034001c0800c0821030381542e031200e000b208044409404100d220144132034203050014406e005165032a0300c0d0034100c001030040c08000e07200d203800403d10079040c00200841d03f03070140e0103184540c0e407a204102c2d0707211041c03001b0340075404140c1e0081041c008202090b100c0c4007006402c05807070341c2800020020340740300140c000120759050b901040181d89a114250700e0744440e200e01c684801001e6400000a240b00d61440602030048000081908007404c0315015000c8412034190414906024010b01c00414014150400000e003230000c40e0042e1413082603228010a010f9040d502c1011070f0b2600407054540c216028284042420050000e03803403208010b03604054001d8592030710345501d007132440c10500506c030b00c41301b10441d0040c1103548007805400c0300d40c030144e0220001060814000381c591034000485d0b620311a9924042440c20030140382c1450280702015203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 981163857 1250 981162607 981162619
    0xe030a1712010b1c0213090515150d0e030f0a14040b03040c0905060907081f0f06030c1701050108130f0b09011a0109030b0f0408130902190806130f0b06070b06090105 73
    0x4420802184207022101c1f03000300031401359074203204078081500044009030000080604543d801c0055002007108a20344a0b00300500441101b101d40d480c05144186039414400b00a401282400b079080c0d222481d51a02c0181e103000d845c4c1d052840c55030415030341150311040d801c0040c00120114081c583c0d0149042d00c99503881e2408290003030503040040c2c0314024a42041034000007054901c2c480c040500f036100401c40206079903c04c0100107002410006000600c040007407400f2090080c3d60310304032601659110400e03240d00e10b120815071b0a2080440d243e8a2000c040c0000851244c00a846006500000284000c04015130300c100d0141000090411003051001c0c0001044201c02a03003129031954549100e5440c1e181035aa01d04c681000d075a03400f1907403078000071100c0554008110403420080501c0c480e08a5450039240c2c02400d48081d980076140c508129400f841e9035001000c01d00d090403020032000490f60110701f0742c0e0321802c001c0c0c40c448802c40421820b8240300d0a41801031400b6228 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 981165107 1250 981163857 981163867
    0xa3e163201061d060a0302011d060c0d081008071401051204031d151b0c0306040b0a060f180b01021207080c0d0507020915010309150507030c0e030a1712010b1c02 71
    0x50100c5c3c80c00e0200a040c44880b20329004144001040c1c400e40140107040640d0754104d02c41565a00e921100e140c00014405034001001c41d0103d83c0f280381290000300c01441203905140d0034004ca149100780c80c40c1001402c0c00302015807074400e00400d0040d0b0082d204d00c00013074414034040307400f0748044250600609a81c50100ca050b000001100e4000d00d02c9880d09254a02c501402418070311034044440c1d041c8541c0c01404207104610090350701030401c0340001c2101d02da655440e0b0803000f1041c4140000d9061070641c607880c4c3c900b03581107a410000144140c5d00c40f50020140101c40350400c0405403180303000416000803554080000b203101c0c555504005061581a90015011140040c500200e1005842c8201c025902035008541c81c1d6034003801d03d000440c040701140004080072a5a00c00090810300c010000034066101c03405036182c043c01070080d00c01d042d11074200181000034804248001003000962105a0302c0303119019007450103c495440c241c40340d5504000003600c0c920044076104005c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 981166357 1250 981165107 981165109
    0x7150e06071b260c07150c0b06100201090816050c03280c08010f020909060f0108180c091501091a0306090a3e163201061d06 55
    0x1414100c41d8850382c40602ca001d561205445410110100000c4140200384c800381454040b4460059400c40070315515050359529007143d01124800001d041d0082e9100030515505200c103100007201e96a00002ca071402c495075800040354495003007017000310209510201040018010350000035030031001441301402200c064405245d850a40710304a05001d01d0210800082403a030400400c0b50700000c200d10705103500386601944c070811b8110b2241c040f0100240440c46c00110034054010180d4480c03601d6902c04a9a05030000e001c4100782c810310400036002202e03960b918140788101c000ca2240f0b07035902c0059002405041464001b40822241d6183e102080382012013507980c0310130100c505406035120003003400002c100004101405400e0710300e1100001c9501c00c2c4144204d800c59421081d403d500c80d00c460200d0080440c540744482850b00400302042804070510342502d4600d00c250350140d41140140080e2410a1090360340f40d44403a0704101c80b514488800041e6840354202c01014603080e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 981167607 1250 981166357 981166397
    0x6020f0c060f04140109170703020f06030f01090c09030f050f1c0c08090406080303100e0601030e0c1908060a0509100605010c06050a020912061008030c0a03110307150e0607 76
    0x1c01044c4210049012840c0180e00c0f42e02507a004110305000b08171000e00403121140c84503500d0105900503446600302c080725082407030880380b09040040da0302050364200360201c001740207103c40390000c10014440200104840d09400780f10240314000410f1990743c01c40949081c030b601c490861210686840191000c65000b03c90b2aa0042d03120805039503440103100041d004001301d0300400c00750300c0003108100304010a100d0070782c1598a40d2821510759902e0340011420f907482440102050340002402e021981481440c0c4280d41e840e0b54103804609898400151600408440c000c2140307071140184842c0717540c103106654094025030740900c620390618001030500700f03500d8401050f40b0703a80c80004002542c550f0503558911001010f10120b200c201c10f50642e1050b06035000c58840c184801c000981003000021640741600c00c0f0060300340f04c0202e071815956a004a00c004c1482e020410140001910f042c51000050520201c0045c0c00d00300c021449180250007013400b0107206810303052904002840d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 981168857 1250 981167607 981167609
    0x12130c030809031018061a0a050f04180b0708070c0c031407090e07031b03171303020301021315090e1b07210f05040b040605210106020f0c060f04 64
    0x41c14403680d910380140840d00e00100c920781c051106142485050402d0000e28240310034a0082c603041c0112600406142d0404c94403012507903002c0c0d4000000c2007103040000f0360082601c40184002281e4900c0b104145030664100403c5401705150b6003041022600a5481e0703130007003820701d4804285100f035a18400740c11694000981003c07402d0040e866007a03030801421010701009072040c00b542c500e800c04565100d90902045030003201446410160242c40030b4a40128dd410050340000d803404449001c0e96680400040d2204045400011026841c00d000400c000c9000c0c07140f000655203080042040143c2d010b000700200301700d41c0300800c40b0f4440420180d030050314880003415403000a00c2112810f210b820401083c520204103604940074642c4488401604651a205c1d600807070100101c0301c0380704034041e040b410b507400e104c1486018414400340c2040c40301c40c0b2845a402c01441d95405580101340e002c10016402082001d40c000000d1290100100c025904a03040101c61101c0805602407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 981170107 1250 981168857 981168863
    0x1302090a09050d0c05010e070602070602150c03010b1b030a081503062e18020c0d080403020d080403090506030a0501080c0f01020c2b06200906090409060209120312130c03 75
    0x50138942031140a500c4144400550005c44000300c0d07450300060745640544c4500400360180180071086100c40003041449a0010717646180b4613820b010b41100c081d00020f030741c028821592004030b880f280040008080c1541140c40301c2ea01854003001841c107540940314928000d030003e2092007202d60324000522800010f0107800162080c9072140200707a000c542e030108100318040d818400c0c0c02e1040743c0c01041501400425603001c4401d03040d0960301c13401e0a40300200140d000300c10746010f8522920f26107030080c1c070034644140d226a560b00004d581d03030020b8521000081da81c1c0c0042210000070001850b07100d10507560345204805080000c2d458a0482c00aa401440c25221070071450511110701144521242c9500c40c407403c003800d0445c0140004c0c4030004140c60b0401c41c501c005580700e800c0d104a40e00044c61140341c480140140005842a907008071071a5801b4080d40f002556424013481c42180b104008548850204041201e060300150070107000b0741140c103009000c01c4884440200396a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 981171357 1250 981170107 981170117
    0x30301091a1e220f0c030e030d0f11030103060c0f091805040807020d0b04060606090e0403030b120f010c140f0a260720010c02030d0e0f061302090a09050d 68
    0xd50080891222424042c541d6440300d6000307103c00300400954004003110403490001c00820032a81e0041e03080b11542207440d00258414451108040b441e80c00a9103007008941000c18101c0c20421040080e420a810850750030342c581102c000d50340e60019074014040b0040c600441c0e8540b6018507800b4480600003081c2010b81c03201c0c0002e05001c6072000300c2d04215405000140c402d40c0c036003012003d011054030100d03240c40c14910001410392060b003031031080c3c45030190181c40c56100c2d0f0740c0c01e5009044418000c0d402482c864050031318550140030440c04400024004100040c10000080070302e0220076000c0a0003006000b080b1504204000b6209450324030706181012001c0c1150440e540421a5040201590145c04003e0070503445030320140282004580440c6000f2640704503800d0b18407410408005900500941070728045035009a0303109021582038440002902c042d41c1d04040c0704840c5910001c4005070300c0c90460074881d0346950700c007101201c2004412081c0e601d050b141c801c0a41080704000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 981172607 1250 981171357 981171409
    0x31031d06180423040c0e09100e39030318240409020a0f0203090f0919020f04051903050a2d03080912070302060619080f030301091a 58
    0x80c45543c80541c0c1150459421100a4200000e01001050840b0300b00c4507028019000181114050700d03950041d84003602074248080d248a80c40001c01030f0010302d41c118410554481546c90a600d44111030a019000d128036070a0464018103010030b8403003c050099008003d00001103164824104091f0b0044032280d00d1101081903042d031900345d426810b2096000000c4c00280d000d099801449800c4043d180d0b4440c501c1e200e00309903182d009646846422001d610a40c100d41d01c0c1c42c40c00a0f50229205003042c081c40d9804007544126001a00502eaa00310000f50511180c0b40032051013200f116110f007aa9400e44c10340d541d0680f54106000c00a101d80641240441000041c80d402c1da4000c03044d02c440e2014042e0750400901030003081d605180d550051a88206581c000f8130708940d0010741503001061540c0302c50f000e0000d440305802d010200e040560401040c40130080c080003090301d010300c00441e240d50605520030304540c10103032100143c541842c0c0700c0055485140c0c0d00c500c3c07900000c000001c66 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 981173857 1250 981172607 981172609
    0x312122d0905030f030903071104090206070b19090c0306060e01121e0812060f040b030d0503090a1208150406030317060427140d02070302060331031d0618 68
    0x14000c0c1c0d010070844040100c03c000c4d80500000203841d10502800310a209d00ca2658207100850b44407080207500440100083d8001c602511941a0822094042605442c8001d24003004440041e2001c454040344e82000b0014010b050240b00043c2114180541041d45420120403091102010041101910386007140e44464900003041e0010307000036207255200340840703031001c61041c02c0724024412907084194200d58145886507541020b000340003000d1080d6405002e40c3d00742c2004004204070b100b417820b45400104201c510606030f0700d640d01e64141c207050560b800b1030301c0030700c40095900641ca00801007011a900c8900c0c05410303c5105c181c031002c2d44405021402805591880d801da25808d0281d004109040398406007086001c3d0710060b0083d021005c000d601c5d1404813084100503444924107001501d0404c00564215024031030303e01030700030140019140484008100a6140d1181151805058200c42d0b520001d01030280560301c0d14400d030001a01c0c0340502c140d6421210000d081e50906 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 981175107 1250 981173857 981173863
    0x10509011d030303040b07030518030f070606090615080109020f090f061303030f02120c0d1808010e030a030c020a021e010302070503030c0d14040b010902070c0312122d0905 76
    0xd8408040c099075030305d1415041200c2544001d41d030b00c400013031070000000c5640c150366468211849401000e580f502d13800345c1200c450f81d0480071060f24100c1d030700e1000043c071030880d1080c000284100c503408481d48040c124080c0c0080030586c0701e4164180104480c11410f01071004072030800724216010104840000f009c224180a041c40e130711104035810b0030110506800a05050880e18a40d084544010a540d001d516602414008112540c8003000c07c0903501d0003550300c0c0c2d601d61701a4040759503013550390164600751100e0074642d85454200003900200244e050040300d4000d09680000c0503201c03040d601080c0d2074030b103080d0314252004c03100c2c040c070031141c1c400d40407101c4c0190803d04417900d80c2000794030b85c5440e1b07000c860080301071454005c42c1c114040d0f410b01c40c6231080740c200b046222aa0300c1c16106001030361142000302c0d4141c82c0c50300301000055038504181c0c00e0340700e5a03840031106040c2c002160101d6481c15074030f0f400e02c2284680b02c00311000c58804501c00e03807007a2070045101e002501e41545 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 981176357 1250 981175107 981175157
    0x130f030c050318031c080a0506042a0207062a0212010c080f0708101403030f0d090b010b0c0d0e040f14040c0905072703020907260601050901 62
    0x80180800911480d48040f6540810442d141c21400d5a54516268108040641c0c04c88010700c00b00e0320707400000c0c1c030034149503000550004015001280d2004181c81907072500c00380c402030f0755000720074001c0e81d070740168104046009001c0506100810303c02403244107104100b078005844101003035003010b00440d1106524004056130400007030200703040101010b00517400846030250140420000605200d00c5051010300580c1191030010041d4181101c151204400440003605440100032915040c10100014060b1490141c00010410700b10b242181d5880010307440f141245030b040c0b121000c1d460700460003400c0100d06080c08403c1200c00400b15015080069698002e10300c0c1022204120f01c07015141741c81240b0a04800c20300e152174040c02812110706580380c40000360380c0c4404006140068071a0110f01c0f10341001c7e0741140e5960b500103200703820215889000142895020701c04c071321400625045c80440607000a03c0348c074081c0b00080c600c0c0120381d14581008440c0a0320b0604000c030030a041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 981177607 1250 981176357 981176363
    0x8010315020a180815090102030c07031d090a051501091a09010c020a120b0703050f01150536030c0d03030207020a0f0b0316080717070e0d060b030105010509130f030c 73
    0x510490f54444809071100644031710480248004800551085418400c50303202d440c0f00034a1900b0000d054500b02c2d0880700704010300340048002202e01526940f03001810780f05030305c0003a0120b01454415000700c080140d00c620f89041c8410700034140a035050141d13810880900c041e1860340c403801e210300100c1c1c400001002c040e400420700e04000c10101341071100f0f0768120b8014181304a5a441d1003a08404940c4220b42d091560768190b8018081500c010303000410802103403911714144008004c026201520042c01c044089100034441501100c4d140003001600303c088001d00101c0501e84041000014405401010590300045a000715502c49080c4005003030030184403052191900b0b480b4610350f000b41c0d510000b100303542400d02c0c8403601c1808014807804103a030303402c0508204144000180300018081740140403050b001c0c0342031512641d181000341401150046580b441c4842410300f102c406800180c0618250402c01042c480302c011200d01050b840ba11310054419541411a41c4041140d002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 981178857 1250 981177607 981177647
    0x50a05060a240311072306060d0804060804380108150c070501200d05010f12060504030e030f03090a08010b0108130303060b030f0609012705090c031c09050108010315020a 75
    0xd001040d4180c001802090200e10441f003554a0728801c01c80d4100200074003c110900400041c051349104000c0960864400e071035421011003403802c00d814054242c40311500c1c401e201403c3c8525800b8030400707503004000c0c40010f0580145185c0f100002240010400d828080c400201038041040942c04900810014500452040c0040c00c0c1f004c965400070380300500c40c0e81000000f04045405100321000c58844441e54100d925407a507900024003001071040d820710000e00e00c501d02c191814020340d80ea03100484080e641d80d021070000c000300f080060300a00c0d45070b03140c06140072045c1d0b041903d854200c010700b488036622807910300d03044018004607049903110700408018051552507809001d030203400e04580048407682c03186000300141800007003402d244100d240310300281368016403045400403030807001d42e11800039160109292541c2524010014118032100c001610b0b48003142d040546005d2030301c0d10041d4519269844040d84040303184110550008801c50301d41e0160444281c000100209 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 981180107 1250 981178857 981178883
    0x809030405210319270302210303150103051f0b03040f15020325080a1d0706050c100504030507290103110a0b07082506050a05060a24031107 62
    0x1c1268001c0c2400c0b90b0224100c0808500d0501070030b018a0443c5c41c50426102c4494030315020414202d164840500408082d01501c0c01d410000303100840c401c14407806250204201c0c280010f00311040100207101e216403c0080086400015001c0021284e01d04042501d0761910305004003c0c042600b80201021402680c080034042c454002e075219441c40c200c040f580c46840600c10802410600b01400001c02c3c007000148452284e9100308400e240024200c02e0841e034880c240b528041c8160440401b0400104164580000c00c015100140741e01c08800e0015080070b03a405445400383d0350300101000f40e505d0407112160b0111100550080c803418900040356900d0604000300510a054a80158505000804c0c010681c0c001c60300601da2024495140040742074820303a044841407040280345d09582403020101d00b2078068203004047c14040018141030030400c0001103101d66004484114000f40c01020384041610345200c00c030003908001ca581883c40d03440d038100d4400c07140028056444001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 981181357 1250 981180107 981180127
    0x604030f05300112170c010e03030f010e1602030a0f0e0d0c2603030612071206020405130507050a2a0c0306050c090604090c020a0602030f0a05010608090304052103 72
    0x42c001c901c0d070000c4104030324140d1302c500011154008202000e4580c41c008541c034082c00803240000d055829003d400010035000045e182411030703100341c40e00b4074500c2441005104c06003503440c4058001000000d64040d040390000040d40f240244040e00341448140c6c0400e20400b07004808543d0402801403c040008130940380c12604442036000c4c403215052080c0f45803061114205200340d11808801c021415a13a84074200074000e071020008400601801d900000c21041045104000c2d0307206800c09603d5500b09030a000d8010158049910300d18213042c02d114040d5000022124000e00da45411202c11003810200815140c1018071b030840544110400000c0c0208011214180d901c50304083c401605d9107102a04103009582190b0740c482c10800c010007071041d103a84a56881c10b000d005440c511500c6031910700c00c81e00304864010300300a0200401c6200e56880c8501400350100f828400c1150501410042d0b507030256014a81c0145107409081d607880f849002181018610101220360f13038400b00c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 981182607 1250 981181357 981181417
    0x30f0305060d0f030f1121090607080f07060b0402121306111909090b0102122b020a020f1b1e090c04030212120307030f0b040e060907090204080604030f05 68
    0x800b005d000032280382840c0b1900c02c0100d540e115512030140b01c00300b031100542d019025a07020800456000004200041c00100510081c0802c0b03410300c40c4240c0c4644903170801c2c0c0151076440801510892042010403c1079884482860b0864418491062090030341e2404070300401d9803120541d040c0c0d1000c503481071240c3d450041101c4072401c42d660030200c1c03a5a85070400585110045403030241c0c00c90a000c942002140c000703810740f0004003014001d90801c0c5075450f8204229100c0401d5580d0700056140c007a03540400408011a8000300200305112060080608400058084501c00c3e54280c800203494002c806845013035481c001d14081c920700701040101450f6102e484201d00821b8080050450301c003000c2128050801500b10b1a841c44c4c0d54040100c0090855501c902c1100d545d510060781c06894600c1030b0750302005444018201070803c89101c500c2c0c00e583d6407000702c0300d0340100030501c0741610128800707412581c582486000341c1c031980e5044c0d03100d0062109507030700304400c20350a0f002e0303030f03401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 981183857 1250 981182607 981182627
    0x3060c030b030c061803030d05040308011a031302010e01050f04090e1911060a03060b1c06080703210203070215070201080a09030e010809030d1a1903030f0305060d0f03 74
    0x40d03102008100310050a0585805500007034035440b4805220744103d0070610300300b1010503800101907910703101c1d00f4104441190b20998082c0e002410050060041c20f414601c0644180d0b108003e007030951070021041c0f83d1902c04e0342c00090403c60400008617542c3d001c5c5040c1c5150071a443d440b50303291900d0722034003070003440c140c032a8900500c11242e40d000910000e0b00c846503c160044000110b0052440902030706038802c03810f0f042015580e12000400c09034000c06007010240c8402588400d4201182c0c02080e0b5507207400c004501e4000180800010b1b041c0b0f614000c2481d05440e6031803251025070b03c142d040d805070b260069000514400320041c1014050003c14981d4801d0320b403507803142c030307004110011544420b0006010503402144010258050422180e00283c0c80080381c0c07610b82120340f101c007520008001102081080d6042809034600200f00075840b401c92506c0c20f500902d1030710024401c640c000800c0062558035000320b0345985840c0b0718486881d820078040690420f451400030020010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 981185107 1250 981183857 981183881
    0xf06080c2e0e041103011a0309070b072307060203041802040b0406020d0906020303151917010917120408161718121b0d050a06050f0108150c03040305130306 69
    0x113050b2070b01c61031400b44000d4030305a0310020a0710300d48050312603824030075502c054400c000621034200001050000c0318020400544910301401250301c0c1040c4200c0e001158140d028a1604402e800388a2123030b000040d06c044075900b070503441110031a0a09800248140d404c0140b18500021340451259000240c0031b04070034882d035805680c141d44800c02c0741c490000342c0d81400b80546e50310700562603152210b19001c402c4094021505085d90305c0111090110201360300b910f490751a51000014401007024900500403c6041d052911302002d00340310301d2010040c4014000c2002040074a1110141221074900790703445a42c0e040c40780700c045000d400319040b25545c00039008070802c083d001410302c2c4481510b0020090010288418a12000d05800c03050b10f00c0c00c0c3c1c001c031150f035401c00130404c20807503c8a018020076002589040c054200707091000d0503000300143d64401e58801c1001035a00000c164030500104005d0780340c0e01c651500b114a442844544280c4005449000c018060154821007401003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 981186357 1250 981185107 981185111
    0x110c060d091a131205040609140303130608100e04050c091b03010303021507031e0f090b0115030501060206040317060d140606091608010b0a0e100503010503010f06080c2e0e04 77
    0x603020b241145d03184218040d0f60001265450104821240101d00c00d600c140300a05481c144400400304840d05125644803500140300c1c0303010301000660040c03030480542009205030381989019146e0950741d002000006003d5400d010021303044203030303030980340b4129003544100c903507a0b59503820001e5031641040f04200f1110620004600740e103010340b05003c1c0c11820202801c110048a0800500a248892010600a40b240720200019103840c1d1490702804801c6540348200040d4000181160380582050065502080900000c05c2c4c200c0701000c500c1e17141e101c4800d040ea4440b40480c0d00040c1e60003005207041201c0d00442c3d100080440c856100e104140c400d00d0242c1d40d1480c5013420905032408001c0071510400041c03095140d004014540c03183d8600b4030b40904c4810390081241c1881e2054143d001500100052006250a004091802045a505108841c10080e07556202c0302e440b00342d5407003500058010424886016440c001d440c909032404884408540e8010300455603010141344154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 981187607 1250 981186357 981186383
    0x303090b010e2a0c070906030c050306070c060b011704060207120509010c11150f03070201061a03010608040f0507080c0a0f14100c0506010b0703110c060d091a13 71
    0x1c464902218410b004040f6541d440c85507030410081001d02640c009800c030501080600d0343c1610400580008200c00100001c001345035042640700741c14107400c2140709400490a0101c200e91180a5095040e004a00083c0804903a001a5501c0300d20101099503c038a020130042403041e29030281c0340190059143ca0b6010b00c4d0000229914400c0c108000e01107506080c0d403401181507020904200380d000360180b01300c540d00700e0b00410386400000c0240301c42a400010052240d50a02440700200500b24030345c000412618441c41d00381c0814003e903810460042e00150a11038101b90112070a0341200a4601e602d403104c91050301c03500c01e049102d000b89004040094031009890b8180111008c682103c0170000c00d420400420b6404c40403810200959a041100415018042c190003480100302c500d5071002d081ca000751504691903c01b82e02600b00545821050702c400d000c0350069003034107900155a615900d031071080b14500e0f44400382110050010031400c003205103203140c1c005000b10303541c060700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 981188857 1250 981187607 981187619
    0x10315122301050f1e0106050a03020c070f0b1b0f03072004050405070518060f011107080322050f2209080705150c070f0b07090b13090608070803030c0313050601030303090b01 77
    0x1070028419100010300401c079449d01d5a109034094007010f51150103488031303595644003805c2000083c0d00200c00c4954005103154010503140700303107820303400c40c00041c04804401d0300076039451b80249503002d0005807800b4094104810912800344616500070410001420523007001c1d80c1ea2051402400e00030001040407442ca0391f0b05485403071003108001c00c6a28920400001150340e50b1441c5a0b541640c803441c00f004c101d511080c000342030100c3c1d42c080c06010906080312404043c0d00c2c99803050340901401c8182d10f505440316801e81b0707514a03c078140595900141000030f0700410201102404105000c035a04041100104440726046d103c150300080c503860700c0109552030f22422600034426400711021300e0008103031311415a0321100303900f044111541e541c4080181a4403030b0701070b00c135907094412003070140d441d80d4032445018108450040484604240c00d040c4c3c0c9200141185031a110003200051440c61203108228800c2d51190648880303507528900175000e010341280485180b07080b4400841d007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 981190107 1250 981188857 981188911
    0xf020103052406370206061c110a0803040e01050f01030e060a090f0b090a12050a1b0f29010909020604030803072c010315122301050f 59
    0x450405414403104281042085141d0380010801d14201540108103864004c0b051a0321060003202d600503985510000d02c02801c1c01c20085c061841980311003185504041d142087c1c0307407119803289004507031240e0400059184100c0341e0040712144400940851007501c0c1107050b034100c80082e200000e801c440c0e40b00543c1510070408a10700594410f000054640040340c00040700680a000c204603141015220859241805c90b07000c8010f40c040d00f602c100f00700b9180520078401c0d0307943c40d0541c100005000300070000480101d900c2002192503601c4014020740310003c00102d40c2c4512052614105054800c030540310707c5025000c0341c80c0a07400040c0e182c049000303001400d6402410949441e0850b41d81855581010384a0410445020380540c11150450101a010040104032148008103040010f041c0c5a041c0702d10440548581410041e921500b40000c000e640d10030301040d5200c400300b8061080c4ea80101e03c0a070190309101c10b100120401c02a03082c003035181c00582030921810001700d090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 981191357 1250 981190107 981190141
    0x60f0702030a12230601120b01020c01030e0708060a062108040501120f1a040b0604050906120f0601060903140a0b0117010f020d0209010f0c050c101b0f02010305 71
    0x10150700304009168400e841007240010640d124900002d1000107558400c2e07245a4200302c841100c43d4007000e118841d82c0100003001800500d0005010f001080c100007503c60340c103001c1086c103040d142c400a99910b0010720990001d821101c2c100d403041d250100d010303400340c926031041545603211030501a0b40281507030984c1c4000341e0800300240c9000d1070200115000720807042c05081e400d13521405200c400c1c283d802900740398688004002c55408840041000b2550188006840b03840b04000811050320307511189903124108640c2c9882c40d413100c028850400d0340c0440e00c482140204000881d00e2500a2201815640255000040c0c01c0c0c0ca0f804140d941c10305000003505080c0498010001508258601d650380da442a0020030440f105140d840240e03000030b01d01404642d0049501c0a840d40e2014260007844507030b1600c071b0814041c6450f65a15210107501032070240d042c0300c03091a1450300600402c020341d00d80082111000380c1d0781c01c140003000a01c4d4401c900013401c0c00301196085448803c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 981192607 1250 981191357 981191371
    0x9141b010512150126091002040f05040207060e161e0806150310061404230c0a09032301050703020a020d1d0402071505010e010b030a0e070512030408060f 68
    0x2c0203500c4120440740c0303030034000030810f0400c010410441d131000034907500b010700c030161103000f400c107402c00c5005203042044900c4080382c528810b004c00c0000d00342111742001107510a80b401a6520260b04144002e400005064007082c0b10700c80c5011040110b00b5407400440301e000c010f4405072200c4040303800e01d407161441204051303071203040455840e6195442640400000604887d222003c480703504c4141c40031507100ca0030802044c100d800450800d406800c082c4140c0846170040c03c1d016000d0304400402c06480308502020108013000c00c01d02413a200320140d900010b003011131419101075074030380c0f0201d452165070035400d01c1e0118440901900907900d41070320907009000a05040c200850740c41e600780c035144408407240341350b0f603c65440f9031008180300380c0245c032046180101481050305554040c0e1260021034508401000101c1c0341c1020f0301c0d00300111000215418002254162038900f035070b001a548041d00400c4242c2d201000002801100c41040503070300181e4540d01c804640b00c0040310030b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 981193857 1250 981192607 981192637
    0x20a0807020f010e120d030b1c170d1d0f070e0613060f0b0304020a06080106021011090a06210e06160908010c0201020a1e090308090409141b0105 64
    0x503005142c8030284540910041c508802402e0754403002490010204d580e000c115040003920040d200d0303150244080c590001d450117601d0881c21038801d00d200f0b03020f642c049c0c80b02090b0395607911200d840b802100c020840c00c01c402d00196031190b040c84001240c2d240e800600d40301c0c100c0d101c05071b090081078040c111521421001584e0340c0e00402d1202c002e288582c2d00b84240e503075000c08507000c645035411202500102030303595207070700e4244180019202103420003070600000d9001002055070026110946160750100400c00c8044140c0c0d04400e40180e40105611901c007807400305c0c519134000c00004590801030321075110308002010341421a503501403140c203c0e400040000e03500c11034544d0364403d0b149407440c002828aa640951070700315542000c0080042c0d40002d0803c1e20b560b4045061902c060b81d000c64800c1c54114040d000c0e0014031a40b1000b04031180c00324660b00c996959502c1030420640010b504d80300003007000e01740341d160113042d0728071003132340503a45a82c001551044d03066540700c2009201c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 981195107 1250 981193857 981193867
    0x1c03141605030a0b090a060314161e030f0302010506040612030e1e031504020a060306080d03151221091d090a0807030f0e0907050405010813080c0d0f020a08 69
    0x10850751580024840c1c030038103440f0340056416864600805204080003840064490704502d82440105c1c1052600e4089501c840030030200c1c210010b82c02c4003212a664800c89400000d130301818803504660f40003a0a44a250495005050f01904081d202d40b208030740812005c1e446031201454001c00ca10054005411410007000ca824061085414684411146007001c9264000245858280d031a02d0000554250900086082c40501c0300090820350a0030704c492400c2081881c2c1e1035011001c03a900f007513210f000110b000c040410002c409404001180d04401e070140c1407405148104400901022216040d8031210034460850749003640d0030382c5020b011000d462605030309650800380042c4014018001d195000611000040070440d1294494145a0b070a0800207030543c50b601ca68079000d0b2090a04100c0c200d0341c010304175001da6600742480f01158070b075080560f0800c080b10600606603800020705a400310300003e94051311010a03500d014060340610320807a110010150020180402441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 981196357 1250 981195107 981195151
    0x3010e07140316020d050a212d0c03020301061416050304171c0905120708010204030f0b0603010621030203040506032a18060a03202a0604231c0314 65
    0x2801982414064010035041c0303071480c005800031144008801c603e40c070105c4682d104e15030ae018070302220320389082c1181550315058004d082c840c03100364606581880003d401000703c006110010810750008102c07074a40b9101d04909901d081c284080889030700c510318007000034092101e16603c60800d542c3d510480240360009001c28158075510201d0140030300c034408180e402d824030241c00154007403400090840e10070f041101d1400009407001d8003c0c1d05044090281c2c908020b40040e03d0b00c07000400c1c1c888120607003012400c0d401250400d5503c590000140402c1103000e1000e440b8401a0b0080000d0318140c0d44c039494440d10070ba1284882e07007400c1105c1c000e000d15090b80642500803c1e0308000c10031140190240e0441140d00314150904180494500314048800c1c2c3c0d040c891111403d0030302440c0302070039259940d0f074000600040000074151072800d20900380840142085070030344110750781c424808000d0483c416140504c50002464184014160070640703504078040c0c2d80204481483c414800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981197607 1250 981196357 981196397
    0x106031a09030412110a05180103030807051b0c1908071404020d051e070905030c24160b070905180a180c080d0503070503010e07140316020d050a 64
    0x20620716142c0814880090018240d001c04a0001d206941d0b0601801d003402c10401008030300d0700154011052003200800392110420010705682d0941040c0603541d1742c8050407203042c401d4000d40980000c1520f00c0901950303001658501024041f1041e00d440c038204240d003411203000f4410005a94004d000c100000c40c03441c010008146405003015181c1420f248898003030b40c50546100c004410b26500e078a1203880e2070804580c0194184c03902d8404c041c500070001c2c0d41d8003000a0a24071072032660b80c0107107511104248104491224072030054454003100c800304414800624191210201100002d14251241c0c1081091700c00007400c2c03030403582c1c01c802862003601d401800041620399a08035001c20b04000300003500803500c500300982425084c810103a04006180903510140700c014000d020500e50400f0540b03064501402007c00ca0750384081044541c034440309150001c10400009119000e444119a000c18101a80031962180e00010003140c1e2441008001000251801d1030701400d00406 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 981198857 1250 981197607 981197611
    0x2030a1b0f060e03031b130513090203010c020a111c080d0e0f0c03010f09030507020904060209040207030e0405090a15150f0b030106090e060f0402070602191d030106031a 75
    0x1001000c841d9881d03640c54008a401c041d0302600340b0b034404030070484a282d80428922008884400281c100450074842c001682014007955100c0c0c0d448030480710b100450b0350311006516030001d0080c04041d000c0c98001c0d40711000c2c00c8080c0c9404071b40199618150a0854010706042c4d01701c120604051460388641c00030380c006414400500d600e81c280e106d48040c0c1003090003210145000074110080380759080608444000c4a004045030802d513a050120307800505450265030181c030743e0b0410b03948038940900280710307030707c0c2d030f40e80c41380c400b05d401c80505500c00d0b12558042019502006940c944180d070319580c2c0041c040003002d80600b0b150708031701c0355950781002c81380c02481c49061003820345620000b10708145640004a0640012004002081e400444000202650925201c442c103241000c221424000300ea501d014030b070002420303001c000c0340c0c0d8100e448004850940140a280c006401004035242c03552611501d445200c00c0010ba140c1072082004480e440b114080c5502d100c000462104000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 981200107 1250 981198857 981198863
    0x90c1e02010216030e030d0207050d110d12080604050106020a05101d1504170f0d09030917070e01062618061905070504050607031809020f0301090c02030a1b 69
    0xa0007661000d02e0f044241090180c0b0a80b40c10020117414400e041c600b200180b0901d046502c000c000b04807907201d0300298501c054104817207000c0c40304c201d40402c42034841c0480003012500b00c804550f0348981d001300c541d805030800b00c40c1808581d03a00e00d000c036511416010050a1500400741895282030694000d01c09440b01d100c4510300c203100744403030904103010005007004241100d030401c82080220070800a41c0d08000b1205e41c00c105070042141c1642c06000b10313030800140e807000803c0a041c000c1207141c00030000640205000115110301d42c2d101c50051166a50b10024200041942ca0040d050600e14501c00828a64402c1c2d20140d8048600000390000c400c1009030300601c24086001e20005104645d080b00401a48002c00c03604011620020040010060103000510039603031a0003c4812041e014901051482101440d4001c188a035510002c1d0306071001550200c4c0a001001441c120340380f2490800102410107001ea803240300708031540c0001041c0003541c0003c07643c03100c00020b003140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 981201357 1250 981200107 981200111
    0x30301033e150f0304020f0d4e020c0a0b0904150806070f0e0102060c03040818040615020c0a0f030212191406060d030818010f05130c090c1e0201 64
    0xc01441c1c82295640094481c0e2800f00d4000100800d41c208400300c5064000140c682680340e4600d51245801025045032841e038070501420f681e20b0f2040310060b1030001040202d01c14010443c00031030000301d0302d41c0000c5000036018203600360b10503203401c50040c003c8882c1d040d80c1c0b5240c45400030400000f424501240b4000300381c00400400c0d900c0041100502c1054140c0303030164100c0d45503c0c0079040307030f501002060441d4020010014040040801c4e01c3c4c001e07603c00050354842c852178441c22001c21015100d25006450680e00003120f01080c08a528800306a4090b40c00720134541050080301032450152004598080320f08100508141c000c0c000817030410303026119044820100f410b0700c3e100d040c000f583c41c86c0798098444803c9100307000103500b10302e00f160070303c000094541e0041d0601c00700801c034122428500c04030352602102908021030340c00441e101040207107040a0303842c6c2080080042600d00b010070180c0800e44090394429460100032035225404102d000000b1040c0d011180d45561007195 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 981202607 1250 981201357 981201379
    0x6060f07021801122f2b0302071404051509060102030d020d020d060b0c060a0e160801050708010519050f01110d090806090d1403060301020417030301033e 68
    0x81074403140d060107040a4002107a20204e1814240070202048544149100810f4244260300c01d0034003400d0f181c40300070b840078451860040080c20340c000c2040c81c1c004060510845806c20581e001c145141036402004805620507440021300049403021695401c800089080c426014234110843c5a409070051044038030f800042d10302c15040c0e0300311002c1c40340015008901440e45041c14020301002e804507140840c10080b0102502c1d60300c0ca805050802c40d036540c0c2c0d618075424401403012600380b08050300c444001c80e546807005030081a040b80c5000002b4802400071426241803001d01c000b0820041c1609105070420b8102700c18586e100c01094103020500102d0072510500340540d254401064131410b07192454121103506014004001045c2500a403641c0e5030b0217900070248114545031109640e88079a1042d000c24020f10a0303412407403a00c0b40920308010900030000045050701c1c420301d802142d146614110422041c1341140c12840001d4946259004034000312040c507000c031008100d64909 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 981203857 1250 981202607 981202639
    0x406090804180207150902060d15080a0503031f0f14010905101d150f07060e0f060106180312181a0a080903040b0a050a03020903060f07110606060f0702 67
    0x10100070540038a0042e004100807050000310346241d451005c280301c00340150b280d540c0c0001c40e1031158a41615003699038141c00844842c01d003507064090329050086819812050812a9807500225149030501c0c0303046101a41e2005c410340c0c1e0303000f112507240c0f0400b581810444100303281d031075040529041100165000882d960b4030f82045240c24036540780c8015041100d480401c0495000c3c2026000f10540900d82440c1c05000e01101d45e0801401105512a242c902d070910103070601084050003441f5540f03103000e48040100700503040720015245c01d00d80340900074618080240c2e511010b802000310f0418100418042c2c1401600151801103010380203480c0c9c0e0084074032075032800314600900320110784c032100181c024000c143c1229403070000354202407030807c03c010302d48501c0b406481003120114510321100e0180d0191003030103100409071001c928106003c0d004101044903c0300001d200c0284505000e4008204140901005481689800340d0408810030a078050072040342c1180e482c000d040c1c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 981205107 1250 981203857 981203879
    0x31810060806060108161d040f0c230405010f020c12251a0703121b0e010f092108043506061c0f03031b0c0b0406090804 53
    0x1404014100055014103249a80b450000b0003410107041c00740442c10f015070035a4503141c0c2c456990322454100c80c103021007100c400301d039204c84600541003401c3c28080303c80c110150b0095000f006803170341da110b0311045030004105005e940100c12400540304100a022951123140e203170500d010740f40100e84841c411030703010521482e08040c11f000a500032035840300305140450030541407000742041140489083c40301c2c520008200407182c00044c54001035030030070140507200d0010907440480e400c00071145259910303440d02c03009100640c001110f86c10103071641e40c054040200f0314002030b170b40c40c044142843c1200100d403451050f031002400a8a841e40c002070724410050014060b0030a03155040254507010348c40040818414009922a10468000c1840000b400030fa1002c0115045901e85d0480f10702c503c000c07444070002416800c525001801407541603004503409015412080c1d25030203c00d00b003110444081500107115070350380c0b13000c207010503110f80101c1c0d0130b10700400307a083c0b80c1551440d00d080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 981206357 1250 981205107 981205123
    0x62a0f060906110a05030a18020a0e0f010603060e04031409061b0d0c051b19120b09060112060506211e0102030f04080c01060e0c04030c09020901020d050318 69
    0x5016030700d95014604102c41d0f030042c14014414010410705008078924040c050303000050210508654075019100351960303002090b84011b4000d0021031005445070f090022080701140e01d10b0300e5491400001a07a28864414142200c000b41c00481e6281c842e40e80c00c898541c0c1d001040c0601e6001407014860942e10000140281001d032802c240403185010191810020705031345260a00c02014403000100b4408140150001d0134440341110084000c03002843d648034045904071145039601010a01071050030300141030501030340d800b84169a805221740e44da0882405020036060709440141c001941075041141c10070700081c084c8580d074000801c441d0750b541018800e902d40d544000c4c02d01c142c80c4201044107202e4850311000313514500c0c1ca041c50f0450502d018000401204000908468502c020f48c0700d13034040c1910486815440c2440c0e040c1d103d05400600003a50302042101000130990600e00c2101c00c0d041068001e05902840d4100940721500018401c46005145400d041069403051001403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 981207607 1250 981206357 981206363
    0x7020d332c1908120106030f05060409050304060309020409060f0209150c1902192405071e020d150c09120c0b0310050d081e04062a0f 59
    0x41d40030400440e0010003030060780da03501c490045114104001e00e01003003502502c400300341d0010220b1542e141c651028840d4103042c8482110800012500c10f81c15080707030800c2c050b0300c2d5040c0421b840701001c00003103e04424008203e540200010011217020b5009800d80c0c0780010400102285d0300e0707c032001581c2ca00001140003e40c00100c00c0c0e200d1400c54000b80003295440000da046c4513801c66016030b60540c0c401c503880090001001c000440d501d025521842d0300c000c9202d0700c01141e551440c3d451080c6223524000d03c03400804142072100b4402c809503210346401038001c0d2042024400d483c4860504c0002c240d0f001106501070002044240800140c1030140000c0000c25000c1408010700c04c002640103408180c3d41440c9910214036045440815540d811401c070382d43c4c0d15001031042400b08603502083d000140c0303a12100501c08810040c0c44031144110105c0d0091103800e034001c0c014450317030003284049010543c0c0440e241200b83c00c075000d030401410440c00011096116020040100403040b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 981208857 1250 981207607 981207611
    0x61b0c0f060810031203020f09030102070f0c17060a05180a03020c0f060412030e011806090e010803030903030a18201503160305041b0b0a080c07020d33 67
    0x401c21503070320850342d03a031008941c024556810306559901c0c000b81c2e01704400004042c1c000c51200b50b041c401500b1505000d000a000710350312081c5203440c0d04d01410181c02560b440f59030100004504041100c1c0d08507503801c44028040b5540c404a0b088000e040181040302090f0800b01e031b0b8401001c0801214001d2030083c0c00500204400e03004204400c4602400d140c060f0702e0500040208000184c0d501003007551504000e03c442c2c107907400407100182d00c403e0301c004402d0b03181c0001070744030b811960303032000e5440c01b400244c0c0350380e00c40044a0b501d21094451140301e07881040002d21040c0190f2181ca60501901111640d105582c3c40303000783c2c501001c114200444602c500d143d0303580b80000c9003224400c4c1d2a0303109070448c60036075400c0b440e03a0041c043e04820f054542c4d00160410030042c1c00c610340e1050703e0508c030401c0c1e0f480e806070900c5900101400c0c00411040004105070220f40c409a408043d40101440080d4286942d0340c10000303485038049400010241c130280700300c03516096000c01c1030091880 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 981210107 1250 981208857 981208859
    0x4090503030a0b0d0b0604020a0c0c090f050c0910050c160e01060e0109050f1e0409060c021504050706050a050c0f0c0a0b160803220f1a10061b0c0f 65
    0x5542c00716107074116441e01c18116240c074900000c11200f035065002a0890b00161600c007500800d854440c0d020308000c0c1000d06203140851b100c180c42d40030102d40300c0c10315810411039413a4141c1c0480c0f40b18102015500039500c0c4a508015803180000b0b003090300c0711030300780d40c4d40b6404880900c14400c030540020b0820117024005000e0a82e11013004d1100300000d02e841c02c805071406000c121fa00d041403007128054400c11903c0e40031182702c2d159045605001400c10031003002d681c105071000f0081ca2041030014094040c9000c0f9a120000c039107800f45802c10003500402d494040241c4030ba51000c0f11a00a00c036081c400005959018000c80c646211000050000d8030301210811001d081c05801c0a21011800e0100180030034000805510a0382d2020701b0740e17982c0e103030152442030f4650f0303078961030b101500303680440010040c4440020a450740700d54901030040740740034200c00344000101c1b6091602c13011980d080011f03e124481d0000d0395907024504104030481c54035007414040903034101e0195030485240c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 981211357 1250 981210107 981210121
    0xa29070b0610050a09060e010504081507080f09030a0c03090e0907030203011d0616020106052809050f150a08070905090c010e060f0913020304061d010203161407020409050303 77
    0x1080c0c802c0405140c8649029210b6001800701c02c001c0c0038a5007000f00c2d821001d98964000d80840340502050012244c03d030070003468a4298a0044800710005035644000c181c03541d1610301e000d80514107441c06541801920201110100d42e80142602041460a000034801c2c01e94040c5a02860928001e800d2140c1035005141c01d4903c98051020881f0240425403461f8101250a81e003002c0d54039140c00ca51104003904a0248c801604860f40c030603103d0002e501c0200100c20b18114070201d241e26400425592403041045480494508031100d01900024102c03010254907040c000da0300401140441e0740307c08800f458108180c00094030300da590824401c460750100000c243d4a07a00b441e11343c2142d030340c1802050003801041142e6910040205a20318180c0e1071042c0076600f00a008001c5440f850a07042040107010104000940e0082080c62448a140103000b00c0f489050000c000b140c1500c402441240d00ca60008406240b0100905c079030401a41d91f40540079200e0f008800858590a2841c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 981212607 1250 981211357 981211369
    0x3020901170d0806030a14070312050309010f0c09170f030301060e030c030726031903020417060709170307061802091614180307180f020403020a29070b06 68
    0x1040b090a1118100800440e07940003d01040c419901c00001500080041c6d8400d1414401d0341005017108100507100614035030040280d4420f1245e20002e11144c0d14202c10f0008403801c800c69140054200364040c820f41d07248244003400c040041003214001c0d50820030003801c40c0c00070b0300100009910f4078540c4400e4070702040310310301010301140606080e514083c03a01045012888031a040414000310300032545d1802e00549030701d20800051071900c5104440700400039403050281401030007001c0341d0344494110008500b80304014a03129511110300f801d007001ca0005507000c00784814402002940c001035818060f0410061000d4031511000103e881000440c1c11300520489600101c2c02030150101e51103201c3c041204051b040071031356400300360001070144c1e1403025129014421a030f000a410700d4140c1d00843d030440080420014202d0b424980410307031140c1c0c03001075400b040d100c605004900c4100320703d105828140310820300700c203441001c1d41e4031a00100c10582d44040c020040140030b003404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 981213857 1250 981212607 981212623
    0x4140f010c030b06040f330c0b0a050928021c020906120604020f0f210606010e010905040b03010b0d06050103110d02030307060915020c07141c1101090302090117 71
    0x300c883d80d041a0a00e170354103070044024440c5a060b10705800c214121f140403485480034034444503215484400070310b1030142000700f40c100308a41803803000e0b0001e00c44807400c0c4511070082c460b160103040365440044005001a5a10444010a0f80480201740040c0e685c2d049032990030700750082d40a0820346600410039000c8004102c240110341c0c03011140007403007000c101c10303500603811030b501c0c03400906038400301d0442c48540c5961600540c00c6101655920124503403042c0c0510b8800440c0d00656501c0c0c01100c01e60781c49001580445c0e031030f8609020b01c0c50542c00c0802c0d00f000c0600001079810701d40300007034100c0100c0c3d8403e88282d03646000600c140010304081e64013400040d41e20340b1200c142980483e94901c103200c6d000d015036030380701303000700400095507900c210100e1140f0055480c2e052034014070307486410030b104c0c40030449458581420759081000d0740b0f60700c403039600f03900051004403900c07020302c590115903120381080a4441d0110050340c40d101e42c3e80c06000f202c55005c8404145d900207a103000c0030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 981215107 1250 981213857 981213859
    0x170c2502030d03020903100917031509090c060a03051819030806100903020d060b040203091b0a0b040b0c0a0c09020c0d032705010f0203130209010b0307120504140f010c030b 76
    0x10170070221180c07800110240c031080b4080340001c4011541c20b005850a0f04110400c907030303942c000300b40072a4014041100707030f490342c044440071b5603501c5201d01c0340d6403507030b0720b144064100006110a070340f518042d600a0b1351016074110400c90b401110020a820a410f41502c0700030900ca18190340145a0b008003410f80c0107609480e100c0c182d00105401910a0200380720091040000c818080104a00c941112082c420003420035174690500c040c07180d8450032160500c2c2c0311580c800384481c0c407500d800f030205402c40741c00803009840c0c00d0a0507003403034044c0c0c01400d04a5882c411096000d00260140b200d160040401e10300050703d0742c000000d07150070305140040040c2010304005800204081c1e4200f035108000e14600c2c8958105003071b00d8a907015015802440000317505c08000c001d21019103c1503049924821600710384075a80b11b50f0009014041594210001070049168990391076440d4481034006019012050900d40700b40e601c10705e00500c502203864213944407040c420070f16416001da4540100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 981216357 1250 981215107 981215111
    0x90c0d030c050d170f0106050d02160f0b0610050f030406051f18141e0603012004050301050105010c0528050d020106080c03010c0503060d0206090a030c1410170c2502030d03 76
    0x45441f400a00602071401220390995000a40b0394401c108075002207041c42c1e03c08140f0080b40c29138240b42c02ea410048410382e000c0c144c40056031011034401ca04490481c0e207100311048c20740e283c1e5260031004090003801900100070012079100c04020315000d400007454036a01c1342c004c90720110101d1064565030701280c440c03117074003106104514582e1034440802180083c940c00c1240e850200003805070002024441024451761018250209180000d00c166034041c0c0081c407003640e03184011511a4040c0e00d01a00c02d400204074001030306401201050540c44405448201c0c1c403007601d801c0e0501c06045008000344c7e40d140b40410052074180f205961441c002c5000700b240007000c0c413010b4624880240420300c504580e00c000403c40d526401074607581080030708082041c0342c4a190400c0090194010946032804205006c40140ba2200e0880601d800594511540e40b1180c040d1b0000140c01501d06546400b0038132074041c1c28094004404442445001009550501070061508102004003c00c003054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 981217607 1250 981216357 981216359
    0x60307090614150409020f1e121303020a120203071202070503100e0a0503210c0f04090905010b040213170708070e040c0504050c0304031205090c0d030c050d170f01 72
    0x141030b80300c01c095804042c0e40e00d001c101c4544040103250b1103160014000e5900c04a01c0c5454625260090410a2590300e40112125003e481c4068607000b14180b6044206c40c1340d000491034000c11030b1010310702c1c2c42f900440c2d05007100c543d5001c048001a221040c0107034004503081040c400c2e022500c0ca003040b00c0c0e0014110307a604100200f910b6110755800d41c0c41c0030392100589503e42404000c8141c81c240c018050341e03100c3c550000c00341080802c1c1307001c01c280d000380a030106100740440011210200780313415650385802e20f005044d501500780c8a02c141c1d0155643d036814015920380b03000800000a02d1a0b400c1050741c108420244140c1d1120131224103584528000c1c440d18500203545400d540f06841d030072001c1c2e81c582c50004003400d480e170000c60b08141450240412144c414000e907000c0e600c01c1c0c58049012032044083c1e400c03180203c8402ca41030f4800e201010b240e007840840c202d2100d00030320741114481c0c40c54071210700c0d0902c501c0a4100080c0c429040c90100385e40b00c8000ca4020070035502c1c4100c19 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 981218857 1250 981217607 981217619
    0x3091220010f1407140a0506040b1b040314031303050d30051306020408031b0a020d1101030e031804050711060f0a02071209060f0c08070b100308030f0603070906 71
    0x1034110301c1d945083e0b0b18400104403050041690030800310031103420403201002145e150450300d5002c103407001c0b2605000003012541040b060746601140710700b400b4410b4106891501c95090300c02411009181d10b000420400c0078001c0501c140101441c0074400602e2407250800008000c100c428a01c08100410014a058074101442c001c0b0188886030a01080d0b6880325035003211240d80c40007000303240c40e01c0010006480070b8048040c0406507084c464410900410b459a56203480c03040c0380096025100ba00c041d0300007401410030703a07080310061400080500706d040c0418036592041007001040c801442c9409040c0c58140101640802c591405002100514042c0c550b100809051403424440c400c3c0001d4000e62113030f050340c8110350400d03451a01c03061a2600544506242d001d01c10000311281d484500c11401080034980295015824074a40300c1c2507200e0325130a52010b440c0da801c401104000001003807549000d50702a4038800c0d18411241000001c140c81d05410354494400142058020840f03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 981220107 1250 981218857 981218867
    0xe04110f0313030f1805131b0207060f360503030703090305061305030d05061516020117100902090613230306060109050607021807020706020f0105060a050d03091220010f 75
    0x6c64100751440240c40c114001300e00b02903c070004070301c2004800c980c507401103180e0000b000700840388103807a009418092400100c0b18949480001d14590350b40620911180c140c0c1c42d0300c2111960040b03000b06a4030385400c0007904584c004001900003925101d024400d0040c18082d040d00251035090162560510ba911552030b4002d944509540c0e41d503800000d038913911441d800b43c9100081034010342d034030901c0c80710703418015445202c05d80c00140002c0035000c00328082459940140311051803003d03400d1901041c01c000c0d5101c3d100315604200d00b030003501c4410115a03156006081034015480c41c200f07013a00100721076968030810a200c1d40c00041844031590300203081400751401910016035910482c00480c10070354161281c4641c0100c0d40303041003813181d404210201a10030680c00d0361401008014a2403e0762010345d00300c5d41c0013040d0007007084185400e02c41803010520900303142c04007564649002200d601c012805640e20700b0381e40d1014000300c5030032201104542d02400d019032180015440104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 981221357 1250 981220107 981220109
    0x501061b03030b060318100935040312020f03090f040c030e12190c12110f0f010606090503010c080106030b0a05030102160c0e0103030e04110f0313030f18 68
    0x1088940c0010380014544250406000110b0241079655030b424000c0c0c101d01c00641c0102c03002c2e030741d000d000c440d544000c01c680241061140c01001843d000710325030703c10310801909082802502000030640398291215540a00001d40c05500d00005404d6003000180c00c04088041d071800c980c108201191442d40c4074011404400800da400140b41d5041480030381c01416806801030151041c14017040303111110000520461010341d820000c4c100d615081581d46040e80e82c4014514480e0903000c800d000d01c5040500d41949400d8101d030344848044051a040000301c0131210001d9441e04805d000c500d03045070305800204401d03002081402b04440c002020340006005103810107450b4011583e00355180c000081c09030000034021559524245000d20150840340030417940858110000210081a84803c5040b244c250b26205000c100c03850800c0000c0039008803a5103a80810f00c44071080030485009948034252181d90104d00340403608001e8401c1500803214800c03c1691501d43c0701008070940410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 981222607 1250 981221357 981221387
    0xb0106050a0c05010912140c0c042a020703030f050a02030d0504230601051c03050406080919050f06010905010b04180608120706150e070503090106152001050106 71
    0x652203000070501103555026829001d000356007001e9141091120b420701000d103080c0c0b1511060a018283c1d80e6101003030042d44442070564002c42c0601e11581003581081c4283e0054030003104120190402c1d0005201315101035400680c0540d0051040503040550720141214908020b810032a880780001d589124018482c6501070300c900114081002c0084030216480c00342000070404014002d5541d5078080910640d4401c0c200420b04102008050201d01502c41d0940d441510300f6087c00e03001d440000000d001c48130907205900a0a100400400f1059207d030300c02d00140c402140e10441d031031305d8104180c1001c00740d2480c04004001d042d040b4002c0350101d032244486a100039051601501c010042d96024001d680151030000300104481c000a243c0d0503c0b4090411a90404282c1c018820150b8011428030520b084046450316000b1006103a1041e203c0e400030403a1501ca10800021005600704140802d00b0528002140140c480d1400c90316450708008000d03647c5880c0008004008600000b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 981223857 1250 981222607 981222617
    0x604020a060f0e0918070f0305060103121403070c0605150a06300b03070b07051f0b0a0b130e040c0302010503040c090222060c0b0c0306030a0b161403040b0106 70
    0x880b005500802481603180760007801104103107880042c0304000500c14206001034040c207036010603100d013262460b80a40784c02000074007481e03007107a480e07000b2900d1155880f0144540c29005000c90f0010030011031042c005580d400a00103030600c0c0c0071003540c001500203652100c140b001c1005684950320300e02c044403202d01e01211290b8003800c06d1180585c4000c07145081c210640b81a81110107070340c0007008072500a80465400c41d40d40c1c4400d1800d40030b540300c010515000309580035801a010801c203910985050f10002c6e80100400c00a00003003000d520440c502e00300407540e8103800720307050306220050555551081007454070703035902d103006100340c00028148003020011500740400c40204401825000310300f103540c0d0000c941d000717a640c10313080410301c030841c614200810754030320640d0014912640008200e0703081e21000b0030004c0503040248001d41500c03c11110350045000701c81301d02d020b49101d00440c00e05122000c4024041502d5682803040c1ca4800c00c280400038483c803070418119035640c900703 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 981225107 1250 981223857 981223877
    0x60b030424021201080c1804052d0102070b040308010f06080f0c07050604030c060c140307031a030d05030108010b010e030d12061703190311040302040f060b0c1507020604020a06 78
    0x404003c0c011100c01d03510024400c000800d54210000f4154183e1201f02c50f2603038400200340ca40746850f141260011b0007034004080c0f4030040051164500f00d001d0392200c051240c00088042242260411141610b401c22200244014140c0100815000d00280109a05454180b401c007414245c809404400c0b41306000c000109803048580560740320396801415100d10b8101410014000060f881c020f584031845d02c07180f50540b9000d500004034241b00c081c0f81608654035501d00743c1c01031100300010620350701402c40c0280c20395410300009085485030b448203910ba505100d04942150340340b905d62814040782007a0980d06a400064130710002c0201d260219500c82010908005080304d6070207101d429007040740110039150080040c154120044800480300c4950307010803016140b20552044044034100401d2026080540101c1d440b10103980002c160342c4d9a880c102103403640682c0e20603040760001c0300301d045414054000c09070481440e1009040f00c0c2041d40004d44280c20ba031041c003090080b1000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 981226357 1250 981225107 981225173
    0x1b1e0a350d0e090c0f030907030605090d0c0f0f05030f0a030b060f040b030405071a0c150f06060d02040b0f13080706051206030a0b0c040618152a080706060b0304 71
    0x104444081105c034071844c0d1242040c6000320358500440c04116000c070700306400628002d0303002403a25214034565a40348280d040541701c803080700316007001c15900e02582d98031080c04294100000e01d07148604500055840b001c4110090403a804450306901c0b420003007008084511404042d18180c805c84903078241e59441702d14003146000c407a580558066055400c90259400b00c0030041d00003c04032400b560601400342d0443c1d58169000c840c2801c0c04103e601c0841d14508150b0007072b0203085020b80b0018503250f00c0da0f103041000d802c160f4045080c6000000c1d00c0c0e9030300f0182c1054000174a40c103001001d0403420540040d0007801090a182c1002c3e0703202e000906a56003c00881514030b810911403642401c240c090f42c041a8040d0144102203600e4a058a11100c0e4502c40c0c20121803030f12803400060400d18a00300c0d88010288090039612020002c800200484006810801c0c1d118652907540e414040c41c1010640e0142d9002d541006014810003020440390700c080f41c01e42d40c41160141d90604401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 981227607 1250 981226357 981226381
    0x3050303150316090507080603010513111315060f050315040218100e190e1302010905091810020c2104120605091b1e0a350d0e09 57
    0x40321035031600f01d0003075000400c20000c0d8001405003c1c11b0b9035444540d0350310020b15007030322001ea50351001200e09e4154240404c040c0c64044c142c00070000c01c0300320708082400100e000e407010275104071412030b4241c008002040d08000011150304481c01e245042d40350005003910109a00b01480e030069400103620200d4541000301794211840086c0b0b15034209070354010041102406515442c003918600417545005038241c440602210384052001d000ba540720404a500e40d10712940c12410b0194030580400d103540c0f840c8006205244412480480c02c035050000f915109003850101070b114410414421400c00100b56054064100c0c0d05002c0041c903003060350b900074031450b07211000f0581d240a0040801243e6000640a0300d40f82d0112540c07207604001301107200e09111360040e401409062002c400080403006054180c82c000d04051003250754030140da048101e801c034000002c0a030302c0d0070405103081803080c650104070008028107804842c124027426524011640c584034400300c0b4000f0300c502c0010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 981228857 1250 981227607 981227623
    0x12020301110d2003010f03060902120718060f0b0403031d121510060912030909020304080403051b01020303270114100b03091009030219200307030503031503 69
    0x3204499503a0000c040c0b01c40203141c0d800700c00800780c104076000f042c00c01c01282580c0c142c43d403150080091074510343d81c1c00010301c2c48400481c0c005900071420818050107011150080052606030089081c004426400703e85a0f41c001c0702c0850004c040a1101d041c4840956041d40d605080c00a8110490b044541d801c4c0030403000c0940c40b000102c2d42804e500c0d03020035440d80c045c1c0340e5500c802051b242c242090344089254040c450000710140810448050f8900c00c015116009041c501b40740394446402c5420381c1e0042310300fa159298009070403c02c0001c2004072180c0c0b0700552034517070a02e600c0340b40002d481c3d1002401481d5402045551001d50102041c030000c51081e04034000c0050850202a0721a02401150074408161001c0300010311100084105c9200308030b0070020740300148903400d00900528800d04140d003188140e00051411403020f15050620a00407404003411041d00303090f0300381e04907034064454041d8004a070f040000620000507281c1101c0c442e0310342c14601d125200884d241040f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 981230107 1250 981228857 981228881
    0x12180b07200705010f051c0c05160f0b0112240b0a120c06210911130b030105090d0203160f02100801150c050309010e04020d0603051e0105040c12020301 67
    0x16019414070036000040b0032003200c0d020b880e9000804551070040e181401440600c070041c0450803500380c0480160360002e10044060b00b486818590f842401d805030211181d01142c091181d4043c1106110310a56880e004120303034600b03010b4a45c0c60380d4030b46000b02119400120f803da19000940c95036103542d002046c0e882e10140030309221319990703620904288110401030b50380640d08040414024440d4031442c61841c4d0b218030070b005c2400b00c411502c2c010700c001d2100380c40c010041f50031184141c1d2101000081e0505074800841c008650344209821260060400401d0703038040e294602e00160040155810000064250b0741042802d040078602222840402588071040c00b80c400300307040d04a41c4d41410380b07081509030500e1b0710300c0c10030035940d808443c0d00c0a0070742c2e80144407100c000e41c0300d440d03c44c8003403401800250400403545441d0342074805a800848440d080600326a0a0902000c0840b40b20404d1000034040c60825403a09175100d0464001c1c4000251406108821364509410444038804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 981231357 1250 981230107 981230147
    0x31e04320a060912020a030912030509121507030b010c020d0809180103050c0a031505060a0f15020c0f060a140903030301090912020f030306011b0b100612180b07 71
    0x205860510000c04a00c0011124600344081320b20040e4400155860000c5d4181c031802d00c41410000d80e00003c40900a048041090070040c0650315101c0d040c410180d150b900f4000d10850072006110030541c0c07402070410707040526010240308131f40e030703c11001500c19406a4240e6000d07002c0e41020226840742159840d00001c14118111f0b200f8040d030446412680254242c0c0c151841c070100300300d92090b05120280c840000303010504140705099001c1c0b03810102c014032046856039a00c02c828840c82940e409288c020354070000b4244c00b141c0501900199071411640004a0034001000a1981c05509030383c204009080c01205c103001080400c885a51b60010203c07030700c0750307500e00c44480a4011400c08803903641a9180060982d400000c054404010540283d41160b8501c80119840004c401006000707100840c02140401c0c601001c103030080f6041d0040840c06824600007a1605415085aa006a242c002030360380a25120925200310f03030f44010b050040c0d40710b41c01c04541d408500074840d04404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 981232607 1250 981231357 981231373
    0x10b10052701120e031e03100e1e070309050a051605010305010b040e0705220518070c1101260906010f1404020304060e0d030902040c020706080117071703031e0432 72
    0x10301400280d07120360003d40850004d50344851442204010540380c104032100040ac4c41e1081080f0403030f41030b500c80700c0c0e454001400c2925484451502908820036202074000750414070f0240c0e20941d22902610b000e00b420b100b554584009644148502d00c01c018034607000304003040025100d03600300d40110341400300354881e03403454810321840e0019038485c2034440c64a40c031038111511008046144140b1503600d07001100800f90300d81c1c480340356503085624100400f68100488110b05410b007900881d604580140e154a0210203403442d0050603040000000f40144003081215800b8916510b42c42c02034801603166100d524210700941a900442d840e6402040c100d070078050f0f890340c0860b5096008441c00c1c00400c10204050340c03912014054100090b01000052142c0303c001502034101920340001c481d10b0355690103201c640d038903c50740d0319072050f00000b0510803400c0c15000c01032115080080c105e6100d08140d41c0e5140d0100245590607081c141000308409a4060646d0b10400c030280d50b826035030a1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 981233857 1250 981232607 981232657
    0x60603070306120c0504180f1b150e09010e24010e04061502060f0c04170309061605060609010b0a0e0109090c0309020114070807080c010b10052701120e03 68
    0x8403040d0155a010f10728081d41481e41503030b420047c291040d0405400901081c807603e55031503019845040ea0766900343c0c08000645980a0302250941d0140b5585103600701040380c1c1040700c000c4040c0d1000e108400c400041c803c9050a20902412407418041e8400001e1003190040c0d40c042c41c001d0316164028079000340000d40b25a510000380e0034034070a5003614025503c1201071a2180c6096810301810b1409000501140c400c2c558403c20441d18002100e0502d40754800081946c2e0040224402c2030015422880c10004204105a04250700300e4000d0390a60500c90303050401d014000100c2c04000002c01c0003001640030318540300281c00c140d079041c002c41e00c0024018016140c0b020003207000524003510300300408400010740d01e0315030b40a0143d83c13a01c00e05481c0e48586411034041c502165503030352030554456441e030848800120450306d4072500d40b01d28240021811440f0000307010705917070b00000c3d5001340e07901003002d41e4500c1c86100d001408802e00e4446900d10f0041041d034032014641c0034199109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 981235107 1250 981233857 981233873
    0xc06150b0309011404030e010c050a08040801140a0c0e040902010c050d021605010306030b13020a092318070b160602040807081c020a1e021008072606060307030612 72
    0x46002c0c0407000303210380f4003075400059104c40212005000a8607010442c0303510f620820045100d10300510423a84684629118076086910030341c0450b0712a0b545400074140f940c48901c1c4541d00911514040004140084029110310004080e403842160740b4055007045a0044500c43c0c45d01e5001012103002140303000e0080d6807100841c0f41060a0400078400050139880303070140000740c1f644180001495110007101500f8030003140000c0347c2c049200390b0041845103c502c910341c2280e000c1c041d400c1c420310300c1e002c6c00c09031220050004115161a07181400c14060300113840c40844212010742942c51201d065080e0250b141c10800905443c00080c4c006045140001c54505440918080c0c9a4000c0082100142074400128050158100205081c040740694503052528400c019284500c1205680001e4440c03000e51400d002003289041400341d44dc2e0300c441032964482c20710302182100702c1e94102134030f071007a002401c0030310410000001444640c42608500010850240c407010301030410f00d81462 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 981236357 1250 981235107 981235111
    0x1e060603150b040e0702032104030806040504081e0903010f06051503040b0f19090602130b03091216050d020d080f011a0a141b0c1206070c06150b03 65
    0x3400c10007003007008540381814400319510b200c1d02500d481d03d800310040300c0d00001883c92095010502c825139580b10341021464500c00c21040d00c01c030b240351619025101c408090009806203181000b00400103800008843d06002c001c405c00315607840300b4907000301c64410200c0c0c0e5901542400e41303056019500d44c1102041d56400c9400d51610344030840010b00c00c1c002114050004640030b40071039412000d00cad2400d0b811a42504925101422075001042918581c50040f10015800100300201001054521010300841405a8a14200410420b64030b2034404240103031080300056080c616007a11440e4049a64407070240c5002020428000e500c840c100f02c0c0c044040384104000a29456500303d40380d06030f5104689110b035041039000344554a41141c20545c0500200740812003100d03c0360005403100031010840030180e03040c0240b41c5814106c0002669000d41600c589150304040c011503841e90100403032601981500d05801c00c00c3c05890340300c070500c140094000020551001c5140294 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 981237607 1250 981236357 981236369
    0x11130302120616110a0c0b0901231c0b04060e010512030405010c0b270f010f0203040f0219030c08060f070f090501030218030708030702010e06041208030a1e06 70
    0xc61039012407680548504048801c0820a1124010040c52501440c0007580c1400c4582c101c0c0c2c4076007919503841c00d8144441d0481014860081440300d01d030741e40803045150340f00508440540b0b980d03110005522600400b519000d1489141280f050070030410b521a11440300f0050080c403030302d030b655000b24140003002e0240c18000c1005501907030103800b00000726411103c043c1d41308034103c41640c07521002031101414010f140000c5290080d0604d152a14065400c00580041c004c94000d43c00000e0071100603103040c0345180c0c018410007010619a40d44400c0c095019103d0480000d0704480e06810300b030741a0401049400d0400006c260807000042191240440050701c071416220b500c0250b0f54540c0d14001d0030000380b90324500344819442078001e040000c050700b08070725000c411100000e08003605038004c409030b52300101e03e940946d0b078020703110b8100034001d842942c6081d05020282c036100d0302d4440e0260201d44000b001c42c400c019290b11103c2841885440400a4822081e200018009500c00c103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 981238857 1250 981237607 981237619
    0x1030606050105070809040c05090414160c0818065202042f0d0c0311040603180803070302031008010e0309090405070302060a020a120801230411130302 67
    0xc50039500070f01c1100e07000c0c3c1d00844000d0030060140100009003584090383c00400c04140410000b9403503e015000c5130201d840c2c81d110340c0d441c03c1c00e090400d925070003170b44400300812a4507000124860742e04941c00c01080440c0e10303448800d0305002ca00c0501c01c0710f000020000d8250564180282600701c0204440702150900c0c07108040701100f10802c803602e00700c1c0601011100c04090051910f5031002c1501e00c1921040340002c080f4010f4201a5803d0044008441e540081c4030200c11010f0310403001406c0d4903090802469043c0c5c201c260b40d5000343d0250006040d5a04501408140c1508980d004d040d400481241c0ea1320303120030010065001a03803a0840482046404182c10b10103003d86c01d0751158000080d405c0030865810048000c4010b402942e29025244001c0003503104e4100a09001e00203400030004900245090f11940203060010400c000080c0d0042c00800c03441852016102c00c40084254803580d8240094020607035031800d00240d12001a004070003d10b044207a00840e4004c642c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 981240107 1250 981238857 981238859
    0x3040e0c0a031b08060f040605120d020c0414040318080328091505071703090102270d0807080c0a21080c220b0d090b0c0c1005180109080301030606 65
    0xc00240303075101503002d001207525034000481070709002e4048203107035400400108c3c509075144041915518186203119058001c141540368544e010480070f08003034000d903010032100c8242816942c6003800644014100421800c9610505d40c0c0300381c60b20007800700c05055075a104504400c0032459400d500c00213107003186620702000c00d607004008842c2109e68185a64409100d130180440d0280d000c0801220300d4400340d403a004c1c121800102861203558413a00040c0e850740c80740000b030180015154054031000e14004240d1450701c0b02c000740d007040b03036019141c0c640b10384c0107213405442070080070b0000c203076413041e00d0b0031809001d180d03000403001f912117000065960703c590004a6110004039034040300385008100329090124915640740192114051154a0b1602c2e608000005d9100380038a150b0707140c81c2c8085000784040d5841c1a500f0078001030055103440303100ba400d80d841c0e030389680004203040d03958070005000222100d811070144040800030401d0301e61a14020015030801e00083d01e1651034110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 981241357 1250 981240107 981240131
    0xc06050108072d0e0901110d05040c0806040305070605180118061a0f0d2607051605100c03031d160e0606070b060a0911030712020a2003040e0c0a03 65
    0x8003da04900544510700705182031805000f124000544240c45565807080300102c5480344001400035005d603040b0101c0d0034140303800c001182401a0300038081980258040c013000a4201c4210780080d41d001002103003503903072840400c410b03404560001c944c1e5403d103003a010303502d001c0c88032400d03085102e500704201c1e001c101120940384203d2481225000514004004030710300d0030b0400110501e10801c101d94003507840310031985042a002a00b0380c0c0e800008110882004014000450500d030782901d01044e5a1a000000c1c0c020865410040140011010018107142c40b0350030010581d51408114002521000c40c0c543c0d5a1007800c15600c01e1401442000c41c1001040b9800350003500020507841c2888404d40ba1510341000c05020076034001d400c0c0c40d001800d035080d801361822503031340350003c282c030784c64124005450040f085c2e603006102841042070321039058000700610801d841000a080500d442c40b02e40901d540705d1504008940c685070000c00c04105040c0008016107a101c6d1781c14852040d000d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 981242607 1250 981241357 981241409
    0x20c0f0615060906040801021306020c0609180a0615020d18140928020901080f0c030a021803160303090812030f13170432100c0605010807 61
    0x964001d4000c5000d4488104929080c0d01810503600e009141500e051342c0c0740044c1d800c99004a040070700c54400c1c1401000300c25010b1000f80e20600060300c0e100e10709001c20001460050740000c14043c90074910000c00c0f08640203a100101502c1c140e583c408070900005000387d5100803a03641140025680508601040320842e0312808582c860b28480424211072010401c055400030310b8100c9042600e0b03000c0041c01083c030310520324145034140040c1d07203c0070701000400d100801001c0403483e12181061290160200c41180e90040340c0c0c080042e00d031402d40860012150188040c668144541e40c4441c084243c03002e5084207d91280c2ca0300c89007a9518200603031107100d4503a8a42205600b030000401103420009400c1c0d004182441417004d85840742c2c2c0303942d40000c41c0f02d01100030f0b8401040a0150418800288030300d28484010150761120038200d240d14517400b030801c50b014007002c040d5443c46a004d9490014500e6014038107000660b143d8004964484841c41601c4106542d0360906002917105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 981243857 1250 981242607 981242611
    0x61d07081b030f1501091a01230904020714071a030402042c15060409050a060b0103021e0304150b090601030506010203160501020318010606050a1206050a0306020c0f06 74
    0x380003070a00301000e001e40810020765041d440342c260150040c0c1610001003400350f03c641e4100440da0749180e50620180c501110740c2201092042d002c0d0604901c0640e800c40d41e81c4100011540c4070801e00103010309640030a000c0e09014541160002c0340394820040f400200300001007284040303a040350364541e501c404541c502080c10150000030804240507061070703080402491035881d00fa101c0201c1060480a5241d1000e4440307409810046c084e040c0200c84144464000500711807d0146002c00e88400380c40e40713032040008104995441000c26543d001c1e80540b4254091507641e840c1c0307081c0100b281041130f4001c881c00c07901c0d000119200000051184a42011402c010b482400d481d03486400640050901030b00990540c84203000310a600041c4a210b141e050f1305c184005603c9050a0320700820343d05041003206116410700b0700038070900364820145c0310207400c0c500e44064400a05d0280f08001c0c41c0c0741e0080c0d500001c402e5404000d01c1459001850568a00c004580703681d0104c1c48502d45460007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 981245107 1250 981243857 981243869
    0x12021204061104032604030b011202100e15030912031306050f0c1213050d030b04060f05181b07031e0c15020703050c0d0801050108090604080405040c0516061d07 71
    0x100c036959901245d50300820005107000401c00524198507600e8070044038600b40d00500340110003105140c01c60031b0800145d10890010b0409421150300d003400548016061a043c0117010707808000200341c40c80c03c04c001918040c424131150350301e050411182039090b2b04044140d907981c0c24000811020381e91400035501c07600c40f00142c1030919803402194000d200d8050081001401d030301d1840300108109000d60a4510340310b40700060b22000c08000d220640710b8503484812201581203041121351038040f88040da6400800c0540c2d02d035600d80301041481030000100018880e00801e50908068000c0200500342440d2601c640201d002d140c000ca90742e001100008240c2c080802c1d041032440c00325005094082c0c400d0500c113082c007151990040c0341c0500101180001a810001048a541c0000401d0782000e04440940202d240680340c0401038403da208040c01250340d81400750146200e04140d40340d210b500148000d20380450b09018010b44507c25224031403040740186007000910010328002200c0c0c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 981246357 1250 981245107 981245123
    0x206010e07021e01150b1c0e06040b07140a02010f060e04050c1201060b03090a0b1e040b060607020612060108090721030306030b0703092f09071202120406110403 71
    0x15a1864071030615440740ea02203c10740d02c1d0764503040709440b4604254040d25410041e19200c60302048580c0000180180c86a844ea10305081c0307070105000480c001354000d4205000680e40d4440e400d04403000d500d04407a082072500c02040d94080c1e160b0640040181c9202c00c0b0060041a407240000780400c0c805a40050280e400000c9060383c03424210f8211968554000c00040c40c9659913002e045258003c5603080080d0308401032860410071145071050f04a01a08140d10342c409948007189011040a00f01400740c40c481e10014441d541c4800c115558507902134911600c480292028407d14141519014042805440095003a040c00170b0514111124240755504004c0a034120050b0f19400080a07000c068540740041f011544000e0404e014221681d4001101d603940e0800b00b9011f48040007c4c140e160100c281c200c4d15228a1840e1600c0c1f90080f6010314103505c810714281c0c1d02d007044010001c4c20b0340c0081040164854070705c8a10b4411401214180b00c04610811318400030710072030100030220340c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 981247607 1250 981246357 981246373
    0xe040b1804060903090504020c03070209010f0f12082502030606060a0f1209060606050c070b1206060c0a15090c12230c2d100801090b0f0a150206010e0702 68
    0x182d51504448220b40c040e04081d91802d803a08080b40580c0e00050040c80035520010f60f034000c40c2070400180b401400703024102e417040307810038051000c5440076108101403030345142c2e01802030280800c01c4440c154000c26401001e851460840ba410b21100e200c140d00c603000f0000010350700d0606104541110605a0358a03490109000c07041d9090a440710600c1c20f00755840c2c403080d002404078840d580141000c0e446d43d9890b003018076600c41c60b141054214090981d801c4c8030603561030710002c0000d03810542c12901962218a11001540380c48180d22018100040710300300903544c0c0d48264858810741d0301840c8000ca650b62107010310780381131003210b40062907040550000c075104e6101c0503945080d100403100740c0f09148204000603c2c041441c8030480b00c41210140c0380c2000e040782c12401094820241d172100881d03a40320601806020b41445a4181541c840d2154201551086840d485d40c00d0010891403240380c40f0b60007a0b0040d40345112050241c85481c00200d40d944034211198410031081c3e00511004e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 981248857 1250 981247607 981247613
    0xb01171801140405031b0c2d041d0c0603060901090902010c05060703050f1f030602090604080304030809010f0c170a050408011422200f060a0e040b1804 67
    0xc2219181458000d5584003210040760600c070161500680c09440103644864509082030400c00c980b038580011030780004580c841607111140c2a801c1c8842c0d60b4440d80303841004592035185a0350882500743d10514000b901170140191020280300010080100c81c1c900c40300a050221038801903607a190b10a003950010465401190003c03e9190b106251140801c2c00991310030345411401d40343c0c0404a0346450410883c041701041490344840030100104000e000b040014001e0345850202a000c107400184414407a181c180031100100084002c80b1b56456a0b400c20030569080303528901e00150420034010202813107401c6640c10150810240000c00e2027038640503c40da07020300035400900c0070a10001030442001e02c0707516000441516180d00d03915050744002d0980e80c1800440d14030028045070400400c48840451460b00038070440484408000000501c0c0380d841814826030028002070702e01400f07a4011030b030078441182513400b80801c0400000b001079800c2500306c0b044c206040d9078005004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 981250107 1250 981248857 981248881
    0x220f1e1203030b0d0c0e0c16150b0a030803160c2f09011509061103090111070e040813050402120f0619081501091803050a0e0402120405010b0117 64
    0x36140320b03050014001c02c0300408100b074595043c0040d21803158801c801c0002c13518991503164810059030340c85181004540300c2e00040e080012020b0404000301611242c40d074020390250350910b0008000e041c89503076a240c0581198402c0364004004480c8600b81c0d502c207402004001c01055108800c0d1518880d002074484034100d10700d5031003401c114407194856542d04e0f400c150ba400b0304103a100106528404640107000c0c036403035500103010040320401101d507170700c0044183e580181013442d049146201da5001c080c40c001458024480d0145214203210800500030020a030900000a441040e141d440c0708000c120300a608907841010000750024810303400b00d4400e60303803006000300302281c543d0140e000c3d540200b190350000100c1c0d600c00e4408141f96220844030a0051420b01c00500c000c009030079594241c0125058010240540850324030b0115000b9000e0002008000d0801c54440000c01e918401a10087d10141c8181d440d10702c4071125540b1440d0a0010401e004007107000603100d0b070070f1140b6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 981251357 1250 981250107 981250139
    0x2131203090b0c1f09030e1504290c06060306010803040b0909062403190b18040f0b070309200d020909030d020f09120712030c0602220f1e 61
    0x43d041c05a4200519200c3d80d994084d034412034100000550f5403003515000d80a124400c0c04144035030010208100c10f5002101200e060354100e4101e00c4404801c00140e04124015420040e8548000706550026410003d4080d2042d6401c508803031460340e8442c01c1d151644114001c1094901d410040880d86080242d072070398000b9805080f50050090418660307076040d5840035100c0030401c0010900000340c1043d050f00599030701440c820824241c3c2c00000460a661a03941f005401064030001424840c0911108041a422100d405200d103030a2800600a007102d0000700c42010340d1802001c0c0c81c8541143c1240d9940005c2c244075040c041580800c80340310001400c00005100420035100c4c00d19050001d004070480c0d035a141034498400104004a400e107005022241b0703842100100134217441c040781d120a00360135041029501610b810014040c1c030903140703030f440440a030010b000c0d1150f0140c1e07a0003040780c2100d42241c0c003c2c0d440d801c039150854104000e4658180c0c54040910840019080b001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 981252607 1250 981251357 981251377
    0x61605040303051806042106061d0a0903110f01150b03090615150705070302040e0105070504090b010302160302100e031e0d020d051305100605060706090c050a0902131203090b 77
    0x2800c266031207c9055443c1081443c0081080d4518114002c102e000d014100240c142c0c071200c0d00c501c4082d074220310700f0101c0080c2480d0004e0b443d90a6030b8181402a102c00e0f4440703039004203540c2c0c004ca07031038041d034040d1080604481c0101e40ca09800503008030420b007602c0c095920b400151446032502c00442000c20000c000d202d078401d0010580c0070900034040b009018030b500c500b01605e0b90518500400c412204035180105450341000204003405911030203c9042e81c5024800145484007400124000e010303545c812901c0c9602c2c90310394000c0c50f0b00020b04020401a41c1024040030100c0c4000030f07103902800c82c5c03010607252a00908203510000b403019201454410000506218100c0341900640743d042ea080c0d0f5a548400088400388007080c4503110320400d440400340305032494840402daa501c00c1d01c0c40a00510b039620b5009003001034209603880180001400c05080c540c0300e81040c0000e500460382c02074105000c0e40b00241e5030000300d800e00303c03440d01500c40c0ca01c05460b2107200d08003940025440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 981253857 1250 981252607 981252619
    0x606130504110a0906080c1203040302060d150f150e030d0e18010611070602070e22060507050c010b040902150c030c01020c0a111815030c120616050403030518 70
    0xc1c20b4180c954601a0004000f01800031030300f280340c41c1e010ba0403c442155558010040e0040b8650075110000c100c4040725130540e0a00d603103501746000800105601041c1246480c0d0b2440001a20b00d500e03500c010a0b13480c020400c061540d03441d0001d0380c109a5158136650176400142e4150f0080d0f005440e0500740403400b40150882446807080707224141001d130000c1c3d01107488840e10010914081241c14041d0000c1d000400a450401558505041005108501d90905a05900c0314190841d1080d2501503102c070007401325082c0550050032070b03000340b40d5400c015071802c034100030301d4a85400b6206100341c0242045840f07200700c0b00d01d405654842c02841216110030071158406081c00d10080c4004c060000262021487c1c51034080e10012403160701c1c80c0324105520380304515008d28140903811002e07040c00041401000d5002c42e0030181400e0714207610050b01d0041d0308a580e800b1900b140704808081c1e2030301d22110391100c241d5107801a8040507001400c24801d4464180e041c0e8606030310441c00130a5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 981255107 1250 981253857 981253883
    0x114090a0e060423090d0206091b040b06030f180c01080a020c19030f02120a050a0c02011e170702071a09040b0a0b1902030405010c060f020d02040b070b090606130504 73
    0x8032071340154042481d03d4a54480f20401038019824800003914150074800b030440c5007001810740b59500c04046a03039542c00c810010300384203651154884080c021000c1d1001d0340300d160005000803548022104080c1586505004c0300c0205800f09020441c000141c6404095880700d682400003034001e021008001d20030307900c10f222a0501003002402e02482991214545881050b00a040202d800c031040401d20081c40520200794100d0305880720350301540b0b00002c80c074080740012104041c119210f4080b41107054803510f00304d98001603043c040081da000d103080c0c0761181039040b42d490425104211100e01441541011400088010b0843c0e8070000d101207020b42c91131001035440c51059201c000710b01c1d400075100c04540020740f01d00c003a01c40d5a0028500301440e190010304103c0035074100912282d690040c40d590000190705941f14032000314000c42d200c80d1108400c420681c4010340075990400990b001513400d4900182e0700c1d00c5140094841c2c5404416a80c00c0c0c4050100130f0700c200c901c6914049 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 981256357 1250 981255107 981255131
    0xf022505090405030a0f0c03080712140c0409060b040602251a1801210c02070f0b040608010927080c160918050601150207120b060114090a0e0604 64
    0x11680b07009034094005140e0722001a040a40310b003207501c80030700612514030f0b04800032a80040c54140c0c86215820207800045d00040780000400d030740c1c80c40da4007030f07d0070509010f10042003802410554864100070094203440c3e18134821240554880c01d8010390040d43d2120100881c404040c0c0740510300c03102041c0c065240c08400d01007004501c18003100d940c000c1684800381c1c00c1d0300390402025000b070070b055050391126003207840e050000b411806181c2d9103c250400409208002080003801086e103440f410a0301d40c04012040e03400ba20944000440010021a2050703491141c0c17411403080281ca1501c103801e0a07010362480f0552032050714414424000ca40b40440c00384180140c10000109500c00341c0d0a14480100f190001d040400b850099440e00c03d000510000310a41034071003407035a082406164420032481c0c4803541e000690390160240003481040041c001c680c1c02481c09885415500901902884503030081182069008455003000c0140760340d14545503400000c0035201065059100b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 981257607 1250 981256357 981256369
    0x10212040b13360b0108041101050405180402100f0c120e19051306060c08090d0c2903060d060b04021e0d1b050a140d050906160f022505 60
    0x2401d014110780c5000143d2582e80000000c0b4061095101000c02481400c0c200003821518000c00003007200450381d6290a080c0e010b401505c0013010002c008204503144140034444807141583e00305c0c061005800300c52240350080628a00700f00382ca83c0c03050040c0d083c0b5102c032403040340210103020500140d403103c003169442d02a0302c540c421180010310201d41c1c2c079240521105e40c4c03640c4a0740b08003a03e131900034024a6404004c480045412007007c90311000d41c8000100440d600500082c003545549200280300e002910502140c5d003514003e4101c0d0301c0641011281910040b1030455010180800707040001c0c00d80e900603952240041d00042c00c10200c2c18041c40c2c1c60b442c00c5208024148d01140055001c0881d0040c0d801d030b000b282c07010b048202c10360a406000c41c003540c0556000e01126200d0f0700714400c01c607010b940c0341030050007083c8124280701b0311054441d0b9054400521010110030400042b902454100000914031303401060035001c1e08940391042c128107240c030040032054000c005441d03035030f01d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 981258857 1250 981257607 981257639
    0x20607050a18150210020f0a0c080c01060e090f060103170705010f06090204081c050306090c0702060711030c0307081c050904090b16030605030c060d1d0c010e010212040b13 76
    0x6450001c00c00340c0c006001034a441c800d803080c0107000340100002008071818400391240842340e420f01c4011121546011201d501450101c01255031030310b00005a221a132411681c0a0405802561104860b4081864039800e09003c054181400c4940880a01a0003402000418007800002901d4040070441d00700341c412a038460300c680c0750081002d000d514010300c6801803e103d50702c10000c190840903030242041c00018403441c4901003a400190a14200b0821150740c2540240070315655070040c5010b4410540c2181007038040d11440601e080b0500700050304105840c060001059401441c1110304071042411a51a0401c00b0500482e101038603240580d1600600c00c10f481c00e541d1816118601c1001002d0304402e0425044c40020032650f10701044401100905907806a44c2c2e410510404001d402c00302c600c019000c0262440034003644010640c84d0407014241d0300e10300540083c0d001260358103205501d00480d203004102c20030000c88110010500070407060704c40d00c129075032141000d650884d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 981260107 1250 981258857 981258869
    0x15050708060105310f0e06030a06150b04270c08040210020c180a1b050d110f0315040b030a150e070e01170607050a0503070c1e030c0209090a03020607050a18 69
    0x207103003005d000640810f030400b00600450082129180341240c0082e54900d420280a0942c42d074400c140040c038980306401c0005000c0ca90756031542d441d81e42c407000c020a81d02e100c0344140da04402500e104030201d80e0107503818010085d034440007643c0f1a0303001c10690f101812005030962041401c40c40d8140c460801c103129910010079010018a4241480816141c024007100701c80805800ea1082c0180c001c020366659200e079003c001907220b540301c9181d817540b20740301011800741030200c200140d40b004211958406441941c09101b6542c3e000141650b5030b0312000c0052407008251101260514954003010040800100b1103c203541e80c1c01c51640220000c1c1c1009050820707400c0303000100c1034100a142e0700301100b403030068035100d004440200030b400050440800c00142c08551400d004c0032443c40c0000500103100c5402e40c40c100c0c03030701900b2281c0c00001240500a80d80c00104040004128040d0f92901a00900b5440c2d580d040101c590354844a0090280503070060300c0450060b04540761405481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 981261357 1250 981260107 981260197
    0x10c02030604171e0309190302030304150212042915041509020a022802062205060406050c121206120a050d031e0621060609050c040315050708060105 66
    0x8106515031f080101080ca41801200640030201c0041c2d0700204590f44281c210501d61100b0803100c42e080e000e40328620041010303940d50304c103001c144a080e040c0141c3e1150000c000310050103407940d0b02003411208030350048002c402d24443c0d0020381050f4106a041d81c44071401c480d07c0742d031074408080490304005103a07401a0312a0070100ca51030034401880d001000504e40d0251004001ea0028840d440782c6a20000540f507030580c10101c5d03014000d00807002c4d10000b080c890f19180c580000909903000200054881d12400c552002c0d042403d004a5192500d605130f1100303140d1b140c40900504800e07400c501c1d06284111b10542d00411014030580305190b000356404103c03c00121071500e2503007030b4101d13030120a510b4a0010402000c1c0c05200c02d000c84100d000300009030b119424640014a10356010100403400d000812039011070004c000c2c4182c0e0700c81c805002c44200d041440c00e040355002c03609000810a0500400c05560148018000022010314210802d40000003290100014000e00a6280d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 981262607 1250 981261357 981261361
    0x4050d0b04200f010e03240916030203030d0e191a0702061614280908160902030a02210a0507180b0702010c0507061d010c02030604171e03 61
    0x2c00801c075004800b9800142510281c48044002410031407024195418070030700004c50f48054078180034480181c01007907030482c02c1c0c006180304070400702402c0380c120100b40260440c49544901050b60078040e01c2e0080c0095040280120155006010010040300c50348a5105111003c87d0a90300d840e5040b03105560511100c5007400842105420280420042d07401070307020072160310380e88880c0208042c00e61500000c00c881c02004c1d43d40920940003c804c9051049210724001252003007010301c2c400c000d94640e03102c195580c0311103480d1560305004114844446004200000694018540242d00040014982201c40c00da4400100c0240075a0220b1903211003044241c2401d0721800381c3c0403a290406096000c03010354012001d00b0140240a480e80010407103d0659108803e6035042d10307030010031035600c10340760310001e808681d000784224000c0500b00c4400445511865050710010741c0036000300300d25100da655084042008446031b21901e0000e00100140000840300303140145090524541d0705c4c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 981263857 1250 981262607 981262613
    0x3030306090f09150515030a1b08030a050a05030606040b0c010c1d0d0f05030c16080d03020f2706161502030103170304030309050703080901030c18060e0604050d0b04 73
    0x1542c0e1200820542e1440c01c0203ca0102e028000007001c100d0003018000303000d5884140084241012000903501881030b81c44e5030041001120010f054145d208903898111946c0b81c3c8410f91f03a06c41c0d10451000910b080c4107003402c2d80d00810180d500031070700511003810a0348a040c050030680041821040e181e44030300c180d00403030380c22a04245280c0c41b094402e004122061020860100d41e503e8000c01e5048092815070900a0500a50f0444e503e54803e0383e40014600141c405010b002e400b5001040c000c01584401d664040e1003190146601d00840710b007487d0a43c1c4410a8107000e44034140003c030111401c422459403650f004000740b60351000900480074880c18418101d0380341640c1044550710410061021801444406074130b6544541c1040c0c1c0c90780e891030200c02519909000600b1032003981c80c00302c00c0184d10409014802c1003030760108601c6400c9070f800c88025050903004126810814030520280744105490104164050602031030070341e0b0707a000304a01c0f65621078256288a003600a200c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 981265107 1250 981263857 981263861
    0x30207060c0804030e0f030102040f030f14010c021b1801030b1828141605040f0c0c14011e050108070e070e2106041b081b10030b0a0303030609 63
    0x84101c461800341d08500c1d260b58060003c0ca020004c00d0300c641180e01514090359400d404031400703850040c3c51140ea043e84c81c036054050406808040345c11200c00d003515040f9203414400c4070b2840740c01c2e90040401500c0b0320040300c3c1500b203240702d00390404091100c2c1e40b5210303103e0700101d0007148150042c503c14a40a21800b144040014403a440d40d0403c0002c08031445494010480024103c001049451038510f403407140000049400b4615000b440000c0200005400c0307a00204e400642c1c0c18020503122038050011038089040600210311500034600206050304d60806031507041000019a001c8048070748000341d03590140c000b0301d0a40301c40051200d4501848240d0080c51b940d4861a050b051582c4090403103c04002c03498004c081e24452080d045912508000b00c00d4200300036501e00c1c0c20300c0d0500890ac3c3c1203511121810903854200000d90701400220003144a02958444003404107a4081141402c1141e084404268a0b1406a5036503601c489500c0001d5200ea14001200342c904800281 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 981266357 1250 981265107 981265121
    0x7020a080102031006110f03040311062502030d050903030a030c02010e010207060b0a050307060f050d0b0603070203030402090c040807061b1a010f080706050a120609020a09080106080a0f02010503130b0703020706 93
    0x29107030480e5030007c2c81294008160380c10340e58000f8006540c5040c1c40b0200e1900d004404c942e4603a01401d6151030700300f0a03228500b4180038025020b40d12480103900081c0d446202d0b00340420380550042040741c0c9007a110b60b001c100e17107200600c00401c0039101080200c2c26600b101006466140d5140400c843c1032609040c11070003403505074017400845203810310103020400880342c031000b801800240001c64510070f922010ba1140008d2180b81c40e13007040c020095880e0000c403000c03070003200c04c0c0c00800c1d44491000d081c5c4003100d110800030a40b4034201a41260401110194850241d410f036140000241d0b08008440c0c2c401a00b20744c0f80459807400d00c0c0c0700d82840351a40201066080348a05011556001c011514804118241892440c00d1040c02400038215907101402c0300e440405c000d00c12550101d080011110180000e00203940c03111250782d2181401940180014010f541c45401940554013843d40844a1519170035900516100d0f465481800c540000000b03600058403020402c440c41800c0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 981267607 1250 981266357 981266387
    0x703230a0914010c1704031212180c0506070303020408030f07170903120a0c15020904060f0803220306050a1e0b0901180b0409050c01020c09040f060207020a080102031006 75
    0x2c40180003800e25000f011000e454a03060100345507040140384103e40042d035210308888070b17040c0ba404c002040d10303540a8425018600307040003110784402e883c0c40341011503000040104150300e0441008241c0d80902002c40502d03800780070000d12a04184003600030400041c1c400b0344d49a071035103414100c1d40320790586012181c409109503032043d10700085c0754503901d250000f180c0d5504400b90081d2a000c805070002046090202200c619601458000d08000b40c02945c00b0b00210342c0300e600407180c07030940303004849003544280071707407020181f21184030841c00e45600b4403842d00c90707101d441d00410743e0b104917418400b15460300ca0513440350300891800c14404848040070420492001e00040003148113105000360146805070300012600c9540c404045000c1c001c108110806040c035065484c8c40010982c203000d401100c1d0000c11508100060740d11440d4090302441120341c0e01d03032703641c80250800d80041c2c0e00002c100c100451150300910065014108132200845520302e000001011420414480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 981268857 1250 981267607 981267629
    0x5060f090903040902090d02090403020717030408191e0c052403180106080d1814090a020f160807021914060c0109081207021207170703230a09 63
    0x1407a680c0110a980c00c4d03441810b005079869020303200003814895204006540201c0340820300c0101a0005001d50440e1314003821400c9140550441544a0080384650303000e0b5004081da0b012416042d18a61146074803070451341000a00d2030b8407141100d40d00c403d00300e8022455a109200c0307446c101e0141d003580e034074503d10103101800500c500c00560001500d0010301c40354264080b0500b06080d0844006040302e0b8040390011030707840100808044020b20403004903450a0f1001c50707481c01c1620000d201300f4018212007103649518401b0380c02940b0080c0b446034001d030180880d129403d850b655400d0000d001e20720941d01c030006401041349001002c81171003242d05240c4420010820701103095001e0355021141140c440790186125405401b40c4007005112400014400404100703045c103907409500c982d801ca411310482e14010420720322510303001804069400c04060103d84004009100942c840d04c2e0911a0141d0a000d58044080041c4045a5a000411301000b050b0340f004c00000245000204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 981270107 1250 981268857 981268861
    0xb132301090b0f010f0c120c14060105030601060f02010e1b100809060601050705010905070e07081501051b160b09030f06150f0105160804030b1302010909051003080c0105060f09 78
    0x10f03c0441903c035040d041c001c5803811005014011100e02c0090341c0c0202050070009080c0100030045001c0410071030b598071080091800341e04001811318141e80c0f000e0f0080146908126041d108401405505030843d034a803070404060103028005000a00000d0034a00b90741000142004800382c1a50030503010000c4840c1000482440020340c0c40c2c2102003820129a00d500f01d04110303014005214001c2c04030b00c030300d0b0800110684800101441a0503907a0303280e8450b1900180e48070380307111b100ca0740c1d4001841070010200c0d9012034121170b20521414400c80d0a0004416428041006141c0c0101800080421418058107043c40302800a950300300142401d481d0080380f050007582c0e0080d04034003942d030428121100b64081d404580412000c941c00b2131201c5910310708540c003030303006000803105000640e000c01c4c0081440b0380800c1e0768550503140c0a00c01400c00018400030140201030203611b4070703105000030100b280a40140b0144d85480000700b59032900005000448040c02c803903501410418017 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 981271357 1250 981270107 981270109
    0x30c0d080f0903070309060f11010203010311090c0c0a060b0d240606020102040602030d0917040b0414040605030318190902030a0e060103020a0306022d07151e0b132301090b 76
    0x21084003547c680d8140a01c004001e4030381105c98032038105e050b03100d135072000001009012070780e03a081c0110142225000001d03620511141000c1c041c01c1c000c0441a80300600c1c120005040f0380004c004d01134060200514040e5540300d65091030300d12288400c000203000d01d440052750071030150101a0000c1d0009500d4649090b02c025500d104803180100a0b50341c071400f0742d0401c484000c0b60f54801024120564035541c032400c500c02c07203501500c00d018800307070601c058020780d041c14080d09049034401000b460a0500404280001c1c0482c190a035500c0780710001da00c0c0e0901a041c100d440a468405401a100d1900120550481c0e03a41d0b818514164400401040103940d02c0030ba050603680d010701e000d030f21020004402407048610b24006511940c0020b0100740c0301c515034014080050089212058002d0f54445140444888080440041e19951100043c204d00e40d0400d800b42200544801c000d0380a482e480340c21190003240c00340c2000e0b480349071071907158040c008043c05022402000c00110441d04c2c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 981272607 1250 981271357 981271367
    0x3090f06130f150608060a0615050a03020711030d020318090903040303051e0f0a020d03060b031501021e0c0306010e060a060f030e0d08060307090527030c0d080f09030703 75
    0x600040402c01840180e00400c59290800d58460342c20a070140444d5803120b020944850007140c459103071074036060000600c01022078101900603c1912280c1c40d10148110442c0030354008003003a41c4111400c2410041920100080c01d043c190f664041c646420385607000d06c002c2d10691408920070340c120810b10100300c1d07003c4100d80480f0303418109a07607281c400d541c401c581042511b000c1500f0a002151007545017070341d1070007006007901990070ba402802c140790b0250708945aa001d000f070f01140600c001100c00c02c1000056540540500440d00b410760303024071609500d00314816101c21604075044181240c14204152400b502010301075841e285031600100d01810f21900c201d0003007012880b0b20541e21402644004401400102510300d040092100500441010344800e4080c3c41074443c0081c100d01e42d0310849024141c01e480300341c40c0108800b031a8035040c0c2c0303825845841307001c03c001a40e0000700805c14000d0794a45500c50050307a203462012000040c10003002e1060540040040302c000035404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 981273857 1250 981272607 981272641
    0x8010f0530030a111f09140d05030105120f1f020702090c1305011b0605070c0b090106060206060415030209062b0b0703020c0c01031a040204180c0e131109060a0503090f06 75
    0x21705800544004103040c05c00000c160101034040e98095284140b00715a400001541621000d403401c0c4850360009880c1503031a501d00c501c0c2c2040d500500740c13010214030380396404074007664031140241c02e0401c150009035192030213540e210341c1c000c0001481d0308000c642d404000010602420b0041006501d51198143c1115034500200919901c900180c4480d0141034407880a0b50000f100c03560a1400410441c000e214502616000d80300c2e0000040311458039000d04180b00c8801700700704035007914507400d2045450016045903032100c905a203001c06103942204039014034203100c10910507120141404182070102810550802d0b00400c440d400c00140014140b691107028a8000f96840e418011510241596003585134050300001c0c0005185039503d00000d030b0520503807000c11125000c80030554400e21441c8079070fa0021001921245000c100745c3c840d05c201154020b02c5440d1295020024029622101c40c04001c2240401880301e071002c1044105d030346a07085801080c213410705402d002180c5540d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 981275107 1250 981273857 981273913
    0x819092406090207030e1806030c01050d0b220b030705010e1c06050c09190302090c031308122202090a020f090d050703021008010f0530030a11 63
    0x300c010000031040264490002800801411034540b4103e140040c00e0807095055944101d80b4036401405510a1400c03080c0207100050080200003c040015a407079000000c010000c11b680f10035443c040e85541d1804042c40142540c0304407807044091080341143c8500d05994002e42c011101403041d640c1000c0802003605007101d02c1810000001c5800c1140d50b445030f0000c0140b42440c060000000812018005446041f40d903e4030b84d03501025409000211407102075840a52080401c1400303e4030317802560031001c400280480d0700070382d840310921070380603030085c42661005104101c070810303044a01641000380c3c060b0302148622113070001008180d0160101841c29070000d0341c88002c0700310408440c800715010707080c0c0910030740508005880716402d2200340d018100d1000030440b41403142c03100a05840c185007100311002d007004244a08142106900d107081c0113040c0c0d68085414080c4c404d96044101da0300116034991884500500c111450709480419a02c400200902409298072841045074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 981276357 1250 981275107 981275153
    0x9090c0c120503010e2410181a0901050c07030c0f030c06020a0c0308031005120102030a0e06070215100506031503010b0609130203100e0406050103021905010f0c02150406081909 78
    0x241c405c00e1072001d000501916480702c1401d002d000e0154108110051400b808d038403525030079075030304600c0284000e4440c903185514001c000380104d640c002c8002d0118034410130111030b2140e031203039205c0100c2e402d250090810222500400c03c02c101401c0e0038036000d05007910113000303032135101c1e90ba003400311503075020050481102200040c1d403004c60340c404000409004144401524038066060300075031043e580d20141e0f6041c21340c468000680015624062001a4000c100b00100c0c60200c6444500242c000c0c0c5080c010546c00003000e5884030301450013180032942d4582c5800d805c60070142120358007040140100d10900180c4466540d401200006032005100541d5a60314041c0505074010385410140c2051071242c280018450315030b11a5058070b01c29242e811041c01c44c0103118410b1181c51080d540042c0c242c081c1070300300314482c070890104644080c0c8182a05d4020710315480c100d811542003000040c820b0002c112034280002050101c00c4c110b06c00030031240c3c4040d124145c401a2688003c8080d030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 981277607 1250 981276357 981276391
    0x60f01030e06070c051f0603050d14120601020102070f03030b01090e0c1b0a0501230f100b0a0c020306280903020304060f0c1a010e06030c06091009090c0c120503010e 73
    0x21091002100800b80c042066500d1101036144e00011f286500082d140361285015070716001d80280400036803214000c00e441d003031504840b25540d081b5002070419045540a11040300040d1005107090075040c801d1320049081c04050000401640b861741c02072100174482e40500c110020010202d690150540591245002c2c0c030620082c03918402d81170040c02c40d0710f082c1c0c3d0034601d4040e450b1000380700c58046841744c007152550360368540e6480c0b040d030b844c03040604154020071654009800403c02c4004a0611003011181078000a0411500301c41c0029a100d08091401074000c8402d00d40c0302600348a0020040c140d01034800039940c2c05540540400c1c00161103440c1245405404400105075100c10500e0781c1d045003402260030a0800c0c490a0404481ca4001c6865807034041031a554921000d0034142c144615a010410b0742c040212600741403015220000c0f4100145010b83c102c040e400c0e40f52041c40c0400c1c1c0c41c0880401c41c030012440c0c00c00105200601c60b04140000c110b802040a400d074100300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 981278857 1250 981277607 981277613
    0x90501060503120c07091505060c1005190f050c0901180b0301090b0112090b0a02090418141c08072114150105040e040b18060c03060f01030e06070c 65
    0x1018140c000e00c0d4140f01c0c40300100f9480e200d0400901041594009452009541740102800d450340010090344a40e0075034410700241c01c09601a010b210002d5085030b0b5500c02c00301c0600c04070f680654011544c100000c0864254aa02e4000c1c8000e100039040e04012500d8501c4600d00e9502883c920f0358108408a0807a0703201590121009010301000300c8515580c1d6507a0052400805a20845502281600100303d4031428240f18042189411079055441680c80c0e0480100a600c0030100381c0d4007070340d40d40c40070b0520700c2c02c01e241c2502140300300341041da0040000380e41c6181c0364210440c103021840640da828210f0f5072200380b054200b49181098801c81c10a94011400800e41c0240500c00911309021048080454010359005070030031760351501c8003601c0400444151140307011700b804e030303503802408200050000c5150030f9110314411041e406418803083c415081c2042520030b0704a0010100c04d0007040d103003682e10907c001200342800c115189840507900c1d10fa18004024209000c02c0d02c0e00d110038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 981280107 1250 981278857 981278861
    0xe0a0b07230715080402040b120a1104020c0a03051c02030105180c0904090f03080106081b0304050c030a030909050a09020d0222050915010b0901080c1c060605040302190e060103090501 81
    0xd4045556a0001c0c0b03002d0603c000c00c1c8100072501a4812420301010010724101038140c90100c00800c40909500c5201703441398480b004c0c01c503481541240e0708100c80c3c2c2c005101441100e000301d110340e580a40e074400342d0a10343c03c800c0c0f040f003100c0742d2680304100401050391041140180c41400015895107603a40c110b035141c40e80107480410390040d0a256404040240c8141005c010a11940b10641e80e6600c410045821440840d0070b5110880715280084040d40220040c5034814860000c036220200d9102c0400d00f4003803041d0080300803541041061007055220b004140c0e10440710407042201a1140c2c001130300c0010071580c082d0103051080d000b0720b42140c41d13580800c150070703071b03e0401e0200b4201038152540d1901000002400200884004a104031a07007080300c103400016514802c80382c9a05801103142c0e4003500505a000300010807a116038691030103800000c0c800c54403096141c86c03950051003240302441404252313407203501009004983c42020304580001c42884e00080804da07038030748140 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 981281357 1250 981280107 981280109
    0x60a0c08070209010b0702040507030e0c120f15091e070501031109030114060325030803092104090b030d080f10050306091c140708280e0a0b072307 65
    0x500403081000100e110809031000301b00c0706100356000c10141c0e039203a204800f114015200440c454101c0d0001e198186070000c640c03c042044001900c849940480c4030900e8036150443c112440c3c40d05504116a01a051200307211004035860213041410b5964a0315403100441d0007281e040c950f0f1544070281c0400c0303540076500d0a440250081000f900c2100781c0040c040710464501c1d01c02d11604c1806012090360f001c2801300305c4003164030700c2162070440d5108119500001c0c8099840d1040000c00c007540070007004400108981c441e5041e5456092410a00941301c1c61100300c0c1c0203a20841d6042246544405100c0c0e100e04a000706105079200c1c44c484604904103503000c19414402c41090080c081004207459030350780c00c0510a52030020fa6110700380e03009803e502081ca4803030030034007900011409000043c84141021040101c003440900310203032141804081e0000010140c0721209600e04040340e4036005003130701c1740d025801c010280d40c4d00d45015844c070800100d0056002c01d80f01030910308100004c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 981282607 1250 981281357 981281359
    0x5030a020d09300306031a07051c06140402040311010e040b0a0803130807030b040f0302010906060b030f07080c04290703080405011119030203131b0303110606060a0c080702 76
    0x18144603d00001154807580c908807040d10500d0038650f10366200d0003880f560080b25031000541340301039410300302a031103140020700b210103205080003420304414403915003011350350740040001400b6040241c007038029400c17006014041c80c8104420300c0450780501003413038080300074648001c0c0304c01c81c900400c000d0403402d0391158204450110100306440040f02a01310076443c8004040819030382e0b4440d0795925403622000d08000700600200c1c2c082003a07801c084580074002e000100da5100b450340c81208580c1140c0c4603c2c00c08601005000302010907400d900e4021185150145080c28509407514642c070617441414400c0d0f501072070241a200c580312a4441a204000c0c4868a49015081c0070303000b008115802c4415503c1c0035540020412902c042e02d030901c0500800f6140910300311401c1c0c0003580b029003c043c00740d0110001c600050400c100994100050040941030f83c0e16501c0c0207407a009142e50800210b03006201006620786404e01a508002c1182c5002c115170165800c0106032403044c01800f03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 981283857 1250 981282607 981282623
    0xf0604060e09090a032c18040605070c031d011206080d09090216170c070915050d0b0c03100f060e131424040509010c14070305030a020d09 61
    0xc0d8440e00444607858100c0165010340141c1d8810391a50b480f00f589020007404614444000c02e01145c2c03a002c0710031410707003004106e04004078810010700040803c0c102d40c800d26042d50100001c2061a02030140c02080c0341c1842c1000513466507020303041044010810344035420818540c242c0d81c0c46403006a41500b002c0c40708004190300c40c66800c0d04c848401c0b0062022448400b0006105600c41c42151040008041c0309402d44d00c0a070365882c8100c244800360b22141806000e000c070022024054100104100000081d01c4020301902e42c4500000d9400b451050b8207900b0704402040c12240e00c0b0760303c184201ea106946ea078031182403141e1490550080c260f1030f00c5154001c152030b034210707641c031300c00700e0301251020b035000420101c05003900c240d007119900744804003002c00c46800404100c80755211308445401c0f0300704184004a0200e61045481c003480e0ba440d00d110b8059070b5007006903410f10b13054448107030b81360100c291800b80c04c83c0300180c06039403001e40c002400c0709000041e6009041503940001a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 981285107 1250 981283857 981283859
    0x309060911030706050304110f0117090c0906060f040311030a23060c0a020307020d0302010f09030801050f010e09070c0606051f090e060a030b0a06030f0b0103030813080405040b0f0604 81
    0x1029041e2003a400d218001d1140f4440403071824001c9041d41d02c1282d210059140d401d070340703400b0b02c40710380c8910001c3d5045c854503108520b0492041c04030f45100f0582d250042c00550100c804100115401800302805000c08109004545002e40215030a9a8100d819000c9903203205021a1600307100b15009011600b8026901d40c0b01c00c911081004241100400c0310190303150009140442c0c0303d100300c0035015038010840e210060070030b05150348881d8003c4c0000100424070000d60404c6c0d0b08414402c50000e4007040042c031040ca021200d04403102c1085ca454032007c1d00d001c01103001284050a845c003441810000d030000c02070540c10010181502800c900c0f044a0500a18080b05503c0f00c24500070509030f9001040000c0021900f61086900030417010a081c5184c50f003440900c4060860130340d42c2d481d00c0002c03010600380c42150080910400002e091580345013401000b11001800f4091903120303411054001c98a180180c8068910440b000100080d03d40b00107100e40c0138458004c0e4001402242c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 981286357 1250 981285107 981285113
    0x709061d150a0e15240a0c02190807060e0f010801050f150c011d010c02070501200114160e0f01180806090d0212030f0c0a110f0f0c1210180c03061a010c170a03090609 73
    0xf8bc41381c200e8116498640e10446508100040c01724000491b0b400511407100400c41880c140380309020070708001c0c02d02c081c1003c0d00355180d60306d540040390320013507691502403c0c9403c881c0d651003240003420343c400800407050003000c025200d40040c801d041c104840014403946040c402c642140da898000d60081160400c19120f003652058110346419846519820500d174850040e25100b0703603208020048030301e5440030b00055814500107000021044004200800d918030104101d60140c102d4000508641c040024028a046500c98403001010b81c14003c0c0030621100204441d000302c0d450072050384a00c50b01e035048400d500c101105100070700c1840300b82c01202e2004030b81c02041a01c04001e07184900300c40010720520501d010700400003a44050070300072095440d50b100c0d084903900380240001951300c075107c4100b2a80903400c01c0e10035035a5403040c04013240d03415020f0103c0f030500303007802d00480440740c8900750050001003c410000d0400101c07010000c2c03081d40304a8549900000070030003030407682 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 981287607 1250 981286357 981286363
    0x30b03121204060b0609010c080c030405041107140304060c080901140a03090506060609011d182d040f030f02070b04080709061d150a0e15240a0c021908 67
    0x10301c2c140c90703503854904102164100202282d51180781a1151280c0344101da44904642e44200d142100382d0005100200305a0340307902895a503807030017940d0a0b803508201d040025101c4000040d0425941c030402c02000f0840c0c100c0b1854400540100708070341c40d40003140c0162500c2c2125039286c0c4022400041c007040d05c9e90590300c0005c0c40350042d400c649580c0e882030144101d6200ea41c0006001c9000a04a448626000d08a1f141400c4001d070400498201500c501d0550100c04d8800c807646d80b40716510200040090200b2511a4140c4140340d102c0c1c3c2400c0e121805011031400c8060200b00071038841d00d00c910700810400c0002d04500f510280c0d55690340c186a51120f003103000740e1035000d0900c200055510915002640111490044140b035515102002c44003001c0c4074801a4000c45008000220342a0300011140325170b0b005902c40303c07c6403891041240700c4003454241d60000883c0c010040d90141040c0580703503605003a040019113000d09000040c041051000d001c05190710141001c0340421003c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 981288857 1250 981287607 981287611
    0xf090819064d0d1d210c01090f230c06090d1b0801090212010209010e1009031703011509030c21060c11120405131d0109060c0e01020106080706030b031212 68
    0x11100d0003010349030021300301345c41e000703554080f0414030b002400710894040d0410081820500e40d42c00042d0f5144150340340d00b6050308a140a4039011189802c24030703c400390074800003290032044d001d00f1550018500044150090400d03450142c82101950410010900c0c1808025800c10031100724031581c5040d039070f019180c4440200d0203400b08010706242c84105000365400204140c660180a80050080c8017080c100f0700360040070400074120020119010182c1c40c41101c480c200100c0d17aa40c1001c94406200b00e2030300494080203400c0e0020804540c2d0001e0388429103000e09911884c0060350459440f503040c1c050310140100f0710384010780d0101e0ba005525020000308002c01c7d41c42052144292b20442d0003a440760382d030000d405c48034440b0b010750980c0c020b60b512407aa0648182d00c02c54004c11a003142c0307170020103c50150352902810760058000408000e000e6091000740100c906129034240c4441d0140300e0007040c1501d03800b01c003403165400e1007194900c882c0c548030345031036100000503506a5981 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 981290107 1250 981288857 981288881
    0xc0301091101020d09080a02040b1f090e061012050901060b03160806030f0d05030408071b081c0e090907120605010915080307030f090819064d0d 64
    0x2024034942c044c070302072000d40c0100c40070031000e42208a45502401b015082c0b032a03c05234440501403103002c0c41c0c3c807a040e241c041c4019541c0c4041c4801c2c1801c030300449841000e410300b07100b40c0100c0654164154051407059418900c40c0c0c0204498550f048040d002d000c2c26088950040800f004000809024605201d6290080e681d03482031611040c0605443d00100e800b0114107400030b094903041140144001c580140c40345001d82d2814449840d000000004e0b207040c402c80703c9810904100c002e5040151007140794505c110f03c9200f58540102070700003001d54400502035590100050a100340c240721040081200213040b03050f000d46441c10f6801050240205040d45240c0b10050410800fa00300c1c00081e035240c8402585000b515440075aa03c0000201d00c0c020400e03942c9010034070f0301040c03040700c0041e0040d40e180301d0003244504e00f40d000e90b4101081e05009003606080d00741940f8142284050203505c1c2032184803201c0b5000041501d401c00315103000da2450f0009405016590380358003084085103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 981291357 1250 981290107 981290113
    0x1a04110903061b031b0912010e0601060813110402041509030c06020a020a06180f12290f040305091e13060f0512030c15010302130203010f03060e0c030109110102 71
    0x40c0300c150445400760800c000010202e030610000b1072030f00c1c2e060b80511788001c2031500e07642001c80c00c80000d24031140300d4410720700d070341d440d8005046090b20801a881c0944054140181c540c81d00c4d0020602d121124400500410481c02d602e403010744455040fa0301602e030303a00310052050003000e400780c099203280c44100d82c110000403002469070301c04242d181e883c541c020191149185403040880300c2441c030f02084a0060208a0002490b00366050b04c1d20007003070342c0d02608814413624103059005102a4880c6030500600c0f05d8401100340c034068403190301c003501d0303c1c05080710b0702e890900f101d0b2400340001a83d0090302250011f02615034142212218460031242c046917038441c40031943c103642d054451005a009132040c00e02691404450f4411421101001c880c10812450b0403149051603500c161842c1c140010014020340c01d0024000c6494040c00c00103502d55450010740100d820003a2001a1066a40c0c44826a0000d41448905104000140244442059410582095040c00b000a40984 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 981292607 1250 981291357 981291361
    0x6011b021026040b0a0504110907080702071a0a111203040f060f09110126160306060203040e0118020f0c0706030f0902091b1903020307020d0912061a0411090306 71
    0x20360100c1030074400c036407044a0403101c1d290307602041c001d4003020f4001c5444000c0f049048c00c1c19200c03190f0f404c0c45007034941e9403038038181490071001e410700060390031820b6610800c001034076401d090807040740c0b900c0c5041e2800350078803a10030034941e050031031141c0b028420740030000c24003060000a0340f11040c080e0007214104501507520074804212055444018074400f042c0795200030f00d40c0914103401c0304e481454580803101c903c0241010380b0940c200e0701a18100f01c040341215046506105400161038a40021454903003000d4040320005014441e440c4074070700032042d200701c182554060b500203642c942c800b2921611041a07894071130b90705024100002c0c0c6809204100d000040c0650b40b403007500035142841c56248d0007020244101da0950040d00405c040003417003441c48040b464810520002d5034016124103203508000d0800c54141c0380c0700300f0454000c40602000400c3c09903901c040350701000001c0c40c0458407420030340d24070b1034001c2503500c280341c10014001d0b02c03140c02c02441402e00450965902d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 981293857 1250 981292607 981292667
    0xa1205042108090315042d0b1306020a0c0b0601091202151207020a030f1722060609061e0812160507060908060f060906011b0210 57
    0x540200e00c00c078220007548100c01880c5024048421500e00d0049106902e003082050210340303040401c03d20041c44c140c00c441000b041c0690080c40d4403400340e00c0f100b9603408145420004240404145000d00383c01d2010021404401c070100000b003200398815000e540710120100b0150107075a0400b425906410710f00000b07480b9611a121035416640d5103d0a00212801502842001040010210340c2d0710f00c200a684c032648030690540703100740d100b81d0042c0440d4600785070080043e81c642d0381013018411039084002d211380c0311000c2e05030320807090f60b400504c4181c01d82107480b164860f2040a0500303850442c000c182d03070307250b0b412400540784000d055105c3c0004024445115040c81d01c103c0d6907681003400e01503451031840000744288800402075400303500351901d405041406660003c4049030860404224004007806025444600c244140c0407501e030200203e40031100c02445141084010342117848142c1c040c006c28948181c000d0140407254140c00400742c0390402e443c1100c12035001d0a50303a40f080b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 981294964 1107 981293857 981293867
    0x1509020a0c061a0a0902090109060e01020a021f02010b01020a0c27050106030f0b0f010906111006080d14070507060c140105090d0e0301110301052404080a12 69
    0x21104004100144c00307005900103c4100c0c0144002c0c461607030001c22040c11640303a0704011901c5240413004070300b030141c2d00e0030080d80458100c2503d00a03041024041c184041c03076400820507052460010380e41d4a141d46001010030140c07640074010a190508407500f4150030300106035403030a441c038103002901d5098000c400001c0c5da070300c180300000c0c10b07034010403c01c110150f81802c82141407500003412107049000c0e00090002c80400641c0c03251040160044000038000d040003030544400000c0d03200c0c05000c06501c002080340028102c0040303441c00310703402c15900c4402080c0e90351400800396201c98100d1010346243c1c0d8164030602d0440003c1c0261b61051504001618081d941101c0c054444a0f41481450007a0b00d884c201c4848031058a0459065600845000c06511014001d50754200e0301c00300f0400e29440c0c0864005085800080c102c0a028807030110071000e0b42d48000102c41c = true := by decide +kernel

theorem cover : BRFrame.Cov 981115107 981294964 := by
  have h0 := BRFrame.cov_init 981115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 981115107 ≤ n) (h2 : n < 981294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
