-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4867
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:59:51.077403+00:00
-- url     : https://prove2.me/submissions/c6f5c734-4e50-4c14-8b7b-65121ca4e99b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 875179856 ≤ n < 875359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 875181106 1250 875179856 875179859
    0x307080d060621090311010f0c1e02031603020102070816031101111b070302030f03071515030f140607051b060615210403030c080105061c0f0908040e01 67
    0x40108507030154001030700788180b5a02e440500c0f4540d0b54041e04040c41000000340e0500c0300d041c1039038a02100d00a00d4659030030007404107411242c0c0d8001041c0d00c5007580b6008030484090b8046814800900e81c0da600607070003032115000c9038099404500c0368500900005140110b0b646030604142d2040900710180300900b000201019407000c04001c020401070001c200007082e41c2503111113441110b400e502840d01407404014505030500a603c0210f50080445000c120040c00300358070717034004400545002c070540310480c84001d407038001c0e2482d10f40004c0c03884a0321350941d61401d1503944a010107440003181803020900c500130070424076014901c0f684500341c03100e01284500c02c8940b06c0d174440c1c20f81c5030040e43c140113083d12003141d404100e0a5031726100b600ca204201030000c1e540e807120341c00f4142c08030703050501081c10b4041e48140360701c00c1b466440036980ea880e0000c1c004a48501202213010100d03148200030040c1c102c5d400411580102000030401ca80310381c40e00c1c0d1054015810100118102000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 875182356 1250 875181106 875181127
    0x80705120c010801060e0120060708100806011a07050d0207080c10021513050a140d1706011815120b0f0d060b0a0e0a090320031e0c030708 61
    0x14419500550340d4010052000003400081030f0000611604040c0041c0c880380503096806200c01c4000c1071040d00707070344100558448a09a071000142c0d4080702180040700852130300020090302609664140c0010b0815074078000890003034511480401c4a40e074400d01c00342001032424481d01203d0810b99008002c25820602c3c0c6a013001154601c2a00c2683c400200d40302c400c0e004149c0d004000650301c101c407110798825151041500301d59400030042e00820581101304181d205044101a031410119180319002480a4450752036407010000c0304c82e0602d0024005610404900c41c0c101c85054501d0449503a85071851000a264044003000c12562000141880c46902c181c04d1000c804944007040140c110700407508a1313440b60000307815a529401c40d003141e070f11114088002440c1a410a04081c9492011a0010001300000b1000201c02403d607038120802040b4003c102072407103010754500038810203580000c01080089400d07000041c84009040581803000d00540c9008140c0299508440103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 875183606 1250 875182356 875182369
    0x320030703090c060c02151e0702120111120f041e03181202012703021003020705030a030204031509120509040612120212040f0e0403170a0617030c03030609041a01080705 75
    0x14610700d41c00c00107100f19a08c10320080510b00020142922440d074034160360010034a400c0700c418814480c5d41c00e085114100001c07000003015084c0f4050000e40303070f6440e02e500c41c92980000313680c0503118200d443e0b8403115015620b407204009a108e400c0c0882d1940030724400315841c4403981d2003250001c500f200c0324015035030014400d480078070302c036118500300144001640440302e00a00020340102e40aa03101d808880c000e0b4100e400c4540c01404803070b22400a000010081e51280c04100c50b47c0b80c0010040180320f409014012807181d00c000c0103d000c6d080c0c8001141c8503000383c030740c056001c1c0d200d01780004c0031266942014250bc0c000d161136070200c00c00d00303000313890014424120111007004002c100203a8800d06684420760303500d00c1d861116610349060460b4a222070325101c820241c0c90006100710740d203040c0d1005081b115442c0e000a0780c0c01005808a8880c050b40000c0e6009410400004009107442207503954898802e11418500011780f0194200600090300004626884801c0600903450260b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 875184856 1250 875183606 875183629
    0x705070f05031b100507030903050f0d0306090e0d2a08090f03120702010c063b15010e04020a08190201021216060506010516060209040605010320030703090c060c02 72
    0x1407407004071a10700e020214244000404e070344800c1110200c0c05c8402c25209904a400440d00a030498500b10b20407809641c480b0744421a2801203450b003140003a0007003690140400c4a80b1101c00341c84020b40da540d0aa0304070003001d10240713102d81d520041140401811706200b9030b0034040c07800e09448035403103801c0c410b1a010348403003a440385d4041d4079913800f006501002c50f000d80c0d60a180003c6034402501c0c1c410041c1410101640003030344c0303070400681a508800700345026201e99529125101c14422085501d50101c0c0c50b404000109400041c440345194490b41a041440900b803614401c0d9105603450800215030348844100702e06120034425980d04001074104000581c042518080c40303171000300c65440400e50700404143e1640b001502c1c6a001d217085d00d40b002ca0141c041c641520061920400075404135002500c920720b0b01c2004140c075403083c45000c40c01d100c540d41000c03d0500803401250740782c000034904402c164841500400141c0903414103001881152110580c0a443d07104002c40300172078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 875186106 1250 875184856 875184883
    0xa24210911180721140901050c090a09110f0a09082404020d052503150203090304060516021306260c010f0210090311060117031e0705070f0503 63
    0x80351405000e0381009455280c0281a80c02d110504081000713100144040c1a041c5009180c68911480c1c2d0f45480700760301e40c1c416005080200002e0b5580c1041038501e0081052158221403052800d22001c40d99034005903607138603d40b411038202015940403030840e9022a440c8000140115407c0018400401600942010110b504c0d4980040c1010059081400500281c17080c030310711700e911052200034001c02414400001c64444c000c554007103003140310409448101e49483da010b11144008500b031080e24001c030001b03005186424504402143e054001b070301e10311910f1120318030800041c0e44045420a03840c401c2440072500f82d240c03540f010410202880e85240206511004110301e50000c0760b81003003c036007407d0108045011650483c81c02803191f001c175840f1031030b00f00c000081c0354010140c2d01c070302210302d0100c0d884ca070b880c0c04a185840301d24195000072a4402c0c80400e00b03a0400b06135016018140c8040c050602d442600d40c4c2d0f01d4127005a01002a0603403880040c04682018410710484100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 875187356 1250 875186106 875186119
    0x201020709020412230303131b0e090d080f13031e0c02092a0f1b0105090c1c060f020705032706040f050d080f070506060109050a24210911 61
    0xb030081c902c641b64800141046100802d40c15a0410003410340700606001404003140c0c801c0030303240e043c2d0040c040c3d000d032640d003030a208912480075090f2050211034480c0d000b80f802d100481d25800104401621800340031405d0080c0740721040c40704901c0d0481c9401c252203595030305c2414000c0c2d0042c0600e45102800c0101c151040116121040c085c0c0a2140b0303001d0091b44a0b603a03200414aa00d001d1409024070440040d0151818248035100c150810390080c08400191911040942c04000b102c985401031522130a90028800d404200507034880e5800c910b80003070140c94041d803a0f40300350865104003688142c008500000c40c1c004100c01030801100e407000c0e10084c0c0340900f4900d50310410412031040900c981030303406541d000c0080f01025102e5442c03800681d151207110600e00240c0f20300301241c4050000b503041ca0b00041030700d4610100300498403400303881b03802c0b9441c00c034070168030040c0d5200f1002401988280d19640c602c80c4142598015140c0d4000640c04c5043e2900c1744109011750354440c415030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 875188606 1250 875187356 875187413
    0x6041109010519120c030f06050102070521070e04050607020601080606130207170415031a0105040302040b01180602031209030406050406081e040807151401060c0201020709020412 79
    0xb600903048410520740d580a81d81960400d074030403510700d030602c1401400c15040c01d0380b121440350940c1003400100c5201c06c1c01c0c00301c65190401242c1d203a200e4440e4a074000002d800a204000340e0008000318040304200355a000b40d01c030f0280d4900c401d820348017200e180d8000010812403075410b1111074058040c00b4081c100d5030410711f0009440407007580312004400e5002840c2410005440c08450f04142171820f107584842d0340b00d59110000803203010b814040703418038545160200d60455080c40d000b07816100d442c205419074017881b0086c00019140c1d4188a540d6110040c0641103030003c0008241d20750003903580c2c07850300303101404091001d0607005241e03105020a0150301d811405580036504035143c200e0590f41e50304160500a06841d80c0f210800480c8014171040c00030f07038002840800d00440101e142c001240c0c454408890107504444054030401d4018403041e88100d900542007030051044038205603c5604000881c0d01582c8103c0c00840e2502c800803c0100d604156480c1100b030300380304210b62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 875189856 1250 875188606 875188609
    0x406050615030a0e16260a02090f04080919080c03070e0103030e0604150806010e09090607030c0302090a09140c0a08070804020627120a0c030b0402030a0b0f06041109 73
    0xd00015000c400d80a0300e500b441c0340d03808010094405c189840c2c010004105590702000166032000b00c56034074500d00b02103412000c29200051400c14030f0b40c051704c000c1041d07441c1c0a41d04500000078004a95021081003040110740e518020088030101400e019945603240c490804d1400d404108a01d00075005902c040002c0030034800881c2c11240c00d414164499241c1c00009292803007143c01c0f419003420f100503000721081e40442401c2c8212000c1c2c07280c528580d001c404102c103c64003100c0750b101700e500400c0011540352107a042940141d00b00c0c1400360a0690382e50003c0d00d114029080402500e40e038040ca07850014051034001d801c0417400c5130103840c01381400701c010280b000c010302c403900380001c1c0c8001c02c0c1103488403011281090788908072080024030707103984100917611610901c4c1c0324440031410b482c01107001103000740b1900c2d4842c941d4494249599943c0d94110300042050341d040c00348449031008140035050315440760030303000040c01c075925001d0200401c4814040e48035841031428400040903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 875191106 1250 875189856 875189899
    0x405090f0c12010e03030405010917090d1214070506041205090303040306150f06031d0f0a0605040215070c03031701050a060e150a0302071e1109090f0a0b04060506 72
    0x1205082e925001d814554092142c0502074800203041d41c0c4c070002040105001065014800b1103100311156240c011804c00f2640c018040c0030310240e8005684100c11000906051030200c04103030703d042c00041c6164801a810258004810945035900b14104010401c180a0070719084c1300c4482c1001c41c00e007040b100100e90b0720301807804014688c5980748280741c01c0c80c48030030920001f041c495000107072070741d103d00000307020f0301d114001c000c4a650007401e0031101f4000030592001011017240204203030542030b01d56002504d000b400c1070360004800915000c1074001c1c14000d003045030040c0b01031400c488c80e501e8002c203c130700c50850f003102d025421401400182c2d034114040c422502031b89030003003c180d240d2000464040d4a12070314810080c00160001020360103801905055004081030003505d401c502001810f10010140100700700c0303640e04176200c0c604e030244606d80c100070b1076422a401e4001c00311400b440d01401140c10341d41d0500c1a010041000a540607941e4050402c1c1c5564103800c0c1d514035040d00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 875192356 1250 875191106 875191123
    0x10b150903010510061b03020106080118120c05030f0d020d0207061506031a0909010f150f050105072303040b0301030c0f050d0203060103030e010525210f1407200405090f 75
    0x6c4118080c07811106141c402d4000d0000342084a00801808e12840c1c0d542c000f0381690a001c403020302c240711600c0384175800b60000c1c8030320907000030107180b030140c0c10581c015403a4888a50b4140c0140e00b40644020301c00944003400b56540715490014510b880c15201407900515036004908041c2000b003c07079107000c2c004842c0c002624080e0b8444109450703501e4071a01401c4000381090410307103003940c175240514205100c0021a0404140c40d844152034400440c1c40d4400c2c010046c0c0903c03048103c1034907040700020b000f04450310361002c0d00d0034580c88040d0b5001950081c0d02c02ea071100c4030004180010114482c5e204000d00c0102c800d0307014040c1c240c1c0402c0c1c8a101c1481302030305101301c00300780c0b40c13459002d40203c0d040f0840b41e44040d07055541850706d20700c2100c02c40500351807000000c05074500001d612040f18205400c80d03100c20600c00c01c1924100e60b10080307615039500c006001d1040c0710004962100210f101e40781c40e1098044d6006140512040301c01c0144106065032081c00c4601c4035200200d070141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 875193606 1250 875192356 875192387
    0x80604210c1a1005013204030b040507090b0a08100f060f0b041a0901170606040f080d1106070e0402090402040f0b0310091b050c010b15090301051006 66
    0x10040c0201140c20746500401c218080c1c41041240600c1890030081400070b8400d10388044006041c0d510741d0011502d20703c804c40b00040200700003c44074040303075240302d002c2c0b402c400c281c0c5181d1410303480365a0305548440c29602122140d1151005100142c40e5000b01c0801c003809070f584150280c41c00c290303280d40b04100641c42c264580d4a00c18051406e40c1e40e000b100141c012942013130b0b0355139a200c4510000394001c1c481c00341e00c1c94403004c0d48061445584100c0e58441016074880c0c0514102411040c840b49000e0311440d0b100c00304100c005662010682c3c0000140075190140030192030028000e407440c0c0c502c50b43d442158005604100d516600002c5052128805030340050300d4079035480102d4024071981d040958100c900c0103000507074039003600040d403103610602042044180e0b62152181500c588140c4240c01c1b04542d2003c0600510440c050091b0b001280c5c00800c01481e8403020442c80400f503003803242100800222a5414142401a1a007085205000500082c60004010300f103001116142 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 875194856 1250 875193606 875193653
    0x1080307030915022b021e1f150603091202070803030c090105070b10180203091c1707050a02070b090319020a0905150a06020307020117070c050307120801080604 71
    0x100c440602c02c00c13000107801c1702c08a540c00c005503183d00c500144151110410010310039842e14135070340101009555608007610005020283c3c2c10b000da00003119003c4e04d0303455130755076800c05c100307210035090030030401003490f51000555007030320b07042ca6030036101c0e0f4002080c01c0d94010642004800c00020407070303512824203170316a5150744d01031004070340354400c0b00030151044c850b0fa0184001c0e44d02c402c000700c04030b0b0805000710340d040401c14a1700c400c0c2d000484600b00c2d0b640046c94032518503442c040d0205001000ca140c821076030759201c0d10346524040251070743d000050f00881c0611200d501080000d014125185006040a60071000640c0d2284a01510045010780381c041004548850007440054100100e051080b8541102c0312a000c903000010603118805051000404c9400482140e02c1c0c0364040e915078100a03504034800c54030760f00180c0300b01d041010752034003500410014805003840620950000440c0c009140c0b000301a444180c000c1c0110b5000f21090100042060500110000b40d04800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 875196106 1250 875194856 875194889
    0xc05252c0601261519140a03080408010b030607090608160c020915040522150e070b09040f0506181819060605090f16050405040501030f0b010b0412170c0f06090105010803070309 78
    0x803403801711043d0301c000c10049c1b01140104002606410201d03041509a080301d80d01e654000701213805601e40d106201c0030a45080109090002d8085011070400042c1840600d12032503a011500700c1604035900c1c44050211000d1004c0e078503041c0589900310900340282c50103002500c06007100340860700c00003428a08064140c1482241c140c100018206030101901d4100c3d550b0802c0c030019038480102c1070310071440c1485850f1848a40d22515000e4507020b4114518080782c0d500c007400a10004c1c1490211010b2000900c4616404001d0156510208581c120b10f14180c1e01d8200140d0f6920740185105034101001c00c0120403408807100d5116141e11540d0798011000402070304c07603208070740010390420304101c00401400714142003c48550310503407031400641c1e03a0710b056203000d008a0250801c2c05060341c0d2144042180c0f480d4481400c48082700540c6400c110700c4000c1d00d4110012030006d4035810140c00c210318a0800c0c0719076801404040059441c100351581c004040d8a00c41c0603c04440721001c05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 875197356 1250 875196106 875196109
    0xc0608160806130606020d0215241201020a0203181e210a0f02090703060b0a05092701050a1a190c05252c060126151914 53
    0x4032000c440f42044100160358032004000e4a81d075000040c1030151245a039503594403400340160500c82c0d4003030001203084008152010070708924402c1855880503c5007d04c2451460a00c01488003585580041d0764403849100500000914000e415110390200101c17050002c08900310020642000c4801105641889990411321002c400501b07080d8400c0e1809130041141c00580116003500807100d0210565407000214240c038010300401c0041801402419034483c05034029040300100140719411014580031116246c8941c01619012071400380010480783c01e100000b90081d010141c04c1c902c00980f103031211021881001d014400049180c0c4007001214480c513150100103a2101c00c3c1c5003800121444054041c400400030050003011002c0020151200c07000d02c400c03100285606200340c60700c0780a020001c0740040400d414441d850000303848480b5105010184040d000070310180030b003400300002d0f08121a109906015402460740105410050401201203c040303084ea4040401c8400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 875198606 1250 875197356 875197369
    0x201020c0a0335040b0603030307320c010204050a05010813030c020a03050607031406010f0206010b0703021c020d020c0402031e0604020f0a0306170a1208060a0b070f0c0608160806 79
    0x44a898800c0b242a01081007010390f4400300d40a2809590300c040c00ba00ca0b1070030143c4a1005580403804508490300c142900841c080f882d6003c241d800404901c14000425950295031001d02e0098070ba1f5030000e03090110b4900015282c1c0503000078078002e10385181502c4400c00d101c840020250a02050035401c038115600c041c8801d003e540d010003a42c00328140900c0c041c01030608008414000c0f4403540025045500ca0007000c1a00301c000e5004000f40e92074140c10100ca54043c407400e030114013a0201101280e080005141c5015441e07034010480f50942d100001d05007032980544a204600403c18890108100360040042d0cc04441041c1a16160000054020b105058008442102c08a0700c224400e4141d44400100ca01c1031a8098080c9071000003551203004d84030000b04101c41c1d146150851710b02c0349402035441752000d05054403080e21040704200b80e0300b02d01c00c1140c80d0702542a900c0304101d0250703803910081980b0b045c003000c4c500740450f1104036901008023900411500b0030004142d5502e29 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 875199856 1250 875198606 875198657
    0xa0c1d010e0411040905010f141303080c220612061208090a080105010b070203011a01020a0b070309170c0f0105040c060c1703040c080d022a060702130605010e010201020c0a03 77
    0x9004005d5040145081c5000c8c1c044080c440c0300007031502000310042ca240e020b55600c2203c00d01c40a44a040c290703a01510007200240c040c07519004284040d92800b501800c02411124100d07402c8415945003940042c042ca4200981a00550511800300120410202040245a48074180c02d03180d0052102042c8465074a62000d6010340c281000054200340c6e0300c0003003200034000d40003804419242605509900a0340a0040c016440b0354250001f107000c5041080d0004081c2c40d02040394003ca48070381c070031040010003881c20300000151079075030410104400c00b00e141560000b44580d250603203070356044103030501c500d07000e108800101c003003006003803103420402e0316962010b540c490615003441d0301240c010340100c036141e10500d10042039180c000200302c8c6220b680b46118501280f589500310010b41410b9800310340114003480b1a0300140e503500003000107020342500024a0900e044001428520346041481c1564410041c0c010b001c1800b0074078400540e054280100d0001c0e40a1010f00300c240d16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 875201106 1250 875199856 875199859
    0x100e040e010c03021b030c0c0607080c010c020d12090312020f0d020409140132010c140607080c0f0f1608041508061503150310060303020a0c1d010e0411 67
    0x2c11844000c100c0c1c05502404800d204e00710b41148000d0104030482da03d214001d600c8010f0b0740003402501403440c01000801c100d0384500c00c0343d41419000381c442ca080d1030007001e140b03016070008106000c00302d40c0820311440f00000510203106064581e10003030030f40748180381ca5682143e00000e464131800071300030403214040303030012085549582d0390b803101c00200542d03240c0b411000c000d000002152220030341e20450780e62201c00380d0300c801d0700c031003403510010107504220606000350710843c0300c040340d02c903002d480441501e600548003901d0700c03036070003081e012005100000c0380400380040e43c002030904090b0751400750170380881566075030f52801000300c1e0240c08030010025400002c01160b80041c82e200c110f103544060300c0b03c0803642c881904200b5024110000444222418400200400d1003130786464008403001c1c09036a181000c0300317209415a125900300b90701503807218144070200704103c401403000b0120403181c40b030b80000e040485a00380c0c1040c03040307000152950000c94144110a040014101e10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 875202356 1250 875201106 875201111
    0x308060d0c080a210e0a0b130b0f341104110f041404050103021507020f1509010e040b011b030504081c0f020c0306070c15090305120c09100e040e01 65
    0x143ca2a05007048200f14124050324046045800c4116020311505000340314000d100381c1c00c65042140144013030300522412a100c21089400003000034000c00105844000c0e8280907aa031860411000301c0c0b40c02d0340810003c03d02408160030b42d8001e449202c030b1002540112031120070b40b00d1a0004028104555070081034840000f40c2d0121149600010401c031a0a40b0000070b0410031001000210b410904c00030390845001a01c8810044a0034001d240703c510040c100c921054007c40865580388060b10548032084000800d0019503800c14060f0b2410383d0103c0d014050a044640000c0c031000c42c108034600c103000384468010130140148240c0b0007402c600000c555184452140845041035032070b02410100c0c241107449110309102050000c0c441030b000e0000c1c038554440300012582e12030700100c01d403040c00000140401d007807454066802d00d24020b640d440e44601a4510b001562580a824042c3c4080b00700f00710852501c84100c000c01100c00c905040300b01510b24008180540310001c4501072551 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 875203606 1250 875202356 875202373
    0xb030702010902010f030506181e0c09040f06230a0b030703050708011217090312040e04060c0c11130e0328030c05040e15060408150f01030308060d0c08 67
    0x140c0c154020b40005000b607841140c540d4054500364102d8030b0a80303503160006151400e40000c0403500b82d41580144100904850112114a910752181b00964207203925100010355100c82d850a030040400849640c541004400d16000c1112000f01c103258190800c88212031725600f2550b07500c40368400801c4483e180641d60307d80304c1320050080904a4003100445e5120b000801c0e804000300f403101005600103117045041e00002160072154100e042029418804c00390380e40c5407155000702900080199001c0342030030b800c0c18504902942c1403103170b0034001c0040c031403400d102240e00f03103410400c0500306a50340c0003400f00180c8030340c0103040141c4000301c0b980710001e01b4003c84400c44440c0c100590400d01c095140200240c030890039144004501d20006806000074800301c91070104540d0008020704030a103035400b690340481e18540080e80079400700d070000004a80b070406a1a010795000441809501d803560440da80605400700140410f07024400310045141000340741051300014084800443c8d6070704 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 875204856 1250 875203606 875203621
    0x20d060204090c0302030402010c030804170403060204030c062604080904050103150608010c05091207120b09060c040609090542090402030607080c2104110f090a0e070b03 75
    0x207600c1441400348041c42c08a200440c14828420340703001d140d05079520104010583c4040301c03005030141099490040c6000029040822038001304025442a140036032103901c1c5060100e88030505902140070b00c8103110340c2c0800801421920710201e003444600d0b601c44e0b1602d041000090042503d9a07410528150001c400d03c101c4d807144902810f17200c503003842003681704e01140342038031502040d10010490074010035a15140101e0b030600500d02c220111800566104d000c4800344001090540b20080200240542948184141c6a000c8008a4601d142516080b0020301c0d201441c410101da2941d1a000300382c402031702001c0300016212014240008508400f407914111885140380320036a404045000c03c00d06160450030b2056030001d0240555681e0700c0c00035202c210008000081c142c9080150803602801140361001e000c602c0c030300000f0710340760618101001e030b0500e0014510502c60003105050540d40c510600f680401200c402084441c000840b030782c50080540c203c14240d510100801560 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 875206106 1250 875204856 875204861
    0x601050102030a050d111c0f0b0f0d29060108100b0414011e2a0b0f040213090b0103110301050906150f06070809190810020f040e0910050106031103010302130207020d06 74
    0x1540747d02c0b40100071301c2c041000002e00719483c000d4299004018114065624901005060700d003500803400040c00020450041c0200f01200d058540c1800c050300c14011596845550380d42e0040daa0101c0b07200c01400d189000700030740200d2181140307041010740c0c8580603034403d0955240d8240e4259070000c06403680b640160035440064901c06900001d03030105c04e070111503a44503115107600180d0310b10035500c13508040003100900400590b000840d0803011700c20400e4520544c1c01e440d02881d074010a80d41540b0702035020310001e042c0c040c4a0782c14202444500034000c5030440d008001d40c4044c040002a442c081800a1030240c031301a802900440e041c024400380d0001002c42010443d400b580d84c8070010703100114026107000d0341b00780c0c0d03200c1d070070701c40d000101c5038000c0000002c00c10440e4101550b4000c1140401c0003141c4003000c680064000503403e00b07143c004c007405400f250500340010902c10b01e041c02d8500051102a100b102e03640e180c26200b1105a04481007150003510000b955415130811001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 875207356 1250 875206106 875206147
    0x6180702150907030224161b170c010f0e060c10060909030c06020d020405060a030e1b100e300706080103080301051e0307060c140601050102030a050d11 67
    0x41100c0701400582e40403004a02e20b010341c0e6009040d0761003101d07204000303c0700900007010356030075100400c41d4100c400150245682158400e0f0085010a16000120340f20840b29a10900c01480108001640306401003111314090b5400c1c0380c038941d00000d42900301c0b0318404840050350170040010305078112450116580b42103010501c2c080c002580d69140d680700311041e0090140014029808143c0080c0460b002481c100c0440d0f072001d810a9221000030328154009017600e00400c2e074039005d201c0c9600d028400c044a035060828240d880b80e070b144c4040345030b448141c0700d0340c002c215001c004c9a0f0a03a8507007079219070403440d10036400c04004007150884144d0083d100108120300c02c4800020300703144220495030590340d211180303d085034a400c05102c8031010b51150a9107a0080c901500d8881e2420071007000140704940d0b031104d4422841c02d0a2050302080d01160680b070304000014006660004200c0e03d900000d803038120b9565045900310001403c1d0b407588010b240200184a080304e9010031940403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 875208606 1250 875207356 875207383
    0x2004060f1805101520160803070203030f0c010e072c010302100c0812040302010e07080d090b0705010209030115181119020a0606031209084c0204150c051506180702 72
    0x9105a071907c185d1036a0340203820f0000c0d4036074420032851908a9400c805002010000340001c1000215010f41a04000158210781c3c412013070500c2c0c0e6040036080d10382c07589001e6030003424a6074a50454012a003c440c100d031840c070510402504100822117510201d942000c24519000405d04251800a01070580c0300010f48440c450034901143c81d92000c18101c841042c2c0ba11807180c958904410b0308101c5d0840b0f01e003a65255428028008943c03020300582410000000c0001a4141000d580301c80451090309041802d40c50080b965030071038842800c0b1303220456170049194001c6480c5904a02c0e11305d004000a104a040680000401114211540304172059842d02c68080340c41e16501030f070329008103862125888030284203140d030081c0c1f90003010007241c0a00d044900303200c0a5150b0b0403034110315003c00032010b60000f001c016611045501e01d0060b940c61404101907610f40e15120f5450445541c40781319280340c00080743c01d90b0745400d1801001d001030010707540300b4a001c03040070b074403a42c0c6c04001c0f8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 875209856 1250 875208606 875208643
    0x11040b01122408150a2a080702070906030f0f08131203080c0a0206040f0c21050c06042603160623060a032004060f1805101520 56
    0x4926402c0118000011041d420003a00040c2d95050801c40a0311b080c0d00604684984460018150301040301c5480000c0b666458007019810144402442c0007e10b9100a03800d0745400800e00c0014800006480d40c103400c0b40683c00340f21a039040480d25846080c0301e01003000720481d40054000001004101c0e52406030f11407425a40d00c0f0300d42900c041c800c010b0800d0043e00b00000180014915944e0b0801150280d40c0b03c10a0584036940250550301c0700420784540243e4000d4041000410004001c0b0280c00369001ca040038034101c441004003907407103000088038000c46200d050318203040099a0300c2d4410441c16541e03202850500000401c0010010b581681c0b410184107031848941450394002c5601600344403455285845045400700b0101d2044072082c5515106005603403940a11005404a10003c208107443e028110030a102200141070343c450030513041001c80000d041107070044400380008072010104078041118200c1d0000c68904110a0f4034041d107c3c445030008240c05480442d02c4075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 875211106 1250 875209856 875209859
    0x1215040e1b0d0f031b140a0b09120a05030a0e100501051906090501030c020a060c05121501080103020418120806031b1e011e0f12020711040b011224 65
    0x42c03004a0180315409007001c24640070038000a03106032007840d043e0852641e00313124080280d880c8007290b0352200284105501045e4502d0a01003403040c030540001c030460040108c480907808040d014040d00b80e5400510502100180c00c0442a80201101c080c1c204161307072250b0b02d500036440003007500707002d4240150300e0354103d05014022580c4000c10351b040344e1921540030f442d24004401606140c40c1560843c000d010350400014640c2c0103074501d10b003254507001e4540015103208003075410000d240c10341072400c402580f000c40e40c12500c4a415684c040e034000c41c5a5902c64202c00294980402c02001580b803250351380d03030312540801268041c1e4030403420350f2426a1001160102d019002c2a09940314a00100749006601801c07100207040d0018140041c54040204810400d0203c100c03011000c20700c86800000701f1070344090600540141a001141840c0395a220a4040b03161200100d000300c0d0b80d070013950b5148e80581c070410100c000444040c480e11031902e40c0d01c401070322814004101203070360740c0c0f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 875212356 1250 875211106 875211109
    0x915060306020d050127050703060e0a270f152a2717150c0a03140114090702190503120a020430060e030306030c10051215040e1b 57
    0x10f8001c6c410b044410510302d41c4d529283c2802084058070030000d042d138a03100002d1264003090f505110307140701640060308045048010144260100d0a01944440000e112000034802c84001044e1034100301c2040d01b810044a2005c02064002003441e1821003070100000c091680f1082c11013000d2a0780d58100282d0140000300b520803071b00000d580030a01c0001c1c02405101c079940b0401c00c010222004560444040200c044400f04003600d2446805100043c01800c1d66094003c1c41b02c40000e0352604001c5600d4041004080302601a036180b1585031b180c040381e82103100300080666504d003800b0342801c0c120a407514664940c80007a207000300c00482800078989480d030303209680407103052500d074020500d60040408c450850307007040c00000184074101c40020801601c1000e00d03103000c0400959070780c1410307000c041c5041314000a00348992200c1c51401080d90303000d03048d00c448a06041e4020959110907000a900080102032250002e242c1382d400e410000e0b0003e58881c466040b44a8040c8071100e550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 875213606 1250 875212356 875212379
    0xf0204090605090f0313180209040c0507170405011b0f050d120e0102160f03050d02030f240303160c0305030a0216151d031005040501020a02010b01021605040915060306020d0501 78
    0x1440c400096030a81c2c20801c15100303c94104109401e00d60042c80c0a2703150000800b2500d40c86800c01c0040d101107120800c00000e0028400c0c00c2035030b4001d003070030185000700007004170746815260061402d9480001040001c2f00b40100881d0740e01500f0754000303d03200e070030081c01e00c4010000801800c3c10240382c014030060610841e100d01a00030307807001001c080d64035050f081600c1e00004800300300c0200045d400c004001e10103180600080c901400303482c00d159001307061440301500d00404480c0d03900001c03800d0399000401c6584003070b511404600080924181a5498842640080c203540400241c200805030301151000600d032180b04920b107215100c000c02e07441400c40b1105803021403190703055102007521501a003284c0c15402402c0300d40c40360602030440251402a01c040351a41e4002c2141d004840c0c0a002c2d03c055140c0c203100a04c581e50340d1000014a424980c03144074001c2c0e0756070b1050001d100415150818036172409106000c0c403650ba240100003940240c0c41101c14a01e01000480c00c460340d035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 875214856 1250 875213606 875213617
    0x61d0d05070302060a052106040f021206040f0609020d02030703051b03061306171c17010302090a062303010b011e0f23090405010f0308160f0204090605090f03 70
    0x2200a2070240d00b19030901001e07a110202c00018000140401604581d400641d20052110090b02410500701107040c80140d0303005032144c0c1c0740b903130051200d03401c12003154000a601000c120382c003142100210b6281001080550807403400d0310b00024440c12104440e0300114010101550208401d075500714150b2a00380c002407580b001c2c40810000301c1e100340b60100320340b040c2503042d140000b40e0030780d144261600c864004c0d0300034800d0b401451002015441030020714070410001e00b0400001850181e905880003014000207200300b0130071021410740c681ea5030129014140340b680b4240c0100007048070481d20001708034460f210350300741204c4841c07952113140c0c0d000f8030018440c0c46c10003492540005544058007030307445100f000301743e4021b00c1c03036403c0311000d405001800403038031135403803040e181880300742c1d00140c000340c1c0c418014010810024107848201d0300d500316031307404c1820780200602c1d0002c01c021048402951080c1072098034414444154001405601c062084a100c070410689080e200d0241 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 875216106 1250 875214856 875214863
    0xc012f0304021305040206041520010e1e0309190e06010e0d02060c0a05031b010e0c0d171e0405120604150c0203130b120108030412200a061d0d 63
    0x7070343c140c0301034081030750896600548001c146504040e203a0305c1122401c480781691400003004d1702e01803402840013507415807680a900000b4441d490100c0e01c083e640d2404d40300546988804800c80400c0c4040074030503100b08800060540a50350074407000c00030700e64000c0c015004030280301804541d00398080c82a410003098050840101600a502086100d41194180ca05103010780030310400010400d200800c031070001c104800380240010840c03242100c202c55090041507000e42c02d14001940ca040309206207513440494103001035800c6015071114011510302d2810041c4c440ca080340c180c0007060180081d00c00c162200c444108544850759034030300c0c0070340c0c1c0503000e0b40d01c40c40351150846440c1c0189450f00c0303a600440f4640044160426003081081d441001001d0b0086281c0c0030407040d880340c0500400240c801141010709001d030043d001400101d000b0b00c55164031080c0403110100400e400c0807010300401000c00f155644030003820703030480c684000342103280301102410185000c5401c000d8080c0c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 875217356 1250 875216106 875216119
    0x5040c0608060d0609080c0f0f1015080a060b1512190e030310060306061103030f190e010605010306060507050c060c0c1f0e06070b0a0f020c012f030402 67
    0x1a000c0155119032000d818550080301e411100008207035140517849003240305403055541d4020340e0683c0d5041c42e00a0002e0a96500014800d40341ca180005004065880750700300000c0151241002d0340c0864165031020b442d500601c0a0340d0240440d5510103100c040050746c41154030541d001c0040c410348140003022500050180105202c01200305e03004040070764140307000480406034080a03265410840d5606200d144400d0107100d05c0740d05020303050041ca910b01f005c204010140821686a000007024a4001400c200000d000924000c140c00b801e000d0a810030041007226901240c041d21846c024140800e041a20004006110b0400c540d140d0340c0103000b4113065005130f810403030b440d03110503c41c0040b4410041034260540d10402441d60071b40e11980120148000404050580c0c4510554944529418003070700022a00344500b107584400303440e90000e021042c41014500074002d10400c0e403072961900000c0214060303c11a80303440d01900284449180e81940c1840105102c101d400075000300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 875218606 1250 875217356 875217359
    0xa142409150f1303030f06181107030c060b030a1208070f0509010c030503060a0506030916050103150905250525030c080a03020412061b081b0a02070e01060e031005040c 74
    0xa070f4444080e10b402e2103460007080f50415942c911068800070b40210640d100e5016203070241e1007981c0304082c41c1000c0342c180c460415003187c41c0603001e182c2182019214540b03070101005542c0e4244024085607a0041c080018001440c82c020007074002140c200010411141c1c2c00b0320380a004100b90780204a05959035508421680d50403501508050b1495400030340ca8500400d0700d0b658640950f1140e81740344000c25108a06481c00d260b418525480203040c9883c01c00cbd011016015442017200340c0c0c210220200b00358075196410801460b00204400c0254120900849141d03801401002c4041a0042601009144005000c0703048203202000740480d01d2130600d000000d0303486000e00840c0b03869050060401d0f6a860300016421a402011103155035141105030200c942840064800c1a041ca410b01c2c50745004000440c48102c080c05580c00c50402081c030402d040d00c00c00598001d40407210032030070556035a46018110030310300d2900d5842406032a040720480c05540c8100341c81241c100e0700e41a00d05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 875219856 1250 875218606 875218621
    0xe010b012d02030d050c130e06090105060f07020d1b1a030411030327010306060813060509120720031b2b0c170a03020a142409150f 58
    0x2a25074880346003980000d1146002d148400d115a520070080d600303400717550b51f042201d88820344019802480b10001f00e0018080b80c2e0321a80303c0641507603410740f10300e55a0f41a280da8901140a5000c009500040486100e020844543e840c2c595011010f03202c500c0c2d0035102c10030b00080e107804070003a0b4140c0f43d0030710019000c14424058040204d20150640b03252031901c175400034003a06009a6071821014010240001d544c0c9481100010115442c100f0114100034003c510403840046c0d0203407803140c0b035402190b0070000030b02401060004d050b42e40c550701d456524200c1192003040c480c907034883d2840c48185c40281804560744680045080000c00303665104403c102015181510f0311007220807091000903140000702c00c440d0007601400b0106503e034500301c996070010003040032101050700004038400000e41c0000701c480c903999001c5280d0111100c0840300920b002d04a13180d00c2d00391085d00950380142e4511550250140518005464038064600002a0502400e84020020507501000101c1c3c8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 875221106 1250 875219856 875219927
    0xa05070206071e060c0207091b0c020a09021c0f0504020306041b0302090a2025060906050f0f060913080901120501091a030d05030403110a020a090e010b01 68
    0x11584502411410482c02041ca070705804068141100d0241c0e5401c0d05c01c2c040c0b07804014600040481250610800d510422407001502e40784503134405021110354a04215515601758001510381550300315141d24203030543c07441c002c8803220499003481c940256044220001d01560f841190050000c12054840361741d161844682c100590ba91018402c001000690351a01c00301d00504a400c0d0105489001d80f480d881c995801403480080e041c03081114136680b840e81c4450410744030b09a904800702071824144417002d40200003005080b50301d4101041885000e05540c24080d8001000c074201d1581c90809128180205440d00741b1031800946000e000179048400620b282070041c50720441d0020080720100c1910710a0704100403040d00c41c010b09000140c080401d52994100702d00070301450039000303406049880058400b40400c4001c0d01c2032030740c0c100200b2052502c15400b40002441c20780e6100b00e8001088102e40340c0c1007650800c100b4816070762240110b1451485a100346003032075000c0c8481c0030322 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 875222356 1250 875221106 875221117
    0x3060904020603070c0206030f06030c10140d18080307020d090b0724060f06020f01060e06040e12071a011509090e010e16030b01210807080904050414120a05070206 72
    0x1082001761240c0d0068aa45000e0343c0114051060030100307080c400304040c10b040c071402e03416001d0301e00360031080c50301a4020480651101c1d010b0400d69a805915000c034041c0c10003007901d05847c501c01c440801085600c50085100325980d609031201c003a242803040b0b4480180d44524040e01b2024888100402d030000e15047c0043c1090f070b14602801815014030050350950760151081d0540d01604020454040c00104070703050b640002000414144082d070f00b08241c0c042d00d414003d5640d001d01e070300c10741c41c1080301a45444034034101e90b03103a004602d0b10a440b00c00200260441c0c00d022000002e44960a0b83d2000194002d9140c1c1c1500358203040c80000201200d8101004035901e42c0c0c88110304c840180700000010f102412615080740c1541024410b42e607043c0d024080401e0034001c3c0c81d04405001c17040040a6600c80070700e550326107160410300264094801196400340c5000c045c0010482005c0840b011500488142c43e10345200c028212078074010a8842e80105104220b054018a0240000c0a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 875223606 1250 875222356 875222371
    0xf0b07080f1228180609020a08030316021018022404060509040e0d0f051608040e0a0b030303100b0d0f0204180f1a1e030d0c06060b03060904020603 65
    0x10309001000c052510301020641e071810040f0848450511648a02c1c444000c1e10b107010f583c14003070b180c40c0c01d0111400d04071501d00680801d5480e01c02004554481c541d40000307280202c101c07501c03420059110f4400c0c0f282c24541401511039800d0036064508180118410102d082e039103001c0b10b180790303000c2c004141466907061600280e0b0043c0411342010f248098406003c00756501c945861103c0b044c0701c01c842e50300555002c0780e80807903110700f0402d070b000707810314a5120303186091604e416400080301588104820018902ca60101d800f00d944250660207520400c1a40410701000c40c0140505440e84400e6580754420303980001c1c18880003000000800300e1200480b0006400c0a06038288401c03a08207411900c17800d01c0500b9200b01d40301c2a0b0103854004a040c41c420080700617544110b29500f130800318010f002d00383c1078580c40c0c06007529907910192090060f0a07102101c0e031081c0c00401500305550200d80781e515001c0c01003410800d200079203101e4600500100d07502e8031281c0030030140d80c00081020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 875224856 1250 875223606 875223637
    0x10903080a03020705070b0702100507061103010306050633070f0506040302031e041d06010c0b2a0f03070c0c15050936090f120706060f0b0708 63
    0x1001038200c00041480301000c0d580143c03200d185140180c100f4901d035003d07452030f19052100e0b402598a17003500c0709000c1d001d8100255600d42d90326082c000740000e144003261404010000100b8081030343c2084d48581d400311104010512806030001f20380140384c2140704555681204481c107240780074000d115880c000c5031300e80c040405a81d2100c0c036140040320304a0040c0c101043c003500c090340c004043e1440c0300d41c84011509181c10b2100000d1080940b0412001400c1ca0201068451740900760304605560800d1040010389820000f010711a610640000c40c01c88080a9032080300c0d00308010750b440c06004e1584180340d40c83d03850048680030403420064403011251000015019400f10502e00380456945a080d25080f07000f08101084054850017000c0a4040300100740301502d03034200c5440032101d00800419601c4c2c0988952500408031903041032841021001d101050704e00014251081c0f0a44081c00380c1d54841d41c50000c0941a4400d842d000b8205002e201c00049220703020301400d0f00c0f0480345 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 875226106 1250 875224856 875224859
    0x121703070f26100906240302070201031413050c040b090606031b180a050909060f15130e100603080d091e0f0201110102043609140601050d0309030305090109 69
    0x196052030030b03100fa042c43c0005038010810b10070140038103402010002c0b01e031140405003100a200e83d14141c0031080c105940090094216806540705c031140c40c44200b84034405142218040d6404c1000503800e0f04e0754401c0c80e40315015403820b03000744080c81c00003412540b82a2500b0382800b54607040a80710080c80e803107501c1c00100401c5001d01504101d008400c48041000060781440304102e80350300598000c5230054100901c0100c0018820b400500e500c0c045405aa035244540c80c086c00c0c01e0b06455841103000011310500e40b0141c00800c50300e0089030079220407030703000c40e5140c017120740520000381300f41028001900b002c6000d50050100c14000c1c00d00c110300d408200c502c5c03403d520920404455a40c3c498910320195644030160380c0030040d02000841c03a09040880c424039240c403c3c88d2941884c400102000030340f0490b0396001a40142d032000030300840717101d407030f040c80301d8112141d6003000c52064000010302c524028600810b015015200c00c00d41d2400d5490455040d40030030721007070611040c00350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 875227356 1250 875226106 875226167
    0x25031425151b120603390f1a03070801030201110a05013e090f040905010515030d02031603030513020909060a06060c080a080619121703070f 62
    0x11260460b602100d000c2c0004100240076129240c0b600d030038100f8a24045044c0000b800c6119102040000d0304e090000c4c44002d41c1091039190f80c03c41040700039000c90080000c217103480d01c1c1d03600261007140304a08001c2c403080c20202c2c0907000842d1610001002140108050f5004115541103170380c904080e102c1484498540c982560300006540030b5200208901c01090070580d041502c000012084c9d100d1104000750000782c042c065140394921902142d282000c856440e9404210400d50081c024445c46c40d008000f402d5422980f84214080e0040e40101503480e40302200301c5040740400c124556511089440807002442e0092040c1000f000a16004000d42e0341c602d00c0070700c90300c035001c000c007124070781428003000740c61490340200e06201d010380441c2d0001d0f820700e040d40c01c496501e243c512490b035103010004415440c40d140c030003102c0051020100300180a05845842c890094103010b100c4008000f0b0301c1c2c0e49210485480c0c002031904140ca4940c00c1c414413400b07620340c01c0c645041401104801c07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 875228606 1250 875227356 875227361
    0x50a090902190e040902030727050118060e0106050d02160506180f0a020102030909100f06120c0f170402040f020a050310050a03021809032503142515 66
    0x3041d1100b94035806981c0410254481100120802c06407402c0c404c81c01c0940c0030035a1395205004842a90603940498007040044d0110300c00c208042c1042400996925811401419100504403a42509010000c52807040c0303014824101c4015603140e1346401903c6100400075003010b4103220301d10500d0624203010480820146018211020302a22030300b450303090f51450240100c200459a8110106030800760b80c0120507148a18001d8a618460b507a9003061221101e0903a0007481501170306440209041e6442000490700714100c0b8420002610780c1c42b0142c82c8404a4440c55000a20000c452041404004e100c1387e04544040c2c008500c40702c2c2a08403a041e2303002000306000040740801001030449100c0e000d2001003409a505010140c1541c0124060424034440000300030004004103608441c00c004482000ca01401c2c008042c1d80b2900d55010060300404c016000140300402d00306c0d0440040048490452551941c21103604c0d06002084415941c807200351a0710000380c2003902c4028050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 875229856 1250 875228606 875228617
    0x1605070611030a0501080d09030f060b0409293102041e05010509060d12090f0b03041a01060504090b1801030501090326061c1b06020f030c03040303050a090902 70
    0xc908688a1074a040c0090495405a000507142d03842007c20317480c580c6d00a034084081e00e800c1250034000c18010b08001001d80629182075030041e2905441805014a038241e111b80d4498030954501850b04d03210030400780c0d10b0b00781e40c030b8a81c41c00044020420605d100c1c00300260041e1981d0481e0042c0386940006d81203540e800b84d410388051010f4030081090301103201c0e0380d000d40000c4501031024103018004c280c940780416030040001500da841060582e002d101c0c4c01000308a0070703070342ca94965201c01540382c00390002d440844034403542010358034007020307812603982c165841c1e60f0360b41d410685801141c01c09004084502034101144101d0202040201200c450107140580d0010907a00b5951030700424084500750310040402d00c0885101c00c0c40c00104007150020000c942c1940000790240301c202c02104000002481da0400803031302901d20f04260700ea0310031501250281c0d0101849040075588a10600b8003541031900700700800d0000070700078405408540780500e0300e01601511140c400040f40d028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 875231106 1250 875229856 875229881
    0xd09051f0215280e030a111002030c090a06082a1b0a11030303070801030f031e030e07060203090d08030702030c07030804090c05040e04061d102703020616050706 71
    0x200d0180c10010301d186500d0840d141083d2400c0084030f00300340c4055182e00a09191500b0000702c04030603400b104040241c0022140a110708540d03d090070022103071035a00c03081c1400d0140d01218800a800b60180a02a10850012140c10307507414000c690351403030b07023000c40c40c500f6001e0040c88408144d0880d5140c80801070403036030003400344441d036090201e6500c0301e912006100b030f4010401c01c02c080d0303403160900341103a82c00b00349030500f14000c2c074007600c04c1c0c0913020b04001300e40900005007150320f500d900401481030008056801700d035200d004c100d03142d115204000e070b00300c90200408400a201340e00195408541c0d407061300d0410b08208420360411019602c103a4900d9030118060102c0f503031038840c810f4009040d0410525051620201c0050100001d00150559551300c070360140400103401c4000300d443c480c2098441308031410b28210004d0a40e04290040c0c13254807000400641030300300c184680d064154004060729134643c0d80020200030051001d60400c40d0500c01103000408900900101855 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 875232356 1250 875231106 875231131
    0x90402130c08102106020c010207080304080712021c0809152a13060c06110c031e0304030801170a050312190b061c06080f0307050d09051f0215 63
    0x1c000d103402c40b100b03c1982111095100c00d0004903680145030810380c00203540008090f89400d441c440030b5009000c1c0540242003110000100405c108180005100300c5100e440c40340c1d101452800100d03078480c01400300100481408521a003854000d5081680c0400c001c012501004550440303a210030f2020340b581e0140034000c800c0c1c00b0340c103094401ca07450710141c05420340d42480e01c185071070b20101c0120712415051040055410041c071880ba000481011024a03030950760b43c0c08902400d94a90055034280e0490480420a40342072540700d04481c003480e01a926041581d081c00b0401143c51301a00451507103200f20210803000806c24006800500240340100301c0d64a062060101051070301d804c1e10f11308501e400c2600036565115020744001000c00c0d450203003001c480d0301c0904010300840d04042181d104211180e0b095100c000020200d6600c40e00995002c80c40250003501c5c80c1180380205039002e40300224140c80c01b1130242400e08545018411100701c003541301600e524402e0180d4554a160b503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 875233606 1250 875232356 875232361
    0x130b03031611030615010f0503070e041b02010e0601050d0b060120010b04050609060d03050a1110020d0621032a0f020316030c0504090507030c0b180d11090402130c08 73
    0x14081c00110b6000020060515200c4121700008140c0d031000814041807000200105490034400c85040740001e0015208200342054010816040340c9215102001903003010b280071008540450310b40c0c1281e401030214020303007401c1e55498804074001040c89042001d141d58074560000041030016411036603a0000844401d444c040c4010b440000740407031f000ba900201400003545420241806075505807030015112141e031031048070401106680c00466200e050800c0029040035402018000c0360300340108401c0e82d40d00c600803200c0d001c5a282410b081444c100b0315000c20700480324040070845240c800f56600c0451090003440c608a440d00383c400300d440107030b21400c40c14100080c1200340515400402c01501e10340d21409042c00c0c60042d14000e9880e6030105041010401484001c0d41d8003000b2a040c1c55100c000368100ca4000d0074032500f072140c1d10004129a81030a071124030100b07070800041e07800c010042c42446407000b4080c10880c0c0000d0520150751070b01c05548107103002d0403090303030b00c0340a00d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 875234856 1250 875233606 875233609
    0x403030e0705060f1b070503070806090c010903200f0d050a03030c210e070503010204150906052107120c0f12050115110708011119020c130b03031611 66
    0x70000b40c000c40d0040100f0400b103d05a161002620f12a00d50454540200c800780b088245c10446264031454051140400128000b000402d160b446510044d04542511038074400441d8261078503c0084c0c03101c1c1c82d0900142540c800c004242002c8140540200c0d80c402801e00401c10a01102030152800c1d002081000c0426900d030050501c1a401d41c504120008103014039001c2d5152080711146030a80d564000c490a007806021050003800e00030f0085440d0b5036620b840900c0b6039403101c04140003441c54100841c0c020702680c00d1354980040a08190f9090f4509401318400c00d5010b002501404103440004400503614012400030400d030396201128010103d00251041c1c3c0c03048058031031141000c00502402601c0302d2008841030440c90240c1034a03a4001400342401030340d403c115019400d03d032440406450110040c01c4980c84102c44040d8008a4241280c5a5074090280f42d40300910f000250640c400e241c21103900b18500030203891901d0b40041c1c2d0200700e0f81041c21f04445d40301c5051116500b9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 875236106 1250 875234856 875234863
    0xb09150114030f2a040f0213030210050a120c0c06060b091905030a06180506041b05010804050714060f0c01050a0e0708060f040606051002100f0c0203180609090403030e 74
    0x801c4042c0300a2a2a5844e644103c1c80e03082d01040489495112000070382c00d6960310b0304a4009102d2040d41159248502c00108001d030415000c01e9000c0c0018481d03400b12144590300301c1c1c0b00e840c400da68015161004080080180803041007071410031000a88140c042845442070300010010015544d65900711740003485203014030b00690000302046440200401e8402090131002150700c01c00000754929002100c5007046480036024215200301001c01040024500941e0f02520102d802d41e01c3c0e0320360318001180c414000b00d41c000d11b1034103e11410806800640040921004c002f0270940c04c2110000050340d554001880d0100c0341e0b0744036024803141e20341c103104481080034103002030032005080c4100180d503020064039180c0150b03400d100003070911084d070388428081c183c0148015040405210002e584415000010103250724201c41d0851025180c07094075242c0d01c0c02e4018504201031155000032a076010f241b40c580040041120203031555507062420710440c46601e0000d0045c5124062a28 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 875237356 1250 875236106 875236123
    0x6040602031026120a09120302120309010f05010e0405030a0f090504090309050f0d0816082106100912021c08121b041a071103010e100b0901060801030b0915011403 72
    0xda100080003502005da0b4802c800c0c605495803500841004500341c80c1c228585450001d1049000710b000c014032440e800c041d0010307002904030a0081c0f107241d8942c0081d888504003a100186554410094008041d005105c84404221142015032400742e4800200d0251052008200c0000b00f480c4014403240c0380114903004640c0f405e03034004419410307964030a1924410150181c071100d540d404040100803845080b26640800c0c85911000650200c0750409480400c0e5100c0c0d02c14002d41c0e5000c404036101701014012a2114080398401511980911a4507014114041001443c2c0704c00c1d20301003a20702004000100750001d024155103881c01d084440241d0724580b051401c8010002000721071951401400180d0310440398907034510103450808a18240c030300640c1e8142d400c00d0f21200045401043e0b6421403144100d0500176008294100101c40c0700902620000c2a150001800407444001401ea40310740c9580072190401d4103035200c0d10545100b680500101d10481c21002c0e0181800d01850a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 875238606 1250 875237356 875237383
    0x30a2003070203030c031f06082706010501030f02120403020a120f050a05090f090a051b03060a030f0f14071716090c0909020f0306040501050102030c06040602031026 73
    0xe045090405000b52240300103004a04045408400f146209103051141300c550048511982081c80e0b85001c0540072280868181c8003804204c0c1c0008a0008800e20801d82000c076440074109580c2003000550080c5052103180d9103940d82403106a0300f5840d00f02c200d5000754006d030001e01e0a000305240600805030108500800c002d0346140d4442c5191b04802554052000c0e410110b884250401c046113045080d509466800b2074000c2c14403140c1ea030207070b201a000f03180400503a504040f031800e040300240300c2a83c0c1d0917004120100704101151002035145440c6104901d1740880001c2610382c019800c210b08031020540e00300701010070624690410741c80411011001521303200080d4141680c1c007078040e1090072040c2d40c6034014040c109105030b000344003400d240d040454894010080d8542107070402c644140c091803901001040e01c0d80000241c40101d58020018089d69a69540c3c00b406504040d003400514a00b0000102d2008030130030a0700c2c1440300b24a0b08002000301400101c1c9484a4010030782c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 875239856 1250 875238606 875238671
    0x6010212030a05130f03080f07020111030604050c091e090a0b1e060f040f05030c0405131727040b04050108121308030c07080f0c0d11040f02030a 64
    0xd40000d5103101500c0d03000200920008441c2c4e0b81030842861144624001000c80700c2e502d03522010950010900e5010700064401d00320503545400717050703003250340303410109040b048107100082c502d14041d00f08603031144041d58250b0510500d1008661090059007022030843c40e035244d400c480342801998194081e9205406001000ca4140499965289031181c0081404d800140341001c1d00c51104541d5840081801295a41d5540c1080b54242e03840d4000e962180c0144110b0441601d0715020b07150003040c050354a4a24007a16681e2050640311200d16215400c2c020720001c1c0d03801c401c0c50b9444a801c101950010107410006080004942004a2051007186013034010b02c83d022000070300b418404180c60303805985050b410009120000b0960183c0390310711000441c032074180000725500c0101d0f102a4101d8007100460710340705403144001e180c03450b0840c01f41004200840d01240c036003640024040c000040f8000790000050503a841140d40441c000d07161000c003094001207840d90926041e00a111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 875241106 1250 875239856 875239873
    0x723060c030c060a0228200c0a0519061818090b0a0c0807030b4b01021f0f0f02190507120e01020f07120314182b0804050306060102 58
    0x1008801c117220540c504244284085c0304d80300c0d004940e0700d00247c0c13081c0005440c5401003011540d42d007001c1c442c01030207002c414100160a0034084010085207607a2180e07144803500303110040343c0c1e000b4006104034280312601e5000070740160070004000c240500036004110300110b401d14101d002009410b00b0440d078034042c5028082544805890342080d0b42d482e0216010300150000b49810f03155072440e0140d004880135400e0b860a81e00320610400181401001c0ba071400440c038000303001d14102e203c41c0075820401c0d01c00b400080070894103800d10700c05800000d01c2c502c0e441d11042250501015015910340c005188407541050003006000c090061a11501d4017006a865090000e0303c48040c1d1300788520b0b6241115560300038802ca801009400d400c4900b05641c0710400d6070303400c00d007400680116100d00382c0008c0749015802251101d116000c270030300c0c1c582d80c50b4051083d244244010310b8001200072070090b035201217940200500b24000d00c0300c292100e080004150501102815982c190360041c42c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 875242356 1250 875241106 875241127
    0x5010606113f03011217041a0703090b0d0c270e0c07050a03081e0c070b07020102090310060504150302010804080901090e1e0609010501020723060c030c060a02 70
    0x40b00d854200d00d0507003140041900009142c008441003112070555000400007182d0200050410050783d0300130614003100e20010890300321b45102d50700074a0704100c0c04121200c10380c2c10401c002c02e801d620a1400124455580168501d1900140381041070300340c840c107050149960080b41460f0100122103000446910035191280301c1129100f0a05220032076400601070b101540c0a603007d071500441030301d003007208510300109283d10032a9003109001c0c0b16500104c1c9520710f1441548280c0704400741e14542842511081a02070005007900110741d020402e079032080d1010301031003852480c40400170402d40e0606023088244d0303060314140f082d41445044100301503a03012801c2c0b50481c1c1c20440f055640c43c000f500483d00403244d50405510102250309000008071840220301d40d082c01d0300d141c41d507561903000401a9841080c0b02d1240113a10100701482082e1a03018200c42c030303901e031200006c3c8203010f107000310b0600d400501401c041c07130300042000e0720f08240a001d26036019441c00c3d411490b2000450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 875243606 1250 875242356 875242393
    0x22110901091a0108090c060a12061a030621010e07091b0206130614070e090a42260706050d0c021609540c030501060611 53
    0x80b001d0400a1120214500000501c504c1c2048503024004035920002e030300c400340941044c02c0303029403007514180300003a00200e20351a100070000c0708400d59113151281800c100b0300b01002100c4104040c010b510341c80c1054030902c2075001c03a403170040c05050310520f403420381022241c5580b9100a800c07054203001c0080d550104d0313406d80c00442045041c200070110305080000309140d1012054000c010000d102134603801a20741340151204440f01d030002d41c3d0380c0c08000191760060700c070150a8140c204252104020083c07080b03801c3c1d15584900303c24040200c1c4082c2c84021640d02404610369148101c1440d440508001d6a000708034100404096207010402001442401a02215560741d03410304140c0c07920901c652440055400050303070f541c54031140c2103001030078044e400300b9028580c0c0090b0620080c501003000320340c07a480c1c0002c03000040f02c1c0c20072412819003409c04501001403c80000d00251105440300095030145000080341420240007402c400842c80e01d41085a0121040440d0340c4905c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 875244856 1250 875243606 875243651
    0x12050702010f182105071e020a0605070c05120a0c0b070605060a0e0a0f0e0a1a01090b1305040624050f0108040807170c030a1112212211090109 63
    0x5040306281362200e040c086840d405100e034020b16034203c20010010344401e0302d2841e04010300850300020259640c03e0b040c0c403544103041000704100101c410402c6140b41070b03046039524400b07100c166440941c03280c2c7d407040b5890309500314484100010544005000c00c61040c50341c0020150fa2a01c10700d4108011a4a00a4011706140307140e038540c1c0c0341c480e40a169400c0901140c55842c1100e00340c00c5d40c1d1030608030103428030103058107441400c00001141c50140c040c02091840c06011400040164644940070380f0300144243c410329107400081d00300403559552154000415001c030751040b8180020008044103000c0c0c428100701c058070900002c102c800c012502495489024800c44e8074038101d80345000d00480c40c80b10b03580c2c040891544281c2c1e8000300c3d082d00198401e029101d003611032048038005030050300030324010010800d291118030381c5401c1c0d4060300100454848078003a0140c95502d548100e9290b0b0072151000c01d14500001c07402c0c5116005d001d0100c10400307010b4030310030304070040d02032818 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 875246106 1250 875244856 875244893
    0x71a0108060f07260712020a050412060608070e04050f03070201050f070321022101270b0d0c0303030e0c13110903012d0c050403080a12050702010f18 66
    0x510003140341c03030b40100b14502c04030614901402a031303004814040707034002044903010082005601010070511880c401c5032440516900d401d405d1034100071003e9102009684111181e039601c442c0490300040822501004104030500000d4601c0d1138078000e4100240b165402d8101d0340700740f002c840141c2e0080d054032100b448040000e600c82c0c1e0743d07003412900300d41c2015264010700440841c0c2c04d03a20f0410340090101e100b403007900b0a0388640141e20242c1200007441910894089070648160b4410140d4451584081c0d42001041d51b80b90311000480e5505481422506c20884c15000c000f0581c15000702c1600000340320103000080880c0c40030582e9040050002101315540b1091100c4000c481c40c00e0303502c030342c0c030140003004a403000d6800c6080c1601c20110a403000e603412446051401060f00442848034040d50b90360f0b0800e4070719030394040190000d001007801d0200ea0b0030620f417411040e200c2c4611540c100c0d4004910369022840d0013040392200000c01800c115a000c040001c00c04d410040e0039003000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 875247356 1250 875246106 875246131
    0x1103160b090c120c010207050a03080904090302100c030f0e0102130b160506130b0c0c0706030510030f150b0109050d0b0c1201030b012c0a0f060b040308071a010806 72
    0xc4966126060403240d401543d480007944210030a60307000010040030b00d61003a02103803015511001041800e0080d0700c4000c201640400c0705070490709181c3c01644485100b40100e8030520840914481524200d2070645e0009a2f50020380c0c82c0c40520307000d407144108c130220003185016581c00c0015501c0115001d030b042e4903800060707504a051102c0e001d1000b034a400c402683d4640c00c00680c1d90082d5401e042d03040c0d4040315034034041540030040c4400c50300062071480050581524168003034000d050010840752281e00d0001000010400920a90040a225405041c40c050b000c01d010702c210b42c003440c13941c2d0402c01d004005121030388442e03c0c08000f450b00b04a0301181d95a858508603281e03c03502c01c0107a269400c1c54000420805a01b4415058402c03203914802e1540494080500240d035402c0319003c0d032200351011648150240c5d001c0c4001c82e041030030100706036403240b81e841d0655006a00886041c400000c40d0401e01901e42742c8820009241400001d1651500c5105683d91070040c009454012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 875248606 1250 875247356 875247361
    0x5090d020d020a08240604020909070e0d02090a14010b0f040b0d20040e0c0a0801170a05030a0917010b0a03030f030b041104050f09010812070c080f0304061103160b 72
    0x540e007801c100000c206042c111015040c4009800c0018241517211075900d9000c880403407040c1c60035000f0307604849800381100241d6515040202c6244109a0380070780c10002c1c80c002100542c4071001c05602c03a04d0900000700d03106900d0564481d01c404140d00c02e4020810038040901101c150300c0842d02103030108100e81e03450302a6800c0950082242c450880e084e4038180380c28a0401c00102e024104a6000050303000f440e5480c007001080714070170340c0740c1e0b0000076940000521501c0180c0040b1030030716000c00c04546240d0318640d10f991455010b032201c84c002c600406400c101c0c15200003004040c803410705c0002d00c00b1546000100d51021958080201445080d0155a8449100740e08c4560802e9000308180200460004055030b5607105002d02c40c025903000c2051021818071002a0341201e100000034066803640b007050390180e4000c410104c9000e0010007000480079800c01c1550800c0c04980c001c0e694032850400003404141da62504001d00c1c0d0001e010a8060092000110320034a030010a02c08003035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 875249856 1250 875248606 875248609
    0xb150a0201060801020a020f06160801090903021c0530010e061f0f120e0a1e0c030b010501020c0904110d1505070807120207080d240e041205090d020d02 67
    0x4000c243c01c800300d1984042200d201c45580000c5110210074401c0586040d61148000410000c589100c2d000200303070403c004011410032984980e402c64000e03c1502c05001c1d0380d010701c03c100c465810181000a80105801c0c0c0c002204000340020f083c0c2d00c64803408808282c1041c41c2003144144541182220702c0c100091540e21440e001003580c0103c0f07240d0840024001030050071070281080c4100c0047c0b0750203160885681184500512003a040005040310082942c40c0340c24502d4141c40d03186d9402e8031030441d82c0012414121580918410b8144d001da03903050400091500c0130340310445100c1e02d966001c0c04080303840c8003c50368107213005071807003400031103541800d0354004442e4a20000882c6000200038200364045030b9503000f280a03a0383c1780c0e00d01e41c60041d030206a02401401500d141010003020580400320f030300c070f110480804070f4500c1e41042e86a0740c29000b00300b5640b11800403251034080008003d082e100c6a8000c01c024100b9a052290344404601207412806000780210608000320007035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 875251106 1250 875249856 875249861
    0xa08270c060c0111030c0307031401080a1202010209040213080609010207230c120d0e0406060f0e190f3002010509191203110c0607081b01050c1c0b150a0201 69
    0x10b030b078940134900c1d40e2400c15010ba19020340c4100c03140c500280c60220200034003880c880210b8100c5a41c40003c10b1202e604e500c030072541030015a40f0070300307641d0300f0008502c05031a40d00282400028105010400a142c09101800c10f440140300703030b1259204200744000914030100c5415030188903100d415500f40c1103989146030100240f030381513112000d00c600c41006000002c224000341e01036920b106042d80101c003800140e540e43e0040343c0100c0d1003555046c070454460903c6442d1403500810b0441c031103000c080300d2a03a0301d10a802c1020100c4000c00d0500c074080d8441d141c046441043c20318001401041c00a840038400c40110003410000c001518804660700c050f1800780c070482070110a280c03243e481c0004404003480750f0084001c544190b140740d2080501107420b02c5070309070150115140c90b1455507101c409a200d8012104596100460210410000d00c02c0920942c0035803000c669543c0d440d140c555200c9401401815413506062010b000d07a241c40000010fa85880034002380c4441c44004140e02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 875252356 1250 875251106 875251121
    0x22107051507110102061603110409060806040b010e090c1c05010e0106051005040e070f0c080301090603021305100306110909040c030605090f030a050a090b0a08270c060c01 76
    0x52040080480d8071903418008010000301d441442e90b0720420342e07807200680e2100c10444006405000c0e604030b54840c18040c1e0003503d982078a00b90120704d459101c014030f504683d020f070090f503c198400c42c200010040c8002e4031274003601103c1035200726031806c40d0815030348402c0201180d01030103201214050f60081e044003105040d038054003c1c084030021503d450300a02e0301d8800c0611521281c074507030040b80d004804840581c1c00908131550309588100043d07444070400724102041001c10501040030610741c07070145028190001c0f002c00c0c4076103140104401c2800ea0701c1459140342c40c100c1400003901440c1c0492040340c0d4003a5010403c01641c0501c144070f40902c14540c0e800071b181c0020441049441145c0c6001d5074442c0c90b042140c0e0300d0301601c45560300103600b074041482d4810070009900c24003510180005030404d00d41500161f0b10340d03100781c180d1b400030443d2001003202c00c0188401c002c2d21445810100200ba07040c14020340c10380d04003a640e9540c4400d454001c11001074240c090301c900713402404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 875253606 1250 875252356 875252359
    0x105031915021b2803090509040f080310090f060b16171317061b131802070c080d0e1c0210080a0f090305040501030c02012c12040302210705 62
    0x180340380003045070f01e40c0701d030054a082c841650100104000340c40ca00340d480b030b10403601956860b8036103050000384400c42c0800f40c0b050703940940b000940c0c03000a0171140114420b81603031031a0030030030740341401c1c0106980c1d000c01242c0d03030b090038804203104151030401a0b81031131100c500107400400c0c45e41410034a10074040c54030010b40400281d45001909240b144808885862421095552811101d07031f8440c101039a50440d204107640040642d108445c01070075030313400c80da55490010765a9044c4640502070407039000c91465008900c1c1c90912030b24540740001032200a000c0d1120b1910040028044890348002a200c0c2e5100343d002c052107000f4a888241560b030240410f03440c44070190028142c0c006c1200e4519100e81000b05810a102c042d02804c00d04503413548402e42003c4c103010054025201e202d400804543d681c1c55084100300038103014920440e08120450721140344130449600701100c5580d21024001c3c02c010800040e200c24010b000c600b242c424003080071520004141d401c0110079882203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 875254856 1250 875253606 875253637
    0xe0111010609090c090e0c100201020d090c0509130b060d0305070b0f1b07080d020706180c051503090303070c05070e15101d0f04060f0815010503191502 67
    0x101e000112503210714410f0380960244104e1558450201d01907590000452080343c1100c140103420342800c902d05d00c50145940005801c3c41000001c09084900000c1d06a6060f0044101041242825070049401c041d00b1000c0090308001c0307488203201c00d040506170500a2a11174420340a16108030182c91881e644000d61002505218411001c03401003507503689500221010304680040c082000c440180342d0084045041965801900b8000d400046050f87c440b51100c0000445180c03050710360507080e10070b4416000da54200000d00c800c5980e1485a1102a02d0810078084905800403e99030300048518000080c2002c900c0c00c18100342865120309943e01000c001e2044500d00c0c10400e000744c000c1503c1c00a2460342c42d26086942800d04008044807691616112526017844150b1240070131024102080321913031084640181586680310003403903040b03a983c4607014031605050381d0040004600800c1022540c030017580000000c60341c000c1000b0500507100e4040121601580c4a0344a030f0b0140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 875256106 1250 875254856 875254859
    0x30606030812010506040315051b07050d1b020307031101020a15020a0e01080c120408250203010b0118060810180906050f011a03040804050603160305090312070e01110106 75
    0x610035038220300c0100382c99122880000c20a810700e1810303201100d4015044488444480098000610b030103044c128440c014190860b01c098403180080c140284070700f00901990f140e2050060114404900f40d40301d0303040103003000780542d80018031a810380380c103c601e0769560480360300103074584021203400034018502034040820f468071590180c540b03260700f922111200c12000e001182c03516000c880f29401d100040c4943d400c0100c502c64000e034400d205000c3c4c2480d000038201c1d00d691154080e48072241d07030011844e00000b1406c0a005a2074003905c01c3c2000102c0a000c8070640f0388001c000e00502c1c040111420001e210320442c0025000141042c480051002e0b0340a42500003038507541c542560200c3c10304000c24140e82c01e46610302d0484808201034030302d05071411000e0550f94400307003060340c582e04140004205662044015400b60b9280040001003a00341c00c00901501d0f802418260142c10600a0f01e00c0101c46200295004000c1c0ca402d032200d40d05280107075441d00c2440d658038040e40c82d00a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 875257356 1250 875256106 875256113
    0xf0f0307141f0908060c07080d051f09060311150304151b0809060f0c03070f11070b09030607050403020d030f02011503061d010b030c0f0109031401050402123403060603 74
    0x3c2e0301c8140c54040060360b00b10303a940400c0c8410703842a801c0040281b00c04100848845070340703170b1050341c10441041d0052541c0903030000b9100b4105454001c1030503a540d42108004110421440c20080d40c03040d07400070020a04008110014000140042c00e131801c02031801500b03402c2503110f11003c7d850311215201e92402a00000c101880441b4040b00a1207580b0200d0004120724070b6245c13091419a001e1840c55540d60012190084010358030b400f40105036180f54441e031418020300000d445918072654550f0b8061040515164000d088141800020002440961141c00500d180d10343c05062030000c40092a0040f8014a40160020000e40c2290004000c00540c0d400c001c0c007000314842c0703a91800504901c46422221540d046562640c4080416621400d090b500d040c140001410300100d442d07600c0d200c0e014a0181044860301a035940c508010442c036110708180400e10100e0024142020220b00c00746252900c5041652103480030a001507100c1c02c001a203401031a44900140501a0f4919 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 875258606 1250 875257356 875257367
    0xa0e04060c030c110a0809040e120a09051c0326090c010e1e04051e07180b0a0518130216120212040b03060a050409030e0f0f0307141f 59
    0xc0400c0002400c1c01c01004107280300e03000c0c000d030f01340c030b02c00141018110990b103d00321540400300300b540141c0c950358051400300c03050068a0107101e9000a01750303904032165005040c43d00681003140724400908035070300304091400c3c1000c3c001d58141400c400c40301c4c001003c100300855210b07559441390007038004c210381501d022a0b182090a020b03202c400100e14250b04105c80c92040c070601742d81c42c003425040c9400358a016000745800c408415900e40690711014101c0d04842c0d012121580881d0542c0c00034114840000f010f03070014050b4002040c02c00c010081d0041461280754490800c0d01e041c0f40003080a6598055400c00e0450a1601195070309070780d03114031245240d00801a100003102402081c0568000308848610462651046180c5400e004e17000c0116000505601d8000c20000400304642d100c0f80b0418020301d000c0d84072000811800340802c480d0701d0891810600519100f0f50109031502c00042f41c0003540c07024078072280c03500c4556021030700002000c2c03094001c44d41da107010781d9022500034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 875259856 1250 875258606 875258621
    0x90b04150b0a0e1e04050c160b07090f0501200c0924030705031c020f06270a0206190509040221010e040b131b03051b19030803060a0e0406 61
    0xf901e560b000c26052404010b01e2220680e0901003e03c541c601c0c448051400f41d100c035034040031f40da100c5810020110503018401040640c11165404c20b00700340020ba6401c804188010321010006100c0c60341001c00003800c55408126540007052603031050501d0503418055002880c40191410603285017141c00c107410301c1c0440340203001c0c02c501c1c1501c4134480d00f1701050003000e4030000340040913490722302466040c2a103d8030481b44c0442c0150142d040d585e8509101301070180c0040000004401201c0f420122079012840c0740e1320844d4000d00d900001a200d20041c0c48000c1124101400000307560041a1010b00c504201c1c154410b1000036400c002e010ba0503040c044218120942c01c03141d80c1c841801804c0150700f43e5014061810207000201c284454000981390180f05a00a40200341003034041240541c45400440f0a81c0004180901c4004407820100400c8030032102c0c1c18402c49440040200210240005401c0c0c0400000141d0f890310307054000f000400d0390300e140800c14171300340c20040005c2008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 875261106 1250 875259856 875259877
    0x60c273605070e0604050a03240e03120a140609070504080a06090c080a0c03060515030318030c060a0819021e0a090b04051008040201141b0f01020301030309090b04150b 74
    0x100031400c41c044c14a40c0a0360260360700608030140c040c2c1162a035580180314001059107250b0407469008502e100d81c01070143d040c00e00c4000750380310b40f204c0d01c1c0041815802440c0242180c903001920900c0d1000802c0c03a030300000b0a45600d80d580d1a46541182e40c0e104036042407689214808808041200b0341d0700c2500c4481c00381c01140300c0643c540032169101c2d910007001518240c6450010300c0170401c3c0b5481160000005007095202e01141800f29003503820a240100212101e002c14007001d040a0110300b03c0d250080b21810315108109201030104400644144c0042d28660141704040d03600c0c0c1d048410300c14141480d0303050040305402c05007640c0d000340c0c0008001031110304001142400d0800381c500340c0d04020580120b44003c4501210f68500041040e410440d001942ca50003101c0800209a00400c11804527400c814203c1c200f8503000600b4032080741c0744c0c410001000445c0e8068030103010b442c280d8002080381890200024007a0001c0034034000d0b070606103940000e0122502d0010500c4903032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 875262356 1250 875261106 875261117
    0xc0d05040f060e011d0109030c0e090c03030c0307080d09051f0b04090c18140903040303020f06070818030903010606030f0b030a110d02040216060c27360507 69
    0x8072482d084810072032060074140811032500c90311841e850b1180d41000800710601d0210303120350307890701c5502d211100c82d40303d100000e0440042c403918900512580c0e42504003640290310f00403403510000c2c0d481c820100007a0074240c002c2101d0045104a411441501c3d801c88122200052048415800c1c0502d00320182003880c0740920311100b0703080500a440405401c14050a0254640808180d07107d096107008280b031650758001070308103035078204118002c0740314034000c540341c42c203601e0040e1278480c041b00303e2901e550103003040042140d070021440760f1041e603842c10000f00b1004000c1c11440e5000c0d9000c056030650a00d80b020a1096256000600141d444902842989941000d260310340032020005096084580c441c552942000420700c0840c52010b80700501c1c0c03d41601500717400c1100d02d20103d58441e2108100204540c1c031441da4911900c080020f20382c00d400e802c8411446013045d200d00009003a0710a8907030b04c28000d4a001c1580401441c2000019050340320750b070001000d045031a4004201c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 875263606 1250 875262356 875262359
    0xc15010e04050309130209030a030e01020d0e150a0c0b070c110f03061506070206040b04030b07111f0b04020309151810050612030c0705090a0509030a0e060c0d05040f 73
    0x4841016501070340c2c20a000d1071400c8000024403280048030707107581c0e00d604d800704030515654038200908401240a0341d1461380c0c011245000a080c915403450346020412050903903d099505c40036041c42e04103080000540e504110841034400c0300d960301d00541842d03440402c0002c101d03002100018028402d01e8a00e8101d01380104002080d41150060707601540202d000901002818500140d0810700404290402c0da095001500da940150840d40d2403110201d0100100140034524a81260040c241000756610388400176a031240340050003c03420b0495021074040100c11b5101e03001000000d0401e6559140501070169208110808000c4204000300055100001800e071000c0400145c000780c4403050503504004003034400a0300e00c0f50b020760b69803088005150100300400403100031402401c0024503010400c0420100204005421401c103002c01081c0e07400882214070510040c20150f140303440d003202160301e03401044007004891003444010100d0f03a4001c1c0c083e01c11916000d45400702c2c1c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 875264856 1250 875263606 875263619
    0x302100f02030306014b0302040501021f0609051e0603030c031219051f06030b0f01031e0204140f1813085401110c060c1501 55
    0x800300200c92005800510104003150b2040b410360001300a0310854140320300004417142c9040318122207242a0300446d4080b41a124140a50010b1104050a0445c10b051900c2e0001c4d480e0340001c000c000d400a400740759000001d0307040d403205000e003c541f4400c000c1450141150540c4d00b1440c0c107241da207600010009a25171800200b15448460f0400c09181000510b109000440001130148100e59601540359400e5010381e01c10b092203160396000c400c200c850b03040001281541660070103400c050410382c17180b010f80c85009070409440307428a0006040514086e00201c001341e0002c0130046503000140000302c02c0000b181070f2403085411641000b504c084202000300c91018080c032024011140d0b070010b800800c100301c400d80301502426a0740c1c5801c1c0c05c20a0840c8116004011402c4d040b5202411706420295230780442d88507014414000e42c0703c80c0018414030301d602d04440141044054801d52480d41c03030522011040c0764001c0e03c0c164075066102ca071152a01070b4040681e0150050f1800020365 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 875266106 1250 875264856 875264867
    0x10e2e1a0405120615060a020106121208070f093b060a060e0d06110c030d06150f0914060906030c070212030a0c0303020a0c0b040f0623130204060f060504030210 71
    0x348007046201c5c500e01c450403040c003400e50040d6040707005556032110b0000e4643d1411a01800062081501210a20b240480a044c801002e8246400c202030304100c101c090740c0200d08003040c0d420940403064464091940203c00100d0b000c00c4a045403210003582811270b0281000b54000e02003140e0759400b2548403041101e401402209070303030340b104003035041c60082910351344204190b414204000d86010111050245954046030f071410600b50344034404c00100360680c000341500f564526021608030b1445800808104040c01440340d08403441a00d5481a80c40360120789040700007502041c6c6900c0c0c40840c802140c2c101e0344081e802041d1042c1109170004c408001c075a5810060b4458500000c1e19840c110300030b40100e9800c00c1030002081000300032800701d0414a04c25882040d0110341f18405140075419030712455529800711310106c24a40303c0501c1301e6503469002020250070807218540b80006030242c51580d0000c165108011004074a6961000080056038000d0712501c006001c1d50300110341 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 875267356 1250 875266106 875266111
    0x30e0615030309060d0b0a080c0301050604050903190e0d031d0103090b0f07030f0207050616020304080a03050906071b031217060d0c09050106030e0105010e2e1a04051206 75
    0xe042e00b04004034025454501c02404003139910791400a07291651401040407201603400060311640f01030881e0001d854240110307540464103503410311141c1410400ba59407400b90401803954440000d8000300520310648495a07440401454cd80500351142800303080f03140d03409400c81d40c180d481d840d224141d5010780100e109407503010b207a5410940d509000d01c0d03561280500030500b0542c0302c080c8000c00800d14000f41012500a501403d03a50502c00c900729001e00c02d80580100b950000c1c84104806000800c01d142442d8140c104640d44105410004556202d800c000800d003044e45000700c000c0707407201c0201600b60ba1241c0b10802c50000303c000c00755000042c000c42e00c42c81c41e080100066075810480d0703402107024860a044c415040d1a02040c1c41620300980103240002d0760760468924400d070901480707004004c0d901c8414050708000e0718406a4503c41c1682e01e0004a01c6824282026161f1a0b0b00e4010a2014000700032403440c500d150325282d0040c40f902d403040d800f0403403000607107401061a50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 875268606 1250 875267356 875267359
    0x215040f150f060905100302061c021e040810140a0209010e180702120f030a02070f0b0a0203150d02031e0a140d0f0e0d1707020301151d0403050313060912030e0615 72
    0x60501044070540311074060454004400c62fa02801800450041ea08071034085185214080d501c5904002620b850424030280e43c140543c1042009000e00101c2c1825a0308600340c0302c0b01598031100000143d80212a8004844c5c01900382540c40c8081c52004040d01e01903001070f0b081d103030192110b420041180c0a00080c03c49007a0741040441c501d840540c1c02000c19500c2111510040b102036120824660740849544d20015000008c0214000c00b07064054203615040b82c14191400880c1c0200e030380c4040350422640c06404d5030b4440a0414001c00402070740642c4511460013003000c0401440d152250850690003044280355110001402104400420b400190280d000049980c44180030364000b0084590f03d080304005240141e102030040328003c00d03100c0c82049070280350802c00e2801c00e440350703641c9541c01a0701082c403000a0f485003c9a0700400c04500140707403200303141420001020342c44401001005c80c0012690259016007092a125210006454a55880683d001460101d01c3c131100d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 875269856 1250 875268606 875268619
    0x60f04060912380f061320091f09150806010c1112030d0501080f031306050309120a08040501060f120314090418050c010215040f150f060905100302 65
    0x40200a9441038803000b910140510041c40124007000c0385034000540c4e411320044248010801036003880703134a8140302039808004010101070442c50004050070103030901d40c0a0b6001400000075510740071110302c095514100c2c65003149854070f01801054144c454000d4000c200c2c0a2540340c540185080d038801e1006841e00c985800c80c0c0d90f290460041c2c8810695030080f45182c50110201c0200b0291148803102080010b995041c507190314584125002440d03466401000f22018001c0e104100e001142c4240c18801d4580d200c001080b2b040001d1050f071020f5003240440d0038035071544c1c00740c10180501d000b03030000c03c81c0039202c40307814000700f24601034901281403100030400040d00c00c0b83e0486145141c2d00b000c9080bc0031501c00101520fa0b1140d000da0348501d000700c964144007080c0081780850200b40004d16981e1448200308588100c010f001600d20002c5454440c207204003413640ca0107914207494104041c21012002400501c51801021001454800095010b9110081c0203050b0303074000707210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 875271106 1250 875269856 875269883
    0x1e1b0201080a0f0606210207080405010c050a06050c1b0105010f0b0918040c17010c0210180b0c0c0c0f1e1c0c03030e100903030518060f04060912 64
    0x103585106010701661462951a00d0684600402d48201009001e0546c1c8595820000e015056081d1042544110380188100081800690301c80101c8046490a007080e40010303000e8180203040007903252016001d1428102001400642c84c001001c1c4d000c00c42180c0d0702101580d01c600c0d130890700d00340140020010384800c18091310b100d00002e86043c6200401125000c6c22074070703100c02c0f0b10400740d0781110000000c0b20140040071401c46805800c4603135a000700061b410604009513078084440c450b800340c541d155048107080c42e4540f018405160800f5110360941880120b44100741d105960704803c6000c0c3c11039401580c41c208038440400740c002401882c00700e603c403030f950101c0c1c49030312421680120214082d483c400c0428800c1c1c00c2c224050754230307501c0c03007880d6003400341003145c24520403840744908080280c840354000071070000790b980515003141c4540000c040d01c81803003028600281d004030040f5001c0440140b41000303205680b201e9850095890f52002c0059084404080080003e80750585 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 875272356 1250 875271106 875271109
    0x9030c060c0f0c100e0c0306041110200f160810020c030412060207110901031a0c1309020403060b0307050105040b0a05071a0414060c07140106090c1e1b02 68
    0x600b03a4103000380e400390324102522190a10b0316404420342e0986546514510074030030014040854040d00c02d80c003a01c814a450f0756030600d000d03580003866201d070302c0741e0031800b102e10320800240c08405880120400807a11007000d16599a10084a1030ba0364402e94403c1ca0181c0c0c02d000c070b0319044401c03003401440e0321130b0340d90118006900880307030f000818482800001144840d124030038002c0c60081000603504c2c4280e0401c41e6820301601d122030b0044801100400000e0003000d18101040d0b0744401041da0ba89500c1c003217480c244196581c40008071818200814a24000d0b402070040700d108460411a21401c1c030241a115969031203190b01240c4140400c0119003002c20061030580401d1508a00d401d01c81c0d0349001c5981c2c90b41041c004100c20220401c420441c0855400001e080544d000b030805240842080c8110b110300880100300d48810000341080030300c25048100a1f2001d414180601240035800170001c2c0714207445102c1d65081518402e08c0c060154410800314003418001305484000c980 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 875273606 1250 875272356 875272381
    0xf04050d02030a0c0e010e091902040e0c19182a0207050a141e030d031a0303040e0415090c0608071206090f14060d1103030c07080c010809030c06 64
    0x16090b80c240c094445035a000401441070341c4041c000c4204110707082d505080c1c442841820003046070390507a0010801e0200d4038544003c001c1c0e1290304079804038215082d0b0646a040101d45148103400002d200b034050300c001c054040c41c8094030f8014202d8414282200d1010065070100a81000c00f406540390030446030070301c450403c69440e060300454032141d9444c004103031642880c0e4011045818542d461040ca8545000c04907400210b030000d600b0a40c5038140000e4403030f03600c0c9032010181503403844520144d00d00d0507600800e0040041c1079a469555515804180c540c04a82c02c640341444481400000764042c8964180c1507001101050703054185801550034050140c1400e084c403c80c1d8903130b05601d152500511025241d8881c0225846400c54007a074103030b03104080d008480c0c0c0320700750402c040c40e1960300c1c9100409800c0b01e040c14180c00c81c580441d0640c89a190103880c00e0050140c0825000400211142c8818003a6501c9000d5521b9480d002c0d100e008800a107065504400b010901650604 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 875274856 1250 875273606 875273629
    0x130308060d050609011e050709051e040e060618010b0304080d060b0316021903080f0402010e0d0b07021209130510080114061801030807150f020403050c090c0f0405 72
    0x7400c0c120700d80d10a07440301803405a00300d481203030716916858418404824840c0c07403142c111402c03c050285042501001d0140c492a0151034001c500d0101d00d41d074260354603070b560100550054410401c24080768140d5032039a0007200e8031805943c4107412a400b0b814988a201c1c101d03074082410794116101d40d40d660505030b0041c04446847c60700c0741408200300d03817108001e602440900001b0f881d005241c05010b803c0c020075074a00102e10f00d044601002003034010078580d0b88484c8144800210b50f55510041e54045524607a85803c50226005a0100a4803043d101d000d18101d808641441e050343d01e035100284128103005401004201400ca00c588142d00201d4020048049101c401515200801d00b103480c4200400d55140d4040144500d038200040e80096003d0b0880d084441581552a41d112521511310000d0008820b60313503801c2e01c540980e0150001400c00801595074070340c0c0303080880e40e910320450518400c0b80500c011882c00c0c40c0a9088030200b15004030004c2c1803d280404010713560085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 875276106 1250 875274856 875274859
    0x308040201020c04060b0903060906060307050f0301180f05060114011b020301110d060e0a09080a1b0c0f05090f22020604090f050f101202090705071a16020613030806 73
    0x840f400000030799564010003000d82140000107855107182006c051801402403e4074003140c0168040c02a00c0c5c17030104424050340c5050740c140340d807800c0c5c180129004249402d5003404082d0010000b60070004044641a070441c040c0040300d48a0b601c2d120004d40310ba085204860103c0e003184c0d20002c455083c3e500c10240d40d800280009101eaa034800c020b1401d07404107440d102401d940e0202800a0440c60303503043c1d0000c00c425000c00c4507040036941c80042d03204000380801030110007522400c1414984000c5d0380322640c04078a24640030360f21010380e19800c00e1030140a01c10642d19002801001c8d00c0c01003140f2070749a10229569811092007500d507a8180c15005a070440020880801c0d00b80035402802482507290a00095600c0c00041c4075451b2480a0900c2c3d458409110701008980c0c50701000302c843c217070103c1d0100c030300391102481502c40380305d45000101baa07255081c11000356264030f884144a000c0865440840c0152118101d0300e07004200c07002e55500d9100134983e40402e02c01c402c402c0d880341c0c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 875277356 1250 875276106 875276113
    0xe090c01121503290603070b1b070f1a12150f03031b060c0c0d030c2001060302010906031415030a0209010e060a230d03031503081e07030c030804020102 67
    0x815036581c5a1451442d0400d0f01c2d80c02c0b0f501e0342c1103a180c2c0c0f102800c10180703c0305004c618290600c1c0c0000303503d800b500d00c12208174541c01f0440382082c1e40341c6510040b01c1188501102c480075600d018910070440300d4401c0c41030800c412280320007445101d01c00c50b150381e241340d14608030359030b00d0703403184010000c050f490607400c003400f03031014621500d00304018098a090102c40740f8000d4120418a40b914034007d050840b0860b0510140e012090001001c040c0840d090502113104e5102d40130446070034680c0c0517010071004900900060407507065001c041503038001ea80c0c1c4c00c5520f46914040d000d8488401062145e035402000050f0150081190f60120300e50080a944141030303541c00081034003c00707801c128981020401480303100e1611031040c200400c481680c0c0c2e0005e01c2103032030307110b1002c0c1c0548009000e40c0c90011440c007014070990000b04045028034202240c25120308240d42140c01104018001e00002244001301680800695008a0341a560b01010180da59000c50700510007038400c81c154130 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 875278606 1250 875277356 875277371
    0x9090114131a1216090501080f07050904030f0c0b0a020c010b010f050f0309100e030316030b10111c0f1d09190e0a0803070f030b0312220605130e090c0112 68
    0x124480000c8004004125002c281075051008c2c0506003d040994070700300e54440c020410084c4c551409845e030058040c00d0962139842e60080a540094810f0b10041000d0400e004004295001e80d000e02104c00b404070007041124158001035481005006982000c11700a01001d600701009200950b885410402541e04510302d540c0541c00f600c2903c2c4071026590008020090101644070603c0080451032506000a000c10701c0403840300d0b08503084107000c2011b40d803214500403c1c10007107105c00600600034540e544a10b98001085092030200f6100016210f8039110b03032140340707003c20f10304100008040b0203494a81410840b081c0e0814450000c1060300d501d0109042c1c103045c003a00418030301560316544e49141c100001805815264105018145001e01c01c1800703440003e1850052060f5590382d0340e03664240b85189100128070f01c030100c03480501b15004180c1d04da2180160490415100041e00d81c941c03180c10703000070080115128107840d84104515001341d8498408a852a0b00b0502c0c00681034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 875279856 1250 875278606 875278633
    0x509071e020606010e060d1e06180c0e0f1804060b0a0512281a010e010e100302040e0a0816030e1017060a0e040308040b0901090b040209040809090114131a12 69
    0xc89400084230100b81e4641c1d0401c00780038200e081406036580c1c41401c21841111040c00351414070035510b80c60050742841e0701a03d598503410b400c0c412608990090604078a054540840901140d04075103000d28039000001505041c081300b40c0c0c0e40140c11002a100d03140d09907883c90340484005501c03051100c00710b00a64041101803c2d101d031856212111400b56604201316a000e420040e880070710a204410100f007110508084980c09032a030464012444070390180d031185c60200a02e0300513110200014070b0b9808042d0f05180b40020030b1007074541614a190010400c0084e1007511007810100e83d60f940c1144a060003858034643c01b50000b030010460316115101b20750350f02c50481d4228040b07900b9805000500510305082c3d40c2c44030a50000780004410340d074514507130050141000340101c2c1a07202040412100354280c41000401074043d02c00796075100d20812440410f154964028107541c0500e529240d9140201c1208400b0414101c51404685050101c4521011803800305405600390712000e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 875281106 1250 875279856 875279891
    0x20a080a020a17041401121d07090c080405030a21060608070305240405100302060c03031b12070507051e030a030b060a090b030a02040509071e020606010e060d 70
    0x500c00794020b0030802c0e10b03854198103010041c0c903401e1840106110401840c4c1e03044541c0c504501080c68006003c1400e000c1c2040130f0100c440304440015904803400001d90000528002225000780041c0310000105030180c0701c40005660150080d0000c00800303d016009006019182d80c9040007115840c41c4484640100c400307640054002403501c0c024031116036458025a130304254010885209104012a00050360050014445c00b0390740f1200001d18504150101e0300065401605e0103035140041851a0f03241e07842110f1000c840140642068406030425055551900010290b00d100351a6450103940681145004640501c1800503050700e203d12150f01e03040100240009548138018540040c0076101c0f824103040c05048184515150315901c4000c0200702c4050710812030380d9403204a111000384c4955049990444c218600344082c03140d1100d00714200215100222500200d00441262542c6040c4c90741c40c00101008900380680c82c051008000564821130001941120400c03045074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 875282356 1250 875281106 875281117
    0x7081803042408070f120e0a1505091e060604020304470f0a0902010203071a01260a0818030f0d02240c0f040b030a05010312030624020a08 61
    0x714284002d986968554000400d82d41000e0941040b160000040b40000c1c662407a100b0010078254840c1901c030303514003040c07008120490b044280c56804402400c8901d021700000e0f50349805034030441001c1c4443d01140000c00080820b03210140c840340d01c4040800c070280d000584247e501280714030040210702124880005080107442d400862807901c0000300c1c0c140550303e211568605400400c00c82d02101a00072994440c2c0300400001c0c000d8081d000413840c0d4050352000a100002c850380c0582c2d118410380d80c96040b80c2c20109038103c0d0845c042036240580c0c490035212445640020701103000510a000030340699107003401195071040809002904e8401002c2c1d2103070064000e061034000e215418442424866500f00e01c40b800100020040002c0103030081455100c2d85001c00c0c2500078014150445004100380c0408580b60300f40840082c000380400e04c4100d450224808108281601074085d00342160354480112299040d03d140d0130804c090070b00c44240450045068000c00200018050300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 875283606 1250 875282356 875282399
    0x4060309230a02010e15072d210309020f0d1511040801140f07080405010f0f0e0c0a0605040302090a0603020307030b0f100b0708130e0108010903030b06030708180304 73
    0x41d02e02d55a000250980b204800184e000740303c5806c24902254522007185c0322203a1100c00114507190781c4455a00c450f0001011462204200d6540c2041c022120b081d4001c4d8916000e280c000744543c2d1809800300e440d02e540081d040482c45071800890b02d045d0000c1c1e03080341d008054a020304011603e111045404014013080d0380003010505001040e424070446050100005141c4410b091048901c144010014106e2003004142d40000f801c1190a4100d10040000d80d81c0c04d0101442900507100540a0729004c0c030554031940c15a80c50034644440c5a070200c0c1c240e03880301480c00342103401b48040c060f4002d1403141265142c01000006850421030f841c000c40c040c80c52940641007480181c52110000b9004a00705985a8402d0002828800c1124021036100500981d10011204030002101451344080302d2045146c0000440080642100700000e100380e8042000340f11101c10007040380401d40f0218001203010000840c40c1c0081c104404d44001040122402c3c0356581032521018403440174500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 875284856 1250 875283606 875283613
    0x3060a1e08030d0f1404170a0c050706090510081504020903010207021f1407110d060f0519150b03060409050a0b070504030b0105180601030b0a0e04050f060603070602030406030923 79
    0x41c40c1d0002c1d40d100c0d000c2c000600002d4203075241081d0f00d82510003a1201c0707800047ca480003607904a11402441c1a207000c0354007009890b00103a035400050a009020321885e40100a601c04168a66225000c940e02c40d0708908401e400210301001804025000301503481c2d0199802c00102c1d015a441602e0759200001e40c00e2346181c0340480000c010150031840280a1041500307201c07250024091a13110700340070900f80c1d13003031840700e52500b88030780500005007402101a20302002e009c21180d001c1c0e1001c0c40c130101440c0901000d5501d0340148546402881521005030342480846c0b590324254100c811914015003c44801525649178040681400e032001404140c1c00074041040000782c0704441d004140407030365000b9003208a4402032000340c000f0201c3c1d0400d59241e81a00c02940c42110100141008000300f00840c5000d01d00a030761800c00d00e01021052007113170001061441e00003901e505840c09a406141020f00e0004140c0280850580869440b001c1000000301d078211705070312202c1507d403103005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 875286106 1250 875284856 875284871
    0x6050106020d140306010c0609081c0b010507020a0e100b0f0301030c050d050c131d030d060f03020d080d0f020307050a08090d1d0d0503030906040303050c03060a1e08030d 75
    0xc2c0ca80820b4001d03280034020310a000010040b80d0030250b981c050000e09000001131494a0030400500d500c4000070400c00002c1b5003a48181028a0314002d00070140c28204100306d17501d030041d650390040c007900075481050240d041c004030502c2121550030002d6001000311094403001b0990868000910034043c8400200041042c4a1842804c10082c00e0035200402035080035141caa84800100002c3c1d4007543c4040941c5210110796480b00c60501101c0c2c02e600003244440034a20380700e81c09015a19259400c01c0c0010650840174040b00c021242d00038910824000e80d03590b8509a504920b800e08000380d5502c0c4da9a80b11805800150311404c22540c5090743c8081001024044c5080601091916070110b5601c1c12401d41110903034250b0784d2082c8582c46811496800912840c10200c4002c11500011040c011480d8001607024042d5100303071810f1100d5a0341c0b44642078140800c84003160b0081302c3d00360801a2511010030950108181c00c0540c980c41d4881c03160515582c000b01800b011290f45161 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 875287356 1250 875286106 875286119
    0x1506070602162a05060f0406030b1207060917011a0d1505010b0406230f0c0102091302090a0b07170a0e0a06090602011107021822050d0e0303070309030314040909060501 74
    0x2520406084c0c11038225080c00e40911802009005c0c134050102403556414403005180d072140d200d003c00980c900100d40b041070700c0b080d0080200319070b44581000112009600c0024100c1805040c5684418400301048407030540c0c01c10036480070307024040e201011151550954942c0d5030103040e01070300c0c0c03180f1241e54031780c5070540c0140080031306100c00210511032003090042c903240c841100c44043ca0107441544170404885028024480c2c614044e501c0030408810840f11400da4001d0f02c0ca09904071400340d1400e070344450359526031040b410010b01111030f00c101c01c010400703c0d00280c44404141c3c40c1c02000c0003034980116402d1038081d048240401d6485104122681e424068546581507804086052291690100d0552503600a115507010381d143d0008000309480b04400c901481e180c4282a03820f040c5003446919240c1c10000040000d00c440c0c00d4020f941800012600031f15130590302e60420318a9134078201c40551602031a41c00a18040200064052042c0505801c0c603010300b2000545504d0700e070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 875288606 1250 875287356 875287433
    0x2508060909061003121205090705010f0c0804183b0c010c06110c070b0405010806040612230f0f0607020d02100c020a0623150607060216 60
    0x10180e08080d4461000c203c0d41c010030420460481394840d07110925207050400c1030341c1100e044414041440c0c40c0004214840307a000804908541007a2a41040b41d90034107400c4030700ca0442c03c009440d032081044100440381e0003111841c4803004a84001070411008130070074030200c0c000c41c5031010f0074201e000300c107400c001c001d058484103400e81c000405608a450001a101d03550b022405816a07a41e000b0280401625a0498818800030b0702905c02c01038480a405482c0c5e0401d00030907000410a8001030140d003402c1c821501a00c006045961144106640320500800350001d01ca000100c0103844c41824402004180032800031312b00642403030310392000800e01d0b00c08028030180441d441702c00b40308601030300030840d401b00d0b000e08000131904101240c8240c0c6040700110300204103a24281c03d104142000e450807641d000c000700355442c0300e9203e008016803078290240d4060750203a030030070804000032071982c000c00c070490710360b10004441003480d11006403240b2024210303074010f41d403035007405a58603810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 875289856 1250 875288606 875288611
    0xc0c01090f0501090629040506270405060a05070c060902281e0e06010f02010e030f03070e0d0804120c0b070c0812030f0123030609010b03010e030c0c0925080609 71
    0x503c02408492100e0381d08103c107404101b071401a6501d40114204e46c81c0c100030040c0800c50040310064500c9004001342281c4400c580c20740e5079000b10408640e4201d8207008131030140c42c1ca65140d40620030b213500d42900814030070204903408200c48056090344560011440000c0d808140140429807502403102803039645009403c4402182890074041a01c0030600280c000c0820700e030035002207174400407da00500f002880702c2d106100210701c0003005040030b07000b076208042035510f802d8043d0246003808a004c1c680040201450020f00090250008a01040142d01d020790040c40402d036030341000075021fa100301425204610b001506005400081021594542c54184818a54901080b00141c900e0701802a20007640346e500c014108102c030a0b5601c0c41102c0000c080da4414105084114000c01c1e200c213249010b0350800468508429000c003d803126059104040e080ca01e40c6001000f6825500401044002c1400101b081c00172214019142d9680305036190003100d41041c004010449400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 875291106 1250 875289856 875289881
    0x42907170d0b01170403030209030304120807020f18040b100b030a0608010506011b060b01090302091306050907050307090b031e0604030206010e06210f0a06090c080102120c0c01090f05010906 84
    0x100078000044c4ca5100351400e078800d07018580142c07103414810000c0d0540c82960301c803187c3c41c4005028481482100401010014030898480462109103014440b0072040b410104040110386400200441c01449190364042c5265000641894031080e551405400a0343d90750849952580188025402440b51680107082400d215070b4646294040801c0010a0300c0700614031600c54003600c00a0f4000c0c1c0030341c0043d6a00401041d15454a0314034444440e80000094071124185004103030341d0302011410303a06940c03001c0d01034a045030078400b40002900c1c450110540611401002e40000401d5081c0f01200102820191507d4100740c18028940075042e04044216a004030502c110b90b5601581200142455005002002a071666aa09100d444881040103020328641c42080092503407240e00e4042c882c0d441d0f09507460f1a510841c0c201c0c0901ca8251051744007a50100324442007000c0500b8004103030b41d001040c1e0311810f541d1000e0740d503111001160642c0d11040a0000c0007000e00134105040203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 875292356 1250 875291106 875291117
    0x71e0b0d051f0816171c020703170304110919090c03020910060e0a0b0901120605121609020c0d080430030b011103041e030803010b0717042907170d0b01 67
    0x44400d91515084072151001b103040c10900308640090080c840140103680041c00d2840820102040c1131295001312011103007000504030086091902c050a580203400141d80c0d00940848440203500a051507001550b101150680000c016a01c94000910812584408805182c6003400140c0031242c910703809845440308460920040004e05c01ba070701c200310240f03070144d201351a0054030402000140c1190b074010080f0000140850030008030030404002c01c11141d60500c2d940c1c0304000c202e001d8413142c03205940004c9000d0040318852039031190028012003044081c0d001c410071500c0c0c01110080340a01c101c040801c00d0320701e29014490b03208901c030b003800c0002c001e040f1030000c40c2d1248220b018111400000012541000c044914200d02a5521190441d038070b585800303800c40700750848041100c1e03e82480803020b0100d16403406480454105e61803424904810b00c0840c480ea02402800e2640d00005100c00000b049803030b02d840300200000c420642d5241c0500001105a0b40c40c1b00340d1030f05100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 875293606 1250 875292356 875292389
    0x108100b0712030b040e0304050f180f040c090513020405090d0f0318021c05070f0f05010f11010515030601120b0105060d020912071e0b0d051f0816 65
    0x2040201100d110035405040e260400d00e001c42e0950007010b004495940291405242d0840c8070300000040c8140d86046940d234180d401941c04000d501d034070031000c0300611260200031a001c48444005560018030841030340c0495900c1e04860000c695044600c1c010403015641e011041d81410300c106034110f000f2402410000004841c0a451740121030100004c150351070703498039501c541100c84041c4081c0c0c001e1100f202c8142c2e080c0c045500d82000c0da41a991800f40140014103d0200307003c960442d61950365501d04d0382c0c600380040d14120f4004010206106000d0a0302c0c0000c3c0b400e1140e0fa01c54030808254610481100d13090514010050300840d2100c408c1c000b1001c00b0803d440f01250441e0011900183e48452481c850400790085407040c58010006600010b880b5070007188042c242c0d54420600c5003080400a2180e501c80041d108855040c0c0302000035540d11a015000650b010511540d0b601c2070310070099422079643c2c075a62090700e068100440300c0380110a400901001010021514031590707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 875294856 1250 875293606 875293619
    0x3060303020303061002010b151201080703020a090b0303160609050d02010b06310314121201030209150a180e06010602120d06090f0507020c10080106050c0f070b09010810 75
    0x9100243c002ca105d1104100c501000070710075004421041800380c240000e01500060481180d0401015044c40786501800490101c000190301404c0726002041900d07002c7ca00b03602074009144c008020340c1c141c00b040000901580d1785007aa9070b4113502c6400001160000340c1000e40c20030001180c146c0442e41130060074074040d40c90000703480804040f0400300c11440400846450001c3c544e0b107400c1c02a0b03402c0c1c1d40000c00c2c0043e94103030092811135103040c2d804080211444200f07602c40d10038a41a07441e01e1000500250421190181c2d0040460040394440d210510004000c0400c41d800700448946660215000e03071007078003440d5801d04103440181080d50600d100039486000034210f003452050080b810343c6e4150110382024005141c010350400020390f080c540303134010708400c448160140c03048000306903c0d41094440b04960b0101903456a4081c0d08250045400390300114504441e440b9094a6014561003846901c008129200b15960741d040c0840026110003c024640b0303e00250110041100c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 875296106 1250 875294856 875294863
    0x11403060411090301050f0f010f03053408030a0201180203030702040c0513090b0f100e010503090304030212060103020f1806010f0504090e100501080706050f0f071a0a050105010306030302 83
    0x800c100c0d00800c1002ca0582c2d456000d01503500700c59855800d20003841040003044601038010803000011120303a82e2030340340e1104849c41c00d06c4010b0003603010350000c21285084548480d00c10b001703201d01460315003c0ba100c83c2c41003040c40d00450300b29040010742011701c0d50244901940034020802d8065581c1450300069124000c110001c3e010315150481542e0702c81c42001159007080c03528524000355900c038070324003005083d01d6a90600600c8192072169207480c2c0f007400c24050050a03541c40c0c809565038801103030300f034001500b40d011910040c0008001640c0d5401d03030141c2c0c08a140300a04082d031440c01003008c15503d9209003800340c1c0940c2010705054440c0741d20540d010600382401070341c07201510300889244c0300310f42c40403d406242c10551781e5010b0010608000c4110206801c1c803450b625840c04685480d428401c84001c100200500790700300d0f0960020307204440c480d658560074410300d501c504100320512200d8881d17402084c010052004080c0c800c03180904800c2c6420170480e030550341c000c1d59 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 875297356 1250 875296106 875296111
    0x6020c01020a060e0a1707020117131716060f23150109090c0503090f0c0f0108191103010612060312050d0e010e0307140f120703051201030f020f011403 67
    0x2800b5211046545014002c2101c1403600391b11040350074148140b500c94000c3c2e03030071020040f40000c240601180040d4551a4094001c16101121100d603803900c2e5104000c01398440900544203409220700189071000c024094401800740c05c0200324902130401c007504440910035640e80d001c03400808203c0b22038920190580c044e072182d8481c640c486860b40140c42480066020481c1c00707040040c4240d00580c07000c007840c05140d006089588110600c00b409844400401096030851342c01903d403181984546200c0e034000c2111940400622030009000341a606031800c0103418110000042120590007450070050243c1110200690340c115034480703412504080354072007040310100744605a00803d511610540c184480204255a04520025246d411164069400c1c0c41c41d007141905061010a141101c42c0d00704001d020980c8001c50228141c1e007142c0d0060f410410300380444844000000344e014080d50282c1854a07500c42c0741c0c4100002c0c100c800302c0703460412481d000141980031004055a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 875298606 1250 875297356 875297363
    0xb10020304150e10090801050601031e0b040207020904030206160203130603020904020909010810060509061c03090e0702060a11120c0a11031206041d0a121e03050a0606020c01020a 79
    0xd840e10448041283c4a450103d00f642c3d0100ca621012503690b6003001d02c031000c40305084c0003441655030300c3d4015800c5803103078a04c40380a000c15042421519540342d00c00711080000400040c108401074010581094088a0440243c0d1000d028403e507101d240f108000d481c00188020b501d001c400650340c500025040c401c5405140c0c02154048061383c0780c3c0c050b18000d14024100d0000da60751000c8469403021050711000c900f514140f0007080c2c40c140b0040b8144241c00142064000c04205048811801d0340c102d0294208035001d440400c02c00c0c80342d0200d60044c2041c2d401031005041a020380c1d02141c01c002408a0b64501c10030401c2035a040f00c114050780309050820950f1100c180c0c503000e0b00c4990460030a80d02c0d0303020020b0803c4295910414090003104142c404100c60b90504050200302e000745e03107041c8103903803103082c4a200080707100360780035007151070b41c0703400144050001040103000e10121000800300e6160420440299040e01c00c04005108030f100610040b0058400130307440d04510314024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 875299856 1250 875298606 875298629
    0xa05070302190905040c14180112030507080f09090703091e05120d0510090212150d0c090b030d020d123612050f09061602060d0f0b10020304 62
    0x510b19100144901d100505030001d041c4440d203000d10f05413070740d9090750184020310601890304e02a039041c1405098441c81107010000c41e1030742080300b203c40c0224845000c17400c0110030400940000c3d0030034003401e01008999072094403200113104100040c0801080002054031300301d0484c1c0400c140c0d0f074059802011071410000101c8050a10908000c1c2c160781c0303013441d001c000508205140460b400726120762a01075014411507186c2c41c80d07005034450708400c060000c00c0035020600c0100714501030a510b0303030028003202d51002181d80e0840450510742c009507080d5a60b5411040c281018807041c5050301032032000e425245071500014020384816051402599959801a01244502c0040d4080b00b072100020401e01c1441c410340001540c844c240882c0c14605810704005140d005505498003403d11000035030405012034180300b05500305040326070043c48080410405038a8039002440c00403440358020622980107100ca206682d540302046004281e40a45402034540c04029201036a04000b0603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 875301106 1250 875299856 875299879
    0x305100e060f03010510030209010f0311060c1c030507081b0316030b0a030b01030c0806070905010302070326010911121519080109031b1101030f09080d05180a05070302 74
    0x416420b03044968465050742ca4102808024080c2150301401c8038070031a4503584076078072041460340d15a4244801011a9a00c650707580c220300c0c019019209005401040b0351407032040e100140591003400c00c0a80100c1c0da41c034207015485900c14030141e0b004030815000c0751060380302ea4070388c03440344002805848081c3c2c034a440c28000500c203411a000d000b031700030100a407480d02c07414110302d005400c0c0b200b00c800d036a070a50b00003000b110102d0828495110b80e1281070402d0715120054000c0c1d84011412810045000c1c0b1080b52005070386400c601c0100200d07845401076062400c04401c540303800c440340080d54810702040140a145031116540120391148007001f100d13581001c80c4c1010044c03542e0b0500c21802e00310110740c9080550107016034500070f58440c41305041c08209410000c83e40780010b010708110010128440d4000c0c0c000140013403108000042a0440c0d80751038010343c12102d5003250700b0f42c075001846100c402240401c4e800f00c103a01c0c040c054481d002d644280e5154428403000340142002c101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 875302356 1250 875301106 875301109
    0x50601030b160f081b0f0f1803060702120702040e031611011403060f0d02030f010905070509060d0201111e030408010608030405130507052b1103060307030312060f031208070305100e06 81
    0x1c0e5006e40c8002c42805032256414900a616500602d011001d00e0000140700b041900c1d000070100d00402160f000340840184201e034040c03556118500580e000ba8136040348040d500c3e401c01c002c10060982e1202d0040394652441c0c20b40c020001150450304000000401310048142c3d0b00c104c03604940b0489440007808041e4011644052400c10065070502505a5542c091441074000c1c04106214009890704141c84000708510110244c07040e6800030140d02c0c1d00d900550145103c1c405000702c81088801442c0e003040004000c143c03241c032038209900041010001c03a0300c01d0042a0280121102450903c1e0074400841c500c4100607035204200da486401141000e8050003c41d4008107a5086002004030a0358200c28680c0360213070701d01c60080c68140c0981c80c0031070810540b4043e1400070050152a4a55201201c1d00c0c01033760401d400980d5203034000980102d02d4491400194454583c0990034141072501030a09072000784408245030621040055402010140b4402d89082622400d01c5460b20030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 875303606 1250 875302356 875302411
    0x918050303040503031504110304020105160c0b072609281706071103030c09011709010504050f030c03070b0a0b0a08012711011b050601030b160f08 65
    0x140500103000010901042c0800030000710312455102d0b024843c0d0504a0090000720380c5c890510881d00d00d42030010030010340c03103034004003414003410320755278200c8481d03485003900079225510049042c580016903004020360151180610744c0031113030070811100040c1100b050741c401c030124a403081e60001d100c14416150308145404a524009010408075105c0e0640c0c0720590b4000c8215980740700756400100030520629500025050b680091403c50301d40e00e0100ca0240c0016141c541813010752404140b4003d140c034907091043c1c0041c000429641018200141001507640d205070b003c0d0010000e008a603c4000216088a40d0001607401c09039103101c0e5600042c4203d0102580c4400d2420000403445815080740792402e81c602001101ea0908000b41e40d07090480e0840104a4074040340c190f14158005ca9450351881c203204c40600d410304442e030303d55003054000d80044500701c003c08184107d0807280e415020210009060200381040c1c036030805030450720001d21004c04e400440b6400101d4031204c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 875304856 1250 875303606 875303651
    0x6050f0408070e10091503080318060a02190804120f0314101404020403110603040f051c020601060c200604090f0e0c040603120c0807020a080115050a060909 69
    0x20400d0b10601a1074490016640d102566542103001000d4070100f10a00307540305a20b49001c2c10003207004942d1441da41c41d0b01542000f045410039a001522640441c1ca0510496200e41c00781100160b4030402010215020521400305c1010000d0076000c21001418210b10550800c54034180700c20a00d4001d041203001e4061040116012080f00090040d0740403501b40a5040d071300071981c4218048000c030180000c03401940b04c003822500f1742400700314043c1030500045410a0041406c100310788050744405240040c201c414100040c2140d03040e555042c1e060003c540075000c0380c5049040b4000503240c1030b8140c40c022401c0d0075410b03290039240c603007591110111401000071207000d10440741d0b01841807000f08804680040c81d8003c0c94699101443c146c41560266076002400901c0841424400c0b40c1507901c40070103c1d8010310400045015a03143c1308060000e0141c03000100b004001b000c0319100c000440d502050080540040900450303421282e401c0541d24940030008002c103201704a000c0400c8503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 875306106 1250 875304856 875304869
    0x7050316050a0201021e0a020409050a0b130b131709030a0b1009060e040320010605150c1b03100903120f0c0212040602060112020d0b0a0b030f1606050f04 68
    0x81400e1903040040205000140c00d000343c0a480786a10100500c4051081810f1210b4564114a0b1300c0d000518141e408604264010811106080c505642d10181c4c110144c41c0410b06c00c2ea5000b90a0400c51294101544915010b5a10070042910758680d010301010511894000300702140403251620300304200350307a05400404520160800941c045241401d500804a40d1420910b01003591000d00c0180303030003140d141d40c40303251222040007010b0303031110130b020700c1425035403074103030000f510394a450082184c8049240d80301d549142e049441e07450980e221181300342d49152042c60344003035580844c2900306074500c0c01011504400b1840c044801ca2910604004581e26100f80101c2540c100d6010840c0b0840305d8089076020101038040c42c00078003035807241500503404030700180710305582c0c42890070b001480545a1801407040799140305042600b102c2c0051001e6403803151031940d02e0204240f80726418041c02401260f801481640c03c000346a029180503c800061030b00c103800b010300200c0b0014401c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 875307356 1250 875306106 875306137
    0x5010210270305030a0e0c130c0216080c1003050426090603040b06090709030f12050f210a0204030f1e3302040e0f07051b0a1406010b0a05070503 64
    0x41c02d2402400d02e400a45690802c00e1034800d694421a6000408a1030a80d005200d4503282c1c5503480030401600c0d0480700c0c00c04501403101c2d1a0b404141c010043c40c040c2c19a10080c0150b40e18080c24800c1c03299000303034084101824031040c440400c024612216201e83d0180350a1207540b0880c5801169210f40310003c0d40010000080009112003051651300035a41229070540d180c0320311000300d03540446800050083c1e0701100c007103070019990000180c4034110b10300709a800d0040500800c070403500200e880a40740b0700300000e030060b04110703808040e51151502e10210b0070702e8150703240c0c0c855138218076400522018581c5018101d10815502003103510741d22642c922184401e44069441c9030206c1207036461100503000d041c8a84650707074000d403400d464005141c106265100100e02c3e01e1200c000c1d2070402807180c00c20041c03800b8210a9195002c50310341d0b030010064880c1c1c5241c0700303a44041c000c11692990b000040140100c440540c200c5555074003030b05d0000d40b500c440382015400e5104e5424070780d15204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 875308606 1250 875307356 875307431
    0xa050a031a07022e0902061204060b061801080603210705011b080a05060f06031005010905040b0a060c060b03030d0b0906030a21050c010501081f020405010210 70
    0x1e00d10600d448200c0a41a40c04040e16001c0302030ba903407030720440d8103400c0301045560380c00201031000d815141c034103048001040c031400342d0300400d40326441480c244079080b1441040000f4440d0030301951517001403e41c0d01a140039081c0180c1000c140c00700e0100d50410203020041441d0782c1e401c01140c40c001e40c07100c1041040d80c0701806041c4507580140011161942040c01454100d1001121610300b1540768880c2c803100d5481c4c50b1000000c000081c00e01b94001035400e00c210722902c812024611030310030440d002e42c0c00342c184800908a00c0c0240d008620444c104000724480b82c88081c808411980d40d4107000404091764a4054082c044901ca40360701488040303088a410398240c0c10101c40c42c0000d890f00700c92503c0304003e041c0c4a90030f00e007001d4000e01d690541c0c100c1418076185009854142c40c0381c260700700f0b03410b01000350a40c0d5083c1d009101e41e0340481740076146401d0040c0090701880d1020011480c0c2482d000020f502c4905410314800704030f907a074405a0b036800c002215078140240d210074107032506 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 875309856 1250 875308606 875308613
    0x131e0e0c0a06090b030a090f0b09030a090f3006020f0307030b01051e1b060112030e121902060d020705060a05100803041716030c090f110d0b0a050a03 66
    0x401080d1280c0d4803500000c000041c545004840a80030b60306850b034181c3c50340d07882c1c900e03010280140e000c085560118545000300400e03100500203024500d00c2014690b11040d03298010700420b003541100071171a0000302c0c100b0405c00100c07048440d005281c29a06145591000c040781c2c1e03107001c56800f41c00340e8000544c1da502d81000784015489114a030302d04005031304084004503660702544094080d41c1002c04410301140c01c408001c0c0504840c0403150741500b5590740701c4581005000c0e88030044c00800c01d0304240c10903400c00c889a224035010360341042e0908034800c07450b643c2e5000307a40d100f00701c02c80c4925480554036418201c4005006c105820340d0345e480c2600d0210f60f0b03140c0c1150102500c5180501003400f1181014034001159083c034021801e29050803070700c02c0030421a15010f10750703200e4642203007c1030034130492142c0110f004904038030119142c16158011b550f18140714003042440d0002c02c0072109a024140c035000321144100052015407000854140c0312990403040d170112210b680041003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 875311106 1250 875309856 875309863
    0xf19020f1c1209060516020a0504060b030405060109092a0b03010605130602011a010509060c16030510230601020106030b010f0f0f060e0607050c040204030f20131e0e 73
    0x740c42840700024952060b0000c4608018600800d400101e08100040d100003281da0341150040c0010088900140d5030310000301100c0440d804800001d1020040100b800700038071001d4010120a01f0601c5010019035400126488540f58107040040726140c524003400e0242240004c0d01c0c2c120410341d40c95854180141c8590840941e1400380240380d070002c200e0600c10700900f080300b000010f904203104182d42c01910039401414030150001c43c280300031042414204030b040c080703624200d4014462800d501b0503c1c109099803402495031410700c050203031220003c8014181428200690390078503250080105d014003c41c0c0e20217013001005000204030800014050b204880300802da000c151940e450860280e0b643d5032081d01c000c508003e6040c8601c1c00d11000909904e842801900d07009008940000c040340c02942091714907490f140000420442c0c9480141040e0481c0f4000409914041001038410195080d0444021351241c00302c07040e0b03200c2e80120301f003520800741042c00f140c0d104800300b694 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 875312356 1250 875311106 875311159
    0xf0f07050d0b04243c0c0c050d0c0308070e0612041505010e07020f0718050c0f0711042a120e010e0a06150e40020906030f19020f 57
    0x80e4400020416544550b60040841103050081c001050046a803594400802c1d02800c41d009107d042080000010f40900001003050b82c0c50701c3e1408205410305008080440c020140410300c0b04240715103a46a45210984440c00200845800310303503500e2504140340f100b1555400f801604090000c030344ea00c1c000303421505c510758650840c0c4410012100241c2d03140340d140308080741c0c47c201c251504919201d5400c1b041d0300030b2003800d0482c90700781d4110603041c1e590311032401580da80c407c540810b001840c140c01004020040d0038281c00c085003074201c41f034030311000500b0010f003403100c80c1c001d0082c04c550310b0300680c1c0c807240814000c02000b0f141204580e00d40f0381602c800c40701541382060000518021a5902c82660114940b041d0740307a070769850303419a0b0015540100d010300303690325005448511111900c0b41070400309001d0b804144613031042c05404c6001130700a5100c3d40122075000040300e40040c0203602c04060000120304608580042540840c0c0c83c0030300c17034211030100c0c0c6044c9018001102144c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 875313606 1250 875312356 875312381
    0x9040f080705280b01092004080105010f0504020903060601080712021209010b0406060c0b0621010b01140f07021e030102190e030d080f0a0e030c0f0f07050d0b0424 72
    0xa0f062a01440d14001d030305190024000e505810060214803020b51044c0d0b00881c984000e500d401e40211f00000c07444d0001e90241c043c582d1600010f0040c02144e110b48401040140c5081d03062444544c0003035281c0030004c0c400750400100c1c40004814078420300d145030015040301001c40d0313503a2590001c0e8031074900446441c0307140e60800108480c2800d00d0710805046980390303031b0f8038034454056075034460710360802403d0185d200d01040330100411108001840f006448840000b540000c4d00c0009001c01481c45059030501f542030107928440c120600c11244040d0341141c6990100b081481d14130340600c0501c2c2026090f601c0031400c0c00300510300804594900045480702000d40c1d0045c0c040568500680703000400184040e00801da00c11008100f40d50000101000400d1110104180074603617048036040c2c55180c1e01154507040c0c650030521141c41b4001e801d070080c0c5030b458200408201080ca21800007000301d502d4000090030700038101000030804807000075940d18800b01d600030b0030140c20030320000d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 875314856 1250 875313606 875313643
    0xc08070503010b0d11060318101a030a0c062d09170111070209060303070f05030a11062502150103030801051813062d0e06010b0c0c09040f080705 64
    0x2001c2403401103c0051090382c02000304011103005c0341401000d030402340140d24214006810744800403400e0100600c203a541c802c00054101220700c0420f00c0344c0c0f1b1010401d0094109280c0a00800c24004403070041d1456810144c040743d1070601000034045e0192140d00c0c0d281c0c11840d000b070315554000e0002c401c5500c01d4104100201c0b030004554200e640e10749030b00e003000b102042087c0040c18103425050340180001c06507030400000381c48520385040e4102044034039400014001805035085600c54401e40910001000c0c0d07894000ea401005c2a14240084040c445004d000f60070580308003c006070b9004e80d2080c120711540c0da89030240100500303002d010b00c9661440788000c00c112401514520130103529003002c0b515050f549425000b4041346580021488040b0003004001a8030660b40c43c140c0802d004c001034a424400004d810a40d06070420056014200b0141220308400146c81c0f400c0482101c0c012450740365840d0100794800d001c44010401078003c07900360180480403030403010400344082a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 875316106 1250 875314856 875314871
    0x20c040f1409151b04080109050f0607021617030c1c0201060501050c030d0b060904021606050f011229161827020d110c0106052e03090c0807050301 65
    0x1050780312403884a400d82c00c001c10100180005000031840800c900d00000b5151502c0d0f02c81b0310650a43d4075940042d10039078004021404030000410880768400050300c0509415501c01080c019444060321440c5009103c2c546d100744914028001c0751040c244100c104c40c40640c81504500780e8841105e40c000c055441c00030006002e5000d00304690200081c80301841c0381c901144141c0000700f0400d12296000030040c415248180c4480c40104600810480440014100f51510740190b49000301030090703200d64000100b100250403511404116030041d1089200140d000605a220301d221103808607080c0c1003c1403001d920002014442194460750f41c2d04425494420401c2c4401e40314401c44042e01a00c41507240c000600c2e8495020071601740001500d44212a40301c041692002185a485108001001d003010002480340f80c0c000d18068030025500b20750981030401800c4078400d000030070904040c3e41c0c1042031096021010b2907900c01c200b01581070711161403a60b94070140c0145406507180100c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 875317356 1250 875316106 875316121
    0xf0703051c090e0105101809091b03030504210506070903060f060b190203040905010e06090a0b221805031b0f030406030b03100228030207051507020c040f14 69
    0x70b004103442c00c003008070f041c2c1e903e010140000c1c10702501c1040c0070040c103460a803040c440310100c0b01d8000c100310007000c00c1d20f2415003080d6042c00b8114019800c0801d108030100b00080e0030070180e0703044074a614155822148102000c1b55003840c0d6144c0100f450050a080081250300544400156405030004115120f0440010021146540a400900c900c18882c42000c42515500078005180c1c13441034a080940d940c04842c2600c1007070708908800a441d4040000a0400d01c0074603034804a0381c00309000401642020660f050b8000702001060706402d241010f2200e0660403410002078012421204030259080054480e00200712105001c01188401d504003880024940c00110700709000e54035044c6400e4043e002000541c100f5901030084130390303a000d04000e41c805004005684882119010000d02c2d030144040da44845140526106020720340114400286806601c49075042c8180e1580b1010400e13482d005121111940c000c0c2008408803e14580d0303000507005d901101580031a5865895 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 875318606 1250 875317356 875317367
    0x90c17060709050f01020f1e1207080a0e0f0d0b090c0109081504051f0b03010c1706041d19020f24130f0b180105040b1206030f0703051c 60
    0x703a0903000a003103001c00b4009464001184694414140121403901503c0000030f41000000c001e20f07560005800a54445401c0911818101000b01d28100d40f0340719840d5590000d5008101108003000011124801151111400030b00004002428002c10800c1031602118860701102c62603200d0091040441c900e500038856101600c141d14094403500300004000d000c080302c0148140d0b15031041010040c2191030f0030b4841d5403a0504a070010441ca03548009060944408880440410100249c0f44180f40300c04011660072010480340403849502c242140040c0194104407240280192040010780c1e422600203440e060384280c41c00d07039000b0062001c0000c8000c00341454128088803200341e04203040c07200c008007000114006010070940d02c2d00c111142c00101a04541640000002e9094001e40041b072401c40c2103d01b4a04145400e080051182d00c5000d800d481c40141c0b0400d1000c200035030f0741403000e00c9056031305000712041d8035940d0400d6a910300601007000803a000868201e0303101c0c0e03c983d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 875319856 1250 875318606 875318611
    0x40311010516030b040605040e070614030c04180902090a021308010606170a0608070e0a0509120a03020d06030b1e01060806011706061306180503211c090c1706 70
    0x40802c0b41104290304802e4024081283c2c0181d445031741d0704d1001c5201c0d17645205010f05510014014921981081005043c002001c0840c00c801c076030a000304000e072006c06040785c09a031030303540504010040404038100600081040254000200e00030040035400703541c06040103040a10711052041d59a101c10350807103483e0300404000070100403d8a000c0040e4601c03164000804800000d002a41e60507140c0c00c110064000100000f500e405009400d8120300603d030f04075128802410708204000710701c00041c4246d1007040d0526801189200314000309501c00c800070b54100e240080c0d00c1c500035500f2080005620f410400000c02c01c0d00104e20988101500e620400b01070710f40d20b0229500c2e020029000e007000782120390102040042441201c45404014000d0500d916220000c080302c440c8030314040580d8010314003a60210319800e840c00840c601c4441d00c50051a411030340c4100a0712103000038a200d000d03001006050111171410400981e0440c4102e0350315146562601448020440d1222403e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 875321106 1250 875319856 875319871
    0x2010207060606230313080f0d020f0d0e0d0e100e06071202011b0c0f02060702060a0906093602070c080709050109380418020a05040c08070e030a08030f0403110105 72
    0x61b40940000950002c010861503418003041420050713a20b40e02e034140d9000c0d6903180b41c0e401c0080340c41c030981551b9021320f844000d43c0d54042e20651140e14401440031600b4941144601c01006001207014003511407c00c0448001c0c5c80c03c1e07911071550902c03501e00b00048403000015842c2c051f000001c503005120306e03103204120390f85040c00e14020352110101000c80002c00d80c0c2c81f500030010040140c0d90603004204460198441c00140392074000080d11368800c507400746040c0250014000301c0040c5400c0c1d1030f0124440c45850824203ca10480c4c07900074065544005c0900001c9840800c180e00006442c03030484202c46810300860780c0300c44500003176072400301c4000782015507003ca0303c00b4132511079500381d410480d000c0000c4e90402001d0002d410703070b0030b5100c048401d6040d1505200035402d100342e0310340c043e10044c4e405000001141d64001d146a00c01041b01040100300c220031005c030f0780c3c24407182c0e007410341004045450703090041c4181c41c0701d035081e41c0032004030340c2d80d18403603c4012041c040c0340c0c0305128 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 875322356 1250 875321106 875321131
    0x150406020628090b090c03030412080d1b09090623010f020c090a0f1b020303040f082a011b0801151107060302030601020d03090507030f03020102070606062303 70
    0x80d900c2c034030114403000c6003003070701152070903a0307602152242880f40f0040e0707500500082c3e40c117041c4030440508007022007401074041e800c100320500100b88030100e496145030348001c4103591801900d000000411010315082901402400b41d00f4103242d1104000381514a010410462035940d010020b1503e20b2985101d421892003c480301c625600810b543c0b100c40c000360055501000d10400040c0106e80200c0e114036100d03640d41c4c0c2c07203405443c10388a10868034010103041d481d8200740c507001039a2804002c0c030061131000c410034404204841c60056843c2032801074280c402d098001d00d6512440c8070341100c1241a03610705035492456288080541d5050741d40c81c0c0b641794980e402d01c101207414000c80c0204406200d1201c404860a070020800800201410b45c0c0050312030915400080c10101a0307207485041500b06200300002c904042190300407a988a80480f26280303840c036099019018030600070f071465203041800950b890304841c8407000e0048081d000303800050f000901014501007070700c90b01291307407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 875323606 1250 875322356 875322361
    0x1150801060201142d0c0414010207030b041209080a0b0a1406090403051303080409020403020906270411121b0d0b060603130b0c04140904020337050c1504060206 71
    0x281803032804414035411302480034403000300d1117070b204101c15100c010002000081c03c002110f081282c0c012203400900c0038010711403654441c250450400740015124010b00f01401965a0044521000038454801039510344200c2d41000801407070308031184220541000042501c58107500c1c1013612070309000381452015295510100c1d200e40201400030208208080c011000c15040b5000e0001054101c03009a904d43c214818066904400343c0218022202d0300c01001103683c212403184181001642c0303601c003030b0b5110f0804040282400d43c03c0c940160f001445035a20102c08682e901851500c012100080c050550500c80044924036001c1c0400311900007040d1a80b4000c402140c10080d035059842500c03c960700ca8002104054620901c3c106d000202004501440303412002d02900072141c01109180940109440b0b1115040240c803c4c02112142d1054200d00c1413a502c1481d80290088990070b01e07071038000d5842d0400035202c0d2140d40343c0e20000b0f85148460007200c040d1030165000e8031164 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 875324856 1250 875323606 875323621
    0x9051501031e0303150e090d0c02100e06160b0702070b03070207051c14250e1906150c060b0303030412050304151a190311190e0115080106020114 64
    0x1402e0b240000c03000c0545584414592070603128050010300441d004461182c1440c4c00603a02d495041e100c0b0b88144010440c41101507650019031909160240c24241c0358811100c000507290712494030101001d240420310071080c044000d0b2518824a0305808030b8125a407584207010440c00120f03107050050317100e12824030032401c02a00403403426107401841c0e020100659600e4008090740480d020440d403100b00002d244241d01005460a040170507030650045040107001c00302200e00601042e0b0510f015610105c6d00580e40e40400001c00c1c0e082074000c0404c000120060062000d11006d542c054184852500240343c0441120300880c0d00c4141c480034610320321419100364100038001d68861004512151700c2021500400035014510030310a401a40c00008101114214143c040c00c004007801c0203000054840c00344152944c000c4548000300041d40c6030303480c0400141d403c00c114109000c400040c11034801610f4401401ca1368032000701c240c2c2c031128128203c60761812080c8400c0591004246d09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 875326106 1250 875324856 875324903
    0x1e05071e0c0504020c01061d07140310030b27210906070f0201140406170a090308240a090b040e03120a0b0402121f060e01020601140102031207030905150103 69
    0x848505d10000b050181e66258a95001e10703080050040710004001002061035000540c5401500c2490085045040840c01e000b0490301a000050449908074003040c000c07040090030b440f5040005440b110000d10030340c00c00d900c0d04c402c1e001460320741754141c0c840c1008880e02020f0b1198607001814140c14030482d5200c0100108200744185d06011078442d0011000356100000e101030040c688401031212009200090109802130081e00343c4c515040c103c03400039034031078175064000c500e141812010028060000c041003528007a400e6100c000010005000c3c0f015030089000d800d0215020000928424021a03d80c8640101c1c03442004509001030741484841d0301120511402800042c00c000da900c3c11281d00c0041980d45204016501031106caa00c030b90f030786821015001600d4042a00004000040d40d00c2c0c2c018020380c110b40311040d0120b20700c1c0e4420800c1da180c480500d01809100e003410b000c068014442c080c010ba031a8080c03020584803079021142d00504a036032050908050300341514070043d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 875327356 1250 875326106 875326117
    0x50a120305070e01020319090e0108010912030e0c120c1008011401031107060c0e0402070b06102a0206070506190b0405060109060813050619180317071e05071e0c050402 74
    0x91123805207000c683c1e4071100c100140604272810002418810a0903e400c1c0d096240100d28101410f01c694581c2691020030b0440e81242c09071100018030401002c8641400310481e40710b90440e611801c0390300c00c1c82d405a1081c1c103d5150000044421840c080114242c0364581407815940c0c81c10000500000c100764841e01e800ca01c3c51501c042080424400603099905c0060f0554501c2e0f03d43d000d1010528200d00203c042d0750290501100043c0d0510250001c8580d000c10054044801d0781403000395150002154111503005c0c040d5500752502c002d1000d0701881d18240044081e142c04407102e0b070f0303081c0b80c8900c50107150140c503041242441e00008880b00d03440106100c2018080c1030200000070010442d1a01603508013008404240d4640465000c95400d404544461709040504402213a003212021101c1e01c1411221100307542c4e0301500b912030b6080d50642a6140101c5a030300c04040d41e10070054003040e442040d1001c1e0751081c41d410041c201c000548080e00c00c0da00994104150b1400b60300825 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 875328606 1250 875327356 875327407
    0x709060e102322050102100605031b01020a080403050609061b0409020307020c040603121407020904030804020a030c08060f090c013006030804140a031518050a120305070e010203 78
    0x1454180000c411401c0b070b002c3e000f0107410280c40400140b00b00d68040c011940084001034003040a140780c10700280c0e8a8a03c2c10306040003e0b10094980d50991092003200b038031940048003a80d880d030f907900d446c0f60344180031a031100c0d00e8002d503808260070701c03440811810304059040001c0d003480d0600d007001e4001d43c0050711002c103602c9840510841a1224058000190f00800c0521070b4031505481c00f801500d00003d4003240b0309401c204890040c2d864031005600560985801c0142ea41c1c0ca1010134200d00b0700c2d41010385866001d44d40022903880004030703941b191941d14500c252076242c001038241d540110751500703030104007191b20080408010351605901100241303400501120080c403113030b046600300e41069803078140c001403e002107020700d83d4940340f0206c151881200c25155403141e0b0820107054507010702132601c40848007440700200024994880d0480c0039130300c00560500c0e0004107941d0064003040880e00f0600040c0407540a0030324111141010b030090f61a1501c140d202443d1034604402c540c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 875329856 1250 875328606 875328677
    0xb1f03050709180608010501091512060e030c030705010b0d0201081305011e051f05100c0f06020f09012a2d03230301050d020f0312030709060e10 64
    0x2021060700140840f00d03540f0040008a00d030910f5511407e441050b001700540f58109104400c04544070401001113036243d16400000c15098074000307000d8900d030084410144000300e000d00d860038012006140c180d110340f0080048038010301c18000740c440c4510010f404640c07900300040c0c0281c07106c520031f00d02c58495400003528000341601d503100a040403548085007607942c4101300c5035204240c1c162030141ca03100803100b1482d24003000503500180210350202000f0301c0c43c035039008001192000d1100340364450010340d01c66100c0c0ba0440c80541000e0844e500291008409401010101070344003401e9096802c1c2d40c050b649140c480354540000806100b6042e039031f2076805405822410114404070740300f65a05e181c3d404119281801e003d10300f5041e03900d4500204010005543c500c40c50481066060303805250301c4014000081c1030499900180c105454000100f2066a0b271260702d90007503a031640c03107041a0121180c180504202226803080100d11080c1107075440c101d0040066950b030182e0b8045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 875331106 1250 875329856 875329859
    0xc0a15030c110d09031b030b1303050904020f031905040305040b071415041401020301180e010f090309081009080d0518030703020a030e010f09060f021e0609010b1f03050709 76
    0x10749240500c0242c070000040c2c181c8070180f0030000711006c01c07408101c8460004582c0fa0a54868090621001c2c0c124022421810624020503001e501520000e00c1c0003002103444d080420744c1d003043c7d64002c69a580b0f46035802000c15007240014410781e401141c0641d10300381402e0400301c00f05050b9000080c10344400316951050011108200181581c00f092a58010074500300307407402c4004542d0f09001004240d0050005010321408000840f512035041c5401092486880c50042d00512a00021581071401d0030981001d15410401712000c6132000000c4980008102e6008400c0320034a4400070311181c4204030000b8282070703680003a0780000c080018418000d0720481e4003890b42d030042c1000c03005600f00015200505070016000714031007100b802e20038010034014034010440055030180c0400d0004118119400c82c0c03082254242401038102400d481340d4203250b00d183e42e20411680340040b0b600f012050502403e1140c50440c60008001241c130f0318002c0c110003a8081c2100034504002c000f0b44000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 875332356 1250 875331106 875331137
    0x923061e09090a0308061e010e0d1a0403110109020f0f0301020c060717010f08060f090c060c010f0c05131401022803030b090c0715090503040f080c0a15030c 69
    0x890360040b08107000800d07080c0401d15010380845402000644aa65400c50040c07881418818401343c801d42440d0015403500140b000542c202c4e07120801070034500d08051042c14030000d140b0218041c038040c0d11088009044500c15a0907501d0b0010005c0d00000180c0d412040350920050b02c03065140004d001504184880c41d94602d00399007110034078005038442547c0c84000e030226440d00e01510688100070902400c1c1444540c3c0c0e2840500031106804003000020b02038a0180302c0c0c0d1801101c0109060303524841d41a0150207400800d0040c0c40081c980003c00794094054000c450015000061001c05245000701803182c8008024000e41503001e03100140003000d040f240301070244030341c06640111004403824001d003103400c040440f41c00b95142c40d05000c42c4510804c182c1e813440380d00c01800b0142440120a07040030f42004c00c00101640300109010030b00981182d124015201410101c41c18074010b81c0070010200042d2080896003002c0b1610028094860b0b00040810305c03140c100341806044825 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 875333606 1250 875332356 875332369
    0xd1805060709170a0305040506030a150b120a020a090302061806070305071e02151e070c1d04020f010509010516060c110313120c03061103010923061e 66
    0x11400d07400100054400c3c030120340303843d41c07a2003880f5241c0000e1582030000d540150003446140074161050703c0203c002030b06e8032010f40103c1c0e4460702c07404580301100c3c1d40e5a207400858000c28101080301c00388c48005000e42d19a07100f41c910811240d030381c0c2c0e00240e14580a0000592041c042c20841d000c03221000d420a0b141c1c0740051009038440d54849030f444060b804d041c507160615107a6031044454107002000581c0c1d074082540c2c00019251402035462101006e002c108010850004035920800318000060042522007542150b280380b00c44610409070041da0204540201c4009510044400c030480c1c0c0c0c0d51040e00035002000c1c0606009142c0036103900807c0d085003103000100c405070344030103210844c540d008162001218020b401503040c0144061800106280d6000341076510300064460401d00640007140002160803106c01c00441011048071303411759000340146501142440041e198500d0111844280700c510748602c181d16884a408100c883c03c2d6018003070340c141c007001c00d10040b03503900c84 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 875334856 1250 875333606 875333611
    0xf1b0d061a041a2b2001030b060a0207182702040b01020607020d0f051216140f0d020c150702030301090b0d120f14120402040b0a080a3f0207050907050d180506 70
    0x5038802c171600320207800141070f1655500c00c24002e0703009000030300740300c3c2d00000c0460030b41d5054a044030105a60802c030400921405c020007001404a80b460b85000c1501d41000708418020f80c3c061100351010401603a41d004103032944c034010790041600f00c041a1150445d5240c001040c58900e103881080242d4100c02c100c240c0f080250300355040c00000c8099080b43d501100c940460b19854186081090300d0080c0c0d0080903141d2040030b800003009109200288103c0f5607030a003181d109509401e081c0d170025501d4000740201811185000c0303607204940361964422140075032205009d050402e07800d5046030711182d00d0740c4a0b014403d01c031007550525202000035012105544220390002d14103801000199054030720306a0003260510310502032a0400301e22000a95044080c483c502e01110200c85403600402c0c0100c0c0360442e025400b200800ca6090a120410102d642255006500c98040050350081a0f96940104d502001031440a0300c0b513030040212042e52194403001103000d80c0300c542c14900304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 875336106 1250 875334856 875334893
    0x9050606090a03081b16031403041e080d090b07080c0a0b0c07152a050909040f02040b0907120c05090a0308040e01080f1b0d061a041a2b 60
    0x104503c0100407541c02421880d20401740101682020900c2800325005240030203046805940d0301d0906554080044400400c001c0441014000110514078510b04950203150403d0061881144040d4404d0303000c5000c1d0340b8100300461a00089944106966000e501d05082c01e0140c80d030300341d01107004080f015100e200450b01c000d0383c8484503d08200c05400144d5140940c61402c3c071400e01c2002e855204000c003813211b81c00500350413102c05040d5418002d6801040c3e004000201304810083c01003c0c590b0410310940301400000e8101003004400182250b0b0180000ca4401c01407828440390707041409500c1950500714540107041c004505c1030400c681054070b141d400020104040b0100c000d40600608990300600328403001000381e103460360036031500000899840407041d10942e5030a20141d09007070b4000810049102c0241010909550070402e4501c91454601d544005826a2442104607840208080700762404c260441203041140c0c0c0400d41007068910412000507d580c0344041c2d500031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 875337356 1250 875336106 875336123
    0xe0109080d0b031516020f1b010e010305060114030709051509011103030103030914060c1501060f0c05120d0905070306200f03060405062202120c040b0409050606090a03 74
    0x10070204030410703100c6101c0880d000342e200c400f0b4841c843c0c0000801c580c11820740144070b2401c400f02c0d40200e00c0d00030004103020460240501034a1100c1c001100e005241c0301c280c0301c51007420074500042d003c50700300f1540035000c07850700c40501c5024056040107503400a40380c24600b8400c1e4881c0c010910305040c841d0501e482c3c40000855204568204080540390350001000750315540c1982d40081030500301e4030445010344070311141101940c2c0d440007030382c4210354000c04031030318641d12130110703404c2280070f200c1e1030045007213140090102417280d1010480705030044020a04103552020030320442d48600b203464050b030f603140c1a00380007500c240031600095001c0d5402181070581c0390000d001c07842c4e02071019080310b4820414500030203100782c00e0300da01403c100e9000803240e441802107254158803040421052881100784d0540040640c058000020103900144071a42c5003842d4000a110b58044c0940e1072105001c200071442c1140c00560303100c0b002610480c1001580804640488201d4100302c8500700d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 875338606 1250 875337356 875337367
    0x1808030d020903190512130e0a1a01050c030919030b0405031215010f08151f0e0418120306030219030b07320c0d020607110a0209060409060e010908 65
    0x180822103512004080b1a0740d800060780c694171259268103104554030450804502203800800062188009100c0401441c40ca807800e458103500a212125030400b110b1540e50540f01c8035481030f002e803603002c14074174002c516040f02001008001e58003017001c02400920084d000c0700058504900f20300861013200255121440e480c0504901c2038000c01d2a8241541c001522009a07400802410b40c090707603013003401c129100d040260154803400f80c550354000c003540300000341007140c440e1115070380b24055a400310220703040c0042200352842c1a03156417840856500030b0001c034004030000100840d0381d0a00045e01940d903404254201e09101c010b072407000c0d00441c10011322503551501e0f94000c0745032611200f8200701d141c00c14800c940c514981c080035812101c00d060745560070307030031140e901e4883d0b0100e90350000c202c40c0c020b6842c281291100c0005510f0303850004440e000107101c0380f01550042400c5501e46d14401800020114036401b9a495030320742c030042c1108031003803040d441e00e030b40a030040343e0317461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 875339856 1250 875338606 875338609
    0x81006080c0c070b2d16080c0f0a0c26100e19030801090507170103140129010e0a0308040603020a26060406121509050c09090709050703020301080307031808030d0209 73
    0x176030112010814580c41005888050f1886c00440c454065010860380e84408851000034500541c600740c1d11300600c9a02100410b0250b4000441f003281e0251020001070070301c17003203c264030545010314000142e100e41403090050300d0396001100e800152a0450300710356444552101e01050100094010600301401444040c02c1809510380c0303d00c045c2817410040e01c14000b811a2004140702c040e1007010f698100c54140c0e4000c1d0008803040049401c04491004c008284401c2540c001843c103004c2000ca8000441e98100060220100d90700080c1d0581441d03c2c04c1019030203036002c2d1600c501084092580300908502c481c0d42c0030b116001030f41514016181c440180011180a5000b00f0914510500e0312400260a080001a24150100d01056101c00f03445e00d43d28003940810503d42c4620201c0c04c001d9440d00c00240c070802c031018400d0600c4141c9030410140c00300e1100b03024220154008008070030120f4010014006031a600403103001015660340c2c1d081d81144c0000307aa4090315500001c115505 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 875341106 1250 875339856 875339917
    0x10e031002041d0603190201020c130204050310050907031b0e0108010f0e16291603030c05040f150909110d150501020c150c120703081006080c0c070b 66
    0x15900d19103d9140e4103019000075510074040414410040c0092804c20031a40b080c044001c0c4004050907200c01445054102e4000c1d401c1402aa40213100d20704c50810000610701565010b45491800ba142003030642d01c508070101c41440c008050fa0080310b0300001c907001d450070740900802941c1c000058050111007030506075503440d13100d840340d43c1c811425810000042100501100c2d1410340009204081400094200a803041081c80070f840220341085070150300c850f00c0b0b210030301c280d03020001036440d400c7c2030714140181e01401040d00c000300c2c01881401c0303001d41c0d410803048040c102012605c1d502c03c0c141054403036900014101600205080489041038001c0c250b80c54a5410310100d4039042500003036549640c110518815500440b216805024200403100341115a20a440b901d500b035914443c1190b0018004a0001d0303150800117a285400801401c00c0e10303c00c0e65004000d031120355205401d5006004d00c60401c2c0502d2000244903003482c0000e04e4405941c540002c20100085601c491 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 875342356 1250 875341106 875341139
    0xc09041415010f060e0d02060a270b070602070f021003060503070806150603180307080406090b030f150301060f0e0103030311030708013b1b1215010e03100204 70
    0x21020110040c0483c440c840749080c00c0d143c00f0310700074007150302c418002811b001210340302a4000000003180c01400e81c0c0501c800b0a0349030103da184179043c84003010100801e407144202c4034441424442200016601d030003c00115020300304040f4080d0258002580c80c3c4107210500c0d000c20b0b0341d00d10410042c00d040c080040107243c104003402c002e1400010100d000c00041ea601da104603400400112404d05501032038510301007003000c032510340071940740c00380c1c081c0c1c00ba001c2c01d40410308421000920382394040440340f1640449080241940b01d0454020000100c40c00c01a815500d804005c91741da580b908854000b03044c940c0080000d07514500b00a803c9510307251510514030400c00400115030740000324641101d685989103130910481c0f201c4045e400c40744e00d0300d001c000310040c609070322402101e0b0251400307103400712034a607032342a0702c001004501c1c41094240703009881e656000840301d01d91000103c141e107406040c20007000f5203c00c006030410414802d11114550b001c2401c0c030410014100202c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 875343606 1250 875342356 875342383
    0x9021905030c0f060d090503130b040504050109020a0e1509100203040e06010201270f0c14010f0f020a2d03020a0c080d091e150909050c03040206090907020c090414 72
    0x454100004040341062003401c80c3c21a84503106e81420b810014200111a500300b8940c200aa401381c644003044407651291051901c181d00345000400c030072400c5c0c800c5aa00d0242500c894074120030304028003a440b941905281404c00c400e00410915440d80d1099010004079039001d19a29030a107000f8007084034000e04070340c0c11613240045500c03c3e03906a40440108040a000d0160031740c1c0249800025142c2095005080c94141c07500000d00c25288030700c0e084140d01c01d8859014a210f509403c03a00d141c52000e050340142d05c0b040c0010b01046455520134000014031080000088540800300c02480c0300040840042c0e10500e0384500f0300068581e54800307000d0f0140903100c82001c1e0080108112064003c68144604841000d1061400c00501d00000d01d5094000b06540841600c094414100c612490781414240800200010f003204104c074400c580c01401107040070b8909003844901c0c00000d00490951141354400d03038050f80c44101c0c2c14401e5200e500041a0300740c009200a051514000015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 875344856 1250 875343606 875343619
    0xa0801060f0b04050d0215090d1220070b0f090604030507060801091b030b1801150201060602150a0b06040305062503090f0303020a0315123302090409021905030c 71
    0x14850760780c0391404036000c59012074503055103035540c00701700c01f0f28418082e4591b0f001510064070001c11201c0361110100c404551950350880a0326034500018001c6104181000d4019200c240400038180703025041d0b0a075881701181c28011000e003c41c0b15a40903400039502c1d6400204d04210042d400b145035405085a95010300095000318903011039056140b045806042e03e88804074140d88451111801e81c0c0303030444003a8101d5075501c1003480c4114410030018019400c1c0000800e4090000030141103072040c4800302181992240c603440000d21884440a40c42101044000003164007004280c0c0105420445104038011414071881201341d03000301c10050500b4203030b403000800e50707180001900070f4140c1400740c0e94002914045004145070740590341c2c0250600380104508141118000c44a485100401901100c440d00c0c0d00c206007034181e403e2540e1025042003103800700542c000d0038039003001410200d0404411750000d600103c14191300c90810b00c10007810031036841c080015040c880b41c15201e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 875346106 1250 875344856 875344859
    0x4031505130308060d150c0e01020d020f060402060703111c02160b0904150b0a020f0d03110313170c0c011416020405060a08030f04140901150e0d020a0801060f0b04 72
    0x50680c4800420203442150b0800c4d154046c02280c0c0340c2d1860410300c1003410005801c08007809815002407481641c014415941110312160000482074045119440104600c0d80e5039420042c0a038040c0c0011801c01410151449069004010502d0f2604000c00300355030950030644001d01c2d141c1c1c2c50709002c8207028100420007000b101078080310f100140988002c0344c980d10b2440a66441501c6c0cac0d016230711800000880c9000b1a60201c4c4500d81d4410b0391059807003841c66214110280d440c00c01802d039200c041000401c11b000603070801d03a02c0c2e40703218841c1c20450b1a015080c2080d035810149504406030000300070a2210740c0e00030100010302c04a80a80c0f400d09161926a101104450170002d01407640e0710b001c12110350f01e00d2140402003007142c007102d9442c0006900385246801610640764074110130020b04c541464807402e140d05951942e5031405500c81001ca0880c4d040106454850304640c004003242d025894280c0e46c100a040e103500046102450058001c180015580c484050901d05020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 875347356 1250 875346106 875346113
    0x30f011a1201091d030c01020405040609020702090708252106060203030601033602150315010c0f02090906150d020d171201030b01033305070507080403150513 70
    0x4070103042d6002c0b040001400d44400c100364002c906103200b40c00072840042401350740550150014000d4a2007564184541503507002084280e00403103400a50244100000a40310791140c085170354007041400804912180c007504c881c3e966080c01804100289044160942c401d400310300900048812644c100f201a00d03100c0300130744034040070340003a04042e03c0310f038828000d20014105000056035100514502101000c4d1020f0000049008170300074106443c2d9a80b003811140203a9224822807030314030203d0345441004403a503200c1400e0031140b041300000b40341d02584032410308501c102c0f01c0074020589410070b4054250409034220325984101c08601c280c0c00162102c00441c0c181c20b6111500080d030f10f1a512446034140a40040c541e8000f00c038a0000082c81050720125049a0091040540c001f61140c50006141541481481e078004d01d02e404810b26a1a40e2005030310a80616005080c8003075a5680803481d0710079842541d06855020065185060fa0320542c1c0d0041000050485041d40655 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 875348606 1250 875347356 875347387
    0x1120905011407020606090c090d05030c0609010c020303090307030c08040b07050c041815020c01140a15050a0e040b09010e0a05010b1005070b04031209020d0303090c090b0a05130b06030f011a 84
    0x1800c1d0608c1d0700780810701c1c0c2d2083d140e0501055415510100b9030340c440006604803035076400100ea4031100c541c24600c4400b503442c0003108583c020700d4218065031070034045840035140f51000b0303142150b800b042000001a000002c201901445110f54041c00e0601800401c1009a810745004a074102882c140042d0005411884c813105010b07840c400561200d03100c15840e0b004107000306254085c29911020829003880a030302c500c20001041506240d280d413036100380500603085024064030400180c0c0800d004c504084049584481664004180041015502c0b4141000500111296034603003070301d2034003480c0c00c08460301005030502d000d50801e8501d0301d80c068041009400078080c0a145210701e030100905412000c0090f4000e400980d243d0403603d0300800901500e40305036502c440c0040d000c02c0031240c40c003465880410081203100501d04045c10401900a441a0b6a00555450b5036409003601c031403018502c61003c1202403a110342c5809003100900c030301c18410b42c80c10941080340c46075601041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 875349856 1250 875348606 875348611
    0x3a091506060c063204290402060c01090503040f0f0e0603190c03050723010f090506090f04060b03010f080a03020d030e03120f1801020c1009020112090501140702060609 74
    0x400e001c0782400700d102642804c101101a50082e11001380c41e41043c1540212200d40120700c40d0120343c5124114125600701c1443e648426080e0328010380c0420054078109014080100e85c10b0300005400100d5030f2120302d158040d60245810040c0c00000700481c05003000080c000b4031038060b410303410340740420009803034094814018400070790250713200c0d0030f1011041140020310b07844000c85903881d84640c8404110380624452842501900343e0651555110f0030150f035a1030340645400700329505001c10480980c00c4400070340e800c1641101c004800faa01c0d0b02500004201c001c0d85540d503541003045501d421507103a003140b041c0340d02401d6402d0001c2d81c005a840301d5450940340000d0155228100e0a08520401c80301605940300300c414440c0c03210181c00044c2c0a003034000070504661190046007420b03401081e40c8512190050502500720703510079001501308a00c1450580d1080d003d0003010b00444891160942d226075444c007400d10000d207480c0c00a0b42014841c0014845454880d00050900300e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 875351106 1250 875349856 875349863
    0x506030114041536120e130e0c06040311180408040e07030603021215130807110d240b010302030405101e06120b07143a091506060c 58
    0x182c18861140e1103070f8001c3c600400312281311900e444c0c0043d90240320040100b0b001501c080711280b281d610f24601a0000000c01040034200b00c01215440c00b144d030081c074203400a8042c60040394400501c942c0c807003000780040c40c45031440740725100703051090000361100300102c0b802220300b00c0284004190244140e030203c030041c41e0407070f001c2d6031080811405020960b00c000c0d003004031190f00c61a942404180180d10300000009141c541c1c2d680d07507803111030070107807071029002c41070403c041d50200320789101b0b40c046024003900041300d40402d56102c82001500006444841e60010070030071640ca00b90203107580140d0709203025401c0d4205512229100c43c001c13144014003941d265000440040254102002070807050403c120045d40c402c08405141386007401283c0c00480b000004500a0042c0940c40e20740d607802d0540c0e400c01c80c0072116100100740400c81015858000b661048210340400f10041002d407140f940890b0100d042c0c58185100d081300500449414184003040c080203600c441010300c0740c0d41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 875352356 1250 875351106 875351111
    0x106210e0705130209040b01022d010b1206100b03041a1b160b0903030f13050f160801050702010c1218080a020105010501110d0e0d031106070305060301140415 70
    0x10010304280c80c08499902c03454120746198640001000300d5030150600b00c200703441c1070200c0d1901c4801262548520100256042500000d0404036016410382d0300d10405038200000302c6040140000c0c06aa80c12020020a40c0c00041002a030000d5404008020042c0210180c03c60a19a565000b40e00404500c80e01c001c0d01003000034001907021071525101c00aa003d0300d5070300c8000300f81413504400c0f2242d050380c1d82403624002c240000b400000301c074070851201100c240c0700d0321040d0046003880d109071402d980303920906441c4150160103120b06070040311940003d903000741c6000d0140e800e444004003844103591402c3c80248810b500940820342034480c007500003905003c0b80c8403080c02c03900304100c0a0034042c008101c7d80340d43c94055200724140d58090700e41480501c0356807911a601c3d01c00c0d05580c80040e030102c840340118140340d03001c41e0000b4400d04015a2607661456001d107055412902000029200c901b40003a80c1000e00c1140d00040d100000f141080c41c00d41c40301a03815086800b194500c56 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 875353606 1250 875352356 875352371
    0x204020d020d05101d040f11030319030605040507081b030612010f02090a0f1a03070c061b081b0f0d060b03040c050f04140f15030a0b04050105010621 66
    0x209180c0c12103004002c000410071841c240041c800f6804501d50050b580344007050001e16250100c1c3c0e02c1c2c3d43c1c0c800d50380021818042c21165841400030035044402c0c44e01071009100014100c2c01c01c80d125241030f4040d6900050b00c5140508100546c1c0c030140503034082c0443c6009105460304403205080c10f0210540229590f03484d4917003c0f8406880e21008900f03103501c0c204201c5a212031940040000f6441114a1003e040c0c0302c03055082c40c3e000c0792290385131500024a1305c10501031800041c0d42d1005840c1001e4103220140d44600c0241c404881c0101c944080340078103440580c0d0440f1580e90880040d07103074141991b0000011210340d10445501000442000c14a02b5460a040d000880036000d58076000ea101d04082c60824041d54650041510800489a030f040f0b050403d480707005d045030883c40d42d803180c030b40701c81000c00800346000d800c0c8011480114a105040e407810000345148920607490303107503a45028103120b800c440e01a040082000700c10700711078901c005801078a61222440c0312001a452 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 875354856 1250 875353606 875353627
    0xd031b082d0108070b04080d0c020411040e2e061b0206070b09060901090b160908030f04260703031412010b0414030c0307180f090506061912020402 65
    0x4440c0079450500421404405040100c1c429419904031145401240c2109031203105d2003202d405140030b06412944085040c2480500c102c6040c2c070b0188c00900001a0409000400c1d6a1070b8071a0f08402505007580091208600054003c1c0255401c014804c41000c5181c035525803c060380c92140404010541c8003104900f020302140620742d5500500b80d56480e1010706e000416a40111034010550007007000040748818103010381da14040e8007841a623126030360000409892205d00c0d10309002c00c480c40e034000c038902500700001c003561501d0031111500e032464850410b0040d41c80200c41410314075110043d03031030b5003400900d20007a00e5260408402c05048052011404c0c000e8076540c1c45030000c035000010710b01c42100c000300259042ca00140340f51110260038590340d542a03500040d05940704a808100d442a01e484922034044501320100c4e0044e6036900040644603500300c2500c4c5a006402031103120300e41040034520a1910310003400000e07180c103070301001c900800800a80150b8000418250700b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 875356106 1250 875354856 875354881
    0x30a0e010b03011821050d02160611031512030306060724270309060806150706020307090f1d040c030203160e0901020c120703020106150305090d031b08 67
    0x2451000b60081203814000800c1c00c0c0070244c20340090714180304070140d903449407000c030000900820154480f2403038408410840c0c8002d6000a606080d400740781c407291400039005005a0504c52110340b021a200d0400c0c1e9001054894940c2c441445075812821801c0075400c044240d0344d01140813201c50761586010304040f4a1100b202c812101b440003080c1809407081d429600403900c00141010b01c080082500c10342ca511150503c802401051101c5c604001440c422000319900100107006554000d000d98a582c0c615009154100c420135004820072031044d03030020381a0000d0090a86a402c5e69140040d00072050310503d52654021125100003814032034101c00d0000103540c09022109a1031205030844012140c034003980b507030802074002280700c040b0140280e4a012500401034440600b41c1e03d82000181c2c0300c0b9504600755500d5003000100610480b07542401501541c40219044c504519040c1c01c14100c64151410705240c400740c4c81c3d04000f16119001d00546a0526082035140c1c00e40700c0c0380c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 875357356 1250 875356106 875356121
    0x60e030f071518051b0105360a0506040b28030207020f060307141c1b0f03090b0c09150f070302010501080c0f100e0303030c0c0d0e0105030a0e01 64
    0x500380002540408101102039000641d40071402c2c10002072900e040c402c54981d000d0b000c00790142e80a400c080c41d0138401c0150b034801500050400c18600350403510b00d038480411803009501810510310010396015030f1540ca0482280084481e1002d003414040094054012401800e0327110a010480030401d1910705660000004603100700d00d03131803005120003006540100f608900800801240c045a8204036003a64041e40003600d418002a40c0d2441d580b1150f003052001c0700290302d4080308181c00b00702c1c521454204074040c0c0c00504500c00000d101400c020803034102c1c8000c041c50020b40c0004620090b1b0030701d8100c90550030580d07482040000150b07080d56030b600d080f00318a10020380e00300c0340c401c240001c007a000d01c650000c0c003803a0b07643c00746540c6881c03c2201007600b05041079070301d11051901608001c4e0a258a0615102803890078003c6490750700225040f00800f6000a42d880c94050100540c0300b03d10f0562070030a09095504000074007500000d01511003043e203030484840d0f030000a41102d207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 875358606 1250 875357356 875357377
    0x10e240a02070b040e06211e0a150c0f0f0e040c020f1f0e0303060307050105090303120f0601110d14130315140708010803030c070326041b080703060e03 67
    0x6480325240c24a1848103002a10b800b1f1162820181c0c000c02078811b14441a801005100542025101d640e5120000058040041054020000404c0004c1c1c2540003081500a154400045007203129001901545145088206008640d0401e202180d4055440207039480c003940c3c007142da2110b10b5410391a044104141c2c4c40d090117901c50038104401c040380300c40049054024140b21311191503904645900c400d1b140d054050304010001e002650040d001008004000340c112450300c8140b401a43c0d0702d032400c0e034010718070045507428010030791707440391090380e044001101410389281c4c01c074000380115800b2544905070503030204200c451700e00000340b100c000790342141004022420340111070340207042042c001c00c0b440e05042c000c0f030b903458401d5080c541650650401545941c0b00c00000045d9900314510440801c00c01101c00404080700b481401c80030940c0c50404800c1303091078980303140300c8040d65003826950101444100011100081c00800712900000005480c1c081c0c180194250310803070300c840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 875359712 1106 875358606 875358629
    0x504030812150603150301050f0601020a141006140a0801050408251a040c08010b03070603090c0510020a0b0f040b0f0702100e010b010e240a0207 64
    0x3590400302c4030902c01a91074400d4005100b540c8200e480078070b00d001c0e400140107181400d0085981126841e20381c402d483c034000300006d541b114030090140c103100e9000868a940402070004000381c4004400074004030751100790040301100600d800501901d88110006440300062240b81d0082c1e5005000e945400940b281c00f00000700441003c2d5054610003094600003034007420a075110110620002d000d41c48e06040006244800d41d000360750036410010011455900480d20754156521820005140d414a0070500b000c98a95004660404641c1c0d4614800075000244156920301c40c8031074100d180d49403e01c0c80005603040e64014000a94100842c10b07a008a11500b0760010461040314040041c2104941c1541c182c0f00410130245d54034502d0014a5901425412001405840f00c01e112000b0072121042100c910400e0481060003180101000c1c2c07003800001c4c020900c00c12503 = true := by decide +kernel

theorem cover : BRFrame.Cov 875179856 875359712 := by
  have h0 := BRFrame.cov_init 875179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 875179856 ≤ n) (h2 : n < 875359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
