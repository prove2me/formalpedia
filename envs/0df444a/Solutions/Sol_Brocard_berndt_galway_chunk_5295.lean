-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5295
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:23:41.684466+00:00
-- url     : https://prove2.me/submissions/d3de6705-0e10-462a-876c-74a133541e68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 952158273 ≤ n < 952338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 952159523 1250 952158273 952158281
    0x30d08070305010f0e1303020c06030a090302060c0702090415020910110c01020d1d030c031005041b030209130816050124080c01050313080a02031b4e0d 67
    0x2040380409420310041c400c501805d4841a080401c070041d514014284e0b01d0101d1400c4840c040c050f42000c0e000c020300083c42c0103030300500912840707a000d650941c3e0711300c0c5c2008203901808001a60003c01400401e011640c4000446040030980a0251403c0d01040100300c3d445081d0b24910006a0403101000c4d25650500410f16074030380034805031110020500d002440300c808414650810800c150900c0c1a80c2e80400c08041d0603070025050340d40001140c4124001414101d90640340c081049400011802d1840c4001d82561b500a200c0d01c101d4a8080d03e101a048654804540d000e40400c0300b10b00f5003444200842c81b4500c03c20001ca282108411881e0709003062403142d081071410060103001e1200040354480b090300f004e18210341c89a984034031207046900d140402400030840005c05a03403141d4040300603c105801c145004200102e00c0d04c2441d929880800380d030000340300d88030003554900001a000c6442e40450b802d40c03801010764002142841048507003030001503000046020b5100e0301405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 952160773 1250 952159523 952159529
    0xf0501030b0102060408090d15060801140405030706050411040e06100b07020f0d1a100603060510120903050912071d130b040501020409020d0903020c060c0d050d0605030d0807030501 80
    0x180a118081c90780d40040d56070b0713102070002003c510010540c42070f40d844801e01401410780020341c0c074440c02012130301c00000f00518080c0200c2c035401e144684400c0c81c05215458003441c4c0c004000c2d49030241d50f44842000b4003000e00202c9951610182c0d032080c503980e5000d0b00c0446024600030b040181001911089040055070108140b4642403100d0400350741c0b01100241880030580320046221100d10b4100040d00504150005010407a020b11482c802c82ca5041400d071141d40d1020811507441d1410401240c1c80180c0e0351000840110103040c14002503041146254460b040050400c5590400120b014203840c250404d0380e480244104501c05842c0301001064020455458a601340b10100125100c0410740150000c1803030000318042000941c111402040d070000d01b1521543e0036400e000c0904080c04058005200d9071040b80041c1c9070034401c89a180400400401d0b24481d00082515a900010024041c0e00d0703a48100143c561000d00c4903c100c0704647c0d45813180c501d0300480180c125501a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 952162023 1250 952160773 952160777
    0xa0e060a0605010909020d020403240b01090b04180b04020f12130506040f030c1505041506140f0a05030111090a1a0d050405012405040c080f04020d03050706090c0f0501 74
    0x741003026982000d041c40686100f0340300907a95451311a00600070344940c0d8802480301e621114152001c0030410040c941020482009000744420f2000444182005002c0d01c1454078040008025503400c08200348142e03034866101180c107139004c00002d4201d030081c540d01381d0305e00c4000981d020000c0400392400c1d07100c203181d1900100d0300400d4403043d95501e80180003e0a110001c2d9043d4181030040302009003a0f81d01c5980e24882d0001d510407003004e403070103580880700380d0540f6900302103000071070181505442c07404411185032003404042100c0300510802040e048407607850041541d80f8280079106c0b002d40c5850304c99070341d84902c2d4103001400507150b04c95800f403038000440c145201c81050448815a64441c0302003034680f81c0d42892401401c0c0d203450500101000e0000c0c410f00c200320384002003100e80449040009000000042d6030f030080444026219290460005d001491302410240406000389416820102c06c1e81e0ba82044130080107090f01d10b454400400c204040e84a171036000601428 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 952163273 1250 952162023 952162031
    0x30c1d010b0703050c071206020406080708060907030506060f0403201c0807061d0a0308060d0b1618060504080d0e09060f030c0a09141303090b030703140a0e060a 71
    0x407840514407402075010003010031000141814900d20b040000a000d4061030000b034040040a00e0080d0003540036106610109203000000f42080d400317010114454403010b45180c0c429900c41100300c005050050005500100074440c00822000c004d010300050352103011001e40307822034030725071421419510042e14420000300107021103841949000310784495018441c030303455015525140c0c002d822110309c91903500e002d07642d42c0441e102c0000b45001041d07000e91542d001944036081800106100c01c3c0c07001d4610302c001c0003c111100c07505103040d41c507456036103000186030861034503031000c14071603a020100145e0041030034801c1007414464080703120014101094a9684000410300100c8020511032140580a40c1e01c0c400f628140b01c50141d100001b4107003004d0310340310b1062500801d0494800d0102038030f154005009002c00310140d100c52a0145c8035900d0161400a0060075980001c0c100f0003050b440304941c05900403840f40481c003a8042c1440800c0781c0c2c1d00040600d14083c402071510840d1810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 952164523 1250 952163273 952163279
    0x18030111040b070308101d04020a1a070f110a081b01050315040b0a05030f0a0c0e042307030f0c03050d0e010f260406050603060108010b01140304110a030c1d01 70
    0x31802c00c4601083e41810300ba2135540d201d4500d084000e425500842884c00c4030921000940502c04d640361003144200c461110303040e183e00c213022810b503805030302085105040044070040b580342d40c501c40c0705034490181420780c80588804102c89a11503440280560b10022603044802d62104030301d9024007081c6440381c1540380031503400c100c1d0180004e0144c01155200001411501c4183c462000b0b0000942100c540385080c0c01d260780c0c0d501ca51341c3c0c191180080c820f0b000c1070820b85080074600031a0840031200c00d9100346501465855603400c811840c5c0c2c4100c85d07000001075880a800c0003941c2c0100020b2001520303608040d07040031a4036404030104070707400700304105982c1c0045415022000c10314102c940c80840a120b46803c560914000c500d03814410304010400145401c070611401069007621203590761000700354245c50706c024999020070844100402d500303c0c49400340d41d01c83e02500107006a10203186c045420000340340c0040c1c0303d2001c414024440c225241c0c0c2a009600c1f107490850700c29601d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 952165773 1250 952164523 952164539
    0x3060a09020a051507060c050415020a0c0b0a05070b0702100b01051e0c0f010e06061804030903022e110105090c01020703151e020a02070e15041e021803011104 70
    0xc860280501c81e10b10f10101007090b0b680407041c5c40009502041c00c20400d0003d002c0500560090312510880002c04500b402d40d951000c0341401009070705c028488051410301a10001c0d9801c20f2004004010007400f070303900454080002140240c40c0e0f5000782018000d03a2020340181d070f070001081418014100003c0d102c1e00d10030b40ca4106800d00c24911b103070300c2d40500c2d080daa080c20500b000c011015802c021035844800303070220b8128014201280c4403440c181d50000c460100043c200e03806030218800ca00c0070030140c205114000200e4804c0f240b500702c60349004500b581290f800c596007600192020590b25403450091182c0b0350003084c5600203028030444040000e583c0c400500000303084120103042c44100e60156001002801e01400c03110614400c481450402900704404507001032040e007800290b0034034061034007030050710074203a09031988140c01c042c04042e01d00c6c1e400100494455108040d0110f846101600072440c0b004204610301c03444204041c00d442c80c0c80d94442da220400c20040240c19 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 952167023 1250 952165773 952165789
    0x50f0607020f010210090303060512011b0503070311070803060a0806011532130906050108040201050c10020a12150e041b0e01090905010c03060b04050f0402071a0603060a0902 77
    0x81d90454490400b03010340c2e40101e007009490006064406e051000a608154154022a0036a5010345100014800d624141801e844448041080c0d03441e68003244082c07140300d803004550183c09420702040400314561195071a83c040e03101036841400110a0081d10300d00301807480c0c007c0c03840800501c60765042c91240d50f0300c2d00c10700c13005030b05110300e24034803260f515080300d500c40380c95910030040314240195401c150a140d010b035000c0ca003e95001603002c55803101c0742c400c00b420369030180e47d165410744da96801929198409451003400b84200f0700b011294a01c039000070f0003001c0701d81da60aa58555a9000c040c140c130303100c8030358502d03810000c50144020041d1500c859400f980102c5404280c808040000541400039003042400c0042e80c07001007001c110540040090034420002005100c00291040302200c00c00d010350326490000b0441005030b4035180d1403a00c51840004d0005141001603692200c070300c5510344100782c108800724100641851305005050748895890403e11090b02d044d0300241c040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 952168273 1250 952167023 952167037
    0xe0a150216142101020316110105040308070f120e03040906080109171e0c01020711011d12150411030c010c2429120d020a110409021e0a050f06 63
    0x2d0803090404003290980783d038120326030780c001d000840d80c03420702d02c0303507052074501203114500401c2041c040040b42c0307081407203464415901036a40c9a00303511010421543d0381c00200248003004102591928005201d20130000c4080300d59000b10740c0d6501d0800c0764001d0b80c81d150300c1880750380d02d00702c03101c804129100c1640c10b8654030907251a5545800711a0f440c0480a0001900045a000310f844d034500c2c0c10560043c402c06000394501102848580c004540ca8080f8002914100850075500c440600f07103c040101000c1c048000c1e20481840000d0100c40620112010f035251201c10001065508045c48031901040c0c084c60425410407440e2240e019200000707801c1e9003040c41e003500303081003403c032a84502c83c03a644804584114901030138030303a4034580b0020300c0780d8400c0400d00741c54441d06000007800d400d0319119401821a084054807045000308010300c0b40c0f03812585928070080140d44003080203448000701c0307140050040c08042400140c002542086005050796200d03d20030307640c0e0000351210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 952169523 1250 952168273 952168279
    0x105010303300f02070b010312031104060c0b0a06090c020a150c09140102160e150105041a03040f05031201061103270f13020901080c030f160e0a15021614 68
    0x803c0c4280681c03c00248209500508215403c030008420445480010481c240d02039905008110b0001d040702d000348502e100784d070003240c590241500082c0d00018090351081e00c0b4032002901c16602e40f40d95040d07a841030082e81c0143c20001e0241c040024407105c5950000c4079010801c84180d40800190401086014107111000308a2001400da84204400250b00c9403101c40440d00650b911420041c0c1c2e078090f24074000703030801c0103031003801c41d4070540c00da404a035140d42400d01140d20315800c1044552010b841035604080321190381020400800040182203c1203a41828540c076000008000d034100807520f015a4004118443e10440082207135003500c0b8080c403a400c881da00c40710000b01402c0b031400000b900700c0900c0c0450702c03066460b5070190038060800e0721400020360b00c0003440c500c603200454010901c01200808180c0d130080c800030010030201a41070454050101c1000585441301c0c550102122100d1125100c500036414000d11240d0b882142c44e00c4182420010390654460b400c81060340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 952170773 1250 952169523 952169531
    0x20909060618040615150e040b03030901030e030c0321070f05120c16030905041103040c3b0a0e0a03090b0d0603060f06090c05030c0301090b061b010501030330 70
    0x81880001c1e8030103829202d0100f044503400c0e42e111810340c006e0614441d0100030404620b1400018200ba02904060841c010301462402099000550003018012681122440f06010f0b69440c1c01081000b482c110f040e01100b002403402451000c0c5000000410060400000f045034200c010303041400d440b40c5424100072140c0941d29040f00b0b02c0c50b40103000c401d00450210101c80c0081c1908500d01606641c0265003e02121149402a040512003601c00801075964250108103840505c0c85a03a062000d161505070406140c00c40d07182c075030031068580c0c070805144500b4450602d4a603c41c1c0324866007100054820840c3c2c5131009401c41d0828411110009000281020211107503071089000d0b581c4400100030007448401b02c040101041e00500540d1841c05e00094440d038000c4042d81d2042d03211150051950713003048081e402403d00541c3d517a030454002e0002500b20241e080814400520342000015650701d14200141440403504c1d6507178210301d603103500f01c0100440501b805001801500046 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 952172023 1250 952170773 952170781
    0x6042d080313020f0d03080402120c21030403240c0c02030303162a120c230a0c080a211d0607050102030403050d05010b0f040302040507180b07020909060618 69
    0x4100a04d004c0c0381c103030b106403803503030742010190080c8656003e0303402507880b14500700c6842d5120351342d08000d02440c0d9210402d1807800480021301e4201d0b010001104083d24149070f84d0395148404485001c11b94408003c0c4031152078042c000601c81d0b40324080c514130f4400281c20443d00402c0e107c2c4000340c60f204c0c45420300581145034030b00403641d18002048103901c084018120035a00c00d018135a868003100c600e00c207608140c1c5040d06c42c0c1c510f00c043c0d641240d0070082010f50b04c0301c2041181c05100900c4520700400c0300c1100400d4000030342400800c42e11010b80a0110703a0718101c500d07110050000010040350f9562000013550101d910b81e03c000010f24a040d14040a00015030786000782507005102e503000108100130550701030003500100d03640800038845a6203e8411002c68060340d010703040e807000c085c0000c10151502d03400c6943c001c1c1a9051082e20040921920403102d070040e0012012400001410811412710030540f507802032002c3d020345280e040100c0040c410100c500040092040d030361f4007007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 952173273 1250 952172023 952172029
    0x3090a02030d11010b0405010b031305010f09080406030c0c0c050f0109090e010608150403020d0e2205010f0501030603120c140f0106061103070c0b0a090806042d08031302 75
    0x5044168004085640c00d401c1414010403c0c00450040c98040d420b001c101e0310303981031500032a41600c0c01000d4003815039070307282d0b0f5040c260040784006603001c0d900c51101a045062521400c0d0480703020300b80442d590ba0400202805650001d0511020841001d00d0100814020003800007070b0346003201c90081c2d03020203030012550b4401980040381c04038608036981341c0c0c0381030541c4100101c1d070200080d2200c15505011040305800c0c2210060056004800076841152080000c0d01e45004010940851180f00c0d40007070840c0302c02410700e208283d03950b80041c041210342c07500c1c000082c40246014020141103655905200100c20701120a0150b181025020480640007054800d07200d2411903001c41c01151900c0c1c060310081c401c600124000903030603400c0c00400300846201c0b40e0005408000d09140c216043c045500c5646a4001c2081d0180c004c9103d01c01800902c1c011801200c0c001d81080000041c1c1403030f5400224020482827140142600280c400c0041e254400400f01000604030602c0c004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 952174523 1250 952173273 952173283
    0x70f030e010213091413030509150d050f1803070803101e090b01030209010c1412070b0928080f09040504050102121006090e060a03080c061608130204020309 69
    0x11821041d40003240c002c000e5a9482c41400c11100c0902d000d2040710301c0c1813407440d002c500035100103080b483d40c440c00c000860f0003140100341000c03002d041000210340407900c2d03440982040380f03107059583d15002030003600d04419000d507400003584c0304416000c0c51165001a542d2080210080419401200091062024000e44001440c0f000c80781c500100c4405d954100302d03405030140408071407401c903011070194440e02c291030403901c042c0c4032003210240b95122062000081c100b03042040c070032441c00450700c032039441c0a02026480340c1511007440c00c04503056810301044801241c0e80c2018004480142680f240c0e01000b60703904417000b556291b140d41e071491131340c1c0710360b08070300350041d00307000901040082c15401001e000003101c40d1505980c8a03a011008100c038a442007200241c41c0310b40a0001c030121074906c607000b4000805c09614542d40c0c2d0356809064100e4a0046400e402000030072241664680501c440e0009171b29020b101342c509201c031000011050f41011380159030210002d462a201044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 952175773 1250 952174523 952174541
    0x4060806040c1119060f1e0501091e09020a090c051e030610080a20042102030615060903010f09020a0e0702030a030902040905250b0c0a3c0201090602060f070f03 71
    0x390510003078000707c001da141204d102d091170600780d241070000903904190784114206030201c2e0380170341440e2130581c0340c40e00075100015059a115554a4001800c0c101c640300300c17601e0f05000d072140c94a0f002d10003900e9014640031070590005413410000c1251542d14003654507445921030070808000d8441001110041141c441c500da40c400034044160714003403a0344043d10490300c2e03450081d4103900004d13441c1070f650702c040c04009415610810206180d420954074030711080c98013501300c5007040c81c42c00020f405e68403081c0f2210101c0c0d58603e03541084d401c0500418001c4c00c00c62000c141d5a0611031030080d0750384100907041c81055500c0200d01d08550f10358010750081034205046031404080c3d0098000b0141008aa80c400c41a50400c00101c2c81d4590f4103440d01090032101518000316152144c07541141c0324202c00c4c405280001c200c00d45c811814901c900510980000888446441d10025007010841c1d001101550700c44010441481c02082140d0fa00000c146000d01b06240000340c00d40141940903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 952177023 1250 952175773 952175801
    0x705120403030c060e01021305042d0605010e01050a0207060c080f031918020604150504081b181311041508061506090112021e04060806040c111906 65
    0x260010038181e100f020201c01a01400c401c200030110503140750300301c2c45a045c107400c80218100701002603250a80c41928102c08000741c150200107042042d50201040803951508256107150512055a001044030340c864820308000d85004090310010b5518a4140b14031400c2220b45138842c401c103d00041540d00c03507441508455120b05061120500119901a0420070246422083c00e106a952015409220b07000313406580b600b410000c4203c0558000000b440501c0f008200000740e80c01c00308080c0031112a2082c1c23034180c02d0544020040400f10072614040f60f0750a20060040c0c00440200c0442185d610031100072000c40c03118081400b40040c03e003200040ca8180d00c0c0051a4007011034080d108070180108948900e907040100070b214002c850f07403140000c503042c0203561040380a038018500c44010b1260561940144c180428031544583c01403800110040c044c801142401e0003903011400b0036040c914050b4100071602c139a200555020104c00d041010028024010181d1109103062214 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 952178273 1250 952177023 952177027
    0x1050112060e15090114091c0810170312010f050a15020a05060106020d1202130506210403030212060d02030c060f0d1506020d020705031002091815270606070512 71
    0xc0a01d050007403420050b941e00407401c2e80c00251141c0c0d404501502140b000403250444450225400c0700d07440c50003440300d0031407542b178000840c0d050b052035489070380d08080e1002540d40324982e044440c1a402c06130700509001050034070502c1070350b80c0c40c03031540152440885022440046800102c2c6440421900901300f400b0b01c82c00441c800b5400701d14001c0441e02038036042010f031498110709040b40705112410702110040d10041c4103c3ca404d00050074071007100c1da0071010034101c03404c1c0d52140c0c1c1d0b41540c0c02c60100350b001580c009aa030701075805c5031b44094110380801002c00240c0100b9140c90190300034a11552000808405040365103040d1503144100380c00400c440c060084000105178000c1c00340201500c91945201601880003485030b098620290240030609800100701000c2d4200405182e80056170f640503012844940d802140f00703145400c0788517640a841000c5c000010621504902400105149480000340b203075081c540003841500d480307550b6107407402c0c840d08014011000d80e80d20040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 952179523 1250 952178273 952178281
    0x90903120509060612030f16150e01020a090518060609130f0231051c14070306060503030405010507081305090c250209060d0804090f1d01050112060e15 67
    0xf840ca44034060071345038080002e00f5015540c2d80d03030081c01410004204100060b016020b044d24100c55014400d2030246d1032003d10030042002e80d201801c0140480c0c1d07020400310700c0182d103d64844000d10301681c2e80c69030b50514141c00305100000815041c0160301c0000d002509841e8071840710790003081c3e80010006001140701e424060b43c4909842060000880761803a08a2888480d4a01001d0507010100c40d0328644814060010081c980f140f0341102248861004540c4210541081c0411003018002d940e04618014084030381c1c5400c4280207900034082804243d03000b000700e071180c6400050700b5481d500e16403000016030401d80c00c040c0e0001001c605001c8a100b031100034111010181082c0720490300c240500403142030300170001070341c058200004163b8600b0048103407034046003e803003424a01030b2100304440c103491030000800150782d901e040452603c10020811142c0d8030641000340055454081c04680c0040814000f038000c0fa0b45070580142d0711402c010a8030216940d11055200c0c0c90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 952180773 1250 952179523 952179541
    0x1103070b090606040501050d030c02030c130504030207060302040623301f050409061508030909090111030c0a090905010e011502060103080f130305030304080c0d050a090909031205 79
    0xc058078241541d1140601103480c1d444c0c280111410784a0152000c0c443c22403a80b421683c00348120420782c0c050080c904500000c2e00e5241086a2000000c54042000e040614000345040119030080d8201441800300384021540002c0c605c500c1c425100c410300141e007201c10098614840c0d8210358190741c441ca0004981746082c06011958945446161440d41d130315007074034030311540700c1025242000808100034000c1d49031a5010399900c60090100181e541d11104110003855040d4100c6a5581c3c40810480c2e03241c42c0c82c8006c150b101405c0c900900401540580000c1c80b80000b42c80985000703800300c0d03001d60b02407040300e0020081548180a015950352800b042e144d01030207010344588500318030b07914080c00e400003076400e040b82c0d40008005e14055800c002d98101741c000120104165410407000408660100051800346006420360b40d079501c00b25045901e00140c00080c079041c840c0030b00c003409881e50002c10300300441e00c00030310105061203e4039045480c2c000c244141d11044d07152000703101e0000c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 952182023 1250 952180773 952180793
    0x4051201151a070215070203010c080a0c02071d0403050c010c050a030c210e0c030303040b151906030510090f200f18011103160204140f16110307 64
    0x99149040c9248030361682c80c1503040082c05050700c1c9250030104200700050500030b0010014003a40025a41806180c0d80003909480000d016000060345000601200e1402880742c810150340318002000c04915103401c1c0072740c691503050760041030b18a402c00101810301078000c4550050110008000c01e481000010303080b0b0f0408074056001900c1e00c405d0280c000d000d404440050380d0006103070b20410344403000e136802501c0d02c020448114050403151240c0e5880400146001714030902031960641350134880040405400080d092040d1607201d4183d01c46030303040401d502520740a2801045a651700d01c040224614240d0010301403a290251403510286130741e0001450854441803000c107a80f941c50040f006005100500c040042c04215192418402030764524408406040014035500240d01d59800c5030802e88442520f41200c4603184110b103058407400403d101180003a240d2400c02040300700303004000910342204400d515500f6014070780103280c00320a480b0004200d0340d450640d403030800c20007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 952183273 1250 952182023 952182041
    0x3030a030e15010b09040509030d02040303020106090f0209010504030f260d110915130b0f0304060c022d0c0603070f0801240c060f050f0412031401060c050304051201 73
    0x707800361581e60b410b0300080c00700075812074507800300e03ca0902582034100401808041c1a842c1144020401609081040c0c0082c0c001940a03800014400740380c443c580040d61100c4a55000003481004004034076a013210949040d80e410040b900b0b0300100ba0301c3c140804041a03406502ca2040340c0c400c404800d20550020410a811130405014200c00050b40c451507004417040344e03901c01441450043d07a0042c18015000b004103003c1255a001e07a20b2580c1d6020358810060900002b000104010a019460280101043e280d100030180059031004c6081555180d1041c524205100305100d11904410081031014074001004103559082003800130301410000800c2402184e00c3c0400001c03901055000210000508204248a94500107049078840d440302000c40314241d0360200c1e80d80b9401c0c5407180901c5001c40205041c0d40e030030241070012602c60590803030010541400c0e500001405412109411200d46082c241180e60341840e0a034114001d40d04981d0f08941081c0c222080c114054005032f040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 952184523 1250 952183273 952183301
    0x5120412030c09261203090717070b0406050705011b020d1101050c0a0302130810020d110a0c02060309150c13060207083a020d0207120b0a0903020c03030a03 69
    0x81034242c5040c0c9802960784604500380403035528450719000c0c0a041e0b0240841004107440145040c0d8125003090380060702d0000321175201e5001400101907840000f4038078100040100840743c0b500030201000d10841c0034100c104100816001c080000c02d40000440510507540d610590244120003940c44040c1500800080c440384954601c580e8103206460040d0458141e00d864411307403003c10b81c06036110314440020401c3c0c011000502500030700c014194130840c4900941e070343c81242c202000340c0d1540e89401f0070210040050890854100038441d40c5654141e81c502e403203a40b003040aa040071400c003c00d1306180740c1d00040042c0307010759000038000012032100c2c0d10303103454664000700d81e104e81034000c1c006260303c60000b2200c0c1c255040760070380030035009802000042c00c200144a5400100140980c05a805114252119501480360001030400f150f07600e00d407070b211525209500d0001030709129400340d845d00d840342414400e00200c000310034050100d03940c03003442c100020300820b903803c04184 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 952185773 1250 952184523 952184531
    0x7050c040f0b12151305060a0e0c120f06010e0f070e0102100c03061a190315120303021305040e0304030809041508070f090504080415021c050405040608010204030f0b070512041203 79
    0x14401190140317100d120b600324000300140c1c1d603805518001040d0340d0900011f6403094078103c98095942020440030b400004028003c1c150003030384038504d0322006820103044582080c0c1040191040c065080b44e0101070b43c540200e84451140040c0d003055888602c68184604003204000040d805800c01c100b25036a46a2009103051880d0f4203074003502811440c0202c8512406904078124400e030060121511840d01ca4031415076a100c0780001405085000ca020940108001c4c9262040e1172010000b80740680e028009084000c245649074070031404001e205020100b03441c0e9407500c80b0341c0015548111403152100f610749510b0056a00ca01e02d1048a1a803010880085070706802d601410340980c0d88040c01d80d0520342070810322400741d40f0b100ca10344114402c4003280c01e84140070ba02d60034250f01c0701c0d880b03160b941e60400b01880203840940d0843d0381e00b41e004120810000e84140d410100c4680c1001e400592512600000c032810712980c0080003001c081c1d003090005020065411f0807030b003003840d28104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 952187023 1250 952185773 952185781
    0x303120606050a110312010608060f09070f0c05070f03080c060916033305060a0501110a060c200706030b0d05120a11060f1b07050c040f0b1215 63
    0x541540c0050260600140702409000000b5020310610344406641400342e17030a04250305c2441801c03490903848400024005018840641031854488020060030b0b10003200c50702e0b0180000e050003071800740c01000c00c08008404024000188180d41c0030b003941030810000d40b03a5900b072507002900680194087c03400b130b100c0490b04140000070841c40704600da6180c0b0580c05d00d961100c40303210b0350700b890300b04490090308100c0700082200c4181c04c2c1a42d0100400203058181030080c01280000b9800042c18000350b01c0010420000c0040c0c0701541c203500c2180881c0030b150f18401290b008400c11000d03c050a50703410b0f81601f05001117508030903940781c0d40e000c00c403040e407000030000d0249004001a21a8200f4400f0552250347e04c03004210f41e021609040305c40c0c1034008007191920a04684250144e0b0340700c01402820582a18526140101042068101045521202e84403d10354072524030456542c1c07080000c1392040d400c24030000c41d000b042503010342c6115400c0c81e00c1303140410400c0c008020820002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 952188273 1250 952187023 952187057
    0x30f0215040807060c02040605030105070309051207020f0f04090b0c0309100b1008041112070503010506120d08061819111602012f1510030b0c03060a090c0201060303 73
    0x2480494042c1d00082071032900e00380342a10400e44808044c1c0e00180c480c20b0120355078509015050050b90150390009440005007030480c145505a810005020381c1081107101581d47c0052042e0b440c51b003102d1410084625800040007003001c0d10380100803100003810007038400e0300c45010b5072142c06030700103444540d030120b0b29040483d0060000c0c25402054881d06070185c0b40302d0455250300a1007100a0b0840b01e1141c40014107a0f1310104558006034001c0e14180040d04080c0a404d421000640d8094480081c601880391601c0740c121090003040326200c0083c06543d142c0c02100b0f210800c0d10303e44c07040c6060440783c84524103604c0f0407071303e151400c25526003030780c02d00c140454451316102c03004141c017101740b075004548607860305100b0114403091030601c2902e0b0420407600700203e10b80000908840d92381c2e620006542000408180d03071154890020004600c1c110105a4000222440340d5500d541c3c00c8009030100d8403c1d004100007030f1812410700300701c50701540883c080c0e034000d40350071000724103a03030701c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 952189523 1250 952188273 952188277
    0x4050a08030d06060219353402060c011407030207050c0a0602060a0c09091a100c0c0905090a120315081c0503041403070c06030b040203100b160606030f0215 69
    0x4007104201c4099401d4005c90032500b40f107000c041e0303080c01c200344490182481d12000c000c2c000303003542004400243c6074842000420b403c201007100e02c0300c10108800741d0f0041a036413442c110300a4010b04000be1030b404501b81c207500030303035484031145900f4050b4241010f000700207410aa00840ba20b100d4640e60031058600402442d0813108164020450740e80c0d805011400f600390402c602082c040000d00104820685001d0702002d8141070811103000803a1f8010003544028030b50b40c10061100428150000c9541d8800d464284c4202010115281d241e43c08000e16000c090350003e07050440c1c010640c0d003650340c1600164205102e03075010030201a120390071503403150f0040512040d1184030064102c0d6040c002c070040c540c4103000398604000d0040c0c3304904d80c11079204100441d1821208141404950381510542740280e00c141d500310f0541c07602000c2c481c03c41c003072401000e81400020552000e43c0350a0b480c02d00c181540880240f15403682ca14201c0400c2e43d031a80101d22800020440684455140c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 952190773 1250 952189523 952189543
    0x606090b010e03120a0c14062e0317251511031503120309010f063c0b0c0a02090604050702071806170606010f02240a0204050a08030d060602 62
    0x2001e000c4d803400304004482180e00001450007400320305244480850701020084085402131806080c00749051850344145500440005060000355036134907096602ca10305072030076a42e10171140601d0542424207601d0718010400e0030310041005845551181c41c0322003800130442d110702025824480e11800d008191000440b50102c82c080070b00c0080d040c814490002e07100c621000e0151110b5011504920519138030480350034000b607460300810300e00024544070f040018900913210380c43c0031184544040d48820262007070701c611100145455030402c81d400101c1c00070590b041c0c4207a0303139040281c40140c98414194099204071022000244982800c0c010540b14201c1540641712090410420000c00c000c0f00c941c8400440c0d0f04d001c085540e0113049044600509084000c7c0503038641200014040f5030240340800441d00100070400401c84004040152007980b0001003a59a581ca6107200090246500680c0c0c0f140d13410b1000509083c001c0000e00f1b0070300110b5428448207859800903650b5499001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 952192023 1250 952190773 952190779
    0x6170d0e15090d020604030b040305130618260f010603110d0c0509040501090221160303052b060608060a152c03070b1b120a2106030606090b010e 64
    0x2108414925200c038503c01c1107480201080c0c14591680c03202c003801441158100c0c0460360020301250500b6041c8410300003802d00b89049680c00c1c044213001c104000c40c500c80d5801d40c40b00380c8010820982c0003010080e8040d02402215444081c108900c2c0c0070f802148800d84141d03e08040c3d1405600300070042c0d030740e0070381c000300c2e0800c070380c3d20b02018001c44410082c016a82c1e95079960000005aa400c2c002c519070140240c650308121541401403820f10041600302031408400b8201040001d81100540c0d645800d0400c03546110b2000302c1e108400204a082801400c3d4540003010030400d0304181c3c0c0314040c503000e0751014445601c5414a5591148013020500030500c03083d000c0c4000320414054140201d4010302d0403001480d504003080c600100d94000c0d100c5010003141586103c10100c002d90f9181c505d40c4024000468030305c048800c0c40c828494180b00300700c402c2881510a0740c200c0c1c0400090b0300307144820400503036a030904200401190194401c420304080f00114550b00c5190700c0c0031114801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 952193273 1250 952192023 952192027
    0x714090c090108040507090e030a080f070c03030b01050d090c0608060a0b0d1d0313090507031a0d26030a18120c0c050402040311180708010b0c0106170d0e15 69
    0x7210054405072402001100c03640724100003c140b180340b82c09042090300c02c00340119120280b1400161481c030f0000c2001d05041603103400c006210780e0085080302e40c4c942504000890701c10301c40041300c0c43c0c483e03100290301690503c004101005100c050130011190b155075208203030b8560004010f0900000e110300011603400303004079401c2c20b180c0d503c60074042c4050140f1600f007c0020940500f56000480120b0301030050000400c603a445038024194040030034541000710501c064032000d5000c80e0700040c00e01403158100c03040c08000385803400c07420f401d810b5542c075803100f001070042400d241e104030351700c45034181400340c0c0305036807407110440195083e80f000505e61800c140c4c040c00c481e0140c60000c261039000c1445030008a907100c45c40104003560040d2114401001d0380802d00101c585007003240c940303031498007040001107070303110452a0640d44000d1f0b003e0355980c60890000e000d041240c0098140039400030300724012210006510400c602c482d242c0d0300240700b40c1d40401628800420b17030000c4000003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 952194523 1250 952193273 952193287
    0x5070e0a031e12021b010e10050c0115121103161e03020a0b041a030103020a051203070606180c0801050906010c02010210090b041412180414090714090c 67
    0x40000e0b50000c00555030500c41281c3c0c4070045041c1981c0920000758001c41c1c2000303480d400c2c030440c0744e000d07103000c0c01d2905105103854049941a08450180c80c100316020501d0381c40000290025440c808448101d00c0e00c1d19110403640c074a11581150842d03101091480c010b501c0c0c00d011501541d50100b03983d11500035840c200d81e00007490244c142c05d11880c00e00607000300050ba65109a907000e800e9801040da1501c1c01c03c0c24002101c3d0001d81c41400300b0328140010801030ba1252590816100c055a044980c0081034000c0c03851401034000c0103108504101002c01c40c441310900041841c100c44000b802110500c2d103064170030550a00130590807850200008109500404030303005c00038411310490350b06682900c407001c00c0380c9559100326042a961000e210505c01c3d0000f030600c004a1200140004ca50140302c0c1540d14820440340340e280c0c1d80b19900d040c00507612907000d5080c01800010f80a079910305034810740d031079004500860f11070700f0303018624040b40c0c06e0418950780720b504200316052800700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 952195773 1250 952194523 952194533
    0x1002010b0d1e1407080106060c02090705160c030f02010305220b0711070803180108091f0b030609011d07033207030602072d12051e03010905070e0a03 66
    0x7800c120b1207180050070001600b52100d4682004811001d810103d003001e54450a50340c0742c1d03111030200243c070314028002d60740e5440c202da00700d061030405a0f940c11062003129001d0306001405400ca1425103030000901c644550343d4100940b00f640c00300181da6a07419410b1000d00d00104056007000510321210001d484600c0c015000350140c2411680382c41c00350082c502d021410781190507140c0004c210420000300049500d1401002402c0c6400c0364074000c0503265031208a9000d8842071074180350007140151700d030341c802d040025014060b6581c5147c00307a4014040c04044c1d858100c0180400072004a41401103190020340e230380000d50081030700000c1e40001d540f400c0d5030350454441c525401156070280d41040791900440c0701d5a00581c40300c0c480d0400c0c1c1400c0c0100b40007000100c180d60001c01d1184100044100c00302c0d44420b0b036000d0504810300486482c01031140c11a00780c0c1e0b0301034000b13a2160011001c1c41c1260070481043c0081d42e1131044c104c0306070b8001c030852608100003002c18400070b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 952197023 1250 952195773 952195793
    0x320070302010f06082d03040305160f0b1213020d0b15030c0f01051c050f07140405010822080d061403011127091014030c030d032301080c1002010b0d 66
    0x91302c41b00000400c0100303101040c1550700a40c404c82d02c5038417001e0079028440f803d40510380109820007100c0340480c908026000d851180c420318500c5c1c0741450b00081c00c19500743c40c800300d035940c018290816000991034071940300007040e01c4a403d40028905003100301c1c90f000601c182a03450141ca030600300c03841e440056403a50440d03664280440d003005814912840383e07119031881038030143c0c145969070510100250040e280d0411045560104100510450360000c11107038211030000b15002a0b281100000142c1088005e002407100c0d0300010b688100d51107d0304400140e84180004800381c2c260b40307080600322801001d1402d01c102e801c0c440420450801c002401d503500a00355162801c00004002850918003199403031130064041d40e0a020341080c006007078040400960060070403124810000f5070303580a0031445001c00d078170360720f0b407003100940303160b024042c500c60001540903075031510182d90b11880400001c0340104c003507100c2c040481e4030500410484110140007404d119040d904c0325a515 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 952198273 1250 952197023 952197073
    0xf0c0f1f090201170405010903140304030e090402180a3608030c07122604050c04050a110c0703110618100c02030607030c110d05040b0306010320070302010f0608 71
    0x8403c05460b640c0803132100c0c143c203522852080300001420400c614010b01200350580312403402c00780078002c0000080d0440c0d07190f640603008031901a19991503100040c280102c050001136428074641c10b10949000c560007a261084204088940280008116492410f051507041d908007520031700050200300003a00464100c1c0d0b250001c14580303503158480c0c507481d0840c90440700020342401c0c6698a042d10514032065940c4225180401307500341a152503980f84602c0000d544a55030b220041408442c040d4000030b20042041c00c03064803504151001e54843c2d030302e84003e46548034102c00030344c104c2c40d020048401442c800035030814128110030a1044050600d940380042c030005190041c00350340c01b0000688102210703a00801e40da14a1000140001142d180c5000c0c01d501881d000290581c20000303850540704e10800c1c003500d17a0344410040707024107a1041240d000780380c540390111413408880f0080c82e000d40243c00030711807010303907030364038421540d443c45003c10076000700480002d0502440105400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 952199523 1250 952198273 952198277
    0x18060e0d14070c0b0c0a02090903090a150c03030c032c100e0a11040b09240901050f091e01030c0f1e05090915010f062706080711030f0c0f1f090201 65
    0x1001ba2141d000c201c0e40c000540d490721095002044009582c030b854040c48009d0640e2404200a249001f84060280062500000c0900d620741d00d41003441440b99010b14001d40f02c00300034000c03003034040d080b040c5075640320946012180242c41f07084400c49083d005191084070a10002c0218403d15143e0b05036400040e05510351060f1540c0300040381c1c3d0b0b1100a131500524121225408071100312400048410b0300440080c014009100100140d80c3e4101482070103240a9807121203640c0d9100148049850501c01070f10a05003400000c428400314215031010760300d180c1b4098203c03d446030352480d10122044a800d07040c4480c40001c0c461400c000d0138454108803294201c1300454480c03407804907650802d030007204001000036000c100e05680011010700131401010384900080d02007a550000000034056034060080310700c042010288241c401849002100d41030300d483c0e148400f4080c416900c56a81403010f03204160510301000404900c2c0b5000c020300a00c1c501c010140f0500d41390107001900c0003641 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 952200773 1250 952199523 952199533
    0x30601120309030c090222050108130f02090703050601020d020114180c0a03050d0e0f0f062d040f14010804060b0d02030708060405011d060a18060e0d14070c0b0c 71
    0x20004e40201d0b1039201601e503c080140e201e001640b100c0c43c283c02d040c03010303d20340484e9000421050341c11003040354200c01120083c19030102241071540c07800c9502c150080d0031011603410400c003540e0561141e80a000241d007941c144a11b0320b10101c1c01e0f50740002c200c580d0700081e00c4c0400c2030040302e802d465840c82030400030358039000506c40004003d292140c0c4140c803150445000440c5240e0b10640841c010301d4122a0442c1e04a03203500486c1c444945883d42d10b02680b00000c00b07222501c203880400e80c8694000c0c21804034041038500da0015904644680394001808500c04640034240c010f0070002010180e540360500e036a0358440402500c818072849400c4501c182100001d41c40510455001c0e0083d40b00602c00d41c1072529006007107400300c50f600240c0d001860000020210040342319038005280007070104203650314510042e00100b100600414040c40d007001c1486200340030441451880441e19502e11101e00c15001c0e1140303120f0f0b68001803020740c10160500c81102894090040c10440f6400c941c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 952202023 1250 952200773 952200779
    0x11070b150a05030d080906180309060906040302090411090601090b032410110d020708070e0627240f04090c03050111120a0c0903030e130218031902030601120309 71
    0xa080c0300003044040d002034805000c06c2125001040101c2c2c11400741d800e0042a07400003484207469002d040040c40c400c14000502c081c03143d45400540d0055a0000c1004440e814035103402c1a41841b0355400a00820345240054890340c0944400c008841645040b1481c541c0c82103a00e00c0b00504211041061100c00b608105083d101c5241c1c4503ca0200ba45500607001c010280461500d070703102e040c0c84115400b408041c014a28041814411030b68544030b4400207072149800500c548a00302c00800082e00280e9207580d01c1498400e846028010b0118698a02d00b59120714007001001d00302007039000401c00c1c0080143e03092641c070680045000b940001c030180c2d1280c0c0c4041c01c0d54a0841c2042c0116808241010070081c074840003500000c4000b410041c000754818040c0908000d840050300b0300801481000362501c2e1347c42e09000000807000c0c00c6590308600302d0b81c08c4c007200000c2c1a0074080e1058017110b21030603500f0b0114014064005000f07081c96841c0017244580300c10891812401c10800001c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 952203273 1250 952202023 952202029
    0x1091e020a0806131b0503071206060902030a1a010306210302010902060705060414030a0215071e09060905040902030705121e0c011b170a0302070f0f020411070b150a05 74
    0x1d540581108070107080e03000b20605001180408010010030384035407505040000c1d0347c0016000048890a4141c1d002a2026040600040c00c080d403102e00c43d04c4c00003003040316940b11540503070320007915095400c40394907d6600443c110360342c90040702400f8001e1100d4551451405280c481024030074400030820781110741c0480c0c000d030000007080769941e01440c103000800412401d910100700408004505204480c0c0b4029581c1d4610140d6007400409900840c4201e031180c0d240a0071300b282d80b200e20824a13170310140181924410302c200c40c0061481d0101060524203802200c0e03001d60024014810142401c04020603030600c0034418010b03114044520014180c00882c800a02c80386101411009500c0c0002600a1400c1c4840d5100785009038865400141400003151281c845404d41d0394581101c0c942c140c0081c4501800500341c820100c095404000141e6284140303144292000d0207005110b0014072218091600e000b070124801600140350108020b04c421040c1034024003420b20160ba036004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 952204523 1250 952203273 952203283
    0x216020d0606080d050f1204030c0f14060603070b0403060f14090703020f060a022d15010503010e0d1b0f0f08120c043c060807030c0201091e020a08 65
    0x104555042e19800708010400f01071007404208200343c10300f140703400c03001d10034404a8801c02030090034440c9500049010715224120b05403440d54406140f031100320362403c0c850031300d000e9101c0c0c51207036100d03090000c4c01d90304020461108079215040e900c0d04043c11a81d0b81405072415000303001c0c88544e10310110001901c0060f078207001740342d035101510b849800c500520811b0400d45000d50302070241001440800c69000030140d202c0e010505040e64040a01e40c0c61402000e800340218100b4400e089074084115400c00105040325000c0b40200920100701a00c9a100d0080e0354603d404219901c5a03004c000b0301415442050900c00d100000d0b9445441d42c0300d20300f000403844240c480c00404036982000c0d4501160951700640c05848242c10580380030100c01c20424a03044400e041203114201142814008414070a904c0100030f400c038005454140041480c00200c0d82903001a0a04000804070350061107042c5049070001c80032103050103406410700d41c040880908903000307035440b8000501e00c58180706c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 952205773 1250 952204523 952204549
    0x50a081e0115150e03070e16090314030409051003081918090209100305160e031203040b040201021011030f1305011b090e060a030609080409090309150807020a0303021602 75
    0x98483e030b00c070f00382e0800030001010045228020341c07084009010b81440403080d964400032012a01040d41001c0d0000c0f161821a0351004004950001c1c80d00c540704030110140040d034004072005c2042d0380d960b80c039800c42c03051035100140604008010000c042ea244141d100f012694074100140c21281107103402012002076800403011560120f0a2246407a10201002c81c0300725519043c040d5080c1442200c08100c403649828083c03120b25110f181c2c054030f046c0000da1003407145509181e121b00d01820991403d445c00c650490050040c0400e0564500062064112042c2d200e40100c0c25592560800202002c01501d000344407006010b900c00052000d0280b941413071505025600101074a08001e0074200381c9170001510702c99408100300341e90710340130320040403240c100b800810980030b81c0c01d00e4500380c0b007150000042c4904000901c07040c150401040c004441000984c0b03500d1103003100c0211912802914000700603000b5407100400300348287c01601a000e0711881d0800c409009500091400400350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 952207023 1250 952205773 952205789
    0x1003021615060311010c02010f030513021e0108090609070e0408070f03090602070801230c041509060806100c03210f090203070b0a1b080d02040605090a050a081e0115 73
    0x2040610804c1084140341414420a081c00035040610b5070001e81107081c21540e2104250f40da1000a180c0c0301009021000d15401038580f000307410321160741c85511110346070640e0105840d000820040b00f00000d18502c5480c03008060400541015920b10031284064000d40f0b4496040c44101c2c007080e12454422010340c031a488084440d0719040f4060b0404010364045600c592400180d1244c0a802905502200703c0d001c48c4100700742d44804000b203c0c0d00598000d01080000d911490302440d41241c10300095070100d89501601343d0741d480400c012403000e180500d00040076030102100080c003078060309044509aa03001d52240813482c0c3c110303040303034040940c0c1c10186450b00d800b2010344c24207001c1d80014000c101c000c01e2a1806201c2c0203006401d10140c01c80d000f101110404040c01003170740598034032400800c425540e5950301c0350010400c1d0004000d9030311403841036100240343e14000300b02a0461381148003400002420004ca5a07171000f00c403003003142954840c4004a558102a00304d036015010b11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 952208273 1250 952207023 952207031
    0xd1802041a150a050409021e0f0c0613020a060e01031116020109080a1a070504030b270a170a05160b10080d0c121205151003020304021003021615 64
    0x11402c01446140454102d100d5000411080501ea6400fa044a01b0f032440d0900150f5551110150070f5000a00d403001c414440d0740114040b00511311544c01044071410080485003551030b844440b1075014071b298070003588848405410031129018403401d02c0c031140c05050004410040d800719403003d80c85600d8880200341d44100d1102151b03000756003071001e009400d00805081020f0303a901c00703820490a41da1032401c83ca440c0050031440c4214100c0e4080d56002c248032583d41802203480a100c2c9c0c0e4280342580341c2010700e501801602c0b00103500c100d40350308403231840006134a4110424103030380300140040401204100307010102d40324a00000010307100b100301070740c0d502e00220f1450490030f086e000521550414401c00e01065404801c24015a41048600b4104a101d520070b403100c0741694004c1d00030034185001c000c082c4140e201034080381c80003600c41801d069a0303444100e04038071003220000e40c031601d096031240249110758003800108584070504400406540c039025014030060003244046912 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 952209523 1250 952208273 952208321
    0xe090115020708240c0c0d0201021c0b010804080a09050301150801050609010311010f051b070602190201050301140f1305061c0f1401020f070602071b0b0d180204 71
    0x104112050003000000082c09680c0c0441d801c8041d920200d899901100300140017140100d019941210000701440e011540305030381b8120081c0c041c0d00111950003402445a2100d00440c0043c020724003036038070580d10700130550b1f2181e841c07006981101e00340c40104001c0c45804110380c1c900740700b01c6c1602014000c003a2045880c01800d1420342d140108101e01800380d01e80100b001402d2610299002503003404c20040304c144a07142181c0324080c2184001048400c82500d100700a030203c0c00d1800ea032820f50070764440c400013541202d0a1035404074001d00052040004004556500c2603007408003000504464100c007488000854000c4006039840183c1c1d5640244202c529183e48240590113124440380342d84403864035151510300c481c01c0003034548442c410552021000c2035045600100c460340c005a2108034908000c0300940000c401200c1300d6801c07803008891106421150b208a80b01400180c0c6020810882d45002d0300e02482d031138220b8400141c0c008010394450080c0c1c00030ba044d00e21018002c0c0a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 952210773 1250 952209523 952209527
    0x30503030f010603060806040f06270c0803040810050a2a080907120f060b0418060501090e06010303050c0f1e0d0c02130225030903150506130902010e090115 69
    0x70381a44001d0a1514007042085103520105403294000d03046140c0340e00352100f500300340c4054004581480d0900f52070b400704d01d582c3d89003221280f180794010315a84080c69280c0010030b5880c861800f510569030701c1158070b0844450190004c1d54000c0c0d108001240310010142040c460521340460440d00042203a40e1000b103d600c00c004030b034072002220042001038074045400480301010b2030007801145040d03e4103000d00c9115040894000000f4104120f1104c003015103c81c0c0385500281110701c9418031000054408240c020b00e040c910441001e44800e03417a66034160f4040d4006a0540c400707004031511036152510502c11080f0201c10304d50030100c04c0c841a54101d003006140c4804405200c144244600580c4401c541001c02c0e1070b00280040e030b50b485c0e16900c007500e100141d00307498842c02c1030291381c41015030003001d80f01100c0c8202d104403e2887e6441c2500c05540d421508030703820004242c070007440703803141d60010403440340103041614443c0154804583c1400e8245c02c007174032101d0061a5410541c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 952212023 1250 952210773 952210801
    0x12010207032a02010503010902180307030803160810051903080309062514091219020f01020d0c06110418150506121b0405060310080601060e0927030403050303 70
    0x404072000741d002c00301c00e6030000e0014001030207030b0607030140d01142800c032085041e100c4002e24200181116907480e074a00d030030f45071644115689140e5030300501c0080901780c09400400d0084100001c444a20303410107082c801e22803000e600c001c40e4038145c600000042440040214050106c85c0d02914181c50a0041d105103100101e00c10040c3c0740f000300d0008000b603400000004c4140c2000c212076520340b80400002c03a034014080c2e207000180602c484e412100c0301c0325840c06034014801c2d100f800c40003203007800690721141c01403441000704651a0f1010000340596006486190950340068181600d0b020900c0b4082e40c2009090705469560000c014941e0451404c2c80c01001c00b100e03160701c0c18499001d02c1e0b07888980602105d0400d055500754465000d000000d50b0094813000c2d0047d80c90b40717403100b8252000343e03c0744101c0642c0d014180000c200144500c8010020ba0006019a401c070703202e420b040b8002e6000a0081048150410303850078880d4010300c000c2000314020307002951a41050b01d89242c0403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 952213273 1250 952212023 952212077
    0x609051906020c010e0424030c0f180e1c0f030f06300f080d110301140f030c1003091109090d1107030206030a1a1002100b1201020703 59
    0x5940a00020007840da80050050790510003881c0c5101182103210100e400303841d003010309400b82202000b44403200c1c4115601070080700d010b8281e040c020781c1d13a100c50b0049155103028035000280b10780050000422503400996551480c1412200541d100c0100c40d0142e5102403030b802c0000301c112452409031a07040c02024903818416204001c02841c02801c0e84d160a500103000c4c41c0c0418800081c40d4503001c1c2c8140b40e503402e0304109240000b060614180103a54004688940c80900e81800340b4100c0c685c0c4000d40341a01c07180050100c1c0619010108851181182c0c00550315101c0d1401c000d0f116242c5803108440c06140c0d80f4045182a03180c03610541c00d103070440c1c805000d41040400c10040e0030000844420b200e00341c0c10030603030000b4540441e601b812450780000e5003049001007030144504040d0700c4844040c2d1444480d0f940300b03000c0c03820091816107002c1c6010040c0d00c24000060b14142c0703070f030100100c40002045000d1381001041c600b42681c200c41415000700b90b48400042c5201c0d8102e80341011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 952214523 1250 952213273 952213309
    0x60503070c0f0b0924070f0c0c12020a0e0118020c0a1403030702010b042c030c01020a181e09020901111605010806010203030903040b16050a060f061e0b031e01060905 73
    0x140720041645a00398000106890100700070707d0300340d503516405958001c55540c0c00c03140090340152074282284030f00540d038400b02e000c0c5944200015003a0f8501e81c445040c1c48002030452604d481d00031540d006074110028030b59442c015012603070009816056461000d11065000d10340f245802180603003103507510b030403540c040c40c203125106201803540080c03e075010145071240810600149081480c41c0030b0b500c10b000c2198170002d0b55004403900b00d000010400c280301018001180c84640c0c00c2c58610351004200a114103c131000d005030310588e006041c945906241006084102c0c80c40ba902e0104885000200340f0410340082c4400d5920015031540048203000962842c103100258665a00c90383c070401e4070b9860017184814060504e000700f0303205241c10904552a1584a081900013010800720119031240340c54070011b055030b90280c1008038030014148000c402850041c0301e0480d50b00080089101800180001c05081d8003098002e010b402c0f1981d03003004182c2400d06000510700d2101007004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 952215773 1250 952214523 952214563
    0x4020c070608130f080c160b0c0607030606021906180b040b06040207150f060b0a02150702011803050705070306110a0e04020f070227150103110f04060503070c0f0b09 73
    0x3001c14002141c0490079a40604041d86c0c0c0d0034400c4020b414901c000042200706440701100003000c07502c002c081c01840320384a054491a40361010168212101840340d100983c204201d5500d080d40c1d6008030030030150007001d001c220240110403101c0d1548000c1d83c102c910a200205100030b0000342034a05074890400d5034114508415910340b0f152240e280b440701c0d4034461f142d00030350000c001940c100800070800400d600740c44111003503019481316260b825040440700c0703100008880d140b05000d0904101c4111031481c2500c1c51640b01101c29074003540041e43d15210707204001001804074030034603405501814001d9140c00c64034100500525081100e184601c2c01881041002d4031003c040382d0ba4198100c80415018911700715007080460300091400d958903401c400c1200c224200900326070741c50380907a800c001820900460019501861100454548040c40140100f50241006582040843c1031001400781c0035501c0d02d0002501c401304030340203074046081c080c031954200240194150010720b084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 952217023 1250 952215773 952215811
    0x62b200a030215190c03170105011209060e0a081902030301031703090114040602030601090b030c1206030703080a030902041127180f01080d0512060103051504020c070608 75
    0xe000c002a6010281c800d03400841054640101501140d805150f0070b052050308002208010300250a01c0c80c099003c80c0d001c05000119101003d4103d068a1051319032103505030250b1100c034010041114112402a41c0b69010820f18804008500225200701e41c002ea482005610380b00b03010040800f00819984240018800681d41e0384082c9072008041204980344d5a45c50f080342c4c054000004920074918202d0240424440c82c1c0d001980b1a06081e207900c0c900d40d6a0303603010740480c40308543d4074400440034000ca040940301d00b030b1078a4200e400101107400c1551a03803202c00d05070b448494400e021a030b82d41200d90031800c050040c2005c00398806445400d04820008000750180814250581c500290307039100c16030364901c0384024131180c1d0020307031426516100024040c0e022007030180100c1880395600344042136121f90110756003c04039042d206c1c40c684498006402508014081d00c01c0c10500d0088119031f40c8992000d4101d40c54001e008140591030500083c203079003405020400351511b601180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 952218273 1250 952217023 952217029
    0xe04020406170d14120f01090501060f08040206070c0f0e0a0c0804030e040c12060f0801050610350406051005030c0f090c04030506010f03050f011b0503062b20 70
    0x14405182c5080000442d440d0213076103041ca00c04c801e00c40d0f003000d01810600c000f0500b00ea02c0c25059600603441000705988868082d6214030105c54210b0009003404002001803d041000d0903040d0b1040b035030070341d505840701582032043e030a50704441c001ea00d00a0411000c42090300030005c4080303031400c02421608082d18014100b0714590807860149482e80c1085031b880340f01c3d4074100c2220000b08400c201464070781200740349519071403181401c40e6003850041001881c1800b8443c10b01c038190b0b280c0c5246400280c45d405030000400b18001502840c41c40b24507150000601d01c90300c03d82c854a0300241518040c50307000007510f465008980294420005505540ca0303007451007948030310488884100d55103171b80300911705100c1e0303410080c81c502440f000065080084800301c420380e84100181c40d41000c040346203d08071640181c16000f1040854003a1104d203014000841d0450006040d010500d0540c0070081c10300c00203c0005c89540283c01152070500080e01401c406201c0b00b140b540c2d076036207021400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 952219523 1250 952218273 952218283
    0xa06050f07180b2b0c0e0f030309180901020f070c08061f091104051504030c060503040506040201080402041415011107030b01060f1b030302030f0606090d110402040503070e0402040617 81
    0x28154901211180c11101382d0b25001d0b19000705100410184242c00400070010324516040b20128001e5914550091161401105440d0082405052082c480c0c600c0c6403003840814001e00b15540f1950308101550b43c4500c41d10041074134500400c002910701d0324151132680b0345800240b0b9030f41240c0740060440181c80900b004201100e00492011540074415000c1821a01c180da0156a000300aa4000d0700c070300c412000030b0801c40c1d000d11500342c002075a500c03041d030315071204403002403140d049207000a0040d8040c4000a4100303001078000103141e040014044100001960342e036003045003003002c00c0010f682c8001540c4403907581901810f0490316565030139184070010300440c01400082c40300f42079040d1081925649142d40c55000f09900380c4103007400780096200b50303a00049066000001001420810210380038104040c2082c10b0720a10307034581010601c00020569806a001c0000103640d83c1c00300051030140c100207407030072090300701441080119040340e80f0864903e5140a40c1039028400850 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 952220773 1250 952219523 952219537
    0x3070e09071b0b090c1801090e030c0a0204050c040b03041401061e0e0403051c0e011506300218090a050609010b070f060c180f0f05040e0a06050f07180b 67
    0x10928103031960300d078407400c5c901002c082e2074102501c04172280220100050007070489981035400c000310600360800031386038419000004155030082943d42c005040c19806594044040c14040f8100303601c9060400c5941d0054506070354440402e24405111030003031058800030640c0e10a0091244038130b40ca1400140b440703104d0f0a081440c03030400542494060300484041c0315059000b84142c180ca059400010481c05192440c550310380750a00088000c0c044042e410384801341c5441894510441e20507110603403c55a241c00565081510500600c0d103001a02e840400e01c400d614016442c6001e10540c0c050050140400390b08100512200703403a50b800d4903054400a0106640ea8101c0e41001c25800300302403001402c00d490b200c1d11255869000e405440960401300c4d069a845550b07658911440005004100c400c4204540401292409900c525032001043d41641c0414505450f1401241c4c8103d44181c203180f1200100801d4a6214442c01401c00d00c80814a1200d0704180f000525409480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 952222023 1250 952220773 952220783
    0x203070c08070f020d051c0807170a150609090f02281404090c0809070f230907020717030406020c0405040f021005040807290703050c0303070e09071b 66
    0xa07800c09000640401403c050740117024400d081950303141055480307081c070140307100d407118000900703424038807400500d80103817059515091071414100000f5200d04000d0803078104c00d5510381d942d2101008002c1c1c074800409140d01da0140c0c01c1d1030720b07080700255400780c106210010703c10080d8110142140300c00c24035252807051031003001440a0b1058601c200d5001c038181a0072000f150000c0c015403150840ca003080302c103546942080e01c40810059407030202c1d004031402407400c000c0a00a210465202051074484032408501c0007046001040c0e0104040c0c80c0c4d48016005807100f803082034489294101d0301007641000750724103480d0440094a440c40074190031722868030352010509010924162030784644d002001c0c802c0044a5000107810b5500c0745c810b80406005030f880001e0700a03244030b25070321081c01a41c07004003d0084501824583d17440440700b00c00340310050080102c40c0c0000c00c051445100d541d00c4030400300b1861010880c1c8508020102c90400a01000d20400090803417950100607a00c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 952223273 1250 952222023 952222027
    0x1050118020c1905030301030311010504050a030e36070c210c052d0114040b091518120306030a0311010b100e13110a0f140c0f0f010203070c08 63
    0x9001101c1c24140e2200c64101001c103c0800001800702c08401141220f12a448404001f110319101c1c50917904d00f101c0162450300207100c1c49022a02440c8218801a001003403900500b00c01000d080900c5052084401d030420f03810340d0418030f003500ca541550800118140b80c04041019564500c640600d0001181c070030100a0701c4000040c003030130442265036485003d40340391140003110f200da103070710f481c00e0603000403101c10030103048403411f10942c2141c1450f9a4a8881e540e07031074480f02501000a0f042e18810300c0f804030000104405a21914008e400c51028028a200604e01c080e10b01000042c60119841080040c010303140c3c0c0002d0340710212a40341c106050000c6d4030030010b600600d41e01d8540c682150b00010702d138030440e50118880c018050700321990310000c0c48610015044480f590003800303016604000104080c0d01524544e42869660704d00030140511a030b40d500c6481e005030310888030552240503201c50816081c0310084000e000f49008508600d00040024115400c0c0b00c800b034504100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 952224523 1250 952223273 952223287
    0x13060b1e0f091b16060f090302010f0e07120828080f1012030201150b0d050a0209061e19080108060f070e13090501060f0f080a02100809160602031b0105011802 70
    0x15502c403004040c2c1d00400c0c00c12100607419440c90147c00310a000710700552800c80001c2c1c0003409807183d26149441100100f20860a2501040320800c4602c001e490102040c8a9048003401c0d01c11405240703800c40d072481900800c013880283c040b0300045c14020750200030000b000100903c2c103c40000301c1d0b2544250a500c0d501500707003a401882c41240c0901003018840d00403030f200d0750820003454400d02e52001000541e40710b1190078102d000e2280070a078082401c0240012004107010907000c5a01c3c04070740c46180403440d011401012240d942c00f03c0100c3d045c1401006808010f00016a000c4078101c8129030b140351030f0307100503c1c00c0742d1001410b110707400c0d414802417100030650000d2902c0d648030000700441c035140c0c00100c0c0d40804a104201c40311425030000b003241000070542d0040d582d4007030b100a0000d8005003065030923500041c00d0940c43d1007075035070141ca440d5001204400800075600515920400c990744003100d011000390810b16030303042c2001002800c0c3c40e20030085451105200040c0c131000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 952225773 1250 952224523 952224547
    0x70602010c0e2b05060603100209031b0a0e0109051501021606080a0e0105010e040204062403090f08031509010504061a130f1502150c0313060b1e0f091b 67
    0x41c10079510f00701c080200781c074a040000010310540512070840454040f00201d11241050303200300010150117401080c03c01ea82074580100d815a4a1001054148550707102d503424045580242d002c20309540d01c032003e0154288070b07060b200c0f000c900f0a01c0500307130804032604101002e00052052030100005980012200d426a500c000c0000440c04024451943e4840c415145540265002c1c0e100300d00e400070018002d0790b809503150341e0402907000c015005801240c268010003a0410a592011145102400064008004500c0303001c0210190782414618400c3c0302090344140c002c2c40c092480c06005001c04200d0b0054203041079540610547d960340b06800002420300c0d580c0c0a003080005004002c40c10b0125aa10101c03500060b80c00c482a208110391040c1c036a80c015265606140410400304940041290700204d42a0007404085405c0031044040f03000f003561700b0387c0c5040b04003031042e01c442e251815101e400f900c0a400c480292403801c2107142440e00d45200c100301489460b0019803604014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 952227023 1250 952225773 952225819
    0x1501050a2c0a15030321020c0615060904050a02030708060a050303040902071a040b07270302010e01111207020f0d0210081b03010b07050d0f050f09062208070602010c0e 74
    0x80f943c0da0030350602656868041e0102d60080c0136000c0748000b001c01090406207503c01d840c594080440100303003540f200344040c0b0ad80c0a5038024a82c211008000e03011040d1620302405005200902005a80b86060280244a2400540103030720404041c40c0401c210303500003007914184ea802c0d4000698400481c50a019981c0400c40910141d034010b1040105108a020116218645030f4592204050201501c000a4566041c480462119082051001d03500c5080c10080300780040c1403c1015650b2580c1040c60b02c408003003003900d40740002400c2402c5040003641050380000a50741400500300c0d903800245911261751006041140040c00a42a81400c3d00c00f158415860070391140c1e2561520440091680900305c183e640d03205940c50f0707403040e80c410035100d03841e40c19607510f032400e0111103030045100d0340c068090b191380041c0612200010081c030001d4144a00945081c10040e5841c03d0312250400440d5801001564540b00d0910003040d08004803440814045a49118140d03400c0c0080000c0703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 952228273 1250 952227023 952227041
    0x6120b01170702070303021501080601120813260c18061f0f09060c020a060f0e04020d02182d040e010507030f06050307060909050c0c1501050a2c0a 65
    0x1a40300d0070a0156a40e00032841d001640d029600b60354121b03440120141103600c007842118826807010004110a0a0391281e910040303101d405502d150800080009241701e07050780041c17400d407051130441d0358850920881540c0441c88003001c0c2032030b10b00a100280790003030144003141c5c25225140c0001ca107942d0720001f4201604189000d10503c0054040050040b44080e01c003d020031003d034130200e0b402e401900c911140f568000c0040c106a400d01c181222440c084002d000c4c01e10220b0106007003996568000742c00e07114a08071b40141c8460040402c006000441c035040c0b4010b41c0b0004482408086090340d0000b83c03a100042d81c5100781040d00440c0013010100d030752081d10351a140500001c03549c19080311005120f4048284070b81c1d6121420103480c4c03442c0c0d00c10100450b43d1000300300885c0782e040e00800e501036010341901c1d04012000d40ca0034240300600c1c050486002034000103001d603182406000780034068113481c1c103c0000c12000c04130200c0002d80c04011030b0340b69820006201c40240d410030901 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 952229523 1250 952228273 952228307
    0x30e0717010e07030c1d150f1309110a150903061a13090c14060909090f0d050d110412060b0a05040e03090906090609061012020310081606120b01 64
    0x30f00d03541c0c0c10040300c281d04e14000c01044880503204000d00c15600c20f5200d0068030303020300039402c008944042180c054940800550407403000c005201180703407144290117255000d0010303502d550410008101100a07990450b50b00b4440d101415401d0030303400b06001007501d0b07001d40005a50266007104a540d001001e1a0a501a00c2e00103011410b5010b0342003603c0b040e21505495880f182c507007038410b9020500b042d00d40d8000354280705850182c6400000d00b5000301c0ea50044e00ca2407050100c01a0401050f240d80e074012540003d00c01e04212107510a020000c8034400b903480c1040c1c1001c5000344c802c1c1e2400d001418190311030b819581d6554030b840c4c00c000140002401040701d500400152a180e400000b039031886000c1000000d400d906000071035510a213002004502280d54520400c0048039940c04c00308100082000d0f1890506042d10003036014090b100ea000d1541854407154a00d00307400011552030384144000304100f2190840d48262108140b5030f004245925090b0040751911003500386012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 952230773 1250 952229523 952229533
    0x9071206020d020a0f0e1f050d020708071208180601060f020312010f2115021e030c13060216030b06060d0f05040203280b0c07020409050f0c01030e0717010e 69
    0x4141c0083d01d0f4504080a600e41783e101540003010007000d410f02503c8039007008a041c042c01f42d03043c440c0005103490303c51002c0050508003ea25050f0441d04000c0e021034482000c03c44010b805d5421036600b6034810580224000c0c181c0301060b100381c442e5018402c3d002400120f046401c420303402807003a507484a610342402e000c07546c0c1d05c0030000717100300c081d2103244000c0c200100d4000e11070b6124030741c4449139900308908a24044100c40380f42c000f50710140901c0a00000000892440000c0400941c00340c144400d00c0c07621201450140c80c03030552a54400b2041d984581d99104482c4102c40780c0b942140d81218940096503940d0b008500c1c0e922031100040c000c54a007004641201070f07240d000c130f0302441c026800c460781410042d4040d0070a1084420140145c00c1059220002a07030302e040d802d03440721902c4030031401e1207455070125090303400030141101c071500701040c0c4088401d001c0000806840c000d2800303100900e1441c5440d51500950b01595281070f22503102c00040c0c260035004030110340d0104d41164 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 952232023 1250 952230773 952230787
    0x905040c090e07031103040f0335070512070e040b030a0c03060507090815040203030405120f100513170f0a0801140103152c07030f050f09071206020d02 67
    0x1c0c10030841d030060014004044011450241c0b00e4400c9064094800a6551454440fa00c3e0343c50590175041c011820084e000c41c0380c04200b44902c1c030981005410008144040c20080b29942086a005002e401003090074810402148042c1c0344860700103815081850141d0000380104003d00500082540c141c803e051112080004c0602c0c00c1e0101c0340501c1d0100f18a4840c254202c640b680c051080781141e612840e6409043c0100285103030f040f5100030f04503480c0c07a50b100080390304120204594103103134005500e41948a40c0a00030490040c60301d0004003c7ca1400b03d010502c204048100a4020034504500940c0c6400304821501d07001a24107400e0303169214200002c3c44403000f40204c41c80c600ea9034400391243d500038025040e80800e58140c41180030300388812130000c11041c2401c4510030250003140074022013200805401000c2940e4003140d0500202c008805946020300f070501ca0b180c45c00104044030390b000c50b82d00300f60703200011644130300611410110003a01584e0500b54075103100007203d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 952233273 1250 952232023 952232027
    0x9070509130e0330010501020616121a0405070f0503220f111e030303280606050408010b0a05130507110303010e06131e0209010c0605010b130b041a0a0905040c 70
    0x5603c2444c540070040200004543d01580150401c2c07007024056400080403070340014132007180c02d90100840c87e00070301140d81000c0074020b40381d8102160300d58900a4450300182e06140c045d5550141c2e503418618042a8000b4008081e880020070207003140100307d203841ca201d0980320601140c5500142c0348014204542041090546101000b034824101014900d600b90300c0f03003403000c5218500070301030344c119514500403036000d014202070300f2031507070004100660f00452480b4050290a043d5103154071682007003211400c640d08140050321400c8224000c20040d55840c9085500c50717401080803c4907112010142d500070010580c0c80b9160002000100347d400464003003502c510822114a01401e54008101c012280b00c2c05400c151002a1803500c0074040e6950018000c0c1c0c5410315007590a81c0b0652140011104d0a0300507020829000443d02c1f1020251514680644182c1c0790840c43c007450024110034507580322054500d0001c020079100c03410740c014807400008040c0a8014440000a4070700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 952234523 1250 952233273 952233307
    0x3010b03060a050307120f03031d100501270207061d1606050c0604030f05130303030e0606120a060b0d0c0e06040e2a0d120f0e09070509130e03 63
    0x1c0940918802c12001a0625000914200302c0d80d00c108005001d03032560712400c2d40403240d52000c4c0d0a05441d03444000c000304403801040c0602c1841d8000d00715055a00d03004000f66071040e0b00c2504c41520102c1800800b1103109120443c1d0f41500d58010390760340d062320381174000c0c050941070303c81c407144114500321440b41c010581c962801506900c000c90b0a80391031003516640a007100620940c2d0000000600181c082c150101148840c0d04010b428544105120300052501380c0040380044d445581c1850a507400300186608800200c494204a642e5100c2d007555464005002401407a2252030a0785561103140700705800b41e810007100c0203c1070b101d104064112070265103160096140018100c500e200c0400c03003101034881e007044c6080e007010203103000c90098424462940d00440003805d100014080c051a82e0307014405803070b00c00104800960160410381029051401141204d0801002c19442411641114004c917030250000c24140903005c01403480c10300505441c800000c8800b096150806 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 952235773 1250 952234523 952234531
    0x213080a1b12111908030309010c02070803070308070f1101090b06090703090b07030209030f03070317181e0c2206090b030a0b04030c050d0903170c0705040e030f03010b03 75
    0x320340302a5580d960942c105808401400340c00d07480105203034859850604481c100e50384007030703083c2210540c40c1c035070040c00e5903c1517400400320f030340d07175095040f0341d507014050700d00142112006182851030540b000703426900d0062a00041001a000700744095004214190401c100e441c0204040561882d0040000e1801c4d5003d0307110b81ca40d00002405140f0034010145a00e6102c00101c00c0750315006015800b82d003110515903894020941d10f49280321080014002c924065540c0042506080f2000400c0f0301010385201540c2c4401c00d031a1791115030010300280c651115080500584007031407612401c0440080003144d01100d102c00705140302d00c0d1840c0b4080c0b905502c0c01c0c00c000e850354466900046845200d6032581640001c810540800c0807003542582c014000d051140820406548072070801400c41a100042105568280140199841540c042c01c06002001e40b5069804000c2d070340d2100c1034030441d440340e40c442003c0700d24854284103176211410f0a851403501c83d6180c01001c401604119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 952237023 1250 952235773 952235813
    0x70e070203030717060f010509041d0a020a062d090b121602010920240a03051501021b0111012f0301060909020c2113060206190213080a 60
    0x158000c0e44400c0203048a008400003845a544031b2540e5005481d42e0308003d01c0c10380e00c00d580740c09500e00c8084482030741a00003400b01c00b8140b80601e034410089048407070b4025030b003007000b901d90b019810b0340170140908800400220300101f494089000300c074a49543d400c809100d4101260804100e40107064031805400c2c000800b002400b49540b0480c02c0f1014200c0140040d000000321b0f080c161805a545400303980045e025014050300c40c00d24080d1001c441e40f07003c60002d40000d00900e5198184101500a00c0380aa000e08071481040000d5541d01c1c0c03040041185078a65851100d507a000d50701c00203440b65510700900144541405c00710100300965161180006443d082251a44044085a045c0c1308261550602c103410800c40d2402500000038024952040d04d6886517100f010071031203240d1b01d10400d40ca6036142003047c00843c0380307c41c03a40034070305646c0729409100a084501050700a50b40c4200001601c1d0760a80300725851942035580243c166000e100c104500780501080c070724544d090380c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 952238273 1250 952237023 952237037
    0x2811030106050418060b011b080c1207080d06060c0b040b0a0e01051812130605030907080102070c18110414010c02090405060f0f070804080c0c0a06030f06091a0909070e0702030307 79
    0x207801518208100c2210308141c00c032344204100081e040d200903109443d005011201282c070500d00d54442940200001e8554500c04a41d100305681c080c0107103806014140740038001d0100d9580c4101c2c00001c00b40005059800b45030000700880e2080d40b20402c0760900400a00031420001155403410b206034102d441c09000f100707200c804003214001106c11003c0200d6629039428503141040301c550700080c1000c1000d0088100000780c955090000d000070300e0041d400c11074121f01d4600608609a41409000300345803d010607510401022030a8074200c4001c45405000030340d00d880126445186080d00950146555082c40180440064441d1144000c41880002c41e26410400c101c1d1060842d9100300140d00d440000e000206160064406030702c03001c045560000c200c400140900c030030b6411200c0020b030398818145c0c405000d03028540003402c00707510401c0b80c20018240200d082030711100c0c0c24000c0080c90045a0f100c1010054000201708030305040c4900d082240e4025143e41c8181d0704c0034002814 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 952239523 1250 952238273 952238291
    0xc1a0601090b071101080c0d0e0d1b111509031c020c01081302010c021503070f02010c09140d050309150901090e01061b030201110c0f281103010605041806 68
    0x70090842d000d01341c00c18000400c900601c0011500070800034503000c030300038040c010407000800303034000d80550802070000742081007031550000780b6800e0005030b904003a14452400902040380c00c0b1a110701c50b00107981708425981e040a0400d090f10a5085098142c0302e28503e004107008480c0850503207078004d50035142001da0f41c00045a404000740c0e1114130540340381c4900401580645140d207040e510107041404042414540900260401c5581c18042900b2036094405642e080c4552007452215091070b205090400d0001c10003800c071003070124040c810250398982072040802c1030340d1070007500a03c5410140c480d054410095040074280c103020400c1340e87c0203e0031071900c0308128141c410680d115850342c140c91542c441a108044400c1d8195540c820f02084492000002413124100c2070b00102100003211208520301108001f618a160306541d05c849142030b001e13455002c81540110515003e200f000e400a40102510f42c403440d4843e152045601c200102e03c1050050603010f03103c01c0044100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 952240773 1250 952239523 952239539
    0x3070f1d0c1314031f1409011505010305040c09020f070c05060901080705181908061008060106180e0f150301200a09170624100c030c1a060109 63
    0x240c140801c0d03034624071050078080101e07032800300c94541500601710399402a203144480d1001840c0d1004403941900e40384401c41e4818001403158020f0001c1c402000070840c4002d048008071b4080c01403074101034840d4089018004070107100d0b8081c0c0000e010031035440ea10910300e01d00300d03800180211900b0182c0301d4002007501d407100a9070340291040c0c40b0394100755103c2600319550b602c0524181c00480c41e044030345041e5296200500c0c0d002e103034543d81d4400a070619078450b00d0818010055900003070b005006202c50100840c0c007e04664560900d850440c521203010246414036030042170509030745001b0814907401182d080c42c0a0103d10030512140c8410400741401d894100c40444201c50200d02d0b4540703154004001420011101d00d0b20100c25034940c0b188908446103035134851007560169007400743c40c1d9134181d6180312030030750b450700003c90750100c0001c1211202d52401d58020301852444610606025075803e02a4544c00328650100301030072100c10350454000d9079090300240c4544000f0500301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 952242023 1250 952240773 952240777
    0xa0f0614011805280c0c0c083007110103020d2f070c030201110f06091b0306071719020309160806011508040c05130903020715090905040201110d02060906100302011d03070f1d0c 78
    0xf1072101c2c110b03071410090746c55005441340102107243c101a070800c10000c1d000458430032122030740c041184031503201318208640700c012000032902c1804030308104000c1d00026541c4442e20201ca90a0800303400451400001c103043c00c24441100e815401903600f0014003440128010464600d48112803030002c0010081c556a80c10403240c0202144081109910b400c42d00d403001c1d9400880c0100036964030b25029260802d03a00251619000e42d4018031008000c0da0307824074001d000c0c05004c1e000340440d6142442e80d042420303040207046c0601066801207024004401c0b1500043c0c01d001d41019404c00011000400402c4042015001800346400210b01c0895500c030090301c06406075181ea50030b508020341500100b5020303200724180b0681c000002c00c0340f8018000c075000ca500d241c01034429458070320300315030030008014120000d00805000610050fa00b0610b8100b00600320621358810760743d0390780442c0c5040c086400000400081c1007000608010301c2000f40f0380040b080e0a88105600c941038100801c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 952243273 1250 952242023 952242103
    0x100c050708061f15081005040e06010e01080a0218090c04090f020909061501030f0b03011112251101111306140301080a0f0614011805280c0c0c08 64
    0x207102a41c04c1d040155100e0080305c0e401070000d540c080392065668000508a988143c2031030419040600100312210102c00641e00403c62034000d03101ca9000780d4002010448501d03c40340303d2080102c00318041480822500310054405041000b056445040101d06614405002c81c8651107100000d504528086a000c0c0a141c4400300040781c0c00c0c042d00150003401c08056221902a03541ca006111b543c0c0174010300744112448000d103681d1b0a14680d5142c11404010801c007840c41c00d56107001c6044004941080c01700200e0b181902840030901901805006d03140c0703400d01243d502044007080950318552501c2101d00640741c0800c82050300025000301d000910841c042034100090400202c1e5403101d03000b08080c800e10740019180031505080804a1003078103c1829412007034050280c09915100b035503041540b42c10790401c00551302c0110b41c610144030300458012601c5030646183c10380640343c820025980b084407102616110314210b6070f01c01080e580c3ca805450b0f13400c5620715414580c22102d050b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 952244523 1250 952243273 952243289
    0x7051b0f01032009221b0201020a0c0b130609060506014d0a0c0f050103050f060f12030d0b03060c030c121012140d0908030405100c050708061f 63
    0x1003400280f030f11409800c00a0b81036000300c01c1000c054a6034094800744d941c100c1d5254800038108200036144800c0c4a1405925400d6a01c104030059055410000780c40307246600002c042c42e183da40d0b0b4505550713044100c90060030141003601c00000c006c203a400288c441d400a0380c402440d50f0000807002c0000c1400004009250608000c50080b20104842d480c2c4c1400c140008910101e40e00540074a0011407513401d941107000c1c0c40c07003030210719800850040100b40134607090156003813844008000000c080d00151040d8601d8220140903203424801c400094600415641c0b1800146001d0300507041010040d4403a015010005416442d0310082d24001c0d445030040c0307800c0c0f0080e041105520b010140c859a08840c0d41c1100181c1952100c0c0304001c2c841c440c1c03008052501005000074640b0a1108101c02480b01081c01030185400c0002500d0032a43c1c2203c210341901d080c0403056482c3c14250f90054400c1c0155840400c460784005075003400b5040540054180d05100344d1141c6800c0410300036003c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 952245773 1250 952244523 952244561
    0x170324040624031b020708150c0d15151e090b0a050309010b0d052103072a0f0b07020601050411041203350a02070f080f07051b0f0103 59
    0x2e903940002c021180035429040c00954500721564540c000c0c0d1038824100300607032181c0d4051040e11030038030850400c0814241c0802040c10000490345283c0078961b048044d180c2d039451003880040484031814010007c034685101c03e15007102c0000c003012a00e074003000800c0e41010030a0b5809204030030300070856201551260070800f0500003258150302c0602500c40350764031140c0391411591a0b4070075200b840d110f4801410909500740d40081c9004505a198481c1c0c0428801c014456802840c83c0d4015003880c8030800484e10000d0300b910400c504014050b007104440b03210310003001884c0c0040c1d07025821980032a041680da4508000540c1c00c4141e070000c600005010401001a26400005d4001e01c2410400511030034000c0ea2084207483d9140307000c540e0b50070b40e9032a540c690100703002900414102e41c01d5107400c203962220f0403140d40103400105664400103400e01d501034000150b402a07640403041e21003441a2103060f496840f004482c2c1882079180031280c0b10b1540c042c1c49107001ca0100d90103850 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 952247023 1250 952245773 952245809
    0x10803090d1a13020102010b01080f13150e030702091b09100c05060c1e0316111c020304091a031027120e1504050d1703240406 56
    0x45100107000032103020400d42c0000d8141040c03030400b1840703100c22400c41240307a81075000090a45072542030050500100384103001c0c41001401c11541c2c846100040b0755030764250740c6004440d4006580b1102042c03403501e02d15a8001e94080010910240215800b0078aa125206241c054102040d010f0108901c01c200050060804070107418601d404d900f40041071410729260b5508001d41103a1507107000b00000703403200341502d5140381c40c00307200c0100190b02e0840c0703040300c4010000c00ca140100e0090060003800880008000c005030000f400b241100e2403131240c0b00c01c2e00a56a50040c0c0181c50225041641d14140d25020b40c83c01c82070b60320f00600501c81420f2091429004180d48040700c1d0350340caa0180d01c82600c0408052030b201c5c2c0c0d03200b40b10900c1181004040140311101c000591845070400000480d0782c00408003e032401d9440c2202e0320011040107182090341c48007589039545450001104100303a5503071320901d5110008600c80c0e031901c0602d000c4108005c07501075000c0d490390403098107498 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 952248273 1250 952247023 952247029
    0xf0f0e0c0325090801090c09050a0b0102030306040e01110705030d05151012060b04030b04020307121a071b050309040c030615030902040605030f0f0f07030201080f0604271a01080309 80
    0x2d256080303142d00b04015015110030700030b800e440c603425040c1d40f5003404072403c00c9080480d01c00c079584130800c030500700601403d082c0001d4580c400900300900c59500c1c0d90322650b8410382075009080c03442012489560b80c80c61403600c1912900140f990644491410300003585103108040420039804005004143c0301400701401d41e2544010481e0607015a0750b154042180350480c0300600185020b0036100c111464148100351a00100c2d8004905800c00074844000080e0030102a102d0060085056400ca0361081c40c101c0e03800c1d802c984410503aa000e05400c0b014040080003c0094600540d0306004407c110711055007a1a0f0354442c80400c42c141c0303440050500e01c41c0d401021914401000400c195654100003460008080c1003200150030008c00451094000c1005100f004414006054210714540000e07014001c0200081e5181811100145071355030346070312000e0043d440b81031030f44d4503205078012800b40140404080b143c0c200460081074003800c06c1400c29040729502001141f4110b406014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 952249523 1250 952248273 952248331
    0x1e0c1909080d0c11030705010c080d110703030c030b09090631030f0801140a0510051303120e030304180b0111011407030b0612060105030c040f0f0e0c03 67
    0x204208080e40041128141806421031084842d51808989181820144c1c0c40030382150804c2d21030340c844a0300700020f0341c100c401c0f910059005100c0c00d0700c0300034407256000a07101000b2200c2174010300140d15010140c040d8065100300001d95820003081440a06000b840c07802651180300f158007100006410032411403a40308890131030300c640c007440d00300008800c10001d0050320480219001c1442d5080c0b40d5885060b2500409407110ba6040000004002c03e01888490141501034620790b524001200e0081048402050801900701e01103640c0b800c00441540500c1d48400000c1c50f0f024010785103140010903101a54603108500740244014004000100500c00c0c411f818441c00800480406000303214154520112010701c4800b4034010f50014211090b5503a0144070700e0b410301c1444e03211440c60620540c030160a080180d40d03500c0d03003880348506000b15484021681c101e10408176107414074111540c01c44040c203101c81113503250140c0d0600e0a0104581044c4014550302c4410a01410340d14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 952250773 1250 952249523 952249567
    0xc100501290a2c030f06250c02060d060509040b04020102250e1305120a0f0c1509080d1503140601121b0306060b0c100203060a030213020c0d081e0c 65
    0x502000c018001290a0614004100c881034001a04104d410b41c0c410200800440301031f05075030300100d5140f801070100f400400001e4051a8013089280071020345134031035000381100802d1400c26284c189842c007159070f800c41f0128014064210030b02c000c5203c02c50640d070150604040040c02909092410901010082510a24801401003400071403003c0c030112390b94022010714142e60303019100380941045460400300302000704040c05000451001201d0500c5816281380205255610307013418101400340007542a1006d1400d0300000c0510365070100c070011244203000710504480c3c013003415030b1100300902c100c0c0c01c014154a20751002070843c4080141000280655030001070300c03602c401c011500300d60010700c8003190000c1d0f4070041420400c512100b40141007001d41c41d514014012130400c41141c07000a010f6521000c160034451b1440d0190b80b0710002480855440c0620484001e02d000c0c0c090b5000e12003100b1201d50306205039030145c0c445100d40c211004507407414030245100e081c0031282003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 952252023 1250 952250773 952250837
    0x290402042108090d0f11150f09010908160918080403151e27030e010513121a010806040305030c0a030b091f1e06050c100501290a 57
    0x403050303030a550f81403000c0c040700707006100117a501c20303441c50400032100c1d00d9403c46120380b100700060401e100c0d00100f190a0f9800001c031681d2a00521030040e10444d10b0381c0c120b449240501e50b16806d0420440066604586440394180850015810460751310104034601078540d400400050001c207405e0b22508419408640f00003581d0000e1403002d0900904540e80064500d07100d0700f401007110740640e900074240d4907403110100760600f269800740403541c02007079940c180300022840c9800341c0d02540c03000e0020803c000100701c0d803140c00c0c58403070480362010020390f80c6a824800040f031240da0000313500f881240d2503240c01d45543c90f40120b4550380d0b00208403d034109500c442c80404541ca6421515004840b034080301d0800844441d094290007120390040340c2e210170001d0401640308803801c04c25040300c0172802c20a075603010140b10345d400c20200e83c51030640d0324149400000c03861400c00f800580c0e0b000080700c10050400c0e070400c0c40f20901c9140307480c1d0005200c070030b40c1102c0c5284d940850081d020f030384 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 952253273 1250 952252023 952252027
    0x12040203030d09080304111207060e0d0f140105070908030706020f040b12010302090a020a080c0903030c030a05090a050901140f1306120605010f1d19290402042108 72
    0x44040c16007601c43e50755045610181c040300b8842003021030200380e0401801124142c540301481010140d956100c0d03c510b50810000600410081d00c5900c04942c050741c109a054000c00c08509003510030700324100304002c5640ca40000103440b00c1c803030b8108205a4882101a500e0150b540d11044069040000d00b5080d0300010000025030442c040000c002c40001560300d281d0940c95801003203a4540010002c410f00c0c1c1c010000c07107841e40e030301c080100d0b0312140322031100d82c1b1070441d0340210f80b5601a172400c01c0c01d280300000308034483c541c1201c00380c81c076002c003105c03072071805030721401840704401080c81004640300270b2020a440d18079044100303030212400a44a5000401c40722508425200c23594400c10400240c0501d070800e0280d1401018090708125020142c180d2800810382050700044030255507100ca2040410305840d0b0311503007243c0400320020280402c5100840024912007a6422003041194280801d9130303600f440d00075681160340303801c00c0b1010f00c080c802c100095010916400c40701c442e41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 952254523 1250 952253273 952253287
    0x20a05040e1810020a02030f1c0609063209090610080d120902010c020411070c05030331030b0114100914130b090f011a0f07080d14012312031204020303 67
    0x1680c40680300c00201c0c1c14001480f02200c0389c130740381201c0c6147c100c5080d00d41851404c0c401c0d48001c004445a0540c182000c90010109581e0102c060300b0a000040d400040344050081d160400540300303008205911403040c04d9691103005658841d03a6007a120081400340c005c40300c1d511020790151010b00d0060602c07200e020010380c005021984460f920008802c3c0214005081c411403d100754050b0509a0040d490051441101d1882c180c0c1c0c26500c10b03c070080001010031144042c102c050056a00817000040c03941c40d44055000d105188020030b02940c3c50180d0941158400c0c4140b0048486452718980660a103c05106e41caa42090f03a00d016541c4272140c0b00c00c6501c64aa040e4400c2d031040c82001110350510341c60102240e10ba401e1503030721480071300c034166071314520b00e00f11121103a101600c0d075540c0e44512585005400d03445002203001071144000281c00b0382c0d0b49212007150551404002403a00c1314010000c0c6038030082d20300c4a079680240300b46080d5020b0600c24940003400103085a0130560 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 952255773 1250 952254523 952254547
    0x180c0c010e010204090f0b0a14010c0c030605011503150b0f04030c0902030610090e0105040902130e1c030905061f1a120f0433020a05040e1810020a0203 67
    0x116040d900c50320340e40c000b80402c01c0c4001071140407106c0f410200140000848640080e011800340d00904a48103480c0c0a454845d07801000b002105c103601100d00c030130540c3d0b00d090040080c0b0091003085103098444118003940b0f48284541040c9018040b4450303460350521021490541100110304400c000401c0f022022401885000005041000015a4034075140040c05013145403070741c0171010b220700008180001c0400e0f89015040d07500030ba8000400030b00354000181d5024030742041c0d03046d01e0308d84655140c0c1d010000c21411640b0074003441c0d680e408029114210219150040040c00540201c0f010810307c0c19801b0f00500d02001050320340d64130301c1d00d81c0c12840c020f8000500c201041100050030b0200c0042c104034160740075132407201c03140c1146041d03110a130030758801d40b103000d000e607000b440302d843c03001c0f0004401046560518421074850411150240007580140119907415014500044910501c404840d062400c2d900161151212000806001e034002940b160f00750b0000707100110f5201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 952257023 1250 952255773 952255781
    0x503031c0e1005041a040302030a0e04090605070e040e03090f040b0d05120c150f0403110f1603060b030307030c08070f0506100e181f0f020c0303010e070e180c0c01 72
    0x2c040c0300800641e0781042e04e0607504098180054840003500c8104000109801000344c4181e80164146100c40b1007003480001c008003410b0100030011881c1034288159079a0007501c9c0100d040741030b5070822407882650855541c90043c640c0aa501001901c1c0c418842d060603000340c203600c02d000d0800c0412001e15521503007401d201e00142005010b001c5150184020b04110025400040904052203400c0542184031007050040014007841468004020300d5a01003010070f4900c0000e40c103403890307100070f60b4503200040100c1c4811b90f0050f0074869840501e2501101700d4103555455245c0041c00d00075592901929001080150781e048105540000402c10600005219903e00d440c3d9080c0c03141042030084200d00054249940c046c94264600a03c100029042410038004028540411000400400500403092249002500200354150f1001c800400382d070594003100c002d14015a9003c00c03c6407841801218154003820500c1050b030404542c040c0d40780c0040340c802e40c0e28605203110000609403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 952258273 1250 952257023 952257043
    0x7060509030c060f0403140304031806080702070f0803030126030a18090506010e13020405120705040e2404080d020304050d0e010203040308031803070212060415060503031c0e 77
    0x203030300001200442d110041c40b003150312689440f0000100e013060b85000304000d59140b0030754181c0d0b000101081c14980070380610103928900801c0840c4d0b50781c40c0c000c014145c0e078051742c498016200e40b0001044103000040c004040d58610790040d41160f29103006070840c1c050421800354000c24584150a01c007005200a00140402e070b1103049100c0380c1e402c06c180c03809105a101c2c6040503e403505202e981c0e80d04c0314504403150b1040780d0003800c400f41c001044c00244666840b2a9008030082100c01c00604003241e040201c54080398200111b1404c4a0302648030301003100000d4040e6544440982c01e4868101d80366001405513680d142030480018003001207a000356400e5070154801c079401202181e001e0401c40100c18207101850815203140d5400c000c40c08090945046d0008820170b0b0016054200141c4240f56001803101c2c401500501c01191a940f046d94107840c048035030410015094054000d000032203402500651a0145184118111f5030b00c1012020303916888654110080808201e4000300c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 952259523 1250 952258273 952258291
    0x909060f0a090b0a120209060f01020f0f06061e0901030f030921020a0f06140322210206011401110a0803010b13080a0825120e010f03110405040908070605 68
    0xf03031020070402c0300581c01079020404554220700b01c40700589414110f940c0240c0183c40124407200c010f00144d040610b01c290a11080c49400780c41003a460300040c2403806204191180104030340c0f0b82c80a511002d00c00302c2482d1300040c05900400005000c800d1004003140a40303804044be03034075140034802460423132407603030f01c0c90301610107640641c5480030100000380403050003d100245481c2c0d024040500c411254031131150040b000405440d01d810300074135070941003880b04096000c3c901e0482040c9a11405091480c0400e00c805110341d4000500681079940d540210200002c4480044544003120514000e2030300860b05c903040090105000345010380f81184240740c0321012180131000340b0800e50702503101c83e4005500380300400e50107000c0714103410501c1080c0c2d00189038000307820341c84050004002d101c50080a1081c406640c030824050060200341e076400c0100e002000b0072416648507403043e01101c903003000204020701d89507003c90380c56031180c9001410286543c0302e0108643e81100d00c004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 952260773 1250 952259523 952259531
    0xf0314030c04050f090907050d05030d0606021e0106080a021003020c011d0d02070e0c2b1401051818070b070606030c0b070809060304030c060504060c1b05030909060f0a09 75
    0x345140255282d4841c0b04e040d80d42050500d00310308030590b520801e200701800703410b03d0307806a0148201841201c68041c0c00000512041703a0760741e0029510300070002c03d43e22003801040d801c10120018040c1d007046030f1401006118440d083e40030400003000b8003506006042c0d081001d17408551084c011600311404400245041442d03040030103040c4001040004215013210006000d00d05221500541148820385410340f2540005103099243e803a02ca65890380c6100c1050418901d00317150803020f4055520304d04d003821a641c0d801030107400c090000c0035080d0446000000303401c9244d80700007a54541100d0040361007465890514035000d510804081c2c804c030341c58400074018000304180c014028034000d10b0191400c890341e02c0b108110301800d424a403203000c0000215041c5845118129074450700410100311900703051621800600c0c0c501a0403000c0350030840301004024203500341035001c3d90030801645c906003d50301040b00e1904001d01842d809200e4031102c1c00d01391a61500c000140500d104001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 952262023 1250 952260773 952260779
    0xf0302070501180602030708090303090d0602130608070c020f01020c0a180c141606060906120501140903090f0a03050a03051b030a0504120f05121c09030206040f0314030c04 76
    0x508030f002078002030500d074031403c10070803a059000040300c00706a00000d0507921000c2050000c0d046110301403c40ba48403501c0310b01d44042c030140d58000c0c150011007007015518107940351016141c003041218054041420b1b07600003409030402048408504805105861501040d03500080c1c5180254101c41c3c50004151080900c0341150300c5000300707440c07040c10100000d079801e04c0c0006180c401c83e015641e480e441000e00e281000301542005000c2d10114506104681d2146041d00030300500040c203554a608050001e0a880d0b07480c00e000c0e014401c200c01651401c940f2406206041000c0100240c216190060000100310207001800d04244a41d881c0c0355074940d03e084000b070b05143c0380d025102503003040101d0080b05401104850031910504841d02001c00182004280328540001c094510b000700051200106003400040c00b98100b0b88500c070141c0c035082000d010807207212502c01005603110002107004100ea11240d041080c1c46444c100d810303856a43c40310300d1990819a504618418040782c14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 952263273 1250 952262023 952262027
    0x603071a07050106440a0f050c0f0a050d210c140c010f120b0a080601090c0504080312092401030b0f042013050c03040605060a0b0306090604090f0302070501 69
    0x100c4018511010603086140c20340301011019500e00b170071580c956002c80303a0f0650424058516040038461841a12101000e07420000449480c020b02240c841c002c084110030140381c020003140c4d0810001e02121091800d000500a04080101c015101891101c1902c40d15894142c0c5c04407503840180e603412100000740c549045a141641c070a041d5603042541d110407140d03801010340c1ea560031180b43c440100355561111030300601140d0001a04080111000b0881d04030010300b0138100d40080c034041100c0b03060f1403001c54003030055010381301c00b03600f082100f00102c004150100e600422030509079809d0344021100c841540740741c0d614007218201c00700010424400142c442c9680002d00c0840c5100b40e15160f07035005041c403425400e5148242c0c5200e295155525214843c02100000100810190400072140d001070341040310308603007203803e21001514030709002101104031480d6525140c2540c5801e020020307a0040144140d4200e13503035903917400105840801341900f40b8041d8001d460618105800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 952264523 1250 952263273 952263281
    0x718151e1d06091302090a241206090201091e06091d0a11040503030f0d240905040204020d05161205060d14030c1509010605030a03050f030603071a070501 68
    0x1020340700c04190415910740041d40700c25a035004204407040212551603038201c074040b80e4510400f9410484440800650590702c1e0f014544c040c10440c078034454801641c00d0b48080c0701081c0210b1000103075404a101c0000c8454000d181010700c1414081480782d203840c040310080080c1c0030301328100280303007104104841d00015001d001e03116804956080e4002d000c0f509488501c06401100e1055940442290711008031090782c0151074000e0070b403507840c40500d42c124407903081151003201040c070780391440f1600255284e040d800c501d4079100c480c0c0464604404203004000091060340c101d602000301302c80643d80c034417626101c4c030300100300440e00d005004801040d84034a207800221541c6801e040c40309c9580c07040b0400c07400c01c0d4402142031100c10200b407202c0c01c501030101d48280d00d1043c1500c000b10300c6070f030281c000d10920041008210a607507170401c05036039150901d406008070782c040092170b09110811008540c0490302800b102d16103a0b90301e1441072448181000000308078030124814080000c01e0003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 952265773 1250 952264523 952264529
    0x120b1b0f040e1b0414030709020a0309030e18041202190309080d0908030906070f020a0314120f0f0706090213050618010e010504050601091508040212010e0718151e 72
    0x3c00168000482d0340e224085100364014000350740084c1143c00102d680030081a00640a0850309540f10801040081c0c0644070f0100114041106801c07505040c1c10441c0140c04410444070148030b9a8079592166201c0c103481e64581000c6015080020f02c2c6040c007403240c0446039203e583d03001420340c9802c080b00d04140007074140300100214000708010050000068944001003183e94070742d038100d10314008030120b0172404000d410a0305e01d280001484110550f19505414681c1500ea01e6200c03450b080006109451070010110403e0205d41d650343c62120180c800316105900000381e00384960006203c1c0644568800e407001e440340100821800e00c0d40140d480c0e0100c201081d4955410803090003510030341401001e0040c1d64030f40000390140c0c400c3c0112001402411589000703000710910082c0480c008403010303809801002c45e20850301d50144501c14242c1c0510000c0c00000d41461268030230044924003c2d90312070344400d00c28040700d008203a00300c003c0000902214804400740600024640280c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 952267023 1250 952265773 952265791
    0x3020a1203090201020c040203130204050c120f070f140c0f060106110f0622020d06020717030f060d0204020d0e01050402030c0a0303020d0804080717070b0907120b1b0f040e 76
    0x342d82200140d0b00014018442c03c411600540c0320764901403080e422080b120340c003079801800d02c001c4c400a0b59408005248050036480740500d0703580c54014100d080d9406444190005210070502c005007407041100811421404100504d00a41012a00d203001a40c0701d00c00c0c40c80e00514010880f070f981042103156424216405003e11400211800d921044014600d0004001d04180c41c2c50310b00c1c04002140c00036038000c00c1502040400d051510003500700d0b490861340a1169108400c8041071442960300c0f0b0842103a125266607a00d0b014006071780b40c4002c040b07802c15000d03c680c80d031500359405030349a00c04043c4000111440c180c010145400e05c0800d070140140600002070001c60380c045440c5c003c82d0210b003081d142c503898900d043e001c9481215009092255282e001b10340000042e0300030410603004458450598585035001e0303885002c1403180c0d42e4003050a603445070000e1803110600da44007139600c5066810740204840003c45d603118905003030410100040a00c054a21b1441c07243d0445101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 952268273 1250 952267023 952267031
    0x15020307031431081c050c090f0d0201024209060105190e070818012c070806100513020405090a09060209100513090b09040f0515010303020a1203 64
    0x1c2e9404811008440ea5074030080708621080b42202000401d03c0c01c046548040c0d01170303070340b080b2841022110115002200300c042c01c08010550041084064070000b1100809198010405034200f01c80b81c0c1a0420480c15030080800c14446842c80c000c40800701175502000701e040d40c03817800704c2d460081c3d1110800245044c03441c007804010940028810305440d425070350700445000d690b441c0301a61300b02d9070010b107441e00c1410401401551094030703e401066003c1e401500009440700c0c1d1070030b83d807900504194600c440c1c1000d001c03160280421260249122007a500c0442c0c0301c04c9050705040382180d0111540001401c20819414091a48ad040907441070045007401d04202c00243d034490003030400c1d44002d449070512001c2c03041d1a8111030900d4802000d60585101c0d0070300c0034082e600305240c21114240310000004081f40d82e809104000400241050308a503110364850241641f0900190f403d44a4000004141c1e426a08124017940c0241c000b42001485442c001c815189401c040b4000c160034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 952269523 1250 952268273 952268281
    0x18052719050c1003090f110315040c1401050909160311070b06010e0102060f010e1902033607030b180a0503130f0501080609091002040b0c0d020601030b0406051003150203070314 78
    0x10046d1150700180d02103d59000000c500380000d181660102d4203a00c00340c10728041c0020040c00f000c5100440e14040410340b120051103005440602540d007200f50001d4203800000c410110b516411145c1c00118203000035030010280400c24a03030004101110030003d0101442250740e00588401c8084100744000c1c02545060520300e1106401071150600d9a1480800700c0c00942c24078000c1046d603000399201f19140e160107603078a40c0310002d11103250510688207880c500d840b911690b2100d0032051120081a1007071559490441c9800f0092042108118211034001181c4060001c1c00a1501131001103442c4e041c0480e803d000c21030243d02203442d03000c210408000300e9800292440d8001002c4541405c3d560301d4403503090604450182c000d1480303100140210b91820300d81c0c042d1820140f4402181c0c001082500160b0740d500302030202a001c5241c040001e00023419540019900c10b140c0ca00c3c01501d01d5a955580340600800e18881c0c070202d07004020410f4076a07151081300d110b50414130300b1142c0d13420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 952270773 1250 952269523 952269533
    0xe120408210a030f020f0a0e01080603030f04300c06090504090c091d011d160819060b090a0b040506150f0a0903080a050418052719050c100309 63
    0xc80c820b00036060548502d0302045116280d410344084580c019019aa0342a04020051401c10310034945400f0070500030210716181030000c160740755030f00c1c0c0c02c1042d454542030420780c0d011013107041d40c3d490b24172488030200d92414605880b500d19840c0b1900c0c144a4150403d100980b01c8141900701d103008510340300d070700000729840340032440c22203a00c20000101d100300880c0c1840340c1406400b51042c80e41c24505c40c8440c031555400c030080406912001e071410740280406800d484c0c856840360303518662201c41e102c4c2e0300815812441080074421000090b0000d8440b022901c9040d0845117140e1007580c402c52007105007070501a407a406481180c0f00c0f010b420304041c0410403401220824143c440020403c680d0142c0030b1071030300001c0c6400c0070303005880c0d088403c00141a60f0080c003403a00601014000700c48202d60358040c041c0074036000311001c42d1403a058842102e28940c048251100ea10a20004a040c01c003652404440ea500a0b80540154403151052107842c1e0360700c10034142058a0701d513503440420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 952272023 1250 952270773 952270777
    0xe0d0207120312021803070e060102010f140708070908060106050d0f0b100e060714010203070905191e091d010510050f090702030723061015120e12040821 68
    0x100c20b0f2005865030010b241c901d05401d01a100d2541620803040c004c1015090b043d80e080c41101d00340c1c001d000000ca81c11000e42600d1658508405070b640c00c40c040392006000e854660760000b12894800156036480d081180703003890a0340541d02140c00000c0c00100740b4081d000c0c1ca4222101c10a003408007074503081c01b0403c000d800c40340c00700030000342c3c00c00c130141c5a4581c01190800c980000c0102000c04504445500075481550f002000c11402100062203040207940c5581c400880d0400711440c926003010400c40e10003c4206510b02c1d01e1850011485030b8081c425424800c0801e41c0007415200207441d00ca085900243c00f90104d6812041e04104a03524400c101071003440c01d0b02c81c2021911800026131440c0582c0390b00402d032003140300c41180140600950308940d51038120480d134003501c84092010300c0a5449c0901c10f140d1103501c00342c841c1b4902964060341c08043c0c41d040020f00c00100b20b9a1400e00302c80045100655000240404c0640c10411540400c0c44812602c2c564416032480c405001d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 952273273 1250 952272023 952272047
    0xc03090607031119081e060d030c11091302090c040f0306113007030515042c030c0114010501020a02090a02072009090a031b020d060e0d02071203 64
    0x142d00c07500c1d0800031010980c140d82c0341c40c05904200c24903028900010b0701c0320348215020800f00c006c13084841070b00948008828010580078060303001c03a00049e1804c846030061040b081e2451640c001d950300068480d484028400c070150840d42584030700ca441002000d880250400d00e03007003024481840794110344c001c4842200d5001c140002e541744200d2105400340100340d80414001a5000c1e2211520251200e004241e0030007608545103036907495054044400540303818210b0301081d50014014281948038404003905140109802442010071030408201c4c50310060b41c9030404038010410701401d000f008040c4440380c0c804080c83d81030200003035589080315001381c4902500c4000c40c000700c100d54121000c030303600200310329a8507041c180228403001910002d540165288000184030b03800100d07485080304d41c036980d0128a14901c1d0011820949940030585c0d00076505801c4d03000188140c1301e0b07142e0701d287e004058105420325460190804009038400010420080c09140009500c0340719224a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 952274523 1250 952273273 952273277
    0x3030f39022d120a0c090b1315060c020d232a01051c0207060c0809010c140915070b06090708070207061209021801081204030804050f01050f0a0f080c03090607 70
    0x111210f1080e40b103142200c44c1030301170f05600c070b0580045540034142c1c01c07141c00740b01c003682d815401181000c000c01c2140c0e62003a580c02ca0070a000c6041c005580300d41c808449181c00200f641c0308250140e01d580000303141c281d11407038012882c8074110384908000d2000101c3c21000c001f0601510300da00000610a01e800d0410604200001841840d2003950030741408154218004c11502d071510303403510400400b0720441100115103400c00250004905014018810707205650301101c00481c540c2600072500702a50503a4005800707a03a00e41c02c000c1a801801070303d40601d0401c1c6072800d00c4014002c4c04040a84804100102039042005240d0001810f10440c3c0d801d01e00300020300300c9544540004c14070751070025030140d1444540210704100130304141c144c441c010184c1d000c0c0004402222034911892100900c14901803108000b540b4011003171000380401810060318202c001d92214880380c0c01800480085075005401c000700d40e0b44000f0781a407040041e2869490741c03d000c454240d503100300038a8001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 952275773 1250 952274523 952274539
    0x1305130903050711040912080603010f0513021302093106081504050a0f0f120806010c060b0d080415110c010801050f0307090204180e0703030f39022d 66
    0xa550f48a07640b01c009256044404111201f080407002080c134041510410700c29800c2031340c000020101c030700c1b44a01848a004981214900e15400e0010400041c20b07030801c1e56a081c840d0b085591176a0080c1500400b02580301864800c1c0050201881c1074801900740100385040000c0c08005400a5400c04186000124001a80d0b0751720700503107800030b180e80050682c44414070520810141c403104030b00c5e2a2103111503002150032048112017201c4102c0e6254005030714a144100490f0079a030104903000406002d0b0f00306d01c6041d486000f042e500941c0044680c0501d01030041c0b1495000d505029a0480100600b1164030f0510008180c19418041c0c02e1140b0001c0c912203089544c1003200c0b200600d04154155182c950b140401d4914104207690049401e0a0072003030341002102055080a072941601c98400c26035200c00100c8000b010b80403c8050790000d64a91202c052480c1006100d030941580d018204400c80d1052004102d09141c1c5903030041800070324a00c14403480d0030502200c40c000c1e50196 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 952277023 1250 952275773 952275803
    0x2040e070e06091008100b0f09040809040e16030311060a0b0d0b0901090615140a0305070905280b1309020a030b06030a1b1d0403050a03020d06080313051309030507 72
    0x48040320264000c290b541b00d200412402d0100c0f0b85c0200320034850480e59400c0110340e8101b800005081110000d20700202001068020720b1300ba442406800018812a88428503070b943c0b040d1000d01540090700410418070b99000381c610308101c180d074020385c94482071203100b9420001c1100c6d115200c1c002040107080c8400500f441c00d096100780c1520f90082c800340715508204010940006c01401010903000700850101028202120003804996001d402090401c0c50081144020840903140150074404800c00c2d85100281e031069030200c2c03110f0751001070084413600810092b1181c81441d034884030f0504034000056a50502da600c102e9030003e890b80580d07510040040c1c01c084c2000c40042c800095180f40801c5012205145025101c0302c02481c054115544140c1108540448008001600c00c22000d0a0300303120b60050014038500b0f000100b003103038031041d00e24110b0304246541c1c0060b50080b1010411403a150b003210780d590002d000c0410451006482c0200540300343c1034050704207400c2c455030b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 952278273 1250 952277023 952277041
    0x3031302060d020a09030c092c0c2107150c030f0318050601030b150303070318050a06080708180c010c0c051804061104050a120201021002030c0702040e070e0609 71
    0x7030b4140428500110350b903001040c4082c0031050240020b640d0842240300101d11100d087c40341c41d00c224540e40404400944060107441a040030030000c2c1510f0184c405080525221910001126031003c5403800c0c08050301c0072450700c1e000045e0f1148110084103607402181e20303004000500f00796010b2803e100c0d11210194190040c0c40000390450340803400a9083c1e05002c00800c01c24180c80c45480f0103102503c034034028001e00390180d950154160010040c0c1d00009016141c4010981c10400c441c0c3d0a540d5070308000750b80f1114540c0b00101152000c0200100d1961003100c2e15807116440400c0a0802c0031062015503c4c0c804040c041c0c1030141c000d111005000c84108550f006080003006006100c04c0030503000e02200c415142101c99506103031402640340024801c4e24140c0350090140c843c1c039450000c030191850740003030f4264150f02589105540c82007031800194801c020b400f0000b65145050301c140011240c0c0d0a031144003e412009082c40fa04070803004007a00100304640c0307400d491b1640b41031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 952279523 1250 952278273 952278277
    0x60910030e0313050307120209060d06140a090b06180a0b0103020403050a0f05101127030d20122d03040c03020103111204020103110903070b0403230303130206 70
    0x254150742c840480c0f0f00c000c0c02090301c1860261002a800d452200b50755490031080c5c0100d8450007588911b407000020a1802c02603400c5240501038080420310b00c007405008090b002040d9000000300ea00d441d0030b0070070700102228a90f000700c4240d40d5090726084401c00b40d020140c000e840b4840e01c4d0b440304c0c41401660700c81c1d01030750061030f0000251b0710308010524000c0310715001c0b140100c03040e010b039a1034000b2448044c070402c0d500d501a010000c0c60041c400d125001d0381111000761601070381101a850105450420400c0201c0303100b42c4a00107911240c418003844c0c42c900051b1528503900581c100079500410034103980e40504403501d0302a9814031071300c50441da403070f1030070400c0b41010000c030401c01402400c400c001c0459000380c904000c4840458468403c40c4107906040743c00c060f801000c1001035100e5030001c209548901317203003814035403980c0c002411701d040d66000343c14144d000f10701442842444240c84112040e00c4081d429507005a480300c2d622400014446000c000851149030f040d502e032001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 952280773 1250 952279523 952279541
    0x51c0b070e18010b03071107211e050708251502241b0405030a200a0e010806180d050d020f04090203180c0f1c0609030809190206091003 60
    0x284940083da12144106182c1c1c004503450385c00107090700d01c1e8400a1354081011019074600319902d4203000c000c842c01d0254000350703002c200c0e212001e07a406180d41b05074038515030b140c007807140d40a400b00524046007245441c803d01d840011070441403c40c425109695240042107644450034407145150040082e81020088024407007880303400c4000440d00144604694818542e807a2029211110840101c035a4083d500505415031b01c1004481c02168020800300c90384599200150607140b0000c01092050b00d0542c010761208880e01c0050011103024000c1c10b81c0070386078018026050500340342540e03641c2c201c55010f0041c010008cc0d01d0303004080607012550b01d0000070152a6030b030750344e074030186000390701c01c5a001c8a03854071142a1880894045142031138020010b040c6070181e443d802c00c002c07064562000084950000d818514001942401030413002c5000313403140c001c945003030340d00c81d403d12030301410740400440300c100e030f02005a5401043d9868030038203482c1c0c0004489444816002050704503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 952282023 1250 952280773 952280809
    0x6120b060405190303020d0c080a0806040b1e0301050a020712050a051207170f0c0301090c0c0c0f0609240c050a32010e070506070512070c051c0b070e 66
    0x300e1580a8030700f4a06034402101d1090703089403d1089118003c60304040b8050340107018400400c902d0060f540319034890798100070f0003880004d229480c800042c070744925180c11181400d0a441e440300c40e40c5403e01c59280c2c032072100311055107272105940e1080c80b0300e031440f6244407d1240c041131116a4510400c20b80d42c03542e0305d07403810382414182624050640c0c410182c1c8250100441c81c0010380c0d098111030541d002d0380000241c14250f9007010b00a00191a440c0d4224003046440501c5802280351188164000e14164a0420341070341880402000c40c0d0b143e8000da0321031109803a04565005800044075000c0c03c1e83d280c20f07003210855282242c10844080005040c05440541d4041200c01c16070140301d400800e80f16000c286030071045881c1c2642c0000a02c134a241c1c110480410490510400402c81c540c4a007064907121500b800100b501c680007440140c1b100780c00082c0500c61410880d19044214016880350707464a04180c3d10400d800c00000d10040420800010203401510740c0d4001203c040707804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 952283273 1250 952282023 952282039
    0x3160b0406060b07030e120a05101401060f020a0201050702041e0b030d020a020a030b1f0801091203020304020616141b270c130504060b18040606120b060405 69
    0x6810040410001603405581035480d1800006014580900303c402031036064446180d0a51150104041455900a81c280b940a541d285c1400540240402d900350320195100081d4a40394009803021200160810000d10020301ca070100ba850f000128100c140e5424a446955824580701040c0038000c0f81d207201255030b80702900d01d403421503190400d41400c20305508a0b104526182070482c1d4038031040d01d0194000d07002c0c0c0c0040c80443e2208400c5a840044002d03050004003102001d070b248441254017514880e50340d0324203041002803240b800e6128250901c0c0950460500b0740000b1940c2c41003100014620072540b002d10108065410b50000e1240f042c801e4400e00c4070048000158101503506051248007400d4441c50010003c0c3c24213203401c03001c02c904900300d98409090700050340c011100c250072401c0750000060b003a6220f000f0300025000d0032899a441d400b04400040c00c802c4603915041c800d504082c1c090012651166010b00904001500419280d071008040790a0740b04a800043e0040c0309 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 952284523 1250 952283273 952283317
    0x90d061a04020c01020306010e0a0f0e0402040b09040311070e010317090f0a0803090111010204030b0601110705041a01030509060f1f0b0a0302040f0906030b0402010e21010e0c031f090503 82
    0x2065001d180700c0c1f142070b00c60300c02c0f00e0b40c0c101c10411441c0b418003800101000581080c00310008208129520520103040010200c0c1e450000909030f140c1240c00710001075050200e000910b0003800010000d1150b6255031010354115039031b4100d1410040500c80020b100840c040d0956503414103000c50341040030f4954542c407502e455803941c0301d40c481004140895014250640300c0300e814401c680403240c00003080b11103a2600c0e00111201e4441b04180941485040340c0402d440d552482046d40001c402101046030811601c0090f064440041c81c1c840303036400c00000c11405641d02c07070056a0144803020025070b5500b402c190240c03011110340003801c1030b42e030219541e40c9554041d030090003500c01c01c00344034a11641e03a28110041e102c050100400780307100031000c10015409000740c1c3c100c0040007030070540640c28002100c0080081e14404403101d07034403030748588907210044c41503403421402600644015491036850501d041c4a080100300204c2d51184a9020b2003010300903611102c0d040054407401c60b036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 952285773 1250 952284523 952284547
    0x90103060203151f21180b0c090f1504030b0c030103050f160b1e0c0c0a05010e010903290916050906091906270c0203090d061a0402 58
    0x2003141c1c04003500585980114452034040d0801c5441c95415a01900d0740144d034108403080540120f0751030009401d80c841c4088001d50b4021820a2080410400c010030550b081c800300550000d802602d03070304010050b416076605d669040840c2c040050b540700d03100301c0341c1c0360a01030944902e5202030400100c40c024011444120002075040300d005000b21080300c0b0f500f024150f00d46088400c80c0341072105a0a003000610f40200240c020604040002502c0c0d4401007601240d95108440c03d5801d41c1090302e1074502031600c2441100540310030301c1c1030700075004c400d0000303841070243c3cbc000500036001d420102d010400c0b82105240d00e030101c203603901615080c00304107182e690005041401604456a8011986040916103a44220001031030f0000356204d50010386040982e86c031444d0491900c07001c020038a40c40403802613010314400091a80c107101c05a03091703803c981030070300c1800441d002045102c3c2d41d5601c05240b4948645c1098000949c2000041c051f031070700d18920b0005421600209078003100315 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 952287023 1250 952285773 952285777
    0x10020412140f150408070b0a02070c0f0518130f122601061d0a0612050c03010518102103020c010c0203031c11070b180609030307110c0901030602 64
    0x81c07140d012002414001c0019a441c1c0802c0080c148160b48410309440c5080b002d0401c59800c40e001c0c501c2d0915042c050345a40740ca20070200c9a50810f550005001010404003075040c20052440c0b181005940d802c0c800060301185030408400c0003920518003061050380151040d020181c0d1102071448042d1803446c0c50445050088290000304002d03ca250310b10101e4903168109c14403404005809582c00c01d00107684800d04000502a010a009071300322580e10b5915485000e0041503c1d00c9030b600a4650101d000e40d44000c020000708031051004103c2c40e1100c00c164040807002c0c400700c000302e0f9503001c21038032442c969038007810f40e1f0480040c03000c1c1c00700b50300e28440180034040d03402d90f68010451750066034401d0502200940551040010410000408095501030004144c000c2081b02c480b004041d280c1d0440380b419100c040761403040c06030401080b41c503070a00650201c0600f44c149024001c854490200500b07900600c01e0380c0e0305181d60f400c42403104d1006150700070000780d00c55031a4204074000f5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 952288273 1250 952287023 952287059
    0x1e020304030e120303090a29070e0307170705210601061d030c0906100e120706020613081603111c0f020a20030304050a140a09020412060c02100204 65
    0x40c0300c1c0f90514038a0404044112071107030956800422070030886640307a0138010307548c0490301180885a40040284481d440314680105180e80c4d0708540c1400b02c0c401c16082c5521039100c044040040b0740e940c00d6804001c228039003121812200c28204080c0001da603491044002d01000160041038004640d440e045000107500122655800c04203d801c01c040c996038103102103181d5440114a40003c48500d42f42018002c0605a0310307204d07000802c7d502c00300da950304620700c1c4c43c5101d0b00108401c0c001142d040192951108400440c140e5913003071925442054420b0740400b038407a01c021000c0006050060140500c0d000851045403c0313101381042d4864100120701c803500006030056581b5601c0e41c1b00080200c0381a07040300c0c0c0343c1d6610030400b001303a580d4004551559054001403100107001d40c0e0304588103006201d00000411290f51312400c1048010640e0003126901e441840103221760007c2e000e806680c69031007440000c207048903c0d0140e00c1c0c0300d80c4070031b44900c141c0001404a502d070342c8001c99103a2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 952289523 1250 952288273 952288279
    0x1080601061d01052b060803070b070203120403110a080d0504060b060306100804020312030c0d1503170313170c010b06090325050a03061e1e1e020304030e 68
    0xc1160403582082e0341103140300c1c09000510500046401c031244443c0d4a04020f401210107044000c1c0206120950710320b40d20429140c2c2002c907055061008043d0348980c46405c030b10181d403078210074403040e039011480a003020301003045903000d0f1401a142000a01407a075004002d8603241c1c000c0c100b0803c003501c001c40b4204d41d0350b4108000c0c2c00d0b003414060107407401108020403507007203500c1000707046642d584024002c2c0d0b131520520340303120403000c540c0008500401101d047e150343d07054100c100c41e003503403409541c09100894881007000411b4515190300c1040c0d4030f01e4800b941d00d4444801d541425010000054001110f502020040241c4c10000b40b1040c40c02000911411072038900b0802c0781c1c050740d07841e10b130140c005040d01c0401d0980308580c25074044040c24650502920307000410390401c916081120019902c1281c518018045600030303d10701c3e881c0100b800f0684c1c0300103a03c0000040c2800a00c292510b90030700425001040c00000500c402280f0f0864503841c0600b002004042445600d81c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 952290773 1250 952289523 952289537
    0x90a0803010f260c04110f0406050304030f090f1203020f0f011b080c0d0c09081204090e0c1f02010b04021606060519050603060d050a030201050402150406140318060108060106 77
    0x20b070150883c030904980588006480c0c0404100c0c01e02c000340c004452490762810041001505102d20080600094044c990340c140e1280741a04c0c0c09071050450800c01c0d4140a020070b020802070158002c042c060341e202027110a000ba00e98a4140d2078070544541181d114000c88413000c94000b4154042514002c8000c018981000801c0c016540960140e80c40301602500b000454007020300c1d40c0110301003a441c0d2a010804a0340e964040c2d003004c0304c0f08055074203150300041c10400c21000740100038180303030350902406480302500d00041401440d50062001103416550b5414028000c1d8084c20102c1d001400566640d034104800c800c10901003082229483c0c50f00d00081164100f001191106040250740b84080705e08043c104056030b000244510f51003010380ca2082e001030810300c41d07584510321903000030410703042c0b47c4100114050442011043c2d940c092004004080d40044980f4142c44000040da55903181ca51100303032000000e800030022031040300000135403440c0002d50300b8120344845d62005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 952292023 1250 952290773 952290809
    0xd050c1e060d090809060307050711060c100f0b030a03030e1203061309050a02040f050405010b041506030b0a0302030f06090d0320131503020c10140708090a0803010f 73
    0x3105511840500301d4005900b48040e544120441d40030b00e464500a9401c1e5080805840004035158001c4801c0c00c00140c010800500300074500280820540085500300e040064500c442c42d56030310001002700c019600c0b0929403030003804603800411800405415580c00700114180580900508215160f26100d01809112000b00e21001d803030141c50001c2032020031050f80010700010b00000c200907141400f640c040800103036900d11134030314401000c1d40042194601410101d0841c0c40d59001c0501850900c0000708406000303030705140541d522410001210700901002c100c0038581c0c5d0700005d40500c94800380d048026000540d543c800d0100d941264201c07410424210241c034804142e84645800b00304050041440c010090190018107102c41841e2a0b44c41201052000c1c183c441c4001099000910f24941c802c00e2252036181d405015043c8180e028210508221110040140c000c1014610216a11041c18031402090580085816132a96100c601c1405d00344194421141c074541000c88103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 952293273 1250 952292023 952292059
    0x601092403030207061112272e0c2910050102070911130b04230d02040507210b10020615010f090504050a0b0901210f0f020d050c 57
    0xd00180d941c07550141040a01d08042030b6079041c54070041c090341e8003407034030120420382a00c8041c4c0b4600041b02100310007044030390b003146869141030415034011a10051850303801100700e40c2c00811081842d44c200f000d0404201c08231514a40c1400040a81544901d0250112000490850203500c142078100d0036890b08180031014503418070816002d07810000042041800e1548116801e119590720306180001514100d052101c4980200c00c800f9000f08041c42110500c2e401c1c4840d0502d000b20009c02c07844108001b90100844060080c800ca490350001402e5511510405c1c00b5105401c814030b5012828600c100041c0c040c0d40f1601d4013070031102091045552000810318081d400364003c83c44108802c500448460224420070700030720061a0000840e5100e07486900e1180e04059400181c0440384000c1222600040c3e010381e42d0300c91003107100c03540c80c8000014a00901c1d4080d0a4040c0d100d0780b0326256130091180c1e5806940300395a50900d80900201140385c401e041e504603001d056400460b100d13 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 952294523 1250 952293273 952293341
    0xf050702180402090c1c02072a0608010f0503070b0a090e090c03100c081b130807090b011e08130807061b05031017100204081c0201061a030612060109 66
    0x200003030a00381507005c25100c0303030550041000500412030030300d82005140252149c00b80b800507456040c91071860800c50190310014243c09019201c1e1503210251400001955030740c82030040000b006c4000030400b00d054040c030b42c000020003014076001c00524007071541a4948852500701c9029016001000000d0716246c4a401d086001540701d484c01074a0b540c180e00d20a50250803000c400038010004440040c1c0e140318944000e15000700148031640c20000c042c0d0070384040030102814440c851580f01503c05408130741071000c05180c50080b09a0f958507651a0188280036406852003000144180600400b50041c80c1c40103c0311202c80c42440c01c004045078180b0044959000e4a1800030060000c800c5150981d0340d81c0014004503003d40307890b0b0408e10201e074095400a402c43e44036440d00314171031918400e0305080071300c203000801005260180004007191004141c9000a000100149055440043e441d000c12100c2007110000d41e1228076030b1006080c01c1075904517091441840c0c8035070202d0000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 952295773 1250 952294523 952294537
    0x15021605061204060f0b090a090c080f0303010e0702030409090627080a050703030e060708100816150314010303021b0a032003100c0c03030501170a030f050702180402090c 75
    0x30020701c2c0390b902c40d25580000d1540481e894006521041081d003503550702c0d01c00354092000b01600048000992a00580c5880c0691010040e40c00030440c8011400000c800c0c0c0381141e80c442c2a19030182c2d00c0040490562280d5081102c03030724900b1103402e05100f1568012250801d204400c5e0640c01300340c940d800c4103002d078404010a104010010000070522402c041c051261007410041000c1c011464000d0800104662000c001218503080004041420103028018000800070303141c1c040700303070300b6603a030525581c0500074220852014002c03400e4405d521030403040443c06800d103020751f1246002900c2d1005103e54000ca00300301c1c440c3d40802d21340307000e045040b60760ac4038250341d1000504400100389804060015890300421000c000d111405003d000122403050380c40c000c000d10140f4024044400c10303080303240d240c15100099050000c0000d041094140c03d0b00f04011140e111b514200d8092080c40300094110f0303030030001c0304251050107900d0381c0030354400c42d1200156668410200c0403805021 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 952297023 1250 952295773 952295797
    0x30f0924130e060d11010e04020c01020a020106060804080a1808060f0105010e03011e2c150a022713110c010f050403170907050d08030f0105040b030a060e071502160506 74
    0x4c001c400941c25403081e4400ca68181403555000d888140000c1c102c0e0030000344c0b0440c5940004413040e88030381c20b1140c80007500c02030500300c2c160306183d210a1024080d2118000c00d111083c82405840152280124000e2410000b00c840303d00c0e0111060910980a100701d0b80411030400f04594a85418080c000f074195404881000440d40c01642c0005000c3c4600c200c0c10700309564000481c18a0718801c0b00e0880c0300840c00405120501e031401031090314004180103c0e0b90300c1406a881a000000b03468061941c441446080c4030303611303c0005114904401f03002c90024506541d64030f1003800340015268820900c8020401e0111171603140c0d050700c0d8200c40c000c1c00582c080c0c000103040c65010b1100340d00400240100d8014688610200b80d2070045840305444400010040151860074206004c0c09080d094030103010031500d08010030b985468004e00200455100e50751800e0300181088400018541c102c6941340070751034803e01a484404483e14800c2d013003503200c00819241400c204a9041704190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 952298273 1250 952297023 952297039
    0x60a0f031d1b0604050a0f0612060b090d1505091612030905010f14120124021b030c090114090705030f070302090d0c03080309011508030f0924130e06 66
    0x71445080b1403040c6034001c40d88540f0034440440c0365100c200910016001491400100c18204603025103400d00003088200306500f04101072003a24103100941e00001b000343e51030580030701c00e894484680d080300070512008502d40001c00041e80c200040c400b22098240c00da5264068a400a180c940c02e605440500481d480c50300c01c010070352007158400d180505501d49002e00c8200c00c2d880c000940e010000d0003021007043c0006000403054161801200013555181c1c0c110005101d070b000c3d4803611100707451f043d40d100500d400905500d043c84207030329180740104080e50070340e19115030203404580c040c0a140606a41c400095580d405441182e001d164103103601c091039600c450044010f50b200080b01074101628000000000764500210340c040d610403181c0365242d1034040342150071101d4a0710545103030111802e08000541002c0300302d5142e003402c08400c95990000d40041004039051410000c1103440402508032a20310381e0b401303000c0b0390f014483c41c501d0941da20860401490001e0320b10039848024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 952299523 1250 952298273 952298293
    0xc030303040f051609020d1a0108160306030c15080c0711090403120507030903110316020402071e050f010c0e03060a0e0f03180f03060c16060605060a0f031d 69
    0x4102c000d0540d0a2180c401c65030700c2100c0f40d83c1c00c4100000d41d0300c00d071201d03a00454050314244060060785d408030400c01c00b402044c0c2d202000280300300005409840805980058003106034480d4004402464211408800583d0f5910541c41c509a90794401c400082131100400d655000e403400703c1d22100e82108480501c3c20400080003804074014008506103c6506c0aa6022880c01c1c00b5542c803664164800041480d2141000340c07901d00d0003213198501c1d41040144d000740c01d00f03241e00300030341540582c2e0041e10356201e17290003900d001481400944c81590740d28010108100010b00f05074803905c4030000d21101d1010b00080e252040c01306400380c0d246c0c04c903070006070ba4060550b200b0302d09181d0b00c3c811075040055200e035940c1540d014004023015050031110300503042c00d01d401e0f511000141900101160b240c2811440c101e40154071341180c0415644441409010320398011002a0800801c0166540700c203040c06005005c54200c228007003401c20901c0d820b4203130410202d03420309100001814075161 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 952300773 1250 952299523 952299533
    0xb0d05032502031c0309061805151b0d1515030b0301051b0a1707120e0c0306040f03020705061206040e0a0201050f0c070e0a02040617090c0d082b0e0c03030304 70
    0x60840c4c100b1042540d01c1d181c64000c11200c0c082e00300d140d2140060700c03110707503550309000b82085801075021014207039103001d00200c10000c8805a9440500031000740c6c0340c80e00901c80717101600040c0400308081e0704007030002c280b9520509140c000ea0300300c2d0310100001109241031500740d0b0340031102101400c201403c145602c40d090401015404580c0c54481c880c0b01800c0b00b02e03010700344c00b620791130009659000307491004d001c2842400040e4602d50000c12062000c0c0002942d600f90040000707201da0340d45588a001c05008101400141c10700601c00c60300d44036020944110014210b0701e4a120b241400000002c1e11800b1510190190301a0740305490094082c1c0401c0450384090050109446940e0b00003c00e82c0321010303828000c6158410150762545480d4009200f6034808080171070300c04040e4180004280006001e05849600361740031b442e810083e0814244900a8142001500651401c45503481c203010300303d085a0f010700c070b00c00c02045450000c0e203542d4044400040e60143e00400126001c90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 952302023 1250 952300773 952300813
    0x93304020d061514040501030c150c0b01060815010f0c0611070f14011d07030210031b020109120c0308270d0203041a1215040b0d0503250203 62
    0x1400500300403001075003a641c80301200c040c002d2588103200281010f01a811030300c0d14034008007408450500155045441d03135107440105104e1030603e00070038012a80c603030b4001e601400c020780d00624500c500e981d580001034001c020441c0c0200356940000b07420951507010b18103500b2902e9050741c0d81400c101c003a0b980ea1000b4444084501c250300e4042c065403000911511001e500f50b0710920099610540071844942510340c21801c483ca140305003e1141c00d0510300180380d00c00c50390100d035032800d03d0300600f0041d0024980c580c140d520042c001041001c0d41901500010380b054407410584104928001c1e042b42c8084074010010001000c03000403c000140b0541d40d65030701501c04c142d00030154103503a100e501d000079030405800981c1010400300f01d001b101e0354650b8402c05201c0e05480ca440b640038440724840d100100352450700c2c0c884021b00e222a845551140c0c00c81c0201038140b04491088d401c00698030b401084030700d180e0020001304401d103031200384141401c166000d001010910b440c00346200301b01c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 952303273 1250 952302023 952302031
    0x70e060a030320031c0906050603070b1c0212010303170708071209050c0a031406070e061204030e060327010207020a0506030405330915070e060c06070302030933 71
    0x244030501045c04908000c03454800440020a0002440061403912406460000706510b01ca90803100003005500001011a03c204000401019455410720641c1c4d000340110348400300c185082d80004010140c014004c02c400700c3c21943c02400d10396440b40126501003048641c10005800c0c0072015450820581040d0f26151180d41a140c07080c0703030f00010440607080f99000395481380340040400007812090140c03075082051450304001c034a100310045442c6100d40000e008070907034075000140602d8415103110205580c000c00050b642c0c20034044042c0021451640c2035403813001c4030015201c4031310510848101950203132501d03a000b0721300010481c46400080c429907050150001c10380362028003040807240120002d40c1e60545002103484030038103c50003859240d0750f520109140300c21030b504106442d0300032101c1c60518607446110b03001c52000d0094100c641100d204a0f024042d074180c054003d54418600c0310121036014140503043e1a10b80740714003140707c500c0ca4801034922000d030000031312580 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 952304523 1250 952303273 952303337
    0x406050a1e0810022715030901152601060e040825060207140309010828020315030f030f0319020f1206010810030213020904090b09070e060a0303 64
    0x2815981c0c0022428414401d520403440c903030005400318010846060f100c002c503620441340044c10102800306080c144448010340c010000403000400304000ad4101d08031800d8844405030704c2c241e4440c07045840c8130b5090318104202014100007020300390144183c00485071582e42e051096116525032001ea94840c03a5412940b8080581a8403071107841a45c070a00381d8401c038001a5207440071301f046615820b14440c646000c0e0401c0124008503039003c4a8142c1040751140400140c0b4002001da43d042204200070340e19142c00031007000b015140040034200010703415030603940b2100250701015185c0c42400d900145210302800883c42a004424188044400c4420010710f0500e1001d800709103508038a20082142480208020389940c1c044040e40d0483d40c00c8a0680301281942e00040210705441c4044010b036601042e210390640d1113030080200c03190410340c0001f03030f4100300343c0181d00c4507450b009a06603a0f40072004a680c504006e008082180c0c0c05689204650740002c40030224900c1b204202c0386 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 952305773 1250 952304523 952304579
    0xb0108161206140907080622020f04020c0706030504110d051e150a020307030c080705090103020f0d05010e04030905031b040506030a0602030a0b01020c0a0b0a0f09030c060504090b0406050a 83
    0x480f440806007280d00503000c0300000e010951a007a1803a280050041030080010144520303000c1c201c04c00360000d000300d036040300c00300c4004840c40b000c07030020f02440c50342c400540b145007400120316030580d1086018074024a10729900d90141c40c00d21000e90720042c8000d205503c03154900080d40c0da42040c0084210542c0207039110071884141c02d500d120004e544092000380e001003480841a01445030000031a40c90070302d9001460728910152450203900d0b03299050640000e1080d030003c031007404030345e00491842420003071035071070b0030702949029022038040f00070810984012442e072070700041c08407010380881d47c1c110038440344d007080c403014100181040e0b070184501d00e00240042c4150000d503208914101002810148a0000915103d0110714250094511b418103010304841d002c12501800501d003002e43c840e280750a0200d0f02c0b40030680c80a4141100410045800d41d0b0007001001169200c220600c1030180090030401190390303d1103041c2d48021603100401042c100c01c99003101404031504030700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 952307023 1250 952305773 952305791
    0xe0d080105060c03130e090610030c090f0209030a050c030f011116030c150c0e0901050d06020f07080c01060312051204020f0f0402031f300c1d040b0108161206 70
    0x114210b402e1b4101043c00410042000f020300420869160703c42030014525041c1481c0d5290490044018003c00784082e45034500380c141c1303002d5a0115200c0150103000c0351154107560400585960300e50420602ca4004d50706a2118104140141c0110b49440b14075146000c5a0030b0200240c0e03850414101c0c14004012000004036580101c4a4000c1041c0c01000c00d0a00741030030002c11884203002480c1c4100484001803184d6103803010803c80744c503803106005a991000000b4a0282e01802c00000c3c046c1c040050388030801601904441c080ba48124031047d0015000e200170385081c02a04420034405000200180c003501d800310001c6803100c030181c176807110b041c80707627000c0380a03039004441c0022a00c241e96601c0f02116110411100107002d5115a59000c004116810680000125482900d01e40850006003445902031000f0010301c9113118560140c003050a1007100c07c223089030240d4003044407900000f19868042400320402e200580000111420665008903003100900d041e1035a0f40d58840507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 952308273 1250 952307023 952307047
    0xa0c030e0a0b090d03092a050a090606021603051b152d030403170c0d05010905061207060e0402130f0b0316020307021c030c0c180e0d080105060c03 65
    0x607880980a031014180520341281c41a1809001d010041c00305460010601c0110b803488440b0300c0e403000703035281415400101110340f00e031800c900e4104642c000c001d403100049400840e0300c000200caa040d0240c803002052408002414000c0d03101c00f030301980040e1801010130076054080c0e4090b540041c61050f0f450804211450b032601b02042505c20043e460000a4090140c10006040071000340030315403840c509a030b00184a0702d41984031381240c45994010900c01ca007100c0640d482881c0040e0200111f6a45015038409840281c9550780141d201d0303030205440c2c10001c02c441003502d0b00c5231500700508003400144002540442e6100030b03100d6030b80802050110740000740c500201202070380e20f51030f0305010101c0b00644000d2201c08007503600402080005031a000070401e110040040003aa1341c08840c102602c000041c100c2c010020398001e8400302c0c4d01e07411005580324008410320108504102010344541d101c0b06800d000010404800c01001a454944028865586242e058070309090640d481 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 952309523 1250 952308273 952308283
    0x320030901060b031302010201240302060d02070803040b25050a1101060f060e010f03061a0307020c030d09081002070c0e0903070b070215090c0a0e0901091703010f0e010e0a0c030e 79
    0x1080d94454011541c0005569090103405c800b0107035010811800c2c07101c5c0802b42c2003c030075440000e0003850f0100301100c6600181e41079610060b00084e450f590f0f0300d020300e80103000e21411039100e88940c2e15901501d15203401c0b814070450000e4980c03036203480c1405056090310240c00b0003031807450079900c0717030004594203441c00c003280000d10719501e034a884406814000741000312a00305c3c4504041c50104108140001c0419803100c07078948506c1d640d500e0300c1c0c2c050100c4c240790354910020b03014407540c0904c0765400c0d03101d0822003c861410090301c46c3c99101c901b50100b030348240700e030107000c092502c00107109192a16070316640141e2488203da2400c0b14658410401c2c0100729480070258003e14860a4006500c1e413150b1342c040c001d14050f002101c10390001503486142405210140740210000940d007000035448141510307001300f03250301010307086440b10a042d4002d0040c8142140000c2c80040c6400721340040d181603c010032110f1500b0350322400c1d400002d020100a2000b011348801742000c0d1131005001e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 952310773 1250 952309523 952309531
    0xa0209040e190303110a051815130608060117010302040507050c0a03022503050307060908040504020c070315050f191b030b0301110324040b030d1e0320030901060b03 73
    0x181842c40825401e010381103a452911452000d071007040843c0440358040221140140340303050018410854001142803100610b0164002540000e00d040c03404800321129000c0f10060340e00c481095a400340110380c1d281d0301d000401809200390005100600e002d402540c1c1c440d640340f0303101d8101145641800d2030040120b5040d00548c010f200c0c0084100c142e40c0d01c0c1100c180c041c00034804101e00d150388050343d0f4072604901800c02e40c4e40d02820410004e4034421071f002800001c0c030070342d1140b081010381902c48101d88011034980b990040d00170302e4650107018035807041c010020045444c0d0740e08880806142941d0340c80d000c0c090b64402c04030411181c11a21215626060b80e0002540356500c4113040c2111103180e6540202c0c0307c10b008204841100c03c0404e410401032818402c01103c1450104010b0484416041e525004500c140e4014550104214501c02c00003242e8580c4107075000401c0e01214480070201500005c9036040000d00d00c581001542c0010a141c0005031255666943c980207400c156 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 952312023 1250 952310773 952310803
    0x612060b04050a0b2d04061107050a15180b09031b03030415050c07061707020a0b0c0a121425021002160609111503150409140114060918060a0209040e 66
    0x22809200c0b41b40d008408d001030701905401441120700b0480001e1654803075200e40130341c201c03001104212039441098220030b84000b06052003022074440107141a585c001e9100c1a00030711640c14002640100807907072690b508809409180f17894180b03c0d40340040d100c0801c401c07080c00800c10908550002c2007014100614880d55005160f0086078035401c0014406403401c130845d4000d804000c0864a07000c160703500411541c85403071384c6243d80d03407050740c088004a100b018040e01c0c005940042c070b074030758a54a11405981d0341000440c1607036543c1c80c0c00c2090350b001080041e4895550788400d07841560040240c0021032407070114000d01d6640c0e01c820f41d009541c04840c82040400d08203124180301a418010840d01e40b001da0851410b030007260f1384c20740744100a5114580301c52003001400300081e004105036048034024448070031420052450b0003c103452140c060001e407400245c05007204000c0a030f9001249000d4150780c0c4845040078045d4008408181e070296440ba0594110282003040700741003240c3d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 952313273 1250 952312023 952312027
    0x9010507080f0a110307020a23040501030b01090608030a090e04060b0306040f020f0a0324091a01080c040e0613050304050301090b09100c090603240612060b04050a0b2d 74
    0xd100300130310602160b4000c252590003400340000690790404e082095445842501c5041c0c01c40c070644c040242e0000c45056041440d000011061180040030541611030b545002d015040d0b481880703c0d628031039425414001654200d05110304d005401c0e003e50854001c0c103011480f04000d40009060448c260b804a0b410444141d070b450441c00d00040c10301038448104c841009070f5207152113161f02c00303d04032001c1318101c14510340100e0425159000880c5150012101d440d04121130742961090f640c04c0c00381116074828942c0e0b00c500c5140902400160031b415002407d5280c0718100c400c0c803540b480010481d2350780410300000c51140c03001d00c55010b40074050707840e081c0c1e642068102103050801800c2c000c900d0604210340038180c03a40148070001150310500c0c0015480155440928000031084110f05240ba04814001a41d9174000d00b440e0000b20105e00c1042101e0703403240320178801d201c0c51050315044003400000300042da200030060302c1d80c40b03a001320f80003454900c44402c0e07407143c0c60010912089800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 952314523 1250 952313273 952313287
    0x16032c060f07030e0a1412070f0c0503160612110a03060e0a050606071e020d0c09150e150301020c01050a4701110d0201050a14060a0b09010507080f 65
    0x188512407900b09145007020441d2160018040341c0b40d844400000c1c141c2114848040c00500017000f400b02c1107141e02d03081a0700d64590b86401d0103519100007040e5130010a400e004541c0b8036010801940e903031000c00501c04003918200082d01d40061098402119680e07074860548407114220003450103078080c2e0340000e415420705501704898400a0046814185000100030042d00c500080754501900000b0703245082c900325152054105c04086c00a4100100c003880104001c5da040f42a0141d5400b80303410b005038041200c1c9001c190105110300100880c0748404200c41e45400c07914411a100064009490007800c010442d00b07441007590780b07442807036030f0707880d072918806500405903841020808003148901040001e900032035015044c801288240c612810200da01520070035550040e5407050354075200b10000b000e40201000c44003d042c5a0401e100340510326240d0301c50300c0c442d10009204403045420450440d480f604060f10b0281400010440c0700d000c03486202c05840c08007590603040da03441700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 952315773 1250 952314523 952314541
    0x52e0305060103240302091b0c070608070f0c1106040308032a0a0206061903060906290d2d050a150209061206061603020f0c060316032c06 61
    0x10803a24941c400c11031300369900c801e540030004120b049a030100d03800c0e802502d81c011510781001800d0040f0382203070300c00181a6008200450044101c8401e9240c1001681c1e6840f401d4926207181942c2000281030103e41000150041492040da0000904960f060a45980c0c40121591058505404164051810000c1154031103106034000400c104071a052515070440a0345e598800f510b410b00c101c000400000c0036062a2007518025a0090024031002c81181028030061512a0a218201d840002100e12402c3d0003034012240c08009883c0c180344002d5500e81c0c0790100c113542240c0f910201c2440400000300c4101d445008058001c04c090510103a451601d10100a0782c0c0141c0300c4910300500c40400565691003e0714001052400180c2d41903555100203880c070700c114400701c4e8240d003401c075800080c17540c00110500305c119400c0481d004803203a0020024580800c550b41d43d82d8550740400d184202d1701ca81c0010003242004560051096016020000c0071b80c400140d40d207880d40400c1c1000740c1d0704 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 952317023 1250 952315773 952315781
    0x220e0f161a0a0f050a1b0807060b04061208070503130b121e010306090f0206130905103816050d0c03090603020a0e0a0b07150c020601052e0305060103 66
    0x7460350307425881c202580c0300151901941c0d0204505100011032107a181d0350180003280300048102c00b991207880359034030f400301c2075810061040d03840919280e074920036030910340300b404143c4061048146d809a10340d039a0365420303030084400b1035083c00306209100031034120121042c040e00211480030740351044009041400b110003002c40d900b00c0d1420b800719806a440706c1d14141500c3d080036020506008908103071408241d40f01000f500014009500090540e4038100c40c1d05551100c5814002a01e9031031000c00c5104041c0503113440c1c9260865041c40f0040301e100d510f803400715410080721807901e036004d0a2100360805410500d500a5164080081050500802005242905100d1400589070310010107030341c214000c0030207065000414440543c040c2600d0321208000038030382503072240c5a0b5105040790b0040385044070302c20903410142144042c507001d84c40000100381d008182580c6814100800c1001040e4202c4800c0a0403001d201200031156140c008403e440d10042203e04224000400715 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 952318273 1250 952317023 952317059
    0x21312050a151401060503070513080d030e1513050a06020c0307031707021e030405150c010b0a060c0b0c040510090303180b040e15030307060c020c220e0f16 69
    0x4289404003548031841914403c0e41914554a0000e03201c0d51500f4040c2c41c0d510591002e10400440010001210000010080b03200c40c0d503030f079050041941c0d503880160f076800e8680011507003020101c00512002c00915041c05064040d0085035004d00668885104990100105002940001500400b410f8005a100c0030b07810301211440c0ca18600f07580000d45a0300400600030003260144001c00070041f040050300c0c081c160042c41e684c1c48280e400c0700e00807650f0041d030500096500300034401e0464504070803040c003100c07040d86810f4405540b5543d45a0f10700b2000300040501c0c2402c1c4404580b58490415a003411501c5441c0c29030302d42d04504010340a107001c203094010700225080c1c140002d00c120000e035412514903840c2258035489054203110440c200380885c507058800030402d80148281f5401c54014001c8907025194494070f60303c2804120604a20b04021542c0d41d0b00c444148901140e0002707205084082c20344440305034101c400c0f41014070111101c0c80600301e8031001d008241341d81c11030040d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 952319523 1250 952318273 952318313
    0x6100507211701290f090103050903091c050d09150e06072f03010c0f030f1b0207031104050105060a050913020408010e071d0f1305030a0305180f030d021312050a 71
    0x6105c40b02004021601c90603403154101a154400700e0000b40c1d04105a526910008119103001d40d44403480c000c014165900580301c5200c0c80c64070491143c007815801003a80c482c00c0707107100f0703841d03a00d00261540601d07031580729000341c0d003004403030041008804e0198151703a8034600101d003c0e6803080a8082d810642c80e40d103100743d140034011701485030000c43c004c2c040c04044c2008183c0301c004102d18401006002d42c1550504140c0c44c8c14102190b0100e0380368256480b41456003500c050200500045500034014070303401c8081041040c044600036400b17011183c500800c540071008401c06084240c2e002540060b08aa4407440785104141d401e02a03131001e17181c0d5100303405c00caa00310450703400c005034080d104082600b144030200d810149481901041d03a42c014089036035401c0342d203400400425040f2080f00d041403540d4003050703400b2008138100c00c06440c2e0348002d41c105170408002000030341c0b103000b4408076043d4504000900540c20703040b41c94010b0184e0b014054416050a0001c40d80c0c0c80902c0542ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 952320773 1250 952319523 952319527
    0x3020d141b0111030f06131a060c0f0703080904060b0319050402270109180302070e070c0218010302091e0106030209130e060610050721170129 63
    0x6910448003515919000d0300041030540811018850051960343c00414003c04000104114400190a4980104015030f00410a640d2100c401d50480d00e0200d001e00d81865448501003092808c000680071824620043d61142c0900302c0d21249022a00d40c02118031036404070b401051f40c6054450384000b04403802c4007a24510303081180030480e002c0c083c07104426699510108080d0348821000c0400030030740c80542c061050070780d18082c2d1010401d100794020700d030403c1c1e44480c00401c0c1c6c03151f030125135034190020318a031400c001050903902e200400002c00c000741490310401603a20218044501402c003800c2c9800c650440c0180701008000900041c2c003a154040c0b410150784421140c1811100e10b07180041c0c807003100b0400144001d20200c4001d001c076083c058081549900480c1083c0122012900d00b0302d00c1c05421400d54840c0150080a0842510b03071040150960120368110080e00d45403400c5c10441318000040e02c04080d0030381003040410300d10074a0380708044d010031010320b01ea0790b0441028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 952322023 1250 952320773 952320797
    0x20106091a190b1318091e030212040605040311090103020607060f060e040501050f0f07020a0624080303240607120309061a0102010b06210414010f0903020d 69
    0x10911414640100034030b10001c0581d0704212004806444852119660340c2c009942054451409016805040141ea10340600004840c8103906141d9400703c404681c141a0f4001103101c6459640c0640540c019400c400314215810402040544600c0e2a000d4070703581141030005100790310080c500c0c040c802c0721b4014000f5070b840d0801e6030351080e84164080b502160003282c01010740f08991000a6803441c00303061104000d81900010b00c80c000c980364810031650307202d006090f07616041e5040c40c00f503041200440041140343d00444d4025241c1c92070b0300451141c00240381078641d0540d1045065800201c1480344011120a00114040d0460015403012484000082e5207100d1014014102c000641a1960081c001e412040c5401c1c2c009104003e40c800825050790b88044000c0c3c580c0c015442c000c8210106d1410f1b2080e10822083d0034510902c100c0718001080030b10300054000c2c0d821828040130112501c13400d0286442c92250070350080340b00c0800346006071501351100001c40a03ca540b070141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 952323273 1250 952322023 952322051
    0x2130219030609151a1603050a081605340602030718151b060c020c030c0405010e040b0c0c030304030207030c0608040512031005060c0105010501080c030c12040303061508060102010609 81
    0xb04c1501e032162400c2c9541c890031540000c03d84501442c40c3d00e003a0341d44040401f49070300007015000d040301d07030388814190340d0303d81c80e21107104100e9441c49030110300144100700075080400503440c5a01c001d05844170f0100e8210320700c0b00c8920042c40b401c6511540010401038201e60000c0d0003110410880511010182045035a1201c0000d104c82102000415055041c41a03a440b00d48258150440c800b000540404503000f5101c00000d04414020311905940f2003150400784241c604071012040fa13000c0c10748441d520700100e07003005040784041c078100303000001c0003030002e1008600851007a001050420700e186842e00c40ca2266a2000c02405228010407010a40202d0203001d150511250300d0b5803651584c1030b2210413051600002d801c000041100c2010720015440306044c2e407404d032242182550751030700d03560f41d6110071206196124130034417091540780304111100360410f2090401040d029198000f115010404882000000d0311000078400d0950302032013041c0c081d00719100140444000c0390a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 952324523 1250 952323273 952323311
    0x301030b06240a02070f080f0715050f030118060e1314100c08100512120a120516030b060c0d12020c0d050301082b050702130219030609 60
    0x354500070b8040082d15a15148400c1c010090401445007a50311810200740095540040e40a9044d241001c1d1501140505000502d03810740c0810500500c0c4460810610a0702801c01c541203105002060084507500c20144001d54040c2005a4816403140341c082030502c140c46103540120311118100c414429140c0d5403000041071701d40c01000107076103622000c11141c90070140500030107505103003410510956a0180c0c0140c0502c141284880001d502e0b1020420300032101c0070702c103402d41c1c00301143e002000313101e0000c1c003e4410340c1d0400d6058540c1c2c0102d020143e880423688a009070040304040d41c0440d0701403041d009916000d07039042d405c2a45500d811075a171070802c180d050078841e00840c010b10718102c6070129208142c0c420203940100c0c80c030a80c0a000c0e41c0003800b443d40d03140120703000c0082030a11034841110070080c542400540b0201003030150340b5980480c02c01c0c1d0f002100019070702d1042a036400240800240710300d601c0c061100c6a03800030110f0320640c025483c800d0510740c00c81d6020740c29000d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 952325773 1250 952324523 952324531
    0x3090c0b0a12050a090204050c0a0203121807060e010f03050402090c0706181a010617060603070c020306101a04080307030e0d0b09100f0203240310090809150301030b 73
    0x140d00e99250004402650107540ca0310390b02290301e042108104243c0307202d401001d0f60030f10a40b070034425515101c0c00910039020f1400d44100580c02448954010282c2d41c02090b04101009096000404004115030801083d070301320001007a001c6c07080b0b0666503440200c0c2c00d10340e0790314942040141800e600050540304041e284c40180340c000b15800e400d00a99500401c2d075100c0b030644810041e00603240c0480781d80d06404180641c80f90840000072028050001c0700711151000782d44040554440c002c1082a400107400002004005454100180c07070400c9468021000c04410900e19441c0050540001000c80d03684e1002d00170a11003044858800415540002d034581000040c6048007000719000b030340700203c003515408481003841480d9501017400d031200d07101c920b414405101d9010045080c1e1106031505140410b01c0700202c14504e0080200da4420a0010b098a0400300680d259406842c80c10318242d421180004e054015854a606140d02468812629508641c0f55131529041c000e0020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 952327023 1250 952325773 952325789
    0x1305240c0720011b05010504030e0105120a15180b0420090f0f1003051b2d0c0d0504080c12030f0313060e03181e0114040f061101060603090c 62
    0x600d41e030721a80580c0625400c024004c44c2507540e101c4c1800c003140600b10a4a054021800d2080324102c40d500c00e0088440302828100030181d1901c88a0138034000f0010701c0000c0c100d441120b4008030740b0071442030454440c0140044040f03038022803c401c00089854002d551076401d5459110115010f0b03d5a041cde4801500c2120105564020718010404405d060740e09903034042d2060185020b41e47d0903a105034011030700d000d6075940c8179480030100d1281d48500850900301c0a0f81c081448481d492048131500250042d41e0240d04003840701e60981c4c54521941c40c804081440402c0600580134100421004a03c04503416004c800013030b0704150700c03441410705800e101500000001c400515245003400082e5200b0403c000d050140c41c4901c0d12900078003c83c1d141d03080b00030b941d280149005444800c419161101e00e12040c028cd00054482406000c48080400e800303003c00212000c4035200c0c400140441c5c1c0311900012281d4103080c1c00c5400907007007071081c035282c90008400300d00d9090b03459003502e105c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 952328273 1250 952327023 952327073
    0x50603190b060c16060311030c0403081b0f0c19060816090e010f0e0a0c21090506070507050607030c050703050906091302091512070302031305240c07 66
    0x70380450140d00c40c010030480984941c2c000e200f061000c0d0100c03c02112500d0350200904945c3c040026020300c07060341c0b0301c079984030188024070100750480b004180c3c58998448940c00b408920510303d0a1041000c2243c1c041c4d008604102a241003c41003082c41800400c0705000103410000044c12080e0701802c42c450140441d0ba2050f621030207440d0103809090000d00b85040c41d85e507141c440700342514500a6083c814241c0d000f2510b08a8035009130b0f43c410341385455072000f640620005809030010001c5079030b2525110000c1030b010031418020360b4001c14069442560710701c000d040991030684c3c05030805007051b180034084a00c65601105072040103a0601c0c0080d5a00001e2000030b460780142c0c1082c9030301c801c4c8c0044200c0c044c040b960041c80d180c4030a036501450340850f0400200d050068045501104072114000b80b2003902c80d900956011107031032150002150340340c8449141921203c042c000c0c0c0000400302841034000d441ca43c0e80e000c59501001440d08010360381c0c90700410031106a0901603204 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 952329523 1250 952328273 952328291
    0x415030b060d0c140403150c0c020a051017090109060e0d020a1112010212090c040c090915080d0c020405180c091012050a0c080d0504032004230105060319 68
    0x11661080d10813034185805a520340c1d032030b130800301c4140c8030120825016500e0540c0d81c20702c40d80101b4440700d42c15001070070300c1c007020302d40030a0203110038858040b0010005070300303450b4400c0c01c070048420340034241d14000004d41907003500d040e00403a032061940002603800203201c40c03c1641c2c005551412941d0182516201486403004180d05c40f410129400e62940085400e2144081c020b141c1031160300c1590032130390000c0d5610244411200040c22140006803c0b15003484420b06c50b1300089001310780080c1c5049400da80785080f0342044040185c8000150740c1003842d00035031a01d40101070f04541c851008410000b4600d440e283d49a8201d41168024002800003034a2000d01c4007007040142541d81c0c1c4000e044410345026034680a480c003044800d05040e00d00400c0021001400e06103c100d01e8a5080c0f4080c00e50b2610314820440c1504030740c94502d54251b1058645560003000300090b986010a0600d8801e59020f00d5a141b05130801406180d0034410031062504446501c22414a07500340058a002c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 952330773 1250 952329523 952329527
    0x30302090d02040e3d1a04060609060809011b08070e0901080d14092803080a03050108060601140306061e0f0a080a0e030901050c1603080415030b060d0c 67
    0x1101c006580103107451000d101185000c40c105c0703601a40715005100840c40150546000380d4490f40724034802907568030003603200c11a648106140c0d04038000701440691007400007010740350183c0145000a0701c0715010400203401207481500304042000900c207003410390100c617a8645040d00725408000440d00071600042c02012048a1080054000c1e03105685030321020f6500e107480c166000c0000c640e0b0342d030540c4414068041d80c2c05404001c00c1c10800b13051381600012506400c0c60403411410340c0f0f20000000a1001c2c00510b0152025100803c4561501c2906410710800900e400d0600c004240011081d0031913004480d400130701103400649030015410140c03a0700301003076286030700e107000044e01d040005042e80c0030f4400a017603903440d80754550b115503a4000391280c40749070403595031044c0182c1d44158010006080c02a442100302d400b034030005020310801d142990b0003555014000541800301000d0910280c0500c8080d081c1805148400000315100b0300c100b44587c00345075a108402c01c807080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 952332023 1250 952330773 952330789
    0x10503041218060203031e090606010e0102031c1508010509060703200301121b0803030406050a02090916030501060f140d0915050f220b0a0b0a0e060a050f030a03030209 74
    0x34501240d096840f1040a540c907841610507251400321160b0401c54980c503c03140d1489510410060f01e4203031200c100554440e225032000c5030540c0014081c254114096040132449540b00c82c102003101080990031542015203500301c1207190b41030004002103040300048407a080ba509140005155422a16101c10340c12000d180b20804080000001030201c1028204003801340950000e801c0702c4003442e81840c0b01e0f101841040400c1c1c000b440001c0204549034011940080d2484015280004c040700044a00f04225020b00c9102045807138504200e925128603809040d26061021001e04442c80161503002101c1c1c80e0484264001800703038001000f0b40065491170f80c0218a460b07480200e030a08006000e00b01c1d1003400308a5031400007110348640041000301603003810035040c40c540d031603200c41801e500000c1600c03940300e8032030703420141507180c2c40100e40041ca0203080c0d0300c1c4641022003c20140b0882ea6222074411080c6803440d83c41c996000c40c000c1c600300d625060040c3d50301d2110340818a11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 952333273 1250 952332023 952332047
    0x8041e0512040e0f0c13030f0602211911041404090f0b19060e0a091a1003030905040603030e191d090c03010509190201140403080901090b090105030412 67
    0x2440c408107002840203a400f20060180c0f154000c45680303640c62000e44051406005004541580c228600304041000ca200b0309403451b000b0400980390003440d82c5142c40800c0b0b54200b050b1840f240f002000f04072111305541030742495000700284400c1c6034503d0701c00030030b00580c000e00c00400e0b0b08003201400d554881d03102d85200740d0701c00e000040c1d0150506216001440499520310068030f010340c0c0803200c808511601041c3c680948661640344c0b20070365100c00601e19144210b94003001c0d1404030740380f0303031042e901c0030721816035840d58842040c2103103030040191036a035002900031400c000b0240700094204102c2c42e06148140c0c1c103200000c500380b05094010003e94440d00382c1d000060011000121403400280c400c14185088868610b119410300d800c8840449204496402c24100d00c011030004400c803410490051500c0c0d900840900384070105a8059401142c0340b100020383d0204650304400c40d000181040b401c842c0c18260524000303805032000400c0100455032100b4039082c040d0141d440c4c0201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 952334523 1250 952333273 952333303
    0x18150e0616110f060c0421050607030515120d09080c06031b0f1908070c030c080309100e07080c0109031a1012030c060524041d03070507031208041e05 66
    0x9400c00c2100420f985d0b1280c0034482c00c0c0352014006031f010560b024001180198084024021fa64842804030000d21003d001d0704494088044501c00300d5035034a82e4030130a400300c0001303409028407a010140203120305a00412641d000803c000132183e41d00429290320200c00d4102038005203000100c40b08074810b60301184540e50020075207079000d0100380380107072000b621501d400d03190351901d0000f0b880a0f02c25810080000343d04081000008940c40003850700b00c07507030700101e40c0f60306c003900b201c0c009440d0407001100980d8400b00040000c01410002c0048900b0b01703007420a036039400c42d2070703c104000b9492004040d0760f0440c40412900303401c2a4444009102340426400440c80764a4010b080b982003c600303a4440d8102400309640d12489558215281c0107060b00032228105401440043c10025803000c0e0851343c00729115000a00610042001c98804e9001d003d0780b90640c513051030501001da898100304210030042000062101c0a1210243d03401c582a02140190703141c004c0c03901044205031a9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 952335773 1250 952334523 952334533
    0x206030c0906091e1008090c010e06191e0c08122214160f05192c0702030f04090510031407080601050d050304120618150e0616110f 58
    0x413001c0483c0c00118240840b28100900304a1400700c2d011082a00d075000c0c50341226810311080e6000d000c1000380e90401612890801890b140e07144001050302e180b080100d0807400280c04954110840316494048500340061100c0007a11154440c1c042d400c0140c1c01d01102601041403003a100d072114181c03108100b10030b05441182e1a21418540c446000007403a441080700d00320696032803c0c42c0b54141c612612040003600d103000304000103001a020545200342e1815000301d0101c0b180800c2c0d403400b12402488000e4200064044084000300520550031900240004901c42c40300204480843e58900804102c944560402c0301c000c034025407000340300701042041c1d001c400c0004542d00742110082e0059030400d80c3d803841846003d00e1184030040507a08104018040016080c0c030542d4245d00030000020408030a0341511560138400d041907520a0041e84c0003c02c170780d000c3c001e640041d01c80f1801781c4120705015020380036581104000c8400e020546841b49100d0000300002d13200c0c0740e8103408842c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 952337023 1250 952335773 952335799
    0xd06120f141005160f080108100f060509070201240b0306090603030d05090f070803130b03130f05060a0605061201030213020f0301090c1710061808030a02150901090206030c090609 79
    0x1540001c409001d05002c100c110045c0c5006a004852081c101c40180300030b40841c0c00d1460b45d8000400c1524500c0c60701c40c3c0d4030b600c00b00d01500d508004620408603500000780d420064012400340300c520700f85120311104140c009102105032042a01d4000c40d00341c402e0354081e1141c000090075400755084481c0b1003480c040c10854214000640300041560700015111402d0f00c9003a11a143d101348200d46038020f40030b10003004010a40c4c001140d00076126841410f59505c107598a0084030700049042d540f981c0150144040d0030440d2217604010070003280c40502e06195441d02d5804140140300184c0f25030801e01400001a88a4044900403800c642e010355880d83c413485108020700080403c400014580c841c1000c1800300900003e01904604c001c0c540500e20300b0000300c0e5482e040041d6581988ac01040018245108001070310500d10a0340182c00e201079904c4200c2c0821a0060003080aa03040440450150725142c080700d41202c0e45400385661404070f900410344610502c41995000b002c0640c0c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 952338129 1106 952337023 952337041
    0xb2410020111040e04050c09070c020f01120609051005040c170601020a06020a0e03060a06230a03021807030c0503010312081902040b0d06120f141005 66
    0x8507814120781c0003000140c109a10004c2c0301c44101060000b080b206020b11009000b06596000c1c1510306034030f00412291911401a0150b030600c611842e01d80d209001d0707246595076002d000e10001c0ea8481d0020001e02040b10004080411002d000c142454140580048400e072903594450904410000c4841e00b0405441e080c19842900c48141c0003409034006841d000321a61100040d83c580c0505050411000400000d0b9051800b00c00744032000a00b15074a04c0c25103815400c113213402846010a07a0b80407142c00180d44010b61803801030850328054881841800180e90601c11288140400e030b071507020030700009008080c01004990040d118443c040c1d4003d0110446c400d07080b00286c07102080b0380c060f400084000c00c0004440d0990b00e440c2c01010000c010a00925a1a00942c0c40344859a140720f50020401c00e0500210780001c2c204108807600700c0007211040215040010344 = true := by decide +kernel

theorem cover : BRFrame.Cov 952158273 952338129 := by
  have h0 := BRFrame.cov_init 952158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 952158273 ≤ n) (h2 : n < 952338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
